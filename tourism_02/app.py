from flask import Flask, render_template, request, session, redirect, url_for, flash, jsonify, Response
from config import Config
import firebase_admin
from firebase_admin import credentials, db as firebase_db, auth as firebase_auth
from firebase_config import FIREBASE_WEB_CONFIG
import os
import json
import uuid
import io
import time
import csv
import zipfile
import re
import math
from datetime import datetime, timedelta
import smtplib
from email.message import EmailMessage
from werkzeug.utils import secure_filename
from PIL import Image

try:
    from gtts import gTTS
    GTTS_AVAILABLE = True
except Exception:
    gTTS = None
    GTTS_AVAILABLE = False

app = Flask(__name__)
app.config.from_object(Config)

# Simple in-memory cache for external API responses
_api_cache = {}
_CACHE_TTL = {
    'weather': 600,       # 10 minutes
    'sun_times': 3600,    # 1 hour
    'restaurants': 86400, # 24 hours
    'trust_score': 900    # 15 minutes
}

def cache_get(key):
    entry = _api_cache.get(key)
    if entry and time.time() - entry['ts'] < entry['ttl']:
        return entry['data']
    return None

def cache_set(key, data, ttl):
    _api_cache[key] = {'data': data, 'ts': time.time(), 'ttl': ttl}


def cache_get_stale(key):
    """Return cached data even if expired, used as graceful fallback."""
    entry = _api_cache.get(key)
    return entry['data'] if entry else None


def _weather_cache_key(lat, lng):
    """Use coarse weather cache buckets to reduce provider rate-limit pressure."""
    return f'weather:{lat:.2f},{lng:.2f}'


def _safe_int(value, default=0):
    try:
        return int(float(value))
    except Exception:
        return default


def _wttr_to_wmo(code):
    """Map wttr/WWO weather codes to Open-Meteo/WMO-like weather codes used by UI."""
    c = _safe_int(code, 0)
    if c == 113:
        return 0
    if c == 116:
        return 2
    if c in (119, 122):
        return 3
    if c in (143, 248, 260):
        return 45
    if c in (263, 266, 281):
        return 51
    if c in (176, 293, 296, 353):
        return 61
    if c in (299, 302, 305, 356):
        return 63
    if c in (308, 359):
        return 65
    if c in (311, 314, 317, 320, 362, 365):
        return 67
    if c in (179, 182, 185, 227, 230, 323, 326, 368):
        return 71
    if c in (329, 332, 335, 338, 371, 392, 395):
        return 75
    if c in (200, 386, 389):
        return 95
    return 3


def _build_wttr_weather_payload(raw_data, forecast_days):
    current_raw = ((raw_data or {}).get('current_condition') or [{}])[0]
    daily_raw = (raw_data or {}).get('weather') or []

    daily_time = []
    daily_codes = []
    daily_max = []
    daily_min = []
    daily_rain = []

    for day in daily_raw[:forecast_days]:
        hourly = day.get('hourly') or []
        if hourly:
            mid = hourly[len(hourly) // 2]
            code = _wttr_to_wmo(mid.get('weatherCode'))
            rain_values = [_safe_int(h.get('chanceofrain'), 0) for h in hourly]
            rain_prob = max(rain_values) if rain_values else 0
        else:
            code = 3
            rain_prob = 0

        daily_time.append(day.get('date', ''))
        daily_codes.append(code)
        daily_max.append(_safe_int(day.get('maxtempC'), 0))
        daily_min.append(_safe_int(day.get('mintempC'), 0))
        daily_rain.append(max(0, min(100, rain_prob)))

    if not daily_time:
        for i in range(forecast_days):
            day = datetime.now() + timedelta(days=i)
            daily_time.append(day.strftime('%Y-%m-%d'))
            daily_codes.append(3)
            daily_max.append(29)
            daily_min.append(22)
            daily_rain.append(20)

    return {
        'current': {
            'temperature_2m': _safe_int(current_raw.get('temp_C'), 0),
            'relative_humidity_2m': _safe_int(current_raw.get('humidity'), 0),
            'apparent_temperature': _safe_int(current_raw.get('FeelsLikeC'), 0),
            'weather_code': _wttr_to_wmo(current_raw.get('weatherCode')),
            'wind_speed_10m': _safe_int(current_raw.get('windspeedKmph'), 0),
        },
        'daily': {
            'time': daily_time,
            'weather_code': daily_codes,
            'temperature_2m_max': daily_max,
            'temperature_2m_min': daily_min,
            'precipitation_probability_max': daily_rain,
        }
    }


def _fetch_weather_with_fallback(lat, lng, forecast_days=7):
    """Fetch weather from Open-Meteo first, then fallback to wttr.in."""
    import requests as req

    open_meteo_url = (
        f'https://api.open-meteo.com/v1/forecast?latitude={lat}&longitude={lng}'
        f'&current=temperature_2m,relative_humidity_2m,apparent_temperature,weather_code,wind_speed_10m'
        f'&daily=weather_code,temperature_2m_max,temperature_2m_min,precipitation_probability_max'
        f'&timezone=Asia%2FKolkata&forecast_days={forecast_days}'
    )

    try:
        resp = req.get(open_meteo_url, timeout=6)
        resp.raise_for_status()
        return resp.json(), 'open-meteo', ''
    except Exception as open_meteo_err:
        print(f"⚠️  Open-Meteo fallback triggered: {open_meteo_err}")

    try:
        wttr_url = f'https://wttr.in/{lat},{lng}?format=j1'
        wttr_resp = req.get(wttr_url, timeout=8, headers={'User-Agent': 'NammaKarnataka/1.0'})
        wttr_resp.raise_for_status()
        wttr_data = _build_wttr_weather_payload(wttr_resp.json(), forecast_days)
        return wttr_data, 'wttr.in', 'Open-Meteo was rate-limited; weather loaded from fallback provider.'
    except Exception as wttr_err:
        raise RuntimeError(
            f'Open-Meteo unavailable and wttr fallback failed: {wttr_err}'
        )


def _haversine_km(lat1, lon1, lat2, lon2):
    r = 6371.0
    p1 = math.radians(lat1)
    p2 = math.radians(lat2)
    dp = math.radians(lat2 - lat1)
    dl = math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return r * (2 * math.atan2(math.sqrt(a), math.sqrt(1 - a)))
app.secret_key = 'demo_secret_key_for_tourism_app'  # Required for session storage

# --- File Upload Config ---
UPLOAD_FOLDER = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'static', 'uploads')
os.makedirs(UPLOAD_FOLDER, exist_ok=True)
app.config['UPLOAD_FOLDER'] = UPLOAD_FOLDER
app.config['MAX_CONTENT_LENGTH'] = 16 * 1024 * 1024  # 16 MB max
ALLOWED_IMG_EXT = {'png', 'jpg', 'jpeg', 'gif', 'webp'}
ALLOWED_VID_EXT = {'mp4', 'webm', 'mov'}
STORY_AUDIO_FOLDER = os.path.join(UPLOAD_FOLDER, 'stories')
os.makedirs(STORY_AUDIO_FOLDER, exist_ok=True)

def allowed_file(filename, allowed_ext):
    return '.' in filename and filename.rsplit('.', 1)[1].lower() in allowed_ext

def optimize_image(file_obj, max_width=1920, max_height=1080, quality=90):
    """Resize and compress image for high-quality display without blur."""
    try:
        img = Image.open(file_obj)
        # Convert RGBA/palette to RGB for JPEG compatibility
        if img.mode in ('RGBA', 'LA', 'P'):
            bg = Image.new('RGB', img.size, (255, 255, 255))
            if img.mode == 'RGBA':
                bg.paste(img, mask=img.split()[3])
            else:
                bg.paste(img)
            img = bg
        # Only downscale, never upscale (upscaling causes blur)
        if img.width > max_width or img.height > max_height:
            img.thumbnail((max_width, max_height), Image.Resampling.LANCZOS)
        img_io = io.BytesIO()
        img.save(img_io, format='JPEG', quality=quality, optimize=True)
        img_io.seek(0)
        return img_io
    except Exception as e:
        print(f'Image optimization failed: {e}')
        file_obj.seek(0)
        return None

def save_uploaded_files(files, allowed_ext):
    """Save uploaded files with optimization and return list of URL paths."""
    urls = []
    for f in files:
        if f and f.filename and allowed_file(f.filename, allowed_ext):
            ext = f.filename.rsplit('.', 1)[1].lower()
            # Optimize images for high-quality display
            if ext in ALLOWED_IMG_EXT:
                optimized = optimize_image(f)
                if optimized:
                    unique_name = f'{uuid.uuid4().hex}.jpg'
                    save_path = os.path.join(UPLOAD_FOLDER, unique_name)
                    with open(save_path, 'wb') as out:
                        out.write(optimized.read())
                else:
                    unique_name = f'{uuid.uuid4().hex}.{ext}'
                    f.save(os.path.join(UPLOAD_FOLDER, unique_name))
            else:
                unique_name = f'{uuid.uuid4().hex}.{ext}'
                f.save(os.path.join(UPLOAD_FOLDER, unique_name))
            urls.append(f'/static/uploads/{unique_name}')
    return urls

# --- Firebase Initialization (Realtime Database — free Spark plan) ---
FIREBASE_ENABLED = False

def _load_service_account_info():
    """Load Firebase service account from file (local) or env (Render)."""
    cred_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'serviceAccountKey.json')
    if os.path.exists(cred_path):
        with open(cred_path, 'r', encoding='utf-8') as f:
            return json.load(f), 'file'

    # Prefer explicit JSON env var for cloud deployments.
    raw_json = os.environ.get('FIREBASE_SERVICE_ACCOUNT_JSON', '').strip()
    if not raw_json:
        raw_json = os.environ.get('GOOGLE_SERVICE_ACCOUNT_JSON', '').strip()

    if raw_json:
        return json.loads(raw_json), 'env'

    return None, ''


def _resolve_database_url(project_id):
    """Choose DB URL from env/config; fallback to regional default format."""
    return (
        os.environ.get('FIREBASE_DATABASE_URL', '').strip()
        or FIREBASE_WEB_CONFIG.get('databaseURL', '').strip()
        or f'https://{project_id}-default-rtdb.asia-southeast1.firebasedatabase.app'
    )


def _iter_valid_user_records(all_users):
    """Yield (key, user_dict) entries while skipping null/invalid nodes."""
    if not all_users or not isinstance(all_users, dict):
        return
    for uid, udata in all_users.items():
        if isinstance(udata, dict):
            yield uid, udata


def _touch_last_login(user_key):
    """Persist last-login metadata for observability and audits."""
    now_ts = int(time.time())
    now_iso = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    payload = {
        'last_login_ts': now_ts,
        'last_login_at': now_iso,
    }

    if FIREBASE_ENABLED:
        try:
            firebase_db.reference(f'/users/{user_key}').update(payload)
        except Exception as e:
            print(f"⚠️  Firebase last-login update error: {e}")
    else:
        user_obj = MOCK_DATABASE.get('users', {}).get(user_key)
        if isinstance(user_obj, dict):
            user_obj.update(payload)


try:
    sa_info, source = _load_service_account_info()
    if sa_info:
        project_id = sa_info.get('project_id', 'my-project')
        db_url = _resolve_database_url(project_id)
        cred = credentials.Certificate(sa_info)
        firebase_admin.initialize_app(cred, {'databaseURL': db_url})
        FIREBASE_ENABLED = True
        print(f"✅ Firebase Realtime Database initialized via {source}.")
        print(f"   Database URL: {db_url}")
    else:
        print("ℹ️  Firebase credentials not found. Running in MOCK mode.")
        print("   Add FIREBASE_SERVICE_ACCOUNT_JSON on Render to enable realtime DB writes.")
except Exception as e:
    print(f"⚠️  Firebase initialization failed: {e}")
    print("   Running in MOCK mode (in-memory database)")

# Make session data available to all templates for dynamic navbar
@app.context_processor
def inject_user():
    return dict(
        logged_in=bool(session.get('user_id')),
        user_role=session.get('role', ''),
        user_name=session.get('name', ''),
        firebase_enabled=FIREBASE_ENABLED,
        firebase_web_config=FIREBASE_WEB_CONFIG,
        notification_poll_ms=app.config.get('NOTIFICATION_POLL_MS', 12000)
    )

# Mock Firebase Database
MOCK_DATABASE = {
    'packages': {
        'chikmagalur': {
            'id': 'chikmagalur',
            'agency_id': 'A2001',
            'tag': 'Weekend Getaway',
            'title': 'Monsoon Special in Chikmagalur',
            'description': 'Escape to the lush coffee plantations of Chikmagalur. Enjoy a serene estate stay with coffee tasting and a trek to the highest peak in Karnataka.',
            'duration': '2 Days / 1 Night Estate Stay',
            'old_price': 5000,
            'price': 2500,
            'discount': '50% OFF',
            'image': 'https://images.unsplash.com/photo-1600010419356-829283eac4e7?ixlib=rb-4.0.3&auto=format&fit=crop&w=500&q=80',
            'images': [
                'https://images.unsplash.com/photo-1600010419356-829283eac4e7?ixlib=rb-4.0.3&auto=format&fit=crop&w=1200&q=80'
            ],
            'gallery': [
                'https://images.unsplash.com/photo-1600010419356-829283eac4e7?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1506905925346-21bda4d32df4?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1501785888041-af3ef285b470?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1470071459604-3b5ec3a7fe05?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1441974231531-c6227db76b6e?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1472214103451-9374bd1c798e?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1518173946687-a1e0e2a3a324?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1542202229-7d93c33f5d07?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1586348943529-beaae6c28db9?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1465188162913-8fb5709d6d57?auto=format&fit=crop&w=1200&q=80'
            ],
            'videos': [
                'https://www.youtube.com/embed/dA0VGEbbw4g',
                'https://www.youtube.com/embed/LXb3EKWsInQ'
            ],
            'features': ['Coffee Estate Stay', 'Guided Trekking', 'Organic Meals', 'Bonfire Night', 'Bird Watching', 'Free Wi-Fi'],
            'ambient_sound': {'type': 'forest', 'label': 'Coffee Estate Ambience', 'icon': 'fa-leaf'},
            'tags': ['Estate Stay', 'Relaxation', 'Nature'],
            'location': {'lat': 13.3161, 'lng': 75.7720, 'name': 'Chikmagalur, Karnataka'},
            'itinerary': [
                {'day': 1, 'title': 'Arrival at Coffee Estate', 'desc': 'Check-in to your serene estate stay. Evening coffee tasting session.'},
                {'day': 2, 'title': 'Mullayanagiri Trek & Departure', 'desc': 'Early morning trek to the highest peak in Karnataka before heading back.'}
            ],
            'accessibility': {'wheelchair': 2, 'family': 4, 'senior': 3}
        },
        'hampi': {
            'id': 'hampi',
            'agency_id': 'A2002',
            'tag': 'Heritage',
            'title': 'The Grandeur of Hampi & Badami',
            'description': 'Experience the magnificent ruins of the Vijayanagara Empire with our curated heritage tour. Enjoy comfortable stays, guided explorations, and breathtaking sunsets.',
            'duration': '3 Days / 2 Nights Heritage Tour',
            'old_price': 12000,
            'price': 9999,
            'discount': '15% OFF',
            'image': 'https://images.unsplash.com/photo-1596707328608-f404dc7ff957?ixlib=rb-4.0.3&auto=format&fit=crop&w=500&q=80',
            'images': [
                'https://images.unsplash.com/photo-1596707328608-f404dc7ff957?ixlib=rb-4.0.3&auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1627582236894-0baef2395340?ixlib=rb-4.0.3&auto=format&fit=crop&w=600&q=80'
            ],
            'gallery': [
                'https://images.unsplash.com/photo-1596707328608-f404dc7ff957?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1627582236894-0baef2395340?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1590050751776-5fee6e8da747?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1524492412937-b28074a5d7da?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1564507592333-c60657eea523?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1548013146-72479768bada?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1585135497273-1a86d9d54789?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1609766856923-7e0a0c06e54d?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1570168007204-dfb528c6958f?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1477587458883-47145ed94245?auto=format&fit=crop&w=1200&q=80'
            ],
            'videos': [
                'https://www.youtube.com/embed/VWqKcePPAnc',
                'https://www.youtube.com/embed/sLBcw1W0A4A',
                'https://www.youtube.com/embed/B63E3v04sKA'
            ],
            'features': ['Heritage Walks', 'Guided Tour', 'Meals Included', 'Sunset Point Visit', 'AC Transport', 'Photography Spots'],
            'ambient_sound': {'type': 'heritage', 'label': 'Ancient Temple Bells', 'icon': 'fa-landmark'},
            'tags': ['Heritage', 'Guided Tour', 'Meals Included'],
            'location': {'lat': 15.3350, 'lng': 76.4600, 'name': 'Hampi, Karnataka'},
            'itinerary': [
                {'day': 1, 'title': 'Arrival in Hospet & Virupaksha Temple', 'desc': 'Arrive in Hospet and check into your heritage stay. Evening visit to Virupaksha Temple and sunset at Hemakuta Hill.'},
                {'day': 2, 'title': 'Explore the Ruins', 'desc': 'Full day guided tour covering Vittala Temple, Stone Chariot, Elephant Stables, and Lotus Mahal.'},
                {'day': 3, 'title': 'Badami Caves & Departure', 'desc': 'Morning drive to Badami. Explore the rock-cut cave temples before your onward journey.'}
            ],
            'accessibility': {'wheelchair': 3, 'family': 5, 'senior': 3}
        },
        'gokarna': {
            'id': 'gokarna',
            'agency_id': 'A2001',
            'tag': 'Coastal Escapes',
            'title': 'Gokarna Beach Trek',
            'description': 'Discover the pristine beaches of Gokarna on this coastal trek. Walk through hidden coves, enjoy stunning sunsets, and visit the ancient Mahabaleshwar Temple.',
            'duration': '3 Days / 2 Nights',
            'old_price': 8000,
            'price': 6500,
            'discount': '20% OFF',
            'image': 'https://images.unsplash.com/photo-1590766940554-634a7ed41450?ixlib=rb-4.0.3&auto=format&fit=crop&w=500&q=80',
            'images': [
                'https://images.unsplash.com/photo-1590766940554-634a7ed41450?ixlib=rb-4.0.3&auto=format&fit=crop&w=1200&q=80'
            ],
            'gallery': [
                'https://images.unsplash.com/photo-1590766940554-634a7ed41450?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1507525428034-b723cf961d3e?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1519046904884-53103b34b206?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1473116763249-2faaef81ccda?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1506953823976-51570aa3f933?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1468413253725-0d5181091126?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1544551763-46a013bb70d5?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1518509562904-e7ef99cdcc86?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1510414842594-a61c69b5ae57?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1484821582734-6c6c9a0c6c5b?auto=format&fit=crop&w=1200&q=80'
            ],
            'videos': [
                'https://www.youtube.com/embed/xIsIBJ0bID8',
                'https://www.youtube.com/embed/hIkCmbvAHQQ',
                'https://www.youtube.com/embed/pU3bIib9MYw'
            ],
            'features': ['Beach Camping', 'Trekking Gear', 'BBQ Dinner', 'Snorkeling', 'Sunset Cruise', 'Temple Visit'],
            'ambient_sound': {'type': 'ocean', 'label': 'Ocean Waves & Seagulls', 'icon': 'fa-water'},
            'tags': ['Beach', 'Trekking', 'Coastal'],
            'location': {'lat': 14.5479, 'lng': 74.3188, 'name': 'Gokarna, Karnataka'},
            'itinerary': [
                {'day': 1, 'title': 'Arrival & Om Beach', 'desc': 'Arrive in Gokarna. Relax at Om Beach and enjoy the sunset.'},
                {'day': 2, 'title': 'Beach Trekking', 'desc': 'Trek through Half Moon Beach to Paradise Beach.'},
                {'day': 3, 'title': 'Mahabaleshwar Temple & Departure', 'desc': 'Visit the ancient temple before departure.'}
            ],
            'accessibility': {'wheelchair': 1, 'family': 3, 'senior': 2}
        },
        'bandipur': {
            'id': 'bandipur',
            'agency_id': 'A2002',
            'tag': 'Wildlife',
            'title': 'Bandipur Safari & Kabini',
            'description': 'Embark on a wildlife adventure through the Bandipur National Park and Kabini backwaters. Spot elephants, deer, and if you\'re lucky, a tiger on your safari.',
            'duration': '2 Days / 1 Night Jungle Lodge',
            'old_price': 15000,
            'price': 13500,
            'discount': '10% OFF',
            'image': 'https://images.unsplash.com/photo-1628282305596-f99aee2678da?ixlib=rb-4.0.3&auto=format&fit=crop&w=500&q=80',
            'images': [
                'https://images.unsplash.com/photo-1628282305596-f99aee2678da?ixlib=rb-4.0.3&auto=format&fit=crop&w=1200&q=80'
            ],
            'gallery': [
                'https://images.unsplash.com/photo-1628282305596-f99aee2678da?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1549366021-9f761d450615?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1474511320723-9a56873571b7?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1564760055775-d63b17a55c44?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1557050543-4d5f4e07ef46?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1503656142023-618e7d1f435a?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1456926631375-92c8ce872def?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1504006833117-8886a355efbf?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1535338454528-3370d0555f68?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1518709766631-a6a7f45921c3?auto=format&fit=crop&w=1200&q=80'
            ],
            'videos': [
                'https://www.youtube.com/embed/pPH-smkOeL0',
                'https://www.youtube.com/embed/ydYDqZQpim8'
            ],
            'features': ['Jeep Safari', 'Boat Safari', 'Jungle Lodge', 'Naturalist Guide', 'Campfire', 'Nature Walk'],
            'ambient_sound': {'type': 'wildlife', 'label': 'Jungle Night Sounds', 'icon': 'fa-paw'},
            'tags': ['Wildlife Safari', 'Jungle Lodge', 'Nature'],
            'location': {'lat': 11.6690, 'lng': 76.6343, 'name': 'Bandipur, Karnataka'},
            'itinerary': [
                {'day': 1, 'title': 'Arrival & Evening Safari', 'desc': 'Check-in to the jungle lodge. Evening jeep safari in Bandipur National Park.'},
                {'day': 2, 'title': 'Kabini Backwaters & Departure', 'desc': 'Morning boat safari on the Kabini backwaters before heading home.'}
            ],
            'accessibility': {'wheelchair': 2, 'family': 4, 'senior': 2}
        },
        'royal-mysuru-heritage-tria': {
            'id': 'royal-mysuru-heritage-tria',
            'agency_id': 'A2001',
            'tag': 'Heritage',
            'title': 'Royal Mysuru Heritage Trail',
            'description': 'Experience the royal charm of Mysuru with palace grandeur, spiritual landmarks, and scenic viewpoints. This package covers the iconic Mysore Palace, Chamundi Hills, Brindavan Gardens, St. Philomenas Cathedral, and local market exploration. Includes comfortable stay, guided sightseeing, and cultural experiences.',
            'duration': '3 Days / 2 Nights Heritage Tour',
            'old_price': 10000,
            'price': 7999,
            'discount': '20% OFF',
            'image': 'https://images.unsplash.com/photo-1600100397608-e1b4af20e974?auto=format&fit=crop&w=500&q=80',
            'images': [
                'https://images.unsplash.com/photo-1600100397608-e1b4af20e974?auto=format&fit=crop&w=1200&q=80'
            ],
            'gallery': [
                'https://images.unsplash.com/photo-1600100397608-e1b4af20e974?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1590050751776-5fee6e8da747?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1524492412937-b28074a5d7da?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1564507592333-c60657eea523?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1548013146-72479768bada?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1585135497273-1a86d9d54789?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1570168007204-dfb528c6958f?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1609766856923-7e0a0c06e54d?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1477587458883-47145ed94245?auto=format&fit=crop&w=1200&q=80',
                'https://images.unsplash.com/photo-1596707328608-f404dc7ff957?auto=format&fit=crop&w=1200&q=80'
            ],
            'videos': [
                'https://www.youtube.com/embed/wXx3hCuzhAo',
                'https://www.youtube.com/embed/PNjG22Gbo6U'
            ],
            'features': ['Palace Tour', 'Guided Sightseeing', 'Heritage Walk', 'Temple Visit', 'Garden Tour', 'Local Market Experience'],
            'ambient_sound': {'type': 'heritage', 'label': 'Royal Palace Bells', 'icon': 'fa-landmark'},
            'tags': ['Heritage', 'Palace Tour', 'Cultural'],
            'location': {'lat': 12.3051, 'lng': 76.6551, 'name': 'Mysuru, Karnataka'},
            'itinerary': [
                {'day': 1, 'title': 'Arrival & Mysore Palace', 'desc': 'Arrive in Mysuru and check in. Afternoon visit to the Mysore Palace with guided tour of Durbar Hall, Royal Gallery, and palace grounds. Evening light show.'},
                {'day': 2, 'title': 'Chamundi Hills & Brindavan Gardens', 'desc': 'Morning trek up Chamundi Hills with temple visit and Nandi statue. Afternoon at Brindavan Gardens with musical fountain show.'},
                {'day': 3, 'title': 'St. Philomenas Cathedral & Departure', 'desc': 'Visit St. Philomenas Cathedral and Devaraja Market for local souvenirs before departure.'}
            ],
            'accessibility': {'wheelchair': 4, 'family': 5, 'senior': 4}
        }
    }
}

# Keep fallback mode empty so agencies start with no preloaded packages.
MOCK_DATABASE['packages'] = {}

# --- Firebase Realtime Database Helpers ---
# These functions abstract all DB access. They use Realtime Database when available,
# otherwise fall back to the in-memory MOCK_DATABASE.

def db_clear_old_data():
    """Clear ALL old seeded packages from Firebase for a fresh start."""
    if not FIREBASE_ENABLED:
        return
    try:
        ref = firebase_db.reference('/packages')
        existing = ref.get()
        if existing and isinstance(existing, dict):
            # Wipe all packages - fresh start
            ref.delete()
            print(f"🧹 Cleared all {len(existing)} old packages from Firebase. Fresh start!")
        else:
            print("ℹ️  No packages in Firebase to clean up.")
    except Exception as e:
        print(f"⚠️  Cleanup failed: {e}")

def db_get_all_packages():
    """Get all packages as a dict of {id: package_data}."""
    data = {}
    if FIREBASE_ENABLED:
        try:
            ref = firebase_db.reference('/packages')
            data = ref.get() or {}
            if not isinstance(data, dict):
                data = {}
        except Exception as e:
            print(f"⚠️  Firebase read error: {e}")
            data = {}
    else:
        data = MOCK_DATABASE['packages']

    recent_booking_map = _get_recent_bookings_map()
    for pkg in data.values():
        if isinstance(pkg, dict):
            _attach_carbon_score(pkg)
            _attach_recent_booking_label(pkg, recent_booking_map)
    return data

def db_get_package(pkg_id):
    """Get a single package by ID."""
    data = None
    if FIREBASE_ENABLED:
        try:
            ref = firebase_db.reference(f'/packages/{pkg_id}')
            data = ref.get()
        except Exception as e:
            print(f"⚠️  Firebase read error: {e}")
            data = None
    else:
        data = MOCK_DATABASE['packages'].get(pkg_id)

    if isinstance(data, dict):
        _attach_carbon_score(data)
        _attach_recent_booking_label(data)
        _ensure_hyperlocal_stories(data, persist=not bool(data.get('hyperlocal_stories')))
    return data

def db_add_package(pkg_id, pkg_data):
    """Add a new package."""
    if FIREBASE_ENABLED:
        try:
            ref = firebase_db.reference(f'/packages/{pkg_id}')
            ref.set(pkg_data)
            return True
        except Exception as e:
            print(f"⚠️  Firebase write error: {e}")
            return False
    MOCK_DATABASE['packages'][pkg_id] = pkg_data
    return True

def db_update_package(pkg_id, pkg_data):
    """Update an existing package."""
    if FIREBASE_ENABLED:
        try:
            ref = firebase_db.reference(f'/packages/{pkg_id}')
            ref.update(pkg_data)
            return True
        except Exception as e:
            print(f"⚠️  Firebase update error: {e}")
            return False
    if pkg_id in MOCK_DATABASE['packages']:
        MOCK_DATABASE['packages'][pkg_id].update(pkg_data)
    return True

def db_delete_package(pkg_id):
    """Delete a package by ID."""
    if FIREBASE_ENABLED:
        try:
            ref = firebase_db.reference(f'/packages/{pkg_id}')
            ref.delete()
            return True
        except Exception as e:
            print(f"⚠️  Firebase delete error: {e}")
            return False
    if pkg_id in MOCK_DATABASE['packages']:
        del MOCK_DATABASE['packages'][pkg_id]
    return True

def db_get_packages_by_agency(agency_id):
    """Get packages belonging to a specific agency."""
    if FIREBASE_ENABLED:
        try:
            ref = firebase_db.reference('/packages')
            data = ref.get()
            if data and isinstance(data, dict):
                packages = [pkg for pkg in data.values() if pkg.get('agency_id') == agency_id]
                recent_booking_map = _get_recent_bookings_map()
                for pkg in packages:
                    if isinstance(pkg, dict):
                        _attach_carbon_score(pkg)
                        _attach_recent_booking_label(pkg, recent_booking_map)
                return packages
            return []
        except Exception as e:
            print(f"⚠️  Firebase query error: {e}")
    packages = [pkg for pkg in MOCK_DATABASE['packages'].values() if pkg.get('agency_id') == agency_id]
    recent_booking_map = _get_recent_bookings_map()
    for pkg in packages:
        if isinstance(pkg, dict):
            _attach_carbon_score(pkg)
            _attach_recent_booking_label(pkg, recent_booking_map)
    return packages


def _get_recent_bookings_map():
    """Return map {package_id: latest_booked_on_str} for social-proof labels."""
    latest_by_package = {}
    bookings_data = {}

    if FIREBASE_ENABLED:
        try:
            bookings_data = firebase_db.reference('/bookings').get() or {}
            if not isinstance(bookings_data, dict):
                bookings_data = {}
        except Exception as e:
            print(f"⚠️  Firebase booking social-proof read error: {e}")
            bookings_data = {}
    else:
        bookings_data = MOCK_DATABASE.get('bookings', {})

    for booking in bookings_data.values():
        if not isinstance(booking, dict):
            continue
        package_id = booking.get('package_id')
        booked_on = booking.get('booked_on', '')
        if not package_id or not booked_on:
            continue
        current = latest_by_package.get(package_id)
        if not current or booked_on > current:
            latest_by_package[package_id] = booked_on

    return latest_by_package


def _humanize_last_booked(booked_on):
    """Convert booking timestamp string to human-readable social-proof text."""
    if not booked_on:
        return ''
    try:
        booked_at = datetime.strptime(booked_on, '%Y-%m-%d %H:%M')
    except Exception:
        return ''

    delta_seconds = int((datetime.now() - booked_at).total_seconds())
    if delta_seconds < 0:
        delta_seconds = 0

    if delta_seconds < 60:
        return 'Last booked just now'
    if delta_seconds < 3600:
        mins = delta_seconds // 60
        return f'Last booked {mins} min ago' if mins == 1 else f'Last booked {mins} mins ago'
    if delta_seconds < 86400:
        hrs = delta_seconds // 3600
        return f'Last booked {hrs} hour ago' if hrs == 1 else f'Last booked {hrs} hours ago'
    days = delta_seconds // 86400
    if days <= 7:
        return f'Last booked {days} day ago' if days == 1 else f'Last booked {days} days ago'
    return f'Last booked on {booked_on.split(" ")[0]}'


def _attach_recent_booking_label(package, recent_booking_map=None):
    if recent_booking_map is None:
        recent_booking_map = _get_recent_bookings_map()
    pkg_id = package.get('id', '')
    booked_on = recent_booking_map.get(pkg_id, '')
    package['last_booked_on'] = booked_on
    package['last_booked_label'] = _humanize_last_booked(booked_on)
    return package


def _story_safe_slug(text):
    cleaned = re.sub(r'[^a-zA-Z0-9]+', '-', (text or '').strip().lower()).strip('-')
    return cleaned or 'package'


def _estimate_story_duration_seconds(narration):
    words = len((narration or '').split())
    # Approx 140 wpm -> ~2.33 words/sec
    seconds = int(max(30, min(60, round(words / 2.33))))
    return seconds


def _build_hyperlocal_story_scripts(package):
    place = (package.get('location', {}) or {}).get('name') or package.get('title', 'this destination')
    title = package.get('title', 'This destination')
    tag = package.get('tag', 'travel')

    stories = [
        {
            'title': 'Origins and Identity',
            'theme': 'history',
            'language': 'en',
            'narration': (
                f'Welcome to {place}. Long before modern tourism, this region grew around trade routes, '
                f'temples, and seasonal communities that shaped its identity. {title} reflects that layered '
                f'past through local architecture, everyday rituals, and stories passed between generations. '
                f'As you explore, notice how old craft traditions and modern life coexist side by side. '
                f'This is not just a stop on a map, but a living cultural landscape.'
            ),
        },
        {
            'title': 'Myths, Legends, and Sacred Memory',
            'theme': 'myth',
            'language': 'en',
            'narration': (
                f'Every corner of {place} carries a legend. Locals often connect hills, rivers, and shrines '
                f'to stories of guardians, saints, and heroic journeys. Even when versions differ from family '
                f'to family, the emotion is the same: respect for land, water, and memory. While enjoying this '
                f'{tag.lower()} experience, listen to local names and symbols. They often reveal how folklore '
                f'quietly guides culture, festivals, and everyday choices in the region.'
            ),
        },
        {
            'title': 'Local Culture Through Everyday Life',
            'theme': 'culture',
            'language': 'en',
            'narration': (
                f'To understand {place}, watch daily rhythms: early markets, temple bells, tea stalls, and '
                f'streets that change mood from morning to evening. Food, textiles, and conversation styles '
                f'carry strong regional character here. During your {title} journey, try one local dish, greet '
                f'people in the local way, and spend a few minutes observing public spaces. Small details often '
                f'create the most meaningful travel memories.'
            ),
        },
    ]

    for s in stories:
        s['duration_sec'] = _estimate_story_duration_seconds(s.get('narration', ''))
    return stories


def _generate_story_audio_file(pkg_id, story_idx, narration, force=False):
    safe_pkg = _story_safe_slug(pkg_id)
    filename = f'{safe_pkg}-story-{story_idx + 1}.mp3'
    abs_path = os.path.join(STORY_AUDIO_FOLDER, filename)
    rel_url = f'/static/uploads/stories/{filename}'

    if os.path.exists(abs_path) and not force:
        return rel_url

    if not GTTS_AVAILABLE:
        return ''

    try:
        tts = gTTS(text=narration, lang='en', slow=False)
        tts.save(abs_path)
        return rel_url
    except Exception as e:
        print(f"⚠️  Story audio generation error: {e}")
        return ''


def _ensure_hyperlocal_stories(package, persist=False, force=False):
    """Attach short location-based stories and audio tracks to a package."""
    existing = package.get('hyperlocal_stories')
    if existing and isinstance(existing, list) and len(existing) > 0:
        if force:
            existing = []
        else:
        # Ensure missing audio links can still be generated.
            changed = False
            for idx, s in enumerate(existing):
                if not isinstance(s, dict):
                    continue
                if not s.get('duration_sec'):
                    s['duration_sec'] = _estimate_story_duration_seconds(s.get('narration', ''))
                    changed = True
                if not s.get('audio_url') and s.get('narration'):
                    audio_url = _generate_story_audio_file(package.get('id', 'package'), idx, s.get('narration', ''))
                    if audio_url:
                        s['audio_url'] = audio_url
                        changed = True
            if changed:
                package['hyperlocal_stories'] = existing
                if persist and package.get('id'):
                    db_update_package(package['id'], {'hyperlocal_stories': existing})
            return package

    scripts = _build_hyperlocal_story_scripts(package)
    stories = []
    for idx, s in enumerate(scripts):
        audio_url = _generate_story_audio_file(package.get('id', 'package'), idx, s['narration'], force=force)
        stories.append({
            'id': f"{_story_safe_slug(package.get('id', 'package'))}-story-{idx + 1}",
            'order': idx + 1,
            'title': s['title'],
            'theme': s['theme'],
            'language': s['language'],
            'duration_sec': s['duration_sec'],
            'narration': s['narration'],
            'audio_url': audio_url,
        })

    package['hyperlocal_stories'] = stories
    if persist and package.get('id'):
        db_update_package(package['id'], {'hyperlocal_stories': stories})
    return package


@app.route('/agency/story/regenerate/<id>', methods=['POST'])
def agency_regenerate_package_stories(id):
    if session.get('role') != 'agency':
        return jsonify({'error': 'Unauthorized'}), 403

    package = db_get_package(id)
    if not package:
        return jsonify({'error': 'Package not found'}), 404

    if package.get('agency_id') != session.get('user_id'):
        return jsonify({'error': 'You do not have permission to regenerate stories for this package.'}), 403

    _ensure_hyperlocal_stories(package, persist=True, force=True)
    return jsonify({'success': True, 'message': 'Hyperlocal stories regenerated successfully.'})


def _extract_trip_days(duration_text):
    if not duration_text:
        return 2
    match = re.search(r'(\d+)\s*day', duration_text, flags=re.IGNORECASE)
    if match:
        try:
            return max(1, int(match.group(1)))
        except ValueError:
            return 2
    return 2


def _infer_transport_type(package):
    explicit = (package.get('transport_type') or '').strip().lower()
    if explicit:
        return explicit

    haystack = ' '.join([
        str(package.get('duration', '')),
        str(package.get('description', '')),
        ' '.join(package.get('features', []) if isinstance(package.get('features', []), list) else []),
    ]).lower()

    if 'train' in haystack or 'rail' in haystack:
        return 'train'
    if 'bus' in haystack or 'coach' in haystack:
        return 'bus'
    if 'flight' in haystack or 'air' in haystack:
        return 'flight'
    if 'shared' in haystack and ('cab' in haystack or 'tempo' in haystack or 'van' in haystack):
        return 'shared_cab'
    if 'cab' in haystack or 'taxi' in haystack or 'car' in haystack or 'transport' in haystack:
        return 'private_cab'
    return 'mixed'


def _calculate_carbon_score(duration_text, transport_type):
    base_map = {
        'train': 92,
        'bus': 82,
        'shared_cab': 74,
        'self_drive': 62,
        'private_cab': 56,
        'flight': 28,
        'mixed': 66,
    }
    days = _extract_trip_days(duration_text)
    transport = (transport_type or 'mixed').strip().lower()
    base = base_map.get(transport, 60)
    duration_penalty = min(30, max(0, days - 1) * 4)
    score = int(max(10, min(100, base - duration_penalty)))

    if score >= 80:
        level = 'Eco Smart'
        badge = 'low-impact'
    elif score >= 60:
        level = 'Balanced'
        badge = 'medium-impact'
    else:
        level = 'High Impact'
        badge = 'high-impact'

    return {
        'score': score,
        'days': days,
        'level': level,
        'badge': badge,
        'transport_type': transport,
    }


def _attach_carbon_score(package):
    transport = _infer_transport_type(package)
    package['transport_type'] = transport
    package['carbon_score'] = _calculate_carbon_score(package.get('duration', ''), transport)
    return package


def _get_users_map():
    """Get all users as dict {user_id: user_data}."""
    if FIREBASE_ENABLED:
        try:
            users = firebase_db.reference('/users').get()
            if users and isinstance(users, dict):
                return users
        except Exception as e:
            print(f"⚠️  Firebase users query error: {e}")
        return {}
    return MOCK_DATABASE.get('users', {})


def _get_agency_user(agency_id):
    users = _get_users_map()
    user = users.get(agency_id)
    if user and user.get('role') == 'agency':
        return agency_id, user
    return None, None


def _get_all_agency_users():
    users = _get_users_map()
    return [(uid, udata) for uid, udata in users.items() if udata.get('role') == 'agency']


def _save_notification(agency_id, payload):
    notification_id = payload.get('id') or uuid.uuid4().hex[:12]
    payload['id'] = notification_id
    if FIREBASE_ENABLED:
        try:
            firebase_db.reference(f'/notifications/{agency_id}/{notification_id}').set(payload)
            return True
        except Exception as e:
            print(f"⚠️  Firebase notification write error: {e}")
            return False
    if 'notifications' not in MOCK_DATABASE:
        MOCK_DATABASE['notifications'] = {}
    if agency_id not in MOCK_DATABASE['notifications']:
        MOCK_DATABASE['notifications'][agency_id] = {}
    MOCK_DATABASE['notifications'][agency_id][notification_id] = payload
    return True


def _get_notifications_for_agency(agency_id, limit=20):
    notifications = []
    if FIREBASE_ENABLED:
        try:
            data = firebase_db.reference(f'/notifications/{agency_id}').get()
            if data and isinstance(data, dict):
                notifications = list(data.values())
        except Exception as e:
            print(f"⚠️  Firebase notification read error: {e}")
    else:
        notifications = list(MOCK_DATABASE.get('notifications', {}).get(agency_id, {}).values())
    notifications.sort(key=lambda n: n.get('created_at_ts', 0), reverse=True)
    return notifications[:limit]


def _count_unread_notifications(agency_id):
    notifications = _get_notifications_for_agency(agency_id, limit=200)
    return sum(1 for n in notifications if not n.get('is_read'))


def _mark_notification_read(agency_id, notification_id):
    if FIREBASE_ENABLED:
        try:
            firebase_db.reference(f'/notifications/{agency_id}/{notification_id}/is_read').set(True)
            return True
        except Exception as e:
            print(f"⚠️  Firebase notification update error: {e}")
            return False
    bucket = MOCK_DATABASE.get('notifications', {}).get(agency_id, {})
    if notification_id in bucket:
        bucket[notification_id]['is_read'] = True
        return True
    return False


def _mark_all_notifications_read(agency_id):
    notifications = _get_notifications_for_agency(agency_id, limit=500)
    for n in notifications:
        if n.get('id') and not n.get('is_read'):
            _mark_notification_read(agency_id, n['id'])


def _send_email_alert(to_email, subject, body):
    if not to_email:
        return False
    host = app.config.get('SMTP_HOST')
    user = app.config.get('SMTP_USER')
    password = app.config.get('SMTP_PASSWORD')
    sender = app.config.get('EMAIL_FROM') or user
    if not host or not user or not password or not sender:
        return False
    try:
        msg = EmailMessage()
        msg['Subject'] = subject
        msg['From'] = sender
        msg['To'] = to_email
        msg.set_content(body)

        with smtplib.SMTP(host, app.config.get('SMTP_PORT', 587), timeout=10) as smtp:
            if app.config.get('SMTP_USE_TLS', True):
                smtp.starttls()
            smtp.login(user, password)
            smtp.send_message(msg)
        return True
    except Exception as e:
        print(f"⚠️  Email alert error: {e}")
        return False


def _normalize_whatsapp_to(value):
    if not value:
        return ''
    raw = str(value).strip().replace(' ', '').replace('-', '')
    if raw.startswith('whatsapp:'):
        return raw
    if raw.startswith('+'):
        return f'whatsapp:{raw}'
    # Accept plain digit numbers and normalize to E.164-like format.
    digits_only = ''.join(ch for ch in raw if ch.isdigit())
    if len(digits_only) >= 10:
        if raw.startswith('91') and len(digits_only) == 12:
            return f'whatsapp:+{digits_only}'
        if len(digits_only) == 10:
            return f'whatsapp:+91{digits_only}'
        return f'whatsapp:+{digits_only}'
    return ''


def _resolve_whatsapp_recipient(primary_value, fallback_value):
    """Return normalized WhatsApp recipient, falling back when primary is invalid."""
    primary = _normalize_whatsapp_to(primary_value)
    if primary:
        return primary
    return _normalize_whatsapp_to(fallback_value)


def _send_whatsapp_alert(to_number, message):
    sid = app.config.get('TWILIO_ACCOUNT_SID')
    token = app.config.get('TWILIO_AUTH_TOKEN')
    sender = app.config.get('TWILIO_WHATSAPP_FROM')
    recipient = _normalize_whatsapp_to(to_number)
    if not sid or not token or not sender or not recipient:
        return False
    try:
        from twilio.rest import Client
        client = Client(sid, token)
        client.messages.create(from_=sender, body=message, to=recipient)
        return True
    except Exception as e:
        print(f"⚠️  WhatsApp alert error: {e}")
        return False


def _dispatch_booking_alerts(booking):
    """Send in-app, email and WhatsApp alerts for a new booking."""
    agency_id = booking.get('agency_id', '')
    package_title = booking.get('package_title', 'Package')
    booking_id = booking.get('id', '')
    customer_name = booking.get('customer_name', 'Traveler')
    travelers = booking.get('travelers', 1)
    travel_date = booking.get('travel_date', '')
    amount = booking.get('amount', 0)
    total_amount = amount * travelers
    now_ts = int(time.time())
    now_str = datetime.now().strftime('%Y-%m-%d %H:%M')

    target_agencies = []
    uid, user = _get_agency_user(agency_id)
    if uid and user:
        target_agencies.append((uid, user))
    elif agency_id:
        # Preserve in-app alert bucket for legacy package owner IDs.
        target_agencies.append((agency_id, {}))
    else:
        target_agencies = _get_all_agency_users()

    for target_uid, agency_user in target_agencies:
        payload = {
            'id': uuid.uuid4().hex[:12],
            'type': 'booking_created',
            'title': 'New booking request',
            'message': f'{customer_name} booked {package_title} for {travelers} traveler(s).',
            'booking_id': booking_id,
            'package_id': booking.get('package_id', ''),
            'package_title': package_title,
            'customer_name': customer_name,
            'travel_date': travel_date,
            'total_amount': total_amount,
            'is_read': False,
            'created_at': now_str,
            'created_at_ts': now_ts,
        }
        _save_notification(target_uid, payload)

        email_to = agency_user.get('email', '')
        email_subject = f'New Booking Alert: {package_title} ({booking_id})'
        email_body = (
            f'Hello {agency_user.get("name", "Agency")},\n\n'
            f'You have received a new booking request.\n\n'
            f'Booking ID: {booking_id}\n'
            f'Package: {package_title}\n'
            f'Customer: {customer_name}\n'
            f'Travel Date: {travel_date}\n'
            f'Travelers: {travelers}\n'
            f'Total Amount: INR {total_amount}\n\n'
            f'Please review it in your agency dashboard.\n'
        )
        _send_email_alert(email_to, email_subject, email_body)

        agency_phone = agency_user.get('phone') or agency_user.get('whatsapp')
        fallback_phone = app.config.get('DEFAULT_AGENCY_WHATSAPP_TO')
        whatsapp_recipient = _resolve_whatsapp_recipient(agency_phone, fallback_phone)
        whatsapp_text = (
            f'New booking request!\n'
            f'Booking: {booking_id}\n'
            f'Package: {package_title}\n'
            f'Customer: {customer_name}\n'
            f'Date: {travel_date}\n'
            f'Travelers: {travelers}\n'
            f'Total: INR {total_amount}'
        )
        _send_whatsapp_alert(whatsapp_recipient, whatsapp_text)

# One-time cleanup already done — disable to protect new packages
# db_clear_old_data()

@app.route('/')
def index():
    return render_template('index.html')

@app.route('/api/packages')
def get_packages():
    return db_get_all_packages()

@app.route('/api/package/<id>')
def api_get_package(id):
    package = db_get_package(id)
    if not package:
        return jsonify({'error': 'Package not found'}), 404
    return jsonify(package)

@app.route('/package/<id>')
def package_details(id):
    package = db_get_package(id)
    if not package:
        return "Package not found", 404
    return render_template('package-details.html', package=package)

@app.route('/api/weather')
def get_weather():
    """Fetch current weather + 7-day forecast with resilient provider fallback."""
    lat = request.args.get('lat', type=float)
    lng = request.args.get('lng', type=float)
    if lat is None or lng is None:
        return jsonify({'error': 'lat and lng required'}), 400
    cache_key = _weather_cache_key(lat, lng)
    cached = cache_get(cache_key)
    if cached:
        return jsonify(cached)

    stale = cache_get_stale(cache_key)

    try:
        data, source, warning = _fetch_weather_with_fallback(lat, lng, forecast_days=7)
        result = data.copy()
        if warning:
            result['data_quality'] = {
                'provider': source,
                'warning': warning
            }
        cache_set(cache_key, result, _CACHE_TTL['weather'])
        return jsonify(result)
    except Exception as e:
        if stale:
            stale_result = stale.copy()
            stale_result['data_quality'] = {
                'stale': True,
                'warning': 'Live weather provider temporarily unavailable; showing last cached update.'
            }
            return jsonify(stale_result)
        return jsonify({'error': str(e)}), 500


@app.route('/api/sun-times')
def get_sun_times():
    """Fetch sunrise, sunset & golden hour times using free Sunrise-Sunset API."""
    lat = request.args.get('lat', type=float)
    lng = request.args.get('lng', type=float)
    if lat is None or lng is None:
        return jsonify({'error': 'lat and lng required'}), 400
    cache_key = f'sun:{lat:.3f},{lng:.3f}'
    cached = cache_get(cache_key)
    if cached:
        return jsonify(cached)
    try:
        import requests as req
        url = f'https://api.sunrise-sunset.org/json?lat={lat}&lng={lng}&formatted=0'
        resp = req.get(url, timeout=5)
        resp.raise_for_status()
        data = resp.json()
        if data.get('status') != 'OK':
            return jsonify({'error': 'API returned non-OK status'}), 500
        result = data['results']
        cache_set(cache_key, result, _CACHE_TTL['sun_times'])
        return jsonify(result)
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/api/nearby-restaurants')
def get_nearby_restaurants():
    """Fetch nearby restaurants using free Overpass (OpenStreetMap) API."""
    lat = request.args.get('lat', type=float)
    lng = request.args.get('lng', type=float)
    radius = request.args.get('radius', 3000, type=int)  # 3km default
    if lat is None or lng is None:
        return jsonify({'error': 'lat and lng required'}), 400
    cache_key = f'rest:{lat:.3f},{lng:.3f}:{radius}'
    cached = cache_get(cache_key)
    if cached:
        return jsonify(cached)
    try:
        import requests as req
        query = f"""
        [out:json][timeout:10];
        (
          node["amenity"="restaurant"](around:{radius},{lat},{lng});
          node["amenity"="cafe"](around:{radius},{lat},{lng});
          node["amenity"="fast_food"](around:{radius},{lat},{lng});
        );
        out body 6;
        """
        resp = req.post('https://overpass-api.de/api/interpreter', data={'data': query}, timeout=10)
        resp.raise_for_status()
        data = resp.json()
        restaurants = []
        for el in data.get('elements', []):
            tags = el.get('tags', {})
            name = tags.get('name', '')
            if not name:
                continue
            restaurants.append({
                'name': name,
                'cuisine': tags.get('cuisine', ''),
                'type': tags.get('amenity', 'restaurant'),
                'phone': tags.get('phone', tags.get('contact:phone', '')),
                'website': tags.get('website', ''),
                'opening_hours': tags.get('opening_hours', ''),
                'vegetarian': 'yes' in tags.get('diet:vegetarian', ''),
                'lat': el.get('lat'),
                'lng': el.get('lon'),
                'rating': tags.get('stars', '')
            })
        result = {'restaurants': restaurants}
        cache_set(cache_key, result, _CACHE_TTL['restaurants'])
        return jsonify(result)
    except Exception as e:
        # Overpass occasionally rate-limits; keep UI functional with empty data.
        print(f"⚠️  Nearby restaurants fallback: {e}")
        return jsonify({
            'restaurants': [],
            'warning': 'Restaurant data temporarily unavailable. Please try again later.'
        })


@app.route('/api/local-trust-score')
def get_local_trust_score():
    """Compute local trust graph score using live weather + OSM signals.

    Components:
    - safety_score: weather severity + wind + humidity + medical fallback
    - crowd_score: attraction density + weekend pressure + rain moderation
    - road_score: road network density + weather reliability
    - medical_score: nearest hospital proximity
    """
    lat = request.args.get('lat', type=float)
    lng = request.args.get('lng', type=float)
    tag = (request.args.get('tag', '') or '').strip().lower()

    if lat is None or lng is None:
        return jsonify({'error': 'lat and lng required'}), 400

    cache_key = f'trust:{lat:.3f},{lng:.3f}:{tag}'
    cached = cache_get(cache_key)
    if cached:
        return jsonify(cached)

    try:
        import requests as req

        # 1) Weather context (resilient fallback + stale-cache strategy)
        weather_warning = ''
        weather_cache_key = _weather_cache_key(lat, lng)
        weather_data = cache_get(weather_cache_key)
        if not weather_data:
            weather_data = cache_get_stale(weather_cache_key)

        if not weather_data:
            try:
                weather_data, weather_source, weather_warning = _fetch_weather_with_fallback(lat, lng, forecast_days=2)
                cache_set(weather_cache_key, weather_data, _CACHE_TTL['weather'])
                if weather_warning:
                    weather_warning = f'{weather_warning} Source: {weather_source}.'
            except Exception as weather_err:
                weather_warning = f'Weather service unavailable: {weather_err}'
                weather_data = {
                    'current': {
                        'weather_code': 3,
                        'wind_speed_10m': 14,
                        'relative_humidity_2m': 65,
                        'temperature_2m': 27,
                    },
                    'daily': {
                        'precipitation_probability_max': [20]
                    }
                }

        current = weather_data.get('current', {}) or {}
        daily = weather_data.get('daily', {}) or {}
        weather_code = int(current.get('weather_code', 0) or 0)
        wind_kmh = float(current.get('wind_speed_10m', 0) or 0)
        humidity = float(current.get('relative_humidity_2m', 0) or 0)
        rain_prob = 0
        if isinstance(daily.get('precipitation_probability_max'), list) and daily.get('precipitation_probability_max'):
            rain_prob = int(daily.get('precipitation_probability_max')[0] or 0)

        # 2) OSM context (hospitals, attractions, roads)
        overpass_query = f"""
        [out:json][timeout:12];
        (
          node["amenity"="hospital"](around:10000,{lat},{lng});
          node["amenity"="clinic"](around:10000,{lat},{lng});
          node["tourism"~"attraction|museum|viewpoint|theme_park|zoo"](around:3500,{lat},{lng});
          way["highway"~"motorway|trunk|primary|secondary|tertiary"](around:5000,{lat},{lng});
        );
        out center 80;
        """
        elements = []
        osm_warning = ''
        try:
            osm_resp = req.post('https://overpass-api.de/api/interpreter', data={'data': overpass_query}, timeout=14)
            osm_resp.raise_for_status()
            elements = (osm_resp.json() or {}).get('elements', [])
        except Exception as osm_err:
            osm_warning = str(osm_err)
            print(f"⚠️  Trust-score OSM fallback: {osm_warning}")

        hospital_points = []
        attraction_count = 0
        road_count = 0

        for el in elements:
            tags = el.get('tags', {}) or {}
            amenity = tags.get('amenity', '')
            tourism = tags.get('tourism', '')
            highway = tags.get('highway', '')

            if amenity in ('hospital', 'clinic'):
                h_lat = el.get('lat') if el.get('lat') is not None else (el.get('center') or {}).get('lat')
                h_lng = el.get('lon') if el.get('lon') is not None else (el.get('center') or {}).get('lon')
                if h_lat is not None and h_lng is not None:
                    hospital_points.append((float(h_lat), float(h_lng)))

            if tourism in ('attraction', 'museum', 'viewpoint', 'theme_park', 'zoo'):
                attraction_count += 1

            if highway in ('motorway', 'trunk', 'primary', 'secondary', 'tertiary'):
                road_count += 1

        nearest_hospital_km = None
        if hospital_points:
            nearest_hospital_km = min(_haversine_km(lat, lng, hp[0], hp[1]) for hp in hospital_points)

        # --- Component Scoring ---
        # Medical proximity
        if nearest_hospital_km is None:
            medical_score = 38
        elif nearest_hospital_km <= 2:
            medical_score = 95
        elif nearest_hospital_km <= 5:
            medical_score = 82
        elif nearest_hospital_km <= 10:
            medical_score = 68
        else:
            medical_score = 52

        # Safety (weather + wind + humidity + medical buffer)
        safety_score = 85
        if weather_code >= 95:
            safety_score -= 35
        elif weather_code >= 80:
            safety_score -= 22
        elif weather_code >= 61:
            safety_score -= 16
        elif weather_code >= 51:
            safety_score -= 10
        if wind_kmh > 45:
            safety_score -= 18
        elif wind_kmh > 30:
            safety_score -= 10
        if humidity > 85:
            safety_score -= 5
        safety_score += int((medical_score - 50) * 0.15)

        # Crowd behavior (pressure + moderation)
        weekday_idx = datetime.now().weekday()  # 0 Monday ... 6 Sunday
        weekend_penalty = 12 if weekday_idx >= 5 else 0
        attraction_penalty = min(28, attraction_count * 2)
        rain_relief = min(14, rain_prob // 6)
        tag_bonus = 0
        if tag in ('heritage', 'pilgrimage', 'weekend getaway'):
            tag_bonus = -4
        crowd_score = 82 - weekend_penalty - attraction_penalty + rain_relief + tag_bonus

        # Road reliability (network + weather impact)
        road_bonus = min(12, road_count // 8)
        rain_road_penalty = min(24, rain_prob // 3)
        wind_road_penalty = 10 if wind_kmh > 35 else (5 if wind_kmh > 22 else 0)
        road_score = 68 + road_bonus - rain_road_penalty - wind_road_penalty

        # Clamp scores
        safety_score = max(10, min(100, int(round(safety_score))))
        crowd_score = max(10, min(100, int(round(crowd_score))))
        road_score = max(10, min(100, int(round(road_score))))
        medical_score = max(10, min(100, int(round(medical_score))))

        overall = int(round(
            safety_score * 0.35 +
            crowd_score * 0.2 +
            road_score * 0.25 +
            medical_score * 0.2
        ))

        if overall >= 80:
            trust_level = 'High Trust'
            trust_color = 'high'
        elif overall >= 60:
            trust_level = 'Moderate Trust'
            trust_color = 'medium'
        else:
            trust_level = 'Caution Advised'
            trust_color = 'low'

        weakest = min(
            [('Safety', safety_score), ('Crowd', crowd_score), ('Road', road_score), ('Medical', medical_score)],
            key=lambda x: x[1]
        )[0]

        recommendation_map = {
            'Safety': 'Prefer daylight visits, keep emergency contacts handy, and avoid isolated stretches in bad weather.',
            'Crowd': 'Visit major spots early morning, pre-book entries, and keep buffer time for queues.',
            'Road': 'Use reliable cabs, avoid late-night intercity travel in rain, and keep a route backup.',
            'Medical': 'Share nearest hospital route with co-travelers and carry essentials/first-aid before departure.',
        }

        result = {
            'overall_score': overall,
            'trust_level': trust_level,
            'trust_color': trust_color,
            'components': {
                'safety_score': safety_score,
                'crowd_score': crowd_score,
                'road_score': road_score,
                'medical_score': medical_score,
            },
            'signals': {
                'rain_probability': rain_prob,
                'wind_kmh': round(wind_kmh, 1),
                'attraction_density': attraction_count,
                'road_links': road_count,
                'nearest_hospital_km': round(nearest_hospital_km, 2) if nearest_hospital_km is not None else None,
            },
            'focus_area': weakest,
            'recommendation': recommendation_map.get(weakest, 'Travel with normal precautions.'),
        }

        if osm_warning:
            result['data_quality'] = {
                'osm_available': False,
                'warning': 'OSM context temporarily unavailable; score uses weather-priority fallback.'
            }
        if weather_warning:
            result.setdefault('data_quality', {})
            result['data_quality']['weather_available'] = False
            result['data_quality']['weather_warning'] = weather_warning

        cache_set(cache_key, result, _CACHE_TTL['trust_score'])
        return jsonify(result)
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/search')
def search():
    origin = request.args.get('origin', '')
    destination = request.args.get('destination', '')
    all_packages = db_get_all_packages()
    results = []
    for pkg in all_packages.values():
        if destination.lower() in pkg['title'].lower() or destination.lower() in pkg['tag'].lower() or not destination:
            results.append(pkg)
    return render_template('search-results.html', results=results, query=destination or origin)

@app.route('/book', methods=['POST'])
def book_package():
    if not session.get('user_id'):
        flash('Please login to book a package.', 'error')
        return redirect(url_for('login'))

    pkg_id = request.form.get('package_id', '').strip()
    travel_date = request.form.get('travel_date', '').strip()
    travelers = request.form.get('travelers', '1').strip()
    customer_name = request.form.get('customer_name', session.get('name', '')).strip()
    customer_phone = request.form.get('customer_phone', '').strip()
    customer_email = request.form.get('customer_email', '').strip()

    if not pkg_id or not travel_date:
        flash('Package and travel date are required.', 'error')
        return redirect(request.referrer or url_for('index'))

    package = db_get_package(pkg_id)
    if not package:
        flash('Package not found.', 'error')
        return redirect(url_for('index'))

    booking_id = uuid.uuid4().hex[:10].upper()
    booking = {
        'id': booking_id,
        'package_id': pkg_id,
        'package_title': package.get('title', ''),
        'package_image': package.get('image', ''),
        'agency_id': package.get('agency_id', ''),
        'user_id': session.get('user_id'),
        'customer_name': customer_name,
        'customer_phone': customer_phone,
        'customer_email': customer_email,
        'travel_date': travel_date,
        'travelers': int(travelers) if travelers.isdigit() else 1,
        'amount': package.get('price', 0),
        'status': 'pending',
        'booked_on': datetime.now().strftime('%Y-%m-%d %H:%M'),
    }

    # Save booking
    if FIREBASE_ENABLED:
        try:
            firebase_db.reference(f'/bookings/{booking_id}').set(booking)
        except Exception as e:
            print(f"⚠️  Firebase booking write error: {e}")
            flash('Failed to submit booking. Please try again.', 'error')
            return redirect(request.referrer or url_for('index'))
    else:
        if 'bookings' not in MOCK_DATABASE:
            MOCK_DATABASE['bookings'] = {}
        MOCK_DATABASE['bookings'][booking_id] = booking

    # Fire notification pipeline after successful booking write.
    try:
        _dispatch_booking_alerts(booking)
    except Exception as e:
        print(f"⚠️  Booking notification pipeline error: {e}")

    flash(f'Booking request submitted! Your Booking ID is {booking_id}. The agency will review and approve it shortly.', 'success')
    return redirect(url_for('profile'))


@app.route('/agency/booking/<booking_id>/approve', methods=['POST'])
def agency_approve_booking(booking_id):
    if session.get('role') != 'agency':
        return jsonify({'error': 'Unauthorized'}), 403
    booking = _get_booking(booking_id)
    if not booking:
        return jsonify({'error': 'Booking not found'}), 404
    # Agency dashboard acts as admin moderation inbox for pending requests.
    _update_booking_status(booking_id, 'approved')
    return jsonify({'success': True, 'status': 'approved'})


@app.route('/agency/booking/<booking_id>/reject', methods=['POST'])
def agency_reject_booking(booking_id):
    if session.get('role') != 'agency':
        return jsonify({'error': 'Unauthorized'}), 403
    booking = _get_booking(booking_id)
    if not booking:
        return jsonify({'error': 'Booking not found'}), 404
    # Agency dashboard acts as admin moderation inbox for pending requests.
    _update_booking_status(booking_id, 'rejected')
    return jsonify({'success': True, 'status': 'rejected'})


def _get_booking(booking_id):
    if FIREBASE_ENABLED:
        try:
            return firebase_db.reference(f'/bookings/{booking_id}').get()
        except Exception as e:
            print(f"⚠️  Firebase booking read error: {e}")
            return None
    return MOCK_DATABASE.get('bookings', {}).get(booking_id)


def _update_booking_status(booking_id, status):
    if FIREBASE_ENABLED:
        try:
            firebase_db.reference(f'/bookings/{booking_id}/status').set(status)
        except Exception as e:
            print(f"⚠️  Firebase booking update error: {e}")
    else:
        if booking_id in MOCK_DATABASE.get('bookings', {}):
            MOCK_DATABASE['bookings'][booking_id]['status'] = status


def _get_bookings_for_agency(agency_id):
    """Get all bookings for packages owned by this agency."""
    bookings = []
    if FIREBASE_ENABLED:
        try:
            ref = firebase_db.reference('/bookings')
            data = ref.get()
            if data and isinstance(data, dict):
                bookings = [b for b in data.values() if b.get('agency_id') == agency_id]
        except Exception as e:
            print(f"⚠️  Firebase bookings query error: {e}")
    else:
        bookings = [b for b in MOCK_DATABASE.get('bookings', {}).values() if b.get('agency_id') == agency_id]
    bookings.sort(key=lambda b: b.get('booked_on', ''), reverse=True)
    return bookings


def _get_all_bookings():
    """Get all bookings (admin moderation view)."""
    bookings = []
    if FIREBASE_ENABLED:
        try:
            ref = firebase_db.reference('/bookings')
            data = ref.get()
            if data and isinstance(data, dict):
                bookings = list(data.values())
        except Exception as e:
            print(f"⚠️  Firebase bookings query error: {e}")
    else:
        bookings = list(MOCK_DATABASE.get('bookings', {}).values())
    bookings.sort(key=lambda b: b.get('booked_on', ''), reverse=True)
    return bookings


def _get_bookings_for_user(user_id):
    """Get all bookings made by this user."""
    bookings = []
    if FIREBASE_ENABLED:
        try:
            ref = firebase_db.reference('/bookings')
            data = ref.get()
            if data and isinstance(data, dict):
                bookings = [b for b in data.values() if b.get('user_id') == user_id]
        except Exception as e:
            print(f"⚠️  Firebase bookings query error: {e}")
    else:
        bookings = [b for b in MOCK_DATABASE.get('bookings', {}).values() if b.get('user_id') == user_id]
    bookings.sort(key=lambda b: b.get('booked_on', ''), reverse=True)
    return bookings


@app.route('/agency/notifications')
def agency_notifications():
    if session.get('role') != 'agency':
        return jsonify({'error': 'Unauthorized'}), 403
    agency_id = session.get('user_id')
    notifications = _get_notifications_for_agency(agency_id, limit=20)
    unread_count = _count_unread_notifications(agency_id)
    return jsonify({'notifications': notifications, 'unread_count': unread_count})


@app.route('/agency/notifications/read', methods=['POST'])
def agency_notifications_mark_read():
    if session.get('role') != 'agency':
        return jsonify({'error': 'Unauthorized'}), 403
    agency_id = session.get('user_id')
    data = request.get_json(silent=True) or {}
    notification_id = data.get('notification_id', '').strip()

    if notification_id:
        _mark_notification_read(agency_id, notification_id)
    else:
        _mark_all_notifications_read(agency_id)

    unread_count = _count_unread_notifications(agency_id)
    return jsonify({'success': True, 'unread_count': unread_count})

# --- USER & AGENCY PORTALS ---

@app.route('/login', methods=['GET', 'POST'])
def login():
    if request.method == 'POST':
        email = request.form.get('email', '').strip()
        password = request.form.get('password', '').strip()
        role = (request.form.get('role', 'user') or 'user').strip().lower()
        
        if not email or not password:
            flash('Email and password are required.', 'error')
            return render_template('login.html')
        
        # Look up all accounts matching this email first.
        email_matches = []
        if FIREBASE_ENABLED:
            try:
                ref = firebase_db.reference('/users')
                all_users = ref.get()
                for uid, udata in _iter_valid_user_records(all_users):
                    if udata.get('email', '').lower() == email.lower():
                        email_matches.append((uid, udata))
            except Exception as e:
                print(f"⚠️  Firebase auth error: {e}")
                flash('An error occurred. Please try again.', 'error')
                return render_template('login.html')
        else:
            # Fallback: check in-memory users
            for uid, udata in MOCK_DATABASE.get('users', {}).items():
                if udata.get('email', '').lower() == email.lower():
                    email_matches.append((uid, udata))

        if not email_matches:
            flash('Account not found. Please register first or check your role tab.', 'error')
            return render_template('login.html')

        # Verify password against matched accounts, prioritizing selected role.
        from werkzeug.security import check_password_hash

        prioritized = []
        secondary = []
        for uid, udata in email_matches:
            account_role = (udata.get('role', 'user') or 'user').strip().lower()
            if account_role == role:
                prioritized.append((uid, udata))
            else:
                secondary.append((uid, udata))

        user_key = None
        user_data = None

        for uid, udata in prioritized + secondary:
            pwd_hash = (udata or {}).get('password_hash', '')
            if not pwd_hash:
                continue
            try:
                if check_password_hash(pwd_hash, password):
                    user_key = uid
                    user_data = udata
                    break
            except Exception:
                continue

        if not user_data:
            google_only_account = any(
                (u.get('auth_provider') == 'google') and not u.get('password_hash')
                for _, u in email_matches
            )
            if google_only_account:
                flash('This account was created with Google. Please use Sign in with Google.', 'error')
            else:
                flash('Incorrect password. Please try again.', 'error')
            return render_template('login.html')
        
        # Set session
        authenticated_role = user_data.get('role', 'user')
        session['user_id'] = user_key
        session['role'] = authenticated_role
        session['name'] = user_data.get('name', 'User')
        _touch_last_login(user_key)
        
        if authenticated_role == 'agency':
            flash(f'Welcome back, {user_data["name"]}!', 'success')
            return redirect(url_for('agency_dashboard'))
        else:
            flash(f'Welcome back, {user_data["name"]}!', 'success')
            return redirect(url_for('profile'))
            
    return render_template('login.html')

@app.route('/auth/google', methods=['POST'])
def google_auth():
    """Handle Google OAuth sign-in via Firebase ID token."""
    data = request.get_json(silent=True) or {}
    id_token = data.get('idToken', '')
    role = data.get('role', 'user')
    
    if not id_token:
        return jsonify({'error': 'No token provided'}), 400
    
    if not FIREBASE_ENABLED:
        return jsonify({'error': 'Firebase is not configured on the server. Please use email/password login.'}), 500
    
    uid = None
    email = ''
    name = ''
    photo = ''
    
    # Method 1: Verify the Firebase ID token (standard approach)
    try:
        decoded = firebase_auth.verify_id_token(id_token)
        uid = decoded['uid']
        email = decoded.get('email', '')
        name = decoded.get('name', decoded.get('email', 'User'))
        photo = decoded.get('picture', '')
    except Exception as token_err:
        print(f'Token verification failed ({type(token_err).__name__}): {token_err}')
        
        # Method 2: Fallback — use client-provided UID and verify via Firebase Auth
        client_uid = data.get('uid', '')
        client_email = data.get('email', '')
        if client_uid:
            try:
                fb_user = firebase_auth.get_user(client_uid)
                # Confirm the email matches what the client sent (prevent spoofing)
                if fb_user.email and fb_user.email.lower() == client_email.lower():
                    uid = fb_user.uid
                    email = fb_user.email
                    name = fb_user.display_name or fb_user.email or 'User'
                    photo = fb_user.photo_url or ''
                    print(f'Fallback auth succeeded for {email}')
                else:
                    print(f'Fallback auth email mismatch: {fb_user.email} vs {client_email}')
                    return jsonify({'error': 'Authentication failed. Email mismatch.'}), 401
            except Exception as fallback_err:
                print(f'Fallback auth also failed ({type(fallback_err).__name__}): {fallback_err}')
                return jsonify({'error': 'Authentication failed. Please try again.'}), 401
        else:
            return jsonify({'error': 'Authentication failed. Please try again.'}), 401
    
    try:
        # Create or update user record in RTDB
        user_record = {
            'name': name,
            'email': email.lower(),
            'role': role,
            'photo': photo,
            'auth_provider': 'google',
            'firebase_uid': uid
        }
        
        # Check if user already exists with this email and role
        existing_user_key = None
        try:
            ref = firebase_db.reference('/users')
            all_users = ref.get()
            for ukey, udata in _iter_valid_user_records(all_users):
                if udata.get('email', '').lower() == email.lower() and udata.get('role') == role:
                    existing_user_key = ukey
                    break
        except Exception as e:
            print(f'Firebase lookup error: {e}')
        
        # Use existing key or Firebase UID as key
        user_key = existing_user_key or uid
        
        firebase_db.reference(f'/users/{user_key}').update(user_record)
        
        # Set Flask session
        session['user_id'] = user_key
        session['role'] = role
        session['name'] = name
        _touch_last_login(user_key)
        
        # Determine redirect URL
        redirect_url = url_for('agency_dashboard') if role == 'agency' else url_for('profile')
        
        return jsonify({'success': True, 'redirect': redirect_url})
    
    except Exception as e:
        print(f'Google auth session/db error ({type(e).__name__}): {e}')
        return jsonify({'error': f'Authentication failed: {e}'}), 500

@app.route('/register', methods=['GET', 'POST'])
def register():
    if request.method == 'POST':
        name = request.form.get('name', '').strip()
        email = request.form.get('email', '').strip()
        password = request.form.get('password', '').strip()
        role = request.form.get('role', 'user')
        
        if not name or not email or not password:
            flash('All fields are required.', 'error')
            return render_template('login.html', show_register=True)
        
        if len(password) < 6:
            flash('Password must be at least 6 characters.', 'error')
            return render_template('login.html', show_register=True)
        
        # Check if email already exists
        email_exists = False
        if FIREBASE_ENABLED:
            try:
                ref = firebase_db.reference('/users')
                all_users = ref.get()
                for uid, udata in _iter_valid_user_records(all_users):
                    if udata.get('email', '').lower() == email.lower() and udata.get('role') == role:
                        email_exists = True
                        break
            except Exception as e:
                print(f"⚠️  Firebase register error: {e}")
        else:
            for uid, udata in MOCK_DATABASE.get('users', {}).items():
                if udata.get('email', '').lower() == email.lower() and udata.get('role') == role:
                    email_exists = True
                    break
        
        if email_exists:
            flash('An account with this email already exists for this role.', 'error')
            return render_template('login.html', show_register=True)
        
        # Create user
        from werkzeug.security import generate_password_hash
        import time
        
        # Generate user ID
        if role == 'agency':
            user_id = f'A{int(time.time())}'
        else:
            user_id = f'U{int(time.time())}'
        
        user_record = {
            'name': name,
            'email': email.lower(),
            'password_hash': generate_password_hash(password),
            'role': role,
            'created_at': int(time.time())
        }
        
        if FIREBASE_ENABLED:
            try:
                firebase_db.reference(f'/users/{user_id}').set(user_record)
            except Exception as e:
                print(f"⚠️  Firebase write error: {e}")
                flash('Registration failed. Please try again.', 'error')
                return render_template('login.html', show_register=True)
        else:
            if 'users' not in MOCK_DATABASE:
                MOCK_DATABASE['users'] = {}
            MOCK_DATABASE['users'][user_id] = user_record
        
        # Auto-login after registration
        session['user_id'] = user_id
        session['role'] = role
        session['name'] = name
        
        if role == 'agency':
            flash(f'Agency account created! Welcome, {name}!', 'success')
            return redirect(url_for('agency_dashboard'))
        else:
            flash(f'Account created! Welcome, {name}!', 'success')
            return redirect(url_for('profile'))
    
    return render_template('login.html', show_register=True)

@app.route('/logout')
def logout():
    session.clear()
    flash('You have been logged out.', 'success')
    return redirect(url_for('index'))

@app.route('/profile')
def profile():
    # Check if a user is logged in
    if session.get('role') != 'user':
        flash('Please login as a user to access this page.', 'error')
        return redirect(url_for('login'))
    
    # Get real user data from Firebase
    user_id = session.get('user_id')
    user_email = ''
    user_name = session.get('name', 'User')
    
    if FIREBASE_ENABLED:
        try:
            user_ref = firebase_db.reference(f'/users/{user_id}')
            user_data = user_ref.get()
            if user_data:
                user_email = user_data.get('email', '')
                user_name = user_data.get('name', user_name)
        except Exception as e:
            print(f"⚠️  Firebase user read error: {e}")
    
    # Get bookings for this user
    bookings = _get_bookings_for_user(user_id)
    
    user_info = {
        'name': user_name,
        'email': user_email,
        'bookings': bookings
    }
    return render_template('profile.html', user=user_info)

@app.route('/agency')
def agency_dashboard():
    # Check if an agency is logged in
    if session.get('role') != 'agency':
        flash('Please login as an agency to access this page.', 'error')
        return redirect(url_for('login'))
    
    agency_id = session.get('user_id')
    # Pull only packages owned by this agency
    agency_packages = db_get_packages_by_agency(agency_id)
    agency_bookings = _get_bookings_for_agency(agency_id)
    # Legacy data may contain package/agency IDs that do not match current
    # agency account IDs. Show all bookings in dashboard as admin inbox so
    # pending requests are never hidden.
    if not agency_bookings:
        agency_bookings = _get_all_bookings()

    total_revenue = sum(b.get('amount', 0) * b.get('travelers', 1) for b in agency_bookings if b.get('status') == 'approved')
    pending_count = sum(1 for b in agency_bookings if b.get('status') == 'pending')

    mock_agency = {
        'name': session.get('name', 'Wanderlust Karnataka Travels'),
        'packages': agency_packages,
        'bookings': agency_bookings,
        'stats': {
            'total_bookings': len(agency_bookings),
            'pending_bookings': pending_count,
            'revenue': f'₹{total_revenue:,}',
            'active_packages': len(agency_packages)
        }
    }
    return render_template('agency-dashboard.html', agency=mock_agency)


def _csv_cell(value):
    """Normalize values for CSV output."""
    if value is None:
        return ''
    if isinstance(value, (list, dict)):
        return json.dumps(value, ensure_ascii=False)
    return str(value)


def _parse_export_date(value):
    if not value:
        return None
    try:
        return datetime.strptime(str(value).strip(), '%Y-%m-%d').date()
    except Exception:
        return None


def _extract_date(value):
    if not value:
        return None
    text = str(value).strip()
    if not text:
        return None
    candidates = [text, text[:10]]
    for candidate in candidates:
        for fmt in ('%Y-%m-%d %H:%M', '%Y-%m-%d'):
            try:
                return datetime.strptime(candidate, fmt).date()
            except Exception:
                continue
    return None


def _in_date_range(date_value, start_date=None, end_date=None):
    if not start_date and not end_date:
        return True
    item_date = _extract_date(date_value)
    if item_date is None:
        return False
    if start_date and item_date < start_date:
        return False
    if end_date and item_date > end_date:
        return False
    return True


def _filter_bookings_for_export(bookings, status='all', start_date=None, end_date=None):
    normalized_status = (status or 'all').strip().lower()
    allowed_status = {'pending', 'approved', 'rejected', 'all'}
    if normalized_status not in allowed_status:
        normalized_status = 'all'

    filtered = []
    for booking in bookings:
        booking_status = str(booking.get('status', '')).strip().lower()
        if normalized_status != 'all' and booking_status != normalized_status:
            continue
        if not _in_date_range(booking.get('booked_on', ''), start_date, end_date):
            continue
        filtered.append(booking)
    return filtered


def _filter_packages_for_export(packages, start_date=None, end_date=None):
    if not start_date and not end_date:
        return packages
    filtered = []
    for pkg in packages:
        created_at = pkg.get('created_at', '')
        if not created_at:
            filtered.append(pkg)
            continue
        if _in_date_range(created_at, start_date, end_date):
            filtered.append(pkg)
    return filtered


def _build_packages_csv(packages):
    output = io.StringIO(newline='')
    writer = csv.writer(output)
    header = [
        'id', 'title', 'tag', 'duration', 'price', 'old_price', 'discount',
        'transport_type', 'location_name', 'created_at'
    ]
    writer.writerow(header)
    for pkg in packages:
        location = pkg.get('location') or {}
        writer.writerow([
            _csv_cell(pkg.get('id')),
            _csv_cell(pkg.get('title')),
            _csv_cell(pkg.get('tag')),
            _csv_cell(pkg.get('duration')),
            _csv_cell(pkg.get('price')),
            _csv_cell(pkg.get('old_price')),
            _csv_cell(pkg.get('discount')),
            _csv_cell(pkg.get('transport_type')),
            _csv_cell(location.get('name')),
            _csv_cell(pkg.get('created_at')),
        ])
    return output.getvalue()


def _build_bookings_csv(bookings):
    output = io.StringIO(newline='')
    writer = csv.writer(output)
    header = [
        'id', 'package_id', 'package_title', 'customer_name', 'customer_email',
        'customer_phone', 'travel_date', 'travelers', 'amount_per_traveler',
        'total_amount', 'status', 'booked_on'
    ]
    writer.writerow(header)
    for booking in bookings:
        amount = booking.get('amount', 0)
        travelers = booking.get('travelers', 1)
        try:
            total_amount = float(amount) * int(travelers)
        except Exception:
            total_amount = ''
        writer.writerow([
            _csv_cell(booking.get('id')),
            _csv_cell(booking.get('package_id')),
            _csv_cell(booking.get('package_title')),
            _csv_cell(booking.get('customer_name')),
            _csv_cell(booking.get('customer_email')),
            _csv_cell(booking.get('customer_phone')),
            _csv_cell(booking.get('travel_date')),
            _csv_cell(travelers),
            _csv_cell(amount),
            _csv_cell(total_amount),
            _csv_cell(booking.get('status')),
            _csv_cell(booking.get('booked_on')),
        ])
    return output.getvalue()


@app.route('/agency/export/csv')
def agency_export_csv():
    if session.get('role') != 'agency':
        flash('Please login as an agency to export data.', 'error')
        return redirect(url_for('login'))

    agency_id = session.get('user_id')
    dataset = (request.args.get('dataset', 'bookings') or 'bookings').strip().lower()
    status = (request.args.get('status', 'all') or 'all').strip().lower()
    start_date = _parse_export_date(request.args.get('start_date', ''))
    end_date = _parse_export_date(request.args.get('end_date', ''))

    if start_date and end_date and start_date > end_date:
        flash('Start date must be earlier than or equal to end date.', 'error')
        return redirect(url_for('agency_dashboard'))

    if dataset not in {'bookings', 'packages', 'all'}:
        dataset = 'bookings'

    now_tag = datetime.now().strftime('%Y%m%d-%H%M%S')

    bookings = _get_bookings_for_agency(agency_id)
    if not bookings:
        bookings = _get_all_bookings()
    filtered_bookings = _filter_bookings_for_export(bookings, status=status, start_date=start_date, end_date=end_date)

    packages = db_get_packages_by_agency(agency_id)
    filtered_packages = _filter_packages_for_export(packages, start_date=start_date, end_date=end_date)

    if dataset == 'packages':
        csv_content = _build_packages_csv(filtered_packages)
        filename = f'agency-packages-{agency_id}-{now_tag}.csv'
        return Response(
            csv_content,
            mimetype='text/csv; charset=utf-8',
            headers={'Content-Disposition': f'attachment; filename="{filename}"'}
        )

    if dataset == 'all':
        archive_name = f'agency-export-{agency_id}-{now_tag}.zip'
        zip_buffer = io.BytesIO()
        with zipfile.ZipFile(zip_buffer, mode='w', compression=zipfile.ZIP_DEFLATED) as zf:
            zf.writestr(f'bookings-{agency_id}-{now_tag}.csv', _build_bookings_csv(filtered_bookings))
            zf.writestr(f'packages-{agency_id}-{now_tag}.csv', _build_packages_csv(filtered_packages))
        zip_buffer.seek(0)
        return Response(
            zip_buffer.getvalue(),
            mimetype='application/zip',
            headers={'Content-Disposition': f'attachment; filename="{archive_name}"'}
        )

    csv_content = _build_bookings_csv(filtered_bookings)
    filename = f'agency-bookings-{agency_id}-{now_tag}.csv'
    return Response(
        csv_content,
        mimetype='text/csv; charset=utf-8',
        headers={'Content-Disposition': f'attachment; filename="{filename}"'}
    )

@app.route('/agency/add', methods=['POST'])
def agency_add_package():
    if session.get('role') != 'agency':
        flash('Please login as an agency.', 'error')
        return redirect(url_for('login'))
    
    title = request.form.get('title', '').strip()
    duration = request.form.get('duration', '').strip()
    price = request.form.get('price', '0').strip()
    old_price = request.form.get('old_price', '0').strip()
    tag = request.form.get('tag', 'Adventure').strip()
    transport_type = request.form.get('transport_type', 'mixed').strip().lower()
    image_url = request.form.get('image_url', '').strip()
    
    # Parse day-by-day itinerary from form
    day_count = int(request.form.get('day_count', '0') or '0')
    itinerary = []
    description_parts = []
    for i in range(1, day_count + 1):
        day_title = request.form.get(f'day_title_{i}', '').strip()
        day_desc = request.form.get(f'day_desc_{i}', '').strip()
        if day_title or day_desc:
            itinerary.append({'day': len(itinerary) + 1, 'title': day_title, 'desc': day_desc})
            if day_title:
                description_parts.append(f'Day {len(itinerary)}: {day_title}')
            if day_desc:
                description_parts.append(day_desc)
    description = '\n'.join(description_parts) if description_parts else f'Explore {title} with our expert-guided tour package.'
    if not itinerary:
        itinerary = [{'day': 1, 'title': f'Explore {title}', 'desc': description}]
    
    # Handle file uploads for gallery images
    gallery_files = request.files.getlist('gallery_files')
    gallery_urls = save_uploaded_files(gallery_files, ALLOWED_IMG_EXT)
    
    # Handle file uploads for videos
    video_files = request.files.getlist('video_files')
    video_urls = save_uploaded_files(video_files, ALLOWED_VID_EXT)
    
    # Also accept URL inputs as fallback
    gallery_raw = request.form.get('gallery_urls', '').strip()
    video_raw = request.form.get('video_urls', '').strip()
    if gallery_raw:
        gallery_urls += [u.strip() for u in gallery_raw.splitlines() if u.strip()]
    if video_raw:
        video_urls += [u.strip() for u in video_raw.splitlines() if u.strip()]
    
    features_raw = request.form.get('features', '').strip()
    features_list = [f.strip() for f in features_raw.splitlines() if f.strip()] if features_raw else []
    
    # Handle main image upload
    main_image_file = request.files.get('main_image_file')
    if main_image_file and main_image_file.filename and allowed_file(main_image_file.filename, ALLOWED_IMG_EXT):
        saved = save_uploaded_files([main_image_file], ALLOWED_IMG_EXT)
        if saved:
            image_url = saved[0]
    
    # Parse ambient sound type
    ambient_type = request.form.get('ambient_sound', '').strip()
    ambient_sound = None
    if ambient_type:
        sound_map = {
            'forest': {'type': 'forest', 'label': 'Forest & Nature Ambience', 'icon': 'fa-leaf'},
            'ocean': {'type': 'ocean', 'label': 'Ocean Waves & Seagulls', 'icon': 'fa-water'},
            'heritage': {'type': 'heritage', 'label': 'Ancient Temple Bells', 'icon': 'fa-landmark'},
            'wildlife': {'type': 'wildlife', 'label': 'Jungle Night Sounds', 'icon': 'fa-paw'}
        }
        ambient_sound = sound_map.get(ambient_type)
    
    if not title or not price:
        flash('Package title and price are required.', 'error')
        return redirect(url_for('agency_dashboard'))
    
    # Generate a slug-based ID
    pkg_id = title.lower().replace(' ', '-').replace('&', 'and')[:30]
    
    # Default image if none provided
    if not image_url:
        image_url = 'https://images.unsplash.com/photo-1476514525535-07fb3b4ae5f1?auto=format&fit=crop&w=500&q=80'
    
    # Build gallery: use provided gallery URLs, or fall back to the single image
    if not gallery_urls:
        gallery_urls = [image_url]
    
    new_package = {
        'id': pkg_id,
        'agency_id': session.get('user_id'),
        'tag': tag,
        'transport_type': transport_type or 'mixed',
        'title': title,
        'description': description or f'Explore {title} with our expert-guided tour package.',
        'duration': duration or '2 Days / 1 Night',
        'old_price': int(old_price) if old_price else int(price),
        'price': int(price),
        'discount': '',
        'image': image_url,
        'images': [image_url],
        'gallery': gallery_urls,
        'videos': video_urls,
        'features': features_list,
        'ambient_sound': ambient_sound,
        'tags': [tag],
        'location': {
            'lat': float(request.form.get('location_lat', '0') or '0'),
            'lng': float(request.form.get('location_lng', '0') or '0'),
            'name': request.form.get('location_name', '').strip()
        },
        'climate_info': {
            'best_season': request.form.get('best_season', '').strip(),
            'expected_temp': request.form.get('expected_temp', '').strip(),
            'terrain': request.form.get('terrain', '').strip(),
            'rainfall': request.form.get('rainfall', '').strip(),
            'weather_tips': request.form.get('weather_tips', '').strip()
        },
        'show_nearby_restaurants': request.form.get('show_nearby_restaurants') == 'on',
        'accessibility': {
            'wheelchair': int(request.form.get('accessibility_wheelchair', '0') or '0'),
            'family': int(request.form.get('accessibility_family', '0') or '0'),
            'senior': int(request.form.get('accessibility_senior', '0') or '0')
        },
        'itinerary': itinerary
    }

    _attach_carbon_score(new_package)
    
    # Calculate discount if old_price > price
    if new_package['old_price'] > new_package['price']:
        pct = round((1 - new_package['price'] / new_package['old_price']) * 100)
        new_package['discount'] = f'{pct}% OFF'
    
    if not db_add_package(pkg_id, new_package):
        flash('Package save failed in Firebase. Please check DB credentials/rules and try again.', 'error')
        return redirect(url_for('agency_dashboard'))

    flash(f'Package "{title}" added successfully! It is now visible to customers.', 'success')
    return redirect(url_for('agency_dashboard'))

@app.route('/agency/delete/<id>', methods=['POST'])
def agency_delete_package(id):
    if session.get('role') != 'agency':
        flash('Please login as an agency.', 'error')
        return redirect(url_for('login'))
    
    package = db_get_package(id)
    if not package:
        flash('Package not found.', 'error')
        return redirect(url_for('agency_dashboard'))
    
    # Only allow deletion if the agency owns this package
    if package.get('agency_id') != session.get('user_id'):
        flash('You do not have permission to delete this package.', 'error')
        return redirect(url_for('agency_dashboard'))
    
    if not db_delete_package(id):
        flash('Package delete failed in Firebase. Please try again.', 'error')
        return redirect(url_for('agency_dashboard'))

    flash(f'Package "{package["title"]}" has been removed.', 'success')
    return redirect(url_for('agency_dashboard'))

@app.route('/agency/edit/<id>', methods=['GET'])
def agency_edit_package_form(id):
    if session.get('role') != 'agency':
        flash('Please login as an agency.', 'error')
        return redirect(url_for('login'))
    
    package = db_get_package(id)
    if not package:
        flash('Package not found.', 'error')
        return redirect(url_for('agency_dashboard'))
    
    if package.get('agency_id') != session.get('user_id'):
        flash('You do not have permission to edit this package.', 'error')
        return redirect(url_for('agency_dashboard'))
    
    return jsonify(package)

@app.route('/agency/edit/<id>', methods=['POST'])
def agency_edit_package(id):
    if session.get('role') != 'agency':
        flash('Please login as an agency.', 'error')
        return redirect(url_for('login'))
    
    package = db_get_package(id)
    if not package:
        flash('Package not found.', 'error')
        return redirect(url_for('agency_dashboard'))
    
    if package.get('agency_id') != session.get('user_id'):
        flash('You do not have permission to edit this package.', 'error')
        return redirect(url_for('agency_dashboard'))
    
    title = request.form.get('title', '').strip()
    duration = request.form.get('duration', '').strip()
    price = request.form.get('price', '0').strip()
    old_price = request.form.get('old_price', '0').strip()
    tag = request.form.get('tag', 'Adventure').strip()
    transport_type = request.form.get('transport_type', (package.get('transport_type') or 'mixed')).strip().lower()
    image_url = request.form.get('image_url', '').strip()
    
    # Parse day-by-day itinerary from form
    day_count = int(request.form.get('day_count', '0') or '0')
    itinerary = []
    description_parts = []
    for i in range(1, day_count + 1):
        day_title = request.form.get(f'day_title_{i}', '').strip()
        day_desc = request.form.get(f'day_desc_{i}', '').strip()
        if day_title or day_desc:
            itinerary.append({'day': len(itinerary) + 1, 'title': day_title, 'desc': day_desc})
            if day_title:
                description_parts.append(f'Day {len(itinerary)}: {day_title}')
            if day_desc:
                description_parts.append(day_desc)
    description = '\n'.join(description_parts) if description_parts else package.get('description', '')
    
    # Handle file uploads for videos
    video_files = request.files.getlist('video_files')
    video_urls = save_uploaded_files(video_files, ALLOWED_VID_EXT)
    
    # Also accept URL inputs for videos
    video_raw = request.form.get('video_urls', '').strip()
    if video_raw:
        video_urls += [u.strip() for u in video_raw.splitlines() if u.strip()]
    
    features_raw = request.form.get('features', '').strip()
    features_list = [f.strip() for f in features_raw.splitlines() if f.strip()] if features_raw else []
    
    # Handle main image upload
    main_image_file = request.files.get('main_image_file')
    if main_image_file and main_image_file.filename and allowed_file(main_image_file.filename, ALLOWED_IMG_EXT):
        saved = save_uploaded_files([main_image_file], ALLOWED_IMG_EXT)
        if saved:
            image_url = saved[0]
    # Parse ambient sound type
    ambient_type = request.form.get('ambient_sound', '').strip()
    ambient_sound = None
    if ambient_type:
        sound_map = {
            'forest': {'type': 'forest', 'label': 'Forest & Nature Ambience', 'icon': 'fa-leaf'},
            'ocean': {'type': 'ocean', 'label': 'Ocean Waves & Seagulls', 'icon': 'fa-water'},
            'heritage': {'type': 'heritage', 'label': 'Ancient Temple Bells', 'icon': 'fa-landmark'},
            'wildlife': {'type': 'wildlife', 'label': 'Jungle Night Sounds', 'icon': 'fa-paw'}
        }
        ambient_sound = sound_map.get(ambient_type)
    
    if not title or not price:
        flash('Package title and price are required.', 'error')
        return redirect(url_for('agency_dashboard'))
    
    # Build update data
    update_data = {
        'title': title,
        'tag': tag,
        'transport_type': transport_type or 'mixed',
        'duration': duration or package.get('duration', '2 Days / 1 Night'),
        'price': int(price),
        'old_price': int(old_price) if old_price else int(price),
        'description': description or package.get('description', ''),
        'itinerary': itinerary if itinerary else package.get('itinerary', []),
        'ambient_sound': ambient_sound,
        'tags': [tag],
        'location': {
            'lat': float(request.form.get('location_lat', '0') or '0'),
            'lng': float(request.form.get('location_lng', '0') or '0'),
            'name': request.form.get('location_name', '').strip()
        },
        'climate_info': {
            'best_season': request.form.get('best_season', '').strip(),
            'expected_temp': request.form.get('expected_temp', '').strip(),
            'terrain': request.form.get('terrain', '').strip(),
            'rainfall': request.form.get('rainfall', '').strip(),
            'weather_tips': request.form.get('weather_tips', '').strip()
        },
        'show_nearby_restaurants': request.form.get('show_nearby_restaurants') == 'on',
        'accessibility': {
            'wheelchair': int(request.form.get('accessibility_wheelchair', '0') or '0'),
            'family': int(request.form.get('accessibility_family', '0') or '0'),
            'senior': int(request.form.get('accessibility_senior', '0') or '0')
        }
    }
    
    # Handle main image removal
    remove_main = request.form.get('remove_main_image', '0') == '1'
    if remove_main and not image_url:
        update_data['image'] = 'https://images.unsplash.com/photo-1476514525535-07fb3b4ae5f1?auto=format&fit=crop&w=500&q=80'
        update_data['images'] = [update_data['image']]
    elif image_url:
        update_data['image'] = image_url
        update_data['images'] = [image_url]
    
    # Handle existing gallery (after removals by user)
    existing_gallery_raw = request.form.get('existing_gallery_urls', '').strip()
    existing_gallery = [u.strip() for u in existing_gallery_raw.splitlines() if u.strip()] if existing_gallery_raw else []
    
    # Merge: existing gallery (with removals applied) + newly uploaded files
    new_uploads_only = save_uploaded_files(request.files.getlist('gallery_files'), ALLOWED_IMG_EXT)
    final_gallery = existing_gallery + new_uploads_only
    if final_gallery:
        update_data['gallery'] = final_gallery
    else:
        # User removed all images and added none — keep at least the main image
        update_data['gallery'] = [update_data.get('image', package.get('image', ''))]
    
    if video_urls:
        update_data['videos'] = video_urls
    
    if features_list:
        update_data['features'] = features_list
    
    # Recalculate discount
    if update_data['old_price'] > update_data['price']:
        pct = round((1 - update_data['price'] / update_data['old_price']) * 100)
        update_data['discount'] = f'{pct}% OFF'
    else:
        update_data['discount'] = ''

    update_data['carbon_score'] = _calculate_carbon_score(update_data['duration'], update_data['transport_type'])
    
    if not db_update_package(id, update_data):
        flash('Package update failed in Firebase. Please check DB credentials/rules and try again.', 'error')
        return redirect(url_for('agency_dashboard'))

    flash(f'Package "{title}" updated successfully!', 'success')
    return redirect(url_for('agency_dashboard'))

# ═══════════════════════════════════════════════════════
# TRAVEL BLOG / REVIEWS
# ═══════════════════════════════════════════════════════

def db_get_reviews(pkg_id):
    """Get all reviews for a package."""
    if FIREBASE_ENABLED:
        try:
            ref = firebase_db.reference(f'/reviews/{pkg_id}')
            data = ref.get()
            if data and isinstance(data, dict):
                return list(data.values())
            return []
        except Exception as e:
            print(f"⚠️  Firebase review read error: {e}")
    return MOCK_DATABASE.get('reviews', {}).get(pkg_id, [])

def db_add_review(pkg_id, review):
    """Add a review for a package."""
    review_id = uuid.uuid4().hex[:12]
    review['id'] = review_id
    if FIREBASE_ENABLED:
        try:
            ref = firebase_db.reference(f'/reviews/{pkg_id}/{review_id}')
            ref.set(review)
            return True
        except Exception as e:
            print(f"⚠️  Firebase review write error: {e}")
    if 'reviews' not in MOCK_DATABASE:
        MOCK_DATABASE['reviews'] = {}
    if pkg_id not in MOCK_DATABASE['reviews']:
        MOCK_DATABASE['reviews'][pkg_id] = []
    MOCK_DATABASE['reviews'][pkg_id].append(review)
    return True

def db_get_all_reviews():
    """Get all reviews across all packages."""
    if FIREBASE_ENABLED:
        try:
            ref = firebase_db.reference('/reviews')
            data = ref.get()
            if data and isinstance(data, dict):
                all_reviews = []
                for pkg_id, reviews in data.items():
                    if isinstance(reviews, dict):
                        for r in reviews.values():
                            r['package_id'] = pkg_id
                            all_reviews.append(r)
                return all_reviews
            return []
        except Exception as e:
            print(f"⚠️  Firebase reviews read error: {e}")
    all_reviews = []
    for pkg_id, reviews in MOCK_DATABASE.get('reviews', {}).items():
        for r in reviews:
            r['package_id'] = pkg_id
            all_reviews.append(r)
    return all_reviews

@app.route('/reviews')
def travel_blog():
    """Travel blog / reviews page — shows all reviews as travel stories."""
    all_reviews = db_get_all_reviews()
    # Sort by date (newest first)
    all_reviews.sort(key=lambda r: r.get('date', ''), reverse=True)
    # Attach package info for each review
    all_packages = db_get_all_packages()
    for review in all_reviews:
        pkg = all_packages.get(review.get('package_id', ''), {})
        review['package_title'] = pkg.get('title', 'Unknown Destination')
        review['package_image'] = pkg.get('image', '')
        review['package_location'] = pkg.get('location', {}).get('name', '')
    return render_template('reviews.html', reviews=all_reviews)

@app.route('/api/reviews/<pkg_id>')
def api_get_reviews(pkg_id):
    """API to get reviews for a specific package."""
    reviews = db_get_reviews(pkg_id)
    # Sort newest first
    reviews.sort(key=lambda r: r.get('date', ''), reverse=True)
    # Calculate stats
    if reviews:
        avg = sum(r.get('rating', 0) for r in reviews) / len(reviews)
        counts = {i: sum(1 for r in reviews if r.get('rating') == i) for i in range(1, 6)}
    else:
        avg = 0
        counts = {i: 0 for i in range(1, 6)}
    return jsonify({
        'reviews': reviews,
        'stats': {
            'average': round(avg, 1),
            'total': len(reviews),
            'counts': counts
        }
    })

@app.route('/api/reviews/<pkg_id>', methods=['POST'])
def api_add_review(pkg_id):
    """API to add a review for a package."""
    if not session.get('user_id'):
        return jsonify({'error': 'Please login to write a review'}), 401
    
    # Check if package exists
    package = db_get_package(pkg_id)
    if not package:
        return jsonify({'error': 'Package not found'}), 404
    
    rating = request.form.get('rating', type=int)
    title = request.form.get('title', '').strip()
    content = request.form.get('content', '').strip()
    trip_type = request.form.get('trip_type', '').strip()
    
    if not rating or rating < 1 or rating > 5:
        return jsonify({'error': 'Rating must be between 1 and 5'}), 400
    if not title or not content:
        return jsonify({'error': 'Title and review content are required'}), 400

    # Handle photo uploads
    photo_files = request.files.getlist('photos')
    photo_urls = save_uploaded_files(photo_files, ALLOWED_IMG_EXT) if photo_files else []
    
    review = {
        'user_name': session.get('name', 'Anonymous'),
        'user_id': session.get('user_id'),
        'rating': rating,
        'title': title,
        'content': content,
        'trip_type': trip_type,
        'photos': photo_urls,
        'date': datetime.now().strftime('%Y-%m-%d'),
        'helpful': 0
    }
    
    db_add_review(pkg_id, review)
    return jsonify({'success': True, 'review': review})

if __name__ == '__main__':
    app.run(debug=True, port=5000)
