from flask import Flask, render_template, request, session, redirect, url_for, flash, jsonify, Response, send_from_directory
from config import Config
import firebase_admin
from firebase_admin import credentials, db as firebase_db, auth as firebase_auth, storage as firebase_storage
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
import mimetypes
import threading
import secrets
from urllib.parse import quote, unquote, urlparse
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
_MEDIA_ROUTE_CACHE = {}
_MEDIA_ROUTE_CACHE_TTL = 900
_MEDIA_ROUTE_MISS_TTL = 180
_MEDIA_CACHE_NOT_FOUND = '__NOT_FOUND__'
_MEDIA_CACHE_IMAGE_FALLBACK = '__IMAGE_FALLBACK__'
_MEDIA_PLACEHOLDER_URL = 'https://images.unsplash.com/photo-1476514525535-07fb3b4ae5f1?auto=format&fit=crop&w=1000&q=80'

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


def _media_route_cache_get(key):
    entry = _MEDIA_ROUTE_CACHE.get(key)
    if not entry:
        return None
    if time.time() - entry['ts'] >= entry['ttl']:
        _MEDIA_ROUTE_CACHE.pop(key, None)
        return None
    return entry['value']


def _media_route_cache_set(key, value, ttl=_MEDIA_ROUTE_CACHE_TTL):
    _MEDIA_ROUTE_CACHE[key] = {'value': value, 'ts': time.time(), 'ttl': ttl}


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
        print(f"âš ï¸  Open-Meteo fallback triggered: {open_meteo_err}")

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
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DEFAULT_UPLOAD_FOLDER = os.path.join(BASE_DIR, 'static', 'uploads')
UPLOAD_FOLDER = os.environ.get('UPLOAD_PERSISTENT_DIR', '').strip() or DEFAULT_UPLOAD_FOLDER
if not os.path.isabs(UPLOAD_FOLDER):
    UPLOAD_FOLDER = os.path.join(BASE_DIR, UPLOAD_FOLDER)
UPLOAD_PUBLIC_PREFIX = '/uploads'
os.makedirs(UPLOAD_FOLDER, exist_ok=True)
app.config['UPLOAD_FOLDER'] = UPLOAD_FOLDER
app.config['MAX_CONTENT_LENGTH'] = 16 * 1024 * 1024  # 16 MB max
ALLOWED_IMG_EXT = {'png', 'jpg', 'jpeg', 'gif', 'webp'}
ALLOWED_VID_EXT = {'mp4', 'webm', 'mov'}
STORY_AUDIO_FOLDER = os.path.join(UPLOAD_FOLDER, 'stories')
os.makedirs(STORY_AUDIO_FOLDER, exist_ok=True)

if os.environ.get('RENDER') and not os.environ.get('UPLOAD_PERSISTENT_DIR', '').strip():
    print('âš ï¸  UPLOAD_PERSISTENT_DIR is not set on Render. Local uploads may be ephemeral across restarts.')

LOCAL_RUNTIME_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'runtime_data')
LOCAL_USERS_FILE = os.path.join(LOCAL_RUNTIME_DIR, 'users.json')
_LOCAL_USERS_LOCK = threading.Lock()
PASSWORD_RESET_OTP_LEN = 6
PASSWORD_RESET_OTP_TTL_SEC = 600
PASSWORD_RESET_MAX_ATTEMPTS = 5

def allowed_file(filename, allowed_ext):
    return '.' in filename and filename.rsplit('.', 1)[1].lower() in allowed_ext


def _upload_public_url(relative_path):
    clean = str(relative_path or '').replace('\\', '/').lstrip('/')
    return f'{UPLOAD_PUBLIC_PREFIX}/{clean}'


def _guess_content_type(filename, fallback='application/octet-stream'):
    guessed, _ = mimetypes.guess_type(str(filename or ''), strict=False)
    return guessed or fallback


def _firebase_download_url(bucket_name, object_name, token):
    encoded_name = quote(str(object_name or ''), safe='')
    return f'https://firebasestorage.googleapis.com/v0/b/{bucket_name}/o/{encoded_name}?alt=media&token={token}'


def _firebase_public_url(bucket_name, object_name):
    encoded_name = quote(str(object_name or ''), safe='/')
    return f'https://storage.googleapis.com/{bucket_name}/{encoded_name}'


def _iter_storage_bucket_candidates():
    seen = set()
    for name in FIREBASE_STORAGE_BUCKET_CANDIDATES:
        candidate = str(name or '').strip()
        if not candidate or candidate in seen:
            continue
        seen.add(candidate)
        yield candidate

    fallback = str(FIREBASE_STORAGE_BUCKET or '').strip()
    if fallback and fallback not in seen:
        yield fallback


def _promote_storage_bucket(bucket_name):
    global FIREBASE_STORAGE_BUCKET_CANDIDATES, FIREBASE_STORAGE_BUCKET
    normalized = str(bucket_name or '').strip()
    if not normalized:
        return

    FIREBASE_STORAGE_BUCKET = normalized
    existing = [b for b in FIREBASE_STORAGE_BUCKET_CANDIDATES if b != normalized]
    FIREBASE_STORAGE_BUCKET_CANDIDATES = [normalized] + existing


def _upload_to_firebase_storage(content_bytes, object_name, content_type):
    """Upload bytes to Firebase Storage and return a durable download URL."""
    if not FIREBASE_STORAGE_ENABLED:
        return ''
    if not content_bytes:
        return ''

    normalized_object = str(object_name or '').replace('\\', '/').strip().lstrip('/')
    if not normalized_object:
        return ''

    last_error = ''
    for bucket_name in _iter_storage_bucket_candidates():
        try:
            bucket = firebase_storage.bucket(name=bucket_name)
            blob = bucket.blob(normalized_object)
            existing_metadata = blob.metadata or {}
            token_field = str(existing_metadata.get('firebaseStorageDownloadTokens', '') or '')
            token = token_field.split(',')[0].strip() if token_field else ''
            if not token:
                token = uuid.uuid4().hex

            metadata = dict(existing_metadata)
            metadata['firebaseStorageDownloadTokens'] = token
            blob.metadata = metadata
            blob.cache_control = 'public, max-age=31536000'
            blob.upload_from_string(content_bytes, content_type=content_type)
            try:
                blob.make_public()
            except Exception as acl_err:
                print(f"âš ï¸  Firebase make_public skipped for {normalized_object} in bucket {bucket_name}: {acl_err}")
            _promote_storage_bucket(bucket_name)
            return _firebase_download_url(bucket_name, normalized_object, token)
        except Exception as e:
            last_error = str(e)
            print(f"âš ï¸  Firebase Storage upload error for {normalized_object} in bucket {bucket_name}: {e}")

    if last_error:
        print(f"âš ï¸  Firebase Storage upload failed for all buckets: {last_error}")
    return ''


def _firebase_object_url_if_exists(object_name):
    """Return Firebase Storage download URL for existing object, else empty string."""
    if not FIREBASE_STORAGE_ENABLED:
        return ''

    normalized_object = str(object_name or '').replace('\\', '/').strip().lstrip('/')
    if not normalized_object:
        return ''

    for bucket_name in _iter_storage_bucket_candidates():
        try:
            bucket = firebase_storage.bucket(name=bucket_name)
            blob = bucket.blob(normalized_object)
            if not blob.exists(timeout=1):
                continue

            blob.reload(timeout=1)
            metadata = blob.metadata or {}
            token_field = str(metadata.get('firebaseStorageDownloadTokens', '') or '')
            token = token_field.split(',')[0].strip() if token_field else ''
            if not token:
                token = uuid.uuid4().hex
                metadata['firebaseStorageDownloadTokens'] = token
                blob.metadata = metadata
                blob.patch(timeout=1)

            try:
                blob.make_public()
            except Exception as acl_err:
                print(f"âš ï¸  Firebase make_public skipped for existing {normalized_object} in bucket {bucket_name}: {acl_err}")

            _promote_storage_bucket(bucket_name)
            return _firebase_download_url(bucket_name, normalized_object, token)
        except Exception as e:
            print(f"âš ï¸  Firebase Storage lookup error for {normalized_object} in bucket {bucket_name}: {e}")

    return ''

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

def _sanitize_upload_folder(folder_hint, default_folder='packages'):
    raw = str(folder_hint or '').strip().replace('\\', '/').strip('/')
    if not raw:
        return default_folder

    safe_segments = []
    for segment in raw.split('/'):
        seg = re.sub(r'[^a-zA-Z0-9_-]+', '-', segment.strip())
        if not seg or seg in ('.', '..'):
            continue
        safe_segments.append(seg)

    if not safe_segments:
        return default_folder
    return '/'.join(safe_segments)


def _upload_single_file_to_firebase(file_obj, allowed_ext, folder_prefix='packages'):
    """Upload one Werkzeug FileStorage object to Firebase using memory-only bytes."""
    if not file_obj or not file_obj.filename:
        return None, 'No file selected.'
    if not allowed_file(file_obj.filename, allowed_ext):
        return None, 'Invalid file type.'

    ext = file_obj.filename.rsplit('.', 1)[1].lower()
    content_type = _guess_content_type(file_obj.filename)
    content_bytes = b''
    object_ext = ext

    if ext in ALLOWED_IMG_EXT:
        optimized = optimize_image(file_obj)
        if optimized:
            content_bytes = optimized.read()
            content_type = 'image/jpeg'
            object_ext = 'jpg'
        else:
            try:
                file_obj.seek(0)
            except Exception:
                pass
            content_bytes = file_obj.read()
    else:
        try:
            file_obj.seek(0)
        except Exception:
            pass
        content_bytes = file_obj.read()

    if not content_bytes:
        return None, 'Empty file stream.'

    clean_folder = _sanitize_upload_folder(folder_prefix)
    object_name = f'{clean_folder}/{uuid.uuid4().hex}.{object_ext}'
    cloud_url = _upload_to_firebase_storage(content_bytes, object_name, content_type)
    if not cloud_url:
        return None, 'Upload failed. Firebase Storage may be unavailable.'

    return {
        'url': cloud_url,
        'object_name': object_name,
        'content_type': content_type,
        'size': len(content_bytes),
    }, ''


def save_uploaded_files(files, allowed_ext, folder_prefix='packages'):
    """Upload many files in-memory to Firebase and return public URLs."""
    urls = []
    for f in files:
        uploaded, _ = _upload_single_file_to_firebase(f, allowed_ext, folder_prefix=folder_prefix)
        if uploaded and uploaded.get('url'):
            urls.append(uploaded['url'])
    return urls


def _normalize_media_url(value):
    """Normalize package media links to browser-safe URLs."""
    if not isinstance(value, str):
        return ''

    raw = value.strip()
    if not raw:
        return ''

    normalized = raw.replace('\\', '/')
    lowered = normalized.lower()

    # Handle legacy typo paths like /upload/file.jpg
    if '/static/upload/' in lowered:
        normalized = re.sub(r'/static/upload/', '/static/uploads/', normalized, flags=re.IGNORECASE)
        lowered = normalized.lower()
    if '/upload/' in lowered:
        normalized = re.sub(r'/upload/', '/uploads/', normalized, flags=re.IGNORECASE)
        lowered = normalized.lower()

    if lowered.startswith(('http://', 'https://', 'data:', 'blob:')):
        return normalized
    if lowered.startswith('gs://'):
        # Convert gs://bucket/object into app-routed uploads path.
        no_scheme = normalized[5:]
        parts = no_scheme.split('/', 1)
        object_name = parts[1] if len(parts) > 1 else ''
        object_name = unquote(object_name).strip().lstrip('/')
        if object_name:
            return _upload_public_url(object_name)
        return ''
    if lowered.startswith('//'):
        return f'https:{normalized}'
    if lowered.startswith('www.'):
        return f'https://{normalized}'

    # Handle absolute local paths that include /static/uploads/... or /uploads/...
    static_idx = lowered.find('/static/uploads/')
    if static_idx >= 0:
        tail = normalized[static_idx + len('/static/uploads/'):]
        return _upload_public_url(tail)

    uploads_idx = lowered.find('/uploads/')
    if uploads_idx >= 0:
        return normalized[uploads_idx:]

    if lowered.startswith('static/uploads/'):
        tail = normalized[len('static/uploads/'):]
        return _upload_public_url(tail)
    if lowered.startswith('/static/uploads/'):
        tail = normalized[len('/static/uploads/'):]
        return _upload_public_url(tail)
    if lowered.startswith('static/upload/'):
        tail = normalized[len('static/upload/'):]
        return _upload_public_url(tail)
    if lowered.startswith('/static/upload/'):
        tail = normalized[len('/static/upload/'):]
        return _upload_public_url(tail)
    if lowered.startswith('upload/'):
        tail = normalized[len('upload/'):]
        return _upload_public_url(tail)
    if lowered.startswith('/upload/'):
        tail = normalized[len('/upload/'):]
        return _upload_public_url(tail)
    if lowered.startswith('uploads/'):
        return '/' + normalized.lstrip('/')
    if lowered.startswith('/uploads/'):
        return normalized

    if lowered.startswith('./'):
        trimmed = normalized[2:]
        trimmed_lower = trimmed.lower()
        if trimmed_lower.startswith('static/uploads/'):
            return _upload_public_url(trimmed[len('static/uploads/'):])
        if trimmed_lower.startswith('static/upload/'):
            return _upload_public_url(trimmed[len('static/upload/'):])
        if trimmed_lower.startswith('upload/'):
            return _upload_public_url(trimmed[len('upload/'):])
        if trimmed_lower.startswith('uploads/'):
            return '/' + trimmed.lstrip('/')
        normalized = trimmed

    # Convert encoded Firebase object names like packages%2Fabc.jpg.
    if '%2f' in lowered and '/' not in normalized:
        decoded = unquote(normalized).strip().lstrip('/')
        if '/' in decoded:
            return _upload_public_url(decoded)

    if '/' not in normalized and re.match(r'^[A-Za-z0-9_.-]+\.(png|jpe?g|gif|webp)$', normalized, re.IGNORECASE):
        return _upload_public_url(normalized)

    # Legacy records may store bare object keys/ids (without folder or extension).
    if '/' not in normalized and re.match(r'^[A-Za-z0-9_.-]{12,}$', normalized):
        return _upload_public_url(normalized)

    if normalized.startswith('/'):
        return normalized

    return normalized


def _normalize_media_list(values):
    if isinstance(values, str):
        values = [values]
    if not isinstance(values, list):
        return []

    normalized_values = []
    seen = set()
    for value in values:
        cleaned = _normalize_media_url(value)
        if not cleaned or cleaned in seen:
            continue
        normalized_values.append(cleaned)
        seen.add(cleaned)
    return normalized_values


def _normalize_package_media(package):
    if not isinstance(package, dict):
        return package

    image = _normalize_media_url(package.get('image', ''))
    images = _normalize_media_list(package.get('images', []))
    gallery = _normalize_media_list(package.get('gallery', []))

    if not image and images:
        image = images[0]
    if not image and gallery:
        image = gallery[0]

    if image:
        images = [image] + [u for u in images if u != image]
        if not gallery:
            gallery = [image]

    package['image'] = image
    package['images'] = images
    package['gallery'] = gallery

    if 'package_image' in package:
        package['package_image'] = _normalize_media_url(package.get('package_image', ''))

    return package


def _media_preview_list(values, limit=3):
    items = _normalize_media_list(values)
    preview = items[:limit]
    if len(items) > limit:
        preview.append(f'...(+{len(items) - limit} more)')
    return preview


def _log_package_media_trace(stage, package_id, agency_id, payload):
    """Structured logs to trace image/gallery transitions during package edits."""
    try:
        serialized = json.dumps(payload, ensure_ascii=True, default=str)
    except Exception:
        serialized = str(payload)
    app.logger.info(
        'MEDIA_TRACE stage=%s package_id=%s agency_id=%s payload=%s',
        stage,
        package_id,
        agency_id,
        serialized,
    )


def _extract_upload_object_name(media_url):
    """Extract storage object key from /uploads, /upload, /static/uploads, or /static/upload paths."""
    if not isinstance(media_url, str):
        return ''

    raw = media_url.strip()
    if not raw:
        return ''

    try:
        parsed = urlparse(raw)
        candidate = parsed.path if (parsed.scheme or parsed.netloc) else raw
    except Exception:
        candidate = raw

    normalized = candidate.replace('\\', '/').strip()
    lowered = normalized.lower()

    object_name = ''
    static_marker = '/static/uploads/'
    static_typo_marker = '/static/upload/'
    uploads_marker = '/uploads/'
    upload_typo_marker = '/upload/'
    if static_marker in lowered:
        idx = lowered.find(static_marker)
        object_name = normalized[idx + len(static_marker):]
    elif static_typo_marker in lowered:
        idx = lowered.find(static_typo_marker)
        object_name = normalized[idx + len(static_typo_marker):]
    elif uploads_marker in lowered:
        idx = lowered.find(uploads_marker)
        object_name = normalized[idx + len(uploads_marker):]
    elif upload_typo_marker in lowered:
        idx = lowered.find(upload_typo_marker)
        object_name = normalized[idx + len(upload_typo_marker):]
    elif lowered.startswith('static/uploads/'):
        object_name = normalized[len('static/uploads/'):]
    elif lowered.startswith('static/upload/'):
        object_name = normalized[len('static/upload/'):]
    elif lowered.startswith('uploads/'):
        object_name = normalized[len('uploads/'):]
    elif lowered.startswith('upload/'):
        object_name = normalized[len('upload/'):]

    object_name = object_name.split('?', 1)[0].split('#', 1)[0].strip().lstrip('/')
    if not object_name:
        return ''

    # Normalize and reject traversal-like paths.
    segments = [seg for seg in object_name.split('/') if seg and seg != '.']
    if any(seg == '..' for seg in segments):
        return ''
    return '/'.join(segments)


def _migrate_media_url_to_cloud(media_url):
    """Migrate one upload URL/path to Firebase Storage URL if possible."""
    cleaned = _normalize_media_url(media_url)
    if not cleaned:
        return '', 'empty'

    object_name = _extract_upload_object_name(cleaned)
    if not object_name:
        return cleaned, 'external'

    existing_cloud_url = _firebase_object_url_if_exists(object_name)
    if existing_cloud_url:
        return existing_cloud_url, 'already_cloud'

    local_path = os.path.join(UPLOAD_FOLDER, *object_name.split('/'))
    if not os.path.exists(local_path):
        return cleaned, 'missing_local'

    try:
        with open(local_path, 'rb') as f:
            content = f.read()
    except Exception:
        return cleaned, 'read_failed'

    if not content:
        return cleaned, 'missing_local'

    cloud_url = _upload_to_firebase_storage(content, object_name, _guess_content_type(object_name))
    if cloud_url:
        return cloud_url, 'uploaded'
    return cleaned, 'upload_failed'


def _migrate_package_media_to_cloud(package):
    """Return (patch, stats) for one package media migration run."""
    stats = {
        'scanned': 0,
        'uploaded': 0,
        'already_cloud': 0,
        'external': 0,
        'missing_local': 0,
        'read_failed': 0,
        'upload_failed': 0,
        'empty': 0,
    }

    if not isinstance(package, dict):
        return {}, stats

    old_image = _normalize_media_url(package.get('image', ''))
    old_images = _normalize_media_list(package.get('images', []))
    old_gallery = _normalize_media_list(package.get('gallery', []))

    migrated_image, status = _migrate_media_url_to_cloud(old_image)
    stats['scanned'] += 1
    stats[status] = stats.get(status, 0) + 1

    migrated_images = []
    image_sources = package.get('images', [])
    if isinstance(image_sources, str):
        image_sources = [image_sources]
    for item in image_sources if isinstance(image_sources, list) else []:
        migrated, status = _migrate_media_url_to_cloud(item)
        stats['scanned'] += 1
        stats[status] = stats.get(status, 0) + 1
        if migrated:
            migrated_images.append(migrated)

    migrated_gallery = []
    gallery_sources = package.get('gallery', [])
    if isinstance(gallery_sources, str):
        gallery_sources = [gallery_sources]
    for item in gallery_sources if isinstance(gallery_sources, list) else []:
        migrated, status = _migrate_media_url_to_cloud(item)
        stats['scanned'] += 1
        stats[status] = stats.get(status, 0) + 1
        if migrated:
            migrated_gallery.append(migrated)

    migrated_images = _normalize_media_list(migrated_images)
    migrated_gallery = _normalize_media_list(migrated_gallery)
    migrated_image = _normalize_media_url(migrated_image)

    if not migrated_image and migrated_images:
        migrated_image = migrated_images[0]
    if not migrated_image and migrated_gallery:
        migrated_image = migrated_gallery[0]

    if migrated_image:
        migrated_images = [migrated_image] + [u for u in migrated_images if u != migrated_image]
        if not migrated_gallery:
            migrated_gallery = [migrated_image]

    patch = {}
    if migrated_image != old_image:
        patch['image'] = migrated_image
    if migrated_images != old_images:
        patch['images'] = migrated_images
    if migrated_gallery != old_gallery:
        patch['gallery'] = migrated_gallery

    return patch, stats

# --- Firebase Initialization (Realtime Database â€” free Spark plan) ---
FIREBASE_ENABLED = False
FIREBASE_STORAGE_ENABLED = False
FIREBASE_STORAGE_BUCKET = ''
FIREBASE_STORAGE_BUCKET_CANDIDATES = []
FIREBASE_PROJECT_ID = ''

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


def _resolve_storage_bucket_candidates(project_id):
    """Resolve ordered bucket candidates (env, config, and common Firebase defaults)."""
    candidates = []
    for val in (
        os.environ.get('FIREBASE_STORAGE_BUCKET', '').strip(),
        FIREBASE_WEB_CONFIG.get('storageBucket', '').strip(),
        f'{project_id}.appspot.com',
        f'{project_id}.firebasestorage.app',
    ):
        if val and val not in candidates:
            candidates.append(val)
    return candidates


def _iter_valid_user_records(all_users):
    """Yield (key, user_dict) entries while skipping null/invalid nodes."""
    if not all_users or not isinstance(all_users, dict):
        return
    for uid, udata in all_users.items():
        if isinstance(udata, dict):
            yield uid, udata


def _normalize_email(value):
    return str(value or '').strip().lower()


def _normalize_role(value):
    role = str(value or '').strip().lower()
    if not role:
        return 'user'

    compact = role.replace('_', ' ').replace('-', ' ')
    if 'agency' in compact or 'operator' in compact or 'vendor' in compact:
        return 'agency'
    if compact in ('user', 'customer', 'traveler', 'traveller', 'tourist'):
        return 'user'
    return 'user'


def _verify_user_password(user_key, user_data, password):
    """Verify hashed/legacy passwords and migrate legacy plaintext when possible."""
    from werkzeug.security import check_password_hash, generate_password_hash

    pwd_hash = (
        (user_data or {}).get('password_hash')
        or (user_data or {}).get('passwordHash')
        or ''
    )
    if pwd_hash:
        try:
            if check_password_hash(pwd_hash, password):
                return True
        except Exception:
            pass

    legacy_password = (user_data or {}).get('password', '')
    if isinstance(legacy_password, str) and legacy_password and legacy_password == password:
        # One-time migration from plaintext to password_hash.
        patch = {
            'password_hash': generate_password_hash(password),
            'password': ''
        }
        try:
            if FIREBASE_ENABLED:
                firebase_db.reference(f'/users/{user_key}').update(patch)
            _update_local_user(user_key, patch)
        except Exception as e:
            print(f"âš ï¸  Legacy password migration warning for {user_key}: {e}")
        try:
            user_data.update(patch)
        except Exception:
            pass
        return True

    return False


def _generate_password_reset_otp():
    return ''.join(str(secrets.randbelow(10)) for _ in range(PASSWORD_RESET_OTP_LEN))


def _write_local_users_nolock(users_map):
    os.makedirs(LOCAL_RUNTIME_DIR, exist_ok=True)
    tmp_file = LOCAL_USERS_FILE + '.tmp'
    with open(tmp_file, 'w', encoding='utf-8') as f:
        json.dump(users_map, f, ensure_ascii=True)
    os.replace(tmp_file, LOCAL_USERS_FILE)


def _read_local_users():
    """Load local users from disk for non-Firebase deployments."""
    with _LOCAL_USERS_LOCK:
        users = {}
        if os.path.exists(LOCAL_USERS_FILE):
            try:
                with open(LOCAL_USERS_FILE, 'r', encoding='utf-8') as f:
                    raw = json.load(f)
                    if isinstance(raw, dict):
                        users = {str(k): v for k, v in raw.items() if isinstance(v, dict)}
            except Exception as e:
                print(f"âš ï¸  Local users file read error: {e}")

        # One-time seed from in-memory users if present.
        seeded = False
        mem_users = MOCK_DATABASE.get('users', {}) if isinstance(MOCK_DATABASE, dict) else {}
        if isinstance(mem_users, dict):
            for uid, udata in mem_users.items():
                if uid not in users and isinstance(udata, dict):
                    users[uid] = udata
                    seeded = True

        if seeded:
            try:
                _write_local_users_nolock(users)
            except Exception as e:
                print(f"âš ï¸  Local users seed write error: {e}")

        return users


def _upsert_local_user(user_id, user_record):
    with _LOCAL_USERS_LOCK:
        users = {}
        if os.path.exists(LOCAL_USERS_FILE):
            try:
                with open(LOCAL_USERS_FILE, 'r', encoding='utf-8') as f:
                    raw = json.load(f)
                    if isinstance(raw, dict):
                        users = {str(k): v for k, v in raw.items() if isinstance(v, dict)}
            except Exception as e:
                print(f"âš ï¸  Local users preload error: {e}")
        users[str(user_id)] = user_record
        _write_local_users_nolock(users)


def _update_local_user(user_id, patch):
    with _LOCAL_USERS_LOCK:
        users = {}
        if os.path.exists(LOCAL_USERS_FILE):
            try:
                with open(LOCAL_USERS_FILE, 'r', encoding='utf-8') as f:
                    raw = json.load(f)
                    if isinstance(raw, dict):
                        users = {str(k): v for k, v in raw.items() if isinstance(v, dict)}
            except Exception as e:
                print(f"âš ï¸  Local users preload error: {e}")
        obj = users.get(str(user_id), {})
        if isinstance(obj, dict):
            obj.update(patch)
            users[str(user_id)] = obj
            _write_local_users_nolock(users)


def _persist_user_patch(user_id, patch):
    """Persist user patch to primary store and local mirror."""
    if FIREBASE_ENABLED:
        firebase_db.reference(f'/users/{user_id}').update(patch)
    _update_local_user(user_id, patch)


def _find_accounts_by_email(email):
    all_users = _get_users_map()
    matches = []
    for uid, udata in _iter_valid_user_records(all_users):
        if _normalize_email(udata.get('email', '')) == email:
            matches.append((uid, udata))
    return matches


def _resolve_account_for_role(email, role):
    """Resolve account for role, with a single-account fallback for wrong tab picks."""
    role = _normalize_role(role)
    matches = _find_accounts_by_email(email)
    if not matches:
        return None, None, 'not_found'

    role_matches = []
    for uid, udata in matches:
        account_role = (udata.get('role', 'user') or 'user').strip().lower()
        if account_role == role:
            role_matches.append((uid, udata))

    if role_matches:
        return role_matches[0][0], role_matches[0][1], ''

    if len(matches) == 1:
        return matches[0][0], matches[0][1], ''

    return None, None, 'role_conflict'


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
            _update_local_user(user_key, payload)
        except Exception as e:
            print(f"âš ï¸  Firebase last-login update error: {e}")
    else:
        try:
            _update_local_user(user_key, payload)
        except Exception as e:
            print(f"âš ï¸  Local last-login update error: {e}")


@app.before_request
def _normalize_session_role():
    if 'role' in session:
        normalized = _normalize_role(session.get('role', ''))
        if session.get('role') != normalized:
            session['role'] = normalized


try:
    sa_info, source = _load_service_account_info()
    if sa_info:
        project_id = sa_info.get('project_id', 'my-project')
        db_url = _resolve_database_url(project_id)
        storage_candidates = _resolve_storage_bucket_candidates(project_id)
        storage_bucket = storage_candidates[0] if storage_candidates else ''
        cred = credentials.Certificate(sa_info)
        firebase_admin.initialize_app(cred, {
            'databaseURL': db_url,
            'storageBucket': storage_bucket,
        })
        FIREBASE_ENABLED = True
        FIREBASE_PROJECT_ID = project_id
        FIREBASE_STORAGE_BUCKET = storage_bucket
        FIREBASE_STORAGE_BUCKET_CANDIDATES = storage_candidates
        FIREBASE_STORAGE_ENABLED = bool(storage_bucket)
        print(f"âœ… Firebase Realtime Database initialized via {source}.")
        print(f"   Database URL: {db_url}")
        if FIREBASE_STORAGE_ENABLED:
            print(f"âœ… Firebase Storage enabled with bucket: {FIREBASE_STORAGE_BUCKET}")
            if len(FIREBASE_STORAGE_BUCKET_CANDIDATES) > 1:
                print(f"   Storage bucket candidates: {', '.join(FIREBASE_STORAGE_BUCKET_CANDIDATES)}")
        else:
            print("â„¹ï¸  Firebase Storage bucket not configured; uploads will use local storage fallback.")
    else:
        print("â„¹ï¸  Firebase credentials not found. Running in MOCK mode.")
        print("   Add FIREBASE_SERVICE_ACCOUNT_JSON on Render to enable realtime DB writes.")
        print("   Add FIREBASE_STORAGE_BUCKET and/or storageBucket config to persist uploads in cloud storage.")
        print(f"   Using local auth store: {LOCAL_USERS_FILE}")
except Exception as e:
    print(f"âš ï¸  Firebase initialization failed: {e}")
    print("   Running in MOCK mode (in-memory database)")
    print("   Uploads will use local disk fallback unless Firebase initialization succeeds.")
    print(f"   Using local auth store: {LOCAL_USERS_FILE}")

# Make session data available to all templates for dynamic navbar
@app.context_processor
def inject_user():
    return dict(
        logged_in=bool(session.get('user_id')),
        user_role=_normalize_role(session.get('role', '')),
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
            print(f"ðŸ§¹ Cleared all {len(existing)} old packages from Firebase. Fresh start!")
        else:
            print("â„¹ï¸  No packages in Firebase to clean up.")
    except Exception as e:
        print(f"âš ï¸  Cleanup failed: {e}")

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
            print(f"âš ï¸  Firebase read error: {e}")
            data = {}
    else:
        data = MOCK_DATABASE['packages']

    recent_booking_map = _get_recent_bookings_map()
    for pkg in data.values():
        if isinstance(pkg, dict):
            _normalize_package_media(pkg)
            _attach_carbon_score(pkg)
            _attach_food_trail(pkg)
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
            print(f"âš ï¸  Firebase read error: {e}")
            data = None
    else:
        data = MOCK_DATABASE['packages'].get(pkg_id)

    if isinstance(data, dict):
        _normalize_package_media(data)
        _attach_carbon_score(data)
        _attach_food_trail(data)
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
            print(f"âš ï¸  Firebase write error: {e}")
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
            print(f"âš ï¸  Firebase update error: {e}")
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
            print(f"âš ï¸  Firebase delete error: {e}")
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
                        _normalize_package_media(pkg)
                        _attach_carbon_score(pkg)
                        _attach_food_trail(pkg)
                        _attach_recent_booking_label(pkg, recent_booking_map)
                return packages
            return []
        except Exception as e:
            print(f"âš ï¸  Firebase query error: {e}")
    packages = [pkg for pkg in MOCK_DATABASE['packages'].values() if pkg.get('agency_id') == agency_id]
    recent_booking_map = _get_recent_bookings_map()
    for pkg in packages:
        if isinstance(pkg, dict):
            _normalize_package_media(pkg)
            _attach_carbon_score(pkg)
            _attach_food_trail(pkg)
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
            print(f"âš ï¸  Firebase booking social-proof read error: {e}")
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
    cloud_object = f'stories/{filename}'
    abs_path = os.path.join(STORY_AUDIO_FOLDER, filename)
    rel_url = _upload_public_url(f'stories/{filename}')

    if FIREBASE_STORAGE_ENABLED:
        if not force:
            existing_url = _firebase_object_url_if_exists(cloud_object)
            if existing_url:
                return existing_url

        if not GTTS_AVAILABLE:
            return ''

        try:
            tts = gTTS(text=narration, lang='en', slow=False)
            audio_buffer = io.BytesIO()
            tts.write_to_fp(audio_buffer)
            audio_bytes = audio_buffer.getvalue()
            if not audio_bytes:
                return ''
            cloud_url = _upload_to_firebase_storage(audio_bytes, cloud_object, 'audio/mpeg')
            if cloud_url:
                return cloud_url
        except Exception as e:
            print(f"âš ï¸  Story audio cloud generation error: {e}")

    if os.path.exists(abs_path) and not force:
        return rel_url

    if not GTTS_AVAILABLE:
        return ''

    try:
        tts = gTTS(text=narration, lang='en', slow=False)
        tts.save(abs_path)
        return rel_url
    except Exception as e:
        print(f"âš ï¸  Story audio generation error: {e}")
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
    if _normalize_role(session.get('role')) != 'agency':
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


_FOOD_TRAIL_LIBRARY = {
    'karnataka': [
        {'name': 'Bisi Bele Bath', 'type': 'veg', 'note': 'Comforting rice-lentil classic with spice and ghee.'},
        {'name': 'Mysore Pak', 'type': 'veg', 'note': 'Rich gram-flour sweet with a melt-in-mouth finish.'},
        {'name': 'Ragi Mudde with Soppu Saaru', 'type': 'veg', 'note': 'Traditional millet ball served with leafy curry.'},
        {'name': 'Koli Saaru', 'type': 'non-veg', 'note': 'Peppery chicken curry loved in many Karnataka homes.'},
    ],
    'mysuru': [
        {'name': 'Mysore Masala Dosa', 'type': 'veg', 'note': 'Crisp dosa with spicy chutney layer and potato filling.'},
        {'name': 'Mysore Pak', 'type': 'veg', 'note': 'Signature sweet from old royal kitchens.'},
        {'name': 'Nanjangud Banana Bajji', 'type': 'veg', 'note': 'Local-style fritter, ideal for evening snack breaks.'},
        {'name': 'Mutton Chops', 'type': 'non-veg', 'note': 'Spiced, slow-cooked side served in classic military hotels.'},
    ],
    'chikmagalur': [
        {'name': 'Akki Roti', 'type': 'veg', 'note': 'Rustic rice flatbread served hot with chutney.'},
        {'name': 'Neer Dosa', 'type': 'veg', 'note': 'Soft lace-like dosa that pairs with coconut gravies.'},
        {'name': 'Filter Coffee', 'type': 'veg', 'note': 'Estate-fresh brew, a must in coffee country.'},
        {'name': 'Chicken Ghee Roast', 'type': 'non-veg', 'note': 'Bold roast with red chilli and aromatic spices.'},
    ],
    'coorg': [
        {'name': 'Kadambuttu', 'type': 'veg', 'note': 'Steamed rice dumplings, a hallmark Coorg side.'},
        {'name': 'Pandi Curry', 'type': 'non-veg', 'note': 'Famous Coorg-style pork curry with kachampuli tang.'},
        {'name': 'Bamboo Shoot Curry', 'type': 'veg', 'note': 'Seasonal hill delicacy with earthy flavor.'},
        {'name': 'Noolputtu with Curry', 'type': 'veg', 'note': 'String hoppers enjoyed with coconut-based curries.'},
    ],
    'hampi': [
        {'name': 'Jolada Rotti', 'type': 'veg', 'note': 'North Karnataka sorghum flatbread served with ennegayi.'},
        {'name': 'Ennegayi', 'type': 'veg', 'note': 'Stuffed brinjal curry rich in roasted spice paste.'},
        {'name': 'Shenga Chutney Pudi', 'type': 'veg', 'note': 'Nutty dry chutney powder, great with rotis.'},
        {'name': 'Kharabath Mutton', 'type': 'non-veg', 'note': 'Local spicy meat style popular in this region.'},
    ],
    'gokarna': [
        {'name': 'Bangude Pulimunchi', 'type': 'non-veg', 'note': 'Coastal fish curry with tangy chilli profile.'},
        {'name': 'Kane Rava Fry', 'type': 'non-veg', 'note': 'Crispy semolina fish fry from seaside kitchens.'},
        {'name': 'Patrode', 'type': 'veg', 'note': 'Steamed colocasia-leaf rolls with spiced rice mix.'},
        {'name': 'Mangalorean Buns', 'type': 'veg', 'note': 'Sweet-savoury banana buns for tea-time snacking.'},
    ],
    'bandipur': [
        {'name': 'Ragi Mudde with Bassaru', 'type': 'veg', 'note': 'Hearty millet meal ideal before safari stretches.'},
        {'name': 'Avarekai Saaru', 'type': 'veg', 'note': 'Bean-forward curry with village-style seasoning.'},
        {'name': 'Country Chicken Saaru', 'type': 'non-veg', 'note': 'Lightly spiced curry common in forest-side homestays.'},
        {'name': 'Kesari Bath', 'type': 'veg', 'note': 'Classic sweet ending for a local breakfast plate.'},
    ],
    'sakleshpur': [
        {'name': 'Malnad Gulla Palya', 'type': 'veg', 'note': 'Native brinjal curry from Malnad home kitchens.'},
        {'name': 'Kesuvina Soppu Curry', 'type': 'veg', 'note': 'Leafy hill-special dish with coconut spice base.'},
        {'name': 'Chicken Sukka', 'type': 'non-veg', 'note': 'Dry roast-style chicken with pepper and curry leaves.'},
        {'name': 'Filter Coffee', 'type': 'veg', 'note': 'Must-have hill-station coffee between viewpoints.'},
    ],
    'bengaluru': [
        {'name': 'Thatte Idli', 'type': 'veg', 'note': 'Soft plate-sized idli popular in old Bengaluru joints.'},
        {'name': 'Benne Masala Dosa', 'type': 'veg', 'note': 'Butter-heavy dosa with crisp edges and rich center.'},
        {'name': 'Donne Biryani', 'type': 'non-veg', 'note': 'Iconic biryani served in eco leaf bowls.'},
        {'name': 'Maddur Vada', 'type': 'veg', 'note': 'Crunchy onion vada, perfect for road trips nearby.'},
    ],
}


def _normalize_food_type(value):
    label = str(value or '').strip().lower()
    if label in ('veg', 'vegetarian', 'v'):
        return 'veg'
    if label in ('non-veg', 'non veg', 'nonveg', 'nv', 'non vegetarian', 'non-vegetarian'):
        return 'non-veg'
    return 'veg'


def _normalize_food_trail(food_items):
    if isinstance(food_items, dict):
        food_items = [food_items]
    if not isinstance(food_items, list):
        return []

    cleaned_items = []
    seen = set()
    for item in food_items:
        if isinstance(item, str):
            dish_name = item.strip()
            dish_type = 'veg'
            dish_note = ''
        elif isinstance(item, dict):
            dish_name = str(item.get('name', '')).strip()
            dish_type = _normalize_food_type(item.get('type', 'veg'))
            dish_note = str(item.get('note', '')).strip()
        else:
            continue

        if not dish_name:
            continue

        key = f"{dish_name.lower()}::{dish_type}"
        if key in seen:
            continue

        cleaned_items.append({'name': dish_name, 'type': dish_type, 'note': dish_note})
        seen.add(key)

        if len(cleaned_items) >= 8:
            break

    return cleaned_items


def _parse_food_trail_form(raw_text):
    """Parse dashboard textarea lines into food trail objects.

    Expected line format:
    Dish Name | veg/non-veg | short note
    """
    text = str(raw_text or '').strip()
    if not text:
        return []

    items = []
    for line in text.splitlines():
        row = line.strip()
        if not row:
            continue

        if '|' in row:
            parts = [p.strip() for p in row.split('|', 2)]
        elif ',' in row:
            parts = [p.strip() for p in row.split(',', 2)]
        else:
            parts = [row, 'veg', '']

        dish_name = parts[0] if len(parts) >= 1 else ''
        dish_type = parts[1] if len(parts) >= 2 else 'veg'
        dish_note = parts[2] if len(parts) >= 3 else ''

        if dish_name:
            items.append({'name': dish_name, 'type': dish_type, 'note': dish_note})

    return _normalize_food_trail(items)


def _resolve_food_trail_key(package):
    location = package.get('location', {}) if isinstance(package.get('location', {}), dict) else {}
    location_name = str(location.get('name', '')).strip()
    haystack = ' '.join([
        str(package.get('title', '')),
        str(package.get('description', '')),
        str(package.get('tag', '')),
        location_name,
    ]).lower()

    keyword_map = [
        ('mysuru', 'mysuru'),
        ('mysore', 'mysuru'),
        ('chikmagalur', 'chikmagalur'),
        ('chikkamagaluru', 'chikmagalur'),
        ('coorg', 'coorg'),
        ('kodagu', 'coorg'),
        ('hampi', 'hampi'),
        ('gokarna', 'gokarna'),
        ('bandipur', 'bandipur'),
        ('sakleshpur', 'sakleshpur'),
        ('bengaluru', 'bengaluru'),
        ('bangalore', 'bengaluru'),
    ]

    for needle, region_key in keyword_map:
        if needle in haystack:
            return region_key

    tag_text = str(package.get('tag', '')).strip().lower()
    if 'coastal' in tag_text:
        return 'gokarna'
    if 'wildlife' in tag_text:
        return 'bandipur'
    return 'karnataka'


def _attach_food_trail(package):
    custom_food_trail = _normalize_food_trail(package.get('food_trail', []))
    if custom_food_trail:
        package['food_trail'] = custom_food_trail
        return package

    region_key = _resolve_food_trail_key(package)
    package['food_trail'] = _normalize_food_trail(
        _FOOD_TRAIL_LIBRARY.get(region_key, _FOOD_TRAIL_LIBRARY.get('karnataka', []))
    )
    return package


def _get_users_map():
    """Get all users as dict {user_id: user_data}."""
    if FIREBASE_ENABLED:
        try:
            users = firebase_db.reference('/users').get()
            if users and isinstance(users, dict):
                # Keep a local mirror for resilience during transient Firebase issues.
                try:
                    with _LOCAL_USERS_LOCK:
                        _write_local_users_nolock({str(k): v for k, v in users.items() if isinstance(v, dict)})
                except Exception as mirror_err:
                    print(f"âš ï¸  Local users mirror write error: {mirror_err}")
                return users
        except Exception as e:
            print(f"âš ï¸  Firebase users query error: {e}")
            fallback = _read_local_users()
            if fallback:
                print("â„¹ï¸  Using local auth fallback due to Firebase read issue.")
                return fallback
        return {}
    return _read_local_users()


def _get_agency_user(agency_id):
    users = _get_users_map()
    user = users.get(agency_id)
    if user and _normalize_role(user.get('role')) == 'agency':
        return agency_id, user
    return None, None


def _get_all_agency_users():
    users = _get_users_map()
    return [(uid, udata) for uid, udata in users.items() if _normalize_role(udata.get('role')) == 'agency']


def _save_notification(agency_id, payload):
    notification_id = payload.get('id') or uuid.uuid4().hex[:12]
    payload['id'] = notification_id
    if FIREBASE_ENABLED:
        try:
            firebase_db.reference(f'/notifications/{agency_id}/{notification_id}').set(payload)
            return True
        except Exception as e:
            print(f"âš ï¸  Firebase notification write error: {e}")
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
            print(f"âš ï¸  Firebase notification read error: {e}")
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
            print(f"âš ï¸  Firebase notification update error: {e}")
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
        print(f"âš ï¸  Email alert error: {e}")
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
        print(f"âš ï¸  WhatsApp alert error: {e}")
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

# One-time cleanup already done â€” disable to protect new packages
# db_clear_old_data()

@app.route('/')
def index():
    return render_template('index.html')


@app.route('/uploads/<path:filename>')
def uploaded_media(filename):
    """Serve uploaded media from local disk, then Firebase Storage fallback."""
    safe_name = str(filename or '').replace('\\', '/').lstrip('/')
    if not safe_name:
        return 'File not found', 404

    cache_key = f'uploaded_media:{safe_name.lower()}'
    cached = _media_route_cache_get(cache_key)
    if cached == _MEDIA_CACHE_IMAGE_FALLBACK:
        return redirect(_MEDIA_PLACEHOLDER_URL)
    if cached == _MEDIA_CACHE_NOT_FOUND:
        return 'File not found', 404
    if isinstance(cached, str) and cached.startswith('local:'):
        cached_local = cached[len('local:'):]
        cached_local_path = os.path.join(UPLOAD_FOLDER, *cached_local.split('/'))
        if os.path.exists(cached_local_path):
            return send_from_directory(UPLOAD_FOLDER, cached_local)
    if isinstance(cached, str) and cached.startswith(('http://', 'https://')):
        return redirect(cached)

    def _add_candidate(candidates, value, seen):
        cand = str(value or '').replace('\\', '/').strip().lstrip('/')
        if not cand:
            return
        segments = [seg for seg in cand.split('/') if seg]
        if not segments or any(seg in ('.', '..') for seg in segments):
            return
        normalized = '/'.join(segments)
        if normalized in seen:
            return
        seen.add(normalized)
        candidates.append(normalized)

    candidates = []
    seen = set()
    _add_candidate(candidates, safe_name, seen)
    _add_candidate(candidates, unquote(safe_name), seen)

    ext_match = re.search(r'\.([A-Za-z0-9]{2,6})$', safe_name)
    has_extension = bool(ext_match)
    current_ext = (ext_match.group(1).lower() if ext_match else '')
    prefixes = ('packages', 'stories', 'uploads', 'gallery', 'reviews')

    # Legacy auto-generated hash filenames are often already missing; fail fast.
    if re.match(r'^[a-f0-9]{24,}\.(png|jpe?g|gif|webp)$', safe_name, flags=re.IGNORECASE):
        app.logger.warning('MEDIA_404_FAST_FALLBACK requested=%s', safe_name)
        _media_route_cache_set(cache_key, _MEDIA_CACHE_IMAGE_FALLBACK, ttl=_MEDIA_ROUTE_MISS_TTL)
        return redirect(_MEDIA_PLACEHOLDER_URL)

    if '/' not in safe_name:
        for prefix in prefixes:
            _add_candidate(candidates, f'{prefix}/{safe_name}', seen)

        if has_extension:
            base = safe_name.rsplit('.', 1)[0]
            _add_candidate(candidates, base, seen)
            for prefix in prefixes:
                _add_candidate(candidates, f'{prefix}/{base}', seen)

            ext_swaps = []
            if current_ext == 'jpg':
                ext_swaps.append('jpeg')
            elif current_ext == 'jpeg':
                ext_swaps.append('jpg')

            for alt_ext in ext_swaps:
                alt_name = f'{base}.{alt_ext}'
                _add_candidate(candidates, alt_name, seen)
                for prefix in prefixes:
                    _add_candidate(candidates, f'{prefix}/{alt_name}', seen)

        if not has_extension:
            for ext in ('jpg', 'jpeg', 'png', 'webp', 'gif', 'mp4', 'webm', 'mov', 'mp3'):
                _add_candidate(candidates, f'{safe_name}.{ext}', seen)
                for prefix in prefixes:
                    _add_candidate(candidates, f'{prefix}/{safe_name}.{ext}', seen)

    for candidate in candidates:
        local_path = os.path.join(UPLOAD_FOLDER, *candidate.split('/'))
        if os.path.exists(local_path):
            _media_route_cache_set(cache_key, f'local:{candidate}')
            return send_from_directory(UPLOAD_FOLDER, candidate)

    max_cloud_checks = 2 if ('/' not in safe_name and has_extension) else 4
    for candidate in candidates[:max_cloud_checks]:
        cloud_url = _firebase_object_url_if_exists(candidate)
        if cloud_url:
            _media_route_cache_set(cache_key, cloud_url)
            return redirect(cloud_url)

    if re.search(r'\.(png|jpe?g|gif|webp)$', safe_name, flags=re.IGNORECASE):
        app.logger.warning('MEDIA_404_IMAGE_FALLBACK requested=%s tried=%s', safe_name, json.dumps(candidates, ensure_ascii=True))
        _media_route_cache_set(cache_key, _MEDIA_CACHE_IMAGE_FALLBACK, ttl=_MEDIA_ROUTE_MISS_TTL)
        return redirect(_MEDIA_PLACEHOLDER_URL)

    app.logger.warning('MEDIA_404 requested=%s tried=%s', safe_name, json.dumps(candidates, ensure_ascii=True))
    _media_route_cache_set(cache_key, _MEDIA_CACHE_NOT_FOUND, ttl=_MEDIA_ROUTE_MISS_TTL)

    return 'File not found', 404


@app.route('/upload/<path:filename>')
def uploaded_media_legacy_alias(filename):
    """Legacy alias for singular /upload/* paths."""
    return uploaded_media(filename)

@app.route('/api/packages')
def get_packages():
    return db_get_all_packages()


@app.route('/api/media-storage-status')
def media_storage_status():
    return jsonify({
        'firebase_database_enabled': FIREBASE_ENABLED,
        'firebase_storage_enabled': FIREBASE_STORAGE_ENABLED,
        'firebase_project_id': FIREBASE_PROJECT_ID,
        'firebase_storage_bucket': FIREBASE_STORAGE_BUCKET,
        'firebase_storage_bucket_candidates': FIREBASE_STORAGE_BUCKET_CANDIDATES,
        'upload_public_prefix': UPLOAD_PUBLIC_PREFIX,
        'upload_folder': UPLOAD_FOLDER,
        'upload_persistent_dir_env': os.environ.get('UPLOAD_PERSISTENT_DIR', '').strip(),
    })


@app.route('/api/upload/image', methods=['POST'])
def api_upload_image():
    """Upload a single image file directly from request.files to Firebase Storage."""
    if _normalize_role(session.get('role')) != 'agency':
        return jsonify({'success': False, 'error': 'Unauthorized'}), 403

    if not FIREBASE_STORAGE_ENABLED:
        return jsonify({'success': False, 'error': 'Firebase Storage is not configured.'}), 503

    file_obj = request.files.get('file') or request.files.get('image')
    if not file_obj or not file_obj.filename:
        return jsonify({'success': False, 'error': 'No file provided.'}), 400

    if not allowed_file(file_obj.filename, ALLOWED_IMG_EXT):
        return jsonify({
            'success': False,
            'error': 'Invalid file type. Allowed: png, jpg, jpeg, gif, webp.',
        }), 400

    folder = _sanitize_upload_folder(request.form.get('folder', 'packages'), default_folder='packages')
    uploaded, err = _upload_single_file_to_firebase(file_obj, ALLOWED_IMG_EXT, folder_prefix=folder)
    if err:
        status = 400 if err in ('No file selected.', 'Invalid file type.', 'Empty file stream.') else 502
        return jsonify({'success': False, 'error': err}), status

    return jsonify({
        'success': True,
        'url': uploaded['url'],
        'object_path': uploaded['object_name'],
        'content_type': uploaded['content_type'],
        'size': uploaded['size'],
    })

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
        print(f"âš ï¸  Nearby restaurants fallback: {e}")
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
            print(f"âš ï¸  Trust-score OSM fallback: {osm_warning}")

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
            print(f"âš ï¸  Firebase booking write error: {e}")
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
        print(f"âš ï¸  Booking notification pipeline error: {e}")

    flash(f'Booking request submitted! Your Booking ID is {booking_id}. The agency will review and approve it shortly.', 'success')
    return redirect(url_for('profile'))


@app.route('/agency/booking/<booking_id>/approve', methods=['POST'])
def agency_approve_booking(booking_id):
    if _normalize_role(session.get('role')) != 'agency':
        return jsonify({'error': 'Unauthorized'}), 403
    booking = _get_booking(booking_id)
    if not booking:
        return jsonify({'error': 'Booking not found'}), 404
    # Agency dashboard acts as admin moderation inbox for pending requests.
    _update_booking_status(booking_id, 'approved')
    return jsonify({'success': True, 'status': 'approved'})


@app.route('/agency/booking/<booking_id>/reject', methods=['POST'])
def agency_reject_booking(booking_id):
    if _normalize_role(session.get('role')) != 'agency':
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
            print(f"âš ï¸  Firebase booking read error: {e}")
            return None
    return MOCK_DATABASE.get('bookings', {}).get(booking_id)


def _update_booking_status(booking_id, status):
    if FIREBASE_ENABLED:
        try:
            firebase_db.reference(f'/bookings/{booking_id}/status').set(status)
        except Exception as e:
            print(f"âš ï¸  Firebase booking update error: {e}")
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
            print(f"âš ï¸  Firebase bookings query error: {e}")
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
            print(f"âš ï¸  Firebase bookings query error: {e}")
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
            print(f"âš ï¸  Firebase bookings query error: {e}")
    else:
        bookings = [b for b in MOCK_DATABASE.get('bookings', {}).values() if b.get('user_id') == user_id]
    bookings.sort(key=lambda b: b.get('booked_on', ''), reverse=True)
    return bookings


@app.route('/agency/notifications')
def agency_notifications():
    if _normalize_role(session.get('role')) != 'agency':
        return jsonify({'error': 'Unauthorized'}), 403
    agency_id = session.get('user_id')
    notifications = _get_notifications_for_agency(agency_id, limit=20)
    unread_count = _count_unread_notifications(agency_id)
    return jsonify({'notifications': notifications, 'unread_count': unread_count})


@app.route('/agency/notifications/read', methods=['POST'])
def agency_notifications_mark_read():
    if _normalize_role(session.get('role')) != 'agency':
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
        email = _normalize_email(request.form.get('email', ''))
        password = request.form.get('password', '').strip()
        role = _normalize_role(request.form.get('role', 'user'))
        
        if not email or not password:
            flash('Email and password are required.', 'error')
            return render_template('login.html')
        
        # Look up all accounts matching this email first.
        email_matches = _find_accounts_by_email(email)

        if not email_matches:
            flash('Account not found. Please register first or check your role tab.', 'error')
            return render_template('login.html')

        # Verify password against matched accounts, prioritizing selected role.
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
            if _verify_user_password(uid, udata, password):
                user_key = uid
                user_data = udata
                break

        if not user_data:
            google_only_account = any(
                (u.get('auth_provider') == 'google')
                and not (
                    u.get('password_hash')
                    or u.get('passwordHash')
                    or u.get('password')
                )
                for _, u in email_matches
            )
            if google_only_account:
                flash('This account was created with Google. Please use Sign in with Google.', 'error')
            else:
                flash('Incorrect password. Please try again.', 'error')
            return render_template('login.html')
        
        # Set session
        authenticated_role = _normalize_role(user_data.get('role', 'user'))
        raw_role = str(user_data.get('role', 'user') or 'user')
        if raw_role != authenticated_role:
            try:
                _persist_user_patch(user_key, {'role': authenticated_role})
            except Exception as e:
                print(f"âš ï¸  Role normalization write warning for {user_key}: {e}")
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
    role = _normalize_role(data.get('role', 'user'))
    
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
        email = _normalize_email(decoded.get('email', ''))
        name = decoded.get('name', decoded.get('email', 'User'))
        photo = decoded.get('picture', '')
    except Exception as token_err:
        print(f'Token verification failed ({type(token_err).__name__}): {token_err}')
        
        # Method 2: Fallback â€” use client-provided UID and verify via Firebase Auth
        client_uid = data.get('uid', '')
        client_email = _normalize_email(data.get('email', ''))
        if client_uid:
            try:
                fb_user = firebase_auth.get_user(client_uid)
                # Confirm the email matches what the client sent (prevent spoofing)
                if fb_user.email and _normalize_email(fb_user.email) == client_email:
                    uid = fb_user.uid
                    email = _normalize_email(fb_user.email)
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
            'email': _normalize_email(email),
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
                if _normalize_email(udata.get('email', '')) == _normalize_email(email) and (udata.get('role', 'user') or 'user').strip().lower() == role:
                    existing_user_key = ukey
                    break
        except Exception as e:
            print(f'Firebase lookup error: {e}')
        
        # Use existing key or Firebase UID as key
        user_key = existing_user_key or uid
        
        firebase_db.reference(f'/users/{user_key}').update(user_record)
        try:
            _upsert_local_user(user_key, user_record)
        except Exception as mirror_err:
            print(f"âš ï¸  Local users mirror write error: {mirror_err}")
        
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


@app.route('/auth/forgot-password/request', methods=['POST'])
def forgot_password_request():
    data = request.get_json(silent=True) or {}
    email = _normalize_email(data.get('email', ''))
    role = _normalize_role(data.get('role', 'user'))

    if not email:
        return jsonify({'error': 'Email is required.'}), 400

    user_key, user_data, resolve_error = _resolve_account_for_role(email, role)
    if resolve_error == 'role_conflict':
        return jsonify({'error': 'This email exists under multiple roles. Please choose the correct role tab.'}), 409
    if resolve_error == 'not_found' or not user_key or not user_data:
        return jsonify({'error': 'Account not found for the provided email.'}), 404

    otp = _generate_password_reset_otp()
    otp_expiry_ts = int(time.time()) + PASSWORD_RESET_OTP_TTL_SEC

    from werkzeug.security import generate_password_hash
    patch = {
        'password_reset_otp_hash': generate_password_hash(otp),
        'password_reset_otp_expiry_ts': otp_expiry_ts,
        'password_reset_otp_attempts': 0,
        'password_reset_requested_at': int(time.time())
    }

    try:
        _persist_user_patch(user_key, patch)
    except Exception as e:
        print(f"âš ï¸  OTP persist error: {e}")
        return jsonify({'error': 'Could not start password reset. Please try again.'}), 500

    minutes = max(1, PASSWORD_RESET_OTP_TTL_SEC // 60)
    subject = 'NammaKarnataka Password Reset OTP'
    body = (
        f'Hello {user_data.get("name", "Traveler")},\n\n'
        f'Your OTP to reset your password is: {otp}\n'
        f'This OTP is valid for {minutes} minutes.\n\n'
        f'If you did not request this reset, please ignore this email.\n'
    )

    if not _send_email_alert(email, subject, body):
        try:
            _persist_user_patch(user_key, {
                'password_reset_otp_hash': '',
                'password_reset_otp_expiry_ts': 0,
                'password_reset_otp_attempts': 0
            })
        except Exception:
            pass
        return jsonify({'error': 'Email service is unavailable. Please try again later.'}), 503

    return jsonify({'success': True, 'message': f'OTP sent to {email}.'})


@app.route('/auth/forgot-password/verify', methods=['POST'])
def forgot_password_verify():
    data = request.get_json(silent=True) or {}
    email = _normalize_email(data.get('email', ''))
    role = _normalize_role(data.get('role', 'user'))
    otp = str(data.get('otp', '')).strip()
    new_password = str(data.get('new_password', '')).strip()

    if not email or not otp or not new_password:
        return jsonify({'error': 'Email, OTP, and new password are required.'}), 400
    if len(new_password) < 6:
        return jsonify({'error': 'New password must be at least 6 characters.'}), 400
    if not otp.isdigit() or len(otp) != PASSWORD_RESET_OTP_LEN:
        return jsonify({'error': 'Please enter a valid 6-digit OTP.'}), 400

    user_key, user_data, resolve_error = _resolve_account_for_role(email, role)
    if resolve_error == 'role_conflict':
        return jsonify({'error': 'This email exists under multiple roles. Please choose the correct role tab.'}), 409
    if resolve_error == 'not_found' or not user_key or not user_data:
        return jsonify({'error': 'Account not found for the provided email.'}), 404

    otp_hash = (user_data.get('password_reset_otp_hash') or '').strip()
    otp_expiry_ts = int(user_data.get('password_reset_otp_expiry_ts') or 0)
    attempts = int(user_data.get('password_reset_otp_attempts') or 0)
    now_ts = int(time.time())

    if not otp_hash or otp_expiry_ts <= 0:
        return jsonify({'error': 'OTP not requested. Please request a new OTP.'}), 400
    if now_ts > otp_expiry_ts:
        return jsonify({'error': 'OTP has expired. Please request a new OTP.'}), 400
    if attempts >= PASSWORD_RESET_MAX_ATTEMPTS:
        return jsonify({'error': 'Too many invalid OTP attempts. Please request a new OTP.'}), 429

    from werkzeug.security import check_password_hash, generate_password_hash
    otp_ok = False
    try:
        otp_ok = check_password_hash(otp_hash, otp)
    except Exception:
        otp_ok = False

    if not otp_ok:
        attempts += 1
        try:
            _persist_user_patch(user_key, {'password_reset_otp_attempts': attempts})
        except Exception:
            pass
        remaining = max(0, PASSWORD_RESET_MAX_ATTEMPTS - attempts)
        if remaining == 0:
            return jsonify({'error': 'Too many invalid OTP attempts. Please request a new OTP.'}), 429
        return jsonify({'error': f'Invalid OTP. {remaining} attempt(s) left.'}), 400

    account_role = (user_data.get('role', 'user') or 'user').strip().lower()
    patch = {
        'password_hash': generate_password_hash(new_password),
        'password': '',
        'passwordHash': '',
        'password_reset_otp_hash': '',
        'password_reset_otp_expiry_ts': 0,
        'password_reset_otp_attempts': 0,
        'password_reset_completed_at': now_ts
    }

    try:
        _persist_user_patch(user_key, patch)
    except Exception as e:
        print(f"âš ï¸  Password reset persist error: {e}")
        return jsonify({'error': 'Could not reset password. Please try again.'}), 500

    session['user_id'] = user_key
    session['role'] = account_role
    session['name'] = user_data.get('name', 'User')
    _touch_last_login(user_key)

    redirect_url = url_for('agency_dashboard') if account_role == 'agency' else url_for('profile')
    return jsonify({'success': True, 'redirect': redirect_url, 'message': 'Password reset successful.'})

@app.route('/register', methods=['GET', 'POST'])
def register():
    if request.method == 'POST':
        name = request.form.get('name', '').strip()
        email = _normalize_email(request.form.get('email', ''))
        password = request.form.get('password', '').strip()
        role = _normalize_role(request.form.get('role', 'user'))
        
        if not name or not email or not password:
            flash('All fields are required.', 'error')
            return render_template('login.html', show_register=True)
        
        if len(password) < 6:
            flash('Password must be at least 6 characters.', 'error')
            return render_template('login.html', show_register=True)
        
        # Check if email already exists
        email_exists = False
        all_users = _get_users_map()
        for uid, udata in _iter_valid_user_records(all_users):
            existing_role = (udata.get('role', 'user') or 'user').strip().lower()
            if _normalize_email(udata.get('email', '')) == email and existing_role == role:
                email_exists = True
                break
        
        if email_exists:
            flash('An account with this email already exists for this role.', 'error')
            return render_template('login.html', show_register=True)
        
        # Create user
        from werkzeug.security import generate_password_hash
        import time
        
        # Generate collision-proof user ID
        prefix = 'A' if role == 'agency' else 'U'
        user_id = f'{prefix}{uuid.uuid4().hex[:12]}'
        
        user_record = {
            'name': name,
            'email': email,
            'password_hash': generate_password_hash(password),
            'role': role,
            'created_at': int(time.time())
        }
        
        if FIREBASE_ENABLED:
            try:
                firebase_db.reference(f'/users/{user_id}').set(user_record)
                try:
                    _upsert_local_user(user_id, user_record)
                except Exception as mirror_err:
                    print(f"âš ï¸  Local users mirror write error: {mirror_err}")
            except Exception as e:
                print(f"âš ï¸  Firebase write error: {e}")
                flash('Registration failed. Please try again.', 'error')
                return render_template('login.html', show_register=True)
        else:
            try:
                _upsert_local_user(user_id, user_record)
            except Exception as e:
                print(f"âš ï¸  Local users write error: {e}")
                flash('Registration failed. Please try again.', 'error')
                return render_template('login.html', show_register=True)
        
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
    if _normalize_role(session.get('role')) != 'user':
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
            print(f"âš ï¸  Firebase user read error: {e}")
    
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
    if _normalize_role(session.get('role')) != 'agency':
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
            'revenue': f'â‚¹{total_revenue:,}',
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


def _slugify_package_id(title, max_len=48):
    raw = str(title or '').strip().lower()
    slug = re.sub(r'[^a-z0-9]+', '-', raw).strip('-')
    if not slug:
        slug = 'package'
    return slug[:max_len].strip('-') or 'package'


def _generate_unique_package_id(title):
    base = _slugify_package_id(title, max_len=48)
    candidate = base
    if not db_get_package(candidate):
        return candidate

    # Avoid accidental overwrite when titles are similar.
    for _ in range(8):
        suffix = uuid.uuid4().hex[:6]
        prefix = base[: max(1, 48 - 7)].strip('-') or 'package'
        candidate = f'{prefix}-{suffix}'
        if not db_get_package(candidate):
            return candidate

    return f'package-{uuid.uuid4().hex[:8]}'


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
    if _normalize_role(session.get('role')) != 'agency':
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


@app.route('/agency/media/migrate', methods=['GET', 'POST'])
def agency_migrate_media_to_cloud():
    if _normalize_role(session.get('role')) != 'agency':
        return jsonify({'success': False, 'error': 'Please login as an agency.'}), 401

    if request.method == 'GET' and request.args.get('run') != '1':
        return jsonify({
            'success': False,
            'message': 'Call this endpoint with POST or GET ?run=1 to execute migration.',
            'example': '/agency/media/migrate?run=1',
        }), 400

    if not FIREBASE_STORAGE_ENABLED:
        return jsonify({
            'success': False,
            'error': 'Firebase Storage is not enabled. Configure FIREBASE_STORAGE_BUCKET and credentials first.',
        }), 503

    agency_id = session.get('user_id')
    packages = db_get_packages_by_agency(agency_id)

    aggregate = {
        'scanned': 0,
        'uploaded': 0,
        'already_cloud': 0,
        'external': 0,
        'missing_local': 0,
        'read_failed': 0,
        'upload_failed': 0,
        'empty': 0,
    }
    updated_packages = 0
    unchanged_packages = 0
    failed_updates = []

    for pkg in packages:
        pkg_id = str((pkg or {}).get('id', '')).strip()
        if not pkg_id:
            continue

        patch, stats = _migrate_package_media_to_cloud(pkg)
        for key, value in stats.items():
            aggregate[key] = aggregate.get(key, 0) + int(value)

        if not patch:
            unchanged_packages += 1
            continue

        if db_update_package(pkg_id, patch):
            updated_packages += 1
        else:
            failed_updates.append(pkg_id)

    return jsonify({
        'success': True,
        'agency_id': agency_id,
        'total_packages': len(packages),
        'updated_packages': updated_packages,
        'unchanged_packages': unchanged_packages,
        'failed_updates': failed_updates,
        'url_stats': aggregate,
        'note': 'Run once after enabling Firebase Storage to convert old /uploads paths to durable cloud URLs.',
    })

@app.route('/agency/add', methods=['POST'])
def agency_add_package():
    if _normalize_role(session.get('role')) != 'agency':
        flash('Please login as an agency.', 'error')
        return redirect(url_for('login'))
    
    title = request.form.get('title', '').strip()
    duration = request.form.get('duration', '').strip()
    price = request.form.get('price', '0').strip()
    old_price = request.form.get('old_price', '0').strip()
    tag = request.form.get('tag', 'Adventure').strip()
    transport_type = request.form.get('transport_type', 'mixed').strip().lower()
    image_url = _normalize_media_url(request.form.get('image_url', '').strip())
    
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
    gallery_files_all = request.files.getlist('gallery_files')
    gallery_files = [f for f in gallery_files_all if f and f.filename]
    valid_gallery_files = [f for f in gallery_files if allowed_file(f.filename, ALLOWED_IMG_EXT)]
    if gallery_files and not valid_gallery_files:
        flash('Invalid gallery file type. Allowed: png, jpg, jpeg, gif, webp.', 'error')
        return redirect(url_for('agency_dashboard'))

    gallery_urls = save_uploaded_files(valid_gallery_files, ALLOWED_IMG_EXT)
    if valid_gallery_files and len(gallery_urls) < len(valid_gallery_files):
        flash('Gallery image upload failed. Please verify Firebase Storage configuration and try again.', 'error')
        return redirect(url_for('agency_dashboard'))
    
    # Handle file uploads for videos
    video_files_all = request.files.getlist('video_files')
    video_files = [f for f in video_files_all if f and f.filename]
    valid_video_files = [f for f in video_files if allowed_file(f.filename, ALLOWED_VID_EXT)]
    if video_files and not valid_video_files:
        flash('Invalid video file type. Allowed: mp4, webm, mov.', 'error')
        return redirect(url_for('agency_dashboard'))

    video_urls = save_uploaded_files(valid_video_files, ALLOWED_VID_EXT)
    if valid_video_files and len(video_urls) < len(valid_video_files):
        flash('Video upload failed. Please verify Firebase Storage configuration and try again.', 'error')
        return redirect(url_for('agency_dashboard'))
    
    # Also accept URL inputs as fallback
    gallery_raw = request.form.get('gallery_urls', '').strip()
    video_raw = request.form.get('video_urls', '').strip()
    if gallery_raw:
        gallery_urls += [u.strip() for u in gallery_raw.splitlines() if u.strip()]
    gallery_urls = _normalize_media_list(gallery_urls)
    if video_raw:
        video_urls += [u.strip() for u in video_raw.splitlines() if u.strip()]
    
    features_raw = request.form.get('features', '').strip()
    features_list = [f.strip() for f in features_raw.splitlines() if f.strip()] if features_raw else []
    food_trail_list = _parse_food_trail_form(request.form.get('food_trail', ''))
    
    # Handle main image upload
    main_image_file = request.files.get('main_image_file')
    if main_image_file and main_image_file.filename:
        if not allowed_file(main_image_file.filename, ALLOWED_IMG_EXT):
            flash('Invalid main image type. Allowed: png, jpg, jpeg, gif, webp.', 'error')
            return redirect(url_for('agency_dashboard'))
        saved = save_uploaded_files([main_image_file], ALLOWED_IMG_EXT)
        if not saved:
            flash('Main image upload failed. Please verify Firebase Storage configuration and try again.', 'error')
            return redirect(url_for('agency_dashboard'))
        image_url = saved[0]
    image_url = _normalize_media_url(image_url)
    
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
    
    # Generate a collision-safe package ID (prevents accidental overwrite).
    pkg_id = _generate_unique_package_id(title)
    
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
        'food_trail': food_trail_list,
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
    if _normalize_role(session.get('role')) != 'agency':
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
    if _normalize_role(session.get('role')) != 'agency':
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
    if _normalize_role(session.get('role')) != 'agency':
        flash('Please login as an agency.', 'error')
        return redirect(url_for('login'))
    
    package = db_get_package(id)
    if not package:
        flash('Package not found.', 'error')
        return redirect(url_for('agency_dashboard'))
    
    if package.get('agency_id') != session.get('user_id'):
        flash('You do not have permission to edit this package.', 'error')
        return redirect(url_for('agency_dashboard'))

    before_image = _normalize_media_url(package.get('image', ''))
    before_gallery = _normalize_media_list(package.get('gallery', []))
    
    title = request.form.get('title', '').strip()
    duration = request.form.get('duration', '').strip()
    price = request.form.get('price', '0').strip()
    old_price = request.form.get('old_price', '0').strip()
    tag = request.form.get('tag', 'Adventure').strip()
    transport_type = request.form.get('transport_type', (package.get('transport_type') or 'mixed')).strip().lower()
    image_url = _normalize_media_url(request.form.get('image_url', '').strip())
    
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
    video_files_all = request.files.getlist('video_files')
    video_files = [f for f in video_files_all if f and f.filename]
    valid_video_files = [f for f in video_files if allowed_file(f.filename, ALLOWED_VID_EXT)]
    if video_files and not valid_video_files:
        flash('Invalid video file type. Allowed: mp4, webm, mov.', 'error')
        return redirect(url_for('agency_dashboard'))

    video_urls = save_uploaded_files(valid_video_files, ALLOWED_VID_EXT)
    if valid_video_files and len(video_urls) < len(valid_video_files):
        flash('Video upload failed. Please verify Firebase Storage configuration and try again.', 'error')
        return redirect(url_for('agency_dashboard'))
    
    # Also accept URL inputs for videos
    video_raw = request.form.get('video_urls', '').strip()
    if video_raw:
        video_urls += [u.strip() for u in video_raw.splitlines() if u.strip()]
    
    features_raw = request.form.get('features', '').strip()
    features_list = [f.strip() for f in features_raw.splitlines() if f.strip()] if features_raw else []
    food_trail_raw = request.form.get('food_trail', '')
    food_trail_list = _parse_food_trail_form(food_trail_raw)
    
    # Handle main image upload
    main_image_file = request.files.get('main_image_file')
    if main_image_file and main_image_file.filename:
        if not allowed_file(main_image_file.filename, ALLOWED_IMG_EXT):
            flash('Invalid main image type. Allowed: png, jpg, jpeg, gif, webp.', 'error')
            return redirect(url_for('agency_dashboard'))
        saved = save_uploaded_files([main_image_file], ALLOWED_IMG_EXT)
        if not saved:
            flash('Main image upload failed. Please verify Firebase Storage configuration and try again.', 'error')
            return redirect(url_for('agency_dashboard'))
        image_url = saved[0]
    image_url = _normalize_media_url(image_url)
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
    
    # Preserve gallery safely: only clear/replace when explicit user input is present.
    existing_gallery_raw = request.form.get('existing_gallery_urls', '').strip()
    gallery_raw = request.form.get('gallery_urls', '').strip()
    if existing_gallery_raw:
        existing_gallery = [u.strip() for u in existing_gallery_raw.splitlines() if u.strip()]
    elif gallery_raw:
        existing_gallery = [u.strip() for u in gallery_raw.splitlines() if u.strip()]
    else:
        existing_gallery = package.get('gallery', [])
    existing_gallery = _normalize_media_list(existing_gallery)

    # Merge: existing gallery + newly uploaded files.
    gallery_files_all = request.files.getlist('gallery_files')
    gallery_files = [f for f in gallery_files_all if f and f.filename]
    valid_gallery_files = [f for f in gallery_files if allowed_file(f.filename, ALLOWED_IMG_EXT)]
    if gallery_files and not valid_gallery_files:
        flash('Invalid gallery file type. Allowed: png, jpg, jpeg, gif, webp.', 'error')
        return redirect(url_for('agency_dashboard'))

    new_uploads_only = save_uploaded_files(valid_gallery_files, ALLOWED_IMG_EXT)
    if valid_gallery_files and len(new_uploads_only) < len(valid_gallery_files):
        flash('Gallery image upload failed. Please verify Firebase Storage configuration and try again.', 'error')
        return redirect(url_for('agency_dashboard'))
    final_gallery = _normalize_media_list(existing_gallery + new_uploads_only)
    if not final_gallery:
        # Keep at least one valid image reference.
        fallback_image = _normalize_media_url(update_data.get('image', '') or package.get('image', ''))
        if fallback_image:
            final_gallery = [fallback_image]
    update_data['gallery'] = final_gallery

    _log_package_media_trace('pre_update', id, session.get('user_id'), {
        'before_image': before_image,
        'before_gallery_count': len(before_gallery),
        'before_gallery_preview': _media_preview_list(before_gallery),
        'remove_main_requested': remove_main,
        'incoming_image_url': image_url,
        'existing_gallery_raw_present': bool(existing_gallery_raw),
        'gallery_textarea_present': bool(gallery_raw),
        'uploaded_gallery_count': len(new_uploads_only),
        'uploaded_gallery_preview': _media_preview_list(new_uploads_only),
        'resolved_image': update_data.get('image', before_image),
        'resolved_gallery_count': len(final_gallery),
        'resolved_gallery_preview': _media_preview_list(final_gallery),
    })
    
    if video_urls:
        update_data['videos'] = video_urls
    
    if features_list:
        update_data['features'] = features_list

    # Food trail can be explicitly managed by agency via textarea input.
    if str(food_trail_raw).strip():
        update_data['food_trail'] = food_trail_list
    elif 'food_trail' in package:
        update_data['food_trail'] = []
    
    # Recalculate discount
    if update_data['old_price'] > update_data['price']:
        pct = round((1 - update_data['price'] / update_data['old_price']) * 100)
        update_data['discount'] = f'{pct}% OFF'
    else:
        update_data['discount'] = ''

    update_data['carbon_score'] = _calculate_carbon_score(update_data['duration'], update_data['transport_type'])
    
    if not db_update_package(id, update_data):
        _log_package_media_trace('update_failed', id, session.get('user_id'), {
            'attempted_image': update_data.get('image', before_image),
            'attempted_gallery_count': len(update_data.get('gallery', [])),
            'attempted_gallery_preview': _media_preview_list(update_data.get('gallery', [])),
        })
        flash('Package update failed in Firebase. Please check DB credentials/rules and try again.', 'error')
        return redirect(url_for('agency_dashboard'))

    persisted = db_get_package(id) or {}
    persisted_gallery = _normalize_media_list(persisted.get('gallery', []))
    _log_package_media_trace('post_update', id, session.get('user_id'), {
        'persisted_image': _normalize_media_url(persisted.get('image', '')),
        'persisted_gallery_count': len(persisted_gallery),
        'persisted_gallery_preview': _media_preview_list(persisted_gallery),
    })

    flash(f'Package "{title}" updated successfully!', 'success')
    return redirect(url_for('agency_dashboard'))

# â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•
# TRAVEL BLOG / REVIEWS
# â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•

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
            print(f"âš ï¸  Firebase review read error: {e}")
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
            print(f"âš ï¸  Firebase review write error: {e}")
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
            print(f"âš ï¸  Firebase reviews read error: {e}")
    all_reviews = []
    for pkg_id, reviews in MOCK_DATABASE.get('reviews', {}).items():
        for r in reviews:
            r['package_id'] = pkg_id
            all_reviews.append(r)
    return all_reviews

@app.route('/reviews')
def travel_blog():
    """Travel blog / reviews page â€” shows all reviews as travel stories."""
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

