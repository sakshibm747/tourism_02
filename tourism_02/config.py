import os
from dotenv import load_dotenv

load_dotenv()

class Config:
    SECRET_KEY = os.environ.get('SECRET_KEY') or 'dev-secret-key-for-tourism-app'

    # SMTP email alert settings
    SMTP_HOST = os.environ.get('SMTP_HOST', '')
    SMTP_PORT = int(os.environ.get('SMTP_PORT', '587'))
    SMTP_USER = os.environ.get('SMTP_USER', '')
    SMTP_PASSWORD = os.environ.get('SMTP_PASSWORD', '')
    SMTP_USE_TLS = os.environ.get('SMTP_USE_TLS', 'true').lower() == 'true'
    EMAIL_FROM = os.environ.get('EMAIL_FROM', SMTP_USER)

    # Twilio WhatsApp alert settings
    TWILIO_ACCOUNT_SID = os.environ.get('TWILIO_ACCOUNT_SID', '')
    TWILIO_AUTH_TOKEN = os.environ.get('TWILIO_AUTH_TOKEN', '')
    TWILIO_WHATSAPP_FROM = os.environ.get('TWILIO_WHATSAPP_FROM', '')  # Example: whatsapp:+14155238886

    # Optional fallback recipient for WhatsApp if agency phone is not stored
    DEFAULT_AGENCY_WHATSAPP_TO = os.environ.get('DEFAULT_AGENCY_WHATSAPP_TO', '')  # Example: whatsapp:+9198xxxxxx

    # Frontend polling interval (milliseconds) for in-app bell updates
    NOTIFICATION_POLL_MS = int(os.environ.get('NOTIFICATION_POLL_MS', '12000'))
