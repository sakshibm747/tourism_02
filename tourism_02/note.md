.\run_app.bat
cd c:\Users\saksh\OneDrive\Desktop\tourism_02\tourism_02; C:/Users/saksh/AppData/Local/Programs/Python/Python313/python.exe app.py

Super easy version: use Render (free/easy) + your domain provider (GoDaddy/Namecheap).

1. Put project on GitHub
- Create a new GitHub repo.
- Upload your project.
- Important: your Flask app is inside the inner tourism_02 folder, so remember that.

2. Make sure production server is installed
- In requirements.txt add gunicorn if missing.
- Example line:
  gunicorn==23.0.0

3. Add a Procfile in the project folder (same place as app.py)
Contents:
  web: gunicorn app:app

4. Deploy on Render
- Go to render.com, sign in.
- New + → Web Service → Connect your GitHub repo.
- Set:
  - Root Directory: tourism_02
  - Build Command: pip install -r requirements.txt
  - Start Command: gunicorn app:app
- Click Deploy.

5. Add environment variables in Render
Copy values from your .env into Render Environment section:
- SECRET_KEY
- TWILIO_ACCOUNT_SID
- TWILIO_AUTH_TOKEN
- TWILIO_WHATSAPP_FROM
- DEFAULT_AGENCY_WHATSAPP_TO
- SMTP_HOST
- SMTP_PORT
- SMTP_USER
- SMTP_PASSWORD
- SMTP_USE_TLS
- EMAIL_FROM
- NOTIFICATION_POLL_MS

For Firebase key:
- Easiest: keep serviceAccountKey.json in repo (private repo only).
- Better (later): move key to env secret file.

6. Test your Render URL
- Render gives URL like: yourapp.onrender.com
- Open it and test login, booking, WhatsApp, CSV export.

7. Add your custom domain
- In Render service: Settings → Custom Domains → Add domain
  - add www.yourdomain.com
  - add yourdomain.com
- Render shows DNS records to add.
- Go to your domain provider DNS and paste exactly those records.
- Wait 5 to 30 minutes (sometimes longer).
- SSL/HTTPS is auto-enabled by Render.

If you want, I can give you the exact ready-to-copy Procfile and a deployment checklist you can tick one by one in 5 minutes.