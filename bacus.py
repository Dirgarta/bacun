#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
BACUS BANDUNG - toko online dan back office dalam satu file.

Isi:
  * Toko: katalog per kategori (Beer, Anggur, Wine, Whisky, Vodka, Tradisional,
    Lain-lain), keranjang, kode promo, hitung jarak dari link Google Maps,
    validasi lokasi rumah dari link Maps, free ongkir radius 10 km dengan minimal
    belanja, checkout wajib mengisi data pengantaran + foto rumah, lalu membuka
    WhatsApp toko dengan pesan order terisi.
  * Back office (/admin): pesanan dan statusnya, harga produk, harga promo,
    kode promo dan banner, pengaturan
    toko (WhatsApp, rekening, titik toko, radius, minimal free ongkir).

CARA MENJALANKAN (lokal)
  1. Pasang Python 3.9+ lalu:  pip install -r requirements.txt
     (pillow tidak wajib, tapi disarankan: foto diperkecil dan data lokasi
      GPS di dalam foto dihapus sebelum disimpan)
  2. Jalankan:  python bacus.py
  3. Buka http://localhost:8000  dan  http://localhost:8000/admin
     Atur BACUS_ADMIN_USER dan BACUS_ADMIN_PASSWORD (min. 12 karakter) sebelum
     startup pertama. Password tidak pernah dicetak atau disimpan sebagai teks.

PENGATURAN LEWAT ENVIRONMENT VARIABLE (opsional)
  BACUS_DATA            folder data (database + foto). Default: ./bacus_data
  BACUS_ADMIN_USER      username admin pertama (wajib saat database dibuat)
  BACUS_ADMIN_PASSWORD  password admin pertama, min. 12 karakter (wajib)
  BACUS_ADMIN_RESET=1   sekali pakai: paksa ganti password admin dari variable di atas
  BACUS_ADMIN_WA        nomor WhatsApp tujuan notifikasi admin
  BACUS_SECRET_KEY      kunci sesi, min. 32 karakter (wajib bila BACUS_HTTPS=1)
  BACUS_PHOTO_KEY       kunci enkripsi foto KTP/rumah (opsional, sangat disarankan)
  BACUS_HTTPS=1         wajib diisi saat sudah memakai HTTPS (cookie aman)
  PORT                  port server. Default: 8000

MENJALANKAN DI RAILWAY
  Railway memakai Procfile dan PORT secara otomatis. Pasang persistent volume
  di /data, lalu set BACUS_DATA=/data, BACUS_HTTPS=1, dan BACUS_SECRET_KEY
  sebagai variables/secrets di Railway. Set BACUS_ADMIN_WA=08974109148 untuk
  memilih nomor penerima notifikasi order; variable ini mengesampingkan nomor
  pada menu Pengaturan. Set BACUS_ADMIN_PASSWORD untuk membuat password admin
  pertama yang diketahui; bila tidak diatur, password acak hanya tercetak di logs.
  Website ini menyimpan foto KTP: pastikan HTTPS aktif dan batasi akses log.
  Folder BACUS_DATA berisi database dan foto; buat backup rutin.
  Titik awal toko: -6.902017, 107.652076 (Bacus Bandung, dari link Maps yang diberikan).
  Jarak rumah dihitung garis lurus. Order di luar radius tetap masuk dengan ongkir
  menunggu konfirmasi admin. Pelanggan harus menekan Kirim di WhatsApp; pengiriman
  pesan otomatis memerlukan integrasi WhatsApp Business Cloud API.

MENJALANKAN DI SERVER LAIN (produksi)
  pip install -r requirements.txt
  BACUS_HTTPS=1 gunicorn --workers 1 --bind 0.0.0.0:$PORT bacus:app
  Atur PORT dan gunakan persistent storage untuk BACUS_DATA. Website ini
  menyimpan foto KTP, jadi JANGAN dibuka ke publik tanpa HTTPS.
"""

import base64
import hashlib
import hmac
import io
import json
import math
import os
import re
import secrets
import sqlite3
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta, timezone
from functools import wraps

from flask import (Flask, abort, flash, g, jsonify, redirect, render_template,
                   request, send_file, session, url_for)
from jinja2 import DictLoader
from markupsafe import Markup
from werkzeug.middleware.proxy_fix import ProxyFix
from werkzeug.security import check_password_hash, generate_password_hash

try:
    from PIL import Image, ImageOps
    Image.MAX_IMAGE_PIXELS = 30_000_000      # tolak gambar bom dekompresi
except Exception:  # Pillow tidak terpasang: unggah foto ditolak (lihat save_photo)
    Image = None

try:
    from cryptography.fernet import Fernet, InvalidToken
except Exception:
    Fernet = InvalidToken = None

# ---------------------------------------------------------------------------
# Konfigurasi
# ---------------------------------------------------------------------------
BASE = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.environ.get("BACUS_DATA", os.path.join(BASE, "bacus_data"))
UPLOAD_DIR = os.path.join(DATA_DIR, "foto")
DB_PATH = os.path.join(DATA_DIR, "bacus.db")
os.makedirs(UPLOAD_DIR, exist_ok=True)
try:
    os.chmod(DATA_DIR, 0o700)
    os.chmod(UPLOAD_DIR, 0o700)
except OSError:
    pass
HTTPS_MODE = os.environ.get("BACUS_HTTPS") == "1"
ADMIN_IDLE_SECONDS = 4 * 3600                 # admin otomatis keluar setelah 4 jam tidak aktif

MAX_FOTO = 10 * 1024 * 1024          # 10 MB per foto
CATS = [("beer", "Beer"), ("anggur", "Anggur"), ("wine", "Wine"), ("whisky", "Whisky"),
        ("vodka", "Vodka"), ("tradisional", "Tradisional"), ("lain", "Lain-lain")]
CAT_KEYS = [c[0] for c in CATS]
LABELS = ["a", "b", "c", "d", "e"]
ORDER_STATUS = [("baru", "Menunggu transfer"), ("lunas", "Transfer terverifikasi"),
                ("dikirim", "Sedang diantar"), ("selesai", "Selesai"), ("batal", "Batal")]
ORDER_STATUS_D = dict(ORDER_STATUS)

DEFAULT_ADMIN_WA = ""   # isi lewat BACUS_ADMIN_WA atau menu Pengaturan

DEFAULT_SETTINGS = {
    "wa": DEFAULT_ADMIN_WA,
    "store_lat": -6.902017, "store_lng": 107.652076,
    "radius_km": 10, "free_min": 100000,
    "bank_name": "BCA", "bank_no": "000 000 0000", "bank_holder": "Bacus Bandung",
    "ship_per_km": 3000,
    "hours_on": 0, "open_time": "10:00", "close_time": "22:00", "force_closed": 0,
    "banner": "",
}

SEED_PRODUCTS = [
    # nama, kemasan, abv, jenis, kategori, harga, harga promo, label
    ("Lager Botol", "330 ml · botol", 4.7, "Lager", "beer", 35000, 0, "a"),
    ("Lager Kaleng", "500 ml · kaleng", 4.7, "Lager", "beer", 42000, 0, "a"),
    ("Pilsner Besar", "620 ml · botol", 5.0, "Pilsner", "beer", 58000, 0, "c"),
    ("Radler Lemon", "330 ml · kaleng", 2.0, "Radler", "beer", 30000, 0, "e"),
    ("Wheat Beer", "330 ml · botol", 5.2, "Hefeweizen", "beer", 65000, 0, "b"),
    ("Pale Ale", "330 ml · kaleng", 5.0, "Pale Ale", "beer", 68000, 0, "c"),
    ("IPA", "330 ml · kaleng", 6.2, "India Pale Ale", "beer", 75000, 0, "b"),
    ("Stout", "330 ml · botol", 4.9, "Stout", "beer", 48000, 0, "d"),
    ("Paket 6 Lager", "6 × 330 ml kaleng", 4.7, "Paket hemat", "beer", 190000, 175000, "a"),
    ("Paket Craft Mix", "4 × 330 ml campur", 5.5, "Paket craft", "beer", 260000, 0, "d"),
    ("Anggur Merah", "620 ml · botol", 14.7, "Anggur merah", "anggur", 85000, 0, "e"),
    ("Anggur Kolesom", "620 ml · botol", 19.7, "Anggur kolesom", "anggur", 90000, 0, "b"),
    ("Red Wine Cabernet", "750 ml · botol", 13.5, "Red wine", "wine", 280000, 0, "e"),
    ("White Wine Sauvignon", "750 ml · botol", 12.5, "White wine", "wine", 270000, 0, "c"),
    ("Blended Whisky", "700 ml · botol", 40, "Blended", "whisky", 420000, 0, "b"),
    ("Bourbon", "700 ml · botol", 40, "Bourbon", "whisky", 480000, 0, "a"),
    ("Vodka Original", "700 ml · botol", 40, "Vodka", "vodka", 350000, 0, "d"),
    ("Arak Bali", "600 ml · botol", 35, "Arak", "tradisional", 150000, 0, "c"),
    ("Brem Bali", "330 ml · botol", 5, "Brem", "tradisional", 60000, 0, "e"),
    ("Soju Original", "360 ml · botol", 16.5, "Soju", "lain", 95000, 0, "d"),
    ("Dry Gin", "700 ml · botol", 40, "Gin", "lain", 390000, 0, "c"),
]

SCHEMA = """
CREATE TABLE IF NOT EXISTS settings(k TEXT PRIMARY KEY, v TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS admins(
  id INTEGER PRIMARY KEY, username TEXT UNIQUE NOT NULL, pw_hash TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS products(
  id INTEGER PRIMARY KEY, name TEXT NOT NULL, volume TEXT DEFAULT '', abv REAL DEFAULT 0,
  style TEXT DEFAULT '', cat TEXT DEFAULT 'beer', price INTEGER NOT NULL,
  promo_price INTEGER DEFAULT 0, label TEXT DEFAULT 'a', image_file TEXT DEFAULT '',
  active INTEGER DEFAULT 1,
  sort INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS promos(
  id INTEGER PRIMARY KEY, code TEXT UNIQUE NOT NULL, kind TEXT DEFAULT 'rp',
  value INTEGER NOT NULL, min_order INTEGER DEFAULT 0, active INTEGER DEFAULT 1);
CREATE TABLE IF NOT EXISTS members(
  id INTEGER PRIMARY KEY, member_no TEXT UNIQUE, name TEXT NOT NULL, wa TEXT UNIQUE NOT NULL,
  pin_hash TEXT NOT NULL, address TEXT, landmark TEXT, map_url TEXT,
  ktp_file TEXT, house_file TEXT, status TEXT DEFAULT 'pending', note TEXT DEFAULT '',
  created_at TEXT, approved_at TEXT);
CREATE TABLE IF NOT EXISTS orders(
  id INTEGER PRIMARY KEY, order_no TEXT UNIQUE NOT NULL, token TEXT NOT NULL,
  created_at TEXT, member_id INTEGER, name TEXT, wa TEXT, address TEXT, landmark TEXT,
  map_url TEXT, distance_km REAL, map_status TEXT DEFAULT 'unknown',
  delivery_radius_km REAL DEFAULT 10, house_file TEXT, items_json TEXT, subtotal INTEGER,
  member_disc INTEGER, promo_code TEXT, promo_disc INTEGER, free_ship INTEGER,
  total INTEGER, status TEXT DEFAULT 'baru', note TEXT DEFAULT '');
"""

# ---------------------------------------------------------------------------
# Aplikasi
# ---------------------------------------------------------------------------
app = Flask(__name__)
# Railway berada di belakang proxy: ambil IP asli dan skema https dari header proxy (1 lapis saja)
app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=0)


def _secret_key():
    env = os.environ.get("BACUS_SECRET_KEY")
    if env:
        if len(env) < 32:
            raise RuntimeError("BACUS_SECRET_KEY minimal 32 karakter. Buat dengan: "
                               "python -c \"import secrets;print(secrets.token_hex(32))\"")
        return env
    if HTTPS_MODE:
        raise RuntimeError("Atur BACUS_SECRET_KEY di Variables sebelum menjalankan mode produksi (BACUS_HTTPS=1).")
    path = os.path.join(DATA_DIR, ".secret_key")
    if not os.path.exists(path):
        with open(path, "w") as f:
            f.write(secrets.token_hex(32))
        os.chmod(path, 0o600)
    with open(path) as f:
        return f.read().strip()


app.config.update(
    SECRET_KEY=_secret_key(),
    MAX_CONTENT_LENGTH=25 * 1024 * 1024,
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=HTTPS_MODE,
    SESSION_COOKIE_NAME="__Host-bacus" if HTTPS_MODE else "bacus",
    PERMANENT_SESSION_LIFETIME=timedelta(days=14),
    MAX_FORM_PARTS=200,
    JSON_SORT_KEYS=False,
)


def db():
    if "db" not in g:
        g.db = sqlite3.connect(DB_PATH, timeout=15)
        g.db.row_factory = sqlite3.Row
        g.db.execute("PRAGMA foreign_keys=ON")
    return g.db


@app.teardown_appcontext
def _close_db(_exc):
    conn = g.pop("db", None)
    if conn is not None:
        conn.close()


try:
    from zoneinfo import ZoneInfo
    LOCAL_TZ = ZoneInfo(os.environ.get("BACUS_TZ", "Asia/Jakarta"))
except Exception:                      # tzdata tidak ada: pakai WIB tetap (UTC+7)
    LOCAL_TZ = timezone(timedelta(hours=7))


def local_now():
    return datetime.now(LOCAL_TZ)


def now_str():
    return local_now().strftime("%Y-%m-%d %H:%M")


TIME_RE = re.compile(r"([01][0-9]|2[0-3]):[0-5][0-9]")


def store_status():
    """(buka?, pesan). Dihitung dari pengaturan jam buka/tutup dan tombol tutup manual."""
    s = S()
    if int(s.get("force_closed") or 0):
        return False, "Toko sedang tutup. Kamu masih bisa melihat katalog, tapi pesanan belum bisa dikirim."
    if not int(s.get("hours_on") or 0):
        return True, ""
    o, c = str(s.get("open_time", "10:00")), str(s.get("close_time", "22:00"))
    if not (TIME_RE.fullmatch(o) and TIME_RE.fullmatch(c)) or o == c:
        return True, ""
    now = local_now().strftime("%H:%M")
    is_open = (o <= now < c) if o < c else (now >= o or now < c)
    if is_open:
        return True, ""
    return False, "Toko tutup. Jam buka %s - %s WIB. Kamu masih bisa melihat katalog, tapi pesanan belum bisa dikirim." % (o, c)


def init_db():
    conn = sqlite3.connect(DB_PATH, timeout=15)
    conn.execute("PRAGMA journal_mode=WAL")
    conn.executescript(SCHEMA)
    product_columns = {row[1] for row in conn.execute("PRAGMA table_info(products)")}
    if "image_file" not in product_columns:
        conn.execute("ALTER TABLE products ADD COLUMN image_file TEXT DEFAULT ''")
    order_columns = {row[1] for row in conn.execute("PRAGMA table_info(orders)")}
    if "map_status" not in order_columns:
        conn.execute("ALTER TABLE orders ADD COLUMN map_status TEXT DEFAULT 'unknown'")
    for col in ("ship_fee", "ship_km"):
        if col not in order_columns:
            conn.execute("ALTER TABLE orders ADD COLUMN %s INTEGER DEFAULT 0" % col)
    if "delivery_radius_km" not in order_columns:
        conn.execute("ALTER TABLE orders ADD COLUMN delivery_radius_km REAL DEFAULT 10")
    for k, v in DEFAULT_SETTINGS.items():
        conn.execute("INSERT OR IGNORE INTO settings(k, v) VALUES(?, ?)", (k, json.dumps(v)))
    env_admin_wa = os.environ.get("BACUS_ADMIN_WA")
    if env_admin_wa:
        normalized_admin_wa = norm_wa(env_admin_wa)
        if not re.fullmatch(r"62[0-9]{9,13}", normalized_admin_wa):
            conn.close()
            raise ValueError("BACUS_ADMIN_WA tidak valid. Periksa format nomor WhatsApp.")
    if conn.execute("SELECT COUNT(*) FROM products").fetchone()[0] == 0:
        for i, p in enumerate(SEED_PRODUCTS):
            conn.execute("INSERT INTO products(name, volume, abv, style, cat, price, promo_price, label, sort)"
                         " VALUES(?,?,?,?,?,?,?,?,?)", (*p, i))
        conn.execute("INSERT OR IGNORE INTO promos(code, kind, value, min_order, active)"
                     " VALUES('HALOBACUS', 'rp', 15000, 150000, 0)")
    created = None
    env_user = os.environ.get("BACUS_ADMIN_USER", "").strip()
    env_pw = os.environ.get("BACUS_ADMIN_PASSWORD", "")
    n_admin = conn.execute("SELECT COUNT(*) FROM admins").fetchone()[0]
    reset = os.environ.get("BACUS_ADMIN_RESET") == "1"
    if n_admin == 0 or reset:
        if not re.fullmatch(r"[A-Za-z0-9_.-]{3,30}", env_user) or len(env_pw) < 12:
            conn.close()
            raise ValueError("Atur BACUS_ADMIN_USER (3-30 huruf/angka) dan BACUS_ADMIN_PASSWORD "
                             "(minimal 12 karakter) di environment.")
        pw_hash = generate_password_hash(env_pw)
        if conn.execute("SELECT 1 FROM admins WHERE username=?", (env_user,)).fetchone():
            conn.execute("UPDATE admins SET pw_hash=? WHERE username=?", (pw_hash, env_user))
        else:
            conn.execute("INSERT INTO admins(username, pw_hash) VALUES(?, ?)", (env_user, pw_hash))
        created = "reset" if reset and n_admin else "baru"
    conn.commit()
    conn.close()
    for suffix in ("", "-wal", "-shm"):
        try:
            os.chmod(DB_PATH + suffix, 0o600)
        except OSError:
            pass
    return created


def S():
    """Pengaturan toko (dibaca sekali per request)."""
    if "settings" not in g:
        g.settings = dict(DEFAULT_SETTINGS)
        for r in db().execute("SELECT k, v FROM settings"):
            g.settings[r["k"]] = json.loads(r["v"])
    return g.settings


def save_setting(k, v):
    db().execute("INSERT INTO settings(k, v) VALUES(?, ?) ON CONFLICT(k) DO UPDATE SET v=excluded.v",
                 (k, json.dumps(v)))


# ---------------------------------------------------------------------------
# Bantuan umum
# ---------------------------------------------------------------------------
def rp(n):
    return "Rp " + f"{int(round(n or 0)):,}".replace(",", ".")


def norm_wa(s):
    d = re.sub(r"[^0-9]", "", str(s or ""))
    if d.startswith("0"):
        d = "62" + d[1:]
    elif d.startswith("8"):
        d = "62" + d
    return d


def wa_link(number, text):
    return "https://wa.me/" + norm_wa(number) + "?text=" + urllib.parse.quote(text)


def admin_whatsapp():
    """Nomor tujuan notifikasi admin, dengan environment sebagai override Railway."""
    return norm_wa(os.environ.get("BACUS_ADMIN_WA") or S()["wa"])


app.jinja_env.globals["admin_whatsapp"] = admin_whatsapp


def to_int(v, default=0):
    try:
        return int(float(str(v).replace(".", "").replace(",", ".")))
    except (TypeError, ValueError):
        return default


def to_float(v, default=0.0):
    try:
        return float(str(v).replace(",", "."))
    except (TypeError, ValueError):
        return default


def _num(v):
    """5.0 -> 5 supaya tampil rapi; 2.5 tetap 2.5."""
    return int(v) if float(v).is_integer() else v


def eff_price(p):
    return p["promo_price"] if 0 < (p["promo_price"] or 0) < p["price"] else p["price"]


app.jinja_env.filters["rp"] = rp
app.jinja_env.filters["km"] = lambda v: ("%.1f" % v).replace(".", ",") if v is not None else "—"


def safe_eq(a, b):
    """Perbandingan waktu-konstan yang aman untuk teks non-ASCII (tidak melempar TypeError)."""
    return hmac.compare_digest(str(a or "").encode("utf-8"), str(b or "").encode("utf-8"))


def safe_next(url, default):
    """Hanya izinkan redirect ke path internal (cegah open redirect)."""
    url = url or ""
    if url.startswith("/") and not url.startswith("//") and "\\" not in url and "\n" not in url and "\r" not in url:
        return url
    return default


# --- pembatas laju (in-memory; aplikasi berjalan dengan 1 worker) -----------
_rl = {}
_rl_lock = threading.Lock()


def rate_hit(key, limit, window):
    """Catat 1 percobaan. True bila masih di bawah batas, False bila sudah diblokir."""
    now = time.time()
    with _rl_lock:
        hits = [t for t in _rl.get(key, []) if now - t < window]
        ok = len(hits) < limit
        if ok:
            hits.append(now)
        _rl[key] = hits
        if len(_rl) > 20000:
            for k in [k for k, v in _rl.items() if not v or now - v[-1] > 3600]:
                _rl.pop(k, None)
    return ok


def rate_peek(key, limit, window):
    now = time.time()
    with _rl_lock:
        return len([t for t in _rl.get(key, []) if now - t < window]) >= limit


def rate_fail(key):
    with _rl_lock:
        _rl.setdefault(key, []).append(time.time())


def client_ip():
    return request.remote_addr or "?"


def throttle(name, limit, window):
    """Batasi endpoint per IP. Kembalikan None bila lolos, atau response 429."""
    if not rate_hit("%s:%s" % (name, client_ip()), limit, window):
        return render_template("error.html", code=429, msg="Terlalu banyak permintaan. Coba lagi beberapa menit lagi."), 429
    return None


# --- CSRF ------------------------------------------------------------------
def csrf_token():
    if "_csrf" not in session:
        session["_csrf"] = secrets.token_urlsafe(32)
    return session["_csrf"]


@app.before_request
def _csrf_protect():
    if request.method == "POST":
        sent = request.form.get("_csrf") or request.headers.get("X-CSRF") or ""
        if not session.get("_csrf") or not safe_eq(sent, session.get("_csrf")):
            abort(400, "Sesi kedaluwarsa. Muat ulang halaman lalu coba lagi.")


app.jinja_env.globals.update(
    csrf=lambda: Markup('<input type="hidden" name="_csrf" value="%s">' % csrf_token()),
    csrf_token=csrf_token, CATS=CATS, ORDER_STATUS=ORDER_STATUS, ORDER_STATUS_D=ORDER_STATUS_D,
    LABELS=LABELS)


def get_nonce():
    if "nonce" not in g:
        g.nonce = secrets.token_urlsafe(16)
    return g.nonce


@app.before_request
def _https_and_nonce():
    get_nonce()
    if HTTPS_MODE and not request.is_secure:
        return redirect(request.url.replace("http://", "https://", 1), code=308)


app.jinja_env.globals["nonce"] = get_nonce


@app.after_request
def _security_headers(resp):
    h = resp.headers
    n = get_nonce()
    h["X-Content-Type-Options"] = "nosniff"
    h["X-Frame-Options"] = "DENY"
    h["Referrer-Policy"] = "same-origin"
    h["Permissions-Policy"] = "geolocation=(), camera=(), microphone=(), payment=(), usb=()"
    h["Cross-Origin-Opener-Policy"] = "same-origin"
    h["Cross-Origin-Resource-Policy"] = "same-origin"
    h["Content-Security-Policy"] = (
        "default-src 'none'; base-uri 'none'; object-src 'none'; frame-ancestors 'none'; "
        "form-action 'self'; connect-src 'self'; img-src 'self' data:; "
        "script-src 'nonce-%s'; style-src 'nonce-%s' https://fonts.googleapis.com; "
        "style-src-attr 'unsafe-inline'; font-src https://fonts.gstatic.com" % (n, n))
    if HTTPS_MODE:
        h["Strict-Transport-Security"] = "max-age=31536000; includeSubDomains"
    if request.path.startswith(("/admin", "/pesanan", "/api")):
        h["X-Robots-Tag"] = "noindex, nofollow, noarchive"
    if "Cache-Control" not in h:
        h["Cache-Control"] = "private, no-store"
    h.pop("Server", None)
    return resp


@app.route("/robots.txt")
def robots():
    return ("User-agent: *\nDisallow: /admin\nDisallow: /pesanan\nDisallow: /api\n",
            200, {"Content-Type": "text/plain; charset=utf-8", "Cache-Control": "public, max-age=3600"})


DUMMY_HASH = generate_password_hash(secrets.token_hex(8))


# --- sesi admin ---------------------------------------------------
@app.before_request
def _load_users():
    g.admin = None
    if session.get("admin_id"):
        row = db().execute("SELECT id, username, pw_hash FROM admins WHERE id=?", (session["admin_id"],)).fetchone()
        fresh = time.time() - float(session.get("admin_ts", 0)) < ADMIN_IDLE_SECONDS
        if row and fresh and safe_eq(session.get("av"), pw_stamp(row["pw_hash"])):
            g.admin = row
            session["admin_ts"] = time.time()
        else:   # sesi kedaluwarsa, akun dihapus, atau password sudah diganti
            for k in ("admin_id", "admin_ts", "av"):
                session.pop(k, None)


def pw_stamp(pw_hash):
    """Sidik satu-arah dari hash password: sesi lama otomatis tidak sah setelah password diganti."""
    return hmac.new(app.config["SECRET_KEY"].encode(), pw_hash.encode(), hashlib.sha256).hexdigest()[:24]


def admin_required(fn):
    @wraps(fn)
    def wrapper(*a, **kw):
        if not g.admin:
            # halaman admin tidak "ketahuan" ada bagi orang yang belum login
            abort(404)
        return fn(*a, **kw)
    return wrapper


@app.context_processor
def _ctx():
    is_open, closed_msg = store_status()
    return {"S": S(), "me_admin": g.get("admin"), "store_open": is_open, "store_msg": closed_msg}


# --- foto ----------------------------------------------------------------
_fernet = None
if Fernet and os.environ.get("BACUS_PHOTO_KEY"):
    try:
        _fernet = Fernet(os.environ["BACUS_PHOTO_KEY"].encode())
    except Exception:
        raise RuntimeError("BACUS_PHOTO_KEY tidak valid. Buat dengan: python -c "
                           "\"from cryptography.fernet import Fernet;print(Fernet.generate_key().decode())\"")
elif HTTPS_MODE:
    print("PERINGATAN: BACUS_PHOTO_KEY belum diatur. Foto KTP/rumah tersimpan tanpa enkripsi.", flush=True)


def read_private_photo(path):
    with open(path, "rb") as f:
        raw = f.read()
    if _fernet:
        try:
            return _fernet.decrypt(raw)
        except InvalidToken:
            pass          # file lama yang belum terenkripsi
    return raw


def save_photo(fs, prefix):
    """Simpan foto unggahan di folder privat. Kembalikan (nama_file, pesan_error)."""
    if not fs or not fs.filename:
        return None, "missing"
    data = fs.read(MAX_FOTO + 1)
    if len(data) > MAX_FOTO:
        return None, "Foto terlalu besar. Maksimal 10 MB."
    if data[:3] == b"\xff\xd8\xff":
        ext = "jpg"
    elif data[:8] == b"\x89PNG\r\n\x1a\n":
        ext = "png"
    elif data[:4] == b"RIFF" and data[8:12] == b"WEBP":
        ext = "webp"
    else:
        return None, "Format foto tidak didukung. Gunakan foto JPG, PNG, atau WEBP."
    if Image is None:
        return None, "Server belum siap menerima foto (Pillow belum terpasang)."
    if True:
        try:
            img = Image.open(io.BytesIO(data))
            img = ImageOps.exif_transpose(img)
            img.thumbnail((2000, 2000))
            if img.mode not in ("RGB", "L"):
                img = img.convert("RGB")
            out = io.BytesIO()
            img.save(out, "JPEG", quality=85)   # menyimpan ulang = data GPS/EXIF terhapus
            data, ext = out.getvalue(), "jpg"
        except Exception:
            return None, "Foto tidak bisa dibaca. Coba foto lain."
    name = "%s_%s.%s" % (prefix, secrets.token_hex(16), ext)
    path = os.path.join(UPLOAD_DIR, name)
    if _fernet and prefix in ("ktp", "rumah"):
        data = _fernet.encrypt(data)
    with open(path, "wb") as f:
        f.write(data)
    os.chmod(path, 0o600)
    return name, None


def delete_photo(name):
    if name and re.fullmatch(r"[a-z]+_[0-9a-f]{32}\.(jpg|png|webp)", name):
        try:
            os.remove(os.path.join(UPLOAD_DIR, name))
        except FileNotFoundError:
            pass


# --- lokasi dan jarak -------------------------------------------------------
COORD_PATTERNS = [
    r"!3d(-?[0-9]+\.[0-9]+)!4d(-?[0-9]+\.[0-9]+)",
    r"[?&](?:q|query|ll|destination|daddr|center)=(?:loc:)?(-?[0-9]+\.[0-9]+)(?:,|%2C)\s*\+?(-?[0-9]+\.[0-9]+)",
    r"@(-?[0-9]+\.[0-9]+),(-?[0-9]+\.[0-9]+)",
    r"/(?:place|search|dir)/(-?[0-9]+\.[0-9]+),\+?(-?[0-9]+\.[0-9]+)",
]
MAP_HOST_RE = re.compile(r"^(maps\.app\.goo\.gl|goo\.gl|g\.co|(www\.|maps\.)?google\.[a-z.]+)$", re.I)
_geo_cache = {}


def coords_from(text):
    for pat in COORD_PATTERNS:
        m = re.search(pat, text or "")
        if m:
            lat, lng = float(m.group(1)), float(m.group(2))
            if -90 <= lat <= 90 and -180 <= lng <= 180:
                return lat, lng
    return None


def is_map_link(url):
    try:
        u = urllib.parse.urlparse(url.strip())
    except ValueError:
        return False
    host = (u.hostname or "").lower()
    if u.scheme not in ("http", "https") or not MAP_HOST_RE.match(host):
        return False
    if host.startswith(("www.google.", "google.")) and not u.path.startswith("/maps"):
        return False
    return True


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None


_opener = urllib.request.build_opener(_NoRedirect)


def resolve_map(url):
    """Ambil koordinat dari link Google Maps, termasuk link pendek maps.app.goo.gl."""
    url = (url or "").strip()
    if url in _geo_cache:
        return _geo_cache[url]
    found = coords_from(url)
    current = url
    hops = 0
    while not found and hops < 4 and is_map_link(current):
        hops += 1
        try:
            req = urllib.request.Request(current, headers={"User-Agent": "Mozilla/5.0"})
            resp = _opener.open(req, timeout=6)
            body = resp.read(300000).decode("utf-8", "ignore")
            found = coords_from(resp.geturl()) or coords_from(body)
            break
        except urllib.error.HTTPError as e:
            loc = e.headers.get("Location")
            if not loc:
                break
            current = urllib.parse.urljoin(current, loc)
            found = coords_from(current)
        except Exception:
            break
    if len(_geo_cache) > 500:
        _geo_cache.clear()
    _geo_cache[url] = found
    return found


def haversine(a, b):
    r = 6371.0
    la1, lo1, la2, lo2 = map(math.radians, (a[0], a[1], b[0], b[1]))
    h = math.sin((la2 - la1) / 2) ** 2 + math.cos(la1) * math.cos(la2) * math.sin((lo2 - lo1) / 2) ** 2
    return 2 * r * math.asin(math.sqrt(h))


def locate(map_url):
    """Kembalikan (status, jarak_km). Status: none, invalid, unknown, in, out."""
    s = S()
    if not map_url:
        return "none", None
    if not is_map_link(map_url):
        return "invalid", None
    c = resolve_map(map_url)
    if not c:
        return "unknown", None
    d = haversine((float(s["store_lat"]), float(s["store_lng"])), c)
    return ("in" if d <= float(s["radius_km"]) else "out"), d


# --- perhitungan harga (satu sumber kebenaran) ------------------------------
def compute(items, code, map_url):
    s = S()
    prods = {r["id"]: r for r in db().execute("SELECT * FROM products WHERE active=1")}
    lines, sub, count = [], 0, 0
    for pid, qty in (items or {}).items():
        p = prods.get(to_int(pid, -1))
        qty = max(0, min(99, to_int(qty)))
        if not p or not qty:
            continue
        price = eff_price(p)
        lines.append({"id": p["id"], "name": p["name"], "volume": p["volume"], "qty": qty,
                      "price": price, "total": price * qty})
        sub += price * qty
        count += qty
    code = re.sub(r"\s+", "", (code or "")).upper()
    c_disc, code_msg, promo = 0, "", None
    if code:
        promo = db().execute("SELECT * FROM promos WHERE code=? AND active=1", (code,)).fetchone()
        if not promo:
            code_msg = "Kode promo tidak ditemukan atau sudah tidak berlaku."
        elif sub < (promo["min_order"] or 0):
            code_msg = "Kode %s berlaku untuk belanja minimal %s." % (code, rp(promo["min_order"]))
        else:
            c_disc = round(sub * promo["value"] / 100) if promo["kind"] == "pct" else min(promo["value"], sub)
            code_msg = "Kode %s terpasang." % code
    status, dist = locate(map_url)
    free_min = int(s["free_min"] or 0)
    free = status == "in" and sub >= free_min
    short = free_min - sub if status == "in" and not free else 0
    # ongkir otomatis di luar radius: selisih jarak dibulatkan ke atas per km x tarif per km
    rate = max(0, to_int(s.get("ship_per_km"), 3000))
    ship_km, ship_fee = 0, 0
    if status == "out" and dist is not None:
        ship_km = max(1, math.ceil(round(dist - float(s["radius_km"]), 6)))
        ship_fee = ship_km * rate
    km_txt = ("%.1f" % dist).replace(".", ",") if dist is not None else ""
    map_msg = {
        "none": "",
        "invalid": "Ini bukan link Google Maps. Tempel link dari tombol Bagikan di Google Maps.",
        "unknown": "Titik rumah belum terbaca. Bagikan pin lokasi rumah dari Google Maps, lalu coba lagi.",
        "in": "Sekitar %s km dari toko, masuk radius free ongkir%s." % (
            km_txt, (" untuk belanja minimal " + rp(free_min)) if free_min else ""),
        "out": "Sekitar %s km dari toko, %s km di luar radius free ongkir %s km. Ongkir %s (%s km x %s)." % (
            km_txt, ship_km, _num(float(s["radius_km"])), rp(ship_fee), ship_km, rp(rate)),
    }[status]
    return {
        "lines": lines, "count": count, "sub": sub,
        "promo_code": code if c_disc else "", "promo_disc": c_disc, "code_msg": code_msg,
        "code_ok": bool(c_disc), "map_status": status, "map_msg": map_msg, "dist": dist,
        "free": free, "short": short, "total": max(0, sub - c_disc),
        "ship_fee": ship_fee, "ship_km": ship_km, "ship_rate": rate,
        "grand": max(0, sub - c_disc) + ship_fee,
    }


def ship_text(c):
    radius = c.get("radius_km", S()["radius_km"])
    km_txt = ("%.1f" % c["dist"]).replace(".", ",") if c.get("dist") is not None else ""
    if c["free"]:
        return "GRATIS (sekitar %s km)" % km_txt
    if c.get("ship_fee"):
        return "%s (%s km di luar radius %s km x %s)" % (
            rp(c["ship_fee"]), c["ship_km"], _num(float(radius)), rp(c["ship_fee"] // max(1, c["ship_km"])))
    if c["map_status"] == "in":
        return "dicek admin (sekitar %s km, belanja di bawah minimal free ongkir %s)" % (km_txt, rp(S()["free_min"]))
    if c["map_status"] == "out":
        return "dicek admin (sekitar %s km, di luar radius %s km)" % (km_txt, _num(float(radius)))
    return "dicek admin (jarak belum terhitung)"


# ---------------------------------------------------------------------------
# Halaman toko
# ---------------------------------------------------------------------------
@app.route("/")
def shop():
    prods = db().execute("SELECT * FROM products WHERE active=1 ORDER BY sort, id").fetchall()
    data = {str(p["id"]): {"n": p["name"], "p": eff_price(p)} for p in prods}
    return render_template("shop.html", products=prods, pdata=data, eff_price=eff_price)


@app.route("/api/hitung", methods=["POST"])
def api_hitung():
    limited = throttle("hitung", 90, 60)
    if limited:
        return jsonify({"error": "terlalu banyak permintaan"}), 429
    body = request.get_json(silent=True) or {}
    c = compute(body.get("items") or {}, body.get("kode"), body.get("peta"))
    c["sub_t"], c["total_t"], c["grand_t"] = rp(c["sub"]), rp(c["total"]), rp(c["grand"])
    c["promo_disc_t"], c["short_t"], c["ship_fee_t"] = rp(c["promo_disc"]), rp(c["short"]), rp(c["ship_fee"])
    c["ship_rate_t"] = rp(c["ship_rate"])
    c["dist"] = round(c["dist"], 2) if c["dist"] is not None else None
    return jsonify(c)


@app.route("/checkout", methods=["POST"])
def checkout():
    limited = throttle("checkout", 12, 600)
    if limited:
        return limited
    is_open, closed_msg = store_status()
    if not is_open:
        flash(closed_msg, "bad")
        return redirect(url_for("shop"))
    f = request.form
    try:
        items = json.loads(f.get("items") or "{}")
    except ValueError:
        items = {}
    c = compute(items, f.get("kode"), f.get("peta", "").strip())
    errors = []
    name, wa = f.get("nama", "").strip(), f.get("wa", "").strip()
    address, landmark, map_url = f.get("alamat", "").strip(), f.get("patokan", "").strip(), f.get("peta", "").strip()
    if not c["count"]:
        errors.append("Keranjang masih kosong.")
    if len(name) < 2:
        errors.append("Isi nama penerima.")
    if len(norm_wa(wa)) < 10:
        errors.append("Isi nomor WhatsApp yang aktif.")
    if len(address) < 15:
        errors.append("Isi alamat lengkap.")
    if len(landmark) < 2:
        errors.append("Isi patokan lokasi rumah.")
    if c["map_status"] in ("none", "invalid"):
        errors.append("Tempel link Google Maps titik rumahmu.")
    elif c["map_status"] == "unknown":
        errors.append("Titik rumah belum bisa dibaca dari link Google Maps. Bagikan pin lokasi rumah yang tepat lalu coba lagi.")
    if f.get("umur") != "1":
        errors.append("Centang pernyataan usia 21 tahun ke atas.")
    if errors:
        for error in errors:
            flash(error, "bad")
        return redirect(url_for("shop") + "#checkout")
    house = None
    house, err = save_photo(request.files.get("foto"), "rumah")
    if err:
        flash("Unggah foto tampak depan rumah." if err == "missing" else err, "bad")
        return redirect(url_for("shop") + "#checkout")
    for _ in range(5):
        order_no = "BCS-%s-%04d" % (local_now().strftime("%y%m%d"), secrets.randbelow(10000))
        if not db().execute("SELECT 1 FROM orders WHERE order_no=?", (order_no,)).fetchone():
            break
    token = secrets.token_urlsafe(16)
    db().execute(
        "INSERT INTO orders(order_no, token, created_at, name, wa, address, landmark, map_url,"
        " distance_km, map_status, delivery_radius_km, house_file, items_json, subtotal, member_disc, promo_code,"
        " promo_disc, free_ship, total, ship_fee, ship_km) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,0,?,?,?,?,?,?)",
        (order_no, token, now_str(), name, wa, address, landmark, map_url,
         c["dist"], c["map_status"], S()["radius_km"], house, json.dumps(c["lines"]), c["sub"],
         c["promo_code"], c["promo_disc"], 1 if c["free"] else 0, c["total"], c["ship_fee"], c["ship_km"]))
    db().commit()
    return redirect(url_for("order_page", order_no=order_no, k=token))


def order_message(o, lines):
    s = S()
    map_status = o["map_status"] or "unknown"
    radius = o["delivery_radius_km"] if o["delivery_radius_km"] is not None else float(s["radius_km"])
    if map_status == "unknown" and o["distance_km"] is not None:
        map_status = "in" if o["distance_km"] <= float(radius) else "out"
    c = {"free": bool(o["free_ship"]), "dist": o["distance_km"], "map_status": map_status,
         "radius_km": radius, "ship_fee": o["ship_fee"] or 0, "ship_km": o["ship_km"] or 0}
    out = ["*PESANAN BARU - BACUS BANDUNG*", "No. order: " + o["order_no"],
           "Waktu: " + o["created_at"], "", "*Pesanan*"]
    if c["dist"] is not None:
        out += ["*Lokasi:* %s km garis lurus dari toko (radius %s km)." % (
            ("%.2f" % c["dist"]).replace(".", ","), _num(float(radius)))]
    if c["map_status"] == "out":
        out.append("*DI LUAR RADIUS* - ongkir sudah dihitung otomatis.")
    elif c["map_status"] == "in":
        out.append("Lokasi masuk radius toko.")
    out += ["• %dx %s (%s) = %s" % (l["qty"], l["name"], l["volume"], rp(l["total"])) for l in lines]
    out.append("Subtotal: " + rp(o["subtotal"]))
    if o["promo_disc"]:
        out.append("Kode promo %s: -%s" % (o["promo_code"], rp(o["promo_disc"])))
    out.append("Ongkir: " + ship_text(c))
    if o["free_ship"]:
        out.append("*Total transfer: %s*" % rp(o["total"]))
    elif c["ship_fee"]:
        out.append("*Total transfer: %s* (barang %s + ongkir %s)" % (
            rp(o["total"] + c["ship_fee"]), rp(o["total"]), rp(c["ship_fee"])))
    else:
        out.append("*Total: %s + ongkir (menunggu konfirmasi admin)*" % rp(o["total"]))
    out += ["", "*Pengantaran*", "Nama: " + o["name"], "WhatsApp: " + o["wa"],
            "Alamat: " + o["address"], "Patokan: " + o["landmark"]]
    out += ["Pin rumah: " + o["map_url"], "Titik toko: https://maps.app.goo.gl/mWTbxSwqTx8SJH3LA", "",
            "*Foto tampak depan rumah:* terlampir di chat ini. Jika belum ada, minta pelanggan mengirim fotonya sebelum pesanan diproses.",
            "Pembayaran: transfer bank. Bukti transfer saya kirim di chat ini.",
            "Saya berusia 21 tahun ke atas."]
    return "\n".join(out)


@app.route("/pesanan/<order_no>")
def order_page(order_no):
    o = db().execute("SELECT * FROM orders WHERE order_no=?", (order_no,)).fetchone()
    if not o or not safe_eq(request.args.get("k", ""), o["token"]):
        abort(404)
    delivery_status = o["map_status"] or "unknown"
    if delivery_status == "unknown" and o["distance_km"] is not None:
        radius = o["delivery_radius_km"]
        if radius is None:
            radius = float(S()["radius_km"])
        delivery_status = "in" if o["distance_km"] <= float(radius) else "out"
    lines = json.loads(o["items_json"] or "[]")
    msg = order_message(o, lines)
    return render_template("order.html", o=o, lines=lines, delivery_status=delivery_status,
                           wa=wa_link(admin_whatsapp(), msg), msg=msg)


@app.route("/pesanan/<order_no>/foto")
def order_photo(order_no):
    """Foto rumah milik pembeli sendiri (dilindungi token pesanan) untuk dikirim ke WhatsApp admin."""
    o = db().execute("SELECT house_file, token FROM orders WHERE order_no=?", (order_no,)).fetchone()
    if not o or not safe_eq(request.args.get("k", ""), o["token"]) or not o["house_file"]:
        abort(404)
    if not re.fullmatch(r"rumah_[0-9a-f]{32}\.(jpg|png|webp)", o["house_file"]):
        abort(404)
    path = os.path.join(UPLOAD_DIR, o["house_file"])
    if not os.path.exists(path):
        abort(404)
    ext = o["house_file"].rsplit(".", 1)[1]
    resp = send_file(io.BytesIO(read_private_photo(path)), mimetype="image/" + ("jpeg" if ext == "jpg" else ext))
    resp.headers["Cache-Control"] = "private, no-store"
    resp.headers["Content-Disposition"] = 'inline; filename="foto-rumah-%s.%s"' % (order_no, ext)
    return resp


# ---------------------------------------------------------------------------
# Back office
# ---------------------------------------------------------------------------
@app.route("/admin/login", methods=["GET", "POST"])
def admin_login():
    if request.method == "POST":
        user, pw = request.form.get("username", "").strip()[:60], request.form.get("password", "")[:256]
        key_a, key_ip = "alogin:%s:%s" % (client_ip(), user.lower()), "alogin-ip:" + client_ip()
        if rate_peek(key_a, 5, 900) or rate_peek(key_ip, 20, 900):
            flash("Terlalu banyak percobaan masuk. Coba lagi dalam 15 menit.", "bad")
            return render_template("admin_login.html"), 429
        a = db().execute("SELECT * FROM admins WHERE username=?", (user,)).fetchone()
        ok = check_password_hash(a["pw_hash"] if a else DUMMY_HASH, pw) and a is not None
        if ok:
            session.clear()
            session["admin_id"] = a["id"]
            session["admin_ts"] = time.time()
            session["av"] = pw_stamp(a["pw_hash"])
            nxt = request.args.get("next", "")
            return redirect(nxt if nxt.startswith("/admin") and safe_next(nxt, "") else url_for("admin_orders"))
        rate_fail(key_a)
        rate_fail(key_ip)
        flash("Username atau password salah.", "bad")
    return render_template("admin_login.html")


@app.route("/admin/logout", methods=["POST"])
def admin_logout():
    session.clear()
    return redirect(url_for("admin_login"))


@app.route("/admin")
def admin_home():
    if not g.admin:
        return redirect(url_for("admin_login"))
    return redirect(url_for("admin_orders"))


@app.route("/admin/foto/<name>")
@admin_required
def admin_photo(name):
    if not re.fullmatch(r"[a-z]+_[0-9a-f]{32}\.(jpg|png|webp)", name):
        abort(404)
    path = os.path.join(UPLOAD_DIR, name)
    if not os.path.exists(path):
        abort(404)
    resp = send_file(io.BytesIO(read_private_photo(path)),
                     mimetype="image/" + ("jpeg" if name.endswith("jpg") else name.rsplit(".", 1)[1]))
    resp.headers["Cache-Control"] = "private, no-store"
    resp.headers["Content-Disposition"] = "inline"
    return resp


@app.route("/produk/foto/<name>")
def product_photo(name):
    if not re.fullmatch(r"produk_[0-9a-f]{32}\.(jpg|png|webp)", name):
        abort(404)
    path = os.path.join(UPLOAD_DIR, name)
    if not os.path.exists(path):
        abort(404)
    resp = send_file(path)
    resp.headers["Cache-Control"] = "public, max-age=86400"
    return resp


# --- pesanan --------------------------------------------------------------
@app.route("/admin/pesanan")
@admin_required
def admin_orders():
    st = request.args.get("status", "baru")
    q = request.args.get("q", "").strip()
    sql, args = "SELECT * FROM orders WHERE 1=1", []
    if st != "semua":
        sql += " AND status=?"
        args.append(st)
    if q:
        sql += " AND (order_no LIKE ? OR name LIKE ? OR wa LIKE ?)"
        args += ["%" + q + "%"] * 3
    rows = db().execute(sql + " ORDER BY id DESC LIMIT 300", args).fetchall()
    counts = {r["status"]: r["n"] for r in db().execute("SELECT status, COUNT(*) n FROM orders GROUP BY status")}
    return render_template("admin_orders.html", rows=rows, st=st, q=q, counts=counts, tab="pesanan")


@app.route("/admin/pesanan/<int:oid>", methods=["GET", "POST"])
@admin_required
def admin_order(oid):
    o = db().execute("SELECT * FROM orders WHERE id=?", (oid,)).fetchone()
    if not o:
        abort(404)
    if request.method == "POST":
        st = request.form.get("status")
        if st in ORDER_STATUS_D:
            db().execute("UPDATE orders SET status=?, note=? WHERE id=?", (st, request.form.get("note", "").strip(), oid))
            db().commit()
            flash("Pesanan %s diperbarui: %s." % (o["order_no"], ORDER_STATUS_D[st]), "ok")
        return redirect(url_for("admin_order", oid=oid))
    delivery_status = o["map_status"] or "unknown"
    if delivery_status == "unknown" and o["distance_km"] is not None:
        radius = o["delivery_radius_km"]
        if radius is None:
            radius = float(S()["radius_km"])
        delivery_status = "in" if o["distance_km"] <= float(radius) else "out"
    lines = json.loads(o["items_json"] or "[]")
    msgs = {
        "lunas": "Halo %s, transfer untuk pesanan %s sudah kami terima. Pesanan segera disiapkan. Terima kasih! - Bacus Bandung" % (o["name"], o["order_no"]),
        "dikirim": "Halo %s, pesanan %s sedang diantar ke alamatmu. Siapkan KTP untuk ditunjukkan ke kurir ya. - Bacus Bandung" % (o["name"], o["order_no"]),
    }
    wa_msgs = {k: wa_link(o["wa"], v) for k, v in msgs.items()}
    return render_template("admin_order.html", o=o, lines=lines, delivery_status=delivery_status,
                           wa_msgs=wa_msgs,
                           wa_chat=wa_link(o["wa"], ""), tab="pesanan")


# --- produk ----------------------------------------------------------------
def product_from_form(f):
    cat = f.get("cat") if f.get("cat") in CAT_KEYS else "lain"
    label = f.get("label") if f.get("label") in LABELS else "a"
    return (f.get("name", "").strip(), f.get("volume", "").strip(), to_float(f.get("abv")),
            f.get("style", "").strip(), cat, to_int(f.get("price")), to_int(f.get("promo_price")),
            label, 1 if f.get("active") else 0, to_int(f.get("sort")))


@app.route("/admin/produk", methods=["GET", "POST"])
@admin_required
def admin_products():
    if request.method == "POST":
        f = request.form
        action, pid = f.get("action"), to_int(f.get("id"), -1)
        if action == "hapus":
            product = db().execute("SELECT image_file FROM products WHERE id=?", (pid,)).fetchone()
            if not product:
                abort(404)
            db().execute("DELETE FROM products WHERE id=?", (pid,))
            db().commit()
            delete_photo(product["image_file"])
            flash("Produk dihapus.", "ok")
        else:
            vals = product_from_form(f)
            if not vals[0] or vals[5] <= 0:
                flash("Produk perlu nama dan harga lebih dari 0.", "bad")
                return redirect(url_for("admin_products", cat=f.get("cat")))
            upload = request.files.get("foto")
            new_image = None
            if upload and upload.filename:
                new_image, error = save_photo(upload, "produk")
                if error:
                    flash(error, "bad")
                    return redirect(url_for("admin_products", cat=f.get("cat")))
            if action == "tambah":
                db().execute("INSERT INTO products(name, volume, abv, style, cat, price, promo_price, label,"
                             " image_file, active, sort) VALUES(?,?,?,?,?,?,?,?,?,?,?)",
                             (*vals[:8], new_image or "", *vals[8:]))
                flash("Produk %s ditambahkan." % vals[0], "ok")
            else:
                product = db().execute("SELECT image_file FROM products WHERE id=?", (pid,)).fetchone()
                if not product:
                    delete_photo(new_image)
                    abort(404)
                old_image = product["image_file"]
                image_file = new_image or ("" if f.get("hapus_foto") else old_image or "")
                db().execute("UPDATE products SET name=?, volume=?, abv=?, style=?, cat=?, price=?, promo_price=?,"
                             " label=?, image_file=?, active=?, sort=? WHERE id=?",
                             (*vals[:8], image_file, *vals[8:], pid))
                flash("Produk %s disimpan." % vals[0], "ok")
            if action == "tambah":
                old_image = None
            db().commit()
            if old_image and (new_image or f.get("hapus_foto")):
                delete_photo(old_image)
        return redirect(url_for("admin_products", cat=request.args.get("cat", "")))
    cat = request.args.get("cat", "")
    sql, args = "SELECT * FROM products", []
    if cat in CAT_KEYS:
        sql += " WHERE cat=?"
        args.append(cat)
    rows = db().execute(sql + " ORDER BY cat, sort, id", args).fetchall()
    return render_template("admin_products.html", rows=rows, cat=cat, tab="produk")


# --- promo ----------------------------------------------------------------
@app.route("/admin/promo", methods=["GET", "POST"])
@admin_required
def admin_promos():
    if request.method == "POST":
        f = request.form
        action = f.get("action")
        if action == "banner":
            save_setting("banner", f.get("banner", "").strip()[:200])
            flash("Banner disimpan.", "ok")
        elif action == "hapus":
            db().execute("DELETE FROM promos WHERE id=?", (to_int(f.get("id"), -1),))
            flash("Kode promo dihapus.", "ok")
        else:
            code = re.sub(r"[^A-Z0-9]", "", f.get("code", "").upper())[:30]
            kind = "pct" if f.get("kind") == "pct" else "rp"
            value, min_order = to_int(f.get("value")), to_int(f.get("min_order"))
            active = 1 if f.get("active") else 0
            if not code or value <= 0 or (kind == "pct" and value > 100):
                flash("Periksa kode dan nilai potongan.", "bad")
                return redirect(url_for("admin_promos"))
            try:
                if action == "tambah":
                    db().execute("INSERT INTO promos(code, kind, value, min_order, active) VALUES(?,?,?,?,?)",
                                 (code, kind, value, min_order, active))
                else:
                    db().execute("UPDATE promos SET code=?, kind=?, value=?, min_order=?, active=? WHERE id=?",
                                 (code, kind, value, min_order, active, to_int(f.get("id"), -1)))
                flash("Kode %s disimpan." % code, "ok")
            except sqlite3.IntegrityError:
                flash("Kode %s sudah ada." % code, "bad")
        db().commit()
        return redirect(url_for("admin_promos"))
    rows = db().execute("SELECT * FROM promos ORDER BY id DESC").fetchall()
    return render_template("admin_promos.html", rows=rows, tab="promo")


# --- pengaturan dan akun ---------------------------------------------------
@app.route("/admin/pengaturan", methods=["GET", "POST"])
@admin_required
def admin_settings():
    if request.method == "POST":
        f = request.form
        wa = norm_wa(f.get("wa"))
        if len(wa) < 10:
            flash("Nomor WhatsApp toko belum benar.", "bad")
            return redirect(url_for("admin_settings"))
        store_lat = to_float(f.get("store_lat"), float("nan"))
        store_lng = to_float(f.get("store_lng"), float("nan"))
        radius_km = to_float(f.get("radius_km"), float("nan"))
        if (not math.isfinite(store_lat) or not -90 <= store_lat <= 90
                or not math.isfinite(store_lng) or not -180 <= store_lng <= 180
                or not math.isfinite(radius_km) or radius_km < 0):
            flash("Koordinat toko atau radius tidak valid. Periksa latitude, longitude, dan radius.", "bad")
            return redirect(url_for("admin_settings"))
        save_setting("wa", wa)
        for k in ("bank_name", "bank_no", "bank_holder"):
            save_setting(k, f.get(k, "").strip())
        save_setting("store_lat", store_lat)
        save_setting("store_lng", store_lng)
        save_setting("radius_km", _num(radius_km))
        save_setting("free_min", max(0, to_int(f.get("free_min"))))
        save_setting("ship_per_km", max(0, to_int(f.get("ship_per_km"))))
        open_t, close_t = f.get("open_time", "").strip(), f.get("close_time", "").strip()
        if not (TIME_RE.fullmatch(open_t) and TIME_RE.fullmatch(close_t)):
            db().rollback()
            flash("Format jam harus HH:MM, misalnya 10:00 dan 22:00.", "bad")
            return redirect(url_for("admin_settings"))
        save_setting("open_time", open_t)
        save_setting("close_time", close_t)
        save_setting("hours_on", 1 if f.get("hours_on") else 0)
        save_setting("force_closed", 1 if f.get("force_closed") else 0)
        db().commit()
        _geo_cache.clear()
        flash("Pengaturan disimpan.", "ok")
        return redirect(url_for("admin_settings"))
    return render_template("admin_settings.html", tab="pengaturan")


@app.route("/admin/akun", methods=["GET", "POST"])
@admin_required
def admin_account():
    if request.method == "POST":
        f = request.form
        if f.get("action") == "password":
            a = db().execute("SELECT * FROM admins WHERE id=?", (g.admin["id"],)).fetchone()
            if not check_password_hash(a["pw_hash"], f.get("old", "")):
                flash("Password lama salah.", "bad")
            elif len(f.get("new", "")) < 12 or f.get("new") != f.get("new2"):
                flash("Password baru minimal 12 karakter dan harus diulang dengan sama.", "bad")
            else:
                new_hash = generate_password_hash(f["new"])
                db().execute("UPDATE admins SET pw_hash=? WHERE id=?", (new_hash, a["id"]))
                db().commit()
                session["av"] = pw_stamp(new_hash)
                flash("Password diganti. Sesi di perangkat lain otomatis keluar.", "ok")
        elif f.get("action") == "tambah":
            user, pw = f.get("username", "").strip(), f.get("password", "")
            if not re.fullmatch(r"[A-Za-z0-9_.-]{3,30}", user) or len(pw) < 12:
                flash("Username 3-30 huruf/angka dan password minimal 12 karakter.", "bad")
            else:
                try:
                    db().execute("INSERT INTO admins(username, pw_hash) VALUES(?, ?)", (user, generate_password_hash(pw)))
                    db().commit()
                    flash("Admin %s ditambahkan." % user, "ok")
                except sqlite3.IntegrityError:
                    flash("Username sudah dipakai.", "bad")
        elif f.get("action") == "hapus":
            aid = to_int(f.get("id"), -1)
            if aid == g.admin["id"]:
                flash("Tidak bisa menghapus akun yang sedang dipakai.", "bad")
            else:
                db().execute("DELETE FROM admins WHERE id=?", (aid,))
                db().commit()
                flash("Admin dihapus.", "ok")
        return redirect(url_for("admin_account"))
    admins = db().execute("SELECT id, username FROM admins ORDER BY id").fetchall()
    return render_template("admin_account.html", admins=admins, tab="akun")


@app.errorhandler(413)
def _too_large(_e):
    flash("Ukuran file terlalu besar. Maksimal 10 MB per foto.", "bad")
    return redirect(request.referrer or url_for("shop"))


@app.errorhandler(400)
@app.errorhandler(404)
@app.errorhandler(405)
def _simple_error(e):
    return render_template("error.html", code=e.code, msg=getattr(e, "description", "")), e.code


@app.errorhandler(Exception)
def _server_error(e):
    from werkzeug.exceptions import HTTPException
    if isinstance(e, HTTPException):
        return e
    app.logger.exception("Kesalahan server")        # detail hanya di log server, tidak ke pengunjung
    return render_template("error.html", code=500, msg="Terjadi kesalahan di server. Coba lagi nanti."), 500


# ---------------------------------------------------------------------------
# Tampilan
# ---------------------------------------------------------------------------
CSS = r"""
:root{
  --bg:#F6F4FB; --surface:#FFFFFF; --ink:#1B1440; --muted:#5E5880; --line:#DDD8EC;
  --lager:#FFD23F; --lager-ink:#1B1440; --accent:#E8381B; --accent-ink:#FFFFFF;
  --wa:#128C4A; --wa-ink:#FFFFFF; --ok:#0F7A43; --warn:#9A5B00; --bad:#C22A12;
  --lab-a:#FFD23F; --lab-b:#FF9A5A; --lab-c:#9FE0C0; --lab-d:#B9B4FF; --lab-e:#F7A8C8; --lab-ink:#1B1440;
  --display:"Bricolage Grotesque","Arial Black",system-ui,sans-serif;
  --body:"Plus Jakarta Sans",system-ui,-apple-system,"Segoe UI",sans-serif;
  --mono:"DM Mono",ui-monospace,Menlo,monospace;
}
@media (prefers-color-scheme: dark){:root{
  --bg:#130E28; --surface:#1F183D; --ink:#F3F0FF; --muted:#ABA4CC; --line:#372E5E;
  --accent:#FF6A4D; --accent-ink:#1B1440; --wa:#2FBF71; --wa-ink:#0B2416;
  --ok:#5BD899; --warn:#FFC35A; --bad:#FF8A73; color-scheme:dark}}
*{box-sizing:border-box}
html{scroll-padding-top:16px}
body{margin:0;background:var(--bg);color:var(--ink);font-family:var(--body);font-size:16px;line-height:1.55}
img{max-width:100%}
[hidden]{display:none!important}
.wrap{max-width:1080px;margin:0 auto;padding-inline:16px;padding-block:16px 120px;display:flex;flex-direction:column;gap:32px}
h1,h2,h3{font-family:var(--display);line-height:1.05;margin:0;text-wrap:balance}
h2{font-size:clamp(1.6rem,4vw,2.2rem);font-weight:800}
h3{font-size:1.25rem;font-weight:800}
p{margin:0}
a{color:inherit}
.mono{font-family:var(--mono);font-variant-numeric:tabular-nums}
:focus-visible{outline:3px solid var(--accent);outline-offset:2px}
.nav{display:flex;justify-content:space-between;align-items:center;gap:12px;flex-wrap:wrap}
.brand{font-family:var(--display);font-weight:800;font-size:1.15rem;text-decoration:none}
.nav nav{display:flex;gap:6px;flex-wrap:wrap;align-items:center}
.nav nav a,.tabs a{font-weight:600;font-size:.92rem;text-decoration:none;border:2px solid var(--ink);border-radius:999px;padding:4px 14px}
.nav nav a.on,.tabs a.on{background:var(--ink);color:var(--bg)}
.age{font-family:var(--mono);font-size:.8rem;border:2px solid var(--ink);border-radius:999px;padding:4px 10px}
.flash{display:flex;flex-direction:column;gap:8px}
.flash p{border-radius:12px;padding:10px 14px;font-weight:600;background:var(--surface);border:2px solid var(--line)}
.flash .ok{border-color:var(--ok);color:var(--ok)} .flash .bad{border-color:var(--bad);color:var(--bad)} .flash .warn{border-color:var(--warn);color:var(--warn)}
.hero{background:var(--lager);color:var(--lager-ink);border-radius:28px;padding:24px;display:flex;flex-direction:column;gap:20px}
.hero h1{font-size:clamp(2.6rem,10vw,5.4rem);font-weight:800;letter-spacing:-.03em}
.hero h1 span{display:inline-block;background:var(--lager-ink);color:var(--lager);padding:0 .18em;border-radius:.16em;transform:rotate(-2deg)}
.hero p{max-width:56ch;font-size:1.05rem;font-weight:500}
.chips{display:flex;flex-wrap:wrap;gap:8px;list-style:none;margin:0;padding:0}
.chips li{background:var(--lager-ink);color:var(--lager);border-radius:999px;padding:6px 14px;font-weight:600;font-size:.9rem}
.banner{background:var(--accent);color:var(--accent-ink);border-radius:14px;padding:10px 16px;font-weight:700}
.banner.closed{background:var(--bad);color:#fff}
.add[disabled],.wa[disabled]{opacity:.45;cursor:not-allowed}
.steps{list-style:none;margin:0;padding:0;display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));gap:12px;counter-reset:s}
.steps li{counter-increment:s;border-top:3px solid var(--ink);padding-top:10px;min-width:0}
.steps li::before{content:counter(s);font-family:var(--display);font-weight:800;font-size:1.8rem;display:block;line-height:1}
.steps b{display:block;margin-top:4px}
.steps span{color:var(--muted);font-size:.92rem}
.sec-head{display:flex;justify-content:space-between;align-items:flex-end;gap:12px;flex-wrap:wrap;margin-bottom:16px}
.note,.hint{color:var(--muted);font-size:.86rem;font-weight:400}
.filters{display:flex;flex-wrap:wrap;gap:8px;margin-bottom:16px}
.pill{font:600 .92rem var(--body);background:transparent;color:var(--ink);border:2px solid var(--ink);border-radius:999px;padding:6px 16px;cursor:pointer;text-decoration:none}
.pill[aria-pressed="true"],.pill.on{background:var(--ink);color:var(--bg)}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(200px,1fr));gap:16px}
.card{background:var(--surface);border:1px solid var(--line);border-radius:20px;overflow:hidden;display:flex;flex-direction:column;min-width:0}
.product-image{display:block;width:100%;height:190px;object-fit:cover;background:var(--surface)}
.product-photo-preview img{display:block;width:160px;height:120px;object-fit:cover;border-radius:12px;border:1px solid var(--line)}
.label{color:var(--lab-ink);padding:14px 16px;display:flex;justify-content:space-between;align-items:flex-end;gap:8px;min-height:104px}
.lab-a{background:var(--lab-a)} .lab-b{background:var(--lab-b)} .lab-c{background:var(--lab-c)} .lab-d{background:var(--lab-d)} .lab-e{background:var(--lab-e)}
.label .abv{font-family:var(--display);font-weight:800;font-size:2.4rem;line-height:.9;letter-spacing:-.03em}
.label .abv small{font-size:.9rem;font-family:var(--mono);font-weight:500;letter-spacing:0}
.label .style{font-family:var(--mono);font-size:.74rem;text-transform:uppercase;letter-spacing:.08em;text-align:right;overflow-wrap:anywhere}
.info{padding:14px 16px 16px;display:flex;flex-direction:column;gap:10px;flex:1}
.info h3{font-size:1.15rem;overflow-wrap:anywhere}
.vol{color:var(--muted);font-size:.85rem}
.buy{display:flex;justify-content:space-between;align-items:center;gap:8px;margin-top:auto;flex-wrap:wrap}
.price{font-weight:500;font-size:1.02rem}
.price s{color:var(--muted);font-size:.82rem;display:block}
.price .promo{color:var(--accent)}
.add,.step button{font:700 .9rem var(--body);cursor:pointer;border:0}
.add{background:var(--ink);color:var(--bg);border-radius:999px;padding:8px 16px}
.step{display:inline-flex;align-items:center;gap:6px;background:var(--lager);color:var(--lager-ink);border-radius:999px;padding:3px}
.step button{width:32px;height:32px;border-radius:50%;background:var(--lager-ink);color:var(--lager);font-size:1.1rem;line-height:1}
.step output{min-width:22px;text-align:center;font-family:var(--mono);font-weight:500}
.two{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1.25fr);gap:20px;align-items:start}
@media (max-width:800px){.two{grid-template-columns:minmax(0,1fr)}}
.panel{background:var(--surface);border:1px solid var(--line);border-radius:20px;padding:20px;display:flex;flex-direction:column;gap:16px;min-width:0}
.lines{list-style:none;margin:0;padding:0;display:flex;flex-direction:column;gap:10px}
.lines li{display:flex;justify-content:space-between;gap:12px;align-items:center}
.lines .nm{min-width:0;overflow-wrap:anywhere}
.empty{color:var(--muted)}
.tot{border-top:1px dashed var(--line);padding-top:12px;display:flex;flex-direction:column;gap:6px}
.tot div{display:flex;justify-content:space-between;gap:12px}
.tot .disc{color:var(--ok)} .tot .grand{font-weight:700;font-size:1.2rem}
.box{background:var(--bg);border-radius:14px;padding:14px;display:flex;flex-direction:column;gap:6px}
.row{display:flex;justify-content:space-between;align-items:center;gap:10px;flex-wrap:wrap}
.box .no{font-size:1.15rem;font-weight:500;user-select:all}
.mini{font:600 .82rem var(--body);background:transparent;color:var(--ink);border:1.5px solid var(--ink);border-radius:999px;padding:5px 12px;cursor:pointer;text-decoration:none;display:inline-block}
.mini.danger{color:var(--bad);border-color:var(--bad)}
.wrap>a.mini{align-self:flex-start}
form,.stack{display:flex;flex-direction:column;gap:14px}
.f{display:flex;flex-direction:column;gap:5px;min-width:0}
.f>label{font-weight:600;font-size:.92rem}
input[type=text],input[type=tel],input[type=url],input[type=number],input[type=password],input[type=search],textarea,select{font:400 1rem var(--body);color:var(--ink);background:var(--bg);border:1.5px solid var(--line);border-radius:12px;padding:10px 12px;width:100%;min-width:0}
textarea{min-height:80px;resize:vertical}
.inline{display:flex;gap:8px;align-items:center}
.inline input{flex:1}
.status{font-size:.88rem;font-weight:600}
.status.ok{color:var(--ok)} .status.warn{color:var(--warn)} .status.bad{color:var(--bad)}
.check{display:flex;gap:10px;align-items:flex-start;font-size:.92rem}
.check input{width:20px;height:20px;margin-top:2px;flex:none;accent-color:var(--accent)}
.wa{display:flex;justify-content:center;align-items:center;background:var(--wa);color:var(--wa-ink);text-decoration:none;font:700 1.05rem var(--body);border-radius:999px;padding:14px 20px;text-align:center;border:0;cursor:pointer}
.solid{font:700 1rem var(--body);background:var(--ink);color:var(--bg);border:0;border-radius:999px;padding:12px 20px;cursor:pointer;text-decoration:none;text-align:center}
.legal{color:var(--muted);font-size:.84rem;max-width:70ch}
.mhero{background:var(--ink);color:var(--bg);border-radius:28px;padding:24px;display:flex;flex-direction:column;gap:14px}
.mhero h1{font-size:clamp(2rem,7vw,3.6rem);font-weight:800;letter-spacing:-.02em}
.mhero h1 b{color:var(--lager)}
.mhero ul{margin:0;padding-left:20px;display:flex;flex-direction:column;gap:4px;max-width:60ch}
.mcard{background:var(--lager);color:var(--lager-ink);border-radius:20px;padding:20px;display:flex;flex-direction:column;gap:6px}
.mcard .num{font-family:var(--mono);font-size:1.5rem;font-weight:500;letter-spacing:.04em}
.bar{position:fixed;left:0;right:0;bottom:0;padding:10px 16px calc(10px + env(safe-area-inset-bottom,0px));background:var(--ink);color:var(--bg);z-index:5}
.bar .in{max-width:1080px;margin:0 auto;display:flex;justify-content:space-between;align-items:center;gap:12px}
.bar a{background:var(--lager);color:var(--lager-ink);text-decoration:none;font-weight:700;border-radius:999px;padding:9px 18px;white-space:nowrap}
.bar small{display:block;opacity:.75;font-size:.78rem}
/* back office */
.tabs{display:flex;gap:6px;flex-wrap:wrap}
.tbl{overflow-x:auto;border:1px solid var(--line);border-radius:16px;background:var(--surface)}
table{border-collapse:collapse;width:100%;font-size:.92rem}
th,td{text-align:left;padding:10px 12px;border-bottom:1px solid var(--line);vertical-align:top}
th{font-size:.78rem;text-transform:uppercase;letter-spacing:.06em;color:var(--muted)}
td.num{text-align:right;font-family:var(--mono)}
.badge{display:inline-block;border-radius:999px;padding:2px 10px;font-size:.78rem;font-weight:700;border:1.5px solid currentColor;white-space:nowrap}
.b-baru,.b-pending{color:var(--warn)} .b-lunas,.b-aktif{color:var(--ok)} .b-dikirim{color:var(--accent)}
.b-selesai{color:var(--muted)} .b-batal,.b-ditolak,.b-dicabut{color:var(--bad)}
.arow{border:1px solid var(--line);border-radius:16px;padding:14px;display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:10px;align-items:end;background:var(--surface)}
.arow .wide{grid-column:span 2}
@media (max-width:420px){.arow .wide{grid-column:auto}}
.af{display:flex;flex-direction:column;gap:4px;font-size:.8rem;font-weight:600;color:var(--muted);min-width:0}
.af input,.af select{padding:8px 10px;font-size:.95rem}
.af.chk{flex-direction:row;align-items:center;gap:8px;color:var(--ink);font-size:.9rem;padding-bottom:8px}
.af.chk input{width:20px;height:20px;accent-color:var(--accent)}
.photos{display:flex;gap:12px;flex-wrap:wrap}
.photos a{display:flex;flex-direction:column;gap:4px;text-decoration:none;font-size:.8rem;font-weight:600;color:var(--muted)}
.photos img{width:220px;max-width:100%;height:150px;object-fit:cover;border-radius:12px;border:1px solid var(--line);background:var(--bg)}
dl.kv{margin:0;display:grid;grid-template-columns:auto minmax(0,1fr);gap:4px 14px}
dl.kv dt{color:var(--muted)} dl.kv dd{margin:0;overflow-wrap:anywhere}
"""
app.jinja_env.globals["CSS"] = CSS

T = {}

T["base.html"] = r"""<!doctype html>
<html lang="id"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<title>{% block title %}Bacus Bandung{% endblock %}</title>
<link rel="preconnect" href="https://fonts.googleapis.com"><link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Bricolage+Grotesque:opsz,wght@12..96,600;12..96,800&family=Plus+Jakarta+Sans:wght@400;500;600;700&family=DM+Mono:wght@400;500&display=swap">
<style nonce="{{ nonce() }}">{{ CSS|safe }}</style></head>
<body>
<div class="wrap">
  <div class="nav">
    <a class="brand" href="{{ url_for('shop') }}">BACUS BANDUNG · Bottleshop</a>
    <nav aria-label="Menu">
      {% block nav %}
      <a href="{{ url_for('shop') }}" class="{{ 'on' if request.endpoint == 'shop' }}">Toko</a>
      <span class="age">21+</span>
      {% endblock %}
    </nav>
  </div>
  {% with msgs = get_flashed_messages(with_categories=true) %}{% if msgs %}
  <div class="flash" role="status">{% for c, m in msgs %}<p class="{{ c }}">{{ m }}</p>{% endfor %}</div>
  {% endif %}  {% endwith %}
  {% block body %}{% endblock %}
</div>
{% block after %}{% endblock %}
<script nonce="{{ nonce() }}">
document.addEventListener("click", function (e) {
  var t = e.target.closest("[data-confirm]");
  if (t && !confirm(t.getAttribute("data-confirm"))) { e.preventDefault(); e.stopPropagation(); }
}, true);
document.addEventListener("submit", function (e) {
  var t = e.target.closest("[data-confirm-form]");
  if (t && !confirm(t.getAttribute("data-confirm-form"))) { e.preventDefault(); }
}, true);
</script>
</body></html>"""

T["shop.html"] = r"""{% extends "base.html" %}
{% block body %}
<header class="hero">
  <h1>Bir dingin, <span>diantar</span> ke rumah.</h1>
  <p>Beer, anggur, wine, whisky, sampai minuman tradisional. Pilih di sini, kirim order ke WhatsApp toko, transfer, lalu kami antar ke titik lokasimu.</p>
  <ul class="chips">
    <li>Free ongkir radius {{ S.radius_km }} km{% if S.free_min %}, min. belanja {{ S.free_min|rp }}{% endif %}</li>
    <li>Lewat radius: {{ S.ship_per_km|rp }} per km</li>
    <li>Bayar via transfer</li>
    {% if S.hours_on %}<li>Buka {{ S.open_time }} - {{ S.close_time }} WIB</li>{% endif %}
  </ul>
</header>
{% if not store_open %}<div class="banner closed" role="status">{{ store_msg }}</div>{% endif %}
{% if S.banner %}<div class="banner">{{ S.banner }}</div>{% endif %}

<section aria-labelledby="h-cara">
  <div class="sec-head"><h2 id="h-cara">Cara order</h2></div>
  <ol class="steps">
    <li><b>Pilih minuman</b><span>Masukkan ke keranjang.</span></li>
    <li><b>Isi data antar</b><span>Lengkapi semua data, bagikan pin rumah dari Google Maps, dan unggah foto rumah.</span></li>
    <li><b>Kirim ke WhatsApp</b><span>Pesanan tersimpan; tekan Kirim di WhatsApp agar toko menerima notifikasi.</span></li>
    <li><b>Transfer</b><span>Kirim bukti transfer di chat yang sama.</span></li>
    <li><b>Diantar</b><span>Setelah admin memverifikasi transfer.</span></li>
  </ol>
</section>

<section aria-labelledby="h-kat">
  <div class="sec-head"><h2 id="h-kat">Katalog</h2></div>
  <div class="filters">
    <button type="button" class="pill" data-cat="all" aria-pressed="true">Semua</button>
    {% for k, l in CATS %}<button type="button" class="pill" data-cat="{{ k }}" aria-pressed="false">{{ l }}</button>{% endfor %}
  </div>
  <div class="grid" id="grid">
    {% for p in products %}
    <article class="card" data-cat="{{ p.cat }}" data-id="{{ p.id }}">
      {% if p.image_file %}<img class="product-image" src="{{ url_for('product_photo', name=p.image_file) }}" alt="Foto {{ p.name }}" loading="lazy">{% endif %}
      <div class="label lab-{{ p.label }}">
        <span class="abv">{{ ('%g' % p.abv)|replace('.', ',') }}<small>% ABV</small></span><span class="style">{{ p.style }}</span>
      </div>
      <div class="info"><div><h3>{{ p.name }}</h3><span class="vol">{{ p.volume }}</span></div>
        <div class="buy"><span class="price mono">{% if eff_price(p) < p.price %}<s>{{ p.price|rp }}</s><span class="promo">{{ p.promo_price|rp }}</span>{% else %}{{ p.price|rp }}{% endif %}</span><span class="ctl"></span></div>
      </div>
    </article>
    {% endfor %}
  </div>
  <p class="empty" id="cat-empty" hidden>Belum ada produk di kategori ini.</p>
</section>

<section id="checkout" aria-labelledby="h-co">
  <div class="sec-head"><h2 id="h-co">Checkout</h2></div>
  <form class="two" method="post" action="{{ url_for('checkout') }}" enctype="multipart/form-data" id="co-form">
    {{ csrf() }}<input type="hidden" name="items" id="items">
    <div class="panel">
      <h3>Pesananmu</h3>
      <ul class="lines" id="lines"></ul>
      <div class="f">
        <label for="kode">Kode promo</label>
        <div class="inline"><input type="text" name="kode" id="kode" autocomplete="off" autocapitalize="characters"><button type="button" class="mini" id="kode-btn">Pakai</button></div>
        <span class="status" id="kode-status" role="status"></span>
      </div>
      <div class="tot mono" id="tot"></div>
      <div class="box">
        <span class="hint">Transfer ke rekening toko</span>
        <span><b>{{ S.bank_name }}</b> · a.n. {{ S.bank_holder }}</span>
        <div class="row"><span class="mono no" id="bank-no">{{ S.bank_no }}</span><button type="button" class="mini" data-copy="{{ S.bank_no|replace(' ', '') }}">Salin</button></div>
        <span class="hint">Pesanan dikirim setelah admin WhatsApp memverifikasi transfer.</span>
      </div>
    </div>
    <div class="panel">
      <h3>Data pengantaran</h3>
      <div class="f"><label for="nama">Nama penerima</label><input type="text" name="nama" id="nama" autocomplete="name" minlength="2" required></div>
      <div class="f"><label for="wa">Nomor WhatsApp</label><input type="tel" name="wa" id="wa" inputmode="tel" placeholder="08xxxxxxxxxx" autocomplete="tel" required></div>
      <div class="f"><label for="alamat">Alamat lengkap</label><textarea name="alamat" id="alamat" placeholder="Jalan, nomor rumah, RT/RW, kelurahan, kecamatan" minlength="15" required></textarea></div>
      <div class="f"><label for="patokan">Patokan lokasi</label><input type="text" name="patokan" id="patokan" placeholder="Contoh: pagar hitam, sebelah minimarket" minlength="2" required></div>
      <div class="f">
        <label for="peta">Link Google Maps titik rumah</label>
        <input type="url" name="peta" id="peta" inputmode="url" placeholder="https://maps.app.goo.gl/..." required>
        <span class="hint">Buka Google Maps, tekan lama tepat di rumahmu, pilih Bagikan, lalu tempel link di sini.</span>
        <span class="status" id="peta-status" role="status"></span>
      </div>
      <div class="f">
        <label for="foto">Foto tampak depan rumah</label>
        <input type="file" name="foto" id="foto" accept="image/jpeg,image/png,image/webp" required>
        <span class="hint">Wajib diunggah setiap order. Foto ikut dikirim ke WhatsApp admin dari halaman berikutnya.</span>
      </div>
      <label class="check" for="umur"><input type="checkbox" name="umur" id="umur" value="1" required><span>Saya berusia 21 tahun ke atas dan siap menunjukkan KTP saat pesanan diterima.</span></label>
      <button type="submit" class="wa" id="co-btn" {{ '' if store_open else 'disabled' }}>{{ 'Simpan pesanan &amp; lanjut ke WhatsApp'|safe if store_open else 'Toko tutup' }}</button>
      <span class="hint">Setelah pesanan tersimpan, tombol WhatsApp berisi pesan order muncul di halaman berikutnya.</span>
    </div>
  </form>
</section>
<p class="legal">Minuman beralkohol hanya untuk usia 21+. Jangan mengemudi setelah minum. Jarak rumah dibandingkan dengan titik Bacus Bandung menggunakan jarak garis lurus. Free ongkir berlaku sampai {{ S.radius_km }} km{% if S.free_min %} untuk belanja minimal {{ S.free_min|rp }} (dihitung dari subtotal barang sebelum diskon){% endif %}. Di luar radius, ongkir dihitung otomatis {{ S.ship_per_km|rp }} per km (selisih jarak dari batas radius dibulatkan ke atas, misalnya lebih 0,5 km dihitung 1 km).</p>
{% endblock %}
{% block after %}
<div class="bar"><div class="in">
  <div><b id="bar-count">Keranjang kosong</b><small class="mono" id="bar-total">Rp 0</small></div>
  <a href="#checkout">Checkout</a>
</div></div>
<script nonce="{{ nonce() }}">
const P = {{ pdata|tojson }};
const CSRF = {{ csrf_token()|tojson }};
const CLOSED = {{ 'false' if store_open else 'true' }};
const $ = id => document.getElementById(id);
const rp = n => "Rp " + Math.round(n).toLocaleString("id-ID");
const esc = s => String(s).replace(/[&<>"']/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
let cart = {};
try { cart = JSON.parse(localStorage.getItem("bacus-cart") || "{}") || {}; } catch (e) { cart = {}; }
for (const id in cart) if (!P[id]) delete cart[id];
let code = "", timer = null;

function save(){ try { localStorage.setItem("bacus-cart", JSON.stringify(cart)); } catch (e) {} }
function setQty(id, q){ if (q <= 0) delete cart[id]; else cart[id] = Math.min(q, 99); save(); render(); }
function stepper(id, q, name){
  return `<span class="step"><button type="button" data-dec="${id}" aria-label="Kurangi ${esc(name)}">−</button><output>${q}</output><button type="button" data-inc="${id}" aria-label="Tambah ${esc(name)}">+</button></span>`;
}
function render(){
  document.querySelectorAll(".card").forEach(c => {
    const id = c.dataset.id, q = cart[id] || 0;
    c.querySelector(".ctl").innerHTML = CLOSED ? `<button type="button" class="add" disabled>Tutup</button>` : q ? stepper(id, q, P[id].n) : `<button type="button" class="add" data-inc="${id}">Tambah</button>`;
  });
  const ids = Object.keys(cart);
  $("lines").innerHTML = ids.length ? ids.map(id => `<li><span class="nm"><b>${esc(P[id].n)}</b><br><span class="vol mono">${cart[id]} × ${rp(P[id].p)}</span></span>${stepper(id, cart[id], P[id].n)}</li>`).join("")
    : `<li class="empty">Belum ada minuman di keranjang. Pilih dulu di katalog.</li>`;
  let count = 0, sub = 0;
  ids.forEach(id => { count += cart[id]; sub += cart[id] * P[id].p; });
  $("bar-count").textContent = count ? count + " item di keranjang" : "Keranjang kosong";
  $("bar-total").textContent = rp(sub);
  $("items").value = JSON.stringify(cart);
  quoteSoon();
}
function quoteSoon(){ clearTimeout(timer); timer = setTimeout(quote, 350); }
async function quote(){
  try {
    const r = await fetch("{{ url_for('api_hitung') }}", {method: "POST", headers: {"Content-Type": "application/json", "X-CSRF": CSRF},
      body: JSON.stringify({items: cart, kode: code, peta: $("peta").value})});
    if (!r.ok) return;
    const c = await r.json();
    const ship = c.free ? "GRATIS" : c.ship_fee > 0 ? c.ship_fee_t : (c.map_status === "none" || c.map_status === "invalid") ? "—" : "Dicek admin";
    $("tot").innerHTML = `<div><span>Subtotal</span><span>${c.sub_t}</span></div>`
      + (c.promo_disc ? `<div class="disc"><span>Kode ${esc(c.promo_code)}</span><span>− ${c.promo_disc_t}</span></div>` : "")
      + `<div><span>Ongkir</span><span>${ship}</span></div>`
      + (c.short > 0 && c.count ? `<div class="disc"><span>Tambah ${c.short_t} lagi untuk free ongkir</span><span></span></div>` : "")
      + (c.ship_fee > 0 ? `<div class="hint"><span>${c.ship_km} km di luar radius × ${c.ship_rate_t}</span><span></span></div>` : "")
      + `<div class="grand"><span>Total transfer</span><span>${c.ship_fee > 0 ? c.grand_t : c.total_t}${(!c.free && c.ship_fee <= 0 && ship !== "—") ? " + ongkir" : ""}</span></div>`;
    const st = $("peta-status");
    st.textContent = c.map_msg;
    st.className = "status " + (c.map_status === "in" ? "ok" : c.map_status === "invalid" ? "bad" : "warn");
    const ks = $("kode-status");
    ks.textContent = code ? c.code_msg : "";
    ks.className = "status " + (c.code_ok ? "ok" : "warn");
  } catch (e) {}
}
document.addEventListener("click", e => {
  const t = e.target.closest("button"); if (!t) return;
  if (t.dataset.inc && CLOSED) return;
  if (t.dataset.inc) setQty(t.dataset.inc, (cart[t.dataset.inc] || 0) + 1);
  else if (t.dataset.dec) setQty(t.dataset.dec, (cart[t.dataset.dec] || 0) - 1);
  else if (t.dataset.cat){
    document.querySelectorAll(".filters .pill").forEach(b => b.setAttribute("aria-pressed", b === t));
    let shown = 0;
    document.querySelectorAll(".card").forEach(c => { c.hidden = !(t.dataset.cat === "all" || c.dataset.cat === t.dataset.cat); if (!c.hidden) shown++; });
    $("cat-empty").hidden = shown > 0;
  }
  else if (t.id === "kode-btn"){ code = $("kode").value.trim(); quote(); }
  else if (t.dataset.copy){
    const done = () => { t.textContent = "Tersalin"; setTimeout(() => t.textContent = "Salin", 1500); };
    try { navigator.clipboard.writeText(t.dataset.copy).then(done, () => {}); } catch (err) {}
  }
});
$("peta").addEventListener("change", quote);
$("kode").addEventListener("change", () => { code = $("kode").value.trim(); quote(); });
$("co-form").addEventListener("submit", e => { if (CLOSED) { e.preventDefault(); return; } $("items").value = JSON.stringify(cart); $("co-btn").disabled = true; $("co-btn").textContent = "Menyimpan..."; });
window.addEventListener("pageshow", () => { $("co-btn").disabled = CLOSED; $("co-btn").textContent = CLOSED ? "Toko tutup" : "Simpan pesanan & lanjut ke WhatsApp"; });
render();
</script>
{% endblock %}"""

T["order.html"] = r"""{% extends "base.html" %}
{% block title %}Pesanan {{ o.order_no }} · Bacus Bandung{% endblock %}
{% block body %}
<div class="two">
  <div class="panel">
    <h2>Pesanan tersimpan</h2>
    <p>Nomor order <b class="mono">{{ o.order_no }}</b> · <span class="badge b-{{ o.status }}">{{ ORDER_STATUS_D[o.status] }}</span></p>
    <ul class="lines">{% for l in lines %}<li><span class="nm"><b>{{ l.name }}</b><br><span class="vol mono">{{ l.qty }} × {{ l.price|rp }}</span></span><span class="mono">{{ l.total|rp }}</span></li>{% endfor %}</ul>
    <div class="tot mono">
      <div><span>Subtotal</span><span>{{ o.subtotal|rp }}</span></div>
      {% if o.promo_disc %}<div class="disc"><span>Kode {{ o.promo_code }}</span><span>− {{ o.promo_disc|rp }}</span></div>{% endif %}
      <div><span>Ongkir</span><span>{% if o.free_ship %}GRATIS{% elif o.ship_fee %}{{ o.ship_fee|rp }}{% else %}Dicek admin{% endif %}</span></div>
      <div><span>Jarak dari toko</span><span>{{ o.distance_km|km }} km ·
        {% if delivery_status == 'out' %}{{ o.ship_km }} km di luar radius {{ o.delivery_radius_km|km }} km
        {% else %}dalam radius toko{% endif %}</span></div>
      <div class="grand"><span>Total transfer</span><span>{% if o.ship_fee %}{{ (o.total + o.ship_fee)|rp }}{% else %}{{ o.total|rp }}{{ '' if o.free_ship else ' + ongkir' }}{% endif %}</span></div>
    </div>
  </div>
  <div class="panel">
    <h3>Langkah berikutnya</h3>
    <ol class="stack" style="margin:0;padding-left:20px">
      <li>{% if o.house_file %}Tekan <b>Kirim pesanan + foto rumah</b>, pilih WhatsApp, lalu pilih chat admin dan tekan kirim. Foto rumah ikut terlampir.{% else %}Tekan tombol hijau di bawah, lalu tekan kirim di WhatsApp.{% endif %}</li>
      <li>{% if o.free_ship %}Transfer <b>{{ o.total|rp }}</b>{% elif o.ship_fee %}Transfer <b>{{ (o.total + o.ship_fee)|rp }}</b> (barang + ongkir){% else %}Tunggu admin mengonfirmasi ongkir, lalu transfer totalnya{% endif %} ke rekening di bawah.</li>
      <li>Kirim foto bukti transfer di chat yang sama. Pesanan diantar setelah admin memverifikasi transfer.</li>
    </ol>
    {% if o.house_file %}
    <button type="button" class="wa" id="share-btn" data-msg="{{ msg }}" data-photo="{{ url_for('order_photo', order_no=o.order_no, k=o.token) }}" data-name="foto-rumah-{{ o.order_no }}.jpg" hidden>Kirim pesanan + foto rumah ke WhatsApp</button>
    <p class="hint" id="share-hint" hidden>WhatsApp terbuka dengan foto dan detail order terlampir. Pilih chat admin ({{ admin_whatsapp() }}), lalu tekan Kirim.</p>
    {% endif %}
    <a class="wa" id="wa-link" href="{{ wa }}" target="_blank" rel="noopener">Kirim detail order ke admin ({{ admin_whatsapp() }})</a>
    {% if o.house_file %}
    <div class="stack" id="photo-fallback">
      <p class="hint">Kalau tombol di atas tidak muncul (misalnya di komputer), kirim detail order lewat tombol hijau, lalu lampirkan foto rumahmu di chat itu secara manual:</p>
      <img src="{{ url_for('order_photo', order_no=o.order_no, k=o.token) }}" alt="Foto rumah yang kamu unggah" style="max-width:220px;border-radius:12px;border:1px solid var(--line)">
      <a class="mini" href="{{ url_for('order_photo', order_no=o.order_no, k=o.token) }}" download="foto-rumah-{{ o.order_no }}.jpg">Simpan foto rumah</a>
    </div>
    {% endif %}
    <p class="hint">Tekan Kirim di WhatsApp agar admin benar-benar menerima pesananmu. Pengiriman otomatis tanpa menekan Kirim tidak bisa dilakukan oleh website.</p>
    <div class="box">
      <span class="hint">Rekening toko</span>
      <span><b>{{ S.bank_name }}</b> · a.n. {{ S.bank_holder }}</span>
      <div class="row"><span class="mono no">{{ S.bank_no }}</span><button type="button" class="mini" data-copy="{{ S.bank_no|replace(' ', '') }}">Salin</button></div>
    </div>
    <p class="hint">Simpan halaman ini kalau perlu melihat pesananmu lagi.</p>
  </div>
</div>
{% endblock %}
{% block after %}
<script nonce="{{ nonce() }}">
try { localStorage.removeItem("bacus-cart"); } catch (e) {}
(function () {
  const btn = document.getElementById("share-btn");
  if (!btn || !navigator.share || !navigator.canShare) return;
  let file = null;
  fetch(btn.dataset.photo, {credentials: "same-origin"}).then(r => r.ok ? r.blob() : null).then(b => {
    if (!b) return;
    const f = new File([b], btn.dataset.name, {type: b.type || "image/jpeg"});
    if (!navigator.canShare({files: [f]})) return;
    file = f;
    btn.hidden = false;
    document.getElementById("share-hint").hidden = false;
  }).catch(() => {});
  btn.addEventListener("click", () => {
    if (!file) return;
    navigator.share({files: [file], text: btn.dataset.msg}).catch(() => {});
  });
})();
document.addEventListener("click", e => {
  const t = e.target.closest("[data-copy]"); if (!t) return;
  try { navigator.clipboard.writeText(t.dataset.copy).then(() => { t.textContent = "Tersalin"; setTimeout(() => t.textContent = "Salin", 1500); }, () => {}); } catch (err) {}
});
</script>
{% endblock %}"""

T["error.html"] = r"""{% extends "base.html" %}
{% block body %}
<div class="panel" style="max-width:560px"><h2>{{ 'Halaman tidak ditemukan' if code == 404 else ('Terlalu banyak permintaan' if code == 429 else ('Kesalahan server' if code == 500 else 'Permintaan tidak bisa diproses')) }}</h2>
<p>{{ msg if code != 404 else 'Periksa lagi alamat halamannya.' }}</p><a class="solid" href="{{ url_for('shop') }}">Kembali ke toko</a></div>
{% endblock %}"""

# ---- back office templates ----
T["admin_base.html"] = r"""{% extends "base.html" %}
{% block title %}Back office · Bacus Bandung{% endblock %}
{% block nav %}
<a href="{{ url_for('shop') }}" target="_blank" rel="noopener">Lihat toko</a>
<form method="post" action="{{ url_for('admin_logout') }}" style="display:inline">{{ csrf() }}<button class="mini" type="submit">Keluar ({{ me_admin.username }})</button></form>
{% endblock %}
{% block body %}
<div class="tabs">
  {% for k, l, ep in [('pesanan','Pesanan','admin_orders'),('produk','Produk & harga','admin_products'),('promo','Promo','admin_promos'),('pengaturan','Pengaturan','admin_settings'),('akun','Akun admin','admin_account')] %}
  <a href="{{ url_for(ep) }}" class="{{ 'on' if tab == k }}">{{ l }}</a>
  {% endfor %}
</div>
{% block admin %}{% endblock %}
{% endblock %}"""

T["admin_login.html"] = r"""{% extends "base.html" %}
{% block title %}Masuk back office{% endblock %}
{% block body %}
<form class="panel" method="post" style="max-width:420px">
  {{ csrf() }}
  <h2>Back office</h2>
  <div class="f"><label for="u">Username</label><input type="text" name="username" id="u" autocomplete="username"></div>
  <div class="f"><label for="p">Password</label><input type="password" name="password" id="p" autocomplete="current-password"></div>
  <button class="solid" type="submit">Masuk</button>
</form>
{% endblock %}"""

T["admin_orders.html"] = r"""{% extends "admin_base.html" %}
{% block admin %}
<div class="row">
  <div class="filters" style="margin:0">
    {% for k, l in ORDER_STATUS %}<a class="pill {{ 'on' if st == k }}" href="{{ url_for('admin_orders', status=k) }}">{{ l }} ({{ counts.get(k, 0) }})</a>{% endfor %}
    <a class="pill {{ 'on' if st == 'semua' }}" href="{{ url_for('admin_orders', status='semua') }}">Semua</a>
  </div>
  <form method="get" class="inline"><input type="hidden" name="status" value="{{ st }}"><input type="search" name="q" value="{{ q }}" placeholder="Cari no. order, nama, WA" aria-label="Cari pesanan"><button class="mini" type="submit">Cari</button></form>
</div>
<div class="tbl"><table>
  <thead><tr><th>No. order</th><th>Waktu</th><th>Pembeli</th><th>Total</th><th>Ongkir</th><th>Status</th></tr></thead>
  <tbody>
  {% for o in rows %}
    <tr><td><a href="{{ url_for('admin_order', oid=o.id) }}" class="mono">{{ o.order_no }}</a></td><td>{{ o.created_at }}</td>
      <td>{{ o.name }}<br><span class="hint">{{ o.wa }}</span></td>
      <td class="num">{{ (o.total + (o.ship_fee or 0))|rp }}</td><td>{% if o.free_ship %}Gratis{% elif o.ship_fee %}{{ o.ship_fee|rp }}{% else %}Cek{% endif %} · {{ o.distance_km|km }} km</td>
      <td><span class="badge b-{{ o.status }}">{{ ORDER_STATUS_D[o.status] }}</span></td></tr>
  {% else %}
    <tr><td colspan="6" class="empty">Belum ada pesanan di daftar ini.</td></tr>
  {% endfor %}
  </tbody></table></div>
{% endblock %}"""

T["admin_order.html"] = r"""{% extends "admin_base.html" %}
{% block admin %}
<a class="mini" href="{{ url_for('admin_orders') }}">← Semua pesanan</a>
<div class="two">
  <div class="panel">
    <h2 class="mono" style="font-size:1.5rem">{{ o.order_no }}</h2>
    <p><span class="badge b-{{ o.status }}">{{ ORDER_STATUS_D[o.status] }}</span> · {{ o.created_at }}</p>
    <ul class="lines">{% for l in lines %}<li><span class="nm"><b>{{ l.name }}</b> <span class="hint">{{ l.volume }}</span><br><span class="vol mono">{{ l.qty }} × {{ l.price|rp }}</span></span><span class="mono">{{ l.total|rp }}</span></li>{% endfor %}</ul>
    <div class="tot mono">
      <div><span>Subtotal</span><span>{{ o.subtotal|rp }}</span></div>
      {% if o.promo_disc %}<div class="disc"><span>Kode {{ o.promo_code }}</span><span>− {{ o.promo_disc|rp }}</span></div>{% endif %}
      <div><span>Ongkir</span><span>{% if o.free_ship %}GRATIS{% elif o.ship_fee %}{{ o.ship_fee|rp }} ({{ o.ship_km }} km){% else %}Perlu dikonfirmasi{% endif %}</span></div>
      <div class="grand"><span>Total transfer</span><span>{% if o.ship_fee %}{{ (o.total + o.ship_fee)|rp }}{% else %}{{ o.total|rp }}{{ '' if o.free_ship else ' + ongkir' }}{% endif %}</span></div>
    </div>
    <form method="post" class="stack">
      {{ csrf() }}
      <div class="f"><label for="status">Status pesanan</label>
        <select name="status" id="status">{% for k, l in ORDER_STATUS %}<option value="{{ k }}" {{ 'selected' if o.status == k }}>{{ l }}</option>{% endfor %}</select></div>
      <div class="f"><label for="note">Catatan admin (ongkir, kurir, dll.)</label><textarea name="note" id="note">{{ o.note or '' }}</textarea></div>
      <button class="solid" type="submit">Simpan status</button>
    </form>
  </div>
  <div class="panel">
    <h3>Pengantaran</h3>
    <dl class="kv">
      <dt>Nama</dt><dd>{{ o.name }}</dd>
      <dt>WhatsApp</dt><dd>{{ o.wa }} · <a href="{{ wa_chat }}" target="_blank" rel="noopener">Chat</a></dd>
      <dt>Alamat</dt><dd>{{ o.address }}</dd>
      {% if o.landmark %}<dt>Patokan</dt><dd>{{ o.landmark }}</dd>{% endif %}
      <dt>Peta</dt><dd><a href="{{ o.map_url }}" target="_blank" rel="noopener noreferrer">Buka Google Maps</a></dd>
      <dt>Jarak</dt><dd>{{ o.distance_km|km }} km (garis lurus) ·
        {% if delivery_status == 'out' %}<b>Di luar radius ({{ o.ship_km }} km lewat)</b>
        {% elif delivery_status == 'in' %}Dalam radius toko
        {% else %}Lokasi belum terverifikasi{% endif %}</dd>
    </dl>
    <div class="photos">
      {% set house = o.house_file %}
      {% if house %}<a href="{{ url_for('admin_photo', name=house) }}" target="_blank"><img src="{{ url_for('admin_photo', name=house) }}" alt="Foto rumah pembeli">Foto rumah</a>{% else %}<p class="empty">Tidak ada foto rumah.</p>{% endif %}
    </div>
    <h3>Kabari pembeli</h3>
    <a class="wa" href="{{ wa_msgs.lunas }}" target="_blank" rel="noopener">Transfer diterima</a>
    <a class="wa" href="{{ wa_msgs.dikirim }}" target="_blank" rel="noopener">Pesanan sedang diantar</a>
    <p class="hint">Tombol membuka WhatsApp dengan pesan terisi. Status pesanan tetap diubah lewat form status.</p>
  </div>
</div>
{% endblock %}"""

T["admin_products.html"] = r"""{% extends "admin_base.html" %}
{% macro fields(p) %}
  <label class="af wide">Nama produk<input type="text" name="name" value="{{ p.name if p }}" required></label>
  {% if p and p.image_file %}<div class="product-photo-preview wide"><img src="{{ url_for('product_photo', name=p.image_file) }}" alt="Foto {{ p.name }}"></div>{% endif %}
  <label class="af wide">Foto produk (JPG, PNG, atau WEBP; maks. 10 MB)<input type="file" name="foto" accept="image/jpeg,image/png,image/webp"></label>
  {% if p and p.image_file %}<label class="af chk"><input type="checkbox" name="hapus_foto" value="1">Hapus foto saat disimpan</label>{% endif %}
  <label class="af">Kemasan<input type="text" name="volume" value="{{ p.volume if p }}" placeholder="330 ml · botol"></label>
  <label class="af">Jenis<input type="text" name="style" value="{{ p.style if p }}" placeholder="Lager"></label>
  <label class="af">ABV %<input type="number" step="0.1" min="0" name="abv" value="{{ ('%g' % p.abv) if p else '' }}"></label>
  <label class="af">Kategori<select name="cat">{% for k, l in CATS %}<option value="{{ k }}" {{ 'selected' if p and p.cat == k }}>{{ l }}</option>{% endfor %}</select></label>
  <label class="af">Harga (Rp)<input type="number" step="500" min="0" name="price" value="{{ p.price if p else '' }}" required></label>
  <label class="af">Harga promo (0 = tidak ada)<input type="number" step="500" min="0" name="promo_price" value="{{ p.promo_price if p else 0 }}"></label>
  <label class="af">Warna label<select name="label">{% for k in LABELS %}<option value="{{ k }}" {{ 'selected' if p and p.label == k }}>{{ {'a':'Kuning','b':'Oranye','c':'Hijau','d':'Ungu','e':'Merah muda'}[k] }}</option>{% endfor %}</select></label>
  <label class="af">Urutan<input type="number" name="sort" value="{{ p.sort if p else 0 }}"></label>
  <label class="af chk"><input type="checkbox" name="active" value="1" {{ 'checked' if not p or p.active }}>Tampil di toko</label>
{% endmacro %}
{% block admin %}
<div class="filters" style="margin:0">
  <a class="pill {{ 'on' if not cat }}" href="{{ url_for('admin_products') }}">Semua</a>
  {% for k, l in CATS %}<a class="pill {{ 'on' if cat == k }}" href="{{ url_for('admin_products', cat=k) }}">{{ l }}</a>{% endfor %}
</div>
<details class="panel"><summary><b>Tambah produk baru</b></summary>
  <form method="post" enctype="multipart/form-data" class="arow" style="border:0;padding:0;margin-top:12px">{{ csrf() }}<input type="hidden" name="action" value="tambah">{{ fields(None) }}<button class="solid" type="submit">Tambah</button></form>
</details>
{% for p in rows %}
<form method="post" enctype="multipart/form-data" class="arow">
  {{ csrf() }}<input type="hidden" name="id" value="{{ p.id }}">
  {{ fields(p) }}
  <div class="inline"><button class="mini" type="submit" name="action" value="simpan">Simpan</button>
  <button class="mini danger" type="submit" name="action" value="hapus" data-confirm="Hapus produk {{ p.name }}?">Hapus</button></div>
</form>
{% else %}<p class="empty">Belum ada produk di kategori ini.</p>{% endfor %}
{% endblock %}"""

T["admin_promos.html"] = r"""{% extends "admin_base.html" %}
{% macro fields(p) %}
  <label class="af">Kode<input type="text" name="code" value="{{ p.code if p }}" autocapitalize="characters" required></label>
  <label class="af">Jenis potongan<select name="kind"><option value="rp" {{ 'selected' if p and p.kind == 'rp' }}>Rupiah</option><option value="pct" {{ 'selected' if p and p.kind == 'pct' }}>Persen</option></select></label>
  <label class="af">Nilai<input type="number" name="value" min="1" value="{{ p.value if p else '' }}" required></label>
  <label class="af">Minimal belanja (Rp)<input type="number" name="min_order" min="0" step="1000" value="{{ p.min_order if p else 0 }}"></label>
  <label class="af chk"><input type="checkbox" name="active" value="1" {{ 'checked' if not p or p.active }}>Aktif</label>
{% endmacro %}
{% block admin %}
<form method="post" class="panel">{{ csrf() }}<input type="hidden" name="action" value="banner">
  <h3>Banner promo</h3>
  <div class="f"><label for="banner">Teks banner di halaman toko (kosongkan untuk menyembunyikan)</label><input type="text" name="banner" id="banner" maxlength="200" value="{{ S.banner }}"></div>
  <button class="solid" type="submit">Simpan banner</button>
</form>
<div class="panel">
  <h3>Kode promo</h3>
  <p class="hint">Pembeli mengetik kode saat checkout. Harga coret per produk diatur di menu Produk &amp; harga.</p>
  <form method="post" class="arow">{{ csrf() }}<input type="hidden" name="action" value="tambah">{{ fields(None) }}<button class="solid" type="submit">Tambah kode</button></form>
  {% for p in rows %}
  <form method="post" class="arow">{{ csrf() }}<input type="hidden" name="id" value="{{ p.id }}">{{ fields(p) }}
    <div class="inline"><button class="mini" type="submit" name="action" value="simpan">Simpan</button>
    <button class="mini danger" type="submit" name="action" value="hapus" data-confirm="Hapus kode {{ p.code }}?">Hapus</button></div></form>
  {% else %}<p class="empty">Belum ada kode promo.</p>{% endfor %}
</div>
{% endblock %}"""

T["admin_settings.html"] = r"""{% extends "admin_base.html" %}
{% block admin %}
<form method="post" class="stack">{{ csrf() }}
  <div class="panel"><h3>WhatsApp dan rekening</h3><div class="arow" style="border:0;padding:0">
    <label class="af wide">Nomor WhatsApp admin penerima notifikasi<input type="tel" name="wa" value="{{ admin_whatsapp() }}"></label>
    <p class="hint wide">Format lokal 08... atau internasional 62... diterima. Jika BACUS_ADMIN_WA diatur di Railway, nomor tersebut menjadi penerima dan mengesampingkan isian ini.</p>
    <label class="af">Bank<input type="text" name="bank_name" value="{{ S.bank_name }}"></label>
    <label class="af">Nomor rekening<input type="text" name="bank_no" value="{{ S.bank_no }}"></label>
    <label class="af">Atas nama<input type="text" name="bank_holder" value="{{ S.bank_holder }}"></label>
  </div></div>
  <div class="panel"><h3>Jam buka toko</h3>
    <p class="hint">Di luar jam buka, pengunjung masih bisa melihat katalog, tetapi tombol tambah dan kirim pesanan nonaktif. Pengecekan juga dilakukan di server. Zona waktu: WIB.</p>
    <div class="arow" style="border:0;padding:0">
      <label class="af">Jam buka<input type="time" name="open_time" value="{{ S.open_time }}" required></label>
      <label class="af">Jam tutup<input type="time" name="close_time" value="{{ S.close_time }}" required></label>
      <label class="af chk"><input type="checkbox" name="hours_on" value="1" {{ 'checked' if S.hours_on }}>Aktifkan jam buka otomatis</label>
      <label class="af chk"><input type="checkbox" name="force_closed" value="1" {{ 'checked' if S.force_closed }}>Tutup sekarang (manual, mengabaikan jam)</label>
    </div>
    <p class="hint">Status saat ini: <b>{{ 'BUKA' if store_open else 'TUTUP' }}</b>. Jam tutup lebih kecil dari jam buka dianggap lewat tengah malam (contoh buka 18:00, tutup 02:00).</p>
  </div>
  <div class="panel"><h3>Lokasi toko dan free ongkir</h3>
    <p class="hint">Bacus Bandung · Jl. Khp Hasan Mustopa, Padasuka, Kec. Cibeunying Kidul, Kota Bandung, Jawa Barat 40125 · <a href="https://maps.app.goo.gl/mWTbxSwqTx8SJH3LA" target="_blank" rel="noopener noreferrer">Buka titik toko di Google Maps</a></p>
    <div class="arow" style="border:0;padding:0">
    <label class="af">Radius (km)<input type="number" step="0.5" min="0" name="radius_km" value="{{ S.radius_km }}"></label>
    <label class="af">Minimal belanja free ongkir (Rp)<input type="number" step="1000" min="0" name="free_min" value="{{ S.free_min }}"></label>
    <label class="af">Ongkir per km di luar radius (Rp)<input type="number" step="500" min="0" name="ship_per_km" value="{{ S.ship_per_km }}"></label>
    <label class="af">Latitude toko<input type="text" name="store_lat" value="{{ S.store_lat }}"></label>
    <label class="af">Longitude toko<input type="text" name="store_lng" value="{{ S.store_lng }}"></label>
  </div><p class="hint">Koordinat awal: -6.902017, 107.652076 (dari link Google Maps Bacus). Jarak ke pin rumah dihitung garis lurus, bukan jarak jalan. Di luar radius, ongkir = (selisih jarak dari batas radius, dibulatkan ke atas, minimal 1 km) x tarif per km. Contoh radius 5 km dan tarif Rp3.000: jarak 5,5 km = Rp3.000, jarak 7,2 km = 3 km = Rp9.000. Minimal free ongkir dihitung dari subtotal barang sebelum diskon dan hanya berlaku di dalam radius.</p></div>
  <button class="solid" type="submit">Simpan pengaturan</button>
</form>
{% endblock %}"""

T["admin_account.html"] = r"""{% extends "admin_base.html" %}
{% block admin %}
<div class="two">
  <form class="panel" method="post">{{ csrf() }}<input type="hidden" name="action" value="password">
    <h3>Ganti password</h3>
    <div class="f"><label for="old">Password lama</label><input type="password" name="old" id="old" autocomplete="current-password"></div>
    <div class="f"><label for="new">Password baru (min. 12 karakter)</label><input type="password" name="new" id="new" autocomplete="new-password"></div>
    <div class="f"><label for="new2">Ulangi password baru</label><input type="password" name="new2" id="new2" autocomplete="new-password"></div>
    <button class="solid" type="submit">Ganti password</button>
  </form>
  <div class="stack">
    <form class="panel" method="post">{{ csrf() }}<input type="hidden" name="action" value="tambah">
      <h3>Tambah admin</h3>
      <div class="f"><label for="nu">Username</label><input type="text" name="username" id="nu" autocomplete="off"></div>
      <div class="f"><label for="np">Password (min. 12 karakter)</label><input type="password" name="password" id="np" autocomplete="new-password"></div>
      <button class="solid" type="submit">Tambah</button>
    </form>
    <div class="panel"><h3>Daftar admin</h3>
      {% for a in admins %}<form method="post" class="row">{{ csrf() }}<input type="hidden" name="action" value="hapus"><input type="hidden" name="id" value="{{ a.id }}">
        <span>{{ a.username }}{{ ' (kamu)' if a.id == me_admin.id }}</span>{% if a.id != me_admin.id %}<button class="mini danger" type="submit" data-confirm="Hapus admin {{ a.username }}?">Hapus</button>{% endif %}</form>{% endfor %}
    </div>
  </div>
</div>
{% endblock %}"""

app.jinja_loader = DictLoader(T)

# Siapkan database saat file dimuat (juga saat dijalankan lewat gunicorn)
_created_admin = init_db()
if _created_admin == "baru":
    print("Akun admin pertama dibuat dari environment. Hapus BACUS_ADMIN_PASSWORD dari Variables setelah login berhasil.", flush=True)
elif _created_admin == "reset":
    print("Password admin direset dari environment. Hapus BACUS_ADMIN_RESET dan BACUS_ADMIN_PASSWORD dari Variables sekarang.", flush=True)


if __name__ == "__main__":
    port = int(os.environ.get("PORT", "8000"))
    print(" Toko:        http://localhost:%d" % port)
    print(" Back office: http://localhost:%d/admin" % port, flush=True)
    app.run(host="0.0.0.0", port=port, debug=False)
