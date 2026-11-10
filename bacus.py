#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
BACUS BANDUNG - toko online, member, dan back office dalam satu file.

Isi:
  * Toko: katalog per kategori (Beer, Anggur, Wine, Whisky, Vodka, Tradisional,
    Lain-lain), keranjang, kode promo, hitung jarak dari link Google Maps,
    free ongkir radius 10 km dengan minimal belanja, checkout yang menyimpan
    pesanan + foto rumah lalu membuka WhatsApp toko dengan pesan terisi.
  * Member: daftar dengan foto KTP/SIM + foto rumah + PIN, biaya daftar sekali
    (seumur hidup), diskon otomatis, alamat tersimpan, masuk pakai nomor WA + PIN.
  * Back office (/admin): pesanan dan statusnya, harga produk, harga promo,
    kode promo dan banner, verifikasi member (lihat foto KTP/SIM), pengaturan
    toko (WhatsApp, rekening, titik toko, radius, minimal free ongkir).

CARA MENJALANKAN (lokal)
  1. Pasang Python 3.9+ lalu:  pip install flask pillow
     (pillow tidak wajib, tapi disarankan: foto diperkecil dan data lokasi
      GPS di dalam foto dihapus sebelum disimpan)
  2. Jalankan:  python bacus.py
  3. Buka http://localhost:8000  dan  http://localhost:8000/admin
     Saat pertama kali jalan, username dan password admin dicetak di terminal.
     Segera ganti password di menu Akun.

PENGATURAN LEWAT ENVIRONMENT VARIABLE (opsional)
  BACUS_DATA            folder data (database + foto). Default: ./bacus_data
  BACUS_ADMIN_USER      username admin pertama. Default: admin
  BACUS_ADMIN_PASSWORD  password admin pertama. Default: dibuat acak
  BACUS_SECRET_KEY      kunci sesi. Default: dibuat acak dan disimpan di folder data
  BACUS_HTTPS=1         wajib diisi saat sudah memakai HTTPS (cookie aman)
  PORT                  port server. Default: 8000

MENJALANKAN DI SERVER (produksi)
  pip install flask pillow gunicorn
  BACUS_HTTPS=1 gunicorn -w 2 -b 127.0.0.1:8000 bacus:app
  Taruh di belakang Nginx/Caddy dengan HTTPS. Website ini menyimpan foto KTP,
  jadi JANGAN dibuka ke publik tanpa HTTPS. Folder BACUS_DATA berisi database
  dan foto: jangan dijadikan folder publik, dan buat backup rutin.
"""

import io
import json
import math
import os
import re
import secrets
import sqlite3
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta
from functools import wraps

from flask import (Flask, abort, flash, g, jsonify, redirect, render_template,
                   request, send_file, session, url_for)
from jinja2 import DictLoader
from markupsafe import Markup
from werkzeug.security import check_password_hash, generate_password_hash

try:
    from PIL import Image, ImageOps
except Exception:  # Pillow tidak terpasang: foto disimpan apa adanya
    Image = None

# ---------------------------------------------------------------------------
# Konfigurasi
# ---------------------------------------------------------------------------
BASE = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.environ.get("BACUS_DATA", os.path.join(BASE, "bacus_data"))
UPLOAD_DIR = os.path.join(DATA_DIR, "foto")
DB_PATH = os.path.join(DATA_DIR, "bacus.db")
os.makedirs(UPLOAD_DIR, exist_ok=True)

MAX_FOTO = 10 * 1024 * 1024          # 10 MB per foto
CATS = [("beer", "Beer"), ("anggur", "Anggur"), ("wine", "Wine"), ("whisky", "Whisky"),
        ("vodka", "Vodka"), ("tradisional", "Tradisional"), ("lain", "Lain-lain")]
CAT_KEYS = [c[0] for c in CATS]
LABELS = ["a", "b", "c", "d", "e"]
ORDER_STATUS = [("baru", "Menunggu transfer"), ("lunas", "Transfer terverifikasi"),
                ("dikirim", "Sedang diantar"), ("selesai", "Selesai"), ("batal", "Batal")]
ORDER_STATUS_D = dict(ORDER_STATUS)
MEMBER_STATUS = {"pending": "Menunggu verifikasi", "aktif": "Aktif",
                 "ditolak": "Ditolak", "dicabut": "Dicabut"}

DEFAULT_SETTINGS = {
    "wa": "628974109148",
    "store_lat": -6.902017, "store_lng": 107.652076,
    "radius_km": 10, "free_min": 100000,
    "bank_name": "BCA", "bank_no": "000 000 0000", "bank_holder": "Bacus Bandung",
    "member_fee": 50000, "member_disc": 5, "promo_stack": 1,
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
  promo_price INTEGER DEFAULT 0, label TEXT DEFAULT 'a', active INTEGER DEFAULT 1,
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
  map_url TEXT, distance_km REAL, house_file TEXT, items_json TEXT, subtotal INTEGER,
  member_disc INTEGER, promo_code TEXT, promo_disc INTEGER, free_ship INTEGER,
  total INTEGER, status TEXT DEFAULT 'baru', note TEXT DEFAULT '');
"""

# ---------------------------------------------------------------------------
# Aplikasi
# ---------------------------------------------------------------------------
app = Flask(__name__)


def _secret_key():
    env = os.environ.get("BACUS_SECRET_KEY")
    if env:
        return env
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
    SESSION_COOKIE_SECURE=os.environ.get("BACUS_HTTPS") == "1",
    PERMANENT_SESSION_LIFETIME=timedelta(days=30),
)


def db():
    if "db" not in g:
        g.db = sqlite3.connect(DB_PATH)
        g.db.row_factory = sqlite3.Row
        g.db.execute("PRAGMA foreign_keys=ON")
    return g.db


@app.teardown_appcontext
def _close_db(_exc):
    conn = g.pop("db", None)
    if conn is not None:
        conn.close()


def now_str():
    return datetime.now().strftime("%Y-%m-%d %H:%M")


def init_db():
    conn = sqlite3.connect(DB_PATH)
    conn.executescript(SCHEMA)
    for k, v in DEFAULT_SETTINGS.items():
        conn.execute("INSERT OR IGNORE INTO settings(k, v) VALUES(?, ?)", (k, json.dumps(v)))
    if conn.execute("SELECT COUNT(*) FROM products").fetchone()[0] == 0:
        for i, p in enumerate(SEED_PRODUCTS):
            conn.execute("INSERT INTO products(name, volume, abv, style, cat, price, promo_price, label, sort)"
                         " VALUES(?,?,?,?,?,?,?,?,?)", (*p, i))
        conn.execute("INSERT OR IGNORE INTO promos(code, kind, value, min_order, active)"
                     " VALUES('HALOBACUS', 'rp', 15000, 150000, 0)")
    created = None
    if conn.execute("SELECT COUNT(*) FROM admins").fetchone()[0] == 0:
        user = os.environ.get("BACUS_ADMIN_USER", "admin")
        pw = os.environ.get("BACUS_ADMIN_PASSWORD") or secrets.token_urlsafe(10)
        conn.execute("INSERT INTO admins(username, pw_hash) VALUES(?, ?)",
                     (user, generate_password_hash(pw)))
        created = (user, pw)
    conn.commit()
    conn.close()
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
    d = re.sub(r"\D", "", str(s or ""))
    if d.startswith("0"):
        d = "62" + d[1:]
    elif d.startswith("8"):
        d = "62" + d
    return d


def wa_link(number, text):
    return "https://wa.me/" + norm_wa(number) + "?text=" + urllib.parse.quote(text)


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


# --- CSRF ------------------------------------------------------------------
def csrf_token():
    if "_csrf" not in session:
        session["_csrf"] = secrets.token_urlsafe(32)
    return session["_csrf"]


@app.before_request
def _csrf_protect():
    if request.method == "POST":
        sent = request.form.get("_csrf") or request.headers.get("X-CSRF") or ""
        if not secrets.compare_digest(sent, session.get("_csrf", "")):
            abort(400, "Sesi kedaluwarsa. Muat ulang halaman lalu coba lagi.")


app.jinja_env.globals.update(
    csrf=lambda: Markup('<input type="hidden" name="_csrf" value="%s">' % csrf_token()),
    csrf_token=csrf_token, CATS=CATS, ORDER_STATUS=ORDER_STATUS, ORDER_STATUS_D=ORDER_STATUS_D,
    MEMBER_STATUS=MEMBER_STATUS, LABELS=LABELS)


@app.after_request
def _security_headers(resp):
    resp.headers.setdefault("X-Content-Type-Options", "nosniff")
    resp.headers.setdefault("X-Frame-Options", "DENY")
    resp.headers.setdefault("Referrer-Policy", "same-origin")
    return resp


# --- batas percobaan login ---------------------------------------------------
_fails = {}


def blocked(key):
    now = time.time()
    _fails[key] = [t for t in _fails.get(key, []) if now - t < 600]
    return len(_fails[key]) >= 5


def record_fail(key):
    _fails.setdefault(key, []).append(time.time())


# --- sesi admin dan member ---------------------------------------------------
@app.before_request
def _load_users():
    g.admin = None
    g.member = None
    if session.get("admin_id"):
        g.admin = db().execute("SELECT id, username FROM admins WHERE id=?", (session["admin_id"],)).fetchone()
    if session.get("member_id"):
        m = db().execute("SELECT * FROM members WHERE id=?", (session["member_id"],)).fetchone()
        if m and m["status"] == "aktif":
            g.member = m
        else:
            session.pop("member_id", None)


def admin_required(fn):
    @wraps(fn)
    def wrapper(*a, **kw):
        if not g.admin:
            return redirect(url_for("admin_login", next=request.path))
        return fn(*a, **kw)
    return wrapper


@app.context_processor
def _ctx():
    return {"S": S(), "me_admin": g.get("admin"), "me_member": g.get("member")}


# --- foto ----------------------------------------------------------------
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
    if Image is not None:
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
    r"!3d(-?\d+\.\d+)!4d(-?\d+\.\d+)",
    r"[?&](?:q|query|ll|destination|daddr|center)=(?:loc:)?(-?\d+\.\d+)(?:,|%2C)\s*\+?(-?\d+\.\d+)",
    r"@(-?\d+\.\d+),(-?\d+\.\d+)",
    r"/(?:place|search|dir)/(-?\d+\.\d+),\+?(-?\d+\.\d+)",
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
def compute(items, code, map_url, member):
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
    m_disc = round(sub * float(s["member_disc"]) / 100) if member else 0
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
    if member and not int(s["promo_stack"]) and c_disc and m_disc:
        if c_disc > m_disc:
            m_disc = 0
        else:
            c_disc = 0
            code_msg = "Kode promo tidak bisa digabung dengan diskon member. Diskon member yang dipakai."
    status, dist = locate(map_url)
    free_min = int(s["free_min"] or 0)
    free = status == "in" and sub >= free_min
    short = free_min - sub if status == "in" and not free else 0
    km_txt = ("%.1f" % dist).replace(".", ",") if dist is not None else ""
    map_msg = {
        "none": "",
        "invalid": "Ini bukan link Google Maps. Tempel link dari tombol Bagikan di Google Maps.",
        "unknown": "Link diterima, tapi titiknya belum terbaca. Admin akan mengecek jarak dan ongkir.",
        "in": "Sekitar %s km dari toko, masuk radius free ongkir%s." % (
            km_txt, (" untuk belanja minimal " + rp(free_min)) if free_min else ""),
        "out": "Sekitar %s km dari toko, di luar radius free ongkir %s km. Admin akan mengonfirmasi ongkir." % (
            km_txt, s["radius_km"]),
    }[status]
    return {
        "lines": lines, "count": count, "sub": sub, "member_disc": m_disc,
        "promo_code": code if c_disc else "", "promo_disc": c_disc, "code_msg": code_msg,
        "code_ok": bool(c_disc), "map_status": status, "map_msg": map_msg, "dist": dist,
        "free": free, "short": short, "total": max(0, sub - m_disc - c_disc),
    }


def ship_text(c):
    km_txt = ("%.1f" % c["dist"]).replace(".", ",") if c.get("dist") is not None else ""
    if c["free"]:
        return "GRATIS (sekitar %s km)" % km_txt
    if c["map_status"] == "in":
        return "dicek admin (sekitar %s km, belanja di bawah minimal free ongkir %s)" % (km_txt, rp(S()["free_min"]))
    if c["map_status"] == "out":
        return "dicek admin (sekitar %s km, di luar radius %s km)" % (km_txt, S()["radius_km"])
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
    body = request.get_json(silent=True) or {}
    c = compute(body.get("items") or {}, body.get("kode"), body.get("peta"), g.member)
    c["sub_t"], c["total_t"] = rp(c["sub"]), rp(c["total"])
    c["member_disc_t"], c["promo_disc_t"], c["short_t"] = rp(c["member_disc"]), rp(c["promo_disc"]), rp(c["short"])
    c["dist"] = round(c["dist"], 2) if c["dist"] is not None else None
    return jsonify(c)


@app.route("/checkout", methods=["POST"])
def checkout():
    f = request.form
    try:
        items = json.loads(f.get("items") or "{}")
    except ValueError:
        items = {}
    c = compute(items, f.get("kode"), f.get("peta", "").strip(), g.member)
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
    if c["map_status"] in ("none", "invalid"):
        errors.append("Tempel link Google Maps titik rumahmu.")
    if not f.get("umur"):
        errors.append("Centang pernyataan usia 21 tahun ke atas.")
    house = None
    if not errors:
        house, err = save_photo(request.files.get("foto"), "rumah")
        if err == "missing":
            if not g.member:
                errors.append("Unggah foto tampak depan rumah.")
        elif err:
            errors.append(err)
    if errors:
        for e in errors:
            flash(e, "bad")
        return redirect(url_for("shop") + "#checkout")
    for _ in range(5):
        order_no = "BCS-%s-%04d" % (datetime.now().strftime("%y%m%d"), secrets.randbelow(10000))
        if not db().execute("SELECT 1 FROM orders WHERE order_no=?", (order_no,)).fetchone():
            break
    token = secrets.token_urlsafe(16)
    db().execute(
        "INSERT INTO orders(order_no, token, created_at, member_id, name, wa, address, landmark, map_url,"
        " distance_km, house_file, items_json, subtotal, member_disc, promo_code, promo_disc, free_ship, total)"
        " VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
        (order_no, token, now_str(), g.member["id"] if g.member else None, name, wa, address, landmark, map_url,
         c["dist"], house, json.dumps(c["lines"]), c["sub"], c["member_disc"], c["promo_code"],
         c["promo_disc"], 1 if c["free"] else 0, c["total"]))
    db().commit()
    return redirect(url_for("order_page", order_no=order_no, k=token))


def order_message(o, lines):
    s = S()
    member_no = None
    if o["member_id"]:
        m = db().execute("SELECT member_no FROM members WHERE id=?", (o["member_id"],)).fetchone()
        member_no = m["member_no"] if m else None
    c = {"free": bool(o["free_ship"]), "dist": o["distance_km"],
         "map_status": ("in" if o["distance_km"] is not None and o["distance_km"] <= float(s["radius_km"])
                        else "out" if o["distance_km"] is not None else "unknown")}
    out = ["*ORDER BACUS BANDUNG*", "No. order: " + o["order_no"],
           ("Member: %s" % member_no) if member_no else "Member: bukan member", "", "*Pesanan*"]
    out += ["• %dx %s (%s) = %s" % (l["qty"], l["name"], l["volume"], rp(l["total"])) for l in lines]
    out.append("Subtotal: " + rp(o["subtotal"]))
    if o["member_disc"]:
        out.append("Diskon member %s%%: -%s" % (s["member_disc"], rp(o["member_disc"])))
    if o["promo_disc"]:
        out.append("Kode promo %s: -%s" % (o["promo_code"], rp(o["promo_disc"])))
    out.append("Ongkir: " + ship_text(c))
    out.append(("*Total transfer: %s*" % rp(o["total"])) if o["free_ship"]
               else "*Total: %s + ongkir (menunggu konfirmasi admin)*" % rp(o["total"]))
    out += ["", "*Pengantaran*", "Nama: " + o["name"], "WhatsApp: " + o["wa"], "Alamat: " + o["address"]]
    if o["landmark"]:
        out.append("Patokan: " + o["landmark"])
    out += ["Link peta: " + o["map_url"], "",
            "Foto rumah sudah saya unggah di website." if o["house_file"] else "Foto rumah sudah tersimpan di data member.",
            "Pembayaran: transfer bank. Bukti transfer saya kirim di chat ini.",
            "Saya berusia 21 tahun ke atas."]
    return "\n".join(out)


@app.route("/pesanan/<order_no>")
def order_page(order_no):
    o = db().execute("SELECT * FROM orders WHERE order_no=?", (order_no,)).fetchone()
    if not o or not secrets.compare_digest(request.args.get("k", ""), o["token"]):
        abort(404)
    lines = json.loads(o["items_json"] or "[]")
    return render_template("order.html", o=o, lines=lines, wa=wa_link(S()["wa"], order_message(o, lines)))


# ---------------------------------------------------------------------------
# Member
# ---------------------------------------------------------------------------
@app.route("/member", methods=["GET", "POST"])
def member_home():
    if g.member:
        if request.method == "POST":
            f = request.form
            address, map_url = f.get("alamat", "").strip(), f.get("peta", "").strip()
            if len(address) < 15 or not is_map_link(map_url):
                flash("Isi alamat lengkap dan link Google Maps yang benar.", "bad")
            else:
                db().execute("UPDATE members SET address=?, landmark=?, map_url=? WHERE id=?",
                             (address, f.get("patokan", "").strip(), map_url, g.member["id"]))
                db().commit()
                flash("Alamat tersimpan.", "ok")
            return redirect(url_for("member_home"))
        return render_template("member_account.html", m=g.member)
    return render_template("member_info.html")


@app.route("/member/masuk", methods=["POST"])
def member_login():
    wa, pin = norm_wa(request.form.get("wa")), request.form.get("pin", "")
    key = "m:" + (request.remote_addr or "") + wa
    if blocked(key):
        flash("Terlalu banyak percobaan. Coba lagi 10 menit lagi.", "bad")
        return redirect(url_for("member_home"))
    m = db().execute("SELECT * FROM members WHERE wa=?", (wa,)).fetchone()
    if not m or not check_password_hash(m["pin_hash"], pin):
        record_fail(key)
        flash("Nomor WhatsApp atau PIN salah.", "bad")
    elif m["status"] == "pending":
        flash("Pendaftaranmu masih menunggu verifikasi admin.", "warn")
    elif m["status"] != "aktif":
        flash("Keanggotaan ini tidak aktif. Hubungi admin lewat WhatsApp.", "bad")
    else:
        session.permanent = True
        session["member_id"] = m["id"]
        flash("Selamat datang, %s." % m["name"], "ok")
        return redirect(request.form.get("next") or url_for("shop"))
    return redirect(url_for("member_home"))


@app.route("/member/keluar", methods=["POST"])
def member_logout():
    session.pop("member_id", None)
    return redirect(url_for("shop"))


@app.route("/member/daftar", methods=["GET", "POST"])
def member_register():
    if request.method == "GET":
        return render_template("member_register.html", f={})
    f = request.form
    errors = []
    name, wa = f.get("nama", "").strip(), norm_wa(f.get("wa"))
    address, landmark, map_url = f.get("alamat", "").strip(), f.get("patokan", "").strip(), f.get("peta", "").strip()
    pin, pin2 = f.get("pin", ""), f.get("pin2", "")
    if len(name) < 2:
        errors.append("Isi nama sesuai KTP/SIM.")
    if len(wa) < 10:
        errors.append("Isi nomor WhatsApp yang aktif.")
    if len(address) < 15:
        errors.append("Isi alamat lengkap.")
    if not is_map_link(map_url):
        errors.append("Tempel link Google Maps titik rumahmu.")
    if not re.fullmatch(r"\d{6}", pin):
        errors.append("PIN harus 6 angka.")
    elif pin != pin2:
        errors.append("Ulangi PIN dengan angka yang sama.")
    if not f.get("umur"):
        errors.append("Centang pernyataan usia 21 tahun ke atas.")
    if not f.get("setuju"):
        errors.append("Centang persetujuan penyimpanan foto KTP/SIM.")
    old = db().execute("SELECT * FROM members WHERE wa=?", (wa,)).fetchone() if wa else None
    if old and old["status"] in ("pending", "aktif"):
        errors.append("Nomor WhatsApp ini sudah terdaftar. Masuk di halaman Member atau hubungi admin.")
    ktp = house = None
    if not errors:
        ktp, err = save_photo(request.files.get("ktp"), "ktp")
        if err:
            errors.append("Unggah foto KTP atau SIM." if err == "missing" else err)
        house, err = save_photo(request.files.get("rumah"), "rumah")
        if err:
            errors.append("Unggah foto tampak depan rumah." if err == "missing" else err)
    if errors:
        delete_photo(ktp)
        delete_photo(house)
        for e in errors:
            flash(e, "bad")
        return render_template("member_register.html", f=f)
    if old:  # pernah ditolak/dicabut: pakai baris lama
        delete_photo(old["ktp_file"])
        delete_photo(old["house_file"])
        db().execute("UPDATE members SET name=?, pin_hash=?, address=?, landmark=?, map_url=?, ktp_file=?,"
                     " house_file=?, status='pending', created_at=? WHERE id=?",
                     (name, generate_password_hash(pin), address, landmark, map_url, ktp, house, now_str(), old["id"]))
        mid = old["id"]
    else:
        cur = db().execute("INSERT INTO members(name, wa, pin_hash, address, landmark, map_url, ktp_file,"
                           " house_file, status, created_at) VALUES(?,?,?,?,?,?,?,?, 'pending', ?)",
                           (name, wa, generate_password_hash(pin), address, landmark, map_url, ktp, house, now_str()))
        mid = cur.lastrowid
    db().commit()
    s = S()
    msg = "\n".join(["*DAFTAR MEMBER BACUS BANDUNG*", "ID pendaftaran: D-%04d" % mid, "Nama: " + name,
                     "WhatsApp: " + wa, "",
                     "Foto KTP/SIM dan foto rumah sudah saya unggah di website.",
                     "Biaya member seumur hidup %s sudah/akan saya transfer. Bukti transfer saya kirim di chat ini." % rp(s["member_fee"])])
    return render_template("member_registered.html", mid=mid, wa=wa_link(s["wa"], msg))


# ---------------------------------------------------------------------------
# Back office
# ---------------------------------------------------------------------------
@app.route("/admin/login", methods=["GET", "POST"])
def admin_login():
    if request.method == "POST":
        user, pw = request.form.get("username", "").strip(), request.form.get("password", "")
        key = "a:" + (request.remote_addr or "")
        if blocked(key):
            flash("Terlalu banyak percobaan. Coba lagi 10 menit lagi.", "bad")
        else:
            a = db().execute("SELECT * FROM admins WHERE username=?", (user,)).fetchone()
            if a and check_password_hash(a["pw_hash"], pw):
                session.clear()
                session["admin_id"] = a["id"]
                nxt = request.args.get("next", "")
                return redirect(nxt if nxt.startswith("/admin") else url_for("admin_orders"))
            record_fail(key)
            flash("Username atau password salah.", "bad")
    return render_template("admin_login.html")


@app.route("/admin/logout", methods=["POST"])
def admin_logout():
    session.clear()
    return redirect(url_for("admin_login"))


@app.route("/admin")
@admin_required
def admin_home():
    return redirect(url_for("admin_orders"))


@app.route("/admin/foto/<name>")
@admin_required
def admin_photo(name):
    if not re.fullmatch(r"[a-z]+_[0-9a-f]{32}\.(jpg|png|webp)", name):
        abort(404)
    path = os.path.join(UPLOAD_DIR, name)
    if not os.path.exists(path):
        abort(404)
    resp = send_file(path)
    resp.headers["Cache-Control"] = "private, no-store"
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
    m = db().execute("SELECT * FROM members WHERE id=?", (o["member_id"],)).fetchone() if o["member_id"] else None
    lines = json.loads(o["items_json"] or "[]")
    msgs = {
        "lunas": "Halo %s, transfer untuk pesanan %s sudah kami terima. Pesanan segera disiapkan. Terima kasih! - Bacus Bandung" % (o["name"], o["order_no"]),
        "dikirim": "Halo %s, pesanan %s sedang diantar ke alamatmu. Siapkan KTP untuk ditunjukkan ke kurir ya. - Bacus Bandung" % (o["name"], o["order_no"]),
    }
    wa_msgs = {k: wa_link(o["wa"], v) for k, v in msgs.items()}
    return render_template("admin_order.html", o=o, m=m, lines=lines, wa_msgs=wa_msgs,
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
            db().execute("DELETE FROM products WHERE id=?", (pid,))
            flash("Produk dihapus.", "ok")
        else:
            vals = product_from_form(f)
            if not vals[0] or vals[5] <= 0:
                flash("Produk perlu nama dan harga lebih dari 0.", "bad")
                return redirect(url_for("admin_products", cat=f.get("cat")))
            if action == "tambah":
                db().execute("INSERT INTO products(name, volume, abv, style, cat, price, promo_price, label, active, sort)"
                             " VALUES(?,?,?,?,?,?,?,?,?,?)", vals)
                flash("Produk %s ditambahkan." % vals[0], "ok")
            else:
                db().execute("UPDATE products SET name=?, volume=?, abv=?, style=?, cat=?, price=?, promo_price=?,"
                             " label=?, active=?, sort=? WHERE id=?", (*vals, pid))
                flash("Produk %s disimpan." % vals[0], "ok")
        db().commit()
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


# --- member ---------------------------------------------------------------
@app.route("/admin/member")
@admin_required
def admin_members():
    st = request.args.get("status", "pending")
    q = request.args.get("q", "").strip()
    sql, args = "SELECT * FROM members WHERE 1=1", []
    if st in MEMBER_STATUS:
        sql += " AND status=?"
        args.append(st)
    if q:
        sql += " AND (member_no LIKE ? OR name LIKE ? OR wa LIKE ?)"
        args += ["%" + q + "%"] * 3
    rows = db().execute(sql + " ORDER BY id DESC LIMIT 500", args).fetchall()
    counts = {r["status"]: r["n"] for r in db().execute("SELECT status, COUNT(*) n FROM members GROUP BY status")}
    return render_template("admin_members.html", rows=rows, st=st, q=q, counts=counts, tab="member")


@app.route("/admin/member/<int:mid>", methods=["GET", "POST"])
@admin_required
def admin_member(mid):
    m = db().execute("SELECT * FROM members WHERE id=?", (mid,)).fetchone()
    if not m:
        abort(404)
    if request.method == "POST":
        f = request.form
        action = f.get("action")
        if action == "setujui":
            no = m["member_no"]
            if not no:
                n = db().execute("SELECT COUNT(*) FROM members WHERE member_no IS NOT NULL").fetchone()[0] + 1
                while db().execute("SELECT 1 FROM members WHERE member_no=?", ("BCM-%04d" % n,)).fetchone():
                    n += 1
                no = "BCM-%04d" % n
            db().execute("UPDATE members SET status='aktif', member_no=?, approved_at=? WHERE id=?", (no, now_str(), mid))
            flash("Member disetujui dengan nomor %s. Kabari lewat WhatsApp." % no, "ok")
        elif action == "tolak":
            db().execute("UPDATE members SET status='ditolak' WHERE id=?", (mid,))
            flash("Pendaftaran ditolak.", "ok")
        elif action == "cabut":
            db().execute("UPDATE members SET status='dicabut' WHERE id=?", (mid,))
            flash("Keanggotaan dicabut.", "ok")
        elif action == "aktifkan":
            db().execute("UPDATE members SET status='aktif' WHERE id=?", (mid,))
            flash("Keanggotaan diaktifkan lagi.", "ok")
        elif action == "simpan":
            db().execute("UPDATE members SET name=?, address=?, landmark=?, map_url=?, note=? WHERE id=?",
                         (f.get("nama", m["name"]).strip(), f.get("alamat", "").strip(), f.get("patokan", "").strip(),
                          f.get("peta", "").strip(), f.get("note", "").strip(), mid))
            flash("Data member disimpan.", "ok")
        elif action == "pin":
            pin = f.get("pin", "")
            if re.fullmatch(r"\d{6}", pin):
                db().execute("UPDATE members SET pin_hash=? WHERE id=?", (generate_password_hash(pin), mid))
                flash("PIN baru disimpan. Beri tahu member lewat WhatsApp.", "ok")
            else:
                flash("PIN harus 6 angka.", "bad")
        elif action == "hapus":
            delete_photo(m["ktp_file"])
            delete_photo(m["house_file"])
            db().execute("UPDATE orders SET member_id=NULL WHERE member_id=?", (mid,))
            db().execute("DELETE FROM members WHERE id=?", (mid,))
            db().commit()
            flash("Data member dan fotonya dihapus permanen.", "ok")
            return redirect(url_for("admin_members", status="semua"))
        db().commit()
        return redirect(url_for("admin_member", mid=mid))
    s = S()
    welcome = wa_link(m["wa"], "Halo %s, pendaftaran member Bacus Bandung sudah disetujui. Nomor member: %s. "
                      "Masuk di website lewat menu Member dengan nomor WhatsApp ini dan PIN yang kamu buat. "
                      "Diskon %s%% otomatis di setiap order. Terima kasih!" % (m["name"], m["member_no"] or "-", s["member_disc"]))
    orders = db().execute("SELECT order_no, created_at, total, status, id FROM orders WHERE member_id=? ORDER BY id DESC LIMIT 20",
                          (mid,)).fetchall()
    return render_template("admin_member.html", m=m, welcome=welcome, chat=wa_link(m["wa"], ""), orders=orders, tab="member")


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
        save_setting("wa", wa)
        for k in ("bank_name", "bank_no", "bank_holder"):
            save_setting(k, f.get(k, "").strip())
        save_setting("store_lat", to_float(f.get("store_lat"), DEFAULT_SETTINGS["store_lat"]))
        save_setting("store_lng", to_float(f.get("store_lng"), DEFAULT_SETTINGS["store_lng"]))
        save_setting("radius_km", _num(max(0.0, to_float(f.get("radius_km"), 10))))
        save_setting("free_min", max(0, to_int(f.get("free_min"))))
        save_setting("member_fee", max(0, to_int(f.get("member_fee"))))
        save_setting("member_disc", _num(min(100.0, max(0.0, to_float(f.get("member_disc"), 5)))))
        save_setting("promo_stack", 1 if f.get("promo_stack") else 0)
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
            elif len(f.get("new", "")) < 8 or f.get("new") != f.get("new2"):
                flash("Password baru minimal 8 karakter dan harus diulang dengan sama.", "bad")
            else:
                db().execute("UPDATE admins SET pw_hash=? WHERE id=?", (generate_password_hash(f["new"]), a["id"]))
                db().commit()
                flash("Password diganti.", "ok")
        elif f.get("action") == "tambah":
            user, pw = f.get("username", "").strip(), f.get("password", "")
            if not re.fullmatch(r"[A-Za-z0-9_.-]{3,30}", user) or len(pw) < 8:
                flash("Username 3-30 huruf/angka dan password minimal 8 karakter.", "bad")
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
def _simple_error(e):
    return render_template("error.html", code=e.code, msg=getattr(e, "description", "")), e.code


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
<style>{{ CSS|safe }}</style></head>
<body>
<div class="wrap">
  <div class="nav">
    <a class="brand" href="{{ url_for('shop') }}">BACUS BANDUNG · Bottleshop</a>
    <nav aria-label="Menu">
      {% block nav %}
      <a href="{{ url_for('shop') }}" class="{{ 'on' if request.endpoint == 'shop' }}">Toko</a>
      <a href="{{ url_for('member_home') }}" class="{{ 'on' if request.endpoint and request.endpoint.startswith('member') }}">{{ 'Akun member' if me_member else 'Member' }}</a>
      {% if me_admin %}<a href="{{ url_for('admin_orders') }}">Back office</a>{% endif %}
      <span class="age">21+</span>
      {% endblock %}
    </nav>
  </div>
  {% with msgs = get_flashed_messages(with_categories=true) %}{% if msgs %}
  <div class="flash" role="status">{% for c, m in msgs %}<p class="{{ c }}">{{ m }}</p>{% endfor %}</div>
  {% endif %}{% endwith %}
  {% block body %}{% endblock %}
</div>
{% block after %}{% endblock %}
</body></html>"""

T["shop.html"] = r"""{% extends "base.html" %}
{% block body %}
<header class="hero">
  <h1>Bir dingin, <span>diantar</span> ke rumah.</h1>
  <p>Beer, anggur, wine, whisky, sampai minuman tradisional. Pilih di sini, kirim order ke WhatsApp toko, transfer, lalu kami antar ke titik lokasimu.</p>
  <ul class="chips">
    <li>Free ongkir radius {{ S.radius_km }} km{% if S.free_min %}, min. belanja {{ S.free_min|rp }}{% endif %}</li>
    <li>Bayar via transfer</li>
    <li>Member diskon {{ S.member_disc }}%</li>
  </ul>
</header>
{% if S.banner %}<div class="banner">{{ S.banner }}</div>{% endif %}

<section aria-labelledby="h-cara">
  <div class="sec-head"><h2 id="h-cara">Cara order</h2></div>
  <ol class="steps">
    <li><b>Pilih minuman</b><span>Masukkan ke keranjang.</span></li>
    <li><b>Isi data antar</b><span>Alamat, link peta, dan foto rumah. Member tinggal pakai alamat tersimpan.</span></li>
    <li><b>Kirim ke WhatsApp</b><span>Pesanan tersimpan, lalu WhatsApp toko terbuka dengan pesan terisi.</span></li>
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
  <form class="two" method="post" action="{{ url_for('checkout') }}" enctype="multipart/form-data" id="co-form" novalidate>
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
      {% if not me_member %}<p class="note" id="upsell" hidden></p>{% endif %}
      <div class="box">
        <span class="hint">Transfer ke rekening toko</span>
        <span><b>{{ S.bank_name }}</b> · a.n. {{ S.bank_holder }}</span>
        <div class="row"><span class="mono no" id="bank-no">{{ S.bank_no }}</span><button type="button" class="mini" data-copy="{{ S.bank_no|replace(' ', '') }}">Salin</button></div>
        <span class="hint">Pesanan dikirim setelah admin WhatsApp memverifikasi transfer.</span>
      </div>
    </div>
    <div class="panel">
      <h3>Data pengantaran</h3>
      {% if me_member %}<p class="status ok">Member {{ me_member.member_no }}: diskon {{ S.member_disc }}% terpasang dan alamat tersimpan dipakai.</p>{% endif %}
      <div class="f"><label for="nama">Nama penerima</label><input type="text" name="nama" id="nama" autocomplete="name" value="{{ me_member.name if me_member }}"></div>
      <div class="f"><label for="wa">Nomor WhatsApp</label><input type="tel" name="wa" id="wa" inputmode="tel" placeholder="08xxxxxxxxxx" autocomplete="tel" value="{{ me_member.wa if me_member }}"></div>
      <div class="f"><label for="alamat">Alamat lengkap</label><textarea name="alamat" id="alamat" placeholder="Jalan, nomor rumah, RT/RW, kelurahan, kecamatan">{{ me_member.address if me_member }}</textarea></div>
      <div class="f"><label for="patokan">Patokan <span class="hint">(opsional)</span></label><input type="text" name="patokan" id="patokan" placeholder="Contoh: pagar hitam, sebelah minimarket" value="{{ me_member.landmark if me_member and me_member.landmark }}"></div>
      <div class="f">
        <label for="peta">Link Google Maps titik rumah</label>
        <input type="url" name="peta" id="peta" inputmode="url" placeholder="https://maps.app.goo.gl/..." value="{{ me_member.map_url if me_member }}">
        <span class="hint">Buka Google Maps, tekan lama tepat di rumahmu, pilih Bagikan, lalu tempel link di sini.</span>
        <span class="status" id="peta-status" role="status"></span>
      </div>
      {% if not me_member %}
      <div class="f">
        <label for="foto">Foto tampak depan rumah</label>
        <input type="file" name="foto" id="foto" accept="image/jpeg,image/png,image/webp">
        <span class="hint">Foto disimpan bersama pesanan dan hanya bisa dilihat admin.</span>
      </div>
      {% endif %}
      <label class="check" for="umur"><input type="checkbox" name="umur" id="umur" value="1"><span>Saya berusia 21 tahun ke atas dan siap menunjukkan KTP saat pesanan diterima.</span></label>
      <button type="submit" class="wa" id="co-btn">Simpan pesanan &amp; lanjut ke WhatsApp</button>
      <span class="hint">Setelah pesanan tersimpan, tombol WhatsApp berisi pesan order muncul di halaman berikutnya.</span>
    </div>
  </form>
</section>
<p class="legal">Minuman beralkohol hanya untuk usia 21+. Jangan mengemudi setelah minum. Free ongkir berlaku sampai {{ S.radius_km }} km dari toko{% if S.free_min %} untuk belanja minimal {{ S.free_min|rp }} (dihitung dari subtotal barang sebelum diskon){% endif %}. Di luar ketentuan itu, admin akan mengonfirmasi dulu pengiriman dan ongkirnya.</p>
{% endblock %}
{% block after %}
<div class="bar"><div class="in">
  <div><b id="bar-count">Keranjang kosong</b><small class="mono" id="bar-total">Rp 0</small></div>
  <a href="#checkout">Checkout</a>
</div></div>
<script>
const P = {{ pdata|tojson }};
const CSRF = {{ csrf_token()|tojson }};
const IS_MEMBER = {{ 'true' if me_member else 'false' }};
const MEMBER_DISC = {{ S.member_disc|tojson }};
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
    c.querySelector(".ctl").innerHTML = q ? stepper(id, q, P[id].n) : `<button type="button" class="add" data-inc="${id}">Tambah</button>`;
  });
  const ids = Object.keys(cart);
  $("lines").innerHTML = ids.length ? ids.map(id => `<li><span class="nm"><b>${esc(P[id].n)}</b><br><span class="vol mono">${cart[id]} × ${rp(P[id].p)}</span></span>${stepper(id, cart[id], P[id].n)}</li>`).join("")
    : `<li class="empty">Belum ada minuman di keranjang. Pilih dulu di katalog.</li>`;
  let count = 0, sub = 0;
  ids.forEach(id => { count += cart[id]; sub += cart[id] * P[id].p; });
  $("bar-count").textContent = count ? count + " item di keranjang" : "Keranjang kosong";
  $("bar-total").textContent = rp(sub);
  $("items").value = JSON.stringify(cart);
  const up = $("upsell");
  if (up){ up.hidden = !sub; up.innerHTML = `Member hemat ${rp(sub * MEMBER_DISC / 100)} di order ini. <a href="{{ url_for('member_home') }}">Daftar member</a>`; }
  quoteSoon();
}
function quoteSoon(){ clearTimeout(timer); timer = setTimeout(quote, 350); }
async function quote(){
  try {
    const r = await fetch("{{ url_for('api_hitung') }}", {method: "POST", headers: {"Content-Type": "application/json", "X-CSRF": CSRF},
      body: JSON.stringify({items: cart, kode: code, peta: $("peta").value})});
    if (!r.ok) return;
    const c = await r.json();
    const ship = c.free ? "GRATIS" : (c.map_status === "none" || c.map_status === "invalid") ? "—" : "Dicek admin";
    $("tot").innerHTML = `<div><span>Subtotal</span><span>${c.sub_t}</span></div>`
      + (c.member_disc ? `<div class="disc"><span>Diskon member</span><span>− ${c.member_disc_t}</span></div>` : "")
      + (c.promo_disc ? `<div class="disc"><span>Kode ${esc(c.promo_code)}</span><span>− ${c.promo_disc_t}</span></div>` : "")
      + `<div><span>Ongkir</span><span>${ship}</span></div>`
      + (c.short > 0 && c.count ? `<div class="disc"><span>Tambah ${c.short_t} lagi untuk free ongkir</span><span></span></div>` : "")
      + `<div class="grand"><span>Total transfer</span><span>${c.total_t}${(!c.free && ship !== "—") ? " + ongkir" : ""}</span></div>`;
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
$("co-form").addEventListener("submit", () => { $("items").value = JSON.stringify(cart); $("co-btn").disabled = true; $("co-btn").textContent = "Menyimpan..."; });
window.addEventListener("pageshow", () => { $("co-btn").disabled = false; $("co-btn").textContent = "Simpan pesanan & lanjut ke WhatsApp"; });
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
      {% if o.member_disc %}<div class="disc"><span>Diskon member</span><span>− {{ o.member_disc|rp }}</span></div>{% endif %}
      {% if o.promo_disc %}<div class="disc"><span>Kode {{ o.promo_code }}</span><span>− {{ o.promo_disc|rp }}</span></div>{% endif %}
      <div><span>Ongkir</span><span>{{ 'GRATIS' if o.free_ship else 'Dicek admin' }}</span></div>
      <div class="grand"><span>Total transfer</span><span>{{ o.total|rp }}{{ '' if o.free_ship else ' + ongkir' }}</span></div>
    </div>
  </div>
  <div class="panel">
    <h3>Langkah berikutnya</h3>
    <ol class="stack" style="margin:0;padding-left:20px">
      <li>Tekan tombol di bawah. WhatsApp toko terbuka dengan pesan order yang sudah terisi, lalu tekan kirim.</li>
      <li>{% if o.free_ship %}Transfer <b>{{ o.total|rp }}</b>{% else %}Tunggu admin mengonfirmasi ongkir, lalu transfer totalnya{% endif %} ke rekening di bawah.</li>
      <li>Kirim foto bukti transfer di chat yang sama. Pesanan diantar setelah admin memverifikasi transfer.</li>
    </ol>
    <a class="wa" href="{{ wa }}" target="_blank" rel="noopener">Kirim order ke WhatsApp</a>
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
<script>
try { localStorage.removeItem("bacus-cart"); } catch (e) {}
document.addEventListener("click", e => {
  const t = e.target.closest("[data-copy]"); if (!t) return;
  try { navigator.clipboard.writeText(t.dataset.copy).then(() => { t.textContent = "Tersalin"; setTimeout(() => t.textContent = "Salin", 1500); }, () => {}); } catch (err) {}
});
</script>
{% endblock %}"""

T["member_info.html"] = r"""{% extends "base.html" %}
{% block title %}Member · Bacus Bandung{% endblock %}
{% block body %}
<header class="mhero">
  <h1>Member Bacus. <b>{{ S.member_fee|rp }}</b> sekali, seumur hidup.</h1>
  <ul>
    <li>Diskon {{ S.member_disc }}% di setiap pembelian.</li>
    <li>Alamat, link peta, dan patokan tersimpan. Order berikutnya tinggal pilih minuman.</li>
    <li>Tidak perlu unggah foto rumah lagi di setiap order.</li>
  </ul>
</header>
<div class="two">
  <form class="panel" method="post" action="{{ url_for('member_login') }}">
    {{ csrf() }}
    <h3>Masuk member</h3>
    <div class="f"><label for="m-wa">Nomor WhatsApp</label><input type="tel" name="wa" id="m-wa" inputmode="tel" autocomplete="tel" placeholder="08xxxxxxxxxx"></div>
    <div class="f"><label for="m-pin">PIN 6 angka</label><input type="password" name="pin" id="m-pin" inputmode="numeric" maxlength="6" autocomplete="current-password"></div>
    <button class="solid" type="submit">Masuk</button>
    <p class="hint">Lupa PIN? Hubungi admin lewat WhatsApp untuk dibuatkan PIN baru.</p>
  </form>
  <div class="panel">
    <h3>Belum jadi member?</h3>
    <p>Siapkan foto KTP atau SIM dan foto tampak depan rumah. Setelah daftar, transfer biaya {{ S.member_fee|rp }} dan kirim buktinya lewat WhatsApp. Admin memverifikasi lalu mengaktifkan akunmu.</p>
    <a class="solid" href="{{ url_for('member_register') }}">Daftar member</a>
  </div>
</div>
{% endblock %}"""

T["member_register.html"] = r"""{% extends "base.html" %}
{% block title %}Daftar member · Bacus Bandung{% endblock %}
{% block body %}
<div class="two">
  <div class="stack">
    <h2>Daftar member</h2>
    <p>Biaya {{ S.member_fee|rp }} sekali, berlaku seumur hidup. Diskon {{ S.member_disc }}% di setiap pembelian.</p>
    <div class="box">
      <span class="hint">Foto KTP/SIM dan foto rumah dipakai hanya untuk verifikasi member dan pengantaran. Foto disimpan di server toko dan hanya bisa dibuka admin.</span>
    </div>
  </div>
  <form class="panel" method="post" enctype="multipart/form-data" novalidate>
    {{ csrf() }}
    <div class="f"><label for="r-nama">Nama sesuai KTP/SIM</label><input type="text" name="nama" id="r-nama" autocomplete="name" value="{{ f.get('nama', '') }}"></div>
    <div class="f"><label for="r-wa">Nomor WhatsApp</label><input type="tel" name="wa" id="r-wa" inputmode="tel" placeholder="08xxxxxxxxxx" value="{{ f.get('wa', '') }}"></div>
    <div class="f"><label for="r-alamat">Alamat lengkap</label><textarea name="alamat" id="r-alamat">{{ f.get('alamat', '') }}</textarea></div>
    <div class="f"><label for="r-patokan">Patokan <span class="hint">(opsional)</span></label><input type="text" name="patokan" id="r-patokan" value="{{ f.get('patokan', '') }}"></div>
    <div class="f"><label for="r-peta">Link Google Maps titik rumah</label><input type="url" name="peta" id="r-peta" placeholder="https://maps.app.goo.gl/..." value="{{ f.get('peta', '') }}"></div>
    <div class="f"><label for="r-ktp">Foto KTP atau SIM</label><input type="file" name="ktp" id="r-ktp" accept="image/jpeg,image/png,image/webp"></div>
    <div class="f"><label for="r-rumah">Foto tampak depan rumah</label><input type="file" name="rumah" id="r-rumah" accept="image/jpeg,image/png,image/webp"></div>
    <div class="f"><label for="r-pin">Buat PIN 6 angka</label><input type="password" name="pin" id="r-pin" inputmode="numeric" maxlength="6" autocomplete="new-password"></div>
    <div class="f"><label for="r-pin2">Ulangi PIN</label><input type="password" name="pin2" id="r-pin2" inputmode="numeric" maxlength="6" autocomplete="new-password"></div>
    <label class="check" for="r-umur"><input type="checkbox" name="umur" id="r-umur" value="1"><span>Saya berusia 21 tahun ke atas.</span></label>
    <label class="check" for="r-setuju"><input type="checkbox" name="setuju" id="r-setuju" value="1"><span>Saya setuju foto KTP/SIM dan foto rumah disimpan toko untuk verifikasi member.</span></label>
    <button class="solid" type="submit">Kirim pendaftaran</button>
  </form>
</div>
{% endblock %}"""

T["member_registered.html"] = r"""{% extends "base.html" %}
{% block body %}
<div class="panel" style="max-width:640px">
  <h2>Pendaftaran terkirim</h2>
  <p>ID pendaftaran <b class="mono">D-{{ '%04d' % mid }}</b>. Langkah terakhir:</p>
  <ol style="margin:0;padding-left:20px">
    <li>Transfer biaya member <b>{{ S.member_fee|rp }}</b> ke {{ S.bank_name }} <span class="mono">{{ S.bank_no }}</span> a.n. {{ S.bank_holder }}.</li>
    <li>Tekan tombol di bawah dan kirim bukti transfer di chat WhatsApp.</li>
    <li>Setelah admin memverifikasi, kamu bisa masuk di menu Member dengan nomor WhatsApp dan PIN.</li>
  </ol>
  <a class="wa" href="{{ wa }}" target="_blank" rel="noopener">Kirim konfirmasi ke WhatsApp</a>
</div>
{% endblock %}"""

T["member_account.html"] = r"""{% extends "base.html" %}
{% block title %}Akun member · Bacus Bandung{% endblock %}
{% block body %}
<div class="two">
  <div class="stack">
    <div class="mcard">
      <span>Kartu member</span>
      <span class="num">{{ m.member_no }}</span>
      <b>{{ m.name }}</b>
      <span>Diskon {{ S.member_disc }}% otomatis di setiap order.</span>
    </div>
    <a class="solid" href="{{ url_for('shop') }}">Belanja sekarang</a>
    <form method="post" action="{{ url_for('member_logout') }}">{{ csrf() }}<button class="mini danger" type="submit">Keluar</button></form>
  </div>
  <form class="panel" method="post">
    {{ csrf() }}
    <h3>Alamat tersimpan</h3>
    <div class="f"><label for="p-alamat">Alamat lengkap</label><textarea name="alamat" id="p-alamat">{{ m.address or '' }}</textarea></div>
    <div class="f"><label for="p-patokan">Patokan</label><input type="text" name="patokan" id="p-patokan" value="{{ m.landmark or '' }}"></div>
    <div class="f"><label for="p-peta">Link Google Maps</label><input type="url" name="peta" id="p-peta" value="{{ m.map_url or '' }}"></div>
    <button class="solid" type="submit">Simpan alamat</button>
    <p class="hint">Kalau pindah rumah, kirim foto rumah yang baru ke admin lewat WhatsApp.</p>
  </form>
</div>
{% endblock %}"""

T["error.html"] = r"""{% extends "base.html" %}
{% block body %}
<div class="panel" style="max-width:560px"><h2>{{ 'Halaman tidak ditemukan' if code == 404 else 'Permintaan tidak bisa diproses' }}</h2>
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
  {% for k, l, ep in [('pesanan','Pesanan','admin_orders'),('produk','Produk & harga','admin_products'),('promo','Promo','admin_promos'),('member','Member','admin_members'),('pengaturan','Pengaturan','admin_settings'),('akun','Akun admin','admin_account')] %}
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
      <td>{{ o.name }}{% if o.member_id %} <span class="badge b-aktif">member</span>{% endif %}<br><span class="hint">{{ o.wa }}</span></td>
      <td class="num">{{ o.total|rp }}</td><td>{{ 'Gratis' if o.free_ship else 'Cek' }} · {{ o.distance_km|km }} km</td>
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
      {% if o.member_disc %}<div class="disc"><span>Diskon member</span><span>− {{ o.member_disc|rp }}</span></div>{% endif %}
      {% if o.promo_disc %}<div class="disc"><span>Kode {{ o.promo_code }}</span><span>− {{ o.promo_disc|rp }}</span></div>{% endif %}
      <div><span>Ongkir</span><span>{{ 'GRATIS' if o.free_ship else 'Perlu dikonfirmasi' }}</span></div>
      <div class="grand"><span>Total</span><span>{{ o.total|rp }}{{ '' if o.free_ship else ' + ongkir' }}</span></div>
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
      <dt>Member</dt><dd>{% if m %}<a href="{{ url_for('admin_member', mid=m.id) }}">{{ m.member_no }}</a>{% else %}Bukan member{% endif %}</dd>
      <dt>Alamat</dt><dd>{{ o.address }}</dd>
      {% if o.landmark %}<dt>Patokan</dt><dd>{{ o.landmark }}</dd>{% endif %}
      <dt>Peta</dt><dd><a href="{{ o.map_url }}" target="_blank" rel="noopener noreferrer">Buka Google Maps</a></dd>
      <dt>Jarak</dt><dd>{{ o.distance_km|km }} km (garis lurus)</dd>
    </dl>
    <div class="photos">
      {% set house = o.house_file or (m.house_file if m) %}
      {% if house %}<a href="{{ url_for('admin_photo', name=house) }}" target="_blank"><img src="{{ url_for('admin_photo', name=house) }}" alt="Foto rumah pembeli">Foto rumah{{ ' (data member)' if not o.house_file }}</a>{% else %}<p class="empty">Tidak ada foto rumah.</p>{% endif %}
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
  <form method="post" class="arow" style="border:0;padding:0;margin-top:12px">{{ csrf() }}<input type="hidden" name="action" value="tambah">{{ fields(None) }}<button class="solid" type="submit">Tambah</button></form>
</details>
{% for p in rows %}
<form method="post" class="arow">
  {{ csrf() }}<input type="hidden" name="id" value="{{ p.id }}">
  {{ fields(p) }}
  <div class="inline"><button class="mini" type="submit" name="action" value="simpan">Simpan</button>
  <button class="mini danger" type="submit" name="action" value="hapus" onclick="return confirm('Hapus produk {{ p.name|e }}?')">Hapus</button></div>
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
    <button class="mini danger" type="submit" name="action" value="hapus" onclick="return confirm('Hapus kode {{ p.code|e }}?')">Hapus</button></div></form>
  {% else %}<p class="empty">Belum ada kode promo.</p>{% endfor %}
</div>
{% endblock %}"""

T["admin_members.html"] = r"""{% extends "admin_base.html" %}
{% block admin %}
<div class="row">
  <div class="filters" style="margin:0">
    {% for k, l in MEMBER_STATUS.items() %}<a class="pill {{ 'on' if st == k }}" href="{{ url_for('admin_members', status=k) }}">{{ l }} ({{ counts.get(k, 0) }})</a>{% endfor %}
    <a class="pill {{ 'on' if st == 'semua' }}" href="{{ url_for('admin_members', status='semua') }}">Semua</a>
  </div>
  <form method="get" class="inline"><input type="hidden" name="status" value="{{ st }}"><input type="search" name="q" value="{{ q }}" placeholder="Cari no. member, nama, WA" aria-label="Cari member"><button class="mini" type="submit">Cari</button></form>
</div>
<div class="tbl"><table>
  <thead><tr><th>No. member</th><th>Nama</th><th>WhatsApp</th><th>Daftar</th><th>Status</th></tr></thead>
  <tbody>
  {% for m in rows %}
    <tr><td class="mono"><a href="{{ url_for('admin_member', mid=m.id) }}">{{ m.member_no or ('D-%04d' % m.id) }}</a></td><td>{{ m.name }}</td><td>{{ m.wa }}</td><td>{{ m.created_at }}</td>
      <td><span class="badge b-{{ m.status }}">{{ MEMBER_STATUS[m.status] }}</span></td></tr>
  {% else %}
    <tr><td colspan="5" class="empty">Tidak ada member di daftar ini.</td></tr>
  {% endfor %}
  </tbody></table></div>
{% endblock %}"""

T["admin_member.html"] = r"""{% extends "admin_base.html" %}
{% block admin %}
<a class="mini" href="{{ url_for('admin_members', status='semua') }}">← Semua member</a>
<div class="two">
  <div class="panel">
    <h2>{{ m.name }}</h2>
    <p><span class="badge b-{{ m.status }}">{{ MEMBER_STATUS[m.status] }}</span> · <span class="mono">{{ m.member_no or ('D-%04d' % m.id) }}</span> · daftar {{ m.created_at }}</p>
    <div class="photos">
      {% if m.ktp_file %}<a href="{{ url_for('admin_photo', name=m.ktp_file) }}" target="_blank"><img src="{{ url_for('admin_photo', name=m.ktp_file) }}" alt="Foto KTP atau SIM">KTP/SIM</a>{% endif %}
      {% if m.house_file %}<a href="{{ url_for('admin_photo', name=m.house_file) }}" target="_blank"><img src="{{ url_for('admin_photo', name=m.house_file) }}" alt="Foto rumah">Rumah</a>{% endif %}
    </div>
    <form method="post" class="inline" style="flex-wrap:wrap">{{ csrf() }}
      {% if m.status == 'pending' %}
        <button class="solid" name="action" value="setujui">Setujui (biaya sudah diterima)</button>
        <button class="mini danger" name="action" value="tolak">Tolak</button>
      {% elif m.status == 'aktif' %}
        <button class="mini danger" name="action" value="cabut">Cabut keanggotaan</button>
      {% else %}
        <button class="mini" name="action" value="aktifkan">Aktifkan lagi</button>
      {% endif %}
    </form>
    {% if m.status == 'aktif' %}<a class="wa" href="{{ welcome }}" target="_blank" rel="noopener">Kirim kabar diterima ke WhatsApp</a>{% endif %}
    <a class="mini" href="{{ chat }}" target="_blank" rel="noopener">Chat {{ m.wa }}</a>
    <h3>Riwayat order</h3>
    <ul class="lines">{% for o in orders %}<li><a class="mono" href="{{ url_for('admin_order', oid=o.id) }}">{{ o.order_no }}</a><span class="mono">{{ o.total|rp }}</span><span class="badge b-{{ o.status }}">{{ ORDER_STATUS_D[o.status] }}</span></li>{% else %}<li class="empty">Belum ada order.</li>{% endfor %}</ul>
  </div>
  <div class="stack">
    <form class="panel" method="post">{{ csrf() }}<input type="hidden" name="action" value="simpan">
      <h3>Data member</h3>
      <div class="f"><label for="nama">Nama</label><input type="text" name="nama" id="nama" value="{{ m.name }}"></div>
      <div class="f"><label for="alamat">Alamat</label><textarea name="alamat" id="alamat">{{ m.address or '' }}</textarea></div>
      <div class="f"><label for="patokan">Patokan</label><input type="text" name="patokan" id="patokan" value="{{ m.landmark or '' }}"></div>
      <div class="f"><label for="peta">Link Google Maps</label><input type="url" name="peta" id="peta" value="{{ m.map_url or '' }}">{% if m.map_url %}<a class="hint" href="{{ m.map_url }}" target="_blank" rel="noopener noreferrer">Buka peta</a>{% endif %}</div>
      <div class="f"><label for="note">Catatan admin</label><textarea name="note" id="note">{{ m.note or '' }}</textarea></div>
      <button class="solid" type="submit">Simpan</button>
    </form>
    <form class="panel" method="post">{{ csrf() }}<input type="hidden" name="action" value="pin">
      <h3>Buat PIN baru</h3>
      <div class="inline"><input type="text" name="pin" inputmode="numeric" maxlength="6" placeholder="6 angka" aria-label="PIN baru"><button class="mini" type="submit">Simpan PIN</button></div>
    </form>
    <form class="panel" method="post" onsubmit="return confirm('Hapus permanen data dan foto member ini?')">{{ csrf() }}<input type="hidden" name="action" value="hapus">
      <h3>Hapus data</h3><p class="hint">Menghapus data member beserta foto KTP/SIM dan foto rumah secara permanen. Riwayat order tetap ada.</p>
      <button class="mini danger" type="submit">Hapus permanen</button>
    </form>
  </div>
</div>
{% endblock %}"""

T["admin_settings.html"] = r"""{% extends "admin_base.html" %}
{% block admin %}
<form method="post" class="stack">{{ csrf() }}
  <div class="panel"><h3>WhatsApp dan rekening</h3><div class="arow" style="border:0;padding:0">
    <label class="af wide">Nomor WhatsApp toko<input type="tel" name="wa" value="{{ S.wa }}"></label>
    <label class="af">Bank<input type="text" name="bank_name" value="{{ S.bank_name }}"></label>
    <label class="af">Nomor rekening<input type="text" name="bank_no" value="{{ S.bank_no }}"></label>
    <label class="af">Atas nama<input type="text" name="bank_holder" value="{{ S.bank_holder }}"></label>
  </div></div>
  <div class="panel"><h3>Free ongkir</h3><div class="arow" style="border:0;padding:0">
    <label class="af">Radius (km)<input type="number" step="0.5" min="0" name="radius_km" value="{{ S.radius_km }}"></label>
    <label class="af">Minimal belanja (Rp)<input type="number" step="1000" min="0" name="free_min" value="{{ S.free_min }}"></label>
    <label class="af">Latitude toko<input type="text" name="store_lat" value="{{ S.store_lat }}"></label>
    <label class="af">Longitude toko<input type="text" name="store_lng" value="{{ S.store_lng }}"></label>
  </div><p class="hint">Jarak dihitung garis lurus dari titik toko. Minimal belanja dihitung dari subtotal barang sebelum diskon.</p></div>
  <div class="panel"><h3>Member</h3><div class="arow" style="border:0;padding:0">
    <label class="af">Diskon member (%)<input type="number" step="0.5" min="0" max="100" name="member_disc" value="{{ S.member_disc }}"></label>
    <label class="af">Biaya daftar seumur hidup (Rp)<input type="number" step="1000" min="0" name="member_fee" value="{{ S.member_fee }}"></label>
    <label class="af chk"><input type="checkbox" name="promo_stack" value="1" {{ 'checked' if S.promo_stack }}>Kode promo boleh digabung dengan diskon member</label>
  </div></div>
  <button class="solid" type="submit">Simpan pengaturan</button>
</form>
{% endblock %}"""

T["admin_account.html"] = r"""{% extends "admin_base.html" %}
{% block admin %}
<div class="two">
  <form class="panel" method="post">{{ csrf() }}<input type="hidden" name="action" value="password">
    <h3>Ganti password</h3>
    <div class="f"><label for="old">Password lama</label><input type="password" name="old" id="old" autocomplete="current-password"></div>
    <div class="f"><label for="new">Password baru (min. 8 karakter)</label><input type="password" name="new" id="new" autocomplete="new-password"></div>
    <div class="f"><label for="new2">Ulangi password baru</label><input type="password" name="new2" id="new2" autocomplete="new-password"></div>
    <button class="solid" type="submit">Ganti password</button>
  </form>
  <div class="stack">
    <form class="panel" method="post">{{ csrf() }}<input type="hidden" name="action" value="tambah">
      <h3>Tambah admin</h3>
      <div class="f"><label for="nu">Username</label><input type="text" name="username" id="nu" autocomplete="off"></div>
      <div class="f"><label for="np">Password (min. 8 karakter)</label><input type="password" name="password" id="np" autocomplete="new-password"></div>
      <button class="solid" type="submit">Tambah</button>
    </form>
    <div class="panel"><h3>Daftar admin</h3>
      {% for a in admins %}<form method="post" class="row">{{ csrf() }}<input type="hidden" name="action" value="hapus"><input type="hidden" name="id" value="{{ a.id }}">
        <span>{{ a.username }}{{ ' (kamu)' if a.id == me_admin.id }}</span>{% if a.id != me_admin.id %}<button class="mini danger" type="submit" onclick="return confirm('Hapus admin {{ a.username|e }}?')">Hapus</button>{% endif %}</form>{% endfor %}
    </div>
  </div>
</div>
{% endblock %}"""

app.jinja_loader = DictLoader(T)

# Siapkan database saat file dimuat (juga saat dijalankan lewat gunicorn)
_created_admin = init_db()
if _created_admin:
    print("=" * 60)
    print(" Akun admin pertama dibuat. CATAT dan segera ganti passwordnya:")
    print("   username:", _created_admin[0])
    print("   password:", _created_admin[1])
    print("=" * 60, flush=True)


if __name__ == "__main__":
    port = int(os.environ.get("PORT", "8000"))
    print(" Toko:        http://localhost:%d" % port)
    print(" Back office: http://localhost:%d/admin" % port, flush=True)
    app.run(host=os.environ.get("HOST", "0.0.0.0"), port=port, debug=False)
