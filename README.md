# Bacus Bandung - siap deploy (Railway)

## 1. Siapkan rahasia (di komputer kamu, sekali saja)
```
python -c "import secrets;print(secrets.token_hex(32))"
python -c "from cryptography.fernet import Fernet;print(Fernet.generate_key().decode())"
```
Hasil pertama untuk `BACUS_SECRET_KEY`, kedua untuk `BACUS_PHOTO_KEY`.
Simpan keduanya di password manager. **Kalau BACUS_PHOTO_KEY hilang, foto KTP/rumah tidak bisa dibuka lagi.**

## 2. Railway
1. Push folder ini ke GitHub (file `.env` dan `bacus_data/` sudah di-ignore).
2. Service > **Settings > Volumes**: buat Volume, mount path `/data`.
3. Service > **Variables**, isi (lihat `.env.example`):
   `BACUS_DATA=/data`, `BACUS_HTTPS=1`, `BACUS_SECRET_KEY`, `BACUS_PHOTO_KEY`,
   `BACUS_ADMIN_USER`, `BACUS_ADMIN_PASSWORD` (min. 12 karakter), `BACUS_ADMIN_WA`.
4. Deploy. Setelah bisa login di `/admin`, **hapus `BACUS_ADMIN_PASSWORD`** dari Variables.
5. Lupa password admin: isi `BACUS_ADMIN_USER`, `BACUS_ADMIN_PASSWORD` baru dan `BACUS_ADMIN_RESET=1`,
   deploy, login, lalu hapus ketiga-tiganya (kecuali USER boleh tetap).

Aplikasi sengaja **menolak start** kalau secret key atau akun admin belum diatur.

## 3. Yang sudah dikunci
- Password admin/PIN member disimpan sebagai hash; tidak pernah dikirim ke browser atau dicetak di log.
- Login admin: maks. 5 salah per 15 menit per IP+username; sesi habis setelah 4 jam tidak aktif;
  ganti password otomatis mengeluarkan sesi lain.
- Cookie `__Host-` + Secure + HttpOnly + SameSite; CSRF di semua POST; HTTPS dipaksa + HSTS.
- CSP ketat (tanpa inline script tak bertanda), anti-iframe, no-store untuk halaman sensitif.
- Foto KTP/rumah dienkripsi di disk (Fernet) dan hanya bisa dibuka admin yang login.
- Error server tidak menampilkan detail; access log gunicorn dimatikan (URL pesanan memuat token).
- Batas laju untuk checkout, cek pesanan, daftar member, dan hitung ongkir.

## 4. Backup
Volume `/data` berisi `bacus.db` dan `foto/`. Backup rutin, dan simpan `BACUS_PHOTO_KEY` terpisah dari backup.

## 5. Ongkir dan foto rumah
- Di dalam radius: free ongkir (jika belanja mencapai minimum).
- Di luar radius: ongkir otomatis = selisih jarak dari batas radius, **dibulatkan ke atas** (minimal 1 km), dikali tarif per km.
  Contoh radius 5 km, tarif Rp3.000: 5,5 km = Rp3.000; 7,2 km = 3 km = Rp9.000.
  Radius, minimum belanja, dan tarif per km diatur di **Back office > Pengaturan**.
- Foto rumah: di halaman pesanan muncul tombol **Kirim pesanan + foto rumah ke WhatsApp** (HP). WhatsApp terbuka dengan foto
  dan detail order terlampir; pembeli memilih chat admin lalu menekan Kirim. Di komputer, pembeli mengirim detail lewat
  tombol hijau dan melampirkan foto manual. Pesan juga memuat link ke back office (butuh login admin) untuk melihat foto.
- Fitur member dihapus dari tampilan dan rute. Tabel lama di database dibiarkan (tidak dihapus), jadi data lama aman.

## 6. Back office tersembunyi, jam buka, tanpa Cek pesanan
- Tidak ada tautan ke back office di situs. Buka langsung `https://domainmu/admin`. Halaman admin lain mengembalikan 404
  bagi orang yang belum login.
- Menu Cek pesanan dihapus. Status dan konfirmasi pesanan ditangani lewat chat WhatsApp admin.
- **Pengaturan > Jam buka toko**: isi jam buka dan jam tutup (WIB), centang *Aktifkan jam buka otomatis*.
  Di luar jam itu katalog tetap bisa dilihat, tetapi tombol Tambah dan kirim pesanan nonaktif, dan server menolak checkout.
  Ada juga kotak *Tutup sekarang* untuk menutup manual. Zona waktu bisa diganti lewat variable `BACUS_TZ` (default Asia/Jakarta).
- Waktu pesanan kini dicatat dalam WIB (sebelumnya mengikuti jam server).
