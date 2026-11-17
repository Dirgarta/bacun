import os
import gunicorn

# Samarkan versi server di header "Server"
gunicorn.SERVER = "web"

bind = "0.0.0.0:" + os.environ.get("PORT", "8000")
# 1 worker: pembatas laju login ada di memori dan SQLite menulis ke satu file.
workers = 1
threads = 4
timeout = 60
limit_request_line = 4094
limit_request_fields = 50
limit_request_field_size = 8190
# Access log DIMATIKAN: URL pesanan memuat token rahasia (?k=...), jangan tulis ke log.
accesslog = None
errorlog = "-"
loglevel = "warning"
forwarded_allow_ips = "*"   # Railway: proxy tepercaya mengisi X-Forwarded-*
