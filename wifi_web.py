"""
WiFi Analyzer - web service
===========================

Espone tutta l'interfaccia di wifi_analyzer.py su una porta HTTP, cosi' il
sistema si controlla da un browser: scansione live, salvataggio CSV, playback,
notifiche Teams, grafico e tabella.

Avvio (vedi wifi_analyzer.py --help):
  python wifi_analyzer.py --web 8080                 # solo da questo PC
  python wifi_analyzer.py --web 8080 --host 0.0.0.0  # dalla rete, con token

Solo libreria standard di Python (http.server) piu' matplotlib, gia' richiesto.

Sicurezza: di default ascolta solo su 127.0.0.1. Se lo si espone sulla rete
serve un token (generato all'avvio se non indicato con --token): il link con il
token viene stampato sulla console e, aperto una volta, imposta un cookie.
"""

import collections
import dataclasses
import hmac
import io
import ipaddress
import json
import os
import secrets
import socket
import threading
import time
from datetime import datetime
from http import cookies
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

from matplotlib.figure import Figure

import wifi_analyzer as wa

HTML_PATH = Path(__file__).with_name("wifi_web.html")
COOKIE_NAME = "wifi_analyzer_token"
CSRF_HEADER = "X-Requested-With"
CSRF_VALUE = "wifi-analyzer"

# Impostazioni modificabili dal browser: (tipo, minimo, massimo)
EDITABLE = {
    "interval": (int, 5, 3600), "min_rssi": (int, -100, -30), "group": (bool,),
    "auto_scan": (bool,), "save_csv": (bool,), "save_dir": (str,), "play_speed": (float, 0.1, 60),
    "teams_webhook": (str,), "notify_image": (bool,), "report_enabled": (bool,),
    "report_hours": (float, 0.25, 168), "alert_enabled": (bool,), "alert_threshold": (int, 1, 50),
    "alert_cooldown_min": (int, 1, 1440),
}
# Cambiano il risultato dell'analisi (sovrapposizioni), non solo la vista
ANALYSIS_KEYS = {"min_rssi", "group"}
NUMERIC_COLUMNS = {"rssi", "rate", "nss", "util", "sta", "novl", "detail"}


def parse_setting(key, value):
    spec = EDITABLE[key]
    kind = spec[0]
    if kind is bool:
        if not isinstance(value, bool):
            raise ValueError(f"{key}: atteso true/false")
        return value
    if kind is str:
        value = str(value).strip()
        if key == "teams_webhook" and value and not value.lower().startswith("https://"):
            raise ValueError("L'URL del webhook deve iniziare con https://")
        if key == "save_dir" and not value:
            raise ValueError("Indica la cartella dove salvare i CSV")
        return value
    try:
        value = kind(value)
    except (TypeError, ValueError):
        raise ValueError(f"{key}: valore non valido") from None
    return min(max(value, spec[1]), spec[2])


def sort_value(cid, n):
    value = wa.SORT_KEYS[cid](n)
    return value[0] * 100 + value[1] if isinstance(value, tuple) else value


class Engine:
    """Stato condiviso del servizio: scansione in background, playback e notifiche.

    Tutti i campi sono protetti da self.lock; la scansione e il playback girano in
    thread propri, il server HTTP legge lo stato e invia comandi.
    """

    def __init__(self, scanner, settings):
        self.scanner = scanner
        self.settings = settings
        self.lock = threading.Condition()
        self.render_lock = threading.Lock()  # matplotlib: un grafico alla volta
        self.running = True

        self.raw = []            # reti dell'ultima scansione / del file in playback
        self.when = None         # data/ora dei dati mostrati
        self.version = 0         # cambia quando cambiano i dati o l'analisi
        self.mode = "live"
        self.scanning = False
        self.scan_requested = scanner is not None
        self.next_scan = 0.0
        self.mode_token = 0      # invalida le scansioni avviate prima di un cambio modalita'
        self.status = "In attesa della prima scansione" if scanner else "Nessuna scheda Wi-Fi: solo playback"
        self.notify_state = dict(seq=0, kind="", ok=True, text="", time="")
        self.pb = dict(dir="", files=[], index=0, when="", playing=False)
        self.pb_cache = {}
        self.chart_cache = collections.OrderedDict()
        self.notifier = wa.Notifier(settings, self._notify_result)

        threading.Thread(target=self._scan_loop, daemon=True, name="scan").start()
        threading.Thread(target=self._play_loop, daemon=True, name="playback").start()

    def stop(self):
        with self.lock:
            self.running = False
            self.lock.notify_all()

    # ---------------------------------------------------------------- scansione
    def _scan_loop(self):
        while True:
            with self.lock:
                if not self.running:
                    return
                live = self.mode == "live" and self.scanner is not None
                due = live and self.settings["auto_scan"] and time.time() >= self.next_scan
                if not live or not (self.scan_requested or due):
                    wait = 1.0
                    if live and self.settings["auto_scan"]:
                        wait = min(wait, max(0.05, self.next_scan - time.time()))
                    self.lock.wait(wait)
                    continue
                self.scan_requested = False
                self.scanning = True
                self.status = "Scansione in corso..."
                token = self.mode_token
            try:
                nets, error = self.scanner.scan(), None
            except Exception as e:
                nets, error = None, e
            when = datetime.now()
            with self.lock:
                self.scanning = False
                self.next_scan = time.time() + self.settings["interval"]
                if token != self.mode_token:
                    continue  # nel frattempo si e' passati al playback
                if error is not None:
                    self.status = f"Errore di scansione: {error}"
                    continue
                msg = f"Ultima scansione {when:%H:%M:%S}  -  {len(nets)} BSSID"
                if self.settings["save_csv"]:
                    try:
                        path = wa.save_csv(nets, self.settings["save_dir"], when, self.settings["min_rssi"])
                        msg += f"  -  salvata {path.name}"
                    except OSError as e:
                        msg += f"  -  ERRORE salvataggio: {e}"
                self.raw, self.when = nets, when
                self.version += 1
                self.status = msg
                min_rssi = self.settings["min_rssi"]
            self.notifier.check(nets, min_rssi)  # fuori dal lock: prepara il grafico

    def request_scan(self):
        with self.lock:
            if self.mode != "live" or self.scanner is None:
                return "La scansione e' disponibile solo in modalita' live"
            self.scan_requested = True
            self.lock.notify_all()
        return None

    # ---------------------------------------------------------------- impostazioni
    def update_settings(self, values):
        unknown = set(values) - set(EDITABLE)
        if unknown:
            raise ValueError(f"Impostazioni sconosciute: {', '.join(sorted(unknown))}")
        parsed = {k: parse_setting(k, v) for k, v in values.items()}
        with self.lock:
            old = dict(self.settings)
            self.notifier.settings_changed(old, parsed)
            self.settings.update(parsed)
            if any(old[k] != self.settings[k] for k in ANALYSIS_KEYS):
                self.version += 1
            if "interval" in parsed or "auto_scan" in parsed:
                self.next_scan = min(self.next_scan, time.time() + self.settings["interval"])
            self.lock.notify_all()
        wa.store_settings(self.settings)

    # ---------------------------------------------------------------- playback
    def enter_playback(self, folder):
        folder = str(folder).strip()
        files = wa.list_saved_scans(folder) if folder and Path(folder).is_dir() else []
        if not files:
            return f"Nessun file {wa.CSV_PREFIX}*.csv nella cartella {folder or '(vuota)'}"
        with self.lock:
            self.mode = "playback"
            self.mode_token += 1
            self.pb.update(dir=str(Path(folder).resolve()), files=files, playing=False)
            self.pb_cache.clear()
            self._show_frame(0)
            self.lock.notify_all()
        return None

    def enter_live(self):
        with self.lock:
            if self.scanner is None:
                return "Nessuna scheda Wi-Fi disponibile su questo sistema"
            self.mode = "live"
            self.mode_token += 1
            self.pb["playing"] = False
            self.raw, self.when = [], None
            self.version += 1
            self.status = "Ritorno al live..."
            self.scan_requested = True
            self.lock.notify_all()
        return None

    def _show_frame(self, idx):
        files = self.pb["files"]
        idx = max(0, min(idx, len(files) - 1))
        path = files[idx]
        if path not in self.pb_cache:
            try:
                self.pb_cache[path] = wa.load_csv(path)
            except (OSError, ValueError, UnicodeDecodeError) as e:
                self.pb_cache[path] = (wa.time_from_filename(path), [])
                self.status = f"Errore lettura {path.name}: {e}"
        when, nets = self.pb_cache[path]
        self.pb.update(index=idx, when=when)
        self.raw, self.when = nets, None
        self.version += 1
        self.status = f"{path.name}  -  {len(nets)} BSSID"

    def playback_action(self, action, index=None):
        with self.lock:
            if self.mode != "playback":
                return "Non sei in modalita' playback"
            last = len(self.pb["files"]) - 1
            i = self.pb["index"]
            if action == "seek":
                try:
                    self._show_frame(int(index))
                except (TypeError, ValueError):
                    return "Indice non valido"
            elif action in ("first", "prev", "next", "last"):
                self._show_frame({"first": 0, "prev": i - 1, "next": i + 1, "last": last}[action])
            elif action == "play":
                if i >= last:
                    self._show_frame(0)
                self.pb["playing"] = True
            elif action == "pause":
                self.pb["playing"] = False
            elif action == "reload":
                current = self.pb["files"][i]
                files = wa.list_saved_scans(self.pb["dir"])
                if files:
                    self.pb["files"] = files
                    self._show_frame(files.index(current) if current in files else 0)
            else:
                return f"Azione sconosciuta: {action}"
            self.lock.notify_all()
        return None

    def _play_loop(self):
        while True:
            with self.lock:
                if not self.running:
                    return
                if not (self.mode == "playback" and self.pb["playing"]):
                    self.lock.wait(0.5)
                    continue
                delay = self.settings["play_speed"]
            time.sleep(delay)
            with self.lock:
                if self.mode == "playback" and self.pb["playing"]:
                    if self.pb["index"] >= len(self.pb["files"]) - 1:
                        self.pb["playing"] = False
                    else:
                        self._show_frame(self.pb["index"] + 1)

    # ---------------------------------------------------------------- notifiche
    def _notify_result(self, kind, ok, text):
        with self.lock:
            self.notify_state = dict(seq=self.notify_state["seq"] + 1, kind=kind, ok=ok, text=text,
                                     time=datetime.now().strftime("%H:%M"))

    def send_notification(self, kind, url=None, image=None):
        if kind not in ("report", "test"):
            return "Tipo di notifica non valido"
        if url is not None:
            url = parse_setting("teams_webhook", url)
        with self.lock:
            radios = wa.group_radios(self.raw)
            min_rssi = self.settings["min_rssi"]
        if not self.notifier.send(kind, radios, min_rssi, url=url or None, image=image):
            return "Configura prima l'URL del webhook Teams"
        return None

    # ---------------------------------------------------------------- viste
    def _view(self):
        """Copia delle reti con le sovrapposizioni calcolate (chiamare con il lock)."""
        if self.settings["group"]:
            nets = wa.group_radios(self.raw)
        else:
            nets = [dataclasses.replace(n, overlaps=[]) for n in self.raw]
        wa.compute_overlaps(nets, self.settings["min_rssi"])
        return nets

    def state(self):
        with self.lock:
            thr = self.settings["min_rssi"]
            nets = self._view()
            pb = self.pb
            return dict(
                version=self.version, mode=self.mode, scanning=self.scanning, status=self.status,
                scanner=getattr(self.scanner, "name", None),
                next_scan=max(0, round(self.next_scan - time.time()))
                if self.mode == "live" and self.settings["auto_scan"] and not self.scanning else None,
                notify=dict(self.notify_state),
                settings={k: self.settings[k] for k in EDITABLE},
                webhook_from_env=bool(os.environ.get(wa.WEBHOOK_ENV)),
                playback=dict(dir=pb["dir"], count=len(pb["files"]), index=pb["index"], when=pb["when"],
                              file=pb["files"][pb["index"]].name if pb["files"] else "",
                              playing=pb["playing"]),
                columns=[[cid, title] for cid, title, _w in wa.TABLE_COLUMNS],
                numeric_columns=sorted(NUMERIC_COLUMNS),
                bands=[[k, b["title"]] for k, b in wa.BANDS.items()],
                font_sizes=list(wa.FONT_SIZES),
                rows=[dict(id=n.bssid, band=n.band, tag=wa.row_tag(n, thr), cells=list(wa.row_values(n)),
                           sort=[sort_value(cid, n) for cid, _t, _w in wa.TABLE_COLUMNS])
                      for n in nets],
            )

    def chart_png(self, width, height, dpr, font, bands, show_util, selected):
        with self.lock:
            key = (self.version, width, height, dpr, font, tuple(bands), show_util, selected,
                   self.settings["min_rssi"], self.settings["group"])
            if key in self.chart_cache:
                self.chart_cache.move_to_end(key)
                return self.chart_cache[key]
            nets = self._view()
            thr = self.settings["min_rssi"]
        with self.render_lock:
            fig = Figure(figsize=(width / 100, height / 100), dpi=100, layout="constrained")
            wa.draw_bands(fig, nets, bands, thr, selected or None, font, show_util)
            buf = io.BytesIO()
            fig.savefig(buf, format="png", dpi=100 * dpr)
        png = buf.getvalue()
        with self.lock:
            self.chart_cache[key] = png
            while len(self.chart_cache) > 8:
                self.chart_cache.popitem(last=False)
        return png

    def table_csv(self):
        with self.lock:
            nets = [dataclasses.replace(n, overlaps=[]) for n in self.raw]
            when = self.when or datetime.now()
            thr = self.settings["min_rssi"]
        out = io.StringIO()
        wa.write_csv(out, nets, when, thr)
        return wa.csv_filename(when), out.getvalue().encode("utf-8-sig")


# --------------------------------------------------------------------------
# HTTP
# --------------------------------------------------------------------------

class Handler(BaseHTTPRequestHandler):
    engine = None
    token = None
    allowed_hosts = None  # con bind su loopback: protezione contro DNS rebinding
    server_version = "WiFiAnalyzer/1.0"

    def log_message(self, fmt, *args):
        pass  # niente log per ogni richiesta (il browser interroga lo stato ogni secondo)

    # ---------------------------------------------------------------- risposte
    def _send(self, code, body, ctype, headers=None):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("X-Frame-Options", "DENY")
        for k, v in (headers or {}).items():
            self.send_header(k, v)
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(body)

    def _json(self, code, obj):
        self._send(code, json.dumps(obj).encode("utf-8"), "application/json; charset=utf-8")

    def _error(self, code, message):
        self._json(code, {"error": message})

    # ---------------------------------------------------------------- accesso
    def _authorized(self, url):
        if self.allowed_hosts is not None:
            if self.headers.get("Host", "").lower() not in self.allowed_hosts:
                self._send(403, b"Host non consentito", "text/plain; charset=utf-8")
                return False
        if not self.token:
            return True
        jar = cookies.SimpleCookie(self.headers.get("Cookie", ""))
        sent = jar[COOKIE_NAME].value if COOKIE_NAME in jar else ""
        if sent and hmac.compare_digest(sent, self.token):
            return True
        query_token = parse_qs(url.query).get("token", [""])[0]
        if self.command == "GET" and url.path == "/" and query_token and \
                hmac.compare_digest(query_token, self.token):
            # primo accesso con il link della console: cookie e redirect senza token nell'URL
            self._send(303, b"", "text/plain", {
                "Location": "/",
                "Set-Cookie": f"{COOKIE_NAME}={self.token}; Path=/; HttpOnly; SameSite=Strict; Max-Age=31536000"})
            return False
        self._send(401, "Accesso negato: apri il link con il token stampato dalla console del "
                        "servizio.".encode("utf-8"), "text/plain; charset=utf-8")
        return False

    # ---------------------------------------------------------------- GET
    def do_GET(self):
        url = urlparse(self.path)
        if not self._authorized(url):
            return
        if url.path in ("/", "/index.html"):
            try:
                self._send(200, HTML_PATH.read_bytes(), "text/html; charset=utf-8")
            except OSError:
                self._send(500, f"Manca {HTML_PATH.name}".encode(), "text/plain; charset=utf-8")
        elif url.path == "/api/state":
            self._json(200, self.engine.state())
        elif url.path == "/api/chart.png":
            self._chart(parse_qs(url.query))
        elif url.path == "/api/table.csv":
            name, data = self.engine.table_csv()
            self._send(200, data, "text/csv; charset=utf-8",
                       {"Content-Disposition": f'attachment; filename="{name}"'})
        elif url.path == "/favicon.ico":
            self._send(204, b"", "image/x-icon")
        else:
            self._error(404, "Risorsa non trovata")

    do_HEAD = do_GET

    def _chart(self, q):
        def num(name, conv, default, lo, hi):
            try:
                return min(max(conv(q.get(name, [default])[0]), lo), hi)
            except (TypeError, ValueError):
                return default
        bands = [b for b in q.get("bands", ["2.4,5,6"])[0].split(",") if b in wa.BANDS]
        if not bands:
            return self._error(400, "Nessuna banda selezionata")
        png = self.engine.chart_png(
            num("w", int, 1200, 300, 4000), num("h", int, 800, 200, 3000),
            num("dpr", float, 1.0, 1.0, 3.0), num("font", int, 11, 6, 30), bands,
            q.get("util", ["1"])[0] == "1", q.get("sel", [""])[0][:64])
        self._send(200, png, "image/png")

    # ---------------------------------------------------------------- POST
    def do_POST(self):
        url = urlparse(self.path)
        if not self._authorized(url):
            return
        # header personalizzato: un'altra pagina web non puo' inviarlo senza preflight CORS
        if self.headers.get(CSRF_HEADER) != CSRF_VALUE:
            return self._error(403, "Richiesta non consentita")
        try:
            length = int(self.headers.get("Content-Length", "0"))
            if length > 65536:
                return self._error(413, "Richiesta troppo grande")
            body = json.loads(self.rfile.read(length) or b"{}")
            if not isinstance(body, dict):
                raise ValueError
        except ValueError:
            return self._error(400, "JSON non valido")

        engine, error = self.engine, None
        try:
            if url.path == "/api/scan":
                error = engine.request_scan()
            elif url.path == "/api/settings":
                engine.update_settings(body)
            elif url.path == "/api/mode":
                if body.get("mode") == "playback":
                    error = engine.enter_playback(body.get("dir", ""))
                elif body.get("mode") == "live":
                    error = engine.enter_live()
                else:
                    error = "Modalita' sconosciuta"
            elif url.path == "/api/playback":
                error = engine.playback_action(body.get("action"), body.get("index"))
            elif url.path == "/api/notify":
                image = body.get("notify_image")
                error = engine.send_notification(body.get("kind"), body.get("teams_webhook"),
                                                 image if isinstance(image, bool) else None)
            else:
                return self._error(404, "Risorsa non trovata")
        except ValueError as e:
            error = str(e)
        if error:
            return self._error(400, error)
        self._json(200, {"ok": True})


def _is_loopback(host):
    if host == "localhost":
        return True
    try:
        return ipaddress.ip_address(host).is_loopback
    except ValueError:
        return False


def serve(scanner, settings, host, port, token=None, playback_dir=None):
    loopback = _is_loopback(host)
    if not loopback and not token:
        token = secrets.token_urlsafe(16)
    engine = Engine(scanner, settings)
    if playback_dir:
        error = engine.enter_playback(playback_dir)
        if error:
            print(error)

    Handler.engine = engine
    Handler.token = token
    Handler.allowed_hosts = ({f"localhost:{port}", f"127.0.0.1:{port}", f"[::1]:{port}"}
                             if loopback else None)
    try:
        httpd = ThreadingHTTPServer((host, port), Handler)
    except OSError as e:
        engine.stop()
        raise SystemExit(f"Impossibile aprire la porta {port} su {host}: {e}")
    httpd.daemon_threads = True

    suffix = f"/?token={token}" if token else "/"
    print(f"WiFi Analyzer web service ({getattr(scanner, 'name', 'solo playback')})")
    if loopback:
        print(f"  Apri nel browser:  http://localhost:{port}{suffix}")
    else:
        names = {socket.gethostname()}
        try:
            names |= {a for a in socket.gethostbyname_ex(socket.gethostname())[2]
                      if not a.startswith("127.")}
        except OSError:
            pass
        for name in sorted(names):
            print(f"  Apri nel browser:  http://{name}:{port}{suffix}")
        print("  Il token da' pieno controllo del servizio: condividilo solo con chi deve usarlo.")
    print("  Ctrl+C per fermare.")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        engine.stop()
        httpd.server_close()
        wa.store_settings(settings)
