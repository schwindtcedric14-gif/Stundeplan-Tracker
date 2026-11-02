#!/usr/bin/env python3
"""Stundenplan-Tracker: kleiner lokaler Server, der deinen WebUntis-Stundenplan
ausliest und auswertet, wie oft du seit Schuljahresbeginn frei / Vertretung hattest.

Starten:  python3 server.py   ->  http://localhost:8765 im Browser öffnen
Benutzername und Passwort werden nur an WebUntis geschickt und nirgends gespeichert.
Der geladene Stundenplan liegt nur im Arbeitsspeicher, solange der Server läuft.
"""
import datetime as dt
import http.cookiejar
import json
import os
import random
import secrets
import ssl
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter, defaultdict
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

UNTIS_SERVER = "rs-einrich.webuntis.com"
UNTIS_SCHOOL = "rs-einrich"
PORT = int(os.environ.get("PORT", "8765"))
# Lokal nur auf dem eigenen Mac erreichbar; im Internet (z. B. Render setzt PORT) für alle
HOST = os.environ.get("HOST", "0.0.0.0" if "PORT" in os.environ else "127.0.0.1")
# Schutz gegen Passwort-Raten: so viele Fehlversuche pro IP in 15 Minuten
MAX_FAILED_LOGINS = 8
HERE = os.path.dirname(os.path.abspath(__file__))

# Ab diesem Tag (Monat, Tag) zählt das 2. Halbjahr
HALBJAHR_2_START = (2, 1)
# So viele Tage über heute hinaus wird der Plan geladen (für die Wochenansicht)
LOOKAHEAD_DAYS = 14
SESSION_TTL = 3 * 3600

# Nachträgliche Vertretungen: Stunden, die Untis als normalen Unterricht zeigt,
# die aber eigentlich Vertretung waren (z. B. Lehrkraft fest für eine kranke Lehrkraft eingesetzt).
# "lehrkraft": Untis-Kürzel der Vertretung (Groß-/Kleinschreibung egal)
# "fehlte":    Untis-Kürzel der Lehrkraft, die eigentlich unterrichtet hätte
# "statt":     welches Fach eigentlich dran gewesen wäre (nur für die Anzeige)
# Es werden nur Stunden umgewandelt, die Untis als normalen Unterricht zeigt (keine Zusatzstunden).
NACHTRAEGLICHE_VERTRETUNGEN = [
    # Herr Bilo (Bil) war bis zu den Herbstferien fest für Herrn Kramer (Kr, krank) in Physik eingeplant
    {"lehrkraft": ["Bil", "Bilo"], "von": "2026-08-10", "bis": "2026-10-02",
     "fehlte": "Kr", "statt": "Physik"},
]

TEACHER, SUBJECT, ROOM = 2, 3, 4
SESSIONS = {}
FAILED = defaultdict(list)


class UntisError(Exception):
    pass


def ssl_context():
    # Python von python.org bringt auf dem Mac oft keine Zertifikate mit -> macOS-Zertifikate nutzen
    ctx = ssl.create_default_context()
    if not ctx.get_ca_certs() and os.path.exists("/etc/ssl/cert.pem"):
        ctx.load_verify_locations("/etc/ssl/cert.pem")
    return ctx


# ---------------------------------------------------------------- WebUntis

class Untis:
    def __init__(self, server, school):
        self.base = f"https://{server}/WebUntis"
        self.school = school
        self.opener = urllib.request.build_opener(
            urllib.request.HTTPSHandler(context=ssl_context()),
            urllib.request.HTTPCookieProcessor(http.cookiejar.CookieJar()))
        self.token = None
        self.person_id = None
        self.person_type = None

    def _request(self, url, data=None, headers=None):
        h = {"User-Agent": "Stundenplan-Tracker/1.0", "Accept": "application/json"}
        h.update(headers or {})
        body = None
        if data is not None:
            body = json.dumps(data).encode()
            h["Content-Type"] = "application/json"
        req = urllib.request.Request(url, data=body, headers=h)
        with self.opener.open(req, timeout=30) as r:
            return r.read().decode("utf-8")

    def rpc(self, method, params=None):
        url = f"{self.base}/jsonrpc.do?school={urllib.parse.quote(self.school)}"
        res = json.loads(self._request(
            url, {"id": "1", "method": method, "params": params or {}, "jsonrpc": "2.0"}))
        if "error" in res:
            err = res["error"]
            raise UntisError(f"{method}: {err.get('message')} ({err.get('code')})")
        return res.get("result")

    def login(self, user, password):
        try:
            res = self.rpc("authenticate", {"user": user, "password": password,
                                            "client": "StundenplanTracker"})
        except UntisError as e:
            if "-8504" in str(e) or "bad credentials" in str(e).lower():
                raise UntisError("Benutzername oder Passwort falsch.")
            raise
        self.person_id = res.get("personId")
        self.person_type = res.get("personType")
        if not self.person_id:
            raise UntisError("Login ok, aber Untis liefert keine Personen-ID "
                             "(Eltern-Accounts werden nicht unterstützt).")
        try:
            self.token = self._request(f"{self.base}/api/token/new").strip().strip('"')
        except Exception:
            self.token = None

    def logout(self):
        try:
            self.rpc("logout")
        except Exception:
            pass

    def timegrid(self):
        """Stundenraster der Schule: [{name, start, end}, ...] (leer, wenn nicht verfügbar)."""
        try:
            best = []
            for day in self.rpc("getTimegridUnits") or []:
                units = sorted(day.get("timeUnits", []), key=lambda u: u["startTime"])
                if len(units) > len(best):
                    best = units
            return [{"name": u.get("name") or str(i + 1), "start": u["startTime"], "end": u["endTime"]}
                    for i, u in enumerate(best)]
        except Exception:
            return []

    def schoolyear(self):
        today = dt.date.today()
        try:
            sy = self.rpc("getCurrentSchoolyear")
            if sy and sy.get("startDate"):
                return parse_date(sy["startDate"]), parse_date(sy["endDate"])
        except Exception:
            pass
        try:
            for sy in self.rpc("getSchoolyears") or []:
                s, e = parse_date(sy["startDate"]), parse_date(sy["endDate"])
                if s <= today <= e:
                    return s, e
        except Exception:
            pass
        y = today.year if today.month >= 8 else today.year - 1
        return dt.date(y, 8, 1), dt.date(y + 1, 7, 31)

    # --- Variante A: Wochen-Daten wie in der Untis-Webseite (mit Namen)
    def lessons_weekly(self, start, end):
        lessons = []
        monday = start - dt.timedelta(days=start.weekday())
        headers = {"Authorization": f"Bearer {self.token}"} if self.token else {}
        while monday <= end:
            url = (f"{self.base}/api/public/timetable/weekly/data?elementType={self.person_type}"
                   f"&elementId={self.person_id}&date={monday.isoformat()}&formatId=1")
            data = json.loads(self._request(url, headers=headers))["data"]["result"]["data"]
            lessons += normalize_weekly(data)
            monday += dt.timedelta(days=7)
        return lessons

    # --- Variante B: klassische JSON-RPC-Schnittstelle
    def lessons_rpc(self, start, end):
        names = {}
        try:
            for t in self.rpc("getTeachers") or []:
                names[t["id"]] = t.get("name") or t.get("longName")
        except Exception:
            pass
        lessons = []
        chunk = start
        while chunk <= end:
            chunk_end = min(chunk + dt.timedelta(days=27), end)
            res = self.rpc("getTimetable", {"options": {
                "element": {"id": self.person_id, "type": self.person_type},
                "startDate": int(chunk.strftime("%Y%m%d")),
                "endDate": int(chunk_end.strftime("%Y%m%d")),
                "showSubstText": True, "showInfo": True, "showLsText": True,
                "teacherFields": ["id", "name", "longname"],
                "subjectFields": ["id", "name", "longname"],
                "roomFields": ["id", "name"],
            }}) or []
            lessons += normalize_rpc(res, names)
            chunk = chunk_end + dt.timedelta(days=1)
        return lessons


def parse_date(v):
    s = str(v).replace("-", "")
    return dt.date(int(s[:4]), int(s[4:6]), int(s[6:8]))


def teacher_label(names, tid):
    if not tid:
        return None
    return names.get(tid) or f"Lehrkraft #{tid}"


def normalize_weekly(data):
    names, subjects, rooms = {}, {}, {}
    for e in data.get("elements", []):
        label = e.get("name") or e.get("displayname") or e.get("longName")
        if not label:
            continue
        if e.get("type") == TEACHER:
            names[e["id"]] = label
        elif e.get("type") == SUBJECT:
            subjects[e["id"]] = e.get("longName") or label
        elif e.get("type") == ROOM:
            rooms[e["id"]] = label
    out = []
    for periods in data.get("elementPeriods", {}).values():
        for p in periods:
            teachers, subject, room = [], "", ""
            for el in p.get("elements", []):
                if el.get("type") == TEACHER:
                    teachers.append((el.get("id") or 0, el.get("orgId") or 0))
                elif el.get("type") == SUBJECT:
                    subject = subjects.get(el.get("id")) or subjects.get(el.get("orgId")) or ""
                elif el.get("type") == ROOM:
                    room = rooms.get(el.get("id")) or rooms.get(el.get("orgId")) or ""
            state = (p.get("cellState") or "STANDARD").upper()
            flags = p.get("is") or {}
            changed = any(org and org != tid for tid, org in teachers)
            if state == "CANCEL" or flags.get("cancelled"):
                status = "cancelled"
            elif state == "SUBSTITUTION" or flags.get("substitution") or changed:
                status = "substitution"
            elif state == "ADDITIONAL" or flags.get("additional"):
                status = "additional"
            elif state in ("SHIFT", "ROOMSUBSTITUTION") or flags.get("shift") or flags.get("roomSubstitution"):
                status = "change"
            elif state == "EXAM" or flags.get("exam"):
                status = "exam"
            else:
                status = "normal"
            out.append(make_lesson(p.get("date"), p.get("startTime"), p.get("endTime"),
                                   subject, room, status, teachers, names,
                                   p.get("substText") or p.get("lessonText") or ""))
    return out


def normalize_rpc(lessons, names):
    out = []
    for l in lessons:
        if l.get("lstype") in ("oh", "sb", "bs"):
            continue
        teachers = []
        for t in l.get("te", []):
            if t.get("name"):
                names.setdefault(t["id"], t.get("name"))
            if t.get("orgid") and t.get("orgname"):
                names.setdefault(t["orgid"], t.get("orgname"))
            teachers.append((t.get("id") or 0, t.get("orgid") or 0))
        su = l.get("su") or []
        subject = (su[0].get("longname") or su[0].get("name")) if su else ""
        ro = l.get("ro") or []
        room = ro[0].get("name", "") if ro else ""
        code = l.get("code")
        changed = any(org and org != tid for tid, org in teachers)
        if code == "cancelled":
            status = "cancelled"
        elif changed:
            status = "substitution"
        elif l.get("lstype") == "ex":
            status = "exam"
        elif code == "irregular":
            status = "change"
        else:
            status = "normal"
        out.append(make_lesson(l.get("date"), l.get("startTime"), l.get("endTime"),
                               subject, room, status, teachers, names, l.get("substText") or ""))
    return out


def make_lesson(date, start, end, subject, room, status, teachers, names, text):
    original = [teacher_label(names, org or tid) for tid, org in teachers]
    current = [teacher_label(names, tid) for tid, org in teachers if tid]
    return {
        "date": parse_date(date).isoformat(),
        "start": int(start or 0), "end": int(end or 0),
        "subject": subject or "?", "room": room or "", "status": status,
        "original": [t for t in original if t] or ["unbekannt"],
        "current": [t for t in current if t],
        "text": text,
    }


# ---------------------------------------------------------------- Auswertung

def to_min(t):
    return (t // 100) * 60 + t % 100


def teacher_matches(label, names):
    return (label or "").strip().lower() in names


def apply_overrides(lessons):
    for l in lessons:
        l.setdefault("manual", False)
        if l["status"] != "normal":
            continue
        for rule in NACHTRAEGLICHE_VERTRETUNGEN:
            names = [n.lower() for n in rule["lehrkraft"]]
            if not (rule["von"] <= l["date"] <= rule["bis"]):
                continue
            hits = [t for t in l["current"] + l["original"] if teacher_matches(t, names)]
            if hits:
                l["status"] = "substitution"
                l["current"] = [hits[0]]
                l["original"] = [rule["fehlte"]]
                l["manual"] = True
                l["statt"] = rule.get("statt", "")
                note = f"nachgetragen: {hits[0]} fest als Vertretung für {rule['fehlte']}"
                if rule.get("statt"):
                    note += f" (statt {rule['statt']})"
                l["text"] = (l["text"] + " · " if l["text"] else "") + note
                break
    return lessons


def prepare(lessons):
    """Doppelte entfernen, sortieren und markieren, welche Ausfälle wirklich frei waren."""
    lessons = apply_overrides(lessons)
    seen, items = set(), []
    for l in lessons:
        key = (l["date"], l["start"], l["end"], l["subject"], l["status"], tuple(l["original"]))
        if key not in seen:
            seen.add(key)
            items.append(l)
    items.sort(key=lambda l: (l["date"], l["start"]))
    by_day = defaultdict(list)
    for l in items:
        by_day[l["date"]].append(l)
    # Ausfall zählt nur als "frei", wenn im selben Zeitraum kein anderer Unterricht stattfindet
    for day in by_day.values():
        for l in day:
            l["free"] = l["status"] == "cancelled" and not any(
                o is not l and o["status"] != "cancelled"
                and o["start"] < l["end"] and l["start"] < o["end"] for o in day)
    return items


def guess_grid(items):
    """Ohne Untis-Raster: häufige Anfangszeiten als Stunden nehmen."""
    starts = Counter(l["start"] for l in items)
    grid = []
    for i, s in enumerate(sorted(t for t, c in starts.items() if c >= 3)):
        ends = Counter(l["end"] for l in items if l["start"] == s)
        e = min(ends)  # bei Doppelstunden die kürzere Endzeit
        if grid and s < grid[-1]["end"]:
            continue
        grid.append({"name": str(len(grid) + 1), "start": s, "end": e})
    return grid


def slot_state(day_lessons, s, e):
    """Was war in diesem Zeitfenster? None (nichts geplant) / free / subst / held."""
    in_slot = [l for l in day_lessons if l["start"] < e and s < l["end"]
               and not (l["status"] == "cancelled" and not l["free"])]
    if not in_slot:
        return None
    if all(l["status"] == "cancelled" for l in in_slot):
        return "free"
    if any(l["status"] == "substitution" for l in in_slot):
        return "subst"
    return "held"


def compute_stats(all_items, frm, to, grid):
    today = dt.date.today()
    to = min(to, today)
    items = [l for l in all_items if frm.isoformat() <= l["date"] <= to.isoformat()]

    by_day = defaultdict(list)
    for l in items:
        by_day[l["date"]].append(l)

    free = [l for l in items if l["free"]]
    subst = [l for l in items if l["status"] == "substitution"]
    held = [l for l in items if l["status"] != "cancelled"]
    total = len(held) + len(free)

    free_teacher, subst_teacher, substitute = Counter(), Counter(), Counter()
    free_subject, subst_subject = Counter(), Counter()
    for l in free:
        for t in l["original"]:
            free_teacher[t] += 1
        free_subject[l["subject"]] += 1
    for l in subst:
        for t in l["original"]:
            subst_teacher[t] += 1
        for t in l["current"]:
            if t not in l["original"]:
                substitute[t] += 1
        subst_subject[l["subject"]] += 1

    months = defaultdict(lambda: {"free": 0, "subst": 0, "total": 0})
    for l in items:
        if l["status"] == "cancelled" and not l["free"]:
            continue
        m = months[l["date"][:7]]
        m["total"] += 1
        if l["free"]:
            m["free"] += 1
        elif l["status"] == "substitution":
            m["subst"] += 1

    free_days = [d for d, day in by_day.items()
                 if day and all(l["status"] == "cancelled" and l["free"] for l in day)]

    # Übersicht: für jeden Wochentag und jede Stunde, wie oft frei / Vertretung
    heat = [[{"total": 0, "free": 0, "subst": 0} for _ in grid] for _ in range(5)]
    for date, day in by_day.items():
        wd = dt.date.fromisoformat(date).weekday()
        if wd > 4:
            continue
        for i, g in enumerate(grid):
            st = slot_state(day, g["start"], g["end"])
            if st:
                cell = heat[wd][i]
                cell["total"] += 1
                if st in ("free", "subst"):
                    cell[st] += 1

    def top(c):
        return [{"name": k, "count": v} for k, v in c.most_common()]

    events = [l for l in items if l["free"] or l["status"] == "substitution"]
    return {
        "from": frm.isoformat(), "to": to.isoformat(), "empty": frm > to,
        "total": total, "free": len(free), "subst": len(subst),
        "manual": [public(l) for l in subst if l["manual"]],
        "freeMinutes": sum(to_min(l["end"]) - to_min(l["start"]) for l in free),
        "freeDays": sorted(free_days),
        "freeByTeacher": top(free_teacher), "substByTeacher": top(subst_teacher),
        "substitutes": top(substitute),
        "freeBySubject": top(free_subject), "substBySubject": top(subst_subject),
        "months": [{"month": k, **v} for k, v in sorted(months.items())],
        "period6": sixth_period_stats(by_day, grid[5] if len(grid) >= 6 else None),
        "heat": heat,
        "events": [public(l) for l in reversed(events)][:300],
    }


def public(l):
    return {k: l.get(k) for k in ("date", "start", "end", "subject", "room", "status",
                                  "original", "current", "text", "free", "manual", "statt")}


def sixth_period_stats(by_day, slot):
    result = {"slot": None, "days": 0, "free": 0, "streak": 0, "best": 0,
              "bestFrom": None, "bestTo": None}
    if not slot:
        return result
    result["slot"] = [slot["start"], slot["end"]]
    run, run_start = 0, None
    for date in sorted(by_day):
        st = slot_state(by_day[date], slot["start"], slot["end"])
        if not st:
            continue  # an dem Tag gab es keine 6. Stunde -> zählt nicht, bricht Streak nicht
        result["days"] += 1
        if st == "free":
            result["free"] += 1
            run_start = date if run == 0 else run_start
            run += 1
            if run > result["best"]:
                result["best"], result["bestFrom"], result["bestTo"] = run, run_start, date
        else:
            run = 0
    result["streak"] = run
    return result


def halves(year_start, year_end):
    m, d = HALBJAHR_2_START
    h2 = dt.date(year_start.year + 1, m, d)
    return [
        {"key": "year", "label": "Ganzes Schuljahr", "from": year_start.isoformat(), "to": year_end.isoformat()},
        {"key": "h1", "label": "1. Halbjahr", "from": year_start.isoformat(),
         "to": (h2 - dt.timedelta(days=1)).isoformat()},
        {"key": "h2", "label": "2. Halbjahr", "from": h2.isoformat(), "to": year_end.isoformat()},
    ]


# ---------------------------------------------------------------- Laden & Sitzungen

def load_untis(user, password):
    u = Untis(UNTIS_SERVER, UNTIS_SCHOOL)
    u.login(user, password)
    try:
        year_start, year_end = u.schoolyear()
        load_to = min(year_end, dt.date.today() + dt.timedelta(days=LOOKAHEAD_DAYS))
        grid = u.timegrid()
        errors, lessons = [], None
        for fn in (u.lessons_weekly, u.lessons_rpc):
            try:
                lessons = fn(year_start, load_to)
                break
            except Exception as e:
                errors.append(f"{fn.__name__}: {e}")
        if lessons is None:
            raise UntisError("Stundenplan konnte nicht geladen werden. " + " | ".join(errors))
        return year_start, year_end, load_to, grid, lessons
    finally:
        u.logout()


def load_demo():
    today = dt.date.today()
    y = today.year if today.month >= 8 else today.year - 1
    year_start, year_end = dt.date(y, 8, 10), dt.date(y + 1, 7, 2)
    load_to = today + dt.timedelta(days=LOOKAHEAD_DAYS)
    rnd = random.Random(7)
    plan = [("Mathe", "MÜL", "A12"), ("Deutsch", "SCH", "B03"), ("Englisch", "WEB", "B05"),
            ("Bio", "KLE", "NW1"), ("Sport", "BRA", "Halle"), ("Geschichte", "SCH", "B03"),
            ("Physik", "MÜL", "NW2"), ("Kunst", "HOF", "K1")]
    others = ["KRA", "LAN", "ZIM", "FRI"]
    times = [(745, 830), (835, 920), (940, 1025), (1030, 1115), (1135, 1220), (1225, 1310)]
    grid = [{"name": str(i + 1), "start": s, "end": e} for i, (s, e) in enumerate(times)]
    out, d = [], year_start
    while d <= load_to:
        if d.weekday() < 5:
            whole_day_off = rnd.random() < 0.02
            periods = times if d.weekday() != 4 else times[:5]  # freitags nur 5 Stunden
            for i, (s, e) in enumerate(periods):
                subject, t, room = plan[(d.weekday() * 3 + i) % len(plan)]
                if t == "HOF" and d <= dt.date(y, 10, 2):
                    t = "Bil"
                r = rnd.random()
                status, current = "normal", [t]
                if whole_day_off or r < 0.06 + (0.08 if t == "MÜL" else 0) + (0.3 if i == 5 else 0):
                    status, current = "cancelled", []
                elif r < 0.14 + (0.06 if t == "WEB" else 0):
                    status, current = "substitution", [rnd.choice(others)]
                out.append({"date": d.isoformat(), "start": s, "end": e, "subject": subject,
                            "room": room, "status": status, "original": [t],
                            "current": current, "text": ""})
        d += dt.timedelta(days=1)
    return year_start, year_end, load_to, grid, out


def fill_session(sid, loaded):
    """Geladene Untis-Daten in die Sitzung schreiben (beim Login und beim Aktualisieren)."""
    year_start, year_end, load_to, grid, lessons = loaded
    items = prepare(lessons)
    SESSIONS[sid].update({"items": items, "grid": grid or guess_grid(items), "yearStart": year_start,
                          "yearEnd": year_end, "loadTo": load_to, "loadedAt": time.time()})


def create_session(loaded, demo=False, cred=None):
    now = time.time()
    # Sitzungen, die 3 Stunden nicht benutzt wurden, samt Zugangsdaten verwerfen
    for sid in [k for k, v in SESSIONS.items() if now - v["seen"] > SESSION_TTL]:
        del SESSIONS[sid]
    sid = secrets.token_urlsafe(16)
    # cred (Untis-Login) liegt nur im Arbeitsspeicher, damit "Aktualisieren" ohne neues Anmelden geht
    SESSIONS[sid] = {"created": now, "seen": now, "demo": demo, "cred": cred}
    fill_session(sid, loaded)
    return sid


MIN_REFRESH_SECONDS = 20


def refresh_session(sid):
    s = SESSIONS[sid]
    if time.time() - s["loadedAt"] < MIN_REFRESH_SECONDS:
        return  # gerade erst geladen – Untis nicht unnötig belasten
    fill_session(sid, load_demo() if s["demo"] else load_untis(*s["cred"]))


def session_info(sid):
    s = SESSIONS[sid]
    today = dt.date.today()
    return {
        "ok": True, "session": sid, "demo": s["demo"], "today": today.isoformat(),
        "year": {"from": s["yearStart"].isoformat(), "to": s["yearEnd"].isoformat()},
        "loadedTo": s["loadTo"].isoformat(),
        "loadedAt": s["loadedAt"],
        "ranges": halves(s["yearStart"], s["yearEnd"]),
        "grid": s["grid"],
        "stats": compute_stats(s["items"], s["yearStart"], today, s["grid"]),
    }


def week(sid, date):
    s = SESSIONS[sid]
    monday = date - dt.timedelta(days=date.weekday())
    days = [(monday + dt.timedelta(days=i)).isoformat() for i in range(5)]
    lessons = [public(l) for l in s["items"] if days[0] <= l["date"] <= days[-1]]
    return {"ok": True, "monday": monday.isoformat(), "days": days, "lessons": lessons,
            "grid": s["grid"], "today": dt.date.today().isoformat()}


# ---------------------------------------------------------------- Webserver

class Handler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        sys.stderr.write("[%s] %s\n" % (self.log_date_time_string(), fmt % args))

    def _send(self, code, body, ctype="application/json; charset=utf-8"):
        data = body if isinstance(body, bytes) else json.dumps(body).encode()
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def client_ip(self):
        fwd = self.headers.get("X-Forwarded-For")
        return fwd.split(",")[0].strip() if fwd else self.client_address[0]

    def do_HEAD(self):
        self.send_response(200 if self.path in ("/", "/index.html") else 404)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.end_headers()

    def do_GET(self):
        if self.path in ("/", "/index.html"):
            with open(os.path.join(HERE, "index.html"), "rb") as f:
                return self._send(200, f.read(), "text/html; charset=utf-8")
        self._send(404, {"error": "Nicht gefunden"})

    def do_POST(self):
        try:
            length = int(self.headers.get("Content-Length") or 0)
            req = json.loads(self.rfile.read(length) or b"{}")
            if self.path == "/api/login":
                if req.get("demo"):
                    return self._send(200, session_info(create_session(load_demo(), demo=True)))
                user, pw = (req.get("username") or "").strip(), req.get("password") or ""
                if not user or not pw:
                    return self._send(400, {"ok": False, "error": "Bitte Benutzername und Passwort eingeben."})
                ip, now = self.client_ip(), time.time()
                FAILED[ip] = [t for t in FAILED[ip] if now - t < 900]
                if len(FAILED[ip]) >= MAX_FAILED_LOGINS:
                    return self._send(429, {"ok": False, "error": "Zu viele Fehlversuche – bitte 15 Minuten warten."})
                try:
                    return self._send(200, session_info(create_session(load_untis(user, pw), cred=(user, pw))))
                except UntisError as e:
                    if "falsch" in str(e):
                        FAILED[ip].append(now)
                    raise

            sid = req.get("session")
            if sid not in SESSIONS:
                return self._send(401, {"ok": False, "expired": True,
                                        "error": "Sitzung abgelaufen – bitte neu anmelden."})
            if self.path == "/api/stats":
                frm, to = parse_date(req["from"]), parse_date(req["to"])
                if frm > to:
                    frm, to = to, frm
                s = SESSIONS[sid]
                return self._send(200, {"ok": True, "stats": compute_stats(s["items"], frm, to, s["grid"])})
            SESSIONS[sid]["seen"] = time.time()
            if self.path == "/api/refresh":
                refresh_session(sid)
                return self._send(200, session_info(sid))
            if self.path == "/api/logout":
                SESSIONS.pop(sid, None)
                return self._send(200, {"ok": True})
            if self.path == "/api/week":
                return self._send(200, week(sid, parse_date(req.get("date") or dt.date.today().isoformat())))
            self._send(404, {"ok": False, "error": "Nicht gefunden"})
        except UntisError as e:
            self._send(400, {"ok": False, "error": str(e)})
        except urllib.error.URLError as e:
            self._send(502, {"ok": False, "error": f"WebUntis nicht erreichbar: {e}"})
        except Exception as e:
            self._send(500, {"ok": False, "error": f"Unerwarteter Fehler: {e}"})


if __name__ == "__main__":
    srv = ThreadingHTTPServer((HOST, PORT), Handler)
    print(f"Stundenplan-Tracker läuft: http://localhost:{PORT}  (Beenden mit Strg+C)", flush=True)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass
