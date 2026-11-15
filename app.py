"""
Video Remix Bot - one file.

You upload a video + a reference image of your main character. The bot:
  1. cuts the video into short parts (Seedance 2 makes 4-15s per clip),
  2. optionally blurs the caption area of each part,
  3. sends each part to Seedance 2 on Krea as a *video edit* (same motion and story, new main character,
     simpler side characters, changed colors and backgrounds, captions removed),
  4. joins the new parts and lays the ORIGINAL sound/voice back on top.

Run on Railway: see the Dockerfile + requirements.txt next to this file.

Environment variables:
  (no Krea key needed)  click "Login with Krea" on the page: videos are paid with your Krea app compute units.
  KREA_API_KEY      optional fallback. Krea API token; uses the separate API balance when you are not logged in.
  TOKEN_FILE        optional. Where the Krea login is saved. Use a Railway Volume (e.g. /data/krea_oauth.json) so it
                    survives redeploys. Default is a temp file (you click Login again after each deploy).
  APP_PASSWORD      optional but recommended: the connected Krea account is shared by everyone who opens the page.
  PUBLIC_URL        optional. e.g. https://my-app.up.railway.app  (Krea downloads your clip + images from it)
  CHUNK_SECONDS     part length, default 15 (max 15, Krea limit)
  MAX_VIDEO_SECONDS longest upload allowed, default 120
  SEEDANCE_ENDPOINT / SEEDANCE_MODEL  override the API path / MCP model id if Krea changes them
  SEEDANCE_TOOL     optional. Force the exact Krea MCP tool name used to make the video (e.g. generate_video).
  PORT              set by Railway
"""
import base64
import hashlib
import hmac
import json
import math
import os
import re
import secrets
import shutil
import subprocess
import tempfile
import threading
import time
import traceback
import urllib.error
import urllib.parse
import urllib.request
import uuid
from collections import deque

from flask import Flask, abort, jsonify, request, send_file
from PIL import Image

KREA = "https://api.krea.ai"
KREA_KEY = os.environ.get("KREA_API_KEY", "")
ENDPOINT = os.environ.get("SEEDANCE_ENDPOINT", "/generate/video/bytedance/seedance-2")
MODEL_ID = os.environ.get("SEEDANCE_MODEL", "video/bytedance/seedance-2")
FORCED_TOOL = os.environ.get("SEEDANCE_TOOL", "").strip()
MCP_URL = "https://api.krea.ai/mcp"
TOKEN_FILE = os.environ.get("TOKEN_FILE", os.path.join(tempfile.gettempdir(), "krea_oauth.json"))
PASSWORD = os.environ.get("APP_PASSWORD", "")
CHUNK = max(5, min(15, int(os.environ.get("CHUNK_SECONDS", "15"))))   # Seedance 2 on Krea: 4-15s per clip
MAX_VIDEO = int(os.environ.get("MAX_VIDEO_SECONDS", "120"))
JOB_DIR = os.path.join(tempfile.gettempdir(), "remix_jobs")
os.makedirs(JOB_DIR, exist_ok=True)

LOGS = deque(maxlen=1500)
LOG_LOCK = threading.Lock()
LOG_N = [0]


def log(msg):
    with LOG_LOCK:
        LOG_N[0] += 1
        line = time.strftime("%H:%M:%S ", time.gmtime()) + str(msg)
        LOGS.append((LOG_N[0], line))
    print(line, flush=True)


# ------------------------------------------------------------------ ffmpeg helpers
def run(cmd):
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode:
        raise RuntimeError(f"{cmd[0]} failed: {r.stderr[-300:]}")
    return r.stdout.strip()


def duration(p):
    return float(run(["ffprobe", "-v", "error", "-show_entries", "format=duration", "-of", "csv=p=0", p]) or 0)


def has_audio(p):
    return bool(run(["ffprobe", "-v", "error", "-select_streams", "a", "-show_entries",
                     "stream=codec_type", "-of", "csv=p=0", p]))


def dims(p):
    w, h = run(["ffprobe", "-v", "error", "-select_streams", "v:0", "-show_entries",
                "stream=width,height", "-of", "csv=s=x:p=0", p]).split("x")[:2]
    return int(w), int(h)


# caption zone -> (top fraction, height fraction) of the frame that gets blurred
ZONES = {"bottom": (0.62, 0.38), "middle": (0.35, 0.30), "top": (0.0, 0.25)}


def make_chunk(src, dst, start, length, zone):
    vf = "fps=30,scale=w='if(gt(iw,ih),1280,720)':h=-2"
    if zone in ZONES:
        y, h = ZONES[zone]
        vf += (f",split[a][b];[b]crop=iw:ih*{h}:0:ih*{y},boxblur=25:3[bl];[a][bl]overlay=0:H*{y}")
    vf += ",format=yuv420p"
    run(["ffmpeg", "-y", "-loglevel", "error", "-ss", f"{start:.3f}", "-t", f"{length:.3f}", "-i", src,
         "-an", "-vf", vf, "-c:v", "libx264", "-preset", "veryfast", "-crf", "20", dst])


# ------------------------------------------------------------------ Krea access
# Two ways in:  (1) "Login with Krea" (OAuth through Krea's MCP server) -> billed to your Krea app compute units
#               (2) KREA_API_KEY -> billed to the separate API balance
def http(url, data=None, headers=None, method=None, form=False, timeout=60):
    body, h = None, {"User-Agent": "remix-bot/1.0", **(headers or {})}
    if data is not None:
        if form:
            body = urllib.parse.urlencode(data).encode()
            h["Content-Type"] = "application/x-www-form-urlencoded"
        else:
            body = json.dumps(data).encode()
            h["Content-Type"] = "application/json"
    req = urllib.request.Request(url, data=body, headers=h, method=method or ("POST" if body else "GET"))
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.status, dict(r.headers), r.read().decode()


def http_json(url, data=None, headers=None, form=False, timeout=60):
    try:
        return json.loads(http(url, data, headers, form=form, timeout=timeout)[2])
    except urllib.error.HTTPError as e:
        detail = re.sub(r"\s+", " ", e.read().decode(errors="ignore"))[:300]
        raise RuntimeError(f"HTTP {e.code} from {urllib.parse.urlparse(url).netloc}: {detail}")


AUTH = {"tokens": None, "clients": {}, "pending": {}, "meta": None}


def _load_auth():
    try:
        with open(TOKEN_FILE) as fh:
            d = json.load(fh)
        AUTH["tokens"], AUTH["clients"] = d.get("tokens"), d.get("clients", {})
    except (OSError, ValueError):
        pass


def _save_auth():
    try:
        with open(TOKEN_FILE, "w") as fh:
            json.dump({"tokens": AUTH["tokens"], "clients": AUTH["clients"]}, fh)
        os.chmod(TOKEN_FILE, 0o600)
    except OSError as e:
        log(f"[login] could not save the login to {TOKEN_FILE}: {e}")


def discover():
    """Find Krea's OAuth endpoints (standard MCP discovery)."""
    if AUTH["meta"]:
        return AUTH["meta"]
    urls = []
    try:
        http(MCP_URL, {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {
            "protocolVersion": "2025-06-18", "capabilities": {}, "clientInfo": {"name": "remix-bot", "version": "1"}}},
             {"Accept": "application/json, text/event-stream"})
    except urllib.error.HTTPError as e:
        m = re.search(r'resource_metadata="([^"]+)"', e.headers.get("WWW-Authenticate", ""))
        if m:
            urls.append(m.group(1))
    except OSError:
        pass
    urls += ["https://api.krea.ai/.well-known/oauth-protected-resource/mcp",
             "https://api.krea.ai/.well-known/oauth-protected-resource"]
    issuer = None
    for u in urls:
        try:
            issuer = json.loads(http(u)[2])["authorization_servers"][0]
            break
        except Exception:  # noqa
            continue
    issuer = (issuer or "https://api.krea.ai").rstrip("/")
    for u in (issuer + "/.well-known/oauth-authorization-server", issuer + "/.well-known/openid-configuration"):
        try:
            meta = json.loads(http(u)[2])
            if meta.get("authorization_endpoint") and meta.get("token_endpoint"):
                AUTH["meta"] = meta
                log(f"[login] found Krea login endpoints at {issuer}")
                return meta
        except Exception:  # noqa
            continue
    raise RuntimeError("Could not find Krea's login endpoints. Check the Live log and tell me what it says.")


def oauth_start(base):
    meta, redirect = discover(), base + "/oauth/callback"
    cid = AUTH["clients"].get(redirect)
    if not cid:
        if not meta.get("registration_endpoint"):
            raise RuntimeError("Krea does not allow apps to register automatically.")
        reg = http_json(meta["registration_endpoint"], {
            "client_name": "Video Remix Bot", "redirect_uris": [redirect], "grant_types": ["authorization_code", "refresh_token"],
            "response_types": ["code"], "token_endpoint_auth_method": "none"})
        cid = reg["client_id"]
        AUTH["clients"][redirect] = cid
        _save_auth()
    verifier = secrets.token_urlsafe(64)
    challenge = base64.urlsafe_b64encode(hashlib.sha256(verifier.encode()).digest()).rstrip(b"=").decode()
    state = secrets.token_urlsafe(16)
    AUTH["pending"] = {k: v for k, v in AUTH["pending"].items() if time.time() - v["t"] < 900}
    AUTH["pending"][state] = dict(verifier=verifier, redirect=redirect, cid=cid, t=time.time())
    q = {"response_type": "code", "client_id": cid, "redirect_uri": redirect, "code_challenge": challenge,
         "code_challenge_method": "S256", "state": state, "resource": MCP_URL}
    if meta.get("scopes_supported"):
        q["scope"] = " ".join(meta["scopes_supported"])
    return meta["authorization_endpoint"] + "?" + urllib.parse.urlencode(q)


def _store_tokens(tok, cid):
    old = AUTH["tokens"] or {}
    AUTH["tokens"] = dict(access_token=tok["access_token"], refresh_token=tok.get("refresh_token") or old.get("refresh_token"),
                          expires_at=time.time() + int(tok.get("expires_in") or 3000) - 60, client_id=cid)
    _save_auth()


def oauth_finish(code, state):
    p = AUTH["pending"].pop(state, None)
    if not p:
        raise RuntimeError("Login expired or was not started here. Click Login with Krea again.")
    tok = http_json(discover()["token_endpoint"], {
        "grant_type": "authorization_code", "code": code, "redirect_uri": p["redirect"], "client_id": p["cid"],
        "code_verifier": p["verifier"], "resource": MCP_URL}, form=True)
    _store_tokens(tok, p["cid"])
    log("[login] connected to Krea: video costs now use your Krea compute units")


def get_token():
    t = AUTH["tokens"]
    if not t:
        return None
    if time.time() < t.get("expires_at", 0):
        return t["access_token"]
    if t.get("refresh_token"):
        try:
            tok = http_json(discover()["token_endpoint"], {"grant_type": "refresh_token", "refresh_token": t["refresh_token"],
                                                           "client_id": t["client_id"], "resource": MCP_URL}, form=True)
            _store_tokens(tok, t["client_id"])
            return AUTH["tokens"]["access_token"]
        except RuntimeError as e:
            log(f"[login] refresh failed: {e}")
    AUTH["tokens"] = None
    _save_auth()
    return None


def find_key(o, keys):
    if isinstance(o, dict):
        for k in keys:
            if o.get(k) not in (None, "", [], {}):
                return o[k]
        for v in o.values():
            r = find_key(v, keys)
            if r is not None:
                return r
    elif isinstance(o, list):
        for v in o:
            r = find_key(v, keys)
            if r is not None:
                return r
    return None


def find_video_url(o):
    urls = find_key(o, ("urls",))
    if isinstance(urls, list) and urls and isinstance(urls[0], str):
        return urls[0]
    u = find_key(o, ("video_url", "url"))
    return u if isinstance(u, str) and u.startswith("http") else None


class Mcp:
    """Tiny MCP client (Streamable HTTP) for Krea's server, using the logged-in account."""

    def __init__(self):
        self.sid, self.n, self.tools = None, 0, None
        self.rpc("initialize", {"protocolVersion": "2025-06-18", "capabilities": {},
                                "clientInfo": {"name": "remix-bot", "version": "1"}})
        self._post({"jsonrpc": "2.0", "method": "notifications/initialized"})

    def _post(self, payload):
        tok = get_token()
        if not tok:
            raise RuntimeError("Not logged in to Krea. Click Login with Krea.")
        h = {"Authorization": "Bearer " + tok, "Accept": "application/json, text/event-stream",
             "MCP-Protocol-Version": "2025-06-18"}
        if self.sid:
            h["Mcp-Session-Id"] = self.sid
        try:
            _, hdrs, body = http(MCP_URL, payload, h, timeout=90)
        except urllib.error.HTTPError as e:
            raise RuntimeError(f"Krea HTTP {e.code}: {re.sub(chr(10), ' ', e.read().decode(errors='ignore'))[:250]}")
        sid = {k.lower(): v for k, v in hdrs.items()}.get("mcp-session-id")
        if sid:
            self.sid = sid
        return body.strip()

    def rpc(self, method, params=None):
        self.n += 1
        body = self._post({"jsonrpc": "2.0", "id": self.n, "method": method, "params": params or {}})
        msgs = ([json.loads(body)] if body.startswith("{") else
                [json.loads(l[5:].strip()) for l in body.splitlines() if l.startswith("data:") and l[5:].strip().startswith("{")])
        m = next((x for x in msgs if x.get("id") == self.n), msgs[-1] if msgs else None)
        if not m:
            raise RuntimeError(f"Empty reply from Krea for {method}")
        if "error" in m:
            raise RuntimeError(f"Krea error: {str(m['error'])[:250]}")
        return m.get("result", {})

    def call(self, tool, args):
        res = self.rpc("tools/call", {"name": tool, "arguments": args})
        data = res.get("structuredContent")
        if data is None:
            txt = "".join(c.get("text", "") for c in res.get("content", []) if c.get("type") == "text")
            try:
                data = json.loads(txt)
            except ValueError:
                data = {"text": txt}
        if res.get("isError"):
            raise RuntimeError(f"Krea tool error: {str(data)[:300]}")
        return data

    def tool_map(self):
        if self.tools is None:
            tools, cursor = {}, None
            while True:
                res = self.rpc("tools/list", {"cursor": cursor} if cursor else {})
                tools.update({t["name"]: t for t in res.get("tools", [])})
                cursor = res.get("nextCursor")
                if not cursor:
                    break
            self.tools = tools
        return self.tools

    def tool(self, name):
        tm = self.tool_map()
        if name not in tm:
            raise RuntimeError(f"Krea MCP has no '{name}' tool. Tools: {', '.join(tm)}")
        return tm[name]

    def pick_generate_tool(self):
        """Krea renames tools now and then, so find the one that makes videos."""
        tm = self.tool_map()
        names = list(tm)
        if FORCED_TOOL:
            if FORCED_TOOL in tm:
                return FORCED_TOOL
            raise RuntimeError(f"SEEDANCE_TOOL='{FORCED_TOOL}' is not a Krea tool. Tools: {', '.join(names)}")
        for n in ("generate", "generate_video", "video_generate", "create_video", "generate_media"):
            if n in tm:
                return n
        skip = ("ad_studio", "brand", "node", "swap", "style", "agent", "desktop", "token", "job", "plan", "balance")
        pool = [n for n in names if not any(s in n for s in skip)]
        for pred in (lambda n: "generate" in n and "video" in n,
                     lambda n: "video" in n and ("create" in n or "make" in n or "edit" in n),
                     lambda n: n.startswith("generate")):
            hit = [n for n in pool if pred(n)]
            if hit:
                return hit[0]
        raise RuntimeError("Could not find a video tool on Krea's MCP server. Tools: " + ", ".join(names)
                           + ". Set SEEDANCE_TOOL to the right name.")


_MODEL_CACHE = {}


def resolve_model(m):
    """Ask Krea's MCP which Seedance model id it really accepts (ids differ from the REST API)."""
    if "id" in _MODEL_CACHE:
        return _MODEL_CACHE["id"]
    chosen = MODEL_ID
    if not os.environ.get("SEEDANCE_MODEL"):
        try:
            lp = (m.tool("list_models").get("inputSchema") or {}).get("properties", {})
            raw = None
            for a in ({"category": "video"}, {"type": "video"}, {}):
                a = {k: v for k, v in a.items() if k in lp}
                try:
                    raw = m.call("list_models", a)
                    break
                except RuntimeError:
                    continue
            txt = json.dumps(raw) if raw is not None else ""
            found = sorted(set(re.findall(r"[A-Za-z0-9_./\-]*seedance[A-Za-z0-9_./\-]*", txt, re.I)))
            log(f"[remix] Krea Seedance models: {', '.join(found) or 'none found'}")
            if not found:
                log(f"[remix] list_models said: {txt[:1200]}")
            else:
                full = [f for f in found if "/" in f] or found
                good = [f for f in full if not re.search(r"fast|mini|lite|pro-fast", f, re.I)]
                pick = [f for f in good if re.search(r"seedance-?2", f, re.I)] or good or full
                chosen = pick[0]
        except Exception as e:  # noqa
            log(f"[remix] could not list models: {e}")
    log(f"[remix] using model id '{chosen}'")
    try:
        sp = (m.tool("get_model_schema").get("inputSchema") or {}).get("properties", {})
        key = next((k for k in ("model", "model_id", "modelId", "id") if k in sp), None)
        if key:
            sch = m.call("get_model_schema", {key: chosen})
            log(f"[remix] model schema: {json.dumps(sch)[:1500]}")
    except Exception as e:  # noqa
        log(f"[remix] schema lookup skipped: {e}")
    _MODEL_CACHE["id"] = chosen
    return chosen


def oauth_generate(job, i, total, body):
    m = Mcp()
    gname = m.pick_generate_tool()
    model_id = resolve_model(m)
    gen = m.tool(gname)
    props = (gen.get("inputSchema") or {}).get("properties", {})
    if i == 1:
        log(f"[remix] using Krea tool '{gname}'")
        log(f"[remix] it takes: {', '.join(props) or '(no schema given)'}")
        log(f"[remix] all Krea tools: {', '.join(m.tool_map())}")
    mk = next((k for k in ("model", "model_id", "modelId") if k in props), None)
    nest = next((k for k in ("params", "parameters", "input", "inputs", "body", "arguments") if k in props), None)

    def args(preflight=False):
        a = {}
        if mk:
            a[mk] = model_id
        elif not props:
            a["model"] = model_id
        if nest:
            a[nest] = dict(body)
        else:
            a.update({k: v for k, v in body.items() if not props or k in props} if props else body)
        if "sync" in props:
            a["sync"] = False                      # we poll get_job ourselves
        if preflight and "preflight" in props:
            a["preflight"] = True
        return a

    if i == 1 and "preflight" in props:          # price check before spending anything
        try:
            q = m.call(gname, args(True))
            cu, have = find_key(q, ("compute_units",)), find_key(q, ("available_compute_units",))
            log(f"[remix] cost quote: about {cu} compute units per part, you have {have}")
            if find_key(q, ("affordable",)) is False:
                raise RuntimeError(f"Not enough Krea compute units: one part costs about {cu} and you have {have}.")
        except RuntimeError as e:
            if "Not enough" in str(e):
                raise
            log(f"[remix] cost quote skipped: {e}")
    if i == 1:
        dropped = [k for k in body if props and not nest and k not in props]
        if dropped:
            log(f"[remix] WARNING: this Krea tool has no field for: {', '.join(dropped)} (not sent)")
    data = m.call(gname, args())
    url = find_video_url(data)
    jid = find_key(data, ("job_id", "jobId", "id"))
    if url and not jid:
        return url
    if not jid:
        raise RuntimeError(f"Krea did not return a job id: {str(data)[:250]}")
    log(f"[remix] part {i}/{total}: Krea job {jid} started")
    jprops = (m.tool("get_job").get("inputSchema") or {}).get("properties", {})
    jk = next((k for k in ("jobId", "job_id", "id") if k in jprops), "jobId")
    t0, fails = time.time(), 0
    while time.time() - t0 < 20 * 60:
        time.sleep(4)
        try:
            j = m.call("get_job", {jk: jid})
            fails = 0
        except RuntimeError as e:
            fails += 1
            if fails > 4:
                raise
            if "HTTP 40" in str(e):
                m = Mcp()
            continue
        st = str(find_key(j, ("status",)) or "").lower()
        job["note"] = f"Part {i}/{total}: Seedance is working ({st or 'waiting'}, {int(time.time() - t0)}s)"
        if st == "completed":
            u = find_video_url(j)
            if not u:
                raise RuntimeError(f"Krea finished but I found no video URL: {str(j)[:250]}")
            log(f"[remix] part {i}/{total}: done in {int(time.time() - t0)}s")
            return u
        if st in ("failed", "cancelled"):
            raise RuntimeError(f"Krea job {st}: {str(find_key(j, ('error', 'message')) or j)[:250]}")
    raise RuntimeError("Krea took longer than 20 minutes for one part.")


def krea_call(path, body=None, timeout=60):
    return http_json(KREA + path, body, {"Authorization": "Bearer " + KREA_KEY}, timeout=timeout)


def api_generate(job, i, total, body):
    sub = krea_call(ENDPOINT, body)
    jid = sub.get("job_id")
    if not jid:
        raise RuntimeError(f"Krea did not return a job id: {str(sub)[:200]}")
    log(f"[remix] part {i}/{total}: Krea API job {jid} started")
    t0 = time.time()
    while time.time() - t0 < 20 * 60:
        time.sleep(4)
        j = krea_call(f"/jobs/{jid}")
        st = str(j.get("status", "")).lower()
        job["note"] = f"Part {i}/{total}: Seedance is working ({st}, {int(time.time() - t0)}s)"
        if st == "completed":
            urls = (j.get("result") or {}).get("urls") or []
            if not urls:
                raise RuntimeError("Krea finished but gave no video URL.")
            log(f"[remix] part {i}/{total}: done in {int(time.time() - t0)}s")
            return urls[0]
        if st in ("failed", "cancelled"):
            raise RuntimeError(f"Krea job {st}: {str(j.get('error') or j)[:250]}")
    raise RuntimeError("Krea took longer than 20 minutes for one part.")


def build_prompt(style, simplify, idx, total):
    p = ("Edit the reference video: keep exactly the same story, actions, camera movement, framing, pacing and "
         "timing as the reference video. Replace the main character with the character shown in the reference "
         "image(s); keep that character's face, outfit and proportions identical in every shot. ")
    if simplify:
        p += ("Every other character becomes a simpler, flatter, lower-detail design in the same art style as the "
              "main character. ")
    p += ("Change the color palette and redesign the backgrounds so the scene looks clearly different from the "
          "reference video, while the layout and action stay readable. ")
    if style:
        p += f"Style notes: {style}. "
    p += "Remove all captions, subtitles, on-screen text, watermarks and logos, and do not add any text."
    if total > 1:
        p += f" This is part {idx} of {total} of one continuous video; keep the same look in every part."
    return p


ASPECTS = {"16:9": 16 / 9, "4:3": 4 / 3, "1:1": 1.0, "3:4": 3 / 4, "9:16": 9 / 16, "21:9": 21 / 9}


def nearest_aspect(w, h):
    r = w / h
    return min(ASPECTS, key=lambda k: abs(ASPECTS[k] - r))


def generate_part(job, i, total, video_url, image_urls, prompt, resolution, seconds, aspect):
    body = {"prompt": prompt, "reference_videos": [video_url], "reference_images": image_urls[:9],
            "resolution": resolution, "duration": max(4, min(15, round(seconds, 1))), "aspect_ratio": aspect}
    if AUTH["tokens"]:
        return oauth_generate(job, i, total, body)
    return api_generate(job, i, total, body)


def download(url, dst):
    req = urllib.request.Request(url, headers={"User-Agent": "remix-bot/1.0"})
    with urllib.request.urlopen(req, timeout=120) as r, open(dst, "wb") as f:
        shutil.copyfileobj(r, f)


# ------------------------------------------------------------------ the job
app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = 300 * 1024 * 1024
JOBS = {}
LOCK = threading.Semaphore(1)       # one remix at a time


def worker(jid, base, opts):
    job, wd = JOBS[jid], os.path.join(JOB_DIR, jid)
    try:
        with LOCK:
            job["status"] = "working"
            src = os.path.join(wd, "source.mp4")
            dur = duration(src)
            n = max(1, math.ceil(dur / CHUNK))
            length = dur / n
            if opts["test_first"]:
                n_run = 1
            else:
                n_run = n
            log(f"[remix {jid}] {dur:.1f}s video -> {n} part(s) of {length:.1f}s, running {n_run}")
            image_urls = [f"{base}/files/{jid}/{f}" for f in sorted(os.listdir(wd)) if f.startswith("ref_")]
            outs = []
            for i in range(n_run):
                job["progress"] = i / n_run
                job["note"] = f"Part {i + 1}/{n_run}: preparing the clip..."
                chunk = os.path.join(wd, f"chunk_{i + 1}.mp4")
                make_chunk(src, chunk, i * length, length, opts["zone"])
                cw, ch = dims(chunk)
                url = generate_part(job, i + 1, n_run, f"{base}/files/{jid}/chunk_{i + 1}.mp4", image_urls,
                                    build_prompt(opts["style"], opts["simplify"], i + 1, n_run), opts["resolution"],
                                    length, nearest_aspect(cw, ch))
                out = os.path.join(wd, f"out_{i + 1}.mp4")
                download(url, out)
                outs.append((chunk, out))
            job["note"], job["progress"] = "Joining the parts and adding the original sound...", 0.95
            w, h = dims(outs[0][0])
            fixed = []
            for k, (_, out) in enumerate(outs, 1):          # same size/fps so the parts join cleanly
                fx = os.path.join(wd, f"fix_{k}.mp4")
                run(["ffmpeg", "-y", "-loglevel", "error", "-i", out, "-an", "-vf",
                     f"scale={w}:{h},fps=30,format=yuv420p", "-c:v", "libx264", "-preset", "veryfast",
                     "-crf", "19", fx])
                fixed.append(fx)
            lst = os.path.join(wd, "list.txt")
            with open(lst, "w") as fh:
                fh.write("".join(f"file '{p}'\n" for p in fixed))
            joined = os.path.join(wd, "joined.mp4")
            run(["ffmpeg", "-y", "-loglevel", "error", "-f", "concat", "-safe", "0", "-i", lst, "-c", "copy", joined])
            final = os.path.join(wd, "final.mp4")
            if has_audio(src):                               # put the ORIGINAL sound on the new video
                run(["ffmpeg", "-y", "-loglevel", "error", "-i", joined, "-i", src, "-map", "0:v", "-map", "1:a",
                     "-c:v", "copy", "-c:a", "aac", "-b:a", "192k", "-shortest", "-movflags", "+faststart", final])
            else:
                shutil.copy(joined, final)
            job.update(status="done", progress=1.0, note="Done! Original sound is on the new video.")
            log(f"[remix {jid}] DONE")
    except Exception as e:  # noqa
        log(f"[remix {jid}] FAILED: {str(e)[:900]}")
        print(traceback.format_exc(), flush=True)
        job.update(status="error", error=str(e)[:900])


def cleanup():
    now = time.time()
    for jid in list(JOBS):
        if now - JOBS[jid]["created"] > 7200:
            JOBS.pop(jid, None)
            shutil.rmtree(os.path.join(JOB_DIR, jid), ignore_errors=True)


def public_base():
    env = os.environ.get("PUBLIC_URL", "").rstrip("/")
    if env:
        return env
    proto = request.headers.get("X-Forwarded-Proto", "https")
    return f"{proto}://{request.headers.get('X-Forwarded-Host', request.host)}"


def fit_reference(im):
    """Seedance wants reference images with aspect ratio 0.4-2.5 and a decent size: pad/upscale if needed."""
    w, h = im.size
    lo, hi = 0.5, 2.0                                   # stay safely inside 0.4-2.5
    r = w / h
    if r > hi or r < lo:
        nw, nh = (w, math.ceil(w / hi)) if r > hi else (math.ceil(h * lo), h)
        bg = im.getpixel((0, 0))                         # fill with the picture's corner colour
        canvas = Image.new("RGB", (nw, nh), bg)
        canvas.paste(im, ((nw - w) // 2, (nh - h) // 2))
        im = canvas
    w, h = im.size
    if min(w, h) < 512:                                  # tiny images get rejected: scale up
        sc = 512 / min(w, h)
        im = im.resize((round(w * sc), round(h * sc)), Image.LANCZOS)
    im.thumbnail((1536, 1536))
    return im


@app.post("/start")
def start():
    if PASSWORD and not hmac.compare_digest(request.form.get("password", ""), PASSWORD):
        return jsonify(error="Wrong password."), 403
    if not (AUTH["tokens"] or KREA_KEY):
        return jsonify(error="Click \"Login with Krea\" first."), 400
    cleanup()
    if sum(1 for j in JOBS.values() if j["status"] in ("queued", "working")) >= 2:
        return jsonify(error="Busy with another video, try again in a few minutes."), 429
    vid, imgs = request.files.get("video"), [f for f in request.files.getlist("images") if f and f.filename]
    if not vid or not vid.filename:
        return jsonify(error="Please choose a video."), 400
    if not imgs:
        return jsonify(error="Please add at least one reference image of your main character."), 400
    jid = uuid.uuid4().hex[:12]
    wd = os.path.join(JOB_DIR, jid)
    os.makedirs(wd)
    try:
        raw = os.path.join(wd, "upload.bin")
        vid.save(raw)
        run(["ffmpeg", "-y", "-loglevel", "error", "-i", raw, "-c:v", "libx264", "-preset", "veryfast",
             "-crf", "18", "-c:a", "aac", "-pix_fmt", "yuv420p", os.path.join(wd, "source.mp4")])
        os.remove(raw)
        d = duration(os.path.join(wd, "source.mp4"))
        if d < 4:
            raise RuntimeError("The video must be at least 4 seconds long.")
        if d > MAX_VIDEO:
            raise RuntimeError(f"The video is {d:.0f}s; the limit is {MAX_VIDEO}s (MAX_VIDEO_SECONDS).")
        for k, f in enumerate(imgs[:8], 1):
            im = fit_reference(Image.open(f.stream).convert("RGB"))
            im.save(os.path.join(wd, f"ref_{k}.jpg"), quality=92)
    except Exception as e:  # noqa
        shutil.rmtree(wd, ignore_errors=True)
        return jsonify(error=f"Could not read your files: {str(e)[:200]}"), 400
    opts = dict(style=(request.form.get("style") or "").strip()[:400],
                simplify=request.form.get("simplify") == "on",
                zone=request.form.get("zone") if request.form.get("zone") in ZONES else "none",
                resolution=request.form.get("resolution") if request.form.get("resolution") in ("480p", "720p", "1080p") else "720p",
                test_first=request.form.get("test_first") == "on")
    JOBS[jid] = dict(status="queued", progress=0.0, created=time.time(), note="Waiting in line...")
    log(f"[remix {jid}] uploaded: {d:.1f}s video, {len(imgs)} image(s), opts={opts}")
    threading.Thread(target=worker, args=(jid, public_base(), opts), daemon=True).start()
    return jsonify(id=jid)


@app.get("/status/<jid>")
def status(jid):
    j = JOBS.get(jid)
    if not j:
        abort(404)
    return jsonify(status=j["status"], progress=j["progress"], note=j.get("note", ""), error=j.get("error"))


@app.get("/files/<jid>/<name>")
def files(jid, name):          # Krea downloads the clip + reference images from here
    if jid not in JOBS or not re.fullmatch(r"(chunk_\d+\.mp4|ref_\d+\.jpg)", name):
        abort(404)
    p = os.path.join(JOB_DIR, jid, name)
    if not os.path.exists(p):
        abort(404)
    return send_file(p, mimetype="video/mp4" if name.endswith(".mp4") else "image/jpeg", conditional=True)


@app.get("/result/<jid>")
def result(jid):
    p = os.path.join(JOB_DIR, jid, "final.mp4")
    if jid not in JOBS or JOBS[jid]["status"] != "done" or not os.path.exists(p):
        abort(404)
    return send_file(p, mimetype="video/mp4", conditional=True)


@app.post("/login")
def login():
    if PASSWORD and not hmac.compare_digest(request.form.get("password", ""), PASSWORD):
        return jsonify(error="Type the password first."), 403
    try:
        return jsonify(url=oauth_start(public_base()))
    except Exception as e:  # noqa
        log(f"[login] FAILED: {e}")
        return jsonify(error=str(e)), 500


@app.get("/oauth/callback")
def oauth_callback():
    if request.args.get("error"):
        return ("", 302, {"Location": "/?autherror=" + urllib.parse.quote(request.args.get("error_description") or request.args["error"])})
    try:
        oauth_finish(request.args.get("code", ""), request.args.get("state", ""))
        return ("", 302, {"Location": "/?connected=1"})
    except Exception as e:  # noqa
        log(f"[login] FAILED: {e}")
        return ("", 302, {"Location": "/?autherror=" + urllib.parse.quote(str(e)[:200])})


@app.post("/logout")
def logout():
    if PASSWORD and not hmac.compare_digest(request.form.get("password", ""), PASSWORD):
        return jsonify(error="Type the password first."), 403
    AUTH["tokens"] = None
    _save_auth()
    log("[login] disconnected from Krea")
    return jsonify(ok=True)


@app.get("/auth/status")
def auth_status():
    return jsonify(connected=bool(AUTH["tokens"]), api_key=bool(KREA_KEY))


@app.get("/logs")
def logs():
    since = request.args.get("since", 0, type=int)
    with LOG_LOCK:
        items = list(LOGS)
    return jsonify(lines=[x for x in items if x[0] > since])


@app.get("/health")
def health():
    return f"ok | Krea login: {'connected' if AUTH['tokens'] else 'not connected'} | API key: {'set' if KREA_KEY else 'none'}"


PAGE = """<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Video Remix Bot</title>
<style>
 body{font-family:system-ui,sans-serif;background:#0f1220;color:#eef;max-width:1200px;margin:0 auto;padding:16px}
 #wrap{display:flex;gap:20px;flex-wrap:wrap;align-items:flex-start} #main{flex:1 1 440px;max-width:620px;min-width:0} #side{flex:1 1 360px;min-width:0;position:sticky;top:10px}
 #log{background:#080a14;border:1px solid #334;border-radius:8px;height:80vh;overflow:auto;font:12px/1.5 ui-monospace,Consolas,monospace;padding:8px;white-space:pre-wrap;word-break:break-word;color:#b8c4e0} #log .err{color:#ff8a8a} #log .ok{color:#7be0a0}
 h1{font-size:1.5rem} label{display:block;margin:12px 0 4px;font-size:.9rem;color:#aab}
 input,select,textarea{width:100%;padding:10px;border-radius:8px;border:1px solid #334;background:#181d33;color:#fff;font-size:1rem;box-sizing:border-box}
 .row{display:grid;grid-template-columns:1fr 1fr;gap:10px} .chk{display:flex;gap:8px;align-items:center;margin-top:14px} .chk input{width:auto}
 button{margin-top:18px;width:100%;padding:14px;border:0;border-radius:10px;background:#ff5a4d;color:#fff;font-size:1.1rem;font-weight:700} button:disabled{opacity:.5}
 .bar{height:10px;background:#252b48;border-radius:5px;margin-top:16px;overflow:hidden;display:none} .bar div{height:100%;width:0;background:#4ad98a}
 #msg{margin-top:10px;color:#cdd} video{width:100%;margin-top:14px;border-radius:10px;background:#000} a.dl{display:inline-block;margin-top:10px;color:#8fd3ff}
 small{color:#889} #conn{background:#181d33;border:1px solid #334;border-radius:10px;padding:10px 12px;margin:10px 0;display:flex;gap:10px;align-items:center;justify-content:space-between}
 #conn button{margin:0;width:auto;padding:8px 14px;font-size:.9rem;background:#3b6cff}
</style></head><body><div id="wrap"><div id="main">
<h1>Video Remix Bot</h1>
<div id="conn"><span>Krea: <b id="cs">checking...</b></span><button type="button" id="cb">Login with Krea</button></div>
<form id="f">
 <label>1. Your video (4 to __MAXV__ seconds)</label><input type="file" name="video" accept="video/*" required>
 <label>2. Reference image(s) of your main character</label><input type="file" name="images" accept="image/*" multiple required>
 <small>One clear picture is enough. More angles = more consistent character.</small>
 <label>3. What should change? (colors, backgrounds, style)</label>
 <textarea name="style" rows="3" maxlength="400" placeholder="e.g. neon purple and orange colors, new backgrounds: futuristic city and desert, flat cartoon look"></textarea>
 <div class="chk"><input type="checkbox" name="simplify" id="sm" checked><label for="sm" style="margin:0">Make the other characters simpler (based on the main character's style)</label></div>
 <div class="row">
  <div><label>Where are the captions in your video?</label><select name="zone"><option value="bottom">Bottom</option><option value="middle">Middle</option><option value="top">Top</option><option value="none">No captions</option></select></div>
  <div><label>Quality</label><select name="resolution"><option value="480p">480p (cheapest)</option><option value="720p" selected>720p</option><option value="1080p">1080p (most expensive)</option></select></div>
 </div>
 <div class="chk"><input type="checkbox" name="test_first" id="tf" checked><label for="tf" style="margin:0">Test run: only remix the first part (saves money while you check the look)</label></div>
 __PW__
 <button id="go">Remix my video</button>
</form>
<div class="bar" id="bar"><div id="fill"></div></div><div id="msg"></div><div id="out"></div>
</div>
<div id="side"><h2 style="font-size:1rem">Live log</h2><div id="log">Waiting for activity...</div></div></div>
<script>
const f=document.getElementById('f'),go=document.getElementById('go'),bar=document.getElementById('bar'),fill=document.getElementById('fill'),msg=document.getElementById('msg'),out=document.getElementById('out');
f.addEventListener('submit',async e=>{
 e.preventDefault(); go.disabled=true; out.innerHTML=''; bar.style.display='block'; fill.style.width='3%'; msg.textContent='Uploading... (big videos take a moment)';
 try{
  const r=await fetch('/start',{method:'POST',body:new FormData(f)}); const j=await r.json();
  if(!r.ok){msg.textContent=j.error||'Something went wrong.'; go.disabled=false; bar.style.display='none'; return;}
  poll(j.id);
 }catch(err){msg.textContent='Could not reach the server.'; go.disabled=false;}
});
async function poll(id){
 try{
  const r=await fetch('/status/'+id); if(!r.ok) throw new Error('lost'); const j=await r.json();
  msg.textContent=j.note||'';
  if(j.status==='done'){fill.style.width='100%'; out.innerHTML='<video src="/result/'+id+'" controls autoplay loop playsinline></video><a class="dl" href="/result/'+id+'" download="remix.mp4">Download MP4</a>'; go.disabled=false; return;}
  if(j.status==='error'){msg.textContent='Error: '+j.error; go.disabled=false; return;}
  fill.style.width=Math.max(3,Math.round(j.progress*100))+'%'; setTimeout(()=>poll(id),2500);
 }catch(err){msg.textContent='Lost connection to the job. Try again.'; go.disabled=false;}
}
const cs=document.getElementById('cs'),cb=document.getElementById('cb'); let isConn=false;
async function conn(){
 try{const j=await (await fetch('/auth/status')).json(); isConn=j.connected;
  cs.textContent=j.connected?'connected (videos use your Krea compute units)':(j.api_key?'not logged in (using API balance)':'not connected');
  cs.style.color=j.connected?'#7be0a0':'#ffd479'; cb.textContent=j.connected?'Disconnect':'Login with Krea';}catch(e){}
}
cb.onclick=async()=>{
 const fd=new FormData(); const pw=f.querySelector('[name=password]'); if(pw) fd.append('password',pw.value);
 const r=await fetch(isConn?'/logout':'/login',{method:'POST',body:fd}); const j=await r.json();
 if(!r.ok){msg.textContent=j.error||'Could not start the login.'; return;}
 if(j.url) location.href=j.url; else conn();
};
const qs=new URLSearchParams(location.search);
if(qs.get('autherror')) msg.textContent='Krea login failed: '+qs.get('autherror');
if(qs.get('connected')) msg.textContent='Connected to Krea!';
conn();
let last=0; const L=document.getElementById('log');
async function logs(){
 try{const r=await fetch('/logs?since='+last); const j=await r.json(); if(j.lines.length&&last===0) L.innerHTML='';
  for(const [n,l] of j.lines){const d=document.createElement('div'); d.textContent=l;
   if(/error|failed|traceback|HTTP [45]/i.test(l)) d.className='err'; else if(/DONE|done in/.test(l)) d.className='ok'; L.appendChild(d); last=n;}
  if(j.lines.length) L.scrollTop=L.scrollHeight;}catch(e){}
 setTimeout(logs,1500);
}
logs();
</script></body></html>"""


@app.get("/")
def index():
    pw = '<label>Password</label><input type="password" name="password" required>' if PASSWORD else ""
    return PAGE.replace("__PW__", pw).replace("__MAXV__", str(MAX_VIDEO))


_load_auth()

if __name__ == "__main__":
    if not shutil.which("ffmpeg"):
        print("WARNING: ffmpeg not found.")
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 8080)))
