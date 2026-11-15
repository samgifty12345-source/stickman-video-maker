"""
Video Remix Bot - one file.

You upload a video + a reference image of your main character. The bot:
  1. cuts the video into short parts (Seedance 2.5 makes up to 30s per clip),
  2. optionally blurs the caption area of each part,
  3. sends each part to Seedance 2.5 on Krea as a *video edit* (same motion and story, new main character,
     simpler side characters, changed colors and backgrounds, captions removed),
  4. joins the new parts and lays the ORIGINAL sound/voice back on top.

Run on Railway: see the Dockerfile + requirements.txt next to this file.

Environment variables:
  KREA_API_KEY      required. Krea API token (krea.ai -> API keys). API balance is separate from app credits.
  APP_PASSWORD      optional. If set, people must type it.
  PUBLIC_URL        optional. e.g. https://my-app.up.railway.app  (Krea must be able to download your files from it)
  CHUNK_SECONDS     part length, default 15 (max 30)
  MAX_VIDEO_SECONDS longest upload allowed, default 120
  SEEDANCE_ENDPOINT override the endpoint path if Krea changes it
  PORT              set by Railway
"""
import hmac
import json
import math
import os
import re
import shutil
import subprocess
import tempfile
import threading
import time
import traceback
import urllib.error
import urllib.request
import uuid
from collections import deque

from flask import Flask, abort, jsonify, request, send_file
from PIL import Image

KREA = "https://api.krea.ai"
KREA_KEY = os.environ.get("KREA_API_KEY", "")
ENDPOINT = os.environ.get("SEEDANCE_ENDPOINT", "/generate/video/bytedance/seedance-2-5")
PASSWORD = os.environ.get("APP_PASSWORD", "")
CHUNK = max(5, min(30, int(os.environ.get("CHUNK_SECONDS", "15"))))
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


# ------------------------------------------------------------------ Krea API
def krea_call(path, body=None, timeout=60):
    req = urllib.request.Request(
        KREA + path, data=json.dumps(body).encode() if body is not None else None,
        method="POST" if body is not None else "GET",
        headers={"Authorization": "Bearer " + KREA_KEY, "Content-Type": "application/json",
                 "User-Agent": "remix-bot/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return json.loads(r.read().decode())
    except urllib.error.HTTPError as e:
        detail = re.sub(r"\s+", " ", e.read().decode(errors="ignore"))[:300]
        raise RuntimeError(f"Krea HTTP {e.code}: {detail}")


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


def generate_part(job, i, total, video_url, image_urls, prompt, resolution):
    body = {"prompt": prompt, "reference_videos": [video_url], "reference_images": image_urls,
            "resolution": resolution, "generate_audio": False}
    sub = krea_call(ENDPOINT, body)
    jid = sub.get("job_id")
    if not jid:
        raise RuntimeError(f"Krea did not return a job id: {str(sub)[:200]}")
    log(f"[remix] part {i}/{total}: Krea job {jid} started")
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
                url = generate_part(job, i + 1, n_run, f"{base}/files/{jid}/chunk_{i + 1}.mp4", image_urls,
                                    build_prompt(opts["style"], opts["simplify"], i + 1, n_run), opts["resolution"])
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
        log(f"[remix {jid}] FAILED: {traceback.format_exc()[-700:]}")
        job.update(status="error", error=str(e))


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


@app.post("/start")
def start():
    if PASSWORD and not hmac.compare_digest(request.form.get("password", ""), PASSWORD):
        return jsonify(error="Wrong password."), 403
    if not KREA_KEY:
        return jsonify(error="KREA_API_KEY is not set in Railway Variables."), 400
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
            im = Image.open(f.stream).convert("RGB")
            im.thumbnail((1536, 1536))
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


@app.get("/logs")
def logs():
    since = request.args.get("since", 0, type=int)
    with LOG_LOCK:
        items = list(LOGS)
    return jsonify(lines=[x for x in items if x[0] > since])


@app.get("/health")
def health():
    return f"ok | Krea key: {'set' if KREA_KEY else 'MISSING'}"


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
 small{color:#889}
</style></head><body><div id="wrap"><div id="main">
<h1>Video Remix Bot</h1>
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


if __name__ == "__main__":
    if not shutil.which("ffmpeg"):
        print("WARNING: ffmpeg not found.")
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 8080)))
