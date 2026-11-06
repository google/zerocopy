#!/usr/bin/env python3
"""Bounded, direct Lean 4 server RPC lifetime and historical-query probe."""
import hashlib
import json
import os
import select
import signal
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
WORK = ROOT / "work"
LEAN = Path(os.environ["LEAN_BIN"]).resolve()
T0 = time.monotonic()
EVENTS = []
SERVERS = []
V1 = "theorem demo (n : Nat) (h : n = 7) : n + 1 = 8 := by\n  exact ?_\n"
V2 = "theorem demo (n : Nat) (h : n = 7) : n + 1 = 9 := by\n  exact ?_\n"
V3 = "theorem demo (n : Nat) (h : n = 7) : n + 1 = 10 := by\n  exact ?_\n"
SLOW = '''import Lean
theorem demo : True := by
  run_tac do
    IO.FS.writeFile "gate.entered" "1"
    while !(← (System.FilePath.mk "gate.release").pathExists) do
      IO.sleep 10
  exact ?_
'''
FAST = "theorem demo : False := by\n  exact ?_\n"


def sha(data):
    return hashlib.sha256(data if isinstance(data, bytes) else data.encode()).hexdigest()


def log(kind, **kw):
    EVENTS.append(dict(seq=len(EVENTS), ms=round((time.monotonic()-T0)*1000, 1), kind=kind, **kw))


class Server:
    def __init__(self, label):
        self.label, self.buf, self.n = label, b"", 10
        self.p = subprocess.Popen([str(LEAN), "--server"], cwd=WORK,
            env=dict(os.environ, LEAN_NUM_THREADS="1"), stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0)
        SERVERS.append(self)
        log("start", server=label, pid=self.p.pid)
        self.send(dict(jsonrpc="2.0", id=1, method="initialize", params=dict(
            processId=os.getpid(), rootUri=WORK.as_uri(), capabilities={},
            initializationOptions={"hasWidgets": False})))
        self.until(1)
        self.send(dict(jsonrpc="2.0", method="initialized", params={}))

    def send(self, msg):
        raw = json.dumps(msg, separators=(",", ":")).encode()
        self.p.stdin.write(b"Content-Length: " + str(len(raw)).encode() + b"\r\n\r\n" + raw)
        self.p.stdin.flush()
        log("client", server=self.label, message=msg)

    def read(self, timeout=15):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            if b"\r\n\r\n" in self.buf:
                header, body = self.buf.split(b"\r\n\r\n", 1)
                sizes = [int(x.split(b":", 1)[1]) for x in header.split(b"\r\n")
                         if x.lower().startswith(b"content-length:")]
                if sizes and len(body) >= sizes[0]:
                    raw, self.buf = body[:sizes[0]], body[sizes[0]:]
                    msg = json.loads(raw)
                    log("server", server=self.label, message=msg)
                    if msg.get("method") == "client/registerCapability" and "id" in msg:
                        self.send(dict(jsonrpc="2.0", id=msg["id"], result=None))
                    return msg
            ready, _, _ = select.select([self.p.stdout], [], [], min(.1, max(0, end-time.monotonic())))
            if ready:
                chunk = os.read(self.p.stdout.fileno(), 65536)
                if not chunk:
                    break
                self.buf += chunk
        raise TimeoutError(f"{self.label} read")

    def until(self, rid, timeout=15):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            msg = self.read(max(.1, end-time.monotonic()))
            if msg.get("id") == rid:
                return msg
        raise TimeoutError(f"{self.label} request {rid}")

    def request(self, method, params, rid=None):
        if rid is None:
            rid, self.n = self.n, self.n + 1
        t = time.monotonic()
        self.send(dict(jsonrpc="2.0", id=rid, method=method, params=params))
        result = self.until(rid)
        log("latency", server=self.label, method=method, rid=rid,
            elapsed_ms=round((time.monotonic()-t)*1000, 1))
        return result

    def open(self, file, text, ver=1):
        uri = file.as_uri()
        self.send(dict(jsonrpc="2.0", method="textDocument/didOpen", params={"textDocument":
            dict(uri=uri, languageId="lean", version=ver, text=text)}))
        return self.wait(uri, ver)

    def edit(self, uri, text, ver):
        self.send(dict(jsonrpc="2.0", method="textDocument/didChange", params={
            "textDocument": dict(uri=uri, version=ver), "contentChanges": [dict(text=text)]}))
        return self.wait(uri, ver)

    def wait(self, uri, ver):
        return self.request("textDocument/waitForDiagnostics", dict(uri=uri, version=ver))

    def goal(self, uri, line, col, ver=None, rid=None):
        doc = dict(uri=uri)
        if ver is not None:
            doc["version"] = ver
        return self.request("$/lean/plainGoal", dict(textDocument=doc,
            position=dict(line=line, character=col)), rid)

    def connect(self, uri):
        return self.request("$/lean/rpc/connect", dict(uri=uri))

    def rpc(self, uri, sid, line, col, rid=None):
        pos = dict(line=line, character=col)
        return self.request("$/lean/rpc/call", dict(textDocument=dict(uri=uri), position=pos,
            sessionId=sid, method="Lean.Widget.getInteractiveGoals",
            params=dict(textDocument=dict(uri=uri), position=pos)), rid)

    def close(self, uri):
        self.send(dict(jsonrpc="2.0", method="textDocument/didClose",
            params=dict(textDocument=dict(uri=uri))))

    def stop(self):
        if self.p.poll() is not None:
            return
        try:
            self.request("shutdown", None, 99)
            self.send(dict(jsonrpc="2.0", method="exit"))
            self.p.wait(timeout=5)
        except Exception as exc:
            log("stop_exception", server=self.label, error=repr(exc))
            self.p.kill()
            self.p.wait()
        log("stop", server=self.label, rc=self.p.returncode, pid=self.p.pid,
            stderr=self.p.stderr.read().decode(errors="replace"))


def child_pids(parent):
    p = subprocess.run(["ps", "-axo", "pid=,ppid=,rss="], capture_output=True, text=True)
    rows = [list(map(int, line.split())) for line in p.stdout.splitlines() if len(line.split()) == 3]
    return [(pid, rss*1024) for pid, ppid, rss in rows if ppid == parent]


def live_pids(pids):
    if not pids:
        return []
    p = subprocess.run(["ps", "-p", ",".join(str(x) for x in pids),
                        "-o", "pid=,ppid=,stat=,rss="], capture_output=True, text=True)
    return p.stdout.splitlines()


def run():
    WORK.mkdir(exist_ok=True)
    log("subject", lean_version=subprocess.check_output([str(LEAN), "--version"], text=True).strip(),
        lean_sha256=sha(LEAN.read_bytes()), source_sha256={k: sha(v) for k,v in
            dict(v1=V1,v2=V2,v3=V3,slow=SLOW,fast=FAST).items()})
    f = WORK / "Proof.lean"
    hist = WORK / "Historical.lean"
    f.write_text(V1); hist.write_text(V1)
    s = Server("lifecycle")
    uri = f.as_uri()
    s.open(f,V1)
    sid1 = s.connect(uri)["result"]["sessionId"]
    initial = s.rpc(uri,sid1,1,9)
    ctx = initial.get("result",{}).get("goals",[{}])[0].get("ctx")
    log("retained", session=sid1, context_ref=ctx, plain_json_sha256=sha(json.dumps(initial,sort_keys=True)))
    s.edit(uri,V2,2)
    old_session_after_edit=s.rpc(uri,sid1,1,9)
    s.send(dict(jsonrpc="2.0",method="$/lean/rpc/release",params=dict(uri=uri,sessionId=sid1,refs=[ctx])))
    log("after_edit", old_session_result=old_session_after_edit)
    s.close(uri)
    s.open(f,V3,1)
    stale=s.rpc(uri,sid1,1,9)
    sid2=s.connect(uri)["result"]["sessionId"]
    new=s.rpc(uri,sid2,1,9)
    log("after_reopen", old=stale,new=new,old_sid=sid1,new_sid=sid2,
        child_pids=child_pids(s.p.pid))
    # Separate URI retains exact V1 bytes while primary URI advances to V3.
    t=time.monotonic();s.open(hist,V1); open_ms=round((time.monotonic()-t)*1000,1)
    historical=s.goal(hist.as_uri(),1,9,ver=1)
    current=s.goal(uri,1,9,ver=1)
    log("historical", source_bytes=len(V1.encode()), open_ms=open_ms,
        historical=historical,current=current,children=child_pids(s.p.pid))
    lifecycle_pids=[pid for pid,_ in child_pids(s.p.pid)]
    s.stop()
    log("clean_after",watchdog_rc=s.p.returncode,worker_pids=lifecycle_pids,
        live_prior_pids=live_pids(lifecycle_pids))
    # New server and same URI/version/request number; old sid has no authority.
    fresh=Server("fresh")
    fresh.open(f,V3)
    cross=fresh.rpc(uri,sid2,1,9,rid=50)
    fresh_sid=fresh.connect(uri)["result"]["sessionId"]
    fresh_rpc=fresh.rpc(uri,fresh_sid,1,9,rid=51)
    log("fresh_session", cross=cross,fresh=fresh_rpc,old_sid=sid2,new_sid=fresh_sid)
    # Kill only the file worker; ask the watchdog to replace it.
    worker_before=child_pids(fresh.p.pid)
    if len(worker_before) == 1:
        os.kill(worker_before[0][0], signal.SIGKILL)
        time.sleep(.2)
        try:
            after_crash_old=fresh.rpc(uri,fresh_sid,1,9)
            after_crash_connect=fresh.connect(uri)
            crash_sid=after_crash_connect.get("result",{}).get("sessionId")
            after_crash_new=fresh.rpc(uri,crash_sid,1,9) if crash_sid is not None else None
            log("worker_crash", before=worker_before,after=child_pids(fresh.p.pid),
                old_session=after_crash_old,new_connect=after_crash_connect,new_session=after_crash_new)
        except Exception as exc:
            log("worker_crash_unresolved", before=worker_before, after=child_pids(fresh.p.pid),
                error=repr(exc))
        try:
            fresh.close(uri)
            reopened=fresh.open(f,V3,1)
            after_reopen_connect=fresh.connect(uri)
            after_reopen_sid=after_reopen_connect.get("result",{}).get("sessionId")
            after_reopen_goal=fresh.rpc(uri,after_reopen_sid,1,9) if after_reopen_sid else None
            log("worker_crash_recovery",wait=reopened,connect=after_reopen_connect,
                goal=after_reopen_goal,children=child_pids(fresh.p.pid))
        except Exception as exc:
            log("worker_crash_recovery_unresolved",error=repr(exc),children=child_pids(fresh.p.pid))
    else:
        log("worker_crash_unavailable", before=worker_before)
    fresh.stop()
    # Causal late reply across process replacement. Gate makes old request in flight.
    gate=WORK/"gate.release"; entered=WORK/"gate.entered"
    gate.unlink(missing_ok=True);entered.unlink(missing_ok=True)
    slowfile=WORK/"Slow.lean";slowfile.write_text(SLOW)
    old=Server("old-gated")
    old.send(dict(jsonrpc="2.0",method="textDocument/didOpen",params={"textDocument":
        dict(uri=slowfile.as_uri(),languageId="lean",version=1,text=SLOW)}))
    deadline=time.monotonic()+15
    while not entered.exists() and time.monotonic()<deadline:
        time.sleep(.01)
    if not entered.exists():
        raise TimeoutError("gate did not enter")
    old.send(dict(jsonrpc="2.0",id=50,method="$/lean/plainGoal",params={
        "textDocument":dict(uri=slowfile.as_uri()),"position":dict(line=5,character=8)}))
    replacement=Server("replacement")
    replacement.open(slowfile,FAST,1)
    fast_goal=replacement.goal(slowfile.as_uri(),1,9,ver=1,rid=50)
    gate.write_text("release")
    old_goal=old.until(50,15)
    log("late_reply", old_response=old_goal,new_response=fast_goal,
        old_pid=old.p.pid,new_pid=replacement.p.pid,same_request_id=50,
        same_uri=slowfile.as_uri(),same_version=1)
    old.stop();replacement.stop()
    # Request cancellation while the worker is blocked in an elaborator tactic.
    gate.unlink(missing_ok=True);entered.unlink(missing_ok=True)
    cancelled=Server("rpc-cancel")
    cancelled.send(dict(jsonrpc="2.0",method="textDocument/didOpen",params={"textDocument":
        dict(uri=slowfile.as_uri(),languageId="lean",version=1,text=SLOW)}))
    deadline=time.monotonic()+15
    while not entered.exists() and time.monotonic()<deadline:
        time.sleep(.01)
    if not entered.exists():raise TimeoutError("cancel gate did not enter")
    try:
        cancel_sid=cancelled.connect(slowfile.as_uri())["result"]["sessionId"]
        rpc_params=dict(textDocument=dict(uri=slowfile.as_uri()),
            position=dict(line=5,character=8),sessionId=cancel_sid,
            method="Lean.Widget.getInteractiveGoals",
            params=dict(textDocument=dict(uri=slowfile.as_uri()),position=dict(line=5,character=8)))
        cancelled.send(dict(jsonrpc="2.0",id=60,method="$/lean/rpc/call",params=rpc_params))
        cancelled.send(dict(jsonrpc="2.0",method="$/cancelRequest",params=dict(id=60)))
        gate.write_text("release")
        cancelled_result=cancelled.until(60,10)
        after_cancel=cancelled.rpc(slowfile.as_uri(),cancel_sid,5,8)
        log("rpc_cancel",response=cancelled_result,session_after=after_cancel)
    except Exception as exc:
        gate.write_text("release")
        log("rpc_cancel_unresolved",error=repr(exc))
    cancelled.stop()
    # Forced termination while the tactic gate holds an old worker.
    gate.unlink(missing_ok=True);entered.unlink(missing_ok=True)
    forced=Server("forced-gated")
    forced.send(dict(jsonrpc="2.0",method="textDocument/didOpen",params={"textDocument":
        dict(uri=slowfile.as_uri(),languageId="lean",version=1,text=SLOW)}))
    deadline=time.monotonic()+15
    while not entered.exists() and time.monotonic()<deadline:
        time.sleep(.01)
    if not entered.exists():raise TimeoutError("forced gate did not enter")
    children=child_pids(forced.p.pid)
    log("forced_before", children=children)
    forced.p.kill();forced.p.wait(timeout=5)
    gate.write_text("release")
    time.sleep(.2)
    log("forced_after", watchdog_rc=forced.p.returncode,
        surviving_direct_children=child_pids(forced.p.pid), prior_children=children,
        live_prior_pids=live_pids([pid for pid,_ in children]),
        stderr=forced.p.stderr.read().decode(errors="replace"))
    log("completed")


try:
    run()
except Exception as exc:
    log("fatal",error=repr(exc))
    raise
finally:
    for s in SERVERS:
        if s.p.poll() is None:
            s.p.kill();s.p.wait();log("cleanup_kill",server=s.label,pid=s.p.pid)
    raw=json.dumps(EVENTS,indent=2)+"\n"
    raw=raw.replace(WORK.as_uri(),"$WORK_URI").replace(str(WORK),"$WORK")
    raw=raw.replace(str(LEAN),"$LEAN_BIN")
    (ROOT/"transcript.json").write_text(raw)
