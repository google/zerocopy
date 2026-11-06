#!/usr/bin/env python3
"""Bounded direct Lean prefix edit/cancel experiment; writes only this package."""
import hashlib
import json
import os
import select
import shutil
import signal
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORK = HERE / "work"
LEAN = Path(os.environ.get("LEAN_BIN", "/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean"))
EVENTS = []
START = time.monotonic()
RSS_CAP_BYTES = 1_500_000_000

def sha(data):
    return hashlib.sha256(data if isinstance(data, bytes) else data.encode()).hexdigest()

def log(kind, **fields):
    EVENTS.append({"seq":len(EVENTS), "ms":round((time.monotonic()-START)*1000,1),
                   "kind":kind, **fields})

def marker(tag):
    path = '"markers.txt"'
    return ("run_cmd do\n"
            f"  let p := {path}\n"
            "  let old ← liftIO <| IO.FS.readFile p <|> pure \"\"\n"
            f"  liftIO <| IO.FS.writeFile p (old ++ \"{tag}\\n\")\n")

def source(version, value, target, gate=False):
    gate_text = ""
    if gate:
        entered = '"gate.entered"'
        released = '"gate.release"'
        gate_text = ("run_cmd do\n"
                     f"  liftIO <| IO.FS.writeFile {entered} \"entered\"\n"
                     f"  while !(← (System.FilePath.mk {released}).pathExists) do\n"
                     "    liftIO <| IO.sleep 10\n")
    return ("import Lean\nopen Lean Elab Command\n" + marker("A") +
            f"def generated : Nat := {value}\n" + gate_text +
            marker(f"B{version}") +
            f"theorem target : generated = {target} := by decide\n" + marker(f"C{version}"))

class Server:
    def __init__(self):
        self.p = subprocess.Popen([str(LEAN), "--server"], cwd=WORK,
            env=dict(os.environ, LEAN_NUM_THREADS="1"), stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0, start_new_session=True)
        self.buf = b""
        self.peak_rss = 0
        log("server_start", pid=self.p.pid)
        self.send({"jsonrpc":"2.0","id":1,"method":"initialize","params":{
            "processId":os.getpid(),"rootUri":WORK.as_uri(),"capabilities":{},
            "initializationOptions":{"hasWidgets":False}}})
        self.until(1)
        self.send({"jsonrpc":"2.0","method":"initialized","params":{}})

    def send(self, message):
        raw = json.dumps(message, separators=(",",":"), ensure_ascii=False).encode()
        self.p.stdin.write(b"Content-Length: " + str(len(raw)).encode() + b"\r\n\r\n" + raw)
        self.p.stdin.flush()
        log("send", message=message)

    def read(self, timeout=15):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            self.sample_rss()
            if b"\r\n\r\n" in self.buf:
                header, body = self.buf.split(b"\r\n\r\n",1)
                lengths = [int(h.split(b":",1)[1]) for h in header.split(b"\r\n")
                           if h.lower().startswith(b"content-length:")]
                if lengths and len(body) >= lengths[0]:
                    raw, self.buf = body[:lengths[0]], body[lengths[0]:]
                    msg = json.loads(raw)
                    log("recv", message=msg)
                    if msg.get("method") == "client/registerCapability" and "id" in msg:
                        self.send({"jsonrpc":"2.0","id":msg["id"],"result":None})
                    return msg
            ready,_,_ = select.select([self.p.stdout],[],[],min(.1,max(0,deadline-time.monotonic())))
            if ready:
                chunk = os.read(self.p.stdout.fileno(),65536)
                if not chunk: break
                self.buf += chunk
        raise TimeoutError("server read")

    def sample_rss(self):
        rows = subprocess.check_output(["ps","-axo","pid=,ppid=,rss="],text=True,timeout=2)
        parsed = []
        for line in rows.splitlines():
            fields=line.split()
            if len(fields)==3:
                parsed.append(tuple(map(int,fields)))
        members={self.p.pid}
        while True:
            more={pid for pid,ppid,_ in parsed if ppid in members}
            if more <= members: break
            members |= more
        rss=sum(kib*1024 for pid,_,kib in parsed if pid in members)
        self.peak_rss=max(self.peak_rss,rss)
        if rss > RSS_CAP_BYTES:
            raise MemoryError(f"server process-tree RSS {rss} exceeds {RSS_CAP_BYTES}")
        return rss

    def until(self, request_id, timeout=15):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            msg = self.read(max(.1,deadline-time.monotonic()))
            if msg.get("id") == request_id: return msg
        raise TimeoutError(request_id)

    def stop(self):
        if self.p.poll() is not None: return
        try:
            self.send({"jsonrpc":"2.0","id":99,"method":"shutdown","params":None})
            self.until(99,5)
            self.send({"jsonrpc":"2.0","method":"exit"})
            self.p.wait(timeout=5)
        finally:
            if self.p.poll() is None:
                os.killpg(self.p.pid, signal.SIGKILL)
                self.p.wait()
            log("server_stop", returncode=self.p.returncode,
                stderr=self.p.stderr.read().decode(errors="replace"),
                peak_sampled_rss_bytes=self.peak_rss, rss_cap_bytes=RSS_CAP_BYTES)

def markers():
    path = WORK / "markers.txt"
    return path.read_text().splitlines() if path.exists() else []

def main():
    free = shutil.disk_usage(HERE).free
    assert free >= 1_000_000_000, f"requires 1 GB free disk, got {free}"
    version = subprocess.check_output([str(LEAN),"--version"],text=True).strip()
    assert "4.30.0-rc2" in version
    WORK.mkdir(exist_ok=True)
    for name in ("markers.txt","gate.entered","gate.release"):
        (WORK/name).unlink(missing_ok=True)
    v1, v2, v3 = source(1,1,1), source(2,2,1,gate=True), source(3,3,3)
    texts = [(1,v1),(2,v2),(3,v3)]
    for number, text in texts:
        (WORK/f"V{number}.lean").write_text(text)
    (WORK/"Active.lean").write_text(v1)
    log("subject", lean_version=version, binary_sha256=sha(LEAN.read_bytes()),
        free_disk_bytes=free, source_sha256={str(n):sha(t) for n,t in texts})
    # Sequential fresh controls; remove their marker side effects before LSP.
    for number in (1,3):
        result = subprocess.run([str(LEAN),"--json",str(WORK/f"V{number}.lean")],
            cwd=WORK, env=dict(os.environ,LEAN_NUM_THREADS="1"),
            capture_output=True,text=True,timeout=15)
        log("batch", version=number, returncode=result.returncode,
            stdout=result.stdout, stderr=result.stderr, markers=markers())
    (WORK/"markers.txt").unlink(missing_ok=True)
    uri = (WORK/"Active.lean").as_uri()
    server = Server()
    try:
        server.send({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{
            "textDocument":{"uri":uri,"languageId":"lean","version":1,"text":v1}}})
        server.send({"jsonrpc":"2.0","id":10,"method":"textDocument/waitForDiagnostics",
                     "params":{"uri":uri,"version":1}})
        ready1 = server.until(10)
        log("ready",version=1,response=ready1,markers=markers())
        assert markers() == ["A","B1","C1"]

        server.send({"jsonrpc":"2.0","method":"textDocument/didChange","params":{
            "textDocument":{"uri":uri,"version":2},"contentChanges":[{"text":v2}]}})
        server.send({"jsonrpc":"2.0","id":20,"method":"textDocument/waitForDiagnostics",
                     "params":{"uri":uri,"version":2}})
        deadline=time.monotonic()+10
        while not (WORK/"gate.entered").exists() and time.monotonic()<deadline:
            server.sample_rss()
            time.sleep(.01)
        assert (WORK/"gate.entered").exists(), "v2 did not enter early-command gate"
        log("gate_entered", markers=markers(), gate_sha256=sha((WORK/"gate.entered").read_bytes()))

        server.send({"jsonrpc":"2.0","method":"textDocument/didChange","params":{
            "textDocument":{"uri":uri,"version":3},"contentChanges":[{"text":v3}]}})
        server.send({"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":20}})
        log("edit_and_cancel_sent", markers=markers())
        (WORK/"gate.release").write_text("release")
        log("gate_released", markers=markers())
        server.send({"jsonrpc":"2.0","id":21,"method":"textDocument/waitForDiagnostics",
                     "params":{"uri":uri,"version":3}})
        pending={20,21}
        deadline=time.monotonic()+20
        replies={}
        while pending and time.monotonic()<deadline:
            msg=server.read(max(.1,deadline-time.monotonic()))
            if msg.get("id") in pending:
                replies[str(msg["id"])]=msg
                pending.remove(msg["id"])
        log("wait_replies", responses=replies, pending=sorted(pending), markers=markers())
        assert 21 not in pending
        theorem_line = next(i for i,line in enumerate(v3.splitlines()) if "theorem target" in line)
        tactic_col = v3.splitlines()[theorem_line].index("decide")
        server.send({"jsonrpc":"2.0","id":22,"method":"$/lean/plainGoal","params":{
            "textDocument":{"uri":uri},"position":{"line":theorem_line,"character":tactic_col}}})
        goal = server.until(22)
        log("final_goal", position={"line":theorem_line,"character":tactic_col},
            response=goal, markers=markers())
        log("completed", markers=markers())
    finally:
        (WORK/"gate.release").write_text("release")
        server.stop()

signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError("45-second outer deadline")))
signal.alarm(45)
try: main()
except Exception as exc:
    log("fatal", error=repr(exc))
    raise
finally:
    signal.alarm(0)
    raw = json.dumps(EVENTS,indent=2,ensure_ascii=False)+"\n"
    raw = raw.replace(WORK.as_uri(),"$WORK_URI").replace(str(WORK),"$WORK").replace(str(LEAN),"$LEAN")
    (HERE/"transcript.json").write_text(raw)
