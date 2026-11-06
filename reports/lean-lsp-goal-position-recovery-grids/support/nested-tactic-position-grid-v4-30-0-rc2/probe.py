#!/usr/bin/env python3
"""Direct Lean batch/LSP position grid; writes only this report's support files."""
import hashlib
import json
import os
import select
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "Nested.lean"
LEAN = Path(os.environ.get("LEAN_BIN", "/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean"))
TEXT = SOURCE.read_text()
URI = SOURCE.as_uri()
EVENTS = []
START = time.monotonic()

def sha(data):
    if isinstance(data, str): data = data.encode()
    return hashlib.sha256(data).hexdigest()

def record(kind, **fields):
    EVENTS.append({"kind": kind, "seq": len(EVENTS), "ms": round((time.monotonic()-START)*1000, 1), **fields})

def position(needle, occurrence=0, offset=0):
    hits = [(i, line, line.index(needle)) for i, line in enumerate(TEXT.splitlines()) if needle in line]
    i, line, col = hits[occurrence]
    before = line[:col + offset]
    return {"line": i, "character": len(before.encode("utf-16-le")) // 2}

class Server:
    def __init__(self):
        self.proc = subprocess.Popen([str(LEAN), "--server"], cwd=ROOT,
            env=dict(os.environ, LEAN_NUM_THREADS="1"), stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0)
        self.pending = b""
        self.next_id = 10
        record("start", pid=self.proc.pid)
        self.send({"jsonrpc":"2.0","id":1,"method":"initialize","params":{
            "processId":os.getpid(),"rootUri":ROOT.as_uri(),"capabilities":{},
            "initializationOptions":{"hasWidgets":False}}})
        self.until(1)
        self.send({"jsonrpc":"2.0","method":"initialized","params":{}})

    def send(self, msg):
        raw=json.dumps(msg,separators=(",",":"),ensure_ascii=False).encode()
        self.proc.stdin.write(b"Content-Length: "+str(len(raw)).encode()+b"\r\n\r\n"+raw)
        self.proc.stdin.flush()
        record("send", message=msg)

    def read(self, timeout=15):
        deadline=time.monotonic()+timeout
        while time.monotonic()<deadline:
            if b"\r\n\r\n" in self.pending:
                header, body=self.pending.split(b"\r\n\r\n",1)
                lengths=[int(h.split(b":",1)[1]) for h in header.split(b"\r\n") if h.lower().startswith(b"content-length:")]
                if lengths and len(body)>=lengths[0]:
                    raw,self.pending=body[:lengths[0]],body[lengths[0]:]
                    msg=json.loads(raw)
                    record("recv", message=msg)
                    if msg.get("method")=="client/registerCapability" and "id" in msg:
                        self.send({"jsonrpc":"2.0","id":msg["id"],"result":None})
                    return msg
            ready,_,_=select.select([self.proc.stdout],[],[],min(.1,max(0,deadline-time.monotonic())))
            if ready:
                chunk=os.read(self.proc.stdout.fileno(),65536)
                if not chunk: break
                self.pending+=chunk
        raise TimeoutError("Lean server response")

    def until(self, rid, timeout=15):
        deadline=time.monotonic()+timeout
        while time.monotonic()<deadline:
            msg=self.read(max(.1,deadline-time.monotonic()))
            if msg.get("id")==rid:return msg
        raise TimeoutError(rid)

    def request(self, method, params):
        rid=self.next_id;self.next_id+=1
        self.send({"jsonrpc":"2.0","id":rid,"method":method,"params":params})
        return self.until(rid)

    def finish(self):
        if self.proc.poll() is not None:return
        try:
            self.send({"jsonrpc":"2.0","id":99,"method":"shutdown","params":None})
            self.until(99,5)
            self.send({"jsonrpc":"2.0","method":"exit"})
            self.proc.wait(timeout=5)
        finally:
            if self.proc.poll() is None:self.proc.kill();self.proc.wait()
            record("stop", returncode=self.proc.returncode,
                stderr=self.proc.stderr.read().decode(errors="replace"))

def main():
    assert "4.30.0-rc2" in subprocess.check_output([str(LEAN),"--version"],text=True)
    record("subject",lean_version=subprocess.check_output([str(LEAN),"--version"],text=True).strip(),
        binary_sha256=sha(LEAN.read_bytes()),source_sha256=sha(TEXT))
    batch=subprocess.run([str(LEAN),"--json",str(SOURCE)],cwd=ROOT,
        env=dict(os.environ,LEAN_NUM_THREADS="1"),capture_output=True,text=True,timeout=20)
    record("batch",argv=["$LEAN","--json","$SOURCE"],returncode=batch.returncode,
        stdout=batch.stdout,stderr=batch.stderr)
    server=Server()
    try:
        server.send({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{
            "textDocument":{"uri":URI,"languageId":"lean","version":1,"text":TEXT}}})
        ready=server.request("textDocument/waitForDiagnostics",{"uri":URI,"version":1})
        record("ready",response=ready)
        points={
            "nested_by":position(":= by",0,3),
            "have_before":position("have hz"),
            "inner_simpa_before":position("simpa"),
            "inner_simpa_after":position("simpa",offset=5),
            "first_keyword":position("first"),
            "trace_before":position("trace"),
            "emoji_open_quote":position("\"🧪\""),
            "emoji_inside":position("🧪"),
            "emoji_after":position("🧪",offset=1),
            "outer_exact_before":position("exact hz"),
            "outer_exact_after":position("exact hz",offset=8),
            "unselected_branch":position("exact h",1),
            "constructor_before":position("constructor"),
            "first_bullet":position("· trivial"),
            "trivial_before":position("trivial"),
            "trivial_after":position("trivial",offset=7),
            "second_bullet":position("· rfl"),
            "rfl_before":position("rfl"),
            "term_exact_before":position("exact Eq.refl"),
            "term_expr":position("Eq.refl"),
        }
        for name,pos in points.items():
            response=server.request("$/lean/plainGoal",{"textDocument":{"uri":URI},"position":pos})
            record("goal",name=name,position=pos,response=response)
        for name in ("term_exact_before","term_expr","emoji_after"):
            pos=points[name]
            response=server.request("$/lean/plainTermGoal",{"textDocument":{"uri":URI},"position":pos})
            record("term_goal",name=name,position=pos,response=response)
        record("completed")
    finally:server.finish()

try:main()
except Exception as exc:
    record("fatal",error=repr(exc));raise
finally:
    raw=json.dumps(EVENTS,indent=2,ensure_ascii=False)+"\n"
    raw=raw.replace(URI,"$URI").replace(str(SOURCE),"$SOURCE").replace(str(LEAN),"$LEAN")
    (ROOT/"transcript.json").write_text(raw)
