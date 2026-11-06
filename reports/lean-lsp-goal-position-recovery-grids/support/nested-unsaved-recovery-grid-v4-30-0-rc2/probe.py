#!/usr/bin/env python3
"""Small direct Lean server probe. Writes only beside this script."""
import hashlib
import json
import os
import select
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = Path(os.environ.get("LEAN_BIN", "/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean"))
SOURCE = HERE / "Nested.lean"
BASE = """import Lean

theorem nested (n : Nat) (h : n = 0) : n + 0 = 0 := by
  have hz : n + 0 = 0 := by
    simpa using h
  exact hz

theorem tail : True := by
  trivial
"""
VERSIONS = [(1, "valid", BASE), (2, "syntax", BASE.replace("simpa using h", ")")),
            (3, "unknown", BASE.replace("simpa using h", "this_is_not_a_tactic")),
            (4, "recovered", BASE)]
EVENTS = []
START = time.monotonic()

def digest(data):
    if isinstance(data, str): data = data.encode()
    return hashlib.sha256(data).hexdigest()

def event(kind, **fields):
    EVENTS.append({"seq": len(EVENTS), "kind": kind,
                   "ms": round((time.monotonic() - START) * 1000, 1), **fields})

def pos(text, needle, offset=0):
    for line_no, line in enumerate(text.splitlines()):
        if needle in line:
            prefix = line[:line.index(needle) + offset]
            return {"line": line_no, "character": len(prefix.encode("utf-16-le")) // 2}
    raise ValueError(needle)

class Server:
    def __init__(self):
        self.proc = subprocess.Popen([str(LEAN), "--server"], cwd=HERE,
            env=dict(os.environ, LEAN_NUM_THREADS="1"), stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0)
        self.buffer = b""
        self.next_id = 10
        event("start", pid=self.proc.pid)
        self.send({"jsonrpc":"2.0", "id":1, "method":"initialize", "params":{
            "processId":os.getpid(), "rootUri":HERE.as_uri(), "capabilities":{},
            "initializationOptions":{"hasWidgets":False}}})
        self.until(1)
        self.send({"jsonrpc":"2.0", "method":"initialized", "params":{}})

    def send(self, message):
        raw = json.dumps(message, ensure_ascii=False, separators=(",", ":")).encode()
        self.proc.stdin.write(b"Content-Length: " + str(len(raw)).encode() + b"\r\n\r\n" + raw)
        self.proc.stdin.flush()
        event("send", message=message)

    def read(self, timeout=20):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if b"\r\n\r\n" in self.buffer:
                header, body = self.buffer.split(b"\r\n\r\n", 1)
                lengths = [int(h.split(b":", 1)[1]) for h in header.split(b"\r\n")
                           if h.lower().startswith(b"content-length:")]
                if lengths and len(body) >= lengths[0]:
                    raw, self.buffer = body[:lengths[0]], body[lengths[0]:]
                    message = json.loads(raw)
                    event("recv", message=message)
                    if message.get("method") == "client/registerCapability" and "id" in message:
                        self.send({"jsonrpc":"2.0", "id":message["id"], "result":None})
                    return message
            ready, _, _ = select.select([self.proc.stdout], [], [], min(.1, max(0, deadline-time.monotonic())))
            if ready:
                chunk = os.read(self.proc.stdout.fileno(), 65536)
                if not chunk: break
                self.buffer += chunk
        raise TimeoutError("server read")

    def until(self, request_id, timeout=20):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            response = self.read(max(.1, deadline-time.monotonic()))
            if response.get("id") == request_id: return response
        raise TimeoutError(request_id)

    def request(self, method, params):
        request_id = self.next_id
        self.next_id += 1
        self.send({"jsonrpc":"2.0", "id":request_id, "method":method, "params":params})
        return self.until(request_id)

    def close(self):
        if self.proc.poll() is not None: return
        try:
            self.send({"jsonrpc":"2.0", "id":99, "method":"shutdown", "params":None})
            self.until(99, 5)
            self.send({"jsonrpc":"2.0", "method":"exit"})
            self.proc.wait(timeout=5)
        finally:
            if self.proc.poll() is None: self.proc.kill(); self.proc.wait()
            event("stop", returncode=self.proc.returncode,
                  stderr=self.proc.stderr.read().decode(errors="replace"))

def main():
    assert "4.30.0-rc2" in subprocess.check_output([str(LEAN), "--version"], text=True)
    assert SOURCE.read_text() == BASE
    event("subject", version=subprocess.check_output([str(LEAN), "--version"], text=True).strip(),
          binary_sha256=digest(LEAN.read_bytes()), disk_sha256=digest(SOURCE.read_bytes()))
    variant_dir = HERE / "variants"
    variant_dir.mkdir(exist_ok=True)
    for version, label, text in VERSIONS[:3]:
        path = variant_dir / f"{version}-{label}.lean"
        path.write_text(text)
        result = subprocess.run([str(LEAN), "--json", str(path)], cwd=HERE,
            env=dict(os.environ, LEAN_NUM_THREADS="1"), capture_output=True, text=True, timeout=30)
        event("batch", version=version, label=label, sha256=digest(text),
              returncode=result.returncode, stdout=result.stdout, stderr=result.stderr)
    uri = SOURCE.as_uri()
    server = Server()
    try:
        for version, label, text in VERSIONS:
            if version == 1:
                server.send({"jsonrpc":"2.0", "method":"textDocument/didOpen", "params":{
                    "textDocument":{"uri":uri, "languageId":"lean", "version":version, "text":text}}})
            else:
                server.send({"jsonrpc":"2.0", "method":"textDocument/didChange", "params":{
                    "textDocument":{"uri":uri, "version":version}, "contentChanges":[{"text":text}]}})
            ready = server.request("textDocument/waitForDiagnostics", {"uri":uri, "version":version})
            event("ready", version=version, label=label, sha256=digest(text), response=ready)
            needle = ")" if label == "syntax" else "this_is_not_a_tactic" if label == "unknown" else "simpa using h"
            nested_before = {"line":4, "character":4} if label == "syntax" else pos(text, needle)
            nested_mid = {"line":4, "character":5} if label == "syntax" else pos(text, needle, min(2,len(needle)))
            nested_end = {"line":4, "character":5} if label == "syntax" else pos(text, needle, len(needle))
            positions = {"nested_before":nested_before,
                         "nested_mid":nested_mid,
                         "nested_end":nested_end,
                         "outer_exact":pos(text, "exact hz"),
                         "tail_before":pos(text, "trivial"),
                         "tail_after":pos(text, "trivial", len("trivial")),
                         "eof":{"line":len(text.splitlines()), "character":0}}
            for name, position in positions.items():
                result = server.request("$/lean/plainGoal", {"textDocument":{"uri":uri}, "position":position})
                event("goal", version=version, label=label, name=name, position=position, response=result)
        event("completed")
    finally:
        server.close()

try: main()
except Exception as exc:
    event("fatal", error=repr(exc))
    raise
finally:
    output = json.dumps(EVENTS, indent=2, ensure_ascii=False) + "\n"
    output = output.replace(str(HERE.as_uri()), "$URI_ROOT").replace(str(HERE), "$ROOT").replace(str(LEAN), "$LEAN")
    (HERE / "transcript.json").write_text(output)
