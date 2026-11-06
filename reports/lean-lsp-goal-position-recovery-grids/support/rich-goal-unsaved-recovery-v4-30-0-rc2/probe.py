#!/usr/bin/env python3
"""Direct Lean plain/rich goal comparison across unsaved nested proof edits."""
import hashlib
import json
import os
import select
import shutil
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = Path(os.environ.get("LEAN_BIN") or shutil.which("lean") or "lean").resolve()
BASE = """import Lean

theorem nested (n : Nat) (h : n = 0) : n + 0 = 0 := by
  have hz : n + 0 = 0 := by
    simpa using h
  exact hz

theorem tail : True := by
  trivial
"""
VARIANTS = [
    (1, "valid", BASE),
    (2, "syntax", BASE.replace("simpa using h", ")")),
    (3, "unknown", BASE.replace("simpa using h", "this_is_not_a_tactic")),
    (4, "recovered", BASE),
]
POSITIONS = {
    "outer_have": (3, 2),
    "inner_start": (4, 4),
    "inner_inside": (4, 8),
    "inner_end": (4, 24),
    "after_inner": (5, 2),
    "tail": (8, 2),
}
START = time.monotonic()
EVENTS = []

def sha(data):
    return hashlib.sha256(data if isinstance(data, bytes) else data.encode()).hexdigest()

def log(kind, **fields):
    EVENTS.append(dict(seq=len(EVENTS), ms=round((time.monotonic()-START)*1000, 1), kind=kind, **fields))

class Server:
    def __init__(self):
        self.p = subprocess.Popen([str(LEAN), "--server"], cwd=HERE,
            env=dict(os.environ, LEAN_NUM_THREADS="1"), stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0)
        self.buf = b""
        self.next_id = 10
        log("start", pid=self.p.pid)
        self.send(dict(jsonrpc="2.0", id=1, method="initialize", params=dict(
            processId=os.getpid(), rootUri=HERE.as_uri(), capabilities={},
            initializationOptions={"hasWidgets": False})))
        self.until(1)
        self.send(dict(jsonrpc="2.0", method="initialized", params={}))

    def send(self, message):
        raw = json.dumps(message, ensure_ascii=False, separators=(",", ":")).encode()
        self.p.stdin.write(b"Content-Length: " + str(len(raw)).encode() + b"\r\n\r\n" + raw)
        self.p.stdin.flush()
        log("send", message=message)

    def read(self, timeout=20):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if b"\r\n\r\n" in self.buf:
                header, body = self.buf.split(b"\r\n\r\n", 1)
                lengths = [int(h.split(b":", 1)[1]) for h in header.split(b"\r\n")
                           if h.lower().startswith(b"content-length:")]
                if lengths and len(body) >= lengths[0]:
                    raw, self.buf = body[:lengths[0]], body[lengths[0]:]
                    message = json.loads(raw)
                    log("recv", message=message)
                    if message.get("method") == "client/registerCapability" and "id" in message:
                        self.send(dict(jsonrpc="2.0", id=message["id"], result=None))
                    return message
            ready, _, _ = select.select([self.p.stdout], [], [],
                                         min(.1, max(0, deadline-time.monotonic())))
            if ready:
                chunk = os.read(self.p.stdout.fileno(), 65536)
                if not chunk:
                    break
                self.buf += chunk
        raise TimeoutError("server read")

    def until(self, rid, timeout=20):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            message = self.read(max(.1, deadline-time.monotonic()))
            if message.get("id") == rid:
                return message
        raise TimeoutError(rid)

    def request(self, method, params):
        rid = self.next_id
        self.next_id += 1
        self.send(dict(jsonrpc="2.0", id=rid, method=method, params=params))
        return self.until(rid)

    def stop(self):
        if self.p.poll() is not None:
            return
        try:
            self.send(dict(jsonrpc="2.0", id=99, method="shutdown", params=None))
            self.until(99, 5)
            self.send(dict(jsonrpc="2.0", method="exit"))
            self.p.wait(timeout=5)
        finally:
            if self.p.poll() is None:
                self.p.kill()
                self.p.wait()
            log("stop", rc=self.p.returncode, stderr=self.p.stderr.read().decode(errors="replace"))

def goal_pair(server, uri, session, line, character):
    position = dict(line=line, character=character)
    document = dict(uri=uri)
    plain = server.request("$/lean/plainGoal", dict(textDocument=document, position=position))
    rich = server.request("$/lean/rpc/call", dict(textDocument=document, position=position,
        sessionId=session, method="Lean.Widget.getInteractiveGoals",
        params=dict(textDocument=document, position=position)))
    return dict(plain=plain, rich=rich)

def main():
    version_text = subprocess.check_output([str(LEAN), "--version"], text=True).strip()
    assert "4.30.0-rc2" in version_text
    log("subject", version=version_text, binary_sha256=sha(LEAN.read_bytes()),
        source_sha256={label: sha(text) for _, label, text in VARIANTS})
    source = HERE / "Nested.lean"
    source.write_text(BASE)
    # Each batch control is a distinct path. The server URI stays on disk at BASE.
    batch = {}
    for version, label, text in VARIANTS[:3]:
        path = HERE / f"Batch-{label}.lean"
        path.write_text(text)
        proc = subprocess.run([str(LEAN), "--json", str(path)], cwd=HERE,
            env=dict(os.environ, LEAN_NUM_THREADS="1"), capture_output=True,
            text=True, timeout=30)
        batch[label] = dict(rc=proc.returncode, stdout=proc.stdout, stderr=proc.stderr)
        log("batch", version=version, label=label, sha256=sha(text), **batch[label])
    uri = source.as_uri()
    server = Server()
    cases = []
    try:
        for version, label, text in VARIANTS:
            if version == 1:
                server.send(dict(jsonrpc="2.0", method="textDocument/didOpen", params=dict(
                    textDocument=dict(uri=uri, languageId="lean", version=version, text=text))))
            else:
                server.send(dict(jsonrpc="2.0", method="textDocument/didChange", params=dict(
                    textDocument=dict(uri=uri, version=version),
                    contentChanges=[dict(text=text)])))
            wait = server.request("textDocument/waitForDiagnostics", dict(uri=uri, version=version))
            # The same session is retained through didChange to test its observed lifetime.
            if version == 1:
                connect = server.request("$/lean/rpc/connect", dict(uri=uri))
                session = connect["result"]["sessionId"]
            samples = {name: goal_pair(server, uri, session, *point)
                       for name, point in POSITIONS.items()}
            case = dict(version=version, label=label, source_sha256=sha(text),
                        wait=wait, samples=samples)
            cases.append(case)
            log("case", **case)
        server.send(dict(jsonrpc="2.0", method="textDocument/didClose",
                         params=dict(textDocument=dict(uri=uri))))
    finally:
        server.stop()
    assert source.read_text() == BASE
    result = dict(subject=dict(version=version_text, binary_sha256=sha(LEAN.read_bytes())),
                  disk_sha256=sha(BASE), positions=POSITIONS, batch=batch, cases=cases)
    result_raw = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    result_raw = result_raw.replace(str(HERE), "$HERE").replace(str(LEAN), "$LEAN_BIN")
    (HERE / "results.json").write_text(result_raw)

try:
    main()
finally:
    raw = json.dumps(EVENTS, indent=2, ensure_ascii=False) + "\n"
    raw = raw.replace(HERE.as_uri(), "$HERE_URI").replace(str(HERE), "$HERE")
    raw = raw.replace(str(LEAN), "$LEAN_BIN")
    (HERE / "transcript.json").write_text(raw)
