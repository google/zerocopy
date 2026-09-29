#!/usr/bin/env python3
"""Bounded direct Lean test of an old wait/query during a marked newer edit."""
import hashlib
import json
import os
import select
import subprocess
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
WORK = ROOT / "work"
WORK.mkdir(exist_ok=True)
LEAN = Path(os.environ["LEAN_BIN"]).resolve()
DOC = WORK / "Proof.lean"
V1 = '''import Lean

theorem demo : True := by
  run_tac do
    IO.FS.writeFile "v1.entered" "1"
    while !(← (System.FilePath.mk "v1.release").pathExists) do
      IO.sleep 10
  trivial
'''
V2 = '''import Lean

theorem demo : False := by
  run_tac do
    IO.FS.writeFile "v2.entered" "2"
  exact ?_
'''
START = time.monotonic_ns()
events = []
messages = []
cv = threading.Condition()
send_lock = threading.Lock()
server = None


def sha(data):
    return hashlib.sha256(data if isinstance(data, bytes) else data.encode()).hexdigest()


def log(kind, **fields):
    with cv:
        events.append({"ns": time.monotonic_ns() - START, "kind": kind, **fields})
        cv.notify_all()


def send(message):
    data = json.dumps(message, separators=(",", ":")).encode()
    with send_lock:
        server.stdin.write(b"Content-Length: " + str(len(data)).encode() + b"\r\n\r\n" + data)
        server.stdin.flush()
        log("client", message=message)


def receive_loop():
    buf = b""
    while True:
        ready, _, _ = select.select([server.stdout], [], [], .1)
        if not ready:
            if server.poll() is not None:
                return
            continue
        part = os.read(server.stdout.fileno(), 65536)
        if not part:
            return
        buf += part
        while b"\r\n\r\n" in buf:
            header, body = buf.split(b"\r\n\r\n", 1)
            lengths = [int(line.split(b":", 1)[1]) for line in header.split(b"\r\n") if line.lower().startswith(b"content-length:")]
            if not lengths:
                raise ValueError("missing content length")
            if len(body) < lengths[0]:
                break
            raw, buf = body[:lengths[0]], body[lengths[0]:]
            message = json.loads(raw)
            with cv:
                messages.append(message)
                events.append({"ns": time.monotonic_ns() - START, "kind": "server", "message": message})
                cv.notify_all()
            if message.get("method") == "client/registerCapability" and "id" in message:
                send({"jsonrpc": "2.0", "id": message["id"], "result": None})


def wait_id(request_id, seconds):
    deadline = time.monotonic() + seconds
    with cv:
        while True:
            hits = [m for m in messages if m.get("id") == request_id]
            if hits:
                return hits[-1]
            remain = deadline - time.monotonic()
            if remain <= 0:
                raise TimeoutError(f"response {request_id}")
            cv.wait(min(remain, .1))


def marker(name, seconds):
    deadline = time.monotonic() + seconds
    while time.monotonic() < deadline:
        if (WORK / name).exists():
            log("marker", name=name)
            return True
        time.sleep(.01)
    log("marker_timeout", name=name)
    return False


def batch(label, source):
    path = WORK / f"{label}.lean"
    path.write_text(source)
    result = subprocess.run([str(LEAN), "--json", str(path)], cwd=WORK, capture_output=True, text=True, timeout=20, env=dict(os.environ, LEAN_NUM_THREADS="1"))
    log("batch", label=label, source_sha256=sha(source), exit=result.returncode, stdout=result.stdout, stderr=result.stderr)


def request(request_id, method, params):
    send({"jsonrpc": "2.0", "id": request_id, "method": method, "params": params})


try:
    version = subprocess.check_output([str(LEAN), "--version"], text=True).strip()
    binary_hash = sha(LEAN.read_bytes())
    if binary_hash != "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997":
        raise RuntimeError("unexpected Lean binary")
    log("subject", version=version, binary_sha256=binary_hash, v1_sha256=sha(V1), v2_sha256=sha(V2))
    (WORK / "v1.release").write_text("release")
    batch("V1", V1)
    batch("V2", V2)
    for name in ("v1.entered", "v1.release", "v2.entered"):
        (WORK / name).unlink(missing_ok=True)
    DOC.write_text(V1)
    server = subprocess.Popen([str(LEAN), "--server"], cwd=WORK, env=dict(os.environ, LEAN_NUM_THREADS="1"), stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0)
    log("server_start", pid=server.pid)
    reader = threading.Thread(target=receive_loop, daemon=True)
    reader.start()
    request(1, "initialize", {"processId": os.getpid(), "rootUri": WORK.as_uri(), "capabilities": {}, "initializationOptions": {"hasWidgets": False}})
    wait_id(1, 10)
    send({"jsonrpc": "2.0", "method": "initialized", "params": {}})
    uri = DOC.as_uri()
    send({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {"uri": uri, "languageId": "lean", "version": 1, "text": V1}}})
    request(10, "textDocument/waitForDiagnostics", {"uri": uri, "version": 1})
    if not marker("v1.entered", 10):
        raise RuntimeError("V1 gate did not enter")
    request(20, "$/lean/plainGoal", {"textDocument": {"uri": uri}, "position": {"line": 3, "character": 9}})
    send({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {"textDocument": {"uri": uri, "version": 2}, "contentChanges": [{"text": V2}]}})
    request(11, "textDocument/waitForDiagnostics", {"uri": uri, "version": 2})
    marked_while_gated = marker("v2.entered", 8)
    queried_v2 = False
    if marked_while_gated:
        try:
            wait_id(11, 5)
            log("v2_wait_before_v1_release")
            request(21, "$/lean/plainGoal", {"textDocument": {"uri": uri, "version": 1}, "position": {"line": 3, "character": 9}})
            queried_v2 = True
            wait_id(21, 5)
            log("v2_goal_before_v1_release")
        except TimeoutError:
            log("v2_wait_or_goal_pending_before_v1_release")
    (WORK / "v1.release").write_text("release")
    log("v1_released", v2_marked_before_release=marked_while_gated)
    for rid in (10, 20, 11):
        try:
            wait_id(rid, 12)
        except TimeoutError:
            log("response_timeout", id=rid)
    request(12, "textDocument/waitForDiagnostics", {"uri": uri, "version": 1})
    wait_id(12, 10)
    if not queried_v2:
        request(21, "$/lean/plainGoal", {"textDocument": {"uri": uri, "version": 1}, "position": {"line": 3, "character": 9}})
        wait_id(21, 10)
    request(99, "shutdown", None)
    wait_id(99, 5)
    send({"jsonrpc": "2.0", "method": "exit"})
    server.wait(timeout=5)
finally:
    if server is not None and server.poll() is None:
        server.kill()
        server.wait(timeout=5)
        log("forced_exit")
    if server is not None:
        reader.join(timeout=1)
        log("server_exit", exit=server.returncode, stderr=server.stderr.read().decode(errors="replace"))
    raw = json.dumps(events, indent=2) + "\n"
    raw = raw.replace(str(WORK), "$WORK").replace(str(LEAN), "$LEAN_BIN")
    (ROOT / "transcript.json").write_text(raw)
