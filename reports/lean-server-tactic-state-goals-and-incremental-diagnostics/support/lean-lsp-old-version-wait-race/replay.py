#!/usr/bin/env python3
"""Probe whether an old-version diagnostics wait pins the following goal query.

Usage: python3 replay.py /absolute/path/to/lean
All writable files stay beside this script. The saved transcript replaces local
paths and process IDs with stable labels; no server logs are enabled.
"""

import hashlib
import json
import os
import select
import subprocess
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parent
LEAN = Path(sys.argv[1]).resolve()
DOC = ROOT / "Generated.lean"
V1 = "theorem demo (n : Nat) : n = n := by\n  exact ?_\n"
V2 = "theorem demo (n : Nat) : n = n := by\n  rfl\n"
DOC.write_text(V1)
events = []


def clean(value):
    if isinstance(value, dict):
        return {k: clean(v) for k, v in value.items() if k not in {"processId", "pid"}}
    if isinstance(value, list):
        return [clean(v) for v in value]
    if isinstance(value, str):
        return value.replace(ROOT.as_uri(), "file://$PROBE").replace(str(ROOT), "$PROBE").replace(str(LEAN), "$LEAN")
    return value


def record(kind, data):
    events.append({"kind": kind, "data": clean(data)})


for label, source in (("v1", V1), ("v2", V2)):
    source_file = ROOT / f"batch-{label}.lean"
    source_file.write_text(source)
    result = subprocess.run([str(LEAN), "--json", str(source_file)], cwd=ROOT, capture_output=True, text=True, timeout=30)
    record("batch", {"version": label, "sha256": hashlib.sha256(source.encode()).hexdigest(), "exit": result.returncode,
                     "stdout": result.stdout, "stderr": result.stderr})

proc = subprocess.Popen([str(LEAN), "--server"], cwd=ROOT, stdin=subprocess.PIPE,
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0)
buffer = b""


def send(message):
    raw = json.dumps(message, separators=(",", ":")).encode()
    proc.stdin.write(b"Content-Length: " + str(len(raw)).encode() + b"\r\n\r\n" + raw)
    proc.stdin.flush()
    record("client", message)


def read_until(predicate, timeout=30):
    global buffer
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        while b"\r\n\r\n" in buffer:
            header, rest = buffer.split(b"\r\n\r\n", 1)
            length = next((int(line.split(b":", 1)[1]) for line in header.split(b"\r\n")
                           if line.lower().startswith(b"content-length:")), None)
            if length is None:
                raise ValueError("missing Content-Length")
            if len(rest) < length:
                break
            raw, buffer = rest[:length], rest[length:]
            message = json.loads(raw)
            record("server", message)
            if message.get("method") == "client/registerCapability" and "id" in message:
                send({"jsonrpc": "2.0", "id": message["id"], "result": None})
            if predicate(message):
                return message
        ready, _, _ = select.select([proc.stdout], [], [], max(0, deadline - time.monotonic()))
        if not ready:
            break
        chunk = os.read(proc.stdout.fileno(), 65536)
        if not chunk:
            break
        buffer += chunk
    raise TimeoutError("server response did not arrive")


uri = DOC.as_uri()
try:
    send({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {
        "processId": os.getpid(), "rootUri": ROOT.as_uri(), "capabilities": {},
        "initializationOptions": {"hasWidgets": False}}})
    read_until(lambda m: m.get("id") == 1)
    send({"jsonrpc": "2.0", "method": "initialized", "params": {}})
    send({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {
        "uri": uri, "languageId": "lean", "version": 1, "text": V1}}})
    send({"jsonrpc": "2.0", "id": 11, "method": "textDocument/waitForDiagnostics", "params": {"uri": uri, "version": 1}})
    read_until(lambda m: m.get("id") == 11)
    send({"jsonrpc": "2.0", "id": 21, "method": "$/lean/plainGoal", "params": {
        "textDocument": {"uri": uri}, "position": {"line": 1, "character": 10}}})
    read_until(lambda m: m.get("id") == 21)

    send({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
        "textDocument": {"uri": uri, "version": 2}, "contentChanges": [{"text": V2}]}})
    send({"jsonrpc": "2.0", "id": 12, "method": "textDocument/waitForDiagnostics", "params": {"uri": uri, "version": 2}})
    read_until(lambda m: m.get("id") == 12)
    send({"jsonrpc": "2.0", "id": 22, "method": "$/lean/plainGoal", "params": {
        "textDocument": {"uri": uri}, "position": {"line": 1, "character": 5}}})
    read_until(lambda m: m.get("id") == 22)

    # The client now intentionally asks for an obsolete version.
    send({"jsonrpc": "2.0", "id": 13, "method": "textDocument/waitForDiagnostics", "params": {"uri": uri, "version": 1}})
    read_until(lambda m: m.get("id") == 13)
    send({"jsonrpc": "2.0", "id": 23, "method": "$/lean/plainGoal", "params": {
        "textDocument": {"uri": uri}, "position": {"line": 1, "character": 5}}})
    read_until(lambda m: m.get("id") == 23)
    send({"jsonrpc": "2.0", "id": 99, "method": "shutdown", "params": None})
    read_until(lambda m: m.get("id") == 99)
    send({"jsonrpc": "2.0", "method": "exit"})
except Exception as exc:
    record("exception", repr(exc))
    raise
finally:
    try:
        proc.wait(timeout=3)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait(timeout=3)
    record("server_exit", {"exit": proc.returncode, "stderr": proc.stderr.read().decode(errors="replace")})
    (ROOT / "transcript.json").write_text(json.dumps(events, indent=2) + "\n")
