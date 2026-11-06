#!/usr/bin/env python3
"""Direct Lean open-buffer authority across overwrite, save, rename, deletion."""
import hashlib
import json
import os
import select
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
WORK = ROOT / "work"
WORK.mkdir(exist_ok=True)
LEAN = Path(os.environ["LEAN_BIN"]).resolve()
ORIGINAL = WORK / "Open.lean"
RENAMED = WORK / "Renamed.lean"
SOURCE = {n: f"theorem demo : {n} = {n} := by\n  exact ?_\n" for n in (1, 2, 3)}
START = time.monotonic_ns()
events = []
server = None
buffer = b""


def sha(data):
    return hashlib.sha256(data if isinstance(data, bytes) else data.encode()).hexdigest()


def log(kind, **fields):
    events.append({"ns": time.monotonic_ns() - START, "kind": kind, **fields})


def state(label, path, intended_buffer_version=None):
    log("disk_state", label=label, path=str(path), exists=path.exists(), sha256=sha(path.read_bytes()) if path.exists() else None, intended_buffer_version=intended_buffer_version)


def send(message):
    data = json.dumps(message, separators=(",", ":")).encode()
    server.stdin.write(b"Content-Length: " + str(len(data)).encode() + b"\r\n\r\n" + data)
    server.stdin.flush()
    log("client", message=message)


def read(seconds=10):
    global buffer
    deadline = time.monotonic() + seconds
    while time.monotonic() < deadline:
        if b"\r\n\r\n" in buffer:
            header, body = buffer.split(b"\r\n\r\n", 1)
            lengths = [int(line.split(b":", 1)[1]) for line in header.split(b"\r\n") if line.lower().startswith(b"content-length:")]
            if not lengths:
                raise ValueError("missing Content-Length")
            if len(body) >= lengths[0]:
                raw, buffer = body[:lengths[0]], body[lengths[0]:]
                message = json.loads(raw)
                log("server", message=message)
                if message.get("method") == "client/registerCapability" and "id" in message:
                    send({"jsonrpc": "2.0", "id": message["id"], "result": None})
                return message
        ready, _, _ = select.select([server.stdout], [], [], min(.1, max(0, deadline - time.monotonic())))
        if ready:
            part = os.read(server.stdout.fileno(), 65536)
            if not part:
                break
            buffer += part
    raise TimeoutError("server read")


def until(request_id, seconds=12):
    deadline = time.monotonic() + seconds
    while time.monotonic() < deadline:
        message = read(max(.1, deadline - time.monotonic()))
        if message.get("id") == request_id:
            return message
    raise TimeoutError(f"request {request_id}")


def request(request_id, method, params):
    send({"jsonrpc": "2.0", "id": request_id, "method": method, "params": params})
    return until(request_id)


def notify(method, params):
    send({"jsonrpc": "2.0", "method": method, "params": params})


def opened(uri, text, version):
    notify("textDocument/didOpen", {"textDocument": {"uri": uri, "languageId": "lean", "version": version, "text": text}})


def barrier(uri, version, rid):
    result = request(rid, "textDocument/waitForDiagnostics", {"uri": uri, "version": version})
    if result.get("result") != {}:
        raise AssertionError((rid, result))


def goal(uri, rid):
    return request(rid, "$/lean/plainGoal", {"textDocument": {"uri": uri}, "position": {"line": 1, "character": 2}})


def batch(label, path, source=None):
    if source is not None:
        path.write_text(source)
    result = subprocess.run([str(LEAN), "--json", str(path)], cwd=WORK, env=dict(os.environ, LEAN_NUM_THREADS="1"), capture_output=True, text=True, timeout=15)
    log("batch", label=label, path=str(path), source_sha256=sha(path.read_bytes()) if path.exists() else None, exit=result.returncode, stdout=result.stdout, stderr=result.stderr)


try:
    binary_hash = sha(LEAN.read_bytes())
    if binary_hash != "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997":
        raise RuntimeError("unexpected Lean binary")
    log("subject", version=subprocess.check_output([str(LEAN), "--version"], text=True).strip(), binary_sha256=binary_hash, source_sha256={str(k): sha(v) for k, v in SOURCE.items()})
    for n, text in SOURCE.items():
        batch(f"source-{n}", WORK / f"Batch-{n}.lean", text)
    ORIGINAL.write_text(SOURCE[1])
    RENAMED.unlink(missing_ok=True)
    state("initial", ORIGINAL)
    server = subprocess.Popen([str(LEAN), "--server"], cwd=WORK, env=dict(os.environ, LEAN_NUM_THREADS="1"), stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0)
    log("server_start", pid=server.pid)
    request(1, "initialize", {"processId": os.getpid(), "rootUri": WORK.as_uri(), "capabilities": {}, "initializationOptions": {"hasWidgets": False}})
    notify("initialized", {})
    old_uri, new_uri = ORIGINAL.as_uri(), RENAMED.as_uri()
    opened(old_uri, SOURCE[1], 1)
    barrier(old_uri, 1, 10)
    goal(old_uri, 20)

    notify("textDocument/didChange", {"textDocument": {"uri": old_uri, "version": 2}, "contentChanges": [{"text": SOURCE[2]}]})
    barrier(old_uri, 2, 11)
    state("unsaved-B-disk-A", ORIGINAL, 2)
    goal(old_uri, 21)

    ORIGINAL.write_text(SOURCE[3])
    state("external-C-no-watcher", ORIGINAL, 2)
    barrier(old_uri, 2, 12)
    goal(old_uri, 22)
    notify("workspace/didChangeWatchedFiles", {"changes": [{"uri": old_uri, "type": 2}]})
    log("watcher_sent", label="external-C-changed")
    barrier(old_uri, 2, 13)
    goal(old_uri, 23)

    ORIGINAL.write_text(SOURCE[2])
    notify("textDocument/didSave", {"textDocument": {"uri": old_uri}})
    state("saved-B-over-C", ORIGINAL, 2)
    barrier(old_uri, 2, 14)
    goal(old_uri, 24)

    ORIGINAL.rename(RENAMED)
    state("renamed-old-absent", ORIGINAL, 2)
    state("renamed-new-B", RENAMED)
    notify("workspace/didChangeWatchedFiles", {"changes": [{"uri": old_uri, "type": 3}, {"uri": new_uri, "type": 1}]})
    log("watcher_sent", label="rename")
    barrier(old_uri, 2, 15)
    goal(old_uri, 25)
    notify("textDocument/didClose", {"textDocument": {"uri": old_uri}})
    goal(old_uri, 26)

    opened(new_uri, RENAMED.read_text(), 1)
    barrier(new_uri, 1, 16)
    goal(new_uri, 27)
    RENAMED.unlink()
    state("deleted-open-new-uri", RENAMED, 1)
    notify("workspace/didChangeWatchedFiles", {"changes": [{"uri": new_uri, "type": 3}]})
    log("watcher_sent", label="delete")
    barrier(new_uri, 1, 17)
    goal(new_uri, 28)
    notify("textDocument/didClose", {"textDocument": {"uri": new_uri}})
    goal(new_uri, 29)
    batch("deleted-path", RENAMED)

    RENAMED.write_text(SOURCE[3])
    state("recreated-C", RENAMED)
    opened(new_uri, RENAMED.read_text(), 2)
    barrier(new_uri, 2, 18)
    goal(new_uri, 30)
    batch("recreated-C", RENAMED)
    notify("textDocument/didClose", {"textDocument": {"uri": new_uri}})
    request(99, "shutdown", None)
    notify("exit", {})
    server.stdin.close()
    drain_deadline = time.monotonic() + 5
    while time.monotonic() < drain_deadline:
        try:
            read(.2)
        except TimeoutError:
            if server.poll() is not None:
                break
    server.wait(timeout=5)
    log("wire_drain_complete")
except Exception as exc:
    log("fatal", error=repr(exc))
    raise
finally:
    if server is not None and server.poll() is None:
        server.kill()
        server.wait(timeout=5)
        log("forced_exit")
    if server is not None:
        log("server_exit", exit=server.returncode, stderr=server.stderr.read().decode(errors="replace"))
    raw = json.dumps(events, indent=2) + "\n"
    raw = raw.replace(str(WORK), "$WORK").replace(str(LEAN), "$LEAN_BIN")
    (ROOT / "transcript.json").write_text(raw)
