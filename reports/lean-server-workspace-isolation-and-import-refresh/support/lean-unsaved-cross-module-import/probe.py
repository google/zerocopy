#!/usr/bin/env python3
"""I038: an open Lean consumer imports another open, unsaved producer."""
import hashlib
import json
import os
import select
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
FIXTURE = ROOT / "fixture"
FIXTURE.mkdir(exist_ok=True)
LEAN = Path(os.environ["LEAN_BIN"]).resolve()
EVENTS = []
OLD = "def sharedValue : Nat := 3\n"
NEW = "def sharedValue : Nat := 4\n"
PROOF = "import Dep\ntheorem current : sharedValue = 3 := by\n  rfl\n"


def sha(data):
    return hashlib.sha256(data if isinstance(data, bytes) else data.encode()).hexdigest()


def record(kind, **data):
    EVENTS.append({"kind": kind, "time_monotonic": time.monotonic(), **data})


def run(label, argv):
    p = subprocess.run(argv, cwd=FIXTURE, env=dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(FIXTURE)), capture_output=True, text=True, timeout=30)
    record("command", label=label, argv=argv, exit_code=p.returncode, stdout=p.stdout, stderr=p.stderr)
    return p


def build_dep(text, label):
    (FIXTURE / "Dep.lean").write_text(text)
    p = run(label, [str(LEAN), "-o", "Dep.olean", "Dep.lean"])
    if p.returncode:
        raise RuntimeError(f"{label} failed: {p.stderr}")
    record("artifact", label=label, source_sha256=sha(text), olean_sha256=sha((FIXTURE / "Dep.olean").read_bytes()))


class Server:
    def __init__(self):
        self.buf = b""
        self.next_id = 1
        self.p = subprocess.Popen([str(LEAN), "--server"], cwd=FIXTURE, env=dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(FIXTURE)), stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0)
        record("server_start", argv=[str(LEAN), "--server"], cwd=str(FIXTURE), lean_path=str(FIXTURE), pid=self.p.pid)
        self.req("initialize", {"processId": os.getpid(), "rootUri": FIXTURE.as_uri(), "capabilities": {}, "initializationOptions": {"hasWidgets": False}})
        self.send({"jsonrpc": "2.0", "method": "initialized", "params": {}})

    def send(self, msg):
        body = json.dumps(msg, separators=(",", ":")).encode()
        self.p.stdin.write(b"Content-Length: " + str(len(body)).encode() + b"\r\n\r\n" + body)
        self.p.stdin.flush()
        record("client_message", message=msg)

    def recv(self, timeout=20):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            while b"\r\n\r\n" in self.buf:
                head, rest = self.buf.split(b"\r\n\r\n", 1)
                lengths = [int(line.split(b":", 1)[1]) for line in head.split(b"\r\n") if line.lower().startswith(b"content-length:")]
                if not lengths or len(rest) < lengths[0]:
                    break
                raw, self.buf = rest[:lengths[0]], rest[lengths[0]:]
                msg = json.loads(raw)
                record("server_message", message=msg)
                if msg.get("method") == "client/registerCapability" and "id" in msg:
                    self.send({"jsonrpc": "2.0", "id": msg["id"], "result": None})
                return msg
            ready, _, _ = select.select([self.p.stdout], [], [], min(0.2, max(0, end - time.monotonic())))
            if ready:
                chunk = os.read(self.p.stdout.fileno(), 65536)
                if not chunk:
                    break
                self.buf += chunk
        raise TimeoutError("Lean server response timeout")

    def req(self, method, params, timeout=20):
        rid = self.next_id
        self.next_id += 1
        self.send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            msg = self.recv(max(0.1, end - time.monotonic()))
            if msg.get("id") == rid:
                return msg
        raise TimeoutError(f"no response to {method} id={rid}")

    def open(self, filename, text, version=1, materialize=True):
        path = FIXTURE / filename
        if materialize:
            path.write_text(text)
        uri = path.as_uri()
        self.send({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {"uri": uri, "languageId": "lean", "version": version, "text": text}}})
        barrier = self.req("textDocument/waitForDiagnostics", {"uri": uri, "version": version})
        record("barrier", filename=filename, version=version, response=barrier)
        return uri

    def change(self, uri, text, version):
        self.send({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {"textDocument": {"uri": uri, "version": version}, "contentChanges": [{"text": text}]}})
        barrier = self.req("textDocument/waitForDiagnostics", {"uri": uri, "version": version})
        record("barrier", uri=uri, version=version, response=barrier)

    def goal(self, label, uri, version):
        result = self.req("$/lean/plainGoal", {"textDocument": {"uri": uri, "version": version}, "position": {"line": 2, "character": 5}})
        record("goal", label=label, response=result)
        return result

    def close(self, uri):
        self.send({"jsonrpc": "2.0", "method": "textDocument/didClose", "params": {"textDocument": {"uri": uri}}})

    def stop(self):
        try:
            self.req("shutdown", None, timeout=5)
            self.send({"jsonrpc": "2.0", "method": "exit"})
            self.p.wait(timeout=5)
        except Exception as e:
            record("shutdown_failure", error=repr(e))
            self.p.kill()
            self.p.wait()
        record("server_exit", exit_code=self.p.returncode, stderr=self.p.stderr.read().decode(errors="replace"))


try:
    build_dep(OLD, "build_old_dependency")
    srv = Server()
    producer = srv.open("Dep.lean", OLD)
    consumer = srv.open("Consumer.lean", PROOF)
    srv.goal("consumer_before_unsaved_edit", consumer, 1)
    srv.change(producer, NEW, 2)
    record("unsaved_producer_state", buffer_sha256=sha(NEW), disk_sha256=sha((FIXTURE / "Dep.lean").read_bytes()), olean_sha256=sha((FIXTURE / "Dep.olean").read_bytes()), proof_sha256=sha(PROOF))
    srv.goal("consumer_after_unsaved_edit", consumer, 1)
    fresh_unsaved = srv.open("FreshWhileProducerUnsaved.lean", PROOF)
    srv.goal("new_consumer_while_producer_unsaved", fresh_unsaved, 1)
    run("batch_with_old_artifact", [str(LEAN), "--json", "Consumer.lean"])
    build_dep(NEW, "build_new_dependency")
    record("materialized_state", buffer_sha256=sha(NEW), disk_sha256=sha((FIXTURE / "Dep.lean").read_bytes()), olean_sha256=sha((FIXTURE / "Dep.olean").read_bytes()), proof_sha256=sha(PROOF))
    srv.send({"jsonrpc": "2.0", "method": "workspace/didChangeWatchedFiles", "params": {"changes": [{"uri": (FIXTURE / "Dep.lean").as_uri(), "type": 2}]}})
    srv.goal("old_consumer_after_materialization", consumer, 1)
    fresh_materialized = srv.open("FreshAfterMaterialization.lean", PROOF)
    srv.goal("new_consumer_after_materialization", fresh_materialized, 1)
    run("batch_with_new_artifact", [str(LEAN), "--json", "Consumer.lean"])
    srv.close(consumer)
    reopened = srv.open("Consumer.lean", PROOF, 2)
    srv.goal("reopened_consumer_after_materialization", reopened, 2)
    missing = FIXTURE / "OnlyBuffer.lean"
    missing.unlink(missing_ok=True)
    (FIXTURE / "OnlyBuffer.olean").unlink(missing_ok=True)
    srv.open("OnlyBuffer.lean", "def onlyBufferValue : Nat := 9\n", materialize=False)
    record("open_only_buffer", source_exists=missing.exists(), artifact_exists=(FIXTURE / "OnlyBuffer.olean").exists())
    srv.open("ImportsOnlyBuffer.lean", "import OnlyBuffer\n#check onlyBufferValue\n")
    srv.stop()
    record("lean_version", value=subprocess.check_output([str(LEAN), "--version"], text=True).strip())
except Exception as e:
    record("fatal", error=repr(e))
    if "srv" in globals():
        srv.stop()
    raise
finally:
    raw = json.dumps(EVENTS, indent=2) + "\n"
    raw = raw.replace(str(FIXTURE), "$FIXTURE").replace(str(LEAN), "$LEAN_BIN").replace(str(LEAN.parent.parent), "$TOOLCHAIN")
    (ROOT / "transcript.json").write_text(raw)
