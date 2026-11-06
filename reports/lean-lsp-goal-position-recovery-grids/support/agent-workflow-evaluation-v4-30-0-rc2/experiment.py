#!/usr/bin/env python3
"""Disposable, narrow Lean proof workflow comparator; no Anneal integration."""
import argparse
import hashlib
import json
import os
import resource
import select
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
WORK = ROOT / "work"
LOG = ROOT / "events.jsonl"
LEAN = Path(os.environ["LEAN_BIN"]).resolve()


def sha(data):
    if isinstance(data, str):
        data = data.encode()
    return hashlib.sha256(data).hexdigest()


def event(kind, **fields):
    with LOG.open("a") as out:
        out.write(json.dumps({"time_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                              "kind": kind, **fields}, sort_keys=True) + "\n")


def command(label, args, cwd, env_extra=None):
    start = time.monotonic()
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    env = dict(os.environ, LEAN_NUM_THREADS="1", **(env_extra or {}))
    p = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True, timeout=30)
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    result = {"label": label, "argv": args, "cwd": str(cwd), "rc": p.returncode,
              "stdout": p.stdout, "stderr": p.stderr,
              "wall_ms": round((time.monotonic() - start) * 1000, 1),
              "child_user_s": round(after.ru_utime - before.ru_utime, 3),
              "child_system_s": round(after.ru_stime - before.ru_stime, 3),
              "child_maxrss_raw_cumulative": after.ru_maxrss}
    event("command", **result)
    return result


class LeanServer:
    def __init__(self, directory):
        self.directory = directory
        self.buf = b""
        self.next_id = 2
        self.p = subprocess.Popen([str(LEAN), "--server"], cwd=directory,
                                  env=dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(directory)),
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        event("server_start", directory=str(directory), pid=self.p.pid)
        self.send({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                   "params": {"processId": os.getpid(), "rootUri": directory.as_uri(),
                              "capabilities": {}, "initializationOptions": {"hasWidgets": False}}})
        self.until(lambda m: m.get("id") == 1)
        self.send({"jsonrpc": "2.0", "method": "initialized", "params": {}})

    def send(self, message):
        data = json.dumps(message, separators=(",", ":")).encode()
        self.p.stdin.write(b"Content-Length: " + str(len(data)).encode() + b"\r\n\r\n" + data)
        self.p.stdin.flush()
        event("lsp_client", directory=str(self.directory), message=message)

    def read(self, timeout=15):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if b"\r\n\r\n" in self.buf:
                header, body = self.buf.split(b"\r\n\r\n", 1)
                lengths = [int(line.split(b":", 1)[1]) for line in header.split(b"\r\n")
                           if line.lower().startswith(b"content-length:")]
                if lengths and len(body) >= lengths[0]:
                    raw, self.buf = body[:lengths[0]], body[lengths[0]:]
                    message = json.loads(raw)
                    event("lsp_server", directory=str(self.directory), message=message)
                    if message.get("method") == "client/registerCapability" and "id" in message:
                        self.send({"jsonrpc": "2.0", "id": message["id"], "result": None})
                    return message
            ready, _, _ = select.select([self.p.stdout], [], [], min(0.1, deadline - time.monotonic()))
            if ready:
                chunk = os.read(self.p.stdout.fileno(), 65536)
                if not chunk:
                    break
                self.buf += chunk
        raise TimeoutError("Lean server response")

    def until(self, predicate):
        deadline = time.monotonic() + 15
        while time.monotonic() < deadline:
            m = self.read(max(0.1, deadline - time.monotonic()))
            if predicate(m):
                return m
        raise TimeoutError("Lean server expected message")

    def request(self, method, params):
        rid = self.next_id
        self.next_id += 1
        self.send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
        return self.until(lambda m: m.get("id") == rid)

    def close(self):
        try:
            self.request("shutdown", None)
            self.send({"jsonrpc": "2.0", "method": "exit"})
            self.p.wait(timeout=3)
        finally:
            if self.p.poll() is None:
                self.p.kill()
                self.p.wait()
            event("server_exit", directory=str(self.directory), rc=self.p.returncode,
                  stderr=self.p.stderr.read().decode(errors="replace"))


def setup():
    WORK.mkdir(exist_ok=True)
    old = WORK / "old"
    old.mkdir(exist_ok=True)
    (old / "Generated.lean").write_text("def modelValue : Nat := 4\n")
    (old / "Proof.lean").write_text("import Generated\ntheorem claim (n : Nat) (h : n = modelValue) : n + 2 = 6 := by\n  exact ?_\n")
    for arm in ("exact", "batch"):
        directory = WORK / arm
        directory.mkdir(exist_ok=True)
        (directory / "Generated.lean").write_text("def modelValue : Nat := 5\n")
        (directory / "Proof.lean").write_text("import Generated\ntheorem claim (n : Nat) (h : n = modelValue) : n + 2 = 7 := by\n  exact ?_\n")
    for directory in (old, WORK / "exact", WORK / "batch"):
        r = command("build-" + directory.name, [str(LEAN), "--json", "-o", "Generated.olean", "Generated.lean"], directory)
        if r["rc"]:
            raise RuntimeError(r)
        event("snapshot", directory=str(directory), generated_sha256=sha((directory / "Generated.lean").read_bytes()),
              generated_olean_sha256=sha((directory / "Generated.olean").read_bytes()),
              proof_sha256=sha((directory / "Proof.lean").read_bytes()))
    event("tool_identity", version=subprocess.check_output([str(LEAN), "--version"], text=True).strip(),
          lean_sha256=sha(LEAN.read_bytes()), python=sys.version)


def query(arm):
    directory = WORK / arm
    proof = (directory / "Proof.lean").read_text()
    start = time.monotonic()
    server = LeanServer(directory)
    try:
        uri = (directory / "Proof.lean").as_uri()
        server.send({"jsonrpc": "2.0", "method": "textDocument/didOpen",
                     "params": {"textDocument": {"uri": uri, "languageId": "lean", "version": 1, "text": proof}}})
        diagnostics = server.request("textDocument/waitForDiagnostics", {"uri": uri, "version": 1})
        goal = server.request("$/lean/plainGoal", {"textDocument": {"uri": uri},
                                                    "position": {"line": 2, "character": len(proof.splitlines()[2])}})
        envelope = {"arm": arm, "document_version": 1, "proof_sha256": sha(proof),
                    "generated_olean_sha256": sha((directory / "Generated.olean").read_bytes()),
                    "diagnostics": diagnostics, "goal": goal,
                    "wall_ms": round((time.monotonic() - start) * 1000, 1)}
        event("query_envelope", **envelope)
        print(json.dumps(envelope, indent=2))
    finally:
        server.close()


def diagnose():
    directory = WORK / "batch"
    proof = (directory / "Proof.lean").read_bytes()
    event("batch_input", proof_sha256=sha(proof), generated_olean_sha256=sha((directory / "Generated.olean").read_bytes()))
    print(json.dumps(command("batch-diagnostics", [str(LEAN), "--json", "Proof.lean"], directory,
                             {"LEAN_PATH": str(directory)}), indent=2))


def inspect(arm):
    directory = WORK / arm
    proof = (directory / "Proof.lean").read_text()
    result = {"arm": arm, "proof": proof, "proof_sha256": sha(proof),
              "generated_olean_sha256": sha((directory / "Generated.olean").read_bytes())}
    event("inspect", **result)
    print(json.dumps(result, indent=2))


def conflict(arm):
    directory = WORK / arm
    proof_path = directory / "Proof.lean"
    old = proof_path.read_text()
    new = old + "-- concurrent harmless note\n"
    proof_path.write_text(new)
    event("concurrent_writer", arm=arm, before_sha256=sha(old), after_sha256=sha(new))


def apply(arm, expected, tactic):
    directory = WORK / arm
    path = directory / "Proof.lean"
    current = path.read_text()
    if sha(current) != expected:
        result = {"accepted": False, "reason": "proof_hash_conflict", "expected": expected,
                  "actual": sha(current), "arm": arm}
    elif "  exact ?_\n" not in current and "  simp [h, modelValue]\n" not in current:
        result = {"accepted": False, "reason": "expected_tactic_absent", "arm": arm}
    else:
        old_tactic = "  exact ?_\n" if "  exact ?_\n" in current else "  simp [h, modelValue]\n"
        new = current.replace(old_tactic, "  " + tactic + "\n", 1)
        path.write_text(new)
        result = {"accepted": True, "arm": arm, "before_sha256": sha(current), "after_sha256": sha(new),
                  "proof": new}
    event("guarded_edit", **result)
    print(json.dumps(result, indent=2))


def oracle(arm):
    directory = WORK / arm
    proof = (directory / "Proof.lean").read_text()
    batch = command("final-proof-" + arm, [str(LEAN), "--json", "-o", "Proof.olean", "Proof.lean"],
                    directory, {"LEAN_PATH": str(directory)})
    oracle_text = "import Proof\nexample (n : Nat) (h : n = modelValue) : n + 2 = 7 := claim n h\n#print axioms claim\n"
    (directory / "Oracle.lean").write_text(oracle_text)
    check = command("fixed-consumer-" + arm, [str(LEAN), "--json", "Oracle.lean"], directory,
                    {"LEAN_PATH": str(directory)}) if batch["rc"] == 0 else None
    result = {"arm": arm, "proof_sha256": sha(proof),
              "generated_olean_sha256": sha((directory / "Generated.olean").read_bytes()),
              "proof_olean_sha256": sha((directory / "Proof.olean").read_bytes()) if (directory / "Proof.olean").exists() else None,
              "oracle_sha256": sha(oracle_text), "proof_rc": batch["rc"],
              "consumer_rc": check["rc"] if check else None,
              "sorry_ax": "sorryAx" in check["stdout"] if check else None}
    event("oracle", **result)
    print(json.dumps(result, indent=2))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("action", choices=("setup", "query", "diagnose", "inspect", "conflict", "apply", "oracle"))
    parser.add_argument("--arm", choices=("old", "exact", "batch"))
    parser.add_argument("--expected")
    parser.add_argument("--tactic")
    args = parser.parse_args()
    if args.action == "setup": setup()
    elif args.action == "query": query(args.arm)
    elif args.action == "diagnose": diagnose()
    elif args.action == "inspect": inspect(args.arm)
    elif args.action == "conflict": conflict(args.arm)
    elif args.action == "apply": apply(args.arm, args.expected, args.tactic)
    elif args.action == "oracle": oracle(args.arm)


if __name__ == "__main__":
    main()
