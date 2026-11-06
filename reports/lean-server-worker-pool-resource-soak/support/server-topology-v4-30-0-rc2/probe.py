#!/usr/bin/env python3
"""Direct Lean server topology probe, deliberately limited to two open files."""
import hashlib
import json
import os
import select
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
WORK = ROOT / "work"
LEAN = Path(os.environ["LEAN_BIN"]).resolve()
START = time.monotonic()
EVENTS = []
SERVERS = []
RSS_LIMIT = 1536 * 1024 * 1024


def sha(data):
    if isinstance(data, str):
        data = data.encode()
    return hashlib.sha256(data).hexdigest()


def rec(kind, **fields):
    EVENTS.append({"seq": len(EVENTS), "ms": round((time.monotonic() - START) * 1000, 1),
                   "kind": kind, **fields})


def run(label, argv, cwd, env_extra=None):
    t = time.monotonic()
    p = subprocess.run(argv, cwd=cwd, env=dict(os.environ, LEAN_NUM_THREADS="1", **(env_extra or {})),
                       capture_output=True, text=True, timeout=20)
    rec("command", label=label, argv=argv, cwd=str(cwd), rc=p.returncode,
        stdout=p.stdout, stderr=p.stderr, wall_ms=round((time.monotonic() - t) * 1000, 1))
    return p


def process_snapshot(label, roots):
    p = subprocess.run(["ps", "-axo", "pid=,ppid=,rss=,comm="], capture_output=True, text=True, timeout=5)
    if p.returncode:
        rec("process_snapshot_unavailable", label=label, rc=p.returncode, stderr=p.stderr)
        return None
    all_rows = {}
    for line in p.stdout.splitlines():
        pieces = line.strip().split(maxsplit=3)
        if len(pieces) == 4:
            try:
                pid, ppid, rss = map(int, pieces[:3])
            except ValueError:
                continue
            all_rows[pid] = {"pid": pid, "ppid": ppid, "rss_bytes": rss * 1024,
                             "command": pieces[3]}
    frontier = set(roots)
    included = set()
    while frontier:
        pid = frontier.pop()
        if pid in included:
            continue
        included.add(pid)
        frontier.update(row["pid"] for row in all_rows.values() if row["ppid"] == pid)
    rows = [all_rows[pid] for pid in sorted(included) if pid in all_rows]
    total = sum(row["rss_bytes"] for row in rows)
    snapshot = {"label": label, "root_pids": roots, "processes": rows,
                "count": len(rows), "summed_rss_bytes": total}
    rec("process_snapshot", **snapshot)
    if total > RSS_LIMIT:
        raise MemoryError(f"process-tree RSS guard exceeded: {total}")
    return snapshot


class Server:
    def __init__(self, label, cwd, lean_path):
        self.label = label
        self.cwd = cwd
        self.buf = b""
        self.next_id = 2
        self.last_diags = {}
        self.epoch = len(SERVERS) + 1
        t = time.monotonic()
        self.p = subprocess.Popen([str(LEAN), "--server"], cwd=cwd,
                                  env=dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(lean_path)),
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        SERVERS.append(self)
        rec("server_start", label=label, epoch=self.epoch, pid=self.p.pid,
            cwd=str(cwd), lean_path=str(lean_path))
        self.send({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                   "params": {"processId": os.getpid(), "rootUri": cwd.as_uri(),
                              "capabilities": {}, "initializationOptions": {"hasWidgets": False}}})
        self.until(lambda m: m.get("id") == 1)
        self.send({"jsonrpc": "2.0", "method": "initialized", "params": {}})
        rec("server_initialized", label=label, epoch=self.epoch,
            wall_ms=round((time.monotonic() - t) * 1000, 1))

    def send(self, m):
        payload = json.dumps(m, separators=(",", ":")).encode()
        self.p.stdin.write(b"Content-Length: " + str(len(payload)).encode() + b"\r\n\r\n" + payload)
        self.p.stdin.flush()
        rec("lsp_client", label=self.label, epoch=self.epoch, message=m)

    def read(self, timeout=15):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if b"\r\n\r\n" in self.buf:
                header, body = self.buf.split(b"\r\n\r\n", 1)
                lengths = [int(line.split(b":", 1)[1]) for line in header.split(b"\r\n")
                           if line.lower().startswith(b"content-length:")]
                if lengths and len(body) >= lengths[0]:
                    raw, self.buf = body[:lengths[0]], body[lengths[0]:]
                    m = json.loads(raw)
                    rec("lsp_server", label=self.label, epoch=self.epoch, message=m)
                    if m.get("method") == "textDocument/publishDiagnostics":
                        ps = m["params"]
                        self.last_diags[ps["uri"]] = ps
                    if m.get("method") == "client/registerCapability" and "id" in m:
                        self.send({"jsonrpc": "2.0", "id": m["id"], "result": None})
                    return m
            ready, _, _ = select.select([self.p.stdout], [], [], min(0.1, max(0, deadline - time.monotonic())))
            if ready:
                block = os.read(self.p.stdout.fileno(), 65536)
                if not block:
                    break
                self.buf += block
        raise TimeoutError(f"server {self.label} response")

    def until(self, predicate):
        deadline = time.monotonic() + 15
        while time.monotonic() < deadline:
            m = self.read(max(0.1, deadline - time.monotonic()))
            if predicate(m):
                return m
        raise TimeoutError(f"server {self.label} predicate")

    def request(self, method, params):
        rid = self.next_id
        self.next_id += 1
        t = time.monotonic()
        self.send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
        response = self.until(lambda m: m.get("id") == rid)
        rec("request_latency", label=self.label, epoch=self.epoch, method=method,
            request_id=rid, wall_ms=round((time.monotonic() - t) * 1000, 1))
        return response

    def open(self, path, text, version=1):
        uri = path.as_uri()
        t = time.monotonic()
        self.send({"jsonrpc": "2.0", "method": "textDocument/didOpen",
                   "params": {"textDocument": {"uri": uri, "languageId": "lean",
                                               "version": version, "text": text}}})
        wait = self.request("textDocument/waitForDiagnostics", {"uri": uri, "version": version})
        rec("document_ready", label=self.label, epoch=self.epoch, uri=uri, version=version,
            text_sha256=sha(text), wall_ms=round((time.monotonic() - t) * 1000, 1),
            last_diagnostics=self.last_diags.get(uri), wait=wait)
        return uri

    def change(self, uri, text, version):
        self.send({"jsonrpc": "2.0", "method": "textDocument/didChange",
                   "params": {"textDocument": {"uri": uri, "version": version},
                              "contentChanges": [{"text": text}]}})
        return self.request("textDocument/waitForDiagnostics", {"uri": uri, "version": version})

    def close_document(self, uri):
        self.send({"jsonrpc": "2.0", "method": "textDocument/didClose",
                   "params": {"textDocument": {"uri": uri}}})

    def goal(self, uri, line, character):
        return self.request("$/lean/plainGoal", {"textDocument": {"uri": uri},
                                                    "position": {"line": line, "character": character}})

    def rpc_connect(self, uri):
        return self.request("$/lean/rpc/connect", {"uri": uri})

    def rpc_goal(self, uri, session_id, line, character):
        return self.request("$/lean/rpc/call", {"textDocument": {"uri": uri},
                                                  "position": {"line": line, "character": character},
                                                  "sessionId": session_id,
                                                  "method": "Lean.Widget.getInteractiveGoals",
                                                  "params": {"textDocument": {"uri": uri},
                                                             "position": {"line": line, "character": character}}})

    def stop(self):
        if self.p.poll() is not None:
            return
        try:
            self.request("shutdown", None)
            self.send({"jsonrpc": "2.0", "method": "exit"})
            self.p.wait(timeout=4)
        finally:
            if self.p.poll() is None:
                self.p.kill()
                self.p.wait()
            rec("server_exit", label=self.label, epoch=self.epoch, pid=self.p.pid,
                rc=self.p.returncode, stderr=self.p.stderr.read().decode(errors="replace"))


def write_fixture():
    WORK.mkdir(exist_ok=True)
    for name, value in (("A", 11), ("B", 22)):
        directory = WORK / name
        directory.mkdir(exist_ok=True)
        dep = f"def selected : Nat := {value}\n"
        proof = (f"import Dep\n#eval selected\ntheorem claim : selected = {value} := by\n"
                 f"  rfl\ntheorem scratch : selected = {value} := by\n  exact ?_\n")
        (directory / "Dep.lean").write_text(dep)
        (directory / "Proof.lean").write_text(proof)
        p = run("build-" + name, [str(LEAN), "-o", "Dep.olean", "Dep.lean"], directory)
        assert p.returncode == 0, p.stderr
        rec("fixture", name=name, dep_sha256=sha(dep), proof_sha256=sha(proof),
            olean_sha256=sha((directory / "Dep.olean").read_bytes()))
    scratch = "import Dep\ntheorem scratchClaim : selected = 11 := by\n  exact ?_\n"
    (WORK / "A" / "Scratch.lean").write_text(scratch)
    rec("scratch_fixture", text_sha256=sha(scratch))


def document_sample(server, directory):
    text = (directory / "Proof.lean").read_text()
    uri = server.open(directory / "Proof.lean", text)
    goal = server.goal(uri, 5, len(text.splitlines()[5]))
    rec("document_sample", label=server.label, epoch=server.epoch, uri=uri,
        goal=goal, diagnostics=server.last_diags.get(uri), text_sha256=sha(text))
    return uri


def main():
    try:
        rec("subject", lean_version=subprocess.check_output([str(LEAN), "--version"], text=True).strip(),
            lean_sha256=sha(LEAN.read_bytes()), rss_limit_bytes=RSS_LIMIT)
        write_fixture()
        a, b = WORK / "A", WORK / "B"
        # Phase 1: two files under one process-global cwd and LEAN_PATH.
        shared = Server("shared-A", a, a)
        document_sample(shared, a)
        document_sample(shared, b)
        process_snapshot("shared-two-files", [shared.p.pid])
        shared.stop()
        process_snapshot("shared-after-stop", [shared.p.pid])
        # Phase 2: same files under independent process-global environments.
        sa = Server("separate-A", a, a)
        sb = Server("separate-B", b, b)
        document_sample(sa, a)
        document_sample(sb, b)
        process_snapshot("separate-two-servers", [sa.p.pid, sb.p.pid])
        sa.stop()
        sb.stop()
        process_snapshot("separate-after-stop", [sa.p.pid, sb.p.pid])
        # Phase 3: one scratch URI reused in a worker, then closed/reopened.
        scratch = Server("scratch-reuse", a, a)
        initial = (a / "Scratch.lean").read_text()
        uri = scratch.open(a / "Scratch.lean", initial, 1)
        goal1 = scratch.goal(uri, 2, len(initial.splitlines()[2]))
        conn1 = scratch.rpc_connect(uri)
        sid1 = conn1.get("result", {}).get("sessionId")
        rpc1 = scratch.rpc_goal(uri, sid1, 2, len(initial.splitlines()[2])) if sid1 is not None else None
        process_snapshot("scratch-first-worker", [scratch.p.pid])
        solved = initial.replace("exact ?_", "rfl")
        scratch.change(uri, solved, 2)
        goal2 = scratch.goal(uri, 2, len(solved.splitlines()[2]))
        rec("scratch_reused_worker", initial_goal=goal1, solved_goal=goal2,
            initial_sha256=sha(initial), solved_sha256=sha(solved), rpc_connect=conn1,
            rpc_goal=rpc1)
        scratch.close_document(uri)
        process_snapshot("scratch-after-close", [scratch.p.pid])
        scratch.open(a / "Scratch.lean", initial, 1)
        old_rpc = scratch.rpc_goal(uri, sid1, 2, len(initial.splitlines()[2])) if sid1 is not None else None
        conn2 = scratch.rpc_connect(uri)
        sid2 = conn2.get("result", {}).get("sessionId")
        rpc2 = scratch.rpc_goal(uri, sid2, 2, len(initial.splitlines()[2])) if sid2 is not None else None
        goal3 = scratch.goal(uri, 2, len(initial.splitlines()[2]))
        process_snapshot("scratch-reopened-worker", [scratch.p.pid])
        rec("scratch_new_worker", old_rpc=old_rpc, fresh_connect=conn2, fresh_rpc=rpc2,
            reopened_goal=goal3, reused_document_version=1,
            old_session_id=sid1, new_session_id=sid2)
        scratch.stop()
        process_snapshot("scratch-after-stop", [scratch.p.pid])
        # Phase 4: fresh watchdog with request IDs restarted from 1.
        fresh = Server("scratch-fresh-server", a, a)
        fresh_uri = fresh.open(a / "Scratch.lean", initial, 1)
        fresh_goal = fresh.goal(fresh_uri, 2, len(initial.splitlines()[2]))
        rec("scratch_fresh_server", epoch=fresh.epoch, goal=fresh_goal,
            text_sha256=sha(initial), reused_document_version=1)
        fresh.stop()
        process_snapshot("fresh-after-stop", [fresh.p.pid])
        rec("completed")
    except Exception as e:
        rec("fatal", error=repr(e))
        raise
    finally:
        for s in SERVERS:
            if s.p.poll() is None:
                s.p.kill()
                s.p.wait()
                rec("forced_server_exit", label=s.label, epoch=s.epoch, pid=s.p.pid)
        data = json.dumps(EVENTS, indent=2) + "\n"
        data = data.replace(WORK.as_uri(), "$WORK_URI").replace(str(WORK), "$WORK")
        data = data.replace(str(LEAN), "$LEAN_BIN").replace(str(LEAN.parent.parent), "$LEAN_HOME")
        (ROOT / "transcript.json").write_text(data)


if __name__ == "__main__":
    main()
