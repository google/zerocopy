#!/usr/bin/env python3
"""Six tiny direct Lean/Lake layout cells; no Anneal source translation."""
import hashlib
import json
import os
import select
import shutil
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
WORK = ROOT / "work"
LEAN = Path(os.environ["LEAN_BIN"]).resolve()
LAKE = Path(os.environ["LAKE_BIN"]).resolve()
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


def command(label, args, cwd, extra=None, timeout=30):
    env = dict(os.environ, LEAN_NUM_THREADS="1", ELAN_TOOLCHAIN="leanprover/lean4:v4.30.0-rc2",
               LAKE_ARTIFACT_CACHE="false", MATHLIB_NO_CACHE_ON_UPDATE="1", **(extra or {}))
    start = time.monotonic()
    p = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True, timeout=timeout)
    result = {"label": label, "argv": args, "cwd": str(cwd), "rc": p.returncode,
              "stdout": p.stdout, "stderr": p.stderr,
              "wall_ms": round((time.monotonic() - start) * 1000, 1)}
    rec("command", **result)
    return result


def inventory(directory):
    root = directory / ".lake/build/lib/lean"
    return {str(p.relative_to(root)): {"sha256": sha(p.read_bytes()), "bytes": p.stat().st_size,
                                     "mtime_ns": p.stat().st_mtime_ns}
            for p in sorted(root.rglob("*.olean"))} if root.exists() else {}


def processes(label, roots):
    p = subprocess.run(["ps", "-axo", "pid=,ppid=,rss=,comm="], capture_output=True, text=True, timeout=5)
    if p.returncode:
        rec("rss_unavailable", label=label, rc=p.returncode, stderr=p.stderr)
        return None
    all_rows = {}
    for line in p.stdout.splitlines():
        fields = line.strip().split(maxsplit=3)
        if len(fields) == 4:
            try:
                pid, ppid, kib = map(int, fields[:3])
            except ValueError:
                continue
            all_rows[pid] = {"pid": pid, "ppid": ppid, "rss_bytes": kib * 1024,
                             "command": fields[3]}
    todo, found = set(roots), set()
    while todo:
        pid = todo.pop()
        if pid in found:
            continue
        found.add(pid)
        todo.update(row["pid"] for row in all_rows.values() if row["ppid"] == pid)
    rows = [all_rows[pid] for pid in sorted(found) if pid in all_rows]
    result = {"label": label, "roots": roots, "rows": rows, "process_count": len(rows),
              "worker_count": sum(row["pid"] not in roots for row in rows),
              "summed_rss_bytes": sum(row["rss_bytes"] for row in rows)}
    rec("processes", **result)
    if result["summed_rss_bytes"] > RSS_LIMIT:
        raise MemoryError(result)
    return result


class Server:
    def __init__(self, label, cwd, lean_path):
        self.label = label
        self.cwd = cwd
        self.buf = b""
        self.next_id = 2
        self.p = subprocess.Popen([str(LEAN), "--server"], cwd=cwd,
                                  env=dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(lean_path)),
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        SERVERS.append(self)
        rec("server_start", label=label, pid=self.p.pid, cwd=str(cwd), lean_path=str(lean_path))
        self.send({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                   "params": {"processId": os.getpid(), "rootUri": cwd.as_uri(),
                              "capabilities": {}, "initializationOptions": {"hasWidgets": False}}})
        self.until(lambda m: m.get("id") == 1)
        self.send({"jsonrpc": "2.0", "method": "initialized", "params": {}})

    def send(self, message):
        data = json.dumps(message, separators=(",", ":")).encode()
        self.p.stdin.write(b"Content-Length: " + str(len(data)).encode() + b"\r\n\r\n" + data)
        self.p.stdin.flush()
        rec("lsp_client", label=self.label, message=message)

    def read(self, timeout=15):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            if b"\r\n\r\n" in self.buf:
                header, body = self.buf.split(b"\r\n\r\n", 1)
                lengths = [int(line.split(b":", 1)[1]) for line in header.split(b"\r\n")
                           if line.lower().startswith(b"content-length:")]
                if lengths and len(body) >= lengths[0]:
                    raw, self.buf = body[:lengths[0]], body[lengths[0]:]
                    message = json.loads(raw)
                    rec("lsp_server", label=self.label, message=message)
                    if message.get("method") == "client/registerCapability" and "id" in message:
                        self.send({"jsonrpc": "2.0", "id": message["id"], "result": None})
                    return message
            ready, _, _ = select.select([self.p.stdout], [], [], min(0.1, max(0, end - time.monotonic())))
            if ready:
                block = os.read(self.p.stdout.fileno(), 65536)
                if not block:
                    break
                self.buf += block
        raise TimeoutError(self.label)

    def until(self, predicate):
        end = time.monotonic() + 15
        while time.monotonic() < end:
            m = self.read(max(0.1, end - time.monotonic()))
            if predicate(m):
                return m
        raise TimeoutError(self.label)

    def request(self, method, params):
        rid = self.next_id
        self.next_id += 1
        self.send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
        return self.until(lambda m: m.get("id") == rid)

    def open(self, path):
        text = path.read_text()
        uri = path.as_uri()
        start = time.monotonic()
        self.send({"jsonrpc": "2.0", "method": "textDocument/didOpen",
                   "params": {"textDocument": {"uri": uri, "version": 1,
                                               "languageId": "lean", "text": text}}})
        wait = self.request("textDocument/waitForDiagnostics", {"uri": uri, "version": 1})
        rec("document_ready", label=self.label, uri=uri, text_sha256=sha(text),
            wall_ms=round((time.monotonic() - start) * 1000, 1), wait=wait)

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
            rec("server_exit", label=self.label, pid=self.p.pid, rc=self.p.returncode,
                stderr=self.p.stderr.read().decode(errors="replace"))


def fixture(size, layout):
    directory = WORK / f"pad{size}" / layout
    directory.mkdir(parents=True, exist_ok=True)
    model = "def modelValue : Nat := 7\n" + "".join(f"def pad{i} : Nat := {i}\n" for i in range(size))
    helper = "theorem helper (n : Nat) (h : n = modelValue) : n + 1 = 8 := by\n  rw [h]; rfl\n"
    one = "theorem claimOne (n : Nat) (h : n = modelValue) : n + 1 = 8 := by\n  exact helper n h\n"
    two = "theorem claimTwo (n : Nat) (h : n = modelValue) : n + 1 = 8 := by\n  exact helper n h\n"
    if layout == "per-annotation":
        sources = {"Model.lean": model, "Shared.lean": "import Model\n" + helper,
                   "AnnOne.lean": "import Shared\n" + one,
                   "AnnTwo.lean": "import Shared\n" + two,
                   "Aggregate.lean": "import AnnOne\nimport AnnTwo\nexample (n : Nat) (h : n = modelValue) : n + 1 = 8 := claimOne n h\nexample (n : Nat) (h : n = modelValue) : n + 1 = 8 := claimTwo n h\n"}
        proof_files = ("AnnOne.lean", "AnnTwo.lean")
        edit_file = "AnnOne.lean"
    elif layout == "per-file":
        sources = {"Model.lean": model, "File.lean": "import Model\n" + helper + one + two,
                   "Aggregate.lean": "import File\nexample (n : Nat) (h : n = modelValue) : n + 1 = 8 := claimOne n h\nexample (n : Nat) (h : n = modelValue) : n + 1 = 8 := claimTwo n h\n"}
        proof_files = ("File.lean",)
        edit_file = "File.lean"
    else:
        sources = {"Artifact.lean": model + helper + one + two,
                   "Aggregate.lean": "import Artifact\nexample (n : Nat) (h : n = modelValue) : n + 1 = 8 := claimOne n h\nexample (n : Nat) (h : n = modelValue) : n + 1 = 8 := claimTwo n h\n"}
        proof_files = ("Artifact.lean",)
        edit_file = "Artifact.lean"
    targets = [name.removesuffix(".lean") for name in sources if name.endswith(".lean")]
    sources["lakefile.lean"] = ("import Lake\nopen Lake DSL\npackage layout where\n" +
                                "".join(f"lean_lib {name}\n" for name in targets))
    sources["lean-toolchain"] = "leanprover/lean4:v4.30.0-rc2\n"
    for name, content in sources.items():
        (directory / name).write_text(content)
    rec("fixture", size=size, layout=layout, directory=str(directory),
        source_hashes={name: sha(content) for name, content in sources.items()},
        proof_files=proof_files, edit_file=edit_file)
    return directory, proof_files, edit_file, targets


def build_sequence(prefix, phase, directory, targets, expect_failure=False):
    outputs = []
    for target in targets:
        result = command(f"{prefix}-{phase}-{target}",
                         [str(LAKE), "--keep-toolchain", "--no-cache", "build", target], directory)
        outputs.append(result)
        if result["rc"] != 0:
            if not expect_failure:
                raise AssertionError((prefix, phase, target, result))
            break
    assert (outputs[-1]["rc"] != 0) == expect_failure
    return {"rc": outputs[-1]["rc"], "wall_ms": round(sum(x["wall_ms"] for x in outputs), 1),
            "targets_attempted": [x["label"] for x in outputs]}


def cell(size, layout):
    directory, proof_files, edit_file, targets = fixture(size, layout)
    prefix = f"{size}-{layout}"
    cold = build_sequence(prefix, "cold", directory, targets)
    before = inventory(directory)
    warm = build_sequence(prefix, "warm", directory, targets)
    for name in proof_files:
        proof = command(prefix + "-batch-" + name, [str(LEAN), "--json", name], directory,
                        {"LEAN_PATH": str(directory / ".lake/build/lib/lean")})
        assert proof["rc"] == 0, (prefix, name, proof)
    importer = command(prefix + "-aggregate-batch", [str(LEAN), "--json", "Aggregate.lean"],
                       directory, {"LEAN_PATH": str(directory / ".lake/build/lib/lean")})
    assert importer["rc"] == 0
    server = Server(prefix, directory, directory / ".lake/build/lib/lean")
    for name in proof_files:
        server.open(directory / name)
    process = processes(prefix + "-open", [server.p.pid])
    server.stop()
    processes(prefix + "-stopped", [server.p.pid])
    edit_path = directory / edit_file
    original = edit_path.read_text()
    edited = original.replace("exact helper n h", "exact (helper n h)", 1)
    assert edited != original
    edit_path.write_text(edited)
    incremental = build_sequence(prefix, "incremental", directory, targets)
    after = inventory(directory)
    changed = sorted(name for name in set(before) | set(after)
                     if before.get(name, {}).get("mtime_ns") != after.get(name, {}).get("mtime_ns"))
    rec("incremental_inventory", size=size, layout=layout, before=before, after=after,
        changed_mtime_modules=changed, edited_sha256=sha(edited))
    bad = edited.replace("exact (helper n h)", "exact ?_", 1)
    edit_path.write_text(bad)
    failure = build_sequence(prefix, "failure", directory, targets, expect_failure=True)
    sibling = None
    if layout == "per-annotation":
        sibling = command(prefix + "-sibling-batch", [str(LEAN), "--json", "AnnTwo.lean"], directory,
                          {"LEAN_PATH": str(directory / ".lake/build/lib/lean")})
        assert sibling["rc"] == 0
    rec("cell", size=size, layout=layout, cold_ms=cold["wall_ms"], warm_ms=warm["wall_ms"],
        aggregate_import_ms=importer["wall_ms"], incremental_ms=incremental["wall_ms"],
        failure_rc=failure["rc"], sibling_rc=sibling["rc"] if sibling else None,
        module_count=len(before), changed_mtime_modules=changed,
        worker_count=process["worker_count"] if process else None,
        summed_rss_bytes=process["summed_rss_bytes"] if process else None)


def main():
    try:
        if WORK.exists():
            shutil.rmtree(WORK)
        rec("subject", lean_version=subprocess.check_output([str(LEAN), "--version"], text=True).strip(),
            lean_sha256=sha(LEAN.read_bytes()), lake_sha256=sha(LAKE.read_bytes()),
            rss_limit_bytes=RSS_LIMIT)
        for size in (1, 128):
            for layout in ("per-annotation", "per-file", "per-artifact"):
                cell(size, layout)
        rec("completed")
    except Exception as e:
        rec("fatal", error=repr(e))
        raise
    finally:
        for server in SERVERS:
            if server.p.poll() is None:
                server.p.kill()
                server.p.wait()
                rec("forced_server_exit", label=server.label, pid=server.p.pid)
        data = json.dumps(EVENTS, indent=2) + "\n"
        data = data.replace(WORK.as_uri(), "$WORK_URI").replace(str(WORK), "$WORK")
        data = data.replace(str(LEAN), "$LEAN_BIN").replace(str(LAKE), "$LAKE_BIN")
        data = data.replace(str(LEAN.parent.parent), "$LEAN_HOME")
        (ROOT / "raw.json").write_text(data)


if __name__ == "__main__":
    main()
