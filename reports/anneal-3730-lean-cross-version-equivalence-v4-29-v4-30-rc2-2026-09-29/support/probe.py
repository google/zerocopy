#!/usr/bin/env python3
"""Bounded, pin-specific Lean/Lake equivalence and refresh experiment.

Usage: python3 support/probe.py --work /new/empty/scratch/path
No toolchain downloads or installs are attempted. All heavy work stays in --work.
"""
import argparse
import hashlib
import json
import os
import select
import shutil
import subprocess
import time
from pathlib import Path

TOOLCHAINS = {
    "v4.29.0": "leanprover--lean4---v4.29.0",
    "v4.30.0-rc2": "leanprover--lean4---v4.30.0-rc2",
}
REPO_TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains")
PROOF = "import Dep\ntheorem generatedEq : depValue + 1 = 8 := by\n  decide\n#print axioms generatedEq\n#eval depValue\n"


def sha(data):
    return hashlib.sha256(data if isinstance(data, bytes) else data.encode()).hexdigest()


def command(label, argv, cwd, env, events, timeout=45):
    start = time.monotonic()
    try:
        p = subprocess.run([str(x) for x in argv], cwd=cwd, env=env,
                           capture_output=True, text=True, timeout=timeout)
        row = dict(kind="command", label=label, argv=[str(x) for x in argv], cwd=str(cwd),
                   rc=p.returncode, stdout=p.stdout, stderr=p.stderr,
                   wall_ms=round((time.monotonic()-start)*1000, 1))
    except subprocess.TimeoutExpired as e:
        row = dict(kind="command", label=label, argv=[str(x) for x in argv], cwd=str(cwd),
                   rc="timeout", stdout=str(e.stdout), stderr=str(e.stderr),
                   wall_ms=round((time.monotonic()-start)*1000, 1))
    events.append(row)
    return row


def inventory(root):
    return {str(p.relative_to(root)): {"sha256": sha(p.read_bytes()), "bytes": p.stat().st_size}
            for p in sorted(root.rglob("*")) if p.is_file() and
            (p.suffix in (".olean", ".ilean", ".trace") or p.name in ("Dep.lean", "Generated.lean", "lakefile.toml", "lean-toolchain"))}


def make_project(root, version):
    root.mkdir(parents=True)
    (root / "lean-toolchain").write_text("leanprover/lean4:" + version + "\n")
    (root / "lakefile.toml").write_text('name = "cross_version"\ndefaultTargets = ["Dep"]\n[[lean_lib]]\nname = "Dep"\n')
    (root / "Dep.lean").write_text("def depValue : Nat := 7\n")
    (root / "Generated.lean").write_text(PROOF)


class Server:
    def __init__(self, label, argv, cwd, env, events):
        self.label, self.events = label, events
        self.buffer, self.seq = b"", 1
        self.messages = []
        self.p = subprocess.Popen([str(x) for x in argv], cwd=cwd, env=env,
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                  bufsize=0)
        self.events.append(dict(kind="server_start", label=label, argv=[str(x) for x in argv],
                                cwd=str(cwd), pid=self.p.pid))
        self.req("initialize", {"processId": os.getpid(), "rootUri": cwd.as_uri(),
                                "capabilities": {}, "initializationOptions": {"hasWidgets": False}})
        self.send({"jsonrpc": "2.0", "method": "initialized", "params": {}})

    def send(self, message):
        body = json.dumps(message, separators=(",", ":")).encode()
        self.p.stdin.write(b"Content-Length: " + str(len(body)).encode() + b"\r\n\r\n" + body)
        self.p.stdin.flush()
        self.events.append(dict(kind="client", label=self.label, message=message))

    def recv(self, timeout=20):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            if b"\r\n\r\n" in self.buffer:
                head, body = self.buffer.split(b"\r\n\r\n", 1)
                length = [int(x.split(b":", 1)[1]) for x in head.split(b"\r\n")
                          if x.lower().startswith(b"content-length:")]
                if length and len(body) >= length[0]:
                    raw, self.buffer = body[:length[0]], body[length[0]:]
                    message = json.loads(raw)
                    self.messages.append(message)
                    self.events.append(dict(kind="server", label=self.label, message=message))
                    if message.get("method") == "client/registerCapability" and "id" in message:
                        self.send({"jsonrpc": "2.0", "id": message["id"], "result": None})
                    return message
            ready, _, _ = select.select([self.p.stdout], [], [], min(.2, max(0, end-time.monotonic())))
            if ready:
                block = os.read(self.p.stdout.fileno(), 65536)
                if not block:
                    break
                self.buffer += block
        raise TimeoutError(self.label)

    def req(self, method, params, timeout=20):
        rid = self.seq
        self.seq += 1
        self.send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            message = self.recv(max(.1, end-time.monotonic()))
            if message.get("id") == rid:
                return message
        raise TimeoutError(method)

    def open(self, path, version=1):
        uri = path.as_uri()
        self.send({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params":
                   {"textDocument": {"uri": uri, "languageId": "lean", "version": version,
                                     "text": path.read_text()}}})
        wait = self.req("textDocument/waitForDiagnostics", {"uri": uri, "version": version})
        return uri, wait

    def goal(self, uri, version=1):
        return self.req("$/lean/plainGoal", {"textDocument": {"uri": uri, "version": version},
                                             "position": {"line": 2, "character": 8}})

    def close(self, uri):
        self.send({"jsonrpc": "2.0", "method": "textDocument/didClose",
                   "params": {"textDocument": {"uri": uri}}})

    def stop(self):
        try:
            self.req("shutdown", None, 5)
            self.send({"jsonrpc": "2.0", "method": "exit"})
            self.p.wait(timeout=5)
        except Exception as e:
            self.events.append(dict(kind="server_stop_error", label=self.label, error=repr(e)))
            self.p.kill()
            self.p.wait(timeout=5)
        self.events.append(dict(kind="server_exit", label=self.label, rc=self.p.returncode,
                                stderr=self.p.stderr.read().decode(errors="replace")))


def live(label, argv, root, env, events):
    srv = Server(label, argv, root, env, events)
    try:
        uri, wait = srv.open(root / "Generated.lean")
        goal = srv.goal(uri)
        diagnostics = [m.get("params") for m in srv.messages
                       if m.get("method") == "textDocument/publishDiagnostics" and
                       m.get("params", {}).get("uri") == uri]
        return {"wait": wait, "goal": goal, "diagnostics": diagnostics}
    finally:
        srv.stop()


def refresh(label, argv, root, env, lean, events):
    srv = Server(label, argv, root, env, events)
    try:
        uri, first_wait = srv.open(root / "Generated.lean")
        first = srv.goal(uri)
        old_hash = sha((root / ".lake/build/lib/lean/Dep.olean").read_bytes())
        shutil.copy2(root / "replacement/Dep.olean", root / ".lake/build/lib/lean/Dep.olean")
        new_hash = sha((root / ".lake/build/lib/lean/Dep.olean").read_bytes())
        srv.send({"jsonrpc": "2.0", "method": "workspace/didChangeWatchedFiles", "params":
                  {"changes": [{"uri": (root / ".lake/build/lib/lean/Dep.olean").as_uri(), "type": 2}]}})
        old_after = srv.goal(uri)
        srv.close(uri)
        reopened_uri, reopen_wait = srv.open(root / "Generated.lean", 2)
        reopened = srv.goal(reopened_uri, 2)
        batch = command(label+"-fresh-batch", [lean, "--json", "Generated.lean"], root, env, events)
        return {"source_sha256": sha((root / "Generated.lean").read_bytes()),
                "dependency_source_sha256": sha((root / "Dep.lean").read_bytes()),
                "old_olean_sha256": old_hash, "new_olean_sha256": new_hash,
                "first_wait": first_wait, "old_goal_before": first, "old_goal_after": old_after,
                "reopened_wait": reopen_wait, "reopened_goal": reopened,
                "fresh_batch": batch}
    finally:
        srv.stop()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--work", type=Path, required=True)
    args = ap.parse_args()
    work = args.work.resolve()
    if work.exists():
        raise SystemExit("--work must be absent")
    work.mkdir(parents=True)
    output = Path(__file__).resolve().parent / "results.json"
    events = []
    result = {"work": str(work), "versions": {}, "events": events,
              "fixture_proof_sha256": sha(PROOF)}
    try:
        for version, directory in TOOLCHAINS.items():
            tool = REPO_TOOLS / directory
            lean, lake = tool / "bin/lean", tool / "bin/lake"
            if not (lean.is_file() and lake.is_file()):
                raise FileNotFoundError(f"cached tools missing for {version}: {tool}")
            home = work / ("home-" + version)
            home.mkdir()
            env = dict(os.environ, HOME=str(home), PATH=str(tool / "bin")+os.pathsep+os.environ.get("PATH", ""),
                       ELAN_TOOLCHAIN="leanprover/lean4:"+version, LEAN_NUM_THREADS="1",
                       LAKE_ARTIFACT_CACHE="false", MATHLIB_NO_CACHE_ON_UPDATE="1",
                       LAKE_CACHE_DIR=str(home / "lake-cache"))
            root = work / version
            clean = root / "clean"
            make_project(clean, version)
            entry = {"toolchain_dir": str(tool), "lean_sha256": sha(lean.read_bytes()),
                     "lake_sha256": sha(lake.read_bytes()), "source_hashes":
                     {p.name: sha(p.read_bytes()) for p in clean.glob("*.lean")}}
            entry["versions"] = [command(version+"-lean-version", [lean, "--version"], clean, env, events),
                                  command(version+"-lake-version", [lake, "--version"], clean, env, events)]
            build = command(version+"-clean-build", [lake, "build", "Dep"], clean, env, events, 90)
            if build["rc"] != 0 or not (clean / ".lake/build/lib/lean/Dep.olean").exists():
                raise RuntimeError(f"build failed: {version}")
            prepared = root / "prepared"
            shutil.copytree(clean, prepared)
            entry["clean_inventory"] = inventory(clean)
            entry["prepared_inventory_before"] = inventory(prepared)
            entry["baseline"] = {}
            for kind, path in (("clean", clean), ("prepared", prepared)):
                env_path = dict(env, LEAN_PATH=str(path / ".lake/build/lib/lean"))
                rows = []
                for mode, argv in (("direct", [lean, "--json", "Generated.lean"]),
                                   ("lake-env", [lake, "env", "lean", "--json", "Generated.lean"])):
                    rows.append(command(version+"-"+kind+"-"+mode+"-batch", argv, path, env_path, events))
                setup = command(version+"-"+kind+"-setup", [lake, "--no-cache", "--no-build", "setup-file", "Generated.lean"], path, env_path, events)
                lives = {}
                for mode, argv in (("direct", [lean, "--server"]),
                                   ("lake-env", [lake, "env", "lean", "--server"]),
                                   ("lake-serve", [lake, "serve"])):
                    lives[mode] = live(version+"-"+kind+"-"+mode, argv, path, env_path, events)
                entry["baseline"][kind] = {"batch": rows, "setup": setup, "live": lives}
            entry["prepared_inventory_after"] = inventory(prepared)

            # Independent source-only and artifact-only cells, both copied from the same prepared baseline.
            source_only = root / "source-only"
            shutil.copytree(prepared, source_only)
            (source_only / "Dep.lean").write_text("def depValue : Nat := 9\n")
            source_env = dict(env, LEAN_PATH=str(source_only / ".lake/build/lib/lean"))
            entry["source_only"] = {"inventory": inventory(source_only),
                "direct_batch": command(version+"-source-only-direct", [lean, "--json", "Generated.lean"], source_only, source_env, events),
                "lake_batch": command(version+"-source-only-lake", [lake, "env", "lean", "--json", "Generated.lean"], source_only, source_env, events),
                "no_build": command(version+"-source-only-no-build", [lake, "--no-cache", "--no-build", "build", "Dep"], source_only, source_env, events)}
            entry["source_only"]["live"] = {}
            for mode, argv in (("direct", [lean, "--server"]),
                               ("lake-env", [lake, "env", "lean", "--server"]),
                               ("lake-serve", [lake, "serve"])):
                cell = root / ("source-live-"+mode)
                shutil.copytree(source_only, cell)
                cell_env = dict(env, LEAN_PATH=str(cell / ".lake/build/lib/lean"))
                before = inventory(cell)
                live_result = live(version+"-source-only-"+mode, argv, cell, cell_env, events)
                entry["source_only"]["live"][mode] = {
                    "before_inventory": before, "after_inventory": inventory(cell),
                    "result": live_result}

            artifact = root / "artifact-only"
            shutil.copytree(prepared, artifact)
            replacement = artifact / "replacement"
            replacement.mkdir()
            (replacement / "Dep.lean").write_text("def depValue : Nat := 9\n")
            build_replacement = command(version+"-replacement-build", [lean, "-o", "Dep.olean", "Dep.lean"], replacement, env, events)
            if build_replacement["rc"] != 0:
                raise RuntimeError(f"replacement build failed: {version}")
            artifact_env = dict(env, LEAN_PATH=str(artifact / ".lake/build/lib/lean"))
            entry["artifact_only_refresh"] = {}
            for mode, argv in (("direct", [lean, "--server"]),
                               ("lake-env", [lake, "env", "lean", "--server"]),
                               ("lake-serve", [lake, "serve"])):
                # Each mode gets an identical pristine prepared copy so it can perform its own replacement.
                cell = root / ("artifact-refresh-"+mode)
                shutil.copytree(artifact, cell)
                cell_env = dict(env, LEAN_PATH=str(cell / ".lake/build/lib/lean"))
                entry["artifact_only_refresh"][mode] = refresh(version+"-artifact-"+mode, argv, cell, cell_env, lean, events)
            shutil.copy2(replacement / "Dep.olean", artifact / ".lake/build/lib/lean/Dep.olean")
            entry["artifact_only"] = {"inventory": inventory(artifact),
                "direct_batch": command(version+"-artifact-only-direct", [lean, "--json", "Generated.lean"], artifact, artifact_env, events),
                "lake_batch": command(version+"-artifact-only-lake", [lake, "env", "lean", "--json", "Generated.lean"], artifact, artifact_env, events),
                "no_build": command(version+"-artifact-only-no-build", [lake, "--no-cache", "--no-build", "build", "Dep"], artifact, artifact_env, events)}
            result["versions"][version] = entry
    finally:
        serialized = json.dumps(result, indent=2, sort_keys=True)+"\n"
        serialized = serialized.replace(str(work), "$WORK")
        serialized = serialized.replace(str(REPO_TOOLS), "$CACHED_TOOLCHAINS")
        output.write_text(serialized)
    print(json.dumps({"versions": list(result["versions"]), "events": len(events),
                      "results": str(output)}, indent=2))


if __name__ == "__main__":
    main()
