#!/usr/bin/env python3
"""Serial, bounded replay of the supported local Lean import closure.

Outputs and cache live in an explicit external work directory. A cache entry
requires matching compiler/source/direct-dependency/object identities. This is
cooperative build caching, not authentication or a verified build system.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
SOURCE = Path(__file__).resolve().parents[1]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def reusable(entry, source_sha, dependencies, object_path):
    return (isinstance(entry, dict) and entry.get("source_sha256") == source_sha
            and entry.get("dependency_objects") == dependencies
            and object_path.is_file() and not object_path.is_symlink()
            and entry.get("object_sha256") == sha(object_path))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--label", required=True, help="new log directory name")
    parser.add_argument("--lean", default=shutil.which("lean"))
    parser.add_argument("modules", nargs="+")
    args = parser.parse_args()
    if not re.fullmatch(r"[a-z0-9-]+", args.label) or not args.lean:
        raise SystemExit("need a unique simple label and an installed Lean executable")
    workspace = args.work_dir.resolve()
    if workspace == SOURCE or SOURCE in workspace.parents:
        raise SystemExit("work-dir must be outside the source directory")
    cache = workspace / "cache"
    logs = workspace / "logs" / args.label
    logs.mkdir(parents=True)  # create-only; never overwrite an earlier run
    cache.mkdir(parents=True, exist_ok=True)
    version = subprocess.run([args.lean, "--version"], cwd=SOURCE,
                             capture_output=True, text=True, check=True).stdout.strip()
    if "version 4.34.1," not in version or "5045d0056413266e57c625dcd7c365b10e377c52" not in version:
        raise SystemExit("this experiment pins Lean4.34.1 commit5045d0056413266e57c625dcd7c365b10e377c52")
    index_path = cache / "index.json"
    index = json.loads(index_path.read_text()) if index_path.exists() else {}
    if index.get("lean_version") != version:
        index = {"lean_version": version, "modules": {}}
    modules = index["modules"]
    order, deps = [], {}

    def visit(name):
        if name in deps:
            if name not in order:
                raise SystemExit("cyclic local imports: " + name)
            return
        if not re.fullmatch(r"AnnealResearch\.[A-Za-z0-9_.]+", name):
            raise SystemExit("unsupported module: " + name)
        path = SOURCE / (name.replace(".", "/") + ".lean")
        text = path.read_text()
        if re.search(r"^(#eval|run_cmd|initialize|builtin_initialize)\b", text, re.M):
            raise SystemExit("unexpected executable metaprogram in " + name)
        imports = re.findall(r"^import ([A-Za-z0-9_.]+)\s*$", text, re.M)
        if any(not item.startswith("AnnealResearch.") for item in imports):
            raise SystemExit("unexpected nonlocal import in " + name)
        deps[name] = imports
        for item in imports:
            visit(item)
        order.append(name)

    for name in args.modules:
        visit(name)
    results = []
    env = dict(os.environ, LEAN_PATH=str(cache))
    for name in order:
        source = SOURCE / (name.replace(".", "/") + ".lean")
        object_path = cache / (name.replace(".", "/") + ".olean")
        object_path.parent.mkdir(parents=True, exist_ok=True)
        source_sha = sha(source)
        identities = {dep: modules[dep]["object_sha256"] for dep in deps[name]}
        result = {"module": name, "source_sha256": source_sha,
                  "dependency_objects": identities}
        if reusable(modules.get(name), source_sha, identities, object_path):
            result.update({"disposition": "reused matching compiler/source/dependency/object identities",
                           "object_sha256": sha(object_path)})
        else:
            command = [args.lean, "-j1", "-M2048", "-DElab.async=false", "--profile",
                       "-o", str(object_path), str(source)]
            start, peak, stop = time.monotonic(), 0, None
            with (logs / (name + ".stdout")).open("wb") as out, (logs / (name + ".stderr")).open("wb") as err:
                process = subprocess.Popen(command, cwd=SOURCE, env=env, stdout=out, stderr=err)
                try:
                    while process.poll() is None:
                        sample = subprocess.run(["ps", "-o", "rss=", "-p", str(process.pid)],
                                                capture_output=True, text=True)
                        if sample.returncode != 0:
                            if process.poll() is None:
                                stop = "RSS observer unavailable"
                        elif sample.stdout.strip():
                            peak = max(peak, int(sample.stdout.strip()) * 1024)
                        if peak >= 3 * 1024**3:
                            stop = "3GiB sampled direct-process RSS stop"
                        elif time.monotonic() - start >= 60:
                            stop = "60second deadline"
                        if stop:
                            process.kill()
                            break
                        time.sleep(.1)
                finally:
                    if process.poll() is None:
                        process.kill()
                    status = process.wait()
            result.update({"command": command, "exit_code": status,
                           "seconds": round(time.monotonic() - start, 3),
                           "sampled_peak_rss_bytes": peak, "stop_reason": stop})
            if status == 0 and stop is None:
                result["object_sha256"] = sha(object_path)
                modules[name] = {key: result[key] for key in
                                 ("source_sha256", "dependency_objects", "object_sha256")}
                staged = index_path.with_suffix(".json.staged")
                staged.write_text(json.dumps(index, indent=2) + "\n")
                staged.replace(index_path)
        results.append(result)
        (logs / "results.json").write_text(json.dumps({"lean_version": version, "results": results}, indent=2) + "\n")
        print(json.dumps(result), flush=True)
        if result.get("exit_code", 0) != 0 or result.get("stop_reason"):
            raise SystemExit("stopped; inspect " + str(logs))
    print("requested exact-source closure passed", flush=True)


if __name__ == "__main__":
    main()
