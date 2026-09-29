#!/usr/bin/env python3
"""Offline same-target A -> B -> A source-edit probe for pinned Charon."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixture-origin"
WORK = Path(os.environ.get("I080_WORK_ROOT", HERE / "work")).resolve()
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
RUST = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"
CHARON = TOOLS / "bin/charon"
MIN_DISK = 10 * 1024**3
MIN_MEMORY = 30
TIMEOUT = 30
OLD = b"x.wrapping_add(1)"
NEW = b"x.wrapping_add(2)"

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def headroom():
    out = subprocess.check_output(["/usr/bin/memory_pressure", "-Q"], text=True)
    match = re.search(r"System-wide memory free percentage: (\d+)%", out)
    if not match:
        raise RuntimeError(out)
    return {"free_disk_bytes": shutil.disk_usage(WORK.parent).free,
            "free_memory_percent": int(match.group(1))}

def guarded():
    h = headroom()
    if h["free_disk_bytes"] < MIN_DISK or h["free_memory_percent"] < MIN_MEMORY:
        raise RuntimeError("headroom guard: " + repr(h))
    return h

def target_stats(target):
    if not target.exists():
        return {"files": 0, "file_bytes": 0, "incremental_files": 0,
                "incremental_bytes": 0, "allocated_kib": 0}
    files = [p for p in target.rglob("*") if p.is_file()]
    inc = [p for p in files if "incremental" in p.parts]
    du = subprocess.check_output(["/usr/bin/du", "-sk", str(target)], text=True)
    return {"files": len(files), "file_bytes": sum(p.stat().st_size for p in files),
            "incremental_files": len(inc),
            "incremental_bytes": sum(p.stat().st_size for p in inc),
            "allocated_kib": int(du.split()[0])}

def project(path):
    d = json.loads(path.read_text())
    bodies = {}
    for decl in d["translated"]["fun_decls"]:
        meta = decl["item_meta"]
        if meta["is_local"]:
            name = "::".join(part["Ident"][0] for part in meta["name"] if "Ident" in part)
            body = json.dumps(decl["body"], sort_keys=True, separators=(",", ":")).encode()
            bodies[name] = hashlib.sha256(body).hexdigest()
    return {"sha256": sha(path), "bytes": path.stat().st_size,
            "crate_name": d["translated"]["crate_name"], "has_errors": d["has_errors"],
            "local_body_sha256": bodies}

def environment(target, incremental):
    e = dict(os.environ)
    e.update(RUSTUP_HOME=str(TOOLS / "rustup"), CARGO_HOME=str(TOOLS / "cargo"),
             CHARON_TOOLCHAIN_IS_IN_PATH="1", CARGO_BUILD_JOBS="1",
             CARGO_INCREMENTAL=str(incremental), RAYON_NUM_THREADS="1",
             CARGO_NET_OFFLINE="true", CARGO_TARGET_DIR=str(target), BUILD_VALUE="7",
             PATH=os.pathsep.join((str(RUST), str(TOOLS / "bin"), e.get("PATH", ""))),
             DYLD_LIBRARY_PATH=os.pathsep.join((str(RUST.parent / "lib"),
                 str(RUST.parent / "lib/rustlib/aarch64-apple-darwin/lib"),
                 e.get("DYLD_LIBRARY_PATH", ""))))
    return e

def run(root, target, incremental, label):
    guarded()
    dest = HERE / "artifacts" / f"{label}.llbc"
    cmd = [str(CHARON), "cargo", "--preset", "aeneas", "--dest-file", str(dest), "--",
           "--manifest-path", str(root / "Cargo.toml"), "--package", "warm_probe",
           "--lib", "--offline", "--locked"]
    started = time.monotonic()
    proc = subprocess.Popen(cmd, cwd=root, env=environment(target, incremental),
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            text=True, start_new_session=True)
    samples = []
    reason = None
    while proc.poll() is None:
        h = headroom()
        samples.append({"elapsed_seconds": round(time.monotonic() - started, 4), **h})
        if h["free_disk_bytes"] < MIN_DISK or h["free_memory_percent"] < MIN_MEMORY:
            reason = "headroom"
            break
        if time.monotonic() - started > TIMEOUT:
            reason = "timeout"
            break
        time.sleep(0.1)
    if reason:
        os.killpg(proc.pid, signal.SIGTERM)
    try:
        stdout, stderr = proc.communicate(timeout=3)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        stdout, stderr = proc.communicate(timeout=3)
    result = {"label": label, "root": str(root), "target": str(target),
              "source_sha256": sha(root / "app/src/lib.rs"), "command": cmd,
              "environment": {k: environment(target, incremental)[k] for k in
                              ("CARGO_INCREMENTAL", "CARGO_TARGET_DIR", "CARGO_BUILD_JOBS",
                               "RAYON_NUM_THREADS", "CARGO_NET_OFFLINE", "BUILD_VALUE")},
              "exit": proc.returncode, "reason": reason, "stdout": stdout, "stderr": stderr,
              "elapsed_seconds": round(time.monotonic() - started, 4),
              "headroom_samples": samples, "target_stats": target_stats(target),
              "output": project(dest) if proc.returncode == 0 and dest.exists() else None}
    if result["exit"] != 0 or reason or result["output"] is None:
        raise RuntimeError(f"{label}: exit={result['exit']} guard={reason}")
    return result

def set_source(path, state):
    data = path.read_bytes()
    if state == "edited":
        assert data.count(OLD) == 1 and NEW not in data
        path.write_bytes(data.replace(OLD, NEW))
    else:
        assert data.count(NEW) == 1 and OLD not in data
        path.write_bytes(data.replace(NEW, OLD))
    return sha(path)

def main():
    assert not WORK.exists(), WORK
    assert FIXTURE.is_dir() and CHARON.is_file() and (RUST / "cargo").is_file()
    WORK.mkdir(parents=True)
    (HERE / "artifacts").mkdir(exist_ok=True)
    data = {"preflight": {**guarded(), "charon_sha256": sha(CHARON),
                          "cargo_sha256": sha(RUST / "cargo"),
                          "rustc_sha256": sha(RUST / "rustc"),
                          "fixture_files": {str(p.relative_to(FIXTURE)): sha(p)
                                            for p in FIXTURE.rglob("*") if p.is_file()},
                          "min_free_disk_bytes": MIN_DISK,
                          "min_free_memory_percent": MIN_MEMORY,
                          "command_timeout_seconds": TIMEOUT},
            "cells": [], "cleanup": None}
    try:
        for inc in (0, 1):
            cell = WORK / f"inc{inc}"
            roots = {name: cell / name for name in ("A", "B")}
            for root in roots.values():
                shutil.copytree(FIXTURE, root)
            assert len(str(roots["A"])) == len(str(roots["B"]))
            a_source = roots["A"] / "app/src/lib.rs"
            baseline_sha = sha(a_source)
            target = cell / "shared-target"
            oracle_target = cell / "oracle-target"
            record = {"incremental": inc, "roots": {k: str(v) for k, v in roots.items()},
                      "shared_target": str(target), "baseline_sha256": baseline_sha,
                      "oracle": {}, "phases": []}
            # Independent cold oracles use the same root but never the shared target.
            record["oracle"]["baseline"] = run(roots["A"], oracle_target, inc,
                                                  f"inc{inc}-oracle-baseline")
            shutil.rmtree(oracle_target)
            record["edited_sha256"] = set_source(a_source, "edited")
            record["oracle"]["edited"] = run(roots["A"], oracle_target, inc,
                                                f"inc{inc}-oracle-edited")
            shutil.rmtree(oracle_target)
            assert set_source(a_source, "baseline") == baseline_sha
            for phase in ("baseline", "edited", "reverted"):
                if phase == "edited":
                    assert set_source(a_source, "edited") == record["edited_sha256"]
                elif phase == "reverted":
                    assert set_source(a_source, "baseline") == baseline_sha
                record["phases"].append({"name": phase,
                    "source_hashes": {n: sha(r / "app/src/lib.rs") for n, r in roots.items()},
                    "runs": {n: run(r, target, inc, f"inc{inc}-{phase}-{n}")
                             for n, r in roots.items()}})
            data["cells"].append(record)
            (HERE / "results.json").write_text(json.dumps(data, indent=2) + "\n")
            shutil.rmtree(cell)
        data["cleanup"] = {"work_exists_after_removal": False,
                           "headroom_after": guarded()}
    finally:
        if WORK.exists():
            shutil.rmtree(WORK)
        data["cleanup"] = {"work_exists_after_removal": WORK.exists(),
                           "headroom_after": headroom()}
        (HERE / "results.json").write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps({"cells": len(data["cells"]), "runs": sum(2+sum(len(p["runs"]) for p in c["phases"]) for c in data["cells"]),
                      "cleanup": data["cleanup"]}, indent=2))

if __name__ == "__main__":
    main()
