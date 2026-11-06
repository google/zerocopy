#!/usr/bin/env python3
"""Sequential, offline two-process Cargo target-layout matrix for a tiny Charon fixture."""
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
WORK = HERE / "work"
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
RUST = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"
CHARON = TOOLS / "bin/charon"
MIN_FREE_DISK = 10 * 1024**3
MIN_FREE_MEMORY_PERCENT = 30
CELL_TIMEOUT = 35

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def memory_free_percent():
    out = subprocess.check_output(["/usr/bin/memory_pressure", "-Q"], text=True)
    match = re.search(r"System-wide memory free percentage: (\d+)%", out)
    if not match:
        raise RuntimeError(out)
    return int(match.group(1))

def headroom():
    return {"free_disk_bytes": shutil.disk_usage(HERE).free,
            "free_memory_percent": memory_free_percent()}

def require_headroom():
    h = headroom()
    if h["free_disk_bytes"] < MIN_FREE_DISK or h["free_memory_percent"] < MIN_FREE_MEMORY_PERCENT:
        raise RuntimeError("headroom guard: " + repr(h))
    return h

def env(target, incremental):
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

def tree_stats(path):
    if not path.exists():
        return {"files": 0, "file_bytes": 0, "allocated_kib": 0,
                "incremental_files": 0, "incremental_bytes": 0}
    files = [p for p in path.rglob("*") if p.is_file()]
    inc = [p for p in files if "incremental" in p.parts]
    du = subprocess.check_output(["/usr/bin/du", "-sk", str(path)], text=True)
    return {"files": len(files), "file_bytes": sum(p.stat().st_size for p in files),
            "allocated_kib": int(du.split()[0]), "incremental_files": len(inc),
            "incremental_bytes": sum(p.stat().st_size for p in inc)}

def allocated_kib(path):
    if not path.exists():
        return 0
    return int(subprocess.check_output(["/usr/bin/du", "-sk", str(path)], text=True).split()[0])

def ps_rows():
    out = subprocess.check_output(["/bin/ps", "-axo", "pid=,ppid=,pgid=,rss=,state="], text=True)
    rows = []
    for line in out.splitlines():
        x = line.split()
        if len(x) == 5:
            rows.append((int(x[0]), int(x[1]), int(x[2]), int(x[3]), x[4]))
    return rows

def group_members(pid, rows):
    return [{"pid": p, "rss_kib": rss} for p, _, pgid, rss, state in rows
            if pgid == pid and not state.startswith("Z")]

def stop(proc):
    if proc.poll() is None:
        os.killpg(proc.pid, signal.SIGTERM)
        try:
            proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait(timeout=2)

def output_projection(dest):
    if not dest.exists():
        return None
    d = json.loads(dest.read_text())
    t = d["translated"]
    bodies = {}
    for decl in t["fun_decls"]:
        if decl["item_meta"]["is_local"]:
            name = "::".join(part["Ident"][0] for part in decl["item_meta"]["name"] if "Ident" in part)
            body = decl["body"]
            bodies[name] = hashlib.sha256(json.dumps(body, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"sha256": sha(dest), "bytes": dest.stat().st_size,
            "crate_name": t["crate_name"], "has_errors": d["has_errors"],
            "local_body_sha256": bodies}

def run_phase(cell, layout, incremental, phase):
    roots = {n: WORK / cell / n for n in ("A", "B")}
    targets = {n: WORK / cell / ("shared-target" if layout == "shared" else n + "-target") for n in roots}
    outdir = HERE / "artifacts" / cell
    outdir.mkdir(parents=True, exist_ok=True)
    procs = {}
    commands = {}
    started = time.monotonic()
    for n in roots:
        dest = outdir / f"{phase}-{n}.llbc"
        argv = [str(CHARON), "cargo", "--preset", "aeneas", "--dest-file", str(dest), "--",
                "--manifest-path", str(roots[n] / "Cargo.toml"), "--package", "warm_probe",
                "--lib", "--offline", "--locked"]
        commands[n] = argv
        procs[n] = subprocess.Popen(argv, cwd=roots[n], env=env(targets[n], incremental),
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                    text=True, start_new_session=True)
    samples = []
    reason = None
    try:
        while True:
            h = headroom()
            rows = ps_rows()
            members = {n: group_members(p.pid, rows) for n, p in procs.items()}
            s = {"elapsed_seconds": round(time.monotonic() - started, 4), "headroom": h,
                 "groups": members, "exits": {n: p.poll() for n, p in procs.items()},
                 "target_allocated_kib": {n: allocated_kib(targets[n]) for n in targets}}
            samples.append(s)
            if h["free_disk_bytes"] < MIN_FREE_DISK or h["free_memory_percent"] < MIN_FREE_MEMORY_PERCENT:
                reason = "headroom"; break
            if s["elapsed_seconds"] > CELL_TIMEOUT:
                reason = "timeout"; break
            if all(p.poll() is not None for p in procs.values()):
                break
            time.sleep(0.1)
    finally:
        if reason or any(p.poll() is None for p in procs.values()):
            for p in procs.values():
                stop(p)
    results = {}
    for n, p in procs.items():
        stdout, stderr = p.communicate(timeout=3)
        dest = outdir / f"{phase}-{n}.llbc"
        results[n] = {"pid": p.pid, "exit": p.returncode, "command": commands[n],
                      "target": str(targets[n]), "stdout": stdout, "stderr": stderr,
                      "output": output_projection(dest) if p.returncode == 0 else None}
    return {"phase": phase, "reason": reason, "samples": samples, "results": results,
            "targets": {n: tree_stats(targets[n]) for n in targets}}

def main():
    assert not WORK.exists(), WORK
    assert FIXTURE.is_dir() and CHARON.is_file() and (RUST / "cargo").is_file()
    pre = require_headroom()
    pre.update(charon_sha256=sha(CHARON), cargo_sha256=sha(RUST / "cargo"),
               rustc_sha256=sha(RUST / "rustc"),
               fixture_files={str(p.relative_to(FIXTURE)): sha(p) for p in FIXTURE.rglob("*") if p.is_file()},
               cell_timeout_seconds=CELL_TIMEOUT,
               minimum_free_disk_bytes=MIN_FREE_DISK,
               minimum_free_memory_percent=MIN_FREE_MEMORY_PERCENT)
    WORK.mkdir()
    data = {"preflight": pre, "cells": [], "cleanup": None}
    (HERE / "results.json").write_text(json.dumps(data, indent=2) + "\n")
    groups = {}
    try:
        for layout in ("private", "shared"):
            for incremental in (0, 1):
                require_headroom()
                # Keep the absolute source-root length equal across target layouts.
                cell = f"{layout.ljust(7, '_')}-inc{incremental}"
                cellwork = WORK / cell
                cellwork.mkdir()
                for n in ("A", "B"):
                    shutil.copytree(FIXTURE, cellwork / n)
                    build = cellwork / n / "app/build.rs"
                    build.write_text(build.read_text().replace("fn main() {",
                        "fn main() {\n  std::thread::sleep(std::time::Duration::from_secs(1));"))
                record = {"layout": layout, "incremental": incremental,
                          "source_root_paths": {n: str(cellwork / n) for n in ("A", "B")},
                          "phases": []}
                for phase in ("cold", "warm"):
                    run = run_phase(cell, layout, incremental, phase)
                    record["phases"].append(run)
                    groups.update({f"{cell}-{phase}-{n}": r["pid"] for n, r in run["results"].items()})
                    if run["reason"] or any(r["exit"] != 0 for r in run["results"].values()):
                        data["cells"].append(record)
                        (HERE / "results.json").write_text(json.dumps(data, indent=2) + "\n")
                        raise RuntimeError(f"failed phase: {cell} {phase} {run['reason']}")
                record["final_targets"] = {n: tree_stats(cellwork / ("shared-target" if layout == "shared" else n + "-target")) for n in ("A", "B")}
                data["cells"].append(record)
                (HERE / "results.json").write_text(json.dumps(data, indent=2) + "\n")
                shutil.rmtree(cellwork)
        rows = ps_rows()
        group_check = {key: {"pgid": pid, "members": group_members(pid, rows)} for key, pid in groups.items()}
        shutil.rmtree(WORK)
        data["cleanup"] = {"process_groups": group_check,
                           "work_exists_after_removal": WORK.exists(),
                           "headroom_after": headroom()}
        (HERE / "results.json").write_text(json.dumps(data, indent=2) + "\n")
        print(json.dumps({"cells": [(c["layout"], c["incremental"]) for c in data["cells"]],
                          "cleanup": data["cleanup"]["work_exists_after_removal"]}, indent=2))
    except Exception:
        # Leave a guarded failure's private tree for explicit inspection; no next cell is started.
        raise

if __name__ == "__main__":
    main()
