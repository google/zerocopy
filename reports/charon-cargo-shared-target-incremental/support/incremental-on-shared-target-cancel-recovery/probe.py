#!/usr/bin/env python3
"""Guarded incremental-on shared Cargo-target cancellation and retry."""
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
WORK = Path(os.environ.get("I080_CANCEL_WORK_ROOT", HERE / "work")).resolve()
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
RUST = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"
CHARON = TOOLS / "bin/charon"
MIN_DISK = 10 * 1024**3
MIN_MEMORY = 30
MAX_GROUP_RSS_KIB = 1024 * 1024
MAX_WORK_KIB = 100 * 1024
SERIAL_TIMEOUT = 15
PAIR_TIMEOUT = 20
OLD = b"x.wrapping_add(1)"
NEW = b"x.wrapping_add(2)"
BUILD_INSERT = ('fn main() {\n  std::fs::write('
                'std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(".build-entered"), '
                'b"entered").unwrap();\n  '
                'std::thread::sleep(std::time::Duration::from_secs(3));')

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def memory_free():
    out = subprocess.check_output(["/usr/bin/memory_pressure", "-Q"], text=True)
    m = re.search(r"System-wide memory free percentage: (\d+)%", out)
    if not m:
        raise RuntimeError(out)
    return int(m.group(1))

def disk_free():
    return shutil.disk_usage(WORK.parent).free

def work_kib():
    if not WORK.exists():
        return 0
    return int(subprocess.check_output(["/usr/bin/du", "-sk", str(WORK)], text=True).split()[0])

def target_stats(target):
    if not target.exists():
        return {"files": 0, "file_bytes": 0, "incremental_files": 0,
                "incremental_bytes": 0, "allocated_kib": 0}
    files = [p for p in target.rglob("*") if p.is_file()]
    inc = [p for p in files if "incremental" in p.parts]
    return {"files": len(files), "file_bytes": sum(p.stat().st_size for p in files),
            "incremental_files": len(inc),
            "incremental_bytes": sum(p.stat().st_size for p in inc),
            "allocated_kib": int(subprocess.check_output(
                ["/usr/bin/du", "-sk", str(target)], text=True).split()[0])}

def ps_rows():
    out = subprocess.check_output(["/bin/ps", "-axo", "pid=,ppid=,pgid=,rss=,state="], text=True)
    rows = []
    for line in out.splitlines():
        f = line.split()
        if len(f) == 5:
            rows.append((int(f[0]), int(f[1]), int(f[2]), int(f[3]), f[4]))
    return rows

def group(pid, rows):
    return [{"pid": p, "rss_kib": rss} for p, _, pgid, rss, state in rows
            if pgid == pid and not state.startswith("Z")]

def sample(procs, started):
    rows = ps_rows()
    groups = {name: group(p.pid, rows) for name, p in procs.items()}
    return {"elapsed_seconds": round(time.monotonic() - started, 4),
            "free_disk_bytes": disk_free(), "free_memory_percent": memory_free(),
            "work_allocated_kib": work_kib(), "groups": groups,
            "group_rss_sum_kib": {n: sum(m["rss_kib"] for m in members)
                                  for n, members in groups.items()},
            "exits": {name: p.poll() for name, p in procs.items()}}

def guard(s):
    if s["free_disk_bytes"] < MIN_DISK:
        return "free_disk"
    if s["free_memory_percent"] < MIN_MEMORY:
        return "free_memory"
    if s["work_allocated_kib"] > MAX_WORK_KIB:
        return "private_work"
    if any(v > MAX_GROUP_RSS_KIB for v in s["group_rss_sum_kib"].values()):
        return "group_rss"
    return None

def environment(target):
    e = dict(os.environ)
    e.update(RUSTUP_HOME=str(TOOLS / "rustup"), CARGO_HOME=str(TOOLS / "cargo"),
             CHARON_TOOLCHAIN_IS_IN_PATH="1", CARGO_BUILD_JOBS="1",
             CARGO_INCREMENTAL="1", RAYON_NUM_THREADS="1",
             CARGO_NET_OFFLINE="true", CARGO_TARGET_DIR=str(target), BUILD_VALUE="7",
             PATH=os.pathsep.join((str(RUST), str(TOOLS / "bin"), e.get("PATH", ""))),
             DYLD_LIBRARY_PATH=os.pathsep.join((str(RUST.parent / "lib"),
                 str(RUST.parent / "lib/rustlib/aarch64-apple-darwin/lib"),
                 e.get("DYLD_LIBRARY_PATH", ""))))
    return e

def command(root, label):
    dest = HERE / "artifacts" / f"{label}.llbc"
    return [str(CHARON), "cargo", "--preset", "aeneas", "--dest-file", str(dest), "--",
            "--manifest-path", str(root / "Cargo.toml"), "--package", "warm_probe",
            "--lib", "--offline", "--locked"]

def start(root, target, label):
    cmd = command(root, label)
    p = subprocess.Popen(cmd, cwd=root, env=environment(target),
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         text=True, start_new_session=True)
    return p, cmd

def terminate(p):
    if p.poll() is None:
        os.killpg(p.pid, signal.SIGTERM)
        try:
            p.wait(timeout=2)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL)
            p.wait(timeout=2)

def project(dest):
    d = json.loads(dest.read_text())
    bodies = {}
    for decl in d["translated"]["fun_decls"]:
        meta = decl["item_meta"]
        if meta["is_local"]:
            name = "::".join(part["Ident"][0] for part in meta["name"] if "Ident" in part)
            body = json.dumps(decl["body"], sort_keys=True, separators=(",", ":")).encode()
            bodies[name] = hashlib.sha256(body).hexdigest()
    return {"sha256": sha(dest), "bytes": dest.stat().st_size,
            "crate_name": d["translated"]["crate_name"], "has_errors": d["has_errors"],
            "local_body_sha256": bodies}

def record(p, cmd, root, target, label):
    stdout, stderr = p.communicate(timeout=3)
    dest = HERE / "artifacts" / f"{label}.llbc"
    return {"label": label, "pid": p.pid, "exit": p.returncode,
            "root": str(root), "target": str(target), "command": cmd,
            "source_sha256": sha(root / "app/src/lib.rs"),
            "build_script_sha256": sha(root / "app/build.rs"),
            "stdout": stdout, "stderr": stderr,
            "output": project(dest) if dest.exists() else None}

def run_serial(root, target, label):
    p, cmd = start(root, target, label)
    started = time.monotonic()
    samples = []
    reason = None
    try:
        while True:
            s = sample({label: p}, started)
            samples.append(s)
            reason = guard(s)
            if reason or s["elapsed_seconds"] > SERIAL_TIMEOUT:
                reason = reason or "timeout"
                break
            if p.poll() is not None:
                break
            time.sleep(0.05)
    finally:
        if reason or p.poll() is None:
            terminate(p)
    r = record(p, cmd, root, target, label)
    result = {"reason": reason, "samples": samples, "run": r,
              "target_after": target_stats(target)}
    if reason or r["exit"] != 0 or r["output"] is None:
        raise RuntimeError(f"serial {label}: {reason} {r['exit']}")
    return result

def run_cancel_pair(a, b, target, marker):
    started = time.monotonic()
    pa, ca = start(a, target, "cancel-A")
    procs = {"A": pa}
    commands = {"A": ca}
    samples = []
    events = {}
    reason = None
    try:
        while not marker.exists():
            s = sample(procs, started)
            samples.append(s)
            reason = guard(s)
            if reason or s["elapsed_seconds"] > PAIR_TIMEOUT or pa.poll() is not None:
                reason = reason or ("owner_exited_before_marker" if pa.poll() is not None else "timeout")
                raise RuntimeError(reason)
            time.sleep(0.05)
        events["marker_seen_seconds"] = round(time.monotonic() - started, 4)
        pb, cb = start(b, target, "companion-B")
        procs["B"] = pb
        commands["B"] = cb
        events["companion_started_seconds"] = round(time.monotonic() - started, 4)
        # Keep the owner in its build-script sleep while the peer reaches Cargo's lock.
        time.sleep(0.15)
        s = sample(procs, started)
        samples.append(s)
        reason = guard(s)
        if reason or pa.poll() is not None or pb.poll() is not None:
            reason = reason or "pair_not_live_at_cancel"
            raise RuntimeError(reason)
        events["both_live_before_cancel"] = bool(s["groups"]["A"] and s["groups"]["B"])
        events["signal_seconds"] = round(time.monotonic() - started, 4)
        terminate(pa)
        events["owner_exit_seconds"] = round(time.monotonic() - started, 4)
        events["companion_live_after_owner_exit"] = pb.poll() is None
        while True:
            s = sample(procs, started)
            samples.append(s)
            reason = guard(s)
            if reason or s["elapsed_seconds"] > PAIR_TIMEOUT:
                reason = reason or "timeout"
                raise RuntimeError(reason)
            if pb.poll() is not None:
                break
            time.sleep(0.05)
        events["companion_exit_seconds"] = round(time.monotonic() - started, 4)
    finally:
        for p in procs.values():
            if reason or p.poll() is None:
                terminate(p)
    runs = {name: record(p, commands[name], a if name == "A" else b, target,
                         "cancel-A" if name == "A" else "companion-B")
            for name, p in procs.items()}
    result = {"reason": reason, "events": events, "samples": samples,
              "runs": runs, "target_after": target_stats(target)}
    if (reason or set(runs) != {"A", "B"} or runs["A"]["exit"] != -15 or
            runs["A"]["output"] is not None or runs["B"]["exit"] != 0 or
            runs["B"]["output"] is None):
        raise RuntimeError(f"cancel pair failed: {reason} { {k: v['exit'] for k, v in runs.items()} }")
    return result

def main():
    assert not WORK.exists(), WORK
    assert FIXTURE.is_dir() and CHARON.is_file() and (RUST / "cargo").is_file()
    pre = {"free_disk_bytes": disk_free(), "free_memory_percent": memory_free(),
           "charon_sha256": sha(CHARON), "cargo_sha256": sha(RUST / "cargo"),
           "rustc_sha256": sha(RUST / "rustc"),
           "fixture_files": {str(p.relative_to(FIXTURE)): sha(p)
                             for p in FIXTURE.rglob("*") if p.is_file()},
           "min_free_disk_bytes": MIN_DISK, "min_free_memory_percent": MIN_MEMORY,
           "max_group_rss_kib": MAX_GROUP_RSS_KIB, "max_private_work_kib": MAX_WORK_KIB,
           "serial_timeout_seconds": SERIAL_TIMEOUT, "pair_timeout_seconds": PAIR_TIMEOUT}
    assert pre["free_disk_bytes"] >= MIN_DISK and pre["free_memory_percent"] >= MIN_MEMORY
    WORK.mkdir(parents=True)
    a, b = WORK / "A", WORK / "B"
    shutil.copytree(FIXTURE, a)
    shutil.copytree(FIXTURE, b)
    assert len(str(a)) == len(str(b))
    target = WORK / "shared-target"
    data = {"preflight": pre, "roots": {"A": str(a), "B": str(b)},
            "shared_target": str(target), "phases": {}, "cleanup": None}
    try:
        data["phases"]["prewarm_A"] = run_serial(a, target, "prewarm-A")
        data["phases"]["prewarm_B"] = run_serial(b, target, "prewarm-B")
        baseline = (a / "app/src/lib.rs").read_bytes()
        assert baseline.count(OLD) == 1 and NEW not in baseline
        (a / "app/src/lib.rs").write_bytes(baseline.replace(OLD, NEW))
        build = a / "app/build.rs"
        original_build = build.read_text()
        assert original_build.count("fn main() {") == 1
        build.write_text(original_build.replace("fn main() {", BUILD_INSERT))
        marker = a / "app/.build-entered"
        assert not marker.exists()
        data["edit"] = {"baseline_sha256": hashlib.sha256(baseline).hexdigest(),
                        "edited_sha256": sha(a / "app/src/lib.rs"),
                        "original_build_sha256": hashlib.sha256(original_build.encode()).hexdigest(),
                        "instrumented_build_sha256": sha(build),
                        "marker": str(marker)}
        data["phases"]["cancel_pair"] = run_cancel_pair(a, b, target, marker)
        data["phases"]["recovery_A"] = run_serial(a, target, "recovery-A")
        data["phases"]["oracle_edited_A"] = run_serial(a, WORK / "oracle-edited-target", "oracle-edited-A")
        data["phases"]["oracle_baseline_B"] = run_serial(b, WORK / "oracle-baseline-target", "oracle-baseline-B")
        data["final_shared_target"] = target_stats(target)
        rows = ps_rows()
        all_runs = [data["phases"][k]["run"] for k in
                    ("prewarm_A", "prewarm_B", "recovery_A", "oracle_edited_A", "oracle_baseline_B")]
        all_runs += list(data["phases"]["cancel_pair"]["runs"].values())
        data["postrun_groups"] = {r["label"]: group(r["pid"], rows) for r in all_runs}
    finally:
        if WORK.exists():
            shutil.rmtree(WORK)
        data["cleanup"] = {"work_exists_after_removal": WORK.exists(),
                           "free_disk_bytes": disk_free(),
                           "free_memory_percent": memory_free()}
        (HERE / "results.json").write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps({"exits": {k: (v["run"]["exit"] if "run" in v else
                                          {n: r["exit"] for n, r in v["runs"].items()})
                                for k, v in data["phases"].items()},
                      "cleanup": data["cleanup"]}, indent=2))

if __name__ == "__main__":
    main()
