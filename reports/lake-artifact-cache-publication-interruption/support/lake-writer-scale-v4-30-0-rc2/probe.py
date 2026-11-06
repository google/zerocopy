#!/usr/bin/env python3
"""Bounded Lake shared-writer, interruption, and definition-sentinel probe."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time

TOOLCHAIN = "leanprover/lean4:v4.30.0-rc2"


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def inventory(root):
    d = {}
    for p in sorted(root.rglob("*")):
        if p.is_file():
            st = p.stat()
            d[str(p.relative_to(root))] = {"sha256": sha(p), "bytes": st.st_size,
                                          "blocks_bytes": st.st_blocks * 512,
                                          "mtime_ns": st.st_mtime_ns}
    return d


def totals(root):
    files = inventory(root)
    return {"files": len(files), "logical_bytes": sum(v["bytes"] for v in files.values()),
            "blocks_bytes": sum(v["blocks_bytes"] for v in files.values())}


def make(base, name, expected=7, producer=False, pause_marker=None):
    prod = base / "producer"
    if producer:
        prod.mkdir(parents=True)
        (prod / "lakefile.lean").write_text(
            "import Lake\nopen Lake DSL\npackage probe_dep\n@[default_target]\nlean_lib Dep\n")
        source = "import Lean\n"
        if pause_marker:
            source += ("run_cmd do\n  let tag ← IO.getEnv \"PROBE_WRITER\"\n"
                       f'  let _ ← IO.FS.writeFile ("{pause_marker}" ++ tag.getD "none") "entered"\n'
                       "  let _ ← IO.sleep 1500\n")
        source += "def depValue : Nat := 7\n"
        (prod / "Dep.lean").write_text(source)
        (prod / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    c = base / name
    c.mkdir(parents=True)
    (c / "lakefile.lean").write_text(
        'import Lake\nopen Lake DSL\nrequire probe_dep from "../producer"\n'
        "package probe_consumer\n@[default_target]\nlean_lib Generated\n")
    (c / "Generated.lean").write_text(
        f"import Dep\ntheorem expectedValue : depValue = {expected} := by decide\n"
        "#eval depValue\n")
    (c / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    manifest = {"version": "1.2.0", "packagesDir": ".lake/packages",
                "packages": [{"type": "path", "scope": "", "name": "probe_dep",
                              "manifestFile": "lake-manifest.json", "inherited": False,
                              "dir": "../producer", "configFile": "lakefile.lean"}],
                "name": "probe_consumer", "lakeDir": ".lake", "fixedToolchain": False}
    (c / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return prod, c


def freeze(root):
    for p in sorted(root.rglob("*"), reverse=True):
        if p.is_file():
            p.chmod(0o444)
        elif p.is_dir():
            p.chmod(0o555)
    root.chmod(0o555)


def ps_sample(roots):
    try:
        raw = subprocess.run(["ps", "-axo", "pid=,ppid=,rss="], capture_output=True,
                             text=True, timeout=2).stdout
    except (OSError, subprocess.TimeoutExpired):
        return None
    rows = {}
    for line in raw.splitlines():
        try:
            pid, ppid, rss = map(int, line.split()[:3])
            rows[pid] = (ppid, rss)
        except (ValueError, IndexError):
            continue
    descendants = set(roots)
    changed = True
    while changed:
        old = len(descendants)
        descendants.update(pid for pid, (ppid, _) in rows.items() if ppid in descendants)
        changed = len(descendants) != old
    return {"rss_kib_sum": sum(rows[p][1] for p in descendants if p in rows),
            "processes": sum(p in rows for p in descendants)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lake", type=Path, required=True)
    ap.add_argument("--lean", type=Path, required=True)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    a.work = a.work.resolve()
    a.out = a.out.resolve()
    a.work.mkdir(parents=True, exist_ok=False)
    a.out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN, LEAN_NUM_THREADS="1",
               LAKE_CACHE_DIR="", LAKE_ARTIFACT_CACHE="false",
               MATHLIB_NO_CACHE_ON_UPDATE="1")
    env["PATH"] = str(a.lake.parent) + os.pathsep + env.get("PATH", "")
    results = {"toolchain": TOOLCHAIN, "lake_sha256": sha(a.lake),
               "lean_sha256": sha(a.lean), "runs": [], "observations": {}}

    def run(label, cwd, args, extra_env=None):
        e = dict(env)
        if extra_env:
            e.update(extra_env)
        argv = [str(a.lake), "--keep-toolchain", "--no-cache", *args]
        t = time.monotonic()
        p = subprocess.run(argv, cwd=cwd, env=e, capture_output=True,
                           text=True, timeout=25)
        r = {"label": label, "cwd": str(cwd.relative_to(a.work)),
             "args": argv[1:], "exit": p.returncode,
             "seconds": round(time.monotonic() - t, 3),
             "stdout": p.stdout, "stderr": p.stderr}
        results["runs"].append(r)
        return r

    def parallel(label, consumers, extra_tags=None, kill_index=None, markers=None):
        procs = []
        start = time.monotonic()
        for i, c in enumerate(consumers):
            e = dict(env)
            if extra_tags:
                e["PROBE_WRITER"] = extra_tags[i]
            p = subprocess.Popen([str(a.lake), "--keep-toolchain", "--no-cache",
                                  "build", "Generated"], cwd=c, env=e,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 text=True, start_new_session=True)
            procs.append(p)
        peak = {"rss_kib_sum": 0, "processes": 0}
        marker_seen = []
        killed = False
        while any(p.poll() is None for p in procs):
            sample = ps_sample([p.pid for p in procs])
            if sample:
                for key in peak:
                    peak[key] = max(peak[key], sample[key])
            if markers:
                marker_seen = [m.exists() for m in markers]
                if all(marker_seen) and not killed and kill_index is not None:
                    os.killpg(procs[kill_index].pid, signal.SIGKILL)
                    killed = True
            if time.monotonic() - start > 20:
                for p in procs:
                    if p.poll() is None:
                        os.killpg(p.pid, signal.SIGKILL)
                break
            time.sleep(0.02)
        records = []
        for i, (c, p) in enumerate(zip(consumers, procs)):
            out, err = p.communicate(timeout=3)
            r = {"label": f"{label}-{i}", "cwd": str(c.relative_to(a.work)),
                 "args": ["--keep-toolchain", "--no-cache", "build", "Generated"],
                 "exit": p.returncode, "stdout": out, "stderr": err}
            records.append(r)
            results["runs"].append(r)
        return {"wall_seconds": round(time.monotonic() - start, 3),
                "peak_sampled": peak, "exits": [p.returncode for p in procs],
                "marker_seen": marker_seen, "killed": killed,
                "consumer_totals": [totals(c) for c in consumers]}

    # Same source, same shared writable producer: compare 1, 2, 4 writers.
    for n in (1, 2, 4):
        base = a.work / f"shared-{n}"
        producer, first = make(base, "consumer-0", producer=True)
        cs = [first] + [make(base, f"consumer-{i}")[1] for i in range(1, n)]
        outcome = parallel(f"shared-{n}", cs)
        outcome["producer_totals"] = totals(producer)
        outcome["producer_inventory"] = inventory(producer)
        results["observations"][f"shared-{n}"] = outcome

    # Frozen prebuilt comparison with a fresh consumer set.
    for n in (1, 2, 4):
        base = a.work / f"frozen-{n}"
        producer, primer = make(base, "primer", producer=True)
        run(f"frozen-{n}-prime", primer, ["build", "Generated"])
        shutil.rmtree(primer)
        cs = [make(base, f"consumer-{i}")[1] for i in range(n)]
        freeze(producer)
        before = inventory(producer)
        outcome = parallel(f"frozen-{n}", cs)
        outcome["producer_unchanged"] = before == inventory(producer)
        outcome["producer_totals"] = totals(producer)
        results["observations"][f"frozen-{n}"] = outcome

    # Controlled in-source pause. Kill writer A only after both writers wrote
    # their own marker from inside Dep.lean, before the sleep elapses.
    base = a.work / "interrupted"
    marker_prefix = str(a.work / "interrupted-marker-")
    producer, a_consumer = make(base, "consumer-a", producer=True,
                                pause_marker=marker_prefix)
    b_consumer = make(base, "consumer-b")[1]
    markers = [Path(marker_prefix + tag) for tag in ("A", "B")]
    outcome = parallel("interrupted", [a_consumer, b_consumer],
                       extra_tags=["A", "B"], kill_index=0, markers=markers)
    outcome["producer_inventory"] = inventory(producer)
    results["observations"]["interrupted"] = outcome
    run("interrupted-retry", b_consumer, ["build", "Generated"])
    run("interrupted-no-build-check", b_consumer,
        ["--no-build", "build", "Dep"])

    # Explicit semantic sentinel: keep source mtime unchanged while changing
    # its definition. Compare hash freshness with --old mtime fallback.
    base = a.work / "sentinel"
    producer, c7 = make(base, "consumer-seven", expected=7, producer=True)
    run("sentinel-seven-build", c7, ["build", "Generated"])
    source = producer / "Dep.lean"
    old_stat = source.stat()
    old_hash = sha(source)
    old_olean = sha(producer / ".lake/build/lib/lean/Dep.olean")
    _, c9 = make(base, "consumer-nine", expected=9)
    source.write_text("import Lean\ndef depValue : Nat := 9\n")
    os.utime(source, ns=(old_stat.st_atime_ns, old_stat.st_mtime_ns))
    results["observations"]["sentinel_before"] = {
        "old_source_sha256": old_hash, "new_source_sha256": sha(source),
        "source_mtime_same": source.stat().st_mtime_ns == old_stat.st_mtime_ns,
        "old_olean_sha256": old_olean}
    run("sentinel-hash-no-build", c9, ["--no-build", "build", "Dep"])
    run("sentinel-old-no-build", c9, ["--old", "--no-build", "build", "Dep"])
    run("sentinel-nine-before-rebuild", c9, ["env", "lean", "--json", "Generated.lean"])
    run("sentinel-nine-rebuild", c9, ["build", "Generated"])
    run("sentinel-seven-after-rebuild", c7, ["build", "Generated"])
    results["observations"]["sentinel_after"] = {
        "new_olean_sha256": sha(producer / ".lake/build/lib/lean/Dep.olean"),
        "producer_totals": totals(producer)}
    (a.out / "results.json").write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
