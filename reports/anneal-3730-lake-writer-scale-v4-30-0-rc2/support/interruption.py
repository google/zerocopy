#!/usr/bin/env python3
"""Paired Lake writer interruption after both enter Dep compilation."""
import argparse
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time

from probe import TOOLCHAIN, inventory, make, ps_sample, sha, totals


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
    prefix = str(a.work / "marker-")
    producer, a_consumer = make(a.work / "pair", "consumer-a", producer=True,
                                pause_marker=prefix)
    b_consumer = make(a.work / "pair", "consumer-b")[1]
    results = {"lake_sha256": sha(a.lake), "lean_sha256": sha(a.lean),
               "runs": [], "observations": {}}

    def run(label, cwd, tag=None, args=("build", "Generated")):
        e = dict(env)
        if tag:
            e["PROBE_WRITER"] = tag
        argv = [str(a.lake), "--keep-toolchain", "--no-cache", *args]
        t = time.monotonic()
        p = subprocess.run(argv, cwd=cwd, env=e, text=True, capture_output=True,
                           timeout=12)
        r = {"label": label, "cwd": str(cwd.relative_to(a.work)),
             "args": argv[1:], "exit": p.returncode,
             "seconds": round(time.monotonic() - t, 3),
             "stdout": p.stdout, "stderr": p.stderr}
        results["runs"].append(r)
        return r

    # Compile both consumers once to stabilize configuration, then remove only
    # module build directories. Each concurrent writer must compile Dep again.
    run("prime-a", a_consumer, "P")
    run("prime-b", b_consumer, "P")
    for p in (producer / ".lake/build", a_consumer / ".lake/build",
              b_consumer / ".lake/build"):
        if p.exists():
            shutil.rmtree(p)
    results["observations"]["pre_parallel_producer"] = inventory(producer)

    procs = []
    start = time.monotonic()
    for tag, c in (("A", a_consumer), ("B", b_consumer)):
        e = dict(env, PROBE_WRITER=tag)
        p = subprocess.Popen([str(a.lake), "--keep-toolchain", "--no-cache",
                              "build", "Generated"], cwd=c, env=e,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             text=True, start_new_session=True)
        procs.append(p)
    peak = {"rss_kib_sum": 0, "processes": 0}
    markers = [Path(prefix + x) for x in ("A", "B")]
    killed = False
    while any(p.poll() is None for p in procs):
        sample = ps_sample([p.pid for p in procs])
        if sample:
            peak = {k: max(peak[k], sample[k]) for k in peak}
        if all(m.exists() for m in markers) and not killed:
            os.killpg(procs[0].pid, signal.SIGKILL)
            killed = True
        if time.monotonic() - start > 10:
            for p in procs:
                if p.poll() is None:
                    os.killpg(p.pid, signal.SIGKILL)
            break
        time.sleep(0.02)
    for tag, c, p in zip(("A", "B"), (a_consumer, b_consumer), procs):
        out, err = p.communicate(timeout=3)
        results["runs"].append({"label": "interrupted-" + tag,
                                "cwd": str(c.relative_to(a.work)),
                                "args": ["--keep-toolchain", "--no-cache", "build", "Generated"],
                                "exit": p.returncode, "stdout": out, "stderr": err})
    results["observations"]["paired"] = {
        "markers": [m.exists() for m in markers], "killed_A": killed,
        "exits": [p.returncode for p in procs],
        "wall_seconds": round(time.monotonic() - start, 3),
        "peak_sampled": peak, "producer_inventory": inventory(producer),
        "producer_totals": totals(producer)}
    run("survivor-retry", b_consumer, "B")
    run("survivor-no-build", b_consumer, "B", ("--no-build", "build", "Dep"))
    (a.out / "results.json").write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
