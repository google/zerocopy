#!/usr/bin/env python3
"""Guarded, serial Lean --run probe; records sampled process RSS, not allocations."""
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "fixture" / "Probe.lean"
RAW = ROOT / "raw"
MODES = ("array-retained", "array-discarded", "map-retained", "map-discarded")

def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def admission():
    vm = subprocess.check_output(["vm_stat"], text=True)
    page = int(re.search(r"page size of (\d+) bytes", vm).group(1))
    values = [int(x) for x in re.findall(r"Pages (?:free|inactive|speculative):\s+(\d+)", vm)]
    assert len(values) == 3
    total = int(subprocess.check_output(["sysctl", "-n", "hw.memsize"], text=True))
    percent = 100 * page * sum(values) / total
    disk = shutil.disk_usage(ROOT).free
    scratch = sum(f.stat().st_size for f in RAW.rglob("*") if f.is_file())
    sample = {"reclaimable_percent": percent, "disk_free_bytes": disk, "owned_raw_bytes": scratch}
    if percent <= 20 or disk <= 1_073_741_824 or scratch >= 100_000_000:
        raise RuntimeError(f"admission rejected: {sample}")
    return sample

def rss(pid):
    p = subprocess.run(["ps", "-o", "rss=", "-p", str(pid)], capture_output=True, text=True)
    try: return int(p.stdout.strip()) * 1024
    except ValueError: return 0

def run(version, lean, mode, n, repeat):
    sample = admission()
    command = [str(lean), "--run", str(FIXTURE), mode, str(n)]
    start = time.monotonic()
    proc = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    peak = 0; polls = 0; terminated = None
    while proc.poll() is None:
        peak = max(peak, rss(proc.pid)); polls += 1
        if peak > 1_073_741_824:
            terminated = "sampled RSS exceeded 1 GiB"; proc.kill(); break
        if time.monotonic() - start > 30:
            terminated = "30-second timeout"; proc.kill(); break
        time.sleep(0.025)
    out, err = proc.communicate()
    peak = max(peak, rss(proc.pid))
    stem = f"{version}--{mode}--n{n}--r{repeat}"
    (RAW / (stem + ".stdout")).write_bytes(out)
    (RAW / (stem + ".stderr")).write_bytes(err)
    return {"version": version, "mode": mode, "n": n, "repeat": repeat, "command": command,
            "admission": sample, "exit_code": proc.returncode, "terminated": terminated,
            "elapsed_s": time.monotonic() - start, "peak_sampled_rss_bytes": peak, "rss_polls": polls,
            "stdout_sha256": hashlib.sha256(out).hexdigest(), "stderr_sha256": hashlib.sha256(err).hexdigest(),
            "stdout_bytes": len(out), "stderr_bytes": len(err)}

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--old-lean", type=Path, required=True)
    p.add_argument("--new-lean", type=Path, required=True)
    p.add_argument("--n", type=int, default=8192)
    args = p.parse_args()
    RAW.mkdir(exist_ok=True)
    lean = {"old": args.old_lean.resolve(), "new": args.new_lean.resolve()}
    result_file = ROOT / "results.json"
    result = json.loads(result_file.read_text()) if result_file.exists() else {"fixture_sha256": sha(FIXTURE), "tools": {}, "cells": []}
    assert result["fixture_sha256"] == sha(FIXTURE)
    for version, path in lean.items():
        result["tools"][version] = {"lean_version": subprocess.check_output([str(path), "--version"], text=True).strip(),
                                     "lean_sha256": sha(path), "executable": str(path)}
    for version, path in lean.items():
        for mode in MODES:
            for repeat in range(3):
                if any(c["version"] == version and c["mode"] == mode and c["n"] == args.n and c["repeat"] == repeat for c in result["cells"]):
                    continue
                cell = run(version, path, mode, args.n, repeat)
                result["cells"].append(cell)
                (ROOT / "results.json").write_text(json.dumps(result, indent=2) + "\n")
                print(version, mode, repeat, cell["exit_code"], cell["peak_sampled_rss_bytes"], flush=True)
                if cell["exit_code"] != 0 or cell["terminated"]:
                    raise RuntimeError(f"probe failed: {version}/{mode}/{repeat}: {cell['terminated']}")

if __name__ == "__main__": main()
