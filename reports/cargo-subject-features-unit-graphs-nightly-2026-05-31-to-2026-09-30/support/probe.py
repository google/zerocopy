#!/usr/bin/env python3
"""Offline, serial, resource-gated Cargo matrix for one reconstructed fixture."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "fixture"
RAW = ROOT / "raw"
SCRATCH = ROOT / "scratch"
EXPECTED_TOOLS = {
    "pinned": ("71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1",
               "2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc",
               "fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef", "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1"),
    "stable": ("778478868dbfe74960e49329bb5813d2f5ba95c8bfb1f37cd626c62cb26a214a",
               "2814fb55fb9cfb3eef5848a8104d77e3de7fd95394661144a12ee90cd4405340",
               "797e8a9bca276c1c9f9f738d2a20f484fa4eea9d", "48a229ceaefd4985c50990b14116b6d856af0985"),
    "newer": ("a59fccc480f931538408a17c2c2daae588da33d5196a38c526761db36a18ec66",
              "29f8ccc9aa7b0d8798eda854fa7f0e4ba3867c8c336b87d52dbb3b24b3f0878d",
              "3d7cf6e937d6127d0f49881bf689c560b36d35c4", "5c543b0b8c73c7b72bc8284ced4fb22ead15734d"),
}

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def size(path):
    if not path.exists():
        return 0
    return sum(f.stat().st_size for f in path.rglob("*") if f.is_file())

def admission():
    vm = subprocess.check_output(["vm_stat"], text=True)
    page = int(re.search(r"page size of (\d+) bytes", vm).group(1))
    values = {k: int(v) for k, v in re.findall(r"Pages (free|inactive|speculative):\s+(\d+)", vm)}
    memory = int(subprocess.check_output(["sysctl", "-n", "hw.memsize"], text=True))
    percent = 100 * page * sum(values.values()) / memory
    disk = shutil.disk_usage(ROOT).free
    scratch = size(SCRATCH)
    sample = {"reclaimable_percent": percent, "disk_free_bytes": disk, "scratch_bytes": scratch}
    if percent <= 20 or disk <= 1_073_741_824 or scratch >= 100_000_000:
        raise RuntimeError(f"resource admission rejected: {sample}")
    return sample

def run(label, version, args, cargo, rustc, target, timeout=30):
    sample = admission()
    env = os.environ.copy()
    env.update({"RUSTC": str(rustc), "CARGO_NET_OFFLINE": "true", "CARGO_HOME": str(SCRATCH / "cargo-home"),
                "CARGO_TARGET_DIR": str(target), "CARGO_BUILD_JOBS": "1", "CARGO_TERM_COLOR": "never"})
    command = [str(cargo), *args, "--manifest-path", str(FIXTURE / "Cargo.toml")]
    started = time.monotonic()
    try:
        p = subprocess.run(command, cwd=FIXTURE, env=env, capture_output=True, timeout=timeout)
        code, out, err, timed_out = p.returncode, p.stdout, p.stderr, False
    except subprocess.TimeoutExpired as e:
        code, out, err, timed_out = None, e.stdout or b"", e.stderr or b"", True
    elapsed = time.monotonic() - started
    stem = f"{version}--{label}"
    (RAW / (stem + ".stdout")).write_bytes(out)
    (RAW / (stem + ".stderr")).write_bytes(err)
    return {"version": version, "label": label, "command": command, "admission": sample,
            "exit_code": code, "timed_out": timed_out, "elapsed_s": elapsed,
            "stdout_sha256": hashlib.sha256(out).hexdigest(), "stderr_sha256": hashlib.sha256(err).hexdigest(),
            "stdout_bytes": len(out), "stderr_bytes": len(err)}

def main():
    p = argparse.ArgumentParser()
    for name in ("pinned", "stable", "newer"):
        p.add_argument("--" + name + "-cargo", type=Path, required=True)
        p.add_argument("--" + name + "-rustc", type=Path, required=True)
    a = p.parse_args()
    if RAW.exists(): shutil.rmtree(RAW)
    if SCRATCH.exists(): shutil.rmtree(SCRATCH)
    RAW.mkdir()
    SCRATCH.mkdir()
    (SCRATCH / "cargo-home").mkdir()
    tools = {}
    for name in ("pinned", "stable", "newer"):
        cargo, rustc = getattr(a, name + "_cargo").resolve(), getattr(a, name + "_rustc").resolve()
        tools[name] = {"cargo": str(cargo), "rustc": str(rustc), "cargo_sha256": sha(cargo), "rustc_sha256": sha(rustc),
                       "cargo_version": subprocess.check_output([str(cargo), "-Vv"], text=True),
                       "rustc_version": subprocess.check_output([str(rustc), "-Vv"], text=True)}
        expected = EXPECTED_TOOLS[name]
        if (tools[name]["cargo_sha256"], tools[name]["rustc_sha256"]) != expected[:2]:
            raise RuntimeError(f"{name}: supplied Cargo/rustc binary hashes are not the pinned identities")
        if expected[2] not in tools[name]["cargo_version"] or expected[3] not in tools[name]["rustc_version"]:
            raise RuntimeError(f"{name}: supplied Cargo/rustc version strings do not match the pinned commits")
    results = {"fixture_sha256": {str(x.relative_to(FIXTURE)): sha(x) for x in sorted(FIXTURE.rglob("*")) if x.is_file() and x.name != "Cargo.lock"},
               "tools": tools, "cells": []}
    host = next(x.split(": ", 1)[1] for x in tools["pinned"]["rustc_version"].splitlines() if x.startswith("host: "))
    jobs = [
        ("metadata-default", ["metadata", "--format-version", "1", "--offline"]),
        ("metadata-feature", ["metadata", "--format-version", "1", "--offline", "--features", "with-opt"]),
        ("metadata-filter-host", ["metadata", "--format-version", "1", "--offline", "--filter-platform", host]),
        ("metadata-filter-windows", ["metadata", "--format-version", "1", "--offline", "--filter-platform", "x86_64-pc-windows-gnu"]),
        ("unit-build", ["build", "--offline", "-p", "probe-app", "-Z", "unstable-options", "--unit-graph"]),
        ("unit-feature", ["build", "--offline", "-p", "probe-app", "--features", "with-opt", "-Z", "unstable-options", "--unit-graph"]),
        ("unit-release", ["build", "--offline", "-p", "probe-app", "--release", "-Z", "unstable-options", "--unit-graph"]),
        ("unit-test", ["test", "--offline", "-p", "probe-app", "--no-run", "-Z", "unstable-options", "--unit-graph"]),
        ("unit-target", ["build", "--offline", "-p", "probe-app", "--target", host, "-Z", "unstable-options", "--unit-graph"]),
        ("build-cold", ["build", "--offline", "-p", "probe-app", "-vv"]),
        ("build-warm", ["build", "--offline", "-p", "probe-app", "-vv"]),
        ("build-feature", ["build", "--offline", "-p", "probe-app", "--features", "with-opt", "-vv"]),
        ("test-no-run", ["test", "--offline", "-p", "probe-app", "--no-run", "-vv"]),
    ]
    for name in tools:
        target = SCRATCH / (name + "-target")
        for label, args in jobs:
            cell = run(label, name, args, Path(tools[name]["cargo"]), Path(tools[name]["rustc"]), target)
            results["cells"].append(cell)
            (ROOT / "results.json").write_text(json.dumps(results, indent=2) + "\n")
            print(name, label, cell["exit_code"], f"{cell['elapsed_s']:.3f}s", flush=True)
    results["final_scratch_bytes"] = size(SCRATCH)
    results["lock_sha256"] = sha(FIXTURE / "Cargo.lock")
    (ROOT / "results.json").write_text(json.dumps(results, indent=2) + "\n")

if __name__ == "__main__": main()
