#!/usr/bin/env python3
"""Which file of a Lean 4 toolchain actually carries the kernel?

Usage:
    python3 lean_toolchain_identity_probe.py --prefix <lean toolchain prefix> \
        [--lock <foundation-lock.json>] [--runs 5]

`--prefix` is the directory printed by `lean --print-prefix` (for an elan
install: ~/.elan/toolchains/leanprover--lean4---v4.34.1).
`--lock` is optionally a JSON file with a top-level "distributions" object
mapping a `lean --version` string to a SHA-256 (the shape used by
`trusted/lean/foundation-lock.json` in joshlf/anneal); the probe reports which
toolchain files, if any, have a digest listed there.

Linux/ELF only (uses `ldd`, `readelf`, `nm`). Everything reported is measured
on the given prefix; no value is hardcoded.
"""

import argparse
import hashlib
import json
import os
import statistics
import subprocess
import sys
import time

KERNEL_SYMBOLS = ("lean_kernel_check", "lean_kernel_is_def_eq", "lean_add_decl")


def sha256(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def run(cmd):
    return subprocess.run(cmd, capture_output=True, text=True).stdout


def timed(cmd, runs):
    xs = []
    for _ in range(runs):
        t = time.perf_counter()
        subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)
        xs.append(time.perf_counter() - t)
    return {
        "runs": runs,
        "min_s": round(min(xs), 4),
        "median_s": round(statistics.median(xs), 4),
        "max_s": round(max(xs), 4),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--prefix", required=True)
    ap.add_argument("--lock")
    ap.add_argument("--runs", type=int, default=5)
    args = ap.parse_args()
    prefix = os.path.realpath(args.prefix)
    lean = os.path.join(prefix, "bin", "lean")

    version = run([lean, "--version"]).strip()
    dynamic = run(["readelf", "-d", lean])
    needed = [l.split("[")[1].rstrip("]") for l in dynamic.splitlines() if "(NEEDED)" in l]
    runpath = [l.split("[")[1].rstrip("]") for l in dynamic.splitlines() if "RUNPATH" in l or "RPATH" in l]

    resolved = {}
    for line in run(["ldd", lean]).splitlines():
        parts = line.split()
        if len(parts) >= 3 and parts[1] == "=>":
            resolved[parts[0]] = os.path.realpath(parts[2])

    files = {}
    for name, path in sorted(resolved.items()):
        inside = path.startswith(prefix + os.sep)
        entry = {"inside_prefix": inside, "bytes": os.path.getsize(path)}
        if inside:
            entry["path"] = os.path.relpath(path, prefix)
            entry["sha256"] = sha256(path)
            syms = run(["nm", "-D", "--defined-only", path])
            defined = {l.split()[-1] for l in syms.splitlines() if l.strip()}
            entry["defines_kernel_entry_points"] = sorted(s for s in KERNEL_SYMBOLS if s in defined)
        else:
            entry["path"] = path
        files[name] = entry

    launcher = {"path": "bin/lean", "bytes": os.path.getsize(lean), "sha256": sha256(lean)}
    syms = run(["nm", "-D", "--defined-only", lean])
    launcher["defines_kernel_entry_points"] = sorted(
        s for s in KERNEL_SYMBOLS if s in {l.split()[-1] for l in syms.splitlines() if l.strip()}
    )

    out = {
        "lean_version": version,
        "host": " ".join(os.uname()[i] for i in (0, 4)),
        "launcher": launcher,
        "launcher_needed": needed,
        "launcher_runpath": runpath,
        "resolved_libraries": files,
        "timing": {
            "lean_version_startup": timed([lean, "--version"], args.runs),
            "sha256sum_launcher": timed(["sha256sum", lean], args.runs),
        },
    }
    kernel_libs = [n for n, e in files.items() if e.get("defines_kernel_entry_points")]
    out["libraries_defining_kernel_entry_points"] = kernel_libs
    for n in kernel_libs:
        p = os.path.join(prefix, files[n]["path"])
        out["timing"]["sha256sum_" + n] = timed(["sha256sum", p], args.runs)

    if args.lock:
        lock = json.load(open(args.lock))
        dist = lock.get("distributions", {})
        locked = {v.lower() for v in dist.values()}
        out["lock"] = {
            "distribution_entries": len(dist),
            "version_string_listed": version in dist,
            "launcher_digest_listed": launcher["sha256"] in locked,
            "launcher_digest_matches_entry_for_this_version": dist.get(version, "").lower()
            == launcher["sha256"],
            "library_digests_listed": {
                n: (e["sha256"] in locked) for n, e in files.items() if "sha256" in e
            },
            "lock_text_mentions_any_library_digest": any(
                e["sha256"] in json.dumps(lock) for e in files.values() if "sha256" in e
            ),
        }
    json.dump(out, sys.stdout, indent=2, sort_keys=True)
    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
