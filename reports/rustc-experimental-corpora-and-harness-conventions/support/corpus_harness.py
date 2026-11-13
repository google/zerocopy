#!/usr/bin/env python3
"""Shared experimental corpus and compiler-wrapper harness for rustc 1.99.1."""
import argparse
import json
import os
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent

TIER1_TARGETS = [
    "x86_64-unknown-linux-gnu",
    "x86_64-pc-windows-msvc",
    "x86_64-pc-windows-gnu",
    "aarch64-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "aarch64-pc-windows-msvc",
    "i686-unknown-linux-gnu",
    "i686-pc-windows-msvc",
]

NO_STD_PROBE_RS = """#![no_std]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn verified_crc32c_step(acc: u32, data: *const u8, len: usize) -> u32 {
    if data.is_null() {
        return acc;
    }
    let mut crc = !acc;
    let mut i = 0usize;
    while i < len {
        let byte = unsafe { *data.add(i) };
        crc ^= byte as u32;
        let mut bit = 0;
        while bit < 8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0x82F63B78u32 & mask);
            bit += 1;
        }
        i += 1;
    }
    !crc
}
"""

def summarize_samples(samples: list[float]) -> dict:
    s = sorted(samples)
    n = len(s)
    med = statistics.median(s)
    q25 = s[max(0, (n * 1) // 4 - 1)] if n >= 4 else s[0]
    q75 = s[min(n - 1, (n * 3) // 4)] if n >= 4 else s[-1]
    iqr = q75 - q25
    mad = statistics.median([abs(x - med) for x in s])
    return {
        "n": n,
        "min": round(s[0], 6),
        "median": round(med, 6),
        "mean": round(statistics.mean(s), 6),
        "iqr": round(iqr, 6),
        "normalized_iqr_pct": round((iqr / med) * 100.0, 3) if med > 0 else 0.0,
        "mad": round(mad, 6),
        "max": round(s[-1], 6),
    }

def run_tier1_smoke(rustc_cmd: list[str], extra_flags: list[str], reps: int) -> dict:
    results = {}
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        src = tmp_path / "lib.rs"
        src.write_text(NO_STD_PROBE_RS, encoding="utf-8")
        for t in TIER1_TARGETS:
            out_dir = tmp_path / t
            out_dir.mkdir(exist_ok=True)
            times = []
            rc = 0
            for _ in range(reps):
                t0 = time.monotonic()
                p = subprocess.run(
                    rustc_cmd + [
                        "--edition=2021", "--crate-type=rlib,staticlib",
                        "-C", "opt-level=3", "-C", "panic=abort",
                        "--emit=obj,llvm-ir,asm", "--target", t,
                        str(src), "--out-dir", str(out_dir)
                    ] + extra_flags,
                    capture_output=True, text=True
                )
                times.append(time.monotonic() - t0)
                rc = p.returncode
                if rc != 0:
                    break
            sizes = {f.name: f.stat().st_size for f in out_dir.iterdir()} if out_dir.is_dir() else {}
            results[t] = {
                "returncode": rc,
                "timing_sec": summarize_samples(times),
                "artifacts_bytes": sizes,
            }
    return results

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rustc", default="rustc +1.99.1-x86_64-unknown-linux-gnu", help="rustc command or path")
    parser.add_argument("--suite", choices=["manifest-check", "tier1-smoke"], default="manifest-check")
    parser.add_argument("--reps", type=int, default=3, help="Repetitions per target")
    parser.add_argument("--crate-flags-json", type=Path, help="Optional JSON mapping crate name to extra rustc flags")
    parser.add_argument("--fn-filter", default="", help="Optional per-function filter forwarded via ANNEAL_FN_FILTER")
    args = parser.parse_args()

    crates_data = json.loads((HERE / "crates_manifest.json").read_text(encoding="utf-8"))
    apps_data = json.loads((HERE / "applications_and_benchmarks.json").read_text(encoding="utf-8"))
    conv_data = json.loads((HERE / "measurement_conventions.json").read_text(encoding="utf-8"))

    assert len(crates_data["top_100_by_recent_downloads"]) == 100
    assert all(c["crate_archive_sha256"] for c in crates_data["top_100_by_recent_downloads"])
    assert len(crates_data["stratified_25_crate_subset"]) == 25
    assert len(apps_data["applications"]) >= 8

    if args.suite == "manifest-check":
        print(json.dumps({
            "status": "ok",
            "top_100_verified": len(crates_data["top_100_by_recent_downloads"]),
            "dependency_closure_count": len(crates_data["dependency_closure_lock_checksums"]),
            "stratified_subset_count": len(crates_data["stratified_25_crate_subset"]),
            "applications_count": len(apps_data["applications"]),
            "statistical_sample_size_rule": conv_data["statistical_protocol"]["sample_size"],
        }, indent=2))
        return 0

    rustc_cmd = args.rustc.split()
    extra = []
    if args.fn_filter:
        os.environ["ANNEAL_FN_FILTER"] = args.fn_filter
    out = run_tier1_smoke(rustc_cmd, extra, args.reps)
    print(json.dumps(out, indent=2))
    return 0 if all(v["returncode"] == 0 for v in out.values()) else 1

if __name__ == "__main__":
    sys.exit(main())
