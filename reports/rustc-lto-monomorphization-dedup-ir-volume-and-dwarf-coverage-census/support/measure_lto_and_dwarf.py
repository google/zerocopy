#!/usr/bin/env python3
"""Reproducible empirical sweep for rustc 1.99.1 LLVM IR volume, LTO dedup, and DWARF coverage.

Usage:
  python3 measure_lto_and_dwarf.py \
      --manifest-path /path/to/anneal/Cargo.toml \
      --ll-root /path/to/emitted_ll_dir \
      --out-dir ./results \
      --toolchain +1.99.1
"""
import argparse
import json
import os
from pathlib import Path
import statistics
import subprocess
import tempfile
import time


def measure_ir_volume(root: Path) -> dict:
    """Count defined functions, basic blocks, and LLVM instructions across compiled runtime .ll files."""
    lls = sorted(p for p in root.rglob("*.ll") if p.stat().st_size > 1000 and "/build/" not in str(p))
    per_crate = []
    tot_fns = tot_bbs = tot_insts = 0
    for ll in lls:
        fns = bbs = insts = 0
        in_fn = False
        for ln in ll.read_text(encoding="utf-8", errors="ignore").splitlines():
            if not in_fn:
                if ln.startswith("define ") and ln.rstrip().endswith("{"):
                    in_fn = True
                    fns += 1
                    bbs += 1
            else:
                if ln == "}":
                    in_fn = False
                else:
                    s = ln.lstrip()
                    if not s or s.startswith(";"):
                        continue
                    if ln[0] != " " and ln[0] != "\t" and ":" in ln:
                        bbs += 1
                    else:
                        insts += 1
        tot_fns += fns
        tot_bbs += bbs
        tot_insts += insts
        per_crate.append({"file": ll.name, "fns": fns, "bbs": bbs, "insts": insts})
    per_crate.sort(key=lambda x: x["insts"], reverse=True)
    return {
        "num_runtime_ll_files": len(lls),
        "total_post_o3_fns": tot_fns,
        "total_post_o3_bbs": tot_bbs,
        "total_post_o3_llvm_insts": tot_insts,
        "mean_insts_per_fn": round(tot_insts / max(tot_fns, 1), 2),
        "top_15_crates": per_crate[:15],
    }


def elf_text_and_syms(bin_path: Path) -> dict:
    sz_out = subprocess.check_output(["size", str(bin_path)], text=True).splitlines()
    text_b = int(sz_out[1].split()[0]) if len(sz_out) >= 2 else 0
    nm_out = subprocess.check_output(["nm", "--defined-only", "-n", str(bin_path)], text=True).splitlines()
    text_syms = [ln for ln in nm_out if " t " in ln or " T " in ln]
    generic_syms = sum(1 for ln in text_syms if "_RIN" in ln)
    return {
        "file_bytes": bin_path.stat().st_size,
        "text_bytes": text_b,
        "defined_text_symbols": len(text_syms),
        "v0_generic_monomorph_symbols": generic_syms,
    }


def run_lto_sweep(manifest: str, toolchain: str, work: Path) -> dict:
    configs = [
        ("lto_off_cgu16", {"CARGO_PROFILE_RELEASE_LTO": "off", "CARGO_PROFILE_RELEASE_CODEGEN_UNITS": "16"}),
        ("lto_off_cgu1", {"CARGO_PROFILE_RELEASE_LTO": "off", "CARGO_PROFILE_RELEASE_CODEGEN_UNITS": "1"}),
        ("lto_thin", {"CARGO_PROFILE_RELEASE_LTO": "thin"}),
        ("lto_fat", {"CARGO_PROFILE_RELEASE_LTO": "fat"}),
    ]
    rows = {}
    for name, cenv in configs:
        tdir = work / f"lto_{name}"
        env = os.environ.copy()
        env.pop("RUSTFLAGS", None)
        env.update(cenv)
        env["RUSTC_ICE"] = "0"
        t0 = time.monotonic()
        res = subprocess.run(
            ["cargo", toolchain, "build", "--manifest-path", manifest,
             "-p", "anneal-audit", "--bin", "anneal-audit", "--release",
             "--target-dir", str(tdir)],
            cwd=str(work), env=env, capture_output=True, text=True, timeout=600,
        )
        if res.returncode != 0:
            raise RuntimeError(f"LTO {name} failed (rc={res.returncode}): {res.stderr[-800:]}")
        build_s = round(time.monotonic() - t0, 2)
        bin_p = tdir / "release/anneal-audit"
        meta = elf_text_and_syms(bin_p)
        run_ms = []
        for _ in range(7):
            rt0 = time.monotonic()
            subprocess.run([str(bin_p), "--help"], capture_output=True, text=True, timeout=30)
            run_ms.append((time.monotonic() - rt0) * 1000.0)
        rows[name] = {
            "cargo_profile_env": cenv,
            "clean_build_sec": build_s,
            **meta,
            "cli_median_ms": round(statistics.median(run_ms), 3),
        }
    return rows


def run_dwarf_coverage_sweep(manifest: str, toolchain: str, work: Path) -> dict:
    rows = {}
    for opt in ("0", "1", "2", "3"):
        tdir = work / f"dwarf_O{opt}"
        env = os.environ.copy()
        env.pop("RUSTFLAGS", None)
        env["CARGO_PROFILE_DEV_OPT_LEVEL"] = opt
        env["CARGO_PROFILE_DEV_DEBUG"] = "2"
        env["RUSTC_ICE"] = "0"
        res = subprocess.run(
            ["cargo", toolchain, "build", "--manifest-path", manifest,
             "-p", "anneal-audit", "--bin", "anneal-audit",
             "--target-dir", str(tdir)],
            cwd=str(work), env=env, capture_output=True, text=True, timeout=600,
        )
        if res.returncode != 0:
            raise RuntimeError(f"DWARF O{opt} failed (rc={res.returncode}): {res.stderr[-800:]}")
        bin_p = tdir / "debug/anneal-audit"
        st = json.loads(subprocess.check_output(["llvm-dwarfdump", "--statistics", str(bin_p)], text=True, timeout=120))
        tot_vars = st.get("#local vars processed by location statistics", 0)
        cov_100 = st.get("#local vars with 100% of parent scope covered by DW_AT_location", 0)
        cov_0 = st.get("#local vars with 0% of parent scope covered by DW_AT_location", 0)
        tot_params = st.get("#params processed by location statistics", 0)
        p_100 = st.get("#params with 100% of parent scope covered by DW_AT_location", 0)
        p_0 = st.get("#params with 0% of parent scope covered by DW_AT_location", 0)
        pc_cov = st.get("sum_all_variables(#bytes in parent scope covered by DW_AT_location)", 0)
        pc_tot = st.get("sum_all_variables(#bytes in parent scope)", 1)
        rows[f"O{opt}"] = {
            "opt_level": int(opt),
            "binary_mb": round(bin_p.stat().st_size / (1024 * 1024), 2),
            "dwarf_version": st.get("version"),
            "local_vars_total": tot_vars,
            "local_vars_100pct_cov": cov_100,
            "local_vars_0pct_cov": cov_0,
            "local_vars_100pct_pct": round(100.0 * cov_100 / max(tot_vars, 1), 2),
            "local_vars_0pct_pct": round(100.0 * cov_0 / max(tot_vars, 1), 2),
            "params_total": tot_params,
            "params_100pct_pct": round(100.0 * p_100 / max(tot_params, 1), 2),
            "params_0pct_pct": round(100.0 * p_0 / max(tot_params, 1), 2),
            "pc_bytes_covered_pct": round(100.0 * pc_cov / max(pc_tot, 1), 2),
            "raw_stats_subset": {k: v for k, v in st.items() if "location" in k or "scope" in k or "inlined" in k},
        }
    return rows


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest-path", required=True)
    ap.add_argument("--ll-root", required=True)
    ap.add_argument("--out-dir", required=True)
    ap.add_argument("--toolchain", default="+1.99.1")
    args = ap.parse_args()

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="rustc_lto_dwarf_") as td:
        work = Path(td)
        ir_vol = measure_ir_volume(Path(args.ll_root))
        lto = run_lto_sweep(args.manifest_path, args.toolchain, work)
        (out_dir / "e1_6_real_lto_and_ir_volume.json").write_text(
            json.dumps({"benchmark": "E1-6_T11_real_lto_and_ir_volume", "ir_volume": ir_vol, "lto_sweep": lto}, indent=2)
        )
        dwarf = run_dwarf_coverage_sweep(args.manifest_path, args.toolchain, work)
        (out_dir / "e1_7_real_dwarf_coverage.json").write_text(
            json.dumps({"benchmark": "E1-7_T06_real_dwarf_coverage", "opt_sweep": dwarf}, indent=2)
        )


if __name__ == "__main__":
    main()
