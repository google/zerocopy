#!/usr/bin/env python3
"""Standalone empirical probe suite for ELF loader closure, component economics, and sysroot resolution:
1. Transitive GNU glibc ld.so DT_RPATH vs. DT_RUNPATH inheritance & /proc/self/maps closure
   (Cases A, B, C under cross-nightly libLLVM.so SONAME collision).
2. Custom monorepo librustc_driver symbol mangling (-C metadata & CFG_VERSION /
   RUSTC_FORCE_RUSTC_VERSION) and rustc -vV / rustc_version_str() formats.
3. Official Rust channel manifest & on-disk component byte economics (rustc, rust-std,
   rustc-dev, cargo), compile-time/RSS/binary-size measurements of a zero-dependency
   rustc_private MIR-capture driver, and runtime execution with 0 bytes of rustc-dev.
4. filesearch.rs AT_FDCWD "lib/rustlib" symlink-sysroot bug across installed releases
   (1.56.0..1.102.0-nightly) and sealed --sysroot isolation audit (core, proc_macro, tools).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import tempfile
import time
import tomllib
import urllib.request
from pathlib import Path
from typing import Any


MIR_CAPTURE_DRIVER_RS = r'''#![feature(rustc_private, cfg_version)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;

use std::fs;
use std::process::ExitCode;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;

struct CaptureCallbacks {
    bodies: usize,
    basic_blocks: usize,
    statements: usize,
    terminators: usize,
    extern_crates: usize,
    version_str: Option<&'static str>,
}

impl Callbacks for CaptureCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        self.version_str = rustc_interface::util::rustc_version_str();
        self.extern_crates = tcx.crates(()).len();
        for &cnum in tcx.crates(()) {
            let _src = tcx.used_crate_source(cnum);
        }
        for local_def_id in tcx.hir_body_owners() {
            let body = tcx.mir_drops_elaborated_and_const_checked(local_def_id).borrow();
            self.bodies += 1;
            for bb_data in body.basic_blocks.iter() {
                self.basic_blocks += 1;
                self.statements += bb_data.statements.len();
                if bb_data.terminator.is_some() {
                    self.terminators += 1;
                }
            }
        }
        Compilation::Stop
    }
}

fn collect_toolchain_maps() -> Vec<String> {
    let Ok(maps) = fs::read_to_string("/proc/self/maps") else {
        return Vec::new();
    };
    let mut seen = Vec::new();
    for line in maps.lines() {
        if let Some(idx) = line.find('/') {
            let path = line[idx..].trim().to_string();
            if (path.contains("librustc_driver")
                || path.contains("libLLVM")
                || path.contains("libstd-")
                || path.contains("librustc_codegen"))
                && !seen.contains(&path)
            {
                seen.push(path);
            }
        }
    }
    seen
}

fn invoke_driver(args: &[String], cb: &mut CaptureCallbacks) {
    #[cfg(version("1.102"))]
    {
        rustc_driver::compiler_entrypoint(args, cb);
    }
    #[cfg(not(version("1.102")))]
    {
        rustc_driver::run_compiler(args, cb);
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let mut cb = CaptureCallbacks {
        bodies: 0,
        basic_blocks: 0,
        statements: 0,
        terminators: 0,
        extern_crates: 0,
        version_str: rustc_interface::util::rustc_version_str(),
    };
    let exit_code = rustc_driver::catch_with_exit_code(|| {
        invoke_driver(&args, &mut cb);
    });
    let ok = exit_code == ExitCode::SUCCESS;
    let mapped = collect_toolchain_maps();
    println!(
        "CAPTURE_REPORT ok={} version_str={:?} bodies={} bbs={} stmts={} terms={} crates={}",
        ok,
        cb.version_str,
        cb.bodies,
        cb.basic_blocks,
        cb.statements,
        cb.terminators,
        cb.extern_crates
    );
    for m in mapped {
        println!("MAPPED_SO {}", m);
    }
    exit_code
}
'''

SAMPLE_TARGET_CRATE_RS = r'''#![crate_type = "lib"]

pub fn checked_linear_combination(xs: &[u32; 4], scale: u32) -> Option<u32> {
    let mut acc: u32 = 0;
    let mut i = 0;
    while i < xs.len() {
        let term = xs[i].checked_mul(scale)?;
        acc = acc.checked_add(term)?;
        i += 1;
    }
    Some(acc)
}
'''


def clean_env(extra: dict[str, str] | None = None, remove_llp: bool = True) -> dict[str, str]:
    env = dict(os.environ)
    for k in ("RUSTUP_TOOLCHAIN", "RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER"):
        env.pop(k, None)
    if remove_llp:
        env.pop("LD_LIBRARY_PATH", None)
    if extra:
        env.update(extra)
    return env


def parse_rustc_vv(rustc_bin: Path) -> dict[str, str]:
    out = subprocess.check_output(
        [str(rustc_bin), "-vV"], env=clean_env(), text=True, stderr=subprocess.STDOUT
    )
    lines = [ln.strip() for ln in out.strip().splitlines() if ln.strip()]
    info: dict[str, str] = {"headline": lines[0] if lines else "", "raw": out.strip()}
    for ln in lines[1:]:
        if ":" in ln:
            k, v = ln.split(":", 1)
            info[k.strip()] = v.strip()
    return info


def readelf_dynamic_rpath(elf_path: Path) -> dict[str, Any]:
    out = subprocess.check_output(["readelf", "-d", str(elf_path)], text=True)
    dt_rpath = None
    dt_runpath = None
    dt_soname = None
    dt_needed: list[str] = []
    for ln in out.splitlines():
        if "(RPATH)" in ln:
            m = re.search(r"\[(.*?)\]", ln)
            dt_rpath = m.group(1) if m else ln.strip()
        elif "(RUNPATH)" in ln:
            m = re.search(r"\[(.*?)\]", ln)
            dt_runpath = m.group(1) if m else ln.strip()
        elif "(SONAME)" in ln:
            m = re.search(r"\[(.*?)\]", ln)
            dt_soname = m.group(1) if m else ln.strip()
        elif "(NEEDED)" in ln:
            m = re.search(r"\[(.*?)\]", ln)
            if m:
                dt_needed.append(m.group(1))
    return {
        "dt_rpath": dt_rpath,
        "dt_runpath": dt_runpath,
        "dt_soname": dt_soname,
        "dt_needed": dt_needed,
    }


def sanitize_kernel_release(rel: str) -> str:
    m = re.match(r"^(\d+\.\d+(?:\.\d+)?)", rel)
    return f"{m.group(1)}-{platform.machine()}" if m else platform.machine()


def sanitize_ldd_headline(line: str) -> str:
    m = re.search(r"(\d+\.\d+)\s*$", line.strip())
    return f"ldd (GNU libc) {m.group(1)}" if m else "ldd (GNU libc)"


def run_probe1_glibc_rpath_and_maps(
    toolchains_dir: Path, patchelf_bin: Path
) -> dict[str, Any]:
    """Empirical proof of glibc ld.so DT_RPATH vs DT_RUNPATH transitivity & /proc/self/maps."""
    tc_main = toolchains_dir / "nightly-x86_64-unknown-linux-gnu"
    tc_poison = toolchains_dir / "nightly-2026-11-20-x86_64-unknown-linux-gnu"
    tc_alt = toolchains_dir / "nightly-2026-11-13-x86_64-unknown-linux-gnu"

    main_vv = parse_rustc_vv(tc_main / "bin" / "rustc")
    poison_vv = parse_rustc_vv(tc_poison / "bin" / "rustc")
    alt_vv = parse_rustc_vv(tc_alt / "bin" / "rustc")

    driver_so_main = next((tc_main / "lib").glob("librustc_driver-*.so"))
    llvm_so_main = next((tc_main / "lib").glob("libLLVM.so.*"))
    llvm_so_poison = next((tc_poison / "lib").glob("libLLVM.so.*"))
    llvm_so_alt = next((tc_alt / "lib").glob("libLLVM.so.*"))

    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = Path(tmp_str)
        driver_src = tmp / "driver.rs"
        target_src = tmp / "sample.rs"
        driver_src.write_text(MIR_CAPTURE_DRIVER_RS, encoding="utf-8")
        target_src.write_text(SAMPLE_TARGET_CRATE_RS, encoding="utf-8")

        bin_base = tmp / "capture_base"
        subprocess.run(
            [
                str(tc_main / "bin" / "rustc"),
                "--edition=2021",
                "-O",
                f"-Clink-arg=-Wl,-rpath,{tc_main / 'lib'}",
                str(driver_src),
                "-o",
                str(bin_base),
            ],
            env=clean_env(),
            check=True,
        )

        def parse_run(bin_path: Path, env: dict[str, str], sysroot: Path) -> dict[str, Any]:
            proc = subprocess.run(
                [
                    str(bin_path),
                    str(target_src),
                    "--sysroot",
                    str(sysroot),
                    "--edition=2021",
                ],
                env=env,
                capture_output=True,
                text=True,
            )
            mapped = []
            report_line = None
            for ln in proc.stdout.splitlines():
                if ln.startswith("CAPTURE_REPORT "):
                    report_line = ln
                elif ln.startswith("MAPPED_SO "):
                    mapped.append(ln[len("MAPPED_SO ") :].strip())
            ld_debug_interesting = []
            for ln in proc.stderr.splitlines():
                if any(
                    tok in ln
                    for tok in (
                        "find library=librustc_driver",
                        "find library=libLLVM",
                        "find library=libstd-",
                        "trying file=",
                        "search path=",
                    )
                ):
                    if len(ld_debug_interesting) < 40:
                        ld_debug_interesting.append(ln.strip())
            return {
                "returncode": proc.returncode,
                "report": report_line,
                "mapped_so": mapped,
                "ld_debug_excerpt": ld_debug_interesting,
            }

        bin_case_a = tmp / "capture_case_a"
        shutil.copy2(bin_base, bin_case_a)
        subprocess.run(
            [
                str(patchelf_bin),
                "--force-rpath",
                "--set-rpath",
                str(tc_main / "lib"),
                str(bin_case_a),
            ],
            check=True,
        )
        env_poisoned_debug = clean_env(
            {
                "LD_LIBRARY_PATH": str(tc_poison / "lib"),
                "LD_DEBUG": "libs",
            },
            remove_llp=False,
        )
        res_case_a = parse_run(bin_case_a, env_poisoned_debug, tc_main)

        staged_sysroot = tmp / "staged_nightly"
        (staged_sysroot / "lib").mkdir(parents=True)
        staged_driver_so = staged_sysroot / "lib" / driver_so_main.name
        shutil.copy2(driver_so_main, staged_driver_so)
        os.chmod(staged_driver_so, 0o755)
        for item in (tc_main / "lib").iterdir():
            dst = staged_sysroot / "lib" / item.name
            if not dst.exists():
                dst.symlink_to(item)
        subprocess.run(
            [
                str(patchelf_bin),
                "--force-rpath",
                "--set-rpath",
                "$ORIGIN/../lib",
                str(staged_driver_so),
            ],
            check=True,
        )
        bin_case_b = tmp / "capture_case_b"
        shutil.copy2(bin_base, bin_case_b)
        subprocess.run(
            [
                str(patchelf_bin),
                "--force-rpath",
                "--set-rpath",
                str(staged_sysroot / "lib"),
                str(bin_case_b),
            ],
            check=True,
        )
        res_case_b = parse_run(bin_case_b, env_poisoned_debug, staged_sysroot)

        env_scrubbed_debug = clean_env({"LD_DEBUG": "libs"}, remove_llp=True)
        res_case_c = parse_run(bin_base, env_scrubbed_debug, tc_main)

        expected_lib_real = str((tc_main / "lib").resolve())
        case_a_driver_only_check_passes = all(
            p.startswith(expected_lib_real)
            for p in res_case_a["mapped_so"]
            if "librustc_driver-" in p
        )
        case_a_full_closure_check_passes = all(
            p.startswith(expected_lib_real) for p in res_case_a["mapped_so"]
        )
        case_c_full_closure_check_passes = all(
            p.startswith(expected_lib_real) for p in res_case_c["mapped_so"]
        )

        ldd_first = subprocess.check_output(["ldd", "--version"], text=True).splitlines()[0]
        return {
            "host_ldd_version": sanitize_ldd_headline(ldd_first),
            "patchelf_version": subprocess.check_output(
                [str(patchelf_bin), "--version"], text=True
            ).strip(),
            "toolchains": {
                "nightly_main": {
                    "headline": main_vv["headline"],
                    "commit_hash": main_vv.get("commit-hash"),
                    "llvm_version": main_vv.get("LLVM version"),
                    "driver_so": driver_so_main.name,
                    "driver_elf": readelf_dynamic_rpath(driver_so_main),
                    "llvm_so": llvm_so_main.name,
                    "llvm_sha256_prefix16": hashlib.sha256(
                        llvm_so_main.read_bytes()
                    ).hexdigest()[:16],
                },
                "nightly_2026_11_20_poison": {
                    "headline": poison_vv["headline"],
                    "commit_hash": poison_vv.get("commit-hash"),
                    "llvm_version": poison_vv.get("LLVM version"),
                    "llvm_so": llvm_so_poison.name,
                    "llvm_sha256_prefix16": hashlib.sha256(
                        llvm_so_poison.read_bytes()
                    ).hexdigest()[:16],
                },
                "nightly_2026_11_13_collision": {
                    "headline": alt_vv["headline"],
                    "commit_hash": alt_vv.get("commit-hash"),
                    "llvm_version": alt_vv.get("LLVM version"),
                    "llvm_so": llvm_so_alt.name,
                },
            },
            "shared_llvm_soname_equal": (
                llvm_so_main.name == llvm_so_poison.name == llvm_so_alt.name
            ),
            "case_a_exe_dt_rpath_only": {
                "exe_elf": readelf_dynamic_rpath(bin_case_a),
                "driver_elf": readelf_dynamic_rpath(driver_so_main),
                "result": res_case_a,
                "driver_only_maps_check_passes_falsely": case_a_driver_only_check_passes,
                "full_closure_maps_check_passes": case_a_full_closure_check_passes,
            },
            "case_b_both_exe_and_driver_dt_rpath": {
                "exe_elf": readelf_dynamic_rpath(bin_case_b),
                "driver_elf": readelf_dynamic_rpath(staged_driver_so),
                "result": res_case_b,
            },
            "case_c_parent_scrubs_llp_plus_full_maps_closure": {
                "exe_elf": readelf_dynamic_rpath(bin_base),
                "result": res_case_c,
                "full_closure_maps_check_passes": case_c_full_closure_check_passes,
            },
        }


def run_probe2_monorepo_abi_and_version_formats(toolchains_dir: Path) -> dict[str, Any]:
    """Empirical proof of CFG_VERSION / -C metadata symbol mangling & version string formats."""
    tc_stable = toolchains_dir / "stable-x86_64-unknown-linux-gnu"
    tc_nightly = toolchains_dir / "nightly-x86_64-unknown-linux-gnu"
    tc_stage1 = toolchains_dir / "stage1"

    def inspect_driver_abi(tc: Path) -> dict[str, Any]:
        rustc_bin = tc / "bin" / "rustc"
        vv = parse_rustc_vv(rustc_bin)
        drivers = list((tc / "lib").glob("librustc_driver*.so"))
        driver_so = drivers[0] if drivers else None
        sample_syms: list[str] = []
        if driver_so:
            nm_out = subprocess.check_output(
                ["nm", "-D", "--defined-only", str(driver_so)], text=True
            )
            for ln in nm_out.splitlines():
                parts = ln.split()
                if len(parts) >= 3 and "run_compiler" in parts[2]:
                    sample_syms.append(parts[2])
                    if len(sample_syms) >= 5:
                        break
        return {
            "rustc_vv": vv,
            "driver_filename": driver_so.name if driver_so else None,
            "driver_soname": readelf_dynamic_rpath(driver_so)["dt_soname"]
            if driver_so
            else None,
            "run_compiler_exported_symbols": sample_syms,
        }

    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = Path(tmp_str)
        lib_src = tmp / "mock_driver.rs"
        lib_src.write_text(
            '#![crate_type = "dylib"]\n'
            "pub fn run_compiler_entry(x: u64) -> u64 { x.wrapping_add(1) }\n",
            encoding="utf-8",
        )
        rustc_bin = tc_nightly / "bin" / "rustc"

        variants = [
            (
                "upstream_baseline",
                ["-Cmetadata=nightly1.102.0", "-Csymbol-mangling-version=v0"],
                {"RUSTC_FORCE_RUSTC_VERSION": "1.102.0-nightly (3ef0c22cd 2026-11-11)"},
            ),
            (
                "same_sha_chromium_description",
                ["-Cmetadata=nightly1.102.0", "-Csymbol-mangling-version=v0"],
                {
                    "RUSTC_FORCE_RUSTC_VERSION": (
                        "1.102.0-nightly (3ef0c22cd 2026-11-11) "
                        "(3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1-1-llvmorg-23 chromium)"
                    )
                },
            ),
            (
                "same_sha_omit_git_hash",
                ["-Cmetadata=nightly1.102.0", "-Csymbol-mangling-version=v0"],
                {"RUSTC_FORCE_RUSTC_VERSION": "1.102.0-nightly"},
            ),
            (
                "same_sha_dev_channel_metadata",
                ["-Cmetadata=dev1.102.0", "-Csymbol-mangling-version=v0"],
                {"RUSTC_FORCE_RUSTC_VERSION": "1.102.0-dev"},
            ),
            (
                "legacy_mangling_upstream",
                [
                    "-Cmetadata=nightly1.102.0",
                    "-Csymbol-mangling-version=legacy",
                    "-Zunstable-options",
                ],
                {"RUSTC_FORCE_RUSTC_VERSION": "1.102.0-nightly (3ef0c22cd 2026-11-11)"},
            ),
            (
                "legacy_mangling_chromium_description",
                [
                    "-Cmetadata=nightly1.102.0",
                    "-Csymbol-mangling-version=legacy",
                    "-Zunstable-options",
                ],
                {
                    "RUSTC_FORCE_RUSTC_VERSION": (
                        "1.102.0-nightly (3ef0c22cd 2026-11-11) "
                        "(3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1-1-llvmorg-23 chromium)"
                    )
                },
            ),
        ]
        mangling_matrix = {}
        for label, flags, extra_env in variants:
            out_so = tmp / f"libmock_{label}.so"
            subprocess.run(
                [str(rustc_bin), "--edition=2021", *flags, str(lib_src), "-o", str(out_so)],
                env=clean_env(extra_env),
                check=True,
            )
            nm_out = subprocess.check_output(
                ["nm", "-D", "--defined-only", str(out_so)], text=True
            )
            exported = [
                ln.split()[2]
                for ln in nm_out.splitlines()
                if len(ln.split()) >= 3 and "run_compiler_entry" in ln.split()[2]
            ]
            mangling_matrix[label] = {
                "flags": flags,
                "cfg_version_simulated": extra_env["RUSTC_FORCE_RUSTC_VERSION"],
                "exported_symbol": exported[0] if exported else None,
            }

        override_vv = subprocess.check_output(
            [str(rustc_bin), "-vV"],
            env=clean_env({"RUSTC_OVERRIDE_VERSION_STRING": "1.99.9-custom-monorepo"}),
            text=True,
        ).strip()

    toolchains_abi = {
        "stable_1_100_0": inspect_driver_abi(tc_stable),
        "nightly_2026_11_11": inspect_driver_abi(tc_nightly),
    }
    if tc_stage1.exists():
        toolchains_abi["local_stage1_dev_build"] = inspect_driver_abi(tc_stage1)

    return {
        "installed_toolchains_abi": toolchains_abi,
        "controlled_cfg_version_and_metadata_mangling_matrix": mangling_matrix,
        "runtime_override_version_string_vv": override_vv,
    }


def measure_manifest_component_bytes(sysroot: Path, manifest_name: str) -> dict[str, Any]:
    mpath = sysroot / "lib" / "rustlib" / manifest_name
    if not mpath.exists():
        return {"present": False, "file_count": 0, "installed_bytes": 0}
    total = 0
    count = 0
    by_ext: dict[str, int] = {}
    for ln in mpath.read_text(encoding="utf-8").splitlines():
        if ln.startswith("file:"):
            rel = ln[len("file:") :]
            fp = sysroot / rel
            if fp.is_file():
                sz = fp.stat().st_size
                total += sz
                count += 1
                ext = "".join(fp.suffixes[-2:]) if len(fp.suffixes) >= 2 else fp.suffix
                by_ext[ext or "<bin>"] = by_ext.get(ext or "<bin>", 0) + sz
    top_ext = dict(sorted(by_ext.items(), key=lambda kv: kv[1], reverse=True)[:8])
    return {
        "present": True,
        "file_count": count,
        "installed_bytes": total,
        "installed_mib": round(total / (1024 * 1024), 2),
        "top_extensions_bytes": top_ext,
    }


def fetch_channel_manifest_economics(url: str, target: str) -> dict[str, Any]:
    req = urllib.request.Request(url, method="GET")
    with urllib.request.urlopen(req, timeout=25) as resp:
        raw = resp.read()
    manifest_sha256 = hashlib.sha256(raw).hexdigest()
    parsed = tomllib.loads(raw.decode("utf-8"))
    date = parsed.get("date")
    pkgs_out: dict[str, Any] = {}
    for pkg_name in ("rustc", "rust-std", "rustc-dev", "cargo", "rust-src"):
        pkg = parsed.get("pkg", {}).get(pkg_name, {})
        tgt_tbl = pkg.get("target", {})
        entry = tgt_tbl.get(target) or tgt_tbl.get("*")
        if not entry or not entry.get("available", False):
            continue
        xz_url = entry.get("xz_url")
        xz_hash = entry.get("xz_hash")
        gz_url = entry.get("url")
        gz_hash = entry.get("hash")
        xz_bytes = None
        gz_bytes = None
        for kind, archive_url in (("xz", xz_url), ("gz", gz_url)):
            if archive_url:
                hreq = urllib.request.Request(archive_url, method="HEAD")
                with urllib.request.urlopen(hreq, timeout=15) as hresp:
                    clen = hresp.headers.get("Content-Length")
                    if clen is not None:
                        if kind == "xz":
                            xz_bytes = int(clen)
                        else:
                            gz_bytes = int(clen)
        pkgs_out[pkg_name] = {
            "version": pkg.get("version"),
            "git_commit_hash": pkg.get("git_commit_hash"),
            "xz_url": xz_url,
            "xz_sha256": xz_hash,
            "xz_compressed_bytes": xz_bytes,
            "xz_compressed_mib": round(xz_bytes / (1024 * 1024), 2)
            if xz_bytes is not None
            else None,
            "gz_url": gz_url,
            "gz_sha256": gz_hash,
            "gz_compressed_bytes": gz_bytes,
            "gz_compressed_mib": round(gz_bytes / (1024 * 1024), 2)
            if gz_bytes is not None
            else None,
        }
    return {
        "manifest_url": url,
        "manifest_sha256": manifest_sha256,
        "manifest_date": date,
        "target": target,
        "components": pkgs_out,
    }


def parse_gnu_time_rss_kb(stderr_text: str) -> int | None:
    for ln in stderr_text.splitlines():
        if "Maximum resident set size (kbytes):" in ln:
            return int(ln.split(":")[-1].strip())
    return None


def benchmark_driver_compile_and_zero_rustc_dev_runtime(
    toolchains_dir: Path,
) -> dict[str, Any]:
    tc_stable_with_dev = toolchains_dir / "stable-x86_64-unknown-linux-gnu"
    tc_1_100_no_dev = toolchains_dir / "1.100.0-x86_64-unknown-linux-gnu"
    tc_nightly = toolchains_dir / "nightly-x86_64-unknown-linux-gnu"

    results: dict[str, Any] = {}
    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = Path(tmp_str)
        driver_src = tmp / "driver.rs"
        target_src = tmp / "sample.rs"
        driver_src.write_text(MIR_CAPTURE_DRIVER_RS, encoding="utf-8")
        target_src.write_text(SAMPLE_TARGET_CRATE_RS, encoding="utf-8")

        for label, tc, need_bootstrap in [
            ("stable_1_100_0", tc_stable_with_dev, True),
            ("nightly_2026_11_11", tc_nightly, False),
        ]:
            rustc_bin = tc / "bin" / "rustc"
            extra_env = {"RUSTC_BOOTSTRAP": "1"} if need_bootstrap else {}
            env = clean_env(extra_env)

            out_bin = tmp / f"driver_{label}"
            t0 = time.perf_counter()
            c1 = subprocess.run(
                [
                    "/usr/bin/time",
                    "-v",
                    str(rustc_bin),
                    "--edition=2021",
                    "-O",
                    str(driver_src),
                    "-o",
                    str(out_bin),
                ],
                env=env,
                capture_output=True,
                text=True,
                check=True,
            )
            cold_ms = (time.perf_counter() - t0) * 1000.0
            cold_rss_kb = parse_gnu_time_rss_kb(c1.stderr)

            warm_times_ms = []
            warm_rss_kbs = []
            for idx in range(3):
                out_warm = tmp / f"driver_{label}_warm_{idx}"
                tw = time.perf_counter()
                cw = subprocess.run(
                    [
                        "/usr/bin/time",
                        "-v",
                        str(rustc_bin),
                        "--edition=2021",
                        "-O",
                        str(driver_src),
                        "-o",
                        str(out_warm),
                    ],
                    env=env,
                    capture_output=True,
                    text=True,
                    check=True,
                )
                warm_times_ms.append((time.perf_counter() - tw) * 1000.0)
                rss = parse_gnu_time_rss_kb(cw.stderr)
                if rss is not None:
                    warm_rss_kbs.append(rss)

            unstripped_bytes = out_bin.stat().st_size
            stripped_bin = tmp / f"driver_{label}_stripped"
            shutil.copy2(out_bin, stripped_bin)
            subprocess.run(["strip", "--strip-all", str(stripped_bin)], check=True)
            stripped_bytes = stripped_bin.stat().st_size

            results[label] = {
                "rustc_vv_headline": parse_rustc_vv(rustc_bin)["headline"],
                "rustc_bootstrap_env_required": need_bootstrap,
                "first_compile_wall_ms": round(cold_ms, 2),
                "first_compile_peak_rss_kib": cold_rss_kb,
                "first_compile_peak_rss_mib": round(cold_rss_kb / 1024.0, 2)
                if cold_rss_kb
                else None,
                "warm_compile_wall_ms_runs": [round(x, 2) for x in warm_times_ms],
                "warm_compile_wall_ms_median": round(sorted(warm_times_ms)[1], 2),
                "warm_compile_peak_rss_kib_median": sorted(warm_rss_kbs)[1]
                if len(warm_rss_kbs) == 3
                else None,
                "unstripped_binary_bytes": unstripped_bytes,
                "stripped_binary_bytes": stripped_bytes,
                "stripped_binary_kib": round(stripped_bytes / 1024.0, 2),
            }

        bin_bound_to_nodev = tmp / "driver_1_100_0_bound_to_nodev"
        subprocess.run(
            [
                str(tc_stable_with_dev / "bin" / "rustc"),
                "--edition=2021",
                "-O",
                f"-Clink-arg=-Wl,-rpath,{tc_1_100_no_dev / 'lib'}",
                str(driver_src),
                "-o",
                str(bin_bound_to_nodev),
            ],
            env=clean_env({"RUSTC_BOOTSTRAP": "1"}),
            check=True,
        )
        subprocess.run(["strip", "--strip-all", str(bin_bound_to_nodev)], check=True)
        run_nodev = subprocess.run(
            [
                str(bin_bound_to_nodev),
                str(target_src),
                "--sysroot",
                str(tc_1_100_no_dev),
                "--edition=2021",
            ],
            env=clean_env(),
            capture_output=True,
            text=True,
        )

        pruned_sysroot = tmp / "pruned_runtime_only_sysroot"
        for mname in (
            "manifest-rustc-x86_64-unknown-linux-gnu",
            "manifest-rust-std-x86_64-unknown-linux-gnu",
        ):
            for ln in (
                tc_stable_with_dev / "lib" / "rustlib" / mname
            ).read_text(encoding="utf-8").splitlines():
                if ln.startswith("file:"):
                    rel = ln[len("file:") :]
                    src_f = tc_stable_with_dev / rel
                    dst_f = pruned_sysroot / rel
                    dst_f.parent.mkdir(parents=True, exist_ok=True)
                    dst_f.symlink_to(src_f)
        rustc_dev_files_in_pruned = list(
            (pruned_sysroot / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "lib").glob(
                "librustc_*"
            )
        )
        bin_bound_to_pruned = tmp / "driver_1_100_0_bound_to_pruned"
        subprocess.run(
            [
                str(tc_stable_with_dev / "bin" / "rustc"),
                "--edition=2021",
                "-O",
                f"-Clink-arg=-Wl,-rpath,{pruned_sysroot / 'lib'}",
                str(driver_src),
                "-o",
                str(bin_bound_to_pruned),
            ],
            env=clean_env({"RUSTC_BOOTSTRAP": "1"}),
            check=True,
        )
        run_pruned = subprocess.run(
            [
                str(bin_bound_to_pruned),
                str(target_src),
                "--sysroot",
                str(pruned_sysroot),
                "--edition=2021",
            ],
            env=clean_env(),
            capture_output=True,
            text=True,
        )

        results["zero_rustc_dev_runtime_proofs"] = {
            "official_1_100_0_toolchain_without_rustc_dev": {
                "has_manifest_rustc_dev": (
                    tc_1_100_no_dev
                    / "lib"
                    / "rustlib"
                    / "manifest-rustc-dev-x86_64-unknown-linux-gnu"
                ).exists(),
                "librustc_rlib_rmeta_count": len(
                    list(
                        (
                            tc_1_100_no_dev
                            / "lib"
                            / "rustlib"
                            / "x86_64-unknown-linux-gnu"
                            / "lib"
                        ).glob("librustc_*")
                    )
                ),
                "returncode": run_nodev.returncode,
                "stdout": run_nodev.stdout.strip().splitlines(),
            },
            "staged_sysroot_with_only_rustc_and_rust_std_manifests": {
                "librustc_rlib_rmeta_count": len(rustc_dev_files_in_pruned),
                "returncode": run_pruned.returncode,
                "stdout": run_pruned.stdout.strip().splitlines(),
            },
        }

    return results


def run_probe3_component_economics(
    toolchains_dir: Path, offline: bool = False
) -> dict[str, Any]:
    tc_stable = toolchains_dir / "stable-x86_64-unknown-linux-gnu"
    tc_nightly = toolchains_dir / "nightly-x86_64-unknown-linux-gnu"

    on_disk_stable = {
        comp: measure_manifest_component_bytes(tc_stable, f"manifest-{comp}")
        for comp in (
            "rustc-x86_64-unknown-linux-gnu",
            "rust-std-x86_64-unknown-linux-gnu",
            "rustc-dev-x86_64-unknown-linux-gnu",
            "cargo-x86_64-unknown-linux-gnu",
            "llvm-tools-preview-x86_64-unknown-linux-gnu",
        )
    }
    on_disk_nightly = {
        comp: measure_manifest_component_bytes(tc_nightly, f"manifest-{comp}")
        for comp in (
            "rustc-x86_64-unknown-linux-gnu",
            "rust-std-x86_64-unknown-linux-gnu",
            "rustc-dev-x86_64-unknown-linux-gnu",
            "cargo-x86_64-unknown-linux-gnu",
            "rust-src",
        )
    }

    stable_lib_breakdown = {}
    for pat in ("librustc_driver-*.so", "libLLVM*.so*", "libstd-*.so"):
        matches = [
            p for p in (tc_stable / "lib").glob(pat) if p.is_file() and not p.is_symlink()
        ]
        stable_lib_breakdown[pat] = [
            {
                "name": p.name,
                "bytes": p.stat().st_size,
                "mib": round(p.stat().st_size / (1024 * 1024), 2),
            }
            for p in matches
        ]

    upstream_manifests = {}
    if not offline:
        for key, url in (
            (
                "channel_rust_1_100_0",
                "https://static.rust-lang.org/dist/channel-rust-1.100.0.toml",
            ),
            (
                "channel_rust_nightly_2026_11_12",
                "https://static.rust-lang.org/dist/2026-11-12/channel-rust-nightly.toml",
            ),
            (
                "channel_rust_nightly_latest",
                "https://static.rust-lang.org/dist/channel-rust-nightly.toml",
            ),
        ):
            upstream_manifests[key] = fetch_channel_manifest_economics(
                url, "x86_64-unknown-linux-gnu"
            )

    compile_and_runtime = benchmark_driver_compile_and_zero_rustc_dev_runtime(
        toolchains_dir
    )

    return {
        "upstream_channel_manifests": upstream_manifests,
        "installed_stable_1_100_0_components": on_disk_stable,
        "installed_stable_1_100_0_rustc_lib_files": stable_lib_breakdown,
        "installed_nightly_2026_11_11_components": on_disk_nightly,
        "driver_compile_and_runtime_benchmarks": compile_and_runtime,
    }


def run_probe4_filesearch_regression_and_sysroot_audit(
    toolchains_dir: Path,
) -> dict[str, Any]:
    """Test AT_FDCWD lib/rustlib bug across 1.56.0..nightly & sealed --sysroot isolation."""
    versions = [
        "1.56.0-x86_64-unknown-linux-gnu",
        "1.61.0-x86_64-unknown-linux-gnu",
        "1.78.0-x86_64-unknown-linux-gnu",
        "1.84.0-x86_64-unknown-linux-gnu",
        "1.93.1-x86_64-unknown-linux-gnu",
        "1.100.0-x86_64-unknown-linux-gnu",
        "nightly-x86_64-unknown-linux-gnu",
    ]
    matrix = []
    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = Path(tmp_str)
        cwd_clean = tmp / "cwd_without_lib_rustlib"
        cwd_clean.mkdir()
        cwd_decoy = tmp / "cwd_with_decoy_lib_rustlib"
        (cwd_decoy / "lib" / "rustlib").mkdir(parents=True)

        for tc_name in versions:
            tc_dir = toolchains_dir / tc_name
            if not tc_dir.exists():
                continue
            real_rustc = (tc_dir / "bin" / "rustc").resolve()
            real_sysroot = str(tc_dir.resolve())
            vv = parse_rustc_vv(real_rustc)

            cas_sysroot = tmp / f"cas_{tc_name}"
            (cas_sysroot / "bin").mkdir(parents=True)
            (cas_sysroot / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "lib").mkdir(
                parents=True
            )
            symlink_rustc = cas_sysroot / "bin" / "rustc"
            symlink_rustc.symlink_to(real_rustc)

            sysroot_in_clean_cwd = subprocess.check_output(
                [str(symlink_rustc), "--print", "sysroot"],
                cwd=str(cwd_clean),
                env=clean_env(),
                text=True,
            ).strip()
            sysroot_in_decoy_cwd = subprocess.check_output(
                [str(symlink_rustc), "--print", "sysroot"],
                cwd=str(cwd_decoy),
                env=clean_env(),
                text=True,
            ).strip()

            matrix.append(
                {
                    "toolchain": tc_name,
                    "headline": vv["headline"],
                    "commit_hash": vv.get("commit-hash"),
                    "cas_sysroot_expected": str(cas_sysroot),
                    "real_dll_sysroot": real_sysroot,
                    "printed_sysroot_when_cwd_lacks_lib_rustlib": sysroot_in_clean_cwd,
                    "printed_sysroot_when_cwd_has_decoy_lib_rustlib": sysroot_in_decoy_cwd,
                    "at_fdcwd_bug_present": (
                        sysroot_in_clean_cwd == real_sysroot
                        and sysroot_in_decoy_cwd == str(cas_sysroot)
                    ),
                }
            )

        tc_100 = toolchains_dir / "1.100.0-x86_64-unknown-linux-gnu"
        tc_nightly = toolchains_dir / "nightly-x86_64-unknown-linux-gnu"
        rustc_100 = tc_100 / "bin" / "rustc"
        rustc_nightly = tc_nightly / "bin" / "rustc"

        sealed_empty = tmp / "sealed_empty"
        sealed_empty.mkdir()
        nostd_src = tmp / "nostd.rs"
        nostd_src.write_text(
            '#![no_std]\n#![crate_type = "rlib"]\npub fn f() {}\n', encoding="utf-8"
        )
        r_core = subprocess.run(
            [
                str(rustc_100),
                "--sysroot",
                str(sealed_empty),
                str(nostd_src),
                "--out-dir",
                str(tmp),
            ],
            env=clean_env(),
            capture_output=True,
            text=True,
        )

        sealed_no_pm = tmp / "sealed_no_proc_macro"
        tlib_dst = sealed_no_pm / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "lib"
        tlib_dst.mkdir(parents=True)
        for item in (
            tc_100 / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "lib"
        ).iterdir():
            if "proc_macro" not in item.name:
                (tlib_dst / item.name).symlink_to(item)
        pm_src = tmp / "my_pm.rs"
        pm_src.write_text(
            '#![crate_type = "proc-macro"]\nextern crate proc_macro;\n'
            "use proc_macro::TokenStream;\n"
            "#[proc_macro]\npub fn m(ts: TokenStream) -> TokenStream { ts }\n",
            encoding="utf-8",
        )
        r_pm = subprocess.run(
            [
                str(rustc_100),
                "--sysroot",
                str(sealed_no_pm),
                str(pm_src),
                "--out-dir",
                str(tmp),
            ],
            env=clean_env(),
            capture_output=True,
            text=True,
        )

        sealed_no_tools = tmp / "sealed_no_tools_bin"
        ntlib_dst = (
            sealed_no_tools / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "lib"
        )
        ntlib_dst.mkdir(parents=True)
        for item in (
            tc_nightly / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "lib"
        ).iterdir():
            (ntlib_dst / item.name).symlink_to(item)
        bin_src = tmp / "hello_bin.rs"
        bin_src.write_text("fn main() {}\n", encoding="utf-8")
        r_lld_fallback = subprocess.run(
            [
                str(rustc_nightly),
                "--sysroot",
                str(sealed_no_tools),
                "-Clinker-features=+lld",
                "-Clink-self-contained=+linker",
                "-Zunstable-options",
                str(bin_src),
                "-o",
                str(tmp / "hello_bin"),
            ],
            env=clean_env(),
            capture_output=True,
            text=True,
        )

    return {
        "at_fdcwd_symlink_sysroot_matrix": matrix,
        "sealed_sysroot_isolation_probes": {
            "empty_sealed_sysroot_core_lookup": {
                "returncode": r_core.returncode,
                "fails_closed_without_default_fallback": r_core.returncode != 0,
                "stderr_first_line": r_core.stderr.splitlines()[0]
                if r_core.stderr
                else "",
            },
            "sealed_sysroot_without_proc_macro_lookup": {
                "returncode": r_pm.returncode,
                "fails_closed_without_default_fallback": r_pm.returncode != 0,
                "stderr_first_line": r_pm.stderr.splitlines()[0]
                if r_pm.stderr
                else "",
            },
            "sealed_sysroot_without_bin_tools_rust_lld_fallback": {
                "has_bin_dir_in_sealed_sysroot": (
                    sealed_no_tools
                    / "lib"
                    / "rustlib"
                    / "x86_64-unknown-linux-gnu"
                    / "bin"
                ).exists(),
                "returncode": r_lld_fallback.returncode,
                "falls_back_to_sysroot_default_via_all_paths": (
                    r_lld_fallback.returncode == 0
                ),
                "stderr": r_lld_fallback.stderr.strip(),
            },
        },
    }


def find_patchelf(explicit: str | None) -> Path:
    if explicit:
        return Path(explicit)
    found = shutil.which("patchelf")
    if found:
        return Path(found)
    out = subprocess.check_output(
        [
            "nix",
            "--extra-experimental-features",
            "nix-command flakes",
            "build",
            "--no-link",
            "--print-out-paths",
            "nixpkgs#patchelf",
        ],
        text=True,
    ).strip()
    return Path(out) / "bin" / "patchelf"


def sanitize_output(obj: Any, rustup_dir: Path) -> Any:
    home_str = str(Path.home())
    rustup_str = str(rustup_dir.resolve())
    if isinstance(obj, str):
        s = obj
        if rustup_str and rustup_str != "/":
            s = s.replace(rustup_str, "<RUSTUP_HOME>")
        if home_str and home_str != "/":
            s = s.replace(home_str + "/.rustup", "<RUSTUP_HOME>")
            s = s.replace(home_str, "<HOME>")
        s = re.sub(r"/tmp/tmp[A-Za-z0-9_]+", "<TMPDIR>", s)
        return s
    if isinstance(obj, list):
        return [sanitize_output(x, rustup_dir) for x in obj]
    if isinstance(obj, dict):
        return {k: sanitize_output(v, rustup_dir) for k, v in obj.items()}
    return obj


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--rustup-dir",
        type=Path,
        default=Path(os.environ.get("RUSTUP_HOME", str(Path.home() / ".rustup"))),
        help="Path to rustup home directory (read-only)",
    )
    parser.add_argument(
        "--patchelf",
        type=str,
        default=None,
        help="Optional explicit path to patchelf binary",
    )
    parser.add_argument(
        "--offline",
        action="store_true",
        help="Skip fetching static.rust-lang.org channel manifests",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parent
        / "probe_loader_and_component_economics.json",
        help="Path to output JSON report",
    )
    args = parser.parse_args()

    toolchains_dir = args.rustup_dir / "toolchains"
    patchelf_bin = find_patchelf(args.patchelf)

    report = sanitize_output(
        {
            "host": {
                "os": platform.system(),
                "arch": platform.machine(),
                "kernel": sanitize_kernel_release(platform.release()),
                "python": platform.python_version(),
            },
            "probe1_glibc_rpath_and_maps_closure": run_probe1_glibc_rpath_and_maps(
                toolchains_dir, patchelf_bin
            ),
            "probe2_monorepo_abi_and_version_formats": run_probe2_monorepo_abi_and_version_formats(
                toolchains_dir
            ),
            "probe3_component_economics": run_probe3_component_economics(
                toolchains_dir, offline=args.offline
            ),
            "probe4_filesearch_and_sysroot_audit": run_probe4_filesearch_regression_and_sysroot_audit(
                toolchains_dir
            ),
        },
        args.rustup_dir,
    )

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.output} ({args.output.stat().st_size} bytes)")


if __name__ == "__main__":
    main()
