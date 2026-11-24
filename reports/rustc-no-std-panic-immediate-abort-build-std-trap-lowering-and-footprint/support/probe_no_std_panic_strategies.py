#!/usr/bin/env python3
"""Empirical probe for #![no_std] PanicStrategy::{Unwind, Abort, ImmediateAbort},
prebuilt-sysroot compatibility vs. -Zbuild-std=core trap lowering, and #[panic_handler] ABI.
"""

from __future__ import annotations

import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
from typing import Any


PKG_DIR = pathlib.Path(__file__).resolve().parent.parent
OUT_JSON = PKG_DIR / "support" / "probe_results.json"
TARGET_X86 = "x86_64-unknown-linux-gnu"
TARGET_AARCH64 = "aarch64-unknown-linux-gnu"

CORE_PROBE_LIB_RS = """#![no_std]

#[unsafe(no_mangle)]
pub extern "C" fn div(a: u32, b: u32) -> u32 {
    a / b
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn idx(s: *const u32, len: usize, i: usize) -> u32 {
    let slice = unsafe { core::slice::from_raw_parts(s, len) };
    slice[i]
}
"""

CFG_DUAL_PROBE_RS = """#![no_std]

#[unsafe(no_mangle)]
pub extern "C" fn cfg_flags_mask() -> u32 {
    let mut mask = 0u32;
    if cfg!(panic = "immediate-abort") {
        mask |= 1;
    }
    if cfg!(panic = "abort") {
        mask |= 2;
    }
    if cfg!(panic = "unwind") {
        mask |= 4;
    }
    mask
}
"""


def find_toolchain_env() -> tuple[dict[str, str], dict[str, str]]:
    env = os.environ.copy()
    cargo_bin = pathlib.Path.home() / ".cargo" / "bin"
    extra_paths = [str(cargo_bin)] if cargo_bin.is_dir() else []
    env["PATH"] = ":".join(extra_paths + [env.get("PATH", "")])

    rustc_ver = subprocess.run(
        ["rustc", "--version", "-v"], env=env, capture_output=True, text=True, check=True
    ).stdout.strip()
    sysroot = subprocess.run(
        ["rustc", "--print", "sysroot"], env=env, capture_output=True, text=True, check=True
    ).stdout.strip()
    host = None
    commit_sha = None
    llvm_ver = None
    for line in rustc_ver.splitlines():
        if line.startswith("host: "):
            host = line.split(": ", 1)[1].strip()
        elif line.startswith("commit-hash: "):
            commit_sha = line.split(": ", 1)[1].strip()
        elif line.startswith("LLVM version: "):
            llvm_ver = line.split(": ", 1)[1].strip()

    llvm_bin_dir = pathlib.Path(sysroot) / "lib" / "rustlib" / (host or TARGET_X86) / "bin"
    if llvm_bin_dir.is_dir():
        env["PATH"] = f"{llvm_bin_dir}:{env['PATH']}"

    meta = {
        "rustc_version": rustc_ver,
        "rustc_commit_sha": commit_sha or "unknown",
        "llvm_version": llvm_ver or "unknown",
        "host": host or TARGET_X86,
        "sysroot": sysroot,
    }
    return env, meta


def sanitize_text(text: str, home_dir: str, sysroot: str, tmp_dir: str) -> str:
    out = text
    if sysroot:
        out = out.replace(sysroot, "<sysroot>")
    if home_dir:
        out = out.replace(home_dir, "<home>")
    if tmp_dir:
        out = out.replace(tmp_dir, "<tmp>")
    # Normalize rustc tmp workspace hashes/prefixes if any remain
    out = re.sub(r"/tmp/tmp[a-zA-Z0-9_]+", "<tmp>", out)
    return out


def extract_llvm_functions_and_decls(ll_text: str, fn_names: tuple[str, ...]) -> dict[str, Any]:
    lines = ll_text.splitlines()
    functions: dict[str, list[str]] = {}
    resolved_attributes: dict[str, str] = {}
    attr_map: dict[str, str] = {}
    decls: list[str] = []

    for line in lines:
        m = re.match(r"^(attributes #\d+ = \{.*\})$", line)
        if m:
            key = line.split("=", 1)[0].strip().replace("attributes ", "")
            attr_map[key] = m.group(1)
        elif line.startswith("declare ") and any(
            tok in line for tok in ("panicking", "rust_eh_personality", "llvm.trap")
        ):
            decls.append(line)

    for fn in fn_names:
        start_prefix = f"define "
        sig_pat = re.compile(rf"^define\b.*@{re.escape(fn)}\(")
        captured: list[str] = []
        in_fn = False
        for line in lines:
            if not in_fn:
                if line.startswith(start_prefix) and sig_pat.match(line):
                    in_fn = True
                    captured.append(line)
                    m_attr = re.search(r"(#\d+)\b", line)
                    if m_attr and m_attr.group(1) in attr_map:
                        resolved_attributes[fn] = attr_map[m_attr.group(1)]
            else:
                captured.append(line)
                if line.strip() == "}":
                    break
        if captured:
            functions[fn] = captured

    metrics_by_fn: dict[str, dict[str, Any]] = {}
    for fn, flines in functions.items():
        body_lines = [
            l for l in flines[1:-1] if l.strip() and not l.strip().startswith(";") and not l.strip().endswith(":")
        ]
        joined = "\n".join(flines)
        metrics_by_fn[fn] = {
            "has_personality": "personality ptr" in flines[0],
            "instruction_line_count": len(body_lines),
            "call_count": len(re.findall(r"\bcall\b", joined)),
            "invoke_count": len(re.findall(r"\binvoke\b", joined)),
            "landingpad_count": len(re.findall(r"\blandingpad\b", joined)),
            "llvm_trap_count": len(re.findall(r"@llvm\.trap\(\)", joined)),
        }

    return {
        "functions": functions,
        "resolved_attributes": resolved_attributes,
        "llvm_decls": decls,
        "metrics_by_fn": metrics_by_fn,
    }


def inspect_object_file(obj_path: pathlib.Path, env: dict[str, str], home_dir: str, sysroot: str, tmp_dir: str) -> dict[str, Any]:
    nm_res = subprocess.run(
        ["llvm-nm", "-u", str(obj_path)], env=env, capture_output=True, text=True, check=True
    )
    undef_syms = [line.strip() for line in nm_res.stdout.splitlines() if line.strip()]

    size_res = subprocess.run(
        ["llvm-size", str(obj_path)], env=env, capture_output=True, text=True, check=True
    )
    size_lines = [line.strip() for line in size_res.stdout.splitlines() if line.strip()]
    section_sizes: dict[str, int] = {}
    if len(size_lines) >= 2:
        parts = size_lines[-1].split()
        if len(parts) >= 4:
            section_sizes = {
                "text_bytes": int(parts[0]),
                "data_bytes": int(parts[1]),
                "bss_bytes": int(parts[2]),
                "dec_total_bytes": int(parts[3]),
            }

    objdump_res = subprocess.run(
        ["llvm-objdump", "-d", str(obj_path)], env=env, capture_output=True, text=True, check=True
    )
    disasm = sanitize_text(objdump_res.stdout.strip(), home_dir, sysroot, tmp_dir)

    return {
        "undefined_symbols_llvm_nm": undef_syms,
        "section_sizes": section_sizes,
        "objdump_disassembly": disasm,
    }


def run_rustc_sysroot_case(
    work_dir: pathlib.Path,
    name: str,
    src_text: str,
    crate_type: str,
    extra_args: list[str],
    env: dict[str, str],
    home_dir: str,
    sysroot: str,
    fn_names: tuple[str, ...] = ("div", "idx"),
) -> dict[str, Any]:
    case_dir = work_dir / name
    case_dir.mkdir(parents=True, exist_ok=True)
    src_path = case_dir / "probe.rs"
    src_path.write_text(src_text)

    cmd = [
        "rustc",
        "--edition",
        "2024",
        "--crate-name",
        "panic_probe",
        "--crate-type",
        crate_type,
        *extra_args,
        str(src_path),
    ]
    res = subprocess.run(cmd, cwd=case_dir, env=env, capture_output=True, text=True)
    entry: dict[str, Any] = {
        "crate_type": crate_type,
        "extra_args": extra_args,
        "compile_returncode": res.returncode,
        "compile_stdout": sanitize_text(res.stdout.strip(), home_dir, sysroot, str(work_dir)),
        "compile_stderr": sanitize_text(res.stderr.strip(), home_dir, sysroot, str(work_dir)),
    }
    if res.returncode == 0 and "--emit=llvm-ir,obj" in extra_args:
        ll_files = sorted(case_dir.glob("*.ll"))
        obj_files = sorted(case_dir.glob("*.o"))
        if ll_files:
            ll_info = extract_llvm_functions_and_decls(ll_files[0].read_text(), fn_names)
            entry.update(ll_info)
        if obj_files:
            obj_info = inspect_object_file(obj_files[0], env, home_dir, sysroot, str(work_dir))
            entry.update(obj_info)
    return entry


def run_build_std_case(
    cargo_proj: pathlib.Path,
    target_dir: pathlib.Path,
    crate_type: str,
    mode: str,
    rustflags: str,
    target: str,
    profile_flag: str,
    src_text: str,
    env: dict[str, str],
    home_dir: str,
    sysroot: str,
) -> dict[str, Any]:
    (cargo_proj / "Cargo.toml").write_text(
        f'[package]\nname = "panic_probe"\nversion = "0.1.0"\nedition = "2024"\n\n[lib]\ncrate-type = ["{crate_type}"]\n'
    )
    (cargo_proj / "src" / "lib.rs").write_text(src_text)
    lock_file = cargo_proj / "Cargo.lock"
    if not lock_file.exists():
        lock_file.write_text("# This file is automatically @generated by Cargo.\nversion = 4\n")

    sub_env = env.copy()
    sub_env["RUSTFLAGS"] = rustflags
    sub_env["CARGO_TARGET_DIR"] = str(target_dir)

    cmd = [
        "cargo",
        "rustc",
        "--offline",
        "-Zbuild-std=core",
        "--target",
        target,
        profile_flag,
        "--",
        "--emit=llvm-ir,obj",
    ]
    res = subprocess.run(cmd, cwd=cargo_proj, env=sub_env, capture_output=True, text=True)
    entry: dict[str, Any] = {
        "mode": mode,
        "crate_type": crate_type,
        "target": target,
        "profile_flag": profile_flag,
        "rustflags": rustflags,
        "command": " ".join(cmd),
        "compile_returncode": res.returncode,
        "compile_stdout": sanitize_text(res.stdout.strip(), home_dir, sysroot, str(cargo_proj.parent)),
        "compile_stderr": sanitize_text(res.stderr.strip(), home_dir, sysroot, str(cargo_proj.parent)),
    }
    if res.returncode == 0:
        prof_dir = "release" if profile_flag == "--release" else "debug"
        deps_dir = target_dir / target / prof_dir / "deps"
        ll_candidates = sorted(deps_dir.glob("panic_probe*.ll"), key=lambda p: p.stat().st_mtime, reverse=True)
        obj_candidates = sorted(deps_dir.glob("panic_probe*.o"), key=lambda p: p.stat().st_mtime, reverse=True)
        if ll_candidates:
            ll_info = extract_llvm_functions_and_decls(ll_candidates[0].read_text(), ("div", "idx"))
            entry.update(ll_info)
        if obj_candidates:
            obj_info = inspect_object_file(
                obj_candidates[0], env, home_dir, sysroot, str(cargo_proj.parent)
            )
            entry.update(obj_info)
        if crate_type == "cdylib":
            so_candidates = sorted(
                (target_dir / target / prof_dir).glob("libpanic_probe*.so"),
                key=lambda p: p.stat().st_mtime,
                reverse=True,
            )
            if so_candidates:
                so_nm = subprocess.run(
                    ["llvm-nm", "-u", str(so_candidates[0])],
                    env=env,
                    capture_output=True,
                    text=True,
                    check=True,
                )
                entry["cdylib_undefined_symbols_llvm_nm"] = [
                    l.strip() for l in so_nm.stdout.splitlines() if l.strip()
                ]
                so_size = subprocess.run(
                    ["llvm-size", str(so_candidates[0])],
                    env=env,
                    capture_output=True,
                    text=True,
                    check=True,
                )
                entry["cdylib_llvm_size_raw"] = so_size.stdout.strip()
    return entry


def collect_mir_postcleanup_probe(
    work_dir: pathlib.Path, env: dict[str, str], home_dir: str, sysroot: str
) -> dict[str, Any]:
    out: dict[str, Any] = {}
    modes = {
        "unwind": ["-Copt-level=2", "-Cpanic=unwind"],
        "abort": ["-Copt-level=2", "-Cpanic=abort"],
        "immediate_abort": ["-Copt-level=2", "-Zunstable-options", "-Cpanic=immediate-abort"],
    }
    for mode, flags in modes.items():
        mdir = work_dir / f"mir_{mode}"
        dump_dir = mdir / "mir_dump"
        dump_dir.mkdir(parents=True, exist_ok=True)
        src = mdir / "probe.rs"
        src.write_text(CORE_PROBE_LIB_RS)
        cmd = [
            "rustc",
            "--edition",
            "2024",
            "--crate-name",
            "mir_probe",
            "--crate-type",
            "lib",
            *flags,
            "-Zdump-mir=all",
            f"-Zdump-mir-dir={dump_dir}",
            str(src),
        ]
        res = subprocess.run(cmd, cwd=mdir, env=env, capture_output=True, text=True)
        fn_mir: dict[str, dict[str, list[str]]] = {}
        for stage in ("runtime-post-cleanup", "runtime-optimized"):
            stage_map: dict[str, list[str]] = {}
            for mf in sorted(dump_dir.glob(f"*{stage}.after.mir")):
                for fn in ("div", "idx"):
                    if f".{fn}." in mf.name:
                        stage_map[fn] = sanitize_text(
                            mf.read_text(), home_dir, sysroot, str(work_dir)
                        ).splitlines()
            fn_mir[stage] = stage_map
        out[mode] = {
            "compile_returncode": res.returncode,
            "stages": fn_mir,
        }
    return out


def main() -> int:
    env, meta = find_toolchain_env()
    home_dir = str(pathlib.Path.home())
    sysroot = meta["sysroot"]

    with tempfile.TemporaryDirectory() as tmp:
        root = pathlib.Path(tmp)
        sysroot_dir = root / "sysroot_cases"
        sysroot_dir.mkdir()

        prebuilt_sysroot = {
            "sysroot_lib_panic_unwind": run_rustc_sysroot_case(
                sysroot_dir,
                "sysroot_lib_panic_unwind",
                CORE_PROBE_LIB_RS,
                "lib",
                ["-Copt-level=2", "--emit=llvm-ir,obj", "-Cpanic=unwind"],
                env,
                home_dir,
                sysroot,
            ),
            "sysroot_lib_panic_abort": run_rustc_sysroot_case(
                sysroot_dir,
                "sysroot_lib_panic_abort",
                CORE_PROBE_LIB_RS,
                "lib",
                ["-Copt-level=2", "--emit=llvm-ir,obj", "-Cpanic=abort"],
                env,
                home_dir,
                sysroot,
            ),
            "sysroot_lib_panic_immediate_abort_without_build_std": run_rustc_sysroot_case(
                sysroot_dir,
                "sysroot_lib_panic_immediate_abort_without_build_std",
                CORE_PROBE_LIB_RS,
                "lib",
                ["-Copt-level=2", "--emit=llvm-ir,obj", "-Zunstable-options", "-Cpanic=immediate-abort"],
                env,
                home_dir,
                sysroot,
            ),
            "sysroot_immediate_abort_requires_unstable_options": run_rustc_sysroot_case(
                sysroot_dir,
                "sysroot_immediate_abort_requires_unstable_options",
                CORE_PROBE_LIB_RS,
                "lib",
                ["-Copt-level=2", "-Cpanic=immediate-abort"],
                env,
                home_dir,
                sysroot,
            ),
            "sysroot_cdylib_immediate_abort_rejected_core_panic_strategy_mismatch": run_rustc_sysroot_case(
                sysroot_dir,
                "sysroot_cdylib_immediate_abort_rejected_core_panic_strategy_mismatch",
                CORE_PROBE_LIB_RS,
                "cdylib",
                ["-Copt-level=2", "-Zunstable-options", "-Cpanic=immediate-abort"],
                env,
                home_dir,
                sysroot,
            ),
            "sysroot_cdylib_immediate_abort_with_panic_handler_also_rejected": run_rustc_sysroot_case(
                sysroot_dir,
                "sysroot_cdylib_immediate_abort_with_panic_handler_also_rejected",
                CORE_PROBE_LIB_RS
                + "\n#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! {\n    loop {}\n}\n",
                "cdylib",
                ["-Copt-level=2", "-Zunstable-options", "-Cpanic=immediate-abort"],
                env,
                home_dir,
                sysroot,
            ),
            "sysroot_lib_cfg_panic_immediate_abort_dual_cfg": run_rustc_sysroot_case(
                sysroot_dir,
                "sysroot_lib_cfg_panic_immediate_abort_dual_cfg",
                CFG_DUAL_PROBE_RS,
                "lib",
                ["-Copt-level=2", "--emit=llvm-ir,obj", "-Zunstable-options", "-Cpanic=immediate-abort"],
                env,
                home_dir,
                sysroot,
                fn_names=("cfg_flags_mask",),
            ),
        }

        mir_postcleanup = collect_mir_postcleanup_probe(root, env, home_dir, sysroot)

        cargo_proj = root / "cargo_proj"
        (cargo_proj / "src").mkdir(parents=True)
        shared_target_dir = root / "cargo_target"

        rebuild_core_via_build_std = {
            "build_std_core_lib_panic_unwind": run_build_std_case(
                cargo_proj,
                shared_target_dir,
                "lib",
                "unwind",
                "-Cpanic=unwind",
                TARGET_X86,
                "--release",
                CORE_PROBE_LIB_RS,
                env,
                home_dir,
                sysroot,
            ),
            "build_std_core_lib_panic_abort": run_build_std_case(
                cargo_proj,
                shared_target_dir,
                "lib",
                "abort",
                "-Cpanic=abort",
                TARGET_X86,
                "--release",
                CORE_PROBE_LIB_RS,
                env,
                home_dir,
                sysroot,
            ),
            "build_std_core_lib_panic_immediate_abort": run_build_std_case(
                cargo_proj,
                shared_target_dir,
                "lib",
                "immediate-abort",
                "-Zunstable-options -Cpanic=immediate-abort",
                TARGET_X86,
                "--release",
                CORE_PROBE_LIB_RS,
                env,
                home_dir,
                sysroot,
            ),
            "build_std_core_cdylib_immediate_abort_no_panic_handler_ok": run_build_std_case(
                cargo_proj,
                shared_target_dir,
                "cdylib",
                "immediate-abort-cdylib-no-handler",
                "-Zunstable-options -Cpanic=immediate-abort",
                TARGET_X86,
                "--release",
                CORE_PROBE_LIB_RS,
                env,
                home_dir,
                sysroot,
            ),
            "build_std_core_lib_immediate_abort_opt0": run_build_std_case(
                cargo_proj,
                shared_target_dir,
                "lib",
                "immediate-abort-opt0",
                "-Zunstable-options -Cpanic=immediate-abort",
                TARGET_X86,
                "--profile=dev",
                CORE_PROBE_LIB_RS,
                env,
                home_dir,
                sysroot,
            ),
            "build_std_core_cdylib_immediate_abort_opt0_no_handler_ok": run_build_std_case(
                cargo_proj,
                shared_target_dir,
                "cdylib",
                "immediate-abort-cdylib-opt0-no-handler",
                "-Zunstable-options -Cpanic=immediate-abort",
                TARGET_X86,
                "--profile=dev",
                CORE_PROBE_LIB_RS,
                env,
                home_dir,
                sysroot,
            ),
            "build_std_core_lib_panic_immediate_abort_aarch64": run_build_std_case(
                cargo_proj,
                shared_target_dir,
                "lib",
                "immediate-abort-aarch64",
                "-Zunstable-options -Cpanic=immediate-abort",
                TARGET_AARCH64,
                "--release",
                CORE_PROBE_LIB_RS,
                env,
                home_dir,
                sysroot,
            ),
        }

        ph_dir = root / "panic_handler_cases"
        ph_dir.mkdir()
        panic_handler_abi = {
            "valid_panic_handler_never_return_cdylib_ok": run_rustc_sysroot_case(
                ph_dir,
                "valid_panic_handler_never_return_cdylib_ok",
                CORE_PROBE_LIB_RS
                + "\n#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! {\n    loop {}\n}\n",
                "cdylib",
                ["-Copt-level=2", "-Cpanic=abort"],
                env,
                home_dir,
                sysroot,
            ),
            "invalid_panic_handler_unit_return_rejected_e0308": run_rustc_sysroot_case(
                ph_dir,
                "invalid_panic_handler_unit_return_rejected_e0308",
                "#![no_std]\n\n#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> () {}\n",
                "lib",
                [],
                env,
                home_dir,
                sysroot,
            ),
            "missing_panic_handler_cdylib_panic_abort_rejected": run_rustc_sysroot_case(
                ph_dir,
                "missing_panic_handler_cdylib_panic_abort_rejected",
                CORE_PROBE_LIB_RS,
                "cdylib",
                ["-Copt-level=2", "-Cpanic=abort"],
                env,
                home_dir,
                sysroot,
            ),
            "missing_panic_handler_cdylib_panic_unwind_rejected": run_rustc_sysroot_case(
                ph_dir,
                "missing_panic_handler_cdylib_panic_unwind_rejected",
                CORE_PROBE_LIB_RS,
                "cdylib",
                ["-Copt-level=2", "-Cpanic=unwind"],
                env,
                home_dir,
                sysroot,
            ),
            "missing_panic_handler_rlib_panic_abort_ok": run_rustc_sysroot_case(
                ph_dir,
                "missing_panic_handler_rlib_panic_abort_ok",
                CORE_PROBE_LIB_RS,
                "rlib",
                ["-Copt-level=2", "-Cpanic=abort"],
                env,
                home_dir,
                sysroot,
            ),
        }

    results = {
        "rustc_version": sanitize_text(meta["rustc_version"], home_dir, sysroot, ""),
        "rustc_commit_sha": meta["rustc_commit_sha"],
        "llvm_version": meta["llvm_version"],
        "host": meta["host"],
        "experiments": {
            "a_codegen_and_footprint_prebuilt_sysroot_vs_build_std_core": {
                "prebuilt_sysroot": prebuilt_sysroot,
                "mir_post_cleanup": mir_postcleanup,
                "rebuild_core_via_build_std": rebuild_core_via_build_std,
            },
            "b_no_std_panic_handler_abi_and_omission": panic_handler_abi,
        },
    }

    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.write_text(json.dumps(results, indent=2) + "\n")
    print(f"Wrote {OUT_JSON} ({OUT_JSON.stat().st_size} bytes)")

    expected_ok = [
        ("prebuilt_sysroot", "sysroot_lib_panic_unwind"),
        ("prebuilt_sysroot", "sysroot_lib_panic_abort"),
        ("prebuilt_sysroot", "sysroot_lib_panic_immediate_abort_without_build_std"),
        ("prebuilt_sysroot", "sysroot_lib_cfg_panic_immediate_abort_dual_cfg"),
        ("rebuild_core_via_build_std", "build_std_core_lib_panic_unwind"),
        ("rebuild_core_via_build_std", "build_std_core_lib_panic_abort"),
        ("rebuild_core_via_build_std", "build_std_core_lib_panic_immediate_abort"),
        ("rebuild_core_via_build_std", "build_std_core_cdylib_immediate_abort_no_panic_handler_ok"),
        ("rebuild_core_via_build_std", "build_std_core_lib_immediate_abort_opt0"),
        ("rebuild_core_via_build_std", "build_std_core_cdylib_immediate_abort_opt0_no_handler_ok"),
        ("rebuild_core_via_build_std", "build_std_core_lib_panic_immediate_abort_aarch64"),
    ]
    for grp, key in expected_ok:
        rc = results["experiments"]["a_codegen_and_footprint_prebuilt_sysroot_vs_build_std_core"][grp][key]["compile_returncode"]
        assert rc == 0, f"Expected rc=0 for {grp}.{key}, got {rc}"
    assert results["experiments"]["b_no_std_panic_handler_abi_and_omission"]["valid_panic_handler_never_return_cdylib_ok"]["compile_returncode"] == 0
    assert results["experiments"]["b_no_std_panic_handler_abi_and_omission"]["missing_panic_handler_rlib_panic_abort_ok"]["compile_returncode"] == 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
