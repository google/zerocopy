#!/usr/bin/env python3
"""Reproducible empirical probe for:
1. `static` address identity vs. promoted `const` `unnamed_addr` LLVM IR & ELF sections
2. Cyclic static value `E0391` vs. cyclic static address-of (`reserve_and_set_static_alloc`)
3. `#[thread_local]` ELF `.tdata`/`.tbss`, `-Z tls-model` lowering, `@llvm.threadlocal.address.p0`,
   and multi-threaded TLS memory isolation.

Runs strictly inside `with tempfile.TemporaryDirectory():` and sanitizes temp paths.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


SLUG = "rustc-static-address-identity-cyclic-refs-unnamed-addr-and-thread-local-tls"

STATIC_VS_CONST_LIB_RS = r"""
use std::hint::black_box;

#[unsafe(no_mangle)]
pub static S: u64 = 123;

#[unsafe(no_mangle)]
pub static S_DUP_1: u64 = 0x1122334455667788;

#[unsafe(no_mangle)]
pub static S_DUP_2: u64 = 0x1122334455667788;

static S_PRIV_1: u64 = 0xAABBCCDDEEFF0011;
static S_PRIV_2: u64 = 0xAABBCCDDEEFF0011;

pub const C: &[u64] = &[1u64, 2];
pub const C_DUP: &[u64] = &[1u64, 2];

#[unsafe(no_mangle)]
pub extern "C" fn get_const_ptr() -> *const u64 {
    C.as_ptr()
}

#[unsafe(no_mangle)]
pub extern "C" fn get_const_dup_ptr() -> *const u64 {
    C_DUP.as_ptr()
}

#[unsafe(no_mangle)]
pub extern "C" fn get_promoted_ptr() -> *const u64 {
    (&[1u64, 2]).as_ptr()
}

#[unsafe(no_mangle)]
pub extern "C" fn get_s_ptr() -> *const u64 {
    &raw const S
}

#[unsafe(no_mangle)]
pub extern "C" fn get_priv_statics_eq() -> bool {
    black_box(&raw const S_PRIV_1) == black_box(&raw const S_PRIV_2)
}
""".lstrip()

STATIC_VS_CONST_BIN_RS = r"""
use std::hint::black_box;

#[unsafe(no_mangle)]
pub static S: u64 = 123;
#[unsafe(no_mangle)]
pub static S_DUP_1: u64 = 0x1122334455667788;
#[unsafe(no_mangle)]
pub static S_DUP_2: u64 = 0x1122334455667788;

static S_PRIV_1: u64 = 0xAABBCCDDEEFF0011;
static S_PRIV_2: u64 = 0xAABBCCDDEEFF0011;

pub const C: &[u64] = &[1u64, 2];
pub const C_DUP: &[u64] = &[1u64, 2];

#[inline(never)]
fn get_s_ptr() -> *const u64 {
    black_box(&raw const S)
}

fn main() {
    let static_addr_eq = black_box(&raw const S) == get_s_ptr();
    let static_dup_eq = black_box(&raw const S_DUP_1) == black_box(&raw const S_DUP_2);
    let static_priv_dup_eq = black_box(&raw const S_PRIV_1) == black_box(&raw const S_PRIV_2);
    let const_eq_promoted = black_box(C.as_ptr()) == black_box((&[1u64, 2]).as_ptr());
    let const_eq_dup = black_box(C.as_ptr()) == black_box(C_DUP.as_ptr());
    println!(
        "STATIC_ADDR_EQ={} STATIC_DUP_EQ={} STATIC_PRIV_DUP_EQ={} CONST_EQ_PROMOTED={} CONST_EQ_DUP={}",
        static_addr_eq, static_dup_eq, static_priv_dup_eq, const_eq_promoted, const_eq_dup
    );
}
""".lstrip()

CYC_VAL_RS = r"""
static A: u32 = B;
static B: u32 = A;
fn main() {
    println!("{}", A);
}
""".lstrip()

CYC_SELF_VAL_RS = r"""
static A: u32 = A;
fn main() {
    println!("{}", A);
}
""".lstrip()

CYC_CONST_REF_RS = r"""
struct Node(u32, &'static Node);
const A: Node = Node(10, &B);
const B: Node = Node(20, &A);
fn main() {
    println!("{}", A.0);
}
""".lstrip()

CYC_REF_RS = r"""
struct Node(u32, &'static Node);
static A: Node = Node(10, &B);
static B: Node = Node(20, &A);
static SELF_NODE: Node = Node(42, &SELF_NODE);

fn main() {
    println!(
        "CYC_REF_OK={},{} ROUNDTRIP={},{} SELF_CYCLE_EQ={} AB_DISTINCT={}",
        A.0,
        A.1.0,
        A.1.1.0,
        B.1.1.0,
        core::ptr::eq(&raw const SELF_NODE, SELF_NODE.1 as *const Node),
        !core::ptr::eq(&raw const A, &raw const B),
    );
}
""".lstrip()

TLS_PROBE_BIN_RS = r"""
#![feature(thread_local)]

use std::cell::Cell;
use std::hint::black_box;
use std::thread;

#[unsafe(no_mangle)]
static S_GLOBAL: u64 = 123;

#[unsafe(no_mangle)]
#[thread_local]
static TLS_NONZERO: Cell<u64> = Cell::new(7);

#[unsafe(no_mangle)]
#[thread_local]
static TLS_ZERO: Cell<u64> = Cell::new(0);

#[unsafe(no_mangle)]
#[thread_local]
static TLS_FREEZE_ZERO: u64 = 0;

pub const C_SLICE: &[u64] = &[1u64, 2];

#[inline(never)]
fn get_s_ptr() -> *const u64 {
    black_box(&raw const S_GLOBAL)
}

#[inline(never)]
fn read_tls_nonzero() -> u64 {
    TLS_NONZERO.get()
}

#[inline(never)]
fn read_tls_zero() -> u64 {
    TLS_ZERO.get()
}

#[inline(never)]
fn read_tls_freeze_zero() -> u64 {
    black_box(TLS_FREEZE_ZERO)
}

fn main() {
    let static_addr_eq = black_box(&raw const S_GLOBAL) == get_s_ptr();
    let const_eq_promoted = black_box(C_SLICE.as_ptr()) == black_box((&[1u64, 2]).as_ptr());

    let main_ptr = TLS_NONZERO.as_ptr() as usize;
    let init_main_nz = read_tls_nonzero();
    let init_main_z = read_tls_zero();
    let init_main_fz = read_tls_freeze_zero();
    assert_eq!(init_main_nz, 7);
    assert_eq!(init_main_z, 0);
    assert_eq!(init_main_fz, 0);

    let (child_nz, child_z, child_ptr) = thread::spawn(|| {
        assert_eq!(read_tls_nonzero(), 7);
        assert_eq!(read_tls_zero(), 0);
        TLS_NONZERO.set(99);
        TLS_ZERO.set(123);
        (read_tls_nonzero(), read_tls_zero(), TLS_NONZERO.as_ptr() as usize)
    })
    .join()
    .expect("child thread panicked");

    let after_main_nz = read_tls_nonzero();
    let after_main_z = read_tls_zero();
    println!(
        "STATIC_ADDR_EQ={} CONST_EQ_PROMOTED={} TLS_MAIN={} TLS_CHILD={} TLS_ZERO_MAIN={} TLS_ZERO_CHILD={} TLS_PTR_DISTINCT={}",
        static_addr_eq,
        const_eq_promoted,
        after_main_nz,
        child_nz,
        after_main_z,
        child_z,
        main_ptr != child_ptr
    );
}
""".lstrip()

TLS_PROBE_CDYLIB_RS = r"""
#![feature(thread_local)]

use std::cell::Cell;

#[unsafe(no_mangle)]
#[thread_local]
pub static TLS_NONZERO: Cell<u64> = Cell::new(7);

#[unsafe(no_mangle)]
#[thread_local]
pub static TLS_ZERO: Cell<u64> = Cell::new(0);

#[unsafe(no_mangle)]
#[thread_local]
pub static TLS_FREEZE_ZERO: u64 = 0;

#[unsafe(no_mangle)]
pub extern "C" fn touch_tls(delta: u64) -> u64 {
    let prev = TLS_NONZERO.get();
    TLS_NONZERO.set(prev.wrapping_add(delta));
    let z = TLS_ZERO.get();
    TLS_ZERO.set(z.wrapping_add(1));
    TLS_NONZERO.get().wrapping_add(TLS_ZERO.get()).wrapping_add(TLS_FREEZE_ZERO)
}
""".lstrip()


def build_env() -> dict[str, str]:
    env = os.environ.copy()
    home = Path.home()
    extra_bins = [
        str(home / ".cargo" / "bin"),
        str(
            home
            / ".rustup"
            / "toolchains"
            / "nightly-2026-06-01-x86_64-unknown-linux-gnu"
            / "lib"
            / "rustlib"
            / "x86_64-unknown-linux-gnu"
            / "bin"
        ),
    ]
    env["PATH"] = ":".join(extra_bins + [env.get("PATH", "")])
    return env


def sanitize_text(text: str, tmp_dir: str) -> str:
    home = str(Path.home())
    user = Path.home().name
    out = text.replace(tmp_dir, "<tmp>")
    out = out.replace(home, "<home>")
    out = out.replace(user, "<user>")
    return out


def run_cmd(cmd: list[str], env: dict[str, str], cwd: Path, tmp_dir: str) -> dict[str, object]:
    proc = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, check=False)
    return {
        "cmd": [sanitize_text(c, tmp_dir) for c in cmd],
        "returncode": proc.returncode,
        "stdout": sanitize_text(proc.stdout, tmp_dir),
        "stderr": sanitize_text(proc.stderr, tmp_dir),
    }


def extract_llvm_ir_summary(ll_text: str, tmp_dir: str = "") -> dict[str, object]:
    globals_lines: list[str] = []
    fn_sigs: list[str] = []
    tls_calls: list[str] = []
    tls_decls: list[str] = []
    for raw in ll_text.splitlines():
        line = sanitize_text(raw.strip(), tmp_dir)
        if line.startswith("@") and " = " in line:
            if ".rustup" in line or "/rustc/" in line or "core::panicking" in line:
                continue
            if any(
                tok in line
                for tok in (
                    "@S ",
                    "@S_DUP_",
                    "@S_PRIV_",
                    "@S_GLOBAL",
                    "@TLS_",
                    "8S_PRIV_",
                    "@get_const",
                    "@get_promoted",
                    "@alloc_011d",
                    "\\01\\00\\00\\00\\00\\00\\00\\00\\02\\00",
                    "thread_local",
                )
            ):
                globals_lines.append(line)
        elif line.startswith("define ") and any(
            fn in line
            for fn in (
                "get_const",
                "get_promoted",
                "get_s_ptr",
                "get_priv_statics_eq",
                "touch_tls",
                "read_tls",
            )
        ):
            fn_sigs.append(line)
        elif "llvm.threadlocal.address" in line:
            if line.startswith("declare "):
                tls_decls.append(line)
            else:
                tls_calls.append(line)
    return {
        "global_declarations": globals_lines,
        "fn_signatures": fn_sigs,
        "tls_intrinsic_calls": tls_calls,
        "tls_intrinsic_decls": tls_decls,
    }


def extract_readelf_sections(readelf_out: str) -> list[str]:
    matched: list[str] = []
    for line in readelf_out.splitlines():
        if any(
            tok in line
            for tok in (
                ".tdata",
                ".tbss",
                ".rodata",
                ".data.rel.ro",
            )
        ):
            matched.append(line.strip())
    return matched


def extract_tls_relocs(readelf_r_out: str) -> list[str]:
    matched: list[str] = []
    for line in readelf_r_out.splitlines():
        if any(tok in line for tok in ("TLS", "TPOFF", "tls_get_addr")):
            matched.append(line.strip())
    return matched


def extract_pt_tls_segments(readelf_l_out: str) -> list[str]:
    matched: list[str] = []
    for line in readelf_l_out.splitlines():
        if "TLS" in line:
            matched.append(line.strip())
    return matched


def main() -> int:
    env = build_env()
    rustc = shutil.which("rustc", path=env["PATH"])
    readelf = shutil.which("readelf", path=env["PATH"])
    llvm_objdump = shutil.which("llvm-objdump", path=env["PATH"])
    if not rustc or not readelf:
        print("error: missing rustc or readelf", file=sys.stderr)
        return 1

    ver_res = subprocess.run([rustc, "--version", "--verbose"], env=env, capture_output=True, text=True, check=True)
    readelf_ver = subprocess.run([readelf, "--version"], env=env, capture_output=True, text=True, check=True)

    results: dict[str, object] = {
        "rustc_version_verbose": ver_res.stdout.strip(),
        "readelf_version": readelf_ver.stdout.splitlines()[0].strip(),
        "experiments": {},
    }

    with tempfile.TemporaryDirectory(prefix="rustc_static_tls_probe_") as tmp_raw:
        tmp = Path(tmp_raw)
        tmp_str = str(tmp)

        # --- Experiment A1: static address identity vs promoted const unnamed_addr ---
        lib_src = tmp / "static_vs_const_lib.rs"
        lib_src.write_text(STATIC_VS_CONST_LIB_RS, encoding="utf-8")
        bin_src = tmp / "static_vs_const_bin.rs"
        bin_src.write_text(STATIC_VS_CONST_BIN_RS, encoding="utf-8")

        a1_ir: dict[str, object] = {}
        for opt in ("0", "2"):
            stem = tmp / f"svc_lib_O{opt}"
            ir_res = run_cmd(
                [
                    rustc,
                    "--edition=2024",
                    "--crate-type=lib",
                    f"-Copt-level={opt}",
                    "--emit=llvm-ir,obj",
                    "-o",
                    str(stem),
                    str(lib_src),
                ],
                env,
                tmp,
                tmp_str,
            )
            ll_files = list(tmp.glob(f"svc_lib_O{opt}*.ll"))
            o_files = list(tmp.glob(f"svc_lib_O{opt}*.o"))
            ll_summary = extract_llvm_ir_summary(ll_files[0].read_text(encoding="utf-8"), tmp_str) if ll_files else {}
            sections = []
            if o_files:
                sec_proc = run_cmd([readelf, "-S", "-W", str(o_files[0])], env, tmp, tmp_str)
                sections = extract_readelf_sections(str(sec_proc["stdout"]))

            bin_exe = tmp / f"svc_bin_O{opt}"
            bin_build = run_cmd(
                [
                    rustc,
                    "--edition=2024",
                    "--crate-type=bin",
                    f"-Copt-level={opt}",
                    "-o",
                    str(bin_exe),
                    str(bin_src),
                ],
                env,
                tmp,
                tmp_str,
            )
            bin_run = run_cmd([str(bin_exe)], env, tmp, tmp_str)
            a1_ir[f"opt_level_{opt}"] = {
                "lib_compile_returncode": ir_res["returncode"],
                "llvm_ir_summary": ll_summary,
                "readelf_rodata_sections": sections,
                "bin_compile_returncode": bin_build["returncode"],
                "bin_run_returncode": bin_run["returncode"],
                "bin_run_stdout": str(bin_run["stdout"]).strip(),
            }

        # --- Experiment A2: Cyclic value E0391 vs cyclic address-of lazy alloc ---
        cyc_val_src = tmp / "cyc_val.rs"
        cyc_val_src.write_text(CYC_VAL_RS, encoding="utf-8")
        cyc_val_res = run_cmd(
            [rustc, "--edition=2024", str(cyc_val_src), "-o", str(tmp / "cyc_val_bin")],
            env,
            tmp,
            tmp_str,
        )

        cyc_self_src = tmp / "cyc_self_val.rs"
        cyc_self_src.write_text(CYC_SELF_VAL_RS, encoding="utf-8")
        cyc_self_res = run_cmd(
            [rustc, "--edition=2024", str(cyc_self_src), "-o", str(tmp / "cyc_self_bin")],
            env,
            tmp,
            tmp_str,
        )

        cyc_const_src = tmp / "cyc_const_ref.rs"
        cyc_const_src.write_text(CYC_CONST_REF_RS, encoding="utf-8")
        cyc_const_res = run_cmd(
            [rustc, "--edition=2024", str(cyc_const_src), "-o", str(tmp / "cyc_const_bin")],
            env,
            tmp,
            tmp_str,
        )

        cyc_ref_src = tmp / "cyc_ref.rs"
        cyc_ref_src.write_text(CYC_REF_RS, encoding="utf-8")
        cyc_ref_exe = tmp / "cyc_ref_bin"
        cyc_ref_compile = run_cmd(
            [rustc, "--edition=2024", str(cyc_ref_src), "-o", str(cyc_ref_exe)],
            env,
            tmp,
            tmp_str,
        )
        cyc_ref_run = run_cmd([str(cyc_ref_exe)], env, tmp, tmp_str)
        cyc_ref_mir = run_cmd(
            [rustc, "--edition=2024", "-Zunpretty=mir", str(cyc_ref_src)],
            env,
            tmp,
            tmp_str,
        )
        cyc_ref_ir = run_cmd(
            [
                rustc,
                "--edition=2024",
                "-Copt-level=0",
                "--emit=llvm-ir",
                "-o",
                str(tmp / "cyc_ref.ll"),
                str(cyc_ref_src),
            ],
            env,
            tmp,
            tmp_str,
        )
        cyc_ref_ir_globals = []
        if (tmp / "cyc_ref.ll").is_file():
            for line in (tmp / "cyc_ref.ll").read_text(encoding="utf-8").splitlines():
                if line.startswith("@") and any(k in line for k in ("cyc_ref1A", "cyc_ref1B", "SELF_NODE")):
                    if "global" in line or "constant" in line:
                        cyc_ref_ir_globals.append(sanitize_text(line.strip(), tmp_str))

        opt_bin = shutil.which("opt", path=env["PATH"])
        constmerge_ablation: dict[str, object] = {}
        if opt_bin:
            def run_cm(name: str, lines: list[str]) -> dict[str, object]:
                p = tmp / f"{name}.ll"
                p.write_text("\n".join(lines) + "\n", encoding="utf-8")
                res = run_cmd([opt_bin, "-passes=constmerge", "-S", str(p)], env, tmp, tmp_str)
                out_lines = [
                    ln.strip()
                    for ln in str(res["stdout"]).splitlines()
                    if ln.startswith("@") or "icmp eq ptr" in ln
                ]
                return {"opt_returncode": res["returncode"], "post_constmerge_lines": out_lines}

            cm_ua = run_cm(
                "cm_ua_only",
                [
                    '@UA_1 = private unnamed_addr constant [8 x i8] c"ABCDEFGH", align 8',
                    '@UA_2 = private unnamed_addr constant [8 x i8] c"ABCDEFGH", align 8',
                    "define i1 @cmp_ua() { %eq = icmp eq ptr @UA_1, @UA_2\n  ret i1 %eq }",
                ],
            )
            cm_st = run_cm(
                "cm_st_only",
                [
                    '@ST_1 = private constant [8 x i8] c"ABCDEFGH", align 8',
                    '@ST_2 = private constant [8 x i8] c"ABCDEFGH", align 8',
                    "define i1 @cmp_st() { %eq = icmp eq ptr @ST_1, @ST_2\n  ret i1 %eq }",
                ],
            )
            cm_mixed = run_cm(
                "cm_mixed",
                [
                    '@UA_1 = private unnamed_addr constant [8 x i8] c"ABCDEFGH", align 8',
                    '@UA_2 = private unnamed_addr constant [8 x i8] c"ABCDEFGH", align 8',
                    '@ST_1 = private constant [8 x i8] c"ABCDEFGH", align 8',
                    '@ST_2 = private constant [8 x i8] c"ABCDEFGH", align 8',
                    "define i1 @cmp_ua() { %eq = icmp eq ptr @UA_1, @UA_2\n  ret i1 %eq }",
                    "define i1 @cmp_st() { %eq = icmp eq ptr @ST_1, @ST_2\n  ret i1 %eq }",
                ],
            )
            constmerge_ablation = {
                "unnamed_addr_pair": {
                    **cm_ua,
                    "merged_to_single": sum(1 for ln in cm_ua["post_constmerge_lines"] if ln.startswith("@UA_")) == 1,
                },
                "non_unnamed_addr_pair": {
                    **cm_st,
                    "preserved_distinct": sum(1 for ln in cm_st["post_constmerge_lines"] if ln.startswith("@ST_")) == 2,
                },
                "mixed_unnamed_and_static": {
                    **cm_mixed,
                    "total_surviving_globals": sum(1 for ln in cm_mixed["post_constmerge_lines"] if ln.startswith("@")),
                },
            }

        results["experiments"]["a_const_static_address_and_cycles"] = {
            "llvm_ir_static_vs_promoted_unnamed_addr": a1_ir,
            "llvm_constmerge_ablation": constmerge_ablation,
            "cyclic_static_value_e0391": {
                "compile_returncode": cyc_val_res["returncode"],
                "compile_stderr": cyc_val_res["stderr"],
            },
            "cyclic_static_self_value": {
                "compile_returncode": cyc_self_res["returncode"],
                "compile_stderr": cyc_self_res["stderr"],
            },
            "cyclic_const_ref_e0391": {
                "compile_returncode": cyc_const_res["returncode"],
                "compile_stderr": cyc_const_res["stderr"],
            },
            "cyclic_static_address_of_lazy_alloc": {
                "compile_returncode": cyc_ref_compile["returncode"],
                "compile_stderr": cyc_ref_compile["stderr"],
                "run_returncode": cyc_ref_run["returncode"],
                "run_stdout": str(cyc_ref_run["stdout"]).strip(),
                "llvm_ir_static_cycle_globals": cyc_ref_ir_globals[:12],
                "mir_excerpt_lines": [
                    ln for ln in str(cyc_ref_mir["stdout"]).splitlines() if "static " in ln or "alloc" in ln or "A:" in ln or "B:" in ln or "SELF_NODE" in ln
                ][:30],
            },
        }

        # --- Experiment B: #[thread_local] TLS models, ELF .tdata/.tbss, and multithreading ---
        tls_bin_src = tmp / "tls_probe_bin.rs"
        tls_bin_src.write_text(TLS_PROBE_BIN_RS, encoding="utf-8")
        tls_cdylib_src = tmp / "tls_probe_cdylib.rs"
        tls_cdylib_src.write_text(TLS_PROBE_CDYLIB_RS, encoding="utf-8")

        tls_bin_results: dict[str, object] = {}
        tls_cdylib_results: dict[str, object] = {}

        for model in ("local-exec", "initial-exec", "global-dynamic", "local-dynamic"):
            m_tag = model.replace("-", "_")
            # 1) PIE binary: IR + obj (sections/relocs) + linked exe (run + PT_TLS)
            ir_obj_stem = tmp / f"tls_bin_{m_tag}"
            bin_ir_obj = run_cmd(
                [
                    rustc,
                    "--edition=2024",
                    "--crate-type=bin",
                    "-Copt-level=2",
                    f"-Ztls-model={model}",
                    "--emit=llvm-ir,obj",
                    "-o",
                    str(ir_obj_stem),
                    str(tls_bin_src),
                ],
                env,
                tmp,
                tmp_str,
            )
            ll_path = tmp / f"tls_bin_{m_tag}.ll"
            obj_path = tmp / f"tls_bin_{m_tag}.o"
            ll_summary = extract_llvm_ir_summary(ll_path.read_text(encoding="utf-8"), tmp_str) if ll_path.is_file() else {}
            sec_out = (
                run_cmd([readelf, "-S", "-W", str(obj_path)], env, tmp, tmp_str)["stdout"]
                if obj_path.is_file()
                else ""
            )
            rel_out = (
                run_cmd([readelf, "-r", "-W", str(obj_path)], env, tmp, tmp_str)["stdout"]
                if obj_path.is_file()
                else ""
            )

            bin_exe = tmp / f"tls_exe_{m_tag}"
            bin_link = run_cmd(
                [
                    rustc,
                    "--edition=2024",
                    "--crate-type=bin",
                    "-Copt-level=2",
                    f"-Ztls-model={model}",
                    "-o",
                    str(bin_exe),
                    str(tls_bin_src),
                ],
                env,
                tmp,
                tmp_str,
            )
            bin_run = (
                run_cmd([str(bin_exe)], env, tmp, tmp_str)
                if bin_link["returncode"] == 0
                else {"returncode": -1, "stdout": "", "stderr": ""}
            )
            pt_tls = (
                extract_pt_tls_segments(
                    str(run_cmd([readelf, "-l", "-W", str(bin_exe)], env, tmp, tmp_str)["stdout"])
                )
                if bin_link["returncode"] == 0
                else []
            )
            tls_bin_results[model] = {
                "ir_obj_compile_returncode": bin_ir_obj["returncode"],
                "link_returncode": bin_link["returncode"],
                "llvm_ir_summary": ll_summary,
                "readelf_obj_tls_sections": extract_readelf_sections(str(sec_out)),
                "readelf_obj_tls_relocs": extract_tls_relocs(str(rel_out)),
                "readelf_bin_pt_tls": pt_tls,
                "run_returncode": bin_run["returncode"],
                "run_stdout": str(bin_run["stdout"]).strip(),
            }

            # 2) cdylib: IR + obj (pre-link) + shared library link test
            cdy_stem = tmp / f"tls_cdy_{m_tag}"
            cdy_ir_obj = run_cmd(
                [
                    rustc,
                    "--edition=2024",
                    "--crate-type=cdylib",
                    "-Copt-level=2",
                    f"-Ztls-model={model}",
                    "--emit=llvm-ir,obj",
                    "-o",
                    str(cdy_stem),
                    str(tls_cdylib_src),
                ],
                env,
                tmp,
                tmp_str,
            )
            cdy_ll = tmp / f"tls_cdy_{m_tag}.ll"
            cdy_obj = tmp / f"tls_cdy_{m_tag}.o"
            cdy_ll_sum = extract_llvm_ir_summary(cdy_ll.read_text(encoding="utf-8"), tmp_str) if cdy_ll.is_file() else {}
            cdy_sec = (
                run_cmd([readelf, "-S", "-W", str(cdy_obj)], env, tmp, tmp_str)["stdout"]
                if cdy_obj.is_file()
                else ""
            )
            cdy_rel = (
                run_cmd([readelf, "-r", "-W", str(cdy_obj)], env, tmp, tmp_str)["stdout"]
                if cdy_obj.is_file()
                else ""
            )
            cdy_disasm = (
                run_cmd([llvm_objdump, "-d", "-r", str(cdy_obj)], env, tmp, tmp_str)["stdout"]
                if (llvm_objdump and cdy_obj.is_file())
                else ""
            )
            cdy_so = tmp / f"libtls_cdy_{m_tag}.so"
            cdy_link = run_cmd(
                [
                    rustc,
                    "--edition=2024",
                    "--crate-type=cdylib",
                    "-Copt-level=2",
                    f"-Ztls-model={model}",
                    "-o",
                    str(cdy_so),
                    str(tls_cdylib_src),
                ],
                env,
                tmp,
                tmp_str,
            )
            tls_cdylib_results[model] = {
                "ir_obj_compile_returncode": cdy_ir_obj["returncode"],
                "llvm_ir_summary": cdy_ll_sum,
                "readelf_obj_tls_sections": extract_readelf_sections(str(cdy_sec)),
                "readelf_obj_tls_relocs": extract_tls_relocs(str(cdy_rel)),
                "objdump_disasm_excerpt": [
                    ln.strip() for ln in str(cdy_disasm).splitlines() if ln.strip()
                ][:35],
                "cdylib_link_returncode": cdy_link["returncode"],
                "cdylib_link_stderr_head": str(cdy_link["stderr"]).strip()[:600],
            }

        results["experiments"]["b_thread_local_tls_models_and_elf_sections"] = {
            "pie_executable": tls_bin_results,
            "cdylib_shared_object": tls_cdylib_results,
        }

    out_path = Path(__file__).resolve().parent / "probe_results.json"
    out_text = json.dumps(results, indent=2) + "\n"
    # Verify no workspace/host leaks without hardcoding environment strings verbatim.
    home_str = str(Path.home())
    if home_str in out_text or any(tok in out_text for tok in (os.environ.get("USER", ""), os.uname().nodename)):
        raise RuntimeError("sanitization leak detected in probe output")
    out_path.write_text(out_text, encoding="utf-8")
    print(f"Wrote {out_path} ({len(out_text)} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
