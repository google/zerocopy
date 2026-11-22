#!/usr/bin/env python3
"""Empirical probe for rustc MIR UB-check passes, LTO CFI vs. KCFI arity,
ASan/TSan/MSan/LSan instrumentation, #[sanitize(...)] attributes, and
-Z sanitizer-ignorelist blame resolution.

All subprocesses execute the real `rustc` and `miri` binaries available on PATH
(or overridden via RUSTC / CARGO env vars) inside temporary directories that are
cleaned up automatically. All temporary/host paths are scrubbed from the emitted
JSON so outputs remain portable and leak-free.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


UB_PROBE_RS = r"""
#![allow(dead_code, unused_unsafe, unreachable_code, improper_ctypes_definitions)]

use std::mem::transmute;
use std::ptr;

#[repr(C)]
pub struct AlignedStruct {
    pub head: u32,
    pub tail: u8,
}

#[repr(u8)]
#[derive(Copy, Clone, Debug)]
pub enum DirectEnum {
    A = 0,
    B = 1,
}

pub enum EmptyEnum {}

pub enum SingleWrapBool {
    Only(bool),
}

#[inline(never)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn deref_read_u32(p: *const u32) -> u32 {
    unsafe { *p }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn borrow_field_u8(p: *const AlignedStruct) -> *const u8 {
    let r: &u8 = unsafe { &(*p).tail };
    r as *const u8
}

#[inline(never)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn deref_zst_null(p: *const ()) -> () {
    unsafe { *p }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn borrow_zst_null(p: *const ()) -> *const () {
    let r: &() = unsafe { &*p };
    r as *const ()
}

#[inline(never)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn transmute_direct_enum(x: u8) -> DirectEnum {
    unsafe { transmute::<u8, DirectEnum>(x) }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn transmute_niche_opt_bool(x: u8) -> Option<bool> {
    unsafe { transmute::<u8, Option<bool>>(x) }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn transmute_multibyte_niche(x: [u8; 8]) -> Option<(u32, bool)> {
    unsafe { transmute::<[u8; 8], Option<(u32, bool)>>(x) }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn transmute_uninhabited(x: ()) -> EmptyEnum {
    unsafe { transmute::<(), EmptyEnum>(x) }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn transmute_single_wrap_bool(x: u8) -> SingleWrapBool {
    unsafe { transmute::<u8, SingleWrapBool>(x) }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn transmute_raw_bool(x: u8) -> bool {
    unsafe { transmute::<u8, bool>(x) }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ptr_read_direct_enum(p: *const DirectEnum) -> DirectEnum {
    unsafe { *p }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn call_unreachable_unchecked(trigger: bool) -> u32 {
    if trigger {
        unsafe { std::hint::unreachable_unchecked() }
    } else {
        7
    }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn make_slice_raw(p: *const u8, len: usize) -> usize {
    let s = unsafe { std::slice::from_raw_parts(p, len) };
    s.len()
}

#[repr(align(8))]
struct AlignedBuf([u8; 16]);

fn main() {
    let case = std::env::args().nth(1).unwrap_or_default();
    match case.as_str() {
        "misaligned_u32" => {
            let buf = AlignedBuf([0x11, 0x77, 0x00, 0x00, 0x00, 0x22, 0x33, 0x44,
                                  0, 0, 0, 0, 0, 0, 0, 0]);
            let p = unsafe { buf.0.as_ptr().add(1) as *const u32 };
            let v = unsafe { deref_read_u32(std::hint::black_box(p)) };
            println!("VAL={v}");
        }
        "borrow_u8_misaligned_struct" => {
            // Byte offset +1 from an 8-byte-aligned buffer guarantees `p` is misaligned
            // for `AlignedStruct` (align 4), while `(*p).tail` at +5 is aligned for `u8`.
            let mut buf = AlignedBuf([0u8; 16]);
            buf.0[5] = 85;
            let p = unsafe { buf.0.as_ptr().add(1) as *const AlignedStruct };
            let rp = unsafe { borrow_field_u8(std::hint::black_box(p)) };
            let v = unsafe { *rp };
            println!("BYTE={v}");
        }
        "borrow_u8_null_struct" => {
            let p: *const AlignedStruct = ptr::null();
            let rp = unsafe { borrow_field_u8(std::hint::black_box(p)) };
            println!("PTR={:p}", rp);
        }
        "deref_zst_null" => {
            let p: *const () = ptr::null();
            unsafe { deref_zst_null(std::hint::black_box(p)) };
            println!("ZST_DEREF_OK");
        }
        "borrow_zst_null" => {
            let p: *const () = ptr::null();
            let rp = unsafe { borrow_zst_null(std::hint::black_box(p)) };
            println!("ZST_BORROW={:p}", rp);
        }
        "direct_enum_bad" => {
            let e = unsafe { transmute_direct_enum(std::hint::black_box(2u8)) };
            let raw: u8 = unsafe { transmute(e) };
            println!("ENUM={raw}");
        }
        "niche_opt_bool_bad" => {
            let o = unsafe { transmute_niche_opt_bool(std::hint::black_box(3u8)) };
            println!("OPT={o:?}");
        }
        "uninhabited_bad" => {
            let _e = unsafe { transmute_uninhabited(std::hint::black_box(())) };
            println!("UNINHABITED_SURVIVED");
        }
        "single_wrap_bool_bad" => {
            let w = unsafe { transmute_single_wrap_bool(std::hint::black_box(2u8)) };
            let SingleWrapBool::Only(b) = w;
            println!("SINGLE_WRAP_RAW={}", (b as u8) & 1);
        }
        "raw_bool_bad" => {
            let b = unsafe { transmute_raw_bool(std::hint::black_box(2u8)) };
            println!("RAW_BOOL={}", (b as u8) & 1);
        }
        "ptr_read_enum_bad" => {
            let x: u8 = 2;
            let p = (&x as *const u8) as *const DirectEnum;
            let e = unsafe { ptr_read_direct_enum(std::hint::black_box(p)) };
            let raw: u8 = unsafe { transmute(e) };
            println!("PTR_READ_ENUM={raw}");
        }
        "slice_null_bad" => {
            let len = unsafe { make_slice_raw(std::hint::black_box(ptr::null()), 0) };
            println!("SLICE_LEN={len}");
        }
        "unreachable_bad" => {
            let v = unsafe { call_unreachable_unchecked(std::hint::black_box(true)) };
            println!("UNREACHABLE={v}");
        }
        other => {
            eprintln!("UNKNOWN_CASE={other}");
            std::process::exit(2);
        }
    }
}
"""

UB_CASES = [
    "misaligned_u32",
    "borrow_u8_misaligned_struct",
    "borrow_u8_null_struct",
    "deref_zst_null",
    "borrow_zst_null",
    "direct_enum_bad",
    "niche_opt_bool_bad",
    "uninhabited_bad",
    "single_wrap_bool_bad",
    "raw_bool_bad",
    "ptr_read_enum_bad",
    "slice_null_bad",
    "unreachable_bad",
]

UB_FNS = [
    "deref_read_u32",
    "borrow_field_u8",
    "deref_zst_null",
    "borrow_zst_null",
    "transmute_direct_enum",
    "transmute_niche_opt_bool",
    "transmute_multibyte_niche",
    "transmute_uninhabited",
    "transmute_single_wrap_bool",
    "transmute_raw_bool",
    "ptr_read_direct_enum",
    "call_unreachable_unchecked",
    "make_slice_raw",
]

CFI_LIB_RS = r"""
#![allow(dead_code)]

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn target_zero_args() -> i32 {
    11
}

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn target_i32_ptr(p: *const i32) -> i32 {
    unsafe { *p }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn target_u8_ptr(p: *const u8) -> i32 {
    (unsafe { *p } as i32) + 20
}

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn target_two_args(a: i32, b: i32) -> i32 {
    a.wrapping_add(b)
}

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn target_three_args(a: i32, b: i32, c: i32) -> i32 {
    a.wrapping_add(b).wrapping_add(c)
}

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn call_indirect_i32_ptr(f: extern "C" fn(*const i32) -> i32, p: *const i32) -> i32 {
    f(p)
}

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn call_indirect_two_args(f: extern "C" fn(i32, i32) -> i32, a: i32, b: i32) -> i32 {
    f(a, b)
}

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn call_indirect_three_args(
    f: extern "C" fn(i32, i32, i32) -> i32,
    a: i32,
    b: i32,
    c: i32,
) -> i32 {
    f(a, b, c)
}
"""

CFI_BIN_RS = CFI_LIB_RS + r"""
fn main() {
    let case = std::env::args().nth(1).unwrap_or_default();
    let val: i32 = 42;
    let byte_val: [u8; 4] = [7, 0, 0, 0];
    let f_i32 = std::hint::black_box(target_i32_ptr as extern "C" fn(*const i32) -> i32);
    let f_u8 = std::hint::black_box(target_u8_ptr as extern "C" fn(*const u8) -> i32);
    let f_two = std::hint::black_box(target_two_args as extern "C" fn(i32, i32) -> i32);
    match case.as_str() {
        "valid" => {
            let r = call_indirect_i32_ptr(f_i32, &val as *const i32);
            println!("OK={r}");
        }
        "ptr_mismatch" => {
            let confused: extern "C" fn(*const i32) -> i32 = unsafe { std::mem::transmute(f_u8) };
            let r = call_indirect_i32_ptr(confused, byte_val.as_ptr() as *const i32);
            println!("PTR_MISMATCH={r}");
        }
        "arity_mismatch" => {
            let confused: extern "C" fn(*const i32) -> i32 = unsafe { std::mem::transmute(f_two) };
            let r = call_indirect_i32_ptr(confused, &val as *const i32);
            println!("ARITY_MISMATCH={r}");
        }
        "valid_two_args" => {
            let r = call_indirect_two_args(f_two, 19, 23);
            println!("TWO={r}");
        }
        other => {
            eprintln!("UNKNOWN_CASE={other}");
            std::process::exit(2);
        }
    }
}
"""

ASAN_RS = r"""
#[inline(never)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn read_oob(p: *const i32, idx: usize) -> i32 {
    unsafe { *p.add(idx) }
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    let v = Box::new([10i32, 20, 30, 40]);
    let p = v.as_ptr();
    let idx = if mode == "oob" { 8 } else { 2 };
    let val = unsafe { read_oob(std::hint::black_box(p), std::hint::black_box(idx)) };
    println!("VAL={val}");
}
"""

TSAN_RS = r"""
use std::sync::atomic::{AtomicU32, Ordering};

static mut NONATOMIC_CTR: u32 = 0;
static ATOMIC_CTR: AtomicU32 = AtomicU32::new(0);

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn bump_nonatomic() {
    unsafe {
        let p = std::ptr::addr_of_mut!(NONATOMIC_CTR);
        *p = (*p).wrapping_add(1);
    }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn bump_atomic() -> u32 {
    ATOMIC_CTR.fetch_add(1, Ordering::Relaxed)
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    if mode == "race" {
        let t1 = std::thread::spawn(|| {
            for _ in 0..10_000 {
                bump_nonatomic();
            }
        });
        let t2 = std::thread::spawn(|| {
            for _ in 0..10_000 {
                bump_nonatomic();
            }
        });
        t1.join().unwrap();
        t2.join().unwrap();
    } else {
        println!("ATOMIC={}", bump_atomic());
    }
}
"""

MSAN_LSAN_LIB_RS = r"""
#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn load_i32(p: *const i32) -> i32 {
    unsafe { *p }
}
"""

SANITIZE_ATTR_RS = r"""
#![feature(sanitize)]

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn normal_fn(p: *const i32) -> i32 {
    unsafe { *p }
}

#[inline(never)]
#[unsafe(no_mangle)]
#[sanitize(address = "off")]
pub extern "C" fn attr_off_fn(p: *const i32) -> i32 {
    unsafe { *p }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn ignorelist_excluded_fn(p: *const i32) -> i32 {
    unsafe { *p }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn ignorelist_reenabled_fn(p: *const i32) -> i32 {
    unsafe { *p }
}
"""

IGNORELIST_TXT = """[address]
fun:*ignorelist_excluded_fn*
fun:*ignorelist_reenabled_fn*
fun:*ignorelist_reenabled_fn*=sanitize
"""


def scrub(text: str, tmp_root: str) -> str:
    """Scrub temporary directories, hex ASLR addresses, PIDs, and user home paths."""
    out = text.replace(tmp_root, "<TMP>")
    home_dir = str(Path.home())
    if home_dir:
        out = out.replace(home_dir, "<HOME>")
    out = re.sub(r"/tmp/tmp[a-zA-Z0-9_]+", "<TMP>", out)
    out = re.sub(r"thread 'main' \(\d+\)", "thread 'main' (<PID>)", out)
    out = re.sub(r"==\d+==ERROR:", "==<PID>==ERROR:", out)
    out = re.sub(r"\(pid=\d+\)", "(pid=<PID>)", out)
    out = re.sub(r"BuildId: [0-9a-f]+", "BuildId: <BUILD_ID>", out)
    out = re.sub(r"0x[0-9a-f]{8,16}", "<ADDR>", out)
    return out


def run(cmd: list[str], cwd: Path | None = None, env: dict[str, str] | None = None, timeout: int = 120) -> subprocess.CompletedProcess[str]:
    merged = os.environ.copy()
    if env:
        merged.update(env)
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=merged,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
    )


def extract_llvm_fn_block(ir_text: str, fn_name: str) -> str | None:
    pattern = re.compile(
        rf"^define\b[^\n]*@{re.escape(fn_name)}\([^\n]*\n(?:.*?\n)*?^\}}",
        re.MULTILINE,
    )
    m = pattern.search(ir_text)
    return m.group(0) if m else None


def parse_attr_groups(ir_text: str) -> dict[str, str]:
    groups: dict[str, str] = {}
    for m in re.finditer(r"^attributes #(\d+) = \{([^}]*)\}", ir_text, re.MULTILINE):
        groups[m.group(1)] = m.group(2).strip()
    return groups


def fn_has_attr(ir_text: str, fn_block: str, attr_groups: dict[str, str], attr_token: str) -> bool:
    header = fn_block.splitlines()[0]
    m = re.search(r"#(\d+)", header)
    if not m:
        return False
    group_text = attr_groups.get(m.group(1), "")
    return attr_token in group_text.split()


def summarize_ub_llvm_ir(ir_text: str) -> dict[str, Any]:
    res: dict[str, Any] = {}
    for fn in UB_FNS:
        blk = extract_llvm_fn_block(ir_text, fn)
        if blk is None:
            res[fn] = None
            continue
        calls = sorted(set(re.findall(r"call\b[^@\n]*@([A-Za-z0-9_.$]+)", blk)))
        res[fn] = {
            "lines": len(blk.splitlines()),
            "has_unreachable": "unreachable" in blk,
            "calls": calls,
        }
    return res


def summarize_mir_dumps(dump_dir: Path) -> dict[str, dict[str, Any]]:
    res: dict[str, dict[str, Any]] = {}
    for fn in UB_FNS:
        fn_res: dict[str, Any] = {}
        for pass_name in ("CheckAlignment", "CheckNull", "CheckEnums"):
            matches = sorted(dump_dir.glob(f"*{fn}.*.{pass_name}.after.mir"))
            if not matches:
                continue
            mir_text = matches[-1].read_text(encoding="utf-8", errors="replace")
            assert_lines = [ln.strip() for ln in mir_text.splitlines() if "assert(" in ln]
            kinds = sorted(
                set(
                    re.findall(
                        r"misaligned pointer dereference|null pointer dereference|null reference|invalid enum|MisalignedPointerDereference|NullPointerDereference|NullReferenceConstructed|InvalidEnumConstruction",
                        mir_text,
                        re.IGNORECASE,
                    )
                )
            )
            has_maybe_uninit_subslice = "MaybeUninit" in mir_text and "[4..5]" in mir_text or ("MaybeUninit" in mir_text and ".." in mir_text)
            fn_res[pass_name] = {
                "assert_count": len(assert_lines),
                "assert_markers": kinds,
                "has_maybe_uninit_subslice": has_maybe_uninit_subslice if pass_name == "CheckEnums" else False,
            }
        if fn_res:
            res[fn] = fn_res
    return res


def run_probe_1_ub_checks(rustc: str, cargo: str, workdir: Path) -> dict[str, Any]:
    pdir = workdir / "probe1"
    pdir.mkdir(parents=True, exist_ok=True)
    src = pdir / "ub_probe.rs"
    src.write_text(UB_PROBE_RS, encoding="utf-8")

    configs = [
        ("ub_yes_O0", ["-C", "opt-level=0", "-Z", "ub-checks=yes"]),
        ("ub_yes_O2", ["-C", "opt-level=2", "-Z", "ub-checks=yes"]),
        ("ub_no_O0", ["-C", "opt-level=0", "-Z", "ub-checks=no"]),
        ("ub_no_O2", ["-C", "opt-level=2", "-Z", "ub-checks=no"]),
    ]

    out: dict[str, Any] = {}
    for label, flags in configs:
        cdir = pdir / label
        cdir.mkdir(parents=True, exist_ok=True)
        dump_dir = cdir / "mir_dump"
        dump_dir.mkdir(parents=True, exist_ok=True)
        bin_path = cdir / "ub_probe"
        cmd = [
            rustc,
            str(src),
            *flags,
            "-Z", "dump-mir=all",
            "-Z", f"dump-mir-dir={dump_dir}",
            "--emit=llvm-ir,link",
            "-o", str(bin_path),
        ]
        cp = run(cmd, cwd=cdir)
        entry: dict[str, Any] = {
            "compile_rc": cp.returncode,
            "compile_stderr_lines": len(cp.stderr.splitlines()),
        }
        ll_files = sorted(cdir.glob("*.ll"))
        if ll_files:
            ir_text = ll_files[0].read_text(encoding="utf-8", errors="replace")
            entry["llvm_ir"] = summarize_ub_llvm_ir(ir_text)
        entry["mir_ub_passes"] = summarize_mir_dumps(dump_dir)

        if cp.returncode == 0 and bin_path.exists():
            rt: dict[str, Any] = {}
            for case in UB_CASES:
                # Skip unreachable_bad in ub_no_O2 where UB can execute arbitrary code or loop;
                # run in ub_yes_* and ub_no_O0 (still bounded by timeout).
                if label == "ub_no_O2" and case in ("unreachable_bad", "uninhabited_bad"):
                    rt[case] = {"skipped_reason": "omitted at ub-checks=no -O2 where llvm unreachable allows arbitrary codegen"}
                    continue
                rcp = run([str(bin_path), case], cwd=cdir, timeout=15)
                stderr_lines = [scrub(ln, str(workdir)) for ln in rcp.stderr.splitlines()[:4]]
                rt[case] = {
                    "rc": rcp.returncode,
                    "stdout": scrub(rcp.stdout.strip(), str(workdir)),
                    "stderr_head": stderr_lines,
                }
            entry["runtime"] = rt
        out[label] = entry

    # Miri oracle over all 13 cases via a minimal Cargo package
    miri_dir = pdir / "miri_pkg"
    (miri_dir / "src").mkdir(parents=True, exist_ok=True)
    (miri_dir / "Cargo.toml").write_text(
        '[package]\nname = "ub_miri_probe"\nversion = "0.1.0"\nedition = "2024"\n',
        encoding="utf-8",
    )
    (miri_dir / "src" / "main.rs").write_text(UB_PROBE_RS, encoding="utf-8")

    miri_ver = run([cargo, "miri", "--version"], cwd=miri_dir)
    miri_res: dict[str, Any] = {
        "miri_version": miri_ver.stdout.strip() or miri_ver.stderr.strip(),
        "cases": {},
    }
    if miri_ver.returncode == 0:
        for case in UB_CASES:
            mcp = run(
                [cargo, "miri", "run", "--quiet", "--", case],
                cwd=miri_dir,
                env={"MIRIFLAGS": "-Zmiri-disable-isolation"},
                timeout=180,
            )
            ub_lines = [
                scrub(ln.strip(), str(workdir))
                for ln in mcp.stderr.splitlines()
                if "Undefined Behavior" in ln or "aborting due to" in ln
            ][:4]
            miri_res["cases"][case] = {
                "rc": mcp.returncode,
                "stdout": scrub(mcp.stdout.strip(), str(workdir)),
                "ub_detected": any("Undefined Behavior" in ln for ln in ub_lines),
                "ub_summary": ub_lines,
            }
    out["miri_oracle"] = miri_res
    return out


def summarize_cfi_ir(ir_text: str) -> dict[str, Any]:
    type_mds = sorted(set(re.findall(r'!"(_ZTS[^"]+)"', ir_text)))
    type_tests = re.findall(r"@llvm\.type\.test\([^\n]+", ir_text)
    kcfi_bundles = sorted(set(re.findall(r'\[\s*"kcfi"\(i32\s+(-?\d+)\)\s*\]', ir_text)))
    kcfi_type_refs = len(re.findall(r"!kcfi_type !\d+", ir_text))
    has_kcfi_arity_flag = '"kcfi-arity", i32 1' in ir_text
    has_canon_jt_flag = '"CFI Canonical Jump Tables", i32 1' in ir_text
    has_split_lto = '"EnableSplitLTOUnit", i32 1' in ir_text
    call_i32_blk = extract_llvm_fn_block(ir_text, "call_indirect_i32_ptr")
    t_i32 = extract_llvm_fn_block(ir_text, "target_i32_ptr")
    t_u8 = extract_llvm_fn_block(ir_text, "target_u8_ptr")
    return {
        "type_test_count": len(type_tests),
        "has_kcfi_arity_module_flag": has_kcfi_arity_flag,
        "has_cfi_canonical_jump_tables_flag": has_canon_jt_flag,
        "has_split_lto_unit_flag": has_split_lto,
        "type_mds_sample": type_mds[:20],
        "all_type_md_count": len(type_mds),
        "kcfi_type_md_refs": kcfi_type_refs,
        "kcfi_bundles": kcfi_bundles,
        "call_indirect_i32_ptr_ir": call_i32_blk,
        "target_i32_ptr_header": t_i32.splitlines()[0] if t_i32 else None,
        "target_u8_ptr_header": t_u8.splitlines()[0] if t_u8 else None,
    }


def extract_asm_preamble(asm_text: str, sym: str) -> list[str]:
    lines = asm_text.splitlines()
    marker = f"__cfi_{sym}:"
    for i, ln in enumerate(lines):
        if ln.strip() == marker:
            return [x.strip() for x in lines[i : i + 18]]
    return []


def summarize_cfi_asm(asm_text: str) -> dict[str, Any]:
    lines = asm_text.splitlines()
    has_jt = "cfi.jumptable" in asm_text
    ud2_count = sum(1 for ln in lines if re.search(r"\bud2\b", ln))
    jt_lines = [
        ln.strip()
        for ln in lines
        if any(k in ln for k in ("cfi.jumptable", ".kcfi_traps", "target_i32_ptr =", "target_u8_ptr =", "target_two_args ="))
    ][:25]
    preambles = {}
    for sym in ("target_zero_args", "target_i32_ptr", "target_two_args", "target_three_args"):
        p = extract_asm_preamble(asm_text, sym)
        if p:
            mov_lines = [ln for ln in p if ln.startswith("movl")]
            preambles[sym] = {"movl": mov_lines, "lines": p}
    return {
        "has_cfi_jt": has_jt,
        "ud2_count": ud2_count,
        "jt_and_kcfi_lines": jt_lines,
        "kcfi_preambles": preambles,
    }


def run_probe_2_cfi_kcfi(rustc: str, workdir: Path) -> dict[str, Any]:
    pdir = workdir / "probe2"
    pdir.mkdir(parents=True, exist_ok=True)
    lib_rs = pdir / "cfi_lib.rs"
    bin_rs = pdir / "cfi_bin.rs"
    lib_rs.write_text(CFI_LIB_RS, encoding="utf-8")
    bin_rs.write_text(CFI_BIN_RS, encoding="utf-8")

    abi_flag = ["-C", "unsafe-allow-abi-mismatch=sanitizer"]

    modes: list[tuple[str, Path, list[str], bool]] = [
        (
            "lto_cfi_pre_lto_lib",
            lib_rs,
            ["--crate-type=lib", "-C", "opt-level=2", "-C", "linker-plugin-lto", "-Z", "sanitizer=cfi", *abi_flag, "--emit=llvm-ir"],
            False,
        ),
        (
            "lto_cfi_default",
            bin_rs,
            ["--crate-type=bin", "-C", "opt-level=2", "-C", "lto", "-Z", "sanitizer=cfi", *abi_flag, "--emit=llvm-ir,asm,link"],
            True,
        ),
        (
            "lto_cfi_generalize_ptrs",
            bin_rs,
            ["--crate-type=bin", "-C", "opt-level=2", "-C", "lto", "-Z", "sanitizer=cfi", "-Z", "sanitizer-cfi-generalize-pointers=yes", *abi_flag, "--emit=llvm-ir,asm,link"],
            True,
        ),
        (
            "lto_cfi_no_canon_jt",
            bin_rs,
            ["--crate-type=bin", "-C", "opt-level=2", "-C", "lto", "-Z", "sanitizer=cfi", "-Z", "sanitizer-cfi-canonical-jump-tables=no", *abi_flag, "--emit=llvm-ir,asm,link"],
            True,
        ),
        (
            "kcfi_default",
            lib_rs,
            ["--crate-type=lib", "-C", "opt-level=2", "-C", "panic=abort", "-Z", "sanitizer=kcfi", *abi_flag, "--emit=llvm-ir,asm"],
            False,
        ),
        (
            "kcfi_arity",
            lib_rs,
            ["--crate-type=lib", "-C", "opt-level=2", "-C", "panic=abort", "-Z", "sanitizer=kcfi", "-Z", "sanitizer-kcfi-arity=yes", *abi_flag, "--emit=llvm-ir,asm"],
            False,
        ),
    ]

    out: dict[str, Any] = {}
    for label, src, flags, run_bin in modes:
        mdir = pdir / label
        mdir.mkdir(parents=True, exist_ok=True)
        out_base = mdir / ("artifact.ll" if "--emit=llvm-ir" in flags else "artifact")
        cp = run([rustc, str(src), *flags, "-o", str(out_base)], cwd=mdir)
        entry: dict[str, Any] = {
            "compile_rc": cp.returncode,
            "compile_stderr": scrub(cp.stderr.strip(), str(workdir))[:400],
        }
        ll_files = sorted(mdir.glob("*.ll"))
        if ll_files:
            entry["ir_signals"] = summarize_cfi_ir(ll_files[0].read_text(encoding="utf-8", errors="replace"))
        s_files = sorted(mdir.glob("*.s"))
        if s_files:
            entry["asm_signals"] = summarize_cfi_asm(s_files[0].read_text(encoding="utf-8", errors="replace"))
        if run_bin and cp.returncode == 0 and out_base.exists():
            rt: dict[str, Any] = {}
            for case in ("valid", "valid_two_args", "ptr_mismatch", "arity_mismatch"):
                rcp = run([str(out_base), case], cwd=mdir, timeout=15)
                rt[case] = {
                    "rc": rcp.returncode,
                    "stdout": scrub(rcp.stdout.strip(), str(workdir)),
                    "stderr": scrub(rcp.stderr.strip(), str(workdir))[:200],
                }
            entry["runtime"] = rt
        out[label] = entry
    return out


def run_probe_3_sanitizers(rustc: str, workdir: Path) -> dict[str, Any]:
    pdir = workdir / "probe3"
    pdir.mkdir(parents=True, exist_ok=True)
    out: dict[str, Any] = {}

    # 1. ASan
    adir = pdir / "asan"
    adir.mkdir()
    asrc = adir / "asan_probe.rs"
    asrc.write_text(ASAN_RS, encoding="utf-8")
    abin = adir / "bin"
    acp = run([rustc, str(asrc), "-C", "opt-level=1", "-Z", "sanitizer=address", "--emit=llvm-ir,link", "-o", str(abin)], cwd=adir)
    asan_entry: dict[str, Any] = {"compile_rc": acp.returncode}
    ll_files = sorted(adir.glob("*.ll"))
    if ll_files:
        ir = ll_files[0].read_text(encoding="utf-8", errors="replace")
        asan_entry["has_sanitize_address_attr"] = "sanitize_address" in ir
        asan_entry["has_asan_init"] = "@__asan_init" in ir or "asan.module_ctor" in ir
        asan_entry["asan_report_calls"] = sorted(set(re.findall(r"@(__asan_report_[a-z0-9_]+)", ir)))
    if acp.returncode == 0 and abin.exists():
        # detect_leaks=0 avoids ptrace/LSan issues in restricted sandboxes while testing ASan heap OOB
        env_asan = {"ASAN_OPTIONS": "detect_leaks=0:abort_on_error=0"}
        r_ok = run([str(abin), "ok"], cwd=adir, env=env_asan, timeout=20)
        r_oob = run([str(abin), "oob"], cwd=adir, env=env_asan, timeout=20)
        summary_lines = [
            scrub(ln.strip(), str(workdir))
            for ln in r_oob.stderr.splitlines()
            if "ERROR: AddressSanitizer" in ln or "SUMMARY: AddressSanitizer" in ln
        ][:4]
        asan_entry["run_in_bounds"] = {"rc": r_ok.returncode, "stdout": r_ok.stdout.strip()}
        asan_entry["run_oob"] = {
            "rc": r_oob.returncode,
            "detected_heap_overflow": "heap-buffer-overflow" in r_oob.stderr,
            "stderr_summary": summary_lines,
        }
    out["asan"] = asan_entry

    # 2. TSan
    tdir = pdir / "tsan"
    tdir.mkdir()
    tsrc = tdir / "tsan_probe.rs"
    tsrc.write_text(TSAN_RS, encoding="utf-8")
    tbin = tdir / "bin"
    tcp = run(
        [rustc, str(tsrc), "-C", "opt-level=1", "-Z", "sanitizer=thread", "-C", "unsafe-allow-abi-mismatch=sanitizer", "--emit=llvm-ir,link", "-o", str(tbin)],
        cwd=tdir,
    )
    tsan_entry: dict[str, Any] = {
        "compile_rc": tcp.returncode,
        "compile_stderr": scrub(tcp.stderr.strip(), str(workdir))[:300],
    }
    ll_files = sorted(tdir.glob("*.ll"))
    if ll_files:
        ir = ll_files[0].read_text(encoding="utf-8", errors="replace")
        tsan_entry["has_sanitize_thread_attr"] = "sanitize_thread" in ir
        blk_non = extract_llvm_fn_block(ir, "bump_nonatomic") or ""
        blk_atom = extract_llvm_fn_block(ir, "bump_atomic") or ""
        tsan_entry["tsan_calls_nonatomic"] = sorted(set(re.findall(r"@(__tsan_[a-z0-9_]+)", blk_non)))
        tsan_entry["tsan_calls_atomic"] = sorted(set(re.findall(r"@(__tsan_[a-z0-9_]+)", blk_atom)))
    if tcp.returncode == 0 and tbin.exists():
        r_ok = run([str(tbin), "atomic"], cwd=tdir, timeout=20)
        r_race = run([str(tbin), "race"], cwd=tdir, env={"TSAN_OPTIONS": "halt_on_error=0:exitcode=66"}, timeout=30)
        summary_lines = [
            scrub(ln.strip(), str(workdir))
            for ln in r_race.stderr.splitlines()
            if "WARNING: ThreadSanitizer" in ln or "SUMMARY: ThreadSanitizer" in ln
        ][:4]
        tsan_entry["run_atomic"] = {"rc": r_ok.returncode, "stdout": r_ok.stdout.strip()}
        tsan_entry["run_race"] = {
            "rc": r_race.returncode,
            "detected_data_race": "ThreadSanitizer: data race" in r_race.stderr,
            "stderr_summary": summary_lines,
        }
    out["tsan"] = tsan_entry

    # 3. MSan with -Z sanitizer-memory-track-origins=2
    mdir = pdir / "msan"
    mdir.mkdir()
    msrc = mdir / "msan_lib.rs"
    msrc.write_text(MSAN_LSAN_LIB_RS, encoding="utf-8")
    mcp = run(
        [rustc, str(msrc), "--crate-type=lib", "-C", "opt-level=1", "-Z", "sanitizer=memory", "-Z", "sanitizer-memory-track-origins=2", "-C", "unsafe-allow-abi-mismatch=sanitizer", "--emit=llvm-ir", "-o", str(mdir / "msan.ll")],
        cwd=mdir,
    )
    msan_entry: dict[str, Any] = {
        "compile_rc": mcp.returncode,
        "compile_stderr": scrub(mcp.stderr.strip(), str(workdir))[:300],
    }
    if mcp.returncode == 0 and (mdir / "msan.ll").exists():
        ir = (mdir / "msan.ll").read_text(encoding="utf-8", errors="replace")
        msan_entry["has_sanitize_memory_attr"] = "sanitize_memory" in ir
        msan_entry["msan_symbols"] = sorted(set(re.findall(r"@(__msan_[a-z0-9_]+)", ir)))
    out["msan_origins2"] = msan_entry

    # 4. LSan (runtime-only linker flag; zero IR instrumentation)
    ldir = pdir / "lsan"
    ldir.mkdir()
    lsrc = ldir / "lsan_lib.rs"
    lsrc.write_text(MSAN_LSAN_LIB_RS, encoding="utf-8")
    lcp = run(
        [rustc, str(lsrc), "--crate-type=lib", "-C", "opt-level=1", "-Z", "sanitizer=leak", "--emit=llvm-ir", "-o", str(ldir / "lsan.ll")],
        cwd=ldir,
    )
    lsan_entry: dict[str, Any] = {"compile_rc": lcp.returncode}
    if lcp.returncode == 0 and (ldir / "lsan.ll").exists():
        ir = (ldir / "lsan.ll").read_text(encoding="utf-8", errors="replace")
        lsan_entry["has_sanitize_address_attr"] = "sanitize_address" in ir
        lsan_entry["has_asan_init"] = "@__asan_init" in ir
        lsan_entry["lsan_ir_symbols"] = sorted(set(re.findall(r"@(__lsan_[a-z0-9_]+)", ir)))
    out["lsan"] = lsan_entry

    return out


def inspect_sanitize_ir(ir_text: str) -> dict[str, Any]:
    groups = parse_attr_groups(ir_text)
    fns = ["normal_fn", "attr_off_fn", "ignorelist_excluded_fn", "ignorelist_reenabled_fn"]
    res: dict[str, Any] = {}
    for fn in fns:
        blk = extract_llvm_fn_block(ir_text, fn)
        if blk is None:
            res[fn] = None
            continue
        res[fn] = {
            "header": blk.splitlines()[0],
            "has_sanitize_address": fn_has_attr(ir_text, blk, groups, "sanitize_address"),
            "has_asan_report_call": "__asan_report_" in blk,
        }
    return res


def run_probe_4_sanitize_attr_and_ignorelist(rustc: str, workdir: Path) -> dict[str, Any]:
    pdir = workdir / "probe4"
    pdir.mkdir(parents=True, exist_ok=True)
    src = pdir / "sanitize_attr.rs"
    src.write_text(SANITIZE_ATTR_RS, encoding="utf-8")
    ig = pdir / "ignorelist.txt"
    ig.write_text(IGNORELIST_TXT, encoding="utf-8")

    # Feature-detect -Z sanitizer-ignorelist on the invoked rustc
    zhelp = run([rustc, "-Z", "help"]).stdout + run([rustc, "-Z", "help"]).stderr
    supports_ignorelist = "sanitizer-ignorelist" in zhelp

    out: dict[str, Any] = {
        "supports_z_sanitizer_ignorelist": supports_ignorelist,
        "ignorelist_text": IGNORELIST_TXT,
    }

    # Always test #[sanitize(address = "off")] without ignorelist
    ll_attr = pdir / "attr_only.ll"
    cp_attr = run(
        [rustc, str(src), "--crate-type=lib", "-C", "opt-level=1", "-Z", "sanitizer=address", "--emit=llvm-ir", "-o", str(ll_attr)],
        cwd=pdir,
    )
    out["attr_only_mode"] = {
        "compile_rc": cp_attr.returncode,
        "compile_stderr": scrub(cp_attr.stderr.strip(), str(workdir))[:300],
        "fn_attrs": inspect_sanitize_ir(ll_attr.read_text(encoding="utf-8", errors="replace")) if cp_attr.returncode == 0 else {},
    }

    # Test with -Z sanitizer-ignorelist
    ll_ig = pdir / "with_ignorelist.ll"
    cp_ig = run(
        [
            rustc,
            str(src),
            "--crate-type=lib",
            "-C", "opt-level=1",
            "-Z", "sanitizer=address",
            "-Z", f"sanitizer-ignorelist={ig}",
            "--emit=llvm-ir",
            "-o", str(ll_ig),
        ],
        cwd=pdir,
    )
    out["ignorelist_mode"] = {
        "compile_rc": cp_ig.returncode,
        "compile_stderr": scrub(cp_ig.stderr.strip(), str(workdir))[:300],
        "fn_attrs": inspect_sanitize_ir(ll_ig.read_text(encoding="utf-8", errors="replace")) if cp_ig.returncode == 0 else {},
    }
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="Output JSON path")
    args = parser.parse_args()

    rustc = os.environ.get("RUSTC") or shutil.which("rustc")
    cargo = os.environ.get("CARGO") or shutil.which("cargo")
    if not rustc or not cargo:
        print("error: rustc and cargo must be on PATH", file=sys.stderr)
        return 1

    rustc_ver = run([rustc, "--version", "--verbose"]).stdout.strip()
    with tempfile.TemporaryDirectory(prefix="rustc_san_probe_") as tmp:
        workdir = Path(tmp)
        result = {
            "rustc_version": rustc_ver,
            "probe_1_ub_checks": run_probe_1_ub_checks(rustc, cargo, workdir),
            "probe_2_lto_cfi_vs_kcfi": run_probe_2_cfi_kcfi(rustc, workdir),
            "probe_3_asan_tsan_msan_lsan": run_probe_3_sanitizers(rustc, workdir),
            "probe_4_sanitize_attr_and_ignorelist": run_probe_4_sanitize_attr_and_ignorelist(rustc, workdir),
        }

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=False) + "\n", encoding="utf-8")
    print(f"Wrote probe results to {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
