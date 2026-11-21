#!/usr/bin/env python3
"""Empirical probe for #[repr(packed(N))] layout, E0793, AddMovesForPackedDrops,
LLVM IR alignment emission, and the -Z ub-checks vs Miri alignment-check matrix.

Runs standalone using the active nightly `rustc` and `cargo miri` in PATH and
writes scrubbed, deterministic JSON to stdout or `--out <path>`.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _env_with_cargo() -> dict[str, str]:
    env = dict(os.environ)
    cargo_bin = str(Path.home() / ".cargo" / "bin")
    path = env.get("PATH", "")
    if cargo_bin not in path.split(os.pathsep):
        env["PATH"] = f"{cargo_bin}{os.pathsep}{path}" if path else cargo_bin
    return env


def _scrub(text: str, tmpdir: str) -> str:
    """Remove volatile temp dirs, home dirs, PIDs, and raw stack addresses."""
    out = text.replace(tmpdir, "<TMP>")
    home = str(Path.home())
    if home:
        out = out.replace(home, "<HOME>")
    out = re.sub(r"thread '([^']+)' \(\d+\)", r"thread '\1' (<TID>)", out)
    out = re.sub(r"0x[0-9a-fA-F]{6,16}", "<ADDR>", out)
    return out


def _run(
    cmd: list[str],
    *,
    cwd: str | None = None,
    env: dict[str, str] | None = None,
    timeout: int = 120,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=cwd,
        env=env,
        text=True,
        capture_output=True,
        timeout=timeout,
    )


def _run_miri_single(src: str, name: str, tmpdir: str, env: dict[str, str]) -> dict[str, Any]:
    crate_dir = Path(tmpdir) / f"miri_{name}"
    (crate_dir / "src").mkdir(parents=True, exist_ok=True)
    (crate_dir / "Cargo.toml").write_text(
        f'[package]\nname = "{name}"\nversion = "0.1.0"\nedition = "2021"\n',
        encoding="utf-8",
    )
    (crate_dir / "src" / "main.rs").write_text(src, encoding="utf-8")
    p = _run(["cargo", "miri", "run", "--offline"], cwd=str(crate_dir), env=env)
    return {
        "rc": p.returncode,
        "stdout": _scrub(p.stdout, tmpdir).strip(),
        "stderr_ub_lines": [
            _scrub(line, tmpdir)
            for line in p.stderr.splitlines()
            if any(
                k in line
                for k in (
                    "Undefined Behavior",
                    "alignment",
                    "misaligned",
                    "dangling",
                    "error:",
                    "panicked",
                )
            )
        ][:12],
    }


def exp1_layout_and_llvm_ir(tmpdir: str, env: dict[str, str]) -> dict[str, Any]:
    """Measure packed layouts, DST rounding, ABI suppression, and LLVM IR align attributes."""
    layout_src = r"""
use std::mem::{align_of, offset_of, size_of, size_of_val};
use std::ptr;

#[repr(C, packed)]
#[allow(dead_code)]
struct Packed1 { tag: u8, x: u32, y: u64 }

#[repr(C, packed(2))]
#[allow(dead_code)]
struct Packed2 { tag: u8, x: u32, y: u64 }

#[repr(C, packed(4))]
#[allow(dead_code)]
struct Packed4 { tag: u8, x: u32, y: u64 }

#[repr(C)]
#[allow(dead_code)]
struct InnerAligned { a: u32, b: u8 }

#[repr(C, packed)]
#[allow(dead_code)]
struct OuterPackedInnerAligned { tag: u8, inner: InnerAligned }

#[repr(packed)]
#[allow(dead_code)]
struct PackedNewtype(u64);

#[allow(dead_code)]
struct AlignedNewtype(u64);

#[repr(C)]
#[allow(dead_code)]
struct InnerDst { a: u32, tail: [u8] }

#[repr(C, packed(2))]
#[allow(dead_code)]
struct OuterPacked2Dst { b: u8, inner: InnerDst }

fn dst_size(elems: usize) -> usize {
    let raw: *const [u8] = ptr::slice_from_raw_parts(ptr::dangling::<u8>(), elems);
    let dst = raw as *const OuterPacked2Dst;
    // SAFETY: size_of_val on a slice-tail DST reads only the length metadata.
    unsafe { size_of_val(&*dst) }
}

fn main() {
    println!("Packed1 size={} align={} offsets={},{},{}",
        size_of::<Packed1>(), align_of::<Packed1>(),
        offset_of!(Packed1, tag), offset_of!(Packed1, x), offset_of!(Packed1, y));
    println!("Packed2 size={} align={} offsets={},{},{}",
        size_of::<Packed2>(), align_of::<Packed2>(),
        offset_of!(Packed2, tag), offset_of!(Packed2, x), offset_of!(Packed2, y));
    println!("Packed4 size={} align={} offsets={},{},{}",
        size_of::<Packed4>(), align_of::<Packed4>(),
        offset_of!(Packed4, tag), offset_of!(Packed4, x), offset_of!(Packed4, y));
    println!("InnerAligned size={} align={} offsets={},{}",
        size_of::<InnerAligned>(), align_of::<InnerAligned>(),
        offset_of!(InnerAligned, a), offset_of!(InnerAligned, b));
    println!("OuterPackedInnerAligned size={} align={} offsets={},{}",
        size_of::<OuterPackedInnerAligned>(), align_of::<OuterPackedInnerAligned>(),
        offset_of!(OuterPackedInnerAligned, tag), offset_of!(OuterPackedInnerAligned, inner));
    println!("PackedNewtype size={} align={}", size_of::<PackedNewtype>(), align_of::<PackedNewtype>());
    println!("AlignedNewtype size={} align={}", size_of::<AlignedNewtype>(), align_of::<AlignedNewtype>());
    println!("OuterPacked2Dst_sizes 0={} 1={} 2={} 5={}",
        dst_size(0), dst_size(1), dst_size(2), dst_size(5));
}
"""
    rs_path = Path(tmpdir) / "exp1_layout.rs"
    bin_path = Path(tmpdir) / "exp1_layout"
    rs_path.write_text(layout_src, encoding="utf-8")
    c = _run(["rustc", "--edition=2021", "-C", "opt-level=0", str(rs_path), "-o", str(bin_path)], env=env)
    assert c.returncode == 0, c.stderr
    r = _run([str(bin_path)], env=env)
    assert r.returncode == 0, r.stderr

    ir_src = r"""
#![crate_type = "lib"]

#[repr(C, packed)]
pub struct Packed1 { pub tag: u8, pub x: u32, pub y: u64 }

#[repr(C, packed(2))]
pub struct Packed2 { pub tag: u8, pub x: u32, pub y: u64 }

#[repr(C, packed(4))]
pub struct Packed4 { pub tag: u8, pub x: u32, pub y: u64 }

#[repr(packed)]
pub struct PackedNewtype(pub u64);

pub struct AlignedNewtype(pub u64);

#[unsafe(no_mangle)]
pub extern "C" fn read_p1_u32(p: &Packed1) -> u32 { p.x }

#[unsafe(no_mangle)]
pub extern "C" fn write_p1_u32(p: &mut Packed1, v: u32) { p.x = v; }

#[unsafe(no_mangle)]
pub extern "C" fn read_p2_u32(p: &Packed2) -> u32 { p.x }

#[unsafe(no_mangle)]
pub extern "C" fn write_p2_u32(p: &mut Packed2, v: u32) { p.x = v; }

#[unsafe(no_mangle)]
pub extern "C" fn read_p4_u32(p: &Packed4) -> u32 { p.x }

#[unsafe(no_mangle)]
pub extern "C" fn read_p4_u64(p: &Packed4) -> u64 { p.y }

#[unsafe(no_mangle)]
pub unsafe extern "C" fn read_p1_unaligned_raw(p: &Packed1) -> u32 {
    let raw: *const u32 = &raw const p.x;
    unsafe { core::ptr::read_unaligned(raw) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn read_p1_ub_deref_raw(p: &Packed1) -> u32 {
    let raw: *const u32 = core::hint::black_box(&raw const p.x);
    unsafe { *raw }
}

#[unsafe(no_mangle)]
pub fn pass_packed_newtype(v: PackedNewtype) -> u64 { v.0.wrapping_add(1) }

#[unsafe(no_mangle)]
pub fn pass_aligned_newtype(v: AlignedNewtype) -> u64 { v.0.wrapping_add(2) }
"""
    ir_rs = Path(tmpdir) / "exp1_ir.rs"
    ir_rs.write_text(ir_src, encoding="utf-8")

    llvm_results: dict[str, Any] = {}
    for opt in ("0", "2"):
        ll_path = Path(tmpdir) / f"exp1_ir_O{opt}.ll"
        c_ir = _run(
            [
                "rustc",
                "--edition=2021",
                "-C",
                f"opt-level={opt}",
                "-C",
                "debuginfo=0",
                "--emit=llvm-ir",
                str(ir_rs),
                "-o",
                str(ll_path),
            ],
            env=env,
        )
        assert c_ir.returncode == 0, c_ir.stderr
        ir_text = ll_path.read_text(encoding="utf-8")
        fns: dict[str, Any] = {}
        fn_names = [
            "read_p1_u32",
            "write_p1_u32",
            "read_p2_u32",
            "write_p2_u32",
            "read_p4_u32",
            "read_p4_u64",
            "read_p1_unaligned_raw",
            "read_p1_ub_deref_raw",
            "pass_packed_newtype",
            "pass_aligned_newtype",
        ]
        for fname in fn_names:
            m = re.search(
                rf"^define[^\n]*@{re.escape(fname)}\b[^\n]*\n(.*?)^\}}",
                ir_text,
                re.MULTILINE | re.DOTALL,
            )
            if not m:
                fns[fname] = {"found": False}
                continue
            full_def = m.group(0)
            header = full_def.splitlines()[0]
            mem_ops = [
                line.strip()
                for line in full_def.splitlines()
                if any(tok in line for tok in ("load ", "store ", "llvm.memcpy"))
            ]
            fns[fname] = {"header": header, "mem_ops": mem_ops}
        llvm_results[f"O{opt}"] = fns

    return {
        "layout_stdout": r.stdout.strip().splitlines(),
        "llvm_ir": llvm_results,
    }


def exp2_e0793_and_wfcheck_matrix(tmpdir: str, env: dict[str, str]) -> list[dict[str, Any]]:
    """Compile-time matrix for E0793, Copy copy-out, &raw const, E0277, E0587, E0588, E0634, E0509."""
    cases = [
        (
            "safe_ref_packed1_u32",
            "#[repr(C, packed)] pub struct P1 { pub tag: u8, pub x: u32 }\n"
            "pub fn f(p: &P1) -> &u32 { &p.x }\n",
            False,
        ),
        (
            "unsafe_ref_packed1_u32",
            "#[repr(C, packed)] pub struct P1 { pub tag: u8, pub x: u32 }\n"
            "pub fn f(p: &P1) -> &u32 { unsafe { &p.x } }\n",
            False,
        ),
        (
            "println_implicit_ref_packed1_u32",
            "#[repr(C, packed)] pub struct P1 { pub tag: u8, pub x: u32 }\n"
            "pub fn f(p: &P1) { println!(\"{}\", p.x); }\n",
            False,
        ),
        (
            "braced_copy_packed1_u32",
            "#[repr(C, packed)] pub struct P1 { pub tag: u8, pub x: u32 }\n"
            "pub fn f(p: &P1) { println!(\"{}\", { p.x }); }\n",
            True,
        ),
        (
            "safe_ref_packed1_u8_ok",
            "#[repr(C, packed)] pub struct P1 { pub tag: u8, pub x: u32 }\n"
            "pub fn f(p: &P1) -> &u8 { &p.tag }\n",
            True,
        ),
        (
            "safe_ref_packed4_u32_ok",
            "#[repr(C, packed(4))] pub struct P4 { pub tag: u8, pub x: u32, pub y: u64 }\n"
            "pub fn f(p: &P4) -> &u32 { &p.x }\n",
            True,
        ),
        (
            "safe_ref_packed4_u64_err",
            "#[repr(C, packed(4))] pub struct P4 { pub tag: u8, pub x: u32, pub y: u64 }\n"
            "pub fn f(p: &P4) -> &u64 { &p.y }\n",
            False,
        ),
        (
            "safe_raw_ptr_packed1_u32_ok",
            "#[repr(C, packed)] pub struct P1 { pub tag: u8, pub x: u32 }\n"
            "pub fn f(p: &mut P1) -> (*const u32, *mut u32) { (&raw const p.x, &raw mut p.x) }\n",
            True,
        ),
        (
            "packed_unsized_drop_tail_err",
            "pub struct D(pub u32);\nimpl Drop for D { fn drop(&mut self) {} }\n"
            "#[repr(C, packed)] pub struct S { pub tag: u8, pub tail: [D] }\n",
            False,
        ),
        (
            "packed_unsized_manually_drop_tail_ok",
            "use core::mem::ManuallyDrop;\n"
            "pub struct D(pub u32);\nimpl Drop for D { fn drop(&mut self) {} }\n"
            "#[repr(C, packed)] pub struct S { pub tag: u8, pub tail: ManuallyDrop<[D]> }\n",
            True,
        ),
        (
            "repr_packed_and_align_conflict_e0587",
            "#[repr(packed, align(8))] pub struct Bad { pub a: u8 }\n",
            False,
        ),
        (
            "packed_containing_repr_align_e0588",
            "#[repr(align(64))] pub struct OverAligned(pub u64);\n"
            "#[repr(C, packed)] pub struct Holder { pub b: u8, pub o: OverAligned }\n",
            False,
        ),
        (
            "repr_packed_duplicate_e0634",
            "#[repr(packed(1), packed(2))] pub struct Bad { pub a: u8 }\n",
            False,
        ),
        (
            "custom_drop_move_from_mut_ref_e0507",
            "pub struct D(pub u32);\nimpl Drop for D { fn drop(&mut self) {} }\n"
            "#[repr(packed)] pub struct S { pub tag: u8, pub d: D }\n"
            "impl Drop for S { fn drop(&mut self) { let _x = self.d; } }\n",
            False,
        ),
        (
            "custom_drop_owned_move_field_e0509",
            "pub struct D(pub u32);\nimpl Drop for D { fn drop(&mut self) {} }\n"
            "#[repr(packed)] pub struct S { pub tag: u8, pub d: D }\n"
            "impl Drop for S { fn drop(&mut self) {} }\n"
            "pub fn f(s: S) -> D { s.d }\n",
            False,
        ),
    ]
    results = []
    for name, src, expect_ok in cases:
        rs = Path(tmpdir) / f"exp2_{name}.rs"
        out = Path(tmpdir) / f"libexp2_{name}.rlib"
        rs.write_text(src, encoding="utf-8")
        p = _run(
            [
                "rustc",
                "--edition=2021",
                "--crate-type=lib",
                "--error-format=json",
                str(rs),
                "-o",
                str(out),
            ],
            env=env,
        )
        codes: list[str] = []
        msgs: list[str] = []
        for line in p.stderr.splitlines():
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            if obj.get("level") == "error":
                code = obj.get("code")
                if isinstance(code, dict) and code.get("code"):
                    codes.append(code["code"])
                if obj.get("message"):
                    msgs.append(_scrub(obj["message"], tmpdir))
        results.append(
            {
                "case": name,
                "expected_ok": expect_ok,
                "compiled_ok": p.returncode == 0,
                "error_codes": codes,
                "error_messages": msgs,
            }
        )
    return results


def exp3_add_moves_for_packed_drops(tmpdir: str, env: dict[str, str]) -> dict[str, Any]:
    """Capture AddMovesForPackedDrops before/after MIR (user body AND DropGlue shim) + native/Miri runs.

    Uses `DropU128([u128; 2])` (natural ABI alignment 16 on x86_64-unknown-linux-gnu, no #[repr(align)])
    wrapped inside `#[repr(align(16))] struct Align16<T>(T)` so the packed field offset `1` guarantees
    `(&raw const holder.0.aligned).addr() % 16 == 1` deterministically across native and Miri.
    """
    src = r"""
use std::sync::atomic::{AtomicUsize, Ordering};

static LAST_DROP_MOD16: AtomicUsize = AtomicUsize::new(999);
static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

#[repr(C)]
#[allow(dead_code)]
struct DropU128([u128; 2]);

impl Drop for DropU128 {
    fn drop(&mut self) {
        let addr = (self as *const Self).addr();
        LAST_DROP_MOD16.store(addr % 16, Ordering::SeqCst);
        DROP_COUNT.fetch_add(1, Ordering::SeqCst);
    }
}

#[repr(C, packed)]
#[allow(dead_code)]
struct PackedHolder {
    pad: u8,
    aligned: DropU128,
}

#[repr(align(16))]
struct Align16<T>(T);

#[inline(never)]
fn overwrite_packed_field(mut holder: Align16<PackedHolder>, replacement: DropU128) -> (usize, usize) {
    let field_mod = (&raw const holder.0.aligned).addr() % 16;
    // Direct field overwrite emits TerminatorKind::Drop on `(holder.0).1` in user MIR.
    holder.0.aligned = replacement;
    let after_overwrite_mod = LAST_DROP_MOD16.load(Ordering::SeqCst);
    drop(holder);
    (field_mod, after_overwrite_mod)
}

#[inline(never)]
fn drop_whole_packed_holder(holder: Align16<PackedHolder>) -> usize {
    let field_mod = (&raw const holder.0.aligned).addr() % 16;
    drop(holder);
    field_mod
}

fn main() {
    assert_eq!(std::mem::align_of::<DropU128>(), 16);
    assert_eq!(std::mem::align_of::<PackedHolder>(), 1);
    assert_eq!(std::mem::offset_of!(PackedHolder, aligned), 1);

    let p1 = Align16(PackedHolder { pad: 7, aligned: DropU128([1, 2]) });
    let r1 = DropU128([3, 4]);
    let (ov_field_mod, ov_drop_mod) = overwrite_packed_field(p1, r1);
    let ov_final_mod = LAST_DROP_MOD16.load(Ordering::SeqCst);
    let ov_count = DROP_COUNT.load(Ordering::SeqCst);

    let p2 = Align16(PackedHolder { pad: 9, aligned: DropU128([5, 6]) });
    let whole_field_mod = drop_whole_packed_holder(p2);
    let whole_drop_mod = LAST_DROP_MOD16.load(Ordering::SeqCst);
    let total_count = DROP_COUNT.load(Ordering::SeqCst);

    println!(
        "OVERWRITE_FIELD_MOD16={} OVERWRITE_DROP_MOD16={} FINAL_MOD16={} OV_COUNT={} WHOLE_FIELD_MOD16={} WHOLE_DROP_MOD16={} TOTAL_COUNT={}",
        ov_field_mod, ov_drop_mod, ov_final_mod, ov_count, whole_field_mod, whole_drop_mod, total_count
    );
}
"""
    rs = Path(tmpdir) / "exp3_packed_drops.rs"
    bin_path = Path(tmpdir) / "exp3_packed_drops"
    dump_dir = Path(tmpdir) / "exp3_mir_dump"
    dump_dir.mkdir(exist_ok=True)
    rs.write_text(src, encoding="utf-8")

    c = _run(
        [
            "rustc",
            "--edition=2021",
            "-C",
            "opt-level=0",
            "-C",
            "debuginfo=0",
            "-Z",
            "dump-mir=AddMovesForPackedDrops",
            "-Z",
            f"dump-mir-dir={dump_dir}",
            str(rs),
            "-o",
            str(bin_path),
        ],
        env=env,
    )
    assert c.returncode == 0, c.stderr
    native_run = _run([str(bin_path)], env=env)
    assert native_run.returncode == 0, native_run.stderr
    miri_run = _run_miri_single(src, "exp3_packed_drops", tmpdir, env)

    mir_files = sorted(f.name for f in dump_dir.iterdir() if f.is_file())
    snippets: dict[str, str] = {}
    for fname in mir_files:
        text = (dump_dir / fname).read_text(encoding="utf-8")
        if any(k in fname for k in ("overwrite_packed_field", "drop_whole_packed_holder")) or (
            "PackedHolder" in text and ("drop_glue" in fname or "drop_in_place" in fname)
        ):
            snippets[fname] = _scrub(text, tmpdir)

    return {
        "native_rc": native_run.returncode,
        "native_stdout": native_run.stdout.strip(),
        "miri": miri_run,
        "dumped_mir_files_count": len(mir_files),
        "relevant_mir_files": sorted(snippets.keys()),
        "mir_snippets": snippets,
    }


def exp4_nested_packed_and_unwind_safety(tmpdir: str, env: dict[str, str]) -> dict[str, Any]:
    """Nested packed structs (packed(1) wrapping packed(4)) + panicking multi-field packed drop unwind safety."""
    src = r"""
use std::panic::{self, AssertUnwindSafe};
use std::sync::Mutex;

static LOG: Mutex<Vec<String>> = Mutex::new(Vec::new());

#[repr(C)]
#[allow(dead_code)]
struct Logged16 {
    val: u128,
    id: &'static str,
    should_panic: bool,
}

impl Drop for Logged16 {
    fn drop(&mut self) {
        let m = (self as *const Self).addr() % 16;
        LOG.lock().unwrap().push(format!("{}:mod16={}:panic={}", self.id, m, self.should_panic));
        if self.should_panic {
            panic!("intentional drop panic in {}", self.id);
        }
    }
}

#[repr(C, packed(4))]
#[allow(dead_code)]
struct InnerPacked4 {
    b1: u8,
    f1: Logged16,
    f2: Logged16,
}

#[repr(C, packed)]
#[allow(dead_code)]
struct OuterPacked1 {
    b0: u8,
    inner: InnerPacked4,
    tail: Logged16,
}

#[repr(align(16))]
struct Align16<T>(T);

#[inline(never)]
fn drop_nested_with_panic() -> (bool, usize, usize, usize) {
    let outer = Align16(OuterPacked1 {
        b0: 1,
        inner: InnerPacked4 {
            b1: 2,
            f1: Logged16 { val: 10, id: "inner.f1", should_panic: true },
            f2: Logged16 { val: 20, id: "inner.f2", should_panic: false },
        },
        tail: Logged16 { val: 30, id: "outer.tail", should_panic: false },
    });
    let m_f1 = (&raw const outer.0.inner.f1).addr() % 16;
    let m_f2 = (&raw const outer.0.inner.f2).addr() % 16;
    let m_tail = (&raw const outer.0.tail).addr() % 16;
    let caught = panic::catch_unwind(AssertUnwindSafe(move || {
        drop(outer);
    })).is_err();
    (caught, m_f1, m_f2, m_tail)
}

fn main() {
    assert_eq!(std::mem::align_of::<Logged16>(), 16);
    assert_eq!(std::mem::align_of::<InnerPacked4>(), 4);
    assert_eq!(std::mem::align_of::<OuterPacked1>(), 1);
    let (caught, m_f1, m_f2, m_tail) = drop_nested_with_panic();
    let entries = LOG.lock().unwrap().join(",");
    println!(
        "CAUGHT={} PRE_MOD16=({},{},{}) LOG=[{}]",
        caught, m_f1, m_f2, m_tail, entries
    );
}
"""
    rs = Path(tmpdir) / "exp4_nested_unwind.rs"
    bin_path = Path(tmpdir) / "exp4_nested_unwind"
    dump_dir = Path(tmpdir) / "exp4_mir_dump"
    dump_dir.mkdir(exist_ok=True)
    rs.write_text(src, encoding="utf-8")

    c = _run(
        [
            "rustc",
            "--edition=2021",
            "-C",
            "opt-level=0",
            "-C",
            "panic=unwind",
            "-C",
            "debuginfo=0",
            "-Z",
            "dump-mir=AddMovesForPackedDrops",
            "-Z",
            f"dump-mir-dir={dump_dir}",
            str(rs),
            "-o",
            str(bin_path),
        ],
        env=env,
    )
    assert c.returncode == 0, c.stderr
    native_run = _run([str(bin_path)], env=env)
    assert native_run.returncode == 0, native_run.stderr
    miri_run = _run_miri_single(src, "exp4_nested_unwind", tmpdir, env)

    shim_snippets: dict[str, str] = {}
    for f in sorted(dump_dir.iterdir()):
        if not f.is_file():
            continue
        text = f.read_text(encoding="utf-8")
        if ("OuterPacked1" in text or "InnerPacked4" in text) and (
            "drop_glue" in f.name or "drop_in_place" in f.name
        ):
            shim_snippets[f.name] = _scrub(text, tmpdir)

    return {
        "native_rc": native_run.returncode,
        "native_stdout": native_run.stdout.strip(),
        "miri": miri_run,
        "shim_mir_files": sorted(shim_snippets.keys()),
        "shim_mir_snippets": shim_snippets,
    }


def exp5_ub_checks_vs_miri_matrix(tmpdir: str, env: dict[str, str]) -> dict[str, Any]:
    """Empirical matrix proving the -Z ub-checks vs Miri alignment-check divergence across 8 cases."""
    common_types = r"""
use std::hint::black_box;
use std::mem::ManuallyDrop;

#[repr(C)]
#[allow(dead_code)]
struct DropU128([u128; 2]);

impl Drop for DropU128 {
    fn drop(&mut self) {
        let m = (self as *const Self).addr() % 16;
        println!("DROP_U128_MOD16={}", m);
    }
}

#[repr(align(64))]
#[allow(dead_code)]
struct Aligned64([u64; 8]);

impl Drop for Aligned64 {
    fn drop(&mut self) {
        let m = (self as *const Self).addr() % 64;
        println!("DROP_ALIGNED64_MOD64={}", m);
    }
}

#[allow(dead_code)]
struct DropLeaf(u64);

impl Drop for DropLeaf {
    fn drop(&mut self) {
        println!("DROP_LEAF_VAL={}", self.0);
    }
}

#[repr(C)]
#[allow(dead_code)]
struct GlueOnly16 {
    a: u128,
    inner: DropLeaf,
}

#[repr(C, packed)]
#[allow(dead_code)]
struct PackedManual {
    pad: u8,
    a: ManuallyDrop<DropU128>,
    g: ManuallyDrop<GlueOnly16>,
}

#[repr(align(16))]
struct Align16<T>(T);

#[repr(align(64))]
struct RawBuf64([u8; 192]);

fn make_packed() -> Align16<PackedManual> {
    black_box(Align16(PackedManual {
        pad: 0xAA,
        a: ManuallyDrop::new(DropU128([42, 43])),
        g: ManuallyDrop::new(GlueOnly16 { a: 7, inner: DropLeaf(99) }),
    }))
}

#[allow(dead_code)]
fn make_unaligned_aligned64_buf() -> RawBuf64 {
    let mut buf = RawBuf64([0u8; 192]);
    let ptr = unsafe { buf.0.as_mut_ptr().add(1).cast::<Aligned64>() };
    unsafe { core::ptr::write_unaligned(ptr, Aligned64([55; 8])) };
    black_box(buf)
}
"""

    cases: list[tuple[str, str]] = [
        (
            "case5a_direct_user_mut_ref_packed_u128",
            common_types
            + r"""
fn main() {
    let mut p = make_packed();
    let ptr: *mut DropU128 = (&raw mut p.0.a).cast();
    let pre_mod = ptr.addr() % 16;
    unsafe {
        let r: &mut DropU128 = &mut *ptr;
        println!("USER_MUT_REF_OK pre_mod={} addr_mod={}", pre_mod, (r as *const DropU128).addr() % 16);
    }
}
""",
        ),
        (
            "case5b_direct_user_mut_ref_aligned64",
            common_types
            + r"""
fn main() {
    let mut buf = make_unaligned_aligned64_buf();
    let ptr: *mut Aligned64 = unsafe { buf.0.as_mut_ptr().add(1).cast() };
    let pre_mod = ptr.addr() % 64;
    unsafe {
        let r: &mut Aligned64 = &mut *ptr;
        println!("USER_MUT_REF64_OK pre_mod={} addr_mod={}", pre_mod, (r as *const Aligned64).addr() % 64);
    }
}
""",
        ),
        (
            "case5c_direct_user_read_deref",
            common_types
            + r"""
fn main() {
    let p = make_packed();
    let ptr: *const DropU128 = (&raw const p.0.a).cast();
    let pre_mod = ptr.addr() % 16;
    unsafe {
        let v = (*ptr).0[0];
        println!("USER_READ_OK pre_mod={} v={}", pre_mod, v);
    }
}
""",
        ),
        (
            "case5d_drop_in_place_packed_u128",
            common_types
            + r"""
fn main() {
    let mut p = make_packed();
    let ptr: *mut DropU128 = (&raw mut p.0.a).cast();
    let pre_mod = ptr.addr() % 16;
    unsafe {
        core::ptr::drop_in_place(ptr);
    }
    println!("DROP_IN_PLACE_U128_DONE pre_mod={}", pre_mod);
}
""",
        ),
        (
            "case5e_drop_in_place_aligned64",
            common_types
            + r"""
fn main() {
    let mut buf = make_unaligned_aligned64_buf();
    let ptr: *mut Aligned64 = unsafe { buf.0.as_mut_ptr().add(1).cast() };
    let pre_mod = ptr.addr() % 64;
    unsafe {
        core::ptr::drop_in_place(ptr);
    }
    println!("DROP_IN_PLACE_ALIGNED64_DONE pre_mod={}", pre_mod);
}
""",
        ),
        (
            "case5f_drop_in_place_glue_field_only",
            common_types
            + r"""
fn main() {
    let mut p = make_packed();
    let ptr: *mut GlueOnly16 = (&raw mut p.0.g).cast();
    let pre_mod = ptr.addr() % 16;
    unsafe {
        core::ptr::drop_in_place(ptr);
    }
    println!("DROP_IN_PLACE_GLUE_DONE pre_mod={}", pre_mod);
}
""",
        ),
        (
            "case5g_generic_sized_inline_always_ref",
            common_types
            + r"""
#[inline(always)]
unsafe fn generic_sized_ref<'a, T>(ptr: *mut T) -> &'a mut T {
    unsafe { &mut *ptr }
}

fn main() {
    let mut p = make_packed();
    let ptr: *mut DropU128 = (&raw mut p.0.a).cast();
    let pre_mod = ptr.addr() % 16;
    unsafe {
        let r = generic_sized_ref(ptr);
        println!("GENERIC_SIZED_OK pre_mod={} addr_mod={}", pre_mod, (r as *const DropU128).addr() % 16);
    }
}
""",
        ),
        (
            "case5h_generic_unsized_inline_always_ref",
            common_types
            + r"""
#[inline(always)]
unsafe fn generic_unsized_ref<'a, T: ?Sized>(ptr: *mut T) -> &'a mut T {
    unsafe { &mut *ptr }
}

fn main() {
    let mut p = make_packed();
    let ptr: *mut DropU128 = (&raw mut p.0.a).cast();
    let pre_mod = ptr.addr() % 16;
    unsafe {
        let r = generic_unsized_ref(ptr);
        println!("GENERIC_UNSIZED_OK pre_mod={} addr_mod={}", pre_mod, (r as *const DropU128).addr() % 16);
    }
}
""",
        ),
        (
            "case5i_custom_mir_terminator_only_deref",
            r"""#![feature(custom_mir, core_intrinsics)]
use core::intrinsics::mir::*;
use std::hint::black_box;
use std::mem::ManuallyDrop;

#[repr(C)]
#[allow(dead_code)]
struct DropU128([u128; 2]);

#[repr(C, packed)]
#[allow(dead_code)]
struct PackedManual {
    pad: u8,
    a: ManuallyDrop<DropU128>,
}

#[repr(align(16))]
struct Align16<T>(T);

#[inline(never)]
fn sink(x: DropU128) -> u128 {
    black_box(x.0[0])
}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
unsafe fn call_terminator_deref(p: *const DropU128) -> u128 {
    mir! {
        let ret: u128;
        {
            Call(ret = sink(Move(*p)), ReturnTo(bb1), UnwindContinue())
        }
        bb1 = {
            RET = ret;
            Return()
        }
    }
}

fn main() {
    let p = black_box(Align16(PackedManual {
        pad: 0xAA,
        a: ManuallyDrop::new(DropU128([77, 88])),
    }));
    let ptr: *const DropU128 = (&raw const p.0.a).cast();
    let pre_mod = ptr.addr() % 16;
    let v = unsafe { call_terminator_deref(ptr) };
    println!("CUSTOM_MIR_TERM_DEREF_OK pre_mod={} v={}", pre_mod, v);
}
""",
        ),
    ]

    matrix: dict[str, Any] = {}
    for name, src in cases:
        rs = Path(tmpdir) / f"{name}.rs"
        rs.write_text(src, encoding="utf-8")
        entry: dict[str, Any] = {}

        configs = [
            ("native_O0_ub_yes", ["-C", "opt-level=0", "-Z", "ub-checks=yes"]),
            ("native_O2_ub_yes", ["-C", "opt-level=2", "-Z", "ub-checks=yes"]),
            ("native_O0_ub_no", ["-C", "opt-level=0", "-Z", "ub-checks=no"]),
        ]
        for cfg_name, flags in configs:
            bin_path = Path(tmpdir) / f"{name}_{cfg_name}"
            dump_dir = Path(tmpdir) / f"{name}_{cfg_name}_mir"
            extra = []
            if cfg_name == "native_O0_ub_yes":
                dump_dir.mkdir(exist_ok=True)
                extra = [
                    "-Z",
                    "dump-mir=CheckAlignment|Inline|SimplifyCfg-make_shim",
                    "-Z",
                    f"dump-mir-dir={dump_dir}",
                ]
            c = _run(
                [
                    "rustc",
                    "--edition=2021",
                    "-C",
                    "debuginfo=0",
                    *flags,
                    *extra,
                    str(rs),
                    "-o",
                    str(bin_path),
                ],
                env=env,
            )
            if c.returncode != 0:
                entry[cfg_name] = {
                    "compile_rc": c.returncode,
                    "compile_stderr": _scrub(c.stderr, tmpdir)[:400],
                }
                continue
            r = _run([str(bin_path)], env=env)
            rec: dict[str, Any] = {
                "rc": r.returncode,
                "stdout": _scrub(r.stdout, tmpdir).strip(),
                "stderr_head": _scrub(r.stderr, tmpdir).strip()[:320],
            }
            if cfg_name == "native_O0_ub_yes":
                assert_counts: dict[str, int] = {}
                for f in sorted(dump_dir.iterdir()):
                    if not f.is_file():
                        continue
                    txt = f.read_text(encoding="utf-8")
                    cnt = txt.count("misaligned pointer dereference")
                    if cnt > 0 or any(
                        k in f.name
                        for k in ("main", "drop_glue", "generic_", "call_terminator_deref")
                    ):
                        assert_counts[f.name] = cnt
                rec["mir_misaligned_assert_counts"] = assert_counts
            entry[cfg_name] = rec

        entry["miri"] = _run_miri_single(src, name, tmpdir, env)
        matrix[name] = entry

    return matrix


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", help="Optional path to write JSON output")
    args = parser.parse_args()

    env = _env_with_cargo()
    rustc_v = _run(["rustc", "--version", "--verbose"], env=env)
    miri_v = _run(["cargo", "miri", "--version"], env=env)
    assert rustc_v.returncode == 0, rustc_v.stderr

    with tempfile.TemporaryDirectory(prefix="packed_probe_") as tmpdir:
        report = {
            "toolchain": {
                "rustc_version_verbose": rustc_v.stdout.strip(),
                "miri_version": miri_v.stdout.strip(),
            },
            "exp1_layout_and_llvm_ir": exp1_layout_and_llvm_ir(tmpdir, env),
            "exp2_e0793_and_wfcheck_matrix": exp2_e0793_and_wfcheck_matrix(tmpdir, env),
            "exp3_add_moves_for_packed_drops": exp3_add_moves_for_packed_drops(tmpdir, env),
            "exp4_nested_packed_and_unwind_safety": exp4_nested_packed_and_unwind_safety(tmpdir, env),
            "exp5_ub_checks_vs_miri_matrix": exp5_ub_checks_vs_miri_matrix(tmpdir, env),
        }

    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.out:
        Path(args.out).write_text(rendered, encoding="utf-8")
        print(f"Wrote {args.out} ({len(rendered)} bytes)")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
