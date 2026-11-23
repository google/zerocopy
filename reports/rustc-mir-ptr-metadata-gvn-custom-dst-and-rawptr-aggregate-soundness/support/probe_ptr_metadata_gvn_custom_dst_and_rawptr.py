#!/usr/bin/env python3
"""Live rustc MIR/LLVM-IR + Miri (Stacked Borrows & Tree Borrows) differential probe.

Probes:
  - LowerIntrinsics (`ptr_metadata` -> `UnOp::PtrMetadata`,
    `aggregate_raw_ptr` -> `AggregateKind::RawPtr`) and `LowerSliceLenCalls`;
  - GVN `UnOp::PtrMetadata` folding asymmetry (`&[T; N] -> &[T]` folded vs.
    `&Wrapper<[u8; 3]> -> &Wrapper<[u8]>` unfolded);
  - `FakeForPtrMetadata` bounds-check generation vs. `&(*raw_wide_ptr)` vs.
    direct `ptr::metadata(raw_wide_ptr)` on dangling/null/unaligned pointers;
  - `Box<Wrapper<[u8]>>` deref elaboration (`Unique -> NonNull -> Transmute` in
    rustc 1.98 vs. `BoxRaw -> BoxDerefTransmute` at rust-lang/rust HEAD) and
    `rustc_codegen_ssa` `ScalarPair` + `PlaceRef::project_field` LLVM O0/O2 IR;
  - A 15-case Miri differential litmus matrix executed under both default
    Stacked Borrows and `-Zmiri-tree-borrows`.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import socket
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


MAIN_PROBE_SOURCE = r'''#![feature(core_intrinsics, ptr_metadata)]
#![allow(dead_code, internal_features, unused_unsafe)]

use std::ptr::{self, DynMetadata};

pub trait Summarize {
    fn score(&self) -> u32;
}

#[repr(C)]
pub struct Concrete {
    pub a: u32,
    pub b: u64,
}

impl Summarize for Concrete {
    #[inline(never)]
    fn score(&self) -> u32 {
        self.a.wrapping_add(self.b as u32)
    }
}

#[repr(C)]
pub struct Inner<T: ?Sized> {
    pub tag: u16,
    pub tail: T,
}

#[repr(C)]
pub struct Wrapper<T: ?Sized> {
    pub head: u8,
    pub inner: Inner<T>,
}

const CONST_META_RAW_SLICE: usize = {
    let p: *const [u8] = ptr::from_raw_parts(ptr::null::<()>(), 5);
    ptr::metadata(p)
};

const CONST_META_WRAPPER: usize = {
    let w = Wrapper { head: 1, inner: Inner { tag: 2, tail: [10u8, 20, 30] } };
    let u: &Wrapper<[u8]> = &w;
    ptr::metadata(u)
};

#[inline(never)]
pub fn probe_a_array_to_slice(arr: &[u32; 4]) -> (usize, usize, u32) {
    let s: &[u32] = arr;
    let meta: usize = core::ptr::metadata(s);
    (meta, s.len(), s[2])
}

#[inline(never)]
pub fn probe_b_trait_obj_metadata(c: &Concrete) -> (usize, usize, u32) {
    let obj: &dyn Summarize = c;
    let meta: DynMetadata<dyn Summarize> = core::ptr::metadata(obj);
    (meta.size_of(), meta.align_of(), obj.score())
}

#[inline(never)]
pub fn probe_c_nested_struct_unsize_ref(w: &Wrapper<[u8; 3]>) -> (usize, u8, u16, usize, u8) {
    let u: &Wrapper<[u8]> = w;
    let meta: usize = core::ptr::metadata(u);
    (meta, u.head, u.inner.tag, u.inner.tail.len(), u.inner.tail[2])
}

#[inline(never)]
pub fn probe_c_nested_struct_unsize_box(w: Box<Wrapper<[u8; 3]>>) -> (usize, u8, u16, u8) {
    let u: Box<Wrapper<[u8]>> = w;
    let meta: usize = core::ptr::metadata(&*u);
    (meta, u.head, u.inner.tag, u.inner.tail[1])
}

#[inline(never)]
pub fn probe_d_from_raw_parts_roundtrip(
    arr: &[u32; 4],
    c: &Concrete,
    w: &Wrapper<[u8; 3]>,
) -> (u32, u32, u8, u8, usize, usize, usize, bool) {
    // 1. Slice round-trip
    let s: &[u32] = arr;
    let s_ptr: *const [u32] = s;
    let s_data: *const () = s_ptr.cast::<()>();
    let s_meta: usize = core::ptr::metadata(s_ptr);
    let s_rebuilt: *const [u32] = core::ptr::from_raw_parts(s_data, s_meta);
    let s_val = unsafe { (&*s_rebuilt)[3] };

    // 2. Trait object round-trip
    let obj: &dyn Summarize = c;
    let obj_ptr: *const dyn Summarize = obj;
    let obj_data: *const () = obj_ptr.cast::<()>();
    let obj_meta = core::ptr::metadata(obj_ptr);
    let obj_rebuilt: *const dyn Summarize = core::ptr::from_raw_parts(obj_data, obj_meta);
    let obj_val = unsafe { (&*obj_rebuilt).score() };

    // 3. Nested custom DST struct round-trip
    let wu: &Wrapper<[u8]> = w;
    let wu_ptr: *const Wrapper<[u8]> = wu;
    let wu_data: *const () = wu_ptr.cast::<()>();
    let wu_meta: usize = core::ptr::metadata(wu_ptr);
    let wu_rebuilt: *const Wrapper<[u8]> = core::ptr::from_raw_parts(wu_data, wu_meta);
    let (wu_head, wu_last) = unsafe { ((*wu_rebuilt).head, (*wu_rebuilt).inner.tail[2]) };

    // 4. Null & unaligned dangling raw wide pointers (metadata without deref)
    let null_slice: *const [u32] = core::ptr::from_raw_parts(core::ptr::null::<()>(), 17);
    let unaligned_dst: *const Wrapper<[u8]> =
        core::ptr::from_raw_parts(core::ptr::without_provenance::<()>(1), 9);

    // 5. Thin pointer via aggregate_raw_ptr with unit metadata
    let thin_rebuilt: *const u32 =
        unsafe { std::intrinsics::aggregate_raw_ptr(arr.as_ptr().cast::<()>(), ()) };

    (
        s_val,
        obj_val,
        wu_head,
        wu_last,
        core::ptr::metadata(null_slice),
        core::ptr::metadata(unaligned_dst),
        CONST_META_RAW_SLICE + CONST_META_WRAPPER,
        thin_rebuilt == arr.as_ptr(),
    )
}

#[inline(never)]
fn mutate_and_index(w: &mut Wrapper<[u8]>) -> usize {
    w.head = 42;
    w.inner.tag = 999;
    1
}

#[inline(never)]
pub fn probe_e_fake_for_ptr_metadata_and_mut_raw_parts(
    mut w: Wrapper<[u8; 3]>,
) -> (u8, u16, u8, u8) {
    let wu: &mut Wrapper<[u8]> = &mut w;
    let raw_mut: *mut Wrapper<[u8]> = wu as *mut Wrapper<[u8]>;
    let data_mut: *mut () = raw_mut.cast::<()>();
    let meta: usize = core::ptr::metadata(raw_mut);
    let rebuilt: *mut Wrapper<[u8]> = core::ptr::from_raw_parts_mut(data_mut, meta);
    unsafe {
        (*rebuilt).inner.tail[2] = 77;
        let idx = mutate_and_index(&mut *rebuilt);
        let elem = (*rebuilt).inner.tail[idx];
        ((*rebuilt).head, (*rebuilt).inner.tag, elem, (*rebuilt).inner.tail[2])
    }
}

fn main() {
    let arr = std::hint::black_box([10u32, 20, 30, 40]);
    let c = std::hint::black_box(Concrete { a: 7, b: 35 });
    let w = std::hint::black_box(Wrapper {
        head: 9,
        inner: Inner { tag: 513, tail: [101u8, 102, 103] },
    });
    let wb = Box::new(Wrapper {
        head: 5,
        inner: Inner { tag: 77, tail: [11u8, 22, 33] },
    });
    let wm = std::hint::black_box(Wrapper {
        head: 1,
        inner: Inner { tag: 2, tail: [11u8, 22, 33] },
    });

    let ra = probe_a_array_to_slice(&arr);
    let rb = probe_b_trait_obj_metadata(&c);
    let rc_ref = probe_c_nested_struct_unsize_ref(&w);
    let rc_box = probe_c_nested_struct_unsize_box(wb);
    let rd = probe_d_from_raw_parts_roundtrip(&arr, &c, &w);
    let re = probe_e_fake_for_ptr_metadata_and_mut_raw_parts(wm);
    println!(
        "{{\"A\":[{},{},{}],\"B\":[{},{},{}],\"C_REF\":[{},{},{},{},{}],\"C_BOX\":[{},{},{},{}],\"D\":[{},{},{},{},{},{},{},{}],\"E\":[{},{},{},{}]}}",
        ra.0, ra.1, ra.2,
        rb.0, rb.1, rb.2,
        rc_ref.0, rc_ref.1, rc_ref.2, rc_ref.3, rc_ref.4,
        rc_box.0, rc_box.1, rc_box.2, rc_box.3,
        rd.0, rd.1, rd.2, rd.3, rd.4, rd.5, rd.6, if rd.7 { "true" } else { "false" },
        re.0, re.1, re.2, re.3,
    );
}
'''


LITMUS_PRELUDE = r'''#![feature(core_intrinsics, ptr_metadata)]
#![allow(dead_code, internal_features, unused_imports, unused_unsafe)]

use std::mem::{self, MaybeUninit};
use std::ptr::{self, DynMetadata};

#[repr(align(8))]
struct AlignedBacking([u8; 32]);

pub trait Summarize {
    fn score(&self) -> u32;
}

#[repr(C)]
pub struct Concrete {
    pub a: u32,
    pub b: u64,
}

impl Summarize for Concrete {
    fn score(&self) -> u32 {
        self.a.wrapping_add(self.b as u32)
    }
}

#[repr(C)]
pub struct Inner<T: ?Sized> {
    pub tag: u16,
    pub tail: T,
}

#[repr(C)]
pub struct Wrapper<T: ?Sized> {
    pub head: u8,
    pub inner: Inner<T>,
}
'''


# (case_id, expect_sb_pass, expect_tb_pass, description, body)
LITMUS_CASES: list[tuple[str, bool, bool, str, str]] = [
    (
        "l01_pass_metadata_null_raw_slice",
        True,
        True,
        "ptr::metadata on null *const [u32] reads metadata without deref or null check",
        r'''
fn main() {
    let p: *const [u32] = ptr::from_raw_parts(ptr::null::<()>(), 42);
    assert_eq!(ptr::metadata(p), 42);
}
''',
    ),
    (
        "l02_pass_metadata_unaligned_dangling_raw_custom_dst",
        True,
        True,
        "ptr::metadata on unaligned/no-provenance *const Wrapper<[u8]> avoids OffsetMode::Inbounds",
        r'''
fn main() {
    let p: *const Wrapper<[u8]> = ptr::from_raw_parts(ptr::without_provenance::<()>(1), 99);
    assert_eq!(ptr::metadata(p), 99);
}
''',
    ),
    (
        "l03_pass_metadata_freed_box_raw_slice",
        True,
        True,
        "ptr::metadata on freed Box<[u8]> raw wide pointer succeeds in both SB and TB",
        r'''
fn main() {
    let b: Box<[u8]> = Box::new([1u8, 2, 3, 4]);
    let p: *const [u8] = &*b;
    drop(b);
    assert_eq!(ptr::metadata(p), 4);
}
''',
    ),
    (
        "l04_pass_metadata_freed_box_raw_dyn",
        True,
        True,
        "ptr::metadata + DynMetadata::{size_of, align_of} on freed *const dyn Summarize",
        r'''
fn main() {
    let b: Box<Concrete> = Box::new(Concrete { a: 7, b: 35 });
    let p: *const dyn Summarize = &*b;
    drop(b);
    let m: DynMetadata<dyn Summarize> = ptr::metadata(p);
    assert_eq!((m.size_of(), m.align_of()), (16, 8));
}
''',
    ),
    (
        "l05_pass_metadata_oversized_raw_slice",
        True,
        True,
        "ptr::metadata on *const [u64] with len = usize::MAX (> isize::MAX bytes) passes",
        r'''
fn main() {
    let p: *const [u64] = ptr::from_raw_parts(ptr::without_provenance::<()>(8), usize::MAX);
    assert_eq!(ptr::metadata(p), usize::MAX);
}
''',
    ),
    (
        "l06_pass_fake_for_ptr_metadata_mut_slice_and_wrapper",
        True,
        True,
        "FakeForPtrMetadata bounds check on &mut [u32] and &mut Wrapper<[u8]> overlaps &mut call",
        r'''
fn mutate_slice(s: &mut [u32]) -> usize {
    s[0] += 1;
    2
}
fn mutate_wrap(w: &mut Wrapper<[u8]>) -> usize {
    w.head = 42;
    w.inner.tag = 999;
    1
}
fn main() {
    let mut arr = [10u32, 20, 30, 40];
    let s: &mut [u32] = &mut arr;
    let v = s[mutate_slice(s)];
    assert_eq!((v, arr[0]), (30, 11));

    let mut w = Wrapper { head: 1, inner: Inner { tag: 2, tail: [11u8, 22, 33] } };
    let wu: &mut Wrapper<[u8]> = &mut w;
    let tv = wu.inner.tail[mutate_wrap(wu)];
    assert_eq!((tv, w.head, w.inner.tag), (22, 42, 999));
}
''',
    ),
    (
        "l07_pass_from_raw_parts_mut_custom_dst_write",
        True,
        True,
        "from_raw_parts_mut::<Wrapper<[u8]>> preserves mutable provenance through round-trip",
        r'''
fn main() {
    let mut w = Wrapper { head: 3, inner: Inner { tag: 5, tail: [1u8, 2, 3] } };
    let wu: &mut Wrapper<[u8]> = &mut w;
    let p: *mut Wrapper<[u8]> = wu as *mut Wrapper<[u8]>;
    let data: *mut () = p.cast::<()>();
    let meta: usize = ptr::metadata(p);
    let rebuilt: *mut Wrapper<[u8]> = ptr::from_raw_parts_mut(data, meta);
    unsafe {
        (*rebuilt).inner.tail[1] = 77;
    }
    assert_eq!(w.inner.tail, [1, 77, 3]);
}
''',
    ),
    (
        "l08_pass_const_eval_ptr_metadata_and_raw_parts",
        True,
        True,
        "CTFE evaluates ptr::metadata on null raw slice and unsized Wrapper<[u8]>",
        r'''
const C_RAW: usize = ptr::metadata(ptr::from_raw_parts::<[u8]>(ptr::null::<()>(), 5));
const C_WRAP: usize = {
    let w = Wrapper { head: 1, inner: Inner { tag: 2, tail: [10u8, 20, 30] } };
    let u: &Wrapper<[u8]> = &w;
    ptr::metadata(u)
};
fn main() {
    assert_eq!((C_RAW, C_WRAP), (5, 3));
}
''',
    ),
    (
        "l09_ub_deref_ref_reborrow_null_raw_slice",
        False,
        False,
        "Creating &*raw_ptr on null *const [u32] triggers null-reference UB",
        r'''
fn main() {
    let p: *const [u32] = ptr::from_raw_parts(ptr::null::<()>(), 4);
    let _r: &[u32] = unsafe { &*p };
}
''',
    ),
    (
        "l10_ub_deref_ref_reborrow_freed_box_raw_slice",
        False,
        False,
        "Creating &*raw_ptr on freed Box<[u8]> triggers use-after-free UB",
        r'''
fn main() {
    let b: Box<[u8]> = Box::new([1u8, 2, 3, 4]);
    let p: *const [u8] = &*b;
    drop(b);
    let _r: &[u8] = unsafe { &*p };
}
''',
    ),
    (
        "l11_ub_deref_ref_reborrow_unaligned_custom_dst",
        False,
        False,
        "Creating &*raw_ptr on unaligned/dangling *const Wrapper<[u8]> triggers UB",
        r'''
fn main() {
    let p: *const Wrapper<[u8]> = ptr::from_raw_parts(ptr::without_provenance::<()>(1), 3);
    let _r: &Wrapper<[u8]> = unsafe { &*p };
}
''',
    ),
    (
        "l12_ub_project_nonzero_field_on_dangling_custom_dst",
        False,
        False,
        "&raw const (*p).inner.tail on dangling *const Wrapper<[u8]> fails OffsetMode::Inbounds",
        r'''
fn main() {
    let p: *const Wrapper<[u8]> = ptr::from_raw_parts(ptr::without_provenance::<()>(2), 3);
    let _tail: *const [u8] = unsafe { &raw const (*p).inner.tail };
}
''',
    ),
    (
        "l13_ub_forged_vtable_raw_parts_dyn",
        False,
        False,
        "from_raw_parts::<dyn Summarize> with forged stack vtable fails wide-ptr validity",
        r'''
fn main() {
    let fake_vt: [usize; 4] = [0; 4];
    let bad_meta: DynMetadata<dyn Summarize> = unsafe { mem::transmute(&fake_vt) };
    let p: *const dyn Summarize = ptr::from_raw_parts(ptr::null::<()>(), bad_meta);
    let _ = ptr::metadata(p);
}
''',
    ),
    (
        "l14a_198_raw_box_deref_unaligned_transmute_gap",
        True,
        True,
        "In rustc 1.98 (Unique->NonNull->Transmute), &raw const (*b) on unaligned Box slot avoids UB",
        r'''
fn main() {
    let mut backing = AlignedBacking([0u8; 32]);
    let mut b: Box<Wrapper<[u8]>> = Box::new(Wrapper {
        head: 1,
        inner: Inner { tag: 2, tail: [10u8, 20, 30] },
    });
    let slot_ptr: *mut *mut Wrapper<[u8]> = (&raw mut b).cast::<*mut Wrapper<[u8]>>();
    let unaligned_ptr: *mut Wrapper<[u8]> =
        ptr::from_raw_parts_mut(unsafe { backing.0.as_mut_ptr().add(1) }, 3);
    unsafe {
        let orig_ptr = ptr::read(slot_ptr);
        ptr::write(slot_ptr, unaligned_ptr);
        let raw_p: *const Wrapper<[u8]> = &raw const (*b);
        let m = ptr::metadata(raw_p);
        ptr::write(slot_ptr, orig_ptr);
        assert_eq!(m, 3);
    }
}
''',
    ),
    (
        "l14b_ub_ref_box_deref_unaligned",
        False,
        False,
        "Ref deref &(*b) on unaligned Box slot triggers unaligned reference UB",
        r'''
fn main() {
    let mut backing = AlignedBacking([0u8; 32]);
    let mut b: Box<Wrapper<[u8]>> = Box::new(Wrapper {
        head: 1,
        inner: Inner { tag: 2, tail: [10u8, 20, 30] },
    });
    let slot_ptr: *mut *mut Wrapper<[u8]> = (&raw mut b).cast::<*mut Wrapper<[u8]>>();
    let unaligned_ptr: *mut Wrapper<[u8]> =
        ptr::from_raw_parts_mut(unsafe { backing.0.as_mut_ptr().add(1) }, 3);
    unsafe {
        let orig_ptr = ptr::read(slot_ptr);
        ptr::write(slot_ptr, unaligned_ptr);
        let _ref_p: &Wrapper<[u8]> = &(*b);
        ptr::write(slot_ptr, orig_ptr);
    }
}
''',
    ),
]


def scrub_text(text: str, replacements: list[tuple[str, str]]) -> str:
    out = text
    for needle, repl in replacements:
        if needle:
            out = out.replace(needle, repl)
    home_str = str(Path.home())
    if home_str:
        out = out.replace(home_str, "<USER_HOME>")
    user_name = os.environ.get("USER", "")
    if user_name:
        out = out.replace(f"/home/{user_name}", "<USER_HOME>")
    tmp_root = str(Path(tempfile.gettempdir()))
    if tmp_root:
        out = re.sub(re.escape(tmp_root) + r"/[^\s:\"']+", "<TMP>", out)
    return out


def extract_mir_functions(mir_text: str) -> dict[str, str]:
    fns: dict[str, str] = {}
    cur_name: str | None = None
    cur_lines: list[str] = []
    brace_depth = 0
    header_re = re.compile(r"^fn\s+([A-Za-z0-9_]+)\s*\(")
    for line in mir_text.splitlines():
        if cur_name is None:
            m = header_re.match(line)
            if m:
                cur_name = m.group(1)
                cur_lines = [line]
                brace_depth = line.count("{") - line.count("}")
        else:
            cur_lines.append(line)
            brace_depth += line.count("{") - line.count("}")
            if brace_depth <= 0:
                fns[cur_name] = "\n".join(cur_lines)
                cur_name = None
                cur_lines = []
    return fns


def extract_llvm_functions(ll_text: str) -> dict[str, str]:
    fns: dict[str, str] = {}
    cur_name: str | None = None
    cur_lines: list[str] = []
    header_re = re.compile(r"^define\s+.*@([A-Za-z0-9_.$]+)\(")
    for line in ll_text.splitlines():
        if cur_name is None:
            m = header_re.match(line)
            if m:
                cur_name = m.group(1)
                cur_lines = [line]
        else:
            cur_lines.append(line)
            if line.strip() == "}":
                fns[cur_name] = "\n".join(cur_lines)
                cur_name = None
                cur_lines = []
    return fns


def summarize_mir_body(body: str) -> dict[str, Any]:
    return {
        "ptr_metadata_ops": len(re.findall(r"\bPtrMetadata\(", body)),
        "unsize_coercions": len(re.findall(r"PointerCoercion\(Unsize", body)),
        "raw_ptr_aggregates": len(re.findall(r"\*const\b.*from\s*\(|\*mut\b.*from\s*\(|Aggregate.*RawPtr", body)),
        "fake_for_ptr_metadata": len(re.findall(r"&raw const \(fake\)", body)),
        "ptr_to_ptr_casts": len(re.findall(r"\(PtrToPtr\)", body)),
        "box_deref_transmutes": len(re.findall(r"\(BoxDerefTransmute\)", body)),
        "transmutes": len(re.findall(r"\(Transmute\)", body)),
        "slice_len_calls": len(re.findall(r"::len\(", body)),
        "const_4_usize": "const 4_usize" in body,
        "const_3_usize": "const 3_usize" in body,
    }


def collect_dump_mir_passes(dump_dir: Path, fn_substr: str, replacements: list[tuple[str, str]]) -> dict[str, str]:
    passes = [
        "built.after.mir",
        "ElaborateBoxDerefs.after.mir",
        "LowerIntrinsics.after.mir",
        "LowerSliceLenCalls.after.mir",
        "InstSimplify-before-inline.after.mir",
        "Inline.after.mir",
        "GVN.after.mir",
        "runtime-optimized.after.mir",
    ]
    out: dict[str, str] = {}
    files = sorted(dump_dir.glob(f"*{fn_substr}*.mir"))
    for p_suffix in passes:
        for f in files:
            if f.name.endswith(p_suffix):
                out[p_suffix] = scrub_text(f.read_text(encoding="utf-8"), replacements)
                break
    return out


def ensure_miri_sysroot(env: dict[str, str], tmpdir: Path, sysroot: Path, target_triple: str) -> tuple[str, Path | None]:
    """Use prebuilt cargo-miri sysroot if available, otherwise build a minimal std-free core sysroot?
    Note: litmus cases use `std::` so try `cargo miri setup --print-sysroot --offline` first."""
    proc = subprocess.run(
        ["cargo", "miri", "setup", "--print-sysroot", "--offline"],
        env=env,
        capture_output=True,
        text=True,
    )
    if proc.returncode == 0 and proc.stdout.strip():
        return proc.stdout.strip(), None
    # Fallback: build sysroot without --offline if cache missing
    proc2 = subprocess.run(
        ["cargo", "miri", "setup", "--print-sysroot"],
        env=env,
        capture_output=True,
        text=True,
    )
    if proc2.returncode == 0 and proc2.stdout.strip():
        return proc2.stdout.strip(), None
    raise RuntimeError(f"Failed to locate Miri sysroot:\n{proc.stderr}\n{proc2.stderr}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).resolve().parent / "ptr_metadata_gvn_custom_dst_probe_results.json",
        help="Output JSON file path",
    )
    args = parser.parse_args()

    env = os.environ.copy()
    cargo_bin = Path.home() / ".cargo" / "bin"
    if cargo_bin.is_dir():
        env["PATH"] = f"{cargo_bin}:{env.get('PATH', '')}"

    rustc_ver = subprocess.run(["rustc", "-vV"], env=env, check=True, capture_output=True, text=True).stdout.strip()
    sysroot = Path(subprocess.run(["rustc", "--print", "sysroot"], env=env, check=True, capture_output=True, text=True).stdout.strip())
    miri_ver = subprocess.run(["cargo", "miri", "--version"], env=env, check=True, capture_output=True, text=True).stdout.strip()
    miri_bin = sysroot / "bin" / "miri"
    if not miri_bin.is_file():
        raise RuntimeError(f"miri driver binary not found at {miri_bin}")

    target_triple = "x86_64-unknown-linux-gnu"
    for line in rustc_ver.splitlines():
        if line.startswith("host:"):
            target_triple = line.split(":", 1)[1].strip()

    hostname = socket.gethostname()

    with tempfile.TemporaryDirectory(prefix="ptr_meta_probe_") as tmp_str:
        tmpdir = Path(tmp_str)
        replacements = [
            (str(sysroot), "<SYSROOT>"),
            (str(tmpdir), "<TMPDIR>"),
            (hostname, "<HOST>"),
        ]

        crate_dir = tmpdir / "probe_crate"
        (crate_dir / "src").mkdir(parents=True, exist_ok=True)
        (crate_dir / "Cargo.toml").write_text(
            '[package]\nname = "probe_ptr_meta"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        main_rs = crate_dir / "src" / "main.rs"
        main_rs.write_text(MAIN_PROBE_SOURCE, encoding="utf-8")

        # 1. Native execution
        native_bin = tmpdir / "probe_native_o2"
        subprocess.run(
            ["rustc", "--edition=2024", "-Copt-level=2", "--crate-name=probe_ptr_meta", str(main_rs), "-o", str(native_bin)],
            env=env,
            check=True,
            capture_output=True,
            text=True,
        )
        native_stdout = subprocess.run([str(native_bin)], env=env, check=True, capture_output=True, text=True).stdout.strip()
        native_data = json.loads(native_stdout)

        # 2. Cargo +nightly miri run (Stacked Borrows and Tree Borrows) on the 5 main probes
        sb_run = subprocess.run(
            ["cargo", "miri", "run", "--offline"],
            cwd=crate_dir,
            env=env,
            check=True,
            capture_output=True,
            text=True,
        )
        tb_env = env.copy()
        tb_env["MIRIFLAGS"] = "-Zmiri-tree-borrows"
        tb_run = subprocess.run(
            ["cargo", "miri", "run", "--offline"],
            cwd=crate_dir,
            env=tb_env,
            check=True,
            capture_output=True,
            text=True,
        )
        miri_sb_data = json.loads(sb_run.stdout.strip())
        miri_tb_data = json.loads(tb_run.stdout.strip())
        assert miri_sb_data == native_data, f"SB mismatch: {miri_sb_data} != {native_data}"
        assert miri_tb_data == native_data, f"TB mismatch: {miri_tb_data} != {native_data}"

        # 3. MIR opt sweep (-Zmir-opt-level=0, 1, 2 at -Copt-level=0) & full -Zdump-mir=all at O2
        target_fns = [
            "probe_a_array_to_slice",
            "probe_b_trait_obj_metadata",
            "probe_c_nested_struct_unsize_ref",
            "probe_c_nested_struct_unsize_box",
            "probe_d_from_raw_parts_roundtrip",
            "probe_e_fake_for_ptr_metadata_and_mut_raw_parts",
        ]
        mir_opt_sweep: dict[str, Any] = {}
        for opt_lvl in (0, 1, 2):
            mdir = tmpdir / f"emit_mir_{opt_lvl}"
            mdir.mkdir(parents=True, exist_ok=True)
            subprocess.run(
                [
                    "rustc",
                    "--edition=2024",
                    "--crate-name=probe_ptr_meta",
                    f"-Zmir-opt-level={opt_lvl}",
                    "-Copt-level=0",
                    "--emit=mir",
                    "--out-dir",
                    str(mdir),
                    str(main_rs),
                ],
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )
            mir_text = (mdir / "probe_ptr_meta.mir").read_text(encoding="utf-8")
            fn_map = extract_mir_functions(mir_text)
            mir_opt_sweep[f"mir_opt_level_{opt_lvl}"] = {
                fn: summarize_mir_body(fn_map[fn]) for fn in target_fns if fn in fn_map
            }

        # Dump all passes under -Copt-level=2 (-Zmir-opt-level=2) and emit LLVM IR at O0 and O2
        dump_dir = tmpdir / "mir_dump_o2"
        dump_dir.mkdir(parents=True, exist_ok=True)
        o2_bin = tmpdir / "probe_dump_o2"
        subprocess.run(
            [
                "rustc",
                "--edition=2024",
                "--crate-name=probe_ptr_meta",
                "-Copt-level=2",
                "-Zdump-mir=all",
                f"-Zdump-mir-dir={dump_dir}",
                str(main_rs),
                "-o",
                str(o2_bin),
            ],
            env=env,
            check=True,
            capture_output=True,
            text=True,
        )
        per_probe_mir = {
            fn: collect_dump_mir_passes(dump_dir, fn, replacements) for fn in target_fns
        }

        ll_o0_dir = tmpdir / "llvm_o0"
        ll_o2_dir = tmpdir / "llvm_o2"
        ll_o0_dir.mkdir(parents=True, exist_ok=True)
        ll_o2_dir.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["rustc", "--edition=2024", "--crate-name=probe_ptr_meta", "-Copt-level=0", "--emit=llvm-ir", "--out-dir", str(ll_o0_dir), str(main_rs)],
            env=env,
            check=True,
            capture_output=True,
            text=True,
        )
        subprocess.run(
            ["rustc", "--edition=2024", "--crate-name=probe_ptr_meta", "-Copt-level=2", "--emit=llvm-ir", "--out-dir", str(ll_o2_dir), str(main_rs)],
            env=env,
            check=True,
            capture_output=True,
            text=True,
        )
        ll_o0_text = (ll_o0_dir / "probe_ptr_meta.ll").read_text(encoding="utf-8")
        ll_o2_text = (ll_o2_dir / "probe_ptr_meta.ll").read_text(encoding="utf-8")
        ll_o0_fns = extract_llvm_functions(ll_o0_text)
        ll_o2_fns = extract_llvm_functions(ll_o2_text)

        vtable_globals = [
            scrub_text(line.strip(), replacements)
            for line in ll_o0_text.splitlines()
            if line.startswith("@vtable.")
        ]

        per_probe_llvm: dict[str, Any] = {}
        for fn in target_fns:
            m0 = next((k for k in ll_o0_fns if fn in k), None)
            m2 = next((k for k in ll_o2_fns if fn in k), None)
            per_probe_llvm[fn] = {
                "o0": scrub_text(ll_o0_fns[m0], replacements) if m0 else None,
                "o2": scrub_text(ll_o2_fns[m2], replacements) if m2 else None,
            }

        # 4. 15-case Miri Differential Litmus Matrix (Stacked Borrows vs Tree Borrows)
        miri_sysroot, _ = ensure_miri_sysroot(env, tmpdir, sysroot, target_triple)
        litmus_results: list[dict[str, Any]] = []
        for case_id, exp_sb, exp_tb, desc, body in LITMUS_CASES:
            case_rs = tmpdir / f"{case_id}.rs"
            case_rs.write_text(LITMUS_PRELUDE + "\n" + body, encoding="utf-8")

            row: dict[str, Any] = {
                "case_id": case_id,
                "description": desc,
                "expected_sb": "PASS" if exp_sb else "UB",
                "expected_tb": "PASS" if exp_tb else "UB",
            }
            for mode_name, extra_flags, exp_ok in (
                ("stacked_borrows", [], exp_sb),
                ("tree_borrows", ["-Zmiri-tree-borrows"], exp_tb),
            ):
                proc = subprocess.run(
                    [
                        str(miri_bin),
                        "--edition=2024",
                        f"--sysroot={miri_sysroot}",
                        *extra_flags,
                        str(case_rs),
                    ],
                    env=env,
                    capture_output=True,
                    text=True,
                )
                passed = proc.returncode == 0
                if passed != exp_ok:
                    raise RuntimeError(
                        f"Litmus {case_id} ({mode_name}) expected pass={exp_ok}, got rc={proc.returncode}:\n{proc.stderr}"
                    )
                ub_msg = None
                for line in proc.stderr.splitlines():
                    if "Undefined Behavior:" in line:
                        ub_msg = scrub_text(line.strip(), replacements)
                        break
                row[mode_name] = {
                    "observed": "PASS" if passed else "UB",
                    "exit_code": proc.returncode,
                    "ub_diagnostic": ub_msg,
                }
            litmus_results.append(row)

    payload = {
        "toolchain": {
            "rustc_verbose_version": scrub_text(rustc_ver, []),
            "miri_version": scrub_text(miri_ver, []),
            "target_triple": target_triple,
        },
        "main_4plus1_probes": {
            "native_o2_stdout": native_data,
            "miri_stacked_borrows_stdout": miri_sb_data,
            "miri_tree_borrows_stdout": miri_tb_data,
            "mir_opt_sweep": mir_opt_sweep,
            "vtable_globals_llvm_o0": vtable_globals,
            "per_probe_mir_passes": per_probe_mir,
            "per_probe_llvm_ir": per_probe_llvm,
        },
        "miri_differential_litmus": {
            "total_cases": len(litmus_results),
            "sb_matched": sum(1 for r in litmus_results if r["stacked_borrows"]["observed"] == r["expected_sb"]),
            "tb_matched": sum(1 for r in litmus_results if r["tree_borrows"]["observed"] == r["expected_tb"]),
            "cases": litmus_results,
        },
    }

    args.out.parent.mkdir(parents=True, exist_ok=True)
    serialized = json.dumps(payload, indent=2, sort_keys=False) + "\n"
    home_str = str(Path.home())
    tmp_root = str(Path(tempfile.gettempdir())) + "/"
    user_name = os.environ.get("USER", "")
    for forbidden in (home_str, tmp_root, hostname, user_name):
        if forbidden and forbidden in serialized:
            raise AssertionError(f"Forbidden host/path substring {forbidden!r} leaked into JSON output")
    args.out.write_text(serialized, encoding="utf-8")
    print(
        f"Wrote {args.out.name} "
        f"({len(litmus_results)}/{len(litmus_results)} SB & TB litmus matched, "
        f"3 MIR opt levels, O0/O2 LLVM IR)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
