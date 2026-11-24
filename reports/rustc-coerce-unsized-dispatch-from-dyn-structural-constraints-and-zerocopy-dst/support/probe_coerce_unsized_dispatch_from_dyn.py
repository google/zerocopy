#!/usr/bin/env python3
"""Live rustc & zerocopy probes for CoerceUnsized, DispatchFromDyn, Unsize, and KnownLayout DSTs."""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path
from typing import Any


def resolve_rustc() -> str:
    env_rustc = os.environ.get("RUSTC")
    if env_rustc:
        return env_rustc
    found = shutil.which("rustc")
    if found:
        return found
    cargo_rustc = Path.home() / ".cargo" / "bin" / "rustc"
    if cargo_rustc.exists():
        return str(cargo_rustc)
    raise FileNotFoundError("rustc executable not found in RUSTC, PATH, or ~/.cargo/bin/rustc")


def resolve_zerocopy_src(cli_arg: str | None) -> Path:
    candidates: list[Path] = []
    if cli_arg:
        candidates.append(Path(cli_arg))
    if os.environ.get("ZEROCOPY_SRC"):
        candidates.append(Path(os.environ["ZEROCOPY_SRC"]))
    here = Path(__file__).resolve()
    for parent in here.parents:
        candidates.append(parent)
        candidates.append(parent / "zerocopy")
    projects_dir = Path.home() / "Projects"
    if projects_dir.is_dir():
        for sub in sorted(projects_dir.iterdir()):
            candidates.append(sub / "zerocopy" / "zerocopy")
            candidates.append(sub / "zerocopy")
    workspace_dir = Path.home() / "workspace"
    if workspace_dir.is_dir():
        candidates.append(workspace_dir / "zerocopy" / "zerocopy")
        candidates.append(workspace_dir / "zerocopy")
    for cand in candidates:
        if (cand / "src" / "lib.rs").is_file() and (cand / "Cargo.toml").is_file():
            return cand.resolve()
        if (cand / "zerocopy" / "src" / "lib.rs").is_file() and (cand / "zerocopy" / "Cargo.toml").is_file():
            return (cand / "zerocopy").resolve()
    raise FileNotFoundError(
        "zerocopy crate source not found; pass --zerocopy-src <path-to-zerocopy-crate> or set ZEROCOPY_SRC"
    )


def sanitize_output(text: str, td: str, zc_src: Path | None = None) -> str:
    out = text.replace(td + os.sep, "").replace(td, "<tmpdir>")
    if zc_src is not None:
        out = out.replace(str(zc_src) + os.sep, "zerocopy/").replace(str(zc_src), "zerocopy")
    return out.strip()


def run_rustc_probe(
    rustc: str,
    name: str,
    code: str,
    edition: str = "2024",
    expect_compile_ok: bool = True,
    extra_args: list[str] | None = None,
) -> dict[str, Any]:
    extra_args = extra_args or []
    with tempfile.TemporaryDirectory() as td:
        src = Path(td) / "probe.rs"
        exe = Path(td) / "probe"
        src.write_text(code, encoding="utf-8")
        cmd = [rustc, f"--edition={edition}", *extra_args, str(src), "-o", str(exe)]
        comp = subprocess.run(cmd, text=True, capture_output=True, check=False)
        res: dict[str, Any] = {
            "name": name,
            "edition": edition,
            "extra_args": extra_args,
            "compile_returncode": comp.returncode,
            "compile_stdout": sanitize_output(comp.stdout, td),
            "compile_stderr": sanitize_output(comp.stderr, td),
        }
        if comp.returncode == 0:
            run = subprocess.run([str(exe)], text=True, capture_output=True, check=False)
            res["run_returncode"] = run.returncode
            res["run_stdout"] = sanitize_output(run.stdout, td)
            res["run_stderr"] = sanitize_output(run.stderr, td)
            if run.returncode != 0:
                raise AssertionError(f"probe {name} failed at runtime: {res}")
        if expect_compile_ok and comp.returncode != 0:
            raise AssertionError(f"probe {name} unexpectedly failed to compile: {res}")
        if not expect_compile_ok and comp.returncode == 0:
            raise AssertionError(f"probe {name} unexpectedly compiled cleanly")
        return res


def run_zerocopy_probe(rustc: str, zc_src: Path) -> dict[str, Any]:
    cargo_toml = tomllib.loads((zc_src / "Cargo.toml").read_text(encoding="utf-8"))
    zc_version = str(cargo_toml["package"]["version"])
    zc_env = os.environ.copy()
    zc_env["CARGO_PKG_VERSION"] = zc_version

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        rlib_path = td_path / "libzerocopy.rlib"
        zc_lib = zc_src / "src" / "lib.rs"
        comp_zc = subprocess.run(
            [
                rustc,
                "--crate-name",
                "zerocopy",
                "--crate-type",
                "rlib",
                "--edition=2021",
                str(zc_lib),
                "-o",
                str(rlib_path),
            ],
            env=zc_env,
            text=True,
            capture_output=True,
            check=False,
        )
        if comp_zc.returncode != 0:
            raise AssertionError(
                f"failed to build zerocopy rlib: {sanitize_output(comp_zc.stderr, td, zc_src)}"
            )

        probe_rs = td_path / "zc_probe.rs"
        probe_exe = td_path / "zc_probe"
        probe_rs.write_text(
            r'''
use zerocopy::{CastError, KnownLayout, Ref};

#[repr(align(4))]
struct AlignedBuf([u8; 16]);

#[repr(C)]
struct LocalUnaligned {
    _a: u8,
}

fn main() {
    let aligned = AlignedBuf([
        10, 0, 0, 0,
        20, 0, 0, 0,
        30, 0, 0, 0,
        40, 0, 0, 0,
    ]);
    let bytes12: &[u8] = &aligned.0[..12];
    let dst_ref: Ref<&[u8], [u32]> =
        Ref::<&[u8], [u32]>::from_bytes_with_elems(bytes12, 3).expect("aligned 12B => 3 u32s");
    let raw_ptr: *const [u32] = &*dst_ref;
    let meta: usize = <[u32] as KnownLayout>::pointer_to_metadata(raw_ptr.cast_mut());
    let sum: u32 = dst_ref.iter().copied().sum();

    let (pref, rest) =
        Ref::<&[u8], [u32]>::from_prefix_with_elems(&aligned.0[..], 2).expect("prefix 2 u32s");
    let (head_rest, suff) =
        Ref::<&[u8], [u32]>::from_suffix_with_elems(&aligned.0[..], 2).expect("suffix 2 u32s");

    // Negative size mismatch check: 12 bytes != 4 * 4 bytes
    let size_err_ok = matches!(
        Ref::<&[u8], [u32]>::from_bytes_with_elems(bytes12, 4),
        Err(CastError::Size(_))
    );
    // Negative alignment check: offset by 1 byte breaks align_of::<u32>() == 4
    let misalign_err_ok = matches!(
        Ref::<&[u8], [u32]>::from_bytes_with_elems(&aligned.0[1..13], 3),
        Err(CastError::Alignment(_))
    );
    // Zero-element suffix alignment check on unaligned end address
    let zero_suff_align_ok = matches!(
        Ref::<&[u8], [u32]>::from_suffix_with_elems(&aligned.0[..13], 0),
        Err(CastError::Alignment(_))
    );

    println!(
        "ZC_DST_LEN={} ZC_META={} ZC_SUM={} PREF_REST={} SUFF_HEAD={} SIZE_ERR={} ALIGN_ERR={} ZERO_SUFF_ERR={}",
        dst_ref.len(),
        meta,
        sum,
        rest.len(),
        head_rest.len(),
        size_err_ok,
        misalign_err_ok,
        zero_suff_align_ok,
    );
    let _ = (pref, suff, LocalUnaligned { _a: 0 });
}
''',
            encoding="utf-8",
        )
        comp_probe = subprocess.run(
            [
                rustc,
                "--edition=2024",
                "--extern",
                f"zerocopy={rlib_path}",
                str(probe_rs),
                "-o",
                str(probe_exe),
            ],
            text=True,
            capture_output=True,
            check=False,
        )
        if comp_probe.returncode != 0:
            raise AssertionError(
                f"failed to compile zerocopy probe: {sanitize_output(comp_probe.stderr, td, zc_src)}"
            )
        run = subprocess.run([str(probe_exe)], text=True, capture_output=True, check=False)
        if run.returncode != 0:
            raise AssertionError(f"zerocopy probe failed at runtime: {run.stderr}")
        return {
            "name": "zerocopy_known_layout_ref_from_bytes_with_elems_dst",
            "edition_zerocopy": "2021",
            "edition_probe": "2024",
            "zerocopy_lib_compile_returncode": comp_zc.returncode,
            "probe_compile_returncode": comp_probe.returncode,
            "probe_compile_stderr": sanitize_output(comp_probe.stderr, td, zc_src),
            "probe_run_returncode": run.returncode,
            "probe_run_stdout": sanitize_output(run.stdout, td, zc_src),
            "probe_run_stderr": sanitize_output(run.stderr, td, zc_src),
        }


def run_zerocopy_derive_custom_dst_probe(zc_src: Path) -> dict[str, Any]:
    vendor_dir = zc_src / "vendor"
    cargo_bin = shutil.which("cargo") or str(Path.home() / ".cargo" / "bin" / "cargo")
    if not vendor_dir.is_dir() or not Path(cargo_bin).exists():
        return {
            "name": "zerocopy_derive_custom_dst_packet",
            "skipped": True,
            "reason": "vendored dependencies or cargo executable unavailable in offline environment",
        }

    with tempfile.TemporaryDirectory() as td:
        p = Path(td)
        (p / "Cargo.toml").write_text(
            f'''[package]
name = "zc_derive_probe"
version = "0.1.0"
edition = "2024"

[dependencies]
zerocopy = {{ path = "{zc_src}", features = ["derive"] }}
''',
            encoding="utf-8",
        )
        (p / ".cargo").mkdir()
        (p / ".cargo" / "config.toml").write_text(
            f'''[source.crates-io]
replace-with = "vendored-sources"
[source.vendored-sources]
directory = "{vendor_dir}"
''',
            encoding="utf-8",
        )
        (p / "src").mkdir()
        (p / "src" / "main.rs").write_text(
            r'''
use core::cell::{Cell, UnsafeCell};
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, Ref};
use zerocopy::pointer::{Ptr, invariant};

#[derive(FromBytes, Immutable, KnownLayout)]
#[repr(C)]
struct Packet {
    hdr: u32,
    tag: u16,
    payload: [u16],
}

#[derive(FromBytes, IntoBytes, Immutable, KnownLayout)]
#[repr(C)]
struct UnpaddedPacket {
    hdr: u32,
    payload: [u32],
}

#[repr(align(4))]
struct Aligned16([u8; 16]);

fn main() {
    let mut raw = [0u8; 16];
    raw[0..4].copy_from_slice(&7u32.to_le_bytes());
    raw[4..6].copy_from_slice(&0x1234u16.to_le_bytes());
    for (i, v) in [10u16, 20, 30, 40, 50].iter().enumerate() {
        raw[6 + 2 * i..8 + 2 * i].copy_from_slice(&v.to_le_bytes());
    }
    let aligned = Aligned16(raw);
    let r5: Ref<&[u8], Packet> =
        Ref::<&[u8], Packet>::from_bytes_with_elems(&aligned.0[..], 5).expect("valid 16B Packet(5)");
    let r4: Ref<&[u8], Packet> =
        Ref::<&[u8], Packet>::from_bytes_with_elems(&aligned.0[..], 4).expect("valid 16B Packet(4) with 2B tail pad");
    let meta5 = <Packet as KnownLayout>::pointer_to_metadata((&*r5 as *const Packet).cast_mut());
    let meta4 = <Packet as KnownLayout>::pointer_to_metadata((&*r4 as *const Packet).cast_mut());

    // Transparent wrapper DST cast via Ptr::transmute (uses CastExact / SizeEq) + IntoBytes::as_bytes
    let mut cell_pkt_bytes = aligned.0;
    let mut r_mut: Ref<&mut [u8], UnpaddedPacket> =
        Ref::<&mut [u8], UnpaddedPacket>::from_bytes_with_elems(&mut cell_pkt_bytes[..], 3)
            .expect("valid 16B UnpaddedPacket(3)");
    let bytes_len = r_mut.as_bytes().len();
    let ptr_u: Ptr<'_, UnpaddedPacket, _> = Ptr::from_mut(&mut *r_mut);
    let ptr_cell: Ptr<'_, Cell<UnpaddedPacket>, _> =
        ptr_u.transmute::<Cell<UnpaddedPacket>, invariant::Initialized, _>();
    let ptr_ucell: Ptr<'_, UnsafeCell<UnpaddedPacket>, _> =
        ptr_cell.transmute::<UnsafeCell<UnpaddedPacket>, invariant::Initialized, _>();
    let ucell_meta = <UnsafeCell<UnpaddedPacket> as KnownLayout>::pointer_to_metadata(
        ptr_ucell.as_inner().as_ptr()
    );

    println!(
        "ZC_CUSTOM_DST_META5={} META4={} HDR={} TAG={} SUM5={} SUM4={} BYTES_LEN={} UCELL_META={}",
        meta5,
        meta4,
        r5.hdr,
        r5.tag,
        r5.payload.iter().sum::<u16>(),
        r4.payload.iter().sum::<u16>(),
        bytes_len,
        ucell_meta,
    );
}
''',
            encoding="utf-8",
        )
        run = subprocess.run(
            [cargo_bin, "run", "--offline", "--quiet"],
            cwd=p,
            text=True,
            capture_output=True,
            check=False,
        )
        if run.returncode != 0:
            raise AssertionError(
                f"zerocopy derive custom DST probe failed: {sanitize_output(run.stderr, td, zc_src)}"
            )

        # Negative check: #[derive(KnownLayout)] on non-#[repr(C)] slice DST requires Self: Sized
        (p / "src" / "main.rs").write_text(
            r'''
use zerocopy::KnownLayout;

#[derive(KnownLayout)]
struct NonReprCPacket {
    hdr: u32,
    payload: [u16],
}

fn main() {}
''',
            encoding="utf-8",
        )
        neg = subprocess.run(
            [cargo_bin, "check", "--offline", "--quiet"],
            cwd=p,
            text=True,
            capture_output=True,
            check=False,
        )
        if neg.returncode == 0:
            raise AssertionError("non-repr(C) derive(KnownLayout) DST unexpectedly compiled")

        return {
            "name": "zerocopy_derive_custom_dst_packet",
            "skipped": False,
            "edition": "2024",
            "probe_run_returncode": run.returncode,
            "probe_run_stdout": sanitize_output(run.stdout, td, zc_src),
            "probe_run_stderr": sanitize_output(run.stderr, td, zc_src),
            "non_repr_c_derive_compile_returncode": neg.returncode,
            "non_repr_c_derive_compile_stderr": sanitize_output(neg.stderr, td, zc_src),
        }


def run_all_probes(rustc: str, zc_src: Path) -> dict[str, Any]:
    ver = subprocess.run([rustc, "-vV"], text=True, capture_output=True, check=True).stdout.strip()

    group_a: dict[str, Any] = {}
    group_a["valid_myptr_coerce_unsized_and_dispatch_from_dyn"] = run_rustc_probe(
        rustc,
        "valid_myptr_coerce_unsized_and_dispatch_from_dyn",
        r'''
#![feature(coerce_unsized, dispatch_from_dyn, unsize, arbitrary_self_types)]
use std::fmt::Display;
use std::marker::Unsize;
use std::ops::{CoerceUnsized, Deref, DispatchFromDyn};

struct MyPtr<T: ?Sized>(*const T);

impl<T: ?Sized> Deref for MyPtr<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.0 }
    }
}

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<MyPtr<U>> for MyPtr<T> {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<MyPtr<U>> for MyPtr<T> {}

trait Measure {
    fn measure(self: MyPtr<Self>) -> usize;
}

struct Val(usize);
impl Measure for Val {
    fn measure(self: MyPtr<Self>) -> usize {
        (*self).0
    }
}

fn main() {
    let arr = [1u8, 2, 3, 4];
    let p_arr: MyPtr<[u8; 4]> = MyPtr(&arr);
    let p_slice: MyPtr<[u8]> = p_arr;
    let slice_len = p_slice.len();

    let x: u32 = 42;
    let p_u32: MyPtr<u32> = MyPtr(&x);
    let p_dyn: MyPtr<dyn Display> = p_u32;
    let dyn_str = format!("{}", &*p_dyn);

    let v = Val(99);
    let p_val: MyPtr<Val> = MyPtr(&v);
    let p_meas: MyPtr<dyn Measure> = p_val;
    let measured = p_meas.measure();

    println!("UNSIZE_SLICE={} UNSIZE_DYN={} DYN_DISPATCH={}", slice_len, dyn_str, measured);
}
''',
        expect_compile_ok=True,
    )

    group_a["valid_dispatch_from_dyn_non_generic_1zst_sibling"] = run_rustc_probe(
        rustc,
        "valid_dispatch_from_dyn_non_generic_1zst_sibling",
        r'''
#![feature(coerce_unsized, dispatch_from_dyn, unsize, arbitrary_self_types)]
use std::marker::{PhantomData, Unsize};
use std::ops::{CoerceUnsized, Deref, DispatchFromDyn};

#[derive(Copy, Clone)]
struct UnitTag;

struct TaggedPtr<T: ?Sized>(*const T, UnitTag, PhantomData<T>);

impl<T: ?Sized> Deref for TaggedPtr<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.0 }
    }
}

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<TaggedPtr<U>> for TaggedPtr<T> {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<TaggedPtr<U>> for TaggedPtr<T> {}

trait Echo {
    fn echo(self: TaggedPtr<Self>) -> u32;
}
impl Echo for u32 {
    fn echo(self: TaggedPtr<Self>) -> u32 {
        *self
    }
}

fn main() {
    let v = 77u32;
    let p: TaggedPtr<dyn Echo> = TaggedPtr(&v, UnitTag, PhantomData);
    println!("TAGGED_DYN_DISPATCH={}", p.echo());
}
''',
        expect_compile_ok=True,
    )

    group_a["zero_unsizable_fields_rejected_e0374"] = run_rustc_probe(
        rustc,
        "zero_unsizable_fields_rejected_e0374",
        r'''
#![feature(coerce_unsized, unsize)]
use std::marker::{PhantomData, Unsize};
use std::ops::CoerceUnsized;

struct Zero<T: ?Sized>(PhantomData<T>, u32);

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<Zero<U>> for Zero<T> {}

fn main() {}
''',
        expect_compile_ok=False,
    )

    group_a["two_unsizable_fields_rejected_e0375"] = run_rustc_probe(
        rustc,
        "two_unsizable_fields_rejected_e0375",
        r'''
#![feature(coerce_unsized, unsize)]
use std::marker::Unsize;
use std::ops::CoerceUnsized;

struct Two<T: ?Sized>(*const T, *const T);

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<Two<U>> for Two<T> {}

fn main() {}
''',
        expect_compile_ok=False,
    )

    group_a["distinct_structs_rejected_e0377"] = run_rustc_probe(
        rustc,
        "distinct_structs_rejected_e0377",
        r'''
#![feature(coerce_unsized, unsize)]
use std::marker::Unsize;
use std::ops::CoerceUnsized;

struct PtrA<T: ?Sized>(*const T);
struct PtrB<T: ?Sized>(*const T);

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<PtrB<U>> for PtrA<T> {}

fn main() {}
''',
        expect_compile_ok=False,
    )

    group_a["non_struct_enum_rejected_e0377_formerly_e0376"] = run_rustc_probe(
        rustc,
        "non_struct_enum_rejected_e0377_formerly_e0376",
        r'''
#![feature(coerce_unsized, unsize)]
use std::marker::Unsize;
use std::ops::CoerceUnsized;

enum EnumPtr<T: ?Sized> {
    Ptr(*const T),
}

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<EnumPtr<U>> for EnumPtr<T> {}

fn main() {}
''',
        expect_compile_ok=False,
    )

    group_a["dispatch_from_dyn_extra_field_rejected_e0378"] = run_rustc_probe(
        rustc,
        "dispatch_from_dyn_extra_field_rejected_e0378",
        r'''
#![feature(coerce_unsized, dispatch_from_dyn, unsize)]
use std::marker::Unsize;
use std::ops::{CoerceUnsized, DispatchFromDyn};

struct BadDyn<T: ?Sized>(*const T, u32);

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<BadDyn<U>> for BadDyn<T> {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<BadDyn<U>> for BadDyn<T> {}

fn main() {}
''',
        expect_compile_ok=False,
    )

    group_a["dispatch_from_dyn_overaligned_zst_rejected_e0378"] = run_rustc_probe(
        rustc,
        "dispatch_from_dyn_overaligned_zst_rejected_e0378",
        r'''
#![feature(coerce_unsized, dispatch_from_dyn, unsize)]
use std::marker::Unsize;
use std::ops::{CoerceUnsized, DispatchFromDyn};

#[repr(align(8))]
struct Align8Zst;

struct BadDynAlign<T: ?Sized>(*const T, Align8Zst);

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<BadDynAlign<U>> for BadDynAlign<T> {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<BadDynAlign<U>> for BadDynAlign<T> {}

fn main() {}
''',
        expect_compile_ok=False,
    )

    group_a["dispatch_from_dyn_generic_1zst_rejected_e0378"] = run_rustc_probe(
        rustc,
        "dispatch_from_dyn_generic_1zst_rejected_e0378",
        r'''
#![feature(coerce_unsized, dispatch_from_dyn, unsize)]
use std::marker::{PhantomData, Unsize};
use std::ops::{CoerceUnsized, DispatchFromDyn};

struct Marker<M>(PhantomData<fn() -> M>);

struct BadDynGenericZst<T: ?Sized, M>(*const T, Marker<M>);

impl<T: ?Sized + Unsize<U>, U: ?Sized, M> CoerceUnsized<BadDynGenericZst<U, M>>
    for BadDynGenericZst<T, M>
{}
impl<T: ?Sized + Unsize<U>, U: ?Sized, M> DispatchFromDyn<BadDynGenericZst<U, M>>
    for BadDynGenericZst<T, M>
{}

fn main() {}
''',
        expect_compile_ok=False,
    )

    group_a["dispatch_from_dyn_repr_c_rejected_e0378"] = run_rustc_probe(
        rustc,
        "dispatch_from_dyn_repr_c_rejected_e0378",
        r'''
#![feature(coerce_unsized, dispatch_from_dyn, unsize)]
use std::marker::Unsize;
use std::ops::{CoerceUnsized, DispatchFromDyn};

#[repr(C)]
struct BadRepr<T: ?Sized>(*const T);

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<BadRepr<U>> for BadRepr<T> {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<BadRepr<U>> for BadRepr<T> {}

fn main() {}
''',
        expect_compile_ok=False,
    )

    group_a["dispatch_from_dyn_repr_packed_rejected_e0378"] = run_rustc_probe(
        rustc,
        "dispatch_from_dyn_repr_packed_rejected_e0378",
        r'''
#![feature(coerce_unsized, dispatch_from_dyn, unsize)]
use std::marker::Unsize;
use std::ops::{CoerceUnsized, DispatchFromDyn};

#[repr(packed)]
struct BadPacked<T: ?Sized>(*const T);

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<BadPacked<U>> for BadPacked<T> {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<BadPacked<U>> for BadPacked<T> {}

fn main() {}
''',
        expect_compile_ok=False,
    )

    group_b: dict[str, Any] = {}
    group_b["custom_dst_tail_unsizing_ok"] = run_rustc_probe(
        rustc,
        "custom_dst_tail_unsizing_ok",
        r'''
#[repr(C)]
struct Packet<T: ?Sized> {
    hdr: u32,
    tag: u16,
    payload: T,
}

fn coerce(p: &Packet<[u8; 4]>) -> &Packet<[u8]> {
    p
}

fn main() {
    let pkt = Packet { hdr: 7, tag: 0x1234, payload: [10u8, 20, 30, 40] };
    let off_hdr_sized = core::mem::offset_of!(Packet<[u8; 4]>, hdr);
    let off_tag_sized = core::mem::offset_of!(Packet<[u8; 4]>, tag);
    let off_pay_sized = core::mem::offset_of!(Packet<[u8; 4]>, payload);
    let dst = coerce(&pkt);
    let base_addr = dst as *const Packet<[u8]> as *const u8 as usize;
    let hdr_addr = &dst.hdr as *const u32 as usize;
    let tag_addr = &dst.tag as *const u16 as usize;
    let pay_addr = &dst.payload[0] as *const u8 as usize;
    assert_eq!(hdr_addr - base_addr, off_hdr_sized);
    assert_eq!(tag_addr - base_addr, off_tag_sized);
    assert_eq!(pay_addr - base_addr, off_pay_sized);
    println!(
        "PACKET_LEN={} HDR={} OFF_HDR={} OFF_TAG={} OFF_PAYLOAD={}",
        dst.payload.len(),
        dst.hdr,
        off_hdr_sized,
        off_tag_sized,
        off_pay_sized,
    );
}
''',
        expect_compile_ok=True,
    )

    group_b["custom_dst_non_last_unsized_field_rejected_e0277"] = run_rustc_probe(
        rustc,
        "custom_dst_non_last_unsized_field_rejected_e0277",
        r'''
struct BadFirst<T: ?Sized> {
    head: T,
    tail: u32,
}

fn coerce(p: &BadFirst<[u8; 4]>) -> &BadFirst<[u8]> {
    p
}

fn main() {}
''',
        expect_compile_ok=False,
    )

    group_b["custom_dst_two_unsized_fields_rejected_e0277"] = run_rustc_probe(
        rustc,
        "custom_dst_two_unsized_fields_rejected_e0277",
        r'''
struct BadTwo<T: ?Sized> {
    a: T,
    b: T,
}

fn coerce(p: &BadTwo<[u8; 4]>) -> &BadTwo<[u8]> {
    p
}

fn main() {}
''',
        expect_compile_ok=False,
    )

    group_b["custom_dst_prefix_mentions_param_rejected"] = run_rustc_probe(
        rustc,
        "custom_dst_prefix_mentions_param_rejected",
        r'''
struct PrefixMentionsParam<T: ?Sized> {
    meta_ptr: *const T,
    tail: T,
}

fn coerce(p: &PrefixMentionsParam<[u8; 4]>) -> &PrefixMentionsParam<[u8]> {
    p
}

fn main() {}
''',
        expect_compile_ok=False,
    )

    group_b["zerocopy_known_layout_ref_from_bytes_with_elems_dst"] = run_zerocopy_probe(rustc, zc_src)
    group_b["zerocopy_derive_custom_dst_packet"] = run_zerocopy_derive_custom_dst_probe(zc_src)

    return {
        "rustc_version": ver,
        "experiments": {
            "a_coerce_unsized_and_dispatch_from_dyn_constraints": group_a,
            "b_custom_dst_tail_unsize_and_zerocopy": group_b,
        },
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", help="Optional path to write JSON output")
    parser.add_argument("--zerocopy-src", help="Path to google/zerocopy zerocopy crate directory")
    args = parser.parse_args(argv)

    rustc = resolve_rustc()
    zc_src = resolve_zerocopy_src(args.zerocopy_src)
    results = run_all_probes(rustc, zc_src)
    encoded = json.dumps(results, indent=2) + "\n"
    if args.out:
        Path(args.out).write_text(encoded, encoding="utf-8")
    else:
        sys.stdout.write(encoded)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
