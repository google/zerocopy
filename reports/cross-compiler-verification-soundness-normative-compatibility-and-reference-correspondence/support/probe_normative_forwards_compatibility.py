#!/usr/bin/env python3
"""Live multi-toolchain empirical verification of Rust's 3-category normative
stability envelope and `zerocopy`'s compile-time `PaddingFree` guard.

Runs strictly inside `tempfile.TemporaryDirectory()` (read-only on all
installed `rustup` toolchains) across `rustc 1.78.0` through `1.102.0-nightly`
plus `-Z randomize-layout -Z layout-seed={7,42}`.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import subprocess
import tempfile

RUSTUP_ROOT = pathlib.Path.home() / ".rustup" / "toolchains"

DESIRED_TOOLCHAINS = [
    "1.78.0-x86_64-unknown-linux-gnu",
    "1.84.0-x86_64-unknown-linux-gnu",
    "1.93.1-x86_64-unknown-linux-gnu",
    "1.96.0-x86_64-unknown-linux-gnu",
    "1.99.1-x86_64-unknown-linux-gnu",
    "1.100.0-x86_64-unknown-linux-gnu",
    "nightly-x86_64-unknown-linux-gnu",
]

RUNTIME_PROBE_RS = r"""
use core::any::{type_name, TypeId};
use core::convert::Infallible;
use core::mem::{align_of, offset_of, size_of, transmute};
use core::num::NonZeroU64;
use core::ptr::NonNull;

#[repr(C)]
struct ReprCStruct {
    a: u8,
    b: u32,
    c: u64,
}

#[repr(transparent)]
struct ReprTransparentWrap(NonNull<u64>, core::marker::PhantomData<u8>);

#[repr(u8)]
enum ReprU8Enum {
    First(u32) = 1,
    Second(u64) = 2,
}

#[repr(packed)]
struct ReprRustPacked {
    a: u8,
    b: u64,
    c: u16,
}

// Accidentally padding-free (16 bytes) under default rustc field sorting,
// and 8-byte aligned `(u8, u32, u16, u8)` (8 bytes default -> 16 bytes when randomized),
// neither normatively guaranteed padding-free across conforming compilers!
struct ReprRustAccidentallyUnpadded {
    d: u8,
    b: u32,
    a: u64,
    c: u16,
    e: u8,
}

#[repr(align(8))]
struct ReprRustAlign8EightBytes {
    a: u8,
    b: u32,
    c: u16,
    d: u8,
}

fn main() {
    // Category A checks: normatively guaranteed across all conforming compilers
    let repr_c_ok = size_of::<ReprCStruct>() == 16
        && align_of::<ReprCStruct>() == 8
        && offset_of!(ReprCStruct, a) == 0
        && offset_of!(ReprCStruct, b) == 4
        && offset_of!(ReprCStruct, c) == 8;

    let repr_transparent_ok = size_of::<ReprTransparentWrap>() == size_of::<usize>()
        && align_of::<ReprTransparentWrap>() == align_of::<usize>();

    let repr_u8_ok = size_of::<ReprU8Enum>() == 16 && align_of::<ReprU8Enum>() == 8;

    let repr_packed_ok = size_of::<ReprRustPacked>() == 11 && align_of::<ReprRustPacked>() == 1;

    let npo_none_ref: Option<&u64> = unsafe { transmute(0usize) };
    let npo_none_nn: Option<NonNull<u64>> = unsafe { transmute(0usize) };
    let npo_none_nz: Option<NonZeroU64> = unsafe { transmute(0u64) };
    let npo_none_fn: Option<fn()> = unsafe { transmute(0usize) };
    let npo_ok = size_of::<Option<&u64>>() == 8
        && size_of::<Option<NonNull<u64>>>() == 8
        && size_of::<Option<NonZeroU64>>() == 8
        && size_of::<Option<fn()>>() == 8
        && npo_none_ref.is_none()
        && npo_none_nn.is_none()
        && npo_none_nz.is_none()
        && npo_none_fn.is_none();

    // Category B observations: cross-release / conforming-compiler degrees of freedom
    let rr_size = size_of::<ReprRustAccidentallyUnpadded>();
    let rr_offsets = [
        offset_of!(ReprRustAccidentallyUnpadded, a),
        offset_of!(ReprRustAccidentallyUnpadded, b),
        offset_of!(ReprRustAccidentallyUnpadded, c),
        offset_of!(ReprRustAccidentallyUnpadded, d),
        offset_of!(ReprRustAccidentallyUnpadded, e),
    ];
    let rr8_size = size_of::<ReprRustAlign8EightBytes>();
    let rr8_offsets = [
        offset_of!(ReprRustAlign8EightBytes, a),
        offset_of!(ReprRustAlign8EightBytes, b),
        offset_of!(ReprRustAlign8EightBytes, c),
        offset_of!(ReprRustAlign8EightBytes, d),
    ];
    let infallible_type_name = type_name::<Infallible>();

    println!(
        "{{\"cat_a_repr_c\":{},\"cat_a_transparent\":{},\"cat_a_repr_u8\":{},\"cat_a_packed\":{},\"cat_a_npo\":{},\"rr_size\":{},\"rr_offsets\":{:?},\"rr8_size\":{},\"rr8_offsets\":{:?},\"infallible_type_name\":\"{}\"}}",
        str_bool(repr_c_ok),
        str_bool(repr_transparent_ok),
        str_bool(repr_u8_ok),
        str_bool(repr_packed_ok),
        str_bool(npo_ok),
        rr_size,
        rr_offsets,
        rr8_size,
        rr8_offsets,
        infallible_type_name,
    );
}

fn str_bool(b: bool) -> &'static str {
    if b { "true" } else { "false" }
}
"""

NEVER_TYPEID_PROBE_RS = r"""
#![cfg_attr(feature = "nightly_never", feature(never_type))]
use core::any::TypeId;
use core::convert::Infallible;

trait HasNever {
    type Out;
}
impl<T> HasNever for fn() -> T {
    type Out = T;
}
type ExtractedNever = <fn() -> ! as HasNever>::Out;

fn main() {
    let eq_never = TypeId::of::<Infallible>() == TypeId::of::<ExtractedNever>();
    println!("{{\"infallible_eq_never\":{}}}", if eq_never { "true" } else { "false" });
}
"""

ZEROCOPY_PADDING_FREE_GUARD_RS = r"""
use core::mem::size_of;

pub unsafe trait IntoBytes {}
pub trait PaddingFree<T: ?Sized, const PADDING_BYTES: usize> {}
impl<T: ?Sized> PaddingFree<T, 0> for () {}

pub struct ReprRustAccidentallyUnpadded {
    pub d: u8,
    pub b: u32,
    pub a: u64,
    pub c: u16,
    pub e: u8,
}

const PADDING: usize = size_of::<ReprRustAccidentallyUnpadded>()
    - (size_of::<u8>() + size_of::<u32>() + size_of::<u64>() + size_of::<u16>() + size_of::<u8>());

// Compile-time PaddingFree pattern (`zerocopy-derive/src/derive/into_bytes.rs`):
unsafe impl IntoBytes for ReprRustAccidentallyUnpadded
where
    (): PaddingFree<ReprRustAccidentallyUnpadded, PADDING>,
{}

fn require_into_bytes<T: IntoBytes>(_x: &T) -> usize {
    size_of::<T>()
}

fn main() {
    let v = ReprRustAccidentallyUnpadded { d: 1, b: 2, a: 3, c: 4, e: 5 };
    println!("{{\"compiled_size\":{}}}", require_into_bytes(&v));
}
"""

EDITION_DROP_ORDER_PROBE_RS = r"""
use std::cell::RefCell;

struct DropLogger<'a>(&'static str, &'a RefCell<Vec<&'static str>>);
impl<'a> Drop for DropLogger<'a> {
    fn drop(&mut self) {
        self.1.borrow_mut().push(self.0);
    }
}

fn make_temp<'a>(log: &'a RefCell<Vec<&'static str>>) -> (u32, DropLogger<'a>) {
    (42, DropLogger("tail_temp", log))
}

fn run() -> Vec<&'static str> {
    let log = RefCell::new(Vec::new());
    let _val = {
        let _local = DropLogger("block_local", &log);
        make_temp(&log).0
    };
    log.into_inner()
}

fn main() {
    println!("{{\"drop_order\":{:?}}}", run());
}
"""


def clean_env(tc_dir: pathlib.Path) -> dict[str, str]:
    env = {
        k: v
        for k, v in os.environ.items()
        if not k.startswith(("RUSTUP_", "CARGO_", "LD_"))
    }
    env["PATH"] = f"{tc_dir / 'bin'}:/usr/bin:/bin"
    return env


def run_rustc_and_bin(
    tc_dir: pathlib.Path,
    src_code: str,
    extra_args: list[str],
    tmp_dir: pathlib.Path,
    tag: str,
) -> dict[str, object]:
    rustc = tc_dir / "bin" / "rustc"
    src_file = tmp_dir / f"{tag}.rs"
    bin_file = tmp_dir / f"{tag}.bin"
    src_file.write_text(src_code, encoding="utf-8")
    cmd = [
        str(rustc),
        "--sysroot",
        str(tc_dir),
        "--edition=2021",
        *extra_args,
        "-o",
        str(bin_file),
        str(src_file),
    ]
    comp = subprocess.run(
        cmd, env=clean_env(tc_dir), text=True, capture_output=True, check=False
    )
    if comp.returncode != 0:
        return {
            "compiled": False,
            "rustc_rc": comp.returncode,
            "stderr_head": comp.stderr.strip().splitlines()[:8],
        }
    exe = subprocess.run(
        [str(bin_file)],
        env=clean_env(tc_dir),
        text=True,
        capture_output=True,
        check=False,
    )
    out = exe.stdout.strip()
    try:
        parsed: object = json.loads(out)
    except Exception:
        parsed = {"raw_stdout": out}
    return {
        "compiled": True,
        "rustc_rc": 0,
        "run_rc": exe.returncode,
        "result": parsed,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=pathlib.Path, default=None)
    args = parser.parse_args()

    results: dict[str, object] = {"toolchains": [], "edition_drop_order": {}}
    available: list[tuple[str, pathlib.Path]] = []
    for name in DESIRED_TOOLCHAINS:
        d = RUSTUP_ROOT / name
        if (d / "bin" / "rustc").exists():
            available.append((name, d))
        elif name.startswith("nightly"):
            nightlies = sorted(RUSTUP_ROOT.glob("*nightly*x86_64*"))
            if nightlies:
                available.append((nightlies[-1].name, nightlies[-1]))

    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = pathlib.Path(tmp_str)
        for name, tc_dir in available:
            vv = subprocess.check_output(
                [str(tc_dir / "bin" / "rustc"), "-vV"],
                env=clean_env(tc_dir),
                text=True,
            ).strip()
            is_nightly = "nightly" in vv
            configs = [("default", [])]
            if is_nightly:
                configs.append(
                    ("randomize_seed_7", ["-Zrandomize-layout", "-Zlayout-seed=7"])
                )
                configs.append(
                    ("randomize_seed_42", ["-Zrandomize-layout", "-Zlayout-seed=42"])
                )
            for cfg_name, flags in configs:
                tag_prefix = f"{name}_{cfg_name}".replace(".", "_").replace("-", "_")
                rt = run_rustc_and_bin(
                    tc_dir, RUNTIME_PROBE_RS, flags, tmp, f"{tag_prefix}_rt"
                )
                nv = run_rustc_and_bin(
                    tc_dir, NEVER_TYPEID_PROBE_RS, flags, tmp, f"{tag_prefix}_nv"
                )
                zc = run_rustc_and_bin(
                    tc_dir,
                    ZEROCOPY_PADDING_FREE_GUARD_RS,
                    flags,
                    tmp,
                    f"{tag_prefix}_zc",
                )
                results["toolchains"].append(
                    {
                        "toolchain_dir": name,
                        "rustc_vV": vv.splitlines(),
                        "config": cfg_name,
                        "flags": flags,
                        "runtime_envelope": rt,
                        "never_typeid": nv,
                        "zerocopy_padding_free_guard": zc,
                    }
                )

            if any(k in name for k in ("1.93", "1.100")):
                ed21 = run_rustc_and_bin(
                    tc_dir,
                    EDITION_DROP_ORDER_PROBE_RS,
                    [],
                    tmp,
                    f"{name}_ed21".replace(".", "_"),
                )
                rustc = tc_dir / "bin" / "rustc"
                src_f = tmp / "ed24_probe.rs"
                bin_f = tmp / "ed24_probe.bin"
                src_f.write_text(EDITION_DROP_ORDER_PROBE_RS, encoding="utf-8")
                c24 = subprocess.run(
                    [
                        str(rustc),
                        "--sysroot",
                        str(tc_dir),
                        "--crate-name",
                        "ed24_probe",
                        "--edition=2024",
                        "-o",
                        str(bin_f),
                        str(src_f),
                    ],
                    env=clean_env(tc_dir),
                    text=True,
                    capture_output=True,
                    check=False,
                )
                r24 = None
                if c24.returncode == 0:
                    e24 = subprocess.run(
                        [str(bin_f)],
                        env=clean_env(tc_dir),
                        text=True,
                        capture_output=True,
                        check=False,
                    )
                    r24 = e24.stdout.strip()
                results["edition_drop_order"][name] = {
                    "edition_2021": ed21,
                    "edition_2024_stdout": r24,
                }

    rendered = json.dumps(results, indent=2) + "\n"
    if args.out is not None:
        args.out.write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
