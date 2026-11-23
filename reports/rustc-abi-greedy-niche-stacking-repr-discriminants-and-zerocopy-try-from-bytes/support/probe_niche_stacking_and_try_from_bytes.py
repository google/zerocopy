#!/usr/bin/env python3
"""Reproducible rustc, Miri, and zerocopy::TryFromBytes empirical probe."""

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


PKG_DIR = Path(__file__).resolve().parent
DEFAULT_OUT = PKG_DIR / "probe_results.json"


def _sanitize(text: str, tmp_dir: str, home_dir: str, zc_dir: str | None) -> str:
    out = text
    if zc_dir:
        out = out.replace(zc_dir, "<zerocopy>")
    out = out.replace(tmp_dir, "<tmp>")
    if home_dir:
        out = out.replace(home_dir, "<home>")
    out = re.sub(r"/tmp/tmp[A-Za-z0-9_]+", "<tmp>", out)
    return out


def _run(cmd: list[str], cwd: Path | None = None, env: dict[str, str] | None = None,
         tmp_dir: str = "", home_dir: str = "", zc_dir: str | None = None) -> dict:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )
    return {
        "command": " ".join(_sanitize(c, tmp_dir, home_dir, zc_dir) for c in cmd),
        "returncode": proc.returncode,
        "stdout": _sanitize(proc.stdout.strip(), tmp_dir, home_dir, zc_dir),
        "stderr": _sanitize(proc.stderr.strip(), tmp_dir, home_dir, zc_dir),
    }


def _find_zerocopy_dir(explicit: str | None) -> Path | None:
    candidates = []
    if explicit:
        candidates.append(Path(explicit))
    env_dir = os.environ.get("ZEROCOPY_DIR")
    if env_dir:
        candidates.append(Path(env_dir))
    home = Path.home()
    for base in [
        Path.cwd() / "zerocopy",
        home / "workspace" / "zerocopy" / "zerocopy",
        home / "zerocopy" / "zerocopy",
    ]:
        candidates.append(base)
    for parent in [Path.cwd(), *Path.cwd().parents, *Path(__file__).resolve().parents]:
        candidates.append(parent / "zerocopy")
        candidates.append(parent / "zerocopy" / "zerocopy")
    for c in candidates:
        if (c / "Cargo.toml").is_file() and (c / "vendor").is_dir():
            return c.resolve()
    return None


TYPE_SIZE_AND_EXEC_SRC = r"""
#![allow(dead_code)]
use core::mem::{align_of, offset_of, size_of, transmute};
use core::num::NonZeroU8;
use core::ptr::NonNull;

#[repr(u8)]
enum ReprU8Data {
    A(u16) = 5,
    B(u8) = 9,
}

#[repr(C, u8)]
enum ReprCU8Data {
    A(u16) = 5,
    B(u8) = 9,
}

#[repr(C)]
enum ReprCData {
    A(u16),
    B(u8),
}

#[repr(C)]
enum CLikeC {
    X = 1,
    Y = 2,
}

#[repr(u8)]
enum CLikeU8 {
    X = 1,
    Y = 2,
}

enum BoolPlusTwo {
    Payload(bool),
    X,
    Y,
}

fn main() {
    let ob: [u8; 3] = unsafe {
        [
            transmute(Some(false)),
            transmute(Some(true)),
            transmute(None::<bool>),
        ]
    };
    let oob: [u8; 4] = unsafe {
        [
            transmute(Some(Some(false))),
            transmute(Some(Some(true))),
            transmute(Some(None::<bool>)),
            transmute(None::<Option<bool>>),
        ]
    };
    let ooob: [u8; 5] = unsafe {
        [
            transmute(Some(Some(Some(false)))),
            transmute(Some(Some(Some(true)))),
            transmute(Some(Some(None::<bool>))),
            transmute(Some(None::<Option<bool>>)),
            transmute(None::<Option<Option<bool>>>),
        ]
    };
    let bpt: [u8; 4] = unsafe {
        [
            transmute(BoolPlusTwo::Payload(false)),
            transmute(BoolPlusTwo::Payload(true)),
            transmute(BoolPlusTwo::X),
            transmute(BoolPlusTwo::Y),
        ]
    };
    let o3c: [u32; 4] = unsafe {
        [
            transmute(Some(Some(Some('A')))),
            transmute(Some(Some(None::<char>))),
            transmute(Some(None::<Option<char>>)),
            transmute(None::<Option<Option<char>>>),
        ]
    };
    let nn_none: usize = unsafe { transmute(None::<NonNull<u8>>) };
    let nz_none: u8 = unsafe { transmute(None::<NonZeroU8>) };

    let ru8_b_bytes: [u8; 4] = unsafe {
        let mut val = ReprU8Data::B(0x42);
        let p = (&mut val as *mut ReprU8Data) as *mut u8;
        // Initialize full enum storage deterministically for reading layout bytes.
        let mut raw = [0xAAu8; 4];
        core::ptr::copy_nonoverlapping(p, raw.as_mut_ptr(), 1);
        core::ptr::copy_nonoverlapping(p.add(1), raw.as_mut_ptr().add(1), 1);
        raw
    };
    let ru8_b_off = {
        let val = ReprU8Data::B(0x42);
        let base = (&val as *const ReprU8Data) as usize;
        match &val {
            ReprU8Data::B(inner) => (inner as *const u8 as usize) - base,
            _ => unreachable!(),
        }
    };
    let rcu8_b_off = {
        let val = ReprCU8Data::B(0x42);
        let base = (&val as *const ReprCU8Data) as usize;
        match &val {
            ReprCU8Data::B(inner) => (inner as *const u8 as usize) - base,
            _ => unreachable!(),
        }
    };
    let rc_b_off = {
        let val = ReprCData::B(0x42);
        let base = (&val as *const ReprCData) as usize;
        match &val {
            ReprCData::B(inner) => (inner as *const u8 as usize) - base,
            _ => unreachable!(),
        }
    };
    let ru8_a_off = {
        let val = ReprU8Data::A(0x1234);
        let base = (&val as *const ReprU8Data) as usize;
        match &val {
            ReprU8Data::A(inner) => (inner as *const u16 as usize) - base,
            _ => unreachable!(),
        }
    };

    let ru8_tag: u8 = unsafe { *((&ReprU8Data::B(0x42) as *const ReprU8Data) as *const u8) };
    let rcu8_tag: u8 = unsafe { *((&ReprCU8Data::B(0x42) as *const ReprCU8Data) as *const u8) };
    let rc_tag: u32 = unsafe { *((&ReprCData::B(0x42) as *const ReprCData) as *const u32) };

    let oonn_0: [u64; 2] = unsafe { transmute(Some(Some(NonNull::<u8>::dangling()))) };
    let oonn_1: [u64; 2] = unsafe { transmute(Some(None::<NonNull<u8>>)) };
    let oonn_2: [u64; 2] = unsafe { transmute(None::<Option<NonNull<u8>>>) };
    let oonz: [u8; 2] = unsafe {
        [
            transmute::<Option<Option<NonZeroU8>>, [u8; 2]>(Some(Some(NonZeroU8::new(7).unwrap())))[0],
            transmute::<Option<Option<NonZeroU8>>, [u8; 2]>(Some(None))[0],
        ]
    };
    let oonz_none_tag: u8 = unsafe {
        transmute::<Option<Option<NonZeroU8>>, [u8; 2]>(None)[0]
    };

    let mut _keep = (ru8_b_bytes, oonz);
    _keep.0[0] ^= 0;

    let result = format!(
        "{{\"opt_bool\":{:?},\"opt_opt_bool\":{:?},\"opt3_bool\":{:?},\"bool_plus_two\":{:?},\
\"opt3_char_hex\":[\"0x{:x}\",\"0x{:x}\",\"0x{:x}\",\"0x{:x}\"],\
\"nonnull_none\":{},\"nonzero_u8_none\":{},\
\"opt2_nonnull_tags\":[{},{},{}],\"opt2_nonzero_u8_tags\":[{},{},{}],\
\"sizes\":{{\"ReprU8Data\":[{},{}],\"ReprCU8Data\":[{},{}],\"ReprCData\":[{},{}],\
\"CLikeC\":[{},{}],\"CLikeU8\":[{},{}],\"OptChar3\":[{},{}],\"OptNonNull2\":[{},{}],\"OptNonZeroU8_2\":[{},{}]}},\
\"field_offsets\":{{\"ReprU8Data_A\":{},\"ReprU8Data_B\":{},\"ReprCU8Data_B\":{},\"ReprCData_B\":{}}},\
\"tags\":{{\"ReprU8Data_B\":{},\"ReprCU8Data_B\":{},\"ReprCData_B\":{}}}}}",
        ob, oob, ooob, bpt,
        o3c[0], o3c[1], o3c[2], o3c[3],
        nn_none, nz_none,
        oonn_0[0], oonn_1[0], oonn_2[0],
        oonz[0], oonz[1], oonz_none_tag,
        size_of::<ReprU8Data>(), align_of::<ReprU8Data>(),
        size_of::<ReprCU8Data>(), align_of::<ReprCU8Data>(),
        size_of::<ReprCData>(), align_of::<ReprCData>(),
        size_of::<CLikeC>(), align_of::<CLikeC>(),
        size_of::<CLikeU8>(), align_of::<CLikeU8>(),
        size_of::<Option<Option<Option<char>>>>(), align_of::<Option<Option<Option<char>>>>(),
        size_of::<Option<Option<NonNull<u8>>>>(), align_of::<Option<Option<NonNull<u8>>>>(),
        size_of::<Option<Option<NonZeroU8>>>(), align_of::<Option<Option<NonZeroU8>>>(),
        ru8_a_off, ru8_b_off, rcu8_b_off, rc_b_off,
        ru8_tag, rcu8_tag, rc_tag
    );
    println!("{}", result);
    let _ = offset_of!((u8, u16), 1);
}
"""


E0732_SRC = r"""
#[repr(C)]
enum BadReprC {
    A(u16) = 5,
    B(u8) = 9,
}

fn main() {}
"""

E0732_UNIT_DISCR_SRC = r"""
#[repr(C)]
enum BadReprCUnit {
    A(u16),
    B = 9,
}

fn main() {}
"""

MIRI_CASES = {
    "miri_valid_option_option_bool_0_1_2_255_ok": r"""
use core::mem::transmute;
fn main() {
    let vals: [Option<Option<bool>>; 4] = unsafe {
        [transmute(0u8), transmute(1u8), transmute(2u8), transmute(255u8)]
    };
    println!("MIRI_NICHE_VALID={:?}", vals);
}
""",
    "miri_invalid_niche_tag_3_ub_caught": r"""
use core::mem::transmute;
fn main() {
    let bad: Option<Option<bool>> = unsafe { transmute(3u8) };
    println!("{:?}", bad);
}
""",
    "miri_invalid_niche_tag_3_opt3_ub_caught": r"""
use core::mem::transmute;
fn main() {
    let bad: Option<Option<Option<bool>>> = unsafe { transmute(3u8) };
    println!("{:?}", bad);
}
""",
    "miri_invalid_char_niche_0x110000_ub_caught": r"""
use core::mem::transmute;
fn main() {
    let bad: Option<char> = unsafe { transmute(0x110000u32) };
    println!("{:?}", bad);
}
""",
    "miri_invalid_char_surrogate_0xd800_ub_caught": r"""
use core::mem::transmute;
fn main() {
    let bad: Option<char> = unsafe { transmute(0xD800u32) };
    println!("{:?}", bad);
}
""",
    "miri_repr_u8_vs_cu8_offsets_ok": r"""
#[repr(u8)]
enum ReprU8Data {
    A(u16) = 5,
    B(u8) = 9,
}
#[repr(C, u8)]
enum ReprCU8Data {
    A(u16) = 5,
    B(u8) = 9,
}
fn main() {
    let u = ReprU8Data::B(0x42);
    let cu = ReprCU8Data::B(0x42);
    let u_off = match &u {
        ReprU8Data::B(p) => (p as *const u8 as usize) - (&u as *const ReprU8Data as usize),
        _ => unreachable!(),
    };
    let cu_off = match &cu {
        ReprCU8Data::B(p) => (p as *const u8 as usize) - (&cu as *const ReprCU8Data as usize),
        _ => unreachable!(),
    };
    assert_eq!(u_off, 1);
    assert_eq!(cu_off, 2);
    println!("MIRI_OFFSETS=({}, {})", u_off, cu_off);
}
""",
    "miri_invalid_repr_u8_tag_ub_caught": r"""
use core::mem::transmute;
#[repr(u8)]
#[derive(Debug)]
enum ReprU8Data {
    A(u16) = 5,
    B(u8) = 9,
}
fn main() {
    let raw: [u8; 4] = [7, 0, 0, 0];
    let bad: ReprU8Data = unsafe { transmute(raw) };
    println!("{:?}", bad);
}
""",
}

ZEROCOPY_PROBE_MAIN = r"""
#![allow(dead_code)]
use core::num::NonZeroU8;
use zerocopy::{Immutable, KnownLayout, TryFromBytes};

#[derive(TryFromBytes, KnownLayout, Immutable, Debug, PartialEq, Eq)]
#[repr(u8)]
enum PacketU8 {
    A(u16) = 5,
    B(u8) = 9,
    C(bool) = 12,
}

#[derive(TryFromBytes, KnownLayout, Immutable, Debug, PartialEq, Eq)]
#[repr(C)]
enum PacketC {
    A(u16),
    B(bool),
}

#[repr(align(4))]
struct Aligned8([u8; 8]);

#[repr(align(4))]
struct Aligned4([u8; 4]);

fn main() {
    let b0 = bool::try_ref_from_bytes(&[0]).copied().ok();
    let b1 = bool::try_ref_from_bytes(&[1]).copied().ok();
    let b2_err = bool::try_ref_from_bytes(&[2]).is_err();
    let b255_err = bool::try_ref_from_bytes(&[255]).is_err();

    let c_ok_buf = Aligned4(0x41u32.to_le_bytes());
    let c_ok = char::try_ref_from_bytes(&c_ok_buf.0).copied().ok();
    let c_surr_buf = Aligned4(0xD800u32.to_le_bytes());
    let c_surr_err = char::try_ref_from_bytes(&c_surr_buf.0).is_err();
    let c_oob_buf = Aligned4(0xFFFFFFFFu32.to_le_bytes());
    let c_oob_err = char::try_ref_from_bytes(&c_oob_buf.0).is_err();

    let onz0 = Option::<NonZeroU8>::try_ref_from_bytes(&[0]).copied().ok();
    let onz7 = Option::<NonZeroU8>::try_ref_from_bytes(&[7]).copied().ok().flatten().map(|n| n.get());

    // PacketU8: #[repr(u8)] -> B(u8) at offset 1, C(bool) at offset 1, A(u16) at offset 2.
    let pu8_a_buf = Aligned4([5, 0xFF, 0x34, 0x12]);
    let pu8_a_ok = matches!(PacketU8::try_ref_from_bytes(&pu8_a_buf.0), Ok(PacketU8::A(0x1234)));
    let pu8_b_buf = Aligned4([9, 0x42, 0xAA, 0xBB]);
    let pu8_b_ok = matches!(PacketU8::try_ref_from_bytes(&pu8_b_buf.0), Ok(PacketU8::B(0x42)));
    let pu8_c_ok_buf = Aligned4([12, 1, 0xFF, 0xFF]);
    let pu8_c_ok = matches!(PacketU8::try_ref_from_bytes(&pu8_c_ok_buf.0), Ok(PacketU8::C(true)));
    let pu8_c_bad_field_buf = Aligned4([12, 2, 0, 0]);
    let pu8_c_bad_field_err = PacketU8::try_ref_from_bytes(&pu8_c_bad_field_buf.0).is_err();
    let pu8_bad_tag_buf = Aligned4([7, 0, 0, 0]);
    let pu8_bad_tag_err = PacketU8::try_ref_from_bytes(&pu8_bad_tag_buf.0).is_err();

    // PacketC: #[repr(C)] -> 4-byte tag at 0..4, payload at 4..6, size 8.
    let mut pc_b_ok_bytes = [0u8; 8];
    pc_b_ok_bytes[0..4].copy_from_slice(&1u32.to_le_bytes());
    pc_b_ok_bytes[4] = 1;
    let pc_b_ok_buf = Aligned8(pc_b_ok_bytes);
    let pc_b_ok = matches!(PacketC::try_ref_from_bytes(&pc_b_ok_buf.0), Ok(PacketC::B(true)));

    let mut pc_b_bad_field_bytes = [0u8; 8];
    pc_b_bad_field_bytes[0..4].copy_from_slice(&1u32.to_le_bytes());
    pc_b_bad_field_bytes[4] = 2;
    let pc_b_bad_field_buf = Aligned8(pc_b_bad_field_bytes);
    let pc_b_bad_field_err = PacketC::try_ref_from_bytes(&pc_b_bad_field_buf.0).is_err();

    let mut pc_bad_tag_bytes = [0u8; 8];
    pc_bad_tag_bytes[0..4].copy_from_slice(&99u32.to_le_bytes());
    let pc_bad_tag_buf = Aligned8(pc_bad_tag_bytes);
    let pc_bad_tag_err = PacketC::try_ref_from_bytes(&pc_bad_tag_buf.0).is_err();

    println!(
        "ZC_RESULTS bool=({:?},{:?},{},{}) char=({:?},{},{}) onz=({:?},{:?}) pkt_u8=({},{},{},{},{}) pkt_c=({},{},{})",
        b0, b1, b2_err, b255_err,
        c_ok, c_surr_err, c_oob_err,
        onz0, onz7,
        pu8_a_ok, pu8_b_ok, pu8_c_ok, pu8_c_bad_field_err, pu8_bad_tag_err,
        pc_b_ok, pc_b_bad_field_err, pc_bad_tag_err
    );
    assert_eq!(b0, Some(false));
    assert_eq!(b1, Some(true));
    assert!(b2_err && b255_err);
    assert_eq!(c_ok, Some('A'));
    assert!(c_surr_err && c_oob_err);
    assert_eq!(onz0, Some(None));
    assert_eq!(onz7, Some(7));
    assert!(pu8_a_ok && pu8_b_ok && pu8_c_ok && pu8_c_bad_field_err && pu8_bad_tag_err);
    assert!(pc_b_ok && pc_b_bad_field_err && pc_bad_tag_err);
}
"""

ZEROCOPY_REJECT_CU8_SRC = r"""
use zerocopy::TryFromBytes;

#[derive(TryFromBytes)]
#[repr(C, u8)]
enum RejectCU8 {
    A(u16) = 5,
    B(u8) = 9,
}

fn main() {}
"""


def _write_cargo_project(proj_dir: Path, name: str, edition: str, main_src: str,
                         extra_deps: str = "", vendor_dir: Path | None = None,
                         lock_file: Path | None = None) -> None:
    (proj_dir / "src").mkdir(parents=True, exist_ok=True)
    (proj_dir / "Cargo.toml").write_text(
        f'[package]\nname = "{name}"\nversion = "0.1.0"\nedition = "{edition}"\n\n[dependencies]\n{extra_deps}\n',
        encoding="utf-8",
    )
    (proj_dir / "src" / "main.rs").write_text(main_src, encoding="utf-8")
    if vendor_dir is not None:
        (proj_dir / ".cargo").mkdir(exist_ok=True)
        (proj_dir / ".cargo" / "config.toml").write_text(
            f'[env]\n__ZEROCOPY_LOCAL_DEV = "1"\n\n[source.crates-io]\nreplace-with = "vendored-sources"\n\n[source.vendored-sources]\ndirectory = "{vendor_dir}"\n',
            encoding="utf-8",
        )
    if lock_file is not None and lock_file.is_file():
        shutil.copy2(lock_file, proj_dir / "Cargo.lock")


def run_probes(zerocopy_arg: str | None) -> dict:
    home_dir = str(Path.home())
    env = os.environ.copy()
    cargo_bin = str(Path.home() / ".cargo" / "bin")
    if cargo_bin not in env.get("PATH", ""):
        env["PATH"] = f"{cargo_bin}:{env.get('PATH', '')}"

    zc_dir = _find_zerocopy_dir(zerocopy_arg)
    zc_str = str(zc_dir) if zc_dir else None

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        rustc_ver = _run(["rustc", "-Vv"], env=env, tmp_dir=tmp, home_dir=home_dir, zc_dir=zc_str)
        miri_ver = _run(["cargo", "miri", "--version"], env=env, tmp_dir=tmp, home_dir=home_dir, zc_dir=zc_str)

        # 1. -Zprint-type-sizes + native execution
        probe_rs = tmp_path / "probe.rs"
        probe_bin = tmp_path / "probe_bin"
        probe_rs.write_text(TYPE_SIZE_AND_EXEC_SRC, encoding="utf-8")

        pts = _run(
            ["rustc", "--edition=2024", "-Zprint-type-sizes", str(probe_rs), "-o", str(probe_bin)],
            cwd=tmp_path,
            env=env,
            tmp_dir=tmp,
            home_dir=home_dir,
            zc_dir=zc_str,
        )
        exec_res = _run(
            [str(probe_bin)],
            cwd=tmp_path,
            env=env,
            tmp_dir=tmp,
            home_dir=home_dir,
            zc_dir=zc_str,
        )
        parsed_exec = json.loads(exec_res["stdout"]) if exec_res["returncode"] == 0 else None

        # 2. E0732 negative compilation tests
        e0732_rs = tmp_path / "e0732.rs"
        e0732_rs.write_text(E0732_SRC, encoding="utf-8")
        e0732_res = _run(
            ["rustc", "--edition=2024", "--error-format=short", str(e0732_rs), "-o", str(tmp_path / "e0732_bin")],
            cwd=tmp_path,
            env=env,
            tmp_dir=tmp,
            home_dir=home_dir,
            zc_dir=zc_str,
        )
        e0732_unit_rs = tmp_path / "e0732_unit.rs"
        e0732_unit_rs.write_text(E0732_UNIT_DISCR_SRC, encoding="utf-8")
        e0732_unit_res = _run(
            ["rustc", "--edition=2024", "--error-format=short", str(e0732_unit_rs), "-o", str(tmp_path / "e0732_unit_bin")],
            cwd=tmp_path,
            env=env,
            tmp_dir=tmp,
            home_dir=home_dir,
            zc_dir=zc_str,
        )

        # 3. Miri tests (sharing target dir inside TemporaryDirectory)
        miri_target = tmp_path / "miri_target"
        miri_env = env.copy()
        miri_env["CARGO_TARGET_DIR"] = str(miri_target)
        miri_results = {}
        for case_name, src in MIRI_CASES.items():
            case_dir = tmp_path / f"miri_{case_name}"
            _write_cargo_project(case_dir, f"miri_{case_name}", "2024", src)
            miri_results[case_name] = _run(
                ["cargo", "miri", "run", "--offline"],
                cwd=case_dir,
                env=miri_env,
                tmp_dir=tmp,
                home_dir=home_dir,
                zc_dir=zc_str,
            )

        # 4. Real zerocopy::TryFromBytes tests (native + Miri + negative repr(C, u8))
        zc_results: dict[str, object] = {"zerocopy_available": zc_dir is not None}
        if zc_dir is not None:
            zc_target = tmp_path / "zc_target"
            zc_env = env.copy()
            zc_env["CARGO_TARGET_DIR"] = str(zc_target)
            deps = f'zerocopy = {{ path = "{zc_dir}", features = ["derive"] }}'

            zc_proj = tmp_path / "zc_probe"
            _write_cargo_project(
                zc_proj,
                "zc_probe",
                "2024",
                ZEROCOPY_PROBE_MAIN,
                extra_deps=deps,
                vendor_dir=zc_dir / "vendor",
                lock_file=zc_dir / "Cargo.lock",
            )
            zc_results["native_run"] = _run(
                ["cargo", "run", "--offline"],
                cwd=zc_proj,
                env=zc_env,
                tmp_dir=tmp,
                home_dir=home_dir,
                zc_dir=zc_str,
            )
            zc_results["miri_run"] = _run(
                ["cargo", "miri", "run", "--offline"],
                cwd=zc_proj,
                env=zc_env,
                tmp_dir=tmp,
                home_dir=home_dir,
                zc_dir=zc_str,
            )

            zc_reject_proj = tmp_path / "zc_reject_cu8"
            _write_cargo_project(
                zc_reject_proj,
                "zc_reject_cu8",
                "2024",
                ZEROCOPY_REJECT_CU8_SRC,
                extra_deps=deps,
                vendor_dir=zc_dir / "vendor",
                lock_file=zc_dir / "Cargo.lock",
            )
            zc_results["reject_repr_c_u8"] = _run(
                ["cargo", "check", "--offline"],
                cwd=zc_reject_proj,
                env=zc_env,
                tmp_dir=tmp,
                home_dir=home_dir,
                zc_dir=zc_str,
            )

    return {
        "rustc_version": rustc_ver["stdout"],
        "miri_version": miri_ver["stdout"],
        "a_type_sizes_and_niche_bit_patterns": {
            "print_type_sizes": pts,
            "niche_and_repr_execution": exec_res,
            "parsed_execution_values": parsed_exec,
            "e0732_non_unit_explicit_discr": e0732_res,
            "e0732_unit_explicit_discr_with_non_unit_variant": e0732_unit_res,
        },
        "b_miri_enum_validity": miri_results,
        "c_zerocopy_try_from_bytes": zc_results,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT, help="Output JSON path")
    parser.add_argument("--zerocopy-dir", default=None, help="Path to zerocopy crate root")
    args = parser.parse_args()

    results = run_probes(args.zerocopy_dir)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
