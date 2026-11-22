#!/usr/bin/env python3
"""Differential rustc + Miri probe for MIR UbChecks, RuntimeChecks, and CheckEnums.

Executes:
  1. 12 single-crate probes (8 core cases matching the 1.102.0-nightly reference
     baseline plus 4 soundness/completeness probes covering signed-niche
     sign-extension, unsized raw-pointer skips, and field-load vs borrow
     projection asymmetry) across:
       - rustc -C opt-level=0 -Z ub-checks=yes (with MIR pass dumps)
       - rustc -C opt-level=0 -Z ub-checks=no
       - Miri (when installed and sysroot available)
  2. Cross-crate up_lib -> down RuntimeChecks matrix:
       - All 4 combinations of up_ub in {no, yes} x down_ub in {no, yes}
         with up_lib at -C opt-level=2
       - up_lib at -C opt-level=0 (default mir-opt-level=1) vs -Z mir-opt-level=0
       - up_lib with #![rustc_preserve_ub_checks] at -C opt-level=2 -Z ub-checks=no
       - cross-crate RuntimeChecks::OverflowChecks comparison (not folded by SimplifyUbCheck)

Standalone, Python 3.10+ stdlib only. Produces sanitized JSON output.
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


PID_RE = re.compile(r"(thread '[^']+' \()\d+(\) panicked)")
ADDR_RE = re.compile(r"0x[0-9a-fA-F]{6,}")
RUSTC_DEV_RE = re.compile(r"/rustc(?:-dev)?/[0-9a-f]{7,40}/")


def sanitize_text(text: str, tmpdir: str) -> str:
    """Strip temporary paths, home paths, and volatile PIDs from compiler/runtime output."""
    out = text.replace(tmpdir, "<tmp>")
    home = os.path.expanduser("~")
    if home and home != "/":
        out = out.replace(home, "<home>")
    out = RUSTC_DEV_RE.sub("<rustc>/", out)
    out = PID_RE.sub(r"\1<pid>\2", out)
    return out


def run_cmd(
    cmd: list[str],
    *,
    cwd: Path,
    env: dict[str, str],
    timeout: int = 60,
) -> tuple[int, str, str]:
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(cwd),
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return proc.returncode, proc.stdout, proc.stderr
    except subprocess.TimeoutExpired as exc:
        return -999, (exc.stdout or ""), f"TIMEOUT after {timeout}s"


def detect_miri(env: dict[str, str]) -> tuple[str | None, str | None]:
    """Locate miri binary and prebuilt sysroot if available offline."""
    rc, sysroot_out, _ = run_cmd(["rustc", "--print", "sysroot"], cwd=Path("/tmp"), env=env)
    miri_bin: str | None = None
    if rc == 0:
        candidate = Path(sysroot_out.strip()) / "bin" / "miri"
        if candidate.is_file() and os.access(candidate, os.X_OK):
            miri_bin = str(candidate)
    if miri_bin is None:
        miri_bin = shutil.which("miri", path=env.get("PATH"))

    miri_sysroot: str | None = None
    for env_key in ("MIRI_SYSROOT",):
        val = env.get(env_key)
        if val and (Path(val) / "lib" / "rustlib").is_dir():
            miri_sysroot = val
            break
    if miri_sysroot is None:
        default_cache = Path.home() / ".cache" / "miri"
        if (default_cache / "lib" / "rustlib").is_dir():
            miri_sysroot = str(default_cache)
    return miri_bin, miri_sysroot


SINGLE_CRATE_CASES: list[dict[str, Any]] = [
    {
        "name": "ub_01_misaligned_raw_ptr_read_caught",
        "code": r"""#[repr(align(16))]
struct AlignedBuf([u8; 16]);

fn main() {
    let buf = AlignedBuf([0; 16]);
    let p = unsafe { buf.0.as_ptr().add(1) as *const u32 };
    let v = unsafe { *std::hint::black_box(p) };
    println!("V={v}");
}
""",
        "run_miri": True,
    },
    {
        "name": "ub_02_borrowed_field_projection_uses_field_align_not_struct_align",
        "code": r"""#[repr(align(16))]
struct AlignedBuf([u8; 64]);

#[repr(C, align(16))]
struct OverAligned {
    byte_field: u8,
    word_field: u32,
}

fn main() {
    let buf = AlignedBuf([0; 64]);
    let p = unsafe { buf.0.as_ptr().add(1) as *const OverAligned };
    let r: &u8 = unsafe { &(*std::hint::black_box(p)).byte_field };
    println!("BYTE={}", *r);
}
""",
        "run_miri": True,
    },
    {
        "name": "ub_03_borrowed_u32_field_projection_misaligned_caught",
        "code": r"""#[repr(align(16))]
struct AlignedBuf([u8; 64]);

#[repr(C, align(16))]
struct OverAligned {
    byte_field: u8,
    word_field: u32,
}

fn main() {
    let buf = AlignedBuf([0; 64]);
    let p = unsafe { buf.0.as_ptr().add(1) as *const OverAligned };
    let r: &u32 = unsafe { &(*std::hint::black_box(p)).word_field };
    println!("WORD={}", *r);
}
""",
        "run_miri": True,
    },
    {
        "name": "ub_04_zst_null_raw_copy_allowed_vs_zst_null_borrow_rejected",
        "code": r"""fn main() {
    let p: *const () = std::hint::black_box(core::ptr::null());
    let v: () = unsafe { *p };
    println!("RAW_ZST_OK={v:?}");
    let r: &() = unsafe { &*p };
    println!("REF_ZST={r:p}");
}
""",
        "run_miri": True,
    },
    {
        "name": "ub_05_check_enums_direct_negative_signed_discriminant",
        "code": r"""#[repr(isize)]
enum NegFieldless {
    MinusOne = -1,
    PlusOne = 1,
}

fn main() {
    let ok: NegFieldless = unsafe { std::mem::transmute(std::hint::black_box(-1isize)) };
    println!("VALID_NEG_OK={}", ok as isize);
    let bad: NegFieldless = unsafe { std::mem::transmute(std::hint::black_box(0isize)) };
    println!("INVALID_ZERO={}", bad as isize);
}
""",
        "run_miri": True,
    },
    {
        "name": "ub_06_check_enums_wrapping_niche_valid_vs_invalid",
        "code": r"""#[repr(u8)]
enum High {
    H254 = 254,
    H255 = 255,
}

fn main() {
    let ok_some: Option<High> = unsafe { std::mem::transmute(std::hint::black_box(254u8)) };
    let ok_none: Option<High> = unsafe { std::mem::transmute(std::hint::black_box(0u8)) };
    println!("WRAP_OK={} {}", ok_some.is_some(), ok_none.is_none());
    let bad: Option<High> = unsafe { std::mem::transmute(std::hint::black_box(100u8)) };
    println!("WRAP_BAD={}", bad.is_some());
}
""",
        "run_miri": True,
    },
    {
        "name": "ub_07_check_enums_blind_spot_ptr_read_bypasses_transmute_visitor",
        "code": r"""#[repr(u8)]
#[derive(Copy, Clone)]
enum BinaryTag {
    Zero = 0,
    One = 1,
}

#[repr(C)]
union RawOrEnum {
    raw: u8,
    en: BinaryTag,
}

fn main() {
    let invalid_byte: u8 = std::hint::black_box(2u8);
    let via_ptr: BinaryTag = unsafe { *(&raw const invalid_byte as *const BinaryTag) };
    let u = RawOrEnum { raw: std::hint::black_box(2u8) };
    let via_union: BinaryTag = unsafe { u.en };
    println!(
        "BYPASSED_CHECK_ENUMS={} {}",
        std::mem::size_of_val(&via_ptr),
        std::mem::size_of_val(&via_union)
    );
}
""",
        "run_miri": True,
    },
    {
        "name": "ub_08_ub_check_assert_nounwind_aborts_even_inside_catch_unwind",
        "code": r"""fn main() {
    let res = std::panic::catch_unwind(|| {
        let p: *const u32 = std::hint::black_box(core::ptr::null());
        unsafe { *p }
    });
    println!("CAUGHT={}", res.is_err());
}
""",
        "run_miri": True,
    },
    {
        "name": "ub_09_signed_niche_false_positive_valid_transmute_aborts",
        "code": r"""#[repr(i8)]
#[derive(Debug, Copy, Clone)]
enum NegMid {
    A = -10,
    B = -9,
}

fn main() {
    let ok: Option<NegMid> =
        unsafe { std::mem::transmute::<u8, Option<NegMid>>(std::hint::black_box((-10i8) as u8)) };
    println!("VALID_NEGMID={ok:?}");
}
""",
        "run_miri": True,
    },
    {
        "name": "ub_10_signed_niche_false_negative_wrapping_0x80_bypass",
        "code": r"""#[repr(i8)]
#[derive(Debug, Copy, Clone)]
enum NegHigh {
    MinusTwo = -2,
    MinusOne = -1,
}

fn main() {
    let ok1: Option<NegHigh> =
        unsafe { std::mem::transmute::<u8, Option<NegHigh>>(std::hint::black_box((-2i8) as u8)) };
    let ok2: Option<NegHigh> =
        unsafe { std::mem::transmute::<u8, Option<NegHigh>>(std::hint::black_box(0u8)) };
    println!("VALID_NEGHIGH={} {}", ok1.is_some(), ok2.is_none());
    let bad_neg: Option<NegHigh> =
        unsafe { std::mem::transmute::<u8, Option<NegHigh>>(std::hint::black_box(0x80u8)) };
    println!("BYPASSED_SIGNED_NICHE_0x80={}", bad_neg.is_some());
}
""",
        "run_miri": True,
    },
    {
        "name": "ub_11_check_pointers_unsized_slice_raw_ptr_blind_spot",
        "code": r"""#[repr(align(16))]
struct AlignedBuf([u8; 16]);

fn main() {
    let buf = AlignedBuf([0; 16]);
    let raw_elem = unsafe { buf.0.as_ptr().add(1) as *const u32 };
    let raw_slice: *const [u32] = core::ptr::slice_from_raw_parts(raw_elem, 2);
    let r: &[u32] = unsafe { &*std::hint::black_box(raw_slice) };
    println!("UNSIZED_LEN={}", r.len());
}
""",
        "run_miri": True,
    },
    {
        "name": "ub_12_raw_borrow_allowed_vs_direct_field_load_checked",
        "code": r"""#[repr(align(16))]
struct AlignedBuf([u8; 64]);

#[repr(C, align(16))]
struct OverAligned {
    byte_field: u8,
    word_field: u32,
}

fn main() {
    let buf = AlignedBuf([0; 64]);
    let p = unsafe { buf.0.as_ptr().add(1) as *const OverAligned };
    let raw_field: *const u8 = unsafe { &raw const (*std::hint::black_box(p)).byte_field };
    println!("RAW_BORROW_OK={}", !raw_field.is_null());
    let loaded: u8 = unsafe { (*std::hint::black_box(p)).byte_field };
    println!("DIRECT_FIELD_LOAD={loaded}");
}
""",
        "run_miri": True,
    },
]


def summarize_mir_dumps(mir_dir: Path) -> dict[str, dict[str, Any]]:
    summary: dict[str, dict[str, Any]] = {}
    if not mir_dir.is_dir():
        return summary
    for p in sorted(mir_dir.glob("*.mir")):
        text = p.read_text(encoding="utf-8", errors="replace")
        summary[p.name] = {
            "has_ub_checks": "UbChecks" in text,
            "has_overflow_checks": "OverflowChecks" in text,
            "has_misaligned_assert": "misaligned pointer dereference" in text,
            "has_null_deref_assert": "null pointer dereference occurred" in text,
            "has_null_ref_assert": "null reference produced" in text,
            "has_invalid_enum_assert": "trying to construct an enum from an invalid value" in text,
            "has_unwind_unreachable": "unwind unreachable" in text,
            "lines": len(text.splitlines()),
        }
    return summary


def run_single_crate_case(
    tmpdir: Path,
    spec: dict[str, Any],
    env: dict[str, str],
    miri_bin: str | None,
    miri_sysroot: str | None,
) -> dict[str, Any]:
    name = spec["name"]
    case_dir = tmpdir / name
    case_dir.mkdir(parents=True, exist_ok=True)
    src = case_dir / "probe.rs"
    src.write_text(spec["code"], encoding="utf-8")

    out: dict[str, Any] = {}
    for mode_key, ub_val, dump_mir in (
        ("ub_checks_yes", "yes", True),
        ("ub_checks_no", "no", False),
    ):
        bin_path = case_dir / f"bin_{mode_key}"
        mir_dir = case_dir / f"mir_{mode_key}"
        flags = ["-C", "opt-level=0", "-Z", f"ub-checks={ub_val}"]
        cmd = ["rustc", "--edition=2024", "--crate-name=probe"] + flags
        if dump_mir:
            mir_dir.mkdir(parents=True, exist_ok=True)
            cmd += [
                "-Z",
                "dump-mir=CheckAlignment | CheckNull | CheckEnums | runtime-optimized",
                "-Z",
                f"dump-mir-dir={mir_dir}",
                "-Z",
                "dump-mir-graphviz=no",
            ]
        cmd += [str(src), "-o", str(bin_path)]
        comp_rc, _, comp_err = run_cmd(cmd, cwd=case_dir, env=env)
        entry: dict[str, Any] = {
            "flags": flags,
            "compile_rc": comp_rc,
            "compile_stderr": sanitize_text(comp_err[:800], str(tmpdir)),
        }
        if comp_rc == 0:
            run_rc, run_out, run_err = run_cmd([str(bin_path)], cwd=case_dir, env=env)
            entry["run_rc"] = run_rc
            entry["run_stdout"] = run_out.strip()
            entry["run_stderr_head"] = sanitize_text(run_err.strip()[:600], str(tmpdir))
        if dump_mir:
            entry["mir_dumps"] = summarize_mir_dumps(mir_dir)
        out[mode_key] = entry

    if spec.get("run_miri") and miri_bin and miri_sysroot:
        miri_cmd = [
            miri_bin,
            "--edition=2024",
            "--crate-name=probe",
            "--sysroot",
            miri_sysroot,
            str(src),
        ]
        m_rc, m_out, m_err = run_cmd(miri_cmd, cwd=case_dir, env=env)
        err_clean = sanitize_text(m_err, str(tmpdir))
        ub_lines = [ln for ln in err_clean.splitlines() if "Undefined Behavior:" in ln or ln.startswith("error:")]
        out["miri"] = {
            "rc": m_rc,
            "ub_detected": "Undefined Behavior:" in err_clean,
            "stdout": m_out.strip(),
            "error_summary": "\n".join(ub_lines[:6]),
        }
    return out


UP_LIB_CODE_TEMPLATE = r"""#![allow(internal_features)]
#![feature(core_intrinsics)]
{extra_attrs}

#[inline(always)]
pub fn inlined_ub_check(idx: usize, len: usize) -> usize {{
    if core::intrinsics::ub_checks() && idx >= len {{
        panic!("UP_LIB_UB_CHECK_FIRED");
    }}
    idx.wrapping_add(len)
}}

#[inline(always)]
pub fn generic_ub_check<T>(slice: &[T], idx: usize) -> usize {{
    if core::intrinsics::ub_checks() && idx >= slice.len() {{
        panic!("UP_LIB_GENERIC_UB_CHECK_FIRED");
    }}
    idx.wrapping_add(slice.len())
}}

#[inline(never)]
pub fn non_generic_ub_check(idx: usize, len: usize) -> usize {{
    if core::intrinsics::ub_checks() && idx >= len {{
        panic!("UP_LIB_UB_CHECK_FIRED");
    }}
    idx.wrapping_add(len)
}}

#[inline(always)]
pub fn generic_overflow_check<T>(slice: &[T], idx: usize) -> usize {{
    if core::intrinsics::overflow_checks() && idx >= slice.len() {{
        panic!("UP_LIB_OVERFLOW_CHECK_FIRED");
    }}
    idx.wrapping_add(slice.len())
}}
"""

DOWN_CODE = r"""extern crate up_lib;

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    let arr = [10u8, 20, 30, 40];
    match mode.as_str() {
        "inlined_oob" => {
            let v = up_lib::inlined_ub_check(std::hint::black_box(10), arr.len());
            std::hint::black_box(v);
        }
        "generic_oob" => {
            let v = up_lib::generic_ub_check(&arr, std::hint::black_box(10));
            std::hint::black_box(v);
        }
        "non_generic_oob" => {
            let v = up_lib::non_generic_ub_check(std::hint::black_box(10), arr.len());
            std::hint::black_box(v);
        }
        "std_get_unchecked_oob" => {
            let v = unsafe { *arr.get_unchecked(std::hint::black_box(10)) };
            std::hint::black_box(v);
        }
        "generic_overflow_check_oob" => {
            let v = up_lib::generic_overflow_check(&arr, std::hint::black_box(10));
            std::hint::black_box(v);
        }
        _ => panic!("unknown mode"),
    }
}
"""


def run_cross_crate_config(
    tmpdir: Path,
    name: str,
    *,
    up_flags: list[str],
    down_flags: list[str],
    extra_up_attrs: str = "",
    modes: tuple[str, ...] = ("inlined_oob", "generic_oob", "non_generic_oob", "std_get_unchecked_oob"),
    env: dict[str, str],
) -> dict[str, Any]:
    cdir = tmpdir / f"xc_{name}"
    cdir.mkdir(parents=True, exist_ok=True)
    up_src = cdir / "up_lib.rs"
    down_src = cdir / "down.rs"
    up_rlib = cdir / "libup_lib.rlib"
    down_bin = cdir / "down_bin"
    mir_dir = cdir / "up_mir"
    mir_dir.mkdir(parents=True, exist_ok=True)

    up_src.write_text(UP_LIB_CODE_TEMPLATE.format(extra_attrs=extra_up_attrs), encoding="utf-8")
    down_src.write_text(DOWN_CODE, encoding="utf-8")

    up_cmd = [
        "rustc",
        "--edition=2024",
        "--crate-type=rlib",
        "--crate-name=up_lib",
        "-Z",
        "dump-mir=InstSimplify-before-inline | runtime-optimized",
        "-Z",
        f"dump-mir-dir={mir_dir}",
        "-Z",
        "dump-mir-graphviz=no",
    ] + up_flags + [str(up_src), "-o", str(up_rlib)]
    up_rc, _, up_err = run_cmd(up_cmd, cwd=cdir, env=env)

    result: dict[str, Any] = {
        "up_flags": up_flags,
        "down_flags": down_flags,
        "extra_up_attrs": extra_up_attrs.strip(),
        "up_rc": up_rc,
        "up_mir_summary": summarize_mir_dumps(mir_dir),
    }
    if up_rc != 0:
        result["up_stderr"] = sanitize_text(up_err[:600], str(tmpdir))
        return result

    down_cmd = [
        "rustc",
        "--edition=2024",
        "--crate-name=down",
        "--extern",
        f"up_lib={up_rlib}",
    ] + down_flags + [str(down_src), "-o", str(down_bin)]
    down_rc, _, down_err = run_cmd(down_cmd, cwd=cdir, env=env)
    result["down_rc"] = down_rc
    if down_rc != 0:
        result["down_stderr"] = sanitize_text(down_err[:600], str(tmpdir))
        return result

    for mode in modes:
        rc, out_s, err_s = run_cmd([str(down_bin), mode], cwd=cdir, env=env)
        clean_err = sanitize_text(err_s.strip()[:600], str(tmpdir))
        result[mode] = {
            "rc": rc,
            "stdout": out_s.strip(),
            "panicked_ub_check": rc != 0 and (
                "UB_CHECK_FIRED" in clean_err
                or "OVERFLOW_CHECK_FIRED" in clean_err
                or "unsafe precondition(s) violated" in clean_err
            ),
            "stderr_head": clean_err,
        }
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=None, help="Output JSON file path")
    args = parser.parse_args()

    env = dict(os.environ)
    cargo_bin = str(Path.home() / ".cargo" / "bin")
    if cargo_bin not in env.get("PATH", "").split(os.pathsep):
        env["PATH"] = f"{cargo_bin}{os.pathsep}{env.get('PATH', '')}"

    rc_v, rustc_ver, _ = run_cmd(["rustc", "-Vv"], cwd=Path("/tmp"), env=env)
    if rc_v != 0:
        print("ERROR: rustc not found in PATH", file=sys.stderr)
        return 1

    miri_bin, miri_sysroot = detect_miri(env)
    miri_ver = None
    if miri_bin:
        m_v_rc, m_v_out, _ = run_cmd([miri_bin, "--version"], cwd=Path("/tmp"), env=env)
        if m_v_rc == 0:
            miri_ver = m_v_out.strip()

    results: dict[str, Any] = {
        "rustc_version": rustc_ver.strip(),
        "miri_available": bool(miri_bin and miri_sysroot),
        "miri_version": miri_ver,
        "cases": {},
        "cross_crate_runtime_checks": {},
    }

    with tempfile.TemporaryDirectory(prefix="ubchk_probe_") as td:
        tmpdir = Path(td)
        for spec in SINGLE_CRATE_CASES:
            results["cases"][spec["name"]] = run_single_crate_case(
                tmpdir, spec, env, miri_bin, miri_sysroot
            )

        xc_configs: list[tuple[str, list[str], list[str], str, tuple[str, ...]]] = [
            (
                "up_no__down_no",
                ["-C", "opt-level=2", "-Z", "ub-checks=no"],
                ["-C", "opt-level=0", "-Z", "ub-checks=no"],
                "",
                ("inlined_oob", "generic_oob", "non_generic_oob", "std_get_unchecked_oob"),
            ),
            (
                "up_no__down_yes",
                ["-C", "opt-level=2", "-Z", "ub-checks=no"],
                ["-C", "opt-level=0", "-Z", "ub-checks=yes"],
                "",
                ("inlined_oob", "generic_oob", "non_generic_oob", "std_get_unchecked_oob"),
            ),
            (
                "up_yes__down_no",
                ["-C", "opt-level=2", "-Z", "ub-checks=yes"],
                ["-C", "opt-level=0", "-Z", "ub-checks=no"],
                "",
                ("inlined_oob", "generic_oob", "non_generic_oob", "std_get_unchecked_oob"),
            ),
            (
                "up_yes__down_yes",
                ["-C", "opt-level=2", "-Z", "ub-checks=yes"],
                ["-C", "opt-level=0", "-Z", "ub-checks=yes"],
                "",
                ("inlined_oob", "generic_oob", "non_generic_oob", "std_get_unchecked_oob"),
            ),
            (
                "up_no_opt0_default__down_yes",
                ["-C", "opt-level=0", "-Z", "ub-checks=no"],
                ["-C", "opt-level=0", "-Z", "ub-checks=yes"],
                "",
                ("inlined_oob", "generic_oob", "non_generic_oob", "std_get_unchecked_oob"),
            ),
            (
                "up_no_miropt0__down_yes",
                ["-C", "opt-level=0", "-Z", "mir-opt-level=0", "-Z", "ub-checks=no"],
                ["-C", "opt-level=0", "-Z", "ub-checks=yes"],
                "",
                ("inlined_oob", "generic_oob", "non_generic_oob", "std_get_unchecked_oob"),
            ),
            (
                "up_no_preserve_attr__down_yes",
                ["-C", "opt-level=2", "-Z", "ub-checks=no"],
                ["-C", "opt-level=0", "-Z", "ub-checks=yes"],
                "#![feature(rustc_attrs)]\n#![rustc_preserve_ub_checks]",
                ("inlined_oob", "generic_oob", "non_generic_oob", "std_get_unchecked_oob"),
            ),
            (
                "up_ovf_no__down_ovf_yes",
                ["-C", "opt-level=2", "-C", "overflow-checks=no"],
                ["-C", "opt-level=0", "-C", "overflow-checks=yes"],
                "",
                ("generic_overflow_check_oob",),
            ),
            (
                "up_ovf_yes__down_ovf_no",
                ["-C", "opt-level=2", "-C", "overflow-checks=yes"],
                ["-C", "opt-level=0", "-C", "overflow-checks=no"],
                "",
                ("generic_overflow_check_oob",),
            ),
        ]
        for xc_name, up_f, down_f, extra_a, modes in xc_configs:
            results["cross_crate_runtime_checks"][xc_name] = run_cross_crate_config(
                tmpdir,
                xc_name,
                up_flags=up_f,
                down_flags=down_f,
                extra_up_attrs=extra_a,
                modes=modes,
                env=env,
            )

    rendered = json.dumps(results, indent=2) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
