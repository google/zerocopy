#!/usr/bin/env python3
"""Standalone revalidation probe for Rust standard-library MIR capture and census claims.

Requires Python 3.10+ and only the Python standard library.
Accepts explicit paths to a `rustc` executable, sysroot, `library/` tree, and
optional `anneal-rustc-capture` binary so no host paths are assumed.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


RE_UNSAFE_FN = re.compile(r"\bunsafe\s+(?:extern\s+)?fn\b")
RE_UNSAFE_BLOCK = re.compile(r"\bunsafe\s*\{")
RE_UNSAFE_TRAIT = re.compile(r"\bunsafe\s+(?:auto\s+)?trait\b")
RE_UNSAFE_IMPL = re.compile(r"\bunsafe\s+impl\b")
RE_RUSTC_INTRINSIC = re.compile(r"#\s*\[\s*rustc_intrinsic\b")
RE_INTRINSIC_CALL = re.compile(r"\bintrinsics::([a-zA-Z0-9_]+)\b")
RE_UB_PRECOND = re.compile(r"\bassert_unsafe_precondition!\s*\(")
RE_INHERIT_OVF = re.compile(r"#\s*\[\s*rustc_inherit_overflow_checks\s*\]")
RE_LANG_ITEM = re.compile(r"#\s*\[\s*lang\s*=")
RE_SAFETY_DOC = re.compile(r"^\s*(?:///|//!)\s*#+\s*Safety\b", re.MULTILINE)


def strip_comments_and_strings(src: str) -> str:
    """Replace comments and string literals with whitespace while preserving newlines."""
    out: list[str] = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if c == "/" and i + 1 < n and src[i + 1] == "/":
            j = src.find("\n", i)
            if j == -1:
                j = n
            out.append(" " * (j - i))
            i = j
        elif c == "/" and i + 1 < n and src[i + 1] == "*":
            depth = 1
            j = i + 2
            while j < n and depth > 0:
                if src[j : j + 2] == "/*":
                    depth += 1
                    j += 2
                elif src[j : j + 2] == "*/":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            seg = src[i:j]
            out.append("".join("\n" if ch == "\n" else " " for ch in seg))
            i = j
        elif c == "r" and i + 1 < n and src[i + 1] in ("#", '"'):
            j = i + 1
            hashes = 0
            while j < n and src[j] == "#":
                hashes += 1
                j += 1
            if j < n and src[j] == '"':
                end_pat = '"' + ("#" * hashes)
                k = src.find(end_pat, j + 1)
                if k != -1:
                    end = k + len(end_pat)
                    seg = src[i:end]
                    out.append("".join("\n" if ch == "\n" else " " for ch in seg))
                    i = end
                    continue
            out.append(c)
            i += 1
        elif c == '"':
            j = i + 1
            while j < n:
                if src[j] == "\\":
                    j += 2
                elif src[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            seg = src[i:j]
            out.append("".join("\n" if ch == "\n" else " " for ch in seg))
            i = j
        else:
            out.append(c)
            i += 1
    return "".join(out)


def scan_stdlib_census(library_dir: Path) -> dict[str, dict[str, int]]:
    """Scan non-test `.rs` files in `core/src`, `alloc/src`, and `std/src`."""
    crate_stats: dict[str, Counter[str]] = defaultdict(Counter)
    for crate in ("core", "alloc", "std"):
        src_root = library_dir / crate / "src"
        if not src_root.is_dir():
            raise FileNotFoundError(f"missing {src_root}")
        for path in sorted(src_root.rglob("*.rs")):
            rel = path.relative_to(library_dir).as_posix()
            if (
                "/tests/" in rel
                or "/benches/" in rel
                or rel.endswith("/tests.rs")
                or rel.endswith("/benches.rs")
            ):
                continue
            body = path.read_text(encoding="utf-8", errors="replace")
            stripped = strip_comments_and_strings(body)
            st = crate_stats[crate]
            st["files"] += 1
            st["loc"] += len(body.splitlines())
            st["unsafe_fn"] += len(RE_UNSAFE_FN.findall(stripped))
            st["unsafe_block"] += len(RE_UNSAFE_BLOCK.findall(stripped))
            st["unsafe_trait"] += len(RE_UNSAFE_TRAIT.findall(stripped))
            st["unsafe_impl"] += len(RE_UNSAFE_IMPL.findall(stripped))
            st["safety_docs"] += len(RE_SAFETY_DOC.findall(body))
            st["rustc_intrinsic_decl"] += len(RE_RUSTC_INTRINSIC.findall(stripped))
            st["intrinsic_call_sites"] += len(RE_INTRINSIC_CALL.findall(stripped))
            st["assert_unsafe_precondition"] += len(RE_UB_PRECOND.findall(stripped))
            st["inherit_overflow_checks"] += len(RE_INHERIT_OVF.findall(stripped))
            st["lang_items"] += len(RE_LANG_ITEM.findall(stripped))
    return {k: dict(v) for k, v in crate_stats.items()}


CHECKS_PROBE_SRC = """#![no_std]
#![allow(internal_features, incomplete_features)]
#![feature(core_intrinsics, rustc_attrs, contracts)]

#[rustc_inherit_overflow_checks]
pub const fn inherited_add_u32(a: u32, b: u32) -> u32 {
    a + b
}

pub unsafe fn nonzero_like_ub_check(n: u32) -> u32 {
    if core::intrinsics::ub_checks() && n == 0 {
        core::intrinsics::abort();
    }
    n
}

#[core::contracts::requires(x < 100)]
#[core::contracts::ensures(move |ret: &u32| *ret == x + 1)]
pub fn contracted_inc(x: u32) -> u32 {
    x + 1
}

#[core::contracts::requires(x < 100)]
pub fn contracted_req_only(x: u32) -> u32 {
    x + 1
}
"""


INTRINSICS_PROBE_SRC = """#![no_std]
#![allow(internal_features)]
#![feature(core_intrinsics)]
use core::cmp::Ordering;
use core::intrinsics;

pub fn i_wrapping_add(a: u32, b: u32) -> u32 { intrinsics::wrapping_add(a, b) }
pub fn i_add_with_overflow(a: u32, b: u32) -> (u32, bool) { intrinsics::add_with_overflow(a, b) }
pub fn i_three_way_compare(a: i32, b: i32) -> Ordering { intrinsics::three_way_compare(a, b) }
pub unsafe fn i_unreachable() -> ! { unsafe { intrinsics::unreachable() } }
pub fn i_forget(x: u32) { intrinsics::forget(x) }
pub fn i_size_of() -> usize { const { intrinsics::size_of::<u64>() } }
pub fn i_align_of() -> usize { const { intrinsics::align_of::<u64>() } }
pub fn i_abort() -> ! { intrinsics::abort() }

pub unsafe fn i_unchecked_add(a: u32, b: u32) -> u32 { unsafe { intrinsics::unchecked_add(a, b) } }
pub unsafe fn i_unchecked_shl(a: u32, b: u32) -> u32 { unsafe { intrinsics::unchecked_shl(a, b) } }
pub unsafe fn i_exact_div(a: u32, b: u32) -> u32 { unsafe { intrinsics::exact_div(a, b) } }
pub unsafe fn i_disjoint_bitor(a: u32, b: u32) -> u32 { unsafe { intrinsics::disjoint_bitor(a, b) } }
pub unsafe fn i_assume(b: bool) { unsafe { intrinsics::assume(b) } }
pub fn i_ub_checks() -> bool { intrinsics::ub_checks() }
pub unsafe fn i_transmute_unchecked(x: u32) -> i32 { unsafe { intrinsics::transmute_unchecked(x) } }
pub fn i_ctlz(x: u32) -> u32 { intrinsics::ctlz(x) }
pub fn i_ctpop(x: u32) -> u32 { intrinsics::ctpop(x) }
pub fn i_bswap(x: u32) -> u32 { intrinsics::bswap(x) }
pub fn i_rotate_left(x: u32, n: u32) -> u32 { intrinsics::rotate_left(x, n) }
pub fn i_saturating_add(a: u32, b: u32) -> u32 { intrinsics::saturating_add(x_or(a), b) }
pub fn i_is_val_statically_known(x: u32) -> bool { intrinsics::is_val_statically_known(x) }
pub fn i_select_unpredictable(c: bool, a: u32, b: u32) -> u32 { intrinsics::select_unpredictable(c, a, b) }
pub unsafe fn i_copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize) {
    unsafe { intrinsics::copy_nonoverlapping(src, dst, count) }
}
pub unsafe fn i_offset(p: *const u8, d: isize) -> *const u8 {
    unsafe { intrinsics::offset(p, d) }
}

const fn x_or(a: u32) -> u32 { a }
""".replace("x_or(a)", "a")


def probe_mir_phases(rustc: Path, sysroot: Path, work: Path) -> dict[str, bool]:
    """Verify PostCleanup vs Optimized MIR invariants for UbChecks, overflow, and contracts."""
    checks: dict[str, bool] = {}
    for label, prefix in (
        ("without_preserve", ""),
        ("with_preserve", "#![rustc_preserve_ub_checks]\n"),
    ):
        sub = work / label
        sub.mkdir()
        src = sub / "lib.rs"
        src.write_text(prefix + CHECKS_PROBE_SRC, encoding="utf-8")
        dumps = sub / "dumps"
        subprocess.run(
            [
                str(rustc),
                str(src),
                "--crate-type=rlib",
                "--edition=2024",
                f"--sysroot={sysroot}",
                f"--out-dir={sub}",
                "-Copt-level=3",
                "-Cdebug-assertions=no",
                "-Coverflow-checks=no",
                "-Zub-checks=no",
                "-Zcontract-checks=no",
                "-Zdump-mir=runtime-post-cleanup | runtime-optimized",
                f"-Zdump-mir-dir={dumps}",
            ],
            check=True,
            capture_output=True,
            text=True,
        )
        def read_fn_mir(fn_name: str, phase: str) -> str:
            matches = [
                p
                for p in sorted(dumps.glob(f"*.{fn_name}.*{phase}.after.mir"))
                if "{closure" not in p.name
            ]
            if len(matches) != 1:
                raise RuntimeError(f"expected 1 MIR dump for {fn_name} ({phase}), got {matches}")
            return matches[0].read_text(encoding="utf-8")

        ub_post = read_fn_mir("nonzero_like_ub_check", "runtime-post-cleanup")
        ub_opt = read_fn_mir("nonzero_like_ub_check", "runtime-optimized")
        ovf_post = read_fn_mir("inherited_add_u32", "runtime-post-cleanup")
        ovf_opt = read_fn_mir("inherited_add_u32", "runtime-optimized")
        req_post = read_fn_mir("contracted_req_only", "runtime-post-cleanup")
        ens_opt = read_fn_mir("contracted_inc", "runtime-optimized")

        checks[f"{label}_ub_in_postcleanup"] = "UbChecks" in ub_post
        checks[f"{label}_ub_in_optimized"] = "UbChecks" in ub_opt
        checks[f"{label}_inherit_ovf_assert_in_postcleanup"] = "AddWithOverflow" in ovf_post and "assert(" in ovf_post
        checks[f"{label}_inherit_ovf_assert_in_optimized"] = "AddWithOverflow" in ovf_opt and "assert(" in ovf_opt
        checks[f"{label}_contracts_closure_in_postcleanup"] = "contract_check_requires" in req_post
        checks[f"{label}_contracts_ensures_option_in_optimized"] = "Option::<{closure@" in ens_opt
    return checks


def probe_capture(capture_bin: Path, sysroot: Path, work: Path) -> dict[str, object]:
    """Run live `anneal-rustc-capture` checks when the driver binary is supplied."""
    nocore = work / "min_nocore.rs"
    nocore.write_text(
        "#![feature(no_core, lang_items)]\n#![no_core]\n"
        '#[lang = "pointee_sized"] pub trait PointeeSized {}\n'
        '#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}\n'
        '#[lang = "sized"] pub trait Sized: MetaSized {}\n'
        '#[lang = "copy"] pub trait Copy: Sized {}\n'
        "pub const fn id_u32(x: u32) -> u32 { x }\n",
        encoding="utf-8",
    )
    p_nc = subprocess.run(
        [
            str(capture_bin),
            "capture",
            f"--crate-root={nocore}",
            "--crate-name=min_nocore",
            "--edition=2024",
            "--target=x86_64-unknown-linux-gnu",
            f"--sysroot={sysroot}",
            f"--out-dir={work / 'nc_out'}",
            "--select=id_u32",
            f"--source-file={nocore}",
        ],
        capture_output=True,
        text=True,
    )
    nc_json = json.loads(p_nc.stdout)

    intr = work / "intrinsics_probe.rs"
    intr.write_text(INTRINSICS_PROBE_SRC, encoding="utf-8")
    ok_fns = [
        "i_wrapping_add",
        "i_add_with_overflow",
        "i_three_way_compare",
        "i_unreachable",
        "i_forget",
        "i_size_of",
        "i_align_of",
        "i_abort",
    ]
    p_ok = subprocess.run(
        [
            str(capture_bin),
            "capture",
            f"--crate-root={intr}",
            "--crate-name=intrinsics_probe",
            "--edition=2024",
            "--target=x86_64-unknown-linux-gnu",
            f"--sysroot={sysroot}",
            f"--out-dir={work / 'intr_ok'}",
            f"--source-file={intr}",
        ]
        + [f"--select={fn}" for fn in ok_fns],
        capture_output=True,
        text=True,
    )
    ok_json = json.loads(p_ok.stdout)
    return {
        "no_core_status": nc_json.get("status"),
        "no_core_diagnostics": nc_json.get("diagnostics"),
        "lowered_intrinsics_rc": p_ok.returncode,
        "lowered_intrinsics_status": ok_json.get("status"),
        "lowered_intrinsics_selected_count": ok_json.get("selected_count"),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rustc", type=Path, help="Path to nightly rustc binary")
    parser.add_argument("--sysroot", type=Path, help="Path to matching Rust sysroot")
    parser.add_argument("--rust-library", type=Path, help="Path to upstream Rust library/ directory")
    parser.add_argument("--anneal-rustc-capture", type=Path, help="Optional path to anneal-rustc-capture")
    args = parser.parse_args()

    summary: dict[str, object] = {}
    if args.rust_library:
        summary["census"] = scan_stdlib_census(args.rust_library)

    with tempfile.TemporaryDirectory(prefix="stdlib_mir_probe_") as tmp:
        work = Path(tmp)
        if args.rustc and args.sysroot:
            mir_checks = probe_mir_phases(args.rustc, args.sysroot, work)
            summary["mir_checks"] = mir_checks
            assert mir_checks["without_preserve_ub_in_postcleanup"] is True
            assert mir_checks["without_preserve_ub_in_optimized"] is False
            assert mir_checks["with_preserve_ub_in_postcleanup"] is True
            assert mir_checks["with_preserve_ub_in_optimized"] is True
            assert mir_checks["with_preserve_inherit_ovf_assert_in_optimized"] is True
            assert mir_checks["with_preserve_contracts_closure_in_postcleanup"] is True
        if args.anneal_rustc_capture and args.sysroot:
            cap = probe_capture(args.anneal_rustc_capture, args.sysroot, work)
            summary["capture_checks"] = cap
            assert cap["no_core_status"] == "unsupported"
            assert cap["lowered_intrinsics_rc"] == 0
            assert cap["lowered_intrinsics_status"] == "captured"
            assert cap["lowered_intrinsics_selected_count"] == 8

    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
