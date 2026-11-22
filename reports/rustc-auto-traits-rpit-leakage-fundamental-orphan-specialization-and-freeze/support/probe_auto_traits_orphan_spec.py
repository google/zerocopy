#!/usr/bin/env python3
"""Empirical rustc + readelf probe for auto-trait synthesis, RPIT leakage vs.
dyn Trait erasure, #[fundamental] orphan rules, min_specialization soundness
bans, #[marker] overlapping impls, negative impls with negative coherence, and
Freeze vs. UnsafeCell ELF section placement (.rodata A vs. .data WA).

Run standalone:
  python3 support/probe_auto_traits_orphan_spec.py --out support/probe_results.json
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
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def _find_rustc() -> str:
    env_rustc = os.environ.get("RUSTC")
    if env_rustc and shutil.which(env_rustc):
        return env_rustc
    direct = shutil.which("rustc")
    if direct:
        return direct
    cargo_rustc = Path.home() / ".cargo" / "bin" / "rustc"
    if cargo_rustc.is_file():
        return str(cargo_rustc)
    raise FileNotFoundError("rustc binary not found in PATH or ~/.cargo/bin/rustc")


def _find_readelf() -> str:
    for candidate in ("readelf", "llvm-readelf"):
        found = shutil.which(candidate)
        if found:
            return found
    raise FileNotFoundError("readelf (or llvm-readelf) not found in PATH")


def _scrub(text: str, tmp_dir: Path) -> str:
    """Remove host-specific temp paths and sysroot absolute paths."""
    out = text.replace(str(tmp_dir), "<WORKDIR>")
    home_str = str(Path.home())
    out = re.sub(r"/(?:[^\s/]+/)*\.rustup/toolchains/[^/\s]+", "<RUST_SYSROOT>", out)
    if home_str and home_str != "/":
        out = out.replace(home_str, "<USER_DIR>")
    out = re.sub(r"/rustc/[0-9a-f]{40}", "<RUSTC_SRC>", out)
    return out


def _extract_error_codes(stderr: str) -> list[str]:
    return sorted(set(re.findall(r"error\[(E\d{4})\]", stderr)))


def _run_compile_and_exec(
    rustc: str,
    tmp_dir: Path,
    stem: str,
    source: str,
    extra_args: list[str] | None = None,
    expect_run: bool = True,
) -> dict[str, Any]:
    src_path = tmp_dir / f"{stem}.rs"
    bin_path = tmp_dir / f"{stem}.bin"
    src_path.write_text(source, encoding="utf-8")

    cmd = [rustc, "--edition=2024", str(src_path), "-o", str(bin_path)]
    if extra_args:
        cmd.extend(extra_args)

    comp = subprocess.run(cmd, capture_output=True, text=True, check=False)
    stderr_clean = _scrub(comp.stderr.strip(), tmp_dir)
    stderr_head = "\n".join(stderr_clean.splitlines()[:20])
    result: dict[str, Any] = {
        "compile_rc": comp.returncode,
        "error_codes": _extract_error_codes(stderr_clean),
        "stderr_head": stderr_head,
    }
    if comp.returncode == 0 and expect_run:
        run = subprocess.run([str(bin_path)], capture_output=True, text=True, check=False)
        result["run_rc"] = run.returncode
        result["stdout"] = run.stdout.strip()
        if run.stderr.strip():
            result["run_stderr"] = _scrub(run.stderr.strip(), tmp_dir)
    return result


def _parse_readelf_sections(text: str) -> dict[str, dict[str, str]]:
    """Parse `readelf -S -W` section table indexed by section index string."""
    sections: dict[str, dict[str, str]] = {}
    # Match lines like: [ 3] .rodata.FROZEN_STAT PROGBITS 0000000000000000 000040 000004 00   A  0   0  4
    rx = re.compile(
        r"^\s*\[\s*(\d+)\]\s+(\S+)\s+(\S+)\s+[0-9a-fA-F]+\s+[0-9a-fA-F]+\s+([0-9a-fA-F]+)\s+[0-9a-fA-F]+\s+([A-Za-z]*)\s+\d+\s+\d+\s+(\d+)\s*$"
    )
    for line in text.splitlines():
        m = rx.match(line)
        if m:
            idx, name, stype, size_hex, flags, align = m.groups()
            sections[idx] = {
                "name": name,
                "type": stype,
                "size_bytes": str(int(size_hex, 16)),
                "flags": flags,
                "align": align,
            }
    return sections


def _parse_readelf_symbols(text: str, target_names: set[str]) -> dict[str, dict[str, str]]:
    """Parse `readelf -s -W` symbol table for requested symbol names."""
    found: dict[str, dict[str, str]] = {}
    # Num: Value Size Type Bind Vis Ndx Name
    rx = re.compile(
        r"^\s*\d+:\s+[0-9a-fA-F]+\s+(\d+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s*$"
    )
    for line in text.splitlines():
        m = rx.match(line)
        if m:
            size, sym_type, bind, vis, ndx, name = m.groups()
            if name in target_names:
                found[name] = {
                    "size": size,
                    "type": sym_type,
                    "bind": bind,
                    "vis": vis,
                    "ndx": ndx,
                }
    return found


def run_probe() -> dict[str, Any]:
    rustc = _find_rustc()
    readelf = _find_readelf()

    rustc_ver = subprocess.run([rustc, "-vV"], capture_output=True, text=True, check=True).stdout.strip()
    readelf_ver = subprocess.run([readelf, "--version"], capture_output=True, text=True, check=True).stdout.splitlines()[0].strip()

    with tempfile.TemporaryDirectory(prefix="probe_auto_traits_") as td:
        tmp = Path(td)

        # Build foreign upstream rlib crate for Part B (orphan rules) and negative-coherence checks.
        foreign_rs = tmp / "foreign_tr.rs"
        foreign_rlib = tmp / "libforeign_tr.rlib"
        foreign_rs.write_text(
            "pub trait ForeignTr { fn tag(&self) -> u32; }\n"
            "pub struct ForeignStruct(pub u32);\n",
            encoding="utf-8",
        )
        foreign_comp = subprocess.run(
            [rustc, "--edition=2024", "--crate-type=rlib", "--crate-name=foreign_tr", str(foreign_rs), "-o", str(foreign_rlib)],
            capture_output=True,
            text=True,
            check=True,
        )
        assert foreign_comp.returncode == 0
        extern_args = ["--extern", f"foreign_tr={foreign_rlib}"]

        # ------------------------------------------------------------------
        # Part A: RPIT Auto-Trait Leakage vs. dyn Trait Erasure (6 cases)
        # ------------------------------------------------------------------
        part_a = {
            "rpit_leaks_send_sync_unpin_for_u32": _run_compile_and_exec(
                rustc,
                tmp,
                "a1_rpit_u32",
                """
use std::fmt::Debug;
fn mk() -> impl Debug { 42u32 }
fn assert_all<T: Send + Sync + Unpin>(_: T) {}
fn main() {
    assert_all(mk());
    println!("RPIT_U32_LEAKS_ALL=ok");
}
""",
            ),
            "rpit_blocks_send_for_rc": _run_compile_and_exec(
                rustc,
                tmp,
                "a2_rpit_rc",
                """
use std::fmt::Debug;
use std::rc::Rc;
fn mk() -> impl Debug { Rc::new(42u32) }
fn assert_send<T: Send>(_: T) {}
fn main() { assert_send(mk()); }
""",
                expect_run=False,
            ),
            "rpit_send_not_sync_for_cell": _run_compile_and_exec(
                rustc,
                tmp,
                "a3_rpit_cell_send",
                """
use std::cell::Cell;
use std::fmt::Debug;
fn mk() -> impl Debug { Cell::new(42u32) }
fn assert_send<T: Send>(_: T) {}
fn main() {
    assert_send(mk());
    println!("RPIT_CELL_SEND=ok");
}
""",
            ),
            "rpit_blocks_sync_for_cell": _run_compile_and_exec(
                rustc,
                tmp,
                "a4_rpit_cell_sync",
                """
use std::cell::Cell;
use std::fmt::Debug;
fn mk() -> impl Debug { Cell::new(42u32) }
fn assert_sync<T: Sync>(_: T) {}
fn main() { assert_sync(mk()); }
""",
                expect_run=False,
            ),
            "rpit_blocks_unpin_for_phantom_pinned": _run_compile_and_exec(
                rustc,
                tmp,
                "a5_rpit_unpin",
                """
use std::fmt::Debug;
use std::marker::PhantomPinned;
fn mk() -> impl Debug { PhantomPinned }
fn assert_unpin<T: Unpin>(_: T) {}
fn main() { assert_unpin(mk()); }
""",
                expect_run=False,
            ),
            "dyn_trait_does_not_leak_send": _run_compile_and_exec(
                rustc,
                tmp,
                "a6_dyn_no_leak",
                """
use std::fmt::Debug;
fn mk() -> Box<dyn Debug> { Box::new(42u32) }
fn assert_send<T: Send>(_: T) {}
fn main() { assert_send(mk()); }
""",
                expect_run=False,
            ),
        }

        # ------------------------------------------------------------------
        # Part B: #[fundamental] Orphan Rules (4 cases)
        # ------------------------------------------------------------------
        part_b = {
            "fundamental_box_ref_pin_local_allowed": _run_compile_and_exec(
                rustc,
                tmp,
                "b1_fundamental_ok",
                """
use std::pin::Pin;
use foreign_tr::ForeignTr;

struct Local(u32);

impl ForeignTr for Box<Local> {
    fn tag(&self) -> u32 { self.0 + 10 }
}
impl ForeignTr for &Local {
    fn tag(&self) -> u32 { self.0 + 20 }
}
impl ForeignTr for &mut Local {
    fn tag(&self) -> u32 { self.0 + 30 }
}
impl ForeignTr for Pin<Box<Local>> {
    fn tag(&self) -> u32 { self.as_ref().get_ref().0 + 40 }
}

fn main() {
    let b = Box::new(Local(1));
    let mut loc = Local(2);
    let r: &Local = &loc;
    let r_tag = r.tag();
    let mr: &mut Local = &mut loc;
    let mr_tag = mr.tag();
    let p: Pin<Box<Local>> = Box::pin(Local(3));
    println!("FUND_OK={},{},{},{}", b.tag(), r_tag, mr_tag, p.tag());
}
""",
                extra_args=extern_args,
            ),
            "non_fundamental_vec_local_rejected_e0117": _run_compile_and_exec(
                rustc,
                tmp,
                "b2_vec_e0117",
                """
use foreign_tr::ForeignTr;
struct Local(u32);
impl ForeignTr for Vec<Local> { fn tag(&self) -> u32 { 0 } }
fn main() {}
""",
                extra_args=extern_args,
                expect_run=False,
            ),
            "non_fundamental_option_local_rejected_e0117": _run_compile_and_exec(
                rustc,
                tmp,
                "b3_option_e0117",
                """
use foreign_tr::ForeignTr;
struct Local(u32);
impl ForeignTr for Option<Local> { fn tag(&self) -> u32 { 0 } }
fn main() {}
""",
                extra_args=extern_args,
                expect_run=False,
            ),
            "fundamental_uncovered_generic_box_t_rejected_e0210": _run_compile_and_exec(
                rustc,
                tmp,
                "b4_uncovered_e0210",
                """
use foreign_tr::ForeignTr;
impl<T> ForeignTr for Box<T> { fn tag(&self) -> u32 { 0 } }
fn main() {}
""",
                extra_args=extern_args,
                expect_run=False,
            ),
        }

        # ------------------------------------------------------------------
        # Part C: min_specialization & #[marker] (5 cases)
        # ------------------------------------------------------------------
        part_c = {
            "min_spec_type_concrete_ok": _run_compile_and_exec(
                rustc,
                tmp,
                "c1_spec_concrete",
                """
#![feature(min_specialization)]
trait Tag { fn tag() -> &'static str; }
impl<T> Tag for T {
    default fn tag() -> &'static str { "generic" }
}
impl Tag for u32 {
    fn tag() -> &'static str { "u32" }
}
fn main() {
    println!("SPEC={},{}", <i32 as Tag>::tag(), <u32 as Tag>::tag());
}
""",
            ),
            "min_spec_lifetime_static_rejected_soundness": _run_compile_and_exec(
                rustc,
                tmp,
                "c2_spec_static_e0119",
                """
#![feature(min_specialization)]
trait BadSpec { fn is_static() -> bool; }
impl<T> BadSpec for T { default fn is_static() -> bool { false } }
impl<T: 'static> BadSpec for T { fn is_static() -> bool { true } }
fn main() {}
""",
                expect_run=False,
            ),
            "min_spec_equal_ref_lifetimes_rejected": _run_compile_and_exec(
                rustc,
                tmp,
                "c3_spec_eqlt_e0119",
                """
#![feature(min_specialization)]
trait SameLt { fn same() -> bool; }
impl<'a, 'b> SameLt for (&'a u8, &'b u8) { default fn same() -> bool { false } }
impl<'a> SameLt for (&'a u8, &'a u8) { fn same() -> bool { true } }
fn main() {}
""",
                expect_run=False,
            ),
            "marker_overlapping_blanket_impls_ok": _run_compile_and_exec(
                rustc,
                tmp,
                "c4_marker_overlap",
                """
#![feature(marker_trait_attr)]
#[marker]
trait MyMark {}
impl<T: Copy> MyMark for T {}
impl<T: Clone> MyMark for T {}
fn assert_mark<T: MyMark>(_: T) {}
fn main() {
    assert_mark(7u32);
    assert_mark(String::from("hi"));
    println!("MARKER_OVERLAP=ok");
}
""",
            ),
            "marker_with_assoc_item_rejected_e0714": _run_compile_and_exec(
                rustc,
                tmp,
                "c5_marker_e0714",
                """
#![feature(marker_trait_attr)]
#[marker]
trait BadMarker { const X: u32 = 1; }
fn main() {}
""",
                expect_run=False,
            ),
        }

        # ------------------------------------------------------------------
        # Part D: Negative Impls, with_negative_coherence, & Freeze ELF (3 cases)
        # ------------------------------------------------------------------
        # Build ELF object for Freeze vs UnsafeCell section placement.
        elf_src = tmp / "d3_freeze_elf.rs"
        elf_obj = tmp / "d3_freeze_elf.o"
        elf_src.write_text(
            """
#![crate_type = "lib"]
use std::cell::UnsafeCell;
use std::marker::PhantomData;

#[repr(transparent)]
pub struct SyncCell(UnsafeCell<u32>);
unsafe impl Sync for SyncCell {}

pub struct FrozenWithPhantom(pub u32, pub PhantomData<UnsafeCell<u32>>);
unsafe impl Sync for FrozenWithPhantom {}

#[unsafe(no_mangle)]
pub static FROZEN_STAT: u32 = 0x1234_5678;

#[unsafe(no_mangle)]
pub static UNFROZEN_STAT: SyncCell = SyncCell(UnsafeCell::new(0x1234_5678));

#[unsafe(no_mangle)]
pub static ZERO_UNFROZEN_STAT: SyncCell = SyncCell(UnsafeCell::new(0));

#[unsafe(no_mangle)]
pub static PHANTOM_FREEZE_STAT: FrozenWithPhantom = FrozenWithPhantom(0x55aa_1234, PhantomData);
""",
            encoding="utf-8",
        )
        elf_comp = subprocess.run(
            [
                rustc,
                "--edition=2024",
                "--crate-type=lib",
                "--emit=obj",
                "-C",
                "opt-level=2",
                str(elf_src),
                "-o",
                str(elf_obj),
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        elf_result: dict[str, Any] = {
            "compile_rc": elf_comp.returncode,
            "stderr_head": _scrub(elf_comp.stderr.strip(), tmp),
            "symbols": {},
        }
        if elf_comp.returncode == 0:
            sec_out = subprocess.run([readelf, "-S", "-W", str(elf_obj)], capture_output=True, text=True, check=True).stdout
            sym_out = subprocess.run([readelf, "-s", "-W", str(elf_obj)], capture_output=True, text=True, check=True).stdout
            sections = _parse_readelf_sections(sec_out)
            syms = _parse_readelf_symbols(sym_out, {"FROZEN_STAT", "UNFROZEN_STAT", "ZERO_UNFROZEN_STAT", "PHANTOM_FREEZE_STAT"})
            for name, sinfo in sorted(syms.items()):
                sec = sections.get(sinfo["ndx"], {})
                elf_result["symbols"][name] = {
                    "ndx": sinfo["ndx"],
                    "size": sinfo["size"],
                    "bind": sinfo["bind"],
                    "section": {
                        "name": sec.get("name", ""),
                        "type": sec.get("type", ""),
                        "flags": sec.get("flags", ""),
                    },
                }

        part_d = {
            "negative_impl_blocks_send": _run_compile_and_exec(
                rustc,
                tmp,
                "d1_neg_send",
                """
#![feature(negative_impls)]
struct NoSend(u32);
impl !Send for NoSend {}
fn assert_send<T: Send>(_: T) {}
fn main() { assert_send(NoSend(1)); }
""",
                expect_run=False,
            ),
            "with_negative_coherence_disjoint_impls_ok": _run_compile_and_exec(
                rustc,
                tmp,
                "d2_neg_coh",
                """
#![feature(negative_impls, with_negative_coherence)]
trait Classify { fn id() -> u32; }
struct NoSend(u32);
impl !Send for NoSend {}
impl<T: Send> Classify for T { fn id() -> u32 { 1 } }
impl Classify for NoSend { fn id() -> u32 { 2 } }
fn main() {
    let _ = NoSend(0).0;
    println!("NEG_COH={},{}", <u32 as Classify>::id(), <NoSend as Classify>::id());
}
""",
            ),
            "freeze_vs_unsafe_cell_elf_sections": elf_result,
        }

        # ------------------------------------------------------------------
        # Supplementary discriminators: Layer-2 min_specialization,
        # OverlapMode::Stable vs WithNegative on foreign Rc<T>,
        # and RPIT Freeze leakage under #![feature(freeze)].
        # ------------------------------------------------------------------
        supplementary = {
            "layer2_min_spec_static_ref_rejected": _run_compile_and_exec(
                rustc,
                tmp,
                "s1_spec_static_ref",
                """
#![feature(min_specialization)]
trait Tr { fn f() -> u32; }
impl<T> Tr for T { default fn f() -> u32 { 0 } }
impl Tr for &'static u8 { fn f() -> u32 { 1 } }
fn main() {}
""",
                expect_run=False,
            ),
            "layer2_min_spec_duplicate_param_rejected": _run_compile_and_exec(
                rustc,
                tmp,
                "s2_spec_dup_param",
                """
#![feature(min_specialization)]
trait Tr { fn f() -> u32; }
impl<T> Tr for T { default fn f() -> u32 { 0 } }
impl<T> Tr for (T, T) { fn f() -> u32 { 1 } }
fn main() {}
""",
                expect_run=False,
            ),
            "layer2_min_spec_non_spec_trait_bound_rejected": _run_compile_and_exec(
                rustc,
                tmp,
                "s3_spec_trait_bound",
                """
#![feature(min_specialization)]
trait Tr { fn f() -> u32; }
impl<T> Tr for T { default fn f() -> u32 { 0 } }
impl<T: Clone> Tr for T { fn f() -> u32 { 1 } }
fn main() {}
""",
                expect_run=False,
            ),
            "foreign_rc_disjoint_without_negative_coherence_rejected_e0119": _run_compile_and_exec(
                rustc,
                tmp,
                "s4_rc_no_neg_coh",
                """
use std::rc::Rc;
trait Classify { fn id() -> u32; }
impl<T: Send> Classify for T { fn id() -> u32 { 1 } }
impl<T> Classify for Rc<T> { fn id() -> u32 { 2 } }
fn main() {}
""",
                expect_run=False,
            ),
            "foreign_rc_disjoint_with_negative_coherence_ok": _run_compile_and_exec(
                rustc,
                tmp,
                "s5_rc_with_neg_coh",
                """
#![feature(with_negative_coherence)]
use std::rc::Rc;
trait Classify { fn id() -> u32; }
impl<T: Send> Classify for T { fn id() -> u32 { 1 } }
impl<T> Classify for Rc<T> { fn id() -> u32 { 2 } }
fn main() {
    println!("RC_NEG_COH={},{}", <u32 as Classify>::id(), <Rc<u32> as Classify>::id());
}
""",
            ),
            "rpit_leaks_freeze_for_u32_blocks_for_cell": {
                "u32_freeze_ok": _run_compile_and_exec(
                    rustc,
                    tmp,
                    "s6a_rpit_freeze_u32",
                    """
#![feature(freeze)]
use std::fmt::Debug;
use std::marker::Freeze;
fn mk() -> impl Debug { 42u32 }
fn assert_freeze<T: Freeze>(_: T) {}
fn main() {
    assert_freeze(mk());
    println!("RPIT_FREEZE_U32=ok");
}
""",
                ),
                "cell_freeze_rejected": _run_compile_and_exec(
                    rustc,
                    tmp,
                    "s6b_rpit_freeze_cell",
                    """
#![feature(freeze)]
use std::cell::Cell;
use std::fmt::Debug;
use std::marker::Freeze;
fn mk() -> impl Debug { Cell::new(42u32) }
fn assert_freeze<T: Freeze>(_: T) {}
fn main() { assert_freeze(mk()); }
""",
                    expect_run=False,
                ),
            },
            "auto_trait_orphan_rejects_box_local_e0321": _run_compile_and_exec(
                rustc,
                tmp,
                "s7_auto_orphan_box_local",
                """
struct Local(u32);
unsafe impl Send for Box<Local> {}
fn main() {}
""",
                expect_run=False,
            ),
            "negative_auto_trait_cannot_be_specialized_e0366": _run_compile_and_exec(
                rustc,
                tmp,
                "s8_neg_auto_e0366",
                """
#![feature(negative_impls)]
struct Wrapper<T>(T);
impl !Send for Wrapper<u32> {}
fn main() {}
""",
                expect_run=False,
            ),
        }

    return {
        "schema_version": 1,
        "timestamp_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "rustc_version": rustc_ver,
        "readelf_version": readelf_ver,
        "core_case_count": (
            len(part_a) + len(part_b) + len(part_c) + len(part_d)
        ),
        "part_a_rpit_auto_trait_leakage": part_a,
        "part_b_fundamental_orphan_rules": part_b,
        "part_c_min_specialization_and_marker": part_c,
        "part_d_negative_impls_and_freeze_rodata_shift": part_d,
        "supplementary_discriminators": supplementary,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=None, help="Write JSON output to file")
    args = parser.parse_args(argv)

    data = run_probe()
    rendered = json.dumps(data, indent=2, ensure_ascii=True) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered, encoding="utf-8")
        print(f"wrote {args.out} ({len(rendered)} bytes, {data['core_case_count']} core cases)")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
