#!/usr/bin/env python3
"""Cross-version empirical rustc_public compilation & execution stability matrix across installed rustup toolchains."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import tempfile
from pathlib import Path

COMPAT_SRC = r"""#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
#[macro_use]
extern crate rustc_public;

use std::ops::ControlFlow;
use rustc_public::mir::{Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{AdtKind, ConstantKind, RigidTy, TyKind};

fn analyze() -> ControlFlow<(), ()> {
    let krate = rustc_public::local_crate();
    let exts = rustc_public::external_crates();
    let items = rustc_public::all_local_items();
    let mut pm = 0usize;
    let mut uses = 0usize;
    let mut adts = 0usize;
    for item in &items {
        if let Some(body) = item.body() {
            for bb in &body.blocks {
                for st in &bb.statements {
                    if matches!(st.kind, StatementKind::PlaceMention(_)) {
                        pm += 1;
                    }
                    if matches!(st.kind, StatementKind::Assign(_, Rvalue::Use(_, _))) {
                        uses += 1;
                    }
                }
                if let TerminatorKind::Call { .. } = &bb.terminator.kind {}
            }
            for (_, decl) in body.local_decls() {
                let _ = decl.ty.layout();
                if let TyKind::RigidTy(RigidTy::Adt(adt, _)) = decl.ty.kind() {
                    adts += 1;
                    let _ = adt.repr();
                    let _ = adt.kind() == AdtKind::Enum;
                    let _ = adt.num_variants();
                }
            }
        }
    }
    println!(
        "COMPAT_OK krate={} ext={} items={} pm={} uses={} adts={}",
        krate.name, exts.len(), items.len(), pm, uses, adts
    );
    let _ = std::any::type_name::<ConstantKind>();
    ControlFlow::Break(())
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let _ = rustc_public::run!(&args, analyze);
}
"""

PIN_SURFACE_SRC = r"""#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
#[macro_use]
extern crate rustc_public;

use std::ops::ControlFlow;
use rustc_public::abi::LayoutShape;
use rustc_public::mir::{Rvalue, Statement, WithRetag};
use rustc_public::rustc_internal;

fn probe_pin_surface() -> ControlFlow<(), ()> {
    for item in rustc_public::all_local_items() {
        if let Some(body) = item.body() {
            for bb in &body.blocks {
                let _ = &bb.terminator.span;
                for st in &bb.statements {
                    let st_ref: &Statement = st;
                    let _ = st_ref.span;
                    if let rustc_public::mir::StatementKind::Assign(_, Rvalue::Use(_, WithRetag::Yes)) = &st.kind {}
                }
            }
            for (_, decl) in body.local_decls() {
                if let Ok(lay) = decl.ty.layout() {
                    let shape: LayoutShape = lay.shape();
                    let _ = &shape.abi;
                }
            }
        }
    }
    let _ = rustc_internal::run::<fn(), ()>;
    let _ = rustc_driver::run_compiler as *const ();
    println!("PIN_SURFACE_OK");
    ControlFlow::Break(())
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let _ = rustc_public::run!(&args, probe_pin_surface);
}
"""

TARGET_SRC = r"""#![crate_type = "lib"]
#[repr(C)]
pub struct Pair { pub a: u8, pub b: u32 }
pub fn add_pair(p: Pair) -> u32 { (p.a as u32) + p.b }
"""


def discover_toolchains() -> list[str]:
    out = subprocess.check_output(["rustup", "toolchain", "list"], text=True)
    res = []
    for line in out.splitlines():
        tc = line.split()[0]
        proc = subprocess.run(["rustup", "run", tc, "rustc", "--print", "sysroot"], capture_output=True, text=True)
        if proc.returncode != 0:
            continue
        sysroot = proc.stdout.strip()
        if any(Path(sysroot).glob("lib/rustlib/*/lib/librustc_public*")):
            res.append(tc)
    return res


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--toolchains", nargs="*", help="Toolchains to probe (default: all installed with librustc_public)")
    parser.add_argument("--out", type=Path, help="Optional JSON output file")
    args = parser.parse_args()

    toolchains = args.toolchains or discover_toolchains()
    results = []
    with tempfile.TemporaryDirectory() as tmp:
        tmp_dir = Path(tmp)
        compat_rs = tmp_dir / "matrix_compat.rs"
        pin_rs = tmp_dir / "matrix_pin_surface.rs"
        target_rs = tmp_dir / "matrix_target.rs"
        compat_rs.write_text(COMPAT_SRC)
        pin_rs.write_text(PIN_SURFACE_SRC)
        target_rs.write_text(TARGET_SRC)

        for tc in toolchains:
            ver = subprocess.check_output(["rustup", "run", tc, "rustc", "--version"], text=True).strip()
            sysroot = subprocess.check_output(["rustup", "run", tc, "rustc", "--print", "sysroot"], text=True).strip()
            host_triple = sysroot.rsplit("-", 3)[-3:]  # informative only
            is_stable_channel = "nightly" not in tc
            variants = [("compat", compat_rs, False), ("pin_surface", pin_rs, False)]
            if is_stable_channel:
                variants.extend([("compat_bootstrap", compat_rs, True), ("pin_surface_bootstrap", pin_rs, True)])

            tc_rec = {"toolchain": tc, "version": ver, "probes": {}}
            for label, src, bootstrap in variants:
                bin_path = tmp_dir / f"probe_{tc.replace('.', '_').replace('-', '_')}_{label}"
                env = os.environ.copy()
                if bootstrap:
                    env["RUSTC_BOOTSTRAP"] = "1"
                else:
                    env.pop("RUSTC_BOOTSTRAP", None)
                lib_rlib = str(next(Path(sysroot).glob("lib/rustlib/*/lib")))
                proc = subprocess.run(
                    [
                        "rustup", "run", tc, "rustc", "--edition", "2024",
                        "-L", f"native={sysroot}/lib",
                        "-C", f"link-arg=-Wl,-rpath,{sysroot}/lib:{lib_rlib}",
                        "-o", str(bin_path), str(src),
                    ],
                    env=env, capture_output=True, text=True,
                )
                entry = {
                    "compile_rc": proc.returncode,
                    "bootstrap": bootstrap,
                    "compile_err_head": "\n".join(proc.stderr.splitlines()[:15]) if proc.returncode != 0 else "",
                }
                if proc.returncode == 0:
                    run_proc = subprocess.run(
                        [str(bin_path), "matrix_probe", "--edition", "2024", "--sysroot", sysroot, str(target_rs)],
                        capture_output=True, text=True,
                    )
                    entry["run_rc"] = run_proc.returncode
                    entry["run_stdout"] = run_proc.stdout.strip()
                tc_rec["probes"][label] = entry
            results.append(tc_rec)

    payload = json.dumps(results, indent=2)
    if args.out:
        args.out.write_text(payload + "\n")
    print(payload)


if __name__ == "__main__":
    main()
