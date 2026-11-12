#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Reproducible probe suite for foreign MIR availability, inlining, and intrinsic lowering."""

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path


INSPECTOR_RS = r'''#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_interface::interface::Compiler;
use rustc_middle::mir::{
    Body, NonDivergingIntrinsic, Operand, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::ty::{Instance, InstanceKind, TyCtxt, TypeVisitableExt, TypingEnv};
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::panic::{catch_unwind, AssertUnwindSafe};

struct MirSummary {
    phase: String,
    basic_blocks: usize,
    statements: usize,
    storage_markers: usize,
    ub_checks: usize,
    overflow_checks: usize,
    bin_ops: BTreeSet<String>,
    un_ops: BTreeSet<String>,
    cast_kinds: BTreeSet<String>,
    non_diverging_intrinsics: BTreeSet<String>,
    calls: Vec<CallEdge>,
    has_unreachable_term: bool,
    has_assert_term: bool,
    local_info_cleared: bool,
}

#[derive(Clone)]
struct CallEdge {
    def_id: Option<DefId>,
    path: String,
    resolved_def_id: Option<DefId>,
    resolved_instance_kind: Option<String>,
    resolved_path: Option<String>,
    is_intrinsic: bool,
    intrinsic_name: Option<String>,
    intrinsic_must_be_overridden: Option<bool>,
}

fn summarize_body<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> MirSummary {
    let mut statements = 0usize;
    let mut storage_markers = 0usize;
    let mut ub_checks = 0usize;
    let mut overflow_checks = 0usize;
    let mut bin_ops = BTreeSet::new();
    let mut un_ops = BTreeSet::new();
    let mut cast_kinds = BTreeSet::new();
    let mut non_diverging_intrinsics = BTreeSet::new();
    let mut calls = Vec::new();
    let mut has_unreachable_term = false;
    let mut has_assert_term = false;

    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            statements += 1;
            match &stmt.kind {
                StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => {
                    storage_markers += 1;
                }
                StatementKind::Intrinsic(intr) => match &**intr {
                    NonDivergingIntrinsic::Assume(_) => {
                        non_diverging_intrinsics.insert("Assume".to_string());
                    }
                    NonDivergingIntrinsic::CopyNonOverlapping(_) => {
                        non_diverging_intrinsics.insert("CopyNonOverlapping".to_string());
                    }
                },
                StatementKind::Assign(assign) => {
                    let (_, rval) = &**assign;
                    match rval {
                        Rvalue::BinaryOp(op, _) => {
                            bin_ops.insert(format!("{:?}", op));
                        }
                        Rvalue::UnaryOp(op, _) => {
                            un_ops.insert(format!("{:?}", op));
                        }
                        Rvalue::Cast(kind, _, _) => {
                            cast_kinds.insert(format!("{:?}", kind));
                        }
                        Rvalue::Use(Operand::RuntimeChecks(rc), _) => {
                            let s = format!("{:?}", rc);
                            if s.contains("UbChecks") {
                                ub_checks += 1;
                            } else if s.contains("OverflowChecks") {
                                overflow_checks += 1;
                            }
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        if let Some(term) = &bb.terminator {
            match &term.kind {
                TerminatorKind::Call { func, .. } => {
                    if let Operand::Constant(c) = func {
                        if let rustc_middle::ty::TyKind::FnDef(callee_did, args) = c.const_.ty().kind() {
                            let intr = tcx.intrinsic(*callee_did);
                            let mut resolved_def_id = None;
                            let mut resolved_instance_kind = None;
                            let mut resolved_path = None;
                            if !args.has_non_region_param() {
                                if let Some(erased_args) = tcx.erase_and_anonymize_regions(*args).no_bound_vars() {
                                    if let Ok(Some(inst)) = Instance::try_resolve(tcx, TypingEnv::fully_monomorphized(), *callee_did, erased_args) {
                                        resolved_def_id = Some(inst.def_id());
                                        resolved_instance_kind = Some(match inst.def {
                                            InstanceKind::Item(_) => "Item".to_string(),
                                            InstanceKind::Intrinsic(_) => "Intrinsic".to_string(),
                                            InstanceKind::Virtual(_, _) => "Virtual".to_string(),
                                            _ => "Other".to_string(),
                                        });
                                        resolved_path = Some(tcx.def_path_str(inst.def_id()));
                                    }
                                }
                            }
                            calls.push(CallEdge {
                                def_id: Some(*callee_did),
                                path: tcx.def_path_str(*callee_did),
                                resolved_def_id,
                                resolved_instance_kind,
                                resolved_path,
                                is_intrinsic: intr.is_some(),
                                intrinsic_name: intr.map(|i| i.name.as_str().to_string()),
                                intrinsic_must_be_overridden: intr.map(|i| i.must_be_overridden),
                            });
                        }
                    }
                }
                TerminatorKind::Unreachable => {
                    has_unreachable_term = true;
                }
                TerminatorKind::Assert { .. } => {
                    has_assert_term = true;
                }
                _ => {}
            }
        }
    }

    let local_info_cleared = body
        .local_decls
        .iter()
        .all(|d| matches!(d.local_info, rustc_middle::mir::ClearCrossCrate::Clear));

    MirSummary {
        phase: format!("{:?}", body.phase),
        basic_blocks: body.basic_blocks.len(),
        statements,
        storage_markers,
        ub_checks,
        overflow_checks,
        bin_ops,
        un_ops,
        cast_kinds,
        non_diverging_intrinsics,
        calls,
        has_unreachable_term,
        has_assert_term,
        local_info_cleared,
    }
}

fn summary_to_json(s: &MirSummary) -> String {
    let bin_ops: Vec<String> = s.bin_ops.iter().map(|x| format!("{:?}", x)).collect();
    let un_ops: Vec<String> = s.un_ops.iter().map(|x| format!("{:?}", x)).collect();
    let cast_kinds: Vec<String> = s.cast_kinds.iter().map(|x| format!("{:?}", x)).collect();
    let ndi: Vec<String> = s.non_diverging_intrinsics.iter().map(|x| format!("{:?}", x)).collect();
    let calls: Vec<String> = s
        .calls
        .iter()
        .map(|c| {
            format!(
                "{{\"path\":{:?},\"resolved_kind\":{},\"resolved_path\":{},\"is_intrinsic\":{},\"intrinsic_name\":{},\"must_be_overridden\":{}}}",
                c.path,
                match &c.resolved_instance_kind {
                    Some(k) => format!("{:?}", k),
                    None => "null".to_string(),
                },
                match &c.resolved_path {
                    Some(p) => format!("{:?}", p),
                    None => "null".to_string(),
                },
                c.is_intrinsic,
                match &c.intrinsic_name {
                    Some(n) => format!("{:?}", n),
                    None => "null".to_string(),
                },
                match c.intrinsic_must_be_overridden {
                    Some(b) => format!("{}", b),
                    None => "null".to_string(),
                }
            )
        })
        .collect();
    format!(
        "{{\"phase\":{:?},\"basic_blocks\":{},\"statements\":{},\"storage_markers\":{},\"ub_checks\":{},\"overflow_checks\":{},\"local_info_cleared\":{},\"has_unreachable_term\":{},\"has_assert_term\":{},\"bin_ops\":[{}],\"un_ops\":[{}],\"cast_kinds\":[{}],\"non_diverging_intrinsics\":[{}],\"calls\":[{}]}}",
        s.phase,
        s.basic_blocks,
        s.statements,
        s.storage_markers,
        s.ub_checks,
        s.overflow_checks,
        s.local_info_cleared,
        s.has_unreachable_term,
        s.has_assert_term,
        bin_ops.join(","),
        un_ops.join(","),
        cast_kinds.join(","),
        ndi.join(","),
        calls.join(",")
    )
}

struct InspectorCallbacks;

impl Callbacks for InspectorCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let mode = std::env::var("PROBE_MODE").unwrap_or_else(|_| "core_suite".to_string());
        if mode == "core_suite" {
            let mut local_entries = Vec::new();
            let mut foreign_dids = BTreeMap::<String, DefId>::new();

            for local_did in tcx.hir_body_owners() {
                let def_id = local_did.to_def_id();
                if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
                    continue;
                }
                let name = tcx.def_path_str(def_id);
                let post_summary = {
                    let post_body = tcx.mir_drops_elaborated_and_const_checked(local_did).borrow();
                    summarize_body(tcx, &post_body)
                };
                for c in &post_summary.calls {
                    if let Some(cdid) = c.def_id {
                        if cdid.krate != LOCAL_CRATE {
                            foreign_dids.insert(tcx.def_path_str(cdid), cdid);
                        }
                    }
                    if let Some(rdid) = c.resolved_def_id {
                        if rdid.krate != LOCAL_CRATE {
                            foreign_dids.insert(tcx.def_path_str(rdid), rdid);
                        }
                    }
                }
                let opt_body = tcx.optimized_mir(def_id);
                let opt_summary = summarize_body(tcx, opt_body);
                for c in &opt_summary.calls {
                    if let Some(cdid) = c.def_id {
                        if cdid.krate != LOCAL_CRATE {
                            foreign_dids.insert(tcx.def_path_str(cdid), cdid);
                        }
                    }
                    if let Some(rdid) = c.resolved_def_id {
                        if rdid.krate != LOCAL_CRATE {
                            foreign_dids.insert(tcx.def_path_str(rdid), rdid);
                        }
                    }
                }
                local_entries.push(format!(
                    "{{\"fn_name\":{:?},\"postcleanup\":{},\"optimized\":{}}}",
                    name,
                    summary_to_json(&post_summary),
                    summary_to_json(&opt_summary)
                ));
            }

            // Transitively expand foreign callees up to depth 3
            let mut queue: Vec<DefId> = foreign_dids.values().copied().collect();
            let mut visited: HashSet<DefId> = queue.iter().copied().collect();
            let mut depth = 0;
            while !queue.is_empty() && depth < 3 {
                let mut next_queue = Vec::new();
                for fdid in queue {
                    if tcx.is_mir_available(fdid) {
                        let body = tcx.optimized_mir(fdid);
                        let sum = summarize_body(tcx, body);
                        for c in &sum.calls {
                            if let Some(cdid) = c.def_id {
                                if cdid.krate != LOCAL_CRATE && visited.insert(cdid) {
                                    foreign_dids.insert(tcx.def_path_str(cdid), cdid);
                                    next_queue.push(cdid);
                                }
                            }
                        }
                    }
                }
                queue = next_queue;
                depth += 1;
            }

            let mut foreign_entries = Vec::new();
            for (path, fdid) in &foreign_dids {
                let is_mir = tcx.is_mir_available(*fdid);
                let is_const = tcx.is_const_fn(*fdid);
                let cross_inline = tcx.cross_crate_inlinable(*fdid);
                let intr_def = tcx.intrinsic(*fdid);
                let intr = intr_def.map(|i| i.name.as_str().to_string());
                let must_override = intr_def.map(|i| i.must_be_overridden);
                let inline_attr = format!("{:?}", tcx.codegen_fn_attrs(*fdid).inline);

                let opt_json = if is_mir {
                    let body = tcx.instance_mir(InstanceKind::Item(*fdid));
                    summary_to_json(&summarize_body(tcx, body))
                } else {
                    "null".to_string()
                };
                let ctfe_json = if is_const && intr.is_none() {
                    match catch_unwind(AssertUnwindSafe(|| {
                        let body = tcx.mir_for_ctfe(*fdid);
                        summary_to_json(&summarize_body(tcx, body))
                    })) {
                        Ok(s) => s,
                        Err(_) => "null".to_string(),
                    }
                } else {
                    "null".to_string()
                };

                foreign_entries.push(format!(
                    "{{\"path\":{:?},\"crate_name\":{:?},\"is_mir_available\":{},\"is_const_fn\":{},\"cross_crate_inlinable\":{},\"intrinsic\":{},\"must_be_overridden\":{},\"inline_attr\":{:?},\"instance_mir\":{},\"mir_for_ctfe\":{}}}",
                    path,
                    tcx.crate_name(fdid.krate).as_str(),
                    is_mir,
                    is_const,
                    cross_inline,
                    match intr {
                        Some(n) => format!("{:?}", n),
                        None => "null".to_string(),
                    },
                    match must_override {
                        Some(b) => format!("{}", b),
                        None => "null".to_string(),
                    },
                    inline_attr,
                    opt_json,
                    ctfe_json
                ));
            }

            println!(
                "PROBE_JSON:{{\"local_functions\":[{}],\"foreign_callees\":[{}]}}",
                local_entries.join(","),
                foreign_entries.join(",")
            );
        } else if mode == "ext_matrix" {
            let mut ext_entries = Vec::new();
            let mut foreign_dids = Vec::new();
            for local_did in tcx.hir_body_owners() {
                let post_body = tcx.mir_drops_elaborated_and_const_checked(local_did).borrow();
                let post_summary = summarize_body(tcx, &post_body);
                for c in &post_summary.calls {
                    if let Some(cdid) = c.def_id {
                        if cdid.krate != LOCAL_CRATE && tcx.crate_name(cdid.krate).as_str() == "ext_lib" {
                            foreign_dids.push(cdid);
                        }
                    }
                }
            }
            foreign_dids.sort_by_key(|d| tcx.def_path_str(*d));
            foreign_dids.dedup();

            for fdid in foreign_dids {
                let path = tcx.def_path_str(fdid);
                let is_mir = tcx.is_mir_available(fdid);
                let is_const = tcx.is_const_fn(fdid);
                let cross_inline = tcx.cross_crate_inlinable(fdid);
                let req_mono = tcx.generics_of(fdid).requires_monomorphization(tcx);

                let instance_mir_ok = catch_unwind(AssertUnwindSafe(|| {
                    let b = tcx.instance_mir(InstanceKind::Item(fdid));
                    b.basic_blocks.len()
                }))
                .is_ok();

                let mir_for_ctfe_ok = catch_unwind(AssertUnwindSafe(|| {
                    let b = tcx.mir_for_ctfe(fdid);
                    b.basic_blocks.len()
                }))
                .is_ok();

                ext_entries.push(format!(
                    "{{\"path\":{:?},\"is_mir_available\":{},\"is_const_fn\":{},\"cross_crate_inlinable\":{},\"requires_monomorphization\":{},\"instance_mir_ok\":{},\"mir_for_ctfe_ok\":{}}}",
                    path, is_mir, is_const, cross_inline, req_mono, instance_mir_ok, mir_for_ctfe_ok
                ));
            }
            println!("PROBE_JSON:{{\"ext_items\":[{}]}}", ext_entries.join(","));
        }
        Compilation::Stop
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut callbacks = InspectorCallbacks;
    rustc_driver::compiler_entrypoint(&args, &mut callbacks);
}
'''

CORE_SUITE_RS = r'''#![no_std]
#![allow(dead_code)]

pub fn call_from_be(x: u64) -> u64 { u64::from_be(x) }
pub fn call_to_be(x: u64) -> u64 { x.to_be() }
pub fn call_swap_bytes(x: u64) -> u64 { x.swap_bytes() }
pub fn call_overflowing_add(a: u64, b: u64) -> (u64, bool) { a.overflowing_add(b) }
pub fn call_overflowing_sub(a: u64, b: u64) -> (u64, bool) { a.overflowing_sub(b) }
pub fn call_overflowing_mul(a: u64, b: u64) -> (u64, bool) { a.overflowing_mul(b) }
pub fn call_wrapping_add(a: u64, b: u64) -> u64 { a.wrapping_add(b) }
pub fn call_wrapping_sub(a: u64, b: u64) -> u64 { a.wrapping_sub(b) }
pub fn call_wrapping_mul(a: u64, b: u64) -> u64 { a.wrapping_mul(b) }
pub fn call_wrapping_shl(a: u64, b: u32) -> u64 { a.wrapping_shl(b) }
pub fn call_wrapping_shr(a: u64, b: u32) -> u64 { a.wrapping_shr(b) }
pub fn call_checked_add(a: u64, b: u64) -> Option<u64> { a.checked_add(b) }
pub fn call_checked_sub(a: u64, b: u64) -> Option<u64> { a.checked_sub(b) }
pub fn call_checked_mul(a: u64, b: u64) -> Option<u64> { a.checked_mul(b) }
pub fn call_saturating_add(a: u64, b: u64) -> u64 { a.saturating_add(b) }
pub fn call_saturating_sub(a: u64, b: u64) -> u64 { a.saturating_sub(b) }
pub fn call_unchecked_add(a: u64, b: u64) -> u64 { unsafe { a.unchecked_add(b) } }
pub fn call_leading_zeros(x: u64) -> u32 { x.leading_zeros() }
pub fn call_trailing_zeros(x: u64) -> u32 { x.trailing_zeros() }
pub fn call_count_ones(x: u64) -> u32 { x.count_ones() }
pub fn call_rotate_left(x: u64, n: u32) -> u64 { x.rotate_left(n) }
pub fn call_option_is_some(x: Option<u64>) -> bool { x.is_some() }
pub fn call_option_is_none(x: Option<u64>) -> bool { x.is_none() }
pub fn call_option_unwrap_or(x: Option<u64>, d: u64) -> u64 { x.unwrap_or(d) }
pub fn call_cmp_min(a: u64, b: u64) -> u64 { core::cmp::min(a, b) }
pub fn call_cmp_max(a: u64, b: u64) -> u64 { core::cmp::max(a, b) }
pub fn call_partial_eq(a: &u64, b: &u64) -> bool { a == b }
pub fn call_slice_len(s: &[u8]) -> usize { s.len() }
'''

EXT_LIB_RS = r'''#![no_std]

#[inline(never)]
pub fn helper_non_inlined(x: u64) -> u64 {
    x ^ 0x5555_5555_5555_5555
}

// 1. Plain non-generic function with a non-intrinsic call (calls > 0 => not small-leaf cross_crate_inlinable)
pub fn plain_non_generic(x: u64) -> u64 {
    helper_non_inlined(x).wrapping_add(1)
}

// 2. Small leaf non-generic function without #[inline] (0 non-intrinsic calls, <= 100 statements)
pub fn small_leaf_non_generic(x: u64) -> u64 {
    x + 1
}

// 3. #[inline] non-generic function
#[inline]
pub fn inline_non_generic(x: u64) -> u64 {
    helper_non_inlined(x) + 2
}

pub const fn const_helper(x: u64) -> u64 {
    x ^ 0xaaaa_aaaa_aaaa_aaaa
}

// 4. pub const fn without #[inline] that calls another const fn (so calls > 0 => cross_crate_inlinable is false at opt-level=0)
pub const fn const_non_inlined(x: u64) -> u64 {
    const_helper(x) + 3
}

// 5. #[inline] pub const fn
#[inline]
pub const fn const_inlined(x: u64) -> u64 {
    const_helper(x) + 4
}

// 6. Generic function (requires_monomorphization == true, even without #[inline])
pub fn generic_fn<T: Copy>(x: T) -> T {
    x
}
'''

EXT_CALLER_RS = r'''#![no_std]
extern crate ext_lib;

pub fn exercise_all(x: u64) -> u64 {
    let a = ext_lib::plain_non_generic(x);
    let b = ext_lib::small_leaf_non_generic(a);
    let c = ext_lib::inline_non_generic(b);
    let d = ext_lib::const_non_inlined(c);
    let e = ext_lib::const_inlined(d);
    ext_lib::generic_fn(e)
}
'''


def get_toolchain_env():
    sysroot = subprocess.check_output(["rustc", "--print", "sysroot"], text=True).strip()
    env = os.environ.copy()
    lib_dir = os.path.join(sysroot, "lib")
    existing = env.get("LD_LIBRARY_PATH", "")
    env["LD_LIBRARY_PATH"] = f"{lib_dir}:{existing}" if existing else lib_dir
    return env, sysroot


def extract_probe_json(stdout: str):
    for line in stdout.splitlines():
        if line.startswith("PROBE_JSON:"):
            return json.loads(line[len("PROBE_JSON:"):])
    raise RuntimeError(f"No PROBE_JSON found in output:\n{stdout}")


def main():
    env, sysroot = get_toolchain_env()
    rustc_v = subprocess.check_output(["rustc", "-vV"], text=True).strip()

    with tempfile.TemporaryDirectory(prefix="anneal_foreign_mir_probe_") as tmp:
        tmp_path = Path(tmp)
        inspector_src = tmp_path / "inspector.rs"
        inspector_bin = tmp_path / "inspector"
        inspector_src.write_text(INSPECTOR_RS)

        subprocess.run(
            ["rustc", "--edition=2021", "-O", str(inspector_src), "-o", str(inspector_bin)],
            check=True,
            env=env,
        )

        # Part 1: Run core_suite under 3 flag configurations
        core_src = tmp_path / "core_suite.rs"
        core_src.write_text(CORE_SUITE_RS)

        configs = {
            "opt0": ["-C", "opt-level=0"],
            "opt0_inline_mir": ["-C", "opt-level=0", "-Z", "inline-mir=yes"],
            "opt2": ["-C", "opt-level=2"],
        }
        core_results = {}
        for cfg_name, flags in configs.items():
            run_env = env.copy()
            run_env["PROBE_MODE"] = "core_suite"
            proc = subprocess.run(
                [
                    str(inspector_bin),
                    "--sysroot",
                    sysroot,
                    "--crate-type=lib",
                    "--edition=2021",
                    *flags,
                    str(core_src),
                ],
                capture_output=True,
                text=True,
                env=run_env,
            )
            if proc.returncode != 0:
                raise RuntimeError(f"inspector failed ({cfg_name}):\n{proc.stderr}\n{proc.stdout}")
            core_results[cfg_name] = extract_probe_json(proc.stdout)

        # Part 2: Run ext_lib matrix across 5 upstream build modes
        ext_src = tmp_path / "ext_lib.rs"
        ext_caller_src = tmp_path / "ext_caller.rs"
        ext_src.write_text(EXT_LIB_RS)
        ext_caller_src.write_text(EXT_CALLER_RS)

        ext_modes = {
            "rlib_opt0": ["--crate-type=rlib", "-C", "opt-level=0"],
            "rlib_opt2": ["--crate-type=rlib", "-C", "opt-level=2"],
            "rmeta_only_opt2": ["--crate-type=rlib", "--emit=metadata", "-C", "opt-level=2"],
            "rlib_opt0_always_encode": ["--crate-type=rlib", "-C", "opt-level=0", "-Z", "always-encode-mir=yes"],
            "rmeta_only_opt0_always_encode": [
                "--crate-type=rlib",
                "--emit=metadata",
                "-C",
                "opt-level=0",
                "-Z",
                "always-encode-mir=yes",
            ],
        }
        ext_results = {}
        for mode_name, build_flags in ext_modes.items():
            mode_dir = tmp_path / mode_name
            mode_dir.mkdir()
            subprocess.run(
                [
                    "rustc",
                    "--crate-name=ext_lib",
                    "--edition=2021",
                    *build_flags,
                    "--out-dir",
                    str(mode_dir),
                    str(ext_src),
                ],
                check=True,
                env=env,
            )
            artifact = mode_dir / ("libext_lib.rmeta" if "rmeta_only" in mode_name else "libext_lib.rlib")
            run_env = env.copy()
            run_env["PROBE_MODE"] = "ext_matrix"
            proc = subprocess.run(
                [
                    str(inspector_bin),
                    "--sysroot",
                    sysroot,
                    "--crate-type=rlib",
                    "--edition=2021",
                    "--extern",
                    f"ext_lib={artifact}",
                    "-L",
                    f"dependency={mode_dir}",
                    str(ext_caller_src),
                ],
                capture_output=True,
                text=True,
                env=run_env,
            )
            if proc.returncode != 0:
                raise RuntimeError(f"inspector ext failed ({mode_name}):\n{proc.stderr}\n{proc.stdout}")
            ext_results[mode_name] = extract_probe_json(proc.stdout)["ext_items"]

        out = {
            "rustc_version": rustc_v,
            "core_suite_by_config": core_results,
            "ext_lib_encoding_matrix": ext_results,
        }
        if len(sys.argv) > 1:
            Path(sys.argv[1]).write_text(json.dumps(out, indent=2) + "\n")
        else:
            print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
