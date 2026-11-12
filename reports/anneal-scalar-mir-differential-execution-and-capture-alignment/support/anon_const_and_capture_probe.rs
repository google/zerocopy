// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Standalone `rustc_driver` probe for Q-B1: `DefKind::AnonConst` and
//! `DefKind::InlineConst` taxonomy, parent `DefKind` relationships, variant
//! discriminant evaluation, and PME/panicking constant behavior in pinned
//! `rustc 1.98.0-nightly (f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1)`.

#![feature(rustc_private, box_patterns)]

extern crate rustc_abi;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::sync::{Mutex, OnceLock};

use rustc_data_structures::steal::Steal;
use rustc_driver::Compilation;
use rustc_hir::def::DefKind;
use rustc_interface::interface;
use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt};
use rustc_middle::util::Providers;
use rustc_span::def_id::LocalDefId;

type Provider = for<'tcx> fn(TyCtxt<'tcx>, LocalDefId) -> &'tcx Steal<mir::Body<'tcx>>;
static DEFAULT_PROVIDER: OnceLock<Provider> = OnceLock::new();
static IN_AFTER_ANALYSIS: Mutex<bool> = Mutex::new(false);
static RESOLVE_UNEVAL: Mutex<bool> = Mutex::new(false);
static HOOKED_BODIES: Mutex<BTreeMap<u32, HookedBodyInfo>> = Mutex::new(BTreeMap::new());

#[derive(Clone, Default)]
struct HookedBodyInfo {
    def_id: u32,
    path: String,
    kind: String,
    phase: String,
    blocks: usize,
    called_before_after_analysis: bool,
    required_consts_raw: Vec<String>,
    operand_consts_raw: Vec<String>,
}

#[derive(Default)]
struct ScenarioReport {
    scenario: String,
    reached_after_analysis: bool,
    has_errors_at_after_analysis_entry: bool,
    has_errors_at_after_analysis_exit: bool,
    driver_result_ok: bool,
    defs: Vec<String>,
    enums: Vec<String>,
    bodies: Vec<String>,
}

struct TaxonomyCallbacks {
    force_discriminants: bool,
    force_body_mir: bool,
    report: Mutex<ScenarioReport>,
}

fn esc(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "")
        .replace('\t', "\\t")
}

fn format_eval_result(
    res: Result<mir::ConstValue, mir::interpret::ErrorHandled>,
) -> String {
    match res {
        Ok(val) => format!("Ok({val:?})"),
        Err(mir::interpret::ErrorHandled::Reported(info, _span)) => {
            format!(
                "Err(Reported(allowed_in_infallible={}))",
                info.is_allowed_in_infallible()
            )
        }
        Err(mir::interpret::ErrorHandled::TooGeneric(_span)) => "Err(TooGeneric)".to_string(),
    }
}

fn format_const_hook<'tcx>(
    tcx: TyCtxt<'tcx>,
    c: &mir::ConstOperand<'tcx>,
    resolve_uneval: bool,
) -> String {
    match c.const_ {
        mir::Const::Val(val, ty) => format!("Val({val:?}, {ty:?})"),
        mir::Const::Unevaluated(uv, ty) => {
            let def_path = tcx.def_path_str(uv.def);
            let def_kind = tcx.def_kind(uv.def);
            if resolve_uneval {
                let eval_res = tcx.const_eval_resolve(
                    ty::TypingEnv::fully_monomorphized(),
                    uv,
                    c.span,
                );
                format!(
                    "Unevaluated(def={def_path}, kind={def_kind:?}, args={:?}, promoted={:?}, ty={ty:?}, const_eval_resolve={})",
                    uv.args,
                    uv.promoted,
                    format_eval_result(eval_res)
                )
            } else {
                format!(
                    "Unevaluated(def={def_path}, kind={def_kind:?}, args={:?}, promoted={:?}, ty={ty:?})",
                    uv.args, uv.promoted
                )
            }
        }
        mir::Const::Ty(ty, ct) => format!("Ty({ty:?}, {ct:?})"),
    }
}

fn hook<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> &'tcx Steal<mir::Body<'tcx>> {
    let provider = DEFAULT_PROVIDER.get().unwrap();
    let original = provider(tcx, def);
    let in_after = *IN_AFTER_ANALYSIS.lock().unwrap();
    let resolve_flag = *RESOLVE_UNEVAL.lock().unwrap();
    if !original.is_stolen() {
        let body = original.borrow();
        let resolve = in_after && resolve_flag && tcx.generics_of(def).count() == 0;
        let req_consts: Vec<String> = body
            .required_consts
            .as_deref()
            .unwrap_or(&[])
            .iter()
            .map(|c| format_const_hook(tcx, c, resolve))
            .collect();
        let mut op_consts = Vec::new();
        for (bb_id, bb) in body.basic_blocks.iter_enumerated() {
            for (s_idx, stmt) in bb.statements.iter().enumerate() {
                if let mir::StatementKind::Assign(box (_, rval)) = &stmt.kind {
                    match rval {
                        mir::Rvalue::Use(mir::Operand::Constant(c), _)
                        | mir::Rvalue::Repeat(mir::Operand::Constant(c), _)
                        | mir::Rvalue::UnaryOp(_, mir::Operand::Constant(c)) => {
                            op_consts.push(format!(
                                "bb{}[{}]: {}",
                                bb_id.as_u32(),
                                s_idx,
                                format_const_hook(tcx, c, resolve)
                            ));
                        }
                        mir::Rvalue::BinaryOp(_, box (l, r)) => {
                            for op in [l, r] {
                                if let mir::Operand::Constant(c) = op {
                                    op_consts.push(format!(
                                        "bb{}[{}]: {}",
                                        bb_id.as_u32(),
                                        s_idx,
                                        format_const_hook(tcx, c, resolve)
                                    ));
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        HOOKED_BODIES.lock().unwrap().insert(
            def.local_def_index.as_u32(),
            HookedBodyInfo {
                def_id: def.local_def_index.as_u32(),
                path: tcx.def_path_str(def),
                kind: format!("{:?}", tcx.def_kind(def)),
                phase: format!("{:?}", body.phase),
                blocks: body.basic_blocks.len(),
                called_before_after_analysis: !in_after,
                required_consts_raw: req_consts,
                operand_consts_raw: op_consts,
            },
        );
    }
    original
}

fn override_queries(_: &rustc_session::Session, providers: &mut Providers) {
    let _ = DEFAULT_PROVIDER.set(providers.queries.mir_drops_elaborated_and_const_checked);
    providers.queries.mir_drops_elaborated_and_const_checked = hook;
}

impl rustc_driver::Callbacks for TaxonomyCallbacks {
    fn config(&mut self, config: &mut interface::Config) {
        config.override_queries = Some(override_queries);
    }

    fn after_analysis<'tcx>(&mut self, _: &interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        *IN_AFTER_ANALYSIS.lock().unwrap() = true;
        let mut rep = self.report.lock().unwrap();
        rep.reached_after_analysis = true;
        rep.has_errors_at_after_analysis_entry = tcx.dcx().has_errors().is_some();

        let body_owners: BTreeSet<u32> = tcx
            .hir_body_owners()
            .map(|d| d.local_def_index.as_u32())
            .collect();

        let defs: Vec<LocalDefId> = tcx.iter_local_def_id().collect();

        if tcx.dcx().has_errors().is_none() && self.force_body_mir {
            for &def in &defs {
                let idx = def.local_def_index.as_u32();
                if body_owners.contains(&idx) {
                    let _ = tcx.mir_drops_elaborated_and_const_checked(def);
                }
            }
        }

        let hooked = HOOKED_BODIES.lock().unwrap().clone();

        for def in defs {
            let idx = def.local_def_index.as_u32();
            let path = tcx.def_path_str(def);
            let kind = tcx.def_kind(def);
            let has_body = body_owners.contains(&idx);
            let (
                parent_kind_str,
                parent_path_str,
                grandparent_info,
                is_variant_discr_anon_const,
                matches_explicit_variant_discr,
            ) = if let Some(parent_did) = tcx.opt_parent(def.to_def_id()) {
                let pk = tcx.def_kind(parent_did);
                let pp = tcx.def_path_str(parent_did);
                let gp = if let Some(gp_did) = tcx.opt_parent(parent_did) {
                    format!("{:?} ({})", tcx.def_kind(gp_did), tcx.def_path_str(gp_did))
                } else {
                    "None".to_string()
                };
                let is_var_discr =
                    matches!(kind, DefKind::AnonConst) && matches!(pk, DefKind::Variant);
                let is_explicit_discr = if is_var_discr {
                    if let Some(gp_did) = tcx.opt_parent(parent_did) {
                        if matches!(tcx.def_kind(gp_did), DefKind::Enum) {
                            tcx.adt_def(gp_did).variants().iter().any(|v| {
                                v.def_id == parent_did
                                    && v.discr == ty::VariantDiscr::Explicit(def.to_def_id())
                            })
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                } else {
                    false
                };
                (format!("{pk:?}"), pp, gp, is_var_discr, is_explicit_discr)
            } else {
                (
                    "None".to_string(),
                    "None".to_string(),
                    "None".to_string(),
                    false,
                    false,
                )
            };

            let const_ctx = if has_body {
                format!("{:?}", tcx.hir_body_const_context(def))
            } else {
                "None".to_string()
            };
            let generics_count = match kind {
                DefKind::AnonConst
                | DefKind::InlineConst
                | DefKind::Const { .. }
                | DefKind::AssocConst { .. }
                | DefKind::Enum
                | DefKind::Struct
                | DefKind::Fn
                | DefKind::AssocFn => tcx.generics_of(def).count(),
                _ => 0,
            };
            let ty_str = match kind {
                DefKind::AnonConst
                | DefKind::InlineConst
                | DefKind::Const { .. }
                | DefKind::AssocConst { .. }
                | DefKind::Static { .. }
                | DefKind::Enum
                | DefKind::Struct
                | DefKind::Variant
                | DefKind::ConstParam => {
                    format!("{:?}", tcx.type_of(def).instantiate_identity())
                }
                _ => "N/A".to_string(),
            };
            let poly_eval = if matches!(
                kind,
                DefKind::AnonConst | DefKind::Const { .. } | DefKind::AssocConst { .. }
            ) && generics_count == 0
                && tcx.dcx().has_errors().is_none()
            {
                format_eval_result(tcx.const_eval_poly(def.to_def_id()))
            } else {
                "skipped".to_string()
            };

            let (called_before_after, is_stolen_now) =
                if has_body && tcx.dcx().has_errors().is_none() {
                    let st = tcx.mir_drops_elaborated_and_const_checked(def).is_stolen();
                    let cb = hooked
                        .get(&idx)
                        .map(|h| h.called_before_after_analysis)
                        .unwrap_or(false);
                    (cb, st)
                } else {
                    (false, false)
                };

            rep.defs.push(format!(
                "{{\"def_id\": {idx}, \"path\": \"{}\", \"kind\": \"{kind:?}\", \"has_body\": {has_body}, \"generics_count\": {generics_count}, \"const_context\": \"{}\", \"parent_kind\": \"{}\", \"parent_path\": \"{}\", \"grandparent\": \"{}\", \"type_of\": \"{}\", \"const_eval\": \"{}\", \"is_variant_discr_anon_const\": {is_variant_discr_anon_const}, \"matches_explicit_variant_discr\": {matches_explicit_variant_discr}, \"mir_called_during_analysis\": {called_before_after}, \"mir_stolen_by_ctfe\": {is_stolen_now}}}",
                esc(&path),
                esc(&const_ctx),
                esc(&parent_kind_str),
                esc(&parent_path_str),
                esc(&grandparent_info),
                esc(&ty_str),
                esc(&poly_eval),
            ));

            if matches!(kind, DefKind::Enum) {
                let adt = tcx.adt_def(def);
                let mut variants_json = Vec::new();
                for (v_idx, v_def) in adt.variants().iter_enumerated() {
                    let discr_repr = match v_def.discr {
                        ty::VariantDiscr::Explicit(d) => {
                            format!(
                                "Explicit(def_id={}, path={}, kind={:?})",
                                d.index.as_u32(),
                                tcx.def_path_str(d),
                                tcx.def_kind(d)
                            )
                        }
                        ty::VariantDiscr::Relative(offset) => format!("Relative({offset})"),
                    };
                    variants_json.push(format!(
                        "{{\"variant_idx\": {}, \"name\": \"{}\", \"fields_count\": {}, \"discr_kind\": \"{}\"}}",
                        v_idx.as_u32(),
                        esc(v_def.name.as_str()),
                        v_def.fields.len(),
                        esc(&discr_repr)
                    ));
                }
                let mut evaluated_discrs = Vec::new();
                if self.force_discriminants {
                    for (v_idx, discr) in adt.discriminants(tcx) {
                        evaluated_discrs.push(format!(
                            "{{\"variant_idx\": {}, \"val_u128\": \"{}\", \"val_i64\": {}, \"ty\": \"{:?}\"}}",
                            v_idx.as_u32(),
                            discr.val,
                            (discr.val as u64) as i64,
                            discr.ty
                        ));
                    }
                }
                rep.enums.push(format!(
                    "{{\"def_id\": {idx}, \"path\": \"{}\", \"repr_discr_type\": \"{:?}\", \"variants\": [{}], \"evaluated_discriminants\": [{}]}}",
                    esc(&path),
                    adt.repr().discr_type(),
                    variants_json.join(", "),
                    evaluated_discrs.join(", ")
                ));
            }
        }

        for h in hooked.values() {
            let req_s: Vec<String> = h
                .required_consts_raw
                .iter()
                .map(|s| format!("\"{}\"", esc(s)))
                .collect();
            let op_s: Vec<String> = h
                .operand_consts_raw
                .iter()
                .map(|s| format!("\"{}\"", esc(s)))
                .collect();
            rep.bodies.push(format!(
                "{{\"def_id\": {}, \"path\": \"{}\", \"kind\": \"{}\", \"phase\": \"{}\", \"blocks\": {}, \"called_before_after_analysis\": {}, \"required_consts\": [{}], \"operand_consts\": [{}]}}",
                h.def_id,
                esc(&h.path),
                esc(&h.kind),
                esc(&h.phase),
                h.blocks,
                h.called_before_after_analysis,
                req_s.join(", "),
                op_s.join(", "),
            ));
        }

        rep.has_errors_at_after_analysis_exit = tcx.dcx().has_errors().is_some();
        Compilation::Stop
    }
}

fn run_scenario(
    work_dir: &std::path::Path,
    sysroot: &str,
    name: &str,
    source: &str,
    force_discriminants: bool,
    force_body_mir: bool,
    resolve_uneval: bool,
) -> String {
    *IN_AFTER_ANALYSIS.lock().unwrap() = false;
    *RESOLVE_UNEVAL.lock().unwrap() = resolve_uneval;
    HOOKED_BODIES.lock().unwrap().clear();

    let src_path = work_dir.join(format!("{name}.rs"));
    let out_dir = work_dir.join(format!("out_{name}"));
    std::fs::create_dir_all(&out_dir).unwrap();
    std::fs::write(&src_path, source).unwrap();

    let args = vec![
        "anon_const_and_capture_probe".to_string(),
        src_path.to_str().unwrap().to_string(),
        "--crate-type=lib".to_string(),
        format!("--crate-name={name}"),
        "--edition=2024".to_string(),
        "--target=x86_64-unknown-linux-gnu".to_string(),
        "--emit=metadata".to_string(),
        "-Copt-level=0".to_string(),
        "-Cdebug-assertions=no".to_string(),
        "-Coverflow-checks=no".to_string(),
        format!("--sysroot={sysroot}"),
        format!("--out-dir={}", out_dir.to_str().unwrap()),
    ];

    let mut callbacks = TaxonomyCallbacks {
        force_discriminants,
        force_body_mir,
        report: Mutex::new(ScenarioReport {
            scenario: name.to_string(),
            ..Default::default()
        }),
    };

    let compiler_res = rustc_driver::catch_fatal_errors(|| {
        rustc_driver::run_compiler(&args, &mut callbacks);
    });
    let mut rep = callbacks.report.into_inner().unwrap();
    rep.driver_result_ok = compiler_res.is_ok();

    format!(
        "  {{\n    \"scenario\": \"{}\",\n    \"driver_result_ok\": {},\n    \"reached_after_analysis\": {},\n    \"has_errors_at_after_analysis_entry\": {},\n    \"has_errors_at_after_analysis_exit\": {},\n    \"defs\": [\n      {}\n    ],\n    \"enums\": [\n      {}\n    ],\n    \"bodies\": [\n      {}\n    ]\n  }}",
        esc(&rep.scenario),
        rep.driver_result_ok,
        rep.reached_after_analysis,
        rep.has_errors_at_after_analysis_entry,
        rep.has_errors_at_after_analysis_exit,
        rep.defs.join(",\n      "),
        rep.enums.join(",\n      "),
        rep.bodies.join(",\n      "),
    )
}

fn main() {
    let sysroot = std::env::var("ANNEAL_SYSROOT").expect("set ANNEAL_SYSROOT");
    let work_dir = PathBuf::from(
        std::env::var("PROBE_WORK_DIR").unwrap_or_else(|_| "/tmp/anon_const_probe".to_string()),
    );
    std::fs::create_dir_all(&work_dir).unwrap();

    // Scenario 1: All valid constructs (a) explicit enum discriminants,
    // (a2) payload enum with array field length to test parent_kind of field AnonConst,
    // (b) array length & repeat counts, (c) live inline const block,
    // (d) generic const parameter defaults, plus associated/module consts.
    let scenario_valid = r#"#![allow(dead_code)]

// (a) Explicit and implicit enum variant discriminants
pub enum ExplicitEnum {
    Neg = -1,
    ImplicitZero,
    Pos = 1 + 2,
}

// (a2) Enum variant with an array payload (AnonConst inside a Variant's Field)
pub enum PayloadArrayEnum {
    Arr([u8; 4]),
}

// (b) Array length and repeat count expressions
pub fn array_and_repeat() -> [u8; 4] {
    let _rep = [0u8; 1 + 1];
    [1u8; 4]
}

// (c1) Live inline const block
pub fn live_inline_const(x: i32) -> i32 {
    x + const { 40 + 2 }
}

// (d) Generic const parameter defaults
pub struct ConstDefaultStruct<const N: usize = 8, const M: usize = { 2 + 3 }>;

// Module-level const and associated const for comparison
pub const MODULE_CONST: i32 = -42;

pub fn use_module_and_assoc_const(x: i32, y: i8) -> (i32, i8) {
    (x + MODULE_CONST, y + i8::MIN)
}
"#;

    // Scenario 2a: (e) Compile-time failing enum discriminant (`enum Bad { X = 1 / 0 }`)
    let scenario_bad_enum_div = r#"#![allow(dead_code, unconditional_panic)]

pub enum Bad {
    X = 1 / 0,
}

pub fn trivial() -> u64 {
    0
}
"#;

    // Scenario 2b: Compile-time panicking enum discriminant (`enum BadPanic { X = panic!(...) }`)
    let scenario_bad_enum_panic = r#"#![allow(dead_code, unconditional_panic)]

pub enum BadPanic {
    X = { panic!("discriminant boom") },
}

pub fn trivial() -> u64 {
    0
}
"#;

    // Scenario 3: Dead-branch panicking `const { 1 / 0 }`
    let scenario_dead_inline_const_only = r#"#![allow(dead_code, unconditional_panic)]

pub fn dead_inline_const_div_zero(x: i32) -> i32 {
    if false {
        const { 1 / 0 }
    } else {
        x + 7
    }
}
"#;

    let r1 = run_scenario(
        &work_dir,
        &sysroot,
        "taxonomy_valid_and_mixed",
        scenario_valid,
        true,
        true,
        true,
    );
    let r2a = run_scenario(
        &work_dir,
        &sysroot,
        "bad_enum_discriminant_div_zero",
        scenario_bad_enum_div,
        false,
        false,
        false,
    );
    let r2b = run_scenario(
        &work_dir,
        &sysroot,
        "bad_enum_discriminant_explicit_panic",
        scenario_bad_enum_panic,
        false,
        false,
        false,
    );
    let r3a = run_scenario(
        &work_dir,
        &sysroot,
        "dead_branch_inline_const_div_zero_without_const_eval_resolve",
        scenario_dead_inline_const_only,
        true,
        true,
        false,
    );
    let r3b = run_scenario(
        &work_dir,
        &sysroot,
        "dead_branch_inline_const_div_zero_with_const_eval_resolve",
        scenario_dead_inline_const_only,
        true,
        true,
        true,
    );

    let json = format!("[\n{r1},\n{r2a},\n{r2b},\n{r3a},\n{r3b}\n]\n");
    let out_file = std::env::var("PROBE_OUT")
        .unwrap_or_else(|_| "anon_const_taxonomy_results.json".to_string());
    std::fs::write(&out_file, json).unwrap();
}
