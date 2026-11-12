// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

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
use std::sync::{Mutex, OnceLock};

use rustc_data_structures::steal::Steal;
use rustc_driver::Compilation;
use rustc_hir::def::DefKind;
use rustc_interface::interface;
use rustc_middle::mir::{self, MirPhase, RuntimePhase};
use rustc_middle::ty::{self, TyCtxt};
use rustc_middle::util::Providers;
use rustc_span::def_id::LocalDefId;

type Provider = for<'tcx> fn(TyCtxt<'tcx>, LocalDefId) -> &'tcx Steal<mir::Body<'tcx>>;
static DEFAULT_PROVIDER: OnceLock<Provider> = OnceLock::new();
static REPORTS: Mutex<BTreeMap<u32, BodyReport>> = Mutex::new(BTreeMap::new());

#[derive(Clone, Debug, Default)]
struct BodyReport {
    def_id: u32,
    path: String,
    kind: String,
    phase: String,
    arg_count: usize,
    is_unsafe: bool,
    generics_count: usize,
    abi: String,
    required_consts: Vec<String>,
    cleanup_blocks: usize,
    total_blocks: usize,
    total_statements: usize,
    local_decls: Vec<(u32, String, bool)>,
    unsupported_tys: BTreeSet<String>,
    projections: BTreeSet<String>,
    statements_kinds: BTreeSet<String>,
    rvalue_kinds: BTreeSet<String>,
    binops: BTreeSet<String>,
    unops: BTreeSet<String>,
    casts: BTreeSet<String>,
    aggregates: BTreeSet<String>,
    refs: BTreeSet<String>,
    constants: BTreeSet<String>,
    unsupported_constants: BTreeSet<String>,
    terminators: BTreeSet<String>,
    calls: Vec<String>,
    asserts: Vec<String>,
    drops: Vec<String>,
    mvp_gaps: BTreeSet<String>,
    pretty_mir: String,
}

fn is_mvp_ty<'tcx>(tcx: TyCtxt<'tcx>, t: ty::Ty<'tcx>) -> Result<(), String> {
    let (bits, _signed) = match *t.kind() {
        ty::Bool | ty::Never => return Ok(()),
        ty::Tuple(elements) if elements.is_empty() => return Ok(()),
        ty::Uint(u) => (u.bit_width().unwrap_or(64), false),
        ty::Int(i) => (i.bit_width().unwrap_or(64), true),
        ty::Adt(adt, args) if adt.did().is_local() && adt.is_enum() && args.is_empty() => {
            if !matches!(
                adt.repr().discr_type(),
                rustc_abi::IntegerType::Pointer(true)
            ) {
                return Err(format!("non-isize enum discriminant: {t:?}"));
            }
            if adt.variants().iter().any(|v| !v.fields.is_empty()) {
                return Err(format!("enum with payload: {t:?}"));
            }
            for (_, discr) in adt.discriminants(tcx) {
                if !matches!(discr.ty.kind(), ty::Int(ty::IntTy::Isize)) {
                    return Err(format!("non-isize discr val: {t:?}"));
                }
                if u64::try_from(discr.val).is_err() {
                    return Err(format!("discr > 64 bits: {t:?}"));
                }
            }
            return Ok(());
        }
        _ => return Err(format!("{t:?}")),
    };
    if bits > 64 {
        return Err(format!("int > 64 bits ({bits}): {t:?}"));
    }
    Ok(())
}

fn check_place<'tcx>(
    body: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    place: &mir::Place<'tcx>,
    report: &mut BodyReport,
) {
    if !place.projection.is_empty() {
        let mut cur_pty = mir::PlaceTy::from_ty(body.local_decls[place.local].ty);
        let mut proj_desc = Vec::new();
        for elem in place.projection.iter() {
            let cur_ty = cur_pty.ty;
            match elem {
                mir::ProjectionElem::Deref => {
                    proj_desc.push(format!("Deref(from {cur_ty:?})"));
                    report.mvp_gaps.insert("Projection::Deref".into());
                }
                mir::ProjectionElem::Field(f, fty) => {
                    proj_desc.push(format!("Field({}, {fty:?} on {cur_ty:?})", f.as_u32()));
                    report.mvp_gaps.insert(format!("Projection::Field(on {cur_ty:?})"));
                }
                mir::ProjectionElem::Downcast(sym, v) => {
                    proj_desc.push(format!("Downcast({sym:?}, variant {} on {cur_ty:?})", v.as_u32()));
                    report.mvp_gaps.insert(format!("Projection::Downcast(on {cur_ty:?})"));
                }
                mir::ProjectionElem::Index(idx) => {
                    proj_desc.push(format!("Index(_{})", idx.as_u32()));
                    report.mvp_gaps.insert("Projection::Index".into());
                }
                other => {
                    proj_desc.push(format!("{other:?}"));
                    report.mvp_gaps.insert(format!("Projection::{other:?}"));
                }
            }
            cur_pty = cur_pty.projection_ty(tcx, elem);
        }
        report
            .projections
            .insert(format!("_{}: [{}]", place.local.as_u32(), proj_desc.join(", ")));
    }
}

fn check_operand<'tcx>(
    body: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    op: &mir::Operand<'tcx>,
    report: &mut BodyReport,
) {
    match op {
        mir::Operand::Copy(place) | mir::Operand::Move(place) => {
            check_place(body, tcx, place, report);
        }
        mir::Operand::Constant(c) => {
            let cty = c.const_.ty();
            let desc = format!("{:?} : {:?}", c.const_, cty);
            report.constants.insert(desc.clone());
            if let Err(e) = is_mvp_ty(tcx, cty) {
                report.unsupported_constants.insert(format!("const of unsupported ty ({e}): {desc}"));
                report.mvp_gaps.insert(format!("ConstTy({e})"));
                return;
            }
            match c.const_ {
                mir::Const::Val(mir::ConstValue::ZeroSized, _) => {
                    if !matches!(cty.kind(), ty::Tuple(els) if els.is_empty()) {
                        report.unsupported_constants.insert(format!("non-unit ZeroSized: {desc}"));
                        report.mvp_gaps.insert("Const::NonUnitZeroSized".into());
                    }
                }
                mir::Const::Val(val, _) => {
                    if val.try_to_scalar_int().is_none() {
                        report.unsupported_constants.insert(format!("non-scalar-int Const::Val: {desc}"));
                        report.mvp_gaps.insert("Const::NonScalarInt".into());
                    }
                }
                other => {
                    report.unsupported_constants.insert(format!("non-Val const: {other:?}"));
                    report.mvp_gaps.insert(format!("Const::{other:?}"));
                }
            }
        }
        other => {
            report.mvp_gaps.insert(format!("Operand::{other:?}"));
        }
    }
}

fn inspect_body<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId, body: &mir::Body<'tcx>) -> BodyReport {
    let mut report = BodyReport {
        def_id: def.local_def_index.as_u32(),
        path: tcx.def_path_str(def),
        kind: format!("{:?}", tcx.def_kind(def)),
        phase: format!("{:?}", body.phase),
        arg_count: body.arg_count,
        is_unsafe: false,
        generics_count: tcx.generics_of(def).count(),
        abi: String::new(),
        ..Default::default()
    };
    if matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn) {
        let sig = tcx.fn_sig(def).instantiate_identity().skip_binder();
        report.is_unsafe = sig.safety().is_unsafe();
        report.abi = format!("{:?}", sig.abi());
        if sig.abi() != rustc_abi::ExternAbi::Rust || sig.c_variadic() {
            report.mvp_gaps.insert(format!("ABI({})", report.abi));
        }
    }
    if body.phase != MirPhase::Runtime(RuntimePhase::PostCleanup) {
        report.mvp_gaps.insert(format!("Phase({:?})", body.phase));
    }
    if report.generics_count != 0 {
        report.mvp_gaps.insert(format!("Generics({})", report.generics_count));
    }
    if let Some(rc) = body.required_consts.as_deref() {
        for c in rc {
            report.required_consts.push(format!("{:?}", c.const_));
        }
        if !rc.is_empty() {
            report.mvp_gaps.insert(format!("RequiredConsts({})", rc.len()));
        }
    } else {
        report.mvp_gaps.insert("RequiredConsts(None)".into());
    }

    for (idx, decl) in body.local_decls.iter_enumerated() {
        let ok = is_mvp_ty(tcx, decl.ty);
        if let Err(ref e) = ok {
            report.unsupported_tys.insert(e.clone());
            report.mvp_gaps.insert(format!("LocalTy({e})"));
        }
        report
            .local_decls
            .push((idx.as_u32(), format!("{:?}", decl.ty), ok.is_ok()));
    }

    report.total_blocks = body.basic_blocks.len();
    let mut pretty = String::new();
    pretty.push_str(&format!(
        "// def_id={} path={} args={} locals={} blocks={}\n",
        report.def_id,
        report.path,
        report.arg_count,
        body.local_decls.len(),
        body.basic_blocks.len()
    ));
    for (idx, decl) in body.local_decls.iter_enumerated() {
        pretty.push_str(&format!("//   _{}: {:?} (mut={:?})\n", idx.as_u32(), decl.ty, decl.mutability));
    }

    for (bb_id, block) in body.basic_blocks.iter_enumerated() {
        if block.is_cleanup {
            report.cleanup_blocks += 1;
            report.mvp_gaps.insert("CleanupBlock".into());
        }
        pretty.push_str(&format!("bb{} (cleanup={}): {{\n", bb_id.as_u32(), block.is_cleanup));
        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            report.total_statements += 1;
            pretty.push_str(&format!("  [{}] {:?}\n", stmt_idx, stmt.kind));
            match &stmt.kind {
                mir::StatementKind::Assign(box (place, rval)) => {
                    report.statements_kinds.insert("Assign".into());
                    check_place(body, tcx, place, &mut report);
                    match rval {
                        mir::Rvalue::Use(op, _) => {
                            report.rvalue_kinds.insert("Use".into());
                            check_operand(body, tcx, op, &mut report);
                        }
                        mir::Rvalue::BinaryOp(op, box (l, r)) => {
                            report.rvalue_kinds.insert("BinaryOp".into());
                            report.binops.insert(format!("{op:?}"));
                            check_operand(body, tcx, l, &mut report);
                            check_operand(body, tcx, r, &mut report);
                            let supported_binop = matches!(
                                op,
                                mir::BinOp::BitAnd
                                    | mir::BinOp::BitOr
                                    | mir::BinOp::BitXor
                                    | mir::BinOp::Shl
                                    | mir::BinOp::Shr
                                    | mir::BinOp::Add
                                    | mir::BinOp::Sub
                                    | mir::BinOp::Mul
                                    | mir::BinOp::Eq
                                    | mir::BinOp::Ne
                                    | mir::BinOp::Lt
                                    | mir::BinOp::Le
                                    | mir::BinOp::Gt
                                    | mir::BinOp::Ge
                            );
                            if !supported_binop {
                                report.mvp_gaps.insert(format!("BinOp::{op:?}"));
                            }
                        }
                        mir::Rvalue::UnaryOp(op, operand) => {
                            report.rvalue_kinds.insert("UnaryOp".into());
                            report.unops.insert(format!("{op:?}"));
                            report.mvp_gaps.insert(format!("Rvalue::UnaryOp({op:?})"));
                            check_operand(body, tcx, operand, &mut report);
                        }
                        mir::Rvalue::Cast(kind, operand, target_ty) => {
                            let src_ty = operand.ty(body, tcx);
                            let cast_desc = format!("{kind:?}: {src_ty:?} -> {target_ty:?}");
                            report.rvalue_kinds.insert("Cast".into());
                            report.casts.insert(cast_desc.clone());
                            report.mvp_gaps.insert(format!("Rvalue::Cast({cast_desc})"));
                            check_operand(body, tcx, operand, &mut report);
                        }
                        mir::Rvalue::Aggregate(box kind, ops) => {
                            report.rvalue_kinds.insert("Aggregate".into());
                            if matches!(kind, mir::AggregateKind::Tuple) && ops.is_empty() {
                                report.aggregates.insert("UnitTuple".into());
                            } else {
                                let agg_desc = match kind {
                                    mir::AggregateKind::Tuple => format!("Tuple(arity={})", ops.len()),
                                    mir::AggregateKind::Adt(did, v_idx, args, _, _) => {
                                        format!(
                                            "Adt({}, variant={}, args={:?})",
                                            tcx.def_path_str(*did),
                                            v_idx.as_u32(),
                                            args
                                        )
                                    }
                                    mir::AggregateKind::Array(ety) => format!("Array({ety:?})"),
                                    other => format!("{other:?}"),
                                };
                                report.aggregates.insert(agg_desc.clone());
                                report.mvp_gaps.insert(format!("Rvalue::Aggregate({agg_desc})"));
                                for op in ops {
                                    check_operand(body, tcx, op, &mut report);
                                }
                            }
                        }
                        mir::Rvalue::Discriminant(p) => {
                            report.rvalue_kinds.insert("Discriminant".into());
                            check_place(body, tcx, p, &mut report);
                            let pty = p.ty(body, tcx).ty;
                            if is_mvp_ty(tcx, pty).is_err() {
                                report.mvp_gaps.insert(format!("Discriminant(on {pty:?})"));
                            }
                        }
                        mir::Rvalue::Ref(_, borrow_kind, p) => {
                            let pty = p.ty(body, tcx).ty;
                            let ref_desc = format!("Ref({borrow_kind:?}, {pty:?})");
                            report.rvalue_kinds.insert("Ref".into());
                            report.refs.insert(ref_desc.clone());
                            report.mvp_gaps.insert(format!("Rvalue::{ref_desc}"));
                            check_place(body, tcx, p, &mut report);
                        }
                        mir::Rvalue::CopyForDeref(p) => {
                            let pty = p.ty(body, tcx).ty;
                            report.rvalue_kinds.insert("CopyForDeref".into());
                            report.mvp_gaps.insert(format!("Rvalue::CopyForDeref({pty:?})"));
                            check_place(body, tcx, p, &mut report);
                        }
                        mir::Rvalue::RawPtr(kind, p) => {
                            report.rvalue_kinds.insert("RawPtr".into());
                            report.mvp_gaps.insert(format!("Rvalue::RawPtr({kind:?})"));
                            check_place(body, tcx, p, &mut report);
                        }
                        other => {
                            report.rvalue_kinds.insert(format!("{other:?}"));
                            report.mvp_gaps.insert(format!("Rvalue::{other:?}"));
                        }
                    }
                }
                mir::StatementKind::StorageLive(_) => {
                    report.statements_kinds.insert("StorageLive".into());
                }
                mir::StatementKind::StorageDead(_) => {
                    report.statements_kinds.insert("StorageDead".into());
                }
                mir::StatementKind::Nop => {
                    report.statements_kinds.insert("Nop".into());
                }
                mir::StatementKind::SetDiscriminant { place, variant_index } => {
                    report.statements_kinds.insert("SetDiscriminant".into());
                    report.mvp_gaps.insert(format!("Statement::SetDiscriminant(variant={})", variant_index.as_u32()));
                    check_place(body, tcx, place, &mut report);
                }
                mir::StatementKind::Intrinsic(box intr) => {
                    report.statements_kinds.insert(format!("Intrinsic({intr:?})"));
                    report.mvp_gaps.insert(format!("Statement::Intrinsic({intr:?})"));
                }
                other => {
                    report.statements_kinds.insert(format!("{other:?}"));
                    report.mvp_gaps.insert(format!("Statement::{other:?}"));
                }
            }
        }
        if let Some(term) = &block.terminator {
            pretty.push_str(&format!("  TERM: {:?}\n", term.kind));
            match &term.kind {
                mir::TerminatorKind::Goto { .. } => {
                    report.terminators.insert("Goto".into());
                }
                mir::TerminatorKind::SwitchInt { discr, .. } => {
                    report.terminators.insert("SwitchInt".into());
                    check_operand(body, tcx, discr, &mut report);
                }
                mir::TerminatorKind::Return => {
                    report.terminators.insert("Return".into());
                }
                mir::TerminatorKind::Unreachable => {
                    report.terminators.insert("Unreachable".into());
                }
                mir::TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                    unwind,
                    ..
                } => {
                    report.terminators.insert("Call".into());
                    check_place(body, tcx, destination, &mut report);
                    for a in args {
                        check_operand(body, tcx, &a.node, &mut report);
                    }
                    let fty = func.ty(body, tcx);
                    let callee_desc = match *fty.kind() {
                        ty::FnDef(def_id, substs) => {
                            let path = tcx.def_path_str(def_id);
                            if substs.is_empty() {
                                path
                            } else {
                                format!("{path}::<{substs:?}>")
                            }
                        }
                        _ => format!("{func:?} : {fty:?}"),
                    };
                    report.calls.push(format!(
                        "{callee_desc} -> dest={destination:?}, target={target:?}, unwind={unwind:?}"
                    ));
                    report.mvp_gaps.insert(format!("Terminator::Call({callee_desc})"));
                }
                mir::TerminatorKind::Assert {
                    cond,
                    expected,
                    msg,
                    target,
                    unwind,
                } => {
                    report.terminators.insert("Assert".into());
                    check_operand(body, tcx, cond, &mut report);
                    report.asserts.push(format!(
                        "expected={expected}, msg={msg:?}, target={target:?}, unwind={unwind:?}"
                    ));
                    report.mvp_gaps.insert(format!("Terminator::Assert({msg:?})"));
                }
                mir::TerminatorKind::Drop {
                    place,
                    target,
                    unwind,
                    ..
                } => {
                    report.terminators.insert("Drop".into());
                    check_place(body, tcx, place, &mut report);
                    let pty = place.ty(body, tcx).ty;
                    report.drops.push(format!("place={place:?} ({pty:?}), target={target:?}, unwind={unwind:?}"));
                    report.mvp_gaps.insert(format!("Terminator::Drop({pty:?})"));
                }
                mir::TerminatorKind::UnwindResume => {
                    report.terminators.insert("UnwindResume".into());
                    report.mvp_gaps.insert("Terminator::UnwindResume".into());
                }
                other => {
                    report.terminators.insert(format!("{other:?}"));
                    report.mvp_gaps.insert(format!("Terminator::{other:?}"));
                }
            }
        }
        pretty.push_str("}\n");
    }
    report.pretty_mir = pretty;
    report
}

fn hook<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> &'tcx Steal<mir::Body<'tcx>> {
    let provider = DEFAULT_PROVIDER.get().unwrap();
    let original = provider(tcx, def);
    let report = inspect_body(tcx, def, &original.borrow());
    REPORTS.lock().unwrap().insert(def.local_def_index.as_u32(), report);
    original
}

fn override_queries(_: &rustc_session::Session, providers: &mut Providers) {
    DEFAULT_PROVIDER
        .set(providers.queries.mir_drops_elaborated_and_const_checked)
        .unwrap();
    providers.queries.mir_drops_elaborated_and_const_checked = hook;
}

struct ProbeCallbacks;

impl rustc_driver::Callbacks for ProbeCallbacks {
    fn config(&mut self, config: &mut interface::Config) {
        config.override_queries = Some(override_queries);
    }

    fn after_analysis<'tcx>(&mut self, _: &interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        for def in tcx.hir_body_owners() {
            let kind = tcx.def_kind(def);
            if matches!(kind, DefKind::Fn | DefKind::AssocFn) {
                let _ = tcx.mir_drops_elaborated_and_const_checked(def);
            }
        }
        let reports = REPORTS.lock().unwrap();
        let mut out = String::new();
        out.push_str("[\n");
        let mut first = true;
        for r in reports.values() {
            if !first {
                out.push_str(",\n");
            }
            first = false;
            let esc = |s: &str| {
                s.replace('\\', "\\\\")
                    .replace('"', "\\\"")
                    .replace('\n', "\\n")
                    .replace('\r', "")
                    .replace('\t', "\\t")
            };
            let list_str = |items: Vec<String>| {
                items
                    .into_iter()
                    .map(|x| format!("\"{}\"", esc(&x)))
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            out.push_str(&format!(
                "  {{\"def_id\": {}, \"path\": \"{}\", \"kind\": \"{}\", \"arg_count\": {}, \"is_unsafe\": {}, \"generics_count\": {}, \"abi\": \"{}\", \"total_blocks\": {}, \"cleanup_blocks\": {}, \"total_statements\": {}, \"required_consts\": [{}], \"unsupported_tys\": [{}], \"projections\": [{}], \"statements_kinds\": [{}], \"rvalue_kinds\": [{}], \"binops\": [{}], \"unops\": [{}], \"casts\": [{}], \"aggregates\": [{}], \"refs\": [{}], \"constants\": [{}], \"unsupported_constants\": [{}], \"terminators\": [{}], \"calls\": [{}], \"asserts\": [{}], \"drops\": [{}], \"mvp_gaps\": [{}], \"pretty_mir\": \"{}\"}}",
                r.def_id,
                esc(&r.path),
                esc(&r.kind),
                r.arg_count,
                r.is_unsafe,
                r.generics_count,
                esc(&r.abi),
                r.total_blocks,
                r.cleanup_blocks,
                r.total_statements,
                list_str(r.required_consts.clone()),
                list_str(r.unsupported_tys.iter().cloned().collect()),
                list_str(r.projections.iter().cloned().collect()),
                list_str(r.statements_kinds.iter().cloned().collect()),
                list_str(r.rvalue_kinds.iter().cloned().collect()),
                list_str(r.binops.iter().cloned().collect()),
                list_str(r.unops.iter().cloned().collect()),
                list_str(r.casts.iter().cloned().collect()),
                list_str(r.aggregates.iter().cloned().collect()),
                list_str(r.refs.iter().cloned().collect()),
                list_str(r.constants.iter().cloned().collect()),
                list_str(r.unsupported_constants.iter().cloned().collect()),
                list_str(r.terminators.iter().cloned().collect()),
                list_str(r.calls.clone()),
                list_str(r.asserts.clone()),
                list_str(r.drops.clone()),
                list_str(r.mvp_gaps.iter().cloned().collect()),
                esc(&r.pretty_mir),
            ));
        }
        out.push_str("\n]\n");
        std::fs::write(
            std::env::var("PROBE_OUT").unwrap_or_else(|_| "mir_probe_out.json".into()),
            out,
        )
        .unwrap();
        Compilation::Stop
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut callbacks = ProbeCallbacks;
    let _ = rustc_driver::catch_fatal_errors(|| {
        rustc_driver::run_compiler(&args, &mut callbacks);
    });
}
