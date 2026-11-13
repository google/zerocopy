#![feature(rustc_private, box_patterns)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface;
use rustc_middle::mir::*;
use rustc_middle::ty::{self, TyCtxt};
use std::collections::BTreeMap;

struct CensusCallbacks {
    crate_name: String,
    out_path: String,
}

#[derive(Default)]
struct Counts {
    bodies: usize,
    basic_blocks: usize,
    statements: BTreeMap<String, usize>,
    terminators: BTreeMap<String, usize>,
    unwind_actions: BTreeMap<String, usize>,
    rvalues: BTreeMap<String, usize>,
    operands: BTreeMap<String, usize>,
    projections: BTreeMap<String, usize>,
    casts: BTreeMap<String, usize>,
    binops: BTreeMap<String, usize>,
    unops: BTreeMap<String, usize>,
    aggregates: BTreeMap<String, usize>,
    nondiverging_intrinsics: BTreeMap<String, usize>,
    call_intrinsics: BTreeMap<String, usize>,
    const_kinds: BTreeMap<String, usize>,
}

fn inc(map: &mut BTreeMap<String, usize>, k: impl Into<String>) {
    *map.entry(k.into()).or_insert(0) += 1;
}

fn record_place<'tcx>(c: &mut Counts, place: &Place<'tcx>) {
    for elem in place.projection.iter() {
        let name = match elem {
            ProjectionElem::Deref => "Deref",
            ProjectionElem::Field(..) => "Field",
            ProjectionElem::Index(..) => "Index",
            ProjectionElem::ConstantIndex { .. } => "ConstantIndex",
            ProjectionElem::Subslice { .. } => "Subslice",
            ProjectionElem::Downcast(..) => "Downcast",
            ProjectionElem::OpaqueCast(..) => "OpaqueCast",
            ProjectionElem::UnwrapUnsafeBinder(..) => "UnwrapUnsafeBinder",
        };
        inc(&mut c.projections, name);
    }
}

fn record_operand<'tcx>(_tcx: TyCtxt<'tcx>, c: &mut Counts, op: &Operand<'tcx>) {
    match op {
        Operand::Copy(p) => {
            inc(&mut c.operands, "Copy");
            record_place(c, p);
        }
        Operand::Move(p) => {
            inc(&mut c.operands, "Move");
            record_place(c, p);
        }
        Operand::Constant(co) => {
            inc(&mut c.operands, "Constant");
            let ck = match co.const_ {
                Const::Ty(_, _) => "Const::Ty",
                Const::Unevaluated(_, _) => "Const::Unevaluated",
                Const::Val(cv, _) => match cv {
                    ConstValue::Scalar(_) => "Const::Val(Scalar)",
                    ConstValue::ZeroSized => "Const::Val(ZeroSized)",
                    ConstValue::Slice { .. } => "Const::Val(Slice)",
                    ConstValue::Indirect { .. } => "Const::Val(Indirect)",
                },
            };
            inc(&mut c.const_kinds, ck);
        }
        Operand::RuntimeChecks(rc) => {
            inc(&mut c.operands, format!("RuntimeChecks({rc:?})"));
        }
    }
}

fn walk_body<'tcx>(tcx: TyCtxt<'tcx>, c: &mut Counts, body: &Body<'tcx>) {
    c.bodies += 1;
    for bb in body.basic_blocks.iter() {
        c.basic_blocks += 1;
        for stmt in &bb.statements {
            let sk = match &stmt.kind {
                StatementKind::Assign(box (place, rv)) => {
                    record_place(c, place);
                    let rvk = match rv {
                        Rvalue::Use(op, retag) => {
                            record_operand(tcx, c, op);
                            format!("Use(WithRetag::{retag:?})")
                        }
                        Rvalue::Repeat(op, _) => {
                            record_operand(tcx, c, op);
                            "Repeat".to_string()
                        }
                        Rvalue::Ref(_, bk, p) => {
                            record_place(c, p);
                            let bks = match bk {
                                BorrowKind::Shared => "Shared",
                                BorrowKind::Fake(_) => "Fake",
                                BorrowKind::Mut { .. } => "Mut",
                            };
                            format!("Ref({bks})")
                        }
                        Rvalue::ThreadLocalRef(_) => "ThreadLocalRef".to_string(),
                        Rvalue::RawPtr(rk, p) => {
                            record_place(c, p);
                            format!("RawPtr({rk:?})")
                        }
                        Rvalue::Cast(ck, op, _) => {
                            record_operand(tcx, c, op);
                            let cks = match ck {
                                CastKind::PointerExposeProvenance => "PointerExposeProvenance".to_string(),
                                CastKind::PointerWithExposedProvenance => "PointerWithExposedProvenance".to_string(),
                                CastKind::PointerCoercion(pc, _) => format!("PointerCoercion({pc:?})"),
                                CastKind::IntToInt => "IntToInt".to_string(),
                                CastKind::FloatToInt => "FloatToInt".to_string(),
                                CastKind::FloatToFloat => "FloatToFloat".to_string(),
                                CastKind::IntToFloat => "IntToFloat".to_string(),
                                CastKind::PtrToPtr => "PtrToPtr".to_string(),
                                CastKind::FnPtrToPtr => "FnPtrToPtr".to_string(),
                                CastKind::Transmute => "Transmute".to_string(),
                                CastKind::BoxDerefTransmute => "BoxDerefTransmute".to_string(),
                                CastKind::Subtype => "Subtype".to_string(),
                            };
                            inc(&mut c.casts, cks);
                            "Cast".to_string()
                        }
                        Rvalue::BinaryOp(bop, box (lhs, rhs)) => {
                            record_operand(tcx, c, lhs);
                            record_operand(tcx, c, rhs);
                            inc(&mut c.binops, format!("{bop:?}"));
                            "BinaryOp".to_string()
                        }
                        Rvalue::UnaryOp(uop, op) => {
                            record_operand(tcx, c, op);
                            inc(&mut c.unops, format!("{uop:?}"));
                            "UnaryOp".to_string()
                        }
                        Rvalue::Discriminant(p) => {
                            record_place(c, p);
                            "Discriminant".to_string()
                        }
                        Rvalue::Aggregate(box ak, ops) => {
                            for op in ops {
                                record_operand(tcx, c, op);
                            }
                            let aks = match ak {
                                AggregateKind::Array(_) => "Array",
                                AggregateKind::Tuple => "Tuple",
                                AggregateKind::Adt(_, _, _, _, Some(_)) => "Adt(Union)",
                                AggregateKind::Adt(did, _, _, _, None) => {
                                    if tcx.adt_def(*did).is_enum() {
                                        "Adt(Enum)"
                                    } else {
                                        "Adt(Struct)"
                                    }
                                }
                                AggregateKind::Closure(..) => "Closure",
                                AggregateKind::Coroutine(..) => "Coroutine",
                                AggregateKind::CoroutineClosure(..) => "CoroutineClosure",
                                AggregateKind::RawPtr(..) => "RawPtr",
                            };
                            inc(&mut c.aggregates, aks);
                            "Aggregate".to_string()
                        }
                        Rvalue::CopyForDeref(p) => {
                            record_place(c, p);
                            "CopyForDeref".to_string()
                        }
                        Rvalue::WrapUnsafeBinder(op, _) => {
                            record_operand(tcx, c, op);
                            "WrapUnsafeBinder".to_string()
                        }
                        Rvalue::Reborrow(_, m, p) => {
                            record_place(c, p);
                            format!("Reborrow({m:?})")
                        }
                    };
                    inc(&mut c.rvalues, rvk);
                    "Assign"
                }
                StatementKind::FakeRead(box (_, p)) => {
                    record_place(c, p);
                    "FakeRead"
                }
                StatementKind::SetDiscriminant { place, .. } => {
                    record_place(c, place);
                    "SetDiscriminant"
                }
                StatementKind::StorageLive(_) => "StorageLive",
                StatementKind::StorageDead(_) => "StorageDead",
                StatementKind::PlaceMention(box p) => {
                    record_place(c, p);
                    "PlaceMention"
                }
                StatementKind::AscribeUserType(box (p, _), _) => {
                    record_place(c, p);
                    "AscribeUserType"
                }
                StatementKind::Coverage(_) => "Coverage",
                StatementKind::Intrinsic(box ndi) => {
                    let ndis = match ndi {
                        NonDivergingIntrinsic::Assume(op) => {
                            record_operand(tcx, c, op);
                            "Assume"
                        }
                        NonDivergingIntrinsic::CopyNonOverlapping(cno) => {
                            record_operand(tcx, c, &cno.src);
                            record_operand(tcx, c, &cno.dst);
                            record_operand(tcx, c, &cno.count);
                            "CopyNonOverlapping"
                        }
                    };
                    inc(&mut c.nondiverging_intrinsics, ndis);
                    "Intrinsic"
                }
                StatementKind::ConstEvalCounter => "ConstEvalCounter",
                StatementKind::Nop => "Nop",
                StatementKind::BackwardIncompatibleDropHint { place, .. } => {
                    record_place(c, place);
                    "BackwardIncompatibleDropHint"
                }
            };
            inc(&mut c.statements, sk);
        }
        if let Some(term) = &bb.terminator {
            fn record_unwind(c: &mut Counts, u: &UnwindAction) {
                let us = match u {
                    UnwindAction::Continue => "Continue",
                    UnwindAction::Unreachable => "Unreachable",
                    UnwindAction::Terminate(r) => match r {
                        UnwindTerminateReason::Abi => "Terminate(Abi)",
                        UnwindTerminateReason::InCleanup => "Terminate(InCleanup)",
                    },
                    UnwindAction::Cleanup(_) => "Cleanup",
                };
                inc(&mut c.unwind_actions, us);
            }
            let tk = match &term.kind {
                TerminatorKind::Goto { .. } => "Goto",
                TerminatorKind::SwitchInt { discr, .. } => {
                    record_operand(tcx, c, discr);
                    "SwitchInt"
                }
                TerminatorKind::UnwindResume => "UnwindResume",
                TerminatorKind::UnwindTerminate(r) => match r {
                    UnwindTerminateReason::Abi => "UnwindTerminate(Abi)",
                    UnwindTerminateReason::InCleanup => "UnwindTerminate(InCleanup)",
                },
                TerminatorKind::Return => "Return",
                TerminatorKind::Unreachable => "Unreachable",
                TerminatorKind::Drop { place, unwind, .. } => {
                    record_place(c, place);
                    record_unwind(c, unwind);
                    "Drop"
                }
                TerminatorKind::Call { func, args, destination, unwind, .. } => {
                    record_operand(tcx, c, func);
                    for a in args {
                        record_operand(tcx, c, &a.node);
                    }
                    record_place(c, destination);
                    record_unwind(c, unwind);
                    if let Operand::Constant(box co) = func {
                        if let ty::FnDef(def_id, _) = *co.const_.ty().kind() {
                            if tcx.is_intrinsic(def_id, tcx.item_name(def_id)) {
                                inc(&mut c.call_intrinsics, tcx.item_name(def_id).to_string());
                            }
                        }
                    }
                    "Call"
                }
                TerminatorKind::TailCall { func, args, .. } => {
                    record_operand(tcx, c, func);
                    for a in args {
                        record_operand(tcx, c, &a.node);
                    }
                    "TailCall"
                }
                TerminatorKind::Assert { cond, unwind, .. } => {
                    record_operand(tcx, c, cond);
                    record_unwind(c, unwind);
                    "Assert"
                }
                TerminatorKind::Yield { value, resume_arg, .. } => {
                    record_operand(tcx, c, value);
                    record_place(c, resume_arg);
                    "Yield"
                }
                TerminatorKind::CoroutineDrop => "CoroutineDrop",
                TerminatorKind::FalseEdge { .. } => "FalseEdge",
                TerminatorKind::FalseUnwind { unwind, .. } => {
                    record_unwind(c, unwind);
                    "FalseUnwind"
                }
                TerminatorKind::InlineAsm { unwind, .. } => {
                    record_unwind(c, unwind);
                    "InlineAsm"
                }
            };
            inc(&mut c.terminators, tk);
        }
    }
}

fn format_map(m: &BTreeMap<String, usize>) -> String {
    let entries: Vec<String> = m.iter().map(|(k, v)| format!("\"{}\": {}", k, v)).collect();
    format!("{{{}}}", entries.join(", "))
}

fn format_counts(c: &Counts) -> String {
    format!(
        "{{\"bodies\": {}, \"basic_blocks\": {}, \"statements\": {}, \"terminators\": {}, \"unwind_actions\": {}, \"rvalues\": {}, \"operands\": {}, \"projections\": {}, \"casts\": {}, \"binops\": {}, \"unops\": {}, \"aggregates\": {}, \"nondiverging_intrinsics\": {}, \"call_intrinsics\": {}, \"const_kinds\": {}}}",
        c.bodies,
        c.basic_blocks,
        format_map(&c.statements),
        format_map(&c.terminators),
        format_map(&c.unwind_actions),
        format_map(&c.rvalues),
        format_map(&c.operands),
        format_map(&c.projections),
        format_map(&c.casts),
        format_map(&c.binops),
        format_map(&c.unops),
        format_map(&c.aggregates),
        format_map(&c.nondiverging_intrinsics),
        format_map(&c.call_intrinsics),
        format_map(&c.const_kinds),
    )
}

impl Callbacks for CensusCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let mut pc_counts = Counts::default();
        let mut opt_counts = Counts::default();
        for def_id in tcx.hir_body_owners() {
            let kind = tcx.def_kind(def_id);
            if matches!(kind, DefKind::Fn | DefKind::AssocFn | DefKind::Closure) {
                if tcx.is_mir_available(def_id) {
                    let steal = tcx.mir_drops_elaborated_and_const_checked(def_id);
                    if !steal.is_stolen() {
                        let body = steal.borrow();
                        walk_body(tcx, &mut pc_counts, &body);
                    }
                }
            }
        }
        for def_id in tcx.hir_body_owners() {
            let kind = tcx.def_kind(def_id);
            if matches!(kind, DefKind::Fn | DefKind::AssocFn | DefKind::Closure) {
                if tcx.is_mir_available(def_id) {
                    let body = tcx.optimized_mir(def_id);
                    walk_body(tcx, &mut opt_counts, body);
                }
            }
        }
        let json = format!(
            "{{\"crate\": \"{}\", \"postcleanup\": {}, \"optimized\": {}}}",
            self.crate_name,
            format_counts(&pc_counts),
            format_counts(&opt_counts)
        );
        std::fs::write(&self.out_path, json).unwrap();
        Compilation::Stop
    }
}

fn main() {
    let mut args: Vec<String> = std::env::args().collect();
    let out_idx = args.iter().position(|a| a == "--census-out").unwrap();
    let out_path = args.remove(out_idx + 1);
    args.remove(out_idx);
    let crate_idx = args.iter().position(|a| a == "--census-crate").unwrap();
    let crate_name = args.remove(crate_idx + 1);
    args.remove(crate_idx);

    let mut cb = CensusCallbacks { crate_name, out_path };
    rustc_driver::run_compiler(&args, &mut cb);
}
