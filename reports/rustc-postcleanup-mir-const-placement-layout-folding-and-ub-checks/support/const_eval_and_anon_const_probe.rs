#![feature(rustc_private)]
#![allow(dead_code)]

extern crate rustc_abi;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use std::collections::{BTreeMap, HashMap};
use std::sync::Mutex;

use rustc_data_structures::steal::Steal;
use rustc_hir as hir;
use rustc_hir::def::DefKind;
use rustc_hir::intravisit::{self, Visitor as HirVisitor};
use rustc_interface::interface;
use rustc_middle::mir::interpret::Scalar;
use rustc_middle::mir::{
    self, Body, Const, ConstValue, NonDivergingIntrinsic, Operand, Rvalue, StatementKind,
    TerminatorKind,
};
use rustc_middle::ty::{self, GenericArgsRef, InstanceKind, Ty, TyCtxt};
use rustc_middle::util::Providers;
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::{DUMMY_SP, Span};

// ============================================================================
// Hook storage: capture PostCleanup MIR before `optimized_mir` steals it
// ============================================================================

static POSTCLEANUP_MIR: Mutex<Option<BTreeMap<u32, String>>> = Mutex::new(None);

fn override_queries(_sess: &rustc_session::Session, local: &mut Providers) {
    local.queries.mir_drops_elaborated_and_const_checked = postcleanup_hook;
}

fn postcleanup_hook(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
) -> &Steal<Body<'_>> {
    let steal = (rustc_interface::DEFAULT_QUERY_PROVIDERS
        .queries
        .mir_drops_elaborated_and_const_checked)(tcx, def);
    let body = steal.borrow();
    let dump = dump_body_summary(tcx, def, &body);
    if let Some(map) = POSTCLEANUP_MIR.lock().unwrap().as_mut() {
        map.insert(def.local_def_index.as_u32(), dump);
    }
    steal
}

fn dump_body_summary<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId, body: &Body<'tcx>) -> String {
    let mut out = String::new();
    let path = tcx.def_path_str(def);
    let kind = tcx.def_kind(def);
    let generics = tcx.generics_of(def);
    out.push_str(&format!(
        "=== PostCleanup Body: `{path}` (DefIdx={}, kind={kind:?}) ===\n",
        def.local_def_index.as_u32()
    ));
    out.push_str(&format!(
        "  generics: parent={:?}, parent_count={}, own_params={:?}\n",
        generics.parent,
        generics.parent_count,
        generics
            .own_params
            .iter()
            .map(|p| format!("{}:{}:{:?}", p.index, p.name, p.kind))
            .collect::<Vec<_>>()
    ));
    out.push_str(&format!("   phase: {:?}\n", body.phase));
    let req_consts: Vec<String> = body
        .required_consts()
        .iter()
        .map(|c| format!("{:?} (span={:?})", c.const_, c.span))
        .collect();
    out.push_str(&format!("  required_consts: {:?}\n", req_consts));
    for (local, decl) in body.local_decls.iter_enumerated() {
        out.push_str(&format!(
            "  local {local:?}: ty={:?} (kind={:?}), span={:?}, user_ty={:?}\n",
            decl.ty,
            decl.ty.kind(),
            decl.source_info.span,
            decl.user_ty.is_some()
        ));
    }
    for (bb, blk) in body.basic_blocks.iter_enumerated() {
        out.push_str(&format!("  {bb:?}:\n"));
        for (si, stmt) in blk.statements.iter().enumerate() {
            out.push_str(&format!(
                "    stmt[{si}] (span={:?}): {:?}\n",
                stmt.source_info.span, stmt.kind
            ));
        }
        if let Some(term) = &blk.terminator {
            out.push_str(&format!(
                "    term (span={:?}): {:?}\n",
                term.source_info.span, term.kind
            ));
        }
    }
    out
}

// ============================================================================
// Prototype IR & Extraction for Deliverables 1, 2, 3
// ============================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
enum ProtoTy {
    Usize,
    Isize,
    Uint(u8),
    Int(u8),
    Bool,
    Char,
    Unit,
    ByteArray(u64),
    ArraySizeOf(Box<ProtoTy>, Box<ProtoTy>),
    Ref(Box<ProtoTy>),
    RefMut(Box<ProtoTy>),
    RawPtr(String, Box<ProtoTy>),
    Adt(String),
    Tuple(Vec<ProtoTy>),
    Param(u32, String),
    Unmodeled(String),
}

impl ProtoTy {
    fn subst(&self, args: &[ProtoTy]) -> ProtoTy {
        match self {
            ProtoTy::Param(i, _) => args.get(*i as usize).cloned().unwrap_or_else(|| self.clone()),
            ProtoTy::ArraySizeOf(elem, sized) => ProtoTy::ArraySizeOf(
                Box::new(elem.subst(args)),
                Box::new(sized.subst(args)),
            ),
            ProtoTy::Ref(t) => ProtoTy::Ref(Box::new(t.subst(args))),
            ProtoTy::RefMut(t) => ProtoTy::RefMut(Box::new(t.subst(args))),
            ProtoTy::RawPtr(m, t) => ProtoTy::RawPtr(m.clone(), Box::new(t.subst(args))),
            ProtoTy::Tuple(ts) => ProtoTy::Tuple(ts.iter().map(|t| t.subst(args)).collect()),
            _ => self.clone(),
        }
    }

    fn pointee(&self) -> Option<&ProtoTy> {
        match self {
            ProtoTy::Ref(t) | ProtoTy::RefMut(t) | ProtoTy::RawPtr(_, t) => Some(t),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum AnonLenClass {
    /// `AnonConst` body is a pure `core::mem::size_of::<TargetTy>()` call.
    PureSizeOf(ProtoTy),
    /// `AnonConst` body is a layout-independent constant expression (no `size_of`/`align_of`/`offset_of` or ADTs).
    LayoutIndependentLiteral(u64),
    /// `AnonConst` body depends on layout in a compound expression (e.g. `size_of::<T>() + 1`) — must fail closed!
    UnsupportedLayoutDependent(String),
}

#[derive(Clone, Debug)]
enum ProtoLayoutQuery {
    SizeOf(ProtoTy),
    AlignOf(ProtoTy),
    OffsetOf {
        container_ty: ProtoTy,
        variant_idx: u32,
        field_idx: u32,
    },
}

#[derive(Clone, Debug)]
enum ProtoStmt {
    Assign(String, String),
    Repeat {
        dst: String,
        op: String,
        len: u64,
    },
    RepeatSizeOf {
        dst: String,
        op: String,
        sized_ty: ProtoTy,
    },
    EvalConst {
        dst: String,
        const_def: u32,
        const_path: String,
        type_args: Vec<ProtoTy>,
        dst_ty: ProtoTy,
    },
    EvalForeignCoreConst {
        dst: String,
        const_path: String,
        folded_val: String,
        dst_ty: ProtoTy,
    },
    AssignRuntimeCheck {
        dst: String,
        check: String,
    },
    CopyNonOverlapping {
        src: String,
        dst: String,
        count: String,
    },
    Other(String),
}

#[derive(Clone, Debug)]
enum ProtoTerm {
    CallLayout {
        dst: String,
        query: ProtoLayoutQuery,
        target: u32,
    },
    TransmuteCopy {
        dst: String,
        src_ty: ProtoTy,
        dst_ty: ProtoTy,
        op: String,
        target: u32,
    },
    Return,
    Other(String),
}

fn translate_ty<'tcx>(tcx: TyCtxt<'tcx>, t: Ty<'tcx>) -> ProtoTy {
    match *t.kind() {
        ty::Uint(ty::UintTy::Usize) => ProtoTy::Usize,
        ty::Int(ty::IntTy::Isize) => ProtoTy::Isize,
        ty::Uint(u) => ProtoTy::Uint(u.bit_width().unwrap() as u8),
        ty::Int(i) => ProtoTy::Int(i.bit_width().unwrap() as u8),
        ty::Bool => ProtoTy::Bool,
        ty::Char => ProtoTy::Char,
        ty::Tuple(ts) if ts.is_empty() => ProtoTy::Unit,
        ty::Tuple(ts) => ProtoTy::Tuple(ts.iter().map(|elem| translate_ty(tcx, elem)).collect()),
        ty::Array(elem, len) => {
            if *elem.kind() == ty::Uint(ty::UintTy::U8)
                && let Some(n) = len.try_to_target_usize(tcx)
            {
                ProtoTy::ByteArray(n)
            } else {
                ProtoTy::Unmodeled(format!("Array({elem:?}, {len:?})"))
            }
        }
        ty::Ref(_, inner, hir::Mutability::Not) => {
            ProtoTy::Ref(Box::new(translate_ty(tcx, inner)))
        }
        ty::Ref(_, inner, hir::Mutability::Mut) => {
            ProtoTy::RefMut(Box::new(translate_ty(tcx, inner)))
        }
        ty::RawPtr(inner, mutbl) => {
            ProtoTy::RawPtr(format!("{mutbl:?}"), Box::new(translate_ty(tcx, inner)))
        }
        ty::Adt(adt_def, args) if adt_def.is_struct() && args.is_empty() => {
            ProtoTy::Adt(tcx.def_path_str(adt_def.did()))
        }
        ty::Param(p) => ProtoTy::Param(p.index, p.name.to_string()),
        _ => ProtoTy::Unmodeled(format!("{t:?}")),
    }
}

fn unwrap_fn_def_args<'tcx>(
    #[cfg(not(rustc_1_101))] args: GenericArgsRef<'tcx>,
    #[cfg(rustc_1_101)] args: ty::Binder<'tcx, GenericArgsRef<'tcx>>,
) -> GenericArgsRef<'tcx> {
    #[cfg(not(rustc_1_101))]
    {
        args
    }
    #[cfg(rustc_1_101)]
    {
        args.skip_binder()
    }
}

// ============================================================================
// Deliverable 2 Prototype: Classify `DefKind::AnonConst` via `mir_for_ctfe`
// ============================================================================

fn classify_anon_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    anon_def: LocalDefId,
    evaluated_len: Option<u64>,
) -> AnonLenClass {
    // 1. Fast path: `tcx.is_trivial_const(anon_def)` means the body is a pure
    //    literal assignment `_0 = const Val; return;` (and `mir_for_ctfe` is bypassed).
    if tcx.is_trivial_const(anon_def) {
        if let Some(n) = evaluated_len {
            return AnonLenClass::LayoutIndependentLiteral(n);
        }
    }

    // 2. Non-trivial `AnonConst`: inspect `tcx.mir_for_ctfe(anon_def.to_def_id())`.
    //    Note: `mir_built` and `mir_drops_elaborated_and_const_checked` for `anon_def`
    //    are stolen during typecheck when `rustc` evaluates the array length, whereas
    //    `mir_for_ctfe` returns `&'tcx Body<'tcx>` and remains intact!
    let body = tcx.mir_for_ctfe(anon_def.to_def_id());

    // Pattern A: Pure `core::mem::size_of::<TargetTy>()` call:
    //   bb0 has no value-modifying statements before terminator `Call` to `size_of::<TargetTy>()`
    //   writing directly to `_0` and jumping to `bb1: Return`.
    if body.basic_blocks.len() == 2 {
        let bb0 = &body.basic_blocks[mir::BasicBlock::from_u32(0)];
        let bb1 = &body.basic_blocks[mir::BasicBlock::from_u32(1)];
        let only_storage_stmts = bb0.statements.iter().all(|s| {
            matches!(
                s.kind,
                StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::ConstEvalCounter
                    | StatementKind::Nop
            )
        });
        if only_storage_stmts
            && let Some(term0) = &bb0.terminator
            && let TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(t_bb),
                ..
            } = &term0.kind
            && t_bb.as_u32() == 1
            && destination.local.as_u32() == 0
            && destination.projection.is_empty()
            && args.is_empty()
            && let Some(term1) = &bb1.terminator
            && matches!(term1.kind, TerminatorKind::Return)
            && let ty::FnDef(callee_def, raw_callee_args) = *func.ty(&body.local_decls, tcx).kind()
        {
            let callee_args = unwrap_fn_def_args(raw_callee_args);
            if is_core_mem_size_of(tcx, callee_def)
                && callee_args.len() == 1
                && let Some(arg_ty) = callee_args[0].as_type()
            {
                return AnonLenClass::PureSizeOf(translate_ty(tcx, arg_ty));
            }
        }
    }

    // Pattern B: Check whether the `AnonConst` body mentions any layout query
    // (`size_of`, `align_of`, `offset_of`) or any `Const::Unevaluated`.
    for blk in body.basic_blocks.iter() {
        for stmt in &blk.statements {
            if let StatementKind::Assign(b) = &stmt.kind
                && rvalue_mentions_unevaluated(&b.1)
            {
                return AnonLenClass::UnsupportedLayoutDependent(format!(
                    "AnonConst contains Const::Unevaluated in statement: {:?}",
                    stmt.kind
                ));
            }
        }
        if let Some(term) = &blk.terminator {
            if let TerminatorKind::Call { func, .. } = &term.kind {
                return AnonLenClass::UnsupportedLayoutDependent(format!(
                    "AnonConst contains non-pure function call: {:?}",
                    func
                ));
            }
        }
    }

    if let Some(n) = evaluated_len {
        AnonLenClass::LayoutIndependentLiteral(n)
    } else {
        AnonLenClass::UnsupportedLayoutDependent("unable to evaluate literal length".into())
    }
}

fn rvalue_mentions_unevaluated<'tcx>(rv: &Rvalue<'tcx>) -> bool {
    let op_uneval =
        |op: &Operand<'tcx>| matches!(op, Operand::Constant(c) if matches!(c.const_, Const::Unevaluated(..)));
    match rv {
        Rvalue::Use(op, ..) | Rvalue::Repeat(op, _) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(_, op, _) => {
            op_uneval(op)
        }
        Rvalue::BinaryOp(_, b) => op_uneval(&b.0) || op_uneval(&b.1),
        _ => false,
    }
}

fn is_core_mem_size_of(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let p = tcx.def_path_str(def_id);
    p.ends_with("mem::size_of") || p.ends_with("intrinsics::size_of")
}

fn is_core_mem_align_of(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let p = tcx.def_path_str(def_id);
    p.ends_with("mem::align_of")
        || p.ends_with("intrinsics::align_of")
        || p.ends_with("intrinsics::min_align_of")
}

fn is_core_intrinsics_offset_of(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.def_path_str(def_id).ends_with("intrinsics::offset_of")
}

fn is_core_mem_transmute_copy(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.def_path_str(def_id).ends_with("mem::transmute_copy")
}

// ============================================================================
// HIR Visitor to collect `AnonConst` array lengths and `OffsetOf` expressions
// ============================================================================

struct HirCorrelationCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx ty::TypeckResults<'tcx>,
    /// Span of `hir::ExprKind::Repeat` -> classified `AnonConst`
    repeat_expr_spans: HashMap<Span, (LocalDefId, AnonLenClass)>,
    /// Span of `hir::LetStmt.ty` -> translated `ProtoTy` (with `ArraySizeOf` if present)
    let_pat_spans: HashMap<Span, ProtoTy>,
    /// HIR `offset_of!` expressions discovered via `hir::ExprKind::OffsetOf` + `typeck.offset_of_data()`
    offset_of_exprs: Vec<(Span, String, Vec<(ProtoTy, u32, u32)>)>,
    /// All `AnonConst` items visited inside this body
    anon_consts: Vec<(LocalDefId, Span, AnonLenClass, String)>,
}

impl<'tcx> HirCorrelationCollector<'tcx> {
    fn translate_hir_ty(&mut self, hir_ty: &'tcx hir::Ty<'tcx>, mid_ty: Ty<'tcx>) -> ProtoTy {
        match (&hir_ty.kind, mid_ty.kind()) {
            (hir::TyKind::Array(elem_hir, const_arg), ty::Array(elem_mid, len_const)) => {
                let elem_proto = self.translate_hir_ty(elem_hir, *elem_mid);
                let eval_len = len_const.try_to_target_usize(self.tcx);
                if let hir::ConstArgKind::Anon(anon) = &const_arg.kind {
                    let class = classify_anon_const(self.tcx, anon.def_id, eval_len);
                    let ctfe_mir = self.tcx.mir_for_ctfe(anon.def_id.to_def_id());
                    let summary = dump_body_summary(self.tcx, anon.def_id, ctfe_mir);
                    self.anon_consts
                        .push((anon.def_id, hir_ty.span, class.clone(), summary));
                    match class {
                        AnonLenClass::PureSizeOf(sized_ty) => {
                            return ProtoTy::ArraySizeOf(
                                Box::new(elem_proto),
                                Box::new(sized_ty),
                            );
                        }
                        AnonLenClass::LayoutIndependentLiteral(n)
                            if elem_proto == ProtoTy::Uint(8) =>
                        {
                            return ProtoTy::ByteArray(n);
                        }
                        AnonLenClass::UnsupportedLayoutDependent(reason) => {
                            return ProtoTy::Unmodeled(format!(
                                "FAIL_CLOSED_ARRAY_LEN({reason})"
                            ));
                        }
                        _ => {}
                    }
                }
                translate_ty(self.tcx, mid_ty)
            }
            #[cfg(not(rustc_1_101))]
            (hir::TyKind::Ref(_, mut_ty), ty::Ref(_, inner_mid, hir::Mutability::Not)) => {
                ProtoTy::Ref(Box::new(self.translate_hir_ty(mut_ty.ty, *inner_mid)))
            }
            #[cfg(rustc_1_101)]
            (hir::TyKind::Ref(_, inner_hir, _), ty::Ref(_, inner_mid, hir::Mutability::Not)) => {
                ProtoTy::Ref(Box::new(self.translate_hir_ty(inner_hir, *inner_mid)))
            }
            #[cfg(not(rustc_1_101))]
            (hir::TyKind::Ref(_, mut_ty), ty::Ref(_, inner_mid, hir::Mutability::Mut)) => {
                ProtoTy::RefMut(Box::new(self.translate_hir_ty(mut_ty.ty, *inner_mid)))
            }
            #[cfg(rustc_1_101)]
            (hir::TyKind::Ref(_, inner_hir, _), ty::Ref(_, inner_mid, hir::Mutability::Mut)) => {
                ProtoTy::RefMut(Box::new(self.translate_hir_ty(inner_hir, *inner_mid)))
            }
            #[cfg(not(rustc_1_101))]
            (hir::TyKind::Ptr(mut_ty), ty::RawPtr(inner_mid, mutbl)) => ProtoTy::RawPtr(
                format!("{mutbl:?}"),
                Box::new(self.translate_hir_ty(mut_ty.ty, *inner_mid)),
            ),
            #[cfg(rustc_1_101)]
            (hir::TyKind::Ptr(inner_hir, _), ty::RawPtr(inner_mid, mutbl)) => ProtoTy::RawPtr(
                format!("{mutbl:?}"),
                Box::new(self.translate_hir_ty(inner_hir, *inner_mid)),
            ),
            _ => translate_ty(self.tcx, mid_ty),
        }
    }
}

impl<'tcx> HirVisitor<'tcx> for HirCorrelationCollector<'tcx> {
    fn visit_stmt(&mut self, s: &'tcx hir::Stmt<'tcx>) {
        if let hir::StmtKind::Let(let_stmt) = s.kind
            && let Some(hir_ty) = let_stmt.ty
        {
            let mid_ty = self.typeck.node_type(let_stmt.hir_id);
            let proto_ty = self.translate_hir_ty(hir_ty, mid_ty);
            self.let_pat_spans.insert(let_stmt.pat.span, proto_ty);
        }
        intravisit::walk_stmt(self, s);
    }

    fn visit_expr(&mut self, ex: &'tcx hir::Expr<'tcx>) {
        match &ex.kind {
            hir::ExprKind::Repeat(_elem, const_arg) => {
                let expr_ty = self.typeck.expr_ty(ex);
                let eval_len = if let ty::Array(_, len_c) = expr_ty.kind() {
                    len_c.try_to_target_usize(self.tcx)
                } else {
                    None
                };
                if let hir::ConstArgKind::Anon(anon) = &const_arg.kind {
                    let class = classify_anon_const(self.tcx, anon.def_id, eval_len);
                    let ctfe_mir = self.tcx.mir_for_ctfe(anon.def_id.to_def_id());
                    let summary = dump_body_summary(self.tcx, anon.def_id, ctfe_mir);
                    self.anon_consts
                        .push((anon.def_id, ex.span, class.clone(), summary));
                    self.repeat_expr_spans
                        .insert(ex.span.source_callsite(), (anon.def_id, class));
                }
            }
            hir::ExprKind::OffsetOf(container_hir_ty, fields) => {
                let field_names: Vec<String> = fields.iter().map(|f| f.name.to_string()).collect();
                let mut steps = Vec::new();
                if let Some(indices) = self.typeck.offset_of_data().get(ex.hir_id) {
                    for &(container_ty, variant_idx, field_idx) in indices.iter() {
                        steps.push((
                            translate_ty(self.tcx, container_ty),
                            variant_idx.as_u32(),
                            field_idx.as_u32(),
                        ));
                    }
                }
                self.offset_of_exprs.push((
                    ex.span,
                    format!("offset_of!({:?}, {})", container_hir_ty.span, field_names.join(".")),
                    steps,
                ));
            }
            hir::ExprKind::ConstBlock(const_block) => {
                // Also traverse into nested `const { ... }` blocks (such as `offset_of!` expansion!)
                let nested_body = self.tcx.hir_body(const_block.body);
                let nested_typeck = self.tcx.typeck(const_block.def_id);
                let prev_typeck = self.typeck;
                self.typeck = nested_typeck;
                self.visit_body(nested_body);
                self.typeck = prev_typeck;
            }
            _ => {}
        }
        intravisit::walk_expr(self, ex);
    }
}

// ============================================================================
// Deliverable 1, 2, 3 Unified Prototype Extractor on PostCleanup MIR
// ============================================================================

fn resolve_unevaluated_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    uv: mir::UnevaluatedConst<'tcx>,
) -> Result<(DefId, GenericArgsRef<'tcx>, Vec<ProtoTy>), String> {
    let instance = match ty::Instance::try_resolve(tcx, typing_env, uv.def, uv.args) {
        Ok(Some(inst)) if matches!(inst.def, InstanceKind::Item(_)) => inst,
        _ => return Err(format!("could not resolve constant {:?}", uv.def)),
    };
    let target = instance.def_id();
    let mut raw_args: Vec<ty::GenericArg<'tcx>> = instance.args.iter().collect();

    // Check if `target` is an inline `const { ... }` block across both 1.98 (`DefKind::InlineConst`)
    // and 1.101 (`DefKind::AnonConst` with `Node::ConstBlock` / `sym::const_ty_placeholder`).
    let is_inline_const_block = tcx
        .generics_of(target)
        .own_params
        .last()
        .is_some_and(|p| p.name == rustc_span::sym::const_ty_placeholder);
    if is_inline_const_block {
        // Inline `const { ... }` block: `own_params` has a trailing synthetic `<const_ty>`
        // parameter at index `parent_count`. Pop it so `type_args` matches `0..parent_count`.
        raw_args.pop();
    }

    let mut type_args = Vec::with_capacity(raw_args.len());
    for arg in raw_args {
        let Some(t) = arg.as_type() else {
            return Err(format!("non-type generic arg {arg:?} on constant {target:?}"));
        };
        type_args.push(translate_ty(tcx, t));
    }
    Ok((target, instance.args, type_args))
}

fn extract_const_scalar<'tcx>(tcx: TyCtxt<'tcx>, c: &Const<'tcx>) -> String {
    let ty = translate_ty(tcx, c.ty());
    match c {
        Const::Val(ConstValue::Scalar(Scalar::Int(int)), _) => match ty {
            ProtoTy::Usize
            | ProtoTy::Isize
            | ProtoTy::Uint(_)
            | ProtoTy::Int(_)
            | ProtoTy::Char => {
                format!("Val::Usize({})", int.to_bits(int.size()))
            }
            ProtoTy::Bool => format!("Val::Bool({})", int.to_bits(int.size()) != 0),
            _ => format!("Val::Uninit(ty={ty:?})"),
        },
        Const::Val(ConstValue::ZeroSized, _) if ty == ProtoTy::Unit => "Val::Unit".into(),
        _ => format!("Val::Other({c:?})"),
    }
}

fn run_prototype_extractions<'tcx>(tcx: TyCtxt<'tcx>) -> (String, String) {
    let mut out = String::new();
    let mut json_entries = Vec::new();
    out.push_str("\n====================================================================\n");
    out.push_str("PROTOTYPE EXTRACTOR RESULTS FOR DELIVERABLES 1, 2, AND 3\n");
    out.push_str("====================================================================\n");

    for def in tcx.hir_body_owners() {
        let path = tcx.def_path_str(def);
        let kind = tcx.def_kind(def);
        if matches!(kind, DefKind::AnonConst)
            && !matches!(tcx.hir_node_by_def_id(def), hir::Node::ConstBlock(_))
        {
            // Array-length `AnonConst` bodies are inspected through their parent function/item.
            continue;
        }
        let is_const_body = !matches!(kind, DefKind::Fn);

        let body_guard;
        let body: &Body<'tcx> = if is_const_body && tcx.is_trivial_const(def) {
            body_guard = tcx.mir_drops_elaborated_and_const_checked(def).borrow();
            &body_guard
        } else if is_const_body {
            tcx.mir_for_ctfe(def.to_def_id())
        } else {
            body_guard = tcx.mir_drops_elaborated_and_const_checked(def).borrow();
            &body_guard
        };

        let typeck = tcx.typeck(def);
        let mut hir_collector = HirCorrelationCollector {
            tcx,
            typeck,
            repeat_expr_spans: HashMap::new(),
            let_pat_spans: HashMap::new(),
            offset_of_exprs: Vec::new(),
            anon_consts: Vec::new(),
        };
        if let Some(body_id) = tcx.hir_node_by_def_id(def).body_id() {
            hir_collector.visit_body(tcx.hir_body(body_id));
        }

        // Step 1: Translate local_decls, refining signature types (`_0..=arg_count`) from HIR `fn_decl`
        // and `let` binding types from `let_pat_spans`.
        let mut local_tys: Vec<ProtoTy> = body
            .local_decls
            .iter()
            .map(|d| translate_ty(tcx, d.ty))
            .collect();

        if let Some(fn_decl) = tcx.hir_node_by_def_id(def).fn_decl() {
            let sig = tcx.fn_sig(def).skip_binder().skip_binder();
            if let hir::FnRetTy::Return(ret_hir_ty) = fn_decl.output {
                local_tys[0] = hir_collector.translate_hir_ty(ret_hir_ty, sig.output());
            }
            for (i, (inp_hir, inp_mid)) in fn_decl.inputs.iter().zip(sig.inputs().iter()).enumerate()
            {
                local_tys[i + 1] = hir_collector.translate_hir_ty(inp_hir, *inp_mid);
            }
        }

        for (local, decl) in body.local_decls.iter_enumerated() {
            if let Some(refined) = hir_collector.let_pat_spans.get(&decl.source_info.span) {
                local_tys[local.as_usize()] = refined.clone();
            }
        }

        // Step 2: Walk MIR basic blocks and extract statements & terminators.
        let typing_env = body.typing_env(tcx);
        let mut proto_stmts = Vec::new();
        let mut proto_terms = Vec::new();
        let mut required_layouts = Vec::new();

        for (bb, blk) in body.basic_blocks.iter_enumerated() {
            for stmt in &blk.statements {
                match &stmt.kind {
                    StatementKind::Assign(b) => {
                        let (dst, rv) = &**b;
                        match rv {
                            // Value-producing or unit `Stmt::EvalConst`
                            Rvalue::Use(Operand::Constant(c), ..)
                                if let Const::Unevaluated(uv, c_ty) = c.const_ =>
                            {
                                let dst_ty = translate_ty(tcx, c_ty);
                                match resolve_unevaluated_const(tcx, typing_env, uv) {
                                    Ok((target_def, inst_args, type_args)) => {
                                        if let Some(local_def) = target_def.as_local() {
                                            proto_stmts.push((
                                                bb.as_u32(),
                                                ProtoStmt::EvalConst {
                                                    dst: format!("{dst:?}"),
                                                    const_def: local_def.local_def_index.as_u32(),
                                                    const_path: tcx.def_path_str(target_def),
                                                    type_args,
                                                    dst_ty,
                                                },
                                            ));
                                        } else if tcx.crate_name(target_def.krate).as_str()
                                            == "core"
                                            && inst_args.is_empty()
                                        {
                                            let inst = ty::Instance::new_raw(target_def, inst_args);
                                            let val_str = match tcx.const_eval_instance(
                                                typing_env,
                                                inst,
                                                DUMMY_SP,
                                            ) {
                                                Ok(ConstValue::Scalar(Scalar::Int(int))) => {
                                                    format!(
                                                        "Val::Usize({})",
                                                        int.to_bits(int.size())
                                                    )
                                                }
                                                other => format!("{other:?}"),
                                            };
                                            proto_stmts.push((
                                                bb.as_u32(),
                                                ProtoStmt::EvalForeignCoreConst {
                                                    dst: format!("{dst:?}"),
                                                    const_path: tcx.def_path_str(target_def),
                                                    folded_val: val_str,
                                                    dst_ty,
                                                },
                                            ));
                                        }
                                    }
                                    Err(e) => {
                                        proto_stmts.push((
                                            bb.as_u32(),
                                            ProtoStmt::Other(format!("ERR: {e}")),
                                        ));
                                    }
                                }
                            }
                            // `Operand::RuntimeChecks(RuntimeChecks::UbChecks)`
                            Rvalue::Use(Operand::RuntimeChecks(chk), ..) => {
                                proto_stmts.push((
                                    bb.as_u32(),
                                    ProtoStmt::AssignRuntimeCheck {
                                        dst: format!("{dst:?}"),
                                        check: format!("{chk:?}"),
                                    },
                                ));
                            }
                            // `Rvalue::Repeat(op, len)` correlated with HIR `ExprKind::Repeat`
                            Rvalue::Repeat(op, len_c) => {
                                let callsite = stmt.source_info.span.source_callsite();
                                let op_str = match op {
                                    Operand::Constant(c) => extract_const_scalar(tcx, &c.const_),
                                    other => format!("{other:?}"),
                                };
                                if let Some((_anon_def, class)) =
                                    hir_collector.repeat_expr_spans.get(&callsite)
                                {
                                    match class {
                                        AnonLenClass::PureSizeOf(sized_ty) => {
                                            if dst.projection.is_empty() {
                                                let elem_ty =
                                                    match &local_tys[dst.local.as_usize()] {
                                                        ProtoTy::ByteArray(_) => ProtoTy::Uint(8),
                                                        other => other.clone(),
                                                    };
                                                local_tys[dst.local.as_usize()] =
                                                    ProtoTy::ArraySizeOf(
                                                        Box::new(elem_ty),
                                                        Box::new(sized_ty.clone()),
                                                    );
                                            }
                                            proto_stmts.push((
                                                bb.as_u32(),
                                                ProtoStmt::RepeatSizeOf {
                                                    dst: format!("{dst:?}"),
                                                    op: op_str,
                                                    sized_ty: sized_ty.clone(),
                                                },
                                            ));
                                        }
                                        AnonLenClass::LayoutIndependentLiteral(n) => {
                                            proto_stmts.push((
                                                bb.as_u32(),
                                                ProtoStmt::Repeat {
                                                    dst: format!("{dst:?}"),
                                                    op: op_str,
                                                    len: *n,
                                                },
                                            ));
                                        }
                                        AnonLenClass::UnsupportedLayoutDependent(reason) => {
                                            proto_stmts.push((
                                                bb.as_u32(),
                                                ProtoStmt::Other(format!(
                                                    "FAIL_CLOSED_REPEAT_LEN: {reason}"
                                                )),
                                            ));
                                        }
                                    }
                                } else if let Some(n) = len_c.try_to_target_usize(tcx) {
                                    proto_stmts.push((
                                        bb.as_u32(),
                                        ProtoStmt::Repeat {
                                            dst: format!("{dst:?}"),
                                            op: op_str,
                                            len: n,
                                        },
                                    ));
                                }
                            }
                            // Propagate `ArraySizeOf` across `&place`, `&mut place`, `&raw const/mut place`, and `Use(Copy/Move(place))`
                            _ => {
                                if dst.projection.is_empty() {
                                    match rv {
                                        Rvalue::Ref(_, bk, place) => {
                                            let base_ty = &local_tys[place.local.as_usize()];
                                            let target_ty = if place.projection.len() == 1
                                                && matches!(
                                                    place.projection[0],
                                                    mir::ProjectionElem::Deref
                                                ) {
                                                base_ty.pointee().cloned()
                                            } else if place.projection.is_empty() {
                                                Some(base_ty.clone())
                                            } else {
                                                None
                                            };
                                            if let Some(inner) = target_ty
                                                && matches!(inner, ProtoTy::ArraySizeOf(..))
                                            {
                                                local_tys[dst.local.as_usize()] = if matches!(
                                                    bk,
                                                    mir::BorrowKind::Mut { .. }
                                                ) {
                                                    ProtoTy::RefMut(Box::new(inner))
                                                } else {
                                                    ProtoTy::Ref(Box::new(inner))
                                                };
                                            }
                                        }
                                        Rvalue::RawPtr(kind, place) => {
                                            let base_ty = &local_tys[place.local.as_usize()];
                                            let target_ty = if place.projection.len() == 1
                                                && matches!(
                                                    place.projection[0],
                                                    mir::ProjectionElem::Deref
                                                ) {
                                                base_ty.pointee().cloned()
                                            } else if place.projection.is_empty() {
                                                Some(base_ty.clone())
                                            } else {
                                                None
                                            };
                                            if let Some(inner) = target_ty
                                                && matches!(inner, ProtoTy::ArraySizeOf(..))
                                            {
                                                local_tys[dst.local.as_usize()] = ProtoTy::RawPtr(
                                                    format!("{kind:?}"),
                                                    Box::new(inner),
                                                );
                                            }
                                        }
                                        Rvalue::Use(
                                            Operand::Copy(place) | Operand::Move(place),
                                            ..,
                                        ) if place.projection.is_empty() => {
                                            if matches!(
                                                local_tys[place.local.as_usize()],
                                                ProtoTy::ArraySizeOf(..)
                                                    | ProtoTy::Ref(_)
                                                    | ProtoTy::RefMut(_)
                                            ) {
                                                local_tys[dst.local.as_usize()] =
                                                    local_tys[place.local.as_usize()].clone();
                                            }
                                        }
                                        _ => {}
                                    }
                                }

                                if let Rvalue::BinaryOp(_, bin_ops) = rv {
                                    for op in [&bin_ops.0, &bin_ops.1] {
                                        if let Operand::Constant(c) = op
                                            && let Const::Unevaluated(uv, c_ty) = c.const_
                                            && let Ok((target_def, _inst_args, type_args)) =
                                                resolve_unevaluated_const(tcx, typing_env, uv)
                                            && let Some(local_def) = target_def.as_local()
                                        {
                                            proto_stmts.push((
                                                bb.as_u32(),
                                                ProtoStmt::EvalConst {
                                                    dst: format!("LIFTED_TMP_FOR_{dst:?}"),
                                                    const_def: local_def.local_def_index.as_u32(),
                                                    const_path: tcx.def_path_str(target_def),
                                                    type_args,
                                                    dst_ty: translate_ty(tcx, c_ty),
                                                },
                                            ));
                                        }
                                    }
                                }

                                if let Rvalue::Use(Operand::Constant(c), ..) = rv {
                                    proto_stmts.push((
                                        bb.as_u32(),
                                        ProtoStmt::Assign(
                                            format!("{dst:?}"),
                                            extract_const_scalar(tcx, &c.const_),
                                        ),
                                    ));
                                }
                            }
                        }
                    }
                    StatementKind::Intrinsic(intr) => {
                        if let NonDivergingIntrinsic::CopyNonOverlapping(c) = &**intr {
                            proto_stmts.push((
                                bb.as_u32(),
                                ProtoStmt::CopyNonOverlapping {
                                    src: format!("{:?}", c.src),
                                    dst: format!("{:?}", c.dst),
                                    count: format!("{:?}", c.count),
                                },
                            ));
                        }
                    }
                    _ => {}
                }
            }

            if let Some(term) = &blk.terminator {
                match &term.kind {
                    TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        target: Some(t_bb),
                        ..
                    } => {
                        if let ty::FnDef(callee_def, raw_callee_args) =
                            *func.ty(&body.local_decls, tcx).kind()
                        {
                            let callee_args = unwrap_fn_def_args(raw_callee_args);
                            if is_core_mem_size_of(tcx, callee_def)
                                && let Some(arg_ty) = callee_args.get(0).and_then(|a| a.as_type())
                            {
                                let q_ty = translate_ty(tcx, arg_ty);
                                required_layouts.push(q_ty.clone());
                                proto_terms.push((
                                    bb.as_u32(),
                                    ProtoTerm::CallLayout {
                                        dst: format!("{destination:?}"),
                                        query: ProtoLayoutQuery::SizeOf(q_ty),
                                        target: t_bb.as_u32(),
                                    },
                                ));
                            } else if is_core_mem_align_of(tcx, callee_def)
                                && let Some(arg_ty) = callee_args.get(0).and_then(|a| a.as_type())
                            {
                                let q_ty = translate_ty(tcx, arg_ty);
                                required_layouts.push(q_ty.clone());
                                proto_terms.push((
                                    bb.as_u32(),
                                    ProtoTerm::CallLayout {
                                        dst: format!("{destination:?}"),
                                        query: ProtoLayoutQuery::AlignOf(q_ty),
                                        target: t_bb.as_u32(),
                                    },
                                ));
                            } else if is_core_intrinsics_offset_of(tcx, callee_def)
                                && let Some(container_ty) =
                                    callee_args.get(0).and_then(|a| a.as_type())
                                && args.len() == 2
                                && let Some(var_idx) = extract_u32_const_arg(&args[0].node)
                                && let Some(fld_idx) = extract_u32_const_arg(&args[1].node)
                            {
                                let c_ty = translate_ty(tcx, container_ty);
                                required_layouts.push(c_ty.clone());
                                proto_terms.push((
                                    bb.as_u32(),
                                    ProtoTerm::CallLayout {
                                        dst: format!("{destination:?}"),
                                        query: ProtoLayoutQuery::OffsetOf {
                                            container_ty: c_ty,
                                            variant_idx: var_idx,
                                            field_idx: fld_idx,
                                        },
                                        target: t_bb.as_u32(),
                                    },
                                ));
                            } else if is_core_mem_transmute_copy(tcx, callee_def)
                                && callee_args.len() == 2
                                && args.len() == 1
                            {
                                let mut src_ty =
                                    translate_ty(tcx, callee_args[0].expect_ty());
                                let mut dst_ty =
                                    translate_ty(tcx, callee_args[1].expect_ty());
                                if let Operand::Copy(p) | Operand::Move(p) = &args[0].node
                                    && p.projection.is_empty()
                                    && let Some(pointee) = local_tys[p.local.as_usize()].pointee()
                                    && matches!(pointee, ProtoTy::ArraySizeOf(..))
                                {
                                    src_ty = pointee.clone();
                                }
                                if destination.projection.is_empty()
                                    && matches!(
                                        local_tys[destination.local.as_usize()],
                                        ProtoTy::ArraySizeOf(..)
                                    )
                                {
                                    dst_ty = local_tys[destination.local.as_usize()].clone();
                                }
                                proto_terms.push((
                                    bb.as_u32(),
                                    ProtoTerm::TransmuteCopy {
                                        dst: format!("{destination:?}"),
                                        src_ty,
                                        dst_ty,
                                        op: format!("{:?}", args[0].node),
                                        target: t_bb.as_u32(),
                                    },
                                ));
                            } else {
                                proto_terms.push((
                                    bb.as_u32(),
                                    ProtoTerm::Other(format!(
                                        "Call({}, args={:?})",
                                        tcx.def_path_str(callee_def),
                                        callee_args
                                    )),
                                ));
                            }
                        }
                    }
                    TerminatorKind::Return => {
                        proto_terms.push((bb.as_u32(), ProtoTerm::Return));
                    }
                    _ => {}
                }
            }
        }

        for lty in &local_tys {
            if matches!(lty, ProtoTy::Adt(_) | ProtoTy::Param(..) | ProtoTy::ArraySizeOf(..))
                && !required_layouts.contains(lty)
            {
                required_layouts.push(lty.clone());
            }
        }

        out.push_str(&format!(
            "\n--- Extracted `{path}` (DefIdx={}, kind={kind:?}, is_const={is_const_body}) ---\n",
            def.local_def_index.as_u32()
        ));
        out.push_str(&format!("  ret_ty (_0): {:?}\n", local_tys[0]));
        for (idx, lty) in local_tys.iter().enumerate().skip(1) {
            out.push_str(&format!("  local _{idx}: {lty:?}\n"));
        }
        out.push_str(&format!("  required_layouts: {required_layouts:?}\n"));
        if !hir_collector.anon_consts.is_empty() {
            out.push_str("  AnonConst children classified via `mir_for_ctfe`:\n");
            for (adef, aspan, aclass, asum) in &hir_collector.anon_consts {
                out.push_str(&format!(
                    "    * {:?} (span={aspan:?}) => {aclass:?}\n",
                    tcx.def_path_str(*adef)
                ));
                for line in asum.lines() {
                    out.push_str(&format!("      {line}\n"));
                }
            }
        }
        if !hir_collector.offset_of_exprs.is_empty() {
            out.push_str(&format!(
                "  HIR offset_of_data: {:?}\n",
                hir_collector.offset_of_exprs
            ));
        }
        for (bb, st) in &proto_stmts {
            out.push_str(&format!("  bb{bb} stmt: {st:?}\n"));
        }
        for (bb, tm) in &proto_terms {
            out.push_str(&format!("  bb{bb} term: {tm:?}\n"));
        }

        json_entries.push(format!(
            "  {{\n    \"path\": {:?},\n    \"def_idx\": {},\n    \"kind\": {:?},\n    \"is_const\": {},\n    \"ret_ty\": {:?},\n    \"local_tys\": {:?},\n    \"required_layouts\": {:?},\n    \"stmts\": {:?},\n    \"terms\": {:?}\n  }}",
            path,
            def.local_def_index.as_u32(),
            format!("{kind:?}"),
            is_const_body,
            format!("{:?}", local_tys[0]),
            local_tys.iter().map(|t| format!("{t:?}")).collect::<Vec<_>>(),
            required_layouts.iter().map(|t| format!("{t:?}")).collect::<Vec<_>>(),
            proto_stmts.iter().map(|(b, s)| format!("bb{b}: {s:?}")).collect::<Vec<_>>(),
            proto_terms.iter().map(|(b, t)| format!("bb{b}: {t:?}")).collect::<Vec<_>>(),
        ));
    }

    let json = format!("[\n{}\n]\n", json_entries.join(",\n"));
    (out, json)
}

fn extract_u32_const_arg<'tcx>(op: &Operand<'tcx>) -> Option<u32> {
    if let Operand::Constant(c) = op
        && let Const::Val(ConstValue::Scalar(Scalar::Int(int)), _) = c.const_
    {
        Some(int.to_bits(int.size()) as u32)
    } else {
        None
    }
}

// ============================================================================
// Driver Entrypoint
// ============================================================================

struct ProbeCallbacks {
    json_out_path: Option<String>,
}

impl rustc_driver::Callbacks for ProbeCallbacks {
    fn config(&mut self, config: &mut interface::Config) {
        config.override_queries = Some(override_queries);
        *POSTCLEANUP_MIR.lock().unwrap() = Some(BTreeMap::new());
    }

    fn after_analysis(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'_>,
    ) -> rustc_driver::Compilation {
        let (proto_report, json_str) = run_prototype_extractions(tcx);
        let map = POSTCLEANUP_MIR.lock().unwrap().take().unwrap_or_default();
        println!("=== CAPTURED POSTCLEANUP BODIES ({}) ===", map.len());
        for (_idx, dump) in &map {
            print!("{dump}");
        }
        println!("{proto_report}");
        if let Some(path) = &self.json_out_path {
            std::fs::write(path, json_str).expect("write json output");
        }
        rustc_driver::Compilation::Stop
    }
}

fn main() {
    let mut args: Vec<String> = std::env::args().collect();
    let mut json_out_path = None;
    if let Some(pos) = args.iter().position(|a| a == "--json-out") {
        args.remove(pos);
        json_out_path = Some(args.remove(pos));
    }
    let mut cb = ProbeCallbacks { json_out_path };
    #[cfg(not(rustc_1_101))]
    rustc_driver::run_compiler(&args, &mut cb);
    #[cfg(rustc_1_101)]
    rustc_driver::compiler_entrypoint(&args, &mut cb);
}
