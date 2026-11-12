// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![feature(rustc_private)]

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
use rustc_middle::mir::visit::{NonUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{self, Location, MirPhase, RuntimePhase};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_middle::util::Providers;
use rustc_span::def_id::LocalDefId;

type Provider = for<'tcx> fn(TyCtxt<'tcx>, LocalDefId) -> &'tcx Steal<mir::Body<'tcx>>;
static DEFAULT_PROVIDER: OnceLock<Provider> = OnceLock::new();
static BODY_ANALYSES: Mutex<BTreeMap<u32, BodyPlaceAnalysis>> = Mutex::new(BTreeMap::new());

#[allow(dead_code)]
#[derive(Clone, Debug, Default)]
struct BodyPlaceAnalysis {
    def_id: u32,
    path: String,
    kind: String,
    phase: String,
    is_callable: bool,
    arg_count: usize,
    is_unsafe: bool,
    generics_count: usize,
    total_blocks: usize,
    total_statements: usize,

    // Projection statistics (operational places only, excluding VarDebugInfo)
    total_places: usize,
    projected_places: usize,
    max_proj_len: usize,
    deref_at_zero: usize,
    deref_after_zero: usize,
    deref_base_ref_shared: usize,
    deref_base_ref_mut: usize,
    deref_base_raw_const: usize,
    deref_base_raw_mut: usize,
    deref_base_box: usize,
    deref_base_other: usize,

    proj_field_struct: usize,
    proj_field_tuple: usize,
    proj_field_enum: usize,
    proj_field_closure: usize,
    proj_field_union: usize,
    proj_field_other: usize,

    proj_downcast: usize,
    downcast_not_followed_by_field: usize,
    proj_index_array: usize,
    proj_index_slice: usize,
    proj_const_index: usize,
    proj_subslice: usize,
    proj_opaque_cast: usize,
    proj_unwrap_unsafe_binder: usize,
    proj_other: usize,

    proj_patterns: BTreeMap<String, usize>,

    // Rvalue::Ref statistics
    ref_shared: usize,
    ref_mut_default: usize,
    ref_mut_two_phase: usize,
    ref_mut_closure_capture: usize,
    ref_fake: usize,
    two_phase_details: Vec<String>,
    tp_immediate_call: usize,
    tp_disjoint_eval: usize,
    tp_overlapping_shared_read: usize,
    tp_overlapping_mut_access: usize,
    tp_overlap_examples: Vec<String>,

    // Callees for call-DAG closure
    local_callees: BTreeSet<u32>,
    external_callees: BTreeSet<String>,
    heap_adt_kinds: BTreeSet<String>,

    ref_target_local: usize,
    ref_target_local_field: usize,
    ref_target_deref_reborrow: usize,
    ref_target_deref_field_reborrow: usize,
    ref_target_deref_downcast_field: usize,
    ref_target_deref_index: usize,
    ref_target_other: usize,

    // WithRetag::No copies of references (Derefer + EraseDerefTemps)
    no_retag_copy_shared_ref: usize,
    no_retag_copy_mut_ref: usize,
    no_retag_copy_raw_ptr: usize,
    no_retag_copy_details: Vec<String>,

    // Subtype casts on references
    subtype_casts: usize,
    ptr_to_ptr_casts: usize,
    raw_ptr_rvalues: usize,
    transmute_casts: usize,

    // Reference locals lifecycle
    ref_param_count: usize,
    ref_param_mut_count: usize,
    ref_param_reseated_count: usize,
    ref_local_temp_count: usize,
    ref_local_multi_assign_count: usize,
    ref_local_no_storage_marker_count: usize,
    ref_in_aggregate_count: usize,
    ref_returned_in_ret_slot: bool,
    ref_written_through_deref: usize,

    // Memory model tier blockers
    has_raw_ptr: bool,
    has_unsafe_cell: bool,
    has_slice_or_str_ref: bool,
    has_dyn_trait: bool,
    has_heap_adt: bool,
    has_fixed_array_index: bool,
    has_union: bool,
    has_inline_asm: bool,

    pretty_mir: String,
}

fn classify_ty_flags<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    ty: Ty<'tcx>,
    analysis: &mut BodyPlaceAnalysis,
) {
    let typing_env = ty::TypingEnv::post_analysis(tcx, def.to_def_id());
    for sub in ty.walk() {
        if let ty::GenericArgKind::Type(t) = sub.kind() {
            match t.kind() {
                ty::RawPtr(_, _) => analysis.has_raw_ptr = true,
                ty::Slice(_) | ty::Str => analysis.has_slice_or_str_ref = true,
                ty::Dynamic(_, _) => analysis.has_dyn_trait = true,
                ty::Adt(adt, _) => {
                    if adt.is_union() {
                        analysis.has_union = true;
                    }
                    if adt.is_unsafe_cell() {
                        analysis.has_unsafe_cell = true;
                    }
                    let path = tcx.def_path_str(adt.did());
                    for kind in [
                        "Vec",
                        "Box",
                        "Arc",
                        "HashMap",
                        "String",
                        "BTree",
                        "Formatter",
                        "RawVec",
                    ] {
                        if path.contains(kind) {
                            analysis.has_heap_adt = true;
                            analysis.heap_adt_kinds.insert(kind.to_string());
                        }
                    }
                }
                _ => {}
            }
            if !t.is_freeze(tcx, typing_env) && !t.is_ref() && !t.is_raw_ptr() {
                // Check if non-freeze due to UnsafeCell
                if let ty::Adt(adt, _) = t.kind() {
                    if adt.is_unsafe_cell() {
                        analysis.has_unsafe_cell = true;
                    }
                }
            }
        }
    }
}

struct PlaceVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a mir::Body<'tcx>,
    analysis: &'a mut BodyPlaceAnalysis,
    assign_counts: BTreeMap<u32, usize>,
    has_storage_marker: BTreeSet<u32>,
}

impl<'a, 'tcx> Visitor<'tcx> for PlaceVisitor<'a, 'tcx> {
    fn visit_place(&mut self, place: &mir::Place<'tcx>, context: PlaceContext, _location: Location) {
        if matches!(context, PlaceContext::NonUse(NonUseContext::VarDebugInfo)) {
            return;
        }
        self.analysis.total_places += 1;
        if place.projection.is_empty() {
            return;
        }
        self.analysis.projected_places += 1;
        if place.projection.len() > self.analysis.max_proj_len {
            self.analysis.max_proj_len = place.projection.len();
        }

        let mut cur_pty = mir::PlaceTy::from_ty(self.body.local_decls[place.local].ty);
        let mut pat_elems = Vec::new();
        let projs: Vec<_> = place.projection.iter().collect();

        for (idx, elem) in projs.iter().enumerate() {
            let cur_ty = cur_pty.ty;
            match elem {
                mir::ProjectionElem::Deref => {
                    pat_elems.push("Deref".to_string());
                    if idx == 0 {
                        self.analysis.deref_at_zero += 1;
                    } else {
                        self.analysis.deref_after_zero += 1;
                    }
                    match cur_ty.kind() {
                        ty::Ref(_, _, mir::Mutability::Not) => {
                            self.analysis.deref_base_ref_shared += 1;
                        }
                        ty::Ref(_, _, mir::Mutability::Mut) => {
                            self.analysis.deref_base_ref_mut += 1;
                        }
                        ty::RawPtr(_, mir::Mutability::Not) => {
                            self.analysis.deref_base_raw_const += 1;
                            self.analysis.has_raw_ptr = true;
                        }
                        ty::RawPtr(_, mir::Mutability::Mut) => {
                            self.analysis.deref_base_raw_mut += 1;
                            self.analysis.has_raw_ptr = true;
                        }
                        ty::Adt(adt, _) if adt.is_box() => {
                            self.analysis.deref_base_box += 1;
                            self.analysis.has_heap_adt = true;
                        }
                        _ => {
                            self.analysis.deref_base_other += 1;
                        }
                    }
                }
                mir::ProjectionElem::Field(_, _) => {
                    pat_elems.push("Field".to_string());
                    match cur_ty.kind() {
                        ty::Tuple(_) => self.analysis.proj_field_tuple += 1,
                        ty::Adt(adt, _) => {
                            if adt.is_struct() {
                                self.analysis.proj_field_struct += 1;
                            } else if adt.is_enum() {
                                self.analysis.proj_field_enum += 1;
                            } else if adt.is_union() {
                                self.analysis.proj_field_union += 1;
                                self.analysis.has_union = true;
                            }
                        }
                        ty::Closure(_, _) | ty::CoroutineClosure(_, _) => {
                            self.analysis.proj_field_closure += 1;
                        }
                        _ => self.analysis.proj_field_other += 1,
                    }
                }
                mir::ProjectionElem::Downcast(_, _) => {
                    pat_elems.push("Downcast".to_string());
                    self.analysis.proj_downcast += 1;
                    if !matches!(projs.get(idx + 1), Some(mir::ProjectionElem::Field(_, _))) {
                        self.analysis.downcast_not_followed_by_field += 1;
                    }
                }
                mir::ProjectionElem::Index(_) => {
                    pat_elems.push("Index".to_string());
                    match cur_ty.kind() {
                        ty::Array(_, _) => {
                            self.analysis.proj_index_array += 1;
                            self.analysis.has_fixed_array_index = true;
                        }
                        ty::Slice(_) => {
                            self.analysis.proj_index_slice += 1;
                            self.analysis.has_slice_or_str_ref = true;
                        }
                        _ => {
                            self.analysis.proj_index_slice += 1;
                        }
                    }
                }
                mir::ProjectionElem::ConstantIndex { .. } => {
                    pat_elems.push("ConstantIndex".to_string());
                    self.analysis.proj_const_index += 1;
                }
                mir::ProjectionElem::Subslice { .. } => {
                    pat_elems.push("Subslice".to_string());
                    self.analysis.proj_subslice += 1;
                }
                mir::ProjectionElem::OpaqueCast(_) => {
                    pat_elems.push("OpaqueCast".to_string());
                    self.analysis.proj_opaque_cast += 1;
                }
                mir::ProjectionElem::UnwrapUnsafeBinder(_) => {
                    pat_elems.push("UnwrapUnsafeBinder".to_string());
                    self.analysis.proj_unwrap_unsafe_binder += 1;
                }
            }
            cur_pty = cur_pty.projection_ty(self.tcx, *elem);
        }

        let pat_str = pat_elems.join("->");
        *self.analysis.proj_patterns.entry(pat_str).or_insert(0) += 1;

        self.super_place(place, context, _location);
    }

    fn visit_statement(&mut self, stmt: &mir::Statement<'tcx>, location: Location) {
        match &stmt.kind {
            mir::StatementKind::StorageLive(l) | mir::StatementKind::StorageDead(l) => {
                self.has_storage_marker.insert(l.as_u32());
            }
            mir::StatementKind::Assign(assign_box) => {
                let (dest, rval) = &**assign_box;
                if dest.projection.is_empty() {
                    *self.assign_counts.entry(dest.local.as_u32()).or_insert(0) += 1;
                }
                let dest_ty = dest.ty(&self.body.local_decls, self.tcx).ty;
                if !dest.projection.is_empty()
                    && dest.projection[0] == mir::ProjectionElem::Deref
                    && dest_ty.is_ref()
                {
                    self.analysis.ref_written_through_deref += 1;
                }
                match rval {
                    mir::Rvalue::Ref(_, bkind, place) => {
                        match bkind {
                            mir::BorrowKind::Shared => self.analysis.ref_shared += 1,
                            mir::BorrowKind::Mut { kind: mir::MutBorrowKind::Default } => {
                                self.analysis.ref_mut_default += 1;
                            }
                            mir::BorrowKind::Mut { kind: mir::MutBorrowKind::TwoPhaseBorrow } => {
                                self.analysis.ref_mut_two_phase += 1;
                                self.analysis.two_phase_details.push(format!(
                                    "{}::bb{}[{}]: {:?} = &two_phase mut {:?}",
                                    self.analysis.path,
                                    location.block.as_u32(),
                                    location.statement_index,
                                    dest,
                                    place
                                ));
                            }
                            mir::BorrowKind::Mut { kind: mir::MutBorrowKind::ClosureCapture } => {
                                self.analysis.ref_mut_closure_capture += 1;
                            }
                            mir::BorrowKind::Fake(_) => {
                                self.analysis.ref_fake += 1;
                            }
                        }
                        let projs: Vec<_> = place.projection.iter().collect();
                        if projs.is_empty() {
                            self.analysis.ref_target_local += 1;
                        } else if projs.iter().all(|p| matches!(p, mir::ProjectionElem::Field(_, _))) {
                            self.analysis.ref_target_local_field += 1;
                        } else if projs.len() == 1 && projs[0] == mir::ProjectionElem::Deref {
                            self.analysis.ref_target_deref_reborrow += 1;
                        } else if projs[0] == mir::ProjectionElem::Deref
                            && projs[1..].iter().all(|p| matches!(p, mir::ProjectionElem::Field(_, _)))
                        {
                            self.analysis.ref_target_deref_field_reborrow += 1;
                        } else if projs[0] == mir::ProjectionElem::Deref
                            && projs[1..].iter().any(|p| matches!(p, mir::ProjectionElem::Downcast(_, _)))
                        {
                            self.analysis.ref_target_deref_downcast_field += 1;
                        } else if projs[0] == mir::ProjectionElem::Deref
                            && projs[1..].iter().any(|p| matches!(p, mir::ProjectionElem::Index(_)))
                        {
                            self.analysis.ref_target_deref_index += 1;
                        } else {
                            self.analysis.ref_target_other += 1;
                        }
                    }
                    mir::Rvalue::Use(mir::Operand::Copy(src_place), mir::WithRetag::No) => {
                        let src_ty = src_place.ty(&self.body.local_decls, self.tcx).ty;
                        match src_ty.kind() {
                            ty::Ref(_, _, mir::Mutability::Not) => {
                                self.analysis.no_retag_copy_shared_ref += 1;
                                self.analysis.no_retag_copy_details.push(format!(
                                    "{}::bb{}[{}]: {:?} = no_retag copy {:?} ({:?})",
                                    self.analysis.path,
                                    location.block.as_u32(),
                                    location.statement_index,
                                    dest,
                                    src_place,
                                    src_ty
                                ));
                            }
                            ty::Ref(_, _, mir::Mutability::Mut) => {
                                self.analysis.no_retag_copy_mut_ref += 1;
                                self.analysis.no_retag_copy_details.push(format!(
                                    "{}::bb{}[{}]: {:?} = no_retag copy {:?} ({:?})",
                                    self.analysis.path,
                                    location.block.as_u32(),
                                    location.statement_index,
                                    dest,
                                    src_place,
                                    src_ty
                                ));
                            }
                            ty::RawPtr(_, _) => {
                                self.analysis.no_retag_copy_raw_ptr += 1;
                            }
                            _ => {}
                        }
                    }
                    mir::Rvalue::Cast(kind, _, _) => match kind {
                        mir::CastKind::Subtype => self.analysis.subtype_casts += 1,
                        mir::CastKind::PtrToPtr => self.analysis.ptr_to_ptr_casts += 1,
                        mir::CastKind::Transmute => self.analysis.transmute_casts += 1,
                        _ => {}
                    },
                    mir::Rvalue::RawPtr(_, _) => {
                        self.analysis.raw_ptr_rvalues += 1;
                        self.analysis.has_raw_ptr = true;
                    }
                    mir::Rvalue::Aggregate(_, ops) => {
                        for op in ops {
                            let op_ty = op.ty(&self.body.local_decls, self.tcx);
                            if op_ty.is_ref() {
                                self.analysis.ref_in_aggregate_count += 1;
                            }
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
        self.super_statement(stmt, location);
    }

    fn visit_terminator(&mut self, term: &mir::Terminator<'tcx>, location: Location) {
        if let mir::TerminatorKind::Call { func, destination, .. } = &term.kind {
            if destination.projection.is_empty() {
                *self.assign_counts.entry(destination.local.as_u32()).or_insert(0) += 1;
            }
            let fn_ty = func.ty(&self.body.local_decls, self.tcx);
            if let ty::FnDef(callee_def_id, _) = *fn_ty.kind() {
                if let Some(local_id) = callee_def_id.as_local() {
                    self.analysis.local_callees.insert(local_id.local_def_index.as_u32());
                } else {
                    self.analysis.external_callees.insert(self.tcx.def_path_str(callee_def_id));
                }
            }
        }
        if matches!(term.kind, mir::TerminatorKind::InlineAsm { .. }) {
            self.analysis.has_inline_asm = true;
        }
        self.super_terminator(term, location);
    }
}

fn operand_local<'tcx>(op: &mir::Operand<'tcx>) -> Option<u32> {
    match op {
        mir::Operand::Copy(p) | mir::Operand::Move(p) => Some(p.local.as_u32()),
        mir::Operand::Constant(_) | mir::Operand::RuntimeChecks(_) => None,
    }
}

fn analyze_two_phase_borrows<'tcx>(body: &mir::Body<'tcx>, analysis: &mut BodyPlaceAnalysis) {
    // Map each reference/copy temporary local to its root local if uniquely assigned from a place
    let mut parent_local: BTreeMap<u32, u32> = BTreeMap::new();
    for block in body.basic_blocks.iter() {
        for stmt in &block.statements {
            if let mir::StatementKind::Assign(assign_box) = &stmt.kind {
                let (dest, rval) = &**assign_box;
                if dest.projection.is_empty() {
                    let src_local = match rval {
                        mir::Rvalue::Ref(_, _, p) | mir::Rvalue::RawPtr(_, p) => {
                            Some(p.local.as_u32())
                        }
                        mir::Rvalue::Use(op, _)
                        | mir::Rvalue::Cast(_, op, _) => operand_local(op),
                        _ => None,
                    };
                    if let Some(s) = src_local {
                        if s != dest.local.as_u32() {
                            parent_local.entry(dest.local.as_u32()).or_insert(s);
                        }
                    }
                }
            }
        }
    }
    let resolve_root = |mut l: u32| -> u32 {
        let mut seen = BTreeSet::new();
        while let Some(&p) = parent_local.get(&l) {
            if !seen.insert(l) {
                break;
            }
            l = p;
        }
        l
    };

    for (bb_id, block) in body.basic_blocks.iter_enumerated() {
        for (s_idx, stmt) in block.statements.iter().enumerate() {
            let mir::StatementKind::Assign(assign_box) = &stmt.kind else {
                continue;
            };
            let (dest, mir::Rvalue::Ref(_, mir::BorrowKind::Mut { kind: mir::MutBorrowKind::TwoPhaseBorrow }, borrowed_place)) = &**assign_box else {
                continue;
            };
            let tp_local = dest.local.as_u32();
            let target_root = resolve_root(borrowed_place.local.as_u32());

            // Check if immediate in the same block with zero intervening non-Storage statements
            let mut non_storage_intervening = 0usize;
            for rem_stmt in &block.statements[s_idx + 1..] {
                if !matches!(
                    rem_stmt.kind,
                    mir::StatementKind::StorageLive(_) | mir::StatementKind::StorageDead(_)
                ) {
                    non_storage_intervening += 1;
                }
            }

            // Do BFS across basic blocks starting at (bb_id, s_idx + 1) until tp_local is consumed or killed
            let mut queue = std::collections::VecDeque::new();
            let mut visited_blocks = BTreeSet::new();
            queue.push_back((bb_id, s_idx + 1));

            let mut shared_overlap = false;
            let mut mut_overlap = false;
            let mut overlap_desc = String::new();

            while let Some((cur_bb, start_idx)) = queue.pop_front() {
                let cur_block = &body.basic_blocks[cur_bb];
                let mut activated_or_dead = false;
                for (idx, st) in cur_block.statements.iter().enumerate().skip(start_idx) {
                    match &st.kind {
                        mir::StatementKind::StorageDead(l) if l.as_u32() == tp_local => {
                            activated_or_dead = true;
                            break;
                        }
                        mir::StatementKind::Assign(assign_box2) => {
                            let (d, rv) = &**assign_box2;
                            // Check if tp_local is used on RHS
                            let mut uses_tp = false;
                            match rv {
                                mir::Rvalue::Use(op, _)
                                | mir::Rvalue::Repeat(op, _)
                                | mir::Rvalue::Cast(_, op, _)
                                | mir::Rvalue::UnaryOp(_, op) => {
                                    if operand_local(op) == Some(tp_local) {
                                        uses_tp = true;
                                    }
                                }
                                mir::Rvalue::Ref(_, _, p) => {
                                    if p.local.as_u32() == tp_local {
                                        uses_tp = true;
                                    }
                                }
                                _ => {}
                            }
                            if uses_tp {
                                activated_or_dead = true;
                                break;
                            }
                            // Check if d writes through target_root (not via tp_local)
                            if d.local.as_u32() != tp_local
                                && !d.projection.is_empty()
                                && resolve_root(d.local.as_u32()) == target_root
                            {
                                mut_overlap = true;
                                if overlap_desc.is_empty() {
                                    overlap_desc = format!(
                                        "{}::bb{}[{}] (tp=_{}, root=_{}) -> mut write at bb{}[{}]: {:?}",
                                        analysis.path,
                                        bb_id.as_u32(),
                                        s_idx,
                                        tp_local,
                                        target_root,
                                        cur_bb.as_u32(),
                                        idx,
                                        st.kind
                                    );
                                }
                            }
                            // Check RHS for reads/borrows of target_root
                            match rv {
                                mir::Rvalue::Ref(_, bkind, p) => {
                                    if p.local.as_u32() != tp_local
                                        && resolve_root(p.local.as_u32()) == target_root
                                    {
                                        if matches!(bkind, mir::BorrowKind::Mut { .. }) {
                                            mut_overlap = true;
                                        } else {
                                            shared_overlap = true;
                                        }
                                        if overlap_desc.is_empty() {
                                            overlap_desc = format!(
                                                "{}::bb{}[{}] (tp=_{}, root=_{}) -> overlap borrow at bb{}[{}]: {:?}",
                                                analysis.path,
                                                bb_id.as_u32(),
                                                s_idx,
                                                tp_local,
                                                target_root,
                                                cur_bb.as_u32(),
                                                idx,
                                                st.kind
                                            );
                                        }
                                    }
                                }
                                mir::Rvalue::Use(op, _)
                                | mir::Rvalue::Cast(_, op, _)
                                | mir::Rvalue::UnaryOp(_, op) => {
                                    if let Some(ol) = operand_local(op) {
                                        if ol != tp_local && resolve_root(ol) == target_root {
                                            // Wait: if d is a temporary that is just copying target_root or a field of target_root:
                                            shared_overlap = true;
                                            if overlap_desc.is_empty() {
                                                overlap_desc = format!(
                                                    "{}::bb{}[{}] (tp=_{}, root=_{}) -> overlap read at bb{}[{}]: {:?}",
                                                    analysis.path,
                                                    bb_id.as_u32(),
                                                    s_idx,
                                                    tp_local,
                                                    target_root,
                                                    cur_bb.as_u32(),
                                                    idx,
                                                    st.kind
                                                );
                                            }
                                        }
                                    }
                                }
                                mir::Rvalue::BinaryOp(_, bin_ops) => {
                                    let (op1, op2) = &**bin_ops;
                                    for op in [op1, op2] {
                                        if let Some(ol) = operand_local(op) {
                                            if ol != tp_local && resolve_root(ol) == target_root {
                                                shared_overlap = true;
                                                if overlap_desc.is_empty() {
                                                    overlap_desc = format!(
                                                        "{}::bb{}[{}] (tp=_{}, root=_{}) -> overlap binop read at bb{}[{}]: {:?}",
                                                        analysis.path,
                                                        bb_id.as_u32(),
                                                        s_idx,
                                                        tp_local,
                                                        target_root,
                                                        cur_bb.as_u32(),
                                                        idx,
                                                        st.kind
                                                    );
                                                }
                                            }
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                        _ => {}
                    }
                }
                if activated_or_dead {
                    continue;
                }
                if let Some(term) = &cur_block.terminator {
                    if let mir::TerminatorKind::Call { args, target, .. } = &term.kind {
                        let consumes_tp = args.iter().any(|a| operand_local(&a.node) == Some(tp_local));
                        if consumes_tp {
                            // Also check if another arg in the same Call uses target_root directly
                            for a in args {
                                if let Some(ol) = operand_local(&a.node) {
                                    if ol != tp_local && resolve_root(ol) == target_root {
                                        shared_overlap = true;
                                        if overlap_desc.is_empty() {
                                            overlap_desc = format!(
                                                "{}::bb{}[{}] (tp=_{}, root=_{}) -> call arg overlap at bb{}: {:?}",
                                                analysis.path,
                                                bb_id.as_u32(),
                                                s_idx,
                                                tp_local,
                                                target_root,
                                                cur_bb.as_u32(),
                                                term.kind
                                            );
                                        }
                                    }
                                }
                            }
                            continue;
                        }
                        // Call does not consume tp_local (it's an intermediate call while evaluating args!)
                        for a in args {
                            if let Some(ol) = operand_local(&a.node) {
                                if ol != tp_local && resolve_root(ol) == target_root {
                                    let o_ty = body.local_decls[mir::Local::from_u32(ol)].ty;
                                    if matches!(o_ty.kind(), ty::Ref(_, _, mir::Mutability::Mut)) {
                                        mut_overlap = true;
                                    } else {
                                        shared_overlap = true;
                                    }
                                    if overlap_desc.is_empty() {
                                        overlap_desc = format!(
                                            "{}::bb{}[{}] (tp=_{}, root=_{}) -> intermediate call on root at bb{}: {:?}",
                                            analysis.path,
                                            bb_id.as_u32(),
                                            s_idx,
                                            tp_local,
                                            target_root,
                                            cur_bb.as_u32(),
                                            term.kind
                                        );
                                    }
                                }
                            }
                        }
                        if let Some(next_bb) = *target {
                            if visited_blocks.insert(next_bb) {
                                queue.push_back((next_bb, 0));
                            }
                        }
                    } else {
                        for succ in term.successors() {
                            if !body.basic_blocks[succ].is_cleanup && visited_blocks.insert(succ) {
                                queue.push_back((succ, 0));
                            }
                        }
                    }
                }
            }

            if mut_overlap {
                analysis.tp_overlapping_mut_access += 1;
                analysis.tp_overlap_examples.push(overlap_desc);
            } else if shared_overlap {
                analysis.tp_overlapping_shared_read += 1;
                analysis.tp_overlap_examples.push(overlap_desc);
            } else if non_storage_intervening == 0 {
                analysis.tp_immediate_call += 1;
            } else {
                analysis.tp_disjoint_eval += 1;
            }
        }
    }
}

fn analyze_body<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId, body: &mir::Body<'tcx>) -> BodyPlaceAnalysis {
    let kind = tcx.def_kind(def);
    let is_callable = matches!(kind, DefKind::Fn | DefKind::AssocFn | DefKind::Closure);
    let mut analysis = BodyPlaceAnalysis {
        def_id: def.local_def_index.as_u32(),
        path: tcx.def_path_str(def),
        kind: format!("{kind:?}"),
        phase: format!("{:?}", body.phase),
        is_callable,
        arg_count: body.arg_count,
        is_unsafe: false,
        generics_count: tcx.generics_of(def).count(),
        total_blocks: body.basic_blocks.len(),
        total_statements: body.basic_blocks.iter().map(|b| b.statements.len()).sum(),
        ..Default::default()
    };

    if matches!(kind, DefKind::Fn | DefKind::AssocFn) {
        let sig = tcx.fn_sig(def).instantiate_identity().skip_binder();
        analysis.is_unsafe = sig.safety().is_unsafe();
    }

    for (idx, decl) in body.local_decls.iter_enumerated() {
        classify_ty_flags(tcx, def, decl.ty, &mut analysis);
        if idx.as_u32() == 0 && decl.ty.is_ref() {
            analysis.ref_returned_in_ret_slot = true;
        }
    }

    let mut visitor = PlaceVisitor {
        tcx,
        body,
        analysis: &mut analysis,
        assign_counts: BTreeMap::new(),
        has_storage_marker: BTreeSet::new(),
    };
    visitor.visit_body(body);

    let assign_counts = visitor.assign_counts.clone();
    let has_storage_marker = visitor.has_storage_marker.clone();

    analyze_two_phase_borrows(body, &mut analysis);

    for (idx, decl) in body.local_decls.iter_enumerated() {
        let l_idx = idx.as_u32();
        if let ty::Ref(_, _, mutability) = decl.ty.kind() {
            let assigns = *assign_counts.get(&l_idx).unwrap_or(&0);
            if l_idx >= 1 && (l_idx as usize) <= body.arg_count {
                analysis.ref_param_count += 1;
                if matches!(mutability, mir::Mutability::Mut) {
                    analysis.ref_param_mut_count += 1;
                }
                if assigns > 0 {
                    analysis.ref_param_reseated_count += 1;
                }
            } else if (l_idx as usize) > body.arg_count {
                analysis.ref_local_temp_count += 1;
                if assigns > 1 {
                    analysis.ref_local_multi_assign_count += 1;
                }
                if !has_storage_marker.contains(&l_idx) {
                    analysis.ref_local_no_storage_marker_count += 1;
                }
            }
        }
    }

    if std::env::var("DUMP_PRETTY_MIR").is_ok() {
        let mut pretty = String::new();
        for (idx, decl) in body.local_decls.iter_enumerated() {
            pretty.push_str(&format!("  _{}: {:?} (mut={:?})\n", idx.as_u32(), decl.ty, decl.mutability));
        }
        for (bb_id, block) in body.basic_blocks.iter_enumerated() {
            pretty.push_str(&format!("bb{} (cleanup={}): {{\n", bb_id.as_u32(), block.is_cleanup));
            for (s_idx, stmt) in block.statements.iter().enumerate() {
                pretty.push_str(&format!("  [{}] {:?}\n", s_idx, stmt.kind));
            }
            if let Some(term) = &block.terminator {
                pretty.push_str(&format!("  TERM: {:?}\n", term.kind));
            }
            pretty.push_str("}\n");
        }
        analysis.pretty_mir = pretty;
    }

    assert_eq!(body.phase, MirPhase::Runtime(RuntimePhase::PostCleanup));
    analysis
}

fn hook<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> &'tcx Steal<mir::Body<'tcx>> {
    let provider = DEFAULT_PROVIDER.get().unwrap();
    let original = provider(tcx, def);
    let analysis = analyze_body(tcx, def, &original.borrow());
    BODY_ANALYSES
        .lock()
        .unwrap()
        .insert(def.local_def_index.as_u32(), analysis);
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
            let _ = tcx.mir_drops_elaborated_and_const_checked(def);
        }
        let analyses = BODY_ANALYSES.lock().unwrap();
        let esc = |s: &str| {
            s.replace('\\', "\\\\")
                .replace('"', "\\\"")
                .replace('\n', "\\n")
                .replace('\r', "")
                .replace('\t', "\\t")
        };
        let mut out = String::from("[\n");
        let mut first = true;
        for a in analyses.values() {
            if !first {
                out.push_str(",\n");
            }
            first = false;
            let pat_json = a
                .proj_patterns
                .iter()
                .map(|(k, v)| format!("\"{}\": {}", esc(k), v))
                .collect::<Vec<_>>()
                .join(", ");
            let tp_json = a
                .two_phase_details
                .iter()
                .map(|s| format!("\"{}\"", esc(s)))
                .collect::<Vec<_>>()
                .join(", ");
            let tp_ov_json = a
                .tp_overlap_examples
                .iter()
                .map(|s| format!("\"{}\"", esc(s)))
                .collect::<Vec<_>>()
                .join(", ");
            let nr_json = a
                .no_retag_copy_details
                .iter()
                .map(|s| format!("\"{}\"", esc(s)))
                .collect::<Vec<_>>()
                .join(", ");
            let lc_json = a
                .local_callees
                .iter()
                .map(|id| id.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            let ec_json = a
                .external_callees
                .iter()
                .map(|s| format!("\"{}\"", esc(s)))
                .collect::<Vec<_>>()
                .join(", ");
            let hk_json = a
                .heap_adt_kinds
                .iter()
                .map(|s| format!("\"{}\"", esc(s)))
                .collect::<Vec<_>>()
                .join(", ");
            out.push_str(&format!(
                "  {{\"def_id\": {}, \"path\": \"{}\", \"kind\": \"{}\", \"is_callable\": {}, \"arg_count\": {}, \"is_unsafe\": {}, \"generics_count\": {}, \"total_blocks\": {}, \"total_statements\": {}, \"total_places\": {}, \"projected_places\": {}, \"max_proj_len\": {}, \"deref_at_zero\": {}, \"deref_after_zero\": {}, \"deref_base_ref_shared\": {}, \"deref_base_ref_mut\": {}, \"deref_base_raw_const\": {}, \"deref_base_raw_mut\": {}, \"deref_base_box\": {}, \"deref_base_other\": {}, \"proj_field_struct\": {}, \"proj_field_tuple\": {}, \"proj_field_enum\": {}, \"proj_field_closure\": {}, \"proj_field_union\": {}, \"proj_downcast\": {}, \"downcast_not_followed_by_field\": {}, \"proj_index_array\": {}, \"proj_index_slice\": {}, \"proj_const_index\": {}, \"proj_subslice\": {}, \"proj_opaque_cast\": {}, \"proj_unwrap_unsafe_binder\": {}, \"proj_patterns\": {{{}}}, \"ref_shared\": {}, \"ref_mut_default\": {}, \"ref_mut_two_phase\": {}, \"ref_mut_closure_capture\": {}, \"ref_fake\": {}, \"two_phase_details\": [{}], \"tp_immediate_call\": {}, \"tp_disjoint_eval\": {}, \"tp_overlapping_shared_read\": {}, \"tp_overlapping_mut_access\": {}, \"tp_overlap_examples\": [{}], \"ref_target_local\": {}, \"ref_target_local_field\": {}, \"ref_target_deref_reborrow\": {}, \"ref_target_deref_field_reborrow\": {}, \"ref_target_deref_downcast_field\": {}, \"ref_target_deref_index\": {}, \"ref_target_other\": {}, \"no_retag_copy_shared_ref\": {}, \"no_retag_copy_mut_ref\": {}, \"no_retag_copy_raw_ptr\": {}, \"no_retag_copy_details\": [{}], \"subtype_casts\": {}, \"ptr_to_ptr_casts\": {}, \"raw_ptr_rvalues\": {}, \"transmute_casts\": {}, \"ref_param_count\": {}, \"ref_param_mut_count\": {}, \"ref_param_reseated_count\": {}, \"ref_local_temp_count\": {}, \"ref_local_multi_assign_count\": {}, \"ref_local_no_storage_marker_count\": {}, \"ref_in_aggregate_count\": {}, \"ref_returned_in_ret_slot\": {}, \"ref_written_through_deref\": {}, \"has_raw_ptr\": {}, \"has_unsafe_cell\": {}, \"has_slice_or_str_ref\": {}, \"has_dyn_trait\": {}, \"has_heap_adt\": {}, \"has_fixed_array_index\": {}, \"has_union\": {}, \"has_inline_asm\": {}, \"local_callees\": [{}], \"external_callees\": [{}], \"heap_adt_kinds\": [{}], \"pretty_mir\": \"{}\"}}",
                a.def_id,
                esc(&a.path),
                esc(&a.kind),
                a.is_callable,
                a.arg_count,
                a.is_unsafe,
                a.generics_count,
                a.total_blocks,
                a.total_statements,
                a.total_places,
                a.projected_places,
                a.max_proj_len,
                a.deref_at_zero,
                a.deref_after_zero,
                a.deref_base_ref_shared,
                a.deref_base_ref_mut,
                a.deref_base_raw_const,
                a.deref_base_raw_mut,
                a.deref_base_box,
                a.deref_base_other,
                a.proj_field_struct,
                a.proj_field_tuple,
                a.proj_field_enum,
                a.proj_field_closure,
                a.proj_field_union,
                a.proj_downcast,
                a.downcast_not_followed_by_field,
                a.proj_index_array,
                a.proj_index_slice,
                a.proj_const_index,
                a.proj_subslice,
                a.proj_opaque_cast,
                a.proj_unwrap_unsafe_binder,
                pat_json,
                a.ref_shared,
                a.ref_mut_default,
                a.ref_mut_two_phase,
                a.ref_mut_closure_capture,
                a.ref_fake,
                tp_json,
                a.tp_immediate_call,
                a.tp_disjoint_eval,
                a.tp_overlapping_shared_read,
                a.tp_overlapping_mut_access,
                tp_ov_json,
                a.ref_target_local,
                a.ref_target_local_field,
                a.ref_target_deref_reborrow,
                a.ref_target_deref_field_reborrow,
                a.ref_target_deref_downcast_field,
                a.ref_target_deref_index,
                a.ref_target_other,
                a.no_retag_copy_shared_ref,
                a.no_retag_copy_mut_ref,
                a.no_retag_copy_raw_ptr,
                nr_json,
                a.subtype_casts,
                a.ptr_to_ptr_casts,
                a.raw_ptr_rvalues,
                a.transmute_casts,
                a.ref_param_count,
                a.ref_param_mut_count,
                a.ref_param_reseated_count,
                a.ref_local_temp_count,
                a.ref_local_multi_assign_count,
                a.ref_local_no_storage_marker_count,
                a.ref_in_aggregate_count,
                a.ref_returned_in_ret_slot,
                a.ref_written_through_deref,
                a.has_raw_ptr,
                a.has_unsafe_cell,
                a.has_slice_or_str_ref,
                a.has_dyn_trait,
                a.has_heap_adt,
                a.has_fixed_array_index,
                a.has_union,
                a.has_inline_asm,
                lc_json,
                ec_json,
                hk_json,
                esc(&a.pretty_mir)
            ));
        }
        out.push_str("\n]\n");
        std::fs::write(
            std::env::var("PROBE_OUT").unwrap_or_else(|_| "place_path_census.json".into()),
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
