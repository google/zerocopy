// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Deterministic small-step MIR evaluator (`eval_body` / `MachineState`)
//! aligned 1:1 with `Trusted.MirSemantics.{State,Step,Boundary}` across both
//! Profile v1 (with intra-crate `Call` and pinned `SysrootCall`) and Profile v2
//! (with caller memory, references, raw pointers, slices, `CoreCall`, `Assert`,
//! and single-level `PartialTuple` moves).

use alloc::{
    borrow::Cow, boxed::Box, collections::BTreeSet, format, string::String, vec, vec::Vec,
};

use serde::{Deserialize, Serialize};

use crate::{
    ir::{
        AggregateKind, AssertKind, BinOp, Block, Body, CastKind, CoreCallOp, EnumTagRepr, IntTy,
        IntWidth, Mutability, Operand, Place, Program, ProjectionElem, Rvalue, Statement,
        SysrootNumKind, SysrootNumOp, Terminator, Ty, UnOp, UnwindAction,
    },
    memory::{
        CallerMemory, ISIZE_MAX_BYTES, LayoutData, MemPlace, MemoryState, TargetEndian,
        deinit_indirect, encode_val, eval_const_lit, int_layout, layout_of_ty, load_indirect,
        offset_is_aligned, ptr_add_in_mem, ref_access_spans, ref_access_spans_list,
        ref_valid_in_mem, refs_stay_in_caller_mem, refs_valid_in_mem, refs_valid_in_mem_list,
        slice_get_unchecked_check, spans_pairwise_disjoint, store_indirect, valid_caller_memory,
    },
    ops::{eval_bin_op, eval_int_to_int_cast, eval_un_op},
    value::{
        AllocByte, FaultDetail, FaultKind, PtrVal, ScalarVal, UbClass, Val, check_args_match,
        check_val, enum_admitted, is_int_like_ty, is_primitive_readable_ty, is_supported_local_ty,
        is_supported_v1_local_ty, is_supported_v2_local_ty, is_unicode_scalar, is_zst_enum_ty,
    },
};

/// Evaluation query matching `Trusted.MirModel.Query`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Query {
    pub args: Vec<Val>,
    #[serde(default)]
    pub caller_mem: CallerMemory,
}

/// Storage state of a single MIR local slot (`Trusted.MirModel.LocalSlot`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum LocalSlot {
    Dead,
    Immediate { val: Option<Val> },
    PartialTuple { fields: Vec<Option<Val>> },
    Indirect { place: MemPlace },
}

/// Return continuation for Profile v1 nested function calls.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CallReturnTarget {
    pub block_idx: Option<usize>,
    pub dst_local: u32,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub dst_projection: Vec<ProjectionElem>,
}

/// Active call stack frame (`Trusted.MirSemantics.FrameState`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrameState {
    pub def_id: usize,
    pub block_idx: usize,
    pub stmt_idx: usize,
    pub locals: Vec<LocalSlot>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sysroot_op: Option<SysrootNumOp>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub return_to: Option<CallReturnTarget>,
}

/// Observable terminal value matching `Trusted.MirModel.TerminalOut`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TerminalOut {
    Returned { ret: Val, caller_mem: CallerMemory },
    Unwound { caller_mem: CallerMemory },
}

/// Result of running an evaluation trace to completion, abort, fault, or fuel
/// limit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
pub enum Outcome {
    Returned(TerminalOut),
    /// Process termination via `UnwindAction::Terminate` (unused by current
    /// `Trusted.MirSemantics`, retained for trace schema compatibility).
    Aborted {
        caller_mem: CallerMemory,
    },
    Fault(FaultDetail),
    OutOfFuel,
}

/// Execution profile enforcing either Profile v1 or Profile v2 semantics
/// matching `Trusted.MirSemantics`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvalProfile {
    /// Profile v1 (`mir_profile_version == 1`): scalars/enums/overflow pairs
    /// with multi-frame intra-crate `Call` and pinned `SysrootCall`.
    StrictV1,
    /// Profile v2 (`mir_profile_version == 2`): single-frame execution with
    /// caller memory, references, raw pointers, slices, `CoreCall`, `Assert`,
    /// and single-level `PartialTuple` moves.
    ProfileV2,
}

/// Configuration knobs for MIR stepping.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EvalConfig {
    /// Selected semantic profile (`StrictV1` vs `ProfileV2`).
    pub profile: EvalProfile,
    /// Target memory byte order (`TargetEndian::Big` for Profile v1,
    /// `TargetEndian::Little` for Profile v2).
    pub endian: TargetEndian,
    /// Record per-step execution events inside [`StepTrace`].
    pub record_events: bool,
}

impl Default for EvalConfig {
    fn default() -> Self {
        Self::profile_v1()
    }
}

impl EvalConfig {
    /// Profile v1 configuration matching
    /// `Trusted.MirSemantics.profileTargetEndian`.
    pub const fn profile_v1() -> Self {
        Self { profile: EvalProfile::StrictV1, endian: TargetEndian::Big, record_events: true }
    }

    /// Profile v2 configuration matching
    /// `Trusted.MirSemantics.profileV2TargetEndian`.
    pub const fn profile_v2(endian: TargetEndian) -> Self {
        Self { profile: EvalProfile::ProfileV2, endian, record_events: true }
    }

    /// Select the configuration matching `program.mir_profile_version` (`1` ->
    /// Profile v1, `2` -> Profile v2 little-endian), failing closed on any
    /// other version or big-endian Profile v2 manifest.
    pub fn for_program(
        program: &Program,
        manifest_endian: Option<TargetEndian>,
    ) -> Result<Self, FaultDetail> {
        match program.mir_profile_version {
            1 => Ok(Self::profile_v1()),
            2 => match manifest_endian {
                Some(TargetEndian::Big) => Err(FaultDetail::unsupported(
                    "Profile v2 only supports little-endian targets \
                     (Trusted.MirSemantics.profileV2TargetEndian)",
                )),
                Some(TargetEndian::Little) | None => Ok(Self::profile_v2(TargetEndian::Little)),
            },
            other => Err(FaultDetail::unsupported(format!(
                "unsupported mir_profile_version {other} (expected 1 or 2)"
            ))),
        }
    }

    pub const fn is_strict_profile_v1(&self) -> bool {
        matches!(self.profile, EvalProfile::StrictV1)
    }

    pub const fn enable_profile_v2(&self) -> bool {
        matches!(self.profile, EvalProfile::ProfileV2)
    }
}

/// Single step transition summary emitted in [`StepTrace::events`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StepEvent {
    pub step: usize,
    pub def_id: usize,
    pub block_idx: usize,
    pub stmt_idx: usize,
    pub kind: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub fault: Option<FaultDetail>,
}

/// Complete trace returned by [`eval_body`], [`eval_body_with_config`], and
/// [`eval_body_with_query`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StepTrace {
    pub body_id: usize,
    pub identity: String,
    pub steps_executed: usize,
    pub fuel_limit: usize,
    pub outcome: Outcome,
    pub events: Vec<StepEvent>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub final_state: Option<MachineState>,
}

/// Single-step result before fuel accounting (`StepResult`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StepOutcome {
    Stepped { summary: String },
    Done(TerminalOut),
    Aborted { caller_mem: CallerMemory },
    Fault(FaultDetail),
}

/// Running machine state of the concrete MIR stepper
/// (`Trusted.MirSemantics.State`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MachineState {
    pub frames: Vec<FrameState>,
    pub caller_mem: CallerMemory,
    pub mem: MemoryState,
    pub step_count: usize,
    #[serde(skip)]
    moved_locals_per_frame: Vec<BTreeSet<u32>>,
    #[serde(skip)]
    move_deinit_bytes: BTreeSet<(u64, u64)>,
}

/// Underlying MIR binary operator implemented by each [`SysrootNumKind`],
/// matching `Trusted.MirSemantics.sysrootNumBinOp`.
pub const fn sysroot_num_bin_op(kind: SysrootNumKind) -> BinOp {
    match kind {
        SysrootNumKind::UncheckedAdd => BinOp::AddUnchecked,
        SysrootNumKind::UncheckedSub => BinOp::SubUnchecked,
        SysrootNumKind::UncheckedMul => BinOp::MulUnchecked,
        SysrootNumKind::WrappingAdd => BinOp::Add,
        SysrootNumKind::WrappingSub => BinOp::Sub,
        SysrootNumKind::WrappingMul => BinOp::Mul,
    }
}

/// Pinned synthetic MIR [`Body`] for a verified `core::num` sysroot call,
/// matching `Trusted.MirSemantics.sysrootNumBody`.
pub fn sysroot_num_body(op: SysrootNumOp) -> Body {
    let ty = Ty::Int(op.ty);
    let is_unsafe = matches!(
        op.kind,
        SysrootNumKind::UncheckedAdd | SysrootNumKind::UncheckedSub | SysrootNumKind::UncheckedMul
    );
    Body {
        arg_count: 2,
        is_unsafe,
        local_tys: vec![ty.clone(), ty.clone(), ty],
        blocks: vec![Block {
            statements: vec![Statement::Assign {
                local: 0,
                projection: Vec::new(),
                value: Rvalue::Binary {
                    op: sysroot_num_bin_op(op.kind),
                    left: Operand::Copy { local: 1, projection: Vec::new() },
                    right: Operand::Copy { local: 2, projection: Vec::new() },
                },
            }],
            terminator: Terminator::Ret,
            cleanup: false,
        }],
        identity: String::from("core::num::sysroot"),
    }
}

fn active_frame_body<'a>(program: &'a Program, frame: &FrameState) -> Option<Cow<'a, Body>> {
    match frame.sysroot_op {
        Some(op) => Some(Cow::Owned(sysroot_num_body(op))),
        None => program.bodies.get(frame.def_id).map(Cow::Borrowed),
    }
}

fn place_mentions_local_v2(place: &Place, lid: u32) -> bool {
    place.local == lid
}

fn operand_mentions_local_v2(op: &Operand, lid: u32) -> bool {
    op.as_place().is_some_and(|(local, _, _)| local == lid)
}

fn rvalue_mentions_local_v2(rv: &Rvalue, lid: u32) -> bool {
    match rv {
        Rvalue::Use { operand, .. }
        | Rvalue::UseRetag { operand }
        | Rvalue::Unary { operand, .. }
        | Rvalue::Cast { operand, .. }
        | Rvalue::Repeat { operand, .. }
        | Rvalue::AggregateRangeTo { end: operand, .. }
        | Rvalue::AggregateRangeFrom { start: operand, .. } => {
            operand_mentions_local_v2(operand, lid)
        }
        Rvalue::Binary { left, right, .. } => {
            operand_mentions_local_v2(left, lid) || operand_mentions_local_v2(right, lid)
        }
        Rvalue::Discriminant { place }
        | Rvalue::Ref { place, .. }
        | Rvalue::AddressOf { place, .. }
        | Rvalue::FakeAddressOf { place } => place_mentions_local_v2(place, lid),
        Rvalue::AggregateTuple { fields } | Rvalue::Aggregate { fields, .. } => {
            fields.iter().any(|op| operand_mentions_local_v2(op, lid))
        }
        Rvalue::AggregateArray { elems, .. } => {
            elems.iter().any(|op| operand_mentions_local_v2(op, lid))
        }
        Rvalue::Unsupported => false,
    }
}

fn terminator_mentions_local_v2(term: &Terminator, lid: u32) -> bool {
    match term {
        Terminator::Goto { .. }
        | Terminator::Ret
        | Terminator::Unreachable
        | Terminator::UnwindResume
        | Terminator::Unsupported => false,
        Terminator::SwitchInt { operand, .. } => operand_mentions_local_v2(operand, lid),
        Terminator::Assert { cond, .. } => operand_mentions_local_v2(cond, lid),
        Terminator::CoreCall { args, dst, .. } => {
            args.iter().any(|op| operand_mentions_local_v2(op, lid))
                || place_mentions_local_v2(dst, lid)
        }
        Terminator::Call { args, dst_local, .. }
        | Terminator::SysrootCall { args, dst_local, .. } => {
            args.iter().any(|op| operand_mentions_local_v2(op, lid)) || *dst_local == lid
        }
    }
}

fn fake_address_of_types_match_v2(local_tys: &[Ty], dst_id: u32, src: &Place) -> bool {
    if src.local == dst_id || src.projection.as_slice() != [ProjectionElem::Deref] {
        return false;
    }
    let (Some(base_ty), Some(dst_ty)) =
        (local_tys.get(src.local as usize), local_tys.get(dst_id as usize))
    else {
        return false;
    };
    let (Ty::Ref { pointee, .. } | Ty::RawPtr { pointee, .. }) = base_ty else {
        return false;
    };
    pointee.as_overflow_pair().is_none()
        && dst_ty
            .structural_eq(&Ty::RawPtr { mutability: Mutability::Shared, pointee: pointee.clone() })
}

/// Return `true` when local `lid` of `body` is a metadata-only
/// `FakeForPtrMetadata` temporary, matching
/// `Trusted.MirSemantics.isFakePtrMetadataLocalV2`.
pub fn is_fake_ptr_metadata_local_v2(body: &Body, lid: usize) -> bool {
    if lid <= body.arg_count {
        return false;
    }
    let Ok(lid_u32) = u32::try_from(lid) else {
        return false;
    };
    if !matches!(body.local_tys.get(lid), Some(Ty::RawPtr { mutability: Mutability::Shared, .. })) {
        return false;
    }
    let mut saw_fake_assign = false;
    for bb in &body.blocks {
        for stmt in &bb.statements {
            if let Some((dst_local, dst_proj, rv)) = stmt.as_assign() {
                if dst_local == lid_u32 {
                    if !dst_proj.is_empty() {
                        return false;
                    }
                    let Rvalue::FakeAddressOf { place } = rv else {
                        return false;
                    };
                    if !fake_address_of_types_match_v2(&body.local_tys, lid_u32, place) {
                        return false;
                    }
                    saw_fake_assign = true;
                } else if rvalue_mentions_local_v2(rv, lid_u32) {
                    let ok = match rv {
                        Rvalue::Unary { op: UnOp::PtrMetadata, operand } => operand
                            .as_place()
                            .is_some_and(|(loc, proj, _)| loc == lid_u32 && proj.is_empty()),
                        _ => false,
                    };
                    if !ok {
                        return false;
                    }
                }
            } else {
                match stmt {
                    Statement::StorageLive { .. }
                    | Statement::StorageDead { .. }
                    | Statement::Nop
                    | Statement::PlaceMention { .. }
                    | Statement::Unsupported => {}
                    Statement::Assign { .. } | Statement::AssignPlace { .. } => unreachable!(),
                }
            }
        }
        if terminator_mentions_local_v2(&bb.terminator, lid_u32) {
            return false;
        }
    }
    saw_fake_assign
}

/// Return `true` when every `Rvalue::FakeAddressOf` in `body` writes to an
/// unprojected local satisfying [`is_fake_ptr_metadata_local_v2`], matching
/// `Trusted.MirSemantics.bodyFakeAddressOfValidV2`.
pub fn body_fake_address_of_valid_v2(body: &Body) -> bool {
    body.blocks.iter().all(|bb| {
        bb.statements.iter().all(|stmt| match stmt.as_assign() {
            Some((dst_local, dst_proj, Rvalue::FakeAddressOf { .. })) => {
                dst_proj.is_empty() && is_fake_ptr_metadata_local_v2(body, dst_local as usize)
            }
            _ => true,
        })
    })
}

/// Return `true` when `body` declares any non-`FakeForPtrMetadata` raw-pointer
/// local, matching `Trusted.MirSemantics.bodyHasRawPtrLocalV2`.
pub fn body_has_raw_ptr_local_v2(body: &Body) -> bool {
    body.local_tys
        .iter()
        .enumerate()
        .any(|(idx, ty)| ty.has_raw_ptr_v2() && !is_fake_ptr_metadata_local_v2(body, idx))
}

/// Return `true` when `body` contains both reference-typed and non-fake
/// raw-pointer-typed locals, matching
/// `Trusted.MirSemantics.bodyMixesRefsAndRawPtrsV2`.
pub fn body_mixes_refs_and_raw_ptrs_v2(body: &Body) -> bool {
    body.local_tys.iter().any(Ty::has_ref_v2) && body_has_raw_ptr_local_v2(body)
}

/// Validate program-level target, MIR profile, and body-table invariants
/// (`ProgramVerified` / `ProgramVerifiedV2` structural preconditions).
pub fn validate_program_config(program: &Program, config: &EvalConfig) -> Result<(), FaultDetail> {
    if program.pointer_width_bits != 64 {
        return Err(FaultDetail::unsupported("only 64-bit targets are supported"));
    }
    if config.is_strict_profile_v1() && program.mir_profile_version != 1 {
        return Err(FaultDetail::unsupported(
            "strict Profile v1 requires mir_profile_version == 1",
        ));
    }
    if config.enable_profile_v2() {
        if program.mir_profile_version != 2 {
            return Err(FaultDetail::unsupported(format!(
                "Profile v2 requires mir_profile_version == 2 (got {})",
                program.mir_profile_version
            )));
        }
        if config.endian != TargetEndian::Little {
            return Err(FaultDetail::unsupported(
                "Profile v2 only supports little-endian targets \
                 (Trusted.MirSemantics.profileV2TargetEndian)",
            ));
        }
    }
    if program.bodies.is_empty() {
        return Err(FaultDetail::unsupported("MIR program has no bodies"));
    }
    if (program.entry_def_id as usize) >= program.bodies.len() {
        return Err(FaultDetail::unsupported("MIR program entry_def_id out of bounds"));
    }
    let mut seen_identities = BTreeSet::new();
    for body in &program.bodies {
        if body.identity.is_empty() {
            return Err(FaultDetail::unsupported("MIR body identity is empty"));
        }
        if !seen_identities.insert(body.identity.as_str()) {
            return Err(FaultDetail::unsupported(format!(
                "duplicate MIR body identity '{}'",
                body.identity
            )));
        }
    }
    Ok(())
}

impl MachineState {
    /// Initialize execution state for `body_id` with empty caller memory.
    pub fn init(
        program: &Program,
        body_id: usize,
        args: &[Val],
        config: &EvalConfig,
    ) -> Result<Self, FaultDetail> {
        Self::init_with_caller_mem(program, body_id, args, CallerMemory::default(), config)
    }

    /// Initialize execution state with explicit initial `caller_mem`,
    /// matching `Trusted.MirSemantics.initState` (Profile v1) and
    /// `Trusted.MirSemantics.initStateV2` (Profile v2).
    pub fn init_with_caller_mem(
        program: &Program,
        body_id: usize,
        args: &[Val],
        caller_mem: CallerMemory,
        config: &EvalConfig,
    ) -> Result<Self, FaultDetail> {
        validate_program_config(program, config)?;
        let body = program
            .bodies
            .get(body_id)
            .ok_or_else(|| FaultDetail::unsupported("entry body id out of bounds"))?;
        if config.enable_profile_v2() {
            if !valid_caller_memory(&caller_mem) {
                return Err(FaultDetail::unsupported(
                    "invalid Profile v2 caller memory allocations",
                ));
            }
            validate_body_entry(body, config)?;
            let param_tys = body
                .param_tys()
                .ok_or_else(|| FaultDetail::unsupported("argument count exceeds local count"))?;
            if !check_args_match(args, param_tys, true) {
                return Err(FaultDetail::unsupported(
                    "entry arguments do not match Profile v2 body parameter types",
                ));
            }
            let entry_mem = MemoryState::entry_memory_for_args_v2(&caller_mem, param_tys, args)?;
            if let Err(err) = refs_valid_in_mem_list(&entry_mem, config.endian, param_tys, args) {
                return Err(FaultDetail::undefined_classified(
                    UbClass::EntryInvalidRefArg,
                    format!("invalid Profile v2 entry reference argument: {}", err.reason),
                ));
            }
            if !spans_pairwise_disjoint(&ref_access_spans_list(param_tys, args)) {
                return Err(FaultDetail::undefined_classified(
                    UbClass::EntryInvalidRefArg,
                    "overlapping mutable reference arguments at Profile v2 entry",
                ));
            }
            let locals = init_locals(body, args);
            let frame = FrameState {
                def_id: body_id,
                block_idx: 0,
                stmt_idx: 0,
                locals,
                sysroot_op: None,
                return_to: None,
            };
            Ok(Self {
                frames: vec![frame],
                caller_mem,
                mem: entry_mem,
                step_count: 0,
                moved_locals_per_frame: vec![BTreeSet::new()],
                move_deinit_bytes: BTreeSet::new(),
            })
        } else {
            if !caller_mem.is_empty() {
                return Err(FaultDetail::unsupported(
                    "non-empty callerMem at entry is unsupported in Profile v1",
                ));
            }
            validate_body_in_program(program, body, config)?;
            let param_tys = body
                .param_tys()
                .ok_or_else(|| FaultDetail::unsupported("argument count exceeds local count"))?;
            if !check_args_match(args, param_tys, false) {
                return Err(FaultDetail::unsupported(
                    "entry arguments do not match body parameter types",
                ));
            }
            let locals = init_locals(body, args);
            let frame = FrameState {
                def_id: body_id,
                block_idx: 0,
                stmt_idx: 0,
                locals,
                sysroot_op: None,
                return_to: None,
            };
            Ok(Self {
                frames: vec![frame],
                caller_mem,
                mem: MemoryState::entry_memory(),
                step_count: 0,
                moved_locals_per_frame: vec![BTreeSet::new()],
                move_deinit_bytes: BTreeSet::new(),
            })
        }
    }

    fn ensure_moved_tracking(&mut self) {
        if self.moved_locals_per_frame.len() != self.frames.len() {
            self.moved_locals_per_frame.resize_with(self.frames.len(), BTreeSet::new);
        }
    }

    /// Move immediate local `local_id` of the single active frame into a fresh
    /// stack allocation, matching `Trusted.MirSemantics.forceAllocation`.
    pub fn force_allocation(
        &mut self,
        program: &Program,
        local_id: u32,
        config: &EvalConfig,
    ) -> Result<MemPlace, FaultDetail> {
        if self.frames.len() != 1 {
            return Err(FaultDetail::unsupported("force_allocation requires single active frame"));
        }
        let body = active_frame_body(program, &self.frames[0])
            .ok_or_else(|| FaultDetail::unsupported("active frame body id out of bounds"))?;
        let idx = local_id as usize;
        let ty = body
            .local_tys
            .get(idx)
            .ok_or_else(|| FaultDetail::unsupported("local id out of bounds"))?;
        let slot = self.frames[0]
            .locals
            .get(idx)
            .ok_or_else(|| FaultDetail::unsupported("local slot out of bounds"))?
            .clone();
        match slot {
            LocalSlot::Dead => Err(FaultDetail::undefined_classified(
                UbClass::DeadLocalAccess,
                "force_allocation on dead local",
            )),
            LocalSlot::Indirect { place } => Ok(place),
            LocalSlot::Immediate { val } => {
                self.ensure_moved_tracking();
                let layout = layout_of_ty(ty, config.enable_profile_v2())
                    .ok_or_else(|| FaultDetail::unsupported("local type has no layout"))?;
                let mut next_mem = self.mem.clone();
                let place = next_mem.try_allocate_stack(layout)?;
                let mut next_move_bytes = self.move_deinit_bytes.clone();
                if let Some(v) = val {
                    store_indirect(
                        &mut next_mem,
                        config.endian,
                        ty,
                        place,
                        &v,
                        config.enable_profile_v2(),
                    )?;
                } else if self.moved_locals_per_frame[0].contains(&local_id) {
                    mark_move_deinit_span(&mut next_move_bytes, place, layout.size);
                }
                self.mem = next_mem;
                self.move_deinit_bytes = next_move_bytes;
                self.frames[0].locals[idx] = LocalSlot::Indirect { place };
                Ok(place)
            }
            LocalSlot::PartialTuple { .. } => {
                Err(FaultDetail::unsupported("force_allocation on partially moved tuple"))
            }
        }
    }

    /// Execute one small-step transition matching `Trusted.MirSemantics`'s
    /// `evalStep` (Profile v1) or `evalStepV2` (Profile v2).
    pub fn step(&mut self, program: &Program, config: &EvalConfig) -> StepOutcome {
        if config.enable_profile_v2() {
            self.step_v2(program, config)
        } else {
            self.step_v1(program, config)
        }
    }

    fn step_v1(&mut self, program: &Program, config: &EvalConfig) -> StepOutcome {
        self.ensure_moved_tracking();
        let Some(frame_idx) = self.frames.len().checked_sub(1) else {
            return StepOutcome::Fault(FaultDetail::unsupported("empty call stack"));
        };
        let Some(body) = active_frame_body(program, &self.frames[frame_idx]) else {
            return StepOutcome::Fault(FaultDetail::unsupported("frame def_id out of bounds"));
        };
        let block_idx = self.frames[frame_idx].block_idx;
        let stmt_idx = self.frames[frame_idx].stmt_idx;
        let Some(bb) = body.blocks.get(block_idx) else {
            return StepOutcome::Fault(FaultDetail::unsupported("basic block index out of bounds"));
        };
        self.step_count += 1;
        if let Some(stmt) = bb.statements.get(stmt_idx) {
            self.eval_statement_v1(&body, frame_idx, stmt, config)
        } else if stmt_idx == bb.statements.len() {
            self.eval_terminator_v1(program, &body, bb, frame_idx, config)
        } else {
            StepOutcome::Fault(FaultDetail::unsupported("statement index out of bounds"))
        }
    }

    fn step_v2(&mut self, program: &Program, config: &EvalConfig) -> StepOutcome {
        self.ensure_moved_tracking();
        if self.frames.len() != 1 {
            return StepOutcome::Fault(FaultDetail::unsupported(
                "Profile v2 requires single active frame",
            ));
        }
        let def_id = self.frames[0].def_id;
        let block_idx = self.frames[0].block_idx;
        let stmt_idx = self.frames[0].stmt_idx;
        let Some(body) = program.bodies.get(def_id) else {
            return StepOutcome::Fault(FaultDetail::unsupported("frame def_id out of bounds"));
        };
        let Some(bb) = body.blocks.get(block_idx) else {
            return StepOutcome::Fault(FaultDetail::unsupported("basic block index out of bounds"));
        };
        self.step_count += 1;
        if let Some(stmt) = bb.statements.get(stmt_idx) {
            self.eval_statement_v2(body, stmt, config)
        } else if stmt_idx == bb.statements.len() {
            self.eval_terminator_v2(body, bb, config)
        } else {
            StepOutcome::Fault(FaultDetail::unsupported("statement index out of bounds"))
        }
    }

    fn eval_statement_v1(
        &mut self,
        body: &Body,
        frame_idx: usize,
        stmt: &Statement,
        config: &EvalConfig,
    ) -> StepOutcome {
        let summary = match stmt {
            Statement::Nop => {
                self.frames[frame_idx].stmt_idx += 1;
                "nop".into()
            }
            Statement::PlaceMention { local, projection } => {
                if !projection.is_empty() {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "PlaceMention with non-empty projection is unsupported",
                    ));
                }
                let Some(ty) = body.local_tys.get(*local as usize) else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "PlaceMention local out of bounds",
                    ));
                };
                if !ty.is_sized() {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "PlaceMention on unsized local is unsupported",
                    ));
                }
                self.frames[frame_idx].stmt_idx += 1;
                format!("place_mention(_{local})")
            }
            Statement::StorageLive { local } => {
                let idx = *local as usize;
                let Some(local_ty) = body.local_tys.get(idx) else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "StorageLive local out of bounds in body",
                    ));
                };
                let Some(old) = self.frames[frame_idx].locals.get(idx).cloned() else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "StorageLive local out of bounds in frame",
                    ));
                };
                self.frames[frame_idx].locals[idx] = live_uninit_slot(local_ty);
                self.moved_locals_per_frame[frame_idx].remove(local);
                if let Err(err) = deallocate_local(&mut self.mem, &mut self.move_deinit_bytes, &old)
                {
                    return StepOutcome::Fault(err);
                }
                self.frames[frame_idx].stmt_idx += 1;
                format!("storage_live(_{local})")
            }
            Statement::StorageDead { local } => {
                if *local == 0 {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "StorageDead on return place _0 is unsupported",
                    ));
                }
                let idx = *local as usize;
                let Some(old) = self.frames[frame_idx].locals.get(idx).cloned() else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "StorageDead local out of bounds",
                    ));
                };
                self.frames[frame_idx].locals[idx] = LocalSlot::Dead;
                self.moved_locals_per_frame[frame_idx].remove(local);
                if let Err(err) = deallocate_local(&mut self.mem, &mut self.move_deinit_bytes, &old)
                {
                    return StepOutcome::Fault(err);
                }
                self.frames[frame_idx].stmt_idx += 1;
                format!("storage_dead(_{local})")
            }
            stmt if stmt.as_assign().is_some() => {
                let (local, projection, value) = stmt.as_assign().expect("checked is_some");
                if !projection.is_empty() {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "projected assignment is unsupported in Profile v1",
                    ));
                }
                let Some(dst_ty) = body.local_tys.get(local as usize) else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "assignment destination local out of bounds",
                    ));
                };
                let mut next_locals = self.frames[frame_idx].locals.clone();
                let mut next_moved = self.moved_locals_per_frame[frame_idx].clone();
                let mut next_move_bytes = self.move_deinit_bytes.clone();
                let mut next_mem = self.mem.clone();
                let mut moved =
                    MoveTracker { locals: &mut next_moved, bytes: &mut next_move_bytes };
                let val = match eval_rvalue_v1(
                    &body.local_tys,
                    &mut next_locals,
                    &mut moved,
                    &mut next_mem,
                    dst_ty,
                    value,
                    config.endian,
                ) {
                    Ok(v) => v,
                    Err(err) => return StepOutcome::Fault(err),
                };
                if let Err(err) = write_place_v1(
                    &mut next_locals,
                    &mut moved,
                    &mut next_mem,
                    local,
                    dst_ty,
                    val,
                    config.endian,
                ) {
                    return StepOutcome::Fault(err);
                }
                self.frames[frame_idx].locals = next_locals;
                self.moved_locals_per_frame[frame_idx] = next_moved;
                self.move_deinit_bytes = next_move_bytes;
                self.mem = next_mem;
                self.frames[frame_idx].stmt_idx += 1;
                format!("assign(_{local})")
            }
            _ => {
                return StepOutcome::Fault(FaultDetail::unsupported("unmodeled MIR statement"));
            }
        };
        StepOutcome::Stepped { summary }
    }

    fn eval_terminator_v1(
        &mut self,
        program: &Program,
        body: &Body,
        bb: &Block,
        frame_idx: usize,
        config: &EvalConfig,
    ) -> StepOutcome {
        match &bb.terminator {
            Terminator::Goto { block } => {
                self.frames[frame_idx].block_idx = *block as usize;
                self.frames[frame_idx].stmt_idx = 0;
                StepOutcome::Stepped { summary: format!("goto(bb{block})") }
            }
            Terminator::Ret => {
                if bb.cleanup {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "Return from cleanup block is unsupported",
                    ));
                }
                if frame_idx > 0
                    && self.frames[frame_idx]
                        .locals
                        .iter()
                        .any(|s| matches!(s, LocalSlot::Indirect { .. }))
                {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "non-root callee return with indirect locals is unsupported in Profile v1",
                    ));
                }
                let ret_val = match self.frames[frame_idx].locals.first() {
                    Some(LocalSlot::Immediate { val: Some(v) }) => v.clone(),
                    Some(LocalSlot::Immediate { val: None }) => {
                        let class = uninit_class(&self.moved_locals_per_frame[frame_idx], 0);
                        return StepOutcome::Fault(FaultDetail::undefined_classified(
                            class,
                            "returning with uninitialized _0",
                        ));
                    }
                    Some(LocalSlot::Dead) => {
                        return StepOutcome::Fault(FaultDetail::undefined_classified(
                            UbClass::DeadLocalAccess,
                            "returning with dead _0",
                        ));
                    }
                    Some(LocalSlot::PartialTuple { .. }) => {
                        return StepOutcome::Fault(FaultDetail::unsupported(
                            "partially moved tuple in Profile v1 return",
                        ));
                    }
                    Some(LocalSlot::Indirect { place }) => {
                        let Some(ret_ty) = body.local_tys.first() else {
                            return StepOutcome::Fault(FaultDetail::unsupported(
                                "body missing return local _0 type",
                            ));
                        };
                        match load_indirect(&self.mem, config.endian, ret_ty, *place, false) {
                            Ok(Some(v)) => v,
                            Ok(None) => {
                                let moved = MoveView {
                                    locals: &self.moved_locals_per_frame[frame_idx],
                                    bytes: &self.move_deinit_bytes,
                                };
                                let class = moved.uninit_indirect_local(0, *place, ret_ty, false);
                                return StepOutcome::Fault(FaultDetail::undefined_classified(
                                    class,
                                    "returning with uninitialized indirect _0",
                                ));
                            }
                            Err(err) => return StepOutcome::Fault(err),
                        }
                    }
                    None => {
                        return StepOutcome::Fault(FaultDetail::unsupported(
                            "frame missing return local _0",
                        ));
                    }
                };
                if frame_idx == 0 {
                    if self.frames[0].return_to.is_some() {
                        return StepOutcome::Fault(FaultDetail::unsupported(
                            "root frame cannot carry a return_to continuation",
                        ));
                    }
                    return StepOutcome::Done(TerminalOut::Returned {
                        ret: ret_val,
                        caller_mem: self.caller_mem.clone(),
                    });
                }
                let Some(return_to) = self.frames[frame_idx].return_to.clone() else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "non-root frame missing return destination",
                    ));
                };
                if !return_to.dst_projection.is_empty() {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "projected call return destination is unsupported in Profile v1",
                    ));
                }
                let caller_idx = frame_idx - 1;
                let Some(caller_body) = active_frame_body(program, &self.frames[caller_idx]) else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "caller body id out of bounds",
                    ));
                };
                let Some(dst_ty) = caller_body.local_tys.get(return_to.dst_local as usize) else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "call return destination local out of bounds",
                    ));
                };
                let mut next_locals = self.frames[caller_idx].locals.clone();
                let mut next_moved = self.moved_locals_per_frame[caller_idx].clone();
                let mut next_move_bytes = self.move_deinit_bytes.clone();
                let mut next_mem = self.mem.clone();
                let mut moved =
                    MoveTracker { locals: &mut next_moved, bytes: &mut next_move_bytes };
                if let Err(err) = write_place_v1(
                    &mut next_locals,
                    &mut moved,
                    &mut next_mem,
                    return_to.dst_local,
                    dst_ty,
                    ret_val,
                    config.endian,
                ) {
                    return StepOutcome::Fault(err);
                }
                let Some(tgt_block) = return_to.block_idx else {
                    return StepOutcome::Fault(FaultDetail::undefined_classified(
                        UbClass::DivergingCallReturned,
                        "diverging call returned to caller with no continuation block",
                    ));
                };
                self.frames.pop();
                self.moved_locals_per_frame.pop();
                self.frames[caller_idx].locals = next_locals;
                self.moved_locals_per_frame[caller_idx] = next_moved;
                self.move_deinit_bytes = next_move_bytes;
                self.mem = next_mem;
                self.frames[caller_idx].block_idx = tgt_block;
                self.frames[caller_idx].stmt_idx = 0;
                StepOutcome::Stepped { summary: format!("return_to_caller(bb{tgt_block})") }
            }
            Terminator::Unreachable => StepOutcome::Fault(FaultDetail::undefined_classified(
                UbClass::UnreachableExecuted,
                "executed Unreachable terminator",
            )),
            Terminator::SwitchInt { operand, targets, otherwise } => {
                let mut next_locals = self.frames[frame_idx].locals.clone();
                let mut next_moved = self.moved_locals_per_frame[frame_idx].clone();
                let mut next_move_bytes = self.move_deinit_bytes.clone();
                let mut next_mem = self.mem.clone();
                let mut moved =
                    MoveTracker { locals: &mut next_moved, bytes: &mut next_move_bytes };
                let discr_val = match eval_primitive_operand_v1(
                    &body.local_tys,
                    &mut next_locals,
                    &mut moved,
                    &mut next_mem,
                    operand,
                    config.endian,
                ) {
                    Ok(v) => v,
                    Err(err) => return StepOutcome::Fault(err),
                };
                match eval_switch_target(&discr_val, *otherwise, targets) {
                    Ok(target) => {
                        self.frames[frame_idx].locals = next_locals;
                        self.moved_locals_per_frame[frame_idx] = next_moved;
                        self.move_deinit_bytes = next_move_bytes;
                        self.mem = next_mem;
                        self.frames[frame_idx].block_idx = target as usize;
                        self.frames[frame_idx].stmt_idx = 0;
                        StepOutcome::Stepped { summary: format!("switch_int(->bb{target})") }
                    }
                    Err(err) => StepOutcome::Fault(err),
                }
            }
            Terminator::Call { callee, args, dst_local, dst_projection, target, unwind } => {
                let Some(callee_body) = program.bodies.get(*callee as usize) else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "callee body index out of bounds",
                    ));
                };
                if callee_body.is_unsafe {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "Profile v1 refuses intra-crate calls to unsafe fn callees",
                    ));
                }
                self.eval_call_terminator_v1(
                    body,
                    bb,
                    frame_idx,
                    *callee as usize,
                    None,
                    callee_body,
                    args,
                    *dst_local,
                    dst_projection,
                    *target,
                    *unwind,
                    config.endian,
                )
            }
            Terminator::SysrootCall { op, args, dst_local, dst_projection, target, unwind } => {
                let callee_body = sysroot_num_body(*op);
                self.eval_call_terminator_v1(
                    body,
                    bb,
                    frame_idx,
                    0,
                    Some(*op),
                    &callee_body,
                    args,
                    *dst_local,
                    dst_projection,
                    *target,
                    *unwind,
                    config.endian,
                )
            }
            Terminator::CoreCall { .. }
            | Terminator::Assert { .. }
            | Terminator::UnwindResume
            | Terminator::Unsupported => {
                StepOutcome::Fault(FaultDetail::unsupported("unmodeled Profile v1 MIR terminator"))
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn eval_call_terminator_v1(
        &mut self,
        caller_body: &Body,
        bb: &Block,
        frame_idx: usize,
        callee_def_id: usize,
        sysroot_op: Option<SysrootNumOp>,
        callee_body: &Body,
        args: &[Operand],
        dst_local: u32,
        dst_projection: &[ProjectionElem],
        target: Option<u32>,
        unwind: UnwindAction,
        endian: TargetEndian,
    ) -> StepOutcome {
        if !call_target_admitted(
            caller_body,
            bb,
            callee_body,
            args,
            dst_local,
            dst_projection,
            target,
            unwind,
        ) || callee_body.blocks.is_empty()
            || !storage_annotations_in_bounds(callee_body)
            || !discriminant_types_valid(callee_body)
            || !cast_types_valid(callee_body)
            || !assign_types_valid(callee_body)
            || !callee_body.local_tys.iter().all(is_supported_v1_local_ty)
        {
            return StepOutcome::Fault(FaultDetail::unsupported(
                "call site or callee body rejected by Profile v1 static admission",
            ));
        }
        let has_move = args.iter().any(|a| a.as_place().is_some_and(|(_, _, is_move)| is_move));
        let Some(param_tys) = callee_body.param_tys() else {
            return StepOutcome::Fault(FaultDetail::unsupported(
                "callee argument count exceeds locals",
            ));
        };
        let mut next_locals = self.frames[frame_idx].locals.clone();
        let mut next_moved = self.moved_locals_per_frame[frame_idx].clone();
        let mut next_move_bytes = self.move_deinit_bytes.clone();
        let mut next_mem = self.mem.clone();
        let mut moved = MoveTracker { locals: &mut next_moved, bytes: &mut next_move_bytes };
        let mut arg_vals = Vec::with_capacity(args.len());
        for (opnd, param_ty) in args.iter().zip(param_tys.iter()) {
            let indirect_blocked = match opnd.as_place() {
                Some((local, _, false)) => {
                    has_move
                        && matches!(
                            next_locals.get(local as usize),
                            Some(LocalSlot::Indirect { .. })
                        )
                }
                Some((local, _, true)) => {
                    matches!(next_locals.get(local as usize), Some(LocalSlot::Indirect { .. }))
                }
                None => false,
            };
            if indirect_blocked {
                return StepOutcome::Fault(FaultDetail::unsupported(
                    "indirect call argument with move is unsupported in Profile v1",
                ));
            }
            let (src_ty, slot_val) = match eval_operand_to_slot_v1(
                &caller_body.local_tys,
                &mut next_locals,
                &mut moved,
                &mut next_mem,
                |src_ty| src_ty.structural_eq(param_ty),
                opnd,
                endian,
            ) {
                Ok(res) => res,
                Err(err) => return StepOutcome::Fault(err),
            };
            if !src_ty.structural_eq(param_ty) {
                return StepOutcome::Fault(FaultDetail::unsupported(
                    "call argument type disagrees with callee parameter type",
                ));
            }
            match slot_val {
                ReadSlotVal::Init(v) => arg_vals.push(v),
                ReadSlotVal::Uninit(class) => {
                    return StepOutcome::Fault(FaultDetail::undefined_classified(
                        class,
                        "passing uninitialized argument to call",
                    ));
                }
            }
        }
        match next_locals.get(dst_local as usize) {
            None => {
                return StepOutcome::Fault(FaultDetail::unsupported(
                    "call destination local out of bounds",
                ));
            }
            Some(LocalSlot::Dead) => {
                return StepOutcome::Fault(FaultDetail::undefined_classified(
                    UbClass::DeadLocalAccess,
                    "call destination local is storage-dead",
                ));
            }
            Some(LocalSlot::Indirect { .. }) => {
                return StepOutcome::Fault(FaultDetail::unsupported(
                    "indirect call destination is unsupported in Profile v1",
                ));
            }
            Some(LocalSlot::PartialTuple { .. }) => {
                return StepOutcome::Fault(FaultDetail::unsupported(
                    "partially moved tuple call destination in Profile v1",
                ));
            }
            Some(LocalSlot::Immediate { .. }) => {}
        }
        self.frames[frame_idx].locals = next_locals;
        self.moved_locals_per_frame[frame_idx] = next_moved;
        self.move_deinit_bytes = next_move_bytes;
        self.mem = next_mem;
        let callee_locals = init_locals(callee_body, &arg_vals);
        self.frames.push(FrameState {
            def_id: callee_def_id,
            block_idx: 0,
            stmt_idx: 0,
            locals: callee_locals,
            sysroot_op,
            return_to: Some(CallReturnTarget {
                block_idx: target.map(|b| b as usize),
                dst_local,
                dst_projection: Vec::new(),
            }),
        });
        self.moved_locals_per_frame.push(BTreeSet::new());
        let summary = match sysroot_op {
            Some(op) => format!("sysroot_call({:?})", op.kind),
            None => format!("call(body_{callee_def_id})"),
        };
        StepOutcome::Stepped { summary }
    }

    fn eval_statement_v2(
        &mut self,
        body: &Body,
        stmt: &Statement,
        config: &EvalConfig,
    ) -> StepOutcome {
        let summary = match stmt {
            Statement::Nop => {
                self.frames[0].stmt_idx += 1;
                "nop".into()
            }
            Statement::PlaceMention { local, projection } => {
                if !projection.is_empty() {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "PlaceMention with non-empty projection is unsupported",
                    ));
                }
                let Some(ty) = body.local_tys.get(*local as usize) else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "PlaceMention local out of bounds",
                    ));
                };
                if !ty.is_sized() {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "PlaceMention on unsized local is unsupported",
                    ));
                }
                self.frames[0].stmt_idx += 1;
                format!("place_mention(_{local})")
            }
            Statement::StorageLive { local } => {
                let idx = *local as usize;
                let Some(local_ty) = body.local_tys.get(idx) else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "StorageLive local out of bounds in body",
                    ));
                };
                let Some(old) = self.frames[0].locals.get(idx).cloned() else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "StorageLive local out of bounds in frame",
                    ));
                };
                self.frames[0].locals[idx] = live_uninit_slot(local_ty);
                self.moved_locals_per_frame[0].remove(local);
                if let Err(err) = deallocate_local(&mut self.mem, &mut self.move_deinit_bytes, &old)
                {
                    return StepOutcome::Fault(err);
                }
                self.frames[0].stmt_idx += 1;
                format!("storage_live(_{local})")
            }
            Statement::StorageDead { local } => {
                if *local == 0 {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "StorageDead on return place _0 is unsupported",
                    ));
                }
                let idx = *local as usize;
                let Some(old) = self.frames[0].locals.get(idx).cloned() else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "StorageDead local out of bounds",
                    ));
                };
                self.frames[0].locals[idx] = LocalSlot::Dead;
                self.moved_locals_per_frame[0].remove(local);
                if let Err(err) = deallocate_local(&mut self.mem, &mut self.move_deinit_bytes, &old)
                {
                    return StepOutcome::Fault(err);
                }
                self.frames[0].stmt_idx += 1;
                format!("storage_dead(_{local})")
            }
            stmt if stmt.as_assign().is_some() => {
                let (local, projection, value) = stmt.as_assign().expect("checked is_some");
                let Some(dst_ty) = place_static_ty_v2(&body.local_tys, local, projection) else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "assignment destination place has no Profile v2 static type",
                    ));
                };
                // Resolve destination BEFORE evaluating rvalue, matching
                // `Trusted.MirSemantics.evalStatementV2`
                // (`resolvePlaceDestV2`).
                let moved_view = MoveView {
                    locals: &self.moved_locals_per_frame[0],
                    bytes: &self.move_deinit_bytes,
                };
                let dest = match resolve_place_dest_v2(
                    &body.local_tys,
                    &self.frames[0].locals,
                    moved_view,
                    &self.mem,
                    local,
                    projection,
                    &dst_ty,
                    config.endian,
                ) {
                    Ok(d) => d,
                    Err(err) => return StepOutcome::Fault(err),
                };
                let mut next_locals = self.frames[0].locals.clone();
                let mut next_moved = self.moved_locals_per_frame[0].clone();
                let mut next_move_bytes = self.move_deinit_bytes.clone();
                let mut next_mem = self.mem.clone();
                let mut moved =
                    MoveTracker { locals: &mut next_moved, bytes: &mut next_move_bytes };
                let val = match eval_rvalue_v2(
                    &body.local_tys,
                    &mut next_locals,
                    &mut moved,
                    &mut next_mem,
                    &dst_ty,
                    value,
                    config.endian,
                ) {
                    Ok(v) => v,
                    Err(err) => return StepOutcome::Fault(err),
                };
                if let Err(err) = write_place_dest_v2(
                    &mut next_locals,
                    &mut moved,
                    &mut next_mem,
                    &dest,
                    &dst_ty,
                    val,
                    config.endian,
                ) {
                    return StepOutcome::Fault(err);
                }
                if let Err(err) = check_assign_copy_hazard_v2(
                    &body.local_tys,
                    &self.frames[0].locals,
                    &self.mem,
                    &dest,
                    &dst_ty,
                    value,
                    config.endian,
                ) {
                    return StepOutcome::Fault(err);
                }
                self.frames[0].locals = next_locals;
                self.moved_locals_per_frame[0] = next_moved;
                self.move_deinit_bytes = next_move_bytes;
                self.mem = next_mem;
                self.frames[0].stmt_idx += 1;
                if projection.is_empty() {
                    format!("assign(_{local})")
                } else {
                    format!("assign_place(*_{local})")
                }
            }
            _ => {
                return StepOutcome::Fault(FaultDetail::unsupported("unmodeled MIR statement"));
            }
        };
        StepOutcome::Stepped { summary }
    }

    fn eval_terminator_v2(&mut self, body: &Body, bb: &Block, config: &EvalConfig) -> StepOutcome {
        match &bb.terminator {
            Terminator::Goto { block } => {
                self.frames[0].block_idx = *block as usize;
                self.frames[0].stmt_idx = 0;
                StepOutcome::Stepped { summary: format!("goto(bb{block})") }
            }
            Terminator::Ret => {
                if bb.cleanup {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "Return from cleanup block is unsupported",
                    ));
                }
                if self.frames[0].return_to.is_some() {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "root frame cannot carry a return_to continuation",
                    ));
                }
                let Some(ret_ty) = body.local_tys.first() else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "body missing return local _0 type",
                    ));
                };
                let ret_val = match self.frames[0].locals.first() {
                    Some(LocalSlot::Immediate { val: Some(v) }) => v.clone(),
                    Some(LocalSlot::Immediate { val: None }) => {
                        let class = uninit_class(&self.moved_locals_per_frame[0], 0);
                        return StepOutcome::Fault(FaultDetail::undefined_classified(
                            class,
                            "returning with uninitialized _0",
                        ));
                    }
                    Some(LocalSlot::PartialTuple { .. }) => {
                        return StepOutcome::Fault(FaultDetail::undefined_classified(
                            UbClass::MoveDeinitLocalRead,
                            "returning with partially moved tuple in _0",
                        ));
                    }
                    Some(LocalSlot::Dead) => {
                        return StepOutcome::Fault(FaultDetail::undefined_classified(
                            UbClass::DeadLocalAccess,
                            "returning with dead _0",
                        ));
                    }
                    Some(LocalSlot::Indirect { place }) => {
                        match load_indirect(&self.mem, config.endian, ret_ty, *place, true) {
                            Ok(Some(v)) => v,
                            Ok(None) => {
                                let moved = MoveView {
                                    locals: &self.moved_locals_per_frame[0],
                                    bytes: &self.move_deinit_bytes,
                                };
                                let class = moved.uninit_indirect_local(0, *place, ret_ty, true);
                                return StepOutcome::Fault(FaultDetail::undefined_classified(
                                    class,
                                    "returning with uninitialized indirect _0",
                                ));
                            }
                            Err(err) => return StepOutcome::Fault(err),
                        }
                    }
                    None => {
                        return StepOutcome::Fault(FaultDetail::unsupported(
                            "frame missing return local _0",
                        ));
                    }
                };
                if let Err(class) = refs_stay_in_caller_mem(&self.caller_mem, ret_ty, &ret_val) {
                    return StepOutcome::Fault(FaultDetail::undefined_classified(
                        class,
                        "returned reference escapes callee stack frame",
                    ));
                }
                if let Err(err) = refs_valid_in_mem(&self.mem, config.endian, ret_ty, &ret_val) {
                    return StepOutcome::Fault(err);
                }
                if !spans_pairwise_disjoint(&ref_access_spans(ret_ty, &ret_val)) {
                    return StepOutcome::Fault(FaultDetail::undefined_classified(
                        UbClass::OverlappingMutRefsReturned,
                        "returned references violate mutable-borrow disjointness",
                    ));
                }
                StepOutcome::Done(TerminalOut::Returned {
                    ret: ret_val,
                    caller_mem: self.mem.extract_caller_memory(&self.caller_mem),
                })
            }
            Terminator::Unreachable => StepOutcome::Fault(FaultDetail::undefined_classified(
                UbClass::UnreachableExecuted,
                "executed Unreachable terminator",
            )),
            Terminator::SwitchInt { operand, targets, otherwise } => {
                let mut next_locals = self.frames[0].locals.clone();
                let mut next_moved = self.moved_locals_per_frame[0].clone();
                let mut next_move_bytes = self.move_deinit_bytes.clone();
                let mut next_mem = self.mem.clone();
                let mut moved =
                    MoveTracker { locals: &mut next_moved, bytes: &mut next_move_bytes };
                let discr_val = match eval_primitive_operand_v2(
                    &body.local_tys,
                    &mut next_locals,
                    &mut moved,
                    &mut next_mem,
                    operand,
                    config.endian,
                ) {
                    Ok(v) => v,
                    Err(err) => return StepOutcome::Fault(err),
                };
                match eval_switch_target(&discr_val, *otherwise, targets) {
                    Ok(target) => {
                        self.frames[0].locals = next_locals;
                        self.moved_locals_per_frame[0] = next_moved;
                        self.move_deinit_bytes = next_move_bytes;
                        self.mem = next_mem;
                        self.frames[0].block_idx = target as usize;
                        self.frames[0].stmt_idx = 0;
                        StepOutcome::Stepped { summary: format!("switch_int(->bb{target})") }
                    }
                    Err(err) => StepOutcome::Fault(err),
                }
            }
            Terminator::Assert { cond, expected, msg, target, unwind: _ } => {
                let mut next_locals = self.frames[0].locals.clone();
                let mut next_moved = self.moved_locals_per_frame[0].clone();
                let mut next_move_bytes = self.move_deinit_bytes.clone();
                let mut next_mem = self.mem.clone();
                let mut moved =
                    MoveTracker { locals: &mut next_moved, bytes: &mut next_move_bytes };
                let cond_val = match eval_primitive_operand_v2(
                    &body.local_tys,
                    &mut next_locals,
                    &mut moved,
                    &mut next_mem,
                    cond,
                    config.endian,
                ) {
                    Ok(v) => v,
                    Err(err) => return StepOutcome::Fault(err),
                };
                let Val::Bool(actual) = cond_val else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "Assert condition must be bool",
                    ));
                };
                if actual == *expected {
                    self.frames[0].locals = next_locals;
                    self.moved_locals_per_frame[0] = next_moved;
                    self.move_deinit_bytes = next_move_bytes;
                    self.mem = next_mem;
                    self.frames[0].block_idx = *target as usize;
                    self.frames[0].stmt_idx = 0;
                    StepOutcome::Stepped { summary: format!("assert_ok(->bb{target})") }
                } else {
                    match msg {
                        AssertKind::MisalignedPtrDeref | AssertKind::NullPtrDeref => {
                            StepOutcome::Fault(FaultDetail::undefined_classified(
                                UbClass::CheckPtrAssertOnly,
                                format!("pointer UB-check assert failed ({msg:?})"),
                            ))
                        }
                        other => StepOutcome::Fault(FaultDetail::unsupported(format!(
                            "panicking Assert ({other:?}) is unsupported in Profile v2"
                        ))),
                    }
                }
            }
            Terminator::CoreCall { op, args, dst, target: Some(target), unwind: _ } => {
                if !dst.projection.is_empty() {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "CoreCall destination must be an unprojected local",
                    ));
                }
                let Some(dst_ty) = body.local_tys.get(dst.local as usize) else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "CoreCall destination local out of bounds",
                    ));
                };
                let mut next_locals = self.frames[0].locals.clone();
                let mut next_moved = self.moved_locals_per_frame[0].clone();
                let mut next_move_bytes = self.move_deinit_bytes.clone();
                let mut next_mem = self.mem.clone();
                let mut moved =
                    MoveTracker { locals: &mut next_moved, bytes: &mut next_move_bytes };
                let typed_args = match eval_arg_operands_v2(
                    &body.local_tys,
                    &mut next_locals,
                    &mut moved,
                    &mut next_mem,
                    args,
                    config.endian,
                ) {
                    Ok(v) => v,
                    Err(err) => return StepOutcome::Fault(err),
                };
                let res_val =
                    match exec_core_call_op(&next_mem, op, &typed_args, dst_ty, config.endian) {
                        Ok(v) => v,
                        Err(err) => return StepOutcome::Fault(err),
                    };
                let dest = match resolve_place_dest_v2(
                    &body.local_tys,
                    &next_locals,
                    moved.as_view(),
                    &next_mem,
                    dst.local,
                    &dst.projection,
                    dst_ty,
                    config.endian,
                ) {
                    Ok(d) => d,
                    Err(err) => return StepOutcome::Fault(err),
                };
                if let Err(err) = write_place_dest_v2(
                    &mut next_locals,
                    &mut moved,
                    &mut next_mem,
                    &dest,
                    dst_ty,
                    res_val,
                    config.endian,
                ) {
                    return StepOutcome::Fault(err);
                }
                self.frames[0].locals = next_locals;
                self.moved_locals_per_frame[0] = next_moved;
                self.move_deinit_bytes = next_move_bytes;
                self.mem = next_mem;
                self.frames[0].block_idx = *target as usize;
                self.frames[0].stmt_idx = 0;
                StepOutcome::Stepped { summary: format!("core_call({op:?}->bb{target})") }
            }
            Terminator::CoreCall { target: None, .. }
            | Terminator::UnwindResume
            | Terminator::Call { .. }
            | Terminator::SysrootCall { .. }
            | Terminator::Unsupported => {
                StepOutcome::Fault(FaultDetail::unsupported("unmodeled Profile v2 MIR terminator"))
            }
        }
    }
}

/// Evaluate body `body_id` with Profile v1 defaults up to `fuel` steps.
pub fn eval_body(program: &Program, body_id: usize, args: &[Val], fuel: usize) -> StepTrace {
    let config = EvalConfig::profile_v1();
    eval_body_with_config(program, body_id, args, fuel, &config)
}

/// Evaluate body `body_id` selecting the profile automatically from
/// `program.mir_profile_version` (`1` -> Profile v1, `2` -> Profile v2).
pub fn eval_body_auto(program: &Program, body_id: usize, args: &[Val], fuel: usize) -> StepTrace {
    match EvalConfig::for_program(program, None) {
        Ok(config) => eval_body_with_config(program, body_id, args, fuel, &config),
        Err(err) => StepTrace {
            body_id,
            identity: program.bodies.get(body_id).map(|b| b.identity.clone()).unwrap_or_default(),
            steps_executed: 0,
            fuel_limit: fuel,
            outcome: Outcome::Fault(err),
            events: Vec::new(),
            final_state: None,
        },
    }
}

/// Evaluate body matching `identity` with automatic profile selection.
pub fn eval_body_by_identity(
    program: &Program,
    identity: &str,
    args: &[Val],
    fuel: usize,
) -> Result<StepTrace, FaultDetail> {
    let Some(body_id) = program.bodies.iter().position(|b| b.identity == identity) else {
        return Err(FaultDetail::unsupported(format!("no body with identity '{identity}' found")));
    };
    Ok(eval_body_auto(program, body_id, args, fuel))
}

/// Evaluate `body_id` with explicit [`EvalConfig`] and empty caller memory.
pub fn eval_body_with_config(
    program: &Program,
    body_id: usize,
    args: &[Val],
    fuel: usize,
    config: &EvalConfig,
) -> StepTrace {
    eval_body_with_caller_mem(program, body_id, args, CallerMemory::default(), fuel, config)
}

/// Evaluate `body_id` with an explicit [`Query`] (`args` + `caller_mem`) and
/// [`EvalConfig`].
pub fn eval_body_with_query(
    program: &Program,
    body_id: usize,
    query: &Query,
    fuel: usize,
    config: &EvalConfig,
) -> StepTrace {
    eval_body_with_caller_mem(program, body_id, &query.args, query.caller_mem.clone(), fuel, config)
}

/// Evaluate `body_id` with explicit initial `caller_mem` and [`EvalConfig`].
pub fn eval_body_with_caller_mem(
    program: &Program,
    body_id: usize,
    args: &[Val],
    caller_mem: CallerMemory,
    fuel: usize,
    config: &EvalConfig,
) -> StepTrace {
    let identity = program.bodies.get(body_id).map(|b| b.identity.clone()).unwrap_or_default();
    let mut state =
        match MachineState::init_with_caller_mem(program, body_id, args, caller_mem, config) {
            Ok(s) => s,
            Err(err) => {
                return StepTrace {
                    body_id,
                    identity,
                    steps_executed: 0,
                    fuel_limit: fuel,
                    outcome: Outcome::Fault(err),
                    events: Vec::new(),
                    final_state: None,
                };
            }
        };
    let mut events = Vec::new();
    for step_idx in 0..fuel {
        let active = &state.frames[state.frames.len() - 1];
        let def_id = active.def_id;
        let block_idx = active.block_idx;
        let stmt_idx = active.stmt_idx;
        match state.step(program, config) {
            StepOutcome::Stepped { summary } => {
                if config.record_events {
                    events.push(StepEvent {
                        step: step_idx,
                        def_id,
                        block_idx,
                        stmt_idx,
                        kind: summary,
                        fault: None,
                    });
                }
            }
            StepOutcome::Done(out) => {
                if config.record_events {
                    events.push(StepEvent {
                        step: step_idx,
                        def_id,
                        block_idx,
                        stmt_idx,
                        kind: "terminal".into(),
                        fault: None,
                    });
                }
                return StepTrace {
                    body_id,
                    identity,
                    steps_executed: step_idx + 1,
                    fuel_limit: fuel,
                    outcome: Outcome::Returned(out),
                    events,
                    final_state: Some(state),
                };
            }
            StepOutcome::Aborted { caller_mem } => {
                if config.record_events {
                    events.push(StepEvent {
                        step: step_idx,
                        def_id,
                        block_idx,
                        stmt_idx,
                        kind: "abort".into(),
                        fault: None,
                    });
                }
                return StepTrace {
                    body_id,
                    identity,
                    steps_executed: step_idx + 1,
                    fuel_limit: fuel,
                    outcome: Outcome::Aborted { caller_mem },
                    events,
                    final_state: Some(state),
                };
            }
            StepOutcome::Fault(err) => {
                if config.record_events {
                    events.push(StepEvent {
                        step: step_idx,
                        def_id,
                        block_idx,
                        stmt_idx,
                        kind: "fault".into(),
                        fault: Some(err.clone()),
                    });
                }
                return StepTrace {
                    body_id,
                    identity,
                    steps_executed: step_idx + 1,
                    fuel_limit: fuel,
                    outcome: Outcome::Fault(err),
                    events,
                    final_state: Some(state),
                };
            }
        }
    }
    StepTrace {
        body_id,
        identity,
        steps_executed: fuel,
        fuel_limit: fuel,
        outcome: Outcome::OutOfFuel,
        events,
        final_state: Some(state),
    }
}

#[derive(Clone, Copy)]
struct MoveView<'a> {
    locals: &'a BTreeSet<u32>,
    bytes: &'a BTreeSet<(u64, u64)>,
}

struct MoveTracker<'a> {
    locals: &'a mut BTreeSet<u32>,
    bytes: &'a mut BTreeSet<(u64, u64)>,
}

enum ReadSlotVal {
    Init(Val),
    Uninit(UbClass),
}

fn mark_move_deinit_span(move_deinit_bytes: &mut BTreeSet<(u64, u64)>, place: MemPlace, size: u64) {
    for off in 0..size {
        if let Some(addr) = place.offset.checked_add(off) {
            move_deinit_bytes.insert((place.alloc_id, addr));
        }
    }
}

fn clear_move_deinit_span(
    move_deinit_bytes: &mut BTreeSet<(u64, u64)>,
    place: MemPlace,
    size: u64,
) {
    if size == 0 {
        return;
    }
    let end_incl = place.offset.saturating_add(size - 1);
    let to_remove: Vec<(u64, u64)> = move_deinit_bytes
        .range((place.alloc_id, place.offset)..=(place.alloc_id, end_incl))
        .copied()
        .collect();
    for key in to_remove {
        move_deinit_bytes.remove(&key);
    }
}

fn clear_move_deinit_alloc(move_deinit_bytes: &mut BTreeSet<(u64, u64)>, alloc_id: u64) {
    move_deinit_bytes.retain(|&(aid, _)| aid != alloc_id);
}

impl MoveView<'_> {
    fn uninit_local(self, local: u32) -> UbClass {
        uninit_class(self.locals, local)
    }

    fn has_deinit_in_span(self, place: MemPlace, size: u64) -> bool {
        if size == 0 {
            return false;
        }
        let end_incl = place.offset.saturating_add(size - 1);
        self.bytes
            .range((place.alloc_id, place.offset)..=(place.alloc_id, end_incl))
            .next()
            .is_some()
    }

    fn uninit_deref(self, place: MemPlace, size: u64) -> UbClass {
        if self.has_deinit_in_span(place, size) {
            UbClass::MoveDeinitLocalRead
        } else {
            UbClass::UninitMemoryRead
        }
    }

    fn uninit_indirect_local(
        self,
        local: u32,
        place: MemPlace,
        ty: &Ty,
        enable_profile_v2: bool,
    ) -> UbClass {
        let byte_moved = layout_of_ty(ty, enable_profile_v2)
            .is_some_and(|lay| self.has_deinit_in_span(place, lay.size));
        if byte_moved || self.locals.contains(&local) {
            UbClass::MoveDeinitLocalRead
        } else {
            UbClass::UninitMemoryRead
        }
    }
}

impl MoveTracker<'_> {
    fn as_view(&self) -> MoveView<'_> {
        MoveView { locals: self.locals, bytes: self.bytes }
    }

    fn mark_local(&mut self, local: u32) {
        self.locals.insert(local);
    }

    fn clear_local(&mut self, local: u32) {
        self.locals.remove(&local);
    }

    fn mark_bytes_span(&mut self, place: MemPlace, size: u64) {
        mark_move_deinit_span(self.bytes, place, size);
    }

    fn clear_bytes_span(&mut self, place: MemPlace, size: u64) {
        clear_move_deinit_span(self.bytes, place, size);
    }
}

fn store_indirect_tracked(
    mem: &mut MemoryState,
    moved: &mut MoveTracker<'_>,
    endian: TargetEndian,
    ty: &Ty,
    place: MemPlace,
    val: &Val,
    enable_profile_v2: bool,
) -> Result<(), FaultDetail> {
    store_indirect(mem, endian, ty, place, val, enable_profile_v2)?;
    if let Some(layout) = layout_of_ty(ty, enable_profile_v2) {
        moved.clear_bytes_span(place, layout.size);
    }
    Ok(())
}

fn deinit_indirect_tracked(
    mem: &mut MemoryState,
    moved: &mut MoveTracker<'_>,
    ty: &Ty,
    place: MemPlace,
    enable_profile_v2: bool,
) -> Result<(), FaultDetail> {
    let Some(layout) = layout_of_ty(ty, enable_profile_v2) else {
        return Err(FaultDetail::unsupported("indirect local has no memory layout"));
    };
    let init_offsets: Vec<u64> = mem
        .find(place.alloc_id)
        .and_then(|alloc| {
            let start = usize::try_from(place.offset).ok()?;
            let size = usize::try_from(layout.size).ok()?;
            let slice = alloc.bytes.get(start..start.checked_add(size)?)?;
            Some(
                slice
                    .iter()
                    .enumerate()
                    .filter_map(|(i, b)| {
                        matches!(b, AllocByte::Init { .. })
                            .then(|| place.offset.checked_add(i as u64))
                            .flatten()
                    })
                    .collect(),
            )
        })
        .unwrap_or_default();
    deinit_indirect(mem, ty, place, enable_profile_v2)?;
    for addr in init_offsets {
        moved.bytes.insert((place.alloc_id, addr));
    }
    Ok(())
}

fn uninit_class(moved_locals: &BTreeSet<u32>, local: u32) -> UbClass {
    if moved_locals.contains(&local) {
        UbClass::MoveDeinitLocalRead
    } else {
        UbClass::UninitLocalRead
    }
}

fn downgrade_conservative_ref_check(err: FaultDetail) -> FaultDetail {
    if err.kind == FaultKind::Undefined { FaultDetail::undefined(err.reason) } else { err }
}

fn live_uninit_slot(ty: &Ty) -> LocalSlot {
    match ty {
        Ty::Unit => LocalSlot::Immediate { val: Some(Val::Unit) },
        Ty::Enum(ety) if is_zst_enum_ty(ety) => {
            LocalSlot::Immediate { val: Some(Val::EnumVal { ty: ety.clone(), variant: 0 }) }
        }
        _ => LocalSlot::Immediate { val: None },
    }
}

fn has_storage_annotation(body: &Body, local_id: usize) -> bool {
    let target = u32::try_from(local_id).ok();
    body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| match stmt {
            Statement::StorageLive { local } | Statement::StorageDead { local } => {
                target == Some(*local)
            }
            _ => false,
        })
    })
}

fn storage_annotations_in_bounds(body: &Body) -> bool {
    let num_locals = body.local_tys.len();
    body.blocks.iter().all(|bb| {
        bb.statements.iter().all(|stmt| match stmt {
            Statement::StorageLive { local } | Statement::StorageDead { local } => {
                (*local as usize) < num_locals
            }
            _ => true,
        })
    })
}

fn discriminant_types_valid(body: &Body) -> bool {
    body.blocks.iter().all(|bb| {
        bb.statements.iter().all(|stmt| {
            let Some((
                dst_local,
                dst_proj,
                Rvalue::Discriminant { place: Place { local: src_local, projection: src_proj } },
            )) = stmt.as_assign()
            else {
                return true;
            };
            if !dst_proj.is_empty() || !src_proj.is_empty() {
                return true;
            }
            let (Some(src_ty), Some(dst_ty)) =
                (body.local_tys.get(*src_local as usize), body.local_tys.get(dst_local as usize))
            else {
                return true;
            };
            match src_ty {
                Ty::Enum(ety) if enum_admitted(ety) => dst_ty.structural_eq(&Ty::Int(ety.discr())),
                Ty::Ordering => {
                    dst_ty.structural_eq(&Ty::Int(IntTy { width: IntWidth::I8, signed: true }))
                }
                _ => true,
            }
        })
    })
}

fn cast_types_valid(body: &Body) -> bool {
    body.blocks.iter().all(|bb| {
        bb.statements.iter().all(|stmt| {
            let Some((
                dst_local,
                dst_proj,
                Rvalue::Cast { cast_kind: CastKind::IntToInt, ty: cast_ty, .. },
            )) = stmt.as_assign()
            else {
                return true;
            };
            if !dst_proj.is_empty() {
                return true;
            }
            let Some(dst_ty) = body.local_tys.get(dst_local as usize) else {
                return true;
            };
            dst_ty.structural_eq(cast_ty)
        })
    })
}

const fn bin_op_left_homogeneous(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Add
            | BinOp::AddUnchecked
            | BinOp::Sub
            | BinOp::SubUnchecked
            | BinOp::Mul
            | BinOp::MulUnchecked
            | BinOp::Div
            | BinOp::Rem
            | BinOp::BitXor
            | BinOp::BitAnd
            | BinOp::BitOr
            | BinOp::Offset
            | BinOp::Shl
            | BinOp::ShlUnchecked
            | BinOp::Shr
            | BinOp::ShrUnchecked
    )
}

const fn bin_op_right_homogeneous(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Add
            | BinOp::AddUnchecked
            | BinOp::AddWithOverflow
            | BinOp::Sub
            | BinOp::SubUnchecked
            | BinOp::SubWithOverflow
            | BinOp::Mul
            | BinOp::MulUnchecked
            | BinOp::MulWithOverflow
            | BinOp::Div
            | BinOp::Rem
            | BinOp::BitXor
            | BinOp::BitAnd
            | BinOp::BitOr
            | BinOp::Eq
            | BinOp::Ne
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
            | BinOp::Cmp
    )
}

const fn un_op_homogeneous(op: UnOp) -> bool {
    matches!(op, UnOp::Not | UnOp::Neg)
}

fn local_operand_matches_ty(locals: &[Ty], opnd: &Operand, expected: &Ty) -> bool {
    match opnd.as_place() {
        Some((local, [], _)) => {
            locals.get(local as usize).is_none_or(|src_ty| src_ty.structural_eq(expected))
        }
        _ => true,
    }
}

fn operand_ty_opt<'a>(locals: &'a [Ty], opnd: &'a Operand) -> Option<&'a Ty> {
    match opnd {
        Operand::Constant { ty, .. } => Some(ty),
        _ => match opnd.as_place() {
            Some((local, [], _)) => locals.get(local as usize),
            _ => None,
        },
    }
}

fn assign_types_valid(body: &Body) -> bool {
    body.blocks.iter().all(|bb| {
        bb.statements.iter().all(|stmt| {
            let Some((dst_local, dst_proj, rv)) = stmt.as_assign() else {
                return true;
            };
            if !dst_proj.is_empty() {
                return true;
            }
            let Some(dst_ty) = body.local_tys.get(dst_local as usize) else {
                return true;
            };
            match rv {
                Rvalue::Use { operand, .. } => {
                    local_operand_matches_ty(&body.local_tys, operand, dst_ty)
                }
                Rvalue::Binary { op, left, right } => {
                    let lhs_ok = !bin_op_left_homogeneous(*op)
                        || local_operand_matches_ty(&body.local_tys, left, dst_ty);
                    let rhs_ok = !bin_op_right_homogeneous(*op)
                        || operand_ty_opt(&body.local_tys, left).is_none_or(|l_ty| {
                            local_operand_matches_ty(&body.local_tys, right, l_ty)
                        });
                    lhs_ok && rhs_ok
                }
                Rvalue::Unary { op, operand } => {
                    !un_op_homogeneous(*op)
                        || local_operand_matches_ty(&body.local_tys, operand, dst_ty)
                }
                _ => true,
            }
        })
    })
}

fn move_definitely_disjoint(
    args: &[Operand],
    dst_local: u32,
    dst_projection: &[ProjectionElem],
) -> bool {
    if !dst_projection.is_empty() {
        return false;
    }
    let mut seen = BTreeSet::new();
    for arg in args {
        if let Some((local, proj, true)) = arg.as_place()
            && (!proj.is_empty() || !seen.insert(local))
        {
            return false;
        }
    }
    seen.insert(dst_local)
}

fn call_args_match_body(body_locals: &[Ty], args: &[Operand], param_tys: &[Ty]) -> bool {
    if args.len() != param_tys.len() {
        return false;
    }
    for (opnd, param_ty) in args.iter().zip(param_tys.iter()) {
        let ok = match opnd {
            Operand::Constant { ty, lit } => {
                ty.structural_eq(param_ty) && eval_const_lit(ty, lit).is_ok()
            }
            _ => match opnd.as_place() {
                Some((local, [], _)) => body_locals
                    .get(local as usize)
                    .is_some_and(|arg_ty| arg_ty.structural_eq(param_ty)),
                _ => false,
            },
        };
        if !ok {
            return false;
        }
    }
    true
}

#[allow(clippy::too_many_arguments)]
fn call_target_admitted(
    body: &Body,
    bb: &Block,
    callee_body: &Body,
    args: &[Operand],
    dst_local: u32,
    dst_projection: &[ProjectionElem],
    target: Option<u32>,
    unwind: UnwindAction,
) -> bool {
    if bb.cleanup || matches!(unwind, UnwindAction::Cleanup { .. }) {
        return false;
    }
    if let Some(tgt) = target
        && (tgt as usize) >= body.blocks.len()
    {
        return false;
    }
    if !dst_projection.is_empty() || !move_definitely_disjoint(args, dst_local, dst_projection) {
        return false;
    }
    if args.len() != callee_body.arg_count || callee_body.arg_count >= callee_body.local_tys.len() {
        return false;
    }
    let (Some(dst_ty), Some(ret_ty)) =
        (body.local_tys.get(dst_local as usize), callee_body.local_tys.first())
    else {
        return false;
    };
    if !is_supported_v1_local_ty(dst_ty) || !dst_ty.structural_eq(ret_ty) {
        return false;
    }
    let Some(param_tys) = callee_body.param_tys() else {
        return false;
    };
    call_args_match_body(&body.local_tys, args, param_tys)
}

fn calls_admitted(program: &Program, body: &Body) -> bool {
    body.blocks.iter().all(|bb| match &bb.terminator {
        Terminator::Call { callee, args, dst_local, dst_projection, target, unwind } => {
            let Some(callee_body) = program.bodies.get(*callee as usize) else {
                return false;
            };
            !callee_body.is_unsafe
                && call_target_admitted(
                    body,
                    bb,
                    callee_body,
                    args,
                    *dst_local,
                    dst_projection,
                    *target,
                    *unwind,
                )
        }
        Terminator::SysrootCall { op, args, dst_local, dst_projection, target, unwind } => {
            call_target_admitted(
                body,
                bb,
                &sysroot_num_body(*op),
                args,
                *dst_local,
                dst_projection,
                *target,
                *unwind,
            )
        }
        _ => true,
    })
}

fn body_has_any_call(body: &Body) -> bool {
    body.blocks
        .iter()
        .any(|bb| matches!(bb.terminator, Terminator::Call { .. } | Terminator::SysrootCall { .. }))
}

fn single_body_static_admitted_v1(program: &Program, body: &Body) -> bool {
    program.pointer_width_bits == 64
        && program.mir_profile_version == 1
        && !body.identity.is_empty()
        && !body.blocks.is_empty()
        && body.arg_count < body.local_tys.len()
        && storage_annotations_in_bounds(body)
        && discriminant_types_valid(body)
        && cast_types_valid(body)
        && body.local_tys.iter().all(is_supported_v1_local_ty)
        && calls_admitted(program, body)
}

/// Validate single-body static admission invariants (`BodyStaticAdmitted` /
/// `BodyStaticAdmittedV2` without cross-body call-graph checks).
pub fn validate_body_entry(body: &Body, config: &EvalConfig) -> Result<(), FaultDetail> {
    if body.identity.is_empty() {
        return Err(FaultDetail::unsupported("MIR body identity is empty"));
    }
    if body.blocks.is_empty() {
        return Err(FaultDetail::unsupported("MIR body has no basic blocks"));
    }
    if body.arg_count >= body.local_tys.len() {
        return Err(FaultDetail::unsupported("MIR body arg_count exceeds local_tys length"));
    }
    if !storage_annotations_in_bounds(body) {
        return Err(FaultDetail::unsupported("storage annotation local id out of bounds"));
    }
    if !discriminant_types_valid(body) {
        return Err(FaultDetail::unsupported("discriminant assignment destination type invalid"));
    }
    if !cast_types_valid(body) {
        return Err(FaultDetail::unsupported("cast assignment destination type invalid"));
    }
    if config.enable_profile_v2() && body_mixes_refs_and_raw_ptrs_v2(body) {
        return Err(FaultDetail::unsupported(
            "Profile v2 refuses bodies mixing reference and raw-pointer locals",
        ));
    }
    if config.enable_profile_v2() && !body_fake_address_of_valid_v2(body) {
        return Err(FaultDetail::unsupported(
            "Profile v2 refuses Rvalue::FakeAddressOf outside metadata-only temporaries",
        ));
    }
    if !body.local_tys.iter().all(|ty| is_supported_local_ty(ty, config.enable_profile_v2())) {
        return Err(FaultDetail::unsupported("body contains unsupported local variable type"));
    }
    Ok(())
}

/// Validate full program-aware static admission for `body` inside `program`,
/// including Profile v1 `callsAdmitted` and `allCallBodiesStaticAdmitted`.
pub fn validate_body_in_program(
    program: &Program,
    body: &Body,
    config: &EvalConfig,
) -> Result<(), FaultDetail> {
    validate_body_entry(body, config)?;
    if config.is_strict_profile_v1() {
        if !calls_admitted(program, body) {
            return Err(FaultDetail::unsupported(
                "Profile v1 call terminator fails static admission (missing/unsafe callee, \
                 mismatched signature, aliasing move, or cleanup unwind)",
            ));
        }
        if body_has_any_call(body)
            && (!assign_types_valid(body)
                || !program
                    .bodies
                    .iter()
                    .all(|b| single_body_static_admitted_v1(program, b) && assign_types_valid(b)))
        {
            return Err(FaultDetail::unsupported(
                "calling program fails transitive Profile v1 body static admission",
            ));
        }
    }
    Ok(())
}

fn init_locals(body: &Body, args: &[Val]) -> Vec<LocalSlot> {
    let mut locals = Vec::with_capacity(body.local_tys.len());
    for (idx, ty) in body.local_tys.iter().enumerate() {
        let slot = if idx == 0 {
            live_uninit_slot(ty)
        } else if idx <= body.arg_count {
            match args.get(idx - 1) {
                Some(v) => LocalSlot::Immediate { val: Some(v.clone()) },
                None => LocalSlot::Dead,
            }
        } else if has_storage_annotation(body, idx) {
            LocalSlot::Dead
        } else {
            live_uninit_slot(ty)
        };
        locals.push(slot);
    }
    locals
}

fn deallocate_local(
    mem: &mut MemoryState,
    move_deinit_bytes: &mut BTreeSet<(u64, u64)>,
    old: &LocalSlot,
) -> Result<(), FaultDetail> {
    match old {
        LocalSlot::Indirect { place } => {
            mem.deallocate_stack(*place)?;
            clear_move_deinit_alloc(move_deinit_bytes, place.alloc_id);
            Ok(())
        }
        LocalSlot::Dead | LocalSlot::Immediate { .. } | LocalSlot::PartialTuple { .. } => Ok(()),
    }
}

fn tuple_field_tys(ty: &Ty) -> Option<Vec<Ty>> {
    if let Some(ity) = ty.as_overflow_pair() {
        Some(vec![Ty::Int(ity), Ty::Bool])
    } else if let Ty::Tuple { fields } = ty {
        Some(fields.clone())
    } else {
        None
    }
}

// =============================================================================
// Profile v1 Expression & Place Helpers (`Step.lean:100-406`)
// =============================================================================

fn eval_operand_to_slot_v1<F>(
    body_locals: &[Ty],
    locals: &mut [LocalSlot],
    moved: &mut MoveTracker<'_>,
    mem: &mut MemoryState,
    ty_ok: F,
    opnd: &Operand,
    endian: TargetEndian,
) -> Result<(Ty, ReadSlotVal), FaultDetail>
where
    F: Fn(&Ty) -> bool,
{
    match opnd {
        Operand::Constant { ty, lit } => {
            let val = eval_const_lit(ty, lit)?;
            Ok((ty.clone(), ReadSlotVal::Init(val)))
        }
        _ => {
            let Some((local, projection, is_move)) = opnd.as_place() else {
                return Err(FaultDetail::unsupported("unexpected operand variant"));
            };
            let idx = local as usize;
            let (Some(base_ty), Some(slot)) = (body_locals.get(idx), locals.get(idx).cloned())
            else {
                return Err(FaultDetail::unsupported("operand local out of bounds"));
            };
            match slot {
                LocalSlot::Dead => Err(FaultDetail::undefined_classified(
                    UbClass::DeadLocalAccess,
                    if is_move { "Move from dead local" } else { "Copy from dead local" },
                )),
                LocalSlot::PartialTuple { .. } => {
                    Err(FaultDetail::unsupported("partially moved tuple unsupported in Profile v1"))
                }
                LocalSlot::Immediate { val } => {
                    if !projection.is_empty() {
                        return Err(FaultDetail::unsupported(
                            "projected operand unsupported in Profile v1",
                        ));
                    }
                    let slot_val = match val {
                        Some(v) => {
                            if is_move {
                                let next_slot = live_uninit_slot(base_ty);
                                if matches!(next_slot, LocalSlot::Immediate { val: None }) {
                                    moved.mark_local(local);
                                }
                                locals[idx] = next_slot;
                            }
                            ReadSlotVal::Init(v)
                        }
                        None => {
                            let class = moved.as_view().uninit_local(local);
                            if is_move {
                                locals[idx] = live_uninit_slot(base_ty);
                            }
                            ReadSlotVal::Uninit(class)
                        }
                    };
                    Ok((base_ty.clone(), slot_val))
                }
                LocalSlot::Indirect { place } => {
                    if !projection.is_empty() {
                        return Err(FaultDetail::unsupported(
                            "projected operand unsupported in Profile v1",
                        ));
                    }
                    if !ty_ok(base_ty) {
                        return Err(FaultDetail::unsupported(
                            "operand type rejected before indirect load",
                        ));
                    }
                    let val = load_indirect(mem, endian, base_ty, place, false)?;
                    let slot_val = match val {
                        Some(v) => {
                            if is_move {
                                deinit_indirect_tracked(mem, moved, base_ty, place, false)?;
                                if layout_of_ty(base_ty, false).is_some_and(|l| l.size > 0) {
                                    moved.mark_local(local);
                                }
                            }
                            ReadSlotVal::Init(v)
                        }
                        None => {
                            let class =
                                moved.as_view().uninit_indirect_local(local, place, base_ty, false);
                            if is_move {
                                deinit_indirect(mem, base_ty, place, false)?;
                            }
                            ReadSlotVal::Uninit(class)
                        }
                    };
                    Ok((base_ty.clone(), slot_val))
                }
            }
        }
    }
}

fn eval_primitive_operand_v1(
    body_locals: &[Ty],
    locals: &mut [LocalSlot],
    moved: &mut MoveTracker<'_>,
    mem: &mut MemoryState,
    opnd: &Operand,
    endian: TargetEndian,
) -> Result<Val, FaultDetail> {
    let (ty, slot_val) = eval_operand_to_slot_v1(
        body_locals,
        locals,
        moved,
        mem,
        is_primitive_readable_ty,
        opnd,
        endian,
    )?;
    if !is_primitive_readable_ty(&ty) {
        return Err(FaultDetail::unsupported("non-primitive operand type"));
    }
    match slot_val {
        ReadSlotVal::Init(v) => Ok(v),
        ReadSlotVal::Uninit(class) => {
            Err(FaultDetail::undefined_classified(class, "reading uninitialized primitive operand"))
        }
    }
}

fn eval_rvalue_v1(
    body_locals: &[Ty],
    locals: &mut [LocalSlot],
    moved: &mut MoveTracker<'_>,
    mem: &mut MemoryState,
    dst_ty: &Ty,
    rvalue: &Rvalue,
    endian: TargetEndian,
) -> Result<Val, FaultDetail> {
    match rvalue {
        Rvalue::Use { operand, with_retag } => {
            if *with_retag && !dst_ty.is_retag_noop() {
                return Err(FaultDetail::unsupported(
                    "retagging Use rvalue on reference-bearing type is unsupported",
                ));
            }
            let (src_ty, slot_val) = eval_operand_to_slot_v1(
                body_locals,
                locals,
                moved,
                mem,
                |src_ty| src_ty.structural_eq(dst_ty),
                operand,
                endian,
            )?;
            if !src_ty.structural_eq(dst_ty) {
                return Err(FaultDetail::unsupported(
                    "Use operand type disagrees with destination type",
                ));
            }
            match slot_val {
                ReadSlotVal::Init(v) => Ok(v),
                ReadSlotVal::Uninit(class) => {
                    Err(FaultDetail::undefined_classified(class, "Use reading uninitialized value"))
                }
            }
        }
        Rvalue::Binary { op, left, right } => {
            let l_val = eval_primitive_operand_v1(body_locals, locals, moved, mem, left, endian)?;
            let r_val = eval_primitive_operand_v1(body_locals, locals, moved, mem, right, endian)?;
            eval_bin_op(*op, &l_val, &r_val)
        }
        Rvalue::Unary { op, operand } => {
            let val = eval_primitive_operand_v1(body_locals, locals, moved, mem, operand, endian)?;
            eval_un_op(*op, &val)
        }
        Rvalue::Cast { cast_kind: CastKind::IntToInt, operand, ty } => {
            if !dst_ty.structural_eq(ty) {
                return Err(FaultDetail::unsupported("cast assignment destination type invalid"));
            }
            let (src_ty, slot_val) = eval_operand_to_slot_v1(
                body_locals,
                locals,
                moved,
                mem,
                is_int_like_ty,
                operand,
                endian,
            )?;
            if !is_int_like_ty(&src_ty) {
                return Err(FaultDetail::unsupported("cast source is not integer-like"));
            }
            let ReadSlotVal::Init(v) = slot_val else {
                let ReadSlotVal::Uninit(class) = slot_val else { unreachable!() };
                return Err(FaultDetail::undefined_classified(
                    class,
                    "Cast reading uninitialized operand",
                ));
            };
            eval_int_to_int_cast(CastKind::IntToInt, &v, ty)
        }
        Rvalue::Discriminant { place } => eval_discriminant_rvalue(
            body_locals,
            locals,
            moved.as_view(),
            mem,
            place.local,
            &place.projection,
            dst_ty,
            endian,
            false,
        ),
        _ => Err(FaultDetail::unsupported("unmodeled Profile v1 MIR rvalue")),
    }
}

fn write_place_v1(
    locals: &mut [LocalSlot],
    moved: &mut MoveTracker<'_>,
    mem: &mut MemoryState,
    dst_local_id: u32,
    dst_ty: &Ty,
    val: Val,
    endian: TargetEndian,
) -> Result<(), FaultDetail> {
    if !check_val(&val, dst_ty, false) {
        return Err(FaultDetail::unsupported("assigned value disagrees with destination type"));
    }
    let Some(slot) = locals.get_mut(dst_local_id as usize) else {
        return Err(FaultDetail::unsupported("destination local id out of bounds"));
    };
    match slot {
        LocalSlot::Dead => Err(FaultDetail::undefined_classified(
            UbClass::DeadLocalAccess,
            "write to dead destination local",
        )),
        LocalSlot::Immediate { .. } => {
            *slot = LocalSlot::Immediate { val: Some(val) };
            moved.clear_local(dst_local_id);
            Ok(())
        }
        LocalSlot::Indirect { place } => {
            store_indirect_tracked(mem, moved, endian, dst_ty, *place, &val, false)?;
            moved.clear_local(dst_local_id);
            Ok(())
        }
        LocalSlot::PartialTuple { .. } => {
            Err(FaultDetail::unsupported("partially moved tuple destination in Profile v1"))
        }
    }
}

// =============================================================================
// Profile v2 Expression, Place, & CoreCall Helpers (`Step.lean:755-1936`)
// =============================================================================

#[derive(Clone, Debug)]
enum PlaceDestV2 {
    Local(u32),
    Deref { pointee: Ty, lay: LayoutData, pv: PtrVal },
}

fn place_static_ty_v2(body_locals: &[Ty], local: u32, projection: &[ProjectionElem]) -> Option<Ty> {
    let base = body_locals.get(local as usize)?;
    match projection {
        [] => Some(base.clone()),
        [ProjectionElem::Deref] => match base {
            Ty::Ref { pointee, .. } | Ty::RawPtr { pointee, .. } if !pointee.is_unsized() => {
                Some((**pointee).clone())
            }
            _ => None,
        },
        _ => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn resolve_place_dest_v2(
    body_locals: &[Ty],
    locals: &[LocalSlot],
    moved: MoveView<'_>,
    mem: &MemoryState,
    local: u32,
    projection: &[ProjectionElem],
    dst_ty: &Ty,
    endian: TargetEndian,
) -> Result<PlaceDestV2, FaultDetail> {
    match projection {
        [] => Ok(PlaceDestV2::Local(local)),
        [ProjectionElem::Deref] => {
            let (Some(ptr_ty), Some(slot)) =
                (body_locals.get(local as usize), locals.get(local as usize))
            else {
                return Err(FaultDetail::unsupported("deref destination local out of bounds"));
            };
            if matches!(slot, LocalSlot::Dead) {
                return Err(FaultDetail::undefined_classified(
                    UbClass::DeadLocalAccess,
                    "deref destination pointer local is storage-dead",
                ));
            }
            let (ptr_mut, pointee) = match ptr_ty {
                Ty::Ref { mutability, pointee } | Ty::RawPtr { mutability, pointee } => {
                    (*mutability, pointee.as_ref())
                }
                _ => {
                    return Err(FaultDetail::unsupported(
                        "deref destination requires pointer or reference local",
                    ));
                }
            };
            if pointee.is_unsized() || !pointee.structural_eq(dst_ty) {
                return Err(FaultDetail::unsupported(
                    "deref destination pointee type mismatch or unsized",
                ));
            }
            if ptr_mut != Mutability::Mut {
                return Err(FaultDetail::undefined(
                    "store through shared reference or *const pointer",
                ));
            }
            let Some(lay) = layout_of_ty(pointee, true) else {
                return Err(FaultDetail::unsupported("deref destination pointee has no layout"));
            };
            let ptr_val = match slot {
                LocalSlot::Dead => unreachable!("checked above"),
                LocalSlot::PartialTuple { .. } => {
                    return Err(FaultDetail::undefined_classified(
                        UbClass::MoveDeinitLocalRead,
                        "deref destination pointer local is partially moved",
                    ));
                }
                LocalSlot::Immediate { val } => val.clone().ok_or_else(|| {
                    FaultDetail::undefined_classified(
                        moved.uninit_local(local),
                        "deref destination pointer local is uninitialized",
                    )
                })?,
                LocalSlot::Indirect { place } => load_indirect(mem, endian, ptr_ty, *place, true)?
                    .ok_or_else(|| {
                        FaultDetail::undefined_classified(
                            moved.uninit_indirect_local(local, *place, ptr_ty, true),
                            "deref destination pointer local is uninitialized",
                        )
                    })?,
            };
            match ptr_val {
                Val::Ptr(pv) => Ok(PlaceDestV2::Deref { pointee: pointee.clone(), lay, pv }),
                _ => Err(FaultDetail::unsupported("deref destination slot does not hold thin ptr")),
            }
        }
        _ => {
            Err(FaultDetail::unsupported("unsupported destination place projection in Profile v2"))
        }
    }
}

fn write_place_dest_v2(
    locals: &mut [LocalSlot],
    moved: &mut MoveTracker<'_>,
    mem: &mut MemoryState,
    dest: &PlaceDestV2,
    dst_ty: &Ty,
    val: Val,
    endian: TargetEndian,
) -> Result<(), FaultDetail> {
    if !check_val(&val, dst_ty, true) {
        return Err(FaultDetail::unsupported(
            "assigned value disagrees with Profile v2 destination type",
        ));
    }
    match dest {
        PlaceDestV2::Local(local_id) => {
            let Some(slot) = locals.get_mut(*local_id as usize) else {
                return Err(FaultDetail::unsupported("destination local id out of bounds"));
            };
            match slot {
                LocalSlot::Dead => Err(FaultDetail::undefined_classified(
                    UbClass::DeadLocalAccess,
                    "write to dead destination local",
                )),
                LocalSlot::Immediate { .. } | LocalSlot::PartialTuple { .. } => {
                    *slot = LocalSlot::Immediate { val: Some(val) };
                    moved.clear_local(*local_id);
                    Ok(())
                }
                LocalSlot::Indirect { place } => {
                    store_indirect_tracked(mem, moved, endian, dst_ty, *place, &val, true)?;
                    moved.clear_local(*local_id);
                    Ok(())
                }
            }
        }
        PlaceDestV2::Deref { pointee, lay, pv } => match pv.alloc_id {
            None => {
                if pv.offset_bytes == 0 {
                    let class = if lay.size == 0 {
                        UbClass::ZstNullRawPtrDeref
                    } else {
                        UbClass::NullOrNoProvPtrAccess
                    };
                    return Err(FaultDetail::undefined_classified(
                        class,
                        "write through null pointer",
                    ));
                }
                if lay.size > 0 {
                    return Err(FaultDetail::undefined_classified(
                        UbClass::NullOrNoProvPtrAccess,
                        "non-zero-sized write through provenance-free pointer",
                    ));
                }
                if !offset_is_aligned(pv.offset_bytes, lay.align_log2) {
                    return Err(FaultDetail::undefined_classified(
                        UbClass::MisalignedMemoryAccess,
                        "misaligned zero-sized write through provenance-free pointer",
                    ));
                }
                let encoded = encode_val(endian, pointee, &val, true)?;
                if encoded.is_empty() {
                    Ok(())
                } else {
                    Err(FaultDetail::unsupported("zero-sized pointee encoded non-empty bytes"))
                }
            }
            Some(aid) => {
                let Some(alloc) = mem.find(aid) else {
                    let class = if lay.size == 0 {
                        UbClass::ZstProvenanceDeadOrOob
                    } else {
                        UbClass::DanglingOrUnknownAllocAccess
                    };
                    return Err(FaultDetail::undefined_classified(
                        class,
                        "write through pointer to unknown allocation",
                    ));
                };
                if lay.size > 0 {
                    if !alloc.live {
                        return Err(FaultDetail::undefined_classified(
                            UbClass::DanglingOrUnknownAllocAccess,
                            "write through dangling pointer",
                        ));
                    }
                    if alloc.mutability != Mutability::Mut {
                        return Err(FaultDetail::undefined_classified(
                            UbClass::WriteToReadOnlyMemory,
                            "write through pointer to immutable allocation",
                        ));
                    }
                }
                store_indirect_tracked(
                    mem,
                    moved,
                    endian,
                    pointee,
                    MemPlace { alloc_id: aid, offset: pv.offset_bytes },
                    &val,
                    true,
                )
            }
        },
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CopyReprV2 {
    Zst { align_log2: u32 },
    Scalar { align_log2: u32 },
    ScalarPair { elem_align_log2: u32 },
    MemoryCopy,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TupleCopyPayloadV2 {
    None,
    OneScalar(u32),
    TwoScalars(u32),
    Memory,
}

fn layout_of_array_elem_v2(ty: &Ty) -> Option<LayoutData> {
    match ty {
        Ty::Array { elem, len } => {
            let elem_lay = layout_of_array_elem_v2(elem)?;
            Some(LayoutData {
                size: len.checked_mul(elem_lay.size)?,
                align_log2: elem_lay.align_log2,
            })
        }
        other => layout_of_ty(other, true),
    }
}

fn copy_repr_of_ty_v2(ty: &Ty) -> CopyReprV2 {
    if let Some(ity) = ty.as_overflow_pair() {
        let a = int_layout(ity.width).align_log2;
        return if a == 0 {
            CopyReprV2::ScalarPair { elem_align_log2: 0 }
        } else {
            CopyReprV2::MemoryCopy
        };
    }
    match ty {
        Ty::Unit | Ty::Never => CopyReprV2::Zst { align_log2: 0 },
        Ty::Bool | Ty::Ordering => CopyReprV2::Scalar { align_log2: 0 },
        Ty::Int(ity) => CopyReprV2::Scalar { align_log2: int_layout(ity.width).align_log2 },
        Ty::Char => CopyReprV2::Scalar { align_log2: 2 },
        Ty::Enum(ety) => {
            if !enum_admitted(ety) {
                CopyReprV2::MemoryCopy
            } else {
                match ety.tag_repr {
                    EnumTagRepr::ZeroSized => CopyReprV2::Zst { align_log2: 0 },
                    EnumTagRepr::Scalar(tag) => {
                        CopyReprV2::Scalar { align_log2: int_layout(tag.width).align_log2 }
                    }
                }
            }
        }
        Ty::RangeTo { elem } | Ty::RangeFrom { elem } if elem.is_usize() => {
            CopyReprV2::Scalar { align_log2: 3 }
        }
        Ty::Ref { pointee, .. } | Ty::RawPtr { pointee, .. } => {
            if pointee.is_unsized() {
                CopyReprV2::ScalarPair { elem_align_log2: 3 }
            } else {
                CopyReprV2::Scalar { align_log2: 3 }
            }
        }
        Ty::Array { elem, len } => match copy_repr_of_ty_v2(elem) {
            CopyReprV2::Zst { align_log2 } => CopyReprV2::Zst { align_log2 },
            CopyReprV2::Scalar { align_log2 }
            | CopyReprV2::ScalarPair { elem_align_log2: align_log2 } => {
                if *len == 0 {
                    CopyReprV2::Zst { align_log2 }
                } else {
                    CopyReprV2::MemoryCopy
                }
            }
            CopyReprV2::MemoryCopy => {
                if *len == 0 {
                    match layout_of_array_elem_v2(elem) {
                        Some(lay) => CopyReprV2::Zst { align_log2: lay.align_log2 },
                        None => CopyReprV2::MemoryCopy,
                    }
                } else {
                    CopyReprV2::MemoryCopy
                }
            }
        },
        Ty::Tuple { fields } => {
            let mut max_align = 0u32;
            let mut payload = TupleCopyPayloadV2::None;
            for f in fields {
                match copy_repr_of_ty_v2(f) {
                    CopyReprV2::Zst { align_log2 } => {
                        max_align = max_align.max(align_log2);
                    }
                    CopyReprV2::Scalar { align_log2 } => {
                        max_align = max_align.max(align_log2);
                        payload = match payload {
                            TupleCopyPayloadV2::None => TupleCopyPayloadV2::OneScalar(align_log2),
                            TupleCopyPayloadV2::OneScalar(a0) if a0 == align_log2 => {
                                TupleCopyPayloadV2::TwoScalars(a0)
                            }
                            _ => TupleCopyPayloadV2::Memory,
                        };
                    }
                    CopyReprV2::ScalarPair { elem_align_log2 } => {
                        max_align = max_align.max(elem_align_log2);
                        payload = match payload {
                            TupleCopyPayloadV2::None => {
                                TupleCopyPayloadV2::TwoScalars(elem_align_log2)
                            }
                            _ => TupleCopyPayloadV2::Memory,
                        };
                    }
                    CopyReprV2::MemoryCopy => {
                        payload = TupleCopyPayloadV2::Memory;
                    }
                }
            }
            match payload {
                TupleCopyPayloadV2::None => CopyReprV2::Zst { align_log2: max_align },
                TupleCopyPayloadV2::OneScalar(a) => {
                    if max_align <= a {
                        CopyReprV2::Scalar { align_log2: a }
                    } else {
                        CopyReprV2::MemoryCopy
                    }
                }
                TupleCopyPayloadV2::TwoScalars(a) => {
                    if max_align <= a {
                        CopyReprV2::ScalarPair { elem_align_log2: a }
                    } else {
                        CopyReprV2::MemoryCopy
                    }
                }
                TupleCopyPayloadV2::Memory => CopyReprV2::MemoryCopy,
            }
        }
        Ty::OverflowPair(_)
        | Ty::Slice { .. }
        | Ty::RangeTo { .. }
        | Ty::RangeFrom { .. }
        | Ty::Unsupported => CopyReprV2::MemoryCopy,
    }
}

fn is_memory_copy_repr_ty_v2(ty: &Ty) -> bool {
    matches!(copy_repr_of_ty_v2(ty), CopyReprV2::MemoryCopy)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OverlapReplayKindV2 {
    /// True `BackendRepr::Memory` (always copied via `copy_nonoverlapping` in Miri).
    AlwaysBackendMemory,
    /// Padded `ScalarPair` (triggers `copy_nonoverlapping` UB in Miri only when
    /// the source place is in memory / indirect, not an immediate local).
    PaddedScalarPair,
    /// Conservative model-only over-approximation (e.g. unmodeled/unknown types).
    ConservativeModelOnly,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OverlapAbiReprV2 {
    Zst { align_log2: u32 },
    Scalar { align_log2: u32 },
    ScalarPair { a0: u32, a1: u32 },
    Memory { align_log2: u32 },
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TupleOverlapPayloadV2 {
    None,
    OneScalar(u32),
    TwoScalars(u32, u32),
    Memory,
}

fn overlap_abi_repr_v2(ty: &Ty) -> OverlapAbiReprV2 {
    match ty {
        Ty::Unit | Ty::Never => OverlapAbiReprV2::Zst { align_log2: 0 },
        Ty::Bool | Ty::Ordering => OverlapAbiReprV2::Scalar { align_log2: 0 },
        Ty::Int(ity) => OverlapAbiReprV2::Scalar { align_log2: int_layout(ity.width).align_log2 },
        Ty::Char => OverlapAbiReprV2::Scalar { align_log2: 2 },
        Ty::Enum(ety) => {
            if !enum_admitted(ety) {
                OverlapAbiReprV2::Unknown
            } else {
                match ety.tag_repr {
                    EnumTagRepr::ZeroSized => OverlapAbiReprV2::Zst { align_log2: 0 },
                    EnumTagRepr::Scalar(tag) => {
                        OverlapAbiReprV2::Scalar { align_log2: int_layout(tag.width).align_log2 }
                    }
                }
            }
        }
        Ty::RangeTo { elem } | Ty::RangeFrom { elem } if elem.is_usize() => {
            OverlapAbiReprV2::Scalar { align_log2: 3 }
        }
        Ty::Ref { pointee, .. } | Ty::RawPtr { pointee, .. } => {
            if pointee.is_unsized() {
                OverlapAbiReprV2::ScalarPair { a0: 3, a1: 3 }
            } else {
                OverlapAbiReprV2::Scalar { align_log2: 3 }
            }
        }
        Ty::OverflowPair(ity) => {
            OverlapAbiReprV2::ScalarPair { a0: int_layout(ity.width).align_log2, a1: 0 }
        }
        Ty::Array { elem, len } => match overlap_abi_repr_v2(elem) {
            OverlapAbiReprV2::Zst { align_log2 } => OverlapAbiReprV2::Zst { align_log2 },
            OverlapAbiReprV2::Scalar { align_log2 } | OverlapAbiReprV2::Memory { align_log2 } => {
                if *len == 0 {
                    OverlapAbiReprV2::Zst { align_log2 }
                } else {
                    OverlapAbiReprV2::Memory { align_log2 }
                }
            }
            OverlapAbiReprV2::ScalarPair { a0, a1 } => {
                let align_log2 = a0.max(a1);
                if *len == 0 {
                    OverlapAbiReprV2::Zst { align_log2 }
                } else {
                    OverlapAbiReprV2::Memory { align_log2 }
                }
            }
            OverlapAbiReprV2::Unknown => OverlapAbiReprV2::Unknown,
        },
        Ty::Tuple { fields } => {
            let mut max_align = 0u32;
            let mut payload = TupleOverlapPayloadV2::None;
            for f in fields {
                match overlap_abi_repr_v2(f) {
                    OverlapAbiReprV2::Zst { align_log2 } => {
                        max_align = max_align.max(align_log2);
                    }
                    OverlapAbiReprV2::Scalar { align_log2 } => {
                        max_align = max_align.max(align_log2);
                        payload = match payload {
                            TupleOverlapPayloadV2::None => {
                                TupleOverlapPayloadV2::OneScalar(align_log2)
                            }
                            TupleOverlapPayloadV2::OneScalar(a0) => {
                                TupleOverlapPayloadV2::TwoScalars(a0, align_log2)
                            }
                            TupleOverlapPayloadV2::TwoScalars(..)
                            | TupleOverlapPayloadV2::Memory => TupleOverlapPayloadV2::Memory,
                        };
                    }
                    OverlapAbiReprV2::ScalarPair { a0, a1 } => {
                        max_align = max_align.max(a0).max(a1);
                        payload = match payload {
                            TupleOverlapPayloadV2::None => {
                                TupleOverlapPayloadV2::TwoScalars(a0, a1)
                            }
                            TupleOverlapPayloadV2::OneScalar(..)
                            | TupleOverlapPayloadV2::TwoScalars(..)
                            | TupleOverlapPayloadV2::Memory => TupleOverlapPayloadV2::Memory,
                        };
                    }
                    OverlapAbiReprV2::Memory { align_log2 } => {
                        max_align = max_align.max(align_log2);
                        payload = TupleOverlapPayloadV2::Memory;
                    }
                    OverlapAbiReprV2::Unknown => return OverlapAbiReprV2::Unknown,
                }
            }
            match payload {
                TupleOverlapPayloadV2::None => OverlapAbiReprV2::Zst { align_log2: max_align },
                TupleOverlapPayloadV2::OneScalar(a) => {
                    if max_align > a {
                        OverlapAbiReprV2::Memory { align_log2: max_align }
                    } else {
                        OverlapAbiReprV2::Scalar { align_log2: a }
                    }
                }
                TupleOverlapPayloadV2::TwoScalars(a0, a1) => {
                    if max_align > a0.max(a1) {
                        OverlapAbiReprV2::Memory { align_log2: max_align }
                    } else {
                        OverlapAbiReprV2::ScalarPair { a0, a1 }
                    }
                }
                TupleOverlapPayloadV2::Memory => OverlapAbiReprV2::Memory { align_log2: max_align },
            }
        }
        Ty::Slice { .. } | Ty::RangeTo { .. } | Ty::RangeFrom { .. } | Ty::Unsupported => {
            OverlapAbiReprV2::Unknown
        }
    }
}

fn overlap_replay_kind_v2(ty: &Ty) -> OverlapReplayKindV2 {
    match overlap_abi_repr_v2(ty) {
        OverlapAbiReprV2::Memory { .. } => OverlapReplayKindV2::AlwaysBackendMemory,
        OverlapAbiReprV2::ScalarPair { a0, a1 } if a0 != a1 => {
            OverlapReplayKindV2::PaddedScalarPair
        }
        _ => OverlapReplayKindV2::ConservativeModelOnly,
    }
}

fn overlapping_copy_ub_class_v2(ty: &Ty, src_span: &CopyPlaceSpanV2) -> UbClass {
    match overlap_replay_kind_v2(ty) {
        OverlapReplayKindV2::AlwaysBackendMemory => UbClass::OverlappingMemoryCopy,
        OverlapReplayKindV2::PaddedScalarPair => {
            if matches!(src_span, CopyPlaceSpanV2::MemRange { .. }) {
                UbClass::OverlappingMemoryCopy
            } else {
                UbClass::ConservativeOverlappingAssignCopy
            }
        }
        OverlapReplayKindV2::ConservativeModelOnly => UbClass::ConservativeOverlappingAssignCopy,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum CopyPlaceSpanV2 {
    MemRange { alloc_id: u64, offset: u64, size: u64 },
    ImmPath { local_id: u32, steps: Vec<u32> },
}

fn imm_proj_prefix_sym_v2(a: &[u32], b: &[u32]) -> bool {
    a.iter().zip(b.iter()).all(|(x, y)| x == y)
}

fn copy_spans_overlap_v2(a: &CopyPlaceSpanV2, b: &CopyPlaceSpanV2) -> bool {
    match (a, b) {
        (
            CopyPlaceSpanV2::MemRange { alloc_id: a1, offset: o1, size: s1 },
            CopyPlaceSpanV2::MemRange { alloc_id: a2, offset: o2, size: s2 },
        ) => {
            a1 == a2
                && *s1 > 0
                && *s2 > 0
                && u128::from(*o1) < u128::from(*o2) + u128::from(*s2)
                && u128::from(*o2) < u128::from(*o1) + u128::from(*s1)
        }
        (
            CopyPlaceSpanV2::ImmPath { local_id: l1, steps: p1 },
            CopyPlaceSpanV2::ImmPath { local_id: l2, steps: p2 },
        ) => l1 == l2 && imm_proj_prefix_sym_v2(p1, p2),
        _ => false,
    }
}

fn normalize_imm_proj_path_v2(base_ty: &Ty, projs: &[ProjectionElem]) -> Option<Vec<u32>> {
    let mut cur_ty = base_ty.clone();
    let mut steps = Vec::with_capacity(projs.len());
    for elem in projs {
        let ProjectionElem::Field { field_idx, ty: f_ty } = elem else {
            return None;
        };
        let idx = *field_idx as usize;
        if let Some(ts) = tuple_field_tys(&cur_ty) {
            let elem_ty = ts.get(idx)?;
            if !elem_ty.structural_eq(f_ty) {
                return None;
            }
            steps.push(*field_idx);
            cur_ty = elem_ty.clone();
        } else if matches!(
            &cur_ty,
            Ty::RangeTo { elem } | Ty::RangeFrom { elem } if elem.is_usize()
        ) && *field_idx == 0
            && f_ty.is_usize()
        {
            steps.push(0);
            cur_ty = Ty::Int(IntTy { width: IntWidth::Isize, signed: false });
        } else {
            return None;
        }
    }
    Some(steps)
}

fn project_memory_field_layout_v2(base_ty: &Ty, projs: &[ProjectionElem]) -> Option<(Ty, u64)> {
    let mut cur_ty = base_ty.clone();
    let mut off = 0u64;
    for elem in projs {
        let ProjectionElem::Field { field_idx, ty: f_ty } = elem else {
            return None;
        };
        if let Some(ity) = cur_ty.as_overflow_pair() {
            match *field_idx {
                0 => {
                    let expected = Ty::Int(ity);
                    if !expected.structural_eq(f_ty) {
                        return None;
                    }
                    cur_ty = expected;
                }
                1 => {
                    if *f_ty != Ty::Bool {
                        return None;
                    }
                    off = off.checked_add(int_layout(ity.width).size)?;
                    cur_ty = Ty::Bool;
                }
                _ => return None,
            }
        } else if matches!(
            &cur_ty,
            Ty::RangeTo { elem } | Ty::RangeFrom { elem } if elem.is_usize()
        ) && *field_idx == 0
            && f_ty.is_usize()
        {
            cur_ty = Ty::Int(IntTy { width: IntWidth::Isize, signed: false });
        } else {
            return None;
        }
    }
    Some((cur_ty, off))
}

fn dest_copy_span_v2(
    locals: &[LocalSlot],
    dest: &PlaceDestV2,
    dst_ty: &Ty,
) -> Option<CopyPlaceSpanV2> {
    match dest {
        PlaceDestV2::Local(lid) => match locals.get(*lid as usize)? {
            LocalSlot::Indirect { place } => {
                let lay = layout_of_ty(dst_ty, true)?;
                Some(CopyPlaceSpanV2::MemRange {
                    alloc_id: place.alloc_id,
                    offset: place.offset,
                    size: lay.size,
                })
            }
            LocalSlot::Immediate { .. } | LocalSlot::PartialTuple { .. } => {
                Some(CopyPlaceSpanV2::ImmPath { local_id: *lid, steps: Vec::new() })
            }
            LocalSlot::Dead => None,
        },
        PlaceDestV2::Deref { lay, pv, .. } => pv.alloc_id.map(|alloc_id| {
            CopyPlaceSpanV2::MemRange { alloc_id, offset: pv.offset_bytes, size: lay.size }
        }),
    }
}

fn dest_aggregate_sub_span_v2(
    base: &CopyPlaceSpanV2,
    agg_ty: &Ty,
    idx: usize,
) -> Option<CopyPlaceSpanV2> {
    let idx_u32 = u32::try_from(idx).ok()?;
    match base {
        CopyPlaceSpanV2::ImmPath { local_id, steps } => {
            let mut next = steps.clone();
            next.push(idx_u32);
            Some(CopyPlaceSpanV2::ImmPath { local_id: *local_id, steps: next })
        }
        CopyPlaceSpanV2::MemRange { alloc_id, offset, .. } => {
            let ity = agg_ty.as_overflow_pair()?;
            match idx {
                0 => Some(CopyPlaceSpanV2::MemRange {
                    alloc_id: *alloc_id,
                    offset: *offset,
                    size: int_layout(ity.width).size,
                }),
                1 => Some(CopyPlaceSpanV2::MemRange {
                    alloc_id: *alloc_id,
                    offset: offset.checked_add(int_layout(ity.width).size)?,
                    size: 1,
                }),
                _ => None,
            }
        }
    }
}

fn src_place_copy_span_v2(
    body_locals: &[Ty],
    locals: &[LocalSlot],
    mem: &MemoryState,
    local: u32,
    projection: &[ProjectionElem],
    endian: TargetEndian,
) -> Option<CopyPlaceSpanV2> {
    let base_ty = body_locals.get(local as usize)?;
    let slot = locals.get(local as usize)?;
    match projection {
        [] => match slot {
            LocalSlot::Indirect { place } => {
                let lay = layout_of_ty(base_ty, true)?;
                Some(CopyPlaceSpanV2::MemRange {
                    alloc_id: place.alloc_id,
                    offset: place.offset,
                    size: lay.size,
                })
            }
            LocalSlot::Immediate { .. } | LocalSlot::PartialTuple { .. } => {
                Some(CopyPlaceSpanV2::ImmPath { local_id: local, steps: Vec::new() })
            }
            LocalSlot::Dead => None,
        },
        [ProjectionElem::Deref, rest @ ..] => {
            let pointee = match base_ty {
                Ty::Ref { pointee, .. } | Ty::RawPtr { pointee, .. } => pointee.as_ref(),
                _ => return None,
            };
            let ptr_val = match slot {
                LocalSlot::Immediate { val } => val.clone()?,
                LocalSlot::Indirect { place } => {
                    load_indirect(mem, endian, base_ty, *place, true).ok()??
                }
                LocalSlot::Dead | LocalSlot::PartialTuple { .. } => return None,
            };
            let Val::Ptr(pv) = ptr_val else { return None };
            let alloc_id = pv.alloc_id?;
            if rest.is_empty() {
                let lay = layout_of_ty(pointee, true)?;
                Some(CopyPlaceSpanV2::MemRange {
                    alloc_id,
                    offset: pv.offset_bytes,
                    size: lay.size,
                })
            } else {
                let (leaf_ty, sub_off) = project_memory_field_layout_v2(pointee, rest)?;
                let lay = layout_of_ty(&leaf_ty, true)?;
                Some(CopyPlaceSpanV2::MemRange {
                    alloc_id,
                    offset: pv.offset_bytes.checked_add(sub_off)?,
                    size: lay.size,
                })
            }
        }
        projs => match slot {
            LocalSlot::Indirect { place } => {
                let (leaf_ty, sub_off) = project_memory_field_layout_v2(base_ty, projs)?;
                let lay = layout_of_ty(&leaf_ty, true)?;
                Some(CopyPlaceSpanV2::MemRange {
                    alloc_id: place.alloc_id,
                    offset: place.offset.checked_add(sub_off)?,
                    size: lay.size,
                })
            }
            LocalSlot::Immediate { .. } | LocalSlot::PartialTuple { .. } => {
                let steps = normalize_imm_proj_path_v2(base_ty, projs)?;
                Some(CopyPlaceSpanV2::ImmPath { local_id: local, steps })
            }
            LocalSlot::Dead => None,
        },
    }
}

fn operand_copy_span_v2(
    body_locals: &[Ty],
    locals: &[LocalSlot],
    mem: &MemoryState,
    opnd: &Operand,
    endian: TargetEndian,
) -> Option<CopyPlaceSpanV2> {
    let (local, projection, _is_move) = opnd.as_place()?;
    src_place_copy_span_v2(body_locals, locals, mem, local, projection, endian)
}

fn operand_deref_base_span_v2(
    body_locals: &[Ty],
    locals: &[LocalSlot],
    mem: &MemoryState,
    opnd: &Operand,
    endian: TargetEndian,
) -> Option<Option<CopyPlaceSpanV2>> {
    let (local, projection, _is_move) = opnd.as_place()?;
    if projection.iter().any(|e| matches!(e, ProjectionElem::Deref)) {
        Some(src_place_copy_span_v2(body_locals, locals, mem, local, &[], endian))
    } else {
        None
    }
}

fn check_assign_copy_hazard_v2(
    body_locals: &[Ty],
    locals: &[LocalSlot],
    mem: &MemoryState,
    dest: &PlaceDestV2,
    dst_ty: &Ty,
    rvalue: &Rvalue,
    endian: TargetEndian,
) -> Result<(), FaultDetail> {
    match rvalue {
        Rvalue::Use { operand, .. } | Rvalue::UseRetag { operand } => {
            let Some((src_local, src_proj, _)) = operand.as_place() else {
                return Ok(());
            };
            if !is_memory_copy_repr_ty_v2(dst_ty) {
                return Ok(());
            }
            match (
                dest_copy_span_v2(locals, dest, dst_ty),
                src_place_copy_span_v2(body_locals, locals, mem, src_local, src_proj, endian),
            ) {
                (Some(d_span), Some(s_span)) => {
                    if copy_spans_overlap_v2(&d_span, &s_span) {
                        return Err(FaultDetail::undefined_classified(
                            overlapping_copy_ub_class_v2(dst_ty, &s_span),
                            "overlapping memory copy in Assign Use",
                        ));
                    }
                    Ok(())
                }
                _ => Err(FaultDetail::unsupported(
                    "unresolved copy span in Profile v2 Assign Use hazard check",
                )),
            }
        }
        Rvalue::AggregateTuple { fields }
        | Rvalue::Aggregate { aggregate_kind: AggregateKind::Tuple, fields } => {
            if matches!(copy_repr_of_ty_v2(dst_ty), CopyReprV2::Zst { .. }) {
                return Ok(());
            }
            let (Some(field_tys), Some(base_span)) =
                (tuple_field_tys(dst_ty), dest_copy_span_v2(locals, dest, dst_ty))
            else {
                return Err(FaultDetail::unsupported(
                    "unresolved destination span in Profile v2 AggregateTuple hazard check",
                ));
            };
            let mut written_spans: Vec<CopyPlaceSpanV2> = Vec::with_capacity(fields.len());
            for (idx, (field_ty, opnd)) in field_tys.iter().zip(fields.iter()).enumerate() {
                let op_span = operand_copy_span_v2(body_locals, locals, mem, opnd, endian);
                if let Some(ref os) = op_span
                    && written_spans.iter().any(|w| copy_spans_overlap_v2(w, os))
                {
                    return Err(FaultDetail::unsupported(
                        "in-place Aggregate field write aliases a subsequent operand",
                    ));
                }
                let ptr_clobbered =
                    match operand_deref_base_span_v2(body_locals, locals, mem, opnd, endian) {
                        None => false,
                        Some(None) => !written_spans.is_empty(),
                        Some(Some(ref ps)) => {
                            written_spans.iter().any(|w| copy_spans_overlap_v2(w, ps))
                        }
                    };
                if ptr_clobbered {
                    return Err(FaultDetail::unsupported(
                        "in-place Aggregate field write aliases a subsequent deref pointer local",
                    ));
                }
                match dest_aggregate_sub_span_v2(&base_span, dst_ty, idx) {
                    Some(sub_span) => {
                        if let Some(ref os) = op_span
                            && copy_spans_overlap_v2(&sub_span, os)
                            && is_memory_copy_repr_ty_v2(field_ty)
                        {
                            return Err(FaultDetail::undefined_classified(
                                overlapping_copy_ub_class_v2(field_ty, os),
                                "overlapping memory copy in Aggregate field write",
                            ));
                        }
                        written_spans.push(sub_span);
                    }
                    None => {
                        if let Some(ref os) = op_span
                            && copy_spans_overlap_v2(&base_span, os)
                        {
                            return Err(FaultDetail::unsupported(
                                "in-place Aggregate destination aliases operand",
                            ));
                        }
                        written_spans.push(base_span.clone());
                    }
                }
            }
            Ok(())
        }
        Rvalue::Binary { .. }
        | Rvalue::Unary { .. }
        | Rvalue::Cast { .. }
        | Rvalue::Discriminant { .. }
        | Rvalue::AggregateArray { .. }
        | Rvalue::Repeat { .. }
        | Rvalue::AggregateRangeTo { .. }
        | Rvalue::AggregateRangeFrom { .. }
        | Rvalue::Aggregate { .. }
        | Rvalue::Ref { .. }
        | Rvalue::AddressOf { .. }
        | Rvalue::FakeAddressOf { .. }
        | Rvalue::Unsupported => Ok(()),
    }
}

fn eval_ptr_offset_v2(
    mem: &MemoryState,
    elem_size: u64,
    ptr: PtrVal,
    count_val: &Val,
) -> Result<Val, FaultDetail> {
    let Val::Scalar(sv) = *count_val else {
        return Err(FaultDetail::unsupported("pointer offset count must be scalar"));
    };
    if sv.width != IntWidth::Isize {
        return Err(FaultDetail::unsupported("pointer offset count must be isize or usize"));
    }
    if !sv.signed {
        let count = sv.truncated_bits() as u64;
        return ptr_add_in_mem(mem, elem_size, ptr, count).map(Val::Ptr);
    }
    let signed_count = sv.to_signed_i128();
    if signed_count >= 0 {
        return ptr_add_in_mem(mem, elem_size, ptr, signed_count as u64).map(Val::Ptr);
    }
    let abs_count = signed_count.unsigned_abs();
    let delta = abs_count * u128::from(elem_size);
    if delta >= u128::from(ISIZE_MAX_BYTES) {
        return Err(FaultDetail::undefined_classified(
            UbClass::PtrOffsetOverflowOrOob,
            "negative pointer offset delta exceeds isize::MAX",
        ));
    }
    match ptr.alloc_id {
        None => Err(FaultDetail::undefined_classified(
            if delta == 0 {
                UbClass::ZeroOffsetDeadOrOobPtr
            } else {
                UbClass::PtrOffsetOverflowOrOob
            },
            "negative pointer offset on provenance-free pointer",
        )),
        Some(aid) => {
            let Some(alloc) = mem.find(aid) else {
                return Err(FaultDetail::undefined_classified(
                    if delta == 0 {
                        UbClass::ZeroOffsetDeadOrOobPtr
                    } else {
                        UbClass::PtrOffsetOverflowOrOob
                    },
                    "negative pointer offset into unknown allocation",
                ));
            };
            let off = u128::from(ptr.offset_bytes);
            if !alloc.live || off > alloc.bytes.len() as u128 || delta > off {
                return Err(FaultDetail::undefined_classified(
                    if delta == 0 {
                        UbClass::ZeroOffsetDeadOrOobPtr
                    } else {
                        UbClass::PtrOffsetOverflowOrOob
                    },
                    "negative pointer offset out of bounds or on dead allocation",
                ));
            }
            Ok(Val::Ptr(PtrVal { offset_bytes: ptr.offset_bytes - (delta as u64), ..ptr }))
        }
    }
}

fn promote_local_to_memory(
    body_locals: &[Ty],
    locals: &mut [LocalSlot],
    moved: &mut MoveTracker<'_>,
    mem: &mut MemoryState,
    local_id: u32,
    endian: TargetEndian,
) -> Result<(Ty, MemPlace), FaultDetail> {
    let idx = local_id as usize;
    let (Some(local_ty), Some(slot)) = (body_locals.get(idx), locals.get(idx).cloned()) else {
        return Err(FaultDetail::unsupported("address-taken local out of bounds"));
    };
    match slot {
        LocalSlot::Dead => Err(FaultDetail::undefined_classified(
            UbClass::DeadLocalAccess,
            "taking address of storage-dead local",
        )),
        LocalSlot::Indirect { place } => {
            if local_ty.is_unsized() {
                Err(FaultDetail::unsupported("cannot promote unsized local"))
            } else {
                Ok((local_ty.clone(), place))
            }
        }
        LocalSlot::Immediate { val } => {
            let Some(lay) = layout_of_ty(local_ty, true) else {
                return Err(FaultDetail::unsupported(
                    "address-taken local has no Profile v2 layout",
                ));
            };
            let place = mem.try_allocate_stack(lay)?;
            if let Some(v) = val {
                store_indirect_tracked(mem, moved, endian, local_ty, place, &v, true)?;
            } else if moved.locals.contains(&local_id) {
                moved.mark_bytes_span(place, lay.size);
            }
            locals[idx] = LocalSlot::Indirect { place };
            Ok((local_ty.clone(), place))
        }
        LocalSlot::PartialTuple { .. } => {
            Err(FaultDetail::unsupported("cannot take address of partially moved tuple"))
        }
    }
}

fn project_val_field_v2(
    base_ty: &Ty,
    val: &Val,
    projection: &[ProjectionElem],
) -> Result<(Ty, Val), FaultDetail> {
    let mut cur_ty = base_ty.clone();
    let mut cur_val = val.clone();
    for elem in projection {
        let ProjectionElem::Field { field_idx, ty: f_ty } = elem else {
            return Err(FaultDetail::unsupported("unsupported nested projection element"));
        };
        let idx = *field_idx as usize;
        match (&cur_ty, &cur_val) {
            (Ty::Tuple { .. } | Ty::OverflowPair(_), Val::Tuple(vs)) => {
                let Some(ts) = tuple_field_tys(&cur_ty) else {
                    return Err(FaultDetail::unsupported("expected tuple field types"));
                };
                let (Some(elem_ty), Some(elem_val)) = (ts.get(idx), vs.get(idx)) else {
                    return Err(FaultDetail::unsupported("tuple field index out of bounds"));
                };
                if !elem_ty.structural_eq(f_ty) {
                    return Err(FaultDetail::unsupported("tuple field projection type mismatch"));
                }
                cur_ty = elem_ty.clone();
                cur_val = elem_val.clone();
            }
            (Ty::RangeTo { elem }, Val::RangeTo(end)) if elem.is_usize() && idx == 0 => {
                if !f_ty.is_usize() {
                    return Err(FaultDetail::unsupported("RangeTo field 0 must be usize"));
                }
                cur_ty = Ty::Int(IntTy { width: IntWidth::Isize, signed: false });
                cur_val = Val::usize_val(*end);
            }
            (Ty::RangeFrom { elem }, Val::RangeFrom(start)) if elem.is_usize() && idx == 0 => {
                if !f_ty.is_usize() {
                    return Err(FaultDetail::unsupported("RangeFrom field 0 must be usize"));
                }
                cur_ty = Ty::Int(IntTy { width: IntWidth::Isize, signed: false });
                cur_val = Val::usize_val(*start);
            }
            _ => {
                return Err(FaultDetail::unsupported("field projection on non-tuple/range value"));
            }
        }
    }
    Ok((cur_ty, cur_val))
}

fn tuple_slot_fields(slot: &LocalSlot) -> Option<Vec<Option<Val>>> {
    match slot {
        LocalSlot::Immediate { val: Some(Val::Tuple(vs)) } => {
            Some(vs.iter().cloned().map(Some).collect())
        }
        LocalSlot::PartialTuple { fields } => Some(fields.clone()),
        _ => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn read_place_v2(
    body_locals: &[Ty],
    locals: &mut [LocalSlot],
    moved: &mut MoveTracker<'_>,
    mem: &mut MemoryState,
    is_move: bool,
    local: u32,
    projection: &[ProjectionElem],
    endian: TargetEndian,
) -> Result<(Ty, ReadSlotVal), FaultDetail> {
    let idx = local as usize;
    let (Some(base_ty), Some(slot)) = (body_locals.get(idx), locals.get(idx).cloned()) else {
        return Err(FaultDetail::unsupported("operand local out of bounds"));
    };
    if matches!(slot, LocalSlot::Dead) {
        return Err(FaultDetail::undefined_classified(
            UbClass::DeadLocalAccess,
            if is_move { "Move from dead local" } else { "Copy from dead local" },
        ));
    }
    match projection {
        [] => {
            if !is_supported_v2_local_ty(base_ty) {
                return Err(FaultDetail::unsupported("local type outside Profile v2 fragment"));
            }
            match slot {
                LocalSlot::Dead => unreachable!("checked above"),
                LocalSlot::PartialTuple { .. } => Err(FaultDetail::undefined_classified(
                    UbClass::MoveDeinitLocalRead,
                    "reading partially moved tuple as a whole",
                )),
                LocalSlot::Immediate { val } => {
                    let slot_val = match val {
                        Some(v) => {
                            if is_move {
                                let next_slot = live_uninit_slot(base_ty);
                                if matches!(next_slot, LocalSlot::Immediate { val: None }) {
                                    moved.mark_local(local);
                                }
                                locals[idx] = next_slot;
                            }
                            ReadSlotVal::Init(v)
                        }
                        None => {
                            let class = moved.as_view().uninit_local(local);
                            if is_move {
                                locals[idx] = live_uninit_slot(base_ty);
                            }
                            ReadSlotVal::Uninit(class)
                        }
                    };
                    Ok((base_ty.clone(), slot_val))
                }
                LocalSlot::Indirect { place } => {
                    let val = load_indirect(mem, endian, base_ty, place, true)?;
                    let slot_val = match val {
                        Some(v) => {
                            if is_move {
                                deinit_indirect_tracked(mem, moved, base_ty, place, true)?;
                                if layout_of_ty(base_ty, true).is_some_and(|l| l.size > 0) {
                                    moved.mark_local(local);
                                }
                            }
                            ReadSlotVal::Init(v)
                        }
                        None => {
                            let class =
                                moved.as_view().uninit_indirect_local(local, place, base_ty, true);
                            if is_move {
                                deinit_indirect(mem, base_ty, place, true)?;
                            }
                            ReadSlotVal::Uninit(class)
                        }
                    };
                    Ok((base_ty.clone(), slot_val))
                }
            }
        }
        [ProjectionElem::Deref] => {
            if is_move {
                return Err(FaultDetail::unsupported(
                    "Move through dereference projection is unsupported in Profile v2",
                ));
            }
            let pointee = match base_ty {
                Ty::Ref { pointee, .. } | Ty::RawPtr { pointee, .. } => pointee.as_ref(),
                _ => {
                    return Err(FaultDetail::unsupported(
                        "deref projection requires reference or raw pointer local",
                    ));
                }
            };
            if pointee.is_unsized() {
                return Err(FaultDetail::unsupported(
                    "deref load of unsized pointee is unsupported in Profile v2",
                ));
            }
            let Some(lay) = layout_of_ty(pointee, true) else {
                return Err(FaultDetail::unsupported("deref pointee has no Profile v2 layout"));
            };
            let ptr_val = match slot {
                LocalSlot::Dead => unreachable!("checked above"),
                LocalSlot::PartialTuple { .. } => {
                    return Err(FaultDetail::undefined_classified(
                        UbClass::MoveDeinitLocalRead,
                        "dereferencing partially moved slot",
                    ));
                }
                LocalSlot::Immediate { val } => val.ok_or_else(|| {
                    FaultDetail::undefined_classified(
                        moved.as_view().uninit_local(local),
                        "dereferencing uninitialized pointer local",
                    )
                })?,
                LocalSlot::Indirect { place } => load_indirect(mem, endian, base_ty, place, true)?
                    .ok_or_else(|| {
                        FaultDetail::undefined_classified(
                            moved.as_view().uninit_indirect_local(local, place, base_ty, true),
                            "dereferencing uninitialized pointer local",
                        )
                    })?,
            };
            let Val::Ptr(pv) = ptr_val else {
                return Err(FaultDetail::unsupported(
                    "deref operand local does not hold thin pointer",
                ));
            };
            match pv.alloc_id {
                None => {
                    if pv.offset_bytes == 0 {
                        let class = if lay.size == 0 {
                            UbClass::ZstNullRawPtrDeref
                        } else {
                            UbClass::NullOrNoProvPtrAccess
                        };
                        return Err(FaultDetail::undefined_classified(
                            class,
                            "dereferencing null pointer",
                        ));
                    }
                    if lay.size > 0 {
                        return Err(FaultDetail::undefined_classified(
                            UbClass::NullOrNoProvPtrAccess,
                            "non-zero-sized deref of provenance-free pointer",
                        ));
                    }
                    if !offset_is_aligned(pv.offset_bytes, lay.align_log2) {
                        return Err(FaultDetail::undefined_classified(
                            UbClass::MisalignedMemoryAccess,
                            "misaligned zero-sized deref of provenance-free pointer",
                        ));
                    }
                    let slot_val = match crate::memory::decode_val(endian, pointee, &[], true)? {
                        Some(v) => ReadSlotVal::Init(v),
                        None => ReadSlotVal::Uninit(UbClass::UninitMemoryRead),
                    };
                    Ok((pointee.clone(), slot_val))
                }
                Some(aid) => {
                    let mp = MemPlace { alloc_id: aid, offset: pv.offset_bytes };
                    let slot_val = match load_indirect(mem, endian, pointee, mp, true)? {
                        Some(v) => ReadSlotVal::Init(v),
                        None => ReadSlotVal::Uninit(moved.as_view().uninit_deref(mp, lay.size)),
                    };
                    Ok((pointee.clone(), slot_val))
                }
            }
        }
        [ProjectionElem::Deref, ..] => Err(FaultDetail::unsupported(
            "chained projection after Deref unsupported in Profile v2",
        )),
        [ProjectionElem::Field { field_idx, ty: f_ty }, rest @ ..] => {
            if is_move {
                if !rest.is_empty() {
                    return Err(FaultDetail::unsupported(
                        "nested field move is unsupported in Profile v2",
                    ));
                }
                if matches!(slot, LocalSlot::Immediate { val: None }) {
                    return Err(FaultDetail::undefined_classified(
                        moved.as_view().uninit_local(local),
                        "field move from uninitialized tuple local",
                    ));
                }
                let (Some(ts), Some(mut fs)) = (tuple_field_tys(base_ty), tuple_slot_fields(&slot))
                else {
                    return Err(FaultDetail::unsupported(
                        "field move requires immediate or partially moved tuple local",
                    ));
                };
                let fidx = *field_idx as usize;
                let (Some(elem_ty), Some(field_opt)) = (ts.get(fidx), fs.get(fidx)) else {
                    return Err(FaultDetail::unsupported("tuple field index out of bounds"));
                };
                let Some(elem_val) = field_opt.clone() else {
                    return Err(FaultDetail::undefined_classified(
                        UbClass::MoveDeinitLocalRead,
                        "moving already-moved tuple field",
                    ));
                };
                if !elem_ty.structural_eq(f_ty) {
                    return Err(FaultDetail::unsupported("tuple field move type mismatch"));
                }
                let moved_val = match live_uninit_slot(elem_ty) {
                    LocalSlot::Immediate { val } => val,
                    _ => None,
                };
                fs[fidx] = moved_val;
                if fs.iter().all(Option::is_none) {
                    locals[idx] = LocalSlot::Immediate { val: None };
                    moved.mark_local(local);
                } else {
                    locals[idx] = LocalSlot::PartialTuple { fields: fs };
                }
                Ok((elem_ty.clone(), ReadSlotVal::Init(elem_val)))
            } else {
                match slot {
                    LocalSlot::Dead => unreachable!("checked above"),
                    LocalSlot::Immediate { val: None } => Err(FaultDetail::undefined_classified(
                        moved.as_view().uninit_local(local),
                        "field copy from uninitialized local",
                    )),
                    LocalSlot::Immediate { val: Some(v) } => {
                        let (fty, fv) = project_val_field_v2(base_ty, &v, projection)?;
                        Ok((fty, ReadSlotVal::Init(fv)))
                    }
                    LocalSlot::Indirect { place } => {
                        let Some(v) = load_indirect(mem, endian, base_ty, place, true)? else {
                            return Err(FaultDetail::undefined_classified(
                                moved.as_view().uninit_indirect_local(local, place, base_ty, true),
                                "field copy from uninitialized indirect local",
                            ));
                        };
                        let (fty, fv) = project_val_field_v2(base_ty, &v, projection)?;
                        Ok((fty, ReadSlotVal::Init(fv)))
                    }
                    LocalSlot::PartialTuple { fields } => {
                        if !rest.is_empty() {
                            return Err(FaultDetail::unsupported(
                                "nested field copy from partially moved tuple is unsupported",
                            ));
                        }
                        let Some(ts) = tuple_field_tys(base_ty) else {
                            return Err(FaultDetail::unsupported(
                                "partial tuple slot requires tuple local type",
                            ));
                        };
                        let fidx = *field_idx as usize;
                        let (Some(elem_ty), Some(field_opt)) = (ts.get(fidx), fields.get(fidx))
                        else {
                            return Err(FaultDetail::unsupported(
                                "tuple field index out of bounds",
                            ));
                        };
                        let Some(elem_val) = field_opt.clone() else {
                            return Err(FaultDetail::undefined_classified(
                                UbClass::MoveDeinitLocalRead,
                                "copying already-moved tuple field",
                            ));
                        };
                        if !elem_ty.structural_eq(f_ty) {
                            return Err(FaultDetail::unsupported("tuple field copy type mismatch"));
                        }
                        Ok((elem_ty.clone(), ReadSlotVal::Init(elem_val)))
                    }
                }
            }
        }
        [ProjectionElem::ConstantIndex { .. } | ProjectionElem::Unsupported, ..] => {
            Err(FaultDetail::unsupported("unsupported place projection element"))
        }
    }
}

fn eval_operand_to_slot_v2(
    body_locals: &[Ty],
    locals: &mut [LocalSlot],
    moved: &mut MoveTracker<'_>,
    mem: &mut MemoryState,
    opnd: &Operand,
    endian: TargetEndian,
) -> Result<(Ty, ReadSlotVal), FaultDetail> {
    match opnd {
        Operand::Constant { ty, lit } => {
            let val = eval_const_lit(ty, lit)?;
            Ok((ty.clone(), ReadSlotVal::Init(val)))
        }
        _ => {
            let Some((local, projection, is_move)) = opnd.as_place() else {
                return Err(FaultDetail::unsupported("unexpected operand variant"));
            };
            read_place_v2(body_locals, locals, moved, mem, is_move, local, projection, endian)
        }
    }
}

fn eval_primitive_operand_v2(
    body_locals: &[Ty],
    locals: &mut [LocalSlot],
    moved: &mut MoveTracker<'_>,
    mem: &mut MemoryState,
    opnd: &Operand,
    endian: TargetEndian,
) -> Result<Val, FaultDetail> {
    let (ty, slot_val) = eval_operand_to_slot_v2(body_locals, locals, moved, mem, opnd, endian)?;
    if !is_primitive_readable_ty(&ty) {
        return Err(FaultDetail::unsupported("non-primitive operand type"));
    }
    match slot_val {
        ReadSlotVal::Init(v) => Ok(v),
        ReadSlotVal::Uninit(class) => {
            Err(FaultDetail::undefined_classified(class, "reading uninitialized primitive operand"))
        }
    }
}

fn eval_arg_operands_v2(
    body_locals: &[Ty],
    locals: &mut [LocalSlot],
    moved: &mut MoveTracker<'_>,
    mem: &mut MemoryState,
    args: &[Operand],
    endian: TargetEndian,
) -> Result<Vec<(Ty, Val)>, FaultDetail> {
    let mut out = Vec::with_capacity(args.len());
    for opnd in args {
        let (ty, slot_val) =
            eval_operand_to_slot_v2(body_locals, locals, moved, mem, opnd, endian)?;
        let ReadSlotVal::Init(v) = slot_val else {
            let ReadSlotVal::Uninit(class) = slot_val else { unreachable!() };
            return Err(FaultDetail::undefined_classified(
                class,
                "reading uninitialized argument operand",
            ));
        };
        out.push((ty, v));
    }
    Ok(out)
}

fn eval_ptr_to_ptr_cast_v2(src_ty: &Ty, src_val: Val, cast_ty: &Ty) -> Result<Val, FaultDetail> {
    let Ty::RawPtr { mutability: cast_mut, pointee: cast_pt } = cast_ty else {
        return Err(FaultDetail::unsupported("PtrToPtr target must be raw pointer"));
    };
    if src_ty.is_const_raw_ptr() && *cast_mut == Mutability::Mut {
        return Err(FaultDetail::unsupported(
            "Profile v2 refuses *const T -> *mut T pointer casts",
        ));
    }
    match (src_ty, src_val) {
        (Ty::RawPtr { pointee: src_pt, .. }, Val::Ptr(p)) => {
            if src_pt.is_unsized() || cast_pt.is_unsized() {
                Err(FaultDetail::unsupported("thin PtrToPtr cast requires sized pointees"))
            } else {
                Ok(Val::Ptr(p))
            }
        }
        (Ty::RawPtr { pointee: src_pt, .. }, Val::SlicePtr { ptr, len }) => {
            match (src_pt.as_ref(), cast_pt.as_ref()) {
                (Ty::Slice { elem: src_elem }, Ty::Slice { elem: cast_elem })
                    if src_elem.structural_eq(cast_elem) =>
                {
                    Ok(Val::SlicePtr { ptr, len })
                }
                _ => Err(FaultDetail::unsupported(
                    "wide PtrToPtr cast requires matching slice element types",
                )),
            }
        }
        _ => Err(FaultDetail::unsupported("PtrToPtr requires raw pointer source")),
    }
}

#[allow(clippy::too_many_arguments)]
fn eval_ref_rvalue_v2(
    body_locals: &[Ty],
    locals: &mut [LocalSlot],
    moved: &mut MoveTracker<'_>,
    mem: &mut MemoryState,
    dst_ty: &Ty,
    req_mut: Mutability,
    place: &Place,
    endian: TargetEndian,
) -> Result<Val, FaultDetail> {
    match place.projection.as_slice() {
        [] => {
            let (local_ty, mplace) =
                promote_local_to_memory(body_locals, locals, moved, mem, place.local, endian)?;
            let expected = Ty::Ref { mutability: req_mut, pointee: Box::new(local_ty.clone()) };
            if !dst_ty.structural_eq(&expected) {
                return Err(FaultDetail::unsupported(
                    "Ref destination type disagrees with borrowed local type",
                ));
            }
            let rv = Val::Ptr(PtrVal {
                alloc_id: Some(mplace.alloc_id),
                offset_bytes: mplace.offset,
                width: IntWidth::Isize,
            });
            ref_valid_in_mem(mem, endian, req_mut, &local_ty, &rv)?;
            Ok(rv)
        }
        [ProjectionElem::Deref] => {
            let idx = place.local as usize;
            let (Some(base_ty), Some(slot)) = (body_locals.get(idx), locals.get(idx)) else {
                return Err(FaultDetail::unsupported("reborrow local out of bounds"));
            };
            if matches!(slot, LocalSlot::Dead) {
                return Err(FaultDetail::undefined_classified(
                    UbClass::DeadLocalAccess,
                    "reborrowing dead reference local",
                ));
            }
            let Ty::Ref { mutability: src_mut, pointee } = base_ty else {
                return Err(FaultDetail::unsupported(
                    "Profile v2 Ref(&*x) only supports reborrowing reference locals",
                ));
            };
            if *src_mut == Mutability::Shared && req_mut == Mutability::Mut {
                return Err(FaultDetail::undefined("mutable reborrow through shared reference"));
            }
            let expected = Ty::Ref { mutability: req_mut, pointee: pointee.clone() };
            if !dst_ty.structural_eq(&expected) {
                return Err(FaultDetail::unsupported(
                    "reborrow destination type disagrees with reference pointee",
                ));
            }
            let v = match slot {
                LocalSlot::Dead => unreachable!("checked above"),
                LocalSlot::PartialTuple { .. } => {
                    return Err(FaultDetail::undefined_classified(
                        UbClass::MoveDeinitLocalRead,
                        "reborrowing partially moved slot",
                    ));
                }
                LocalSlot::Immediate { val } => val.clone().ok_or_else(|| {
                    FaultDetail::undefined_classified(
                        moved.as_view().uninit_local(place.local),
                        "reborrowing uninitialized reference local",
                    )
                })?,
                LocalSlot::Indirect { place: mp } => {
                    load_indirect(mem, endian, base_ty, *mp, true)?.ok_or_else(|| {
                        FaultDetail::undefined_classified(
                            moved.as_view().uninit_indirect_local(place.local, *mp, base_ty, true),
                            "reborrowing uninitialized reference local",
                        )
                    })?
                }
            };
            ref_valid_in_mem(mem, endian, req_mut, pointee, &v)?;
            Ok(v)
        }
        _ => Err(FaultDetail::unsupported("unsupported Ref place projection in Profile v2")),
    }
}

#[allow(clippy::too_many_arguments)]
fn eval_address_of_rvalue_v2(
    body_locals: &[Ty],
    locals: &mut [LocalSlot],
    moved: &mut MoveTracker<'_>,
    mem: &mut MemoryState,
    dst_ty: &Ty,
    req_mut: Mutability,
    place: &Place,
    endian: TargetEndian,
) -> Result<Val, FaultDetail> {
    match place.projection.as_slice() {
        [] => {
            let (local_ty, mplace) =
                promote_local_to_memory(body_locals, locals, moved, mem, place.local, endian)?;
            let expected = Ty::RawPtr { mutability: req_mut, pointee: Box::new(local_ty) };
            if !dst_ty.structural_eq(&expected) {
                return Err(FaultDetail::unsupported(
                    "AddressOf destination type disagrees with borrowed local type",
                ));
            }
            Ok(Val::Ptr(PtrVal {
                alloc_id: Some(mplace.alloc_id),
                offset_bytes: mplace.offset,
                width: IntWidth::Isize,
            }))
        }
        [ProjectionElem::Deref] => {
            let idx = place.local as usize;
            let (Some(base_ty), Some(slot)) = (body_locals.get(idx), locals.get(idx)) else {
                return Err(FaultDetail::unsupported("AddressOf local out of bounds"));
            };
            if matches!(slot, LocalSlot::Dead) {
                return Err(FaultDetail::undefined_classified(
                    UbClass::DeadLocalAccess,
                    "AddressOf on dead raw pointer local",
                ));
            }
            let Ty::RawPtr { mutability: src_mut, pointee } = base_ty else {
                return Err(FaultDetail::unsupported(
                    "Profile v2 AddressOf(&raw *p) only supports raw pointer locals",
                ));
            };
            if *src_mut == Mutability::Shared && req_mut == Mutability::Mut {
                return Err(FaultDetail::undefined("mutable raw reborrow through *const pointer"));
            }
            let expected = Ty::RawPtr { mutability: req_mut, pointee: pointee.clone() };
            if !dst_ty.structural_eq(&expected) {
                return Err(FaultDetail::unsupported(
                    "AddressOf destination type disagrees with raw pointer pointee",
                ));
            }
            match slot {
                LocalSlot::Dead => unreachable!("checked above"),
                LocalSlot::PartialTuple { .. } => Err(FaultDetail::undefined_classified(
                    UbClass::MoveDeinitLocalRead,
                    "AddressOf on partially moved slot",
                )),
                LocalSlot::Immediate { val } => val.clone().ok_or_else(|| {
                    FaultDetail::undefined_classified(
                        moved.as_view().uninit_local(place.local),
                        "AddressOf on uninitialized raw pointer local",
                    )
                }),
                LocalSlot::Indirect { place: mp } => {
                    load_indirect(mem, endian, base_ty, *mp, true)?.ok_or_else(|| {
                        FaultDetail::undefined_classified(
                            moved.as_view().uninit_indirect_local(place.local, *mp, base_ty, true),
                            "AddressOf on uninitialized raw pointer local",
                        )
                    })
                }
            }
        }
        _ => Err(FaultDetail::unsupported("unsupported AddressOf place projection in Profile v2")),
    }
}

fn eval_fake_address_of_rvalue_v2(
    body_locals: &[Ty],
    locals: &[LocalSlot],
    moved: &MoveTracker<'_>,
    mem: &MemoryState,
    dst_ty: &Ty,
    place: &Place,
    endian: TargetEndian,
) -> Result<Val, FaultDetail> {
    match place.projection.as_slice() {
        [ProjectionElem::Deref] => {
            let idx = place.local as usize;
            let (Some(base_ty), Some(slot)) = (body_locals.get(idx), locals.get(idx)) else {
                return Err(FaultDetail::unsupported("FakeAddressOf local out of bounds"));
            };
            if matches!(slot, LocalSlot::Dead) {
                return Err(FaultDetail::undefined_classified(
                    UbClass::DeadLocalAccess,
                    "FakeAddressOf on dead local",
                ));
            }
            let read_slot = || -> Result<Val, FaultDetail> {
                match slot {
                    LocalSlot::Dead => unreachable!("checked above"),
                    LocalSlot::PartialTuple { .. } => Err(FaultDetail::undefined_classified(
                        UbClass::MoveDeinitLocalRead,
                        "FakeAddressOf on partially moved slot",
                    )),
                    LocalSlot::Immediate { val } => val.clone().ok_or_else(|| {
                        FaultDetail::undefined_classified(
                            moved.as_view().uninit_local(place.local),
                            "FakeAddressOf on uninitialized local",
                        )
                    }),
                    LocalSlot::Indirect { place: mp } => {
                        load_indirect(mem, endian, base_ty, *mp, true)?.ok_or_else(|| {
                            FaultDetail::undefined_classified(
                                moved.as_view().uninit_indirect_local(
                                    place.local,
                                    *mp,
                                    base_ty,
                                    true,
                                ),
                                "FakeAddressOf on uninitialized local",
                            )
                        })
                    }
                }
            };
            match base_ty {
                Ty::Ref { mutability: src_mut, pointee } => {
                    let expected =
                        Ty::RawPtr { mutability: Mutability::Shared, pointee: pointee.clone() };
                    if pointee.as_overflow_pair().is_some() || !dst_ty.structural_eq(&expected) {
                        return Err(FaultDetail::unsupported(
                            "FakeAddressOf destination type disagrees with reference pointee",
                        ));
                    }
                    let val = read_slot()?;
                    ref_valid_in_mem(mem, endian, *src_mut, pointee, &val)
                        .map_err(downgrade_conservative_ref_check)?;
                    Ok(val)
                }
                Ty::RawPtr { pointee, .. } => {
                    let expected =
                        Ty::RawPtr { mutability: Mutability::Shared, pointee: pointee.clone() };
                    if pointee.as_overflow_pair().is_some() || !dst_ty.structural_eq(&expected) {
                        return Err(FaultDetail::unsupported(
                            "FakeAddressOf destination type disagrees with raw pointer pointee",
                        ));
                    }
                    read_slot()
                }
                _ => Err(FaultDetail::unsupported(
                    "Profile v2 FakeAddressOf(&raw const (fake) *p) requires reference or raw pointer local",
                )),
            }
        }
        _ => Err(FaultDetail::unsupported(
            "unsupported FakeAddressOf place projection in Profile v2",
        )),
    }
}

fn eval_rvalue_v2(
    body_locals: &[Ty],
    locals: &mut [LocalSlot],
    moved: &mut MoveTracker<'_>,
    mem: &mut MemoryState,
    dst_ty: &Ty,
    rvalue: &Rvalue,
    endian: TargetEndian,
) -> Result<Val, FaultDetail> {
    match rvalue {
        Rvalue::Use { operand, with_retag } => {
            if *with_retag && !dst_ty.is_retag_noop() {
                return Err(FaultDetail::unsupported(
                    "retagging Use rvalue on reference-bearing type requires UseRetag",
                ));
            }
            let (src_ty, slot_val) =
                eval_operand_to_slot_v2(body_locals, locals, moved, mem, operand, endian)?;
            if !src_ty.structural_eq(dst_ty) {
                return Err(FaultDetail::unsupported(
                    "Use operand type disagrees with destination type",
                ));
            }
            match slot_val {
                ReadSlotVal::Init(v) => Ok(v),
                ReadSlotVal::Uninit(class) => {
                    Err(FaultDetail::undefined_classified(class, "Use reading uninitialized value"))
                }
            }
        }
        Rvalue::UseRetag { operand } => {
            let (src_ty, slot_val) =
                eval_operand_to_slot_v2(body_locals, locals, moved, mem, operand, endian)?;
            if !src_ty.structural_eq(dst_ty) {
                return Err(FaultDetail::unsupported(
                    "UseRetag operand type disagrees with destination type",
                ));
            }
            let ReadSlotVal::Init(v) = slot_val else {
                let ReadSlotVal::Uninit(class) = slot_val else { unreachable!() };
                return Err(FaultDetail::undefined_classified(
                    class,
                    "UseRetag reading uninitialized value",
                ));
            };
            refs_valid_in_mem(mem, endian, &src_ty, &v)?;
            Ok(v)
        }
        Rvalue::Binary { op: BinOp::Offset, left, right } => {
            let (lhs_ty, lhs_slot) =
                eval_operand_to_slot_v2(body_locals, locals, moved, mem, left, endian)?;
            let ReadSlotVal::Init(lhs_val) = lhs_slot else {
                let ReadSlotVal::Uninit(class) = lhs_slot else { unreachable!() };
                return Err(FaultDetail::undefined_classified(
                    class,
                    "Offset reading uninitialized pointer",
                ));
            };
            let Val::Ptr(p) = lhs_val else {
                return Err(FaultDetail::unsupported("Offset requires thin raw pointer operand"));
            };
            let Ty::RawPtr { pointee, .. } = &lhs_ty else {
                return Err(FaultDetail::unsupported("Offset requires raw pointer operand type"));
            };
            if pointee.is_unsized() || !dst_ty.structural_eq(&lhs_ty) {
                return Err(FaultDetail::unsupported(
                    "Offset requires sized pointee and matching destination type",
                ));
            }
            let Some(lay) = layout_of_ty(pointee, true) else {
                return Err(FaultDetail::unsupported("Offset pointee has no Profile v2 layout"));
            };
            let (_, rhs_slot) =
                eval_operand_to_slot_v2(body_locals, locals, moved, mem, right, endian)?;
            let ReadSlotVal::Init(rhs_val) = rhs_slot else {
                let ReadSlotVal::Uninit(class) = rhs_slot else { unreachable!() };
                return Err(FaultDetail::undefined_classified(
                    class,
                    "Offset reading uninitialized count",
                ));
            };
            eval_ptr_offset_v2(mem, lay.size, p, &rhs_val)
        }
        Rvalue::Binary { op, left, right } => {
            let l_val = eval_primitive_operand_v2(body_locals, locals, moved, mem, left, endian)?;
            let r_val = eval_primitive_operand_v2(body_locals, locals, moved, mem, right, endian)?;
            eval_bin_op(*op, &l_val, &r_val)
        }
        Rvalue::Unary { op: UnOp::PtrMetadata, operand } => {
            let (src_ty, slot_val) =
                eval_operand_to_slot_v2(body_locals, locals, moved, mem, operand, endian)?;
            let ReadSlotVal::Init(val) = slot_val else {
                let ReadSlotVal::Uninit(class) = slot_val else { unreachable!() };
                return Err(FaultDetail::undefined_classified(
                    class,
                    "PtrMetadata reading uninitialized pointer",
                ));
            };
            match (&src_ty, &val) {
                (Ty::Ref { mutability, pointee }, Val::SlicePtr { len, .. })
                    if matches!(pointee.as_ref(), Ty::Slice { .. }) =>
                {
                    if !dst_ty.is_usize() {
                        return Err(FaultDetail::unsupported(
                            "slice PtrMetadata destination must be usize",
                        ));
                    }
                    ref_valid_in_mem(mem, endian, *mutability, pointee, &val)
                        .map_err(downgrade_conservative_ref_check)?;
                    Ok(Val::usize_val(*len))
                }
                (Ty::RawPtr { pointee, .. }, Val::SlicePtr { len, .. })
                    if matches!(pointee.as_ref(), Ty::Slice { .. }) =>
                {
                    if !dst_ty.is_usize() {
                        return Err(FaultDetail::unsupported(
                            "slice PtrMetadata destination must be usize",
                        ));
                    }
                    Ok(Val::usize_val(*len))
                }
                (Ty::Ref { mutability, pointee }, Val::Ptr(_)) => {
                    if pointee.is_unsized() || *dst_ty != Ty::Unit {
                        return Err(FaultDetail::unsupported(
                            "thin PtrMetadata requires sized pointee and unit destination",
                        ));
                    }
                    ref_valid_in_mem(mem, endian, *mutability, pointee, &val)
                        .map_err(downgrade_conservative_ref_check)?;
                    Ok(Val::Unit)
                }
                (Ty::RawPtr { pointee, .. }, Val::Ptr(_)) => {
                    if pointee.is_unsized() || *dst_ty != Ty::Unit {
                        return Err(FaultDetail::unsupported(
                            "thin PtrMetadata requires sized pointee and unit destination",
                        ));
                    }
                    Ok(Val::Unit)
                }
                _ => Err(FaultDetail::unsupported("unsupported PtrMetadata operand")),
            }
        }
        Rvalue::Unary { op, operand } => {
            let val = eval_primitive_operand_v2(body_locals, locals, moved, mem, operand, endian)?;
            eval_un_op(*op, &val)
        }
        Rvalue::Cast { cast_kind: CastKind::IntToInt, operand, ty } => {
            let (src_ty, slot_val) =
                eval_operand_to_slot_v2(body_locals, locals, moved, mem, operand, endian)?;
            if !is_int_like_ty(&src_ty) || !dst_ty.structural_eq(ty) {
                return Err(FaultDetail::unsupported("invalid IntToInt cast types"));
            }
            let ReadSlotVal::Init(v) = slot_val else {
                let ReadSlotVal::Uninit(class) = slot_val else { unreachable!() };
                return Err(FaultDetail::undefined_classified(
                    class,
                    "IntToInt reading uninitialized operand",
                ));
            };
            eval_int_to_int_cast(CastKind::IntToInt, &v, ty)
        }
        Rvalue::Cast { cast_kind: CastKind::PtrToPtr, operand, ty } => {
            if !dst_ty.structural_eq(ty) {
                return Err(FaultDetail::unsupported("PtrToPtr destination type mismatch"));
            }
            let (src_ty, slot_val) =
                eval_operand_to_slot_v2(body_locals, locals, moved, mem, operand, endian)?;
            let ReadSlotVal::Init(v) = slot_val else {
                let ReadSlotVal::Uninit(class) = slot_val else { unreachable!() };
                return Err(FaultDetail::undefined_classified(
                    class,
                    "PtrToPtr reading uninitialized pointer",
                ));
            };
            eval_ptr_to_ptr_cast_v2(&src_ty, v, ty)
        }
        Rvalue::Cast { cast_kind: CastKind::IntToPtr, operand, ty } => {
            if !dst_ty.structural_eq(ty) {
                return Err(FaultDetail::unsupported("IntToPtr destination type mismatch"));
            }
            let Ty::RawPtr { pointee, .. } = ty else {
                return Err(FaultDetail::unsupported("IntToPtr target must be raw pointer"));
            };
            if pointee.is_unsized() {
                return Err(FaultDetail::unsupported("IntToPtr target must be sized"));
            }
            let (src_ty, slot_val) =
                eval_operand_to_slot_v2(body_locals, locals, moved, mem, operand, endian)?;
            match (src_ty, slot_val) {
                (ty_src, ReadSlotVal::Init(Val::Scalar(sv))) if ty_src.is_usize() => {
                    Ok(Val::Ptr(PtrVal {
                        alloc_id: None,
                        offset_bytes: sv.truncated_bits() as u64,
                        width: IntWidth::Isize,
                    }))
                }
                (_, ReadSlotVal::Uninit(class)) => Err(FaultDetail::undefined_classified(
                    class,
                    "IntToPtr reading uninitialized address",
                )),
                _ => Err(FaultDetail::unsupported("IntToPtr requires usize operand")),
            }
        }
        Rvalue::Discriminant { place } => eval_discriminant_rvalue(
            body_locals,
            locals,
            moved.as_view(),
            mem,
            place.local,
            &place.projection,
            dst_ty,
            endian,
            true,
        ),
        Rvalue::Ref { mutability, place } => {
            eval_ref_rvalue_v2(body_locals, locals, moved, mem, dst_ty, *mutability, place, endian)
        }
        Rvalue::AddressOf { mutability, place } => eval_address_of_rvalue_v2(
            body_locals,
            locals,
            moved,
            mem,
            dst_ty,
            *mutability,
            place,
            endian,
        ),
        Rvalue::FakeAddressOf { place } => {
            eval_fake_address_of_rvalue_v2(body_locals, locals, moved, mem, dst_ty, place, endian)
        }
        Rvalue::AggregateTuple { fields } => {
            let Some(field_tys) = tuple_field_tys(dst_ty) else {
                return Err(FaultDetail::unsupported(
                    "AggregateTuple requires tuple destination type",
                ));
            };
            let typed_vals = eval_arg_operands_v2(body_locals, locals, moved, mem, fields, endian)?;
            let vs: Vec<Val> = typed_vals.into_iter().map(|(_, v)| v).collect();
            if !check_args_match(&vs, &field_tys, true) {
                return Err(FaultDetail::unsupported(
                    "AggregateTuple field values disagree with destination tuple types",
                ));
            }
            Ok(Val::Tuple(vs))
        }
        Rvalue::Aggregate { aggregate_kind: AggregateKind::Tuple, fields } => {
            if fields.is_empty() && *dst_ty == Ty::Unit {
                return Ok(Val::Unit);
            }
            let Some(field_tys) = tuple_field_tys(dst_ty) else {
                return Err(FaultDetail::unsupported(
                    "Aggregate(Tuple) requires tuple destination type",
                ));
            };
            let typed_vals = eval_arg_operands_v2(body_locals, locals, moved, mem, fields, endian)?;
            let vs: Vec<Val> = typed_vals.into_iter().map(|(_, v)| v).collect();
            if !check_args_match(&vs, &field_tys, true) {
                return Err(FaultDetail::unsupported(
                    "Aggregate(Tuple) field values disagree with destination tuple types",
                ));
            }
            Ok(Val::Tuple(vs))
        }
        Rvalue::AggregateRangeTo { elem_ty, end } => {
            let expected = Ty::RangeTo {
                elem: Box::new(Ty::Int(IntTy { width: IntWidth::Isize, signed: false })),
            };
            if !elem_ty.is_usize() || !dst_ty.structural_eq(&expected) {
                return Err(FaultDetail::unsupported(
                    "AggregateRangeTo requires usize element and RangeTo<usize> destination",
                ));
            }
            let (src_ty, slot_val) =
                eval_operand_to_slot_v2(body_locals, locals, moved, mem, end, endian)?;
            match (src_ty, slot_val) {
                (ty_src, ReadSlotVal::Init(Val::Scalar(sv))) if ty_src.is_usize() => {
                    Ok(Val::RangeTo(sv.truncated_bits() as u64))
                }
                (_, ReadSlotVal::Uninit(class)) => Err(FaultDetail::undefined_classified(
                    class,
                    "AggregateRangeTo reading uninitialized end",
                )),
                _ => Err(FaultDetail::unsupported("AggregateRangeTo end must be usize")),
            }
        }
        Rvalue::AggregateRangeFrom { elem_ty, start } => {
            let expected = Ty::RangeFrom {
                elem: Box::new(Ty::Int(IntTy { width: IntWidth::Isize, signed: false })),
            };
            if !elem_ty.is_usize() || !dst_ty.structural_eq(&expected) {
                return Err(FaultDetail::unsupported(
                    "AggregateRangeFrom requires usize element and RangeFrom<usize> destination",
                ));
            }
            let (src_ty, slot_val) =
                eval_operand_to_slot_v2(body_locals, locals, moved, mem, start, endian)?;
            match (src_ty, slot_val) {
                (ty_src, ReadSlotVal::Init(Val::Scalar(sv))) if ty_src.is_usize() => {
                    Ok(Val::RangeFrom(sv.truncated_bits() as u64))
                }
                (_, ReadSlotVal::Uninit(class)) => Err(FaultDetail::undefined_classified(
                    class,
                    "AggregateRangeFrom reading uninitialized start",
                )),
                _ => Err(FaultDetail::unsupported("AggregateRangeFrom start must be usize")),
            }
        }
        Rvalue::Cast { cast_kind: CastKind::Unsize | CastKind::Unsupported, .. }
        | Rvalue::Aggregate { .. }
        | Rvalue::AggregateArray { .. }
        | Rvalue::Repeat { .. }
        | Rvalue::Unsupported => Err(FaultDetail::unsupported("unmodeled Profile v2 MIR rvalue")),
    }
}

fn exec_core_call_op(
    mem: &MemoryState,
    op: &CoreCallOp,
    args: &[(Ty, Val)],
    dst_ty: &Ty,
    endian: TargetEndian,
) -> Result<Val, FaultDetail> {
    match (op, args) {
        (
            CoreCallOp::SliceLen,
            [(Ty::Ref { mutability, pointee }, val @ Val::SlicePtr { len, .. })],
        ) if matches!(pointee.as_ref(), Ty::Slice { elem } if matches!(elem.as_ref(), Ty::Int(_))) =>
        {
            if !dst_ty.is_usize() {
                return Err(FaultDetail::unsupported("SliceLen destination must be usize"));
            }
            ref_valid_in_mem(mem, endian, *mutability, pointee, val)
                .map_err(downgrade_conservative_ref_check)?;
            Ok(Val::usize_val(*len))
        }
        (
            CoreCallOp::SliceGetUncheckedRangeTo,
            [
                (Ty::Ref { mutability: in_mut, pointee }, val @ Val::SlicePtr { ptr, len }),
                (Ty::RangeTo { elem: idx_ty }, Val::RangeTo(end_off)),
            ],
        ) if idx_ty.is_usize()
            && matches!(
                pointee.as_ref(),
                Ty::Slice { elem }
                    if matches!(elem.as_ref(), Ty::Int(IntTy { width: IntWidth::I8, signed: false }))
            ) =>
        {
            let Ty::Ref { mutability: out_mut, pointee: dst_pt } = dst_ty else {
                return Err(FaultDetail::unsupported(
                    "SliceGetUncheckedRangeTo destination must be &[u8] or &mut [u8]",
                ));
            };
            if !dst_pt.structural_eq(pointee) {
                return Err(FaultDetail::unsupported(
                    "SliceGetUncheckedRangeTo destination pointee mismatch",
                ));
            }
            if *in_mut == Mutability::Shared && *out_mut == Mutability::Mut {
                return Err(FaultDetail::undefined(
                    "cannot produce &mut [u8] from &[u8] in get_unchecked",
                ));
            }
            ref_valid_in_mem(mem, endian, *in_mut, pointee, val)?;
            slice_get_unchecked_check(mem, *ptr, *len, 0, *end_off, 1)
        }
        (
            CoreCallOp::SliceGetUncheckedRangeFrom,
            [
                (Ty::Ref { mutability: in_mut, pointee }, val @ Val::SlicePtr { ptr, len }),
                (Ty::RangeFrom { elem: idx_ty }, Val::RangeFrom(start_off)),
            ],
        ) if idx_ty.is_usize()
            && matches!(
                pointee.as_ref(),
                Ty::Slice { elem }
                    if matches!(elem.as_ref(), Ty::Int(IntTy { width: IntWidth::I8, signed: false }))
            ) =>
        {
            let Ty::Ref { mutability: out_mut, pointee: dst_pt } = dst_ty else {
                return Err(FaultDetail::unsupported(
                    "SliceGetUncheckedRangeFrom destination must be &[u8] or &mut [u8]",
                ));
            };
            if !dst_pt.structural_eq(pointee) {
                return Err(FaultDetail::unsupported(
                    "SliceGetUncheckedRangeFrom destination pointee mismatch",
                ));
            }
            if *in_mut == Mutability::Shared && *out_mut == Mutability::Mut {
                return Err(FaultDetail::undefined(
                    "cannot produce &mut [u8] from &[u8] in get_unchecked",
                ));
            }
            ref_valid_in_mem(mem, endian, *in_mut, pointee, val)?;
            slice_get_unchecked_check(mem, *ptr, *len, *start_off, *len, 1)
        }
        (
            CoreCallOp::PtrAdd { mutability, pointee },
            [
                (Ty::RawPtr { mutability: arg_mut, pointee: arg_pt }, Val::Ptr(p)),
                (count_ty, Val::Scalar(count_sv)),
            ],
        ) if count_ty.is_usize() => {
            let expected_dst =
                Ty::RawPtr { mutability: *mutability, pointee: Box::new(pointee.clone()) };
            if arg_mut != mutability
                || !arg_pt.structural_eq(pointee)
                || !dst_ty.structural_eq(&expected_dst)
                || pointee.is_unsized()
            {
                return Err(FaultDetail::unsupported(
                    "PtrAdd argument or destination type mismatch",
                ));
            }
            let Some(lay) = layout_of_ty(pointee, true) else {
                return Err(FaultDetail::unsupported("PtrAdd pointee has no Profile v2 layout"));
            };
            let count = count_sv.truncated_bits() as u64;
            ptr_add_in_mem(mem, lay.size, *p, count).map(Val::Ptr)
        }
        (CoreCallOp::UsizeUncheckedSub, [(l_ty, Val::Scalar(l_sv)), (r_ty, Val::Scalar(r_sv))])
            if l_ty.is_usize() && r_ty.is_usize() =>
        {
            if !dst_ty.is_usize() {
                return Err(FaultDetail::unsupported(
                    "UsizeUncheckedSub destination must be usize",
                ));
            }
            let l = l_sv.truncated_bits() as u64;
            let r = r_sv.truncated_bits() as u64;
            if r > l {
                Err(FaultDetail::undefined_classified(
                    UbClass::UncheckedArithOverflow,
                    "usize::unchecked_sub underflow",
                ))
            } else {
                Ok(Val::usize_val(l - r))
            }
        }
        _ => Err(FaultDetail::unsupported("invalid CoreCallOp arguments or signature")),
    }
}

// =============================================================================
// Shared Discriminant & SwitchInt Helpers
// =============================================================================

#[allow(clippy::too_many_arguments)]
fn eval_discriminant_rvalue(
    body_locals: &[Ty],
    locals: &[LocalSlot],
    moved: MoveView<'_>,
    mem: &MemoryState,
    local: u32,
    projection: &[ProjectionElem],
    _dst_ty: &Ty,
    endian: TargetEndian,
    enable_profile_v2: bool,
) -> Result<Val, FaultDetail> {
    if enable_profile_v2 && !projection.is_empty() {
        return Err(FaultDetail::unsupported("projected Discriminant rvalue is unsupported"));
    }
    let idx = local as usize;
    let (Some(src_ty), Some(slot)) = (body_locals.get(idx), locals.get(idx)) else {
        return Err(FaultDetail::unsupported("Discriminant local out of bounds"));
    };
    let (opt_val, class) = match slot {
        LocalSlot::Dead => {
            return Err(FaultDetail::undefined_classified(
                UbClass::DeadLocalAccess,
                "Discriminant read on dead local",
            ));
        }
        LocalSlot::Immediate { val } => {
            if !projection.is_empty() {
                return Err(FaultDetail::unsupported(
                    "projected Discriminant rvalue is unsupported",
                ));
            }
            (val.clone(), moved.uninit_local(local))
        }
        LocalSlot::PartialTuple { .. } => {
            return Err(FaultDetail::unsupported(
                "Discriminant read on partially moved tuple is unsupported",
            ));
        }
        LocalSlot::Indirect { place } => {
            if !projection.is_empty() {
                return Err(FaultDetail::unsupported(
                    "projected Discriminant rvalue is unsupported",
                ));
            }
            if !matches!(src_ty, Ty::Enum(_) | Ty::Ordering) {
                return Err(FaultDetail::unsupported(
                    "Discriminant rvalue requires fieldless enum or Ordering local",
                ));
            }
            (
                load_indirect(mem, endian, src_ty, *place, enable_profile_v2)?,
                moved.uninit_indirect_local(local, *place, src_ty, enable_profile_v2),
            )
        }
    };
    match src_ty {
        Ty::Enum(ety) => eval_discriminant_of_val(ety, opt_val.as_ref(), class),
        Ty::Ordering => eval_ordering_discriminant_of_val(opt_val.as_ref(), class),
        _ => Err(FaultDetail::unsupported(
            "Discriminant rvalue requires fieldless enum or Ordering local",
        )),
    }
}

fn eval_discriminant_of_val(
    ety: &crate::ir::EnumTy,
    opt_val: Option<&Val>,
    uninit_cls: UbClass,
) -> Result<Val, FaultDetail> {
    if !enum_admitted(ety) {
        return Err(FaultDetail::unsupported("unadmitted enum type in Discriminant"));
    }
    match (&ety.tag_repr, opt_val) {
        (crate::ir::EnumTagRepr::ZeroSized, None) => {
            let Some(&disc) = ety.discriminants.first() else {
                return Err(FaultDetail::unsupported("empty ZST enum discriminants"));
            };
            Ok(Val::Scalar(ScalarVal::new(ety.discr_width, ety.discr_signed, disc)))
        }
        (crate::ir::EnumTagRepr::ZeroSized, Some(Val::EnumVal { ty: ety2, variant }))
            if ety == ety2 && *variant == 0 =>
        {
            let Some(&disc) = ety.discriminants.first() else {
                return Err(FaultDetail::unsupported("empty ZST enum discriminants"));
            };
            Ok(Val::Scalar(ScalarVal::new(ety.discr_width, ety.discr_signed, disc)))
        }
        (crate::ir::EnumTagRepr::Scalar(_), None) => Err(FaultDetail::undefined_classified(
            uninit_cls,
            "Discriminant read on uninitialized scalar-tagged enum",
        )),
        (crate::ir::EnumTagRepr::Scalar(_), Some(Val::EnumVal { ty: ety2, variant }))
            if ety == ety2 =>
        {
            let Some(&disc) = ety.discriminants.get(*variant) else {
                return Err(FaultDetail::unsupported("enum variant index out of bounds"));
            };
            Ok(Val::Scalar(ScalarVal::new(ety.discr_width, ety.discr_signed, disc)))
        }
        _ => Err(FaultDetail::unsupported("mismatched enum value in Discriminant")),
    }
}

fn eval_ordering_discriminant_of_val(
    opt_val: Option<&Val>,
    uninit_cls: UbClass,
) -> Result<Val, FaultDetail> {
    match opt_val {
        None => Err(FaultDetail::undefined_classified(
            uninit_cls,
            "Discriminant read on uninitialized Ordering",
        )),
        Some(Val::Ordering(ord)) => {
            Ok(Val::Scalar(ScalarVal::new(IntWidth::I8, true, ord.tag_bits())))
        }
        Some(_) => Err(FaultDetail::unsupported("non-Ordering value in Ordering Discriminant")),
    }
}

fn eval_switch_target(
    discr_val: &Val,
    otherwise: u32,
    targets: &[(u128, u32)],
) -> Result<u32, FaultDetail> {
    match discr_val {
        Val::Scalar(sv) => eval_scalar_switch(sv.width, sv.bits, otherwise, targets),
        Val::Bool(b) => eval_bool_switch(*b, otherwise, targets),
        Val::Char(c) => eval_char_switch(*c, otherwise, targets),
        _ => {
            if targets.is_empty() {
                Ok(otherwise)
            } else {
                Err(FaultDetail::unsupported("non-empty SwitchInt targets on non-scalar primitive"))
            }
        }
    }
}

fn eval_scalar_switch(
    w: IntWidth,
    discr_bits: u128,
    otherwise: u32,
    targets: &[(u128, u32)],
) -> Result<u32, FaultDetail> {
    let mask = w.mask();
    let truncated_discr = discr_bits & mask;
    for &(case_bits, target) in targets {
        if (case_bits & mask) != case_bits {
            return Err(FaultDetail::unsupported("SwitchInt case value exceeds operand width"));
        }
        if truncated_discr == case_bits {
            return Ok(target);
        }
    }
    Ok(otherwise)
}

fn eval_bool_switch(
    discr: bool,
    otherwise: u32,
    targets: &[(u128, u32)],
) -> Result<u32, FaultDetail> {
    for &(case_bits, target) in targets {
        if case_bits > 255 {
            return Err(FaultDetail::unsupported("bool SwitchInt case value exceeds 8 bits"));
        }
        if case_bits == 0 {
            if !discr {
                return Ok(target);
            }
        } else if case_bits == 1 {
            if discr {
                return Ok(target);
            }
        } else {
            return Err(FaultDetail::undefined_classified(
                UbClass::SyntheticInvalidConstOrSwitch,
                "invalid boolean bit pattern in SwitchInt case",
            ));
        }
    }
    Ok(otherwise)
}

fn eval_char_switch(
    discr: char,
    otherwise: u32,
    targets: &[(u128, u32)],
) -> Result<u32, FaultDetail> {
    let discr_u32 = u32::from(discr);
    for &(case_bits, target) in targets {
        if case_bits > u128::from(u32::MAX) {
            return Err(FaultDetail::unsupported("char SwitchInt case value exceeds 32 bits"));
        }
        if !is_unicode_scalar(case_bits) {
            return Err(FaultDetail::undefined_classified(
                UbClass::SyntheticInvalidConstOrSwitch,
                "invalid char scalar in SwitchInt case",
            ));
        }
        if case_bits as u32 == discr_u32 {
            return Ok(target);
        }
    }
    Ok(otherwise)
}

/// Helper checking whether `outcome` is an [`Outcome::Fault`] with
/// [`FaultKind::Undefined`].
pub const fn is_undefined_fault(outcome: &Outcome) -> bool {
    matches!(outcome, Outcome::Fault(FaultDetail { kind: FaultKind::Undefined, .. }))
}

#[cfg(test)]
mod overlapping_copy_class_tests {
    use super::*;
    use crate::{memory::Allocation, value::WitnessClass};

    #[test]
    fn classifies_replayable_vs_conservative_overlapping_assign_copies() {
        let u8_ty = Ty::Int(IntTy { width: IntWidth::I8, signed: false });
        let u32_ty = Ty::Int(IntTy { width: IntWidth::I32, signed: false });
        let u64_ty = Ty::Int(IntTy { width: IntWidth::I64, signed: false });
        let imm = CopyPlaceSpanV2::ImmPath { local_id: 1, steps: Vec::new() };
        let mem = CopyPlaceSpanV2::MemRange { alloc_id: 1, offset: 0, size: 8 };

        let tup3 = Ty::Tuple { fields: vec![u32_ty.clone(), u32_ty.clone(), u32_ty.clone()] };
        assert_eq!(overlapping_copy_ub_class_v2(&tup3, &imm), UbClass::OverlappingMemoryCopy);
        assert_eq!(overlapping_copy_ub_class_v2(&tup3, &mem), UbClass::OverlappingMemoryCopy);

        let padded_pair = Ty::OverflowPair(IntTy { width: IntWidth::I32, signed: false });
        let imm_cls = overlapping_copy_ub_class_v2(&padded_pair, &imm);
        assert_eq!(imm_cls, UbClass::ConservativeOverlappingAssignCopy);
        assert_eq!(imm_cls.witness_class(), WitnessClass::ModelOnlyUnreplayed);
        let mem_cls = overlapping_copy_ub_class_v2(&padded_pair, &mem);
        assert_eq!(mem_cls, UbClass::OverlappingMemoryCopy);
        assert_eq!(mem_cls.witness_class(), WitnessClass::ReplayableMiriUb);

        let u16_ty = Ty::Int(IntTy { width: IntWidth::I16, signed: false });
        let u128_ty = Ty::Int(IntTy { width: IntWidth::I128, signed: false });
        let byte_slice_ref = Ty::Ref {
            mutability: Mutability::Shared,
            pointee: Box::new(Ty::Slice { elem: Box::new(u8_ty.clone()) }),
        };

        // Alignment-inflated tuples have `BackendRepr::Memory` in rustc
        // whenever a ZST field raises aggregate alignment above the scalar
        // alignment, so both immediate and in-memory overlaps are replayable.
        let align_inflated_cases = [
            Ty::Tuple {
                fields: vec![
                    Ty::Array { elem: Box::new(u64_ty.clone()), len: 0 },
                    u32_ty.clone(),
                    u32_ty.clone(),
                ],
            },
            Ty::Tuple {
                fields: vec![Ty::Array { elem: Box::new(u32_ty.clone()), len: 0 }, u8_ty.clone()],
            },
            Ty::Tuple {
                fields: vec![
                    Ty::Array { elem: Box::new(u16_ty), len: 0 },
                    u8_ty.clone(),
                    u8_ty.clone(),
                ],
            },
            Ty::Tuple {
                fields: vec![Ty::Array { elem: Box::new(u128_ty), len: 0 }, byte_slice_ref],
            },
            Ty::Tuple {
                fields: vec![
                    Ty::Array { elem: Box::new(u64_ty), len: 0 },
                    u32_ty.clone(),
                    Ty::Bool,
                ],
            },
            Ty::Tuple {
                fields: vec![
                    Ty::Tuple {
                        fields: vec![Ty::Array { elem: Box::new(u32_ty.clone()), len: 0 }, u8_ty],
                    },
                    u32_ty.clone(),
                ],
            },
        ];
        for ty in &align_inflated_cases {
            assert!(is_memory_copy_repr_ty_v2(ty), "expected MemoryCopy for {ty:?}");
            assert_eq!(
                overlapping_copy_ub_class_v2(ty, &imm),
                UbClass::OverlappingMemoryCopy,
                "expected ReplayableMiriUb (imm) for {ty:?}"
            );
            assert_eq!(
                overlapping_copy_ub_class_v2(ty, &mem),
                UbClass::OverlappingMemoryCopy,
                "expected ReplayableMiriUb (mem) for {ty:?}"
            );
        }

        // Negative controls: ZST alignment <= scalar alignment does not force
        // `BackendRepr::Memory`.
        let non_inflated_pair = Ty::Tuple {
            fields: vec![
                Ty::Array { elem: Box::new(u32_ty.clone()), len: 0 },
                u32_ty.clone(),
                u32_ty.clone(),
            ],
        };
        assert!(!is_memory_copy_repr_ty_v2(&non_inflated_pair));

        let non_inflated_padded = Ty::Tuple {
            fields: vec![Ty::Array { elem: Box::new(u32_ty.clone()), len: 0 }, u32_ty, Ty::Bool],
        };
        assert!(is_memory_copy_repr_ty_v2(&non_inflated_padded));
        assert_eq!(
            overlapping_copy_ub_class_v2(&non_inflated_padded, &imm),
            UbClass::ConservativeOverlappingAssignCopy
        );
        assert_eq!(
            overlapping_copy_ub_class_v2(&non_inflated_padded, &mem),
            UbClass::OverlappingMemoryCopy
        );
    }

    #[test]
    fn aggregate_deref_ptr_clobber_fails_closed_while_pre_write_order_succeeds() {
        let u32_ty = Ty::Int(IntTy { width: IntWidth::I32, signed: false });
        let ptr_u32 =
            Ty::RawPtr { mutability: Mutability::Shared, pointee: Box::new(u32_ty.clone()) };
        let ovf_u32 = Ty::OverflowPair(IntTy { width: IntWidth::I32, signed: false });
        let ptr_bool = Ty::RawPtr { mutability: Mutability::Shared, pointee: Box::new(Ty::Bool) };
        let mem = MemoryState {
            next_alloc_id: 3,
            allocations: vec![
                Allocation {
                    alloc_id: 1,
                    align_log2: 2,
                    mutability: Mutability::Mut,
                    bytes: vec![AllocByte::Init { byte: 1, prov: None }; 4],
                    live: true,
                },
                Allocation {
                    alloc_id: 2,
                    align_log2: 3,
                    mutability: Mutability::Mut,
                    bytes: vec![AllocByte::Init { byte: 0, prov: Some(1) }; 8],
                    live: true,
                },
            ],
        };
        let body_locals = vec![Ty::Unit, u32_ty, ptr_bool, ptr_u32];
        let locals = vec![
            LocalSlot::Immediate { val: None },
            LocalSlot::Immediate { val: Some(Val::u32(7)) },
            LocalSlot::Indirect { place: MemPlace { alloc_id: 2, offset: 0 } },
            LocalSlot::Indirect { place: MemPlace { alloc_id: 2, offset: 0 } },
        ];
        let dest = PlaceDestV2::Deref {
            pointee: ovf_u32.clone(),
            lay: LayoutData { size: 8, align_log2: 2 },
            pv: PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize },
        };
        let clobber_rv = Rvalue::AggregateTuple {
            fields: vec![
                Operand::Copy { local: 1, projection: Vec::new() },
                Operand::Copy { local: 2, projection: vec![ProjectionElem::Deref] },
            ],
        };
        let err = check_assign_copy_hazard_v2(
            &body_locals,
            &locals,
            &mem,
            &dest,
            &ovf_u32,
            &clobber_rv,
            TargetEndian::Little,
        )
        .unwrap_err();
        assert_eq!(err.kind, FaultKind::Unsupported);

        // Positive control: when `_2` lives in a disjoint allocation (or is
        // read before its storage is overwritten), the hazard check passes.
        let safe_locals = vec![
            LocalSlot::Immediate { val: None },
            LocalSlot::Immediate { val: Some(Val::u32(7)) },
            LocalSlot::Immediate {
                val: Some(Val::Ptr(PtrVal {
                    alloc_id: Some(1),
                    offset_bytes: 0,
                    width: IntWidth::Isize,
                })),
            },
            LocalSlot::Indirect { place: MemPlace { alloc_id: 2, offset: 0 } },
        ];
        assert!(
            check_assign_copy_hazard_v2(
                &body_locals,
                &safe_locals,
                &mem,
                &dest,
                &ovf_u32,
                &clobber_rv,
                TargetEndian::Little,
            )
            .is_ok()
        );
    }
}
