// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Deterministic small-step MIR evaluator (`eval_body` / `MachineState`)
//! matching `Trusted.MirSemantics.{State,Step}` in Profile v1 and extensible
//! to Profile v2 constructs.

use alloc::{collections::BTreeSet, format, string::String, vec, vec::Vec};

use serde::{Deserialize, Serialize};

use crate::{
    ir::{
        AggregateKind, Block, Body, CastKind, IntTy, IntWidth, Operand, Program, ProjectionElem,
        Rvalue, Statement, Terminator, Ty, UnwindAction,
    },
    memory::{
        CallerMemory, MemPlace, MemoryState, TargetEndian, deinit_indirect, encode_val,
        eval_const_lit, layout_of_ty, load_indirect, store_indirect,
    },
    ops::{eval_bin_op, eval_int_to_int_cast, eval_un_op},
    value::{
        AllocByte, FaultDetail, ScalarVal, Val, check_args_match, check_val, enum_admitted,
        is_int_like_ty, is_primitive_readable_ty, is_supported_local_ty, is_unicode_scalar,
        is_zst_enum_ty,
    },
};

const MAX_CALL_DEPTH_V2: usize = 256;

/// Storage state of a single MIR local slot (`LocalSlot`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum LocalSlot {
    Dead,
    Immediate { val: Option<Val> },
    PartialTuple { fields: Vec<LocalSlot> },
    Indirect { place: MemPlace },
}

/// Active call stack frame (`FrameState`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrameState {
    pub def_id: usize,
    pub block_idx: usize,
    pub stmt_idx: usize,
    pub locals: Vec<LocalSlot>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub return_to: Option<CallReturnTarget>,
}

fn default_unwind_action() -> UnwindAction {
    UnwindAction::Continue
}

/// Return continuation for Profile v2 nested function calls.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CallReturnTarget {
    pub block_idx: usize,
    pub dst_local: u32,
    pub dst_projection: Vec<ProjectionElem>,
    #[serde(default = "default_unwind_action")]
    pub unwind: UnwindAction,
}

/// Observable terminal value matching `Trusted.MirModel.TerminalOut`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TerminalOut {
    Returned { ret: Val, caller_mem: CallerMemory },
    Unwound { caller_mem: CallerMemory },
}

/// Result of running an evaluation trace to completion, abort, fault, or fuel limit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
pub enum Outcome {
    Returned(TerminalOut),
    /// Process termination via `UnwindAction::Terminate` (stops execution
    /// rather than unwinding to the caller).
    Aborted {
        caller_mem: CallerMemory,
    },
    Fault(FaultDetail),
    OutOfFuel,
}

/// Execution profile enforcing either strict Profile v1 parity or Profile v2
/// extensions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvalProfile {
    /// Strict Profile v1 parity with `Trusted.MirSemantics` (requires
    /// `mir_profile_version == 1`, single stack frame, and rejects Profile v2
    /// constructs).
    StrictV1,
    /// Opt-in Profile v2 extensions enabling tuple aggregates, field
    /// projections, `Assert`, and direct `Call` terminators.
    ProfileV2,
}

/// Configuration knobs for MIR stepping.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EvalConfig {
    /// Selected semantic profile (`StrictV1` vs `ProfileV2`).
    pub profile: EvalProfile,
    /// Target memory byte order (`TargetEndian::Big` matches Profile v1
    /// `Trusted.MirSemantics.profileTargetEndian`).
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
    /// Strict Profile v1 configuration matching `Trusted.MirSemantics`.
    pub const fn profile_v1() -> Self {
        Self { profile: EvalProfile::StrictV1, endian: TargetEndian::Big, record_events: true }
    }

    /// Preview Profile v2 configuration enabling opt-in extensions (tuple
    /// aggregates, field projections, assertions, direct calls, and
    /// `UnwindAction::Terminate`, not yet stabilized in `Trusted.MirSemantics`).
    pub const fn profile_v2(endian: TargetEndian) -> Self {
        Self { profile: EvalProfile::ProfileV2, endian, record_events: true }
    }

    /// Select the default configuration strictly for stabilized Profile v1
    /// (`program.mir_profile_version == 1`), failing closed on any other
    /// version (including `2`, which requires explicit opt-in via
    /// [`Self::profile_v2`]).
    pub fn for_program(
        program: &Program,
        _manifest_endian: Option<TargetEndian>,
    ) -> Result<Self, FaultDetail> {
        match program.mir_profile_version {
            1 => Ok(Self::profile_v1()),
            other => Err(FaultDetail::unsupported(format!(
                "unsupported mir_profile_version {other} for strict Profile v1 defaults \
                 (opt in explicitly via EvalConfig::profile_v2 / --profile-v2)"
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

/// Complete trace returned by [`eval_body`] and [`eval_body_with_config`].
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

/// Running machine state of the concrete MIR stepper (`Trusted.MirSemantics.State`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MachineState {
    pub frames: Vec<FrameState>,
    pub caller_mem: CallerMemory,
    pub mem: MemoryState,
    pub step_count: usize,
}

/// Validate program-level target, MIR profile, and body-table invariants
/// (`ProgramVerified` structural preconditions) before entry.
pub fn validate_program_config(program: &Program, config: &EvalConfig) -> Result<(), FaultDetail> {
    if program.pointer_width_bits != 64 {
        return Err(FaultDetail::unsupported("only 64-bit targets are supported"));
    }
    if config.is_strict_profile_v1() && program.mir_profile_version != 1 {
        return Err(FaultDetail::unsupported(
            "strict Profile v1 requires mir_profile_version == 1",
        ));
    }
    if config.enable_profile_v2() && !matches!(program.mir_profile_version, 1 | 2) {
        return Err(FaultDetail::unsupported(format!(
            "Profile v2 requires mir_profile_version 1 or 2 (got {})",
            program.mir_profile_version
        )));
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
    /// Initialize execution state for `body_id` (`eval_body` entry point).
    pub fn init(
        program: &Program,
        body_id: usize,
        args: &[Val],
        config: &EvalConfig,
    ) -> Result<Self, FaultDetail> {
        Self::init_with_caller_mem(program, body_id, args, CallerMemory::default(), config)
    }

    /// Initialize execution state with explicit initial `caller_mem`.
    pub fn init_with_caller_mem(
        program: &Program,
        body_id: usize,
        args: &[Val],
        caller_mem: CallerMemory,
        config: &EvalConfig,
    ) -> Result<Self, FaultDetail> {
        validate_program_config(program, config)?;
        if !caller_mem.allocations.is_empty() {
            return Err(FaultDetail::unsupported("non-empty callerMem at entry is unsupported"));
        }
        let body = program
            .bodies
            .get(body_id)
            .ok_or_else(|| FaultDetail::unsupported("entry body id out of bounds"))?;
        validate_body_entry(body, config)?;
        let param_tys = body
            .param_tys()
            .ok_or_else(|| FaultDetail::unsupported("argument count exceeds local count"))?;
        if !check_args_match(args, param_tys, config.enable_profile_v2()) {
            return Err(FaultDetail::unsupported(
                "entry arguments do not match body parameter types",
            ));
        }
        let locals = init_locals(body, args);
        let frame =
            FrameState { def_id: body_id, block_idx: 0, stmt_idx: 0, locals, return_to: None };
        Ok(Self {
            frames: vec![frame],
            caller_mem,
            mem: MemoryState::entry_memory(),
            step_count: 0,
        })
    }

    /// Move immediate local `local_id` of the top frame into a fresh stack
    /// allocation, returning its `MemPlace` (`Trusted.MirSemantics.forceAllocation`).
    pub fn force_allocation(
        &mut self,
        program: &Program,
        local_id: u32,
        config: &EvalConfig,
    ) -> Result<MemPlace, FaultDetail> {
        if self.frames.len() != 1 {
            return Err(FaultDetail::unsupported("force_allocation requires single active frame"));
        }
        let def_id = self.frames[0].def_id;
        let body = program
            .bodies
            .get(def_id)
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
            LocalSlot::Dead => Err(FaultDetail::undefined("force_allocation on dead local")),
            LocalSlot::Indirect { place } => Ok(place),
            LocalSlot::Immediate { .. } => {
                let val = read_immediate_slot(&slot)?;
                let layout = layout_of_ty(ty, config.enable_profile_v2())
                    .ok_or_else(|| FaultDetail::unsupported("local type has no layout"))?;
                let mut next_mem = self.mem.clone();
                let place = next_mem.allocate_stack(layout);
                if let Some(v) = val {
                    store_indirect(
                        &mut next_mem,
                        config.endian,
                        ty,
                        place,
                        &v,
                        config.enable_profile_v2(),
                    )?;
                }
                self.mem = next_mem;
                self.frames[0].locals[idx] = LocalSlot::Indirect { place };
                Ok(place)
            }
            LocalSlot::PartialTuple { fields } => {
                let layout = layout_of_ty(ty, config.enable_profile_v2())
                    .ok_or_else(|| FaultDetail::unsupported("local type has no layout"))?;
                let Some(ity) = ty.as_overflow_pair() else {
                    return Err(FaultDetail::unsupported(
                        "partial tuple force_allocation requires overflow pair type",
                    ));
                };
                if fields.len() != 2 {
                    return Err(FaultDetail::unsupported(
                        "partial tuple force_allocation field count mismatch",
                    ));
                }
                let width_bytes = ity.width.byte_size();
                let mut bytes = vec![
                    AllocByte::Uninit;
                    usize::try_from(layout.size)
                        .expect("overflow pair layout fits usize")
                ];
                if let Some(int_val) = read_immediate_slot(&fields[0])? {
                    let encoded = encode_val(
                        config.endian,
                        &Ty::Int(ity),
                        &int_val,
                        config.enable_profile_v2(),
                    )?;
                    bytes[..width_bytes].copy_from_slice(&encoded);
                }
                if let Some(bool_val) = read_immediate_slot(&fields[1])? {
                    let encoded = encode_val(
                        config.endian,
                        &Ty::Bool,
                        &bool_val,
                        config.enable_profile_v2(),
                    )?;
                    bytes[width_bytes..width_bytes + 1].copy_from_slice(&encoded);
                }
                let mut next_mem = self.mem.clone();
                let place = next_mem.allocate_stack(layout);
                next_mem.write_bytes(place, layout.align_log2, &bytes)?;
                self.mem = next_mem;
                self.frames[0].locals[idx] = LocalSlot::Indirect { place };
                Ok(place)
            }
        }
    }

    /// Execute one small-step transition matching `Trusted.MirSemantics.evalStep`.
    pub fn step(&mut self, program: &Program, config: &EvalConfig) -> StepOutcome {
        if config.is_strict_profile_v1() && self.frames.len() != 1 {
            return StepOutcome::Fault(FaultDetail::unsupported(
                "strict Profile v1 requires single stack frame",
            ));
        }
        let Some(frame_idx) = self.frames.len().checked_sub(1) else {
            return StepOutcome::Fault(FaultDetail::unsupported("empty call stack"));
        };
        let def_id = self.frames[frame_idx].def_id;
        let block_idx = self.frames[frame_idx].block_idx;
        let stmt_idx = self.frames[frame_idx].stmt_idx;
        let Some(body) = program.bodies.get(def_id) else {
            return StepOutcome::Fault(FaultDetail::unsupported("frame def_id out of bounds"));
        };
        let Some(bb) = body.blocks.get(block_idx) else {
            return StepOutcome::Fault(FaultDetail::unsupported("basic block index out of bounds"));
        };
        self.step_count += 1;
        if let Some(stmt) = bb.statements.get(stmt_idx) {
            self.eval_statement(body, frame_idx, stmt, config)
        } else if stmt_idx == bb.statements.len() {
            self.eval_terminator(program, body, bb, frame_idx, config)
        } else {
            StepOutcome::Fault(FaultDetail::unsupported("statement index out of bounds"))
        }
    }

    fn eval_statement(
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
                if let Err(err) = deallocate_local(&mut self.mem, &old) {
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
                if let Err(err) = deallocate_local(&mut self.mem, &old) {
                    return StepOutcome::Fault(err);
                }
                self.frames[frame_idx].stmt_idx += 1;
                format!("storage_dead(_{local})")
            }
            Statement::Assign { local, projection, value } => {
                if !projection.is_empty() && !config.enable_profile_v2() {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "projected assignment is unsupported in Profile v1",
                    ));
                }
                let Some(local_ty) = body.local_tys.get(*local as usize) else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "assignment destination local out of bounds",
                    ));
                };
                let dst_ty = match resolve_projected_ty(local_ty, projection, config) {
                    Ok(ty) => ty,
                    Err(err) => return StepOutcome::Fault(err),
                };
                let mut next_locals = self.frames[frame_idx].locals.clone();
                let mut next_mem = self.mem.clone();
                let val = match eval_rvalue(
                    &body.local_tys,
                    &mut next_locals,
                    &mut next_mem,
                    &dst_ty,
                    value,
                    config,
                ) {
                    Ok(v) => v,
                    Err(err) => return StepOutcome::Fault(err),
                };
                if let Err(err) = write_place(
                    &mut next_locals,
                    &mut next_mem,
                    *local,
                    projection,
                    local_ty,
                    val,
                    config,
                ) {
                    return StepOutcome::Fault(err);
                }
                self.frames[frame_idx].locals = next_locals;
                self.mem = next_mem;
                self.frames[frame_idx].stmt_idx += 1;
                format!("assign(_{local})")
            }
            Statement::Unsupported => {
                return StepOutcome::Fault(FaultDetail::unsupported("unmodeled MIR statement"));
            }
        };
        StepOutcome::Stepped { summary }
    }

    fn eval_terminator(
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
                let ret_val = match self.frames[frame_idx].locals.first() {
                    Some(slot @ (LocalSlot::Immediate { .. } | LocalSlot::PartialTuple { .. })) => {
                        match read_immediate_slot(slot) {
                            Ok(Some(v)) => v,
                            Ok(None) => {
                                return StepOutcome::Fault(FaultDetail::undefined(
                                    "returning with uninitialized _0",
                                ));
                            }
                            Err(err) => return StepOutcome::Fault(err),
                        }
                    }
                    Some(LocalSlot::Dead) => {
                        return StepOutcome::Fault(FaultDetail::undefined(
                            "returning with uninitialized or dead _0",
                        ));
                    }
                    Some(LocalSlot::Indirect { place }) => {
                        let Some(ret_ty) = body.local_tys.first() else {
                            return StepOutcome::Fault(FaultDetail::unsupported(
                                "body missing return local _0 type",
                            ));
                        };
                        match load_indirect(
                            &self.mem,
                            config.endian,
                            ret_ty,
                            *place,
                            config.enable_profile_v2(),
                        ) {
                            Ok(Some(v)) => v,
                            Ok(None) => {
                                return StepOutcome::Fault(FaultDetail::undefined(
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
                if let Some(return_to) = self.frames[frame_idx].return_to.clone() {
                    if !config.enable_profile_v2() {
                        return StepOutcome::Fault(FaultDetail::unsupported(
                            "multi-frame return unsupported in Profile v1",
                        ));
                    }
                    let Some(caller_idx) = frame_idx.checked_sub(1) else {
                        return StepOutcome::Fault(FaultDetail::unsupported(
                            "call return target with empty caller stack",
                        ));
                    };
                    let caller_def_id = self.frames[caller_idx].def_id;
                    let Some(caller_body) = program.bodies.get(caller_def_id) else {
                        return StepOutcome::Fault(FaultDetail::unsupported(
                            "caller body id out of bounds",
                        ));
                    };
                    let Some(dst_local_ty) =
                        caller_body.local_tys.get(return_to.dst_local as usize)
                    else {
                        return StepOutcome::Fault(FaultDetail::unsupported(
                            "call return destination local out of bounds",
                        ));
                    };
                    let mut next_locals = self.frames[caller_idx].locals.clone();
                    let mut next_mem = self.mem.clone();
                    for slot in &self.frames[frame_idx].locals {
                        if let Err(err) = deallocate_local(&mut next_mem, slot) {
                            return StepOutcome::Fault(err);
                        }
                    }
                    if let Err(err) = write_place(
                        &mut next_locals,
                        &mut next_mem,
                        return_to.dst_local,
                        &return_to.dst_projection,
                        dst_local_ty,
                        ret_val,
                        config,
                    ) {
                        return StepOutcome::Fault(err);
                    }
                    self.frames.pop();
                    self.frames[caller_idx].locals = next_locals;
                    self.mem = next_mem;
                    self.frames[caller_idx].block_idx = return_to.block_idx;
                    self.frames[caller_idx].stmt_idx = 0;
                    StepOutcome::Stepped {
                        summary: format!("return_to_caller(bb{})", return_to.block_idx),
                    }
                } else {
                    StepOutcome::Done(TerminalOut::Returned {
                        ret: ret_val,
                        caller_mem: self.caller_mem.clone(),
                    })
                }
            }
            Terminator::Unreachable => {
                StepOutcome::Fault(FaultDetail::undefined("executed Unreachable terminator"))
            }
            Terminator::SwitchInt { operand, targets, otherwise } => {
                let mut next_locals = self.frames[frame_idx].locals.clone();
                let mut next_mem = self.mem.clone();
                let discr_val = match eval_primitive_operand(
                    &body.local_tys,
                    &mut next_locals,
                    &mut next_mem,
                    operand,
                    config,
                ) {
                    Ok(v) => v,
                    Err(err) => return StepOutcome::Fault(err),
                };
                let target_res = match &discr_val {
                    Val::Scalar(sv) => eval_scalar_switch(sv.width, sv.bits, *otherwise, targets),
                    Val::Bool(b) => eval_bool_switch(*b, *otherwise, targets),
                    Val::Char(c) => eval_char_switch(*c, *otherwise, targets),
                    _ => {
                        if targets.is_empty() {
                            Ok(*otherwise)
                        } else {
                            Err(FaultDetail::unsupported(
                                "non-empty SwitchInt targets on non-scalar primitive",
                            ))
                        }
                    }
                };
                match target_res {
                    Ok(target) => {
                        self.frames[frame_idx].locals = next_locals;
                        self.mem = next_mem;
                        self.frames[frame_idx].block_idx = target as usize;
                        self.frames[frame_idx].stmt_idx = 0;
                        StepOutcome::Stepped { summary: format!("switch_int(->bb{target})") }
                    }
                    Err(err) => StepOutcome::Fault(err),
                }
            }
            Terminator::Assert { cond, expected, msg: _, target, unwind }
                if config.enable_profile_v2() =>
            {
                let mut next_locals = self.frames[frame_idx].locals.clone();
                let mut next_mem = self.mem.clone();
                let cond_val = match eval_primitive_operand(
                    &body.local_tys,
                    &mut next_locals,
                    &mut next_mem,
                    cond,
                    config,
                ) {
                    Ok(v) => v,
                    Err(err) => return StepOutcome::Fault(err),
                };
                let Val::Bool(actual) = cond_val else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "Assert condition must be bool",
                    ));
                };
                self.frames[frame_idx].locals = next_locals;
                self.mem = next_mem;
                if actual == *expected {
                    self.frames[frame_idx].block_idx = *target as usize;
                    self.frames[frame_idx].stmt_idx = 0;
                    StepOutcome::Stepped { summary: format!("assert_ok(->bb{target})") }
                } else {
                    self.unwind_frames(*unwind)
                }
            }
            Terminator::UnwindResume if config.enable_profile_v2() => {
                self.unwind_frames(UnwindAction::Continue)
            }
            Terminator::Call { callee, args, dst_local, dst_projection, target, unwind }
                if config.enable_profile_v2() =>
            {
                if self.frames.len() >= MAX_CALL_DEPTH_V2 {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "call stack depth limit exceeded",
                    ));
                }
                let Some(callee_body) = program.bodies.get(*callee as usize) else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "callee body out of bounds",
                    ));
                };
                if let Err(err) = validate_body_entry(callee_body, config) {
                    return StepOutcome::Fault(err);
                }
                let Some(param_tys) = callee_body.param_tys() else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "callee arg_count out of bounds",
                    ));
                };
                if args.len() != param_tys.len() {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "call argument count does not match callee arity",
                    ));
                }
                let Some(dst_base_ty) = body.local_tys.get(*dst_local as usize) else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "call destination local out of bounds",
                    ));
                };
                let dst_ty = match resolve_projected_ty(dst_base_ty, dst_projection, config) {
                    Ok(ty) => ty,
                    Err(err) => return StepOutcome::Fault(err),
                };
                if !dst_ty.structural_eq(&callee_body.local_tys[0]) {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "call destination type does not match callee return type",
                    ));
                }
                let Some(return_block) = *target else {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "diverging Call terminator without return block is unsupported",
                    ));
                };
                for (arg_op, expected_ty) in args.iter().zip(param_tys.iter()) {
                    let arg_ty = match operand_static_ty(&body.local_tys, arg_op, config) {
                        Ok(ty) => ty,
                        Err(err) => return StepOutcome::Fault(err),
                    };
                    if !arg_ty.structural_eq(expected_ty) {
                        return StepOutcome::Fault(FaultDetail::unsupported(
                            "call argument operand type does not match callee parameter type",
                        ));
                    }
                }
                let mut next_locals = self.frames[frame_idx].locals.clone();
                let mut next_mem = self.mem.clone();
                let mut arg_vals = Vec::with_capacity(args.len());
                for (arg_op, expected_ty) in args.iter().zip(param_tys.iter()) {
                    match eval_operand_to_slot(
                        &body.local_tys,
                        &mut next_locals,
                        &mut next_mem,
                        |ty| ty.structural_eq(expected_ty),
                        arg_op,
                        config,
                    ) {
                        Ok((_, Some(v))) => arg_vals.push(v),
                        Ok((_, None)) => {
                            return StepOutcome::Fault(FaultDetail::undefined(
                                "passing uninitialized argument to Call",
                            ));
                        }
                        Err(err) => return StepOutcome::Fault(err),
                    }
                }
                if !check_args_match(&arg_vals, param_tys, config.enable_profile_v2()) {
                    return StepOutcome::Fault(FaultDetail::unsupported(
                        "call arguments do not match callee parameter types",
                    ));
                }
                self.frames[frame_idx].locals = next_locals;
                self.mem = next_mem;
                let callee_locals = init_locals(callee_body, &arg_vals);
                self.frames.push(FrameState {
                    def_id: *callee as usize,
                    block_idx: 0,
                    stmt_idx: 0,
                    locals: callee_locals,
                    return_to: Some(CallReturnTarget {
                        block_idx: return_block as usize,
                        dst_local: *dst_local,
                        dst_projection: dst_projection.clone(),
                        unwind: *unwind,
                    }),
                });
                StepOutcome::Stepped { summary: format!("call(body_{callee})") }
            }
            Terminator::UnwindResume
            | Terminator::Assert { .. }
            | Terminator::Call { .. }
            | Terminator::Unsupported => {
                StepOutcome::Fault(FaultDetail::unsupported("unmodeled MIR terminator"))
            }
        }
    }

    fn unwind_frames(&mut self, mut action: UnwindAction) -> StepOutcome {
        loop {
            match action {
                UnwindAction::Cleanup { block } => {
                    let Some(idx) = self.frames.len().checked_sub(1) else {
                        return StepOutcome::Fault(FaultDetail::unsupported("empty call stack"));
                    };
                    self.frames[idx].block_idx = block as usize;
                    self.frames[idx].stmt_idx = 0;
                    return StepOutcome::Stepped {
                        summary: format!("unwind_cleanup(->bb{block})"),
                    };
                }
                UnwindAction::Unreachable => {
                    return StepOutcome::Fault(FaultDetail::undefined(
                        "unwound into UnwindAction::Unreachable",
                    ));
                }
                UnwindAction::Terminate => {
                    return StepOutcome::Aborted { caller_mem: self.caller_mem.clone() };
                }
                UnwindAction::Continue => {
                    let Some(top) = self.frames.last() else {
                        return StepOutcome::Fault(FaultDetail::unsupported("empty call stack"));
                    };
                    let Some(return_to) = top.return_to.clone() else {
                        return StepOutcome::Done(TerminalOut::Unwound {
                            caller_mem: self.caller_mem.clone(),
                        });
                    };
                    for slot in &top.locals {
                        if let Err(err) = deallocate_local(&mut self.mem, slot) {
                            return StepOutcome::Fault(err);
                        }
                    }
                    self.frames.pop();
                    action = return_to.unwind;
                }
            }
        }
    }
}

/// Evaluate body `body_id` with strict Profile v1 defaults up to `fuel` steps.
pub fn eval_body(program: &Program, body_id: usize, args: &[Val], fuel: usize) -> StepTrace {
    let config = EvalConfig::profile_v1();
    eval_body_with_config(program, body_id, args, fuel, &config)
}

/// Evaluate body `body_id` under strict Profile v1 auto-selection (rejecting
/// `mir_profile_version != 1`; use [`eval_body_with_config`] with
/// [`EvalConfig::profile_v2`] to opt into preview Profile v2 extensions).
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

/// Evaluate body matching `identity` with strict Profile v1 defaults (via [`eval_body`]).
pub fn eval_body_by_identity(
    program: &Program,
    identity: &str,
    args: &[Val],
    fuel: usize,
) -> Result<StepTrace, FaultDetail> {
    let Some(body_id) = program.bodies.iter().position(|b| b.identity == identity) else {
        return Err(FaultDetail::unsupported(format!("no body with identity '{identity}' found")));
    };
    Ok(eval_body(program, body_id, args, fuel))
}

/// Evaluate `body_id` with explicit [`EvalConfig`] up to `fuel` small steps.
pub fn eval_body_with_config(
    program: &Program,
    body_id: usize,
    args: &[Val],
    fuel: usize,
    config: &EvalConfig,
) -> StepTrace {
    let identity = program.bodies.get(body_id).map(|b| b.identity.clone()).unwrap_or_default();
    let mut state = match MachineState::init(program, body_id, args, config) {
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

fn zst_default_val(ty: &Ty) -> Option<Val> {
    match ty {
        Ty::Unit => Some(Val::Unit),
        Ty::Enum(ety) if is_zst_enum_ty(ety) => Some(Val::EnumVal { ty: ety.clone(), variant: 0 }),
        Ty::Tuple { fields } => {
            let vals = fields.iter().map(zst_default_val).collect::<Option<Vec<_>>>()?;
            Some(Val::Tuple(vals))
        }
        _ => None,
    }
}

fn live_uninit_slot(ty: &Ty) -> LocalSlot {
    LocalSlot::Immediate { val: zst_default_val(ty) }
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
        bb.statements.iter().all(|stmt| match stmt {
            Statement::Assign {
                local: dst_local,
                projection: dst_proj,
                value: Rvalue::Discriminant { local: src_local, projection: src_proj },
            } if dst_proj.is_empty() && src_proj.is_empty() => {
                let (Some(src_ty), Some(dst_ty)) = (
                    body.local_tys.get(*src_local as usize),
                    body.local_tys.get(*dst_local as usize),
                ) else {
                    return true;
                };
                match src_ty {
                    Ty::Enum(ety) if enum_admitted(ety) => {
                        dst_ty.structural_eq(&Ty::Int(ety.discr()))
                    }
                    Ty::Ordering => {
                        dst_ty.structural_eq(&Ty::Int(IntTy { width: IntWidth::I8, signed: true }))
                    }
                    _ => true,
                }
            }
            _ => true,
        })
    })
}

fn cast_types_valid(body: &Body) -> bool {
    body.blocks.iter().all(|bb| {
        bb.statements.iter().all(|stmt| match stmt {
            Statement::Assign {
                local: dst_local,
                projection: dst_proj,
                value: Rvalue::Cast { cast_kind: CastKind::IntToInt, ty: cast_ty, .. },
            } if dst_proj.is_empty() => {
                let Some(dst_ty) = body.local_tys.get(*dst_local as usize) else {
                    return true;
                };
                dst_ty.structural_eq(cast_ty)
            }
            _ => true,
        })
    })
}

/// Validate static body-admission invariants (`BodyStaticAdmitted`) prior to
/// executing or probing `body`.
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
    if !body.local_tys.iter().all(|ty| is_supported_local_ty(ty, config.enable_profile_v2())) {
        return Err(FaultDetail::unsupported("body contains unsupported local variable type"));
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

fn deallocate_local(mem: &mut MemoryState, old: &LocalSlot) -> Result<(), FaultDetail> {
    match old {
        LocalSlot::Indirect { place } => mem.deallocate_stack(*place),
        LocalSlot::PartialTuple { fields } => {
            for field in fields {
                deallocate_local(mem, field)?;
            }
            Ok(())
        }
        LocalSlot::Dead | LocalSlot::Immediate { .. } => Ok(()),
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

fn read_immediate_slot(slot: &LocalSlot) -> Result<Option<Val>, FaultDetail> {
    match slot {
        LocalSlot::Dead => Err(FaultDetail::undefined("reading dead local")),
        LocalSlot::Immediate { val } => Ok(val.clone()),
        LocalSlot::PartialTuple { fields } => {
            let mut vals = Vec::with_capacity(fields.len());
            for field in fields {
                match read_immediate_slot(field)? {
                    Some(v) => vals.push(v),
                    None => return Ok(None),
                }
            }
            Ok(Some(Val::Tuple(vals)))
        }
        LocalSlot::Indirect { .. } => {
            Err(FaultDetail::unsupported("unexpected indirect slot in immediate read"))
        }
    }
}

fn read_projected_slot(
    slot: &LocalSlot,
    base_ty: &Ty,
    projection: &[ProjectionElem],
    config: &EvalConfig,
) -> Result<Option<Val>, FaultDetail> {
    if projection.is_empty() {
        return read_immediate_slot(slot);
    }
    match (slot, &projection[0]) {
        (LocalSlot::Dead, _) => Err(FaultDetail::undefined("Copy from dead local")),
        (LocalSlot::Immediate { val: None }, _) => {
            let projected_ty = resolve_projected_ty(base_ty, projection, config)?;
            Ok(zst_default_val(&projected_ty))
        }
        (LocalSlot::Immediate { val: Some(v) }, _) => project_val(v, projection).map(Some),
        (LocalSlot::PartialTuple { fields }, ProjectionElem::Field { field_idx, .. }) => {
            let field_tys = tuple_field_tys(base_ty).ok_or_else(|| {
                FaultDetail::unsupported("field projection on non-tuple local type")
            })?;
            let child_ty = field_tys
                .get(*field_idx as usize)
                .ok_or_else(|| FaultDetail::unsupported("tuple field index out of bounds"))?;
            let child = fields
                .get(*field_idx as usize)
                .ok_or_else(|| FaultDetail::unsupported("tuple field index out of bounds"))?;
            read_projected_slot(child, child_ty, &projection[1..], config)
        }
        (_, ProjectionElem::Deref | ProjectionElem::Unsupported)
        | (LocalSlot::Indirect { .. }, _) => {
            Err(FaultDetail::unsupported("unsupported place projection"))
        }
    }
}

fn move_projected_slot(
    slot: &mut LocalSlot,
    base_ty: &Ty,
    projection: &[ProjectionElem],
    config: &EvalConfig,
) -> Result<(Ty, Option<Val>), FaultDetail> {
    if projection.is_empty() {
        if matches!(slot, LocalSlot::Dead) {
            return Err(FaultDetail::undefined("Move from dead local"));
        }
        let val = read_immediate_slot(slot)?;
        *slot = live_uninit_slot(base_ty);
        return Ok((base_ty.clone(), val));
    }
    if !config.enable_profile_v2() {
        return Err(FaultDetail::unsupported("projected Move operand unsupported"));
    }
    let projected_ty = resolve_projected_ty(base_ty, projection, config)?;
    match slot {
        LocalSlot::Dead => return Err(FaultDetail::undefined("Move from dead local")),
        LocalSlot::Immediate { val: None } => {
            let zst = zst_default_val(&projected_ty);
            return Ok((projected_ty, zst));
        }
        LocalSlot::Immediate { val: Some(Val::Tuple(vals)) } => {
            let field_slots =
                vals.iter().map(|v| LocalSlot::Immediate { val: Some(v.clone()) }).collect();
            *slot = LocalSlot::PartialTuple { fields: field_slots };
        }
        LocalSlot::Immediate { val: Some(_) } => {
            return Err(FaultDetail::unsupported(
                "field projection move on non-tuple runtime value",
            ));
        }
        LocalSlot::PartialTuple { .. } => {}
        LocalSlot::Indirect { .. } => {
            return Err(FaultDetail::unsupported("projected Move on indirect local unsupported"));
        }
    }
    let ProjectionElem::Field { field_idx, .. } = &projection[0] else {
        return Err(FaultDetail::unsupported("unsupported place projection element"));
    };
    let field_tys = tuple_field_tys(base_ty)
        .ok_or_else(|| FaultDetail::unsupported("field projection on non-tuple local type"))?;
    let child_ty = field_tys
        .get(*field_idx as usize)
        .ok_or_else(|| FaultDetail::unsupported("tuple field index out of bounds"))?;
    let LocalSlot::PartialTuple { fields } = slot else {
        unreachable!("promoted to PartialTuple above");
    };
    let child_slot = fields
        .get_mut(*field_idx as usize)
        .ok_or_else(|| FaultDetail::unsupported("tuple value field index out of bounds"))?;
    let (_, val) = move_projected_slot(child_slot, child_ty, &projection[1..], config)?;
    Ok((projected_ty, val))
}

fn resolve_projected_ty(
    base_ty: &Ty,
    projection: &[ProjectionElem],
    config: &EvalConfig,
) -> Result<Ty, FaultDetail> {
    let mut current = base_ty.clone();
    for elem in projection {
        if !config.enable_profile_v2() {
            return Err(FaultDetail::unsupported("place projection unsupported in Profile v1"));
        }
        match elem {
            ProjectionElem::Field { field_idx, ty } => {
                let expected = if let Some(ity) = current.as_overflow_pair() {
                    match field_idx {
                        0 => Ty::Int(ity),
                        1 => Ty::Bool,
                        _ => {
                            return Err(FaultDetail::unsupported(
                                "overflow pair field index out of bounds",
                            ));
                        }
                    }
                } else if let Ty::Tuple { fields } = &current {
                    fields.get(*field_idx as usize).cloned().ok_or_else(|| {
                        FaultDetail::unsupported("tuple field index out of bounds")
                    })?
                } else {
                    return Err(FaultDetail::unsupported(
                        "field projection on non-tuple local type",
                    ));
                };
                if !expected.structural_eq(ty) {
                    return Err(FaultDetail::unsupported("field projection type mismatch"));
                }
                current = expected;
            }
            ProjectionElem::Deref | ProjectionElem::Unsupported => {
                return Err(FaultDetail::unsupported("unsupported place projection element"));
            }
        }
    }
    Ok(current)
}

fn project_val(val: &Val, projection: &[ProjectionElem]) -> Result<Val, FaultDetail> {
    let mut cur = val;
    for elem in projection {
        match elem {
            ProjectionElem::Field { field_idx, .. } => match cur {
                Val::Tuple(fields) => {
                    cur = fields.get(*field_idx as usize).ok_or_else(|| {
                        FaultDetail::unsupported("tuple value field index out of bounds")
                    })?;
                }
                _ => {
                    return Err(FaultDetail::unsupported(
                        "field projection read on non-tuple runtime value",
                    ));
                }
            },
            ProjectionElem::Deref | ProjectionElem::Unsupported => {
                return Err(FaultDetail::unsupported("unsupported value projection"));
            }
        }
    }
    Ok(cur.clone())
}

fn eval_operand_to_slot<F>(
    body_locals: &[Ty],
    locals: &mut [LocalSlot],
    mem: &mut MemoryState,
    ty_ok: F,
    opnd: &Operand,
    config: &EvalConfig,
) -> Result<(Ty, Option<Val>), FaultDetail>
where
    F: Fn(&Ty) -> bool,
{
    match opnd {
        Operand::Copy { local, projection } => {
            let idx = *local as usize;
            let (Some(base_ty), Some(slot)) = (body_locals.get(idx), locals.get(idx)) else {
                return Err(FaultDetail::unsupported("operand Copy local out of bounds"));
            };
            match slot {
                LocalSlot::Dead => Err(FaultDetail::undefined("Copy from dead local")),
                LocalSlot::Immediate { .. } | LocalSlot::PartialTuple { .. } => {
                    if projection.is_empty() {
                        Ok((base_ty.clone(), read_immediate_slot(slot)?))
                    } else if config.enable_profile_v2() {
                        let projected_ty = resolve_projected_ty(base_ty, projection, config)?;
                        let projected_val = read_projected_slot(slot, base_ty, projection, config)?;
                        Ok((projected_ty, projected_val))
                    } else {
                        Err(FaultDetail::unsupported("projected Copy operand unsupported"))
                    }
                }
                LocalSlot::Indirect { place } => {
                    if !projection.is_empty() {
                        return Err(FaultDetail::unsupported(
                            "projected Copy on indirect local unsupported",
                        ));
                    }
                    if !ty_ok(base_ty) {
                        return Err(FaultDetail::unsupported(
                            "operand type rejected before indirect load",
                        ));
                    }
                    let val = load_indirect(
                        mem,
                        config.endian,
                        base_ty,
                        *place,
                        config.enable_profile_v2(),
                    )?;
                    Ok((base_ty.clone(), val))
                }
            }
        }
        Operand::Move { local, projection } => {
            let idx = *local as usize;
            let (Some(base_ty), Some(slot)) = (body_locals.get(idx), locals.get(idx).cloned())
            else {
                return Err(FaultDetail::unsupported("operand Move local out of bounds"));
            };
            match slot {
                LocalSlot::Dead => Err(FaultDetail::undefined("Move from dead local")),
                LocalSlot::Immediate { .. } | LocalSlot::PartialTuple { .. } => {
                    move_projected_slot(&mut locals[idx], base_ty, projection, config)
                }
                LocalSlot::Indirect { place } => {
                    if !projection.is_empty() {
                        return Err(FaultDetail::unsupported(
                            "projected Move on indirect local unsupported",
                        ));
                    }
                    if !ty_ok(base_ty) {
                        return Err(FaultDetail::unsupported(
                            "operand type rejected before indirect Move",
                        ));
                    }
                    let val = load_indirect(
                        mem,
                        config.endian,
                        base_ty,
                        place,
                        config.enable_profile_v2(),
                    )?;
                    deinit_indirect(mem, base_ty, place, config.enable_profile_v2())?;
                    Ok((base_ty.clone(), val))
                }
            }
        }
        Operand::Constant { ty, lit } => {
            let val = eval_const_lit(ty, lit)?;
            Ok((ty.clone(), Some(val)))
        }
    }
}

fn eval_primitive_operand(
    body_locals: &[Ty],
    locals: &mut [LocalSlot],
    mem: &mut MemoryState,
    opnd: &Operand,
    config: &EvalConfig,
) -> Result<Val, FaultDetail> {
    let (ty, opt_val) =
        eval_operand_to_slot(body_locals, locals, mem, is_primitive_readable_ty, opnd, config)?;
    if !is_primitive_readable_ty(&ty) {
        return Err(FaultDetail::unsupported("non-primitive operand type"));
    }
    opt_val.ok_or_else(|| FaultDetail::undefined("reading uninitialized primitive operand"))
}

fn eval_rvalue(
    body_locals: &[Ty],
    locals: &mut [LocalSlot],
    mem: &mut MemoryState,
    dst_ty: &Ty,
    rvalue: &Rvalue,
    config: &EvalConfig,
) -> Result<Val, FaultDetail> {
    match rvalue {
        Rvalue::Use { operand, with_retag } => {
            if *with_retag && !dst_ty.is_retag_noop() {
                return Err(FaultDetail::unsupported(
                    "retagging Use rvalue on reference-bearing type is unsupported",
                ));
            }
            let (src_ty, opt_val) = eval_operand_to_slot(
                body_locals,
                locals,
                mem,
                |src_ty| src_ty.structural_eq(dst_ty),
                operand,
                config,
            )?;
            if !src_ty.structural_eq(dst_ty) {
                return Err(FaultDetail::unsupported(
                    "Use operand type disagrees with destination type",
                ));
            }
            opt_val.ok_or_else(|| FaultDetail::undefined("Use reading uninitialized value"))
        }
        Rvalue::Binary { op, left, right } => {
            let l_val = eval_primitive_operand(body_locals, locals, mem, left, config)?;
            let r_val = eval_primitive_operand(body_locals, locals, mem, right, config)?;
            eval_bin_op(*op, &l_val, &r_val)
        }
        Rvalue::Unary { op, operand } => {
            let val = eval_primitive_operand(body_locals, locals, mem, operand, config)?;
            eval_un_op(*op, &val)
        }
        Rvalue::Cast { cast_kind, operand, ty } => {
            if *cast_kind != CastKind::IntToInt {
                return Err(FaultDetail::unsupported("unsupported cast kind"));
            }
            if !dst_ty.structural_eq(ty) {
                return Err(FaultDetail::unsupported("cast assignment destination type invalid"));
            }
            let (src_ty, opt_val) =
                eval_operand_to_slot(body_locals, locals, mem, is_int_like_ty, operand, config)?;
            if !is_int_like_ty(&src_ty) {
                return Err(FaultDetail::unsupported("cast source is not integer-like"));
            }
            let v = opt_val
                .ok_or_else(|| FaultDetail::undefined("Cast reading uninitialized operand"))?;
            eval_int_to_int_cast(*cast_kind, &v, ty)
        }
        Rvalue::Discriminant { local, projection } => {
            let idx = *local as usize;
            let (Some(src_ty), Some(slot)) = (body_locals.get(idx), locals.get(idx)) else {
                return Err(FaultDetail::unsupported("Discriminant local out of bounds"));
            };
            if projection.is_empty() {
                let expected_dst_ty = match src_ty {
                    Ty::Enum(ety) if enum_admitted(ety) => Some(Ty::Int(ety.discr())),
                    Ty::Ordering => Some(Ty::Int(IntTy { width: IntWidth::I8, signed: true })),
                    _ => None,
                };
                if let Some(expected) = expected_dst_ty
                    && !dst_ty.structural_eq(&expected)
                {
                    return Err(FaultDetail::unsupported(
                        "discriminant assignment destination type invalid",
                    ));
                }
            }
            let opt_val = match slot {
                LocalSlot::Dead => {
                    return Err(FaultDetail::undefined("Discriminant read on dead local"));
                }
                LocalSlot::Immediate { .. } | LocalSlot::PartialTuple { .. } => {
                    if !projection.is_empty() {
                        return Err(FaultDetail::unsupported(
                            "projected Discriminant rvalue is unsupported",
                        ));
                    }
                    read_immediate_slot(slot)?
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
                    load_indirect(mem, config.endian, src_ty, *place, config.enable_profile_v2())?
                }
            };
            match src_ty {
                Ty::Enum(ety) => eval_discriminant_of_val(ety, opt_val.as_ref()),
                Ty::Ordering => eval_ordering_discriminant_of_val(opt_val.as_ref()),
                _ => Err(FaultDetail::unsupported(
                    "Discriminant rvalue requires fieldless enum or Ordering local",
                )),
            }
        }
        Rvalue::AggregateTuple { fields } if config.enable_profile_v2() => {
            eval_tuple_aggregate(body_locals, locals, mem, dst_ty, fields, config)
        }
        Rvalue::Aggregate { aggregate_kind: AggregateKind::Tuple, fields }
            if config.enable_profile_v2() =>
        {
            eval_tuple_aggregate(body_locals, locals, mem, dst_ty, fields, config)
        }
        Rvalue::AggregateTuple { .. }
        | Rvalue::Aggregate { .. }
        | Rvalue::Ref { .. }
        | Rvalue::AddressOf { .. }
        | Rvalue::Unsupported => Err(FaultDetail::unsupported("unmodeled MIR rvalue")),
    }
}

fn operand_static_ty(
    body_locals: &[Ty],
    opnd: &Operand,
    config: &EvalConfig,
) -> Result<Ty, FaultDetail> {
    match opnd {
        Operand::Copy { local, projection } | Operand::Move { local, projection } => {
            let Some(base_ty) = body_locals.get(*local as usize) else {
                return Err(FaultDetail::unsupported("operand local out of bounds"));
            };
            if projection.is_empty() {
                Ok(base_ty.clone())
            } else {
                resolve_projected_ty(base_ty, projection, config)
            }
        }
        Operand::Constant { ty, .. } => Ok(ty.clone()),
    }
}

fn eval_tuple_aggregate(
    body_locals: &[Ty],
    locals: &mut [LocalSlot],
    mem: &mut MemoryState,
    dst_ty: &Ty,
    fields: &[Operand],
    config: &EvalConfig,
) -> Result<Val, FaultDetail> {
    if fields.is_empty() {
        return match dst_ty {
            Ty::Unit => Ok(Val::Unit),
            Ty::Tuple { fields: ty_fields } if ty_fields.is_empty() => Ok(Val::Tuple(Vec::new())),
            _ => Err(FaultDetail::unsupported(
                "empty tuple aggregate requires unit or empty tuple destination type",
            )),
        };
    }
    let Some(expected_tys) = tuple_field_tys(dst_ty) else {
        return Err(FaultDetail::unsupported("tuple aggregate requires tuple destination type"));
    };
    if expected_tys.len() != fields.len() {
        return Err(FaultDetail::unsupported(
            "tuple aggregate field count does not match destination tuple type",
        ));
    }
    for (field_op, expected_ty) in fields.iter().zip(expected_tys.iter()) {
        let field_ty = operand_static_ty(body_locals, field_op, config)?;
        if !field_ty.structural_eq(expected_ty) {
            return Err(FaultDetail::unsupported(
                "tuple aggregate field operand type does not match destination tuple field",
            ));
        }
    }
    let mut vals = Vec::with_capacity(fields.len());
    for (field_op, expected_ty) in fields.iter().zip(expected_tys.iter()) {
        let (_, opt_val) = eval_operand_to_slot(
            body_locals,
            locals,
            mem,
            |ty| ty.structural_eq(expected_ty),
            field_op,
            config,
        )?;
        let val = opt_val
            .ok_or_else(|| FaultDetail::undefined("tuple aggregate reading uninitialized field"))?;
        vals.push(val);
    }
    Ok(Val::Tuple(vals))
}

fn eval_discriminant_of_val(
    ety: &crate::ir::EnumTy,
    opt_val: Option<&Val>,
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
        (crate::ir::EnumTagRepr::Scalar(_), None) => {
            Err(FaultDetail::undefined("Discriminant read on uninitialized scalar-tagged enum"))
        }
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

fn eval_ordering_discriminant_of_val(opt_val: Option<&Val>) -> Result<Val, FaultDetail> {
    match opt_val {
        None => Err(FaultDetail::undefined("Discriminant read on uninitialized Ordering")),
        Some(Val::Ordering(ord)) => {
            Ok(Val::Scalar(ScalarVal::new(IntWidth::I8, true, ord.tag_bits())))
        }
        Some(_) => Err(FaultDetail::unsupported("non-Ordering value in Ordering Discriminant")),
    }
}

fn write_projected_slot(
    slot: &mut LocalSlot,
    base_ty: &Ty,
    projection: &[ProjectionElem],
    val: Val,
) -> Result<(), FaultDetail> {
    if projection.is_empty() {
        *slot = LocalSlot::Immediate { val: Some(val) };
        return Ok(());
    }
    match slot {
        LocalSlot::Dead => return Err(FaultDetail::undefined("write to dead local")),
        LocalSlot::Immediate { val: Some(Val::Tuple(vals)) } => {
            let field_slots =
                vals.iter().map(|v| LocalSlot::Immediate { val: Some(v.clone()) }).collect();
            *slot = LocalSlot::PartialTuple { fields: field_slots };
        }
        LocalSlot::Immediate { val: None } => {
            let field_tys = tuple_field_tys(base_ty).ok_or_else(|| {
                FaultDetail::unsupported("projected write to non-tuple local type")
            })?;
            *slot = LocalSlot::PartialTuple {
                fields: field_tys.iter().map(live_uninit_slot).collect(),
            };
        }
        LocalSlot::Immediate { val: Some(_) } => {
            return Err(FaultDetail::unsupported("projected write to non-tuple runtime value"));
        }
        LocalSlot::PartialTuple { .. } => {}
        LocalSlot::Indirect { .. } => {
            return Err(FaultDetail::unsupported("projected write to indirect local unsupported"));
        }
    }
    let ProjectionElem::Field { field_idx, .. } = &projection[0] else {
        return Err(FaultDetail::unsupported("unsupported place projection element"));
    };
    let field_tys = tuple_field_tys(base_ty)
        .ok_or_else(|| FaultDetail::unsupported("projected write to non-tuple local type"))?;
    let child_ty = field_tys
        .get(*field_idx as usize)
        .ok_or_else(|| FaultDetail::unsupported("tuple field index out of bounds"))?;
    let LocalSlot::PartialTuple { fields } = slot else {
        unreachable!("promoted to PartialTuple above");
    };
    let child_slot = fields
        .get_mut(*field_idx as usize)
        .ok_or_else(|| FaultDetail::unsupported("tuple field index out of bounds"))?;
    write_projected_slot(child_slot, child_ty, &projection[1..], val)
}

fn write_place(
    locals: &mut [LocalSlot],
    mem: &mut MemoryState,
    dst_local_id: u32,
    projection: &[ProjectionElem],
    dst_local_ty: &Ty,
    val: Val,
    config: &EvalConfig,
) -> Result<(), FaultDetail> {
    let dst_ty = resolve_projected_ty(dst_local_ty, projection, config)?;
    if !check_val(&val, &dst_ty, config.enable_profile_v2()) {
        return Err(FaultDetail::unsupported("assigned value disagrees with destination type"));
    }
    let idx = dst_local_id as usize;
    let Some(slot) = locals.get_mut(idx) else {
        return Err(FaultDetail::unsupported("destination local id out of bounds"));
    };
    if !projection.is_empty() {
        if !config.enable_profile_v2() {
            return Err(FaultDetail::unsupported("projected write unsupported in Profile v1"));
        }
        return write_projected_slot(slot, dst_local_ty, projection, val);
    }
    match slot {
        LocalSlot::Dead => Err(FaultDetail::undefined("write to dead destination local")),
        LocalSlot::Immediate { .. } | LocalSlot::PartialTuple { .. } => {
            *slot = LocalSlot::Immediate { val: Some(val) };
            Ok(())
        }
        LocalSlot::Indirect { place } => {
            store_indirect(mem, config.endian, &dst_ty, *place, &val, config.enable_profile_v2())
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
            return Err(FaultDetail::undefined("invalid boolean bit pattern in SwitchInt case"));
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
            return Err(FaultDetail::undefined("invalid char scalar in SwitchInt case"));
        }
        if case_bits as u32 == discr_u32 {
            return Ok(target);
        }
    }
    Ok(otherwise)
}
