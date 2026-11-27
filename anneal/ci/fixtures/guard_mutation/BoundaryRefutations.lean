-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import GuardRefuteBase

/-!
# Negative Refutations for `Trusted.MirSemantics.Boundary` Soundness Guards

Exercises every top-level verification-judgment and static-admission guard in
`Trusted/MirSemantics/Boundary.lean`:

- `WellFormed`: forbids reachable faults.
- `SatisfiesPost`: requires `WellFormed` and enforces `post` on terminal output.
- `BodyStaticAdmitted`: all 9 unconditional single-body static-admission
  conjuncts (`singleBodyStaticAdmitted` in `Trusted/MirSemantics/State.lean`,
  tested with uninhabited `MirTy.never` parameter bodies so `ValidEntryArgs`
  is empty and `BodyStaticAdmitted` is the sole line of defense).
- `BodyVerified`: binds `body` to `p.bodies[defId]`, requires
  `BodyStaticAdmitted`, and ignores `safetyPre` on safe functions.
- `ProgramVerified`: non-empty `bodies`, `entryDefId < bodies.length`,
  `bodiesHaveUniqueIdentities`, universal per-body `BodyVerified`, and
  `specs.property`.
- `CrateTheorem` and `UnitTheorem`: enforce `.crate` vs `.unit` scope.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Guard `boundary_wellformed_forbids_faults`: a program that immediately hits
`TerminatorKind.unreachable` must refute `WellFormed`. -/
theorem refute_boundary_wellformed_forbids_faults :
    ¬ WellFormed (mkSingleBlockProg 0 [.unit] [] .unreachable) queryEmpty :=
  fun hWf => hWf.2 .undefined (reachesResult_of_execFault (fuel := 1) rfl)

/-- Safe (`isUnsafe = false`) body that executes `TerminatorKind.unreachable`.
-/
noncomputable def safeUnreachableBody : Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{ statements := [], terminator := .unreachable }]
  isUnsafe := false
  identity := "guard_mutation::safe_unreachable"
}

/-- Program wrapping `safeUnreachableBody`. -/
noncomputable def safeUnreachableProg : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [safeUnreachableBody]
}

/-- Guard `boundary_safe_fn_ignores_safety_pre`: a safe (`isUnsafe = false`)
faulty body must still refute `BodyVerified` even when `safetyPre` is `False`.
-/
theorem refute_boundary_safe_fn_ignores_safety_pre :
    ¬ BodyVerified safeUnreachableProg 0 safeUnreachableBody (fun _ => False) :=
  fun hVer =>
    have hWf : WellFormed (entryProgForBody safeUnreachableProg 0)
        { args := [] } :=
      hVer.2.2 [] rfl (fun hFalse => Bool.noConfusion hFalse)
    hWf.2 .undefined (reachesResult_of_execFault (fuel := 1) rfl)

/-- Uninhabited (`MirTy.never`) parameter body with an out-of-bounds
`StorageLive 9` annotation, which fails `BodyStaticAdmitted`. -/
noncomputable def badNeverBody : Body := {
  argumentCount := 1
  locals := [.unit, .never]
  basicBlocks := [{ statements := [.storageLive 9], terminator := .unreachable }]
  isUnsafe := false
  identity := "guard_mutation::bad_never"
}

/-- Program wrapping `badNeverBody`. -/
noncomputable def badNeverProg : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [badNeverBody]
}

/-- Guard `boundary_body_static_admitted`: a body failing `BodyStaticAdmitted`
must refute `BodyVerified` even when `ValidEntryArgs` is empty. -/
theorem refute_boundary_body_static_admitted :
    ¬ BodyVerified badNeverProg 0 badNeverBody (fun _ => True) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Safe zero-argument Profile v2 body that faults with `.unreachable`. -/
noncomputable def bodyUnreachableV2 : Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{ statements := [], terminator := .unreachable }]
  isUnsafe := false
  identity := "guard_mutation::unreachable_v2"
}

/-- Profile v2 program wrapping `bodyUnreachableV2`. -/
noncomputable def progUnreachableV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [bodyUnreachableV2]
}

/-- Reachability of `.fault .undefined` on `progUnreachableV2`. -/
theorem reaches_fault_unreachable_v2 :
    ReachesResultV2 progUnreachableV2 queryEmpty (.fault .undefined) := by
  unfold ReachesResultV2
  change ∃ s : State, ReachesV2 progUnreachableV2 _ s ∧
    StepV2 progUnreachableV2 s (.fault .undefined)
  exact ⟨_, ReachesV2.refl _, ⟨0, rfl, rfl⟩⟩

/-- Guard `boundary_v2_wellformed_forbids_faults`: `WellFormedV2` must be
refuted by a reachable `.fault .undefined`. -/
theorem refute_boundary_v2_wellformed_forbids_faults :
    ¬ WellFormedV2 progUnreachableV2 queryEmpty :=
  fun hWf => hWf.2 .undefined reaches_fault_unreachable_v2

/-- Guard `boundary_v2_safe_fn_ignores_safety_pre`: `BodyVerifiedV2` must reject
a faulting safe function even when `safetyPre := fun _ => False`. -/
theorem refute_boundary_v2_safe_fn_ignores_safety_pre :
    ¬ BodyVerifiedV2 progUnreachableV2 0 bodyUnreachableV2 (fun _ => False) :=
  fun hVer =>
    refute_boundary_v2_wellformed_forbids_faults
      (hVer.2.2 queryEmpty ⟨rfl, rfl, rfl, rfl⟩ (fun h => Bool.noConfusion h))

/-- Uninhabited (`MirTy.never`) parameter Profile v2 body with an out-of-bounds
`StorageLive 9` annotation, failing `BodyStaticAdmittedV2`. -/
noncomputable def badNeverBodyV2 : Body := {
  argumentCount := 1
  locals := [.unit, .never]
  basicBlocks := [{ statements := [.storageLive 9], terminator := .unreachable }]
  isUnsafe := false
  identity := "guard_mutation::bad_never_v2"
}

/-- Profile v2 program wrapping `badNeverBodyV2`. -/
noncomputable def badNeverProgV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [badNeverBodyV2]
}

/-- Guard `boundary_v2_body_static_admitted`: a body failing
`BodyStaticAdmittedV2` must refute `BodyVerifiedV2` even when `ValidEntryArgsV2`
is empty. -/
theorem refute_boundary_v2_body_static_admitted :
    ¬ BodyVerifiedV2 badNeverProgV2 0 badNeverBodyV2 (fun _ => True) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Profile v2 body whose locals mix a shared reference and a raw pointer but
otherwise pass `BodyStaticAdmittedV2`. -/
noncomputable def mixedRefRawBodyV2 : Body := {
  argumentCount := 2
  locals :=
    [.unit, .ref .shared (.int .i8 false), .rawPtr .shared (.int .i8 false)]
  basicBlocks := [{ statements := [], terminator := .return_ }]
  isUnsafe := true
  identity := "guard_mutation::mixed_ref_raw_v2"
}

/-- Profile v2 program wrapping `mixedRefRawBodyV2`. -/
noncomputable def mixedRefRawProgV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [mixedRefRawBodyV2]
}

/-- Guard `boundary_v2_rejects_mixed_refs_and_raw_ptrs`: Profile v2 has no
aliasing model, so a body mixing reference and raw-pointer locals must refute
`BodyVerifiedV2` regardless of its safety precondition. -/
theorem refute_boundary_v2_rejects_mixed_refs_and_raw_ptrs :
    ¬ BodyVerifiedV2 mixedRefRawProgV2 0 mixedRefRawBodyV2 (fun _ => False) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Profile v2 safe body under `--panic abort` that aborts unconditionally via
a failing `.divByZero` assert. -/
noncomputable def abortSafeBodyV2 : Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{
    statements := []
    terminator :=
      .assert (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩) true
        .divByZero 0 .unreachable
  }]
  isUnsafe := false
  identity := "guard_mutation::abort_safe_v2"
}

/-- Profile v2 `--panic abort` program wrapping `abortSafeBodyV2`. -/
noncomputable def abortSafeProgV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  panicStrategy := .abort
  hasLocalPanicHandler := false
  bodies := [abortSafeBodyV2]
}

/-- Guard `boundary_v2_effect_mask_allow_abort_default`: `EffectMaskV2` defaults
`allowAbort` to `false`. -/
theorem refute_boundary_v2_effect_mask_allow_abort_default :
    ({} : EffectMaskV2).allowAbort = false :=
  rfl

/-- Guard `boundary_v2_safe_contract_allow_abort_default`: `SafeContractV2`
defaults `effects.allowAbort` to `false`, rejecting aborting paths even when
`postAbort := True`. -/
theorem refute_boundary_v2_safe_contract_allow_abort_default :
    ¬ BodySatisfiesSafeContractV2 abortSafeProgV2 0 abortSafeBodyV2
      { postAbort := fun _ _ => True } :=
  fun hSat =>
    Bool.noConfusion
      ((hSat.2.2 queryEmpty ⟨rfl, rfl, rfl, rfl⟩ trivial).2
        (.aborted queryEmpty.callerMem) ⟨_, ReachesV2.refl _, ⟨0, rfl, rfl⟩⟩).1

/-- Guard `boundary_v2_safe_contract_post_abort_default`: `SafeContractV2`
defaults `postAbort` to `False`, rejecting aborting paths even when
`allowAbort := true`. -/
theorem refute_boundary_v2_safe_contract_post_abort_default :
    ¬ BodySatisfiesSafeContractV2 abortSafeProgV2 0 abortSafeBodyV2
      { effects := { allowAbort := true } } :=
  fun hSat =>
    ((hSat.2.2 queryEmpty ⟨rfl, rfl, rfl, rfl⟩ trivial).2
      (.aborted queryEmpty.callerMem) ⟨_, ReachesV2.refl _, ⟨0, rfl, rfl⟩⟩).2

/-- Profile v2 body where parameter `_2` (`2 <= argumentCount`) is written by
`.fakeAddressOf` and read by `.ptrMetadata`, which `isFakePtrMetadataLocalV2`
must reject because caller parameters are never synthetic temporaries. -/
noncomputable def fakeMetaArgBodyV2 : Body := {
  argumentCount := 2
  locals := [
    .int .isize false,
    .ref .mut (.slice (.int .i8 false)),
    .rawPtr .shared (.slice (.int .i8 false))
  ]
  basicBlocks := [{
    statements := [
      .assign ⟨2, []⟩ (.fakeAddressOf ⟨1, [.deref]⟩),
      .assign ⟨0, []⟩ (.unaryOp .ptrMetadata (.move ⟨2, []⟩))
    ]
    terminator := .return_
  }]
  isUnsafe := false
  identity := "guard_mutation::fake_meta_arg_v2"
}

/-- Profile v2 program wrapping `fakeMetaArgBodyV2`. -/
noncomputable def fakeMetaArgProgV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [fakeMetaArgBodyV2]
}

/-- Guard `boundary_v2_fake_ptr_metadata_forbids_arg_or_ret`: caller parameters
cannot qualify as `isFakePtrMetadataLocalV2` temporaries. -/
theorem refute_boundary_v2_fake_ptr_metadata_forbids_arg_or_ret :
    ¬ BodyVerifiedV2 fakeMetaArgProgV2 0 fakeMetaArgBodyV2 (fun _ => False) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Profile v2 body with a reference parameter `_1` and an unused non-argument
`*const [u8]` local `_2` (`2 > argumentCount`) without any `.fakeAddressOf`
assignment, which must still be rejected as mixed ref + raw-pointer locals. -/
noncomputable def unusedRawLocalWithRefBodyV2 : Body := {
  argumentCount := 1
  locals := [
    .unit,
    .ref .mut (.slice (.int .i8 false)),
    .rawPtr .shared (.slice (.int .i8 false))
  ]
  basicBlocks := [{ statements := [], terminator := .return_ }]
  isUnsafe := false
  identity := "guard_mutation::unused_raw_with_ref_v2"
}

/-- Profile v2 program wrapping `unusedRawLocalWithRefBodyV2`. -/
noncomputable def unusedRawLocalWithRefProgV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [unusedRawLocalWithRefBodyV2]
}

/-- Guard `boundary_v2_fake_ptr_metadata_requires_fake_assign`: an unused
non-argument `*const` local without `.fakeAddressOf` must not bypass
`bodyMixesRefsAndRawPtrsV2`. -/
theorem refute_boundary_v2_fake_ptr_metadata_requires_fake_assign :
    ¬ BodyVerifiedV2 unusedRawLocalWithRefProgV2 0
      unusedRawLocalWithRefBodyV2 (fun _ => False) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Profile v2 body that assigns `.fakeAddressOf` to `_2` and then dereferences
`*_2` instead of passing `_2` exclusively to `.unaryOp .ptrMetadata`. -/
noncomputable def derefFakeMetaBodyV2 : Body := {
  argumentCount := 1
  locals := [
    .int .i8 false,
    .ref .mut (.int .i8 false),
    .rawPtr .shared (.int .i8 false)
  ]
  basicBlocks := [{
    statements := [
      .assign ⟨2, []⟩ (.fakeAddressOf ⟨1, [.deref]⟩),
      .assign ⟨0, []⟩ (.use (.copy ⟨2, [.deref]⟩))
    ]
    terminator := .return_
  }]
  isUnsafe := false
  identity := "guard_mutation::deref_fake_meta_v2"
}

/-- Profile v2 program wrapping `derefFakeMetaBodyV2`. -/
noncomputable def derefFakeMetaProgV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [derefFakeMetaBodyV2]
}

/-- Guard `boundary_v2_fake_ptr_metadata_forbids_non_metadata_use`: reading or
dereferencing a `.fakeAddressOf` local outside `.unaryOp .ptrMetadata` must
refute `BodyVerifiedV2`. -/
theorem refute_boundary_v2_fake_ptr_metadata_forbids_non_metadata_use :
    ¬ BodyVerifiedV2 derefFakeMetaProgV2 0 derefFakeMetaBodyV2
      (fun _ => False) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Raw-pointer-only Profile v2 body (`tyListHasRefV2 = false`) that assigns
`.fakeAddressOf` to `_2` and copies `_2` into `_0` without `PtrMetadata`-only
discipline. -/
noncomputable def rawOnlyEscapedFakeMetaBodyV2 : Body := {
  argumentCount := 1
  locals := [
    .rawPtr .shared (.int .i8 false),
    .rawPtr .shared (.int .i8 false),
    .rawPtr .shared (.int .i8 false)
  ]
  basicBlocks := [{
    statements := [
      .assign ⟨2, []⟩ (.fakeAddressOf ⟨1, [.deref]⟩),
      .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))
    ]
    terminator := .return_
  }]
  isUnsafe := true
  identity := "guard_mutation::raw_only_escaped_fake_meta_v2"
}

/-- Profile v2 program wrapping `rawOnlyEscapedFakeMetaBodyV2`. -/
noncomputable def rawOnlyEscapedFakeMetaProgV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [rawOnlyEscapedFakeMetaBodyV2]
}

/-- Guard `boundary_v2_body_fake_address_of_valid`: `BodyStaticAdmittedV2` must
reject non-metadata `.fakeAddressOf` uses even in raw-pointer-only bodies. -/
theorem refute_boundary_v2_body_fake_address_of_valid :
    ¬ BodyVerifiedV2 rawOnlyEscapedFakeMetaProgV2 0
      rawOnlyEscapedFakeMetaBodyV2 (fun _ => False) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Profile v2 body where `.fakeAddressOf` references its own local `_2`
(`src.localId == dstId`), which `fakeAddressOfTypesMatchV2` must reject. -/
noncomputable def selfAssignFakeMetaBodyV2 : Body := {
  argumentCount := 1
  locals := [
    .int .isize false,
    .ref .mut (.slice (.int .i8 false)),
    .rawPtr .shared (.slice (.int .i8 false))
  ]
  basicBlocks := [{
    statements := [
      .assign ⟨2, []⟩ (.fakeAddressOf ⟨2, [.deref]⟩),
      .assign ⟨0, []⟩ (.unaryOp .ptrMetadata (.move ⟨2, []⟩))
    ]
    terminator := .return_
  }]
  isUnsafe := false
  identity := "guard_mutation::self_assign_fake_meta_v2"
}

/-- Profile v2 program wrapping `selfAssignFakeMetaBodyV2`. -/
noncomputable def selfAssignFakeMetaProgV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [selfAssignFakeMetaBodyV2]
}

/-- Guard `boundary_v2_fake_ptr_metadata_forbids_self_assign`:
`fakeAddressOfTypesMatchV2` rejects self-referential `.fakeAddressOf (*_lid)`
assignments into `_lid`. -/
theorem refute_boundary_v2_fake_ptr_metadata_forbids_self_assign :
    ¬ BodyVerifiedV2 selfAssignFakeMetaProgV2 0 selfAssignFakeMetaBodyV2
      (fun _ => False) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Profile v2 body with an overflow-pair pointee `(u8, bool)` on
`.fakeAddressOf`, exercising `fakeAddressOfTypesMatchV2`'s `!isOverflowPairTy`
defense-in-depth conjunct directly via `isFakePtrMetadataLocalV2`. -/
noncomputable def overflowPairFakeMetaBodyV2 : Body := {
  argumentCount := 1
  locals := [
    .unit,
    .ref .mut (.tuple [.int .i8 false, .bool]),
    .rawPtr .shared (.tuple [.int .i8 false, .bool])
  ]
  basicBlocks := [{
    statements := [
      .assign ⟨2, []⟩ (.fakeAddressOf ⟨1, [.deref]⟩),
      .assign ⟨0, []⟩ (.unaryOp .ptrMetadata (.move ⟨2, []⟩))
    ]
    terminator := .return_
  }]
  isUnsafe := false
  identity := "guard_mutation::overflow_pair_fake_meta_v2"
}

/-- Guard `boundary_v2_fake_ptr_metadata_forbids_overflow_pair`:
`fakeAddressOfTypesMatchV2` rejects overflow-pair pointees `(int, bool)`. -/
theorem refute_boundary_v2_fake_ptr_metadata_forbids_overflow_pair :
    isFakePtrMetadataLocalV2 overflowPairFakeMetaBodyV2 2 = false :=
  rfl

/-- Profile v2 body where `.fakeAddressOf (*_1)` from `&mut u8` assigns into
a mismatched `*const u16` destination `_2`. -/
noncomputable def mismatchedPointeeFakeMetaBodyV2 : Body := {
  argumentCount := 1
  locals := [
    .unit,
    .ref .mut (.int .i8 false),
    .rawPtr .shared (.int .i16 false)
  ]
  basicBlocks := [{
    statements := [
      .assign ⟨2, []⟩ (.fakeAddressOf ⟨1, [.deref]⟩),
      .assign ⟨0, []⟩ (.unaryOp .ptrMetadata (.move ⟨2, []⟩))
    ]
    terminator := .return_
  }]
  isUnsafe := false
  identity := "guard_mutation::mismatched_pointee_fake_meta_v2"
}

/-- Profile v2 program wrapping `mismatchedPointeeFakeMetaBodyV2`. -/
noncomputable def mismatchedPointeeFakeMetaProgV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [mismatchedPointeeFakeMetaBodyV2]
}

/-- Guard `boundary_v2_fake_ptr_metadata_requires_matching_pointee`:
`fakeAddressOfTypesMatchV2` requires the destination `*const T` pointee type to
match the base place's pointee type. -/
theorem refute_boundary_v2_fake_ptr_metadata_requires_matching_pointee :
    ¬ BodyVerifiedV2 mismatchedPointeeFakeMetaProgV2 0
      mismatchedPointeeFakeMetaBodyV2 (fun _ => False) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Profile v2 body with both an unprojected `.fakeAddressOf` assignment to `_2`
and a projected assignment `(*_2) = .fakeAddressOf (*_1)`, exercising
`stmtRespectsFakePtrMetadataLocalV2`'s `dst.projection.isEmpty` conjunct in
isolation from `bodyFakeAddressOfValidV2`. -/
noncomputable def projectedDstFakeMetaBodyV2 : Body := {
  argumentCount := 1
  locals := [
    .int .isize false,
    .ref .mut (.slice (.int .i8 false)),
    .rawPtr .shared (.slice (.int .i8 false))
  ]
  basicBlocks := [{
    statements := [
      .assign ⟨2, []⟩ (.fakeAddressOf ⟨1, [.deref]⟩),
      .assign ⟨2, [.deref]⟩ (.fakeAddressOf ⟨1, [.deref]⟩),
      .assign ⟨0, []⟩ (.unaryOp .ptrMetadata (.move ⟨2, []⟩))
    ]
    terminator := .return_
  }]
  isUnsafe := false
  identity := "guard_mutation::projected_dst_fake_meta_v2"
}

/-- Guard `boundary_v2_fake_ptr_metadata_forbids_projected_dst`:
`stmtRespectsFakePtrMetadataLocalV2` rejects projected writes through `_lid`,
so `bodyHasRawPtrLocalV2` keeps classifying `_2` as a non-fake raw pointer. -/
theorem refute_boundary_v2_fake_ptr_metadata_forbids_projected_dst :
    isFakePtrMetadataLocalV2 projectedDstFakeMetaBodyV2 2 = false :=
  rfl

/-- Profile v2 body where `.unaryOp .ptrMetadata` reads a projected place
`(*_2)` instead of unprojected `_2`. -/
noncomputable def projectedPtrMetaOpFakeMetaBodyV2 : Body := {
  argumentCount := 1
  locals := [
    .int .isize false,
    .ref .mut (.slice (.int .i8 false)),
    .rawPtr .shared (.slice (.int .i8 false))
  ]
  basicBlocks := [{
    statements := [
      .assign ⟨2, []⟩ (.fakeAddressOf ⟨1, [.deref]⟩),
      .assign ⟨0, []⟩ (.unaryOp .ptrMetadata (.move ⟨2, [.deref]⟩))
    ]
    terminator := .return_
  }]
  isUnsafe := false
  identity := "guard_mutation::projected_ptr_meta_op_fake_meta_v2"
}

/-- Profile v2 program wrapping `projectedPtrMetaOpFakeMetaBodyV2`. -/
noncomputable def projectedPtrMetaOpFakeMetaProgV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [projectedPtrMetaOpFakeMetaBodyV2]
}

/-- Guard `boundary_v2_fake_ptr_metadata_forbids_projected_ptr_meta_operand`:
`stmtRespectsFakePtrMetadataLocalV2` requires `.ptrMetadata` operands reading
a fake-metadata local to have an empty projection. -/
theorem refute_boundary_v2_fake_ptr_metadata_forbids_projected_ptr_meta_operand
    : ¬ BodyVerifiedV2 projectedPtrMetaOpFakeMetaProgV2 0
      projectedPtrMetaOpFakeMetaBodyV2 (fun _ => False) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Profile v2 body where a `.fakeAddressOf` local `_2` escapes through a
`TerminatorKind.coreCall` argument (`ptrAdd`), which `isFakePtrMetadataLocalV2`
must reject via `!terminatorMentionsLocalV2 lid bb.terminator`. -/
noncomputable def terminatorEscapeFakeMetaBodyV2 : Body := {
  argumentCount := 1
  locals := [
    .rawPtr .shared (.int .i8 false),
    .rawPtr .shared (.int .i8 false),
    .rawPtr .shared (.int .i8 false)
  ]
  basicBlocks := [
    {
      statements := [
        .assign ⟨2, []⟩ (.fakeAddressOf ⟨1, [.deref]⟩)
      ]
      terminator :=
        .coreCall (.ptrAdd .shared (.int .i8 false))
          [.copy ⟨2, []⟩, .constant ⟨.int .isize false, .scalar 0⟩]
          ⟨0, []⟩ (some 1) .unreachable
    },
    {
      statements := []
      terminator := .return_
    }
  ]
  isUnsafe := true
  identity := "guard_mutation::terminator_escape_fake_meta_v2"
}

/-- Profile v2 program wrapping `terminatorEscapeFakeMetaBodyV2`. -/
noncomputable def terminatorEscapeFakeMetaProgV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [terminatorEscapeFakeMetaBodyV2]
}

/-- Guard `boundary_v2_fake_ptr_metadata_forbids_terminator_use`:
`isFakePtrMetadataLocalV2` must reject fake-metadata locals referenced by any
terminator (such as `coreCall` arguments or destinations). -/
theorem refute_boundary_v2_fake_ptr_metadata_forbids_terminator_use :
    ¬ BodyVerifiedV2 terminatorEscapeFakeMetaProgV2 0
      terminatorEscapeFakeMetaBodyV2 (fun _ => False) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Anti-overreach canary: a safe `&mut [u8]` body using a metadata-only
`.fakeAddressOf` + `.ptrMetadata` temporary is admitted by
`BodyStaticAdmittedV2` and has `bodyHasRawPtrLocalV2 = false`. -/
noncomputable def validFakeMetaBodyV2 : Body := {
  argumentCount := 1
  locals := [
    .int .isize false,
    .ref .mut (.slice (.int .i8 false)),
    .rawPtr .shared (.slice (.int .i8 false))
  ]
  basicBlocks := [{
    statements := [
      .assign ⟨2, []⟩ (.fakeAddressOf ⟨1, [.deref]⟩),
      .assign ⟨0, []⟩ (.unaryOp .ptrMetadata (.move ⟨2, []⟩))
    ]
    terminator := .return_
  }]
  isUnsafe := false
  identity := "guard_mutation::valid_fake_meta_v2"
}

/-- Profile v2 program wrapping `validFakeMetaBodyV2`. -/
noncomputable def validFakeMetaProgV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [validFakeMetaBodyV2]
}

theorem positive_boundary_v2_admits_valid_fake_ptr_metadata :
    BodyStaticAdmittedV2 validFakeMetaProgV2 validFakeMetaBodyV2 = true ∧
      bodyHasRawPtrLocalV2 validFakeMetaBodyV2 = false :=
  ⟨rfl, rfl⟩

/-- Guard `boundary_satisfies_post_requires_wf`: a faulty program refutes
`SatisfiesPost` even when `post` is `True`. -/
theorem refute_boundary_satisfies_post_requires_wf :
    ¬ SatisfiesPost safeUnreachableProg queryEmpty (fun _ => True) :=
  fun hSat =>
    hSat.1.2 .undefined (reachesResult_of_execFault (fuel := 1) rfl)

/-- Guard `boundary_satisfies_post_enforces_post`: a well-formed program
returning `42u32` refutes `SatisfiesPost` for `out = returned(0u32)`. -/
theorem refute_boundary_satisfies_post_enforces_post :
    ¬ SatisfiesPost (mkConstRetProg u32Ty 42) queryEmpty
        (fun out => out = .returned ⟨u32Val 0, ⟨[]⟩⟩) :=
  fun hSat =>
    have hEq : TerminalOut.returned ⟨u32Val 42, ⟨[]⟩⟩ =
        TerminalOut.returned ⟨u32Val 0, ⟨[]⟩⟩ :=
      hSat.2 _ (behavior_of_execDone (fuel := 2) rfl)
    by cases hEq

/-- Valid uninhabited (`MirTy.never`) parameter body used to isolate individual
`BodyStaticAdmitted` conjuncts. -/
noncomputable def okNeverBody : Body := {
  argumentCount := 1
  locals := [.unit, .never]
  basicBlocks := [{ statements := [], terminator := .unreachable }]
  isUnsafe := false
  identity := "guard_mutation::ok_never"
}

/-- Helper wrapping a single body into a `Program` with configurable metadata.
-/
noncomputable def mkBoundaryProg (body : Body) (ptrBits : Nat := 64)
    (profVer : Nat := 1) (sc : VerificationScope := .unit) : Program := {
  scope := sc
  pointerWidthBits := ptrBits
  mirProfileVersion := profVer
  bodies := [body]
}

/-- Guard `boundary_static_admitted_pointer_width`: `BodyStaticAdmitted`
rejects 32-bit `pointerWidthBits` even on an uninhabited `never`-arg body. -/
theorem refute_boundary_static_admitted_pointer_width :
    ¬ BodyVerified (mkBoundaryProg okNeverBody (ptrBits := 32)) 0 okNeverBody
        (fun _ => True) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Guard `boundary_static_admitted_profile_v1`: `BodyStaticAdmitted` rejects
`mirProfileVersion = 2` even on an uninhabited `never`-arg body. -/
theorem refute_boundary_static_admitted_profile_v1 :
    ¬ BodyVerified (mkBoundaryProg okNeverBody (profVer := 2)) 0 okNeverBody
        (fun _ => True) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Uninhabited `never`-arg body with an empty `identity := ""`. -/
noncomputable def emptyIdNeverBody : Body :=
  { okNeverBody with identity := "" }

/-- Guard `boundary_static_admitted_nonempty_identity`: `BodyStaticAdmitted`
rejects empty `body.identity` even on an uninhabited `never`-arg body. -/
theorem refute_boundary_static_admitted_nonempty_identity :
    ¬ BodyVerified (mkBoundaryProg emptyIdNeverBody) 0 emptyIdNeverBody
        (fun _ => True) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Uninhabited `never`-arg body with zero basic blocks. -/
noncomputable def emptyBlocksNeverBody : Body :=
  { okNeverBody with basicBlocks := [] }

/-- Guard `boundary_static_admitted_nonempty_blocks`: `BodyStaticAdmitted`
rejects empty `basicBlocks` even on an uninhabited `never`-arg body. -/
theorem refute_boundary_static_admitted_nonempty_blocks :
    ¬ BodyVerified (mkBoundaryProg emptyBlocksNeverBody) 0 emptyBlocksNeverBody
        (fun _ => True) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Uninhabited `never`-arg body with `argumentCount = 2 ≥ locals.length`. -/
noncomputable def badArgCountNeverBody : Body :=
  { okNeverBody with argumentCount := 2 }

/-- Guard `boundary_static_admitted_arg_count_bound`: `BodyStaticAdmitted`
rejects `argumentCount ≥ locals.length` on an uninhabited `never`-arg body. -/
theorem refute_boundary_static_admitted_arg_count_bound :
    ¬ BodyVerified (mkBoundaryProg badArgCountNeverBody) 0 badArgCountNeverBody
        (fun _ => True) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Guard `boundary_static_admitted_storage_bounds`: `BodyStaticAdmitted`
rejects out-of-bounds `StorageLive` on an uninhabited `never`-arg body. -/
theorem refute_boundary_static_admitted_storage_bounds :
    ¬ BodyVerified badNeverProg 0 badNeverBody (fun _ => True) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Uninhabited `never`-arg body with an ill-typed `Discriminant` assignment.
-/
noncomputable def badDiscrNeverBody : Body := {
  argumentCount := 1
  locals := [u8Ty, .never, .ordering]
  basicBlocks := [{
    statements := [.assign ⟨0, []⟩ (.discriminant ⟨2, []⟩)]
    terminator := .unreachable
  }]
  isUnsafe := false
  identity := "guard_mutation::bad_discr_never"
}

/-- Guard `boundary_static_admitted_discr_types`: `BodyStaticAdmitted` rejects
ill-typed `Discriminant` destinations on an uninhabited `never`-arg body. -/
theorem refute_boundary_static_admitted_discr_types :
    ¬ BodyVerified (mkBoundaryProg badDiscrNeverBody) 0 badDiscrNeverBody
        (fun _ => True) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Uninhabited `never`-arg body with an ill-typed `Cast(IntToInt)` assignment.
-/
noncomputable def badCastNeverBody : Body := {
  argumentCount := 1
  locals := [u8Ty, .never, u32Ty]
  basicBlocks := [{
    statements := [.assign ⟨0, []⟩ (.cast .intToInt (.copy ⟨2, []⟩) u32Ty)]
    terminator := .unreachable
  }]
  isUnsafe := false
  identity := "guard_mutation::bad_cast_never"
}

/-- Guard `boundary_static_admitted_cast_types`: `BodyStaticAdmitted` rejects
ill-typed `Cast` destinations on an uninhabited `never`-arg body. -/
theorem refute_boundary_static_admitted_cast_types :
    ¬ BodyVerified (mkBoundaryProg badCastNeverBody) 0 badCastNeverBody
        (fun _ => True) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Uninhabited `never`-arg body carrying an unsupported `.ref` local. -/
noncomputable def badLocalTyNeverBody : Body := {
  argumentCount := 1
  locals := [.unit, .never, .ref .shared u32Ty]
  basicBlocks := [{ statements := [], terminator := .unreachable }]
  isUnsafe := false
  identity := "guard_mutation::bad_local_never"
}

/-- Guard `boundary_static_admitted_local_types`: `BodyStaticAdmitted` rejects
unsupported local types on an uninhabited `never`-arg body. -/
theorem refute_boundary_static_admitted_local_types :
    ¬ BodyVerified (mkBoundaryProg badLocalTyNeverBody) 0 badLocalTyNeverBody
        (fun _ => True) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Guard `boundary_body_verified_binds_body`: `BodyVerified` refuses a
mismatched `body` stub (`okNeverBody`) that disagrees with `p.bodies[0]`
(`safeUnreachableBody`). -/
theorem refute_boundary_body_verified_binds_body :
    ¬ BodyVerified safeUnreachableProg 0 okNeverBody (fun _ => True) :=
  fun hVer => by cases hVer.1

/-- Minimal valid 0-arg unit-returning body with identity `ident`. -/
noncomputable def mkOkUnitBody (ident : String) : Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{ statements := [], terminator := .return_ }]
  isUnsafe := false
  identity := ident
}

/-- Default trivial `Specs`. -/
noncomputable def trivialSpecs : Specs :=
  ⟨fun _ _ => True, fun _ => True⟩

/-- Program whose `entryDefId` (`1`) is out of bounds for 1 body. -/
noncomputable def badEntryDefIdProg : Program := {
  scope := .unit
  entryDefId := 1
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [mkOkUnitBody "guard_mutation::ok_only"]
}

/-- Guard `boundary_program_verified_entry_in_bounds`: `ProgramVerified`
rejects out-of-bounds `entryDefId`. -/
theorem refute_boundary_program_verified_entry_in_bounds :
    ¬ ProgramVerified badEntryDefIdProg trivialSpecs :=
  fun hVer => Bool.noConfusion hVer.2.2.2.1

/-- Program with two valid bodies sharing the same `identity`. -/
noncomputable def dupIdProg : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    mkOkUnitBody "guard_mutation::dup",
    mkOkUnitBody "guard_mutation::dup"
  ]
}

/-- Guard `boundary_program_verified_unique_identities`: `ProgramVerified`
rejects programs containing duplicate body identities. -/
theorem refute_boundary_program_verified_unique_identities :
    ¬ ProgramVerified dupIdProg trivialSpecs :=
  fun hVer => Bool.noConfusion hVer.2.2.2.2.1

/-- Two-body program where body `0` is valid and body `1` faults with
`.unreachable`. -/
noncomputable def twoBodySecondBadProg : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    mkOkUnitBody "guard_mutation::ok_0",
    safeUnreachableBody
  ]
}

/-- Guard `boundary_program_verified_checks_all_bodies`: `ProgramVerified`
verifies every body in `p.bodies`, not only `entryDefId = 0`. -/
theorem refute_boundary_program_verified_checks_all_bodies :
    ¬ ProgramVerified twoBodySecondBadProg trivialSpecs :=
  fun hVer =>
    have hBody1 : BodyVerified twoBodySecondBadProg 1 safeUnreachableBody
        (fun _ => True) :=
      hVer.2.2.2.2.2.1 1 safeUnreachableBody rfl
    have hWf : WellFormed (entryProgForBody twoBodySecondBadProg 1)
        { args := [] } :=
      hBody1.2.2 [] rfl (fun _ => trivial)
    hWf.2 .undefined (reachesResult_of_execFault (fuel := 1) rfl)

/-- Valid 1-body unit-scoped program. -/
noncomputable def okUnitScopeProg : Program :=
  mkBoundaryProg (mkOkUnitBody "guard_mutation::ok_unit") (sc := .unit)

/-- Valid 1-body crate-scoped program. -/
noncomputable def okCrateScopeProg : Program :=
  mkBoundaryProg (mkOkUnitBody "guard_mutation::ok_crate") (sc := .crate)

/-- Guard `boundary_program_verified_checks_property`: `ProgramVerified`
enforces `specs.property p`. -/
theorem refute_boundary_program_verified_checks_property :
    ¬ ProgramVerified okUnitScopeProg ⟨fun _ _ => True, fun _ => False⟩ :=
  fun hVer => hVer.2.2.2.2.2.2

/-- Guard `boundary_crate_theorem_requires_crate_scope`: `CrateTheorem` rejects
a `.unit`-scoped capture. -/
theorem refute_boundary_crate_theorem_requires_crate_scope :
    ¬ CrateTheorem ⟨okUnitScopeProg, trivialSpecs⟩ :=
  fun hCrate => by cases hCrate.1

/-- Guard `boundary_unit_theorem_requires_unit_scope`: `UnitTheorem` rejects a
`.crate`-scoped capture. -/
theorem refute_boundary_unit_theorem_requires_unit_scope :
    ¬ UnitTheorem ⟨okCrateScopeProg, trivialSpecs⟩ :=
  fun hUnit => by cases hUnit.1

end GuardMutation
