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

Exercises the top-level verification-judgment guards in
`Trusted/MirSemantics/Boundary.lean`:

1. `WellFormed` forbids reachable faults (disabling the fault-forbidding
   conjunct must break `¬ WellFormed`).
2. `BodyVerified` ignores `safetyPre` for safe functions (`isUnsafe = false`),
   preventing a `False` safety precondition from vacuously verifying an unsound
   safe function.
3. `BodyVerified` requires `BodyStaticAdmitted` unconditionally, even for
   functions with uninhabited (`MirTy.never`) parameters.
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
    (hVer.2.2 [] rfl (fun hFalse => Bool.noConfusion hFalse)).2 .undefined
      (reachesResult_of_execFault (fuel := 1) rfl)

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

end GuardMutation
