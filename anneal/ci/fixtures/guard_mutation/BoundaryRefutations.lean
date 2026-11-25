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

/-- Valid safe body returning `()` with a non-empty `identity`. -/
noncomputable def okUnitBody (ident : String := "guard_mutation::ok_unit") :
    Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{ statements := [], terminator := .return_ }]
  isUnsafe := false
  identity := ident
}

/-- Dummy uninhabited-parameter body whose `ValidEntryArgs` is empty while
passing `BodyStaticAdmitted`. -/
noncomputable def goodNeverStubBody : Body := {
  argumentCount := 1
  locals := [.unit, .never]
  basicBlocks := [{ statements := [], terminator := .return_ }]
  isUnsafe := false
  identity := "guard_mutation::never_stub"
}

/-- Guard `boundary_body_verified_binds_def_id`: `BodyVerified` binds `body`
to `p.bodies[defId]` so an unrelated `.never`-parameter stub cannot verify
`safeUnreachableBody`. -/
theorem refute_boundary_body_verified_binds_def_id :
    ¬ BodyVerified safeUnreachableProg 0 goodNeverStubBody (fun _ => True) :=
  fun hVer =>
    Nat.noConfusion (congrArg Body.argumentCount (Option.some.inj hVer.1))

/-- Program wrapping `okUnitBody` with an empty `identity := ""`. -/
noncomputable def emptyIdentProg : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [okUnitBody ""]
}

/-- Guard `boundary_admitted_nonempty_identity`: `BodyStaticAdmitted` rejects
a body whose `identity` string is empty. -/
theorem refute_boundary_admitted_nonempty_identity :
    ¬ BodyVerified emptyIdentProg 0 (okUnitBody "") (fun _ => True) :=
  fun hVer => Bool.noConfusion hVer.2.1

/-- Program with a non-empty valid body list but out-of-bounds `entryDefId`.
-/
noncomputable def badEntryDefProg : Program := {
  scope := .unit
  entryDefId := 1
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [okUnitBody "guard_mutation::entry_oob"]
}

/-- Guard `boundary_program_entry_def_in_bounds`: `ProgramVerified` requires
`entryDefId < p.bodies.length`. -/
theorem refute_boundary_program_entry_def_in_bounds :
    ¬ ProgramVerified badEntryDefProg {} :=
  fun hVer => Bool.noConfusion hVer.2.2.2.1

/-- Program with two distinct bodies sharing the same `identity`. -/
noncomputable def dupIdentityProg : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [okUnitBody "guard_mutation::dup", okUnitBody "guard_mutation::dup"]
}

/-- Guard `boundary_unique_body_identities`: `ProgramVerified` enforces
pairwise-distinct body identities so `Specs.safety` cannot collide. -/
theorem refute_boundary_unique_body_identities :
    ¬ ProgramVerified dupIdentityProg {} :=
  fun hVer => Bool.noConfusion hVer.2.2.2.2.1

/-- Guard `boundary_crate_theorem_scope`: `CrateTheorem` rejects a program
whose verification scope is `.unit` rather than `.crate`. -/
theorem refute_boundary_crate_theorem_scope :
    ¬ CrateTheorem {
      program := {
        scope := .unit
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [okUnitBody "guard_mutation::unit_scope"]
      }
      specs := {}
    } :=
  fun h => VerificationScope.noConfusion h.1

end GuardMutation
