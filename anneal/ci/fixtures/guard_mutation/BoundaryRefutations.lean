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
  targetEndian := .little
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
  targetEndian := .little
  mirProfileVersion := 1
  bodies := [badNeverBody]
}

/-- Guard `boundary_body_static_admitted`: a body failing `BodyStaticAdmitted`
must refute `BodyVerified` even when `ValidEntryArgs` is empty. -/
theorem refute_boundary_body_static_admitted :
    ¬ BodyVerified badNeverProg 0 badNeverBody (fun _ => True) :=
  fun hVer => Bool.noConfusion hVer.2.1

end GuardMutation
