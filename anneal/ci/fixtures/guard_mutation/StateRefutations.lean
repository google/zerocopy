-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import GuardRefuteWf

/-!
# Negative Refutations for `Trusted.MirSemantics.State` Guards

Exercises every entry precondition and storage-liveness guard in
`Trusted/MirSemantics/State.lean`:

- `initState`: 64-bit `pointerWidthBits`, `mirProfileVersion = 1`, empty
  `callerMem`, non-empty `basicBlocks`, `argumentCount < locals.length`,
  `storageAnnotationsInBounds`, `discriminantTypesValid` (fieldless enum and
  `Ordering`), `castTypesValid`, `isSupportedScalarOrUnitTy`, and
  `checkArgsMatch`.
- `initLocalsLoop`: non-argument locals with any `StorageLive`/`StorageDead`
  annotation start `.dead` rather than live.

Static-admission witnesses place the malformed statement in an unreachable
basic block (`bb1`) while `bb0` returns cleanly, guaranteeing that `initState`
itself—not later execution—is the sole guard rejecting the program.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Minimal valid unit-returning program with a custom `pointerWidthBits` and
`mirProfileVersion`. -/
noncomputable def mkMetaProg (ptrBits profVer : Nat) : Program where
  scope := .unit
  pointerWidthBits := ptrBits
  mirProfileVersion := profVer
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [{ statements := [], terminator := .return_ }]
  }]

/-- Guard `state_init_pointer_width_64`: `initState` rejects 32-bit target
programs with `.unsupported`. -/
theorem refute_state_init_pointer_width_64 :
    ReachesResult (mkMetaProg 32 1) queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed (mkMetaProg 32 1) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `state_init_mir_profile_v1`: `initState` rejects non-v1 MIR profile
programs with `.unsupported`. -/
theorem refute_state_init_mir_profile_v1 :
    ReachesResult (mkMetaProg 64 2) queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed (mkMetaProg 64 2) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Query carrying a non-empty `callerMem` allocation list. -/
noncomputable def queryNonEmptyCallerMem : Query := {
  args := []
  callerMem := ⟨[{
    allocId := 1
    alignLog2 := 0
    mutability := .mut
    bytes := []
    live := true
  }]⟩
}

/-- Guard `state_init_empty_caller_mem`: `initState` rejects queries with
non-empty `callerMem` with `.unsupported`. -/
theorem refute_state_init_empty_caller_mem :
    ReachesResult (mkMetaProg 64 1) queryNonEmptyCallerMem
      (.fault .unsupported) ∧
    ¬ WellFormed (mkMetaProg 64 1) queryNonEmptyCallerMem :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program whose entry body has zero basic blocks. -/
noncomputable def progEmptyBasicBlocks : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    basicBlocks := []
  }]

/-- Guard `state_init_nonempty_blocks`: `initState` itself rejects an entry
body with no basic blocks with `.error .unsupported`. -/
theorem refute_state_init_nonempty_blocks :
    initState progEmptyBasicBlocks queryEmpty = .error .unsupported :=
  rfl

/-- Program whose `argumentCount` equals `locals.length` (missing parameter
slot). -/
noncomputable def progArgCountOutOfBounds : Program :=
  mkSingleBlockProg 1 [.unit] [] .return_

/-- Guard `state_init_arg_count_lt_locals`: `initState` rejects
`argumentCount ≥ locals.length` with `.unsupported`. -/
theorem refute_state_init_arg_count_lt_locals :
    ReachesResult progArgCountOutOfBounds queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed progArgCountOutOfBounds queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program with clean `bb0` return and an out-of-bounds `StorageLive 9` in
unreachable `bb1`. -/
noncomputable def progUnreachableOobStorageLive : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [
      { statements := [], terminator := .return_ },
      { statements := [.storageLive 9], terminator := .return_ }
    ]
  }]

/-- Guard `state_init_storage_annotations_in_bounds`: `initState` rejects
out-of-bounds `StorageLive` annotations even in unreachable blocks. -/
theorem refute_state_init_storage_annotations_in_bounds :
    ReachesResult progUnreachableOobStorageLive queryEmpty
      (.fault .unsupported) ∧
    ¬ WellFormed progUnreachableOobStorageLive queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program with clean `bb0` return and an out-of-bounds `StorageDead 9` in
unreachable `bb1`. -/
noncomputable def progUnreachableOobStorageDead : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [
      { statements := [], terminator := .return_ },
      { statements := [.storageDead 9], terminator := .return_ }
    ]
  }]

/-- Guard `state_storage_oob_marker_check`: `storageAnnotationsInBounds`
rejects out-of-bounds `StorageLive`/`StorageDead` markers. -/
theorem refute_state_storage_oob_marker_check :
    ReachesResult progUnreachableOobStorageDead queryEmpty
      (.fault .unsupported) ∧
    ¬ WellFormed progUnreachableOobStorageDead queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program with clean `bb0` return and an ill-typed enum `Discriminant`
destination (`i8` instead of `u8`) in unreachable `bb1`. -/
noncomputable def progUnreachableBadEnumDiscr : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [i8Ty, .enum reprU8EnumTy]
    basicBlocks := [
      { statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨i8Ty, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .return_ },
      { statements := [.assign ⟨0, []⟩ (.discriminant ⟨1, []⟩)]
        terminator := .return_ }
    ]
  }]

/-- Guard `state_init_discriminant_types_valid`: `initState` rejects ill-typed
fieldless-enum `Discriminant` destinations even in unreachable blocks. -/
theorem refute_state_init_discriminant_types_valid :
    ReachesResult progUnreachableBadEnumDiscr queryEmpty
      (.fault .unsupported) ∧
    ¬ WellFormed progUnreachableBadEnumDiscr queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program with clean `bb0` return and an ill-typed `Ordering` `Discriminant`
destination (`u8` instead of `i8`) in unreachable `bb1`. -/
noncomputable def progUnreachableBadOrderingDiscr : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u8Ty, .ordering]
    basicBlocks := [
      { statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .return_ },
      { statements := [.assign ⟨0, []⟩ (.discriminant ⟨1, []⟩)]
        terminator := .return_ }
    ]
  }]

/-- Guard `state_discr_ordering_type_check`: `discriminantTypesValid` rejects
ill-typed `Ordering` `Discriminant` destinations (`u8` vs `i8`). -/
theorem refute_state_discr_ordering_type_check :
    ReachesResult progUnreachableBadOrderingDiscr queryEmpty
      (.fault .unsupported) ∧
    ¬ WellFormed progUnreachableBadOrderingDiscr queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program with clean `bb0` return and an ill-typed `Cast(IntToInt)`
destination (`u8` destination with `u32` cast target) in unreachable `bb1`. -/
noncomputable def progUnreachableBadCast : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u8Ty, u32Ty]
    basicBlocks := [
      { statements := [
          .assign ⟨0, []⟩ (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .return_ },
      { statements := [.assign ⟨0, []⟩ (.cast .intToInt (.copy ⟨1, []⟩) u32Ty)]
        terminator := .return_ }
    ]
  }]

/-- Guard `state_init_cast_types_valid`: `initState` rejects ill-typed
`Cast(IntToInt)` destinations even in unreachable blocks. -/
theorem refute_state_init_cast_types_valid :
    ReachesResult progUnreachableBadCast queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed progUnreachableBadCast queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program with an unused `.ref` local and clean `()` return. -/
noncomputable def progUnsupportedLocalTy : Program :=
  mkSingleBlockProg 0 [.unit, .ref .shared u32Ty] [] .return_

/-- Guard `state_init_supported_local_types`: `initState` rejects bodies with
unsupported local types even when unused. -/
theorem refute_state_init_supported_local_types :
    ReachesResult progUnsupportedLocalTy queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed progUnsupportedLocalTy queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- 1-arg `u32` program ignoring its argument and returning `()`. -/
noncomputable def progIgnoreU32Arg : Program :=
  mkSingleBlockProg 1 [.unit, u32Ty] [] .return_

/-- Guard `state_init_args_match_param_tys`: `initState` rejects a query whose
argument type (`bool`) disagrees with the parameter type (`u32`). -/
theorem refute_state_init_args_match_param_tys :
    ReachesResult progIgnoreU32Arg { args := [.bool true] }
      (.fault .unsupported) ∧
    ¬ WellFormed progIgnoreU32Arg { args := [.bool true] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program reading `.unit` local `_1` before its `StorageLive 1` statement.
Because `liveUninitSlot .unit` is already inhabited, only starting `_1` as
`.dead` causes the pre-`StorageLive` read to fault with `.undefined`. -/
noncomputable def progReadBeforeStorageLive : Program :=
  mkSingleBlockProg 0 [.unit, .unit]
    [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩)), .storageLive 1]

/-- Guard `state_init_annotated_local_starts_dead`: a non-argument local with a
`StorageLive` annotation starts `.dead`, so reading it before `StorageLive`
faults with `.undefined`. -/
theorem refute_state_init_annotated_local_starts_dead :
    ReachesResult progReadBeforeStorageLive queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progReadBeforeStorageLive queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

end GuardMutation
