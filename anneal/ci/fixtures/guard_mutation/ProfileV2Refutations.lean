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
import PositiveSanity

/-!
# Additional Profile v2 Refutations for `Bytes`, `State`, and `Step`

Closes high-consequence Profile v2 UB guard blind spots across
`Trusted/MirSemantics/{Bytes,State,Step}.lean`:
- Silent Lean `Nat`-subtraction saturation UB (`usize::unchecked_sub` underflow
  and negative `evalPtrOffsetV2` underflow before allocation byte `0`),
- Return-time and entry-time mutable-reference aliasing (`spansPairwiseDisjoint`
  and `spanDisjoint` `&mut`/`&mut` + `&mut`/`&` exclusion) and return-time
  reference validity (`refsValidInMem`),
- Negative `evalPtrOffsetV2` guards (starting out-of-bounds, provenance-free
  pointer, and dead allocation),
- Thin-reference `&T` / `&mut T` validity (`refValidInMem`: null ZST, `&mut`
  over `.shared`, and uninitialized pointee bytes),
- `UseRetag` reference re-validation and provenance-free non-ZST dereference
  reads and writes.
Shared allocation and value helpers, and the anti-overreach positive canaries
for these guards, live in `PositiveSanity.lean`, which the runner compiles and
requires to pass on every mutant before this module.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Live immutable (`.shared`) 4-byte allocation holding initialized bytes. -/
noncomputable def v2SharedInit4Alloc : Allocation :=
  { v2MutInit4Alloc with mutability := .shared }

/-- Live mutable 1-byte allocation holding an uninitialized byte. -/
noncomputable def v2MutUninit1Alloc : Allocation := {
  allocId := 1
  alignLog2 := 0
  mutability := .mut
  bytes := [.uninit]
  live := true
}

/-- Live mutable 1-byte allocation holding invalid `bool` byte `2`. -/
noncomputable def v2InvalidBoolAlloc : Allocation := {
  allocId := 1
  alignLog2 := 0
  mutability := .mut
  bytes := [.init 2 none]
  live := true
}

/-- Deallocated (`live = false`) 4-byte allocation with id `1`. -/
noncomputable def v2DeadAlloc : Allocation :=
  { v2MutInit4Alloc with live := false }

-- ---------------------------------------------------------------------------
-- Trusted/MirSemantics/Bytes.lean Profile v2 guards
-- ---------------------------------------------------------------------------

/-- Guard `bytes_v2_span_disjoint_overlap`: overlapping mutable spans fail
`spansPairwiseDisjoint`. -/
theorem refute_bytes_v2_span_disjoint_overlap :
    spansPairwiseDisjoint [(true, 1, 0, 2), (true, 1, 1, 2)] = false :=
  rfl

/-- Guard `bytes_v2_span_disjoint_mut_vs_shared`: a mutable span overlapping a
shared span in the same allocation fails `spansPairwiseDisjoint` (enforcing
`!(m1 || m2)`, not `!(m1 && m2)`). -/
theorem refute_bytes_v2_span_disjoint_mut_vs_shared :
    spansPairwiseDisjoint [(true, 1, 0, 2), (false, 1, 1, 2)] = false :=
  rfl

/-- Guard `bytes_v2_ref_valid_null_zst`: a provenance-free null thin reference
`&()` faults with `.undefined` even though `()` is zero-sized. -/
theorem refute_bytes_v2_ref_valid_null_zst :
    refValidInMem MemoryState.empty .shared .unit
      (.ptr ⟨none, 0, .isize⟩) = .error .undefined :=
  rfl

/-- Guard `bytes_v2_ref_valid_readonly_mut`: a thin `&mut u8` pointing into a
`.shared` allocation faults with `.undefined`. -/
theorem refute_bytes_v2_ref_valid_readonly_mut :
    refValidInMem (v2MemOf v2SharedInit4Alloc) .mut u8Ty
      (.ptr ⟨some 1, 0, .isize⟩) = .error .undefined :=
  rfl

/-- Guard `bytes_v2_ref_valid_uninit_pointee`: a thin `&u8` pointing to an
uninitialized byte faults with `.undefined`. -/
theorem refute_bytes_v2_ref_valid_uninit_pointee :
    refValidInMem (v2MemOf v2MutUninit1Alloc) .shared u8Ty
      (.ptr ⟨some 1, 0, .isize⟩) = .error .undefined :=
  rfl

-- ---------------------------------------------------------------------------
-- Trusted/MirSemantics/State.lean Profile v2 guards
-- ---------------------------------------------------------------------------

/-- Minimal Profile v2 program taking two `&mut u8` arguments and returning
`()`. -/
noncomputable def progTwoMutRefsV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [{
    argumentCount := 2
    locals := [.unit, .ref .mut u8Ty, .ref .mut u8Ty]
    basicBlocks := [{ statements := [], terminator := .return_ }]
    isUnsafe := false
    identity := "guard_mutation::two_mut_refs_v2"
  }]
}

/-- Minimal Profile v2 program taking one `&u8` argument and returning `()`. -/
noncomputable def progOneRefV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [{
    argumentCount := 1
    locals := [.unit, .ref .shared u8Ty]
    basicBlocks := [{ statements := [], terminator := .return_ }]
    isUnsafe := false
    identity := "guard_mutation::one_ref_v2"
  }]
}

/-- Guard `state_v2_init_invalid_entry_ref`: `initStateV2` rejects an entry
reference pointing to uninitialized memory with `.error .undefined`. -/
theorem refute_state_v2_init_invalid_entry_ref :
    (match initStateV2 progOneRefV2
        { args := [.ptr ⟨some 1, 0, .isize⟩],
          callerMem := ⟨[v2MutUninit1Alloc]⟩ } with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `state_v2_init_aliased_entry_refs`: `initStateV2` rejects two
overlapping `&mut u8` entry arguments with `.error .undefined`. -/
theorem refute_state_v2_init_aliased_entry_refs :
    (match initStateV2 progTwoMutRefsV2
        { args := [.ptr ⟨some 1, 0, .isize⟩, .ptr ⟨some 1, 0, .isize⟩],
          callerMem := ⟨[v2MutInit4Alloc]⟩ } with
     | .error .undefined => True
     | _ => False) :=
  trivial

-- ---------------------------------------------------------------------------
-- Trusted/MirSemantics/Step.lean Profile v2 guards
-- ---------------------------------------------------------------------------

/-- Guard `step_v2_usize_unchecked_sub_underflow`: `usize::unchecked_sub(0, 1)`
faults with `.undefined` instead of silently saturating `0 - 1 = 0`. -/
theorem refute_step_v2_usize_unchecked_sub_underflow :
    execCoreCallOp MemoryState.empty .usizeUncheckedSub
      [(.int .isize false, v2UsizeVal 0), (.int .isize false, v2UsizeVal 1)]
      (.int .isize false) = .error .undefined :=
  rfl

/-- Guard `step_v2_ptr_offset_neg_underflow`: negative `evalPtrOffsetV2`
stepping before byte `0` of a live allocation (`offset = 1`, `count = -2`)
faults with `.undefined` instead of silently saturating `1 - 2 = 0`. -/
theorem refute_step_v2_ptr_offset_neg_underflow :
    evalPtrOffsetV2 (v2MemOf v2MutInit4Alloc) 1 ⟨some 1, 1, .isize⟩
      (v2IsizeBits (Nat.pow 2 64 - 2)) = .error .undefined :=
  rfl

/-- Guard `step_v2_ptr_offset_neg_start_oob`: negative `evalPtrOffsetV2`
starting past the end of a live 4-byte allocation (`offset = 6`, `count = -1`)
faults with `.undefined` even though `delta <= offset`. -/
theorem refute_step_v2_ptr_offset_neg_start_oob :
    evalPtrOffsetV2 (v2MemOf v2MutInit4Alloc) 1 ⟨some 1, 6, .isize⟩
      (v2IsizeBits (Nat.pow 2 64 - 1)) = .error .undefined :=
  rfl

/-- Guard `step_v2_ptr_offset_neg_null`: negative `evalPtrOffsetV2` on a
provenance-free pointer faults with `.undefined`. -/
theorem refute_step_v2_ptr_offset_neg_null :
    evalPtrOffsetV2 MemoryState.empty 1 ⟨none, 8, .isize⟩
      (v2IsizeBits (Nat.pow 2 64 - 1)) = .error .undefined :=
  rfl

/-- Guard `step_v2_ptr_offset_neg_dead_alloc`: negative `evalPtrOffsetV2` on a
deallocated (`live = false`) allocation faults with `.undefined`. -/
theorem refute_step_v2_ptr_offset_neg_dead_alloc :
    evalPtrOffsetV2 (v2MemOf v2DeadAlloc) 1 ⟨some 1, 2, .isize⟩
      (v2IsizeBits (Nat.pow 2 64 - 1)) = .error .undefined :=
  rfl

/-- Guard `step_v2_return_aliased_mut_refs`: returning a pair of overlapping
`&mut [u8]` slices into the same live caller allocation faults with
`.undefined`. -/
theorem refute_step_v2_return_aliased_mut_refs :
    (match evalTerminatorV2 bodyReturnAliasedMutSlices
        { statements := [], terminator := .return_ }
        { defId := 0, blockIdx := 0, stmtIdx := 0,
          locals := [.immediate (some (.tuple [
            .slicePtr ⟨some 1, 0, .isize⟩ 3,
            .slicePtr ⟨some 1, 2, .isize⟩ 2]))] }
        (v2MemOf v2MutInit4Alloc)
        ⟨[v2MutInit4Alloc]⟩ with
     | .fault .undefined => True
     | _ => False) :=
  trivial

/-- Body whose return local `_0` has type `&bool`. -/
noncomputable def bodyReturnBoolRef : Body := {
  argumentCount := 0
  locals := [.ref .shared .bool]
  basicBlocks := [{ statements := [], terminator := .return_ }]
}

/-- Guard `step_v2_return_invalid_ref`: returning a `&bool` into a live caller
allocation holding invalid byte `2` faults with `.undefined`. -/
theorem refute_step_v2_return_invalid_ref :
    (match evalTerminatorV2 bodyReturnBoolRef
        { statements := [], terminator := .return_ }
        { defId := 0, blockIdx := 0, stmtIdx := 0,
          locals := [.immediate (some (.ptr ⟨some 1, 0, .isize⟩))] }
        (v2MemOf v2InvalidBoolAlloc)
        ⟨[v2InvalidBoolAlloc]⟩ with
     | .fault .undefined => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_use_retag_invalid_ref`: `Rvalue.useRetag` re-validates
references and faults with `.undefined` on a `&bool` pointing to invalid byte
`2`. -/
theorem refute_step_v2_use_retag_invalid_ref :
    (match evalRvalueV2
        [.ref .shared .bool, .ref .shared .bool]
        [.immediate none, .immediate (some (.ptr ⟨some 1, 0, .isize⟩))]
        (v2MemOf v2InvalidBoolAlloc)
        (.ref .shared .bool)
        (.useRetag (.copy ⟨1, []⟩)) with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_read_no_prov_non_zst`: dereferencing a provenance-free
(`IntToPtr`) `*const u8` at non-null aligned address `8` faults with
`.undefined` because `u8` is non-zero-sized. -/
theorem refute_step_v2_read_no_prov_non_zst :
    (match readPlaceV2
        [.unit, .rawPtr .shared u8Ty]
        [.immediate (some .unit), .immediate (some (.ptr ⟨none, 8, .isize⟩))]
        MemoryState.empty
        false
        ⟨1, [.deref]⟩ with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_write_no_prov_non_zst`: storing through a provenance-free
(`IntToPtr`) `*mut u8` at non-null aligned address `8` faults with `.undefined`
because `u8` is non-zero-sized. -/
theorem refute_step_v2_write_no_prov_non_zst :
    (match writePlaceV2
        [.unit, .rawPtr .mut u8Ty]
        [.immediate (some .unit), .immediate (some (.ptr ⟨none, 8, .isize⟩))]
        MemoryState.empty
        ⟨1, [.deref]⟩
        u8Ty
        (.scalar ⟨.i8, false, BitVec.ofNat 128 1⟩) with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `bytes_v2_array_elem_layout`: `encodeValV2` refuses an array whose
element type has no `layoutOfTyV2` (`[[Option<bool>; 2]; 1]`, whose inner
`[Option<bool>; 2]` `layoutOfArrayV2` does not lay out), matching
`decodeValV2`, which needs that layout to split the bytes. A one-level
`[Option<bool>; 2]` still encodes to its niche tags `2` (`None`) and `1`
(`Some(true)`). -/
theorem refute_bytes_v2_array_elem_layout :
    encodeValV2 profileV2TargetEndian (.array (.array (.option .bool) 2) 1)
        (.array [.array [.optionVal none, .optionVal (some (.bool true))]]) =
      .error .unsupported ∧
    encodeValV2 profileV2TargetEndian (.array (.option .bool) 2)
        (.array [.optionVal none, .optionVal (some (.bool true))]) =
      .ok [AllocByte.init 2 none, AllocByte.init 1 none] :=
  ⟨rfl, rfl⟩

end GuardMutation
