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
# Positive Sanity Check for Guard-Mutation CI

Confirms that a basic UB-free program (`30u32 + 12u32 = 42u32`) still proves
against every single-guard mutant of `Trusted.MirSemantics`.

Why this matters: positive proofs keep passing when a UB guard is deleted or
weakened, which is precisely why guard-mutation CI pairs this sanity check with
explicit negative refutations. Passing this file on each mutant also rules out
accidental syntax or type errors that would otherwise masquerade as mutant
kills.
It also holds the Profile v2 anti-overreach canaries for the `Bytes`, `State`,
and `Step` guards (and the helpers `ProfileV2Refutations.lean` imports), so
every mutant must keep those valid operations working too.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

theorem positive_sanity_add_u32 :
    Behavior (mkBinOpProg .add u32Ty u32Ty u32Ty)
      { args := [u32Val 30, u32Val 12] }
      (.returned ⟨u32Val 42, ⟨[]⟩⟩) :=
  behavior_of_execDone (fuel := 2) rfl

-- ---------------------------------------------------------------------------
-- Profile v2 helpers and canaries (shared with `ProfileV2Refutations.lean`)
-- ---------------------------------------------------------------------------

/-- Live mutable 4-byte allocation holding initialized `0` bytes. -/
noncomputable def v2MutInit4Alloc : Allocation := {
  allocId := 1
  alignLog2 := 2
  mutability := .mut
  bytes := [.init 0 none, .init 0 none, .init 0 none, .init 0 none]
  live := true
}

/-- Live mutable 1-byte allocation holding valid `bool` byte `1`. -/
noncomputable def v2ValidBoolAlloc : Allocation := {
  allocId := 1
  alignLog2 := 0
  mutability := .mut
  bytes := [.init 1 none]
  live := true
}

/-- Wrap a single allocation in a `MemoryState`. -/
noncomputable def v2MemOf (a : Allocation) : MemoryState :=
  { nextAllocId := 2, allocations := [a] }

/-- Construct an `isize` scalar `Val` from its two's-complement bit pattern. -/
noncomputable def v2IsizeBits (bits : Nat) : Val :=
  .scalar ⟨.isize, true, BitVec.ofNat 128 bits⟩

/-- Construct a `usize` scalar `Val`. -/
noncomputable def v2UsizeVal (n : Nat) : Val :=
  .scalar ⟨.isize, false, BitVec.ofNat 128 n⟩

/-- Body whose return local `_0` has type `(&mut [u8], &mut [u8])`. -/
noncomputable def bodyReturnAliasedMutSlices : Body := {
  argumentCount := 0
  locals := [.tuple [.ref .mut (.slice u8Ty), .ref .mut (.slice u8Ty)]]
  basicBlocks := [{ statements := [], terminator := .return_ }]
}

/-- Anti-overreach Profile v2 canaries for the `Bytes`, `State`, and `Step`
guards: overlapping shared spans and disjoint mutable spans pass
`spansPairwiseDisjoint`, a non-underflowing `usize::unchecked_sub` succeeds, an
in-bounds negative `evalPtrOffsetV2` succeeds, returning disjoint `&mut [u8]`
slices succeeds, and `Rvalue.useRetag` of a `&bool` pointing to valid byte `1`
succeeds. -/
theorem positive_sanity_v2_step_and_bytes :
    spansPairwiseDisjoint [(false, 1, 0, 2), (false, 1, 1, 2)] = true ∧
    spansPairwiseDisjoint [(true, 1, 0, 2), (true, 1, 2, 2)] = true ∧
    execCoreCallOp MemoryState.empty .usizeUncheckedSub
      [(.int .isize false, v2UsizeVal 5), (.int .isize false, v2UsizeVal 2)]
      (.int .isize false) = .ok (v2UsizeVal 3) ∧
    evalPtrOffsetV2 (v2MemOf v2MutInit4Alloc) 1 ⟨some 1, 3, .isize⟩
      (v2IsizeBits (Nat.pow 2 64 - 2)) = .ok (.ptr ⟨some 1, 1, .isize⟩) ∧
    (match evalTerminatorV2 bodyReturnAliasedMutSlices
        { statements := [], terminator := .return_ }
        { defId := 0, blockIdx := 0, stmtIdx := 0,
          locals := [.immediate (some (.tuple [
            .slicePtr ⟨some 1, 0, .isize⟩ 2,
            .slicePtr ⟨some 1, 2, .isize⟩ 2]))] }
        (v2MemOf v2MutInit4Alloc)
        ⟨[v2MutInit4Alloc]⟩ with
     | .done (.returned _) => True
     | _ => False) ∧
    (match evalRvalueV2
        [.ref .shared .bool, .ref .shared .bool]
        [.immediate none, .immediate (some (.ptr ⟨some 1, 0, .isize⟩))]
        (v2MemOf v2ValidBoolAlloc)
        (.ref .shared .bool)
        (.useRetag (.copy ⟨1, []⟩)) with
     | .ok _ => True
     | _ => False) :=
  ⟨rfl, rfl, rfl, rfl, trivial, trivial⟩

end GuardMutation
