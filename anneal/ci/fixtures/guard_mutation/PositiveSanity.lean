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
It also holds every anti-overreach positive canary for the guards checked
against this module (`Bytes`, `Enum`, `Ops`, `State`, `Step`, `Boundary`, and
their Profile v2 variants), plus the helpers those canaries share with
`BytesRefutations.lean`, `StepRefutations.lean`, and
`ProfileV2Refutations.lean`, which import this module. Keeping positive canaries
out of the refutation modules matters: a refutation module is expected to fail
to compile on its mutant, so a positive canary inside it could break unnoticed.
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

/-- Anti-overreach canary for zero-size raw-pointer dereference stores and
reads (`writePlaceV2` / `readPlaceV2`): `*mut ()` into a dead `.shared`
allocation succeeds consistently with `Memory.lean`. -/
theorem positive_step_v2_zst_raw_ptr_write_and_read :
    (match writePlaceV2
        [.unit, .rawPtr .mut .unit]
        [.immediate (some .unit), .immediate (some (.ptr ⟨some 1, 0, .isize⟩))]
        { allocations := [{
            allocId := 1
            alignLog2 := 0
            mutability := .shared
            bytes := [.init 0 none]
            live := false
          }], nextAllocId := 2 }
        { localId := 1, projection := [.deref] }
        .unit
        .unit with
     | .ok _ => True
     | .error _ => False) ∧
    (match readPlaceV2
        [.unit, .rawPtr .mut .unit]
        [.immediate (some .unit), .immediate (some (.ptr ⟨some 1, 0, .isize⟩))]
        { allocations := [{
            allocId := 1
            alignLog2 := 0
            mutability := .shared
            bytes := [.init 0 none]
            live := false
          }], nextAllocId := 2 }
        false
        { localId := 1, projection := [.deref] } with
     | .ok (.unit, some .unit, _, _) => True
     | _ => False) :=
  ⟨trivial, trivial⟩

/-- Anti-overreach canary for `step_v2_ptr_cast_const_to_mut`: `PtrToPtr`
casts that do not add mutability (`*mut u32` to `*const u32`, `*mut u32` to
`*mut u8`, `*const u32` to `*const u8`, and `*mut [u8]` to `*const [u8]`)
still succeed. -/
theorem positive_step_v2_ptr_cast_keeps_or_drops_mut :
    (match evalPtrToPtrCastV2 (.rawPtr .mut (.int .i32 false))
        (.ptr ⟨some 1, 0, .isize⟩) (.rawPtr .shared (.int .i32 false)) with
     | .ok (.ptr ⟨some 1, 0, .isize⟩) => True
     | _ => False) ∧
    (match evalPtrToPtrCastV2 (.rawPtr .mut (.int .i32 false))
        (.ptr ⟨some 1, 0, .isize⟩) (.rawPtr .mut (.int .i8 false)) with
     | .ok (.ptr ⟨some 1, 0, .isize⟩) => True
     | _ => False) ∧
    (match evalPtrToPtrCastV2 (.rawPtr .shared (.int .i32 false))
        (.ptr ⟨some 1, 0, .isize⟩) (.rawPtr .shared (.int .i8 false)) with
     | .ok (.ptr ⟨some 1, 0, .isize⟩) => True
     | _ => False) ∧
    (match evalPtrToPtrCastV2 (.rawPtr .mut (.slice (.int .i8 false)))
        (.slicePtr ⟨some 1, 0, .isize⟩ 4) (.rawPtr .shared (.slice (.int .i8 false))) with
     | .ok (.slicePtr ⟨some 1, 0, .isize⟩ 4) => True
     | _ => False) :=
  ⟨trivial, trivial, trivial, trivial⟩

/-- Admitted zero-sized single-variant fieldless enum (`enum One { A }`). -/
noncomputable def zstOneEnumTy : EnumTy := {
  id := 7
  discrWidth := .isize
  discrSigned := true
  tagRepr := .zeroSized
  discriminants := [0]
}

/-- Anti-overreach canary for provenance-free zero-size reference
dereferences: reading and writing `*r` for `r : &mut One` holding an aligned,
non-null address without provenance succeeds, consistently with
`refValidInMem` admitting such references at entry. -/
theorem positive_step_v2_zst_enum_no_provenance_deref :
    (match readPlaceV2
        [.unit, .ref .mut (.enum zstOneEnumTy)]
        [.immediate (some .unit), .immediate (some (.ptr ⟨none, 1, .isize⟩))]
        MemoryState.empty
        false
        { localId := 1, projection := [.deref] } with
     | .ok (_, some (.enumVal _ 0), _, _) => True
     | _ => False) ∧
    (match writePlaceV2
        [.unit, .ref .mut (.enum zstOneEnumTy)]
        [.immediate (some .unit), .immediate (some (.ptr ⟨none, 1, .isize⟩))]
        MemoryState.empty
        { localId := 1, projection := [.deref] }
        (.enum zstOneEnumTy)
        (.enumVal zstOneEnumTy 0) with
     | .ok _ => True
     | .error _ => False) :=
  ⟨trivial, trivial⟩

/-- Read-only 2-byte allocation with id `1` holding initialized bytes, for
the `get_unchecked` input-mutability refutations. -/
noncomputable def sharedInit2Mem : MemoryState :=
  { allocations := [{
      allocId := 1
      alignLog2 := 0
      mutability := .shared
      bytes := [.init 0 none, .init 0 none]
      live := true
    }], nextAllocId := 2 }

/-- Anti-overreach canary for `step_v2_get_unchecked_range_to_in_mut` and
`step_v2_get_unchecked_range_from_in_mut`: the `get_unchecked(..1)` and
`get_unchecked(1..)` calls those refutations make on a `&mut [u8]` input
succeed on a `&[u8]` input over the `.shared` allocation. -/
theorem positive_step_v2_get_unchecked_shared_input :
    (match execCoreCallOp sharedInit2Mem .sliceGetUncheckedRangeTo
        [(.ref .shared (.slice (.int .i8 false)),
            .slicePtr ⟨some 1, 0, .isize⟩ 2),
          (.rangeTo (.int .isize false), .rangeTo 1)]
        (.ref .shared (.slice (.int .i8 false))) with
     | .ok _ => True
     | .error _ => False) ∧
    (match execCoreCallOp sharedInit2Mem .sliceGetUncheckedRangeFrom
        [(.ref .shared (.slice (.int .i8 false)),
            .slicePtr ⟨some 1, 0, .isize⟩ 2),
          (.rangeFrom (.int .isize false), .rangeFrom 1)]
        (.ref .shared (.slice (.int .i8 false))) with
     | .ok _ => True
     | .error _ => False) :=
  ⟨trivial, trivial⟩

/-- Anti-overreach canary for `step_v2_raw_borrow_mut_through_const`:
`&raw const *p` through a `*const u8` still succeeds. -/
theorem positive_step_v2_raw_borrow_const_through_const :
    (match evalAddressOfRvalueV2
        [.unit, .rawPtr .shared (.int .i8 false), .rawPtr .shared (.int .i8 false)]
        [.immediate (some .unit), .immediate (some (.ptr ⟨some 1, 0, .isize⟩)),
          .immediate none]
        { allocations := [{
            allocId := 1
            alignLog2 := 0
            mutability := .mut
            bytes := [.init 0 none]
            live := true
          }], nextAllocId := 2 }
        (.rawPtr .shared (.int .i8 false)) .shared
        { localId := 1, projection := [.deref] } with
     | .ok _ => True
     | .error _ => False) :=
  trivial

/-- Overflow pair type `(u8, bool)`. -/
noncomputable def overflowPairU8 : MirTy := .tuple [.int .i8 false, .bool]

/-- Local slots after `move (_1.1)`: field 0 still holds `7_u8`. -/
noncomputable def partialPairLocals : List LocalSlot :=
  [.immediate (some .unit),
    .partialTuple [some (.scalar ⟨.i8, false, BitVec.ofNat 128 7⟩), none]]

/-- Anti-overreach canary for the `step_v2_partial_tuple_*` guards: moving
field 1 and then field 0 out of an initialized overflow pair returns both
values, leaves field 0 readable in between, and restores the uninitialized
`.immediate none` slot once both fields are moved. -/
theorem positive_step_v2_partial_tuple_moves :
    readPlaceV2 [.unit, overflowPairU8]
        [.immediate (some .unit),
          .immediate (some (.tuple
            [.scalar ⟨.i8, false, BitVec.ofNat 128 7⟩, .bool false]))]
        MemoryState.empty true
        { localId := 1, projection := [.field 1 .bool] } =
      .ok (.bool, some (.bool false), partialPairLocals, MemoryState.empty) ∧
    readPlaceV2 [.unit, overflowPairU8] partialPairLocals
        MemoryState.empty false
        { localId := 1, projection := [.field 0 (.int .i8 false)] } =
      .ok (.int .i8 false, some (.scalar ⟨.i8, false, BitVec.ofNat 128 7⟩),
        partialPairLocals, MemoryState.empty) ∧
    readPlaceV2 [.unit, overflowPairU8] partialPairLocals
        MemoryState.empty true
        { localId := 1, projection := [.field 0 (.int .i8 false)] } =
      .ok (.int .i8 false, some (.scalar ⟨.i8, false, BitVec.ofNat 128 7⟩),
        [.immediate (some .unit), .immediate none], MemoryState.empty) :=
  ⟨rfl, rfl, rfl⟩

/-- `buggy_add_u8(x: u8) -> u8 { x + 1 }` as captured under
`-Coverflow-checks=yes --panic abort` (hence the `.unreachable` unwind
action). -/
noncomputable def bodyOverflowAddV2 : Body := {
  argumentCount := 1
  locals := [.int .i8 false, .int .i8 false, .int .i8 false, overflowPairU8]
  basicBlocks := [
    { statements := [
        .storageLive 2,
        .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨3, []⟩ (.binaryOp .addWithOverflow (.copy ⟨2, []⟩)
          (.constant ⟨.int .i8 false, .scalar (BitVec.ofNat 128 1)⟩))
      ]
      terminator := .assert (.move ⟨3, [.field 1 .bool]⟩) false
        (.overflow .add) 1 .unreachable },
    { statements := [
        .assign ⟨0, []⟩ (.use (.move ⟨3, [.field 0 (.int .i8 false)]⟩)),
        .storageDead 2
      ]
      terminator := .return_ }
  ]
  isUnsafe := false
  identity := "guard_mutation::overflow_add_v2"
}

/-- Profile v2 program wrapping `bodyOverflowAddV2`, with overflow checks and
the default `.unwind` panic strategy, under which a failed overflow assert
faults rather than aborting. -/
noncomputable def progOverflowAddV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [bodyOverflowAddV2]
  overflowChecks := true
}

/-! The run below is split into one declaration per state so that no single
proof has to evaluate all seven steps of `progOverflowAddV2`. -/

/-- `progOverflowAddV2` called with `x = 254`. -/
noncomputable def queryOverflowAdd254 : Query :=
  { args := [.scalar ⟨.i8, false, BitVec.ofNat 128 254⟩] }

/-- Entry state of `progOverflowAddV2` on `queryOverflowAdd254`. -/
noncomputable def overflowAdd254S0 : State :=
  match initStateV2 progOverflowAddV2 queryOverflowAdd254 with
  | .ok s => s
  | .error _ => { frames := [], mem := MemoryState.empty }

/-- Successor of `s` under `progOverflowAddV2` (or `s` itself when the step
does not continue). -/
noncomputable def overflowAdd254Next (s : State) : State :=
  match evalStepV2 progOverflowAddV2 s with
  | .step s' => s'
  | _ => s

noncomputable def overflowAdd254S1 : State :=
  overflowAdd254Next overflowAdd254S0

noncomputable def overflowAdd254S2 : State :=
  overflowAdd254Next overflowAdd254S1

noncomputable def overflowAdd254S3 : State :=
  overflowAdd254Next overflowAdd254S2

noncomputable def overflowAdd254S4 : State :=
  overflowAdd254Next overflowAdd254S3

noncomputable def overflowAdd254S5 : State :=
  overflowAdd254Next overflowAdd254S4

noncomputable def overflowAdd254S6 : State :=
  overflowAdd254Next overflowAdd254S5

/-- Terminal output of the final step from `overflowAdd254S6`. -/
noncomputable def overflowAdd254Out : Out :=
  match evalStepV2 progOverflowAddV2 overflowAdd254S6 with
  | .done (.returned out) => out
  | _ => ⟨.unit, ⟨[]⟩⟩

theorem overflowAdd254_init :
    initStateV2 progOverflowAddV2 queryOverflowAdd254 = .ok overflowAdd254S0 :=
  rfl

theorem overflowAdd254_step1 :
    StepV2 progOverflowAddV2 overflowAdd254S0 (.step overflowAdd254S1) :=
  ⟨0, rfl, rfl⟩

theorem overflowAdd254_step2 :
    StepV2 progOverflowAddV2 overflowAdd254S1 (.step overflowAdd254S2) :=
  ⟨0, rfl, rfl⟩

theorem overflowAdd254_step3 :
    StepV2 progOverflowAddV2 overflowAdd254S2 (.step overflowAdd254S3) :=
  ⟨0, rfl, rfl⟩

theorem overflowAdd254_step4 :
    StepV2 progOverflowAddV2 overflowAdd254S3 (.step overflowAdd254S4) :=
  ⟨0, rfl, rfl⟩

theorem overflowAdd254_step5 :
    StepV2 progOverflowAddV2 overflowAdd254S4 (.step overflowAdd254S5) :=
  ⟨0, rfl, rfl⟩

theorem overflowAdd254_step6 :
    StepV2 progOverflowAddV2 overflowAdd254S5 (.step overflowAdd254S6) :=
  ⟨0, rfl, rfl⟩

theorem overflowAdd254_done :
    StepV2 progOverflowAddV2 overflowAdd254S6
      (.done (.returned overflowAdd254Out)) :=
  ⟨0, rfl, rfl⟩

theorem overflowAdd254_ret :
    overflowAdd254Out.ret = .scalar ⟨.i8, false, BitVec.ofNat 128 255⟩ :=
  rfl

/-- Anti-overreach canary for `step_v2_assert_failure_faults`:
`progOverflowAddV2` with `x = 254` passes its overflow assert and returns
`255`. -/
theorem positive_step_v2_overflow_assert_passes :
    ∃ out : Out,
      ReachesResultV2 progOverflowAddV2
        { args := [.scalar ⟨.i8, false, BitVec.ofNat 128 254⟩] }
        (.done (.returned out)) ∧
      out.ret = .scalar ⟨.i8, false, BitVec.ofNat 128 255⟩ := by
  refine ⟨overflowAdd254Out, ?_, overflowAdd254_ret⟩
  change ReachesResultV2 progOverflowAddV2 queryOverflowAdd254 _
  unfold ReachesResultV2
  rw [overflowAdd254_init]
  exact ⟨_,
    ReachesV2.tail (ReachesV2.tail (ReachesV2.tail (ReachesV2.tail
      (ReachesV2.tail (ReachesV2.tail (ReachesV2.refl _)
        overflowAdd254_step1) overflowAdd254_step2) overflowAdd254_step3)
      overflowAdd254_step4) overflowAdd254_step5) overflowAdd254_step6,
    overflowAdd254_done⟩

/-- Anti-overreach canary for `step_assert_optional_overflow_unsupported` and
`step_assert_checked_overflow_local_handler_unsupported`: with
`overflowChecks`, no crate-local `#[panic_handler]`, and `--panic abort`, a
failed checked overflow assertion aborts with the caller memory, while under
`--panic unwind` it still faults. -/
theorem positive_step_assert_checked_overflow_aborts :
    evalAssertFailure (.overflow .add) .abort .unreachable
        queryEmpty.callerMem false true =
      .done (.aborted queryEmpty.callerMem) ∧
      evalAssertFailure .overflowNeg .abort .continue_
        queryEmpty.callerMem false true =
        .done (.aborted queryEmpty.callerMem) ∧
      evalAssertFailure (.overflow .shl) .unwind .unreachable
        queryEmpty.callerMem false true = .fault .unsupported :=
  ⟨rfl, rfl, rfl⟩

/-- Anti-overreach canary for `enum_v2_overflow_pair_pointee`: an overflow
pair itself, and pointers to its integer or `bool` field types, remain admitted
local types. -/
theorem positive_enum_v2_overflow_pair_local :
    isSupportedV2LocalTy (.tuple [.int .i8 false, .bool]) = true ∧
    isSupportedV2LocalTy (.rawPtr .shared (.int .i8 false)) = true ∧
    isSupportedV2LocalTy (.ref .shared .bool) = true :=
  ⟨rfl, rfl, rfl⟩

/-- Anti-overreach canary for `enum_v2_overflow_pair_vec_elem`,
`enum_v2_overflow_pair_box_pointee`, and `enum_v2_overflow_pair_slice_elem`:
`Vec`, `Box`, and slices of scalar elements remain admitted local types. -/
theorem positive_enum_v2_vec_box_slice_scalar_elems :
    isSupportedV2LocalTy (.vec (.int .i8 false)) = true ∧
    isSupportedV2LocalTy (.box (.int .i64 false)) = true ∧
    isSupportedV2LocalTy (.box (.slice .bool)) = true ∧
    isSupportedV2LocalTy (.ref .shared (.slice .char)) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Anti-overreach canary for `step_v2_resolve_local_proj_validates_first`:
`updateValAtProjV2` updates `RangeTo` and `RangeFrom` `.field 0`. -/
theorem positive_step_v2_update_val_at_proj_ranges :
    (match updateValAtProjV2
        (.rangeTo (.int .isize false)) (.rangeTo 1)
        [.field 0 (.int .isize false)] (.scalar ⟨.isize, false, 7⟩) with
     | .ok (.rangeTo 7) => True
     | _ => False) ∧
    (match updateValAtProjV2
        (.rangeFrom (.int .isize false)) (.rangeFrom 2)
        [.field 0 (.int .isize false)] (.scalar ⟨.isize, false, 9⟩) with
     | .ok (.rangeFrom 9) => True
     | _ => False) :=
  ⟨trivial, trivial⟩

/-- Anti-overreach canary for `step_v2_assign_use_overlap_ub`: zero-sized
(`[u32; 0]`), `Scalar` (`([u32; 0], u32)`), padding-free `ScalarPair`
(`(u8, bool)`, `(u32, u32)`), and disjoint element (`a[0] = a[1]`) copies step
cleanly. -/
theorem positive_step_v2_assign_use_non_overlapping_and_scalar_pairs :
    let arr4Ty : MirTy := .array u8Ty 4
    let zstArrTy : MirTy := .array (.int .i32 false) 0
    let bodyNoPadPair : Body := {
      argumentCount := 0
      locals := [.unit, .tuple [u8Ty, .bool],
        .tuple [.int .i32 false, .int .i32 false],
        zstArrTy, .tuple [zstArrTy, .int .i32 false]]
      basicBlocks := []
    }
    let frameNoPadPair : FrameState := {
      defId := 0, blockIdx := 0, stmtIdx := 0
      locals := [
        .immediate none,
        .immediate (some (.tuple [.scalar ⟨.i8, false, 9⟩, .bool true])),
        .immediate (some (.tuple [
          .scalar ⟨.i32, false, 1⟩, .scalar ⟨.i32, false, 2⟩
        ])),
        .immediate (some (.array [])),
        .immediate (some (.tuple [.array [], .scalar ⟨.i32, false, 7⟩]))
      ]
    }
    let bodyArrOfArr : Body := {
      argumentCount := 0
      locals := [.unit, .array arr4Ty 2]
      basicBlocks := []
    }
    let vArr4 : Val := .array [
      .scalar ⟨.i8, false, 1⟩, .scalar ⟨.i8, false, 2⟩,
      .scalar ⟨.i8, false, 3⟩, .scalar ⟨.i8, false, 4⟩
    ]
    let frameArrOfArr : FrameState := {
      defId := 0, blockIdx := 0, stmtIdx := 0
      locals := [.immediate none, .immediate (some (.array [vArr4, vArr4]))]
    }
    (match evalStatementV2 bodyNoPadPair frameNoPadPair emptyMemory
        { allocations := [] }
        (.assign { localId := 1, projection := [] }
          (.use (.copy { localId := 1, projection := [] }))) with
     | .step _ => True
     | _ => False) ∧
    (match evalStatementV2 bodyNoPadPair frameNoPadPair emptyMemory
        { allocations := [] }
        (.assign { localId := 2, projection := [] }
          (.use (.copy { localId := 2, projection := [] }))) with
     | .step _ => True
     | _ => False) ∧
    (match evalStatementV2 bodyNoPadPair frameNoPadPair emptyMemory
        { allocations := [] }
        (.assign { localId := 3, projection := [] }
          (.use (.copy { localId := 3, projection := [] }))) with
     | .step _ => True
     | _ => False) ∧
    (match evalStatementV2 bodyNoPadPair frameNoPadPair emptyMemory
        { allocations := [] }
        (.assign { localId := 4, projection := [] }
          (.use (.copy { localId := 4, projection := [] }))) with
     | .step _ => True
     | _ => False) ∧
    (match evalStatementV2 bodyArrOfArr frameArrOfArr emptyMemory
        { allocations := [] }
        (.assign { localId := 1, projection := [.constantIndex 0 2 false] }
          (.use (.copy
            { localId := 1, projection := [.constantIndex 1 2 false] }))) with
     | .step _ => True
     | _ => False) :=
  ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- Anti-overreach canary for `step_v2_assign_aggregate_clobber_unsupported`:
non-clobbering scalar aggregate `_1 = (_1.0, _1.1)` steps cleanly. -/
theorem positive_step_v2_assign_aggregate_non_clobbering :
    let u32Ty : MirTy := .int .i32 false
    let body : Body := {
      argumentCount := 0
      locals := [.unit, .tuple [u32Ty, u32Ty]]
      basicBlocks := []
    }
    let frame : FrameState := {
      defId := 0, blockIdx := 0, stmtIdx := 0
      locals := [.immediate none,
        .immediate (some (.tuple [
          .scalar ⟨.i32, false, 1⟩, .scalar ⟨.i32, false, 2⟩
        ]))]
    }
    (match evalStatementV2 body frame emptyMemory { allocations := [] }
        (.assign { localId := 1, projection := [] }
          (.aggregateTuple [
            .copy { localId := 1, projection := [.field 0 u32Ty] },
            .copy { localId := 1, projection := [.field 1 u32Ty] }
          ])) with
     | .step _ => True
     | _ => False) :=
  trivial

/-- Anti-overreach canary for
`step_v2_assign_aggregate_deref_ptr_clobber_unsupported`: reading `*_2` at
field 0 before `_2` is overwritten steps cleanly for both tuple and array
aggregates. -/
theorem positive_step_v2_assign_aggregate_deref_ptr_before_overwrite :
    let u32Ty : MirTy := .int .i32 false
    let ptrU32Ty : MirTy := .rawPtr .shared u32Ty
    let arr2Ty : MirTy := .array u32Ty 2
    let tup3Ty : MirTy := .tuple [u32Ty, u32Ty, u32Ty]
    let mem : MemoryState := {
      allocations := [
        { allocId := 1, bytes := [
            .init 1 none, .init 0 none, .init 0 none, .init 0 none
          ], alignLog2 := 2, mutability := .mut, live := true },
        { allocId := 2, bytes := [
            .init 0 (some 1), .init 0 (some 1), .init 0 (some 1), .init 0 (some 1),
            .init 0 (some 1), .init 0 (some 1), .init 0 (some 1), .init 0 (some 1),
            .init 0 none, .init 0 none, .init 0 none, .init 0 none
          ], alignLog2 := 3, mutability := .mut, live := true }
      ]
      nextAllocId := 3
    }
    let body : Body := {
      argumentCount := 0
      locals := [
        .unit, u32Ty, ptrU32Ty, .rawPtr .mut arr2Ty, .rawPtr .mut tup3Ty
      ]
      basicBlocks := []
    }
    let frame : FrameState := {
      defId := 0, blockIdx := 0, stmtIdx := 0
      locals := [
        .immediate none,
        .immediate (some (.scalar ⟨.i32, false, 7⟩)),
        .indirect { allocId := 2, offset := 0 },
        .immediate (some (.ptr {
          allocId := some 2, offsetBytes := 0, width := .isize
        })),
        .immediate (some (.ptr {
          allocId := some 2, offsetBytes := 0, width := .isize
        }))
      ]
    }
    (match checkAggregateCopyHazardLoopV2 body.locals frame.locals mem
        (.memRange 2 0 12) tup3Ty false 0 [] [u32Ty, u32Ty, u32Ty] [
          .copy { localId := 2, projection := [.deref] },
          .copy { localId := 1, projection := [] },
          .copy { localId := 1, projection := [] }
        ] with
     | .ok () => True
     | _ => False) ∧
    (match evalStatementV2 body frame mem { allocations := [] }
        (.assign { localId := 3, projection := [.deref] }
          (.aggregateArray u32Ty [
            .copy { localId := 2, projection := [.deref] },
            .copy { localId := 1, projection := [] }
          ])) with
     | .step _ => True
     | _ => False) :=
  ⟨trivial, trivial⟩

/-- Anti-overreach canary for `step_v2_assign_repeat_overlap_ub`: disjoint
in-place `Rvalue.repeat_` `a = [a[1]; 2]` steps cleanly. -/
theorem positive_step_v2_assign_repeat_disjoint :
    let arr4Ty : MirTy := .array u8Ty 4
    let vArr4 : Val := .array [
      .scalar ⟨.i8, false, 1⟩, .scalar ⟨.i8, false, 2⟩,
      .scalar ⟨.i8, false, 3⟩, .scalar ⟨.i8, false, 4⟩
    ]
    let body : Body := {
      argumentCount := 0
      locals := [.unit, .array arr4Ty 2]
      basicBlocks := []
    }
    let frame : FrameState := {
      defId := 0, blockIdx := 0, stmtIdx := 0
      locals := [.immediate none, .immediate (some (.array [vArr4, vArr4]))]
    }
    (match evalStatementV2 body frame emptyMemory { allocations := [] }
        (.assign { localId := 1, projection := [] }
          (.repeat_
            (.copy { localId := 1, projection := [.constantIndex 1 2 false] })
            arr4Ty 2)) with
     | .step _ => True
     | _ => False) :=
  trivial

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

/-- Anti-overreach canary for `bytes_v2_array_elem_layout`: a one-level
`[Option<bool>; 2]` still encodes to its niche tags `2` (`None`) and `1`
(`Some(true)`). -/
theorem positive_bytes_v2_array_elem_layout_one_level :
    encodeValV2 profileV2TargetEndian (.array (.option .bool) 2)
        (.array [.optionVal none, .optionVal (some (.bool true))]) =
      .ok [AllocByte.init 2 none, AllocByte.init 1 none] :=
  rfl

/-- Anti-overreach canary for `core_contracts_slice_{subslice,split_at}_in_mut`:
the same `Index::index` and `split_at` calls on a `&[u8]` input over the
`.shared` allocation succeed. -/
theorem positive_core_contracts_slice_shared_input :
    (match execCoreContractOp sharedInit2Mem
        (.sliceIndexRange .shared (.int .i8 false))
        [(.ref .shared (.slice (.int .i8 false)),
            .slicePtr ⟨some 1, 0, .isize⟩ 2),
          (.range (.int .isize false), .range 0 1)]
        (.ref .shared (.slice (.int .i8 false))) with
     | .ok _ => True
     | .error _ => False) ∧
    (match execCoreContractOp sharedInit2Mem
        (.sliceSplitAt .shared (.int .i8 false))
        [(.ref .shared (.slice (.int .i8 false)),
            .slicePtr ⟨some 1, 0, .isize⟩ 2),
          (.int .isize false, .scalar ⟨.isize, false, 1⟩)]
        (.tuple [.ref .shared (.slice (.int .i8 false)),
          .ref .shared (.slice (.int .i8 false))]) with
     | .ok _ => True
     | .error _ => False) :=
  ⟨trivial, trivial⟩

/-- Anti-overreach canary for `core_contracts_i128_host_overflow`: in-bounds
128-bit checked, saturating, and overflowing arithmetic succeed without false
overflow. -/
theorem positive_core_contracts_i128_in_bounds :
    let u128Ty : MirTy := .int .i128 false
    let u128MaxMinus1 : ScalarVal :=
      ⟨.i128, false, BitVec.ofNat 128 340282366920938463463374607431768211454⟩
    let u128Max : ScalarVal :=
      ⟨.i128, false, BitVec.ofNat 128 340282366920938463463374607431768211455⟩
    let u128One : ScalarVal := ⟨.i128, false, 1⟩
    let u128Two : ScalarVal := ⟨.i128, false, 2⟩
    let u128Three : ScalarVal := ⟨.i128, false, 3⟩
    execCoreContractOp MemoryState.empty (.numCheckedAdd .i128 false)
      [(u128Ty, .scalar u128One), (u128Ty, .scalar u128Two)]
      (.option u128Ty) =
      .ok (.optionVal (some (.scalar u128Three)), MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numSaturatingAdd .i128 false)
      [(u128Ty, .scalar u128MaxMinus1), (u128Ty, .scalar u128One)] u128Ty =
      .ok (.scalar u128Max, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numOverflowingAdd .i128 false)
      [(u128Ty, .scalar u128One), (u128Ty, .scalar u128Two)]
      (.tuple [u128Ty, .bool]) =
      .ok (.tuple [.scalar u128Three, .bool false], MemoryState.empty) :=
  ⟨rfl, rfl, rfl⟩

/-- Anti-overreach canary for `bytes_v2_slice_uninhabited_elem`: empty
`&[] : &[!]` (`len = 0`) and positive-length inhabited ZST `&[()]` slices
remain valid under `refValidInMem`. -/
theorem positive_bytes_v2_slice_empty_never_and_zst_unit :
    refValidInMem MemoryState.empty .shared (.slice .never)
      (.slicePtr ⟨none, 1, .isize⟩ 0) = .ok () ∧
    refValidInMem MemoryState.empty .shared (.slice .unit)
      (.slicePtr ⟨none, 1, .isize⟩ 3) = .ok () :=
  ⟨rfl, rfl⟩

/-- Anti-overreach canary for `core_contracts_option_unwrap_refs_valid`:
`Option::unwrap` on a live `Some(&u8)` succeeds. -/
theorem positive_core_contracts_option_unwrap_live_ref :
    let refU8Ty : MirTy := .ref .shared (.int .i8 false)
    let liveMem : MemoryState := {
      allocations := [{
        allocId := 2
        alignLog2 := 0
        mutability := .shared
        bytes := [.init 7 none]
        live := true
      }]
      nextAllocId := 3
    }
    execCoreContractOp liveMem (.optionUnwrap refU8Ty)
      [(.option refU8Ty, .optionVal (some (.ptr ⟨some 2, 0, .isize⟩)))]
      refU8Ty = .ok (.ptr ⟨some 2, 0, .isize⟩, liveMem) :=
  rfl

/-- Anti-overreach canary for `step_v2_option_discriminant_dst_ty`: projected
`Option` discriminant returns `1isize` for an `isize` destination. -/
theorem positive_step_v2_option_discriminant_isize_dst :
    let optU8Ty : MirTy := .option (.int .i8 false)
    let tupTy : MirTy := .tuple [optU8Ty, .int .i8 false]
    let locals : List LocalSlot := [
      .immediate (some (.tuple [.optionVal (some (.scalar ⟨.i8, false, 9⟩)),
        .scalar ⟨.i8, false, 1⟩]))
    ]
    let place : Place := { localId := 0, projection := [.field 0 optU8Ty] }
    evalRvalueV2 [tupTy] locals MemoryState.empty (.int .isize true)
      (.discriminant place) =
      .ok (.scalar ⟨.isize, true, BitVec.ofNat 128 1⟩, locals,
        MemoryState.empty) :=
  rfl

/-- Anti-overreach canary for `step_v2_ptr_metadata_str_dst_ty`: `ptrMetadata`
on a live `&str` returns its byte length for a `usize` destination. -/
theorem positive_step_v2_ptr_metadata_str_usize :
    let localsTys : List MirTy := [.int .isize false, .ref .shared .str]
    let validStr : Val := .slicePtr ⟨some 2, 0, .isize⟩ 2
    let locals : List LocalSlot := [.immediate none, .immediate (some validStr)]
    let mem : MemoryState := {
      nextAllocId := 3
      allocations := [{
        allocId := 2
        bytes := [.init 111 none, .init 107 none]
        alignLog2 := 0
        mutability := .shared
        live := true
      }]
    }
    evalRvalueV2 localsTys locals mem (.int .isize false)
      (.unaryOp .ptrMetadata (.copy { localId := 1, projection := [] })) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 2⟩, locals, mem) :=
  rfl

/-- Anti-overreach canaries for `bytes_utf8_*`: valid multi-byte UTF-8
sequences at every RFC 3629 range boundary are accepted by `validUtf8Bytes`. -/
theorem positive_bytes_utf8_valid_boundaries :
    validUtf8Bytes [0xC2, 0x80] = true ∧
    validUtf8Bytes [0xDF, 0xBF] = true ∧
    validUtf8Bytes [0xE0, 0xA0, 0x80] = true ∧
    validUtf8Bytes [0xED, 0x9F, 0xBF] = true ∧
    validUtf8Bytes [0xEE, 0x80, 0x80] = true ∧
    validUtf8Bytes [0xF0, 0x90, 0x80, 0x80] = true ∧
    validUtf8Bytes [0xF0, 0x9F, 0x98, 0x80] = true ∧
    validUtf8Bytes [0xF4, 0x8F, 0xBF, 0xBF] = true ∧
    validUtf8Bytes [0xE2, 0x82, 0xAC] = true ∧
    validUtf8Bytes [0xC2, 0xBF] = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ---------------------------------------------------------------------------
-- Shared setup programs and positive setup-prefix canaries for the 8 pinned
-- multi-step refutations in `BytesRefutations.lean` and `StepRefutations.lean`
-- ---------------------------------------------------------------------------

/-- Program `StorageLive(_1: u32); _0 = copy _1; return`, used to test indirect
uninitialized-byte reads after `forceAllocation`. -/
noncomputable def progIndirectUninitRead : Program :=
  mkSingleBlockProg 0 [u32Ty, u32Ty]
    [.storageLive 1, .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]

/-- Program moving out of `_1 : u32` and then reading `_1` again without
re-initialization. -/
noncomputable def progUseAfterMove : Program :=
  mkSingleBlockProg 1 [u32Ty, u32Ty]
    [.assign ⟨0, []⟩ (.use (.move ⟨1, []⟩)),
     .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]

/-- Program returning immediately with an uninitialized `_0 : u32`. -/
noncomputable def progReturnUninit : Program :=
  mkSingleBlockProg 0 [u32Ty] [] .return_

/-- Program whose local `_1` starts `.dead` because it has a `StorageLive`
annotation in the body. -/
noncomputable def progDeadLocalForForceAlloc : Program :=
  mkSingleBlockProg 0 [.unit, u32Ty] [.storageLive 1] .return_

/-- Profile v2 program taking a shared reference to stack parameter `_1 : u8`
and attempting to return it. -/
noncomputable def progDanglingStackRefV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [{
    argumentCount := 1
    locals := [.ref .shared (.int .i8 false), .int .i8 false]
    basicBlocks := [{
      statements := [
        .assign { localId := 0, projection := [] }
          (.ref .shared { localId := 1, projection := [] })
      ]
      terminator := .return_
    }]
    isUnsafe := false
    identity := "guard_mutation::dangling_stack_ref_v2"
  }]
}

/-- Profile v2 program under `--panic abort` writing `7 : u8` through `&mut u8`
before failing a non-optional `.divByZero` assert. -/
noncomputable def progMutBeforeAbortV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  panicStrategy := .abort
  hasLocalPanicHandler := false
  bodies := [{
    argumentCount := 1
    locals := [.unit, .ref .mut u8Ty]
    basicBlocks := [{
      statements := [
        .assign { localId := 1, projection := [.deref] }
          (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 7)⟩))
      ]
      terminator :=
        .assert (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩) true
          .divByZero 0 .unreachable
    }]
    isUnsafe := false
    identity := "guard_mutation::mut_before_abort_v2"
  }]
}

def cmBeforeAbort : CallerMemory := {
  allocations := [{
    allocId := 2
    alignLog2 := 0
    mutability := .mut
    bytes := [.init 0 none]
    live := true
  }]
}

def cmAfterAbort : CallerMemory := {
  allocations := [{
    allocId := 2
    alignLog2 := 0
    mutability := .mut
    bytes := [.init 7 none]
    live := true
  }]
}

/-- Shared valid `&'static str` `"ok"` rodata operand for `.panicAbort`
guard-mutation fixtures. -/
def panicOkStrOperand : Operand :=
  .constant ⟨.ref .shared .str, .rodataRef [.init 111, .init 107] 0 0 (some 2)⟩

/-- Profile v2 program under `--panic abort` writing `7 : u8` through `&mut u8`
before executing `.coreCall .panicAbort`. -/
noncomputable def progMutBeforeCorePanicV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  panicStrategy := .abort
  hasLocalPanicHandler := false
  bodies := [{
    argumentCount := 1
    locals := [.unit, .ref .mut u8Ty, .never]
    basicBlocks := [{
      statements := [
        .assign { localId := 1, projection := [.deref] }
          (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 7)⟩))
      ]
      terminator :=
        .coreCall .panicAbort [panicOkStrOperand]
          { localId := 2, projection := [] } none .unreachable
    }]
    isUnsafe := false
    identity := "guard_mutation::mut_before_core_panic_v2"
  }]
}

/-- Anti-overreach canaries for the 8 pinned multi-step setup refutations:
each setup prefix (`initState`/`initStateV2`/`forceAllocation`/`evalStep`
leading up to the final tested step) must still succeed on every mutant so
an over-rejecting mutant cannot register a false kill during setup. -/
theorem positive_pinned_setup_prefixes :
    (match initState progIndirectUninitRead queryEmpty with
     | .ok s₀ =>
       match evalStep progIndirectUninitRead 0 s₀ with
       | .step s₁ =>
         match forceAllocation progIndirectUninitRead s₁ 1 with
         | .ok _ => True
         | .error _ => False
       | _ => False
     | .error _ => False) ∧
    (match initState progUseAfterMove { args := [u32Val 7] } with
     | .ok s₀ =>
       match forceAllocation progUseAfterMove s₀ 1 with
       | .ok (s₁, _) =>
         match evalStep progUseAfterMove 0 s₁ with
         | .step _ => True
         | _ => False
       | .error _ => False
     | .error _ => False) ∧
    (match initState progReturnUninit queryEmpty with
     | .ok s₀ =>
       match forceAllocation progReturnUninit s₀ 0 with
       | .ok _ => True
       | .error _ => False
     | .error _ => False) ∧
    (match initState progDeadLocalForForceAlloc queryEmpty with
     | .ok _ => True
     | .error _ => False) ∧
    (match initStateV2 progDanglingStackRefV2
        { args := [.scalar ⟨.i8, false, BitVec.ofNat 128 42⟩] } with
     | .ok s₀ =>
       match evalStepV2 progDanglingStackRefV2 s₀ with
       | .step _ => True
       | _ => False
     | .error _ => False) ∧
    (match initStateV2 progMutBeforeAbortV2
        { args := [.ptr ⟨some 2, 0, .isize⟩], callerMem := cmBeforeAbort } with
     | .ok s₀ =>
       match evalStepV2 progMutBeforeAbortV2 s₀ with
       | .step _ => True
       | _ => False
     | .error _ => False) ∧
    (let rawU8Const : MirTy := .rawPtr .shared u8Ty
     let prog : Program := {
       scope := .unit
       pointerWidthBits := 64
       mirProfileVersion := 2
       bodies := [{
         argumentCount := 1
         locals := [u8Ty, rawU8Const, u8Ty, rawU8Const]
         basicBlocks := [{
           statements := [
             .storageLive 2,
             .assign { localId := 2, projection := [] }
               (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 42)⟩)),
             .storageLive 3,
             .assign { localId := 3, projection := [] }
               (.addressOf .shared { localId := 2, projection := [] }),
             .assign { localId := 0, projection := [] }
               (.use (.copy { localId := 1, projection := [.deref] }))
           ]
           terminator := .return_
         }]
         isUnsafe := true
         identity := "guard_mutation::dangling_raw_ptr_vs_stack_alloc"
       }]
     }
     match initStateV2 prog
         { args := [.ptr ⟨some 2, 0, .isize⟩],
           callerMem := { allocations := [] } } with
     | .ok s0 =>
       match evalStepV2 prog s0 with
       | .step s1 =>
         match evalStepV2 prog s1 with
         | .step s2 =>
           match evalStepV2 prog s2 with
           | .step s3 =>
             match evalStepV2 prog s3 with
             | .step _ => True
             | _ => False
           | _ => False
         | _ => False
       | _ => False
     | .error _ => False) ∧
    (match initStateV2 progMutBeforeCorePanicV2
        { args := [.ptr ⟨some 2, 0, .isize⟩], callerMem := cmBeforeAbort } with
     | .ok s₀ =>
       match evalStepV2 progMutBeforeCorePanicV2 s₀ with
       | .step _ => True
       | _ => False
     | .error _ => False) :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end GuardMutation
