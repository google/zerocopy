-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Cross-Release `AbiCompatHash` Equivalence and Verified ABI Marshaling Thunk Synthesis (`AbiBridgeThunk`)

Mechanizes:
1. `PhysicalArgLoc` and `PhysicalFnAbi`: the physical register/stack calling-convention
   descriptor hashed by `AbiCompatHash(sig)` in `.anneal-mir`.
2. `direct_link_sound_of_abi_eq`: whenever a caller compiled under `rustc` release $V_2$
   and a cached `.rlib` callee verified under release $V_1$ have equal `PhysicalFnAbi`
   (`abiCompatEq callerAbi calleeAbi = true`), direct cross-release linking preserves
   exact call semantics without recompiling or re-proving the callee.
3. `synthesizeBridgeThunk` and `bridge_thunk_sound`: when upstream `rustc` modifies
   `CanonAbi::Rust` for a subset of signatures (such as `rustc 1.100.0` PR `#161583` on
   `i686` shifting `f32`/`f64`/SIMD arguments from `[esp + disp]` stack slots into
   `XMM0..XMM2`), the synthesized marshaling thunk translates between `callerAbi` and
   `calleeAbi` while preserving exact argument values, return values, stack pointer
   offset, and callee-saved registers.
-/

namespace Anneal.AbiBridge

/-- Physical parameter or return location in `MiniMach`. -/
inductive PhysicalArgLoc where
  | gpr (regIdx : Nat)
  | xmm (regIdx : Nat)
  | stack (slotIdx : Nat)
  deriving Repr, DecidableEq

/-- Canonical physical calling-convention projection hashed by `AbiCompatHash`. -/
structure PhysicalFnAbi where
  convId : Nat
  args : List PhysicalArgLoc
  ret : PhysicalArgLoc
  calleePopBytes : Nat
  canUnwind : Bool
  deriving Repr, DecidableEq

/-- Decidable cross-release ABI compatibility check (`AbiCompatHash` equality model). -/
def abiCompatEq (callerAbi calleeAbi : PhysicalFnAbi) : Bool :=
  callerAbi == calleeAbi

/-- Machine state at a function call boundary. -/
structure CallFrameState where
  gprs : Nat → UInt64
  xmms : Nat → UInt64
  stackSlots : Nat → UInt64
  calleeSaved : Nat → UInt64
  spOffset : Int

/-- Read a 64-bit value (or zero-extended 32-bit float/int word) from `loc`. -/
def readPhysLoc (st : CallFrameState) (loc : PhysicalArgLoc) : UInt64 :=
  match loc with
  | .gpr r => st.gprs r
  | .xmm x => st.xmms x
  | .stack s => st.stackSlots s

/-- Write a 64-bit value to `loc`, preserving `calleeSaved` and `spOffset`. -/
def writePhysLoc (st : CallFrameState) (loc : PhysicalArgLoc) (v : UInt64) : CallFrameState :=
  match loc with
  | .gpr r => { st with gprs := fun i => if i == r then v else st.gprs i }
  | .xmm x => { st with xmms := fun i => if i == x then v else st.xmms i }
  | .stack s => { st with stackSlots := fun i => if i == s then v else st.stackSlots i }

@[simp]
theorem readPhysLoc_writePhysLoc_same (st : CallFrameState) (loc : PhysicalArgLoc) (v : UInt64) :
    readPhysLoc (writePhysLoc st loc v) loc = v := by
  cases loc <;> simp [readPhysLoc, writePhysLoc]

theorem readPhysLoc_writePhysLoc_diff (st : CallFrameState) (loc1 loc2 : PhysicalArgLoc) (v : UInt64)
    (hne : loc2 ≠ loc1) :
    readPhysLoc (writePhysLoc st loc1 v) loc2 = readPhysLoc st loc2 := by
  cases loc1 <;> cases loc2 <;> simp [readPhysLoc, writePhysLoc] at hne ⊢
  · intro h; subst h; contradiction
  · intro h; subst h; contradiction
  · intro h; subst h; contradiction

@[simp]
theorem writePhysLoc_calleeSaved (st : CallFrameState) (loc : PhysicalArgLoc) (v : UInt64) :
    (writePhysLoc st loc v).calleeSaved = st.calleeSaved := by
  cases loc <;> rfl

@[simp]
theorem writePhysLoc_spOffset (st : CallFrameState) (loc : PhysicalArgLoc) (v : UInt64) :
    (writePhysLoc st loc v).spOffset = st.spOffset := by
  cases loc <;> rfl

/-- Extract the list of argument values placed by a caller according to `abi.args`. -/
def decodeArgs (st : CallFrameState) (locs : List PhysicalArgLoc) : List UInt64 :=
  locs.map (readPhysLoc st)

/-- Write a list of argument values into `locs` from left to right. -/
def encodeArgs (st : CallFrameState) (locs : List PhysicalArgLoc) (vals : List UInt64) : CallFrameState :=
  match locs, vals with
  | loc :: restLocs, v :: restVals => encodeArgs (writePhysLoc st loc v) restLocs restVals
  | _, _ => st

@[simp]
theorem encodeArgs_calleeSaved (st : CallFrameState) (locs : List PhysicalArgLoc) (vals : List UInt64) :
    (encodeArgs st locs vals).calleeSaved = st.calleeSaved := by
  induction locs generalizing st vals with
  | nil => simp [encodeArgs]
  | cons l ls ih =>
      cases vals with
      | nil => simp [encodeArgs]
      | cons v vs =>
          simp only [encodeArgs]
          rw [ih, writePhysLoc_calleeSaved]

@[simp]
theorem encodeArgs_spOffset (st : CallFrameState) (locs : List PhysicalArgLoc) (vals : List UInt64) :
    (encodeArgs st locs vals).spOffset = st.spOffset := by
  induction locs generalizing st vals with
  | nil => simp [encodeArgs]
  | cons l ls ih =>
      cases vals with
      | nil => simp [encodeArgs]
      | cons v vs =>
          simp only [encodeArgs]
          rw [ih, writePhysLoc_spOffset]

theorem readPhysLoc_encodeArgs_not_mem (st : CallFrameState) (loc : PhysicalArgLoc)
    (locs : List PhysicalArgLoc) (vals : List UInt64)
    (hnot : ∀ l ∈ locs, loc ≠ l) :
    readPhysLoc (encodeArgs st locs vals) loc = readPhysLoc st loc := by
  induction locs generalizing st vals with
  | nil => simp [encodeArgs]
  | cons l ls ih =>
      cases vals with
      | nil => simp [encodeArgs]
      | cons v vs =>
          simp only [encodeArgs]
          have hne : loc ≠ l := hnot l (by simp)
          have hrest : ∀ l' ∈ ls, loc ≠ l' := fun l' hl' => hnot l' (by simp [hl'])
          rw [ih (writePhysLoc st l v) vs hrest]
          exact readPhysLoc_writePhysLoc_diff st l loc v hne

theorem decodeArgs_encodeArgs_id (st : CallFrameState)
    (locs : List PhysicalArgLoc) (vals : List UInt64)
    (hnodup : locs.Nodup) (hlen : locs.length = vals.length) :
    decodeArgs (encodeArgs st locs vals) locs = vals := by
  induction locs generalizing st vals with
  | nil =>
      cases vals with
      | nil => rfl
      | cons _ _ => contradiction
  | cons l ls ih =>
      cases vals with
      | nil => contradiction
      | cons v vs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          rcases List.nodup_cons.mp hnodup with ⟨hnotmem, hnodup_ls⟩
          simp only [decodeArgs, List.map_cons, encodeArgs]
          have hhead : readPhysLoc (encodeArgs (writePhysLoc st l v) ls vs) l = v := by
            have hnot : ∀ l' ∈ ls, l ≠ l' := by
              intro l' hl' heq
              subst heq
              exact hnotmem hl'
            rw [readPhysLoc_encodeArgs_not_mem (writePhysLoc st l v) l ls vs hnot]
            exact readPhysLoc_writePhysLoc_same st l v
          have htail : List.map (readPhysLoc (encodeArgs (writePhysLoc st l v) ls vs)) ls = vs :=
            ih (writePhysLoc st l v) vs hnodup_ls hlen
          rw [hhead, htail]

/-- Execute a direct call from a `callerAbi` call site to a `calleeAbi` function body `sem`. -/
def execDirectCall (callerAbi calleeAbi : PhysicalFnAbi) (sem : List UInt64 → UInt64)
    (st : CallFrameState) (argVals : List UInt64) : CallFrameState :=
  let stCaller := encodeArgs st callerAbi.args argVals
  let calleeInputs := decodeArgs stCaller calleeAbi.args
  let retVal := sem calleeInputs
  writePhysLoc stCaller calleeAbi.ret retVal

/-- Theorem 1 (`direct_link_sound_of_abi_eq`): When `abiCompatEq callerAbi calleeAbi = true`,
linking the `callerAbi` call site directly to the cached `calleeAbi` object section
without recompiling or re-proving the callee yields the exact mathematical return value
`sem argVals` in `callerAbi.ret` and preserves `calleeSaved` and `spOffset`. -/
theorem direct_link_sound_of_abi_eq
    (callerAbi calleeAbi : PhysicalFnAbi) (sem : List UInt64 → UInt64)
    (st : CallFrameState) (argVals : List UInt64)
    (heq : abiCompatEq callerAbi calleeAbi = true)
    (hnodup : callerAbi.args.Nodup)
    (hlen : callerAbi.args.length = argVals.length) :
    let stOut := execDirectCall callerAbi calleeAbi sem st argVals
    readPhysLoc stOut callerAbi.ret = sem argVals ∧
    stOut.calleeSaved = st.calleeSaved ∧
    stOut.spOffset = st.spOffset := by
  unfold abiCompatEq at heq
  simp only [beq_iff_eq] at heq
  subst heq
  dsimp [execDirectCall]
  rw [decodeArgs_encodeArgs_id st callerAbi.args argVals hnodup hlen]
  refine ⟨readPhysLoc_writePhysLoc_same _ _ _, ?_, ?_⟩
  · rw [writePhysLoc_calleeSaved, encodeArgs_calleeSaved]
  · rw [writePhysLoc_spOffset, encodeArgs_spOffset]

/-- A synthesized ABI bridge thunk (`AbiBridgeThunk`) between `callerAbi` and `calleeAbi`. -/
structure AbiBridgeThunk where
  srcArgs : List PhysicalArgLoc
  dstArgs : List PhysicalArgLoc
  srcRet : PhysicalArgLoc
  dstRet : PhysicalArgLoc
  deriving Repr, DecidableEq

/-- Synthesize a deterministic marshaling thunk when `callerAbi` and `calleeAbi` have
the same arity and unwind contract. -/
def synthesizeBridgeThunk (callerAbi calleeAbi : PhysicalFnAbi) : Option AbiBridgeThunk :=
  if callerAbi.args.length == calleeAbi.args.length && callerAbi.canUnwind == calleeAbi.canUnwind then
    some {
      srcArgs := callerAbi.args
      dstArgs := calleeAbi.args
      srcRet := calleeAbi.ret
      dstRet := callerAbi.ret
    }
  else
    none

/-- Decidable certificate checker for a synthesized `AbiBridgeThunk`. -/
def checkBridgeThunk (callerAbi calleeAbi : PhysicalFnAbi) (thunk : AbiBridgeThunk) : Bool :=
  (thunk.srcArgs == callerAbi.args) &&
  (thunk.dstArgs == calleeAbi.args) &&
  (thunk.srcRet == calleeAbi.ret) &&
  (thunk.dstRet == callerAbi.ret) &&
  (callerAbi.args.length == calleeAbi.args.length)

/-- Execute a bridged call through `thunk`:
1. Reads caller arguments from `thunk.srcArgs`
2. Marshals them into `thunk.dstArgs`
3. Invokes the unmodified cached callee (`calleeAbi`)
4. Reads callee return from `thunk.srcRet` and writes to `thunk.dstRet`. -/
def execBridgedCall (callerAbi calleeAbi : PhysicalFnAbi) (thunk : AbiBridgeThunk)
    (sem : List UInt64 → UInt64) (st : CallFrameState) (argVals : List UInt64) : CallFrameState :=
  let stCaller := encodeArgs st callerAbi.args argVals
  let marshaledVals := decodeArgs stCaller thunk.srcArgs
  let stCalleeEntry := encodeArgs stCaller thunk.dstArgs marshaledVals
  let calleeInputs := decodeArgs stCalleeEntry calleeAbi.args
  let retVal := sem calleeInputs
  let stCalleeExit := writePhysLoc stCalleeEntry calleeAbi.ret retVal
  let bridgedRet := readPhysLoc stCalleeExit thunk.srcRet
  writePhysLoc stCalleeExit thunk.dstRet bridgedRet

/-- Theorem 2 (`bridge_thunk_sound`): Any thunk accepted by `checkBridgeThunk`
soundly bridges a `callerAbi` call site to a cached `calleeAbi` implementation
with zero callee proof invalidation. -/
theorem bridge_thunk_sound
    (callerAbi calleeAbi : PhysicalFnAbi) (thunk : AbiBridgeThunk)
    (sem : List UInt64 → UInt64) (st : CallFrameState) (argVals : List UInt64)
    (hcheck : checkBridgeThunk callerAbi calleeAbi thunk = true)
    (hnodup_caller : callerAbi.args.Nodup)
    (hnodup_callee : calleeAbi.args.Nodup)
    (hlen : callerAbi.args.length = argVals.length) :
    let stOut := execBridgedCall callerAbi calleeAbi thunk sem st argVals
    readPhysLoc stOut callerAbi.ret = sem argVals ∧
    stOut.calleeSaved = st.calleeSaved ∧
    stOut.spOffset = st.spOffset := by
  unfold checkBridgeThunk at hcheck
  rcases thunk with ⟨sArgs, dArgs, sRet, dRet⟩
  have h1 : sArgs = callerAbi.args := by
    revert hcheck; cases h : (sArgs == callerAbi.args) <;> simp_all
  have h2 : dArgs = calleeAbi.args := by
    revert hcheck; cases h : (dArgs == calleeAbi.args) <;> simp_all
  have h3 : sRet = calleeAbi.ret := by
    revert hcheck; cases h : (sRet == calleeAbi.ret) <;> simp_all
  have h4 : dRet = callerAbi.ret := by
    revert hcheck; cases h : (dRet == callerAbi.ret) <;> simp_all
  have h5 : callerAbi.args.length = calleeAbi.args.length := by
    revert hcheck; cases h : (callerAbi.args.length == calleeAbi.args.length) <;> simp_all
  subst h1 h2 h3 h4
  dsimp [execBridgedCall]
  have hdec1 : decodeArgs (encodeArgs st callerAbi.args argVals) callerAbi.args = argVals :=
    decodeArgs_encodeArgs_id st callerAbi.args argVals hnodup_caller hlen
  rw [hdec1]
  have hlen2 : calleeAbi.args.length = argVals.length := by omega
  have hdec2 : decodeArgs (encodeArgs (encodeArgs st callerAbi.args argVals) calleeAbi.args argVals) calleeAbi.args = argVals :=
    decodeArgs_encodeArgs_id _ calleeAbi.args argVals hnodup_callee hlen2
  rw [hdec2]
  rw [readPhysLoc_writePhysLoc_same]
  refine ⟨readPhysLoc_writePhysLoc_same _ _ _, ?_, ?_⟩
  · simp [writePhysLoc_calleeSaved, encodeArgs_calleeSaved]
  · simp [writePhysLoc_spOffset, encodeArgs_spOffset]

/-- Concrete instantiation for `rustc 1.99.1 -> 1.100.0` `i686` `#161583` SSE ABI drift:
- In `1.99.1`, `fn compute_f32_pair(tag: u32, a: f32, b: f64) -> f32` under `CanonAbi::Rust`
  passes `tag` in `EAX` (`.gpr 0`), `a` on stack slot `1` (`[esp+4]`), `b` on stack slot `2`
  (`[esp+8]`), and returns on stack/float slot `0`.
- In `1.100.0` (`#161583`), `CanonAbi::Rust` on `i686` passes `tag` in `EAX` (`.gpr 0`),
  `a` in `XMM0` (`.xmm 0`), `b` in `XMM1` (`.xmm 1`), and returns in `XMM0` (`.xmm 0`). -/
def i686RustAbi_1991_float2 : PhysicalFnAbi := {
  convId := 1991
  args := [.gpr 0, .stack 1, .stack 2]
  ret := .stack 0
  calleePopBytes := 0
  canUnwind := true
}

def i686RustAbi_1100_float2 : PhysicalFnAbi := {
  convId := 1100
  args := [.gpr 0, .xmm 0, .xmm 1]
  ret := .xmm 0
  calleePopBytes := 0
  canUnwind := true
}

def i686FloatThunk_1100_to_1991 : AbiBridgeThunk := {
  srcArgs := [.gpr 0, .xmm 0, .xmm 1]
  dstArgs := [.gpr 0, .stack 1, .stack 2]
  srcRet := .stack 0
  dstRet := .xmm 0
}

theorem i686_1100_to_1991_float_thunk_sound
    (sem : List UInt64 → UInt64) (st : CallFrameState) (v0 v1 v2 : UInt64) :
    let stOut := execBridgedCall i686RustAbi_1100_float2 i686RustAbi_1991_float2
                   i686FloatThunk_1100_to_1991 sem st [v0, v1, v2]
    readPhysLoc stOut i686RustAbi_1100_float2.ret = sem [v0, v1, v2] ∧
    stOut.calleeSaved = st.calleeSaved ∧
    stOut.spOffset = st.spOffset := by
  apply bridge_thunk_sound
  · rfl
  · decide
  · decide
  · rfl

/-- Negative canary: directly calling a `1.99.1` `i686` stack-float callee from a `1.100.0`
`XMM0..XMM1` caller without `AbiBridgeThunk` reads stale stack slots (`0`) instead of `XMM0` (`0x3f800000`). -/
def zeroFrame : CallFrameState := {
  gprs := fun _ => 0
  xmms := fun _ => 0
  stackSlots := fun _ => 0
  calleeSaved := fun _ => 0
  spOffset := 0
}

theorem canary_unbridged_i686_1100_to_1991_corrupts_float_args :
    let sem := fun (xs : List UInt64) => xs.getD 1 0 + xs.getD 2 0
    let stOut := execDirectCall i686RustAbi_1100_float2 i686RustAbi_1991_float2
                   sem zeroFrame [1, 0x3f800000, 0x40000000]
    readPhysLoc stOut i686RustAbi_1100_float2.ret ≠ sem [1, 0x3f800000, 0x40000000] := by
  decide

#print axioms direct_link_sound_of_abi_eq
#print axioms bridge_thunk_sound
#print axioms i686_1100_to_1991_float_thunk_sound
#print axioms canary_unbridged_i686_1100_to_1991_corrupts_float_args

end Anneal.AbiBridge
