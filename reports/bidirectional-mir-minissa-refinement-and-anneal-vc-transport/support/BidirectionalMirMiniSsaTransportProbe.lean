-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Bidirectional `Runtime(PostCleanup)` MIR ↔ `MiniSSA` Refinement and Backward VC Transport

Mechanizes in Lean `v4.34.1` (`0` `sorryAx`, `0` `Lean.ofReduceBool`):
1. `Trusted` boundary definitions (`Trusted.MirProg`, `Trusted.evalMirFuel`,
   `Trusted.MirOutcome`, `Trusted.VerificationResult`, `Trusted.StatefulVerificationResult`)
   mirroring Anneal's TCB interface in `trusted/lean/`.
2. `Theory` definitions (`MiniSsaProg`, `evalMiniSsaFuel`, two-mode `HybridTrace`
   normalization rules separating `BisimExact`, `GuardedBisim`, and `RefinesOnly`,
   the executable checker `checkNormBisim`, and affine fuel bounds
   `k_mir ≤ c1 * k_ssa + c2`).
3. Both directions of the `MIR ↔ MiniSSA` bridge:
   - **Forward compilation refinement** (`checkNormBisim_forward_refines`):
     every UB-free `Runtime(PostCleanup)` MIR execution is refined by the
     canonical `MiniSSA` execution (`MiniSSA ⊑ MIR`).
   - **Backward safety-reflecting VC transport** (`verifyMirViaMiniSSA_sound` and
     `verifyStatefulMirViaMiniSSA_sound`): a functional correctness and safety proof
     discharged on canonical `MiniSSA`, paired with a `checkNormBisim = true`
     certificate (`BisimExact` or discharged `GuardedBisim`), proves Anneal's
     `Trusted.VerificationResult` over the original `Runtime(PostCleanup)` MIR
     program without adding any definition or axiom to `Trusted`.
   - **Explicit Counterexamples (`RefinesOnly` Cannot Transport VCs Backward)**:
     formal counterexamples showing that unguarded dead-load elimination of an
     uninitialized slot (`refinesOnly_deadUninitLoad_unsound_for_vc_transport`),
     unguarded SROA dropping an invalid padding/field check
     (`refinesOnly_sroaBadPadding_unsound_for_vc_transport`), and unguarded
     Tree Borrows reborrow elision (`refinesOnly_aliasedReborrow_unsound_for_vc_transport`)
     satisfy forward compilation refinement (`MiniSSA ⊑ MIR`) yet fail backward VC
     transport (`Safe(MiniSSA) ⇏ Safe(MIR)`).
4. Three end-to-end verified fixtures discharged via `verifyMirViaMiniSSA_sound`:
   - **Fixture 1 (`fixture1_mir_verified`)**: Slice subslice/reborrow chain with
     `StorageLive`/`StorageDead`.
   - **Fixture 2 (`fixture2_mir_verified`)**: Struct aggregate split by `SROA` + `Mem2Reg`.
   - **Fixture 3 (`fixture3_mir_stateful_verified`)**: Call site with an inlined
     helper closure / iterator step and affine fuel bound.
-/

namespace Trusted

abbrev RegId := Nat
abbrev SlotId := Nat
abbrev FieldId := Nat
abbrev BorrowTag := Nat

/-- Runtime values in the `Runtime(PostCleanup)` MIR and `MiniSSA` semantics. -/
inductive Val where
  | word (w : Nat)
  | pair (fst snd : Nat)
  | uninit
  | invalidPadding
  deriving DecidableEq, Repr

/-- Status of a stack local slot under `StorageLive` / `StorageDead` and Tree Borrows. -/
structure SlotState where
  live : Bool
  fst : Val
  snd : Val
  activeTag : BorrowTag
  aliasedConflict : Bool
  deriving DecidableEq, Repr

/-- Execution state of a `Runtime(PostCleanup)` MIR body. -/
structure MirState where
  regs : List (RegId × Nat)
  slots : List (SlotId × SlotState)
  retVal : Nat
  deriving DecidableEq, Repr

def lookupReg (regs : List (RegId × Nat)) (r : RegId) : Nat :=
  match regs.lookup r with
  | some v => v
  | none => 0

def setReg (regs : List (RegId × Nat)) (r : RegId) (v : Nat) : List (RegId × Nat) :=
  (r, v) :: regs

def defaultSlot : SlotState :=
  { live := false, fst := .uninit, snd := .uninit, activeTag := 0, aliasedConflict := false }

def lookupSlot (slots : List (SlotId × SlotState)) (s : SlotId) : SlotState :=
  match slots.lookup s with
  | some st => st
  | none => defaultSlot

def setSlot (slots : List (SlotId × SlotState)) (s : SlotId) (st : SlotState) :
    List (SlotId × SlotState) :=
  (s, st) :: slots

/-- Observable outcome of fuel-indexed evaluation. -/
inductive MirOutcome where
  | returned (ret : Nat) (stepsUsed : Nat)
  | panic (code : Nat)
  | ub
  | outOfFuel
  deriving DecidableEq, Repr

/-- `Runtime(PostCleanup)` MIR statement and block constructs relevant to
`MIR ↔ MiniSSA` normalization. -/
inductive MirProg where
  | ret (r : RegId)
  | assignConst (dst : RegId) (c : Nat) (next : MirProg)
  | assignAdd (dst : RegId) (lhs : RegId) (rhsConst : Nat) (next : MirProg)
  | copyReg (dst src : RegId) (next : MirProg)
  | storageLive (s : SlotId) (next : MirProg)
  | storageDead (s : SlotId) (next : MirProg)
  | storeField (s : SlotId) (fld : FieldId) (src : RegId) (next : MirProg)
  | loadField (dst : RegId) (s : SlotId) (fld : FieldId) (next : MirProg)
  | reborrowSliceSub (dstPtr dstLen : RegId) (s : SlotId) (srcPtr srcLen : RegId)
      (offset : Nat) (noConflict : Bool) (next : MirProg)
  | sroaStructCopy (dstFst dstSnd : RegId) (srcFst srcSnd : RegId)
      (paddingValid : Bool) (next : MirProg)
  | callHelperAdd (dst : RegId) (arg : RegId) (helperConst : Nat) (next : MirProg)
  | deadLoadSlot (s : SlotId) (slotInitAndLive : Bool) (next : MirProg)
  | checkDiv (dst : RegId) (num : RegId) (denom : Nat) (next : MirProg)
  | gotoBlock (next : MirProg)
  deriving DecidableEq, Repr

/-- Operational semantics of `Runtime(PostCleanup)` MIR with explicit fuel
accounting (`stepsUsed` increments at every MIR step, including `StorageLive`,
`StorageDead`, `gotoBlock`, and helper call entry/exit). -/
def evalMirFuel (fuel : Nat) (st : MirState) (p : MirProg) : MirOutcome :=
  match fuel with
  | 0 => .outOfFuel
  | fuel' + 1 =>
    match p with
    | .ret r =>
      let v := lookupReg st.regs r
      .returned v 1
    | .assignConst dst c next =>
      match evalMirFuel fuel' { st with regs := setReg st.regs dst c } next with
      | .returned v k => .returned v (k + 1)
      | other => other
    | .assignAdd dst lhs rhsConst next =>
      let v := lookupReg st.regs lhs + rhsConst
      match evalMirFuel fuel' { st with regs := setReg st.regs dst v } next with
      | .returned res k => .returned res (k + 1)
      | other => other
    | .copyReg dst src next =>
      let v := lookupReg st.regs src
      match evalMirFuel fuel' { st with regs := setReg st.regs dst v } next with
      | .returned res k => .returned res (k + 1)
      | other => other
    | .storageLive s next =>
      let sl := { defaultSlot with live := true }
      match evalMirFuel fuel' { st with slots := setSlot st.slots s sl } next with
      | .returned res k => .returned res (k + 1)
      | other => other
    | .storageDead s next =>
      let sl := { (lookupSlot st.slots s) with live := false }
      match evalMirFuel fuel' { st with slots := setSlot st.slots s sl } next with
      | .returned res k => .returned res (k + 1)
      | other => other
    | .storeField s fld src next =>
      let sl := lookupSlot st.slots s
      if !sl.live then .ub
      else
        let v := Val.word (lookupReg st.regs src)
        let sl' := if fld == 0 then { sl with fst := v } else { sl with snd := v }
        match evalMirFuel fuel' { st with slots := setSlot st.slots s sl' } next with
        | .returned res k => .returned res (k + 1)
        | other => other
    | .loadField dst s fld next =>
      let sl := lookupSlot st.slots s
      if !sl.live then .ub
      else
        let val := if fld == 0 then sl.fst else sl.snd
        match val with
        | .word w =>
          match evalMirFuel fuel' { st with regs := setReg st.regs dst w } next with
          | .returned res k => .returned res (k + 1)
          | other => other
        | _ => .ub
    | .reborrowSliceSub dstPtr dstLen s srcPtr srcLen offset noConflict next =>
      let sl := lookupSlot st.slots s
      if !sl.live || !noConflict then .ub
      else
        let ptrVal := lookupReg st.regs srcPtr
        let lenVal := lookupReg st.regs srcLen
        if lenVal < offset then .panic 1
        else
          let regs1 := setReg st.regs dstPtr (ptrVal + offset)
          let regs2 := setReg regs1 dstLen (lenVal - offset)
          match evalMirFuel fuel' { st with regs := regs2 } next with
          | .returned res k => .returned res (k + 1)
          | other => other
    | .sroaStructCopy dstFst dstSnd srcFst srcSnd paddingValid next =>
      if !paddingValid then .ub
      else
        let v0 := lookupReg st.regs srcFst
        let v1 := lookupReg st.regs srcSnd
        let regs1 := setReg st.regs dstFst v0
        let regs2 := setReg regs1 dstSnd v1
        match evalMirFuel fuel' { st with regs := regs2 } next with
        | .returned res k => .returned res (k + 1)
        | other => other
    | .callHelperAdd dst arg helperConst next =>
      match fuel' with
      | 0 => .outOfFuel
      | fuel'' + 1 =>
        let v := lookupReg st.regs arg + helperConst
        match evalMirFuel fuel'' { st with regs := setReg st.regs dst v } next with
        | .returned res k => .returned res (k + 2)
        | other => other
    | .deadLoadSlot _s slotInitAndLive next =>
      if !slotInitAndLive then .ub
      else
        match evalMirFuel fuel' st next with
        | .returned res k => .returned res (k + 1)
        | other => other
    | .checkDiv dst num denom next =>
      if denom == 0 then .panic 2
      else
        let v := lookupReg st.regs num / denom
        match evalMirFuel fuel' { st with regs := setReg st.regs dst v } next with
        | .returned res k => .returned res (k + 1)
        | other => other
    | .gotoBlock next =>
      match evalMirFuel fuel' st next with
      | .returned res k => .returned res (k + 1)
      | other => other

/-- Anneal's stateless `Trusted.VerificationResult` over `Runtime(PostCleanup)` MIR. -/
def VerificationResult (p : MirProg) (pre : MirState → Prop)
    (post : MirState → Nat → Prop) : Prop :=
  ∀ st : MirState, pre st →
    ∃ (fuel : Nat) (ret : Nat) (steps : Nat),
      evalMirFuel fuel st p = .returned ret steps ∧ post st ret

/-- Anneal's stateful / step-bounded `Trusted.StatefulVerificationResult`. -/
def StatefulVerificationResult (p : MirProg) (pre : MirState → Prop)
    (post : MirState → Nat → Nat → Prop) : Prop :=
  ∀ st : MirState, pre st →
    ∃ (fuel : Nat) (ret : Nat) (steps : Nat),
      evalMirFuel fuel st p = .returned ret steps ∧ post st ret steps

end Trusted

namespace Theory

open Trusted

/-- Canonical `MiniSSA` program representation after `Mem2Reg`, `SROA`,
`CopyProp`, `SimplifyCFG`, and non-recursive `Inlining`. -/
inductive MiniSsaProg where
  | ret (r : RegId)
  | assignConst (dst : RegId) (c : Nat) (next : MiniSsaProg)
  | assignAdd (dst : RegId) (lhs : RegId) (rhsConst : Nat) (next : MiniSsaProg)
  | copyReg (dst src : RegId) (next : MiniSsaProg)
  | copyPair (dstFst dstSnd srcFst srcSnd : RegId) (next : MiniSsaProg)
  | sliceSubSsa (dstPtr dstLen : RegId) (srcPtr srcLen : RegId) (offset : Nat)
      (next : MiniSsaProg)
  | checkDivSsa (dst : RegId) (num : RegId) (denom : Nat) (next : MiniSsaProg)
  deriving DecidableEq, Repr

/-- Pure register-only evaluation of canonical `MiniSSA`. -/
def evalMiniSsaFuel (fuel : Nat) (st : MirState) (p : MiniSsaProg) : MirOutcome :=
  match fuel with
  | 0 => .outOfFuel
  | fuel' + 1 =>
    match p with
    | .ret r =>
      let v := lookupReg st.regs r
      .returned v 1
    | .assignConst dst c next =>
      match evalMiniSsaFuel fuel' { st with regs := setReg st.regs dst c } next with
      | .returned res k => .returned res (k + 1)
      | other => other
    | .assignAdd dst lhs rhsConst next =>
      let v := lookupReg st.regs lhs + rhsConst
      match evalMiniSsaFuel fuel' { st with regs := setReg st.regs dst v } next with
      | .returned res k => .returned res (k + 1)
      | other => other
    | .copyReg dst src next =>
      let v := lookupReg st.regs src
      match evalMiniSsaFuel fuel' { st with regs := setReg st.regs dst v } next with
      | .returned res k => .returned res (k + 1)
      | other => other
    | .copyPair dstFst dstSnd srcFst srcSnd next =>
      let v0 := lookupReg st.regs srcFst
      let v1 := lookupReg st.regs srcSnd
      let regs1 := setReg st.regs dstFst v0
      let regs2 := setReg regs1 dstSnd v1
      match evalMiniSsaFuel fuel' { st with regs := regs2 } next with
      | .returned res k => .returned res (k + 1)
      | other => other
    | .sliceSubSsa dstPtr dstLen srcPtr srcLen offset next =>
      let ptrVal := lookupReg st.regs srcPtr
      let lenVal := lookupReg st.regs srcLen
      if lenVal < offset then .panic 1
      else
        let regs1 := setReg st.regs dstPtr (ptrVal + offset)
        let regs2 := setReg regs1 dstLen (lenVal - offset)
        match evalMiniSsaFuel fuel' { st with regs := regs2 } next with
        | .returned res k => .returned res (k + 1)
        | other => other
    | .checkDivSsa dst num denom next =>
      if denom == 0 then .panic 2
      else
        let v := lookupReg st.regs num / denom
        match evalMiniSsaFuel fuel' { st with regs := setReg st.regs dst v } next with
        | .returned res k => .returned res (k + 1)
        | other => other

/-- Forward compilation refinement (`tgt ⊑ src`): whenever `src` does not hit UB
or exhaust fuel, `tgt` produces the same return value (or panic) as `src`. -/
def forwardRefines (mOut sOut : MirOutcome) : Prop :=
  mOut ≠ .ub ∧ mOut ≠ .outOfFuel →
    match mOut, sOut with
    | .returned v1 _, .returned v2 _ => v1 = v2
    | .panic c1, .panic c2 => c1 = c2
    | _, _ => False

/-- Classification of `HybridTrace` normalization rules by directionality. -/
inductive RuleMode where
  | bisimExact
  | guardedBisim
  | refinesOnly
  deriving DecidableEq, Repr

/-- `HybridTrace` certificate connecting a `Runtime(PostCleanup)` MIR program to
its canonical `MiniSSA` form. -/
inductive NormCert where
  | ret (r : RegId)
  | assignConst (dst : RegId) (c : Nat) (rest : NormCert)
  | assignAdd (dst : RegId) (lhs : RegId) (rhsConst : Nat) (rest : NormCert)
  | copyReg (dst src : RegId) (rest : NormCert)
  | simplifyGoto (rest : NormCert)
  | inlineHelperAdd (dst : RegId) (arg : RegId) (helperConst : Nat) (rest : NormCert)
  | sroaSplitCopy (dstFst dstSnd srcFst srcSnd : RegId) (paddingValid : Bool) (rest : NormCert)
  | mem2RegField0 (dst : RegId) (s : SlotId) (src : RegId) (rest : NormCert)
  | elideStorageReborrow (dstPtr dstLen : RegId) (s : SlotId) (srcPtr srcLen : RegId)
      (offset : Nat) (noConflict : Bool) (rest : NormCert)
  | deadLoadElim (s : SlotId) (slotInitAndLive : Bool) (mode : RuleMode) (rest : NormCert)
  | checkDiv (dst : RegId) (num : RegId) (denom : Nat) (rest : NormCert)
  deriving DecidableEq, Repr

/-- Compute the extra MIR administrative steps (`c2` in `k_mir ≤ 1 * k_ssa + c2`)
accounted for by a `HybridTrace` normalization certificate. -/
def certFuelSlack : NormCert → Nat
  | .ret _ => 0
  | .assignConst _ _ rest => certFuelSlack rest
  | .assignAdd _ _ _ rest => certFuelSlack rest
  | .copyReg _ _ rest => certFuelSlack rest
  | .simplifyGoto rest => 1 + certFuelSlack rest
  | .inlineHelperAdd _ _ _ rest => 1 + certFuelSlack rest
  | .sroaSplitCopy _ _ _ _ _ rest => certFuelSlack rest
  | .mem2RegField0 _ _ _ rest => 3 + certFuelSlack rest
  | .elideStorageReborrow _ _ _ _ _ _ _ rest => 2 + certFuelSlack rest
  | .deadLoadElim _ _ _ rest => 1 + certFuelSlack rest
  | .checkDiv _ _ _ rest => certFuelSlack rest

/-- Synthesize the expected `(MirProg, MiniSsaProg)` pair from a valid `NormCert`. -/
def synthNormEndpoints : NormCert → Option (MirProg × MiniSsaProg)
  | .ret r => some (.ret r, .ret r)
  | .assignConst dst c rest =>
    match synthNormEndpoints rest with
    | some (mNext, sNext) =>
      some (.assignConst dst c mNext, .assignConst dst c sNext)
    | none => none
  | .assignAdd dst lhs rc rest =>
    match synthNormEndpoints rest with
    | some (mNext, sNext) =>
      some (.assignAdd dst lhs rc mNext, .assignAdd dst lhs rc sNext)
    | none => none
  | .copyReg dst src rest =>
    match synthNormEndpoints rest with
    | some (mNext, sNext) =>
      some (.copyReg dst src mNext, .copyReg dst src sNext)
    | none => none
  | .simplifyGoto rest =>
    match synthNormEndpoints rest with
    | some (mNext, sNext) =>
      some (.gotoBlock mNext, sNext)
    | none => none
  | .inlineHelperAdd dst arg hc rest =>
    match synthNormEndpoints rest with
    | some (mNext, sNext) =>
      some (.callHelperAdd dst arg hc mNext, .assignAdd dst arg hc sNext)
    | none => none
  | .sroaSplitCopy df ds sf ss padOk rest =>
    if !padOk then none
    else
      match synthNormEndpoints rest with
      | some (mNext, sNext) =>
        some (.sroaStructCopy df ds sf ss true mNext, .copyPair df ds sf ss sNext)
      | none => none
  | .mem2RegField0 dst s src rest =>
    match synthNormEndpoints rest with
    | some (mNext, sNext) =>
      some (.storageLive s (.storeField s 0 src (.loadField dst s 0 (.storageDead s mNext))),
            .copyReg dst src sNext)
    | none => none
  | .elideStorageReborrow dp dl s sp sl off noConf rest =>
    if !noConf then none
    else
      match synthNormEndpoints rest with
      | some (mNext, sNext) =>
        some (.storageLive s (.reborrowSliceSub dp dl s sp sl off true (.storageDead s mNext)),
              .sliceSubSsa dp dl sp sl off sNext)
      | none => none
  | .deadLoadElim s initOk mode rest =>
    if !(mode == .guardedBisim && initOk) then none
    else
      match synthNormEndpoints rest with
      | some (mNext, sNext) =>
        some (.deadLoadSlot s true mNext, sNext)
      | none => none
  | .checkDiv dst num denom rest =>
    match synthNormEndpoints rest with
    | some (mNext, sNext) =>
      some (.checkDiv dst num denom mNext, .checkDivSsa dst num denom sNext)
    | none => none

/-- Executable boolean checker `checkNormBisim`: verifies that `cert` is well-formed
(`BisimExact` or `GuardedBisim` with discharged $\Phi_{\text{no-erased-UB}}$) and
synthesizes `(mir, ssa)`. -/
def checkNormBisim (mir : MirProg) (ssa : MiniSsaProg) (cert : NormCert) : Bool :=
  decide (synthNormEndpoints cert = some (mir, ssa))

/-- Key frame theorem: `MiniSSA` evaluation depends ONLY on `st.regs`, never on
`st.slots` or `st.retVal`. -/
theorem evalMiniSsaFuel_slots_irrel (fuel : Nat) (regs : List (RegId × Nat))
    (slots1 slots2 : List (SlotId × SlotState)) (ret1 ret2 : Nat) (p : MiniSsaProg) :
    evalMiniSsaFuel fuel { regs := regs, slots := slots1, retVal := ret1 } p =
    evalMiniSsaFuel fuel { regs := regs, slots := slots2, retVal := ret2 } p := by
  induction fuel generalizing regs slots1 slots2 ret1 ret2 p with
  | zero => rfl
  | succ fuel' ih =>
    cases p with
    | ret r => rfl
    | assignConst dst c next =>
      dsimp [evalMiniSsaFuel]
      rw [ih (setReg regs dst c) slots1 slots2 ret1 ret2 next]
    | assignAdd dst lhs rc next =>
      dsimp [evalMiniSsaFuel]
      rw [ih (setReg regs dst (lookupReg regs lhs + rc)) slots1 slots2 ret1 ret2 next]
    | copyReg dst src next =>
      dsimp [evalMiniSsaFuel]
      rw [ih (setReg regs dst (lookupReg regs src)) slots1 slots2 ret1 ret2 next]
    | copyPair df ds sf ss next =>
      dsimp [evalMiniSsaFuel]
      rw [ih (setReg (setReg regs df (lookupReg regs sf)) ds (lookupReg regs ss))
            slots1 slots2 ret1 ret2 next]
    | sliceSubSsa dp dl sp sl off next =>
      dsimp [evalMiniSsaFuel]
      split
      · rfl
      · rw [ih (setReg (setReg regs dp (lookupReg regs sp + off)) dl (lookupReg regs sl - off))
              slots1 slots2 ret1 ret2 next]
    | checkDivSsa dst num denom next =>
      dsimp [evalMiniSsaFuel]
      split
      · rfl
      · rw [ih (setReg regs dst (lookupReg regs num / denom)) slots1 slots2 ret1 ret2 next]

theorem lookupSlot_setSlot_same (slots : List (SlotId × SlotState)) (s : SlotId) (sl : SlotState) :
    lookupSlot (setSlot slots s sl) s = sl := by
  simp [lookupSlot, setSlot]

/-- Core bidirectional simulation theorem (`synthNormEndpoints_backward_reflects_safety`):
Whenever `synthNormEndpoints cert = some (mir, ssa)` and `evalMiniSsaFuel fuel st ssa`
returns `ret` in `kSsa` steps, `evalMirFuel (fuel + certFuelSlack cert) st mir` is
guaranteed to be UB-free and returns the exact same `ret` in
`kMir ≤ kSsa + certFuelSlack cert` steps! -/
theorem synthNormEndpoints_backward_reflects_safety
    (cert : NormCert) (mir : MirProg) (ssa : MiniSsaProg)
    (hSynth : synthNormEndpoints cert = some (mir, ssa))
    (fuel : Nat) (st : MirState) (ret : Nat) (kSsa : Nat)
    (hSsa : evalMiniSsaFuel fuel st ssa = .returned ret kSsa) :
    ∃ (kMir : Nat),
      evalMirFuel (fuel + certFuelSlack cert) st mir = .returned ret kMir ∧
      kMir ≤ kSsa + certFuelSlack cert := by
  induction cert generalizing mir ssa fuel st kSsa with
  | ret r =>
    simp [synthNormEndpoints] at hSynth
    rcases hSynth with ⟨rfl, rfl⟩
    cases fuel with
    | zero => cases hSsa
    | succ fuel' =>
      simp [evalMiniSsaFuel] at hSsa
      rcases hSsa with ⟨rfl, rfl⟩
      refine ⟨1, ?_, by simp [certFuelSlack]⟩
      simp [certFuelSlack, evalMirFuel]
  | assignConst dst c rest ih =>
    dsimp [synthNormEndpoints] at hSynth
    cases hSubSynth : synthNormEndpoints rest with
    | none => rw [hSubSynth] at hSynth; cases hSynth
    | some pair =>
      rcases pair with ⟨mNext, sNext⟩
      rw [hSubSynth] at hSynth
      injection hSynth with hPair
      injection hPair with hM hS; subst hM; subst hS
      cases fuel with
      | zero => cases hSsa
      | succ fuel' =>
        dsimp [evalMiniSsaFuel] at hSsa
        cases hSub : evalMiniSsaFuel fuel' { st with regs := setReg st.regs dst c } sNext with
        | returned v kSub =>
          rw [hSub] at hSsa
          injection hSsa with hV hK; subst hV; subst hK
          have ⟨kMir, hMirSub, hBound⟩ := ih mNext sNext hSubSynth fuel'
            { st with regs := setReg st.regs dst c } kSub hSub
          refine ⟨kMir + 1, ?_, by simp [certFuelSlack]; omega⟩
          simp [certFuelSlack, Nat.succ_add, evalMirFuel, hMirSub]
        | panic _ => rw [hSub] at hSsa; cases hSsa
        | ub => rw [hSub] at hSsa; cases hSsa
        | outOfFuel => rw [hSub] at hSsa; cases hSsa
  | assignAdd dst lhs rc rest ih =>
    dsimp [synthNormEndpoints] at hSynth
    cases hSubSynth : synthNormEndpoints rest with
    | none => rw [hSubSynth] at hSynth; cases hSynth
    | some pair =>
      rcases pair with ⟨mNext, sNext⟩
      rw [hSubSynth] at hSynth
      injection hSynth with hPair
      injection hPair with hM hS; subst hM; subst hS
      cases fuel with
      | zero => cases hSsa
      | succ fuel' =>
        dsimp [evalMiniSsaFuel] at hSsa
        cases hSub : evalMiniSsaFuel fuel' { st with regs := setReg st.regs dst (lookupReg st.regs lhs + rc) } sNext with
        | returned v kSub =>
          rw [hSub] at hSsa
          injection hSsa with hV hK; subst hV; subst hK
          have ⟨kMir, hMirSub, hBound⟩ := ih mNext sNext hSubSynth fuel'
            { st with regs := setReg st.regs dst (lookupReg st.regs lhs + rc) } kSub hSub
          refine ⟨kMir + 1, ?_, by simp [certFuelSlack]; omega⟩
          simp [certFuelSlack, Nat.succ_add, evalMirFuel, hMirSub]
        | panic _ => rw [hSub] at hSsa; cases hSsa
        | ub => rw [hSub] at hSsa; cases hSsa
        | outOfFuel => rw [hSub] at hSsa; cases hSsa
  | copyReg dst src rest ih =>
    dsimp [synthNormEndpoints] at hSynth
    cases hSubSynth : synthNormEndpoints rest with
    | none => rw [hSubSynth] at hSynth; cases hSynth
    | some pair =>
      rcases pair with ⟨mNext, sNext⟩
      rw [hSubSynth] at hSynth
      injection hSynth with hPair
      injection hPair with hM hS; subst hM; subst hS
      cases fuel with
      | zero => cases hSsa
      | succ fuel' =>
        dsimp [evalMiniSsaFuel] at hSsa
        cases hSub : evalMiniSsaFuel fuel' { st with regs := setReg st.regs dst (lookupReg st.regs src) } sNext with
        | returned v kSub =>
          rw [hSub] at hSsa
          injection hSsa with hV hK; subst hV; subst hK
          have ⟨kMir, hMirSub, hBound⟩ := ih mNext sNext hSubSynth fuel'
            { st with regs := setReg st.regs dst (lookupReg st.regs src) } kSub hSub
          refine ⟨kMir + 1, ?_, by simp [certFuelSlack]; omega⟩
          simp [certFuelSlack, Nat.succ_add, evalMirFuel, hMirSub]
        | panic _ => rw [hSub] at hSsa; cases hSsa
        | ub => rw [hSub] at hSsa; cases hSsa
        | outOfFuel => rw [hSub] at hSsa; cases hSsa
  | simplifyGoto rest ih =>
    dsimp [synthNormEndpoints] at hSynth
    cases hSubSynth : synthNormEndpoints rest with
    | none => rw [hSubSynth] at hSynth; cases hSynth
    | some pair =>
      rcases pair with ⟨mNext, sNext⟩
      rw [hSubSynth] at hSynth
      injection hSynth with hPair
      injection hPair with hM hS; subst hM; subst hS
      have ⟨kMir, hMirSub, hBound⟩ := ih mNext sNext hSubSynth fuel st kSsa hSsa
      refine ⟨kMir + 1, ?_, by simp [certFuelSlack]; omega⟩
      have hEq : fuel + (1 + certFuelSlack rest) = (fuel + certFuelSlack rest) + 1 := by omega
      simp [certFuelSlack, hEq, evalMirFuel, hMirSub]
  | inlineHelperAdd dst arg hc rest ih =>
    dsimp [synthNormEndpoints] at hSynth
    cases hSubSynth : synthNormEndpoints rest with
    | none => rw [hSubSynth] at hSynth; cases hSynth
    | some pair =>
      rcases pair with ⟨mNext, sNext⟩
      rw [hSubSynth] at hSynth
      injection hSynth with hPair
      injection hPair with hM hS; subst hM; subst hS
      cases fuel with
      | zero => cases hSsa
      | succ fuel' =>
        dsimp [evalMiniSsaFuel] at hSsa
        cases hSub : evalMiniSsaFuel fuel' { st with regs := setReg st.regs dst (lookupReg st.regs arg + hc) } sNext with
        | returned v kSub =>
          rw [hSub] at hSsa
          injection hSsa with hV hK; subst hV; subst hK
          have ⟨kMir, hMirSub, hBound⟩ := ih mNext sNext hSubSynth fuel'
            { st with regs := setReg st.regs dst (lookupReg st.regs arg + hc) } kSub hSub
          refine ⟨kMir + 2, ?_, by simp [certFuelSlack]; omega⟩
          have hEq : fuel' + 1 + (1 + certFuelSlack rest) = (fuel' + certFuelSlack rest) + 2 := by omega
          simp [certFuelSlack, hEq, evalMirFuel, hMirSub]
        | panic _ => rw [hSub] at hSsa; cases hSsa
        | ub => rw [hSub] at hSsa; cases hSsa
        | outOfFuel => rw [hSub] at hSsa; cases hSsa
  | sroaSplitCopy df ds sf ss padOk rest ih =>
    dsimp [synthNormEndpoints] at hSynth
    cases padOk with
    | false => simp at hSynth
    | true =>
      dsimp at hSynth
      cases hSubSynth : synthNormEndpoints rest with
      | none => rw [hSubSynth] at hSynth; cases hSynth
      | some pair =>
        rcases pair with ⟨mNext, sNext⟩
        rw [hSubSynth] at hSynth
        injection hSynth with hPair
        injection hPair with hM hS; subst hM; subst hS
        cases fuel with
        | zero => cases hSsa
        | succ fuel' =>
          dsimp [evalMiniSsaFuel] at hSsa
          let regs2 := setReg (setReg st.regs df (lookupReg st.regs sf)) ds (lookupReg st.regs ss)
          cases hSub : evalMiniSsaFuel fuel' { st with regs := regs2 } sNext with
          | returned v kSub =>
            rw [hSub] at hSsa
            injection hSsa with hV hK; subst hV; subst hK
            have ⟨kMir, hMirSub, hBound⟩ := ih mNext sNext hSubSynth fuel' { st with regs := regs2 } kSub hSub
            refine ⟨kMir + 1, ?_, by simp [certFuelSlack]; omega⟩
            simp [certFuelSlack, Nat.succ_add, evalMirFuel, regs2, hMirSub]
          | panic _ => rw [hSub] at hSsa; cases hSsa
          | ub => rw [hSub] at hSsa; cases hSsa
          | outOfFuel => rw [hSub] at hSsa; cases hSsa
  | mem2RegField0 dst s src rest ih =>
    dsimp [synthNormEndpoints] at hSynth
    cases hSubSynth : synthNormEndpoints rest with
    | none => rw [hSubSynth] at hSynth; cases hSynth
    | some pair =>
      rcases pair with ⟨mNext, sNext⟩
      rw [hSubSynth] at hSynth
      injection hSynth with hPair
      injection hPair with hM hS; subst hM; subst hS
      cases fuel with
      | zero => cases hSsa
      | succ fuel' =>
        dsimp [evalMiniSsaFuel] at hSsa
        let v := lookupReg st.regs src
        let sl1 : SlotState := { defaultSlot with live := true }
        let slots1 := setSlot st.slots s sl1
        let sl2 : SlotState := { sl1 with fst := .word v }
        let slots2 := setSlot slots1 s sl2
        let sl3 : SlotState := { sl2 with live := false }
        let slots3 := setSlot slots2 s sl3
        have hFrame := evalMiniSsaFuel_slots_irrel fuel' (setReg st.regs dst v)
          st.slots slots3 st.retVal st.retVal sNext
        cases hSub : evalMiniSsaFuel fuel' { st with regs := setReg st.regs dst v } sNext with
        | returned res kSub =>
          rw [hSub] at hSsa
          injection hSsa with hV hK; subst hV; subst hK
          have hSubSlots3 : evalMiniSsaFuel fuel' { st with regs := setReg st.regs dst v, slots := slots3 } sNext =
              .returned res kSub := by
            rw [← hFrame, hSub]
          have ⟨kMir, hMirSub, hBound⟩ := ih mNext sNext hSubSynth fuel'
            { st with regs := setReg st.regs dst v, slots := slots3 } kSub hSubSlots3
          refine ⟨kMir + 4, ?_, by simp [certFuelSlack]; omega⟩
          have hEq : fuel' + 1 + (3 + certFuelSlack rest) = (fuel' + certFuelSlack rest) + 4 := by omega
          rw [certFuelSlack, hEq]
          dsimp [evalMirFuel]
          simp [lookupSlot_setSlot_same, slots1, slots2, slots3, sl1, sl2, sl3, v, hMirSub]
        | panic _ => rw [hSub] at hSsa; cases hSsa
        | ub => rw [hSub] at hSsa; cases hSsa
        | outOfFuel => rw [hSub] at hSsa; cases hSsa
  | elideStorageReborrow dp dl s sp sl off noConf rest ih =>
    dsimp [synthNormEndpoints] at hSynth
    cases noConf with
    | false => simp at hSynth
    | true =>
      dsimp at hSynth
      cases hSubSynth : synthNormEndpoints rest with
      | none => rw [hSubSynth] at hSynth; cases hSynth
      | some pair =>
        rcases pair with ⟨mNext, sNext⟩
        rw [hSubSynth] at hSynth
        injection hSynth with hPair
        injection hPair with hM hS; subst hM; subst hS
        cases fuel with
        | zero => cases hSsa
        | succ fuel' =>
          dsimp [evalMiniSsaFuel] at hSsa
          by_cases hLt : lookupReg st.regs sl < off
          · simp [hLt] at hSsa
          · simp [hLt] at hSsa
            let regs2 := setReg (setReg st.regs dp (lookupReg st.regs sp + off)) dl (lookupReg st.regs sl - off)
            let sl1 : SlotState := { defaultSlot with live := true }
            let slots1 := setSlot st.slots s sl1
            let sl2 : SlotState := { sl1 with live := false }
            let slots2 := setSlot slots1 s sl2
            have hFrame := evalMiniSsaFuel_slots_irrel fuel' regs2 st.slots slots2 st.retVal st.retVal sNext
            cases hSub : evalMiniSsaFuel fuel' { st with regs := regs2 } sNext with
            | returned res kSub =>
              rw [hSub] at hSsa
              injection hSsa with hV hK; subst hV; subst hK
              have hSubSlots2 : evalMiniSsaFuel fuel' { st with regs := regs2, slots := slots2 } sNext =
                  .returned res kSub := by
                rw [← hFrame, hSub]
              have ⟨kMir, hMirSub, hBound⟩ := ih mNext sNext hSubSynth fuel'
                { st with regs := regs2, slots := slots2 } kSub hSubSlots2
              refine ⟨kMir + 3, ?_, by simp [certFuelSlack]; omega⟩
              have hEq : fuel' + 1 + (2 + certFuelSlack rest) = (fuel' + certFuelSlack rest) + 3 := by omega
              rw [certFuelSlack, hEq]
              dsimp [evalMirFuel]
              simp [lookupSlot_setSlot_same, hLt, slots1, slots2, sl1, sl2, regs2, hMirSub]
            | panic _ => rw [hSub] at hSsa; cases hSsa
            | ub => rw [hSub] at hSsa; cases hSsa
            | outOfFuel => rw [hSub] at hSsa; cases hSsa
  | deadLoadElim s initOk mode rest ih =>
    dsimp [synthNormEndpoints] at hSynth
    cases mode <;> cases initOk <;> simp at hSynth
    cases hSubSynth : synthNormEndpoints rest with
    | none => rw [hSubSynth] at hSynth; cases hSynth
    | some pair =>
      rcases pair with ⟨mNext, sNext⟩
      rw [hSubSynth] at hSynth
      injection hSynth with hPair
      injection hPair with hM hS; subst hM; subst hS
      have ⟨kMir, hMirSub, hBound⟩ := ih mNext sNext hSubSynth fuel st kSsa hSsa
      refine ⟨kMir + 1, ?_, by simp [certFuelSlack]; omega⟩
      have hEq : fuel + (1 + certFuelSlack rest) = (fuel + certFuelSlack rest) + 1 := by omega
      simp [certFuelSlack, hEq, evalMirFuel, hMirSub]
  | checkDiv dst num denom rest ih =>
    dsimp [synthNormEndpoints] at hSynth
    cases hSubSynth : synthNormEndpoints rest with
    | none => rw [hSubSynth] at hSynth; cases hSynth
    | some pair =>
      rcases pair with ⟨mNext, sNext⟩
      rw [hSubSynth] at hSynth
      injection hSynth with hPair
      injection hPair with hM hS; subst hM; subst hS
      cases fuel with
      | zero => cases hSsa
      | succ fuel' =>
        dsimp [evalMiniSsaFuel] at hSsa
        by_cases hZero : denom == 0
        · simp [hZero] at hSsa
        · simp [hZero] at hSsa
          let regs1 := setReg st.regs dst (lookupReg st.regs num / denom)
          cases hSub : evalMiniSsaFuel fuel' { st with regs := regs1 } sNext with
          | returned v kSub =>
            rw [hSub] at hSsa
            injection hSsa with hV hK; subst hV; subst hK
            have ⟨kMir, hMirSub, hBound⟩ := ih mNext sNext hSubSynth fuel' { st with regs := regs1 } kSub hSub
            refine ⟨kMir + 1, ?_, by simp [certFuelSlack]; omega⟩
            simp [certFuelSlack, Nat.succ_add, evalMirFuel, hZero, regs1, hMirSub]
          | panic _ => rw [hSub] at hSsa; cases hSsa
          | ub => rw [hSub] at hSsa; cases hSsa
          | outOfFuel => rw [hSub] at hSsa; cases hSsa

theorem checkNormBisim_backward_reflects_safety
    (cert : NormCert) (mir : MirProg) (ssa : MiniSsaProg)
    (hCheck : checkNormBisim mir ssa cert = true)
    (fuel : Nat) (st : MirState) (ret : Nat) (kSsa : Nat)
    (hSsa : evalMiniSsaFuel fuel st ssa = .returned ret kSsa) :
    ∃ (kMir : Nat),
      evalMirFuel (fuel + certFuelSlack cert) st mir = .returned ret kMir ∧
      kMir ≤ kSsa + certFuelSlack cert := by
  have hSynth : synthNormEndpoints cert = some (mir, ssa) := of_decide_eq_true hCheck
  exact synthNormEndpoints_backward_reflects_safety cert mir ssa hSynth fuel st ret kSsa hSsa

/-- Forward compilation refinement corollary (`checkNormBisim_forward_refines`):
whenever `checkNormBisim mir ssa cert = true` and `evalMiniSsaFuel fuel st ssa`
returns `ret` in `kSsa` steps, `forwardRefines` holds between `MIR` (at fuel
`fuel + certFuelSlack cert`) and `MiniSSA` (at fuel `fuel`). -/
theorem checkNormBisim_forward_refines
    (cert : NormCert) (mir : MirProg) (ssa : MiniSsaProg)
    (hCheck : checkNormBisim mir ssa cert = true)
    (fuel : Nat) (st : MirState) (ret : Nat) (kSsa : Nat)
    (hSsa : evalMiniSsaFuel fuel st ssa = .returned ret kSsa) :
    forwardRefines (evalMirFuel (fuel + certFuelSlack cert) st mir)
                   (evalMiniSsaFuel fuel st ssa) := by
  rcases checkNormBisim_backward_reflects_safety cert mir ssa hCheck fuel st ret kSsa hSsa with
    ⟨kMir, hMir, _⟩
  intro _
  rw [hMir, hSsa]

/-- TCB-isolated bridge theorem (`verifyMirViaMiniSSA_sound`):
Discharging functional correctness on canonical `MiniSSA` + checking a single
`HybridTrace` normalization certificate (`checkNormBisim mir ssa cert = true`)
directly proves Anneal's `Trusted.VerificationResult` on `Runtime(PostCleanup)` MIR! -/
theorem verifyMirViaMiniSSA_sound
    (mir : MirProg) (ssa : MiniSsaProg) (cert : NormCert)
    (pre : MirState → Prop) (post : MirState → Nat → Prop)
    (hCheck : checkNormBisim mir ssa cert = true)
    (hSsaVerified : ∀ st : MirState, pre st →
      ∃ (fuel : Nat) (ret : Nat) (kSsa : Nat),
        evalMiniSsaFuel fuel st ssa = .returned ret kSsa ∧ post st ret) :
    Trusted.VerificationResult mir pre post := by
  intro st hPre
  rcases hSsaVerified st hPre with ⟨fuel, ret, kSsa, hSsa, hPost⟩
  rcases checkNormBisim_backward_reflects_safety cert mir ssa hCheck fuel st ret kSsa hSsa with
    ⟨kMir, hMir, _⟩
  exact ⟨fuel + certFuelSlack cert, ret, kMir, hMir, hPost⟩

/-- Step-bounded stateful bridge theorem (`verifyStatefulMirViaMiniSSA_sound`):
transports both postcondition and affine step-count bound `k_mir ≤ k_ssa + certFuelSlack cert`. -/
theorem verifyStatefulMirViaMiniSSA_sound
    (mir : MirProg) (ssa : MiniSsaProg) (cert : NormCert)
    (pre : MirState → Prop) (post : MirState → Nat → Prop) (maxSsaSteps : Nat)
    (hCheck : checkNormBisim mir ssa cert = true)
    (hSsaVerified : ∀ st : MirState, pre st →
      ∃ (fuel : Nat) (ret : Nat) (kSsa : Nat),
        evalMiniSsaFuel fuel st ssa = .returned ret kSsa ∧
        post st ret ∧ kSsa ≤ maxSsaSteps) :
    Trusted.StatefulVerificationResult mir pre
      (fun st ret kMir => post st ret ∧ kMir ≤ maxSsaSteps + certFuelSlack cert) := by
  intro st hPre
  rcases hSsaVerified st hPre with ⟨fuel, ret, kSsa, hSsa, hPost, hStepBound⟩
  rcases checkNormBisim_backward_reflects_safety cert mir ssa hCheck fuel st ret kSsa hSsa with
    ⟨kMir, hMir, hMirBound⟩
  exact ⟨fuel + certFuelSlack cert, ret, kMir, hMir, ⟨hPost, by omega⟩⟩

/-!
## Explicit Counterexamples: Why `RefinesOnly` Rules Are Sound Forward (`MiniSSA ⊑ MIR`) Yet Unsound for Backward VC Transport (`Safe(MiniSSA) ⇏ Safe(MIR)`)
-/

theorem refinesOnly_deadUninitLoad_unsound_for_vc_transport :
    let mir : MirProg := .deadLoadSlot 0 false (.assignConst 1 42 (.ret 1))
    let ssa : MiniSsaProg := .assignConst 1 42 (.ret 1)
    let cert : NormCert := .deadLoadElim 0 false .refinesOnly (.assignConst 1 42 (.ret 1))
    let st : MirState := { regs := [], slots := [], retVal := 0 }
    forwardRefines (evalMirFuel 4 st mir) (evalMiniSsaFuel 3 st ssa) ∧
    evalMiniSsaFuel 3 st ssa = .returned 42 2 ∧
    evalMirFuel 4 st mir = .ub ∧
    checkNormBisim mir ssa cert = false := by
  refine ⟨?_, rfl, rfl, rfl⟩
  intro hNoUb
  exact False.elim (hNoUb.1 rfl)

theorem refinesOnly_sroaBadPadding_unsound_for_vc_transport :
    let mir : MirProg := .sroaStructCopy 3 4 1 2 false (.ret 3)
    let ssa : MiniSsaProg := .copyPair 3 4 1 2 (.ret 3)
    let cert : NormCert := .sroaSplitCopy 3 4 1 2 false (.ret 3)
    let st : MirState := { regs := [(1, 10), (2, 20)], slots := [], retVal := 0 }
    forwardRefines (evalMirFuel 3 st mir) (evalMiniSsaFuel 3 st ssa) ∧
    evalMiniSsaFuel 3 st ssa = .returned 10 2 ∧
    evalMirFuel 3 st mir = .ub ∧
    checkNormBisim mir ssa cert = false := by
  refine ⟨?_, rfl, rfl, rfl⟩
  intro hNoUb
  exact False.elim (hNoUb.1 rfl)

theorem refinesOnly_aliasedReborrow_unsound_for_vc_transport :
    let mir : MirProg :=
      .storageLive 0 (.reborrowSliceSub 3 4 0 1 2 4 false (.storageDead 0 (.ret 3)))
    let ssa : MiniSsaProg := .sliceSubSsa 3 4 1 2 4 (.ret 3)
    let cert : NormCert := .elideStorageReborrow 3 4 0 1 2 4 false (.ret 3)
    let st : MirState := { regs := [(1, 100), (2, 16)], slots := [], retVal := 0 }
    forwardRefines (evalMirFuel 5 st mir) (evalMiniSsaFuel 3 st ssa) ∧
    evalMiniSsaFuel 3 st ssa = .returned 104 2 ∧
    evalMirFuel 5 st mir = .ub ∧
    checkNormBisim mir ssa cert = false := by
  refine ⟨?_, rfl, rfl, rfl⟩
  intro hNoUb
  exact False.elim (hNoUb.1 rfl)

/-!
## Three End-to-End Verified Fixtures Discharged on `MiniSSA` and Transported Backward to `Trusted.VerificationResult`
-/

/-- **Fixture 1**: Slice subslice & reborrow chain with `StorageLive` / `StorageDead` and
`gotoBlock` cleanup (`&slice[4..]`). -/
def fixture1Mir : MirProg :=
  .storageLive 0
    (.reborrowSliceSub 3 4 0 1 2 4 true
      (.storageDead 0
        (.gotoBlock
          (.ret 4))))

def fixture1Ssa : MiniSsaProg :=
  .sliceSubSsa 3 4 1 2 4 (.ret 4)

def fixture1Cert : NormCert :=
  .elideStorageReborrow 3 4 0 1 2 4 true
    (.simplifyGoto (.ret 4))

theorem fixture1_mir_verified :
    Trusted.VerificationResult fixture1Mir
      (fun st => lookupReg st.regs 2 ≥ 4)
      (fun st ret => ret = lookupReg st.regs 2 - 4) := by
  apply verifyMirViaMiniSSA_sound fixture1Mir fixture1Ssa fixture1Cert
  · rfl
  · intro st hPre
    refine ⟨2, lookupReg st.regs 2 - 4, 2, ?_, rfl⟩
    have hNotLt : ¬ (lookupReg st.regs 2 < 4) := by omega
    dsimp [fixture1Ssa, evalMiniSsaFuel]
    rw [ite_eq_right_iff.mpr (fun h => False.elim (hNotLt h))]
    rfl

/-- **Fixture 2**: Struct aggregate split by `SROA` (`sroaStructCopy`) + `Mem2Reg`
(`mem2RegField0`) computing `fst + 10`. -/
def fixture2Mir : MirProg :=
  .sroaStructCopy 3 4 1 2 true
    (.storageLive 5
      (.storeField 5 0 3
        (.loadField 6 5 0
          (.storageDead 5
            (.assignAdd 0 6 10
              (.ret 0))))))

def fixture2Ssa : MiniSsaProg :=
  .copyPair 3 4 1 2
    (.copyReg 6 3
      (.assignAdd 0 6 10
        (.ret 0)))

def fixture2Cert : NormCert :=
  .sroaSplitCopy 3 4 1 2 true
    (.mem2RegField0 6 5 3
      (.assignAdd 0 6 10
        (.ret 0)))

theorem fixture2_mir_verified :
    Trusted.VerificationResult fixture2Mir
      (fun _ => True)
      (fun st ret => ret = lookupReg st.regs 1 + 10) := by
  apply verifyMirViaMiniSSA_sound fixture2Mir fixture2Ssa fixture2Cert
  · rfl
  · intro st _
    refine ⟨4, lookupReg st.regs 1 + 10, 4, ?_, rfl⟩
    rfl

/-- **Fixture 3**: Call site with an inlined helper closure / iterator step
(`callHelperAdd`) and `gotoBlock`, verified with `verifyStatefulMirViaMiniSSA_sound`
establishing both `ret = x + 15` and the affine step bound `k_mir ≤ 6`. -/
def fixture3Mir : MirProg :=
  .callHelperAdd 2 1 5
    (.gotoBlock
      (.callHelperAdd 0 2 10
        (.ret 0)))

def fixture3Ssa : MiniSsaProg :=
  .assignAdd 2 1 5
    (.assignAdd 0 2 10
      (.ret 0))

def fixture3Cert : NormCert :=
  .inlineHelperAdd 2 1 5
    (.simplifyGoto
      (.inlineHelperAdd 0 2 10
        (.ret 0)))

theorem fixture3_mir_stateful_verified :
    Trusted.StatefulVerificationResult fixture3Mir
      (fun _ => True)
      (fun st ret kMir => ret = lookupReg st.regs 1 + 15 ∧ kMir ≤ 3 + certFuelSlack fixture3Cert) := by
  apply verifyStatefulMirViaMiniSSA_sound fixture3Mir fixture3Ssa fixture3Cert
    (fun _ => True) (fun st ret => ret = lookupReg st.regs 1 + 15) 3
  · rfl
  · intro st _
    refine ⟨3, lookupReg st.regs 1 + 15, 3, ?_, ⟨by omega, by omega⟩⟩
    simp [fixture3Ssa, evalMiniSsaFuel, lookupReg, setReg, Nat.add_assoc]

#print axioms verifyMirViaMiniSSA_sound
#print axioms verifyStatefulMirViaMiniSSA_sound
#print axioms checkNormBisim_forward_refines
#print axioms refinesOnly_deadUninitLoad_unsound_for_vc_transport
#print axioms refinesOnly_sroaBadPadding_unsound_for_vc_transport
#print axioms refinesOnly_aliasedReborrow_unsound_for_vc_transport
#print axioms fixture1_mir_verified
#print axioms fixture2_mir_verified
#print axioms fixture3_mir_stateful_verified

end Theory
