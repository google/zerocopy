-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted.MirSemantics
import Iris.Instances.UPred.Instance
import Iris.Instances.IProp.Instance
import Iris.Instances.Lib.FUpd
import Iris.Instances.Lib.GhostVar
import Iris.Instances.Lib.GhostMap
import Iris.Std.HeapInstances
import Iris.ProofMode

/-!
# Round 2 Probe: `iris-lean` `IProp` + `FUpd` Adequacy and IPM Scaling
-/

namespace Anneal.R2IrisLeanProbe

open Iris Iris.BI Iris.Std Iris.ProofMode COFE

/-! ## Part 1: `IProp GF` + `FUpd` Instantiation and Adequacy Bridge -/

/-- Finite map carrier used for Anneal's ghost non-atomic heap
    (`Nat ↦ MirVal`). -/
abbrev HeapMapF := fun V => Std.ExtTreeMap Nat V compare

/-- Concrete `BundledGFunctors` (`Σ` / `GF`) for Anneal's `MirMachine`:
    - Slots `0..3`: `InvGpreS` (invariants, mask tokens, and later credits
      for `FUpd`),
    - Slot `4`: `GhostMapG` over `Nat → Trusted.MirVal` (spatial points-to
      `loc ↦ₘ v`),
    - Slot `5`: `GhostVarG` over `Trusted.MirState` (full state ownership
      when needed). -/
def AnnealGF : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView Nat (Agree (DiscreteO Trusted.MirVal)) HeapMapF),
          by infer_instance⟩
  | 5 => ⟨GhostVarF Trusted.MirState, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance instInvGpreS_AnnealGF : InvGpreS AnnealGF where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    · exists 3

instance instGhostMapG_AnnealGF :
    GhostMapG AnnealGF Nat Trusted.MirVal HeapMapF where
  elem := ⟨4, rfl⟩

instance instGhostVarG_AnnealGF :
    GhostVarG AnnealGF Trusted.MirState where
  elemG := ⟨5, rfl⟩

/-- Non-atomic location ownership invariant in `Trusted.MemState`: location
    `loc` is initialized to `v` and both its last write (`naWriteTs loc`) and
    last read (`naReadTs loc`) are visible in the active thread's coherence
    view (`curView loc`). -/
def OwnLocInMem (mem : Trusted.MemState) (loc : Nat) (v : Trusted.MirVal) : Prop :=
  mem.naVal loc = some v ∧
  mem.naWriteTs loc ≤ mem.curView loc ∧
  mem.naReadTs loc ≤ mem.curView loc

/-- Spatial points-to assertion `loc ↦ₘ[γh]{dq} v` for a non-atomic memory
    location in Anneal's `MemState` inside `IProp GF`. -/
def mirPointsTo {GF : BundledGFunctors}
    [GhostMapG GF Nat Trusted.MirVal HeapMapF]
    (γh : GName) (dq : DFrac) (loc : Nat) (v : Trusted.MirVal) : IProp GF :=
  γh ↪◯MAP[loc]{dq} v

notation loc:50 " ↦ₘ[" γh:50 "]{" dq:50 "} " v:50 => mirPointsTo γh dq loc v
notation loc:50 " ↦ₘ[" γh:50 "] " v:50 => mirPointsTo γh (DFrac.own 1) loc v

/-- Ghost heap state interpretation tying `ghost_map_auth` to
    `MirState.mem`. -/
def mirHeapInterp {GF : BundledGFunctors}
    [GhostMapG GF Nat Trusted.MirVal HeapMapF]
    (γh : GName) (m : HeapMapF Trusted.MirVal) (s : Trusted.MirState) : IProp GF :=
  iprop((γh ↪●MAP m) ∗ ⌜∀ loc v, PartialMap.get? m loc = some v → OwnLocInMem s.mem loc v⌝)

/-- Looking up a spatial `loc ↦ₘ[γh]{dq} v` against `mirHeapInterp` yields the
    pure fact `OwnLocInMem s.mem loc v` (guaranteeing race-free `readNA` and
    `writeNA`) inside `IProp GF`. -/
theorem mirPointsTo_lookup {GF : BundledGFunctors}
    [GhostMapG GF Nat Trusted.MirVal HeapMapF]
    (γh : GName) (m : HeapMapF Trusted.MirVal) (s : Trusted.MirState)
    (loc : Nat) (dq : DFrac) (v : Trusted.MirVal) :
    iprop(mirHeapInterp γh m s ∗ (loc ↦ₘ[γh]{dq} v)) ⊢@{IProp GF}
      ⌜OwnLocInMem s.mem loc v⌝ := by
  unfold mirHeapInterp mirPointsTo
  iintro ⟨⟨Hauth, %Hcoh⟩, Hfrag⟩
  ihave %Hget := ghost_map_lookup $$ Hauth Hfrag
  ipureintro
  exact Hcoh loc v Hget

/-- Two exclusive spatial points-to assertions for the same location `loc` are
    incompatible. -/
theorem mirPointsTo_exclusive {GF : BundledGFunctors}
    [GhostMapG GF Nat Trusted.MirVal HeapMapF]
    (γh : GName) (loc : Nat) (v1 v2 : Trusted.MirVal) :
    iprop((loc ↦ₘ[γh] v1) ∗ (loc ↦ₘ[γh] v2)) ⊢@{IProp GF} False := by
  unfold mirPointsTo
  iintro ⟨H1, H2⟩
  ihave %Hne := ghost_map_elem_ne γh loc loc (.own 1) v1 v2 $$ H1 H2
  ipureintro
  exact Hne rfl

/-- Updating a spatial `loc ↦ₘ[γh] v` against `γh ↪●MAP m` via
    `ghost_map_update` inside `IProp GF`. -/
theorem mirPointsTo_update {GF : BundledGFunctors}
    [GhostMapG GF Nat Trusted.MirVal HeapMapF]
    (γh : GName) (m : HeapMapF Trusted.MirVal)
    (loc : Nat) (v v' : Trusted.MirVal) :
    iprop((γh ↪●MAP m) ∗ (loc ↦ₘ[γh] v)) ⊢@{IProp GF}
      |==> ((γh ↪●MAP PartialMap.insert m loc v') ∗ (loc ↦ₘ[γh] v')) := by
  unfold mirPointsTo
  iintro ⟨Hauth, Hfrag⟩
  iapply ghost_map_update v' $$ Hauth Hfrag

/-! ### Step-Indexed Weakest Precondition (`wpIProp`) with `FUpd` -/

section WpIProp

variable {Prog State Obs Val : Type}
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF]

/-- Fuel-indexed weakest precondition inside `IProp GF` over Anneal's
    `SmallStepMachine`, using `iris-lean`'s step-indexed fancy update
    `|={⊤}[∅]▷=>` (`|={⊤,∅}=> ▷ |={∅,⊤}=>`) at every operational step and
    `|={⊤}=>` at terminal outcomes. -/
def wpIProp
    (M : Trusted.SmallStepMachine Prog State Obs Val)
    (stateInterp : State → List Obs → IProp GF)
    (p : Prog) :
    Nat → State → List Obs → (List Obs → Trusted.PrefixOutcome Val → IProp GF) → IProp GF
  | 0, s, hist, Φ =>
      iprop(stateInterp s hist ={⊤}=∗ (stateInterp s hist ∗ Φ hist .running))
  | k + 1, s, hist, Φ =>
      iprop(⌜∃ r0, M.step p s r0⌝ ∧
        ∀ (r : Trusted.StepResult State Obs Val), ⌜M.step p s r⌝ -∗
          match r with
          | .step obs s' =>
              stateInterp s hist ={⊤}[∅]▷=∗
                (stateInterp s' (hist ++ [obs]) ∗ wpIProp M stateInterp p k s' (hist ++ [obs]) Φ)
          | .choice _ branches =>
              ⌜∃ s0, branches s0⌝ ∧
              ∀ s', ⌜branches s'⌝ -∗
                stateInterp s hist ={⊤}[∅]▷=∗
                  (stateInterp s' hist ∗ wpIProp M stateInterp p k s' hist Φ)
          | .terminated term =>
              stateInterp s hist ={⊤}=∗ (stateInterp s hist ∗ Φ hist (.terminated term))
          | .failed _ =>
              False)

/-- A single fancy update `|={⊤}=> P` entails one step-indexed fancy update
    `|={⊤}[∅]▷=> |={⊤}=> P`. -/
theorem fupd_to_step_fupd {P : IProp GF} :
    (|={⊤}=> P) ⊢@{IProp GF} |={⊤}[∅]▷=> |={⊤}=> P := by
  iintro HP
  imod HP
  imod (fupd_mask_subseteq (E1 := ⊤) (E2 := ∅) LawfulSet.empty_subset) with Hclose
  imodintro
  iintro !>
  imod Hclose
  imodintro
  imodintro
  iexact HP

/-- A fancy update `|={⊤}=> P` can be padded with `n` step-indexed fancy
    updates `|={⊤}[∅]▷=>^[n] |={⊤}=> P` (used when a machine halts before
    exhausting fuel). -/
theorem fupd_to_step_fupdN (n : Nat) {P : IProp GF} :
    (|={⊤}=> P) ⊢@{IProp GF} |={⊤}[∅]▷=>^[n] |={⊤}=> P := by
  induction n with
  | zero => exact .rfl
  | succ n ih =>
    dsimp only [Nat.repeat]
    refine fupd_to_step_fupd.trans ?_
    exact step_fupd_mono ih

/-- Absorb a leading `|={⊤}=>` into `|={⊤}[∅]▷=>^[n] |={⊤}=> P`. -/
theorem fupd_step_fupdN_fupd (n : Nat) {P : IProp GF} :
    (|={⊤}=> |={⊤}[∅]▷=>^[n] |={⊤}=> P) ⊢@{IProp GF} |={⊤}[∅]▷=>^[n] |={⊤}=> P := by
  cases n with
  | zero =>
    dsimp only [Nat.repeat]
    exact BIFUpdate.trans
  | succ n =>
    dsimp only [Nat.repeat]
    iintro H
    imod H
    iexact H

/-- Convert `|={⊤}[∅]▷=>^[n] |={⊤}=> P` into `|={⊤}[∅]▷=>^[n + 1] P` so that
    `Iris.step_fupdN_soundness_close` can discharge all `n + 1` steps and masks
    at once. -/
theorem step_fupdN_fupd_to_succ (n : Nat) {P : IProp GF} :
    (|={⊤}[∅]▷=>^[n] |={⊤}=> P) ⊢@{IProp GF} |={⊤}[∅]▷=>^[n + 1] P := by
  induction n with
  | zero =>
    dsimp only [Nat.repeat]
    iintro HP
    imod HP
    imod (fupd_mask_subseteq (E1 := ⊤) (E2 := ∅) LawfulSet.empty_subset) with Hclose
    imodintro
    iintro !>
    imod Hclose
    imodintro
    iexact HP
  | succ n ih =>
    dsimp only [Nat.repeat]
    exact step_fupd_mono ih

/-- Core preservation lemma: along any reachable prefix
    `ReachesPrefix M p init k s tr out`, combining `stateInterp s hist` with
    `wpIProp` yields `k` nested step-indexed fancy updates
    `|={⊤}[∅]▷=>^[k] |={⊤}=> ⌜out.isSafe ∧ post (hist ++ tr) out⌝`. -/
theorem wpIProp_reachesPrefix
    (M : Trusted.SmallStepMachine Prog State Obs Val)
    (stateInterp : State → List Obs → IProp GF)
    {p : Prog} {init : State}
    {k : Nat} {s : State} {tr : List Obs} {out : Trusted.PrefixOutcome Val}
    (hreach : Trusted.ReachesPrefix M p init k s tr out)
    (hist : List Obs)
    (post : List Obs → Trusted.PrefixOutcome Val → Prop) :
    iprop(stateInterp s hist ∗
      wpIProp M stateInterp p k s hist (fun tr' out' => iprop(⌜post tr' out'⌝))) ⊢@{IProp GF}
      |={⊤}[∅]▷=>^[k] |={⊤}=> ⌜out.isSafe ∧ post (hist ++ tr) out⌝ := by
  induction hreach generalizing hist with
  | zero s =>
    dsimp only [wpIProp, Nat.repeat]
    iintro ⟨Hs, Hwp⟩
    ihave Hupd := Hwp $$ Hs
    imod Hupd with ⟨_, %Hpost⟩
    imodintro
    ipureintro
    simp only [List.append_nil]
    exact ⟨trivial, Hpost⟩
  | step n s s' obs tr out hstep _ ih =>
    dsimp only [wpIProp, Nat.repeat]
    iintro ⟨Hs, Hwp⟩
    icases Hwp with ⟨_, Hwp⟩
    ihave Hstep := Hwp $$ %(.step obs s') %hstep Hs
    iapply step_fupd_wand $$ Hstep
    iintro Hnext
    have ih' := ih (hist ++ [obs])
    rw [List.append_assoc, List.singleton_append] at ih'
    iapply ih' $$ Hnext
  | choice n kind s s' branches tr out hstep hbranch _ ih =>
    dsimp only [wpIProp, Nat.repeat]
    iintro ⟨Hs, Hwp⟩
    icases Hwp with ⟨_, Hwp⟩
    icases Hwp $$ %(.choice kind branches) %hstep with ⟨_, Hbr⟩
    ihave Hstep := Hbr $$ %s' %hbranch Hs
    iapply step_fupd_wand $$ Hstep
    iintro Hnext
    have ih' := ih hist
    iapply ih' $$ Hnext
  | emptyChoice n kind s branches hstep hempty =>
    dsimp only [wpIProp]
    iintro ⟨_, Hwp⟩
    icases Hwp with ⟨_, Hwp⟩
    icases Hwp $$ %(.choice kind branches) %hstep with ⟨%hex, _⟩
    exact False.elim (hempty hex)
  | terminated n s term hstep =>
    dsimp only [wpIProp]
    iintro ⟨Hs, Hwp⟩
    icases Hwp with ⟨_, Hwp⟩
    iapply fupd_to_step_fupdN (n + 1)
    ihave Hupd := Hwp $$ %(.terminated term) %hstep Hs
    imod Hupd with ⟨_, %Hpost⟩
    imodintro
    ipureintro
    simp only [List.append_nil]
    exact ⟨trivial, Hpost⟩
  | failed n s err hstep =>
    dsimp only [wpIProp]
    iintro ⟨_, Hwp⟩
    icases Hwp with ⟨_, Hwp⟩
    icases Hwp $$ %(.failed err) %hstep with ⟨⟩
  | noStep n s hnostep =>
    dsimp only [wpIProp]
    iintro ⟨_, Hwp⟩
    icases Hwp with ⟨%hex, _⟩
    exact False.elim (hnostep hex)

end WpIProp

/-! ### Top-Level Adequacy Theorem: `IProp GF` + `FUpd` to Anneal `SpecOn` -/

/-- Adequacy bridge from `iris-lean`'s `IProp GF` and `FUpd`
    (`Iris.step_fupdN_soundness_close` and `UPred.pure_soundness`) to Anneal's
    pure `Trusted.BehaviorOf M p ≤ M.toLanguage.SpecOn pre post`. -/
theorem wpIProp_adequacy
    {Prog State Obs Val : Type}
    {GF : BundledGFunctors} [InvGpreS GF]
    (M : Trusted.SmallStepMachine Prog State Obs Val)
    (p : Prog)
    (pre : Trusted.ExecQuery State → Prop)
    (post : Trusted.ExecQuery State → Trusted.ExecOut Obs Val → Prop)
    (hwp : ∀ (q : Trusted.ExecQuery State), pre q → M.initState p q.init →
      ∀ [InvGS_gen .hasLC GF],
        ⊢@{IProp GF} |={⊤}=> ∃ (stateInterp : State → List Obs → IProp GF),
          stateInterp q.init [] ∗
          wpIProp M stateInterp p q.steps q.init []
            (fun tr out => iprop(⌜post q ⟨tr, out⟩⌝))) :
    Trusted.BehaviorOf M p ≤ M.toLanguage.SpecOn pre post := by
  intro q hpre
  have hrun : M.initState p q.init → ∀ tr out,
      Trusted.ReachesPrefix M p q.init q.steps q.init tr out →
      out.isSafe ∧ post q ⟨tr, out⟩ := by
    intro hinit_q tr out hreach
    apply UPred.pure_soundness (M := IResUR GF)
    apply Iris.step_fupdN_soundness_close (hlc := .hasLC) (GF := GF) (q.steps + 1) 0
    intro hinv
    iintro _Hcred
    iapply step_fupdN_fupd_to_succ q.steps
    iapply fupd_step_fupdN_fupd q.steps
    ihave Hstart := @hwp q hpre hinit_q hinv
    imod Hstart with ⟨%stateInterp, Hinit⟩
    imodintro
    have Hpres := wpIProp_reachesPrefix (GF := GF) M stateInterp hreach []
      (fun tr' out' => post q ⟨tr', out'⟩)
    simp only [List.nil_append] at Hpres
    iapply Hpres $$ Hinit
  refine ⟨fun hinit_q tr out hreach => (hrun hinit_q tr out hreach).1, ?_⟩
  intro exec ⟨hinit_q, hreach⟩
  exact (hrun hinit_q exec.trace exec.outcome hreach).2

/-! ### `MirMachine` WP Lifting Rules and Verified MIR Canaries -/

section MirWpLifting

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF]

/-- Zero-fuel WP rule for `MirMachine`. -/
theorem wpIProp_mir_zero
    (stateInterp : Trusted.MirState → List Unit → IProp GF)
    (body : Trusted.MirBody) (s : Trusted.MirState) (hist : List Unit)
    (Φ : List Unit → Trusted.PrefixOutcome Trusted.MirVal → IProp GF) :
    iprop(stateInterp s hist ={⊤}=∗ (stateInterp s hist ∗ Φ hist .running)) ⊢@{IProp GF}
      wpIProp Trusted.MirMachine stateInterp body 0 s hist Φ :=
  .rfl

/-- Deterministic single-step WP rule for `MirMachine`: when
    `evalMirStep body s = .step () s'`, proving `wpIProp` at `k + 1` reduces to
    proving the step-indexed fancy update
    `stateInterp s hist ={⊤}[∅]▷=∗ (stateInterp s' (hist ++ [()]) ∗ ...)`. -/
theorem wpIProp_mir_step
    (stateInterp : Trusted.MirState → List Unit → IProp GF)
    (body : Trusted.MirBody) (k : Nat) (s s' : Trusted.MirState) (hist : List Unit)
    (Φ : List Unit → Trusted.PrefixOutcome Trusted.MirVal → IProp GF)
    (hstep : Trusted.evalMirStep body s = .step () s') :
    iprop(stateInterp s hist ={⊤}[∅]▷=∗
      (stateInterp s' (hist ++ [()]) ∗
       wpIProp Trusted.MirMachine stateInterp body k s' (hist ++ [()]) Φ)) ⊢@{IProp GF}
      wpIProp Trusted.MirMachine stateInterp body (k + 1) s hist Φ := by
  dsimp only [wpIProp]
  iintro H
  isplit
  · ipureintro
    exact ⟨.step () s', hstep.symm⟩
  · iintro %r %hr
    have hr' : r = .step () s' := hr.trans hstep
    subst hr'
    iexact H

/-- Deterministic termination WP rule for `MirMachine`: when
    `evalMirStep body s = .terminated term`, proving `wpIProp` at `k + 1`
    reduces to `stateInterp s hist ={⊤}=∗ (stateInterp s hist ∗ Φ ...)`. -/
theorem wpIProp_mir_terminated
    (stateInterp : Trusted.MirState → List Unit → IProp GF)
    (body : Trusted.MirBody) (k : Nat) (s : Trusted.MirState) (hist : List Unit)
    (term : Trusted.TerminationKind Trusted.MirVal)
    (Φ : List Unit → Trusted.PrefixOutcome Trusted.MirVal → IProp GF)
    (hstep : Trusted.evalMirStep body s = .terminated term) :
    iprop(stateInterp s hist ={⊤}=∗ (stateInterp s hist ∗ Φ hist (.terminated term))) ⊢@{IProp GF}
      wpIProp Trusted.MirMachine stateInterp body (k + 1) s hist Φ := by
  dsimp only [wpIProp]
  iintro H
  isplit
  · ipureintro
    exact ⟨.terminated term, hstep.symm⟩
  · iintro %r %hr
    have hr' : r = .terminated term := hr.trans hstep
    subst hr'
    iexact H

end MirWpLifting

/-! ### Canary 1: `idCopyBody` Verified End-to-End via `iris-lean` -/

/-- Canonical `Runtime(PostCleanup)` MIR body for
    `pub fn id(x: usize) -> usize { x }`. -/
def idCopyBody : Trusted.MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.copy ⟨1⟩))]
      terminator := .return_ }
  ]

/-- End-to-end verification of `idCopyBody`
    (`Trusted.MirSem idCopyBody ≤ Trusted.EnsuresEqArg 1`) proved inside
    `iris-lean`'s `IProp AnnealGF` using `GhostVarG` state allocation,
    `wpIProp_mir_step`, `wpIProp_mir_terminated`, and `wpIProp_adequacy`. -/
theorem idCopyBody_verified_via_iris_lean :
    Trusted.MirSem idCopyBody ≤ Trusted.EnsuresEqArg 1 := by
  apply wpIProp_adequacy (GF := AnnealGF) Trusted.MirMachine idCopyBody
  intro q _ hinit hinv
  have hb : q.init.block = 0 := hinit.1
  have hs : q.init.stmtIdx = 0 := hinit.2.1
  obtain ⟨⟨v, hv1, _⟩, _⟩ := hinit.2.2.2
  -- Allocate a ghost variable in `IProp AnnealGF` tracking `MirState`.
  imod (ghost_var_alloc (GF := AnnealGF) q.init) with ⟨%γs, Hγ⟩
  imodintro
  iexists (fun (s : Trusted.MirState) (_ : List Unit) => iprop(γs ↪VAR s))
  iframe Hγ
  let s1 : Trusted.MirState := { q.init with
    locals := Trusted.updateLocal q.init.locals 0 (some v)
    block := 0
    stmtIdx := 1
  }
  have hstep0 : Trusted.evalMirStep idCopyBody q.init = .step () s1 := by
    unfold Trusted.evalMirStep idCopyBody
    rw [hb, hs]
    change (match Trusted.evalOperand q.init.locals (.copy ⟨1⟩) with
      | some (v, locals') =>
          Trusted.StepResult.step () { q.init with
            locals := Trusted.updateLocal locals' 0 (some v)
            stmtIdx := q.init.stmtIdx + 1
          }
      | none => Trusted.StepResult.failed .ub) = _
    dsimp [Trusted.evalOperand]
    rw [hv1, hb, hs]
  have hstep1 : Trusted.evalMirStep idCopyBody s1 = .terminated (.normal v) := rfl
  cases q.steps with
  | zero =>
    iapply wpIProp_mir_zero
    iintro Hγ !>
    iframe Hγ
    ipureintro
    intro _ h; cases h
  | succ k =>
    iapply wpIProp_mir_step _ _ k q.init s1 [] _ hstep0
    iintro Hγ
    imod ghost_var_update s1 γs q.init $$ Hγ with Hγ1
    imod (fupd_mask_subseteq (E1 := ⊤) (E2 := ∅) LawfulSet.empty_subset) with Hclose
    imodintro
    iintro !>
    imod Hclose
    imodintro
    iframe Hγ1
    cases k with
    | zero =>
      iapply wpIProp_mir_zero
      iintro Hγ1 !>
      iframe Hγ1
      ipureintro
      intro _ h; cases h
    | succ k' =>
      iapply wpIProp_mir_terminated _ _ k' s1 ([] ++ [()]) (.normal v) _ hstep1
      iintro Hγ1 !>
      iframe Hγ1
      ipureintro
      intro ret hret
      injection hret with hterm
      injection hterm with hveq
      subst hveq
      exact hv1

/-- `idCopyBody` satisfies baseline `MirLang.WellFormed` via
    `idCopyBody_verified_via_iris_lean`. -/
theorem idCopyBody_wellFormed_via_iris_lean :
    Trusted.MirSem idCopyBody ≤ Trusted.MirLang.WellFormed := by
  intro q htrue
  obtain ⟨hdef, _⟩ := idCopyBody_verified_via_iris_lean q htrue
  exact ⟨hdef, fun _ _ => trivial⟩

/-! ### Canary 2: Mutable-Reference Write + Read via Spatial Points-To -/

/-- MIR body for `pub fn write_read_42(x: &mut usize) -> usize { *x = 42; *x }`:
    ```text
    bb0: {
        (*_1) = const 42_usize;
        _0 = (*_1);
        return;
    }
    ``` -/
def writeRead42Body : Trusted.MirBody where
  argTys := [.refMutUsize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [
        .assignDeref ⟨1⟩ (.constVal (.usize 42)),
        .assign ⟨0⟩ (.deref ⟨1⟩)
      ]
      terminator := .return_ }
  ]

/-- Specification for `writeRead42Body`: well-defined for all valid initial
    states, and any normal return value is `.usize 42`. -/
def EnsuresWriteRead42 : Trusted.MirLang.Behavior :=
  Trusted.MirLang.Spec (fun _ out =>
    ∀ ret, out.outcome = .terminated (.normal ret) → ret = .usize 42)

/-- Helper lemma: `writeNA` succeeds when `OwnLocInMem` holds, and establishes
    `OwnLocInMem` for the newly written value. -/
theorem writeNA_of_ownLocInMem {m : Trusted.MemState} {loc : Nat} {v0 v1 : Trusted.MirVal}
    (hown : OwnLocInMem m loc v0) :
    ∃ m', m.writeNA loc v1 = some m' ∧ OwnLocInMem m' loc v1 := by
  rcases hown with ⟨_, hw, hr⟩
  unfold Trusted.MemState.writeNA
  have hcond : (decide (m.naWriteTs loc ≤ m.curView loc) &&
      decide (m.naReadTs loc ≤ m.curView loc)) = true := by
    simp [hw, hr]
  rw [hcond]
  refine ⟨_, rfl, ?_⟩
  unfold OwnLocInMem Trusted.View.bump
  simp only [beq_self_eq_true, ↓reduceIte]
  refine ⟨trivial, ?_, ?_⟩
  · exact Nat.max_le.mpr ⟨Nat.le_trans hw (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
  · exact Nat.max_le.mpr ⟨Nat.le_trans hr (Nat.le_max_left _ _), Nat.le_max_right _ _⟩

/-- Helper lemma: `readNA` succeeds when `OwnLocInMem` holds, returning the
    owned value and preserving `OwnLocInMem`. -/
theorem readNA_of_ownLocInMem {m : Trusted.MemState} {loc : Nat} {v : Trusted.MirVal}
    (hown : OwnLocInMem m loc v) :
    ∃ m', m.readNA loc = some (v, m') ∧ OwnLocInMem m' loc v := by
  rcases hown with ⟨hval, hw, hr⟩
  unfold Trusted.MemState.readNA
  have hcond : decide (m.naWriteTs loc ≤ m.curView loc) = true := decide_eq_true hw
  rw [hcond, hval]
  refine ⟨_, rfl, ?_⟩
  unfold OwnLocInMem Trusted.View.bump
  simp only [beq_self_eq_true, ↓reduceIte]
  exact ⟨hval, hw, Nat.max_le.mpr ⟨hr, Nat.le_refl _⟩⟩

/-- End-to-end verification of `writeRead42Body`
    (`MirSem writeRead42Body ≤ EnsuresWriteRead42`) using spatial points-to
    assertions `loc ↦ₘ[γh] v` (`GhostMapG`) in `IProp AnnealGF`. -/
theorem writeRead42Body_verified_via_iris_lean :
    Trusted.MirSem writeRead42Body ≤ EnsuresWriteRead42 := by
  apply wpIProp_adequacy (GF := AnnealGF) Trusted.MirMachine writeRead42Body
  intro q _ hinit hinv
  have hb : q.init.block = 0 := hinit.1
  have hs : q.init.stmtIdx = 0 := hinit.2.1
  obtain ⟨⟨vArg, hv1, hvalid⟩, _⟩ := hinit.2.2.2
  have hty : vArg.hasTy q.init.mem .refMutUsize := hvalid.1
  cases vArg with
  | usize _ | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | ordering _ =>
    cases hty
  | refMutLoc loc =>
    obtain ⟨n0, hnaVal, hnaW, hnaR⟩ := hty
    have hown0 : OwnLocInMem q.init.mem loc (.usize n0) := ⟨hnaVal, hnaW, hnaR⟩
    -- Allocate the spatial ghost heap map and insert `loc ↦ₘ (.usize n0)`.
    imod (ghost_map_alloc_empty (GF := AnnealGF) (K := Nat) (V := Trusted.MirVal) (H := HeapMapF))
      with ⟨%γh, Hauth0⟩
    have hget_empty : PartialMap.get? (∅ : HeapMapF Trusted.MirVal) loc = none :=
      LawfulPartialMap.get?_empty loc
    imod ghost_map_insert loc (.usize n0) hget_empty $$ Hauth0 with ⟨Hauth1, Hpts0⟩
    -- Allocate a ghost variable tracking exact state equality for locals/PC.
    imod (ghost_var_alloc (GF := AnnealGF) q.init) with ⟨%γs, Hγs⟩
    imodintro
    -- Our state interpretation bundles the authoritative ghost heap map and
    -- the ghost state variable.
    let m0 : HeapMapF Trusted.MirVal := PartialMap.insert (∅ : HeapMapF Trusted.MirVal) loc (.usize n0)
    let stateInterp : Trusted.MirState → List Unit → IProp AnnealGF :=
      fun s _ => iprop(
        (∃ m : HeapMapF Trusted.MirVal, (γh ↪●MAP m) ∗
          ⌜∀ v, PartialMap.get? m loc = some v → OwnLocInMem s.mem loc v⌝) ∗
        (γs ↪VAR s))
    iexists stateInterp
    dsimp only [stateInterp]
    have hm0_coh : ∀ v,
        PartialMap.get? m0 loc = some v → OwnLocInMem q.init.mem loc v := by
      intro v hget
      rw [LawfulPartialMap.get?_insert_eq rfl] at hget
      injection hget with hveq
      subst hveq
      exact hown0
    isplitl [Hauth1 Hγs]
    · iframe Hγs
      iexists m0
      iframe Hauth1
      ipureintro
      exact hm0_coh
    -- Verify the 3-step execution using `Hpts0 : loc ↦ₘ[γh] (.usize n0)`.
    obtain ⟨mem1, hwrite1, hown1⟩ := writeNA_of_ownLocInMem (v1 := .usize 42) hown0
    let s1 : Trusted.MirState := { q.init with
      locals := q.init.locals
      mem := mem1
      block := 0
      stmtIdx := 1
    }
    have hstep0 : Trusted.evalMirStep writeRead42Body q.init = .step () s1 := by
      unfold Trusted.evalMirStep writeRead42Body
      rw [hb, hs]
      change (match Trusted.evalOperand q.init.locals (.constVal (.usize 42)) with
        | none => Trusted.StepResult.failed .ub
        | some (v, locals1) =>
          match locals1 1 with
          | some (.refMutLoc l) =>
            match q.init.mem.writeNA l v with
            | some m' => Trusted.StepResult.step () { q.init with
                locals := locals1
                mem := m'
                stmtIdx := q.init.stmtIdx + 1
              }
            | none => Trusted.StepResult.failed .ub
          | _ => Trusted.StepResult.failed .ub) = _
      dsimp [Trusted.evalOperand]
      rw [hv1]
      dsimp only
      rw [hwrite1, hb, hs]
    obtain ⟨mem2, hread2, hown2⟩ := readNA_of_ownLocInMem hown1
    let s2 : Trusted.MirState := { s1 with
      locals := Trusted.updateLocal s1.locals 0 (some (.usize 42))
      mem := mem2
      block := 0
      stmtIdx := 2
    }
    have hstep1 : Trusted.evalMirStep writeRead42Body s1 = .step () s2 := by
      unfold Trusted.evalMirStep writeRead42Body
      change (match s1.locals 1 with
        | some (.refMutLoc l) | some (.refSharedLoc l) =>
          match s1.mem.readNA l with
          | some (v, m') => Trusted.StepResult.step () { s1 with
              locals := Trusted.updateLocal s1.locals 0 (some v)
              mem := m'
              stmtIdx := s1.stmtIdx + 1
            }
          | none => Trusted.StepResult.failed .ub
        | _ => Trusted.StepResult.failed .ub) = _
      change (match q.init.locals 1 with
        | some (.refMutLoc l) | some (.refSharedLoc l) =>
          match mem1.readNA l with
          | some (v, m') => Trusted.StepResult.step () { s1 with
              locals := Trusted.updateLocal s1.locals 0 (some v)
              mem := m'
              stmtIdx := 2
            }
          | none => Trusted.StepResult.failed .ub
        | _ => Trusted.StepResult.failed .ub) = _
      rw [hv1]
      dsimp only
      rw [hread2]
    have hstep2 : Trusted.evalMirStep writeRead42Body s2 = .terminated (.normal (.usize 42)) := rfl
    cases q.steps with
    | zero =>
      iapply wpIProp_mir_zero
      iintro Hsi !>
      iframe Hsi
      ipureintro
      intro _ h; cases h
    | succ k1 =>
      iapply wpIProp_mir_step _ _ k1 q.init s1 [] _ hstep0
      iintro ⟨⟨%m, Hauth, %_⟩, Hγs⟩
      -- Update `loc ↦ₘ[γh] (.usize n0)` to `loc ↦ₘ[γh] (.usize 42)`.
      imod ghost_map_update (.usize 42) $$ Hauth Hpts0 with ⟨Hauth1', Hpts1⟩
      imod ghost_var_update s1 γs q.init $$ Hγs with Hγs1
      imod (fupd_mask_subseteq (E1 := ⊤) (E2 := ∅) LawfulSet.empty_subset) with Hclose
      imodintro
      iintro !>
      imod Hclose
      imodintro
      have hm1_coh : ∀ v,
          PartialMap.get? (PartialMap.insert m loc (.usize 42)) loc = some v →
          OwnLocInMem s1.mem loc v := by
        intro v hget
        rw [LawfulPartialMap.get?_insert_eq rfl] at hget
        injection hget with hveq
        subst hveq
        exact hown1
      isplitr [Hpts1]
      · iframe Hγs1
        iexists (PartialMap.insert m loc (.usize 42))
        iframe Hauth1'
        ipureintro
        exact hm1_coh
      · cases k1 with
        | zero =>
          iapply wpIProp_mir_zero
          iintro Hsi !>
          iframe Hsi
          ipureintro
          intro _ h; cases h
        | succ k2 =>
          iapply wpIProp_mir_step _ _ k2 s1 s2 ([] ++ [()]) _ hstep1
          iintro ⟨⟨%m', Hauth', %hcoh'⟩, Hγs1⟩
          -- Use `ghost_map_lookup` on `Hpts1 : loc ↦ₘ[γh] (.usize 42)` to prove
          -- `OwnLocInMem s1.mem loc (.usize 42)`.
          ihave %hget42 := ghost_map_lookup $$ Hauth' Hpts1
          have _hown42 : OwnLocInMem s1.mem loc (.usize 42) := hcoh' (.usize 42) hget42
          imod ghost_var_update s2 γs s1 $$ Hγs1 with Hγs2
          imod (fupd_mask_subseteq (E1 := ⊤) (E2 := ∅) LawfulSet.empty_subset) with Hclose2
          imodintro
          iintro !>
          imod Hclose2
          imodintro
          have hm2_coh : ∀ v,
              PartialMap.get? m' loc = some v → OwnLocInMem s2.mem loc v := by
            intro v hget
            rw [hget42] at hget
            injection hget with hveq
            subst hveq
            exact hown2
          isplitr [Hpts1]
          · iframe Hγs2
            iexists m'
            iframe Hauth'
            ipureintro
            exact hm2_coh
          · cases k2 with
            | zero =>
              iapply wpIProp_mir_zero
              iintro Hsi !>
              iframe Hsi
              ipureintro
              intro _ h; cases h
            | succ k3 =>
              iapply wpIProp_mir_terminated _ _ k3 s2 (([] ++ [()]) ++ [()]) (.normal (.usize 42)) _ hstep2
              iintro Hsi !>
              iframe Hsi
              ipureintro
              intro ret hret
              injection hret with hterm
              injection hterm with hveq
              exact hveq.symm

/-- `writeRead42Body` satisfies baseline `MirLang.WellFormed`. -/
theorem writeRead42Body_wellFormed_via_iris_lean :
    Trusted.MirSem writeRead42Body ≤ Trusted.MirLang.WellFormed := by
  intro q htrue
  obtain ⟨hdef, _⟩ := writeRead42Body_verified_via_iris_lean q htrue
  exact ⟨hdef, fun _ _ => trivial⟩

#print axioms wpIProp_adequacy
#print axioms idCopyBody_verified_via_iris_lean
#print axioms writeRead42Body_verified_via_iris_lean

/-! ## Part 2: `iris-lean` IPM Framing Scaling Benchmark ($N = 5..40$) -/

section BenchmarkHarness

open Lean Elab Command Meta

/-- Custom command wrapper that elaborates `cmd`, measures wall-clock time (ms)
    and heartbeats, and inspects the resulting declaration `declId` in the
    kernel environment to report proof term DAG size (`Expr.numObjs`) and depth
    (`Expr.approxDepth`). -/
elab "measure_decl " declId:ident cmd:command : command => do
  let t0 ← IO.monoNanosNow
  let hb0 ← IO.getNumHeartbeats
  elabCommand cmd
  let hb1 ← IO.getNumHeartbeats
  let t1 ← IO.monoNanosNow
  let env ← getEnv
  let fullName := (← getCurrNamespace) ++ declId.getId
  let (numObjs, depth) ← match env.find? fullName with
    | some cinfo =>
      match cinfo.value? (allowOpaque := true) with
      | some v =>
        let n ← liftIO v.numObjs
        pure (n, v.approxDepth.toNat)
      | none => pure (0, 0)
    | none => pure (0, 0)
  let ms100 := (t1 - t0) / 10000
  let msWhole := ms100 / 100
  let msFrac := ms100 % 100
  let hbDiff := hb1 - hb0
  logInfo m!"BENCHMARK | {declId.getId} | time={msWhole}.{msFrac}ms | heartbeats={hbDiff} | numObjs={numObjs} | depth={depth}"

end BenchmarkHarness

section IpmBenchmarks

variable (γ : GName) (v w : Trusted.MirVal)

/-! ### Family 1: In-Order `iintro` + `iframe` ($N = 5, 10, 20, 40$) -/

measure_decl bench_iframe_inorder_5
theorem bench_iframe_inorder_5 :
    ⊢@{IProp AnnealGF}
      ((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v)) -∗
      ((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v)) := by
  iintro ⟨H1, H2, H3, H4, H5⟩
  iframe

measure_decl bench_iframe_inorder_10
theorem bench_iframe_inorder_10 :
    ⊢@{IProp AnnealGF}
      ((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v) ∗
       (6 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v) ∗ (10 ↦ₘ[γ] v)) -∗
      ((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v) ∗
       (6 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v) ∗ (10 ↦ₘ[γ] v)) := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  iframe

measure_decl bench_iframe_inorder_20
theorem bench_iframe_inorder_20 :
    ⊢@{IProp AnnealGF}
      ((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v) ∗
       (6 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v) ∗ (10 ↦ₘ[γ] v) ∗
       (11 ↦ₘ[γ] v) ∗ (12 ↦ₘ[γ] v) ∗ (13 ↦ₘ[γ] v) ∗ (14 ↦ₘ[γ] v) ∗ (15 ↦ₘ[γ] v) ∗
       (16 ↦ₘ[γ] v) ∗ (17 ↦ₘ[γ] v) ∗ (18 ↦ₘ[γ] v) ∗ (19 ↦ₘ[γ] v) ∗ (20 ↦ₘ[γ] v)) -∗
      ((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v) ∗
       (6 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v) ∗ (10 ↦ₘ[γ] v) ∗
       (11 ↦ₘ[γ] v) ∗ (12 ↦ₘ[γ] v) ∗ (13 ↦ₘ[γ] v) ∗ (14 ↦ₘ[γ] v) ∗ (15 ↦ₘ[γ] v) ∗
       (16 ↦ₘ[γ] v) ∗ (17 ↦ₘ[γ] v) ∗ (18 ↦ₘ[γ] v) ∗ (19 ↦ₘ[γ] v) ∗ (20 ↦ₘ[γ] v)) := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10,
          H11, H12, H13, H14, H15, H16, H17, H18, H19, H20⟩
  iframe

measure_decl bench_iframe_inorder_40
theorem bench_iframe_inorder_40 :
    ⊢@{IProp AnnealGF}
      ((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v) ∗
       (6 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v) ∗ (10 ↦ₘ[γ] v) ∗
       (11 ↦ₘ[γ] v) ∗ (12 ↦ₘ[γ] v) ∗ (13 ↦ₘ[γ] v) ∗ (14 ↦ₘ[γ] v) ∗ (15 ↦ₘ[γ] v) ∗
       (16 ↦ₘ[γ] v) ∗ (17 ↦ₘ[γ] v) ∗ (18 ↦ₘ[γ] v) ∗ (19 ↦ₘ[γ] v) ∗ (20 ↦ₘ[γ] v) ∗
       (21 ↦ₘ[γ] v) ∗ (22 ↦ₘ[γ] v) ∗ (23 ↦ₘ[γ] v) ∗ (24 ↦ₘ[γ] v) ∗ (25 ↦ₘ[γ] v) ∗
       (26 ↦ₘ[γ] v) ∗ (27 ↦ₘ[γ] v) ∗ (28 ↦ₘ[γ] v) ∗ (29 ↦ₘ[γ] v) ∗ (30 ↦ₘ[γ] v) ∗
       (31 ↦ₘ[γ] v) ∗ (32 ↦ₘ[γ] v) ∗ (33 ↦ₘ[γ] v) ∗ (34 ↦ₘ[γ] v) ∗ (35 ↦ₘ[γ] v) ∗
       (36 ↦ₘ[γ] v) ∗ (37 ↦ₘ[γ] v) ∗ (38 ↦ₘ[γ] v) ∗ (39 ↦ₘ[γ] v) ∗ (40 ↦ₘ[γ] v)) -∗
      ((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v) ∗
       (6 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v) ∗ (10 ↦ₘ[γ] v) ∗
       (11 ↦ₘ[γ] v) ∗ (12 ↦ₘ[γ] v) ∗ (13 ↦ₘ[γ] v) ∗ (14 ↦ₘ[γ] v) ∗ (15 ↦ₘ[γ] v) ∗
       (16 ↦ₘ[γ] v) ∗ (17 ↦ₘ[γ] v) ∗ (18 ↦ₘ[γ] v) ∗ (19 ↦ₘ[γ] v) ∗ (20 ↦ₘ[γ] v) ∗
       (21 ↦ₘ[γ] v) ∗ (22 ↦ₘ[γ] v) ∗ (23 ↦ₘ[γ] v) ∗ (24 ↦ₘ[γ] v) ∗ (25 ↦ₘ[γ] v) ∗
       (26 ↦ₘ[γ] v) ∗ (27 ↦ₘ[γ] v) ∗ (28 ↦ₘ[γ] v) ∗ (29 ↦ₘ[γ] v) ∗ (30 ↦ₘ[γ] v) ∗
       (31 ↦ₘ[γ] v) ∗ (32 ↦ₘ[γ] v) ∗ (33 ↦ₘ[γ] v) ∗ (34 ↦ₘ[γ] v) ∗ (35 ↦ₘ[γ] v) ∗
       (36 ↦ₘ[γ] v) ∗ (37 ↦ₘ[γ] v) ∗ (38 ↦ₘ[γ] v) ∗ (39 ↦ₘ[γ] v) ∗ (40 ↦ₘ[γ] v)) := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10,
          H11, H12, H13, H14, H15, H16, H17, H18, H19, H20,
          H21, H22, H23, H24, H25, H26, H27, H28, H29, H30,
          H31, H32, H33, H34, H35, H36, H37, H38, H39, H40⟩
  iframe

/-! ### Family 2: Reverse-Order `iintro` + `iframe` ($N = 5, 10, 20, 40$) -/

measure_decl bench_iframe_rev_5
theorem bench_iframe_rev_5 :
    ⊢@{IProp AnnealGF}
      ((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v)) -∗
      ((5 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (1 ↦ₘ[γ] v)) := by
  iintro ⟨H1, H2, H3, H4, H5⟩
  iframe

measure_decl bench_iframe_rev_10
theorem bench_iframe_rev_10 :
    ⊢@{IProp AnnealGF}
      ((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v) ∗
       (6 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v) ∗ (10 ↦ₘ[γ] v)) -∗
      ((10 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (6 ↦ₘ[γ] v) ∗
       (5 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (1 ↦ₘ[γ] v)) := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  iframe

measure_decl bench_iframe_rev_20
theorem bench_iframe_rev_20 :
    ⊢@{IProp AnnealGF}
      ((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v) ∗
       (6 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v) ∗ (10 ↦ₘ[γ] v) ∗
       (11 ↦ₘ[γ] v) ∗ (12 ↦ₘ[γ] v) ∗ (13 ↦ₘ[γ] v) ∗ (14 ↦ₘ[γ] v) ∗ (15 ↦ₘ[γ] v) ∗
       (16 ↦ₘ[γ] v) ∗ (17 ↦ₘ[γ] v) ∗ (18 ↦ₘ[γ] v) ∗ (19 ↦ₘ[γ] v) ∗ (20 ↦ₘ[γ] v)) -∗
      ((20 ↦ₘ[γ] v) ∗ (19 ↦ₘ[γ] v) ∗ (18 ↦ₘ[γ] v) ∗ (17 ↦ₘ[γ] v) ∗ (16 ↦ₘ[γ] v) ∗
       (15 ↦ₘ[γ] v) ∗ (14 ↦ₘ[γ] v) ∗ (13 ↦ₘ[γ] v) ∗ (12 ↦ₘ[γ] v) ∗ (11 ↦ₘ[γ] v) ∗
       (10 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (6 ↦ₘ[γ] v) ∗
       (5 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (1 ↦ₘ[γ] v)) := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10,
          H11, H12, H13, H14, H15, H16, H17, H18, H19, H20⟩
  iframe

measure_decl bench_iframe_rev_40
theorem bench_iframe_rev_40 :
    ⊢@{IProp AnnealGF}
      ((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v) ∗
       (6 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v) ∗ (10 ↦ₘ[γ] v) ∗
       (11 ↦ₘ[γ] v) ∗ (12 ↦ₘ[γ] v) ∗ (13 ↦ₘ[γ] v) ∗ (14 ↦ₘ[γ] v) ∗ (15 ↦ₘ[γ] v) ∗
       (16 ↦ₘ[γ] v) ∗ (17 ↦ₘ[γ] v) ∗ (18 ↦ₘ[γ] v) ∗ (19 ↦ₘ[γ] v) ∗ (20 ↦ₘ[γ] v) ∗
       (21 ↦ₘ[γ] v) ∗ (22 ↦ₘ[γ] v) ∗ (23 ↦ₘ[γ] v) ∗ (24 ↦ₘ[γ] v) ∗ (25 ↦ₘ[γ] v) ∗
       (26 ↦ₘ[γ] v) ∗ (27 ↦ₘ[γ] v) ∗ (28 ↦ₘ[γ] v) ∗ (29 ↦ₘ[γ] v) ∗ (30 ↦ₘ[γ] v) ∗
       (31 ↦ₘ[γ] v) ∗ (32 ↦ₘ[γ] v) ∗ (33 ↦ₘ[γ] v) ∗ (34 ↦ₘ[γ] v) ∗ (35 ↦ₘ[γ] v) ∗
       (36 ↦ₘ[γ] v) ∗ (37 ↦ₘ[γ] v) ∗ (38 ↦ₘ[γ] v) ∗ (39 ↦ₘ[γ] v) ∗ (40 ↦ₘ[γ] v)) -∗
      ((40 ↦ₘ[γ] v) ∗ (39 ↦ₘ[γ] v) ∗ (38 ↦ₘ[γ] v) ∗ (37 ↦ₘ[γ] v) ∗ (36 ↦ₘ[γ] v) ∗
       (35 ↦ₘ[γ] v) ∗ (34 ↦ₘ[γ] v) ∗ (33 ↦ₘ[γ] v) ∗ (32 ↦ₘ[γ] v) ∗ (31 ↦ₘ[γ] v) ∗
       (30 ↦ₘ[γ] v) ∗ (29 ↦ₘ[γ] v) ∗ (28 ↦ₘ[γ] v) ∗ (27 ↦ₘ[γ] v) ∗ (26 ↦ₘ[γ] v) ∗
       (25 ↦ₘ[γ] v) ∗ (24 ↦ₘ[γ] v) ∗ (23 ↦ₘ[γ] v) ∗ (22 ↦ₘ[γ] v) ∗ (21 ↦ₘ[γ] v) ∗
       (20 ↦ₘ[γ] v) ∗ (19 ↦ₘ[γ] v) ∗ (18 ↦ₘ[γ] v) ∗ (17 ↦ₘ[γ] v) ∗ (16 ↦ₘ[γ] v) ∗
       (15 ↦ₘ[γ] v) ∗ (14 ↦ₘ[γ] v) ∗ (13 ↦ₘ[γ] v) ∗ (12 ↦ₘ[γ] v) ∗ (11 ↦ₘ[γ] v) ∗
       (10 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (6 ↦ₘ[γ] v) ∗
       (5 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (1 ↦ₘ[γ] v)) := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10,
          H11, H12, H13, H14, H15, H16, H17, H18, H19, H20,
          H21, H22, H23, H24, H25, H26, H27, H28, H29, H30,
          H31, H32, H33, H34, H35, H36, H37, H38, H39, H40⟩
  iframe

/-! ### Family 3: Single-Step `iintro` + `isplitr` + `iframe` + `iapply` -/

measure_decl bench_step_split_apply_5
theorem bench_step_split_apply_5 :
    ⊢@{IProp AnnealGF}
      ((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v)) -∗
      ((5 ↦ₘ[γ] v) -∗ (5 ↦ₘ[γ] w)) -∗
      (((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v)) ∗ (5 ↦ₘ[γ] w)) := by
  iintro ⟨H1, H2, H3, H4, H5⟩ Hstep
  isplitr [H5 Hstep]
  · iframe
  · iapply Hstep $$ H5

measure_decl bench_step_split_apply_10
theorem bench_step_split_apply_10 :
    ⊢@{IProp AnnealGF}
      ((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v) ∗
       (6 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v) ∗ (10 ↦ₘ[γ] v)) -∗
      ((10 ↦ₘ[γ] v) -∗ (10 ↦ₘ[γ] w)) -∗
      (((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v) ∗
        (6 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v)) ∗ (10 ↦ₘ[γ] w)) := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩ Hstep
  isplitr [H10 Hstep]
  · iframe
  · iapply Hstep $$ H10

measure_decl bench_step_split_apply_20
theorem bench_step_split_apply_20 :
    ⊢@{IProp AnnealGF}
      ((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v) ∗
       (6 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v) ∗ (10 ↦ₘ[γ] v) ∗
       (11 ↦ₘ[γ] v) ∗ (12 ↦ₘ[γ] v) ∗ (13 ↦ₘ[γ] v) ∗ (14 ↦ₘ[γ] v) ∗ (15 ↦ₘ[γ] v) ∗
       (16 ↦ₘ[γ] v) ∗ (17 ↦ₘ[γ] v) ∗ (18 ↦ₘ[γ] v) ∗ (19 ↦ₘ[γ] v) ∗ (20 ↦ₘ[γ] v)) -∗
      ((20 ↦ₘ[γ] v) -∗ (20 ↦ₘ[γ] w)) -∗
      (((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v) ∗
        (6 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v) ∗ (10 ↦ₘ[γ] v) ∗
        (11 ↦ₘ[γ] v) ∗ (12 ↦ₘ[γ] v) ∗ (13 ↦ₘ[γ] v) ∗ (14 ↦ₘ[γ] v) ∗ (15 ↦ₘ[γ] v) ∗
        (16 ↦ₘ[γ] v) ∗ (17 ↦ₘ[γ] v) ∗ (18 ↦ₘ[γ] v) ∗ (19 ↦ₘ[γ] v)) ∗ (20 ↦ₘ[γ] w)) := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10,
          H11, H12, H13, H14, H15, H16, H17, H18, H19, H20⟩ Hstep
  isplitr [H20 Hstep]
  · iframe
  · iapply Hstep $$ H20

measure_decl bench_step_split_apply_40
theorem bench_step_split_apply_40 :
    ⊢@{IProp AnnealGF}
      ((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v) ∗
       (6 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v) ∗ (10 ↦ₘ[γ] v) ∗
       (11 ↦ₘ[γ] v) ∗ (12 ↦ₘ[γ] v) ∗ (13 ↦ₘ[γ] v) ∗ (14 ↦ₘ[γ] v) ∗ (15 ↦ₘ[γ] v) ∗
       (16 ↦ₘ[γ] v) ∗ (17 ↦ₘ[γ] v) ∗ (18 ↦ₘ[γ] v) ∗ (19 ↦ₘ[γ] v) ∗ (20 ↦ₘ[γ] v) ∗
       (21 ↦ₘ[γ] v) ∗ (22 ↦ₘ[γ] v) ∗ (23 ↦ₘ[γ] v) ∗ (24 ↦ₘ[γ] v) ∗ (25 ↦ₘ[γ] v) ∗
       (26 ↦ₘ[γ] v) ∗ (27 ↦ₘ[γ] v) ∗ (28 ↦ₘ[γ] v) ∗ (29 ↦ₘ[γ] v) ∗ (30 ↦ₘ[γ] v) ∗
       (31 ↦ₘ[γ] v) ∗ (32 ↦ₘ[γ] v) ∗ (33 ↦ₘ[γ] v) ∗ (34 ↦ₘ[γ] v) ∗ (35 ↦ₘ[γ] v) ∗
       (36 ↦ₘ[γ] v) ∗ (37 ↦ₘ[γ] v) ∗ (38 ↦ₘ[γ] v) ∗ (39 ↦ₘ[γ] v) ∗ (40 ↦ₘ[γ] v)) -∗
      ((40 ↦ₘ[γ] v) -∗ (40 ↦ₘ[γ] w)) -∗
      (((1 ↦ₘ[γ] v) ∗ (2 ↦ₘ[γ] v) ∗ (3 ↦ₘ[γ] v) ∗ (4 ↦ₘ[γ] v) ∗ (5 ↦ₘ[γ] v) ∗
        (6 ↦ₘ[γ] v) ∗ (7 ↦ₘ[γ] v) ∗ (8 ↦ₘ[γ] v) ∗ (9 ↦ₘ[γ] v) ∗ (10 ↦ₘ[γ] v) ∗
        (11 ↦ₘ[γ] v) ∗ (12 ↦ₘ[γ] v) ∗ (13 ↦ₘ[γ] v) ∗ (14 ↦ₘ[γ] v) ∗ (15 ↦ₘ[γ] v) ∗
        (16 ↦ₘ[γ] v) ∗ (17 ↦ₘ[γ] v) ∗ (18 ↦ₘ[γ] v) ∗ (19 ↦ₘ[γ] v) ∗ (20 ↦ₘ[γ] v) ∗
        (21 ↦ₘ[γ] v) ∗ (22 ↦ₘ[γ] v) ∗ (23 ↦ₘ[γ] v) ∗ (24 ↦ₘ[γ] v) ∗ (25 ↦ₘ[γ] v) ∗
        (26 ↦ₘ[γ] v) ∗ (27 ↦ₘ[γ] v) ∗ (28 ↦ₘ[γ] v) ∗ (29 ↦ₘ[γ] v) ∗ (30 ↦ₘ[γ] v) ∗
        (31 ↦ₘ[γ] v) ∗ (32 ↦ₘ[γ] v) ∗ (33 ↦ₘ[γ] v) ∗ (34 ↦ₘ[γ] v) ∗ (35 ↦ₘ[γ] v) ∗
        (36 ↦ₘ[γ] v) ∗ (37 ↦ₘ[γ] v) ∗ (38 ↦ₘ[γ] v) ∗ (39 ↦ₘ[γ] v)) ∗ (40 ↦ₘ[γ] w)) := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10,
          H11, H12, H13, H14, H15, H16, H17, H18, H19, H20,
          H21, H22, H23, H24, H25, H26, H27, H28, H29, H30,
          H31, H32, H33, H34, H35, H36, H37, H38, H39, H40⟩ Hstep
  isplitr [H40 Hstep]
  · iframe
  · iapply Hstep $$ H40

/-! ### Family 4: Functional Local Map Lookup Across $N = 5, 10, 20, 40$ -/

/-- Populate `n` stack locals in a functional `locals` map via
    `Trusted.updateLocal`. -/
def populateLocals (v : Trusted.MirVal) : Nat → (Nat → Option Trusted.MirVal)
  | 0 => fun _ => none
  | k + 1 => Trusted.updateLocal (populateLocals v k) (k + 1) (some v)

measure_decl bench_func_locals_5
theorem bench_func_locals_5 :
    populateLocals v 5 1 = some v := rfl

measure_decl bench_func_locals_10
theorem bench_func_locals_10 :
    populateLocals v 10 1 = some v := rfl

measure_decl bench_func_locals_20
theorem bench_func_locals_20 :
    populateLocals v 20 1 = some v := rfl

measure_decl bench_func_locals_40
theorem bench_func_locals_40 :
    populateLocals v 40 1 = some v := rfl

end IpmBenchmarks

/-! ## Part 3: Mechanized Audit and Resolution of `ChoiceKind.angelic` -/

section ChoiceKindResolution

/-! ### 3.1 Semantic Trap in Option B (`Trusted.StepResult.choice .angelic`) -/

/-- A 3-state test machine demonstrating the semantic trap of
    `ChoiceKind.angelic` in the current `Trusted.ReachesPrefix` +
    `Trusted.BehaviorOf`:
    - `0` (initial state) steps via
      `.choice .angelic (fun s => s = 1 ∨ s = 2)`,
    - `1` (good angelic witness) terminates normally via
      `.terminated (.normal ())`,
    - `2` (bad angelic branch) fails with `.failed .ub`. -/
def angelicTrapMachine : Trusted.SmallStepMachine Unit Nat Unit Unit where
  initState _ s := s = 0
  step _ s r :=
    match s with
    | 0 => r = .choice .angelic (fun s' => s' = 1 ∨ s' = 2)
    | 1 => r = .terminated (.normal ())
    | _ => r = .failed .ub

/-- Even though state `0` makes an `.angelic` choice and branch `s' = 1`
    terminates safely, `Trusted.BehaviorOf angelicTrapMachine () ⟨0, 2⟩` is
    UNDEFINED (`defined = False`, i.e. `Partial.ub`) because
    `Trusted.ReachesPrefix.choice` treats `.angelic` identically to
    `.demonic`. -/
theorem optionB_angelic_trap_is_ub :
    ¬ (Trusted.BehaviorOf angelicTrapMachine () ⟨0, 2⟩).defined := by
  intro hdef
  have hinit : angelicTrapMachine.initState () 0 := rfl
  have hstep0 : angelicTrapMachine.step () 0 (.choice .angelic (fun s' => s' = 1 ∨ s' = 2)) := rfl
  have hbranch2 : (fun s' => s' = 1 ∨ s' = 2) 2 := Or.inr rfl
  have hstep2 : angelicTrapMachine.step () 2 (.failed .ub) := rfl
  have hreach_bad :
      Trusted.ReachesPrefix angelicTrapMachine () 0 2 0 [] (.failed .ub) :=
    Trusted.ReachesPrefix.choice 1 .angelic 0 2 _ [] (.failed .ub)
      hstep0 hbranch2 (Trusted.ReachesPrefix.failed 0 2 .ub hstep2)
  exact hdef hinit [] (.failed .ub) hreach_bad

/-! ### 3.2 Option A: Demonic-Only `StepResultA` (Removing `ChoiceKind`) -/

/-- Option A `StepResultA`: removes `ChoiceKind` so `.choice` is unambiguously
    demonic (`branches : State → Prop`). -/
inductive StepResultA (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (branches : State → Prop)
  | terminated (term : Trusted.TerminationKind Val)
  | failed (err : Trusted.FailureKind)

/-- Option A `SmallStepMachineA`. -/
structure SmallStepMachineA (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResultA State Obs Val → Prop

/-- Option A `ReachesPrefixA`: identical to `Trusted.ReachesPrefix` without the
    dead `kind : ChoiceKind` parameter on `.choice` and `.emptyChoice`. -/
inductive ReachesPrefixA (M : SmallStepMachineA Prog State Obs Val) (p : Prog)
    (init : State) : Nat → State → List Obs → Trusted.PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefixA M p init 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs) (out : Trusted.PrefixOutcome Val) :
      M.step p s (.step obs s') →
      ReachesPrefixA M p init n s' tr out →
      ReachesPrefixA M p init (n + 1) s (obs :: tr) out
  | choice (n : Nat) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : Trusted.PrefixOutcome Val) :
      M.step p s (.choice branches) →
      branches s' →
      ReachesPrefixA M p init n s' tr out →
      ReachesPrefixA M p init (n + 1) s tr out
  | emptyChoice (n : Nat) (s : State) (branches : State → Prop) :
      M.step p s (.choice branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefixA M p init (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : Trusted.TerminationKind Val) :
      M.step p s (.terminated term) →
      ReachesPrefixA M p init (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) (err : Trusted.FailureKind) :
      M.step p s (.failed err) →
      ReachesPrefixA M p init (n + 1) s [] (.failed err)
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step p s r) →
      ReachesPrefixA M p init (n + 1) s [] .stuck

/-- Embedding an Option A machine into `Trusted.SmallStepMachine` (mapping
    `.choice` to `.choice .demonic`). -/
def SmallStepMachineA.toTrusted (M : SmallStepMachineA Prog State Obs Val) :
    Trusted.SmallStepMachine Prog State Obs Val where
  initState := M.initState
  step p s r :=
    match r with
    | .step obs s' => M.step p s (.step obs s')
    | .choice .demonic branches => M.step p s (.choice branches)
    | .choice .angelic _ => False
    | .terminated term => M.step p s (.terminated term)
    | .failed err => M.step p s (.failed err)

/-- Exact equivalence between `ReachesPrefixA` and `Trusted.ReachesPrefix` on
    `M.toTrusted`. -/
theorem reachesPrefixA_iff_reachesPrefix
    (M : SmallStepMachineA Prog State Obs Val) (p : Prog) (init : State)
    (n : Nat) (s : State) (tr : List Obs) (out : Trusted.PrefixOutcome Val) :
    ReachesPrefixA M p init n s tr out ↔
      Trusted.ReachesPrefix M.toTrusted p init n s tr out := by
  constructor
  · intro h
    induction h with
    | zero s => exact .zero s
    | step n s s' obs tr out hstep _ ih => exact .step n s s' obs tr out hstep ih
    | choice n s s' branches tr out hstep hbr _ ih =>
      exact .choice n .demonic s s' branches tr out hstep hbr ih
    | emptyChoice n s branches hstep hemp =>
      exact .emptyChoice n .demonic s branches hstep hemp
    | terminated n s term hstep => exact .terminated n s term hstep
    | failed n s err hstep => exact .failed n s err hstep
    | noStep n s hno =>
      refine .noStep n s (fun ⟨r, hr⟩ => hno ?_)
      cases r with
      | step obs s' => exact ⟨.step obs s', hr⟩
      | choice kind branches =>
        cases kind with
        | demonic => exact ⟨.choice branches, hr⟩
        | angelic => exact False.elim hr
      | terminated term => exact ⟨.terminated term, hr⟩
      | failed err => exact ⟨.failed err, hr⟩
  · intro h
    induction h with
    | zero s => exact .zero s
    | step n s s' obs tr out hstep _ ih => exact .step n s s' obs tr out hstep ih
    | choice n kind s s' branches tr out hstep hbr _ ih =>
      cases kind with
      | demonic => exact .choice n s s' branches tr out hstep hbr ih
      | angelic => exact False.elim hstep
    | emptyChoice n kind s branches hstep hemp =>
      cases kind with
      | demonic => exact .emptyChoice n s branches hstep hemp
      | angelic => exact False.elim hstep
    | terminated n s term hstep => exact .terminated n s term hstep
    | failed n s err hstep => exact .failed n s err hstep
    | noStep n s hno =>
      refine .noStep n s (fun ⟨r, hr⟩ => hno ?_)
      cases r with
      | step obs s' => exact ⟨.step obs s', hr⟩
      | choice branches => exact ⟨.choice .demonic branches, hr⟩
      | terminated term => exact ⟨.terminated term, hr⟩
      | failed err => exact ⟨.failed err, hr⟩

/-! ### 3.3 Option C: Two-Player Strategy / Game Semantics -/

/-- Option C: Fuel-indexed two-player game / strategy satisfaction
    `GameHolds M p post fuel s hist`.
    - `.choice .demonic branches` is universal
      (`(∃ s0, branches s0) ∧ ∀ s', branches s' → ...`),
    - `.choice .angelic branches` is existential
      (`∃ s', branches s' ∧ ...`),
    - `.step`, `.terminated` require compatibility across enabled steps. -/
def GameHolds (M : Trusted.SmallStepMachine Prog State Obs Val) (p : Prog)
    (post : List Obs → Trusted.PrefixOutcome Val → Prop) :
    Nat → State → List Obs → Prop
  | 0, _, hist =>
      post hist .running
  | n + 1, s, hist =>
      (∃ r0, M.step p s r0) ∧
      ∀ r, M.step p s r →
        match r with
        | .step obs s' => GameHolds M p post n s' (hist ++ [obs])
        | .choice .demonic branches =>
            (∃ s0, branches s0) ∧ ∀ s', branches s' → GameHolds M p post n s' hist
        | .choice .angelic branches =>
            ∃ s', branches s' ∧ GameHolds M p post n s' hist
        | .terminated term => post hist (.terminated term)
        | .failed _ => False

/-- Induced partial behavior under Option C (`GameHolds`):
    - `defined`: from any valid initial state `q.init`, `GameHolds` holds for
      `out.isSafe` (requiring all demonic branches to be safe and at least one
      angelic branch to be safe).
    - `val`: the set of outcomes reachable along a safe angelic strategy. -/
def GameBehaviorOf (M : Trusted.SmallStepMachine Prog State Obs Val) (p : Prog) :
    Trusted.ExecQuery State → Trusted.Partial (Trusted.ExecOut Obs Val → Prop) :=
  fun q => {
    defined := M.initState p q.init → GameHolds M p (fun _ out => out.isSafe) q.steps q.init []
    val := fun _ out =>
      M.initState p q.init ∧
      Trusted.ReachesPrefix M p q.init q.steps q.init out.trace out.outcome ∧
      out.outcome.isSafe
  }

/-- Under Option C (`GameHolds`), `angelicTrapMachine` at query `⟨0, 2⟩` IS
    safe and satisfies normal termination
    (`outcome = .terminated (.normal ())`), witnessed by the angelic choice
    `s' = 1`. -/
theorem optionC_angelic_trap_holds :
    GameHolds angelicTrapMachine ()
      (fun _ out => out.isSafe ∧ out = .terminated (.normal ())) 2 0 [] := by
  refine ⟨⟨_, rfl⟩, ?_⟩
  intro r hr
  have hr' : r = .choice .angelic (fun s' => s' = 1 ∨ s' = 2) := hr
  subst hr'
  refine ⟨1, Or.inl rfl, ⟨_, rfl⟩, ?_⟩
  intro r1 hr1
  have hr1' : r1 = .terminated (.normal ()) := hr1
  subst hr1'
  exact ⟨trivial, rfl⟩

/-- Corollary: `GameBehaviorOf angelicTrapMachine () ⟨0, 2⟩` is `defined`
    (`True`), contrasting with `optionB_angelic_trap_is_ub`
    (`¬ (Trusted.BehaviorOf angelicTrapMachine () ⟨0, 2⟩).defined`). -/
theorem optionC_angelic_trap_is_defined :
    (GameBehaviorOf angelicTrapMachine () ⟨0, 2⟩).defined := by
  intro _
  refine ⟨⟨_, rfl⟩, ?_⟩
  intro r hr
  have hr' : r = .choice .angelic (fun s' => s' = 1 ∨ s' = 2) := hr
  subst hr'
  refine ⟨1, Or.inl rfl, ⟨_, rfl⟩, ?_⟩
  intro r1 hr1
  have hr1' : r1 = .terminated (.normal ()) := hr1
  subst hr1'
  exact trivial

/-- An angelic strategy (Skolem witness function) selecting the target state at
    each `.choice .angelic` transition as a function of remaining fuel and
    current state. -/
abbrev AngelicStrategy (State : Type) := Nat → State → State

/-- Option C (Skolemized Strategy-Tree Form): Inductive reachability
    parameterized by an angelic strategy `strat : AngelicStrategy State`.
    - `.choice .demonic` branches universally over all `s'` with `branches s'`.
    - `.choice .angelic` steps to the strategy's chosen witness `strat n s`
      (or `.stuck` if `¬ branches (strat n s)`).
    This formulation reduces two-player angelic/demonic reachability for a
    chosen `strat` directly to pathwise demonic reachability, compatible with
    `Iris.step_fupdN_soundness_close`. -/
inductive ReachesWithStrategy (M : Trusted.SmallStepMachine Prog State Obs Val)
    (strat : AngelicStrategy State) (p : Prog) (init : State) :
    Nat → State → List Obs → Trusted.PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesWithStrategy M strat p init 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs) (out : Trusted.PrefixOutcome Val) :
      M.step p s (.step obs s') →
      ReachesWithStrategy M strat p init n s' tr out →
      ReachesWithStrategy M strat p init (n + 1) s (obs :: tr) out
  | demonicChoice (n : Nat) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : Trusted.PrefixOutcome Val) :
      M.step p s (.choice .demonic branches) →
      branches s' →
      ReachesWithStrategy M strat p init n s' tr out →
      ReachesWithStrategy M strat p init (n + 1) s tr out
  | emptyDemonicChoice (n : Nat) (s : State) (branches : State → Prop) :
      M.step p s (.choice .demonic branches) →
      (¬ ∃ s', branches s') →
      ReachesWithStrategy M strat p init (n + 1) s [] .stuck
  | angelicChoice (n : Nat) (s : State) (branches : State → Prop)
      (tr : List Obs) (out : Trusted.PrefixOutcome Val) :
      M.step p s (.choice .angelic branches) →
      branches (strat n s) →
      ReachesWithStrategy M strat p init n (strat n s) tr out →
      ReachesWithStrategy M strat p init (n + 1) s tr out
  | invalidAngelicChoice (n : Nat) (s : State) (branches : State → Prop) :
      M.step p s (.choice .angelic branches) →
      ¬ branches (strat n s) →
      ReachesWithStrategy M strat p init (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : Trusted.TerminationKind Val) :
      M.step p s (.terminated term) →
      ReachesWithStrategy M strat p init (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) (err : Trusted.FailureKind) :
      M.step p s (.failed err) →
      ReachesWithStrategy M strat p init (n + 1) s [] (.failed err)
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step p s r) →
      ReachesWithStrategy M strat p init (n + 1) s [] .stuck

/-- Strategy-indexed partial behavior (`Option C` Skolemized form):
    `defined` holds when there exists an angelic strategy `strat` under which
    every demonic path is safe (`out.isSafe`). -/
def StrategyBehaviorOf (M : Trusted.SmallStepMachine Prog State Obs Val) (p : Prog) :
    Trusted.ExecQuery State → Trusted.Partial (Trusted.ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∃ strat : AngelicStrategy State,
          ∀ tr out,
            ReachesWithStrategy M strat p q.init q.steps q.init tr out →
            out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ∃ strat : AngelicStrategy State,
        (∀ tr' out', ReachesWithStrategy M strat p q.init q.steps q.init tr' out' → out'.isSafe) ∧
        ReachesWithStrategy M strat p q.init q.steps q.init out.trace out.outcome
  }

/-- Under `StrategyBehaviorOf`, `angelicTrapMachine` at `⟨0, 2⟩` is `defined`
    (`True`), witnessed by the constant angelic strategy
    `strat := fun _ _ => 1`. -/
theorem optionC_strategy_angelic_trap_is_defined :
    (StrategyBehaviorOf angelicTrapMachine () ⟨0, 2⟩).defined := by
  intro _
  refine ⟨fun _ _ => 1, ?_⟩
  intro tr out hreach
  cases hreach with
  | step _ _ _ _ _ _ h0 _ => cases h0
  | demonicChoice _ _ _ _ _ _ h0 _ _ => cases h0
  | emptyDemonicChoice _ _ _ h0 _ => cases h0
  | invalidAngelicChoice _ _ _ h0 hbad =>
    have h0' : Trusted.StepResult.choice .angelic _ =
        Trusted.StepResult.choice (State := Nat) (Obs := Unit) (Val := Unit)
          .angelic (fun s' => s' = 1 ∨ s' = 2) := h0
    injection h0' with _ hbr
    rw [hbr] at hbad
    exact False.elim (hbad (Or.inl rfl))
  | terminated _ _ _ h0 => cases h0
  | failed _ _ _ h0 => cases h0
  | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
  | angelicChoice _ _ _ _ _ h0 _ hrest =>
    cases hrest with
    | step _ _ _ _ _ _ h1 _ => cases h1
    | demonicChoice _ _ _ _ _ _ h1 _ _ => cases h1
    | emptyDemonicChoice _ _ _ h1 _ => cases h1
    | angelicChoice _ _ _ _ _ h1 _ _ => cases h1
    | invalidAngelicChoice _ _ _ h1 _ => cases h1
    | terminated _ _ _ _ => exact trivial
    | failed _ _ _ h1 => cases h1
    | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)

end ChoiceKindResolution

end Anneal.R2IrisLeanProbe
