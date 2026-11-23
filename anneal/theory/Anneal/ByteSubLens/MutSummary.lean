-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirWp
public import Anneal.MirTotal.Ops
public import Anneal.ByteSubLens.Lens

public section
namespace Anneal.ByteSubLens

open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal

/-!
# Interprocedural `&mut Field` Call Summaries & `@[irreducible]` Cutpoints
(`ByteSubLens.MutSummary`)

Provides an LCNF-computable (`0` `noncomputable`, `0` `._unsafe_rec`) summary
layer coupling `ByteSubLens` directly to `Trusted.MirSemantics.evalStep` and
`Anneal.MirWp.wpState`:

1. **`MirCalleeRunsTo` & `mirCalleeRunsTo_implies_wpState`:** Fuel-bounded
   operational execution predicate over `Trusted.MirSemantics.evalStep p 0`
   recording both the post-call `MemoryState` (`memOut`) and return `Val`
   (`retVal`), lifting unconditionally into `Anneal.MirWp.wpState`.
2. **`MutFieldCallSummary`, `execMutSummaryCall`, & `CalleeRealizesSummary`:**
   Computable byte-slice summary evaluator (`execMutSummaryCall`) paired with
   its semantic realization obligation over `LocalSlot.indirect ⟨subL.allocId,
   subL.offset⟩` (`initSuballocCalleeState`).
3. **Zero-`Prop`-Argument `@[irreducible] MutSummaryCut`:** Seals callee MIR
   proofs (`seal_mutSummaryCut`) behind an opaque kernel firewall so callers
   evaluate `execMutSummaryCall` by `rfl` and extract `MirCalleeRunsTo`,
   `Anneal.MirWp.wpState`, target-slice post-state, and universal disjoint
   `MemoryState` framing (`apply_mutSummaryCut_sound`) without unfolding callee
   MIR bodies.
4. **Chained Multi-Call Framing (`execMutSummaryChain`):** Composes `N`
   sequential `&mut` field/slot summary calls via `List.foldr` (`0`
   `._unsafe_rec`), proving `O(N)` `rfl` summary execution, step-by-step
   `MirCalleeRunsTo` adequacy, and disjoint-frame preservation
   (`execMutSummaryChain_frame_disjoint`).
-/

/-! ## 1. Callee Entry State & `evalStep` / `Anneal.MirWp` Adequacy -/

private theorem ms_boolFalseNeTrue (h : false = true) : False :=
  Bool.noConfusion h

private theorem ms_bandLeft {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact False.elim (ms_boolFalseNeTrue h)
  | true => rfl

private theorem ms_bandRight {a b : Bool} (h : (a && b) = true) :
    b = true := by
  cases a with
  | false => exact False.elim (ms_boolFalseNeTrue h)
  | true => exact h

private theorem ms_natEq_of_beq (a b : Nat) (h : Nat.beq a b = true) :
    a = b := by
  revert b
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ _ => exact False.elim (ms_boolFalseNeTrue h)
  | succ _ ih =>
    intro b h
    cases b with
    | zero => exact False.elim (ms_boolFalseNeTrue h)
    | succ b' => exact congrArg Nat.succ (ih b' h)

/-- Constructs the single-frame callee entry `State` (`0` `noncomputable`) with
`_0 := liveUninitSlotComp retTy`, `_1 := LocalSlot.indirect ⟨subL.allocId,
subL.offset⟩`, immediate value arguments `extraArgs`, and uninitialized
temporaries `extraTempTys`. -/
@[expose] def initSuballocCalleeState (retTy : MirTy) (subL : ByteSubLens)
    (extraArgs : List Val) (extraTempTys : List MirTy)
    (mem : MemoryState) : State :=
  let argSlots := List.foldr (fun v acc => LocalSlot.immediate (some v) :: acc)
    [] extraArgs
  let tempSlots := List.foldr (fun ty acc => liveUninitSlotComp ty :: acc)
    [] extraTempTys
  let locals : List LocalSlot :=
    liveUninitSlotComp retTy ::
      LocalSlot.indirect ⟨subL.allocId, subL.offset⟩ ::
      (argSlots ++ tempSlots)
  { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := locals }]
    callerMem := ⟨[]⟩
    mem := mem }

/-- Fuel-bounded callee execution predicate over `Trusted.MirSemantics.evalStep`
(`0` `noncomputable`), requiring normal `.done (.returned out)` termination with
`cur.mem = memOut` and `out.ret = retVal` and forbidding unwinds and faults. -/
@[expose] def MirCalleeRunsTo (p : Program) (memOut : MemoryState) (retVal : Val)
    (fuel : Nat) (st : State) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun _ => False)
    (fun _ ih cur =>
      match evalStep p 0 cur with
      | .step stNext => ih stNext
      | .done d =>
        match d with
        | .returned out => cur.mem = memOut ∧ out.ret = retVal
        | .unwound _ => False
      | .fault _ => False)
    fuel st

/-- Base equation `MirCalleeRunsTo p memOut retVal 0 st = False`. -/
theorem mirCalleeRunsTo_zero (p : Program) (memOut : MemoryState)
    (retVal : Val) (st : State) :
    MirCalleeRunsTo p memOut retVal 0 st = False := rfl

/-- Step equation unfolding one step of `MirCalleeRunsTo`. -/
theorem mirCalleeRunsTo_succ (p : Program) (memOut : MemoryState)
    (retVal : Val) (n : Nat) (st : State) :
    MirCalleeRunsTo p memOut retVal (n + 1) st =
      (match evalStep p 0 st with
      | .step stNext => MirCalleeRunsTo p memOut retVal n stNext
      | .done d =>
        match d with
        | .returned out => st.mem = memOut ∧ out.ret = retVal
        | .unwound _ => False
      | .fault _ => False) := rfl

private theorem mirCalleeRunsTo_implies_execState {p : Program}
    {memOut : MemoryState} {retVal : Val} :
    ∀ {fuel : Nat} {st : State},
      MirCalleeRunsTo p memOut retVal fuel st →
      Anneal.MirWp.execState p fuel st
        (fun out => ∃ r, out = .returned r ∧ r.ret = retVal)
  | 0, _, h => False.elim h
  | n + 1, st, h => by
    rw [mirCalleeRunsTo_succ] at h
    change (match evalStep p 0 st with
      | .step st' =>
        Anneal.MirWp.execState p n st'
          (fun out => ∃ r, out = .returned r ∧ r.ret = retVal)
      | .done out => ∃ r, out = .returned r ∧ r.ret = retVal
      | .fault _ => False)
    cases hStep : evalStep p 0 st with
    | step stNext =>
      rw [hStep] at h
      exact mirCalleeRunsTo_implies_execState h
    | done d =>
      rw [hStep] at h
      cases d with
      | returned out => exact ⟨out, rfl, h.2⟩
      | unwound _ => exact False.elim h
    | fault _ =>
      rw [hStep] at h
      exact False.elim h

/-- Unconditional adequacy lift from `MirCalleeRunsTo` into
`Anneal.MirWp.wpState` (`ValidChoice`-quantified weakest precondition over
`Trusted.MirSemantics.evalStep`). -/
theorem mirCalleeRunsTo_implies_wpState {p : Program} {memOut : MemoryState}
    {retVal : Val} {fuel : Nat} {st : State}
    (h : MirCalleeRunsTo p memOut retVal fuel st) :
    Anneal.MirWp.wpState p fuel st
      (fun out => ∃ r, out = .returned r ∧ r.ret = retVal) :=
  Anneal.MirWp.wpOutcomeState_iff_execOutcomeState.mpr
    (mirCalleeRunsTo_implies_execState h)

/-! ## 2. `MutFieldCallSummary`, `execMutSummaryCall`, & `@[irreducible]` Cut -/

/-- Pure data specification of an `&mut Field` / `&mut slots[i]` method call
over an aligned `fieldSize`-byte `ByteSubLens` slice (`0` `noncomputable`). -/
structure MutFieldCallSummary where
  retTy : MirTy
  fieldSize : Nat
  alignLog2 : Nat
  tempTys : List MirTy
  summaryFn : List AllocByte → List Val → Option (List AllocByte × Val)

/-- Computable caller-side summary evaluator (`0` `noncomputable`): validates
slice width and alignment, reads `oldSlice` via `byteSubLensGet`, evaluates
`sum.summaryFn`, and commits `newSlice` via `byteSubLensPut` without touching
callee MIR. -/
@[expose] def execMutSummaryCall (sum : MutFieldCallSummary) (subL : ByteSubLens)
    (mem : MemoryState) (extraArgs : List Val) :
    Option (MemoryState × Val) :=
  match Nat.beq subL.size sum.fieldSize &&
      Nat.beq subL.alignLog2 sum.alignLog2 with
  | false => none
  | true =>
    match byteSubLensGet subL mem with
    | none => none
    | some oldSlice =>
      match sum.summaryFn oldSlice extraArgs with
      | none => none
      | some (newSlice, retVal) =>
        match byteSubLensPut subL mem newSlice with
        | none => none
        | some memOut => some (memOut, retVal)

/-- Semantic realization contract: for every `MemoryState`, aligned
`ByteSubLens`, readable `oldSlice`, and argument tuple accepted by
`sum.summaryFn`, `p` steps via `Trusted.MirSemantics.evalStep` to normal return
`retVal` with post-memory `memOut` matching `byteSubLensPut`. -/
@[expose] def CalleeRealizesSummary (p : Program) (fuel : Nat)
    (sum : MutFieldCallSummary) : Prop :=
  ∀ (subL : ByteSubLens) (mem : MemoryState)
    (oldSlice newSlice : List AllocByte) (extraArgs : List Val) (retVal : Val),
    subL.size = sum.fieldSize →
    subL.alignLog2 = sum.alignLog2 →
    byteSubLensGet subL mem = some oldSlice →
    sum.summaryFn oldSlice extraArgs = some (newSlice, retVal) →
    ∃ memOut : MemoryState,
      MirCalleeRunsTo p memOut retVal fuel
        (initSuballocCalleeState sum.retTy subL extraArgs sum.tempTys mem) ∧
      byteSubLensPut subL mem newSlice = some memOut

/-- Zero-`Prop`-argument opaque cutpoint predicate sealing a verified callee
`MutFieldCallSummary` (`[irreducible]` applied after `seal`/`open`). -/
@[expose] def MutSummaryCut (p : Program) (fuel : Nat)
    (sum : MutFieldCallSummary) : Prop :=
  CalleeRealizesSummary p fuel sum

/-- Seals a `CalleeRealizesSummary` proof into `MutSummaryCut`. -/
theorem seal_mutSummaryCut {p : Program} {fuel : Nat}
    {sum : MutFieldCallSummary} (h : CalleeRealizesSummary p fuel sum) :
    MutSummaryCut p fuel sum := h

/-- Opens a sealed `MutSummaryCut` back to `CalleeRealizesSummary`. -/
theorem open_mutSummaryCut {p : Program} {fuel : Nat}
    {sum : MutFieldCallSummary} (h : MutSummaryCut p fuel sum) :
    CalleeRealizesSummary p fuel sum := h

attribute [irreducible] MutSummaryCut

/-- Caller composition rule for `@[irreducible] MutSummaryCut`: whenever
computable `execMutSummaryCall sum subL mem extraArgs` returns
`some (memOut, retVal)` (e.g. by `rfl`), the underlying MIR callee `p` steps via
`Trusted.MirSemantics.evalStep` to `(memOut, retVal)` (`MirCalleeRunsTo` and
`Anneal.MirWp.wpState`), updates `subL` to `newSlice`, and preserves every
disjoint slice `otherL` across `MemoryState`. -/
theorem apply_mutSummaryCut_sound {p : Program} {fuel : Nat}
    {sum : MutFieldCallSummary} (hCut : MutSummaryCut p fuel sum)
    {subL : ByteSubLens} {mem memOut : MemoryState}
    {extraArgs : List Val} {retVal : Val}
    (hExec : execMutSummaryCall sum subL mem extraArgs =
      some (memOut, retVal)) :
    MirCalleeRunsTo p memOut retVal fuel
      (initSuballocCalleeState sum.retTy subL extraArgs sum.tempTys mem) ∧
    Anneal.MirWp.wpState p fuel
      (initSuballocCalleeState sum.retTy subL extraArgs sum.tempTys mem)
      (fun out => ∃ r, out = .returned r ∧ r.ret = retVal) ∧
    (∃ oldSlice newSlice : List AllocByte,
      byteSubLensGet subL mem = some oldSlice ∧
      sum.summaryFn oldSlice extraArgs = some (newSlice, retVal) ∧
      byteSubLensPut subL mem newSlice = some memOut ∧
      byteSubLensGet subL memOut = some newSlice) ∧
    (∀ otherL : ByteSubLens,
      byteLensDisjoint subL otherL = true →
      byteSubLensGet otherL memOut = byteSubLensGet otherL mem) := by
  dsimp only [execMutSummaryCall] at hExec
  cases hGeo : (Nat.beq subL.size sum.fieldSize &&
      Nat.beq subL.alignLog2 sum.alignLog2) with
  | false => rw [hGeo] at hExec; nomatch hExec
  | true =>
    rw [hGeo] at hExec
    dsimp only at hExec
    have hSz := ms_natEq_of_beq _ _ (ms_bandLeft hGeo)
    have hAl := ms_natEq_of_beq _ _ (ms_bandRight hGeo)
    cases hGet : byteSubLensGet subL mem with
    | none => rw [hGet] at hExec; nomatch hExec
    | some oldSlice =>
      rw [hGet] at hExec
      dsimp only at hExec
      cases hSum : sum.summaryFn oldSlice extraArgs with
      | none => rw [hSum] at hExec; nomatch hExec
      | some pair =>
        rw [hSum] at hExec
        cases pair with
        | mk newSlice rv =>
          dsimp only at hExec
          cases hPut : byteSubLensPut subL mem newSlice with
          | none => rw [hPut] at hExec; nomatch hExec
          | some mPut =>
            rw [hPut] at hExec
            injection hExec with hOutEq
            have hM : mPut = memOut := congrArg Prod.fst hOutEq
            have hR : rv = retVal := congrArg Prod.snd hOutEq
            subst hM; subst hR
            cases open_mutSummaryCut hCut subL mem oldSlice newSlice extraArgs
                rv hSz hAl hGet hSum with
            | intro mReal hReal =>
              rw [hPut] at hReal
              injection hReal.2 with hRealEq
              subst hRealEq
              exact ⟨hReal.1, mirCalleeRunsTo_implies_wpState hReal.1,
                ⟨oldSlice, newSlice, rfl, hSum, hPut,
                  byteSubLens_put_get subL mem mPut newSlice hPut⟩,
                fun otherL hDisj =>
                  byteSubLens_get_put_disjoint subL otherL mem mPut newSlice
                    hDisj hPut⟩

/-! ## 3. Chained Multi-Call Composition & Disjoint-Frame Preservation -/

/-- Pure data descriptor for one `&mut` summary call site in a sequence (`0`
`noncomputable`). -/
structure SummaryCallSite where
  sum : MutFieldCallSummary
  subL : ByteSubLens
  extraArgs : List Val

/-- Executes a list of `&mut` summary call sites left-to-right via `List.foldr`
(`0` `noncomputable`, `0` `._unsafe_rec`), returning the final `MemoryState` and
the list of per-call return values. -/
@[expose] def execMutSummaryChain (sites : List SummaryCallSite) (mem : MemoryState) :
    Option (MemoryState × List Val) :=
  List.foldr
    (fun (site : SummaryCallSite)
        (k : MemoryState → Option (MemoryState × List Val))
        (mCur : MemoryState) =>
      match execMutSummaryCall site.sum site.subL mCur site.extraArgs with
      | none => none
      | some (mNext, rv) =>
        match k mNext with
        | none => none
        | some (mFin, rvs) => some (mFin, rv :: rvs))
    (fun mCur => some (mCur, []))
    sites mem

/-- Decidable check that `otherL` is disjoint from every `site.subL` in
`sites`. -/
@[expose] def allSitesDisjoint (otherL : ByteSubLens) (sites : List SummaryCallSite) :
    Bool :=
  List.foldr (fun site acc => byteLensDisjoint site.subL otherL && acc)
    true sites

/-- Multi-call disjoint-frame theorem (`[]` zero axioms): executing any chain of
`SummaryCallSite`s preserves `byteSubLensGet otherL` whenever `otherL` is
disjoint from every call site in `sites`. -/
theorem execMutSummaryChain_frame_disjoint (otherL : ByteSubLens)
    (sites : List SummaryCallSite) :
    ∀ (mem memOut : MemoryState) (rets : List Val),
      allSitesDisjoint otherL sites = true →
      execMutSummaryChain sites mem = some (memOut, rets) →
      byteSubLensGet otherL memOut = byteSubLensGet otherL mem := by
  induction sites with
  | nil =>
    intro mem memOut _ _ hChain
    injection hChain with hPair
    have hM : mem = memOut := congrArg Prod.fst hPair
    subst hM
    rfl
  | cons hd tl ih =>
    intro mem memOut rets hDisjAll hChain
    have hDisjHd := ms_bandLeft hDisjAll
    have hDisjTl := ms_bandRight hDisjAll
    change (match execMutSummaryCall hd.sum hd.subL mem hd.extraArgs with
      | none => none
      | some (mNext, rv) =>
        match execMutSummaryChain tl mNext with
        | none => none
        | some (mFin, rvs) => some (mFin, rv :: rvs)) =
        some (memOut, rets) at hChain
    cases hHd : execMutSummaryCall hd.sum hd.subL mem hd.extraArgs with
    | none => rw [hHd] at hChain; nomatch hChain
    | some p1 =>
      rw [hHd] at hChain
      cases p1 with
      | mk mNext rv =>
        dsimp only at hChain
        cases hTl : execMutSummaryChain tl mNext with
        | none => rw [hTl] at hChain; nomatch hChain
        | some pFin =>
          rw [hTl] at hChain
          cases pFin with
          | mk mFin rvs =>
            injection hChain with hOut
            have hMFin : mFin = memOut := congrArg Prod.fst hOut
            subst hMFin
            have hFrameHd :
                byteSubLensGet otherL mNext = byteSubLensGet otherL mem := by
              dsimp only [execMutSummaryCall] at hHd
              cases hG : (Nat.beq hd.subL.size hd.sum.fieldSize &&
                  Nat.beq hd.subL.alignLog2 hd.sum.alignLog2) with
              | false => rw [hG] at hHd; nomatch hHd
              | true =>
                rw [hG] at hHd; dsimp only at hHd
                cases hGet0 : byteSubLensGet hd.subL mem with
                | none => rw [hGet0] at hHd; nomatch hHd
                | some s0 =>
                  rw [hGet0] at hHd; dsimp only at hHd
                  cases hS0 : hd.sum.summaryFn s0 hd.extraArgs with
                  | none => rw [hS0] at hHd; nomatch hHd
                  | some pr =>
                    rw [hS0] at hHd
                    cases pr with
                    | mk sNew rv0 =>
                      dsimp only at hHd
                      cases hP0 : byteSubLensPut hd.subL mem sNew with
                      | none => rw [hP0] at hHd; nomatch hHd
                      | some mP =>
                        rw [hP0] at hHd
                        injection hHd with hEqP
                        have hMP : mP = mNext := congrArg Prod.fst hEqP
                        subst hMP
                        exact byteSubLens_get_put_disjoint hd.subL otherL mem
                          mP sNew hDisjHd hP0
            exact Eq.trans (ih mNext mFin rvs hDisjTl hTl) hFrameHd

/-- Inductive step-by-step operational trace certificate witnessing that every
call site in `sites` is backed by a verified `MirCalleeRunsTo` MIR execution
from `mem` to `memOut` producing `rets`. -/
inductive MirCalleeChainRunsTo :
    List (Program × Nat × SummaryCallSite) → MemoryState →
      MemoryState → List Val → Prop where
  | nil (m : MemoryState) :
      MirCalleeChainRunsTo [] m m []
  | cons {p : Program} {fuel : Nat} {site : SummaryCallSite}
      {rest : List (Program × Nat × SummaryCallSite)}
      {m0 m1 mFin : MemoryState} {rv : Val} {rvs : List Val}
      (headRun : MirCalleeRunsTo p m1 rv fuel
        (initSuballocCalleeState site.sum.retTy site.subL site.extraArgs
          site.sum.tempTys m0))
      (tailRuns : MirCalleeChainRunsTo rest m1 mFin rvs) :
      MirCalleeChainRunsTo ((p, fuel, site) :: rest) m0 mFin (rv :: rvs)

/-- Predicate asserting that every `(p, fuel, site)` entry in `specs` carries a
sealed `@[irreducible] MutSummaryCut p fuel site.sum` (`List.foldr`, `0`
`._unsafe_rec`). -/
@[expose] def AllSitesSummaryCut (specs : List (Program × Nat × SummaryCallSite)) :
    Prop :=
  List.foldr (fun e acc => MutSummaryCut e.1 e.2.1 e.2.2.sum ∧ acc) True specs

/-- Chained `@[irreducible] MutSummaryCut` soundness: if every entry in `specs`
carries a sealed `MutSummaryCut` and computable `execMutSummaryChain` returns
`some (memOut, rets)`, then the full sequence is operationally realized step by
step via `MirCalleeChainRunsTo` over `Trusted.MirSemantics.evalStep` while
preserving every disjoint `ByteSubLens`. -/
theorem execMutSummaryChain_certified_sound
    (specs : List (Program × Nat × SummaryCallSite)) :
    ∀ {mem memOut : MemoryState} {rets : List Val},
      AllSitesSummaryCut specs →
      execMutSummaryChain (List.foldr (fun e acc => e.2.2 :: acc) [] specs)
        mem = some (memOut, rets) →
      MirCalleeChainRunsTo specs mem memOut rets ∧
      (∀ otherL : ByteSubLens,
        allSitesDisjoint otherL
          (List.foldr (fun e acc => e.2.2 :: acc) [] specs) = true →
        byteSubLensGet otherL memOut = byteSubLensGet otherL mem) := by
  induction specs with
  | nil =>
    intro mem memOut rets _ hChain
    injection hChain with hPair
    have hM : mem = memOut := congrArg Prod.fst hPair
    have hR : ([] : List Val) = rets := congrArg Prod.snd hPair
    subst hM; subst hR
    exact ⟨.nil mem, fun _ _ => rfl⟩
  | cons entry rest ih =>
    cases entry with
    | mk p fSite =>
      cases fSite with
      | mk fuel site =>
        intro mem memOut rets hAll hChain
        let sites :=
          site :: List.foldr
            (fun (e : Program × Nat × SummaryCallSite) acc => e.2.2 :: acc)
            [] rest
        have hFrameAll : ∀ otherL : ByteSubLens,
            allSitesDisjoint otherL sites = true →
            byteSubLensGet otherL memOut = byteSubLensGet otherL mem :=
          fun otherL hDisj =>
            execMutSummaryChain_frame_disjoint otherL sites mem memOut rets
              hDisj hChain
        change (match execMutSummaryCall site.sum site.subL mem
            site.extraArgs with
          | none => none
          | some (mNext, rv) =>
            match execMutSummaryChain
                (List.foldr (fun e acc => e.2.2 :: acc) [] rest) mNext with
            | none => none
            | some (mFin, rvs) => some (mFin, rv :: rvs)) =
            some (memOut, rets) at hChain
        cases hHd : execMutSummaryCall site.sum site.subL mem site.extraArgs
            with
        | none => rw [hHd] at hChain; nomatch hChain
        | some p1 =>
          rw [hHd] at hChain
          cases p1 with
          | mk mNext rv =>
            dsimp only at hChain
            cases hTl : execMutSummaryChain
                (List.foldr (fun e acc => e.2.2 :: acc) [] rest) mNext with
            | none => rw [hTl] at hChain; nomatch hChain
            | some pFin =>
              rw [hTl] at hChain
              cases pFin with
              | mk mFin rvs =>
                injection hChain with hOut
                have hMFin : mFin = memOut := congrArg Prod.fst hOut
                have hRets : rv :: rvs = rets := congrArg Prod.snd hOut
                subst hMFin; subst hRets
                have hStepSound := apply_mutSummaryCut_sound hAll.1 hHd
                have hTailSound := ih hAll.2 hTl
                exact ⟨.cons hStepSound.1 hTailSound.1, hFrameAll⟩

end Anneal.ByteSubLens

end
