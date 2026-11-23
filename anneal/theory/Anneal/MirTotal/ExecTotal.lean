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
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirWp
public import Anneal.MirTotal.StepCore

public section

namespace Anneal.MirTotal

open Trusted.MirAst Trusted.MirSemantics

/-!
# Unbounded-Depth MIR Evaluator and WP Bridges (`MirTotal.ExecTotal`)

Thin terminal `noncomputable` leaf instantiating `MirTotal.StepCore` at
`Trusted.MirAst.MirTy.beq` (`hasIR = false` due to nested inductive `MirTy`,
`Trusted/MirAst.lean:81-90`). Because `MirTy.beq` is already total across
arbitrary `.tuple`, `.ref`, and `.rawPtr` nesting depths, every step,
entry-admission, and `Anneal.MirWp` adequacy bridge holds unconditionally with
zero local-type-support or type-depth side conditions.
-/

/-- Unbounded-depth single-step MIR evaluator instantiating `evalMirStepBy` at
`Trusted.MirAst.MirTy.beq`. -/
@[expose] noncomputable def evalMirStepTotal (p : Program) (c : Choice) (s : State) :
    StepResult State TerminalOut :=
  evalMirStepBy MirTy.beq p c s

/-- Premise-free single-step equivalence between `evalMirStepTotal` and
`Trusted.MirSemantics.evalStep` across all programs, choices, and states. -/
theorem evalMirStepTotal_eq_evalStep (p : Program) (c : Choice) (s : State) :
    evalMirStepTotal p c s = evalStep p c s :=
  evalMirStepBy_eq MirTy.beq (fun _ _ => rfl) p c s

/-- Unbounded-depth fuel-bounded MIR evaluator instantiating `evalMirFuelBy` at
`Trusted.MirAst.MirTy.beq`. -/
@[expose] noncomputable def evalMirFuelTotal (p : Program) (fuel : Nat) (s : State) :
    StepResult State TerminalOut :=
  evalMirFuelBy MirTy.beq p fuel s

/-- Premise-free adequacy bridge from `evalMirFuelTotal` into
`Anneal.MirWp.wpOutcomeState` covering both `.done` and `.fault` outcomes. -/
theorem wpOutcomeState_of_evalMirFuelTotal {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State}
    (h : match evalMirFuelTotal p fuel s with
         | .done out => onDone out
         | .fault k => onFault k
         | .step _ => False) :
    Anneal.MirWp.wpOutcomeState p onDone onFault fuel s :=
  wpOutcomeState_of_evalMirFuelBy (fun _ _ => rfl) h

/-- Lifts a terminating `evalMirFuelTotal` run (`= .done out`) into
`Anneal.MirWp.wpState`. -/
theorem wpState_of_evalMirFuelTotal {p : Program} {fuel : Nat} {s : State}
    {out : TerminalOut} {post : TerminalOut → Prop}
    (hRun : evalMirFuelTotal p fuel s = .done out) (hPost : post out) :
    Anneal.MirWp.wpState p fuel s post := by
  refine wpOutcomeState_of_evalMirFuelTotal ?_
  rw [hRun]
  exact hPost

/-- Lifts a faulting `evalMirFuelTotal` run (`= .fault expected`) into
`Anneal.MirWp.wpFaultState`. -/
theorem wpFaultState_of_evalMirFuelTotal {p : Program} {fuel : Nat} {s : State}
    {expected : FaultKind}
    (hRun : evalMirFuelTotal p fuel s = .fault expected) :
    Anneal.MirWp.wpFaultState p fuel s expected := by
  refine wpOutcomeState_of_evalMirFuelTotal ?_
  rw [hRun]

/-- Unbounded-depth mirror of `Trusted.MirSemantics.checkArgsMatch`. -/
@[expose] noncomputable def checkArgsMatchTotal (vs : List Val) (tys : List MirTy) :
    Bool :=
  checkArgsMatchBy MirTy.beq vs tys

/-- Agreement between `checkArgsMatchTotal` and `checkArgsMatch`. -/
theorem checkArgsMatchTotal_eq (vs : List Val) (tys : List MirTy) :
    checkArgsMatchTotal vs tys = checkArgsMatch vs tys :=
  checkArgsMatchBy_eq MirTy.beq (fun _ _ => rfl) vs tys

/-- Unbounded-depth mirror of `Trusted.MirSemantics.BodyStaticAdmitted`. -/
@[expose] noncomputable def bodyStaticAdmittedTotal (p : Program) (body : Body) : Bool :=
  bodyStaticAdmittedBy MirTy.beq p body

/-- Agreement between `bodyStaticAdmittedTotal` and `BodyStaticAdmitted`. -/
theorem bodyStaticAdmittedTotal_eq (p : Program) (body : Body) :
    bodyStaticAdmittedTotal p body = BodyStaticAdmitted p body :=
  bodyStaticAdmittedBy_eq MirTy.beq (fun _ _ => rfl) p body

/-- Unbounded-depth mirror of `Trusted.MirSemantics.initState`. -/
@[expose] noncomputable def initStateTotal (p : Program) (q : Query) :
    Except FaultKind State :=
  initStateBy MirTy.beq p q

/-- Agreement between `initStateTotal` and `initState`. -/
theorem initStateTotal_eq (p : Program) (q : Query) :
    initStateTotal p q = initState p q :=
  initStateBy_eq MirTy.beq (fun _ _ => rfl) p q

/-- Lifts a program-entry `initStateTotal` + `evalMirFuelTotal` run (`= .done
out`) into `Anneal.MirWp.wpProg`. -/
theorem wpProg_of_evalMirFuelTotal {p : Program} {fuel : Nat} {q : Query}
    {s0 : State} {out : TerminalOut} {post : TerminalOut → Prop}
    (hInit : initStateTotal p q = .ok s0)
    (hRun : evalMirFuelTotal p fuel s0 = .done out)
    (hPost : post out) :
    Anneal.MirWp.wpProg p fuel q post := by
  unfold Anneal.MirWp.wpProg
  rw [← initStateTotal_eq, hInit]
  exact wpState_of_evalMirFuelTotal hRun hPost

/-- Lifts a program-entry `initStateTotal` + `evalMirFuelTotal` run (`= .fault
expected`) into `Anneal.MirWp.wpFaultProg`. -/
theorem wpFaultProg_of_evalMirFuelTotal {p : Program} {fuel : Nat} {q : Query}
    {s0 : State} {expected : FaultKind}
    (hInit : initStateTotal p q = .ok s0)
    (hRun : evalMirFuelTotal p fuel s0 = .fault expected) :
    Anneal.MirWp.wpFaultProg p fuel q expected := by
  unfold Anneal.MirWp.wpFaultProg
  rw [← initStateTotal_eq, hInit]
  exact wpFaultState_of_evalMirFuelTotal hRun

/-- Discharges `Trusted.MirSemantics.BodyVerified` directly from
`initStateTotal` and `evalMirFuelTotal` over `entryProgForBody p defId`. -/
theorem bodyVerified_of_evalMirFuelTotal {p : Program} {defId : DefId}
    {body : Body} {safetyPre : List Val → Prop}
    (hBody : compGetElem? p.bodies defId = some body)
    (hAdm : bodyStaticAdmittedTotal p body = true)
    (hSafe : ∀ args : List Val,
      checkArgsMatchTotal args ((body.locals.drop 1).take body.argumentCount) = true →
      (body.isUnsafe = true → safetyPre args) →
      ∃ (fuel : Nat) (s0 : State) (out : TerminalOut),
        initStateTotal (entryProgForBody p defId) { args := args } = .ok s0 ∧
        evalMirFuelTotal (entryProgForBody p defId) fuel s0 = .done out) :
    BodyVerified p defId body safetyPre := by
  rw [compGetElem?_eq] at hBody
  rw [bodyStaticAdmittedTotal_eq] at hAdm
  refine ⟨hBody, hAdm, ?_⟩
  intro args hValid hUnsafe
  have hArgsC :
      checkArgsMatchTotal args ((body.locals.drop 1).take body.argumentCount) = true := by
    rw [checkArgsMatchTotal_eq]
    exact hValid
  let ⟨fuel, s0, out, hInit, hRun⟩ := hSafe args hArgsC hUnsafe
  have hWp :
      Anneal.MirWp.wpProg (entryProgForBody p defId) fuel { args := args } (fun _ => True) :=
    wpProg_of_evalMirFuelTotal hInit hRun True.intro
  exact (Anneal.MirWp.wellFormed_and_spec_of_wp_base (entryProgForBody p defId)
    { args := args } fuel (fun _ => True) hWp).1.1

end Anneal.MirTotal

end
