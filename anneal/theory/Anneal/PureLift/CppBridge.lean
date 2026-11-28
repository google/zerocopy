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
public import Trusted.MirModel
public import Trusted.CppAst
public import Trusted.CppSemantics
public import Anneal.SpineForce
public import Anneal.CppEquiv
public import Anneal.Framework.StepWp

public section

namespace Anneal.PureLift.CppBridge

open Trusted.MirSemantics
open Trusted.CppAst Trusted.CppSemantics
open Anneal.CppEquiv Anneal.Framework.StepWp Anneal.SpineForce

/-!
# Rung-0 C11 Bridge into the Generic Step Calculus (`Anneal.PureLift.CppBridge`)

Connects the deterministic Rung-0 C11 small-step semantics
(`Trusted.CppSemantics.evalStep`) to the language-agnostic step calculus in
`Anneal.Framework.StepWp`, so C11 bodies captured by `anneal-lower-cpp` are
verified with the same machinery as MIR bodies instead of a parallel C11-only
proof stack.

1. **Step-result bridge (`cppStepMir`).** Reinterprets `evalStep prog` as a
   `StepResult`-valued step function. `cppExec_of_execStepPred` (and its
   demonic form `cppExec_of_wpStepPred`) turns one fault-free `execStepPred`
   run into `CppWellFormed`, `¬ CppDiverges`, a unique `CppBehavior`, and the
   caller's postcondition; `execStepPred_of_cppReaches` is the converse, so
   the bridge loses nothing. `cppFaultsUB_of_execStepPred` is the fault-side
   counterpart, turning a concrete faulting run into a `CppFaultsUB` witness.
2. **Reflective CFG certificate (`cppCfgCheck`).** A `BoolCertCut`-sealed
   checker, built on `SpineForce.checkRange`, certifying that every `goto`,
   `branch`, and `call` continuation of a body is in range. Sealing it once
   per body discharges the target-bounds side condition of every terminator
   step in that body.
3. **Basic-block symbolic-execution rules.** Compositional equations for
   `evalStep` over statements (`evalStep_stmt`, `evalStmt_assign`,
   `evalStmt_storageLive`) and terminators (`evalStep_goto`,
   `evalStep_branch`, `evalStep_ret`), plus value-level helpers
   (`checkCppVal_int`, `writePlaceVal_local`) and `splitBitfield_nil` /
   `splitBitfield_deref`, which discharge the bit-field dispatch for
   projection-free and `*p` places. A per-body proof is a chain of these
   rules whose only residual obligations are the program's own arithmetic
   facts.
-/

/-! ## 1. Step-Result Bridge (`cppStepMir`) -/

/-- Embed a Rung-0 C11 fault classification into the framework `FaultKind`. -/
@[expose] def cppFaultToMir : CppFaultKind → FaultKind
  | .undefined => .undefined
  | .unsupported => .unsupported

/-- Embed a Rung-0 C11 step result into the framework `StepResult`. -/
@[expose] def cppResultToMir {S O : Type} : CppStepResult S O → StepResult S O
  | .step s => .step s
  | .done o => .done o
  | .fault k => .fault (cppFaultToMir k)

/-- `evalStep prog` viewed as a framework step function. -/
@[expose] noncomputable def cppStepMir (prog : CppProgram) (s : CppState) :
    StepResult CppState CppTerminalOut :=
  cppResultToMir (evalStep prog s)

theorem cppStepMir_of_step {prog : CppProgram} {s s' : CppState}
    (h : evalStep prog s = .step s') : cppStepMir prog s = .step s' := by
  unfold cppStepMir
  rw [h]
  rfl

theorem cppStepMir_of_done {prog : CppProgram} {s : CppState}
    {out : CppTerminalOut} (h : evalStep prog s = .done out) :
    cppStepMir prog s = .done out := by
  unfold cppStepMir
  rw [h]
  rfl

theorem cppStepMir_of_fault {prog : CppProgram} {s : CppState}
    {k : CppFaultKind} (h : evalStep prog s = .fault k) :
    cppStepMir prog s = .fault (cppFaultToMir k) := by
  unfold cppStepMir
  rw [h]
  rfl

/-- A fault-free `execStepPred` run over `cppStepMir` reaches a `.done`
transition satisfying `onDone`. -/
theorem cppTerminal_of_execStepPred {prog : CppProgram}
    {onDone : CppState → CppTerminalOut → Prop} :
    ∀ {fuel : Nat} {s : CppState},
      execStepPred (cppStepMir prog) onDone (fun _ _ => False) fuel s →
      ∃ (sEnd : CppState) (out : CppTerminalOut),
        CppReaches prog s sEnd ∧ evalStep prog sEnd = .done out ∧
        onDone sEnd out
  | 0, _, h => False.elim h
  | fuel + 1, s, h => by
    rw [execStepPred_succ_iff] at h
    cases hE : evalStep prog s with
    | step s' =>
      rw [cppStepMir_of_step hE] at h
      have ⟨sEnd, out, hR, hD, hP⟩ := cppTerminal_of_execStepPred h
      exact ⟨sEnd, out, cppReaches_head prog hE hR, hD, hP⟩
    | done out =>
      rw [cppStepMir_of_done hE] at h
      exact ⟨s, out, CppReaches.refl s, hE, h⟩
    | fault k =>
      rw [cppStepMir_of_fault hE] at h
      exact False.elim h

/-- **Bridge soundness.** One fault-free `execStepPred` run from the entry
state yields UB-freedom (`CppWellFormed`), termination (`¬ CppDiverges`), a
unique observable behavior, and the caller's postcondition. -/
theorem cppExec_of_execStepPred {prog : CppProgram} {q : CppQuery}
    {s0 : CppState} {onDone : CppState → CppTerminalOut → Prop} {fuel : Nat}
    (hInit : initCppState prog q = .ok s0)
    (hExec : execStepPred (cppStepMir prog) onDone (fun _ _ => False) fuel s0) :
    ∃ (sEnd : CppState) (out : CppTerminalOut),
      onDone sEnd out ∧
      CppWellFormed prog q ∧ ¬ CppDiverges prog q ∧ CppBehavior prog q out ∧
      (∀ out', CppBehavior prog q out' → out' = out) := by
  have ⟨sEnd, out, hR, hD, hP⟩ := cppTerminal_of_execStepPred hExec
  exact ⟨sEnd, out, hP, cppTerminates_of_trace prog q s0 sEnd out hInit hR hD⟩

/-- `cppStepMir` admits exactly one (trivial) scheduler choice. -/
theorem cppUnitChoice_unique :
    ∀ (_ : CppState) (c : Unit), True ↔ c = ()
  | _, () => ⟨fun _ => rfl, fun _ => True.intro⟩

/-- Demonic-WP form of `cppExec_of_execStepPred`. -/
theorem cppExec_of_wpStepPred {prog : CppProgram} {q : CppQuery}
    {s0 : CppState} {onDone : CppState → CppTerminalOut → Prop} {fuel : Nat}
    (hInit : initCppState prog q = .ok s0)
    (hWp : wpStepPred (fun (_ : CppState) (_ : Unit) => True)
      (fun _ => cppStepMir prog) onDone (fun _ _ => False) fuel s0) :
    ∃ (sEnd : CppState) (out : CppTerminalOut),
      onDone sEnd out ∧
      CppWellFormed prog q ∧ ¬ CppDiverges prog q ∧ CppBehavior prog q out ∧
      (∀ out', CppBehavior prog q out' → out' = out) :=
  cppExec_of_execStepPred hInit
    (execStepPred_of_wpStepPred (step := fun _ => cppStepMir prog)
      cppUnitChoice_unique hWp)

/-- Fault-side soundness: an `execStepPred` run whose only admissible exit is
a fault satisfying `onFault` reaches such a fault (used for UB witnesses). -/
theorem cppFault_of_execStepPred {prog : CppProgram}
    {onFault : CppState → FaultKind → Prop} :
    ∀ {fuel : Nat} {s : CppState},
      execStepPred (cppStepMir prog) (fun _ _ => False) onFault fuel s →
      ∃ (sEnd : CppState) (k : CppFaultKind),
        CppReaches prog s sEnd ∧ evalStep prog sEnd = .fault k ∧
        onFault sEnd (cppFaultToMir k)
  | 0, _, h => False.elim h
  | fuel + 1, s, h => by
    rw [execStepPred_succ_iff] at h
    cases hE : evalStep prog s with
    | step s' =>
      rw [cppStepMir_of_step hE] at h
      have ⟨sEnd, k, hR, hF, hP⟩ := cppFault_of_execStepPred h
      exact ⟨sEnd, k, cppReaches_head prog hE hR, hF, hP⟩
    | done out =>
      rw [cppStepMir_of_done hE] at h
      exact False.elim h
    | fault k =>
      rw [cppStepMir_of_fault hE] at h
      exact ⟨s, k, CppReaches.refl s, hE, h⟩

/-- A fault-only `execStepPred` run classifying the fault as `.undefined`
proves `CppFaultsUB`. -/
theorem cppFaultsUB_of_execStepPred {prog : CppProgram} {q : CppQuery}
    {s0 : CppState} {fuel : Nat}
    (hInit : initCppState prog q = .ok s0)
    (hExec : execStepPred (cppStepMir prog) (fun _ _ => False)
      (fun _ k => k = .undefined) fuel s0) :
    CppFaultsUB prog q := by
  have ⟨sEnd, k, hR, hF, hK⟩ := cppFault_of_execStepPred hExec
  cases k with
  | undefined => exact cppFaultsUB_of_trace prog q s0 sEnd hInit hR hF
  | unsupported => cases hK

/-- **Bridge completeness.** Every finite C11 run ending in `.done out` is an
`execStepPred` run at some fuel. -/
theorem execStepPred_of_cppReaches {prog : CppProgram}
    {onDone : CppState → CppTerminalOut → Prop}
    {onFault : CppState → FaultKind → Prop}
    {s sEnd : CppState} {out : CppTerminalOut}
    (hReach : CppReaches prog s sEnd)
    (hDone : evalStep prog sEnd = .done out) (hPost : onDone sEnd out) :
    ∃ fuel, execStepPred (cppStepMir prog) onDone onFault fuel s := by
  have hLast : execStepPred (cppStepMir prog) onDone onFault 1 sEnd := by
    rw [execStepPred_succ_iff, cppStepMir_of_done hDone]
    exact hPost
  have hGen : ∀ {s₁ s₂ : CppState}, CppReaches prog s₁ s₂ →
      ∀ fuel, execStepPred (cppStepMir prog) onDone onFault fuel s₂ →
        ∃ fuel', execStepPred (cppStepMir prog) onDone onFault fuel' s₁ := by
    intro s₁ s₂ hR
    induction hR with
    | refl => exact fun fuel h => ⟨fuel, h⟩
    | tail _ hStep ih =>
      intro fuel h
      apply ih (fuel + 1)
      rw [execStepPred_succ_iff, cppStepMir_of_step hStep]
      exact h
  exact hGen hReach 1 hLast

/-! ## 2. Reflective CFG Certificate (`cppCfgCheck`, `BoolCertCut`) -/

/-- Every continuation of terminator `t` is a block index below `n`. -/
@[expose] def termTargetsOk (n : Nat) : CppTerminator → Bool
  | .goto t => Nat.blt t n
  | .branch _ t e => Nat.blt t n && Nat.blt e n
  | .call _ _ _ nx => Nat.blt nx n
  | .ret => true
  | .unreachable => true

/-- Per-block target check for block index `i` of `body`. -/
@[expose] noncomputable def cppBlockTargetsOk (body : CppBody) (i : Nat) :
    Bool :=
  match cppGetElem? body.blocks i with
  | some blk => termTargetsOk body.blocks.length blk.term
  | none => false

/-- Whole-body CFG check, iterated with `SpineForce.checkRange` (raw
`@Nat.rec`, zero `._unsafe_rec`). -/
@[expose] noncomputable def cppCfgCheck (body : CppBody) : Bool :=
  checkRange (cppBlockTargetsOk body) body.blocks.length

theorem cppGetElem?_lt {α : Type} :
    ∀ (xs : List α) (i : Nat) (x : α), cppGetElem? xs i = some x → i < xs.length
  | [], _, _, h => by cases h
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: ys, n + 1, x, h => Nat.succ_lt_succ (cppGetElem?_lt ys n x h)

/-- A sealed CFG certificate bounds the terminator targets of every block. -/
theorem cppCfgCheck_block {body : CppBody}
    (hCut : BoolCertCut cppCfgCheck body) {i : Nat} {blk : CppBlock}
    (hBlk : cppGetElem? body.blocks i = some blk) :
    termTargetsOk body.blocks.length blk.term = true := by
  have hChk : cppCfgCheck body = true := BoolCertCut.unseal hCut
  have h : cppBlockTargetsOk body i = true :=
    checkRange_true_imp (cppBlockTargetsOk body) body.blocks.length i
      hChk (cppGetElem?_lt body.blocks i blk hBlk)
  unfold cppBlockTargetsOk at h
  rw [hBlk] at h
  exact h

theorem cppCfg_goto_ok {body : CppBody} (hCut : BoolCertCut cppCfgCheck body)
    {i : Nat} {blk : CppBlock} (hBlk : cppGetElem? body.blocks i = some blk)
    {t : BlockId} (hTerm : blk.term = .goto t) :
    Nat.blt t body.blocks.length = true := by
  have h := cppCfgCheck_block hCut hBlk
  rw [hTerm] at h
  exact h

theorem cppCfg_branch_ok {body : CppBody} (hCut : BoolCertCut cppCfgCheck body)
    {i : Nat} {blk : CppBlock} (hBlk : cppGetElem? body.blocks i = some blk)
    {c : CppExpr} {t e : BlockId} (hTerm : blk.term = .branch c t e)
    (b : Bool) :
    Nat.blt (if b then t else e) body.blocks.length = true := by
  have h := cppCfgCheck_block hCut hBlk
  rw [hTerm] at h
  change
    (Nat.blt t body.blocks.length && Nat.blt e body.blocks.length) = true
    at h
  cases ht : Nat.blt t body.blocks.length with
  | false =>
    rw [ht] at h
    cases h
  | true =>
    rw [ht] at h
    cases b with
    | true => exact ht
    | false => exact h

/-! ## 3. Basic-Block Symbolic-Execution Rules -/

theorem CppIntWidth.beq_refl : ∀ w : CppIntWidth, CppIntWidth.beq w w = true
  | .w8 => rfl
  | .w16 => rfl
  | .w32 => rfl
  | .w64 => rfl
  | .w128 => rfl

theorem Signedness.beq_refl : ∀ s : Signedness, Signedness.beq s s = true
  | .signed => rfl
  | .unsigned => rfl

/-- An in-range integer passes the statement-level value check. -/
theorem checkCppVal_int {policy : CppLangPolicy} {records : List CppRecordDef}
    {w : CppIntWidth} {s : Signedness} {c : Bool} {bits : Nat}
    (h : bits < Nat.pow 2 w.bitWidth) :
    checkCppVal policy records (.int w s bits) (.int w s c) = true := by
  change (CppIntWidth.beq w w && Signedness.beq s s &&
    Nat.blt bits (Nat.pow 2 w.bitWidth)) = true
  rw [CppIntWidth.beq_refl, Signedness.beq_refl, Nat.blt_eq.mpr h]
  rfl

/-- A place with no projections has no bit-field suffix. -/
theorem splitBitfield_nil : splitBitfield [] = none := rfl

/-- An empty projection chain resolves to its starting address. -/
theorem resolveProjChain_nil {prog : CppProgram} {body : CppBody}
    {f : CppFrame} {mem : CppMemory} {forAddrOf : Bool} {cur : ResolvedAddr} :
    resolveProjChain prog body f mem forAddrOf cur [] = .ok cur := rfl

/-- A dereference that is not the operand of `&` is never terminal. -/
theorem notAddrOf_terminal {rest : List CppProjElem} :
    (false && rest.isEmpty) = false := rfl

/-- A single `deref` projection has no bit-field suffix. -/
theorem splitBitfield_deref : splitBitfield [.deref] = none := rfl

/-- Slot `i` of `locs` currently holds a writable immediate (`.uninit` or a
value), so a whole-local store updates it in place. -/
@[expose] def WritableSlot (locs : List CppLocalSlot) (i : Nat) : Prop :=
  cppGetElem? locs i = some .uninit ∨ ∃ w, cppGetElem? locs i = some (.val w)

/-- Storing into a writable immediate non-`const` local of the stored,
padding-free type updates the frame only. -/
theorem writePlaceVal_local {prog : CppProgram} {body : CppBody}
    {f : CppFrame} {mem : CppMemory} {i : Nat} {ty : CppTy} {v : CppVal}
    {d : CppLocalDecl} {locs' : List CppLocalSlot}
    (hDecl : cppGetElem? body.locals i = some d)
    (hTy : CppTy.beq d.ty ty = true)
    (hPad : tyHasNoPadding prog.policy prog.records true 16 d.ty = true)
    (hConst : d.isConst = false)
    (hSlot : WritableSlot f.locals i)
    (hSet : cppSetElem? f.locals i (.val v) = some locs') :
    writePlaceVal prog body f mem { base := i, projs := [] } ty v =
      .ok ({ f with locals := locs' }, mem) := by
  unfold writePlaceVal
  dsimp only
  rw [splitBitfield_nil]
  dsimp only
  rw [hDecl]
  dsimp only
  rw [hTy]
  cases hSlot with
  | inl h =>
    rw [h]
    dsimp only
    rw [hPad, hSet]
    rfl
  | inr h =>
    have ⟨_, hv⟩ := h
    rw [hv]
    dsimp only
    rw [hPad, hConst, hSet]
    rfl

/-! ### Expression rules -/

/-- Reading an initialized immediate local of padding-free type whose
pointers are live. -/
theorem evalExpr_readLocal {prog : CppProgram} {body : CppBody} {f : CppFrame}
    {mem : CppMemory} {i : LocalId} {ty : CppTy} {v : CppVal}
    {d : CppLocalDecl}
    (hDecl : cppGetElem? body.locals i = some d)
    (hTy : CppTy.beq d.ty ty = true)
    (hSlot : cppGetElem? f.locals i = some (.val v))
    (hPad : tyHasNoPadding prog.policy prog.records true 16 d.ty = true)
    (hLive : valLiveInMem prog.policy prog.records mem v d.ty = true) :
    evalExpr prog body f mem (.readPlace { base := i, projs := [] } ty) =
      .ok (v, f, mem) := by
  change readPlaceVal prog body f mem { base := i, projs := [] } ty = _
  unfold readPlaceVal readLocalScalar
  dsimp only
  rw [splitBitfield_nil]
  dsimp only
  rw [hDecl]
  dsimp only
  rw [hTy, hSlot]
  dsimp only
  rw [hPad, hLive]
  rfl

/-- Binary operators over frame- and memory-preserving operands, with a
result of the declared type. -/
theorem evalExpr_binary {prog : CppProgram} {body : CppBody} {f : CppFrame}
    {mem : CppMemory} {op : CppBinOp} {ty : CppTy} {l r : CppExpr}
    {lv rv v : CppVal}
    (hl : evalExpr prog body f mem l = .ok (lv, f, mem))
    (hr : evalExpr prog body f mem r = .ok (rv, f, mem))
    (hop : evalBinOp prog.policy mem op lv rv = .ok v)
    (hTy : binResTyOk op ty v = true) :
    evalExpr prog body f mem (.binary op ty l r) = .ok (v, f, mem) := by
  change (match evalExpr prog body f mem l with
    | .error k => .error k
    | .ok (lv, f1, m1) =>
      match evalExpr prog body f1 m1 r with
      | .error k => .error k
      | .ok (rv, f2, m2) =>
        match evalBinOp prog.policy m2 op lv rv with
        | .ok res =>
          if binResTyOk op ty res then .ok (res, f2, m2)
          else .error .unsupported
        | .error k => .error k :
    Except CppFaultKind (CppVal × CppFrame × CppMemory)) = _
  rw [hl]
  dsimp only
  rw [hr]
  dsimp only
  rw [hop]
  dsimp only
  rw [hTy]
  rfl

/-- Integer conversions (C11 §6.3.1.3) over a matching source type. -/
theorem evalExpr_intCast {prog : CppProgram} {body : CppBody} {f : CppFrame}
    {mem : CppMemory} {fw tw : CppIntWidth} {fs ts : Signedness} {c : Bool}
    {arg : CppExpr} {bits : Nat}
    (h : evalExpr prog body f mem arg = .ok (.int fw fs bits, f, mem)) :
    evalExpr prog body f mem (.intCast fw fs tw ts c arg) =
      .ok (.int tw ts (ofSignedIntWrap tw (cppIntToMathInt fw fs bits)), f,
        mem) := by
  change (match evalExpr prog body f mem arg with
    | .error k => .error k
    | .ok (.int w s bits, f1, m1) =>
      if CppIntWidth.beq w fw && Signedness.beq s fs then
        let x := cppIntToMathInt fw fs bits
        .ok (.int tw ts (ofSignedIntWrap tw x), f1, m1)
      else .error .unsupported
    | .ok (.void, _) | .ok (.bool _, _) | .ok (.ptr _ _ _, _)
    | .ok (.aggregate _, _) => .error .unsupported :
    Except CppFaultKind (CppVal × CppFrame × CppMemory)) = _
  rw [h]
  dsimp only
  rw [CppIntWidth.beq_refl, Signedness.beq_refl]
  rfl

/-- Pointer arithmetic over frame- and memory-preserving operands. -/
theorem evalExpr_ptrAdd {prog : CppProgram} {body : CppBody} {f : CppFrame}
    {mem : CppMemory} {elemTy ty : CppTy} {base off : CppExpr}
    {bv ov r : CppVal}
    (hb : evalExpr prog body f mem base = .ok (bv, f, mem))
    (ho : evalExpr prog body f mem off = .ok (ov, f, mem))
    (hp : ptrAddOffset prog.policy prog.records mem elemTy bv ov = .ok r)
    (hTy : ptrAddTyOk elemTy ty = true) :
    evalExpr prog body f mem (.ptrAdd elemTy ty base off) =
      .ok (r, f, mem) := by
  change (match evalExpr prog body f mem base with
    | .error k => .error k
    | .ok (bv, f1, m1) =>
      match evalExpr prog body f1 m1 off with
      | .error k => .error k
      | .ok (ov, f2, m2) =>
        match ptrAddOffset prog.policy prog.records m2 elemTy bv ov with
        | .ok res =>
          if ptrAddTyOk elemTy ty then .ok (res, f2, m2)
          else .error .unsupported
        | .error k => .error k :
    Except CppFaultKind (CppVal × CppFrame × CppMemory)) = _
  rw [hb]
  dsimp only
  rw [ho]
  dsimp only
  rw [hp]
  dsimp only
  rw [hTy]
  rfl

/-- Reading through a live pointer-typed local (`*p`) whose target passes
`derefCheck`. -/
theorem evalExpr_readDeref {prog : CppProgram} {body : CppBody} {f : CppFrame}
    {mem : CppMemory} {p : LocalId} {ty pointee : CppTy}
    {c1 c2 ma isP cst : Bool}
    {aid : Option Nat} {a sz : Nat} {sr : Option (Nat × Nat)} {v : CppVal}
    (hDecl : cppGetElem? body.locals p =
      some { ty := .ptr pointee c1 c2 ma, isParam := isP, isConst := cst })
    (hSlot : cppGetElem? f.locals p = some (.val (.ptr aid a sr)))
    (hLiveP : valLiveInMem prog.policy prog.records mem (.ptr aid a sr)
      (.ptr pointee c1 c2 ma) = true)
    (hDer : derefCheck prog mem false aid a sr pointee = .ok sz)
    (hRead : readMemory prog.policy prog.records mem aid a ty ma none =
      .ok v) :
    evalExpr prog body f mem (.readPlace { base := p, projs := [.deref] } ty) =
      .ok (v, f, mem) := by
  have hR : readLocalScalar prog body f mem p = .ok (.ptr aid a sr) := by
    unfold readLocalScalar
    rw [hDecl, hSlot]
    dsimp only
    rw [hLiveP]
    rfl
  change readPlaceVal prog body f mem { base := p, projs := [.deref] } ty = _
  unfold readPlaceVal resolvePlaceAddr
  dsimp only
  rw [splitBitfield_deref]
  dsimp only
  rw [hDecl]
  dsimp only
  rw [hR]
  dsimp only
  rw [notAddrOf_terminal, hDer]
  dsimp only
  rw [resolveProjChain_nil]
  dsimp only
  rw [hRead]

/-! ### Statement and terminator rules -/

/-- Statement rule: executing the current statement of the top frame. -/
theorem evalStep_stmt {prog : CppProgram} {f : CppFrame}
    {callers : List CppFrame} {mem : CppMemory} {body : CppBody}
    {blk : CppBlock} {stmt : CppStmt} {f' : CppFrame} {mem' : CppMemory}
    (hBody : cppGetElem? prog.bodies f.defId = some body)
    (hBlk : cppGetElem? body.blocks f.blockId = some blk)
    (hStmt : cppGetElem? blk.stmts f.stmtIdx = some stmt)
    (hEval : evalStmt prog body f mem stmt = .ok (f', mem')) :
    evalStep prog { frames := f :: callers, mem := mem } =
      .step { frames := f' :: callers, mem := mem' } := by
  unfold evalStep
  dsimp only
  rw [hBody]
  dsimp only
  rw [hBlk]
  dsimp only
  rw [hStmt]
  dsimp only
  rw [hEval]

/-- Assignment rule. -/
theorem evalStmt_assign {prog : CppProgram} {body : CppBody} {f : CppFrame}
    {mem : CppMemory} {dst : CppPlace} {ty : CppTy} {e : CppExpr} {v : CppVal}
    {f1 f2 : CppFrame} {m1 m2 : CppMemory}
    (hEval : evalExpr prog body f mem e = .ok (v, f1, m1))
    (hChk : checkCppVal prog.policy prog.records v ty = true)
    (hOv : assignOverlapCheck prog body f1 m1 dst ty e = .ok (f1, m1))
    (hW : writePlaceVal prog body f1 m1 dst ty v = .ok (f2, m2)) :
    evalStmt prog body f mem (.assign dst ty e) =
      .ok ({ f2 with stmtIdx := f2.stmtIdx + 1 }, m2) := by
  unfold evalStmt
  dsimp only
  rw [hEval]
  dsimp only
  rw [hChk]
  rw [hOv]
  dsimp only
  rw [hW]
  rfl

/-- `storageLive` rule. -/
theorem evalStmt_storageLive {prog : CppProgram} {body : CppBody}
    {f : CppFrame} {mem : CppMemory} {lid : LocalId}
    {locs' : List CppLocalSlot}
    (hSet : cppSetElem? f.locals lid .uninit = some locs') :
    evalStmt prog body f mem (.storageLive lid) =
      .ok ({ f with locals := locs', stmtIdx := f.stmtIdx + 1 }, mem) := by
  unfold evalStmt
  dsimp only
  rw [hSet]

/-- Terminator rule: past the last statement, the block terminator runs. -/
theorem evalStep_term {prog : CppProgram} {f : CppFrame}
    {callers : List CppFrame} {mem : CppMemory} {body : CppBody}
    {blk : CppBlock}
    (hBody : cppGetElem? prog.bodies f.defId = some body)
    (hBlk : cppGetElem? body.blocks f.blockId = some blk)
    (hNone : cppGetElem? blk.stmts f.stmtIdx = none) :
    evalStep prog { frames := f :: callers, mem := mem } =
      evalTerminator prog body f callers mem blk.term := by
  unfold evalStep
  dsimp only
  rw [hBody]
  dsimp only
  rw [hBlk]
  dsimp only
  rw [hNone]

/-- `goto` rule, with the target bound discharged by the CFG certificate. -/
theorem evalStep_goto {prog : CppProgram} {f : CppFrame}
    {callers : List CppFrame} {mem : CppMemory} {body : CppBody}
    {blk : CppBlock} {t : BlockId}
    (hCut : BoolCertCut cppCfgCheck body)
    (hBody : cppGetElem? prog.bodies f.defId = some body)
    (hBlk : cppGetElem? body.blocks f.blockId = some blk)
    (hNone : cppGetElem? blk.stmts f.stmtIdx = none)
    (hTerm : blk.term = .goto t) :
    evalStep prog { frames := f :: callers, mem := mem } =
      .step { frames := { f with blockId := t, stmtIdx := 0 } :: callers,
              mem := mem } := by
  rw [evalStep_term hBody hBlk hNone, hTerm]
  unfold evalTerminator
  dsimp only
  rw [cppCfg_goto_ok hCut hBlk hTerm]
  rfl

/-- `branch` rule, with the target bound discharged by the CFG certificate. -/
theorem evalStep_branch {prog : CppProgram} {f : CppFrame}
    {callers : List CppFrame} {mem : CppMemory} {body : CppBody}
    {blk : CppBlock} {c : CppExpr} {t e : BlockId} {b : Bool}
    {f1 : CppFrame} {m1 : CppMemory}
    (hCut : BoolCertCut cppCfgCheck body)
    (hBody : cppGetElem? prog.bodies f.defId = some body)
    (hBlk : cppGetElem? body.blocks f.blockId = some blk)
    (hNone : cppGetElem? blk.stmts f.stmtIdx = none)
    (hTerm : blk.term = .branch c t e)
    (hCond : evalExpr prog body f mem c = .ok (.bool b, f1, m1)) :
    evalStep prog { frames := f :: callers, mem := mem } =
      .step { frames := { f1 with blockId := if b then t else e, stmtIdx := 0 }
                :: callers,
              mem := m1 } := by
  rw [evalStep_term hBody hBlk hNone, hTerm]
  unfold evalTerminator
  dsimp only
  rw [hCond]
  dsimp only
  rw [cppCfg_branch_ok hCut hBlk hTerm b]
  rfl

/-- Top-level `ret` rule for an integer-returning body: the return slot is
read, checked against the return type, and the frame's stack allocations are
released. -/
theorem evalStep_ret {prog : CppProgram} {f : CppFrame} {mem : CppMemory}
    {body : CppBody} {blk : CppBlock} {w : CppIntWidth} {s : Signedness}
    {c : Bool} {v : CppVal}
    (hBody : cppGetElem? prog.bodies f.defId = some body)
    (hBlk : cppGetElem? body.blocks f.blockId = some blk)
    (hNone : cppGetElem? blk.stmts f.stmtIdx = none)
    (hTerm : blk.term = .ret)
    (hRetTy : body.sig.ret = .int w s c)
    (hRead : readLocalScalar prog body f mem 0 = .ok v)
    (hChk : checkCppVal prog.policy prog.records v (.int w s c) = true)
    (hLive : valLiveInMem prog.policy prog.records
      (freeAllocs mem f.stackAllocs) v (.int w s c) = true) :
    evalStep prog { frames := [f], mem := mem } =
      .done (.returned { ret := v, mem := freeAllocs mem f.stackAllocs }) := by
  rw [evalStep_term hBody hBlk hNone, hTerm]
  unfold evalTerminator
  dsimp only
  rw [hRetTy]
  dsimp only
  rw [hRead]
  dsimp only
  rw [hChk]
  rw [hLive]
  rfl

end Anneal.PureLift.CppBridge

end
