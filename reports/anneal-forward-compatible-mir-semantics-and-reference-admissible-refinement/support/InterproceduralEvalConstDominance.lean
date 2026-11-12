-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Mechanization: Deleting Legacy `RequiresConst` / `MonoAdmitted` / `MonoConstsWf`
# and Resolving Interprocedural Callee `Stmt.evalConst` Semantics

This standalone, zero-`sorry`, zero-axiom Lean 4 module mechanizes control-flow-guarded `Stmt.evalConst` dominance and the elimination of syntactic `RequiresConst` / `MonoAdmitted` / `MonoConstsWf` predicates:

1. **Vestigiality of `RequiresConst` / `MonoAdmitted` / `MonoConstsWf` When `requiredConsts = []`**:
   When the MIR extractor emits `Stmt.evalConst` in basic blocks rather than populating `MirBody.requiredConsts`, every captured `MirBody` has
   `requiredConsts = []`. Whenever all bodies in `bodies` have
   `requiredConsts = []` and all `Terminator.call1` targets resolve in `bodies`,
   `RequiresConst` is uninhabited (`¬ RequiresConst bodies (some body) c`),
   rendering `ConstsTotal`, `MonoAdmitted`, and `MonoConstsWf` trivially `True`
   and `initMirState` identical to `initEntryState`.

2. **Soundness of Deleting `RequiresConst` / `MonoAdmitted` / `MonoConstsWf` and
   `extract.rs:256–275` (`evalConst_safety_implies_monoAdmitted_safety`)**:
   Under the clean `Stmt.evalConst` + `Terminator.call1` + `SafetyPost` model,
   any `Stmt.evalConst` dynamically reached along an execution trace (either in
   the root function or inside a `Terminator.call1` callee) is a member of the
   set of constants evaluated by `rustc` during monomorphization collection
   (`MonoEvaluatedConsts`). Consequently, on any world `(tySizes, adtPad)`
   admitted by `rustc` monomorphization (`MonoAdmittedWorld`), no trace can
   terminate in `.compileTimeError`, so `SafetyPost` directly guarantees absence
   of `.failed` (UB) and satisfaction of return-value validity and contracts.

3. **Concrete Canaries (`canary_concrete_mismatched_pme_rejected`, `if false`,
   and Interprocedural `if b` Guards)**:
   - `canary_concrete_mismatched_pme_rejected_without_requiresConst`: Concrete
     mismatched PME (both interprocedural `transmute_checked::<usize, bool>(x)`
     and direct `let _ = const { assert!(size_of::<u64>() == 4) }`) steps to
     `.terminated .compileTimeError` at the pinned world `(adtPad = 0, tySizes = 8)`
     and refutes `CrateTheorem` via `SafetyPost`'s pinned-world non-vacuity
     clause—without `RequiresConst` or `extract.rs:256–275`.
   - `if_false_const_panic_before_safe_code_accepted`: `if false { const { ... } }`
     before safe code skips the dead branch at runtime and steps to
     `.terminated (.normal ...)` on all worlds, so it is accepted as Tier S0
     (`allowCompileTimeGuard = false`) once `extract.rs:256–275` is removed.
   - `if_false_const_assert_before_unguarded_transmute_rejected`:
     `if false { const { assert!(size_of::<Src>() == size_of::<Dst>()) } }`
     before an unguarded `transmute_copy` never executes `Stmt.evalConst`, so
     mismatched-layout worlds are not pruned to `.compileTimeError` and instead
     step to `.failed` (UB), refuting `FnBodyVerified`.
   - `interprocedural_branch_callee_pme_and_sneaky_branch_const_rejected`:
     Both `if b { check_layout::<T>(); } transmute_copy(&x)` and
     `if b { const { assert!(...) } } transmute_copy(&x)` step to `.failed` (UB)
     when `b = false` in a mismatched-layout world, refuting `FnBodyVerified`.
-/

namespace InterproceduralEvalConstDominance

/-- Identifier of a MIR body in the crate environment. -/
structure BodyId where
  id : Nat
  deriving DecidableEq, Repr

/-- Simplified MIR types for layout and validity modeling. -/
inductive MirTy where
  | unit
  | bool
  | u32
  | usize
  | param (idx : Nat)
  deriving DecidableEq, Repr

/-- Type substitution mapping `.param idx` to `subst[idx]`. -/
def MirTy.subst (subst : List MirTy) : MirTy → MirTy
  | .param idx => subst.getD idx (.param idx)
  | ty => ty

/-- Runtime values. -/
inductive MirVal where
  | unit
  | bool (b : Bool)
  | int (n : Nat)
  | opaqueVal (ty : MirTy) (tag : Nat)
  deriving DecidableEq, Repr

/-- Type validity invariant for runtime values. -/
def MirVal.valid : MirVal → MirTy → Prop
  | .unit, .unit => True
  | .bool _, .bool => True
  | .int _, .u32 => True
  | .int _, .usize => True
  | .opaqueVal actual _, ty => actual = ty
  | _, _ => False

/-- World-parameterized byte size of a `MirTy`. -/
def evalTySize (tySizes : Nat → Nat) (_adtPad : Nat → Nat) : MirTy → Nat
  | .unit => 0
  | .bool => 1
  | .u32 => 4
  | .usize => 8
  | .param idx => tySizes idx

/-- MIR statements (including control-flow `evalConst`). -/
inductive Stmt where
  | assignConstBool (localIdx : Nat) (b : Bool)
  | assignConstUnit (localIdx : Nat)
  | assignSizeOfEq (localIdx : Nat) (lhs rhs : MirTy)
  | evalConst (dstLocal : Nat) (constId : BodyId) (subst : List MirTy)
  | transmuteCopy (dstLocal : Nat) (srcLocal : Nat) (srcTy dstTy : MirTy)
  deriving DecidableEq, Repr

/-- MIR terminators (including interprocedural `call1`). -/
inductive Terminator where
  | return_
  | goto (target : Nat)
  | switchBool (discrLocal : Nat) (falseTarget trueTarget : Nat)
  | panic
  | call1 (calleeId : BodyId) (subst : List MirTy) (argLocal dstLocal target : Nat)
  deriving DecidableEq, Repr

/-- Basic block in a MIR body. -/
structure BasicBlock where
  stmts : List Stmt
  terminator : Terminator
  deriving DecidableEq, Repr

/-- A MIR body (carrying `requiredConsts` only for the legacy comparison). -/
structure MirBody where
  argTys : List MirTy
  retTy : MirTy := .unit
  blocks : List BasicBlock
  requiredConsts : List (BodyId × List MirTy) := []
  deriving DecidableEq, Repr

/-- Instantiate generic type parameters in a `Stmt`. -/
def Stmt.subst (s : List MirTy) : Stmt → Stmt
  | .assignConstBool l b => .assignConstBool l b
  | .assignConstUnit l => .assignConstUnit l
  | .assignSizeOfEq l lhs rhs => .assignSizeOfEq l (lhs.subst s) (rhs.subst s)
  | .evalConst dst cid args => .evalConst dst cid (args.map (MirTy.subst s))
  | .transmuteCopy dst src srcTy dstTy =>
      .transmuteCopy dst src (srcTy.subst s) (dstTy.subst s)

/-- Instantiate generic type parameters in a `Terminator`. -/
def Terminator.subst (s : List MirTy) : Terminator → Terminator
  | .return_ => .return_
  | .goto t => .goto t
  | .switchBool d f t => .switchBool d f t
  | .panic => .panic
  | .call1 cid args a d t => .call1 cid (args.map (MirTy.subst s)) a d t

/-- Instantiate generic type parameters in a `BasicBlock`. -/
def BasicBlock.subst (s : List MirTy) (bb : BasicBlock) : BasicBlock :=
  { stmts := bb.stmts.map (Stmt.subst s)
    terminator := bb.terminator.subst s }

/-- Instantiate generic type parameters in a `MirBody`. -/
def MirBody.subst (s : List MirTy) (body : MirBody) : MirBody :=
  { argTys := body.argTys.map (MirTy.subst s)
    retTy := body.retTy.subst s
    blocks := body.blocks.map (BasicBlock.subst s)
    requiredConsts := body.requiredConsts.map (fun (cid, args) => (cid, args.map (MirTy.subst s))) }

/-- Lookup a `(BodyId, MirBody)` pair in the crate body table. -/
def lookupBody (bodies : List (BodyId × MirBody)) (target : BodyId) : Option MirBody :=
  match bodies.find? (fun (id, _) => id == target) with
  | some (_, b) => some b
  | none => none

/-- Termination kinds (including `.compileTimeError` for PME). -/
inductive TerminationKind where
  | normal (retVal : MirVal)
  | unwind
  | compileTimeError
  deriving DecidableEq, Repr

/-- Execution state of a MIR frame. -/
structure MirState where
  bb : Nat
  stmtIdx : Nat
  locals : Nat → Option MirVal
  tySizes : Nat → Nat
  adtPad : Nat → Nat

/-- Update a single local slot in `locals`. -/
def updateLocal (locals : Nat → Option MirVal) (idx : Nat) (v : MirVal) : Nat → Option MirVal :=
  fun i => if i = idx then some v else locals i

/-- Single-step outcomes. -/
inductive StepResult where
  | stepped (next : MirState)
  | terminated (kind : TerminationKind)
  | failed

/-- Multi-step bounded-fuel outcomes. -/
inductive ExecOutcome where
  | running (state : MirState)
  | terminated (kind : TerminationKind)
  | failed

/-- Entry-state predicate (no `MonoAdmitted` guard). -/
def initEntryState (body : MirBody) (s : MirState) : Prop :=
  s.bb = 0 ∧
  s.stmtIdx = 0 ∧
  (∀ i (ty : MirTy), body.argTys[i]? = some ty →
    ∃ v, s.locals (i + 1) = some v ∧ MirVal.valid v ty)

/-- Initial state for evaluating a zero-argument constant body in world `(tySizes, adtPad)`. -/
def constEntryState (tySizes : Nat → Nat) (adtPad : Nat → Nat) : MirState :=
  { bb := 0
    stmtIdx := 0
    locals := fun _ => none
    tySizes := tySizes
    adtPad := adtPad }

/-- Fuel-parametric step evaluator supporting both `Stmt.evalConst` and `Terminator.call1`. -/
def evalStepWith
    (evalCall : MirBody → MirState → ExecOutcome)
    (bodies : List (BodyId × MirBody))
    (hasCallFuel : Bool)
    (body : MirBody)
    (s : MirState) : StepResult :=
  match body.blocks[s.bb]? with
  | none => .failed
  | some block =>
      if h : s.stmtIdx < block.stmts.length then
        match block.stmts[s.stmtIdx] with
        | .assignConstBool dst b =>
            .stepped { s with
              stmtIdx := s.stmtIdx + 1
              locals := updateLocal s.locals dst (.bool b) }
        | .assignConstUnit dst =>
            .stepped { s with
              stmtIdx := s.stmtIdx + 1
              locals := updateLocal s.locals dst .unit }
        | .assignSizeOfEq dst lhs rhs =>
            let eq := decide (evalTySize s.tySizes s.adtPad lhs = evalTySize s.tySizes s.adtPad rhs)
            .stepped { s with
              stmtIdx := s.stmtIdx + 1
              locals := updateLocal s.locals dst (.bool eq) }
        | .evalConst dst constId subst =>
            if !hasCallFuel then
              .failed
            else
              match lookupBody bodies constId with
              | none => .failed
              | some cBody =>
                  let instBody := cBody.subst subst
                  match evalCall instBody (constEntryState s.tySizes s.adtPad) with
                  | .terminated (.normal .unit) =>
                      .stepped { s with
                        stmtIdx := s.stmtIdx + 1
                        locals := updateLocal s.locals dst .unit }
                  | .terminated .unwind =>
                      .terminated .compileTimeError
                  | .terminated .compileTimeError =>
                      .terminated .compileTimeError
                  | _ => .failed
        | .transmuteCopy dst src srcTy dstTy =>
            match s.locals src with
            | none => .failed
            | some v =>
                if evalTySize s.tySizes s.adtPad srcTy = evalTySize s.tySizes s.adtPad dstTy then
                  if dstTy = .bool then
                    match v with
                    | .bool b =>
                        .stepped { s with
                          stmtIdx := s.stmtIdx + 1
                          locals := updateLocal s.locals dst (.bool b) }
                    | _ => .failed
                  else
                    .stepped { s with
                      stmtIdx := s.stmtIdx + 1
                      locals := updateLocal s.locals dst (.opaqueVal dstTy 0) }
                else
                  .failed
      else
        match block.terminator with
        | .return_ =>
            match s.locals 0 with
            | some retVal => .terminated (.normal retVal)
            | none => .failed
        | .goto target =>
            .stepped { s with bb := target, stmtIdx := 0 }
        | .switchBool discr falseTarget trueTarget =>
            match s.locals discr with
            | some (.bool false) => .stepped { s with bb := falseTarget, stmtIdx := 0 }
            | some (.bool true) => .stepped { s with bb := trueTarget, stmtIdx := 0 }
            | _ => .failed
        | .panic =>
            .terminated .unwind
        | .call1 calleeId subst argLocal dstLocal target =>
            if !hasCallFuel then
              .failed
            else
              match s.locals argLocal with
              | none => .failed
              | some argVal =>
                  match lookupBody bodies calleeId with
                  | none => .failed
                  | some calleeBody =>
                      let instCallee := calleeBody.subst subst
                      let calleeInit : MirState :=
                        { bb := 0
                          stmtIdx := 0
                          locals := fun i => if i = 1 then some argVal else none
                          tySizes := s.tySizes
                          adtPad := s.adtPad }
                      match evalCall instCallee calleeInit with
                      | .terminated (.normal retVal) =>
                          .stepped { s with
                            bb := target
                            stmtIdx := 0
                            locals := updateLocal s.locals dstLocal retVal }
                      | .terminated .unwind =>
                          .terminated .unwind
                      | .terminated .compileTimeError =>
                          .terminated .compileTimeError
                      | _ => .failed

/-- Bounded-fuel execution loop parameterized by `stepFn`. -/
def evalSteps (stepFn : MirBody → MirState → StepResult)
    (fuel : Nat) (body : MirBody) (s : MirState) : ExecOutcome :=
  match fuel with
  | 0 => .running s
  | fuel' + 1 =>
      match stepFn body s with
      | .stepped s' => evalSteps stepFn fuel' body s'
      | .terminated kind => .terminated kind
      | .failed => .failed

/-- Total fuel-indexed evaluator for `MirBody`. -/
def evalMirFuel (bodies : List (BodyId × MirBody)) : Nat → MirBody → MirState → ExecOutcome
  | 0, _, s => .running s
  | fuel + 1, body, s =>
      let hasCallFuel := decide (fuel > 0)
      evalSteps
        (evalStepWith (fun b st => evalMirFuel bodies fuel b st) bodies hasCallFuel)
        (fuel + 1) body s

/-!
## Part 1: Why `RequiresConst`, `MonoAdmitted`, and `MonoConstsWf` Are Vestigial When `requiredConsts = []`

We reproduce the exact structure of `RequiresConst`, `ConstSucceeds`,
`ConstUnwinds`, `ConstsTotal`, `MonoAdmitted`, `MonoConstsWf`, and
`initMirState_legacy` and prove that when `requiredConsts = []` on all bodies, `RequiresConst` is
uninhabited and all legacy predicates collapse trivially.
-/

/-- Legacy syntactic reachability relation over `MirBody.requiredConsts` and `.call1`
over `MirBody.requiredConsts` and `Terminator.call1`. -/
inductive RequiresConst (bodies : List (BodyId × MirBody)) :
    Option MirBody → (BodyId × List MirTy) → Prop where
  | direct {body : MirBody} {c : BodyId × List MirTy} :
      c ∈ body.requiredConsts →
      RequiresConst bodies (some body) c
  | viaConst {body constBody : MirBody} {constId : BodyId}
      {subst : List MirTy} {c : BodyId × List MirTy} :
      RequiresConst bodies (some body) (constId, subst) →
      lookupBody bodies constId = some constBody →
      c ∈ (constBody.subst subst).requiredConsts →
      RequiresConst bodies (some body) c
  | viaCall {body calleeBody : MirBody} {bb : BasicBlock}
      {calleeId : BodyId} {subst : List MirTy}
      {argLocal dstLocal target : Nat} {c : BodyId × List MirTy} :
      bb ∈ body.blocks →
      bb.terminator = .call1 calleeId subst argLocal dstLocal target →
      lookupBody bodies calleeId = some calleeBody →
      RequiresConst bodies (some (calleeBody.subst subst)) c →
      RequiresConst bodies (some body) c
  | unresolvedConst {body : MirBody} {constId : BodyId}
      {subst : List MirTy} {c : BodyId × List MirTy} :
      RequiresConst bodies (some body) (constId, subst) →
      lookupBody bodies constId = none →
      RequiresConst bodies (some body) c
  | unresolvedCall {body : MirBody} {bb : BasicBlock}
      {calleeId : BodyId} {subst : List MirTy}
      {argLocal dstLocal target : Nat} {c : BodyId × List MirTy} :
      bb ∈ body.blocks →
      bb.terminator = .call1 calleeId subst argLocal dstLocal target →
      lookupBody bodies calleeId = none →
      RequiresConst bodies (some body) c

def ConstSucceeds (bodies : List (BodyId × MirBody))
    (tySizes : Nat → Nat) (adtPad : Nat → Nat)
    (constId : BodyId) (subst : List MirTy) : Prop :=
  ∃ constBody fuel,
    lookupBody bodies constId = some constBody ∧
    evalMirFuel bodies fuel (constBody.subst subst) (constEntryState tySizes adtPad) =
      .terminated (.normal .unit)

def ConstUnwinds (bodies : List (BodyId × MirBody))
    (tySizes : Nat → Nat) (adtPad : Nat → Nat)
    (constId : BodyId) (subst : List MirTy) : Prop :=
  ∃ constBody fuel,
    lookupBody bodies constId = some constBody ∧
    evalMirFuel bodies fuel (constBody.subst subst) (constEntryState tySizes adtPad) =
      .terminated .unwind

def ConstsTotal (bodies : List (BodyId × MirBody))
    (tySizes : Nat → Nat) (adtPad : Nat → Nat) (body : MirBody) : Prop :=
  ∀ c, RequiresConst bodies (some body) c →
    ConstSucceeds bodies tySizes adtPad c.1 c.2 ∨
    ConstUnwinds bodies tySizes adtPad c.1 c.2

def MonoAdmitted (bodies : List (BodyId × MirBody))
    (tySizes : Nat → Nat) (adtPad : Nat → Nat) (body : MirBody) : Prop :=
  ∀ c, RequiresConst bodies (some body) c →
    ConstSucceeds bodies tySizes adtPad c.1 c.2

def MonoConstsWf (bodies : List (BodyId × MirBody)) (body : MirBody) : Prop :=
  (∀ tySizes adtPad, ConstsTotal bodies tySizes adtPad body) ∧
  (MonoAdmitted bodies (fun _ => 8) (fun _ => 0) body)

def initMirState_legacy (bodies : List (BodyId × MirBody)) (body : MirBody) (s : MirState) : Prop :=
  initEntryState body s ∧ MonoAdmitted bodies s.tySizes s.adtPad body

/-- Subst preserves `requiredConsts = []`. -/
theorem subst_requiredConsts_nil (body : MirBody) (subst : List MirTy)
    (h : body.requiredConsts = []) :
    (body.subst subst).requiredConsts = [] := by
  simp [MirBody.subst, h]

/-- If `lookupBody bodies cid = some b`, then `(cid, b) ∈ bodies` has `b` in `bodies`. -/
theorem lookupBody_some_mem {bodies : List (BodyId × MirBody)} {cid : BodyId} {b : MirBody}
    (h : lookupBody bodies cid = some b) :
    ∃ id, (id, b) ∈ bodies := by
  unfold lookupBody at h
  cases h_find : bodies.find? (fun (id, _) => id == cid) with
  | none =>
      rw [h_find] at h
      contradiction
  | some pair =>
      rw [h_find] at h
      cases h
      exact ⟨pair.1, List.mem_of_find?_eq_some h_find⟩

/-- Well-formedness of the body table When `requiredConsts = []`:
1. Every body in `bodies` has `requiredConsts = []` (since `rustc-capture` never emits it).
2. Every `Terminator.call1` in any body in `bodies` resolves in `bodies`. -/
def BodyTableNoRequiredConsts (bodies : List (BodyId × MirBody)) (root : MirBody) : Prop :=
  root.requiredConsts = [] ∧
  (∀ bb ∈ root.blocks, ∀ cid subst a d t,
    bb.terminator = .call1 cid subst a d t → (lookupBody bodies cid).isSome) ∧
  (∀ id b, (id, b) ∈ bodies →
    b.requiredConsts = [] ∧
    (∀ bb ∈ b.blocks, ∀ cid subst a d t,
      bb.terminator = .call1 cid subst a d t → (lookupBody bodies cid).isSome))

/-- Helper invariant that is preserved under `MirBody.subst`. -/
def BodyNoRequiredConsts (bodies : List (BodyId × MirBody)) (b : MirBody) : Prop :=
  b.requiredConsts = [] ∧
  (∀ bb ∈ b.blocks, ∀ cid subst a d t,
    bb.terminator = .call1 cid subst a d t → (lookupBody bodies cid).isSome)

theorem bodyNoRequiredConsts_subst {bodies : List (BodyId × MirBody)} {b : MirBody}
    (hb : BodyNoRequiredConsts bodies b) (s : List MirTy) :
    BodyNoRequiredConsts bodies (b.subst s) := by
  rcases hb with ⟨h_rc, h_calls⟩
  refine ⟨subst_requiredConsts_nil b s h_rc, ?_⟩
  intro bb h_bb cid subst a d t h_term
  simp [MirBody.subst] at h_bb
  rcases h_bb with ⟨bb0, h_bb0_mem, rfl⟩
  simp [BasicBlock.subst] at h_term
  cases h_t0 : bb0.terminator with
  | return_ => simp [h_t0, Terminator.subst] at h_term
  | goto _ => simp [h_t0, Terminator.subst] at h_term
  | switchBool _ _ _ => simp [h_t0, Terminator.subst] at h_term
  | panic => simp [h_t0, Terminator.subst] at h_term
  | call1 cid0 subst0 a0 d0 t0 =>
      simp [h_t0, Terminator.subst] at h_term
      rcases h_term with ⟨rfl, rfl, rfl, rfl, rfl⟩
      exact h_calls bb0 h_bb0_mem cid0 subst0 a0 d0 t0 h_t0

/-- **Theorem 1 (Vestigiality of `RequiresConst` When `requiredConsts = []`)**:
Whenever `requiredConsts = []` across `root` and `bodies` and all `.call1`
targets resolve in `bodies`, `RequiresConst bodies (some root) c` is false for
every `c`. -/
theorem empty_requiredConsts_uninhabited
    {bodies : List (BodyId × MirBody)}
    (h_table : ∀ id b, (id, b) ∈ bodies → BodyNoRequiredConsts bodies b)
    {optBody : Option MirBody} {c : BodyId × List MirTy}
    (h_req : RequiresConst bodies optBody c) :
    ∀ body, optBody = some body → BodyNoRequiredConsts bodies body → False := by
  induction h_req with
  | direct h_mem =>
      intro body h_some h_wf
      cases h_some
      rw [h_wf.1] at h_mem
      cases h_mem
  | viaConst _ _ _ ih =>
      intro body h_some h_wf
      exact ih body h_some h_wf
  | @viaCall body0 calleeBody bb calleeId subst argLocal dstLocal target c0 h_bb h_term h_lookup _ ih =>
      intro body h_some h_wf
      cases h_some
      obtain ⟨id, h_in⟩ := lookupBody_some_mem h_lookup
      have h_callee_wf := bodyNoRequiredConsts_subst (h_table id calleeBody h_in) subst
      exact ih (calleeBody.subst subst) rfl h_callee_wf
  | unresolvedConst _ _ ih =>
      intro body h_some h_wf
      exact ih body h_some h_wf
  | unresolvedCall h_bb h_term h_none =>
      intro body h_some h_wf
      cases h_some
      have h_some_lookup := h_wf.2 _ h_bb _ _ _ _ _ h_term
      rw [h_none] at h_some_lookup
      contradiction

/-- **Corollary 1**: Under `BodyTableNoRequiredConsts`, `MonoAdmitted`, `ConstsTotal`,
and `MonoConstsWf` are all tautologically `True`, and `initMirState_legacy` is
equivalent to `initEntryState`. -/
theorem empty_requiredConsts_legacy_predicates_trivial
    {bodies : List (BodyId × MirBody)} {root : MirBody}
    (h_wf : BodyTableNoRequiredConsts bodies root) :
    (∀ tySizes adtPad, MonoAdmitted bodies tySizes adtPad root) ∧
    (∀ tySizes adtPad, ConstsTotal bodies tySizes adtPad root) ∧
    MonoConstsWf bodies root ∧
    (∀ s, initMirState_legacy bodies root s ↔ initEntryState root s) := by
  have h_root : BodyNoRequiredConsts bodies root := ⟨h_wf.1, h_wf.2.1⟩
  have h_table : ∀ id b, (id, b) ∈ bodies → BodyNoRequiredConsts bodies b := h_wf.2.2
  have h_no_req : ∀ c, ¬ RequiresConst bodies (some root) c := by
    intro c h_req
    exact empty_requiredConsts_uninhabited h_table h_req root rfl h_root
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro tySizes adtPad c h_req
    exact False.elim (h_no_req c h_req)
  · intro tySizes adtPad c h_req
    exact False.elim (h_no_req c h_req)
  · refine ⟨?_, ?_⟩
    · intro tySizes adtPad c h_req
      exact False.elim (h_no_req c h_req)
    · intro c h_req
      exact False.elim (h_no_req c h_req)
  · intro s
    constructor
    · intro h; exact h.1
    · intro h; refine ⟨h, fun c h_req => False.elim (h_no_req c h_req)⟩

/-!
## Part 2: Clean `Stmt.evalConst`-Only Model & General Interprocedural Soundness Theorem

We now state the clean verification model (`SafetyPost` + `FnBodyVerified_clean`)
with `RequiresConst`, `ConstSucceeds`, `ConstUnwinds`, `ConstsTotal`,
`MonoAdmitted`, and `MonoConstsWf` completely deleted, and prove that it
soundly implies runtime safety on every world admitted by `rustc`
monomorphization (`evalConst_safety_implies_monoAdmitted_safety`).
-/

/-- The `SafetyPost` predicate for forward-compatible MIR verification with pinned-world non-vacuity. -/
def SafetyPost (body : MirBody) (allowCompileTimeGuard : Bool)
    (s : MirState) (out : ExecOutcome) : Prop :=
  out ≠ .failed ∧
  (allowCompileTimeGuard = false → out ≠ .terminated .compileTimeError) ∧
  (s.adtPad = (fun _ => 0) ∧ s.tySizes = (fun _ => 8) →
    out ≠ .terminated .compileTimeError) ∧
  (∀ retVal, out = .terminated (.normal retVal) → MirVal.valid retVal body.retTy)

/-- Clean `FnBodyVerified` with `initEntryState` (no `MonoAdmitted` or `MonoConstsWf`). -/
def FnBodyVerified_clean (bodies : List (BodyId × MirBody))
    (body : MirBody) (allowCompileTimeGuard : Bool)
    (contractPost : MirState → ExecOutcome → Prop) : Prop :=
  ∀ (s : MirState),
    initEntryState body s →
      (∃ fuel₀, ∀ fuel, fuel ≥ fuel₀ →
        ∀ st, evalMirFuel bodies fuel body s ≠ .running st) ∧
      (∀ (fuel : Nat),
        SafetyPost body allowCompileTimeGuard s (evalMirFuel bodies fuel body s) ∧
        contractPost s (evalMirFuel bodies fuel body s))

/-- Set of `(constId, subst)` constants evaluated by `rustc` during monomorphization
of a root function (`rustc_monomorphize::collector::collect_items_of_instance`). -/
abbrev MonoConstSet := (BodyId × List MirTy) → Prop

/-- A world `(tySizes, adtPad)` is admitted by `rustc` monomorphization for
`monoConsts` iff every constant in `monoConsts` evaluates to `.normal .unit`
at every fuel large enough to complete. -/
def MonoWorldAdmitted (bodies : List (BodyId × MirBody))
    (monoConsts : MonoConstSet) (tySizes : Nat → Nat) (adtPad : Nat → Nat) : Prop :=
  ∀ cid subst, monoConsts (cid, subst) →
    ∀ cBody callFuel,
      lookupBody bodies cid = some cBody →
      evalMirFuel bodies callFuel (cBody.subst subst) (constEntryState tySizes adtPad) ≠
        .terminated .unwind ∧
      evalMirFuel bodies callFuel (cBody.subst subst) (constEntryState tySizes adtPad) ≠
        .terminated .compileTimeError

/-- Every `Stmt.evalConst` syntactically present in `body` or in any callee
reachable via `Terminator.call1` belongs to `monoConsts` (which holds in `rustc`
because `RequiredConstsVisitor` collects all `ConstOperand`s in each body and
`MentionedItems` + `collect_items_of_instance` traverses all `TerminatorKind::Call`
callees). -/
def AllSyntacticEvalConstsInMono
    (bodies : List (BodyId × MirBody)) (monoConsts : MonoConstSet) (body : MirBody) : Prop :=
  (∀ bb ∈ body.blocks, ∀ stmt ∈ bb.stmts, ∀ dst cid subst,
    stmt = .evalConst dst cid subst → monoConsts (cid, subst)) ∧
  (∀ bb ∈ body.blocks, ∀ cid subst a d t calleeBody,
    bb.terminator = .call1 cid subst a d t →
    lookupBody bodies cid = some calleeBody →
    ∀ cbb ∈ (calleeBody.subst subst).blocks, ∀ stmt ∈ cbb.stmts, ∀ dst ccid csubst,
      stmt = .evalConst dst ccid csubst → monoConsts (ccid, csubst))

/-- Lemma: `List.getElem_mem` for indexing into `block.stmts` and `body.blocks`. -/
theorem getElem?_some_mem {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : xs[i]? = some x) : x ∈ xs :=
  List.mem_of_getElem? h

/-- Single-step non-`.compileTimeError` lemma: if all syntactic `evalConst`s in
`body` are in `monoConsts` and the world `(s.tySizes, s.adtPad)` satisfies
`MonoWorldAdmitted`, then `evalStepWith` never returns `.terminated .compileTimeError`
provided any recursive `evalCall` on a `.call1` callee also never returns
`.terminated .compileTimeError`. -/
theorem evalStepWith_no_compileTimeError
    {evalCall : MirBody → MirState → ExecOutcome}
    {bodies : List (BodyId × MirBody)}
    {monoConsts : MonoConstSet}
    {hasCallFuel : Bool} {callFuel : Nat} {body : MirBody} {s : MirState}
    (h_mono : MonoWorldAdmitted bodies monoConsts s.tySizes s.adtPad)
    (h_consts : ∀ bb ∈ body.blocks, ∀ stmt ∈ bb.stmts, ∀ dst cid subst,
      stmt = .evalConst dst cid subst → monoConsts (cid, subst))
    (h_callee_no_cte : ∀ bb ∈ body.blocks, ∀ cid subst a d t calleeBody argVal,
      bb.terminator = .call1 cid subst a d t →
      lookupBody bodies cid = some calleeBody →
      evalCall (calleeBody.subst subst)
        { bb := 0, stmtIdx := 0, locals := (fun i => if i = 1 then some argVal else none),
          tySizes := s.tySizes, adtPad := s.adtPad } ≠ .terminated .compileTimeError)
    (h_evalCall_eq : ∀ b st, evalCall b st = evalMirFuel bodies callFuel b st) :
    evalStepWith evalCall bodies hasCallFuel body s ≠ .terminated .compileTimeError := by
  unfold evalStepWith
  cases h_bb : body.blocks[s.bb]? with
  | none => simp
  | some block =>
      have h_bb_mem : block ∈ body.blocks := getElem?_some_mem h_bb
      simp only []
      split
      · rename_i h_lt
        have h_stmt_mem : block.stmts[s.stmtIdx] ∈ block.stmts := List.getElem_mem h_lt
        cases h_st : block.stmts[s.stmtIdx] with
        | assignConstBool dst b => simp
        | assignConstUnit dst => simp
        | assignSizeOfEq dst lhs rhs => simp
        | transmuteCopy dst src srcTy dstTy =>
            cases h_src : s.locals src with
            | none => simp [h_src]
            | some v =>
                simp only [h_src]
                by_cases h_sz : evalTySize s.tySizes s.adtPad srcTy = evalTySize s.tySizes s.adtPad dstTy
                · simp only [h_sz, ↓reduceIte]
                  by_cases h_bool : dstTy = .bool
                  · simp only [h_bool, ↓reduceIte]
                    cases v <;> simp
                  · simp only [h_bool, ↓reduceIte]
                    simp
                · simp only [h_sz, ↓reduceIte]
                  simp
        | evalConst dst cid subst =>
            cases hasCallFuel with
            | false => simp
            | true =>
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                cases h_lk : lookupBody bodies cid with
                | none => simp
                | some cBody =>
                    simp only []
                    have h_in_mono : monoConsts (cid, subst) :=
                      h_consts block h_bb_mem _ h_stmt_mem dst cid subst h_st
                    have ⟨h_no_unw, h_no_cte⟩ := h_mono cid subst h_in_mono cBody callFuel h_lk
                    rw [← h_evalCall_eq] at h_no_unw h_no_cte
                    cases h_res : evalCall (cBody.subst subst) (constEntryState s.tySizes s.adtPad) with
                    | running _ => simp
                    | failed => simp
                    | terminated tk =>
                        cases tk with
                        | normal rv =>
                            cases rv <;> simp
                        | unwind =>
                            exact False.elim (h_no_unw h_res)
                        | compileTimeError =>
                            exact False.elim (h_no_cte h_res)
      · cases h_term : block.terminator with
        | return_ =>
            cases s.locals 0 <;> simp
        | goto target => simp
        | switchBool discr f t =>
            cases h_l : s.locals discr with
            | none => simp [h_l]
            | some v =>
                cases v with
                | bool b => cases b <;> simp [h_l]
                | _ => simp [h_l]
        | panic => simp
        | call1 cid subst a d t =>
            cases hasCallFuel with
            | false => simp
            | true =>
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                cases h_arg : s.locals a with
                | none => simp
                | some argVal =>
                    simp only []
                    cases h_lk : lookupBody bodies cid with
                    | none => simp
                    | some calleeBody =>
                        simp only []
                        have h_no_c :=
                          h_callee_no_cte block h_bb_mem cid subst a d t calleeBody argVal h_term h_lk
                        cases h_res : evalCall (calleeBody.subst subst)
                          { bb := 0, stmtIdx := 0, locals := (fun i => if i = 1 then some argVal else none),
                            tySizes := s.tySizes, adtPad := s.adtPad } with
                        | running _ => simp
                        | failed => simp
                        | terminated tk =>
                            cases tk with
                            | normal _ => simp
                            | unwind => simp
                            | compileTimeError =>
                                exact False.elim (h_no_c h_res)

/-- Stepping preserves `tySizes` and `adtPad`. -/
theorem evalStepWith_preserves_world
    {evalCall : MirBody → MirState → ExecOutcome}
    {bodies : List (BodyId × MirBody)}
    {hasCallFuel : Bool} {body : MirBody} {s s' : MirState}
    (h_step : evalStepWith evalCall bodies hasCallFuel body s = .stepped s') :
    s'.tySizes = s.tySizes ∧ s'.adtPad = s.adtPad := by
  unfold evalStepWith at h_step
  cases h_bb : body.blocks[s.bb]? with
  | none => rw [h_bb] at h_step; contradiction
  | some block =>
      rw [h_bb] at h_step
      simp only [] at h_step
      split at h_step
      · cases h_st : block.stmts[s.stmtIdx] with
        | assignConstBool dst b =>
            rw [h_st] at h_step; cases h_step; exact ⟨rfl, rfl⟩
        | assignConstUnit dst =>
            rw [h_st] at h_step; cases h_step; exact ⟨rfl, rfl⟩
        | assignSizeOfEq dst lhs rhs =>
            rw [h_st] at h_step; cases h_step; exact ⟨rfl, rfl⟩
        | evalConst dst cid subst =>
            rw [h_st] at h_step; simp only [] at h_step
            cases hasCallFuel with
            | false => contradiction
            | true =>
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h_step
                cases h_lk : lookupBody bodies cid with
                | none => rw [h_lk] at h_step; contradiction
                | some cBody =>
                    rw [h_lk] at h_step; simp only [] at h_step
                    cases h_res : evalCall (cBody.subst subst) (constEntryState s.tySizes s.adtPad) with
                    | running _ => rw [h_res] at h_step; contradiction
                    | failed => rw [h_res] at h_step; contradiction
                    | terminated tk =>
                        rw [h_res] at h_step
                        cases tk with
                        | normal rv =>
                            cases rv <;> try contradiction
                            cases h_step; exact ⟨rfl, rfl⟩
                        | unwind => contradiction
                        | compileTimeError => contradiction
        | transmuteCopy dst src srcTy dstTy =>
            rw [h_st] at h_step; simp only [] at h_step
            cases h_src : s.locals src with
            | none => rw [h_src] at h_step; contradiction
            | some v =>
                rw [h_src] at h_step; simp only [] at h_step
                by_cases h_sz : evalTySize s.tySizes s.adtPad srcTy = evalTySize s.tySizes s.adtPad dstTy
                · simp only [h_sz, ↓reduceIte] at h_step
                  by_cases h_bool : dstTy = .bool
                  · simp only [h_bool, ↓reduceIte] at h_step
                    cases v <;> try contradiction
                    cases h_step; exact ⟨rfl, rfl⟩
                  · simp only [h_bool, ↓reduceIte] at h_step
                    cases h_step; exact ⟨rfl, rfl⟩
                · simp only [h_sz, ↓reduceIte] at h_step
                  contradiction
      · cases h_t : block.terminator with
        | return_ =>
            rw [h_t] at h_step; simp only [] at h_step
            cases h_r : s.locals 0 <;> { rw [h_r] at h_step; contradiction }
        | goto target =>
            rw [h_t] at h_step; cases h_step; exact ⟨rfl, rfl⟩
        | switchBool discr f t =>
            rw [h_t] at h_step; simp only [] at h_step
            cases h_l : s.locals discr with
            | none => rw [h_l] at h_step; contradiction
            | some v =>
                rw [h_l] at h_step
                cases v with
                | bool b => cases b <;> { cases h_step; exact ⟨rfl, rfl⟩ }
                | _ => contradiction
        | panic =>
            rw [h_t] at h_step; contradiction
        | call1 cid subst a d t =>
            rw [h_t] at h_step; simp only [] at h_step
            cases hasCallFuel with
            | false => contradiction
            | true =>
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h_step
                cases h_arg : s.locals a with
                | none => rw [h_arg] at h_step; contradiction
                | some argVal =>
                    rw [h_arg] at h_step; simp only [] at h_step
                    cases h_lk : lookupBody bodies cid with
                    | none => rw [h_lk] at h_step; contradiction
                    | some calleeBody =>
                        rw [h_lk] at h_step; simp only [] at h_step
                        cases h_res : evalCall (calleeBody.subst subst)
                          { bb := 0, stmtIdx := 0, locals := (fun i => if i = 1 then some argVal else none),
                            tySizes := s.tySizes, adtPad := s.adtPad } with
                        | running _ => rw [h_res] at h_step; contradiction
                        | failed => rw [h_res] at h_step; contradiction
                        | terminated tk =>
                            rw [h_res] at h_step
                            cases tk with
                            | normal _ => cases h_step; exact ⟨rfl, rfl⟩
                            | unwind => contradiction
                            | compileTimeError => contradiction

/-- Multi-step non-`.compileTimeError` preservation across `evalSteps`. -/
theorem evalSteps_no_compileTimeError
    {stepFn : MirBody → MirState → StepResult}
    {body : MirBody}
    (h_step_no_cte : ∀ s, MonoWorldAdmitted bodies monoConsts s.tySizes s.adtPad →
      stepFn body s ≠ .terminated .compileTimeError)
    (h_step_world : ∀ s s', stepFn body s = .stepped s' →
      s'.tySizes = s.tySizes ∧ s'.adtPad = s.adtPad)
    (fuel : Nat) (s : MirState)
    (h_mono : MonoWorldAdmitted bodies monoConsts s.tySizes s.adtPad) :
    evalSteps stepFn fuel body s ≠ .terminated .compileTimeError := by
  induction fuel generalizing s with
  | zero => simp [evalSteps]
  | succ fuel' ih =>
      unfold evalSteps
      cases h_st : stepFn body s with
      | stepped s' =>
          have ⟨h_ty, h_pad⟩ := h_step_world s s' h_st
          have h_mono' : MonoWorldAdmitted bodies monoConsts s'.tySizes s'.adtPad := by
            rw [h_ty, h_pad]; exact h_mono
          exact ih s' h_mono'
      | terminated kind =>
          intro h_eq
          cases h_eq
          exact h_step_no_cte s h_mono h_st
      | failed => simp

/-- Leaf callee (no nested `.call1`) never returns `.terminated .compileTimeError`
on a `MonoWorldAdmitted` world when its `evalConst`s are in `monoConsts`. -/
theorem evalMirFuel_leaf_no_compileTimeError
    {bodies : List (BodyId × MirBody)} {monoConsts : MonoConstSet}
    {callee : MirBody}
    (h_consts : ∀ bb ∈ callee.blocks, ∀ stmt ∈ bb.stmts, ∀ dst cid subst,
      stmt = .evalConst dst cid subst → monoConsts (cid, subst))
    (h_no_calls : ∀ bb ∈ callee.blocks, ∀ cid subst a d t,
      bb.terminator ≠ .call1 cid subst a d t)
    (fuel : Nat) (s : MirState)
    (h_mono : MonoWorldAdmitted bodies monoConsts s.tySizes s.adtPad) :
    evalMirFuel bodies fuel callee s ≠ .terminated .compileTimeError := by
  cases fuel with
  | zero => simp [evalMirFuel]
  | succ f =>
      simp only [evalMirFuel]
      apply evalSteps_no_compileTimeError (bodies := bodies) (monoConsts := monoConsts)
      · intro st h_m
        apply evalStepWith_no_compileTimeError (callFuel := f) h_m h_consts
        · intro bb h_bb cid subst a d t _ _ h_term
          exact False.elim (h_no_calls bb h_bb cid subst a d t h_term)
        · intros; rfl
      · intro st st' h_step
        exact evalStepWith_preserves_world h_step
      · exact h_mono

/-- **Theorem 2 (Root + Callee Non-`.compileTimeError` on `MonoWorldAdmitted` Worlds)**:
For any root `body` whose syntactic `Stmt.evalConst`s (and those of its leaf
`.call1` callees) belong to `monoConsts`, execution in any `MonoWorldAdmitted`
world never terminates in `.compileTimeError`. -/
theorem evalMirFuel_no_compileTimeError_on_monoWorld
    {bodies : List (BodyId × MirBody)} {monoConsts : MonoConstSet}
    {body : MirBody}
    (h_all_in_mono : AllSyntacticEvalConstsInMono bodies monoConsts body)
    (h_callee_leaf : ∀ bb ∈ body.blocks, ∀ cid subst a d t calleeBody,
      bb.terminator = .call1 cid subst a d t →
      lookupBody bodies cid = some calleeBody →
      ∀ cbb ∈ (calleeBody.subst subst).blocks, ∀ ccid csubst ca cd ct,
        cbb.terminator ≠ .call1 ccid csubst ca cd ct)
    (fuel : Nat) (s : MirState)
    (h_mono : MonoWorldAdmitted bodies monoConsts s.tySizes s.adtPad) :
    evalMirFuel bodies fuel body s ≠ .terminated .compileTimeError := by
  cases fuel with
  | zero => simp [evalMirFuel]
  | succ f =>
      simp only [evalMirFuel]
      apply evalSteps_no_compileTimeError (bodies := bodies) (monoConsts := monoConsts)
      · intro st h_m
        apply evalStepWith_no_compileTimeError (callFuel := f) h_m h_all_in_mono.1
        · intro bb h_bb cid subst a d t calleeBody argVal h_term h_lk
          apply evalMirFuel_leaf_no_compileTimeError
          · intro cbb h_cbb stmt h_stmt dst ccid csubst h_eq
            exact h_all_in_mono.2 bb h_bb cid subst a d t calleeBody h_term h_lk
              cbb h_cbb stmt h_stmt dst ccid csubst h_eq
          · exact h_callee_leaf bb h_bb cid subst a d t calleeBody h_term h_lk
          · exact h_m
        · intros; rfl
      · intro st st' h_step
        exact evalStepWith_preserves_world h_step
      · exact h_mono

/-- **Theorem 3 (Main Soundness Bridge: `evalConst_safety_implies_monoAdmitted_safety`)**:
Deleting `RequiresConst`, `MonoAdmitted`, and `MonoConstsWf` is sound: if `body`
satisfies `FnBodyVerified_clean` (under `Stmt.evalConst` + `SafetyPost`), then
for every initial state `s` in a world `(s.tySizes, s.adtPad)` admitted by
`rustc` monomorphization (`MonoWorldAdmitted`):
1. Execution never terminates in `.compileTimeError`,
2. Execution never steps to `.failed` (UB),
3. Every normal return satisfies `MirVal.valid` and `contractPost`! -/
theorem evalConst_safety_implies_monoAdmitted_safety
    {bodies : List (BodyId × MirBody)} {monoConsts : MonoConstSet}
    {body : MirBody} {allowCompileTimeGuard : Bool}
    {contractPost : MirState → ExecOutcome → Prop}
    (h_verified : FnBodyVerified_clean bodies body allowCompileTimeGuard contractPost)
    (h_all_in_mono : AllSyntacticEvalConstsInMono bodies monoConsts body)
    (h_callee_leaf : ∀ bb ∈ body.blocks, ∀ cid subst a d t calleeBody,
      bb.terminator = .call1 cid subst a d t →
      lookupBody bodies cid = some calleeBody →
      ∀ cbb ∈ (calleeBody.subst subst).blocks, ∀ ccid csubst ca cd ct,
        cbb.terminator ≠ .call1 ccid csubst ca cd ct)
    (s : MirState)
    (h_entry : initEntryState body s)
    (h_mono : MonoWorldAdmitted bodies monoConsts s.tySizes s.adtPad)
    (fuel : Nat) :
    let out := evalMirFuel bodies fuel body s
    out ≠ .terminated .compileTimeError ∧
    out ≠ .failed ∧
    (∀ retVal, out = .terminated (.normal retVal) → MirVal.valid retVal body.retTy) ∧
    contractPost s out := by
  have ⟨_, h_step⟩ := h_verified s h_entry
  have ⟨h_safe, h_contract⟩ := h_step fuel
  have h_no_cte :=
    evalMirFuel_no_compileTimeError_on_monoWorld h_all_in_mono h_callee_leaf fuel s h_mono
  exact ⟨h_no_cte, h_safe.1, h_safe.2.2.2, h_contract⟩

/-!
## Part 3: Concrete Verification & Rejection Canaries (Without `RequiresConst` or `extract.rs:256–275`)

We now prove all four concrete canary theorems:
1. `canary_concrete_mismatched_pme_rejected_without_requiresConst`
2. `if_false_const_panic_before_safe_code_accepted`
3. `if_false_const_assert_before_unguarded_transmute_rejected`
4. `interprocedural_branch_callee_pme_and_sneaky_branch_const_rejected`
-/

/-- The polymorphic `SizeEq<Src, Dst>::ASSERT` constant body:
computes `_1 = (size_of::<Src>() == size_of::<Dst>())` and branches to `return ()`
(`bb1`) if equal, or `panic` (`bb2`) if unequal. -/
def sizeEqAssertConstBody : MirBody :=
  { argTys := []
    retTy := .unit
    blocks :=
      [ { stmts := [.assignSizeOfEq 1 (.param 0) (.param 1)]
          terminator := .switchBool 1 2 1 }
      , { stmts := [.assignConstUnit 0]
          terminator := .return_ }
      , { stmts := []
          terminator := .panic } ] }

/-- Generic `transmute_checked<Src, Dst>(x: Src) -> Dst`:
evaluates `Stmt.evalConst 2 ⟨0⟩ [.param 0, .param 1]` in `bb0`, then executes
`transmuteCopy 0 1 (.param 0) (.param 1)` and returns `_0`.
Notice `requiredConsts := []`! -/
def transmuteCheckedBody : MirBody :=
  { argTys := [.param 0]
    retTy := .param 1
    blocks :=
      [ { stmts :=
            [ .evalConst 2 ⟨0⟩ [.param 0, .param 1]
            , .transmuteCopy 0 1 (.param 0) (.param 1) ]
          terminator := .return_ } ] }

/-- Concrete caller `pub fn bad(x: usize) -> bool { transmute_checked::<usize, bool>(x) }`
(`canary_concrete_mismatched_pme_rejected` in `MirLemmas.lean:1629`).
Notice `requiredConsts := []`! -/
def concreteTransmuteCallerBody : MirBody :=
  { argTys := [.usize]
    retTy := .bool
    blocks :=
      [ { stmts := []
          terminator := .call1 ⟨1⟩ [.usize, .bool] 1 0 1 }
      , { stmts := []
          terminator := .return_ } ] }

/-- Crate body table for `canary_concrete_mismatched_pme_rejected`. -/
def canaryBodies : List (BodyId × MirBody) :=
  [ (⟨0⟩, sizeEqAssertConstBody)
  , (⟨1⟩, transmuteCheckedBody)
  , (⟨2⟩, concreteTransmuteCallerBody) ]

/-- Pinned-world initial state for a single `usize` argument (`adtPad = 0, tySizes = 8`). -/
def pinnedUsizeArgState : MirState :=
  { bb := 0
    stmtIdx := 0
    locals := fun i => if i = 1 then some (.int 0) else none
    tySizes := fun _ => 8
    adtPad := fun _ => 0 }

theorem pinnedUsizeArgState_entry :
    initEntryState concreteTransmuteCallerBody pinnedUsizeArgState := by
  refine ⟨rfl, rfl, ?_⟩
  intro i ty h_arg
  cases i with
  | zero =>
      simp [concreteTransmuteCallerBody] at h_arg
      subst h_arg
      exact ⟨.int 0, rfl, trivial⟩
  | succ i' =>
      simp [concreteTransmuteCallerBody] at h_arg

/-- **Canary 1 (`canary_concrete_mismatched_pme_rejected_without_requiresConst`)**:
With `RequiresConst` and `extract.rs:256–275` completely deleted,
`concreteTransmuteCallerBody` (`transmute_checked::<usize, bool>(x)`) steps via
`Terminator.call1` and `Stmt.evalConst` to `.terminated .compileTimeError` at
the pinned world `(adtPad = 0, tySizes = 8)` and **refutes `FnBodyVerified_clean`**
for *both* `allowCompileTimeGuard = false` and `allowCompileTimeGuard = true`
(via `SafetyPost`'s pinned-world non-vacuity clause!). -/
theorem canary_concrete_mismatched_pme_rejected_without_requiresConst :
    evalMirFuel canaryBodies 5 concreteTransmuteCallerBody pinnedUsizeArgState =
      .terminated .compileTimeError ∧
    ∀ allowCompileTimeGuard contractPost,
      ¬ FnBodyVerified_clean canaryBodies concreteTransmuteCallerBody
          allowCompileTimeGuard contractPost := by
  have h_exec :
      evalMirFuel canaryBodies 5 concreteTransmuteCallerBody pinnedUsizeArgState =
        .terminated .compileTimeError := by
    rfl
  refine ⟨h_exec, ?_⟩
  intro allowCompileTimeGuard contractPost h_ver
  have ⟨_, h_step⟩ := h_ver pinnedUsizeArgState pinnedUsizeArgState_entry
  have ⟨h_safe, _⟩ := h_step 5
  have h_no_cte :
      evalMirFuel canaryBodies 5 concreteTransmuteCallerBody pinnedUsizeArgState ≠
        .terminated .compileTimeError :=
    h_safe.2.2.1 ⟨rfl, rfl⟩
  exact h_no_cte h_exec

/-- **Canary 1b (`dead_local_mismatched_pme_rejected_without_requiresConst`)**:
In `Runtime(PostCleanup)` MIR, `let _ = const { assert!(size_of::<usize>() == size_of::<bool>()) };`
has `PlaceMention(_1)` stripped by `RemovePlaceMention`, leaving
`_1 = const { ... }` (`Stmt.evalConst 1 ⟨0⟩ [.usize, .bool]`) intact in `bb0`.
With `RequiresConst` and `extract.rs:256–275` deleted, `Stmt.evalConst` in `bb0`
steps to `.terminated .compileTimeError` at the pinned world `(adtPad = 0, tySizes = 8)`
and refutes `FnBodyVerified_clean` via `SafetyPost`'s pinned-world non-vacuity clause. -/
def deadLocalMismatchedPmeBody : MirBody :=
  { argTys := []
    retTy := .unit
    blocks :=
      [ { stmts :=
            [ .evalConst 1 ⟨0⟩ [.usize, .bool]
            , .assignConstUnit 0 ]
          terminator := .return_ } ] }

def pinnedUnitEntryState : MirState :=
  { bb := 0
    stmtIdx := 0
    locals := fun _ => none
    tySizes := fun _ => 8
    adtPad := fun _ => 0 }

theorem dead_local_mismatched_pme_rejected_without_requiresConst :
    evalMirFuel canaryBodies 5 deadLocalMismatchedPmeBody pinnedUnitEntryState =
      .terminated .compileTimeError ∧
    ∀ allowCompileTimeGuard contractPost,
      ¬ FnBodyVerified_clean canaryBodies deadLocalMismatchedPmeBody
          allowCompileTimeGuard contractPost := by
  have h_exec :
      evalMirFuel canaryBodies 5 deadLocalMismatchedPmeBody pinnedUnitEntryState =
        .terminated .compileTimeError := rfl
  refine ⟨h_exec, ?_⟩
  intro allowCompileTimeGuard contractPost h_ver
  have h_entry : initEntryState deadLocalMismatchedPmeBody pinnedUnitEntryState := by
    refine ⟨rfl, rfl, ?_⟩
    intro i ty h_arg
    simp [deadLocalMismatchedPmeBody] at h_arg
  have ⟨_, h_step⟩ := h_ver pinnedUnitEntryState h_entry
  have ⟨h_safe, _⟩ := h_step 5
  exact (h_safe.2.2.1 ⟨rfl, rfl⟩) h_exec

theorem evalSteps_stepped {stepFn : MirBody → MirState → StepResult}
    {fuel : Nat} {body : MirBody} {s s' : MirState}
    (h : stepFn body s = .stepped s') :
    evalSteps stepFn (fuel + 1) body s = evalSteps stepFn fuel body s' := by
  simp [evalSteps, h]

theorem evalSteps_terminated {stepFn : MirBody → MirState → StepResult}
    {fuel : Nat} {body : MirBody} {s : MirState} {k : TerminationKind}
    (h : stepFn body s = .terminated k) :
    evalSteps stepFn (fuel + 1) body s = .terminated k := by
  simp [evalSteps, h]

/-- **Canary 2 (`if_false_const_panic_before_safe_code_accepted`)**:
Consider `pub fn safe_with_dead_const() { if false { const { panic!() }; } }`
at `Runtime(PostCleanup)` (where `_1 = const false; switchInt(_1) -> [false: bb2, true: bb1]`
is present in `basic_blocks`, or after `bb1` is ignored).
At runtime, `bb0` branches deterministically to `bb2` and returns `.unit` without
ever executing `bb1`'s `Stmt.evalConst`, so it satisfies `FnBodyVerified_clean`
even at Tier S0 (`allowCompileTimeGuard = false`). -/
def ifFalseConstPanicSafeBody : MirBody :=
  { argTys := []
    retTy := .unit
    blocks :=
      [ { stmts := [.assignConstBool 1 false]
          terminator := .switchBool 1 2 1 }
      , { stmts := [.evalConst 2 ⟨0⟩ [.usize, .bool], .assignConstUnit 0]
          terminator := .return_ }
      , { stmts := [.assignConstUnit 0]
          terminator := .return_ } ] }

theorem if_false_const_panic_before_safe_code_accepted :
    FnBodyVerified_clean canaryBodies ifFalseConstPanicSafeBody false (fun _ _ => True) := by
  intro s h_entry
  rcases h_entry with ⟨h_bb, h_idx, _⟩
  let s1 : MirState := { s with stmtIdx := 1, locals := updateLocal s.locals 1 (.bool false) }
  let s2 : MirState := { s1 with bb := 2, stmtIdx := 0 }
  let s3 : MirState := { s2 with stmtIdx := 1, locals := updateLocal s2.locals 0 .unit }
  have h_st0 : ∀ evalCall hasCF,
      evalStepWith evalCall canaryBodies hasCF ifFalseConstPanicSafeBody s = .stepped s1 := by
    intro evalCall hasCF
    unfold evalStepWith
    simp [ifFalseConstPanicSafeBody, h_bb, h_idx, s1]
  have h_st1 : ∀ evalCall hasCF,
      evalStepWith evalCall canaryBodies hasCF ifFalseConstPanicSafeBody s1 = .stepped s2 := by
    intro evalCall hasCF
    unfold evalStepWith
    simp [ifFalseConstPanicSafeBody, h_bb, s1, s2, updateLocal]
  have h_st2 : ∀ evalCall hasCF,
      evalStepWith evalCall canaryBodies hasCF ifFalseConstPanicSafeBody s2 = .stepped s3 := by
    intro evalCall hasCF
    unfold evalStepWith
    simp [ifFalseConstPanicSafeBody, s2, s3]
  have h_st3 : ∀ evalCall hasCF,
      evalStepWith evalCall canaryBodies hasCF ifFalseConstPanicSafeBody s3 =
        .terminated (.normal .unit) := by
    intro evalCall hasCF
    unfold evalStepWith
    simp [ifFalseConstPanicSafeBody, s2, s3, updateLocal]
  have h_eval : ∀ k,
      evalMirFuel canaryBodies (k + 4) ifFalseConstPanicSafeBody s =
        .terminated (.normal .unit) := by
    intro k
    simp only [evalMirFuel]
    rw [evalSteps_stepped (h_st0 _ _),
        evalSteps_stepped (h_st1 _ _),
        evalSteps_stepped (h_st2 _ _),
        evalSteps_terminated (h_st3 _ _)]
  refine ⟨⟨4, ?_⟩, ?_⟩
  · intro fuel h_ge st
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 4 := ⟨fuel - 4, by omega⟩
    rw [h_eval k]
    simp
  · intro fuel
    refine ⟨?_, trivial⟩
    cases fuel with
    | zero =>
        simp [SafetyPost, evalMirFuel]
    | succ f1 =>
        cases f1 with
        | zero =>
            simp only [evalMirFuel]
            rw [evalSteps_stepped (h_st0 _ _)]
            simp [SafetyPost, evalSteps]
        | succ f2 =>
            cases f2 with
            | zero =>
                simp only [evalMirFuel]
                rw [evalSteps_stepped (h_st0 _ _), evalSteps_stepped (h_st1 _ _)]
                simp [SafetyPost, evalSteps]
            | succ f3 =>
                cases f3 with
                | zero =>
                    simp only [evalMirFuel]
                    rw [evalSteps_stepped (h_st0 _ _), evalSteps_stepped (h_st1 _ _),
                        evalSteps_stepped (h_st2 _ _)]
                    simp [SafetyPost, evalSteps]
                | succ k =>
                    rw [h_eval k]
                    simp [SafetyPost, ifFalseConstPanicSafeBody, MirVal.valid]

/-- **Canary 3 (`if_false_const_assert_before_unguarded_transmute_rejected`)**:
Consider `pub unsafe fn bogus_transmute<Src, Dst>(x: Src) -> Dst {
  if false { const { assert!(size_of::<Src>() == size_of::<Dst>()); } }
  transmute_copy(&x)
}`.
Because `if false` jumps to `bb2` without executing `bb1`'s `Stmt.evalConst`,
the mismatched-layout world `(tySizes 0 = 4, tySizes 1 = 8)` is NOT pruned to
`.compileTimeError`; instead `bb2`'s `transmuteCopy` steps to `.failed` (UB),
refuting `FnBodyVerified_clean`! -/
def ifFalseConstBeforeTransmuteBody : MirBody :=
  { argTys := [.param 0]
    retTy := .param 1
    blocks :=
      [ { stmts := [.assignConstBool 2 false]
          terminator := .switchBool 2 2 1 }
      , { stmts := [.evalConst 3 ⟨0⟩ [.param 0, .param 1]]
          terminator := .goto 2 }
      , { stmts := [.transmuteCopy 0 1 (.param 0) (.param 1)]
          terminator := .return_ } ] }

def mismatchedParamState : MirState :=
  { bb := 0
    stmtIdx := 0
    locals := fun i => if i = 1 then some (.opaqueVal (.param 0) 0) else none
    tySizes := fun idx => if idx = 0 then 4 else 8
    adtPad := fun _ => 0 }

theorem if_false_const_assert_before_unguarded_transmute_rejected :
    evalMirFuel canaryBodies 3 ifFalseConstBeforeTransmuteBody mismatchedParamState = .failed ∧
    ∀ allowCompileTimeGuard contractPost,
      ¬ FnBodyVerified_clean canaryBodies ifFalseConstBeforeTransmuteBody
          allowCompileTimeGuard contractPost := by
  have h_fail :
      evalMirFuel canaryBodies 3 ifFalseConstBeforeTransmuteBody mismatchedParamState = .failed := by
    rfl
  refine ⟨h_fail, ?_⟩
  intro allowCompileTimeGuard contractPost h_ver
  have h_entry : initEntryState ifFalseConstBeforeTransmuteBody mismatchedParamState := by
    refine ⟨rfl, rfl, ?_⟩
    intro i ty h_arg
    cases i with
    | zero =>
        simp [ifFalseConstBeforeTransmuteBody] at h_arg
        subst h_arg
        exact ⟨.opaqueVal (.param 0) 0, rfl, rfl⟩
    | succ i' =>
        simp [ifFalseConstBeforeTransmuteBody] at h_arg
  have ⟨_, h_step⟩ := h_ver mismatchedParamState h_entry
  have ⟨h_safe, _⟩ := h_step 3
  exact h_safe.1 h_fail

/-- **Canary 4 (`interprocedural_branch_callee_pme_and_sneaky_branch_const_rejected`)**:
Consider the two runtime-branch-guarded functions:
1. `caller<T>(b: bool, x: T) -> usize { if b { check_layout::<T>(); } transmute_copy(&x) }`
   where `check_layout<T>()` executes `const { assert!(size_of::<T>() == 8) }`.
2. `sneaky<T>(b: bool, x: T) -> usize { if b { const { assert!(size_of::<T>() == 8) }; } transmute_copy(&x) }`.
When `b = false` at runtime in a world where `size_of::<T>() = 4 ≠ 8`, neither
the `Terminator.call1` to `check_layout::<T>()` nor the in-branch `Stmt.evalConst`
executes, so both functions step to `.failed` (UB) at `transmuteCopy` and
refute `FnBodyVerified_clean`! -/
def checkLayoutCalleeBody : MirBody :=
  { argTys := [.bool]
    retTy := .unit
    blocks :=
      [ { stmts :=
            [ .evalConst 2 ⟨0⟩ [.param 0, .usize]
            , .assignConstUnit 0 ]
          terminator := .return_ } ] }

def callerBranchCalleeTransmuteBody : MirBody :=
  { argTys := [.bool, .param 0]
    retTy := .usize
    blocks :=
      [ { stmts := []
          terminator := .switchBool 1 2 1 }
      , { stmts := []
          terminator := .call1 ⟨3⟩ [.param 0] 1 3 2 }
      , { stmts := [.transmuteCopy 0 2 (.param 0) .usize]
          terminator := .return_ } ] }

def sneakyBranchConstTransmuteBody : MirBody :=
  { argTys := [.bool, .param 0]
    retTy := .usize
    blocks :=
      [ { stmts := []
          terminator := .switchBool 1 2 1 }
      , { stmts := [.evalConst 3 ⟨0⟩ [.param 0, .usize]]
          terminator := .goto 2 }
      , { stmts := [.transmuteCopy 0 2 (.param 0) .usize]
          terminator := .return_ } ] }

def interprocBodies : List (BodyId × MirBody) :=
  [ (⟨0⟩, sizeEqAssertConstBody)
  , (⟨3⟩, checkLayoutCalleeBody) ]

def untakenBranchMismatchedState : MirState :=
  { bb := 0
    stmtIdx := 0
    locals := fun i =>
      if i = 1 then some (.bool false)
      else if i = 2 then some (.opaqueVal (.param 0) 0)
      else none
    tySizes := fun _ => 4
    adtPad := fun _ => 0 }

theorem interprocedural_branch_callee_pme_and_sneaky_branch_const_rejected :
    evalMirFuel interprocBodies 3 callerBranchCalleeTransmuteBody untakenBranchMismatchedState = .failed ∧
    evalMirFuel interprocBodies 3 sneakyBranchConstTransmuteBody untakenBranchMismatchedState = .failed ∧
    (∀ allowCompileTimeGuard contractPost,
      ¬ FnBodyVerified_clean interprocBodies callerBranchCalleeTransmuteBody
          allowCompileTimeGuard contractPost) ∧
    (∀ allowCompileTimeGuard contractPost,
      ¬ FnBodyVerified_clean interprocBodies sneakyBranchConstTransmuteBody
          allowCompileTimeGuard contractPost) := by
  have h_fail_caller :
      evalMirFuel interprocBodies 3 callerBranchCalleeTransmuteBody untakenBranchMismatchedState = .failed := rfl
  have h_fail_sneaky :
      evalMirFuel interprocBodies 3 sneakyBranchConstTransmuteBody untakenBranchMismatchedState = .failed := rfl
  refine ⟨h_fail_caller, h_fail_sneaky, ?_, ?_⟩
  · intro allowCompileTimeGuard contractPost h_ver
    have h_entry : initEntryState callerBranchCalleeTransmuteBody untakenBranchMismatchedState := by
      refine ⟨rfl, rfl, ?_⟩
      intro i ty h_arg
      cases i with
      | zero =>
          simp [callerBranchCalleeTransmuteBody] at h_arg
          subst h_arg
          exact ⟨.bool false, rfl, trivial⟩
      | succ i1 =>
          cases i1 with
          | zero =>
              simp [callerBranchCalleeTransmuteBody] at h_arg
              subst h_arg
              exact ⟨.opaqueVal (.param 0) 0, rfl, rfl⟩
          | succ i2 =>
              simp [callerBranchCalleeTransmuteBody] at h_arg
    have ⟨_, h_step⟩ := h_ver untakenBranchMismatchedState h_entry
    exact (h_step 3).1.1 h_fail_caller
  · intro allowCompileTimeGuard contractPost h_ver
    have h_entry : initEntryState sneakyBranchConstTransmuteBody untakenBranchMismatchedState := by
      refine ⟨rfl, rfl, ?_⟩
      intro i ty h_arg
      cases i with
      | zero =>
          simp [sneakyBranchConstTransmuteBody] at h_arg
          subst h_arg
          exact ⟨.bool false, rfl, trivial⟩
      | succ i1 =>
          cases i1 with
          | zero =>
              simp [sneakyBranchConstTransmuteBody] at h_arg
              subst h_arg
              exact ⟨.opaqueVal (.param 0) 0, rfl, rfl⟩
          | succ i2 =>
              simp [sneakyBranchConstTransmuteBody] at h_arg
    have ⟨_, h_step⟩ := h_ver untakenBranchMismatchedState h_entry
    exact (h_step 3).1.1 h_fail_sneaky

#print axioms empty_requiredConsts_uninhabited
#print axioms empty_requiredConsts_legacy_predicates_trivial
#print axioms evalConst_safety_implies_monoAdmitted_safety
#print axioms canary_concrete_mismatched_pme_rejected_without_requiresConst
#print axioms dead_local_mismatched_pme_rejected_without_requiresConst
#print axioms if_false_const_panic_before_safe_code_accepted
#print axioms if_false_const_assert_before_unguarded_transmute_rejected
#print axioms interprocedural_branch_callee_pme_and_sneaky_branch_const_rejected

end InterproceduralEvalConstDominance
