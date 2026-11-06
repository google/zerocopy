-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Structural `StepResult.externalCall`, Open-World Callback Framing, and Trusted Semantics Canary Suites

This standalone Lean 4 (`v4.34.1`) module mechanizes four components for
Anneal's Trusted Computing Base (`trusted/lean/Trusted/`):

1. **`StructuralExternalCall` (Part I):** Extends `StepResult` and
   `ReachesPrefix` with `.externalCall (boundaryInv : Bool)
   (next : State → Obs → Prop)` to model unresolved trait-method and
   function-pointer callbacks (`<T as Trait>::method`, `FnMut`) in open-world
   Rust libraries without whole-program call-graph closure.
   - Proves constructively (zero `Classical.choice`, zero `Lean.ofReduceBool`,
     zero `sorryAx`) that `TotalStep` and `InhabitedDemonic` preserve
     `exists_reaches_prefix` and `non_vacuity_at_every_depth`.
   - Proves `canary_reentrant_callback_rejected`,
     `canary_unchecked_callback_unsoundly_accepts_reentrantBuggyFn`, and
     `canary_safe_callback_verified`.

2. **`TrustedMutationCanaries` (Part II):** Mechanizes the 25 negative canary
   refutation theorems (`canary_M01` through `canary_M24b`) covering every
   semantic failure branch, deinitialization rule, type-size layout rule,
   representation-invariant admissibility rule, `unsafe impl` obligation, and
   `TrustPolicy` gate in `Trusted/MirSemantics.lean`.

3. **`BoundaryCanary` (Part III):** Mechanizes `X86MachineModel`, the mandatory
   `BoundaryCanarySuite` typeclass (pairing 11 positive conformance witnesses
   with 10 negative refutation theorems), `currentX86Model_fails_BoundaryCanarySuite`,
   and `instBoundaryCanarySuiteFixedX86Model` (annotated with `-- MUTATE_GUARD:`
   markers for automated guard-mutation testing).

4. **`OpenWorldCallbackFraming` (Part IV):** Mechanizes the `BoundedIdx`
   callback re-entrancy exploit (`naive_getUnchecked_verified`,
   `naive_withTempInvalid_verified`, `naive_reentrancy_exploit_triggers_ub`),
   the guarded open-world call contract with System V AMD64 ABI register and
   `BytePerm` frame isolation (`GuardedOpenMachine`,
   `withTempInvalid_rejected_under_guarded_call`,
   `withRestoredBeforeCall_verified`, `withUnexposedPrivateTemp_verified`),
   the straight-line induction composition theorem
   (`open_world_callback_composition_sound`), and the propositional structural
   variant (`StructuralOpenMachine`, `structural_withTempInvalid_rejected`,
   `structural_withRestoredBeforeCall_verified`).
-/

namespace AnnealReference

/-!
## Part I: Refinement Preorder and Structural `StepResult.externalCall`
-/

namespace StructuralExternalCall

class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

abbrev Language.Behavior (L : Language) : Type :=
  StructuralExternalCall.Behavior L.Query L.Out

def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

/-- Extended small-step transition outcome incorporating `.externalCall` for
    open-world trait/callback invocations:
    - `step obs next`: deterministic internal transition.
    - `choice branches`: internal demonic nondeterminism.
    - `externalCall boundaryInv next`: open-world call to an unknown safe
      external callback. If `boundaryInv = false` at the call site, the machine
      steps immediately to `.failed` (fail-closed UB check against broken
      library invariants exposed to re-entrant safe code). If
      `boundaryInv = true`, the machine branches demonically over all
      `(s', obs)` satisfying `next s' obs` (preserving caller-private stack
      slots while allowing any library-invariant-valid return value and
      shared-reference mutation).
    - `terminated term`: normal or unwind completion.
    - `failed`: immediate Undefined Behavior.

    Using `boundaryInv : Bool` (populated via `decide P` for any decidable
    boundary invariant `P : Prop [Decidable P]`) avoids dependent `Prop`-indexed
    `Decidable` fields inside `StepResult`, ensuring Lean's generated
    `StepResult.noConfusion` principle never pulls in `Classical.choice`. -/
inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (branches : State → Prop)
  | externalCall (boundaryInv : Bool) (next : State → Obs → Prop)
  | terminated (term : TerminationKind Val)
  | failed

inductive PrefixOutcome (Val : Type) where
  | running
  | terminated (term : TerminationKind Val)
  | failed
  | stuck

def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed => False
  | .stuck => False

structure ExecQuery (State : Type) where
  init : State
  steps : Nat

structure ExecOut (Obs Val : Type) where
  trace : List Obs
  outcome : PrefixOutcome Val

structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

/-- Inductive prefix reachability extended with `.externalCall`:
    - `externalCallFail`: if `step p s (.externalCall boundaryInv next)` and
      `boundaryInv = false`, the call fails closed in 1 step with `.failed`
      (UB).
    - `externalCallOk`: if `step p s (.externalCall boundaryInv next)` and
      `boundaryInv = true`, the machine branches demonically over every
      `(s', obs)` satisfying `next s' obs`.
    - `emptyExternalCall`: if `boundaryInv = true` holds but `next` is empty,
      records `.stuck` so an uninhabited callback transition cannot silently
      vanish. -/
inductive ReachesPrefix
    (step : Prog → State → StepResult State Obs Val → Prop) (p : Prog) :
    Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefix step p 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome Val) :
      step p s (.step obs s') →
      ReachesPrefix step p n s' tr out →
      ReachesPrefix step p (n + 1) s (obs :: tr) out
  | choice (n : Nat) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      step p s (.choice branches) →
      branches s' →
      ReachesPrefix step p n s' tr out →
      ReachesPrefix step p (n + 1) s tr out
  | emptyChoice (n : Nat) (s : State) (branches : State → Prop) :
      step p s (.choice branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix step p (n + 1) s [] .stuck
  | externalCallFail (n : Nat) (s : State) (boundaryInv : Bool)
      (next : State → Obs → Prop) :
      step p s (.externalCall boundaryInv next) →
      boundaryInv = false →
      ReachesPrefix step p (n + 1) s [] .failed
  | externalCallOk (n : Nat) (s s' : State) (boundaryInv : Bool)
      (next : State → Obs → Prop)
      (obs : Obs) (tr : List Obs) (out : PrefixOutcome Val) :
      step p s (.externalCall boundaryInv next) →
      boundaryInv = true →
      next s' obs →
      ReachesPrefix step p n s' tr out →
      ReachesPrefix step p (n + 1) s (obs :: tr) out
  | emptyExternalCall (n : Nat) (s : State) (boundaryInv : Bool)
      (next : State → Obs → Prop) :
      step p s (.externalCall boundaryInv next) →
      boundaryInv = true →
      (¬ ∃ s' obs, next s' obs) →
      ReachesPrefix step p (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      step p s (.terminated term) →
      ReachesPrefix step p (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) :
      step p s .failed →
      ReachesPrefix step p (n + 1) s [] .failed
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, step p s r) →
      ReachesPrefix step p (n + 1) s [] .stuck

def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M.step p q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M.step p q.steps q.init out.trace out.outcome
  }

def SmallStepMachine.toLanguage (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog := Prog
  Query := ExecQuery State
  Out := ExecOut Obs Val
  sem := BehaviorOf M

/-- Every state of program `p` has at least one outgoing `StepResult`. -/
def TotalStep (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State), ∃ r, M.step p s r

/-- Every reachable demonic `.choice` or valid `.externalCall` node has at least
    one enabled continuation branch. -/
def InhabitedDemonic (M : SmallStepMachine Prog State Obs Val) : Prop :=
  (∀ (p : Prog) (s : State) (branches : State → Prop),
    M.step p s (.choice branches) → ∃ s', branches s') ∧
  (∀ (p : Prog) (s : State) (boundaryInv : Bool)
    (next : State → Obs → Prop),
    M.step p s (.externalCall boundaryInv next) →
    boundaryInv = true →
    ∃ s' obs, next s' obs)

/-- Constructive prefix existence at every step budget `n : Nat` for machines
    with `.externalCall`. Because `boundaryInv : Bool`, the proof case-splits
    constructively on `boundaryInv` without invoking `Classical.em` or
    `Classical.choice`. -/
theorem exists_reaches_prefix
    {M : SmallStepMachine Prog State Obs Val}
    (h_tot : TotalStep M)
    (h_dem : InhabitedDemonic M)
    (p : Prog) (n : Nat) :
    ∀ (s : State),
      ∃ tr out, ReachesPrefix M.step p n s tr out ∧ out ≠ .stuck := by
  induction n with
  | zero =>
    intro s
    exact ⟨[], .running, ReachesPrefix.zero s, by intro h; cases h⟩
  | succ k ih =>
    intro s
    cases h_tot p s with
    | intro r hstep =>
      cases r with
      | step obs s' =>
        cases ih s' with
        | intro tr hrest =>
          cases hrest with
          | intro out hpair =>
            exact ⟨obs :: tr, out,
              ReachesPrefix.step k s s' obs tr out hstep hpair.1,
              hpair.2⟩
      | choice branches =>
        cases h_dem.1 p s branches hstep with
        | intro s' hbranch =>
          cases ih s' with
          | intro tr hrest =>
            cases hrest with
            | intro out hpair =>
              exact ⟨tr, out,
                ReachesPrefix.choice k s s' branches tr out hstep hbranch hpair.1,
                hpair.2⟩
      | externalCall boundaryInv next =>
        cases boundaryInv with
        | false =>
          exact ⟨[], .failed,
            ReachesPrefix.externalCallFail k s false next hstep rfl,
            by intro h; cases h⟩
        | true =>
          cases h_dem.2 p s true next hstep rfl with
          | intro s' hobs =>
            cases hobs with
            | intro obs hnext =>
              cases ih s' with
              | intro tr hrest =>
                cases hrest with
                | intro out hpair =>
                  exact ⟨obs :: tr, out,
                    ReachesPrefix.externalCallOk k s s' true next obs tr out
                      hstep rfl hnext hpair.1,
                    hpair.2⟩
      | terminated term =>
        exact ⟨[], .terminated term,
          ReachesPrefix.terminated k s term hstep,
          by intro h; cases h⟩
      | failed =>
        exact ⟨[], .failed,
          ReachesPrefix.failed k s hstep,
          by intro h; cases h⟩

/-- Structural non-vacuity at every finite step depth `n : Nat` with
    `.externalCall`. -/
theorem non_vacuity_at_every_depth
    {M : SmallStepMachine Prog State Obs Val}
    (h_tot : TotalStep M)
    (h_dem : InhabitedDemonic M)
    (p : Prog) (init : State)
    (h_init : M.initState p init)
    (n : Nat) :
    ∃ out : ExecOut Obs Val,
      M.initState p init ∧
      ReachesPrefix M.step p n init out.trace out.outcome ∧
      out.outcome ≠ .stuck := by
  cases exists_reaches_prefix h_tot h_dem p n init with
  | intro tr hrest =>
    cases hrest with
    | intro oc hpair =>
      refine ⟨{ trace := tr, outcome := oc }, ?_⟩
      exact ⟨h_init, hpair.1, hpair.2⟩

#print axioms exists_reaches_prefix
#print axioms non_vacuity_at_every_depth

/-!
### Symbolic Small-Step Inversion Lemmas for Deterministic `evalStep` with `.externalCall`

These generic inversion lemmas mirror `reachesPrefix_of_step` and
`reachesPrefix_of_terminated` in `theory/Anneal/MirLemmas.lean`, adding
`reachesPrefix_of_externalCall` for `.externalCall`.
-/

theorem reachesPrefix_of_step
    {Prog State Obs Val : Type}
    {eval : Prog → State → StepResult State Obs Val}
    {p : Prog} {s s' : State} {obs : Obs} {n : Nat} {tr : List Obs}
    {out : PrefixOutcome Val}
    (hstep : eval p s = .step obs s')
    (hreach : ReachesPrefix (fun p s r => r = eval p s) p n s tr out) :
    out = .running ∨
      ∃ n' tr', ReachesPrefix (fun p s r => r = eval p s) p n' s' tr' out := by
  cases hreach with
  | zero => exact Or.inl rfl
  | step n' _ s₂ obs₂ tr' _ h1 hr =>
    rw [hstep] at h1
    injection h1 with _ hs
    subst hs
    exact Or.inr ⟨n', tr', hr⟩
  | choice _ _ _ _ _ _ h1 _ _ =>
    rw [hstep] at h1; cases h1
  | emptyChoice _ _ _ h1 _ =>
    rw [hstep] at h1; cases h1
  | externalCallFail _ _ _ _ h1 _ =>
    rw [hstep] at h1; cases h1
  | externalCallOk _ _ _ _ _ _ _ _ h1 _ _ _ =>
    rw [hstep] at h1; cases h1
  | emptyExternalCall _ _ _ _ h1 _ _ =>
    rw [hstep] at h1; cases h1
  | terminated _ _ _ h1 =>
    rw [hstep] at h1; cases h1
  | failed _ _ h1 =>
    rw [hstep] at h1; cases h1
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstep.symm⟩)

theorem reachesPrefix_of_terminated
    {Prog State Obs Val : Type}
    {eval : Prog → State → StepResult State Obs Val}
    {p : Prog} {s : State} {n : Nat} {tr : List Obs}
    {out : PrefixOutcome Val} {term : TerminationKind Val}
    (hstep : eval p s = .terminated term)
    (hreach : ReachesPrefix (fun p s r => r = eval p s) p n s tr out) :
    out = .running ∨ out = .terminated term := by
  cases hreach with
  | zero => exact Or.inl rfl
  | step _ _ _ _ _ _ h1 _ =>
    rw [hstep] at h1; cases h1
  | choice _ _ _ _ _ _ h1 _ _ =>
    rw [hstep] at h1; cases h1
  | emptyChoice _ _ _ h1 _ =>
    rw [hstep] at h1; cases h1
  | externalCallFail _ _ _ _ h1 _ =>
    rw [hstep] at h1; cases h1
  | externalCallOk _ _ _ _ _ _ _ _ h1 _ _ _ =>
    rw [hstep] at h1; cases h1
  | emptyExternalCall _ _ _ _ h1 _ _ =>
    rw [hstep] at h1; cases h1
  | terminated _ _ t h1 =>
    rw [hstep] at h1
    injection h1 with ht
    subst ht
    exact Or.inr rfl
  | failed _ _ h1 =>
    rw [hstep] at h1; cases h1
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstep.symm⟩)

theorem reachesPrefix_of_externalCall
    {Prog State Obs Val : Type}
    {eval : Prog → State → StepResult State Obs Val}
    {p : Prog} {s : State} {n : Nat} {tr : List Obs}
    {out : PrefixOutcome Val} {boundaryInv : Bool}
    {next : State → Obs → Prop}
    (hstep : eval p s = .externalCall boundaryInv next)
    (hinv : boundaryInv = true)
    (hinh : ∃ s' obs, next s' obs)
    (hreach : ReachesPrefix (fun p s r => r = eval p s) p n s tr out) :
    out = .running ∨
      ∃ n' s' obs tr',
        next s' obs ∧
        ReachesPrefix (fun p s r => r = eval p s) p n' s' tr' out := by
  cases hreach with
  | zero => exact Or.inl rfl
  | step _ _ _ _ _ _ h1 _ =>
    rw [hstep] at h1; cases h1
  | choice _ _ _ _ _ _ h1 _ _ =>
    rw [hstep] at h1; cases h1
  | emptyChoice _ _ _ h1 _ =>
    rw [hstep] at h1; cases h1
  | externalCallFail _ _ b2 next2 h1 hnot =>
    rw [hstep] at h1
    injection h1 with hb _
    subst hb
    rw [hinv] at hnot
    cases hnot
  | externalCallOk n' _ s' b2 next2 obs tr' _ h1 _ hnext hr =>
    rw [hstep] at h1
    injection h1 with hb hnextEq
    subst hb hnextEq
    exact Or.inr ⟨n', s', obs, tr', hnext, hr⟩
  | emptyExternalCall _ _ b2 next2 h1 _ hempty =>
    rw [hstep] at h1
    injection h1 with hb hnextEq
    subst hb hnextEq
    exact False.elim (hempty hinh)
  | terminated _ _ _ h1 =>
    rw [hstep] at h1; cases h1
  | failed _ _ h1 =>
    rw [hstep] at h1; cases h1
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstep.symm⟩)

#print axioms reachesPrefix_of_step
#print axioms reachesPrefix_of_terminated
#print axioms reachesPrefix_of_externalCall

/-!
### Concrete MIR Callback Machine Instantiation 
-/

structure LocalId where
  index : Nat
  deriving DecidableEq

structure BlockId where
  index : Nat
  deriving DecidableEq

inductive MirTy where
  | usize
  | adt (id : Nat)
  | ref (inner : MirTy)
  deriving DecidableEq

inductive MirVal where
  | usize (bits : Nat)
  | adt (id : Nat) (inner : MirVal)
  | ref (loc : LocalId)
  deriving DecidableEq

inductive Operand where
  | copy (src : LocalId)
  | constVal (val : MirVal)

inductive Rvalue where
  | use (op : Operand)
  | aggregate (adtId : Nat) (op : Operand)
  | ref (src : LocalId)

inductive Stmt where
  | assign (dst : LocalId) (rv : Rvalue)
  | nop

inductive Terminator where
  | return_
  | goto (target : BlockId)
  | callExternal (dst : LocalId) (argRef : LocalId) (adtId : Nat)
      (target : BlockId)

structure BasicBlock where
  stmts : List Stmt
  terminator : Terminator

structure MirBody where
  argTys : List MirTy
  retTy : MirTy
  blocks : List BasicBlock

structure MirState where
  locals : Nat → Option MirVal
  block : Nat
  stmtIdx : Nat

def updateLocal (locals : Nat → Option MirVal) (target : Nat)
    (val : Option MirVal) : Nat → Option MirVal :=
  fun i => if i == target then val else locals i

/-- Computable boolean check for whether an ADT `adtId` wrapping `v` satisfies
    the library's `NonZeroUsize` representation invariant (`adtId = 0 → n ≠ 0`). -/
def checkNonZeroAdtInv (adtId : Nat) (v : MirVal) : Bool :=
  match adtId, v with
  | 0, .usize n => decide (n ≠ 0)
  | _, .usize _ => true
  | _, _ => false

def NonZeroAdtInv (adtId : Nat) (v : MirVal) : Prop :=
  checkNonZeroAdtInv adtId v = true

instance instDecidableNonZeroAdtInv (adtId : Nat) (v : MirVal) :
    Decidable (NonZeroAdtInv adtId v) :=
  inferInstanceAs (Decidable (checkNonZeroAdtInv adtId v = true))

def MirVal.satisfiesInv (v : MirVal) (ty : MirTy) : Prop :=
  match ty, v with
  | .usize, .usize _ => True
  | .adt tyId, .adt vId inner => vId = tyId ∧ NonZeroAdtInv tyId inner
  | .ref _, .ref _ => True
  | _, _ => False

/-- Computable boolean check for whether the shared reference `argRef` passed to
    an external callback points to a live local whose value satisfies the
    library's `AdtInv` for `adtId`. -/
def checkBoundaryInv (adtId : Nat) (argRef : LocalId) (s : MirState) : Bool :=
  match s.locals argRef.index with
  | some (.ref target) =>
    match s.locals target.index with
    | some (.adt vId inner) => decide (vId = adtId) && checkNonZeroAdtInv adtId inner
    | _ => false
  | _ => false

/-- Pre-call boundary invariant required at an unresolved `.callExternal` site. -/
def BoundaryInvHolds (adtId : Nat) (argRef : LocalId) (s : MirState) : Prop :=
  checkBoundaryInv adtId argRef s = true

instance instDecidableBoundaryInvHolds (adtId : Nat) (argRef : LocalId)
    (s : MirState) : Decidable (BoundaryInvHolds adtId argRef s) :=
  inferInstanceAs (Decidable (checkBoundaryInv adtId argRef s = true))

/-- Frame-isolation relation across an external callback: every caller-private
    local slot `i` (`i ≠ dst.index`) is preserved unchanged (`s'.locals i =
    s.locals i`), while the return destination `dst` receives any library-valid
    `adt adtId` value produced by the safe external callback. -/
def CallerFramePreserved (dst : LocalId) (s s' : MirState) : Prop :=
  ∀ i, i ≠ dst.index → s'.locals i = s.locals i

/-- Demonic post-call relation for a safe external callback returning an
    `.adt adtId` value into `dst` and continuing at `target`. -/
def ExternalCallbackNext (dst : LocalId) (adtId : Nat) (target : BlockId)
    (s s' : MirState) (_obs : Unit) : Prop :=
  CallerFramePreserved dst s s' ∧
  (∃ retVal,
    s'.locals dst.index = some retVal ∧
    retVal.satisfiesInv (.adt adtId)) ∧
  s'.block = target.index ∧
  s'.stmtIdx = 0

theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : (a == b) = false := by
  cases hbeq : (a == b) with
  | false => rfl
  | true =>
    exact False.elim (h (of_decide_eq_true hbeq))

/-- Canonical witness continuation showing `ExternalCallbackNext` is always
    inhabited: the external callback can always return `.adt adtId (.usize 1)`. -/
theorem externalCallbackNext_inhabited (dst : LocalId) (adtId : Nat)
    (target : BlockId) (s : MirState) :
    ∃ s' obs, ExternalCallbackNext dst adtId target s s' obs := by
  let s' : MirState := {
    locals := updateLocal s.locals dst.index (some (.adt adtId (.usize 1)))
    block := target.index
    stmtIdx := 0
  }
  refine ⟨s', (), ?_, ?_, rfl, rfl⟩
  · intro i hi
    have hbeq : (i == dst.index) = false := nat_beq_false_of_ne hi
    dsimp [s', updateLocal]
    rw [hbeq]
    rfl
  · refine ⟨.adt adtId (.usize 1), ?_, ?_⟩
    · have hbeq : (dst.index == dst.index) = true := decide_eq_true rfl
      dsimp [s', updateLocal]
      rw [hbeq]
      rfl
    · refine ⟨rfl, ?_⟩
      unfold NonZeroAdtInv checkNonZeroAdtInv
      cases adtId with
      | zero => rfl
      | succ _ => rfl

def evalOperand (locals : Nat → Option MirVal) (op : Operand) :
    Option MirVal :=
  match op with
  | .copy src => locals src.index
  | .constVal v => some v

def evalStmt (s : MirState) (stmt : Stmt) : StepResult MirState Unit MirVal :=
  match stmt with
  | .assign dst (.use op) =>
    match evalOperand s.locals op with
    | some v =>
      .step () { s with
        locals := updateLocal s.locals dst.index (some v)
        stmtIdx := s.stmtIdx + 1
      }
    | none => .failed
  | .assign dst (.aggregate adtId op) =>
    match evalOperand s.locals op with
    | some v =>
      .step () { s with
        locals := updateLocal s.locals dst.index (some (.adt adtId v))
        stmtIdx := s.stmtIdx + 1
      }
    | none => .failed
  | .assign dst (.ref src) =>
    match s.locals src.index with
    | some _ =>
      .step () { s with
        locals := updateLocal s.locals dst.index (some (.ref src))
        stmtIdx := s.stmtIdx + 1
      }
    | none => .failed
  | .nop =>
    .step () { s with stmtIdx := s.stmtIdx + 1 }

def evalTerminator (s : MirState) (term : Terminator) :
    StepResult MirState Unit MirVal :=
  match term with
  | .return_ =>
    match s.locals 0 with
    | some v => .terminated (.normal v)
    | none => .failed
  | .goto target =>
    .step () { s with block := target.index, stmtIdx := 0 }
  | .callExternal dst argRef adtId target =>
    .externalCall
      (decide (BoundaryInvHolds adtId argRef s))
      (ExternalCallbackNext dst adtId target s)

def evalStep (body : MirBody) (s : MirState) :
    StepResult MirState Unit MirVal :=
  match body.blocks[s.block]? with
  | none => .failed
  | some bb =>
    match bb.stmts[s.stmtIdx]? with
    | some stmt => evalStmt s stmt
    | none => evalTerminator s bb.terminator

def initExtMirState (body : MirBody) (s : MirState) : Prop :=
  s.block = 0 ∧
  s.stmtIdx = 0 ∧
  s.locals 0 = none ∧
  body.argTys.foldr
    (fun ty rest k =>
      (∃ v, s.locals k = some v ∧ v.satisfiesInv ty) ∧ rest (k + 1))
    (fun k => ∀ j, k ≤ j → s.locals j = none)
    1

def ExtMirMachine : SmallStepMachine MirBody MirState Unit MirVal where
  initState := initExtMirState
  step body s r := r = evalStep body s

def ExtMirLang : Language :=
  ExtMirMachine.toLanguage

abbrev ExtMirSem (body : MirBody) : ExtMirLang.Behavior :=
  ExtMirLang.sem body

theorem evalStmt_not_choice (s : MirState) (st : Stmt)
    (branches : MirState → Prop) :
    StepResult.choice branches = evalStmt s st → False := by
  unfold evalStmt
  cases st with
  | assign dst rv =>
    cases rv with
    | use op =>
      dsimp
      cases evalOperand s.locals op <;> intro h <;> cases h
    | aggregate adtId op =>
      dsimp
      cases evalOperand s.locals op <;> intro h <;> cases h
    | ref src =>
      dsimp
      cases s.locals src.index <;> intro h <;> cases h
  | nop =>
    intro h; cases h

theorem evalTerminator_not_choice (s : MirState) (term : Terminator)
    (branches : MirState → Prop) :
    StepResult.choice branches = evalTerminator s term → False := by
  unfold evalTerminator
  cases term with
  | return_ =>
    dsimp
    cases s.locals 0 <;> intro h <;> cases h
  | goto _ =>
    intro h; cases h
  | callExternal _ _ _ _ =>
    intro h; cases h

theorem evalStmt_not_externalCall (s : MirState) (st : Stmt)
    (b : Bool) (next : MirState → Unit → Prop) :
    StepResult.externalCall b next = evalStmt s st → False := by
  unfold evalStmt
  cases st with
  | assign dst rv =>
    cases rv with
    | use op =>
      dsimp
      cases evalOperand s.locals op <;> intro h <;> cases h
    | aggregate adtId op =>
      dsimp
      cases evalOperand s.locals op <;> intro h <;> cases h
    | ref src =>
      dsimp
      cases s.locals src.index <;> intro h <;> cases h
  | nop =>
    intro h; cases h

/-- `ExtMirMachine` is total: `evalStep` is a total function. -/
theorem extMir_totalStep : TotalStep ExtMirMachine := by
  intro p s
  exact ⟨evalStep p s, rfl⟩

/-- `ExtMirMachine` has inhabited demonic choices across all states. -/
theorem extMir_inhabitedDemonic : InhabitedDemonic ExtMirMachine := by
  constructor
  · intro p s branches hstep
    have h : StepResult.choice branches = evalStep p s := hstep
    dsimp [evalStep] at h
    revert h
    cases p.blocks[s.block]? with
    | none => intro h; cases h
    | some bb =>
      intro h
      dsimp at h
      revert h
      cases bb.stmts[s.stmtIdx]? with
      | some st =>
        intro h
        exact False.elim (evalStmt_not_choice s st branches h)
      | none =>
        intro h
        exact False.elim (evalTerminator_not_choice s bb.terminator branches h)
  · intro p s boundaryInv next hstep _hinv
    have h : StepResult.externalCall boundaryInv next = evalStep p s := hstep
    dsimp [evalStep] at h
    revert h
    cases p.blocks[s.block]? with
    | none => intro h; cases h
    | some bb =>
      intro h
      dsimp at h
      revert h
      cases bb.stmts[s.stmtIdx]? with
      | some st =>
        intro h
        exact False.elim (evalStmt_not_externalCall s st boundaryInv next h)
      | none =>
        intro h
        dsimp [evalTerminator] at h
        revert h
        cases bb.terminator with
        | return_ =>
          dsimp
          cases s.locals 0 <;> intro h <;> cases h
        | goto _ =>
          intro h; cases h
        | callExternal dst argRef adtId target =>
          intro h
          injection h with _ hnext
          subst hnext
          exact externalCallbackNext_inhabited dst adtId target s

#print axioms extMir_totalStep
#print axioms extMir_inhabitedDemonic

/-!
### `canary_reentrant_callback_rejected`
-/

def reentrantBuggyFn : MirBody where
  argTys := [.adt 0]
  retTy := .adt 0
  blocks := [
    { stmts := [
        -- _2 = NonZeroUsize(0)  (temporarily breaks NonZeroAdtInv!)
        .assign ⟨2⟩ (.aggregate 0 (.constVal (.usize 0))),
        -- _3 = &_2
        .assign ⟨3⟩ (.ref ⟨2⟩)
      ]
      -- _4 = external_callback(&_2) -> bb1
      terminator := .callExternal ⟨4⟩ ⟨3⟩ 0 ⟨1⟩
    },
    { stmts := [
        -- Restore _2 = _1 and return _0 = _2
        .assign ⟨2⟩ (.use (.copy ⟨1⟩)),
        .assign ⟨0⟩ (.use (.copy ⟨2⟩))
      ]
      terminator := .return_
    }
  ]

/-- Negative canary `reentrantBuggyFn` violates `ExtMirLang.WellFormed`
    (even when called with a valid `NonZeroUsize(1)` argument at entry) because
    `StepResult.externalCall` fails closed at step 3 when `BoundaryInvHolds` is
    violated. -/
theorem canary_reentrant_callback_rejected :
    ¬ (ExtMirSem reentrantBuggyFn ≤ ExtMirLang.WellFormed) := by
  intro hwf
  let s₀ : MirState := {
    locals := fun i => if i == 1 then some (.adt 0 (.usize 1)) else none
    block := 0
    stmtIdx := 0
  }
  have hinit : initExtMirState reentrantBuggyFn s₀ := by
    refine ⟨rfl, rfl, rfl, ?_⟩
    refine ⟨⟨.adt 0 (.usize 1), rfl, ⟨rfl, rfl⟩⟩, ?_⟩
    intro j hj
    have hne : j ≠ 1 := by
      intro hEq
      subst hEq
      cases hj with
      | step hle => cases hle
    have hj1 : (j == 1) = false := nat_beq_false_of_ne hne
    dsimp [s₀]
    rw [hj1]
    rfl
  let s₁ : MirState := {
    locals := updateLocal s₀.locals 2 (some (.adt 0 (.usize 0)))
    block := 0
    stmtIdx := 1
  }
  let s₂ : MirState := {
    locals := updateLocal s₁.locals 3 (some (.ref ⟨2⟩))
    block := 0
    stmtIdx := 2
  }
  have hstep1 : ExtMirMachine.step reentrantBuggyFn s₀ (.step () s₁) := rfl
  have hstep2 : ExtMirMachine.step reentrantBuggyFn s₁ (.step () s₂) := rfl
  have hstep3 : ExtMirMachine.step reentrantBuggyFn s₂
      (.externalCall (decide (BoundaryInvHolds 0 ⟨3⟩ s₂))
        (ExternalCallbackNext ⟨4⟩ 0 ⟨1⟩ s₂)) := rfl
  have hnotInv : decide (BoundaryInvHolds 0 ⟨3⟩ s₂) = false := rfl
  have hreach :
      ReachesPrefix ExtMirMachine.step reentrantBuggyFn 3 s₀ [(), ()] .failed :=
    ReachesPrefix.step 2 s₀ s₁ () [()] .failed hstep1
      (ReachesPrefix.step 1 s₁ s₂ () [] .failed hstep2
        (ReachesPrefix.externalCallFail 0 s₂ (decide (BoundaryInvHolds 0 ⟨3⟩ s₂))
          (ExternalCallbackNext ⟨4⟩ 0 ⟨1⟩ s₂) hstep3 hnotInv))
  have hq := hwf { init := s₀, steps := 3 } True.intro
  cases hq with
  | intro hdef _ =>
    exact hdef hinit [(), ()] .failed hreach

#print axioms canary_reentrant_callback_rejected

/-!
### Contrast Model for Unchecked External Call Unsoundly Accepts `reentrantBuggyFn`
-/

def evalTerminatorUnchecked (s : MirState) (term : Terminator) :
    StepResult MirState Unit MirVal :=
  match term with
  | .return_ =>
    match s.locals 0 with
    | some v => .terminated (.normal v)
    | none => .failed
  | .goto target =>
    .step () { s with block := target.index, stmtIdx := 0 }
  | .callExternal dst _argRef adtId target =>
    .externalCall true (ExternalCallbackNext dst adtId target s)

def evalStepUnchecked (body : MirBody) (s : MirState) :
    StepResult MirState Unit MirVal :=
  match body.blocks[s.block]? with
  | none => .failed
  | some bb =>
    match bb.stmts[s.stmtIdx]? with
    | some stmt => evalStmt s stmt
    | none => evalTerminatorUnchecked s bb.terminator

def UncheckedMirMachine : SmallStepMachine MirBody MirState Unit MirVal where
  initState := initExtMirState
  step body s r := r = evalStepUnchecked body s

def UncheckedMirLang : Language :=
  UncheckedMirMachine.toLanguage

/-- Contrast theorem for when `.externalCall` omits the fail-closed
    `BoundaryInvHolds` check, `reentrantBuggyFn` is unsoundly accepted as
    `WellFormed` because it restores `_2 := _1` after the callback returns. -/
theorem canary_unchecked_callback_unsoundly_accepts_reentrantBuggyFn :
    UncheckedMirLang.sem reentrantBuggyFn ≤ UncheckedMirLang.WellFormed := by
  intro q _
  refine ⟨?_, fun _ _ => True.intro⟩
  intro hinit tr out hreach
  rcases q with ⟨⟨locals₀, block₀, stmtIdx₀⟩, steps⟩
  rcases hinit with ⟨hb0, hst0, _hl0, ⟨⟨v1, hv1, _hv1Inv⟩, _hrest⟩⟩
  dsimp at hb0 hst0 hv1 hreach
  subst hb0 hst0
  let s₀ : MirState := ⟨locals₀, 0, 0⟩
  let s₁ : MirState := ⟨updateLocal locals₀ 2 (some (.adt 0 (.usize 0))), 0, 1⟩
  have hstep1 : evalStepUnchecked reentrantBuggyFn s₀ = .step () s₁ := rfl
  cases reachesPrefix_of_step hstep1 hreach with
  | inl hrun => subst hrun; exact True.intro
  | inr hex1 =>
    rcases hex1 with ⟨n1, tr1, hr1⟩
    let s₂ : MirState := ⟨updateLocal s₁.locals 3 (some (.ref ⟨2⟩)), 0, 2⟩
    have hstep2 : evalStepUnchecked reentrantBuggyFn s₁ = .step () s₂ := rfl
    cases reachesPrefix_of_step hstep2 hr1 with
    | inl hrun => subst hrun; exact True.intro
    | inr hex2 =>
      rcases hex2 with ⟨n2, tr2, hr2⟩
      have hstep3 : evalStepUnchecked reentrantBuggyFn s₂ =
          .externalCall true (ExternalCallbackNext ⟨4⟩ 0 ⟨1⟩ s₂) := rfl
      cases reachesPrefix_of_externalCall hstep3 rfl
          (externalCallbackNext_inhabited ⟨4⟩ 0 ⟨1⟩ s₂) hr2 with
      | inl hrun => subst hrun; exact True.intro
      | inr hex3 =>
        rcases hex3 with ⟨n3, ⟨locals₃, block₃, stmtIdx₃⟩, _obs, tr3, hnext, hr3⟩
        rcases hnext with ⟨hframe, _hret4, hs3b, hs3st⟩
        dsimp at hs3b hs3st
        subst hs3b hs3st
        have hs3_loc1 : locals₃ 1 = some v1 := by
          have h14 : (1 : Nat) ≠ 4 := by intro h; cases h
          have hf := hframe 1 h14
          dsimp at hf
          rw [hf]
          exact hv1
        let s₃ : MirState := ⟨locals₃, 1, 0⟩
        let s₄ : MirState := ⟨updateLocal locals₃ 2 (some v1), 1, 1⟩
        have hstep4 : evalStepUnchecked reentrantBuggyFn s₃ = .step () s₄ := by
          change (match locals₃ 1 with
            | some v => StepResult.step () ⟨updateLocal locals₃ 2 (some v), 1, 1⟩
            | none => StepResult.failed) = StepResult.step () s₄
          rw [hs3_loc1]
        cases reachesPrefix_of_step hstep4 hr3 with
        | inl hrun => subst hrun; exact True.intro
        | inr hex4 =>
          rcases hex4 with ⟨n4, tr4, hr4⟩
          let s₅ : MirState := ⟨updateLocal s₄.locals 0 (some v1), 1, 2⟩
          have hstep5 : evalStepUnchecked reentrantBuggyFn s₄ = .step () s₅ := rfl
          cases reachesPrefix_of_step hstep5 hr4 with
          | inl hrun => subst hrun; exact True.intro
          | inr hex5 =>
            rcases hex5 with ⟨n5, tr5, hr5⟩
            have hstep6 :
                evalStepUnchecked reentrantBuggyFn s₅ = .terminated (.normal v1) := rfl
            cases reachesPrefix_of_terminated hstep6 hr5 with
            | inl hrun => subst hrun; exact True.intro
            | inr hterm => subst hterm; exact True.intro

#print axioms canary_unchecked_callback_unsoundly_accepts_reentrantBuggyFn

/-!
### `canary_safe_callback_verified`
-/

def safeCallbackFn : MirBody where
  argTys := [.adt 0]
  retTy := .adt 0
  blocks := [
    { stmts := [
        -- _2 = copy _1 (caller-private local holding valid NonZeroUsize)
        .assign ⟨2⟩ (.use (.copy ⟨1⟩)),
        -- _3 = &_2 (shared reference to valid NonZeroUsize)
        .assign ⟨3⟩ (.ref ⟨2⟩)
      ]
      -- _4 = external_callback(&_2) -> bb1
      terminator := .callExternal ⟨4⟩ ⟨3⟩ 0 ⟨1⟩
    },
    { stmts := [
        -- Verify caller-private local _2 is still initialized after callback
        .assign ⟨5⟩ (.use (.copy ⟨2⟩)),
        -- Return callback's NonZeroUsize result _4
        .assign ⟨0⟩ (.use (.copy ⟨4⟩))
      ]
      terminator := .return_
    }
  ]

/-- Positive canary `safeCallbackFn` is verified under
    `StepResult.externalCall`—it is free of UB at every step budget and every
    normal return value satisfies `NonZeroAdtInv` (`MirVal.satisfiesInv (.adt 0)`),
    while relying on `CallerFramePreserved` so reading caller-private local `_2`
    after the callback never fails. -/
theorem canary_safe_callback_verified :
    ExtMirSem safeCallbackFn ≤
      ExtMirLang.Spec (fun _ out =>
        ∀ ret, out.outcome = .terminated (.normal ret) →
          ret.satisfiesInv (.adt 0)) := by
  intro q _
  have hmain :
      ∀ tr oc,
        initExtMirState safeCallbackFn q.init →
        ReachesPrefix ExtMirMachine.step safeCallbackFn q.steps q.init tr oc →
        oc.isSafe ∧
          (∀ ret, oc = .terminated (.normal ret) → ret.satisfiesInv (.adt 0)) := by
    intro tr oc hinit hreach
    rcases q with ⟨⟨locals₀, block₀, stmtIdx₀⟩, steps⟩
    rcases hinit with ⟨hb0, hst0, _hl0, ⟨⟨v1, hv1, hv1Inv⟩, _hrest⟩⟩
    dsimp at hb0 hst0 hv1 hreach
    subst hb0 hst0
    let s₀ : MirState := ⟨locals₀, 0, 0⟩
    let s₁ : MirState := ⟨updateLocal locals₀ 2 (some v1), 0, 1⟩
    have hstep1 : evalStep safeCallbackFn s₀ = .step () s₁ := by
      change (match locals₀ 1 with
        | some v => StepResult.step () ⟨updateLocal locals₀ 2 (some v), 0, 1⟩
        | none => StepResult.failed) = StepResult.step () s₁
      rw [hv1]
    cases reachesPrefix_of_step hstep1 hreach with
    | inl hrun =>
      subst hrun
      exact ⟨True.intro, fun _ h => by cases h⟩
    | inr hex1 =>
      rcases hex1 with ⟨n1, tr1, hr1⟩
      let s₂ : MirState := ⟨updateLocal s₁.locals 3 (some (.ref ⟨2⟩)), 0, 2⟩
      have hstep2 : evalStep safeCallbackFn s₁ = .step () s₂ := rfl
      cases reachesPrefix_of_step hstep2 hr1 with
      | inl hrun =>
        subst hrun
        exact ⟨True.intro, fun _ h => by cases h⟩
      | inr hex2 =>
        rcases hex2 with ⟨n2, tr2, hr2⟩
        have hstep3 : evalStep safeCallbackFn s₂ =
            .externalCall (decide (BoundaryInvHolds 0 ⟨3⟩ s₂))
              (ExternalCallbackNext ⟨4⟩ 0 ⟨1⟩ s₂) := rfl
        have hBoundary : decide (BoundaryInvHolds 0 ⟨3⟩ s₂) = true := by
          unfold BoundaryInvHolds checkBoundaryInv
          dsimp [s₂, s₁, updateLocal]
          cases v1 with
          | usize _ => cases hv1Inv
          | ref _ => cases hv1Inv
          | adt vId inner =>
            rcases hv1Inv with ⟨hvId, hNonZero⟩
            subst hvId
            exact decide_eq_true hNonZero
        cases reachesPrefix_of_externalCall hstep3 hBoundary
            (externalCallbackNext_inhabited ⟨4⟩ 0 ⟨1⟩ s₂) hr2 with
        | inl hrun =>
          subst hrun
          exact ⟨True.intro, fun _ h => by cases h⟩
        | inr hex3 =>
          rcases hex3 with ⟨n3, ⟨locals₃, block₃, stmtIdx₃⟩, _obs, tr3, hnext, hr3⟩
          rcases hnext with ⟨hframe, ⟨retVal, hret4, hretInv⟩, hs3b, hs3st⟩
          dsimp at hret4 hs3b hs3st
          subst hs3b hs3st
          have hs3_loc2 : locals₃ 2 = some v1 := by
            have h24 : (2 : Nat) ≠ 4 := by intro h; cases h
            have hf := hframe 2 h24
            dsimp at hf
            rw [hf]
            rfl
          let s₃ : MirState := ⟨locals₃, 1, 0⟩
          let s₄ : MirState := ⟨updateLocal locals₃ 5 (some v1), 1, 1⟩
          have hstep4 : evalStep safeCallbackFn s₃ = .step () s₄ := by
            change (match locals₃ 2 with
              | some v => StepResult.step () ⟨updateLocal locals₃ 5 (some v), 1, 1⟩
              | none => StepResult.failed) = StepResult.step () s₄
            rw [hs3_loc2]
          cases reachesPrefix_of_step hstep4 hr3 with
          | inl hrun =>
            subst hrun
            exact ⟨True.intro, fun _ h => by cases h⟩
          | inr hex4 =>
            rcases hex4 with ⟨n4, tr4, hr4⟩
            have hs4_loc4 : s₄.locals 4 = some retVal := by
              dsimp [s₄, updateLocal]
              exact hret4
            let s₅ : MirState := ⟨updateLocal s₄.locals 0 (some retVal), 1, 2⟩
            have hstep5 : evalStep safeCallbackFn s₄ = .step () s₅ := by
              change (match s₄.locals 4 with
                | some v => StepResult.step () ⟨updateLocal s₄.locals 0 (some v), 1, 2⟩
                | none => StepResult.failed) = StepResult.step () s₅
              rw [hs4_loc4]
            cases reachesPrefix_of_step hstep5 hr4 with
            | inl hrun =>
              subst hrun
              exact ⟨True.intro, fun _ h => by cases h⟩
            | inr hex5 =>
              rcases hex5 with ⟨n5, tr5, hr5⟩
              have hstep6 :
                  evalStep safeCallbackFn s₅ = .terminated (.normal retVal) := rfl
              cases reachesPrefix_of_terminated hstep6 hr5 with
              | inl hrun =>
                subst hrun
                exact ⟨True.intro, fun _ h => by cases h⟩
              | inr hterm =>
                subst hterm
                refine ⟨True.intro, ?_⟩
                intro ret hEq
                injection hEq with hTerm
                injection hTerm with hRet
                subst hRet
                exact hretInv
  refine ⟨fun hinit tr oc hreach => (hmain tr oc hinit hreach).1, ?_⟩
  intro out hval
  exact (hmain out.trace out.outcome hval.1 hval.2).2

#print axioms canary_safe_callback_verified

end StructuralExternalCall

/-!
## Part II: Complete Negative Canary Suite for Trusted Semantics Mutation Audit

This namespace mechanizes the complete 24-canary negative refutation suite
(`canary_M01` through `canary_M24b`) over the exact MIR operational semantics
and crate verification envelope of `Trusted/MirSemantics.lean` (`trusted-core`).
An isomorphic 24-canary suite for `Trusted/X86Semantics.lean` (`mir-to-x86`) is
generated and verified by `run_trusted_mutation_audit.py`.
-/

namespace TrustedMutationCanaries

open StructuralExternalCall (Preorder instPreorderProp instPreorderFun Partial
  instPreorderPartial Behavior Language TerminationKind PrefixOutcome
  ExecQuery ExecOut)

inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed

structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

inductive ReachesPrefix
    (step : Prog → State → StepResult State Obs Val → Prop) (p : Prog) :
    Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefix step p 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome Val) :
      step p s (.step obs s') →
      ReachesPrefix step p n s' tr out →
      ReachesPrefix step p (n + 1) s (obs :: tr) out
  | choice (n : Nat) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      step p s (.choice branches) →
      branches s' →
      ReachesPrefix step p n s' tr out →
      ReachesPrefix step p (n + 1) s tr out
  | emptyChoice (n : Nat) (s : State) (branches : State → Prop) :
      step p s (.choice branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix step p (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      step p s (.terminated term) →
      ReachesPrefix step p (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) :
      step p s .failed →
      ReachesPrefix step p (n + 1) s [] .failed
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, step p s r) →
      ReachesPrefix step p (n + 1) s [] .stuck

def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M.step p q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M.step p q.steps q.init out.trace out.outcome
  }

def SmallStepMachine.toLanguage (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog := Prog
  Query := ExecQuery State
  Out := ExecOut Obs Val
  sem := BehaviorOf M

structure LocalId where
  index : Nat

structure BlockId where
  index : Nat

inductive FieldAccess where
  | pubSafe
  | priv
  | unsafeField

inductive MirTy where
  | usize
  | bool
  | unit
  | adt (id : Nat)
  | param (idx : Nat)
  | ref (inner : MirTy)

structure FieldDecl where
  ty : MirTy
  access : FieldAccess

structure AdtDecl where
  id : Nat
  fields : List FieldDecl
  nonExhaustive : Bool := false

def AdtDecl.allFieldsPubSafe (decl : AdtDecl) : Bool :=
  !decl.nonExhaustive &&
  decl.fields.all (fun f =>
    match f.access with
    | .pubSafe => true
    | .priv | .unsafeField => false)

inductive MirVal where
  | usize (bits : Nat)
  | bool (b : Bool)
  | unit
  | adt (id : Nat) (inner : MirVal)
  | bytes (sz : Nat) (bits : Nat)
  | ref (loc : LocalId)

inductive Operand where
  | copy (src : LocalId)
  | move (src : LocalId)
  | constVal (val : MirVal)

inductive BinOp where
  | eq

inductive Rvalue where
  | use (op : Operand)
  | binaryOp (op : BinOp) (lhs : Operand) (rhs : Operand)
  | aggregate (adtId : Nat) (op : Operand)
  | field0 (src : LocalId)
  | ref (src : LocalId)
  | reborrow (src : LocalId)

inductive Stmt where
  | assign (dst : LocalId) (rv : Rvalue)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | nop

mutual
  inductive Terminator where
    | return_
    | goto (target : BlockId)
    | unreachable
    | panic
    | switchInt (discr : Operand) (falseTarget : BlockId) (trueTarget : BlockId)
    | callSizeOf (dst : LocalId) (ty : MirTy) (target : BlockId)
    | callTransmuteCopy (dst : LocalId) (srcTy dstTy : MirTy) (op : Operand)
        (target : BlockId)
    | call1 (dst : LocalId) (callee : MirBody) (arg : Operand) (target : BlockId)
        (typeArgs : List MirTy := [])

  structure BasicBlock where
    stmts : List Stmt
    terminator : Terminator

  structure MirBody where
    argTys : List MirTy
    retTy : MirTy
    localCount : Nat
    blocks : List BasicBlock
    requiredConsts : List MirBody := []
end

structure StackFrame where
  callerBody : MirBody
  callerLocals : Nat → Option MirVal
  callerTySizes : Nat → Nat := fun _ => 0
  retDst : LocalId
  retBlock : Nat

structure MirState where
  locals : Nat → Option MirVal
  block : Nat
  stmtIdx : Nat
  tySizes : Nat → Nat := fun _ => 0
  curBody : Option MirBody := none
  stack : List StackFrame := []

def updateLocal (locals : Nat → Option MirVal) (target : Nat)
    (val : Option MirVal) : Nat → Option MirVal :=
  fun i => if i == target then val else locals i

def evalTyByteSize (tySizes : Nat → Nat) (ty : MirTy) : Nat :=
  match ty with
  | .usize => 8
  | .bool => 1
  | .unit => 0
  | .adt _ => 8
  | .param idx => tySizes idx
  | .ref _ => 8

def substTySizes (tySizes : Nat → Nat) (typeArgs : List MirTy)
    (idx : Nat) : Nat :=
  match typeArgs[idx]? with
  | some ty => evalTyByteSize tySizes ty
  | none => tySizes idx

abbrev AdtInv := Nat → MirVal → Prop

def defaultAdtInv : AdtInv :=
  fun _ _ => True

def MirVal.satisfiesInv (adtInv : AdtInv) (tySizes : Nat → Nat)
    (v : MirVal) (ty : MirTy) : Prop :=
  match ty, v with
  | .usize, .usize _ => True
  | .bool, .bool _ => True
  | .unit, .unit => True
  | .adt tyId, .adt vId (.usize n) => vId = tyId ∧ adtInv tyId (.usize n)
  | .param idx, .bytes sz _ => sz = tySizes idx
  | .ref _, .ref _ => True
  | _, _ => False

abbrev MirVal.hasTy (tySizes : Nat → Nat) (v : MirVal) (ty : MirTy) : Prop :=
  v.satisfiesInv defaultAdtInv tySizes ty

def argsMatchInv (adtInv : AdtInv) (tySizes : Nat → Nat)
    (argTys : List MirTy) (locals : Nat → Option MirVal) : Prop :=
  argTys.foldr
    (fun ty rest k =>
      (∃ v, locals k = some v ∧ v.satisfiesInv adtInv tySizes ty) ∧
      rest (k + 1))
    (fun k => ∀ j, k ≤ j → locals j = none)
    1

abbrev argsMatchLocals (tySizes : Nat → Nat) (argTys : List MirTy)
    (locals : Nat → Option MirVal) : Prop :=
  argsMatchInv defaultAdtInv tySizes argTys locals

def initEntryState (body : MirBody) (s : MirState) : Prop :=
  s.block = 0 ∧
  s.stmtIdx = 0 ∧
  s.curBody = none ∧
  s.stack = [] ∧
  s.locals 0 = none ∧
  argsMatchLocals s.tySizes body.argTys s.locals

def evalOperand (locals : Nat → Option MirVal) (op : Operand) :
    Option (MirVal × (Nat → Option MirVal)) :=
  match op with
  | .copy src =>
    match locals src.index with
    | some v => some (v, locals)
    | none => none
  | .move src =>
    match locals src.index with
    | some v => some (v, updateLocal locals src.index none)
    | none => none
  | .constVal v => some (v, locals)

def evalBinOp (op : BinOp) (lhs rhs : MirVal) : Option MirVal :=
  match op, lhs, rhs with
  | .eq, .usize a, .usize b => some (.bool (decide (a = b)))
  | .eq, .bool a, .bool b => some (.bool (decide (a = b)))
  | .eq, .unit, .unit => some (.bool true)
  | _, _, _ => none

def evalMirStmt (s : MirState) (stmt : Stmt) : StepResult MirState Unit MirVal :=
  match stmt with
  | .assign dst (.use op) =>
    match evalOperand s.locals op with
    | some (v, locals') =>
      .step () { s with
        locals := updateLocal locals' dst.index (some v)
        stmtIdx := s.stmtIdx + 1
      }
    | none => .failed
  | .assign dst (.binaryOp op lhs rhs) =>
    match evalOperand s.locals lhs with
    | some (v1, locals1) =>
      match evalOperand locals1 rhs with
      | some (v2, locals2) =>
        match evalBinOp op v1 v2 with
        | some outVal =>
          .step () { s with
            locals := updateLocal locals2 dst.index (some outVal)
            stmtIdx := s.stmtIdx + 1
          }
        | none => .failed
      | none => .failed
    | none => .failed
  | .assign dst (.aggregate adtId op) =>
    match evalOperand s.locals op with
    | some (v, locals') =>
      .step () { s with
        locals := updateLocal locals' dst.index (some (.adt adtId v))
        stmtIdx := s.stmtIdx + 1
      }
    | none => .failed
  | .assign dst (.field0 src) =>
    match s.locals src.index with
    | some (.adt _ inner) =>
      .step () { s with
        locals := updateLocal s.locals dst.index (some inner)
        stmtIdx := s.stmtIdx + 1
      }
    | _ => .failed
  | .assign dst (.ref src) =>
    match s.locals src.index with
    | some _ =>
      .step () { s with
        locals := updateLocal s.locals dst.index (some (.ref src))
        stmtIdx := s.stmtIdx + 1
      }
    | none => .failed
  | .assign dst (.reborrow src) =>
    match s.locals src.index with
    | some (.ref target) =>
      match s.locals target.index with
      | some _ =>
        .step () { s with
          locals := updateLocal s.locals dst.index (some (.ref target))
          stmtIdx := s.stmtIdx + 1
        }
      | none => .failed
    | _ => .failed
  | .storageLive loc =>
    .step () { s with
      locals := updateLocal s.locals loc.index none
      stmtIdx := s.stmtIdx + 1
    }
  | .storageDead loc =>
    .step () { s with
      locals := updateLocal s.locals loc.index none
      stmtIdx := s.stmtIdx + 1
    }
  | .nop =>
    .step () { s with stmtIdx := s.stmtIdx + 1 }

def evalTransmuteCopy (tySizes : Nat → Nat) (locals : Nat → Option MirVal)
    (srcTy dstTy : MirTy) (argVal : MirVal) : Option MirVal :=
  let srcSz := evalTyByteSize tySizes srcTy
  let dstSz := evalTyByteSize tySizes dstTy
  if decide (srcSz = dstSz) then
    match argVal with
    | .ref target =>
      match locals target.index with
      | some (.bytes vSz bits) =>
        if decide (vSz = srcSz) then
          some (.bytes dstSz bits)
        else
          none
      | _ => none
    | _ => none
  else
    none

def evalMirTerminator (activeBody : MirBody) (s : MirState)
    (term : Terminator) : StepResult MirState Unit MirVal :=
  match term with
  | .return_ =>
    match s.locals 0 with
    | none => .failed
    | some retVal =>
      match s.stack with
      | [] => .terminated (.normal retVal)
      | frame :: restStack =>
        .step () {
          locals := updateLocal frame.callerLocals frame.retDst.index (some retVal)
          block := frame.retBlock
          stmtIdx := 0
          tySizes := frame.callerTySizes
          curBody := if restStack.isEmpty then none else some frame.callerBody
          stack := restStack
        }
  | .goto target =>
    .step () { s with block := target.index, stmtIdx := 0 }
  | .unreachable =>
    .failed
  | .panic =>
    .terminated .unwind
  | .switchInt discr falseTarget trueTarget =>
    match evalOperand s.locals discr with
    | some (.bool false, locals') =>
      .step () { s with locals := locals', block := falseTarget.index, stmtIdx := 0 }
    | some (.bool true, locals') =>
      .step () { s with locals := locals', block := trueTarget.index, stmtIdx := 0 }
    | _ => .failed
  | .callSizeOf dst ty target =>
    let sz := evalTyByteSize s.tySizes ty
    .step () { s with
      locals := updateLocal s.locals dst.index (some (.usize sz))
      block := target.index
      stmtIdx := 0
    }
  | .callTransmuteCopy dst srcTy dstTy op target =>
    match evalOperand s.locals op with
    | some (argVal, locals') =>
      match evalTransmuteCopy s.tySizes locals' srcTy dstTy argVal with
      | some outVal =>
        .step () { s with
          locals := updateLocal locals' dst.index (some outVal)
          block := target.index
          stmtIdx := 0
        }
      | none => .failed
    | none => .failed
  | .call1 dst callee arg target typeArgs =>
    match evalOperand s.locals arg with
    | some (argVal, callerLocals') =>
      let calleeLocals : Nat → Option MirVal :=
        updateLocal (fun _ => none) 1 (some argVal)
      let frame : StackFrame := {
        callerBody := activeBody
        callerLocals := callerLocals'
        callerTySizes := s.tySizes
        retDst := dst
        retBlock := target.index
      }
      .step () {
        locals := calleeLocals
        block := 0
        stmtIdx := 0
        tySizes := substTySizes s.tySizes typeArgs
        curBody := some callee
        stack := frame :: s.stack
      }
    | none => .failed

def evalMirStep (rootBody : MirBody) (s : MirState) :
    StepResult MirState Unit MirVal :=
  let active := s.curBody.getD rootBody
  match active.blocks[s.block]? with
  | none => .failed
  | some bb =>
    match bb.stmts[s.stmtIdx]? with
    | some stmt => evalMirStmt s stmt
    | none => evalMirTerminator active s bb.terminator

abbrev MirStep (body : MirBody) (s : MirState)
    (r : StepResult MirState Unit MirVal) : Prop :=
  r = evalMirStep body s

inductive RequiresConst :
    (Nat → Nat) → MirBody → (Nat → Nat) → MirBody → Prop where
  | direct {tySizes : Nat → Nat} {body c : MirBody} :
      c ∈ body.requiredConsts →
      RequiresConst tySizes body tySizes c
  | nested {tySizes tySizes' : Nat → Nat} {body c' c : MirBody} :
      c' ∈ body.requiredConsts →
      RequiresConst tySizes c' tySizes' c →
      RequiresConst tySizes body tySizes' c
  | call1 {tySizes tySizes' : Nat → Nat} {body callee c : MirBody}
      {bb : BasicBlock} {dst : LocalId} {arg : Operand} {target : BlockId}
      {typeArgs : List MirTy} :
      bb ∈ body.blocks →
      bb.terminator = .call1 dst callee arg target typeArgs →
      RequiresConst (substTySizes tySizes typeArgs) callee tySizes' c →
      RequiresConst tySizes body tySizes' c

def ConstSucceeds (tySizes : Nat → Nat) (c : MirBody) : Prop :=
  ∃ (s₀ : MirState) (n : Nat) (tr : List Unit) (v : MirVal),
    s₀.tySizes = tySizes ∧
    initEntryState c s₀ ∧
    ReachesPrefix MirStep c n s₀ tr (.terminated (.normal v))

def MonoAdmitted (tySizes : Nat → Nat) (body : MirBody) : Prop :=
  ∀ tySizes' c, RequiresConst tySizes body tySizes' c → ConstSucceeds tySizes' c

def initMirState (body : MirBody) (s : MirState) : Prop :=
  initEntryState body s ∧ MonoAdmitted s.tySizes body

def MirMachine : SmallStepMachine MirBody MirState Unit MirVal where
  initState := initMirState
  step := MirStep

def MirLang : Language :=
  MirMachine.toLanguage

abbrev MirSem (body : MirBody) : MirLang.Behavior :=
  MirLang.sem body

def AdmissibleAdtInv (adts : List AdtDecl) (adtInv : AdtInv) : Prop :=
  ∀ decl, decl ∈ adts → decl.allFieldsPubSafe = true →
    ∀ n, adtInv decl.id (.usize n)

def EnsuresRetLibInv (adtInv : AdtInv) (retTy : MirTy)
    (pre : ExecQuery MirState → Prop) : MirLang.Behavior :=
  MirLang.SpecOn pre (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      ret.satisfiesInv adtInv q.init.tySizes retTy)

def EnsuresEqArg (argLocal : Nat) : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      q.init.locals argLocal = some ret)

def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

inductive TCBItem where
  | rustcLowering (fnName : String) (body : MirBody)
  | userAxiom (name : String) (prop : Prop)

def defaultTrustPolicy (item : TCBItem) : Prop :=
  match item with
  | .rustcLowering _ _ => True
  | .userAxiom _ _ => False

inductive FnKind where
  | pubSafe (traitLaws : Prop := True)
  | pubUnsafe (traitLaws : Prop := True) (safetyPre : ExecQuery MirState → Prop)
  | priv (pre : ExecQuery MirState → Prop := fun _ => True)

structure CapturedFn where
  name : String
  prog : MirBody
  kind : FnKind := .pubSafe True
  specs : List MirLang.Behavior := []

def CapturedFn.effectivePre (adtInv : AdtInv) (fn : CapturedFn)
    (q : ExecQuery MirState) : Prop :=
  match fn.kind with
  | .pubSafe traitLaws =>
    traitLaws ∧
    argsMatchInv adtInv q.init.tySizes fn.prog.argTys q.init.locals
  | .pubUnsafe traitLaws safetyPre =>
    traitLaws ∧
    argsMatchInv adtInv q.init.tySizes fn.prog.argTys q.init.locals ∧
    safetyPre q
  | .priv internalPre =>
    internalPre q

def CapturedFn.effectiveSpecs (adtInv : AdtInv) (fn : CapturedFn) :
    List MirLang.Behavior :=
  let pre := fn.effectivePre adtInv
  match fn.kind with
  | .pubSafe _ | .pubUnsafe _ _ =>
    EnsuresRetLibInv adtInv fn.prog.retTy pre :: fn.specs
  | .priv _ =>
    fn.specs

structure UnsafeImplObligation where
  implName : String
  whereBounds : Prop := True
  traitLaw : AdtInv → Prop

structure Crate where
  adts : List AdtDecl := []
  adtInv : AdtInv := defaultAdtInv
  unsafeImpls : List UnsafeImplObligation := []
  functions : List CapturedFn
  tcb : List TCBItem

def CrateTheorem (c : Crate) : Prop :=
  c.functions ≠ [] ∧
  AdmissibleAdtInv c.adts c.adtInv ∧
  AllHold (c.unsafeImpls.map (fun u => u.whereBounds → u.traitLaw c.adtInv)) ∧
  AllHold (c.tcb.map defaultTrustPolicy) ∧
  AllHold (c.functions.map (fun fn =>
    MirSem fn.prog ≤ MirLang.WellFormedOn (fn.effectivePre c.adtInv) ∧
    AllHold ((fn.effectiveSpecs c.adtInv).map (fun s => MirSem fn.prog ≤ s))))

/-!
### Helper Lemmas for Concise Negative Canary Proofs
-/

def s0_noArgs : MirState where
  locals := fun _ => none
  block := 0
  stmtIdx := 0

theorem initEntryState_s0_noArgs (body : MirBody)
    (hArgs : body.argTys = []) :
    initEntryState body s0_noArgs := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  unfold argsMatchLocals argsMatchInv
  rw [hArgs]
  intro j _
  rfl

theorem monoAdmitted_of_no_call1 (tySizes : Nat → Nat) (body : MirBody)
    (hReq : body.requiredConsts = [])
    (hNoCall1 : ∀ bb ∈ body.blocks, ∀ dst callee arg target typeArgs,
      bb.terminator ≠ .call1 dst callee arg target typeArgs) :
    MonoAdmitted tySizes body := by
  intro tySizes' c hrc
  cases hrc with
  | direct hmem =>
    rw [hReq] at hmem
    cases hmem
  | nested hmem _ =>
    rw [hReq] at hmem
    cases hmem
  | call1 hbb hterm _ =>
    exact False.elim (hNoCall1 _ hbb _ _ _ _ _ hterm)

theorem initMirState_oneBlock_noArgs (body : MirBody) (bb : BasicBlock)
    (hArgs : body.argTys = [])
    (hReq : body.requiredConsts = [])
    (hBlocks : body.blocks = [bb])
    (hTerm : ∀ dst callee arg target typeArgs,
      bb.terminator ≠ .call1 dst callee arg target typeArgs) :
    initMirState body s0_noArgs := by
  refine ⟨initEntryState_s0_noArgs body hArgs, ?_⟩
  refine monoAdmitted_of_no_call1 s0_noArgs.tySizes body hReq ?_
  intro b hb
  rw [hBlocks] at hb
  cases hb with
  | head => exact hTerm
  | tail _ hnil => cases hnil

theorem initMirState_twoBlocks_noArgs (body : MirBody) (bb0 bb1 : BasicBlock)
    (hArgs : body.argTys = [])
    (hReq : body.requiredConsts = [])
    (hBlocks : body.blocks = [bb0, bb1])
    (hTerm0 : ∀ dst callee arg target typeArgs,
      bb0.terminator ≠ .call1 dst callee arg target typeArgs)
    (hTerm1 : ∀ dst callee arg target typeArgs,
      bb1.terminator ≠ .call1 dst callee arg target typeArgs) :
    initMirState body s0_noArgs := by
  refine ⟨initEntryState_s0_noArgs body hArgs, ?_⟩
  refine monoAdmitted_of_no_call1 s0_noArgs.tySizes body hReq ?_
  intro b hb
  rw [hBlocks] at hb
  cases hb with
  | head => exact hTerm0
  | tail _ htail =>
    cases htail with
    | head => exact hTerm1
    | tail _ hnil => cases hnil

theorem not_wellFormed_of_reaches_failed
    {body : MirBody} {s₀ : MirState} {n : Nat} {tr : List Unit}
    (hinit : initMirState body s₀)
    (hreach : ReachesPrefix MirStep body n s₀ tr .failed) :
    ¬ (MirSem body ≤ MirLang.WellFormed) := by
  intro hwf
  have hq := hwf { init := s₀, steps := n } True.intro
  cases hq with
  | intro hdef _ => exact hdef hinit tr .failed hreach

theorem not_spec_of_reaches_normal
    {body : MirBody} {s₀ : MirState} {n : Nat} {tr : List Unit} {v : MirVal}
    {Post : ExecQuery MirState → ExecOut Unit MirVal → Prop}
    (hinit : initMirState body s₀)
    (hreach : ReachesPrefix MirStep body n s₀ tr (.terminated (.normal v)))
    (hnot : ¬ Post { init := s₀, steps := n }
      { trace := tr, outcome := .terminated (.normal v) }) :
    ¬ (MirSem body ≤ MirLang.Spec Post) := by
  intro hspec
  have hq := hspec { init := s₀, steps := n } True.intro
  cases hq with
  | intro _ hval =>
    exact hnot (hval { trace := tr, outcome := .terminated (.normal v) }
      ⟨hinit, hreach⟩)

/-!
### The 24 Negative Canary Refutation Theorems (M01–M24)
-/

-- M01: `evalTyByteSize` `.usize` size = 8 (refutes wrong size 4)
def sizeOfUsizeBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [
    { stmts := [], terminator := .callSizeOf ⟨0⟩ .usize ⟨1⟩ },
    { stmts := [], terminator := .return_ }
  ]

theorem canary_M01_sizeOf_usize_wrong_rejected :
    ¬ (MirSem sizeOfUsizeBody ≤
      MirLang.Spec (fun _ out =>
        ∀ ret, out.outcome = .terminated (.normal ret) → ret = .usize 4)) := by
  have hinit : initMirState sizeOfUsizeBody s0_noArgs :=
    initMirState_twoBlocks_noArgs sizeOfUsizeBody _ _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.usize 8))
    block := 1
    stmtIdx := 0
  }
  have hreach : ReachesPrefix MirStep sizeOfUsizeBody 2 s0_noArgs [()]
      (.terminated (.normal (MirVal.usize 8))) :=
    ReachesPrefix.step 1 s0_noArgs s₁ () []
      (.terminated (.normal (MirVal.usize 8))) rfl
      (ReachesPrefix.terminated 0 s₁ (.normal (MirVal.usize 8)) rfl)
  refine not_spec_of_reaches_normal hinit hreach ?_
  intro hpost
  have heq := hpost (MirVal.usize 8) rfl
  cases heq

-- M02: `evalTyByteSize` `.bool` size = 1 (refutes wrong size 2)
def sizeOfBoolBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [
    { stmts := [], terminator := .callSizeOf ⟨0⟩ .bool ⟨1⟩ },
    { stmts := [], terminator := .return_ }
  ]

theorem canary_M02_sizeOf_bool_wrong_rejected :
    ¬ (MirSem sizeOfBoolBody ≤
      MirLang.Spec (fun _ out =>
        ∀ ret, out.outcome = .terminated (.normal ret) → ret = .usize 2)) := by
  have hinit : initMirState sizeOfBoolBody s0_noArgs :=
    initMirState_twoBlocks_noArgs sizeOfBoolBody _ _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.usize 1))
    block := 1
    stmtIdx := 0
  }
  have hreach : ReachesPrefix MirStep sizeOfBoolBody 2 s0_noArgs [()]
      (.terminated (.normal (MirVal.usize 1))) :=
    ReachesPrefix.step 1 s0_noArgs s₁ () []
      (.terminated (.normal (MirVal.usize 1))) rfl
      (ReachesPrefix.terminated 0 s₁ (.normal (MirVal.usize 1)) rfl)
  refine not_spec_of_reaches_normal hinit hreach ?_
  intro hpost
  have heq := hpost (MirVal.usize 1) rfl
  cases heq

-- M03: `evalOperand` `.copy` of uninitialized local fails
def uninitCopyBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 3
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.copy ⟨2⟩))]
      terminator := .return_ }
  ]

theorem canary_M03_uninit_copy_violates_wellFormed :
    ¬ (MirSem uninitCopyBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState uninitCopyBody s0_noArgs :=
    initMirState_oneBlock_noArgs uninitCopyBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs rfl)

-- M04: `evalOperand` `.move` deinitializes source local (use-after-move fails)
def doubleMoveBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨2⟩ (.use (.constVal (.usize 7))),
        .assign ⟨3⟩ (.use (.move ⟨2⟩)),
        .assign ⟨0⟩ (.use (.copy ⟨2⟩))
      ]
      terminator := .return_ }
  ]

theorem canary_M04_double_move_violates_wellFormed :
    ¬ (MirSem doubleMoveBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState doubleMoveBody s0_noArgs :=
    initMirState_oneBlock_noArgs doubleMoveBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 2 (some (.usize 7))
    stmtIdx := 1
  }
  let s₂ : MirState := { s₁ with
    locals := updateLocal (updateLocal s₁.locals 2 none) 3 (some (.usize 7))
    stmtIdx := 2
  }
  have hreach : ReachesPrefix MirStep doubleMoveBody 3 s0_noArgs [(), ()] .failed :=
    ReachesPrefix.step 2 s0_noArgs s₁ () [()] .failed rfl
      (ReachesPrefix.step 1 s₁ s₂ () [] .failed rfl
        (ReachesPrefix.failed 0 s₂ rfl))
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M05: `evalOperand` `.move` of uninitialized local fails
def uninitMoveBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 3
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.move ⟨2⟩))]
      terminator := .return_ }
  ]

theorem canary_M05_uninit_move_violates_wellFormed :
    ¬ (MirSem uninitMoveBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState uninitMoveBody s0_noArgs :=
    initMirState_oneBlock_noArgs uninitMoveBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs rfl)

-- M06: `evalBinOp` `.eq` on distinct `.usize` values evaluates to `false`, not `true`
def eqDistinctUsizeBody : MirBody where
  argTys := []
  retTy := .bool
  localCount := 1
  blocks := [
    { stmts := [
        .assign ⟨0⟩ (.binaryOp .eq (.constVal (.usize 0)) (.constVal (.usize 1)))
      ]
      terminator := .return_ }
  ]

theorem canary_M06_eq_distinct_usize_not_true :
    ¬ (MirSem eqDistinctUsizeBody ≤
      MirLang.Spec (fun _ out =>
        ∀ ret, out.outcome = .terminated (.normal ret) → ret = .bool true)) := by
  have hinit : initMirState eqDistinctUsizeBody s0_noArgs :=
    initMirState_oneBlock_noArgs eqDistinctUsizeBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.bool false))
    stmtIdx := 1
  }
  have hreach : ReachesPrefix MirStep eqDistinctUsizeBody 2 s0_noArgs [()]
      (.terminated (.normal (MirVal.bool false))) :=
    ReachesPrefix.step 1 s0_noArgs s₁ () []
      (.terminated (.normal (MirVal.bool false))) rfl
      (ReachesPrefix.terminated 0 s₁ (.normal (MirVal.bool false)) rfl)
  refine not_spec_of_reaches_normal hinit hreach ?_
  intro hpost
  have heq := hpost (MirVal.bool false) rfl
  cases heq

-- M07: `evalBinOp` on mismatched operand types (`usize` vs `bool`) fails
def illTypedBinOpBody : MirBody where
  argTys := []
  retTy := .bool
  localCount := 1
  blocks := [
    { stmts := [
        .assign ⟨0⟩ (.binaryOp .eq (.constVal (.usize 0)) (.constVal (.bool false)))
      ]
      terminator := .return_ }
  ]

theorem canary_M07_illTyped_binOp_violates_wellFormed :
    ¬ (MirSem illTypedBinOpBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState illTypedBinOpBody s0_noArgs :=
    initMirState_oneBlock_noArgs illTypedBinOpBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs rfl)

-- M08: `evalMirStmt` `.assign _ (.use _)` `none` branch fails (cannot silently skip)
def failedUseSkipBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal (.usize 0))),
        .assign ⟨2⟩ (.use (.copy ⟨3⟩))
      ]
      terminator := .return_ }
  ]

theorem canary_M08_failed_use_assign_violates_wellFormed :
    ¬ (MirSem failedUseSkipBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState failedUseSkipBody s0_noArgs :=
    initMirState_oneBlock_noArgs failedUseSkipBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.usize 0))
    stmtIdx := 1
  }
  have hreach : ReachesPrefix MirStep failedUseSkipBody 2 s0_noArgs [()] .failed :=
    ReachesPrefix.step 1 s0_noArgs s₁ () [] .failed rfl
      (ReachesPrefix.failed 0 s₁ rfl)
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M09: `evalMirStmt` `.assign _ (.aggregate _ _)` `none` branch fails
def uninitAggregateBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal (.usize 0))),
        .assign ⟨2⟩ (.aggregate 0 (.copy ⟨3⟩))
      ]
      terminator := .return_ }
  ]

theorem canary_M09_uninit_aggregate_violates_wellFormed :
    ¬ (MirSem uninitAggregateBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState uninitAggregateBody s0_noArgs :=
    initMirState_oneBlock_noArgs uninitAggregateBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.usize 0))
    stmtIdx := 1
  }
  have hreach : ReachesPrefix MirStep uninitAggregateBody 2 s0_noArgs [()] .failed :=
    ReachesPrefix.step 1 s0_noArgs s₁ () [] .failed rfl
      (ReachesPrefix.failed 0 s₁ rfl)
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M10: `evalMirStmt` `.assign _ (.field0 _)` on non-ADT fails
def field0NonAdtBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 3
  blocks := [
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal (.usize 0))),
        .assign ⟨2⟩ (.field0 ⟨0⟩)
      ]
      terminator := .return_ }
  ]

theorem canary_M10_field0_non_adt_violates_wellFormed :
    ¬ (MirSem field0NonAdtBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState field0NonAdtBody s0_noArgs :=
    initMirState_oneBlock_noArgs field0NonAdtBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.usize 0))
    stmtIdx := 1
  }
  have hreach : ReachesPrefix MirStep field0NonAdtBody 2 s0_noArgs [()] .failed :=
    ReachesPrefix.step 1 s0_noArgs s₁ () [] .failed rfl
      (ReachesPrefix.failed 0 s₁ rfl)
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M11: `evalMirStmt` `.assign _ (.ref _)` on uninitialized local fails
def refUninitBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal (.usize 0))),
        .assign ⟨2⟩ (.ref ⟨3⟩)
      ]
      terminator := .return_ }
  ]

theorem canary_M11_ref_uninit_violates_wellFormed :
    ¬ (MirSem refUninitBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState refUninitBody s0_noArgs :=
    initMirState_oneBlock_noArgs refUninitBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.usize 0))
    stmtIdx := 1
  }
  have hreach : ReachesPrefix MirStep refUninitBody 2 s0_noArgs [()] .failed :=
    ReachesPrefix.step 1 s0_noArgs s₁ () [] .failed rfl
      (ReachesPrefix.failed 0 s₁ rfl)
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M12: `evalMirStmt` `.assign _ (.reborrow _)` on dead referent (`StorageDead`) fails
def reborrowDeadTargetBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 5
  blocks := [
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal (.usize 0))),
        .assign ⟨2⟩ (.use (.constVal (.usize 1))),
        .assign ⟨3⟩ (.ref ⟨2⟩),
        .storageDead ⟨2⟩,
        .assign ⟨4⟩ (.reborrow ⟨3⟩)
      ]
      terminator := .return_ }
  ]

theorem canary_M12_reborrow_dead_target_violates_wellFormed :
    ¬ (MirSem reborrowDeadTargetBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState reborrowDeadTargetBody s0_noArgs :=
    initMirState_oneBlock_noArgs reborrowDeadTargetBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.usize 0))
    stmtIdx := 1
  }
  let s₂ : MirState := { s₁ with
    locals := updateLocal s₁.locals 2 (some (.usize 1))
    stmtIdx := 2
  }
  let s₃ : MirState := { s₂ with
    locals := updateLocal s₂.locals 3 (some (.ref ⟨2⟩))
    stmtIdx := 3
  }
  let s₄ : MirState := { s₃ with
    locals := updateLocal s₃.locals 2 none
    stmtIdx := 4
  }
  have hreach : ReachesPrefix MirStep reborrowDeadTargetBody 5 s0_noArgs
      [(), (), (), ()] .failed :=
    ReachesPrefix.step 4 s0_noArgs s₁ () [(), (), ()] .failed rfl
      (ReachesPrefix.step 3 s₁ s₂ () [(), ()] .failed rfl
        (ReachesPrefix.step 2 s₂ s₃ () [()] .failed rfl
          (ReachesPrefix.step 1 s₃ s₄ () [] .failed rfl
            (ReachesPrefix.failed 0 s₄ rfl))))
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M13: `evalMirStmt` `.storageDead` deinitializes local (use-after-StorageDead fails)
def useAfterStorageDeadBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal (.usize 0))),
        .assign ⟨2⟩ (.use (.constVal (.usize 1))),
        .storageDead ⟨2⟩,
        .assign ⟨3⟩ (.use (.copy ⟨2⟩))
      ]
      terminator := .return_ }
  ]

theorem canary_M13_use_after_storageDead_violates_wellFormed :
    ¬ (MirSem useAfterStorageDeadBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState useAfterStorageDeadBody s0_noArgs :=
    initMirState_oneBlock_noArgs useAfterStorageDeadBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.usize 0))
    stmtIdx := 1
  }
  let s₂ : MirState := { s₁ with
    locals := updateLocal s₁.locals 2 (some (.usize 1))
    stmtIdx := 2
  }
  let s₃ : MirState := { s₂ with
    locals := updateLocal s₂.locals 2 none
    stmtIdx := 3
  }
  have hreach : ReachesPrefix MirStep useAfterStorageDeadBody 4 s0_noArgs
      [(), (), ()] .failed :=
    ReachesPrefix.step 3 s0_noArgs s₁ () [(), ()] .failed rfl
      (ReachesPrefix.step 2 s₁ s₂ () [()] .failed rfl
        (ReachesPrefix.step 1 s₂ s₃ () [] .failed rfl
          (ReachesPrefix.failed 0 s₃ rfl)))
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M14 (Baseline #1): `evalTransmuteCopy` outer `srcSz = dstSz` mismatch fails
def transmuteOuterMismatchBody : MirBody where
  argTys := []
  retTy := .bool
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨2⟩ (.use (.constVal (.bytes 8 0))),
        .assign ⟨3⟩ (.ref ⟨2⟩)
      ]
      terminator := .callTransmuteCopy ⟨0⟩ .usize .bool (.copy ⟨3⟩) ⟨0⟩ }
  ]

theorem canary_M14_transmute_size_mismatch_violates_wellFormed :
    ¬ (MirSem transmuteOuterMismatchBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState transmuteOuterMismatchBody s0_noArgs :=
    initMirState_oneBlock_noArgs transmuteOuterMismatchBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 2 (some (.bytes 8 0))
    stmtIdx := 1
  }
  let s₂ : MirState := { s₁ with
    locals := updateLocal s₁.locals 3 (some (.ref ⟨2⟩))
    stmtIdx := 2
  }
  have hreach : ReachesPrefix MirStep transmuteOuterMismatchBody 3 s0_noArgs
      [(), ()] .failed :=
    ReachesPrefix.step 2 s0_noArgs s₁ () [()] .failed rfl
      (ReachesPrefix.step 1 s₁ s₂ () [] .failed rfl
        (ReachesPrefix.failed 0 s₂ rfl))
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M15: `evalTransmuteCopy` inner `vSz = srcSz` pointee byte-size mismatch fails
def transmuteInnerMismatchBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨2⟩ (.use (.constVal (.bytes 4 0))),
        .assign ⟨3⟩ (.ref ⟨2⟩)
      ]
      terminator := .callTransmuteCopy ⟨0⟩ .usize .usize (.copy ⟨3⟩) ⟨0⟩ }
  ]

theorem canary_M15_transmute_mismatched_pointee_bytes_violates_wellFormed :
    ¬ (MirSem transmuteInnerMismatchBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState transmuteInnerMismatchBody s0_noArgs :=
    initMirState_oneBlock_noArgs transmuteInnerMismatchBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 2 (some (.bytes 4 0))
    stmtIdx := 1
  }
  let s₂ : MirState := { s₁ with
    locals := updateLocal s₁.locals 3 (some (.ref ⟨2⟩))
    stmtIdx := 2
  }
  have hreach : ReachesPrefix MirStep transmuteInnerMismatchBody 3 s0_noArgs
      [(), ()] .failed :=
    ReachesPrefix.step 2 s0_noArgs s₁ () [()] .failed rfl
      (ReachesPrefix.step 1 s₁ s₂ () [] .failed rfl
        (ReachesPrefix.failed 0 s₂ rfl))
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M16 (Baseline #4): `evalMirTerminator` `.return_` with uninitialized `_0` fails
def uninitReturnBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [{ stmts := [], terminator := .return_ }]

theorem canary_M16_uninit_return_violates_wellFormed :
    ¬ (MirSem uninitReturnBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState uninitReturnBody s0_noArgs :=
    initMirState_oneBlock_noArgs uninitReturnBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs rfl)

-- M17: `evalMirTerminator` `.unreachable` fails
def unreachableBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [{ stmts := [], terminator := .unreachable }]

theorem canary_M17_unreachable_violates_wellFormed :
    ¬ (MirSem unreachableBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState unreachableBody s0_noArgs :=
    initMirState_oneBlock_noArgs unreachableBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs rfl)

-- M18: `evalMirTerminator` `.panic` terminates with `.unwind`, rejecting `ConstSucceeds`
def panicConstBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 1
  blocks := [{ stmts := [], terminator := .panic }]

theorem canary_M18_panicking_const_rejected_by_constSucceeds :
    ¬ ConstSucceeds (fun _ => 0) panicConstBody := by
  intro ⟨s₀, n, tr, v, _hty, hinit, hreach⟩
  rcases hinit with ⟨hb0, hst0, hcur, _hstack, _hl0, _hargs⟩
  have hstep : evalMirStep panicConstBody s₀ = .terminated .unwind := by
    unfold evalMirStep panicConstBody
    rw [hcur, hb0]
    dsimp
    rw [hst0]
    rfl
  generalize hout : PrefixOutcome.terminated (.normal v) = out at hreach
  cases hreach with
  | zero => cases hout
  | step _ _ _ _ _ _ h1 _ =>
    have h1' : _ = evalMirStep panicConstBody s₀ := h1
    rw [hstep] at h1'; cases h1'
  | choice _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalMirStep panicConstBody s₀ := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ h1 _ =>
    have h1' : _ = evalMirStep panicConstBody s₀ := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ t h1 =>
    have h1' : StepResult.terminated t = evalMirStep panicConstBody s₀ := h1
    rw [hstep] at h1'
    injection h1' with ht
    subst ht
    cases hout
  | failed _ _ h1 =>
    have h1' : _ = evalMirStep panicConstBody s₀ := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hno =>
    exact hno ⟨_, hstep.symm⟩

-- M19: `evalMirTerminator` `.switchInt` on non-boolean discriminant fails
def switchIntNonBoolBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [
    { stmts := []
      terminator := .switchInt (.constVal (.usize 0)) ⟨0⟩ ⟨0⟩ }
  ]

theorem canary_M19_switchInt_non_bool_violates_wellFormed :
    ¬ (MirSem switchIntNonBoolBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState switchIntNonBoolBody s0_noArgs :=
    initMirState_oneBlock_noArgs switchIntNonBoolBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs rfl)

-- M20: `evalMirStep` out-of-bounds basic block index fails
def oobGotoBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [{ stmts := [], terminator := .goto ⟨99⟩ }]

theorem canary_M20_oob_goto_violates_wellFormed :
    ¬ (MirSem oobGotoBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState oobGotoBody s0_noArgs :=
    initMirState_oneBlock_noArgs oobGotoBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with block := 99, stmtIdx := 0 }
  have hreach : ReachesPrefix MirStep oobGotoBody 2 s0_noArgs [()] .failed :=
    ReachesPrefix.step 1 s0_noArgs s₁ () [] .failed rfl
      (ReachesPrefix.failed 0 s₁ rfl)
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M21 (Baseline #2): `AdmissibleAdtInv` rejects `nonZeroAdtInv` on `pubSafe` field
def pubSafeAdt0 : AdtDecl where
  id := 0
  fields := [{ ty := .usize, access := .pubSafe }]
  nonExhaustive := false

def nonZeroAdtInv : AdtInv :=
  fun id v =>
    match id, v with
    | 0, .usize n => n ≠ 0
    | _, _ => True

theorem canary_M21_pub_safe_fields_reject_nonzero_inv :
    ¬ AdmissibleAdtInv [pubSafeAdt0] nonZeroAdtInv := by
  intro hadm
  exact hadm pubSafeAdt0 (.head []) rfl 0 rfl

-- M22 (Baseline #3): `EnsuresRetLibInv` rejects returning `NonZeroUsize(0)`
def buggyZeroBody : MirBody where
  argTys := []
  retTy := .adt 0
  localCount := 1
  blocks := [
    { stmts := [.assign ⟨0⟩ (.aggregate 0 (.constVal (.usize 0)))]
      terminator := .return_ }
  ]

theorem canary_M22_buggy_zero_adt_return_rejected :
    ¬ (MirSem buggyZeroBody ≤
      EnsuresRetLibInv nonZeroAdtInv (.adt 0) (fun _ => True)) := by
  have hinit : initMirState buggyZeroBody s0_noArgs :=
    initMirState_oneBlock_noArgs buggyZeroBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.adt 0 (.usize 0)))
    stmtIdx := 1
  }
  have hreach : ReachesPrefix MirStep buggyZeroBody 2 s0_noArgs [()]
      (.terminated (.normal (MirVal.adt 0 (.usize 0)))) :=
    ReachesPrefix.step 1 s0_noArgs s₁ () []
      (.terminated (.normal (MirVal.adt 0 (.usize 0)))) rfl
      (ReachesPrefix.terminated 0 s₁ (.normal (MirVal.adt 0 (.usize 0))) rfl)
  refine not_spec_of_reaches_normal hinit hreach ?_
  intro hpost
  have hinv := hpost (MirVal.adt 0 (.usize 0)) rfl
  exact hinv.2 rfl

-- M23: `defaultTrustPolicy` rejects `.userAxiom` in `CrateTheorem`
def trivialUnitBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 1
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.constVal .unit))]
      terminator := .return_ }
  ]

def unapprovedUserAxiomCrate : Crate where
  adts := []
  adtInv := defaultAdtInv
  unsafeImpls := []
  functions := [{ name := "unit_fn", prog := trivialUnitBody }]
  tcb := [.userAxiom "unsound_bypass" False]

theorem canary_M23_unapproved_userAxiom_rejected :
    ¬ CrateTheorem unapprovedUserAxiomCrate := by
  intro hcrate
  exact hcrate.2.2.2.1.1

-- M24a: `CrateTheorem` rejects violated `unsafeImpls` trait law
def unsoundUnsafeImplCrate : Crate where
  adts := [{ id := 0, fields := [{ ty := .usize, access := .priv }] }]
  adtInv := nonZeroAdtInv
  unsafeImpls := [
    { implName := "ZeroableForNonZeroUsize"
      whereBounds := True
      traitLaw := fun inv => inv 0 (.usize 0) }
  ]
  functions := [{ name := "unit_fn", prog := trivialUnitBody }]
  tcb := []

theorem canary_M24a_unsound_unsafeImpl_rejected :
    ¬ CrateTheorem unsoundUnsafeImplCrate := by
  intro hcrate
  exact hcrate.2.2.1.1 True.intro rfl

-- M24b (Baseline #5): `EnsuresEqArg 1` rejects `wrongIdBody` returning `0`
def wrongIdBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.constVal (.usize 0)))]
      terminator := .return_ }
  ]

theorem canary_M24b_wrong_id_violates_ensures :
    ¬ (MirSem wrongIdBody ≤ EnsuresEqArg 1) := by
  let s₀ : MirState := {
    locals := fun i => if i == 1 then some (.usize 1) else none
    block := 0
    stmtIdx := 0
  }
  have hinit : initMirState wrongIdBody s₀ := by
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨.usize 1, rfl, True.intro⟩, ?_⟩⟩, ?_⟩
    · intro j hj
      have hne : j ≠ 1 := by
        intro hEq
        subst hEq
        cases hj with
        | step hle => cases hle
      have hj1 : (j == 1) = false := StructuralExternalCall.nat_beq_false_of_ne hne
      dsimp [s₀]
      rw [hj1]
      rfl
    · exact monoAdmitted_of_no_call1 s₀.tySizes wrongIdBody rfl
        (by intro b hb; cases hb with
          | head => intro _ _ _ _ _ h; cases h
          | tail _ hnil => cases hnil)
  let s₁ : MirState := { s₀ with
    locals := updateLocal s₀.locals 0 (some (.usize 0))
    stmtIdx := 1
  }
  have hreach : ReachesPrefix MirStep wrongIdBody 2 s₀ [()]
      (.terminated (.normal (MirVal.usize 0))) :=
    ReachesPrefix.step 1 s₀ s₁ () []
      (.terminated (.normal (MirVal.usize 0))) rfl
      (ReachesPrefix.terminated 0 s₁ (.normal (MirVal.usize 0)) rfl)
  refine not_spec_of_reaches_normal hinit hreach ?_
  intro hpost
  have heq := hpost (MirVal.usize 0) rfl
  cases heq

#print axioms canary_M01_sizeOf_usize_wrong_rejected
#print axioms canary_M02_sizeOf_bool_wrong_rejected
#print axioms canary_M03_uninit_copy_violates_wellFormed
#print axioms canary_M04_double_move_violates_wellFormed
#print axioms canary_M05_uninit_move_violates_wellFormed
#print axioms canary_M06_eq_distinct_usize_not_true
#print axioms canary_M07_illTyped_binOp_violates_wellFormed
#print axioms canary_M08_failed_use_assign_violates_wellFormed
#print axioms canary_M09_uninit_aggregate_violates_wellFormed
#print axioms canary_M10_field0_non_adt_violates_wellFormed
#print axioms canary_M11_ref_uninit_violates_wellFormed
#print axioms canary_M12_reborrow_dead_target_violates_wellFormed
#print axioms canary_M13_use_after_storageDead_violates_wellFormed
#print axioms canary_M14_transmute_size_mismatch_violates_wellFormed
#print axioms canary_M15_transmute_mismatched_pointee_bytes_violates_wellFormed
#print axioms canary_M16_uninit_return_violates_wellFormed
#print axioms canary_M17_unreachable_violates_wellFormed
#print axioms canary_M18_panicking_const_rejected_by_constSucceeds
#print axioms canary_M19_switchInt_non_bool_violates_wellFormed
#print axioms canary_M20_oob_goto_violates_wellFormed
#print axioms canary_M21_pub_safe_fields_reject_nonzero_inv
#print axioms canary_M22_buggy_zero_adt_return_rejected
#print axioms canary_M23_unapproved_userAxiom_rejected
#print axioms canary_M24a_unsound_unsafeImpl_rejected
#print axioms canary_M24b_wrong_id_violates_ensures

end TrustedMutationCanaries

/-!
## Part III: Mandatory `BoundaryCanarySuite` for Trusted Machine Models
-/

namespace BoundaryCanary

structure Partial (α : Type) where
  defined : Prop
  outcomes : α → Prop

def Partial.ub {α : Type} : Partial α :=
  { defined := False, outcomes := fun _ => False }

/-- Arithmetic status flags in `RFLAGS`. -/
structure RFlags where
  cf : Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving DecidableEq, Repr

/-- Unified interface for an x86-64 operational semantics model to be tested
against the mandatory `BoundaryCanarySuite`. -/
structure X86MachineModel where
  /-- 64-bit `add` (`addq`) returning `(result_toNat, CF, ZF)`. -/
  evalAdd64 : Nat → Nat → Nat × Bool × Bool
  /-- 64-bit `sub` (`subq`) returning `(result_toNat, CF, SF)`. -/
  evalSub64 : Nat → Nat → Nat × Bool × Bool
  /-- 64-bit `shl` (`shlq`) returning `Partial (result_toNat × RFlags)`. -/
  evalShl64 : Nat → Nat → RFlags → Partial (Nat × RFlags)
  /-- 64-bit `shr` (`shrq`) returning `result_toNat`. -/
  evalShr64 : Nat → Nat → Nat
  /-- 64-bit signed division (`idivq`) returning `Partial (quot_toNat × rem_toNat)`. -/
  evalIdiv64 : BitVec 64 → BitVec 64 → Partial (BitVec 64 × BitVec 64)
  /-- Stack-frame slot write `writeSlot slotCount slotIdx val`. -/
  evalSlotWrite : Nat → Nat → Nat → Partial Nat
  /-- `call` instruction checking System V AMD64 16-byte `rsp` alignment. -/
  evalCallAlign : Nat → Partial Unit
  /-- `ret` instruction checking callee-saved register preservation (`rbp`, `rbx`, `r12`..`r15`). -/
  evalRetCalleeSaved : BitVec 64 → BitVec 64 → Partial Unit
  /-- `transmute_copy` (`rep movsb`) checking `srcByteSize == dstByteSize`. -/
  evalTransmuteCopy : Nat → Nat → Nat → Partial Nat
  /-- Typed scalar/ADT load checking `AdtInv` validity (e.g., `bool` byte `< 2`). -/
  evalLoadBool : Nat → Partial Bool
  /-- CTFE `MonoAdmitted` predicate paired with `ConstNoUnmodeled` non-vacuity guard. -/
  evalCtfeCheck : Bool → Bool → Bool × Bool

/-- **Mandatory `BoundaryCanarySuite` Typeclass**:
Every language model in `trusted/` must instantiate this suite, which pairs
positive conformance witnesses with **negative refutation theorems** that fail
to typecheck if any safety or validity guard in the semantics is weakened. -/
class BoundaryCanarySuite (M : X86MachineModel) : Prop where
  /-- Guard 1A (Positive): `(2^64 - 1) + 1` wraps modulo `2^64` to `0` with `CF = true, ZF = true`. -/
  canary_pos_add64_wrap :
    M.evalAdd64 (2 ^ 64 - 1) 1 = (0, true, true)
  /-- Guard 1B (Negative Refutation): `(2^64 - 1) + 1` must NOT equal unbounded `2^64`. -/
  canary_neg_add64_no_unbounded_nat :
    (M.evalAdd64 (2 ^ 64 - 1) 1).1 ≠ 2 ^ 64
  /-- Guard 2A (Positive): `0 - 1` wraps modulo `2^64` to `2^64 - 1` with `CF = true, SF = true`. -/
  canary_pos_sub64_wrap :
    M.evalSub64 0 1 = (2 ^ 64 - 1, true, true)
  /-- Guard 2B (Negative Refutation): `0 - 1` must NOT truncate to `0` (`Nat` subtraction bug). -/
  canary_neg_sub64_no_zero_truncation :
    (M.evalSub64 0 1).1 ≠ 0
  /-- Guard 3A (Positive): `shlq(1, 64)` masks shift count by `63` (`64 & 63 = 0`)
  and preserves incoming `RFlags`. -/
  canary_pos_shl64_mask_and_flags :
    ∀ f : RFlags,
      (M.evalShl64 1 64 f).defined ∧ (M.evalShl64 1 64 f).outcomes (1, f)
  /-- Guard 3B (Negative Refutation): `shlq(1, 64)` must NOT produce `2^64` and
  `shrq(1, 64)` must NOT produce `0`. -/
  canary_neg_shift64_no_unmasked_count :
    ∀ f : RFlags,
      ¬ (M.evalShl64 1 64 f).outcomes (2 ^ 64, f) ∧ M.evalShr64 1 64 ≠ 0
  /-- Guard 4A (Positive): `idivq(42, 7)` is defined and yields `(6, 0)`. -/
  canary_pos_idiv64_normal :
    (M.evalIdiv64 42#64 7#64).defined ∧
    (M.evalIdiv64 42#64 7#64).outcomes (6#64, 0#64)
  /-- Guard 4B (Negative Refutation — Divide-by-Zero `#DE` Trap):
  `idivq(42, 0)` must be undefined (`¬ defined`). -/
  canary_neg_idiv64_div_zero_traps :
    ¬ (M.evalIdiv64 42#64 0#64).defined
  /-- Guard 5 (Negative Refutation — Signed Overflow `INT64_MIN / -1` `#DE` Trap):
  `idivq(INT64_MIN, -1)` must be undefined (`¬ defined`). -/
  canary_neg_idiv64_intmin_overflow_traps :
    ¬ (M.evalIdiv64 0x8000000000000000#64 0xffffffffffffffff#64).defined
  /-- Guard 6A (Positive): In-bounds stack slot write (`slotIdx < slotCount`) succeeds. -/
  canary_pos_slot_write_in_bounds :
    (M.evalSlotWrite 4 2 99).defined ∧ (M.evalSlotWrite 4 2 99).outcomes 99
  /-- Guard 6B (Negative Refutation — Out-of-Frame Stack Slot Clobber Trap):
  Writing to `slotIdx ≥ slotCount` must be undefined (`¬ defined`). -/
  canary_neg_slot_write_out_of_bounds_traps :
    ¬ (M.evalSlotWrite 4 4 99).defined
  /-- Guard 7A (Positive): `call` with 16-byte aligned `rsp` (`rsp % 16 == 0`) succeeds. -/
  canary_pos_call_rsp_aligned :
    (M.evalCallAlign 0x7fffffffe000).defined
  /-- Guard 7B (Negative Refutation — Misaligned `rsp` at `call` Trap):
  `call` with `rsp % 16 == 8` must be undefined (`¬ defined`). -/
  canary_neg_call_rsp_misaligned_traps :
    ¬ (M.evalCallAlign 0x7fffffffe008).defined
  /-- Guard 8A (Positive): `ret` with preserved callee-saved register state succeeds. -/
  canary_pos_ret_callee_saved_preserved :
    (M.evalRetCalleeSaved 0x1234#64 0x1234#64).defined
  /-- Guard 8B (Negative Refutation — Clobbered Callee-Saved Register Trap):
  `ret` when exit callee-saved register differs from entry must be undefined (`¬ defined`). -/
  canary_neg_ret_callee_saved_clobbered_traps :
    ¬ (M.evalRetCalleeSaved 0x1234#64 0xdead#64).defined
  /-- Guard 9A (Positive): `transmute_copy` with matching `srcSize == dstSize` succeeds. -/
  canary_pos_transmute_copy_same_size :
    (M.evalTransmuteCopy 8 8 0xabcd).defined ∧
    (M.evalTransmuteCopy 8 8 0xabcd).outcomes 0xabcd
  /-- Guard 9B (Negative Refutation — Size-Mismatched `transmute_copy` Trap):
  `transmute_copy` with `srcSize ≠ dstSize` must be undefined (`¬ defined`). -/
  canary_neg_transmute_copy_size_mismatch_traps :
    ¬ (M.evalTransmuteCopy 8 16 0xabcd).defined
  /-- Guard 10A (Positive): Loading a valid `bool` byte (`0` or `1`) succeeds. -/
  canary_pos_load_bool_valid :
    (M.evalLoadBool 1).defined ∧ (M.evalLoadBool 1).outcomes true
  /-- Guard 10B (Negative Refutation — Invalid `AdtInv` Discriminant Trap):
  Loading an invalid `bool` byte (`2`) must be undefined (`¬ defined`). -/
  canary_neg_load_bool_invalid_discriminant_traps :
    ¬ (M.evalLoadBool 2).defined
  /-- Guard 11 (Positive & Negative — Quadrant-4 CTFE Non-Vacuity & Panic Filtering):
  `evalCtfeCheck isModeled constPassed` returns `(constNoUnmodeled, monoAdmitted)`:
  - When `isModeled = true` and `constPassed = true`, `monoAdmitted = true`.
  - When `isModeled = true` and `constPassed = false`, `monoAdmitted = false`.
  - When `isModeled = false` (unmodeled CTFE instruction), `constNoUnmodeled = false`
    (blocking Quadrant-4 vacuous verification!). -/
  canary_ctfe_polarity_guards :
    M.evalCtfeCheck true true = (true, true) ∧
    M.evalCtfeCheck true false = (true, false) ∧
    (M.evalCtfeCheck false true).1 = false

/-! ## Section 5: Current `X86Semantics.lean` (`4f45f0a391a9`) Provably Fails `BoundaryCanarySuite` -/

/-- Model capturing the exact `Nat` ALU and unchecked `writeSlot` behavior of
`mir-to-x86/trusted/lean/Trusted/X86Semantics.lean` at commit
`4f45f0a391a921ced9c9dc773b9a040dbc215d14`. -/
def currentX86Model : X86MachineModel where
  evalAdd64 := fun a b => (a + b, false, (a + b) == 0)
  evalSub64 := fun a b => (a - b, false, false)
  evalShl64 := fun a b f =>
    { defined := True, outcomes := fun out => out = (a <<< b, f) }
  evalShr64 := fun a b => a >>> b
  evalIdiv64 := fun a b =>
    if b == 0#64 then Partial.ub
    else { defined := True, outcomes := fun out => out = (a.sdiv b, a.srem b) }
  -- In `X86Semantics.lean:105-115`, `writeSlot` never checks `slotIdx < slotCount`!
  evalSlotWrite := fun _slotCount _slotIdx val =>
    { defined := True, outcomes := fun out => out = val }
  evalCallAlign := fun _rsp => { defined := True, outcomes := fun _ => True }
  evalRetCalleeSaved := fun _ _ => { defined := True, outcomes := fun _ => True }
  evalTransmuteCopy := fun srcSz dstSz val =>
    if srcSz == dstSz then { defined := True, outcomes := fun out => out = val }
    else Partial.ub
  evalLoadBool := fun b =>
    if b < 2 then { defined := True, outcomes := fun out => out = (b == 1) }
    else Partial.ub
  -- In `X86Semantics.lean:547-555`, `.failed .unmodeled` is not separated from
  -- `.terminated .unwind`, so `constNoUnmodeled` is missing (`true`).
  evalCtfeCheck := fun isModeled constPassed => (true, isModeled && constPassed)

/-- **Theorem 2A (`currentX86Model_fails_BoundaryCanarySuite`)**:
`currentX86Model` (matching `Trusted/X86Semantics.lean` at `4f45f0a391a9`)
provably violates `BoundaryCanarySuite` (in fact, it fails Guards 1B, 2B, 3B,
5, 6B, 7B, 8B, and 11 simultaneously). -/
theorem currentX86Model_fails_BoundaryCanarySuite :
    ¬ BoundaryCanarySuite currentX86Model := by
  intro h_suite
  have h_no_trunc := h_suite.canary_neg_sub64_no_zero_truncation
  exact h_no_trunc rfl

/-! ## Section 6: Corrected `fixedX86Model` Instantiates `BoundaryCanarySuite` -/

/-- Corrected 64-bit `BitVec 64` + bounds-checked x86-64 semantics model.
Each safety/validity guard is annotated with a `-- MUTATE_GUARD:` marker for
automated guard-mutation testing by `run_guard_mutation_probe.py`. -/
def fixedX86Model : X86MachineModel where
  evalAdd64 := fun a b =>
    let va := BitVec.ofNat 64 a
    let vb := BitVec.ofNat 64 b
    let res := (va + vb).toNat -- MUTATE_GUARD: alu_mod64_add
    let cf := a + b >= 2 ^ 64
    (res, cf, res == 0)
  evalSub64 := fun a b =>
    let va := BitVec.ofNat 64 a
    let vb := BitVec.ofNat 64 b
    let res := (va - vb).toNat -- MUTATE_GUARD: alu_mod64_sub
    let cf := a < b
    (res, cf, res >= 2 ^ 63)
  evalShl64 := fun a b f =>
    let va := BitVec.ofNat 64 a
    let c := b % 64 -- MUTATE_GUARD: shift_mask64_check
    if c == 0 then
      { defined := True, outcomes := fun out => out = (va.toNat, f) }
    else
      let res := (va <<< (BitVec.ofNat 64 c)).toNat
      let cf := va.getLsbD (64 - c)
      let zf := res == 0
      let sf := res >= 2 ^ 63
      { defined := True,
        outcomes := fun out =>
          ∃ of_nd : Bool, out = (res, { cf, zf, sf, of := of_nd }) }
  evalShr64 := fun a b =>
    let c := b % 64 -- MUTATE_GUARD: shift_mask64_shr_check
    ((BitVec.ofNat 64 a) >>> (BitVec.ofNat 64 c)).toNat
  evalIdiv64 := fun dividend divisor =>
    let divZero := divisor == 0#64 -- MUTATE_GUARD: div_zero_check
    let sOverflow := dividend == 0x8000000000000000#64 && divisor == 0xffffffffffffffff#64 -- MUTATE_GUARD: idiv_overflow_check
    if divZero || sOverflow then
      Partial.ub
    else
      { defined := True,
        outcomes := fun out => out = (dividend.sdiv divisor, dividend.srem divisor) }
  evalSlotWrite := fun slotCount slotIdx val =>
    let inBounds := slotIdx < slotCount -- MUTATE_GUARD: slot_bounds_check
    if inBounds then
      { defined := True, outcomes := fun out => out = val }
    else
      Partial.ub
  evalCallAlign := fun rsp =>
    let aligned := rsp % 16 == 0 -- MUTATE_GUARD: rsp_align16_check
    if aligned then
      { defined := True, outcomes := fun _ => True }
    else
      Partial.ub
  evalRetCalleeSaved := fun savedEntry savedExit =>
    let preserved := savedEntry == savedExit -- MUTATE_GUARD: callee_saved_check
    if preserved then
      { defined := True, outcomes := fun _ => True }
    else
      Partial.ub
  evalTransmuteCopy := fun srcSz dstSz val =>
    let sizeMatch := srcSz == dstSz -- MUTATE_GUARD: transmute_size_check
    if sizeMatch then
      { defined := True, outcomes := fun out => out = val }
    else
      Partial.ub
  evalLoadBool := fun byteVal =>
    let validBool := byteVal < 2 -- MUTATE_GUARD: adt_inv_check
    if validBool then
      { defined := True, outcomes := fun out => out = (byteVal == 1) }
    else
      Partial.ub
  evalCtfeCheck := fun isModeled constPassed =>
    let noUnmodeled := isModeled -- MUTATE_GUARD: ctfe_no_unmodeled_check
    let monoAdmitted := isModeled && constPassed -- MUTATE_GUARD: ctfe_mono_admitted_check
    (noUnmodeled, monoAdmitted)

/-- **Theorem 2B (`instBoundaryCanarySuiteFixedX86Model`)**:
`fixedX86Model` satisfies all positive and negative canaries in
`BoundaryCanarySuite`. -/
instance instBoundaryCanarySuiteFixedX86Model :
    BoundaryCanarySuite fixedX86Model where
  canary_pos_add64_wrap := by decide
  canary_neg_add64_no_unbounded_nat := by decide
  canary_pos_sub64_wrap := by decide
  canary_neg_sub64_no_zero_truncation := by decide
  canary_pos_shl64_mask_and_flags := fun f => ⟨trivial, rfl⟩
  canary_neg_shift64_no_unmasked_count := by
    intro f
    refine ⟨?_, by decide⟩
    intro h_out
    injection h_out with h_eq _
    revert h_eq
    decide
  canary_pos_idiv64_normal := ⟨trivial, rfl⟩
  canary_neg_idiv64_div_zero_traps := fun h => h
  canary_neg_idiv64_intmin_overflow_traps := fun h => h
  canary_pos_slot_write_in_bounds := ⟨trivial, rfl⟩
  canary_neg_slot_write_out_of_bounds_traps := fun h => h
  canary_pos_call_rsp_aligned := trivial
  canary_neg_call_rsp_misaligned_traps := fun h => h
  canary_pos_ret_callee_saved_preserved := trivial
  canary_neg_ret_callee_saved_clobbered_traps := fun h => h
  canary_pos_transmute_copy_same_size := ⟨trivial, rfl⟩
  canary_neg_transmute_copy_size_mismatch_traps := fun h => h
  canary_pos_load_bool_valid := ⟨trivial, rfl⟩
  canary_neg_load_bool_invalid_discriminant_traps := fun h => h
  canary_ctfe_polarity_guards := by decide


#print axioms currentX86Model_fails_BoundaryCanarySuite
#print axioms instBoundaryCanarySuiteFixedX86Model

end BoundaryCanary


/-!
## Part IV: Open-World Callback Framing, `BoundedIdx` Exploit, and Straight-Line Composition
-/

namespace OpenWorldCallbackFraming

/-!
## 1. Core Refinement Preorder and Small-Step Prefix Semantics (`Trusted`)
-/

/-- A reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Implication (`P → Q`) equips `Prop` with a refinement preorder. -/
instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

/-- Pointwise lifting (`∀ a, f a ≤ g a`) equips function spaces with a
    refinement preorder. -/
instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Constructively lifted partial domain $B \cup \{\mathsf{UB}\}$. -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

/-- Embed an unconditionally defined value `b : B` into `Partial B`. -/
def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

/-- Top element ($\mathsf{UB}$) of `Partial B` (`defined := False`). -/
def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

/-- Map `f` over the defined payload of `Partial B₁`. -/
def Partial.map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) :
    Partial B₂ where
  defined := p.defined
  val h := f (p.val h)

/-- Refinement preorder on `Partial B`. -/
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Order-preserving mapping between behavior preorders. -/
def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

theorem monotone_id {B : Type u} [Preorder B] : Monotone (fun b : B => b) :=
  fun _ _ h => h

/-- Query-indexed partial behaviors over `Query` and `Out`. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- Language carrier bundling programs, queries, outcomes, and semantics. -/
structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

abbrev Language.Behavior (L : Language) : Type :=
  OpenWorldCallbackFraming.Behavior L.Query L.Out

def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

/-- Compilation (refinement) relation `L_tgt.sem t ≤ π_c (L_src.sem s)`. -/
abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

/-- Reflexivity of `Compiles` under the identity behavior map. -/
theorem Compiles.refl (L : Language) (s : L.Prog) :
    Compiles L L id s s :=
  Preorder.le_refl (L.sem s)

/-- Transitive composition of two compilation passes. -/
theorem Compiles.comp
    {L₁ L₂ L₃ : Language}
    {π₁ : L₁.Behavior → L₂.Behavior} {π₂ : L₂.Behavior → L₃.Behavior}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : Compiles L₁ L₂ π₁ p₁ p₂)
    (h₂₃ : Compiles L₂ L₃ π₂ p₂ p₃)
    (h_mono₂ : Monotone π₂) :
    Compiles L₁ L₃ (fun b => π₂ (π₁ b)) p₁ p₃ :=
  Preorder.le_trans h₂₃ (h_mono₂ h₁₂)

/-- Quantifier polarity for nondeterministic choices. -/
inductive ChoiceKind where
  | demonic
  | angelic

/-- Normal return vs. panic/unwind termination. -/
inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

/-- Undefined Behavior vs. contract violation failure. -/
inductive FailureKind where
  | ub
  | contractViolation

/-- Single-step transition outcome. -/
inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (kind : ChoiceKind) (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)

/-- Prefix execution outcome at a finite step budget. -/
inductive PrefixOutcome (Val : Type) where
  | running
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)
  | stuck

def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed _ => False
  | .stuck => False

structure ExecQuery (State : Type) where
  init : State
  steps : Nat

structure ExecOut (Obs Val : Type) where
  trace : List Obs
  outcome : PrefixOutcome Val

structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

inductive ReachesPrefix (M : SmallStepMachine Prog State Obs Val) (p : Prog)
    (init : State) : Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefix M p init 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome Val) :
      M.step p s (.step obs s') →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s (obs :: tr) out
  | choice (n : Nat) (kind : ChoiceKind) (s s' : State)
      (branches : State → Prop) (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.choice kind branches) →
      branches s' →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s tr out
  | emptyChoice (n : Nat) (kind : ChoiceKind) (s : State)
      (branches : State → Prop) :
      M.step p s (.choice kind branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix M p init (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      M.step p s (.terminated term) →
      ReachesPrefix M p init (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) (err : FailureKind) :
      M.step p s (.failed err) →
      ReachesPrefix M p init (n + 1) s [] (.failed err)
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step p s r) →
      ReachesPrefix M p init (n + 1) s [] .stuck

def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M p q.init q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome
  }

def SmallStepMachine.toLanguage (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog := Prog
  Query := ExecQuery State
  Out := ExecOut Obs Val
  sem := BehaviorOf M

def TotalStep (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State), ∃ r, M.step p s r

def InhabitedDemonic (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State) (kind : ChoiceKind) (branches : State → Prop),
    M.step p s (.choice kind branches) → ∃ s', branches s'

theorem behaviorOf_le_specOn
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {pre : ExecQuery State → Prop}
    {Post : ExecQuery State → ExecOut Obs Val → Prop}
    (h : ∀ (q : ExecQuery State) (out : ExecOut Obs Val),
      pre q →
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome →
      out.outcome.isSafe ∧ Post q out) :
    BehaviorOf M p ≤ (M.toLanguage).SpecOn pre Post := by
  intro q hpre
  refine ⟨fun hinit tr oc hreach => (h q ⟨tr, oc⟩ hpre ⟨hinit, hreach⟩).1, ?_⟩
  intro out hval
  exact (h q out hpre hval).2

/-!
## 2. x86-64 Machine Model, `NaiveCodegen`, and `Peephole` (`mir-to-x86@4f45f0a391`)
-/

structure SlotId where
  index : Nat
  deriving DecidableEq

structure BlockLabel where
  index : Nat
  deriving DecidableEq

inductive FieldAccess where
  | pubSafe
  | priv
  | unsafeField
  deriving DecidableEq

inductive X86Ty where
  | usize
  | bool
  | unit
  | adt (id : Nat)
  | param (idx : Nat)
  | refParam (idx : Nat)
  deriving DecidableEq

structure FieldDecl where
  ty : X86Ty
  access : FieldAccess

structure AdtDecl where
  id : Nat
  fields : List FieldDecl
  nonExhaustive : Bool := false

def AdtDecl.allFieldsPubSafe (decl : AdtDecl) : Bool :=
  !decl.nonExhaustive &&
  decl.fields.all (fun f =>
    match f.access with
    | .pubSafe => true
    | .priv | .unsafeField => false)

inductive X86Val where
  | word64 (bits : Nat)
  | boolVal (b : Bool)
  | unit
  | adt (id : Nat) (inner : X86Val)
  | bytes (sz : Nat) (bits : Nat)
  | stackPtr (slot : SlotId)
  deriving DecidableEq

inductive X86Operand where
  | stackSlot (slot : SlotId) (consume : Bool := false)
  | imm (val : X86Val)
  deriving DecidableEq

inductive X86BinOp where
  | add | sub | mul | bitAnd | bitOr | bitXor | shl | shr
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq

inductive X86Instr where
  | mov (dst : SlotId) (src : X86Operand)
  | alu (op : X86BinOp) (dst : SlotId) (lhs : X86Operand) (rhs : X86Operand)
  | wrapAdt (adtId : Nat) (dst : SlotId) (src : X86Operand)
  | extractField0 (dst : SlotId) (src : SlotId)
  | leaSlot (dst : SlotId) (target : SlotId)
  | reborrowSlot (dst : SlotId) (srcPtr : SlotId)
  | allocSlot (slot : SlotId)
  | deallocSlot (slot : SlotId)
  | nop
  deriving DecidableEq

mutual
  inductive X86Term where
    | ret
    | jmp (target : BlockLabel)
    | jccBool (cond : X86Operand) (falseTarget : BlockLabel)
        (trueTarget : BlockLabel)
    | ud2
    | abortPanic
    | movSizeOfJmp (dst : SlotId) (ty : X86Ty) (target : BlockLabel)
    | repMovsbJmp (dst : SlotId) (srcTy dstTy : X86Ty) (ptrOp : X86Operand)
        (target : BlockLabel)
    | call1 (dst : SlotId) (callee : X86Body) (arg : X86Operand)
        (target : BlockLabel)

  structure X86Block where
    instrs : List X86Instr
    term : X86Term

  structure X86Body where
    argTys : List X86Ty
    retTy : X86Ty
    slotCount : Nat
    blocks : List X86Block
    requiredConsts : List X86Body := []
end

structure X86CallFrame where
  callerBody : Option X86Body
  callerMem : Nat → Option X86Val
  retSlot : SlotId
  retBlock : Nat

structure X86State where
  mem : Nat → Option X86Val
  bb : Nat
  ip : Nat
  tySizes : Nat → Nat := fun _ => 0
  curBody : Option X86Body := none
  stack : List X86CallFrame := []

def updateSlot (mem : Nat → Option X86Val) (target : Nat)
    (val : Option X86Val) : Nat → Option X86Val :=
  fun i => if i == target then val else mem i

def evalX86TyByteSize (tySizes : Nat → Nat) (ty : X86Ty) : Nat :=
  match ty with
  | .usize => 8
  | .bool => 1
  | .unit => 0
  | .adt _ => 8
  | .param idx => tySizes idx
  | .refParam _ => 8

def X86Val.hasTy (tySizes : Nat → Nat) (v : X86Val) (ty : X86Ty) : Prop :=
  match ty, v with
  | .usize, .word64 _ => True
  | .bool, .boolVal _ => True
  | .unit, .unit => True
  | .adt tyId, .adt vId (.word64 _) => vId = tyId
  | .param idx, .bytes sz _ => sz = tySizes idx
  | .refParam _, .stackPtr _ => True
  | _, _ => False

def argsMatchStack (tySizes : Nat → Nat) (argTys : List X86Ty)
    (mem : Nat → Option X86Val) : Prop :=
  argTys.foldr
    (fun ty rest k =>
      (∃ v, mem k = some v ∧ v.hasTy tySizes ty) ∧ rest (k + 1))
    (fun k => ∀ j, k ≤ j → mem j = none)
    1

def initX86State (body : X86Body) (s : X86State) : Prop :=
  s.bb = 0 ∧
  s.ip = 0 ∧
  s.curBody = none ∧
  s.stack = [] ∧
  s.mem 0 = none ∧
  argsMatchStack s.tySizes body.argTys s.mem

def evalX86Operand (mem : Nat → Option X86Val) (op : X86Operand) :
    Option (X86Val × (Nat → Option X86Val)) :=
  match op with
  | .stackSlot slot false =>
    match mem slot.index with
    | some v => some (v, mem)
    | none => none
  | .stackSlot slot true =>
    match mem slot.index with
    | some v => some (v, updateSlot mem slot.index none)
    | none => none
  | .imm v => some (v, mem)

def evalX86BinOp (op : X86BinOp) (lhs rhs : X86Val) : Option X86Val :=
  match op, lhs, rhs with
  | .add, .word64 a, .word64 b => some (.word64 (a + b))
  | .sub, .word64 a, .word64 b => some (.word64 (a - b))
  | .mul, .word64 a, .word64 b => some (.word64 (a * b))
  | .eq, .word64 a, .word64 b => some (.boolVal (decide (a = b)))
  | .ne, .word64 a, .word64 b => some (.boolVal (decide (a ≠ b)))
  | .lt, .word64 a, .word64 b => some (.boolVal (decide (a < b)))
  | .le, .word64 a, .word64 b => some (.boolVal (decide (a ≤ b)))
  | .gt, .word64 a, .word64 b => some (.boolVal (decide (b < a)))
  | .ge, .word64 a, .word64 b => some (.boolVal (decide (b ≤ a)))
  | .eq, .boolVal a, .boolVal b => some (.boolVal (decide (a = b)))
  | .ne, .boolVal a, .boolVal b => some (.boolVal (decide (a ≠ b)))
  | .eq, .unit, .unit => some (.boolVal true)
  | .ne, .unit, .unit => some (.boolVal false)
  | _, _, _ => none

def evalX86Instr (s : X86State) (instr : X86Instr) :
    StepResult X86State Unit X86Val :=
  match instr with
  | .mov dst src =>
    match evalX86Operand s.mem src with
    | some (v, mem') =>
      .step () { s with
        mem := updateSlot mem' dst.index (some v)
        ip := s.ip + 1
      }
    | none => .failed .ub
  | .alu op dst lhs rhs =>
    match evalX86Operand s.mem lhs with
    | some (v1, mem1) =>
      match evalX86Operand mem1 rhs with
      | some (v2, mem2) =>
        match evalX86BinOp op v1 v2 with
        | some outVal =>
          .step () { s with
            mem := updateSlot mem2 dst.index (some outVal)
            ip := s.ip + 1
          }
        | none => .failed .ub
      | none => .failed .ub
    | none => .failed .ub
  | .wrapAdt adtId dst src =>
    match evalX86Operand s.mem src with
    | some (v, mem') =>
      .step () { s with
        mem := updateSlot mem' dst.index (some (.adt adtId v))
        ip := s.ip + 1
      }
    | none => .failed .ub
  | .extractField0 dst src =>
    match s.mem src.index with
    | some (.adt _ inner) =>
      .step () { s with
        mem := updateSlot s.mem dst.index (some inner)
        ip := s.ip + 1
      }
    | _ => .failed .ub
  | .leaSlot dst target =>
    match s.mem target.index with
    | some _ =>
      .step () { s with
        mem := updateSlot s.mem dst.index (some (.stackPtr target))
        ip := s.ip + 1
      }
    | none => .failed .ub
  | .reborrowSlot dst srcPtr =>
    match s.mem srcPtr.index with
    | some (.stackPtr target) =>
      match s.mem target.index with
      | some _ =>
        .step () { s with
          mem := updateSlot s.mem dst.index (some (.stackPtr target))
          ip := s.ip + 1
        }
      | none => .failed .ub
    | _ => .failed .ub
  | .allocSlot slot =>
    .step () { s with
      mem := updateSlot s.mem slot.index none
      ip := s.ip + 1
    }
  | .deallocSlot slot =>
    .step () { s with
      mem := updateSlot s.mem slot.index none
      ip := s.ip + 1
    }
  | .nop =>
    .step () { s with ip := s.ip + 1 }

def evalRepMovsb (tySizes : Nat → Nat) (mem : Nat → Option X86Val)
    (srcTy dstTy : X86Ty) (ptrVal : X86Val) : Option X86Val :=
  let srcSz := evalX86TyByteSize tySizes srcTy
  let dstSz := evalX86TyByteSize tySizes dstTy
  if decide (srcSz = dstSz) then
    match ptrVal with
    | .stackPtr target =>
      match mem target.index with
      | some (.bytes vSz bits) =>
        if decide (vSz = srcSz) then
          some (.bytes dstSz bits)
        else
          none
      | _ => none
    | _ => none
  else
    none

def evalX86Term (s : X86State) (term : X86Term) :
    StepResult X86State Unit X86Val :=
  match term with
  | .ret =>
    match s.mem 0 with
    | none => .failed .ub
    | some retVal =>
      match s.stack with
      | [] => .terminated (.normal retVal)
      | frame :: restStack =>
        .step () {
          mem := updateSlot frame.callerMem frame.retSlot.index (some retVal)
          bb := frame.retBlock
          ip := 0
          tySizes := s.tySizes
          curBody := frame.callerBody
          stack := restStack
        }
  | .jmp target =>
    .step () { s with bb := target.index, ip := 0 }
  | .ud2 =>
    .failed .ub
  | .abortPanic =>
    .terminated .unwind
  | .jccBool cond falseTarget trueTarget =>
    match evalX86Operand s.mem cond with
    | some (v, mem') =>
      match v with
      | .boolVal false =>
        .step () { s with mem := mem', bb := falseTarget.index, ip := 0 }
      | .boolVal true =>
        .step () { s with mem := mem', bb := trueTarget.index, ip := 0 }
      | _ => .failed .ub
    | none => .failed .ub
  | .movSizeOfJmp dst ty target =>
    let sz := evalX86TyByteSize s.tySizes ty
    .step () { s with
      mem := updateSlot s.mem dst.index (some (.word64 sz))
      bb := target.index
      ip := 0
    }
  | .repMovsbJmp dst srcTy dstTy ptrOp target =>
    match evalX86Operand s.mem ptrOp with
    | some (ptrVal, mem') =>
      match evalRepMovsb s.tySizes mem' srcTy dstTy ptrVal with
      | some outVal =>
        .step () { s with
          mem := updateSlot mem' dst.index (some outVal)
          bb := target.index
          ip := 0
        }
      | none => .failed .ub
    | none => .failed .ub
  | .call1 dst callee arg target =>
    match evalX86Operand s.mem arg with
    | some (argVal, callerMem') =>
      let calleeMem : Nat → Option X86Val :=
        updateSlot (fun _ => none) 1 (some argVal)
      let frame : X86CallFrame := {
        callerBody := s.curBody
        callerMem := callerMem'
        retSlot := dst
        retBlock := target.index
      }
      .step () {
        mem := calleeMem
        bb := 0
        ip := 0
        tySizes := s.tySizes
        curBody := some callee
        stack := frame :: s.stack
      }
    | none => .failed .ub

def evalX86Step (rootBody : X86Body) (s : X86State) :
    StepResult X86State Unit X86Val :=
  let active := s.curBody.getD rootBody
  match active.blocks[s.bb]? with
  | none => .failed .ub
  | some blk =>
    match blk.instrs[s.ip]? with
    | some instr => evalX86Instr s instr
    | none => evalX86Term s blk.term

def X86Machine : SmallStepMachine X86Body X86State Unit X86Val where
  initState := initX86State
  step body s r := r = evalX86Step body s

def X86Lang : Language :=
  X86Machine.toLanguage

abbrev X86Sem (body : X86Body) : X86Lang.Behavior :=
  X86Lang.sem body

abbrev LibInv := (Nat → Nat) → X86Ty → X86Val → Prop

def defaultLibInv : LibInv :=
  fun tySizes ty v => v.hasTy tySizes ty

def AdmissibleLibInv (adts : List AdtDecl) (libInv : LibInv) : Prop :=
  (∀ tySizes ty v, libInv tySizes ty v → v.hasTy tySizes ty) ∧
  (∀ tySizes n, libInv tySizes .usize (.word64 n)) ∧
  (∀ tySizes b, libInv tySizes .bool (.boolVal b)) ∧
  (∀ tySizes, libInv tySizes .unit .unit) ∧
  (∀ tySizes idx bits, libInv tySizes (.param idx) (.bytes (tySizes idx) bits)) ∧
  (∀ decl, decl ∈ adts → decl.allFieldsPubSafe = true →
    ∀ tySizes v, libInv tySizes .usize v →
      libInv tySizes (.adt decl.id) (.adt decl.id v))

def EnsuresRetLibInv (libInv : LibInv) (retTy : X86Ty)
    (pre : ExecQuery X86State → Prop) : X86Lang.Behavior :=
  X86Lang.SpecOn pre (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      libInv q.init.tySizes retTy ret)

/-!
## Part IV: Callback Re-Entrancy Exploit and Small-Step Open-World Frame Isolation

### 4.1 Architectural Registers, Stack Permissions (`BytePerm`), and `BoundedIdx`
-/

/-- The sixteen 64-bit general-purpose registers of x86-64 (`Trusted/X86Ast.lean`). -/
inductive Reg64 where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq

/-- System V AMD64 ABI callee-saved register classification (§3.2.1, Figure 3.4):
    `rbx`, `rsp`, `rbp`, and `r12`–`r15` belong to the calling function and must
    be preserved by any called procedure. -/
def Reg64.isCalleeSaved (r : Reg64) : Bool :=
  match r with
  | .rbx | .rsp | .rbp | .r12 | .r13 | .r14 | .r15 => true
  | _ => false

/-- Ghost stack-frame memory permissions (`Trusted/X86Ast.lean`). -/
inductive BytePerm where
  | unallocated
  | callerFrame
  | readOnly
  | readWrite
  deriving DecidableEq

/-- Capacity bound `cap = 4` for the private invariant-bearing ADT
    `pub struct BoundedIdx { val: usize }` (`AdtInv`: `val < 4`). -/
def boundedCap : Nat := 4

def boundedIdxAdtDecl : AdtDecl where
  id := 0
  fields := [{ ty := .usize, access := .priv }]

/-- Representation invariant `boundedIdxInv` for `BoundedIdx` (`adt 0`):
    requires `val < boundedCap` (`val < 4`). -/
def boundedIdxInv (tySizes : Nat → Nat) (ty : X86Ty) (v : X86Val) : Prop :=
  match ty, v with
  | .usize, .word64 _ => True
  | .bool, .boolVal _ => True
  | .unit, .unit => True
  | .param idx, .bytes sz _ => sz = tySizes idx
  | .refParam _, .stackPtr _ => True
  | .adt 0, .adt 0 (.word64 n) => n < boundedCap
  | .adt (k + 1), .adt vId (.word64 _) => vId = k + 1
  | _, _ => False

/-- `boundedIdxInv` is admissible because `BoundedIdx`'s field is private
    (`allFieldsPubSafe = false`). -/
theorem boundedIdxInv_admissible :
    AdmissibleLibInv [boundedIdxAdtDecl] boundedIdxInv := by
  refine ⟨?_, fun _ _ => True.intro, fun _ _ => True.intro, fun _ => True.intro,
          fun _ _ _ => rfl, ?_⟩
  · intro tySizes ty v hinv
    cases ty with
    | usize =>
      cases v <;> first | exact True.intro | cases hinv
    | bool =>
      cases v <;> first | exact True.intro | cases hinv
    | unit =>
      cases v <;> first | exact True.intro | cases hinv
    | adt tyId =>
      cases tyId with
      | succ k =>
        cases v with
        | adt vId inner =>
          cases inner <;> first | exact hinv | cases hinv
        | _ => cases hinv
      | zero =>
        cases v with
        | adt vId inner =>
          cases vId with
          | succ _ => cases hinv
          | zero =>
            cases inner <;> first | exact rfl | cases hinv
        | _ => cases hinv
    | param idx =>
      cases v <;> first | exact hinv | cases hinv
    | refParam idx =>
      cases v <;> first | exact True.intro | cases hinv
  · intro decl hmem hPub
    cases hmem with
    | head => cases hPub
    | tail _ hnil => cases hnil

/-!
### 4.2 Open-World x86-64 / MIR Machine with Indirect Callbacks and ISA Frame State
-/

/-- Terminators extended with `.callExternal` (`callIndirect` to an unknown safe
    external function or callback `fn(&BoundedIdx)`):
    - `exposedSlots`: stack/reference slots reachable by the external callee
      (such as `&BoundedIdx` or `&mut BoundedIdx` pointees).
    - `exposedMutSlots`: subset of `exposedSlots` passed by mutable reference
      (`&mut`).
    - `dst`: return value destination slot.
    - `retTy`: static ABI return type of the callback.
    - `target`: basic-block label where execution resumes after the callback. -/
inductive OpenTerm where
  | ret
  | jmp (target : BlockLabel)
  | jccBool (cond : X86Operand) (falseTarget : BlockLabel)
      (trueTarget : BlockLabel)
  | ud2
  | callExternal (exposedSlots : List Nat) (exposedMutSlots : List Nat)
      (dst : SlotId) (retTy : X86Ty) (target : BlockLabel)

structure OpenBlock where
  instrs : List X86Instr
  term : OpenTerm

structure OpenBody where
  argTys : List X86Ty
  retTy : X86Ty
  blocks : List OpenBlock

/-- Instantaneous machine state equipped with stack-slot permissions (`perms`),
    architectural registers (`regs`), entry register snapshot (`entryRegs`), and
    direction flag (`df`, required to be `false` (`DF = 0`) at ABI boundaries). -/
structure OpenState where
  mem : Nat → Option X86Val
  perms : Nat → BytePerm := fun i => if i ≤ 2 then .readWrite else .callerFrame
  regs : Reg64 → Nat := fun _ => 0
  entryRegs : Reg64 → Nat := fun _ => 0
  df : Bool := false
  bb : Nat := 0
  ip : Nat := 0
  tySizes : Nat → Nat := fun _ => 0

/-- Default permission layout for a 1-argument function with return slot `0`,
    argument/aliased `BoundedIdx` slot `1`, caller-private local slot `2`
    (`BytePerm.readWrite`), and caller-frame slots `j ≥ 3`
    (`BytePerm.callerFrame`). -/
def defaultOpenPerms (i : Nat) : BytePerm :=
  if i ≤ 2 then .readWrite else .callerFrame

/-- Valid entry state for an `OpenBody` under `boundedIdxInv`:
    - `bb = 0`, `ip = 0`, `df = false`, `regs = entryRegs`,
    - `perms = defaultOpenPerms`,
    - return slot `0` is `none`, and
    - argument slot `1` holds a valid `BoundedIdx` satisfying `boundedIdxInv`. -/
def initOpenState (body : OpenBody) (s : OpenState) : Prop :=
  s.bb = 0 ∧
  s.ip = 0 ∧
  s.df = false ∧
  s.regs = s.entryRegs ∧
  s.perms = defaultOpenPerms ∧
  s.mem 0 = none ∧
  ∃ v, s.mem 1 = some v ∧ boundedIdxInv s.tySizes (.adt 0) v ∧
  body.blocks ≠ []

def checkWritableSlot (s : OpenState) (slot : Nat) : Bool :=
  s.perms slot == .readWrite

/-- Evaluate a sequential `X86Instr` on `OpenState`, enforcing `BytePerm`:
    any write to a slot whose permission is not `.readWrite` (such as
    `BytePerm.callerFrame`, `BytePerm.readOnly`, or `BytePerm.unallocated`)
    triggers immediate Undefined Behavior (`.failed .ub`). -/
def evalOpenInstr (s : OpenState) (instr : X86Instr) :
    StepResult OpenState Unit X86Val :=
  match instr with
  | .mov dst src =>
    match checkWritableSlot s dst.index with
    | false => .failed .ub
    | true =>
      match evalX86Operand s.mem src with
      | some (v, mem') =>
        .step () { s with mem := updateSlot mem' dst.index (some v), ip := s.ip + 1 }
      | none => .failed .ub
  | .alu op dst lhs rhs =>
    match checkWritableSlot s dst.index with
    | false => .failed .ub
    | true =>
      match evalX86Operand s.mem lhs with
      | some (v1, mem1) =>
        match evalX86Operand mem1 rhs with
        | some (v2, mem2) =>
          match evalX86BinOp op v1 v2 with
          | some outVal =>
            .step () { s with mem := updateSlot mem2 dst.index (some outVal), ip := s.ip + 1 }
          | none => .failed .ub
        | none => .failed .ub
      | none => .failed .ub
  | .wrapAdt adtId dst src =>
    match checkWritableSlot s dst.index with
    | false => .failed .ub
    | true =>
      match evalX86Operand s.mem src with
      | some (v, mem') =>
        .step () { s with mem := updateSlot mem' dst.index (some (.adt adtId v)), ip := s.ip + 1 }
      | none => .failed .ub
  | .extractField0 dst src =>
    match checkWritableSlot s dst.index with
    | false => .failed .ub
    | true =>
      match s.mem src.index with
      | some (.adt _ inner) =>
        .step () { s with mem := updateSlot s.mem dst.index (some inner), ip := s.ip + 1 }
      | _ => .failed .ub
  | .leaSlot dst target =>
    match checkWritableSlot s dst.index with
    | false => .failed .ub
    | true =>
      match s.mem target.index with
      | some _ =>
        .step () { s with mem := updateSlot s.mem dst.index (some (.stackPtr target)), ip := s.ip + 1 }
      | none => .failed .ub
  | .reborrowSlot dst srcPtr =>
    match checkWritableSlot s dst.index with
    | false => .failed .ub
    | true =>
      match s.mem srcPtr.index with
      | some (.stackPtr target) =>
        match s.mem target.index with
        | some _ =>
          .step () { s with mem := updateSlot s.mem dst.index (some (.stackPtr target)), ip := s.ip + 1 }
        | none => .failed .ub
      | _ => .failed .ub
  | .allocSlot slot =>
    match checkWritableSlot s slot.index with
    | false => .failed .ub
    | true =>
      .step () { s with mem := updateSlot s.mem slot.index none, ip := s.ip + 1 }
  | .deallocSlot slot =>
    match checkWritableSlot s slot.index with
    | false => .failed .ub
    | true =>
      .step () { s with mem := updateSlot s.mem slot.index none, ip := s.ip + 1 }
  | .nop =>
    .step () { s with ip := s.ip + 1 }

/-!
### 4.3 Concrete `BoundedIdx` Library Bodies
-/

/-- `pub fn get_unchecked(idx: &BoundedIdx) -> usize`:
    Extracts `idx.val` from slot `1` into scratch slot `2`, checks `idx.val < 4`,
    and either branches to `bb 2` (returning `idx.val`) or to `bb 1` (`ud2`,
    modeling out-of-bounds slice indexing UB). -/
def getUncheckedOpenBody : OpenBody where
  argTys := [.adt 0]
  retTy := .usize
  blocks := [
    { instrs := [
        .extractField0 ⟨2⟩ ⟨1⟩,
        .alu .lt ⟨2⟩ (.stackSlot ⟨2⟩ false) (.imm (.word64 boundedCap))
      ]
      term := .jccBool (.stackSlot ⟨2⟩ true) ⟨1⟩ ⟨2⟩ },
    { instrs := []
      term := .ud2 },
    { instrs := [.extractField0 ⟨0⟩ ⟨1⟩]
      term := .ret }
  ]

/-- `pub fn with_temp_invalid(idx: &mut BoundedIdx, callback: fn(&BoundedIdx))`:
    1. Temporarily mutates `*idx` in slot `1` to `BoundedIdx { val: 5 }`
       (`5 ≥ 4`, violating `boundedIdxInv`),
    2. Invokes the external safe `callback(idx)` exposing slot `1` while
       `idx.val == 5`, and
    3. Restores `*idx` in slot `1` to `BoundedIdx { val: 0 }` (`0 < 4`,
       satisfying `boundedIdxInv`) before returning `.unit`! -/
def withTempInvalidOpenBody : OpenBody where
  argTys := [.adt 0]
  retTy := .unit
  blocks := [
    { instrs := [.wrapAdt 0 ⟨1⟩ (.imm (.word64 5))]
      term := .callExternal [1] [] ⟨0⟩ .unit ⟨1⟩ },
    { instrs := [
        .wrapAdt 0 ⟨1⟩ (.imm (.word64 0)),
        .mov ⟨0⟩ (.imm .unit)
      ]
      term := .ret }
  ]

/-- `pub fn with_restored_before_call(idx: &mut BoundedIdx, callback: fn(&BoundedIdx))`:
    Temporarily mutates `*idx` in slot `1` to `BoundedIdx { val: 5 }`, but
    **restores** `*idx` to `BoundedIdx { val: 2 }` (`2 < 4`, satisfying
    `boundedIdxInv`) *before* invoking `callback(idx)`. -/
def withRestoredBeforeCallOpenBody : OpenBody where
  argTys := [.adt 0]
  retTy := .unit
  blocks := [
    { instrs := [
        .wrapAdt 0 ⟨1⟩ (.imm (.word64 5)),
        .wrapAdt 0 ⟨1⟩ (.imm (.word64 2))
      ]
      term := .callExternal [1] [] ⟨0⟩ .unit ⟨1⟩ },
    { instrs := [.mov ⟨0⟩ (.imm .unit)]
      term := .ret }
  ]

/-- `pub fn with_unexposed_private_temp(idx: &BoundedIdx, callback: fn(&BoundedIdx)) -> usize`:
    Writes an out-of-bounds value `.adt 0 (.word64 99)` into caller-private
    local slot `2` (`2 ∉ exposedSlots`, while keeping valid `idx` in exposed
    slot `1`), invokes `callback(idx)` with `exposedSlots = [1]`, and then
    returns `idx.val` from slot `1`. -/
def withUnexposedPrivateTempOpenBody : OpenBody where
  argTys := [.adt 0]
  retTy := .usize
  blocks := [
    { instrs := [.wrapAdt 0 ⟨2⟩ (.imm (.word64 99))]
      term := .callExternal [1] [] ⟨0⟩ .unit ⟨1⟩ },
    { instrs := [.extractField0 ⟨0⟩ ⟨1⟩]
      term := .ret }
  ]

/-!
### 4.4 The Callback Re-Entrancy Soundness Exploit Under Naive Entry/Exit Checking

Suppose `callExternal` is modeled naively (`evalNaiveOpenStep`) without asserting
`boundedIdxInv` on exposed arguments/references at the call step (checking
`boundedIdxInv` only at the outer function's entry and final `.ret`).
-/

def evalNaiveOpenTerm (s : OpenState) (term : OpenTerm) :
    StepResult OpenState Unit X86Val :=
  match term with
  | .ret =>
    -- Enforce post-return `boundedIdxInv` on mutated `&mut BoundedIdx` in slot 1
    -- as well as return slot 0 at the outer function exit!
    match s.mem 0, s.mem 1 with
    | some retVal, some (.adt 0 (.word64 n)) =>
      if decide (n < boundedCap) then
        .terminated (.normal retVal)
      else
        .failed .ub
    | _, _ => .failed .ub
  | .jmp target =>
    .step () { s with bb := target.index, ip := 0 }
  | .ud2 =>
    .failed .ub
  | .jccBool cond falseTarget trueTarget =>
    match evalX86Operand s.mem cond with
    | some (v, mem') =>
      match v with
      | .boolVal false =>
        .step () { s with mem := mem', bb := falseTarget.index, ip := 0 }
      | .boolVal true =>
        .step () { s with mem := mem', bb := trueTarget.index, ip := 0 }
      | _ => .failed .ub
    | none => .failed .ub
  | .callExternal _ _ dst _ target =>
    -- Naive callback transition: assumes the safe callback returns `.unit`
    -- without checking that `boundedIdxInv` holds on exposed slots `[1]` at the
    -- moment of the call!
    .step () {
      s with
      mem := updateSlot s.mem dst.index (some .unit)
      bb := target.index
      ip := 0
    }

def evalNaiveOpenStep (body : OpenBody) (s : OpenState) :
    StepResult OpenState Unit X86Val :=
  match body.blocks[s.bb]? with
  | none => .failed .ub
  | some blk =>
    match blk.instrs[s.ip]? with
    | some instr => evalOpenInstr s instr
    | none => evalNaiveOpenTerm s blk.term

def NaiveOpenMachine : SmallStepMachine OpenBody OpenState Unit X86Val where
  initState := initOpenState
  step body s r := r = evalNaiveOpenStep body s

def NaiveOpenLang : Language :=
  NaiveOpenMachine.toLanguage

abbrev NaiveOpenSem (body : OpenBody) : NaiveOpenLang.Behavior :=
  NaiveOpenLang.sem body

def EnsuresOpenRetLibInv (libInv : LibInv) (retTy : X86Ty) :
    NaiveOpenLang.Behavior :=
  NaiveOpenLang.Spec (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      libInv q.init.tySizes retTy ret)

/-- Under `NaiveOpenMachine`, `get_unchecked` verifies cleanly (`WellFormed` and
    `EnsuresOpenRetLibInv boundedIdxInv .usize`). -/
theorem naive_getUnchecked_verified :
    NaiveOpenSem getUncheckedOpenBody ≤
      EnsuresOpenRetLibInv boundedIdxInv .usize := by
  refine behaviorOf_le_specOn (M := NaiveOpenMachine) ?_
  intro q out _ hpfx
  cases q with
  | mk s0 steps =>
  cases s0 with
  | mk mem0 perms0 regs0 entryRegs0 df0 bb0 ip0 tySizes0 =>
    have hInit := hpfx.1
    have hReach := hpfx.2
    have hb : bb0 = 0 := hInit.1
    have hip : ip0 = 0 := hInit.2.1
    have hdf : df0 = false := hInit.2.2.1
    have hregs : regs0 = entryRegs0 := hInit.2.2.2.1
    have hperms : perms0 = defaultOpenPerms := hInit.2.2.2.2.1
    subst hb hip hdf hregs hperms
    dsimp at hInit hReach
    cases hInit.2.2.2.2.2.2 with
    | intro v hv =>
      have hv1 : mem0 1 = some v := hv.1
      have hInv : boundedIdxInv tySizes0 (.adt 0) v := hv.2.1
      cases v with
      | word64 _ | boolVal _ | unit | bytes _ _ | stackPtr _ => cases hInv
      | adt adtId inner =>
        cases adtId with
        | succ _ => cases hInv
        | zero =>
          cases inner with
          | boolVal _ | unit | adt _ _ | bytes _ _ | stackPtr _ => cases hInv
          | word64 n =>
            have hLt : n < boundedCap := hInv
            have hDecLt : decide (n < boundedCap) = true := decide_eq_true hLt
            let s0' : OpenState := {
              mem := mem0, perms := defaultOpenPerms, regs := regs0,
              entryRegs := regs0, df := false, bb := 0, ip := 0, tySizes := tySizes0
            }
            have hStep1 : evalNaiveOpenStep getUncheckedOpenBody s0' =
                .step () { s0' with mem := updateSlot mem0 2 (some (.word64 n)), ip := 1 } := by
              change evalOpenInstr s0' (.extractField0 ⟨2⟩ ⟨1⟩) = _
              dsimp [evalOpenInstr, checkWritableSlot, defaultOpenPerms, s0']
              rw [hv1]
              rfl
            cases out with
            | mk trOut outcOut =>
            cases hReach with
            | zero => exact ⟨True.intro, fun _ h => by cases h⟩
            | choice _ _ _ _ _ _ _ h1 _ _ =>
              change _ = evalNaiveOpenStep getUncheckedOpenBody s0' at h1
              rw [hStep1] at h1; cases h1
            | emptyChoice _ _ _ _ h1 _ =>
              change _ = evalNaiveOpenStep getUncheckedOpenBody s0' at h1
              rw [hStep1] at h1; cases h1
            | terminated _ _ _ h1 =>
              change _ = evalNaiveOpenStep getUncheckedOpenBody s0' at h1
              rw [hStep1] at h1; cases h1
            | failed _ _ _ h1 =>
              change _ = evalNaiveOpenStep getUncheckedOpenBody s0' at h1
              rw [hStep1] at h1; cases h1
            | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep1.symm⟩)
            | step k1 _ s1 _ _ _ h1 hr1 =>
              change _ = evalNaiveOpenStep getUncheckedOpenBody s0' at h1
              rw [hStep1] at h1; injection h1 with _ hs1; subst hs1
              let m1 := updateSlot mem0 2 (some (.word64 n))
              let s1' : OpenState := { s0' with mem := m1, ip := 1 }
              have hStep2 : evalNaiveOpenStep getUncheckedOpenBody s1' =
                  .step () { s0' with mem := updateSlot m1 2 (some (.boolVal true)), ip := 2 } := by
                change evalOpenInstr s1'
                  (.alu .lt ⟨2⟩ (.stackSlot ⟨2⟩ false) (.imm (.word64 boundedCap))) = _
                dsimp [evalOpenInstr, checkWritableSlot, defaultOpenPerms, evalX86Operand, evalX86BinOp, s0', s1', m1, updateSlot]
                rw [hDecLt]
                rfl
              cases hr1 with
              | zero => exact ⟨True.intro, fun _ h => by cases h⟩
              | choice _ _ _ _ _ _ _ h2 _ _ =>
                change _ = evalNaiveOpenStep getUncheckedOpenBody s1' at h2
                rw [hStep2] at h2; cases h2
              | emptyChoice _ _ _ _ h2 _ =>
                change _ = evalNaiveOpenStep getUncheckedOpenBody s1' at h2
                rw [hStep2] at h2; cases h2
              | terminated _ _ _ h2 =>
                change _ = evalNaiveOpenStep getUncheckedOpenBody s1' at h2
                rw [hStep2] at h2; cases h2
              | failed _ _ _ h2 =>
                change _ = evalNaiveOpenStep getUncheckedOpenBody s1' at h2
                rw [hStep2] at h2; cases h2
              | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep2.symm⟩)
              | step k2 _ s2 _ _ _ h2 hr2 =>
                change _ = evalNaiveOpenStep getUncheckedOpenBody s1' at h2
                rw [hStep2] at h2; injection h2 with _ hs2; subst hs2
                let m2 := updateSlot m1 2 (some (.boolVal true))
                let s2' : OpenState := { s0' with mem := m2, ip := 2 }
                have hStep3 : evalNaiveOpenStep getUncheckedOpenBody s2' =
                    .step () { s0' with mem := updateSlot m2 2 none, bb := 2, ip := 0 } := rfl
                cases hr2 with
                | zero => exact ⟨True.intro, fun _ h => by cases h⟩
                | choice _ _ _ _ _ _ _ h3 _ _ =>
                  change _ = evalNaiveOpenStep getUncheckedOpenBody s2' at h3
                  rw [hStep3] at h3; cases h3
                | emptyChoice _ _ _ _ h3 _ =>
                  change _ = evalNaiveOpenStep getUncheckedOpenBody s2' at h3
                  rw [hStep3] at h3; cases h3
                | terminated _ _ _ h3 =>
                  change _ = evalNaiveOpenStep getUncheckedOpenBody s2' at h3
                  rw [hStep3] at h3; cases h3
                | failed _ _ _ h3 =>
                  change _ = evalNaiveOpenStep getUncheckedOpenBody s2' at h3
                  rw [hStep3] at h3; cases h3
                | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep3.symm⟩)
                | step k3 _ s3 _ _ _ h3 hr3 =>
                  change _ = evalNaiveOpenStep getUncheckedOpenBody s2' at h3
                  rw [hStep3] at h3; injection h3 with _ hs3; subst hs3
                  let m3 := updateSlot m2 2 none
                  have hm3_1 : m3 1 = some (.adt 0 (.word64 n)) := hv1
                  let s3' : OpenState := { s0' with mem := m3, bb := 2, ip := 0 }
                  have hStep4 : evalNaiveOpenStep getUncheckedOpenBody s3' =
                      .step () { s0' with mem := updateSlot m3 0 (some (.word64 n)), bb := 2, ip := 1 } := by
                    change evalOpenInstr s3' (.extractField0 ⟨0⟩ ⟨1⟩) = _
                    dsimp [evalOpenInstr, checkWritableSlot, defaultOpenPerms, s0', s3']
                    rw [hm3_1]
                    rfl
                  cases hr3 with
                  | zero => exact ⟨True.intro, fun _ h => by cases h⟩
                  | choice _ _ _ _ _ _ _ h4 _ _ =>
                    change _ = evalNaiveOpenStep getUncheckedOpenBody s3' at h4
                    rw [hStep4] at h4; cases h4
                  | emptyChoice _ _ _ _ h4 _ =>
                    change _ = evalNaiveOpenStep getUncheckedOpenBody s3' at h4
                    rw [hStep4] at h4; cases h4
                  | terminated _ _ _ h4 =>
                    change _ = evalNaiveOpenStep getUncheckedOpenBody s3' at h4
                    rw [hStep4] at h4; cases h4
                  | failed _ _ _ h4 =>
                    change _ = evalNaiveOpenStep getUncheckedOpenBody s3' at h4
                    rw [hStep4] at h4; cases h4
                  | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep4.symm⟩)
                  | step k4 _ s4 _ _ _ h4 hr4 =>
                    change _ = evalNaiveOpenStep getUncheckedOpenBody s3' at h4
                    rw [hStep4] at h4; injection h4 with _ hs4; subst hs4
                    let m4 := updateSlot m3 0 (some (.word64 n))
                    have hm4_1 : m4 1 = some (.adt 0 (.word64 n)) := hv1
                    let s4' : OpenState := { s0' with mem := m4, bb := 2, ip := 1 }
                    have hStep5 : evalNaiveOpenStep getUncheckedOpenBody s4' =
                        .terminated (.normal (.word64 n)) := by
                      change evalNaiveOpenTerm s4' .ret = _
                      dsimp [evalNaiveOpenTerm, s4', m4, updateSlot]
                      rw [hm3_1]
                      change (if decide (n < boundedCap) = true then
                                StepResult.terminated (TerminationKind.normal (X86Val.word64 n))
                              else StepResult.failed FailureKind.ub) = _
                      rw [hDecLt]
                      rfl
                    cases hr4 with
                    | zero => exact ⟨True.intro, fun _ h => by cases h⟩
                    | step _ _ _ _ _ _ h5 _ =>
                      change _ = evalNaiveOpenStep getUncheckedOpenBody s4' at h5
                      rw [hStep5] at h5; cases h5
                    | choice _ _ _ _ _ _ _ h5 _ _ =>
                      change _ = evalNaiveOpenStep getUncheckedOpenBody s4' at h5
                      rw [hStep5] at h5; cases h5
                    | emptyChoice _ _ _ _ h5 _ =>
                      change _ = evalNaiveOpenStep getUncheckedOpenBody s4' at h5
                      rw [hStep5] at h5; cases h5
                    | failed _ _ _ h5 =>
                      change _ = evalNaiveOpenStep getUncheckedOpenBody s4' at h5
                      rw [hStep5] at h5; cases h5
                    | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep5.symm⟩)
                    | terminated _ _ term h5 =>
                      change _ = evalNaiveOpenStep getUncheckedOpenBody s4' at h5
                      rw [hStep5] at h5
                      injection h5 with hTerm
                      subst hTerm
                      refine ⟨True.intro, ?_⟩
                      intro ret hRet
                      injection hRet with h1'
                      injection h1' with h2'
                      subst h2'
                      exact True.intro

/-- **Exploit Part 1 (`naive_withTempInvalid_verified`):**
    Under `NaiveOpenMachine` (which checks `boundedIdxInv` at entry and `.ret`
    only), `with_temp_invalid` ALSO passes its full `FnObligation`
    (`EnsuresOpenRetLibInv boundedIdxInv .unit`, including the post-return
    check in `evalNaiveOpenTerm` that slot `1` holds `BoundedIdx { val: 0 }`
    with `0 < 4`)! -/
theorem naive_withTempInvalid_verified :
    NaiveOpenSem withTempInvalidOpenBody ≤
      EnsuresOpenRetLibInv boundedIdxInv .unit := by
  refine behaviorOf_le_specOn (M := NaiveOpenMachine) ?_
  intro q out _ hpfx
  cases q with
  | mk s0 steps =>
  cases s0 with
  | mk mem0 perms0 regs0 entryRegs0 df0 bb0 ip0 tySizes0 =>
    have hInit := hpfx.1
    have hReach := hpfx.2
    have hb : bb0 = 0 := hInit.1
    have hip : ip0 = 0 := hInit.2.1
    have hdf : df0 = false := hInit.2.2.1
    have hregs : regs0 = entryRegs0 := hInit.2.2.2.1
    have hperms : perms0 = defaultOpenPerms := hInit.2.2.2.2.1
    subst hb hip hdf hregs hperms
    dsimp at hInit hReach
    cases out with
    | mk trOut outcOut =>
    cases hReach with
    | zero => exact ⟨True.intro, fun _ h => by cases h⟩
    | choice _ _ _ _ _ _ _ h1 _ _ => cases h1
    | emptyChoice _ _ _ _ h1 _ => cases h1
    | terminated _ _ _ h1 => cases h1
    | failed _ _ _ h1 => cases h1
    | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
    | step k1 _ s1 _ _ _ h1 hr1 =>
      injection h1 with _ hs1; subst hs1
      cases hr1 with
      | zero => exact ⟨True.intro, fun _ h => by cases h⟩
      | choice _ _ _ _ _ _ _ h2 _ _ => cases h2
      | emptyChoice _ _ _ _ h2 _ => cases h2
      | terminated _ _ _ h2 => cases h2
      | failed _ _ _ h2 => cases h2
      | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
      | step k2 _ s2 _ _ _ h2 hr2 =>
        injection h2 with _ hs2; subst hs2
        cases hr2 with
        | zero => exact ⟨True.intro, fun _ h => by cases h⟩
        | choice _ _ _ _ _ _ _ h3 _ _ => cases h3
        | emptyChoice _ _ _ _ h3 _ => cases h3
        | terminated _ _ _ h3 => cases h3
        | failed _ _ _ h3 => cases h3
        | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
        | step k3 _ s3 _ _ _ h3 hr3 =>
          injection h3 with _ hs3; subst hs3
          cases hr3 with
          | zero => exact ⟨True.intro, fun _ h => by cases h⟩
          | choice _ _ _ _ _ _ _ h4 _ _ => cases h4
          | emptyChoice _ _ _ _ h4 _ => cases h4
          | terminated _ _ _ h4 => cases h4
          | failed _ _ _ h4 => cases h4
          | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
          | step k4 _ s4 _ _ _ h4 hr4 =>
            injection h4 with _ hs4; subst hs4
            cases hr4 with
            | zero => exact ⟨True.intro, fun _ h => by cases h⟩
            | step _ _ _ _ _ _ h5 _ => cases h5
            | choice _ _ _ _ _ _ _ h5 _ _ => cases h5
            | emptyChoice _ _ _ _ h5 _ => cases h5
            | failed _ _ _ h5 => cases h5
            | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
            | terminated _ _ term h5 =>
              injection h5 with hTerm
              subst hTerm
              refine ⟨True.intro, ?_⟩
              intro ret hRet
              injection hRet with h1'
              injection h1' with h2'
              subst h2'
              exact True.intro

/-- Concrete linked execution of `caller` when `.callExternal` invokes a safe
    callback `callee` (such as `get_unchecked`) on the shared state `s`:
    `inCallee = false` executes `caller`, and `.callExternal` switches to
    `inCallee = true` (`bb = 0, ip = 0` of `callee`) while preserving `s.mem`
    (so `callee` observes `s.mem 1` directly!). -/
structure LinkedState where
  openState : OpenState
  inCallee : Bool := false
  retTarget : Nat := 0
  retDst : SlotId := ⟨0⟩

def evalLinkedStep (caller callee : OpenBody) (ls : LinkedState) :
    StepResult LinkedState Unit X86Val :=
  let s := ls.openState
  let active := if ls.inCallee then callee else caller
  match active.blocks[s.bb]? with
  | none => .failed .ub
  | some blk =>
    match blk.instrs[s.ip]? with
    | some instr =>
      match evalOpenInstr s instr with
      | .step () s' => .step () { ls with openState := s' }
      | .choice k br => .choice k (fun ls' => ∃ s', br s' ∧ ls' = { ls with openState := s' })
      | .terminated t => .terminated t
      | .failed err => .failed err
    | none =>
      match blk.term with
      | .ret =>
        match s.mem 0 with
        | none => .failed .ub
        | some retVal =>
          if ls.inCallee then
            .step () {
              openState := {
                s with
                mem := updateSlot s.mem ls.retDst.index (some retVal)
                bb := ls.retTarget
                ip := 0
              }
              inCallee := false
            }
          else
            .terminated (.normal retVal)
      | .jmp target =>
        .step () { ls with openState := { s with bb := target.index, ip := 0 } }
      | .ud2 =>
        .failed .ub
      | .jccBool cond falseTarget trueTarget =>
        match evalX86Operand s.mem cond with
        | some (.boolVal false, mem') =>
          .step () { ls with openState := { s with mem := mem', bb := falseTarget.index, ip := 0 } }
        | some (.boolVal true, mem') =>
          .step () { ls with openState := { s with mem := mem', bb := trueTarget.index, ip := 0 } }
        | _ => .failed .ub
      | .callExternal _ _ dst _ target =>
        if ls.inCallee then
          .failed .ub
        else
          .step () {
            openState := { s with bb := 0, ip := 0 }
            inCallee := true
            retTarget := target.index
            retDst := dst
          }

def LinkedMachine (caller callee : OpenBody) :
    SmallStepMachine Unit LinkedState Unit X86Val where
  initState _ ls := ls.inCallee = false ∧ initOpenState caller ls.openState
  step _ ls r := r = evalLinkedStep caller callee ls

/-- **Exploit Part 2 (`naive_reentrancy_exploit_triggers_ub`):**
    Although both `get_unchecked` (`naive_getUnchecked_verified`) and
    `with_temp_invalid` (`naive_withTempInvalid_verified`) pass their individual
    entry-to-exit `FnObligation`s under `NaiveOpenMachine`, composing them in a
    100% safe program `with_temp_invalid(&mut idx, get_unchecked)` on a valid
    initial state `idx = BoundedIdx { val: 0 }` reaches **`.failed .ub` in 6
    steps**! -/
theorem naive_reentrancy_exploit_triggers_ub :
    let s0 : OpenState := {
      mem := updateSlot (fun _ => none) 1 (some (.adt 0 (.word64 0)))
    }
    let ls0 : LinkedState := { openState := s0, inCallee := false }
    initOpenState withTempInvalidOpenBody s0 ∧
    ReachesPrefix (LinkedMachine withTempInvalidOpenBody getUncheckedOpenBody)
      () ls0 6 ls0 [(), (), (), (), ()] (.failed .ub) := by
  intro s0 ls0
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨.adt 0 (.word64 0), rfl, Nat.zero_lt_succ 3, by intro h; cases h⟩⟩, ?_⟩
  let s1 : OpenState := { s0 with mem := updateSlot s0.mem 1 (some (.adt 0 (.word64 5))), ip := 1 }
  let ls1 : LinkedState := { ls0 with openState := s1 }
  let s2 : OpenState := { s1 with bb := 0, ip := 0 }
  let ls2 : LinkedState := { openState := s2, inCallee := true, retTarget := 1, retDst := ⟨0⟩ }
  let s3 : OpenState := { s2 with mem := updateSlot s2.mem 2 (some (.word64 5)), ip := 1 }
  let ls3 : LinkedState := { ls2 with openState := s3 }
  let s4 : OpenState := { s3 with mem := updateSlot s3.mem 2 (some (.boolVal false)), ip := 2 }
  let ls4 : LinkedState := { ls3 with openState := s4 }
  let s5 : OpenState := { s4 with mem := updateSlot s4.mem 2 none, bb := 1, ip := 0 }
  let ls5 : LinkedState := { ls4 with openState := s5 }
  exact ReachesPrefix.step 5 ls0 ls1 () [(), (), (), ()] _ rfl
    (ReachesPrefix.step 4 ls1 ls2 () [(), (), ()] _ rfl
      (ReachesPrefix.step 3 ls2 ls3 () [(), ()] _ rfl
        (ReachesPrefix.step 2 ls3 ls4 () [()] _ rfl
          (ReachesPrefix.step 1 ls4 ls5 () [] _ rfl
            (ReachesPrefix.failed 0 ls5 .ub rfl)))))

/-!
### 4.5 Clean Small-Step Open-World Call & ISA Frame Isolation Contract (`GuardedOpenMachine`)

We now mechanize the small-step open-world call contract (`evalGuardedOpenStep`)
that closes the re-entrancy exploit while requiring **zero step-indexed Iris
logic and zero coinduction** in `trusted/`:

1. **Positive Pre-Call Check (`CallSiteSatisfiesLibInv`):**
   At the exact step of `.callExternal exposedSlots exposedMutSlots dst retTy
   target`, every `slot ∈ exposedSlots` must hold an initialized `BoundedIdx`
   satisfying `boundedIdxInv` (`val < 4`), and the direction flag must satisfy
   `s.df = false`. If any exposed slot violates `boundedIdxInv`, the machine
   steps immediately to **`.failed .ub`**.
2. **Caller Frame Isolation & ISA ABI Preservation (`GuardedPostCallBranch`):**
   When the pre-call check succeeds, `.callExternal` steps via
   `.choice .demonic (GuardedPostCallBranch ...)` to all post-call states `s'`
   that:
   - preserve all unexposed caller-private locals (`i ≠ dst.index ∧ i ∉
     exposedMutSlots → s'.mem i = s.mem i`),
   - preserve all `BytePerm.callerFrame` and `BytePerm.readOnly` stack slots,
     callee-saved registers (`rbp`, `rbx`, `rsp`, `r12`–`r15`), and `DF = 0`
     (`X86AbiFramePreserved s s'`), and
   - demonically havoc `dst` and `exposedMutSlots` to arbitrary values
     satisfying `boundedIdxInv` (`RetAndMutSatisfyLibInv`).
-/

/-- Decidable pre-call check asserting that:
    1. Every exposed `BoundedIdx` slot in `exposedSlots` holds an initialized
       value satisfying `boundedIdxInv` (`n < boundedCap`),
    2. The return destination `dst` and all `exposedMutSlots` have writable
       stack permission (`BytePerm.readWrite`), and
    3. The x86-64 direction flag is clear (`s.df = false`). -/
def checkExposedSlot (s : OpenState) (slot : Nat) : Bool :=
  match s.mem slot with
  | some (.adt 0 (.word64 n)) => decide (n < boundedCap)
  | _ => false

def checkCallSiteLibInv (s : OpenState) (exposedSlots exposedMutSlots : List Nat)
    (dst : SlotId) : Bool :=
  !s.df &&
  checkWritableSlot s dst.index &&
  exposedMutSlots.all (checkWritableSlot s) &&
  exposedSlots.all (checkExposedSlot s)

/-- Propositional characterization of `checkCallSiteLibInv`. -/
def CallSiteSatisfiesLibInv (s : OpenState)
    (exposedSlots exposedMutSlots : List Nat) (dst : SlotId) : Prop :=
  checkCallSiteLibInv s exposedSlots exposedMutSlots dst = true

/-- Decidable check that all System V AMD64 callee-saved registers (`rbx`,
    `rsp`, `rbp`, `r12`–`r15`) match their function-entry snapshot. -/
def checkCalleeSavedPreserved (s : OpenState) : Bool :=
  s.regs .rbx == s.entryRegs .rbx &&
  s.regs .rsp == s.entryRegs .rsp &&
  s.regs .rbp == s.entryRegs .rbp &&
  s.regs .r12 == s.entryRegs .r12 &&
  s.regs .r13 == s.entryRegs .r13 &&
  s.regs .r14 == s.entryRegs .r14 &&
  s.regs .r15 == s.entryRegs .r15

/-- System V AMD64 ABI frame and callee-saved register preservation across a
    call boundary. -/
def X86AbiFramePreserved (s s' : OpenState) (exposedMutSlots : List Nat)
    (dst : SlotId) : Prop :=
  (∀ r : Reg64, r.isCalleeSaved = true → s'.regs r = s.regs r) ∧
  checkCalleeSavedPreserved s' = checkCalleeSavedPreserved s ∧
  s'.entryRegs = s.entryRegs ∧
  s'.df = false ∧
  s'.perms = s.perms ∧
  (∀ slot : Nat, slot ≠ dst.index → slot ∉ exposedMutSlots →
    (s.perms slot = .callerFrame ∨ s.perms slot = .readOnly) →
      s'.mem slot = s.mem slot)

/-- Caller-private local frame isolation across an external call: every stack
    slot `i` that is neither the return destination `dst` nor an exposed
    mutable reference slot in `exposedMutSlots` is preserved unchanged. -/
def CallerFrameIsolated (s s' : OpenState) (exposedMutSlots : List Nat)
    (dst : SlotId) : Prop :=
  ∀ i : Nat, i ≠ dst.index → i ∉ exposedMutSlots → s'.mem i = s.mem i

/-- Demonic post-call branch envelope for an open-world safe call. -/
def GuardedPostCallBranch (s : OpenState) (exposedMutSlots : List Nat)
    (dst : SlotId) (retTy : X86Ty) (target : BlockLabel)
    (s' : OpenState) : Prop :=
  s'.bb = target.index ∧
  s'.ip = 0 ∧
  s'.tySizes = s.tySizes ∧
  CallerFrameIsolated s s' exposedMutSlots dst ∧
  X86AbiFramePreserved s s' exposedMutSlots dst ∧
  (∃ vRet, s'.mem dst.index = some vRet ∧
    boundedIdxInv s.tySizes retTy vRet) ∧
  (∀ i, i ≠ dst.index → i ∈ exposedMutSlots →
    ∃ vMut, s'.mem i = some vMut ∧
      boundedIdxInv s.tySizes (.adt 0) vMut)

/-- Canonical default value for `retTy` under `boundedIdxInv`, used to prove
    that `GuardedPostCallBranch` is constructively inhabited (`InhabitedDemonic`). -/
def defaultBoundedVal (tySizes : Nat → Nat) (ty : X86Ty) : X86Val :=
  match ty with
  | .usize => .word64 0
  | .bool => .boolVal false
  | .unit => .unit
  | .adt adtId => .adt adtId (.word64 0)
  | .param idx => .bytes (tySizes idx) 0
  | .refParam _ => .stackPtr ⟨1⟩

theorem defaultBoundedVal_satisfies (tySizes : Nat → Nat) (ty : X86Ty) :
    boundedIdxInv tySizes ty (defaultBoundedVal tySizes ty) := by
  cases ty with
  | usize => exact True.intro
  | bool => exact True.intro
  | unit => exact True.intro
  | adt id =>
    cases id with
    | zero => exact Nat.zero_lt_succ 3
    | succ k => rfl
  | param idx => exact rfl
  | refParam idx => exact True.intro

/-- Canonical post-call memory witness for `GuardedPostCallBranch`. -/
def canonicalPostCallMem (s : OpenState) (exposedMutSlots : List Nat)
    (dst : SlotId) (retTy : X86Ty) (i : Nat) : Option X86Val :=
  match decide (i = dst.index) with
  | true => some (defaultBoundedVal s.tySizes retTy)
  | false =>
    match decide (i ∈ exposedMutSlots) with
    | true => some (.adt 0 (.word64 0))
    | false => s.mem i

/-- Canonical post-call state witness proving `GuardedPostCallBranch` is always
    inhabited. -/
def canonicalPostCallState (s : OpenState) (exposedMutSlots : List Nat)
    (dst : SlotId) (retTy : X86Ty) (target : BlockLabel) : OpenState where
  mem := canonicalPostCallMem s exposedMutSlots dst retTy
  perms := s.perms
  regs := s.regs
  entryRegs := s.entryRegs
  df := false
  bb := target.index
  ip := 0
  tySizes := s.tySizes

theorem canonicalPostCallState_satisfies (s : OpenState)
    (exposedMutSlots : List Nat) (dst : SlotId) (retTy : X86Ty)
    (target : BlockLabel) :
    GuardedPostCallBranch s exposedMutSlots dst retTy target
      (canonicalPostCallState s exposedMutSlots dst retTy target) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro i hNeDst hNotMut
    dsimp [canonicalPostCallState, canonicalPostCallMem]
    rw [decide_eq_false hNeDst, decide_eq_false hNotMut]
  · refine ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro slot hNeDst hNotMut _
    dsimp [canonicalPostCallState, canonicalPostCallMem]
    rw [decide_eq_false hNeDst, decide_eq_false hNotMut]
  · refine ⟨defaultBoundedVal s.tySizes retTy, ?_,
            defaultBoundedVal_satisfies s.tySizes retTy⟩
    dsimp [canonicalPostCallState, canonicalPostCallMem]
    rw [decide_eq_true rfl]
  · intro i hNeDst hInMut
    refine ⟨.adt 0 (.word64 0), ?_, Nat.zero_lt_succ 3⟩
    dsimp [canonicalPostCallState, canonicalPostCallMem]
    rw [decide_eq_false hNeDst, decide_eq_true hInMut]

/-- Guarded terminator evaluation enforcing:
    1. At `.callExternal`: positive pre-call check `checkCallSiteLibInv`
       (stepping immediately to `.failed .ub` if any exposed slot violates
       `boundedIdxInv`, if `dst`/`exposedMutSlots` are not `.readWrite`, or if
       `df = true`) followed by demonic post-call choice over
       `GuardedPostCallBranch`.
    2. At `.ret`: direction flag `df = false`, callee-saved register
       preservation (`checkCalleeSavedPreserved`), and post-return
       `boundedIdxInv` on mutated/borrowed slot `1`. -/
def evalGuardedOpenTerm (s : OpenState) (term : OpenTerm) :
    StepResult OpenState Unit X86Val :=
  match term with
  | .ret =>
    match !s.df && checkCalleeSavedPreserved s with
    | false => .failed .ub
    | true =>
      match s.mem 0, s.mem 1 with
      | some retVal, some (.adt 0 (.word64 n)) =>
        match decide (n < boundedCap) with
        | true => .terminated (.normal retVal)
        | false => .failed .ub
      | _, _ => .failed .ub
  | .jmp target =>
    .step () { s with bb := target.index, ip := 0 }
  | .ud2 =>
    .failed .ub
  | .jccBool cond falseTarget trueTarget =>
    match evalX86Operand s.mem cond with
    | some (v, mem') =>
      match v with
      | .boolVal false =>
        .step () { s with mem := mem', bb := falseTarget.index, ip := 0 }
      | .boolVal true =>
        .step () { s with mem := mem', bb := trueTarget.index, ip := 0 }
      | _ => .failed .ub
    | none => .failed .ub
  | .callExternal exposedSlots exposedMutSlots dst retTy target =>
    match checkCallSiteLibInv s exposedSlots exposedMutSlots dst with
    | true =>
      .choice .demonic
        (GuardedPostCallBranch s exposedMutSlots dst retTy target)
    | false =>
      .failed .ub

def evalGuardedOpenStep (body : OpenBody) (s : OpenState) :
    StepResult OpenState Unit X86Val :=
  match body.blocks[s.bb]? with
  | none => .failed .ub
  | some blk =>
    match blk.instrs[s.ip]? with
    | some instr => evalOpenInstr s instr
    | none => evalGuardedOpenTerm s blk.term

def GuardedOpenMachine : SmallStepMachine OpenBody OpenState Unit X86Val where
  initState := initOpenState
  step body s r := r = evalGuardedOpenStep body s

def GuardedOpenLang : Language :=
  GuardedOpenMachine.toLanguage

abbrev GuardedOpenSem (body : OpenBody) : GuardedOpenLang.Behavior :=
  GuardedOpenLang.sem body

def EnsuresGuardedRetLibInv (libInv : LibInv) (retTy : X86Ty) :
    GuardedOpenLang.Behavior :=
  GuardedOpenLang.Spec (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      libInv q.init.tySizes retTy ret)

theorem nat_beq_refl (n : Nat) : (n == n) = true :=
  decide_eq_true rfl

theorem checkCalleeSavedPreserved_refl (mem : Nat → Option X86Val)
    (perms : Nat → BytePerm) (regs : Reg64 → Nat) (df : Bool) (bb ip : Nat)
    (tySizes : Nat → Nat) :
    checkCalleeSavedPreserved {
      mem := mem, perms := perms, regs := regs, entryRegs := regs,
      df := df, bb := bb, ip := ip, tySizes := tySizes
    } = true := by
  dsimp [checkCalleeSavedPreserved]
  rw [nat_beq_refl (regs .rbx), nat_beq_refl (regs .rsp),
      nat_beq_refl (regs .rbp), nat_beq_refl (regs .r12),
      nat_beq_refl (regs .r13), nat_beq_refl (regs .r14),
      nat_beq_refl (regs .r15)]
  rfl

def StepResult.isChoice {State Obs Val : Type} : StepResult State Obs Val → Bool
  | .choice _ _ => true
  | _ => false

theorem not_choice_of_isChoice_false {State Obs Val : Type}
    {r : StepResult State Obs Val} {kind : ChoiceKind} {branches : State → Prop}
    (h : r.isChoice = false) : r ≠ .choice kind branches := by
  intro hEq
  rw [hEq] at h
  cases h

theorem evalOpenInstr_isChoice_false (s : OpenState) (instr : X86Instr) :
    (evalOpenInstr s instr).isChoice = false := by
  cases instr with
  | mov dst src =>
    dsimp [evalOpenInstr]
    cases checkWritableSlot s dst.index
    · rfl
    · cases evalX86Operand s.mem src with
      | none => rfl
      | some p => cases p; rfl
  | alu op dst lhs rhs =>
    dsimp [evalOpenInstr]
    cases checkWritableSlot s dst.index
    · rfl
    · dsimp
      cases evalX86Operand s.mem lhs with
      | none => rfl
      | some p1 =>
        cases p1 with
        | mk v1 m1 =>
          dsimp
          cases evalX86Operand m1 rhs with
          | none => rfl
          | some p2 =>
            cases p2 with
            | mk v2 m2 =>
              dsimp
              cases evalX86BinOp op v1 v2 <;> rfl
  | wrapAdt adtId dst src =>
    dsimp [evalOpenInstr]
    cases checkWritableSlot s dst.index
    · rfl
    · cases evalX86Operand s.mem src with
      | none => rfl
      | some p => cases p; rfl
  | extractField0 dst src =>
    dsimp [evalOpenInstr]
    cases checkWritableSlot s dst.index
    · rfl
    · cases s.mem src.index with
      | none => rfl
      | some v => cases v <;> rfl
  | leaSlot dst target =>
    dsimp [evalOpenInstr]
    cases checkWritableSlot s dst.index
    · rfl
    · cases s.mem target.index <;> rfl
  | reborrowSlot dst srcPtr =>
    dsimp [evalOpenInstr]
    cases checkWritableSlot s dst.index
    · rfl
    · dsimp
      cases s.mem srcPtr.index with
      | none => rfl
      | some v =>
        cases v with
        | stackPtr target =>
          dsimp
          cases s.mem target.index <;> rfl
        | _ => rfl
  | allocSlot slot =>
    dsimp [evalOpenInstr]
    cases checkWritableSlot s slot.index <;> rfl
  | deallocSlot slot =>
    dsimp [evalOpenInstr]
    cases checkWritableSlot s slot.index <;> rfl
  | nop => rfl

theorem evalOpenInstr_not_choice (s : OpenState) (instr : X86Instr)
    (kind : ChoiceKind) (branches : OpenState → Prop) :
    evalOpenInstr s instr ≠ .choice kind branches :=
  not_choice_of_isChoice_false (evalOpenInstr_isChoice_false s instr)

theorem evalRet_isChoice_false (s : OpenState) :
    (evalGuardedOpenTerm s .ret).isChoice = false := by
  dsimp [evalGuardedOpenTerm]
  cases (!s.df && checkCalleeSavedPreserved s)
  · rfl
  · dsimp
    cases s.mem 0 with
    | none => rfl
    | some _ =>
      cases s.mem 1 with
      | none => rfl
      | some v1 =>
        cases v1 with
        | adt id inner =>
          cases id with
          | succ _ => rfl
          | zero =>
            cases inner with
            | word64 n =>
              change (match decide (n < boundedCap) with
                      | true => StepResult.terminated (TerminationKind.normal _)
                      | false => StepResult.failed FailureKind.ub).isChoice = false
              cases decide (n < boundedCap) <;> rfl
            | _ => rfl
        | _ => rfl

theorem evalRet_not_choice (s : OpenState)
    (kind : ChoiceKind) (branches : OpenState → Prop) :
    evalGuardedOpenTerm s .ret ≠ .choice kind branches :=
  not_choice_of_isChoice_false (evalRet_isChoice_false s)

theorem evalJccBool_isChoice_false (s : OpenState) (cond : X86Operand)
    (fT tT : BlockLabel) :
    (evalGuardedOpenTerm s (.jccBool cond fT tT)).isChoice = false := by
  dsimp [evalGuardedOpenTerm]
  cases evalX86Operand s.mem cond with
  | none => rfl
  | some p =>
    cases p with
    | mk v _ =>
      cases v with
      | boolVal b => cases b <;> rfl
      | _ => rfl

theorem evalJccBool_not_choice (s : OpenState) (cond : X86Operand)
    (fT tT : BlockLabel) (kind : ChoiceKind) (branches : OpenState → Prop) :
    evalGuardedOpenTerm s (.jccBool cond fT tT) ≠ .choice kind branches :=
  not_choice_of_isChoice_false (evalJccBool_isChoice_false s cond fT tT)

theorem guardedOpenMachine_total : TotalStep GuardedOpenMachine :=
  fun _ _ => ⟨_, rfl⟩

theorem guardedOpenMachine_inhabited : InhabitedDemonic GuardedOpenMachine := by
  intro body s kind branches hStep
  change StepResult.choice kind branches =
    evalGuardedOpenStep body s at hStep
  unfold evalGuardedOpenStep at hStep
  cases hBlk : body.blocks[s.bb]? with
  | none => rw [hBlk] at hStep; cases hStep
  | some blk =>
    rw [hBlk] at hStep
    dsimp at hStep
    cases hInstr : blk.instrs[s.ip]? with
    | some instr =>
      rw [hInstr] at hStep
      dsimp at hStep
      exact False.elim (evalOpenInstr_not_choice s instr kind branches hStep.symm)
    | none =>
      rw [hInstr] at hStep
      dsimp at hStep
      cases hTerm : blk.term with
      | ret =>
        rw [hTerm] at hStep
        exact False.elim (evalRet_not_choice s kind branches hStep.symm)
      | jmp _ => rw [hTerm] at hStep; cases hStep
      | ud2 => rw [hTerm] at hStep; cases hStep
      | jccBool cond fT tT =>
        rw [hTerm] at hStep
        exact False.elim (evalJccBool_not_choice s cond fT tT kind branches hStep.symm)
      | callExternal exposedSlots exposedMutSlots dst retTy target =>
        rw [hTerm] at hStep
        dsimp [evalGuardedOpenTerm] at hStep
        cases hCheck : checkCallSiteLibInv s exposedSlots exposedMutSlots dst with
        | false => rw [hCheck] at hStep; cases hStep
        | true =>
          rw [hCheck] at hStep
          injection hStep with _ hBr
          subst hBr
          exact ⟨canonicalPostCallState s exposedMutSlots dst retTy target,
                 canonicalPostCallState_satisfies s exposedMutSlots dst retTy target⟩

/-- **Theorem (a) (`withTempInvalid_rejected_under_guarded_call`):**
    Under `GuardedOpenMachine`, `with_temp_invalid` is **rejected**: from valid
    initial state `s0` (`BoundedIdx { val: 0 }`), it steps to `.failed .ub` at
    step 2 when `.callExternal [1] []` detects that exposed slot `1` holds
    `BoundedIdx { val: 5 }` (`¬ (5 < 4)`). -/
theorem withTempInvalid_rejected_under_guarded_call :
    ¬ (GuardedOpenSem withTempInvalidOpenBody ≤ GuardedOpenLang.WellFormed) := by
  intro hWf
  let s0 : OpenState := {
    mem := updateSlot (fun _ => none) 1 (some (.adt 0 (.word64 0)))
  }
  have hInit : initOpenState withTempInvalidOpenBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl,
     ⟨.adt 0 (.word64 0), rfl, Nat.zero_lt_succ 3, by intro h; cases h⟩⟩
  let s1 : OpenState := {
    s0 with
    mem := updateSlot s0.mem 1 (some (.adt 0 (.word64 5)))
    ip := 1
  }
  have hReach :
      ReachesPrefix GuardedOpenMachine withTempInvalidOpenBody s0 2 s0 [()]
        (.failed .ub) :=
    ReachesPrefix.step 1 s0 s1 () [] (.failed .ub) rfl
      (ReachesPrefix.failed 0 s1 .ub rfl)
  let q : ExecQuery OpenState := { init := s0, steps := 2 }
  have hStep := hWf q True.intro
  exact hStep.1 hInit [()] (.failed .ub) hReach

/-- **Theorem (b1) (`withRestoredBeforeCall_verified`):**
    If a function temporarily breaks `boundedIdxInv` on slot `1` (`val := 5`)
    but **restores** `boundedIdxInv` (`val := 2 < 4`) *before* invoking the
    external callback, it verifies cleanly under `GuardedOpenMachine` across all
    demonic callback executions! -/
theorem withRestoredBeforeCall_verified :
    GuardedOpenSem withRestoredBeforeCallOpenBody ≤
      EnsuresGuardedRetLibInv boundedIdxInv .unit := by
  refine behaviorOf_le_specOn (M := GuardedOpenMachine) ?_
  intro q out _ hpfx
  cases q with
  | mk s0 steps =>
  cases s0 with
  | mk mem0 perms0 regs0 entryRegs0 df0 bb0 ip0 tySizes0 =>
    have hInit := hpfx.1
    have hReach := hpfx.2
    have hb : bb0 = 0 := hInit.1
    have hip : ip0 = 0 := hInit.2.1
    have hdf : df0 = false := hInit.2.2.1
    have hregs : regs0 = entryRegs0 := hInit.2.2.2.1
    have hperms : perms0 = defaultOpenPerms := hInit.2.2.2.2.1
    subst hb hip hdf hregs hperms
    dsimp at hInit hReach
    let s0' : OpenState := {
      mem := mem0, perms := defaultOpenPerms, regs := regs0,
      entryRegs := regs0, df := false, bb := 0, ip := 0, tySizes := tySizes0
    }
    have hCalleeSaved0 : checkCalleeSavedPreserved s0' = true :=
      checkCalleeSavedPreserved_refl mem0 defaultOpenPerms regs0 false 0 0 tySizes0
    cases out with
    | mk trOut outcOut =>
    cases hReach with
    | zero => exact ⟨True.intro, fun _ h => by cases h⟩
    | choice _ _ _ _ _ _ _ h1 _ _ => cases h1
    | emptyChoice _ _ _ _ h1 _ => cases h1
    | terminated _ _ _ h1 => cases h1
    | failed _ _ _ h1 => cases h1
    | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
    | step k1 _ s1 _ _ _ h1 hr1 =>
      injection h1 with _ hs1; subst hs1
      cases hr1 with
      | zero => exact ⟨True.intro, fun _ h => by cases h⟩
      | choice _ _ _ _ _ _ _ h2 _ _ => cases h2
      | emptyChoice _ _ _ _ h2 _ => cases h2
      | terminated _ _ _ h2 => cases h2
      | failed _ _ _ h2 => cases h2
      | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
      | step k2 _ s2 _ _ _ h2 hr2 =>
        injection h2 with _ hs2; subst hs2
        let m1 := updateSlot mem0 1 (some (.adt 0 (.word64 5)))
        let m2 := updateSlot m1 1 (some (.adt 0 (.word64 2)))
        let s2' : OpenState := { s0' with mem := m2, ip := 2 }
        cases hr2 with
        | zero => exact ⟨True.intro, fun _ h => by cases h⟩
        | step _ _ _ _ _ _ h3 _ => cases h3
        | emptyChoice _ _ _ _ h3 hEmpty =>
          injection h3 with _ hBr
          subst hBr
          exact False.elim (hEmpty ⟨_, canonicalPostCallState_satisfies s2' [] ⟨0⟩ .unit ⟨1⟩⟩)
        | terminated _ _ _ h3 => cases h3
        | failed _ _ _ h3 => cases h3
        | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
        | choice k3 _ _ s3 branches _ _ h3 hIn hr3 =>
          injection h3 with _ hBr
          subst hBr
          have hbb3 : s3.bb = 1 := hIn.1
          have hip3 : s3.ip = 0 := hIn.2.1
          have hIso := hIn.2.2.2.1
          have hAbi := hIn.2.2.2.2.1
          have hs3_mem1 : s3.mem 1 = some (.adt 0 (.word64 2)) := by
            have hIso1 := hIso 1 (fun h => by cases h) (by intro h; cases h)
            exact hIso1
          have hs3_perms : s3.perms = defaultOpenPerms := hAbi.2.2.2.2.1
          have hs3_df : s3.df = false := hAbi.2.2.2.1
          have hs3_cs : checkCalleeSavedPreserved s3 = true := by
            rw [hAbi.2.1]
            exact hCalleeSaved0
          have hW0 : checkWritableSlot s3 0 = true := by
            dsimp [checkWritableSlot]
            rw [hs3_perms]
            rfl
          have hStep4 : evalGuardedOpenStep withRestoredBeforeCallOpenBody s3 =
              .step () { s3 with mem := updateSlot s3.mem 0 (some .unit), ip := 1 } := by
            unfold evalGuardedOpenStep
            rw [hbb3, hip3]
            change evalOpenInstr s3 (.mov ⟨0⟩ (.imm .unit)) = _
            dsimp [evalOpenInstr]
            rw [hW0, hbb3, hip3]
            rfl
          cases hr3 with
          | zero => exact ⟨True.intro, fun _ h => by cases h⟩
          | choice _ _ _ _ _ _ _ h4 _ _ =>
            change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | emptyChoice _ _ _ _ h4 _ =>
            change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | terminated _ _ _ h4 =>
            change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | failed _ _ _ h4 =>
            change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep4.symm⟩)
          | step k4 _ s4 _ _ _ h4 hr4 =>
            change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; injection h4 with _ hs4; subst hs4
            let s4' : OpenState := { s3 with mem := updateSlot s3.mem 0 (some .unit), ip := 1 }
            have hs4_mem1 : s4'.mem 1 = some (.adt 0 (.word64 2)) := hs3_mem1
            have hs4_cs : checkCalleeSavedPreserved s4' = true := hs3_cs
            have hGuard4 : (!s4'.df && checkCalleeSavedPreserved s4') = true := by
              change (!s3.df && checkCalleeSavedPreserved s3) = true
              rw [hs3_df, hs3_cs]
              rfl
            have hStep5 : evalGuardedOpenStep withRestoredBeforeCallOpenBody s4' =
                .terminated (.normal .unit) := by
              unfold evalGuardedOpenStep
              dsimp [s4']
              rw [hbb3]
              dsimp [withRestoredBeforeCallOpenBody, evalGuardedOpenTerm]
              change (match !s4'.df && checkCalleeSavedPreserved s4' with
                      | false => StepResult.failed .ub
                      | true => _) = _
              rw [hGuard4]
              dsimp [s4', updateSlot]
              rw [hs3_mem1]
              rfl
            cases hr4 with
            | zero => exact ⟨True.intro, fun _ h => by cases h⟩
            | step _ _ _ _ _ _ h5 _ =>
              change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | choice _ _ _ _ _ _ _ h5 _ _ =>
              change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | emptyChoice _ _ _ _ h5 _ =>
              change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | failed _ _ _ h5 =>
              change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep5.symm⟩)
            | terminated _ _ term h5 =>
              change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5
              injection h5 with hTerm
              subst hTerm
              refine ⟨True.intro, ?_⟩
              intro ret hRet
              injection hRet with h1'
              injection h1' with h2'
              subst h2'
              exact True.intro

/-- **Theorem (b2) (`withUnexposedPrivateTemp_verified`):**
    If a function writes a broken value (`.adt 0 (.word64 99)`, `99 ≥ 4`) into
    an **unexposed caller-private local slot** (`slot 2 ∉ exposedSlots = [1]`)
    while exposed slot `1` continues to satisfy `boundedIdxInv`, the function
    verifies cleanly under `GuardedOpenMachine` and `CallerFrameIsolated`
    preserves slot `1` across the callback! -/
theorem withUnexposedPrivateTemp_verified :
    GuardedOpenSem withUnexposedPrivateTempOpenBody ≤
      EnsuresGuardedRetLibInv boundedIdxInv .usize := by
  refine behaviorOf_le_specOn (M := GuardedOpenMachine) ?_
  intro q out _ hpfx
  cases q with
  | mk s0 steps =>
  cases s0 with
  | mk mem0 perms0 regs0 entryRegs0 df0 bb0 ip0 tySizes0 =>
    have hInit := hpfx.1
    have hReach := hpfx.2
    have hb : bb0 = 0 := hInit.1
    have hip : ip0 = 0 := hInit.2.1
    have hdf : df0 = false := hInit.2.2.1
    have hregs : regs0 = entryRegs0 := hInit.2.2.2.1
    have hperms : perms0 = defaultOpenPerms := hInit.2.2.2.2.1
    subst hb hip hdf hregs hperms
    dsimp at hInit hReach
    cases hInit.2.2.2.2.2.2 with
    | intro v hv =>
      have hv1 : mem0 1 = some v := hv.1
      have hInv : boundedIdxInv tySizes0 (.adt 0) v := hv.2.1
      cases v with
      | word64 _ | boolVal _ | unit | bytes _ _ | stackPtr _ => cases hInv
      | adt adtId inner =>
        cases adtId with
        | succ _ => cases hInv
        | zero =>
          cases inner with
          | boolVal _ | unit | adt _ _ | bytes _ _ | stackPtr _ => cases hInv
          | word64 n =>
            have hLt : n < boundedCap := hInv
            have hDecLt : decide (n < boundedCap) = true := decide_eq_true hLt
            let s0' : OpenState := {
              mem := mem0, perms := defaultOpenPerms, regs := regs0,
              entryRegs := regs0, df := false, bb := 0, ip := 0, tySizes := tySizes0
            }
            have hCalleeSaved0 : checkCalleeSavedPreserved s0' = true :=
              checkCalleeSavedPreserved_refl mem0 defaultOpenPerms regs0 false 0 0 tySizes0
            cases out with
            | mk trOut outcOut =>
            cases hReach with
            | zero => exact ⟨True.intro, fun _ h => by cases h⟩
            | choice _ _ _ _ _ _ _ h1 _ _ => cases h1
            | emptyChoice _ _ _ _ h1 _ => cases h1
            | terminated _ _ _ h1 => cases h1
            | failed _ _ _ h1 => cases h1
            | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
            | step k1 _ s1 _ _ _ h1 hr1 =>
              injection h1 with _ hs1; subst hs1
              let m1 := updateSlot mem0 2 (some (.adt 0 (.word64 99)))
              have hm1_1 : m1 1 = some (.adt 0 (.word64 n)) := hv1
              let s1' : OpenState := { s0' with mem := m1, ip := 1 }
              have hCheck1 : checkCallSiteLibInv s1' [1] [] ⟨0⟩ = true := by
                dsimp [checkCallSiteLibInv, checkWritableSlot,
                       checkExposedSlot, defaultOpenPerms, s1']
                rw [hm1_1]
                change (true && (decide (n < boundedCap) && true)) = true
                rw [hDecLt]
                rfl
              have hStep2 : evalGuardedOpenStep withUnexposedPrivateTempOpenBody s1' =
                  .choice .demonic (GuardedPostCallBranch s1' [] ⟨0⟩ .unit ⟨1⟩) := by
                change evalGuardedOpenTerm s1' (.callExternal [1] [] ⟨0⟩ .unit ⟨1⟩) = _
                dsimp [evalGuardedOpenTerm]
                rw [hCheck1]
              cases hr1 with
              | zero => exact ⟨True.intro, fun _ h => by cases h⟩
              | step _ _ _ _ _ _ h2 _ =>
                change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s1' at h2
                rw [hStep2] at h2; cases h2
              | emptyChoice _ _ _ _ h2 hEmpty =>
                change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s1' at h2
                rw [hStep2] at h2
                injection h2 with _ hBr
                subst hBr
                exact False.elim (hEmpty ⟨_, canonicalPostCallState_satisfies s1' [] ⟨0⟩ .unit ⟨1⟩⟩)
              | terminated _ _ _ h2 =>
                change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s1' at h2
                rw [hStep2] at h2; cases h2
              | failed _ _ _ h2 =>
                change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s1' at h2
                rw [hStep2] at h2; cases h2
              | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep2.symm⟩)
              | choice k2 _ _ s2 branches _ _ h2 hIn hr2 =>
                change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s1' at h2
                rw [hStep2] at h2
                injection h2 with _ hBr
                subst hBr
                have hbb2 : s2.bb = 1 := hIn.1
                have hip2 : s2.ip = 0 := hIn.2.1
                have hIso := hIn.2.2.2.1
                have hAbi := hIn.2.2.2.2.1
                have hs2_mem1 : s2.mem 1 = some (.adt 0 (.word64 n)) := by
                  have hIso1 := hIso 1 (fun h => by cases h) (by intro h; cases h)
                  rw [hIso1]
                  exact hm1_1
                have hs2_perms : s2.perms = defaultOpenPerms := hAbi.2.2.2.2.1
                have hs2_df : s2.df = false := hAbi.2.2.2.1
                have hs2_cs : checkCalleeSavedPreserved s2 = true := by
                  rw [hAbi.2.1]
                  exact hCalleeSaved0
                have hW0 : checkWritableSlot s2 0 = true := by
                  dsimp [checkWritableSlot]
                  rw [hs2_perms]
                  rfl
                have hStep3 : evalGuardedOpenStep withUnexposedPrivateTempOpenBody s2 =
                    .step () { s2 with mem := updateSlot s2.mem 0 (some (.word64 n)), ip := 1 } := by
                  unfold evalGuardedOpenStep
                  rw [hbb2, hip2]
                  change evalOpenInstr s2 (.extractField0 ⟨0⟩ ⟨1⟩) = _
                  dsimp [evalOpenInstr]
                  rw [hW0, hs2_mem1, hbb2, hip2]
                cases hr2 with
                | zero => exact ⟨True.intro, fun _ h => by cases h⟩
                | choice _ _ _ _ _ _ _ h3 _ _ =>
                  change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s2 at h3
                  rw [hStep3] at h3; cases h3
                | emptyChoice _ _ _ _ h3 _ =>
                  change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s2 at h3
                  rw [hStep3] at h3; cases h3
                | terminated _ _ _ h3 =>
                  change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s2 at h3
                  rw [hStep3] at h3; cases h3
                | failed _ _ _ h3 =>
                  change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s2 at h3
                  rw [hStep3] at h3; cases h3
                | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep3.symm⟩)
                | step k3 _ s3 _ _ _ h3 hr3 =>
                  change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s2 at h3
                  rw [hStep3] at h3; injection h3 with _ hs3; subst hs3
                  let s3' : OpenState := { s2 with mem := updateSlot s2.mem 0 (some (.word64 n)), ip := 1 }
                  have hs3_mem1 : s3'.mem 1 = some (.adt 0 (.word64 n)) := hs2_mem1
                  have hs3_cs : checkCalleeSavedPreserved s3' = true := hs2_cs
                  have hGuard3 : (!s3'.df && checkCalleeSavedPreserved s3') = true := by
                    change (!s2.df && checkCalleeSavedPreserved s2) = true
                    rw [hs2_df, hs2_cs]
                    rfl
                  have hStep4 : evalGuardedOpenStep withUnexposedPrivateTempOpenBody s3' =
                      .terminated (.normal (.word64 n)) := by
                    unfold evalGuardedOpenStep
                    dsimp [s3']
                    rw [hbb2]
                    dsimp [withUnexposedPrivateTempOpenBody, evalGuardedOpenTerm]
                    change (match !s3'.df && checkCalleeSavedPreserved s3' with
                            | false => StepResult.failed .ub
                            | true => _) = _
                    rw [hGuard3]
                    dsimp [s3', updateSlot]
                    rw [hs2_mem1]
                    change (match decide (n < boundedCap) with
                            | true => StepResult.terminated (TerminationKind.normal (X86Val.word64 n))
                            | false => StepResult.failed .ub) = _
                    rw [hDecLt]
                  cases hr3 with
                  | zero => exact ⟨True.intro, fun _ h => by cases h⟩
                  | step _ _ _ _ _ _ h4 _ =>
                    change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s3' at h4
                    rw [hStep4] at h4; cases h4
                  | choice _ _ _ _ _ _ _ h4 _ _ =>
                    change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s3' at h4
                    rw [hStep4] at h4; cases h4
                  | emptyChoice _ _ _ _ h4 _ =>
                    change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s3' at h4
                    rw [hStep4] at h4; cases h4
                  | failed _ _ _ h4 =>
                    change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s3' at h4
                    rw [hStep4] at h4; cases h4
                  | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep4.symm⟩)
                  | terminated _ _ term h4 =>
                    change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s3' at h4
                    rw [hStep4] at h4
                    injection h4 with hTerm
                    subst hTerm
                    refine ⟨True.intro, ?_⟩
                    intro ret hRet
                    injection hRet with h1'
                    injection h1' with h2'
                    subst h2'
                    exact True.intro

/-!
### 4.6 Straight-Line Induction Soundness for Arbitrary Safe Callbacks (`open_world_callback_composition_sound`)

Finally, we prove that any caller `body` verified under `GuardedOpenMachine`,
when linked against **any** concrete external callback implementation `cbEnv`
that respects `GuardedPostCallBranch` whenever `CallSiteSatisfiesLibInv` holds
at the call step, executes with **zero Undefined Behavior and zero stuck states**
for every step budget `n : Nat`.

The proof proceeds by straight-line structural induction on the `ReachesPrefix`
derivation (which is indexed by `n : Nat`), requiring **zero step-indexed Iris
logic and zero coinductive types**.
-/

/-- Concrete external callback environment mapping a pre-call state `s` and call
    site parameters `(exposedSlots, exposedMutSlots, dst, retTy, target)` to the
    concrete post-call state returned by the external callback. -/
abbrev CallbackEnv :=
  OpenState → List Nat → List Nat → SlotId → X86Ty → BlockLabel → OpenState

/-- A `CallbackEnv` is well-behaved (`SoundCallbackEnv`) when, for every call
    site where the pre-call check `CallSiteSatisfiesLibInv` holds, the concrete
    post-call state satisfies `GuardedPostCallBranch`. -/
def SoundCallbackEnv (cbEnv : CallbackEnv) : Prop :=
  ∀ s exposedSlots exposedMutSlots dst retTy target,
    CallSiteSatisfiesLibInv s exposedSlots exposedMutSlots dst →
      GuardedPostCallBranch s exposedMutSlots dst retTy target
        (cbEnv s exposedSlots exposedMutSlots dst retTy target)

/-- Concrete execution step when `body` is linked against a specific external
    callback environment `cbEnv`. -/
def evalConcreteCallbackStep (cbEnv : CallbackEnv) (body : OpenBody)
    (s : OpenState) : StepResult OpenState Unit X86Val :=
  match body.blocks[s.bb]? with
  | none => .failed .ub
  | some blk =>
    match blk.instrs[s.ip]? with
    | some instr => evalOpenInstr s instr
    | none =>
      match blk.term with
      | .callExternal exposedSlots exposedMutSlots dst retTy target =>
        match checkCallSiteLibInv s exposedSlots exposedMutSlots dst with
        | true =>
          .step () (cbEnv s exposedSlots exposedMutSlots dst retTy target)
        | false =>
          .failed .ub
      | otherTerm => evalGuardedOpenTerm s otherTerm

def ConcreteCallbackMachine (cbEnv : CallbackEnv) :
    SmallStepMachine OpenBody OpenState Unit X86Val where
  initState := initOpenState
  step body s r := r = evalConcreteCallbackStep cbEnv body s

/-- Simulation lemma by straight-line induction on `ReachesPrefix`: every
    execution prefix of `ConcreteCallbackMachine cbEnv` from `s` is simulated by
    a corresponding execution prefix of `GuardedOpenMachine` with the **exact
    same outcome `out`** (converting each deterministic callback return step into
    a `.choice .demonic` witness step). -/
theorem concrete_to_guarded_reachesPrefix (cbEnv : CallbackEnv)
    (hEnv : SoundCallbackEnv cbEnv) (body : OpenBody) (s0 : OpenState) :
    ∀ n s tr out,
      ReachesPrefix (ConcreteCallbackMachine cbEnv) body s0 n s tr out →
      ∃ tr_g, ReachesPrefix GuardedOpenMachine body s0 n s tr_g out := by
  intro n
  induction n with
  | zero =>
    intro s tr out hReach
    cases hReach with
    | zero => exact ⟨[], ReachesPrefix.zero s⟩
  | succ k ih =>
    intro s tr out hReach
    cases hReach with
    | step _ _ s' ev tr' out hStep hSub =>
      change StepResult.step ev s' = evalConcreteCallbackStep cbEnv body s at hStep
      cases ev
      cases ih s' tr' out hSub with
      | intro tr_g' hSubG =>
        unfold evalConcreteCallbackStep at hStep
        cases hBlk : body.blocks[s.bb]? with
        | none => rw [hBlk] at hStep; cases hStep
        | some blk =>
          rw [hBlk] at hStep
          dsimp at hStep
          cases hInstr : blk.instrs[s.ip]? with
          | some instr =>
            rw [hInstr] at hStep
            dsimp at hStep
            have hGuardedStep : evalGuardedOpenStep body s = .step () s' := by
              unfold evalGuardedOpenStep
              rw [hBlk]
              dsimp
              rw [hInstr]
              exact hStep.symm
            exact ⟨() :: tr_g',
              ReachesPrefix.step k s s' () tr_g' out hGuardedStep.symm hSubG⟩
          | none =>
            rw [hInstr] at hStep
            dsimp at hStep
            cases hTerm : blk.term with
            | callExternal exposedSlots exposedMutSlots dst retTy target =>
              rw [hTerm] at hStep
              dsimp at hStep
              cases hCheck : checkCallSiteLibInv s exposedSlots exposedMutSlots dst with
              | false =>
                rw [hCheck] at hStep
                cases hStep
              | true =>
                rw [hCheck] at hStep
                injection hStep with _ hs'
                have hGuardedStep : evalGuardedOpenStep body s =
                    .choice .demonic (GuardedPostCallBranch s exposedMutSlots dst retTy target) := by
                  unfold evalGuardedOpenStep
                  rw [hBlk]
                  dsimp
                  rw [hInstr]
                  dsimp
                  rw [hTerm]
                  dsimp [evalGuardedOpenTerm]
                  rw [hCheck]
                have hInBranch :
                    GuardedPostCallBranch s exposedMutSlots dst retTy target s' := by
                  rw [hs']
                  exact hEnv s exposedSlots exposedMutSlots dst retTy target hCheck
                exact ⟨tr_g',
                  ReachesPrefix.choice k .demonic s s'
                    (GuardedPostCallBranch s exposedMutSlots dst retTy target)
                    tr_g' out hGuardedStep.symm hInBranch hSubG⟩
            | ret | jmp _ | ud2 | jccBool _ _ _ =>
              rw [hTerm] at hStep
              have hGuardedStep : evalGuardedOpenStep body s = .step () s' := by
                unfold evalGuardedOpenStep
                rw [hBlk]
                dsimp
                rw [hInstr]
                dsimp
                rw [hTerm]
                exact hStep.symm
              exact ⟨() :: tr_g',
                ReachesPrefix.step k s s' () tr_g' out hGuardedStep.symm hSubG⟩
    | choice _ kind _ _ branches _ _ hStep _ _ =>
      change StepResult.choice kind branches = evalConcreteCallbackStep cbEnv body s at hStep
      unfold evalConcreteCallbackStep at hStep
      cases hBlk : body.blocks[s.bb]? with
      | none => rw [hBlk] at hStep; cases hStep
      | some blk =>
        rw [hBlk] at hStep
        dsimp at hStep
        cases hInstr : blk.instrs[s.ip]? with
        | some instr =>
          rw [hInstr] at hStep
          dsimp at hStep
          exact False.elim (evalOpenInstr_not_choice s instr kind branches hStep.symm)
        | none =>
          rw [hInstr] at hStep
          dsimp at hStep
          cases hTerm : blk.term with
          | callExternal exposedSlots exposedMutSlots dst _ _ =>
            rw [hTerm] at hStep
            dsimp at hStep
            cases hCheck : checkCallSiteLibInv s exposedSlots exposedMutSlots dst with
            | false => rw [hCheck] at hStep; cases hStep
            | true => rw [hCheck] at hStep; cases hStep
          | ret =>
            rw [hTerm] at hStep
            exact False.elim (evalRet_not_choice s kind branches hStep.symm)
          | jmp _ => rw [hTerm] at hStep; cases hStep
          | ud2 => rw [hTerm] at hStep; cases hStep
          | jccBool cond fT tT =>
            rw [hTerm] at hStep
            exact False.elim (evalJccBool_not_choice s cond fT tT kind branches hStep.symm)
    | emptyChoice _ kind _ branches hStep _ =>
      change StepResult.choice kind branches = evalConcreteCallbackStep cbEnv body s at hStep
      unfold evalConcreteCallbackStep at hStep
      cases hBlk : body.blocks[s.bb]? with
      | none => rw [hBlk] at hStep; cases hStep
      | some blk =>
        rw [hBlk] at hStep
        dsimp at hStep
        cases hInstr : blk.instrs[s.ip]? with
        | some instr =>
          rw [hInstr] at hStep
          dsimp at hStep
          exact False.elim (evalOpenInstr_not_choice s instr kind branches hStep.symm)
        | none =>
          rw [hInstr] at hStep
          dsimp at hStep
          cases hTerm : blk.term with
          | callExternal exposedSlots exposedMutSlots dst _ _ =>
            rw [hTerm] at hStep
            dsimp at hStep
            cases hCheck : checkCallSiteLibInv s exposedSlots exposedMutSlots dst with
            | false => rw [hCheck] at hStep; cases hStep
            | true => rw [hCheck] at hStep; cases hStep
          | ret =>
            rw [hTerm] at hStep
            exact False.elim (evalRet_not_choice s kind branches hStep.symm)
          | jmp _ => rw [hTerm] at hStep; cases hStep
          | ud2 => rw [hTerm] at hStep; cases hStep
          | jccBool cond fT tT =>
            rw [hTerm] at hStep
            exact False.elim (evalJccBool_not_choice s cond fT tT kind branches hStep.symm)
    | terminated _ _ t hStep =>
      change StepResult.terminated t = evalConcreteCallbackStep cbEnv body s at hStep
      have hGuardedStep : evalGuardedOpenStep body s = .terminated t := by
        unfold evalConcreteCallbackStep at hStep
        unfold evalGuardedOpenStep
        cases hBlk : body.blocks[s.bb]? with
        | none => rw [hBlk] at hStep; cases hStep
        | some blk =>
          rw [hBlk] at hStep
          dsimp at hStep
          dsimp
          cases hInstr : blk.instrs[s.ip]? with
          | some instr =>
            rw [hInstr] at hStep
            dsimp at hStep
            exact hStep.symm
          | none =>
            rw [hInstr] at hStep
            dsimp at hStep
            dsimp
            cases hTerm : blk.term with
            | callExternal exposedSlots exposedMutSlots dst _ _ =>
              rw [hTerm] at hStep
              dsimp at hStep
              cases hCheck : checkCallSiteLibInv s exposedSlots exposedMutSlots dst with
              | false => rw [hCheck] at hStep; cases hStep
              | true => rw [hCheck] at hStep; cases hStep
            | ret | jmp _ | ud2 | jccBool _ _ _ =>
              rw [hTerm] at hStep
              exact hStep.symm
      exact ⟨[], ReachesPrefix.terminated k s t hGuardedStep.symm⟩
    | failed _ _ err hStep =>
      change StepResult.failed err = evalConcreteCallbackStep cbEnv body s at hStep
      have hGuardedStep : evalGuardedOpenStep body s = .failed err := by
        unfold evalConcreteCallbackStep at hStep
        unfold evalGuardedOpenStep
        cases hBlk : body.blocks[s.bb]? with
        | none =>
          rw [hBlk] at hStep
          exact hStep.symm
        | some blk =>
          rw [hBlk] at hStep
          dsimp at hStep
          dsimp
          cases hInstr : blk.instrs[s.ip]? with
          | some instr =>
            rw [hInstr] at hStep
            dsimp at hStep
            exact hStep.symm
          | none =>
            rw [hInstr] at hStep
            dsimp at hStep
            dsimp
            cases hTerm : blk.term with
            | callExternal exposedSlots exposedMutSlots dst retTy target =>
              rw [hTerm] at hStep
              dsimp at hStep
              dsimp [evalGuardedOpenTerm]
              cases hCheck : checkCallSiteLibInv s exposedSlots exposedMutSlots dst with
              | true => rw [hCheck] at hStep; cases hStep
              | false =>
                rw [hCheck] at hStep
                exact hStep.symm
            | ret | jmp _ | ud2 | jccBool _ _ _ =>
              rw [hTerm] at hStep
              exact hStep.symm
      exact ⟨[], ReachesPrefix.failed k s err hGuardedStep.symm⟩
    | noStep _ _ hNo =>
      exact False.elim (hNo ⟨_, rfl⟩)

/-- **Theorem (c) (`open_world_callback_composition_sound`):**
    Any function `body` verified under `GuardedOpenMachine` (`GuardedOpenSem body
    ≤ EnsuresGuardedRetLibInv boundedIdxInv body.retTy`), when executed against
    **any** safe callback environment `cbEnv` (`SoundCallbackEnv cbEnv`) from any
    valid initial state `s0`, is **100% free of Undefined Behavior and stuck
    states (`out.isSafe`)** and satisfies `boundedIdxInv` on its return value at
    every step budget `n : Nat`! -/
theorem open_world_callback_composition_sound (cbEnv : CallbackEnv)
    (hEnv : SoundCallbackEnv cbEnv) (body : OpenBody)
    (hVerified :
      GuardedOpenSem body ≤ EnsuresGuardedRetLibInv boundedIdxInv body.retTy)
    (s0 : OpenState) (hInit : initOpenState body s0)
    (n : Nat) (tr : List Unit) (out : PrefixOutcome X86Val)
    (hReach : ReachesPrefix (ConcreteCallbackMachine cbEnv) body s0 n s0 tr out) :
    out.isSafe ∧
    (∀ ret, out = .terminated (.normal ret) →
      boundedIdxInv s0.tySizes body.retTy ret) := by
  cases concrete_to_guarded_reachesPrefix cbEnv hEnv body s0 n s0 tr out hReach with
  | intro tr_g hReachG =>
    let q : ExecQuery OpenState := { init := s0, steps := n }
    have hStep := hVerified q True.intro
    have hDef : (GuardedOpenSem body q).defined := hStep.1
    have hSafe : out.isSafe := hDef hInit tr_g out hReachG
    refine ⟨hSafe, ?_⟩
    intro ret hTerm
    exact hStep.2 ⟨tr_g, out⟩ ⟨hInit, hReachG⟩ ret hTerm

/-!
### 4.7 Making Open-World External Call Boundaries Structural in `Trusted/StepResult.lean` (`StepResultExt.externalCall`)

Even with `GuardedOpenMachine` above, a language semantics author in `trusted/`
writing `evalGuardedOpenTerm` had to remember to write an `if
checkCallSiteLibInv ... then .choice .demonic ... else .failed .ub` branch. If a
semantics author in `trusted/` accidentally models an external or indirect call
using a plain `.step` or an unguarded `.choice .demonic` without checking
`boundaryInv`, the callback re-entrancy exploit re-emerges.

To make it **structurally impossible** to model an external or indirect call
without specifying both:
1. the positive pre-call boundary invariant (`boundaryInv : Prop`), where
   `¬ boundaryInv` **automatically transitions to `.failed .ub`** in the generic
   step-prefix relation, and
2. the demonic post-call state transition (`demonicPost : State → Obs → Prop`),
   preserving caller-private frames and callee-saved registers while demonically
   havocing exposed mutable state subject to `AdtInv`,

we extend `StepResult` in `Trusted/StepResult.lean` with a dedicated
constructor:
```lean
| externalCall (boundaryInv : Prop) (demonicPost : State → Obs → Prop)
```
and prove that it preserves `TotalStepExt` and `InhabitedExternalAndDemonicExt`
automatically while rejecting `with_temp_invalid` and admitting safe callback
callers!
-/

/-- Structural extension of `StepResult` (`Trusted/StepResult.lean`) with a
    dedicated `.externalCall` constructor that couples the positive pre-call
    boundary obligation (`boundaryInv : Prop`) with the demonic post-call state
    and observation envelope (`demonicPost : State → Obs → Prop`). -/
inductive StepResultExt (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (kind : ChoiceKind) (branches : State → Prop)
  | externalCall (boundaryInv : Prop) (demonicPost : State → Obs → Prop)
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)

structure SmallStepMachineExt (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResultExt State Obs Val → Prop

/-- Step-indexed execution prefix relation for `SmallStepMachineExt`, where
    `.externalCall boundaryInv demonicPost` **structurally enforces** the
    pre-call boundary check:
    - `externalCallOk`: when `boundaryInv` holds and `demonicPost s' obs` holds,
      execution steps to `s'` emitting `obs`;
    - `externalCallUb`: when `¬ boundaryInv` holds, execution transitions
      **immediately to `.failed .ub`**;
    - `externalCallEmpty`: when `boundaryInv` holds but `demonicPost` is empty,
      execution transitions to `.stuck`. -/
inductive ReachesPrefixExt {Prog State Obs Val : Type}
    (M : SmallStepMachineExt Prog State Obs Val) (prog : Prog)
    (init : State) : Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefixExt M prog init 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome Val) :
      M.step prog s (.step obs s') →
      ReachesPrefixExt M prog init n s' tr out →
      ReachesPrefixExt M prog init (n + 1) s (obs :: tr) out
  | choice (n : Nat) (s : State) (kind : ChoiceKind)
      (branches : State → Prop) (s' : State) (tr : List Obs)
      (out : PrefixOutcome Val) :
      M.step prog s (.choice kind branches) →
      branches s' →
      ReachesPrefixExt M prog init n s' tr out →
      ReachesPrefixExt M prog init (n + 1) s tr out
  | emptyChoice (n : Nat) (s : State) (kind : ChoiceKind)
      (branches : State → Prop) :
      M.step prog s (.choice kind branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefixExt M prog init (n + 1) s [] .stuck
  | externalCallOk (n : Nat) (s s' : State) (obs : Obs)
      (boundaryInv : Prop) (demonicPost : State → Obs → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      M.step prog s (.externalCall boundaryInv demonicPost) →
      boundaryInv →
      demonicPost s' obs →
      ReachesPrefixExt M prog init n s' tr out →
      ReachesPrefixExt M prog init (n + 1) s (obs :: tr) out
  | externalCallUb (n : Nat) (s : State)
      (boundaryInv : Prop) (demonicPost : State → Obs → Prop) :
      M.step prog s (.externalCall boundaryInv demonicPost) →
      ¬ boundaryInv →
      ReachesPrefixExt M prog init (n + 1) s [] (.failed .ub)
  | externalCallEmpty (n : Nat) (s : State)
      (boundaryInv : Prop) (demonicPost : State → Obs → Prop) :
      M.step prog s (.externalCall boundaryInv demonicPost) →
      boundaryInv →
      (¬ ∃ s' obs, demonicPost s' obs) →
      ReachesPrefixExt M prog init (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      M.step prog s (.terminated term) →
      ReachesPrefixExt M prog init (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) (err : FailureKind) :
      M.step prog s (.failed err) →
      ReachesPrefixExt M prog init (n + 1) s [] (.failed err)
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step prog s r) →
      ReachesPrefixExt M prog init (n + 1) s [] .stuck

def TotalStepExt {Prog State Obs Val : Type}
    (M : SmallStepMachineExt Prog State Obs Val) : Prop :=
  ∀ prog s, ∃ r, M.step prog s r

/-- Inhabitedness obligation for `SmallStepMachineExt`: every demonic `.choice`
    is inhabited, and every `.externalCall boundaryInv demonicPost` whose
    pre-call `boundaryInv` holds has at least one valid post-call state and
    observation `(s', obs)` satisfying `demonicPost s' obs`. -/
def InhabitedExternalAndDemonicExt {Prog State Obs Val : Type}
    (M : SmallStepMachineExt Prog State Obs Val) : Prop :=
  (∀ prog s branches,
    M.step prog s (.choice .demonic branches) → ∃ s', branches s') ∧
  (∀ prog s boundaryInv demonicPost,
    M.step prog s (.externalCall boundaryInv demonicPost) →
    boundaryInv →
    ∃ s' obs, demonicPost s' obs)

def BehaviorOfExt {Prog State Obs Val : Type}
    (M : SmallStepMachineExt Prog State Obs Val) (prog : Prog)
    (q : ExecQuery State) : Partial (ExecOut Obs Val → Prop) where
  defined :=
    M.initState prog q.init →
      ∀ tr out, ReachesPrefixExt M prog q.init q.steps q.init tr out → out.isSafe
  val _ out :=
    M.initState prog q.init ∧
      ReachesPrefixExt M prog q.init q.steps q.init out.trace out.outcome

def SmallStepMachineExt.toLanguage {Prog State Obs Val : Type}
    (M : SmallStepMachineExt Prog State Obs Val) : Language where
  Prog := Prog
  Query := ExecQuery State
  Out := ExecOut Obs Val
  sem := BehaviorOfExt M

theorem behaviorOfExt_le_specOn {Prog State Obs Val : Type}
    {M : SmallStepMachineExt Prog State Obs Val} {p : Prog}
    {pre : ExecQuery State → Prop}
    {Post : ExecQuery State → ExecOut Obs Val → Prop}
    (h : ∀ q out, pre q →
      (M.initState p q.init ∧
        ReachesPrefixExt M p q.init q.steps q.init out.trace out.outcome) →
      out.outcome.isSafe ∧ Post q out) :
    BehaviorOfExt M p ≤ (M.toLanguage).SpecOn pre Post := by
  intro q hpre
  refine ⟨fun hinit tr oc hreach => (h q ⟨tr, oc⟩ hpre ⟨hinit, hreach⟩).1, ?_⟩
  intro out hval
  exact (h q out hpre hval).2

/-- Lift a sequential `StepResult` to `StepResultExt`. -/
def StepResult.toExt {State Obs Val : Type}
    (r : StepResult State Obs Val) : StepResultExt State Obs Val :=
  match r with
  | .step obs next => .step obs next
  | .choice kind branches => .choice kind branches
  | .terminated term => .terminated term
  | .failed err => .failed err

theorem toExt_not_choice (r : StepResult OpenState Unit X86Val)
    (kind : ChoiceKind) (branches : OpenState → Prop)
    (h : r ≠ .choice kind branches) :
    r.toExt ≠ .choice kind branches := by
  cases r with
  | choice k b =>
    intro hc
    injection hc with hk hb
    subst hk hb
    exact h rfl
  | _ => intro hc; cases hc

theorem toExt_not_ext (r : StepResult OpenState Unit X86Val)
    (boundaryInv : Prop) (demonicPost : OpenState → Unit → Prop) :
    r.toExt ≠ .externalCall boundaryInv demonicPost := by
  cases r <;> (intro hc; cases hc)

theorem evalOpenInstr_toExt_not_choice (s : OpenState) (instr : X86Instr)
    (kind : ChoiceKind) (branches : OpenState → Prop) :
    (evalOpenInstr s instr).toExt ≠ .choice kind branches :=
  toExt_not_choice (evalOpenInstr s instr) kind branches
    (evalOpenInstr_not_choice s instr kind branches)

theorem evalOpenInstr_toExt_not_ext (s : OpenState) (instr : X86Instr)
    (boundaryInv : Prop) (demonicPost : OpenState → Unit → Prop) :
    (evalOpenInstr s instr).toExt ≠ .externalCall boundaryInv demonicPost :=
  toExt_not_ext (evalOpenInstr s instr) boundaryInv demonicPost

/-- Structural open-world terminator semantics using `StepResultExt.externalCall`:
    notice that `.callExternal` does not write a manual `if ... then ... else
    .failed .ub` branch—it simply emits `.externalCall` with the required
    `CallSiteSatisfiesLibInv` and `GuardedPostCallBranch` arguments! -/
def evalStructuralOpenTerm (s : OpenState) (term : OpenTerm) :
    StepResultExt OpenState Unit X86Val :=
  match term with
  | .callExternal exposedSlots exposedMutSlots dst retTy target =>
    .externalCall
      (CallSiteSatisfiesLibInv s exposedSlots exposedMutSlots dst)
      (fun s' _ => GuardedPostCallBranch s exposedMutSlots dst retTy target s')
  | other => (evalGuardedOpenTerm s other).toExt

def evalStructuralOpenStep (body : OpenBody) (s : OpenState) :
    StepResultExt OpenState Unit X86Val :=
  match body.blocks[s.bb]? with
  | none => .failed .ub
  | some blk =>
    match blk.instrs[s.ip]? with
    | some instr => (evalOpenInstr s instr).toExt
    | none => evalStructuralOpenTerm s blk.term

def StructuralOpenMachine :
    SmallStepMachineExt OpenBody OpenState Unit X86Val where
  initState := initOpenState
  step body s r := r = evalStructuralOpenStep body s

def StructuralOpenLang : Language :=
  StructuralOpenMachine.toLanguage

abbrev StructuralOpenSem (body : OpenBody) : StructuralOpenLang.Behavior :=
  StructuralOpenLang.sem body

def EnsuresStructuralRetLibInv (libInv : LibInv) (retTy : X86Ty) :
    StructuralOpenLang.Behavior :=
  StructuralOpenLang.Spec (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      libInv q.init.tySizes retTy ret)

/-- `StructuralOpenMachine` automatically satisfies `TotalStepExt`. -/
theorem structuralOpenMachine_total : TotalStepExt StructuralOpenMachine :=
  fun _ _ => ⟨_, rfl⟩

/-- `StructuralOpenMachine` automatically satisfies `InhabitedExternalAndDemonicExt`. -/
theorem structuralOpenMachine_inhabited :
    InhabitedExternalAndDemonicExt StructuralOpenMachine := by
  refine ⟨?_, ?_⟩
  · intro body s branches hStep
    change StepResultExt.choice ChoiceKind.demonic branches =
      evalStructuralOpenStep body s at hStep
    unfold evalStructuralOpenStep at hStep
    cases hBlk : body.blocks[s.bb]? with
    | none => rw [hBlk] at hStep; cases hStep
    | some blk =>
      rw [hBlk] at hStep
      dsimp at hStep
      cases hInstr : blk.instrs[s.ip]? with
      | some instr =>
        rw [hInstr] at hStep
        dsimp at hStep
        exact False.elim
          (evalOpenInstr_toExt_not_choice s instr .demonic branches hStep.symm)
      | none =>
        rw [hInstr] at hStep
        dsimp at hStep
        cases hTerm : blk.term with
        | callExternal _ _ _ _ _ =>
          rw [hTerm] at hStep
          cases hStep
        | ret =>
          rw [hTerm] at hStep
          exact False.elim
            (toExt_not_choice (evalGuardedOpenTerm s .ret) .demonic branches
              (evalRet_not_choice s .demonic branches) hStep.symm)
        | jmp _ => rw [hTerm] at hStep; cases hStep
        | ud2 => rw [hTerm] at hStep; cases hStep
        | jccBool cond fT tT =>
          rw [hTerm] at hStep
          exact False.elim
            (toExt_not_choice (evalGuardedOpenTerm s (.jccBool cond fT tT)) .demonic branches
              (evalJccBool_not_choice s cond fT tT .demonic branches) hStep.symm)
  · intro body s boundaryInv demonicPost hStep _
    change StepResultExt.externalCall boundaryInv demonicPost =
      evalStructuralOpenStep body s at hStep
    unfold evalStructuralOpenStep at hStep
    cases hBlk : body.blocks[s.bb]? with
    | none => rw [hBlk] at hStep; cases hStep
    | some blk =>
      rw [hBlk] at hStep
      dsimp at hStep
      cases hInstr : blk.instrs[s.ip]? with
      | some instr =>
        rw [hInstr] at hStep
        dsimp at hStep
        exact False.elim
          (evalOpenInstr_toExt_not_ext s instr boundaryInv demonicPost hStep.symm)
      | none =>
        rw [hInstr] at hStep
        dsimp at hStep
        cases hTerm : blk.term with
        | callExternal exposedSlots exposedMutSlots dst retTy target =>
          rw [hTerm] at hStep
          dsimp [evalStructuralOpenTerm] at hStep
          injection hStep with _ hPost
          subst hPost
          exact ⟨canonicalPostCallState s exposedMutSlots dst retTy target, (),
                 canonicalPostCallState_satisfies s exposedMutSlots dst retTy target⟩
        | ret =>
          rw [hTerm] at hStep
          exact False.elim
            (toExt_not_ext (evalGuardedOpenTerm s .ret) boundaryInv demonicPost hStep.symm)
        | jmp _ => rw [hTerm] at hStep; cases hStep
        | ud2 => rw [hTerm] at hStep; cases hStep
        | jccBool cond fT tT =>
          rw [hTerm] at hStep
          exact False.elim
            (toExt_not_ext (evalGuardedOpenTerm s (.jccBool cond fT tT)) boundaryInv demonicPost hStep.symm)

/-- **Structural Rejection of `with_temp_invalid` (`structural_withTempInvalid_rejected`):**
    Under `StructuralOpenMachine`, `ReachesPrefixExt.externalCallUb`
    automatically fires when `¬ CallSiteSatisfiesLibInv` holds at step 2,
    rejecting `with_temp_invalid`! -/
theorem structural_withTempInvalid_rejected :
    ¬ (StructuralOpenSem withTempInvalidOpenBody ≤
        StructuralOpenLang.WellFormed) := by
  intro hWf
  let s0 : OpenState := {
    mem := updateSlot (fun _ => none) 1 (some (.adt 0 (.word64 0)))
  }
  have hInit : initOpenState withTempInvalidOpenBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl,
     ⟨.adt 0 (.word64 0), rfl, Nat.zero_lt_succ 3, by intro h; cases h⟩⟩
  let s1 : OpenState := {
    s0 with
    mem := updateSlot s0.mem 1 (some (.adt 0 (.word64 5)))
    ip := 1
  }
  have hNotInv : ¬ CallSiteSatisfiesLibInv s1 [1] [] ⟨0⟩ := by
    intro hInv
    cases hInv
  have hReach :
      ReachesPrefixExt StructuralOpenMachine withTempInvalidOpenBody s0 2 s0 [()]
        (.failed .ub) :=
    ReachesPrefixExt.step 1 s0 s1 () [] (.failed .ub) rfl
      (ReachesPrefixExt.externalCallUb 0 s1
        (CallSiteSatisfiesLibInv s1 [1] [] ⟨0⟩)
        (fun s' _ => GuardedPostCallBranch s1 [] ⟨0⟩ .unit ⟨1⟩ s')
        rfl hNotInv)
  let q : ExecQuery OpenState := { init := s0, steps := 2 }
  have hStep := hWf q True.intro
  exact hStep.1 hInit [()] (.failed .ub) hReach

/-- **Structural Verification of `with_restored_before_call`
    (`structural_withRestoredBeforeCall_verified`):**
    Safe callback callers that restore `boundedIdxInv` before `.externalCall`
    verify cleanly under `StructuralOpenMachine`. -/
theorem structural_withRestoredBeforeCall_verified :
    StructuralOpenSem withRestoredBeforeCallOpenBody ≤
      EnsuresStructuralRetLibInv boundedIdxInv .unit := by
  refine behaviorOfExt_le_specOn (M := StructuralOpenMachine) ?_
  intro q out _ hpfx
  cases q with
  | mk s0 steps =>
  cases s0 with
  | mk mem0 perms0 regs0 entryRegs0 df0 bb0 ip0 tySizes0 =>
    have hInit := hpfx.1
    have hReach := hpfx.2
    have hb : bb0 = 0 := hInit.1
    have hip : ip0 = 0 := hInit.2.1
    have hdf : df0 = false := hInit.2.2.1
    have hregs : regs0 = entryRegs0 := hInit.2.2.2.1
    have hperms : perms0 = defaultOpenPerms := hInit.2.2.2.2.1
    subst hb hip hdf hregs hperms
    dsimp at hInit hReach
    let s0' : OpenState := {
      mem := mem0, perms := defaultOpenPerms, regs := regs0,
      entryRegs := regs0, df := false, bb := 0, ip := 0, tySizes := tySizes0
    }
    have hCalleeSaved0 : checkCalleeSavedPreserved s0' = true :=
      checkCalleeSavedPreserved_refl mem0 defaultOpenPerms regs0 false 0 0 tySizes0
    cases out with
    | mk trOut outcOut =>
    cases hReach with
    | zero => exact ⟨True.intro, fun _ h => by cases h⟩
    | choice _ _ _ _ _ _ _ h1 _ _ => cases h1
    | emptyChoice _ _ _ _ h1 _ => cases h1
    | externalCallOk _ _ _ _ _ _ _ _ h1 _ _ _ => cases h1
    | externalCallUb _ _ _ _ h1 _ => cases h1
    | externalCallEmpty _ _ _ _ h1 _ _ => cases h1
    | terminated _ _ _ h1 => cases h1
    | failed _ _ _ h1 => cases h1
    | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
    | step k1 _ s1 _ _ _ h1 hr1 =>
      injection h1 with _ hs1; subst hs1
      cases hr1 with
      | zero => exact ⟨True.intro, fun _ h => by cases h⟩
      | choice _ _ _ _ _ _ _ h2 _ _ => cases h2
      | emptyChoice _ _ _ _ h2 _ => cases h2
      | externalCallOk _ _ _ _ _ _ _ _ h2 _ _ _ => cases h2
      | externalCallUb _ _ _ _ h2 _ => cases h2
      | externalCallEmpty _ _ _ _ h2 _ _ => cases h2
      | terminated _ _ _ h2 => cases h2
      | failed _ _ _ h2 => cases h2
      | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
      | step k2 _ s2 _ _ _ h2 hr2 =>
        injection h2 with _ hs2; subst hs2
        let m1 := updateSlot mem0 1 (some (.adt 0 (.word64 5)))
        let m2 := updateSlot m1 1 (some (.adt 0 (.word64 2)))
        let s2' : OpenState := { s0' with mem := m2, ip := 2 }
        have hInv2 : CallSiteSatisfiesLibInv s2' [1] [] ⟨0⟩ := rfl
        cases hr2 with
        | zero => exact ⟨True.intro, fun _ h => by cases h⟩
        | step _ _ _ _ _ _ h3 _ => cases h3
        | choice _ _ _ _ _ _ _ h3 _ _ => cases h3
        | emptyChoice _ _ _ _ h3 _ => cases h3
        | externalCallUb _ _ _ _ h3 hNotInv =>
          injection h3 with hB _
          rw [hB] at hNotInv
          exact False.elim (hNotInv hInv2)
        | externalCallEmpty _ _ _ _ h3 _ hEmpty =>
          injection h3 with _ hPost
          subst hPost
          exact False.elim (hEmpty ⟨_, (),
            canonicalPostCallState_satisfies s2' [] ⟨0⟩ .unit ⟨1⟩⟩)
        | terminated _ _ _ h3 => cases h3
        | failed _ _ _ h3 => cases h3
        | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
        | externalCallOk k3 _ s3 _ _ _ _ _ h3 _ hIn hr3 =>
          injection h3 with _ hPost
          subst hPost
          have hbb3 : s3.bb = 1 := hIn.1
          have hip3 : s3.ip = 0 := hIn.2.1
          have hIso := hIn.2.2.2.1
          have hAbi := hIn.2.2.2.2.1
          have hs3_mem1 : s3.mem 1 = some (.adt 0 (.word64 2)) :=
            hIso 1 (fun h => by cases h) (by intro h; cases h)
          have hs3_perms : s3.perms = defaultOpenPerms := hAbi.2.2.2.2.1
          have hs3_df : s3.df = false := hAbi.2.2.2.1
          have hs3_cs : checkCalleeSavedPreserved s3 = true := by
            rw [hAbi.2.1]
            exact hCalleeSaved0
          have hW0 : checkWritableSlot s3 0 = true := by
            dsimp [checkWritableSlot]
            rw [hs3_perms]
            rfl
          have hStep4 : evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 =
              .step () { s3 with mem := updateSlot s3.mem 0 (some .unit), ip := 1 } := by
            unfold evalStructuralOpenStep
            rw [hbb3, hip3]
            change (evalOpenInstr s3 (.mov ⟨0⟩ (.imm .unit))).toExt = _
            dsimp [evalOpenInstr, StepResult.toExt]
            rw [hW0, hbb3, hip3]
            rfl
          cases hr3 with
          | zero => exact ⟨True.intro, fun _ h => by cases h⟩
          | choice _ _ _ _ _ _ _ h4 _ _ =>
            change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | emptyChoice _ _ _ _ h4 _ =>
            change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | externalCallOk _ _ _ _ _ _ _ _ h4 _ _ _ =>
            change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | externalCallUb _ _ _ _ h4 _ =>
            change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | externalCallEmpty _ _ _ _ h4 _ _ =>
            change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | terminated _ _ _ h4 =>
            change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | failed _ _ _ h4 =>
            change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep4.symm⟩)
          | step k4 _ s4 _ _ _ h4 hr4 =>
            change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; injection h4 with _ hs4; subst hs4
            let s4' : OpenState := { s3 with mem := updateSlot s3.mem 0 (some .unit), ip := 1 }
            have hs4_mem1 : s4'.mem 1 = some (.adt 0 (.word64 2)) := hs3_mem1
            have hs4_cs : checkCalleeSavedPreserved s4' = true := hs3_cs
            have hGuard4 : (!s4'.df && checkCalleeSavedPreserved s4') = true := by
              change (!s3.df && checkCalleeSavedPreserved s3) = true
              rw [hs3_df, hs3_cs]
              rfl
            have hStep5 : evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' =
                .terminated (.normal .unit) := by
              unfold evalStructuralOpenStep
              dsimp [s4']
              rw [hbb3]
              dsimp [withRestoredBeforeCallOpenBody, evalStructuralOpenTerm,
                     evalGuardedOpenTerm, StepResult.toExt]
              change StepResult.toExt
                (match !s4'.df && checkCalleeSavedPreserved s4' with
                 | false => .failed .ub
                 | true => _) = _
              rw [hGuard4]
              dsimp [s4', updateSlot, StepResult.toExt]
              rw [hs3_mem1]
              rfl
            cases hr4 with
            | zero => exact ⟨True.intro, fun _ h => by cases h⟩
            | step _ _ _ _ _ _ h5 _ =>
              change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | choice _ _ _ _ _ _ _ h5 _ _ =>
              change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | emptyChoice _ _ _ _ h5 _ =>
              change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | externalCallOk _ _ _ _ _ _ _ _ h5 _ _ _ =>
              change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | externalCallUb _ _ _ _ h5 _ =>
              change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | externalCallEmpty _ _ _ _ h5 _ _ =>
              change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | failed _ _ _ h5 =>
              change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep5.symm⟩)
            | terminated _ _ term h5 =>
              change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5
              injection h5 with hTerm
              subst hTerm
              refine ⟨True.intro, ?_⟩
              intro ret hRet
              injection hRet with h1'
              injection h1' with h2'
              subst h2'
              exact True.intro


#print axioms naive_getUnchecked_verified
#print axioms naive_withTempInvalid_verified
#print axioms naive_reentrancy_exploit_triggers_ub
#print axioms guardedOpenMachine_total
#print axioms guardedOpenMachine_inhabited
#print axioms withTempInvalid_rejected_under_guarded_call
#print axioms withRestoredBeforeCall_verified
#print axioms withUnexposedPrivateTemp_verified
#print axioms open_world_callback_composition_sound
#print axioms structuralOpenMachine_total
#print axioms structuralOpenMachine_inhabited
#print axioms structural_withTempInvalid_rejected
#print axioms structural_withRestoredBeforeCall_verified

end OpenWorldCallbackFraming

end AnnealReference
