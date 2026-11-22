/-
  DerefPatternsAndArbitrarySelfSoundness.lean

  Kernel-checked Lean v4.34.1 formalization of three core soundness and
  determinism invariants for 2026 `rustc`:
    1. `deref_patterns` + `DerefPure` + `FakeBorrowKind::Deep` decision-tree
       exhaustiveness soundness (`derefPure_decision_tree_sound`),
       single-deref equivalence (`derefPure_unguarded_matches_single_deref`),
       and constructive sharpness counterexamples for impure `Deref`
       (`ce_impure_deref_breaks_exhaustiveness`) and shallow fake borrows
       (`ce_shallow_fake_borrow_guard_breaks_exhaustiveness`).
    2. `rustc_hir_typeck::method::probe` lexicographic `(stepIndex, refKind, candKind)`
       method-probe determinism and minimality (`methodProbe_first_step_wins`,
       `methodProbe_never_picks_non_deref_step`,
       `methodProbe_never_picks_unsafe_raw_deref`) plus constructive sharpness
       counterexamples covering depth-0 autoref vs depth-1 by-value,
       array-to-slice unsizing ordering, and `PickConstraintsForShadowed`
       asymmetry (`ce_shadowing_asymmetry_and_anti_shadowing`).
    3. `core::ops::Receiver` vs `core::ops::DispatchFromDyn` vtable-shim ABI
       soundness (`dispatchFromDyn_vtable_call_sound`) and constructive
       unsoundness counterexamples (`ce_non_layout_isomorphic_receiver_breaks_vtable_call`,
       `ce_repr_c_receiver_rejected_by_dispatch_from_dyn`,
       `ce_zst_type_param_rejected_by_dispatch_from_dyn`).

  TCB Hygiene:
    - Pure constructive Lean 4 core (no external library imports).
    - Total structural definitions only; kernel-checked with only `propext` / `Quot.sound`
      and zero unproved obligations, solver reflection, or unsafe recursion.
-/

namespace RustcDerefAndArbitrarySelf

/-! ## Part 1: `deref_patterns`, `DerefPure` Idempotence, and `FakeBorrowKind::Deep` -/

/-- Outcome of executing a lowered MIR match decision tree. -/
inductive MatchOutcome (R S : Type) where
  | matched (result : R) (finalStore : S)
  | unreachableUB (finalStore : S)
  deriving DecidableEq, Repr

/-- Top-level pattern shape for a scrutinee matched via `deref!()` or `_`. -/
inductive ArmPat (T : Type) where
  | derefPat (pred : T → Bool)
  | wildPat

/-- One match arm in a lowered decision tree, with optional guard. -/
structure MatchArm (S T R : Type) where
  pat : ArmPat T
  guard : Option (S → Bool × S)
  result : R

/-- Operational semantics of `rustc`'s backtracking match decision tree
(`compiler/rustc_mir_build/src/builder/matches/{match_pair,test,mod}.rs`).
Each `deref!(...)` arm allocates its own temporary and invokes `derefOp`
against the current store `σ`, backtracking to remaining arms on pattern or
guard failure and hitting `TerminatorKind::Unreachable` (`unreachableUB`) if
all arms fail. -/
def evalDecisionTree {S V T R : Type}
    (derefOp : S → V → T × S) (σ : S) (v : V) :
    List (MatchArm S T R) → MatchOutcome R S
  | [] => .unreachableUB σ
  | arm :: rest =>
    match arm.pat with
    | .wildPat =>
      match arm.guard with
      | none => .matched arm.result σ
      | some g =>
        let (ok, σ₁) := g σ
        if ok then .matched arm.result σ₁
        else evalDecisionTree derefOp σ₁ v rest
    | .derefPat pred =>
      let (t, σ₁) := derefOp σ v
      if pred t then
        match arm.guard with
        | none => .matched arm.result σ₁
        | some g =>
          let (ok, σ₂) := g σ₁
          if ok then .matched arm.result σ₂
          else evalDecisionTree derefOp σ₂ v rest
      else
        evalDecisionTree derefOp σ₁ v rest

/-- Idealized single-deref semantics for unguarded matches: evaluates
`derefOp` once on the initial store and checks arms against the cached target. -/
def evalSingleDeref {S V T R : Type}
    (derefOp : S → V → T × S) (σ : S) (v : V) (arms : List (MatchArm S T R)) :
    Option R :=
  let t := (derefOp σ v).1
  let rec go : List (MatchArm S T R) → Option R
    | [] => none
    | arm :: rest =>
      match arm.pat with
      | .wildPat => some arm.result
      | .derefPat pred => if pred t then some arm.result else go rest
  go arms

/-- Relational specification of `core::ops::DerefPure`:
`derefOp` stays within a reflexive-transitive store preorder `Eqv`, and all
`Eqv`-related stores produce the exact same dereferenced target value. -/
structure DerefPureRel {S V T : Type} (Eqv : S → S → Prop)
    (derefOp : S → V → T × S) : Prop where
  refl : ∀ σ, Eqv σ σ
  trans : ∀ σ₁ σ₂ σ₃, Eqv σ₁ σ₂ → Eqv σ₂ σ₃ → Eqv σ₁ σ₃
  preservesState : ∀ σ v, Eqv σ (derefOp σ v).2
  targetInvariant : ∀ σ₁ σ₂ v, Eqv σ₁ σ₂ → (derefOp σ₁ v).1 = (derefOp σ₂ v).1

/-- Guard stability invariant enforced by `FakeBorrowKind::Deep`
(`compiler/rustc_mir_build/src/builder/matches/util.rs`): every guard preserves
the store relation `Eqv` (preventing mutation of the scrutinee's deref target). -/
def DeepFakeBorrowGuards {S T R : Type} (Eqv : S → S → Prop) :
    List (MatchArm S T R) → Prop
  | [] => True
  | arm :: rest =>
    (match arm.guard with
     | none => True
     | some g => ∀ σ, Eqv σ (g σ).2) ∧ DeepFakeBorrowGuards Eqv rest

/-- Static exhaustiveness checked by `rustc_pattern_analysis`: for every possible
dereferenced target value `t : T`, some unguarded arm in `arms` matches `t`. -/
def ArmMatchesTarget {S T R : Type} (arm : MatchArm S T R) (t : T) : Prop :=
  arm.guard = none ∧
  match arm.pat with
  | .wildPat => True
  | .derefPat pred => pred t = true

def ExhaustiveForTarget {S T R : Type} (t : T) : List (MatchArm S T R) → Prop
  | [] => False
  | arm :: rest => ArmMatchesTarget arm t ∨ ExhaustiveForTarget t rest

def ExhaustiveArms {S T R : Type} (arms : List (MatchArm S T R)) : Prop :=
  ∀ t : T, ExhaustiveForTarget t arms

/-- Inductive helper: if the current store `σ` is `Eqv`-related to `σ₀`, and the
remaining arms cover `t₀ = (derefOp σ₀ v).1`, then `evalDecisionTree` matches. -/
theorem evalDecisionTree_sound_aux {S V T R : Type}
    {Eqv : S → S → Prop} {derefOp : S → V → T × S}
    (hPure : DerefPureRel Eqv derefOp)
    (σ₀ : S) (v : V) :
    ∀ (arms : List (MatchArm S T R)) (σ : S),
      Eqv σ₀ σ →
      DeepFakeBorrowGuards Eqv arms →
      ExhaustiveForTarget (derefOp σ₀ v).1 arms →
      ∃ r σ', evalDecisionTree derefOp σ v arms = .matched r σ'
  | [], _, _, _, hExh => False.elim hExh
  | arm :: rest, σ, hEqv, ⟨hGuard, hGuardRest⟩, hExh => by
    cases hPat : arm.pat with
    | wildPat =>
      cases hG : arm.guard with
      | none =>
        exact ⟨arm.result, σ, by simp [evalDecisionTree, hPat, hG]⟩
      | some g =>
        simp only [hG] at hGuard
        cases hRes : g σ with
        | mk ok σ₁ =>
          cases ok with
          | true =>
            exact ⟨arm.result, σ₁, by simp [evalDecisionTree, hPat, hG, hRes]⟩
          | false =>
            have hStep : Eqv σ σ₁ := by
              have h := hGuard σ
              rw [hRes] at h
              exact h
            have hEqv₁ : Eqv σ₀ σ₁ := hPure.trans σ₀ σ σ₁ hEqv hStep
            cases hExh with
            | inl hMatch =>
              have hNone := hMatch.1
              rw [hG] at hNone
              cases hNone
            | inr hExhRest =>
              have ⟨r, σ', hRec⟩ :=
                evalDecisionTree_sound_aux hPure σ₀ v rest σ₁ hEqv₁ hGuardRest hExhRest
              exact ⟨r, σ', by simp [evalDecisionTree, hPat, hG, hRes, hRec]⟩
    | derefPat pred =>
      cases hD : derefOp σ v with
      | mk t σ₁ =>
        have hT : (derefOp σ₀ v).1 = t := by
          have h := hPure.targetInvariant σ₀ σ v hEqv
          rw [hD] at h
          exact h
        have hStepD : Eqv σ σ₁ := by
          have h := hPure.preservesState σ v
          rw [hD] at h
          exact h
        have hEqv₁ : Eqv σ₀ σ₁ := hPure.trans σ₀ σ σ₁ hEqv hStepD
        cases hPred : pred t with
        | true =>
          cases hG : arm.guard with
          | none =>
            exact ⟨arm.result, σ₁, by simp [evalDecisionTree, hPat, hD, hPred, hG]⟩
          | some g =>
            simp only [hG] at hGuard
            cases hRes : g σ₁ with
            | mk ok σ₂ =>
              cases ok with
              | true =>
                exact ⟨arm.result, σ₂, by simp [evalDecisionTree, hPat, hD, hPred, hG, hRes]⟩
              | false =>
                have hStepG : Eqv σ₁ σ₂ := by
                  have h := hGuard σ₁
                  rw [hRes] at h
                  exact h
                have hEqv₂ : Eqv σ₀ σ₂ := hPure.trans σ₀ σ₁ σ₂ hEqv₁ hStepG
                cases hExh with
                | inl hMatch =>
                  have hNone := hMatch.1
                  rw [hG] at hNone
                  cases hNone
                | inr hExhRest =>
                  have ⟨r, σ', hRec⟩ :=
                    evalDecisionTree_sound_aux hPure σ₀ v rest σ₂ hEqv₂ hGuardRest hExhRest
                  exact ⟨r, σ', by simp [evalDecisionTree, hPat, hD, hPred, hG, hRes, hRec]⟩
        | false =>
          cases hExh with
          | inl hMatch =>
            have hTrue := hMatch.2
            simp only [hPat, hT, hPred] at hTrue
            cases hTrue
          | inr hExhRest =>
            have ⟨r, σ', hRec⟩ :=
              evalDecisionTree_sound_aux hPure σ₀ v rest σ₁ hEqv₁ hGuardRest hExhRest
            exact ⟨r, σ', by simp [evalDecisionTree, hPat, hD, hPred, hRec]⟩

/-- **Theorem 1 (`derefPure_decision_tree_sound`)**:
If `derefOp` satisfies `DerefPureRel Eqv`, all match guards obey
`DeepFakeBorrowGuards Eqv` (`FakeBorrowKind::Deep`), and `arms` is statically
exhaustive, then the multi-call MIR decision tree never reaches `unreachableUB`. -/
theorem derefPure_decision_tree_sound {S V T R : Type}
    {Eqv : S → S → Prop} {derefOp : S → V → T × S}
    (hPure : DerefPureRel Eqv derefOp)
    (arms : List (MatchArm S T R))
    (hGuards : DeepFakeBorrowGuards Eqv arms)
    (hExh : ExhaustiveArms arms) :
    ∀ (σ : S) (v : V), ∃ r σ', evalDecisionTree derefOp σ v arms = .matched r σ' :=
  fun σ v =>
    evalDecisionTree_sound_aux hPure σ v arms σ (hPure.refl σ) hGuards (hExh (derefOp σ v).1)

/-- Corollary: `unreachableUB` is strictly unreachable under `DerefPureRel` +
`DeepFakeBorrowGuards` + `ExhaustiveArms`. -/
theorem derefPure_decision_tree_no_ub {S V T R : Type}
    {Eqv : S → S → Prop} {derefOp : S → V → T × S}
    (hPure : DerefPureRel Eqv derefOp)
    (arms : List (MatchArm S T R))
    (hGuards : DeepFakeBorrowGuards Eqv arms)
    (hExh : ExhaustiveArms arms)
    (σ : S) (v : V) (σ' : S) :
    evalDecisionTree derefOp σ v arms ≠ .unreachableUB σ' := by
  intro hUb
  have ⟨r, σ'', hM⟩ := derefPure_decision_tree_sound hPure arms hGuards hExh σ v
  rw [hM] at hUb
  cases hUb

/-- Predicate asserting that no arm in the list carries a match guard. -/
def AllUnguarded {S T R : Type} : List (MatchArm S T R) → Prop
  | [] => True
  | arm :: rest => arm.guard = none ∧ AllUnguarded rest

def outcomeResult {R S : Type} : MatchOutcome R S → Option R
  | .matched r _ => some r
  | .unreachableUB _ => none

theorem derefPure_unguarded_matches_single_deref_aux {S V T R : Type}
    {Eqv : S → S → Prop} {derefOp : S → V → T × S}
    (hPure : DerefPureRel Eqv derefOp)
    (σ₀ : S) (v : V) :
    ∀ (arms : List (MatchArm S T R)) (σ : S),
      Eqv σ₀ σ →
      AllUnguarded arms →
      outcomeResult (evalDecisionTree derefOp σ v arms) =
        evalSingleDeref.go (derefOp σ₀ v).1 arms
  | [], _, _, _ => rfl
  | arm :: rest, σ, hEqv, ⟨hG, hRest⟩ => by
    cases hPat : arm.pat with
    | wildPat =>
      simp [evalDecisionTree, evalSingleDeref.go, outcomeResult, hPat, hG]
    | derefPat pred =>
      cases hD : derefOp σ v with
      | mk t σ₁ =>
        have hT : (derefOp σ₀ v).1 = t := by
          have h := hPure.targetInvariant σ₀ σ v hEqv
          rw [hD] at h
          exact h
        have hStepD : Eqv σ σ₁ := by
          have h := hPure.preservesState σ v
          rw [hD] at h
          exact h
        have hEqv₁ : Eqv σ₀ σ₁ := hPure.trans σ₀ σ σ₁ hEqv hStepD
        cases hPred : pred t with
        | true =>
          simp [evalDecisionTree, evalSingleDeref.go, outcomeResult, hPat, hD, hT, hPred, hG]
        | false =>
          have hRec := derefPure_unguarded_matches_single_deref_aux hPure σ₀ v rest σ₁ hEqv₁ hRest
          rw [hT] at hRec
          simp only [evalDecisionTree, evalSingleDeref.go, hPat, hD, hT, hPred]
          exact hRec

/-- **Theorem 1b (`derefPure_unguarded_matches_single_deref`)**:
For unguarded matches over a `DerefPure` smart pointer, repeated `Deref::deref`
calls in `rustc`'s backtracking automaton always select the exact same arm
result as a single cached `Deref::deref` call. -/
theorem derefPure_unguarded_matches_single_deref {S V T R : Type}
    {Eqv : S → S → Prop} {derefOp : S → V → T × S}
    (hPure : DerefPureRel Eqv derefOp)
    (arms : List (MatchArm S T R))
    (hUnguarded : AllUnguarded arms)
    (σ : S) (v : V) :
    outcomeResult (evalDecisionTree derefOp σ v arms) =
      evalSingleDeref derefOp σ v arms :=
  derefPure_unguarded_matches_single_deref_aux hPure σ v arms σ (hPure.refl σ) hUnguarded

/-! ### Sharpness Counterexamples for Part 1 -/

/-- Stateful impure `Deref` toggling a `Cell<Bool>` on every deref call
(exact model of `LyingToggle` in `probe_deref_patterns_and_arbitrary_self.py`). -/
def toggleDeref : Bool → Unit → Bool × Bool
  | s, () => (s, !s)

/-- Exhaustive unguarded 2-arm boolean match: `[deref!(true) => 1, deref!(false) => 2]`. -/
def boolDerefArms : List (MatchArm Bool Bool Nat) :=
  [ { pat := .derefPat (fun b => b == true),  guard := none, result := 1 }
  , { pat := .derefPat (fun b => b == false), guard := none, result := 2 } ]

/-- **Sharpness Counterexample 1a (`ce_impure_deref_breaks_exhaustiveness`)**:
Dropping `DerefPure` alone breaks decision-tree exhaustiveness: `boolDerefArms`
is statically exhaustive and has no guards, yet `toggleDeref` drives
`evalDecisionTree` straight into `unreachableUB`. -/
theorem ce_impure_deref_breaks_exhaustiveness :
    ExhaustiveArms boolDerefArms ∧
    DeepFakeBorrowGuards Eq boolDerefArms ∧
    evalDecisionTree toggleDeref false () boolDerefArms = .unreachableUB false := by
  refine ⟨?_, ?_, rfl⟩
  · intro t
    cases t with
    | false => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | true => exact Or.inl ⟨rfl, rfl⟩
  · exact ⟨trivial, trivial, trivial⟩

/-- Pure `Box<bool>` dereference satisfying `DerefPureRel Eq`. -/
def pureBoxDeref : Bool → Unit → Bool × Bool
  | s, () => (s, s)

theorem pureBoxDeref_is_pure : DerefPureRel Eq pureBoxDeref where
  refl := fun _ => rfl
  trans := fun _ _ _ h1 h2 => Eq.trans h1 h2
  preservesState := fun _ _ => rfl
  targetInvariant := fun _ _ _ h => by subst h; rfl

/-- Exact formalization of the `compiler/rustc_mir_build/src/builder/matches/util.rs`
guard-mutation exploit when only shallow fake borrows are taken:
`match b { deref!(true) => 1, _ if { *b = true; false } => 2, deref!(false) => 3 }`. -/
def mutatingGuardArms : List (MatchArm Bool Bool Nat) :=
  [ { pat := .derefPat (fun b => b == true),  guard := none, result := 1 }
  , { pat := .wildPat, guard := some (fun _ => (false, true)), result := 2 }
  , { pat := .derefPat (fun b => b == false), guard := none, result := 3 } ]

/-- **Sharpness Counterexample 1b (`ce_shallow_fake_borrow_guard_breaks_exhaustiveness`)**:
Even with a strictly pure `DerefPure` implementation (`pureBoxDeref`), omitting
`FakeBorrowKind::Deep` lets a failing match guard mutate the pointee and drive
an exhaustive match into `unreachableUB`. -/
theorem ce_shallow_fake_borrow_guard_breaks_exhaustiveness :
    DerefPureRel Eq pureBoxDeref ∧
    ExhaustiveArms mutatingGuardArms ∧
    evalDecisionTree pureBoxDeref false () mutatingGuardArms = .unreachableUB true := by
  refine ⟨pureBoxDeref_is_pure, ?_, rfl⟩
  intro t
  cases t with
  | false => exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  | true => exact Or.inl ⟨rfl, rfl⟩


/-! ## Part 2: `rustc_hir_typeck::method::probe` Lexicographic Determinism & Shadowing -/

/-- Per-step receiver adjustment order in `ProbeContext::pick_all_method`
(`compiler/rustc_hir_typeck/src/method/probe.rs:1346-1479`). -/
inductive RefKind where
  | byVal
  | sharedRef
  | mutRef
  | constPtr
  | reborrowPin
  deriving DecidableEq, Repr

def RefKind.rank : RefKind → Nat
  | .byVal       => 0
  | .sharedRef   => 1
  | .mutRef      => 2
  | .constPtr    => 3
  | .reborrowPin => 4

/-- Inherent impl candidates are searched strictly before extension trait
candidates at each `(step, refKind)` (`probe.rs:1750-1764`). -/
inductive CandKind where
  | inherent
  | extension
  deriving DecidableEq, Repr

def CandKind.rank : CandKind → Nat
  | .inherent  => 0
  | .extension => 1

/-- One `CandidateStep` produced by `method_autoderef_steps` (`probe.rs:706-811`). -/
structure ProbeStep where
  ty : Nat
  derefDepth : Nat
  reachableViaDeref : Bool
  fromUnsafeDeref : Bool
  unsize : Bool
  isMutRawPtr : Bool
  deriving DecidableEq, Repr

/-- One assembled method candidate (`probe.rs:115-145`). -/
structure MethodCandidate where
  id : Nat
  kind : CandKind
  expectedTy : Nat
  expectedRef : RefKind
  receiverSteps : Nat
  deriving DecidableEq, Repr

/-- Whether a `RefKind` adjustment is permitted on `step` (`probe.rs:1596, 1721-1727`). -/
def stepAllowsRefKind (step : ProbeStep) : RefKind → Bool
  | .byVal       => !step.unsize
  | .sharedRef   => true
  | .mutRef      => true
  | .constPtr    => !step.unsize && step.isMutRawPtr
  | .reborrowPin => !step.unsize

/-- Whether a candidate matches `(step, rk, ck)` (`probe.rs:1589-1765`). -/
def candidateMatches (step : ProbeStep) (rk : RefKind) (ck : CandKind)
    (c : MethodCandidate) : Bool :=
  stepAllowsRefKind step rk &&
  (c.kind == ck) &&
  (c.expectedTy == step.ty) &&
  (c.expectedRef == rk)

/-- Anti-shadowing filter (`PickConstraintsForShadowed::candidate_may_shadow`,
`probe.rs:190-215`): matches inherent candidates with strictly deeper
`receiverSteps` and distinct `id`. -/
def candidateMayShadow (shadower : MethodCandidate) (c : MethodCandidate) : Bool :=
  (c.id != shadower.id) &&
  (c.kind == .inherent) &&
  (shadower.receiverSteps < c.receiverSteps)

/-- Selected method pick carrying its exact probe coordinates. -/
structure MethodPick where
  stepIdx : Nat
  step : ProbeStep
  refKind : RefKind
  cand : MethodCandidate
  deriving DecidableEq, Repr

inductive ProbeOutcome where
  | picked (pick : MethodPick)
  | ambiguity
  | notFound
  deriving DecidableEq, Repr

/-- Pick unique matching candidate for fixed `(step, rk, ck)` or report ambiguity. -/
def considerCandidates (step : ProbeStep) (rk : RefKind) (ck : CandKind)
    (cands : List MethodCandidate) (stepIdx : Nat) : ProbeOutcome :=
  match cands.filter (candidateMatches step rk ck) with
  | [] => .notFound
  | [c] => .picked { stepIdx := stepIdx, step := step, refKind := rk, cand := c }
  | _ :: _ :: _ => .ambiguity

/-- Search `.inherent` strictly before `.extension` (`probe.rs:1750-1764`). -/
def pickMethod (step : ProbeStep) (rk : RefKind)
    (cands : List MethodCandidate) (stepIdx : Nat) : ProbeOutcome :=
  match considerCandidates step rk .inherent cands stepIdx with
  | .notFound => considerCandidates step rk .extension cands stepIdx
  | res => res

/-- Check whether `shadower` shadows an inherent autoref'd method at `targetRk`
(`check_for_shadowed_autorefd_method`, `probe.rs:1496-1581`). -/
def hasShadowedAutoref (shadower : MethodCandidate) (step : ProbeStep)
    (targetRk : RefKind) (cands : List MethodCandidate) : Bool :=
  (cands.filter (fun c =>
    candidateMatches step targetRk .inherent c && candidateMayShadow shadower c)).isEmpty == false

/-- Exact per-step probe order (`pick_all_method`, `probe.rs:1375-1478`):
`byVal` -> (anti-shadow check on `sharedRef`,`mutRef`) ->
`sharedRef` -> (anti-shadow check on `mutRef`) ->
`mutRef` -> `constPtr` -> `reborrowPin`. -/
def pickAtStep (step : ProbeStep) (cands : List MethodCandidate)
    (arbitrarySelfTypes : Bool) (stepIdx : Nat) : ProbeOutcome :=
  match pickMethod step .byVal cands stepIdx with
  | .picked p =>
    if arbitrarySelfTypes && p.cand.kind == .inherent &&
       (hasShadowedAutoref p.cand step .sharedRef cands ||
        hasShadowedAutoref p.cand step .mutRef cands) then
      .ambiguity
    else
      .picked p
  | .ambiguity => .ambiguity
  | .notFound =>
    match pickMethod step .sharedRef cands stepIdx with
    | .picked p =>
      if arbitrarySelfTypes && p.cand.kind == .inherent &&
         hasShadowedAutoref p.cand step .mutRef cands then
        .ambiguity
      else
        .picked p
    | .ambiguity => .ambiguity
    | .notFound =>
      match pickMethod step .mutRef cands stepIdx with
      | .notFound =>
        match pickMethod step .constPtr cands stepIdx with
        | .notFound => pickMethod step .reborrowPin cands stepIdx
        | res => res
      | res => res

/-- Eligibility predicate matching `probe.rs:1356, 1361`. -/
def stepEligible (step : ProbeStep) : Bool :=
  step.reachableViaDeref && !step.fromUnsafeDeref

/-- Walk `steps` in order starting at index `baseIdx`, skipping ineligible steps,
and return the first non-`.notFound` outcome (`Iterator::find_map` in `probe.rs:1363`). -/
def probePickAux (cands : List MethodCandidate) (arbitrarySelfTypes : Bool) :
    Nat → List ProbeStep → ProbeOutcome
  | _, [] => .notFound
  | idx, step :: rest =>
    if stepEligible step then
      match pickAtStep step cands arbitrarySelfTypes idx with
      | .notFound => probePickAux cands arbitrarySelfTypes (idx + 1) rest
      | res => res
    else
      probePickAux cands arbitrarySelfTypes (idx + 1) rest

def probePick (steps : List ProbeStep) (cands : List MethodCandidate)
    (arbitrarySelfTypes : Bool) : ProbeOutcome :=
  probePickAux cands arbitrarySelfTypes 0 steps

/-- Lexicographic priority order on `(stepIdx, refKind, candKind)`:
smaller key has strictly higher precedence. -/
def ProbePriorityLe (idx₁ : Nat) (rk₁ : RefKind) (ck₁ : CandKind)
    (idx₂ : Nat) (rk₂ : RefKind) (ck₂ : CandKind) : Prop :=
  idx₁ < idx₂ ∨
  (idx₁ = idx₂ ∧ (rk₁.rank < rk₂.rank ∨ (rk₁.rank = rk₂.rank ∧ ck₁.rank ≤ ck₂.rank)))

/-- Helper: if `considerCandidates` returns `.notFound`, no candidate in `cands` matches. -/
theorem considerCandidates_notFound_no_match
    (step : ProbeStep) (rk : RefKind) (ck : CandKind)
    (cands : List MethodCandidate) (stepIdx : Nat)
    (hNF : considerCandidates step rk ck cands stepIdx = .notFound)
    (c : MethodCandidate) (hMem : c ∈ cands) :
    candidateMatches step rk ck c = false := by
  unfold considerCandidates at hNF
  cases hF : cands.filter (candidateMatches step rk ck) with
  | nil =>
    cases hM : candidateMatches step rk ck c with
    | false => rfl
    | true =>
      have hIn : c ∈ cands.filter (candidateMatches step rk ck) :=
        List.mem_filter.mpr ⟨hMem, hM⟩
      rw [hF] at hIn
      cases hIn
  | cons a tl =>
    cases tl with
    | nil => rw [hF] at hNF; cases hNF
    | cons b tl2 => rw [hF] at hNF; cases hNF

/-- Helper: if `considerCandidates` returns `.picked p`, then `p` carries the exact
coordinates and matches. -/
theorem considerCandidates_picked_spec
    (step : ProbeStep) (rk : RefKind) (ck : CandKind)
    (cands : List MethodCandidate) (stepIdx : Nat) (p : MethodPick)
    (hP : considerCandidates step rk ck cands stepIdx = .picked p) :
    p.stepIdx = stepIdx ∧ p.step = step ∧ p.refKind = rk ∧ p.cand.kind = ck ∧
    p.cand ∈ cands ∧ candidateMatches step rk ck p.cand = true := by
  unfold considerCandidates at hP
  cases hF : cands.filter (candidateMatches step rk ck) with
  | nil => rw [hF] at hP; cases hP
  | cons a tl =>
    cases tl with
    | nil =>
      rw [hF] at hP
      cases hP
      have hIn : a ∈ cands.filter (candidateMatches step rk ck) := by rw [hF]; exact List.mem_cons_self
      have ⟨hMem, hMatch⟩ := List.mem_filter.mp hIn
      have hKind : a.kind = ck := by
        unfold candidateMatches at hMatch
        simp only [Bool.and_eq_true, beq_iff_eq] at hMatch
        exact hMatch.1.1.2
      exact ⟨rfl, rfl, rfl, hKind, hMem, hMatch⟩
    | cons b tl2 => rw [hF] at hP; cases hP

/-- Helper: if `pickMethod` returns `.notFound`, neither inherent nor extension matches. -/
theorem pickMethod_notFound_no_match
    (step : ProbeStep) (rk : RefKind)
    (cands : List MethodCandidate) (stepIdx : Nat)
    (hNF : pickMethod step rk cands stepIdx = .notFound)
    (c : MethodCandidate) (hMem : c ∈ cands) :
    candidateMatches step rk c.kind c = false := by
  unfold pickMethod at hNF
  cases hInh : considerCandidates step rk .inherent cands stepIdx with
  | notFound =>
    rw [hInh] at hNF
    cases hK : c.kind with
    | inherent => exact considerCandidates_notFound_no_match step rk .inherent cands stepIdx hInh c hMem
    | extension => exact considerCandidates_notFound_no_match step rk .extension cands stepIdx hNF c hMem
  | picked _ => rw [hInh] at hNF; cases hNF
  | ambiguity => rw [hInh] at hNF; cases hNF

/-- Helper: if `pickMethod` returns `.picked p`, then `p` beats or ties any candidate
at `(step, rk)` in `CandKind.rank`. -/
theorem pickMethod_picked_spec
    (step : ProbeStep) (rk : RefKind)
    (cands : List MethodCandidate) (stepIdx : Nat) (p : MethodPick)
    (hP : pickMethod step rk cands stepIdx = .picked p) :
    p.stepIdx = stepIdx ∧ p.step = step ∧ p.refKind = rk ∧
    p.cand ∈ cands ∧ candidateMatches step rk p.cand.kind p.cand = true ∧
    (∀ c ∈ cands, candidateMatches step rk c.kind c = true → p.cand.kind.rank ≤ c.kind.rank) := by
  unfold pickMethod at hP
  cases hInh : considerCandidates step rk .inherent cands stepIdx with
  | picked q =>
    rw [hInh] at hP
    cases hP
    have ⟨hI, hS, hR, hK, hMem, hMatch⟩ :=
      considerCandidates_picked_spec step rk .inherent cands stepIdx p hInh
    refine ⟨hI, hS, hR, hMem, by rw [hK]; exact hMatch, ?_⟩
    intro c _ _
    rw [hK]
    exact Nat.zero_le _
  | ambiguity => rw [hInh] at hP; cases hP
  | notFound =>
    rw [hInh] at hP
    have ⟨hI, hS, hR, hK, hMem, hMatch⟩ :=
      considerCandidates_picked_spec step rk .extension cands stepIdx p hP
    refine ⟨hI, hS, hR, hMem, by rw [hK]; exact hMatch, ?_⟩
    intro c hCMem hCMatch
    cases hCK : c.kind with
    | inherent =>
      rw [hCK] at hCMatch
      have hNo := considerCandidates_notFound_no_match step rk .inherent cands stepIdx hInh c hCMem
      rw [hNo] at hCMatch
      cases hCMatch
    | extension =>
      rw [hK]
      exact Nat.le_refl _

/-- Helper: if `pickAtStep` returns `.notFound`, no candidate matches ANY `RefKind` on `step`. -/
theorem pickAtStep_notFound_no_match
    (step : ProbeStep) (cands : List MethodCandidate)
    (arbitrarySelfTypes : Bool) (stepIdx : Nat)
    (hNF : pickAtStep step cands arbitrarySelfTypes stepIdx = .notFound)
    (rk : RefKind) (c : MethodCandidate) (hMem : c ∈ cands) :
    candidateMatches step rk c.kind c = false := by
  unfold pickAtStep at hNF
  cases h0 : pickMethod step .byVal cands stepIdx with
  | picked p =>
    simp only [h0] at hNF
    cases hC : (arbitrarySelfTypes && p.cand.kind == .inherent &&
        (hasShadowedAutoref p.cand step .sharedRef cands ||
         hasShadowedAutoref p.cand step .mutRef cands)) <;> simp [hC] at hNF
  | ambiguity => simp only [h0] at hNF; cases hNF
  | notFound =>
    simp only [h0] at hNF
    cases h1 : pickMethod step .sharedRef cands stepIdx with
    | picked p =>
      simp only [h1] at hNF
      cases hC : (arbitrarySelfTypes && p.cand.kind == .inherent &&
          hasShadowedAutoref p.cand step .mutRef cands) <;> simp [hC] at hNF
    | ambiguity => simp only [h1] at hNF; cases hNF
    | notFound =>
      simp only [h1] at hNF
      cases h2 : pickMethod step .mutRef cands stepIdx with
      | picked _ => simp only [h2] at hNF; cases hNF
      | ambiguity => simp only [h2] at hNF; cases hNF
      | notFound =>
        simp only [h2] at hNF
        cases h3 : pickMethod step .constPtr cands stepIdx with
        | picked _ => simp only [h3] at hNF; cases hNF
        | ambiguity => simp only [h3] at hNF; cases hNF
        | notFound =>
          simp only [h3] at hNF
          cases rk with
          | byVal       => exact pickMethod_notFound_no_match step .byVal cands stepIdx h0 c hMem
          | sharedRef   => exact pickMethod_notFound_no_match step .sharedRef cands stepIdx h1 c hMem
          | mutRef      => exact pickMethod_notFound_no_match step .mutRef cands stepIdx h2 c hMem
          | constPtr    => exact pickMethod_notFound_no_match step .constPtr cands stepIdx h3 c hMem
          | reborrowPin => exact pickMethod_notFound_no_match step .reborrowPin cands stepIdx hNF c hMem

/-- Helper: if `pickAtStep` returns `.picked p`, `p` is lexicographically minimal
over `(refKind, candKind)` on `step`. -/
theorem pickAtStep_picked_spec
    (step : ProbeStep) (cands : List MethodCandidate)
    (arbitrarySelfTypes : Bool) (stepIdx : Nat) (p : MethodPick)
    (hP : pickAtStep step cands arbitrarySelfTypes stepIdx = .picked p) :
    p.stepIdx = stepIdx ∧ p.step = step ∧
    p.cand ∈ cands ∧ candidateMatches step p.refKind p.cand.kind p.cand = true ∧
    (∀ rk c, c ∈ cands → candidateMatches step rk c.kind c = true →
      p.refKind.rank < rk.rank ∨ (p.refKind.rank = rk.rank ∧ p.cand.kind.rank ≤ c.kind.rank)) := by
  unfold pickAtStep at hP
  cases h0 : pickMethod step .byVal cands stepIdx with
  | ambiguity => simp only [h0] at hP; cases hP
  | picked q =>
    simp only [h0] at hP
    cases hC : (arbitrarySelfTypes && q.cand.kind == .inherent &&
        (hasShadowedAutoref q.cand step .sharedRef cands ||
         hasShadowedAutoref q.cand step .mutRef cands)) with
    | true => simp [hC] at hP
    | false =>
      simp only [hC, Bool.false_eq_true, ↓reduceIte, ProbeOutcome.picked.injEq] at hP
      subst hP
      have ⟨hI, hS, hR, hMem, hMatch, hMin⟩ :=
        pickMethod_picked_spec step .byVal cands stepIdx q h0
      refine ⟨hI, hS, hMem, by rw [hR]; exact hMatch, ?_⟩
      intro rk c hCMem hCMatch
      cases rk with
      | byVal => exact Or.inr ⟨by rw [hR], hMin c hCMem hCMatch⟩
      | sharedRef => exact Or.inl (by rw [hR]; exact Nat.zero_lt_succ 0)
      | mutRef => exact Or.inl (by rw [hR]; exact Nat.zero_lt_succ 1)
      | constPtr => exact Or.inl (by rw [hR]; exact Nat.zero_lt_succ 2)
      | reborrowPin => exact Or.inl (by rw [hR]; exact Nat.zero_lt_succ 3)
  | notFound =>
    simp only [h0] at hP
    cases h1 : pickMethod step .sharedRef cands stepIdx with
    | ambiguity => simp only [h1] at hP; cases hP
    | picked q =>
      simp only [h1] at hP
      cases hC : (arbitrarySelfTypes && q.cand.kind == .inherent &&
          hasShadowedAutoref q.cand step .mutRef cands) with
      | true => simp [hC] at hP
      | false =>
        simp only [hC, Bool.false_eq_true, ↓reduceIte, ProbeOutcome.picked.injEq] at hP
        subst hP
        have ⟨hI, hS, hR, hMem, hMatch, hMin⟩ :=
          pickMethod_picked_spec step .sharedRef cands stepIdx q h1
        refine ⟨hI, hS, hMem, by rw [hR]; exact hMatch, ?_⟩
        intro rk c hCMem hCMatch
        cases rk with
        | byVal =>
          have hNo := pickMethod_notFound_no_match step .byVal cands stepIdx h0 c hCMem
          rw [hNo] at hCMatch; cases hCMatch
        | sharedRef => exact Or.inr ⟨by rw [hR], hMin c hCMem hCMatch⟩
        | mutRef => exact Or.inl (by rw [hR]; exact Nat.lt_succ_self 1)
        | constPtr => exact Or.inl (by rw [hR]; exact Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_succ_self 2))
        | reborrowPin =>
          exact Or.inl (by rw [hR]; exact Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_succ_self 2)) (Nat.lt_succ_self 3))
    | notFound =>
      simp only [h1] at hP
      cases h2 : pickMethod step .mutRef cands stepIdx with
      | ambiguity => simp only [h2] at hP; cases hP
      | picked q =>
        simp only [h2, ProbeOutcome.picked.injEq] at hP; subst hP
        have ⟨hI, hS, hR, hMem, hMatch, hMin⟩ :=
          pickMethod_picked_spec step .mutRef cands stepIdx q h2
        refine ⟨hI, hS, hMem, by rw [hR]; exact hMatch, ?_⟩
        intro rk c hCMem hCMatch
        cases rk with
        | byVal =>
          have hNo := pickMethod_notFound_no_match step .byVal cands stepIdx h0 c hCMem
          rw [hNo] at hCMatch; cases hCMatch
        | sharedRef =>
          have hNo := pickMethod_notFound_no_match step .sharedRef cands stepIdx h1 c hCMem
          rw [hNo] at hCMatch; cases hCMatch
        | mutRef => exact Or.inr ⟨by rw [hR], hMin c hCMem hCMatch⟩
        | constPtr => exact Or.inl (by rw [hR]; exact Nat.lt_succ_self 2)
        | reborrowPin => exact Or.inl (by rw [hR]; exact Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_succ_self 3))
      | notFound =>
        simp only [h2] at hP
        cases h3 : pickMethod step .constPtr cands stepIdx with
        | ambiguity => simp only [h3] at hP; cases hP
        | picked q =>
          simp only [h3, ProbeOutcome.picked.injEq] at hP; subst hP
          have ⟨hI, hS, hR, hMem, hMatch, hMin⟩ :=
            pickMethod_picked_spec step .constPtr cands stepIdx q h3
          refine ⟨hI, hS, hMem, by rw [hR]; exact hMatch, ?_⟩
          intro rk c hCMem hCMatch
          cases rk with
          | byVal =>
            have hNo := pickMethod_notFound_no_match step .byVal cands stepIdx h0 c hCMem
            rw [hNo] at hCMatch; cases hCMatch
          | sharedRef =>
            have hNo := pickMethod_notFound_no_match step .sharedRef cands stepIdx h1 c hCMem
            rw [hNo] at hCMatch; cases hCMatch
          | mutRef =>
            have hNo := pickMethod_notFound_no_match step .mutRef cands stepIdx h2 c hCMem
            rw [hNo] at hCMatch; cases hCMatch
          | constPtr => exact Or.inr ⟨by rw [hR], hMin c hCMem hCMatch⟩
          | reborrowPin => exact Or.inl (by rw [hR]; exact Nat.lt_succ_self 3)
        | notFound =>
          simp only [h3] at hP
          have ⟨hI, hS, hR, hMem, hMatch, hMin⟩ :=
            pickMethod_picked_spec step .reborrowPin cands stepIdx p hP
          refine ⟨hI, hS, hMem, by rw [hR]; exact hMatch, ?_⟩
          intro rk c hCMem hCMatch
          cases rk with
          | byVal =>
            have hNo := pickMethod_notFound_no_match step .byVal cands stepIdx h0 c hCMem
            rw [hNo] at hCMatch; cases hCMatch
          | sharedRef =>
            have hNo := pickMethod_notFound_no_match step .sharedRef cands stepIdx h1 c hCMem
            rw [hNo] at hCMatch; cases hCMatch
          | mutRef =>
            have hNo := pickMethod_notFound_no_match step .mutRef cands stepIdx h2 c hCMem
            rw [hNo] at hCMatch; cases hCMatch
          | constPtr =>
            have hNo := pickMethod_notFound_no_match step .constPtr cands stepIdx h3 c hCMem
            rw [hNo] at hCMatch; cases hCMatch
          | reborrowPin => exact Or.inr ⟨by rw [hR], hMin c hCMem hCMatch⟩

/-- Total structural indexed lookup in `List`. -/
def listGetOpt {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGetOpt xs n

theorem probePickAux_spec (cands : List MethodCandidate) (arbitrarySelfTypes : Bool) :
    ∀ (steps : List ProbeStep) (baseIdx : Nat) (p : MethodPick),
      probePickAux cands arbitrarySelfTypes baseIdx steps = .picked p →
      stepEligible p.step = true ∧
      baseIdx ≤ p.stepIdx ∧
      listGetOpt steps (p.stepIdx - baseIdx) = some p.step ∧
      p.cand ∈ cands ∧
      candidateMatches p.step p.refKind p.cand.kind p.cand = true ∧
      (∀ (offset : Nat) (s : ProbeStep) (rk : RefKind) (c : MethodCandidate),
        listGetOpt steps offset = some s →
        stepEligible s = true →
        c ∈ cands →
        candidateMatches s rk c.kind c = true →
        ProbePriorityLe p.stepIdx p.refKind p.cand.kind (baseIdx + offset) rk c.kind)
  | [], _, _, h => by cases h
  | step :: rest, baseIdx, p, h => by
    unfold probePickAux at h
    cases hElig : stepEligible step with
    | false =>
      rw [hElig] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      have ⟨hPElig, hGe, hGet, hMem, hMatch, hMin⟩ :=
        probePickAux_spec cands arbitrarySelfTypes rest (baseIdx + 1) p h
      have hGe0 : baseIdx ≤ p.stepIdx := Nat.le_trans (Nat.le_succ baseIdx) hGe
      have hSub : p.stepIdx - baseIdx = (p.stepIdx - (baseIdx + 1)) + 1 := by
        cases hEq : p.stepIdx - baseIdx with
        | zero =>
          have hLe : p.stepIdx ≤ baseIdx := Nat.le_of_sub_eq_zero hEq
          have hLt : baseIdx < p.stepIdx := hGe
          exact False.elim (Nat.not_lt_of_ge hLe hLt)
        | succ k =>
          have hK : p.stepIdx - (baseIdx + 1) = k := by
            rw [Nat.sub_add_eq, hEq, Nat.succ_sub_one]
          rw [hK]
      refine ⟨hPElig, hGe0, ?_, hMem, hMatch, ?_⟩
      · rw [hSub]; exact hGet
      · intro offset s rk c hOff hSElig hCMem hCMatch
        cases offset with
        | zero =>
          simp only [listGetOpt, Option.some.injEq] at hOff
          subst hOff
          rw [hElig] at hSElig
          cases hSElig
        | succ k =>
          have hRes := hMin k s rk c hOff hSElig hCMem hCMatch
          have hIdx : baseIdx + 1 + k = baseIdx + (k + 1) := by
            rw [Nat.add_assoc, Nat.add_comm 1 k]
          rw [hIdx] at hRes
          exact hRes
    | true =>
      rw [hElig] at h
      simp only [↓reduceIte] at h
      cases hStep : pickAtStep step cands arbitrarySelfTypes baseIdx with
      | ambiguity => rw [hStep] at h; cases h
      | picked q =>
        rw [hStep] at h
        cases h
        have ⟨hI, hS, hMem, hMatch, hMin⟩ :=
          pickAtStep_picked_spec step cands arbitrarySelfTypes baseIdx p hStep
        refine ⟨by rw [hS]; exact hElig, by rw [hI]; exact Nat.le_refl _, ?_, hMem, by rw [hS]; exact hMatch, ?_⟩
        · rw [hI, Nat.sub_self, hS]; rfl
        · intro offset s rk c hOff _ hCMem hCMatch
          cases offset with
          | zero =>
            simp only [listGetOpt, Option.some.injEq] at hOff
            subst hOff
            rw [hI, Nat.add_zero]
            exact Or.inr ⟨rfl, hMin rk c hCMem hCMatch⟩
          | succ k =>
            rw [hI]
            exact Or.inl (Nat.lt_add_of_pos_right (Nat.succ_pos k))
      | notFound =>
        rw [hStep] at h
        have ⟨hPElig, hGe, hGet, hMem, hMatch, hMin⟩ :=
          probePickAux_spec cands arbitrarySelfTypes rest (baseIdx + 1) p h
        have hGe0 : baseIdx ≤ p.stepIdx := Nat.le_trans (Nat.le_succ baseIdx) hGe
        have hSub : p.stepIdx - baseIdx = (p.stepIdx - (baseIdx + 1)) + 1 := by
          cases hEq : p.stepIdx - baseIdx with
          | zero =>
            have hLe : p.stepIdx ≤ baseIdx := Nat.le_of_sub_eq_zero hEq
            have hLt : baseIdx < p.stepIdx := hGe
            exact False.elim (Nat.not_lt_of_ge hLe hLt)
          | succ k =>
            have hK : p.stepIdx - (baseIdx + 1) = k := by
              rw [Nat.sub_add_eq, hEq, Nat.succ_sub_one]
            rw [hK]
        refine ⟨hPElig, hGe0, ?_, hMem, hMatch, ?_⟩
        · rw [hSub]; exact hGet
        · intro offset s rk c hOff hSElig hCMem hCMatch
          cases offset with
          | zero =>
            simp only [listGetOpt, Option.some.injEq] at hOff
            subst hOff
            have hNo := pickAtStep_notFound_no_match step cands arbitrarySelfTypes baseIdx hStep rk c hCMem
            rw [hNo] at hCMatch
            cases hCMatch
          | succ k =>
            have hRes := hMin k s rk c hOff hSElig hCMem hCMatch
            have hIdx : baseIdx + 1 + k = baseIdx + (k + 1) := by
              rw [Nat.add_assoc, Nat.add_comm 1 k]
            rw [hIdx] at hRes
            exact hRes

/-- **Theorem 2 (`methodProbe_first_step_wins`)**:
Lexicographic `(stepIndex, refKind, candKind)` determinism and minimality of
`rustc_hir_typeck::method::probe`:
whenever `probePick` selects `p`, `p` is uniquely determined and beats or ties
every applicable candidate at every eligible step in the exact lexicographic
order `(stepIndex, RefKind.rank, CandKind.rank)`. -/
theorem methodProbe_first_step_wins
    (steps : List ProbeStep) (cands : List MethodCandidate)
    (arbitrarySelfTypes : Bool) (p : MethodPick)
    (hPick : probePick steps cands arbitrarySelfTypes = .picked p) :
    listGetOpt steps p.stepIdx = some p.step ∧
    p.step.reachableViaDeref = true ∧
    p.step.fromUnsafeDeref = false ∧
    (∀ (j : Nat) (s : ProbeStep) (rk : RefKind) (c : MethodCandidate),
      listGetOpt steps j = some s →
      s.reachableViaDeref = true →
      s.fromUnsafeDeref = false →
      c ∈ cands →
      candidateMatches s rk c.kind c = true →
      ProbePriorityLe p.stepIdx p.refKind p.cand.kind j rk c.kind) := by
  have ⟨hElig, _, hGet, _, _, hMin⟩ :=
    probePickAux_spec cands arbitrarySelfTypes steps 0 p hPick
  have hSub0 : p.stepIdx - 0 = p.stepIdx := Nat.sub_zero p.stepIdx
  rw [hSub0] at hGet
  unfold stepEligible at hElig
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hElig
  refine ⟨hGet, hElig.1, hElig.2, ?_⟩
  intro j s rk c hJ hR hU hCMem hCMatch
  have hSElig : stepEligible s = true := by
    unfold stepEligible; rw [hR, hU]; rfl
  have hRes := hMin j s rk c hJ hSElig hCMem hCMatch
  rw [Nat.zero_add] at hRes
  exact hRes

/-- Corollary 2a: `probePick` never picks from a `Receiver`-only step
(`reachableViaDeref = false`, `probe.rs:1356`). -/
theorem methodProbe_never_picks_non_deref_step
    (steps : List ProbeStep) (cands : List MethodCandidate)
    (arbitrarySelfTypes : Bool) (p : MethodPick)
    (hPick : probePick steps cands arbitrarySelfTypes = .picked p) :
    p.step.reachableViaDeref = true :=
  (methodProbe_first_step_wins steps cands arbitrarySelfTypes p hPick).2.1

/-- Corollary 2b: `probePick` never implicitly dereferences through a raw pointer
(`fromUnsafeDeref = true`, `probe.rs:1361`). -/
theorem methodProbe_never_picks_unsafe_raw_deref
    (steps : List ProbeStep) (cands : List MethodCandidate)
    (arbitrarySelfTypes : Bool) (p : MethodPick)
    (hPick : probePick steps cands arbitrarySelfTypes = .picked p) :
    p.step.fromUnsafeDeref = false :=
  (methodProbe_first_step_wins steps cands arbitrarySelfTypes p hPick).2.2.1

/-- Corollary 2c: an unsized array-to-slice step (`unsize = true`) can never be
picked by-value or via `constPtr` (`probe.rs:1596, 1721`). -/
theorem methodProbe_unsized_step_never_by_value
    (steps : List ProbeStep) (cands : List MethodCandidate)
    (arbitrarySelfTypes : Bool) (p : MethodPick)
    (hPick : probePick steps cands arbitrarySelfTypes = .picked p)
    (hUnsize : p.step.unsize = true) :
    p.refKind ≠ .byVal ∧ p.refKind ≠ .constPtr := by
  have ⟨_, _, _, _, hMatch, _⟩ :=
    probePickAux_spec cands arbitrarySelfTypes steps 0 p hPick
  unfold candidateMatches at hMatch
  simp only [Bool.and_eq_true] at hMatch
  have hAllow := hMatch.1.1.1
  constructor
  · intro hBV; rw [hBV] at hAllow; unfold stepAllowsRefKind at hAllow; rw [hUnsize] at hAllow; cases hAllow
  · intro hCP; rw [hCP] at hAllow; unfold stepAllowsRefKind at hAllow; rw [hUnsize] at hAllow; cases hAllow

/-! ### Sharpness Counterexamples for Part 2 -/

/-- `(depth=0, sharedRef, extension)` beats `(depth=1, byVal, inherent)`. -/
theorem ce_depth0_autoref_beats_depth1_by_val :
    let step0 : ProbeStep := ⟨10, 0, true, false, false, false⟩
    let step1 : ProbeStep := ⟨20, 1, true, false, false, false⟩
    let extDepth0Ref : MethodCandidate := ⟨1, .extension, 10, .sharedRef, 0⟩
    let inhDepth1Val : MethodCandidate := ⟨2, .inherent,  20, .byVal,     1⟩
    probePick [step0, step1] [inhDepth1Val, extDepth0Ref] true =
      .picked ⟨0, step0, .sharedRef, extDepth0Ref⟩ := rfl

/-- Exact `[T; N]` beats the trailing `unsize = true` `[T]` slice step. -/
theorem ce_array_exact_beats_unsized_slice :
    let arrStep   : ProbeStep := ⟨100, 1, true, false, false, false⟩
    let sliceStep : ProbeStep := ⟨101, 1, true, false, true,  false⟩
    let arrCand   : MethodCandidate := ⟨1, .extension, 100, .sharedRef, 1⟩
    let sliceCand : MethodCandidate := ⟨2, .inherent,  101, .sharedRef, 1⟩
    probePick [arrStep, sliceStep] [sliceCand, arrCand] true =
      .picked ⟨0, arrStep, .sharedRef, arrCand⟩ := rfl

/-- **Sharpness Counterexample 2 (`ce_shadowing_asymmetry_and_anti_shadowing`)**:
Constructively witnesses the exact `PickConstraintsForShadowed` asymmetry
(`probe.rs:208-210, 1496-1581`) empirically observed in `rustc`:
  1. SmartPtr inherent `byVal` (`receiverSteps=0`) vs Inner inherent `sharedRef`
     (`receiverSteps=1`) triggers `.ambiguity` (`E0034`).
  2. SmartPtr inherent `sharedRef` (`receiverSteps=0`) vs Inner inherent `mutRef`
     (`receiverSteps=1`) triggers `.ambiguity` (`E0034`).
  3. Reversing roles: Inner inherent `byVal` (`receiverSteps=1`) vs SmartPtr
     inherent `sharedRef` (`receiverSteps=0`) does NOT trigger anti-shadowing
     (`0 > 1` is false) and selects `innerByVal`! -/
theorem ce_shadowing_asymmetry_and_anti_shadowing :
    let stepPtr   : ProbeStep := ⟨50, 0, true,  false, false, false⟩
    let stepInner : ProbeStep := ⟨51, 1, false, false, false, false⟩
    let ptrVal    : MethodCandidate := ⟨1, .inherent, 50, .byVal,     0⟩
    let ptrRef    : MethodCandidate := ⟨2, .inherent, 50, .sharedRef, 0⟩
    let innerVal  : MethodCandidate := ⟨3, .inherent, 50, .byVal,     1⟩
    let innerRef  : MethodCandidate := ⟨4, .inherent, 50, .sharedRef, 1⟩
    let innerMut  : MethodCandidate := ⟨5, .inherent, 50, .mutRef,    1⟩
    probePick [stepPtr, stepInner] [ptrVal, innerRef] true = .ambiguity ∧
    probePick [stepPtr, stepInner] [ptrRef, innerMut] true = .ambiguity ∧
    probePick [stepPtr, stepInner] [ptrRef, innerVal] true =
      .picked ⟨0, stepPtr, .byVal, innerVal⟩ :=
  ⟨rfl, rfl, rfl⟩


/-! ## Part 3: `Receiver` Without `DispatchFromDyn` Vtable ABI Soundness & Counterexample -/

/-- Structural `#[repr(...)]` attributes relevant to `visit_implementation_of_dispatch_from_dyn`
(`compiler/rustc_hir_analysis/src/coherence/builtin.rs:364-366`). -/
inductive ReprKind where
  | reprRust
  | reprC
  | reprPacked
  deriving DecidableEq, Repr

/-- Field classification for a smart-pointer receiver struct `P<T>`. -/
inductive FieldKind where
  | coercedPtr                        -- The pointer field referencing `T` (`1` word thin, `2` words wide)
  | phantomData                       -- `PhantomData<...>` (`0` words, always ignored)
  | oneZst (mentionsTypeParam : Bool) -- 1-aligned ZST (`0` words; allowed iff `!mentionsTypeParam`)
  | nonZstData (extraWordsMinus1 : Nat) -- Non-ZST payload occupying `extraWordsMinus1 + 1` ABI words
  deriving DecidableEq, Repr

structure ReceiverLayout where
  repr : ReprKind
  fields : List FieldKind
  deriving DecidableEq, Repr

/-- Number of ABI machine words occupied by `L` when instantiated with a wide
`dyn Trait` pointee (`isWide = true`) vs a concrete sized pointee (`isWide = false`). -/
def fieldWords (isWide : Bool) : FieldKind → Nat
  | .coercedPtr          => if isWide then 2 else 1
  | .phantomData         => 0
  | .oneZst _            => 0
  | .nonZstData k        => k + 1

def fieldsWordCount (isWide : Bool) : List FieldKind → Nat
  | [] => 0
  | f :: fs => fieldWords isWide f + fieldsWordCount isWide fs

def abiWordCount (isWide : Bool) (L : ReceiverLayout) : Nat :=
  fieldsWordCount isWide L.fields

/-- Exact word-level ABI serialization of a receiver value `P<T>` given the
pointer's ABI words (`[dataPtr, vtablePtr]` when wide, `[dataPtr]` when thin)
and a payload tag word for any non-ZST extra field. -/
def encodeFields (ptrWords : List Nat) (tagWord : Nat) : List FieldKind → List Nat
  | [] => []
  | .coercedPtr :: fs => ptrWords ++ encodeFields ptrWords tagWord fs
  | .phantomData :: fs => encodeFields ptrWords tagWord fs
  | .oneZst _ :: fs => encodeFields ptrWords tagWord fs
  | .nonZstData k :: fs => List.replicate (k + 1) tagWord ++ encodeFields ptrWords tagWord fs

def encodeReceiver (L : ReceiverLayout) (ptrWords : List Nat) (tagWord : Nat) : List Nat :=
  encodeFields ptrWords tagWord L.fields

/-- Hardwired compiler vtable dispatch shim (`library/core/src/ops/unsize.rs:89-106`,
`coherence/builtin.rs:322-329`): treats the wide receiver ABI identically to a
single `(dataPtr, vtablePtr)` pair, stripping `vtablePtr` and passing `[dataPtr]`
as the thin receiver to the concrete monomorphized callee. -/
def vtableShimNarrow : List Nat → Option (List Nat)
  | [dataPtr, _vtablePtr] => some [dataPtr]
  | _ => none

/-- Count of coerced pointer fields in a struct. -/
def countCoercedPtrs : List FieldKind → Nat
  | [] => 0
  | .coercedPtr :: fs => countCoercedPtrs fs + 1
  | _ :: fs => countCoercedPtrs fs

/-- Every non-`coercedPtr` field is either `PhantomData` or a 1-ZST that does
not mention type parameters (`coherence/builtin.rs:374-411`). -/
def allNonCoercedFieldsAllowed : List FieldKind → Prop
  | [] => True
  | .coercedPtr :: fs => allNonCoercedFieldsAllowed fs
  | .phantomData :: fs => allNonCoercedFieldsAllowed fs
  | .oneZst false :: fs => allNonCoercedFieldsAllowed fs
  | .oneZst true :: _ => False
  | .nonZstData _ :: _ => False

/-- Exact structural gate enforced by `visit_implementation_of_dispatch_from_dyn`
(`compiler/rustc_hir_analysis/src/coherence/builtin.rs:364-459`). -/
structure SatisfiesDispatchFromDyn (L : ReceiverLayout) : Prop where
  reprRust : L.repr = .reprRust
  uniqueCoercedField : countCoercedPtrs L.fields = 1
  onlyAllowedOtherFields : allNonCoercedFieldsAllowed L.fields

theorem zero_coerced_allowed_words (isWide : Bool) :
    ∀ fs : List FieldKind,
      countCoercedPtrs fs = 0 →
      allNonCoercedFieldsAllowed fs →
      fieldsWordCount isWide fs = 0
  | [], _, _ => rfl
  | .coercedPtr :: _, hCnt, _ => by cases hCnt
  | .phantomData :: fs, hCnt, hAll => by
    simp only [fieldsWordCount, fieldWords, Nat.zero_add]
    exact zero_coerced_allowed_words isWide fs hCnt hAll
  | .oneZst false :: fs, hCnt, hAll => by
    simp only [fieldsWordCount, fieldWords, Nat.zero_add]
    exact zero_coerced_allowed_words isWide fs hCnt hAll
  | .oneZst true :: _, _, hAll => False.elim hAll
  | .nonZstData _ :: _, _, hAll => False.elim hAll

theorem zero_coerced_allowed_encode (ptrWords : List Nat) (tagWord : Nat) :
    ∀ fs : List FieldKind,
      countCoercedPtrs fs = 0 →
      allNonCoercedFieldsAllowed fs →
      encodeFields ptrWords tagWord fs = []
  | [], _, _ => rfl
  | .coercedPtr :: _, hCnt, _ => by cases hCnt
  | .phantomData :: fs, hCnt, hAll =>
    zero_coerced_allowed_encode ptrWords tagWord fs hCnt hAll
  | .oneZst false :: fs, hCnt, hAll =>
    zero_coerced_allowed_encode ptrWords tagWord fs hCnt hAll
  | .oneZst true :: _, _, hAll => False.elim hAll
  | .nonZstData _ :: _, _, hAll => False.elim hAll

theorem one_coerced_allowed_words (isWide : Bool) :
    ∀ fs : List FieldKind,
      countCoercedPtrs fs = 1 →
      allNonCoercedFieldsAllowed fs →
      fieldsWordCount isWide fs = if isWide then 2 else 1
  | [], hCnt, _ => by cases hCnt
  | .coercedPtr :: fs, hCnt, hAll => by
    have hZero : countCoercedPtrs fs = 0 := Nat.succ.inj hCnt
    have hRest := zero_coerced_allowed_words isWide fs hZero hAll
    simp only [fieldsWordCount, fieldWords, hRest, Nat.add_zero]
  | .phantomData :: fs, hCnt, hAll => by
    simp only [fieldsWordCount, fieldWords, Nat.zero_add]
    exact one_coerced_allowed_words isWide fs hCnt hAll
  | .oneZst false :: fs, hCnt, hAll => by
    simp only [fieldsWordCount, fieldWords, Nat.zero_add]
    exact one_coerced_allowed_words isWide fs hCnt hAll
  | .oneZst true :: _, _, hAll => False.elim hAll
  | .nonZstData _ :: _, _, hAll => False.elim hAll

theorem one_coerced_allowed_encode (ptrWords : List Nat) (tagWord : Nat) :
    ∀ fs : List FieldKind,
      countCoercedPtrs fs = 1 →
      allNonCoercedFieldsAllowed fs →
      encodeFields ptrWords tagWord fs = ptrWords
  | [], hCnt, _ => by cases hCnt
  | .coercedPtr :: fs, hCnt, hAll => by
    have hZero : countCoercedPtrs fs = 0 := Nat.succ.inj hCnt
    have hRest := zero_coerced_allowed_encode ptrWords tagWord fs hZero hAll
    simp only [encodeFields, hRest, List.append_nil]
  | .phantomData :: fs, hCnt, hAll =>
    one_coerced_allowed_encode ptrWords tagWord fs hCnt hAll
  | .oneZst false :: fs, hCnt, hAll =>
    one_coerced_allowed_encode ptrWords tagWord fs hCnt hAll
  | .oneZst true :: _, _, hAll => False.elim hAll
  | .nonZstData _ :: _, _, hAll => False.elim hAll

/-- **Theorem 3a (`dispatchFromDyn_vtable_call_sound`)**:
Any receiver layout satisfying `SatisfiesDispatchFromDyn` is ABI-isomorphic to
a single pointer (`2` words wide for `dyn Trait`, `1` word thin for concrete
`T`), so `vtableShimNarrow` maps the wide receiver encoding directly and
losslessly to the exact thin receiver encoding expected by the concrete callee. -/
theorem dispatchFromDyn_vtable_call_sound (L : ReceiverLayout)
    (hDfd : SatisfiesDispatchFromDyn L) :
    abiWordCount true L = 2 ∧
    abiWordCount false L = 1 ∧
    (∀ dataPtr vtablePtr tagWord,
      vtableShimNarrow (encodeReceiver L [dataPtr, vtablePtr] tagWord) =
        some (encodeReceiver L [dataPtr] tagWord)) := by
  refine ⟨one_coerced_allowed_words true L.fields hDfd.uniqueCoercedField hDfd.onlyAllowedOtherFields,
          one_coerced_allowed_words false L.fields hDfd.uniqueCoercedField hDfd.onlyAllowedOtherFields,
          ?_⟩
  intro dataPtr vtablePtr tagWord
  unfold encodeReceiver
  rw [one_coerced_allowed_encode [dataPtr, vtablePtr] tagWord L.fields hDfd.uniqueCoercedField hDfd.onlyAllowedOtherFields]
  rw [one_coerced_allowed_encode [dataPtr] tagWord L.fields hDfd.uniqueCoercedField hDfd.onlyAllowedOtherFields]
  rfl

/-- Concrete model of `struct NonDynHandle<T: ?Sized> { ptr: *const T, tag: u32 }`:
a completely valid `core::ops::Receiver<Target = T>` that does NOT satisfy
`DispatchFromDyn` because of its extra non-ZST `tag: u32` field. -/
def nonDynHandleLayout : ReceiverLayout :=
  { repr := .reprRust, fields := [.coercedPtr, .nonZstData 0] }

/-- **Theorem 3b (`ce_non_layout_isomorphic_receiver_breaks_vtable_call`)**:
Constructively proves that `NonDynHandle<T>` (valid for `core::ops::Receiver`):
  1. fails `SatisfiesDispatchFromDyn` (explaining `E0038` / `E0378`),
  2. has ABI word widths `3 ≠ 2` (wide) and `2 ≠ 1` (thin),
  3. is rejected by the wide-to-thin `vtableShimNarrow` ABI contract (`= none`),
     and any naive thin-pointer projection `[dataPtr]` strictly differs from
     the concrete callee's expected `[dataPtr, tag]` ABI buffer (losing `tag`). -/
theorem ce_non_layout_isomorphic_receiver_breaks_vtable_call :
    (¬ SatisfiesDispatchFromDyn nonDynHandleLayout) ∧
    abiWordCount true nonDynHandleLayout = 3 ∧
    abiWordCount false nonDynHandleLayout = 2 ∧
    vtableShimNarrow (encodeReceiver nonDynHandleLayout [4096, 8192] 42) = none ∧
    [4096] ≠ encodeReceiver nonDynHandleLayout [4096] 42 := by
  refine ⟨?_, rfl, rfl, rfl, ?_⟩
  · intro h
    exact h.onlyAllowedOtherFields
  · intro hEq
    cases hEq

/-- Sharpness Counterexample 3c: `#[repr(C)]` single-pointer wrapper is rejected
by `SatisfiesDispatchFromDyn` (`coherence/builtin.rs:364-366`, `E0378`). -/
def reprCHandleLayout : ReceiverLayout :=
  { repr := .reprC, fields := [.coercedPtr] }

theorem ce_repr_c_receiver_rejected_by_dispatch_from_dyn :
    ¬ SatisfiesDispatchFromDyn reprCHandleLayout := by
  intro h
  have hr := h.reprRust
  cases hr

/-- Sharpness Counterexample 3d: a 1-ZST field mentioning a type parameter
(`oneZst true`) is rejected by `SatisfiesDispatchFromDyn` (`coherence/builtin.rs:394-403`). -/
def paramZstHandleLayout : ReceiverLayout :=
  { repr := .reprRust, fields := [.coercedPtr, .oneZst true] }

theorem ce_zst_type_param_rejected_by_dispatch_from_dyn :
    ¬ SatisfiesDispatchFromDyn paramZstHandleLayout := by
  intro h
  exact h.onlyAllowedOtherFields

end RustcDerefAndArbitrarySelf
