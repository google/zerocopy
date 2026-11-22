/-
Accessor purity for deref patterns generalized to user-defined accessors.

These are definitions of a toy model. An accessor is meant to capture a user-defined
`Deref::deref` called by a lowered match: it receives the scrutinee and a hidden state (for
example interior-mutable data) and returns a result and a new hidden state; it cannot modify the
scrutinee. `repeated` is meant to capture a decision tree that calls the accessor once per test
node; `shared` one that calls it once and shares the result as a DAG node. These are not Rust's
definitions.
-/

namespace Toy.MatchGuard.Accessor

/-- An accessor with hidden state `σ`, scrutinee type `S` and result type `R`. -/
abbrev Acc (σ S R : Type) := σ → S → R × σ

variable {σ S R : Type}

/-- Repeated-call lowering: each arm's test calls the accessor afresh (threading the hidden
state) and tests its predicate on the result. Returns the selected arm index (`none` is
`Unreachable`) and the final hidden state. -/
def repeated (acc : Acc σ S R) (s : S) : List (R → Bool) → Nat → σ → Option Nat × σ
  | [], _, st => (none, st)
  | p :: ps, i, st =>
    if p (acc st s).1 then (some i, (acc st s).2) else repeated acc s ps (i + 1) (acc st s).2

/-- The first arm (from index `i`) whose predicate holds of `r`. -/
def findFrom (r : R) : List (R → Bool) → Nat → Option Nat
  | [], _ => none
  | p :: ps, i => if p r then some i else findFrom r ps (i + 1)

/-- Shared (DAG) lowering: one accessor call, whose result every arm's test reuses (no call for
an empty arm list). -/
def shared (acc : Acc σ S R) (s : S) (arms : List (R → Bool)) (st : σ) : Option Nat × σ :=
  match arms with
  | [] => (none, st)
  | _ :: _ => (findFrom (acc st s).1 arms 0, (acc st s).2)

/-- From every hidden state, a second call returns the same result as the first. -/
def ResultStable (acc : Acc σ S R) : Prop := ∀ st s, (acc (acc st s).2 s).1 = (acc st s).1

/-- From every hidden state, a second call leaves the hidden state where the first left it. -/
def StateIdempotent (acc : Acc σ S R) : Prop := ∀ st s, (acc (acc st s).2 s).2 = (acc st s).2

/-- Strict purity: a call never changes the hidden state, and its result does not depend on it. -/
def Pure (acc : Acc σ S R) : Prop := ∀ st s, (acc st s).2 = st ∧ ∀ st', (acc st' s).1 = (acc st s).1

/-- Every result lies in the result domain `RDom` (the accessor is well-typed). -/
def WellTyped (RDom : R → Prop) (acc : Acc σ S R) : Prop := ∀ st s, RDom (acc st s).1

/-- Exhaustiveness of a list of arm predicates on the result domain `RDom`. -/
def ExhaustiveOn (RDom : R → Prop) (arms : List (R → Bool)) : Prop :=
  ∀ r, RDom r → ∃ p ∈ arms, p r = true

/-! ### Lemmas -/

theorem repeated_fst_of_resultStable (acc : Acc σ S R) (h : ResultStable acc) (s : S) :
    ∀ (arms : List (R → Bool)) (i : Nat) (st : σ),
      (repeated acc s arms i st).1 = findFrom (acc st s).1 arms i
  | [], _, _ => rfl
  | p :: ps, i, st => by
    simp only [repeated, findFrom]
    split
    · rfl
    · rw [repeated_fst_of_resultStable acc h s ps (i + 1) (acc st s).2, h st s]

theorem repeated_cons_of_stable (acc : Acc σ S R) (h1 : ResultStable acc)
    (h2 : StateIdempotent acc) (s : S) (p : R → Bool) :
    ∀ (ps : List (R → Bool)) (i : Nat) (st : σ),
      repeated acc s (p :: ps) i st = (findFrom (acc st s).1 (p :: ps) i, (acc st s).2) := by
  intro ps
  induction ps generalizing p with
  | nil =>
    intro i st
    simp only [repeated, findFrom]
    split <;> rfl
  | cons q qs ih =>
    intro i st
    simp only [repeated] at ih ⊢
    simp only [findFrom]
    split
    · rfl
    · rw [ih q (i + 1) (acc st s).2, h1 st s, h2 st s]
      simp only [findFrom]

theorem findFrom_ne_none {r : R} {p : R → Bool} :
    ∀ (arms : List (R → Bool)) (i : Nat), p ∈ arms → p r = true → findFrom r arms i ≠ none
  | [], _, h, _ => by simp at h
  | q :: qs, i, h, hp => by
    simp only [findFrom]
    split
    · simp
    · rename_i hq
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd hp hq
      · exact findFrom_ne_none qs (i + 1) h hp

/-! ### Results -/

/-- **Shared and repeated lowerings select the same arm iff results are stable.** For every
accessor `acc`, the shared and repeated lowerings select the same arm for every scrutinee, every
hidden state and every arm list iff `ResultStable acc` (from every hidden state, reachable or
not, a second call returns the same result as the first). -/
theorem shared_selected_eq_repeated_selected_iff_resultStable (acc : Acc σ S R) :
    (∀ s st arms, (shared acc s arms st).1 = (repeated acc s arms 0 st).1) ↔ ResultStable acc := by
  classical
  constructor
  · intro h st s
    have := h s st [fun _ => false, fun r => decide (r = (acc st s).1)]
    simp only [shared, findFrom, repeated] at this
    by_cases he : (acc (acc st s).2 s).1 = (acc st s).1
    · exact he
    · simp [he] at this
  · intro h s st arms
    cases arms with
    | nil => rfl
    | cons p ps =>
      simp only [shared]
      rw [repeated_fst_of_resultStable acc h s]

/-- **Shared and repeated lowerings agree, including the final hidden state, iff results are
stable and the state is idempotent.** For every accessor `acc`,
`shared acc s arms st = repeated acc s arms 0 st` for every scrutinee, every hidden state and
every arm list iff `ResultStable acc` and `StateIdempotent acc` (each from every hidden state,
reachable or not). -/
theorem shared_eq_repeated_iff_resultStable_and_stateIdempotent (acc : Acc σ S R) :
    (∀ s st arms, shared acc s arms st = repeated acc s arms 0 st) ↔
      ResultStable acc ∧ StateIdempotent acc := by
  classical
  constructor
  · intro h
    refine ⟨(shared_selected_eq_repeated_selected_iff_resultStable acc).mp
      (fun s st arms => by rw [h s st arms]), ?_⟩
    intro st s
    have := h s st [fun _ => false, fun _ => true]
    simp only [shared, findFrom, repeated] at this
    simp at this
    exact this.symm
  · rintro ⟨h1, h2⟩ s st arms
    cases arms with
    | nil => rfl
    | cons p ps =>
      simp only [shared]
      rw [repeated_cons_of_stable acc h1 h2 s p ps 0 st]

/-- **Exhaustiveness preservation for the repeated lowering iff results are stable.** For every
result domain `RDom` and every accessor `acc` whose results from every hidden state and
scrutinee lie in `RDom` (`WellTyped RDom acc`): the repeated lowering does not reach
`Unreachable` for every arm list exhaustive on `RDom` (`ExhaustiveOn RDom arms`), every scrutinee
and every hidden state, iff `ResultStable acc` (from every hidden state, reachable or not, a
second call returns the same result as the first). -/
theorem repeated_not_unreachable_on_exhaustiveOn_iff_resultStable_of_wellTyped (RDom : R → Prop)
    (acc : Acc σ S R) (hwt : WellTyped RDom acc) :
    (∀ arms, ExhaustiveOn RDom arms → ∀ s st, (repeated acc s arms 0 st).1 ≠ none) ↔
      ResultStable acc := by
  classical
  constructor
  · intro h st s
    by_cases he : (acc (acc st s).2 s).1 = (acc st s).1
    · exact he
    · exfalso
      have hex : ExhaustiveOn RDom
          [fun r => decide (r = (acc (acc st s).2 s).1),
            fun r => !decide (r = (acc (acc st s).2 s).1)] := by
        intro r _
        by_cases hr : r = (acc (acc st s).2 s).1
        · exact ⟨_, List.mem_cons_self, by simp [hr]⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by simp [hr]⟩
      apply h _ hex s st
      simp only [repeated]
      have hne : (acc st s).1 ≠ (acc (acc st s).2 s).1 := fun e => he e.symm
      simp [hne]
  · intro h arms hex s st
    rw [repeated_fst_of_resultStable acc h s]
    obtain ⟨p, hp, hpr⟩ := hex _ (hwt st s)
    exact findFrom_ne_none arms 0 hp hpr

/-- Strict purity implies result stability and state idempotence. -/
theorem resultStable_and_stateIdempotent_of_pure (acc : Acc σ S R) (h : Pure acc) :
    ResultStable acc ∧ StateIdempotent acc := by
  constructor
  · intro st s; rw [(h st s).1]
  · intro st s; rw [(h st s).1, (h st s).1]

/-! ### Instances -/

/-- A stateful accessor that returns its hidden flag and flips it on every call. -/
def toggleAcc : Acc Bool Unit Bool := fun st _ => (st, !st)

/-- An accessor that counts its calls and returns `()`. -/
def countAcc : Acc Nat Unit Unit := fun n _ => ((), n + 1)

/-- An accessor that sets a flag on its first call and returns `()`. -/
def flagAcc : Acc Bool Unit Unit := fun _ _ => ((), true)

/-- A pure accessor: returns the scrutinee, leaves the state unchanged. -/
def idAcc : Acc Unit Bool Bool := fun st s => (s, st)

/-- A pure accessor that always returns `false`. -/
def constFalseAcc : Acc Unit Unit Bool := fun st _ => (false, st)

/-- The exhaustive arm list `[true => .., false => ..]` on `bool` results. -/
def boolResultArms : List (Bool → Bool) := [fun r => r, fun r => !r]

theorem boolResultArms_exhaustive : ExhaustiveOn (fun _ => True) boolResultArms := by
  intro r _
  cases r
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  · exact ⟨_, List.mem_cons_self, rfl⟩

/-- **Counterexample (stateful accessor).** `toggleAcc` (hidden state `Bool`, scrutinee `Unit`,
result `Bool`) satisfies `WellTyped (fun _ => True)` (every result lies in the full `Bool`
domain) and is not result-stable; with the exhaustive `boolResultArms` from hidden state `false`,
the repeated lowering reaches `Unreachable` while the shared lowering selects arm `1`. -/
theorem toggleAcc_repeated_reaches_unreachable :
    WellTyped (fun _ => True) toggleAcc ∧ ¬ ResultStable toggleAcc ∧
      ExhaustiveOn (fun _ => True) boolResultArms ∧
      (repeated toggleAcc () boolResultArms 0 false).1 = none ∧
      (shared toggleAcc () boolResultArms false).1 = some 1 := by
  refine ⟨fun _ _ => trivial, ?_, boolResultArms_exhaustive, rfl, rfl⟩
  intro h
  have := h false ()
  revert this; decide

/-- **Positive control (state idempotence matters for final states).** `countAcc` is
result-stable but not state-idempotent; on `[_ if false-pattern, _]` the two lowerings select
the same arm and end in different hidden states. -/
theorem countAcc_same_selection_different_state :
    ResultStable countAcc ∧ ¬ StateIdempotent countAcc ∧
      (shared countAcc () [fun _ => false, fun _ => true] 0).1 =
        (repeated countAcc () [fun _ => false, fun _ => true] 0 0).1 ∧
      (shared countAcc () [fun _ => false, fun _ => true] 0).2 = 1 ∧
      (repeated countAcc () [fun _ => false, fun _ => true] 0 0).2 = 2 := by
  refine ⟨fun _ _ => rfl, ?_, rfl, rfl, rfl⟩
  intro h
  have := h 0 ()
  revert this; decide

/-- **Positive control (purity is not necessary).** `flagAcc` is result-stable and
state-idempotent but not strictly pure (its first call changes the hidden state). -/
theorem flagAcc_stable_idempotent_not_pure :
    ResultStable flagAcc ∧ StateIdempotent flagAcc ∧ ¬ Pure flagAcc := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  intro h
  have := (h false ()).1
  revert this; decide

/-- **Counterexample (well-typed results).** `constFalseAcc` is result-stable, is not well-typed
for the result domain `{true}`, and with the arm list `[true => ..]`, exhaustive on that domain,
the repeated lowering reaches `Unreachable`; so the characterization fails for it. -/
theorem constFalseAcc_resultStable_not_wellTyped_and_iff_fails :
    ResultStable constFalseAcc ∧ ¬ WellTyped (fun r => r = true) constFalseAcc ∧
      ExhaustiveOn (fun r => r = true) [fun r => r] ∧
      (repeated constFalseAcc () [fun r => r] 0 ()).1 = none ∧
      ¬ ((∀ arms, ExhaustiveOn (fun r => r = true) arms → ∀ s st,
            (repeated constFalseAcc s arms 0 st).1 ≠ none) ↔ ResultStable constFalseAcc) := by
  refine ⟨fun _ _ => rfl, ?_, ?_, rfl, ?_⟩
  · intro h; have := h () (); revert this; decide
  · intro r hr; exact ⟨_, List.mem_cons_self, hr⟩
  · intro hiff
    exact hiff.mpr (fun _ _ => rfl) [fun r => r] (fun r hr => ⟨_, List.mem_cons_self, hr⟩) () () rfl

/-- **Non-vacuity.** `idAcc` is strictly pure (hence result-stable and state-idempotent) and
well-typed for the full `bool` domain. -/
theorem idAcc_pure_wellTyped : Pure idAcc ∧ WellTyped (fun _ => True) idAcc :=
  ⟨fun _ _ => ⟨rfl, fun _ => rfl⟩, fun _ _ => trivial⟩

/-- An accessor that returns the scrutinee (a `Bool`) and counts its calls. -/
def countedBoolAcc : Acc Nat Bool Bool := fun n s => (s, n + 1)

/-- An accessor that returns the scrutinee (a `Bool`) and sets a flag on its first call. -/
def loggedBoolAcc : Acc Bool Bool Bool := fun _ s => (s, true)

/-- **Non-vacuity (result type with two values).** `countedBoolAcc` is result-stable, not
state-idempotent and not strictly pure, and its result depends on the scrutinee. -/
theorem countedBoolAcc_resultStable_not_stateIdempotent_not_pure :
    ResultStable countedBoolAcc ∧ ¬ StateIdempotent countedBoolAcc ∧ ¬ Pure countedBoolAcc ∧
      (countedBoolAcc 0 true).1 ≠ (countedBoolAcc 0 false).1 := by
  refine ⟨fun _ _ => rfl, ?_, ?_, by decide⟩
  · intro h; have := h 0 true; revert this; decide
  · intro h; have := (h 0 true).1; revert this; decide

/-- **Non-vacuity (result type with two values).** `loggedBoolAcc` is result-stable and
state-idempotent but not strictly pure, and its result depends on the scrutinee. -/
theorem loggedBoolAcc_resultStable_stateIdempotent_not_pure :
    ResultStable loggedBoolAcc ∧ StateIdempotent loggedBoolAcc ∧ ¬ Pure loggedBoolAcc ∧
      (loggedBoolAcc false true).1 ≠ (loggedBoolAcc false false).1 := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, ?_, by decide⟩
  intro h
  have := (h false true).1
  revert this; decide

/-- Returns `true` on the calls from hidden states `0` and `1`, and `false` from every hidden
state `≥ 2`; each call advances the state to at most `2`. -/
def twoThenFlipAcc : Acc Nat Unit Bool
  | 0, () => (true, 1)
  | 1, () => (true, 2)
  | _, () => (false, 2)

/-- The exhaustive arm list `[false => .., false => .., true => ..]` on `bool` results. -/
def threeBoolArms : List (Bool → Bool) := [fun r => !r, fun r => !r, fun r => r]

theorem threeBoolArms_exhaustive : ExhaustiveOn (fun _ => True) threeBoolArms := by
  intro r _
  cases r
  · exact ⟨_, List.mem_cons_self, rfl⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩

/-- **Two-call stability from one fixed initial state does not suffice.** From hidden state `0`,
a second call of `twoThenFlipAcc` returns the same result as the first, `twoThenFlipAcc` is
well-typed for the full `bool` domain and not result-stable, and on the exhaustive three-arm
list `threeBoolArms` from hidden state `0` the repeated lowering reaches `Unreachable` while the
shared lowering selects arm `2`. -/
theorem twoThenFlipAcc_stable_at_zero_and_repeated_reaches_unreachable :
    (twoThenFlipAcc (twoThenFlipAcc 0 ()).2 ()).1 = (twoThenFlipAcc 0 ()).1 ∧
      WellTyped (fun _ => True) twoThenFlipAcc ∧ ¬ ResultStable twoThenFlipAcc ∧
      ExhaustiveOn (fun _ => True) threeBoolArms ∧
      (repeated twoThenFlipAcc () threeBoolArms 0 0).1 = none ∧
      (shared twoThenFlipAcc () threeBoolArms 0).1 = some 2 := by
  refine ⟨rfl, fun _ _ => trivial, ?_, threeBoolArms_exhaustive, rfl, rfl⟩
  intro h
  have := h 1 ()
  revert this; decide

/-- **Positive control (satisfiable arm predicates on a one-value result type).** For every
accessor with result type `Unit`, every scrutinee, every hidden state and every arm list each of
whose predicates holds of some result, the shared and repeated lowerings agree, including the
final hidden state. -/
theorem shared_eq_repeated_of_unit_of_satisfiable (acc : Acc σ S Unit) (s : S) (st : σ)
    (arms : List (Unit → Bool)) (h : ∀ p ∈ arms, ∃ r, p r = true) :
    shared acc s arms st = repeated acc s arms 0 st := by
  cases arms with
  | nil => rfl
  | cons p ps =>
    obtain ⟨r, hr⟩ := h p List.mem_cons_self
    have hp : p (acc st s).1 = true := by cases r; cases (acc st s).1; exact hr
    simp [shared, repeated, findFrom, hp]

/-! ### Definition examples -/

/-- Positive example (`ResultStable`), with a result type with two values. -/
theorem resultStable_example : ResultStable countedBoolAcc := fun _ _ => rfl
/-- Negative example (`ResultStable`). -/
theorem not_resultStable_example : ¬ ResultStable toggleAcc :=
  toggleAcc_repeated_reaches_unreachable.2.1
/-- Positive example (`StateIdempotent`). -/
theorem stateIdempotent_example : StateIdempotent flagAcc := fun _ _ => rfl
/-- Negative example (`StateIdempotent`). -/
theorem not_stateIdempotent_example : ¬ StateIdempotent countAcc :=
  countAcc_same_selection_different_state.2.1
/-- Positive example (`Pure`). -/
theorem pure_example : Pure idAcc := idAcc_pure_wellTyped.1
/-- Negative example (`Pure`). -/
theorem not_pure_example : ¬ Pure flagAcc := flagAcc_stable_idempotent_not_pure.2.2
/-- Positive example (`WellTyped`). -/
theorem wellTyped_example : WellTyped (fun _ => True) toggleAcc := fun _ _ => trivial
/-- Negative example (`WellTyped`). -/
theorem not_wellTyped_example : ¬ WellTyped (fun r => r = true) constFalseAcc :=
  constFalseAcc_resultStable_not_wellTyped_and_iff_fails.2.1
/-- Positive example (`ExhaustiveOn`). -/
theorem exhaustiveOn_example : ExhaustiveOn (fun _ => True) boolResultArms := boolResultArms_exhaustive
/-- Negative example (`ExhaustiveOn`): `[true => ..]` misses `false`. -/
theorem not_exhaustiveOn_example : ¬ ExhaustiveOn (fun _ => True) [fun r : Bool => r] := by
  intro h
  obtain ⟨p, hp, hr⟩ := h false trivial
  simp at hp; subst hp; cases hr

end Toy.MatchGuard.Accessor
