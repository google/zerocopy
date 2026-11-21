import ToyDrat.Basic

/-!
# Fuel-bounded unit propagation

A *trail* is a list of literals currently assumed true (a partial assignment,
possibly inconsistent). One propagation *round* adds, for every clause, each
literal that the clause forces because all of the clause's other literals are
falsified by the trail. Propagation runs a bounded number of rounds and stops
with `conflict` as soon as the trail contains a complementary pair of literals or
some clause has all of its literals falsified.

Clauses are lists, so a clause may repeat a literal: `x₀ ∨ x₀` forces `x₀` from the
empty trail, exactly like the unit clause `x₀`.

This round-based propagator is monotone in both the formula and the trail at a
fixed budget, which is what the RUP/RAT and deletion results below need. A
production propagator (two watched literals, one literal at a time, run to a
fixpoint) derives the same conflicts given enough steps; that correspondence is
a modeling bridge, not a theorem here.
-/

namespace Toy.Drat

/-- A trail: literals currently assumed true. -/
abbrev Trail := List Lit

/-- `l` is falsified by the trail: its complement is on the trail. -/
def falsified (τ : Trail) (l : Lit) : Bool := decide (l.neg ∈ τ)

/-- Clause `C` forces `l` under `τ`: every literal of `C` other than `l` is falsified.
(Membership `l ∈ C` is imposed separately by `unitLits`.) -/
def forces (τ : Trail) (C : Clause) (l : Lit) : Bool :=
  C.all (fun m => decide (m = l) || falsified τ m)

/-- The literals of `C` that `C` forces under `τ`. For a clause with exactly one
non-falsified literal this is that literal; for a fully falsified clause it is every
literal (harmless: a fully falsified clause is reported as a conflict first). -/
def unitLits (τ : Trail) (C : Clause) : List Lit := C.filter (forces τ C)

/-- A conflict: the trail contains a complementary pair, or some clause of `F` has every
literal falsified by `τ`. (The first disjunct treats the trail literals as unit clauses,
as in the textbook definition `F ∧ ¬C ⊢₁ ⊥` of RUP; it makes tautological clauses RUP.) -/
def hasConflict (F : Formula) (τ : Trail) : Bool :=
  τ.any (falsified τ) || F.any (fun C => C.all (falsified τ))

/-- One propagation round: append every forced literal not already on the trail. -/
def upRound (F : Formula) (τ : Trail) : Trail :=
  τ ++ (F.flatMap (unitLits τ)).filter (fun l => !decide (l ∈ τ))

/-- Outcome of bounded unit propagation: a conflict, or the trail reached when the
budget ran out (which is a fixpoint whenever the budget was large enough). -/
inductive UPResult where
  | conflict
  | trail (τ : Trail)
  deriving DecidableEq, Repr

/-- Unit propagation with a budget of `fuel` rounds, starting from trail `τ`. -/
def unitProp : Nat → Formula → Trail → UPResult
  | 0, F, τ => if hasConflict F τ then .conflict else .trail τ
  | n + 1, F, τ => if hasConflict F τ then .conflict else unitProp n F (upRound F τ)

/-- All literals of the trail are true under `a`. -/
def TrailHolds (a : Assignment) (τ : Trail) : Prop := ∀ l ∈ τ, l.eval a = true

/-- The trail obtained by assuming every literal of `C` false. -/
def negClause (C : Clause) : Trail := C.map Lit.neg

/-! ## Soundness of propagation -/

theorem falsified_eval {a : Assignment} {τ : Trail} (hτ : TrailHolds a τ) {l : Lit}
    (h : falsified τ l = true) : l.eval a = false := by
  have := hτ _ (by simpa [falsified] using h)
  rw [Lit.eval_neg] at this
  simpa using this

theorem hasConflict_false_of_model {a : Assignment} {F : Formula} {τ : Trail}
    (hF : Satisfies a F) (hτ : TrailHolds a τ) : hasConflict F τ = false := by
  rw [hasConflict, Bool.or_eq_false_iff, List.any_eq_false, List.any_eq_false]
  refine ⟨fun l hl hf => ?_, ?_⟩
  · have h1 := hτ l hl
    rw [falsified_eval hτ (by simpa using hf)] at h1
    exact Bool.false_ne_true h1
  intro C hC hall
  have hCtrue := (Satisfies_iff a F).1 hF C hC
  obtain ⟨l, hl, hlt⟩ := (Clause.eval_eq_true_iff a C).1 hCtrue
  have := falsified_eval hτ ((List.all_eq_true.1 (by simpa using hall)) l hl)
  rw [this] at hlt
  exact Bool.false_ne_true hlt

theorem mem_unitLits {τ : Trail} {C : Clause} {l : Lit} :
    l ∈ unitLits τ C ↔ l ∈ C ∧ ∀ m ∈ C, m = l ∨ falsified τ m = true := by
  simp [unitLits, forces, List.mem_filter, List.all_eq_true]

theorem mem_upRound {F : Formula} {τ : Trail} {l : Lit} :
    l ∈ upRound F τ ↔ l ∈ τ ∨ ∃ C ∈ F, l ∈ unitLits τ C := by
  simp only [upRound, List.mem_append, List.mem_filter, List.mem_flatMap,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hl : l ∈ τ
      · exact Or.inl hl
      · exact Or.inr ⟨h, hl⟩

theorem TrailHolds_upRound {a : Assignment} {F : Formula} {τ : Trail}
    (hF : Satisfies a F) (hτ : TrailHolds a τ) : TrailHolds a (upRound F τ) := by
  intro l hl
  rcases mem_upRound.1 hl with h | ⟨C, hC, hu⟩
  · exact hτ l h
  · obtain ⟨-, hforce⟩ := mem_unitLits.1 hu
    obtain ⟨m, hm, hmt⟩ := (Clause.eval_eq_true_iff a C).1 ((Satisfies_iff a F).1 hF C hC)
    rcases hforce m hm with rfl | hf
    · exact hmt
    · rw [falsified_eval hτ hf] at hmt
      exact absurd hmt Bool.false_ne_true

/-- Soundness of bounded unit propagation: a conflict is impossible from a trail that
some model of `F` makes true. -/
theorem unitProp_conflict_sound {a : Assignment} {F : Formula} (hF : Satisfies a F) :
    ∀ (n : Nat) (τ : Trail), TrailHolds a τ → unitProp n F τ ≠ .conflict := by
  intro n
  induction n with
  | zero =>
    intro τ hτ
    simp [unitProp, hasConflict_false_of_model hF hτ]
  | succ n ih =>
    intro τ hτ
    simp only [unitProp, hasConflict_false_of_model hF hτ, Bool.false_eq_true, ↓reduceIte]
    exact ih _ (TrailHolds_upRound hF hτ)

theorem TrailHolds_negClause_iff (a : Assignment) (C : Clause) :
    TrailHolds a (negClause C) ↔ C.eval a = false := by
  simp only [TrailHolds, negClause, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Lit.eval_neg, Bool.not_eq_eq_eq_not, Bool.not_true,
    Clause.eval_eq_false_iff]

/-! ## Monotonicity at a fixed budget -/

/-- Trail inclusion (as sets). -/
def TrailSub (τ τ' : Trail) : Prop := ∀ l ∈ τ, l ∈ τ'

/-- Formula inclusion (as sets of clauses). -/
def FormulaSub (F G : Formula) : Prop := ∀ C ∈ F, C ∈ G

theorem falsified_mono {τ τ' : Trail} (h : TrailSub τ τ') {l : Lit}
    (hf : falsified τ l = true) : falsified τ' l = true := by
  simp only [falsified, decide_eq_true_eq] at hf ⊢
  exact h _ hf

theorem hasConflict_mono {F G : Formula} {τ τ' : Trail} (hFG : FormulaSub F G)
    (hτ : TrailSub τ τ') (h : hasConflict F τ = true) : hasConflict G τ' = true := by
  simp only [hasConflict, Bool.or_eq_true, List.any_eq_true, List.all_eq_true] at h ⊢
  rcases h with ⟨l, hl, hf⟩ | ⟨C, hC, hall⟩
  · exact Or.inl ⟨l, hτ l hl, falsified_mono hτ hf⟩
  · exact Or.inr ⟨C, hFG C hC, fun l hl => falsified_mono hτ (hall l hl)⟩

theorem upRound_mono {F G : Formula} {τ τ' : Trail} (hFG : FormulaSub F G)
    (hτ : TrailSub τ τ') : TrailSub (upRound F τ) (upRound G τ') := by
  intro l hl
  rcases mem_upRound.1 hl with h | ⟨C, hC, hu⟩
  · exact mem_upRound.2 (Or.inl (hτ l h))
  · obtain ⟨hlC, hforce⟩ := mem_unitLits.1 hu
    refine mem_upRound.2 (Or.inr ⟨C, hFG C hC, mem_unitLits.2 ⟨hlC, fun m hm => ?_⟩⟩)
    rcases hforce m hm with h | h
    · exact Or.inl h
    · exact Or.inr (falsified_mono hτ h)

theorem TrailSub_upRound (F : Formula) (τ : Trail) : TrailSub τ (upRound F τ) :=
  fun _ h => mem_upRound.2 (Or.inl h)

/-- At a fixed budget, a conflict persists when the formula and the trail grow. -/
theorem unitProp_conflict_mono {F G : Formula} (hFG : FormulaSub F G) :
    ∀ (n : Nat) {τ τ' : Trail}, TrailSub τ τ' →
      unitProp n F τ = .conflict → unitProp n G τ' = .conflict := by
  intro n
  induction n with
  | zero =>
    intro τ τ' hτ h
    simp only [unitProp] at h ⊢
    by_cases hc : hasConflict F τ = true
    · simp [hasConflict_mono hFG hτ hc]
    · simp [hc] at h
  | succ n ih =>
    intro τ τ' hτ h
    simp only [unitProp] at h ⊢
    by_cases hc : hasConflict F τ = true
    · simp [hasConflict_mono hFG hτ hc]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
      have := ih (upRound_mono hFG hτ) h
      split <;> simp_all

/-- A conflict found within `n` rounds is still found with a larger budget. -/
theorem unitProp_conflict_mono_fuel {F : Formula} :
    ∀ (n : Nat) {τ : Trail}, unitProp n F τ = .conflict → unitProp (n + 1) F τ = .conflict := by
  intro n
  induction n with
  | zero =>
    intro τ h
    simp only [unitProp] at h ⊢
    split at h <;> simp_all
  | succ n ih =>
    intro τ h
    simp only [unitProp] at h ⊢
    split
    · rfl
    · simp_all only [Bool.false_eq_true, ↓reduceIte]
      exact ih h

theorem unitProp_conflict_le_fuel {F : Formula} {τ : Trail} {n m : Nat} (hnm : n ≤ m)
    (h : unitProp n F τ = .conflict) : unitProp m F τ = .conflict := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact unitProp_conflict_mono_fuel _ ih

/-! ## Certifying that no conflict is ever found -/

/-- Propagation from `τ` never reports a conflict, at any budget. -/
def NeverConflict (F : Formula) (τ : Trail) : Prop := ∀ n, unitProp n F τ ≠ .conflict

/-- A trail closed under propagation (`upRound` adds nothing) and conflict-free never
reaches a conflict. -/
theorem neverConflict_of_closed {F : Formula} {τ : Trail} (hclosed : upRound F τ = τ)
    (hc : hasConflict F τ = false) : NeverConflict F τ := by
  intro n
  induction n with
  | zero => simp [unitProp, hc]
  | succ n ih => simpa [unitProp, hc, hclosed] using ih

/-- One round can be peeled off: if `τ` is conflict-free and propagation never finds a
conflict from `upRound F τ`, it never finds one from `τ`. -/
theorem neverConflict_of_step {F : Formula} {τ : Trail} (hc : hasConflict F τ = false)
    (h : NeverConflict F (upRound F τ)) : NeverConflict F τ := by
  intro n
  cases n with
  | zero => simp [unitProp, hc]
  | succ n => simpa [unitProp, hc] using h n

/-! ## Examples -/

section Examples

/-- Positive example: in `(¬x₀ ∨ x₁)` with `x₀` on the trail, the clause forces `x₁`. -/
theorem unitLits_example_pos : unitLits [Lit.p 0] [Lit.n 0, Lit.p 1] = [Lit.p 1] := by decide

/-- Negative example: with an empty trail, `x₀ ∨ x₁` forces nothing. -/
theorem unitLits_example_neg : unitLits [] [Lit.p 0, Lit.p 1] = [] := by decide

/-- Positive example: `x₀`, `¬x₀ ∨ x₁`, `¬x₁` propagate to a conflict within two rounds. -/
theorem unitProp_example_pos :
    unitProp 2 [[Lit.p 0], [Lit.n 0, Lit.p 1], [Lit.n 1]] [] = .conflict := by decide

/-- Negative example: `x₀ ∨ x₁`, `¬x₀ ∨ x₁` (satisfiable, no unit clause) never yield a
conflict from the empty trail, at any budget. -/
theorem unitProp_example_neg :
    NeverConflict [[Lit.p 0, Lit.p 1], [Lit.n 0, Lit.p 1]] [] :=
  neverConflict_of_closed (by decide) (by decide)

/-- Example of the trail outcome: from the empty trail, `x₀` and `¬x₀ ∨ x₁` propagate
`x₀` then `x₁` and stop without conflict. -/
theorem unitProp_example_trail :
    unitProp 3 [[Lit.p 0], [Lit.n 0, Lit.p 1]] [] = .trail [Lit.p 0, Lit.p 1] := by decide

/-- Example: a clause with a repeated literal forces that literal, so `(x₀ ∨ x₀) ∧ (¬x₀ ∨ ¬x₀)`
propagates to a conflict within one round. -/
theorem unitProp_example_dup_lits :
    unitProp 1 [[Lit.p 0, Lit.p 0], [Lit.n 0, Lit.n 0]] [] = .conflict := by decide

/-- Example: a trail containing a complementary pair is a conflict at budget 0 even for the
empty formula. -/
theorem unitProp_example_trail_pair : unitProp 0 [] [Lit.n 0, Lit.p 0] = .conflict := by decide

/-- Negative example of `NeverConflict`: from the empty trail, `x₀ ∧ ¬x₀` reaches a conflict
within one round. -/
theorem NeverConflict_example_neg : ¬ NeverConflict [[Lit.p 0], [Lit.n 0]] [] :=
  fun h => h 1 (by decide)

/-- Positive example of `FormulaSub`: every clause of `x₀` occurs in `x₁ ∧ x₀`. -/
theorem FormulaSub_example_pos : FormulaSub [[Lit.p 0]] [[Lit.p 1], [Lit.p 0]] := by
  intro C hC
  rcases List.mem_cons.1 hC with rfl | h
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · cases h

/-- Negative example of `FormulaSub`: the clause `x₀` does not occur in `x₁`. -/
theorem FormulaSub_example_neg : ¬ FormulaSub [[Lit.p 0]] [[Lit.p 1]] := by
  intro h
  exact absurd (h [Lit.p 0] List.mem_cons_self) (by decide)

end Examples

end Toy.Drat
