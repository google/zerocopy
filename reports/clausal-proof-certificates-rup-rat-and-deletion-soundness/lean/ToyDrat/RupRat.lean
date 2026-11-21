import ToyDrat.UnitProp

/-!
# RUP and RAT

* `RUP F C` (reverse unit propagation, also called asymmetric tautology): assuming
  every literal of `C` false and unit-propagating over `F` yields a conflict.
* `RATOn F C p` (resolution asymmetric tautology on `p`): for every clause `D ∈ F`
  containing `¬p`, the clause `C ∪ (D \ {¬p})` is RUP w.r.t. `F`.
* `RAT F C`: `RATOn` on the *first* literal of `C`, the pivot fixed by the DRAT
  proof format.

`RUP` and `RAT` are the propositional notions (propagation to any finite depth);
`rupCheck` and `ratCheck` are budgeted checkers, sound for every budget.
-/

namespace Toy.Drat

/-- `C` is a reverse-unit-propagation (RUP) consequence of `F`: assuming all literals of
`C` false, unit propagation over `F` reaches a conflict within some finite budget. -/
def RUP (F : Formula) (C : Clause) : Prop := ∃ n, unitProp n F (negClause C) = .conflict

/-- Budgeted RUP checker: propagate for `fuel` rounds from the negation of `C`. -/
def rupCheck (fuel : Nat) (F : Formula) (C : Clause) : Bool :=
  unitProp fuel F (negClause C) == .conflict

/-- The clause checked against `D` when `C` is RAT on `p`: `C ∪ (D \ {¬p})`
(the pivot `p` itself stays in the clause, following the DRAT literature). -/
def resolventOn (C D : Clause) (p : Lit) : Clause := C ++ D.filter (fun m => decide (m ≠ p.neg))

/-- `C` is RAT on literal `p` w.r.t. `F`: every resolution candidate on `p` is RUP.
Membership `p ∈ C` is *not* part of this predicate, unlike the literature definition of
"RAT on `p`", which requires `p ∈ C`. Without `p ∈ C` it does not preserve
satisfiability (`ratOn_without_mem_unsound`); every result using it for satisfiability
assumes `p ∈ C` separately, and `RAT` below fixes `p` to be the first literal of `C`. -/
def RATOn (F : Formula) (C : Clause) (p : Lit) : Prop :=
  ∀ D ∈ F, p.neg ∈ D → RUP F (resolventOn C D p)

/-- `C` is RAT w.r.t. `F` on its first literal, the pivot designated by the DRAT format.
The empty clause has no pivot and is never RAT. -/
def RAT (F : Formula) : Clause → Prop
  | [] => False
  | p :: rest => RATOn F (p :: rest) p

/-- Budgeted RAT checker on the first literal. -/
def ratCheck (fuel : Nat) (F : Formula) : Clause → Bool
  | [] => false
  | p :: rest =>
    F.all (fun D => !decide (p.neg ∈ D) || rupCheck fuel F (resolventOn (p :: rest) D p))

/-- Make literal `p` true, leaving all other variables unchanged. -/
def setTrue (a : Assignment) (p : Lit) : Assignment := fun v => if v = p.var then p.pos else a v

/-- The model used for a RAT addition: keep `a` if it already satisfies `C`, otherwise
make the pivot `p` true. -/
def ratWitness (a : Assignment) (C : Clause) (p : Lit) : Assignment :=
  if C.eval a then a else setTrue a p

/-! ## Checker soundness and basic facts -/

theorem rupCheck_sound {fuel : Nat} {F : Formula} {C : Clause}
    (h : rupCheck fuel F C = true) : RUP F C :=
  ⟨fuel, by simpa [rupCheck] using h⟩

theorem ratCheck_sound {fuel : Nat} {F : Formula} {C : Clause}
    (h : ratCheck fuel F C = true) : RAT F C := by
  cases C with
  | nil => simp [ratCheck] at h
  | cons p rest =>
    intro D hD hpD
    simp only [ratCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not] at h
    rcases h D hD with h | h
    · exact absurd hpD h
    · exact rupCheck_sound h

theorem not_rup_of_neverConflict {F : Formula} {C : Clause}
    (h : NeverConflict F (negClause C)) : ¬ RUP F C :=
  fun ⟨n, hn⟩ => h n hn

theorem rupCheck_eq_false_of_neverConflict {fuel : Nat} {F : Formula} {C : Clause}
    (h : NeverConflict F (negClause C)) : rupCheck fuel F C = false := by
  cases hc : rupCheck fuel F C with
  | false => rfl
  | true => exact absurd (rupCheck_sound hc) (not_rup_of_neverConflict h)

theorem ratCheck_eq_false_of {fuel : Nat} {F : Formula} {p : Lit} {rest : Clause} {D : Clause}
    (hD : D ∈ F) (hneg : p.neg ∈ D) (h : rupCheck fuel F (resolventOn (p :: rest) D p) = false) :
    ratCheck fuel F (p :: rest) = false := by
  cases hc : ratCheck fuel F (p :: rest) with
  | false => rfl
  | true =>
    simp only [ratCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not] at hc
    rcases hc D hD with h1 | h1
    · exact absurd hneg h1
    · rw [h] at h1
      exact absurd h1 Bool.false_ne_true

/-- RUP is monotone: more clauses in the formula, more literals in the clause. -/
theorem rup_mono {F G : Formula} {C C' : Clause} (hFG : FormulaSub F G)
    (hC : ∀ l ∈ C, l ∈ C') (h : RUP F C) : RUP G C' := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, unitProp_conflict_mono hFG n ?_ hn⟩
  intro l hl
  simp only [negClause, List.mem_map] at hl ⊢
  obtain ⟨m, hm, rfl⟩ := hl
  exact ⟨m, hC m hm, rfl⟩

/-- The budgeted RUP checker is monotone in the formula at a fixed budget. -/
theorem rupCheck_mono_formula {fuel : Nat} {F G : Formula} {C : Clause}
    (hFG : FormulaSub F G) (h : rupCheck fuel F C = true) : rupCheck fuel G C = true := by
  simp only [rupCheck, beq_iff_eq] at h ⊢
  exact unitProp_conflict_mono hFG fuel (fun _ hl => hl) h

theorem setTrue_eval_self (a : Assignment) (p : Lit) : p.eval (setTrue a p) = true := by
  simp [Lit.eval, setTrue]

theorem setTrue_eval_of_var_ne (a : Assignment) (p : Lit) {m : Lit} (h : m.var ≠ p.var) :
    m.eval (setTrue a p) = m.eval a := by
  simp [Lit.eval, setTrue, h]

/-! ## RUP is implication -/

/-- **RUP soundness.** If propagating the negation of `C` over `F` reaches a conflict,
then every model of `F` satisfies `C`. -/
theorem rup_implies_entails {F : Formula} {C : Clause} (h : RUP F C) : Entails F C := by
  intro a ha
  obtain ⟨n, hn⟩ := h
  cases hC : C.eval a with
  | true => rfl
  | false =>
    exact absurd hn (unitProp_conflict_sound ha n _ ((TrailHolds_negClause_iff a C).2 hC))

/-- **RUP addition preserves logical equivalence.** -/
theorem rup_addition_preserves_equivalence {F : Formula} {C : Clause} (h : RUP F C) :
    Equivalent (C :: F) F := by
  intro a
  rw [Satisfies_cons]
  exact ⟨fun h' => h'.2, fun h' => ⟨rup_implies_entails h a h', h'⟩⟩

/-- Four clauses over variables 1 and 2 forming an unsatisfiable formula without unit
clauses: `(x₁∨x₂) ∧ (x₁∨¬x₂) ∧ (¬x₁∨x₂) ∧ (¬x₁∨¬x₂)`. -/
def fullSquare : Formula :=
  [[Lit.p 1, Lit.p 2], [Lit.p 1, Lit.n 2], [Lit.n 1, Lit.p 2], [Lit.n 1, Lit.n 2]]

theorem fullSquare_unsat : ¬ Satisfiable fullSquare := by
  rintro ⟨a, ha⟩
  simp only [Satisfies, Formula.eval, fullSquare, Clause.eval, Lit.eval, Lit.p, Lit.n,
    List.all_cons, List.any_cons, List.any_nil, List.all_nil, Bool.or_false,
    Bool.and_true] at ha
  cases h1 : a 1 <;> cases h2 : a 2 <;> simp [h1, h2] at ha

/-- **Unit propagation is incomplete.** `fullSquare` entails the empty clause (it is
unsatisfiable) but the empty clause is not RUP w.r.t. it: entailment does not imply RUP. -/
theorem entails_not_implies_rup : Entails fullSquare [] ∧ ¬ RUP fullSquare [] := by
  refine ⟨fun a ha => absurd ⟨a, ha⟩ fullSquare_unsat, ?_⟩
  exact not_rup_of_neverConflict (neverConflict_of_closed (by decide) (by decide))

/-- `x₀` added to each clause of `fullSquare`: the four clauses `x₀ ∨ ±x₁ ∨ ±x₂`. Satisfiable
(set `x₀` true), entails `x₀`, and contains no `¬x₀`. -/
def x0OrFullSquare : Formula :=
  [[Lit.p 0, Lit.p 1, Lit.p 2], [Lit.p 0, Lit.p 1, Lit.n 2],
   [Lit.p 0, Lit.n 1, Lit.p 2], [Lit.p 0, Lit.n 1, Lit.n 2]]

theorem x0OrFullSquare_entails_x0 : Entails x0OrFullSquare [Lit.p 0] := by
  intro a ha
  simp only [Satisfies, Formula.eval, x0OrFullSquare, Clause.eval, Lit.eval, Lit.p, Lit.n,
    List.all_cons, List.any_cons, List.any_nil, List.all_nil, Bool.or_false,
    Bool.and_true] at ha ⊢
  cases h0 : a 0 <;> cases h1 : a 1 <;> cases h2 : a 2 <;> simp_all

theorem x0OrFullSquare_not_rup_x0 : ¬ RUP x0OrFullSquare [Lit.p 0] :=
  not_rup_of_neverConflict (neverConflict_of_closed (by decide) (by decide))

/-- **Incompleteness is not confined to unsatisfiable formulas or the empty clause.** The
satisfiable formula `x0OrFullSquare` entails the nonempty clause `x₀`, which is not RUP
w.r.t. it at any budget (propagation from `¬x₀` assigns nothing). -/
theorem entails_not_implies_rup_satisfiable_nonempty :
    Satisfiable x0OrFullSquare ∧ Entails x0OrFullSquare [Lit.p 0] ∧
      ¬ RUP x0OrFullSquare [Lit.p 0] :=
  ⟨⟨fun _ => true, by decide⟩, x0OrFullSquare_entails_x0, x0OrFullSquare_not_rup_x0⟩

/-- **RUP is sufficient, not necessary, for preserving equivalence.** `x₀` is RAT (vacuously:
no clause contains `¬x₀`) but not RUP w.r.t. the satisfiable `x0OrFullSquare`, and adding it
preserves logical equivalence because it is entailed. -/
theorem rat_not_rup_addition_preserves_equivalence :
    Satisfiable x0OrFullSquare ∧ RAT x0OrFullSquare [Lit.p 0] ∧
      ratCheck 0 x0OrFullSquare [Lit.p 0] = true ∧ ¬ RUP x0OrFullSquare [Lit.p 0] ∧
      Equivalent ([Lit.p 0] :: x0OrFullSquare) x0OrFullSquare :=
  ⟨⟨fun _ => true, by decide⟩, ratCheck_sound (fuel := 0) (by decide), by decide,
    x0OrFullSquare_not_rup_x0, (equivalent_cons_iff_entails _ _).2 x0OrFullSquare_entails_x0⟩

/-! ## RAT preserves satisfiability, not equivalence -/

/-- **RAT witness.** If `p ∈ C`, `C` is RAT on `p` w.r.t. `F`, and `a` is a model of `F`,
then `ratWitness a C p` (keep `a` if it satisfies `C`, else set `p` true) is a model of
`C ∧ F`. -/
theorem ratOn_witness_satisfies {F : Formula} {C : Clause} {p : Lit} {a : Assignment}
    (hp : p ∈ C) (hrat : RATOn F C p) (ha : Satisfies a F) :
    Satisfies (ratWitness a C p) (C :: F) := by
  unfold ratWitness
  cases hC : C.eval a with
  | true => exact (Satisfies_cons _ _ _).2 ⟨hC, ha⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hpa : p.eval a = false := (Clause.eval_eq_false_iff a C).1 hC p hp
    rw [Satisfies_cons]
    refine ⟨(Clause.eval_eq_true_iff _ _).2 ⟨p, hp, setTrue_eval_self a p⟩, ?_⟩
    rw [Satisfies_iff]
    intro E hE
    obtain ⟨m, hm, hmt⟩ := (Clause.eval_eq_true_iff a E).1 ((Satisfies_iff a F).1 ha E hE)
    by_cases hv : m.var = p.var
    · rcases Lit.eq_or_eq_neg_of_var_eq hv with rfl | rfl
      · rw [hpa] at hmt
        exact absurd hmt Bool.false_ne_true
      · have hent := rup_implies_entails (hrat E hE hm) a ha
        rw [resolventOn, Clause.eval_eq_true_iff] at hent
        obtain ⟨m', hm', hm't⟩ := hent
        rw [List.mem_append] at hm'
        rcases hm' with hm' | hm'
        · rw [(Clause.eval_eq_false_iff a C).1 hC m' hm'] at hm't
          exact absurd hm't Bool.false_ne_true
        · rw [List.mem_filter] at hm'
          obtain ⟨hm'E, hne⟩ := hm'
          have hne : m' ≠ p.neg := by simpa using hne
          have hv' : m'.var ≠ p.var := by
            intro hv'
            rcases Lit.eq_or_eq_neg_of_var_eq hv' with rfl | rfl
            · rw [hpa] at hm't
              exact absurd hm't Bool.false_ne_true
            · exact hne rfl
          exact (Clause.eval_eq_true_iff _ _).2
            ⟨m', hm'E, by rw [setTrue_eval_of_var_ne a p hv']; exact hm't⟩
    · exact (Clause.eval_eq_true_iff _ _).2
        ⟨m, hm, by rw [setTrue_eval_of_var_ne a p hv]; exact hmt⟩

/-- RAT on any literal of the clause preserves satisfiability. -/
theorem ratOn_preserves_satisfiability {F : Formula} {C : Clause} {p : Lit}
    (hp : p ∈ C) (hrat : RATOn F C p) (hF : Satisfiable F) : Satisfiable (C :: F) :=
  let ⟨a, ha⟩ := hF
  ⟨ratWitness a C p, ratOn_witness_satisfies hp hrat ha⟩

/-- **RAT addition preserves satisfiability** (pivot = first literal). -/
theorem rat_addition_preserves_satisfiability {F : Formula} {C : Clause}
    (hrat : RAT F C) (hF : Satisfiable F) : Satisfiable (C :: F) := by
  cases C with
  | nil => exact absurd hrat id
  | cons p rest => exact ratOn_preserves_satisfiability (List.mem_cons_self) hrat hF

/-- RAT addition yields an equisatisfiable formula. -/
theorem rat_addition_equisatisfiable {F : Formula} {C : Clause} (hrat : RAT F C) :
    Equisatisfiable (C :: F) F :=
  ⟨fun ⟨a, ha⟩ => ⟨a, ((Satisfies_cons _ _ _).1 ha).2⟩,
   rat_addition_preserves_satisfiability hrat⟩

/-- **RAT addition does not preserve equivalence.** `x₀` is RAT w.r.t. `F = x₁` (no clause
contains `¬x₀`), yet the model `x₁ = true, x₀ = false` of `F` is not a model of `x₀ ∧ F`;
in particular `F` does not entail the added clause. -/
theorem rat_addition_not_equivalence :
    RAT [[Lit.p 1]] [Lit.p 0] ∧ Satisfies (fun v => v == 1) [[Lit.p 1]] ∧
      ¬ Satisfies (fun v => v == 1) [[Lit.p 0], [Lit.p 1]] ∧
      ¬ Equivalent [[Lit.p 0], [Lit.p 1]] [[Lit.p 1]] ∧ ¬ Entails [[Lit.p 1]] [Lit.p 0] := by
  refine ⟨?_, by decide, by decide, ?_, ?_⟩
  · intro D hD hneg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    subst hD
    exact absurd hneg (by decide)
  · intro h
    exact absurd ((h (fun v => v == 1)).2 (by decide)) (by decide)
  · intro h
    exact absurd (h (fun v => v == 1) (by decide)) (by decide)

/-- **RAT addition can remove a model even on the variables of `F`.** The pivot variable `x₀`
already occurs in `F = ¬x₀ ∨ x₁`; the blocked clause `x₀ ∨ ¬x₁` is RAT on `x₀`, `F` has the
model `x₀ = false, x₁ = true`, and no model of `(x₀ ∨ ¬x₁) ∧ F` agrees with it on `x₀` and
`x₁`. So RAT additions need not preserve the models of `F` restricted to the variables of
`F` (unlike an extension by definitions of fresh variables). -/
theorem rat_addition_loses_projected_model :
    RAT [[Lit.n 0, Lit.p 1]] [Lit.p 0, Lit.n 1] ∧
      Satisfies (fun v => v == 1) [[Lit.n 0, Lit.p 1]] ∧
      ∀ b : Assignment, b 0 = false → b 1 = true →
        ¬ Satisfies b [[Lit.p 0, Lit.n 1], [Lit.n 0, Lit.p 1]] := by
  refine ⟨ratCheck_sound (fuel := 0) (by decide), by decide, fun b h0 h1 hb => ?_⟩
  simp [Satisfies, Formula.eval, Clause.eval, Lit.eval, Lit.p, Lit.n, h0, h1] at hb

/-- **RAT is not monotone in the formula.** `x₀` is RAT w.r.t. `x₁` (vacuously), but not w.r.t.
`¬x₀ ∧ x₁`, which contains every clause of `x₁`. (Contrast `rup_mono`: RUP is monotone.) -/
theorem rat_not_monotone_in_formula :
    RAT [[Lit.p 1]] [Lit.p 0] ∧ FormulaSub [[Lit.p 1]] [[Lit.n 0], [Lit.p 1]] ∧
      ¬ RAT [[Lit.n 0], [Lit.p 1]] [Lit.p 0] := by
  refine ⟨rat_addition_not_equivalence.1,
    fun D hD => List.mem_cons_of_mem _ hD, fun h => ?_⟩
  have := h [Lit.n 0] List.mem_cons_self (by decide)
  have hres : resolventOn [Lit.p 0] [Lit.n 0] (Lit.p 0) = [Lit.p 0] := by decide
  rw [hres] at this
  exact not_rup_of_neverConflict
    (neverConflict_of_step (by decide) (neverConflict_of_closed (by decide) (by decide))) this

/-- **`RATOn` without `p ∈ C` does not preserve satisfiability.** The empty clause is
(vacuously) `RATOn` the literal `x₀ ∉ []` w.r.t. the empty formula, which is satisfiable,
while adding the empty clause makes it unsatisfiable. -/
theorem ratOn_without_mem_unsound :
    Lit.p 0 ∉ ([] : Clause) ∧ RATOn [] [] (Lit.p 0) ∧ Satisfiable [] ∧ ¬ Satisfiable [[]] :=
  ⟨by simp, fun _ hD => absurd hD List.not_mem_nil, ⟨fun _ => false, rfl⟩,
    not_satisfiable_of_nil_mem List.mem_cons_self⟩

/-- RUP implies RAT on *any* literal (the resolvents only add literals to `C`). -/
theorem rup_implies_ratOn {F : Formula} {C : Clause} (p : Lit) (h : RUP F C) : RATOn F C p :=
  fun _ _ _ => rup_mono (fun _ hC => hC) (fun _ hl => List.mem_append_left _ hl) h

/-- **RUP implies RAT for nonempty clauses.** -/
theorem rup_implies_rat_of_ne_nil {F : Formula} {C : Clause} (hne : C ≠ []) (h : RUP F C) :
    RAT F C := by
  cases C with
  | nil => exact absurd rfl hne
  | cons p rest => exact rup_implies_ratOn p h

/-- The empty clause can be RUP (here w.r.t. `x₀ ∧ ¬x₀`) but is never RAT: the
nonemptiness hypothesis of `rup_implies_rat_of_ne_nil` is needed. -/
theorem rup_nil_not_rat : RUP [[Lit.p 0], [Lit.n 0]] [] ∧ ¬ RAT [[Lit.p 0], [Lit.n 0]] [] :=
  ⟨⟨1, by decide⟩, id⟩

/-- **The RAT check is pivot-specific.** W.r.t. `F = ¬x₀`, the clause `x₀ ∨ x₁` is RAT on
its second literal `x₁` (no clause contains `¬x₁`) but neither RUP nor RAT on its first
literal; the reordered clause `x₁ ∨ x₀` is RAT. The budgeted first-literal checker
`ratCheck` accordingly rejects `x₀ ∨ x₁` at every budget and accepts `x₁ ∨ x₀` at budget 0,
so its verdict depends on literal order. -/
theorem rat_check_depends_on_pivot_order :
    RATOn [[Lit.n 0]] [Lit.p 0, Lit.p 1] (Lit.p 1) ∧ ¬ RAT [[Lit.n 0]] [Lit.p 0, Lit.p 1] ∧
      ¬ RUP [[Lit.n 0]] [Lit.p 0, Lit.p 1] ∧ RAT [[Lit.n 0]] [Lit.p 1, Lit.p 0] ∧
      (∀ fuel, ratCheck fuel [[Lit.n 0]] [Lit.p 0, Lit.p 1] = false) ∧
      ratCheck 0 [[Lit.n 0]] [Lit.p 1, Lit.p 0] = true := by
  have hnc : NeverConflict [[Lit.n 0]] (negClause [Lit.p 0, Lit.p 1]) :=
    neverConflict_of_closed (by decide) (by decide)
  have hnr : ¬ RUP [[Lit.n 0]] [Lit.p 0, Lit.p 1] := not_rup_of_neverConflict hnc
  have hvac : RATOn [[Lit.n 0]] [Lit.p 1, Lit.p 0] (Lit.p 1) := by
    intro D hD hneg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    subst hD
    exact absurd hneg (by decide)
  have hres : resolventOn [Lit.p 0, Lit.p 1] [Lit.n 0] (Lit.p 0) = [Lit.p 0, Lit.p 1] := by
    decide
  refine ⟨?_, ?_, hnr, hvac, fun fuel => ?_, by decide⟩
  · intro D hD hneg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    subst hD
    exact absurd hneg (by decide)
  · intro h
    exact hnr (hres ▸ h [Lit.n 0] (by simp) (by decide))
  · exact ratCheck_eq_false_of (D := [Lit.n 0]) List.mem_cons_self (by decide)
      (by rw [hres]; exact rupCheck_eq_false_of_neverConflict hnc)

/-! ## Examples -/

section Examples

/-- Positive example of `RUP`: `x₀ ∧ (¬x₀ ∨ x₁)` RUP-derives `x₁`. -/
theorem RUP_example_pos : RUP [[Lit.p 0], [Lit.n 0, Lit.p 1]] [Lit.p 1] := ⟨1, by decide⟩

/-- Negative example of `RUP`: `x₀ ∨ x₁` does not RUP-derive `x₀` (no budget helps:
propagation from `¬x₀` adds `x₁` and then stops without conflict). -/
theorem RUP_example_neg : ¬ RUP [[Lit.p 0, Lit.p 1]] [Lit.p 0] :=
  not_rup_of_neverConflict
    (neverConflict_of_step (by decide) (neverConflict_of_closed (by decide) (by decide)))

/-- Positive example of `rupCheck` (budget 1). -/
theorem rupCheck_example_pos : rupCheck 1 [[Lit.p 0], [Lit.n 0, Lit.p 1]] [Lit.p 1] = true := by
  decide

/-- Negative example of `rupCheck`: budget 0 is too small for the previous instance
(budgeted checking is sound but incomplete for small budgets). -/
theorem rupCheck_example_neg : rupCheck 0 [[Lit.p 0], [Lit.n 0, Lit.p 1]] [Lit.p 1] = false := by
  decide

/-- Positive example of `RAT` (a blocked clause): w.r.t. `F = ¬x₀ ∨ x₁`, the clause
`x₀ ∨ ¬x₁` is RAT on `x₀`: its only resolution candidate `x₀ ∨ ¬x₁ ∨ x₁` is a tautology,
hence RUP. It is neither RUP nor entailed (see `RAT_example_pos_not_entailed`). -/
theorem RAT_example_pos : RAT [[Lit.n 0, Lit.p 1]] [Lit.p 0, Lit.n 1] :=
  ratCheck_sound (fuel := 0) (by decide)

/-- The blocked clause of `RAT_example_pos` is not entailed: the model `x₀ = false,
x₁ = true` of `¬x₀ ∨ x₁` falsifies `x₀ ∨ ¬x₁`. -/
theorem RAT_example_pos_not_entailed : ¬ Entails [[Lit.n 0, Lit.p 1]] [Lit.p 0, Lit.n 1] := by
  intro h
  exact absurd (h (fun v => v == 1) (by decide)) (by decide)

/-- Negative example of `RAT`: w.r.t. `¬x₀`, the unit clause `x₀` is not RAT. -/
theorem RAT_example_neg : ¬ RAT [[Lit.n 0]] [Lit.p 0] := by
  intro h
  have := h [Lit.n 0] (by simp) (by decide)
  exact not_rup_of_neverConflict (neverConflict_of_closed (by decide) (by decide)) this

/-- Positive example of `ratCheck` (vacuous: no clause contains `¬x₀`). -/
theorem ratCheck_example_pos : ratCheck 0 [[Lit.p 1]] [Lit.p 0] = true := by decide

/-- Positive example of `ratCheck` with a resolution candidate: w.r.t. `¬x₀ ∨ x₁`, the clause
`x₀ ∨ ¬x₁` is accepted because its only resolvent `x₀ ∨ ¬x₁ ∨ x₁` is RUP. -/
theorem ratCheck_example_pos_resolvent :
    ratCheck 0 [[Lit.n 0, Lit.p 1]] [Lit.p 0, Lit.n 1] = true := by decide

/-- Negative example of `ratCheck`: the empty clause is never accepted. -/
theorem ratCheck_example_neg (fuel : Nat) (F : Formula) : ratCheck fuel F [] = false := rfl

/-- Negative example of `ratCheck` on a nonempty clause: w.r.t. `¬x₀`, the clause `x₀` is
rejected (its resolvent `x₀` is not RUP). -/
theorem ratCheck_example_neg_nonempty : ratCheck 2 [[Lit.n 0]] [Lit.p 0] = false := by decide

/-- Positive example of `RATOn` on a non-first literal: w.r.t. `¬x₀`, the clause `x₀ ∨ x₁` is
`RATOn` its second literal `x₁`. -/
theorem RATOn_example_pos : RATOn [[Lit.n 0]] [Lit.p 0, Lit.p 1] (Lit.p 1) :=
  rat_check_depends_on_pivot_order.1

/-- Negative example of `RATOn`: w.r.t. `¬x₀`, the clause `x₀ ∨ x₁` is not `RATOn` `x₀`. -/
theorem RATOn_example_neg : ¬ RATOn [[Lit.n 0]] [Lit.p 0, Lit.p 1] (Lit.p 0) :=
  rat_check_depends_on_pivot_order.2.1

/-- Example of the RAT witness: starting from the all-false assignment (which falsifies the
clause `x₀`), the witness for adding `x₀` on pivot `x₀` makes `x₀` true. -/
theorem ratWitness_example :
    ratWitness (fun _ => false) [Lit.p 0] (Lit.p 0) 0 = true := by decide

end Examples

end Toy.Drat
