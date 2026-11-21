import ToyJunk.Agreement

/-!
# Result 2: the guarded fragment is conservative

For a formula accepted by the syntactic guard checker `guarded`, the human value is
defined at every environment and equals the total value under every junk record, for
either connective semantics and either reading of natural subtraction. Hence Lean-validity
and human-validity coincide on the guarded fragment. The checker is incomplete.

# Result 4: guard placement and closure

The left-to-right guard discipline accepts `b ≤ a ∧ P (a - b)` and rejects
`P (a - b) ∧ b ≤ a`; the guarded fragment is not closed under commutation of `∧` or under
contraposition, although both are equivalences in Lean's reading. Semantically, the class
of everywhere-defined formulas is closed under both under strong Kleene connectives, and
under neither with sequential connectives.
-/

namespace Toy.Junk

/-! ## Facts -/

/-- Every fact in `Γ` is human-true at `ρ`. -/
def FactsTrue (c : Conn) (r : SubReading) (Γ : List Formula) (ρ : Env) : Prop :=
  ∀ f ∈ Γ, hEval c r f ρ = some true

theorem factsTrue_append {c : Conn} {r : SubReading} {Γ Δ : List Formula} {ρ : Env}
    (h₁ : FactsTrue c r Γ ρ) (h₂ : FactsTrue c r Δ ρ) : FactsTrue c r (Γ ++ Δ) ρ := by
  intro f hf
  rcases List.mem_append.mp hf with h | h
  · exact h₁ f h
  · exact h₂ f h

/-- The facts of a human-true formula are human-true. -/
theorem factsTrue_facts (c : Conn) (r : SubReading) :
    ∀ (φ : Formula) (ρ : Env), hEval c r φ ρ = some true → FactsTrue c r φ.facts ρ := by
  intro φ
  induction φ with
  | eq t u | le t u | lt t u | dvd t u =>
    intro ρ h f hf
    simp only [Formula.facts, List.mem_singleton] at hf
    subst hf
    exact h
  | not φ _ =>
    intro ρ h f hf
    cases φ with
    | eq t u =>
      simp only [Formula.facts, List.mem_singleton] at hf
      subst hf
      exact h
    | _ => simp [Formula.facts] at hf
  | and φ ψ ih₁ ih₂ =>
    intro ρ h
    obtain ⟨h1, h2⟩ := tvAnd_eq_some_true.mp h
    exact factsTrue_append (ih₁ ρ h1) (ih₂ ρ h2)
  | or _ _ _ _ | imp _ _ _ _ | allNat _ _ _ | allInt _ _ _ | exNat _ _ _ | exInt _ _ _ =>
    intro ρ _ f hf
    simp [Formula.facts] at hf

/-! ## Term-level soundness -/

theorem hEvalT_zeroOf (r : SubReading) (ρ : Env) (s : Srt) : hEvalT r ρ (zeroOf s) = some 0 := by
  cases s <;> rfl

theorem hSub_nat_of_le (r : SubReading) (J : Junk) (x y : Nat) (h : (y : Int) ≤ x) :
    hSub r .nat (x : Int) (y : Int) = some (Srt.toInt .nat (jSub J .nat x y)) := by
  have h' : y ≤ x := by omega
  cases r <;> simp only [hSub, jSub, Srt.toInt, h, h', ↓reduceIte, Option.some.injEq] <;> omega

theorem mem_of_contains {Γ : List Formula} {f : Formula} (h : Γ.contains f = true) : f ∈ Γ := by
  simpa using h

/-- Term-level soundness of the guard discipline: if all facts in `Γ` are human-true and
`t` is guarded by `Γ`, then the human value of `t` is defined and equals its total value
under every junk record. -/
theorem hEvalT_eq_of_guardedIn (c : Conn) (r : SubReading) (J : Junk) (ρ : Env)
    (Γ : List Formula) (hΓ : FactsTrue c r Γ ρ) :
    ∀ {s : Srt} (t : Term s), t.guardedIn Γ = true →
      hEvalT r ρ t = some (s.toInt (evalT J ρ t)) := by
  intro s t
  induction t with
  | natVar i => intro _; rfl
  | intVar i => intro _; rfl
  | natLit n => intro _; rfl
  | intLit z => intro _; rfl
  | @add s t u iht ihu =>
    intro hg
    simp only [Term.guardedIn, Bool.and_eq_true] at hg
    simp only [hEvalT, iht hg.1, ihu hg.2, obind2, evalT, toInt_opAdd]
  | @mul s t u iht ihu =>
    intro hg
    simp only [Term.guardedIn, Bool.and_eq_true] at hg
    simp only [hEvalT, iht hg.1, ihu hg.2, obind2, evalT, toInt_opMul]
  | @sub s t u iht ihu =>
    cases s
    · intro hg
      simp only [Term.guardedIn, Bool.and_eq_true] at hg
      obtain ⟨⟨hgt, hgu⟩, hc⟩ := hg
      have hf := hΓ _ (mem_of_contains hc)
      simp only [hEval, iht hgt, ihu hgu, hAtom, Option.some.injEq, decide_eq_true_eq] at hf
      simp only [hEvalT, iht hgt, ihu hgu, obind2, evalT]
      exact hSub_nat_of_le r J _ _ hf
    · intro hg
      simp only [Term.guardedIn, Bool.and_eq_true] at hg
      simp only [hEvalT, iht hg.1, ihu hg.2, obind2, evalT, hSub, jSub, Srt.toInt]
  | @div s t u iht ihu =>
    intro hg
    simp only [Term.guardedIn, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨hgt, hgu⟩, hc0⟩, hcd⟩ := hg
    have h0 := hΓ _ (mem_of_contains hc0)
    have hd := hΓ _ (mem_of_contains hcd)
    simp only [hEval, ihu hgu, hEvalT_zeroOf, hAtom, tvNot, Option.map_some,
      Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at h0
    simp only [hEval, iht hgt, ihu hgu, hAtom, Option.some.injEq, decide_eq_true_eq] at hd
    have hdiv : hDiv (s.toInt (evalT J ρ t)) (s.toInt (evalT J ρ u)) =
        some (s.toInt (evalT J ρ t) / s.toInt (evalT J ρ u)) := by
      simp [hDiv, DivDom, h0, hd]
    simp only [hEvalT, iht hgt, ihu hgu, obind2, evalT, hdiv,
      toInt_jDiv_of_hDiv J s _ _ _ hdiv]
  | @mod s t u iht ihu =>
    cases s
    · intro hg
      simp only [Term.guardedIn, Bool.and_eq_true] at hg
      obtain ⟨⟨hgt, hgu⟩, hc0⟩ := hg
      have h0 := hΓ _ (mem_of_contains hc0)
      simp only [hEval, ihu hgu, hAtom, tvNot, Option.map_some, hEvalT,
        Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at h0
      have hne : Srt.toInt .nat (evalT J ρ u) ≠ 0 := by simpa using h0
      have hm : ModDom (Srt.toInt .nat (evalT J ρ t)) (Srt.toInt .nat (evalT J ρ u)) :=
        ⟨Int.natCast_nonneg _, by simp only [Srt.toInt] at hne ⊢; omega⟩
      have hmod : hMod (Srt.toInt .nat (evalT J ρ t)) (Srt.toInt .nat (evalT J ρ u)) =
          some (Srt.toInt .nat (evalT J ρ t) % Srt.toInt .nat (evalT J ρ u)) := by
        simp only [hMod, hm, ↓reduceIte]
      simp only [hEvalT, iht hgt, ihu hgu, obind2, evalT, hmod,
        toInt_jMod_of_hMod J .nat _ _ _ hmod]
    · intro hg
      simp only [Term.guardedIn, Bool.and_eq_true] at hg
      obtain ⟨⟨⟨hgt, hgu⟩, hcu⟩, hct⟩ := hg
      have hu := hΓ _ (mem_of_contains hcu)
      have ht := hΓ _ (mem_of_contains hct)
      simp only [hEval, ihu hgu, hAtom, hEvalT, Option.some.injEq, decide_eq_true_eq] at hu
      simp only [hEval, iht hgt, hAtom, hEvalT, Option.some.injEq, decide_eq_true_eq] at ht
      have hm : ModDom (Srt.toInt .int (evalT J ρ t)) (Srt.toInt .int (evalT J ρ u)) := ⟨ht, hu⟩
      have hmod : hMod (Srt.toInt .int (evalT J ρ t)) (Srt.toInt .int (evalT J ρ u)) =
          some (Srt.toInt .int (evalT J ρ t) % Srt.toInt .int (evalT J ρ u)) := by
        simp only [hMod, hm, ↓reduceIte]
      simp only [hEvalT, iht hgt, ihu hgu, obind2, evalT, hmod,
        toInt_jMod_of_hMod J .int _ _ _ hmod]
  | cast t iht =>
    intro hg
    simp only [Term.guardedIn] at hg
    simp only [hEvalT, iht hg, evalT, Srt.toInt]
  | toNat t iht =>
    intro hg
    simp only [Term.guardedIn, Bool.and_eq_true] at hg
    obtain ⟨hgt, hc⟩ := hg
    have h0 := hΓ _ (mem_of_contains hc)
    simp only [hEval, iht hgt, hAtom, hEvalT, Option.some.injEq, decide_eq_true_eq] at h0
    have hz : hToNat (Srt.toInt .int (evalT J ρ t)) = some (Srt.toInt .int (evalT J ρ t)) := by
      simp only [hToNat, h0, ↓reduceIte]
    show (hEvalT r ρ t).bind hToNat = some (Srt.toInt .nat (jToNat J (evalT J ρ t)))
    rw [iht hgt, Option.bind_some, hz]
    exact congrArg some (toInt_jToNat_of_hToNat J _ _ hz).symm

/-! ## Formula-level soundness -/

/-- Soundness of the guard discipline relative to facts `Γ`. -/
theorem hEval_eq_some_evalJ_of_guardedIn (c : Conn) (r : SubReading) (J : Junk) :
    ∀ (φ : Formula) (Γ : List Formula) (ρ : Env), FactsTrue c r Γ ρ →
      φ.guardedIn Γ = true → hEval c r φ ρ = some (evalJ J φ ρ) := by
  intro φ
  induction φ with
  | eq t u | le t u | lt t u | dvd t u =>
    intro Γ ρ hΓ hg
    simp only [Formula.guardedIn, Bool.and_eq_true] at hg
    simp only [hEval, evalJ, hEvalT_eq_of_guardedIn c r J ρ Γ hΓ t hg.1,
      hEvalT_eq_of_guardedIn c r J ρ Γ hΓ u hg.2, hAtom]
  | not φ ih =>
    intro Γ ρ hΓ hg
    simp only [Formula.guardedIn] at hg
    simp [hEval, evalJ, ih Γ ρ hΓ hg, tvNot]
  | and φ ψ ih₁ ih₂ =>
    intro Γ ρ hΓ hg
    simp only [Formula.guardedIn, Bool.and_eq_true] at hg
    have h1 := ih₁ Γ ρ hΓ hg.1
    simp only [hEval, evalJ, h1]
    cases hb : evalJ J φ ρ
    · simp [tvAnd_some_false]
    · rw [hb] at h1
      have hf := factsTrue_append hΓ (factsTrue_facts c r φ ρ h1)
      rw [ih₂ _ ρ hf hg.2, tvAnd_some_true_some]
      simp
  | or φ ψ ih₁ ih₂ =>
    intro Γ ρ hΓ hg
    simp only [Formula.guardedIn, Bool.and_eq_true] at hg
    simp only [hEval, evalJ, ih₁ Γ ρ hΓ hg.1, ih₂ Γ ρ hΓ hg.2, tvOr_some_some]
  | imp φ ψ ih₁ ih₂ =>
    intro Γ ρ hΓ hg
    simp only [Formula.guardedIn, Bool.and_eq_true] at hg
    have h1 := ih₁ Γ ρ hΓ hg.1
    simp only [hEval, evalJ, h1]
    cases hb : evalJ J φ ρ
    · simp [tvImp_some_false]
    · rw [hb] at h1
      have hf := factsTrue_append hΓ (factsTrue_facts c r φ ρ h1)
      rw [ih₂ _ ρ hf hg.2, tvImp_some_true_some]
      simp
  | allNat x φ ih | exNat x φ ih =>
    intro Γ ρ hΓ hg
    simp only [Formula.guardedIn] at hg
    have hv : ∀ v, hEval c r φ (ρ.setNat x v) = some (evalJ J φ (ρ.setNat x v)) := by
      intro v
      apply ih _ _ _ hg
      intro f hf
      rw [List.mem_filter] at hf
      rw [hEval_congr c r f (ρ.setNat x v) ρ]
      · exact hΓ f hf.1
      · intro i hi
        simp only [Env.setNat]
        split
        · rename_i hix
          subst hix
          simp [hi] at hf
        · rfl
      · intro i _
        rfl
    simp only [hEval, evalJ]
    rw [show (fun v => hEval c r φ (ρ.setNat x v)) = fun v => some (evalJ J φ (ρ.setNat x v))
      from funext hv]
    first
    | exact tvAll_some _
    | exact tvEx_some _
  | allInt x φ ih | exInt x φ ih =>
    intro Γ ρ hΓ hg
    simp only [Formula.guardedIn] at hg
    have hv : ∀ v, hEval c r φ (ρ.setInt x v) = some (evalJ J φ (ρ.setInt x v)) := by
      intro v
      apply ih _ _ _ hg
      intro f hf
      rw [List.mem_filter] at hf
      rw [hEval_congr c r f (ρ.setInt x v) ρ]
      · exact hΓ f hf.1
      · intro i _
        rfl
      · intro i hi
        simp only [Env.setInt]
        split
        · rename_i hix
          subst hix
          simp [hi] at hf
        · rfl
    simp only [hEval, evalJ]
    rw [show (fun v => hEval c r φ (ρ.setInt x v)) = fun v => some (evalJ J φ (ρ.setInt x v))
      from funext hv]
    first
    | exact tvAll_some _
    | exact tvEx_some _

/-- **Conservativity of the guarded fragment.** For every formula accepted by `guarded`,
every connective semantics `c`, every reading `r` of natural subtraction, every junk
record `J` and every environment `ρ`, the human value of `φ` at `ρ` is defined and equals
the total value of `φ` at `ρ` under `J`. -/
theorem hEval_eq_some_evalJ_of_guarded (c : Conn) (r : SubReading) (J : Junk) (φ : Formula)
    (ρ : Env) (hg : guarded φ = true) : hEval c r φ ρ = some (evalJ J φ ρ) :=
  hEval_eq_some_evalJ_of_guardedIn c r J φ [] ρ (by simp [FactsTrue]) hg

/-- Guarded formulas are defined everywhere (any connectives, any reading). -/
theorem definedEverywhere_of_guarded (c : Conn) (r : SubReading) (φ : Formula)
    (hg : guarded φ = true) : DefinedEverywhere c r φ := by
  intro ρ
  rw [hEval_eq_some_evalJ_of_guarded c r leanJ φ ρ hg]
  simp

/-- Guarded formulas are junk-independent. -/
theorem junkIndependent_of_guarded (φ : Formula) (hg : guarded φ = true) :
    JunkIndependent φ := by
  intro J J' ρ
  have h1 := hEval_eq_some_evalJ_of_guarded .kleene .partialNat J φ ρ hg
  have h2 := hEval_eq_some_evalJ_of_guarded .kleene .partialNat J' φ ρ hg
  rw [h1] at h2
  exact Option.some.inj h2

/-- **Validity transfer on the guarded fragment.** A guarded formula is valid in Lean's
reading iff it is valid in the human reading (any connectives, any reading). -/
theorem leanValid_iff_humanValid_of_guarded (c : Conn) (r : SubReading) (φ : Formula)
    (hg : guarded φ = true) : LeanValid φ ↔ HumanValid c r φ := by
  constructor
  · intro h ρ
    rw [hEval_eq_some_evalJ_of_guarded c r leanJ φ ρ hg, h ρ]
  · intro h ρ
    have := h ρ
    rw [hEval_eq_some_evalJ_of_guarded c r leanJ φ ρ hg] at this
    exact Option.some.inj this

/-! ## Non-vacuity, tightness and incompleteness -/

/-- Non-vacuity of result 2: `b ≤ a → a - b + b = a` is accepted by the checker. -/
theorem nv_guarded_subAddCancel : guarded fSubAddCancelGuarded = true := by decide

/-- The guard hypothesis is tight (witnessed at every environment): `(x : Int) / 0 = 0` is
rejected by the checker and its human value is undefined, so no conclusion `= some _` holds. -/
theorem ce_unguarded_divZero (c : Conn) (r : SubReading) :
    guarded fDivZero = false ∧ ∀ ρ, hEval c r fDivZero ρ = none := by
  refine ⟨by decide, ?_⟩
  intro ρ
  simp [hEval, fDivZero, hEvalT, obind2, hDiv, DivDom, hAtom]

/-- The guard hypothesis of the validity transfer is tight (witness: `(x : Int) / 0 = 0`,
Lean-valid since `Int` division by zero returns `0`, unguarded, and not human-valid). -/
theorem ce_unguarded_leanValid_not_humanValid (c : Conn) (r : SubReading) :
    guarded fDivZero = false ∧ LeanValid fDivZero ∧ ¬ HumanValid c r fDivZero := by
  obtain ⟨h1, h2, _, h3⟩ := And.intro (ce_unguarded_divZero c r).1 (ce_leanValid_not_humanValid c r)
  exact ⟨h1, h2, h3⟩

/-- The guard hypothesis of `junkIndependent_of_guarded` is tight (witness: `(0 : Nat) - 1 = 0`,
rejected by the checker and junk-dependent; Lean's truncated `0 - 1 = 0` is one junk choice). -/
theorem ce_unguarded_junkDependent :
    guarded fZeroSubOne = false ∧ ¬ JunkIndependent fZeroSubOne :=
  ⟨by decide, (ce_zeroSubOne_junkDependent .kleene).1⟩

/-- **Incompleteness for junk independence.** `(a - b) * 0 = 0` is junk-independent but
rejected by the checker. -/
theorem guarded_incomplete_junkIndependent :
    guarded fMulZero = false ∧ JunkIndependent fMulZero :=
  ⟨by decide, (ce_junkIndependent_not_definedEverywhere .kleene).1⟩

/-- `0 ≤ 0 ∨ a - b = 0` at `Nat`. -/
def fTrivOr : Formula := .or (.le (.natLit 0) (.natLit 0)) (.eq (.sub vA vB) (.natLit 0))

/-- **Incompleteness for definedness.** `0 ≤ 0 ∨ a - b = 0` is rejected by the checker,
which requires both disjuncts to be guarded (its right disjunct `a - b = 0` is not), yet
it is human-true at every environment under either connective semantics, because the left
disjunct `0 ≤ 0` is true and both semantics return true for a disjunction whose left side
is true. -/
theorem guarded_incomplete_defined (c : Conn) :
    guarded fTrivOr = false ∧ HumanValid c .partialNat fTrivOr := by
  refine ⟨by decide, ?_⟩
  intro ρ
  cases c <;> simp [hEval, fTrivOr, hEvalT, hAtom, tvOr]

/-- `¬ (b ≤ a) ∨ a - b + b = a` at `Nat` (a guard written as a negated left disjunct). -/
def fOrNegGuardSubCancel : Formula := .or (.not (.le vB vA)) fSubAddCancel

/-- `b = 0 ∨ a % b < b` at `Nat` (an idiomatic disjunctive guard). -/
def fModDisjGuard : Formula := .or (.eq vB (.natLit 0)) (.lt (.mod vA vB) vB)

/-- **Incompleteness for disjunctive guards.** For every connective semantics and reading,
`¬ (b ≤ a) ∨ a - b + b = a` and `b = 0 ∨ a % b < b` (at `Nat`) are rejected by the checker,
which adds no facts across `∨`, yet both are human-valid (defined and true at every
environment). -/
theorem guarded_incomplete_disjunctive_guards (c : Conn) (r : SubReading) :
    (guarded fOrNegGuardSubCancel = false ∧ HumanValid c r fOrNegGuardSubCancel) ∧
      (guarded fModDisjGuard = false ∧ HumanValid c r fModDisjGuard) := by
  refine ⟨⟨by decide, ?_⟩, ⟨by decide, ?_⟩⟩
  · intro ρ
    have hg : guarded fSubAddCancelGuarded = true := by decide
    have hv : LeanValid fSubAddCancelGuarded := by
      intro ρ
      rw [evalJ_leanJ_iff]
      show ρ.nat 1 ≤ ρ.nat 0 → ρ.nat 0 - ρ.nat 1 + ρ.nat 1 = ρ.nat 0
      omega
    exact (leanValid_iff_humanValid_of_guarded c r _ hg).mp hv ρ
  · intro ρ
    by_cases hb : ρ.nat 1 = 0
    · have hl : hEval c r (.eq vB (.natLit 0)) ρ = some true := by
        simp [hEval, hEvalT, hAtom, hb]
      show tvOr c (hEval c r (.eq vB (.natLit 0)) ρ) (hEval c r (.lt (.mod vA vB) vB) ρ) = some true
      rw [hl]
      cases c <;> rfl
    · have hl : hEval c r (.eq vB (.natLit 0)) ρ = some false := by
        simp [hEval, hEvalT, hAtom, hb]
      have hpos : (0 : Int) < (ρ.nat 1 : Int) := by omega
      have hm : ModDom (ρ.nat 0 : Int) (ρ.nat 1 : Int) := ⟨Int.natCast_nonneg _, hpos⟩
      have hlt : (ρ.nat 0 : Int) % (ρ.nat 1 : Int) < (ρ.nat 1 : Int) := Int.emod_lt_of_pos _ hpos
      have hr : hEval c r (.lt (.mod vA vB) vB) ρ = some true := by
        simp [hEval, hEvalT, obind2, hMod, hm, hAtom, hlt]
      show tvOr c (hEval c r (.eq vB (.natLit 0)) ρ) (hEval c r (.lt (.mod vA vB) vB) ρ) = some true
      rw [hl, hr]
      cases c <;> rfl

/-- `b ≤ a ∧ a < b → a - b = 1` at `Nat` (contradictory guards). -/
def fContradictoryGuard : Formula :=
  .imp (.and (.le vB vA) (.lt vA vB)) (.eq (.sub vA vB) (.natLit 1))

/-- `∃ b, b ≤ a → a - b = 1` at `Nat` (a bounded existential written with `→`). -/
def fExImpGuard : Formula := .exNat 1 (.imp (.le vB vA) (.eq (.sub vA vB) (.natLit 1)))

/-- `∃ b, b ≤ a ∧ a - b = 1` at `Nat` (the same bounded existential written with `∧`). -/
def fExAndGuard : Formula := .exNat 1 (.and (.le vB vA) (.eq (.sub vA vB) (.natLit 1)))

/-- **Acceptance by the checker does not detect vacuous guards.** For every connective
semantics and reading, `b ≤ a ∧ a < b → a - b = 1` and `∃ b, b ≤ a → a - b = 1` (at `Nat`)
are accepted by the checker, Lean-valid and human-valid, the first because its premise is
never true and the second because `b = a + 1` falsifies the premise; the `∧` form
`∃ b, b ≤ a ∧ a - b = 1` is not Lean-valid (it fails at `a = 0`). -/
theorem guarded_accepts_vacuous_guards (c : Conn) (r : SubReading) :
    (guarded fContradictoryGuard = true ∧ LeanValid fContradictoryGuard ∧
        HumanValid c r fContradictoryGuard) ∧
      (guarded fExImpGuard = true ∧ LeanValid fExImpGuard ∧ HumanValid c r fExImpGuard) ∧
      ¬ LeanValid fExAndGuard := by
  have hg1 : guarded fContradictoryGuard = true := by decide
  have hg2 : guarded fExImpGuard = true := by decide
  have hv1 : LeanValid fContradictoryGuard := by
    intro ρ
    rw [evalJ_leanJ_iff]
    show ρ.nat 1 ≤ ρ.nat 0 ∧ ρ.nat 0 < ρ.nat 1 → ρ.nat 0 - ρ.nat 1 = 1
    omega
  have hv2 : LeanValid fExImpGuard := by
    intro ρ
    rw [evalJ_leanJ_iff]
    refine ⟨ρ.nat 0 + 1, ?_⟩
    show (ρ.setNat 1 (ρ.nat 0 + 1)).nat 1 ≤ (ρ.setNat 1 (ρ.nat 0 + 1)).nat 0 →
      (ρ.setNat 1 (ρ.nat 0 + 1)).nat 0 - (ρ.setNat 1 (ρ.nat 0 + 1)).nat 1 = 1
    simp only [Env.setNat]
    simp
  refine ⟨⟨hg1, hv1, (leanValid_iff_humanValid_of_guarded c r _ hg1).mp hv1⟩,
    ⟨hg2, hv2, (leanValid_iff_humanValid_of_guarded c r _ hg2).mp hv2⟩, ?_⟩
  intro h
  obtain ⟨v, hv⟩ := (evalJ_leanJ_iff _ _).mp (h Env.zero)
  have h1 : (Env.zero.setNat 1 v).nat 1 ≤ (Env.zero.setNat 1 v).nat 0 ∧
      (Env.zero.setNat 1 v).nat 0 - (Env.zero.setNat 1 v).nat 1 = 1 := hv
  simp only [Env.setNat, Env.zero] at h1
  simp at h1

/-- `7 / 2 = 3` at `Nat`. -/
def fSevenDivTwo : Formula := .eq (.div (.natLit 7) (.natLit 2)) (.natLit 3)

/-- `7 % 2 = 1` at `Nat`. -/
def fSevenModTwo : Formula := .eq (.mod (.natLit 7) (.natLit 2)) (.natLit 1)

/-- `¬ (b = 0) → a / b * b + a % b = a` at `Nat` (the floor-division identity). -/
def fNatDivModId : Formula :=
  .imp (.not (.eq vB (.natLit 0))) (.eq (.add (.mul (.div vA vB) vB) (.mod vA vB)) vA)

/-- **Inexact division is junk in this model, inexact remainder is not.** Lean's, the
truncating and the flooring records give `7 / 2 = 3` at `Nat`, while `oneJ` gives `1`;
so `7 / 2 = 3` is junk-dependent and human-undefined, whereas `7 % 2 = 1` is
junk-independent and human-true. The floor-division identity
`¬ (b = 0) → a / b * b + a % b = a` at `Nat` is Lean-valid but rejected by the checker,
junk-dependent, and (for every connective semantics and reading) not defined everywhere. -/
theorem inexact_division_is_junk (c : Conn) (r : SubReading) :
    (evalT leanJ Env.zero (.div (.natLit 7) (.natLit 2)) = (3 : Nat) ∧
        evalT truncJ Env.zero (.div (.natLit 7) (.natLit 2)) = (3 : Nat) ∧
        evalT floorJ Env.zero (.div (.natLit 7) (.natLit 2)) = (3 : Nat) ∧
        evalT oneJ Env.zero (.div (.natLit 7) (.natLit 2)) = (1 : Nat)) ∧
      ¬ JunkIndependent fSevenDivTwo ∧ hEval c r fSevenDivTwo Env.zero = none ∧
      JunkIndependent fSevenModTwo ∧ hEval c r fSevenModTwo Env.zero = some true ∧
      LeanValid fNatDivModId ∧ guarded fNatDivModId = false ∧
      ¬ JunkIndependent fNatDivModId ∧ ¬ DefinedEverywhere c r fNatDivModId := by
  refine ⟨by decide, ?_, by cases c <;> cases r <;> decide, ?_, by cases c <;> cases r <;> decide,
    ?_, by decide, ?_, ?_⟩
  · intro h
    have := h leanJ oneJ Env.zero
    revert this
    decide
  · intro J J' ρ
    simp [evalJ, fSevenModTwo, evalT, jMod, ModDom]
  · intro ρ
    rw [evalJ_leanJ_iff]
    simp only [leanEvalF, fNatDivModId, leanEvalT]
    intro _
    rw [Nat.mul_comm, Nat.div_add_mod]
  · intro h
    have := h leanJ oneJ (envAB 7 2)
    revert this
    decide
  · intro h
    apply h (envAB 7 2)
    cases c <;> cases r <;> decide

/-! ## Result 4: guard placement -/

/-- `b ≤ a ∧ a - b + b = a` (guard first). -/
def fGuardFirst : Formula := .and (.le vB vA) fSubAddCancel

/-- `a - b + b = a ∧ b ≤ a` (guard second). -/
def fGuardSecond : Formula := .and fSubAddCancel (.le vB vA)

/-- `¬ (a - b + b = a) → ¬ (b ≤ a)`, the contrapositive of `b ≤ a → a - b + b = a`. -/
def fContrapositive : Formula := .imp (.not fSubAddCancel) (.not (.le vB vA))

/-- **The guarded fragment is not closed under commutation of `∧`.** The guard-first
conjunction is accepted, the guard-second conjunction is rejected, and the two have the
same total value under every junk record at every environment. -/
theorem ce_guarded_not_closed_under_and_comm :
    guarded fGuardFirst = true ∧ guarded fGuardSecond = false ∧
      ∀ (J : Junk) (ρ : Env), evalJ J fGuardFirst ρ = evalJ J fGuardSecond ρ := by
  refine ⟨by decide, by decide, ?_⟩
  intro J ρ
  simp only [fGuardFirst, fGuardSecond, evalJ, Bool.and_comm]

/-- **The guarded fragment is not closed under contraposition.** `b ≤ a → a - b + b = a`
is accepted, its contrapositive is rejected, and the two have the same total value under
every junk record at every environment. -/
theorem ce_guarded_not_closed_under_contrapose :
    guarded fSubAddCancelGuarded = true ∧ guarded fContrapositive = false ∧
      ∀ (J : Junk) (ρ : Env), evalJ J fSubAddCancelGuarded ρ = evalJ J fContrapositive ρ := by
  refine ⟨by decide, by decide, ?_⟩
  intro J ρ
  show (!evalJ J (.le vB vA) ρ || evalJ J fSubAddCancel ρ) =
    (!(!evalJ J fSubAddCancel ρ) || !evalJ J (.le vB vA) ρ)
  cases evalJ J (.le vB vA) ρ <;> cases evalJ J fSubAddCancel ρ <;> rfl

theorem tvAnd_kleene_comm (x y : Option Bool) : tvAnd .kleene x y = tvAnd .kleene y x := by
  rcases x with _ | _ | _ <;> rcases y with _ | _ | _ <;> rfl

theorem tvImp_kleene_contrapose (x y : Option Bool) :
    tvImp .kleene (tvNot y) (tvNot x) = tvImp .kleene x y := by
  rcases x with _ | _ | _ <;> rcases y with _ | _ | _ <;> rfl

/-- Under strong Kleene connectives, commuting a conjunction does not change the human
value. -/
theorem hEval_kleene_and_comm (r : SubReading) (φ ψ : Formula) (ρ : Env) :
    hEval .kleene r (.and φ ψ) ρ = hEval .kleene r (.and ψ φ) ρ := by
  simp only [hEval, tvAnd_kleene_comm]

/-- Under strong Kleene connectives, contraposition does not change the human value. -/
theorem hEval_kleene_contrapose (r : SubReading) (φ ψ : Formula) (ρ : Env) :
    hEval .kleene r (.imp (.not ψ) (.not φ)) ρ = hEval .kleene r (.imp φ ψ) ρ := by
  simp only [hEval, tvImp_kleene_contrapose]

/-- **Semantic closure under strong Kleene.** The class of everywhere-defined formulas is
closed under commutation of `∧` and under contraposition. -/
theorem definedEverywhere_kleene_closed (r : SubReading) (φ ψ : Formula) :
    (DefinedEverywhere .kleene r (.and φ ψ) ↔ DefinedEverywhere .kleene r (.and ψ φ)) ∧
      (DefinedEverywhere .kleene r (.imp φ ψ) ↔
        DefinedEverywhere .kleene r (.imp (.not ψ) (.not φ))) := by
  constructor
  · constructor <;> intro h ρ
    · rw [hEval_kleene_and_comm]; exact h ρ
    · rw [hEval_kleene_and_comm]; exact h ρ
  · constructor <;> intro h ρ
    · rw [hEval_kleene_contrapose]; exact h ρ
    · rw [← hEval_kleene_contrapose]; exact h ρ

/-- Under strong Kleene connectives and either reading, the guard-second conjunction
`a - b + b = a ∧ b ≤ a` is rejected by the checker and defined at every environment. -/
theorem definedEverywhere_kleene_guardSecond (r : SubReading) :
    guarded fGuardSecond = false ∧ DefinedEverywhere .kleene r fGuardSecond := by
  refine ⟨by decide, ?_⟩
  intro ρ
  have := definedEverywhere_of_guarded .kleene r fGuardFirst (by decide) ρ
  simpa only [fGuardSecond, fGuardFirst, hEval_kleene_and_comm] using this

/-- **Sequential connectives: commutation of `∧` changes definedness.** At `a = 0, b = 1`,
the guard-first conjunction is defined (false) and the guard-second conjunction is
undefined. -/
theorem ce_seq_and_comm_changes_definedness :
    hEval .seq .partialNat fGuardFirst (envAB 0 1) = some false ∧
      hEval .seq .partialNat fGuardSecond (envAB 0 1) = none := by
  decide

/-- **Sequential connectives: contraposition changes definedness.** At `a = 0, b = 1`,
`b ≤ a → a - b + b = a` is defined (true) and its contrapositive is undefined. -/
theorem ce_seq_contrapose_changes_definedness :
    hEval .seq .partialNat fSubAddCancelGuarded (envAB 0 1) = some true ∧
      hEval .seq .partialNat fContrapositive (envAB 0 1) = none := by
  decide

/-- **Sequential connectives: the everywhere-defined class is not closed.** With sequential
connectives (and `partialNat`), the guard-first conjunction and `b ≤ a → a - b + b = a` are
defined everywhere, while the guard-second conjunction and the contrapositive are not. -/
theorem ce_seq_not_closed :
    DefinedEverywhere .seq .partialNat fGuardFirst ∧ ¬ DefinedEverywhere .seq .partialNat fGuardSecond ∧
      DefinedEverywhere .seq .partialNat fSubAddCancelGuarded ∧
      ¬ DefinedEverywhere .seq .partialNat fContrapositive := by
  refine ⟨definedEverywhere_of_guarded _ _ _ (by decide), ?_,
    definedEverywhere_of_guarded _ _ _ (by decide), ?_⟩
  · intro h
    exact h (envAB 0 1) ce_seq_and_comm_changes_definedness.2
  · intro h
    exact h (envAB 0 1) ce_seq_contrapose_changes_definedness.2

/-- Under the `intValued` reading, the guard-second conjunction and the contrapositive are
defined everywhere even with sequential connectives (natural subtraction is always defined
there), so `ce_seq_not_closed` depends on the `partialNat` reading for these formulas. -/
theorem seq_defined_intValued :
    DefinedEverywhere .seq .intValued fGuardSecond ∧
      DefinedEverywhere .seq .intValued fContrapositive := by
  have hs := (ce_intValued_humanValid_not_leanValid .seq).1
  have hl : ∀ ρ, hEval .seq .intValued (.le vB vA) ρ =
      some (decide (((ρ.nat 1 : Nat) : Int) ≤ ((ρ.nat 0 : Nat) : Int))) := fun ρ => rfl
  constructor
  · intro ρ
    show tvAnd .seq (hEval .seq .intValued fSubAddCancel ρ) (hEval .seq .intValued (.le vB vA) ρ) ≠ none
    rw [hs ρ, hl ρ, tvAnd_some_true_some]
    simp
  · intro ρ
    show tvImp .seq (tvNot (hEval .seq .intValued fSubAddCancel ρ))
      (tvNot (hEval .seq .intValued (.le vB vA) ρ)) ≠ none
    rw [hs ρ, hl ρ]
    simp [tvNot, tvImp_some_false]

/-- The environment with integer variable `x` (index 0) equal to `z` and every other
variable `0`. -/
def envX (z : Int) : Env := ⟨fun _ => 0, fun i => if i = 0 then z else 0⟩

/-- `0 ≤ x ∧ toNat x = toNat x` at `Int`/`Nat` (guard first). -/
def fToNatGuardFirst : Formula := .and (.le (.intLit 0) vX) (.eq (.toNat vX) (.toNat vX))
/-- `toNat x = toNat x ∧ 0 ≤ x` (guard second). -/
def fToNatGuardSecond : Formula := .and (.eq (.toNat vX) (.toNat vX)) (.le (.intLit 0) vX)
/-- `0 ≤ x → toNat x = toNat x`. -/
def fToNatImp : Formula := .imp (.le (.intLit 0) vX) (.eq (.toNat vX) (.toNat vX))
/-- `¬ (toNat x = toNat x) → ¬ (0 ≤ x)`, the contrapositive of `fToNatImp`. -/
def fToNatContrapose : Formula :=
  .imp (.not (.eq (.toNat vX) (.toNat vX))) (.not (.le (.intLit 0) vX))

/-- **Sequential connectives break closure under either reading.** With sequential
connectives and either reading of natural subtraction, the guard-first conjunction
`0 ≤ x ∧ toNat x = toNat x` and the implication `0 ≤ x → toNat x = toNat x` are defined
everywhere, while their commuted and contraposed forms are undefined at `x = -1`. -/
theorem ce_seq_not_closed_toNat (r : SubReading) :
    DefinedEverywhere .seq r fToNatGuardFirst ∧ ¬ DefinedEverywhere .seq r fToNatGuardSecond ∧
      DefinedEverywhere .seq r fToNatImp ∧ ¬ DefinedEverywhere .seq r fToNatContrapose := by
  refine ⟨definedEverywhere_of_guarded _ _ _ (by decide), ?_,
    definedEverywhere_of_guarded _ _ _ (by decide), ?_⟩
  · intro h
    have hnone : hEval .seq r fToNatGuardSecond (envX (-1)) = none := by cases r <;> decide
    exact h (envX (-1)) hnone
  · intro h
    have hnone : hEval .seq r fToNatContrapose (envX (-1)) = none := by cases r <;> decide
    exact h (envX (-1)) hnone

/-- Under strong Kleene connectives the contrapositive is defined (true) at the same
point. -/
theorem kleene_contrapositive_defined :
    hEval .kleene .partialNat fContrapositive (envAB 0 1) = some true := by
  decide

end Toy.Junk
