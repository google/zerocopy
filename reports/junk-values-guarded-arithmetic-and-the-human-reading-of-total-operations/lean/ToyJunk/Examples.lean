import ToyJunk.Quantifiers

/-!
# Positive and negative examples for the core definitions

Each definition is tested on an intended instance it must accept and an instance it must
reject.
-/

namespace Toy.Junk

/-! ## Domains -/

/-- `DivDom` accepts exact division by a nonzero divisor, including negative dividends. -/
theorem DivDom_pos : DivDom 6 3 ∧ DivDom (-4) 2 ∧ DivDom 0 5 := by decide

/-- `DivDom` rejects division by zero (even `0 / 0`, although `0 ∣ 0`) and inexact
division. -/
theorem DivDom_neg : ¬ DivDom 5 0 ∧ ¬ DivDom 0 0 ∧ ¬ DivDom 7 2 := by decide

/-- `ModDom` accepts a nonnegative dividend with a positive divisor. -/
theorem ModDom_pos : ModDom 7 2 ∧ ModDom 0 3 := by decide

/-- `ModDom` rejects a zero divisor and negative operands. It is conservative: it also
rejects `(-4) % 2`, where the truncating, flooring and Euclidean remainders all equal `0`. -/
theorem ModDom_neg :
    ¬ ModDom 5 0 ∧ ¬ ModDom (-7) 2 ∧ ¬ ModDom 7 (-2) ∧ ¬ ModDom (-4) 2 ∧
      (Int.tmod (-4) 2 = (-4) % 2 ∧ Int.fmod (-4) 2 = (-4) % 2) := by decide

/-! ## Total semantics -/

/-- Inside the domains the total value does not depend on the junk record. -/
theorem evalT_pos (J : Junk) :
    evalT J Env.zero (.sub (.natLit 5) (.natLit 3)) = (2 : Nat) ∧
      evalT J Env.zero (.div (.natLit 6) (.natLit 3)) = (2 : Nat) ∧
      evalT J Env.zero (.div (.intLit (-6)) (.intLit 3)) = (-2 : Int) ∧
      evalT J Env.zero (.mod (.natLit 7) (.natLit 2)) = (1 : Nat) := by
  simp [evalT, jSub, jDiv, jMod, DivDom, ModDom]

/-- Outside the domains the total value is the junk value, and differs between records. -/
theorem evalT_neg :
    evalT leanJ Env.zero (.sub (.natLit 0) (.natLit 1)) = (0 : Nat) ∧
      evalT oneJ Env.zero (.sub (.natLit 0) (.natLit 1)) = (1 : Nat) ∧
      evalT leanJ Env.zero (.div (.intLit 5) (.intLit 0)) = (0 : Int) ∧
      evalT oneJ Env.zero (.div (.intLit 5) (.intLit 0)) = (1 : Int) := by
  decide

/-- `leanJ` reproduces Lean's operators, including Euclidean `Int` division. -/
theorem leanJ_pos :
    evalT leanJ Env.zero (.div (.intLit (-7)) (.intLit 2)) = Int.ediv (-7) 2 ∧
      evalT leanJ Env.zero (.div (.intLit (-7)) (.intLit 2)) =
        leanEvalT Env.zero (.div (.intLit (-7)) (.intLit 2)) := by
  decide

/-- The truncating record is not Lean's reading. -/
theorem leanJ_neg :
    evalT truncJ Env.zero (.div (.intLit (-7)) (.intLit 2)) ≠
      leanEvalT Env.zero (.div (.intLit (-7)) (.intLit 2)) := by
  decide

/-! ## Human semantics -/

/-- Defined human values, including exact division with a negative dividend. -/
theorem hEvalT_pos (r : SubReading) :
    hEvalT .partialNat Env.zero (.sub (.natLit 5) (.natLit 3)) = some 2 ∧
      hEvalT r Env.zero (.div (.natLit 6) (.natLit 3)) = some 2 ∧
      hEvalT r Env.zero (.div (.intLit (-6)) (.intLit 3)) = some (-2) ∧
      hEvalT .intValued Env.zero (.sub (.natLit 3) (.natLit 5)) = some (-2) := by
  cases r <;> decide

/-- Undefined human values: natural subtraction below zero (under `partialNat`), division
by zero, inexact division, remainder with a negative operand, `toNat` of a negative, and
strict propagation through `* 0`. -/
theorem hEvalT_neg (r : SubReading) :
    hEvalT .partialNat Env.zero (.sub (.natLit 3) (.natLit 5)) = none ∧
      hEvalT r Env.zero (.div (.natLit 5) (.natLit 0)) = none ∧
      hEvalT r Env.zero (.div (.natLit 7) (.natLit 2)) = none ∧
      hEvalT r Env.zero (.mod (.intLit (-7)) (.intLit 2)) = none ∧
      hEvalT r Env.zero (.toNat (.intLit (-3))) = none ∧
      hEvalT .partialNat Env.zero (.mul (.sub (.natLit 0) (.natLit 1)) (.natLit 0)) = none := by
  cases r <;> decide

/-- Strong Kleene connectives are decided by a defined dominant side; sequential
connectives are not when the left side is undefined. -/
theorem tv_pos :
    tvAnd .kleene none (some false) = some false ∧ tvOr .kleene none (some true) = some true ∧
      tvAnd .seq (some false) none = some false ∧ tvOr .seq (some true) none = some true := by
  decide

theorem tv_neg :
    tvAnd .seq none (some false) = none ∧ tvOr .seq none (some true) = none ∧
      tvAnd .kleene none (some true) = none := by
  decide

/-- Implication is true when its premise is false, under both connective semantics, and
under strong Kleene also when its conclusion is true. -/
theorem tvImp_pos :
    tvImp .kleene (some false) none = some true ∧ tvImp .seq (some false) none = some true ∧
      tvImp .kleene none (some true) = some true := by
  decide

/-- Sequential implication is undefined when its premise is undefined; Kleene implication
is undefined when neither side settles it. -/
theorem tvImp_neg :
    tvImp .seq none (some true) = none ∧ tvImp .kleene none (some false) = none ∧
      tvImp .kleene (some true) (some false) = some false := by
  decide

/-- The Kleene quantifier is false as soon as one instance is false, even if others are
undefined. -/
theorem tvAll_pos : tvAll (fun n : Nat => if n = 0 then some false else none) = some false := by
  apply tvAll_eq_some_false_of
  exact ⟨0, rfl⟩

/-- The Kleene quantifier is undefined if no instance is false and some instance is
undefined. -/
theorem tvAll_neg : tvAll (fun n : Nat => if n = 0 then some true else none) = none := by
  apply tvAll_eq_none_of_not
  · intro h
    have := h 1
    simp at this
  · rintro ⟨v, hv⟩
    by_cases h : v = 0 <;> simp [h] at hv

/-- The Kleene existential quantifier is true as soon as one instance is true, even if
others are undefined. -/
theorem tvEx_pos : tvEx (fun n : Nat => if n = 0 then some true else none) = some true :=
  tvEx_eq_some_true.mpr ⟨0, rfl⟩

/-- The Kleene existential quantifier is undefined if no instance is true and some instance
is undefined. -/
theorem tvEx_neg : tvEx (fun n : Nat => if n = 0 then some false else none) = none := by
  unfold tvEx
  have h1 : ¬ ∃ v : Nat, (if v = 0 then some false else none) = some true := by
    rintro ⟨v, hv⟩
    by_cases h : v = 0 <;> simp [h] at hv
  have h2 : ¬ ∀ v : Nat, (if v = 0 then some false else none) = some false := by
    intro h
    have := h 1
    simp at this
  simp only [h1, h2, ↓reduceIte]

/-- Lean's direct reading of formulas: truncated subtraction makes `0 - 1 = 0` true, and the
toy relation symbols are Lean's relations. -/
theorem leanEvalF_pos : leanEvalF fZeroSubOne Env.zero ∧ leanEvalF fDivZero Env.zero :=
  ⟨(evalJ_leanJ_iff _ _).mp (by decide), (evalJ_leanJ_iff _ _).mp (by decide)⟩

/-- Lean's direct reading rejects `2 - 3 < 0` at `Nat` and `a - b + b = a` at `a = 0, b = 1`. -/
theorem leanEvalF_neg : ¬ leanEvalF fNumeralNat Env.zero ∧ ¬ leanEvalF fSubAddCancel (envAB 0 1) :=
  ⟨fun h => absurd ((evalJ_leanJ_iff _ _).mpr h) (by decide),
    fun h => absurd ((evalJ_leanJ_iff _ _).mpr h) (by decide)⟩

/-! ## Properties of formulas -/

theorem JunkIndependent_pos : JunkIndependent fMulZero ∧ JunkIndependent fSubAddCancelGuarded :=
  ⟨(ce_junkIndependent_not_definedEverywhere .kleene).1, junkIndependent_of_guarded _ (by decide)⟩

theorem JunkIndependent_neg : ¬ JunkIndependent fZeroSubOne ∧ ¬ JunkIndependent fSubLeSelf :=
  ⟨(ce_zeroSubOne_junkDependent .kleene).1, (ce_agrees_not_junkIndependent .kleene).2.2.2.1⟩

theorem DefinedEverywhere_pos (c : Conn) (r : SubReading) :
    DefinedEverywhere c r fSubAddCancelGuarded :=
  definedEverywhere_of_guarded c r _ (by decide)

theorem DefinedEverywhere_neg (c : Conn) : ¬ DefinedEverywhere c .partialNat fSubAddCancel := by
  intro h
  apply h (envAB 0 1)
  rw [hEval_subAddCancel_partialNat]
  decide

/-- Under `intValued`, `a - b ≤ a` (at `Nat`) agrees with Lean's reading wherever it is
defined (it is defined and true everywhere there). Under `partialNat` the predicate holds for
every formula (`agreesWhereDefined_partialNat`), so it separates formulas only under
`intValued`. -/
theorem AgreesWhereDefined_pos (c : Conn) : AgreesWhereDefined c .intValued leanJ fSubLeSelf := by
  have hhum : ∀ ρ, hEval c .intValued fSubLeSelf ρ = some true := by
    intro ρ
    have hle : ((ρ.nat 0 : Int) - (ρ.nat 1 : Int)) ≤ (ρ.nat 0 : Int) := by omega
    cases c <;> simp [hEval, fSubLeSelf, hEvalT, obind2, hSub, hAtom, hle]
  intro ρ b hb
  rw [hhum ρ] at hb
  injection hb with hb'
  subst hb'
  exact (ce_agrees_not_junkIndependent c).2.1 ρ

/-- Under `partialNat`, agreement-where-defined holds even for `x / 0 = 0`, which is never
human-defined: the predicate is trivial under that reading. -/
theorem AgreesWhereDefined_partialNat_trivial (c : Conn) (J : Junk) :
    AgreesWhereDefined c .partialNat J fDivZero :=
  agreesWhereDefined_partialNat c J fDivZero

theorem AgreesWhereDefined_neg (c : Conn) : ¬ AgreesWhereDefined c .intValued leanJ fNumeralNat := by
  intro h
  have := h Env.zero true (ce_agreement_intValued c).1
  rw [(ce_agreement_intValued c).2] at this
  cases this

theorem LeanValid_pos : LeanValid fDivZero := (ce_leanValid_not_humanValid .kleene .partialNat).1

theorem LeanValid_neg : ¬ LeanValid fSubAddCancel := (ce_intValued_humanValid_not_leanValid .kleene).2

theorem HumanValid_pos (c : Conn) (r : SubReading) : HumanValid c r fSubAddCancelGuarded :=
  (restate_subAddCancel_guarded c r).2.2

theorem HumanValid_neg (c : Conn) (r : SubReading) : ¬ HumanValid c r fDivZero :=
  (ce_leanValid_not_humanValid c r).2.2

/-! ## Guard discipline -/

/-- Integer variable `y` (index 1). -/
abbrev vY : Term .int := .intVar 1

/-- `¬ (b = 0) → a % b < b` at `Nat`. -/
def fGuardedNatMod : Formula := .imp (.not (.eq vB (.natLit 0))) (.lt (.mod vA vB) vB)

/-- `0 < y ∧ 0 ≤ x → x % y < y` at `Int`. -/
def fGuardedIntMod : Formula :=
  .imp (.and (.lt (.intLit 0) vY) (.le (.intLit 0) vX)) (.lt (.mod vX vY) vY)

/-- `¬ (y = 0) ∧ y ∣ x → x / y * y = x` at `Int`. -/
def fGuardedIntDiv : Formula :=
  .imp (.and (.not (.eq vY (.intLit 0))) (.dvd vY vX)) (.eq (.mul (.div vX vY) vY) vX)

/-- `0 ≤ x → ↑(toNat x) = x` at `Int`. -/
def fGuardedToNat : Formula := .imp (.le (.intLit 0) vX) (.eq (.cast (.toNat vX)) vX)

/-- The checker accepts a guarded instance of each partial-operation rule: `Nat`
subtraction, `Nat` division, a bounded quantifier, `Nat` remainder, `Int` remainder,
`Int` division and `Int.toNat`. -/
theorem guarded_pos :
    guarded fSubAddCancelGuarded = true ∧ guarded fDvdDivGuarded = true ∧
      guarded fBoundedCancel = true ∧ guarded fGuardedNatMod = true ∧
      guarded fGuardedIntMod = true ∧ guarded fGuardedIntDiv = true ∧
      guarded fGuardedToNat = true := by
  decide

/-- The four guarded instances of the `Nat` remainder, `Int` remainder, `Int` division and
`Int.toNat` rules are Lean-valid and human-valid under every connective semantics and
reading. -/
theorem guarded_branches_pos (c : Conn) (r : SubReading) :
    (LeanValid fGuardedNatMod ∧ HumanValid c r fGuardedNatMod) ∧
      (LeanValid fGuardedIntMod ∧ HumanValid c r fGuardedIntMod) ∧
      (LeanValid fGuardedIntDiv ∧ HumanValid c r fGuardedIntDiv) ∧
      (LeanValid fGuardedToNat ∧ HumanValid c r fGuardedToNat) := by
  have hg1 : guarded fGuardedNatMod = true := by decide
  have hg2 : guarded fGuardedIntMod = true := by decide
  have hg3 : guarded fGuardedIntDiv = true := by decide
  have hg4 : guarded fGuardedToNat = true := by decide
  have hv1 : LeanValid fGuardedNatMod := by
    intro ρ; rw [evalJ_leanJ_iff]
    simp only [leanEvalF, fGuardedNatMod, leanEvalT, Srt.ltP]
    intro h; exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)
  have hv2 : LeanValid fGuardedIntMod := by
    intro ρ; rw [evalJ_leanJ_iff]
    simp only [leanEvalF, fGuardedIntMod, leanEvalT, Srt.ltP, Srt.leP]
    rintro ⟨hy, _⟩; exact Int.emod_lt_of_pos _ hy
  have hv3 : LeanValid fGuardedIntDiv := by
    intro ρ; rw [evalJ_leanJ_iff]
    simp only [leanEvalF, fGuardedIntDiv, leanEvalT, Srt.dvdP]
    rintro ⟨_, hd⟩; exact Int.ediv_mul_cancel hd
  have hv4 : LeanValid fGuardedToNat := by
    intro ρ; rw [evalJ_leanJ_iff]
    simp only [leanEvalF, fGuardedToNat, leanEvalT, Srt.leP]
    intro hx; exact Int.toNat_of_nonneg hx
  exact ⟨⟨hv1, (leanValid_iff_humanValid_of_guarded c r _ hg1).mp hv1⟩,
    ⟨hv2, (leanValid_iff_humanValid_of_guarded c r _ hg2).mp hv2⟩,
    ⟨hv3, (leanValid_iff_humanValid_of_guarded c r _ hg3).mp hv3⟩,
    ⟨hv4, (leanValid_iff_humanValid_of_guarded c r _ hg4).mp hv4⟩⟩

/-- `b ≤ a ∧ ∀ b, a - b + b = a`: the outer fact mentions the rebound variable `b`, so it is
discarded under the quantifier. -/
def fStaleGuard : Formula := .and (.le vB vA) (.allNat 1 fSubAddCancel)

/-- The checker rejects unguarded subtraction and division by a literal zero, and does not
let a fact about `b` guard an occurrence under a quantifier that rebinds `b`. -/
theorem guarded_neg :
    guarded fSubAddCancel = false ∧ guarded fDivZero = false ∧ guarded fStaleGuard = false := by
  decide

/-- Facts are the atomic top-level conjuncts (and negated equalities). -/
theorem facts_pos :
    (Formula.and (.le vB vA) (.not (.eq vB (.natLit 0)))).facts =
      [.le vB vA, .not (.eq vB (.natLit 0))] := by
  decide

/-- Disjunctions, implications and negated inequalities contribute no facts. -/
theorem facts_neg :
    (Formula.or (.le vB vA) (.le vA vB)).facts = [] ∧
      (Formula.imp (.le vB vA) (.le vA vB)).facts = [] ∧
      (Formula.not (.le vB vA)).facts = [] := by
  decide

/-- `ballNat x t φ` is `∀ x, x ≤ t → φ`. -/
theorem ballNat_unfold (x : Nat) (t : Term .nat) (φ : Formula) :
    ballNat x t φ = .allNat x (.imp (.le (.natVar x) t) φ) := rfl

end Toy.Junk
