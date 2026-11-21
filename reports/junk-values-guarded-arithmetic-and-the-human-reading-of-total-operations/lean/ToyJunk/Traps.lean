import ToyJunk.Guarded

/-!
# Result 3: one counterexample per unguarded construct

Each theorem is a closed instance whose truth differs between Lean's reading and a human
reading, with every value checked by evaluation.

# Result 5: safe restatements

Guarded or explicit-cast restatements of the trap statements, each with the same truth
value in Lean's reading and in the human reading.
-/

namespace Toy.Junk

/-! ## Result 3 -/

/-- `0 - 1 + 1 = 0` at `Nat` (the instance `a = 0, b = 1` of `a - b + b = a`). -/
def fTruncSubCancel01 : Formula :=
  .eq (.add (.sub (.natLit 0) (.natLit 1)) (.natLit 1)) (.natLit 0)

/-- **Truncated subtraction.** `0 - 1 + 1 = 0` is false in Lean (`0 - 1 = 0`), undefined
in the `partialNat` reading, and true in the `intValued` reading. -/
theorem trap_truncSub_addCancel (c : Conn) :
    evalJ leanJ fTruncSubCancel01 Env.zero = false ∧
      hEval c .partialNat fTruncSubCancel01 Env.zero = none ∧
      hEval c .intValued fTruncSubCancel01 Env.zero = some true ∧
      ((0 : Nat) - 1 + 1 ≠ 0) := by
  cases c <;> decide

/-- `0 - 1 ≤ 0` at `Nat` (the instance `a = 0, b = 1` of `a - b ≤ a`). -/
def fTruncSubLe01 : Formula := .le (.sub (.natLit 0) (.natLit 1)) (.natLit 0)

/-- **Truncated subtraction, junk-dependent truth.** `0 - 1 ≤ 0` is true in Lean, but
false when the junk value of `0 - 1` is `1`; it is undefined in the `partialNat` reading. -/
theorem trap_truncSub_le_self (c : Conn) :
    evalJ leanJ fTruncSubLe01 Env.zero = true ∧ evalJ oneJ fTruncSubLe01 Env.zero = false ∧
      hEval c .partialNat fTruncSubLe01 Env.zero = none := by
  cases c <;> decide

/-- `5 / 0 = 0` at `Int`. -/
def fFiveDivZero : Formula := .eq (.div (.intLit 5) (.intLit 0)) (.intLit 0)

/-- `5 % 0 = 5` at `Nat`. -/
def fFiveModZero : Formula := .eq (.mod (.natLit 5) (.natLit 0)) (.natLit 5)

/-- **Division and remainder by zero.** `5 / 0 = 0` (at `Int`) and `5 % 0 = 5` (at `Nat`)
are true in Lean, false for the junk record `oneJ`, and undefined in both human readings. -/
theorem trap_div_mod_zero (c : Conn) (r : SubReading) :
    evalJ leanJ fFiveDivZero Env.zero = true ∧ evalJ oneJ fFiveDivZero Env.zero = false ∧
      hEval c r fFiveDivZero Env.zero = none ∧
      evalJ leanJ fFiveModZero Env.zero = true ∧ evalJ oneJ fFiveModZero Env.zero = false ∧
      hEval c r fFiveModZero Env.zero = none ∧
      ((5 : Int) / 0 = 0 ∧ (5 : Nat) / 0 = 0 ∧ (5 : Nat) % 0 = 5 ∧ (5 : Int) % 0 = 5) := by
  cases c <;> cases r <;> decide

/-- `7 / 2 * 2 = 7` at `Nat`. -/
def fFloorDiv : Formula := .eq (.mul (.div (.natLit 7) (.natLit 2)) (.natLit 2)) (.natLit 7)

/-- **Floor division read as exact division.** `7 / 2 * 2 = 7` is false in Lean
(`7 / 2 = 3`), and undefined in the human reading, which flags inexact division. -/
theorem trap_floorDiv_exact (c : Conn) (r : SubReading) :
    evalJ leanJ fFloorDiv Env.zero = false ∧ hEval c r fFloorDiv Env.zero = none ∧
      ((7 : Nat) / 2 * 2 = 6) := by
  cases c <;> cases r <;> decide

/-- `(-7) / 2 = -4` at `Int`. -/
def fNegSevenDivTwo : Formula := .eq (.div (.intLit (-7)) (.intLit 2)) (.intLit (-4))
/-- `7 / (-2) = -3` at `Int`. -/
def fSevenDivNegTwo : Formula := .eq (.div (.intLit 7) (.intLit (-2))) (.intLit (-3))
/-- `(-7) % 2 = 1` at `Int`. -/
def fNegSevenModTwo : Formula := .eq (.mod (.intLit (-7)) (.intLit 2)) (.intLit 1)
/-- `7 % (-2) = 1` at `Int`. -/
def fSevenModNegTwo : Formula := .eq (.mod (.intLit 7) (.intLit (-2))) (.intLit 1)

/-- **Integer rounding conventions, values.** The default `Int` operators `/` and `%` are
`Int.ediv` and `Int.emod` (Euclidean: the remainder is nonnegative). Truncating
(`Int.tdiv`/`Int.tmod`) and flooring (`Int.fdiv`/`Int.fmod`) conventions give different
values on negative operands. -/
theorem trap_int_rounding_values :
    ((-7 : Int) / 2 = -4 ∧ Int.tdiv (-7) 2 = -3 ∧ Int.fdiv (-7) 2 = -4) ∧
      ((7 : Int) / (-2) = -3 ∧ Int.tdiv 7 (-2) = -3 ∧ Int.fdiv 7 (-2) = -4) ∧
      ((-7 : Int) % 2 = 1 ∧ Int.tmod (-7) 2 = -1 ∧ Int.fmod (-7) 2 = 1) ∧
      ((7 : Int) % (-2) = 1 ∧ Int.tmod 7 (-2) = 1 ∧ Int.fmod 7 (-2) = -1) ∧
      (∀ a b : Int, a / b = Int.ediv a b ∧ a % b = Int.emod a b) := by
  refine ⟨by decide, by decide, by decide, by decide, fun _ _ => ⟨rfl, rfl⟩⟩

/-- **Integer rounding conventions in the toy.** Each of the four statements is true for
Lean's junk record, at least one is false for the truncating record and one for the
flooring record, and all four are undefined in the human reading. -/
theorem trap_int_rounding (c : Conn) (r : SubReading) :
    (evalJ leanJ fNegSevenDivTwo Env.zero = true ∧ evalJ truncJ fNegSevenDivTwo Env.zero = false ∧
      evalJ floorJ fNegSevenDivTwo Env.zero = true ∧ hEval c r fNegSevenDivTwo Env.zero = none) ∧
    (evalJ leanJ fSevenDivNegTwo Env.zero = true ∧ evalJ truncJ fSevenDivNegTwo Env.zero = true ∧
      evalJ floorJ fSevenDivNegTwo Env.zero = false ∧ hEval c r fSevenDivNegTwo Env.zero = none) ∧
    (evalJ leanJ fNegSevenModTwo Env.zero = true ∧ evalJ truncJ fNegSevenModTwo Env.zero = false ∧
      evalJ floorJ fNegSevenModTwo Env.zero = true ∧ hEval c r fNegSevenModTwo Env.zero = none) ∧
    (evalJ leanJ fSevenModNegTwo Env.zero = true ∧ evalJ truncJ fSevenModNegTwo Env.zero = true ∧
      evalJ floorJ fSevenModNegTwo Env.zero = false ∧ hEval c r fSevenModNegTwo Env.zero = none) := by
  cases c <;> cases r <;> decide

/-- **Quotient conventions agree on exact division.** For all integers `n` and `d`, if
`d ∣ n` then the truncating and flooring quotients equal the default (Euclidean) quotient
`n / d`. (No `d ≠ 0` hypothesis is needed: at `d = 0` all three quotients are `0`.) -/
theorem quotient_conventions_agree_of_dvd (n d : Int) (h : d ∣ n) :
    Int.tdiv n d = n / d ∧ Int.fdiv n d = n / d :=
  ⟨Int.tdiv_eq_ediv_of_dvd h, Int.fdiv_eq_ediv_of_dvd h⟩

/-- **Remainder conventions agree on nonnegative operands.** For all integers `n` and `d`,
if `0 ≤ n` and `0 ≤ d` then the truncating and flooring remainders equal the default
(Euclidean) remainder `n % d`. -/
theorem remainder_conventions_agree_of_nonneg (n d : Int) (hn : 0 ≤ n) (hd : 0 ≤ d) :
    Int.tmod n d = n % d ∧ Int.fmod n d = n % d :=
  ⟨Int.tmod_eq_emod_of_nonneg hn, Int.fmod_eq_emod_of_nonneg n hd⟩

/-- **Rounding conventions agree on the domains** (corollary). On `DivDom` the truncating and
flooring quotients equal the default quotient; on `ModDom` the truncating and flooring
remainders equal the default remainder. So the domains used by the junk-parameterized
semantics do not hide a choice of rounding convention. -/
theorem rounding_conventions_agree_on_domains (n d : Int) :
    (DivDom n d → Int.tdiv n d = n / d ∧ Int.fdiv n d = n / d) ∧
      (ModDom n d → Int.tmod n d = n % d ∧ Int.fmod n d = n % d) :=
  ⟨fun h => quotient_conventions_agree_of_dvd n d h.2,
    fun h => remainder_conventions_agree_of_nonneg n d h.1 (Int.le_of_lt h.2)⟩

/-- Non-vacuity of `quotient_conventions_agree_of_dvd`: `3 ∣ 6` and `2 ∣ -4`. -/
theorem nv_quotient_conventions_agree_of_dvd : (3 : Int) ∣ 6 ∧ (2 : Int) ∣ -4 := by decide

/-- Non-vacuity of `remainder_conventions_agree_of_nonneg`: `0 ≤ 7` and `0 ≤ 2`. -/
theorem nv_remainder_conventions_agree_of_nonneg : (0 : Int) ≤ 7 ∧ (0 : Int) ≤ 2 := by decide

/-- Tightness of `d ∣ n` in `quotient_conventions_agree_of_dvd` (canonical form): at
`n = -7, d = 2`, `d ∣ n` fails and the truncating quotient differs from the default one. -/
theorem ce_quotient_conventions_not_dvd :
    ¬ (2 : Int) ∣ -7 ∧ ¬ (Int.tdiv (-7) 2 = (-7) / 2 ∧ Int.fdiv (-7) 2 = (-7) / 2) := by
  decide

/-- Tightness of `0 ≤ n` in `remainder_conventions_agree_of_nonneg` (canonical form): at
`n = -7, d = 2`, `0 ≤ d` holds, `0 ≤ n` fails, and the truncating remainder differs. -/
theorem ce_remainder_conventions_neg_dividend :
    (0 : Int) ≤ 2 ∧ ¬ (0 : Int) ≤ -7 ∧
      ¬ (Int.tmod (-7) 2 = (-7) % 2 ∧ Int.fmod (-7) 2 = (-7) % 2) := by
  decide

/-- Tightness of `0 ≤ d` in `remainder_conventions_agree_of_nonneg` (canonical form): at
`n = 7, d = -2`, `0 ≤ n` holds, `0 ≤ d` fails, and the flooring remainder differs. -/
theorem ce_remainder_conventions_neg_divisor :
    (0 : Int) ≤ 7 ∧ ¬ (0 : Int) ≤ -2 ∧
      ¬ (Int.tmod 7 (-2) = 7 % (-2) ∧ Int.fmod 7 (-2) = 7 % (-2)) := by
  decide

/-- **`Fin n` wrap-around** (Lean core, outside the toy language). In `Fin 5`, `3 + 4 = 2`;
the values do not add exactly; `2 - 3 = 4`; and the numeral `7` denotes `2`. -/
theorem trap_fin_wrap :
    ((3 : Fin 5) + 4 = 2) ∧ ((3 : Fin 5).val + (4 : Fin 5).val ≠ ((3 : Fin 5) + 4).val) ∧
      ((2 : Fin 5) - 3).val = 4 ∧ (7 : Fin 5).val = 2 := by
  decide

/-- **`Fin n` numerals wrap before a bound is checked** (Lean core). In `Fin 3` the numeral
`4` denotes the element with value `1`, so `(1 : Fin 3).val + (4 : Fin 3).val < 3` holds while
the value of `1 + 4 : Fin 3` is not `1 + 4`. -/
theorem trap_fin_numeral_wraps_before_bound :
    (4 : Fin 3).val = 1 ∧ (1 : Fin 3).val + (4 : Fin 3).val < 3 ∧ ((1 : Fin 3) + 4).val ≠ 1 + 4 := by
  decide

/-- `↑(0 - 1) = ↑0 - ↑1` at `Int`, with the subtraction inside the cast at `Nat`. -/
def fCastPlacement01 : Formula :=
  .eq (.cast (.sub (.natLit 0) (.natLit 1))) (.sub (.cast (.natLit 0)) (.cast (.natLit 1)))

/-- `↑(a - b) = ↑a - ↑b` at `Int`. -/
def fCastPlacement : Formula := .eq (.cast (.sub vA vB)) (.sub (.cast vA) (.cast vB))

/-- Lean-core form of the cast-placement criterion. -/
theorem natCast_sub_eq_iff_le (a b : Nat) : ((a - b : Nat) : Int) = (a : Int) - (b : Int) ↔ b ≤ a := by
  omega

/-- **Cast placement.** `↑(0 - 1) = ↑0 - ↑1` is false in Lean, undefined in the
`partialNat` reading and true in the `intValued` reading; the open statement
`↑(a - b) = ↑a - ↑b` holds in Lean exactly when `b ≤ a`. -/
theorem trap_cast_placement (c : Conn) :
    evalJ leanJ fCastPlacement01 Env.zero = false ∧
      hEval c .partialNat fCastPlacement01 Env.zero = none ∧
      hEval c .intValued fCastPlacement01 Env.zero = some true ∧
      ∀ ρ, evalJ leanJ fCastPlacement ρ = decide (ρ.nat 1 ≤ ρ.nat 0) := by
  refine ⟨by decide, by cases c <;> decide, by cases c <;> decide, ?_⟩
  intro ρ
  have h : evalJ leanJ fCastPlacement ρ = true ↔
      ((ρ.nat 0 - ρ.nat 1 : Nat) : Int) = (ρ.nat 0 : Int) - (ρ.nat 1 : Int) :=
    evalJ_leanJ_iff fCastPlacement ρ
  by_cases hle : ρ.nat 1 ≤ ρ.nat 0
  · simp only [hle, decide_true]
    exact h.mpr (Int.ofNat_sub hle)
  · simp only [hle, decide_false]
    cases hv : evalJ leanJ fCastPlacement ρ
    · rfl
    · exact absurd ((natCast_sub_eq_iff_le _ _).mp (h.mp hv)) hle

/-- `Int.toNat (-3) = 0` at `Nat`. -/
def fToNatNeg : Formula := .eq (.toNat (.intLit (-3))) (.natLit 0)

/-- **`Int.toNat` of a negative.** `Int.toNat (-3) = 0` is true in Lean, false for the
junk record `oneJ`, and undefined in the human reading. -/
theorem trap_toNat_neg (c : Conn) (r : SubReading) :
    evalJ leanJ fToNatNeg Env.zero = true ∧ evalJ oneJ fToNatNeg Env.zero = false ∧
      hEval c r fToNatNeg Env.zero = none ∧ Int.toNat (-3) = 0 := by
  cases c <;> cases r <;> decide

/-- **Numeral typing.** The same text `2 - 3 < 0` is false at `Nat` and true at `Int` in
Lean. In the human readings the `Int` version is true; the `Nat` version is undefined under
`partialNat` and true under `intValued`. Unannotated, Lean elaborates the numerals at
`Nat`: the unannotated `¬ (2 - 3 < 0)` and `2 - 3 = 0` are provable (both are false at
`Int`), and `HEq (2 - 3) ((2 : Nat) - 3)` holds, which forces the unannotated term to have
type `Nat` (`type_eq_of_heq`). -/
theorem trap_numeral_typing (c : Conn) (r : SubReading) :
    evalJ leanJ fNumeralNat Env.zero = false ∧ evalJ leanJ fNumeralInt Env.zero = true ∧
      hEval c .partialNat fNumeralNat Env.zero = none ∧
      hEval c .intValued fNumeralNat Env.zero = some true ∧
      hEval c r fNumeralInt Env.zero = some true ∧
      ¬ (2 - 3 < 0) ∧ ((2 : Int) - 3 < 0) ∧ HEq (2 - 3) ((2 : Nat) - 3) ∧ (2 - 3 = 0) := by
  cases c <;> cases r <;> exact ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, HEq.rfl, by decide⟩

/-! ## Result 5 -/

/-- **Guarded truncated subtraction.** `b ≤ a → a - b + b = a` is accepted by the checker,
is Lean-valid, and is human-valid under either connectives and either reading. -/
theorem restate_subAddCancel_guarded (c : Conn) (r : SubReading) :
    guarded fSubAddCancelGuarded = true ∧ LeanValid fSubAddCancelGuarded ∧
      HumanValid c r fSubAddCancelGuarded := by
  have hg : guarded fSubAddCancelGuarded = true := by decide
  have hv : LeanValid fSubAddCancelGuarded := by
    intro ρ
    rw [evalJ_leanJ_iff]
    show ρ.nat 1 ≤ ρ.nat 0 → ρ.nat 0 - ρ.nat 1 + ρ.nat 1 = ρ.nat 0
    omega
  exact ⟨hg, hv, (leanValid_iff_humanValid_of_guarded c r _ hg).mp hv⟩

/-- `↑a - ↑b + ↑b = ↑a` at `Int`. -/
def fSubAddCancelCast : Formula :=
  .eq (.add (.sub (.cast vA) (.cast vB)) (.cast vB)) (.cast vA)

/-- **Signed difference by explicit casts.** The `Int` term `↑a - ↑b` computes, under every
junk record, exactly the `intValued` human value of the `Nat` term `a - b`; and the trap
`a - b + b = a`, read with `intValued` subtraction, has at every environment the Lean value
of the guarded, Lean-valid restatement `↑a - ↑b + ↑b = ↑a`. -/
theorem restate_signedDiff_cast (c : Conn) :
    (∀ (J : Junk) (ρ : Env), hEvalT .intValued ρ (.sub vA vB) = some (evalT J ρ (.sub (.cast vA) (.cast vB)))) ∧
      guarded fSubAddCancelCast = true ∧ LeanValid fSubAddCancelCast ∧
      ∀ (J : Junk) (ρ : Env), hEval c .intValued fSubAddCancel ρ = some (evalJ J fSubAddCancelCast ρ) := by
  have hg : guarded fSubAddCancelCast = true := by decide
  have hJ : ∀ (J : Junk) (ρ : Env), evalJ J fSubAddCancelCast ρ = true := by
    intro J ρ
    simp [evalJ, fSubAddCancelCast, evalT, opAdd, jSub]
  refine ⟨?_, hg, fun ρ => hJ leanJ ρ, ?_⟩
  · intro J ρ
    simp [hEvalT, obind2, hSub, evalT, jSub]
  · intro J ρ
    rw [hJ J ρ]
    exact (ce_intValued_humanValid_not_leanValid c).1 ρ

/-- Tightness of the fixed `intValued` reading in `restate_signedDiff_cast` (canonical form):
under `partialNat` the first and last conjuncts fail, at `a = 0, b = 1`. -/
theorem ce_restate_signedDiff_partialNat (c : Conn) :
    ¬ (∀ (J : Junk) (ρ : Env),
        hEvalT .partialNat ρ (.sub vA vB) = some (evalT J ρ (.sub (.cast vA) (.cast vB)))) ∧
      ¬ (∀ (J : Junk) (ρ : Env),
        hEval c .partialNat fSubAddCancel ρ = some (evalJ J fSubAddCancelCast ρ)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h leanJ (envAB 0 1)
    revert this
    decide
  · have := h leanJ (envAB 0 1)
    revert this
    cases c <;> decide

/-- **Shallow casting does not commute with nested subtraction.** With `t = 0 - 1` and
`u = 0` at `Nat`, the `intValued` human value of `t - u` is `-1`, while Lean's value of
`↑t - ↑u` at `Int` is `0`. -/
theorem ce_shallow_cast_nested_sub :
    hEvalT .intValued Env.zero (.sub (.sub (.natLit 0) (.natLit 1)) (.natLit 0)) = some (-1) ∧
      evalT leanJ Env.zero (.sub (.cast (.sub (.natLit 0) (.natLit 1))) (.cast (.natLit 0))) =
        (0 : Int) := by
  decide

/-- `b ∣ a → a / b * b = a` at `Nat`. -/
def fDvdDiv : Formula := .imp (.dvd vB vA) (.eq (.mul (.div vA vB) vB) vA)

/-- `¬ (b = 0) → b ∣ a → a / b * b = a` at `Nat`. -/
def fDvdDivGuarded : Formula := .imp (.not (.eq vB (.natLit 0))) fDvdDiv

/-- Human value of `b ∣ a → a / b * b = a` (at `Nat`): undefined when `a = b = 0` and true
at every other environment, under every connective semantics and reading. -/
theorem hEval_dvdDiv (c : Conn) (r : SubReading) (ρ : Env) :
    hEval c r fDvdDiv ρ = if ρ.nat 0 = 0 ∧ ρ.nat 1 = 0 then none else some true := by
  by_cases hab : ρ.nat 0 = 0 ∧ ρ.nat 1 = 0
  · obtain ⟨ha, hb⟩ := hab
    simp only [ha, hb, and_self, ↓reduceIte]
    have hd : ((ρ.nat 1 : Nat) : Int) ∣ ((ρ.nat 0 : Nat) : Int) := by rw [ha, hb]; exact Int.dvd_refl 0
    have hnd : ¬ DivDom ((ρ.nat 0 : Nat) : Int) ((ρ.nat 1 : Nat) : Int) := by
      rintro ⟨h0, _⟩; rw [hb] at h0; exact h0 rfl
    simp [hEval, fDvdDiv, hEvalT, obind2, hDiv, hnd, hAtom, hd]
    cases c <;> rfl
  · simp only [hab, ↓reduceIte]
    by_cases hb : ρ.nat 1 = 0
    · have ha : ρ.nat 0 ≠ 0 := fun ha => hab ⟨ha, hb⟩
      have hdvd : ¬ (((ρ.nat 1 : Nat) : Int) ∣ ((ρ.nat 0 : Nat) : Int)) := by
        rw [hb]
        intro ⟨k, hk⟩
        omega
      simp [hEval, fDvdDiv, hEvalT, hAtom, hdvd, tvImp_some_false]
    · by_cases hd : ((ρ.nat 1 : Nat) : Int) ∣ ((ρ.nat 0 : Nat) : Int)
      · have hbInt : ((ρ.nat 1 : Nat) : Int) ≠ 0 := by omega
        have hdom : DivDom ((ρ.nat 0 : Nat) : Int) ((ρ.nat 1 : Nat) : Int) := ⟨hbInt, hd⟩
        have hcancel : (((ρ.nat 0 : Nat) : Int) / ((ρ.nat 1 : Nat) : Int)) * ((ρ.nat 1 : Nat) : Int) =
            ((ρ.nat 0 : Nat) : Int) := Int.ediv_mul_cancel hd
        simp [hEval, fDvdDiv, hEvalT, obind2, hDiv, hdom, hAtom, hd, hcancel, tvImp_some_true_some]
      · simp [hEval, fDvdDiv, hEvalT, hAtom, hd, tvImp_some_false]

/-- **Exact division: unguarded only at `a = b = 0`; the divisor guard restores agreement.**
For every connective semantics and reading, `b ∣ a → a / b * b = a` at `Nat` is Lean-valid
and rejected by the checker; its human value is undefined when `a = b = 0` and true at every
other environment. Adding the premise `¬ (b = 0)` gives a formula that is accepted by the
checker, Lean-valid and human-valid. -/
theorem restate_dvd_div (c : Conn) (r : SubReading) :
    LeanValid fDvdDiv ∧ guarded fDvdDiv = false ∧
      (∀ ρ, hEval c r fDvdDiv ρ = if ρ.nat 0 = 0 ∧ ρ.nat 1 = 0 then none else some true) ∧
      guarded fDvdDivGuarded = true ∧ LeanValid fDvdDivGuarded ∧ HumanValid c r fDvdDivGuarded := by
  have hv : LeanValid fDvdDiv := by
    intro ρ
    rw [evalJ_leanJ_iff]
    simp only [leanEvalF, fDvdDiv, leanEvalT, Srt.dvdP]
    exact Nat.div_mul_cancel
  have hg : guarded fDvdDivGuarded = true := by decide
  have hv' : LeanValid fDvdDivGuarded := by
    intro ρ
    rw [evalJ_leanJ_iff]
    simp only [leanEvalF, fDvdDivGuarded, fDvdDiv, leanEvalT, Srt.dvdP]
    exact fun _ => Nat.div_mul_cancel
  exact ⟨hv, by decide, hEval_dvdDiv c r, hg, hv',
    (leanValid_iff_humanValid_of_guarded c r _ hg).mp hv'⟩

/-- `¬ (a = 0) → b ∣ a → a / b * b = a` at `Nat` (a dividend guard instead of a divisor
guard). -/
def fDvdDivDividendGuard : Formula := .imp (.not (.eq vA (.natLit 0))) fDvdDiv

/-- **The divisor guard is not required for human validity.** For every connective semantics
and reading, `¬ (a = 0) → b ∣ a → a / b * b = a` at `Nat` is rejected by the checker, yet it
is Lean-valid and human-valid, and in particular human-true at `a = 5, b = 0`. -/
theorem humanValid_dvdDiv_dividend_guard (c : Conn) (r : SubReading) :
    guarded fDvdDivDividendGuard = false ∧ LeanValid fDvdDivDividendGuard ∧
      HumanValid c r fDvdDivDividendGuard ∧
      hEval c r fDvdDivDividendGuard (envAB 5 0) = some true := by
  have hlean : LeanValid fDvdDivDividendGuard := by
    intro ρ
    rw [evalJ_leanJ_iff]
    simp only [leanEvalF, fDvdDivDividendGuard, fDvdDiv, leanEvalT, Srt.dvdP]
    exact fun _ => Nat.div_mul_cancel
  have hhum : HumanValid c r fDvdDivDividendGuard := by
    intro ρ
    show tvImp c (hEval c r (.not (.eq vA (.natLit 0))) ρ) (hEval c r fDvdDiv ρ) = some true
    by_cases ha : ρ.nat 0 = 0
    · have hp : hEval c r (.not (.eq vA (.natLit 0))) ρ = some false := by
        simp [hEval, hEvalT, hAtom, tvNot, ha]
      rw [hp]
      exact tvImp_some_false c _
    · have hp : hEval c r (.not (.eq vA (.natLit 0))) ρ = some true := by
        simp [hEval, hEvalT, hAtom, tvNot, ha]
      have hb : hEval c r fDvdDiv ρ = some true := by
        rw [hEval_dvdDiv]
        simp [ha]
      rw [hp, hb]
      exact tvImp_some_true_some c true
  exact ⟨by decide, hlean, hhum, hhum _⟩

/-- **Named integer division.** The default quotient `a / b` (Euclidean) equals the
truncating quotient `Int.tdiv a b` iff `0 ≤ a ∨ b ∣ a ∨ b = 0`, and equals the flooring
quotient `Int.fdiv a b` iff `0 ≤ b ∨ b ∣ a`; the same conditions characterize agreement of
the remainders. -/
theorem restate_named_int_division (a b : Int) :
    (Int.tdiv a b = a / b ↔ (0 ≤ a ∨ b ∣ a ∨ b = 0)) ∧
      (Int.fdiv a b = a / b ↔ (0 ≤ b ∨ b ∣ a)) ∧
      (Int.tmod a b = a % b ↔ (0 ≤ a ∨ b ∣ a ∨ b = 0)) ∧
      (Int.fmod a b = a % b ↔ (0 ≤ b ∨ b ∣ a)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Int.tdiv_eq_ediv]
    by_cases h : 0 ≤ a ∨ b ∣ a
    · simp only [h, ↓reduceIte, Int.add_zero, true_iff]
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · simp only [h, ↓reduceIte]
      have : a / b + b.sign = a / b ↔ b = 0 := by
        rw [← Int.sign_eq_zero_iff_zero]
        omega
      rw [this]
      constructor
      · intro hb; exact Or.inr (Or.inr hb)
      · rintro (h0 | hd | hb)
        · exact absurd (Or.inl h0) h
        · exact absurd (Or.inr hd) h
        · exact hb
  · rw [Int.fdiv_eq_ediv]
    by_cases h : 0 ≤ b ∨ b ∣ a
    · simp [h]
    · simp only [h, ↓reduceIte, iff_false]
      omega
  · rw [Int.tmod_eq_emod]
    by_cases h : 0 ≤ a ∨ b ∣ a
    · simp only [h, ↓reduceIte, Int.natCast_zero, Int.sub_zero, true_iff]
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · simp only [h, ↓reduceIte]
      have hz : ((b.natAbs : Nat) : Int) = 0 ↔ b = 0 := by
        constructor
        · intro h0; exact Int.natAbs_eq_zero.mp (by omega)
        · intro h0; subst h0; rfl
      have : a % b - ((b.natAbs : Nat) : Int) = a % b ↔ ((b.natAbs : Nat) : Int) = 0 := by omega
      rw [this, hz]
      constructor
      · intro hb; exact Or.inr (Or.inr hb)
      · rintro (h0 | hd | hb)
        · exact absurd (Or.inl h0) h
        · exact absurd (Or.inr hd) h
        · exact hb
  · rw [Int.fmod_eq_emod]
    by_cases h : 0 ≤ b ∨ b ∣ a
    · simp [h]
    · simp only [h, ↓reduceIte, iff_false]
      omega

/-- **Guarded `Fin` addition** (Lean core). If `a.val + b.val < n`, the value of
`a + b : Fin n` is the exact sum. -/
theorem restate_fin_add_of_lt {n : Nat} (a b : Fin n) (h : a.val + b.val < n) :
    (a + b).val = a.val + b.val := by
  rw [Fin.val_add, Nat.mod_eq_of_lt h]

/-- Non-vacuity of `restate_fin_add_of_lt`: `1 + 2` in `Fin 5`. -/
theorem nv_restate_fin_add_of_lt : (1 : Fin 5).val + (2 : Fin 5).val < 5 := by decide

/-- Tightness of the bound in `restate_fin_add_of_lt`: `3 + 4` in `Fin 5` violates it and
the value is not the exact sum. -/
theorem ce_restate_fin_add_bound :
    ¬ ((3 : Fin 5).val + (4 : Fin 5).val < 5) ∧
      ((3 : Fin 5) + 4).val ≠ (3 : Fin 5).val + (4 : Fin 5).val := by
  decide

end Toy.Junk
