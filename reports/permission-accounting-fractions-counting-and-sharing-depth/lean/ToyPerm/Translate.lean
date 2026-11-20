import ToyPerm.Frac
import ToyPerm.Count

/-!
# Translations between counting and fractional permissions

Structure-preserving maps between the counting algebra and the fractional
algebra, in both directions. A map is required to send defined composites to
defined composites of the images (`PreservesOp`); readability is "non-empty
permissions map to non-empty permissions" and exclusivity is "the full / total
permission maps to the full / total permission".

* Counting into fractions: no composition-preserving map gives a single read
  token a non-zero fraction, because token bundles of every size exist while
  fractions are bounded by `1`. For counting with counts bounded by `N`, an
  explicit embedding with step `1/(3N+1)` exists that preserves and reflects
  composition; but for `N ≥ 1` no composition-preserving map reflects
  *compatibility*: every composition-preserving map gives compatible images to
  two sources `source N` or to two bundles `tokens N`, both incompatible pairs in
  bounded counting, and which of the two pairs it is depends on the map.
* Fractions into counting: every composition-preserving map from the full
  fractional algebra is constantly the empty permission (fractions are
  infinitely divisible, token bundles are not). Independently of divisibility,
  in any partial algebra an element that is a composite `h·h` of an element with
  itself cannot be sent to the total counting permission, because the total
  counting permission is not such a composite; this already rules out the
  finitely divisible half-grid `{0, 1/2, 1}`, while the asymmetric grid
  `{0, 1/4, 3/4, 1}` does map into counting with `1 ↦ total`.
-/

namespace Toy.Perm

open FracPerm Count PartialAlg

/-! ## Bounded counting -/

/-- `a` is a counting permission whose integer magnitude is at most `N`. -/
def inRange (N : Nat) : Count → Bool
  | none => true
  | some z => decide (-(N : Int) ≤ z) && decide (z ≤ (N : Int))

/-- `N`-bounded counting permissions: sources with at most `N` outstanding
tokens and bundles of at most `N` tokens. -/
abbrev CountB (N : Nat) := { a : Count // inRange N a = true }

/-- Composition of bounded counting permissions: the counting composite, if it
is defined and still within the bound. -/
def countBOp (N : Nat) (a b : CountB N) : Option (CountB N) :=
  match countOp a.1 b.1 with
  | none => none
  | some c => if hc : inRange N c = true then some ⟨c, hc⟩ else none

/-- The `N`-bounded counting algebra (counting permissions with counts at most
`N`), with unit `none`. -/
def countBAlg (N : Nat) : PartialAlg (CountB N) where
  op := countBOp N
  unit := ⟨none, rfl⟩

/-- The element `readToken` of `CountB 1`. -/
def CountB.tok1 : CountB 1 := ⟨readToken, rfl⟩
/-- The element `source 1` of `CountB 1`. -/
def CountB.src1 : CountB 1 := ⟨source 1, rfl⟩
/-- The element `total` of `CountB 1`. -/
def CountB.total1 : CountB 1 := ⟨total, rfl⟩

/-- Positive and negative examples of bounded counting: in `CountB 1`, a source
with one token absorbs it, but two single tokens no longer pool (the bundle of
two exceeds the bound). -/
theorem countBAlg_examples :
    (countBAlg 1).op CountB.src1 CountB.tok1 = some CountB.total1 ∧
      (countBAlg 1).op CountB.tok1 CountB.tok1 = none ∧
      inRange 1 (tokens 2) = false := by
  decide

/-- The bounded composite is the counting composite whenever it is defined. -/
theorem countBOp_eq_some_iff (N : Nat) (a b c : CountB N) :
    countBOp N a b = some c ↔ countOp a.1 b.1 = some c.1 := by
  unfold countBOp
  cases h : countOp a.1 b.1 with
  | none => simp
  | some r =>
    dsimp only
    constructor
    · intro hr
      split at hr
      · cases hr; rfl
      · cases hr
    · intro hr
      cases hr
      simp [c.2]

theorem countBOp_some_some (N : Nat) (i j : Int) (hi : inRange N (some i) = true)
    (hj : inRange N (some j) = true) :
    countBOp N ⟨some i, hi⟩ ⟨some j, hj⟩ =
      if h : ((i < 0 ∨ j < 0) ∧ (0 ≤ i + j ∨ (i < 0 ∧ j < 0))) ∧ inRange N (some (i + j)) = true
      then some ⟨some (i + j), h.2⟩ else none := by
  unfold countBOp
  simp only [countOp_some_some]
  by_cases h1 : (i < 0 ∨ j < 0) ∧ (0 ≤ i + j ∨ (i < 0 ∧ j < 0))
  · simp only [h1, ↓reduceIte, true_and]
  · simp [h1]

/-- The rational value of the bounded embedding: with step `ε = 1/(3N+1)`, the
source `some z` (`z ≥ 0`) has value `1 - z·ε` and the bundle `some (-k)` has
value `k·ε`; the empty permission has value `0`. With this step two token
bundles sum to at most `2N·ε`, strictly below the value `1 - N·ε` of every
source, so pooled tokens are never confused with a source. -/
def countEmbedVal (N : Nat) : Count → Rat
  | none => 0
  | some z => if 0 ≤ z then 1 - (z : Rat) / (3 * N + 1) else (-(z : Rat)) / (3 * N + 1)

/-- The bounded embedding of `N`-bounded counting permissions into fractional
permissions: `countEmbedVal`, clamped into `[0, 1]` by `ofRat` so that the
definition carries no proof obligations (no clamping occurs on `CountB N`). -/
def countEmbed (N : Nat) (a : CountB N) : FracPerm := ofRat (countEmbedVal N a.1)

/-- Example values for `N = 1` (`ε = 1/4`): a token maps to `1/4`, a source with
one token to `3/4`, the total permission to `1`. -/
theorem countEmbed_one_values :
    (countEmbed 1 CountB.tok1).val = 1 / 4 ∧ (countEmbed 1 CountB.src1).val = 3 / 4 ∧
      countEmbed 1 CountB.total1 = full := by
  decide +kernel

/-! ### Proof helpers for the bounded embedding -/

private theorem r4a_rat_div_mul_cancel {a b : Rat} (hb : b ≠ 0) : (a / b) * b = a := by
  rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel b hb, Rat.mul_one]

private theorem r4a_rat_add_div (a b c : Rat) : (a + b) / c = a / c + b / c := by
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.add_mul]

private theorem r4a_rat_sub_div (a b c : Rat) : (a - b) / c = a / c - b / c := by
  rw [Rat.div_def, Rat.div_def, Rat.div_def]; grind

private theorem r4a_rat_div_nonneg {a b : Rat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  rw [Rat.div_def]
  have hinv : 0 < b⁻¹ := Rat.inv_pos.mpr hb
  have := Rat.mul_le_mul_of_nonneg_right ha (show (0 : Rat) ≤ b⁻¹ by grind)
  simp at this
  exact this

private theorem r4a_rat_div_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [Rat.div_def]
  have hinv : 0 < b⁻¹ := Rat.inv_pos.mpr hb
  have := Rat.mul_lt_mul_of_pos_right ha hinv
  simp at this
  exact this

private theorem r4a_rat_div_le_one {a b : Rat} (hab : a ≤ b) (hb : 0 < b) : a / b ≤ 1 := by
  rw [Rat.div_def]
  have hinv : 0 ≤ b⁻¹ := by have := Rat.inv_pos.mpr hb; grind
  have := Rat.mul_le_mul_of_nonneg_right hab hinv
  rwa [Rat.mul_inv_cancel b (by grind)] at this

private theorem r4a_rat_div_lt_one {a b : Rat} (hab : a < b) (hb : 0 < b) : a / b < 1 := by
  rw [Rat.div_def]
  have hinv : 0 < b⁻¹ := Rat.inv_pos.mpr hb
  have := Rat.mul_lt_mul_of_pos_right hab hinv
  rwa [Rat.mul_inv_cancel b (by grind)] at this

private theorem r4a_int_ratCast_inj {a b : Int} (h : (a : Rat) = (b : Rat)) : a = b := by
  exact_mod_cast h

private theorem r4a_countBAlg_isPCM (N : Nat) : (countBAlg N).IsPCM := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    show countBOp N a b = countBOp N b a
    unfold countBOp
    have hcomm := countAlg_isPCM_cancel_positive.1.1 a.1 b.1
    change countOp a.1 b.1 = countOp b.1 a.1 at hcomm
    rw [hcomm]
  · intro a b c
    show (countBOp N a b).bind (fun ab => countBOp N ab c) =
      (countBOp N b c).bind (fun bc => countBOp N a bc)
    rcases a with ⟨_ | i, hi⟩
    · have h1 : countBOp N ⟨none, hi⟩ b = some b := by simp [countBOp, countOp, b.2]
      rw [h1, Option.bind_some]
      cases hbc : countBOp N b c with
      | none => rfl
      | some bc => simp [countBOp, countOp, bc.2]
    rcases b with ⟨_ | j, hj⟩
    · have h1 : countBOp N ⟨some i, hi⟩ ⟨none, hj⟩ = some ⟨some i, hi⟩ := by
        simp [countBOp, countOp, hi]
      have h2 : countBOp N ⟨none, hj⟩ c = some c := by simp [countBOp, countOp, c.2]
      rw [h1, h2]; rfl
    rcases c with ⟨_ | k, hk⟩
    · have h2 : countBOp N ⟨some j, hj⟩ ⟨none, hk⟩ = some ⟨some j, hj⟩ := by
        simp [countBOp, countOp, hj]
      rw [h2, Option.bind_some]
      cases hab : countBOp N ⟨some i, hi⟩ ⟨some j, hj⟩ with
      | none => rfl
      | some ab =>
        rcases ab with ⟨_ | m, hm⟩ <;> simp [countBOp, countOp, hm]
    have hri : -(N : Int) ≤ i ∧ i ≤ (N : Int) := by simpa [inRange] using hi
    have hrj : -(N : Int) ≤ j ∧ j ≤ (N : Int) := by simpa [inRange] using hj
    have hrk : -(N : Int) ≤ k ∧ k ≤ (N : Int) := by simpa [inRange] using hk
    rw [countBOp_some_some, countBOp_some_some]
    by_cases hL1 : ((i < 0 ∨ j < 0) ∧ (0 ≤ i + j ∨ (i < 0 ∧ j < 0))) ∧
        inRange N (some (i + j)) = true <;>
      by_cases hR1 : ((j < 0 ∨ k < 0) ∧ (0 ≤ j + k ∨ (j < 0 ∧ k < 0))) ∧
        inRange N (some (j + k)) = true
    · simp only [dite_eq_left_of_eq_true (eq_true hL1), dite_eq_left_of_eq_true (eq_true hR1),
        Option.bind_some, countBOp_some_some]
      by_cases hL2 : ((i + j < 0 ∨ k < 0) ∧ (0 ≤ i + j + k ∨ (i + j < 0 ∧ k < 0))) ∧
          inRange N (some (i + j + k)) = true <;>
        by_cases hR2 : ((i < 0 ∨ j + k < 0) ∧ (0 ≤ i + (j + k) ∨ (i < 0 ∧ j + k < 0))) ∧
          inRange N (some (i + (j + k))) = true
      · simp only [dite_eq_left_of_eq_true (eq_true hL2), dite_eq_left_of_eq_true (eq_true hR2),
          Option.some.injEq, Subtype.mk.injEq, Option.some.injEq]; omega
      · exfalso
        have h3 : -(N : Int) ≤ i + j + k ∧ i + j + k ≤ (N : Int) := by simpa [inRange] using hL2.2
        exact hR2 ⟨by omega, by simp [inRange]; omega⟩
      · exfalso
        have h3 : -(N : Int) ≤ i + (j + k) ∧ i + (j + k) ≤ (N : Int) := by
          simpa [inRange] using hR2.2
        exact hL2 ⟨by omega, by simp [inRange]; omega⟩
      · simp only [dite_eq_right_of_eq_false (eq_false hL2), dite_eq_right_of_eq_false (eq_false hR2)]
    · simp only [dite_eq_left_of_eq_true (eq_true hL1), dite_eq_right_of_eq_false (eq_false hR1),
        Option.bind_some, Option.bind_none, countBOp_some_some]
      split
      · rename_i hL2
        exfalso
        have h3 : -(N : Int) ≤ i + j + k ∧ i + j + k ≤ (N : Int) := by simpa [inRange] using hL2.2
        exact hR1 ⟨by omega, by simp [inRange]; omega⟩
      · rfl
    · simp only [dite_eq_right_of_eq_false (eq_false hL1), dite_eq_left_of_eq_true (eq_true hR1),
        Option.bind_none, Option.bind_some, countBOp_some_some]
      split
      · rename_i hR2
        exfalso
        have h3 : -(N : Int) ≤ i + (j + k) ∧ i + (j + k) ≤ (N : Int) := by
          simpa [inRange] using hR2.2
        exact hL1 ⟨by omega, by simp [inRange]; omega⟩
      · rfl
    · simp only [dite_eq_right_of_eq_false (eq_false hL1), dite_eq_right_of_eq_false (eq_false hR1),
        Option.bind_none]
  · intro a
    show countBOp N ⟨none, rfl⟩ a = some a
    simp [countBOp, countOp, a.2]

private theorem r4a_countBAlg_exclusive_iff (N : Nat) (a : CountB N) :
    (countBAlg N).Exclusive a ↔ a = ⟨total, by simp [inRange, total]⟩ := by
  have htot_in : inRange N total = true := by simp [inRange, total]
  constructor
  · intro h
    rcases a with ⟨_ | z, hz⟩
    · have hc : (countBAlg N).Compat ⟨none, hz⟩ ⟨total, htot_in⟩ := by
        simp [Compat, countBAlg, countBOp, countOp, htot_in]
      have hne := congrArg Subtype.val (h _ hc)
      simp [countBAlg, total] at hne
    · have hrz : -(N : Int) ≤ z ∧ z ≤ (N : Int) := by simpa [inRange] using hz
      by_cases hz0 : z = 0
      · subst hz0; rfl
      · exfalso
        by_cases hpos : 0 < z
        · have htok : inRange N (some (-1)) = true := by simp [inRange]; omega
          have hc : (countBAlg N).Compat ⟨some z, hz⟩ ⟨some (-1), htok⟩ := by
            simp only [Compat, countBAlg]
            rw [countBOp_some_some]
            have hcond : ((z < 0 ∨ (-1 : Int) < 0) ∧ (0 ≤ z + -1 ∨ (z < 0 ∧ (-1 : Int) < 0))) ∧
                inRange N (some (z + -1)) = true := ⟨by omega, by simp [inRange]; omega⟩
            rw [dite_eq_left_of_eq_true (eq_true hcond)]; rfl
          have hne := congrArg Subtype.val (h _ hc)
          simp [countBAlg] at hne
        · have hsrc : inRange N (some (-z)) = true := by simp [inRange]; omega
          have hc : (countBAlg N).Compat ⟨some z, hz⟩ ⟨some (-z), hsrc⟩ := by
            simp only [Compat, countBAlg]
            rw [countBOp_some_some]
            have hcond : ((z < 0 ∨ -z < 0) ∧ (0 ≤ z + -z ∨ (z < 0 ∧ -z < 0))) ∧
                inRange N (some (z + -z)) = true := ⟨by omega, by simp [inRange]; omega⟩
            rw [dite_eq_left_of_eq_true (eq_true hcond)]; rfl
          have hne := congrArg Subtype.val (h _ hc)
          simp [countBAlg] at hne
  · rintro rfl ⟨_ | j, hj⟩ hb
    · rfl
    · simp only [Compat, countBAlg, total] at hb
      rw [countBOp_some_some] at hb
      split at hb
      · rename_i hcond; omega
      · simp at hb

private theorem r4a_countEmbedVal_bounds (N : Nat) (a : CountB N) :
    0 ≤ countEmbedVal N a.1 ∧ countEmbedVal N a.1 ≤ 1 := by
  rcases a with ⟨_ | z, hz⟩
  · simp [countEmbedVal]; grind
  · have hrange : -(N : Int) ≤ z ∧ z ≤ (N : Int) := by simpa [inRange] using hz
    have hden : (0 : Rat) < 3 * (N : Rat) + 1 := by grind
    simp only [countEmbedVal]
    split
    · have hz0 : (0 : Rat) ≤ (z : Rat) := by exact_mod_cast (by assumption : (0 : Int) ≤ z)
      have hzN : (z : Rat) ≤ (N : Rat) := by exact_mod_cast hrange.2
      have hdiv0 := r4a_rat_div_nonneg hz0 hden
      have hdiv1 := r4a_rat_div_le_one (by grind : (z : Rat) ≤ 3 * (N : Rat) + 1) hden
      grind
    · have hzneg : (0 : Rat) ≤ -(z : Rat) := by
        have : (0 : Int) ≤ -z := by omega
        exact_mod_cast this
      have hzN : -(z : Rat) ≤ (N : Rat) := by
        have : -z ≤ (N : Int) := by omega
        exact_mod_cast this
      exact ⟨r4a_rat_div_nonneg hzneg hden,
        r4a_rat_div_le_one (by grind : -(z : Rat) ≤ 3 * (N : Rat) + 1) hden⟩

private theorem r4a_countEmbed_val (N : Nat) (a : CountB N) :
    (countEmbed N a).val = countEmbedVal N a.1 :=
  ofRat_val_of (r4a_countEmbedVal_bounds N a).1 (r4a_countEmbedVal_bounds N a).2

private theorem r4a_countEmbed_inj (N : Nat) : Function.Injective (countEmbed N) := by
  intro a b h
  have hv : countEmbedVal N a.1 = countEmbedVal N b.1 := by
    have := congrArg FracPerm.val h
    rwa [r4a_countEmbed_val, r4a_countEmbed_val] at this
  have hden : (3 * (N : Rat) + 1) ≠ 0 := by grind
  apply Subtype.ext
  rcases a with ⟨_ | i, hi⟩ <;> rcases b with ⟨_ | j, hj⟩
  · rfl
  · have hrange : -(N : Int) ≤ j ∧ j ≤ (N : Int) := by simpa [inRange] using hj
    simp only [countEmbedVal] at hv
    split at hv
    · have h1 : (j : Rat) / (3 * (N : Rat) + 1) = 1 := by grind
      have h2 := congrArg (· * (3 * (N : Rat) + 1)) h1
      rw [r4a_rat_div_mul_cancel hden] at h2
      have : j = 3 * (N : Int) + 1 := r4a_int_ratCast_inj (by push_cast; grind)
      omega
    · have h2 := congrArg (· * (3 * (N : Rat) + 1)) hv
      rw [r4a_rat_div_mul_cancel hden] at h2
      have : j = 0 := r4a_int_ratCast_inj (by grind)
      omega
  · have hrange : -(N : Int) ≤ i ∧ i ≤ (N : Int) := by simpa [inRange] using hi
    simp only [countEmbedVal] at hv
    split at hv
    · have h1 : (i : Rat) / (3 * (N : Rat) + 1) = 1 := by grind
      have h2 := congrArg (· * (3 * (N : Rat) + 1)) h1
      rw [r4a_rat_div_mul_cancel hden] at h2
      have : i = 3 * (N : Int) + 1 := r4a_int_ratCast_inj (by push_cast; grind)
      omega
    · have h2 := congrArg (· * (3 * (N : Rat) + 1)) hv
      rw [r4a_rat_div_mul_cancel hden] at h2
      have : i = 0 := r4a_int_ratCast_inj (by grind)
      omega
  · have hri : -(N : Int) ≤ i ∧ i ≤ (N : Int) := by simpa [inRange] using hi
    have hrj : -(N : Int) ≤ j ∧ j ≤ (N : Int) := by simpa [inRange] using hj
    simp only [countEmbedVal] at hv
    split at hv <;> split at hv
    · have h1 : (i : Rat) / (3 * (N : Rat) + 1) = (j : Rat) / (3 * (N : Rat) + 1) := by grind
      have h2 := congrArg (· * (3 * (N : Rat) + 1)) h1
      rw [r4a_rat_div_mul_cancel hden, r4a_rat_div_mul_cancel hden] at h2
      have : i = j := r4a_int_ratCast_inj h2
      subst this; rfl
    · have h1 : ((i : Rat) - (j : Rat)) / (3 * (N : Rat) + 1) = 1 := by
        rw [r4a_rat_sub_div]; grind
      have h2 := congrArg (· * (3 * (N : Rat) + 1)) h1
      rw [r4a_rat_div_mul_cancel hden] at h2
      have : i - j = 3 * (N : Int) + 1 := r4a_int_ratCast_inj (by push_cast; grind)
      omega
    · have h1 : ((j : Rat) - (i : Rat)) / (3 * (N : Rat) + 1) = 1 := by
        rw [r4a_rat_sub_div]; grind
      have h2 := congrArg (· * (3 * (N : Rat) + 1)) h1
      rw [r4a_rat_div_mul_cancel hden] at h2
      have : j - i = 3 * (N : Int) + 1 := r4a_int_ratCast_inj (by push_cast; grind)
      omega
    · have h2 := congrArg (· * (3 * (N : Rat) + 1)) hv
      rw [r4a_rat_div_mul_cancel hden, r4a_rat_div_mul_cancel hden] at h2
      have : i = j := r4a_int_ratCast_inj (by grind)
      subst this; rfl

/-- **Bounded counting embeds into fractions, preserving and reflecting
composition.** For every bound `N`, the `N`-bounded counting algebra is a
partial commutative monoid, and the map `countEmbed N` (token bundle of size `k`
↦ `k/(3N+1)`, source with `n` outstanding tokens ↦ `1 - n/(3N+1)`, empty ↦ `0`)
is injective, sends the unit to `0`, satisfies `a·b = c ↔ f a · f b = f c` for
all `a b c` (so it sends every defined composite to the composite of the images,
and a fractional composite of two images that is itself an image comes from a
bounded-counting composite), maps exactly the exclusive elements to exclusive
fractions, and maps exactly the non-empty permissions to non-zero fractions. -/
theorem countBEmbed_injective_preserves_reflects_op_exclusive_readable (N : Nat) :
    (countBAlg N).IsPCM ∧ Function.Injective (countEmbed N) ∧
      PreservesUnit (countBAlg N) fracAlg (countEmbed N) ∧
      (∀ a b c, (countBAlg N).op a b = some c ↔
        fracAlg.op (countEmbed N a) (countEmbed N b) = some (countEmbed N c)) ∧
      (∀ a, (countBAlg N).Exclusive a ↔ fracAlg.Exclusive (countEmbed N a)) ∧
      (∀ a, a ≠ (countBAlg N).unit ↔ countEmbed N a ≠ fracAlg.unit) := by
  have hden : (3 * (N : Rat) + 1) ≠ 0 := by grind
  have hden_pos : (0 : Rat) < 3 * (N : Rat) + 1 := by grind
  have hunit : PreservesUnit (countBAlg N) fracAlg (countEmbed N) := by
    show countEmbed N ⟨none, rfl⟩ = zero
    ext; rw [r4a_countEmbed_val]; rfl
  have htot : countEmbed N ⟨total, by simp [inRange, total]⟩ = full := by
    ext; rw [r4a_countEmbed_val]; simp [countEmbedVal, total]; grind
  refine ⟨r4a_countBAlg_isPCM N, r4a_countEmbed_inj N, hunit, ?_, ?_, ?_⟩
  · intro a b c
    show countBOp N a b = some c ↔
      fracOp (countEmbed N a) (countEmbed N b) = some (countEmbed N c)
    rw [countBOp_eq_some_iff, fracOp_eq_some_iff, r4a_countEmbed_val, r4a_countEmbed_val,
      r4a_countEmbed_val]
    rcases a with ⟨_ | i, hi⟩
    · simp only [countOp, Option.some.injEq, countEmbedVal]
      constructor
      · intro h; rw [← h]; grind
      · intro h
        have h' : countEmbedVal N b.1 = countEmbedVal N c.1 := by
          have : 0 + countEmbedVal N b.1 = countEmbedVal N c.1 := h
          grind
        have heq : b = c :=
          r4a_countEmbed_inj N (by ext; rw [r4a_countEmbed_val, r4a_countEmbed_val]; exact h')
        exact congrArg Subtype.val heq
    rcases b with ⟨_ | j, hj⟩
    · simp only [countOp, Option.some.injEq, countEmbedVal]
      constructor
      · intro h; rw [← h]; grind
      · intro h
        have h' : countEmbedVal N (⟨some i, hi⟩ : CountB N).1 = countEmbedVal N c.1 := by
          have : countEmbedVal N (some i) + 0 = countEmbedVal N c.1 := h
          grind
        have heq : (⟨some i, hi⟩ : CountB N) = c :=
          r4a_countEmbed_inj N (by ext; rw [r4a_countEmbed_val, r4a_countEmbed_val]; exact h')
        exact congrArg Subtype.val heq
    have hri : -(N : Int) ≤ i ∧ i ≤ (N : Int) := by simpa [inRange] using hi
    have hrj : -(N : Int) ≤ j ∧ j ≤ (N : Int) := by simpa [inRange] using hj
    rcases c with ⟨_ | k, hk⟩
    · constructor
      · intro h; rw [countOp_some_some_eq_some] at h; cases h.2
      · intro h
        have hpos_i : 0 < countEmbedVal N (some i) := by
          simp only [countEmbedVal]; split
          · have : (i : Rat) ≤ (N : Rat) := by exact_mod_cast hri.2
            have := r4a_rat_div_lt_one (by grind : (i : Rat) < 3 * (N : Rat) + 1) hden_pos
            grind
          · have : (0 : Rat) < -(i : Rat) := by
              have : (0 : Int) < -i := by omega
              exact_mod_cast this
            exact r4a_rat_div_pos this hden_pos
        have hnn_j := (r4a_countEmbedVal_bounds N ⟨some j, hj⟩).1
        have hc0 : countEmbedVal N (⟨none, hk⟩ : CountB N).1 = 0 := rfl
        rw [hc0] at h
        grind
    have hrk : -(N : Int) ≤ k ∧ k ≤ (N : Int) := by simpa [inRange] using hk
    rw [countOp_some_some_eq_some]
    constructor
    · rintro ⟨hcond, hsum⟩
      simp only [Option.some.injEq] at hsum
      simp only [countEmbedVal]
      split <;> split <;> split
      · omega
      · omega
      · have hk_eq : (k : Rat) = (i : Rat) + (j : Rat) := by
          have : ((i + j : Int) : Rat) = (k : Rat) := by exact_mod_cast hsum.symm
          push_cast at this; exact this.symm
        rw [hk_eq, r4a_rat_add_div]; grind
      · omega
      · have hk_eq : (k : Rat) = (i : Rat) + (j : Rat) := by
          have : ((i + j : Int) : Rat) = (k : Rat) := by exact_mod_cast hsum.symm
          push_cast at this; exact this.symm
        rw [hk_eq, r4a_rat_add_div]; grind
      · omega
      · omega
      · have hk_eq : -(k : Rat) = -(i : Rat) + -(j : Rat) := by
          have : ((i + j : Int) : Rat) = (k : Rat) := by exact_mod_cast hsum.symm
          push_cast at this; grind
        rw [hk_eq, r4a_rat_add_div]
    · intro h
      simp only [countEmbedVal] at h
      have hmul := congrArg (· * (3 * (N : Rat) + 1)) h
      have h1 := r4a_rat_div_mul_cancel (a := (i : Rat)) hden
      have h1' := r4a_rat_div_mul_cancel (a := -(i : Rat)) hden
      have h2 := r4a_rat_div_mul_cancel (a := (j : Rat)) hden
      have h2' := r4a_rat_div_mul_cancel (a := -(j : Rat)) hden
      have h3 := r4a_rat_div_mul_cancel (a := (k : Rat)) hden
      have h3' := r4a_rat_div_mul_cancel (a := -(k : Rat)) hden
      split at hmul <;> split at hmul <;> split at hmul
      · have hInt : (3 * (N : Int) + 1 - i) + (3 * (N : Int) + 1 - j) = 3 * (N : Int) + 1 - k :=
          r4a_int_ratCast_inj (by push_cast; grind)
        omega
      · have hInt : (3 * (N : Int) + 1 - i) + (3 * (N : Int) + 1 - j) = -k :=
          r4a_int_ratCast_inj (by push_cast; grind)
        omega
      · have hInt : (3 * (N : Int) + 1 - i) + (-j) = 3 * (N : Int) + 1 - k :=
          r4a_int_ratCast_inj (by push_cast; grind)
        exact ⟨by omega, show some k = some (i + j) by congr 1; omega⟩
      · have hInt : (3 * (N : Int) + 1 - i) + (-j) = -k :=
          r4a_int_ratCast_inj (by push_cast; grind)
        omega
      · have hInt : (-i) + (3 * (N : Int) + 1 - j) = 3 * (N : Int) + 1 - k :=
          r4a_int_ratCast_inj (by push_cast; grind)
        exact ⟨by omega, show some k = some (i + j) by congr 1; omega⟩
      · have hInt : (-i) + (3 * (N : Int) + 1 - j) = -k :=
          r4a_int_ratCast_inj (by push_cast; grind)
        omega
      · have hInt : (-i) + (-j) = 3 * (N : Int) + 1 - k :=
          r4a_int_ratCast_inj (by push_cast; grind)
        omega
      · have hInt : (-i) + (-j) = -k :=
          r4a_int_ratCast_inj (by push_cast; grind)
        exact ⟨by omega, show some k = some (i + j) by congr 1; omega⟩
  · intro a
    rw [r4a_countBAlg_exclusive_iff, fracAlg_exclusive_iff, ← htot]
    exact ⟨fun h => h ▸ rfl, fun h => r4a_countEmbed_inj N h⟩
  · intro a
    rw [← hunit]
    exact ⟨fun h he => h (r4a_countEmbed_inj N he), fun h he => h (he ▸ rfl)⟩

/-- The composition clause of
`countBEmbed_injective_preserves_reflects_op_exclusive_readable` contains
composition preservation. -/
theorem preservesOp_of_op_iff {α β : Type} (A : PartialAlg α) (B : PartialAlg β) (f : α → β)
    (h : ∀ a b c, A.op a b = some c ↔ B.op (f a) (f b) = some (f c)) : PreservesOp A B f :=
  fun a b c hab => (h a b c).1 hab

/-- The four elements of `CountB 1`. -/
def countB1Elems : List (CountB 1) := [⟨none, rfl⟩, ⟨some (-1), rfl⟩, ⟨some 0, rfl⟩, ⟨some 1, rfl⟩]

theorem countB1_mem (a : CountB 1) : a ∈ countB1Elems := by
  rcases a with ⟨_ | i, hi⟩
  · simp [countB1Elems]
  · have : -1 ≤ i ∧ i ≤ 1 := by simpa [inRange] using hi
    obtain rfl | rfl | rfl : i = -1 ∨ i = 0 ∨ i = 1 := by omega
    all_goals simp [countB1Elems]

theorem countB1_op_iff_check :
    ∀ a ∈ countB1Elems, ∀ b ∈ countB1Elems, ∀ c ∈ countB1Elems,
      countBOp 1 a b = some c ↔ fracOp (countEmbed 1 a) (countEmbed 1 b) = some (countEmbed 1 c) := by
  decide +kernel

theorem countB1_injective_check :
    ∀ a ∈ countB1Elems, ∀ b ∈ countB1Elems, countEmbed 1 a = countEmbed 1 b → a = b := by
  decide +kernel

/-- Non-vacuity witness for
`countBEmbed_injective_preserves_reflects_op_exclusive_readable` (the case
`N = 1`, fully checked): `countEmbed 1` is injective, sends the unit to `0`,
satisfies `a·b = c ↔ f a · f b = f c`, gives the token the non-zero value `1/4`,
and sends the total permission to the exclusive fraction `1`. -/
theorem countB1Embed_injective_unit_op_iff :
    Function.Injective (countEmbed 1) ∧
      PreservesUnit (countBAlg 1) fracAlg (countEmbed 1) ∧
      (∀ a b c, (countBAlg 1).op a b = some c ↔
        fracAlg.op (countEmbed 1 a) (countEmbed 1 b) = some (countEmbed 1 c)) ∧
      countEmbed 1 CountB.tok1 ≠ zero ∧ fracAlg.Exclusive (countEmbed 1 CountB.total1) := by
  refine ⟨fun a b h => countB1_injective_check a (countB1_mem a) b (countB1_mem b) h, ?_,
    fun a b c => countB1_op_iff_check a (countB1_mem a) b (countB1_mem b) c (countB1_mem c),
    by decide +kernel, ?_⟩
  · show ofRat 0 = zero
    ext; exact ofRat_val_of (by grind) (by grind)
  · rw [fracAlg_exclusive_iff]; decide +kernel

/-- The embedding of `CountB 1` with the step `1/3` (token ↦ `1/3`,
source with one token ↦ `2/3`, total ↦ `1`). -/
def countEmbedThirds (a : CountB 1) : FracPerm :=
  ofRat (match a.1 with
    | none => 0
    | some z => if 0 ≤ z then 1 - (z : Rat) / 3 else (-(z : Rat)) / 3)

theorem countB1_thirds_preservesOp_check :
    ∀ a ∈ countB1Elems, ∀ b ∈ countB1Elems, ∀ c ∈ countB1Elems,
      countBOp 1 a b = some c → fracOp (countEmbedThirds a) (countEmbedThirds b) = some (countEmbedThirds c) := by
  decide +kernel

/-- **The step matters for reflection.** With the step `1/3` instead of `1/4`,
the embedding of `CountB 1` still preserves every defined composite, but it no
longer reflects composition: two single read tokens do not compose in `CountB 1`,
yet their images `1/3 + 1/3` compose to `2/3`, the image of a source with one
outstanding token. -/
theorem countEmbedThirds_preservesOp_not_reflecting :
    PreservesOp (countBAlg 1) fracAlg countEmbedThirds ∧
      (countBAlg 1).op CountB.tok1 CountB.tok1 = none ∧
      fracAlg.op (countEmbedThirds CountB.tok1) (countEmbedThirds CountB.tok1) =
        some (countEmbedThirds CountB.src1) := by
  refine ⟨fun a b c h => countB1_thirds_preservesOp_check a (countB1_mem a) b (countB1_mem b) c
    (countB1_mem c) h, by decide, ?_⟩
  show fracOp _ _ = _
  decide +kernel

/-! ## Bounded counting into fractions: compatibility cannot be reflected -/

/-- **For every bound `N ≥ 1`, no composition-preserving map from `N`-bounded
counting to fractions reflects compatibility.** There is no map `f` from
`N`-bounded counting permissions to fractional permissions that sends every
defined composite to the composite of the images and such that any two
permissions whose images are compatible fractions are compatible in `N`-bounded
counting. (For every composition-preserving `f`, `source N · tokens N = total`
forces `f (source N) + f (tokens N) ≤ 1`. If `f` reflected compatibility, then,
two sources `source N` being incompatible, `f (source N) > 1/2`; hence
`f (tokens N) < 1/2`, and the images of two bundles `tokens N` would be
compatible although `2N` tokens exceed the bound. Without assuming reflection,
the pair whose images are compatible can be either of the two:
`opPreserving_map_countB_to_frac_sources_or_bundles_compat` and
`opPreserving_maps_countB_to_frac_keep_either_pair_incompatible`.) -/
theorem no_opPreserving_map_countB_to_frac_reflecting_compat (N : Nat) (hN : 1 ≤ N) :
    ¬ ∃ f : CountB N → FracPerm, PreservesOp (countBAlg N) fracAlg f ∧
      ∀ a b, fracAlg.Compat (f a) (f b) → (countBAlg N).Compat a b := by
  rintro ⟨f, hop, hrefl⟩
  let srcN : CountB N := ⟨some (N : Int), by simp [inRange]⟩
  let tokN : CountB N := ⟨some (-(N : Int)), by simp [inRange]⟩
  let tot : CountB N := ⟨some 0, by simp [inRange]⟩
  have hcomb : (countBAlg N).op srcN tokN = some tot := by
    show countBOp N srcN tokN = some tot
    rw [countBOp_eq_some_iff, countOp_some_some_eq_some]
    exact ⟨by omega, show some 0 = some ((N : Int) + -(N : Int)) by congr 1; omega⟩
  have hsum : (f srcN).val + (f tokN).val ≤ 1 := by
    have h := hop srcN tokN tot hcomb
    change fracOp _ _ = some (f tot) at h
    rw [fracOp_eq_some_iff] at h
    have := (f tot).le_one
    grind
  have hsrc : ¬ fracAlg.Compat (f srcN) (f srcN) := by
    intro hc
    have h := hrefl srcN srcN hc
    simp only [Compat, countBAlg, srcN] at h
    rw [countBOp_some_some] at h
    split at h
    · rename_i hcond; omega
    · simp at h
  rw [fracAlg_compat_iff] at hsrc
  have htok : fracAlg.Compat (f tokN) (f tokN) := by
    rw [fracAlg_compat_iff]; grind
  have h := hrefl tokN tokN htok
  simp only [Compat, countBAlg, tokN] at h
  rw [countBOp_some_some] at h
  split at h
  · rename_i hcond
    have hr : -(N : Int) ≤ -(N : Int) + -(N : Int) ∧ -(N : Int) + -(N : Int) ≤ (N : Int) := by
      simpa [inRange] using hcond.2
    omega
  · simp at h

/-- The two elements of `CountB 0`. -/
def countB0Elems : List (CountB 0) := [⟨none, rfl⟩, ⟨some 0, rfl⟩]

theorem countB0_mem (a : CountB 0) : a ∈ countB0Elems := by
  rcases a with ⟨_ | i, hi⟩
  · simp [countB0Elems]
  · have : i = 0 := by simp [inRange] at hi; omega
    subst this; simp [countB0Elems]

theorem countB0_check :
    (∀ a ∈ countB0Elems, ∀ b ∈ countB0Elems, ∀ c ∈ countB0Elems,
      countBOp 0 a b = some c → fracOp (countEmbed 0 a) (countEmbed 0 b) = some (countEmbed 0 c)) ∧
    (∀ a ∈ countB0Elems, ∀ b ∈ countB0Elems,
      (fracOp (countEmbed 0 a) (countEmbed 0 b)).isSome = true → (countBOp 0 a b).isSome = true) := by
  decide +kernel

/-- **Positive control** for `no_opPreserving_map_countB_to_frac_reflecting_compat`
and tightness of `hN` (canonical form, `N = 0`): `0`-bounded counting is the
two-point exclusive algebra `{none, total}`, and `countEmbed 0` (`none ↦ 0`,
`total ↦ 1`) preserves composition and reflects compatibility. -/
theorem countB0Embed_preservesOp_reflects_compat :
    ¬ (1 ≤ 0) ∧ PreservesOp (countBAlg 0) fracAlg (countEmbed 0) ∧
      ∀ a b, fracAlg.Compat (countEmbed 0 a) (countEmbed 0 b) → (countBAlg 0).Compat a b :=
  ⟨by decide,
    fun a b c h => countB0_check.1 a (countB0_mem a) b (countB0_mem b) c (countB0_mem c) h,
    fun a b h => countB0_check.2 a (countB0_mem a) b (countB0_mem b) h⟩

/-- The map from `CountB 1` sending every non-empty permission to `1`. -/
def countB1AllFull (a : CountB 1) : FracPerm := if a.1 = none then zero else full

theorem countB1AllFull_check :
    ∀ a ∈ countB1Elems, ∀ b ∈ countB1Elems,
      (fracOp (countB1AllFull a) (countB1AllFull b)).isSome = true → (countBOp 1 a b).isSome = true := by
  decide +kernel

/-- Tightness of the composition-preservation conjunct in
`no_opPreserving_map_countB_to_frac_reflecting_compat` (canonical form, `N = 1`):
`1 ≤ 1`, and the map sending every non-empty permission to `1` reflects
compatibility (its images are compatible only when one side is empty). It does
not preserve composition. -/
theorem countB1AllFull_reflects_compat :
    1 ≤ 1 ∧ ∃ f : CountB 1 → FracPerm,
      ∀ a b, fracAlg.Compat (f a) (f b) → (countBAlg 1).Compat a b :=
  ⟨by decide, countB1AllFull,
    fun a b h => countB1AllFull_check a (countB1_mem a) b (countB1_mem b) h⟩

/-- Tightness of the compatibility-reflection conjunct in
`no_opPreserving_map_countB_to_frac_reflecting_compat` (canonical form, `N = 1`):
`1 ≤ 1`, and `countEmbed 1` preserves composition. -/
theorem countB1Embed_preservesOp :
    1 ≤ 1 ∧ ∃ f : CountB 1 → FracPerm, PreservesOp (countBAlg 1) fracAlg f :=
  ⟨by decide, countEmbed 1,
    preservesOp_of_op_iff _ _ _ countB1Embed_injective_unit_op_iff.2.2.1⟩

/-- Non-vacuity illustration for `no_opPreserving_map_countB_to_frac_reflecting_compat`
at `N = 1`: under `countEmbed 1`, the two single read tokens are incompatible in
`CountB 1` while their images `1/4, 1/4` are compatible fractions. -/
theorem countB1Embed_compat_not_reflected :
    ¬ (countBAlg 1).Compat CountB.tok1 CountB.tok1 ∧
      fracAlg.Compat (countEmbed 1 CountB.tok1) (countEmbed 1 CountB.tok1) := by
  refine ⟨by decide, ?_⟩
  show (fracOp _ _).isSome = true
  decide +kernel

/-! ## Bounded counting into fractions: which incompatible pair gets compatible images -/

/-- The source `source N` (a source with `N` outstanding tokens) as an element of
`CountB N`. -/
def CountB.srcN (N : Nat) : CountB N := ⟨source N, by simp [inRange, source]⟩

/-- The permission `some (-N)` as an element of `CountB N`. For `N ≥ 1` it is the
bundle of `N` tokens, `tokens N` (`CountB.bundleN_val`); for `N = 0` it is
`total`. -/
def CountB.bundleN (N : Nat) : CountB N := ⟨some (-(N : Int)), by simp [inRange]⟩

/-- The total permission `total` as an element of `CountB N`. -/
def CountB.totalN (N : Nat) : CountB N := ⟨total, by simp [inRange, total]⟩

theorem CountB.srcN_val (N : Nat) : (CountB.srcN N).1 = source N := rfl

theorem CountB.bundleN_val (N : Nat) (hN : 1 ≤ N) : (CountB.bundleN N).1 = tokens N :=
  (tokens_of_pos (by omega)).symm

/-- `source N · tokens N = total` in `CountB N` for `N ≥ 1` (for `N = 0` both
factors are `total`, and `total · total` is undefined). -/
theorem countBAlg_srcN_bundleN (N : Nat) (hN : 1 ≤ N) :
    (countBAlg N).op (CountB.srcN N) (CountB.bundleN N) = some (CountB.totalN N) := by
  show countBOp N _ _ = _
  rw [countBOp_eq_some_iff]
  show countOp (some (N : Int)) (some (-(N : Int))) = some (some 0)
  rw [countOp_some_some_eq_some]
  exact ⟨by omega, show some 0 = some ((N : Int) + -(N : Int)) by congr 1; omega⟩

/-- Two sources `source N` are incompatible in `CountB N` (for every `N`). -/
theorem countBAlg_not_compat_srcN_srcN (N : Nat) :
    ¬ (countBAlg N).Compat (CountB.srcN N) (CountB.srcN N) := by
  intro hc
  simp only [Compat, countBAlg, CountB.srcN, source] at hc
  rw [countBOp_some_some] at hc
  split at hc
  · rename_i hcond; omega
  · simp at hc

/-- Two copies of `some (-N)` are incompatible in `CountB N` (for every `N`; for
`N ≥ 1`, `2N` tokens exceed the bound). -/
theorem countBAlg_not_compat_bundleN_bundleN (N : Nat) :
    ¬ (countBAlg N).Compat (CountB.bundleN N) (CountB.bundleN N) := by
  intro hc
  simp only [Compat, countBAlg, CountB.bundleN] at hc
  rw [countBOp_some_some] at hc
  split at hc
  · rename_i hcond
    have hr : -(N : Int) ≤ -(N : Int) + -(N : Int) ∧ -(N : Int) + -(N : Int) ≤ (N : Int) := by
      simpa [inRange] using hcond.2
    omega
  · simp at hc

/-- **Every composition-preserving map from `N`-bounded counting to fractions
gives compatible images to two sources `source N` or to two bundles `tokens N`.**
For every `N ≥ 1` and every map `f` that sends every defined composite to the
composite of the images, both pairs are incompatible in `N`-bounded counting,
`source N · tokens N = total` forces `f (source N) + f (tokens N) ≤ 1`, and so at
least one of the two pairs has compatible images (`f (source N) ≤ 1/2` or
`f (tokens N) ≤ 1/2`). Which of the two pairs it is depends on `f`
(`opPreserving_maps_countB_to_frac_keep_either_pair_incompatible`). -/
theorem opPreserving_map_countB_to_frac_sources_or_bundles_compat (N : Nat) (hN : 1 ≤ N)
    (f : CountB N → FracPerm) (hf : PreservesOp (countBAlg N) fracAlg f) :
    ¬ (countBAlg N).Compat (CountB.srcN N) (CountB.srcN N) ∧
      ¬ (countBAlg N).Compat (CountB.bundleN N) (CountB.bundleN N) ∧
      (f (CountB.srcN N)).val + (f (CountB.bundleN N)).val ≤ 1 ∧
      (fracAlg.Compat (f (CountB.srcN N)) (f (CountB.srcN N)) ∨
        fracAlg.Compat (f (CountB.bundleN N)) (f (CountB.bundleN N))) := by
  have h := hf _ _ _ (countBAlg_srcN_bundleN N hN)
  change fracOp _ _ = some (f (CountB.totalN N)) at h
  rw [fracOp_eq_some_iff] at h
  have := (f (CountB.totalN N)).le_one
  refine ⟨countBAlg_not_compat_srcN_srcN N, countBAlg_not_compat_bundleN_bundleN N, by grind, ?_⟩
  by_cases hs : (f (CountB.srcN N)).val + (f (CountB.srcN N)).val ≤ 1
  · exact .inl (fracAlg_compat_iff.mpr hs)
  · exact .inr (fracAlg_compat_iff.mpr (by grind))

/-- Linear values with step `e`: the bundle `some (-k)` of `k` tokens has value
`k·e`, the source `some z` with `z` outstanding tokens has value `1 - z·e`, the
empty permission has value `0`. -/
def countLinVal (e : Rat) : Count → Rat
  | none => 0
  | some z => if 0 ≤ z then 1 - (z : Rat) * e else (-(z : Rat)) * e

/-- The linear map from `N`-bounded counting to fractions with step `e`
(`countLinVal e`, clamped into `[0, 1]` by `ofRat`; no clamping occurs on
`CountB N` when `0 ≤ e` and `N·e ≤ 1`). -/
def countLin (N : Nat) (e : Rat) (a : CountB N) : FracPerm := ofRat (countLinVal e a.1)

theorem countLinVal_bounds (N : Nat) (e : Rat) (he : 0 ≤ e) (hNe : (N : Rat) * e ≤ 1)
    (a : CountB N) : 0 ≤ countLinVal e a.1 ∧ countLinVal e a.1 ≤ 1 := by
  rcases a with ⟨_ | z, hz⟩
  · simp [countLinVal]; grind
  · have hrange : -(N : Int) ≤ z ∧ z ≤ (N : Int) := by simpa [inRange] using hz
    simp only [countLinVal]
    split
    · have hz0 : (0 : Rat) ≤ (z : Rat) := by exact_mod_cast (by assumption : (0 : Int) ≤ z)
      have hzN : (z : Rat) ≤ (N : Rat) := by exact_mod_cast hrange.2
      have h1 := Rat.mul_nonneg hz0 he
      have h2 := Rat.mul_nonneg (show (0 : Rat) ≤ (N : Rat) - z by grind) he
      grind
    · have hz0 : (0 : Rat) ≤ -(z : Rat) := by
        have : (0 : Int) ≤ -z := by omega
        exact_mod_cast this
      have hzN : -(z : Rat) ≤ (N : Rat) := by
        have : -z ≤ (N : Int) := by omega
        exact_mod_cast this
      have h1 := Rat.mul_nonneg hz0 he
      have h2 := Rat.mul_nonneg (show (0 : Rat) ≤ (N : Rat) - -(z : Rat) by grind) he
      grind

theorem countLin_val (N : Nat) (e : Rat) (he : 0 ≤ e) (hNe : (N : Rat) * e ≤ 1)
    (a : CountB N) : (countLin N e a).val = countLinVal e a.1 :=
  ofRat_val_of (countLinVal_bounds N e he hNe a).1 (countLinVal_bounds N e he hNe a).2

/-- For `N ≥ 1`, `0 ≤ e` and `N·e ≤ 1`, the linear map with step `e` sends the
unit to `0`, sends every defined composite of `N`-bounded counting to the
composite of the images, sends `total` to `1`, `source N` to `1 - N·e` and the
bundle `tokens N` to `N·e`. -/
theorem countLin_preservesUnit_op_values (N : Nat) (hN : 1 ≤ N) (e : Rat) (he : 0 ≤ e)
    (hNe : (N : Rat) * e ≤ 1) :
    PreservesUnit (countBAlg N) fracAlg (countLin N e) ∧
      PreservesOp (countBAlg N) fracAlg (countLin N e) ∧
      countLin N e (CountB.totalN N) = full ∧
      (countLin N e (CountB.srcN N)).val = 1 - (N : Rat) * e ∧
      (countLin N e (CountB.bundleN N)).val = (N : Rat) * e := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show countLin N e ⟨none, rfl⟩ = zero
    ext; rw [countLin_val N e he hNe]; rfl
  · intro a b c hab
    show fracOp (countLin N e a) (countLin N e b) = some (countLin N e c)
    rw [fracOp_eq_some_iff, countLin_val N e he hNe, countLin_val N e he hNe,
      countLin_val N e he hNe]
    change countBOp N a b = some c at hab
    rw [countBOp_eq_some_iff] at hab
    rcases a with ⟨_ | i, hi⟩
    · simp only [countOp, Option.some.injEq] at hab
      rw [← hab]; simp [countLinVal, Rat.zero_add]
    rcases b with ⟨_ | j, hj⟩
    · simp only [countOp, Option.some.injEq] at hab
      rw [← hab]; simp [countLinVal, Rat.add_zero]
    rcases c with ⟨_ | k, hk⟩
    · rw [countOp_some_some_eq_some] at hab; cases hab.2
    rw [countOp_some_some_eq_some] at hab
    obtain ⟨hcond, hsum⟩ := hab
    simp only [Option.some.injEq] at hsum
    have hk_eq : (k : Rat) = (i : Rat) + (j : Rat) := by
      have : ((i + j : Int) : Rat) = (k : Rat) := by exact_mod_cast hsum.symm
      push_cast at this; exact this.symm
    simp only [countLinVal]
    split <;> split <;> split
    all_goals first | omega | (rw [hk_eq]; grind)
  · ext; rw [countLin_val N e he hNe]; simp only [countLinVal, CountB.totalN, total]
    show (if (0 : Int) ≤ 0 then 1 - ((0 : Int) : Rat) * e else _) = 1
    simp only [Int.le_refl, ↓reduceIte]
    grind
  · rw [countLin_val N e he hNe]
    simp [countLinVal, CountB.srcN, source, Rat.intCast_natCast]
  · rw [countLin_val N e he hNe]
    simp only [countLinVal, CountB.bundleN]
    have : ¬ (0 : Int) ≤ -(N : Int) := by omega
    simp only [this, ↓reduceIte]
    push_cast; grind

/-- **Either incompatible pair can keep incompatible images.** For every `N ≥ 1`
there is a map from `N`-bounded counting to fractions that sends the unit to `0`,
every defined composite to the composite of the images and `total` to `1`, sends
`tokens N` to `2/3` and `source N` to `1/3`, and so gives two sources `source N`
compatible images but two bundles `tokens N` incompatible images; and there is
such a map that sends `tokens N` to `1/3` and `source N` to `2/3`, giving two
bundles `tokens N` compatible images but two sources `source N` incompatible
images. (Witnesses: `countLin N (2/(3N))` and `countLin N (1/(3N))`.) So neither
disjunct of `opPreserving_map_countB_to_frac_sources_or_bundles_compat` holds for
every composition-preserving map. -/
theorem opPreserving_maps_countB_to_frac_keep_either_pair_incompatible (N : Nat) (hN : 1 ≤ N) :
    (∃ f : CountB N → FracPerm, PreservesUnit (countBAlg N) fracAlg f ∧
      PreservesOp (countBAlg N) fracAlg f ∧ f (CountB.totalN N) = full ∧
      (f (CountB.bundleN N)).val = 2 / 3 ∧ (f (CountB.srcN N)).val = 1 / 3 ∧
      fracAlg.Compat (f (CountB.srcN N)) (f (CountB.srcN N)) ∧
      ¬ fracAlg.Compat (f (CountB.bundleN N)) (f (CountB.bundleN N))) ∧
    (∃ f : CountB N → FracPerm, PreservesUnit (countBAlg N) fracAlg f ∧
      PreservesOp (countBAlg N) fracAlg f ∧ f (CountB.totalN N) = full ∧
      (f (CountB.bundleN N)).val = 1 / 3 ∧ (f (CountB.srcN N)).val = 2 / 3 ∧
      ¬ fracAlg.Compat (f (CountB.srcN N)) (f (CountB.srcN N)) ∧
      fracAlg.Compat (f (CountB.bundleN N)) (f (CountB.bundleN N))) := by
  have hN0 : (N : Rat) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hNpos : (0 : Rat) < (N : Rat) := by exact_mod_cast (show 0 < N by omega)
  have step (c : Rat) (hc0 : 0 ≤ c) (hc1 : c ≤ 3) :
      0 ≤ c / (3 * (N : Rat)) ∧ (N : Rat) * (c / (3 * (N : Rat))) = c / 3 := by
    have hval : (N : Rat) * (c / (3 * (N : Rat))) = c / 3 := by grind
    refine ⟨?_, hval⟩
    have h3N : (0 : Rat) < 3 * (N : Rat) := by grind
    rw [Rat.div_def]
    exact Rat.mul_nonneg hc0 (by have := Rat.inv_pos.mpr h3N; grind)
  obtain ⟨he2, hv2⟩ := step 2 (by grind) (by grind)
  obtain ⟨he1, hv1⟩ := step 1 (by grind) (by grind)
  obtain ⟨hu2, hop2, ht2, hs2, hb2⟩ :=
    countLin_preservesUnit_op_values N hN (2 / (3 * (N : Rat))) he2 (by grind)
  obtain ⟨hu1, hop1, ht1, hs1, hb1⟩ :=
    countLin_preservesUnit_op_values N hN (1 / (3 * (N : Rat))) he1 (by grind)
  refine ⟨⟨countLin N (2 / (3 * (N : Rat))), hu2, hop2, ht2, by rw [hb2, hv2], by rw [hs2, hv2]; grind,
      ?_, ?_⟩,
    ⟨countLin N (1 / (3 * (N : Rat))), hu1, hop1, ht1, by rw [hb1, hv1], by rw [hs1, hv1]; grind,
      ?_, ?_⟩⟩
  · rw [fracAlg_compat_iff, hs2, hv2]; grind
  · rw [fracAlg_compat_iff, hb2, hv2]; grind
  · rw [fracAlg_compat_iff, hs1, hv1]; grind
  · rw [fracAlg_compat_iff, hb1, hv1]; grind

/-- Non-vacuity illustration for
`opPreserving_maps_countB_to_frac_keep_either_pair_incompatible` at `N = 1`,
fully computed: with step `2/3` the token maps to `2/3` and the source with one
token to `1/3`; with step `1/3` the token maps to `1/3` and the source to `2/3`;
both maps preserve every defined composite of `CountB 1`. -/
theorem countB1Lin_values :
    (countLin 1 (2 / 3) CountB.tok1).val = 2 / 3 ∧ (countLin 1 (2 / 3) CountB.src1).val = 1 / 3 ∧
      (countLin 1 (1 / 3) CountB.tok1).val = 1 / 3 ∧ (countLin 1 (1 / 3) CountB.src1).val = 2 / 3 ∧
      PreservesOp (countBAlg 1) fracAlg (countLin 1 (2 / 3)) ∧
      PreservesOp (countBAlg 1) fracAlg (countLin 1 (1 / 3)) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    (countLin_preservesUnit_op_values 1 (by decide) (2 / 3) (by decide +kernel)
      (by decide +kernel)).2.1,
    (countLin_preservesUnit_op_values 1 (by decide) (1 / 3) (by decide +kernel)
      (by decide +kernel)).2.1⟩

/-- Tightness of `hN` in `opPreserving_map_countB_to_frac_sources_or_bundles_compat`
(canonical form, `N = 0`): `countEmbed 0` preserves composition, and the
conclusion fails, because `source 0 = some (-0) = total` maps to `1`. -/
theorem countB0Embed_sources_or_bundles_compat_fails :
    ¬ (1 ≤ 0) ∧ PreservesOp (countBAlg 0) fracAlg (countEmbed 0) ∧
      ¬ (¬ (countBAlg 0).Compat (CountB.srcN 0) (CountB.srcN 0) ∧
        ¬ (countBAlg 0).Compat (CountB.bundleN 0) (CountB.bundleN 0) ∧
        (countEmbed 0 (CountB.srcN 0)).val + (countEmbed 0 (CountB.bundleN 0)).val ≤ 1 ∧
        (fracAlg.Compat (countEmbed 0 (CountB.srcN 0)) (countEmbed 0 (CountB.srcN 0)) ∨
          fracAlg.Compat (countEmbed 0 (CountB.bundleN 0)) (countEmbed 0 (CountB.bundleN 0)))) := by
  refine ⟨by decide, countB0Embed_preservesOp_reflects_compat.2.1, ?_⟩
  rintro ⟨-, -, -, h | h⟩
  · exact countBAlg_not_compat_srcN_srcN 0 (countB0Embed_preservesOp_reflects_compat.2.2 _ _ h)
  · exact countBAlg_not_compat_bundleN_bundleN 0
      (countB0Embed_preservesOp_reflects_compat.2.2 _ _ h)

/-- Tightness of `hf` in `opPreserving_map_countB_to_frac_sources_or_bundles_compat`
(canonical form, `N = 1`): `1 ≤ 1`, and for the map sending every non-empty
permission to `1` (which does not preserve composition) the conclusion fails. -/
theorem countB1AllFull_sources_or_bundles_compat_fails :
    1 ≤ 1 ∧
      ¬ (¬ (countBAlg 1).Compat (CountB.srcN 1) (CountB.srcN 1) ∧
        ¬ (countBAlg 1).Compat (CountB.bundleN 1) (CountB.bundleN 1) ∧
        (countB1AllFull (CountB.srcN 1)).val + (countB1AllFull (CountB.bundleN 1)).val ≤ 1 ∧
        (fracAlg.Compat (countB1AllFull (CountB.srcN 1)) (countB1AllFull (CountB.srcN 1)) ∨
          fracAlg.Compat (countB1AllFull (CountB.bundleN 1))
            (countB1AllFull (CountB.bundleN 1)))) := by
  refine ⟨by decide, ?_⟩
  rintro ⟨-, -, -, h | h⟩
  · exact countBAlg_not_compat_srcN_srcN 1
      (countB1AllFull_check _ (countB1_mem _) _ (countB1_mem _) h)
  · exact countBAlg_not_compat_bundleN_bundleN 1
      (countB1AllFull_check _ (countB1_mem _) _ (countB1_mem _) h)

/-- Tightness of `hN` in
`opPreserving_maps_countB_to_frac_keep_either_pair_incompatible` (canonical form,
`N = 0`): the conclusion fails, because in `CountB 0` the source `source 0` and
`some (-0)` are the same element `total`. -/
theorem countB0_keep_either_pair_incompatible_fails :
    ¬ (1 ≤ 0) ∧
      ¬ ((∃ f : CountB 0 → FracPerm, PreservesUnit (countBAlg 0) fracAlg f ∧
          PreservesOp (countBAlg 0) fracAlg f ∧ f (CountB.totalN 0) = full ∧
          (f (CountB.bundleN 0)).val = 2 / 3 ∧ (f (CountB.srcN 0)).val = 1 / 3 ∧
          fracAlg.Compat (f (CountB.srcN 0)) (f (CountB.srcN 0)) ∧
          ¬ fracAlg.Compat (f (CountB.bundleN 0)) (f (CountB.bundleN 0))) ∧
        (∃ f : CountB 0 → FracPerm, PreservesUnit (countBAlg 0) fracAlg f ∧
          PreservesOp (countBAlg 0) fracAlg f ∧ f (CountB.totalN 0) = full ∧
          (f (CountB.bundleN 0)).val = 1 / 3 ∧ (f (CountB.srcN 0)).val = 2 / 3 ∧
          ¬ fracAlg.Compat (f (CountB.srcN 0)) (f (CountB.srcN 0)) ∧
          fracAlg.Compat (f (CountB.bundleN 0)) (f (CountB.bundleN 0)))) := by
  refine ⟨by decide, ?_⟩
  rintro ⟨⟨f, -, -, -, -, -, h1, h2⟩, -⟩
  have hsame : CountB.srcN 0 = CountB.bundleN 0 := rfl
  rw [hsame] at h1
  exact h2 h1

/-! ## Counting into fractions: impossibility for unbounded counts -/

theorem rat_exists_nat_mul_gt_one {q : Rat} (hq : 0 < q) : ∃ n : Nat, 1 < (n : Rat) * q := by
  let m : Int := (q⁻¹).floor + 1
  have h1 : q⁻¹ < (m : Rat) := Rat.lt_floor_add_one _
  refine ⟨m.toNat, ?_⟩
  have h2 : (m : Rat) ≤ ((m.toNat : Int) : Rat) := by
    have := Int.self_le_toNat m
    exact_mod_cast this
  rw [Rat.intCast_natCast] at h2
  have h3 : q⁻¹ * q < (m.toNat : Rat) * q := Rat.mul_lt_mul_of_pos_right (by grind) hq
  rw [Rat.inv_mul_cancel q (by grind)] at h3
  exact h3

/-- **No composition-preserving map from (unbounded) counting to fractions gives
a read token a non-zero fraction.** There is no map `f` from counting
permissions to fractional permissions that sends every defined composite to the
composite of the images and sends the single read token to a non-zero fraction.
(Bundles of `n` tokens exist for every `n`, so `n · f(readToken) ≤ 1` for all
`n`.) -/
theorem no_opPreserving_map_count_to_frac_with_nonzero_readToken :
    ¬ ∃ f : Count → FracPerm, PreservesOp countAlg fracAlg f ∧ f readToken ≠ zero := by
  rintro ⟨f, hf, hne⟩
  have hq : 0 < (f readToken).val := by
    have h0 := (f readToken).nonneg
    have : (f readToken).val ≠ 0 := fun h => hne (FracPerm.ext h)
    grind
  have key : ∀ n : Nat, (f (tokens (n + 1))).val = ((n : Rat) + 1) * (f readToken).val := by
    intro n
    induction n with
    | zero =>
      have : tokens (0 + 1) = readToken := rfl
      rw [this]; grind
    | succ n ih =>
      have hop : countAlg.op readToken (tokens (n + 1)) = some (tokens (n + 1 + 1)) := by
        show countOp (some (-1)) (some (-((n + 1 : Nat) : Int))) = some (some (-((n + 1 + 1 : Nat) : Int)))
        rw [countOp_some_some_of (by omega)]
        congr 2; omega
      have h := hf _ _ _ hop
      change fracOp _ _ = _ at h
      rw [fracOp_eq_some_iff, ih] at h
      rw [← h, Rat.natCast_add]; simp; grind
  obtain ⟨n, hn⟩ := rat_exists_nat_mul_gt_one hq
  cases n with
  | zero => simp at hn; grind
  | succ n =>
    have h1 := (f (tokens (n + 1))).le_one
    rw [key n] at h1
    rw [Rat.natCast_add] at hn
    simp at hn
    grind

/-- Positive control for `no_opPreserving_map_count_to_frac_with_nonzero_readToken`:
with counts bounded by `1`, the map `countEmbed 1` preserves every defined
composite and gives the read token the non-zero fraction `1/4`. -/
theorem countB1Embed_preservesOp_nonzero_token :
    PreservesOp (countBAlg 1) fracAlg (countEmbed 1) ∧ countEmbed 1 CountB.tok1 ≠ zero :=
  ⟨preservesOp_of_op_iff _ _ _ countB1Embed_injective_unit_op_iff.2.2.1,
    countB1Embed_injective_unit_op_iff.2.2.2.1⟩

/-- Tightness of the composition-preservation hypothesis: the constant map to
`1` gives the read token a non-zero fraction (and does not preserve
composition). -/
theorem const_full_nonzero_token : ∃ f : Count → FracPerm, f readToken ≠ zero :=
  ⟨fun _ => full, by decide +kernel⟩

/-- Tightness of the non-zero-token hypothesis: the constant map to `0`
preserves every defined composite. -/
theorem const_zero_preservesOp : ∃ f : Count → FracPerm, PreservesOp countAlg fracAlg f := by
  refine ⟨fun _ => zero, fun _ _ _ _ => ?_⟩
  show fracOp zero zero = some zero
  rw [fracOp_eq_some_iff]; simp only [zero_val]; grind

/-- The map from counting to fractions that sends every source (including the
total permission) to `1` and the empty permission and every token bundle to
`0`. -/
def countToFracSourcesOnly : Count → FracPerm
  | none => zero
  | some z => if 0 ≤ z then full else zero

/-- **Exclusivity alone can be preserved.** `countToFracSourcesOnly` preserves
the unit and every defined composite and sends the total permission to the
exclusive fraction `1`; it sends the read token to `0`. So in
`no_opPreserving_map_count_to_frac_with_nonzero_readToken` the hypothesis
`f readToken ≠ 0` cannot be replaced by `f total = 1`. -/
theorem countToFracSourcesOnly_preserves_unit_op_total :
    PreservesUnit countAlg fracAlg countToFracSourcesOnly ∧
      PreservesOp countAlg fracAlg countToFracSourcesOnly ∧
      countToFracSourcesOnly total = full ∧ countToFracSourcesOnly readToken = zero := by
  refine ⟨rfl, ?_, by decide +kernel, by decide +kernel⟩
  intro a b c h
  rcases a with _ | i
  · cases h; show fracOp zero _ = _; rw [fracOp_eq_some_iff]; simp; grind
  rcases b with _ | j
  · cases h; show fracOp _ zero = _; rw [fracOp_eq_some_iff]; simp; grind
  change countOp (some i) (some j) = some c at h
  rw [countOp_some_some_eq_some] at h
  obtain ⟨⟨h1, h2⟩, rfl⟩ := h
  show fracOp _ _ = some _
  rw [fracOp_eq_some_iff]
  simp only [countToFracSourcesOnly]
  split <;> split <;> split <;> simp <;> first | omega | grind

/-! ## Fractions into counting -/

theorem countOp_self_ne_total (x : Count) : countOp x x ≠ some total := by
  rcases x with _ | i
  · simp [countOp, total]
  · intro h
    rw [countOp_some_some_eq_some] at h
    obtain ⟨⟨h1, _⟩, h3⟩ := h
    simp [total] at h3; omega

/-- `halfIter k q = q / 2^k`. -/
def halfIter : Nat → FracPerm → FracPerm
  | 0, x => x
  | k + 1, x => half (halfIter k x)

/-- **Every composition-preserving map from fractions to counting is constantly
empty.** If `g` sends every defined fractional composite to the counting
composite of the images, then `g q = none` for every fractional permission `q`.
(If `g q = some z`, the halving chain `q = q/2 · q/2 = …` forces
`g (q/2^k) = some w_k` with `w_k < 0` and `z = 2^k · w_k` for every `k ≥ 1`,
which is impossible for `k` larger than `|z|`.) -/
theorem opPreserving_map_frac_to_count_eq_none (g : FracPerm → Count)
    (hg : PreservesOp fracAlg countAlg g) : ∀ q, g q = none := by
  intro q
  cases h0 : g q with
  | none => rfl
  | some z0 =>
    exfalso
    have hstep : ∀ k, fracAlg.op (halfIter (k + 1) q) (halfIter (k + 1) q) = some (halfIter k q) :=
      fun k => fracAlg_op_half_half (halfIter k q)
    have claim : ∀ k : Nat, ∃ w : Int, g (halfIter (k + 1) q) = some w ∧ w < 0 ∧ z0 = w * 2 ^ (k + 1) := by
      intro k
      induction k with
      | zero =>
        have h := hg _ _ _ (hstep 0)
        change countOp _ _ = some (g (halfIter 0 q)) at h
        rw [show halfIter 0 q = q from rfl, h0] at h
        cases hx : g (halfIter 1 q) with
        | none => rw [hx] at h; simp [countOp] at h
        | some w =>
          rw [hx] at h
          rw [countOp_some_some_eq_some] at h
          obtain ⟨⟨h1, _⟩, h3⟩ := h
          simp at h3
          exact ⟨w, rfl, by omega, by omega⟩
      | succ k ih =>
        obtain ⟨w, hw, _, hz⟩ := ih
        have h := hg _ _ _ (hstep (k + 1))
        change countOp _ _ = some (g (halfIter (k + 1) q)) at h
        rw [hw] at h
        cases hx : g (halfIter (k + 2) q) with
        | none => rw [hx] at h; simp [countOp] at h
        | some w' =>
          rw [hx] at h
          rw [countOp_some_some_eq_some] at h
          obtain ⟨⟨h1, _⟩, h3⟩ := h
          simp at h3
          refine ⟨w', rfl, by omega, ?_⟩
          rw [hz, h3, Int.pow_succ]; grind
    obtain ⟨w, _, hw0, hz⟩ := claim z0.natAbs
    have hP : (z0.natAbs : Int) < 2 ^ (z0.natAbs + 1) := by
      have := @Nat.lt_two_pow_self (z0.natAbs + 1)
      have h' : ((2 ^ (z0.natAbs + 1) : Nat) : Int) = (2 : Int) ^ (z0.natAbs + 1) := by
        push_cast; rfl
      omega
    generalize hPdef : (2 : Int) ^ (z0.natAbs + 1) = P at hz hP
    have hle : w * P ≤ -1 * P := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    have h1 : z0 ≤ -1 * P := hz ▸ hle
    omega

/-- Corollary of `opPreserving_map_frac_to_count_eq_none`: no
composition-preserving map from fractions to counting sends even a single
fraction (for instance `1`, or `1/2`) to a non-empty counting permission. -/
theorem no_opPreserving_map_frac_to_count_with_nonempty_value :
    ¬ ∃ g : FracPerm → Count, PreservesOp fracAlg countAlg g ∧ ∃ q, g q ≠ none := by
  rintro ⟨g, hg, q, hq⟩
  exact hq (opPreserving_map_frac_to_count_eq_none g hg q)

/-- Non-vacuity of `opPreserving_map_frac_to_count_eq_none`: the constant map to
`none` preserves every defined composite. -/
theorem const_none_preservesOp_frac : PreservesOp fracAlg countAlg (fun _ => none) :=
  fun _ _ _ _ => rfl

/-- Tightness of `hg` in `opPreserving_map_frac_to_count_eq_none` (canonical
form; the theorem has no other hypothesis): the constant map to a read token
is not constantly empty (and does not preserve composition). -/
theorem const_readToken_not_none :
    ¬ ∀ q : FracPerm, (fun _ => readToken : FracPerm → Count) q = none := by
  intro h; have := h zero; simp [readToken] at this

/-- **In any partial algebra, a self-composite cannot be sent to the total
counting permission.** If `h · h = a` in a partial algebra `A`, no map `g` into
the counting algebra that sends every defined composite to the composite of
the images sends `a` to the total permission: the total counting permission is
not of the form `x · x`. -/
theorem no_opPreserving_map_to_count_sending_self_composite_to_total {α : Type}
    (A : PartialAlg α) (h a : α) (hh : A.op h h = some a) :
    ¬ ∃ g : α → Count, PreservesOp A countAlg g ∧ g a = total := by
  rintro ⟨g, hg, hga⟩
  have hc := hg _ _ _ hh
  rw [hga] at hc
  exact countOp_self_ne_total _ hc

/-- Instance for fractions (`1 = 1/2 · 1/2`): no composition-preserving map from
fractions to counting sends `1` to the total permission. On the full fractional
algebra this is also implied by `opPreserving_map_frac_to_count_eq_none`. -/
theorem no_opPreserving_map_frac_to_count_sending_full_to_total :
    ¬ ∃ g : FracPerm → Count, PreservesOp fracAlg countAlg g ∧ g full = total :=
  no_opPreserving_map_to_count_sending_self_composite_to_total fracAlg (half full) full
    (fracAlg_op_half_half full)

/-- The map from the two-point exclusive algebra to fractions (`false ↦ 0`,
`true ↦ 1`). -/
def exclToFrac (b : Bool) : FracPerm := if b then full else zero

/-- The map from the two-point exclusive algebra to counting (`false ↦ none`,
`true ↦ total`). -/
def exclToCount (b : Bool) : Count := if b then total else none

/-- The two-point exclusive algebra is exactly the sub-algebra `{0, 1}` of the
fractional algebra: `exclToFrac` is injective and preserves and reflects
composition. -/
theorem exclToFrac_preserves_reflects :
    Function.Injective exclToFrac ∧
      ∀ a b c, exclAlg.op a b = some c ↔ fracOp (exclToFrac a) (exclToFrac b) = some (exclToFrac c) := by
  refine ⟨?_, ?_⟩
  · intro a b h; cases a <;> cases b <;> first | rfl | (revert h; decide +kernel)
  · decide +kernel

/-- Positive control for
`no_opPreserving_map_to_count_sending_self_composite_to_total` and tightness of
`hh` (canonical form, `A = exclAlg`, `h = a = true`): in the two-point
exclusive algebra (the non-splittable sub-algebra `{0, 1}` of fractions) `true`
is not a self-composite, and the map `false ↦ none`, `true ↦ total` preserves
every defined composite and sends `true` to the total permission. -/
theorem exclToCount_preservesOp_full_to_total :
    exclAlg.op true true ≠ some true ∧
      PreservesOp exclAlg countAlg exclToCount ∧ exclToCount true = total := by
  refine ⟨by decide, ?_, rfl⟩
  intro a b c h
  cases a <;> cases b <;> cases c <;> first | rfl | (simp [exclAlg] at h)

/-- Tightness of the composition-preservation conjunct in
`no_opPreserving_map_to_count_sending_self_composite_to_total` (canonical form,
`A = fracAlg`, `h = 1/2`, `a = 1`): `1/2 · 1/2 = 1`, and the map sending `1` to
`total` and everything else to `none` sends `1` to the total permission (it
does not preserve composition). -/
theorem indicator_full_to_total :
    fracAlg.op (half full) (half full) = some full ∧ ∃ g : FracPerm → Count, g full = total :=
  ⟨fracAlg_op_half_half full, fun q => if q = full then total else none, by simp⟩

/-- Tightness of the conjunct `g a = total` in
`no_opPreserving_map_to_count_sending_self_composite_to_total` (canonical form,
`A = fracAlg`, `h = 1/2`, `a = 1`): `1/2 · 1/2 = 1`, and the constant map to
`none` preserves every defined composite. -/
theorem const_none_preservesOp_frac_half :
    fracAlg.op (half full) (half full) = some full ∧
      ∃ g : FracPerm → Count, PreservesOp fracAlg countAlg g :=
  ⟨fracAlg_op_half_half full, fun _ => none, const_none_preservesOp_frac⟩

theorem halfPow_ne_zero (k : Nat) : halfPow k ≠ zero := by
  have : 0 < (halfPow k).val := by
    induction k with
    | zero => simp [halfPow] <;> grind
    | succ k ih => simp [halfPow] <;> grind
  intro h; rw [h] at this; simp at this

/-- The half-grid algebra `{0, 1/2, 1}`, represented by `Fin 3` (`i` stands for
`i/2`): `i · j = i + j` when `i + j ≤ 2`. -/
def halfGridAlg : PartialAlg (Fin 3) where
  op i j := if h : i.val + j.val ≤ 2 then some ⟨i.val + j.val, by omega⟩ else none
  unit := 0

/-- The half-grid as fractions: `i ↦ i/2`. -/
def halfGridToFrac (i : Fin 3) : FracPerm := ofRat ((i.val : Rat) / 2)

/-- The half-grid as token bundles: `0 ↦ none`, `i ↦ i` tokens. -/
def halfGridToCount (i : Fin 3) : Count := tokens i.val

/-- The half-grid algebra is exactly the sub-algebra `{0, 1/2, 1}` of the
fractional algebra: `halfGridToFrac` is injective and preserves and reflects
composition. -/
theorem halfGridToFrac_preserves_reflects :
    Function.Injective halfGridToFrac ∧
      ∀ i j k, halfGridAlg.op i j = some k ↔
        fracOp (halfGridToFrac i) (halfGridToFrac j) = some (halfGridToFrac k) := by
  refine ⟨?_, by decide +kernel⟩
  intro a b h
  have hall : ∀ a b : Fin 3, halfGridToFrac a = halfGridToFrac b → a = b := by decide +kernel
  exact hall a b h

/-- In the half-grid, `1/2 · 1/2 = 1` (the hypothesis of
`no_opPreserving_map_to_count_sending_self_composite_to_total` holds for
`h = 1/2`, `a = 1`). -/
theorem halfGridAlg_half_half : halfGridAlg.op 1 1 = some 2 := by decide

/-- Instance for the half-grid (`1 = 1/2 · 1/2` in `{0, 1/2, 1}`): no
composition-preserving map from the half-grid to counting sends `1` to the
total permission, although (by `halfGridToCount_preservesOp_nonempty`) a
composition-preserving map that keeps every non-zero element non-empty does
exist. -/
theorem no_opPreserving_map_halfGrid_to_count_sending_full_to_total :
    ¬ ∃ g : Fin 3 → Count, PreservesOp halfGridAlg countAlg g ∧ g 2 = total :=
  no_opPreserving_map_to_count_sending_self_composite_to_total halfGridAlg 1 2 (by decide)

/-- Positive control for `opPreserving_map_frac_to_count_eq_none`: on the
finitely divisible sub-algebra `{0, 1/2, 1}` of fractions, the map `i/2 ↦ i`
tokens preserves every defined composite and sends every non-zero element to a
non-empty counting permission. (It sends `1` to a bundle of two tokens, not to
the total permission.) -/
theorem halfGridToCount_preservesOp_nonempty :
    PreservesOp halfGridAlg countAlg halfGridToCount ∧ ∀ i, i ≠ 0 → halfGridToCount i ≠ none := by
  refine ⟨?_, by decide⟩
  have : ∀ i j k : Fin 3, halfGridAlg.op i j = some k →
      countAlg.op (halfGridToCount i) (halfGridToCount j) = some (halfGridToCount k) := by decide
  exact this

/-- Numerators (in quarters) of the asymmetric grid `{0, 1/4, 3/4, 1}`. -/
def asymGridQuarters : Fin 4 → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 4

/-- The asymmetric grid algebra `{0, 1/4, 3/4, 1}` (index `i` stands for
`asymGridQuarters i / 4`): `0` is the unit, `1/4 · 3/4 = 1`, and every other
composite of non-zero elements is undefined (`1/4 + 1/4 = 1/2` is not in the
grid; the other sums exceed `1`). -/
def asymGridAlg : PartialAlg (Fin 4) where
  op
    | 0, j => some j
    | i, 0 => some i
    | 1, 2 => some 3
    | 2, 1 => some 3
    | _, _ => none
  unit := 0

/-- The asymmetric grid as fractions. -/
def asymGridToFrac (i : Fin 4) : FracPerm := ofRat ((asymGridQuarters i : Rat) / 4)

/-- The asymmetric grid as counting permissions: `0 ↦ none`, `1/4 ↦ readToken`,
`3/4 ↦ source 1`, `1 ↦ total`. -/
def asymGridToCount : Fin 4 → Count
  | 0 => none
  | 1 => readToken
  | 2 => source 1
  | 3 => total

/-- The asymmetric grid algebra is exactly the sub-algebra `{0, 1/4, 3/4, 1}` of
the fractional algebra: `asymGridToFrac` is injective and preserves and reflects
composition. -/
theorem asymGridToFrac_preserves_reflects :
    Function.Injective asymGridToFrac ∧
      ∀ i j k, asymGridAlg.op i j = some k ↔
        fracOp (asymGridToFrac i) (asymGridToFrac j) = some (asymGridToFrac k) := by
  refine ⟨?_, by decide +kernel⟩
  intro a b h
  have hall : ∀ a b : Fin 4, asymGridToFrac a = asymGridToFrac b → a = b := by decide +kernel
  exact hall a b h

/-- **Positive control** for
`no_opPreserving_map_to_count_sending_self_composite_to_total`: the obstruction
is the symmetric split, not splitting as such. In the asymmetric grid
`{0, 1/4, 3/4, 1}` the full permission splits (`1/4 · 3/4 = 1`) but is not a
self-composite, and the map `1/4 ↦ readToken`, `3/4 ↦ source 1`, `1 ↦ total`
preserves every defined composite and sends `1` to the total permission. -/
theorem asymGridToCount_preservesOp_full_to_total :
    asymGridAlg.op 1 2 = some 3 ∧ (∀ x, asymGridAlg.op x x ≠ some 3) ∧
      PreservesOp asymGridAlg countAlg asymGridToCount ∧ asymGridToCount 3 = total := by
  refine ⟨rfl, by decide, ?_, rfl⟩
  have : ∀ i j k : Fin 4, asymGridAlg.op i j = some k →
      countAlg.op (asymGridToCount i) (asymGridToCount j) = some (asymGridToCount k) := by decide
  exact this

/-- Tightness of the composition-preservation hypothesis in
`opPreserving_map_frac_to_count_eq_none`, phrased as in the impossibility
corollary: the constant map to a read token sends every fraction to a non-empty
permission. -/
theorem const_readToken_nonempty : ∃ g : FracPerm → Count, ∃ q, g q ≠ none :=
  ⟨fun _ => readToken, zero, by simp [readToken]⟩

/-- Tightness of the inner conjunct `∃ q, g q ≠ none` in
`no_opPreserving_map_frac_to_count_with_nonempty_value` (canonical form for a
negated existential): without it, a composition-preserving map exists (the
constant map to `none`). -/
theorem opPreserving_map_frac_to_count_exists : ∃ g : FracPerm → Count, PreservesOp fracAlg countAlg g :=
  ⟨fun _ => none, const_none_preservesOp_frac⟩

end Toy.Perm
