/-
Toy.Float.Counterexamples
=========================

Concrete witnesses, all fully proved by kernel evaluation: counterexamples
(in canonical form: the other hypotheses hold and the conclusion fails),
non-vacuity witnesses (all hypotheses hold), and positive controls (a nearby
setting where an impossibility's conclusion fails).

Values are written `dy F m k = m * 2^k`; in `F33`, `dy F33 5 (-4) = 0.3125`.
-/
import Toy.Float.Rewrites

namespace Toy.Float

/-! ### Commutativity and identities -/

/-- Non-vacuity for `add_comm_mul_comm_fma_comm` (no hypotheses): instances
with distinct finite operands where rounding occurs (`2 + 1/4` is a tie that
rounds to `2`; `1.25 * 1.5 = 1.875` rounds to `2`). -/
theorem nv_comm_F33 :
    dy F33 2 0 ≠ dy F33 1 (-2) ∧ dy F33 5 (-2) ≠ dy F33 3 (-1) ∧
    add (dy F33 2 0) (dy F33 1 (-2)) = dy F33 2 0 ∧ mul (dy F33 5 (-2)) (dy F33 3 (-1)) = dy F33 2 0 ∧
    add (dy F33 2 0) (dy F33 1 (-2)) = add (dy F33 1 (-2)) (dy F33 2 0) ∧
    mul (dy F33 5 (-2)) (dy F33 3 (-1)) = mul (dy F33 3 (-1)) (dy F33 5 (-2)) ∧
    fma (dy F33 5 (-4)) (dy F33 7 (-3)) (dy F33 2 0) = fma (dy F33 7 (-3)) (dy F33 5 (-4)) (dy F33 2 0) := by
  decide +kernel

/-- Non-vacuity for `add_negZero_right_and_mul_one_right`: instances at a
negative zero, a subnormal, an infinity and NaN. -/
theorem nv_identities_F33 :
    add (negZero F33) (negZero F33) = negZero F33 ∧ add (dy F33 1 (-4)) (negZero F33) = dy F33 1 (-4) ∧
    mul (.inf true) (one F33) = .inf true ∧ mul .nan (one F33) = .nan := by
  decide +kernel

/-- The failing instance of `x + (+0) → x` (`(-0) + (+0) = +0`), and an
instance where it holds (`(+0) + (+0) = +0`). -/
theorem add_posZero_fails_at_negZero_F33 :
    add (negZero F33) (posZero F33) = posZero F33 ∧ add (negZero F33) (posZero F33) ≠ negZero F33 ∧
    add (posZero F33) (posZero F33) = posZero F33 := by
  decide +kernel

/-- The failing instances of `x - x → +0` (`NaN - NaN` and `∞ - ∞` are NaN)
and a holding instance (`(-0) - (-0) = +0`). The infinite input is not NaN;
only the result is. -/
theorem sub_self_fails_at_nan_inf_F33 :
    sub (.nan : FP F33) .nan = .nan ∧ sub (.inf false : FP F33) (.inf false) = .nan ∧
    sub (.inf true : FP F33) (.inf true) = .nan ∧ (FP.inf false : FP F33).isNaN = false ∧
    sub (negZero F33) (negZero F33) = posZero F33 := by
  decide +kernel

/-- The failing instance of `x == x → true` (NaN), and a holding instance. -/
theorem feq_self_fails_at_nan_F33 : feq (.nan : FP F33) .nan = false ∧ feq (negZero F33) (negZero F33) = true := by
  decide +kernel

/-- The failing instances of `x * (+0) → +0`: NaN, `±∞` (giving NaN), `-1`
and `-0` (giving `-0`); and a holding instance (`3 * (+0) = +0`). -/
theorem mul_posZero_fails_F33 :
    mul (.nan : FP F33) (posZero F33) = .nan ∧ mul (.inf false : FP F33) (posZero F33) = .nan ∧
    mul (.inf true : FP F33) (posZero F33) = .nan ∧
    mul (one F33).neg (posZero F33) = negZero F33 ∧ mul (negZero F33) (posZero F33) = negZero F33 ∧
    mul (dy F33 3 0) (posZero F33) = posZero F33 := by
  decide +kernel

/-! ### Associativity -/

/-- Tightness of `p + 1 ≤ 2 * bias` in `add_assoc_fails_by_rounding_all_normal`
for its witnesses: in the format `F22` (`p + 1 = 3 > 2 = 2 * bias`) the
conclusion fails (`assocRoundA F22` overflows to `+∞`). -/
theorem add_assoc_fails_by_rounding_all_normal_hyp_tight_F22 :
    ¬ (F22.p + 1 ≤ 2 * F22.bias) ∧
    ¬ ([assocRoundA F22, assocRoundB F22, add (assocRoundA F22) (assocRoundB F22),
        add (assocRoundB F22) (assocRoundB F22),
        add (add (assocRoundA F22) (assocRoundB F22)) (assocRoundB F22),
        add (assocRoundA F22) (add (assocRoundB F22) (assocRoundB F22))].all FP.isNormal = true ∧
      add (add (assocRoundA F22) (assocRoundB F22)) (assocRoundB F22) = assocRoundA F22 ∧
      add (assocRoundA F22) (add (assocRoundB F22) (assocRoundB F22)) ≠ assocRoundA F22) := by
  decide +kernel

/-- The hypothesis `p + 1 ≤ 2 * bias` is about the specific witnesses, not
about the phenomenon: in `F23` it fails, yet `1`, `1.25`, `1.25` give an
all-normal rounding counterexample (`3` versus `3.5`). -/
theorem add_assoc_rounding_all_normal_F23 :
    ¬ (F23.p + 1 ≤ 2 * F23.bias) ∧
    [dy F23 1 0, dy F23 5 (-2), add (dy F23 1 0) (dy F23 5 (-2)), add (dy F23 5 (-2)) (dy F23 5 (-2)),
      add (add (dy F23 1 0) (dy F23 5 (-2))) (dy F23 5 (-2)),
      add (dy F23 1 0) (add (dy F23 5 (-2)) (dy F23 5 (-2)))].all FP.isNormal = true ∧
    add (add (dy F23 1 0) (dy F23 5 (-2))) (dy F23 5 (-2)) = dy F23 3 0 ∧
    add (dy F23 1 0) (add (dy F23 5 (-2)) (dy F23 5 (-2))) = dy F23 7 (-1) := by
  decide +kernel

/-- The rounding counterexample `(2, 1/4, 1/4)` in `F33`: `(2 + 1/4) + 1/4 = 2`
and `2 + (1/4 + 1/4) = 2.5`. -/
def envAssocRound : Fin 3 → FP F33 := env3 (dy F33 2 0) (dy F33 1 (-2)) (dy F33 1 (-2))

/-- The overflow counterexample `(14, 14, -14)` in `F33`. -/
def envAssocOverflow : Fin 3 → FP F33 :=
  env3 (maxFinite F33 false) (maxFinite F33 false) (maxFinite F33 true)

/-- Rounding counterexamples survive `nnan`, `ninf`, `nsz` (and `contract`):
at `envAssocRound = (2, 1/4, 1/4)` the source `(x + y) + z` is admissible
under all flags except `reassoc`, evaluates to `2`, the target
`x + (y + z)` evaluates to `2.5`, and the target is not related by `Rel` to
any form of the source generated by `Expr.variants`; hence
`(x + y) + z → x + (y + z)` is not valid modulo all flags except `reassoc`. -/
theorem add_assoc_not_validMod_allBut_reassoc_F33 :
    Admissible (Flags.allBut .reassoc) (rwAddAssoc F33).lhs envAssocRound ∧
    (rwAddAssoc F33).lhs.eval envAssocRound = dy F33 2 0 ∧
    (rwAddAssoc F33).rhs.eval envAssocRound = dy F33 5 (-1) ∧
    (∀ v ∈ (rwAddAssoc F33).lhs.variants (Flags.allBut .reassoc),
      ¬ Rel (Flags.allBut .reassoc) ((rwAddAssoc F33).rhs.eval envAssocRound)
        (v.eval envAssocRound)) ∧
    ¬ ValidMod (Flags.allBut .reassoc) (rwAddAssoc F33) := by
  have hadm : Admissible (Flags.allBut .reassoc) (rwAddAssoc F33).lhs envAssocRound := by
    decide +kernel
  have hrel : ∀ v ∈ (rwAddAssoc F33).lhs.variants (Flags.allBut .reassoc),
      ¬ Rel (Flags.allBut .reassoc) ((rwAddAssoc F33).rhs.eval envAssocRound)
        (v.eval envAssocRound) := by
    decide +kernel
  refine ⟨hadm, by decide +kernel, by decide +kernel, hrel, fun h => ?_⟩
  obtain ⟨v, hv, hr⟩ := h envAssocRound hadm
  exact hrel v hv hr

/-- The overflow counterexample does not survive `ninf` (an intermediate
result is `+∞`), although it is a counterexample without flags. -/
theorem add_assoc_overflow_excluded_by_ninf_F33 :
    (rwAddAssoc F33).rhs.eval envAssocOverflow ≠ (rwAddAssoc F33).lhs.eval envAssocOverflow ∧
    ¬ Admissible { ninf := true } (rwAddAssoc F33).lhs envAssocOverflow := by
  decide +kernel

/-- Non-vacuity for `add_assoc_defect_never_only_zero_sign`: at
`(-0, +0, -0)` the hypothesis holds (both bracketings are `+0`). -/
theorem nv_assoc_zero_sign_F33 :
    EqNsz (add (add (negZero F33) (posZero F33)) (negZero F33))
      (add (negZero F33) (add (posZero F33) (negZero F33))) := by
  decide +kernel

/-- Positive control for `add_assoc_defect_never_only_zero_sign`: the nearby
re-bracketing of a subtraction, `(a - b) - c` versus `a - (b + c)`, does
differ only in the sign of zero, at `(-0, +0, -0)`. -/
theorem sub_rebracket_differs_only_in_zero_sign_F33 :
    sub (sub (negZero F33) (posZero F33)) (negZero F33) = posZero F33 ∧
    sub (negZero F33) (add (posZero F33) (negZero F33)) = negZero F33 := by
  decide +kernel

/-- Tightness of the hypothesis of `add_assoc_defect_never_only_zero_sign`:
without it the conclusion (associativity) fails at `envAssocRound`. -/
theorem add_assoc_fails_F33 :
    add (add (dy F33 2 0) (dy F33 1 (-2))) (dy F33 1 (-2)) ≠
      add (dy F33 2 0) (add (dy F33 1 (-2)) (dy F33 1 (-2))) ∧
    ¬ EqNsz (add (add (dy F33 2 0) (dy F33 1 (-2))) (dy F33 1 (-2)))
      (add (dy F33 2 0) (add (dy F33 1 (-2)) (dy F33 1 (-2)))) ∧
    add (add (dy F33 2 0) (dy F33 1 (-2))) (dy F33 1 (-2)) = dy F33 2 0 ∧
    add (dy F33 2 0) (add (dy F33 1 (-2)) (dy F33 1 (-2))) = dy F33 5 (-1) := by
  decide +kernel

/-- `reassoc` and `contract` are not refinements in `F33`: a permitted form
of `(x + y) + z` differs from it at `(2, 1/4, 1/4)`, and a permitted form of
`x * y + z` differs from it at `(5/16, 7/8, 2)`. -/
theorem not_permittedFormsAgree_F33 :
    ¬ PermittedFormsAgree fReassoc (rwAddAssoc F33).lhs ∧
    ¬ PermittedFormsAgree fContract (rwContract F33).lhs := by
  constructor
  · intro h
    have := h envAssocRound (rwAddAssoc F33).rhs (by decide +kernel)
    revert this; decide +kernel
  · intro h
    have := h (env3 (dy F33 5 (-4)) (dy F33 7 (-3)) (dy F33 2 0)) (rwContract F33).rhs
      (by decide +kernel)
    revert this; decide +kernel

/-! ### Contraction and accuracy -/

/-- Contraction changes results on finite inputs, by rounding alone: for
`a = 5/16`, `b = 7/8`, `c = 2` the inputs, the exact product (`70` units of
`2^-8`, i.e. `35/128 ≥ 1/4`), the rounded product (`1/4`) and both results are
normal, `fma a b c = 2.5` and `a * b + c = 2`. -/
theorem fma_ne_twoStep_all_normal_F33 :
    F33.fracCount * 2 ^ F33.qneg ≤ (dy F33 5 (-4)).units * (dy F33 7 (-3)).units ∧
    (dy F33 5 (-4)).units * (dy F33 7 (-3)).units = 70 ∧
    mul (dy F33 5 (-4)) (dy F33 7 (-3)) = dy F33 1 (-2) ∧
    [dy F33 5 (-4), dy F33 7 (-3), dy F33 2 0, mul (dy F33 5 (-4)) (dy F33 7 (-3)),
      fma (dy F33 5 (-4)) (dy F33 7 (-3)) (dy F33 2 0),
      add (mul (dy F33 5 (-4)) (dy F33 7 (-3))) (dy F33 2 0)].all FP.isNormal = true ∧
    fma (dy F33 5 (-4)) (dy F33 7 (-3)) (dy F33 2 0) = dy F33 5 (-1) ∧
    add (mul (dy F33 5 (-4)) (dy F33 7 (-3))) (dy F33 2 0) = dy F33 2 0 := by
  decide +kernel

/-- The corner where "fma is at least as accurate" fails: for `a = 3/4`,
`b = 12`, `c = 6` (exact `a*b + c = 15`, the overflow threshold) the two-step
`a * b + c` is the finite value `14` (`9` rounds to `8`), while `fma a b c`
overflows to `+∞`; so the error of `fma` is not at most that of the two-step
form. This instance satisfies every hypothesis of
`fma_errLe_twoStep_of_fma_finite` except finiteness of the fused result, and
shows that finiteness of the two-step result is not a sufficient
hypothesis. -/
theorem fma_overflows_while_twoStep_finite_F33 :
    fma (dy F33 3 (-2)) (dy F33 12 0) (dy F33 6 0) = .inf false ∧
    add (mul (dy F33 3 (-2)) (dy F33 12 0)) (dy F33 6 0) = dy F33 14 0 ∧
    exactMulAdd (dy F33 3 (-2)) (dy F33 12 0) (dy F33 6 0) = 15 * 2 ^ 8 ∧
    ¬ ErrLe (errOf (fma (dy F33 3 (-2)) (dy F33 12 0) (dy F33 6 0))
          (exactMulAdd (dy F33 3 (-2)) (dy F33 12 0) (dy F33 6 0)))
        (errOf (add (mul (dy F33 3 (-2)) (dy F33 12 0)) (dy F33 6 0))
          (exactMulAdd (dy F33 3 (-2)) (dy F33 12 0) (dy F33 6 0))) := by
  decide +kernel

/-- Non-vacuity for `fma_nearest_of_fma_finite` and
`fma_errLe_twoStep_of_fma_finite`: at `(5/16, 7/8, 2)` the fused result is
finite, and its error (`29/128`, i.e. 58 units of `2^-8`) is strictly below
the two-step error (`35/128`, i.e. 70 units). -/
theorem nv_fma_accuracy_F33 :
    (fma (dy F33 5 (-4)) (dy F33 7 (-3)) (dy F33 2 0)).isFinite = true ∧
    errOf (fma (dy F33 5 (-4)) (dy F33 7 (-3)) (dy F33 2 0))
      (exactMulAdd (dy F33 5 (-4)) (dy F33 7 (-3)) (dy F33 2 0)) = some 58 ∧
    errOf (add (mul (dy F33 5 (-4)) (dy F33 7 (-3))) (dy F33 2 0))
      (exactMulAdd (dy F33 5 (-4)) (dy F33 7 (-3)) (dy F33 2 0)) = some 70 := by
  decide +kernel

/-- The contraction hazard: at `a = 3/16`, `b = 3`, the product `a*b = 9/16`
rounds to `1/2`, the flag-free value of `a*b - a*b` is `+0`, but
`Expr.variants fContract` generates the form `fma a b (-(a*b))`, whose value is
`1/16` (the rounding error of the product). -/
theorem contract_mulSubMul_nonzero_F33 :
    mul (dy F33 3 (-4)) (dy F33 3 0) = dy F33 1 (-1) ∧
    (eMulSubMul F33).eval (env2 (dy F33 3 (-4)) (dy F33 3 0)) = posZero F33 ∧
    Expr.fma (.var 0) (.var 1) (.neg (.mul (.var 0) (.var 1))) ∈ (eMulSubMul F33).variants fContract ∧
    (Expr.fma (.var 0) (.var 1) (.neg (.mul (.var 0) (.var 1)))).eval
      (env2 (dy F33 3 (-4)) (dy F33 3 0)) = dy F33 1 (-4) := by
  decide +kernel

/-- Bound on the hazard: an inexact product does not always produce a nonzero
`fma a b (-(a*b))`. At `a = 1/16`, `b = 3.5` the product `7/32` rounds to the
normal value `1/4`, yet the error `-1/32` is half the smallest subnormal and
`fma a b (-(a*b))` rounds it to `-0`. -/
theorem fma_mulSubMul_zero_for_inexact_product_F33 :
    mul (dy F33 1 (-4)) (dy F33 7 (-1)) = dy F33 1 (-2) ∧
    (mul (dy F33 1 (-4)) (dy F33 7 (-1))).isNormal = true ∧
    (mul (dy F33 1 (-4)) (dy F33 7 (-1))).val2 ≠ ((dy F33 1 (-4)).units * (dy F33 7 (-1)).units : Nat) ∧
    fma (dy F33 1 (-4)) (dy F33 7 (-1)) (mul (dy F33 1 (-4)) (dy F33 7 (-1))).neg = negZero F33 := by
  decide +kernel

/-! ### Double rounding -/

/-- Double rounding is not innocuous in general: with narrow `F33` (`p = 3`)
and wide `W34` (`p' = 4`), `3/16 + 2.5` computed in `W34` and rounded back is
`3`, while direct addition gives `2.5`. -/
theorem addVia_ne_add_F33_W34 :
    addVia W34 (dy F33 3 (-4)) (dy F33 5 (-1)) ≠ add (dy F33 3 (-4)) (dy F33 5 (-1)) ∧
    addVia W34 (dy F33 3 (-4)) (dy F33 5 (-1)) = dy F33 3 0 ∧
    add (dy F33 3 (-4)) (dy F33 5 (-1)) = dy F33 5 (-1) := by
  decide +kernel

/-- Tightness of `2p + 1 ≤ p'` for addition: `W36` (`p' = 2p = 6`) has the
exponent range of `F33`, yet `7/16 + 5` via `W36` is `6` while direct addition
gives `5`. -/
theorem addVia_ne_add_F33_W36 :
    ¬ (2 * F33.p + 1 ≤ W36.p) ∧ F33.bias ≤ W36.bias ∧
    addVia W36 (dy F33 7 (-4)) (dy F33 5 0) ≠ add (dy F33 7 (-4)) (dy F33 5 0) ∧
    addVia W36 (dy F33 7 (-4)) (dy F33 5 0) = dy F33 6 0 ∧
    add (dy F33 7 (-4)) (dy F33 5 0) = dy F33 5 0 := by
  decide +kernel

/-- Tightness of `bias f ≤ bias g` for addition: `W29` has `p' = 9 ≥ 2p + 1`
but a smaller exponent range, so widening the input `4` to `W29` already
overflows to `+∞`, and `4 + 0` via `W29` is `+∞`. -/
theorem addVia_ne_add_F33_W29 :
    2 * F33.p + 1 ≤ W29.p ∧ ¬ (F33.bias ≤ W29.bias) ∧ cvt F33 W29 (dy F33 4 0) = .inf false ∧
    addVia W29 (dy F33 4 0) (posZero F33) ≠ add (dy F33 4 0) (posZero F33) ∧
    addVia W29 (dy F33 4 0) (posZero F33) = .inf false ∧ add (dy F33 4 0) (posZero F33) = dy F33 4 0 := by
  decide +kernel

/-- Tightness of `2p ≤ p'` for multiplication: narrow `F34` (`p = 4`), wide
`W57` (`p' = 7 = 2p - 1`) with the other two hypotheses satisfied;
`(13/32) * (13/16)` via `W57` is `5/16`, directly `11/32`. -/
theorem mulVia_ne_mul_F34_W57 :
    ¬ (2 * F34.p ≤ W57.p) ∧ 2 * F34.qneg ≤ W57.qneg ∧ F34.bias ≤ W57.bias ∧
    mulVia W57 (dy F34 13 (-5)) (dy F34 13 (-4)) ≠ mul (dy F34 13 (-5)) (dy F34 13 (-4)) ∧
    mulVia W57 (dy F34 13 (-5)) (dy F34 13 (-4)) = dy F34 5 (-4) ∧
    mul (dy F34 13 (-5)) (dy F34 13 (-4)) = dy F34 11 (-5) := by
  decide +kernel

/-- Tightness of `2 * qneg f ≤ qneg g` for multiplication: `W36` has
`p' = 2p` and the exponent range of `F33`, but its smallest subnormal `2^-7`
is not below `(2^-4)^2`; `(3/16)^2` via `W36` is `+0`, directly `1/16`. -/
theorem mulVia_ne_mul_F33_W36 :
    2 * F33.p ≤ W36.p ∧ ¬ (2 * F33.qneg ≤ W36.qneg) ∧ F33.bias ≤ W36.bias ∧
    mulVia W36 (dy F33 3 (-4)) (dy F33 3 (-4)) ≠ mul (dy F33 3 (-4)) (dy F33 3 (-4)) ∧
    mulVia W36 (dy F33 3 (-4)) (dy F33 3 (-4)) = posZero F33 ∧
    mul (dy F33 3 (-4)) (dy F33 3 (-4)) = dy F33 1 (-4) := by
  decide +kernel

/-- Tightness of `bias f ≤ bias g` for multiplication: `W29` satisfies the
precision and subnormal hypotheses, but widening the input `4` to `W29`
already overflows, and `4 * 1` via `W29` is `+∞`. -/
theorem mulVia_ne_mul_F33_W29 :
    2 * F33.p ≤ W29.p ∧ 2 * F33.qneg ≤ W29.qneg ∧ ¬ (F33.bias ≤ W29.bias) ∧
    cvt F33 W29 (dy F33 4 0) = .inf false ∧
    mulVia W29 (dy F33 4 0) (one F33) ≠ mul (dy F33 4 0) (one F33) ∧
    mulVia W29 (dy F33 4 0) (one F33) = .inf false ∧ mul (dy F33 4 0) (one F33) = dy F33 4 0 := by
  decide +kernel

/-! ### Comparisons, `min`/`max` -/

/-- The failing instance of `a < b ↔ ¬(a >= b)`: with a NaN operand both
`<` and `>=` are false. A holding instance: `1 < 2`. -/
theorem lt_ne_not_ge_at_nan_F33 :
    lt .nan (one F33) ≠ !(ge .nan (one F33)) ∧ lt (one F33) (dy F33 2 0) = !(ge (one F33) (dy F33 2 0)) := by
  decide +kernel

/-- `min`/`max` defined by `<` are not commutative under NaN and under signed
zero; they are at `1`, `2`. -/
theorem minLt_maxLt_not_comm_F33 :
    minLt .nan (one F33) ≠ minLt (one F33) .nan ∧
    minLt (posZero F33) (negZero F33) ≠ minLt (negZero F33) (posZero F33) ∧
    maxLt .nan (one F33) ≠ maxLt (one F33) .nan ∧
    maxLt (posZero F33) (negZero F33) ≠ maxLt (negZero F33) (posZero F33) ∧
    minLt (one F33) (dy F33 2 0) = minLt (dy F33 2 0) (one F33) := by
  decide +kernel

/-- Non-vacuity for `minimum_maximum_comm_assoc` at the cases that break
`minLt`: NaN and the two zeros. -/
theorem nv_minimum_F33 :
    minimum .nan (one F33) = minimum (one F33) .nan ∧
    minimum (posZero F33) (negZero F33) = minimum (negZero F33) (posZero F33) ∧
    maximum (posZero F33) (negZero F33) = maximum (negZero F33) (posZero F33) := by
  decide +kernel

/-! ### Moved closed checks and further witnesses -/

/-- Non-vacuity of `add_assoc_fails_by_rounding_all_normal_of_prec_le_two_bias`
[bounded: the formats F32 and F33]: its hypothesis and conclusion hold in both
formats. -/
theorem add_assoc_fails_by_rounding_all_normal_F32_F33 :
    (F32.p + 1 ≤ 2 * F32.bias ∧
      [assocRoundA F32, assocRoundB F32, add (assocRoundA F32) (assocRoundB F32),
        add (assocRoundB F32) (assocRoundB F32),
        add (add (assocRoundA F32) (assocRoundB F32)) (assocRoundB F32),
        add (assocRoundA F32) (add (assocRoundB F32) (assocRoundB F32))].all FP.isNormal = true ∧
      add (add (assocRoundA F32) (assocRoundB F32)) (assocRoundB F32) = assocRoundA F32 ∧
      add (assocRoundA F32) (add (assocRoundB F32) (assocRoundB F32)) ≠ assocRoundA F32) ∧
    (F33.p + 1 ≤ 2 * F33.bias ∧
      [assocRoundA F33, assocRoundB F33, add (assocRoundA F33) (assocRoundB F33),
        add (assocRoundB F33) (assocRoundB F33),
        add (add (assocRoundA F33) (assocRoundB F33)) (assocRoundB F33),
        add (assocRoundA F33) (add (assocRoundB F33) (assocRoundB F33))].all FP.isNormal = true ∧
      add (add (assocRoundA F33) (assocRoundB F33)) (assocRoundB F33) = assocRoundA F33 ∧
      add (assocRoundA F33) (add (assocRoundB F33) (assocRoundB F33)) ≠ assocRoundA F33) := by
  decide +kernel

/-- Non-vacuity of the double-rounding statements: their hypotheses hold for
the format pairs of the bounded instances in `Toy.Float.Bounded`. -/
theorem doubleRounding_hyps_bounded :
    (2 * F33.p + 1 ≤ W37.p ∧ F33.bias ≤ W37.bias) ∧ (2 * F33.p + 1 ≤ W38.p ∧ F33.bias ≤ W38.bias) ∧
    (2 * F33.p ≤ W46.p ∧ 2 * F33.qneg ≤ W46.qneg ∧ F33.bias ≤ W46.bias) ∧
    (2 * F33.p ≤ W38.p ∧ 2 * F33.qneg ≤ W38.qneg ∧ F33.bias ≤ W38.bias) ∧
    (2 * F34.p ≤ W58.p ∧ 2 * F34.qneg ≤ W58.qneg ∧ F34.bias ≤ W58.bias) := by
  decide

/-- Non-vacuity of `permittedFormsAgreeAt_iff_laws` in format F33: at
`(+0, +0, +0)` both pointwise agreements hold, and at `(2, 1/4, 1/4)` and
`(5/16, 7/8, 2)` they fail. -/
theorem nv_permittedFormsAgreeAt_true_and_false_F33 :
    PermittedFormsAgreeAt fReassoc (rwAddAssoc F33).lhs
      (env3 (posZero F33) (posZero F33) (posZero F33)) ∧
    PermittedFormsAgreeAt fContract (rwContract F33).lhs
      (env3 (posZero F33) (posZero F33) (posZero F33)) ∧
    ¬ PermittedFormsAgreeAt fReassoc (rwAddAssoc F33).lhs envAssocRound ∧
    ¬ PermittedFormsAgreeAt fContract (rwContract F33).lhs
        (env3 (dy F33 5 (-4)) (dy F33 7 (-3)) (dy F33 2 0)) := by
  decide +kernel

/-- `((w + x) + y) + z → (w + x) + (y + z)`. -/
def rwAssoc4Step1 (f : Fmt) : Rewrite f 4 :=
  ⟨.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.var 3),
   .add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3))⟩

/-- `(w + x) + (y + z) → w + (x + (y + z))`. -/
def rwAssoc4Step2 (f : Fmt) : Rewrite f 4 :=
  ⟨.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)),
   .add (.var 0) (.add (.var 1) (.add (.var 2) (.var 3)))⟩

/-- The composite `((w + x) + y) + z → w + (x + (y + z))`. -/
def rwAssoc4Comp (f : Fmt) : Rewrite f 4 :=
  ⟨(rwAssoc4Step1 f).lhs, (rwAssoc4Step2 f).rhs⟩

/-- Environment from four values. -/
def env4 {f : Fmt} (w x y z : FP f) : Fin 4 → FP f :=
  fun i => if i.val = 0 then w else if i.val = 1 then x else if i.val = 2 then y else z

/-- The witness `(4, 1/2, 1/16, 1/16)` in F33. -/
def envAssoc4Witness : Fin 4 → FP F33 :=
  env4 (dy F33 4 0) (dy F33 1 (-1)) (dy F33 1 (-4)) (dy F33 1 (-4))

/-- `Expr.variants` performs at most one reassociation step per node: the right
bracketing `w + (x + (y + z))` is not among the forms it generates for
`((w + x) + y) + z`, even with all five flags. -/
theorem reassoc_variants_omits_right_assoc_F33 :
    (rwAssoc4Comp F33).rhs ∉ (rwAssoc4Comp F33).lhs.variants Flags.all := by
  decide +kernel

/-- `ValidMod` is not transitive: both one-step reassociations are valid modulo
`reassoc`, but their composite is not valid even modulo all five flags; at
`(4, 1/2, 1/16, 1/16)` (admissible under all flags) every generated form of
the source evaluates to `4` while the composite's target evaluates to `5`. -/
theorem reassoc_validMod_not_transitive_F33 :
    ValidMod fReassoc (rwAssoc4Step1 F33) ∧
    ValidMod fReassoc (rwAssoc4Step2 F33) ∧
    Admissible Flags.all (rwAssoc4Comp F33).lhs envAssoc4Witness ∧
    (rwAssoc4Comp F33).rhs.eval envAssoc4Witness = dy F33 5 0 ∧
    (∀ v ∈ (rwAssoc4Comp F33).lhs.variants Flags.all, v.eval envAssoc4Witness = dy F33 4 0) ∧
    ¬ ValidMod Flags.all (rwAssoc4Comp F33) := by
  have hadm : Admissible Flags.all (rwAssoc4Comp F33).lhs envAssoc4Witness := by decide +kernel
  have hall : ∀ v ∈ (rwAssoc4Comp F33).lhs.variants Flags.all,
      v.eval envAssoc4Witness = dy F33 4 0 := by decide +kernel
  have hrhs : (rwAssoc4Comp F33).rhs.eval envAssoc4Witness = dy F33 5 0 := by decide +kernel
  refine ⟨?_, ?_, hadm, hrhs, hall, ?_⟩
  · intro env _
    exact ⟨(rwAssoc4Step1 F33).rhs, by decide +kernel, by unfold Rel; split <;> rfl⟩
  · intro env _
    exact ⟨(rwAssoc4Step2 F33).rhs, by decide +kernel, by unfold Rel; split <;> rfl⟩
  · intro h
    obtain ⟨v, hv, hr⟩ := h envAssoc4Witness hadm
    rw [hall v hv, hrhs] at hr
    revert hr; decide +kernel

/-- `Rel` under `nsz` identifies the zero results of underflowing nonzero
operands: the closed rewrite `(-1/16) * (1/2) → +0` (no variables) is valid
modulo `{nsz}`, although neither operand is a zero and the source evaluates to
`-0`. -/
theorem nsz_rel_identifies_underflow_sign_F33 :
    ValidMod fNsz (⟨.mul (.lit (dy F33 (-1) (-4))) (.lit (dy F33 1 (-1))), .lit (posZero F33)⟩ :
      Rewrite F33 0) ∧
    (dy F33 (-1) (-4)).isZero = false ∧ (dy F33 1 (-1)).isZero = false ∧
    mul (dy F33 (-1) (-4)) (dy F33 1 (-1)) = negZero F33 := by
  decide +kernel

/-- `min` defined by `<` is not associative in the presence of NaN:
`minLt (minLt 1 NaN) 2 = 2` while `minLt 1 (minLt NaN 2) = 1`. -/
theorem minLt_not_assoc_at_nan_F33 :
    minLt (minLt (one F33) .nan) (dy F33 2 0) = dy F33 2 0 ∧
    minLt (one F33) (minLt .nan (dy F33 2 0)) = one F33 ∧ dy F33 2 0 ≠ one F33 := by
  decide +kernel

/-- Partial contraction can produce a negative residual: at `a = 5/4`,
`b = 3/2` the product `15/8` rounds up to `2`, and `fma a b (-(a*b)) = -1/8`. -/
theorem fma_mulSubMul_negative_F33 :
    mul (dy F33 5 (-2)) (dy F33 3 (-1)) = dy F33 2 0 ∧
    fma (dy F33 5 (-2)) (dy F33 3 (-1)) (mul (dy F33 5 (-2)) (dy F33 3 (-1))).neg = dy F33 (-1) (-3) := by
  decide +kernel

end Toy.Float
