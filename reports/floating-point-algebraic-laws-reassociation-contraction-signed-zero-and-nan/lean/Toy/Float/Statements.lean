/-
Toy.Float.Statements
====================

Main results, stated for every format `f` (exponent width `e ≥ 2`,
precision `p ≥ 2`) and proved here from the auxiliary lemmas in
`Toy.Float.Arith`, `Toy.Float.Props` and `Toy.Float.Rounding`.
`fma_errLe_twoStep_of_fma_finite` is derived from `fma_nearest_of_fma_finite`.
`Toy.Float.Bounded` additionally checks `fma_nearest_of_fma_finite` and the two
double-rounding statements exhaustively, by kernel evaluation, in the small
formats it names.
-/
import Toy.Float.Props
import Toy.Float.Rounding

namespace Toy.Float

variable {f : Fmt}

/-! ### Commutativity and identities -/

/-- In the collapsed-NaN model, `add`, `mul` and the product part of `fma` are
commutative up to identity of encodings, on all inputs (including NaN, `±∞`,
`±0`). -/
theorem add_comm_mul_comm_fma_comm (x y z : FP f) :
    add x y = add y x ∧ mul x y = mul y x ∧ fma x y z = fma y x z := by
  refine ⟨add_comm' x y, ?_, ?_⟩
  · cases x <;> cases y <;> simp [mul, bne_comm']
    rw [Nat.mul_comm]
  · rcases x with _ | s | ⟨s, E, M⟩ <;> rcases y with _ | t | ⟨t, E', M'⟩ <;>
      rcases z with _ | u | ⟨u, E'', M''⟩
    all_goals try rfl
    all_goals simp only [fma, exactFma, FP.isZero, FP.signBit]
    all_goals try (cases s <;> cases t <;> cases u <;> rfl)
    all_goals try (cases s <;> cases t <;> simp [Bool.or_comm])
    all_goals rw [Nat.mul_comm (unitsOf f E.val M.val)]

theorem add_negZero_right (x : FP f) : add x (negZero f) = x := by
  cases x with
  | nan => rfl
  | inf s => rfl
  | fin s E M =>
    rw [negZero, add_fin_zero]
    split
    · rename_i hu; rw [fin_eq_zero_of_units hu, Bool.and_true]
    · rfl

theorem mul_one_right (x : FP f) : mul x (one f) = x := by
  obtain ⟨E1, M1, h1, -, hu1⟩ := one_fields f
  rw [h1]
  cases x with
  | nan => rfl
  | inf s =>
    show (if unitsOf f E1.val M1.val = 0 then FP.nan else FP.inf (s != false)) = _
    rw [hu1]; simp [Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)]
  | fin s E M =>
    show round f (s != false) (unitsOf f E.val M.val * unitsOf f E1.val M1.val) f.qneg = _
    rw [hu1]
    have := round_units (FP.fin s E M) rfl f.qneg
    simpa [FP.units, FP.signBit] using this

/-- `x + (-0) = x` and `x * 1 = x` for every `x`. -/
theorem add_negZero_right_and_mul_one_right (x : FP f) :
    add x (negZero f) = x ∧ mul x (one f) = x :=
  ⟨add_negZero_right x, mul_one_right x⟩

/-- `x + (+0) = x` holds exactly when `x ≠ -0`, and `x + (+0)` equals `x` up to
the sign of zero for every `x`. -/
theorem add_posZero_right_eq_iff_and_eqNsz (x : FP f) :
    (add x (posZero f) = x ↔ x ≠ negZero f) ∧ EqNsz (add x (posZero f)) x := by
  cases x with
  | nan => exact ⟨⟨fun _ => by simp [negZero, zero], fun _ => rfl⟩, eqNsz_refl _⟩
  | inf s => exact ⟨⟨fun _ => by simp [negZero, zero], fun _ => rfl⟩, eqNsz_refl _⟩
  | fin s E M =>
    rw [posZero, add_fin_zero]
    by_cases hu : unitsOf f E.val M.val = 0
    · rw [if_pos hu, fin_eq_zero_of_units hu, Bool.and_false]
      refine ⟨?_, eqNsz_zeros _ _⟩
      cases s <;> simp [negZero, zero_ne_zero_iff]
    · rw [if_neg hu]
      refine ⟨⟨fun _ h => hu ?_, fun _ => rfl⟩, eqNsz_refl _⟩
      simp only [negZero, zero, FP.fin.injEq] at h
      rw [h.2.1, h.2.2]; rfl

/-- `x - x = +0` holds exactly when `x` is finite, and `x - x` is NaN exactly
when `x` is not finite (NaN or `±∞`). -/
theorem sub_self_eq_posZero_iff_and_eq_nan_iff (x : FP f) :
    (sub x x = posZero f ↔ x.isFinite = true) ∧ (sub x x = .nan ↔ x.isFinite = false) := by
  cases x with
  | nan => simp [sub, add, posZero, zero, FP.isFinite]
  | inf s => cases s <;> simp [sub, add, posZero, zero, FP.neg, FP.isFinite]
  | fin s E M =>
    have h : sub (FP.fin s E M) (FP.fin s E M) = posZero f := by
      cases s
      · have hv : sval false (unitsOf f E.val M.val) + sval true (unitsOf f E.val M.val) = 0 := by
          simp only [sval, Bool.false_eq_true, ite_true, ite_false]; omega
        simp [sub, add, FP.neg, hv, posZero]
      · have hv : sval true (unitsOf f E.val M.val) + sval false (unitsOf f E.val M.val) = 0 := by
          simp only [sval, Bool.false_eq_true, ite_true, ite_false]; omega
        simp [sub, add, FP.neg, hv, posZero]
    rw [h]; simp [posZero, zero, FP.isFinite]

/-- `x == x` holds exactly when `x` is not NaN. -/
theorem feq_self_iff (x : FP f) : feq x x = true ↔ x ≠ .nan := by
  cases x <;> simp [feq, FP.isNaN]

theorem mul_fin_posZero (s : Bool) (E : Fin f.expCount) (M : Fin f.fracCount) :
    mul (FP.fin s E M) (posZero f) = zero f s := by
  show round f (s != false) (unitsOf f E.val M.val * unitsOf f 0 0) f.qneg = _
  simp only [unitsOf_zero_left, Nat.mul_zero, bne_false', round, roundUnits_zero, mkFin_zero]

/-- `x * (+0) = +0` holds exactly when `x` is finite with sign bit clear; for
every non-finite `x` (NaN, `±∞`) the product is NaN, and for every finite `x`
with the sign bit set (`-0` and every negative finite value) it is `-0`. -/
theorem mul_posZero_eq_posZero_iff_and_failure_values (x : FP f) :
    (mul x (posZero f) = posZero f ↔ x.isFinite = true ∧ x.signBit = false) ∧
    (x.isFinite = false → mul x (posZero f) = .nan) ∧
    (x.isFinite = true → x.signBit = true → mul x (posZero f) = negZero f) := by
  cases x with
  | nan => simp [mul, posZero, zero, FP.isFinite]
  | inf s => simp [mul, posZero, zero, unitsOf, FP.isFinite]
  | fin s E M =>
    rw [mul_fin_posZero]
    cases s <;> simp [posZero, negZero, zero_ne_zero_iff, FP.isFinite, FP.signBit]

/-! ### Associativity -/

/-- Rounding alone breaks associativity: if `p + 1 ≤ 2 * bias`, then for
`a = 2^(emin + p)` and `b = 2^emin` the inputs, both intermediate sums and both
results are normal, `(a + b) + b = a` (each addition is a tie that rounds to
even), and `a + (b + b) ≠ a`. -/
theorem add_assoc_fails_by_rounding_all_normal_of_prec_le_two_bias (f : Fmt)
    (h : f.p + 1 ≤ 2 * f.bias) :
    [assocRoundA f, assocRoundB f, add (assocRoundA f) (assocRoundB f),
      add (assocRoundB f) (assocRoundB f),
      add (add (assocRoundA f) (assocRoundB f)) (assocRoundB f),
      add (assocRoundA f) (add (assocRoundB f) (assocRoundB f))].all FP.isNormal = true ∧
    add (add (assocRoundA f) (assocRoundB f)) (assocRoundB f) = assocRoundA f ∧
    add (assocRoundA f) (add (assocRoundB f) (assocRoundB f)) ≠ assocRoundA f := by
  have hp := f.two_le_p
  have hF := f.two_pow_p_eq
  have hFp := f.two_le_fracCount
  have hX : 0 < 2 ^ f.p := Nat.two_pow_pos _
  have hmax : (f.fracCount + 1) * 2 ^ f.p ≤ f.maxUnits := by
    rw [f.maxUnits_eq]; exact Nat.mul_le_mul (by omega) (two_pow_le_two_pow (by omega))
  have hle1 : f.fracCount * 2 ^ f.p ≤ f.maxUnits :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_succ _)) hmax
  have hle2 : 2 ^ f.p ≤ f.maxUnits :=
    Nat.le_trans (Nat.le_mul_of_pos_left _ (by omega)) hmax
  have hle3 : f.fracCount ≤ f.maxUnits := f.fracCount_le_maxUnits
  have rA : IsRepr f (f.fracCount * 2 ^ f.p) := ⟨f.fracCount, f.p, by omega, rfl⟩
  have rB : IsRepr f f.fracCount := isRepr_of_lt (by omega)
  have r2 : IsRepr f (2 ^ f.p) := isRepr_two_pow f f.p
  have rC : IsRepr f ((f.fracCount + 1) * 2 ^ f.p) := ⟨f.fracCount + 1, f.p, by omega, rfl⟩
  have hA : assocRoundA f = mkFin f false (f.fracCount * 2 ^ f.p) := by
    rw [assocRoundA, ofDyadic_false_eq_mkFin f _ (2 * f.p - 1) (by unfold Fmt.qneg; omega)]
    congr 1; unfold Fmt.fracCount; rw [← Nat.pow_add]; congr 1; omega
  have hB : assocRoundB f = mkFin f false f.fracCount := by
    rw [assocRoundB, ofDyadic_false_eq_mkFin f _ (f.p - 1) (by unfold Fmt.qneg; omega)]; rfl
  obtain ⟨EA, MA, hA', huA⟩ := mkFin_repr rA hle1
  obtain ⟨EB, MB, hB', huB⟩ := mkFin_repr rB hle3
  obtain ⟨E2, M2, h2', hu2⟩ := mkFin_repr r2 hle2
  have hab : add (assocRoundA f) (assocRoundB f) = assocRoundA f := by
    rw [hA, hB, hA' false, hB' false, add_fin_false, huA, huB, roundUnits_tie, hA' false]
  have hbb : add (assocRoundB f) (assocRoundB f) = mkFin f false (2 ^ f.p) := by
    rw [hB, hB' false, add_fin_false, huB, show f.fracCount + f.fracCount = 2 ^ f.p by omega,
      roundUnits_repr0 r2]
  have habb : add (assocRoundA f) (add (assocRoundB f) (assocRoundB f)) =
      mkFin f false ((f.fracCount + 1) * 2 ^ f.p) := by
    rw [hbb, h2' false, hA, hA' false, add_fin_false, huA, hu2,
      show f.fracCount * 2 ^ f.p + 2 ^ f.p = (f.fracCount + 1) * 2 ^ f.p by rw [Nat.succ_mul],
      roundUnits_repr0 rC]
  have hne : mkFin f false ((f.fracCount + 1) * 2 ^ f.p) ≠ mkFin f false (f.fracCount * 2 ^ f.p) :=
    mkFin_ne rC hmax rA hle1 (by rw [Nat.succ_mul]; omega) false
  refine ⟨?_, ?_, ?_⟩
  · simp only [hab]
    simp only [habb]
    simp only [hbb]
    simp only [hA, hB, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
      | exact isNormal_mkFin rA (Nat.le_mul_of_pos_right _ hX) hle1 false
      | exact isNormal_mkFin rB (Nat.le_refl _) hle3 false
      | exact isNormal_mkFin r2 (by omega) hle2 false
      | exact isNormal_mkFin rC (Nat.le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_right _ hX)) hmax false
  · rw [hab, hab]
  · rw [habb, hA]; exact hne


theorem add_maxFinite_self (f : Fmt) :
    add (maxFinite f false) (maxFinite f false) = .inf false := by
  obtain ⟨E, M, hM, hu⟩ := maxFinite_fields f
  rw [hM false]
  show (let v := sval false (unitsOf f E.val M.val) + sval false (unitsOf f E.val M.val)
    if v = 0 then zero f (false && false) else round f (decide (v < 0)) v.natAbs 0) = _
  dsimp only
  rw [hu]
  have hpos := maxUnits_pos f
  have hv : sval false f.maxUnits + sval false f.maxUnits = ((f.maxUnits * 2 ^ 1 : Nat) : Int) := by
    simp only [sval, Bool.false_eq_true, ite_false, Nat.pow_one]; push_cast; omega
  rw [hv, if_neg (by omega), Int.natAbs_natCast,
    show decide (((f.maxUnits * 2 ^ 1 : Nat) : Int) < 0) = false from decide_eq_false (by omega)]
  unfold round
  rw [roundUnits_repr0 (f.maxUnits_isRepr.mul_two_pow 1), mkFin_overflow (by rw [Nat.pow_one]; omega)]

theorem add_maxFinite_neg (f : Fmt) :
    add (maxFinite f false) (maxFinite f true) = posZero f := by
  obtain ⟨E, M, hM, hu⟩ := maxFinite_fields f
  rw [hM false, hM true]
  show (let v := sval false (unitsOf f E.val M.val) + sval true (unitsOf f E.val M.val)
    if v = 0 then zero f (false && true) else round f (decide (v < 0)) v.natAbs 0) = _
  have hv : sval false (unitsOf f E.val M.val) + sval true (unitsOf f E.val M.val) = 0 := by
    simp only [sval, Bool.false_eq_true, ite_true, ite_false]; omega
  simp only [hv, ite_true]; rfl

theorem add_maxFinite_posZero (f : Fmt) :
    add (maxFinite f false) (posZero f) = maxFinite f false := by
  obtain ⟨E, M, hM, hu⟩ := maxFinite_fields f
  rw [hM false, posZero, add_fin_zero, if_neg (by rw [hu]; have := maxUnits_pos f; omega)]

/-- Overflow breaks associativity in every format: with `M` the largest
finite value, `(M + M) + (-M) = +∞` while `M + (M + (-M)) = M`. -/
theorem add_assoc_fails_by_overflow (f : Fmt) :
    add (add (maxFinite f false) (maxFinite f false)) (maxFinite f true) = .inf false ∧
    add (maxFinite f false) (add (maxFinite f false) (maxFinite f true)) = maxFinite f false := by
  refine ⟨?_, ?_⟩
  · rw [add_maxFinite_self]
    obtain ⟨E, M, hM, -⟩ := maxFinite_fields f
    rw [hM true]; rfl
  · rw [add_maxFinite_neg, add_maxFinite_posZero]

/-- Under round-to-nearest-even, the two bracketings of a sum never differ
only in the sign of zero: if they are equal up to the sign of zero, they are
identical. -/
theorem add_assoc_defect_never_only_zero_sign (a b c : FP f)
    (h : EqNsz (add (add a b) c) (add a (add b c))) : add (add a b) c = add a (add b c) := by
  unfold EqNsz zeroBlind at h
  by_cases hX : (add (add a b) c).isZero = true <;> by_cases hY : (add a (add b c)).isZero = true
  · have key : add (add a b) c = negZero f ↔ add a (add b c) = negZero f := by
      rw [add_eq_negZero_iff, add_eq_negZero_iff, add_eq_negZero_iff, add_eq_negZero_iff]
      exact and_assoc
    have eX := eq_zero_of_isZero hX
    have eY := eq_zero_of_isZero hY
    generalize (add (add a b) c).signBit = sX at eX
    generalize (add a (add b c)).signBit = sY at eY
    rw [eX, eY] at key ⊢
    cases sX <;> cases sY <;> simp_all [negZero, zero_ne_zero_iff]
  · simp only [hX, hY, ite_true, ite_false, Bool.false_eq_true] at h
    rw [← h] at hY; simp [isZero_zero] at hY
  · simp only [hX, hY, ite_true, ite_false, Bool.false_eq_true] at h
    rw [h] at hX; simp [isZero_zero] at hX
  · simpa [hX, hY] using h

/-- Pointwise: the forms permitted by `reassoc` for `(x + y) + z` all agree with
it at `(a, b, c)` exactly when `(a + b) + c = a + (b + c)`, and the forms
permitted by `contract` for `x * y + z` all agree with it at `(a, b, c)` exactly
when `fma a b c = a * b + c`. -/
theorem permittedFormsAgreeAt_iff_laws (a b c : FP f) :
    (PermittedFormsAgreeAt fReassoc (rwAddAssoc f).lhs (env3 a b c) ↔
      add (add a b) c = add a (add b c)) ∧
    (PermittedFormsAgreeAt fContract (rwContract f).lhs (env3 a b c) ↔
      fma a b c = add (mul a b) c) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    have hv := h (.add (.var 0) (.add (.var 1) (.var 2)))
      (by simp [rwAddAssoc, Expr.variants, fReassoc, Expr.reassocAdd])
    simpa [rwAddAssoc, Expr.eval, env3] using hv.symm
  · intro h v hv
    simp [rwAddAssoc, Expr.variants, fReassoc, Expr.reassocAdd] at hv
    rcases hv with rfl | rfl
    · rfl
    · simpa [rwAddAssoc, Expr.eval, env3] using h.symm
  · intro h
    have hv := h (.fma (.var 0) (.var 1) (.var 2))
      (by simp [rwContract, Expr.variants, fContract, Expr.contractAdd])
    simpa [rwContract, Expr.eval, env3] using hv
  · intro h v hv
    simp [rwContract, Expr.variants, fContract, Expr.contractAdd] at hv
    rcases hv with rfl | rfl
    · rfl
    · simpa [rwContract, Expr.eval, env3] using h

theorem mul_maxFinite_two (f : Fmt) :
    mul (maxFinite f false) (ofDyadic f false 1 1) = .inf false := by
  obtain ⟨E, M, hM, hu⟩ := maxFinite_fields f
  obtain ⟨E2, M2, h2, hu2⟩ := two_fields f
  rw [hM false, h2]
  show round f (false != false) (unitsOf f E.val M.val * unitsOf f E2.val M2.val) f.qneg = _
  rw [hu, hu2]
  have : f.maxUnits * 2 ^ (f.qneg + 1) = (f.maxUnits * 2 ^ 1) * 2 ^ f.qneg := by
    rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm 1]
  rw [this, round_repr (f.maxUnits_isRepr.mul_two_pow 1), mkFin_overflow]
  · rfl
  · have := maxUnits_pos f; omega

theorem fma_maxFinite_two (f : Fmt) :
    fma (maxFinite f false) (ofDyadic f false 1 1) (maxFinite f true) = maxFinite f false := by
  obtain ⟨E, M, hM, hu⟩ := maxFinite_fields f
  obtain ⟨E2, M2, h2, hu2⟩ := two_fields f
  rw [hM false, hM true, h2]
  show (let v := (exactFma f false (unitsOf f E.val M.val) false (unitsOf f E2.val M2.val)
      true (unitsOf f E.val M.val))
    if v = 0 then zero f ((false != false) && true) else
      round f (decide (v < 0)) v.natAbs f.qneg) = _
  dsimp only
  rw [hu, hu2]
  have hv : exactFma f false f.maxUnits false (2 ^ (f.qneg + 1)) true f.maxUnits =
      ((f.maxUnits * 2 ^ f.qneg : Nat) : Int) := by
    unfold exactFma
    simp only [sval, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true]
    rw [Nat.pow_succ]
    have : f.maxUnits * (2 ^ f.qneg * 2) = 2 * (f.maxUnits * 2 ^ f.qneg) := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    rw [this]; push_cast; omega
  have hpos : 0 < f.maxUnits * 2 ^ f.qneg := Nat.mul_pos (maxUnits_pos f) (Nat.two_pow_pos _)
  rw [hv, if_neg (by omega)]
  simp only [Int.natAbs_natCast]
  rw [show decide (((f.maxUnits * 2 ^ f.qneg : Nat) : Int) < 0) = false from
      decide_eq_false (Int.not_lt.mpr (Int.natCast_nonneg _)),
    round_repr f.maxUnits_isRepr, ← hM false]
  rfl

/-- In every format, the permissions `reassoc` and `contract` change results:
with `M` the largest finite value, `(M + M) + (-M) = +∞` but its permitted form
`M + (M + (-M))` is `M`, and `M * 2 + (-M) = +∞` but its permitted form
`fma M 2 (-M)` is `M`; so at these inputs not every permitted form agrees with
the source expression. -/
theorem reassoc_contract_change_result_at_maxFinite (f : Fmt) :
    add (add (maxFinite f false) (maxFinite f false)) (maxFinite f true) = .inf false ∧
    add (maxFinite f false) (add (maxFinite f false) (maxFinite f true)) = maxFinite f false ∧
    add (mul (maxFinite f false) (ofDyadic f false 1 1)) (maxFinite f true) = .inf false ∧
    fma (maxFinite f false) (ofDyadic f false 1 1) (maxFinite f true) = maxFinite f false ∧
    ¬ PermittedFormsAgreeAt fReassoc (rwAddAssoc f).lhs
        (env3 (maxFinite f false) (maxFinite f false) (maxFinite f true)) ∧
    ¬ PermittedFormsAgreeAt fContract (rwContract f).lhs
        (env3 (maxFinite f false) (ofDyadic f false 1 1) (maxFinite f true)) := by
  obtain ⟨h1, h2⟩ := add_assoc_fails_by_overflow f
  have h3 : add (mul (maxFinite f false) (ofDyadic f false 1 1)) (maxFinite f true) =
      .inf false := by
    rw [mul_maxFinite_two]
    obtain ⟨E, M, hM, -⟩ := maxFinite_fields f
    rw [hM true]; rfl
  have h4 := fma_maxFinite_two f
  have hne : (FP.inf false : FP f) ≠ maxFinite f false := by
    obtain ⟨E, M, hM, -⟩ := maxFinite_fields f
    rw [hM false]; simp
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · rw [(permittedFormsAgreeAt_iff_laws _ _ _).1, h1, h2]; exact hne
  · rw [(permittedFormsAgreeAt_iff_laws _ _ _).2, h3, h4]; exact fun h => hne h.symm

/-- Corollary: in every format, neither `reassoc` on `(x + y) + z` nor
`contract` on `x * y + z` is a refinement of the flag-free semantics. -/
theorem not_permittedFormsAgree (f : Fmt) :
    ¬ PermittedFormsAgree fReassoc (rwAddAssoc f).lhs ∧
    ¬ PermittedFormsAgree fContract (rwContract f).lhs := by
  obtain ⟨-, -, -, -, h5, h6⟩ := reassoc_contract_change_result_at_maxFinite f
  exact ⟨fun h => h5 (h _), fun h => h6 (h _)⟩

/-! ### Contraction and accuracy -/

theorem FP.isFinite_ite {p : Prop} [Decidable p] (x y : FP f) :
    (if p then x else y).isFinite = if p then x.isFinite else y.isFinite := by
  split <;> rfl
@[simp] theorem FP.isFinite_nan : (FP.nan : FP f).isFinite = false := rfl
@[simp] theorem FP.isFinite_inf (s : Bool) : (FP.inf s : FP f).isFinite = false := rfl
@[simp] theorem FP.isFinite_fin (s : Bool) (E : Fin f.expCount) (M : Fin f.fracCount) :
    (FP.fin s E M : FP f).isFinite = true := rfl

/-- A finite `fma` result forces finite operands (so finiteness of the
operands need not be assumed separately). -/
theorem fma_isFinite_imp (a b c : FP f) (h : (fma a b c).isFinite = true) :
    a.isFinite = true ∧ b.isFinite = true ∧ c.isFinite = true := by
  cases a <;> cases b <;> cases c <;> simp [fma, FP.isZero, FP.signBit, FP.isFinite_ite] at h ⊢
  all_goals (revert h; cases ‹Bool› <;> cases ‹Bool› <;> cases ‹Bool› <;> simp)

/-- `fma` is the correctly rounded (RNE) value of the exact `a*b + c` for
finite operands whose exact `a*b + c` is nonzero (by definition of `fma`). -/
theorem fma_eq_round_exactMulAdd (a b c : FP f) (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hc : c.isFinite = true) (h0 : exactMulAdd a b c ≠ 0) :
    fma a b c = round f (decide (exactMulAdd a b c < 0)) (exactMulAdd a b c).natAbs f.qneg := by
  cases a <;> cases b <;> cases c <;> simp [FP.isFinite] at ha hb hc
  simp only [exactMulAdd, FP.signBit, FP.units] at h0 ⊢
  simp only [fma, h0, ite_false]; rfl

theorem fma_zero_of_exact_zero {f : Fmt} (a b c : FP f) (ha : a.isFinite = true)
    (hb : b.isFinite = true) (hc : c.isFinite = true) (h0 : exactMulAdd a b c = 0) :
    fma a b c = zero f ((a.signBit != b.signBit) && c.signBit) := by
  cases a <;> cases b <;> cases c <;> simp [FP.isFinite] at ha hb hc
  simp only [exactMulAdd, FP.signBit, FP.units] at h0 ⊢
  simp only [fma, h0, ite_true]

/-- If `fma a b c` is finite, its distance to the exact `a*b + c` is at most
that of every finite value `r`. -/
theorem fma_err_le {f : Fmt} (a b c r : FP f) (h : (fma a b c).isFinite = true)
    (hr : r.isFinite = true) :
    ((fma a b c).val2 - exactMulAdd a b c).natAbs ≤ (r.val2 - exactMulAdd a b c).natAbs := by
  obtain ⟨ha, hb, hc⟩ := fma_isFinite_imp a b c h
  by_cases h0 : exactMulAdd a b c = 0
  · rw [fma_zero_of_exact_zero a b c ha hb hc h0, h0]
    have hz : ∀ s : Bool, (zero f s).val2 = 0 := fun s => by
      simp only [FP.val2, zero_units, Nat.zero_mul, sval_zero]
    rw [hz, Int.sub_zero, Int.natAbs_zero]
    exact Nat.zero_le _
  · rw [fma_eq_round_exactMulAdd a b c ha hb hc h0] at h ⊢
    generalize exactMulAdd a b c = v at h h0 ⊢
    unfold round at h ⊢
    have hle : roundUnits f v.natAbs f.qneg ≤ f.maxUnits := by
      apply Nat.le_of_not_lt
      intro hc'
      rw [mkFin_overflow hc'] at h
      simp [FP.isFinite] at h
    obtain ⟨E, M, hEM, hu⟩ := mkFin_repr (roundUnits_isRepr f _ _) hle
    rw [hEM]
    cases r with
    | nan => simp [FP.isFinite] at hr
    | inf _ => simp [FP.isFinite] at hr
    | fin sr Er Mr =>
      simp only [FP.val2, FP.signBit, FP.units, hu]
      have hn := roundUnits_nearest f v.natAbs f.qneg (unitsOf f Er.val Mr.val)
        (unitsOf_isRepr f Mr.isLt)
      have h0n := roundUnits_nearest f v.natAbs f.qneg 0 (isRepr_zero f)
      rw [Nat.zero_mul] at h0n
      generalize roundUnits f v.natAbs f.qneg * 2 ^ f.qneg = X at hn h0n ⊢
      generalize unitsOf f Er.val Mr.val * 2 ^ f.qneg = Y at hn h0n ⊢
      cases sr <;> by_cases hneg : v < 0 <;> simp [sval, hneg] <;> omega

/-- Nearest property: if `fma a b c` is finite, its error with respect to the
exact `a*b + c` is at most the error of every value `r` of the format
(infinite for NaN and `±∞`). -/
theorem fma_nearest_of_fma_finite (a b c r : FP f) (h : (fma a b c).isFinite = true) :
    ErrLe (errOf (fma a b c) (exactMulAdd a b c)) (errOf r (exactMulAdd a b c)) := by
  unfold errOf
  rw [if_pos h]
  by_cases hr : r.isFinite = true
  · rw [if_pos hr]; exact fma_err_le a b c r h hr
  · rw [if_neg hr]; trivial

/-- If `fma a b c` is finite, its error is at most the error of the two-step
`a * b + c` (whose error is infinite if it overflows). Derived from
`fma_nearest_of_fma_finite` with `r := a * b + c`. -/
theorem fma_errLe_twoStep_of_fma_finite (a b c : FP f) (h : (fma a b c).isFinite = true) :
    ErrLe (errOf (fma a b c) (exactMulAdd a b c)) (errOf (add (mul a b) c) (exactMulAdd a b c)) :=
  fma_nearest_of_fma_finite a b c (add (mul a b) c) h

/-! ### Double rounding -/

/-- Addition computed in a wider format `g` and rounded to `f` equals direct
addition in `f` when `g` has at least `2p + 1` bits of precision and at least
the exponent range of `f` (`bias f ≤ bias g`). -/
theorem addVia_eq_add_of_two_mul_add_one_le_and_bias_le (f g : Fmt) (hp : 2 * f.p + 1 ≤ g.p)
    (hb : f.bias ≤ g.bias) (x y : FP f) : addVia g x y = add x y := by
  have hpp : f.p ≤ g.p := by omega
  have hq : f.qneg < g.qneg := by unfold Fmt.qneg; have := f.two_le_p; omega
  unfold addVia
  rcases x with _ | s | ⟨s, E, M⟩ <;> rcases y with _ | t | ⟨t, E', M'⟩
  case fin.fin =>
    obtain ⟨E2, M2, hc1, hu1⟩ := cvt_up_fin hpp hb s E M
    obtain ⟨E2', M2', hc2, hu2⟩ := cvt_up_fin hpp hb t E' M'
    rw [hc1, hc2]
    have hx := unitsOf_isRepr f (E := E.val) M.isLt
    have hy := unitsOf_isRepr f (E := E'.val) M'.isLt
    simp only [add, hu1, hu2]
    generalize unitsOf f E.val M.val = u1 at hx ⊢
    generalize unitsOf f E'.val M'.val = u2 at hy ⊢
    have ev : sval s (u1 * 2 ^ (g.qneg - f.qneg)) + sval t (u2 * 2 ^ (g.qneg - f.qneg)) =
        (sval s u1 + sval t u2) * ((2 ^ (g.qneg - f.qneg) : Nat) : Int) := by
      rw [Int.add_mul]
      cases s <;> cases t <;> simp only [sval, ite_true, ite_false, Bool.false_eq_true,
        Int.natCast_mul, Int.neg_mul]
    rw [ev]
    have hA : (sval s u1 + sval t u2).natAbs = u1 + u2 ∨ (sval s u1 + sval t u2).natAbs + u2 = u1 ∨
        (sval s u1 + sval t u2).natAbs + u1 = u2 := by
      cases s <;> cases t <;> simp only [sval, ite_true, ite_false, Bool.false_eq_true] <;> omega
    generalize sval s u1 + sval t u2 = v at hA ⊢
    have hK : 0 < 2 ^ (g.qneg - f.qneg) := Nat.two_pow_pos _
    generalize hKd : 2 ^ (g.qneg - f.qneg) = K at hK
    by_cases hv0 : v = 0
    · subst hv0
      simp only [Int.zero_mul, ite_true]
      exact cvt_zero hq _
    · have h1 : v * (K : Int) ≠ 0 := by
        intro h; rcases Int.mul_eq_zero.mp h with h | h
        · exact hv0 h
        · omega
      have h2 : decide (v * (K : Int) < 0) = decide (v < 0) := by
        by_cases hv : v < 0
        · have : v * (K : Int) < 0 := Int.mul_neg_of_neg_of_pos hv (by omega)
          simp [hv, this]
        · have : ¬ v * (K : Int) < 0 := by
            have : 0 ≤ v := by omega
            have := Int.mul_nonneg this (by omega : (0 : Int) ≤ K)
            omega
          simp [hv, this]
      have h3 : (v * (K : Int)).natAbs = v.natAbs * K := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [if_neg h1, if_neg hv0, h2, h3]
      subst hKd
      rw [cvt_round hq, roundUnits_mul_pow_zero]
      have hdr := roundUnits_double_sum f g hp hx hy hA
      have hWr : IsRepr g (roundUnits g v.natAbs 0 * 2 ^ (g.qneg - f.qneg)) :=
        (roundUnits_isRepr g _ 0).mul_two_pow _
      split
      · rename_i hov
        have h4 := overflow_transfer hpp hb hWr hov
        rw [roundUnits_mul_pow, hdr] at h4
        show FP.inf _ = mkFin f _ (roundUnits f v.natAbs 0)
        rw [mkFin_overflow h4]
      · show mkFin f _ (roundUnits f (roundUnits g v.natAbs 0 * 2 ^ (g.qneg - f.qneg))
            (g.qneg - f.qneg)) = mkFin f _ (roundUnits f v.natAbs 0)
        rw [roundUnits_mul_pow, hdr]
  case nan.fin =>
    obtain ⟨E2, M2, hc, -⟩ := cvt_up_fin hpp hb t E' M'; rw [hc]; rfl
  case inf.fin =>
    obtain ⟨E2, M2, hc, -⟩ := cvt_up_fin hpp hb t E' M'; rw [hc]; rfl
  case fin.nan =>
    obtain ⟨E2, M2, hc, -⟩ := cvt_up_fin hpp hb s E M; rw [hc]; rfl
  case fin.inf =>
    obtain ⟨E2, M2, hc, -⟩ := cvt_up_fin hpp hb s E M; rw [hc]; rfl
  case inf.inf => cases s <;> cases t <;> rfl
  all_goals rfl

/-- Multiplication computed in a wider format `g` and rounded to `f` equals
direct multiplication in `f` when `g` has at least `2p` bits of precision, at
least the exponent range of `f`, and a smallest subnormal at most the square
of that of `f` (`2 * qneg f ≤ qneg g`). -/
theorem mulVia_eq_mul_of_two_mul_le_and_qneg_bias_le (f g : Fmt) (hp : 2 * f.p ≤ g.p)
    (hq : 2 * f.qneg ≤ g.qneg) (hb : f.bias ≤ g.bias) (x y : FP f) : mulVia g x y = mul x y := by
  have hpp : f.p ≤ g.p := by have := f.two_le_p; omega
  have hq1 : 1 ≤ f.qneg := by
    unfold Fmt.qneg; have := f.two_le_p; have := f.one_le_bias; omega
  have hqq : f.qneg < g.qneg := by omega
  unfold mulVia
  rcases x with _ | s | ⟨s, E, M⟩ <;> rcases y with _ | t | ⟨t, E', M'⟩
  case fin.fin =>
    obtain ⟨E2, M2, hc1, hu1⟩ := cvt_up_fin hpp hb s E M
    obtain ⟨E2', M2', hc2, hu2⟩ := cvt_up_fin hpp hb t E' M'
    rw [hc1, hc2]
    have hx := unitsOf_isRepr f (E := E.val) M.isLt
    have hy := unitsOf_isRepr f (E := E'.val) M'.isLt
    simp only [mul, hu1, hu2]
    generalize unitsOf f E.val M.val = u1 at hx ⊢
    generalize unitsOf f E'.val M'.val = u2 at hy ⊢
    have e : u1 * 2 ^ (g.qneg - f.qneg) * (u2 * 2 ^ (g.qneg - f.qneg)) =
        u1 * u2 * 2 ^ (g.qneg - 2 * f.qneg) * 2 ^ g.qneg := by
      have : 2 ^ (g.qneg - f.qneg) * 2 ^ (g.qneg - f.qneg) =
          2 ^ (g.qneg - 2 * f.qneg) * 2 ^ g.qneg := by
        rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
      calc u1 * 2 ^ (g.qneg - f.qneg) * (u2 * 2 ^ (g.qneg - f.qneg))
          = u1 * u2 * (2 ^ (g.qneg - f.qneg) * 2 ^ (g.qneg - f.qneg)) := by
            simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
        _ = u1 * u2 * (2 ^ (g.qneg - 2 * f.qneg) * 2 ^ g.qneg) := by rw [this]
        _ = u1 * u2 * 2 ^ (g.qneg - 2 * f.qneg) * 2 ^ g.qneg := by simp only [Nat.mul_assoc]
    rw [e]
    have hr : IsRepr g (u1 * u2 * 2 ^ (g.qneg - 2 * f.qneg)) := by
      obtain ⟨X, a, hX, rfl⟩ := hx
      obtain ⟨Y, b, hY, rfl⟩ := hy
      refine ⟨X * Y, a + b + (g.qneg - 2 * f.qneg), ?_, ?_⟩
      · have hP := Nat.two_pow_pos f.p
        calc X * Y ≤ (2 ^ f.p - 1) * 2 ^ f.p := Nat.mul_le_mul (by omega) (Nat.le_of_lt hY)
          _ < 2 ^ f.p * 2 ^ f.p := Nat.mul_lt_mul_of_pos_right (by omega) hP
          _ = 2 ^ (f.p + f.p) := (Nat.pow_add 2 f.p f.p).symm
          _ ≤ 2 ^ g.p := two_pow_le_two_pow (by omega)
      · simp only [Nat.pow_add, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    have hround : round g (s != t) (u1 * u2 * 2 ^ (g.qneg - 2 * f.qneg) * 2 ^ g.qneg) g.qneg =
        round g (s != t) (u1 * u2 * 2 ^ (g.qneg - 2 * f.qneg)) 0 := by
      unfold round; rw [roundUnits_mul_pow]
    rw [hround, cvt_round hqq, roundUnits_repr0 hr]
    have hscale : roundUnits f (u1 * u2 * 2 ^ (g.qneg - 2 * f.qneg)) (g.qneg - f.qneg) =
        roundUnits f (u1 * u2) f.qneg := by
      rw [show g.qneg - f.qneg = f.qneg + (g.qneg - 2 * f.qneg) by omega, roundUnits_mul_pow_add]
    split
    · rename_i hov
      have h4 := overflow_transfer hpp hb hr hov
      rw [hscale] at h4
      show FP.inf _ = mkFin f _ (roundUnits f (u1 * u2) f.qneg)
      rw [mkFin_overflow h4]
    · show mkFin f _ (roundUnits f (u1 * u2 * 2 ^ (g.qneg - 2 * f.qneg)) (g.qneg - f.qneg)) =
          mkFin f _ (roundUnits f (u1 * u2) f.qneg)
      rw [hscale]
  case inf.fin =>
    obtain ⟨E2, M2, hc, hu⟩ := cvt_up_fin hpp hb t E' M'
    rw [hc]
    by_cases h0 : unitsOf f E'.val M'.val = 0
    · simp [mul, hu, h0, cvt]
    · have : unitsOf f E'.val M'.val * 2 ^ (g.qneg - f.qneg) ≠ 0 :=
        Nat.mul_ne_zero h0 (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
      simp [mul, hu, h0, this, cvt]
  case fin.inf =>
    obtain ⟨E2, M2, hc, hu⟩ := cvt_up_fin hpp hb s E M
    rw [hc]
    by_cases h0 : unitsOf f E.val M.val = 0
    · simp [mul, hu, h0, cvt]
    · have : unitsOf f E.val M.val * 2 ^ (g.qneg - f.qneg) ≠ 0 :=
        Nat.mul_ne_zero h0 (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
      simp [mul, hu, h0, this, cvt]
  case nan.fin =>
    obtain ⟨E2, M2, hc, -⟩ := cvt_up_fin hpp hb t E' M'; rw [hc]; rfl
  case fin.nan =>
    obtain ⟨E2, M2, hc, -⟩ := cvt_up_fin hpp hb s E M; rw [hc]; rfl
  all_goals rfl

/-! ### Comparisons, `min`/`max` -/

theorem decide_lt_eq_not_decide_le (x y : Int) : decide (x < y) = !decide (y ≤ x) := by
  by_cases h : x < y
  · have h2 : ¬ (y ≤ x) := by omega
    simp [h, h2]
  · have h2 : y ≤ x := by omega
    simp [h, h2]

/-- `a < b` equals `¬ (a >= b)` exactly when neither operand is NaN. -/
theorem lt_eq_not_ge_iff (a b : FP f) :
    lt a b = !(ge a b) ↔ (a.isNaN = false ∧ b.isNaN = false) := by
  cases a <;> cases b <;> simp [lt, ge, le, FP.isNaN, decide_lt_eq_not_decide_le]

theorem key_of_isZero {x : FP f} (h : x.isZero = true) : key x = 0 := by
  rw [eq_zero_of_isZero h]; simp [key, zero, unitsOf, sval_zero]

/-- `min`/`max` defined by `<` commute on `a`, `b` exactly when it is not the
case that exactly one operand is NaN or the operands are `+0` and `-0`. -/
theorem minLt_maxLt_comm_iff (a b : FP f) :
    (minLt a b = minLt b a ↔ ¬ OneNaNOrOppositeZeros a b) ∧
    (maxLt a b = maxLt b a ↔ ¬ OneNaNOrOppositeZeros a b) := by
  unfold minLt maxLt OneNaNOrOppositeZeros lt
  cases ha : a.isNaN <;> cases hb : b.isNaN
  · simp only [Bool.not_false, Bool.true_and, decide_eq_true_eq, ne_eq, not_true_eq_false,
      false_or, Bool.false_eq_true, not_false_eq_true]
    rcases Int.lt_trichotomy (key a) (key b) with hlt | heq | hgt
    · have h2 : ¬ key b < key a := by omega
      have hz : ¬ (a.isZero = true ∧ b.isZero = true ∧ ¬ a = b) := by
        rintro ⟨za, zb, -⟩; rw [key_of_isZero za, key_of_isZero zb] at hlt; omega
      simp [hlt, h2, hz]
    · have h1 : ¬ key a < key b := by omega
      have h2 : ¬ key b < key a := by omega
      simp only [h1, h2, ite_false]
      rcases key_inj ha hb heq with he | ⟨za, zb⟩
      · subst he; simp
      · by_cases hab : a = b
        · subst hab; simp
        · have : ¬ b = a := fun h => hab h.symm
          simp [za, zb, hab, this]
    · have h1 : ¬ key a < key b := by omega
      have hz : ¬ (a.isZero = true ∧ b.isZero = true ∧ ¬ a = b) := by
        rintro ⟨za, zb, -⟩; rw [key_of_isZero za, key_of_isZero zb] at hgt; omega
      simp [hgt, h1, hz]
  · have hne : a ≠ b := by intro h; subst h; rw [ha] at hb; exact absurd hb (by simp)
    have hne' : b ≠ a := fun h => hne h.symm
    simp [hne, hne']
  · have hne : a ≠ b := by intro h; subst h; rw [ha] at hb; exact absurd hb (by simp)
    have hne' : b ≠ a := fun h => hne h.symm
    simp [hne, hne']
  · have hab : a = b := by
      cases a <;> cases b <;> simp_all [FP.isNaN]
    subst hab; simp

theorem minimum_comm (a b : FP f) : minimum a b = minimum b a := by
  unfold minimum
  cases ha : a.isNaN <;> cases hb : b.isNaN <;> simp
  by_cases h1 : totalKey a ≤ totalKey b <;> by_cases h2 : totalKey b ≤ totalKey a <;>
    simp [h1, h2]
  · first
      | exact totalKey_inj ha hb (by omega)
      | exact (totalKey_inj ha hb (by omega)).symm
      | exact totalKey_inj hb ha (by omega)
      | exact (totalKey_inj hb ha (by omega)).symm
  · omega

theorem maximum_comm (a b : FP f) : maximum a b = maximum b a := by
  unfold maximum
  cases ha : a.isNaN <;> cases hb : b.isNaN <;> simp
  by_cases h1 : totalKey a ≤ totalKey b <;> by_cases h2 : totalKey b ≤ totalKey a <;>
    simp [h1, h2]
  · first
      | exact totalKey_inj ha hb (by omega)
      | exact (totalKey_inj ha hb (by omega)).symm
      | exact totalKey_inj hb ha (by omega)
      | exact (totalKey_inj hb ha (by omega)).symm
  · omega

theorem minimum_assoc (a b c : FP f) : minimum (minimum a b) c = minimum a (minimum b c) := by
  by_cases ha : a.isNaN = true
  · rw [eq_nan_of_isNaN ha]; simp [minimum, FP.isNaN]
  by_cases hb : b.isNaN = true
  · rw [eq_nan_of_isNaN hb]; simp [minimum, FP.isNaN]
  by_cases hc : c.isNaN = true
  · rw [eq_nan_of_isNaN hc]; simp [minimum, FP.isNaN]
  simp only [Bool.not_eq_true] at ha hb hc
  by_cases h1 : totalKey a ≤ totalKey b <;> by_cases h2 : totalKey b ≤ totalKey c <;>
    by_cases h3 : totalKey a ≤ totalKey c <;> simp [minimum, ha, hb, hc, h1, h2, h3] <;> omega

theorem maximum_assoc (a b c : FP f) : maximum (maximum a b) c = maximum a (maximum b c) := by
  by_cases ha : a.isNaN = true
  · rw [eq_nan_of_isNaN ha]; simp [maximum, FP.isNaN]
  by_cases hb : b.isNaN = true
  · rw [eq_nan_of_isNaN hb]; simp [maximum, FP.isNaN]
  by_cases hc : c.isNaN = true
  · rw [eq_nan_of_isNaN hc]; simp [maximum, FP.isNaN]
  simp only [Bool.not_eq_true] at ha hb hc
  by_cases h1 : totalKey b ≤ totalKey a <;> by_cases h2 : totalKey c ≤ totalKey b <;>
    by_cases h3 : totalKey c ≤ totalKey a <;> simp [maximum, ha, hb, hc, h1, h2, h3] <;> omega

/-- IEEE 754-2019 `minimum` and `maximum` are commutative and associative up
to identity of encodings, on all inputs. -/
theorem minimum_maximum_comm_assoc (a b c : FP f) :
    minimum a b = minimum b a ∧ maximum a b = maximum b a ∧
    minimum (minimum a b) c = minimum a (minimum b c) ∧
    maximum (maximum a b) c = maximum a (maximum b c) :=
  ⟨minimum_comm a b, maximum_comm a b, minimum_assoc a b c, maximum_assoc a b c⟩

/-! ### Flag table: sufficiency in every format -/

theorem mul_negOne_right (x : FP f) : mul x (one f).neg = x.neg := by
  obtain ⟨E1, M1, -, h1, hu1⟩ := one_fields f
  rw [← h1]
  cases x with
  | nan => rfl
  | inf s =>
    show (if unitsOf f E1.val M1.val = 0 then FP.nan else FP.inf (s != true)) = _
    rw [hu1]; simp [Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _), FP.neg]
  | fin s E M =>
    show round f (s != true) (unitsOf f E.val M.val * unitsOf f E1.val M1.val) f.qneg = _
    rw [hu1, round_repr (unitsOf_isRepr f M.isLt), bne_true', ← neg_mkFin, mkFin_fields]

theorem mul_two_eq_add_self (x : FP f) : mul x (ofDyadic f false 1 1) = add x x := by
  obtain ⟨E2, M2, h2, hu2⟩ := two_fields f
  rw [h2]
  cases x with
  | nan => rfl
  | inf s =>
    show (if unitsOf f E2.val M2.val = 0 then FP.nan else FP.inf (s != false)) =
      (if s = s then FP.inf s else FP.nan)
    rw [hu2]; simp [Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)]
  | fin s E M =>
    show round f (s != false) (unitsOf f E.val M.val * unitsOf f E2.val M2.val) f.qneg =
      (let v := sval s (unitsOf f E.val M.val) + sval s (unitsOf f E.val M.val)
       if v = 0 then zero f (s && s) else round f (decide (v < 0)) v.natAbs 0)
    rw [hu2]; dsimp only
    have hsum : sval s (unitsOf f E.val M.val) + sval s (unitsOf f E.val M.val) =
        sval s (2 * unitsOf f E.val M.val) := by cases s <;> simp [sval] <;> omega
    simp only [hsum, sval_eq_zero_iff, sval_natAbs, Bool.and_self, bne_false']
    have hm : unitsOf f E.val M.val * 2 ^ (f.qneg + 1) =
        (2 * unitsOf f E.val M.val) * 2 ^ f.qneg := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ f.qneg) 2, ← Nat.mul_assoc, Nat.mul_comm _ 2]
    unfold round
    rw [hm, roundUnits_mul_pow]
    by_cases hu : unitsOf f E.val M.val = 0
    · simp [hu, roundUnits_zero, mkFin_zero]
    · have h2u : ¬ 2 * unitsOf f E.val M.val = 0 := by omega
      simp [hu, h2u, decide_sval_neg (by omega : 0 < 2 * unitsOf f E.val M.val)]

/-- Each table rewrite is valid modulo its flag set, in every format (with
`ValidMod` quantifying over the forms generated by `Expr.variants`). -/
theorem flagTable_sufficient (f : Fmt) :
    Valid (rwAddNegZero f) ∧ ValidMod fNsz (rwAddPosZero f) ∧ Valid (rwMulOne f) ∧
    Valid (rwMulNegOne f) ∧ Valid (rwMulTwo f) ∧ ValidMod fNnan (rwSubSelf f) ∧
    ValidMod fNnanNsz (rwMulPosZero f) ∧ ValidMod fNsz (rwPosZeroSub f) ∧
    Valid (rwNegZeroSub f) ∧ ValidMod fNsz (rwNegSub f) ∧ Valid (rwAddComm f) ∧
    ValidMod fReassoc (rwAddAssoc f) ∧ ValidMod fReassoc (rwMulAssoc f) ∧
    ValidMod fContract (rwContract f) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rwAddAssoc_validMod_reassoc f,
    rwMulAssoc_validMod_reassoc f, rwContract_validMod_contract f⟩
  · rw [valid_iff_forall_eq]; intro env
    exact (add_negZero_right (env 0)).symm
  · rw [validMod_iff_of_noPerm fNsz rfl rfl]; intro env _
    show EqNsz (env 0) (add (env 0) (posZero f))
    exact eqNsz_symm (add_posZero_right_eq_iff_and_eqNsz (env 0)).2
  · rw [valid_iff_forall_eq]; intro env
    exact (mul_one_right (env 0)).symm
  · rw [valid_iff_forall_eq]; intro env
    exact (mul_negOne_right (env 0)).symm
  · rw [valid_iff_forall_eq]; intro env
    exact (mul_two_eq_add_self (env 0)).symm
  · rw [validMod_iff_of_noPerm fNnan rfl rfl]; intro env hadm
    show posZero f = sub (env 0) (env 0)
    have hn := (hadm (sub (env 0) (env 0))
      (by simp [rwSubSelf, Expr.nodeVals, Expr.eval])).1 rfl
    have hfin : (env 0).isFinite = true := by
      cases hx : (env 0).isFinite
      · rw [((sub_self_eq_posZero_iff_and_eq_nan_iff (env 0)).2.mpr hx)] at hn
        simp [FP.isNaN] at hn
      · rfl
    exact ((sub_self_eq_posZero_iff_and_eq_nan_iff (env 0)).1.mpr hfin).symm
  · rw [validMod_iff_of_noPerm fNnanNsz rfl rfl]; intro env hadm
    show EqNsz (posZero f) (mul (env 0) (posZero f))
    have hn := (hadm (mul (env 0) (posZero f))
      (by simp [rwMulPosZero, Expr.nodeVals, Expr.eval])).1 rfl
    cases hx : env 0 with
    | nan => rw [hx] at hn; simp [mul, FP.isNaN] at hn
    | inf s => rw [hx] at hn; simp [mul, posZero, zero, unitsOf, FP.isNaN] at hn
    | fin s E M => rw [mul_fin_posZero]; exact eqNsz_zeros _ _
  · rw [validMod_iff_of_noPerm fNsz rfl rfl]; intro env _
    show EqNsz (env 0).neg (sub (posZero f) (env 0))
    rw [sub, add_comm']
    exact eqNsz_symm (add_posZero_right_eq_iff_and_eqNsz (env 0).neg).2
  · rw [valid_iff_forall_eq]; intro env
    show (env 0).neg = sub (negZero f) (env 0)
    rw [sub, add_comm', add_negZero_right]
  · rw [validMod_iff_of_noPerm fNsz rfl rfl]; intro env _
    show EqNsz (sub (env 1) (env 0)) (sub (env 0) (env 1)).neg
    have := add_neg_neg_eqNsz (env 0) (env 1).neg
    rw [neg_neg] at this
    rw [sub, sub, add_comm' (env 1)]
    exact this
  · rw [valid_iff_forall_eq]; intro env
    exact add_comm' _ _

end Toy.Float
