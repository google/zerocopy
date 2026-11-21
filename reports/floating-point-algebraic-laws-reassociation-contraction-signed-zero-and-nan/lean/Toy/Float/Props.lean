/-
Toy.Float.Props
===============

Fully proved value-level lemmas used by the general statements in
`Toy.Float.Statements`: signed magnitudes, zeros, the special constants
`1`, `-1`, `2` and the largest finite value, the sign rule for sums, order
keys, negation, and the permitted forms of expressions without permissions.
Nothing here is a result card; these are auxiliary lemmas.
-/
import Toy.Float.Arith
import Toy.Float.Rewrites

namespace Toy.Float

variable {f : Fmt}

/-! ### Signed magnitudes -/

theorem sval_natAbs (s : Bool) (u : Nat) : (sval s u).natAbs = u := by
  cases s <;> simp [sval]

theorem decide_sval_neg {u : Nat} (hu : 0 < u) (s : Bool) : decide (sval s u < 0) = s := by
  cases s <;> simp [sval] <;> omega

theorem sval_eq_zero_iff (s : Bool) (u : Nat) : sval s u = 0 ↔ u = 0 := by
  cases s <;> simp [sval]

theorem sval_not (s : Bool) (u : Nat) : sval (!s) u = - sval s u := by
  cases s <;> simp [sval]

theorem sval_zero (s : Bool) : sval s 0 = 0 := by cases s <;> simp [sval]

/-! ### Zeros -/

theorem fin_eq_zero_of_units {s : Bool} {E : Fin f.expCount} {M : Fin f.fracCount}
    (h : unitsOf f E.val M.val = 0) : (FP.fin s E M : FP f) = zero f s := by
  rw [unitsOf_eq_zero_iff] at h
  simp only [zero, FP.fin.injEq, true_and]
  exact ⟨Fin.ext h.1, Fin.ext h.2⟩

theorem mkFin_zero (s : Bool) : mkFin f s 0 = zero f s := by
  obtain ⟨E, M, h, hu⟩ := mkFin_repr (f := f) (n := 0) ⟨0, 0, Nat.two_pow_pos _, rfl⟩ (Nat.zero_le _)
  rw [h s]; exact fin_eq_zero_of_units hu

theorem zero_units (s : Bool) : (zero f s).units = 0 := by
  simp [zero, FP.units, unitsOf]

theorem zero_ne_zero_iff (s t : Bool) : zero f s = zero f t ↔ s = t := by
  simp [zero]

theorem isZero_fin_iff (s : Bool) (E : Fin f.expCount) (M : Fin f.fracCount) :
    (FP.fin s E M : FP f).isZero = true ↔ unitsOf f E.val M.val = 0 := by
  rw [unitsOf_eq_zero_iff]; simp [FP.isZero]

theorem eq_zero_of_isZero {x : FP f} (h : x.isZero = true) : x = zero f x.signBit := by
  cases x with
  | nan => simp [FP.isZero] at h
  | inf s => simp [FP.isZero] at h
  | fin s E M =>
    rw [isZero_fin_iff] at h
    exact fin_eq_zero_of_units h

theorem isZero_zero (s : Bool) : (zero f s).isZero = true := by simp [zero, FP.isZero]

/-! ### Sums with a zero -/

/-- `x + (±0)` for finite `x`: `x` itself unless `x` is a zero, in which case
the sum-sign rule applies. -/
theorem add_fin_zero (s : Bool) (E : Fin f.expCount) (M : Fin f.fracCount) (t : Bool) :
    add (.fin s E M) (zero f t) =
      if unitsOf f E.val M.val = 0 then zero f (s && t) else .fin s E M := by
  show (let v := sval s (unitsOf f E.val M.val) + sval t (unitsOf f 0 0)
    if v = 0 then zero f (s && t) else round f (decide (v < 0)) v.natAbs 0) = _
  simp only [unitsOf_zero_left, sval_zero, Int.add_zero, sval_eq_zero_iff]
  by_cases hu : unitsOf f E.val M.val = 0
  · simp [hu]
  · simp only [hu, ite_false, sval_natAbs, decide_sval_neg (Nat.pos_of_ne_zero hu)]
    have := round_units (FP.fin s E M) rfl 0
    simpa [FP.units, FP.signBit] using this

/-- `(±0) + y = y + (±0)`. -/
theorem add_comm' (x y : FP f) : add x y = add y x := by
  cases x <;> cases y <;> simp [add]
  · rename_i s t; cases s <;> cases t <;> rfl
  · rw [Int.add_comm, Bool.and_comm]

/-! ### Special constants -/

theorem pow_qneg_le_maxUnits (f : Fmt) : 2 ^ (f.qneg + 1) ≤ f.maxUnits := by
  rw [f.maxUnits_eq, f.two_pow_p_eq]
  have hb := f.one_le_bias
  have hF := f.two_le_fracCount
  have hq : 2 ^ (f.qneg + 1) = f.fracCount * 2 ^ f.bias := by
    unfold Fmt.fracCount Fmt.qneg; rw [← Nat.pow_add]; congr 1; have := f.two_le_p; omega
  rw [hq]
  apply Nat.mul_le_mul (by omega) (two_pow_le_two_pow (by omega))

theorem ofDyadic_pos (f : Fmt) (m : Nat) (k : Int) (hk : 0 ≤ k) :
    ofDyadic f false m k = round f false (m * 2 ^ (k.toNat + f.qneg)) 0 := by
  unfold ofDyadic
  have h1 : 0 ≤ k + (f.qneg : Int) := by omega
  have h2 : (k + (f.qneg : Int)).toNat = k.toNat + f.qneg := by omega
  simp [h1, h2]

/-- `1.0` is finite with magnitude `2^qneg` units. -/
theorem one_fields (f : Fmt) : ∃ E M, one f = .fin false E M ∧ (FP.fin true E M : FP f) = (one f).neg ∧
    unitsOf f E.val M.val = 2 ^ f.qneg := by
  have hle : 2 ^ f.qneg ≤ f.maxUnits :=
    Nat.le_trans (two_pow_le_two_pow (Nat.le_succ _)) (pow_qneg_le_maxUnits f)
  obtain ⟨E, M, h, hu⟩ := mkFin_repr (isRepr_two_pow f f.qneg) hle
  have hone : one f = mkFin f false (2 ^ f.qneg) := by
    unfold one; rw [ofDyadic_pos f 1 0 (by omega)]
    simp only [Int.toNat_zero, Nat.zero_add, Nat.one_mul, round]
    rw [roundUnits_repr0 (isRepr_two_pow f f.qneg)]
  refine ⟨E, M, by rw [hone, h], by rw [hone, h]; rfl, hu⟩

/-- `2.0` is finite with magnitude `2^(qneg + 1)` units. -/
theorem two_fields (f : Fmt) : ∃ E M, ofDyadic f false 1 1 = .fin false E M ∧
    unitsOf f E.val M.val = 2 ^ (f.qneg + 1) := by
  obtain ⟨E, M, h, hu⟩ := mkFin_repr (isRepr_two_pow f (f.qneg + 1)) (pow_qneg_le_maxUnits f)
  refine ⟨E, M, ?_, hu⟩
  rw [ofDyadic_pos f 1 1 (by omega)]
  simp only [Nat.one_mul, round, show (1 : Int).toNat = 1 from rfl, Nat.add_comm 1 f.qneg]
  rw [roundUnits_repr0 (isRepr_two_pow f _), h]

/-- The largest finite value has magnitude `maxUnits` units. -/
theorem maxFinite_fields (f : Fmt) : ∃ E M, (∀ s, maxFinite f s = .fin s E M) ∧
    unitsOf f E.val M.val = f.maxUnits :=
  mkFin_repr f.maxUnits_isRepr (Nat.le_refl _)

theorem maxUnits_pos (f : Fmt) : 0 < f.maxUnits := by
  have := f.fracCount_le_maxUnits; have := f.fracCount_pos; omega

/-! ### The sign rule for sums -/

theorem add_eq_negZero_iff (u w : FP f) :
    add u w = negZero f ↔ u = negZero f ∧ w = negZero f := by
  cases u with
  | nan => simp [add, negZero, zero]
  | inf s =>
    cases w with
    | nan => simp [add, negZero, zero]
    | inf t => by_cases h : s = t <;> simp [add, h, negZero, zero]
    | fin t E M => simp [add, negZero, zero]
  | fin s E M =>
    cases w with
    | nan => simp [add, negZero, zero]
    | inf t => simp [add, negZero, zero]
    | fin t E' M' =>
      show (let v := sval s (unitsOf f E.val M.val) + sval t (unitsOf f E'.val M'.val)
        if v = 0 then zero f (s && t) else round f (decide (v < 0)) v.natAbs 0) = _ ↔ _
      dsimp only
      have hz1 : (FP.fin s E M : FP f) = negZero f ↔ s = true ∧ unitsOf f E.val M.val = 0 := by
        rw [unitsOf_eq_zero_iff]; simp [negZero, zero, Fin.ext_iff]
      have hz2 : (FP.fin t E' M' : FP f) = negZero f ↔ t = true ∧ unitsOf f E'.val M'.val = 0 := by
        rw [unitsOf_eq_zero_iff]; simp [negZero, zero, Fin.ext_iff]
      rw [hz1, hz2]
      by_cases hv : sval s (unitsOf f E.val M.val) + sval t (unitsOf f E'.val M'.val) = 0
      · simp only [hv, ite_true, negZero, zero_ne_zero_iff, Bool.and_eq_true]
        constructor
        · rintro ⟨rfl, rfl⟩
          simp only [sval, ite_true] at hv
          exact ⟨⟨rfl, by omega⟩, ⟨rfl, by omega⟩⟩
        · rintro ⟨⟨rfl, _⟩, ⟨rfl, _⟩⟩; exact ⟨rfl, rfl⟩
      · simp only [hv, ite_false]
        constructor
        · intro h; exact absurd h (round_ne_zero (by omega) _ _)
        · rintro ⟨⟨rfl, h1⟩, ⟨rfl, h2⟩⟩; simp [h1, h2, sval] at hv

/-! ### Negation -/

@[simp] theorem neg_neg (x : FP f) : x.neg.neg = x := by
  cases x <;> simp [FP.neg]

theorem neg_zero (s : Bool) : (zero f s).neg = zero f (!s) := rfl

theorem zeroBlind_zero (s : Bool) : zeroBlind (zero f s) = posZero f := by
  simp [zeroBlind, isZero_zero]

theorem eqNsz_zeros (s t : Bool) : EqNsz (zero f s) (zero f t) := by
  unfold EqNsz; rw [zeroBlind_zero, zeroBlind_zero]

theorem eqNsz_refl (x : FP f) : EqNsz x x := rfl

theorem eqNsz_symm {x y : FP f} (h : EqNsz x y) : EqNsz y x := h.symm

/-- Negation commutes with addition up to the sign of a zero result. -/
theorem add_neg_neg_eqNsz (a b : FP f) : EqNsz (add a.neg b.neg) (add a b).neg := by
  cases a with
  | nan => exact eqNsz_refl _
  | inf s =>
    cases b with
    | nan => exact eqNsz_refl _
    | inf t => by_cases h : s = t <;> simp [add, FP.neg, h] <;> exact eqNsz_refl _
    | fin t E M => exact eqNsz_refl _
  | fin s E M =>
    cases b with
    | nan => exact eqNsz_refl _
    | inf t => exact eqNsz_refl _
    | fin t E' M' =>
      show EqNsz (let v := sval (!s) (unitsOf f E.val M.val) + sval (!t) (unitsOf f E'.val M'.val)
        if v = 0 then zero f (!s && !t) else round f (decide (v < 0)) v.natAbs 0)
        (let v := sval s (unitsOf f E.val M.val) + sval t (unitsOf f E'.val M'.val)
        if v = 0 then zero f (s && t) else round f (decide (v < 0)) v.natAbs 0).neg
      dsimp only
      rw [sval_not, sval_not]
      by_cases hv : sval s (unitsOf f E.val M.val) + sval t (unitsOf f E'.val M'.val) = 0
      · have hv' : -sval s (unitsOf f E.val M.val) + -sval t (unitsOf f E'.val M'.val) = 0 := by omega
        simp only [hv, hv', ite_true, neg_zero]
        exact eqNsz_zeros _ _
      · have hv' : ¬ (-sval s (unitsOf f E.val M.val) + -sval t (unitsOf f E'.val M'.val) = 0) := by
          omega
        simp only [hv, hv', ite_false, neg_round]
        have h1 : (-sval s (unitsOf f E.val M.val) + -sval t (unitsOf f E'.val M'.val)).natAbs =
            (sval s (unitsOf f E.val M.val) + sval t (unitsOf f E'.val M'.val)).natAbs := by omega
        have h2 : decide (-sval s (unitsOf f E.val M.val) + -sval t (unitsOf f E'.val M'.val) < 0) =
            !decide (sval s (unitsOf f E.val M.val) + sval t (unitsOf f E'.val M'.val) < 0) := by
          by_cases h : sval s (unitsOf f E.val M.val) + sval t (unitsOf f E'.val M'.val) < 0
          · simp [h]; omega
          · simp [h]; omega
        rw [h1, h2]; exact eqNsz_refl _

/-! ### Order keys -/

theorem key_fin_abs_le (s : Bool) (E : Fin f.expCount) (M : Fin f.fracCount) :
    (key (FP.fin s E M : FP f)).natAbs ≤ f.maxUnits := by
  simp only [key, sval_natAbs]; exact unitsOf_le_maxUnits f E.isLt M.isLt

/-- `key` is injective on non-NaN values, except that it identifies `+0` and
`-0`. -/
theorem key_inj {x y : FP f} (hx : x.isNaN = false) (hy : y.isNaN = false) (h : key x = key y) :
    x = y ∨ (x.isZero = true ∧ y.isZero = true) := by
  cases x with
  | nan => simp [FP.isNaN] at hx
  | inf s =>
    cases y with
    | nan => simp [FP.isNaN] at hy
    | inf t =>
      left; simp only [key] at h
      cases s <;> cases t <;> simp [sval] at h ⊢ <;> omega
    | fin t E M =>
      exfalso
      have h1 := key_fin_abs_le t E M
      have h2 : (key (FP.inf s : FP f)).natAbs = f.maxUnits + 1 := by simp [key, sval_natAbs]
      rw [h] at h2; omega
  | fin s E M =>
    cases y with
    | nan => simp [FP.isNaN] at hy
    | inf t =>
      exfalso
      have h1 := key_fin_abs_le s E M
      have h2 : (key (FP.inf t : FP f)).natAbs = f.maxUnits + 1 := by simp [key, sval_natAbs]
      rw [← h] at h2; omega
    | fin t E' M' =>
      simp only [key] at h
      by_cases hu : unitsOf f E.val M.val = 0
      · right
        rw [hu, sval_zero, eq_comm, sval_eq_zero_iff] at h
        exact ⟨(isZero_fin_iff _ _ _).mpr hu, (isZero_fin_iff _ _ _).mpr h⟩
      · left
        have hu' : unitsOf f E'.val M'.val = unitsOf f E.val M.val := by
          have := congrArg Int.natAbs h; simp only [sval_natAbs] at this; omega
        rw [hu'] at h
        have hst : s = t := by
          have hpos := Nat.pos_of_ne_zero hu
          cases s <;> cases t <;> simp [sval] at h ⊢ <;> omega
        subst hst
        rw [← mkFin_fields f s E M, ← mkFin_fields f s E' M', hu']

theorem totalKey_inj {x y : FP f} (hx : x.isNaN = false) (hy : y.isNaN = false)
    (h : totalKey x = totalKey y) : x = y := by
  unfold totalKey at h
  have hk : key x = key y := by split at h <;> split at h <;> omega
  rcases key_inj hx hy hk with h1 | ⟨h1, h2⟩
  · exact h1
  · have e1 := eq_zero_of_isZero h1
    have e2 := eq_zero_of_isZero h2
    generalize x.signBit = a at e1
    generalize y.signBit = b at e2
    subst e1; subst e2
    cases a <;> cases b <;> simp_all [posZero, key, zero, unitsOf, sval]

/-! ### Permitted forms without permissions -/

/-- If `S` grants neither `reassoc` nor `contract`, the only permitted form of
`e` is `e` itself. -/
theorem Expr.variants_eq_single {n : Nat} (S : Flags) (hr : S.reassoc = false)
    (hc : S.contract = false) (e : Expr f n) : e.variants S = [e] := by
  induction e with
  | var i => rfl
  | lit c => rfl
  | neg a ih => simp [Expr.variants, ih]
  | add a b iha ihb => simp [Expr.variants, iha, ihb, hr, hc]
  | sub a b iha ihb => simp [Expr.variants, iha, ihb, hc]
  | mul a b iha ihb => simp [Expr.variants, iha, ihb, hr]
  | fma a b c iha ihb ihc => simp [Expr.variants, iha, ihb, ihc]

/-- Validity modulo a flag set without permissions: on every admissible
input, the two sides are related by `Rel S`. -/
theorem validMod_iff_of_noPerm {n : Nat} (S : Flags) (hr : S.reassoc = false)
    (hc : S.contract = false) (r : Rewrite f n) :
    ValidMod S r ↔ ∀ env, Admissible S r.lhs env → Rel S (r.rhs.eval env) (r.lhs.eval env) := by
  unfold ValidMod
  simp [Expr.variants_eq_single S hr hc]

/-- If `rhs` is one of the forms of `lhs` permitted by `S`, then `lhs → rhs`
is valid modulo `S`. -/
theorem validMod_of_rhs_mem {n : Nat} {S : Flags} {r : Rewrite f n}
    (h : r.rhs ∈ r.lhs.variants S) : ValidMod S r := by
  intro env _
  refine ⟨r.rhs, h, ?_⟩
  unfold Rel
  split
  · rfl
  · rfl

theorem rwAddAssoc_validMod_reassoc (f : Fmt) : ValidMod fReassoc (rwAddAssoc f) :=
  validMod_of_rhs_mem (by simp [rwAddAssoc, Expr.variants, Expr.reassocAdd, fReassoc])

theorem rwMulAssoc_validMod_reassoc (f : Fmt) : ValidMod fReassoc (rwMulAssoc f) :=
  validMod_of_rhs_mem (by simp [rwMulAssoc, Expr.variants, Expr.reassocMul, fReassoc])

theorem rwContract_validMod_contract (f : Fmt) : ValidMod fContract (rwContract f) :=
  validMod_of_rhs_mem (by simp [rwContract, Expr.variants, Expr.contractAdd, fContract])

end Toy.Float

namespace Toy.Float

theorem bne_comm' (a b : Bool) : (a != b) = (b != a) := by cases a <;> cases b <;> rfl
theorem bne_false' (b : Bool) : (b != false) = b := by cases b <;> rfl
theorem bne_true' (b : Bool) : (b != true) = !b := by cases b <;> rfl

end Toy.Float

namespace Toy.Float

theorem eq_nan_of_isNaN {f : Fmt} {x : FP f} (h : x.isNaN = true) : x = .nan := by
  cases x <;> simp_all [FP.isNaN]

end Toy.Float

namespace Toy.Float

/-! ### Sums of nonnegative finite values, normality, and the tie of `2^(2p-1) + 2^(p-1)` -/

theorem add_fin_false {f : Fmt} (E : Fin f.expCount) (M : Fin f.fracCount) (E' : Fin f.expCount)
    (M' : Fin f.fracCount) :
    add (FP.fin false E M) (FP.fin false E' M') =
      mkFin f false (roundUnits f (unitsOf f E.val M.val + unitsOf f E'.val M'.val) 0) := by
  show (let v := sval false (unitsOf f E.val M.val) + sval false (unitsOf f E'.val M'.val)
    if v = 0 then zero f (false && false) else round f (decide (v < 0)) v.natAbs 0) = _
  dsimp only
  have hv : sval false (unitsOf f E.val M.val) + sval false (unitsOf f E'.val M'.val) =
      ((unitsOf f E.val M.val + unitsOf f E'.val M'.val : Nat) : Int) := by
    simp only [sval, Bool.false_eq_true, ite_false]; push_cast; rfl
  rw [hv]
  by_cases h0 : unitsOf f E.val M.val + unitsOf f E'.val M'.val = 0
  · rw [h0]; simp [roundUnits_zero, mkFin_zero]
  · rw [if_neg (by omega), Int.natAbs_natCast,
      show decide (((unitsOf f E.val M.val + unitsOf f E'.val M'.val : Nat) : Int) < 0) = false from
        decide_eq_false (Int.not_lt.mpr (Int.natCast_nonneg _))]
    rfl

theorem isNormal_mkFin {f : Fmt} {n : Nat} (hr : IsRepr f n) (h1 : f.fracCount ≤ n)
    (h2 : n ≤ f.maxUnits) (s : Bool) : (mkFin f s n).isNormal = true := by
  obtain ⟨E, M, h, hu⟩ := mkFin_repr hr h2
  rw [h s]
  simp only [FP.isNormal, bne_iff_ne, ne_eq]
  intro hE
  rw [hE, unitsOf_zero_left] at hu
  have := M.isLt; omega

theorem mkFin_ne {f : Fmt} {n n' : Nat} (hr : IsRepr f n) (hn : n ≤ f.maxUnits)
    (hr' : IsRepr f n') (hn' : n' ≤ f.maxUnits) (hne : n ≠ n') (s : Bool) :
    mkFin f s n ≠ mkFin f s n' := by
  obtain ⟨E, M, h, hu⟩ := mkFin_repr hr hn
  obtain ⟨E', M', h', hu'⟩ := mkFin_repr hr' hn'
  rw [h s, h' s]
  intro heq
  simp only [FP.fin.injEq, true_and] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact hne (hu.symm.trans hu')

theorem ofDyadic_false_eq_mkFin (f : Fmt) (k : Int) (j : Nat) (hj : k + (f.qneg : Int) = (j : Int)) :
    ofDyadic f false 1 k = mkFin f false (2 ^ j) := by
  unfold ofDyadic
  simp only [hj, Int.natCast_nonneg, ite_true, Int.toNat_natCast, Nat.one_mul, round]
  rw [roundUnits_repr0 (isRepr_two_pow f j)]

theorem roundUnits_tie (f : Fmt) :
    roundUnits f (f.fracCount * 2 ^ f.p + f.fracCount) 0 = f.fracCount * 2 ^ f.p := by
  have hp := f.two_le_p
  have hF := f.two_pow_p_eq
  have hFp := f.two_le_fracCount
  have hX : 0 < 2 ^ f.p := Nat.two_pow_pos _
  have hb : bitLen (f.fracCount * 2 ^ f.p + f.fracCount) = 2 * f.p := by
    have e1 : 2 ^ (2 * f.p - 1) = f.fracCount * 2 ^ f.p := by
      unfold Fmt.fracCount; rw [← Nat.pow_add]; congr 1; omega
    have e2 : 2 ^ (2 * f.p - 1 + 1) = 2 * (f.fracCount * 2 ^ f.p) := by
      rw [Nat.pow_succ, e1, Nat.mul_comm]
    rw [show 2 * f.p = 2 * f.p - 1 + 1 by omega]
    apply bitLen_eq
    · rw [e1]; omega
    · rw [e2]
      have : f.fracCount < f.fracCount * 2 ^ f.p := by
        have : 2 ≤ 2 ^ f.p := by omega
        calc f.fracCount = f.fracCount * 1 := (Nat.mul_one _).symm
          _ < f.fracCount * 2 ^ f.p := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      omega
  unfold roundUnits
  dsimp only
  simp only [Nat.pow_zero, Nat.div_one, hb, Nat.zero_add,
    show 2 * f.p - f.p = f.p by omega]
  unfold rneDiv
  dsimp only
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hX, Nat.add_mul_mod_self_right,
    Nat.div_eq_of_lt (by omega : f.fracCount < 2 ^ f.p), Nat.mod_eq_of_lt (by omega : f.fracCount < 2 ^ f.p),
    Nat.zero_add]
  have hpar : f.fracCount % 2 = 0 := by
    unfold Fmt.fracCount
    rw [show f.p - 1 = (f.p - 2) + 1 by omega, Nat.pow_succ]; simp
  rw [if_neg (by omega)]

end Toy.Float
