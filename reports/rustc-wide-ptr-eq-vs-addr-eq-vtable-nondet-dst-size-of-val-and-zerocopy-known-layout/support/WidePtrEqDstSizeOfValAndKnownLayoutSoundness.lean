/-
  Kernel-Checked Formalization of:
    1. Wide-Pointer Equality (`ptr::eq` vs `ptr::addr_eq`) & Non-Deterministic `DynMetadata` Vtable Sets
    2. Bit-Exact Equivalence of LLVM Custom-DST Rounding `(x + a - 1) &&& (-a)` and `roundUp`
    3. `rustc_codegen_ssa::size_of_val::size_and_align_of_dst` Two-Step vs Single-Round Equivalence
    4. `google/zerocopy` `KnownLayout` / `DstLayout` Checked Overflow Arithmetic & `isize::MAX` Soundness

  Lean Purity & TCB Contract:
    - Toolchain: `leanprover/lean4:v4.34.1` (core `Init` only, no Mathlib)
    - Every `def` is marked `noncomputable def` (0 plain `def`, 0 `noncomputable section`, 0 `partial def`)
    - Zero `deriving` clauses on any type (0 `._unsafe_rec` constants in the environment)
    - Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`
-/

namespace VerifiedRustc.WidePtrDstKnownLayout

/-! ## Section 1: Pure `Nat` Arithmetic, Divisibility, and Power-of-Two Alignment Helpers -/

noncomputable def isPow2 (a : Nat) : Prop :=
  ∃ k : Nat, a = 2 ^ k

noncomputable def paddingNeeded (x a : Nat) : Nat :=
  if a = 0 then 0
  else
    let r := x % a
    if r = 0 then 0 else a - r

noncomputable def alignToNat (x a : Nat) : Nat :=
  x + paddingNeeded x a

noncomputable def roundUpNat (x a : Nat) : Nat :=
  if a = 0 then x else ((x + a - 1) / a) * a

noncomputable def roundDownNat (x a : Nat) : Nat :=
  if a = 0 then 0 else (x / a) * a

noncomputable def isLeastAlignedGe (r x a : Nat) : Prop :=
  x ≤ r ∧ a ∣ r ∧ ∀ m : Nat, x ≤ m → a ∣ m → r ≤ m

theorem pow2_pos (k : Nat) : 0 < 2 ^ k := by
  exact Nat.pow_pos (by decide : 0 < 2)

theorem pow2_ne_zero (k : Nat) : 2 ^ k ≠ 0 := by
  exact Nat.ne_of_gt (pow2_pos k)

theorem isPow2_pos {a : Nat} (ha : isPow2 a) : 0 < a := by
  rcases ha with ⟨k, rfl⟩
  exact pow2_pos k

theorem pow2_dvd_pow2 {k m : Nat} (hkm : k ≤ m) : 2 ^ k ∣ 2 ^ m := by
  have hm : m = (m - k) + k := (Nat.sub_add_cancel hkm).symm
  rw [hm, Nat.pow_add]
  exact Nat.dvd_mul_left (2 ^ k) (2 ^ (m - k))

theorem pow2_le_of_le_exp {k m : Nat} (hkm : k ≤ m) : 2 ^ k ≤ 2 ^ m := by
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hkm

theorem pow2_lt_of_lt {m k : Nat} (hmk : m < k) : 2 ^ m < 2 ^ k := by
  have h1 : 2 ^ m < 2 ^ (m + 1) := by
    rw [Nat.pow_succ, Nat.mul_two]
    exact Nat.lt_add_of_pos_left (pow2_pos m)
  have h2 : 2 ^ (m + 1) ≤ 2 ^ k := pow2_le_of_le_exp hmk
  exact Nat.lt_of_lt_of_le h1 h2

theorem le_exp_of_pow2_le {k m : Nat} (h : 2 ^ k ≤ 2 ^ m) : k ≤ m := by
  cases Nat.lt_or_ge m k with
  | inl hmk =>
    have hlt : 2 ^ m < 2 ^ k := pow2_lt_of_lt hmk
    exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt h))
  | inr hkm => exact hkm

theorem min_pow2_eq_left_or_right {k1 k2 : Nat} :
    min (2 ^ k1) (2 ^ k2) = 2 ^ k1 ∨ min (2 ^ k1) (2 ^ k2) = 2 ^ k2 := by
  cases Nat.le_total (2 ^ k1) (2 ^ k2) with
  | inl h => exact Or.inl (Nat.min_eq_left h)
  | inr h => exact Or.inr (Nat.min_eq_right h)

theorem max_pow2_eq_left_or_right {k1 k2 : Nat} :
    max (2 ^ k1) (2 ^ k2) = 2 ^ k1 ∨ max (2 ^ k1) (2 ^ k2) = 2 ^ k2 := by
  cases Nat.le_total (2 ^ k1) (2 ^ k2) with
  | inl h => exact Or.inr (Nat.max_eq_right h)
  | inr h => exact Or.inl (Nat.max_eq_left h)

theorem min_pow2_isPow2 {a b : Nat} (ha : isPow2 a) (hb : isPow2 b) : isPow2 (min a b) := by
  rcases ha with ⟨k1, rfl⟩
  rcases hb with ⟨k2, rfl⟩
  cases Nat.le_total (2 ^ k1) (2 ^ k2) with
  | inl h =>
    rw [Nat.min_eq_left h]
    exact ⟨k1, rfl⟩
  | inr h =>
    rw [Nat.min_eq_right h]
    exact ⟨k2, rfl⟩

theorem max_pow2_isPow2 {a b : Nat} (ha : isPow2 a) (hb : isPow2 b) : isPow2 (max a b) := by
  rcases ha with ⟨k1, rfl⟩
  rcases hb with ⟨k2, rfl⟩
  cases Nat.le_total (2 ^ k1) (2 ^ k2) with
  | inl h =>
    rw [Nat.max_eq_right h]
    exact ⟨k2, rfl⟩
  | inr h =>
    rw [Nat.max_eq_left h]
    exact ⟨k1, rfl⟩

theorem min_pow2_dvd_left {a b : Nat} (ha : isPow2 a) (hb : isPow2 b) : min a b ∣ a := by
  rcases ha with ⟨k1, rfl⟩
  rcases hb with ⟨k2, rfl⟩
  cases Nat.le_total (2 ^ k1) (2 ^ k2) with
  | inl h =>
    rw [Nat.min_eq_left h]
    exact Nat.dvd_refl _
  | inr h =>
    rw [Nat.min_eq_right h]
    exact pow2_dvd_pow2 (le_exp_of_pow2_le h)

theorem min_pow2_dvd_right {a b : Nat} (ha : isPow2 a) (hb : isPow2 b) : min a b ∣ b := by
  rcases ha with ⟨k1, rfl⟩
  rcases hb with ⟨k2, rfl⟩
  cases Nat.le_total (2 ^ k1) (2 ^ k2) with
  | inl h =>
    rw [Nat.min_eq_left h]
    exact pow2_dvd_pow2 (le_exp_of_pow2_le h)
  | inr h =>
    rw [Nat.min_eq_right h]
    exact Nat.dvd_refl _

theorem left_dvd_max_pow2 {a b : Nat} (ha : isPow2 a) (hb : isPow2 b) : a ∣ max a b := by
  rcases ha with ⟨k1, rfl⟩
  rcases hb with ⟨k2, rfl⟩
  cases Nat.le_total (2 ^ k1) (2 ^ k2) with
  | inl h =>
    rw [Nat.max_eq_right h]
    exact pow2_dvd_pow2 (le_exp_of_pow2_le h)
  | inr h =>
    rw [Nat.max_eq_left h]
    exact Nat.dvd_refl _

theorem right_dvd_max_pow2 {a b : Nat} (ha : isPow2 a) (hb : isPow2 b) : b ∣ max a b := by
  rcases ha with ⟨k1, rfl⟩
  rcases hb with ⟨k2, rfl⟩
  cases Nat.le_total (2 ^ k1) (2 ^ k2) with
  | inl h =>
    rw [Nat.max_eq_right h]
    exact Nat.dvd_refl _
  | inr h =>
    rw [Nat.max_eq_left h]
    exact pow2_dvd_pow2 (le_exp_of_pow2_le h)

theorem roundDownNat_eq {x a : Nat} (ha : 0 < a) : roundDownNat x a = (x / a) * a := by
  simp [roundDownNat, Nat.ne_of_gt ha]

theorem roundUpNat_eq {x a : Nat} (ha : 0 < a) : roundUpNat x a = ((x + a - 1) / a) * a := by
  simp [roundUpNat, Nat.ne_of_gt ha]

theorem roundDownNat_le (x a : Nat) : roundDownNat x a ≤ x := by
  cases Nat.eq_zero_or_pos a with
  | inl ha0 =>
    subst ha0
    simp [roundDownNat]
  | inr hapos =>
    rw [roundDownNat_eq hapos, Nat.mul_comm]
    exact Nat.mul_div_le x a

theorem roundDownNat_dvd (x a : Nat) : a ∣ roundDownNat x a := by
  cases Nat.eq_zero_or_pos a with
  | inl ha0 =>
    subst ha0
    simp [roundDownNat]
  | inr hapos =>
    rw [roundDownNat_eq hapos]
    exact Nat.dvd_mul_left a (x / a)

theorem lt_roundDownNat_add {x a : Nat} (ha : 0 < a) : x < roundDownNat x a + a := by
  rw [roundDownNat_eq ha]
  have hdiv : a * (x / a) + x % a = x := Nat.div_add_mod x a
  have hmod : x % a < a := Nat.mod_lt x ha
  have hmul : a * (x / a) = (x / a) * a := Nat.mul_comm a (x / a)
  calc
    x = a * (x / a) + x % a := hdiv.symm
    _ = (x / a) * a + x % a := by rw [hmul]
    _ < (x / a) * a + a := Nat.add_lt_add_left hmod ((x / a) * a)

theorem roundDownNat_greatest {x a m : Nat} (ha : 0 < a) (hm_le : m ≤ x) (hdvd : a ∣ m) :
    m ≤ roundDownNat x a := by
  rcases hdvd with ⟨q, rfl⟩
  rw [roundDownNat_eq ha]
  have hq : q ≤ x / a := (Nat.le_div_iff_mul_le ha).2 (by rw [Nat.mul_comm]; exact hm_le)
  rw [Nat.mul_comm a q]
  exact Nat.mul_le_mul_right a hq

theorem roundDownNat_eq_of_dvd {x a : Nat} (hdvd : a ∣ x) : roundDownNat x a = x := by
  cases Nat.eq_zero_or_pos a with
  | inl ha0 =>
    subst ha0
    rcases hdvd with ⟨k, rfl⟩
    simp [roundDownNat]
  | inr hapos =>
    rcases hdvd with ⟨q, rfl⟩
    rw [roundDownNat_eq hapos, Nat.mul_comm a q, Nat.mul_div_cancel q hapos]

theorem roundUpNat_dvd (x : Nat) {a : Nat} (ha : 0 < a) : a ∣ roundUpNat x a := by
  rw [roundUpNat_eq ha]
  exact Nat.dvd_mul_left a ((x + a - 1) / a)

theorem roundUpNat_ge {x a : Nat} (ha : 0 < a) : x ≤ roundUpNat x a := by
  rw [roundUpNat_eq ha]
  have hsum_pos : 0 < x + a := Nat.lt_of_lt_of_le ha (Nat.le_add_left a x)
  have h1 : x ≤ (x + a - 1) + 1 := by
    rw [Nat.sub_add_cancel hsum_pos]
    exact Nat.le_add_right x a
  have hdiv := Nat.div_add_mod (x + a - 1) a
  have hmod : (x + a - 1) % a ≤ a - 1 := Nat.le_pred_of_lt (Nat.mod_lt (x + a - 1) ha)
  have hbound : x + a - 1 ≤ ((x + a - 1) / a) * a + (a - 1) := by
    calc
      x + a - 1 = a * ((x + a - 1) / a) + (x + a - 1) % a := hdiv.symm
      _ = ((x + a - 1) / a) * a + (x + a - 1) % a := by rw [Nat.mul_comm]
      _ ≤ ((x + a - 1) / a) * a + (a - 1) := Nat.add_le_add_left hmod _
  have hadd : x + (a - 1) ≤ ((x + a - 1) / a) * a + (a - 1) := by
    have hassoc : x + (a - 1) = x + a - 1 := (Nat.add_sub_assoc ha x).symm
    rw [hassoc]
    exact hbound
  exact Nat.le_of_add_le_add_right hadd

theorem roundUpNat_minimal {x a m : Nat} (ha : 0 < a) (hxm : x ≤ m) (hdvd : a ∣ m) :
    roundUpNat x a ≤ m := by
  rcases hdvd with ⟨q, rfl⟩
  rw [roundUpNat_eq ha]
  have hlt : x + a - 1 < (q + 1) * a := by
    have hassoc : x + a - 1 = x + (a - 1) := Nat.add_sub_assoc ha x
    have h1 : x + (a - 1) ≤ a * q + (a - 1) := Nat.add_le_add_right hxm (a - 1)
    have h2 : a * q + (a - 1) < a * q + a := Nat.add_lt_add_left (Nat.sub_lt ha (by decide : 0 < 1)) (a * q)
    have h3 : a * q + a = (q + 1) * a := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm a q]
    rw [hassoc, ← h3]
    exact Nat.lt_of_le_of_lt h1 h2
  have hdiv_lt : (x + a - 1) / a < q + 1 := (Nat.div_lt_iff_lt_mul ha).2 hlt
  have hdiv_le : (x + a - 1) / a ≤ q := Nat.le_of_lt_succ hdiv_lt
  rw [Nat.mul_comm a q]
  exact Nat.mul_le_mul_right a hdiv_le

theorem roundUpNat_isLeast {x a : Nat} (ha : 0 < a) : isLeastAlignedGe (roundUpNat x a) x a :=
  ⟨roundUpNat_ge ha, roundUpNat_dvd x ha, fun _ hxm hdvd => roundUpNat_minimal ha hxm hdvd⟩

theorem isLeastAlignedGe_unique {r1 r2 x a : Nat}
    (h1 : isLeastAlignedGe r1 x a) (h2 : isLeastAlignedGe r2 x a) : r1 = r2 := by
  exact Nat.le_antisymm (h1.2.2 r2 h2.1 h2.2.1) (h2.2.2 r1 h1.1 h1.2.1)

theorem roundUpNat_monotone {x y a : Nat} (ha : 0 < a) (hxy : x ≤ y) :
    roundUpNat x a ≤ roundUpNat y a := by
  exact roundUpNat_minimal ha (Nat.le_trans hxy (roundUpNat_ge ha)) (roundUpNat_dvd y ha)

theorem roundUpNat_of_dvd {x a : Nat} (ha : 0 < a) (hdvd : a ∣ x) : roundUpNat x a = x := by
  exact Nat.le_antisymm (roundUpNat_minimal ha (Nat.le_refl x) hdvd) (roundUpNat_ge ha)

theorem roundUpNat_zero (a : Nat) : roundUpNat 0 a = 0 := by
  cases Nat.eq_zero_or_pos a with
  | inl ha0 =>
    subst ha0
    rfl
  | inr hapos =>
    exact roundUpNat_of_dvd hapos (Nat.dvd_zero a)

theorem roundUpNat_add_mul {x c a : Nat} (ha : 0 < a) :
    roundUpNat (x + c * a) a = roundUpNat x a + c * a := by
  apply isLeastAlignedGe_unique (roundUpNat_isLeast ha)
  refine ⟨Nat.add_le_add_right (roundUpNat_ge ha) (c * a), ?_, ?_⟩
  · exact Nat.dvd_add (roundUpNat_dvd x ha) (Nat.dvd_mul_left a c)
  · intro m hm hm_dvd
    have hm_ge_ca : c * a ≤ m := Nat.le_trans (Nat.le_add_left (c * a) x) hm
    have hx_le : x ≤ m - c * a := Nat.le_sub_of_add_le hm
    have hdvd_sub : a ∣ m - c * a := Nat.dvd_sub hm_dvd (Nat.dvd_mul_left a c)
    have hru : roundUpNat x a ≤ m - c * a := roundUpNat_minimal ha hx_le hdvd_sub
    have hsum : roundUpNat x a + c * a ≤ (m - c * a) + c * a := Nat.add_le_add_right hru (c * a)
    rwa [Nat.sub_add_cancel hm_ge_ca] at hsum

theorem roundUpNat_add_of_dvd {x s a : Nat} (ha : 0 < a) (hs : a ∣ s) :
    roundUpNat (x + s) a = roundUpNat x a + s := by
  rcases hs with ⟨c, rfl⟩
  rw [Nat.mul_comm a c]
  exact roundUpNat_add_mul ha

theorem roundUpNat_idem_of_dvd {x a b : Nat} (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b) :
    roundUpNat (roundUpNat x a) b = roundUpNat x b := by
  apply isLeastAlignedGe_unique (r1 := roundUpNat (roundUpNat x a) b) (r2 := roundUpNat x b) _ (roundUpNat_isLeast (x := x) hb)
  refine ⟨Nat.le_trans (roundUpNat_ge (x := x) ha) (roundUpNat_ge (x := roundUpNat x a) hb), roundUpNat_dvd (roundUpNat x a) hb, ?_⟩
  · intro m hxm hbm
    have ham : a ∣ m := Nat.dvd_trans hab hbm
    have hru_a : roundUpNat x a ≤ m := roundUpNat_minimal ha hxm ham
    exact roundUpNat_minimal hb hru_a hbm

theorem paddingNeeded_lt {x a : Nat} (ha : 0 < a) : paddingNeeded x a < a := by
  have hne : a ≠ 0 := Nat.ne_of_gt ha
  simp only [paddingNeeded, ite_eq_right hne]
  cases Nat.eq_zero_or_pos (x % a) with
  | inl hr0 =>
    simp [hr0, ha]
  | inr hrpos =>
    have hrne : x % a ≠ 0 := Nat.ne_of_gt hrpos
    simp only [ite_eq_right hrne]
    exact Nat.sub_lt ha hrpos

theorem alignToNat_isLeast {x a : Nat} (ha : 0 < a) : isLeastAlignedGe (alignToNat x a) x a := by
  have hne : a ≠ 0 := Nat.ne_of_gt ha
  have hge : x ≤ alignToNat x a := Nat.le_add_right x (paddingNeeded x a)
  have hdvd : a ∣ alignToNat x a := by
    simp only [alignToNat, paddingNeeded, ite_eq_right hne]
    cases Nat.eq_zero_or_pos (x % a) with
    | inl hr0 =>
      simp only [ite_eq_left hr0, Nat.add_zero]
      exact Nat.dvd_of_mod_eq_zero hr0
    | inr hrpos =>
      have hrne : x % a ≠ 0 := Nat.ne_of_gt hrpos
      simp only [ite_eq_right hrne]
      have hmod_le : x % a ≤ a := Nat.le_of_lt (Nat.mod_lt x ha)
      have hdiv := Nat.div_add_mod x a
      have heq : x + (a - x % a) = a * (x / a + 1) := by
        calc
          x + (a - x % a) = (a * (x / a) + x % a) + (a - x % a) := by rw [hdiv]
          _ = a * (x / a) + (x % a + (a - x % a)) := Nat.add_assoc _ _ _
          _ = a * (x / a) + a := by rw [Nat.add_sub_cancel' hmod_le]
          _ = a * (x / a + 1) := by rw [Nat.mul_add, Nat.mul_one]
      rw [heq]
      exact Nat.dvd_mul_right a (x / a + 1)
  refine ⟨hge, hdvd, ?_⟩
  intro m hxm hdm
  have hpad : paddingNeeded x a < a := paddingNeeded_lt ha
  have hlt : alignToNat x a < m + a := Nat.add_lt_add_of_le_of_lt hxm hpad
  rcases hdvd with ⟨q1, hq1⟩
  rcases hdm with ⟨q2, hq2⟩
  rw [hq1] at hlt
  rw [hq2] at hlt
  cases Nat.lt_or_ge q2 q1 with
  | inl hq =>
    have hsucc : q2 + 1 ≤ q1 := Nat.succ_le_of_lt hq
    have hmul : a * (q2 + 1) ≤ a * q1 := Nat.mul_le_mul_left a hsucc
    have hcontra : a * q2 + a ≤ a * q1 := by
      have : a * (q2 + 1) = a * q2 + a := by rw [Nat.mul_add, Nat.mul_one]
      rwa [← this]
    exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hcontra hlt))
  | inr hq =>
    rw [hq1, hq2]
    exact Nat.mul_le_mul_left a hq

theorem roundUpNat_eq_alignToNat {x a : Nat} (ha : 0 < a) : roundUpNat x a = alignToNat x a :=
  isLeastAlignedGe_unique (roundUpNat_isLeast ha) (alignToNat_isLeast ha)

theorem roundUpNat_eq_add_roundDown_sub {x a : Nat} (ha : 0 < a) :
    roundUpNat x a = roundDownNat (x + a - 1) a := by
  rw [roundUpNat_eq ha, roundDownNat_eq ha]

theorem roundUpNat_eq_self_plus_pad_le {x a b : Nat} (ha : 0 < a) (hx : x ≤ b) (hb : a ∣ b) :
    roundUpNat x a ≤ b :=
  roundUpNat_minimal ha hx hb

/-! ## Section 2: Bit-Level `BitVec w` Equivalence of LLVM `(x + a - 1) &&& (-a)` and `roundUpNat` -/

noncomputable def llvmRoundDownBV {w : Nat} (y a : BitVec w) : BitVec w :=
  y &&& (0 - a)

noncomputable def llvmAlignUpBV {w : Nat} (x a : BitVec w) : BitVec w :=
  (x + (a - 1)) &&& (0 - a)

theorem two_pow_sub_two_pow_eq_pred_mul {w k : Nat} (hkw : k ≤ w) :
    2 ^ w - 2 ^ k = (2 ^ (w - k) - 1) * 2 ^ k := by
  have hw : 2 ^ w = 2 ^ (w - k) * 2 ^ k := by
    have hadd : (w - k) + k = w := Nat.sub_add_cancel hkw
    calc
      2 ^ w = 2 ^ ((w - k) + k) := by rw [hadd]
      _ = 2 ^ (w - k) * 2 ^ k := Nat.pow_add 2 (w - k) k
  rw [hw, Nat.sub_mul, Nat.one_mul]

theorem testBit_two_pow_sub_one_pure (n j : Nat) :
    (2 ^ n - 1).testBit j = decide (j < n) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    have hpos : 0 < 2 ^ n := pow2_pos n
    have hge1 : 1 ≤ 2 ^ n := Nat.succ_le_of_lt hpos
    have hstep : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
      have hmul : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hmul]
      have hdecomp : 2 ^ n = (2 ^ n - 1) + 1 := (Nat.sub_add_cancel hge1).symm
      calc
        2 * 2 ^ n - 1 = 2 * ((2 ^ n - 1) + 1) - 1 := by rw [← hdecomp]
        _ = (2 * (2 ^ n - 1) + 2) - 1 := by rw [Nat.mul_add, Nat.mul_one]
        _ = 2 * (2 ^ n - 1) + (2 - 1) := Nat.add_sub_assoc (by decide : 1 ≤ 2) _
    cases j with
    | zero =>
      rw [hstep, Nat.testBit_zero]
      have hmod : (2 * (2 ^ n - 1) + 1) % 2 = 1 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_left]
      rw [hmod, decide_eq_true (Nat.succ_pos n)]
      rfl
    | succ j' =>
      rw [hstep, Nat.testBit_succ]
      have hdiv : (2 * (2 ^ n - 1) + 1) / 2 = 2 ^ n - 1 := by
        rw [Nat.mul_add_div (by decide : 0 < 2)]
        rfl
      rw [hdiv, ih j']
      cases Nat.lt_or_ge j' n with
      | inl hj =>
        have hs : j' + 1 < n + 1 := Nat.succ_lt_succ hj
        rw [decide_eq_true hj, decide_eq_true hs]
      | inr hj =>
        have hns : ¬ (j' + 1 < n + 1) := fun h => Nat.not_lt_of_ge hj (Nat.lt_of_succ_lt_succ h)
        rw [decide_eq_false (Nat.not_lt_of_ge hj), decide_eq_false hns]

theorem testBit_neg_two_pow {w k i : Nat} (hkw : k ≤ w) (hki : k ≤ i) (hiw : i < w) :
    (2 ^ w - 2 ^ k).testBit i = true := by
  rw [two_pow_sub_two_pow_eq_pred_mul hkw, Nat.testBit_mul_two_pow]
  have hdec1 : decide (k ≤ i) = true := decide_eq_true hki
  have hik : i - k < w - k := Nat.sub_lt_sub_right hki hiw
  have hdec2 : decide (i - k < w - k) = true := decide_eq_true hik
  rw [hdec1, testBit_two_pow_sub_one_pure, hdec2]
  rfl

theorem testBit_neg_two_pow_lt {w k i : Nat} (hkw : k ≤ w) (hik : i < k) :
    (2 ^ w - 2 ^ k).testBit i = false := by
  rw [two_pow_sub_two_pow_eq_pred_mul hkw, Nat.testBit_mul_two_pow]
  have hnot : ¬ (k ≤ i) := Nat.not_le_of_gt hik
  have hdec : decide (k ≤ i) = false := decide_eq_false hnot
  rw [hdec]
  rfl

theorem nat_land_neg_two_pow_eq_roundDown {w k y : Nat} (hkw : k ≤ w) (hy : y < 2 ^ w) :
    y &&& (2 ^ w - 2 ^ k) = (y / 2 ^ k) * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow]
  cases Nat.lt_or_ge i k with
  | inl hik =>
    have hnot : ¬ (k ≤ i) := Nat.not_le_of_gt hik
    have hdec : decide (k ≤ i) = false := decide_eq_false hnot
    rw [testBit_neg_two_pow_lt hkw hik, hdec, Bool.and_false, Bool.false_and]
  | inr hki =>
    have hdec : decide (k ≤ i) = true := decide_eq_true hki
    rw [hdec, Bool.true_and, Nat.testBit_div_two_pow, Nat.sub_add_cancel hki]
    cases Nat.lt_or_ge i w with
    | inl hiw =>
      rw [testBit_neg_two_pow hkw hki hiw, Bool.and_true]
    | inr hwi =>
      have hy_lt_i : y < 2 ^ i := Nat.lt_of_lt_of_le hy (pow2_le_of_le_exp hwi)
      rw [Nat.testBit_lt_two_pow hy_lt_i, Bool.false_and]

theorem bv_neg_two_pow_toNat {w k : Nat} (hkw : k < w) :
    (0 - (BitVec.ofNat w (2 ^ k))).toNat = 2 ^ w - 2 ^ k := by
  rw [BitVec.toNat_sub]
  have hk_lt_w : 2 ^ k < 2 ^ w := pow2_lt_of_lt hkw
  have hof : (BitVec.ofNat w (2 ^ k)).toNat = 2 ^ k := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hk_lt_w
  have h0 : (0 : BitVec w).toNat = 0 := BitVec.toNat_zero
  rw [hof, h0, Nat.add_zero]
  have hsub_lt : 2 ^ w - 2 ^ k < 2 ^ w := Nat.sub_lt (pow2_pos w) (pow2_pos k)
  exact Nat.mod_eq_of_lt hsub_lt

theorem bv_sub_one_two_pow_toNat {w k : Nat} (hkw : k < w) :
    ((BitVec.ofNat w (2 ^ k)) - (1 : BitVec w)).toNat = 2 ^ k - 1 := by
  have hwpos : 0 < w := Nat.lt_of_le_of_lt (Nat.zero_le k) hkw
  have h1_lt : 1 < 2 ^ w := pow2_lt_of_lt (m := 0) hwpos
  have hk_lt : 2 ^ k < 2 ^ w := pow2_lt_of_lt hkw
  have h1_toNat : (1 : BitVec w).toNat = 1 := by
    change (BitVec.ofNat w 1).toNat = 1
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt h1_lt
  have ha_toNat : (BitVec.ofNat w (2 ^ k)).toNat = 2 ^ k := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hk_lt
  rw [BitVec.toNat_sub, h1_toNat, ha_toNat]
  have hsplit : 2 ^ w - 1 + 2 ^ k = (2 ^ k - 1) + 2 ^ w := by
    have h1_le_poww : 1 ≤ 2 ^ w := Nat.le_of_lt h1_lt
    have h1_le_powk : 1 ≤ 2 ^ k := Nat.succ_le_of_lt (pow2_pos k)
    calc
      2 ^ w - 1 + 2 ^ k = 2 ^ w - 1 + (1 + (2 ^ k - 1)) := by rw [Nat.add_sub_cancel' h1_le_powk]
      _ = (2 ^ w - 1 + 1) + (2 ^ k - 1) := (Nat.add_assoc _ _ _).symm
      _ = 2 ^ w + (2 ^ k - 1) := by rw [Nat.sub_add_cancel h1_le_poww]
      _ = (2 ^ k - 1) + 2 ^ w := Nat.add_comm _ _
  rw [hsplit, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.sub_lt (pow2_pos k) (by decide : 0 < 1)) (Nat.le_of_lt hk_lt))

theorem llvmRoundDownBV_eq_roundDownNat {w k : Nat} (hkw : k < w) (y : BitVec w) :
    (llvmRoundDownBV y (BitVec.ofNat w (2 ^ k))).toNat = roundDownNat y.toNat (2 ^ k) := by
  simp only [llvmRoundDownBV]
  rw [BitVec.toNat_and, bv_neg_two_pow_toNat hkw]
  rw [nat_land_neg_two_pow_eq_roundDown (Nat.le_of_lt hkw) y.isLt]
  rw [roundDownNat_eq (pow2_pos k)]

theorem llvmAlignUpBV_eq_roundUpNat {w k : Nat} (hkw : k < w) (x : BitVec w)
    (h_no_overflow : x.toNat + (2 ^ k - 1) < 2 ^ w) :
    (llvmAlignUpBV x (BitVec.ofNat w (2 ^ k))).toNat = roundUpNat x.toNat (2 ^ k) := by
  simp only [llvmAlignUpBV]
  have hsum : (x + (BitVec.ofNat w (2 ^ k) - 1)).toNat = x.toNat + (2 ^ k - 1) := by
    rw [BitVec.toNat_add, bv_sub_one_two_pow_toNat hkw]
    exact Nat.mod_eq_of_lt h_no_overflow
  rw [BitVec.toNat_and, hsum, bv_neg_two_pow_toNat hkw]
  rw [nat_land_neg_two_pow_eq_roundDown (Nat.le_of_lt hkw) h_no_overflow]
  have hassoc : x.toNat + (2 ^ k - 1) = x.toNat + 2 ^ k - 1 :=
    (Nat.add_sub_assoc (pow2_pos k) x.toNat).symm
  rw [hassoc, roundUpNat_eq (pow2_pos k)]

theorem llvmAlignUpBV_unit_offset {w k : Nat} (hkw : k < w) (sz : BitVec w)
    (h_no_overflow : 1 + sz.toNat + (2 ^ k - 1) < 2 ^ w) :
    (llvmAlignUpBV (1 + sz) (BitVec.ofNat w (2 ^ k))).toNat =
      (((BitVec.ofNat w (2 ^ k)) + sz) &&& (0 - BitVec.ofNat w (2 ^ k))).toNat := by
  have hwpos : 0 < w := Nat.lt_of_le_of_lt (Nat.zero_le k) hkw
  have h1_lt : 1 < 2 ^ w := pow2_lt_of_lt (m := 0) hwpos
  have h1_toNat : (1 : BitVec w).toNat = 1 := by
    change (BitVec.ofNat w 1).toNat = 1
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt h1_lt
  have h1_le_powk : 1 ≤ 2 ^ k := Nat.succ_le_of_lt (pow2_pos k)
  have h1_sz_lt : 1 + sz.toNat < 2 ^ w := by
    exact Nat.lt_of_le_of_lt (Nat.le_add_right (1 + sz.toNat) (2 ^ k - 1)) h_no_overflow
  have h_1_plus_sz : (1 + sz).toNat = 1 + sz.toNat := by
    rw [BitVec.toNat_add, h1_toNat]
    exact Nat.mod_eq_of_lt h1_sz_lt
  have h_sum_eq : 1 + sz.toNat + (2 ^ k - 1) = 2 ^ k + sz.toNat := by
    calc
      1 + sz.toNat + (2 ^ k - 1) = (2 ^ k - 1) + (1 + sz.toNat) := Nat.add_comm _ _
      _ = ((2 ^ k - 1) + 1) + sz.toNat := (Nat.add_assoc _ _ _).symm
      _ = 2 ^ k + sz.toNat := by rw [Nat.sub_add_cancel h1_le_powk]
  have h_no_ovf_lhs : (1 + sz).toNat + (2 ^ k - 1) < 2 ^ w := by
    rwa [h_1_plus_sz]
  have hk_lt_w : 2 ^ k < 2 ^ w := pow2_lt_of_lt hkw
  have ha_toNat : (BitVec.ofNat w (2 ^ k)).toNat = 2 ^ k := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hk_lt_w
  have h_no_ovf_rhs : 2 ^ k + sz.toNat < 2 ^ w := by
    rwa [← h_sum_eq]
  have h_rhs_add : ((BitVec.ofNat w (2 ^ k)) + sz).toNat = 2 ^ k + sz.toNat := by
    rw [BitVec.toNat_add, ha_toNat]
    exact Nat.mod_eq_of_lt h_no_ovf_rhs
  have hlhs := llvmAlignUpBV_eq_roundUpNat hkw (1 + sz) h_no_ovf_lhs
  rw [hlhs, h_1_plus_sz, BitVec.toNat_and, h_rhs_add, bv_neg_two_pow_toNat hkw]
  rw [nat_land_neg_two_pow_eq_roundDown (Nat.le_of_lt hkw) h_no_ovf_rhs]
  rw [roundUpNat_eq (pow2_pos k)]
  have h_inner : 1 + sz.toNat + 2 ^ k - 1 = 2 ^ k + sz.toNat := by
    calc
      1 + sz.toNat + 2 ^ k - 1 = 1 + (sz.toNat + 2 ^ k) - 1 := by rw [Nat.add_assoc]
      _ = (sz.toNat + 2 ^ k) + 1 - 1 := by rw [Nat.add_comm 1 (sz.toNat + 2 ^ k)]
      _ = sz.toNat + 2 ^ k := Nat.add_sub_cancel (sz.toNat + 2 ^ k) 1
      _ = 2 ^ k + sz.toNat := Nat.add_comm _ _
  rw [h_inner]

theorem llvmAlignUpBV_wraps_on_overflow :
    let x : BitVec 64 := BitVec.ofNat 64 (2 ^ 64 - 1)
    let a : BitVec 64 := BitVec.ofNat 64 16
    (llvmAlignUpBV x a).toNat < x.toNat := by
  decide

/-! ## Section 3: Wide Pointers, `ptr::eq` vs `ptr::addr_eq`, and Non-Deterministic Vtables -/

inductive PtrMeta where
  | thin : PtrMeta
  | sliceLen (len : Nat) : PtrMeta
  | dynVtable (vaddr : Nat) : PtrMeta

structure WidePtr where
  addr : Nat
  pmeta : PtrMeta

noncomputable def metaEq (m1 m2 : PtrMeta) : Bool :=
  match m1, m2 with
  | .thin, .thin => true
  | .sliceLen l1, .sliceLen l2 => l1.beq l2
  | .dynVtable v1, .dynVtable v2 => v1.beq v2
  | _, _ => false

noncomputable def ptrEq (p q : WidePtr) : Bool :=
  (p.addr.beq q.addr) && metaEq p.pmeta q.pmeta

noncomputable def ptrNe (p q : WidePtr) : Bool :=
  !(p.addr.beq q.addr) || !(metaEq p.pmeta q.pmeta)

noncomputable def addrEq (p q : WidePtr) : Bool :=
  p.addr.beq q.addr

theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : a.beq b = false := by
  cases hbeq : a.beq b with
  | false => rfl
  | true => exact False.elim (h (Nat.eq_of_beq_eq_true hbeq))

theorem metaEq_refl (m : PtrMeta) : metaEq m m = true := by
  cases m with
  | thin => rfl
  | sliceLen l => exact Nat.beq_refl l
  | dynVtable v => exact Nat.beq_refl v

theorem metaEq_symm {m1 m2 : PtrMeta} (h : metaEq m1 m2 = true) : metaEq m2 m1 = true := by
  cases m1 <;> cases m2 <;> simp only [metaEq, Bool.false_eq_true] at h ⊢
  · rw [Nat.eq_of_beq_eq_true h]; exact Nat.beq_refl _
  · rw [Nat.eq_of_beq_eq_true h]; exact Nat.beq_refl _

theorem metaEq_trans {m1 m2 m3 : PtrMeta}
    (h12 : metaEq m1 m2 = true) (h23 : metaEq m2 m3 = true) : metaEq m1 m3 = true := by
  cases m1 <;> cases m2 <;> cases m3 <;> simp only [metaEq, Bool.false_eq_true] at h12 h23 ⊢
  · rw [Nat.eq_of_beq_eq_true h12, Nat.eq_of_beq_eq_true h23]; exact Nat.beq_refl _
  · rw [Nat.eq_of_beq_eq_true h12, Nat.eq_of_beq_eq_true h23]; exact Nat.beq_refl _

theorem ptrEq_refl (p : WidePtr) : ptrEq p p = true := by
  simp only [ptrEq, Nat.beq_refl, metaEq_refl, Bool.true_and]

theorem ptrEq_symm {p q : WidePtr} (h : ptrEq p q = true) : ptrEq q p = true := by
  simp only [ptrEq, Bool.and_eq_true] at h ⊢
  refine ⟨?_, metaEq_symm h.2⟩
  rw [Nat.eq_of_beq_eq_true h.1]
  exact Nat.beq_refl _

theorem ptrEq_trans {p q r : WidePtr}
    (hpq : ptrEq p q = true) (hqr : ptrEq q r = true) : ptrEq p r = true := by
  simp only [ptrEq, Bool.and_eq_true] at hpq hqr ⊢
  refine ⟨?_, metaEq_trans hpq.2 hqr.2⟩
  rw [Nat.eq_of_beq_eq_true hpq.1, Nat.eq_of_beq_eq_true hqr.1]
  exact Nat.beq_refl _

theorem addrEq_refl (p : WidePtr) : addrEq p p = true := by
  exact Nat.beq_refl p.addr

theorem addrEq_symm {p q : WidePtr} (h : addrEq p q = true) : addrEq q p = true := by
  simp only [addrEq] at h ⊢
  rw [Nat.eq_of_beq_eq_true h]
  exact Nat.beq_refl _

theorem addrEq_trans {p q r : WidePtr}
    (hpq : addrEq p q = true) (hqr : addrEq q r = true) : addrEq p r = true := by
  simp only [addrEq] at hpq hqr ⊢
  rw [Nat.eq_of_beq_eq_true hpq, Nat.eq_of_beq_eq_true hqr]
  exact Nat.beq_refl _

theorem ptrEq_implies_addrEq {p q : WidePtr} (h : ptrEq p q = true) : addrEq p q = true := by
  simp only [ptrEq, Bool.and_eq_true] at h
  exact h.1

theorem ptrNe_eq_not_ptrEq (p q : WidePtr) : ptrNe p q = !(ptrEq p q) := by
  simp only [ptrNe, ptrEq, Bool.not_and]

theorem addrEq_eq_ptrEq_on_thin {a1 a2 : Nat} :
    ptrEq ⟨a1, .thin⟩ ⟨a2, .thin⟩ = addrEq ⟨a1, .thin⟩ ⟨a2, .thin⟩ := by
  simp only [ptrEq, addrEq, metaEq, Bool.and_true]

theorem slice_addrEq_not_implies_ptrEq (baseAddr : Nat) :
    let s2 : WidePtr := ⟨baseAddr, .sliceLen 2⟩
    let s3 : WidePtr := ⟨baseAddr, .sliceLen 3⟩
    addrEq s2 s3 = true ∧ ptrEq s2 s3 = false := by
  refine ⟨?_, ?_⟩
  · exact Nat.beq_refl baseAddr
  · have h23 : Nat.beq 2 3 = false := rfl
    simp only [ptrEq, metaEq, h23, Bool.and_false]

theorem slice_same_len_ptrEq_iff_addrEq (a1 a2 len : Nat) :
    ptrEq ⟨a1, .sliceLen len⟩ ⟨a2, .sliceLen len⟩ =
      addrEq ⟨a1, .sliceLen len⟩ ⟨a2, .sliceLen len⟩ := by
  simp only [ptrEq, addrEq, metaEq, Nat.beq_refl, Bool.and_true]

structure ConcreteDynTarget where
  objAddr : Nat
  concreteTypeId : Nat
  traitId : Nat

structure VtableAllocOracle where
  resolve : ConcreteDynTarget → Nat → Nat

noncomputable def coerceToDyn (oracle : VtableAllocOracle) (tgt : ConcreteDynTarget) (salt : Nat) : WidePtr :=
  ⟨tgt.objAddr, .dynVtable (oracle.resolve tgt salt)⟩

noncomputable def sameObjSaltInvariant (oracle : VtableAllocOracle) (tgt : ConcreteDynTarget) : Prop :=
  ∀ s1 s2 : Nat, oracle.resolve tgt s1 = oracle.resolve tgt s2

noncomputable def vtableDivergesOnSalts (oracle : VtableAllocOracle) (tgt : ConcreteDynTarget) (s1 s2 : Nat) : Prop :=
  oracle.resolve tgt s1 ≠ oracle.resolve tgt s2

noncomputable def vtableDeduplicatesDistinctTypes (oracle : VtableAllocOracle)
    (t1 t2 : ConcreteDynTarget) (s1 s2 : Nat) : Prop :=
  t1.concreteTypeId ≠ t2.concreteTypeId ∧ oracle.resolve t1 s1 = oracle.resolve t2 s2

theorem addrEq_invariant_under_vtable_salts (oracle : VtableAllocOracle)
    (tgt : ConcreteDynTarget) (s1 s2 : Nat) :
    addrEq (coerceToDyn oracle tgt s1) (coerceToDyn oracle tgt s2) = true := by
  exact Nat.beq_refl tgt.objAddr

theorem ptrEq_true_when_salt_invariant (oracle : VtableAllocOracle)
    (tgt : ConcreteDynTarget) (hinv : sameObjSaltInvariant oracle tgt) (s1 s2 : Nat) :
    ptrEq (coerceToDyn oracle tgt s1) (coerceToDyn oracle tgt s2) = true := by
  simp only [coerceToDyn, ptrEq, metaEq, Nat.beq_refl, Bool.true_and]
  rw [hinv s1 s2]
  exact Nat.beq_refl _

theorem ptrEq_false_when_vtable_diverges (oracle : VtableAllocOracle)
    (tgt : ConcreteDynTarget) (s1 s2 : Nat) (hdiv : vtableDivergesOnSalts oracle tgt s1 s2) :
    ptrEq (coerceToDyn oracle tgt s1) (coerceToDyn oracle tgt s2) = false := by
  simp only [coerceToDyn, ptrEq, metaEq, Nat.beq_refl, Bool.true_and]
  exact nat_beq_false_of_ne hdiv

theorem miri_salted_vtable_model_divergence_witness :
    let miriOracle : VtableAllocOracle :=
      ⟨fun tgt salt => 0x20000 + tgt.concreteTypeId * 64 + (salt % 32) * 8⟩
    let tgt : ConcreteDynTarget := ⟨0x20b1b, 1, 1⟩
    let pA := coerceToDyn miriOracle tgt 0
    let pB := coerceToDyn miriOracle tgt 1
    addrEq pA pB = true ∧ ptrEq pA pB = false ∧ ptrEq pA pA = true := by
  refine ⟨rfl, rfl, rfl⟩

theorem native_cgu_vtable_dedup_false_positive_witness :
    let nativeOracle : VtableAllocOracle :=
      ⟨fun _tgt _salt => 0x55e878aaeb98⟩
    let tA : ConcreteDynTarget := ⟨0x7ffd7feb16bd, 10, 7⟩
    let tB : ConcreteDynTarget := ⟨0x7ffd7feb16bd, 11, 7⟩
    tA.concreteTypeId ≠ tB.concreteTypeId ∧
      addrEq (coerceToDyn nativeOracle tA 0) (coerceToDyn nativeOracle tB 0) = true ∧
      ptrEq (coerceToDyn nativeOracle tA 0) (coerceToDyn nativeOracle tB 0) = true := by
  refine ⟨by decide, rfl, rfl⟩

theorem trait_upcast_vtable_prefix_divergence_witness :
    let upcastOracle : VtableAllocOracle :=
      ⟨fun tgt isUpcast => if isUpcast.beq 0 then 0x400100 + tgt.concreteTypeId * 8 else 0x500200 + tgt.concreteTypeId * 8⟩
    let tgt : ConcreteDynTarget := ⟨0x7fff1000, 3, 1⟩
    let pDirect := coerceToDyn upcastOracle tgt 0
    let pUpcast := coerceToDyn upcastOracle tgt 1
    addrEq pDirect pUpcast = true ∧ ptrEq pDirect pUpcast = false := by
  refine ⟨rfl, rfl⟩

/-! ## Section 4: Custom DST `size_and_align_of_dst` Two-Step vs Single-Round Equivalence -/

structure DstTailMeta where
  size : Nat
  align : Nat

structure CustomDstSpec where
  unsizedOffsetUnadj : Nat
  prefixAlign : Nat
  packCap : Option Nat

noncomputable def applyPackCap (a : Nat) (packCap : Option Nat) : Nat :=
  match packCap with
  | none => a
  | some p => min a p

noncomputable def effectiveTailAlign (spec : CustomDstSpec) (tail : DstTailMeta) : Nat :=
  applyPackCap tail.align spec.packCap

noncomputable def fullDstAlign (spec : CustomDstSpec) (tail : DstTailMeta) : Nat :=
  max spec.prefixAlign (effectiveTailAlign spec tail)

noncomputable def sizeAndAlignRustc (spec : CustomDstSpec) (tail : DstTailMeta) : Nat × Nat :=
  let effTail := effectiveTailAlign spec tail
  let fullA := max spec.prefixAlign effTail
  (roundUpNat (spec.unsizedOffsetUnadj + tail.size) fullA, fullA)

noncomputable def sizeAndAlignTwoStep (spec : CustomDstSpec) (tail : DstTailMeta) : Nat × Nat :=
  let effTail := effectiveTailAlign spec tail
  let fullA := max spec.prefixAlign effTail
  let adjOffset := alignToNat spec.unsizedOffsetUnadj effTail
  (alignToNat (adjOffset + tail.size) fullA, fullA)

noncomputable def sizeAndAlignRustcBV {w : Nat} (spec : CustomDstSpec) (tail : DstTailMeta) :
    BitVec w × BitVec w :=
  let effTail := effectiveTailAlign spec tail
  let fullA := max spec.prefixAlign effTail
  let aBV : BitVec w := BitVec.ofNat w fullA
  let sumBV : BitVec w := BitVec.ofNat w spec.unsizedOffsetUnadj + BitVec.ofNat w tail.size
  (llvmAlignUpBV sumBV aBV, aBV)

noncomputable def validPackCap : Option Nat → Prop
  | none => True
  | some p => isPow2 p

theorem effectiveTailAlign_isPow2 (spec : CustomDstSpec) (tail : DstTailMeta)
    (ht : isPow2 tail.align) (hp : validPackCap spec.packCap) :
    isPow2 (effectiveTailAlign spec tail) := by
  cases hcap : spec.packCap with
  | none =>
    simp [effectiveTailAlign, applyPackCap, hcap, ht]
  | some p =>
    simp only [validPackCap, hcap] at hp
    simp only [effectiveTailAlign, applyPackCap, hcap]
    exact min_pow2_isPow2 ht hp

theorem effectiveTailAlign_dvd_tailAlign (spec : CustomDstSpec) (tail : DstTailMeta)
    (ht : isPow2 tail.align) (hp : validPackCap spec.packCap) :
    effectiveTailAlign spec tail ∣ tail.align := by
  cases hcap : spec.packCap with
  | none =>
    simp [effectiveTailAlign, applyPackCap, hcap]
  | some p =>
    simp only [validPackCap, hcap] at hp
    simp only [effectiveTailAlign, applyPackCap, hcap]
    exact min_pow2_dvd_left ht hp

theorem effectiveTailAlign_dvd_fullAlign (spec : CustomDstSpec) (tail : DstTailMeta)
    (hpref : isPow2 spec.prefixAlign) (ht : isPow2 tail.align) (hp : validPackCap spec.packCap) :
    effectiveTailAlign spec tail ∣ fullDstAlign spec tail := by
  have heff := effectiveTailAlign_isPow2 spec tail ht hp
  exact right_dvd_max_pow2 hpref heff

theorem sizeAndAlignRustc_eq_twoStep (spec : CustomDstSpec) (tail : DstTailMeta)
    (hpref : isPow2 spec.prefixAlign)
    (ht : isPow2 tail.align)
    (hp : validPackCap spec.packCap)
    (hdvd_tail : tail.align ∣ tail.size) :
    sizeAndAlignRustc spec tail = sizeAndAlignTwoStep spec tail := by
  have heff_pow2 : isPow2 (effectiveTailAlign spec tail) :=
    effectiveTailAlign_isPow2 spec tail ht hp
  have heff_pos : 0 < effectiveTailAlign spec tail := isPow2_pos heff_pow2
  have hfull_pow2 : isPow2 (fullDstAlign spec tail) :=
    max_pow2_isPow2 hpref heff_pow2
  have hfull_pos : 0 < fullDstAlign spec tail := isPow2_pos hfull_pow2
  have heff_dvd_tail : effectiveTailAlign spec tail ∣ tail.size :=
    Nat.dvd_trans (effectiveTailAlign_dvd_tailAlign spec tail ht hp) hdvd_tail
  have heff_dvd_full : effectiveTailAlign spec tail ∣ fullDstAlign spec tail :=
    effectiveTailAlign_dvd_fullAlign spec tail hpref ht hp
  simp only [sizeAndAlignRustc, sizeAndAlignTwoStep]
  congr 1
  rw [← roundUpNat_eq_alignToNat heff_pos]
  rw [← roundUpNat_eq_alignToNat (a := max spec.prefixAlign (effectiveTailAlign spec tail)) hfull_pos]
  rw [← roundUpNat_add_of_dvd heff_pos heff_dvd_tail]
  exact (roundUpNat_idem_of_dvd heff_pos hfull_pos heff_dvd_full).symm

theorem sizeAndAlignRustc_align_dvd_size (spec : CustomDstSpec) (tail : DstTailMeta)
    (hpref : isPow2 spec.prefixAlign) (ht : isPow2 tail.align) (hp : validPackCap spec.packCap) :
    (sizeAndAlignRustc spec tail).2 ∣ (sizeAndAlignRustc spec tail).1 := by
  have hfull_pos := isPow2_pos (max_pow2_isPow2 hpref (effectiveTailAlign_isPow2 spec tail ht hp))
  simp only [sizeAndAlignRustc]
  exact roundUpNat_dvd _ hfull_pos

theorem sizeAndAlignRustc_size_ge_sum (spec : CustomDstSpec) (tail : DstTailMeta)
    (hpref : isPow2 spec.prefixAlign) (ht : isPow2 tail.align) (hp : validPackCap spec.packCap) :
    spec.unsizedOffsetUnadj + tail.size ≤ (sizeAndAlignRustc spec tail).1 := by
  have heff_pow2 := effectiveTailAlign_isPow2 spec tail ht hp
  have hfull_pos := isPow2_pos (max_pow2_isPow2 hpref heff_pow2)
  simp only [sizeAndAlignRustc]
  exact roundUpNat_ge hfull_pos

theorem sizeAndAlignRustc_bitmask_eq {w : Nat} (spec : CustomDstSpec) (tail : DstTailMeta)
    (hpref : isPow2 spec.prefixAlign)
    (ht : isPow2 tail.align)
    (hp : validPackCap spec.packCap)
    (h_full_lt : fullDstAlign spec tail = 2 ^ k → k < w)
    (h_off_lt : spec.unsizedOffsetUnadj < 2 ^ w)
    (h_tail_lt : tail.size < 2 ^ w)
    (h_sum_lt : spec.unsizedOffsetUnadj + tail.size < 2 ^ w)
    (h_round_no_ovf : spec.unsizedOffsetUnadj + tail.size + (2 ^ k - 1) < 2 ^ w)
    (hk_def : fullDstAlign spec tail = 2 ^ k) :
    (sizeAndAlignRustcBV (w := w) spec tail).1.toNat = (sizeAndAlignRustc spec tail).1 ∧
      (sizeAndAlignRustcBV (w := w) spec tail).2.toNat = (sizeAndAlignRustc spec tail).2 := by
  have _ := hpref
  have _ := ht
  have _ := hp
  have hkw : k < w := h_full_lt hk_def
  have h_full_lt_poww : 2 ^ k < 2 ^ w := pow2_lt_of_lt hkw
  have h_sum_bv :
      (BitVec.ofNat w spec.unsizedOffsetUnadj + BitVec.ofNat w tail.size).toNat =
        spec.unsizedOffsetUnadj + tail.size := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt h_off_lt, Nat.mod_eq_of_lt h_tail_lt]
    exact Nat.mod_eq_of_lt h_sum_lt
  have h_no_ovf_bv :
      (BitVec.ofNat w spec.unsizedOffsetUnadj + BitVec.ofNat w tail.size).toNat + (2 ^ k - 1) < 2 ^ w := by
    rwa [h_sum_bv]
  simp only [sizeAndAlignRustcBV, sizeAndAlignRustc]
  change (llvmAlignUpBV (BitVec.ofNat w spec.unsizedOffsetUnadj + BitVec.ofNat w tail.size)
            (BitVec.ofNat w (fullDstAlign spec tail))).toNat =
          roundUpNat (spec.unsizedOffsetUnadj + tail.size) (fullDstAlign spec tail) ∧
        (BitVec.ofNat w (fullDstAlign spec tail)).toNat = fullDstAlign spec tail
  rw [hk_def]
  refine ⟨?_, ?_⟩
  · have h_bv := llvmAlignUpBV_eq_roundUpNat hkw
      (BitVec.ofNat w spec.unsizedOffsetUnadj + BitVec.ofNat w tail.size) h_no_ovf_bv
    rwa [h_sum_bv] at h_bv
  · rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt h_full_lt_poww

-- Concrete specimen checks matching the live `rustc` & Miri custom DST execution probe:
noncomputable def pktSpec : CustomDstSpec := ⟨1, 1, none⟩
noncomputable def pktU32Spec : CustomDstSpec := ⟨4, 4, none⟩
noncomputable def h6Spec : CustomDstSpec := ⟨6, 4, none⟩
noncomputable def packed2U32Spec : CustomDstSpec := ⟨2, 1, some 2⟩

theorem specimen_pkt_u32_3 :
    sizeAndAlignRustc pktU32Spec ⟨12, 4⟩ = (16, 4) := by
  rfl

theorem specimen_pkt_u32_0 :
    sizeAndAlignRustc pktU32Spec ⟨0, 4⟩ = (4, 4) := by
  rfl

theorem specimen_pkt_u8_3 :
    sizeAndAlignRustc pktSpec ⟨3, 1⟩ = (4, 1) := by
  rfl

theorem specimen_pkt_dyn_small :
    sizeAndAlignRustc pktSpec ⟨1, 1⟩ = (2, 1) := by
  rfl

theorem specimen_pkt_dyn_big :
    sizeAndAlignRustc pktSpec ⟨16, 16⟩ = (32, 16) := by
  rfl

theorem specimen_h6_u8_3 :
    sizeAndAlignRustc h6Spec ⟨3, 1⟩ = (12, 4) := by
  rfl

theorem specimen_h6_dyn_big :
    sizeAndAlignRustc h6Spec ⟨16, 16⟩ = (32, 16) := by
  rfl

theorem specimen_packed2_u32_3 :
    sizeAndAlignRustc packed2U32Spec ⟨12, 4⟩ = (14, 2) := by
  rfl

/-! ## Section 5: `google/zerocopy` `KnownLayout` / `DstLayout` Overflow-Checked Arithmetic & `isize::MAX` Soundness -/

noncomputable def usizeMax (w : Nat) : Nat :=
  2 ^ w - 1

noncomputable def isizeMax (w : Nat) : Nat :=
  2 ^ (w - 1) - 1

theorem isizeMax_le_usizeMax (w : Nat) : isizeMax w ≤ usizeMax w := by
  simp only [isizeMax, usizeMax]
  exact Nat.sub_le_sub_right (pow2_le_of_le_exp (Nat.sub_le w 1)) 1

theorem isizeMax_lt_usizeMax {w : Nat} (hw : 0 < w) : isizeMax w < usizeMax w := by
  simp only [isizeMax, usizeMax]
  have h1 : w - 1 < w := Nat.sub_lt hw (by decide : 0 < 1)
  have hpow : 2 ^ (w - 1) < 2 ^ w := pow2_lt_of_lt h1
  have hpos : 0 < 2 ^ (w - 1) := pow2_pos (w - 1)
  have hge1 : 1 ≤ 2 ^ (w - 1) := Nat.succ_le_of_lt hpos
  have hlt1 : 2 ^ (w - 1) - 1 + 1 < 2 ^ w := by
    rwa [Nat.sub_add_cancel hge1]
  exact Nat.lt_sub_of_add_lt hlt1

noncomputable def checkedAddW (w a b : Nat) : Option Nat :=
  if a + b ≤ usizeMax w then some (a + b) else none

noncomputable def checkedSubW (a b : Nat) : Option Nat :=
  if b ≤ a then some (a - b) else none

noncomputable def checkedMulW (w a b : Nat) : Option Nat :=
  if a * b ≤ usizeMax w then some (a * b) else none

structure ZcTrailingSliceLayout where
  offset : Nat
  elemSize : Nat
  sizeBase : Nat
  sizeAlign : Nat
  sizePhase : Nat

noncomputable def zcWellFormed (t : ZcTrailingSliceLayout) : Prop :=
  0 < t.sizeAlign ∧ t.sizePhase < t.sizeAlign ∧ t.sizeAlign ∣ t.sizeBase

noncomputable def mathObjSize (t : ZcTrailingSliceLayout) (elems : Nat) : Nat :=
  t.sizeBase + roundUpNat (t.sizePhase + elems * t.elemSize) t.sizeAlign

noncomputable def mathObjBytesSize (t : ZcTrailingSliceLayout) (trailingBytes : Nat) : Nat :=
  t.sizeBase + roundUpNat (t.sizePhase + trailingBytes) t.sizeAlign

noncomputable def zcRoundedPhase (t : ZcTrailingSliceLayout) : Nat :=
  if t.sizePhase = 0 then 0 else t.sizeAlign

noncomputable def zcMaxTrailingBytes (w : Nat) (t : ZcTrailingSliceLayout) (avail : Nat) : Option Nat :=
  let rp := zcRoundedPhase t
  match checkedAddW w t.sizeBase rp with
  | none => none
  | some minSize =>
    match checkedSubW avail minSize with
    | none => none
    | some extraBytes =>
      let alignedBytes := roundDownNat extraBytes t.sizeAlign
      let initPad := rp - t.sizePhase
      some (alignedBytes + initPad)

noncomputable def zcSizeForElems (w : Nat) (t : ZcTrailingSliceLayout) (elems : Nat) : Option Nat :=
  match zcMaxTrailingBytes w t (usizeMax w) with
  | none => none
  | some maxTrailing =>
    match checkedMulW w elems t.elemSize with
    | none => none
    | some trailingBytes =>
      if trailingBytes ≤ maxTrailing then
        some (t.sizeBase + roundUpNat (t.sizePhase + trailingBytes) t.sizeAlign)
      else
        none

noncomputable def zcMaxTrailingSliceLen (w : Nat) (t : ZcTrailingSliceLayout) : Nat :=
  if t.elemSize = 0 then
    usizeMax w
  else
    match zcMaxTrailingBytes w t (isizeMax w) with
    | none => 0
    | some maxTrailing => maxTrailing / t.elemSize

noncomputable def zcIsValidMetadata (w : Nat) (t : ZcTrailingSliceLayout) (elems : Nat) : Bool :=
  if elems ≤ usizeMax w then
    if t.elemSize = 0 then
      match zcMaxTrailingBytes w t (isizeMax w) with
      | none => false
      | some _ => true
    else
      match zcMaxTrailingBytes w t (isizeMax w) with
      | none => false
      | some maxTrailing => decide (elems ≤ maxTrailing / t.elemSize)
  else
    false

theorem zcRoundedPhase_eq_roundUp {t : ZcTrailingSliceLayout}
    (ha : 0 < t.sizeAlign) (hp : t.sizePhase < t.sizeAlign) :
    zcRoundedPhase t = roundUpNat t.sizePhase t.sizeAlign := by
  simp only [zcRoundedPhase]
  cases Nat.eq_zero_or_pos t.sizePhase with
  | inl hp0 =>
    simp only [hp0, ite_true]
    exact (roundUpNat_zero t.sizeAlign).symm
  | inr hppos =>
    have hpne : t.sizePhase ≠ 0 := Nat.ne_of_gt hppos
    simp only [ite_eq_right hpne]
    apply Eq.symm
    apply isLeastAlignedGe_unique (roundUpNat_isLeast ha)
    refine ⟨Nat.le_of_lt hp, Nat.dvd_refl t.sizeAlign, ?_⟩
    intro m hm hdvd
    rcases hdvd with ⟨q, rfl⟩
    cases q with
    | zero =>
      simp only [Nat.mul_zero, Nat.le_zero] at hm
      rw [hm] at hppos
      exact False.elim (Nat.lt_irrefl 0 hppos)
    | succ q' =>
      have h1 : 1 ≤ q' + 1 := Nat.succ_le_succ (Nat.zero_le q')
      calc
        t.sizeAlign = t.sizeAlign * 1 := (Nat.mul_one t.sizeAlign).symm
        _ ≤ t.sizeAlign * (q' + 1) := Nat.mul_le_mul_left t.sizeAlign h1

theorem zcRoundedPhase_ge_phase {t : ZcTrailingSliceLayout}
    (ha : 0 < t.sizeAlign) (hp : t.sizePhase < t.sizeAlign) :
    t.sizePhase ≤ zcRoundedPhase t := by
  rw [zcRoundedPhase_eq_roundUp ha hp]
  exact roundUpNat_ge ha

theorem roundUpNat_phase_plus_bytes_le_iff {phase bytes align k : Nat}
    (ha : 0 < align) (_hp : phase < align) (hk_dvd : align ∣ k) (hk_ge : roundUpNat phase align ≤ k) :
    roundUpNat (phase + bytes) align ≤ k ↔ bytes ≤ (k - roundUpNat phase align) + (roundUpNat phase align - phase) := by
  have hp_le_rp : phase ≤ roundUpNat phase align := roundUpNat_ge ha
  have hrp_plus : (k - roundUpNat phase align) + (roundUpNat phase align - phase) = k - phase := by
    calc
      (k - roundUpNat phase align) + (roundUpNat phase align - phase)
          = ((k - roundUpNat phase align) + roundUpNat phase align) - phase :=
            (Nat.add_sub_assoc hp_le_rp (k - roundUpNat phase align)).symm
      _ = k - phase := by rw [Nat.sub_add_cancel hk_ge]
  rw [hrp_plus]
  constructor
  · intro hru
    have hsum : phase + bytes ≤ k := Nat.le_trans (roundUpNat_ge ha) hru
    exact Nat.le_sub_of_add_le' hsum
  · intro hb
    have hsum : phase + bytes ≤ k := by
      have hk_ge_p : phase ≤ k := Nat.le_trans hp_le_rp hk_ge
      have := Nat.add_le_add_left hb phase
      rwa [Nat.add_sub_cancel' hk_ge_p] at this
    exact roundUpNat_minimal ha hsum hk_dvd

theorem zcMaxTrailingBytes_some_spec {w : Nat} {t : ZcTrailingSliceLayout} {avail maxB : Nat}
    (hwf : zcWellFormed t)
    (hav : avail ≤ usizeMax w)
    (hsome : zcMaxTrailingBytes w t avail = some maxB) :
    mathObjBytesSize t maxB ≤ avail ∧
      ∀ b : Nat, mathObjBytesSize t b ≤ avail → b ≤ maxB := by
  rcases hwf with ⟨ha, hp, _⟩
  simp only [zcMaxTrailingBytes] at hsome
  have hrp_eq : zcRoundedPhase t = roundUpNat t.sizePhase t.sizeAlign :=
    zcRoundedPhase_eq_roundUp ha hp
  cases hadd : checkedAddW w t.sizeBase (zcRoundedPhase t) with
  | none =>
    simp [hadd] at hsome
  | some minSize =>
    simp only [hadd] at hsome
    simp only [checkedAddW] at hadd
    cases Nat.lt_or_ge (usizeMax w) (t.sizeBase + zcRoundedPhase t) with
    | inl hgt =>
      rw [ite_eq_right (Nat.not_le_of_gt hgt)] at hadd
      contradiction
    | inr hle =>
      rw [ite_eq_left hle] at hadd
      injection hadd with hmin_eq_raw
      cases hsub : checkedSubW avail minSize with
      | none =>
        simp [hsub] at hsome
      | some extraBytes =>
        simp only [hsub, Option.some.injEq] at hsome
        simp only [checkedSubW] at hsub
        cases Nat.lt_or_ge avail minSize with
        | inl hlt =>
          rw [ite_eq_right (Nat.not_le_of_gt hlt)] at hsub
          contradiction
        | inr hge =>
          rw [ite_eq_left hge] at hsub
          injection hsub with hextra_eq
          subst hmin_eq_raw
          subst hextra_eq
          subst hsome
          have _ := hav
          have hp_le_rp : t.sizePhase ≤ zcRoundedPhase t := zcRoundedPhase_ge_phase ha hp
          have hmin_eq : t.sizeBase + roundUpNat t.sizePhase t.sizeAlign = t.sizeBase + zcRoundedPhase t := by
            rw [hrp_eq]
          have hextra_ge : roundUpNat t.sizePhase t.sizeAlign ≤
              roundUpNat t.sizePhase t.sizeAlign + roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign :=
            Nat.le_add_right _ _
          have hrp_dvd : t.sizeAlign ∣ roundUpNat t.sizePhase t.sizeAlign := roundUpNat_dvd _ ha
          have hrd_dvd : t.sizeAlign ∣ roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign :=
            roundDownNat_dvd _ _
          have hk_dvd : t.sizeAlign ∣ (roundUpNat t.sizePhase t.sizeAlign + roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign) :=
            Nat.dvd_add hrp_dvd hrd_dvd
          have hk_sub : (roundUpNat t.sizePhase t.sizeAlign + roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign) -
              roundUpNat t.sizePhase t.sizeAlign = roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign := by
            rw [Nat.add_comm]
            exact Nat.add_sub_cancel _ _
          have h_iff : ∀ b : Nat,
              roundUpNat (t.sizePhase + b) t.sizeAlign ≤
                roundUpNat t.sizePhase t.sizeAlign + roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign ↔
              b ≤ roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign + (zcRoundedPhase t - t.sizePhase) := by
            intro b
            have hequiv := roundUpNat_phase_plus_bytes_le_iff
              (phase := t.sizePhase) (bytes := b) (align := t.sizeAlign)
              (k := roundUpNat t.sizePhase t.sizeAlign + roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign)
              ha hp hk_dvd hextra_ge
            rw [hk_sub] at hequiv
            have hgoal_rhs :
                roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign + (roundUpNat t.sizePhase t.sizeAlign - t.sizePhase) =
                roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign + (zcRoundedPhase t - t.sizePhase) := by
              rw [← hrp_eq]
            rwa [hgoal_rhs] at hequiv
          have h_fit_max : mathObjBytesSize t (roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign + (zcRoundedPhase t - t.sizePhase)) ≤ avail := by
            simp only [mathObjBytesSize]
            have hru_le : roundUpNat (t.sizePhase + (roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign + (zcRoundedPhase t - t.sizePhase))) t.sizeAlign ≤
                roundUpNat t.sizePhase t.sizeAlign + roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign :=
              (h_iff _).2 (Nat.le_refl _)
            have hstep1 : t.sizeBase + roundUpNat (t.sizePhase + (roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign + (zcRoundedPhase t - t.sizePhase))) t.sizeAlign ≤
                t.sizeBase + (roundUpNat t.sizePhase t.sizeAlign + roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign) :=
              Nat.add_le_add_left hru_le t.sizeBase
            have hstep2 : t.sizeBase + (roundUpNat t.sizePhase t.sizeAlign + roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign) ≤ avail := by
              rw [← Nat.add_assoc, hmin_eq]
              have hrd_le := roundDownNat_le (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign
              have hsum_le : (t.sizeBase + zcRoundedPhase t) + roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign ≤
                  (t.sizeBase + zcRoundedPhase t) + (avail - (t.sizeBase + zcRoundedPhase t)) :=
                Nat.add_le_add_left hrd_le _
              rwa [Nat.add_sub_cancel' hge] at hsum_le
            exact Nat.le_trans hstep1 hstep2
          refine ⟨h_fit_max, ?_⟩
          intro b hb_fit
          simp only [mathObjBytesSize] at hb_fit
          have hsub_le : roundUpNat (t.sizePhase + b) t.sizeAlign ≤ avail - t.sizeBase :=
            Nat.le_sub_of_add_le' hb_fit
          have h_extra_le : roundUpNat (t.sizePhase + b) t.sizeAlign - roundUpNat t.sizePhase t.sizeAlign ≤
              avail - (t.sizeBase + zcRoundedPhase t) := by
            have h1 : roundUpNat t.sizePhase t.sizeAlign ≤ roundUpNat (t.sizePhase + b) t.sizeAlign :=
              roundUpNat_monotone ha (Nat.le_add_right t.sizePhase b)
            have hsum_avail : (t.sizeBase + zcRoundedPhase t) + (roundUpNat (t.sizePhase + b) t.sizeAlign - roundUpNat t.sizePhase t.sizeAlign) ≤ avail := by
              rw [← hmin_eq, Nat.add_assoc, Nat.add_sub_cancel' h1]
              have hbase_le : t.sizeBase ≤ avail := Nat.le_trans (Nat.le_add_right t.sizeBase _) hge
              have := Nat.add_le_add_left hsub_le t.sizeBase
              rwa [Nat.add_sub_cancel' hbase_le] at this
            exact Nat.le_sub_of_add_le' hsum_avail
          have hdvd_diff : t.sizeAlign ∣ (roundUpNat (t.sizePhase + b) t.sizeAlign - roundUpNat t.sizePhase t.sizeAlign) :=
            Nat.dvd_sub (roundUpNat_dvd _ ha) (roundUpNat_dvd _ ha)
          have hrd_ge : roundUpNat (t.sizePhase + b) t.sizeAlign - roundUpNat t.sizePhase t.sizeAlign ≤
              roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign :=
            roundDownNat_greatest ha h_extra_le hdvd_diff
          have h1 : roundUpNat t.sizePhase t.sizeAlign ≤ roundUpNat (t.sizePhase + b) t.sizeAlign :=
            roundUpNat_monotone ha (Nat.le_add_right t.sizePhase b)
          have hle_sum : roundUpNat (t.sizePhase + b) t.sizeAlign ≤
              roundUpNat t.sizePhase t.sizeAlign + roundDownNat (avail - (t.sizeBase + zcRoundedPhase t)) t.sizeAlign := by
            have := Nat.add_le_add_left hrd_ge (roundUpNat t.sizePhase t.sizeAlign)
            rwa [Nat.add_sub_cancel' h1] at this
          exact (h_iff b).1 hle_sum

theorem zcMaxTrailingBytes_none_spec {w : Nat} {t : ZcTrailingSliceLayout} {avail : Nat}
    (hwf : zcWellFormed t)
    (hav : avail ≤ usizeMax w)
    (hnone : zcMaxTrailingBytes w t avail = none) :
    ∀ b : Nat, avail < mathObjBytesSize t b := by
  rcases hwf with ⟨ha, hp, _⟩
  intro b
  simp only [zcMaxTrailingBytes] at hnone
  have hrp_eq : zcRoundedPhase t = roundUpNat t.sizePhase t.sizeAlign :=
    zcRoundedPhase_eq_roundUp ha hp
  have hmono : mathObjBytesSize t 0 ≤ mathObjBytesSize t b := by
    simp only [mathObjBytesSize, Nat.add_zero]
    exact Nat.add_le_add_left (roundUpNat_monotone ha (Nat.le_add_right t.sizePhase b)) t.sizeBase
  have h0_eq : mathObjBytesSize t 0 = t.sizeBase + zcRoundedPhase t := by
    simp only [mathObjBytesSize, Nat.add_zero, hrp_eq]
  cases hadd : checkedAddW w t.sizeBase (zcRoundedPhase t) with
  | none =>
    simp only [checkedAddW] at hadd
    cases Nat.lt_or_ge (usizeMax w) (t.sizeBase + zcRoundedPhase t) with
    | inl hlt =>
      have hlt_av : avail < t.sizeBase + zcRoundedPhase t := Nat.lt_of_le_of_lt hav hlt
      rw [← h0_eq] at hlt_av
      exact Nat.lt_of_lt_of_le hlt_av hmono
    | inr hle =>
      rw [ite_eq_left hle] at hadd
      contradiction
  | some minSize =>
    simp only [hadd] at hnone
    simp only [checkedAddW] at hadd
    cases Nat.lt_or_ge (usizeMax w) (t.sizeBase + zcRoundedPhase t) with
    | inl hgt =>
      rw [ite_eq_right (Nat.not_le_of_gt hgt)] at hadd
      contradiction
    | inr hle =>
      rw [ite_eq_left hle] at hadd
      injection hadd with hmin_eq_raw
      cases hsub : checkedSubW avail minSize with
      | none =>
        simp only [checkedSubW] at hsub
        cases Nat.lt_or_ge avail minSize with
        | inl hlt_av =>
          rw [← hmin_eq_raw, ← h0_eq] at hlt_av
          exact Nat.lt_of_lt_of_le hlt_av hmono
        | inr hge_av =>
          rw [ite_eq_left hge_av] at hsub
          contradiction
      | some extraBytes =>
        simp [hsub] at hnone

theorem zcSizeForElems_some_iff {w : Nat} {t : ZcTrailingSliceLayout} {elems s : Nat}
    (hwf : zcWellFormed t)
    (he : elems ≤ usizeMax w) :
    zcSizeForElems w t elems = some s ↔
      (mathObjSize t elems ≤ usizeMax w ∧ s = mathObjSize t elems) := by
  have h_le_size : ∀ b : Nat, b ≤ mathObjBytesSize t b := by
    intro b
    rcases hwf with ⟨ha, _, _⟩
    simp only [mathObjBytesSize]
    have h1 : b ≤ t.sizePhase + b := Nat.le_add_left b t.sizePhase
    have h2 : t.sizePhase + b ≤ roundUpNat (t.sizePhase + b) t.sizeAlign := roundUpNat_ge ha
    exact Nat.le_trans (Nat.le_trans h1 h2) (Nat.le_add_left _ t.sizeBase)
  constructor
  · intro hsome
    simp only [zcSizeForElems] at hsome
    cases hmax : zcMaxTrailingBytes w t (usizeMax w) with
    | none => simp [hmax] at hsome
    | some maxTrailing =>
      simp only [hmax] at hsome
      have hspec := zcMaxTrailingBytes_some_spec hwf (Nat.le_refl _) hmax
      cases hmul : checkedMulW w elems t.elemSize with
      | none => simp [hmul] at hsome
      | some trailingBytes =>
        simp only [hmul] at hsome
        simp only [checkedMulW] at hmul
        cases Nat.lt_or_ge (usizeMax w) (elems * t.elemSize) with
        | inl hgt =>
          rw [ite_eq_right (Nat.not_le_of_gt hgt)] at hmul
          contradiction
        | inr hle =>
          rw [ite_eq_left hle] at hmul
          injection hmul with hmul_eq
          subst hmul_eq
          cases Nat.lt_or_ge maxTrailing (elems * t.elemSize) with
          | inl hgt =>
            rw [ite_eq_right (Nat.not_le_of_gt hgt)] at hsome
            contradiction
          | inr hfit =>
            rw [ite_eq_left hfit] at hsome
            injection hsome with hs_eq
            subst hs_eq
            refine ⟨?_, rfl⟩
            have hle_max : mathObjBytesSize t (elems * t.elemSize) ≤ mathObjBytesSize t maxTrailing := by
              rcases hwf with ⟨ha, _, _⟩
              simp only [mathObjBytesSize]
              exact Nat.add_le_add_left (roundUpNat_monotone ha (Nat.add_le_add_left hfit t.sizePhase)) t.sizeBase
            exact Nat.le_trans hle_max hspec.1
  · rintro ⟨hfit, rfl⟩
    have _ := he
    simp only [zcSizeForElems]
    cases hmax : zcMaxTrailingBytes w t (usizeMax w) with
    | none =>
      have hnone := zcMaxTrailingBytes_none_spec hwf (Nat.le_refl _) hmax (elems * t.elemSize)
      have hcontra := Nat.lt_of_le_of_lt hfit hnone
      exact False.elim (Nat.lt_irrefl _ hcontra)
    | some maxTrailing =>
      have hspec := zcMaxTrailingBytes_some_spec hwf (Nat.le_refl _) hmax
      have hmul_le : elems * t.elemSize ≤ usizeMax w :=
        Nat.le_trans (h_le_size (elems * t.elemSize)) hfit
      have hmul_t : checkedMulW w elems t.elemSize = some (elems * t.elemSize) := by
        simp [checkedMulW, hmul_le]
      have hle_max : elems * t.elemSize ≤ maxTrailing := hspec.2 (elems * t.elemSize) hfit
      simp only [hmul_t, ite_eq_left hle_max]
      rfl

theorem zcSizeForElems_none_iff {w : Nat} {t : ZcTrailingSliceLayout} {elems : Nat}
    (hwf : zcWellFormed t)
    (he : elems ≤ usizeMax w) :
    zcSizeForElems w t elems = none ↔ usizeMax w < mathObjSize t elems := by
  constructor
  · intro hnone
    cases Nat.lt_or_ge (usizeMax w) (mathObjSize t elems) with
    | inl hlt => exact hlt
    | inr hfit =>
      have hsome := (zcSizeForElems_some_iff hwf he).2 ⟨hfit, rfl⟩
      rw [hnone] at hsome
      contradiction
  · intro hgt
    cases hres : zcSizeForElems w t elems with
    | none => rfl
    | some s =>
      have hfit := ((zcSizeForElems_some_iff hwf he).1 hres).1
      exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hfit hgt))

theorem zcIsValidMetadata_iff_le_isizeMax {w : Nat} {t : ZcTrailingSliceLayout} {elems : Nat}
    (hwf : zcWellFormed t)
    (he : elems ≤ usizeMax w) :
    zcIsValidMetadata w t elems = true ↔ mathObjSize t elems ≤ isizeMax w := by
  have hisize_le_usize : isizeMax w ≤ usizeMax w := isizeMax_le_usizeMax w
  simp only [zcIsValidMetadata, ite_eq_left he]
  cases Nat.eq_zero_or_pos t.elemSize with
  | inl he0 =>
    simp only [he0, ite_true]
    have hobj0 : mathObjSize t elems = mathObjBytesSize t 0 := by
      simp [mathObjSize, mathObjBytesSize, he0]
    cases hmax : zcMaxTrailingBytes w t (isizeMax w) with
    | none =>
      have hnone := zcMaxTrailingBytes_none_spec hwf hisize_le_usize hmax 0
      rw [← hobj0] at hnone
      constructor
      · intro h; contradiction
      · intro hle
        exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle hnone))
    | some maxTrailing =>
      have hspec := zcMaxTrailingBytes_some_spec hwf hisize_le_usize hmax
      have hmono0 : mathObjBytesSize t 0 ≤ mathObjBytesSize t maxTrailing := by
        rcases hwf with ⟨ha, _, _⟩
        simp only [mathObjBytesSize]
        exact Nat.add_le_add_left (roundUpNat_monotone ha (Nat.add_le_add_left (Nat.zero_le maxTrailing) t.sizePhase)) t.sizeBase
      have hfit0 : mathObjSize t elems ≤ isizeMax w := by
        rw [hobj0]
        exact Nat.le_trans hmono0 hspec.1
      simp [hfit0]
  | inr hepos =>
    have hene : t.elemSize ≠ 0 := Nat.ne_of_gt hepos
    simp only [ite_eq_right hene]
    cases hmax : zcMaxTrailingBytes w t (isizeMax w) with
    | none =>
      have hnone := zcMaxTrailingBytes_none_spec hwf hisize_le_usize hmax (elems * t.elemSize)
      constructor
      · intro h; contradiction
      · intro hle
        exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle hnone))
    | some maxTrailing =>
      have hspec := zcMaxTrailingBytes_some_spec hwf hisize_le_usize hmax
      simp only [decide_eq_true_eq]
      constructor
      · intro hdiv
        have hmul_le : elems * t.elemSize ≤ maxTrailing := by
          have hmul1 : elems * t.elemSize ≤ (maxTrailing / t.elemSize) * t.elemSize :=
            Nat.mul_le_mul_right t.elemSize hdiv
          have hmul2 : (maxTrailing / t.elemSize) * t.elemSize ≤ maxTrailing := by
            rw [Nat.mul_comm]
            exact Nat.mul_div_le maxTrailing t.elemSize
          exact Nat.le_trans hmul1 hmul2
        have hmono : mathObjSize t elems ≤ mathObjBytesSize t maxTrailing := by
          rcases hwf with ⟨ha, _, _⟩
          simp only [mathObjSize, mathObjBytesSize]
          exact Nat.add_le_add_left (roundUpNat_monotone ha (Nat.add_le_add_left hmul_le t.sizePhase)) t.sizeBase
        exact Nat.le_trans hmono hspec.1
      · intro hfit
        have hmul_le : elems * t.elemSize ≤ maxTrailing := hspec.2 (elems * t.elemSize) hfit
        exact (Nat.le_div_iff_mul_le hepos).2 hmul_le

theorem zcIsValidMetadata_implies_sizeForElems_some {w : Nat} {t : ZcTrailingSliceLayout} {elems : Nat}
    (hwf : zcWellFormed t)
    (he : elems ≤ usizeMax w)
    (hval : zcIsValidMetadata w t elems = true) :
    ∃ s : Nat, s ≤ isizeMax w ∧ zcSizeForElems w t elems = some s := by
  have hfit_isize : mathObjSize t elems ≤ isizeMax w :=
    (zcIsValidMetadata_iff_le_isizeMax hwf he).1 hval
  have hfit_usize : mathObjSize t elems ≤ usizeMax w :=
    Nat.le_trans hfit_isize (isizeMax_le_usizeMax w)
  have hsome : zcSizeForElems w t elems = some (mathObjSize t elems) :=
    (zcSizeForElems_some_iff hwf he).2 ⟨hfit_usize, rfl⟩
  exact ⟨mathObjSize t elems, hfit_isize, hsome⟩

-- Separation Witness 1: `[u8]` with `elems = usizeMax 64` fits in `usize` (`Some(2^64 - 1)`), yet fails `is_valid_metadata` (`false`)!
noncomputable def zcSliceU8 : ZcTrailingSliceLayout := ⟨0, 1, 0, 1, 0⟩
noncomputable def zcSliceU32 : ZcTrailingSliceLayout := ⟨0, 4, 0, 4, 0⟩
noncomputable def zcSliceZst : ZcTrailingSliceLayout := ⟨0, 0, 0, 1, 0⟩
noncomputable def zcPktU32 : ZcTrailingSliceLayout := ⟨4, 4, 4, 4, 0⟩
noncomputable def zcPktU8 : ZcTrailingSliceLayout := ⟨1, 1, 1, 1, 0⟩
noncomputable def zcH6U8 : ZcTrailingSliceLayout := ⟨6, 1, 4, 4, 2⟩
noncomputable def zcPacked2U32 : ZcTrailingSliceLayout := ⟨2, 4, 2, 2, 0⟩

theorem zc_u8_usize_max_size_some_but_invalid_witness :
    zcSizeForElems 64 zcSliceU8 (usizeMax 64) = some (usizeMax 64) ∧
      zcIsValidMetadata 64 zcSliceU8 (usizeMax 64) = false := by
  refine ⟨rfl, rfl⟩

theorem zc_u32_3_and_overflow_witness :
    zcSizeForElems 64 zcSliceU32 3 = some 12 ∧
      zcSizeForElems 64 zcSliceU32 (usizeMax 64) = none ∧
      zcIsValidMetadata 64 zcSliceU32 3 = true ∧
      zcIsValidMetadata 64 zcSliceU32 (usizeMax 64) = false := by
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem zc_zst_usize_max_valid_witness :
    zcSizeForElems 64 zcSliceZst (usizeMax 64) = some 0 ∧
      zcIsValidMetadata 64 zcSliceZst (usizeMax 64) = true := by
  refine ⟨rfl, rfl⟩

theorem zc_custom_dst_specimens :
    zcSizeForElems 64 zcPktU32 3 = some 16 ∧
      zcSizeForElems 64 zcPktU32 0 = some 4 ∧
      zcSizeForElems 64 zcPktU32 (usizeMax 64) = none ∧
      zcSizeForElems 64 zcPktU8 3 = some 4 ∧
      zcSizeForElems 64 zcH6U8 3 = some 12 ∧
      zcSizeForElems 64 zcH6U8 0 = some 8 ∧
      zcSizeForElems 64 zcPacked2U32 3 = some 14 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 6: Normalized Bridge Between `rustc` `CustomDstSpec` and `zerocopy` `TrailingSliceLayout` -/

noncomputable def normalizeCustomDstToZc (spec : CustomDstSpec) (elemSize elemAlign : Nat) :
    ZcTrailingSliceLayout :=
  let effTail := effectiveTailAlign spec ⟨elemSize, elemAlign⟩
  let fullA := max spec.prefixAlign effTail
  let unadjOff := alignToNat spec.unsizedOffsetUnadj effTail
  let base := roundDownNat unadjOff fullA
  let phase := unadjOff % fullA
  ⟨unadjOff, elemSize, base, fullA, phase⟩

theorem normalizeCustomDstToZc_wellFormed (spec : CustomDstSpec) (elemSize elemAlign : Nat)
    (hpref : isPow2 spec.prefixAlign)
    (helem : isPow2 elemAlign)
    (hp : validPackCap spec.packCap) :
    zcWellFormed (normalizeCustomDstToZc spec elemSize elemAlign) := by
  have heff := effectiveTailAlign_isPow2 spec ⟨elemSize, elemAlign⟩ helem hp
  have hfull := isPow2_pos (max_pow2_isPow2 hpref heff)
  simp only [normalizeCustomDstToZc, zcWellFormed]
  refine ⟨hfull, Nat.mod_lt _ hfull, roundDownNat_dvd _ _⟩

theorem normalizeCustomDstToZc_math_equiv_rustc (spec : CustomDstSpec) (elemSize elemAlign elems : Nat)
    (hpref : isPow2 spec.prefixAlign)
    (helem : isPow2 elemAlign)
    (hp : validPackCap spec.packCap)
    (hdvd : elemAlign ∣ elemSize) :
    mathObjSize (normalizeCustomDstToZc spec elemSize elemAlign) elems =
      (sizeAndAlignRustc spec ⟨elems * elemSize, elemAlign⟩).1 := by
  have heff_pow2 := effectiveTailAlign_isPow2 spec ⟨elemSize, elemAlign⟩ helem hp
  have hfull_pow2 := max_pow2_isPow2 hpref heff_pow2
  have hfull_pos := isPow2_pos hfull_pow2
  have h_twostep := sizeAndAlignRustc_eq_twoStep spec ⟨elems * elemSize, elemAlign⟩ hpref helem hp
    (Nat.dvd_mul_left_of_dvd hdvd elems)
  rw [h_twostep]
  simp only [effectiveTailAlign] at hfull_pos
  simp only [sizeAndAlignTwoStep, normalizeCustomDstToZc, mathObjSize, effectiveTailAlign]
  rw [← roundUpNat_eq_alignToNat (a := max spec.prefixAlign (applyPackCap elemAlign spec.packCap)) hfull_pos]
  have h_base_dvd := roundDownNat_dvd (alignToNat spec.unsizedOffsetUnadj (applyPackCap elemAlign spec.packCap))
    (max spec.prefixAlign (applyPackCap elemAlign spec.packCap))
  have h_decomp :
      roundDownNat (alignToNat spec.unsizedOffsetUnadj (applyPackCap elemAlign spec.packCap))
          (max spec.prefixAlign (applyPackCap elemAlign spec.packCap)) +
        alignToNat spec.unsizedOffsetUnadj (applyPackCap elemAlign spec.packCap) %
          max spec.prefixAlign (applyPackCap elemAlign spec.packCap) =
      alignToNat spec.unsizedOffsetUnadj (applyPackCap elemAlign spec.packCap) := by
    rw [roundDownNat_eq hfull_pos, Nat.mul_comm]
    exact Nat.div_add_mod _ _
  calc
    roundDownNat (alignToNat spec.unsizedOffsetUnadj (applyPackCap elemAlign spec.packCap))
          (max spec.prefixAlign (applyPackCap elemAlign spec.packCap)) +
        roundUpNat
          (alignToNat spec.unsizedOffsetUnadj (applyPackCap elemAlign spec.packCap) %
              max spec.prefixAlign (applyPackCap elemAlign spec.packCap) +
            elems * elemSize)
          (max spec.prefixAlign (applyPackCap elemAlign spec.packCap))
        = roundUpNat
            ((alignToNat spec.unsizedOffsetUnadj (applyPackCap elemAlign spec.packCap) %
                max spec.prefixAlign (applyPackCap elemAlign spec.packCap) +
              elems * elemSize) +
              roundDownNat (alignToNat spec.unsizedOffsetUnadj (applyPackCap elemAlign spec.packCap))
                (max spec.prefixAlign (applyPackCap elemAlign spec.packCap)))
            (max spec.prefixAlign (applyPackCap elemAlign spec.packCap)) := by
          rw [roundUpNat_add_of_dvd hfull_pos h_base_dvd, Nat.add_comm]
    _ = roundUpNat (alignToNat spec.unsizedOffsetUnadj (applyPackCap elemAlign spec.packCap) + elems * elemSize)
          (max spec.prefixAlign (applyPackCap elemAlign spec.packCap)) := by
          have h_re :
              (alignToNat spec.unsizedOffsetUnadj (applyPackCap elemAlign spec.packCap) %
                  max spec.prefixAlign (applyPackCap elemAlign spec.packCap) +
                elems * elemSize) +
                roundDownNat (alignToNat spec.unsizedOffsetUnadj (applyPackCap elemAlign spec.packCap))
                  (max spec.prefixAlign (applyPackCap elemAlign spec.packCap)) =
              alignToNat spec.unsizedOffsetUnadj (applyPackCap elemAlign spec.packCap) + elems * elemSize := by
            calc
              (alignToNat spec.unsizedOffsetUnadj (applyPackCap elemAlign spec.packCap) %
                    max spec.prefixAlign (applyPackCap elemAlign spec.packCap) +
                  elems * elemSize) +
                  roundDownNat (alignToNat spec.unsizedOffsetUnadj (applyPackCap elemAlign spec.packCap))
                    (max spec.prefixAlign (applyPackCap elemAlign spec.packCap))
                  = (roundDownNat (alignToNat spec.unsizedOffsetUnadj (applyPackCap elemAlign spec.packCap))
                        (max spec.prefixAlign (applyPackCap elemAlign spec.packCap)) +
                      alignToNat spec.unsizedOffsetUnadj (applyPackCap elemAlign spec.packCap) %
                        max spec.prefixAlign (applyPackCap elemAlign spec.packCap)) +
                    elems * elemSize := by
                    rw [Nat.add_comm (alignToNat _ _ % _) (elems * elemSize)]
                    rw [Nat.add_assoc, Nat.add_comm (elems * elemSize) _]
                    exact congrArg (· + elems * elemSize) (Nat.add_comm _ _)
              _ = alignToNat spec.unsizedOffsetUnadj (applyPackCap elemAlign spec.packCap) + elems * elemSize := by
                    rw [h_decomp]
          rw [h_re]

theorem normalizeCustomDstToZc_zcSizeForElems_eq_rustc {w : Nat}
    (spec : CustomDstSpec) (elemSize elemAlign elems : Nat)
    (hpref : isPow2 spec.prefixAlign)
    (helem : isPow2 elemAlign)
    (hp : validPackCap spec.packCap)
    (hdvd : elemAlign ∣ elemSize)
    (he : elems ≤ usizeMax w)
    (hfit : (sizeAndAlignRustc spec ⟨elems * elemSize, elemAlign⟩).1 ≤ usizeMax w) :
    zcSizeForElems w (normalizeCustomDstToZc spec elemSize elemAlign) elems =
      some (sizeAndAlignRustc spec ⟨elems * elemSize, elemAlign⟩).1 := by
  have hwf := normalizeCustomDstToZc_wellFormed spec elemSize elemAlign hpref helem hp
  have heq := normalizeCustomDstToZc_math_equiv_rustc spec elemSize elemAlign elems hpref helem hp hdvd
  rw [zcSizeForElems_some_iff hwf he]
  exact ⟨by rwa [heq], heq.symm⟩

theorem normalize_h6_u8_eq_zcH6U8 :
    normalizeCustomDstToZc h6Spec 1 1 = zcH6U8 := by
  rfl

theorem normalize_pkt_u32_eq_zcPktU32 :
    normalizeCustomDstToZc pktSpec 4 4 = zcPktU32 := by
  rfl

theorem normalize_packed2_u32_eq_zcPacked2U32 :
    normalizeCustomDstToZc ⟨1, 1, some 2⟩ 4 4 = zcPacked2U32 := by
  rfl

end VerifiedRustc.WidePtrDstKnownLayout
