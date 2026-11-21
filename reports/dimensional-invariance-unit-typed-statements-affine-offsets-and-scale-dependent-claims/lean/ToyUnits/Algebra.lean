import ToyUnits.Scalar

/-!
# Derived algebra from the named laws

Standard consequences of `CommRingLaws`, `FieldLaws`, `OrderedFieldLaws` and `InvZeroLaw`,
together with natural and integer powers (`npow`, `zpow`) and finite products (`finProd`).
-/

namespace Toy.Units

variable {K : Type} [ScalarOps K]

/-- Natural powers: `npow a 0 = 1`, `npow a (n+1) = npow a n * a`. -/
def npow (a : K) : Nat → K
  | 0 => 1
  | n + 1 => npow a n * a

/-- Integer powers: `zpow a n = npow a n` for `n ≥ 0`, and `zpow a (-(n+1)) = (npow a (n+1))⁻¹`.
At `a = 0` and a negative exponent the value is `0⁻¹`, i.e. whatever the domain's inverse returns at 0. -/
def zpow (a : K) : Int → K
  | .ofNat n => npow a n
  | .negSucc n => (npow a (n + 1))⁻¹

/-- The product `f 0 * (f 1 * (... * 1))` over `Fin n`. -/
def finProd : (n : Nat) → (Fin n → K) → K
  | 0, _ => 1
  | n + 1, f => f 0 * finProd n (fun i => f i.succ)

/-- Induction principle for `Int` by successor and predecessor. -/
theorem int_induction (P : Int → Prop) (h0 : P 0) (hs : ∀ k, P k → P (k + 1))
    (hp : ∀ k, P k → P (k - 1)) : ∀ k, P k := by
  intro k
  cases k with
  | ofNat n =>
    induction n with
    | zero => exact h0
    | succ n ih =>
      have := hs _ ih
      have e : (Int.ofNat n : Int) + 1 = Int.ofNat (n + 1) := rfl
      rwa [e] at this
  | negSucc n =>
    induction n with
    | zero =>
      have := hp _ h0
      have e : (0 : Int) - 1 = Int.negSucc 0 := by omega
      rwa [e] at this
    | succ n ih =>
      have := hp _ ih
      have e : Int.negSucc n - 1 = Int.negSucc (n + 1) := by omega
      rwa [e] at this

section CommRing
variable (h : CommRingLaws K)
include h

theorem zero_add' (a : K) : 0 + a = a := by rw [h.add_comm]; exact h.add_zero a

theorem neg_add_cancel' (a : K) : -a + a = 0 := by rw [h.add_comm]; exact h.add_neg a

theorem add_left_cancel' {a b c : K} (e : a + b = a + c) : b = c := by
  have : -a + (a + b) = -a + (a + c) := by rw [e]
  rwa [← h.add_assoc, ← h.add_assoc, neg_add_cancel' h, zero_add' h, zero_add' h] at this

theorem add_right_cancel' {a b c : K} (e : a + c = b + c) : a = b := by
  rw [h.add_comm a, h.add_comm b] at e; exact add_left_cancel' h e

theorem mul_zero' (a : K) : a * 0 = 0 := by
  have e : a * 0 + a * 0 = a * 0 + 0 := by rw [← h.distrib, h.add_zero, h.add_zero]
  exact add_left_cancel' h e

theorem zero_mul' (a : K) : 0 * a = 0 := by rw [h.mul_comm]; exact mul_zero' h a

theorem one_mul' (a : K) : 1 * a = a := by rw [h.mul_comm]; exact h.mul_one a

theorem add_mul' (a b c : K) : (a + b) * c = a * c + b * c := by
  rw [h.mul_comm, h.distrib, h.mul_comm c, h.mul_comm c]

theorem neg_eq_of_add_eq_zero' {a b : K} (e : a + b = 0) : b = -a := by
  apply add_left_cancel' h (a := a); rw [e, h.add_neg]

theorem mul_neg' (a b : K) : a * -b = -(a * b) := by
  apply neg_eq_of_add_eq_zero' h; rw [← h.distrib, h.add_neg, mul_zero' h]

theorem neg_mul' (a b : K) : -a * b = -(a * b) := by
  rw [h.mul_comm, mul_neg' h, h.mul_comm]

theorem neg_neg' (a : K) : - -a = a := (neg_eq_of_add_eq_zero' h (neg_add_cancel' h a)).symm

theorem neg_zero' : -(0 : K) = 0 := (neg_eq_of_add_eq_zero' h (h.add_zero 0)).symm

theorem mul_left_comm' (a b c : K) : a * (b * c) = b * (a * c) := by
  rw [← h.mul_assoc, h.mul_comm a b, h.mul_assoc]

theorem mul_mul_mul_comm' (a b c d : K) : a * b * (c * d) = a * c * (b * d) := by
  rw [h.mul_assoc, mul_left_comm' h b c d, ← h.mul_assoc]

theorem npow_add (a : K) (m n : Nat) : npow a (m + n) = npow a m * npow a n := by
  induction n with
  | zero => simp only [Nat.add_zero, npow]; rw [h.mul_one]
  | succ n ih => rw [← Nat.add_assoc, npow, ih, npow, h.mul_assoc]

theorem npow_mul_base (a b : K) (n : Nat) : npow (a * b) n = npow a n * npow b n := by
  induction n with
  | zero => simp only [npow]; rw [h.mul_one]
  | succ n ih => simp only [npow]; rw [ih, mul_mul_mul_comm' h]

theorem npow_one_base (n : Nat) : npow (1 : K) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [npow]; rw [ih, h.mul_one]

theorem npow_one (a : K) : npow a 1 = a := by simp only [npow]; rw [one_mul' h]

theorem npow_zero_base_succ (n : Nat) : npow (0 : K) (n + 1) = 0 := by
  simp only [npow]; rw [mul_zero' h]

theorem npow_npow (a : K) (m n : Nat) : npow (npow a m) n = npow a (m * n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [npow, ih, Nat.mul_succ, npow_add h]

theorem finProd_mul (n : Nat) (f g : Fin n → K) :
    finProd n (fun i => f i * g i) = finProd n f * finProd n g := by
  induction n with
  | zero => simp only [finProd]; rw [h.mul_one]
  | succ n ih => simp only [finProd]; rw [ih, mul_mul_mul_comm' h]

theorem finProd_one (n : Nat) : finProd n (fun _ => (1 : K)) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finProd]; rw [ih, h.mul_one]

omit h in
theorem finProd_congr (n : Nat) (f g : Fin n → K) (e : ∀ i, f i = g i) :
    finProd n f = finProd n g := by
  have : f = g := funext e
  rw [this]

end CommRing

section Field
variable (h : FieldLaws K)
include h

theorem inv_mul_cancel' {a : K} (ha : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [h.mul_comm]; exact h.mul_inv a ha

theorem mul_eq_zero' {a b : K} (e : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    have : a⁻¹ * (a * b) = a⁻¹ * 0 := by rw [e]
    rwa [← h.mul_assoc, inv_mul_cancel' h ha, one_mul' h.toCommRingLaws,
      mul_zero' h.toCommRingLaws] at this

theorem mul_ne_zero' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro e; rcases mul_eq_zero' h e with e | e
  · exact ha e
  · exact hb e

theorem inv_ne_zero' {a : K} (ha : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro e
  have := h.mul_inv a ha
  rw [e, mul_zero' h.toCommRingLaws] at this
  exact h.zero_ne_one this

theorem one_ne_zero' : (1 : K) ≠ 0 := fun e => h.zero_ne_one e.symm

theorem eq_inv_of_mul_eq_one' {a b : K} (e : a * b = 1) : b = a⁻¹ := by
  have ha : a ≠ 0 := by
    intro ha; rw [ha, zero_mul' h.toCommRingLaws] at e; exact h.zero_ne_one e
  have : a⁻¹ * (a * b) = a⁻¹ * 1 := by rw [e]
  rwa [← h.mul_assoc, inv_mul_cancel' h ha, one_mul' h.toCommRingLaws, h.mul_one] at this

theorem inv_inv_of_ne_zero' {a : K} (ha : a ≠ 0) : a⁻¹⁻¹ = a :=
  (eq_inv_of_mul_eq_one' h (inv_mul_cancel' h ha)).symm

theorem inv_one' : (1 : K)⁻¹ = 1 :=
  (eq_inv_of_mul_eq_one' h (h.mul_one 1)).symm

theorem mul_inv_of_ne_zero' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  symm; apply eq_inv_of_mul_eq_one' h
  rw [mul_mul_mul_comm' h.toCommRingLaws, h.mul_inv a ha, h.mul_inv b hb, h.mul_one]

theorem mul_left_cancel₀' {a b c : K} (hc : c ≠ 0) (e : c * a = c * b) : a = b := by
  have : c⁻¹ * (c * a) = c⁻¹ * (c * b) := by rw [e]
  rwa [← h.mul_assoc, ← h.mul_assoc, inv_mul_cancel' h hc, one_mul' h.toCommRingLaws,
    one_mul' h.toCommRingLaws] at this

/-- With the convention `0⁻¹ = 0`, inversion distributes over every product. -/
theorem mul_inv' (hz : InvZeroLaw K) (a b : K) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  by_cases ha : a = 0
  · rw [ha, zero_mul' h.toCommRingLaws, hz, zero_mul' h.toCommRingLaws]
  by_cases hb : b = 0
  · rw [hb, mul_zero' h.toCommRingLaws, hz, mul_zero' h.toCommRingLaws]
  exact mul_inv_of_ne_zero' h ha hb

theorem inv_inv' (hz : InvZeroLaw K) (a : K) : a⁻¹⁻¹ = a := by
  by_cases ha : a = 0
  · rw [ha, hz, hz]
  · exact inv_inv_of_ne_zero' h ha

theorem npow_ne_zero {a : K} (ha : a ≠ 0) (n : Nat) : npow a n ≠ 0 := by
  induction n with
  | zero => exact one_ne_zero' h
  | succ n ih => exact mul_ne_zero' h ih ha

theorem zpow_ne_zero {a : K} (ha : a ≠ 0) (k : Int) : zpow a k ≠ 0 := by
  cases k with
  | ofNat n => exact npow_ne_zero h ha n
  | negSucc n => exact inv_ne_zero' h (npow_ne_zero h ha _)

theorem zpow_succ {a : K} (ha : a ≠ 0) (k : Int) : zpow a (k + 1) = zpow a k * a := by
  cases k with
  | ofNat n => rfl
  | negSucc n =>
    cases n with
    | zero =>
      have e : Int.negSucc 0 + 1 = Int.ofNat 0 := rfl
      rw [e]; simp only [zpow, npow]
      rw [one_mul' h.toCommRingLaws, inv_mul_cancel' h ha]
    | succ n =>
      have e : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
      rw [e]; simp only [zpow]
      rw [show npow a (n + 1 + 1) = npow a (n + 1) * a from rfl,
        mul_inv_of_ne_zero' h (npow_ne_zero h ha _) ha, h.mul_assoc,
        inv_mul_cancel' h ha, h.mul_one]

theorem zpow_pred {a : K} (ha : a ≠ 0) (k : Int) : zpow a (k - 1) = zpow a k * a⁻¹ := by
  have e := zpow_succ h ha (k - 1)
  rw [Int.sub_add_cancel] at e
  rw [e, h.mul_assoc, h.mul_inv a ha, h.mul_one]

theorem zpow_add {a : K} (ha : a ≠ 0) (j k : Int) : zpow a (j + k) = zpow a j * zpow a k := by
  revert k
  apply int_induction
  · rw [Int.add_zero]; simp only [zpow, npow]; rw [h.mul_one]
  · intro k ih
    rw [← Int.add_assoc, zpow_succ h ha, ih, zpow_succ h ha, h.mul_assoc]
  · intro k ih
    rw [show j + (k - 1) = (j + k) - 1 by omega, zpow_pred h ha, ih, zpow_pred h ha, h.mul_assoc]

theorem zpow_neg {a : K} (ha : a ≠ 0) (k : Int) : zpow a (-k) = (zpow a k)⁻¹ := by
  apply eq_inv_of_mul_eq_one' h
  rw [← zpow_add h ha, Int.add_right_neg]; rfl

theorem zpow_zpow {a : K} (ha : a ≠ 0) (j k : Int) : zpow (zpow a j) k = zpow a (k * j) := by
  revert k
  apply int_induction
  · rw [Int.zero_mul]; rfl
  · intro k ih
    rw [zpow_succ h (zpow_ne_zero h ha j), ih, Int.add_mul, Int.one_mul, zpow_add h ha]
  · intro k ih
    rw [zpow_pred h (zpow_ne_zero h ha j), ih, Int.sub_mul, Int.one_mul, Int.sub_eq_add_neg,
      zpow_add h ha, zpow_neg h ha]

theorem zpow_one (a : K) : zpow a 1 = a := npow_one h.toCommRingLaws a

omit h in
theorem zpow_zero (a : K) : zpow a 0 = 1 := rfl

theorem zpow_one_base (k : Int) : zpow (1 : K) k = 1 := by
  cases k with
  | ofNat n => exact npow_one_base h.toCommRingLaws n
  | negSucc n => simp only [zpow]; rw [npow_one_base h.toCommRingLaws, inv_one' h]

/-- With `0⁻¹ = 0`, integer powers distribute over every product. -/
theorem zpow_mul_base (hz : InvZeroLaw K) (a b : K) (k : Int) :
    zpow (a * b) k = zpow a k * zpow b k := by
  cases k with
  | ofNat n => exact npow_mul_base h.toCommRingLaws a b n
  | negSucc n => simp only [zpow]; rw [npow_mul_base h.toCommRingLaws, mul_inv' h hz]

theorem finProd_ne_zero (n : Nat) (f : Fin n → K) (hf : ∀ i, f i ≠ 0) : finProd n f ≠ 0 := by
  induction n with
  | zero => exact one_ne_zero' h
  | succ n ih => exact mul_ne_zero' h (hf 0) (ih _ (fun i => hf i.succ))

theorem finProd_inv (hz : InvZeroLaw K) (n : Nat) (f : Fin n → K) :
    (finProd n f)⁻¹ = finProd n (fun i => (f i)⁻¹) := by
  induction n with
  | zero => exact inv_one' h
  | succ n ih => simp only [finProd]; rw [mul_inv' h hz, ih]

theorem finProd_zpow (hz : InvZeroLaw K) (n : Nat) (f : Fin n → K) (k : Int) :
    zpow (finProd n f) k = finProd n (fun i => zpow (f i) k) := by
  induction n with
  | zero => exact zpow_one_base h k
  | succ n ih => simp only [finProd]; rw [zpow_mul_base h hz, ih]

end Field

section Ordered
variable (h : OrderedFieldLaws K)
include h

theorem le_of_lt' {a b : K} (hab : a < b) : a ≤ b := ((h.lt_iff a b).1 hab).1

theorem ne_of_lt' {a b : K} (hab : a < b) : a ≠ b := by
  intro e; subst e; exact ((h.lt_iff a a).1 hab).2 (h.le_refl a)

theorem lt_of_le_of_ne' {a b : K} (hab : a ≤ b) (hne : a ≠ b) : a < b := by
  refine (h.lt_iff a b).2 ⟨hab, fun hba => hne (h.le_antisymm a b hab hba)⟩

theorem sub_nonneg_of_le' {a b : K} (hab : a ≤ b) : 0 ≤ b + -a := by
  have := h.add_le_mono a b (-a) hab
  rwa [h.add_neg] at this

theorem le_of_sub_nonneg' {a b : K} (hab : 0 ≤ b + -a) : a ≤ b := by
  have := h.add_le_mono 0 (b + -a) a hab
  rwa [zero_add' h.toCommRingLaws, h.add_assoc, neg_add_cancel' h.toCommRingLaws,
    h.add_zero] at this

theorem mul_le_mul_of_nonneg_left' {a b c : K} (hab : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  apply le_of_sub_nonneg' h
  rw [← mul_neg' h.toCommRingLaws, ← h.distrib]
  exact h.mul_nonneg c _ hc (sub_nonneg_of_le' h hab)

theorem neg_nonneg_of_nonpos' {a : K} (ha : a ≤ 0) : 0 ≤ -a := by
  have := sub_nonneg_of_le' h ha
  rwa [zero_add' h.toCommRingLaws] at this

theorem zero_le_one' : (0 : K) ≤ 1 := by
  rcases h.le_total 0 1 with h1 | h1
  · exact h1
  · have hn := neg_nonneg_of_nonpos' h h1
    have := h.mul_nonneg _ _ hn hn
    rw [neg_mul' h.toCommRingLaws, mul_neg' h.toCommRingLaws, neg_neg' h.toCommRingLaws,
      h.mul_one] at this
    exact this

theorem zero_lt_one' : (0 : K) < 1 :=
  lt_of_le_of_ne' h (zero_le_one' h) h.zero_ne_one

theorem inv_nonneg_of_pos' {a : K} (ha : 0 < a) : 0 ≤ a⁻¹ := by
  have ha0 : a ≠ 0 := (ne_of_lt' h ha).symm
  rcases h.le_total 0 a⁻¹ with h1 | h1
  · exact h1
  · exfalso
    have hn := neg_nonneg_of_nonpos' h h1
    have := h.mul_nonneg _ _ (le_of_lt' h ha) hn
    rw [mul_neg' h.toCommRingLaws, h.mul_inv a ha0] at this
    have h2 := h.add_le_mono _ _ 1 this
    rw [zero_add' h.toCommRingLaws, neg_add_cancel' h.toCommRingLaws] at h2
    exact h.zero_ne_one (h.le_antisymm _ _ (zero_le_one' h) h2)

theorem mul_pos' {a b : K} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  apply lt_of_le_of_ne' h (h.mul_nonneg _ _ (le_of_lt' h ha) (le_of_lt' h hb))
  intro e
  rcases mul_eq_zero' h.toFieldLaws e.symm with e | e
  · exact ne_of_lt' h ha e.symm
  · exact ne_of_lt' h hb e.symm

theorem inv_pos' {a : K} (ha : 0 < a) : 0 < a⁻¹ :=
  lt_of_le_of_ne' h (inv_nonneg_of_pos' h ha)
    (fun e => inv_ne_zero' h.toFieldLaws (ne_of_lt' h ha).symm e.symm)

/-- Multiplication by a positive element preserves and reflects `≤`. -/
theorem mul_le_mul_left_iff' {a b c : K} (hc : 0 < c) : c * a ≤ c * b ↔ a ≤ b := by
  constructor
  · intro hle
    have := mul_le_mul_of_nonneg_left' h hle (inv_nonneg_of_pos' h hc)
    have hc0 : c ≠ 0 := (ne_of_lt' h hc).symm
    rwa [← h.mul_assoc, ← h.mul_assoc, inv_mul_cancel' h.toFieldLaws hc0,
      one_mul' h.toCommRingLaws, one_mul' h.toCommRingLaws] at this
  · intro hle; exact mul_le_mul_of_nonneg_left' h hle (le_of_lt' h hc)

theorem npow_pos {a : K} (ha : 0 < a) (n : Nat) : 0 < npow a n := by
  induction n with
  | zero => exact zero_lt_one' h
  | succ n ih => exact mul_pos' h ih ha

theorem zpow_pos {a : K} (ha : 0 < a) (k : Int) : 0 < zpow a k := by
  cases k with
  | ofNat n => exact npow_pos h ha n
  | negSucc n => exact inv_pos' h (npow_pos h ha _)

theorem finProd_pos (n : Nat) (f : Fin n → K) (hf : ∀ i, 0 < f i) : 0 < finProd n f := by
  induction n with
  | zero => exact zero_lt_one' h
  | succ n ih => exact mul_pos' h (hf 0) (ih _ (fun i => hf i.succ))

/-- In an ordered field, multiplication by `c` preserves and reflects `≤` exactly when `c > 0`. -/
theorem mul_le_mul_left_iff_forall_iff_pos (c : K) :
    (∀ a b : K, c * a ≤ c * b ↔ a ≤ b) ↔ 0 < c := by
  constructor
  · intro H
    have h01 := (H 0 1).2 (zero_le_one' h)
    rw [mul_zero' h.toCommRingLaws, h.mul_one] at h01
    apply lt_of_le_of_ne' h h01
    intro e
    have := (H 1 0).1
    rw [← e, zero_mul' h.toCommRingLaws, zero_mul' h.toCommRingLaws] at this
    have h10 := this (h.le_refl 0)
    exact h.zero_ne_one (h.le_antisymm _ _ (zero_le_one' h) h10)
  · intro hc a b; exact mul_le_mul_left_iff' h hc

end Ordered

end Toy.Units
