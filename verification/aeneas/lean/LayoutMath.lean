/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Arithmetic
import all Init.Data.Nat.Power2.Basic
@[expose] public section
namespace Zerocopy.LayoutMath

/-- Mathematical ceiling to an alignment, without machine overflow. -/
def roundUp (n a : Nat) : Nat := n + (a - n % a) % a

theorem roundUp_properties (n a : Nat) (ha : 0 < a) :
    n ≤ roundUp n a ∧ roundUp n a < n + a ∧ roundUp n a % a = 0 := by
  have hr := Nat.mod_lt n ha
  have hp := Nat.mod_lt (a - n % a) ha
  refine ⟨by unfold roundUp; omega, by unfold roundUp; omega, ?_⟩
  unfold roundUp
  by_cases hz : n % a = 0
  · simp [hz]
  · have hp' : (a - n % a) % a = a - n % a :=
      Nat.mod_eq_of_lt (by omega)
    rw [Nat.add_mod, Nat.mod_mod, hp']
    rw [show n % a + (a - n % a) = a by omega, Nat.mod_self]

theorem roundUp_le (n a q : Nat) (ha : 0 < a)
    (hn : n ≤ q) (hq : q % a = 0) : roundUp n a ≤ q := by
  have hp := (roundUp_properties n a ha).2.2
  have hbound := Nat.mod_lt (a - n % a) ha
  have hq' : (n + (q - n)) % a = 0 := by
    simpa only [Nat.add_sub_of_le hn] using hq
  have h := (Arithmetic.padding_properties n a _ ha hbound hp).2.1 _ hq'
  unfold roundUp
  omega

theorem roundUp_eq (n a : Nat) (h : n % a = 0) : roundUp n a = n := by
  simp [roundUp, h]

theorem roundUp_mono {n m a : Nat} (ha : 0 < a) (h : n ≤ m) :
    roundUp n a ≤ roundUp m a := by
  have hm := roundUp_properties m a ha
  exact roundUp_le n a _ ha (by omega) hm.2.2

theorem roundUp_shift (n k a : Nat) (hk : k % a = 0) :
    roundUp (k + n) a = k + roundUp n a := by
  simp only [roundUp, Nat.add_mod, hk, Nat.zero_add, Nat.mod_mod]
  omega

theorem roundUp_compose (n a b : Nat) (ha : 0 < a) (hb : 0 < b)
    (hab : a ∣ b) : roundUp (roundUp n a) b = roundUp n b := by
  have hn := roundUp_properties n a ha
  have hnb := roundUp_properties n b hb
  have hba : roundUp n b % a = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_trans hab (Nat.dvd_of_mod_eq_zero hnb.2.2))
  have hle := roundUp_le n a _ ha hnb.1 hba
  apply Nat.le_antisymm
  · exact roundUp_le _ b _ hb hle hnb.2.2
  · exact roundUp_mono hb hn.1

/-- Move a smaller inner ceiling across an addition before a larger ceiling. -/
theorem roundUp_swap (c x a b : Nat) (ha : 0 < a) (hb : 0 < b)
    (hab : a ∣ b) :
    roundUp (c + roundUp x a) b = roundUp (roundUp c a + x) b := by
  have hc := (roundUp_properties c a ha).2.2
  have hx := (roundUp_properties x a ha).2.2
  calc
    roundUp (c + roundUp x a) b = roundUp (roundUp (c + roundUp x a) a) b :=
      (roundUp_compose _ a b ha hb hab).symm
    _ = roundUp (roundUp c a + roundUp x a) b := by
      rw [Nat.add_comm c, roundUp_shift c _ a hx, Nat.add_comm (roundUp x a)]
    _ = roundUp (roundUp (roundUp c a + x) a) b := by
      rw [roundUp_shift x _ a hc]
    _ = roundUp (roundUp c a + x) b := roundUp_compose _ a b ha hb hab

theorem roundUp_inner (c x a b : Nat) (ha : 0 < a) (hba : b ∣ a) :
    roundUp (c + roundUp x a) b = roundUp c b + roundUp x a := by
  have hx : roundUp x a % b = 0 := Nat.mod_eq_zero_of_dvd
    (dvd_trans hba (Nat.dvd_of_mod_eq_zero (roundUp_properties x a ha).2.2))
  rw [Nat.add_comm c, roundUp_shift c _ b hx, Nat.add_comm]

theorem normalize_phase (c x a : Nat) :
    (c - c % a) + roundUp (c % a + x) a = roundUp (c + x) a := by
  have hm := Nat.mod_le c a
  have hk : (c - c % a) % a = 0 := by
    rw [← Nat.div_mul_self_eq_mod_sub_self, Nat.mul_mod_left]
  rw [← roundUp_shift _ _ a hk]
  congr 1
  omega

theorem power_alignments (i j : Nat) :
    if i ≤ j then 2 ^ i ∣ 2 ^ j else 2 ^ j ∣ 2 ^ i := by
  split
  · exact Nat.pow_dvd_pow 2 ‹i ≤ j›
  · exact Nat.pow_dvd_pow 2 (by omega)

/-- Normal form used only as the target of the refinement proof. -/
structure Formula where
  base : Nat
  phase : Nat
  align : Nat
  elem : Nat
  offset : Nat
deriving DecidableEq

def Formula.valid (f : Formula) : Prop := 0 < f.align ∧ f.phase < f.align
def Formula.bytes (f : Formula) (b : Nat) := f.base + roundUp (f.phase + b) f.align
def Formula.size (f : Formula) (n : Nat) := f.bytes (n * f.elem)

theorem Formula.size_mono (f : Formula) (ha : 0 < f.align) {n m : Nat} (h : n ≤ m) :
    f.size n ≤ f.size m := by
  unfold Formula.size Formula.bytes
  exact Nat.add_le_add_left (roundUp_mono ha
    (Nat.add_le_add_left (Nat.mul_le_mul_right f.elem h) f.phase)) f.base

def Formula.pad (f : Formula) (outer : Nat) : Formula :=
  if f.align < outer then
    let fixed := roundUp f.base f.align + f.phase
    { f with base := fixed - fixed % outer, phase := fixed % outer, align := outer }
  else { f with base := roundUp f.base outer }

theorem pad_size (f : Formula) (n outer : Nat) (hf : 0 < f.align)
    (ho : 0 < outer)
    (hd : if f.align < outer then f.align ∣ outer else outer ∣ f.align) :
    (f.pad outer).size n = roundUp (f.size n) outer := by
  unfold Formula.pad Formula.size Formula.bytes
  split <;> rename_i h
  · simp only [h, if_true] at hd
    dsimp only
    rw [normalize_phase]
    rw [roundUp_swap _ _ _ _ hf ho hd]
    congr 1
    omega
  · simp only [h, if_false] at hd
    dsimp only
    exact (roundUp_inner _ _ _ _ hf hd).symm

theorem pad_valid (f : Formula) (outer : Nat) (hf : f.valid) (ho : 0 < outer) :
    (f.pad outer).valid := by
  unfold Formula.pad Formula.valid
  split
  · exact ⟨ho, Nat.mod_lt _ ho⟩
  · exact hf

theorem pad_completed (f : Formula) (outer : Nat) (ho : 0 < outer) :
    outer ≤ (f.pad outer).align ∧ (f.pad outer).base % outer = 0 := by
  unfold Formula.pad
  split <;> rename_i h
  · dsimp only
    refine ⟨by omega, ?_⟩
    rw [← Nat.div_mul_self_eq_mod_sub_self, Nat.mul_mod_left]
  · dsimp only
    exact ⟨by omega, (roundUp_properties _ _ ho).2.2⟩

def Formula.advance (f : Formula) (b e : Nat) : Formula :=
  let shifted := f.phase + b
  { f with base := f.base + shifted - shifted % f.align,
           phase := shifted % f.align, elem := e }

theorem advance_size (f : Formula) (b e n : Nat) :
    (f.advance b e).size n = f.base + roundUp (f.phase + b + n * e) f.align := by
  have hm := Nat.mod_le (f.phase + b) f.align
  unfold Formula.advance Formula.size Formula.bytes
  dsimp only
  rw [show f.base + (f.phase + b) - (f.phase + b) % f.align =
    f.base + ((f.phase + b) - (f.phase + b) % f.align) by omega]
  rw [Nat.add_assoc, normalize_phase]

theorem aligned_element_size (f : Formula) (n : Nat) (he : f.elem % f.align = 0) :
    f.size n = f.size 0 + n * f.elem := by
  have hm : (n * f.elem) % f.align = 0 := by simp [Nat.mul_mod, he]
  unfold Formula.size Formula.bytes
  simp only [Nat.zero_mul, Nat.add_zero]
  rw [Nat.add_comm f.phase, roundUp_shift _ _ _ hm]
  omega

theorem roundUp_le_budget (n a q : Nat) (ha : 0 < a) :
    roundUp n a ≤ q ↔ n ≤ q - q % a := by
  have hfloor := Arithmetic.round_down_properties q a (q - q % a) ha rfl
  have hceil := roundUp_properties n a ha
  constructor
  · intro h
    have := hfloor.2.2.2 _ h hceil.2.2
    omega
  · intro h
    have := roundUp_le n a (q - q % a) ha h hfloor.2.1
    omega

/-- Largest fitting byte count, including rounding plateaus. -/
def Formula.capacity (f : Formula) (available : Nat) : Option Nat :=
  if f.bytes 0 ≤ available then
    some ((available - f.base) - (available - f.base) % f.align - f.phase)
  else none

theorem capacity_spec (f : Formula) (available : Nat) (ha : 0 < f.align) :
    match f.capacity available with
    | none => ∀ b, available < f.bytes b
    | some cap => ∀ b, f.bytes b ≤ available ↔ b ≤ cap := by
  unfold Formula.capacity
  by_cases h : f.bytes 0 ≤ available
  · simp only [h, if_true]
    have hbase : f.base ≤ available := by unfold Formula.bytes at h; omega
    have hphase : f.phase ≤ (available - f.base) - (available - f.base) % f.align := by
      apply (roundUp_le_budget _ _ _ ha).mp
      unfold Formula.bytes at h
      simp only [Nat.add_zero] at h
      omega
    intro b
    have hb := roundUp_le_budget (f.phase + b) f.align (available - f.base) ha
    unfold Formula.bytes
    omega
  · simp only [h, if_false]
    intro b
    have hmono := roundUp_mono ha (show f.phase + 0 ≤ f.phase + b by omega)
    unfold Formula.bytes at *
    omega

theorem roundUp_phase (p a : Nat) (_ha : 0 < a) (hp : p < a) :
    roundUp p a = if p = 0 then 0 else a := by
  by_cases h : p = 0
  · simp [roundUp, h]
  · unfold roundUp
    rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt (show a - p < a by omega)]
    simp only [h, if_false]
    omega

theorem floor_shift (k x a : Nat) (hk : k % a = 0) :
    (k + x) - (k + x) % a = k + (x - x % a) := by
  have := Nat.mod_le x a
  rw [Nat.add_mod, hk, Nat.zero_add, Nat.mod_mod]
  omega

theorem aligned_or (n p a : Nat) (ha : a.isPowerOfTwo)
    (hn : n % a = 0) (hp : p < a) : n ||| p = n + p := by
  obtain ⟨k, hk⟩ := ha
  rw [hk] at hn hp
  have h : n = 2 ^ k * (n / 2 ^ k) := by
    rw [Nat.mul_comm, Nat.div_mul_self_eq_mod_sub_self, hn, Nat.sub_zero]
  rw [h]
  exact (Nat.two_pow_add_eq_or_of_lt hp _).symm

def Formula.sameSequence (f g : Formula) : Prop :=
  f.elem = g.elem ∧ f.size 0 = g.size 0 ∧
    ((f.elem % f.align = 0 ∧ g.elem % g.align = 0) ∨
      (f.align = g.align ∧ f.phase = g.phase))

theorem same_sequence_sound (f g : Formula) (h : f.sameSequence g) (n : Nat) :
    f.size n = g.size n := by
  obtain ⟨he, hzero, hcases⟩ := h
  rcases hcases with ⟨hf, hg⟩ | ⟨ha, hp⟩
  · rw [aligned_element_size f n hf, aligned_element_size g n hg, he, hzero]
  · have hbase : f.base = g.base := by
      unfold Formula.size Formula.bytes at hzero
      simp only [Nat.zero_mul, Nat.add_zero] at hzero
      rw [ha, hp] at hzero
      omega
    simp only [Formula.size, Formula.bytes, hbase, hp, he, ha]

theorem no_dynamic_padding (f : Formula) (hzero : f.size 0 = f.offset)
    (he : f.elem % f.align = 0) (n : Nat) : f.size n = f.offset + n * f.elem := by
  rw [aligned_element_size f n he, hzero]

theorem maximal_metadata (f : Formula) (available cap : Nat) (he : 0 < f.elem)
    (h : f.capacity available = some cap) (ha : 0 < f.align) :
    ∀ n, f.size n ≤ available ↔ n ≤ cap / f.elem := by
  have hc := capacity_spec f available ha
  rw [h] at hc
  intro n
  unfold Formula.size
  rw [hc]
  exact Nat.le_div_iff_mul_le he |>.symm

def Formula.checkedSize (f : Formula) (limit n : Nat) : Option Nat :=
  if f.size n ≤ limit then some (f.size n) else none

theorem checked_size_spec (f : Formula) (limit n : Nat) :
    (f.checkedSize limit n = some (f.size n) ↔ f.size n ≤ limit) ∧
    (f.checkedSize limit n = none ↔ limit < f.size n) := by
  unfold Formula.checkedSize
  split <;> simp_all

end Zerocopy.LayoutMath
