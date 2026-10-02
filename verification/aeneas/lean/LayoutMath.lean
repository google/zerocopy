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

/-- Recursive record semantics, retaining each inner field's complete size. -/
inductive Description where
  | slice (elem alignExponent : Nat)
  | record (leading minAlignExponent : Nat) (packedExponent : Option Nat)
      (tail : Description)
deriving DecidableEq

def Description.alignExponent : Description → Nat
  | .slice _ a => a
  | .record _ minimum packed tail => max minimum
      (match packed with | none => tail.alignExponent | some p => min p tail.alignExponent)

def Description.fieldAlignExponent (packed : Option Nat) (tail : Description) : Nat :=
  match packed with | none => tail.alignExponent | some p => min p tail.alignExponent

def Description.size : Description → Nat → Nat
  | .slice elem _, n => n * elem
  | d@(.record leading _ packed tail), n =>
      roundUp (roundUp leading (2 ^ fieldAlignExponent packed tail) + tail.size n)
        (2 ^ d.alignExponent)

def Description.offset : Description → Nat
  | .slice _ _ => 0
  | .record leading _ packed tail =>
      roundUp leading (2 ^ fieldAlignExponent packed tail) + tail.offset

def Description.elem : Description → Nat
  | .slice e _ => e
  | .record _ _ _ tail => tail.elem

def Description.valid : Description → Prop
  | .slice elem a => elem % 2 ^ a = 0
  | .record _ _ _ tail => tail.valid

def Description.compile : Description → Formula
  | .slice elem a => ⟨0, 0, 2 ^ a, elem, 0⟩
  | d@(.record leading _ packed tail) =>
      let placement := roundUp leading (2 ^ fieldAlignExponent packed tail)
      let inner := tail.compile
      ({ inner with base := placement + inner.base,
                    offset := placement + inner.offset }).pad (2 ^ d.alignExponent)

theorem compile_power (d : Description) : ∃ k, d.compile.align = 2 ^ k := by
  induction d with
  | slice e a => exact ⟨a, rfl⟩
  | record leading minimum packed tail ih =>
    obtain ⟨k, hk⟩ := ih
    unfold Description.compile Formula.pad
    dsimp only
    split
    · exact ⟨_, rfl⟩
    · exact ⟨k, hk⟩

theorem compile_size (d : Description) (h : d.valid) (n : Nat) :
    d.compile.size n = d.size n := by
  induction d with
  | slice e a =>
    simp only [Description.compile, Formula.size, Formula.bytes,
      Description.size, Nat.zero_add]
    apply roundUp_eq
    simp only [Description.valid] at h
    simp [Nat.mul_mod, h]
  | record leading minimum packed tail ih =>
    obtain ⟨k, hk⟩ := compile_power tail
    let placement := roundUp leading (2 ^ Description.fieldAlignExponent packed tail)
    let f : Formula := { tail.compile with
      base := placement + tail.compile.base
      offset := placement + tail.compile.offset }
    change (f.pad (2 ^ (Description.record leading minimum packed tail).alignExponent)).size n = _
    have hf : 0 < f.align := by dsimp [f]; rw [hk]; exact Nat.two_pow_pos k
    have hd : if f.align < 2 ^ (Description.record leading minimum packed tail).alignExponent
        then f.align ∣ 2 ^ (Description.record leading minimum packed tail).alignExponent
        else 2 ^ (Description.record leading minimum packed tail).alignExponent ∣ f.align := by
      dsimp [f]
      rw [hk]
      split <;> rename_i hh
      · exact Nat.pow_dvd_pow 2 ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hh).le
      · exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by omega))
    rw [pad_size f n _ hf (Nat.two_pow_pos _) hd]
    simp only [Formula.size, Formula.bytes, f, Nat.add_assoc]
    change roundUp (placement + tail.compile.size n) _ = _
    rw [ih h]
    rfl

theorem compile_offset (d : Description) : d.compile.offset = d.offset := by
  induction d with
  | slice e a => rfl
  | record leading minimum packed tail ih =>
    unfold Description.compile Formula.pad
    dsimp only
    split <;> simp only [Description.offset, ih]

theorem compile_elem (d : Description) : d.compile.elem = d.elem := by
  induction d with
  | slice e a => rfl
  | record leading minimum packed tail ih =>
    unfold Description.compile Formula.pad
    dsimp only
    split <;> simp only [Description.elem, ih]

theorem compile_valid (d : Description) : d.compile.valid := by
  induction d with
  | slice e a => exact ⟨Nat.two_pow_pos a, Nat.two_pow_pos a⟩
  | record leading minimum packed tail ih =>
    exact pad_valid _ _ ih (Nat.two_pow_pos _)

/-- A complete recursive layout always contains the physical slice bytes. -/
theorem description_contains_tail (d : Description) (n : Nat) :
    d.offset + n * d.elem ≤ d.size n := by
  induction d with
  | slice e a => simp only [Description.offset, Description.elem, Description.size, Nat.zero_add, Nat.le_refl]
  | record leading minimum packed tail ih =>
    have h := (roundUp_properties
      (roundUp leading (2 ^ Description.fieldAlignExponent packed tail) + tail.size n)
      (2 ^ (Description.record leading minimum packed tail).alignExponent)
      (Nat.two_pow_pos _)).1
    simp only [Description.offset, Description.elem, Description.size]
    omega

theorem compiled_contains_tail (d : Description) (h : d.valid) (n : Nat) :
    d.compile.offset + n * d.compile.elem ≤ d.compile.size n := by
  rw [compile_offset, compile_elem, compile_size d h]
  exact description_contains_tail d n

/-- The old flattened formula loses padding inside a packed field. -/
theorem packed_regression :
    (Description.record 2 0 (some 1) (.record 5 2 none (.slice 1 0))).size 0 = 10 ∧
    roundUp 7 2 = 8 := by decide

theorem aligned_below_next (x k a : Nat) (hx : x % a = 0) (hk : k % a = 0)
    (h : x < k + a) : x ≤ k := by
  by_contra hnot
  have heq : x = k + (x - k) := by omega
  have hd : (x - k) % a = 0 := by
    rw [heq, Nat.add_mod, hk, Nat.zero_add, Nat.mod_mod] at hx
    exact hx
  rw [Nat.mod_eq_of_lt (by omega)] at hd
  omega

theorem floor_capacity (n cap a : Nat) (ha : 0 < a) :
    n - n % a ≤ cap ↔ n ≤ cap - cap % a + (a - 1) := by
  have hn := Arithmetic.round_down_properties n a (n - n % a) ha rfl
  have hc := Arithmetic.round_down_properties cap a (cap - cap % a) ha rfl
  constructor
  · intro h
    have hbound := hc.2.2.2 _ h hn.2.1
    omega
  · intro h
    have hbound := aligned_below_next _ _ _ hn.2.1 hc.2.1 (by omega)
    omega

theorem roundUp_from_aligned_budget (budget unused a : Nat) (ha : 0 < a)
    (hb : budget % a = 0) (hu : unused ≤ budget) :
    roundUp (budget - unused) a = budget - (unused - unused % a) := by
  have hm := Nat.mod_le unused a
  have hr := Nat.mod_lt unused ha
  let floor := unused - unused % a
  have hf : floor % a = 0 := by
    dsimp only [floor]
    rw [← Nat.div_mul_self_eq_mod_sub_self, Nat.mul_mod_left]
  have hq : (budget - floor) % a = 0 := by
    have hsplit : budget = (budget - floor) + floor := by dsimp only [floor]; omega
    rw [hsplit, Nat.add_mod, hf, Nat.add_zero, Nat.mod_mod] at hb
    exact hb
  have hceil := roundUp_properties (budget - unused) a ha
  have hupper := roundUp_le (budget - unused) a (budget - floor) ha (by dsimp only [floor]; omega) hq
  have hlower := aligned_below_next (budget - floor) (roundUp (budget - unused) a) a
    hq hceil.2.2 (by dsimp only [floor]; omega)
  dsimp only [floor] at hupper hlower
  omega

theorem capacity_object_size (f : Formula) (available cap : Nat) (ha : 0 < f.align)
    (hcap : f.capacity available = some cap) :
    f.size (cap / f.elem) = f.base +
      ((available - f.base) - (available - f.base) % f.align) -
      (cap % f.elem - cap % f.elem % f.align) := by
  have hspec := capacity_spec f available ha
  rw [hcap] at hspec
  have hzero := (hspec 0).mpr (by omega)
  have hbase : f.base ≤ available := by unfold Formula.bytes at hzero; omega
  have hphase : f.phase ≤ (available - f.base) - (available - f.base) % f.align := by
    apply (roundUp_le_budget f.phase f.align (available - f.base) ha).mp
    unfold Formula.bytes at hzero
    simp only [Nat.add_zero] at hzero
    omega
  have hc : cap = (available - f.base) - (available - f.base) % f.align - f.phase := by
    unfold Formula.capacity at hcap
    simp only [hzero, if_true, Option.some.injEq] at hcap
    exact hcap.symm
  let budget := (available - f.base) - (available - f.base) % f.align
  have hb : budget % f.align = 0 := by
    dsimp only [budget]
    rw [← Nat.div_mul_self_eq_mod_sub_self, Nat.mul_mod_left]
  have hm := Nat.mod_le cap f.elem
  have hdiv := Nat.mod_add_div cap f.elem
  have hinput : f.phase + (cap / f.elem) * f.elem = budget - cap % f.elem := by
    dsimp only [budget]
    rw [Nat.mul_comm] at hdiv
    omega
  unfold Formula.size Formula.bytes
  rw [hinput, roundUp_from_aligned_budget budget _ f.align ha hb (by dsimp only [budget]; omega)]
  have hfloor := Nat.mod_le (cap % f.elem) f.align
  dsimp only [budget]
  omega

/-- An independent description of a layout fragment, with unbounded sizes. -/
inductive Payload where
  | fixed (bytes : Nat)
  | trailing (formula : Formula)
deriving DecidableEq

structure LayoutValue where
  align : Nat
  payload : Payload
  unpadded : Bool
deriving DecidableEq

def LayoutValue.size (v : LayoutValue) (n : Nat) : Nat :=
  match v.payload with
  | .fixed bytes => bytes
  | .trailing f => f.size n

def LayoutValue.initial (align : Nat) : LayoutValue := ⟨align, .fixed 0, true⟩

/-- Outside the `extendFits` domain the placeholder result has no contract. -/
def LayoutValue.extend (v field : LayoutValue) (packing : Nat) : LayoutValue :=
  match v.payload with
  | .trailing _ => v
  | .fixed bytes =>
    let fieldAlign := min field.align packing
    let offset := roundUp bytes fieldAlign
    { align := max v.align fieldAlign,
      payload := match field.payload with
        | .fixed size => .fixed (offset + size)
        | .trailing f => .trailing { f with base := offset + f.base, offset := offset + f.offset },
      unpadded := v.unpadded && field.unpadded && decide (bytes % fieldAlign = 0) }

def LayoutValue.extendFits (v field : LayoutValue) (packing limit : Nat) : Prop :=
  match v.payload with
  | .trailing _ => False
  | .fixed bytes =>
    let offset := roundUp bytes (min field.align packing)
    match field.payload with
    | .fixed size => offset + size ≤ limit
    | .trailing f => offset + f.offset ≤ limit ∧ offset + f.base ≤ limit

def LayoutValue.pad (v : LayoutValue) : LayoutValue :=
  { v with
    payload := match v.payload with
      | .fixed bytes => .fixed (roundUp bytes v.align)
      | .trailing f => .trailing (f.pad v.align)
    unpadded := match v.payload with
      | .fixed bytes => v.unpadded && decide (bytes % v.align = 0)
      | .trailing _ => v.unpadded }

def LayoutValue.padFits (v : LayoutValue) (limit : Nat) : Prop :=
  match v.payload with
  | .fixed bytes => roundUp bytes v.align ≤ limit
  | .trailing f =>
    if f.align < v.align then roundUp f.base f.align + f.phase ≤ limit
    else roundUp f.base v.align ≤ limit

theorem LayoutValue.extend_size (v field : LayoutValue) (packing bytes n : Nat)
    (h : v.payload = .fixed bytes) :
    (v.extend field packing).size n =
      roundUp bytes (min field.align packing) + field.size n := by
  simp only [LayoutValue.extend, h]
  cases hf : field.payload <;> simp [LayoutValue.size, hf, Formula.size, Formula.bytes, Nat.add_assoc]

def LayoutValue.prefixValue (fields : List LayoutValue) (initial : LayoutValue)
    (packing i : Nat) : LayoutValue :=
  (fields.take i).foldl (fun v field => v.extend field packing) initial

theorem LayoutValue.prefixValue_step (fields : List LayoutValue) (initial : LayoutValue)
    (packing i : Nat) (hi : i < fields.length) :
    prefixValue fields initial packing (i + 1) =
      (prefixValue fields initial packing i).extend fields[i] packing := by
  unfold prefixValue
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
  rfl

/-- Direct field placement, evaluated separately for each metadata value.
This rule never manipulates the normalization's base, phase, or size alignment. -/
def recordState (fields : List LayoutValue) (minimum packing metadata count : Nat) : Nat × Nat :=
  (fields.take count).foldl
    (fun state field =>
      (max state.1 (min field.align packing),
       roundUp state.2 (min field.align packing) + field.size metadata))
    (minimum, 0)

theorem recordState_step (fields : List LayoutValue) (minimum packing metadata i : Nat)
    (hi : i < fields.length) :
    recordState fields minimum packing metadata (i + 1) =
      (max (recordState fields minimum packing metadata i).1 (min fields[i].align packing),
       roundUp (recordState fields minimum packing metadata i).2 (min fields[i].align packing) +
         fields[i].size metadata) := by
  unfold recordState
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
  rfl

theorem recordState_refinement (fields : List LayoutValue) (minimum packing metadata limit : Nat)
    (hfit : ∀ i (hi : i < fields.length),
      (LayoutValue.prefixValue fields (LayoutValue.initial minimum) packing i).extendFits
        fields[i] packing limit) :
    ∀ i ≤ fields.length, recordState fields minimum packing metadata i =
      ((LayoutValue.prefixValue fields (LayoutValue.initial minimum) packing i).align,
       (LayoutValue.prefixValue fields (LayoutValue.initial minimum) packing i).size metadata) := by
  intro i
  induction i with
  | zero =>
    intro hi
    simp only [recordState, LayoutValue.prefixValue, List.take_zero, List.foldl_nil,
      LayoutValue.initial, LayoutValue.size]
  | succ i ih =>
    intro hi
    have hil : i < fields.length := by omega
    have hstep := hfit i hil
    let current := LayoutValue.prefixValue fields (LayoutValue.initial minimum) packing i
    cases hc : current.payload with
    | trailing f =>
      dsimp only [current] at hc
      simp only [LayoutValue.extendFits, hc] at hstep
    | fixed bytes =>
      dsimp only [current] at hc
      rw [recordState_step fields minimum packing metadata i hil, ih (by omega),
        LayoutValue.prefixValue_step fields (LayoutValue.initial minimum) packing i hil]
      change _ = ((current.extend fields[i] packing).align,
        (current.extend fields[i] packing).size metadata)
      rw [LayoutValue.extend_size current fields[i] packing bytes metadata hc]
      simp only [current, LayoutValue.extend, hc, LayoutValue.size]

end Zerocopy.LayoutMath
