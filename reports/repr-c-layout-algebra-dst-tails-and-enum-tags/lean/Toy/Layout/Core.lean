namespace Toy.Layout

/-!
# Core Alignment, Rounding, and Field Primitives

This module defines the unbundled arithmetic and field-level primitives used throughout
the `Toy.Layout` model of Rust's `#[repr(C)]` type layout:

* `IsPowerOfTwo`: models Rust's requirement (`r[layout.properties.align]`) that valid
  alignments are powers of two (`1, 2, 4, ...`).
* `paddingNeeded`, `alignUp`, `roundDown`, and `IsLeastMultipleGe`: exact natural-number
  alignment rounding (abstracting away finite `usize` / `isize::MAX` overflow bounds).
* `FieldLayout` and atomic well-formedness predicates (`AlignPos`, `AlignPow2`,
  `SizeMultipleOfAlign`): unbundled `(size, align)` pairs so theorems state minimal
  hypotheses individually.
* `ReprModifier`, `ModifierPackPos`, `ModifierPow2`, and `effFieldAlign`: mutually
  exclusive `#[repr(packed(N))]` and `#[repr(align(N))]` modifiers
  (`r[layout.repr.alignment]`).
-/

/-- A natural number is a power of two (`1, 2, 4, 8, ...`).
    Captures the Rust Reference requirement (`r[layout.properties.align]`) that every
    type alignment is at least `1` and a power of two. -/
def IsPowerOfTwo (a : Nat) : Prop :=
  ∃ k : Nat, a = 2 ^ k

/-- Every power of two is strictly positive (derivation lemma showing `0 < a` follows
    from `IsPowerOfTwo a`). -/
theorem isPowerOfTwo_pos {a : Nat} (h : IsPowerOfTwo a) : 0 < a := by
  rcases h with ⟨k, rfl⟩
  exact Nat.two_pow_pos k

theorem ex_isPowerOfTwo_pos_1 : IsPowerOfTwo 1 := ⟨0, rfl⟩
theorem ex_isPowerOfTwo_pos_4 : IsPowerOfTwo 4 := ⟨2, rfl⟩
theorem ex_isPowerOfTwo_pos_8 : IsPowerOfTwo 8 := ⟨3, rfl⟩

theorem ex_isPowerOfTwo_neg_0 : ¬ IsPowerOfTwo 0 := by
  intro h
  have hpos := isPowerOfTwo_pos h
  omega

theorem ex_isPowerOfTwo_neg_3 : ¬ IsPowerOfTwo 3 := by
  rintro ⟨k, hk⟩
  match k with
  | 0 => simp at hk
  | 1 => simp at hk
  | k + 2 =>
    have : 4 ≤ 2 ^ (k + 2) := by
      have h1 : 1 ≤ 2 ^ k := Nat.two_pow_pos k
      have h2 : 2 ^ (k + 2) = 2 ^ k * 4 := by
        simp [Nat.pow_succ, Nat.mul_assoc]
      omega
    omega

theorem ex_isPowerOfTwo_neg_6 : ¬ IsPowerOfTwo 6 := by
  rintro ⟨k, hk⟩
  match k with
  | 0 | 1 | 2 => simp at hk
  | k + 3 =>
    have : 8 ≤ 2 ^ (k + 3) := by
      have h1 : 1 ≤ 2 ^ k := Nat.two_pow_pos k
      have h2 : 2 ^ (k + 3) = 2 ^ k * 8 := by
        simp [Nat.pow_succ, Nat.mul_assoc]
      omega
    omega

/-- Minimal non-negative padding bytes to add to `n` to reach a multiple of `a`
    when `0 < a`. Totalized to `0` at `a = 0`; layout theorems that require divisibility
    explicitly assume `0 < a`. Captures `MockLayout::padding_needed_for` in the Rust
    Reference (`r[layout.repr.c.struct.size-field-offset]`). -/
def paddingNeeded (n a : Nat) : Nat :=
  if a = 0 then 0
  else
    let r := n % a
    if r = 0 then 0 else a - r

theorem ex_paddingNeeded_pos : paddingNeeded 5 4 = 3 := rfl
theorem ex_paddingNeeded_zero : paddingNeeded 8 4 = 0 := rfl
theorem ex_paddingNeeded_neg : paddingNeeded 5 4 ≠ 0 := by decide

/-- Rounds `n` up to the least multiple of `a` that is `≥ n` (when `0 < a`).
    Totalized to `n` at `a = 0`. Captures alignment rounding (`Size::align_to`) in
    `rustc_abi` and the Rust Reference. -/
def alignUp (n a : Nat) : Nat :=
  n + paddingNeeded n a

theorem ex_alignUp_pos_unaligned : alignUp 5 4 = 8 := rfl
theorem ex_alignUp_pos_aligned : alignUp 8 4 = 8 := rfl
theorem ex_alignUp_neg : alignUp 5 4 ≠ 5 := by decide

/-- Rounding `0` up to any alignment `a` always yields `0`. -/
theorem alignUp_zero (a : Nat) : alignUp 0 a = 0 := by
  unfold alignUp paddingNeeded
  split <;> simp

/-- Rounds `x` down to the greatest multiple of `a` that is `≤ x` (when `0 < a`).
    Totalized to `0` at `a = 0`. Captures `round_down_to_next_multiple_of_alignment`
    used in prefix-cast capacity bounds for dynamically sized types. -/
def roundDown (x a : Nat) : Nat :=
  if a = 0 then 0 else (x / a) * a

theorem ex_roundDown_pos : roundDown 7 4 = 4 := rfl
theorem ex_roundDown_neg : roundDown 7 4 ≠ 7 := by decide

/-- `x` is the least multiple of `a` that is at least `n`.
    Captures the defining specification of `alignUp n a` and of the final struct
    size in `r[layout.repr.c.struct.size-field-offset]`. -/
def IsLeastMultipleGe (x n a : Nat) : Prop :=
  n ≤ x ∧ a ∣ x ∧ ∀ m : Nat, n ≤ m → a ∣ m → x ≤ m

theorem ex_isLeastMultipleGe_pos : IsLeastMultipleGe 8 5 4 := by
  refine ⟨by omega, ⟨2, rfl⟩, ?_⟩
  rintro m hle ⟨q, rfl⟩
  omega

theorem ex_isLeastMultipleGe_neg_not_minimal : ¬ IsLeastMultipleGe 12 5 4 := by
  intro ⟨_, _, hmin⟩
  have h := hmin 8 (by omega) ⟨2, rfl⟩
  omega

theorem ex_isLeastMultipleGe_neg_not_multiple : ¬ IsLeastMultipleGe 5 5 4 := by
  intro ⟨_, ⟨q, hq⟩, _⟩
  omega

/-- Unbundled layout parameters of a single sized field: byte `size` and alignment
    requirement `align`. Kept as plain `Nat`s so positivity, power-of-two, and
    size-multiple-of-alignment hypotheses can be stated and tested independently. -/
structure FieldLayout where
  size : Nat
  align : Nat
  deriving Repr, DecidableEq, BEq

/-- The field has strictly positive alignment (`0 < f.align`).
    Weakest positivity condition needed for modular alignment arithmetic. -/
def AlignPos (f : FieldLayout) : Prop :=
  0 < f.align

theorem ex_alignPos_pos : AlignPos ⟨4, 4⟩ := by simp [AlignPos]
theorem ex_alignPos_neg : ¬ AlignPos ⟨4, 0⟩ := by simp [AlignPos]

/-- The field's alignment is a power of two (`r[layout.properties.align]`). -/
def AlignPow2 (f : FieldLayout) : Prop :=
  IsPowerOfTwo f.align

theorem alignPow2_to_alignPos {f : FieldLayout} (h : AlignPow2 f) : AlignPos f :=
  isPowerOfTwo_pos h

theorem ex_alignPow2_pos : AlignPow2 ⟨4, 4⟩ := ⟨2, rfl⟩
theorem ex_alignPow2_neg : ¬ AlignPow2 ⟨3, 3⟩ := ex_isPowerOfTwo_neg_3

/-- The field's size is a multiple of its alignment (`r[layout.properties.size]`). -/
def SizeMultipleOfAlign (f : FieldLayout) : Prop :=
  f.align ∣ f.size

theorem ex_sizeMultipleOfAlign_pos : SizeMultipleOfAlign ⟨6, 2⟩ := ⟨3, rfl⟩
theorem ex_sizeMultipleOfAlign_neg : ¬ SizeMultipleOfAlign ⟨3, 2⟩ := by
  rintro ⟨q, hq⟩
  dsimp at hq
  omega

/-- Mutually exclusive alignment modifiers applicable to a `#[repr(C)]` struct
    (`r[layout.repr.alignment.constraint-exclusive]`):
    * `none`: plain `#[repr(C)]`;
    * `packed n`: `#[repr(C, packed(n))]`, capping each field's effective alignment at `n`;
    * `aligned n`: `#[repr(C, align(n))]`, raising the struct's overall alignment to at least `n`. -/
inductive ReprModifier where
  | none
  | packed (n : Nat)
  | aligned (n : Nat)
  deriving Repr, DecidableEq, BEq

/-- Any `packed(p)` modifier uses a strictly positive packing bound `p`.
    Does not constrain `none` or `aligned n` (since `aligned n` never reduces alignment). -/
def ModifierPackPos (m : ReprModifier) : Prop :=
  ∀ p : Nat, m = .packed p → 0 < p

theorem ex_modifierPackPos_pos_none : ModifierPackPos .none := by
  intro p h; cases h

theorem ex_modifierPackPos_pos_packed : ModifierPackPos (.packed 2) := by
  intro p h; cases h; decide

theorem ex_modifierPackPos_neg_packed0 : ¬ ModifierPackPos (.packed 0) := by
  intro h
  have := h 0 rfl
  omega

/-- Any numeric argument to `packed(n)` or `aligned(n)` is a power of two
    (`r[layout.repr.alignment.constraint-alignment]`). -/
def ModifierPow2 : ReprModifier → Prop
  | .none => True
  | .packed n => IsPowerOfTwo n
  | .aligned n => IsPowerOfTwo n

theorem modifierPow2_to_packPos {m : ReprModifier} (h : ModifierPow2 m) : ModifierPackPos m := by
  intro p hm
  subst hm
  exact isPowerOfTwo_pos h

theorem ex_modifierPow2_pos_aligned : ModifierPow2 (.aligned 8) := ⟨3, rfl⟩
theorem ex_modifierPow2_neg_aligned : ¬ ModifierPow2 (.aligned 6) := ex_isPowerOfTwo_neg_6
theorem ex_modifierPow2_neg_packed : ¬ ModifierPow2 (.packed 3) := ex_isPowerOfTwo_neg_3

/-- Effective alignment used to position a field of natural alignment `a` under
    modifier `m`. Matches `r[layout.repr.alignment.packed-fields]`: `packed(p)` clamps
    each field's alignment to `min a p`, while `none` and `aligned(n)` leave it at `a`. -/
def effFieldAlign (m : ReprModifier) (a : Nat) : Nat :=
  match m with
  | .packed p => min a p
  | .none | .aligned _ => a

theorem ex_effFieldAlign_pos_packed : effFieldAlign (.packed 2) 8 = 2 := rfl
theorem ex_effFieldAlign_pos_aligned : effFieldAlign (.aligned 16) 4 = 4 := rfl
theorem ex_effFieldAlign_neg_packed_unchanged : effFieldAlign (.packed 2) 8 ≠ 8 := by decide

/-! ## Proof-Support Arithmetic and Alignment Lemmas -/

theorem le_alignUp (n a : Nat) : n ≤ alignUp n a :=
  Nat.le_add_right n (paddingNeeded n a)

theorem alignUp_eq_self_of_dvd {n a : Nat} (h : a ∣ n) : alignUp n a = n := by
  unfold alignUp paddingNeeded
  by_cases ha : a = 0
  · simp [ha]
  · have hmod : n % a = 0 := Nat.mod_eq_zero_of_dvd h
    simp [ha, hmod]

theorem alignUp_one (n : Nat) : alignUp n 1 = n :=
  alignUp_eq_self_of_dvd (Nat.one_dvd n)

theorem dvd_alignUp {n a : Nat} (ha : 0 < a) : a ∣ alignUp n a := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt ha
  unfold alignUp paddingNeeded
  simp only [ha0, ↓reduceIte]
  by_cases hr : n % a = 0
  · simp only [hr, ↓reduceIte, Nat.add_zero]
    exact Nat.dvd_of_mod_eq_zero hr
  · simp only [hr, ↓reduceIte]
    have hlt : n % a < a := Nat.mod_lt n ha
    have hdecomp : a * (n / a) + n % a = n := Nat.div_add_mod n a
    refine ⟨n / a + 1, ?_⟩
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem alignUp_le_of_dvd {n m a : Nat} (hnm : n ≤ m) (hdvd : a ∣ m) : alignUp n a ≤ m := by
  by_cases ha0 : a = 0
  · subst ha0
    simpa [alignUp, paddingNeeded] using hnm
  · have ha : 0 < a := Nat.pos_of_ne_zero ha0
    rcases hdvd with ⟨q, rfl⟩
    unfold alignUp paddingNeeded
    simp only [ha0, ↓reduceIte]
    by_cases hr : n % a = 0
    · simp only [hr, ↓reduceIte, Nat.add_zero]
      exact hnm
    · simp only [hr, ↓reduceIte]
      have hlt : n % a < a := Nat.mod_lt n ha
      have hdecomp : a * (n / a) + n % a = n := Nat.div_add_mod n a
      have hdiv_lt : n / a < q := by
        by_cases hqle : q ≤ n / a
        · have hmul : a * q ≤ a * (n / a) := Nat.mul_le_mul_left a hqle
          omega
        · omega
      have hmul_le : a * (n / a + 1) ≤ a * q := Nat.mul_le_mul_left a hdiv_lt
      rw [Nat.mul_add, Nat.mul_one] at hmul_le
      omega

theorem alignUp_isLeastMultipleGe {n a : Nat} (ha : 0 < a) :
    IsLeastMultipleGe (alignUp n a) n a :=
  ⟨le_alignUp n a, dvd_alignUp ha, fun _ hnm hdvd => alignUp_le_of_dvd hnm hdvd⟩

theorem isLeastMultipleGe_unique {x y n a : Nat}
    (hx : IsLeastMultipleGe x n a) (hy : IsLeastMultipleGe y n a) : x = y :=
  Nat.le_antisymm (hx.2.2 y hy.1 hy.2.1) (hy.2.2 x hx.1 hx.2.1)

theorem alignUp_mono {n₁ n₂ a : Nat} (h : n₁ ≤ n₂) : alignUp n₁ a ≤ alignUp n₂ a := by
  by_cases ha0 : a = 0
  · subst ha0
    simpa [alignUp, paddingNeeded] using h
  · exact alignUp_le_of_dvd (Nat.le_trans h (le_alignUp n₂ a)) (dvd_alignUp (Nat.pos_of_ne_zero ha0))

theorem alignUp_alignUp_of_dvd {n a b : Nat} (hb : 0 < b) (hab : a ∣ b) :
    alignUp (alignUp n a) b = alignUp n b := by
  apply Nat.le_antisymm
  · have h1 : alignUp n a ≤ alignUp n b :=
      alignUp_le_of_dvd (le_alignUp n b) (Nat.dvd_trans hab (dvd_alignUp hb))
    exact alignUp_le_of_dvd h1 (dvd_alignUp hb)
  · exact alignUp_mono (le_alignUp n a)

theorem alignUp_add_of_dvd_left {c x a : Nat} (hc : a ∣ c) :
    alignUp (c + x) a = c + alignUp x a := by
  by_cases ha0 : a = 0
  · subst ha0
    rcases hc with ⟨q, hq⟩
    simp at hq
    subst hq
    simp [alignUp, paddingNeeded]
  · have ha : 0 < a := Nat.pos_of_ne_zero ha0
    apply isLeastMultipleGe_unique (alignUp_isLeastMultipleGe ha)
    refine ⟨Nat.add_le_add_left (le_alignUp x a) c, Nat.dvd_add hc (dvd_alignUp ha), ?_⟩
    intro m hle hdvd
    rcases hc with ⟨qc, rfl⟩
    rcases hdvd with ⟨qm, rfl⟩
    have hq_le : a * qc ≤ a * qm := by omega
    have hsub_dvd : a ∣ (a * qm - a * qc) := ⟨qm - qc, (Nat.mul_sub_left_distrib a qm qc).symm⟩
    have hx_le : x ≤ a * qm - a * qc := by omega
    have hal_le : alignUp x a ≤ a * qm - a * qc := alignUp_le_of_dvd hx_le hsub_dvd
    omega

theorem roundDown_le (x : Nat) {a : Nat} (ha : 0 < a) : roundDown x a ≤ x := by
  unfold roundDown
  simp only [Nat.ne_of_gt ha, ↓reduceIte]
  exact Nat.div_mul_le_self x a

theorem dvd_roundDown (x : Nat) {a : Nat} (ha : 0 < a) : a ∣ roundDown x a := by
  unfold roundDown
  simp only [Nat.ne_of_gt ha, ↓reduceIte]
  exact ⟨x / a, Nat.mul_comm _ _⟩

theorem le_roundDown_of_dvd {m x a : Nat} (ha : 0 < a) (hm : m ≤ x) (hdvd : a ∣ m) :
    m ≤ roundDown x a := by
  unfold roundDown
  simp only [Nat.ne_of_gt ha, ↓reduceIte]
  rcases hdvd with ⟨q, rfl⟩
  have hq : q ≤ x / a := (Nat.le_div_iff_mul_le ha).mpr (by rw [Nat.mul_comm]; exact hm)
  rw [Nat.mul_comm a q]
  exact Nat.mul_le_mul_right a hq

theorem alignUp_le_iff_le_roundDown {y buf a : Nat} (ha : 0 < a) :
    alignUp y a ≤ buf ↔ y ≤ roundDown buf a := by
  constructor
  · intro h
    exact Nat.le_trans (le_alignUp y a) (le_roundDown_of_dvd ha h (dvd_alignUp ha))
  · intro h
    exact Nat.le_trans (alignUp_le_of_dvd h (dvd_roundDown buf ha)) (roundDown_le buf ha)

theorem isPowerOfTwo_max {a b : Nat} (ha : IsPowerOfTwo a) (hb : IsPowerOfTwo b) :
    IsPowerOfTwo (max a b) := by
  by_cases h : a ≤ b
  · rw [Nat.max_eq_right h]; exact hb
  · rw [Nat.max_eq_left (Nat.le_of_not_le h)]; exact ha

theorem isPowerOfTwo_min {a b : Nat} (ha : IsPowerOfTwo a) (hb : IsPowerOfTwo b) :
    IsPowerOfTwo (min a b) := by
  by_cases h : a ≤ b
  · rw [Nat.min_eq_left h]; exact ha
  · rw [Nat.min_eq_right (Nat.le_of_not_le h)]; exact hb

theorem isPowerOfTwo_dvd_of_le {a b : Nat}
    (ha : IsPowerOfTwo a) (hb : IsPowerOfTwo b) (hle : a ≤ b) : a ∣ b := by
  rcases ha with ⟨i, rfl⟩
  rcases hb with ⟨j, rfl⟩
  by_cases hij : i ≤ j
  · refine ⟨2 ^ (j - i), ?_⟩
    rw [← Nat.pow_add, Nat.add_sub_of_le hij]
  · have hji : j < i := Nat.lt_of_not_ge hij
    have hlt : 2 ^ j < 2 ^ i := Nat.pow_lt_pow_right (by decide : 1 < 2) hji
    omega

theorem effFieldAlign_pos {m : ReprModifier} {f : FieldLayout}
    (hf : AlignPos f) (hm : ModifierPackPos m) : 0 < effFieldAlign m f.align := by
  cases m with
  | none => exact hf
  | aligned _ => exact hf
  | packed p =>
    have hp : 0 < p := hm p rfl
    unfold AlignPos at hf
    simp only [effFieldAlign]
    omega

theorem effFieldAlign_pow2 {m : ReprModifier} {f : FieldLayout}
    (hf : AlignPow2 f) (hm : ModifierPow2 m) : IsPowerOfTwo (effFieldAlign m f.align) := by
  cases m with
  | none => exact hf
  | aligned _ => exact hf
  | packed p => exact isPowerOfTwo_min hf hm

theorem alignUp_packed_one_eff (cursor a : Nat) :
    alignUp cursor (effFieldAlign (.packed 1) a) = cursor := by
  simp only [effFieldAlign]
  by_cases ha : a = 0
  · subst ha
    simp [alignUp, paddingNeeded]
  · have hmin : min a 1 = 1 := by omega
    rw [hmin]
    exact alignUp_one cursor

end Toy.Layout
