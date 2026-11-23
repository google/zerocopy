/-!
# Soundness and Separation of `rustc_abi` Struct Layout (`#[repr(Rust)]` vs. `#[repr(C)]`),
# Zero-Sized Type Alignment Propagation, `#[repr(packed(N))]` / `#[repr(align(N))]`,
# `#[repr(transparent)]`, and `E0588` Retirement

Self-contained kernel-checked constructive formalization in Lean `v4.34.1`:
- Complete proofs with no unresolved proof holes or admitted lemmas
- Constructive `Nat` and `List` proofs only (axiom set strictly subset of `{propext, Quot.sound}`)
- Direct structural recursion and elementary `Nat` lemmas (no arithmetic solvers, bitvector reflection, or non-total definitions)
- Every definition marked `noncomputable def` explicitly so no unsafe compiler recursors are generated

Primary-source correspondence:
- `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `49d734536222bf28bb6d07d885b3a81d145981da`, `4e99638c7fb697db838c38669709c01bb7cc799a`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`):
  - `compiler/rustc_abi/src/layout.rs` (`layout_of_univariant`, `layout_of_univariant_biased`, `alignment_group_key`)
  - `compiler/rustc_abi/src/lib.rs` (`ReprOptions`, `LayoutData`, `is_1zst`)
  - `compiler/rustc_hir_analysis/src/check/check.rs` (`check_packed`, `check_packed_inner`, `check_transparent`)
  - `compiler/rustc_passes/src/{check_attr.rs, diagnostics.rs}` (`E0692`)
- `google/zerocopy` (`99238c633f747763a6ce9d403ab0007ddca72751` and `e8dcb7f08edbc19485c9e7980333607ebbff5f48`):
  - `zerocopy/src/wrappers.rs` (`Unalign<T>`, `ReadOnly<T>`)
  - `zerocopy/src/layout.rs` (`DstLayout::for_repr_c_struct`, `extend`, `pad_to_align`)
-/

namespace RustcAbiReprLayout

/-! ## Section 1: Constructive Alignment Arithmetic and Power-of-Two Algebra -/

/-- Power-of-two predicate on byte alignments (`1, 2, 4, 8, ...`). -/
noncomputable def IsPowerOfTwo (a : Nat) : Prop :=
  ∃ k : Nat, a = 2 ^ k

/-- Minimum padding bytes required to advance `cursor` to a multiple of `align`
(totalized to `0` when `align = 0`). -/
noncomputable def paddingNeeded (cursor align : Nat) : Nat :=
  if align = 0 then 0
  else
    let rem := cursor % align
    if rem = 0 then 0 else align - rem

/-- Upward cursor alignment to the least multiple of `align` greater than or equal
to `cursor` (`cursor` unchanged when `align = 0`). -/
noncomputable def alignUp (cursor align : Nat) : Nat :=
  cursor + paddingNeeded cursor align

/-- Declarative specification: `x` is the least multiple of `a` with `n ≤ x`. -/
noncomputable def IsLeastAlignedGe (x n a : Nat) : Prop :=
  n ≤ x ∧ a ∣ x ∧ ∀ m : Nat, n ≤ m → a ∣ m → x ≤ m

theorem paddingNeeded_zero_right (n : Nat) : paddingNeeded n 0 = 0 := by
  simp [paddingNeeded]

theorem paddingNeeded_zero_left (a : Nat) : paddingNeeded 0 a = 0 := by
  unfold paddingNeeded
  if ha : a = 0 then
    simp [ha]
  else
    simp [ha]

theorem alignUp_zero_left (a : Nat) : alignUp 0 a = 0 := by
  simp [alignUp, paddingNeeded_zero_left]

theorem alignUp_zero_right (n : Nat) : alignUp n 0 = n := by
  simp [alignUp, paddingNeeded_zero_right]

theorem alignUp_one (n : Nat) : alignUp n 1 = n := by
  simp [alignUp, paddingNeeded, Nat.mod_one]

theorem le_alignUp (n a : Nat) : n ≤ alignUp n a := by
  exact Nat.le_add_right n (paddingNeeded n a)

theorem paddingNeeded_lt (n a : Nat) (ha : 0 < a) : paddingNeeded n a < a := by
  unfold paddingNeeded
  have hne : a ≠ 0 := Nat.ne_of_gt ha
  simp only [hne, ↓reduceIte]
  if hrem : n % a = 0 then
    simp [hrem, ha]
  else
    simp only [hrem, ↓reduceIte]
    have hpos : 0 < n % a := Nat.pos_of_ne_zero hrem
    exact Nat.sub_lt ha hpos

theorem alignUp_lt_add (n a : Nat) (ha : 0 < a) : alignUp n a < n + a := by
  unfold alignUp
  exact Nat.add_lt_add_left (paddingNeeded_lt n a ha) n

theorem alignUp_eq_self_of_dvd {n a : Nat} (hd : a ∣ n) : alignUp n a = n := by
  unfold alignUp paddingNeeded
  if ha : a = 0 then
    simp [ha]
  else
    have hmod : n % a = 0 := Nat.mod_eq_zero_of_dvd hd
    simp [ha, hmod]

theorem dvd_alignUp (n a : Nat) (ha : 0 < a) : a ∣ alignUp n a := by
  unfold alignUp paddingNeeded
  have hne : a ≠ 0 := Nat.ne_of_gt ha
  simp only [hne, ↓reduceIte]
  if hrem : n % a = 0 then
    simp only [hrem, ↓reduceIte, Nat.add_zero]
    exact Nat.dvd_of_mod_eq_zero hrem
  else
    simp only [hrem, ↓reduceIte]
    have hle : n % a ≤ a := Nat.le_of_lt (Nat.mod_lt n ha)
    have hdiv : (n / a) * a + n % a = n := Nat.div_add_mod' n a
    have heq : n + (a - n % a) = (n / a + 1) * a := by
      calc
        n + (a - n % a)
            = ((n / a) * a + n % a) + (a - n % a) := by rw [hdiv]
        _   = (n / a) * a + (n % a + (a - n % a)) := by rw [Nat.add_assoc]
        _   = (n / a) * a + a := by rw [Nat.add_sub_of_le hle]
        _   = (n / a + 1) * a := by rw [Nat.succ_mul]
    rw [heq]
    exact Nat.dvd_mul_left a (n / a + 1)

private theorem nat_lt_of_mul_lt_mul_right {a b c : Nat} (h : a * c < b * c) : a < b := by
  if hlt : a < b then
    exact hlt
  else
    have hle : b ≤ a := Nat.le_of_not_lt hlt
    have hmul : b * c ≤ a * c := Nat.mul_le_mul_right c hle
    exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hmul h))

theorem alignUp_minimal {n a m : Nat} (ha : 0 < a) (hle : n ≤ m) (hd : a ∣ m) :
    alignUp n a ≤ m := by
  if hrem : n % a = 0 then
    have hdvd : a ∣ n := Nat.dvd_of_mod_eq_zero hrem
    rw [alignUp_eq_self_of_dvd hdvd]
    exact hle
  else
    have hmod_m : m % a = 0 := Nat.mod_eq_zero_of_dvd hd
    have hdiv_lt : n / a < m / a := by
      have hdecomp_n : (n / a) * a + n % a = n := Nat.div_add_mod' n a
      have hdecomp_m : (m / a) * a + m % a = m := Nat.div_add_mod' m a
      rw [hmod_m, Nat.add_zero] at hdecomp_m
      have hpos : 0 < n % a := Nat.pos_of_ne_zero hrem
      have h1 : (n / a) * a < (m / a) * a := by
        calc
          (n / a) * a < (n / a) * a + n % a := Nat.lt_add_of_pos_right hpos
          _ = n := hdecomp_n
          _ ≤ m := hle
          _ = (m / a) * a := hdecomp_m.symm
      exact nat_lt_of_mul_lt_mul_right h1
    have hsucc_le : n / a + 1 ≤ m / a := Nat.succ_le_of_lt hdiv_lt
    have hmul_le : (n / a + 1) * a ≤ (m / a) * a := Nat.mul_le_mul_right a hsucc_le
    have hdecomp_m : (m / a) * a = m := by
      have h := Nat.div_add_mod' m a
      rw [hmod_m, Nat.add_zero] at h
      exact h
    have hne : a ≠ 0 := Nat.ne_of_gt ha
    have hle_rem : n % a ≤ a := Nat.le_of_lt (Nat.mod_lt n ha)
    have hdecomp_n : (n / a) * a + n % a = n := Nat.div_add_mod' n a
    have heq : alignUp n a = (n / a + 1) * a := by
      unfold alignUp paddingNeeded
      simp only [hne, ↓reduceIte, hrem]
      calc
        n + (a - n % a)
            = ((n / a) * a + n % a) + (a - n % a) := by rw [hdecomp_n]
        _   = (n / a) * a + (n % a + (a - n % a)) := by rw [Nat.add_assoc]
        _   = (n / a) * a + a := by rw [Nat.add_sub_of_le hle_rem]
        _   = (n / a + 1) * a := by rw [Nat.succ_mul]
    rw [heq, ← hdecomp_m]
    exact hmul_le

theorem alignUp_isLeastAlignedGe (n a : Nat) (ha : 0 < a) :
    IsLeastAlignedGe (alignUp n a) n a :=
  ⟨le_alignUp n a, dvd_alignUp n a ha, fun _ hle hd => alignUp_minimal ha hle hd⟩

theorem alignUp_mono {n1 n2 a : Nat} (ha : 0 < a) (hle : n1 ≤ n2) :
    alignUp n1 a ≤ alignUp n2 a := by
  exact alignUp_minimal ha (Nat.le_trans hle (le_alignUp n2 a)) (dvd_alignUp n2 a ha)

theorem alignUp_le_alignUp_of_dvd {n a b : Nat} (hb : 0 < b) (hd : a ∣ b) :
    alignUp n a ≤ alignUp n b := by
  have ha : 0 < a := by
    rcases hd with ⟨k, rfl⟩
    cases a with
    | zero =>
      simp only [Nat.zero_mul] at hb
      exact False.elim (Nat.lt_irrefl 0 hb)
    | succ a' => exact Nat.succ_pos a'
  exact alignUp_minimal ha (le_alignUp n b) (Nat.dvd_trans hd (dvd_alignUp n b hb))

theorem alignUp_idem_of_dvd {n a b : Nat} (hb : 0 < b) (hd : a ∣ b) :
    alignUp (alignUp n a) b = alignUp n b := by
  have h1 : alignUp (alignUp n a) b ≤ alignUp n b :=
    alignUp_minimal hb (alignUp_le_alignUp_of_dvd hb hd) (dvd_alignUp n b hb)
  have h2 : alignUp n b ≤ alignUp (alignUp n a) b :=
    alignUp_minimal hb (Nat.le_trans (le_alignUp n a) (le_alignUp (alignUp n a) b))
      (dvd_alignUp (alignUp n a) b hb)
  exact Nat.le_antisymm h1 h2

theorem max_comm_nat (a b : Nat) : max a b = max b a := Nat.max_comm a b

theorem max_assoc_nat (a b c : Nat) : max (max a b) c = max a (max b c) :=
  Nat.max_assoc a b c

theorem nat_max_le_max {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) : max a b ≤ max c d :=
  Nat.max_le.mpr ⟨Nat.le_trans h1 (Nat.le_max_left c d), Nat.le_trans h2 (Nat.le_max_right c d)⟩

theorem nat_min_le_min {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) : min a b ≤ min c d :=
  Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left a b) h1, Nat.le_trans (Nat.min_le_right a b) h2⟩

theorem pow2_pos {a : Nat} (hp : IsPowerOfTwo a) : 0 < a := by
  rcases hp with ⟨k, rfl⟩
  exact Nat.two_pow_pos k

private theorem two_pow_le_two_pow_add (k d : Nat) : 2 ^ k ≤ 2 ^ (k + d) := by
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have hstep : 2 ^ (k + d) ≤ 2 ^ (k + d) + 2 ^ (k + d) := Nat.le_add_right _ _
    have hpow : 2 ^ (k + Nat.succ d) = 2 ^ (k + d) + 2 ^ (k + d) := by
      rw [Nat.add_succ, Nat.pow_succ, Nat.mul_two]
    rw [hpow]
    exact Nat.le_trans ih hstep

private theorem two_pow_lt_two_pow_of_lt {j k : Nat} (h : j < k) : 2 ^ j < 2 ^ k := by
  have hk_eq : j + 1 + (k - (j + 1)) = k := Nat.add_sub_of_le h
  have hstep : 2 ^ j < 2 ^ (j + 1) := by
    have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
    rw [Nat.pow_succ, Nat.mul_two]
    exact Nat.lt_add_of_pos_right hpos
  have htail : 2 ^ (j + 1) ≤ 2 ^ k := by
    rw [← hk_eq]
    exact two_pow_le_two_pow_add (j + 1) (k - (j + 1))
  exact Nat.lt_of_lt_of_le hstep htail

theorem pow2_dvd_iff_le {j k : Nat} : 2 ^ j ∣ 2 ^ k ↔ j ≤ k := by
  constructor
  · intro hd
    if h : j ≤ k then
      exact h
    else
      have hklt : k < j := Nat.lt_of_not_le h
      have hpow_lt : 2 ^ k < 2 ^ j := two_pow_lt_two_pow_of_lt hklt
      have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
      have hle : 2 ^ j ≤ 2 ^ k := Nat.le_of_dvd hpos hd
      exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle hpow_lt))
  · intro hle
    exact Nat.pow_dvd_pow 2 hle

theorem pow2_dvd_or_dvd {a b : Nat} (ha : IsPowerOfTwo a) (hb : IsPowerOfTwo b) :
    a ∣ b ∨ b ∣ a := by
  rcases ha with ⟨j, rfl⟩
  rcases hb with ⟨k, rfl⟩
  cases Nat.le_total j k with
  | inl h => exact Or.inl (Nat.pow_dvd_pow 2 h)
  | inr h => exact Or.inr (Nat.pow_dvd_pow 2 h)

theorem pow2_dvd_of_le {a b : Nat} (ha : IsPowerOfTwo a) (hb : IsPowerOfTwo b) (hle : a ≤ b) :
    a ∣ b := by
  rcases ha with ⟨j, rfl⟩
  rcases hb with ⟨k, rfl⟩
  have hjk : j ≤ k := by
    if h : j ≤ k then
      exact h
    else
      have hk : k < j := Nat.lt_of_not_le h
      have hlt : 2 ^ k < 2 ^ j := two_pow_lt_two_pow_of_lt hk
      exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle hlt))
  exact Nat.pow_dvd_pow 2 hjk

theorem pow2_max {a b : Nat} (ha : IsPowerOfTwo a) (hb : IsPowerOfTwo b) :
    IsPowerOfTwo (max a b) := by
  cases Nat.le_total a b with
  | inl h => rw [Nat.max_eq_right h]; exact hb
  | inr h => rw [Nat.max_eq_left h]; exact ha

theorem pow2_min {a b : Nat} (ha : IsPowerOfTwo a) (hb : IsPowerOfTwo b) :
    IsPowerOfTwo (min a b) := by
  cases Nat.le_total a b with
  | inl h => rw [Nat.min_eq_left h]; exact ha
  | inr h => rw [Nat.min_eq_right h]; exact hb

theorem pow2_one : IsPowerOfTwo 1 := ⟨0, rfl⟩

theorem pow2_min_dvd_of_le {a p1 p2 : Nat}
    (ha : IsPowerOfTwo a) (hp1 : IsPowerOfTwo p1) (hp2 : IsPowerOfTwo p2) (hle : p1 ≤ p2) :
    min a p1 ∣ min a p2 := by
  have hmin1 : IsPowerOfTwo (min a p1) := pow2_min ha hp1
  have hmin2 : IsPowerOfTwo (min a p2) := pow2_min ha hp2
  have hmin_le : min a p1 ≤ min a p2 := by
    cases Nat.le_total a p1 with
    | inl hap1 =>
      rw [Nat.min_eq_left hap1]
      exact Nat.le_min.mpr ⟨Nat.le_refl a, Nat.le_trans hap1 hle⟩
    | inr hp1a =>
      rw [Nat.min_eq_right hp1a]
      exact Nat.le_min.mpr ⟨hp1a, hle⟩
  exact pow2_dvd_of_le hmin1 hmin2 hmin_le

theorem min_dvd_left_pow2 {a p : Nat} (ha : IsPowerOfTwo a) (hp : IsPowerOfTwo p) :
    min a p ∣ a := by
  exact pow2_dvd_of_le (pow2_min ha hp) ha (Nat.min_le_left a p)

theorem min_dvd_right_pow2 {a p : Nat} (ha : IsPowerOfTwo a) (hp : IsPowerOfTwo p) :
    min a p ∣ p := by
  exact pow2_dvd_of_le (pow2_min ha hp) hp (Nat.min_le_right a p)

/-! ## Section 2: `rustc_abi` Representation Options, Fields, and Layout Records -/

/-- Primitive register classification matching `rustc_abi::Primitive`. -/
inductive PrimKind where
  | int
  | float
  | pointer

/-- Structural equality on `PrimKind`. -/
noncomputable def PrimKind.beq : PrimKind → PrimKind → Bool
  | .int, .int => true
  | .float, .float => true
  | .pointer, .pointer => true
  | _, _ => false

/-- Register/memory ABI classification matching `rustc_abi::BackendRepr`. -/
inductive BackendRepr where
  | scalar (prim : PrimKind) (sizeBytes : Nat)
  | scalarPair (p1 p2 : PrimKind) (s1 s2 : Nat)
  | memory (sized : Bool)

/-- Structural equality on `BackendRepr`. -/
noncomputable def BackendRepr.beq : BackendRepr → BackendRepr → Bool
  | .scalar p1 s1, .scalar p2 s2 => PrimKind.beq p1 p2 && (s1 == s2)
  | .scalarPair a1 b1 s1 t1, .scalarPair a2 b2 s2 t2 =>
    PrimKind.beq a1 a2 && PrimKind.beq b1 b2 && (s1 == s2) && (t1 == t2)
  | .memory x, .memory y => x == y
  | _, _ => false

/-- Type layout metadata of a field (`rustc_abi::LayoutData` projection). -/
structure FieldSpec where
  size : Nat
  align : Nat
  unadjustedAbiAlign : Nat
  reprAlign : Option Nat
  maxReprAlign : Option Nat
  isReprC : Bool
  hasNiche : Bool
  backendRepr : BackendRepr

/-- Zero-sized field check (`LayoutData::is_zst` on sized types). -/
noncomputable def FieldSpec.isZst (f : FieldSpec) : Bool :=
  f.size == 0

/-- 1-aligned zero-sized field check (`LayoutData::is_1zst` at `rustc_abi/src/lib.rs:2396`). -/
noncomputable def FieldSpec.is1Zst (f : FieldSpec) : Bool :=
  (f.size == 0) && (f.align == 1)

/-- Maximum over optional alignments (`Option<Align>`). -/
noncomputable def optMax : Option Nat → Option Nat → Option Nat
  | none, none => none
  | some a, none => some a
  | none, some b => some b
  | some a, some b => some (max a b)

theorem optMax_comm (a b : Option Nat) : optMax a b = optMax b a := by
  cases a <;> cases b <;> simp [optMax, Nat.max_comm]

theorem optMax_assoc (a b c : Option Nat) :
    optMax (optMax a b) c = optMax a (optMax b c) := by
  cases a <;> cases b <;> cases c <;> simp [optMax, Nat.max_assoc]

/-- Effective `#[repr(...)]` struct kind. -/
inductive ReprKind where
  | rust
  | c
  | transparent

noncomputable def ReprKind.beq : ReprKind → ReprKind → Bool
  | .rust, .rust => true
  | .c, .c => true
  | .transparent, .transparent => true
  | _, _ => false

/-- Struct representation flags (`rustc_abi::ReprOptions`). -/
structure ReprOptions where
  kind : ReprKind
  pack : Option Nat
  align : Option Nat
  randomizeLayout : Bool

/-- Mirrors `ReprOptions::inhibit_struct_field_reordering` (`rustc_abi/src/lib.rs:234`).
Note: `IS_TRANSPARENT` is NOT in `FIELD_ORDER_UNOPTIMIZABLE`. -/
noncomputable def ReprOptions.inhibitStructFieldReordering (r : ReprOptions) : Bool :=
  ReprKind.beq r.kind .c

/-- Mirrors `ReprOptions::can_randomize_type_layout` (`rustc_abi/src/lib.rs:240`). -/
noncomputable def ReprOptions.canRandomizeTypeLayout (r : ReprOptions) : Bool :=
  (!r.inhibitStructFieldReordering) && r.randomizeLayout

/-- Mirrors `ReprOptions::inhibit_newtype_abi_optimization` (`rustc_abi/src/lib.rs:228`). -/
noncomputable def ReprOptions.inhibitNewtypeAbiOpt (r : ReprOptions) : Bool :=
  ReprKind.beq r.kind .c

/-- Effective alignment of a field under an optional `#[repr(packed(N))]` clamp. -/
noncomputable def effFieldAlign (pack : Option Nat) (fieldAlign : Nat) : Nat :=
  match pack with
  | some p => min fieldAlign p
  | none => fieldAlign

/-- Computed layout of a struct (`rustc_abi::LayoutData`). -/
structure StructLayout where
  offsets : List Nat
  endOffset : Nat
  size : Nat
  align : Nat
  unadjustedAbiAlign : Nat
  maxReprAlign : Option Nat
  backendRepr : BackendRepr
  isReprC : Bool

/-- Positivity invariants on field lists and representation options. -/
noncomputable def AllAlignPos (fields : List FieldSpec) : Prop :=
  ∀ f, f ∈ fields → 0 < f.align

noncomputable def AllPow2Align (fields : List FieldSpec) : Prop :=
  ∀ f, f ∈ fields → IsPowerOfTwo f.align

noncomputable def PackPos (pack : Option Nat) : Prop :=
  ∀ p, pack = some p → 0 < p

noncomputable def ReprModifierValid (r : ReprOptions) : Prop :=
  PackPos r.pack ∧ (∀ a, r.align = some a → 0 < a)

noncomputable def ReprModifierPow2 (r : ReprOptions) : Prop :=
  (∀ p, r.pack = some p → IsPowerOfTwo p) ∧ (∀ a, r.align = some a → IsPowerOfTwo a)

theorem effFieldAlign_pos {pack : Option Nat} {a : Nat}
    (hp : PackPos pack) (ha : 0 < a) : 0 < effFieldAlign pack a := by
  cases pack with
  | none => exact ha
  | some p =>
    have hpos : 0 < p := hp p rfl
    exact Nat.lt_min.mpr ⟨ha, hpos⟩

theorem effFieldAlign_pow2 {pack : Option Nat} {a : Nat}
    (hp : ∀ p, pack = some p → IsPowerOfTwo p) (ha : IsPowerOfTwo a) :
    IsPowerOfTwo (effFieldAlign pack a) := by
  cases pack with
  | none => exact ha
  | some p => exact pow2_min ha (hp p rfl)

theorem effFieldAlign_le_self (pack : Option Nat) (a : Nat) :
    effFieldAlign pack a ≤ a := by
  cases pack with
  | none => exact Nat.le_refl a
  | some p => exact Nat.min_le_left a p

/-! ## Section 3: Field Placement, Aggregate Alignment, ABI Unpacking, & `DstLayout` -/

/-- Sequential field placement starting at `cursor` (`layout_of_univariant_biased` loop
at `compiler/rustc_abi/src/layout.rs:764-805`). -/
noncomputable def placeFieldsFrom (pack : Option Nat) (cursor : Nat) :
    List FieldSpec → List Nat × Nat
  | [] => ([], cursor)
  | f :: fs =>
    let fa := effFieldAlign pack f.align
    let off := alignUp cursor fa
    let rest := placeFieldsFrom pack (off + f.size) fs
    (off :: rest.1, rest.2)

/-- Accumulated effective alignment initialized at `1` (`dl.aggregate_align` / `dl.i8_align`). -/
noncomputable def fieldsMaxEffAlign (pack : Option Nat) (acc : Nat) : List FieldSpec → Nat
  | [] => acc
  | f :: fs => fieldsMaxEffAlign pack (max acc (effFieldAlign pack f.align)) fs

/-- Accumulated `max_repr_align` across fields (`layout.rs:783`). -/
noncomputable def fieldsMaxReprAlign (acc : Option Nat) : List FieldSpec → Option Nat
  | [] => acc
  | f :: fs => fieldsMaxReprAlign (optMax acc f.maxReprAlign) fs

/-- Total sum of field sizes without padding. -/
noncomputable def totalFieldSize : List FieldSpec → Nat
  | [] => 0
  | f :: fs => f.size + totalFieldSize fs

/-- Count of non-ZST fields (`!f.isZst`). -/
noncomputable def nonZstFields : List FieldSpec → List FieldSpec
  | [] => []
  | f :: fs => if f.isZst then nonZstFields fs else f :: nonZstFields fs

/-- Check whether any field is `#[repr(C)]` (`layout.rs:918`). -/
noncomputable def anyFieldReprC : List FieldSpec → Bool
  | [] => false
  | f :: fs => f.isReprC || anyFieldReprC fs

/-- Compute `BackendRepr` for a sized univariant struct (`layout.rs:823-902`). -/
noncomputable def computeBackendRepr (repr : ReprOptions) (fields : List FieldSpec)
    (offsets : List Nat) (size align : Nat) : BackendRepr :=
  if size == 0 then .memory true
  else
    match nonZstFields fields with
    | [f] =>
      let _ := offsets
      if align == f.align && size == f.size then
        match f.backendRepr with
        | .scalar _ _ =>
          if repr.inhibitNewtypeAbiOpt then .memory true else f.backendRepr
        | .scalarPair _ _ _ _ => f.backendRepr
        | .memory _ => .memory true
      else .memory true
    | _ => .memory true

/-- Compute `unadjusted_abi_align` (`layout.rs:809, 905-915`), capturing the
`#[repr(transparent)]` single-non-ZST-field forwarding vs. all-ZST `align` fallback. -/
noncomputable def computeUnadjustedAbiAlign (repr : ReprOptions) (fields : List FieldSpec)
    (preAlignFinal finalAlign : Nat) : Nat :=
  if ReprKind.beq repr.kind .transparent then
    match nonZstFields fields with
    | [f] => f.unadjustedAbiAlign
    | _ => finalAlign
  else preAlignFinal

/-- Complete univariant layout computation for an explicit field placement order
(`layout_of_univariant_biased`, `compiler/rustc_abi/src/layout.rs:590-935`). -/
noncomputable def computeOrderedLayout (repr : ReprOptions) (fields : List FieldSpec) :
    StructLayout :=
  let placed := placeFieldsFrom repr.pack 0 fields
  let preAlign := fieldsMaxEffAlign repr.pack 1 fields
  let finalAlign := match repr.align with
    | some ra => max preAlign ra
    | none => preAlign
  let size := alignUp placed.2 finalAlign
  let maxRepr := fieldsMaxReprAlign repr.align fields
  let unadj := computeUnadjustedAbiAlign repr fields preAlign finalAlign
  let isC := ReprKind.beq repr.kind .c ||
    (ReprKind.beq repr.kind .transparent && anyFieldReprC fields)
  let abi := computeBackendRepr repr fields placed.1 size finalAlign
  { offsets := placed.1
    endOffset := placed.2
    size := size
    align := finalAlign
    unadjustedAbiAlign := unadj
    maxReprAlign := maxRepr
    backendRepr := abi
    isReprC := isC }

/-- Effective size-or-align sort key matching `rustc_abi` `alignment_group_key`
(`compiler/rustc_abi/src/layout.rs:654-690`). -/
noncomputable def alignmentGroupKey (pack : Option Nat) (f : FieldSpec) : Nat :=
  match pack with
  | some p => min f.align p
  | none => max f.align f.size

/-- Insert a field in descending `alignmentGroupKey` order (stable sort matching
`optimizing.sort_by_key(|&x| Reverse(alignment_group_key(f)))`). -/
noncomputable def insertDescByGroup (pack : Option Nat) (f : FieldSpec) :
    List FieldSpec → List FieldSpec
  | [] => [f]
  | g :: gs =>
    if alignmentGroupKey pack g ≤ alignmentGroupKey pack f then
      f :: g :: gs
    else
      g :: insertDescByGroup pack f gs

/-- Deterministic `#[repr(Rust)]` field reordering (`layout.rs:702-729` when
`optimize_field_order && fields.len() > 1 && !can_randomize`). -/
noncomputable def sortFieldsByAlignGroup (pack : Option Nat) :
    List FieldSpec → List FieldSpec
  | [] => []
  | f :: fs => insertDescByGroup pack f (sortFieldsByAlignGroup pack fs)

/-- Default deterministic `#[repr(Rust)]` struct layout calculator. -/
noncomputable def computeReprRustLayout (repr : ReprOptions) (fields : List FieldSpec) :
    StructLayout :=
  let ordered :=
    if repr.inhibitStructFieldReordering then fields
    else sortFieldsByAlignGroup repr.pack fields
  computeOrderedLayout repr ordered

/-- `google/zerocopy` `DstLayout` state (`zerocopy/src/layout.rs:34-50, 1153-1495`). -/
structure ZcDstLayout where
  align : Nat
  size : Nat

noncomputable def zcNewZst (reprAlign : Option Nat) : ZcDstLayout :=
  match reprAlign with
  | some a => { align := a, size := 0 }
  | none => { align := 1, size := 0 }

noncomputable def zcExtend (self field : ZcDstLayout) (reprPacked : Option Nat) : ZcDstLayout :=
  let fieldAlign := effFieldAlign reprPacked field.align
  let align := max self.align fieldAlign
  let padding := paddingNeeded self.size fieldAlign
  let offset := self.size + padding
  { align := align, size := offset + field.size }

noncomputable def zcExtendList (acc : ZcDstLayout) (reprPacked : Option Nat) :
    List ZcDstLayout → ZcDstLayout
  | [] => acc
  | f :: fs => zcExtendList (zcExtend acc f reprPacked) reprPacked fs

noncomputable def zcPadToAlign (self : ZcDstLayout) : ZcDstLayout :=
  { align := self.align, size := alignUp self.size self.align }

/-- Mirrors `DstLayout::for_repr_c_struct` (`zerocopy/src/layout.rs:1153-1197`). -/
noncomputable def zcForReprCStruct (reprAlign reprPacked : Option Nat)
    (fields : List ZcDstLayout) : ZcDstLayout :=
  zcPadToAlign (zcExtendList (zcNewZst reprAlign) reprPacked fields)

noncomputable def fieldToZcDst (f : FieldSpec) : ZcDstLayout :=
  { align := f.align, size := f.size }

noncomputable def fieldsToZcDst : List FieldSpec → List ZcDstLayout
  | [] => []
  | f :: fs => fieldToZcDst f :: fieldsToZcDst fs

/-! ## Section 4: `#[repr]` Diagnostics and the `E0588` Retirement Boundary -/

/-- Compiler release epoch for `check_packed_inner` (`4e99638c7fb697db838c38669709c01bb7cc799a`,
2026-09-14: turned `E0588` into lint `ALIGNED_FIELDS_IN_PACKED` restricted to `repr(C)`). -/
inductive CheckPackedEra where
  | pre4e99638
  | post4e99638

/-- Representation diagnostics modeled from `rustc_hir_analysis` and `rustc_passes`. -/
inductive ReprDiagnostic where
  | ok
  | errE0587   -- conflicting packed and align on the same type
  | errE0588   -- packed type transitively contains #[repr(align)] (pre-4e99638)
  | lintAlignedFieldsInPacked -- deny-by-default lint on repr(C, packed) -> repr(C, align) (post-4e99638)
  | errE0690   -- transparent struct needs at most one non-trivial field
  | errE0692   -- transparent struct cannot have other repr hints

/-- Simplified field AST shape capturing how `check_packed_inner` inspects direct `ty::Adt`
fields vs. generic `ty::Param` / tuple / array wrappers (`check.rs:1754-1780`). -/
inductive FieldCheckNode where
  | adt (isC : Bool) (hasAlign : Bool) (children : List FieldCheckNode)
  | genericParam (instantiatedIsC : Bool) (instantiatedHasAlign : Bool)
  | tupleOrArray

/-- Transitive check matching `check_packed_inner` (`check.rs:1716-1742` pre-4e99638,
`check.rs:1754-1780` post-4e99638). -/
noncomputable def checkPackedInnerList (requireC : Bool) : List FieldCheckNode → Bool
  | [] => false
  | .adt isC hasAlign children :: rest =>
    let hitsNode := (!requireC || isC) && (hasAlign || checkPackedInnerList requireC children)
    hitsNode || checkPackedInnerList requireC rest
  | .genericParam _ _ :: rest =>
    -- `check_packed_inner` inspects uninstantiated identity types; `ty::Param` is skipped!
    checkPackedInnerList requireC rest
  | .tupleOrArray :: rest =>
    -- `check_packed_inner` matches only `ty::Adt`
    checkPackedInnerList requireC rest

/-- Mirrors `check_packed` across `1.98.0-nightly` / `49d734536` (`pre4e99638`) and
`1.102.0-nightly` / `3ef0c22cd` (`post4e99638`). -/
noncomputable def checkPacked (era : CheckPackedEra) (repr : ReprOptions)
    (fields : List FieldCheckNode) : ReprDiagnostic :=
  match repr.pack with
  | none => .ok
  | some _ =>
    match repr.align with
    | some _ => .errE0587
    | none =>
      match era with
      | .pre4e99638 =>
        if checkPackedInnerList false fields then .errE0588 else .ok
      | .post4e99638 =>
        if ReprKind.beq repr.kind .c && checkPackedInnerList true fields then
          .lintAlignedFieldsInPacked
        else .ok

/-- Count fields that fail triviality (`!f.is1Zst || f.isReprC`, `check.rs:1863-1895`). -/
noncomputable def countNonTrivialFields : List FieldSpec → Nat
  | [] => 0
  | f :: fs =>
    let nonTriv := if (!f.is1Zst) || f.isReprC then 1 else 0
    nonTriv + countNonTrivialFields fs

/-- Mirrors `CheckAttrVisitor` (`E0692`) + `check_transparent` (`E0690`, `check.rs:1804`
early exit when `fields.length ≤ 1`). -/
noncomputable def checkTransparent (repr : ReprOptions) (hasOtherReprHint : Bool)
    (fields : List FieldSpec) : ReprDiagnostic :=
  if ReprKind.beq repr.kind .transparent then
    if hasOtherReprHint then .errE0692
    else if fields.length ≤ 1 then .ok
    else if countNonTrivialFields fields > 1 then .errE0690
    else .ok
  else .ok

/-! ## Section 5: Theorem Family 1 — Non-Overlapping In-Bounds Offsets & Alignment Divisibility -/

noncomputable def OffsetsLengthMatch (fields : List FieldSpec) (L : StructLayout) : Prop :=
  L.offsets.length = fields.length

noncomputable def OffsetsEffAligned (pack : Option Nat) (fields : List FieldSpec)
    (L : StructLayout) : Prop :=
  ∀ (i : Nat) (hf : i < fields.length) (ho : i < L.offsets.length),
    effFieldAlign pack fields[i].align ∣ L.offsets[i]

noncomputable def OrderedNonOverlapping (fields : List FieldSpec) (L : StructLayout) : Prop :=
  ∀ (i j : Nat) (hi : i < fields.length) (hj : j < fields.length)
    (hoi : i < L.offsets.length) (hoj : j < L.offsets.length),
    i < j → L.offsets[i] + fields[i].size ≤ L.offsets[j]

noncomputable def FieldsDisjoint (fields : List FieldSpec) (L : StructLayout) : Prop :=
  ∀ (i j : Nat) (hi : i < fields.length) (hj : j < fields.length)
    (hoi : i < L.offsets.length) (hoj : j < L.offsets.length),
    i ≠ j →
      L.offsets[i] + fields[i].size ≤ L.offsets[j] ∨
      L.offsets[j] + fields[j].size ≤ L.offsets[i]

noncomputable def FieldsInBounds (fields : List FieldSpec) (L : StructLayout) : Prop :=
  (∀ (i : Nat) (hf : i < fields.length) (ho : i < L.offsets.length),
    L.offsets[i] + fields[i].size ≤ L.endOffset) ∧
  L.endOffset ≤ L.size

noncomputable def SizeAlignedMinimal (L : StructLayout) : Prop :=
  0 < L.align ∧ L.align ∣ L.size ∧ IsLeastAlignedGe L.size L.endOffset L.align

theorem placeFieldsFrom_length (pack : Option Nat) (cursor : Nat) (fs : List FieldSpec) :
    (placeFieldsFrom pack cursor fs).1.length = fs.length := by
  induction fs generalizing cursor with
  | nil => rfl
  | cons f fs ih =>
    simp only [placeFieldsFrom, List.length_cons]
    exact congrArg Nat.succ (ih _)

theorem placeFieldsFrom_cursor_le_end (pack : Option Nat) (cursor : Nat)
    (fs : List FieldSpec) :
    cursor ≤ (placeFieldsFrom pack cursor fs).2 := by
  induction fs generalizing cursor with
  | nil => exact Nat.le_refl cursor
  | cons f fs ih =>
    simp only [placeFieldsFrom]
    have h1 : cursor ≤ alignUp cursor (effFieldAlign pack f.align) := le_alignUp _ _
    have h2 : alignUp cursor (effFieldAlign pack f.align) ≤
        alignUp cursor (effFieldAlign pack f.align) + f.size := Nat.le_add_right _ _
    exact Nat.le_trans (Nat.le_trans h1 h2) (ih _)

theorem placeFieldsFrom_offsets_ge_cursor (pack : Option Nat) (cursor : Nat)
    (fs : List FieldSpec) :
    ∀ (i : Nat) (h : i < (placeFieldsFrom pack cursor fs).1.length),
      cursor ≤ (placeFieldsFrom pack cursor fs).1[i] := by
  induction fs generalizing cursor with
  | nil =>
    intro i h
    simp [placeFieldsFrom] at h
  | cons f fs ih =>
    intro i h
    cases i with
    | zero =>
      simp only [placeFieldsFrom, List.getElem_cons_zero]
      exact le_alignUp cursor (effFieldAlign pack f.align)
    | succ k =>
      simp only [placeFieldsFrom, List.getElem_cons_succ]
      have hk : k < (placeFieldsFrom pack
          (alignUp cursor (effFieldAlign pack f.align) + f.size) fs).1.length := by
        simp only [placeFieldsFrom, List.length_cons] at h
        exact Nat.lt_of_succ_lt_succ h
      have hsub := ih (alignUp cursor (effFieldAlign pack f.align) + f.size) k hk
      have h1 : cursor ≤ alignUp cursor (effFieldAlign pack f.align) := le_alignUp _ _
      have h2 : alignUp cursor (effFieldAlign pack f.align) ≤
          alignUp cursor (effFieldAlign pack f.align) + f.size := Nat.le_add_right _ _
      exact Nat.le_trans (Nat.le_trans h1 h2) hsub

theorem placeFieldsFrom_aligned (pack : Option Nat) (cursor : Nat) (fs : List FieldSpec)
    (hp : PackPos pack) (ha : AllAlignPos fs) :
    ∀ (i : Nat) (hf : i < fs.length) (ho : i < (placeFieldsFrom pack cursor fs).1.length),
      effFieldAlign pack fs[i].align ∣ (placeFieldsFrom pack cursor fs).1[i] := by
  induction fs generalizing cursor with
  | nil =>
    intro i hf
    cases hf
  | cons f fs ih =>
    intro i hf ho
    cases i with
    | zero =>
      simp only [placeFieldsFrom, List.getElem_cons_zero]
      have hfa : 0 < effFieldAlign pack f.align :=
        effFieldAlign_pos hp (ha f (List.mem_cons_self))
      exact dvd_alignUp cursor (effFieldAlign pack f.align) hfa
    | succ k =>
      simp only [placeFieldsFrom, List.getElem_cons_succ]
      have ha_tail : AllAlignPos fs := fun g hg => ha g (List.mem_cons_of_mem f hg)
      have hkf : k < fs.length := Nat.lt_of_succ_lt_succ hf
      have hko : k < (placeFieldsFrom pack
          (alignUp cursor (effFieldAlign pack f.align) + f.size) fs).1.length := by
        simp only [placeFieldsFrom, List.length_cons] at ho
        exact Nat.lt_of_succ_lt_succ ho
      exact ih (alignUp cursor (effFieldAlign pack f.align) + f.size) ha_tail k hkf hko

theorem placeFieldsFrom_ordered_non_overlapping (pack : Option Nat) (cursor : Nat)
    (fs : List FieldSpec) :
    ∀ (i j : Nat) (hi : i < fs.length) (_hj : j < fs.length)
      (hoi : i < (placeFieldsFrom pack cursor fs).1.length)
      (hoj : j < (placeFieldsFrom pack cursor fs).1.length),
      i < j →
        (placeFieldsFrom pack cursor fs).1[i] + fs[i].size ≤
          (placeFieldsFrom pack cursor fs).1[j] := by
  induction fs generalizing cursor with
  | nil =>
    intro i j hi
    cases hi
  | cons f fs ih =>
    intro i j hi _hj hoi hoj hij
    cases i with
    | zero =>
      cases j with
      | zero => exact False.elim (Nat.lt_irrefl 0 hij)
      | succ k =>
        simp only [placeFieldsFrom, List.getElem_cons_zero, List.getElem_cons_succ]
        have hko : k < (placeFieldsFrom pack
            (alignUp cursor (effFieldAlign pack f.align) + f.size) fs).1.length := by
          simp only [placeFieldsFrom, List.length_cons] at hoj
          exact Nat.lt_of_succ_lt_succ hoj
        exact placeFieldsFrom_offsets_ge_cursor pack
          (alignUp cursor (effFieldAlign pack f.align) + f.size) fs k hko
    | succ i' =>
      cases j with
      | zero => exact False.elim (Nat.not_lt_zero _ hij)
      | succ j' =>
        simp only [placeFieldsFrom, List.getElem_cons_succ]
        have hi' : i' < fs.length := Nat.lt_of_succ_lt_succ hi
        have hj' : j' < fs.length := Nat.lt_of_succ_lt_succ _hj
        have hoi' : i' < (placeFieldsFrom pack
            (alignUp cursor (effFieldAlign pack f.align) + f.size) fs).1.length := by
          simp only [placeFieldsFrom, List.length_cons] at hoi
          exact Nat.lt_of_succ_lt_succ hoi
        have hoj' : j' < (placeFieldsFrom pack
            (alignUp cursor (effFieldAlign pack f.align) + f.size) fs).1.length := by
          simp only [placeFieldsFrom, List.length_cons] at hoj
          exact Nat.lt_of_succ_lt_succ hoj
        exact ih _ i' j' hi' hj' hoi' hoj' (Nat.lt_of_succ_lt_succ hij)

theorem orderedNonOverlapping_implies_disjoint (fields : List FieldSpec) (L : StructLayout)
    (hord : OrderedNonOverlapping fields L) : FieldsDisjoint fields L := by
  intro i j hi hj hoi hoj hne
  cases Nat.lt_trichotomy i j with
  | inl hij => exact Or.inl (hord i j hi hj hoi hoj hij)
  | inr hrest =>
    cases hrest with
    | inl heq => exact False.elim (hne heq)
    | inr hji => exact Or.inr (hord j i hj hi hoj hoi hji)

theorem placeFieldsFrom_in_bounds (pack : Option Nat) (cursor : Nat) (fs : List FieldSpec) :
    ∀ (i : Nat) (hf : i < fs.length) (ho : i < (placeFieldsFrom pack cursor fs).1.length),
      (placeFieldsFrom pack cursor fs).1[i] + fs[i].size ≤ (placeFieldsFrom pack cursor fs).2 := by
  induction fs generalizing cursor with
  | nil =>
    intro i hf
    cases hf
  | cons f fs ih =>
    intro i hf ho
    cases i with
    | zero =>
      simp only [placeFieldsFrom, List.getElem_cons_zero]
      exact placeFieldsFrom_cursor_le_end pack _ fs
    | succ k =>
      simp only [placeFieldsFrom, List.getElem_cons_succ]
      have hkf : k < fs.length := Nat.lt_of_succ_lt_succ hf
      have hko : k < (placeFieldsFrom pack
          (alignUp cursor (effFieldAlign pack f.align) + f.size) fs).1.length := by
        simp only [placeFieldsFrom, List.length_cons] at ho
        exact Nat.lt_of_succ_lt_succ ho
      exact ih _ k hkf hko

theorem fieldsMaxEffAlign_ge_acc (pack : Option Nat) (acc : Nat) (fs : List FieldSpec) :
    acc ≤ fieldsMaxEffAlign pack acc fs := by
  induction fs generalizing acc with
  | nil => exact Nat.le_refl acc
  | cons f fs ih =>
    simp only [fieldsMaxEffAlign]
    exact Nat.le_trans (Nat.le_max_left acc _) (ih _)

theorem fieldsMaxEffAlign_pos (pack : Option Nat) (acc : Nat) (fs : List FieldSpec)
    (hacc : 0 < acc) : 0 < fieldsMaxEffAlign pack acc fs :=
  Nat.lt_of_lt_of_le hacc (fieldsMaxEffAlign_ge_acc pack acc fs)

theorem fieldsMaxEffAlign_ge_elem (pack : Option Nat) (acc : Nat) (fs : List FieldSpec) :
    ∀ f, f ∈ fs → effFieldAlign pack f.align ≤ fieldsMaxEffAlign pack acc fs := by
  induction fs generalizing acc with
  | nil =>
    intro f hf
    cases hf
  | cons g gs ih =>
    intro f hf
    simp only [fieldsMaxEffAlign]
    cases List.mem_cons.mp hf with
    | inl heq =>
      subst heq
      exact Nat.le_trans (Nat.le_max_right acc _) (fieldsMaxEffAlign_ge_acc pack _ gs)
    | inr hmem =>
      exact ih _ f hmem

/-- **Theorem Family 1 (Soundness of Field Offsets, Non-Overlap, Bounds, and Tail-Padding
Alignment)**: For EVERY representation `repr` with positive modifier bounds and EVERY list
`fields` of positive-alignment fields, `computeOrderedLayout repr fields` guarantees length
matching, effective-alignment divisibility of every offset, ordered non-overlap and pairwise
interval disjointness, full in-bounds containment, and minimal alignment-divisible size. -/
theorem computeOrderedLayout_soundness (repr : ReprOptions) (fields : List FieldSpec)
    (hr : ReprModifierValid repr) (ha : AllAlignPos fields) :
    let L := computeOrderedLayout repr fields
    OffsetsLengthMatch fields L ∧
    OffsetsEffAligned repr.pack fields L ∧
    OrderedNonOverlapping fields L ∧
    FieldsDisjoint fields L ∧
    FieldsInBounds fields L ∧
    SizeAlignedMinimal L := by
  dsimp only
  have hlen : (computeOrderedLayout repr fields).offsets.length = fields.length :=
    placeFieldsFrom_length repr.pack 0 fields
  have halign_offs : OffsetsEffAligned repr.pack fields (computeOrderedLayout repr fields) :=
    placeFieldsFrom_aligned repr.pack 0 fields hr.1 ha
  have hord : OrderedNonOverlapping fields (computeOrderedLayout repr fields) :=
    placeFieldsFrom_ordered_non_overlapping repr.pack 0 fields
  have hdisj : FieldsDisjoint fields (computeOrderedLayout repr fields) :=
    orderedNonOverlapping_implies_disjoint fields _ hord
  have hpos_pre : 0 < fieldsMaxEffAlign repr.pack 1 fields :=
    fieldsMaxEffAlign_pos repr.pack 1 fields (by decide)
  have hpos_final : 0 < (computeOrderedLayout repr fields).align := by
    simp only [computeOrderedLayout]
    cases h : repr.align with
    | none => exact hpos_pre
    | some ra =>
      exact Nat.lt_of_lt_of_le hpos_pre (Nat.le_max_left _ _)
  have hbounds : FieldsInBounds fields (computeOrderedLayout repr fields) := by
    refine ⟨placeFieldsFrom_in_bounds repr.pack 0 fields, ?_⟩
    simp only [computeOrderedLayout]
    exact le_alignUp _ _
  have hmin : SizeAlignedMinimal (computeOrderedLayout repr fields) := by
    refine ⟨hpos_final, ?_, ?_⟩
    · simp only [computeOrderedLayout]
      exact dvd_alignUp _ _ hpos_final
    · simp only [computeOrderedLayout]
      exact alignUp_isLeastAlignedGe _ _ hpos_final
  exact ⟨hlen, halign_offs, hord, hdisj, hbounds, hmin⟩

/-- Whenever every field is a ZST (`size = 0`), field placement leaves `cursor` unchanged
at `0` and total struct `size = 0` regardless of alignment propagation (`Align16Zst`). -/
theorem placeFieldsFrom_all_zst (pack : Option Nat) (cursor : Nat) (fs : List FieldSpec)
    (hz : ∀ f, f ∈ fs → f.size = 0)
    (hcur : ∀ f, f ∈ fs → effFieldAlign pack f.align ∣ cursor) :
    (placeFieldsFrom pack cursor fs).2 = cursor := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [placeFieldsFrom]
    have hf0 : f.size = 0 := hz f List.mem_cons_self
    have hfdvd : effFieldAlign pack f.align ∣ cursor := hcur f List.mem_cons_self
    rw [alignUp_eq_self_of_dvd hfdvd, hf0, Nat.add_zero]
    exact ih (fun g hg => hz g (List.mem_cons_of_mem f hg))
             (fun g hg => hcur g (List.mem_cons_of_mem f hg))

theorem computeOrderedLayout_all_zst_zero_size (repr : ReprOptions) (fields : List FieldSpec)
    (hz : ∀ f, f ∈ fields → f.size = 0) :
    (computeOrderedLayout repr fields).endOffset = 0 ∧
    (computeOrderedLayout repr fields).size = 0 := by
  have hend : (placeFieldsFrom repr.pack 0 fields).2 = 0 :=
    placeFieldsFrom_all_zst repr.pack 0 fields hz (fun f _ => Nat.dvd_zero _)
  constructor
  · exact hend
  · simp only [computeOrderedLayout, hend]
    exact alignUp_zero_left _

/-! ## Section 6: Theorem Family 2 — Permutation Invariance & `repr(C)` Prefix Monotonicity -/

theorem fieldsMaxEffAlign_max_comm (pack : Option Nat) (a b : Nat) (fs : List FieldSpec) :
    fieldsMaxEffAlign pack (max a b) fs = max a (fieldsMaxEffAlign pack b fs) := by
  induction fs generalizing a b with
  | nil => rfl
  | cons f fs ih =>
    simp only [fieldsMaxEffAlign, max_assoc_nat]
    exact ih a (max b (effFieldAlign pack f.align))

/-- Aggregate effective alignment is invariant under arbitrary field permutations (`List.Perm`). -/
theorem fieldsMaxEffAlign_perm (pack : Option Nat) (acc : Nat)
    {fs1 fs2 : List FieldSpec} (hperm : List.Perm fs1 fs2) :
    fieldsMaxEffAlign pack acc fs1 = fieldsMaxEffAlign pack acc fs2 := by
  induction hperm generalizing acc with
  | nil => rfl
  | cons x _ ih =>
    simp only [fieldsMaxEffAlign]
    exact ih _
  | swap x y l =>
    simp only [fieldsMaxEffAlign, Nat.max_assoc]
    rw [Nat.max_comm (effFieldAlign pack x.align) (effFieldAlign pack y.align)]
  | trans _ _ ih1 ih2 =>
    exact Eq.trans (ih1 acc) (ih2 acc)

/-- `max_repr_align` propagation is invariant under arbitrary field permutations. -/
theorem fieldsMaxReprAlign_perm (acc : Option Nat)
    {fs1 fs2 : List FieldSpec} (hperm : List.Perm fs1 fs2) :
    fieldsMaxReprAlign acc fs1 = fieldsMaxReprAlign acc fs2 := by
  induction hperm generalizing acc with
  | nil => rfl
  | cons x _ ih =>
    simp only [fieldsMaxReprAlign]
    exact ih _
  | swap x y l =>
    simp only [fieldsMaxReprAlign, optMax_assoc]
    rw [optMax_comm x.maxReprAlign y.maxReprAlign]
  | trans _ _ ih1 ih2 =>
    exact Eq.trans (ih1 acc) (ih2 acc)

theorem anyFieldReprC_perm {fs1 fs2 : List FieldSpec} (hperm : List.Perm fs1 fs2) :
    anyFieldReprC fs1 = anyFieldReprC fs2 := by
  induction hperm with
  | nil => rfl
  | cons x _ ih => simp only [anyFieldReprC, ih]
  | swap x y l =>
    simp only [anyFieldReprC]
    rw [Bool.or_left_comm x.isReprC]
  | trans _ _ ih1 ih2 => exact Eq.trans ih1 ih2

/-- `sortFieldsByAlignGroup` produces a permutation of its input field list. -/
theorem insertDescByGroup_perm (pack : Option Nat) (f : FieldSpec) (fs : List FieldSpec) :
    List.Perm (insertDescByGroup pack f fs) (f :: fs) := by
  induction fs with
  | nil => exact List.Perm.refl _
  | cons g gs ih =>
    simp only [insertDescByGroup]
    by_cases h : alignmentGroupKey pack g ≤ alignmentGroupKey pack f
    · simp only [h, ↓reduceIte]
      exact List.Perm.refl _
    · simp only [h, ↓reduceIte]
      exact List.Perm.trans (List.Perm.cons g ih) (List.Perm.swap f g gs)

theorem sortFieldsByAlignGroup_perm (pack : Option Nat) (fs : List FieldSpec) :
    List.Perm (sortFieldsByAlignGroup pack fs) fs := by
  induction fs with
  | nil => exact List.Perm.nil
  | cons f fs ih =>
    simp only [sortFieldsByAlignGroup]
    exact List.Perm.trans (insertDescByGroup_perm pack f _) (List.Perm.cons f ih)

/-- **Theorem Family 2a (Permutation Invariance of Aggregate Alignment & Pure-ZST Zero Size)**:
Permuting struct fields arbitrarily (including `-Zrandomize-layout` or `univariant_biased` sorting)
leaves aggregate `align`, `maxReprAlign`, and `isReprC` invariant—and when all fields are ZSTs,
leaves `size = 0` invariant as well. -/
theorem perm_invariance_align_and_zst_size (repr : ReprOptions)
    {fs1 fs2 : List FieldSpec} (hperm : List.Perm fs1 fs2) :
    (computeOrderedLayout repr fs1).align = (computeOrderedLayout repr fs2).align ∧
    (computeOrderedLayout repr fs1).maxReprAlign = (computeOrderedLayout repr fs2).maxReprAlign ∧
    (computeOrderedLayout repr fs1).isReprC = (computeOrderedLayout repr fs2).isReprC ∧
    ((∀ f, f ∈ fs1 → f.size = 0) →
      (computeOrderedLayout repr fs1).size = 0 ∧
      (computeOrderedLayout repr fs2).size = 0) := by
  have hpre : fieldsMaxEffAlign repr.pack 1 fs1 = fieldsMaxEffAlign repr.pack 1 fs2 :=
    fieldsMaxEffAlign_perm repr.pack 1 hperm
  have hmra : fieldsMaxReprAlign repr.align fs1 = fieldsMaxReprAlign repr.align fs2 :=
    fieldsMaxReprAlign_perm repr.align hperm
  have hrc : anyFieldReprC fs1 = anyFieldReprC fs2 := anyFieldReprC_perm hperm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [computeOrderedLayout, hpre]
  · simp only [computeOrderedLayout, hmra]
  · simp only [computeOrderedLayout, hrc]
  · intro hz1
    have hz2 : ∀ f, f ∈ fs2 → f.size = 0 := fun g hg => hz1 g (hperm.mem_iff.mpr hg)
    exact ⟨(computeOrderedLayout_all_zst_zero_size repr fs1 hz1).2,
           (computeOrderedLayout_all_zst_zero_size repr fs2 hz2).2⟩

/-- `computeReprRustLayout` preserves aggregate alignment relative to declaration order `fields`. -/
theorem reprRust_align_eq_declaration_order (repr : ReprOptions) (fields : List FieldSpec) :
    (computeReprRustLayout repr fields).align = (computeOrderedLayout repr fields).align := by
  unfold computeReprRustLayout
  cases h : repr.inhibitStructFieldReordering
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (perm_invariance_align_and_zst_size repr (sortFieldsByAlignGroup_perm repr.pack fields)).1
  · simp only [↓reduceIte]

/-- Appending a field `g` under `#[repr(C)]` preserves `placeFieldsFrom` over the prefix. -/
theorem placeFieldsFrom_append (pack : Option Nat) (cursor : Nat)
    (fs gs : List FieldSpec) :
    placeFieldsFrom pack cursor (fs ++ gs) =
      let p1 := placeFieldsFrom pack cursor fs
      let p2 := placeFieldsFrom pack p1.2 gs
      (p1.1 ++ p2.1, p2.2) := by
  induction fs generalizing cursor with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.cons_append, placeFieldsFrom]
    rw [ih _]

/-- **Theorem Family 2b (`#[repr(C)]` Prefix Offset Invariance & Size/Align Monotonicity)**:
Appending an extra field `g` (or suffix `gs`) to a `#[repr(C)]` struct preserves every prefix
field offset verbatim, and monotonically increases `endOffset`, `align`, and `size` (for
power-of-two alignments). -/
theorem reprC_prefix_offsets_invariant (pack : Option Nat) (cursor : Nat)
    (fs gs : List FieldSpec) (i : Nat) (hi : i < fs.length) :
    let h1 : i < (placeFieldsFrom pack cursor (fs ++ gs)).1.length := by
      rw [placeFieldsFrom_length, List.length_append]
      exact Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)
    let h2 : i < (placeFieldsFrom pack cursor fs).1.length := by
      rw [placeFieldsFrom_length]
      exact hi
    (placeFieldsFrom pack cursor (fs ++ gs)).1[i]'h1 =
      (placeFieldsFrom pack cursor fs).1[i]'h2 := by
  have happ := placeFieldsFrom_append pack cursor fs gs
  have hlen : (placeFieldsFrom pack cursor fs).1.length = fs.length :=
    placeFieldsFrom_length pack cursor fs
  intro h1 h2
  have heq_list : (placeFieldsFrom pack cursor (fs ++ gs)).1 =
      (placeFieldsFrom pack cursor fs).1 ++
        (placeFieldsFrom pack (placeFieldsFrom pack cursor fs).2 gs).1 := by
    rw [happ]
  have h2' : i < (placeFieldsFrom pack cursor fs).1.length := h2
  simp only [heq_list]
  exact List.getElem_append_left h2'

theorem fieldsMaxEffAlign_append (pack : Option Nat) (acc : Nat) (fs gs : List FieldSpec) :
    fieldsMaxEffAlign pack acc (fs ++ gs) =
      fieldsMaxEffAlign pack (fieldsMaxEffAlign pack acc fs) gs := by
  induction fs generalizing acc with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.cons_append, fieldsMaxEffAlign]
    exact ih _

theorem fieldsMaxEffAlign_pow2 (pack : Option Nat) (acc : Nat) (fs : List FieldSpec)
    (hacc : IsPowerOfTwo acc) (hp : ∀ p, pack = some p → IsPowerOfTwo p)
    (ha : AllPow2Align fs) :
    IsPowerOfTwo (fieldsMaxEffAlign pack acc fs) := by
  induction fs generalizing acc with
  | nil => exact hacc
  | cons f fs ih =>
    simp only [fieldsMaxEffAlign]
    have hf : IsPowerOfTwo f.align := ha f List.mem_cons_self
    have heff : IsPowerOfTwo (effFieldAlign pack f.align) := effFieldAlign_pow2 hp hf
    exact ih _ (pow2_max hacc heff) (fun g hg => ha g (List.mem_cons_of_mem f hg))

theorem reprC_prefix_monotone (repr : ReprOptions) (fs gs : List FieldSpec)
    (hr : ReprModifierPow2 repr) (ha1 : AllPow2Align fs) (ha2 : AllPow2Align gs) :
    let L1 := computeOrderedLayout repr fs
    let L2 := computeOrderedLayout repr (fs ++ gs)
    L1.endOffset ≤ L2.endOffset ∧ L1.align ≤ L2.align ∧ L1.size ≤ L2.size := by
  dsimp only
  have hend : (placeFieldsFrom repr.pack 0 fs).2 ≤ (placeFieldsFrom repr.pack 0 (fs ++ gs)).2 := by
    rw [placeFieldsFrom_append]
    exact placeFieldsFrom_cursor_le_end repr.pack _ gs
  have halign : (computeOrderedLayout repr fs).align ≤
      (computeOrderedLayout repr (fs ++ gs)).align := by
    simp only [computeOrderedLayout, fieldsMaxEffAlign_append]
    have hpre : fieldsMaxEffAlign repr.pack 1 fs ≤
        fieldsMaxEffAlign repr.pack (fieldsMaxEffAlign repr.pack 1 fs) gs :=
      fieldsMaxEffAlign_ge_acc repr.pack _ gs
    cases repr.align with
    | none => exact hpre
    | some ra => exact nat_max_le_max hpre (Nat.le_refl ra)
  have hp1 : IsPowerOfTwo (computeOrderedLayout repr fs).align := by
    simp only [computeOrderedLayout]
    have hpre : IsPowerOfTwo (fieldsMaxEffAlign repr.pack 1 fs) :=
      fieldsMaxEffAlign_pow2 repr.pack 1 fs pow2_one hr.1 ha1
    cases h : repr.align with
    | none => exact hpre
    | some ra => exact pow2_max hpre (hr.2 ra h)
  have hp2 : IsPowerOfTwo (computeOrderedLayout repr (fs ++ gs)).align := by
    simp only [computeOrderedLayout]
    have ha12 : AllPow2Align (fs ++ gs) := fun x hx =>
      match List.mem_append.mp hx with
      | Or.inl h => ha1 x h
      | Or.inr h => ha2 x h
    have hpre : IsPowerOfTwo (fieldsMaxEffAlign repr.pack 1 (fs ++ gs)) :=
      fieldsMaxEffAlign_pow2 repr.pack 1 (fs ++ gs) pow2_one hr.1 ha12
    cases h : repr.align with
    | none => exact hpre
    | some ra => exact pow2_max hpre (hr.2 ra h)
  have hdvd : (computeOrderedLayout repr fs).align ∣
      (computeOrderedLayout repr (fs ++ gs)).align :=
    pow2_dvd_of_le hp1 hp2 halign
  have hpos2 : 0 < (computeOrderedLayout repr (fs ++ gs)).align := pow2_pos hp2
  have hsize : (computeOrderedLayout repr fs).size ≤
      (computeOrderedLayout repr (fs ++ gs)).size := by
    simp only [computeOrderedLayout]
    exact Nat.le_trans
      (alignUp_mono (pow2_pos hp1) hend)
      (alignUp_le_alignUp_of_dvd hpos2 hdvd)
  exact ⟨hend, halign, hsize⟩

/-- Correspondence between `google/zerocopy` `DstLayout::for_repr_c_struct` (`zcForReprCStruct`)
and `rustc_abi` sequential placement `placeFieldsFrom` + `fieldsMaxEffAlign`. -/
theorem zcExtendList_eq_placeFieldsFrom (pack : Option Nat) (acc : ZcDstLayout)
    (fs : List FieldSpec) :
    let res := zcExtendList acc pack (fieldsToZcDst fs)
    res.size = (placeFieldsFrom pack acc.size fs).2 ∧
    res.align = fieldsMaxEffAlign pack acc.align fs := by
  induction fs generalizing acc with
  | nil => exact ⟨rfl, rfl⟩
  | cons f fs ih =>
    simp only [fieldsToZcDst, zcExtendList, zcExtend, fieldToZcDst, placeFieldsFrom,
      fieldsMaxEffAlign]
    have hsub := ih { align := max acc.align (effFieldAlign pack f.align),
                      size := acc.size + paddingNeeded acc.size (effFieldAlign pack f.align) + f.size }
    simpa [alignUp] using hsub

theorem zcForReprCStruct_eq_computeReprC (reprAlign reprPacked : Option Nat)
    (fs : List FieldSpec) (hra : ∀ a, reprAlign = some a → 1 ≤ a) :
    let repr : ReprOptions :=
      { kind := .c, pack := reprPacked, align := reprAlign, randomizeLayout := false }
    let zc := zcForReprCStruct reprAlign reprPacked (fieldsToZcDst fs)
    let rc := computeOrderedLayout repr fs
    zc.size = rc.size ∧ zc.align = rc.align := by
  dsimp only
  cases h : reprAlign with
  | none =>
    simp only [zcForReprCStruct, zcNewZst, zcPadToAlign, computeOrderedLayout]
    have heq := zcExtendList_eq_placeFieldsFrom reprPacked { align := 1, size := 0 } fs
    simp only at heq
    rw [heq.1, heq.2]
    exact ⟨rfl, rfl⟩
  | some a =>
    simp only [zcForReprCStruct, zcNewZst, zcPadToAlign, computeOrderedLayout]
    have heq := zcExtendList_eq_placeFieldsFrom reprPacked { align := a, size := 0 } fs
    simp only at heq
    have h1le : 1 ≤ a := hra a h
    have hmax : fieldsMaxEffAlign reprPacked a fs =
        max (fieldsMaxEffAlign reprPacked 1 fs) a := by
      have hcomm := fieldsMaxEffAlign_max_comm reprPacked a 1 fs
      have ha1 : max a 1 = a := Nat.max_eq_left h1le
      rw [ha1] at hcomm
      rw [hcomm, Nat.max_comm]
    rw [heq.1, heq.2, hmax]
    exact ⟨rfl, rfl⟩

/-! ## Section 7: Theorem Family 3 — `#[repr(packed(N))]` Compression & `Unalign<T>` Preservation -/

theorem effFieldAlign_packed1 (a : Nat) (ha : 0 < a) : effFieldAlign (some 1) a = 1 := by
  simp only [effFieldAlign]
  exact Nat.min_eq_right ha

theorem fieldsMaxEffAlign_packed1 (acc : Nat) (fs : List FieldSpec)
    (hacc : acc = 1) (ha : AllAlignPos fs) :
    fieldsMaxEffAlign (some 1) acc fs = 1 := by
  subst hacc
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [fieldsMaxEffAlign]
    have hfa : effFieldAlign (some 1) f.align = 1 :=
      effFieldAlign_packed1 f.align (ha f List.mem_cons_self)
    rw [hfa, Nat.max_self]
    exact ih (fun g hg => ha g (List.mem_cons_of_mem f hg))

theorem placeFieldsFrom_packed1_exact (cursor : Nat) (fs : List FieldSpec) (ha : AllAlignPos fs) :
    (placeFieldsFrom (some 1) cursor fs).2 = cursor + totalFieldSize fs ∧
    (∀ (i : Nat) (_hi : i < fs.length) (ho : i < (placeFieldsFrom (some 1) cursor fs).1.length),
      (placeFieldsFrom (some 1) cursor fs).1[i] = cursor + totalFieldSize (fs.take i)) := by
  induction fs generalizing cursor with
  | nil =>
    refine ⟨by simp [placeFieldsFrom, totalFieldSize], fun i hi => False.elim (Nat.not_lt_zero i hi)⟩
  | cons f fs ih =>
    have hf1 : effFieldAlign (some 1) f.align = 1 :=
      effFieldAlign_packed1 f.align (ha f List.mem_cons_self)
    have ha_tail : AllAlignPos fs := fun g hg => ha g (List.mem_cons_of_mem f hg)
    have ih_sub := ih (cursor + f.size) ha_tail
    constructor
    · simp only [placeFieldsFrom, totalFieldSize, hf1, alignUp_one]
      rw [ih_sub.1, Nat.add_assoc]
    · intro i hi ho
      cases i with
      | zero =>
        simp only [placeFieldsFrom, hf1, alignUp_one, List.getElem_cons_zero,
          List.take_zero, totalFieldSize, Nat.add_zero]
      | succ k =>
        simp only [placeFieldsFrom, hf1, alignUp_one, List.getElem_cons_succ,
          List.take_succ_cons, totalFieldSize]
        have hkf : k < fs.length := Nat.lt_of_succ_lt_succ hi
        have hko : k < (placeFieldsFrom (some 1) (cursor + f.size) fs).1.length := by
          simp only [placeFieldsFrom, hf1, alignUp_one, List.length_cons] at ho
          exact Nat.lt_of_succ_lt_succ ho
        rw [ih_sub.2 k hkf hko, Nat.add_assoc]

/-- **Theorem Family 3a (`#[repr(packed(1))]` Zero-Padding & Align-1 Exact Sum Theorem)**:
Under `#[repr(packed(1))]` (without `align(N)`), aggregate alignment is `1`, `unadjustedAbiAlign`
is `1`, total size equals `totalFieldSize fields` (zero inter-field and zero tail padding), and
every field offset `i` equals `totalFieldSize (fields.take i)`. -/
theorem packed1_zero_padding_exact_sum (kind : ReprKind) (rand : Bool)
    (fields : List FieldSpec) (ha : AllAlignPos fields)
    (hnottrans : kind ≠ .transparent) :
    let repr : ReprOptions :=
      { kind := kind, pack := some 1, align := none, randomizeLayout := rand }
    let L := computeOrderedLayout repr fields
    L.align = 1 ∧
    L.unadjustedAbiAlign = 1 ∧
    L.endOffset = totalFieldSize fields ∧
    L.size = totalFieldSize fields ∧
    (∀ (i : Nat) (_hf : i < fields.length) (ho : i < L.offsets.length),
      L.offsets[i] = totalFieldSize (fields.take i)) := by
  dsimp only
  have hall1 : fieldsMaxEffAlign (some 1) 1 fields = 1 :=
    fieldsMaxEffAlign_packed1 1 fields rfl ha
  have hplace := placeFieldsFrom_packed1_exact 0 fields ha
  have hnt : ReprKind.beq kind .transparent = false := by
    cases kind with
    | rust => rfl
    | c => rfl
    | transparent => exact False.elim (hnottrans rfl)
  refine ⟨hall1, ?_, ?_, ?_, ?_⟩
  · simp only [computeOrderedLayout, computeUnadjustedAbiAlign, hnt, Bool.false_eq_true,
      ↓reduceIte, hall1]
  · simp only [computeOrderedLayout, hplace.1, Nat.zero_add]
  · simp only [computeOrderedLayout, hall1, alignUp_one, hplace.1, Nat.zero_add]
  · intro i hf ho
    have ho' : i < (placeFieldsFrom (some 1) 0 fields).1.length := ho
    have hpi := hplace.2 i hf ho'
    rw [Nat.zero_add] at hpi
    exact hpi

theorem placeFieldsFrom_mono_of_pow2 (pack1 pack2 : Option Nat) (c1 c2 : Nat)
    (fs : List FieldSpec)
    (hc : c1 ≤ c2)
    (hdiv : ∀ f, f ∈ fs → effFieldAlign pack1 f.align ∣ effFieldAlign pack2 f.align)
    (hp2 : PackPos pack2) (ha : AllAlignPos fs) :
    (placeFieldsFrom pack1 c1 fs).2 ≤ (placeFieldsFrom pack2 c2 fs).2 ∧
    (∀ (i : Nat) (h1 : i < (placeFieldsFrom pack1 c1 fs).1.length)
      (h2 : i < (placeFieldsFrom pack2 c2 fs).1.length),
      (placeFieldsFrom pack1 c1 fs).1[i] ≤ (placeFieldsFrom pack2 c2 fs).1[i]) := by
  induction fs generalizing c1 c2 with
  | nil => refine ⟨hc, fun i _ => False.elim (Nat.not_lt_zero i (by simpa [placeFieldsFrom] using ‹i < 0›))⟩
  | cons f fs ih =>
    have hf2_pos : 0 < effFieldAlign pack2 f.align :=
      effFieldAlign_pos hp2 (ha f List.mem_cons_self)
    have hfdvd : effFieldAlign pack1 f.align ∣ effFieldAlign pack2 f.align :=
      hdiv f List.mem_cons_self
    have hoff_le : alignUp c1 (effFieldAlign pack1 f.align) ≤
        alignUp c2 (effFieldAlign pack2 f.align) := by
      have h1 : alignUp c1 (effFieldAlign pack1 f.align) ≤
          alignUp c2 (effFieldAlign pack1 f.align) := by
        have hf1_pos : 0 < effFieldAlign pack1 f.align := by
          rcases hfdvd with ⟨k, hk⟩
          cases hfz : effFieldAlign pack1 f.align with
          | zero =>
            rw [hfz, Nat.zero_mul] at hk
            rw [hk] at hf2_pos
            exact False.elim (Nat.lt_irrefl 0 hf2_pos)
          | succ n => exact Nat.succ_pos n
        exact alignUp_mono hf1_pos hc
      have h2 : alignUp c2 (effFieldAlign pack1 f.align) ≤
          alignUp c2 (effFieldAlign pack2 f.align) :=
        alignUp_le_alignUp_of_dvd hf2_pos hfdvd
      exact Nat.le_trans h1 h2
    have hnext_c : alignUp c1 (effFieldAlign pack1 f.align) + f.size ≤
        alignUp c2 (effFieldAlign pack2 f.align) + f.size :=
      Nat.add_le_add_right hoff_le f.size
    have ih_sub := ih _ _ hnext_c
      (fun g hg => hdiv g (List.mem_cons_of_mem f hg))
      (fun g hg => ha g (List.mem_cons_of_mem f hg))
    refine ⟨ih_sub.1, ?_⟩
    intro i h1 h2
    cases i with
    | zero =>
      simp only [placeFieldsFrom, List.getElem_cons_zero]
      exact hoff_le
    | succ k =>
      simp only [placeFieldsFrom, List.getElem_cons_succ]
      have hk1 : k < (placeFieldsFrom pack1
          (alignUp c1 (effFieldAlign pack1 f.align) + f.size) fs).1.length := by
        simp only [placeFieldsFrom, List.length_cons] at h1
        exact Nat.lt_of_succ_lt_succ h1
      have hk2 : k < (placeFieldsFrom pack2
          (alignUp c2 (effFieldAlign pack2 f.align) + f.size) fs).1.length := by
        simp only [placeFieldsFrom, List.length_cons] at h2
        exact Nat.lt_of_succ_lt_succ h2
      exact ih_sub.2 k hk1 hk2

theorem fieldsMaxEffAlign_mono_of_le (pack1 pack2 : Option Nat) (a1 a2 : Nat)
    (fs : List FieldSpec) (ha : a1 ≤ a2)
    (hle : ∀ f, f ∈ fs → effFieldAlign pack1 f.align ≤ effFieldAlign pack2 f.align) :
    fieldsMaxEffAlign pack1 a1 fs ≤ fieldsMaxEffAlign pack2 a2 fs := by
  induction fs generalizing a1 a2 with
  | nil => exact ha
  | cons f fs ih =>
    simp only [fieldsMaxEffAlign]
    have hmax : max a1 (effFieldAlign pack1 f.align) ≤
        max a2 (effFieldAlign pack2 f.align) :=
      nat_max_le_max ha (hle f List.mem_cons_self)
    exact ih _ _ hmax (fun g hg => hle g (List.mem_cons_of_mem f hg))

/-- **Theorem Family 3b (`#[repr(packed(N))]` Monotone Size and Alignment Compression)**:
For any fixed field sequence with power-of-two alignments and power-of-two packing bounds
`p1 ≤ p2` (no `repr(align)` override), tightening packing strictly reduces or preserves
aggregate alignment, every field offset, `endOffset`, and total `size` relative to both
`packed(p2)` and unpacked `.none`. -/
theorem packed_monotone_compression (kind : ReprKind) (rand : Bool)
    (fields : List FieldSpec) (p1 p2 : Nat)
    (ha : AllPow2Align fields) (hp1 : IsPowerOfTwo p1) (hp2 : IsPowerOfTwo p2)
    (hle : p1 ≤ p2) :
    let r1 : ReprOptions := { kind := kind, pack := some p1, align := none, randomizeLayout := rand }
    let r2 : ReprOptions := { kind := kind, pack := some p2, align := none, randomizeLayout := rand }
    let rNone : ReprOptions := { kind := kind, pack := none, align := none, randomizeLayout := rand }
    let L1 := computeOrderedLayout r1 fields
    let L2 := computeOrderedLayout r2 fields
    let LNone := computeOrderedLayout rNone fields
    L1.align ≤ L2.align ∧ L2.align ≤ LNone.align ∧
    L1.endOffset ≤ L2.endOffset ∧ L2.endOffset ≤ LNone.endOffset ∧
    L1.size ≤ L2.size ∧ L2.size ≤ LNone.size := by
  dsimp only
  have ha_pos : AllAlignPos fields := fun f hf => pow2_pos (ha f hf)
  have h12_dvd : ∀ f, f ∈ fields →
      effFieldAlign (some p1) f.align ∣ effFieldAlign (some p2) f.align :=
    fun f hf => pow2_min_dvd_of_le (ha f hf) hp1 hp2 hle
  have h2n_dvd : ∀ f, f ∈ fields →
      effFieldAlign (some p2) f.align ∣ effFieldAlign none f.align :=
    fun f hf => min_dvd_left_pow2 (ha f hf) hp2
  have h12_le : ∀ f, f ∈ fields →
      effFieldAlign (some p1) f.align ≤ effFieldAlign (some p2) f.align :=
    fun f _ => nat_min_le_min (Nat.le_refl _) hle
  have h2n_le : ∀ f, f ∈ fields →
      effFieldAlign (some p2) f.align ≤ effFieldAlign none f.align :=
    fun f _ => Nat.min_le_left _ _
  have hplace12 := placeFieldsFrom_mono_of_pow2 (some p1) (some p2) 0 0 fields (Nat.le_refl 0)
    h12_dvd (fun _ h => by cases h; exact pow2_pos hp2) ha_pos
  have hplace2n := placeFieldsFrom_mono_of_pow2 (some p2) none 0 0 fields (Nat.le_refl 0)
    h2n_dvd (fun _ h => by cases h) ha_pos
  have ha12 : fieldsMaxEffAlign (some p1) 1 fields ≤ fieldsMaxEffAlign (some p2) 1 fields :=
    fieldsMaxEffAlign_mono_of_le (some p1) (some p2) 1 1 fields (Nat.le_refl 1) h12_le
  have ha2n : fieldsMaxEffAlign (some p2) 1 fields ≤ fieldsMaxEffAlign none 1 fields :=
    fieldsMaxEffAlign_mono_of_le (some p2) none 1 1 fields (Nat.le_refl 1) h2n_le
  have hpow_a1 : IsPowerOfTwo (fieldsMaxEffAlign (some p1) 1 fields) :=
    fieldsMaxEffAlign_pow2 (some p1) 1 fields pow2_one (fun _ h => by cases h; exact hp1) ha
  have hpow_a2 : IsPowerOfTwo (fieldsMaxEffAlign (some p2) 1 fields) :=
    fieldsMaxEffAlign_pow2 (some p2) 1 fields pow2_one (fun _ h => by cases h; exact hp2) ha
  have hpow_an : IsPowerOfTwo (fieldsMaxEffAlign none 1 fields) :=
    fieldsMaxEffAlign_pow2 none 1 fields pow2_one (fun _ h => by cases h) ha
  have hdvd_a12 := pow2_dvd_of_le hpow_a1 hpow_a2 ha12
  have hdvd_a2n := pow2_dvd_of_le hpow_a2 hpow_an ha2n
  have hsize12 : alignUp (placeFieldsFrom (some p1) 0 fields).2
      (fieldsMaxEffAlign (some p1) 1 fields) ≤
      alignUp (placeFieldsFrom (some p2) 0 fields).2
      (fieldsMaxEffAlign (some p2) 1 fields) :=
    Nat.le_trans
      (alignUp_mono (pow2_pos hpow_a1) hplace12.1)
      (alignUp_le_alignUp_of_dvd (pow2_pos hpow_a2) hdvd_a12)
  have hsize2n : alignUp (placeFieldsFrom (some p2) 0 fields).2
      (fieldsMaxEffAlign (some p2) 1 fields) ≤
      alignUp (placeFieldsFrom none 0 fields).2
      (fieldsMaxEffAlign none 1 fields) :=
    Nat.le_trans
      (alignUp_mono (pow2_pos hpow_a2) hplace2n.1)
      (alignUp_le_alignUp_of_dvd (pow2_pos hpow_an) hdvd_a2n)
  exact ⟨ha12, ha2n, hplace12.1, hplace2n.1, hsize12, hsize2n⟩

/-- Whenever `p` is at least every field's alignment, `#[repr(packed(p))]` is a complete no-op
(`r[layout.repr.alignment.packed]`). -/
theorem packed_ge_all_fields_noop (repr : ReprOptions) (fields : List FieldSpec) (p : Nat)
    (hge : ∀ f, f ∈ fields → f.align ≤ p) :
    computeOrderedLayout { repr with pack := some p } fields =
    computeOrderedLayout { repr with pack := none } fields := by
  have heff : ∀ (c : Nat) (fs : List FieldSpec), (∀ f, f ∈ fs → f.align ≤ p) →
      placeFieldsFrom (some p) c fs = placeFieldsFrom none c fs := by
    intro c fs hfs
    induction fs generalizing c with
    | nil => rfl
    | cons f fs ih =>
      simp only [placeFieldsFrom, effFieldAlign]
      have hfp : min f.align p = f.align := Nat.min_eq_left (hfs f List.mem_cons_self)
      rw [hfp, ih _ (fun g hg => hfs g (List.mem_cons_of_mem f hg))]
  have hmax : ∀ (acc : Nat) (fs : List FieldSpec), (∀ f, f ∈ fs → f.align ≤ p) →
      fieldsMaxEffAlign (some p) acc fs = fieldsMaxEffAlign none acc fs := by
    intro acc fs hfs
    induction fs generalizing acc with
    | nil => rfl
    | cons f fs ih =>
      simp only [fieldsMaxEffAlign, effFieldAlign]
      have hfp : min f.align p = f.align := Nat.min_eq_left (hfs f List.mem_cons_self)
      rw [hfp, ih _ (fun g hg => hfs g (List.mem_cons_of_mem f hg))]
  simp only [computeOrderedLayout, computeUnadjustedAbiAlign, computeBackendRepr,
    ReprOptions.inhibitNewtypeAbiOpt, heff 0 fields hge, hmax 1 fields hge]
  rfl

/-- **Theorem Family 3c (`google/zerocopy::Unalign<T>` Align-1 Preservation & Generic
Indirection Safety)**: Wrapping ANY sized type `t` (including `#[repr(align(N))]` types!) in
`#[repr(C, packed)] struct Unalign<T>(T)` preserves exact size (`layout.size = t.size`), lowers
`align` and `unadjustedAbiAlign` to `1`, places `t` at offset `0`, propagates `t.maxReprAlign`,
and passes `checkPacked` via generic `ty::Param` indirection in both compiler eras. -/
theorem unalign_preserves_size_sets_align1 (era : CheckPackedEra) (t : FieldSpec)
    (ht_pos : 0 < t.align) :
    let unalignRepr : ReprOptions :=
      { kind := .c, pack := some 1, align := none, randomizeLayout := false }
    let L := computeOrderedLayout unalignRepr [t]
    L.size = t.size ∧
    L.align = 1 ∧
    L.unadjustedAbiAlign = 1 ∧
    L.offsets = [0] ∧
    L.maxReprAlign = t.maxReprAlign ∧
    L.isReprC = true ∧
    checkPacked era unalignRepr [FieldCheckNode.genericParam t.isReprC t.reprAlign.isSome] = .ok := by
  dsimp only
  have hfa : effFieldAlign (some 1) t.align = 1 := effFieldAlign_packed1 t.align ht_pos
  have hmax : max 1 1 = 1 := Nat.max_self 1
  have hopt : optMax none t.maxReprAlign = t.maxReprAlign := by
    cases t.maxReprAlign <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [computeOrderedLayout, placeFieldsFrom, hfa, alignUp_one,
      fieldsMaxEffAlign, hmax]
  · simp [computeOrderedLayout, fieldsMaxEffAlign, hfa, hmax]
  · simp [computeOrderedLayout, computeUnadjustedAbiAlign, ReprKind.beq,
      fieldsMaxEffAlign, hfa, hmax]
  · simp [computeOrderedLayout, placeFieldsFrom, hfa, alignUp_zero_left]
  · simp [computeOrderedLayout, fieldsMaxReprAlign, hopt]
  · simp [computeOrderedLayout, ReprKind.beq]
  · cases era <;> simp [checkPacked, checkPackedInnerList, ReprKind.beq]

/-! ## Section 8: Theorem Family 4 — `#[repr(transparent)]` ABI, Size, Align, & Offset Identity -/

/-- Specification: `fields` consists of `fMain` at index `idx` surrounded solely by `1-ZST`
fields (`size = 0 ∧ align = 1`). -/
noncomputable def IsSoleNon1ZstAt (idx : Nat) (fields : List FieldSpec) (fMain : FieldSpec) :
    Prop :=
  ∃ h : idx < fields.length,
    fields[idx] = fMain ∧
    ∀ (j : Nat) (hj : j < fields.length), j ≠ idx → (fields[j]).is1Zst = true

/-- Every field in `fields` is a `1-ZST` (`size = 0 ∧ align = 1`). -/
noncomputable def All1Zst (fields : List FieldSpec) : Prop :=
  ∀ f, f ∈ fields → f.is1Zst = true

theorem is1Zst_fields (f : FieldSpec) (h : f.is1Zst = true) :
    f.size = 0 ∧ f.align = 1 := by
  simp only [FieldSpec.is1Zst, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem placeFieldsFrom_1zst_prefix (cursor : Nat) (zs : List FieldSpec)
    (hz : All1Zst zs) :
    (placeFieldsFrom none cursor zs).1 = List.replicate zs.length cursor ∧
    (placeFieldsFrom none cursor zs).2 = cursor := by
  induction zs with
  | nil => exact ⟨rfl, rfl⟩
  | cons z zs ih =>
    have h1 := is1Zst_fields z (hz z List.mem_cons_self)
    have ih_sub := ih (fun g hg => hz g (List.mem_cons_of_mem z hg))
    simp only [placeFieldsFrom, effFieldAlign, h1.2, alignUp_one, h1.1, Nat.add_zero]
    rw [ih_sub.1, ih_sub.2]
    exact ⟨rfl, rfl⟩

theorem fieldsMaxEffAlign_1zst (acc : Nat) (zs : List FieldSpec)
    (hacc : 1 ≤ acc) (hz : All1Zst zs) :
    fieldsMaxEffAlign none acc zs = acc := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    have h1 := is1Zst_fields z (hz z List.mem_cons_self)
    simp only [fieldsMaxEffAlign, effFieldAlign, h1.2, Nat.max_eq_left hacc]
    exact ih (fun g hg => hz g (List.mem_cons_of_mem z hg))

theorem nonZstFields_1zst (zs : List FieldSpec) (hz : All1Zst zs) :
    nonZstFields zs = [] := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    have h1 := is1Zst_fields z (hz z List.mem_cons_self)
    have hzt : z.isZst = true := by
      simp only [FieldSpec.isZst, h1.1]
      rfl
    simp only [nonZstFields, hzt, ↓reduceIte]
    exact ih (fun g hg => hz g (List.mem_cons_of_mem z hg))

theorem nonZstFields_append (xs ys : List FieldSpec) :
    nonZstFields (xs ++ ys) = nonZstFields xs ++ nonZstFields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, nonZstFields]
    cases hx : x.isZst
    · simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append, ih]
    · simp only [↓reduceIte, ih]

theorem fieldsMaxEffAlign_append_1zst (acc : Nat) (zs : List FieldSpec)
    (hacc : 1 ≤ acc) (hz : All1Zst zs) :
    fieldsMaxEffAlign none acc zs = acc :=
  fieldsMaxEffAlign_1zst acc zs hacc hz

/-- **Theorem Family 4a (`#[repr(transparent)]` All-1-ZST Identity)**:
A `#[repr(transparent)]` struct whose fields are all `1-ZST`s (including zero fields) has
`size = 0`, `align = 1`, and `unadjustedAbiAlign = 1`. -/
theorem transparent_all_1zst_identity (rand : Bool) (fields : List FieldSpec)
    (hz : All1Zst fields) :
    let repr : ReprOptions :=
      { kind := .transparent, pack := none, align := none, randomizeLayout := rand }
    let L := computeOrderedLayout repr fields
    L.size = 0 ∧ L.align = 1 ∧ L.unadjustedAbiAlign = 1 := by
  dsimp only
  have hall : fieldsMaxEffAlign none 1 fields = 1 :=
    fieldsMaxEffAlign_1zst 1 fields (Nat.le_refl 1) hz
  have hplace := placeFieldsFrom_1zst_prefix 0 fields hz
  have hnz : nonZstFields fields = [] := nonZstFields_1zst fields hz
  refine ⟨?_, ?_, ?_⟩
  · simp only [computeOrderedLayout, hplace.2, hall, alignUp_zero_left]
  · simp only [computeOrderedLayout, hall]
  · simp only [computeOrderedLayout, computeUnadjustedAbiAlign, ReprKind.beq, hnz, hall, ↓reduceIte]

theorem anyFieldReprC_append (xs ys : List FieldSpec) :
    anyFieldReprC (xs ++ ys) = (anyFieldReprC xs || anyFieldReprC ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, anyFieldReprC, ih, Bool.or_assoc]

theorem anyFieldReprC_false_of_all (zs : List FieldSpec)
    (h : ∀ z, z ∈ zs → z.isReprC = false) : anyFieldReprC zs = false := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    have hz : z.isReprC = false := h z List.mem_cons_self
    have hrest : anyFieldReprC zs = false := ih (fun g hg => h g (List.mem_cons_of_mem z hg))
    simp only [anyFieldReprC, hz, hrest, Bool.false_or]

/-- **Theorem Family 4b (`#[repr(transparent)]` Sole Non-1-ZST Size, Align, Zero-Offset,
and ABI Forwarding Identity)**: Given ANY decomposition `fields = pre ++ [fMain] ++ post` where
`pre` and `post` contain solely non-`#[repr(C)]` `1-ZST` fields (matching `check_transparent`
at `check.rs:1852-1873`) and `fMain` has `0 < fMain.align`, `0 < fMain.size`, `fMain.align ∣
fMain.size`, and scalar/scalar-pair `BackendRepr`, `computeOrderedLayout` yields:
`size = fMain.size`, `align = fMain.align`, `fMain` at byte offset `0`, `backendRepr =
fMain.backendRepr`, `unadjustedAbiAlign = fMain.unadjustedAbiAlign`, and `isReprC = fMain.isReprC`
regardless of whether `1-ZST` fields are placed before or after `fMain`. -/
theorem transparent_sole_non_1zst_identity (rand : Bool)
    (pre post : List FieldSpec) (fMain : FieldSpec)
    (hpre : All1Zst pre) (hpost : All1Zst post)
    (hpre_nc : ∀ z, z ∈ pre → z.isReprC = false)
    (hpost_nc : ∀ z, z ∈ post → z.isReprC = false)
    (hf_align : 0 < fMain.align) (hf_size_pos : 0 < fMain.size)
    (hf_dvd : fMain.align ∣ fMain.size)
    (hf_abi : (∃ p s, fMain.backendRepr = .scalar p s) ∨
              (∃ p1 p2 s1 s2, fMain.backendRepr = .scalarPair p1 p2 s1 s2)) :
    let repr : ReprOptions :=
      { kind := .transparent, pack := none, align := none, randomizeLayout := rand }
    let fields := pre ++ [fMain] ++ post
    let L := computeOrderedLayout repr fields
    L.size = fMain.size ∧
    L.align = fMain.align ∧
    (∃ hidx : pre.length < L.offsets.length, L.offsets[pre.length]'hidx = 0) ∧
    L.backendRepr = fMain.backendRepr ∧
    L.unadjustedAbiAlign = fMain.unadjustedAbiAlign ∧
    L.isReprC = fMain.isReprC := by
  dsimp only
  have hpre_place := placeFieldsFrom_1zst_prefix 0 pre hpre
  have hpost_place := placeFieldsFrom_1zst_prefix fMain.size post hpost
  have hf_off0 : alignUp 0 fMain.align = 0 := alignUp_zero_left fMain.align
  have h_place_all :
      placeFieldsFrom none 0 (pre ++ [fMain] ++ post) =
        (List.replicate pre.length 0 ++ (0 :: List.replicate post.length fMain.size),
         fMain.size) := by
    rw [List.append_assoc, placeFieldsFrom_append]
    dsimp only
    rw [hpre_place.1, hpre_place.2]
    simp only [List.singleton_append, placeFieldsFrom, effFieldAlign, hf_off0, Nat.zero_add]
    rw [hpost_place.1, hpost_place.2]
  have h_align_pre : fieldsMaxEffAlign none 1 pre = 1 :=
    fieldsMaxEffAlign_1zst 1 pre (Nat.le_refl 1) hpre
  have h_align_after_main : max 1 fMain.align = fMain.align := Nat.max_eq_right hf_align
  have h_align_all :
      fieldsMaxEffAlign none 1 (pre ++ [fMain] ++ post) = fMain.align := by
    rw [List.append_assoc, fieldsMaxEffAlign_append, h_align_pre]
    simp only [List.singleton_append, fieldsMaxEffAlign, effFieldAlign, h_align_after_main]
    exact fieldsMaxEffAlign_1zst fMain.align post hf_align hpost
  have h_size : alignUp fMain.size fMain.align = fMain.size := alignUp_eq_self_of_dvd hf_dvd
  have h_nz_pre : nonZstFields pre = [] := nonZstFields_1zst pre hpre
  have h_nz_post : nonZstFields post = [] := nonZstFields_1zst post hpost
  have hf_not_zst : fMain.isZst = false := by
    simp only [FieldSpec.isZst, beq_eq_false_iff_ne]
    exact Nat.ne_of_gt hf_size_pos
  have h_nz_all : nonZstFields (pre ++ [fMain] ++ post) = [fMain] := by
    rw [List.append_assoc, nonZstFields_append, h_nz_pre, List.nil_append]
    simp only [List.singleton_append, nonZstFields, hf_not_zst, Bool.false_eq_true, ↓reduceIte,
      h_nz_post]
  have h_rc_pre : anyFieldReprC pre = false := anyFieldReprC_false_of_all pre hpre_nc
  have h_rc_post : anyFieldReprC post = false := anyFieldReprC_false_of_all post hpost_nc
  have h_rc_all : anyFieldReprC (pre ++ [fMain] ++ post) = fMain.isReprC := by
    rw [List.append_assoc, anyFieldReprC_append, h_rc_pre, Bool.false_or]
    simp only [List.singleton_append, anyFieldReprC, h_rc_post, Bool.or_false]
  have h_size_ne0 : (fMain.size == 0) = false := by
    simp only [beq_eq_false_iff_ne]
    exact Nat.ne_of_gt hf_size_pos
  have h_backend :
      computeBackendRepr
        { kind := .transparent, pack := none, align := none, randomizeLayout := rand }
        (pre ++ [fMain] ++ post)
        (List.replicate pre.length 0 ++ (0 :: List.replicate post.length fMain.size))
        fMain.size fMain.align = fMain.backendRepr := by
    have hba : (fMain.align == fMain.align) = true := beq_iff_eq.mpr rfl
    have hbs : (fMain.size == fMain.size) = true := beq_iff_eq.mpr rfl
    simp only [computeBackendRepr, h_size_ne0, Bool.false_eq_true, ↓reduceIte, h_nz_all,
      hba, hbs, Bool.and_self]
    cases hf_abi with
    | inl hs =>
      rcases hs with ⟨p, s, hp⟩
      rw [hp]
      simp [ReprOptions.inhibitNewtypeAbiOpt, ReprKind.beq]
    | inr hsp =>
      rcases hsp with ⟨p1, p2, s1, s2, hsp⟩
      rw [hsp]
  have hidx : pre.length <
      (computeOrderedLayout
        { kind := .transparent, pack := none, align := none, randomizeLayout := rand }
        (pre ++ [fMain] ++ post)).offsets.length := by
    simp only [computeOrderedLayout, h_place_all, List.length_append, List.length_replicate,
      List.length_cons]
    exact Nat.lt_add_of_pos_right (Nat.succ_pos post.length)
  refine ⟨?_, ?_, ⟨hidx, ?_⟩, ?_, ?_, ?_⟩
  · simp only [computeOrderedLayout, h_place_all, h_align_all, h_size]
  · simp only [computeOrderedLayout, h_align_all]
  · simp only [computeOrderedLayout, h_place_all]
    have hlen_rep : (List.replicate pre.length 0).length = pre.length := List.length_replicate
    have hidx2 :
        pre.length < (List.replicate pre.length 0 ++ 0 :: List.replicate post.length fMain.size).length := by
      simp only [List.length_append, hlen_rep, List.length_cons, List.length_replicate]
      exact Nat.lt_add_of_pos_right (Nat.succ_pos post.length)
    have hget := List.getElem_append_right
      (as := List.replicate pre.length 0)
      (bs := 0 :: List.replicate post.length fMain.size)
      (i := pre.length)
      (h₂ := hidx2)
      (Nat.le_of_eq hlen_rep)
    simp only [hlen_rep, Nat.sub_self, List.getElem_cons_zero] at hget
    exact hget
  · simp only [computeOrderedLayout, h_place_all, h_align_all, h_size]
    exact h_backend
  · simp only [computeOrderedLayout, computeUnadjustedAbiAlign, ReprKind.beq, ↓reduceIte, h_nz_all]
  · simp only [computeOrderedLayout, ReprKind.beq, Bool.false_or, Bool.true_and, h_rc_all]

/-- **Theorem Family 4c (Single-Field Non-1-ZST `#[repr(transparent)]` Acceptance &
`unadjusted_abi_align` Fallback)**: When `fields = [z]` (`fields.length ≤ 1`), `checkTransparent`
returns `.ok` (`check.rs:1804`) even when `z` is a non-1-aligned ZST (`z.size = 0 ∧ 1 ≤ z.align`,
such as `[u32; 0]` or `#[repr(align(16))] struct Align16Zst`); its `size` is `0`, its `align` is
`z.align`, and because `nonZstFields [z] = []`, `unadjustedAbiAlign` takes the `None => align`
branch (`layout.rs:908-911`), returning `z.align` rather than `z.unadjustedAbiAlign`. -/
theorem transparent_single_non1zst_accepted_and_unadjusted_align
    (rand : Bool) (z : FieldSpec) (hz_size : z.size = 0) (hz_align : 1 ≤ z.align) :
    let repr : ReprOptions :=
      { kind := .transparent, pack := none, align := none, randomizeLayout := rand }
    let L := computeOrderedLayout repr [z]
    checkTransparent repr false [z] = .ok ∧
    L.size = 0 ∧
    L.align = z.align ∧
    L.unadjustedAbiAlign = z.align ∧
    L.offsets = [0] := by
  dsimp only
  have hzz : z.isZst = true := by
    simp only [FieldSpec.isZst, hz_size]
    rfl
  have hnz : nonZstFields [z] = [] := by
    simp only [nonZstFields, hzz, ↓reduceIte]
  have hall : fieldsMaxEffAlign none 1 [z] = z.align := by
    simp only [fieldsMaxEffAlign, effFieldAlign, Nat.max_eq_right hz_align]
  have hchk : checkTransparent
      { kind := .transparent, pack := none, align := none, randomizeLayout := rand }
      false [z] = .ok := by
    simp only [checkTransparent, ReprKind.beq, Bool.false_eq_true, ↓reduceIte,
      List.length_cons, List.length_nil]
    rfl
  refine ⟨hchk, ?_, hall, ?_, ?_⟩
  · simp only [computeOrderedLayout, placeFieldsFrom, effFieldAlign, alignUp_zero_left, hz_size,
      Nat.zero_add]
  · simp only [computeOrderedLayout, computeUnadjustedAbiAlign, ReprKind.beq, ↓reduceIte, hnz, hall]
  · simp only [computeOrderedLayout, placeFieldsFrom, effFieldAlign, alignUp_zero_left]

/-- **Theorem Family 4d (`google/zerocopy::ReadOnly<T>` Transparent Wrapper Identity)**:
Specializes `transparent_sole_non_1zst_identity` to `#[repr(transparent)] pub struct ReadOnly<T>(T)`. -/
theorem readonly_transparent_wrapper_identity (t : FieldSpec)
    (ht_align : 0 < t.align) (ht_size : 0 < t.size) (ht_dvd : t.align ∣ t.size)
    (ht_abi : (∃ p s, t.backendRepr = .scalar p s) ∨
              (∃ p1 p2 s1 s2, t.backendRepr = .scalarPair p1 p2 s1 s2)) :
    let roRepr : ReprOptions :=
      { kind := .transparent, pack := none, align := none, randomizeLayout := false }
    let L := computeOrderedLayout roRepr [t]
    L.size = t.size ∧
    L.align = t.align ∧
    L.offsets = [0] ∧
    L.backendRepr = t.backendRepr ∧
    L.unadjustedAbiAlign = t.unadjustedAbiAlign ∧
    L.isReprC = t.isReprC := by
  have hmain := transparent_sole_non_1zst_identity false [] [] t
    (fun _ hx => False.elim (List.not_mem_nil hx))
    (fun _ hx => False.elim (List.not_mem_nil hx))
    (fun _ hx => False.elim (List.not_mem_nil hx))
    (fun _ hx => False.elim (List.not_mem_nil hx))
    ht_align ht_size ht_dvd ht_abi
  dsimp only at hmain ⊢
  have hlen : (computeOrderedLayout
      { kind := .transparent, pack := none, align := none, randomizeLayout := false } [t]).offsets = [0] := by
    simp [computeOrderedLayout, placeFieldsFrom, alignUp_zero_left]
  exact ⟨hmain.1, hmain.2.1, hlen, hmain.2.2.2.1, hmain.2.2.2.2.1, hmain.2.2.2.2.2⟩

/-! ## Section 9: Empirical Cross-Checks (`rustc 1.98.0` / `1.102.0`) & Constructive Counterexamples -/

noncomputable def tyU8 : FieldSpec :=
  { size := 1, align := 1, unadjustedAbiAlign := 1, reprAlign := none, maxReprAlign := none,
    isReprC := false, hasNiche := false, backendRepr := .scalar .int 1 }

noncomputable def tyU16 : FieldSpec :=
  { size := 2, align := 2, unadjustedAbiAlign := 2, reprAlign := none, maxReprAlign := none,
    isReprC := false, hasNiche := false, backendRepr := .scalar .int 2 }

noncomputable def tyU32 : FieldSpec :=
  { size := 4, align := 4, unadjustedAbiAlign := 4, reprAlign := none, maxReprAlign := none,
    isReprC := false, hasNiche := false, backendRepr := .scalar .int 4 }

noncomputable def tyU64 : FieldSpec :=
  { size := 8, align := 8, unadjustedAbiAlign := 8, reprAlign := none, maxReprAlign := none,
    isReprC := false, hasNiche := false, backendRepr := .scalar .int 8 }

noncomputable def tyUnit : FieldSpec :=
  { size := 0, align := 1, unadjustedAbiAlign := 1, reprAlign := none, maxReprAlign := none,
    isReprC := false, hasNiche := false, backendRepr := .memory true }

noncomputable def tyZeroU32Arr : FieldSpec :=
  { size := 0, align := 4, unadjustedAbiAlign := 4, reprAlign := none, maxReprAlign := none,
    isReprC := false, hasNiche := false, backendRepr := .memory true }

noncomputable def tyAlign16Zst : FieldSpec :=
  { size := 0, align := 16, unadjustedAbiAlign := 1, reprAlign := some 16, maxReprAlign := some 16,
    isReprC := false, hasNiche := false, backendRepr := .memory true }

noncomputable def tyAligned8 : FieldSpec :=
  { size := 8, align := 8, unadjustedAbiAlign := 8, reprAlign := some 8, maxReprAlign := some 8,
    isReprC := false, hasNiche := false, backendRepr := .memory true }

noncomputable def tyReprCZst : FieldSpec :=
  { size := 0, align := 1, unadjustedAbiAlign := 1, reprAlign := none, maxReprAlign := none,
    isReprC := true, hasNiche := false, backendRepr := .memory true }

/-- Four-field benchmark tuple `(a: u8, b: u64, c: u8, d: u16)` matching Experiment A. -/
noncomputable def fieldsABCD : List FieldSpec := [tyU8, tyU64, tyU8, tyU16]

noncomputable def reprRustDefault : ReprOptions :=
  { kind := .rust, pack := none, align := none, randomizeLayout := false }

noncomputable def reprCDefault : ReprOptions :=
  { kind := .c, pack := none, align := none, randomizeLayout := false }

noncomputable def reprPacked1 : ReprOptions :=
  { kind := .rust, pack := some 1, align := none, randomizeLayout := false }

noncomputable def reprPacked2 : ReprOptions :=
  { kind := .rust, pack := some 2, align := none, randomizeLayout := false }

noncomputable def reprCPacked2 : ReprOptions :=
  { kind := .c, pack := some 2, align := none, randomizeLayout := false }

noncomputable def reprCAlign16 : ReprOptions :=
  { kind := .c, pack := none, align := some 16, randomizeLayout := false }

noncomputable def reprCPacked1 : ReprOptions :=
  { kind := .c, pack := some 1, align := none, randomizeLayout := false }

noncomputable def reprTrans : ReprOptions :=
  { kind := .transparent, pack := none, align := none, randomizeLayout := false }

/-- **Cross-Check 1 (`Exp A`)**: Exact byte-for-byte match against live `rustc` for `(u8, u64, u8, u16)`:
- `repr(Rust)` sorted (`b, d, a, c` -> offsets `[10, 0, 11, 8]`): `size = 16, align = 8`
- `repr(C)` declaration order (`offsets = [0, 8, 16, 18]`): `size = 24, align = 8`
- `repr(packed(2))` sorted (`[10, 0, 11, 8]`): `size = 12, align = 2`
- `repr(C, packed(2))` declaration order (`[0, 2, 10, 12]`): `size = 14, align = 2`
- `repr(C, align(16))` declaration order (`[0, 8, 16, 18]`): `size = 32, align = 16`
- `repr(C, packed)` declaration order (`[0, 1, 9, 10]`): `size = 12, align = 1`
- `-Zrandomize-layout` worst-case declaration permutation (`[tyU8, tyU16, tyU64, tyU8]`): `size = 24, align = 8` -/
theorem xc_expA_abcd_layout_matrix :
    let lRust := computeReprRustLayout reprRustDefault fieldsABCD
    let lC := computeReprRustLayout reprCDefault fieldsABCD
    let lP2 := computeReprRustLayout reprPacked2 fieldsABCD
    let lCP2 := computeReprRustLayout reprCPacked2 fieldsABCD
    let lCA16 := computeReprRustLayout reprCAlign16 fieldsABCD
    let lCP1 := computeReprRustLayout reprCPacked1 fieldsABCD
    let lRandWorst := computeOrderedLayout reprRustDefault [tyU8, tyU16, tyU64, tyU8]
    (lRust.size = 16 ∧ lRust.align = 8) ∧
    (lC.size = 24 ∧ lC.align = 8 ∧ lC.offsets = [0, 8, 16, 18]) ∧
    (lP2.size = 12 ∧ lP2.align = 2) ∧
    (lCP2.size = 14 ∧ lCP2.align = 2 ∧ lCP2.offsets = [0, 2, 10, 12]) ∧
    (lCA16.size = 32 ∧ lCA16.align = 16 ∧ lCA16.offsets = [0, 8, 16, 18]) ∧
    (lCP1.size = 12 ∧ lCP1.align = 1 ∧ lCP1.offsets = [0, 1, 9, 10]) ∧
    (lRandWorst.size = 24 ∧ lRandWorst.align = 8 ∧ lRandWorst.offsets = [0, 2, 8, 16]) := by
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩,
          ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- **Cross-Check 2 (`Exp B`, `CE2`)**: Exact ZST alignment-only separation:
- `ReprCZstMid(u8, Align16Zst, u8)`: `size = 32, align = 16, offsets = [0, 16, 16]`
- `ReprCZstEnd(u8, u8, Align16Zst)`: `size = 16, align = 16, offsets = [0, 1, 16]`
- `ReprRustZst(u8, Align16Zst, u8)`: `size = 16, align = 16`
- `ReprRustMixedZsts(u8, Align16Zst, u8, ())`: `size = 16, align = 16`
- `PureZst(Align16Zst, Align16Zst)`: `size = 0, align = 16, offsets = [0, 0]`
- `Pure1Zst((), PhantomData)`: `size = 0, align = 1, offsets = [0, 0]` -/
theorem xc_expB_zst_alignment_only_matrix :
    let lMid := computeReprRustLayout reprCDefault [tyU8, tyAlign16Zst, tyU8]
    let lEnd := computeReprRustLayout reprCDefault [tyU8, tyU8, tyAlign16Zst]
    let lRust := computeReprRustLayout reprRustDefault [tyU8, tyAlign16Zst, tyU8]
    let lMixed := computeReprRustLayout reprRustDefault [tyU8, tyAlign16Zst, tyU8, tyUnit]
    let lPure := computeReprRustLayout reprRustDefault [tyAlign16Zst, tyAlign16Zst]
    let lPure1 := computeReprRustLayout reprRustDefault [tyUnit, tyUnit]
    (lMid.size = 32 ∧ lMid.align = 16 ∧ lMid.offsets = [0, 16, 16]) ∧
    (lEnd.size = 16 ∧ lEnd.align = 16 ∧ lEnd.offsets = [0, 1, 16]) ∧
    (lRust.size = 16 ∧ lRust.align = 16) ∧
    (lMixed.size = 16 ∧ lMixed.align = 16) ∧
    (lPure.size = 0 ∧ lPure.align = 16 ∧ lPure.offsets = [0, 0]) ∧
    (lPure1.size = 0 ∧ lPure1.align = 1 ∧ lPure1.offsets = [0, 0]) := by
  refine ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- **Cross-Check 3 (`Exp C`, `CE3`)**: `checkTransparent` and `checkPacked` diagnostics across
`pre4e99638` (`rustc 1.98.0-nightly`, `49d734536`) and `post4e99638` (`rustc 1.102.0-nightly`,
`3ef0c22cd`):
- Same-struct `#[repr(packed, align(8))]` -> `.errE0587` in BOTH eras;
- `#[repr(transparent, C)]` -> `.errE0692`;
- `#[repr(transparent)](u32, u8)` -> `.errE0690`;
- `#[repr(transparent)](u8, [u32; 0])` -> `.errE0690`;
- `#[repr(transparent)](u8, CZst)` -> `.errE0690`;
- `#[repr(transparent)]([u32; 0])` -> `.ok`, `size = 0, align = 4` (single-field early return!);
- `#[repr(packed)] struct Bad(Aligned8)` -> `.errE0588` in `pre4e99638`, `.ok` in `post4e99638` (`size = 8, align = 1`);
- `#[repr(C, packed)] struct CBad(CAligned8)` -> `.errE0588` in `pre4e99638`, `.lintAlignedFieldsInPacked` in `post4e99638`;
- `#[repr(C, packed)] struct GenericPacked<T>(T)` (`ZcUnalign<Aligned8>`) -> `.ok` in BOTH eras! -/
theorem xc_expC_diagnostics_and_e0588_retirement :
    let badPackedAlign : ReprOptions :=
      { kind := .rust, pack := some 1, align := some 8, randomizeLayout := false }
    let lUnalignAligned8 := computeOrderedLayout reprCPacked1 [tyAligned8]
    let lSingleNon1Zst := computeOrderedLayout reprTrans [tyZeroU32Arr]
    let lSingleAlign16Zst := computeOrderedLayout reprTrans [tyAlign16Zst]
    checkPacked .pre4e99638 badPackedAlign [] = .errE0587 ∧
    checkPacked .post4e99638 badPackedAlign [] = .errE0587 ∧
    checkTransparent reprTrans true [tyU32] = .errE0692 ∧
    checkTransparent reprTrans false [tyU32, tyU8] = .errE0690 ∧
    checkTransparent reprTrans false [tyU8, tyZeroU32Arr] = .errE0690 ∧
    checkTransparent reprTrans false [tyU8, tyReprCZst] = .errE0690 ∧
    checkTransparent reprTrans false [tyZeroU32Arr] = .ok ∧
    (lSingleNon1Zst.size = 0 ∧ lSingleNon1Zst.align = 4 ∧ lSingleNon1Zst.unadjustedAbiAlign = 4) ∧
    (lSingleAlign16Zst.size = 0 ∧ lSingleAlign16Zst.align = 16 ∧ lSingleAlign16Zst.unadjustedAbiAlign = 16) ∧
    checkPacked .pre4e99638 reprPacked1 [FieldCheckNode.adt false true []] = .errE0588 ∧
    checkPacked .post4e99638 reprPacked1 [FieldCheckNode.adt false true []] = .ok ∧
    checkPacked .pre4e99638 reprCPacked1 [FieldCheckNode.adt true true []] = .errE0588 ∧
    checkPacked .post4e99638 reprCPacked1 [FieldCheckNode.adt true true []] = .lintAlignedFieldsInPacked ∧
    checkPacked .pre4e99638 reprCPacked1 [FieldCheckNode.genericParam true true] = .ok ∧
    checkPacked .post4e99638 reprCPacked1 [FieldCheckNode.genericParam true true] = .ok ∧
    (lUnalignAligned8.size = 8 ∧ lUnalignAligned8.align = 1 ∧
     lUnalignAligned8.unadjustedAbiAlign = 1 ∧ lUnalignAligned8.maxReprAlign = some 8) := by
  dsimp only
  simp only [checkPacked, checkPackedInnerList, checkTransparent, ReprKind.beq,
    computeOrderedLayout, placeFieldsFrom, effFieldAlign, alignUp, paddingNeeded,
    fieldsMaxEffAlign, computeUnadjustedAbiAlign, nonZstFields, FieldSpec.isZst,
    FieldSpec.is1Zst, countNonTrivialFields, fieldsMaxReprAlign, optMax,
    reprPacked1, reprCPacked1, reprTrans, tyAligned8, tyZeroU32Arr, tyAlign16Zst,
    tyU32, tyU8, tyReprCZst]
  repeat' constructor
  all_goals rfl

/-- **Cross-Check 4 (`Exp D`)**: `zerocopy` `ZcPacketHeader(tag: u8, val: Unalign<u64>, tail: u8)`
and `ReadOnly<(u8, u64)>` layout invariants. -/
theorem xc_expD_zerocopy_packet_and_readonly :
    let unalignU64 : FieldSpec :=
      { size := 8, align := 1, unadjustedAbiAlign := 1, reprAlign := none, maxReprAlign := none,
        isReprC := true, hasNiche := false, backendRepr := .memory true }
    let hdr := computeOrderedLayout reprCDefault [tyU8, unalignU64, tyU8]
    let tupleU8U64 : FieldSpec :=
      { size := 16, align := 8, unadjustedAbiAlign := 8, reprAlign := none, maxReprAlign := none,
        isReprC := false, hasNiche := false,
        backendRepr := .scalarPair .int .int 1 8 }
    let roTuple := computeOrderedLayout reprTrans [tupleU8U64]
    let reprCSingleU64 := computeOrderedLayout reprCDefault [tyU64]
    let reprTransSingleU64 := computeOrderedLayout reprTrans [tyU64]
    (hdr.size = 10 ∧ hdr.align = 1 ∧ hdr.offsets = [0, 1, 9]) ∧
    (roTuple.size = 16 ∧ roTuple.align = 8 ∧ roTuple.offsets = [0] ∧
     roTuple.backendRepr = .scalarPair .int .int 1 8) ∧
    (reprCSingleU64.backendRepr = .memory true ∧
     reprTransSingleU64.backendRepr = .scalar .int 8) := by
  refine ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- **Counterexample 5 (`CE5`: Hypothesis Tightness of `AllPow2Align` and `ReprModifierPow2`
for Monotone Packing)**:
- **(5a) Non-power-of-two field alignment (`[⟨3, 3⟩]`):** Under `#[repr(packed(2))]`, `min 3 2 = 2`
  gives `align = 2` and `size = alignUp 3 2 = 4`, whereas under `#[repr(packed(4))]`, `min 3 4 = 3`
  gives `align = 3` and `size = alignUp 3 3 = 3 < 4`.
- **(5b) Non-power-of-two packing bound (`[tyU32]` with `packed(3)` vs. `packed(4)`):** Under
  `packed(3)`, `min 4 3 = 3` gives `align = 3` and `size = alignUp 4 3 = 6`, whereas under
  `packed(4)`, `min 4 4 = 4` gives `align = 4` and `size = alignUp 4 4 = 4 < 6`.
Thus BOTH `AllPow2Align` and `ReprModifierPow2` are strictly required for Theorem 3b. -/
theorem ce5_non_pow2_packed_increases_size :
    let fNonPow2 : FieldSpec :=
      { size := 3, align := 3, unadjustedAbiAlign := 3, reprAlign := none, maxReprAlign := none,
        isReprC := true, hasNiche := false, backendRepr := .memory true }
    let rP2 : ReprOptions := { kind := .c, pack := some 2, align := none, randomizeLayout := false }
    let rP3 : ReprOptions := { kind := .c, pack := some 3, align := none, randomizeLayout := false }
    let rP4 : ReprOptions := { kind := .c, pack := some 4, align := none, randomizeLayout := false }
    let l5a_P2 := computeOrderedLayout rP2 [fNonPow2]
    let l5a_P4 := computeOrderedLayout rP4 [fNonPow2]
    let l5b_P3 := computeOrderedLayout rP3 [tyU32]
    let l5b_P4 := computeOrderedLayout rP4 [tyU32]
    (l5a_P2.size = 4 ∧ l5a_P4.size = 3 ∧ l5a_P4.size < l5a_P2.size) ∧
    (l5b_P3.size = 6 ∧ l5b_P4.size = 4 ∧ l5b_P4.size < l5b_P3.size) := by
  refine ⟨⟨rfl, rfl, Nat.lt_succ_self 3⟩, ⟨rfl, rfl, by decide⟩⟩

/-- **Counterexample 6 (`CE6`: Randomize-Layout Flag Scope)**:
`-Zrandomize-layout` sets `canRandomizeTypeLayout = true` for `repr(Rust)`, `repr(packed)`, and
`repr(transparent)` (`IS_TRANSPARENT` is absent from `FIELD_ORDER_UNOPTIMIZABLE` at `lib.rs:105`),
while keeping `canRandomizeTypeLayout = false` for `repr(C)` and `repr(C, packed)`. -/
theorem ce6_randomize_layout_scope :
    let rRust : ReprOptions := { kind := .rust, pack := none, align := none, randomizeLayout := true }
    let rRustPacked : ReprOptions := { kind := .rust, pack := some 2, align := none, randomizeLayout := true }
    let rTrans : ReprOptions := { kind := .transparent, pack := none, align := none, randomizeLayout := true }
    let rC : ReprOptions := { kind := .c, pack := none, align := none, randomizeLayout := true }
    let rCPacked : ReprOptions := { kind := .c, pack := some 2, align := none, randomizeLayout := true }
    rRust.canRandomizeTypeLayout = true ∧
    rRustPacked.canRandomizeTypeLayout = true ∧
    rTrans.canRandomizeTypeLayout = true ∧
    rC.canRandomizeTypeLayout = false ∧
    rCPacked.canRandomizeTypeLayout = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

end RustcAbiReprLayout

