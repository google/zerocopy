/-
  AbiReprTransparentFfiAttributeInheritanceSoundness.lean

  Kernel-checked Lean v4.34.1 formalization of `rustc` `#[repr(transparent)]`
  FFI `extern "C"` ABI and LLVM attribute inheritance (`noundef`, `range(...)`,
  `zeroext i1`, `nonnull`, `align`, `dereferenceable`, `noalias`, `readonly`),
  `ManuallyDrop<T>` (`MaybeDangling`) vs. `MaybeUninit<T>` union attribute
  erasure, and `zerocopy::ReadOnly<T>` vs. `zerocopy::Unalign<T>`
  (`#[repr(C, packed)]`) ABI divergence across x86_64, AArch64, and i686.

  Purity contract:
  - Standalone `Init`-only Lean v4.34.1 module (zero external imports)
  - Every `def` explicitly marked `noncomputable def` (0 `._unsafe_rec`)
  - 0 `sorry`, 0 `Classical.choice`, 0 `omega`, 0 `bv_decide`, 0 `native_decide`
  - 0 `partial def`, 0 `deriving` clauses on inductive/structure types
-/

namespace AbiReprTransparentSoundness

/-! ## Section 1: Boolean Helpers, Machine Primitives, Target Architectures, and Wrapping Ranges -/

/-- Decidable boolean equality helper without `BEq`/`deriving` machinery. -/
noncomputable def boolEq (a b : Bool) : Bool :=
  match a, b with
  | true, true => true
  | false, false => true
  | _, _ => false

theorem boolEq_refl (a : Bool) : boolEq a a = true := by
  cases a <;> rfl

theorem boolEq_comm (a b : Bool) : boolEq a b = boolEq b a := by
  cases a <;> cases b <;> rfl

theorem boolEq_eq (a b : Bool) : boolEq a b = true → a = b := by
  intro h
  cases a <;> cases b <;> first | rfl | exact False.elim (Bool.false_ne_true h)

/-- Helper converting `n ≠ 0` (via `0 < n`) into `Nat.beq n 0 = false`. -/
theorem nat_beq_zero_false_of_pos {n : Nat} (h : 0 < n) : Nat.beq n 0 = false := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 h)
  | succ _ => rfl

/-- Helper converting `Nat.beq a b = true` to `a = b`. -/
theorem nat_eq_of_beq_true {a b : Nat} (h : Nat.beq a b = true) : a = b :=
  Nat.eq_of_beq_eq_true h

theorem natBeq_comm (a b : Nat) : Nat.beq a b = Nat.beq b a := by
  cases h : Nat.beq a b with
  | true =>
    have heq := Nat.eq_of_beq_eq_true h
    rw [heq, Nat.beq_refl]
  | false =>
    cases hba : Nat.beq b a with
    | false => rfl
    | true =>
      have heq := Nat.eq_of_beq_eq_true hba
      rw [heq, Nat.beq_refl] at h
      exact False.elim (Bool.false_ne_true h.symm)

/-- Helper for `Nat.blt a b = false` when `b ≤ a`. -/
theorem nat_blt_false_of_le {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases hblt : Nat.blt a b with
  | false => rfl
  | true =>
    have hlt : a + 1 ≤ b := Nat.le_of_ble_eq_true hblt
    exact False.elim (Nat.not_lt_of_ge h hlt)

/-- Supported integer scalar widths matching `rustc_abi::Integer`. -/
inductive IntWidth : Type where
  | i8 : IntWidth
  | i16 : IntWidth
  | i32 : IntWidth
  | i64 : IntWidth
  | i128 : IntWidth

noncomputable def IntWidth.bits : IntWidth → Nat
  | .i8 => 8
  | .i16 => 16
  | .i32 => 32
  | .i64 => 64
  | .i128 => 128

noncomputable def IntWidth.bytes : IntWidth → Nat
  | .i8 => 1
  | .i16 => 2
  | .i32 => 4
  | .i64 => 8
  | .i128 => 16

noncomputable def IntWidth.modulus (w : IntWidth) : Nat :=
  Nat.pow 2 w.bits

noncomputable def IntWidth.beq : IntWidth → IntWidth → Bool
  | .i8, .i8 => true
  | .i16, .i16 => true
  | .i32, .i32 => true
  | .i64, .i64 => true
  | .i128, .i128 => true
  | _, _ => false

theorem IntWidth.beq_refl (w : IntWidth) : IntWidth.beq w w = true := by
  cases w <;> rfl

theorem IntWidth.beq_eq (w1 w2 : IntWidth) : IntWidth.beq w1 w2 = true → w1 = w2 := by
  intro h
  cases w1 <;> cases w2 <;> first | rfl | exact False.elim (Bool.false_ne_true h)

theorem IntWidth.bytes_pos (w : IntWidth) : 0 < w.bytes := by
  cases w <;> exact Nat.succ_pos _

theorem IntWidth.bits_pos (w : IntWidth) : 0 < w.bits := by
  cases w <;> exact Nat.succ_pos _

theorem IntWidth.bits_eq_eight_mul_bytes (w : IntWidth) :
    w.bits = 8 * w.bytes := by
  cases w <;> rfl

theorem IntWidth.modulus_pos (w : IntWidth) : 0 < w.modulus := by
  unfold IntWidth.modulus
  exact Nat.pow_pos (Nat.succ_pos 1)

theorem IntWidth.modulus_gt_one (w : IntWidth) : 1 < w.modulus := by
  unfold IntWidth.modulus
  have h1 : 1 < 2 := Nat.lt_succ_self 1
  have hle : 2 ≤ Nat.pow 2 w.bits := by
    cases w <;> exact Nat.le_self_pow (Nat.ne_of_gt (Nat.succ_pos _)) 2
  exact Nat.lt_of_lt_of_le h1 hle

theorem IntWidth.modulus_sub_one_lt (w : IntWidth) : w.modulus - 1 < w.modulus :=
  Nat.sub_lt (IntWidth.modulus_pos w) (Nat.succ_pos 0)

theorem IntWidth.one_le_modulus_sub_one (w : IntWidth) : 1 ≤ w.modulus - 1 :=
  Nat.le_sub_of_add_le (IntWidth.modulus_gt_one w)

/-- Target architectures modeled for FFI lowering divergence (`x86_64` SysV,
`AArch64` AAPCS64, `i686` SysV). -/
inductive TargetArch : Type where
  | x86_64 : TargetArch
  | aarch64 : TargetArch
  | i686 : TargetArch

noncomputable def TargetArch.ptrBytes : TargetArch → Nat
  | .x86_64 => 8
  | .aarch64 => 8
  | .i686 => 4

noncomputable def TargetArch.ptrModulus (arch : TargetArch) : Nat :=
  match arch with
  | .x86_64 => IntWidth.modulus .i64
  | .aarch64 => IntWidth.modulus .i64
  | .i686 => IntWidth.modulus .i32

noncomputable def TargetArch.beq : TargetArch → TargetArch → Bool
  | .x86_64, .x86_64 => true
  | .aarch64, .aarch64 => true
  | .i686, .i686 => true
  | _, _ => false

theorem TargetArch.ptrBytes_pos (arch : TargetArch) : 0 < arch.ptrBytes := by
  cases arch <;> exact Nat.succ_pos _

theorem TargetArch.ptrModulus_gt_one (arch : TargetArch) : 1 < arch.ptrModulus := by
  cases arch
  · exact IntWidth.modulus_gt_one .i64
  · exact IntWidth.modulus_gt_one .i64
  · exact IntWidth.modulus_gt_one .i32

/-- `rustc_abi::Primitive`. Models first-class `Primitive::Bool` alongside
`Int`, `Pointer`, and floats. -/
inductive PrimitiveTy : Type where
  | bool : PrimitiveTy
  | int (w : IntWidth) (signed : Bool) : PrimitiveTy
  | pointer : PrimitiveTy
  | float32 : PrimitiveTy
  | float64 : PrimitiveTy

noncomputable def PrimitiveTy.bytes (arch : TargetArch) : PrimitiveTy → Nat
  | .bool => 1
  | .int w _ => w.bytes
  | .pointer => arch.ptrBytes
  | .float32 => 4
  | .float64 => 8

noncomputable def PrimitiveTy.defaultAlign (arch : TargetArch) : PrimitiveTy → Nat
  | .bool => 1
  | .int w _ => w.bytes
  | .pointer => arch.ptrBytes
  | .float32 => 4
  | .float64 => 8

noncomputable def PrimitiveTy.modulus (arch : TargetArch) : PrimitiveTy → Nat
  | .bool => 2
  | .int w _ => w.modulus
  | .pointer => arch.ptrModulus
  | .float32 => IntWidth.modulus .i32
  | .float64 => IntWidth.modulus .i64

noncomputable def PrimitiveTy.isInt : PrimitiveTy → Bool
  | .int _ _ => true
  | _ => false

noncomputable def PrimitiveTy.isBool : PrimitiveTy → Bool
  | .bool => true
  | _ => false

noncomputable def PrimitiveTy.isPointer : PrimitiveTy → Bool
  | .pointer => true
  | _ => false

noncomputable def PrimitiveTy.beq : PrimitiveTy → PrimitiveTy → Bool
  | .bool, .bool => true
  | .int w1 s1, .int w2 s2 => IntWidth.beq w1 w2 && boolEq s1 s2
  | .pointer, .pointer => true
  | .float32, .float32 => true
  | .float64, .float64 => true
  | _, _ => false

theorem PrimitiveTy.bytes_pos (arch : TargetArch) (p : PrimitiveTy) :
    0 < p.bytes arch := by
  cases p with
  | bool => exact Nat.succ_pos 0
  | int w _ => exact IntWidth.bytes_pos w
  | pointer => exact TargetArch.ptrBytes_pos arch
  | float32 => exact Nat.succ_pos 3
  | float64 => exact Nat.succ_pos 7

theorem PrimitiveTy.defaultAlign_pos (arch : TargetArch) (p : PrimitiveTy) :
    0 < p.defaultAlign arch := by
  cases p with
  | bool => exact Nat.succ_pos 0
  | int w _ => exact IntWidth.bytes_pos w
  | pointer => exact TargetArch.ptrBytes_pos arch
  | float32 => exact Nat.succ_pos 3
  | float64 => exact Nat.succ_pos 7

theorem PrimitiveTy.modulus_gt_one (arch : TargetArch) (p : PrimitiveTy) :
    1 < p.modulus arch := by
  cases p with
  | bool => exact Nat.lt_succ_self 1
  | int w _ => exact IntWidth.modulus_gt_one w
  | pointer => exact TargetArch.ptrModulus_gt_one arch
  | float32 => exact IntWidth.modulus_gt_one .i32
  | float64 => exact IntWidth.modulus_gt_one .i64

theorem PrimitiveTy.beq_refl (p : PrimitiveTy) : PrimitiveTy.beq p p = true := by
  cases p with
  | bool => rfl
  | int w s =>
    dsimp only [PrimitiveTy.beq]
    rw [IntWidth.beq_refl w, boolEq_refl s]
    rfl
  | pointer => rfl
  | float32 => rfl
  | float64 => rfl

/-- Inclusive wrapping range `[start, endVal]` over unsigned bit patterns in
`[0, modulus - 1]`, matching `rustc_abi::WrappingRange`. When `start > endVal`,
represents the wrap-around union `v ≥ start ∨ v ≤ endVal` (used for signed
`NonZero<iN>` / `PatternKind::Or`). -/
structure WrappingRange where
  start : Nat
  endVal : Nat

noncomputable def WrappingRange.beq (r1 r2 : WrappingRange) : Bool :=
  Nat.beq r1.start r2.start && Nat.beq r1.endVal r2.endVal

noncomputable def WrappingRange.full (modVal : Nat) : WrappingRange :=
  { start := 0, endVal := modVal - 1 }

noncomputable def WrappingRange.nonZero (modVal : Nat) : WrappingRange :=
  { start := 1, endVal := modVal - 1 }

noncomputable def WrappingRange.boolRange : WrappingRange :=
  { start := 0, endVal := 1 }

noncomputable def WrappingRange.WellFormed (modVal : Nat) (r : WrappingRange) : Prop :=
  1 < modVal ∧ r.start < modVal ∧ r.endVal < modVal

noncomputable def WrappingRange.contains (modVal : Nat) (r : WrappingRange) (v : Nat) : Prop :=
  v < modVal ∧
    (if r.start ≤ r.endVal then r.start ≤ v ∧ v ≤ r.endVal
     else r.start ≤ v ∨ v ≤ r.endVal)

noncomputable def WrappingRange.containsBool (modVal : Nat) (r : WrappingRange) (v : Nat) : Bool :=
  Nat.blt v modVal &&
    (if Nat.ble r.start r.endVal then Nat.ble r.start v && Nat.ble v r.endVal
     else Nat.ble r.start v || Nat.ble v r.endVal)

noncomputable def WrappingRange.isFull (modVal : Nat) (r : WrappingRange) : Bool :=
  Nat.beq r.start 0 && Nat.beq r.endVal (modVal - 1)

noncomputable def WrappingRange.excludesZero (r : WrappingRange) : Bool :=
  Nat.blt 0 r.start && Nat.ble r.start r.endVal

theorem WrappingRange.beq_refl (r : WrappingRange) : WrappingRange.beq r r = true := by
  dsimp only [WrappingRange.beq]
  rw [Nat.beq_refl r.start, Nat.beq_refl r.endVal]
  rfl

theorem WrappingRange.full_wellFormed (modVal : Nat) (h : 1 < modVal) :
    WrappingRange.WellFormed modVal (WrappingRange.full modVal) := by
  refine ⟨h, Nat.lt_trans Nat.zero_lt_one h, ?_⟩
  exact Nat.sub_lt (Nat.lt_trans Nat.zero_lt_one h) (Nat.succ_pos 0)

theorem WrappingRange.nonZero_wellFormed (modVal : Nat) (h : 1 < modVal) :
    WrappingRange.WellFormed modVal (WrappingRange.nonZero modVal) := by
  refine ⟨h, h, ?_⟩
  exact Nat.sub_lt (Nat.lt_trans Nat.zero_lt_one h) (Nat.succ_pos 0)

theorem WrappingRange.boolRange_wellFormed :
    WrappingRange.WellFormed 2 WrappingRange.boolRange :=
  ⟨Nat.lt_succ_self 1, Nat.succ_pos 1, Nat.lt_succ_self 1⟩

theorem WrappingRange.full_contains (modVal v : Nat) (_hmod : 0 < modVal) (hv : v < modVal) :
    (WrappingRange.full modVal).contains modVal v := by
  unfold WrappingRange.contains WrappingRange.full
  refine ⟨hv, ?_⟩
  have hz : 0 ≤ modVal - 1 := Nat.zero_le _
  simp only [hz, ite_true]
  exact ⟨Nat.zero_le v, Nat.le_sub_one_of_lt hv⟩

theorem WrappingRange.nonZero_contains (modVal v : Nat) (hmod : 1 < modVal)
    (hpos : 1 ≤ v) (hv : v < modVal) :
    (WrappingRange.nonZero modVal).contains modVal v := by
  unfold WrappingRange.contains WrappingRange.nonZero
  refine ⟨hv, ?_⟩
  have h1 : 1 ≤ modVal - 1 := Nat.le_sub_of_add_le hmod
  simp only [h1, ite_true]
  exact ⟨hpos, Nat.le_sub_one_of_lt hv⟩

theorem WrappingRange.nonZero_excludes_zero (modVal : Nat) (hmod : 1 < modVal) :
    ¬ (WrappingRange.nonZero modVal).contains modVal 0 := by
  intro hc
  unfold WrappingRange.contains WrappingRange.nonZero at hc
  have h1 : 1 ≤ modVal - 1 := Nat.le_sub_of_add_le hmod
  have hif := hc.2
  simp only [h1, ite_true] at hif
  exact Nat.not_succ_le_zero 0 hif.1

theorem WrappingRange.contains_implies_lt (modVal : Nat) (r : WrappingRange) (v : Nat)
    (h : r.contains modVal v) : v < modVal :=
  h.1

theorem WrappingRange.excludesZero_sound (modVal : Nat) (r : WrappingRange)
    (h : r.excludesZero = true) : ¬ r.contains modVal 0 := by
  intro hc
  unfold WrappingRange.excludesZero at h
  have hparts := Bool.and_eq_true_iff.mp h
  have hpos : 0 < r.start := Nat.le_of_ble_eq_true hparts.1
  have hle : r.start ≤ r.endVal := Nat.le_of_ble_eq_true hparts.2
  unfold WrappingRange.contains at hc
  have hif := hc.2
  simp only [hle, ite_true] at hif
  exact Nat.not_le_of_gt hpos hif.1

theorem WrappingRange.isFull_eq_true (modVal : Nat) (r : WrappingRange)
    (h : r.isFull modVal = true) : r = WrappingRange.full modVal := by
  unfold WrappingRange.isFull at h
  have hparts := Bool.and_eq_true_iff.mp h
  have hs : r.start = 0 := Nat.eq_of_beq_eq_true hparts.1
  have he : r.endVal = modVal - 1 := Nat.eq_of_beq_eq_true hparts.2
  cases r
  simp only at hs he
  subst hs
  subst he
  rfl

theorem WrappingRange.full_isFull (modVal : Nat) :
    (WrappingRange.full modVal).isFull modVal = true := by
  unfold WrappingRange.isFull WrappingRange.full
  rw [Nat.beq_refl 0, Nat.beq_refl (modVal - 1)]
  rfl

theorem WrappingRange.nonZero_not_isFull (modVal : Nat) :
    (WrappingRange.nonZero modVal).isFull modVal = false := by
  unfold WrappingRange.isFull WrappingRange.nonZero
  have hne : Nat.beq 1 0 = false := rfl
  rw [hne]
  rfl

/-- Wrapped-around signed `NonZero<i32>` range: start = 1, end = 2^32 - 1 (same
unsigned `WrappingRange { start: 1, end: 0xFFFF_FFFF }` emitted by `rustc` as
`range(i32 1, 0)`), and general asymmetric wrapping range `start > endVal`. -/
theorem WrappingRange.wrapAround_excludes_zero (modVal s e : Nat)
    (hmod : 1 < modVal) (hs : e < s) (_he_lt : e < modVal) (hz : 0 < s) :
    ¬ ({ start := s, endVal := e } : WrappingRange).contains modVal 0 ↔ ¬ (0 ≤ e) := by
  unfold WrappingRange.contains
  have hnot : ¬ (s ≤ e) := Nat.not_le_of_gt hs
  simp only [hnot, ite_false]
  constructor
  · intro hn h0
    exact hn ⟨Nat.lt_trans Nat.zero_lt_one hmod, Or.inr h0⟩
  · intro hne ⟨_, hor⟩
    cases hor with
    | inl hge => exact Nat.not_le_of_gt hz hge
    | inr hle => exact hne hle

/-! ## Section 2: `rustc_abi` `Scalar`, `BackendRepr`, `ReprConfig`, and `PointeeFacts` -/

/-- Exact model of `rustc_abi::Scalar` (`compiler/rustc_abi/src/lib.rs`). -/
inductive AbiScalar : Type where
  | initialized (prim : PrimitiveTy) (validRange : WrappingRange) : AbiScalar
  | unionVal (prim : PrimitiveTy) : AbiScalar

noncomputable def AbiScalar.primitive : AbiScalar → PrimitiveTy
  | .initialized p _ => p
  | .unionVal p => p

noncomputable def AbiScalar.toUnion (s : AbiScalar) : AbiScalar :=
  .unionVal s.primitive

noncomputable def AbiScalar.isBool : AbiScalar → Bool
  | .initialized .bool _ => true
  | _ => false

noncomputable def AbiScalar.isUninitValid : AbiScalar → Bool
  | .initialized _ _ => false
  | .unionVal _ => true

noncomputable def AbiScalar.validRange (arch : TargetArch) : AbiScalar → WrappingRange
  | .initialized _ r => r
  | .unionVal p => WrappingRange.full (p.modulus arch)

noncomputable def AbiScalar.isAlwaysValid (arch : TargetArch) : AbiScalar → Bool
  | .initialized p r => r.isFull (p.modulus arch)
  | .unionVal _ => true

noncomputable def AbiScalar.beq : AbiScalar → AbiScalar → Bool
  | .initialized p1 r1, .initialized p2 r2 => PrimitiveTy.beq p1 p2 && WrappingRange.beq r1 r2
  | .unionVal p1, .unionVal p2 => PrimitiveTy.beq p1 p2
  | _, _ => false

theorem AbiScalar.toUnion_primitive (s : AbiScalar) :
    s.toUnion.primitive = s.primitive := by
  cases s <;> rfl

theorem AbiScalar.toUnion_isUninitValid (s : AbiScalar) :
    s.toUnion.isUninitValid = true := by
  cases s <;> rfl

theorem AbiScalar.toUnion_isAlwaysValid (arch : TargetArch) (s : AbiScalar) :
    s.toUnion.isAlwaysValid arch = true := by
  cases s <;> rfl

theorem AbiScalar.toUnion_isBool (s : AbiScalar) :
    s.toUnion.isBool = false := by
  cases s <;> rfl

theorem AbiScalar.toUnion_idempotent (s : AbiScalar) :
    s.toUnion.toUnion = s.toUnion := by
  cases s <;> rfl

theorem AbiScalar.beq_refl (s : AbiScalar) : AbiScalar.beq s s = true := by
  cases s with
  | initialized p r =>
    dsimp only [AbiScalar.beq]
    rw [PrimitiveTy.beq_refl p, WrappingRange.beq_refl r]
    rfl
  | unionVal p =>
    dsimp only [AbiScalar.beq]
    exact PrimitiveTy.beq_refl p

/-- Exact model of `rustc_abi::BackendRepr`. -/
inductive BackendRepr : Type where
  | zst : BackendRepr
  | scalar (s : AbiScalar) : BackendRepr
  | scalarPair (a b : AbiScalar) : BackendRepr
  | memory (sizeBytes alignBytes : Nat) (sized : Bool) : BackendRepr

noncomputable def BackendRepr.toUnion : BackendRepr → BackendRepr
  | .zst => .zst
  | .scalar s => .scalar s.toUnion
  | .scalarPair a b => .scalarPair a.toUnion b.toUnion
  | .memory sz al sized => .memory sz al sized

noncomputable def BackendRepr.isAggregate : BackendRepr → Bool
  | .scalarPair _ _ => true
  | .memory _ _ _ => true
  | _ => false

noncomputable def BackendRepr.isZst : BackendRepr → Bool
  | .zst => true
  | _ => false

noncomputable def BackendRepr.isInitializedNoundef : BackendRepr → Bool
  | .zst => true
  | .scalar s => !s.isUninitValid
  | .scalarPair a b => !a.isUninitValid && !b.isUninitValid
  | .memory _ _ _ => false

theorem BackendRepr.toUnion_idempotent (r : BackendRepr) :
    r.toUnion.toUnion = r.toUnion := by
  cases r with
  | zst => rfl
  | scalar s => exact congrArg BackendRepr.scalar (AbiScalar.toUnion_idempotent s)
  | scalarPair a b =>
    dsimp only [BackendRepr.toUnion]
    rw [AbiScalar.toUnion_idempotent a, AbiScalar.toUnion_idempotent b]
  | memory _ _ _ => rfl

/-- `PointeeInfo` summary from `rustc_middle::ty::layout::ty_and_layout_pointee_info_at`.
Distinguishes safe references (`&T` / `&mut T`) from `MaybeDangling` /
`ManuallyDrop<&T>` (`safe = false`, `derefBytes = 0`, `alignBytes = align(T)`)
and raw pointers. -/
structure PointeeFacts where
  isSafeRef : Bool
  frozen : Bool
  derefBytes : Nat
  alignBytes : Nat

noncomputable def PointeeFacts.maskForMaybeDangling (pf : PointeeFacts) : PointeeFacts :=
  { isSafeRef := false, frozen := false, derefBytes := 0, alignBytes := pf.alignBytes }

noncomputable def PointeeFacts.beq (p1 p2 : PointeeFacts) : Bool :=
  boolEq p1.isSafeRef p2.isSafeRef &&
  boolEq p1.frozen p2.frozen &&
  Nat.beq p1.derefBytes p2.derefBytes &&
  Nat.beq p1.alignBytes p2.alignBytes

theorem PointeeFacts.mask_preserves_align (pf : PointeeFacts) :
    (pf.maskForMaybeDangling).alignBytes = pf.alignBytes := rfl

theorem PointeeFacts.mask_clears_safe (pf : PointeeFacts) :
    (pf.maskForMaybeDangling).isSafeRef = false := rfl

theorem PointeeFacts.mask_clears_deref (pf : PointeeFacts) :
    (pf.maskForMaybeDangling).derefBytes = 0 := rfl

/-- `ReprFlags` / `ReprOptions` modeled from `compiler/rustc_abi/src/lib.rs`. -/
structure ReprConfig where
  isC : Bool
  isTransparent : Bool
  pack : Option Nat
  align : Option Nat

noncomputable def ReprConfig.inhibitNewtypeAbiOpt (r : ReprConfig) : Bool :=
  r.isC

noncomputable def ReprConfig.inhibitsUnionAbiOpt (r : ReprConfig) : Bool :=
  r.isC

theorem ReprConfig.transparent_allows_newtype_opt :
    ({ isC := false, isTransparent := true, pack := none, align := none } : ReprConfig).inhibitNewtypeAbiOpt = false := rfl

theorem ReprConfig.reprC_inhibits_newtype_opt (packOpt alignOpt : Option Nat) :
    ({ isC := true, isTransparent := false, pack := packOpt, align := alignOpt } : ReprConfig).inhibitNewtypeAbiOpt = true := rfl

/-- Complete layout summary mirroring `LayoutData` fields relevant to ABI
classification and attribute emission. -/
structure LayoutSummary where
  size : Nat
  align : Nat
  unadjustedAbiAlign : Nat
  repr : BackendRepr
  pointee : Option PointeeFacts
  hasSliceRefRangeBypass : Bool
  allFieldsNoUndef : Bool

noncomputable def LayoutSummary.isZst (l : LayoutSummary) : Bool :=
  Nat.beq l.size 0

noncomputable def LayoutSummary.isOneZst (l : LayoutSummary) : Bool :=
  Nat.beq l.size 0 && Nat.beq l.align 1

/-! ## Section 3: Rust Wrapper Type AST (`AbiTy`) and `LayoutCalculator` Semantics -/

/-- Source-level Rust type AST covering primitives, 1-ZSTs, over-aligned ZSTs,
`#[repr(transparent)]` wrappers, `#[repr(C)]` / `#[repr(C, packed(N))]` structs,
`ManuallyDrop<T>`, `MaybeUninit<T>`, `zerocopy::ReadOnly<T>`, and
`zerocopy::Unalign<T>`. -/
inductive AbiTy : Type where
  | unit : AbiTy
  | phantomZst : Nat → AbiTy
  | alignedZst (alignBytes : Nat) : AbiTy
  | scalar (prim : PrimitiveTy) (validRange : WrappingRange)
      (pointee : Option PointeeFacts) (isSliceRef : Bool) : AbiTy
  | scalarPair (a b : AbiScalar) (sizeBytes alignBytes : Nat) (isSliceRef : Bool) : AbiTy
  | transparentStruct (zstPrefix : List AbiTy) (inner : AbiTy) (zstSuffix : List AbiTy) : AbiTy
  | cStruct (packAlign : Option Nat) (fields : List AbiTy) : AbiTy
  | manuallyDrop (inner : AbiTy) : AbiTy
  | maybeUninitUnion (inner : AbiTy) : AbiTy
  | readOnly (inner : AbiTy) : AbiTy
  | unalign (inner : AbiTy) : AbiTy

noncomputable def AbiTy.is1Zst : AbiTy → Bool
  | .unit => true
  | .phantomZst _ => true
  | _ => false

noncomputable def all1Zst : List AbiTy → Bool
  | [] => true
  | x :: xs => x.is1Zst && all1Zst xs

noncomputable def AbiTy.WellFormed (arch : TargetArch) : AbiTy → Prop
  | .unit => True
  | .phantomZst _ => True
  | .alignedZst a => 1 < a
  | .scalar p r _ _ => WrappingRange.WellFormed (p.modulus arch) r
  | .scalarPair a b sz al _ =>
    0 < sz ∧ 0 < al ∧
      (match a with
       | .initialized pa ra => WrappingRange.WellFormed (pa.modulus arch) ra
       | .unionVal _ => True) ∧
      (match b with
       | .initialized pb rb => WrappingRange.WellFormed (pb.modulus arch) rb
       | .unionVal _ => True)
  | .transparentStruct zpre inner zsuf =>
    all1Zst zpre = true ∧ all1Zst zsuf = true ∧ inner.WellFormed arch
  | .cStruct packOpt fields =>
    (match packOpt with | none => True | some p => 0 < p) ∧
    (∀ f, f ∈ fields → f.WellFormed arch)
  | .manuallyDrop inner => inner.WellFormed arch
  | .maybeUninitUnion inner => inner.WellFormed arch
  | .readOnly inner => inner.WellFormed arch
  | .unalign inner => inner.WellFormed arch

noncomputable def stripTransparentLayer : AbiTy → AbiTy
  | .transparentStruct _ inner _ => stripTransparentLayer inner
  | .readOnly inner => stripTransparentLayer inner
  | t => t

theorem stripTransparentLayer_transparentStruct (zpre zsuf : List AbiTy) (inner : AbiTy) :
    stripTransparentLayer (.transparentStruct zpre inner zsuf) = stripTransparentLayer inner := rfl

theorem stripTransparentLayer_readOnly (inner : AbiTy) :
    stripTransparentLayer (.readOnly inner) = stripTransparentLayer inner := rfl

/-- Helper: align `offset` up to `align` (when `align > 0`). -/
noncomputable def alignTo (offset alignVal : Nat) : Nat :=
  if Nat.beq alignVal 0 then offset
  else
    let rem := offset % alignVal
    if Nat.beq rem 0 then offset else offset + (alignVal - rem)

theorem alignTo_zero (alignVal : Nat) : alignTo 0 alignVal = 0 := by
  unfold alignTo
  cases Nat.beq alignVal 0 with
  | true => rfl
  | false =>
    have hmod : 0 % alignVal = 0 := Nat.zero_mod alignVal
    simp only [hmod]
    rfl

theorem alignTo_one (offset : Nat) : alignTo offset 1 = offset := by
  unfold alignTo
  have h1 : Nat.beq 1 0 = false := rfl
  have hmod : offset % 1 = 0 := Nat.mod_one offset
  simp only [h1, hmod]
  rfl

noncomputable def nonZstLayouts : List LayoutSummary → List LayoutSummary
  | [] => []
  | l :: ls => if l.isZst then nonZstLayouts ls else l :: nonZstLayouts ls

noncomputable def allLayoutsNoUndef : List LayoutSummary → Bool
  | [] => true
  | l :: ls => l.allFieldsNoUndef && allLayoutsNoUndef ls

noncomputable def foldCFields (packOpt : Option Nat) :
    List LayoutSummary → Nat → Nat → Nat × Nat
  | [], curOffset, curAlign => (alignTo curOffset curAlign, curAlign)
  | l :: ls, curOffset, curAlign =>
    let fAlign := match packOpt with
      | none => l.align
      | some p => Nat.min l.align p
    let nextOff := alignTo curOffset fAlign
    let nextAlign := Nat.max curAlign fAlign
    foldCFields packOpt ls (nextOff + l.size) nextAlign

/-- Pure `LayoutSummary` combinators factoring wrapper transformations cleanly
so wrapper lemmas never duplicate `layoutOf` AST traversal. -/
noncomputable def applyTransparentToLayout (l : LayoutSummary) : LayoutSummary :=
  { size := l.size
    align := l.align
    unadjustedAbiAlign := l.unadjustedAbiAlign
    repr := l.repr
    pointee := l.pointee
    hasSliceRefRangeBypass := false
    allFieldsNoUndef := l.allFieldsNoUndef }

noncomputable def applyMaybeDanglingToLayout (l : LayoutSummary) : LayoutSummary :=
  { size := l.size
    align := l.align
    unadjustedAbiAlign := l.unadjustedAbiAlign
    repr := l.repr
    pointee := Option.map PointeeFacts.maskForMaybeDangling l.pointee
    hasSliceRefRangeBypass := false
    allFieldsNoUndef := l.allFieldsNoUndef }

noncomputable def applyMaybeUninitUnionToLayout (l : LayoutSummary) : LayoutSummary :=
  { size := l.size
    align := l.align
    unadjustedAbiAlign := l.unadjustedAbiAlign
    repr := l.repr.toUnion
    pointee := none
    hasSliceRefRangeBypass := false
    allFieldsNoUndef := false }

noncomputable def applyUnalignToLayout (l : LayoutSummary) : LayoutSummary :=
  let reprVal : BackendRepr :=
    if Nat.beq l.size 0 then .zst else .memory l.size 1 true
  { size := l.size
    align := 1
    unadjustedAbiAlign := 1
    repr := reprVal
    pointee := none
    hasSliceRefRangeBypass := false
    allFieldsNoUndef := l.allFieldsNoUndef }

mutual
/-- Compute `LayoutSummary` for any `AbiTy`, faithfully modeling
`LayoutCalculator::univariant` (`compiler/rustc_abi/src/layout.rs:1329-1417`)
and `layout_of_union` (`compiler/rustc_abi/src/layout.rs:438`). -/
noncomputable def layoutOf (arch : TargetArch) : AbiTy → LayoutSummary
  | .unit =>
    { size := 0, align := 1, unadjustedAbiAlign := 1, repr := .zst
      pointee := none, hasSliceRefRangeBypass := false, allFieldsNoUndef := true }
  | .phantomZst _ =>
    { size := 0, align := 1, unadjustedAbiAlign := 1, repr := .zst
      pointee := none, hasSliceRefRangeBypass := false, allFieldsNoUndef := true }
  | .alignedZst a =>
    { size := 0, align := a, unadjustedAbiAlign := a, repr := .zst
      pointee := none, hasSliceRefRangeBypass := false, allFieldsNoUndef := true }
  | .scalar p r pt isSlice =>
    { size := p.bytes arch
      align := p.defaultAlign arch
      unadjustedAbiAlign := p.defaultAlign arch
      repr := .scalar (.initialized p r)
      pointee := pt
      hasSliceRefRangeBypass := isSlice
      allFieldsNoUndef := true }
  | .scalarPair a b sz al isSlice =>
    { size := sz
      align := al
      unadjustedAbiAlign := al
      repr := .scalarPair a b
      pointee := none
      hasSliceRefRangeBypass := isSlice
      allFieldsNoUndef := !a.isUninitValid && !b.isUninitValid }
  | .transparentStruct _ inner _ =>
    applyTransparentToLayout (layoutOf arch inner)
  | .cStruct packOpt fields =>
    let layouts := layoutOfList arch fields
    let (totalSize, totalAlign) := foldCFields packOpt layouts 0 1
    let nonZsts := nonZstLayouts layouts
    let noundefAll := allLayoutsNoUndef layouts
    let reprVal : BackendRepr :=
      if Nat.beq totalSize 0 then .zst
      else
        match nonZsts with
        | [single] =>
          match single.repr with
          | .scalarPair a b =>
            if Nat.beq totalAlign single.align && Nat.beq totalSize single.size then
              .scalarPair a b
            else
              .memory totalSize totalAlign true
          | _ => .memory totalSize totalAlign true
        | _ => .memory totalSize totalAlign true
    { size := totalSize
      align := totalAlign
      unadjustedAbiAlign := totalAlign
      repr := reprVal
      pointee := none
      hasSliceRefRangeBypass := false
      allFieldsNoUndef := noundefAll }
  | .manuallyDrop inner =>
    applyMaybeDanglingToLayout (layoutOf arch inner)
  | .maybeUninitUnion inner =>
    applyMaybeUninitUnionToLayout (layoutOf arch inner)
  | .readOnly inner =>
    applyTransparentToLayout (layoutOf arch inner)
  | .unalign inner =>
    applyUnalignToLayout (layoutOf arch inner)

noncomputable def layoutOfList (arch : TargetArch) : List AbiTy → List LayoutSummary
  | [] => []
  | f :: fs => layoutOf arch f :: layoutOfList arch fs
end

theorem layoutOf_transparent_eq (arch : TargetArch) (zpre zsuf : List AbiTy) (inner : AbiTy) :
    layoutOf arch (.transparentStruct zpre inner zsuf) =
      applyTransparentToLayout (layoutOf arch inner) := rfl

theorem layoutOf_readOnly_eq (arch : TargetArch) (inner : AbiTy) :
    layoutOf arch (.readOnly inner) = applyTransparentToLayout (layoutOf arch inner) := rfl

theorem layoutOf_manuallyDrop_eq (arch : TargetArch) (inner : AbiTy) :
    layoutOf arch (.manuallyDrop inner) = applyMaybeDanglingToLayout (layoutOf arch inner) := rfl

theorem layoutOf_maybeUninitUnion_eq (arch : TargetArch) (inner : AbiTy) :
    layoutOf arch (.maybeUninitUnion inner) = applyMaybeUninitUnionToLayout (layoutOf arch inner) := rfl

theorem layoutOf_unalign_eq (arch : TargetArch) (inner : AbiTy) :
    layoutOf arch (.unalign inner) = applyUnalignToLayout (layoutOf arch inner) := rfl

theorem layoutOf_unalign_memory (arch : TargetArch) (inner : AbiTy)
    (hsize : 0 < (layoutOf arch inner).size) :
    (layoutOf arch (.unalign inner)).align = 1 ∧
    (layoutOf arch (.unalign inner)).repr = .memory (layoutOf arch inner).size 1 true := by
  rw [layoutOf_unalign_eq]
  unfold applyUnalignToLayout
  have hbeq : Nat.beq (layoutOf arch inner).size 0 = false := nat_beq_zero_false_of_pos hsize
  rw [hbeq]
  exact ⟨rfl, rfl⟩

theorem layoutOf_transparent_preserves_fields (arch : TargetArch)
    (zpre zsuf : List AbiTy) (inner : AbiTy) :
    (layoutOf arch (.transparentStruct zpre inner zsuf)).size = (layoutOf arch inner).size ∧
    (layoutOf arch (.transparentStruct zpre inner zsuf)).align = (layoutOf arch inner).align ∧
    (layoutOf arch (.transparentStruct zpre inner zsuf)).unadjustedAbiAlign =
      (layoutOf arch inner).unadjustedAbiAlign ∧
    (layoutOf arch (.transparentStruct zpre inner zsuf)).repr = (layoutOf arch inner).repr ∧
    (layoutOf arch (.transparentStruct zpre inner zsuf)).pointee = (layoutOf arch inner).pointee ∧
    (layoutOf arch (.transparentStruct zpre inner zsuf)).allFieldsNoUndef =
      (layoutOf arch inner).allFieldsNoUndef := by
  rw [layoutOf_transparent_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem layoutOf_readOnly_preserves_fields (arch : TargetArch) (inner : AbiTy) :
    (layoutOf arch (.readOnly inner)).size = (layoutOf arch inner).size ∧
    (layoutOf arch (.readOnly inner)).align = (layoutOf arch inner).align ∧
    (layoutOf arch (.readOnly inner)).unadjustedAbiAlign =
      (layoutOf arch inner).unadjustedAbiAlign ∧
    (layoutOf arch (.readOnly inner)).repr = (layoutOf arch inner).repr ∧
    (layoutOf arch (.readOnly inner)).pointee = (layoutOf arch inner).pointee := by
  rw [layoutOf_readOnly_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem layoutOf_manuallyDrop_preserves_repr (arch : TargetArch) (inner : AbiTy) :
    (layoutOf arch (.manuallyDrop inner)).size = (layoutOf arch inner).size ∧
    (layoutOf arch (.manuallyDrop inner)).align = (layoutOf arch inner).align ∧
    (layoutOf arch (.manuallyDrop inner)).repr = (layoutOf arch inner).repr := by
  rw [layoutOf_manuallyDrop_eq]
  exact ⟨rfl, rfl, rfl⟩

theorem layoutOf_maybeUninitUnion_erases_scalar (arch : TargetArch) (inner : AbiTy) :
    (layoutOf arch (.maybeUninitUnion inner)).size = (layoutOf arch inner).size ∧
    (layoutOf arch (.maybeUninitUnion inner)).align = (layoutOf arch inner).align ∧
    (layoutOf arch (.maybeUninitUnion inner)).repr = (layoutOf arch inner).repr.toUnion ∧
    (layoutOf arch (.maybeUninitUnion inner)).pointee = none := by
  rw [layoutOf_maybeUninitUnion_eq]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Section 4: `rustc_ty_utils::abi` (`PassMode`, `ArgAttributes`) & `rustc_codegen_llvm` Emission -/

inductive ExtMode : Type where
  | none : ExtMode
  | zext : ExtMode
  | sext : ExtMode

noncomputable def ExtMode.beq : ExtMode → ExtMode → Bool
  | .none, .none => true
  | .zext, .zext => true
  | .sext, .sext => true
  | _, _ => false

theorem ExtMode.beq_refl (e : ExtMode) : ExtMode.beq e e = true := by
  cases e <;> rfl

theorem ExtMode.beq_comm (e1 e2 : ExtMode) : ExtMode.beq e1 e2 = ExtMode.beq e2 e1 := by
  cases e1 <;> cases e2 <;> rfl

/-- Exact `ArgAttributes` modeled from `compiler/rustc_target/src/callconv/mod.rs`. -/
structure ArgAttributes where
  noUndef : Bool
  nonNull : Bool
  ext : ExtMode
  pointeeAlign : Option Nat
  pointeeSize : Nat
  noAlias : Bool
  readOnly : Bool

noncomputable def ArgAttributes.empty : ArgAttributes :=
  { noUndef := false
    nonNull := false
    ext := .none
    pointeeAlign := none
    pointeeSize := 0
    noAlias := false
    readOnly := false }

noncomputable def ArgAttributes.withNoUndef (b : Bool) : ArgAttributes :=
  { noUndef := b
    nonNull := false
    ext := .none
    pointeeAlign := none
    pointeeSize := 0
    noAlias := false
    readOnly := false }

/-- Models `ArgAttributes::eq_abi` (`compiler/rustc_target/src/callconv/mod.rs:186`). -/
noncomputable def ArgAttributes.eqAbi (a b : ArgAttributes) : Bool :=
  ExtMode.beq a.ext b.ext

/-- Models `rustc_target::callconv::PassMode`. -/
inductive PassMode : Type where
  | ignore : PassMode
  | direct (attrs : ArgAttributes) : PassMode
  | pair (a b : ArgAttributes) : PassMode
  | cast (sizeBytes : Nat) (attrs : ArgAttributes) : PassMode
  | indirect (attrs : ArgAttributes) (onStack : Bool) : PassMode

noncomputable def PassMode.sameVariantKind : PassMode → PassMode → Bool
  | .ignore, .ignore => true
  | .direct _, .direct _ => true
  | .pair _ _, .pair _ _ => true
  | .cast sz1 _, .cast sz2 _ => Nat.beq sz1 sz2
  | .indirect _ os1, .indirect _ os2 => boolEq os1 os2
  | _, _ => false

theorem PassMode.sameVariantKind_refl (pm : PassMode) : pm.sameVariantKind pm = true := by
  cases pm with
  | ignore => rfl
  | direct _ => rfl
  | pair _ _ => rfl
  | cast sz _ => exact Nat.beq_refl sz
  | indirect _ os => exact boolEq_refl os

theorem PassMode.sameVariantKind_symm (p1 p2 : PassMode)
    (h : p1.sameVariantKind p2 = true) : p2.sameVariantKind p1 = true := by
  cases p1 with
  | ignore => cases p2 <;> first | rfl | exact False.elim (Bool.false_ne_true h)
  | direct _ => cases p2 <;> first | rfl | exact False.elim (Bool.false_ne_true h)
  | pair _ _ => cases p2 <;> first | rfl | exact False.elim (Bool.false_ne_true h)
  | cast sz1 _ =>
    cases p2 with
    | cast sz2 _ =>
      dsimp only [PassMode.sameVariantKind] at h ⊢
      rw [natBeq_comm] at h
      exact h
    | _ => exact False.elim (Bool.false_ne_true h)
  | indirect _ os1 =>
    cases p2 with
    | indirect _ os2 =>
      dsimp only [PassMode.sameVariantKind] at h ⊢
      rw [boolEq_comm] at h
      exact h
    | _ => exact False.elim (Bool.false_ne_true h)

inductive CallingConv : Type where
  | externC : CallingConv
  | externRust : CallingConv

/-- Exact transcription of `arg_attrs_for_rust_scalar` (`compiler/rustc_ty_utils/src/abi.rs`)
plus `extend_integer_width_to` (`compiler/rustc_target/src/callconv/mod.rs` & `x86_64.rs`). -/
noncomputable def computeArgAttrs (cc : CallingConv)
    (optLevel : Bool) (isReturn : Bool) (s : AbiScalar) (pt : Option PointeeFacts) :
    ArgAttributes :=
  let noUndefVal := !s.isUninitValid
  let extVal : ExtMode :=
    match cc with
    | .externRust =>
      if s.isBool then .zext else .none
    | .externC =>
      match s.primitive with
      | .bool => .zext
      | .int w signed =>
        if Nat.blt w.bits 32 && !isReturn then
          if signed then .sext else .zext
        else
          .none
      | _ => .none
  match s with
  | .initialized .pointer r =>
    let nonNullVal := r.excludesZero
    match pt with
    | none =>
      { noUndef := noUndefVal
        nonNull := nonNullVal
        ext := extVal
        pointeeAlign := none
        pointeeSize := 0
        noAlias := false
        readOnly := false }
    | some info =>
      let alignVal := if Nat.blt 1 info.alignBytes then some info.alignBytes else none
      let derefVal :=
        if optLevel && !isReturn && info.isSafeRef && info.frozen then info.derefBytes
        else 0
      let noAliasVal := optLevel && !isReturn && info.isSafeRef && info.frozen
      let readOnlyVal := optLevel && !isReturn && info.isSafeRef && info.frozen
      { noUndef := noUndefVal
        nonNull := nonNullVal
        ext := extVal
        pointeeAlign := alignVal
        pointeeSize := derefVal
        noAlias := noAliasVal
        readOnly := readOnlyVal }
  | _ =>
    { noUndef := noUndefVal
      nonNull := false
      ext := extVal
      pointeeAlign := none
      pointeeSize := 0
      noAlias := false
      readOnly := false }

/-- Target-aware `fn_abi_adjust_for_abi` (`compiler/rustc_ty_utils/src/abi.rs:624`)
+ `adjust_for_rust_abi` (`compiler/rustc_target/src/callconv/mod.rs:717-817`)
+ `x86_64::compute_abi_info`, `aarch64::compute_abi_info`, `x86::compute_abi_info`. -/
noncomputable def computePassMode (arch : TargetArch) (cc : CallingConv)
    (optLevel : Bool) (isReturn : Bool) (l : LayoutSummary) : PassMode :=
  match l.repr with
  | .zst => .ignore
  | .scalar s => .direct (computeArgAttrs cc optLevel isReturn s l.pointee)
  | .scalarPair a b =>
    match cc with
    | .externRust =>
      .pair (computeArgAttrs cc optLevel isReturn a none)
            (computeArgAttrs cc optLevel isReturn b none)
    | .externC =>
      match arch with
      | .x86_64 => .cast l.size ArgAttributes.empty
      | .aarch64 =>
        if Nat.ble l.size 16 then .cast l.size ArgAttributes.empty
        else .indirect ArgAttributes.empty false
      | .i686 =>
        if isReturn then .indirect ArgAttributes.empty false
        else .indirect ArgAttributes.empty true
  | .memory sz _ _ =>
    match cc with
    | .externRust =>
      -- Per `adjust_for_rust_abi` (`compiler/rustc_target/src/callconv/mod.rs:804-816`):
      -- small aggregates (`size <= ptr_size`) cast to an integer register with
      -- `ArgAttribute::NoUndef` iff `layout_is_noundef`; larger aggregates stay `Indirect`.
      if Nat.ble sz arch.ptrBytes then
        .cast sz (ArgAttributes.withNoUndef l.allFieldsNoUndef)
      else
        .indirect ArgAttributes.empty false
    | .externC =>
      match arch with
      | .x86_64 =>
        if Nat.ble sz 16 then .cast sz ArgAttributes.empty
        else .indirect ArgAttributes.empty true
      | .aarch64 =>
        if Nat.ble sz 16 then .cast sz ArgAttributes.empty
        else .indirect ArgAttributes.empty false
      | .i686 =>
        if isReturn then .indirect ArgAttributes.empty false
        else .indirect ArgAttributes.empty true

/-- Exact LLVM IR type & attribute projection matching
`rustc_codegen_llvm/src/abi.rs` (`get_attrs`, `apply_attrs_to_llfn`, `apply_range_attr`). -/
inductive LlvmCarrierTy : Type where
  | voidTy : LlvmCarrierTy
  | i1 : LlvmCarrierTy
  | intBits (bits : Nat) : LlvmCarrierTy
  | ptr : LlvmCarrierTy
  | structPair (bitsA bitsB : Nat) : LlvmCarrierTy

structure LlvmParamIR where
  carrier : LlvmCarrierTy
  passedDirect : Bool
  passedByCast : Bool
  passedIndirect : Bool
  noUndef : Bool
  zeroExt : Bool
  signExt : Bool
  nonNull : Bool
  rangeAttr : Option WrappingRange
  alignAttr : Option Nat
  dereferenceableAttr : Option Nat
  noAliasAttr : Bool
  readOnlyAttr : Bool
  sliceLengthRange : Option Nat

noncomputable def scalarToLlvmCarrier : PrimitiveTy → LlvmCarrierTy
  | .bool => .i1
  | .int w _ => .intBits w.bits
  | .pointer => .ptr
  | .float32 => .intBits 32
  | .float64 => .intBits 64

/-- `apply_range_attr` (`compiler/rustc_codegen_llvm/src/abi.rs:472-488` & `681-693`):
only emits `range(...)` when optimizing, for integer scalars, excluding `bool`
and full-range scalars (such as `Scalar::Union` or bare `u32`). -/
noncomputable def applyRangeAttr (arch : TargetArch) (optLevel : Bool)
    (s : AbiScalar) : Option WrappingRange :=
  if optLevel && s.primitive.isInt && !s.isBool && !s.isAlwaysValid arch then
    some (s.validRange arch)
  else
    none

/-- Models `get_attrs` + `apply_attrs_to_llfn` (`compiler/rustc_codegen_llvm/src/abi.rs:38-107, 465-583`).
Crucial empirical facts captured directly:
1. `alignAttr` (`pointee_align`), `zeroExt`, and `signExt` (`arg_ext`) are applied
   unconditionally at BOTH `-O0` and `-O2` (`rustc_codegen_llvm/src/abi.rs:66-73`).
2. `noUndef`, `nonNull`, `noAliasAttr`, `readOnlyAttr` live in `OPTIMIZATION_ATTRIBUTES`,
   gated alongside `rangeAttr` and `dereferenceableAttr` on `optLevel = true` (`-O2`,
   unless MemorySanitizer overrides `NoUndef` at `-O0`).
3. `PassMode::Cast` applies ONLY `cast.attrs` and NEVER calls `apply_range_attr`!
4. `PassMode::Pair` (under `extern "Rust"`) attaches the ad-hoc slice-length
   `range(0, isize::MAX / elem_size)` ONLY when `l.hasSliceRefRangeBypass = true`
   (`*arg.layout.ty.kind() == ty::Ref(_, Slice(_), _)`); wrapping `&[T]` in
   `#[repr(transparent)]` turns `ty.kind()` into `ty::Adt`, clearing this bypass! -/
noncomputable def emitLlvmArgAttrs (arch : TargetArch) (optLevel : Bool)
    (pm : PassMode) (l : LayoutSummary) : LlvmParamIR :=
  match pm with
  | .ignore =>
    { carrier := .voidTy
      passedDirect := false, passedByCast := false, passedIndirect := false
      noUndef := false, zeroExt := false, signExt := false, nonNull := false
      rangeAttr := none, alignAttr := none, dereferenceableAttr := none
      noAliasAttr := false, readOnlyAttr := false, sliceLengthRange := none }
  | .direct attrs =>
    let carrierTy :=
      match l.repr with
      | .scalar s => scalarToLlvmCarrier s.primitive
      | _ => .intBits (8 * l.size)
    let rangeOpt :=
      match l.repr with
      | .scalar s => applyRangeAttr arch optLevel s
      | _ => none
    let derefOpt :=
      if optLevel && Nat.blt 0 attrs.pointeeSize then some attrs.pointeeSize else none
    { carrier := carrierTy
      passedDirect := true, passedByCast := false, passedIndirect := false
      noUndef := optLevel && attrs.noUndef
      zeroExt := ExtMode.beq attrs.ext .zext
      signExt := ExtMode.beq attrs.ext .sext
      nonNull := optLevel && attrs.nonNull
      rangeAttr := rangeOpt
      alignAttr := attrs.pointeeAlign
      dereferenceableAttr := derefOpt
      noAliasAttr := optLevel && attrs.noAlias
      readOnlyAttr := optLevel && attrs.readOnly
      sliceLengthRange := none }
  | .pair _ _ =>
    let slRange :=
      if optLevel && l.hasSliceRefRangeBypass then some (IntWidth.modulus .i64)
      else none
    { carrier := .structPair (8 * arch.ptrBytes) (8 * arch.ptrBytes)
      passedDirect := true, passedByCast := false, passedIndirect := false
      noUndef := optLevel, zeroExt := false, signExt := false, nonNull := false
      rangeAttr := none, alignAttr := none, dereferenceableAttr := none
      noAliasAttr := false, readOnlyAttr := false, sliceLengthRange := slRange }
  | .cast sz attrs =>
    let castBits :=
      match arch with
      | .aarch64 => if Nat.ble sz 8 then 64 else 8 * sz
      | _ => 8 * sz
    { carrier := .intBits castBits
      passedDirect := false, passedByCast := true, passedIndirect := false
      noUndef := optLevel && attrs.noUndef
      zeroExt := ExtMode.beq attrs.ext .zext
      signExt := ExtMode.beq attrs.ext .sext
      nonNull := optLevel && attrs.nonNull
      rangeAttr := none
      alignAttr := attrs.pointeeAlign
      dereferenceableAttr := none
      noAliasAttr := false
      readOnlyAttr := false
      sliceLengthRange := none }
  | .indirect _ _ =>
    { carrier := .ptr
      passedDirect := false, passedByCast := false, passedIndirect := true
      noUndef := optLevel, zeroExt := false, signExt := false, nonNull := optLevel
      rangeAttr := none, alignAttr := some l.align, dereferenceableAttr := none
      noAliasAttr := false, readOnlyAttr := false, sliceLengthRange := none }

/-- Key structural lemma: `applyTransparentToLayout` leaves `computePassMode`
completely invariant across ALL architectures, calling conventions, and opt-levels! -/
theorem computePassMode_applyTransparent (arch : TargetArch) (cc : CallingConv)
    (optLevel isReturn : Bool) (l : LayoutSummary) :
    computePassMode arch cc optLevel isReturn (applyTransparentToLayout l) =
    computePassMode arch cc optLevel isReturn l := by
  unfold computePassMode applyTransparentToLayout
  cases l.repr <;> rfl

/-- Key structural lemma: `applyTransparentToLayout` leaves `emitLlvmArgAttrs`
completely invariant for every `PassMode` EXCEPT `PassMode.pair` (where a
`#[repr(transparent)]` wrapper around `&[T]` turns `ty::Ref` into `ty::Adt`,
suppressing the ad-hoc `sliceLengthRange` in `rustc_codegen_llvm/src/abi.rs:553`). -/
theorem emitLlvmArgAttrs_applyTransparent_of_not_pair (arch : TargetArch) (optLevel : Bool)
    (pm : PassMode) (l : LayoutSummary)
    (hnotPair : ∀ a b, pm ≠ .pair a b) :
    emitLlvmArgAttrs arch optLevel pm (applyTransparentToLayout l) =
    emitLlvmArgAttrs arch optLevel pm l := by
  cases pm with
  | ignore => rfl
  | direct _ => rfl
  | pair a b => exact False.elim (hnotPair a b rfl)
  | cast _ _ => rfl
  | indirect _ _ => rfl

theorem computePassMode_not_pair_of_externC (arch : TargetArch)
    (optLevel isReturn : Bool) (l : LayoutSummary) (a b : ArgAttributes) :
    computePassMode arch .externC optLevel isReturn l ≠ .pair a b := by
  unfold computePassMode
  cases hrepr : l.repr with
  | zst => intro h; cases h
  | scalar _ => intro h; cases h
  | scalarPair _ _ =>
    cases arch with
    | x86_64 => intro h; cases h
    | aarch64 =>
      dsimp only
      cases Nat.ble l.size 16 <;> (intro h; cases h)
    | i686 =>
      dsimp only
      cases isReturn <;> (intro h; cases h)
  | memory sz _ _ =>
    cases arch with
    | x86_64 =>
      dsimp only
      cases Nat.ble sz 16 <;> (intro h; cases h)
    | aarch64 =>
      dsimp only
      cases Nat.ble sz 16 <;> (intro h; cases h)
    | i686 =>
      dsimp only
      cases isReturn <;> (intro h; cases h)

theorem computePassMode_not_pair_of_scalar (arch : TargetArch) (cc : CallingConv)
    (optLevel isReturn : Bool) (l : LayoutSummary) (s : AbiScalar)
    (hrepr : l.repr = .scalar s) (a b : ArgAttributes) :
    computePassMode arch cc optLevel isReturn l ≠ .pair a b := by
  unfold computePassMode
  rw [hrepr]
  intro h; cases h

/-! ## Section 5: Operational Runtime Value Model, Rust Validity, and LLVM UB Semantics -/

inductive RuntimeScalar : Type where
  | uninit : RuntimeScalar
  | bits (val : Nat) : RuntimeScalar
  | ptr (addr : Nat) (provValid : Bool) (allocBytes : Nat) (allocAlign : Nat) : RuntimeScalar

noncomputable def rustValidScalar (arch : TargetArch) (p : PrimitiveTy)
    (r : WrappingRange) (pt : Option PointeeFacts) (v : RuntimeScalar) : Prop :=
  match p, v with
  | .bool, .bits n => n ≤ 1
  | .int _ _, .bits n => r.contains (p.modulus arch) n
  | .float32, .bits n => n < p.modulus arch
  | .float64, .bits n => n < p.modulus arch
  | .pointer, .ptr addr provValid allocBytes allocAlign =>
    r.contains (p.modulus arch) addr ∧
    match pt with
    | none => True
    | some info =>
      info.alignBytes ∣ addr ∧
      (if info.isSafeRef then
        provValid = true ∧ info.derefBytes ≤ allocBytes ∧ info.alignBytes ≤ allocAlign
       else True)
  | _, _ => False

noncomputable def rustValidVal (arch : TargetArch) : AbiTy → RuntimeScalar → Prop
  | .unit, _ => True
  | .phantomZst _, _ => True
  | .alignedZst _, _ => True
  | .scalar p r pt _, v => rustValidScalar arch p r pt v
  | .scalarPair _ _ _ _ _, _ => True
  | .transparentStruct _ inner _, v => rustValidVal arch inner v
  | .cStruct _ [inner], v => rustValidVal arch inner v
  | .cStruct _ _, _ => True
  | .manuallyDrop inner, v => rustValidVal arch inner v
  | .maybeUninitUnion _, _ => True
  | .readOnly inner, v => rustValidVal arch inner v
  | .unalign inner, v => rustValidVal arch inner v

/-- LLVM IR parameter attribute soundness obligation (`llvmAttrSatisfied arch ir v`). -/
noncomputable def llvmAttrSatisfied (_arch : TargetArch) (ir : LlvmParamIR)
    (v : RuntimeScalar) : Prop :=
  (ir.noUndef = true → v ≠ .uninit) ∧
  (ir.zeroExt = true →
    match ir.carrier with
    | .i1 => ∃ b, v = .bits b ∧ b ≤ 1
    | _ => ∃ b, v = .bits b) ∧
  (match ir.rangeAttr with
   | none => True
   | some r =>
     match ir.carrier with
     | .intBits bits => ∃ n, v = .bits n ∧ r.contains (Nat.pow 2 bits) n
     | _ => True) ∧
  (ir.nonNull = true →
    match ir.carrier with
    | .ptr => ∃ addr pv ab aa, v = .ptr addr pv ab aa ∧ addr ≠ 0
    | _ => True) ∧
  (match ir.alignAttr with
   | none => True
   | some al =>
     match ir.carrier with
     | .ptr => ∃ addr pv ab aa, v = .ptr addr pv ab aa ∧ al ∣ addr
     | _ => True) ∧
  (match ir.dereferenceableAttr with
   | none => True
   | some sz =>
     match ir.carrier with
     | .ptr => ∃ addr pv ab aa, v = .ptr addr pv ab aa ∧ pv = true ∧ sz ≤ ab
     | _ => True)

noncomputable def AbiAttrSound (arch : TargetArch) (ty : AbiTy) (ir : LlvmParamIR) : Prop :=
  ∀ v, rustValidVal arch ty v → llvmAttrSatisfied arch ir v

theorem llvmAttrSatisfied_empty_attrs (arch : TargetArch) (c : LlvmCarrierTy)
    (pd pc pi : Bool) (v : RuntimeScalar) :
    llvmAttrSatisfied arch
      { carrier := c, passedDirect := pd, passedByCast := pc, passedIndirect := pi
        noUndef := false, zeroExt := false, signExt := false, nonNull := false
        rangeAttr := none, alignAttr := none, dereferenceableAttr := none
        noAliasAttr := false, readOnlyAttr := false, sliceLengthRange := none } v := by
  unfold llvmAttrSatisfied
  refine ⟨?_, ?_, trivial, ?_, trivial, trivial⟩
  · intro h; exact False.elim (Bool.false_ne_true h)
  · intro h; exact False.elim (Bool.false_ne_true h)
  · intro h; exact False.elim (Bool.false_ne_true h)

theorem llvmAttrSatisfied_of_cleared (arch : TargetArch) (ir : LlvmParamIR)
    (hnu : ir.noUndef = false) (hze : ir.zeroExt = false) (hnn : ir.nonNull = false)
    (hr : ir.rangeAttr = none) (ha : ir.alignAttr = none) (hd : ir.dereferenceableAttr = none)
    (v : RuntimeScalar) : llvmAttrSatisfied arch ir v := by
  unfold llvmAttrSatisfied
  rw [hnu, hze, hnn, hr, ha, hd]
  refine ⟨?_, ?_, trivial, ?_, trivial, trivial⟩
  · intro h; exact False.elim (Bool.false_ne_true h)
  · intro h; exact False.elim (Bool.false_ne_true h)
  · intro h; exact False.elim (Bool.false_ne_true h)

/-! ## Section 6: Flagship Soundness, Isomorphism, and Substitution Theorems -/

/-! ### Theorem 1: `#[repr(transparent)]` Exact ABI & Attribute Isomorphism -/

theorem reprTransparent_passMode_eq (arch : TargetArch) (cc : CallingConv)
    (optLevel isReturn : Bool) (zpre zsuf : List AbiTy) (inner : AbiTy) :
    computePassMode arch cc optLevel isReturn
      (layoutOf arch (.transparentStruct zpre inner zsuf)) =
    computePassMode arch cc optLevel isReturn (layoutOf arch inner) := by
  rw [layoutOf_transparent_eq]
  exact computePassMode_applyTransparent arch cc optLevel isReturn (layoutOf arch inner)

theorem reprTransparent_llvm_ir_eq_externC (arch : TargetArch) (optLevel isReturn : Bool)
    (zpre zsuf : List AbiTy) (inner : AbiTy) :
    emitLlvmArgAttrs arch optLevel
      (computePassMode arch .externC optLevel isReturn
        (layoutOf arch (.transparentStruct zpre inner zsuf)))
      (layoutOf arch (.transparentStruct zpre inner zsuf)) =
    emitLlvmArgAttrs arch optLevel
      (computePassMode arch .externC optLevel isReturn (layoutOf arch inner))
      (layoutOf arch inner) := by
  rw [layoutOf_transparent_eq]
  rw [computePassMode_applyTransparent]
  exact emitLlvmArgAttrs_applyTransparent_of_not_pair arch optLevel
    (computePassMode arch .externC optLevel isReturn (layoutOf arch inner))
    (layoutOf arch inner)
    (computePassMode_not_pair_of_externC arch optLevel isReturn (layoutOf arch inner))

theorem reprTransparent_llvm_ir_eq_of_scalar (arch : TargetArch) (cc : CallingConv)
    (optLevel isReturn : Bool) (zpre zsuf : List AbiTy) (inner : AbiTy) (s : AbiScalar)
    (hscalar : (layoutOf arch inner).repr = .scalar s) :
    emitLlvmArgAttrs arch optLevel
      (computePassMode arch cc optLevel isReturn
        (layoutOf arch (.transparentStruct zpre inner zsuf)))
      (layoutOf arch (.transparentStruct zpre inner zsuf)) =
    emitLlvmArgAttrs arch optLevel
      (computePassMode arch cc optLevel isReturn (layoutOf arch inner))
      (layoutOf arch inner) := by
  rw [layoutOf_transparent_eq, computePassMode_applyTransparent]
  exact emitLlvmArgAttrs_applyTransparent_of_not_pair arch optLevel
    (computePassMode arch cc optLevel isReturn (layoutOf arch inner))
    (layoutOf arch inner)
    (computePassMode_not_pair_of_scalar arch cc optLevel isReturn (layoutOf arch inner) s hscalar)

theorem reprTransparent_exact_abi_attr_isomorphism (arch : TargetArch)
    (optLevel isReturn : Bool) (zpre zsuf : List AbiTy) (inner : AbiTy) :
    (layoutOf arch (.transparentStruct zpre inner zsuf)).size = (layoutOf arch inner).size ∧
    (layoutOf arch (.transparentStruct zpre inner zsuf)).align = (layoutOf arch inner).align ∧
    (layoutOf arch (.transparentStruct zpre inner zsuf)).unadjustedAbiAlign =
      (layoutOf arch inner).unadjustedAbiAlign ∧
    (layoutOf arch (.transparentStruct zpre inner zsuf)).repr = (layoutOf arch inner).repr ∧
    (layoutOf arch (.transparentStruct zpre inner zsuf)).pointee = (layoutOf arch inner).pointee ∧
    computePassMode arch .externC optLevel isReturn
      (layoutOf arch (.transparentStruct zpre inner zsuf)) =
      computePassMode arch .externC optLevel isReturn (layoutOf arch inner) ∧
    emitLlvmArgAttrs arch optLevel
      (computePassMode arch .externC optLevel isReturn
        (layoutOf arch (.transparentStruct zpre inner zsuf)))
      (layoutOf arch (.transparentStruct zpre inner zsuf)) =
    emitLlvmArgAttrs arch optLevel
      (computePassMode arch .externC optLevel isReturn (layoutOf arch inner))
      (layoutOf arch inner) := by
  have hf := layoutOf_transparent_preserves_fields arch zpre zsuf inner
  refine ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, ?_, ?_⟩
  · exact reprTransparent_passMode_eq arch .externC optLevel isReturn zpre zsuf inner
  · exact reprTransparent_llvm_ir_eq_externC arch optLevel isReturn zpre zsuf inner

theorem readOnly_exact_abi_attr_isomorphism (arch : TargetArch)
    (optLevel isReturn : Bool) (inner : AbiTy) :
    computePassMode arch .externC optLevel isReturn (layoutOf arch (.readOnly inner)) =
      computePassMode arch .externC optLevel isReturn (layoutOf arch inner) ∧
    emitLlvmArgAttrs arch optLevel
      (computePassMode arch .externC optLevel isReturn (layoutOf arch (.readOnly inner)))
      (layoutOf arch (.readOnly inner)) =
    emitLlvmArgAttrs arch optLevel
      (computePassMode arch .externC optLevel isReturn (layoutOf arch inner))
      (layoutOf arch inner) := by
  rw [layoutOf_readOnly_eq]
  rw [computePassMode_applyTransparent]
  refine ⟨rfl, ?_⟩
  exact emitLlvmArgAttrs_applyTransparent_of_not_pair arch optLevel
    (computePassMode arch .externC optLevel isReturn (layoutOf arch inner))
    (layoutOf arch inner)
    (computePassMode_not_pair_of_externC arch optLevel isReturn (layoutOf arch inner))

theorem nested_transparent_isomorphism_externC (arch : TargetArch)
    (optLevel isReturn : Bool)
    (zpre1 zsuf1 zpre2 zsuf2 : List AbiTy) (inner : AbiTy) :
    emitLlvmArgAttrs arch optLevel
      (computePassMode arch .externC optLevel isReturn
        (layoutOf arch (.transparentStruct zpre1 (.transparentStruct zpre2 inner zsuf2) zsuf1)))
      (layoutOf arch (.transparentStruct zpre1 (.transparentStruct zpre2 inner zsuf2) zsuf1)) =
    emitLlvmArgAttrs arch optLevel
      (computePassMode arch .externC optLevel isReturn (layoutOf arch inner))
      (layoutOf arch inner) := by
  have h1 := reprTransparent_llvm_ir_eq_externC arch optLevel isReturn zpre1 zsuf1
    (.transparentStruct zpre2 inner zsuf2)
  have h2 := reprTransparent_llvm_ir_eq_externC arch optLevel isReturn zpre2 zsuf2 inner
  exact h1.trans h2

/-- Subtlety observed empirically in `rustc_codegen_llvm/src/abi.rs:553`:
In `extern "Rust"`, wrapping `&[u32]` (`isSliceRef = true`) in a `#[repr(transparent)]`
struct preserves `PassMode.pair` and `noundef`, **while losing** the ad-hoc
`sliceLengthRange` (`range(i64 0, ...)`) because `*arg.layout.ty.kind()` changes
from `ty::Ref` to `ty::Adt`! -/
theorem transparent_wrap_slice_ref_loses_ad_hoc_range (arch : TargetArch)
    (zpre zsuf : List AbiTy) (a b : AbiScalar) (sz al : Nat) :
    let sliceTy := AbiTy.scalarPair a b sz al true
    let wrapTy := AbiTy.transparentStruct zpre sliceTy zsuf
    let sliceIr := emitLlvmArgAttrs arch true
      (computePassMode arch .externRust true false (layoutOf arch sliceTy))
      (layoutOf arch sliceTy)
    let wrapIr := emitLlvmArgAttrs arch true
      (computePassMode arch .externRust true false (layoutOf arch wrapTy))
      (layoutOf arch wrapTy)
    sliceIr.sliceLengthRange = some (IntWidth.modulus .i64) ∧
    wrapIr.sliceLengthRange = none ∧
    wrapIr.noUndef = sliceIr.noUndef := by
  exact ⟨rfl, rfl, rfl⟩

/-- Helper lemma factoring `ManuallyDrop` (`MaybeDangling`) preservation of
scalar value attributes cleanly without nested `split` explosions. -/
theorem computeArgAttrs_maskForMaybeDangling (cc : CallingConv)
    (optLevel isReturn : Bool) (s : AbiScalar) (pt : Option PointeeFacts) :
    let aBare := computeArgAttrs cc optLevel isReturn s pt
    let aMd := computeArgAttrs cc optLevel isReturn s (Option.map PointeeFacts.maskForMaybeDangling pt)
    aMd.noUndef = aBare.noUndef ∧
    aMd.nonNull = aBare.nonNull ∧
    aMd.ext = aBare.ext ∧
    aMd.pointeeAlign = aBare.pointeeAlign ∧
    aMd.pointeeSize = 0 ∧
    aMd.noAlias = false ∧
    aMd.readOnly = false := by
  cases s with
  | unionVal _ =>
    dsimp only [computeArgAttrs]
    cases cc <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | initialized p r =>
    cases p with
    | bool => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | int _ _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | float32 => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | float64 => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | pointer =>
      cases pt with
      | none => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | some pf =>
        dsimp only [computeArgAttrs, Option.map, PointeeFacts.maskForMaybeDangling]
        cases optLevel <;> cases isReturn <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `ManuallyDrop<T>` (`MaybeDangling<T>`) preserves value-validity attributes
(`noundef`, `range(...)`, `zeroext`, `nonnull`, `align`) for all scalars, and
selectively clears `noalias`, `readonly`, and `dereferenceable` on references! -/
theorem manuallyDrop_preserves_scalar_value_attrs (arch : TargetArch)
    (cc : CallingConv) (optLevel isReturn : Bool)
    (p : PrimitiveTy) (r : WrappingRange) (pt : Option PointeeFacts) (isSl : Bool) :
    let bareIr := emitLlvmArgAttrs arch optLevel
      (computePassMode arch cc optLevel isReturn (layoutOf arch (.scalar p r pt isSl)))
      (layoutOf arch (.scalar p r pt isSl))
    let mdIr := emitLlvmArgAttrs arch optLevel
      (computePassMode arch cc optLevel isReturn (layoutOf arch (.manuallyDrop (.scalar p r pt isSl))))
      (layoutOf arch (.manuallyDrop (.scalar p r pt isSl)))
    mdIr.carrier = bareIr.carrier ∧
    mdIr.passedDirect = bareIr.passedDirect ∧
    mdIr.noUndef = bareIr.noUndef ∧
    mdIr.zeroExt = bareIr.zeroExt ∧
    mdIr.signExt = bareIr.signExt ∧
    mdIr.nonNull = bareIr.nonNull ∧
    mdIr.rangeAttr = bareIr.rangeAttr ∧
    mdIr.alignAttr = bareIr.alignAttr ∧
    mdIr.dereferenceableAttr = none ∧
    mdIr.noAliasAttr = false ∧
    mdIr.readOnlyAttr = false := by
  intro bareIr mdIr
  have hmask := computeArgAttrs_maskForMaybeDangling cc optLevel isReturn (.initialized p r) pt
  rcases hmask with ⟨hnu, hnn, hext, hal, hps, hna, hro⟩
  dsimp only [bareIr, mdIr, layoutOf, applyMaybeDanglingToLayout, computePassMode, emitLlvmArgAttrs]
  rw [hnu, hnn, hext, hal, hps, hna, hro]
  cases optLevel <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Theorem 2: `MaybeUninit` Union Attribute-Erasure Soundness & Necessity -/

theorem maybeUninit_strips_attributes_preserves_direct_scalar (arch : TargetArch)
    (cc : CallingConv) (optLevel isReturn : Bool)
    (p : PrimitiveTy) (r : WrappingRange) (pt : Option PointeeFacts) (isSl : Bool) :
    let muLay := layoutOf arch (.maybeUninitUnion (.scalar p r pt isSl))
    let muPm := computePassMode arch cc optLevel isReturn muLay
    let muIr := emitLlvmArgAttrs arch optLevel muPm muLay
    muIr.carrier = scalarToLlvmCarrier p ∧
    muIr.passedDirect = true ∧
    muIr.noUndef = false ∧
    muIr.nonNull = false ∧
    muIr.rangeAttr = none ∧
    muIr.alignAttr = none ∧
    muIr.dereferenceableAttr = none ∧
    muIr.noAliasAttr = false ∧
    muIr.readOnlyAttr = false := by
  intro muLay muPm muIr
  dsimp only [muLay, muPm, muIr, layoutOf, applyMaybeUninitUnionToLayout,
    BackendRepr.toUnion, AbiScalar.toUnion, AbiScalar.primitive,
    computePassMode, computeArgAttrs, emitLlvmArgAttrs, applyRangeAttr,
    AbiScalar.isUninitValid, AbiScalar.isAlwaysValid, AbiScalar.isBool,
    PrimitiveTy.isInt]
  cases p <;> cases cc <;> cases optLevel <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Theorem 2a (Soundness of `MaybeUninit<T>` Attribute Erasure):**
For any inner integer scalar `T` with width `≥ 32`, `MaybeUninit<T>`'s emitted
LLVM parameter attributes (`noundef = false`, `rangeAttr = none`, `nonNull = false`,
`alignAttr = none`, `dereferenceableAttr = none`) are 100% sound for ALL
`RuntimeScalar` values, including `.uninit`, `.bits 0`, and arbitrary integers. -/
theorem maybeUninit_int_or_ptr_sound_for_all_values (arch : TargetArch)
    (cc : CallingConv) (optLevel isReturn : Bool)
    (w : IntWidth) (signed : Bool) (r : WrappingRange) (pt : Option PointeeFacts) (isSl : Bool)
    (hge32 : 32 ≤ w.bits) :
    let ty := AbiTy.maybeUninitUnion (.scalar (.int w signed) r pt isSl)
    let lay := layoutOf arch ty
    let ir := emitLlvmArgAttrs arch optLevel (computePassMode arch cc optLevel isReturn lay) lay
    AbiAttrSound arch ty ir := by
  intro ty lay ir v _
  dsimp only [ir, lay, ty, layoutOf, applyMaybeUninitUnionToLayout, BackendRepr.toUnion,
    AbiScalar.toUnion, AbiScalar.primitive, computePassMode, computeArgAttrs,
    emitLlvmArgAttrs, applyRangeAttr, AbiScalar.isUninitValid, AbiScalar.isAlwaysValid,
    AbiScalar.isBool, PrimitiveTy.isInt]
  have hblt : Nat.blt w.bits 32 = false := nat_blt_false_of_le hge32
  apply llvmAttrSatisfied_of_cleared
  · cases optLevel <;> cases cc <;> rfl
  · cases cc with
    | externC =>
      dsimp only
      rw [hblt]
      cases signed <;> cases isReturn <;> rfl
    | externRust => rfl
  · cases optLevel <;> cases cc <;> rfl
  · cases optLevel <;> rfl
  · cases cc <;> rfl
  · cases optLevel <;> cases cc <;> rfl

theorem maybeUninit_pointer_sound_for_all_values (arch : TargetArch)
    (cc : CallingConv) (optLevel isReturn : Bool)
    (r : WrappingRange) (pt : Option PointeeFacts) (isSl : Bool) :
    let ty := AbiTy.maybeUninitUnion (.scalar .pointer r pt isSl)
    let lay := layoutOf arch ty
    let ir := emitLlvmArgAttrs arch optLevel (computePassMode arch cc optLevel isReturn lay) lay
    AbiAttrSound arch ty ir := by
  intro ty lay ir v _
  dsimp only [ir, lay, ty, layoutOf, applyMaybeUninitUnionToLayout, BackendRepr.toUnion,
    AbiScalar.toUnion, AbiScalar.primitive, computePassMode, computeArgAttrs,
    emitLlvmArgAttrs, applyRangeAttr, AbiScalar.isUninitValid, AbiScalar.isAlwaysValid,
    AbiScalar.isBool, PrimitiveTy.isInt]
  apply llvmAttrSatisfied_of_cleared
  · cases optLevel <;> cases cc <;> rfl
  · cases cc <;> rfl
  · cases optLevel <;> cases cc <;> rfl
  · cases optLevel <;> rfl
  · cases cc <;> rfl
  · cases optLevel <;> cases cc <;> rfl

/-- **Theorem 2b (Necessity — Negative Countermodels):**
If a buggy compiler failed to call `to_union()` on `MaybeUninit<NonZeroU32>`
and retained EITHER `noUndef = true` OR `rangeAttr = some (nonZero ...)` while
passing Rust-valid `MaybeUninit<NonZeroU32>` values (`.uninit` or `.bits 0`),
`llvmAttrSatisfied` is provably FALSE (immediate LLVM UB)! -/
theorem maybeUninit_retaining_noundef_is_unsound (arch : TargetArch) (ir : LlvmParamIR)
    (hnoUndef : ir.noUndef = true) :
    ¬ AbiAttrSound arch (.maybeUninitUnion (.scalar (.int .i32 false)
      (WrappingRange.nonZero (IntWidth.modulus .i32)) none false)) ir := by
  intro hsound
  have hvalid : rustValidVal arch (.maybeUninitUnion (.scalar (.int .i32 false)
      (WrappingRange.nonZero (IntWidth.modulus .i32)) none false)) .uninit := trivial
  have hsat := hsound .uninit hvalid
  exact (hsat.1 hnoUndef) rfl

theorem maybeUninit_retaining_range_is_unsound (arch : TargetArch) (ir : LlvmParamIR)
    (hcarr : ir.carrier = .intBits 32)
    (hrange : ir.rangeAttr = some (WrappingRange.nonZero (IntWidth.modulus .i32))) :
    ¬ AbiAttrSound arch (.maybeUninitUnion (.scalar (.int .i32 false)
      (WrappingRange.nonZero (IntWidth.modulus .i32)) none false)) ir := by
  intro hsound
  have hvalid : rustValidVal arch (.maybeUninitUnion (.scalar (.int .i32 false)
      (WrappingRange.nonZero (IntWidth.modulus .i32)) none false)) (.bits 0) := trivial
  have hsat := hsound (.bits 0) hvalid
  have hr := hsat.2.2.1
  rw [hrange, hcarr] at hr
  rcases hr with ⟨n, hnEq, hcontains⟩
  injection hnEq with heq
  subst heq
  exact WrappingRange.nonZero_excludes_zero (IntWidth.modulus .i32) (IntWidth.modulus_gt_one .i32) hcontains

/-! ### Theorem 3: `#[repr(C, packed)]` `Unalign<T>` Conservative Stripping & Divergence -/

noncomputable def tyU32 : AbiTy :=
  .scalar (.int .i32 false) (WrappingRange.full (IntWidth.modulus .i32)) none false

noncomputable def tyNonZeroU32 : AbiTy :=
  .scalar (.int .i32 false) (WrappingRange.nonZero (IntWidth.modulus .i32)) none false

noncomputable def tyNonZeroI32 : AbiTy :=
  .scalar (.int .i32 true) (WrappingRange.nonZero (IntWidth.modulus .i32)) none false

noncomputable def tyNonZeroU8 : AbiTy :=
  .scalar (.int .i8 false) (WrappingRange.nonZero (IntWidth.modulus .i8)) none false

noncomputable def tyBool : AbiTy :=
  .scalar .bool WrappingRange.boolRange none false

noncomputable def tySharedRefU32 : AbiTy :=
  .scalar .pointer (WrappingRange.nonZero (IntWidth.modulus .i64))
    (some { isSafeRef := true, frozen := true, derefBytes := 4, alignBytes := 4 }) false

noncomputable def tyWrapU32 : AbiTy :=
  .transparentStruct [.phantomZst 1] tyU32 [.unit]

noncomputable def tyWrapNz : AbiTy :=
  .transparentStruct [.phantomZst 8] tyNonZeroU32 [.unit]

noncomputable def tyWrapNzI32 : AbiTy :=
  .transparentStruct [.phantomZst 1] tyNonZeroI32 []

noncomputable def tyWrapNzNested : AbiTy :=
  .transparentStruct [.unit] tyWrapNz [.phantomZst 1]

noncomputable def tyWrapBool : AbiTy :=
  .transparentStruct [.unit] tyBool [.phantomZst 1]

noncomputable def tyWrapRefU32 : AbiTy :=
  .transparentStruct [] tySharedRefU32 [.phantomZst 1]

noncomputable def tyManuallyDropNz : AbiTy := .manuallyDrop tyNonZeroU32
noncomputable def tyManuallyDropRef : AbiTy := .manuallyDrop tySharedRefU32
noncomputable def tyMaybeUninitNz : AbiTy := .maybeUninitUnion tyNonZeroU32
noncomputable def tyMaybeUninitRef : AbiTy := .maybeUninitUnion tySharedRefU32
noncomputable def tyReadOnlyU32 : AbiTy := .readOnly tyU32
noncomputable def tyReadOnlyNz : AbiTy := .readOnly tyNonZeroU32
noncomputable def tyReadOnlyRef : AbiTy := .readOnly tySharedRefU32
noncomputable def tyUnalignU32 : AbiTy := .unalign tyU32
noncomputable def tyUnalignNz : AbiTy := .unalign tyNonZeroU32
noncomputable def tyUnalignNzU8 : AbiTy := .unalign tyNonZeroU8
noncomputable def tyUnalignRef : AbiTy := .unalign tySharedRefU32
noncomputable def tyReprCNz : AbiTy := .cStruct none [tyNonZeroU32]

/-- **Theorem 3a (`zerocopy::ReadOnly<T>` vs. `zerocopy::Unalign<T>` Divergence on `x86_64`):**
For `NonZeroU32` on `x86_64` `extern "C"` at `-O2`:
- `ReadOnly<NonZeroU32>` lowers via `PassMode.direct`, emitting `i32`, `noundef = true`,
  and `range(i32 1, 0)`.
- `Unalign<NonZeroU32>` lowers via `PassMode.cast 4`, emitting bare `i32` with
  `noundef = false` and `rangeAttr = none`, and forces alignment `1`. -/
theorem readonly_vs_unalign_x86_64_divergence :
    let roLay := layoutOf .x86_64 tyReadOnlyNz
    let uaLay := layoutOf .x86_64 tyUnalignNz
    let roPm := computePassMode .x86_64 .externC true false roLay
    let uaPm := computePassMode .x86_64 .externC true false uaLay
    let roIr := emitLlvmArgAttrs .x86_64 true roPm roLay
    let uaIr := emitLlvmArgAttrs .x86_64 true uaPm uaLay
    roLay.align = 4 ∧
    uaLay.align = 1 ∧
    roPm.sameVariantKind uaPm = false ∧
    roIr.passedDirect = true ∧
    roIr.noUndef = true ∧
    roIr.rangeAttr = some (WrappingRange.nonZero (IntWidth.modulus .i32)) ∧
    uaIr.passedByCast = true ∧
    uaIr.noUndef = false ∧
    uaIr.rangeAttr = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Theorem 3b (`extern "Rust"` vs. `extern "C"` on `Unalign<NonZeroU32>`):**
Under `extern "Rust"`, `adjust_for_rust_abi` casts 4-byte `BackendRepr::Memory`
to `Reg::i32()` WITH `NoUndef` (`i32 noundef`, matching `@zc_readonly_u32` alias!),
yet STILL drops `range(i32 1, 0)` because `apply_range_attr` never inspects `PassMode::Cast`.
Under `extern "C"`, `x86_64::compute_abi_info` drops BOTH `noundef` AND `range`. -/
theorem externRust_vs_externC_unalign_nz :
    let uaLay := layoutOf .x86_64 tyUnalignNz
    let rustIr := emitLlvmArgAttrs .x86_64 true
      (computePassMode .x86_64 .externRust true false uaLay) uaLay
    let cIr := emitLlvmArgAttrs .x86_64 true
      (computePassMode .x86_64 .externC true false uaLay) uaLay
    rustIr.passedByCast = true ∧ rustIr.noUndef = true ∧ rustIr.rangeAttr = none ∧
    cIr.passedByCast = true ∧ cIr.noUndef = false ∧ cIr.rangeAttr = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Theorem 3c (Even 1-Aligned `Unalign<NonZeroU8>` Still Strips Attributes):**
Because `#[repr(C, packed)]` sets `ReprFlags::IS_C` (`inhibitNewtypeAbiOpt = true`),
even `Unalign<NonZeroU8>` (whose inner alignment is already `1`) is blocked from
`BackendRepr.scalar` forwarding and emits bare `i8` with `noundef = false` and
`rangeAttr = none`. -/
theorem unalign_u8_inhibit_newtype_abi :
    let u8Lay := layoutOf .x86_64 tyUnalignNzU8
    let u8Ir := emitLlvmArgAttrs .x86_64 true
      (computePassMode .x86_64 .externC true false u8Lay) u8Lay
    u8Lay.size = 1 ∧
    u8Lay.align = 1 ∧
    u8Lay.repr = .memory 1 1 true ∧
    u8Ir.passedByCast = true ∧
    u8Ir.noUndef = false ∧
    u8Ir.rangeAttr = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Theorem 3d (`Unalign<NonZeroU32>` Cross-Target ABI Divergence on i686 & AArch64):**
- On `i686` (`extern "C"`), `ReadOnly<NonZeroU32>` stays `PassMode.direct` (`i32 noundef range`),
  whereas `Unalign<NonZeroU32>` diverges into `PassMode.indirect` (`sret` on return / `byval` on arg)!
- On `aarch64` (`extern "C"`), `Unalign<NonZeroU32>` widens into a 64-bit cast `i64`
  without `noundef` or `range(1, 0)`. -/
theorem readonly_vs_unalign_cross_target_divergence :
    let roI686Arg := computePassMode .i686 .externC true false (layoutOf .i686 tyReadOnlyNz)
    let uaI686Arg := computePassMode .i686 .externC true false (layoutOf .i686 tyUnalignNz)
    let uaI686Ret := computePassMode .i686 .externC true true (layoutOf .i686 tyUnalignNz)
    let uaA64Ir := emitLlvmArgAttrs .aarch64 true
      (computePassMode .aarch64 .externC true false (layoutOf .aarch64 tyUnalignNz))
      (layoutOf .aarch64 tyUnalignNz)
    roI686Arg.sameVariantKind uaI686Arg = false ∧
    (emitLlvmArgAttrs .i686 true uaI686Arg (layoutOf .i686 tyUnalignNz)).passedIndirect = true ∧
    (emitLlvmArgAttrs .i686 true uaI686Ret (layoutOf .i686 tyUnalignNz)).passedIndirect = true ∧
    uaA64Ir.passedByCast = true ∧
    uaA64Ir.carrier = .intBits 64 ∧
    uaA64Ir.noUndef = false ∧
    uaA64Ir.rangeAttr = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Theorem 3e (Conservative Stripping Soundness for `Unalign<T>` & `#[repr(C)]`):**
Omitting `noundef`, `range`, `nonnull`, `align`, and `dereferenceable` on `Unalign<T>`
on `x86_64` / `aarch64` `extern "C"` soundly over-approximates all Rust-valid values. -/
theorem unalign_conservative_stripping_sound (arch : TargetArch) (optLevel isReturn : Bool)
    (inner : AbiTy) (harch : arch = .x86_64 ∨ arch = .aarch64)
    (hszPos : 0 < (layoutOf arch inner).size)
    (hszLe : (layoutOf arch inner).size ≤ 16) :
    let ty := AbiTy.unalign inner
    let lay := layoutOf arch ty
    let ir := emitLlvmArgAttrs arch optLevel (computePassMode arch .externC optLevel isReturn lay) lay
    AbiAttrSound arch ty ir := by
  intro ty lay ir v _
  have hbeq : Nat.beq (layoutOf arch inner).size 0 = false := nat_beq_zero_false_of_pos hszPos
  have hle : Nat.ble (layoutOf arch inner).size 16 = true := Nat.ble_eq_true_of_le hszLe
  have hlay : lay = { size := (layoutOf arch inner).size
                      align := 1
                      unadjustedAbiAlign := 1
                      repr := .memory (layoutOf arch inner).size 1 true
                      pointee := none
                      hasSliceRefRangeBypass := false
                      allFieldsNoUndef := (layoutOf arch inner).allFieldsNoUndef } := by
    dsimp only [lay, ty, layoutOf, applyUnalignToLayout]
    rw [hbeq]
    rfl
  dsimp only [ir]
  cases harch with
  | inl hx =>
    subst hx
    have hpm : computePassMode .x86_64 .externC optLevel isReturn lay =
        .cast (layoutOf .x86_64 inner).size ArgAttributes.empty := by
      rw [hlay]
      dsimp only [computePassMode]
      rw [hle]
      rfl
    rw [hpm]
    apply llvmAttrSatisfied_of_cleared
    · cases optLevel <;> rfl
    · rfl
    · cases optLevel <;> rfl
    · rfl
    · rfl
    · rfl
  | inr ha =>
    subst ha
    have hpm : computePassMode .aarch64 .externC optLevel isReturn lay =
        .cast (layoutOf .aarch64 inner).size ArgAttributes.empty := by
      rw [hlay]
      dsimp only [computePassMode]
      rw [hle]
      rfl
    rw [hpm]
    apply llvmAttrSatisfied_of_cleared
    · cases optLevel <;> rfl
    · rfl
    · cases optLevel <;> rfl
    · rfl
    · rfl
    · rfl

/-- Soundness of emitted LLVM attributes on primitive scalars (`NonZeroU32`,
`NonZeroI32`, `u32`, `bool`, `&u32`), and by Theorem 1 on all `#[repr(transparent)]`
wrappers (`WrapNz`, `WrapBool`, `WrapRef`, `ReadOnly`). -/
theorem scalar_llvm_attrs_sound (arch : TargetArch) (cc : CallingConv)
    (optLevel isReturn : Bool) (p : PrimitiveTy) (r : WrappingRange)
    (pt : Option PointeeFacts) (isSl : Bool) :
    let ty := AbiTy.scalar p r pt isSl
    let lay := layoutOf arch ty
    let ir := emitLlvmArgAttrs arch optLevel (computePassMode arch cc optLevel isReturn lay) lay
    AbiAttrSound arch ty ir := by
  intro ty lay ir v hvalid
  cases p with
  | bool =>
    dsimp only [ty, rustValidVal, rustValidScalar] at hvalid
    cases v with
    | uninit => exact False.elim hvalid
    | ptr _ _ _ _ => exact False.elim hvalid
    | bits b =>
      have hcarr : ir.carrier = .i1 := by cases cc <;> rfl
      have hrng : ir.rangeAttr = none := by cases cc <;> cases optLevel <;> rfl
      have hnn : ir.nonNull = false := by cases cc <;> cases optLevel <;> rfl
      have hal : ir.alignAttr = none := by cases cc <;> rfl
      have hderef : ir.dereferenceableAttr = none := by cases cc <;> cases optLevel <;> rfl
      unfold llvmAttrSatisfied
      rw [hcarr, hrng, hnn, hal, hderef]
      refine ⟨fun _ hcontra => RuntimeScalar.noConfusion hcontra, fun _ => ⟨b, rfl, hvalid⟩,
        trivial, fun hcontra => False.elim (Bool.false_ne_true hcontra), trivial, trivial⟩
  | int w s =>
    dsimp only [ty, rustValidVal, rustValidScalar] at hvalid
    cases v with
    | uninit => exact False.elim hvalid
    | ptr _ _ _ _ => exact False.elim hvalid
    | bits n =>
      have hcarr : ir.carrier = .intBits w.bits := by cases cc <;> rfl
      have hnn : ir.nonNull = false := by cases cc <;> cases optLevel <;> rfl
      have hal : ir.alignAttr = none := by cases cc <;> rfl
      have hderef : ir.dereferenceableAttr = none := by cases cc <;> cases optLevel <;> rfl
      unfold llvmAttrSatisfied
      rw [hcarr, hnn, hal, hderef]
      cases optLevel
      · have hrng : ir.rangeAttr = none := by cases cc <;> rfl
        rw [hrng]
        exact ⟨fun _ hcontra => RuntimeScalar.noConfusion hcontra, fun _ => ⟨n, rfl⟩, trivial,
          fun hcontra => False.elim (Bool.false_ne_true hcontra), trivial, trivial⟩
      · have hrng : ir.rangeAttr = if !(r.isFull w.modulus) then some r else none := by
          cases cc <;> rfl
        rw [hrng]
        cases hfull : r.isFull w.modulus
        · refine ⟨fun _ hcontra => RuntimeScalar.noConfusion hcontra, fun _ => ⟨n, rfl⟩, ?_,
            fun hcontra => False.elim (Bool.false_ne_true hcontra), trivial, trivial⟩
          exact ⟨n, rfl, hvalid⟩
        · exact ⟨fun _ hcontra => RuntimeScalar.noConfusion hcontra, fun _ => ⟨n, rfl⟩, trivial,
            fun hcontra => False.elim (Bool.false_ne_true hcontra), trivial, trivial⟩
  | pointer =>
    dsimp only [ty, rustValidVal, rustValidScalar] at hvalid
    cases v with
    | uninit => exact False.elim hvalid
    | bits _ => exact False.elim hvalid
    | ptr addr pv ab aa =>
      rcases hvalid with ⟨hcontain, hpt⟩
      have hcarr : ir.carrier = .ptr := by cases cc <;> rfl
      have hze : ir.zeroExt = false := by cases cc <;> cases pt <;> rfl
      have hrng : ir.rangeAttr = none := by cases cc <;> cases optLevel <;> rfl
      have hnnEq : ir.nonNull = (optLevel && r.excludesZero) := by cases cc <;> cases pt <;> rfl
      unfold llvmAttrSatisfied
      rw [hcarr, hze, hrng, hnnEq]
      cases pt with
      | none =>
        have hal : ir.alignAttr = none := by cases cc <;> rfl
        have hderef : ir.dereferenceableAttr = none := by cases cc <;> cases optLevel <;> rfl
        rw [hal, hderef]
        refine ⟨fun _ hcontra => RuntimeScalar.noConfusion hcontra,
          fun hext => False.elim (Bool.false_ne_true hext), trivial, ?_, trivial, trivial⟩
        intro hnn
        cases optLevel
        · exact False.elim (Bool.false_ne_true hnn)
        · refine ⟨addr, pv, ab, aa, rfl, ?_⟩
          intro haz
          subst haz
          exact WrappingRange.excludesZero_sound ((PrimitiveTy.pointer).modulus arch) r hnn hcontain
      | some info =>
        rcases hpt with ⟨halFact, hsafeFact⟩
        have halEq : ir.alignAttr = if Nat.blt 1 info.alignBytes then some info.alignBytes else none := by
          cases cc <;> rfl
        have hderefEq : ir.dereferenceableAttr =
            if optLevel && Nat.blt 0 (if optLevel && !isReturn && info.isSafeRef && info.frozen then info.derefBytes else 0) then
              some (if optLevel && !isReturn && info.isSafeRef && info.frozen then info.derefBytes else 0)
            else none := by
          cases cc <;> rfl
        rw [halEq, hderefEq]
        refine ⟨fun _ hcontra => RuntimeScalar.noConfusion hcontra,
          fun hext => False.elim (Bool.false_ne_true hext), trivial, ?_, ?_, ?_⟩
        · intro hnn
          cases optLevel
          · exact False.elim (Bool.false_ne_true hnn)
          · refine ⟨addr, pv, ab, aa, rfl, ?_⟩
            intro haz
            subst haz
            exact WrappingRange.excludesZero_sound ((PrimitiveTy.pointer).modulus arch) r hnn hcontain
        · cases hblt : Nat.blt 1 info.alignBytes
          · trivial
          · exact ⟨addr, pv, ab, aa, rfl, halFact⟩
        · cases optLevel
          · trivial
          · cases isReturn
            · cases hsr : info.isSafeRef
              · trivial
              · cases hfr : info.frozen
                · trivial
                · have hif : (if (true && !false && true && true) = true then info.derefBytes else 0) =
                      info.derefBytes := rfl
                  rw [hif]
                  cases hps : Nat.blt 0 info.derefBytes
                  · trivial
                  · rw [hsr] at hsafeFact
                    have hs : pv = true ∧ info.derefBytes ≤ ab ∧ info.alignBytes ≤ aa := hsafeFact
                    exact ⟨addr, pv, ab, aa, rfl, hs.1, hs.2.1⟩
            · trivial
  | float32 =>
    dsimp only [ty, rustValidVal, rustValidScalar] at hvalid
    cases v with
    | uninit => exact False.elim hvalid
    | ptr _ _ _ _ => exact False.elim hvalid
    | bits _ =>
      have hcarr : ir.carrier = .intBits 32 := by cases cc <;> rfl
      have hze : ir.zeroExt = false := by cases cc <;> rfl
      have hrng : ir.rangeAttr = none := by cases cc <;> cases optLevel <;> rfl
      have hnn : ir.nonNull = false := by cases cc <;> cases optLevel <;> rfl
      have hal : ir.alignAttr = none := by cases cc <;> rfl
      have hderef : ir.dereferenceableAttr = none := by cases cc <;> cases optLevel <;> rfl
      unfold llvmAttrSatisfied
      rw [hcarr, hze, hrng, hnn, hal, hderef]
      exact ⟨fun _ hcontra => RuntimeScalar.noConfusion hcontra,
        fun hext => False.elim (Bool.false_ne_true hext), trivial,
        fun hcontra => False.elim (Bool.false_ne_true hcontra), trivial, trivial⟩
  | float64 =>
    dsimp only [ty, rustValidVal, rustValidScalar] at hvalid
    cases v with
    | uninit => exact False.elim hvalid
    | ptr _ _ _ _ => exact False.elim hvalid
    | bits _ =>
      have hcarr : ir.carrier = .intBits 64 := by cases cc <;> rfl
      have hze : ir.zeroExt = false := by cases cc <;> rfl
      have hrng : ir.rangeAttr = none := by cases cc <;> cases optLevel <;> rfl
      have hnn : ir.nonNull = false := by cases cc <;> cases optLevel <;> rfl
      have hal : ir.alignAttr = none := by cases cc <;> rfl
      have hderef : ir.dereferenceableAttr = none := by cases cc <;> cases optLevel <;> rfl
      unfold llvmAttrSatisfied
      rw [hcarr, hze, hrng, hnn, hal, hderef]
      exact ⟨fun _ hcontra => RuntimeScalar.noConfusion hcontra,
        fun hext => False.elim (Bool.false_ne_true hext), trivial,
        fun hcontra => False.elim (Bool.false_ne_true hcontra), trivial, trivial⟩

theorem transparent_preserves_soundness (arch : TargetArch) (zpre zsuf : List AbiTy)
    (inner : AbiTy) (ir : LlvmParamIR)
    (hsound : AbiAttrSound arch inner ir) :
    AbiAttrSound arch (.transparentStruct zpre inner zsuf) ir := by
  intro v hvalid
  exact hsound v hvalid

theorem readOnly_preserves_soundness (arch : TargetArch) (inner : AbiTy) (ir : LlvmParamIR)
    (hsound : AbiAttrSound arch inner ir) :
    AbiAttrSound arch (.readOnly inner) ir := by
  intro v hvalid
  exact hsound v hvalid

/-! ### Theorem 4: FFI Cross-Language Substitution & Observational Interchangeability -/

noncomputable def FfiBoundaryCompatible (arch : TargetArch) (cc : CallingConv)
    (optLevel : Bool) (calleeTy callerTy : AbiTy) : Prop :=
  let calleeLay := layoutOf arch calleeTy
  let callerLay := layoutOf arch callerTy
  let calleeArgPm := computePassMode arch cc optLevel false calleeLay
  let callerArgPm := computePassMode arch cc optLevel false callerLay
  let calleeRetPm := computePassMode arch cc optLevel true calleeLay
  let callerRetPm := computePassMode arch cc optLevel true callerLay
  calleeArgPm.sameVariantKind callerArgPm = true ∧
  calleeRetPm.sameVariantKind callerRetPm = true ∧
  emitLlvmArgAttrs arch optLevel calleeArgPm calleeLay =
    emitLlvmArgAttrs arch optLevel callerArgPm callerLay ∧
  emitLlvmArgAttrs arch optLevel calleeRetPm calleeLay =
    emitLlvmArgAttrs arch optLevel callerRetPm callerLay ∧
  (∀ v, rustValidVal arch callerTy v ↔ rustValidVal arch calleeTy v)

theorem ffiBoundaryCompatible_refl (arch : TargetArch) (cc : CallingConv)
    (optLevel : Bool) (ty : AbiTy) :
    FfiBoundaryCompatible arch cc optLevel ty ty := by
  unfold FfiBoundaryCompatible
  exact ⟨PassMode.sameVariantKind_refl _, PassMode.sameVariantKind_refl _,
    rfl, rfl, fun _ => Iff.rfl⟩

theorem ffiBoundaryCompatible_symm (arch : TargetArch) (cc : CallingConv)
    (optLevel : Bool) (t1 t2 : AbiTy)
    (h : FfiBoundaryCompatible arch cc optLevel t1 t2) :
    FfiBoundaryCompatible arch cc optLevel t2 t1 := by
  unfold FfiBoundaryCompatible at h ⊢
  rcases h with ⟨harg, hret, hirA, hirR, hiff⟩
  exact ⟨PassMode.sameVariantKind_symm _ _ harg,
    PassMode.sameVariantKind_symm _ _ hret,
    hirA.symm, hirR.symm, fun v => (hiff v).symm⟩

/-- **Theorem 4a (General `#[repr(transparent)]` FFI Substitution Theorem):**
Any `#[repr(transparent)]` wrapper `transparentStruct zpre inner zsuf` (such as
`WrapNz` around `NonZeroU32`, `WrapBool` around `bool`, `WrapRef` around `&u32`,
or `zerocopy::ReadOnly<T>` around `T`) is bi-directionally observationally
interchangeable with `inner` across `extern "C"` call boundaries on every target! -/
theorem ffi_transparent_substitution_interchangeable (arch : TargetArch)
    (optLevel : Bool) (zpre zsuf : List AbiTy) (inner : AbiTy) :
    FfiBoundaryCompatible arch .externC optLevel (.transparentStruct zpre inner zsuf) inner ∧
    FfiBoundaryCompatible arch .externC optLevel inner (.transparentStruct zpre inner zsuf) := by
  have hfwd : FfiBoundaryCompatible arch .externC optLevel (.transparentStruct zpre inner zsuf) inner := by
    unfold FfiBoundaryCompatible
    dsimp only
    refine ⟨?_, ?_,
      reprTransparent_llvm_ir_eq_externC arch optLevel false zpre zsuf inner,
      reprTransparent_llvm_ir_eq_externC arch optLevel true zpre zsuf inner,
      fun _ => Iff.rfl⟩
    · rw [reprTransparent_passMode_eq]
      exact PassMode.sameVariantKind_refl _
    · rw [reprTransparent_passMode_eq]
      exact PassMode.sameVariantKind_refl _
  exact ⟨hfwd, ffiBoundaryCompatible_symm arch .externC optLevel _ _ hfwd⟩

theorem ffi_readOnly_substitution_interchangeable (arch : TargetArch)
    (optLevel : Bool) (inner : AbiTy) :
    FfiBoundaryCompatible arch .externC optLevel (.readOnly inner) inner ∧
    FfiBoundaryCompatible arch .externC optLevel inner (.readOnly inner) := by
  have hfwd : FfiBoundaryCompatible arch .externC optLevel (.readOnly inner) inner := by
    unfold FfiBoundaryCompatible
    dsimp only
    have harg := readOnly_exact_abi_attr_isomorphism arch optLevel false inner
    have hret := readOnly_exact_abi_attr_isomorphism arch optLevel true inner
    refine ⟨?_, ?_, harg.2, hret.2, fun _ => Iff.rfl⟩
    · rw [harg.1]
      exact PassMode.sameVariantKind_refl _
    · rw [hret.1]
      exact PassMode.sameVariantKind_refl _
  exact ⟨hfwd, ffiBoundaryCompatible_symm arch .externC optLevel _ _ hfwd⟩

/-- **Theorem 4b (`ManuallyDrop<NonZeroU32>` <-> `NonZeroU32` FFI Substitution):**
For non-reference scalars like `NonZeroU32`, `ManuallyDrop<NonZeroU32>` is
bi-directionally FFI-compatible with `NonZeroU32` across `extern "C"`! -/
theorem ffi_manuallyDrop_nonzero_interchangeable (arch : TargetArch) (optLevel : Bool) :
    FfiBoundaryCompatible arch .externC optLevel tyManuallyDropNz tyNonZeroU32 ∧
    FfiBoundaryCompatible arch .externC optLevel tyNonZeroU32 tyManuallyDropNz := by
  have hfwd : FfiBoundaryCompatible arch .externC optLevel tyManuallyDropNz tyNonZeroU32 := by
    unfold FfiBoundaryCompatible
    refine ⟨rfl, rfl, ?_, ?_, fun _ => Iff.rfl⟩
    · unfold tyManuallyDropNz tyNonZeroU32 layoutOf applyMaybeDanglingToLayout
        computePassMode computeArgAttrs emitLlvmArgAttrs applyRangeAttr
      rfl
    · unfold tyManuallyDropNz tyNonZeroU32 layoutOf applyMaybeDanglingToLayout
        computePassMode computeArgAttrs emitLlvmArgAttrs applyRangeAttr
      rfl
  exact ⟨hfwd, ffiBoundaryCompatible_symm arch .externC optLevel _ _ hfwd⟩

/-- **Theorem 4c (Negative FFI Boundary Rejection — `MaybeUninit<NonZeroU32>`,
`Unalign<NonZeroU32>`, and `#[repr(C)] struct ReprCNz(NonZeroU32)`):**
All three non-equivalent wrappers are provably NOT FFI-compatible with `NonZeroU32`! -/
theorem ffi_maybeUninit_not_compatible_with_nonzero (arch : TargetArch) (optLevel : Bool) :
    ¬ FfiBoundaryCompatible arch .externC optLevel tyNonZeroU32 tyMaybeUninitNz := by
  intro hcompat
  unfold FfiBoundaryCompatible at hcompat
  have hiff := hcompat.2.2.2.2 (.bits 0)
  have hvalidMu : rustValidVal arch tyMaybeUninitNz (.bits 0) := trivial
  have hvalidNz : rustValidVal arch tyNonZeroU32 (.bits 0) := hiff.mp hvalidMu
  unfold tyNonZeroU32 rustValidVal rustValidScalar at hvalidNz
  exact WrappingRange.nonZero_excludes_zero (IntWidth.modulus .i32)
    (IntWidth.modulus_gt_one .i32) hvalidNz

theorem ffi_unalign_not_compatible_with_nonzero (arch : TargetArch) (optLevel : Bool) :
    ¬ FfiBoundaryCompatible arch .externC optLevel tyUnalignNz tyNonZeroU32 := by
  intro hcompat
  unfold FfiBoundaryCompatible at hcompat
  have hpm := hcompat.1
  unfold tyUnalignNz tyNonZeroU32 layoutOf applyUnalignToLayout computePassMode at hpm
  cases arch <;> exact Bool.false_ne_true hpm

theorem ffi_reprC_not_compatible_with_nonzero (arch : TargetArch) (optLevel : Bool) :
    ¬ FfiBoundaryCompatible arch .externC optLevel tyReprCNz tyNonZeroU32 := by
  intro hcompat
  unfold FfiBoundaryCompatible at hcompat
  have hpm := hcompat.1
  unfold tyReprCNz tyNonZeroU32 layoutOf foldCFields alignTo nonZstLayouts computePassMode at hpm
  cases arch <;> exact Bool.false_ne_true hpm

/-! ## Section 7: Concrete Instantiation Witnesses Matching Live `rustc` Probes -/

theorem witness_wrap_u32_eq_bare_u32_ir :
    let bareLay := layoutOf .x86_64 tyU32
    let wrapLay := layoutOf .x86_64 tyWrapU32
    emitLlvmArgAttrs .x86_64 true (computePassMode .x86_64 .externC true false wrapLay) wrapLay =
      emitLlvmArgAttrs .x86_64 true (computePassMode .x86_64 .externC true false bareLay) bareLay ∧
    (emitLlvmArgAttrs .x86_64 true (computePassMode .x86_64 .externC true false wrapLay) wrapLay).noUndef = true ∧
    (emitLlvmArgAttrs .x86_64 true (computePassMode .x86_64 .externC true false wrapLay) wrapLay).rangeAttr = none :=
  ⟨rfl, rfl, rfl⟩

theorem witness_wrap_nz_and_nested_eq_bare_nz_ir :
    let bareLay := layoutOf .x86_64 tyNonZeroU32
    let wrapLay := layoutOf .x86_64 tyWrapNz
    let nestLay := layoutOf .x86_64 tyWrapNzNested
    let nzi32Lay := layoutOf .x86_64 tyWrapNzI32
    emitLlvmArgAttrs .x86_64 true (computePassMode .x86_64 .externC true false wrapLay) wrapLay =
      emitLlvmArgAttrs .x86_64 true (computePassMode .x86_64 .externC true false bareLay) bareLay ∧
    emitLlvmArgAttrs .x86_64 true (computePassMode .x86_64 .externC true false nestLay) nestLay =
      emitLlvmArgAttrs .x86_64 true (computePassMode .x86_64 .externC true false bareLay) bareLay ∧
    emitLlvmArgAttrs .x86_64 true (computePassMode .x86_64 .externC true false nzi32Lay) nzi32Lay =
      emitLlvmArgAttrs .x86_64 true (computePassMode .x86_64 .externC true false bareLay) bareLay ∧
    (emitLlvmArgAttrs .x86_64 true (computePassMode .x86_64 .externC true false wrapLay) wrapLay).noUndef = true ∧
    (emitLlvmArgAttrs .x86_64 true (computePassMode .x86_64 .externC true false wrapLay) wrapLay).rangeAttr =
      some (WrappingRange.nonZero (IntWidth.modulus .i32)) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem witness_wrap_bool_zeroext_i1 :
    let wrapLay := layoutOf .x86_64 tyWrapBool
    let ir := emitLlvmArgAttrs .x86_64 true (computePassMode .x86_64 .externC true false wrapLay) wrapLay
    ir.carrier = .i1 ∧ ir.noUndef = true ∧ ir.zeroExt = true ∧ ir.rangeAttr = none :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem witness_wrap_ref_vs_manuallyDrop_vs_maybeUninit_ref :
    let wrapIr := emitLlvmArgAttrs .x86_64 true
      (computePassMode .x86_64 .externC true false (layoutOf .x86_64 tyWrapRefU32))
      (layoutOf .x86_64 tyWrapRefU32)
    let mdIr := emitLlvmArgAttrs .x86_64 true
      (computePassMode .x86_64 .externC true false (layoutOf .x86_64 tyManuallyDropRef))
      (layoutOf .x86_64 tyManuallyDropRef)
    let muIr := emitLlvmArgAttrs .x86_64 true
      (computePassMode .x86_64 .externC true false (layoutOf .x86_64 tyMaybeUninitRef))
      (layoutOf .x86_64 tyMaybeUninitRef)
    let uaIr := emitLlvmArgAttrs .x86_64 true
      (computePassMode .x86_64 .externC true false (layoutOf .x86_64 tyUnalignRef))
      (layoutOf .x86_64 tyUnalignRef)
    wrapIr.nonNull = true ∧ wrapIr.alignAttr = some 4 ∧
      wrapIr.dereferenceableAttr = some 4 ∧ wrapIr.noAliasAttr = true ∧ wrapIr.readOnlyAttr = true ∧
    mdIr.noUndef = true ∧ mdIr.nonNull = true ∧ mdIr.alignAttr = some 4 ∧
      mdIr.dereferenceableAttr = none ∧ mdIr.noAliasAttr = false ∧ mdIr.readOnlyAttr = false ∧
    muIr.noUndef = false ∧ muIr.nonNull = false ∧ muIr.alignAttr = none ∧
      muIr.dereferenceableAttr = none ∧ muIr.noAliasAttr = false ∧ muIr.readOnlyAttr = false ∧
    uaIr.passedByCast = true ∧ uaIr.noUndef = false ∧ uaIr.nonNull = false ∧
      uaIr.alignAttr = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem witness_o0_suppresses_opt_attrs_retains_abi_attrs :
    let nzIrO0 := emitLlvmArgAttrs .x86_64 false
      (computePassMode .x86_64 .externC false false (layoutOf .x86_64 tyWrapNz))
      (layoutOf .x86_64 tyWrapNz)
    let boolIrO0 := emitLlvmArgAttrs .x86_64 false
      (computePassMode .x86_64 .externC false false (layoutOf .x86_64 tyWrapBool))
      (layoutOf .x86_64 tyWrapBool)
    let refIrO0 := emitLlvmArgAttrs .x86_64 false
      (computePassMode .x86_64 .externC false false (layoutOf .x86_64 tyWrapRefU32))
      (layoutOf .x86_64 tyWrapRefU32)
    nzIrO0.noUndef = false ∧ nzIrO0.rangeAttr = none ∧
    boolIrO0.zeroExt = true ∧ boolIrO0.noUndef = false ∧
    refIrO0.alignAttr = some 4 ∧ refIrO0.noUndef = false ∧
    refIrO0.nonNull = false ∧ refIrO0.dereferenceableAttr = none ∧
    refIrO0.noAliasAttr = false ∧ refIrO0.readOnlyAttr = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem witness_transparent_rejects_align4_zst :
    all1Zst [.alignedZst 4] = false ∧ all1Zst [.phantomZst 1, .unit] = true :=
  ⟨rfl, rfl⟩

/-! ## Section 8: Lattice Order Over LLVM Attribute Strength & Monotonicity -/

noncomputable def LlvmParamIR.WeakerThan (ir1 ir2 : LlvmParamIR) : Prop :=
  ir1.carrier = ir2.carrier ∧
  (ir1.noUndef = true → ir2.noUndef = true) ∧
  (ir1.zeroExt = true → ir2.zeroExt = true) ∧
  (ir1.signExt = true → ir2.signExt = true) ∧
  (ir1.nonNull = true → ir2.nonNull = true) ∧
  (∀ r, ir1.rangeAttr = some r → ir2.rangeAttr = some r) ∧
  (∀ a, ir1.alignAttr = some a → ir2.alignAttr = some a) ∧
  (∀ d, ir1.dereferenceableAttr = some d → ir2.dereferenceableAttr = some d)

theorem LlvmParamIR.weakerThan_refl (ir : LlvmParamIR) : ir.WeakerThan ir :=
  ⟨rfl, fun h => h, fun h => h, fun h => h, fun h => h,
   fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem LlvmParamIR.weakerThan_trans (ir1 ir2 ir3 : LlvmParamIR)
    (h12 : ir1.WeakerThan ir2) (h23 : ir2.WeakerThan ir3) :
    ir1.WeakerThan ir3 := by
  rcases h12 with ⟨hc1, hnu1, hze1, hse1, hnn1, hr1, ha1, hd1⟩
  rcases h23 with ⟨hc2, hnu2, hze2, hse2, hnn2, hr2, ha2, hd2⟩
  refine ⟨hc1.trans hc2, fun h => hnu2 (hnu1 h), fun h => hze2 (hze1 h),
    fun h => hse2 (hse1 h), fun h => hnn2 (hnn1 h),
    fun r h => hr2 r (hr1 r h), fun a h => ha2 a (ha1 a h), fun d h => hd2 d (hd1 d h)⟩

theorem llvmAttrSatisfied_monotone_under_weaker (arch : TargetArch)
    (ir1 ir2 : LlvmParamIR) (hw : ir1.WeakerThan ir2) (v : RuntimeScalar)
    (hsat : llvmAttrSatisfied arch ir2 v) :
    llvmAttrSatisfied arch ir1 v := by
  rcases hw with ⟨hc, hnu, hze, _, hnn, hr, ha, hd⟩
  rcases hsat with ⟨snu, sze, sr, snn, sa, sd⟩
  refine ⟨fun h => snu (hnu h), ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h2 := sze (hze h)
    rw [← hc] at h2
    exact h2
  · cases h1r : ir1.rangeAttr with
    | none => trivial
    | some r =>
      have h2r := hr r h1r
      rw [h2r, ← hc] at sr
      exact sr
  · intro h
    have h2 := snn (hnn h)
    rw [← hc] at h2
    exact h2
  · cases h1a : ir1.alignAttr with
    | none => trivial
    | some al =>
      have h2a := ha al h1a
      rw [h2a, ← hc] at sa
      exact sa
  · cases h1d : ir1.dereferenceableAttr with
    | none => trivial
    | some sz =>
      have h2d := hd sz h1d
      rw [h2d, ← hc] at sd
      exact sd

/-- Exact ordering across wrapper families on `&u32`:
`MaybeUninit<&u32> ⊑ ManuallyDrop<&u32> ⊑ ReadOnly<&u32> = WrapRef<&u32> = &u32`. -/
theorem ref_wrapper_lattice_chain :
    let muIr := emitLlvmArgAttrs .x86_64 true
      (computePassMode .x86_64 .externC true false (layoutOf .x86_64 tyMaybeUninitRef))
      (layoutOf .x86_64 tyMaybeUninitRef)
    let mdIr := emitLlvmArgAttrs .x86_64 true
      (computePassMode .x86_64 .externC true false (layoutOf .x86_64 tyManuallyDropRef))
      (layoutOf .x86_64 tyManuallyDropRef)
    let roIr := emitLlvmArgAttrs .x86_64 true
      (computePassMode .x86_64 .externC true false (layoutOf .x86_64 tyReadOnlyRef))
      (layoutOf .x86_64 tyReadOnlyRef)
    let bareIr := emitLlvmArgAttrs .x86_64 true
      (computePassMode .x86_64 .externC true false (layoutOf .x86_64 tySharedRefU32))
      (layoutOf .x86_64 tySharedRefU32)
    muIr.WeakerThan mdIr ∧ mdIr.WeakerThan roIr ∧ roIr = bareIr := by
  refine ⟨?_, ?_, rfl⟩
  · refine ⟨rfl, fun h => False.elim (Bool.false_ne_true h),
      fun h => False.elim (Bool.false_ne_true h),
      fun h => False.elim (Bool.false_ne_true h),
      fun h => False.elim (Bool.false_ne_true h),
      fun r h => (by have h' : (none : Option WrappingRange) = some r := h; cases h'),
      fun a h => (by have h' : (none : Option Nat) = some a := h; cases h'),
      fun d h => (by have h' : (none : Option Nat) = some d := h; cases h')⟩
  · refine ⟨rfl, fun h => h, fun h => h, fun h => h, fun h => h,
      fun r h => (by have h' : (none : Option WrappingRange) = some r := h; cases h'),
      fun _ h => h,
      fun d h => (by have h' : (none : Option Nat) = some d := h; cases h')⟩

/-- Exact ordering across wrapper families on `NonZeroU32`:
`MaybeUninit<NonZeroU32> ⊑ ManuallyDrop<NonZeroU32> = ReadOnly<NonZeroU32> = WrapNz = NonZeroU32`. -/
theorem nonzero_wrapper_lattice_chain :
    let muIr := emitLlvmArgAttrs .x86_64 true
      (computePassMode .x86_64 .externC true false (layoutOf .x86_64 tyMaybeUninitNz))
      (layoutOf .x86_64 tyMaybeUninitNz)
    let mdIr := emitLlvmArgAttrs .x86_64 true
      (computePassMode .x86_64 .externC true false (layoutOf .x86_64 tyManuallyDropNz))
      (layoutOf .x86_64 tyManuallyDropNz)
    let roIr := emitLlvmArgAttrs .x86_64 true
      (computePassMode .x86_64 .externC true false (layoutOf .x86_64 tyReadOnlyNz))
      (layoutOf .x86_64 tyReadOnlyNz)
    let bareIr := emitLlvmArgAttrs .x86_64 true
      (computePassMode .x86_64 .externC true false (layoutOf .x86_64 tyNonZeroU32))
      (layoutOf .x86_64 tyNonZeroU32)
    muIr.WeakerThan mdIr ∧ mdIr = roIr ∧ roIr = bareIr := by
  refine ⟨?_, rfl, rfl⟩
  refine ⟨rfl, fun h => False.elim (Bool.false_ne_true h),
    fun h => False.elim (Bool.false_ne_true h),
    fun h => False.elim (Bool.false_ne_true h),
    fun h => False.elim (Bool.false_ne_true h),
    fun r h => (by have h' : (none : Option WrappingRange) = some r := h; cases h'),
    fun a h => (by have h' : (none : Option Nat) = some a := h; cases h'),
    fun d h => (by have h' : (none : Option Nat) = some d := h; cases h')⟩

/-- `-O0` attributes are always weaker than `-O2` attributes on scalar types:
`zeroext`/`sext` and `align` persist unconditionally at `-O0` (`rustc_codegen_llvm/src/abi.rs:66-73`),
whereas `noundef`, `nonnull`, `range(...)`, and `dereferenceable` live inside the
optimization gate (`rustc_codegen_llvm/src/abi.rs:41-47, 76-96, 466`) and vanish at `-O0`
(absent MemorySanitizer). -/
theorem computeArgAttrs_optLevel_preserves_abi_attrs (cc : CallingConv) (isReturn : Bool)
    (s : AbiScalar) (pt : Option PointeeFacts) :
    let a0 := computeArgAttrs cc false isReturn s pt
    let a2 := computeArgAttrs cc true isReturn s pt
    a0.noUndef = a2.noUndef ∧
    a0.nonNull = a2.nonNull ∧
    a0.ext = a2.ext ∧
    a0.pointeeAlign = a2.pointeeAlign := by
  cases s with
  | unionVal _ => cases cc <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | initialized p r =>
    cases p with
    | bool => exact ⟨rfl, rfl, rfl, rfl⟩
    | int _ _ => exact ⟨rfl, rfl, rfl, rfl⟩
    | float32 => exact ⟨rfl, rfl, rfl, rfl⟩
    | float64 => exact ⟨rfl, rfl, rfl, rfl⟩
    | pointer =>
      cases pt with
      | none => exact ⟨rfl, rfl, rfl, rfl⟩
      | some _ => exact ⟨rfl, rfl, rfl, rfl⟩

theorem opt_level_monotonicity (arch : TargetArch) (cc : CallingConv) (isReturn : Bool)
    (p : PrimitiveTy) (r : WrappingRange) (pt : Option PointeeFacts) (isSl : Bool) :
    let lay := layoutOf arch (.scalar p r pt isSl)
    (emitLlvmArgAttrs arch false (computePassMode arch cc false isReturn lay) lay).WeakerThan
      (emitLlvmArgAttrs arch true (computePassMode arch cc true isReturn lay) lay) := by
  intro lay
  have hshared := computeArgAttrs_optLevel_preserves_abi_attrs cc isReturn (.initialized p r) pt
  rcases hshared with ⟨_, _, hext, hal⟩
  dsimp only [lay, layoutOf, computePassMode, emitLlvmArgAttrs, applyRangeAttr]
  rw [hext, hal]
  refine ⟨rfl, ?_, fun h => h, fun h => h, ?_, ?_, fun _ h => h, ?_⟩
  · intro h
    exact False.elim (Bool.false_ne_true h)
  · intro h
    exact False.elim (Bool.false_ne_true h)
  · intro r h
    have h' : (none : Option WrappingRange) = some r := h
    cases h'
  · intro d h
    have h' : (none : Option Nat) = some d := h
    cases h'

end AbiReprTransparentSoundness
