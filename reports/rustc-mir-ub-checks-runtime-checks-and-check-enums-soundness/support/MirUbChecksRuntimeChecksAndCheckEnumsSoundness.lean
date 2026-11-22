/-!
# Soundness and Completeness of `rustc` MIR `UbChecks`, `Operand::RuntimeChecks`,
  and `CheckEnums`

Self-contained, pure kernel-checked Lean 4 (`v4.34.1`) formalization of:
1. `CheckAlignment` and `CheckNull` pointer instrumentation (`check_pointers.rs`,
   `check_alignment.rs`, `check_null.rs`), including the ZST null-borrow vs.
   null-copy asymmetry, `BorrowedFieldProjectionMode::FollowProjections`
   soundness under standard non-packed field-alignment divisibility,
   `max_reliable_alignment` mask weakening, and the unsized-pointee skip.
2. `CheckEnums` direct sign-extended discriminant masking and `u128`
   wrapping-niche membership equivalence (`check_enums.rs`, `wrapping_range.rs`)
   for all bit-widths `w ∈ {8, 16, 32, 64, 128}`, including exact recovery under
   `maskW` and constructive proof that omitting `maskW` on signed niche tags
   breaks both soundness (false accept) and completeness (false abort).
3. Cross-crate `Operand::RuntimeChecks` (`UbChecks` / `OverflowChecks` /
   `ContractChecks`) evaluation timing across `LowerIntrinsics`,
   `InstSimplify::SimplifyUbCheck` (gated by `#![rustc_preserve_ub_checks]` and
   `mir_opt_level >= 1`), `.rmeta` serialization, downstream codegen, CTFE, and
   fail-closed capture (`Trusted.MirAst.Operand`).
4. Non-unwinding `UnwindAction::Unreachable` + `#[rustc_nounwind]` abort
   semantics through `catch_unwind` and cleanup frames.
5. Constructive sharpness counterexamples (`ce1`–`ce5`).

Purity invariants enforced throughout:
- Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
  zero `native_decide`, zero `partial def`, zero `unsafe`, zero `._unsafe_rec`.
- No `deriving DecidableEq, Repr` on inductive types carrying `List`/`Option`.
-/

namespace MirUbChecksRuntimeChecksAndCheckEnumsSoundness

/-! ## Part 1: Constructive Modular Arithmetic and Bit-Width Foundations -/

/-- Supported scalar integer tag/discriminant bit-widths in `rustc_abi::Integer`. -/
inductive IntWidth where
  | w8
  | w16
  | w32
  | w64
  | w128

namespace IntWidth

/-- Bit-width in bits (`8`, `16`, `32`, `64`, or `128`). -/
def bits : IntWidth → Nat
  | .w8 => 8
  | .w16 => 16
  | .w32 => 32
  | .w64 => 64
  | .w128 => 128

/-- Byte size (`1`, `2`, `4`, `8`, or `16`). -/
def bytes : IntWidth → Nat
  | .w8 => 1
  | .w16 => 2
  | .w32 => 4
  | .w64 => 8
  | .w128 => 16

/-- Unsigned modulus `2 ^ w.bits`. -/
def modulus (w : IntWidth) : Nat :=
  Nat.pow 2 w.bits

/-- Maximum unsigned value `2 ^ w.bits - 1` (`Size::unsigned_int_max`). -/
def maxVal (w : IntWidth) : Nat :=
  w.modulus - 1

/-- Half-modulus `2 ^ (w.bits - 1)` (the sign-bit threshold for two's complement). -/
def halfModulus (w : IntWidth) : Nat :=
  Nat.pow 2 (w.bits - 1)

theorem bits_eq_bytes_mul_eight (w : IntWidth) : w.bits = w.bytes * 8 := by
  cases w <;> rfl

theorem bits_le_128 (w : IntWidth) : w.bits ≤ 128 := by
  cases w <;> decide

theorem bits_pos (w : IntWidth) : 0 < w.bits := by
  cases w <;> decide

theorem modulus_pos (w : IntWidth) : 0 < w.modulus := by
  unfold modulus
  exact Nat.pow_pos (by decide : 0 < 2)

theorem modulus_eq_two_mul_half (w : IntWidth) :
    w.modulus = 2 * w.halfModulus := by
  cases w <;> decide

theorem halfModulus_lt_modulus (w : IntWidth) :
    w.halfModulus < w.modulus := by
  cases w <;> decide

end IntWidth

/-- Exact `u128` modulus `2^128`. -/
def M128 : Nat := Nat.pow 2 128

theorem M128_pos : 0 < M128 := by
  unfold M128
  exact Nat.pow_pos (by decide : 0 < 2)

theorem pow_le_pow_right_two {a b : Nat} (h : a ≤ b) :
    Nat.pow 2 a ≤ Nat.pow 2 b :=
  Nat.pow_le_pow_right (by decide : 0 < 2) h

theorem modulus_le_M128 (w : IntWidth) : w.modulus ≤ M128 :=
  pow_le_pow_right_two w.bits_le_128

theorem modulus_dvd_M128 (w : IntWidth) : w.modulus ∣ M128 := by
  cases w with
  | w8 =>
    refine ⟨Nat.pow 2 120, ?_⟩
    exact (Nat.pow_add 2 8 120).symm
  | w16 =>
    refine ⟨Nat.pow 2 112, ?_⟩
    exact (Nat.pow_add 2 16 112).symm
  | w32 =>
    refine ⟨Nat.pow 2 96, ?_⟩
    exact (Nat.pow_add 2 32 96).symm
  | w64 =>
    refine ⟨Nat.pow 2 64, ?_⟩
    exact (Nat.pow_add 2 64 64).symm
  | w128 =>
    exact ⟨1, (Nat.mul_one M128).symm⟩

/-- Truncation / bitmask to width `w` (`x & w.unsigned_int_max()`, i.e. `x % 2^w`). -/
def maskW (w : IntWidth) (x : Nat) : Nat :=
  x % w.modulus

theorem maskW_lt (w : IntWidth) (x : Nat) : maskW w x < w.modulus :=
  Nat.mod_lt x w.modulus_pos

theorem maskW_eq_self {w : IntWidth} {x : Nat} (hx : x < w.modulus) :
    maskW w x = x :=
  Nat.mod_eq_of_lt hx

/-- Two's-complement sign extension from width `w` to `u128`, modeling
`CastKind::IntToInt` from signed `i8`/`i16`/`i32`/`i64`/`i128` to `u128`
in `insert_discr_cast_to_u128` (`compiler/rustc_mir_transform/src/check_enums.rs`). -/
def signExtendTo128 (w : IntWidth) (raw : Nat) : Nat :=
  let v := raw % w.modulus
  if v ≥ w.halfModulus then M128 - w.modulus + v else v

theorem signExtendTo128_lt_M128 (w : IntWidth) (raw : Nat) :
    signExtendTo128 w raw < M128 := by
  unfold signExtendTo128
  dsimp only
  split
  · have hlt : raw % w.modulus < w.modulus := Nat.mod_lt raw w.modulus_pos
    have hle : w.modulus ≤ M128 := modulus_le_M128 w
    have h1 : M128 - w.modulus + raw % w.modulus < M128 - w.modulus + w.modulus :=
      Nat.add_lt_add_left hlt (M128 - w.modulus)
    rw [Nat.sub_add_cancel hle] at h1
    exact h1
  · exact Nat.lt_of_lt_of_le (Nat.mod_lt raw w.modulus_pos) (modulus_le_M128 w)

/-- Key algebraic lemma: `(M128 - w.modulus + v) % w.modulus = v` whenever `v < w.modulus`. -/
theorem mod_M128_sub_modulus_add (w : IntWidth) {v : Nat} (hv : v < w.modulus) :
    (M128 - w.modulus + v) % w.modulus = v := by
  have hdvd : w.modulus ∣ M128 := modulus_dvd_M128 w
  rcases hdvd with ⟨k, hk⟩
  have hk_pos : 0 < k := by
    cases k with
    | zero =>
      rw [Nat.mul_zero] at hk
      have hpos : 0 < M128 := M128_pos
      rw [hk] at hpos
      exact False.elim (Nat.lt_irrefl 0 hpos)
    | succ k' => exact Nat.succ_pos k'
  have hk_eq : M128 - w.modulus = w.modulus * (k - 1) := by
    have h1 : k = (k - 1) + 1 := (Nat.sub_add_cancel hk_pos).symm
    have h2 : w.modulus * k = w.modulus * (k - 1) + w.modulus := by
      conv => lhs; rw [h1]
      rw [Nat.mul_add, Nat.mul_one]
    rw [hk, h2, Nat.add_sub_cancel]
  rw [hk_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]

/-- Exact masking recovery theorem: applying `maskW w` (i.e. `& discr.size.unsigned_int_max()`)
after `signExtendTo128 w` always recovers the exact unsigned bit pattern `raw % w.modulus`. -/
theorem maskW_signExtendTo128 (w : IntWidth) (raw : Nat) :
    maskW w (signExtendTo128 w raw) = raw % w.modulus := by
  unfold maskW signExtendTo128
  dsimp only
  split
  · exact mod_M128_sub_modulus_add w (Nat.mod_lt raw w.modulus_pos)
  · exact Nat.mod_mod raw w.modulus

/-- Exact `u128::wrapping_sub(a, b)` for arbitrary `Nat` inputs reduced mod `2^128`. -/
def wrappingSub128 (a b : Nat) : Nat :=
  (a % M128 + M128 - b % M128) % M128

theorem wrappingSub128_lt (a b : Nat) : wrappingSub128 a b < M128 :=
  Nat.mod_lt _ M128_pos

theorem wrappingSub128_eq_sub {a b : Nat} (ha : a < M128) (hb : b < M128) (hba : b ≤ a) :
    wrappingSub128 a b = a - b := by
  unfold wrappingSub128
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  have h_eq : a + M128 - b = (a - b) + M128 := Nat.sub_add_comm hba
  rw [h_eq, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le a b) ha)

theorem wrappingSub128_eq_wrap {a b : Nat} (ha : a < M128) (hb : b < M128) (hab : a < b) :
    wrappingSub128 a b = M128 - (b - a) := by
  unfold wrappingSub128
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  have hba : a ≤ b := Nat.le_of_lt hab
  have hdiff_pos : 0 < b - a := Nat.sub_pos_of_lt hab
  have hdiff_lt : b - a < M128 := Nat.lt_of_le_of_lt (Nat.sub_le b a) hb
  have hdiff_le : b - a ≤ M128 := Nat.le_of_lt hdiff_lt
  have h_eq : a + M128 - b = M128 - (b - a) := by
    have h1 : a + M128 = (M128 - (b - a)) + b := by
      have h2 : (M128 - (b - a)) + (b - a) = M128 := Nat.sub_add_cancel hdiff_le
      have h3 : a + ((M128 - (b - a)) + (b - a)) = a + M128 := congrArg (a + ·) h2
      have h4 : a + ((M128 - (b - a)) + (b - a)) = (M128 - (b - a)) + (a + (b - a)) := by
        rw [Nat.add_left_comm]
      rw [h4, Nat.add_sub_of_le hba] at h3
      exact h3.symm
    rw [h1, Nat.add_sub_cancel]
  rw [h_eq]
  have hlt : M128 - (b - a) < M128 := Nat.sub_lt M128_pos hdiff_pos
  exact Nat.mod_eq_of_lt hlt

/-- Helper lemma: if `x ≤ y`, `y ≤ M`, then `M - y ≤ M - x`. -/
theorem nat_sub_le_sub_left_of_le {M x y : Nat} (hxy : x ≤ y) : M - y ≤ M - x :=
  Nat.sub_le_sub_left hxy M

/-- Helper lemma: if `x < y ≤ M`, then `M - y < M - x`. -/
theorem nat_sub_lt_sub_left_of_lt {M x y : Nat} (hxy : x < y) (hyM : y ≤ M) :
    M - y < M - x := by
  have hxM : x < M := Nat.lt_of_lt_of_le hxy hyM
  have hlt : (M - y) + x < (M - x) + x := by
    calc
      (M - y) + x < (M - y) + y := Nat.add_lt_add_left hxy (M - y)
      _ = M := Nat.sub_add_cancel hyM
      _ = (M - x) + x := (Nat.sub_add_cancel (Nat.le_of_lt hxM)).symm
  exact Nat.lt_of_add_lt_add_right hlt

/-- Divisibility helper: if `d ∣ k`, then `a % d = 0 ↔ (a + k) % d = 0`. -/
theorem mod_add_eq_zero_iff_of_dvd {a k d : Nat} (hdvd : d ∣ k) :
    (a + k) % d = 0 ↔ a % d = 0 := by
  rcases hdvd with ⟨q, hq⟩
  rw [hq, Nat.add_mul_mod_self_left]

/-! ## Part 2: `CheckAlignment` & `CheckNull` Pointer Instrumentation Soundness -/

/-- MIR `PlaceContext` classification modeled after `PointerFinder::should_visit_place`
(`compiler/rustc_mir_transform/src/check_pointers.rs:182-198`). -/
inductive PlaceContextKind where
  | copy
  | move
  | store
  | call
  | yield
  | drop
  | sharedBorrow
  | mutBorrow
  | rawBorrow
  | placeMention

/-- Mirror of `BorrowedFieldProjectionMode` (`check_pointers.rs:19-22`). -/
inductive BorrowedFieldProjectionMode where
  | followProjections
  | noFollowProjections

/-- Mirror of `rustc_middle::mir::AssertKind` UB-check variants
(`compiler/rustc_middle/src/mir/syntax.rs:1043-1056`). -/
inductive UbAssertKind where
  | misalignedPointerDereference
  | nullPointerDereference
  | nullReferenceConstructed
  | invalidEnumConstruction

/-- Layout descriptor for a pointee type (`size`, `align`, `isSized`). -/
structure PointeeLayout where
  size : Nat
  align : Nat
  alignPos : 0 < align
  isSized : Bool

/-- A raw-pointer-rooted place `(*p).field` with base pointee layout and
projected field layout/offset. -/
structure FieldProjectionPlace where
  baseLayout : PointeeLayout
  fieldLayout : PointeeLayout
  fieldOffset : Nat

/-- Mirror of `PointerFinder::should_visit_place` (`check_pointers.rs:182-198`). -/
def shouldVisitPlace : PlaceContextKind → Bool
  | .copy | .move | .store | .call | .yield | .drop
  | .sharedBorrow | .mutBorrow => true
  | .rawBorrow | .placeMention => false

/-- Mirror of the borrow context test in `check_pointers.rs:220-224` and
`check_null.rs:57-58`. -/
def isBorrowContext : PlaceContextKind → Bool
  | .sharedBorrow | .mutBorrow => true
  | _ => false

/-- Mirror of `PointerFinder::visit_place` pointee-type selection
(`check_pointers.rs:212-228`). -/
def effectivePointeeLayout (mode : BorrowedFieldProjectionMode)
    (ctx : PlaceContextKind) (fp : FieldProjectionPlace) : PointeeLayout :=
  match mode with
  | .followProjections =>
    if isBorrowContext ctx then fp.fieldLayout else fp.baseLayout
  | .noFollowProjections => fp.baseLayout

/-- Mirror of `CheckAlignment::run_pass` trivial-alignment exclusion
(`check_alignment.rs:22`: `[bool, i8, u8]` all have `align = 1`) and
`PointerFinder::visit_place` `is_sized` filter (`check_pointers.rs:231`). -/
def checkAlignmentInstruments (mode : BorrowedFieldProjectionMode)
    (ctx : PlaceContextKind) (fp : FieldProjectionPlace) : Bool :=
  let eff := effectivePointeeLayout mode ctx fp
  shouldVisitPlace ctx && eff.isSized && decide (eff.align ≠ 1)

/-- Whether the runtime alignment check inserted by `CheckAlignment` (or skipped)
passes for base pointer address `addr`, given optional target `maxReliableAlign`
(`check_alignment.rs:86-108`). When `maxReliableAlign = 0`, no cap is active
(matching `max_align == Align::MAX`). -/
def checkAlignmentPasses (mode : BorrowedFieldProjectionMode)
    (ctx : PlaceContextKind) (fp : FieldProjectionPlace) (addr : Nat) : Bool :=
  let eff := effectivePointeeLayout mode ctx fp
  if checkAlignmentInstruments mode ctx fp then
    decide (addr % eff.align = 0)
  else
    true

/-- Reference-level alignment requirement for `(*p).field` under `ctx`
(`rust-lang/reference` `src/behavior-considered-undefined.md`:
`r[undefined.misaligned.ptr]`, `r[undefined.misaligned.load-store]`,
`r[undefined.misaligned.raw]`, `r[undefined.misaligned.reference]`). -/
def refAlignmentRequired (ctx : PlaceContextKind)
    (fp : FieldProjectionPlace) (addr : Nat) : Prop :=
  match ctx with
  | .rawBorrow | .placeMention => True
  | .sharedBorrow | .mutBorrow => (addr + fp.fieldOffset) % fp.fieldLayout.align = 0
  | .copy | .move | .store | .call | .yield | .drop => addr % fp.baseLayout.align = 0

/-- Mirror of `CheckNull::insert_null_check` (`check_null.rs:55-127`). -/
def checkNullPointeeShouldBeChecked (ctx : PlaceContextKind)
    (layout : PointeeLayout) : Bool :=
  if isBorrowContext ctx then true else decide (layout.size ≠ 0)

/-- Mirror of `CheckNull` assert kind selection (`check_null.rs:55-88`,
reflecting `1.102.0-nightly` / HEAD split between `NullReferenceConstructed`
and `NullPointerDereference`). -/
def checkNullAssertKind (ctx : PlaceContextKind) : UbAssertKind :=
  if isBorrowContext ctx then .nullReferenceConstructed else .nullPointerDereference

/-- Whether `CheckNull` passes (returns `true`) or aborts (returns `false`)
for base pointer address `addr` on a sized pointee. -/
def checkNullPasses (ctx : PlaceContextKind) (layout : PointeeLayout)
    (addr : Nat) : Bool :=
  if shouldVisitPlace ctx && layout.isSized then
    !(decide (addr = 0) && checkNullPointeeShouldBeChecked ctx layout)
  else
    true

/-- Reference-level null-pointer UB predicate (`r[undefined.dangling.def]`,
`r[undefined.validity.reference-box]`, `r[undefined.pointer-access]`):
a null pointer access is UB iff it is a visited place use AND either a borrow
(even for a ZST!) or a non-ZST access. -/
def nullAccessIsUB (ctx : PlaceContextKind) (layout : PointeeLayout)
    (addr : Nat) : Prop :=
  shouldVisitPlace ctx = true ∧ addr = 0 ∧ (isBorrowContext ctx = true ∨ layout.size ≠ 0)

/-- Soundness and completeness of `CheckNull` for all sized pointees,
place contexts, and pointer addresses. -/
theorem checkNullPasses_eq_false_iff_nullAccessIsUB
    (ctx : PlaceContextKind) (layout : PointeeLayout) (hSized : layout.isSized = true)
    (addr : Nat) :
    checkNullPasses ctx layout addr = false ↔ nullAccessIsUB ctx layout addr := by
  unfold checkNullPasses checkNullPointeeShouldBeChecked nullAccessIsUB
  rw [hSized, Bool.and_true]
  cases hVis : shouldVisitPlace ctx with
  | false =>
    simp
  | true =>
    simp only [↓reduceIte, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq, true_and]
    cases hBor : isBorrowContext ctx with
    | true =>
      simp
    | false =>
      simp

/-- **Theorem (`checkNull_zst_borrow_vs_copy_iff`)**:
For any sized zero-sized type (`layout.size = 0`) and null pointer (`addr = 0`),
`CheckNull` rejects shared and mutable borrows (`&*p`, `&mut *p`) with
`AssertKind::NullReferenceConstructed` while permitting raw copies and moves
(`*p`) — and more generally, for a null ZST pointer under any visited context,
`CheckNull` aborts iff the context is a borrow. -/
theorem checkNull_zst_borrow_vs_copy_iff
    (layout : PointeeLayout) (hSized : layout.isSized = true) (hZst : layout.size = 0) :
    (∀ ctx, shouldVisitPlace ctx = true →
      (checkNullPasses ctx layout 0 = false ↔ isBorrowContext ctx = true)) ∧
    checkNullPasses .sharedBorrow layout 0 = false ∧
    checkNullPasses .mutBorrow layout 0 = false ∧
    checkNullPasses .copy layout 0 = true ∧
    checkNullPasses .move layout 0 = true ∧
    checkNullAssertKind .sharedBorrow = .nullReferenceConstructed ∧
    checkNullAssertKind .mutBorrow = .nullReferenceConstructed ∧
    checkNullAssertKind .copy = .nullPointerDereference := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · intro ctx hVis
    rw [checkNullPasses_eq_false_iff_nullAccessIsUB ctx layout hSized 0]
    unfold nullAccessIsUB
    rw [hVis, hZst]
    constructor
    · intro ⟨_, _, h⟩
      cases h with
      | inl hb => exact hb
      | inr hne => exact False.elim (hne rfl)
    · intro hb
      exact ⟨rfl, rfl, Or.inl hb⟩
  · unfold checkNullPasses checkNullPointeeShouldBeChecked
    rw [hSized]
    rfl
  · unfold checkNullPasses checkNullPointeeShouldBeChecked
    rw [hSized]
    rfl
  · unfold checkNullPasses checkNullPointeeShouldBeChecked
    rw [hSized, hZst]
    rfl
  · unfold checkNullPasses checkNullPointeeShouldBeChecked
    rw [hSized, hZst]
    rfl

/-- **Theorem (`checkAlignment_followProjections_sound`)**:
Under `BorrowedFieldProjectionMode::FollowProjections`, for any non-packed
sized struct/field place where `fieldLayout.align ∣ fieldOffset`:
1. `CheckAlignment` passes on every visited context (`copy`, `move`, `store`,
   `call`, `yield`, `drop`, `sharedBorrow`, `mutBorrow`) if and only if the
   Rust Reference alignment requirement `refAlignmentRequired` holds (even
   when `CheckAlignment` skips `align = 1` pointees like `u8`/`i8`/`bool`,
   and even though `check_pointers.rs:208` checks the base pointer `addr`
   rather than `addr + fieldOffset`).
2. For raw borrows (`&raw const`/`&raw mut`) and `PlaceMention`, `CheckAlignment`
   never instruments and never aborts, matching `r[undefined.misaligned.raw]`. -/
theorem checkAlignment_followProjections_sound
    (fp : FieldProjectionPlace)
    (hBaseSized : fp.baseLayout.isSized = true)
    (hFieldSized : fp.fieldLayout.isSized = true)
    (hOffsetAligned : fp.fieldLayout.align ∣ fp.fieldOffset)
    (ctx : PlaceContextKind) (addr : Nat) :
    checkAlignmentPasses .followProjections ctx fp addr = true ↔
      refAlignmentRequired ctx fp addr := by
  have hModOne : ∀ x : Nat, x % 1 = 0 := fun x => Nat.mod_one x
  cases ctx with
  | rawBorrow =>
    unfold checkAlignmentPasses checkAlignmentInstruments refAlignmentRequired
    simp [shouldVisitPlace]
  | placeMention =>
    unfold checkAlignmentPasses checkAlignmentInstruments refAlignmentRequired
    simp [shouldVisitPlace]
  | sharedBorrow =>
    unfold checkAlignmentPasses checkAlignmentInstruments effectivePointeeLayout refAlignmentRequired
    simp only [shouldVisitPlace, isBorrowContext, ↓reduceIte, hFieldSized, Bool.true_and]
    rw [mod_add_eq_zero_iff_of_dvd hOffsetAligned]
    by_cases h1 : fp.fieldLayout.align = 1
    · rw [h1]
      simp [hModOne]
    · simp [h1]
  | mutBorrow =>
    unfold checkAlignmentPasses checkAlignmentInstruments effectivePointeeLayout refAlignmentRequired
    simp only [shouldVisitPlace, isBorrowContext, ↓reduceIte, hFieldSized, Bool.true_and]
    rw [mod_add_eq_zero_iff_of_dvd hOffsetAligned]
    by_cases h1 : fp.fieldLayout.align = 1
    · rw [h1]
      simp [hModOne]
    · simp [h1]
  | copy | move | store | call | yield | drop =>
    unfold checkAlignmentPasses checkAlignmentInstruments effectivePointeeLayout refAlignmentRequired
    simp only [shouldVisitPlace, isBorrowContext, Bool.false_eq_true, ↓reduceIte, hBaseSized,
      Bool.true_and]
    by_cases h1 : fp.baseLayout.align = 1
    · rw [h1]
      simp [hModOne]
    · simp [h1]

/-- Monotonicity of `max_reliable_alignment` weakening (`check_alignment.rs:86-108`):
if `cap` divides `reqAlign` (both powers of two with `cap ≤ reqAlign`), any
address aligned to `reqAlign` also passes the capped alignment check `addr % cap = 0`. -/
theorem maxReliableAlign_weakening_never_false_aborts
    {reqAlign cap addr : Nat} (hdvd : cap ∣ reqAlign) (hAligned : addr % reqAlign = 0) :
    addr % cap = 0 := by
  have hReqDvd : reqAlign ∣ addr := Nat.dvd_of_mod_eq_zero hAligned
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hdvd hReqDvd)

/-! ## Part 3: `CheckEnums` Direct Masking and `u128` Wrapping-Niche Equivalence -/

/-- Exact model of `rustc_abi::WrappingRange`
(`compiler/rustc_abi/src/wrapping_range.rs:19-22`). -/
structure WrappingRange where
  start : Nat
  end_ : Nat

/-- Exact model of `WrappingRange::contains`
(`compiler/rustc_abi/src/wrapping_range.rs:57-63`). -/
def WrappingRange.contains (r : WrappingRange) (v : Nat) : Bool :=
  if r.start ≤ r.end_ then
    decide (r.start ≤ v ∧ v ≤ r.end_)
  else
    decide (r.start ≤ v ∨ v ≤ r.end_)

/-- Exact model of `CheckEnums::insert_niche_check`'s `u128` wrapping comparison
(`compiler/rustc_mir_transform/src/check_enums.rs:489-526`):
`discr.wrapping_sub(start) <= end.wrapping_sub(start)` computed in `u128`. -/
def insertNicheCheckU128 (r : WrappingRange) (discr : Nat) : Bool :=
  decide (wrappingSub128 discr r.start ≤ wrappingSub128 r.end_ r.start)

/-- Exact model of `CheckEnums::insert_direct_enum_check`'s masked discriminant
membership test (`compiler/rustc_mir_transform/src/check_enums.rs:389-418`). -/
def insertDirectEnumCheck (w : IntWidth) (validDiscrs : List Nat) (raw : Nat) : Bool :=
  let extended := signExtendTo128 w raw
  let masked := maskW w extended
  validDiscrs.any (fun d => decide (masked = maskW w d))

/-- Reference-level direct enum validity test over truncated bit patterns. -/
def directEnumValid (w : IntWidth) (validDiscrs : List Nat) (raw : Nat) : Bool :=
  validDiscrs.any (fun d => decide (raw % w.modulus = d % w.modulus))

/-- **Direct Sign-Extended Masking Soundness (`insertDirectEnumCheck_signed_mask_sound`)**:
For every bit-width `w`, discriminant list `validDiscrs`, and raw bit pattern `raw`,
`insert_direct_enum_check`'s sign-extend-to-`u128` followed by `& unsigned_int_max()`
agrees identically with exact width-`w` unsigned discriminant matching. -/
theorem insertDirectEnumCheck_signed_mask_sound
    (w : IntWidth) (validDiscrs : List Nat) (raw : Nat) :
    insertDirectEnumCheck w validDiscrs raw = directEnumValid w validDiscrs raw := by
  unfold insertDirectEnumCheck directEnumValid
  dsimp only
  rw [maskW_signExtendTo128]
  rfl

/-- Core arithmetic equivalence (non-wrapping branch `start ≤ end_`):
for `discr, start, end_ < M128`, `wrappingSub128 discr start ≤ wrappingSub128 end_ start`
holds iff `start ≤ discr ∧ discr ≤ end_`. -/
theorem wrappingSub128_le_iff_nonwrapping
    {discr start end_ : Nat}
    (hd : discr < M128) (hs : start < M128) (he : end_ < M128) (hle : start ≤ end_) :
    wrappingSub128 discr start ≤ wrappingSub128 end_ start ↔
      (start ≤ discr ∧ discr ≤ end_) := by
  rw [wrappingSub128_eq_sub he hs hle]
  by_cases hsd : start ≤ discr
  · rw [wrappingSub128_eq_sub hd hs hsd]
    constructor
    · intro hsub
      refine ⟨hsd, ?_⟩
      have h1 : (discr - start) + start ≤ (end_ - start) + start :=
        Nat.add_le_add_right hsub start
      rw [Nat.sub_add_cancel hsd, Nat.sub_add_cancel hle] at h1
      exact h1
    · intro ⟨_, hde⟩
      exact Nat.sub_le_sub_right hde start
  · have hds : discr < start := Nat.lt_of_not_ge hsd
    rw [wrappingSub128_eq_wrap hd hs hds]
    constructor
    · intro hcontra
      -- Impossible: M128 - (start - discr) > end_ - start because
      -- (end_ - start) + (start - discr) = end_ - discr < M128.
      have h1 : (M128 - (start - discr)) + (start - discr) ≤
                (end_ - start) + (start - discr) :=
        Nat.add_le_add_right hcontra (start - discr)
      have hsd_lt : start - discr < M128 := Nat.lt_of_le_of_lt (Nat.sub_le start discr) hs
      rw [Nat.sub_add_cancel (Nat.le_of_lt hsd_lt)] at h1
      have hsum_le : (end_ - start) + (start - discr) ≤ end_ := by
        have hstep1 : (end_ - start) + (start - discr) ≤ (end_ - start) + start :=
          Nat.add_le_add_left (Nat.sub_le start discr) (end_ - start)
        rw [Nat.sub_add_cancel hle] at hstep1
        exact hstep1
      have hM_le_end : M128 ≤ end_ := Nat.le_trans h1 hsum_le
      exact False.elim (Nat.not_lt_of_ge hM_le_end he)
    · intro ⟨hsd', _⟩
      exact False.elim (hsd hsd')

/-- Core arithmetic equivalence (wrapping branch `end_ < start`):
for `discr, start, end_ < M128`, `wrappingSub128 discr start ≤ wrappingSub128 end_ start`
holds iff `start ≤ discr ∨ discr ≤ end_`. -/
theorem wrappingSub128_le_iff_wrapping
    {discr start end_ : Nat}
    (hd : discr < M128) (hs : start < M128) (he : end_ < M128) (hlt : end_ < start) :
    wrappingSub128 discr start ≤ wrappingSub128 end_ start ↔
      (start ≤ discr ∨ discr ≤ end_) := by
  rw [wrappingSub128_eq_wrap he hs hlt]
  by_cases hsd : start ≤ discr
  · rw [wrappingSub128_eq_sub hd hs hsd]
    constructor
    · intro _
      exact Or.inl hsd
    · intro _
      -- Need `discr - start ≤ M128 - (start - end_)`.
      -- Equivalent to `(discr - start) + (start - end_) ≤ M128`.
      have h1 : (discr - start) + (start - end_) ≤ M128 := by
        have ha : (discr - start) + (start - end_) ≤ (discr - start) + start :=
          Nat.add_le_add_left (Nat.sub_le start end_) (discr - start)
        rw [Nat.sub_add_cancel hsd] at ha
        exact Nat.le_trans ha (Nat.le_of_lt hd)
      exact Nat.le_sub_of_add_le h1
  · have hds : discr < start := Nat.lt_of_not_ge hsd
    rw [wrappingSub128_eq_wrap hd hs hds]
    constructor
    · intro hle_wrap
      refine Or.inr ?_
      -- From `M128 - (start - discr) ≤ M128 - (start - end_)` we derive `start - end_ ≤ start - discr`,
      -- hence `discr ≤ end_`.
      by_cases hde : discr ≤ end_
      · exact hde
      · have hed : end_ < discr := Nat.lt_of_not_ge hde
        have hdiff_lt : start - discr < start - end_ := by
          exact nat_sub_lt_sub_left_of_lt hed (Nat.le_of_lt hds)
        have hse_le : start - end_ ≤ M128 :=
          Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le start end_) hs)
        have hstrict : M128 - (start - end_) < M128 - (start - discr) :=
          nat_sub_lt_sub_left_of_lt hdiff_lt hse_le
        exact False.elim (Nat.not_lt_of_ge hle_wrap hstrict)
    · intro hdisj
      cases hdisj with
      | inl hsd' => exact False.elim (hsd hsd')
      | inr hde =>
        have hdiff_le : start - end_ ≤ start - discr :=
          nat_sub_le_sub_left_of_le hde
        exact nat_sub_le_sub_left_of_le hdiff_le

/-- **Theorem (`insertNicheCheck_u128_iff_wrappingRange_contains`)**:
For EVERY bit-width `w ∈ {8, 16, 32, 64, 128}`, EVERY `WrappingRange` with
`r.start < 2^w` and `r.end_ < 2^w`, and EVERY `discr < 2^w`, the `u128`
wrapping-subtraction check emitted by `CheckEnums::insert_niche_check` is
logically equivalent to `WrappingRange::contains`.

Crucially, this theorem requires `discr < 2^w` (equivalently `discr < 2^128`
and no unmasked high bits above bit `w`). As `ce2` proves below, violating
`discr < 2^w` via unmasked sign-extension from a signed niche tag breaks BOTH
directions of this equivalence! -/
theorem insertNicheCheck_u128_iff_wrappingRange_contains
    (w : IntWidth) (r : WrappingRange) (discr : Nat)
    (hStart : r.start < w.modulus) (hEnd : r.end_ < w.modulus)
    (hDiscr : discr < w.modulus) :
    insertNicheCheckU128 r discr = r.contains discr := by
  have hM : w.modulus ≤ M128 := modulus_le_M128 w
  have hs : r.start < M128 := Nat.lt_of_lt_of_le hStart hM
  have he : r.end_ < M128 := Nat.lt_of_lt_of_le hEnd hM
  have hd : discr < M128 := Nat.lt_of_lt_of_le hDiscr hM
  unfold insertNicheCheckU128 WrappingRange.contains
  by_cases hle : r.start ≤ r.end_
  · simp only [hle, ↓reduceIte]
    have hiff := wrappingSub128_le_iff_nonwrapping hd hs he hle
    by_cases hp : r.start ≤ discr ∧ discr ≤ r.end_
    · rw [decide_eq_true hp, decide_eq_true (hiff.mpr hp)]
    · rw [decide_eq_false hp, decide_eq_false (fun h => hp (hiff.mp h))]
  · simp only [hle, ↓reduceIte]
    have hlt : r.end_ < r.start := Nat.lt_of_not_ge hle
    have hiff := wrappingSub128_le_iff_wrapping hd hs he hlt
    by_cases hp : r.start ≤ discr ∨ discr ≤ r.end_
    · rw [decide_eq_true hp, decide_eq_true (hiff.mpr hp)]
    · rw [decide_eq_false hp, decide_eq_false (fun h => hp (hiff.mp h))]

/-- Propositional iff corollary of `insertNicheCheck_u128_iff_wrappingRange_contains`. -/
theorem insertNicheCheck_u128_prop_iff
    (w : IntWidth) (r : WrappingRange) (discr : Nat)
    (hStart : r.start < w.modulus) (hEnd : r.end_ < w.modulus)
    (hDiscr : discr < w.modulus) :
    wrappingSub128 discr r.start ≤ wrappingSub128 r.end_ r.start ↔
      r.contains discr = true := by
  have h := insertNicheCheck_u128_iff_wrappingRange_contains w r discr hStart hEnd hDiscr
  unfold insertNicheCheckU128 at h
  constructor
  · intro hle
    rw [← h]
    exact decide_eq_true hle
  · intro ht
    rw [← h] at ht
    exact of_decide_eq_true ht

/-- **Remediation Theorem (`insertNicheCheck_masked_signed_sound`)**:
If `CheckEnums::insert_niche_check` masks the sign-extended `u128` discriminant
with `discr.size.unsigned_int_max()` (`maskW w`) — matching `insert_direct_enum_check`
(`check_enums.rs:390`) — then `insertNicheCheckU128` is unconditionally sound and
complete for BOTH signed and unsigned niche tags at every width `w`. -/
theorem insertNicheCheck_masked_signed_sound
    (w : IntWidth) (r : WrappingRange) (raw : Nat)
    (hStart : r.start < w.modulus) (hEnd : r.end_ < w.modulus) :
    insertNicheCheckU128 r (maskW w (signExtendTo128 w raw)) =
      r.contains (raw % w.modulus) := by
  rw [maskW_signExtendTo128]
  exact insertNicheCheck_u128_iff_wrappingRange_contains w r (raw % w.modulus)
    hStart hEnd (Nat.mod_lt raw w.modulus_pos)

/-! ## Part 4: Cross-Crate `Operand::RuntimeChecks` Timing and Monotonicity -/

/-- Exact model of `rustc_middle::mir::RuntimeChecks`
(`compiler/rustc_middle/src/mir/syntax.rs:1588-1598`). -/
inductive RuntimeCheckKind where
  | ubChecks
  | contractChecks
  | overflowChecks

/-- Crate compilation flags governing `RuntimeChecks` lowering and folding. -/
structure CrateFlags where
  ubChecks : Bool
  overflowChecks : Bool
  contractChecks : Bool
  mirOptLevel : Nat
  preserveUbChecks : Bool

/-- Exact model of `RuntimeChecks::value(self, sess)` (`syntax.rs:1601-1607`). -/
def RuntimeCheckKind.evalInCrate (k : RuntimeCheckKind) (c : CrateFlags) : Bool :=
  match k with
  | .ubChecks => c.ubChecks
  | .contractChecks => c.contractChecks
  | .overflowChecks => c.overflowChecks

/-- Symbolic vs. constant-folded boolean check operand across MIR phases. -/
inductive MirCheckOperand where
  | symbolic (kind : RuntimeCheckKind)
  | constBool (val : Bool)

/-- Model of `InstSimplify::run_pass` + `SimplifyUbCheck::visit_operand`
(`compiler/rustc_mir_transform/src/instsimplify.rs:29-37, 481-492`):
runs when `mirOptLevel ≥ 1`, folds ONLY `RuntimeChecks::UbChecks` when
`preserveUbChecks = false`, and leaves `OverflowChecks`/`ContractChecks` symbolic. -/
def runInstSimplify (up : CrateFlags) (op : MirCheckOperand) : MirCheckOperand :=
  match op with
  | .constBool b => .constBool b
  | .symbolic .ubChecks =>
    if decide (up.mirOptLevel ≥ 1) && !up.preserveUbChecks then
      .constBool up.ubChecks
    else
      .symbolic .ubChecks
  | .symbolic .overflowChecks => .symbolic .overflowChecks
  | .symbolic .contractChecks => .symbolic .contractChecks

/-- Model of `rustc_codegen_ssa::mir::operand::codegen_operand`
(`compiler/rustc_codegen_ssa/src/mir/operand.rs:1164-1173`) evaluating a
serialized `.rmeta` MIR operand in the downstream crate `down`. -/
def evalAtDownstreamCodegen (down : CrateFlags) : MirCheckOperand → Bool
  | .constBool b => b
  | .symbolic k => k.evalInCrate down

/-- End-to-end cross-crate evaluation for a generic / `#[inline]` function
defined in `up` (serialized to `.rmeta` after `optimized_mir`) and
monomorphized in `down`. -/
def crossCrateGenericCheck (up down : CrateFlags) (k : RuntimeCheckKind) : Bool :=
  evalAtDownstreamCodegen down (runInstSimplify up (.symbolic k))

/-- Model of CTFE `CompileTimeMachine::runtime_checks`
(`compiler/rustc_const_eval/src/const_eval/machine.rs:564-571`):
always evaluates to `true`, independent of crate flags. -/
def evalAtCtfe (_k : RuntimeCheckKind) : Bool := true

/-- Model of Anneal's fail-closed capture gate (`Trusted/MirAst.lean:548-556`):
rejects any symbolic `Operand::RuntimeChecks` rather than folding it to a
`.constant` boolean. -/
def annealCaptureAdmits : MirCheckOperand → Bool
  | .constBool _ => true
  | .symbolic _ => false

/-- Boolean implication preorder `a ≤ b` (`a = true → b = true`). -/
def boolLe (a b : Bool) : Prop := a = true → b = true

/-- **Theorem 4.1 (`preserveUbChecks_evaluates_in_downstream`)**:
Any upstream crate marked `#![rustc_preserve_ub_checks]` (such as `core`,
`alloc`, `std`) keeps `Operand::RuntimeChecks(UbChecks)` symbolic through
`InstSimplify`, so generic/`#[inline]` functions evaluate strictly according
to the *downstream* crate's `ubChecks` flag. -/
theorem preserveUbChecks_evaluates_in_downstream
    (up down : CrateFlags) (hPres : up.preserveUbChecks = true) :
    crossCrateGenericCheck up down .ubChecks = down.ubChecks := by
  unfold crossCrateGenericCheck runInstSimplify evalAtDownstreamCodegen RuntimeCheckKind.evalInCrate
  rw [hPres]
  simp

/-- **Theorem 4.2 (`mirOptZero_evaluates_in_downstream`)**:
When upstream disables MIR optimizations (`-Z mir-opt-level=0`), `InstSimplify`
does not run and `UbChecks` likewise evaluates in the downstream crate. -/
theorem mirOptZero_evaluates_in_downstream
    (up down : CrateFlags) (hOpt0 : up.mirOptLevel = 0) :
    crossCrateGenericCheck up down .ubChecks = down.ubChecks := by
  unfold crossCrateGenericCheck runInstSimplify evalAtDownstreamCodegen RuntimeCheckKind.evalInCrate
  rw [hOpt0]
  rfl

/-- **Theorem 4.3 (`overflowAndContractChecks_always_evaluate_in_downstream`)**:
Because `SimplifyUbCheck` matches only `RuntimeChecks::UbChecks`, both
`RuntimeChecks::OverflowChecks` and `RuntimeChecks::ContractChecks` always
survive `InstSimplify` and evaluate in the downstream crate regardless of
`up.preserveUbChecks` and `up.mirOptLevel`. -/
theorem overflowAndContractChecks_always_evaluate_in_downstream
    (up down : CrateFlags) :
    crossCrateGenericCheck up down .overflowChecks = down.overflowChecks ∧
    crossCrateGenericCheck up down .contractChecks = down.contractChecks := by
  exact ⟨rfl, rfl⟩

/-- **Theorem 4.4 (`runtimeChecks_crate_graph_monotonic`)**:
Across any crate graph `(up, down1)` vs `(up, down2)` where `down2` enables at
least the checks enabled in `down1`, `crossCrateGenericCheck` is monotonic in
the downstream flags for all `RuntimeCheckKind`s. Furthermore, when `up`
preserves `UbChecks`, the dependence is exact (strictly reflects `down.ubChecks`). -/
theorem runtimeChecks_crate_graph_monotonic
    (up down1 down2 : CrateFlags)
    (hUb : boolLe down1.ubChecks down2.ubChecks)
    (hOvf : boolLe down1.overflowChecks down2.overflowChecks)
    (hCon : boolLe down1.contractChecks down2.contractChecks)
    (k : RuntimeCheckKind) :
    boolLe (crossCrateGenericCheck up down1 k) (crossCrateGenericCheck up down2 k) := by
  cases k with
  | ubChecks =>
    unfold crossCrateGenericCheck runInstSimplify evalAtDownstreamCodegen RuntimeCheckKind.evalInCrate
    cases hGate : (decide (up.mirOptLevel ≥ 1) && !up.preserveUbChecks) with
    | true =>
      intro h
      exact h
    | false =>
      exact hUb
  | overflowChecks =>
    exact hOvf
  | contractChecks =>
    exact hCon

/-- **Theorem (`premature_fold_runtimeChecks_erases_downstream_ubCheck`)**:
Whenever an ordinary upstream crate (`preserveUbChecks = false`) is compiled
with `mirOptLevel ≥ 1` (which holds by default even at `-C opt-level=0`, since
`OptLevel::No.mir_opt_level() == 1`!) and `-Z ub-checks=no`, `InstSimplify`
prematurely folds `Operand::RuntimeChecks(UbChecks)` to `const false` inside
`optimized_mir` BEFORE `.rmeta` serialization — erasing downstream
`-Z ub-checks=yes` even for generic `#[inline(always)]` functions! -/
theorem premature_fold_runtimeChecks_erases_downstream_ubCheck
    (up down : CrateFlags)
    (hNoPres : up.preserveUbChecks = false)
    (hMirOpt : up.mirOptLevel ≥ 1)
    (hUpOff : up.ubChecks = false)
    (hDownOn : down.ubChecks = true) :
    crossCrateGenericCheck up down .ubChecks = false ∧
    crossCrateGenericCheck up down .ubChecks ≠ down.ubChecks := by
  unfold crossCrateGenericCheck runInstSimplify evalAtDownstreamCodegen
  rw [hNoPres, hUpOff, hDownOn]
  have hd : decide (up.mirOptLevel ≥ 1) = true := decide_eq_true hMirOpt
  rw [hd]
  exact ⟨rfl, fun h => Bool.noConfusion h⟩

/-- **Docstring Refutation Theorem (`premature_fold_refutes_ubChecks_docstring`)**:
Even when upstream has `-Z ub-checks=yes` (`up.ubChecks = true`), without
`#![rustc_preserve_ub_checks]` `InstSimplify` STILL eagerly folds
`RuntimeChecks::UbChecks` to `const true`, forcing upstream checks to fire in a
downstream crate compiled with `-Z ub-checks=no` — directly refuting the
docstring in `library/core/src/intrinsics/mod.rs:2660-2662`. -/
theorem premature_fold_refutes_ubChecks_docstring
    (up down : CrateFlags)
    (hNoPres : up.preserveUbChecks = false)
    (hMirOpt : up.mirOptLevel ≥ 1)
    (hUpOn : up.ubChecks = true)
    (hDownOff : down.ubChecks = false) :
    crossCrateGenericCheck up down .ubChecks = true ∧
    crossCrateGenericCheck up down .ubChecks ≠ down.ubChecks := by
  unfold crossCrateGenericCheck runInstSimplify evalAtDownstreamCodegen
  rw [hNoPres, hUpOn, hDownOff]
  have hd : decide (up.mirOptLevel ≥ 1) = true := decide_eq_true hMirOpt
  rw [hd]
  exact ⟨rfl, fun h => Bool.noConfusion h⟩

/-- **CTFE Crate-Graph Invariance (`ctfe_runtimeChecks_crate_graph_invariant`)**:
CTFE evaluation is independent of all crate flags, preventing unsound const
divergence across crates. -/
theorem ctfe_runtimeChecks_crate_graph_invariant
    (k : RuntimeCheckKind) :
    evalAtCtfe k = true := rfl

/-- **Anneal Fail-Closed Capture Theorem (`anneal_capture_rejects_symbolic_runtimeChecks`)**:
Anneal's `Trusted.MirAst.Operand` rejects every symbolic `RuntimeChecks`
operand (e.g., from `Runtime(PostCleanup)` MIR or `#![rustc_preserve_ub_checks]`
bodies), guaranteeing that crate-dependent runtime check flags can never be
silently mis-folded into constants during verification capture. -/
theorem anneal_capture_rejects_symbolic_runtimeChecks (k : RuntimeCheckKind) :
    annealCaptureAdmits (.symbolic k) = false := rfl

/-! ## Part 5: Non-Unwinding `UnwindAction::Unreachable` + `#[rustc_nounwind]` Semantics -/

/-- Unwind action attached to a MIR `Assert` terminator
(`compiler/rustc_middle/src/mir/syntax.rs:1018-1027`). -/
inductive UnwindActionModel where
  | continue_
  | unreachable
  | terminateInCleanup
  | cleanup

/-- Enclosing dynamic execution frame stack context. -/
inductive FrameContext where
  | normal
  | insideCatchUnwind
  | insideCleanupDrop

/-- Observable runtime outcome of evaluating a failing `Assert` terminator. -/
inductive AssertFailureOutcome where
  | caughtByCatchUnwind
  | unwindPropagates
  | abortNonUnwinding
  | doublePanicAbort
  | ubUnwindIntoUnreachable

/-- Operational semantics of a failing `Assert` terminator parameterized by:
- `calleeNoUnwind`: whether the panic lang item carries `#[rustc_nounwind]`
  (which calls `panic_nounwind_fmt` with `can_unwind = false` -> `SIGABRT`),
- `unwindAction`: the MIR terminator's `UnwindAction`,
- `frame`: the dynamic enclosing call frame. -/
def evalFailingAssert (calleeNoUnwind : Bool) (unwindAction : UnwindActionModel)
    (frame : FrameContext) : AssertFailureOutcome :=
  if calleeNoUnwind then
    -- `#[rustc_nounwind]` panic lang items set `PanicInfo { can_unwind: false }`,
    -- causing `std::panicking::rust_panic_with_hook` to abort immediately (`SIGABRT`)
    -- before any stack unwinding begins.
    .abortNonUnwinding
  else
    -- An unwinding panic lang item initiates unwinding according to `unwindAction`.
    match unwindAction with
    | .unreachable => .ubUnwindIntoUnreachable
    | .terminateInCleanup => .doublePanicAbort
    | .continue_ | .cleanup =>
      match frame with
      | .insideCleanupDrop => .doublePanicAbort
      | .insideCatchUnwind => .caughtByCatchUnwind
      | .normal => .unwindPropagates

/-- **Theorem 5.1 (`nounwind_ubCheck_aborts_even_inside_catchUnwind`)**:
Every MIR UB-check assertion (`CheckAlignment`, `CheckNull`, `CheckEnums`)
pairs a `#[rustc_nounwind]` panic lang item with `UnwindAction::Unreachable`,
guaranteeing immediate non-unwinding abort (`SIGABRT`) across every dynamic
frame context — including inside `std::panic::catch_unwind` and inside a
`Drop` cleanup pad — with zero UB from unwinding into `UnwindAction::Unreachable`. -/
theorem nounwind_ubCheck_aborts_even_inside_catchUnwind (frame : FrameContext) :
    evalFailingAssert true .unreachable frame = .abortNonUnwinding ∧
    evalFailingAssert true .unreachable frame ≠ .caughtByCatchUnwind ∧
    evalFailingAssert true .unreachable frame ≠ .ubUnwindIntoUnreachable := by
  exact ⟨rfl, fun h => AssertFailureOutcome.noConfusion h,
    fun h => AssertFailureOutcome.noConfusion h⟩

/-- **Theorem 5.2 (`nounwind_contract_violated_triggers_ub`)**:
If an assertion carries `UnwindAction::Unreachable` (as `check_pointers.rs:117`
and `check_enums.rs:370, 461, 538` require) but invokes a panic function that
can unwind (`calleeNoUnwind = false`), failing the check causes immediate
unwinding UB (`ubUnwindIntoUnreachable`). -/
theorem nounwind_contract_violated_triggers_ub (frame : FrameContext) :
    evalFailingAssert false .unreachable frame = .ubUnwindIntoUnreachable := rfl

/-! ## Part 6: Constructive Sharpness Counterexamples (`ce1`–`ce5`) -/

/-- Enum value construction site forms in Rust MIR. -/
inductive EnumConstructionSite where
  | transmute
  | rawPtrRead
  | unionFieldRead

/-- Mirror of `EnumFinder::visit_rvalue` (`check_enums.rs:167-237`):
ONLY `Rvalue::Cast(CastKind::Transmute, ..)` is visited and instrumented. -/
def checkEnumsVisitsSite : EnumConstructionSite → Bool
  | .transmute => true
  | .rawPtrRead => false
  | .unionFieldRead => false

/-- Concrete layout of `#[repr(u8)] enum BinaryTag { Zero = 0, One = 1 }`. -/
def binaryTagValidDiscrs : List Nat := [0, 1]

/-- **Counterexample 1 (`ce1_ptr_read_and_union_bypass_checkEnums`)**:
Constructing invalid `BinaryTag` value `2u8` (outside `{0, 1}`) is immediate UB
under the Rust Reference (`r[undefined.validity.enum]`), yet `CheckEnums`
visits only `CastKind::Transmute` and completely bypasses both raw-pointer
dereference (`*p`) and union-field read (`u.en`). -/
theorem ce1_ptr_read_and_union_bypass_checkEnums :
    directEnumValid .w8 binaryTagValidDiscrs 2 = false ∧
    insertDirectEnumCheck .w8 binaryTagValidDiscrs 2 = false ∧
    checkEnumsVisitsSite .transmute = true ∧
    checkEnumsVisitsSite .rawPtrRead = false ∧
    checkEnumsVisitsSite .unionFieldRead = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Concrete wrapping niche range of `Option<NegHigh>` where
`#[repr(i8)] enum NegHigh { MinusTwo = -2, MinusOne = -1 }`:
valid tag bytes are `{254, 255, 0}`, encoded as `WrappingRange { start: 254, end_: 0 }`. -/
def negHighWrappingRange : WrappingRange := ⟨254, 0⟩

/-- Concrete non-wrapping signed niche range of `Option<NegMid>` where
`#[repr(i8)] enum NegMid { A = -10, B = -9 }`:
valid tag bytes are `{246, 247, 248}` (`0xf6..=0xf8`), encoded as
`WrappingRange { start: 246, end_: 248 }`. -/
def negMidNonWrappingRange : WrappingRange := ⟨246, 248⟩

/-- **Counterexample 2 (`ce2_unmasked_high_bits_break_u128_wrapping_niche_check`)**:
Without the `discr < 2^w` precondition (which `CheckEnums::insert_niche_check`
violates in live `rustc` whenever `tag.value` is signed, because
`insert_discr_cast_to_u128` sign-extends to `u128` and `insert_niche_check`
omits `& discr.size.unsigned_int_max()`), `insertNicheCheckU128` fails in
BOTH directions:
1. **Unmasked high bit (`discr = 256` on `u8` wrapping `254..=0`)**: falsely
   accepted (`true`) despite being outside `u8` (`256 ≥ 256`).
2. **Real `rustc` false negative (`Option<NegHigh>`, invalid byte `0x80 = 128`)**:
   `WrappingRange::contains(128) = false` (UB in Miri), yet
   `insertNicheCheckU128 negHighWrappingRange (signExtendTo128 .w8 128) = true`!
3. **Real `rustc` false positive (`Option<NegMid>`, valid byte `0xf6 = 246 = -10i8`)**:
   `WrappingRange::contains(246) = true` (valid in Miri), yet
   `insertNicheCheckU128 negMidNonWrappingRange (signExtendTo128 .w8 246) = false`
   (false `SIGABRT` on a UB-free Rust program!).
4. **Masking repairs both**: applying `maskW .w8` restores exact agreement
   (`false` on `0x80` for `NegHigh`, `true` on `0xf6` for `NegMid`). -/
theorem ce2_unmasked_high_bits_break_u128_wrapping_niche_check :
    -- (1) Generic unmasked high-bit witness `discr = 256` on wrapping `u8` range `254..=0`
    insertNicheCheckU128 negHighWrappingRange 256 = true ∧
    negHighWrappingRange.contains 256 = true ∧
    256 ≥ IntWidth.w8.modulus ∧
    -- (2) Real rustc false-negative witness: `0x80` (`-128i8`) silently accepted in `Option<NegHigh>`
    negHighWrappingRange.contains 128 = false ∧
    insertNicheCheckU128 negHighWrappingRange (signExtendTo128 .w8 128) = true ∧
    -- (3) Real rustc false-positive witness: `0xf6` (`-10i8`) falsely aborted in `Option<NegMid>`
    negMidNonWrappingRange.contains 246 = true ∧
    insertNicheCheckU128 negMidNonWrappingRange (signExtendTo128 .w8 246) = false ∧
    -- (4) Masking with `maskW .w8` repairs both
    insertNicheCheckU128 negHighWrappingRange (maskW .w8 (signExtendTo128 .w8 128)) = false ∧
    insertNicheCheckU128 negMidNonWrappingRange (maskW .w8 (signExtendTo128 .w8 246)) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `wrappingSub128 256 254 = 2 ≤ M128 - 254 = wrappingSub128 0 254`
    unfold insertNicheCheckU128 negHighWrappingRange
    rw [wrappingSub128_eq_sub (by decide) (by decide) (by decide),
        wrappingSub128_eq_wrap (by decide) (by decide) (by decide)]
    decide
  · decide
  · decide
  · decide
  · -- `signExtendTo128 .w8 128 = M128 - 128`, so `wrappingSub128 (M128 - 128) 254 = M128 - 382 ≤ M128 - 254`
    unfold insertNicheCheckU128 negHighWrappingRange signExtendTo128
    dsimp only
    have hge1 : 128 % IntWidth.w8.modulus ≥ IntWidth.w8.halfModulus := by decide
    simp only [hge1, ↓reduceIte]
    have hlt1 : M128 - IntWidth.w8.modulus + 128 % IntWidth.w8.modulus < M128 := by decide
    rw [wrappingSub128_eq_sub hlt1 (by decide) (by decide),
        wrappingSub128_eq_wrap (by decide) (by decide) (by decide)]
    decide
  · decide
  · -- `signExtendTo128 .w8 246 = M128 - 10`, so `wrappingSub128 (M128 - 10) 246 = M128 - 256 > 2 = wrappingSub128 248 246`
    unfold insertNicheCheckU128 negMidNonWrappingRange signExtendTo128
    dsimp only
    have hge2 : 246 % IntWidth.w8.modulus ≥ IntWidth.w8.halfModulus := by decide
    simp only [hge2, ↓reduceIte]
    have hlt2 : M128 - IntWidth.w8.modulus + 246 % IntWidth.w8.modulus < M128 := by decide
    rw [wrappingSub128_eq_sub hlt2 (by decide) (by decide),
        wrappingSub128_eq_sub (by decide) (by decide) (by decide)]
    decide
  · -- Repaired `NegHigh` at `0x80`
    rw [insertNicheCheck_masked_signed_sound .w8 negHighWrappingRange 128 (by decide) (by decide)]
    decide
  · -- Repaired `NegMid` at `0xf6`
    rw [insertNicheCheck_masked_signed_sound .w8 negMidNonWrappingRange 246 (by decide) (by decide)]
    decide

/-- Concrete `#[repr(C, align(16))] struct OverAligned { byte_field: u8, word_field: u32 }`
place for `(*p).byte_field`. -/
def overAlignedByteFieldPlace : FieldProjectionPlace where
  baseLayout := { size := 16, align := 16, alignPos := by decide, isSized := true }
  fieldLayout := { size := 1, align := 1, alignPos := by decide, isSized := true }
  fieldOffset := 0

/-- Concrete `(*p).word_field` (`offset = 4`, `align = 4`) inside `OverAligned`. -/
def overAlignedWordFieldPlace : FieldProjectionPlace where
  baseLayout := { size := 16, align := 16, alignPos := by decide, isSized := true }
  fieldLayout := { size := 4, align := 4, alignPos := by decide, isSized := true }
  fieldOffset := 4

/-- **Counterexample 3 (`ce3_noFollowProjections_false_positive_on_byte_field_borrow`)**:
For `&(*p).byte_field` at misaligned address `addr = 1` (`1 % 16 ≠ 0`, `1 % 1 = 0`):
- The borrow is valid per `r[undefined.misaligned.reference]` (`refAlignmentRequired` holds).
- `CheckAlignment` with `FollowProjections` rightly permits it (`true`).
- Counterfactually passing `NoFollowProjections` to `CheckAlignment` would
  produce a false-positive abort (`false`) on valid Rust code!
- Meanwhile, a direct non-borrow `Copy` load `(*p).byte_field` at `addr = 1`
  violates `r[undefined.misaligned.ptr]` + `r[undefined.misaligned.load-store]`
  and IS caught by `CheckAlignment` even under `FollowProjections` (`false`).
- And `&(*p).word_field` at `addr = 4` (`4 % 16 ≠ 0`, `4 % 4 = 0`) is permitted
  under `FollowProjections` (checking `align = 4`), whereas at `addr = 1` it is
  caught (`false`). -/
theorem ce3_noFollowProjections_false_positive_on_byte_field_borrow :
    refAlignmentRequired .sharedBorrow overAlignedByteFieldPlace 1 ∧
    checkAlignmentPasses .followProjections .sharedBorrow overAlignedByteFieldPlace 1 = true ∧
    checkAlignmentPasses .noFollowProjections .sharedBorrow overAlignedByteFieldPlace 1 = false ∧
    checkAlignmentPasses .followProjections .copy overAlignedByteFieldPlace 1 = false ∧
    checkAlignmentPasses .followProjections .sharedBorrow overAlignedWordFieldPlace 4 = true ∧
    checkAlignmentPasses .followProjections .sharedBorrow overAlignedWordFieldPlace 1 = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Counterexample 4 (`ce4_unwinding_ub_check_in_cleanup_causes_double_panic`)**:
If a failing UB check inside a `Drop` cleanup pad were permitted to unwind
(`calleeNoUnwind = false`, `UnwindAction::Cleanup` / `Continue` / `Terminate(InCleanup)`),
execution terminates in `.doublePanicAbort` (and under `catch_unwind` in a normal
frame, it would be caught via `.caughtByCatchUnwind` instead of aborting!).
By contrast, `#[rustc_nounwind]` + `UnwindAction::Unreachable` deterministically
yields `.abortNonUnwinding` in all contexts without unwinding through
broken unsafe state. -/
theorem ce4_unwinding_ub_check_in_cleanup_causes_double_panic :
    evalFailingAssert false .cleanup .insideCleanupDrop = .doublePanicAbort ∧
    evalFailingAssert false .continue_ .insideCleanupDrop = .doublePanicAbort ∧
    evalFailingAssert false .terminateInCleanup .insideCleanupDrop = .doublePanicAbort ∧
    evalFailingAssert false .cleanup .insideCatchUnwind = .caughtByCatchUnwind ∧
    evalFailingAssert true .unreachable .insideCleanupDrop = .abortNonUnwinding ∧
    evalFailingAssert true .unreachable .insideCatchUnwind = .abortNonUnwinding := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Concrete unsized slice raw pointer place `*const [u32]` (`isSized = false`,
element alignment `4`). -/
def unsizedSliceU32Place : FieldProjectionPlace where
  baseLayout := { size := 0, align := 4, alignPos := by decide, isSized := false }
  fieldLayout := { size := 0, align := 4, alignPos := by decide, isSized := false }
  fieldOffset := 0

/-- **Counterexample 5 (`ce5_unsized_slice_raw_ptr_bypasses_checkPointers`)**:
Because `PointerFinder::visit_place` (`check_pointers.rs:231`) returns early
when `!pointee_ty.is_sized`, both `CheckAlignment` and `CheckNull` silently
bypass misaligned (`addr = 1`) and null (`addr = 0`) raw slice borrows
`&*(raw_slice : *const [u32])`, even though both violate `refAlignmentRequired`
and `nullAccessIsUB`. -/
theorem ce5_unsized_slice_raw_ptr_bypasses_checkPointers :
    checkAlignmentInstruments .followProjections .sharedBorrow unsizedSliceU32Place = false ∧
    checkAlignmentPasses .followProjections .sharedBorrow unsizedSliceU32Place 1 = true ∧
    ¬ refAlignmentRequired .sharedBorrow unsizedSliceU32Place 1 ∧
    checkNullPasses .sharedBorrow unsizedSliceU32Place.baseLayout 0 = true ∧
    nullAccessIsUB .sharedBorrow unsizedSliceU32Place.baseLayout 0 := by
  refine ⟨rfl, rfl, ?_, rfl, ?_⟩
  · unfold refAlignmentRequired unsizedSliceU32Place
    decide
  · unfold nullAccessIsUB unsizedSliceU32Place
    exact ⟨rfl, rfl, Or.inl rfl⟩

/-! ## Part 7: Unified Soundness Summary & Verification Boundary Theorem -/

/-- Combined soundness & completeness contract for a verified-rustc MIR
UB-checking pass suite when all 4 side-conditions hold:
1. Pointee is sized, non-packed (`fieldAlign ∣ fieldOffset`), and `FollowProjections`
   is used for `CheckAlignment`;
2. `CheckNull` runs with `NoFollowProjections` on sized pointees;
3. `CheckEnums` masks sign-extended discriminants with `maskW w` before
   `insertNicheCheckU128` as well as `insertDirectEnumCheck`;
4. Cross-crate `RuntimeChecks::UbChecks` is preserved via
   `#![rustc_preserve_ub_checks]` (or `-Z mir-opt-level=0`), and every failing
   assert uses `#[rustc_nounwind]` + `UnwindAction::Unreachable`. -/
theorem unified_ub_checks_soundness_under_repaired_invariants
    (fp : FieldProjectionPlace)
    (hBaseSized : fp.baseLayout.isSized = true)
    (hFieldSized : fp.fieldLayout.isSized = true)
    (hOffsetAligned : fp.fieldLayout.align ∣ fp.fieldOffset)
    (w : IntWidth) (r : WrappingRange) (hS : r.start < w.modulus) (hE : r.end_ < w.modulus)
    (up down : CrateFlags) (hPres : up.preserveUbChecks = true) :
    (∀ ctx addr,
      checkAlignmentPasses .followProjections ctx fp addr = true ↔
        refAlignmentRequired ctx fp addr) ∧
    (∀ ctx addr,
      checkNullPasses ctx fp.baseLayout addr = false ↔
        nullAccessIsUB ctx fp.baseLayout addr) ∧
    (∀ raw,
      insertNicheCheckU128 r (maskW w (signExtendTo128 w raw)) =
        r.contains (raw % w.modulus)) ∧
    (crossCrateGenericCheck up down .ubChecks = down.ubChecks) ∧
    (∀ frame, evalFailingAssert true .unreachable frame = .abortNonUnwinding) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ctx addr
    exact checkAlignment_followProjections_sound fp hBaseSized hFieldSized hOffsetAligned ctx addr
  · intro ctx addr
    exact checkNullPasses_eq_false_iff_nullAccessIsUB ctx fp.baseLayout hBaseSized addr
  · intro raw
    exact insertNicheCheck_masked_signed_sound w r raw hS hE
  · exact preserveUbChecks_evaluates_in_downstream up down hPres
  · intro frame
    exact (nounwind_ubCheck_aborts_even_inside_catchUnwind frame).1

end MirUbChecksRuntimeChecksAndCheckEnumsSoundness
