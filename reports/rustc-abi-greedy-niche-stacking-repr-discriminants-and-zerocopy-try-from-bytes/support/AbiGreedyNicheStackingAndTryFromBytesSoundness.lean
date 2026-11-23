/-!
# Kernel-Checked Lean v4.34.1 Formalization:
# `rustc_abi` Greedy Zero-Ward `Niche::reserve` Multi-Level Niche Stacking,
# `#[repr(u8)]` / `#[repr(C, u8)]` / `#[repr(C)]` Enum Layouts, `E0732`,
# and `zerocopy::TryFromBytes` Tag-First Bit-Validity Soundness

Primary-source anchors:
- `rust-lang/rust` (`compiler/rustc_abi/src/lib.rs`, `compiler/rustc_abi/src/layout.rs`,
  `compiler/rustc_ty_utils/src/layout.rs`, `compiler/rustc_middle/src/ty/layout.rs`,
  `compiler/rustc_hir_analysis/src/check/check.rs`,
  `compiler/rustc_const_eval/src/interpret/discriminant.rs`)
- `google/zerocopy` (`zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs`,
  `zerocopy/zerocopy-derive/src/derive/project.rs`, `zerocopy/zerocopy-derive/src/repr.rs`,
  `zerocopy/src/lib.rs`, `zerocopy/src/impls.rs`)
- `joshlf/anneal` (`vendor/lean-miri/Miri/ABI/WrappingRange.lean`,
  `vendor/lean-miri/Miri/Interpreter/Discriminant.lean`,
  `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`)

Purity invariants enforced throughout this module:
- Every `def` is marked `noncomputable def` or `private noncomputable def`.
- Zero `deriving` clauses, zero section-wide noncomputable blocks, zero incomplete proof holes.
- Constructive axioms only (`propext`, `Quot.sound`), avoiding reflection or classical shortcuts.
- Zero `._unsafe_rec` kernel constants.
-/

namespace AbiNicheStacking

/-! ## Section 1: Pure `Nat` and `BitVec` Modular Arithmetic Foundations -/

private theorem nat_sub_lt_of_le_of_lt {a b c : Nat} (hle : b ≤ a) (hlt : a < c) :
    a - b < c - b := by
  have h1 : a - b + b = a := Nat.sub_add_cancel hle
  have hcb : b ≤ c := Nat.le_trans hle (Nat.le_of_lt hlt)
  have h2 : c - b + b = c := Nat.sub_add_cancel hcb
  rw [← h1, ← h2] at hlt
  exact Nat.lt_of_add_lt_add_right hlt

private theorem nat_le_of_add_le_add_right {a b c : Nat} (h : a + c ≤ b + c) : a ≤ b :=
  Nat.le_of_add_le_add_right h

private theorem nat_sub_le_sub_right {a b c : Nat} (h : a ≤ b) : a - c ≤ b - c :=
  Nat.sub_le_sub_right h c

private theorem pow2_pos (w : Nat) : 0 < 2 ^ w :=
  Nat.pow_pos (Nat.succ_pos 1)

private theorem pow2_ge_one (w : Nat) : 1 ≤ 2 ^ w :=
  pow2_pos w

private theorem pow2_ge_two {w : Nat} (hw : 0 < w) : 2 ≤ 2 ^ w := by
  cases w with
  | zero => contradiction
  | succ k =>
    have hpos : 1 ≤ 2 ^ k := pow2_ge_one k
    rw [Nat.pow_succ]
    exact Nat.mul_le_mul_right 2 hpos

private theorem pow2_sub_one_lt {w : Nat} : 2 ^ w - 1 < 2 ^ w :=
  Nat.sub_lt (pow2_pos w) (Nat.succ_pos 0)

private theorem nat_ble_true_iff (a b : Nat) : Nat.ble a b = true ↔ a ≤ b :=
  iff_of_eq Nat.ble_eq

private theorem nat_ble_false_iff (a b : Nat) : Nat.ble a b = false ↔ b < a := by
  constructor
  · intro h
    cases Nat.lt_or_ge b a with
    | inl hlt => exact hlt
    | inr hle =>
      have ht : Nat.ble a b = true := (nat_ble_true_iff a b).mpr hle
      rw [ht] at h
      contradiction
  · intro hlt
    cases hb : Nat.ble a b with
    | false => rfl
    | true =>
      have hle : a ≤ b := (nat_ble_true_iff a b).mp hb
      exact False.elim (Nat.not_lt_of_ge hle hlt)

private theorem nat_blt_true_iff (a b : Nat) : Nat.blt a b = true ↔ a < b := by
  unfold Nat.blt
  exact nat_ble_true_iff (Nat.succ a) b

private theorem nat_blt_false_iff (a b : Nat) : Nat.blt a b = false ↔ b ≤ a := by
  unfold Nat.blt
  constructor
  · intro h
    have hlt := (nat_ble_false_iff (Nat.succ a) b).mp h
    exact Nat.le_of_lt_succ hlt
  · intro hle
    exact (nat_ble_false_iff (Nat.succ a) b).mpr (Nat.lt_succ_of_le hle)

private theorem bool_and_eq_true (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

private theorem bool_or_eq_true (a b : Bool) : (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp

private theorem bv_ofNat_zero_toNat (w : Nat) : (BitVec.ofNat w 0).toNat = 0 := by
  rw [BitVec.toNat_ofNat, Nat.zero_mod]

private theorem bv_ofNat_one_toNat {w : Nat} (hw : 0 < w) : (BitVec.ofNat w 1).toNat = 1 := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (pow2_ge_two hw)

private theorem bv_add_right_cancel {w : Nat} {a b c : BitVec w} (h : a + c = b + c) : a = b := by
  have h2 := congrArg (fun z => z - c) h
  rw [BitVec.add_sub_cancel, BitVec.add_sub_cancel] at h2
  exact h2

private theorem bv_sub_right_cancel {w : Nat} {a b c : BitVec w} (h : a - c = b - c) : a = b := by
  have h2 := congrArg (fun z => z + c) h
  rw [BitVec.sub_add_cancel, BitVec.sub_add_cancel] at h2
  exact h2

private theorem bv_add_sub_assoc {w : Nat} (a b c : BitVec w) : (a + b) - c = a + (b - c) := by
  apply bv_add_right_cancel (c := c)
  rw [BitVec.sub_add_cancel, BitVec.add_assoc, BitVec.sub_add_cancel]

private theorem bv_add_sub_comm_left {w : Nat} (a b c : BitVec w) : (a + b) - c = (a - c) + b := by
  rw [BitVec.add_comm a b, bv_add_sub_assoc, BitVec.add_comm b (a - c)]

private theorem bv_sub_sub_rev {w : Nat} (a b c : BitVec w) : a - (b - c) = (a - b) + c := by
  apply bv_add_right_cancel (c := b - c)
  rw [BitVec.sub_add_cancel, BitVec.add_assoc, BitVec.add_comm c (b - c),
    BitVec.sub_add_cancel, BitVec.sub_add_cancel]

private theorem bv_sub_add_sub_assoc {w : Nat} (a b c : BitVec w) :
    a - c = (a - b) + (b - c) := by
  apply bv_add_right_cancel (c := c)
  rw [BitVec.sub_add_cancel, BitVec.add_assoc, BitVec.sub_add_cancel, BitVec.sub_add_cancel]

private theorem bv_sub_toNat_of_le {w : Nat} {a b : BitVec w} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  rw [BitVec.toNat_sub]
  have hb : b.toNat ≤ 2 ^ w := Nat.le_of_lt b.isLt
  have h1 : 2 ^ w - b.toNat + a.toNat = 2 ^ w + (a.toNat - b.toNat) := by
    have ha1 : a.toNat - b.toNat + b.toNat = a.toNat := Nat.sub_add_cancel h
    have ha2 : 2 ^ w - b.toNat + b.toNat = 2 ^ w := Nat.sub_add_cancel hb
    have step : (2 ^ w - b.toNat + a.toNat) + b.toNat = (2 ^ w + (a.toNat - b.toNat)) + b.toNat := by
      rw [Nat.add_assoc, Nat.add_comm a.toNat b.toNat, ← Nat.add_assoc, ha2, Nat.add_assoc, ha1]
    exact Nat.add_right_cancel step
  rw [h1, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
  have hlt : a.toNat - b.toNat < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.sub_le a.toNat b.toNat) a.isLt
  exact Nat.mod_eq_of_lt hlt

private theorem bv_sub_toNat_of_lt {w : Nat} {a b : BitVec w} (h : a.toNat < b.toNat) :
    (a - b).toNat = 2 ^ w - b.toNat + a.toNat := by
  rw [BitVec.toNat_sub]
  have hb : b.toNat ≤ 2 ^ w := Nat.le_of_lt b.isLt
  have hsum : 2 ^ w - b.toNat + a.toNat < 2 ^ w := by
    have step : 2 ^ w - b.toNat + a.toNat < 2 ^ w - b.toNat + b.toNat :=
      Nat.add_lt_add_left h (2 ^ w - b.toNat)
    rw [Nat.sub_add_cancel hb] at step
    exact step
  exact Nat.mod_eq_of_lt hsum

private theorem bv_add_toNat_lt {w : Nat} {a b : BitVec w} (h : a.toNat + b.toNat < 2 ^ w) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt h

private theorem bv_max_add_one {w : Nat} (hw : 0 < w) :
    BitVec.ofNat w (2 ^ w - 1) + BitVec.ofNat w 1 = 0#w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt pow2_sub_one_lt, Nat.mod_eq_of_lt (pow2_ge_two hw)]
  rw [Nat.sub_add_cancel (pow2_ge_one w), Nat.mod_self]
  rfl

private theorem bv_zero_sub_one {w : Nat} (hw : 0 < w) :
    (0#w : BitVec w) - BitVec.ofNat w 1 = BitVec.ofNat w (2 ^ w - 1) := by
  apply bv_add_right_cancel (c := BitVec.ofNat w 1)
  rw [BitVec.sub_add_cancel, bv_max_add_one hw]

/-! ## Section 2: `BitWidth` and `WrappingRange` Algebra -/

/-- Supported integer/pointer machine bit widths matching `rustc_abi::Integer` and `Pointer`. -/
inductive BitWidth where
  | w8
  | w16
  | w32
  | w64
  | w128

/-- Number of bits for a `BitWidth`. -/
noncomputable def BitWidth.bits : BitWidth → Nat
  | .w8 => 8
  | .w16 => 16
  | .w32 => 32
  | .w64 => 64
  | .w128 => 128

/-- Number of bytes for a `BitWidth`. -/
noncomputable def BitWidth.bytes : BitWidth → Nat
  | .w8 => 1
  | .w16 => 2
  | .w32 => 4
  | .w64 => 8
  | .w128 => 16

theorem BitWidth.bits_pos (bw : BitWidth) : 0 < bw.bits := by
  cases bw <;> exact Nat.succ_pos _

theorem BitWidth.bits_eq_bytes_mul_eight (bw : BitWidth) : bw.bits = bw.bytes * 8 := by
  cases bw <;> rfl

/-- Inclusive modular interval `[start, finish]` on `BitVec w`, matching
`rustc_abi::WrappingRange { start, end }` (`compiler/rustc_abi/src/lib.rs:1430-1433`).
If `start.toNat ≤ finish.toNat`, the interval is `{x | start ≤ x ≤ finish}`;
if `finish.toNat < start.toNat`, it wraps around zero: `{x | start ≤ x ∨ x ≤ finish}`. -/
structure WrappingRange (w : Nat) where
  start : BitVec w
  finish : BitVec w

/-- Construct the full range `0..=2^w - 1` (`WrappingRange::full`). -/
noncomputable def WrappingRange.full (w : Nat) : WrappingRange w :=
  ⟨BitVec.ofNat w 0, BitVec.ofNat w (2 ^ w - 1)⟩

/-- Replace the `start` bound (`WrappingRange::with_start`). -/
noncomputable def WrappingRange.withStart {w : Nat} (r : WrappingRange w) (s : BitVec w) :
    WrappingRange w :=
  ⟨s, r.finish⟩

/-- Replace the `finish` bound (`WrappingRange::with_end`). -/
noncomputable def WrappingRange.withFinish {w : Nat} (r : WrappingRange w) (e : BitVec w) :
    WrappingRange w :=
  ⟨r.start, e⟩

/-- Membership check matching `rustc_abi::WrappingRange::contains`. -/
noncomputable def WrappingRange.contains {w : Nat} (r : WrappingRange w) (x : BitVec w) : Bool :=
  if Nat.ble r.start.toNat r.finish.toNat then
    Nat.ble r.start.toNat x.toNat && Nat.ble x.toNat r.finish.toNat
  else
    Nat.ble r.start.toNat x.toNat || Nat.ble x.toNat r.finish.toNat

/-- Full-range check matching `rustc_abi::WrappingRange::is_full_for`. -/
noncomputable def WrappingRange.isFull {w : Nat} (r : WrappingRange w) : Bool :=
  r.start == r.finish + BitVec.ofNat w 1

/-- Number of invalid bit patterns outside `r`, matching `Niche::available`. -/
noncomputable def WrappingRange.available {w : Nat} (r : WrappingRange w) : Nat :=
  (r.start - r.finish - BitVec.ofNat w 1).toNat

/-- Normalized width `(r.finish - r.start).toNat` after shifting by `-r.start`. -/
noncomputable def WrappingRange.normEnd {w : Nat} (r : WrappingRange w) : Nat :=
  (r.finish - r.start).toNat

/-- Range containment check matching `rustc_abi::WrappingRange::contains_range`. -/
noncomputable def WrappingRange.containsRange {w : Nat} (r other : WrappingRange w) : Bool :=
  if r.isFull then
    true
  else
    let maxOff := (r.finish - r.start).toNat
    let oStart := (other.start - r.start).toNat
    let oEnd := (other.finish - r.start).toNat
    Nat.ble oStart oEnd && Nat.ble oEnd maxOff

/-- Fundamental coordinate-shift theorem: a modular value `x : BitVec w` belongs to
`r : WrappingRange w` iff its shifted offset `(x - r.start).toNat` does not exceed
`(r.finish - r.start).toNat`. This holds unconditionally for both non-wrapping and
wrapping intervals, including full ranges. -/
theorem WrappingRange.contains_iff_shift {w : Nat} (r : WrappingRange w) (x : BitVec w) :
    r.contains x = true ↔ (x - r.start).toNat ≤ (r.finish - r.start).toNat := by
  unfold WrappingRange.contains
  cases hsf : Nat.ble r.start.toNat r.finish.toNat with
  | true =>
    have hsle : r.start.toNat ≤ r.finish.toNat := (nat_ble_true_iff _ _).mp hsf
    simp only [ite_true, bool_and_eq_true, nat_ble_true_iff]
    rw [bv_sub_toNat_of_le hsle]
    cases Nat.lt_or_ge x.toNat r.start.toNat with
    | inl hxlt =>
      rw [bv_sub_toNat_of_lt hxlt]
      constructor
      · intro ⟨hsx, _⟩
        exact False.elim (Nat.not_lt_of_ge hsx hxlt)
      · intro hle
        have hbound : r.finish.toNat - r.start.toNat < 2 ^ w - r.start.toNat :=
          nat_sub_lt_of_le_of_lt hsle r.finish.isLt
        have hge : 2 ^ w - r.start.toNat ≤ 2 ^ w - r.start.toNat + x.toNat :=
          Nat.le_add_right _ _
        exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hge hle) hbound)
    | inr hsx =>
      rw [bv_sub_toNat_of_le hsx]
      constructor
      · intro ⟨_, hxf⟩
        exact nat_sub_le_sub_right hxf
      · intro hsub
        refine ⟨hsx, ?_⟩
        have hadd := Nat.add_le_add_right hsub r.start.toNat
        rw [Nat.sub_add_cancel hsx, Nat.sub_add_cancel hsle] at hadd
        exact hadd
  | false =>
    have hflt : r.finish.toNat < r.start.toNat := (nat_ble_false_iff _ _).mp hsf
    simp only [Bool.false_eq_true, ite_false, bool_or_eq_true, nat_ble_true_iff]
    rw [bv_sub_toNat_of_lt hflt]
    cases Nat.lt_or_ge x.toNat r.start.toNat with
    | inl hxlt =>
      rw [bv_sub_toNat_of_lt hxlt]
      constructor
      · intro h
        cases h with
        | inl hsx => exact False.elim (Nat.not_lt_of_ge hsx hxlt)
        | inr hxf => exact Nat.add_le_add_left hxf (2 ^ w - r.start.toNat)
      · intro hle
        right
        exact Nat.le_of_add_le_add_left hle
    | inr hsx =>
      rw [bv_sub_toNat_of_le hsx]
      constructor
      · intro _
        have hxl : x.toNat - r.start.toNat < 2 ^ w - r.start.toNat :=
          nat_sub_lt_of_le_of_lt hsx x.isLt
        exact Nat.le_trans (Nat.le_of_lt hxl) (Nat.le_add_right _ _)
      · intro _
        left
        exact hsx

/-- Available niche count equals `(2^w - 1) - (r.finish - r.start).toNat`. -/
theorem WrappingRange.available_eq_complement {w : Nat} (hw : 0 < w) (r : WrappingRange w) :
    r.available = (2 ^ w - 1) - r.normEnd := by
  unfold WrappingRange.available WrappingRange.normEnd
  have hsub : r.start - r.finish - BitVec.ofNat w 1 =
      BitVec.ofNat w (2 ^ w - 1) - (r.finish - r.start) := by
    apply bv_add_right_cancel (c := BitVec.ofNat w 1)
    rw [BitVec.sub_add_cancel]
    apply bv_add_right_cancel (c := r.finish - r.start)
    rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat w 1), ← BitVec.add_assoc,
      BitVec.sub_add_cancel, bv_max_add_one hw]
    have hc : r.start - r.finish + (r.finish - r.start) = 0#w := by
      rw [← bv_sub_add_sub_assoc, BitVec.sub_self]
    exact hc
  have hmaxToNat : (BitVec.ofNat w (2 ^ w - 1)).toNat = 2 ^ w - 1 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt pow2_sub_one_lt
  have hle : (r.finish - r.start).toNat ≤ (BitVec.ofNat w (2 ^ w - 1)).toNat := by
    rw [hmaxToNat]
    exact Nat.le_pred_of_lt (r.finish - r.start).isLt
  rw [hsub, bv_sub_toNat_of_le hle, hmaxToNat]

/-- Capacity exhaustion equivalence: `r.available = 0 ↔ r.isFull = true`. -/
theorem WrappingRange.available_zero_iff_isFull {w : Nat} (hw : 0 < w) (r : WrappingRange w) :
    r.available = 0 ↔ r.isFull = true := by
  rw [WrappingRange.available_eq_complement hw]
  unfold WrappingRange.isFull WrappingRange.normEnd
  constructor
  · intro hzero
    have hge : 2 ^ w - 1 ≤ (r.finish - r.start).toNat := Nat.le_of_sub_eq_zero hzero
    have hle : (r.finish - r.start).toNat ≤ 2 ^ w - 1 :=
      Nat.le_pred_of_lt (r.finish - r.start).isLt
    have heq : (r.finish - r.start).toNat = 2 ^ w - 1 := Nat.le_antisymm hle hge
    have hbv : r.finish - r.start = BitVec.ofNat w (2 ^ w - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pow2_sub_one_lt]
    have hfull : r.start = r.finish + BitVec.ofNat w 1 := by
      have hstep := congrArg (fun z => z + r.start + BitVec.ofNat w 1) hbv
      rw [BitVec.sub_add_cancel] at hstep
      rw [BitVec.add_assoc, BitVec.add_comm r.start, ← BitVec.add_assoc, bv_max_add_one hw,
        BitVec.zero_add] at hstep
      exact hstep.symm
    exact beq_iff_eq.mpr hfull
  · intro hfull
    have heq : r.start = r.finish + BitVec.ofNat w 1 := beq_iff_eq.mp hfull
    have hsub : r.finish - r.start = BitVec.ofNat w (2 ^ w - 1) := by
      rw [heq, ← BitVec.sub_sub, BitVec.sub_self, bv_zero_sub_one hw]
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pow2_sub_one_lt, Nat.sub_self]

/-- Full range contains every bit pattern `x : BitVec w`. -/
theorem WrappingRange.contains_of_isFull {w : Nat} (hw : 0 < w) (r : WrappingRange w)
    (hf : r.isFull = true) (x : BitVec w) : r.contains x = true := by
  rw [WrappingRange.contains_iff_shift]
  have hav : r.available = 0 := (WrappingRange.available_zero_iff_isFull hw r).mpr hf
  rw [WrappingRange.available_eq_complement hw] at hav
  have hge : 2 ^ w - 1 ≤ (r.finish - r.start).toNat := Nat.le_of_sub_eq_zero hav
  have hx : (x - r.start).toNat ≤ 2 ^ w - 1 := Nat.le_pred_of_lt (x - r.start).isLt
  exact Nat.le_trans hx hge

/-- Equivalence between `0 < r.available` and existence of an unused niche pattern. -/
theorem WrappingRange.available_pos_iff_exists_niche {w : Nat} (hw : 0 < w) (r : WrappingRange w) :
    0 < r.available ↔ ∃ x : BitVec w, r.contains x = false := by
  constructor
  · intro hpos
    refine ⟨r.finish + BitVec.ofNat w 1, ?_⟩
    cases hc : r.contains (r.finish + BitVec.ofNat w 1) with
    | false => rfl
    | true =>
      have hsh : ((r.finish + BitVec.ofNat w 1) - r.start).toNat ≤ (r.finish - r.start).toNat :=
        (WrappingRange.contains_iff_shift r _).mp hc
      have hnot : (r.finish - r.start).toNat < 2 ^ w - 1 := by
        have hav := WrappingRange.available_eq_complement hw r
        rw [hav] at hpos
        cases Nat.lt_or_ge r.normEnd (2 ^ w - 1) with
        | inl h => exact h
        | inr h =>
          have h0 : (2 ^ w - 1) - r.normEnd = 0 := Nat.sub_eq_zero_of_le h
          rw [h0] at hpos
          exact False.elim (Nat.lt_irrefl 0 hpos)
      have hadd : (r.finish + BitVec.ofNat w 1) - r.start = (r.finish - r.start) + BitVec.ofNat w 1 :=
        bv_add_sub_comm_left r.finish (BitVec.ofNat w 1) r.start
      have hsum : (r.finish - r.start).toNat + (BitVec.ofNat w 1).toNat < 2 ^ w := by
        rw [bv_ofNat_one_toNat hw]
        have h1 := Nat.add_lt_add_right hnot 1
        rw [Nat.sub_add_cancel (pow2_ge_one w)] at h1
        exact h1
      rw [hadd, bv_add_toNat_lt hsum, bv_ofNat_one_toNat hw] at hsh
      exact False.elim (Nat.not_succ_le_self _ hsh)
  · intro ⟨x, hfalse⟩
    cases Nat.eq_zero_or_pos r.available with
    | inl hzero =>
      have hf : r.isFull = true := (WrappingRange.available_zero_iff_isFull hw r).mp hzero
      have ht : r.contains x = true := WrappingRange.contains_of_isFull hw r hf x
      rw [ht] at hfalse
      contradiction
    | inr hpos => exact hpos

/-! ## Section 3: Exact `rustc_abi::Niche::reserve` & Soundness Theorems -/

/-- Rust primitive scalar classification (`rustc_abi::Primitive` simplified to layout-relevant kinds). -/
inductive ScalarKind where
  | bool
  | int (signed : Bool) (bw : BitWidth)
  | ptr

/-- Bit width of a `ScalarKind` on LP64 targets (`pointer = 64 bits`, `bool = 8 bits`). -/
noncomputable def ScalarKind.bitWidth : ScalarKind → Nat
  | .bool => 8
  | .int _ bw => bw.bits
  | .ptr => 64

theorem ScalarKind.bitWidth_pos (k : ScalarKind) : 0 < k.bitWidth := by
  cases k with
  | bool => exact Nat.succ_pos _
  | int _ bw => exact bw.bits_pos
  | ptr => exact Nat.succ_pos _

/-- Initialized scalar metadata (`rustc_abi::Scalar::Initialized`). -/
structure ScalarLayout (w : Nat) where
  kind : ScalarKind
  validRange : WrappingRange w

/-- Niche descriptor (`rustc_abi::Niche`). -/
structure NicheDesc (w : Nat) where
  offset : Nat
  kind : ScalarKind
  validRange : WrappingRange w

/-- Extract a niche descriptor when `available > 0` (`Niche::from_scalar`). -/
noncomputable def nicheFromScalar {w : Nat} (offset : Nat) (s : ScalarLayout w) :
    Option (NicheDesc w) :=
  if Nat.blt 0 s.validRange.available then
    some ⟨offset, s.kind, s.validRange⟩
  else
    none

/-- Signed magnitude `size.sign_extend(x).unsigned_abs()` for `x : BitVec w` (`0 < w`). -/
noncomputable def signAbs (w : Nat) (x : BitVec w) : Nat :=
  if Nat.ble (2 ^ (w - 1)) x.toNat then
    2 ^ w - x.toNat
  else
    x.toNat

/-- Lower-bound extension (`move_start` in `compiler/rustc_abi/src/lib.rs:2055`). -/
noncomputable def moveStart {w : Nat} (r : WrappingRange w) (count : Nat) :
    BitVec w × WrappingRange w :=
  let start := r.start - BitVec.ofNat w count
  (start, r.withStart start)

/-- Upper-bound extension (`move_end` in `compiler/rustc_abi/src/lib.rs:2059`). -/
noncomputable def moveEnd {w : Nat} (r : WrappingRange w) (count : Nat) :
    BitVec w × WrappingRange w :=
  let start := r.finish + BitVec.ofNat w 1
  let finish := r.finish + BitVec.ofNat w count
  (start, r.withFinish finish)

/-- Adjust `Primitive::Bool` to `u8` when `valid_range` expands beyond `{0, 1}`. -/
noncomputable def adjustBoolScalar {w : Nat} (k : ScalarKind) (r : WrappingRange w) : ScalarKind :=
  match k with
  | .bool =>
    if Nat.ble 2 (r.finish - r.start).toNat then
      .int false .w8
    else
      .bool
  | other => other

/-- Exact greedy zero-ward `Niche::reserve` algorithm matching
`compiler/rustc_abi/src/lib.rs:2029-2096`. -/
noncomputable def nicheReserve (w : Nat) (_hw : 0 < w) (r : WrappingRange w) (count : Nat) :
    Option (BitVec w × WrappingRange w) :=
  if Nat.beq count 0 then
    none
  else if Nat.blt r.available count then
    none
  else
    let maxVal := 2 ^ w - 1
    let distEndZero := maxVal - r.finish.toNat
    let isBool := Nat.beq w 8 && (r.start == BitVec.ofNat w 0) && (r.finish == BitVec.ofNat w 1)
    if Nat.beq count 1 && !isBool then
      let nextUp := signAbs w (r.finish + BitVec.ofNat w 1)
      let nextDown := signAbs w (r.start - BitVec.ofNat w 1)
      if Nat.ble nextDown nextUp then
        some (moveStart r count)
      else
        some (moveEnd r count)
    else if Nat.blt r.finish.toNat r.start.toNat then
      some (moveEnd r count)
    else if Nat.ble r.start.toNat distEndZero then
      if Nat.ble count r.start.toNat then
        some (moveStart r count)
      else
        some (moveEnd r count)
    else
      let newEnd := r.finish + BitVec.ofNat w count
      if Nat.ble 1 newEnd.toNat && Nat.ble newEnd.toNat r.finish.toNat then
        some (moveStart r count)
      else
        some (moveEnd r count)

/-- Soundness post-condition for a single niche reservation step. -/
noncomputable def ReservePost {w : Nat} (r : WrappingRange w) (count : Nat)
    (nicheStart : BitVec w) (r' : WrappingRange w) : Prop :=
  (∀ x : BitVec w,
    r'.contains x = true ↔
      (r.contains x = true ∨ ∃ j : Nat, j < count ∧ x = nicheStart + BitVec.ofNat w j)) ∧
  (∀ j : Nat, j < count → r.contains (nicheStart + BitVec.ofNat w j) = false) ∧
  (∀ j₁ j₂ : Nat, j₁ < count → j₂ < count →
    nicheStart + BitVec.ofNat w j₁ = nicheStart + BitVec.ofNat w j₂ → j₁ = j₂) ∧
  (r'.available = r.available - count)

private theorem count_lt_pow2 {w : Nat} (hw : 0 < w) (r : WrappingRange w) (count : Nat)
    (hle : count ≤ r.available) : count < 2 ^ w := by
  have hav : r.available ≤ 2 ^ w - 1 := by
    rw [WrappingRange.available_eq_complement hw]
    exact Nat.sub_le _ _
  exact Nat.lt_of_le_of_lt (Nat.le_trans hle hav) pow2_sub_one_lt

private theorem normEnd_add_count_le {w : Nat} (hw : 0 < w) (r : WrappingRange w) (count : Nat)
    (hle : count ≤ r.available) : (r.finish - r.start).toNat + count ≤ 2 ^ w - 1 := by
  have hav := WrappingRange.available_eq_complement hw r
  rw [hav] at hle
  have hn : r.normEnd ≤ 2 ^ w - 1 := Nat.le_pred_of_lt (r.finish - r.start).isLt
  have hsum : count + r.normEnd ≤ (2 ^ w - 1 - r.normEnd) + r.normEnd :=
    Nat.add_le_add_right hle r.normEnd
  rw [Nat.sub_add_cancel hn, Nat.add_comm] at hsum
  exact hsum

private theorem bv_shift_moveStart {w : Nat} (hw : 0 < w) (r : WrappingRange w) (count : Nat)
    (hle : count ≤ r.available) :
    let s' := r.start - BitVec.ofNat w count
    ((r.finish - s').toNat = (r.finish - r.start).toNat + count) ∧
    (∀ x : BitVec w, (x - s').toNat = ((x - r.start).toNat + count) % 2 ^ w) := by
  have hclt : count < 2 ^ w := count_lt_pow2 hw r count hle
  have hnorm_lt : (r.finish - r.start).toNat + count < 2 ^ w :=
    Nat.lt_of_le_of_lt (normEnd_add_count_le hw r count hle) pow2_sub_one_lt
  have hbv_c : (BitVec.ofNat w count).toNat = count := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hclt
  constructor
  · have hEq : r.finish - (r.start - BitVec.ofNat w count) =
        (r.finish - r.start) + BitVec.ofNat w count :=
      bv_sub_sub_rev r.finish r.start (BitVec.ofNat w count)
    rw [hEq, bv_add_toNat_lt, hbv_c]
    rw [hbv_c]
    exact hnorm_lt
  · intro x
    have hEq : x - (r.start - BitVec.ofNat w count) =
        (x - r.start) + BitVec.ofNat w count :=
      bv_sub_sub_rev x r.start (BitVec.ofNat w count)
    rw [hEq, BitVec.toNat_add, hbv_c]

private theorem bv_shift_moveEnd {w : Nat} (hw : 0 < w) (r : WrappingRange w) (count : Nat)
    (hle : count ≤ r.available) :
    let f' := r.finish + BitVec.ofNat w count
    (f' - r.start).toNat = (r.finish - r.start).toNat + count := by
  have hclt : count < 2 ^ w := count_lt_pow2 hw r count hle
  have hnorm_lt : (r.finish - r.start).toNat + count < 2 ^ w :=
    Nat.lt_of_le_of_lt (normEnd_add_count_le hw r count hle) pow2_sub_one_lt
  have hbv_c : (BitVec.ofNat w count).toNat = count := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hclt
  have hEq : (r.finish + BitVec.ofNat w count) - r.start =
      (r.finish - r.start) + BitVec.ofNat w count :=
    bv_add_sub_comm_left r.finish (BitVec.ofNat w count) r.start
  dsimp only
  rw [hEq, bv_add_toNat_lt, hbv_c]
  rw [hbv_c]
  exact hnorm_lt

/-- Exact soundness theorem for `moveStart`. -/
theorem moveStart_sound {w : Nat} (hw : 0 < w) (r : WrappingRange w) (count : Nat)
    (hle : count ≤ r.available) :
    let res := moveStart r count
    ReservePost r count res.1 res.2 := by
  dsimp [moveStart, ReservePost, WrappingRange.withStart]
  have hclt : count < 2 ^ w := count_lt_pow2 hw r count hle
  have hnorm : (r.finish - r.start).toNat + count ≤ 2 ^ w - 1 :=
    normEnd_add_count_le hw r count hle
  obtain ⟨hfin', hshift_x⟩ := bv_shift_moveStart hw r count hle
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [WrappingRange.contains_iff_shift, WrappingRange.contains_iff_shift, hfin', hshift_x]
    let k := (x - r.start).toNat
    change (k + count) % 2 ^ w ≤ (r.finish - r.start).toNat + count ↔
      k ≤ (r.finish - r.start).toNat ∨
        ∃ j, j < count ∧ x = r.start - BitVec.ofNat w count + BitVec.ofNat w j
    have hklt : k < 2 ^ w := (x - r.start).isLt
    constructor
    · intro hle'
      cases Nat.lt_or_ge (k + count) (2 ^ w) with
      | inl hlt2 =>
        rw [Nat.mod_eq_of_lt hlt2] at hle'
        left
        exact nat_le_of_add_le_add_right hle'
      | inr hge2 =>
        right
        let j := k + count - 2 ^ w
        have hjlt : j < count := by
          have hk_plus : k + count < 2 ^ w + count := Nat.add_lt_add_right hklt count
          have hsub := nat_sub_lt_of_le_of_lt hge2 hk_plus
          rw [Nat.add_comm (2 ^ w) count, Nat.add_sub_cancel] at hsub
          exact hsub
        refine ⟨j, hjlt, ?_⟩
        apply bv_sub_right_cancel (c := r.start)
        have hrhs : ((r.start - BitVec.ofNat w count) + BitVec.ofNat w j) - r.start =
            BitVec.ofNat w j - BitVec.ofNat w count := by
          rw [bv_add_sub_comm_left, BitVec.sub_sub, BitVec.add_comm (BitVec.ofNat w count) r.start,
            ← BitVec.sub_sub, BitVec.sub_self]
          apply bv_add_right_cancel (c := BitVec.ofNat w count)
          rw [BitVec.sub_add_cancel]
          have h0 : 0#w - BitVec.ofNat w count + BitVec.ofNat w j + BitVec.ofNat w count =
              0#w - BitVec.ofNat w count + BitVec.ofNat w count + BitVec.ofNat w j := by
            rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat w j), ← BitVec.add_assoc]
          rw [h0, BitVec.sub_add_cancel, BitVec.zero_add]
        rw [hrhs]
        apply BitVec.eq_of_toNat_eq
        have hjlt2 : j < 2 ^ w := Nat.lt_trans hjlt hclt
        have hjbv : (BitVec.ofNat w j).toNat = j := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hjlt2
        have hcbv : (BitVec.ofNat w count).toNat = count := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hclt
        have hjltc : (BitVec.ofNat w j).toNat < (BitVec.ofNat w count).toNat := by
          rw [hjbv, hcbv]; exact hjlt
        rw [bv_sub_toNat_of_lt hjltc, hjbv, hcbv]
        have heqk : 2 ^ w - count + (k + count - 2 ^ w) = k := by
          have h1 : 2 ^ w - count + (k + count - 2 ^ w) + 2 ^ w =
              (2 ^ w - count) + ((k + count - 2 ^ w) + 2 ^ w) := Nat.add_assoc _ _ _
          rw [Nat.sub_add_cancel hge2] at h1
          have hc2 : count ≤ 2 ^ w := Nat.le_of_lt hclt
          have h2 : 2 ^ w - count + (k + count) = (2 ^ w - count + count) + k := by
            rw [Nat.add_comm k count, ← Nat.add_assoc]
          rw [Nat.sub_add_cancel hc2] at h2
          rw [h2, Nat.add_comm (2 ^ w) k] at h1
          exact Nat.add_right_cancel h1
        exact heqk.symm
    · intro hor
      cases hor with
      | inl hle_old =>
        have hlt_sum : k + count < 2 ^ w :=
          Nat.lt_of_le_of_lt (Nat.add_le_add_right hle_old count)
            (Nat.lt_of_le_of_lt hnorm pow2_sub_one_lt)
        rw [Nat.mod_eq_of_lt hlt_sum]
        exact Nat.add_le_add_right hle_old count
      | inr hex =>
        obtain ⟨j, hjlt, hxeq⟩ := hex
        have hjlt2 : j < 2 ^ w := Nat.lt_trans hjlt hclt
        have hjbv : (BitVec.ofNat w j).toNat = j := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hjlt2
        have hshift_eq : x - (r.start - BitVec.ofNat w count) = BitVec.ofNat w j := by
          rw [hxeq, BitVec.add_comm, BitVec.add_sub_cancel]
        have hnat : (k + count) % 2 ^ w = j := by
          change ((x - r.start).toNat + count) % 2 ^ w = j
          rw [← hshift_x x, hshift_eq, hjbv]
        rw [hnat]
        exact Nat.le_trans (Nat.le_of_lt hjlt) (Nat.le_add_left _ _)
  · intro j hjlt
    cases hcont : r.contains ((r.start - BitVec.ofNat w count) + BitVec.ofNat w j) with
    | false => rfl
    | true =>
      have hsh := (WrappingRange.contains_iff_shift r _).mp hcont
      have hsub : ((r.start - BitVec.ofNat w count) + BitVec.ofNat w j) - r.start =
          BitVec.ofNat w j - BitVec.ofNat w count := by
        rw [bv_add_sub_comm_left, BitVec.sub_sub, BitVec.add_comm (BitVec.ofNat w count) r.start,
          ← BitVec.sub_sub, BitVec.sub_self]
        apply bv_add_right_cancel (c := BitVec.ofNat w count)
        rw [BitVec.sub_add_cancel]
        have h0 : 0#w - BitVec.ofNat w count + BitVec.ofNat w j + BitVec.ofNat w count =
            0#w - BitVec.ofNat w count + BitVec.ofNat w count + BitVec.ofNat w j := by
          rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat w j), ← BitVec.add_assoc]
        rw [h0, BitVec.sub_add_cancel, BitVec.zero_add]
      have hjlt2 : j < 2 ^ w := Nat.lt_trans hjlt hclt
      have hjbv : (BitVec.ofNat w j).toNat = j := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hjlt2
      have hcbv : (BitVec.ofNat w count).toNat = count := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hclt
      have hjltc : (BitVec.ofNat w j).toNat < (BitVec.ofNat w count).toNat := by
        rw [hjbv, hcbv]; exact hjlt
      rw [hsub, bv_sub_toNat_of_lt hjltc, hjbv, hcbv] at hsh
      have hbound : 2 ^ w - count + j ≤ (r.finish - r.start).toNat := hsh
      have hsum_le := Nat.add_le_add_right hbound count
      have hc2 : count ≤ 2 ^ w := Nat.le_of_lt hclt
      have hlhs : 2 ^ w - count + j + count = 2 ^ w + j := by
        rw [Nat.add_assoc, Nat.add_comm j count, ← Nat.add_assoc, Nat.sub_add_cancel hc2]
      rw [hlhs] at hsum_le
      have hfin_lt : (r.finish - r.start).toNat + count < 2 ^ w :=
        Nat.lt_of_le_of_lt hnorm pow2_sub_one_lt
      have hcontra : 2 ^ w + j < 2 ^ w := Nat.lt_of_le_of_lt hsum_le hfin_lt
      exact False.elim (Nat.not_lt_of_ge (Nat.le_add_right (2 ^ w) j) hcontra)
  · intro j₁ j₂ hj₁ hj₂ heq
    have heq2 : BitVec.ofNat w j₁ = BitVec.ofNat w j₂ := by
      have hs := congrArg (fun z => z - (r.start - BitVec.ofNat w count)) heq
      rw [BitVec.add_comm (r.start - BitVec.ofNat w count), BitVec.add_sub_cancel] at hs
      rw [BitVec.add_comm (r.start - BitVec.ofNat w count), BitVec.add_sub_cancel] at hs
      exact hs
    have hj1lt2 : j₁ < 2 ^ w := Nat.lt_trans hj₁ hclt
    have hj2lt2 : j₂ < 2 ^ w := Nat.lt_trans hj₂ hclt
    have h1 := congrArg BitVec.toNat heq2
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hj1lt2, Nat.mod_eq_of_lt hj2lt2] at h1
    exact h1
  · rw [WrappingRange.available_eq_complement hw, WrappingRange.available_eq_complement hw]
    unfold WrappingRange.normEnd
    rw [hfin', Nat.sub_add_eq]

/-- Exact soundness theorem for `moveEnd`. -/
theorem moveEnd_sound {w : Nat} (hw : 0 < w) (r : WrappingRange w) (count : Nat)
    (hle : count ≤ r.available) :
    let res := moveEnd r count
    ReservePost r count res.1 res.2 := by
  dsimp [moveEnd, ReservePost, WrappingRange.withFinish]
  have hclt : count < 2 ^ w := count_lt_pow2 hw r count hle
  have hnorm : (r.finish - r.start).toNat + count ≤ 2 ^ w - 1 :=
    normEnd_add_count_le hw r count hle
  have hnorm_lt : (r.finish - r.start).toNat + count < 2 ^ w :=
    Nat.lt_of_le_of_lt hnorm pow2_sub_one_lt
  have hfin' := bv_shift_moveEnd hw r count hle
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [WrappingRange.contains_iff_shift, WrappingRange.contains_iff_shift, hfin']
    dsimp only
    let k := (x - r.start).toNat
    change k ≤ (r.finish - r.start).toNat + count ↔
      k ≤ (r.finish - r.start).toNat ∨
        ∃ j, j < count ∧ x = r.finish + BitVec.ofNat w 1 + BitVec.ofNat w j
    have hklt : k < 2 ^ w := (x - r.start).isLt
    constructor
    · intro hle'
      cases Nat.lt_or_ge (r.finish - r.start).toNat k with
      | inr hkle => left; exact hkle
      | inl hkgt =>
        right
        let j := k - ((r.finish - r.start).toNat + 1)
        have hjlt : j < count := by
          have h1 : (r.finish - r.start).toNat + 1 ≤ k := hkgt
          have h2 : k < (r.finish - r.start).toNat + 1 + count := by
            rw [Nat.add_assoc, Nat.add_comm 1 count, ← Nat.add_assoc]
            exact Nat.lt_succ_of_le hle'
          have hsub := nat_sub_lt_of_le_of_lt h1 h2
          have hrhs : (r.finish - r.start).toNat + 1 + count - ((r.finish - r.start).toNat + 1) =
              count := by
            rw [Nat.add_comm, Nat.add_sub_cancel]
          rw [hrhs] at hsub
          exact hsub
        refine ⟨j, hjlt, ?_⟩
        apply bv_sub_right_cancel (c := r.start)
        have hadd : (r.finish + BitVec.ofNat w 1) + BitVec.ofNat w j - r.start =
            (r.finish - r.start) + BitVec.ofNat w 1 + BitVec.ofNat w j := by
          rw [bv_add_sub_comm_left, bv_add_sub_comm_left]
        rw [hadd]
        apply BitVec.eq_of_toNat_eq
        have hjlt2 : j < 2 ^ w := Nat.lt_trans hjlt hclt
        have hjbv : (BitVec.ofNat w j).toNat = j := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hjlt2
        have h1bv : (BitVec.ofNat w 1).toNat = 1 := bv_ofNat_one_toNat hw
        have hsum1 : (r.finish - r.start).toNat + (BitVec.ofNat w 1).toNat < 2 ^ w := by
          rw [h1bv]
          cases count with
          | zero => contradiction
          | succ c' =>
            have hle1 : (r.finish - r.start).toNat + 1 ≤ (r.finish - r.start).toNat + Nat.succ c' :=
              Nat.add_le_add_left (Nat.succ_pos c') _
            exact Nat.lt_of_le_of_lt hle1 hnorm_lt
        have hsum2 : ((r.finish - r.start) + BitVec.ofNat w 1).toNat + (BitVec.ofNat w j).toNat < 2 ^ w := by
          rw [bv_add_toNat_lt hsum1, h1bv, hjbv, Nat.add_assoc]
          have hjle : 1 + j ≤ count := by
            rw [Nat.add_comm]; exact hjlt
          exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hjle _) hnorm_lt
        rw [bv_add_toNat_lt hsum2, bv_add_toNat_lt hsum1, h1bv, hjbv]
        have h1le : (r.finish - r.start).toNat + 1 ≤ k := hkgt
        rw [Nat.add_comm ((r.finish - r.start).toNat + 1) j]
        exact (Nat.sub_add_cancel h1le).symm
    · intro hor
      cases hor with
      | inl hkle => exact Nat.le_trans hkle (Nat.le_add_right _ _)
      | inr hex =>
        obtain ⟨j, hjlt, hxeq⟩ := hex
        have hjlt2 : j < 2 ^ w := Nat.lt_trans hjlt hclt
        have hjbv : (BitVec.ofNat w j).toNat = j := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hjlt2
        have h1bv : (BitVec.ofNat w 1).toNat = 1 := bv_ofNat_one_toNat hw
        have hsum1 : (r.finish - r.start).toNat + (BitVec.ofNat w 1).toNat < 2 ^ w := by
          rw [h1bv]
          have hcpos : 1 ≤ count := Nat.lt_of_le_of_lt (Nat.zero_le j) hjlt
          exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hcpos _) hnorm_lt
        have hsum2 : ((r.finish - r.start) + BitVec.ofNat w 1).toNat + (BitVec.ofNat w j).toNat < 2 ^ w := by
          rw [bv_add_toNat_lt hsum1, h1bv, hjbv, Nat.add_assoc]
          have hjle : 1 + j ≤ count := by rw [Nat.add_comm]; exact hjlt
          exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hjle _) hnorm_lt
        have hsub : x - r.start = ((r.finish - r.start) + BitVec.ofNat w 1) + BitVec.ofNat w j := by
          rw [hxeq, bv_add_sub_comm_left, bv_add_sub_comm_left]
        change (x - r.start).toNat ≤ (r.finish - r.start).toNat + count
        rw [hsub, bv_add_toNat_lt hsum2, bv_add_toNat_lt hsum1, h1bv, hjbv, Nat.add_assoc]
        have hjle : 1 + j ≤ count := by rw [Nat.add_comm]; exact hjlt
        exact Nat.add_le_add_left hjle _
  · intro j hjlt
    cases hcont : r.contains ((r.finish + BitVec.ofNat w 1) + BitVec.ofNat w j) with
    | false => rfl
    | true =>
      have hsh := (WrappingRange.contains_iff_shift r _).mp hcont
      have hsub : ((r.finish + BitVec.ofNat w 1) + BitVec.ofNat w j) - r.start =
          ((r.finish - r.start) + BitVec.ofNat w 1) + BitVec.ofNat w j := by
        rw [bv_add_sub_comm_left, bv_add_sub_comm_left]
      have hjlt2 : j < 2 ^ w := Nat.lt_trans hjlt hclt
      have hjbv : (BitVec.ofNat w j).toNat = j := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hjlt2
      have h1bv : (BitVec.ofNat w 1).toNat = 1 := bv_ofNat_one_toNat hw
      have hsum1 : (r.finish - r.start).toNat + (BitVec.ofNat w 1).toNat < 2 ^ w := by
        rw [h1bv]
        have hcpos : 1 ≤ count := Nat.lt_of_le_of_lt (Nat.zero_le j) hjlt
        exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hcpos _) hnorm_lt
      have hsum2 : ((r.finish - r.start) + BitVec.ofNat w 1).toNat + (BitVec.ofNat w j).toNat < 2 ^ w := by
        rw [bv_add_toNat_lt hsum1, h1bv, hjbv, Nat.add_assoc]
        have hjle : 1 + j ≤ count := by rw [Nat.add_comm]; exact hjlt
        exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hjle _) hnorm_lt
      rw [hsub, bv_add_toNat_lt hsum2, bv_add_toNat_lt hsum1, h1bv, hjbv] at hsh
      have hlt : (r.finish - r.start).toNat < (r.finish - r.start).toNat + 1 + j := by
        rw [Nat.add_assoc]
        exact Nat.lt_add_of_pos_right (Nat.lt_of_lt_of_le (Nat.succ_pos 0) (Nat.le_add_right 1 j))
      exact False.elim (Nat.not_lt_of_ge hsh hlt)
  · intro j₁ j₂ hj₁ hj₂ heq
    have heq2 : BitVec.ofNat w j₁ = BitVec.ofNat w j₂ := by
      have hs := congrArg (fun z => z - (r.finish + BitVec.ofNat w 1)) heq
      rw [BitVec.add_comm (r.finish + BitVec.ofNat w 1), BitVec.add_sub_cancel] at hs
      rw [BitVec.add_comm (r.finish + BitVec.ofNat w 1), BitVec.add_sub_cancel] at hs
      exact hs
    have hj1lt2 : j₁ < 2 ^ w := Nat.lt_trans hj₁ hclt
    have hj2lt2 : j₂ < 2 ^ w := Nat.lt_trans hj₂ hclt
    have h1 := congrArg BitVec.toNat heq2
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hj1lt2, Nat.mod_eq_of_lt hj2lt2] at h1
    exact h1
  · rw [WrappingRange.available_eq_complement hw, WrappingRange.available_eq_complement hw]
    unfold WrappingRange.normEnd
    rw [hfin', Nat.sub_add_eq]

/-- Universal soundness of `nicheReserve` across all 4 greedy zero-ward heuristic branches. -/
theorem nicheReserve_sound {w : Nat} (hw : 0 < w) (r : WrappingRange w) (count : Nat)
    (nicheStart : BitVec w) (r' : WrappingRange w)
    (hres : nicheReserve w hw r count = some (nicheStart, r')) :
    0 < count ∧ count ≤ r.available ∧ ReservePost r count nicheStart r' := by
  unfold nicheReserve at hres
  cases hcz : Nat.beq count 0 with
  | true =>
    rw [hcz] at hres
    simp at hres
  | false =>
    rw [hcz] at hres
    have hcpos : 0 < count := by
      cases count with
      | zero => contradiction
      | succ k => exact Nat.succ_pos k
    cases hlt : Nat.blt r.available count with
    | true =>
      rw [hlt] at hres
      simp at hres
    | false =>
      rw [hlt] at hres
      have hle : count ≤ r.available := (nat_blt_false_iff r.available count).mp hlt
      refine ⟨hcpos, hle, ?_⟩
      simp only [Bool.false_eq_true, ite_false] at hres
      split at hres
      · split at hres
        · have heq : moveStart r count = (nicheStart, r') := Option.some.inj hres
          have hms := moveStart_sound hw r count hle
          dsimp only at hms
          rw [heq] at hms
          exact hms
        · have heq : moveEnd r count = (nicheStart, r') := Option.some.inj hres
          have hme := moveEnd_sound hw r count hle
          dsimp only at hme
          rw [heq] at hme
          exact hme
      · split at hres
        · have heq : moveEnd r count = (nicheStart, r') := Option.some.inj hres
          have hme := moveEnd_sound hw r count hle
          dsimp only at hme
          rw [heq] at hme
          exact hme
        · split at hres
          · split at hres
            · have heq : moveStart r count = (nicheStart, r') := Option.some.inj hres
              have hms := moveStart_sound hw r count hle
              dsimp only at hms
              rw [heq] at hms
              exact hms
            · have heq : moveEnd r count = (nicheStart, r') := Option.some.inj hres
              have hme := moveEnd_sound hw r count hle
              dsimp only at hme
              rw [heq] at hme
              exact hme
          · split at hres
            · have heq : moveStart r count = (nicheStart, r') := Option.some.inj hres
              have hms := moveStart_sound hw r count hle
              dsimp only at hms
              rw [heq] at hms
              exact hms
            · have heq : moveEnd r count = (nicheStart, r') := Option.some.inj hres
              have hme := moveEnd_sound hw r count hle
              dsimp only at hme
              rw [heq] at hme
              exact hme

/-- Capacity exhaustion gate theorem: `nicheReserve` returns `none` iff `count = 0` or
`r.available < count`. When `r.isFull = true` (`r.available = 0`), every `count ≥ 1`
exhausts capacity and returns `none`. -/
theorem nicheReserve_none_iff {w : Nat} (hw : 0 < w) (r : WrappingRange w) (count : Nat) :
    nicheReserve w hw r count = none ↔ count = 0 ∨ r.available < count := by
  unfold nicheReserve
  cases hcz : Nat.beq count 0 with
  | true =>
    have h0 : count = 0 := Nat.beq_eq.mp hcz
    simp only [ite_true]
    exact ⟨fun _ => Or.inl h0, fun _ => trivial⟩
  | false =>
    have hne0 : count ≠ 0 := by
      intro h0
      rw [h0] at hcz
      contradiction
    cases hlt : Nat.blt r.available count with
    | true =>
      have hlt' : r.available < count := (nat_blt_true_iff _ _).mp hlt
      simp only [Bool.false_eq_true, ite_false, ite_true]
      exact ⟨fun _ => Or.inr hlt', fun _ => trivial⟩
    | false =>
      have hle : count ≤ r.available := (nat_blt_false_iff _ _).mp hlt
      constructor
      · intro hnone
        exfalso
        simp only [Bool.false_eq_true, ite_false] at hnone
        split at hnone
        · split at hnone <;> contradiction
        · split at hnone
          · contradiction
          · split at hnone
            · split at hnone <;> contradiction
            · split at hnone <;> contradiction
      · intro hor
        cases hor with
        | inl h0 => exact False.elim (hne0 h0)
        | inr hgt => exact False.elim (Nat.not_lt_of_ge hle hgt)

theorem nicheReserve_exhausted_of_isFull {w : Nat} (hw : 0 < w) (r : WrappingRange w)
    (hf : r.isFull = true) (count : Nat) (hc : 0 < count) :
    nicheReserve w hw r count = none := by
  rw [nicheReserve_none_iff]
  right
  rw [(WrappingRange.available_zero_iff_isFull hw r).mpr hf]
  exact hc

/-! ## Section 4: Iterated Multi-Level `NicheChain` Injectivity & Disjointness -/

/-- One reservation level in an iterated `Option<Option<...>>` / multi-variant niche stack. -/
structure NicheStep (w : Nat) where
  count : Nat
  nicheStart : BitVec w
  rangeAfter : WrappingRange w

/-- Inductive chain of valid `nicheReserve` reservations starting from `base`. -/
inductive NicheChain (w : Nat) (hw : 0 < w) :
    WrappingRange w → WrappingRange w → List (NicheStep w) → Prop where
  | nil (r : WrappingRange w) : NicheChain w hw r r []
  | cons {base mid top : WrappingRange w} {steps : List (NicheStep w)}
      (count : Nat) (ns : BitVec w)
      (hprev : NicheChain w hw base mid steps)
      (hstep : nicheReserve w hw mid count = some (ns, top)) :
      NicheChain w hw base top (steps ++ [⟨count, ns, top⟩])

/-- Monotonicity: any value valid in `base` remains valid in `top` after a `NicheChain`. -/
theorem NicheChain.mono {w : Nat} {hw : 0 < w} {base top : WrappingRange w}
    {steps : List (NicheStep w)} (hc : NicheChain w hw base top steps) :
    ∀ x : BitVec w, base.contains x = true → top.contains x = true := by
  induction hc with
  | nil => intro _ hx; exact hx
  | cons count ns _ hstep ih =>
    intro x hx
    have hmid := ih x hx
    obtain ⟨_, _, hpost⟩ := nicheReserve_sound hw _ count ns _ hstep
    exact (hpost.1 x).mpr (Or.inl hmid)

/-- Sum of reserved niche counts across a chain. -/
noncomputable def NicheChain.totalReserved {w : Nat} : List (NicheStep w) → Nat
  | [] => 0
  | s :: rest => s.count + NicheChain.totalReserved rest

private theorem totalReserved_append {w : Nat} (a b : List (NicheStep w)) :
    NicheChain.totalReserved (a ++ b) =
      NicheChain.totalReserved a + NicheChain.totalReserved b := by
  induction a with
  | nil => simp [NicheChain.totalReserved]
  | cons x xs ih =>
    simp [NicheChain.totalReserved, ih, Nat.add_assoc]

/-- Capacity conservation along any `NicheChain`:
`top.available + totalReserved = base.available`. -/
theorem NicheChain.available_conservation {w : Nat} {hw : 0 < w}
    {base top : WrappingRange w} {steps : List (NicheStep w)}
    (hc : NicheChain w hw base top steps) :
    top.available + NicheChain.totalReserved steps = base.available := by
  induction hc with
  | nil => simp [NicheChain.totalReserved]
  | cons count ns _ hstep ih =>
    obtain ⟨_, hle, hpost⟩ := nicheReserve_sound hw _ count ns _ hstep
    rw [totalReserved_append]
    dsimp only [NicheChain.totalReserved]
    rw [Nat.add_zero, hpost.2.2.2, Nat.add_comm (NicheChain.totalReserved _) count,
      ← Nat.add_assoc, Nat.sub_add_cancel hle]
    exact ih

/-- Retrieve step `idx` from a chain along with its input range, or default. -/
noncomputable def tagAt {w : Nat} (ns : BitVec w) (slot : Nat) : BitVec w :=
  ns + BitVec.ofNat w slot

/-- Inductive pairwise disjointness and base-disjointness over a `NicheChain`:
1. Every reserved tag `(stepIdx, slot)` lies strictly outside `base` (`base.contains tag = false`).
2. Within any step `i`, distinct slots `j₁ ≠ j₂` yield distinct tags.
3. Across any two distinct steps `i₁ < i₂`, `tag(i₁, j₁) ≠ tag(i₂, j₂)`. -/
noncomputable def ChainTagsValid {w : Nat} (base : WrappingRange w) :
    List (NicheStep w) → Prop
  | [] => True
  | st :: rest =>
    (∀ j : Nat, j < st.count → base.contains (tagAt st.nicheStart j) = false) ∧
    (∀ j₁ j₂ : Nat, j₁ < st.count → j₂ < st.count →
      tagAt st.nicheStart j₁ = tagAt st.nicheStart j₂ → j₁ = j₂) ∧
    (∀ st' ∈ rest, ∀ j₁ j₂ : Nat, j₁ < st.count → j₂ < st'.count →
      tagAt st.nicheStart j₁ ≠ tagAt st'.nicheStart j₂) ∧
    ChainTagsValid base rest

private theorem chainTagsValid_snoc {w : Nat} (base : WrappingRange w)
    (steps : List (NicheStep w)) (newSt : NicheStep w)
    (hprev : ChainTagsValid base steps)
    (hnewOut : ∀ j : Nat, j < newSt.count → base.contains (tagAt newSt.nicheStart j) = false)
    (hnewInj : ∀ j₁ j₂ : Nat, j₁ < newSt.count → j₂ < newSt.count →
      tagAt newSt.nicheStart j₁ = tagAt newSt.nicheStart j₂ → j₁ = j₂)
    (hdisj : ∀ st ∈ steps, ∀ j₁ j₂ : Nat, j₁ < st.count → j₂ < newSt.count →
      tagAt st.nicheStart j₁ ≠ tagAt newSt.nicheStart j₂) :
    ChainTagsValid base (steps ++ [newSt]) := by
  induction steps with
  | nil =>
    exact ⟨hnewOut, hnewInj, fun _ hm => False.elim (List.not_mem_nil hm), trivial⟩
  | cons s rest ih =>
    obtain ⟨hsOut, hsInj, hsDisj, hsRest⟩ := hprev
    refine ⟨hsOut, hsInj, ?_, ?_⟩
    · intro st' hmem j₁ j₂ hj₁ hj₂
      change st' ∈ rest ++ [newSt] at hmem
      rw [List.mem_append, List.mem_singleton] at hmem
      cases hmem with
      | inl hm => exact hsDisj st' hm j₁ j₂ hj₁ hj₂
      | inr heq =>
        rw [heq] at hj₂ ⊢
        exact hdisj s (List.mem_cons_self) j₁ j₂ hj₁ hj₂
    · apply ih hsRest
      intro st hm j₁ j₂ hj₁ hj₂
      exact hdisj st (List.mem_cons_of_mem s hm) j₁ j₂ hj₁ hj₂

/-- **Theorem 1 (Iterated `Niche::reserve` Injectivity & Disjointness Theorem)**:
Across ANY chain of `nicheReserve` invocations starting from `base`:
1. Every reserved niche tag lies strictly outside `base` (`base.contains tag = false`).
2. Every reserved niche tag is contained in `top` (`top.contains tag = true`).
3. Every `(level, slot)` pair maps injectively to a distinct bit pattern (`ChainTagsValid`). -/
theorem NicheChain.tags_sound {w : Nat} {hw : 0 < w}
    {base top : WrappingRange w} {steps : List (NicheStep w)}
    (hc : NicheChain w hw base top steps) :
    ChainTagsValid base steps ∧
    (∀ st ∈ steps, ∀ j : Nat, j < st.count → top.contains (tagAt st.nicheStart j) = true) := by
  induction hc with
  | nil =>
    exact ⟨trivial, fun _ hm => False.elim (List.not_mem_nil hm)⟩
  | cons count ns hcPrev hstep ih =>
    obtain ⟨ihValid, ihInMid⟩ := ih
    obtain ⟨_, _, hpost⟩ := nicheReserve_sound hw _ count ns _ hstep
    constructor
    · apply chainTagsValid_snoc base _ ⟨count, ns, _⟩ ihValid
      · intro j hjlt
        cases hbc : base.contains (tagAt ns j) with
        | false => rfl
        | true =>
          have hmid := NicheChain.mono hcPrev (tagAt ns j) hbc
          unfold tagAt at hmid
          have hnot := hpost.2.1 j hjlt
          rw [hmid] at hnot
          contradiction
      · exact hpost.2.2.1
      · intro st hm j₁ j₂ hj₁ hj₂ heq
        unfold tagAt at heq
        dsimp only at heq
        have hm1 := ihInMid st hm j₁ hj₁
        unfold tagAt at hm1
        have hm2 := hpost.2.1 j₂ hj₂
        rw [← heq, hm1] at hm2
        contradiction
    · intro st hm j hjlt
      rw [List.mem_append, List.mem_singleton] at hm
      cases hm with
      | inl hmOld =>
        have hmid := ihInMid st hmOld j hjlt
        exact (hpost.1 _).mpr (Or.inl hmid)
      | inr heq =>
        rw [heq] at hjlt ⊢
        exact (hpost.1 _).mpr (Or.inr ⟨j, hjlt, rfl⟩)

/-! ## Section 5: Concrete `rustc_abi` Niche-Stacking Instances (`bool`, `char`, `NonNull`, `NonZeroU8`) -/

/-- Valid range of `bool`: `{0, 1}` in 8-bit representation (`rustc_ty_utils/src/layout.rs:384-390`). -/
noncomputable def boolRange : WrappingRange 8 := ⟨0#8, 1#8⟩

/-- Valid scalar range of `char`: `0..=0x10FFFF` in 32-bit representation (`layout.rs:391-397`). -/
noncomputable def charScalarRange : WrappingRange 32 := ⟨0#32, BitVec.ofNat 32 0x10FFFF⟩

/-- Valid range of `NonNull<u8>` on LP64: `1..=2^64-1` (`layout.rs:272`). -/
noncomputable def nonNull64Range : WrappingRange 64 := ⟨1#64, BitVec.ofNat 64 (2 ^ 64 - 1)⟩

/-- Valid range of `NonZero<u8>`: `1..=255` in 8-bit representation. -/
noncomputable def nonZero8Range : WrappingRange 8 := ⟨1#8, 255#8⟩

/-- Exact greedy reservation trace for `Option<bool>`, `Option<Option<bool>>`, and `Option^3(bool)`:
- Level 1 (`Option<bool>`): `is_bool` triggers `moveEnd`, assigning `None = 2`, range `0..=2`.
- Level 2 (`Option<Option<bool>>`): `!is_bool`, `next_down = |-1_i8| = 1 ≤ next_up = 3`, assigns `None = 255`, range `255..=2`.
- Level 3 (`Option<Option<Option<bool>>>`): `next_down = |-2_i8| = 2 ≤ next_up = 3`, assigns `None = 254`, range `254..=2`. -/
theorem optBool_exact :
    nicheReserve 8 (by decide : 0 < 8) boolRange 1 = some (2#8, ⟨0#8, 2#8⟩) := by
  rfl

theorem optOptBool_exact :
    nicheReserve 8 (by decide : 0 < 8) ⟨0#8, 2#8⟩ 1 = some (255#8, ⟨255#8, 2#8⟩) := by
  rfl

theorem opt3Bool_exact :
    nicheReserve 8 (by decide : 0 < 8) ⟨255#8, 2#8⟩ 1 = some (254#8, ⟨254#8, 2#8⟩) := by
  rfl

/-- Contrast: 3-variant `enum BoolPlusTwo { Payload(bool), X, Y }` reserves `count = 2`,
bypassing `count == 1` and picking `moveEnd`, producing `[0, 1, 2, 3]`! -/
theorem boolPlusTwo_exact :
    nicheReserve 8 (by decide : 0 < 8) boolRange 2 = some (2#8, ⟨0#8, 3#8⟩) := by
  rfl

/-- **Theorem 2 (`0x03`-Invalidity Theorem for `Option<Option<bool>>` & `Option^3(bool)`)**:
Byte `0x03` lies strictly outside the valid tag range of both `Option<Option<bool>>`
and `Option<Option<Option<bool>>>` (explaining Miri's `InvalidTag(0x03)` UB), whereas
`0, 1, 2, 255` are all valid for `Option<Option<bool>>`. -/
theorem optOptBool_valid_and_0x03_invalid :
    (⟨255#8, 2#8⟩ : WrappingRange 8).contains 0#8 = true ∧
    (⟨255#8, 2#8⟩ : WrappingRange 8).contains 1#8 = true ∧
    (⟨255#8, 2#8⟩ : WrappingRange 8).contains 2#8 = true ∧
    (⟨255#8, 2#8⟩ : WrappingRange 8).contains 255#8 = true ∧
    (⟨255#8, 2#8⟩ : WrappingRange 8).contains 3#8 = false ∧
    (⟨254#8, 2#8⟩ : WrappingRange 8).contains 3#8 = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact greedy reservation trace for `Option<Option<Option<char>>>`:
`[0x41 ('A'), 0xffffffff, 0xfffffffe, 0xfffffffd]`. -/
theorem optChar_exact :
    nicheReserve 32 (by decide : 0 < 32) charScalarRange 1 =
      some (BitVec.ofNat 32 0xFFFFFFFF, ⟨BitVec.ofNat 32 0xFFFFFFFF, BitVec.ofNat 32 0x10FFFF⟩) := by
  rfl

theorem optOptChar_exact :
    nicheReserve 32 (by decide : 0 < 32) ⟨BitVec.ofNat 32 0xFFFFFFFF, BitVec.ofNat 32 0x10FFFF⟩ 1 =
      some (BitVec.ofNat 32 0xFFFFFFFE, ⟨BitVec.ofNat 32 0xFFFFFFFE, BitVec.ofNat 32 0x10FFFF⟩) := by
  rfl

theorem opt3Char_exact :
    nicheReserve 32 (by decide : 0 < 32) ⟨BitVec.ofNat 32 0xFFFFFFFE, BitVec.ofNat 32 0x10FFFF⟩ 1 =
      some (BitVec.ofNat 32 0xFFFFFFFD, ⟨BitVec.ofNat 32 0xFFFFFFFD, BitVec.ofNat 32 0x10FFFF⟩) := by
  rfl

/-- `0x41` (`'A'`), `0xFFFFFFFF`, `0xFFFFFFFE`, `0xFFFFFFFD` are valid in `Option^3(char)`,
while `0x00110000` is outside the `WrappingRange` (rejected at tag level), and surrogate
`0x0000D800` lies INSIDE `WrappingRange` (requiring deep `char` scalar validation!). -/
theorem opt3Char_tags_and_surrogate_gap :
    let r3 : WrappingRange 32 := ⟨BitVec.ofNat 32 0xFFFFFFFD, BitVec.ofNat 32 0x10FFFF⟩
    r3.contains (BitVec.ofNat 32 0x41) = true ∧
    r3.contains (BitVec.ofNat 32 0xFFFFFFFF) = true ∧
    r3.contains (BitVec.ofNat 32 0xFFFFFFFE) = true ∧
    r3.contains (BitVec.ofNat 32 0xFFFFFFFD) = true ∧
    r3.contains (BitVec.ofNat 32 0x00110000) = false ∧
    r3.contains (BitVec.ofNat 32 0x0000D800) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Theorem 3 (Capacity Exhaustion Spill Theorem)**:
For `NonNull<u8>` (`available = 1`) and `NonZero<u8>` (`available = 1`):
- Level 1 (`Option<T>`) consumes the single niche (`nicheStart = 0`), leaving `available = 0` (`isFull = true`).
- Level 2 (`Option<Option<T>>`) hits `nicheReserve = none`, forcing `Direct` discriminant allocation. -/
theorem nonNull64_spill_theorem :
    nicheReserve 64 (by decide : 0 < 64) nonNull64Range 1 =
      some (0#64, ⟨0#64, BitVec.ofNat 64 (2 ^ 64 - 1)⟩) ∧
    (⟨0#64, BitVec.ofNat 64 (2 ^ 64 - 1)⟩ : WrappingRange 64).available = 0 ∧
    (⟨0#64, BitVec.ofNat 64 (2 ^ 64 - 1)⟩ : WrappingRange 64).isFull = true ∧
    nicheReserve 64 (by decide : 0 < 64) ⟨0#64, BitVec.ofNat 64 (2 ^ 64 - 1)⟩ 1 = none := by
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem nonZero8_spill_theorem :
    nicheReserve 8 (by decide : 0 < 8) nonZero8Range 1 = some (0#8, ⟨0#8, 255#8⟩) ∧
    (⟨0#8, 255#8⟩ : WrappingRange 8).available = 0 ∧
    (⟨0#8, 255#8⟩ : WrappingRange 8).isFull = true ∧
    nicheReserve 8 (by decide : 0 < 8) ⟨0#8, 255#8⟩ 1 = none := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Abstract `Option` layout strategy selector modeling `calculate_niche_filling_layout` fallback
to `TagEncoding::Direct` when `nicheReserve` returns `none`. -/
inductive OptionEncodingKind (w : Nat) where
  | niche (nicheStart : BitVec w) (nextRange : WrappingRange w) (totalBytes : Nat)
  | directSpill (tagBytes : Nat) (totalBytes : Nat)

noncomputable def layoutOptionScalar (w : Nat) (hw : 0 < w)
    (payloadBytes payloadAlign : Nat) (r : WrappingRange w) : OptionEncodingKind w :=
  match nicheReserve w hw r 1 with
  | some (ns, r') => .niche ns r' payloadBytes
  | none =>
    let tagBytes := payloadAlign -- simplified aligned discriminant prefix for pointer/byte spill
    let total := (if payloadAlign ≤ payloadBytes then payloadBytes + payloadAlign else 2 * payloadAlign)
    .directSpill tagBytes total

theorem nonNull64_opt_opt_spills_to_16B :
    layoutOptionScalar 64 (by decide : 0 < 64) 8 8 ⟨0#64, BitVec.ofNat 64 (2 ^ 64 - 1)⟩ =
      .directSpill 8 16 := by
  rfl

theorem nonZero8_opt_opt_spills_to_2B :
    layoutOptionScalar 8 (by decide : 0 < 8) 1 1 ⟨0#8, 255#8⟩ =
      .directSpill 1 2 := by
  rfl

/-! ## Section 6: `#[repr(u8)]` vs. `#[repr(C, u8)]` vs. `#[repr(C)]` & `E0732` -/

/-- Enum representation attributes (`rustc_abi::ReprOptions`). -/
inductive EnumReprAttr where
  | rust
  | c
  | int (signed : Bool) (bw : BitWidth)
  | cInt (signed : Bool) (bw : BitWidth)

noncomputable def EnumReprAttr.isC : EnumReprAttr → Bool
  | .c | .cInt _ _ => true
  | .rust | .int _ _ => false

noncomputable def EnumReprAttr.intRepr : EnumReprAttr → Option (Bool × BitWidth)
  | .int s bw | .cInt s bw => some (s, bw)
  | .rust | .c => none

noncomputable def EnumReprAttr.inhibitsNicheOpt : EnumReprAttr → Bool
  | .rust => false
  | .c | .int _ _ | .cInt _ _ => true

/-- Whether `zerocopy-derive` (`zerocopy-derive/src/repr.rs`) accepts the `#[repr]`.
Note: `zerocopy-derive` accepts `#[repr(C)]` and `#[repr(Int)]`, and rejects `#[repr(C, Int)]`
and default `#[repr(Rust)]`. -/
noncomputable def zerocopyDeriveAcceptsRepr : EnumReprAttr → Bool
  | .c | .int _ _ => true
  | .rust | .cInt _ _ => false

theorem zerocopyDerive_rejects_cInt_and_rust :
    zerocopyDeriveAcceptsRepr (.cInt false .w8) = false ∧
    zerocopyDeriveAcceptsRepr .rust = false := by
  exact ⟨rfl, rfl⟩

/-- Alignment helper matching `Size::align_to` (`a` positive power of two). -/
noncomputable def alignUp (n a : Nat) : Nat :=
  if a = 0 then n else ((n + a - 1) / a) * a

/-- Field layout descriptor `(size, align)`. -/
structure FieldMeta where
  size : Nat
  align : Nat

/-- Variant declaration for `#[repr]` layout and `E0732` checking. -/
structure VariantDecl where
  hasExplicitDiscr : Bool
  discrVal : Int
  fields : List FieldMeta

noncomputable def VariantDecl.isUnit (v : VariantDecl) : Bool :=
  v.fields.isEmpty

/-- `E0732` static check (`compiler/rustc_hir_analysis/src/check/check.rs:1888-1925`):
returns `true` if valid, `false` if compiler must emit `E0732`. -/
noncomputable def checkE0732 (repr : EnumReprAttr) (variants : List VariantDecl) : Bool :=
  match repr.intRepr with
  | some _ => true
  | none =>
    let hasNonUnit := variants.any (fun v => !v.isUnit)
    let hasExplicitUnit := variants.any (fun v => v.isUnit && v.hasExplicitDiscr)
    let hasExplicitNonUnit := variants.any (fun v => !v.isUnit && v.hasExplicitDiscr)
    !(hasExplicitNonUnit || (hasExplicitUnit && hasNonUnit))

/-- Exact `E0732` conformance witnesses. -/
theorem e0732_witnesses :
    let vExplicitNonUnit : List VariantDecl :=
      [⟨true, 5, [⟨2, 2⟩]⟩, ⟨true, 9, [⟨1, 1⟩]⟩]
    let vExplicitUnitWithPayload : List VariantDecl :=
      [⟨false, 0, [⟨2, 2⟩]⟩, ⟨true, 9, []⟩]
    let vCLike : List VariantDecl :=
      [⟨true, 1, []⟩, ⟨true, 2, []⟩]
    let vCImplicitPayload : List VariantDecl :=
      [⟨false, 0, [⟨2, 2⟩]⟩, ⟨false, 1, [⟨1, 1⟩]⟩]
    checkE0732 .c vExplicitNonUnit = false ∧
    checkE0732 .c vExplicitUnitWithPayload = false ∧
    checkE0732 .rust vExplicitNonUnit = false ∧
    checkE0732 (.int false .w8) vExplicitNonUnit = true ∧
    checkE0732 (.cInt false .w8) vExplicitNonUnit = true ∧
    checkE0732 .c vCLike = true ∧
    checkE0732 .c vCImplicitPayload = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Discriminant tag byte size chosen by `discr_range_of_repr` on x86-64/Linux
(`c_enum_min_size = 4` bytes when `repr.isC` and no explicit `intRepr`). -/
noncomputable def directTagBytes (repr : EnumReprAttr) : Nat :=
  match repr.intRepr with
  | some (_, bw) => bw.bytes
  | none => if repr.isC then 4 else 1

noncomputable def maxFieldAlignList : List FieldMeta → Nat
  | [] => 1
  | f :: fs => Nat.max f.align (maxFieldAlignList fs)

noncomputable def maxVariantAlign : List VariantDecl → Nat
  | [] => 1
  | v :: vs => Nat.max (maxFieldAlignList v.fields) (maxVariantAlign vs)

/-- `prefix_align` in `compiler/rustc_abi/src/layout.rs:822-829`. -/
noncomputable def enumPrefixAlign (repr : EnumReprAttr) (variants : List VariantDecl) : Nat :=
  let tagAlign := directTagBytes repr
  if repr.isC then
    Nat.max tagAlign (maxVariantAlign variants)
  else
    tagAlign

/-- Lay out fields of a single variant given `StructKind::Prefixed(prefixSize, prefixAlign)`
(`compiler/rustc_abi/src/layout.rs:1257-1307`). Returns `(fieldOffsets, variantEnd, variantAlign)`. -/
noncomputable def layoutVariantFieldsAux (cursor : Nat) (maxA : Nat) :
    List FieldMeta → List Nat × Nat × Nat
  | [] => ([], cursor, maxA)
  | f :: fs =>
    let off := alignUp cursor f.align
    let nextCursor := off + f.size
    let nextAlign := Nat.max maxA f.align
    let (restOffs, endCur, endAlign) := layoutVariantFieldsAux nextCursor nextAlign fs
    (off :: restOffs, endCur, endAlign)

noncomputable def layoutPrefixedVariant (prefixSize prefixAlign : Nat) (fields : List FieldMeta) :
    List Nat × Nat × Nat :=
  let initOffset := alignUp prefixSize prefixAlign
  layoutVariantFieldsAux initOffset prefixAlign fields

/-- Full direct-tag enum layout summary `(totalSize, totalAlign, tagBytes, variantFieldOffsets)`. -/
structure DirectEnumLayout where
  totalSize : Nat
  totalAlign : Nat
  tagBytes : Nat
  variantOffsets : List (List Nat)

private noncomputable def collectVariantLayouts (prefixSize prefixAlign : Nat) :
    List VariantDecl → Nat × Nat × List (List Nat)
  | [] => (prefixSize, prefixAlign, [])
  | v :: vs =>
    let (offs, vEnd, vAlign) := layoutPrefixedVariant prefixSize prefixAlign v.fields
    let (restMaxSize, restMaxAlign, restOffs) := collectVariantLayouts prefixSize prefixAlign vs
    (Nat.max vEnd restMaxSize, Nat.max vAlign restMaxAlign, offs :: restOffs)

noncomputable def computeDirectEnumLayout (repr : EnumReprAttr) (variants : List VariantDecl) :
    DirectEnumLayout :=
  let tagB := directTagBytes repr
  let pAlign := enumPrefixAlign repr variants
  let (rawMaxSize, maxAlign, offs) := collectVariantLayouts tagB pAlign variants
  let finalSize := alignUp rawMaxSize maxAlign
  ⟨finalSize, maxAlign, tagB, offs⟩

/-- **Theorem 4 (`#[repr(u8)]` vs. `#[repr(C, u8)]` vs. `#[repr(C)]` Field-Offset Divergence)**:
For variants `A(u16)` and `B(u8)`:
- `#[repr(u8)]` has `(size = 4, align = 2, tag = 1, offset(A.0) = 2, offset(B.0) = 1)`.
- `#[repr(C, u8)]` has `(size = 4, align = 2, tag = 1, offset(A.0) = 2, offset(B.0) = 2)` (`prefixAlign = 2` inserts 1 padding byte in `B`).
- `#[repr(C)]` has `(size = 8, align = 4, tag = 4, offset(A.0) = 4, offset(B.0) = 4)`. -/
theorem repr_u8_cu8_c_field_offset_divergence :
    let vs : List VariantDecl := [⟨false, 0, [⟨2, 2⟩]⟩, ⟨false, 1, [⟨1, 1⟩]⟩]
    computeDirectEnumLayout (.int false .w8) vs = ⟨4, 2, 1, [[2], [1]]⟩ ∧
    computeDirectEnumLayout (.cInt false .w8) vs = ⟨4, 2, 1, [[2], [2]]⟩ ∧
    computeDirectEnumLayout .c vs = ⟨8, 4, 4, [[4], [4]]⟩ := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## Section 7: `zerocopy::TryFromBytes` Byte-Level Semantics & Tag-First Soundness -/

/-- Byte array abstraction (values in `0..256` represented as `UInt8` for decidable equality). -/
noncomputable def readSlice (bytes : List UInt8) (offset len : Nat) : Option (List UInt8) :=
  if Nat.ble (offset + len) bytes.length then
    some ((bytes.drop offset).take len)
  else
    none

private theorem take_length_of_le {α : Type} (n : Nat) (xs : List α) (h : n ≤ xs.length) :
    (xs.take n).length = n := by
  rw [List.length_take]
  exact Nat.min_eq_left h

theorem readSlice_length {bytes : List UInt8} {offset len : Nat} {sub : List UInt8}
    (h : readSlice bytes offset len = some sub) : sub.length = len := by
  unfold readSlice at h
  cases hle : Nat.ble (offset + len) bytes.length with
  | false => rw [hle] at h; contradiction
  | true =>
    rw [hle] at h
    have hbound : offset + len ≤ bytes.length := (nat_ble_true_iff _ _).mp hle
    have heq := Option.some.inj h
    rw [← heq]
    apply take_length_of_le
    rw [List.length_drop]
    have hstep := nat_sub_le_sub_right hbound (c := offset)
    rw [Nat.add_comm offset len, Nat.add_sub_cancel] at hstep
    exact hstep

/-- Little-endian natural-number decoding of `List UInt8`. -/
noncomputable def decodeLE : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeLE bs

theorem decodeLE_lt (bs : List UInt8) : decodeLE bs < 2 ^ (8 * bs.length) := by
  induction bs with
  | nil =>
    exact Nat.succ_pos 0
  | cons b rest ih =>
    unfold decodeLE
    have hb : b.toNat < 256 := UInt8.toNat_lt b
    have hpos : 1 ≤ 2 ^ (8 * rest.length) := pow2_pos (8 * rest.length)
    have hpred : decodeLE rest ≤ 2 ^ (8 * rest.length) - 1 := Nat.le_pred_of_lt ih
    have hmul : 256 * decodeLE rest ≤ 256 * (2 ^ (8 * rest.length) - 1) :=
      Nat.mul_le_mul_left 256 hpred
    have hbound : b.toNat + 256 * decodeLE rest < 256 + 256 * (2 ^ (8 * rest.length) - 1) :=
      Nat.add_lt_add_of_lt_of_le hb hmul
    have hrhs : 256 + 256 * (2 ^ (8 * rest.length) - 1) = 2 ^ (8 * (b :: rest).length) := by
      have hsucc : 1 + (2 ^ (8 * rest.length) - 1) = 2 ^ (8 * rest.length) := by
        rw [Nat.add_comm]
        exact Nat.sub_add_cancel hpos
      have hdist : 256 + 256 * (2 ^ (8 * rest.length) - 1) =
          256 * (1 + (2 ^ (8 * rest.length) - 1)) := by
        rw [Nat.mul_add, Nat.mul_one]
      rw [hdist, hsucc]
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.pow_add]
      have h256 : (256 : Nat) = 2 ^ 8 := rfl
      rw [h256, Nat.mul_comm]
    rw [hrhs] at hbound
    exact hbound

/-- Abstract semantic value decoded from an enum or primitive field. -/
inductive DecodedVal where
  | scalar (w : Nat) (val : BitVec w)
  | variant (idx : Nat) (fields : List DecodedVal)
  | optNone (depth : Nat)
  | optSome (depth : Nat) (inner : DecodedVal)

/-- Verified field type contract (`TryFromBytes` soundness invariant at a field type):
`isValid` agrees with total decoding on exact-size byte slices. -/
structure FieldCodec where
  size : Nat
  isValid : List UInt8 → Bool
  decode : List UInt8 → Option DecodedVal
  sound : ∀ bs : List UInt8, bs.length = size → isValid bs = true → ∃ v, decode bs = some v
  complete : ∀ bs : List UInt8, bs.length = size → (∃ v, decode bs = some v) → isValid bs = true

/-- Concrete `FieldCodec` for `bool` (`zerocopy/src/impls.rs:113-116`: `*byte < 2`). -/
noncomputable def boolCodec : FieldCodec where
  size := 1
  isValid bs :=
    match bs with
    | [b] => Nat.blt b.toNat 2
    | _ => false
  decode bs :=
    match bs with
    | [b] =>
      if Nat.blt b.toNat 2 then
        some (.scalar 8 (BitVec.ofNat 8 b.toNat))
      else
        none
    | _ => none
  sound bs hlen hv := by
    cases bs with
    | nil => contradiction
    | cons b rest =>
      cases rest with
      | nil =>
        dsimp only at hv ⊢
        rw [hv]
        exact ⟨.scalar 8 (BitVec.ofNat 8 b.toNat), rfl⟩
      | cons _ _ => contradiction
  complete bs hlen hex := by
    cases bs with
    | nil => contradiction
    | cons b rest =>
      cases rest with
      | nil =>
        dsimp only at hex ⊢
        obtain ⟨v, hv⟩ := hex
        cases hlt : Nat.blt b.toNat 2 with
        | true => rfl
        | false =>
          rw [hlt] at hv
          contradiction
      | cons _ _ =>
        obtain ⟨_, h⟩ := hex
        contradiction

/-- Concrete `FieldCodec` for `u8` (`FromBytes`, always valid at length 1). -/
noncomputable def u8Codec : FieldCodec where
  size := 1
  isValid bs := Nat.beq bs.length 1
  decode bs :=
    match bs with
    | [b] => some (.scalar 8 (BitVec.ofNat 8 b.toNat))
    | _ => none
  sound bs hlen _ := by
    cases bs with
    | nil => contradiction
    | cons b rest =>
      cases rest with
      | nil => exact ⟨.scalar 8 (BitVec.ofNat 8 b.toNat), rfl⟩
      | cons _ _ => contradiction
  complete bs hlen _ := by
    rw [hlen]
    rfl

/-- Concrete `FieldCodec` for `u16` (`FromBytes`, always valid at length 2). -/
noncomputable def u16Codec : FieldCodec where
  size := 2
  isValid bs := Nat.beq bs.length 2
  decode bs :=
    if Nat.beq bs.length 2 then
      some (.scalar 16 (BitVec.ofNat 16 (decodeLE bs)))
    else
      none
  sound bs hlen hv := by
    rw [hv]
    exact ⟨.scalar 16 (BitVec.ofNat 16 (decodeLE bs)), rfl⟩
  complete bs hlen _ := by
    rw [hlen]
    rfl

/-- Concrete `FieldCodec` for `char` (`zerocopy/src/impls.rs:141-147`: `<= 0x10FFFF` and not surrogate `0xD800..=0xDFFF`). -/
noncomputable def isUnicodeScalarNat (n : Nat) : Bool :=
  Nat.ble n 0x10FFFF && !(Nat.ble 0xD800 n && Nat.ble n 0xDFFF)

noncomputable def charCodec : FieldCodec where
  size := 4
  isValid bs :=
    Nat.beq bs.length 4 && isUnicodeScalarNat (decodeLE bs)
  decode bs :=
    if Nat.beq bs.length 4 && isUnicodeScalarNat (decodeLE bs) then
      some (.scalar 32 (BitVec.ofNat 32 (decodeLE bs)))
    else
      none
  sound bs _ hv := by
    rw [hv]
    exact ⟨.scalar 32 (BitVec.ofNat 32 (decodeLE bs)), rfl⟩
  complete bs _ hex := by
    obtain ⟨v, hv⟩ := hex
    cases h : (Nat.beq bs.length 4 && isUnicodeScalarNat (decodeLE bs)) with
    | true => rfl
    | false =>
      rw [h] at hv
      contradiction

/-- Concrete `FieldCodec` for `NonZero<u8>` (`b != 0`). -/
noncomputable def nonZeroU8Codec : FieldCodec where
  size := 1
  isValid bs :=
    match bs with
    | [b] => !(b == 0)
    | _ => false
  decode bs :=
    match bs with
    | [b] =>
      if !(b == 0) then
        some (.scalar 8 (BitVec.ofNat 8 b.toNat))
      else
        none
    | _ => none
  sound bs _ hv := by
    cases bs with
    | nil => contradiction
    | cons b rest =>
      cases rest with
      | nil =>
        dsimp only at hv ⊢
        rw [hv]
        exact ⟨.scalar 8 (BitVec.ofNat 8 b.toNat), rfl⟩
      | cons _ _ => contradiction
  complete bs _ hex := by
    cases bs with
    | nil =>
      obtain ⟨_, hv⟩ := hex
      contradiction
    | cons b rest =>
      cases rest with
      | nil =>
        dsimp only at hex ⊢
        obtain ⟨_, hv⟩ := hex
        cases hz : !(b == 0) with
        | true => rfl
        | false =>
          rw [hz] at hv
          contradiction
      | cons _ _ =>
        obtain ⟨_, hv⟩ := hex
        contradiction

/-- Field placement inside a variant `(offset, codec)`. -/
structure PlacedField where
  offset : Nat
  codec : FieldCodec

/-- Validate all placed fields of a variant sequentially (`derive_variant_is_safe` in
`zerocopy-derive/src/derive/try_from_bytes.rs:33-71`). -/
noncomputable def validateFields (bytes : List UInt8) : List PlacedField → Bool
  | [] => true
  | pf :: rest =>
    match readSlice bytes pf.offset pf.codec.size with
    | some sub => pf.codec.isValid sub && validateFields bytes rest
    | none => false

/-- Decode all placed fields of a variant sequentially. -/
noncomputable def decodeFields (bytes : List UInt8) : List PlacedField → Option (List DecodedVal)
  | [] => some []
  | pf :: rest =>
    match readSlice bytes pf.offset pf.codec.size with
    | none => none
    | some sub =>
      match pf.codec.decode sub, decodeFields bytes rest with
      | some v, some vs => some (v :: vs)
      | _, _ => none

theorem validateFields_sound (bytes : List UInt8) (pfs : List PlacedField)
    (hv : validateFields bytes pfs = true) :
    ∃ vals : List DecodedVal, decodeFields bytes pfs = some vals := by
  induction pfs with
  | nil => exact ⟨[], rfl⟩
  | cons pf rest ih =>
    unfold validateFields at hv
    unfold decodeFields
    cases hs : readSlice bytes pf.offset pf.codec.size with
    | none =>
      rw [hs] at hv
      contradiction
    | some sub =>
      rw [hs] at hv
      obtain ⟨hv1, hvRest⟩ := (bool_and_eq_true _ _).mp hv
      have hlen : sub.length = pf.codec.size := readSlice_length hs
      obtain ⟨v, hvdec⟩ := pf.codec.sound sub hlen hv1
      obtain ⟨vs, hrest⟩ := ih hvRest
      dsimp only
      rw [hvdec, hrest]
      exact ⟨v :: vs, rfl⟩

theorem validateFields_complete (bytes : List UInt8) (pfs : List PlacedField)
    (hdec : ∃ vals : List DecodedVal, decodeFields bytes pfs = some vals) :
    validateFields bytes pfs = true := by
  induction pfs with
  | nil => rfl
  | cons pf rest ih =>
    unfold decodeFields at hdec
    unfold validateFields
    obtain ⟨vals, hvals⟩ := hdec
    cases hs : readSlice bytes pf.offset pf.codec.size with
    | none =>
      rw [hs] at hvals
      contradiction
    | some sub =>
      rw [hs] at hvals
      dsimp only at hvals
      cases hfv : pf.codec.decode sub with
      | none =>
        rw [hfv] at hvals
        contradiction
      | some v =>
        cases hrv : decodeFields bytes rest with
        | none =>
          rw [hfv, hrv] at hvals
          contradiction
        | some vs =>
          have hlen : sub.length = pf.codec.size := readSlice_length hs
          have h1 := pf.codec.complete sub hlen ⟨v, hfv⟩
          have h2 := ih ⟨vs, hrv⟩
          exact (bool_and_eq_true _ _).mpr ⟨h1, h2⟩

/-- One variant of a direct-tag enum: `(tagVal, variantIdx, placedFields)`. -/
structure DirectVariant where
  tagVal : Nat
  variantIdx : Nat
  fields : List PlacedField

/-- Direct-tag enum representation (`TagEncoding::Direct`, matching `derive_is_safe` in
`zerocopy-derive/src/derive/try_from_bytes.rs:121-227`). -/
structure DirectEnumModel where
  totalSize : Nat
  tagSize : Nat
  variants : List DirectVariant

noncomputable def findDirectVariant (tag : Nat) : List DirectVariant → Option DirectVariant
  | [] => none
  | v :: vs => if Nat.beq v.tagVal tag then some v else findDirectVariant tag vs

/-- Tag-first validity check matching `zerocopy-derive`'s `is_safe` on enums:
1. Check byte length equals `totalSize`;
2. Read `tagSize` bytes at offset `0` (`___ZerocopyTagPrimitive`);
3. Match `tag` against declared discriminant constants (`match #tag { ... _ => false }`);
4. Only for the matched variant, project and validate each field via `validateFields`. -/
noncomputable def isBitValidDirect (m : DirectEnumModel) (bytes : List UInt8) : Bool :=
  if !Nat.beq bytes.length m.totalSize then
    false
  else
    match readSlice bytes 0 m.tagSize with
    | none => false
    | some tagBytes =>
      match findDirectVariant (decodeLE tagBytes) m.variants with
      | none => false
      | some v => validateFields bytes v.fields

/-- Total reference decoder corresponding to `DirectEnumModel`. -/
noncomputable def decodeDirect (m : DirectEnumModel) (bytes : List UInt8) : Option DecodedVal :=
  if !Nat.beq bytes.length m.totalSize then
    none
  else
    match readSlice bytes 0 m.tagSize with
    | none => none
    | some tagBytes =>
      match findDirectVariant (decodeLE tagBytes) m.variants with
      | none => none
      | some v =>
        match decodeFields bytes v.fields with
        | none => none
        | some vals => some (.variant v.variantIdx vals)

/-- **Theorem 5 (Tag-First Direct-Enum `TryFromBytes` Bit-Validity Soundness & Completeness)**:
For any `DirectEnumModel` and byte slice `bytes`, `isBitValidDirect m bytes = true` iff
`decodeDirect m bytes` returns `some _`. Furthermore, invalid tags fail at step (3) before any
variant field projection occurs. -/
theorem isBitValidDirect_iff_decode_some (m : DirectEnumModel) (bytes : List UInt8) :
    isBitValidDirect m bytes = true ↔ ∃ val : DecodedVal, decodeDirect m bytes = some val := by
  unfold isBitValidDirect decodeDirect
  cases hlen : Nat.beq bytes.length m.totalSize with
  | false =>
    simp
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    cases hts : readSlice bytes 0 m.tagSize with
    | none =>
      simp
    | some tagBytes =>
      dsimp only
      cases hfv : findDirectVariant (decodeLE tagBytes) m.variants with
      | none =>
        simp
      | some v =>
        dsimp only
        constructor
        · intro hv
          obtain ⟨vals, hdec⟩ := validateFields_sound bytes v.fields hv
          rw [hdec]
          exact ⟨.variant v.variantIdx vals, rfl⟩
        · intro ⟨_, hdec⟩
          cases hdf : decodeFields bytes v.fields with
          | none =>
            rw [hdf] at hdec
            contradiction
          | some vals =>
            exact validateFields_complete bytes v.fields ⟨vals, hdf⟩

theorem isBitValidDirect_rejects_unknown_tag (m : DirectEnumModel) (bytes : List UInt8)
    (tagBytes : List UInt8)
    (hts : readSlice bytes 0 m.tagSize = some tagBytes)
    (hmiss : findDirectVariant (decodeLE tagBytes) m.variants = none) :
    isBitValidDirect m bytes = false := by
  unfold isBitValidDirect
  cases hlen : Nat.beq bytes.length m.totalSize with
  | false => rfl
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [hts]
    dsimp only
    rw [hmiss]

/-! ## Section 8: Multi-Level Stacked-Niche `Option^k(T)` Validity & Zero-UB Soundness -/

/-- Outer-first stacked-niche decoder and validator matching `read_discriminant` (`TagEncoding::Niche`)
and `ValidityVisitor` in `rustc_const_eval`. -/
noncomputable def evalOuterSteps (w : Nat) (baseCodec : FieldCodec) (tag : BitVec w)
    (bytes : List UInt8) (depth : Nat) : List (NicheStep w) → Option DecodedVal
  | [] => baseCodec.decode bytes
  | st :: rest =>
    if !st.rangeAfter.contains tag then
      none
    else if tag == st.nicheStart then
      some (.optNone depth)
    else
      match evalOuterSteps w baseCodec tag bytes (depth + 1) rest with
      | some inner => some (.optSome depth inner)
      | none => none

noncomputable def checkOuterSteps (w : Nat) (baseCodec : FieldCodec) (tag : BitVec w)
    (bytes : List UInt8) : List (NicheStep w) → Bool
  | [] => baseCodec.isValid bytes
  | st :: rest =>
    if !st.rangeAfter.contains tag then
      false
    else if tag == st.nicheStart then
      true
    else
      checkOuterSteps w baseCodec tag bytes rest

noncomputable def decodeNicheStackClean (w : Nat) (baseCodec : FieldCodec)
    (outerSteps : List (NicheStep w)) (bytes : List UInt8) : Option DecodedVal :=
  if !Nat.beq (8 * bytes.length) w then
    none
  else
    evalOuterSteps w baseCodec (BitVec.ofNat w (decodeLE bytes)) bytes 0 outerSteps

noncomputable def isBitValidNicheStackClean (w : Nat) (baseCodec : FieldCodec)
    (outerSteps : List (NicheStep w)) (bytes : List UInt8) : Bool :=
  if !Nat.beq (8 * bytes.length) w then
    false
  else
    checkOuterSteps w baseCodec (BitVec.ofNat w (decodeLE bytes)) bytes outerSteps

private theorem checkOuterSteps_iff_eval_some (w : Nat) (baseCodec : FieldCodec)
    (tag : BitVec w) (bytes : List UInt8) (_hsz : 8 * bytes.length = w)
    (hcodecLen : baseCodec.size = bytes.length)
    (outerSteps : List (NicheStep w)) (depth : Nat) :
    checkOuterSteps w baseCodec tag bytes outerSteps = true ↔
      ∃ val : DecodedVal, evalOuterSteps w baseCodec tag bytes depth outerSteps = some val := by
  induction outerSteps generalizing depth with
  | nil =>
    unfold checkOuterSteps evalOuterSteps
    constructor
    · intro hv
      exact baseCodec.sound bytes hcodecLen.symm hv
    · intro hex
      exact baseCodec.complete bytes hcodecLen.symm hex
  | cons st rest ih =>
    unfold checkOuterSteps evalOuterSteps
    cases hcont : st.rangeAfter.contains tag with
    | false =>
      simp
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      cases hns : (tag == st.nicheStart) with
      | true =>
        simp
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        constructor
        · intro hrest
          obtain ⟨inner, hinner⟩ := (ih (depth + 1)).mp hrest
          rw [hinner]
          exact ⟨.optSome depth inner, rfl⟩
        · intro ⟨val, hval⟩
          cases hrec : evalOuterSteps w baseCodec tag bytes (depth + 1) rest with
          | none =>
            rw [hrec] at hval
            contradiction
          | some inner =>
            exact (ih (depth + 1)).mpr ⟨inner, hrec⟩

/-- **Theorem 6 (Tag-First `Option^k(T)` Niche-Stack Bit-Validity Soundness & Completeness)**:
Whenever `8 * baseCodec.size = w`, the tag-first stacked checker `isBitValidNicheStackClean` returns
`true` iff the total zero-UB decoder `decodeNicheStackClean` produces `some val`. -/
theorem isBitValidNicheStack_iff_decode_some (w : Nat) (baseCodec : FieldCodec)
    (hbw : 8 * baseCodec.size = w) (outerSteps : List (NicheStep w)) (bytes : List UInt8) :
    isBitValidNicheStackClean w baseCodec outerSteps bytes = true ↔
      ∃ val : DecodedVal, decodeNicheStackClean w baseCodec outerSteps bytes = some val := by
  unfold isBitValidNicheStackClean decodeNicheStackClean
  cases hlen : Nat.beq (8 * bytes.length) w with
  | false =>
    simp
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    have hweq : 8 * bytes.length = w := Nat.beq_eq.mp hlen
    have hmul : 8 * baseCodec.size = 8 * bytes.length := hbw.trans hweq.symm
    have hsz : baseCodec.size = bytes.length :=
      Nat.eq_of_mul_eq_mul_left (Nat.succ_pos 7) hmul
    exact checkOuterSteps_iff_eval_some w baseCodec _ bytes hweq hsz outerSteps 0

/-! ## Section 9: End-to-End Concrete Verification Witnesses (`Option^2(bool)`, `Option^3(bool)`, `Option^3(char)`, `PacketU8`, `PacketC`) -/

/-- Exact 3-level `Option<Option<Option<bool>>>` step stack (outer-first: L3, L2, L1). -/
noncomputable def opt3BoolOuterSteps : List (NicheStep 8) :=
  [ ⟨1, 254#8, ⟨254#8, 2#8⟩⟩,
    ⟨1, 255#8, ⟨255#8, 2#8⟩⟩,
    ⟨1, 2#8, ⟨0#8, 2#8⟩⟩ ]

/-- Exact 2-level `Option<Option<bool>>` step stack (outer-first: L2, L1). -/
noncomputable def opt2BoolOuterSteps : List (NicheStep 8) :=
  [ ⟨1, 255#8, ⟨255#8, 2#8⟩⟩,
    ⟨1, 2#8, ⟨0#8, 2#8⟩⟩ ]

/-- Exact 3-level `Option<Option<Option<char>>>` step stack (outer-first). -/
noncomputable def opt3CharOuterSteps : List (NicheStep 32) :=
  [ ⟨1, BitVec.ofNat 32 0xFFFFFFFD, ⟨BitVec.ofNat 32 0xFFFFFFFD, BitVec.ofNat 32 0x10FFFF⟩⟩,
    ⟨1, BitVec.ofNat 32 0xFFFFFFFE, ⟨BitVec.ofNat 32 0xFFFFFFFE, BitVec.ofNat 32 0x10FFFF⟩⟩,
    ⟨1, BitVec.ofNat 32 0xFFFFFFFF, ⟨BitVec.ofNat 32 0xFFFFFFFF, BitVec.ofNat 32 0x10FFFF⟩⟩ ]

/-- Concrete witness: `Option<Option<bool>>` accepts `[0, 1, 2, 255]` and rejects `0x03`! -/
theorem opt2Bool_witness_decode :
    decodeNicheStackClean 8 boolCodec opt2BoolOuterSteps [0] =
      some (.optSome 0 (.optSome 1 (.scalar 8 0#8))) ∧
    decodeNicheStackClean 8 boolCodec opt2BoolOuterSteps [1] =
      some (.optSome 0 (.optSome 1 (.scalar 8 1#8))) ∧
    decodeNicheStackClean 8 boolCodec opt2BoolOuterSteps [2] =
      some (.optSome 0 (.optNone 1)) ∧
    decodeNicheStackClean 8 boolCodec opt2BoolOuterSteps [255] =
      some (.optNone 0) ∧
    decodeNicheStackClean 8 boolCodec opt2BoolOuterSteps [3] = none ∧
    isBitValidNicheStackClean 8 boolCodec opt2BoolOuterSteps [3] = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Concrete witness: `Option<Option<Option<bool>>>` accepts `[0, 1, 2, 255, 254]` and rejects `0x03`! -/
theorem opt3Bool_witness_decode :
    decodeNicheStackClean 8 boolCodec opt3BoolOuterSteps [0] =
      some (.optSome 0 (.optSome 1 (.optSome 2 (.scalar 8 0#8)))) ∧
    decodeNicheStackClean 8 boolCodec opt3BoolOuterSteps [1] =
      some (.optSome 0 (.optSome 1 (.optSome 2 (.scalar 8 1#8)))) ∧
    decodeNicheStackClean 8 boolCodec opt3BoolOuterSteps [2] =
      some (.optSome 0 (.optSome 1 (.optNone 2))) ∧
    decodeNicheStackClean 8 boolCodec opt3BoolOuterSteps [255] =
      some (.optSome 0 (.optNone 1)) ∧
    decodeNicheStackClean 8 boolCodec opt3BoolOuterSteps [254] =
      some (.optNone 0) ∧
    decodeNicheStackClean 8 boolCodec opt3BoolOuterSteps [3] = none ∧
    isBitValidNicheStackClean 8 boolCodec opt3BoolOuterSteps [3] = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Concrete witness: `Option<Option<Option<char>>>` decodes `[0x41, 0xffffffff, 0xfffffffe, 0xfffffffd]`
and rejects both `0x00110000` (invalid enum tag) and `0x0000D800` (surrogate inner char)! -/
theorem opt3Char_witness_decode :
    decodeNicheStackClean 32 charCodec opt3CharOuterSteps [0x41, 0, 0, 0] =
      some (.optSome 0 (.optSome 1 (.optSome 2 (.scalar 32 (BitVec.ofNat 32 0x41))))) ∧
    decodeNicheStackClean 32 charCodec opt3CharOuterSteps [0xFF, 0xFF, 0xFF, 0xFF] =
      some (.optSome 0 (.optSome 1 (.optNone 2))) ∧
    decodeNicheStackClean 32 charCodec opt3CharOuterSteps [0xFE, 0xFF, 0xFF, 0xFF] =
      some (.optSome 0 (.optNone 1)) ∧
    decodeNicheStackClean 32 charCodec opt3CharOuterSteps [0xFD, 0xFF, 0xFF, 0xFF] =
      some (.optNone 0) ∧
    decodeNicheStackClean 32 charCodec opt3CharOuterSteps [0x00, 0x00, 0x11, 0x00] = none ∧
    decodeNicheStackClean 32 charCodec opt3CharOuterSteps [0x00, 0xD8, 0x00, 0x00] = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Concrete `PacketU8` (`#[repr(u8)] enum PacketU8 { A(u16) = 5, B(u8) = 9, C(bool) = 12 }`)
matching the compiled `zerocopy::TryFromBytes` probe:
- `A(u16)`: offset `2`, size `2`
- `B(u8)`: offset `1`, size `1`
- `C(bool)`: offset `1`, size `1` -/
noncomputable def packetU8Model : DirectEnumModel :=
  ⟨4, 1,
    [ ⟨5, 0, [⟨2, u16Codec⟩]⟩,
      ⟨9, 1, [⟨1, u8Codec⟩]⟩,
      ⟨12, 2, [⟨1, boolCodec⟩]⟩ ]⟩

/-- Concrete `PacketC` (`#[repr(C)] enum PacketC { A(u16), B(bool) }`) matching the compiled
`zerocopy::TryFromBytes` probe (`tag = 4B`, `A(u16)` at `4`, `B(bool)` at `4`, total `8B`). -/
noncomputable def packetCModel : DirectEnumModel :=
  ⟨8, 4,
    [ ⟨0, 0, [⟨4, u16Codec⟩]⟩,
      ⟨1, 1, [⟨4, boolCodec⟩]⟩ ]⟩

theorem packetU8_and_packetC_witnesses :
    isBitValidDirect packetU8Model [5, 0xFF, 0x34, 0x12] = true ∧
    decodeDirect packetU8Model [5, 0xFF, 0x34, 0x12] =
      some (.variant 0 [.scalar 16 (BitVec.ofNat 16 0x1234)]) ∧
    isBitValidDirect packetU8Model [9, 0x42, 0xAA, 0xBB] = true ∧
    decodeDirect packetU8Model [9, 0x42, 0xAA, 0xBB] =
      some (.variant 1 [.scalar 8 0x42#8]) ∧
    isBitValidDirect packetU8Model [12, 1, 0xFF, 0xFF] = true ∧
    isBitValidDirect packetU8Model [12, 2, 0, 0] = false ∧
    isBitValidDirect packetU8Model [7, 0, 0, 0] = false ∧
    isBitValidDirect packetCModel [1, 0, 0, 0, 1, 0, 0, 0] = true ∧
    isBitValidDirect packetCModel [1, 0, 0, 0, 2, 0, 0, 0] = false ∧
    isBitValidDirect packetCModel [99, 0, 0, 0, 0, 0, 0, 0] = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 10: Chain Verification Witnesses for `Option^3(bool)` and `Option^3(char)` -/

theorem opt3Bool_niche_chain :
    NicheChain 8 (by decide : 0 < 8) boolRange ⟨254#8, 2#8⟩
      [ ⟨1, 2#8, ⟨0#8, 2#8⟩⟩,
        ⟨1, 255#8, ⟨255#8, 2#8⟩⟩,
        ⟨1, 254#8, ⟨254#8, 2#8⟩⟩ ] := by
  have c0 : NicheChain 8 (by decide : 0 < 8) boolRange boolRange [] :=
    NicheChain.nil boolRange
  have c1 : NicheChain 8 (by decide : 0 < 8) boolRange ⟨0#8, 2#8⟩ [⟨1, 2#8, ⟨0#8, 2#8⟩⟩] :=
    NicheChain.cons 1 2#8 c0 optBool_exact
  have c2 : NicheChain 8 (by decide : 0 < 8) boolRange ⟨255#8, 2#8⟩
      ([⟨1, 2#8, ⟨0#8, 2#8⟩⟩] ++ [⟨1, 255#8, ⟨255#8, 2#8⟩⟩]) :=
    NicheChain.cons 1 255#8 c1 optOptBool_exact
  have c3 : NicheChain 8 (by decide : 0 < 8) boolRange ⟨254#8, 2#8⟩
      (([⟨1, 2#8, ⟨0#8, 2#8⟩⟩, ⟨1, 255#8, ⟨255#8, 2#8⟩⟩]) ++ [⟨1, 254#8, ⟨254#8, 2#8⟩⟩]) :=
    NicheChain.cons 1 254#8 c2 opt3Bool_exact
  exact c3

theorem opt3Char_niche_chain :
    NicheChain 32 (by decide : 0 < 32) charScalarRange
      ⟨BitVec.ofNat 32 0xFFFFFFFD, BitVec.ofNat 32 0x10FFFF⟩
      [ ⟨1, BitVec.ofNat 32 0xFFFFFFFF, ⟨BitVec.ofNat 32 0xFFFFFFFF, BitVec.ofNat 32 0x10FFFF⟩⟩,
        ⟨1, BitVec.ofNat 32 0xFFFFFFFE, ⟨BitVec.ofNat 32 0xFFFFFFFE, BitVec.ofNat 32 0x10FFFF⟩⟩,
        ⟨1, BitVec.ofNat 32 0xFFFFFFFD, ⟨BitVec.ofNat 32 0xFFFFFFFD, BitVec.ofNat 32 0x10FFFF⟩⟩ ] := by
  have c0 : NicheChain 32 (by decide : 0 < 32) charScalarRange charScalarRange [] :=
    NicheChain.nil charScalarRange
  have c1 := NicheChain.cons 1 (BitVec.ofNat 32 0xFFFFFFFF) c0 optChar_exact
  have c2 := NicheChain.cons 1 (BitVec.ofNat 32 0xFFFFFFFE) c1 optOptChar_exact
  have c3 := NicheChain.cons 1 (BitVec.ofNat 32 0xFFFFFFFD) c2 opt3Char_exact
  exact c3

theorem opt3Bool_chain_disjoint_and_available :
    ChainTagsValid boolRange
      [ ⟨1, 2#8, ⟨0#8, 2#8⟩⟩,
        ⟨1, 255#8, ⟨255#8, 2#8⟩⟩,
        ⟨1, 254#8, ⟨254#8, 2#8⟩⟩ ] ∧
    (⟨254#8, 2#8⟩ : WrappingRange 8).available + 3 = boolRange.available := by
  refine ⟨(NicheChain.tags_sound opt3Bool_niche_chain).1, ?_⟩
  exact NicheChain.available_conservation opt3Bool_niche_chain

theorem opt3Char_chain_disjoint_and_available :
    ChainTagsValid charScalarRange
      [ ⟨1, BitVec.ofNat 32 0xFFFFFFFF, ⟨BitVec.ofNat 32 0xFFFFFFFF, BitVec.ofNat 32 0x10FFFF⟩⟩,
        ⟨1, BitVec.ofNat 32 0xFFFFFFFE, ⟨BitVec.ofNat 32 0xFFFFFFFE, BitVec.ofNat 32 0x10FFFF⟩⟩,
        ⟨1, BitVec.ofNat 32 0xFFFFFFFD, ⟨BitVec.ofNat 32 0xFFFFFFFD, BitVec.ofNat 32 0x10FFFF⟩⟩ ] ∧
    (⟨BitVec.ofNat 32 0xFFFFFFFD, BitVec.ofNat 32 0x10FFFF⟩ : WrappingRange 32).available + 3 =
      charScalarRange.available := by
  refine ⟨(NicheChain.tags_sound opt3Char_niche_chain).1, ?_⟩
  exact NicheChain.available_conservation opt3Char_niche_chain

end AbiNicheStacking
