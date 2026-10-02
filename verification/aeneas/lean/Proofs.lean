/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import Proofs.Util
public import Proofs.NestedReference
public import Aeneas
public import Loops
public import LayoutModel
public import RepresentationLaws
public import LayoutMath
import all Mathlib.Data.Nat.Log
import all Init.Data.Nat.Power2.Basic
@[expose] public section

/-!
This module proves contracts about the actual Aeneas function definitions.
The Raw namespace steps through extracted control flow and machine
arithmetic. Those lemmas deliberately retain useful representation domains,
even when an inline specification admits a smaller domain through automatic
decoding.

The canonical theorems outside Raw prove the generated Specs propositions.
They use the raw lemmas, decode accepted inputs, and establish that the
actual returned representation decodes and has the requested mathematical
properties. WP.spec_mono transfers a proved computation to a new
postcondition; it cannot replace that computation. Registered specifications
let later proofs reuse a callee's theorem instead of unfolding its
implementation each time.

Aeneas Result describes execution success, panic, or divergence. Rust Option
and Rust Result values may themselves be successful payloads. The proof must
keep these cases distinct.
-/
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw

set_option linter.unusedVariables false

/- Read the pinned platform's pointer width through its modeled primitive. This
establishes the runtime constant used by encoding and packing arithmetic.
-/
theorem pointer_width_spec :
    layout.POINTER_WIDTH_BITS
      ⦃ w => w.val = System.Platform.numBits ⦄ := by
  unfold layout.POINTER_WIDTH_BITS
  simp only [core.mem.size_of, ite_true, bind_ok]
  have hv : ({ bv := BitVec.ofNat _ (System.Platform.numBits / 8) } : Usize).val =
      System.Platform.numBits / 8 := by
    change (System.Platform.numBits / 8) % 2 ^ System.Platform.numBits = _
    rcases System.Platform.numBits_eq with h | h <;> simp only [h] <;> decide
  step as ⟨w, hw⟩
  · rw [hv]
    rcases System.Platform.numBits_eq with h | h <;>
      simp only [Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq, h,
        UScalar.val] <;> decide
  · rw [hv] at hw
    rcases System.Platform.numBits_eq with h | h <;>
      simp only [h] at hw ⊢ <;> omega

/- Connect the constructor's power-of-two and phase checks to exact encoding.
The canonical form also proves decoding of the actual returned word.
-/
theorem encoding_new_spec :
  ∀ (align : NonZeroUsize) (phase : Usize), ∀ (ha : (align.val.val.isPowerOfTwo : Prop)), ∀ (hp : (phase.val < align.val.val : Prop)),
    @Zerocopy.layout.RoundingAlignAndPhase.new align phase ⦃ encoded => encoded._0.val.val = align.val.val + phase.val ⦄ := by
  intro align phase ha hp
  unfold layout.RoundingAlignAndPhase.new
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step as ⟨b, hb⟩
  have hbt : b = true := by
    have hb' : (b = true) = True := by simpa only [ha] using hb
    exact Eq.mpr hb' trivial
  simp only [massert, hbt, if_true, bind_ok, UScalar.lt_equiv, hp, lift]
  obtain ⟨k, hk⟩ := ha
  have hor : (align.val ||| phase).val = align.val.val + phase.val := by
    rw [UScalar.val_or, hk]
    have h := Nat.two_pow_add_eq_or_of_lt (show phase.val < 2 ^ k by omega) 1
    simpa only [Nat.mul_one] using h.symm
  have hnz : align.val ||| phase ≠ 0#usize := by
    intro hz
    have hz' := congrArg UScalar.val hz
    rw [hor] at hz'
    have hpos := Nat.two_pow_pos k
    change align.val.val + phase.val = 0 at hz'
    omega
  simp only [core.num.nonzero.NonZero.new, cast_eq, hnz, ↓reduceDIte, ↓reduceIte,
    bind_ok, WP.spec_ok]
  exact hor

/- Remove the highest bit from align + phase when phase uses only lower bits.
The decoder implementation uses XOR; the mathematical model uses subtraction.
-/
theorem highest_bit_xor (k p : Nat) (hp : p < 2 ^ k) : (2 ^ k + p) ^^^ 2 ^ k = p := by
  have hjoin : 2 ^ k + p = 2 ^ k ||| p := by
    simpa only [Nat.mul_one] using Nat.two_pow_add_eq_or_of_lt hp 1
  rw [hjoin]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_or]
  by_cases hi : i = k
  · subst i
    rw [Nat.testBit_two_pow_self, Nat.testBit_lt_two_pow hp]
    rfl
  · rw [Nat.testBit_two_pow_of_ne (Ne.symm hi)]
    simp

/- Prove the implementation's bit scan recovers the alignment and phase of every
positive stored word, not only words built by the constructor.
-/
theorem encoding_components_spec :
  ∀ (self : layout.RoundingAlignAndPhase), ∀ (hn : (0 < self._0.val.val : Prop)),
    @Zerocopy.layout.RoundingAlignAndPhase.components self ⦃ (align, phase) =>
    align.val.val.isPowerOfTwo ∧ phase.val < align.val.val ∧
    align.val.val + phase.val = self._0.val.val ∧
    align.val.val = 2 ^ Nat.log2 self._0.val.val ∧
    phase.val = self._0.val.val - 2 ^ Nat.log2 self._0.val.val ⦄ := by
  intro self hn
  let k := Nat.log2 self._0.val.val
  have hbound := (Nat.log2_eq_iff (show self._0.val.val ≠ 0 by omega)).mp (show Nat.log2 self._0.val.val = k from rfl)
  have hsize := UScalar.hSize self._0.val
  rw [UScalar.size, UScalarTy.Usize_numBits_eq] at hsize
  have hk : k < System.Platform.numBits := by
    dsimp [k]
    rw [Nat.log2_eq_log_two]
    apply Nat.log_lt_of_lt_pow (by omega)
    exact hsize
  have hbits : 32 ≤ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> omega
  have hnzbv : self._0.val.bv ≠ 0 := by
    intro h
    have := congrArg BitVec.toNat h
    change self._0.val.val = 0 at this
    omega
  have hlz : (core.num.Usize.leading_zeros self._0.val).val = System.Platform.numBits - k - 1 := by
    change (BitVec.leadingZeros self._0.val.bv) % 2 ^ 32 = _
    unfold BitVec.leadingZeros
    rw [if_neg hnzbv]
    change (System.Platform.numBits - Nat.log 2 self._0.val.val - 1) % 2 ^ 32 = _
    rw [← Nat.log2_eq_log_two]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
  have hcast : (UScalar.cast .Usize (core.num.Usize.leading_zeros self._0.val)).val =
      System.Platform.numBits - k - 1 := by
    rw [UScalar.cast_val_eq, hlz, UScalarTy.Usize_numBits_eq]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
  unfold layout.RoundingAlignAndPhase.components
  step with pointer_width_spec as ⟨w, hw⟩
  have hone : (1#usize).val = 1 := by simp
  have hwpos : (1#usize).val ≤ w.val := by rw [hone, hw]; omega
  step with Usize.sub_spec hwpos as ⟨w1, hw1, _⟩
  simp only [core.num.nonzero.NonZero.get, bind_ok, lift]
  have hsub : (UScalar.cast .Usize (core.num.Usize.leading_zeros self._0.val)).val ≤ w1.val := by
    rw [hcast, hw1, hw]
    omega
  step with Usize.sub_spec hsub as ⟨shift, hshift, _⟩
  have hshift' : shift.val = k := by rw [hcast, hw1, hw] at hshift; omega
  step with Usize.ShiftLeft_spec 1#usize shift (by rw [hshift']; exact hk) as ⟨a, ha, _⟩
  have ha' : a.val = 2 ^ k := by
    rw [hshift'] at ha
    simp only [Nat.shiftLeft_eq, Nat.one_mul] at ha
    have hp : 2 ^ k < Usize.size := by
      rw [Usize.size, Usize.numBits, UScalarTy.Usize_numBits_eq]
      omega
    simpa only [Nat.mod_eq_of_lt hp] using ha
  have haz : a ≠ 0#usize := by
    intro hz
    have hz' := congrArg UScalar.val hz
    rw [ha'] at hz'
    change 2 ^ k = 0 at hz'
    have := Nat.two_pow_pos k
    omega
  simp only [core.num.nonzero.NonZero.new, cast_eq, haz, ↓reduceDIte,
    ↓reduceIte, bind_ok, WP.spec_ok]
  have hp : self._0.val.val - 2 ^ k < 2 ^ k := by
    rw [Nat.pow_succ] at hbound
    omega
  have hx : (self._0.val ^^^ a).val = self._0.val.val - 2 ^ k := by
    rw [UScalar.val_xor, ha']
    have heq : self._0.val.val = 2 ^ k + (self._0.val.val - 2 ^ k) := by omega
    rw [heq]
    simpa only [Nat.add_sub_cancel_left] using highest_bit_xor k _ hp
  refine ⟨?_, ?_, ?_, ha', ?_⟩
  · exact ⟨k, ha'⟩
  · rw [hx, ha']
    exact hp
  · rw [hx, ha']
    omega
  · exact hx

/- Reuse the components theorem for the getter that discards phase.
-/
theorem encoding_align_spec :
  ∀ (self : layout.RoundingAlignAndPhase), ∀ (hn : (0 < self._0.val.val : Prop)),
    @Zerocopy.layout.RoundingAlignAndPhase.align self ⦃ align => align.val.val = 2 ^ Nat.log2 self._0.val.val ⦄ := by
  intro self hn
  unfold layout.RoundingAlignAndPhase.align
  step with encoding_components_spec self hn as ⟨a, p, _, _, _, ha, _⟩
  simpa only [WP.spec_ok] using ha

theorem assume_shallow_unpadded_spec :
  ∀ (self : layout.DstLayout),
    @Zerocopy.layout.DstLayout.assume_shallow_unpadded self ⦃ r => r.align = self.align ∧ r.size_info = self.size_info ∧ r.statically_shallow_unpadded = true ⦄ := by
  intro self
  simp only [layout.DstLayout.assume_shallow_unpadded, WP.spec_ok, and_self]

/- Construct a fixed layout from explicit modeled size and alignment reads.
Those reads are data premises supplied by the external ABI bridge, not axioms
asserting that an arbitrary modeled size is the layout of a Rust type.
-/
theorem for_type_spec :
  ∀ (T : Type) (size align : Usize), ∀ (hs : (core.mem.size_of T = .ok size : Prop)), ∀ (ha : (core.mem.align_of T = .ok align : Prop)), ∀ (hn : (0 < align.val : Prop)),
    @Zerocopy.layout.DstLayout.for_type T ⦃ r => r.align.val = align ∧ r.size_info = layout.SizeInfo.Sized size ∧ r.statically_shallow_unpadded = false ⦄ := by
  intro T size align hs ha hn
  have haz : align ≠ 0#usize := by
    intro h
    have hv := congrArg UScalar.val h
    change align.val = 0 at hv
    omega
  unfold layout.DstLayout.for_type
  rw [ha]
  simp only [bind_ok, core.num.nonzero.NonZero.new, cast_eq, haz,
    ↓reduceDIte, ↓reduceIte, hs, WP.spec_ok, and_self]

/- Construct the same fixed layout with its asserted unpadded flag. The caller's
separate padding justification is outside this numerical contract.
-/
theorem for_unpadded_type_spec :
  ∀ (T : Type) (size align : Usize), ∀ (hs : (core.mem.size_of T = .ok size : Prop)), ∀ (ha : (core.mem.align_of T = .ok align : Prop)), ∀ (hn : (0 < align.val : Prop)),
    @Zerocopy.layout.DstLayout.for_unpadded_type T ⦃ r => r.align.val = align ∧ r.size_info = layout.SizeInfo.Sized size ∧ r.statically_shallow_unpadded = true ⦄ := by
  intro T size align hs ha hn
  unfold layout.DstLayout.for_unpadded_type
  step with for_type_spec T size align hs ha hn as ⟨dl, halign, hsize, _⟩
  step with assume_shallow_unpadded_spec dl as ⟨r, hr, hsi, hp⟩
  exact ⟨hr ▸ halign, hsi ▸ hsize, hp⟩

/- Construct a trailing layout with element size as stride and the modeled ABI
alignment as its rounding alignment. The primitive read premises stay
explicit.
-/
theorem for_slice_spec :
  ∀ (T : Type) (size align : Usize), ∀ (hs : (core.mem.size_of T = .ok size : Prop)), ∀ (ha : (core.mem.align_of T = .ok align : Prop)), ∀ (hp : (align.val.isPowerOfTwo : Prop)),
    @Zerocopy.layout.DstLayout.for_slice T ⦃ r => r.align.val = align ∧ r.statically_shallow_unpadded = true ∧
    ∃ tail, r.size_info = layout.SizeInfo.SliceDst tail ∧
      tail.offset = 0#usize ∧ tail.elem_size = size ∧ tail.size_base = 0#usize ∧
      tail.size_rounding_align_and_phase._0.val.val = align.val ⦄ := by
  intro T size align hs ha hp
  have hpos := Nat.pos_of_isPowerOfTwo hp
  have haz : align ≠ 0#usize := by
    intro h
    have hv := congrArg UScalar.val h
    change align.val = 0 at hv
    omega
  unfold layout.DstLayout.for_slice
  rw [ha]
  simp only [bind_ok, core.num.nonzero.NonZero.new, cast_eq, haz,
    ↓reduceDIte, ↓reduceIte, hs]
  step with encoding_new_spec ⟨align⟩ 0#usize hp (by simpa using hpos) as ⟨encoded, he⟩
  refine ⟨_, rfl, rfl, rfl, rfl, ?_⟩
  simpa using he

theorem max_elems_for_bytes_spec :
  ∀ (bytes : Usize) (elem_size : NonZeroUsize), ∀ (hn : (0 < elem_size.val.val : Prop)),
    @Zerocopy.layout.max_elems_for_bytes bytes elem_size ⦃ (elems, used) =>
    elems.val = bytes.val / elem_size.val.val ∧ used.val = elems.val * elem_size.val.val ∧
    used ≤ bytes ∧ bytes.val < (elems.val + 1) * elem_size.val.val ∧
    (∀ n : Nat, n * elem_size.val.val ≤ bytes.val ↔ n ≤ elems.val) ⦄ := by
  intro bytes elem hn
  unfold layout.max_elems_for_bytes
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step with Usize.div_spec bytes (y := elem.val) (by omega) as ⟨elems, he⟩
  have hfit : elems.val * elem.val.val ≤ bytes.val := by
    rw [he, Nat.mul_comm]
    exact Nat.mul_div_le _ _
  have hav : bytes.val ≤ Usize.max := by scalar_tac
  step as ⟨product, hmul⟩
  cases product with
  | none =>
    simp only [] at hmul
    omega
  | some used =>
    simp only [] at hmul
    simp only [WP.spec_ok]
    refine ⟨he, hmul.2.1, (UScalar.le_equiv _ _).mpr (by omega), ?_, ?_⟩
    · rw [he, Nat.mul_comm]
      exact Nat.lt_mul_div_succ _ hn
    · intro n
      rw [he]
      exact (Nat.le_div_iff_mul_le hn).symm

theorem requires_static_padding_spec :
  ∀ (self : layout.DstLayout),
    @Zerocopy.layout.DstLayout.requires_static_padding self ⦃ r => r = !self.statically_shallow_unpadded ⦄ := by
  intro self
  simp only [layout.DstLayout.requires_static_padding, WP.spec_ok]
  cases self.statically_shallow_unpadded <;> rfl

/- Explain both zero-stride rejection and successful conversion. The raw lemma
retains broad representation coverage; the canonical spec adds recursive
admission rather than silently changing that useful raw theorem.
-/
theorem try_nonzero_spec :
  ∀ (self : layout.SizeInfo Usize),
    @Zerocopy.layout.SizeInfoUsize.try_to_nonzero_elem_size self ⦃ r => match self with
    | .Sized size => r = some (.Sized size)
    | .SliceDst tail =>
      if tail.elem_size = 0#usize then r = none else
        ∃ t, r = some (.SliceDst t) ∧ t.offset = tail.offset ∧
          t.size_base = tail.size_base ∧
          t.size_rounding_align_and_phase = tail.size_rounding_align_and_phase ∧
          t.elem_size.val = tail.elem_size ⦄ := by
  intro self
  cases self with
  | Sized size => simp [layout.SizeInfoUsize.try_to_nonzero_elem_size]
  | SliceDst tail =>
    unfold layout.SizeInfoUsize.try_to_nonzero_elem_size core.num.nonzero.NonZero.new
    by_cases hz : tail.elem_size = 0#usize
    · simp only [cast_eq, hz, ↓reduceDIte, ↓reduceIte, bind_ok, WP.spec_ok]
    · simp only [cast_eq, hz, ↓reduceDIte, ↓reduceIte, bind_ok, WP.spec_ok]
      exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem min_align_eq : layout.DstLayout.MIN_ALIGN = .ok ⟨1#usize⟩ := by
  simp [layout.DstLayout.MIN_ALIGN, core.num.nonzero.NonZero.new]

theorem new_zst_spec :
  ∀ (repr_align : Option NonZeroUsize), ∀ (hp : (∀ a ∈ repr_align, a.val.val.isPowerOfTwo : Prop)),
    @Zerocopy.layout.DstLayout.new_zst repr_align ⦃ r => r.align = repr_align.getD ⟨1#usize⟩ ∧
    r.size_info = .Sized 0#usize ∧ r.statically_shallow_unpadded = true ⦄ := by
  intro repr_align hp
  unfold layout.DstLayout.new_zst
  have ha : (repr_align.getD ⟨1#usize⟩).val.val.isPowerOfTwo := by
    cases repr_align with
    | none => exact ⟨0, by simp⟩
    | some a => exact hp a rfl
  cases repr_align
  all_goals
    simp only [min_align_eq, Option.getD_none, Option.getD_some,
      core.num.nonzero.NonZero.get, bind_ok] at ha ⊢
    step as ⟨b, hb⟩
    have hbt : b = true := by
      have hb' : (b = true) = True := by simpa only [ha, Nat.isPowerOfTwo_one] using hb
      exact Eq.mpr hb' trivial
    simp [massert, hbt, bind_ok, WP.spec_ok]

end Zerocopy.Proofs.Raw

namespace Zerocopy.Proofs
open AeneasSpecs

-- Unfold only representation domains. The model calls and authored outcome
-- predicates remain the independently verified raw contracts below.
macro "representation_simps" : tactic =>
  `(tactic|
    (simp only [WP.spec_equiv_exists]
     simp (config := { index := false }) only [contract_simps]
     simp only [← WP.spec_equiv_exists]))

/- Connect the constructor's power-of-two and phase checks to exact encoding.
The canonical form also proves decoding of the actual returned word.
-/
theorem encoding_new_spec : Zerocopy.Specs.encoding_new_spec := by
  intro align phase av ha pv hp hpow hphase
  have hav := (decodeNonZeroUScalar_iff align av).mp ha
  have hpv := (decodeUScalar_iff phase pv).mp hp
  apply WP.spec_mono (Raw.encoding_new_spec align phase
    (by simpa only [hav] using hpow) (by simpa only [hav, hpv] using hphase))
  intro encoded he
  have hfit : av.value + pv.value ≤ Usize.max := by
    rw [← hav, ← hpv, ← he]
    scalar_tac
  let value : layout.RoundingAlignAndPhase.RoundingValue :=
    ⟨av.value, pv.value, hpow, hphase, hfit⟩
  refine ⟨value, (rounding_decode_iff encoded value).mpr ?_, rfl, rfl⟩
  simpa only [roundingRepresents, value, hav, hpv] using he
register_spec_step encoding_new_spec

/- Prove the implementation's bit scan recovers the alignment and phase of every
positive stored word, not only words built by the constructor.
-/
theorem encoding_components_spec : Zerocopy.Specs.encoding_components_spec := by
  intro self value decoded
  have hn := (encoding_valid_iff self).mp ⟨value, decoded⟩
  have hvalue := rounding_decode_components self value decoded
  apply WP.spec_mono (Raw.encoding_components_spec self hn)
  rintro ⟨align, phase⟩ facts
  let av : NonZeroUsizeValue :=
    ⟨unsignedWord align.val, Nat.pos_of_isPowerOfTwo facts.1⟩
  have ha : modelNonZeroUsize.decode align = some av :=
    (decodeNonZeroUScalar_iff align av).mpr rfl
  refine ⟨(av, unsignedWord phase), ?_, ?_⟩
  · simp only [RustModel.decode,
      dif_pos (Nat.pos_of_isPowerOfTwo facts.1)]
    rfl
  · exact ⟨facts.2.2.2.1.trans hvalue.1.symm,
      facts.2.2.2.2.trans hvalue.2.symm⟩
register_spec_step encoding_components_spec

/- Reuse the components theorem for the getter that discards phase.
-/
theorem encoding_align_spec : Zerocopy.Specs.encoding_align_spec := by
  intro self value decoded
  have hn := (encoding_valid_iff self).mp ⟨value, decoded⟩
  have hvalue := rounding_decode_components self value decoded
  apply WP.spec_mono (Raw.encoding_align_spec self hn)
  intro align he
  have hp : 0 < align.val.val := by rw [he]; exact Nat.two_pow_pos _
  let av : NonZeroUsizeValue := ⟨unsignedWord align.val, hp⟩
  exact ⟨av, (decodeNonZeroUScalar_iff align av).mpr rfl, he.trans hvalue.1.symm⟩
register_spec_step encoding_align_spec

theorem max_elems_for_bytes_spec : Zerocopy.Specs.max_elems_for_bytes_spec := by
  unfold Zerocopy.Specs.max_elems_for_bytes_spec
  representation_simps
  intro bytes elem hn
  apply WP.spec_mono (Raw.max_elems_for_bytes_spec bytes elem hn)
  intro result facts
  refine ⟨?_, facts⟩
  change isValid result
  simp
register_spec_step max_elems_for_bytes_spec

theorem assume_shallow_unpadded_spec : Zerocopy.Specs.assume_shallow_unpadded_spec := by
  unfold Zerocopy.Specs.assume_shallow_unpadded_spec
  representation_simps
  intro self hv
  apply WP.spec_mono (Raw.assume_shallow_unpadded_spec self)
  intro r facts
  refine ⟨?_, facts⟩
  simpa only [facts.1, facts.2.1] using hv
register_spec_step assume_shallow_unpadded_spec

/- Construct a fixed layout from explicit modeled size and alignment reads.
Those reads are data premises supplied by the external ABI bridge, not axioms
asserting that an arbitrary modeled size is the layout of a Rust type.
-/
theorem for_type_spec : Zerocopy.Specs.for_type_spec := by
  unfold Zerocopy.Specs.for_type_spec
  representation_simps
  intro T validity size align hs ha hn
  apply WP.spec_mono (Raw.for_type_spec T size align hs ha hn)
  intro r facts
  refine ⟨?_, facts⟩
  simp only [facts.1, facts.2.1, hn, and_self]
register_spec_step for_type_spec

/- Construct the same fixed layout with its asserted unpadded flag. The caller's
separate padding justification is outside this numerical contract.
-/
theorem for_unpadded_type_spec : Zerocopy.Specs.for_unpadded_type_spec := by
  unfold Zerocopy.Specs.for_unpadded_type_spec
  representation_simps
  intro T validity size align hs ha hn
  apply WP.spec_mono (Raw.for_unpadded_type_spec T size align hs ha hn)
  intro r facts
  refine ⟨?_, facts⟩
  simp only [facts.1, facts.2.1, hn, and_self]
register_spec_step for_unpadded_type_spec

/- Construct a trailing layout with element size as stride and the modeled ABI
alignment as its rounding alignment. The primitive read premises stay
explicit.
-/
theorem for_slice_spec : Zerocopy.Specs.for_slice_spec := by
  unfold Zerocopy.Specs.for_slice_spec
  representation_simps
  intro T validity size align hs ha hp
  apply WP.spec_mono (Raw.for_slice_spec T size align hs ha hp)
  intro r facts
  refine ⟨?_, facts⟩
  rcases facts with ⟨halign, _, tail, hsi, _, _, _, hcode⟩
  simp only [halign, hsi]
  have := Nat.pos_of_isPowerOfTwo hp
  simpa only [hcode, and_self] using this
register_spec_step for_slice_spec

theorem requires_static_padding_spec : Zerocopy.Specs.requires_static_padding_spec := by
  unfold Zerocopy.Specs.requires_static_padding_spec
  representation_simps
  intro self _
  exact Raw.requires_static_padding_spec self
register_spec_step requires_static_padding_spec

end Zerocopy.Proofs

namespace Zerocopy.Proofs
open AeneasSpecs

/- Explain both zero-stride rejection and successful conversion. The raw lemma
retains broad representation coverage; the canonical spec adds recursive
admission rather than silently changing that useful raw theorem.
-/
theorem try_nonzero_spec : Zerocopy.Specs.try_nonzero_spec := by
  unfold Zerocopy.Specs.try_nonzero_spec
  representation_simps
  intro self value decoded
  have hv := (size_info_valid_iff self).mp ⟨value, decoded⟩
  apply WP.spec_mono (Raw.try_nonzero_spec self)
  intro r facts
  constructor
  swap
  · cases self <;> simpa using facts
  change isValid r
  rw [option_valid_iff]
  cases self with
  | Sized size =>
    simp only [] at facts
    rw [facts]
    simp [sizeInfoValid]
  | SliceDst tail =>
    simp only [sizeInfoValid, trailingValid, scalar_valid_iff, true_and] at hv
    simp only [] at facts
    by_cases hz : tail.elem_size = 0#usize
    · simp only [hz, if_true] at facts
      rw [facts]
      simp
    · simp only [hz, if_false] at facts
      rcases facts with ⟨next, hr, _, _, hcode, helem⟩
      rw [hr]
      simp only [Option.mem_some_iff, forall_eq']
      rw [size_info_valid_iff]
      change trailingValid next
      simp only [trailingValid, nonzero_valid_iff, encodingValid, hcode]
      have hnz : tail.elem_size.val ≠ 0 := by
        intro h
        apply hz
        exact UScalar.eq_of_val_eq (by simpa using h)
      exact ⟨by simpa only [helem] using Nat.pos_of_ne_zero hnz, hv⟩
register_spec_step try_nonzero_spec

theorem new_zst_spec : Zerocopy.Specs.new_zst_spec := by
  unfold Zerocopy.Specs.new_zst_spec
  representation_simps
  intro repr_align hv hp
  apply WP.spec_mono (Raw.new_zst_spec repr_align hp)
  intro r facts
  refine ⟨?_, facts⟩
  simp only [facts.1, facts.2.1]
  cases repr_align with
  | none => simp
  | some a => simpa only [Option.getD_some, and_true] using Nat.pos_of_isPowerOfTwo (hp a rfl)
register_spec_step new_zst_spec

end Zerocopy.Proofs
