/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import Proofs.SafetyChecks
public import Proofs.Byteorder
@[expose] public section

/-!
These functions are the size selection and byte-copy implementation called by
IntoBytes's three public write methods. The proofs include unsuccessful writes
and the unaffected destination region, rather than merely checking copied bytes.
The source-bound copy interpretations retain the reference premises documented
in ADMISSION_DESIGN.md; their pointer implementations are not extracted.
-/
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

private theorem decode_write (out : Bool × Slice U8) :
    (inferInstance : RustModel (Bool × Slice U8)).decode out =
      some (out.1, byteSlice out.2) := by
  have decoded := decode_byte_slice out.2
  simp only [RustModel.decode] at decoded ⊢
  rw [decoded]

theorem write_exact_raw (src dst : Slice U8) :
    util.bytewrite.exact src dst ⦃ out =>
      out.1 = decide (src.val.length = dst.val.length) ∧
      out.2.val = if src.val.length = dst.val.length then src.val else dst.val ⦄ := by
  by_cases same : src.val.length = dst.val.length
  · simp [util.bytewrite.exact, Slice.len,
      util.copy_unchecked, same, bind_ok]
  · simp [util.bytewrite.exact, Slice.len, same, Ne.symm same]

theorem write_prefix_raw (src dst : Slice U8) :
    util.bytewrite.prefix src dst ⦃ out =>
      out.1 = decide (src.val.length ≤ dst.val.length) ∧
      out.2.val = if src.val.length ≤ dst.val.length
        then src.val ++ dst.val.drop src.val.length else dst.val ⦄ := by
  by_cases fits : src.val.length ≤ dst.val.length
  · simp [util.bytewrite.prefix, Slice.len, UScalar.le_equiv,
      util.copy_unchecked, fits, bind_ok]
  · simp [util.bytewrite.prefix, Slice.len, UScalar.le_equiv, fits]

theorem write_suffix_raw (src dst : Slice U8) :
    util.bytewrite.suffix src dst ⦃ out =>
      out.1 = decide (src.val.length ≤ dst.val.length) ∧
      out.2.val = if src.val.length ≤ dst.val.length
        then dst.val.take (dst.val.length - src.val.length) ++ src.val else dst.val ⦄ := by
  unfold util.bytewrite.suffix
  step as ⟨start, facts⟩
  cases start with
  | none =>
    have unfit : ¬ src.val.length ≤ dst.val.length := by simpa [Slice.len] using facts
    simp [unfit]
  | some start =>
    have bounds : start.val = dst.val.length - src.val.length ∧
        src.val.length ≤ dst.val.length := by
      simp only [Slice.len] at facts
      exact ⟨facts.2.1, facts.1⟩
    have offset : start.val ≤ dst.val.length := by omega
    have fits : src.val.length ≤ dst.val.length - start.val := by omega
    have finish : start.val + src.val.length = dst.val.length := by omega
    simp only [util.copy_unchecked_at, if_pos offset, dif_pos fits, bind_ok, WP.spec_ok]
    simp [bounds.1, bounds.2]

-- The concrete consumer uses the public byteorder operations, then the same
-- prefix writer as IntoBytes. Reuse the proved encoder rather than recalculate
-- its bitvector arithmetic inside this caller proof.
theorem write_be_word_prefix_raw (n : U16) (dst : Slice U8) :
    util.bytewrite.be_word_prefix n dst ⦃ out =>
      out.1 = decide (2 ≤ dst.val.length) ∧
      out.2.val.map U8.bv = if 2 ≤ dst.val.length
        then Rust.Bytes.encodeBE 2 n.val ++ (dst.val.drop 2).map U8.bv
        else dst.val.map U8.bv ⦄ := by
  have encoding_eq : (do
      let value ← byteorder.U16.new byteorder.BigEndian.Insts.ZerocopyByteorderByteOrder n
      byteorder.U16.to_bytes value) = byteorder.verification.write_u16_be n := by
    simp only [byteorder.verification.write_u16_be, core.convert.IntoFrom.into,
      ArrayU82.Insts.CoreConvertFromU16.from,
      byteorder.U16.to_bytes]
  unfold util.bytewrite.be_word_prefix
  rw [← Aeneas.Std.bind_assoc, encoding_eq]
  step with Raw.write_u16_be n as ⟨bytes, encoded⟩
  simp only [lift, bind_ok]
  apply WP.spec_mono (write_prefix_raw (Array.to_slice bytes) dst)
  intro out facts
  have length : bytes.val.length = 2 := by simp
  simp only [Array.to_slice, Slice.from_val, length] at facts
  refine ⟨facts.1, ?_⟩
  by_cases fits : 2 ≤ dst.val.length
  · simp only [if_pos fits] at facts ⊢
    rw [facts.2, List.map_append, encoded]
  · simp only [if_neg fits] at facts ⊢
    rw [facts.2]

theorem write_exact_spec : Specs.write_exact_spec := by
  intro src dst _ _ _ _
  apply WP.spec_mono (write_exact_raw src dst)
  intro out facts
  exact ⟨(out.1, byteSlice out.2), decode_write out, facts⟩

theorem write_prefix_spec : Specs.write_prefix_spec := by
  intro src dst _ _ _ _
  apply WP.spec_mono (write_prefix_raw src dst)
  intro out facts
  exact ⟨(out.1, byteSlice out.2), decode_write out, facts⟩

theorem write_suffix_spec : Specs.write_suffix_spec := by
  intro src dst _ _ _ _
  apply WP.spec_mono (write_suffix_raw src dst)
  intro out facts
  exact ⟨(out.1, byteSlice out.2), decode_write out, facts⟩

theorem write_be_word_prefix_spec : Specs.write_be_word_prefix_spec := by
  intro n dst _ _ _ _
  apply WP.spec_mono (write_be_word_prefix_raw n dst)
  intro out facts
  exact ⟨(out.1, byteSlice out.2), decode_write out, facts⟩

end Zerocopy.Proofs
