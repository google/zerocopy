-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted
import Trusted.Correspondence
import Anneal.MirWp
import Anneal.MirCorrespondence.Codec
import Anneal.MirCorrespondence.EnumEquiv
import Anneal.MirCorrespondence.MemAlloc

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Miri.ABI Miri.Memory Miri.Interpreter

/-! ## Section 6: `Trusted.MirSemantics` Byte Codec Against `Allocation` -/

/-- `writeScalar` on a fresh allocation stores the big-endian bytes of the
scalar's data and reads the same scalar back. -/
theorem tryNew_writeScalar_getBytes (w : IntWidth) (bits : BitVec 128)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (toMiriSize w) Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc) :
    let alloc := rawAlloc.withExtra
      (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize w))
    ∃ after,
      Allocation.writeScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w))
          (.fromScalarInt (miriScalar w bits)) alloc = .ok () after ∧
      after.getBytesUnchecked (allocRange Size.ZERO (toMiriSize w)) =
        .ok (beBytes (miriScalar w bits).data.toNat (toMiriSize w).bytes.toNat
          (toMiriSize w).bytes.toNat) ∧
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false =
        .ok (.fromScalarInt (miriScalar w bits)) := by
  intro alloc
  have h_t : targetUIntBytesMirror RuntimeTargetDataLayout.default.base
      (toMiriSize w) (miriScalar w bits).data =
      .ok (beBytes (miriScalar w bits).data.toNat (toMiriSize w).bytes.toNat
        (toMiriSize w).bytes.toNat) := by
    cases w <;> exact targetUIntBytesMirror_be _ (by decide) _
  let ⟨after, h_w, _, h_gb, _, _, _, _, _⟩ :=
    writeScalar_readScalar_step w bits
      (beBytes (miriScalar w bits).data.toNat (toMiriSize w).bytes.toNat
        (toMiriSize w).bytes.toNat)
      (beBytes_size _ _ _) h_t h_raw
  let ⟨after', h_w', h_rd', _, _, _, _, _⟩ :=
    tryNew_writeScalar_readScalar w bits h_raw
  have h_eq : after' = after := by
    rw [h_w] at h_w'
    injection h_w' with _ h_a
    exact h_a.symm
  rw [h_eq] at h_rd'
  refine ⟨after, h_w, ?_, h_rd'⟩
  rw [h_gb, array_empty_append_extract _ _ (beBytes_size _ _ _)]

/-- Length of `leBytesOfNat`. -/
theorem leBytesOfNat_length : ∀ (n x : Nat), (leBytesOfNat n x).length = n
  | 0, _ => rfl
  | n + 1, x => by
    change (leBytesOfNat n (Nat.div x 256)).length + 1 = n + 1
    rw [leBytesOfNat_length n]

/-- Byte `j` of `leBytesOfNat n x` is byte `j` of `x`. -/
theorem leBytesOfNat_getElem? : ∀ (n x j : Nat), j < n →
    (leBytesOfNat n x)[j]? =
      some (UInt8.ofNat (HMod.hMod (HDiv.hDiv x (HPow.hPow 256 j)) 256))
  | 0, _, _, h => False.elim (Nat.not_lt_zero _ h)
  | n + 1, x, 0, _ => by
    change some (UInt8.ofNat (HMod.hMod x 256)) =
      some (UInt8.ofNat (HMod.hMod (HDiv.hDiv x (HPow.hPow 256 0)) 256))
    rw [Nat.pow_zero, Nat.div_one]
  | n + 1, x, j + 1, h => by
    change (leBytesOfNat n (HDiv.hDiv x 256))[j]? = _
    rw [leBytesOfNat_getElem? n (HDiv.hDiv x 256) j (Nat.lt_of_succ_lt_succ h),
      Nat.div_div_eq_div_mul, Nat.pow_succ']

private theorem pow256_pos (k : Nat) : 0 < HPow.hPow (256 : Nat) k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    exact Nat.mul_pos ih (by decide)

/-- `leBytesOfNat n x` read back as a little-endian integer is `x` modulo
`256 ^ n`. -/
theorem natOfLeBytes_leBytesOfNat : ∀ (n x : Nat),
    natOfLeBytes (leBytesOfNat n x) = HMod.hMod x (HPow.hPow 256 n)
  | 0, x => by
    change 0 = HMod.hMod x (HPow.hPow 256 0)
    rw [Nat.pow_zero, Nat.mod_one]
  | n + 1, x => by
    change (UInt8.ofNat (HMod.hMod x 256)).toNat +
        256 * natOfLeBytes (leBytesOfNat n (HDiv.hDiv x 256)) =
      HMod.hMod x (HPow.hPow 256 (n + 1))
    rw [natOfLeBytes_leBytesOfNat n, u8_ofNat_toNat_mod, Nat.pow_succ',
      Nat.mul_comm 256]
    exact nat_mod_mul_decomp x 256 (HPow.hPow 256 n) (by decide)
      (pow256_pos n)

/-- The reversed little-endian bytes are `lean-miri`'s big-endian bytes. -/
theorem reverse_leBytesOfNat_eq_beBytes (n x : Nat) :
    Array.mk (leBytesOfNat n x).reverse = beBytes x n n := by
  have h_list : (leBytesOfNat n x).reverse = (beBytes x n n).toList := by
    apply List.ext_getElem?
    intro i
    rw [Array.getElem?_toList (xs := beBytes x n n)]
    cases Nat.lt_or_ge i n with
    | inl h_lt =>
      have h_len : i < (leBytesOfNat n x).length := by
        rw [leBytesOfNat_length]; exact h_lt
      rw [List.getElem?_reverse h_len, leBytesOfNat_length,
        beBytes_getElem? x n n i h_lt]
      have h_idx : n - 1 - i < n :=
        Nat.lt_of_le_of_lt (Nat.sub_le (n - 1) i)
          (Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le i) h_lt) (by decide))
      rw [leBytesOfNat_getElem? n x (n - 1 - i) h_idx, Nat.sub_right_comm,
        Nat.pow_mul]
    | inr h_ge =>
      have h_l : (leBytesOfNat n x).reverse.length ≤ i := by
        rw [List.length_reverse, leBytesOfNat_length]; exact h_ge
      have h_a : (beBytes x n n).size ≤ i := by
        rw [beBytes_size]; exact h_ge
      rw [List.getElem?_eq_none h_l, Array.getElem?_eq_none h_a]
  rw [h_list]

/-- `initBytes?` recovers the raw bytes of initialized, provenance-free
bytes. -/
theorem initBytes?_map_init : ∀ (raw : List UInt8),
    initBytes? (raw.map (fun b => AllocByte.init b none)) = some raw
  | [] => rfl
  | b :: rest => by
    change (match initBytes? (rest.map (fun b => AllocByte.init b none)) with
      | some bs => some (b :: bs)
      | none => none) = some (b :: rest)
    rw [initBytes?_map_init rest]

/-- `Trusted.MirSemantics.decodeVal` inverts `encodeVal` on well-formed
integers at `profileTargetEndian`. -/
theorem decodeVal_int_encode (w : IntWidth) (s : Bool) (bits : BitVec 128) :
    decodeVal profileTargetEndian (.int w s)
        ((leBytesOfNat w.byteSize (truncateBits w bits).toNat).reverse.map
          (fun b => AllocByte.init b none)) =
      .ok (some (.scalar ⟨w, s, truncateBits w bits⟩)) := by
  have h_len :
      ((leBytesOfNat w.byteSize (truncateBits w bits).toNat).reverse.map
        (fun b => AllocByte.init b none)).length = w.byteSize := by
    rw [List.length_map, List.length_reverse, leBytesOfNat_length]
  have h_sz : (intLayout w).size = w.byteSize := by cases w <;> rfl
  have h_nz : Nat.beq w.byteSize 0 = false := by cases w <;> rfl
  have h_pow : Nat.pow 2 w.bitWidth = HPow.hPow 256 w.byteSize := by
    cases w <;> rfl
  have h_x_lt : (truncateBits w bits).toNat < HPow.hPow 256 w.byteSize := by
    rw [toNat_truncateBits, ← h_pow]
    exact Nat.mod_lt _ (intWidth_modulus_pos w)
  have h_dec :
      decodeUInt profileTargetEndian
          (leBytesOfNat w.byteSize (truncateBits w bits).toNat).reverse =
        (truncateBits w bits).toNat := by
    change natOfLeBytes
        (leBytesOfNat w.byteSize (truncateBits w bits).toNat).reverse.reverse =
      (truncateBits w bits).toNat
    rw [List.reverse_reverse, natOfLeBytes_leBytesOfNat]
    exact Nat.mod_eq_of_lt h_x_lt
  change (match layoutOfTy (.int w s) with
    | none => Except.error FaultKind.unsupported
    | some layout =>
      if (!Nat.beq ((leBytesOfNat w.byteSize
          (truncateBits w bits).toNat).reverse.map
          (fun b => AllocByte.init b none)).length layout.size) = true then
        Except.error FaultKind.unsupported
      else if Nat.beq layout.size 0 = true then
        match evalConstLit (.int w s) .zeroSized with
        | .ok v => .ok (some v)
        | .error k => .error k
      else
        match initBytes? ((leBytesOfNat w.byteSize
            (truncateBits w bits).toNat).reverse.map
            (fun b => AllocByte.init b none)) with
        | none => .ok none
        | some raw =>
          match evalConstLit (.int w s)
              (.scalar (BitVec.ofNat 128
                (decodeUInt profileTargetEndian raw))) with
          | .ok v => .ok (some v)
          | .error k => .error k) = _
  have h_lay : layoutOfTy (.int w s) = some (intLayout w) := rfl
  rw [h_lay]
  dsimp only
  rw [h_len, h_sz, Nat.beq_refl, h_nz]
  rw [initBytes?_map_init]
  dsimp only
  rw [h_dec, bitVec128_ofNat_toNat]
  dsimp only [evalConstLit]
  rw [truncateBits_idem, bne_self_eq_false]
  rfl

/-- `Trusted.MirSemantics.encodeVal` stores a well-formed integer as its
big-endian bytes, all initialized and without provenance. -/
theorem encodeVal_int_trunc (w : IntWidth) (s : Bool) (bits : BitVec 128) :
    encodeVal profileTargetEndian (.int w s)
        (.scalar ⟨w, s, truncateBits w bits⟩) =
      .ok ((leBytesOfNat w.byteSize (truncateBits w bits).toNat).reverse.map
        (fun b => AllocByte.init b none)) := by
  have h_wf : (ScalarVal.mk w s (truncateBits w bits)).wf = true := by
    dsimp only [ScalarVal.wf]; rw [truncateBits_idem]
    exact beq_self_eq_true _
  have h_ck : checkVal (.scalar ⟨w, s, truncateBits w bits⟩) (.int w s) =
      true := by
    dsimp only [checkVal, Val.ty?]
    rw [h_wf, mem_ite_true_eq]
    dsimp only [MirTy.beq]
    rw [IntWidth.beq_refl, beq_self_eq_true]
    rfl
  dsimp only [encodeVal]
  rw [h_ck]
  rfl

/-- `Trusted.MirSemantics`'s byte codec agrees with `lean-miri`'s
`Allocation` scalar accesses on every integer width (see
`BytesCodecMatchesMiriClaim`). -/
theorem bytes_codec_matches_miri_base : BytesCodecMatchesMiriClaim := by
  intro w s bits
  refine ⟨?_, ?_⟩
  · let ⟨rawAlloc, h_raw, _⟩ :=
      Allocation.tryNew_replicate_full (P := Miri.Memory.Provenance)
        (toMiriSize w) Align.ONE 1 (by decide) (by decide)
    exact ⟨rawAlloc, h_raw⟩
  intro rawAlloc h_raw
  refine ⟨?_, ?_⟩
  · let ⟨after, h_w, h_gb, h_rd⟩ := tryNew_writeScalar_getBytes w bits h_raw
    have h_n : (toMiriSize w).bytes.toNat = w.byteSize := by cases w <;> rfl
    refine ⟨(leBytesOfNat w.byteSize (truncateBits w bits).toNat).reverse,
      after, encodeVal_int_trunc w s bits, h_w, ?_, h_rd,
      decodeVal_int_encode w s bits⟩
    rw [h_gb, h_n, miriScalar_data, reverse_leBytesOfNat_eq_beBytes]
  · let ⟨after, info, h_wu, h_rd, _, _, _, _⟩ :=
      tryNew_writeUninit_readUninit w h_raw
    refine ⟨after, info, h_wu, h_rd, ?_⟩
    cases w <;> rfl

end Anneal.MirCorrespondence
