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
import Anneal.MirCorrespondence.SimHelpers
import Anneal.MirCorrespondence.ScalarEquiv
import Anneal.MirCorrespondence.EnumEquiv
import Anneal.MirCorrespondence.MemAlloc
import Anneal.MirCorrespondence.ValidateLocal
import Anneal.MirCorrespondence.RetPlace

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Miri.ABI Miri.Memory Miri.Interpreter

private theorem scalarInt_eq_of_data_size' (a b : Miri.Memory.ScalarInt)
    (hd : a.data = b.data) (hs : a.size = b.size) : a = b := by
  cases a
  cases b
  dsimp only [Miri.Memory.ScalarInt.data, Miri.Memory.ScalarInt.size] at hd hs
  subst hd; subst hs; rfl

theorem scalarInt_ofChar_eq_miriScalar (ch : Char) :
    ScalarInt.ofChar ch = miriScalar .i32 (BitVec.ofNat 128 ch.toNat) := by
  have h32 : ch.toNat < Nat.pow 2 32 := UInt32.toNat_lt ch.val
  have h128 : ch.toNat < HPow.hPow 2 128 :=
    Nat.lt_trans h32 (by decide : Nat.pow 2 32 < HPow.hPow 2 128)
  apply scalarInt_eq_of_data_size'
  · rw [miriScalar_data]
    change BitVec.ofNat 128 (UInt32.ofNat ch.toNat).toNat = _
    rw [uint32_ofNat_char_toNat]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_truncateBits, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt h128]
    exact (Nat.mod_eq_of_lt h32).symm
  · rfl

private theorem array_extract_empty_same {α : Type} (a : Array α) (n : Nat) :
    a.extract n n = Array.mk [] := by
  apply Array.eq_empty_of_size_eq_zero
  rw [Array.size_extract]
  exact Nat.sub_eq_zero_of_le (Nat.min_le_left _ _)

private theorem array_extract_append_left {α : Type} (a b : Array α)
    (n : Nat) (h : a.size = n) : (a ++ b).extract 0 n = a := by
  rw [← h, Array.extract_append_left, Array.extract_eq_self_iff]
  exact Or.inr ⟨rfl, Nat.le_refl _⟩

private theorem array_extract_sandwich_prefix {α : Type} (a b c : Array α)
    (n : Nat) (h : a.size = n) : (a ++ b ++ c).extract 0 n = a := by
  rw [Array.append_assoc]
  exact array_extract_append_left a (b ++ c) n h

private theorem array_extract_sandwich {α : Type} (a b c : Array α)
    (m k : Nat) (ha : a.size = m) (hb : b.size = k) :
    (a ++ b ++ c).extract m (m + k) = b := by
  rw [Array.append_assoc, ← ha, Array.extract_append_right]
  exact array_extract_append_left b c k hb

private theorem checkedSliceMirror_ok (bs : Array UInt8) (sz : Size)
    (r : AllocRange) (fin : Size)
    (h_sz : bs.size = sz.bytes.toNat)
    (h_end : r.endExclusive = .ok fin)
    (h_oob : (r.start.bytes > fin.bytes || fin.bytes > sz.bytes) = false) :
    checkedSliceMirror bs sz r =
      .ok (bs.extract r.start.bytes.toNat fin.bytes.toNat) := by
  dsimp only [checkedSliceMirror]
  rw [h_sz, bne_self_eq_false, ite_false_eq_true]
  dsimp only [Except.mapError]
  rw [h_end]
  dsimp only [Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_oob, ite_false_eq_true]

private theorem clearProvenance_of_read_ok_range (r : AllocRange) (fin : Size)
    (h_end : r.endExclusive = .ok fin)
    {after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree}
    {sc : Scalar Miri.Memory.Provenance}
    (h_prov : after.provenanceMap = ProvenanceMap.new)
    (h_rd :
      after.readScalar RuntimeTargetDataLayout.default.base r false = .ok sc) :
    Allocation.clearProvenance r (Size.ofBytes 8) after = .ok () after := by
  have h_bs : ∃ bs, Allocation.getBytesUnchecked after r = .ok bs := by
    dsimp only [Allocation.readScalar] at h_rd
    cases h_im : (after.initializationMask.isRangeInitialized r).mapError
        AllocError.memory with
    | error _ =>
      dsimp only [Allocation.initializationMask] at h_im
      rw [h_im] at h_rd; cases h_rd
    | ok res =>
      dsimp only [Allocation.initializationMask] at h_im
      rw [h_im] at h_rd
      cases res with
      | error _ => cases h_rd
      | ok _ =>
        dsimp only [bind, Except.bind, pure, Pure.pure] at h_rd
        cases h_cs : Allocation.getBytesUnchecked after r with
        | ok bs => exact ⟨bs, rfl⟩
        | error e =>
          dsimp only [Allocation.getBytesUnchecked] at h_cs
          rw [h_cs] at h_rd
          cases h_rd
  let ⟨bs, h_cs⟩ := h_bs
  dsimp only [Allocation.clearProvenance]
  dsimp only [Allocation.getBytesUnchecked] at h_cs
  rw [h_cs]
  dsimp only [Id.run, pure, Pure.pure, bind, Bind.bind]
  dsimp only [Allocation.provenanceMap] at h_prov
  rw [h_prov,
    ProvenanceMap.clear_new r _ (Size.ofBytes 8) fin (by decide) h_end]
  dsimp only
  cases after
  dsimp only at h_prov
  rw [h_prov]

private def boolByte (b : Bool) : UInt8 := if b then 1 else 0

private theorem targetUIntBytesMirror_bool (b : Bool) :
    targetUIntBytesMirror RuntimeTargetDataLayout.default.base
      (Size.ofBytes 1) (ScalarInt.ofBool b).data =
      .ok (Array.mk [boolByte b]) := by
  cases b <;> exact targetUIntBytesMirror_be 1 (by decide) _

private theorem readTargetUInt_bool (b : Bool) :
    Bind.bind
      (readTargetUIntMirror RuntimeTargetDataLayout.default.base
        (Array.mk [boolByte b]))
      (fun x => (Scalar.fromUInt (Prov := Miri.Memory.Provenance)
        x (Size.ofBytes 1)).mapError AllocError.scalar) =
      .ok (.fromBool b) := by
  cases b
  · rw [show (Array.mk [boolByte false] : Array UInt8) = beBytes 0 1 1
      from rfl]
    rw [readTargetUIntMirror_be 1 (by decide) 0]
    rfl
  · rw [show (Array.mk [boolByte true] : Array UInt8) = beBytes 1 1 1
      from rfl]
    rw [readTargetUIntMirror_be 1 (by decide) 1]
    rfl

private theorem scalar_fromScalarInt_toBitsOrPtr (w : IntWidth)
    (bits : BitVec 128) :
    (Scalar.fromScalarInt (miriScalar w bits)
      (Prov := Miri.Memory.Provenance)).toBitsOrPtrInternal
      (toMiriSize w) = .ok (.bits (miriScalar w bits).data) := by
  cases w <;> rfl

private theorem scalar_fromBool_toBitsOrPtr (b : Bool) :
    (Scalar.fromBool b (Prov := Miri.Memory.Provenance)).toBitsOrPtrInternal
      (Size.ofBytes 1) = .ok (.bits (ScalarInt.ofBool b).data) := by
  cases b <;> rfl

private def PairAllocReads (w : IntWidth) (bits : BitVec 128) (b : Bool)
    (a : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    : Prop :=
  a.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (toMiriSize w)) false =
    .ok (.fromScalarInt (miriScalar w bits)) ∧
  a.readScalar RuntimeTargetDataLayout.default.base
      (allocRange (toMiriSize w) (Size.ofBytes 1)) false = .ok (.fromBool b) ∧
  Allocation.clearProvenance (allocRange Size.ZERO (toMiriSize w))
      (Size.ofBytes 8) a = .ok () a ∧
  Allocation.clearProvenance (allocRange (toMiriSize w) (Size.ofBytes 1))
      (Size.ofBytes 8) a = .ok () a ∧
  a.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes) ∧
  a.mutability = .Mut ∧ a.align = Align.ONE

private noncomputable def pairPadRange (w : IntWidth) : AllocRange :=
  allocRange (Size.ofBytes ((toMiriSize w).bytes + 1))
    (Size.ofBytes ((toMiriSize w).bytes - 1))

private theorem pair_size_pos (w : IntWidth) :
    (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes ≠ 0 := by
  cases w <;> decide

private theorem pair_size_two_nat (w : IntWidth) :
    (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes.toNat =
      2 * (toMiriSize w).bytes.toNat := by
  cases w <;> rfl

private theorem pair_r1_end (w : IntWidth) :
    (allocRange Size.ZERO (toMiriSize w)).endExclusive =
      .ok (toMiriSize w) := by
  cases w <;> rfl

private theorem pair_r2_end (w : IntWidth) :
    (allocRange (toMiriSize w) (Size.ofBytes 1)).endExclusive =
      .ok (Size.ofBytes ((toMiriSize w).bytes + 1)) := by
  cases w <;> rfl

private theorem pair_r3_end (w : IntWidth) :
    (pairPadRange w).endExclusive =
      .ok (Size.ofBytes (2 * (toMiriSize w).bytes)) := by
  cases w <;> rfl

private theorem pair_full_end (w : IntWidth) :
    (allocRange Size.ZERO
        (Size.ofBytes (2 * (toMiriSize w).bytes))).endExclusive =
      .ok (Size.ofBytes (2 * (toMiriSize w).bytes)) := by
  cases w <;> rfl

private theorem pair_r1_oob (w : IntWidth) :
    ((allocRange Size.ZERO (toMiriSize w)).start.bytes > (toMiriSize w).bytes ||
      (toMiriSize w).bytes > (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes) =
      false := by
  cases w <;> decide

private theorem pair_r2_oob (w : IntWidth) :
    ((allocRange (toMiriSize w) (Size.ofBytes 1)).start.bytes >
        (Size.ofBytes ((toMiriSize w).bytes + 1)).bytes ||
      (Size.ofBytes ((toMiriSize w).bytes + 1)).bytes >
        (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes) = false := by
  cases w <;> decide

private theorem pair_r3_oob (w : IntWidth) :
    ((pairPadRange w).start.bytes >
        (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes ||
      (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes >
        (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes) = false := by
  cases w <;> decide

private theorem pair_full_oob (w : IntWidth) :
    ((allocRange Size.ZERO
          (Size.ofBytes (2 * (toMiriSize w).bytes))).start.bytes >
        (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes ||
      (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes >
        (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes) = false := by
  cases w <;> decide

private theorem pair_r2_nat_add (w : IntWidth) :
    (toMiriSize w).bytes.toNat + 1 =
      (Size.ofBytes ((toMiriSize w).bytes + 1)).bytes.toNat := by
  cases w <;> rfl

private theorem tryNew_size_uninit_image (sz : Size)
    (h_ne : sz.bytes ≠ 0)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      sz Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc) :
    ∃ (init : Allocation Miri.Memory.Provenance Unit),
      Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        (Array.replicate sz.bytes.toNat 0) Align.ONE .Mut = .ok init ∧
      Allocation.writeUninit (allocRange Size.ZERO sz)
        (Size.ofBytes 8) init = .ok () rawAlloc := by
  let ⟨_, init, h_fb, h_wu⟩ :=
    Allocation.tryNew_uninit_image sz Align.ONE (Size.ofBytes 8)
      rawAlloc (by decide) h_raw
  rw [ite_eq_right h_ne] at h_wu
  exact ⟨init, h_fb, h_wu⟩

private theorem pair_write_read_abstract
    (w : IntWidth) (bits : BitVec 128) (b : Bool)
    (bytes0 data boolBytes : Array UInt8)
    (h_b0 : bytes0.size = (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes.toNat)
    (h_dlen : data.size = (toMiriSize w).bytes.toNat)
    (h_blen : boolBytes.size = 1)
    (h_t1 : targetUIntBytesMirror RuntimeTargetDataLayout.default.base
      (toMiriSize w) (miriScalar w bits).data = .ok data)
    (h_t2 : targetUIntBytesMirror RuntimeTargetDataLayout.default.base
      (Size.ofBytes 1) (ScalarInt.ofBool b).data = .ok boolBytes)
    {init rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (h_fb : Allocation.fromBytes (Prov := Miri.Memory.Provenance)
      bytes0 Align.ONE .Mut = .ok init)
    (h_wu : Allocation.writeUninit
      (allocRange Size.ZERO (Size.ofBytes (2 * (toMiriSize w).bytes)))
      (Size.ofBytes 8) init = .ok () rawAlloc) :
    let alloc := rawAlloc.withExtra (Miri.TreeBorrows.BorrowTree.new
      Miri.Memory.BorTag.one (Size.ofBytes (2 * (toMiriSize w).bytes)))
    ∃ middle after after2,
      Allocation.writeScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w))
          (.fromScalarInt (miriScalar w bits)) alloc = .ok () middle ∧
      middle.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes) ∧
      middle.mutability = .Mut ∧
      Allocation.writeScalar RuntimeTargetDataLayout.default.base
          (allocRange (toMiriSize w) (Size.ofBytes 1))
          (.fromBool b) middle = .ok () after ∧
      Allocation.writeUninit (pairPadRange w) (Size.ofBytes 8) after =
        .ok () after2 ∧
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false =
        Bind.bind
          (readTargetUIntMirror RuntimeTargetDataLayout.default.base data)
          (fun x =>
            (Scalar.fromUInt x (toMiriSize w)).mapError AllocError.scalar) ∧
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange (toMiriSize w) (Size.ofBytes 1)) false =
        Bind.bind
          (readTargetUIntMirror RuntimeTargetDataLayout.default.base boolBytes)
          (fun x =>
            (Scalar.fromUInt x (Size.ofBytes 1)).mapError AllocError.scalar) ∧
      after.provenanceMap = ProvenanceMap.new ∧
      after.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes) ∧
      after.mutability = .Mut ∧ after.align = Align.ONE ∧
      after2.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false =
        Bind.bind
          (readTargetUIntMirror RuntimeTargetDataLayout.default.base data)
          (fun x =>
            (Scalar.fromUInt x (toMiriSize w)).mapError AllocError.scalar) ∧
      after2.readScalar RuntimeTargetDataLayout.default.base
          (allocRange (toMiriSize w) (Size.ofBytes 1)) false =
        Bind.bind
          (readTargetUIntMirror RuntimeTargetDataLayout.default.base boolBytes)
          (fun x =>
            (Scalar.fromUInt x (Size.ofBytes 1)).mapError AllocError.scalar) ∧
      after2.provenanceMap = ProvenanceMap.new ∧
      after2.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes) ∧
      after2.mutability = .Mut ∧ after2.align = Align.ONE := by
  have h_n2 := pair_size_two_nat w
  let ⟨bs1, h_bs1⟩ :
      ∃ x, bytes0.extract 0 0 ++ data ++
        bytes0.extract (toMiriSize w).bytes.toNat
          (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes.toNat = x := ⟨_, rfl⟩
  have h_bytes1 :
      bs1.size = (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes.toNat := by
    rw [← h_bs1, Array.size_append, Array.size_append, Array.size_extract,
      Array.size_extract, h_b0, h_dlen, h_n2, Nat.zero_min, Nat.min_self,
      Nat.sub_zero, Nat.zero_add]
    have h_le :
        (toMiriSize w).bytes.toNat ≤ 2 * (toMiriSize w).bytes.toNat := by
      rw [Nat.two_mul]
      exact Nat.le_add_left _ _
    rw [Nat.add_comm, Nat.sub_add_cancel h_le]
  have h_ext1 : bs1.extract 0 (toMiriSize w).bytes.toNat = data := by
    rw [← h_bs1, array_extract_empty_same, Array.empty_append]
    exact array_extract_append_left data _ _ h_dlen
  let ⟨bs2, h_bs2⟩ :
      ∃ x, bs1.extract 0 (toMiriSize w).bytes.toNat ++ boolBytes ++
        bs1.extract ((toMiriSize w).bytes.toNat + 1)
          (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes.toNat = x := ⟨_, rfl⟩
  have h_bytes2 :
      bs2.size = (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes.toNat := by
    rw [← h_bs2, Array.size_append, Array.size_append, Array.size_extract,
      Array.size_extract, h_bytes1, h_blen, h_n2, Nat.min_self]
    have h_pos : 1 ≤ (toMiriSize w).bytes.toNat := by cases w <;> decide
    have h_le1 :
        (toMiriSize w).bytes.toNat ≤ 2 * (toMiriSize w).bytes.toNat := by
      rw [Nat.two_mul]; exact Nat.le_add_left _ _
    have h_le2 :
        (toMiriSize w).bytes.toNat + 1 ≤ 2 * (toMiriSize w).bytes.toNat := by
      rw [Nat.two_mul]; exact Nat.add_le_add_left h_pos _
    rw [Nat.min_eq_left h_le1, Nat.sub_zero,
      Nat.add_comm ((toMiriSize w).bytes.toNat + 1), Nat.sub_add_cancel h_le2]
  have h_ext_int : bs2.extract 0 (toMiriSize w).bytes.toNat = data := by
    rw [← h_bs2, h_ext1]
    exact array_extract_sandwich_prefix data boolBytes _ _ h_dlen
  have h_ext_bool :
      bs2.extract (toMiriSize w).bytes.toNat ((toMiriSize w).bytes.toNat + 1) =
        boolBytes := by
    rw [← h_bs2, h_ext1]
    exact array_extract_sandwich data boolBytes _ _ 1 h_dlen h_blen
  have h_r1_start :
      (allocRange Size.ZERO (toMiriSize w)).start.bytes.toNat = 0 := rfl
  have h_r2_start :
      (allocRange (toMiriSize w) (Size.ofBytes 1)).start.bytes.toNat =
        (toMiriSize w).bytes.toNat := rfl
  have h_r2_add := pair_r2_nat_add w
  have h_f_end := pair_full_end w
  have h_f_oob := pair_full_oob w
  have h_r1_e := pair_r1_end w
  have h_r1_o := pair_r1_oob w
  have h_r2_e := pair_r2_end w
  have h_r2_o := pair_r2_oob w
  have h_r3_e := pair_r3_end w
  have h_r3_o := pair_r3_oob w
  have h_r1_sz :
      (allocRange Size.ZERO (toMiriSize w)).size = toMiriSize w := rfl
  have h_r2_sz :
      (allocRange (toMiriSize w) (Size.ofBytes 1)).size = Size.ofBytes 1 := rfl
  dsimp only [Allocation.fromBytes] at h_fb
  change (Bind.bind (Except.ok Align.ONE) _) = _ at h_fb
  dsimp only [Bind.bind, Except.bind] at h_fb
  rw [h_b0] at h_fb
  cases w <;> (
    dsimp only [toMiriSize, Size.ofBytes] at h_fb
    injection h_fb with h_init_eq; subst h_init_eq
    rw [UInt64.ofNat_toNat] at h_wu
    change (match checkedSliceMirror bytes0 (Size.ofBytes _) _ with
      | Except.error _ => _ | Except.ok _ => _) = _ at h_wu
    have h_c := checkedSliceMirror_ok bytes0 _ _ _ h_b0 h_f_end h_f_oob
    dsimp only [toMiriSize, Size.ofBytes] at h_c h_wu
    rw [h_c] at h_wu
    dsimp only [allocRange] at h_wu
    change (if false = true then _ else _) = _ at h_wu
    rw [ite_false_eq_true] at h_wu
    change (if false = true then _ else _) = _ at h_wu
    rw [ite_false_eq_true] at h_wu
    injection h_wu with _ h_raw_eq
    simp only [pure, Pure.pure, ProvenanceMap.new, Option.map,
      Size.ZERO] at h_raw_eq
    first
    | (rw [show (2 * 1 : UInt64) = 2 * (toMiriSize .i8).bytes from rfl,
        show Size.ofBytes (0 + 2 * (toMiriSize .i8).bytes) =
          Size.ofBytes (2 * (toMiriSize .i8).bytes) from rfl] at h_raw_eq)
    | (rw [show (2 * 2 : UInt64) = 2 * (toMiriSize .i16).bytes from rfl,
        show Size.ofBytes (0 + 2 * (toMiriSize .i16).bytes) =
          Size.ofBytes (2 * (toMiriSize .i16).bytes) from rfl] at h_raw_eq)
    | (rw [show (2 * 4 : UInt64) = 2 * (toMiriSize .i32).bytes from rfl,
        show Size.ofBytes (0 + 2 * (toMiriSize .i32).bytes) =
          Size.ofBytes (2 * (toMiriSize .i32).bytes) from rfl] at h_raw_eq)
    | (rw [show IntWidth.i64 = IntWidth.i64 from rfl] at h_b0
       rw [show (2 * 8 : UInt64) = 2 * (toMiriSize .i64).bytes from rfl,
        show Size.ofBytes (0 + 2 * (toMiriSize .i64).bytes) =
          Size.ofBytes (2 * (toMiriSize .i64).bytes) from rfl] at h_raw_eq)
    | (rw [show IntWidth.isize = IntWidth.isize from rfl] at h_b0
       rw [show (2 * 8 : UInt64) = 2 * (toMiriSize .isize).bytes from rfl,
        show Size.ofBytes (0 + 2 * (toMiriSize .isize).bytes) =
          Size.ofBytes (2 * (toMiriSize .isize).bytes) from rfl] at h_raw_eq)
    | (rw [show (2 * 16 : UInt64) = 2 * (toMiriSize .i128).bytes from rfl,
        show Size.ofBytes (0 + 2 * (toMiriSize .i128).bytes) =
          Size.ofBytes (2 * (toMiriSize .i128).bytes) from rfl] at h_raw_eq)
    subst h_raw_eq
    dsimp only [Allocation.withExtra]
    apply Exists.intro; apply Exists.intro; apply Exists.intro
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [Allocation.writeScalar, Id.run, bind, Bind.bind,
        pure, Pure.pure]
      rw [bne_self_eq_false, ite_false_eq_true, h_r1_sz,
        scalar_fromScalarInt_toBitsOrPtr]
      dsimp only
      change (match checkedSliceMirror bytes0 (Size.ofBytes _) _ with
        | Except.error _ => _ | Except.ok _ => _) = _
      rw [checkedSliceMirror_ok _ _ _ _ h_b0 h_r1_e h_r1_o]
      dsimp only
      first
      | change (match targetUIntBytesMirror RuntimeTargetDataLayout.default.base
            (toMiriSize .i8) (miriScalar .i8 bits).data with
          | Except.ok _ => _ | Except.error _ => _) = _
      | change (match targetUIntBytesMirror RuntimeTargetDataLayout.default.base
            (toMiriSize .i16) (miriScalar .i16 bits).data with
          | Except.ok _ => _ | Except.error _ => _) = _
      | change (match targetUIntBytesMirror RuntimeTargetDataLayout.default.base
            (toMiriSize .i32) (miriScalar .i32 bits).data with
          | Except.ok _ => _ | Except.error _ => _) = _
      | (rw [show IntWidth.i64 = IntWidth.i64 from rfl] at h_t1
         change (match targetUIntBytesMirror
            RuntimeTargetDataLayout.default.base
            (toMiriSize .i64) (miriScalar .i64 bits).data with
          | Except.ok _ => _ | Except.error _ => _) = _)
      | (rw [show IntWidth.isize = IntWidth.isize from rfl] at h_t1
         change (match targetUIntBytesMirror
            RuntimeTargetDataLayout.default.base
            (toMiriSize .isize) (miriScalar .isize bits).data with
          | Except.ok _ => _ | Except.error _ => _) = _)
      | change (match targetUIntBytesMirror RuntimeTargetDataLayout.default.base
            (toMiriSize .i128) (miriScalar .i128 bits).data with
          | Except.ok _ => _ | Except.error _ => _) = _
      rw [h_t1]
      dsimp only
      rw [h_r1_start, Nat.zero_add, h_b0, h_bs1, h_bytes1]
      change (if false = true then _ else _) = _
      rw [ite_false_eq_true]
    · rfl
    · rfl
    · dsimp only [Allocation.writeScalar, Id.run, bind, Bind.bind,
        pure, Pure.pure]
      rw [bne_self_eq_false, ite_false_eq_true, h_r2_sz,
        scalar_fromBool_toBitsOrPtr]
      dsimp only
      change (match checkedSliceMirror bs1
            (Size.ofBytes (2 * (toMiriSize _).bytes)) _ with
        | Except.error _ => _ | Except.ok _ => _) = _
      rw [checkedSliceMirror_ok _ _ _ _ h_bytes1 h_r2_e h_r2_o]
      dsimp only
      change (match targetUIntBytesMirror RuntimeTargetDataLayout.default.base
          (Size.ofBytes 1) (ScalarInt.ofBool b).data with
        | Except.ok _ => _ | Except.error _ => _) = _
      rw [h_t2]
      dsimp only
      rw [h_r2_start, show (Size.ofBytes 1).bytes.toNat = 1 from rfl,
        h_bytes1, h_bs2, h_bytes2]
      change (if false = true then _ else _) = _
      rw [ite_false_eq_true]
    · change (match checkedSliceMirror bs2
            (Size.ofBytes (2 * (toMiriSize _).bytes)) _ with
        | Except.error _ => _ | Except.ok _ => _) = _
      rw [checkedSliceMirror_ok _ _ _ _ h_bytes2 h_r3_e h_r3_o]
      exact rfl
    · change Bind.bind (checkedSliceMirror bs2
          (Size.ofBytes (2 * (toMiriSize _).bytes)) _) _ = _
      rw [checkedSliceMirror_ok _ _ _ _ h_bytes2 h_r1_e h_r1_o]
      dsimp only [Bind.bind, Except.bind]
      rw [h_r1_start, h_ext_int]
      rfl
    · change Bind.bind (checkedSliceMirror bs2
          (Size.ofBytes (2 * (toMiriSize _).bytes)) _) _ = _
      rw [checkedSliceMirror_ok _ _ _ _ h_bytes2 h_r2_e h_r2_o]
      dsimp only [Bind.bind, Except.bind]
      rw [h_r2_start, ← h_r2_add, h_ext_bool]
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · change Bind.bind (checkedSliceMirror bs2
          (Size.ofBytes (2 * (toMiriSize _).bytes)) _) _ = _
      rw [checkedSliceMirror_ok _ _ _ _ h_bytes2 h_r1_e h_r1_o]
      dsimp only [Bind.bind, Except.bind]
      rw [h_r1_start, h_ext_int]
      rfl
    · change Bind.bind (checkedSliceMirror bs2
          (Size.ofBytes (2 * (toMiriSize _).bytes)) _) _ = _
      rw [checkedSliceMirror_ok _ _ _ _ h_bytes2 h_r2_e h_r2_o]
      dsimp only [Bind.bind, Except.bind]
      rw [h_r2_start, ← h_r2_add, h_ext_bool]
      rfl
    · rfl
    · rfl
    · rfl
    · rfl)

private theorem tryNew_pair_write_read (w : IntWidth) (bits : BitVec 128)
    (b : Bool) {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (Size.ofBytes (2 * (toMiriSize w).bytes)) Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc) :
    let alloc := rawAlloc.withExtra (Miri.TreeBorrows.BorrowTree.new
      Miri.Memory.BorTag.one (Size.ofBytes (2 * (toMiriSize w).bytes)))
    ∃ middle after after2,
      Allocation.writeScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w))
          (.fromScalarInt (miriScalar w bits)) alloc = .ok () middle ∧
      middle.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes) ∧
      middle.mutability = .Mut ∧
      Allocation.writeScalar RuntimeTargetDataLayout.default.base
          (allocRange (toMiriSize w) (Size.ofBytes 1))
          (.fromBool b) middle = .ok () after ∧
      Allocation.writeUninit (pairPadRange w) (Size.ofBytes 8) after =
        .ok () after2 ∧
      PairAllocReads w bits b after ∧ PairAllocReads w bits b after2 := by
  let bytes0 : Array UInt8 :=
    Array.replicate (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes.toNat 0
  have h_b0 :
      bytes0.size = (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes.toNat :=
    Array.size_replicate
  let ⟨init, h_fb, h_wu⟩ :=
    tryNew_size_uninit_image (Size.ofBytes (2 * (toMiriSize w).bytes))
      (pair_size_pos w) h_raw
  let n := (toMiriSize w).bytes.toNat
  let x := (miriScalar w bits).data.toNat
  let data := beBytes x n n
  have h_dlen : data.size = n := beBytes_size x n n
  have h_t1 :
      targetUIntBytesMirror RuntimeTargetDataLayout.default.base
        (toMiriSize w) (miriScalar w bits).data = .ok data := by
    cases w <;> exact targetUIntBytesMirror_be _ (by decide) _
  let boolBytes := Array.mk [boolByte b]
  have h_blen : boolBytes.size = 1 := rfl
  have h_t2 :
      targetUIntBytesMirror RuntimeTargetDataLayout.default.base
        (Size.ofBytes 1) (ScalarInt.ofBool b).data = .ok boolBytes :=
    targetUIntBytesMirror_bool b
  let ⟨middle, after, after2, h_w1, h_msz, h_mmut, h_w2, h_wu2,
      h_a_r1, h_a_r2, h_a_prov, h_a_sz, h_a_mut, h_a_al,
      h_a2_r1, h_a2_r2, h_a2_prov, h_a2_sz, h_a2_mut, h_a2_al⟩ :=
    pair_write_read_abstract w bits b bytes0 data boolBytes
      h_b0 h_dlen h_blen h_t1 h_t2 h_fb h_wu
  have h_n_le : n ≤ 16 := by cases w <;> decide
  have h_bw : 8 * n = w.bitWidth := by cases w <;> rfl
  have h_lt : x < HPow.hPow 2 (8 * n) := by
    dsimp only [x]
    rw [miriScalar_data, toNat_truncateBits, h_bw]
    exact Nat.mod_lt _ (intWidth_modulus_pos w)
  have h_read_int :
      Bind.bind
        (readTargetUIntMirror RuntimeTargetDataLayout.default.base data)
        (fun v => (Scalar.fromUInt (Prov := Miri.Memory.Provenance)
          v (toMiriSize w)).mapError AllocError.scalar) =
        .ok (.fromScalarInt (miriScalar w bits)) := by
    dsimp only [data]
    rw [readTargetUIntMirror_be _ h_n_le _]
    dsimp only [Bind.bind, Except.bind]
    rw [Nat.mod_eq_of_lt h_lt]
    dsimp only [x]
    rw [miriScalar_data, bitVec128_ofNat_toNat]
    exact scalar_fromUInt_truncateBits w bits
  have h_r1 :
      after.readScalar RuntimeTargetDataLayout.default.base
        (allocRange Size.ZERO (toMiriSize w)) false =
        .ok (.fromScalarInt (miriScalar w bits)) := by
    rw [h_a_r1, h_read_int]
  have h_r2 :
      after.readScalar RuntimeTargetDataLayout.default.base
        (allocRange (toMiriSize w) (Size.ofBytes 1)) false =
        .ok (.fromBool b) := by
    rw [h_a_r2]
    exact readTargetUInt_bool b
  have h_c1 :=
    clearProvenance_of_read_ok_range (allocRange Size.ZERO (toMiriSize w))
      (toMiriSize w) (pair_r1_end w) h_a_prov h_r1
  have h_c2 :=
    clearProvenance_of_read_ok_range
      (allocRange (toMiriSize w) (Size.ofBytes 1))
      (Size.ofBytes ((toMiriSize w).bytes + 1)) (pair_r2_end w) h_a_prov h_r2
  have h2_r1 :
      after2.readScalar RuntimeTargetDataLayout.default.base
        (allocRange Size.ZERO (toMiriSize w)) false =
        .ok (.fromScalarInt (miriScalar w bits)) := by
    rw [h_a2_r1, h_read_int]
  have h2_r2 :
      after2.readScalar RuntimeTargetDataLayout.default.base
        (allocRange (toMiriSize w) (Size.ofBytes 1)) false =
        .ok (.fromBool b) := by
    rw [h_a2_r2]
    exact readTargetUInt_bool b
  have h2_c1 :=
    clearProvenance_of_read_ok_range (allocRange Size.ZERO (toMiriSize w))
      (toMiriSize w) (pair_r1_end w) h_a2_prov h2_r1
  have h2_c2 :=
    clearProvenance_of_read_ok_range
      (allocRange (toMiriSize w) (Size.ofBytes 1))
      (Size.ofBytes ((toMiriSize w).bytes + 1)) (pair_r2_end w) h_a2_prov h2_r2
  exact ⟨middle, after, after2, h_w1, h_msz, h_mmut, h_w2, h_wu2,
    ⟨h_r1, h_r2, h_c1, h_c2, h_a_sz, h_a_mut, h_a_al⟩,
    ⟨h2_r1, h2_r2, h2_c1, h2_c2, h_a2_sz, h_a2_mut, h_a2_al⟩⟩

private theorem tryNew_pair_writeUninit (w : IntWidth)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (Size.ofBytes (2 * (toMiriSize w).bytes)) Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc) :
    let alloc := rawAlloc.withExtra (Miri.TreeBorrows.BorrowTree.new
      Miri.Memory.BorTag.one (Size.ofBytes (2 * (toMiriSize w).bytes)))
    ∃ after info,
      Allocation.writeUninit
          (allocRange Size.ZERO (Size.ofBytes (2 * (toMiriSize w).bytes)))
          (Size.ofBytes 8) alloc = .ok () after ∧
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false =
        .error (.invalidUninitBytes info) ∧
      after.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes) ∧
      after.mutability = .Mut ∧ after.align = Align.ONE := by
  let ⟨init, h_fb, h_wu⟩ :=
    tryNew_size_uninit_image (Size.ofBytes (2 * (toMiriSize w).bytes))
      (pair_size_pos w) h_raw
  cases w <;> (
    injection h_fb with h_init_eq; subst h_init_eq
    injection h_wu with _ h_raw_eq
    dsimp only [toMiriSize, allocRange, Size.ZERO, Size.ofBytes] at h_raw_eq
    simp only [pure, Pure.pure, ProvenanceMap.new, Option.map,
      Array.size_replicate] at h_raw_eq
    first
    | (rw [show (2 * 1 : UInt64).toNat = 2 from rfl,
          show (0 + 2 * 1 : UInt64) = 2 from rfl] at h_raw_eq)
    | (rw [show (2 * 2 : UInt64).toNat = 4 from rfl,
          show (0 + 2 * 2 : UInt64) = 4 from rfl] at h_raw_eq)
    | (rw [show (2 * 4 : UInt64).toNat = 8 from rfl,
          show (0 + 2 * 4 : UInt64) = 8 from rfl] at h_raw_eq)
    | (rw [show (2 * 8 : UInt64).toNat = 16 from rfl,
          show (0 + 2 * 8 : UInt64) = 16 from rfl] at h_raw_eq)
    | (rw [show (2 * 16 : UInt64).toNat = 32 from rfl,
          show (0 + 2 * 16 : UInt64) = 32 from rfl] at h_raw_eq)
    subst h_raw_eq
    exact ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩)

private def offMemPlace (off : Size) :
    Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
  ⟨⟨off, some (.concrete retAllocId Miri.Memory.BorTag.one)⟩, .none, none⟩

private theorem sizeAsI64_pair (w : IntWidth) :
    Miri.Memory.sizeAsI64 (Size.ofBytes (2 * (toMiriSize w).bytes)) =
      .ok (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes.toNat := by
  cases w <;> rfl

private theorem fitsI64_of_le32 (n : Nat) (hn : n ≤ 32) :
    ((Neg.neg (HPow.hPow (2 : Int) (63 : Nat)) ≤ Int.ofNat n) &&
      (Int.ofNat n < HPow.hPow (2 : Int) (63 : Nat))) = true := by
  have h_pow : HPow.hPow (2 : Int) (63 : Nat) = Int.ofNat (HPow.hPow 2 63) :=
    int_pow_eq_ofNat 2 63
  have h_val : HPow.hPow (2 : Nat) 63 = 9223372036854775808 := by decide
  rw [h_pow, h_val]
  have h1 : Neg.neg (Int.ofNat 9223372036854775808) ≤ Int.ofNat n :=
    Int.le_trans (by decide) (Int.natCast_nonneg n)
  have h2 : Int.ofNat n < Int.ofNat 9223372036854775808 :=
    Int.ofNat_lt.mpr (Nat.lt_of_le_of_lt hn (by decide))
  rw [decide_eq_true h1, decide_eq_true h2]
  rfl

private theorem checkedBounds_pair (w : IntWidth) :
    Miri.Memory.checkedBounds ⟨Size.ofBytes 8⟩ retAllocId
        (Size.ofBytes (2 * (toMiriSize w).bytes)) Size.ZERO
        (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes.toNat .memoryAccess =
      .ok () := by
  have h_fits := fitsI64_of_le32
    (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes.toNat
    (by cases w <;> decide)
  dsimp only [Miri.Memory.checkedBounds]
  change
    (if (!((Neg.neg (HPow.hPow (2 : Int) (63 : Nat)) ≤
              Int.ofNat
                (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes.toNat) &&
            (Int.ofNat
                (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes.toNat <
              HPow.hPow (2 : Int) (63 : Nat)))) = true
     then _ else _) = Except.ok ()
  rw [h_fits]
  cases w <;> rfl

private theorem checkedBounds_pair_int (w : IntWidth) :
    Miri.Memory.checkedBounds ⟨Size.ofBytes 8⟩ retAllocId
        (Size.ofBytes (2 * (toMiriSize w).bytes)) Size.ZERO
        (toMiriSize w).bytes.toNat .memoryAccess =
      .ok () := by
  have h_fits := fitsI64_of_le32 (toMiriSize w).bytes.toNat
    (by cases w <;> decide)
  dsimp only [Miri.Memory.checkedBounds]
  change
    (if (!((Neg.neg (HPow.hPow (2 : Int) (63 : Nat)) ≤
              Int.ofNat (toMiriSize w).bytes.toNat) &&
            (Int.ofNat (toMiriSize w).bytes.toNat <
              HPow.hPow (2 : Int) (63 : Nat)))) = true
     then _ else _) = Except.ok ()
  rw [h_fits]
  cases w <;> rfl

private theorem checkedBounds_pair_bool (w : IntWidth) :
    Miri.Memory.checkedBounds ⟨Size.ofBytes 8⟩ retAllocId
        (Size.ofBytes (2 * (toMiriSize w).bytes)) (toMiriSize w)
        (Size.ofBytes 1).bytes.toNat .memoryAccess =
      .ok () := by
  have h_fits := fitsI64_of_le32 (Size.ofBytes 1).bytes.toNat (by decide)
  dsimp only [Miri.Memory.checkedBounds]
  change
    (if (!((Neg.neg (HPow.hPow (2 : Int) (63 : Nat)) ≤
              Int.ofNat (Size.ofBytes 1).bytes.toNat) &&
            (Int.ofNat (Size.ofBytes 1).bytes.toNat <
              HPow.hPow (2 : Int) (63 : Nat)))) = true
     then _ else _) = Except.ok ()
  rw [h_fits]
  cases w <;> rfl

private theorem getPtrAllocMut_pair_nonGhost (w : IntWidth)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (h_sz : alloc.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes))
    (h_mut : alloc.mutability = .Mut)
    (h_extra : alloc.extra = Miri.TreeBorrows.BorrowTree.new
      Miri.Memory.BorTag.one (Size.ofBytes (2 * (toMiriSize w).bytes)))
    (h_dr : machine.dataRace = none) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Memory.AllocationAccess.getPtrAllocMut mem ⟨machine, none⟩
        ⟨Size.ofBytes 8⟩ retPtr (Size.ofBytes (2 * (toMiriSize w).bytes))
        false none refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig) =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId,
          allocRange Size.ZERO (Size.ofBytes (2 * (toMiriSize w).bytes)),
          alloc⟩,
        .ok (some ⟨retAllocId,
          allocRange Size.ZERO (Size.ofBytes (2 * (toMiriSize w).bytes)),
          alloc⟩)⟩ := by
  intro mem
  exact Miri.Memory.AllocationAccess.live_mut_of_edges mem ⟨machine, none⟩
    ⟨Size.ofBytes 8⟩ retPtr _ none refAccessConfig.globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
    retAllocId ⟨.stack, alloc⟩ (.concrete Miri.Memory.BorTag.one)
    (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes.toNat
    (sizeAsI64_pair w)
    (by cases w <;> decide)
    (Miri.Interpreter.PlaceMachine.resolvePointer_ok refAccessConfig mem machine
      retPtr _ _ rfl)
    (singleton_live_find _)
    h_mut
    rfl
    (by rw [h_sz]; exact checkedBounds_pair w)
    rfl
    (by
      dsimp only [Miri.Interpreter.PlaceMachine.accessHooks]
      rw [h_extra]
      exact Miri.Interpreter.PlaceMachine.memoryAccess_fresh_write
        refAccessConfig machine retAllocId Miri.Memory.BorTag.one
        _ h_dr rfl rfl rfl)
    (singleton_live_filter_push _ _)

private theorem writeMemory_retPlace_pair (types : List MirTy) (w : IntWidth)
    (s : Bool) (bits : BitVec 128) (b : Bool)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (Size.ofBytes (2 * (toMiriSize w).bytes)) Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, rawAlloc.withExtra
          (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
            (Size.ofBytes (2 * (toMiriSize w).bytes)))⟩)]) })
    (h_dr : st.machine.dataRace = none) :
    ∃ after after2,
      let mem' :=
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      Miri.Interpreter.PlaceMachine.writeMemory refAccessConfig (fun _ => true)
          (.scalarPair (.fromScalarInt (miriScalar w bits)) (.fromBool b))
          ⟨retMemPlace,
            refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ st =
        .ok () { st with machine := { st.machine with memory := mem' } } ∧
      Allocation.writeUninit (pairPadRange w) (Size.ofBytes 8) after =
        .ok () after2 ∧
      PairAllocReads w bits b after ∧ PairAllocReads w bits b after2 := by
  let ⟨_, h_raw_eq, h_rsz, _, _, h_rmut, _⟩ :=
    Allocation.tryNew_replicate_full (P := Miri.Memory.Provenance)
      (Size.ofBytes (2 * (toMiriSize w).bytes)) Align.ONE 1 (by decide)
      (by decide)
  rw [h_raw] at h_raw_eq
  injection h_raw_eq with h_raw_id
  subst h_raw_id
  let alloc := rawAlloc.withExtra (Miri.TreeBorrows.BorrowTree.new
    Miri.Memory.BorTag.one (Size.ofBytes (2 * (toMiriSize w).bytes)))
  let ⟨middle, after, after2, h_w1, _, _, h_w2, h_pad, h_rd1, h_rd2⟩ :=
    tryNew_pair_write_read w bits b h_raw
  have h_sc_sz : (Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
      (miriScalar w bits)).size = toMiriSize w := miriScalar_size w bits
  let place : Miri.Interpreter.MemoryOperandPlace Miri.Memory.Provenance :=
    ⟨retMemPlace, localMemoryLayout (refLocalLayoutForTy types
      (.tuple [.int w s, .bool]))⟩
  have h_uns : place.layout.backendRepr.isUnsized = false := rfl
  have h_ptr_acc := getPtrAllocMut_pair_nonGhost w mem1 alloc st.machine
    h_rsz h_rmut rfl h_dr
  have h_place_acc :
      Miri.Interpreter.getPlaceAllocMut
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
        ⟨st.machine, none⟩ place
        refAccessConfig.runtime false none refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO place.layout.size, alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO place.layout.size,
          alloc⟩)⟩ :=
    Miri.Interpreter.getPlaceAllocMut_sized_of_access _ _ _ _
      (Size.ofBytes 8) none _ _ _ _ h_uns rfl rfl h_ptr_acc
  have h_fb_sz : (Scalar.fromBool (Prov := Miri.Memory.Provenance) b).size =
      Size.ofBytes 1 := by
    cases b <;> rfl
  have h_wA : Miri.ABI.Primitive.size (.Int (toMiriInteger w) s)
      refAccessConfig.runtime =
      .ok (Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
        (miriScalar w bits)).size := by
    rw [h_sc_sz]; cases w <;> rfl
  have h_wB : Miri.ABI.Primitive.size (.Int .I8 false) refAccessConfig.runtime =
      .ok (Scalar.fromBool (Prov := Miri.Memory.Provenance) b).size := by
    rw [h_fb_sz]; rfl
  have h_cB : (Scalar.fromBool (Prov := Miri.Memory.Provenance) b).isPointer =
      false := by
    cases b <;> rfl
  have h_pos : (toMiriSize w).bytes ≠ 0 := by cases w <;> decide
  have h_fe : (Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
      (miriScalar w bits)).size.bytes ≤ (toMiriSize w).bytes := by
    rw [h_sc_sz]; exact UInt64.le_refl _
  have h_bound : (toMiriSize w).bytes.toNat +
      (Scalar.fromBool (Prov := Miri.Memory.Provenance) b).size.bytes.toNat ≤
      (Size.ofBytes (2 * (toMiriSize w).bytes)).bytes.toNat := by
    rw [h_fb_sz]; cases w <;> exact Nat.le_of_ble_eq_true rfl
  have h_wm_op :
      Miri.Interpreter.writeImmediateToMplaceNoValidate
        st.machine.memory ⟨st.machine, none⟩
        (.scalarPair (.fromScalarInt (miriScalar w bits)) (.fromBool b)) place
        refAccessConfig.runtime refAccessConfig.ghostMode
        refAccessConfig.globalKind refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout (fun _ => true) =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO place.layout.size, after⟩,
        .ok ()⟩ := by
    rw [h_mem]
    refine Miri.Interpreter.writeImmediate_pair_of_access
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, middle⟩)]) }
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      ⟨st.machine, none⟩ place
      refAccessConfig.runtime none refAccessConfig.globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
      refAccessConfig.dynamicLayout
      (.fromScalarInt (miriScalar w bits)) (.fromBool b)
      (.Initialized (value := .Int (toMiriInteger w) s)
        (validRange := refFullWrappingRangeSize (toMiriSize w)))
      (.Initialized (value := .Int .I8 false)
        (validRange := ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 1⟩))
      (toMiriSize w) retAllocId alloc middle after
      rfl h_wA h_wB rfl h_cB h_pos h_fe h_bound
      ?_
      (by rw [h_sc_sz]; exact h_w1)
      (singleton_setLiveAllocation mem1 alloc middle)
      (by rw [h_fb_sz]; exact h_w2)
      (singleton_setLiveAllocation mem1 middle after)
    exact h_place_acc
  exact ⟨after, after2,
    Miri.Interpreter.PlaceMachine.writeMemory_of_result refAccessConfig
      (fun _ => true)
      (.scalarPair (.fromScalarInt (miriScalar w bits)) (.fromBool b))
      ⟨retMemPlace, refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ st
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      _ rfl h_wm_op,
    h_pad, h_rd1, h_rd2⟩
private theorem getPtrAlloc_off_ghost (off sz : Size) (signedSize : Int)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_res : cfg.resolvePointer = refResolvePointer)
    (h_gh : cfg.globalHooks = refGlobalAllocationHooks)
    (h_sa : Miri.Memory.sizeAsI64 sz = .ok signedSize)
    (h_nz : (signedSize != 0) = true)
    (h_bounds : Miri.Memory.checkedBounds ⟨Size.ofBytes 8⟩ retAllocId
      alloc.byteSize off signedSize .memoryAccess = .ok ()) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Memory.AllocationAccess.getPtrAlloc mem ⟨machine, none⟩
        ⟨Size.ofBytes 8⟩ (offMemPlace off).ptr sz true none
        cfg.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks cfg) =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId, allocRange off sz, alloc⟩,
        .ok (some ⟨retAllocId, allocRange off sz, alloc⟩)⟩ := by
  intro mem
  have h_raw : Miri.Memory.MemoryLifecycle.getAllocRaw mem ⟨machine, none⟩
      retAllocId none cfg.globalHooks = ⟨mem, ⟨machine, none⟩, .ok alloc⟩ := by
    dsimp only [Miri.Memory.MemoryLifecycle.getAllocRaw]
    rw [h_gh]
    dsimp only [refGlobalAllocationHooks, mem, Id.run, bind, Bind.bind,
      pure, Pure.pure]
    rw [singleton_live_find]
  have h_rp : (Miri.Interpreter.PlaceMachine.accessHooks cfg).resolvePointer
      mem ⟨machine, none⟩ (offMemPlace off).ptr signedSize =
      ⟨⟨machine, none⟩,
        .ok (.ok ⟨retAllocId, off, .concrete Miri.Memory.BorTag.one⟩)⟩ := by
    dsimp only [Miri.Interpreter.PlaceMachine.accessHooks]
    rw [h_res]
    rfl
  dsimp only [Miri.Memory.AllocationAccess.getPtrAlloc]
  change (match Miri.Memory.sizeAsI64 sz with
    | Except.ok _ => _ | Except.error _ => _) = _
  rw [h_sa]
  change (if (signedSize != 0) = true then _ else _) = _
  rw [h_nz, mem_ite_true_eq]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_rp]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [mem_ite_false_eq, h_raw]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_bounds]
  rfl

private theorem getPtrAllocMut_off_ghost (off sz : Size) (signedSize : Int)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (h_mut : alloc.mutability = .Mut)
    (h_sa : Miri.Memory.sizeAsI64 sz = .ok signedSize)
    (h_nz : (signedSize != 0) = true)
    (h_bounds : Miri.Memory.checkedBounds ⟨Size.ofBytes 8⟩ retAllocId
      alloc.byteSize off signedSize .memoryAccess = .ok ()) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Memory.AllocationAccess.getPtrAllocMut mem ⟨machine, none⟩
        ⟨Size.ofBytes 8⟩ (offMemPlace off).ptr sz true none
        refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig) =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId, allocRange off sz, alloc⟩,
        .ok (some ⟨retAllocId, allocRange off sz, alloc⟩)⟩ := by
  intro mem
  have h_raw : Miri.Memory.MemoryLifecycle.getAllocRawMut mem ⟨machine, none⟩
      retAllocId none refAccessConfig.globalHooks =
      ⟨mem, ⟨machine, none⟩, .ok alloc⟩ := by
    dsimp only [Miri.Memory.MemoryLifecycle.getAllocRawMut, refAccessConfig,
      refGlobalAllocationHooks, mem, Id.run, bind, Bind.bind, pure, Pure.pure]
    rw [singleton_live_find]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    rw [h_mut]
    rfl
  have h_rp :
      (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig).resolvePointer
        mem ⟨machine, none⟩ (offMemPlace off).ptr signedSize =
      ⟨⟨machine, none⟩,
        .ok (.ok ⟨retAllocId, off, .concrete Miri.Memory.BorTag.one⟩)⟩ :=
    Miri.Interpreter.PlaceMachine.resolvePointer_ok refAccessConfig mem machine
      _ _ _ rfl
  dsimp only [Miri.Memory.AllocationAccess.getPtrAllocMut]
  change (match Miri.Memory.sizeAsI64 sz with
    | Except.ok _ => _ | Except.error _ => _) = _
  rw [h_sa]
  change (if (signedSize != 0) = true then _ else _) = _
  rw [h_nz, mem_ite_true_eq]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_rp]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [mem_ite_true_eq, h_raw]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_bounds]
  rfl
private theorem readImmediateFromMplaceRaw_pair_int (types : List MirTy)
    (w : IntWidth) (s : Bool)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_res : cfg.resolvePointer = refResolvePointer)
    (h_gh : cfg.globalHooks = refGlobalAllocationHooks)
    (h_sz : after.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes)) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    Miri.Interpreter.readImmediateFromMplaceRaw mem ⟨machine, none⟩
        ⟨retMemPlace, localMemoryLayout (refLocalLayoutForTy types (.int w s))⟩
        RuntimeTargetDataLayout.default true none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .ok (some ⟨.scalar sc,
            localMemoryLayout (refLocalLayoutForTy types (.int w s))⟩)⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .error (.allocation err)⟩ := by
  intro mem
  have h_ptr := getPtrAlloc_off_ghost Size.ZERO (toMiriSize w)
    (toMiriSize w).bytes.toNat mem1 after machine cfg h_res h_gh
    (sizeAsI64_toMiriSize w) (by cases w <;> decide)
    (by rw [h_sz]; exact checkedBounds_pair_int w)
  have h_acc := getPlaceAlloc_sized_of_access_poly mem ⟨machine, none⟩
    ⟨retMemPlace, localMemoryLayout (refLocalLayoutForTy types (.int w s))⟩
    true none cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
    cfg.dynamicLayout ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩
    (by cases w <;> cases s <;> rfl) rfl h_ptr
  exact readImmediateFromMplaceRaw_retPlace_int_aux w s
    (Miri.ABI.AbiAlign.new Align.ONE).abi
    (refFullWrappingRangeSize (toMiriSize w))
    (some (tyIdFor types (.int w s)))
    mem1 after machine cfg h_acc

private theorem readImmediate_mem_pair_int (types : List MirTy)
    (w : IntWidth) (s : Bool)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_rt : cfg.runtime = Miri.ABI.RuntimeTargetDataLayout.default)
    (h_gk : cfg.globalKind = none)
    (h_res : cfg.resolvePointer = refResolvePointer)
    (h_gh : cfg.globalHooks = refGlobalAllocationHooks)
    (h_sz : after.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes)) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    Miri.Interpreter.readImmediate mem ⟨machine, none⟩
        (.indirect retMemPlace)
        (localMemoryLayout (refLocalLayoutForTy types (.int w s)))
        cfg.runtime true cfg.globalKind cfg.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks cfg) cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .ok ⟨.scalar sc,
            localMemoryLayout (refLocalLayoutForTy types (.int w s))⟩⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .error (.allocation err)⟩ := by
  intro mem
  have h_raw := readImmediateFromMplaceRaw_pair_int types w s mem1 after
    machine cfg h_res h_gh h_sz
  rw [h_rt, h_gk]
  cases w <;> cases s <;> (
    dsimp only [Miri.Interpreter.readImmediate,
      Miri.Interpreter.readImmediateRaw,
      Id.run, pure, Pure.pure, bind, Bind.bind]
    rw [h_raw]
    cases after.readScalar RuntimeTargetDataLayout.default.base
        (allocRange Size.ZERO _) false <;> rfl)

private theorem readImmediateFromMplaceRaw_bool_at (types : List MirTy)
    (off : Size)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_acc :
      let mem :=
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      Miri.Interpreter.getPlaceAlloc mem ⟨machine, none⟩
          ⟨offMemPlace off, localMemoryLayout (refLocalLayoutForTy types .bool)⟩
          RuntimeTargetDataLayout.default true none
          cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
          cfg.dynamicLayout =
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange off (Size.ofBytes 1), after⟩,
          .ok (some ⟨retAllocId, allocRange off (Size.ofBytes 1), after⟩)⟩)
    (h_sub : (allocRange off (Size.ofBytes 1)).subrange
        (allocRange Size.ZERO (Size.ofBytes 1)) =
      .ok (allocRange off (Size.ofBytes 1))) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    Miri.Interpreter.readImmediateFromMplaceRaw mem ⟨machine, none⟩
        ⟨offMemPlace off, localMemoryLayout (refLocalLayoutForTy types .bool)⟩
        RuntimeTargetDataLayout.default true none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange off (Size.ofBytes 1)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange off (Size.ofBytes 1), after⟩,
          .ok (some ⟨.scalar sc,
            localMemoryLayout (refLocalLayoutForTy types .bool)⟩)⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange off (Size.ofBytes 1), after⟩,
          .error (.allocation err)⟩ := by
  intro mem
  dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run, pure,
    Pure.pure, bind, Bind.bind]
  rw [h_acc]
  dsimp only [localMemoryLayout, refLocalLayoutForTy, refLayoutDataForTy,
    refBoolLayoutData, refBaseLayoutData, Miri.ABI.BackendRepr.isUnsized]
  simp only [Bool.false_eq_true, ite_false]
  change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
    (Bind.bind (Except.mapError Miri.Interpreter.MemoryOperandError.memoryRange
        ((allocRange off (Size.ofBytes 1)).subrange
          (allocRange Size.ZERO (Size.ofBytes 1))))
      (fun range =>
        Except.mapError Miri.Interpreter.MemoryOperandError.allocation
          (after.readScalar RuntimeTargetDataLayout.default.base range false)))
    _ _ = _
  rw [h_sub]
  change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
    (Except.mapError Miri.Interpreter.MemoryOperandError.allocation
      (after.readScalar RuntimeTargetDataLayout.default.base
        (allocRange off (Size.ofBytes 1)) false)) _ _ = _
  cases after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange off (Size.ofBytes 1)) false <;> rfl

private theorem subrange_bool_at (w : IntWidth) :
    (allocRange (toMiriSize w) (Size.ofBytes 1)).subrange
        (allocRange Size.ZERO (Size.ofBytes 1)) =
      .ok (allocRange (toMiriSize w) (Size.ofBytes 1)) := by
  cases w <;> rfl

private theorem readImmediate_mem_pair_bool (types : List MirTy)
    (w : IntWidth)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_rt : cfg.runtime = Miri.ABI.RuntimeTargetDataLayout.default)
    (h_gk : cfg.globalKind = none)
    (h_res : cfg.resolvePointer = refResolvePointer)
    (h_gh : cfg.globalHooks = refGlobalAllocationHooks)
    (h_sz : after.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes)) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    Miri.Interpreter.readImmediate mem ⟨machine, none⟩
        (.indirect (offMemPlace (toMiriSize w)))
        (localMemoryLayout (refLocalLayoutForTy types .bool))
        cfg.runtime true cfg.globalKind cfg.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks cfg) cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange (toMiriSize w) (Size.ofBytes 1)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange (toMiriSize w) (Size.ofBytes 1), after⟩,
          .ok ⟨.scalar sc, localMemoryLayout (refLocalLayoutForTy types .bool)⟩⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange (toMiriSize w) (Size.ofBytes 1), after⟩,
          .error (.allocation err)⟩ := by
  intro mem
  have h_ptr := getPtrAlloc_off_ghost (toMiriSize w) (Size.ofBytes 1)
    (Size.ofBytes 1).bytes.toNat mem1 after machine cfg h_res h_gh
    rfl rfl
    (by rw [h_sz]; exact checkedBounds_pair_bool w)
  have h_acc := getPlaceAlloc_sized_of_access_poly mem ⟨machine, none⟩
    ⟨offMemPlace (toMiriSize w),
      localMemoryLayout (refLocalLayoutForTy types .bool)⟩
    true none cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
    cfg.dynamicLayout
    ⟨retAllocId, allocRange (toMiriSize w) (Size.ofBytes 1), after⟩
    rfl rfl h_ptr
  have h_raw := readImmediateFromMplaceRaw_bool_at types (toMiriSize w)
    mem1 after machine cfg h_acc (subrange_bool_at w)
  rw [h_rt, h_gk]
  dsimp only [Miri.Interpreter.readImmediate, Miri.Interpreter.readImmediateRaw,
    Id.run, pure, Pure.pure, bind, Bind.bind]
  rw [h_raw]
  cases after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange (toMiriSize w) (Size.ofBytes 1)) false <;> rfl
private theorem validityMemory_readImmediate_of_core_ok (types : List MirTy)
    (op : Operand Miri.Memory.Provenance) (layout : LocalLayout)
    (sc : Scalar Miri.Memory.Provenance) (expected : ExpectedValue)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (ref : Miri.Memory.AllocationAccessRef Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_core :
      Miri.Interpreter.readImmediate
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
        ⟨st.machine, none⟩ op (localMemoryLayout layout)
        refAccessConfig.runtime true none refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩, some ref,
        .ok ⟨.scalar sc, localMemoryLayout layout⟩⟩) :
    Miri.Interpreter.ValidityMemory.readImmediate refValidityMemoryEnv
        ⟨op, layout⟩ expected st =
      .ok ⟨.scalar sc, layout⟩ st := by
  let _ := types
  dsimp only [Miri.Interpreter.ValidityMemory.readImmediate,
    refValidityMemoryEnv, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_mem]
  rw [h_core]
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_mem
      subst h_mem
      rfl

private theorem validityMemory_readImmediate_of_core_uninit (types : List MirTy)
    (op : Operand Miri.Memory.Provenance) (layout : LocalLayout)
    (info : Option Miri.Memory.BadBytesAccess) (expected : ExpectedValue)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (ref : Miri.Memory.AllocationAccessRef Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_core :
      Miri.Interpreter.readImmediate
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
        ⟨st.machine, none⟩ op (localMemoryLayout layout)
        refAccessConfig.runtime true none refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩, some ref,
        .error (.allocation (.invalidUninitBytes info))⟩) :
    ∃ msg,
      Miri.Interpreter.ValidityMemory.readImmediate refValidityMemoryEnv
          ⟨op, layout⟩ expected st =
        .error (.undefinedBehavior msg) st := by
  let _ := types
  dsimp only [Miri.Interpreter.ValidityMemory.readImmediate,
    refValidityMemoryEnv, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_mem]
  rw [h_core]
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_mem
      subst h_mem
      exact ⟨_, rfl⟩

private theorem clearPlaceProvenance_mem_at (types : List MirTy)
    (c : Choice) (mplace : Miri.Interpreter.MemPlace Miri.Memory.Provenance)
    (layout : LocalLayout) (range : AllocRange)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_acc :
      Miri.Interpreter.getPlaceAllocMut
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
        ⟨st.machine, none⟩ ⟨mplace, localMemoryLayout layout⟩
        refAccessConfig.runtime true none refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, range, after⟩,
        .ok (some ⟨retAllocId, range, after⟩)⟩)
    (h_cp : Allocation.clearProvenance range (Size.ofBytes 8) after =
      .ok () after) :
    (refValHooks types).clearProvenance c ⟨.memory mplace, layout⟩ st =
      .ok () st := by
  have h_st_eq :
      ({ st with machine := { st.machine with
          memory :=
            { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
        } } :
        Miri.Interpreter.MachineHooks.State Unit RefUser) = st := by
    cases st with
    | mk stack machine =>
      cases machine with
      | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
          user pendingMoveDeinit =>
        dsimp only at h_mem
        subst h_mem
        rfl
  have h_env_acc :
      Miri.Interpreter.getPlaceAllocMut
        (refValidityMemoryEnv.memory st) (refValidityMemoryEnv.hooks st)
        ⟨mplace, localMemoryLayout layout⟩
        refValidityMemoryEnv.context.runtime true
        refValidityMemoryEnv.context.globalKind
        refValidityMemoryEnv.context.globalHooks
        refValidityMemoryEnv.context.accessHooks
        refValidityMemoryEnv.context.dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, range, after⟩,
        .ok (some ⟨retAllocId, range, after⟩)⟩ := by
    dsimp only [refValidityMemoryEnv]
    rw [h_mem]
    exact h_acc
  rw [refValHooks_clearProvenance]
  have h_res := clearPlaceProvenance_mem_step refValidityMemoryEnv
    (refBasePlaceProjectionHooks types).place
    c (fun st => .ok false st) (fun _ _ st => .ok () st)
    mplace layout st st
    { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    ⟨st.machine, none⟩
    ⟨retAllocId, range, after⟩
    h_env_acc h_st_eq (retAllocId, ⟨.stack, after⟩)
    (by
      dsimp only [refValidityMemoryEnv]; rw [h_mem]
      exact singleton_live_find ⟨.stack, after⟩)
    after h_cp { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    (by
      dsimp only [refValidityMemoryEnv]; rw [h_mem]
      exact singleton_setLiveAllocation mem1 after after)
  rw [h_res]
  dsimp only [refValidityMemoryEnv]
  rw [h_st_eq]

private theorem getPlaceAllocMut_off_ghost (off sz : Size) (signedSize : Int)
    (memLayout : Miri.Interpreter.MemoryOperandLayout)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (h_uns : memLayout.backendRepr.isUnsized = false)
    (h_lsz : memLayout.size = sz)
    (h_mut : alloc.mutability = .Mut)
    (h_sa : Miri.Memory.sizeAsI64 sz = .ok signedSize)
    (h_nz : (signedSize != 0) = true)
    (h_bounds : Miri.Memory.checkedBounds ⟨Size.ofBytes 8⟩ retAllocId
      alloc.byteSize off signedSize .memoryAccess = .ok ()) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Interpreter.getPlaceAllocMut mem ⟨machine, none⟩
        ⟨offMemPlace off, memLayout⟩ refAccessConfig.runtime true none
        refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId, allocRange off sz, alloc⟩,
        .ok (some ⟨retAllocId, allocRange off sz, alloc⟩)⟩ := by
  intro mem
  have h_ptr := getPtrAllocMut_off_ghost off sz signedSize mem1 alloc machine
    h_mut h_sa h_nz h_bounds
  exact getPlaceAllocMut_sized_of_access_poly mem ⟨machine, none⟩
    ⟨offMemPlace off, memLayout⟩ true none refAccessConfig.globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
    refAccessConfig.dynamicLayout
    ⟨retAllocId, allocRange off sz, alloc⟩
    h_uns rfl (by dsimp only; rw [h_lsz]; exact h_ptr)
private noncomputable def pairDataRange (w : IntWidth) :
    Miri.Memory.Validity.DataRangeSet :=
  match (singleDataRange w).addRange (toMiriSize w) (Size.ofBytes 1) with
  | .ok rs => rs
  | .error _ => .empty

private theorem visit_mem_pair_int_ok (types : List MirTy) (c : Choice)
    (fuel : Nat) (path : Miri.Memory.ValidationPath) (w : IntWidth) (s : Bool)
    (sc : Scalar Miri.Memory.Provenance)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types (.int w s)) = some (.int w s))
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes))
    (h_mut : after.mutability = .Mut)
    (h_rd : after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (toMiriSize w)) false = .ok sc)
    (h_cp : Allocation.clearProvenance (allocRange Size.ZERO (toMiriSize w))
      (Size.ofBytes 8) after = .ok () after) :
    let sess :
        Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := path, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := some .empty
    }
    Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
        sess ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩ st =
      .ok { sess with dataBytes := some (singleDataRange w) } st := by
  intro sess
  have h_core := readImmediate_mem_pair_int types w s mem1 after st.machine
    refAccessConfig rfl rfl rfl rfl h_sz
  rw [h_rd] at h_core
  have h_ri : (refValHooks types).readImmediate c
      ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩
      ExpectedValue.integer st =
      .ok ⟨.scalar sc, refLocalLayoutForTy types (.int w s)⟩ st := by
    rw [refValHooks_readImmediate]
    dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    exact validityMemory_readImmediate_of_core_ok types (.indirect retMemPlace)
      (refLocalLayoutForTy types (.int w s)) sc ExpectedValue.integer mem1 after
      ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩ st h_mem h_core
  have h_acc := getPlaceAllocMut_off_ghost Size.ZERO (toMiriSize w)
    (toMiriSize w).bytes.toNat
    (localMemoryLayout (refLocalLayoutForTy types (.int w s)))
    mem1 after st.machine (by cases w <;> cases s <;> rfl) rfl h_mut
    (sizeAsI64_toMiriSize w) (by cases w <;> decide)
    (by rw [h_sz]; exact checkedBounds_pair_int w)
  have h_clr := clearPlaceProvenance_mem_at types c retMemPlace
    (refLocalLayoutForTy types (.int w s)) (allocRange Size.ZERO (toMiriSize w))
    mem1 after st h_mem h_acc h_cp
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind,
    EStateM.bind]
  rw [mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind ((refValHooks types).readImmediate c
    ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩
    ExpectedValue.integer) _) _ st) = _
  rw [eStateM_bind_bind_ok h_ri]
  change (EStateM.bind (EStateM.bind (EStateM.pure sc) _) _ st) = _
  dsimp only [EStateM.bind, EStateM.pure, bind, Bind.bind, pure, Pure.pure]
  have h_ib :
      (Miri.Interpreter.ValidityVisitor.TypeKind.integer == .boolean) =
        false := rfl
  have h_ic :
      (Miri.Interpreter.ValidityVisitor.TypeKind.integer == .character) =
        false := rfl
  rw [h_ib, mem_ite_false_eq, h_ic, mem_ite_false_eq, mem_ite_true_eq]
  change (EStateM.bind (EStateM.bind ((refValHooks types).clearProvenance c
    ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩) _) _ st) = _
  rw [eStateM_bind_bind_ok h_clr]
  dsimp only [EStateM.bind, EStateM.pure, bind, Bind.bind, pure, Pure.pure,
    refValHooks_toOp, Miri.Interpreter.placeToOp,
    Miri.Interpreter.placeToOpCore, refLocalLayoutForTy, refLayoutDataForTy,
    refScalarLayoutData, refBaseLayoutData]
  cases w <;> rfl

private theorem visit_mem_pair_int_uninit_ub (types : List MirTy) (c : Choice)
    (fuel : Nat)
    (sess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (w : IntWidth) (s : Bool) (info : Option Miri.Memory.BadBytesAccess)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types (.int w s)) = some (.int w s))
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes))
    (h_rd : after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (toMiriSize w)) false =
      .error (.invalidUninitBytes info)) :
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
          sess ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩ st =
        .error (.undefinedBehavior msg) st := by
  have h_core := readImmediate_mem_pair_int types w s mem1 after st.machine
    refAccessConfig rfl rfl rfl rfl h_sz
  rw [h_rd] at h_core
  let ⟨msg, h_ri_raw⟩ := validityMemory_readImmediate_of_core_uninit types
    (.indirect retMemPlace) (refLocalLayoutForTy types (.int w s)) info
    ExpectedValue.integer mem1 after
    ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩ st h_mem h_core
  have h_ri : (refValHooks types).readImmediate c
      ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩
      ExpectedValue.integer st = .error (.undefinedBehavior msg) st := by
    rw [refValHooks_readImmediate]
    dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    exact h_ri_raw
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind,
    EStateM.bind]
  rw [mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind ((refValHooks types).readImmediate c
    ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩
    ExpectedValue.integer) _) _ st) = _
  rw [eStateM_bind_bind_err h_ri]

private theorem visit_mem_pair_bool_ok (types : List MirTy) (c : Choice)
    (fuel : Nat) (path : Miri.Memory.ValidationPath) (w : IntWidth) (b : Bool)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types .bool) = some .bool)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes))
    (h_mut : after.mutability = .Mut)
    (h_rd : after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange (toMiriSize w) (Size.ofBytes 1)) false = .ok (.fromBool b))
    (h_cp : Allocation.clearProvenance
      (allocRange (toMiriSize w) (Size.ofBytes 1))
      (Size.ofBytes 8) after = .ok () after) :
    let sess :
        Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := path, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := some (singleDataRange w)
    }
    Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
        sess ⟨.memory (offMemPlace (toMiriSize w)),
          refLocalLayoutForTy types .bool⟩
        st =
      .ok { sess with dataBytes := some (pairDataRange w) } st := by
  intro sess
  have h_core := readImmediate_mem_pair_bool types w mem1 after st.machine
    refAccessConfig rfl rfl rfl rfl h_sz
  rw [h_rd] at h_core
  have h_ri : (refValHooks types).readImmediate c
      ⟨.memory (offMemPlace (toMiriSize w)), refLocalLayoutForTy types .bool⟩
      ExpectedValue.boolean st =
      .ok ⟨.scalar (.fromBool b), refLocalLayoutForTy types .bool⟩ st := by
    rw [refValHooks_readImmediate]
    dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    exact validityMemory_readImmediate_of_core_ok types
      (.indirect (offMemPlace (toMiriSize w))) (refLocalLayoutForTy types .bool)
      (.fromBool b) ExpectedValue.boolean mem1 after
      ⟨retAllocId, allocRange (toMiriSize w) (Size.ofBytes 1), after⟩ st
      h_mem h_core
  have h_acc := getPlaceAllocMut_off_ghost (toMiriSize w) (Size.ofBytes 1)
    (Size.ofBytes 1).bytes.toNat
    (localMemoryLayout (refLocalLayoutForTy types .bool))
    mem1 after st.machine rfl rfl h_mut rfl rfl
    (by rw [h_sz]; exact checkedBounds_pair_bool w)
  have h_clr := clearPlaceProvenance_mem_at types c
    (offMemPlace (toMiriSize w)) (refLocalLayoutForTy types .bool)
    (allocRange (toMiriSize w) (Size.ofBytes 1)) mem1 after st h_mem h_acc h_cp
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind,
    EStateM.bind]
  rw [mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind ((refValHooks types).readImmediate c
    ⟨.memory (offMemPlace (toMiriSize w)), refLocalLayoutForTy types .bool⟩
    ExpectedValue.boolean) _) _ st) = _
  rw [eStateM_bind_bind_ok h_ri]
  change (EStateM.bind (EStateM.bind (EStateM.pure
    (Scalar.fromBool (Prov := Miri.Memory.Provenance) b)) _) _ st) = _
  dsimp only [EStateM.bind, EStateM.pure, bind, Bind.bind, pure, Pure.pure]
  have h_bb :
      (Miri.Interpreter.ValidityVisitor.TypeKind.boolean == .boolean) =
        true := rfl
  have h_bc :
      (Miri.Interpreter.ValidityVisitor.TypeKind.boolean == .character) =
        false := rfl
  rw [h_bb, mem_ite_true_eq]
  cases b <;> (
    dsimp only [EStateM.bind, EStateM.pure, bind, Bind.bind, pure, Pure.pure]
    rw [h_bc, mem_ite_false_eq, mem_ite_true_eq]
    change (EStateM.bind (EStateM.bind ((refValHooks types).clearProvenance c
      ⟨.memory (offMemPlace (toMiriSize w)),
        refLocalLayoutForTy types .bool⟩) _) _
      st) = _
    rw [eStateM_bind_bind_ok h_clr]
    cases w <;> rfl)

private theorem eStateM_bind_ok_trans {ε σ α β : Type} {m : EStateM ε σ α}
    {f : α → EStateM ε σ β} {a : α} {st st' : σ} {r : EStateM.Result ε σ β}
    (h1 : m st = .ok a st') (h2 : f a st' = r) :
    EStateM.bind m f st = r := by
  dsimp only [EStateM.bind]
  rw [h1]
  exact h2

private theorem eStateM_bind_bind_ok_trans {ε σ α β γ : Type}
    {m : EStateM ε σ α}
    {f : α → EStateM ε σ β} {g : β → EStateM ε σ γ} {a : α} {st st' : σ}
    {r : EStateM.Result ε σ γ}
    (h1 : m st = .ok a st') (h2 : EStateM.bind (f a) g st' = r) :
    EStateM.bind (EStateM.bind m f) g st = r := by
  dsimp only [EStateM.bind]
  rw [h1]
  exact h2

private theorem forIn_singleton_yield {ε σ α β : Type} {x : α} {init b : β}
    {f : α → β → EStateM ε σ (ForInStep β)} {st st' : σ}
    (h : f x init st = .ok (.yield b) st') :
    forIn ((Array.mk [x]) : Array α) init f st = .ok b st' := by
  rw [forIn_singleton_array, h]

private theorem beginPadding_pair (types : List MirTy) (c : Choice)
    (w : IntWidth) (s : Bool)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes))
    (h_mut : after.mutability = .Mut) :
    (refValHooks types).beginPadding c
        ⟨retMemPlace, refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩
        (Size.ofBytes (2 * (toMiriSize w).bytes)) st =
      .ok (some ⟨retAllocId, allocRange Size.ZERO
        (Size.ofBytes (2 * (toMiriSize w).bytes))⟩) st := by
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_mem
      subst h_mem
      cases after
      dsimp only [Allocation.byteSize] at h_sz
      dsimp only at h_mut
      subst h_sz h_mut
      cases w <;> rfl

private theorem writePadding_retAlloc (types : List MirTy) (c : Choice)
    (hr rel abs : AllocRange)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after after2 : Allocation Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sub : hr.subrange rel = .ok abs)
    (h_wu : Allocation.writeUninit abs (Size.ofBytes 8) after = .ok () after2) :
    (refValHooks types).writePadding c ⟨retAllocId, hr⟩ rel st =
      .ok () { st with machine := { st.machine with
        memory := { mem1 with
          live := (Array.mk [(retAllocId, ⟨.stack, after2⟩)]) } } } := by
  change Miri.Interpreter.ValidityMemory.writePadding refValidityMemoryEnv
    ⟨retAllocId, hr⟩ rel st = _
  dsimp only [Miri.Interpreter.ValidityMemory.writePadding, bind, Bind.bind,
    EStateM.bind]
  rw [h_sub]
  change (match (EStateM.Result.ok abs st : EStateM.Result StepError
      (Miri.Interpreter.MachineHooks.State Unit RefUser) AllocRange) with
    | EStateM.Result.ok a s => _
    | EStateM.Result.error e s => EStateM.Result.error e s) = _
  dsimp only
  change (EStateM.bind get (fun state => _) st) = _
  dsimp only [get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind]
  have h_wu' : Allocation.writeUninit abs
      refValidityMemoryEnv.context.runtime.pointerSize after = .ok () after2 :=
    h_wu
  dsimp only [refValidityMemoryEnv] at h_wu'
  dsimp only [refValidityMemoryEnv]
  rw [h_mem, singleton_live_find]
  dsimp only
  rw [h_wu', singleton_setLiveAllocation]
  rfl

private theorem subrange_pairPad (w : IntWidth) :
    (allocRange Size.ZERO (Size.ofBytes (2 * (toMiriSize w).bytes))).subrange
        (pairPadRange w) = .ok (pairPadRange w) := by
  cases w <;> rfl

private theorem validatePlace_mem_pair_step_i8 (types : List MirTy) (c : Choice)
    (s : Bool) (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_vis :
      let initSess :
          Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
        path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := some .empty
      }
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c 8
        initSess ⟨.memory retMemPlace,
          refLocalLayoutForTy types (.tuple [.int .i8 s, .bool])⟩ st =
        .ok { initSess with dataBytes := some (pairDataRange .i8) } st) :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooks types) c 8
        ⟨.memory retMemPlace,
          refLocalLayoutForTy types (.tuple [.int .i8 s, .bool])⟩
        false true st = .ok () st := by
  dsimp only [Miri.Interpreter.ValidityVisitor.validatePlace, bind, Bind.bind]
  refine eStateM_bind_ok_trans (refValHooks_typeName types c _ st) ?_
  change EStateM.bind _ _ st = _
  rw [refValHooks_withGhostValidation, mem_ite_true_eq]
  refine eStateM_bind_bind_ok_trans (a := ⟨.indirect retMemPlace,
    refLocalLayoutForTy types (.tuple [.int .i8 s, .bool])⟩) (st' := st) rfl ?_
  change EStateM.bind (EStateM.bind _ _) _ st = _
  refine eStateM_bind_bind_ok_trans h_vis ?_
  change EStateM.bind (EStateM.bind _ _) _ st = _
  refine eStateM_bind_bind_ok_trans (a := ()) (st' := st) ?_ ?_
  · rfl
  · rfl

private theorem validatePlace_mem_pair_step_wide (types : List MirTy)
    (c : Choice)
    (w : IntWidth) (s : Bool) (h_ne : w ≠ .i8)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after after2 : Allocation Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes))
    (h_mut : after.mutability = .Mut)
    (h_pad : Allocation.writeUninit (pairPadRange w) (Size.ofBytes 8) after =
      .ok () after2)
    (h_vis :
      let initSess :
          Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
        path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := some .empty
      }
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c 8
        initSess ⟨.memory retMemPlace,
          refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ st =
        .ok { initSess with dataBytes := some (pairDataRange w) } st) :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooks types) c 8
        ⟨.memory retMemPlace,
          refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩
        false true st =
      .ok () { st with machine := { st.machine with
        memory := { mem1 with
          live := (Array.mk [(retAllocId, ⟨.stack, after2⟩)]) } } } := by
  have h_bp := beginPadding_pair types c w s mem1 after st h_mem h_sz h_mut
  have h_wp : ∀ r, r = pairPadRange w →
      (refValHooks types).writePadding c ⟨retAllocId,
        allocRange Size.ZERO (Size.ofBytes (2 * (toMiriSize w).bytes))⟩ r st =
      .ok () { st with machine := { st.machine with
        memory := { mem1 with
          live := (Array.mk [(retAllocId, ⟨.stack, after2⟩)]) } } } := by
    intro r hr
    subst hr
    exact writePadding_retAlloc types c _ _ _ mem1 after after2 st h_mem
      (subrange_pairPad w) h_pad
  dsimp only [Miri.Interpreter.ValidityVisitor.validatePlace, bind, Bind.bind]
  refine eStateM_bind_ok_trans (refValHooks_typeName types c _ st) ?_
  change EStateM.bind _ _ st = _
  rw [refValHooks_withGhostValidation, mem_ite_true_eq]
  refine eStateM_bind_bind_ok_trans (a := ⟨.indirect retMemPlace,
    refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩) (st' := st) rfl ?_
  change EStateM.bind (EStateM.bind _ _) _ st = _
  refine eStateM_bind_bind_ok_trans h_vis ?_
  change EStateM.bind (EStateM.bind _ _) _ st = _
  refine eStateM_bind_bind_ok_trans (a := ())
    (st' := { st with machine := { st.machine with
      memory := { mem1 with
        live := (Array.mk [(retAllocId, ⟨.stack, after2⟩)]) } } }) ?_ rfl
  change (EStateM.bind (Miri.Interpreter.forceAllocation
      (refValHooks types).projection.place c
      ⟨.memory retMemPlace,
        refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩)
    (fun memory => _) st) = _
  refine eStateM_bind_ok_trans
    (a := ⟨retMemPlace, refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩)
    (st' := st) rfl ?_
  change EStateM.bind _ _ st = _
  refine eStateM_bind_ok_trans
    (a := ⟨retMemPlace, refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩)
    (st' := st) rfl ?_
  change EStateM.bind _ _ st = _
  refine eStateM_bind_ok_trans
    (a := some
      ((refLocalLayoutForTy types (.tuple [.int w s, .bool])).layout.size,
      (refLocalLayoutForTy types (.tuple [.int w s, .bool])).layout.align.abi))
    (st' := st) rfl ?_
  cases w with
  | i8 => exact absurd rfl h_ne
  | i16 | i32 | i64 | i128 | isize =>
    change EStateM.bind _ _ st = _
    refine eStateM_bind_ok_trans h_bp ?_
    change EStateM.bind _ _ st = _
    dsimp only [refLocalLayoutForTy, refLayoutDataForTy,
      refOverflowPairLayoutData, refBaseLayoutData, Option.getD, retMemPlace,
      retPtr, toMiriSize]
    refine eStateM_bind_ok_trans (a := _) (st' := st) rfl ?_
    change EStateM.bind _ _ st = _
    refine eStateM_bind_ok_trans (a := PUnit.unit) ?_ rfl
    refine forIn_singleton_yield ?_
    change EStateM.bind _ _ st = _
    exact eStateM_bind_ok_trans (h_wp _ rfl) rfl
private theorem placeDynamic_field_pair0 (types : List MirTy) (c : Choice)
    (w : IntWidth) (s : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types (.tuple [.int w s, .bool])) =
      some (.tuple [.int w s, .bool])) :
    Miri.Interpreter.PlaceDynamic.field (refBasePlaceProjectionHooks types) c
        ⟨.memory retMemPlace,
          refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩
        0 st =
      .ok ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩ st := by
  have h_fo : (refLocalLayoutForTy types
      (.tuple [.int w s, .bool])).layout.fields.offset 0 = .ok Size.ZERO := rfl
  have h_fl : (refBasePlaceProjectionHooks types).field c
      (refLocalLayoutForTy types (.tuple [.int w s, .bool])) 0 st =
      .ok (refLocalLayoutForTy types (.int w s)) st := by
    dsimp only [refBasePlaceProjectionHooks, refProjectFieldLayout,
      refLocalLayoutForTy]
    rw [h_res]
    rfl
  have h_sz : (refLocalLayoutForTy types (.int w s)).layout.isSized = true :=
    refLayoutDataForTy_isSized (.int w s)
  dsimp only [Miri.Interpreter.PlaceDynamic.field, bind, Bind.bind,
    EStateM.bind]
  rw [h_fo]
  change (EStateM.bind ((refBasePlaceProjectionHooks types).field c
    (refLocalLayoutForTy types (.tuple [.int w s, .bool])) 0) _ st) = _
  rw [mem_eStateM_bind_ok h_fl]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_sz, mem_ite_not_true_eq]
  dsimp only [Miri.Interpreter.PlaceDynamic.offsetWithMeta,
    refBasePlaceProjectionHooks, Miri.Interpreter.PlaceMachine.placeHooks,
    refBaseCompilerHooks, bind, Bind.bind, EStateM.bind, pure, Pure.pure,
    EStateM.pure]
  rw [placeMemoryOffset_retPlace_zero]

private theorem placeMemoryOffset_retPlace_pair (w : IntWidth)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_sz : after.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes)) :
    Miri.Interpreter.placeMemoryOffset refPointerArithmetic
        refResolvePointerPure
        ({ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) } :
          Miri.Memory.MemoryState Miri.Memory.Provenance
            Miri.TreeBorrows.BorrowTree Unit).getAllocInfo
        retMemPlace (toMiriSize w) .inbounds .none st =
      .ok (offMemPlace (toMiriSize w)) st := by
  cases after
  dsimp only [Allocation.byteSize] at h_sz
  subst h_sz
  cases w <;> rfl

private theorem placeDynamic_field_pair1 (types : List MirTy) (c : Choice)
    (w : IntWidth) (s : Bool)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes))
    (h_res : resolveTy types (tyIdFor types (.tuple [.int w s, .bool])) =
      some (.tuple [.int w s, .bool])) :
    Miri.Interpreter.PlaceDynamic.field (refBasePlaceProjectionHooks types) c
        ⟨.memory retMemPlace,
          refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩
        1 st =
      .ok ⟨.memory (offMemPlace (toMiriSize w)),
          refLocalLayoutForTy types .bool⟩
        st := by
  have h_fo : (refLocalLayoutForTy types
      (.tuple [.int w s, .bool])).layout.fields.offset 1 =
      .ok (toMiriSize w) := rfl
  have h_fl : (refBasePlaceProjectionHooks types).field c
      (refLocalLayoutForTy types (.tuple [.int w s, .bool])) 1 st =
      .ok (refLocalLayoutForTy types .bool) st := by
    dsimp only [refBasePlaceProjectionHooks, refProjectFieldLayout,
      refLocalLayoutForTy]
    rw [h_res]
    rfl
  have h_sz' : (refLocalLayoutForTy types .bool).layout.isSized = true :=
    refLayoutDataForTy_isSized .bool
  dsimp only [Miri.Interpreter.PlaceDynamic.field, bind, Bind.bind,
    EStateM.bind]
  rw [h_fo]
  change (EStateM.bind ((refBasePlaceProjectionHooks types).field c
    (refLocalLayoutForTy types (.tuple [.int w s, .bool])) 1) _ st) = _
  rw [mem_eStateM_bind_ok h_fl]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_sz', mem_ite_not_true_eq]
  dsimp only [Miri.Interpreter.PlaceDynamic.offsetWithMeta,
    refBasePlaceProjectionHooks, Miri.Interpreter.PlaceMachine.placeHooks,
    refBaseCompilerHooks, bind, Bind.bind, EStateM.bind, pure, Pure.pure,
    EStateM.pure]
  rw [h_mem, placeMemoryOffset_retPlace_pair w mem1 after st h_sz]
private theorem visit_mem_pair_ok (types : List MirTy) (c : Choice)
    (fuel k : Nat) (h_fuel : fuel = k + 1)
    (w : IntWidth) (s : Bool) (bits : BitVec 128) (b : Bool)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types (.tuple [.int w s, .bool])) =
      some (.tuple [.int w s, .bool]))
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_rd : PairAllocReads w bits b after) :
    let initSess :
        Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := some .empty
    }
    Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
        initSess ⟨.memory retMemPlace,
          refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ st =
      .ok { initSess with dataBytes := some (pairDataRange w) } st := by
  intro initSess
  let ⟨h_ri, h_rb, h_ci, h_cb, h_sz, h_mut, _⟩ := h_rd
  have h_ne_box :
      (Miri.Interpreter.ValidityVisitor.TypeKind.aggregate false false false ==
        .box) = false := rfl
  have h_fields : (refLocalLayoutForTy types
      (.tuple [.int w s, .bool])).layout.fields =
      .Arbitrary (Array.mk [Size.ZERO, toMiriSize w]) (Array.mk [0, 1]) := rfl
  have h_vars : (refLocalLayoutForTy types
      (.tuple [.int w s, .bool])).layout.variants = .Single 0 := rfl
  have h_f0 := placeDynamic_field_pair0 types c w s st h_res
  have h_f1 :=
    placeDynamic_field_pair1 types c w s mem1 after st h_mem h_sz h_res
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind,
    EStateM.bind]
  rw [mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (match (EStateM.Result.ok none st :
      EStateM.Result StepError
        (Miri.Interpreter.MachineHooks.State Unit RefUser)
        (Option (Miri.Interpreter.ValidityVisitor.Session
          Miri.Memory.Provenance))) with
    | EStateM.Result.ok a s => _
    | EStateM.Result.error e s => EStateM.Result.error e s) = _
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ne_box, mem_ite_false_eq, h_fields, h_vars]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [forIn_pair_array]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [refValHooks_projection, h_f0]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [refValHooks_fieldPath]
  dsimp only [bind, Bind.bind, EStateM.bind, initSess, Bool.or]
  rw [h_fuel]
  rw [visit_mem_pair_int_ok types c k
    ({ originalType := "" : Miri.Memory.ValidationPath }.push .enumTag) w s
    (.fromScalarInt (miriScalar w bits)) mem1 after st
    (mem_resolveTy_tyIdFor_int types w s) h_mem h_sz h_mut h_ri h_ci]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_f1]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [refValHooks_fieldPath]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [visit_mem_pair_bool_ok types c k
    ({ originalType := "" : Miri.Memory.ValidationPath }.push .enumTag) w b
    mem1 after st (resolveTy_tyIdFor_of_aux rfl) h_mem h_sz h_mut h_rb h_cb]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_opsemInhabited, h_res]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [mem_ite_true_eq, refValHooks_debugAssertions, mem_ite_false_eq]
  rfl
private theorem writeMemory_retPlace_pair_uninit (types : List MirTy)
    (w : IntWidth) (s : Bool)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (Size.ofBytes (2 * (toMiriSize w).bytes)) Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, rawAlloc.withExtra
          (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
            (Size.ofBytes (2 * (toMiriSize w).bytes)))⟩)]) })
    (h_dr : st.machine.dataRace = none) :
    ∃ after info,
      let mem' :=
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      Miri.Interpreter.PlaceMachine.writeMemory refAccessConfig (fun _ => true)
          .uninit
          ⟨retMemPlace,
            refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ st =
        .ok () { st with machine := { st.machine with memory := mem' } } ∧
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false =
        .error (.invalidUninitBytes info) ∧
      after.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes) ∧
      after.mutability = .Mut := by
  let ⟨_, h_raw_eq, h_rsz, _, _, h_rmut, _⟩ :=
    Allocation.tryNew_replicate_full (P := Miri.Memory.Provenance)
      (Size.ofBytes (2 * (toMiriSize w).bytes)) Align.ONE 1 (by decide)
      (by decide)
  rw [h_raw] at h_raw_eq
  injection h_raw_eq with h_raw_id
  subst h_raw_id
  let alloc := rawAlloc.withExtra (Miri.TreeBorrows.BorrowTree.new
    Miri.Memory.BorTag.one (Size.ofBytes (2 * (toMiriSize w).bytes)))
  let ⟨after, info, h_wu, h_rd, h_asz, h_amut, _⟩ :=
    tryNew_pair_writeUninit w h_raw
  let place : Miri.Interpreter.MemoryOperandPlace Miri.Memory.Provenance :=
    ⟨retMemPlace, localMemoryLayout (refLocalLayoutForTy types
      (.tuple [.int w s, .bool]))⟩
  have h_uns : place.layout.backendRepr.isUnsized = false := rfl
  have h_ptr_acc := getPtrAllocMut_pair_nonGhost w mem1 alloc st.machine
    h_rsz h_rmut rfl h_dr
  have h_place_acc :
      Miri.Interpreter.getPlaceAllocMut
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
        ⟨st.machine, none⟩ place
        refAccessConfig.runtime false none refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId,
          allocRange Size.ZERO (Size.ofBytes (2 * (toMiriSize w).bytes)),
          alloc⟩,
        .ok (some ⟨retAllocId,
          allocRange Size.ZERO (Size.ofBytes (2 * (toMiriSize w).bytes)),
          alloc⟩)⟩ :=
    Miri.Interpreter.getPlaceAllocMut_sized_of_access _ _ _ _
      (Size.ofBytes 8) none _ _ _ _ h_uns rfl rfl h_ptr_acc
  have h_wm_op :
      Miri.Interpreter.writeImmediateToMplaceNoValidate
        st.machine.memory ⟨st.machine, none⟩ .uninit place
        refAccessConfig.runtime refAccessConfig.ghostMode
        refAccessConfig.globalKind refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout (fun _ => true) =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId,
          allocRange Size.ZERO (Size.ofBytes (2 * (toMiriSize w).bytes)),
          after⟩,
        .ok ()⟩ := by
    rw [h_mem]
    refine writeUninit_of_access_poly
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      ⟨st.machine, none⟩ place
      refAccessConfig.runtime refAccessConfig.ghostMode
      refAccessConfig.globalKind refAccessConfig.globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
      refAccessConfig.dynamicLayout (fun _ => true)
      ⟨retAllocId,
        allocRange Size.ZERO (Size.ofBytes (2 * (toMiriSize w).bytes)), alloc⟩
      after h_uns ?_ h_wu (singleton_setLiveAllocation mem1 alloc after)
    exact h_place_acc
  exact ⟨after, info,
    Miri.Interpreter.PlaceMachine.writeMemory_of_result refAccessConfig
      (fun _ => true) .uninit
      ⟨retMemPlace, refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ st
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      _ rfl h_wm_op,
    h_rd, h_asz, h_amut⟩

private theorem visit_mem_pair_uninit_ub (types : List MirTy) (c : Choice)
    (fuel k : Nat) (h_fuel : fuel = k + 1)
    (w : IntWidth) (s : Bool) (info : Option Miri.Memory.BadBytesAccess)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types (.tuple [.int w s, .bool])) =
      some (.tuple [.int w s, .bool]))
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = Size.ofBytes (2 * (toMiriSize w).bytes))
    (h_rd : after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (toMiriSize w)) false =
      .error (.invalidUninitBytes info)) :
    let initSess :
        Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := some .empty
    }
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
          initSess ⟨.memory retMemPlace,
            refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ st =
        .error (.undefinedBehavior msg) st := by
  intro initSess
  have h_ne_box :
      (Miri.Interpreter.ValidityVisitor.TypeKind.aggregate false false false ==
        .box) = false := rfl
  have h_fields : (refLocalLayoutForTy types
      (.tuple [.int w s, .bool])).layout.fields =
      .Arbitrary (Array.mk [Size.ZERO, toMiriSize w]) (Array.mk [0, 1]) := rfl
  have h_f0 := placeDynamic_field_pair0 types c w s st h_res
  let ⟨msg, h_v0⟩ := visit_mem_pair_int_uninit_ub types c k
    { path := { originalType := "" : Miri.Memory.ValidationPath }.push .enumTag,
      flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := some .empty }
    w s info mem1 after st (mem_resolveTy_tyIdFor_int types w s) h_mem h_sz h_rd
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind,
    EStateM.bind]
  rw [mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (match (EStateM.Result.ok none st :
      EStateM.Result StepError
        (Miri.Interpreter.MachineHooks.State Unit RefUser)
        (Option (Miri.Interpreter.ValidityVisitor.Session
          Miri.Memory.Provenance))) with
    | EStateM.Result.ok a s => _
    | EStateM.Result.error e s => EStateM.Result.error e s) = _
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ne_box, mem_ite_false_eq, h_fields]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [forIn_pair_array]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [refValHooks_projection, h_f0]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [refValHooks_fieldPath]
  dsimp only [bind, Bind.bind, EStateM.bind, initSess, Bool.or]
  rw [h_fuel, h_v0]

private theorem refReadReturnVal_pair (types : List MirTy) (w : IntWidth)
    (s : Bool) (bits : BitVec 128) (b : Bool)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (a : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (h_rd : PairAllocReads w bits b a)
    (h_trunc : truncateBits w bits = bits) :
    refReadReturnVal
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, a⟩)]) }
        (.tuple [.int w s, .bool])
        ⟨retMemPlace, refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ =
      .ok (.tuple [.scalar ⟨w, s, bits⟩, .bool b]) := by
  let ⟨h_ri, h_rb, _⟩ := h_rd
  dsimp only [refReadReturnVal, retMemPlace, retPtr]
  rw [singleton_live_find]
  dsimp only
  rw [h_ri]
  dsimp only
  rw [scalar_tryToScalarInt_fromScalarInt]
  dsimp only
  rw [h_rb, miriScalar_data, h_trunc]
  cases b <;> rfl
/-- Executing `copyRuntimePlace` of an initialized overflow-pair immediate into
the fresh `2 * w`-byte return allocation succeeds, updates only
`st.machine.memory`, and `refReadReturnVal` reads the pair back. -/
theorem copyReturn_pair_ok (rp : MiriProg) (c : Choice) (w : IntWidth)
    (s : Bool) (bits : BitVec 128) (b : Bool)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (refLocalLayoutForTy rp.types (.tuple [.int w s, .bool])).layout.size
      Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, rawAlloc.withExtra
          (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
            (refLocalLayoutForTy rp.types
              (.tuple [.int w s, .bool])).layout.size)⟩)]) })
    (h_dr : st.machine.dataRace = none)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_trunc : truncateBits w bits = bits)
    (h_res : resolveTy rp.types (tyIdFor rp.types (.tuple [.int w s, .bool])) =
      some (.tuple [.int w s, .bool])) :
    let h := Miri.Interpreter.ExecutionMachine.withValidation
      (refExecutionConfig rp) refLimits
    ∃ mem',
      Miri.Interpreter.copyRuntimePlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
          ⟨.immediate (valToMiriImmediate (.tuple [.int w s, .bool])
              (.tuple [.scalar ⟨w, s, bits⟩, .bool b])),
            refLocalLayoutForTy rp.types (.tuple [.int w s, .bool])⟩
          ⟨.memory retMemPlace,
            refLocalLayoutForTy rp.types (.tuple [.int w s, .bool])⟩ true st =
        .ok () { st with machine := { st.machine with memory := mem' } } ∧
      refReadReturnVal mem' (.tuple [.int w s, .bool])
          ⟨retMemPlace,
            refLocalLayoutForTy rp.types (.tuple [.int w s, .bool])⟩ =
        .ok (.tuple [.scalar ⟨w, s, bits⟩, .bool b]) := by
  intro h
  let ⟨after, after2, h_wm, h_pad, h_rd1, h_rd2⟩ :=
    writeMemory_retPlace_pair rp.types w s bits b mem1 st h_raw h_mem h_dr
  let ⟨_, _, _, _, h_asz, h_amut, _⟩ := h_rd1
  let mem1' : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit :=
    { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
  let st1 := { st with machine := { st.machine with memory := mem1' } }
  have h_vis := visit_mem_pair_ok rp.types c 7 6 rfl w s bits b mem1 after st1
    h_res rfl h_rd1
  cases w with
  | i8 =>
    exact ⟨mem1',
      copyRuntimePlace_imm_to_mem_step rp c _ _ retMemPlace st st1 _ h_pmd h_wm
        (validatePlace_mem_pair_step_i8 rp.types c s st1 h_vis),
      refReadReturnVal_pair rp.types .i8 s bits b mem1 after h_rd1 h_trunc⟩
  | i16 | i32 | i64 | i128 | isize =>
    refine ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after2⟩)]) },
      ?_, refReadReturnVal_pair rp.types _ s bits b mem1 after2 h_rd2 h_trunc⟩
    have h_val := validatePlace_mem_pair_step_wide rp.types c _ s
      (by intro h_eq; cases h_eq) mem1 after after2 st1 rfl h_asz h_amut h_pad
      h_vis
    exact copyRuntimePlace_imm_to_mem_step rp c _ _ retMemPlace st st1 _ h_pmd
      h_wm h_val

/-- Executing `copyRuntimePlace` of an uninitialized overflow-pair immediate
into the fresh return allocation fails with `.undefinedBehavior`. -/
theorem copyReturn_pair_uninit_ub (rp : MiriProg) (c : Choice)
    (w : IntWidth) (s : Bool)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (refLocalLayoutForTy rp.types (.tuple [.int w s, .bool])).layout.size
      Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, rawAlloc.withExtra
          (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
            (refLocalLayoutForTy rp.types
              (.tuple [.int w s, .bool])).layout.size)⟩)]) })
    (h_dr : st.machine.dataRace = none)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_res : resolveTy rp.types (tyIdFor rp.types (.tuple [.int w s, .bool])) =
      some (.tuple [.int w s, .bool])) :
    let h := Miri.Interpreter.ExecutionMachine.withValidation
      (refExecutionConfig rp) refLimits
    ∃ msg st',
      Miri.Interpreter.copyRuntimePlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
          ⟨.immediate .uninit,
            refLocalLayoutForTy rp.types (.tuple [.int w s, .bool])⟩
          ⟨.memory retMemPlace,
            refLocalLayoutForTy rp.types (.tuple [.int w s, .bool])⟩ true st =
        .error (.undefinedBehavior msg) st' := by
  intro h
  let ⟨after, info, h_wm, h_rd, h_asz, _⟩ :=
    writeMemory_retPlace_pair_uninit rp.types w s mem1 st h_raw h_mem h_dr
  let mem1' : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit :=
    { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
  let st1 := { st with machine := { st.machine with memory := mem1' } }
  let ⟨msg, h_vis⟩ := visit_mem_pair_uninit_ub rp.types c 7 6 rfl w s info
    mem1 after st1 h_res rfl h_asz h_rd
  exact ⟨msg, st1,
    copyRuntimePlace_imm_to_mem_step rp c _ _ retMemPlace st st1 _ h_pmd h_wm
      (validatePlace_mem_ub_step rp.types c _ st1 st1 msg h_vis)⟩

end Anneal.MirCorrespondence
