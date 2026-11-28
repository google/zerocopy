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
import Anneal.MirCorrespondence.ScalarEquiv
import Anneal.MirCorrespondence.EnumEquiv

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Miri.ABI Miri.Memory Miri.Interpreter

/-! ## Section 1: Inductive Big-Endian Byte Encoding/Decoding -/

theorem nat_mod_mul_decomp (x a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    HMod.hMod x a + HMod.hMod (HDiv.hDiv x a) b * a = HMod.hMod x (a * b) := by
  have h_div : HDiv.hDiv x a = b * HDiv.hDiv (HDiv.hDiv x a) b + HMod.hMod (HDiv.hDiv x a) b :=
    (Nat.div_add_mod (HDiv.hDiv x a) b).symm
  have h_x : x = a * HDiv.hDiv x a + HMod.hMod x a := (Nat.div_add_mod x a).symm
  have h_mul_div : a * HDiv.hDiv x a =
      (a * b) * HDiv.hDiv (HDiv.hDiv x a) b + HMod.hMod (HDiv.hDiv x a) b * a := by
    have h1 := congrArg (fun k => a * k) h_div
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm a (HMod.hMod (HDiv.hDiv x a) b)] at h1
    exact h1
  have h_expand :
      x = (a * b) * HDiv.hDiv (HDiv.hDiv x a) b +
        (HMod.hMod x a + HMod.hMod (HDiv.hDiv x a) b * a) := by
    have h2 : a * HDiv.hDiv x a + HMod.hMod x a =
        (a * b) * HDiv.hDiv (HDiv.hDiv x a) b +
          (HMod.hMod x a + HMod.hMod (HDiv.hDiv x a) b * a) := by
      rw [h_mul_div, Nat.add_assoc,
        Nat.add_comm (HMod.hMod (HDiv.hDiv x a) b * a) (HMod.hMod x a)]
    exact h_x.trans h2
  have h_r_lt : HMod.hMod x a + HMod.hMod (HDiv.hDiv x a) b * a < a * b := by
    have h1 : HMod.hMod x a < a := Nat.mod_lt x ha
    have h2 : HMod.hMod (HDiv.hDiv x a) b < b := Nat.mod_lt (HDiv.hDiv x a) hb
    have h3 : HMod.hMod (HDiv.hDiv x a) b + 1 ≤ b := h2
    have h4 : (HMod.hMod (HDiv.hDiv x a) b + 1) * a ≤ b * a := Nat.mul_le_mul_right a h3
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm b a] at h4
    have h5 : HMod.hMod x a + HMod.hMod (HDiv.hDiv x a) b * a <
        a + HMod.hMod (HDiv.hDiv x a) b * a :=
      Nat.add_lt_add_right h1 (HMod.hMod (HDiv.hDiv x a) b * a)
    rw [Nat.add_comm a (HMod.hMod (HDiv.hDiv x a) b * a)] at h5
    exact Nat.lt_of_lt_of_le h5 h4
  have h_mod := congrArg (fun n => HMod.hMod n (a * b)) h_expand
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h_r_lt] at h_mod
  exact h_mod.symm

theorem u8_ofNat_toNat_mod (n : Nat) :
    (UInt8.ofNat (HMod.hMod n 256)).toNat = HMod.hMod n 256 := by
  have h_lt : HMod.hMod n 256 < 256 := Nat.mod_lt n (by decide)
  change HMod.hMod (HMod.hMod n 256) 256 = HMod.hMod n 256
  exact Nat.mod_eq_of_lt h_lt

private theorem pow2_pos (k : Nat) : 0 < HPow.hPow (2 : Nat) k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    exact Nat.mul_pos ih (by decide)

noncomputable def beBytes (x n : Nat) : Nat → Array UInt8
  | 0 => Array.mk []
  | k + 1 =>
    (beBytes x n k).push (UInt8.ofNat (HMod.hMod (HDiv.hDiv x (HPow.hPow 2 (8 * (n - k - 1)))) 256))

theorem beBytes_size (x n : Nat) : ∀ k, (beBytes x n k).size = k
  | 0 => rfl
  | k + 1 => by
    dsimp only [beBytes]
    rw [Array.size_push, beBytes_size x n k]

theorem beBytes_getElem? (x n : Nat) :
    ∀ k i, i < k →
      (beBytes x n k)[i]? =
        some (UInt8.ofNat (HMod.hMod (HDiv.hDiv x (HPow.hPow 2 (8 * (n - i - 1)))) 256))
  | 0, _, h => False.elim (Nat.not_lt_zero _ h)
  | k + 1, i, hi => by
    dsimp only [beBytes]
    rw [Array.getElem?_push, beBytes_size x n k]
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with
    | inl hlt =>
      rw [ite_eq_right (Nat.ne_of_lt hlt)]
      exact beBytes_getElem? x n k i hlt
    | inr heq =>
      subst heq
      rw [ite_eq_left rfl]

private theorem list_range'_succ_end (n : Nat) :
    List.range' 0 (n + 1) 1 = List.range' 0 n 1 ++ [n] := by
  have h : List.range' 0 n 1 ++ List.range' (0 + 1 * n) 1 1 =
      List.range' 0 (n + 1) 1 := List.range'_append
  rw [Nat.one_mul, Nat.zero_add] at h
  exact h.symm

private theorem forIn_append_ok {α β ε : Type}
    (xs ys : List α) (init mid fin : β)
    (f : α → β → Except ε (ForInStep β))
    (h1 : forIn xs init f = .ok mid)
    (h2 : forIn ys mid f = .ok fin)
    (hyield : ∀ a, a ∈ xs → ∀ b, ∃ b', f a b = .ok (.yield b')) :
    forIn (xs ++ ys) init f = .ok fin := by
  induction xs generalizing init with
  | nil =>
    dsimp only [List.nil_append]
    rw [List.forIn_nil] at h1
    injection h1 with h_eq
    rw [h_eq]
    exact h2
  | cons a rest ih =>
    dsimp only [List.cons_append]
    rw [List.forIn_cons] at h1
    rw [List.forIn_cons]
    let ⟨b', hb'⟩ := hyield a (List.Mem.head rest) init
    rw [hb'] at h1
    rw [hb']
    dsimp only [bind, Except.bind] at h1
    dsimp only [bind, Except.bind]
    exact ih b' h1 (fun x hx => hyield x (List.Mem.tail a hx))

/-- Exact mirror of `Miri.Memory.Allocation.lean`'s private `targetUIntBytes`,
definitionally equal to it so `change` exposes `Std.Legacy.Range.forIn` for
kernel-checked rewriting via `Std.Legacy.Range.forIn_eq_forIn_range'`. -/
def targetUIntBytesMirror (layout : TargetDataLayout) (size : Size)
    (bits : U128) : Except AllocError (Array UInt8) :=
  Bind.bind
    (if size.bytes > 16 then
      throw (.scalarBytesTooWide size)
     else pure PUnit.unit)
    (fun _ =>
      let count := size.bytes.toNat
      Bind.bind
        (forIn (m := Except AllocError)
          ({ start := 0, stop := count, step := 1, step_pos := Nat.zero_lt_one } :
            Std.Legacy.Range)
          (Array.mk [])
          (fun index result =>
            let valueIndex :=
              if layout.endian == .little then index else count - index - 1
            let byte :=
              HMod.hMod (HDiv.hDiv bits.toNat (HPow.hPow 2 (8 * valueIndex))) 256
            pure (ForInStep.yield (result.push (UInt8.ofNat byte)))))
        (fun result => pure result))

/-- Exact mirror of `Miri.Memory.Allocation.lean`'s private `readTargetUInt`,
definitionally equal to it. -/
def readTargetUIntMirror (layout : TargetDataLayout)
    (bytes : Array UInt8) : Except AllocError U128 :=
  let k1 := fun (_ : PUnit) =>
    Bind.bind
      (forIn (m := Except AllocError)
        ({ start := 0, stop := bytes.size, step := 1, step_pos := Nat.zero_lt_one } :
          Std.Legacy.Range)
        (0 : Nat)
        (fun index value =>
          match bytes[index]? with
          | some byte =>
            let valueIndex :=
              if layout.endian == .little then index else bytes.size - index - 1
            pure (ForInStep.yield
              (value + byte.toNat * HPow.hPow 2 (8 * valueIndex)))
          | _ =>
            throw (.invalidSliceEndpoints index (index + 1) bytes.size)))
      (fun value => pure (BitVec.ofNat 128 value))
  if bytes.size > 16 then
    Bind.bind (throw (.scalarBytesTooWide (Size.ofBytes (UInt64.ofNat bytes.size)))) k1
  else k1 PUnit.unit

private theorem except_bind_pure {ε α β : Type} (a : α) (f : α → Except ε β) :
    Bind.bind (pure a : Except ε α) f = f a := rfl

theorem targetUIntBytesMirror_be (n : Nat) (hn : n ≤ 16) (d : U128) :
    targetUIntBytesMirror RuntimeTargetDataLayout.default.base
        (Size.ofBytes (UInt64.ofNat n)) d = .ok (beBytes d.toNat n n) := by
  have h_n_lt : n < HPow.hPow (2 : Nat) 64 := Nat.lt_of_le_of_lt hn (by decide)
  have h_sz_nat : (Size.ofBytes (UInt64.ofNat n)).bytes.toNat = n := by
    change HMod.hMod n (HPow.hPow (2 : Nat) 64) = n
    exact Nat.mod_eq_of_lt h_n_lt
  have h_not_gt : ¬ ((Size.ofBytes (UInt64.ofNat n)).bytes > 16) := by
    change ¬ (16 < (Size.ofBytes (UInt64.ofNat n)).bytes.toNat)
    rw [h_sz_nat]
    exact Nat.not_lt.mpr hn
  have h_endian :
      (RuntimeTargetDataLayout.default.base.endian == Endian.little) = false := by
    decide
  dsimp only [targetUIntBytesMirror]
  rw [ite_eq_right h_not_gt, except_bind_pure]
  have h_loop : ∀ k,
      forIn (m := Except AllocError) (List.range' 0 k 1) (Array.mk [] : Array UInt8)
        (fun index acc =>
          pure (ForInStep.yield
            (acc.push (UInt8.ofNat
              (HMod.hMod (HDiv.hDiv d.toNat (HPow.hPow 2 (8 * (n - index - 1)))) 256))))) =
        .ok (beBytes d.toNat n k) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [list_range'_succ_end]
      refine forIn_append_ok _ _ _ (beBytes d.toNat n k) _ _ ih ?_
        (fun _ _ b => ⟨_, rfl⟩)
      rw [List.forIn_cons]
      rfl
  simp only [h_endian, Bool.false_eq_true, ite_false, h_sz_nat,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [h_loop n]
  rfl

private theorem be_accum_step (x k m : Nat) :
    HMod.hMod (HDiv.hDiv x (HPow.hPow 2 (8 * (m + 1)))) (HPow.hPow 2 (8 * k)) *
        HPow.hPow 2 (8 * (m + 1)) +
      HMod.hMod (HDiv.hDiv x (HPow.hPow 2 (8 * m))) 256 * HPow.hPow 2 (8 * m) =
      HMod.hMod (HDiv.hDiv x (HPow.hPow 2 (8 * m))) (HPow.hPow 2 (8 * (k + 1))) *
        HPow.hPow 2 (8 * m) := by
  have h_pow_m : HPow.hPow (2 : Nat) (8 * (m + 1)) = HPow.hPow 2 (8 * m) * 256 := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
  have h_pow_k : 256 * HPow.hPow (2 : Nat) (8 * k) = HPow.hPow 2 (8 * (k + 1)) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
  have h_div : HDiv.hDiv x (HPow.hPow 2 (8 * (m + 1))) =
      HDiv.hDiv (HDiv.hDiv x (HPow.hPow 2 (8 * m))) 256 := by
    rw [h_pow_m, Nat.div_div_eq_div_mul]
  rw [h_div, h_pow_m]
  have h_decomp := nat_mod_mul_decomp (HDiv.hDiv x (HPow.hPow 2 (8 * m))) 256
    (HPow.hPow 2 (8 * k)) (by decide) (pow2_pos _)
  rw [h_pow_k] at h_decomp
  have h_mul := congrArg (fun t => t * HPow.hPow 2 (8 * m)) h_decomp
  rw [Nat.add_mul] at h_mul
  rw [← h_mul, Nat.add_comm]
  have h_assoc :
      HMod.hMod (HDiv.hDiv (HDiv.hDiv x (HPow.hPow 2 (8 * m))) 256) (HPow.hPow 2 (8 * k)) *
          (HPow.hPow 2 (8 * m) * 256) =
        HMod.hMod (HDiv.hDiv (HDiv.hDiv x (HPow.hPow 2 (8 * m))) 256) (HPow.hPow 2 (8 * k)) *
          256 * HPow.hPow 2 (8 * m) := by
    rw [Nat.mul_comm (HPow.hPow 2 (8 * m)) 256, Nat.mul_assoc]
  rw [h_assoc]

theorem readTargetUIntMirror_be (n : Nat) (hn : n ≤ 16) (x : Nat) :
    readTargetUIntMirror RuntimeTargetDataLayout.default.base (beBytes x n n) =
      .ok (BitVec.ofNat 128 (HMod.hMod x (HPow.hPow 2 (8 * n)))) := by
  have h_endian :
      (RuntimeTargetDataLayout.default.base.endian == Endian.little) = false := by
    decide
  have h_not_gt : ¬ ((beBytes x n n).size > 16) := by
    rw [beBytes_size]
    exact Nat.not_lt.mpr hn
  dsimp only [readTargetUIntMirror]
  rw [ite_eq_right h_not_gt, beBytes_size]
  simp only [h_endian, Bool.false_eq_true, ite_false,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  have h_loop : ∀ k, k ≤ n →
      forIn (m := Except AllocError) (List.range' 0 k 1) (0 : Nat)
        (fun index s =>
          match (beBytes x n n)[index]? with
          | some byte =>
            pure (ForInStep.yield
              (s + byte.toNat * HPow.hPow 2 (8 * (n - index - 1))))
          | _ =>
            throw (.invalidSliceEndpoints index (index + 1) n)) =
        .ok (HMod.hMod (HDiv.hDiv x (HPow.hPow 2 (8 * (n - k)))) (HPow.hPow 2 (8 * k)) *
          HPow.hPow 2 (8 * (n - k))) := by
    intro k hk
    induction k with
    | zero =>
      dsimp only [List.range']
      rw [List.forIn_nil]
      change Except.ok 0 =
        Except.ok (HMod.hMod (HDiv.hDiv x (HPow.hPow 2 (8 * (n - 0)))) 1 *
          HPow.hPow 2 (8 * (n - 0)))
      rw [Nat.mod_one, Nat.zero_mul]
    | succ k ih =>
      have hk_lt : k < n := hk
      have hk_le : k ≤ n := Nat.le_of_lt hk_lt
      have h_sub : n - k = (n - k - 1) + 1 := by
        have h1 : 1 ≤ n - k := Nat.sub_pos_of_lt hk_lt
        exact (Nat.sub_add_cancel h1).symm
      have h_sub2 : n - (k + 1) = n - k - 1 := by
        rw [Nat.sub_add_eq]
      rw [list_range'_succ_end]
      refine forIn_append_ok _ _ _
        (HMod.hMod (HDiv.hDiv x (HPow.hPow 2 (8 * (n - k)))) (HPow.hPow 2 (8 * k)) *
          HPow.hPow 2 (8 * (n - k))) _ _
        (ih hk_le) ?_ ?_
      · rw [List.forIn_cons, beBytes_getElem? x n n k hk_lt]
        dsimp only [bind, Except.bind, pure, Except.pure]
        rw [List.forIn_nil]
        change Except.ok
          (HMod.hMod (HDiv.hDiv x (HPow.hPow 2 (8 * (n - k)))) (HPow.hPow 2 (8 * k)) *
              HPow.hPow 2 (8 * (n - k)) +
            (UInt8.ofNat (HMod.hMod (HDiv.hDiv x (HPow.hPow 2 (8 * (n - k - 1)))) 256)).toNat *
              HPow.hPow 2 (8 * (n - k - 1))) =
          Except.ok
            (HMod.hMod (HDiv.hDiv x (HPow.hPow 2 (8 * (n - (k + 1)))))
                (HPow.hPow 2 (8 * (k + 1))) *
              HPow.hPow 2 (8 * (n - (k + 1))))
        have h_step := be_accum_step x k (n - k - 1)
        rw [← h_sub] at h_step
        rw [u8_ofNat_toNat_mod, h_sub2, h_step]
      · intro idx hmem acc
        let ⟨i, hi, hidx⟩ := List.mem_range'.mp hmem
        rw [Nat.one_mul, Nat.zero_add] at hidx
        rw [hidx, beBytes_getElem? x n n i (Nat.lt_trans hi hk_lt)]
        exact ⟨_, rfl⟩
  rw [h_loop n (Nat.le_refl n), Nat.sub_self]
  change Except.ok (BitVec.ofNat 128
    (HMod.hMod (HDiv.hDiv x 1) (HPow.hPow 2 (8 * n)) * 1)) = _
  rw [Nat.div_one, Nat.mul_one]

/-! ## Section 2: Fresh Allocation Initialization and Scalar Round-Trips -/

private theorem ite_const_eq {α β : Type} (c : Bool) (a b : α) (f : α → β) (v : β)
    (ha : f a = v) (hb : f b = v) : f (if c = true then a else b) = v := by
  cases c with
  | true => exact ha
  | false => exact hb

theorem reserveAllocId_empty_eq :
    ∃ mem1,
      (Miri.Memory.MemoryState.empty
        (Prov := Miri.Memory.Provenance)
        (Extra := Miri.TreeBorrows.BorrowTree)
        (MachineKind := Unit)).reserveAllocId =
        (mem1, .ok ⟨1, by decide⟩) ∧
      mem1.live = (Array.mk []) := by
  let e : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit := Miri.Memory.MemoryState.empty
  have h_res :=
    Miri.Memory.MemoryState.reserve_of_highWater e rfl (by decide)
      (fun h => by cases h) (fun h => by cases h)
      (fun _ hm => by cases hm with | mk h => cases h)
      (fun _ hm => by cases hm with | mk h => cases h)
      (fun _ hm => by cases hm with | mk h => cases h)
      (fun _ hm => by cases hm with | mk h => cases h)
  let ⟨mem1, h_eq⟩ := h_res
  refine ⟨mem1, h_eq, ?_⟩
  have h_live : e.reserveAllocId.1.live = (Array.mk []) := by
    dsimp only [e, Miri.Memory.MemoryState.reserveAllocId,
      Miri.Memory.MemoryState.empty, Id.run, bind, Bind.bind, pure, Pure.pure,
      Miri.Memory.AllocId.ofUInt64]
    rw [ite_eq_right (by decide), ite_eq_right (by decide)]
    have h_ne1 : ((1 : UInt64) = 0) → False := by decide
    rw [dite_eq_right h_ne1]
    dsimp only
    exact ite_const_eq _ _ _
      (fun (p : Miri.Memory.MemoryState Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree Unit ×
        Except AllocationIdError Miri.Memory.AllocId) => p.1.live)
      (Array.mk []) rfl rfl
  rw [h_eq] at h_live
  exact h_live

private theorem refLayoutDataForTy_align (ty : MirTy) :
    (refLayoutDataForTy ty).align.abi = Align.ONE := by
  cases ty with
  | unit | never | bool | int _ _ | char | ordering | ref _ _ | rawPtr _ _
  | slice _ | str | array _ _ | vec _ | box _ | rangeTo _ | rangeFrom _ | range _
  | option _ | unsupported | struct_ _ _ => rfl
  | tuple fs =>
    cases refLayoutDataForTy_tuple fs with
    | inl h => rw [h]; rfl
    | inr h =>
      let ⟨_, _, _, h_eq⟩ := h
      rw [h_eq]; rfl
  | enum ety =>
    dsimp only [refLayoutDataForTy, refAsEnumTy?, refEnumLayoutData]
    cases ety.tagRepr <;> rfl

theorem refInitMemoryAndRetPlace_ok (types : List MirTy) (retTy : MirTy) :
    ∃ mem retPlace,
      refInitMemoryAndRetPlace types retTy = .ok (mem, retPlace) := by
  have h_al : (refLocalLayoutForTy types retTy).layout.align.abi = Align.ONE :=
    refLayoutDataForTy_align retTy
  let ⟨rawAlloc, h_raw, _⟩ :=
    Allocation.tryNew_replicate_full (P := Miri.Memory.Provenance)
      (refLocalLayoutForTy types retTy).layout.size Align.ONE 1
      (by decide) (by decide)
  let ⟨mem1, h_res, _⟩ := reserveAllocId_empty_eq
  dsimp only [refInitMemoryAndRetPlace]
  rw [h_al, h_raw]
  dsimp only
  rw [h_res]
  exact ⟨_, _, rfl⟩

/-- Characterization of the fresh uninitialized return allocation produced by
`refInitMemoryAndRetPlace`. -/
theorem refInitMemoryAndRetPlace_shape (types : List MirTy) (retTy : MirTy)
    {mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit}
    {retPlace : MPlaceTy Miri.Memory.Provenance}
    (h : refInitMemoryAndRetPlace types retTy = .ok (mem, retPlace)) :
    ∃ (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree Unit)
      (rawAlloc : Allocation Miri.Memory.Provenance Unit),
      let allocId : Miri.Memory.AllocId := ⟨1, by decide⟩
      let layout := refLocalLayoutForTy types retTy
      let alloc := rawAlloc.withExtra
        (Miri.TreeBorrows.BorrowTree.new BorTag.one layout.layout.size)
      Allocation.tryNew (Prov := Miri.Memory.Provenance)
        layout.layout.size Align.ONE .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc ∧
      alloc.byteSize = layout.layout.size ∧
      alloc.len = layout.layout.size.bytes.toNat ∧
      alloc.mutability = .Mut ∧
      alloc.align = Align.ONE ∧
      alloc.provenanceMap = ProvenanceMap.new ∧
      alloc.initializationMask = InitMask.new layout.layout.size false ∧
      mem = { mem1 with live := (Array.mk [(allocId, ⟨.stack, alloc⟩)]) } ∧
      retPlace = ⟨⟨⟨Size.ZERO, some (.concrete allocId BorTag.one)⟩,
        .none, none⟩, layout⟩ := by
  have h_al : (refLocalLayoutForTy types retTy).layout.align.abi = Align.ONE :=
    refLayoutDataForTy_align retTy
  let ⟨rawAlloc, h_raw, h_sz, h_len, _, h_mut, h_align⟩ :=
    Allocation.tryNew_replicate_full (P := Miri.Memory.Provenance)
      (refLocalLayoutForTy types retTy).layout.size Align.ONE 1
      (by decide) (by decide)
  let ⟨h_prov, h_init⟩ := Allocation.tryNew_uninit_shape _ Align.ONE rawAlloc h_raw
  let ⟨mem1, h_res, h_live⟩ := reserveAllocId_empty_eq
  dsimp only [refInitMemoryAndRetPlace] at h
  rw [h_al, h_raw] at h
  dsimp only at h
  rw [h_res] at h
  injection h with h_pair
  injection h_pair with h_mem h_rp
  refine ⟨mem1, rawAlloc, h_raw, h_sz, h_len, h_mut, h_align, h_prov, h_init,
    ?_, h_rp.symm⟩
  rw [← h_mem, h_live]
  rfl

theorem scalar_fromUInt_truncateBits (w : IntWidth)
    (bits : BitVec 128) :
    (Scalar.fromUInt (Prov := Miri.Memory.Provenance)
      (truncateBits w bits) (toMiriSize w)).mapError AllocError.scalar =
      .ok (.fromScalarInt (miriScalar w bits)) := by
  dsimp only [Scalar.fromUInt, Except.mapError]
  rw [tryFromUInt_eq_truncateFromUInt, truncateFromUInt_eq_miriScalar w]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [truncateBits_idem, bne_self_eq_false, ite_false_eq_true]
  have h_ms : miriScalar w (truncateBits w bits) = miriScalar w bits := by
    have h1 : (miriScalar w (truncateBits w bits)).data =
        (miriScalar w bits).data := by
      rw [miriScalar_data, miriScalar_data, truncateBits_idem]
    have h2 : (miriScalar w (truncateBits w bits)).size =
        (miriScalar w bits).size := by
      cases w <;> rfl
    cases hm1 : miriScalar w (truncateBits w bits)
    cases hm2 : miriScalar w bits
    rw [hm1, hm2] at h1 h2
    dsimp only [ScalarInt.data, ScalarInt.size] at h1 h2
    rw [h1, h2]
  rw [h_ms]

private theorem clearProvenance_of_read_ok (w : IntWidth)
    {after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree}
    {sc : Scalar Miri.Memory.Provenance}
    (h_prov : after.provenanceMap = ProvenanceMap.new)
    (h_rd : after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (toMiriSize w)) false = .ok sc) :
    Allocation.clearProvenance (allocRange Size.ZERO (toMiriSize w))
      (Size.ofBytes 8) after = .ok () after := by
  have h_end : (allocRange Size.ZERO (toMiriSize w)).endExclusive =
      .ok (toMiriSize w) := by
    cases w <;> rfl
  have h_bs : ∃ bs, Allocation.getBytesUnchecked after
      (allocRange Size.ZERO (toMiriSize w)) = .ok bs := by
    dsimp only [Allocation.readScalar] at h_rd
    cases h_im : (after.initializationMask.isRangeInitialized
        (allocRange Size.ZERO (toMiriSize w))).mapError AllocError.memory with
    | error _ =>
      dsimp only [Allocation.initializationMask] at h_im
      rw [h_im] at h_rd; cases h_rd
    | ok r =>
      dsimp only [Allocation.initializationMask] at h_im
      rw [h_im] at h_rd
      cases r with
      | error _ => cases h_rd
      | ok _ =>
        dsimp only [bind, Except.bind, pure, Except.pure] at h_rd
        cases h_cs : Allocation.getBytesUnchecked after
            (allocRange Size.ZERO (toMiriSize w)) with
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
  rw [h_prov, ProvenanceMap.clear_new (allocRange Size.ZERO (toMiriSize w))
    _ (Size.ofBytes 8) (toMiriSize w) (by decide) h_end]
  dsimp only
  cases after
  dsimp only at h_prov
  rw [h_prov]

/-- Concrete uninitialized allocation for width `w`, built via
`Allocation.fromBytes` + `Allocation.writeUninit` and proved equal to
`Allocation.tryNew` via `Allocation.tryNew_uninit_image`. -/
theorem freshAlloc_eq_fromBytes_uninit (w : IntWidth)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (toMiriSize w) Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc) :
    ∃ (init : Allocation Miri.Memory.Provenance Unit),
      Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        (Array.replicate (toMiriSize w).bytes.toNat 0) Align.ONE .Mut =
          .ok init ∧
      Allocation.writeUninit (allocRange Size.ZERO (toMiriSize w))
        (Size.ofBytes 8) init = .ok () rawAlloc := by
  let ⟨_, init, h_fb, h_wu⟩ :=
    Allocation.tryNew_uninit_image (toMiriSize w) Align.ONE (Size.ofBytes 8)
      rawAlloc (by decide) h_raw
  have h_ne0 : (toMiriSize w).bytes ≠ 0 := by cases w <;> decide
  rw [ite_eq_right h_ne0] at h_wu
  exact ⟨init, h_fb, h_wu⟩

theorem array_empty_append_extract (data : Array UInt8) (n : Nat)
    (h : data.size = n) : ((Array.mk []) ++ data ++ (Array.mk [])).extract 0 n = data := by
  have h1 : ((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []) = data := by
    rw [Array.empty_append, Array.append_empty]
  rw [h1, ← h, Array.extract_eq_self_iff]
  exact Or.inr ⟨rfl, Nat.le_refl _⟩

def checkedSliceMirror (rawBytes : Array UInt8) (size : Size)
    (range : AllocRange) : Except AllocError (Array UInt8) :=
  let k1 := fun (_ : PUnit) =>
    Bind.bind (Except.mapError AllocError.memory range.endExclusive) (fun finish =>
      let k2 := fun (_ : PUnit) =>
        pure (rawBytes.extract range.start.bytes.toNat finish.bytes.toNat)
      if (range.start.bytes > finish.bytes || finish.bytes > size.bytes) = true then
        Bind.bind (throw (.outOfBounds range size)) k2
      else k2 PUnit.unit)
  if (rawBytes.size != size.bytes.toNat) = true then
    Bind.bind (throw (.storageLengthMismatch size rawBytes.size)) k1
  else k1 PUnit.unit

private theorem checkedSliceMirror_eq (w : IntWidth) (bytes : Array UInt8)
    (h : bytes.size = (toMiriSize w).bytes.toNat) :
    checkedSliceMirror bytes (toMiriSize w) (allocRange Size.ZERO (toMiriSize w)) =
      .ok (bytes.extract 0 (toMiriSize w).bytes.toNat) := by
  dsimp only [checkedSliceMirror]
  rw [h, bne_self_eq_false, ite_false_eq_true]
  cases w <;> rfl

private theorem writeScalar_readScalar_step_i8
    (bits : BitVec 128) (data : Array UInt8)
    (h_dlen : data.size = (toMiriSize .i8).bytes.toNat)
    (h_t : targetUIntBytesMirror RuntimeTargetDataLayout.default.base
      (toMiriSize .i8) (miriScalar .i8 bits).data = .ok data)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (toMiriSize .i8) Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc) :
    let alloc := rawAlloc.withExtra
      (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize .i8))
    ∃ after,
      Allocation.writeScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize .i8))
          (.fromScalarInt (miriScalar .i8 bits)) alloc = .ok () after ∧
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize .i8)) false =
        Bind.bind
          (readTargetUIntMirror RuntimeTargetDataLayout.default.base
            (((Array.mk []) ++ data ++ (Array.mk [])).extract 0 (toMiriSize .i8).bytes.toNat))
          (fun b => (Scalar.fromUInt b (toMiriSize .i8)).mapError AllocError.scalar) ∧
      after.getBytesUnchecked (allocRange Size.ZERO (toMiriSize .i8)) =
        .ok (((Array.mk []) ++ data ++ (Array.mk [])).extract 0
          (toMiriSize .i8).bytes.toNat) ∧
      after.provenanceMap = ProvenanceMap.new ∧
      after.byteSize = toMiriSize .i8 ∧
      after.mutability = .Mut ∧
      after.align = Align.ONE ∧
      after.extra = alloc.extra := by
  let ⟨init, h_fb, h_wu⟩ := freshAlloc_eq_fromBytes_uninit .i8 h_raw
  have h_len_eq : (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk [])).size =
      (toMiriSize .i8).bytes.toNat := by
    rw [Array.empty_append, Array.append_empty]; exact h_dlen
  injection h_fb with h_init_eq; subst h_init_eq
  injection h_wu with _ h_raw_eq; subst h_raw_eq
  intro alloc
  change ∃ after,
    (match targetUIntBytesMirror RuntimeTargetDataLayout.default.base
        (toMiriSize .i8) (miriScalar .i8 bits).data with
    | Except.ok _ => _
    | Except.error _ => _) = EStateM.Result.ok () after ∧ _
  rw [h_t]
  change ∃ after,
    (if ((((Array.mk []) : Array UInt8) ++ data ++ (Array.mk [])).size != (toMiriSize .i8).bytes.toNat) = true
     then _ else _) = EStateM.Result.ok () after ∧ _
  rw [h_len_eq, bne_self_eq_false, ite_false_eq_true]
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · change Bind.bind
      (checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
        (toMiriSize .i8) (allocRange Size.ZERO (toMiriSize .i8)))
      (fun bytes => Bind.bind
        (readTargetUIntMirror RuntimeTargetDataLayout.default.base bytes)
        (fun b => (Scalar.fromUInt b (toMiriSize .i8)).mapError AllocError.scalar)) = _
    rw [checkedSliceMirror_eq .i8 _ h_len_eq]
    rfl
  · change checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
      (toMiriSize .i8) (allocRange Size.ZERO (toMiriSize .i8)) = _
    exact checkedSliceMirror_eq .i8 _ h_len_eq

private theorem writeScalar_readScalar_step_i16
    (bits : BitVec 128) (data : Array UInt8)
    (h_dlen : data.size = (toMiriSize .i16).bytes.toNat)
    (h_t : targetUIntBytesMirror RuntimeTargetDataLayout.default.base
      (toMiriSize .i16) (miriScalar .i16 bits).data = .ok data)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (toMiriSize .i16) Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc) :
    let alloc := rawAlloc.withExtra
      (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize .i16))
    ∃ after,
      Allocation.writeScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize .i16))
          (.fromScalarInt (miriScalar .i16 bits)) alloc = .ok () after ∧
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize .i16)) false =
        Bind.bind
          (readTargetUIntMirror RuntimeTargetDataLayout.default.base
            (((Array.mk []) ++ data ++ (Array.mk [])).extract 0 (toMiriSize .i16).bytes.toNat))
          (fun b => (Scalar.fromUInt b (toMiriSize .i16)).mapError AllocError.scalar) ∧
      after.getBytesUnchecked (allocRange Size.ZERO (toMiriSize .i16)) =
        .ok (((Array.mk []) ++ data ++ (Array.mk [])).extract 0
          (toMiriSize .i16).bytes.toNat) ∧
      after.provenanceMap = ProvenanceMap.new ∧
      after.byteSize = toMiriSize .i16 ∧
      after.mutability = .Mut ∧
      after.align = Align.ONE ∧
      after.extra = alloc.extra := by
  let ⟨init, h_fb, h_wu⟩ := freshAlloc_eq_fromBytes_uninit .i16 h_raw
  have h_len_eq : (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk [])).size =
      (toMiriSize .i16).bytes.toNat := by
    rw [Array.empty_append, Array.append_empty]; exact h_dlen
  injection h_fb with h_init_eq; subst h_init_eq
  injection h_wu with _ h_raw_eq; subst h_raw_eq
  intro alloc
  change ∃ after,
    (match targetUIntBytesMirror RuntimeTargetDataLayout.default.base
        (toMiriSize .i16) (miriScalar .i16 bits).data with
    | Except.ok _ => _
    | Except.error _ => _) = EStateM.Result.ok () after ∧ _
  rw [h_t]
  change ∃ after,
    (if ((((Array.mk []) : Array UInt8) ++ data ++ (Array.mk [])).size != (toMiriSize .i16).bytes.toNat) = true
     then _ else _) = EStateM.Result.ok () after ∧ _
  rw [h_len_eq, bne_self_eq_false, ite_false_eq_true]
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · change Bind.bind
      (checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
        (toMiriSize .i16) (allocRange Size.ZERO (toMiriSize .i16)))
      (fun bytes => Bind.bind
        (readTargetUIntMirror RuntimeTargetDataLayout.default.base bytes)
        (fun b => (Scalar.fromUInt b (toMiriSize .i16)).mapError AllocError.scalar)) = _
    rw [checkedSliceMirror_eq .i16 _ h_len_eq]
    rfl
  · change checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
      (toMiriSize .i16) (allocRange Size.ZERO (toMiriSize .i16)) = _
    exact checkedSliceMirror_eq .i16 _ h_len_eq

private theorem writeScalar_readScalar_step_i32
    (bits : BitVec 128) (data : Array UInt8)
    (h_dlen : data.size = (toMiriSize .i32).bytes.toNat)
    (h_t : targetUIntBytesMirror RuntimeTargetDataLayout.default.base
      (toMiriSize .i32) (miriScalar .i32 bits).data = .ok data)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (toMiriSize .i32) Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc) :
    let alloc := rawAlloc.withExtra
      (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize .i32))
    ∃ after,
      Allocation.writeScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize .i32))
          (.fromScalarInt (miriScalar .i32 bits)) alloc = .ok () after ∧
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize .i32)) false =
        Bind.bind
          (readTargetUIntMirror RuntimeTargetDataLayout.default.base
            (((Array.mk []) ++ data ++ (Array.mk [])).extract 0 (toMiriSize .i32).bytes.toNat))
          (fun b => (Scalar.fromUInt b (toMiriSize .i32)).mapError AllocError.scalar) ∧
      after.getBytesUnchecked (allocRange Size.ZERO (toMiriSize .i32)) =
        .ok (((Array.mk []) ++ data ++ (Array.mk [])).extract 0
          (toMiriSize .i32).bytes.toNat) ∧
      after.provenanceMap = ProvenanceMap.new ∧
      after.byteSize = toMiriSize .i32 ∧
      after.mutability = .Mut ∧
      after.align = Align.ONE ∧
      after.extra = alloc.extra := by
  let ⟨init, h_fb, h_wu⟩ := freshAlloc_eq_fromBytes_uninit .i32 h_raw
  have h_len_eq : (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk [])).size =
      (toMiriSize .i32).bytes.toNat := by
    rw [Array.empty_append, Array.append_empty]; exact h_dlen
  injection h_fb with h_init_eq; subst h_init_eq
  injection h_wu with _ h_raw_eq; subst h_raw_eq
  intro alloc
  change ∃ after,
    (match targetUIntBytesMirror RuntimeTargetDataLayout.default.base
        (toMiriSize .i32) (miriScalar .i32 bits).data with
    | Except.ok _ => _
    | Except.error _ => _) = EStateM.Result.ok () after ∧ _
  rw [h_t]
  change ∃ after,
    (if ((((Array.mk []) : Array UInt8) ++ data ++ (Array.mk [])).size != (toMiriSize .i32).bytes.toNat) = true
     then _ else _) = EStateM.Result.ok () after ∧ _
  rw [h_len_eq, bne_self_eq_false, ite_false_eq_true]
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · change Bind.bind
      (checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
        (toMiriSize .i32) (allocRange Size.ZERO (toMiriSize .i32)))
      (fun bytes => Bind.bind
        (readTargetUIntMirror RuntimeTargetDataLayout.default.base bytes)
        (fun b => (Scalar.fromUInt b (toMiriSize .i32)).mapError AllocError.scalar)) = _
    rw [checkedSliceMirror_eq .i32 _ h_len_eq]
    rfl
  · change checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
      (toMiriSize .i32) (allocRange Size.ZERO (toMiriSize .i32)) = _
    exact checkedSliceMirror_eq .i32 _ h_len_eq

private theorem writeScalar_readScalar_step_i64
    (bits : BitVec 128) (data : Array UInt8)
    (h_dlen : data.size = (toMiriSize .i64).bytes.toNat)
    (h_t : targetUIntBytesMirror RuntimeTargetDataLayout.default.base
      (toMiriSize .i64) (miriScalar .i64 bits).data = .ok data)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (toMiriSize .i64) Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc) :
    let alloc := rawAlloc.withExtra
      (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize .i64))
    ∃ after,
      Allocation.writeScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize .i64))
          (.fromScalarInt (miriScalar .i64 bits)) alloc = .ok () after ∧
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize .i64)) false =
        Bind.bind
          (readTargetUIntMirror RuntimeTargetDataLayout.default.base
            (((Array.mk []) ++ data ++ (Array.mk [])).extract 0 (toMiriSize .i64).bytes.toNat))
          (fun b => (Scalar.fromUInt b (toMiriSize .i64)).mapError AllocError.scalar) ∧
      after.getBytesUnchecked (allocRange Size.ZERO (toMiriSize .i64)) =
        .ok (((Array.mk []) ++ data ++ (Array.mk [])).extract 0
          (toMiriSize .i64).bytes.toNat) ∧
      after.provenanceMap = ProvenanceMap.new ∧
      after.byteSize = toMiriSize .i64 ∧
      after.mutability = .Mut ∧
      after.align = Align.ONE ∧
      after.extra = alloc.extra := by
  let ⟨init, h_fb, h_wu⟩ := freshAlloc_eq_fromBytes_uninit .i64 h_raw
  have h_len_eq : (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk [])).size =
      (toMiriSize .i64).bytes.toNat := by
    rw [Array.empty_append, Array.append_empty]; exact h_dlen
  injection h_fb with h_init_eq; subst h_init_eq
  injection h_wu with _ h_raw_eq; subst h_raw_eq
  intro alloc
  change ∃ after,
    (match targetUIntBytesMirror RuntimeTargetDataLayout.default.base
        (toMiriSize .i64) (miriScalar .i64 bits).data with
    | Except.ok _ => _
    | Except.error _ => _) = EStateM.Result.ok () after ∧ _
  rw [h_t]
  change ∃ after,
    (if ((((Array.mk []) : Array UInt8) ++ data ++ (Array.mk [])).size != (toMiriSize .i64).bytes.toNat) = true
     then _ else _) = EStateM.Result.ok () after ∧ _
  rw [h_len_eq, bne_self_eq_false, ite_false_eq_true]
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · change Bind.bind
      (checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
        (toMiriSize .i64) (allocRange Size.ZERO (toMiriSize .i64)))
      (fun bytes => Bind.bind
        (readTargetUIntMirror RuntimeTargetDataLayout.default.base bytes)
        (fun b => (Scalar.fromUInt b (toMiriSize .i64)).mapError AllocError.scalar)) = _
    rw [checkedSliceMirror_eq .i64 _ h_len_eq]
    rfl
  · change checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
      (toMiriSize .i64) (allocRange Size.ZERO (toMiriSize .i64)) = _
    exact checkedSliceMirror_eq .i64 _ h_len_eq

private theorem writeScalar_readScalar_step_isize
    (bits : BitVec 128) (data : Array UInt8)
    (h_dlen : data.size = (toMiriSize .isize).bytes.toNat)
    (h_t : targetUIntBytesMirror RuntimeTargetDataLayout.default.base
      (toMiriSize .isize) (miriScalar .isize bits).data = .ok data)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (toMiriSize .isize) Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc) :
    let alloc := rawAlloc.withExtra
      (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize .isize))
    ∃ after,
      Allocation.writeScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize .isize))
          (.fromScalarInt (miriScalar .isize bits)) alloc = .ok () after ∧
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize .isize)) false =
        Bind.bind
          (readTargetUIntMirror RuntimeTargetDataLayout.default.base
            (((Array.mk []) ++ data ++ (Array.mk [])).extract 0 (toMiriSize .isize).bytes.toNat))
          (fun b => (Scalar.fromUInt b (toMiriSize .isize)).mapError AllocError.scalar) ∧
      after.getBytesUnchecked (allocRange Size.ZERO (toMiriSize .isize)) =
        .ok (((Array.mk []) ++ data ++ (Array.mk [])).extract 0
          (toMiriSize .isize).bytes.toNat) ∧
      after.provenanceMap = ProvenanceMap.new ∧
      after.byteSize = toMiriSize .isize ∧
      after.mutability = .Mut ∧
      after.align = Align.ONE ∧
      after.extra = alloc.extra := by
  let ⟨init, h_fb, h_wu⟩ := freshAlloc_eq_fromBytes_uninit .isize h_raw
  have h_len_eq : (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk [])).size =
      (toMiriSize .isize).bytes.toNat := by
    rw [Array.empty_append, Array.append_empty]; exact h_dlen
  injection h_fb with h_init_eq; subst h_init_eq
  injection h_wu with _ h_raw_eq; subst h_raw_eq
  intro alloc
  change ∃ after,
    (match targetUIntBytesMirror RuntimeTargetDataLayout.default.base
        (toMiriSize .isize) (miriScalar .isize bits).data with
    | Except.ok _ => _
    | Except.error _ => _) = EStateM.Result.ok () after ∧ _
  rw [h_t]
  change ∃ after,
    (if ((((Array.mk []) : Array UInt8) ++ data ++ (Array.mk [])).size != (toMiriSize .isize).bytes.toNat) = true
     then _ else _) = EStateM.Result.ok () after ∧ _
  rw [h_len_eq, bne_self_eq_false, ite_false_eq_true]
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · change Bind.bind
      (checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
        (toMiriSize .isize) (allocRange Size.ZERO (toMiriSize .isize)))
      (fun bytes => Bind.bind
        (readTargetUIntMirror RuntimeTargetDataLayout.default.base bytes)
        (fun b => (Scalar.fromUInt b (toMiriSize .isize)).mapError AllocError.scalar)) = _
    rw [checkedSliceMirror_eq .isize _ h_len_eq]
    rfl
  · change checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
      (toMiriSize .isize) (allocRange Size.ZERO (toMiriSize .isize)) = _
    exact checkedSliceMirror_eq .isize _ h_len_eq

private theorem writeScalar_readScalar_step_i128
    (bits : BitVec 128) (data : Array UInt8)
    (h_dlen : data.size = (toMiriSize .i128).bytes.toNat)
    (h_t : targetUIntBytesMirror RuntimeTargetDataLayout.default.base
      (toMiriSize .i128) (miriScalar .i128 bits).data = .ok data)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (toMiriSize .i128) Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc) :
    let alloc := rawAlloc.withExtra
      (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize .i128))
    ∃ after,
      Allocation.writeScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize .i128))
          (.fromScalarInt (miriScalar .i128 bits)) alloc = .ok () after ∧
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize .i128)) false =
        Bind.bind
          (readTargetUIntMirror RuntimeTargetDataLayout.default.base
            (((Array.mk []) ++ data ++ (Array.mk [])).extract 0 (toMiriSize .i128).bytes.toNat))
          (fun b => (Scalar.fromUInt b (toMiriSize .i128)).mapError AllocError.scalar) ∧
      after.getBytesUnchecked (allocRange Size.ZERO (toMiriSize .i128)) =
        .ok (((Array.mk []) ++ data ++ (Array.mk [])).extract 0
          (toMiriSize .i128).bytes.toNat) ∧
      after.provenanceMap = ProvenanceMap.new ∧
      after.byteSize = toMiriSize .i128 ∧
      after.mutability = .Mut ∧
      after.align = Align.ONE ∧
      after.extra = alloc.extra := by
  let ⟨init, h_fb, h_wu⟩ := freshAlloc_eq_fromBytes_uninit .i128 h_raw
  have h_len_eq : (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk [])).size =
      (toMiriSize .i128).bytes.toNat := by
    rw [Array.empty_append, Array.append_empty]; exact h_dlen
  injection h_fb with h_init_eq; subst h_init_eq
  injection h_wu with _ h_raw_eq; subst h_raw_eq
  intro alloc
  change ∃ after,
    (match targetUIntBytesMirror RuntimeTargetDataLayout.default.base
        (toMiriSize .i128) (miriScalar .i128 bits).data with
    | Except.ok _ => _
    | Except.error _ => _) = EStateM.Result.ok () after ∧ _
  rw [h_t]
  change ∃ after,
    (if ((((Array.mk []) : Array UInt8) ++ data ++ (Array.mk [])).size != (toMiriSize .i128).bytes.toNat) = true
     then _ else _) = EStateM.Result.ok () after ∧ _
  rw [h_len_eq, bne_self_eq_false, ite_false_eq_true]
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · change Bind.bind
      (checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
        (toMiriSize .i128) (allocRange Size.ZERO (toMiriSize .i128)))
      (fun bytes => Bind.bind
        (readTargetUIntMirror RuntimeTargetDataLayout.default.base bytes)
        (fun b => (Scalar.fromUInt b (toMiriSize .i128)).mapError AllocError.scalar)) = _
    rw [checkedSliceMirror_eq .i128 _ h_len_eq]
    rfl
  · change checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
      (toMiriSize .i128) (allocRange Size.ZERO (toMiriSize .i128)) = _
    exact checkedSliceMirror_eq .i128 _ h_len_eq

theorem writeScalar_readScalar_step (w : IntWidth)
    (bits : BitVec 128) (data : Array UInt8)
    (h_dlen : data.size = (toMiriSize w).bytes.toNat)
    (h_t : targetUIntBytesMirror RuntimeTargetDataLayout.default.base
      (toMiriSize w) (miriScalar w bits).data = .ok data)
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
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false =
        Bind.bind
          (readTargetUIntMirror RuntimeTargetDataLayout.default.base
            (((Array.mk []) ++ data ++ (Array.mk [])).extract 0 (toMiriSize w).bytes.toNat))
          (fun b => (Scalar.fromUInt b (toMiriSize w)).mapError AllocError.scalar) ∧
      after.getBytesUnchecked (allocRange Size.ZERO (toMiriSize w)) =
        .ok (((Array.mk []) ++ data ++ (Array.mk [])).extract 0
          (toMiriSize w).bytes.toNat) ∧
      after.provenanceMap = ProvenanceMap.new ∧
      after.byteSize = toMiriSize w ∧
      after.mutability = .Mut ∧
      after.align = Align.ONE ∧
      after.extra = alloc.extra := by
  cases w with
  | i8 => exact writeScalar_readScalar_step_i8 bits data h_dlen h_t h_raw
  | i16 => exact writeScalar_readScalar_step_i16 bits data h_dlen h_t h_raw
  | i32 => exact writeScalar_readScalar_step_i32 bits data h_dlen h_t h_raw
  | i64 => exact writeScalar_readScalar_step_i64 bits data h_dlen h_t h_raw
  | isize => exact writeScalar_readScalar_step_isize bits data h_dlen h_t h_raw
  | i128 => exact writeScalar_readScalar_step_i128 bits data h_dlen h_t h_raw

/-- Writing a `miriScalar w bits` into a fresh `toMiriSize w`-byte allocation
succeeds, reads back the identical `Scalar`, satisfies `clearProvenance`
without mutating the allocation, and preserves allocation metadata (`byteSize`,
`mutability`, `align`, `extra`). Covers all 6 `IntWidth`s. -/
theorem tryNew_writeScalar_readScalar (w : IntWidth) (bits : BitVec 128)
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
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false =
        .ok (.fromScalarInt (miriScalar w bits)) ∧
      Allocation.clearProvenance (allocRange Size.ZERO (toMiriSize w))
          (Size.ofBytes 8) after = .ok () after ∧
      after.byteSize = toMiriSize w ∧
      after.mutability = .Mut ∧
      after.align = Align.ONE ∧
      after.extra = alloc.extra := by
  have h_le16 : (toMiriSize w).bytes.toNat ≤ 16 := by cases w <;> decide
  have h_bits_eq : 8 * (toMiriSize w).bytes.toNat = w.bitWidth := by
    cases w <;> rfl
  have h_t : targetUIntBytesMirror RuntimeTargetDataLayout.default.base
      (toMiriSize w) (miriScalar w bits).data =
      .ok (beBytes (miriScalar w bits).data.toNat (toMiriSize w).bytes.toNat
        (toMiriSize w).bytes.toNat) := by
    cases w <;> exact targetUIntBytesMirror_be _ (by decide) _
  let ⟨after, h_w, h_rd, _, h_prov, h_sz, h_mut, h_al, h_ex⟩ :=
    writeScalar_readScalar_step w bits
      (beBytes (miriScalar w bits).data.toNat (toMiriSize w).bytes.toNat
        (toMiriSize w).bytes.toNat)
      (beBytes_size _ _ _) h_t h_raw
  have h_lt : (truncateBits w bits).toNat < HPow.hPow 2 w.bitWidth := by
    rw [toNat_truncateBits]
    exact Nat.mod_lt bits.toNat (intWidth_modulus_pos w)
  have h_rd' : after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (toMiriSize w)) false =
      .ok (.fromScalarInt (miriScalar w bits)) := by
    rw [h_rd, array_empty_append_extract _ _ (beBytes_size _ _ _),
      readTargetUIntMirror_be _ h_le16 _]
    dsimp only [bind, Except.bind]
    rw [h_bits_eq, miriScalar_data, Nat.mod_eq_of_lt h_lt,
      bitVec128_ofNat_toNat]
    exact scalar_fromUInt_truncateBits w bits
  exact ⟨after, h_w, h_rd',
    clearProvenance_of_read_ok w h_prov h_rd', h_sz, h_mut, h_al, h_ex⟩

/-- Writing `.uninit` to a fresh uninitialized allocation leaves it
uninitialized (so `readScalar` returns `.error (.invalidUninitBytes _)`). -/
theorem tryNew_writeUninit_readUninit (w : IntWidth)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (toMiriSize w) Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc) :
    let alloc := rawAlloc.withExtra
      (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize w))
    ∃ after info,
      Allocation.writeUninit (allocRange Size.ZERO (toMiriSize w))
          (Size.ofBytes 8) alloc = .ok () after ∧
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false =
        .error (.invalidUninitBytes info) ∧
      after.byteSize = toMiriSize w ∧
      after.mutability = .Mut ∧
      after.align = Align.ONE ∧
      after.extra = alloc.extra := by
  let ⟨init, h_fb, h_wu⟩ := freshAlloc_eq_fromBytes_uninit w h_raw
  cases w <;> (
    injection h_fb with h_init_eq; subst h_init_eq
    injection h_wu with _ h_raw_eq; subst h_raw_eq
    exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-! ## Section 3: `TerminatorMachine.beforeTerminatorWithChoice` -/

theorem refControlValid_init : RefControlValid refInitControl :=
  ⟨rfl, rfl, rfl, ⟨0, rfl⟩⟩

theorem refControlValid_advance
    {ctrl : Miri.Interpreter.TerminatorMachine.Control Unit}
    (h : RefControlValid ctrl) :
    RefControlValid (advanceRefControl ctrl) := by
  let ⟨h_gc, h_pr, h_ca, n, h_mono⟩ := h
  refine ⟨h_gc, h_pr, h_ca, ⟨BitVec.ofNat 128 (n.toNat + 5000), ?_⟩⟩
  dsimp only [advanceRefControl]
  rw [h_mono]

theorem beforeTerminator_ref_eq
    {st : Miri.Interpreter.MachineHooks.State Unit RefUser}
    (h_ctrl : RefControlValid st.machine.user.control)
    (h_fixed : st.machine.threads.fixedScheduling = true) :
    Miri.Interpreter.TerminatorMachine.beforeTerminatorWithChoice
        refTerminatorMachineHooks (fun st => .ok false st) st =
      .ok () { st with
        machine := { st.machine with
          user := { st.machine.user with
            control := advanceRefControl st.machine.user.control } } } := by
  let ⟨h_gc, h_pr, h_ca, n, h_mono⟩ := h_ctrl
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      cases user with
      | mk control callerMem =>
        cases control with
        | mk bbCount sinceGc gcInterval preemptionRateBits checkedArith
            monotonic =>
          dsimp only at h_gc h_pr h_ca h_mono h_fixed
          subst h_gc h_pr h_ca h_mono
          cases threads with
          | mk active threadsArr fixedSched =>
            dsimp only at h_fixed
            subst h_fixed
            rfl

end Anneal.MirCorrespondence
