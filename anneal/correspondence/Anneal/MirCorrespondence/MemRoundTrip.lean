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

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Miri.ABI Miri.Memory Miri.Interpreter

/-!
# Memory Round-Trip, Validity, and Terminator Control Proofs
(`Anneal.MirCorrespondence.MemRoundTrip`)

Proves:
1. Inductive big-endian (`RuntimeTargetDataLayout.default.base = ⟨.big, .w64⟩`)
   byte-level `Allocation.writeScalar` / `Allocation.readScalar` /
   `Allocation.clearProvenance` / `Allocation.writeUninit` round-trips for all
   6 `IntWidth`s on fresh allocations created by `refInitMemoryAndRetPlace`.
2. `TerminatorMachine.beforeTerminatorWithChoice` deterministic control
   advancement (`advanceRefControl`) and `RefControlValid` preservation.
3. `ValidityVisitor.validatePlace` soundness and completeness on Day-1 `.local`
   and `.memory retPlace` places (both initialized and uninitialized).
4. `copyRuntimePlace` + `refReadReturnVal` exact round-trip for `Return`.
-/

/-! ## Section 1: Inductive Big-Endian Byte Encoding/Decoding -/

private theorem nat_mod_mul_decomp (x a b : Nat) (ha : 0 < a) (hb : 0 < b) :
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

private theorem u8_ofNat_toNat_mod (n : Nat) :
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

private noncomputable def beBytes (x n : Nat) : Nat → Array UInt8
  | 0 => Array.mk []
  | k + 1 =>
    (beBytes x n k).push (UInt8.ofNat (HMod.hMod (HDiv.hDiv x (HPow.hPow 2 (8 * (n - k - 1)))) 256))

private theorem beBytes_size (x n : Nat) : ∀ k, (beBytes x n k).size = k
  | 0 => rfl
  | k + 1 => by
    dsimp only [beBytes]
    rw [Array.size_push, beBytes_size x n k]

private theorem beBytes_getElem? (x n : Nat) :
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
private def targetUIntBytesMirror (layout : TargetDataLayout) (size : Size)
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
private def readTargetUIntMirror (layout : TargetDataLayout)
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

private theorem targetUIntBytesMirror_be (n : Nat) (hn : n ≤ 16) (d : U128) :
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

private theorem readTargetUIntMirror_be (n : Nat) (hn : n ≤ 16) (x : Nat) :
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

theorem refInitMemoryAndRetPlace_ok (types : List MirTy) (retTy : MirTy) :
    ∃ mem retPlace,
      refInitMemoryAndRetPlace types retTy = .ok (mem, retPlace) := by
  have h_al : (refLocalLayoutForTy types retTy).layout.align.abi = Align.ONE := by
    cases retTy with
    | unit | never | bool | int _ _ | tuple _ | ref _ _ | rawPtr _ _
    | unsupported => rfl
    | enum ety =>
      dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
      cases ety.tagRepr <;> rfl
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
  have h_al : (refLocalLayoutForTy types retTy).layout.align.abi = Align.ONE := by
    cases retTy with
    | unit | never | bool | int _ _ | tuple _ | ref _ _ | rawPtr _ _
    | unsupported => rfl
    | enum ety =>
      dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
      cases ety.tagRepr <;> rfl
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

private theorem scalar_fromUInt_truncateBits (w : IntWidth)
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

private theorem array_empty_append_extract (data : Array UInt8) (n : Nat)
    (h : data.size = n) : ((Array.mk []) ++ data ++ (Array.mk [])).extract 0 n = data := by
  have h1 : ((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []) = data := by
    rw [Array.empty_append, Array.append_empty]
  rw [h1, ← h, Array.extract_eq_self_iff]
  exact Or.inr ⟨rfl, Nat.le_refl _⟩

private def checkedSliceMirror (rawBytes : Array UInt8) (size : Size)
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
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  change Bind.bind
    (checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
      (toMiriSize .i8) (allocRange Size.ZERO (toMiriSize .i8)))
    (fun bytes => Bind.bind
      (readTargetUIntMirror RuntimeTargetDataLayout.default.base bytes)
      (fun b => (Scalar.fromUInt b (toMiriSize .i8)).mapError AllocError.scalar)) = _
  rw [checkedSliceMirror_eq .i8 _ h_len_eq]
  rfl

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
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  change Bind.bind
    (checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
      (toMiriSize .i16) (allocRange Size.ZERO (toMiriSize .i16)))
    (fun bytes => Bind.bind
      (readTargetUIntMirror RuntimeTargetDataLayout.default.base bytes)
      (fun b => (Scalar.fromUInt b (toMiriSize .i16)).mapError AllocError.scalar)) = _
  rw [checkedSliceMirror_eq .i16 _ h_len_eq]
  rfl

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
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  change Bind.bind
    (checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
      (toMiriSize .i32) (allocRange Size.ZERO (toMiriSize .i32)))
    (fun bytes => Bind.bind
      (readTargetUIntMirror RuntimeTargetDataLayout.default.base bytes)
      (fun b => (Scalar.fromUInt b (toMiriSize .i32)).mapError AllocError.scalar)) = _
  rw [checkedSliceMirror_eq .i32 _ h_len_eq]
  rfl

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
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  change Bind.bind
    (checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
      (toMiriSize .i64) (allocRange Size.ZERO (toMiriSize .i64)))
    (fun bytes => Bind.bind
      (readTargetUIntMirror RuntimeTargetDataLayout.default.base bytes)
      (fun b => (Scalar.fromUInt b (toMiriSize .i64)).mapError AllocError.scalar)) = _
  rw [checkedSliceMirror_eq .i64 _ h_len_eq]
  rfl

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
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  change Bind.bind
    (checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
      (toMiriSize .isize) (allocRange Size.ZERO (toMiriSize .isize)))
    (fun bytes => Bind.bind
      (readTargetUIntMirror RuntimeTargetDataLayout.default.base bytes)
      (fun b => (Scalar.fromUInt b (toMiriSize .isize)).mapError AllocError.scalar)) = _
  rw [checkedSliceMirror_eq .isize _ h_len_eq]
  rfl

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
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  change Bind.bind
    (checkedSliceMirror (((Array.mk []) : Array UInt8) ++ data ++ (Array.mk []))
      (toMiriSize .i128) (allocRange Size.ZERO (toMiriSize .i128)))
    (fun bytes => Bind.bind
      (readTargetUIntMirror RuntimeTargetDataLayout.default.base bytes)
      (fun b => (Scalar.fromUInt b (toMiriSize .i128)).mapError AllocError.scalar)) = _
  rw [checkedSliceMirror_eq .i128 _ h_len_eq]
  rfl

private theorem writeScalar_readScalar_step (w : IntWidth)
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
  let ⟨after, h_w, h_rd, h_prov, h_sz, h_mut, h_al, h_ex⟩ :=
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

/-! ## Section 4: `ValidityVisitor.validatePlace` on `.local` Places -/

theorem refLayoutDataForTy_isSized (ty : MirTy) :
    (refLayoutDataForTy ty).isSized = true := by
  cases ty with
  | unit | never | bool | int _ _ | tuple _ | ref _ _ | rawPtr _ _
  | unsupported => rfl
  | enum ety =>
    dsimp only [refLayoutDataForTy, refEnumLayoutData]
    cases ety.tagRepr <;> rfl

theorem wrappingRange_full_contains_truncateBits (w : IntWidth)
    (x : BitVec 128) :
    (refFullWrappingRangeSize (toMiriSize w)).contains (truncateBits w x) =
      true := by
  have h_le : (truncateBits w x).toNat ≤ HPow.hPow 2 w.bitWidth - 1 := by
    have h_lt : (truncateBits w x).toNat < HPow.hPow 2 w.bitWidth := by
      rw [toNat_truncateBits]
      exact Nat.mod_lt x.toNat (intWidth_modulus_pos w)
    exact Nat.le_sub_one_of_lt h_lt
  cases w with
  | i8 =>
    have hr : refFullWrappingRangeSize (toMiriSize .i8) =
        ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 (HPow.hPow 2 IntWidth.i8.bitWidth - 1)⟩ := by
      decide
    rw [hr]
    dsimp only [Miri.ABI.WrappingRange.contains]
    change (if 0 ≤ HPow.hPow 2 IntWidth.i8.bitWidth - 1 then
      decide (0 ≤ (truncateBits .i8 x).toNat) &&
        decide ((truncateBits .i8 x).toNat ≤ HPow.hPow 2 IntWidth.i8.bitWidth - 1)
      else _) = true
    rw [ite_eq_left (by decide), decide_eq_true (Nat.zero_le _),
      decide_eq_true h_le]
    rfl
  | i16 =>
    have hr : refFullWrappingRangeSize (toMiriSize .i16) =
        ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 (HPow.hPow 2 IntWidth.i16.bitWidth - 1)⟩ := by
      decide
    rw [hr]
    dsimp only [Miri.ABI.WrappingRange.contains]
    change (if 0 ≤ HPow.hPow 2 IntWidth.i16.bitWidth - 1 then
      decide (0 ≤ (truncateBits .i16 x).toNat) &&
        decide ((truncateBits .i16 x).toNat ≤ HPow.hPow 2 IntWidth.i16.bitWidth - 1)
      else _) = true
    rw [ite_eq_left (by decide), decide_eq_true (Nat.zero_le _),
      decide_eq_true h_le]
    rfl
  | i32 =>
    have hr : refFullWrappingRangeSize (toMiriSize .i32) =
        ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 (HPow.hPow 2 IntWidth.i32.bitWidth - 1)⟩ := by
      decide
    rw [hr]
    dsimp only [Miri.ABI.WrappingRange.contains]
    change (if 0 ≤ HPow.hPow 2 IntWidth.i32.bitWidth - 1 then
      decide (0 ≤ (truncateBits .i32 x).toNat) &&
        decide ((truncateBits .i32 x).toNat ≤ HPow.hPow 2 IntWidth.i32.bitWidth - 1)
      else _) = true
    rw [ite_eq_left (by decide), decide_eq_true (Nat.zero_le _),
      decide_eq_true h_le]
    rfl
  | i64 =>
    have hr : refFullWrappingRangeSize (toMiriSize .i64) =
        ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 (HPow.hPow 2 IntWidth.i64.bitWidth - 1)⟩ := by
      decide
    rw [hr]
    dsimp only [Miri.ABI.WrappingRange.contains]
    change (if 0 ≤ HPow.hPow 2 IntWidth.i64.bitWidth - 1 then
      decide (0 ≤ (truncateBits .i64 x).toNat) &&
        decide ((truncateBits .i64 x).toNat ≤ HPow.hPow 2 IntWidth.i64.bitWidth - 1)
      else _) = true
    rw [ite_eq_left (by decide), decide_eq_true (Nat.zero_le _),
      decide_eq_true h_le]
    rfl
  | isize =>
    have hr : refFullWrappingRangeSize (toMiriSize .isize) =
        ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 (HPow.hPow 2 IntWidth.isize.bitWidth - 1)⟩ := by
      decide
    rw [hr]
    dsimp only [Miri.ABI.WrappingRange.contains]
    change (if 0 ≤ HPow.hPow 2 IntWidth.isize.bitWidth - 1 then
      decide (0 ≤ (truncateBits .isize x).toNat) &&
        decide ((truncateBits .isize x).toNat ≤ HPow.hPow 2 IntWidth.isize.bitWidth - 1)
      else _) = true
    rw [ite_eq_left (by decide), decide_eq_true (Nat.zero_le _),
      decide_eq_true h_le]
    rfl
  | i128 =>
    have hr : refFullWrappingRangeSize (toMiriSize .i128) =
        ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 (HPow.hPow 2 IntWidth.i128.bitWidth - 1)⟩ := by
      decide
    rw [hr]
    dsimp only [Miri.ABI.WrappingRange.contains]
    change (if 0 ≤ HPow.hPow 2 IntWidth.i128.bitWidth - 1 then
      decide (0 ≤ (truncateBits .i128 x).toNat) &&
        decide ((truncateBits .i128 x).toNat ≤ HPow.hPow 2 IntWidth.i128.bitWidth - 1)
      else _) = true
    rw [ite_eq_left (by decide), decide_eq_true (Nat.zero_le _),
      decide_eq_true h_le]
    rfl

theorem refEnum_isVariantUninhabited_false (ety : EnumTy) (tagW : IntWidth)
    (tagS : Bool) (v : Nat)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_lt : v < ety.discriminants.length) :
    (refEnumLayoutData ety).isVariantUninhabited v = false := by
  dsimp only [refEnumLayoutData]
  rw [h_tr]
  dsimp only [Miri.ABI.LayoutData.isVariantUninhabited]
  have h_get : (Array.mk (ety.discriminants.map
      (fun _ => refInhabitedVariantLayout)))[v]? =
      some refInhabitedVariantLayout := by
    rw [array_getElem?_eq_mirGetElem?, mirGetElem?_map]
    let ⟨d, hd⟩ := mirGetElem?_some_of_lt h_lt
    rw [hd]
    rfl
  rw [h_get]
  rfl

private theorem afterLocalRead_no_race
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (localId : LocalId)
    (h_frames : st.stack.frames = (Array.mk [frame]))
    (h_dr : frame.extra.dataRace = none) :
    Miri.Interpreter.MachineHooks.afterLocalRead localId st = .ok () st := by
  have h_curr : st.stack.currentFrame? = some frame := by
    dsimp only [Miri.Interpreter.Stack.currentFrame?]
    rw [h_frames]; rfl
  dsimp only [Miri.Interpreter.MachineHooks.afterLocalRead,
    Miri.Interpreter.MachineHooks.currentFrame,
    get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_curr]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_dr]
  rfl

private theorem refBaseCompilerHooks_debugAssertions (types : List MirTy) :
    (refBaseCompilerHooks types).debugAssertions = false := rfl

private theorem refBaseCompilerHooks_validationInProgress (types : List MirTy) :
    (refBaseCompilerHooks types).validationInProgress = (fun st => .ok false st) := rfl

private theorem refBaseCompilerHooks_projection (types : List MirTy) :
    (refBaseCompilerHooks types).projection = (fun _ st => .ok (refProjectionCx types) st) := rfl

private theorem placeToOp_local_immediate (types : List MirTy)
    (c : Choice) (localId : LocalId) (ty : MirTy)
    (imm : Immediate Miri.Memory.Provenance)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_frames : st.stack.frames = (Array.mk [frame]))
    (h_dr : frame.extra.dataRace = none)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate imm), some (refLocalLayoutForTy types ty)⟩) :
    Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place c
        ⟨.local 0 localId none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types ty⟩ st =
      .ok ⟨.immediate imm, refLocalLayoutForTy types ty⟩ st := by
  have h_curr : st.stack.currentFrame? = some frame := by
    dsimp only [Miri.Interpreter.Stack.currentFrame?]
    rw [h_frames]; rfl
  have h_fidx : st.stack.frameIndex = .ok 0 := by
    dsimp only [Miri.Interpreter.Stack.frameIndex]
    rw [h_frames]; rfl
  have h_op : frame.getLocalOperand localId = .ok (.immediate imm) := by
    dsimp only [Miri.Interpreter.Frame.getLocalOperand]
    rw [h_get]; rfl
  have h_sz : (refLocalLayoutForTy types ty).layout.isSized = true :=
    refLayoutDataForTy_isSized ty
  dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
    refBasePlaceProjectionHooks, Miri.Interpreter.PlaceMachine.placeHooks,
    Miri.Interpreter.PlaceMachine.localToOp,
    Miri.Interpreter.PlaceMachine.localToOpCore,
    Miri.Interpreter.PlaceMachine.layoutLocal,
    Miri.Interpreter.MachineHooks.currentFrame]
  simp only [get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    refBaseCompilerHooks_debugAssertions,
    refBaseCompilerHooks_validationInProgress,
    h_fidx, h_curr, h_get, h_op, h_sz,
    bne_self_eq_false, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [afterLocalRead_no_race frame st localId h_frames h_dr]

private theorem placeToOp_local_field0_scalar_enum (types : List MirTy)
    (c : Choice) (localId : LocalId) (ety : EnumTy) (tagW : IntWidth)
    (tagS : Bool) (imm : Immediate Miri.Memory.Provenance)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_frames : st.stack.frames = (Array.mk [frame]))
    (h_dr : frame.extra.dataRace = none)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate imm), some (refLocalLayoutForTy types (.enum ety))⟩)
    (h_imm_ok : imm = .uninit ∨ ∃ sc, imm = .scalar sc ∧ sc.size = toMiriSize tagW) :
    Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place c
        ⟨.local 0 localId (some Size.ZERO) (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types (.int tagW tagS)⟩ st =
      .ok ⟨.immediate imm, refLocalLayoutForTy types (.int tagW tagS)⟩ st := by
  have h_curr : st.stack.currentFrame? = some frame := by
    dsimp only [Miri.Interpreter.Stack.currentFrame?]
    rw [h_frames]; rfl
  have h_fidx : st.stack.frameIndex = .ok 0 := by
    dsimp only [Miri.Interpreter.Stack.frameIndex]
    rw [h_frames]; rfl
  have h_op : frame.getLocalOperand localId = .ok (.immediate imm) := by
    dsimp only [Miri.Interpreter.Frame.getLocalOperand]
    rw [h_get]; rfl
  have h_sz : (refLocalLayoutForTy types (.enum ety)).layout.isSized = true :=
    refLayoutDataForTy_isSized (.enum ety)
  have h_off :
      (⟨.immediate imm, refLocalLayoutForTy types (.enum ety)⟩ :
          OpTy Miri.Memory.Provenance).offset (refProjectionCx types)
        Size.ZERO (refLocalLayoutForTy types (.int tagW tagS)) =
      .ok ⟨.immediate imm, refLocalLayoutForTy types (.int tagW tagS)⟩ := by
    dsimp only [OpTy.offset, OpTy.offsetWithMeta, refProjectionCx,
      Miri.Interpreter.projectionImmediateOffset, refLocalLayoutForTy,
      refLayoutDataForTy, refEnumLayoutData]
    rw [h_tr]
    cases h_imm_ok with
    | inl h_u =>
      subst h_u
      cases tagW <;> cases tagS <;> rfl
    | inr h_s =>
      let ⟨sc, h_eq, _⟩ := h_s
      subst h_eq
      cases tagW <;> cases tagS <;> rfl
  dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
    refBasePlaceProjectionHooks, Miri.Interpreter.PlaceMachine.placeHooks,
    Miri.Interpreter.PlaceMachine.localToOp,
    Miri.Interpreter.PlaceMachine.localToOpCore,
    Miri.Interpreter.PlaceMachine.layoutLocal,
    Miri.Interpreter.MachineHooks.currentFrame]
  simp only [get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    refBaseCompilerHooks_debugAssertions,
    refBaseCompilerHooks_validationInProgress,
    refBaseCompilerHooks_projection,
    h_fidx, h_curr, h_get, h_op, h_sz,
    bne_self_eq_false, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [afterLocalRead_no_race frame st localId h_frames h_dr]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_off]
  rfl

private theorem validityMemory_readImmediate_imm_scalar
    (types : List MirTy) (ty : MirTy)
    (sc : Scalar Miri.Memory.Provenance) (expected : ExpectedValue)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_prim : (ty = .bool) ∨ (∃ w s, ty = .int w s)) :
    Miri.Interpreter.ValidityMemory.readImmediate refValidityMemoryEnv
        ⟨.immediate (.scalar sc), refLocalLayoutForTy types ty⟩ expected st =
      .ok ⟨.scalar sc, refLocalLayoutForTy types ty⟩ st := by
  cases h_prim with
  | inl h_b =>
    subst h_b
    cases st with | mk stack machine => rfl
  | inr h_i =>
    let ⟨w, s, h_eq⟩ := h_i
    subst h_eq
    cases st with
    | mk stack machine =>
      cases w <;> cases s <;> rfl

private theorem validityMemory_readImmediate_imm_uninit
    (types : List MirTy) (ty : MirTy) (expected : ExpectedValue)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_prim : (ty = .bool) ∨ (∃ w s, ty = .int w s)) :
    ∃ msg,
      Miri.Interpreter.ValidityMemory.readImmediate refValidityMemoryEnv
          ⟨.immediate .uninit, refLocalLayoutForTy types ty⟩ expected st =
        .error (.undefinedBehavior msg) st := by
  cases h_prim with
  | inl h_b =>
    subst h_b
    cases st with | mk stack machine => exact ⟨_, rfl⟩
  | inr h_i =>
    let ⟨w, s, h_eq⟩ := h_i
    subst h_eq
    cases st with
    | mk stack machine =>
      cases w <;> cases s <;> exact ⟨_, rfl⟩

private theorem clearPlaceProvenance_imm_no_prov
    (types : List MirTy) (c : Choice) (place : RuntimePlace Miri.Memory.Provenance)
    (imm : Immediate Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_toOp : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
        c place st = .ok ⟨.immediate imm, place.layout⟩ st)
    (h_noprov : imm.hasProvenance = false) :
    Miri.Interpreter.ValidityMemory.clearPlaceProvenance refValidityMemoryEnv
        (refBasePlaceProjectionHooks types).place c
        (fun st => .ok false st) (fun _ _ st => .ok () st) place st =
      .ok () st := by
  dsimp only [Miri.Interpreter.ValidityMemory.clearPlaceProvenance,
    bind, Bind.bind, EStateM.bind]
  rw [h_toOp]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_noprov]
  rfl

private theorem scalar_fromBool_toBool (b : Bool) :
    (Scalar.fromBool (Prov := Miri.Memory.Provenance) b).toBool = .ok b := by
  cases b <;> rfl

/-- Shorthand for the bound `ValidityVisitor.Hooks` used by `refCompilerHooks`
and `ExecutionMachine.withValidation`. Kept un-unfolded during `visit` proofs
via projection lemmas below. -/
private noncomputable def refValHooks (types : List MirTy) :=
  Miri.Interpreter.TypedMachineBindings.bindValidity
    (refValidityHooks types) refRetagHooks 8

private theorem refValHooks_typeName (types : List MirTy) (c : Choice)
    (tyId : TyId) (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (refValHooks types).typeName c tyId st = .ok "" st := rfl

private theorem refValHooks_withGhostValidation (types : List MirTy)
    {A : Type} (act : Miri.Interpreter.ValidityVisitor.M
      (Miri.Interpreter.MachineHooks.State Unit RefUser) A) :
    (refValHooks types).withGhostValidation act = act := rfl

private theorem refValHooks_debugAssertions (types : List MirTy) :
    (refValHooks types).debugAssertions = false := rfl

private theorem refValHooks_projection (types : List MirTy) :
    (refValHooks types).projection = refBasePlaceProjectionHooks types := rfl

private theorem refValHooks_discriminant (types : List MirTy) :
    (refValHooks types).discriminant = refValidityDiscriminantHooks types := rfl

private theorem refValHooks_toOp (types : List MirTy) :
    (refValHooks types).toOp =
      Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place := rfl

private theorem refValHooks_readImmediate (types : List MirTy) (c : Choice)
    (place : RuntimePlace Miri.Memory.Provenance) (exp : ExpectedValue) :
    (refValHooks types).readImmediate c place exp =
      Bind.bind
        (Miri.Interpreter.placeToOp
          (refBasePlaceProjectionHooks types).place c place)
        (fun op =>
          Miri.Interpreter.ValidityMemory.readImmediate refValidityMemoryEnv
            op exp) := rfl

private theorem refValHooks_clearProvenance (types : List MirTy) (c : Choice)
    (place : RuntimePlace Miri.Memory.Provenance) :
    (refValHooks types).clearProvenance c place =
      Miri.Interpreter.ValidityMemory.clearPlaceProvenance refValidityMemoryEnv
        (refBasePlaceProjectionHooks types).place c
        (fun st => .ok false st) (fun _ _ st => .ok () st) place := rfl

private theorem refValHooks_classify (types : List MirTy) (c : Choice)
    (tyId : TyId) (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (refValHooks types).classify c tyId st =
      match resolveTy types tyId with
      | some .bool => .ok .boolean st
      | some (.int _ _) => .ok .integer st
      | some .unit => .ok (.aggregate false false false) st
      | some .never => .ok .never st
      | some (.enum _) => .ok (.aggregate false false true) st
      | _ => .error (.invalidProgram "unsupported validity type") st := rfl

private theorem refValHooks_opsemInhabited (types : List MirTy) (c : Choice)
    (tyId : TyId) (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (refValHooks types).opsemInhabited c tyId st =
      match resolveTy types tyId with
      | some .never => .ok false st
      | some _ => .ok true st
      | none => .error (.invalidProgram "unknown TyId in opsemInhabited") st := rfl

private theorem refValHooks_fieldPath (types : List MirTy) (c : Choice)
    (l : LocalLayout) (i : Nat) (tyId : TyId)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (refValHooks types).fieldPath c l i tyId st = .ok .enumTag st := rfl

private theorem refValHooks_variantPath (types : List MirTy) (c : Choice)
    (l : LocalLayout) (v : Nat)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (refValHooks types).variantPath c l v st = .ok (.variant "") st := rfl

private theorem ite_true_eq {α : Type} (a b : α) :
    (if (true = true) then a else b) = a := rfl

private theorem ite_false_eq {α : Type} (a b : α) :
    (if (false = true) then a else b) = b := rfl

private theorem ite_not_true_eq {α : Type} (a b : α) :
    (if (!true) = true then a else b) = b := rfl

private theorem eStateM_bind_pure {ε σ α β : Type} (a : α)
    (f : α → EStateM ε σ β) :
    EStateM.bind (EStateM.pure a) f = f a := rfl

private theorem eStateM_bind_ok {ε σ α β : Type} {m : EStateM ε σ α}
    {f : α → EStateM ε σ β} {a : α} {st st' : σ}
    (h : m st = .ok a st') :
    EStateM.bind m f st = f a st' := by
  dsimp only [EStateM.bind]
  rw [h]

private theorem eStateM_bind_err {ε σ α β : Type} {m : EStateM ε σ α}
    {f : α → EStateM ε σ β} {e : ε} {st st' : σ}
    (h : m st = .error e st') :
    EStateM.bind m f st = .error e st' := by
  dsimp only [EStateM.bind]
  rw [h]

private theorem refLocalLayoutForTy_ty (types : List MirTy) (ty : MirTy) :
    (refLocalLayoutForTy types ty).ty = tyIdFor types ty := rfl

private theorem readDiscriminant_validity_scalar_enum
    (types : List MirTy) (c : Choice) (ety : EnumTy) (tagW : IntWidth)
    (tagS : Bool) (variant disc : Nat)
    (op : Miri.Interpreter.Operand Miri.Memory.Provenance)
    (tagOp : OpTy Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_adm : enumAdmitted ety = true)
    (h_res : resolveTy types (tyIdFor types (.enum ety)) = some (.enum ety))
    (h_get_d : MirSemantics.getElem? ety.discriminants variant = some disc)
    (h_proj :
      Miri.Interpreter.OperandMachine.field (refValidityOperandHooks types) c
        ⟨op, refLocalLayoutForTy types (.enum ety)⟩ 0 st = .ok tagOp st)
    (h_ri :
      Miri.Interpreter.PlaceMachine.readImmediate
        { refAccessConfig with ghostMode := true, deinitMovedPlace := false }
        tagOp st =
      .ok ⟨.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))),
          refLocalLayoutForTy types (.int tagW tagS)⟩ st) :
    Miri.Interpreter.Discriminant.readDiscriminant
        (refValidityDiscriminantHooks types) c
        ⟨op, refLocalLayoutForTy types (.enum ety)⟩ st =
      .ok variant st := by
  let ⟨h_bnds, h_pw, h_tag_all⟩ := enumAdmitted_parts h_adm
  have h_v_lt : variant < ety.discriminants.length :=
    mirGetElem?_lt_of_some h_get_d
  have h_ref_adm : refEnumAdmitted ety = true := by
    rw [refEnumAdmitted_eq]; exact h_adm
  have h_tag_ok : tagBitsToDiscrBits tagW tagS ety.discrWidth
      (truncateBits tagW (BitVec.ofNat 128 disc)) = BitVec.ofNat 128 disc := by
    rw [h_tr] at h_tag_all
    have h_elem := list_all_mirGetElem?
      (p := fun d =>
        tagBitsToDiscrBits tagW tagS ety.discrWidth
          (truncateBits tagW (BitVec.ofNat 128 d)) == BitVec.ofNat 128 d)
      h_tag_all h_get_d
    exact eq_of_beq h_elem
  have h_find : refFindDiscrVariant? (BitVec.ofNat 128 disc) ety.discriminants =
      some variant := by
    rw [refFindDiscrVariant?_eq]
    exact findDiscrVariant?_of_enumAdmitted h_adm h_get_d
  have h_int_w : toMiriSize (intWidthOfMiriInteger (toMiriInteger tagW)) =
      toMiriSize tagW := by
    cases tagW <;> rfl
  have h_signed_eq :
      (refScalarLayoutData (intWidthOfMiriInteger (toMiriInteger tagW)) tagS).backendRepr.isSigned =
        .ok tagS := by
    cases tagW <;> cases tagS <;> rfl
  have h_signed_eq2 :
      (refScalarLayoutData tagW tagS).backendRepr.isSigned = .ok tagS := by
    cases tagW <;> cases tagS <;> rfl
  have h_vr :
      (Miri.ABI.Scalar.Union (value := .Int (toMiriInteger tagW) tagS)).validRange
          RuntimeTargetDataLayout.default =
        .ok (refFullWrappingRangeSize (toMiriSize tagW)) := by
    cases tagW <;> cases tagS <;> rfl
  have h_toBits :
      (miriScalar tagW (BitVec.ofNat 128 disc)).toBits (toMiriSize tagW) =
        .ok (truncateBits tagW (BitVec.ofNat 128 disc)) :=
    miriScalar_toUInt tagW (BitVec.ofNat 128 disc)
  have h_discr_trunc :
      (toMiriSize ety.discrWidth).truncate
        (if tagS then
          BitVec.ofInt 128 (signExtendBits tagW (truncateBits tagW (BitVec.ofNat 128 disc)))
        else
          truncateBits tagW (BitVec.ofNat 128 disc)) =
      .ok (BitVec.ofNat 128 disc) := by
    rw [size_truncate_eq]
    have h_eq_td :
        truncateBits ety.discrWidth
          (if tagS then
            BitVec.ofInt 128 (signExtendBits tagW (truncateBits tagW (BitVec.ofNat 128 disc)))
          else
            truncateBits tagW (BitVec.ofNat 128 disc)) =
        tagBitsToDiscrBits tagW tagS ety.discrWidth
          (truncateBits tagW (BitVec.ofNat 128 disc)) := by
      cases tagS with
      | false =>
        dsimp only [tagBitsToDiscrBits]
        rw [ite_false_eq, ite_false_eq, truncateBits_idem]
      | true =>
        dsimp only [tagBitsToDiscrBits]
        rw [ite_true_eq, ite_true_eq, bitVec_ofInt_eq]
    rw [h_eq_td, h_tag_ok]
  have h_dl : (refDiscriminantLeaves types).discriminantLayout c
      (tyIdFor types (.enum ety)) st =
      .ok ⟨tyIdFor types (.int ety.discrWidth ety.discrSigned),
        refScalarLayoutData ety.discrWidth ety.discrSigned⟩ st := by
    dsimp only [refDiscriminantLeaves]
    rw [h_res]
    dsimp only
    rw [h_ref_adm]
    rfl
  have h_vars : (refLocalLayoutForTy types (.enum ety)).layout.variants =
      .Multiple (.Union (value := .Int (toMiriInteger tagW) tagS)) .Direct 0
        (ety.discriminants.map (fun _ => refInhabitedVariantLayout)).toArray := by
    dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
    rw [h_tr]
  have h_tl : (refDiscriminantLeaves types).tagLayout c
      (.Union (value := .Int (toMiriInteger tagW) tagS)) st =
      .ok (refLocalLayoutForTy types (.int (intWidthOfMiriInteger (toMiriInteger tagW)) tagS)) st := rfl
  dsimp only [Miri.Interpreter.Discriminant.readDiscriminant,
    refValidityDiscriminantHooks, bind, Bind.bind, EStateM.bind]
  rw [refLocalLayoutForTy_ty, h_dl]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [h_vars]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [h_tl]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [h_proj]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [h_ri]
  have h_sz_ne :
      ((refLocalLayoutForTy types (.int (intWidthOfMiriInteger (toMiriInteger tagW)) tagS)).layout.size !=
        (refLocalLayoutForTy types (.int tagW tagS)).layout.size) = false := by
    cases tagW <;> cases tagS <;> rfl
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [h_sz_ne, ite_false_eq]
  change (EStateM.bind (match (refScalarLayoutData (intWidthOfMiriInteger (toMiriInteger tagW)) tagS).backendRepr.isSigned with
    | .ok v => EStateM.pure v
    | .error _ => EStateM.throw (StepError.invalidProgram "discriminant requires scalar backend representation"))
    (fun _ => EStateM.bind (match (refScalarLayoutData tagW tagS).backendRepr.isSigned with
      | .ok v => EStateM.pure v
      | .error _ => EStateM.throw (StepError.invalidProgram "discriminant requires scalar backend representation"))
      _) st) = .ok variant st
  rw [h_signed_eq, h_signed_eq2]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [bne_self_eq_false, ite_false_eq]
  have h_tb :
      (miriScalar tagW (BitVec.ofNat 128 disc)).toBits
        (refLocalLayoutForTy types
          (.int (intWidthOfMiriInteger (toMiriInteger tagW)) tagS)).layout.size =
      .ok (truncateBits tagW (BitVec.ofNat 128 disc)) := by
    dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refScalarLayoutData,
      refBaseLayoutData]
    rw [h_int_w]
    exact h_toBits
  have h_se :
      (refLocalLayoutForTy types
          (.int (intWidthOfMiriInteger (toMiriInteger tagW)) tagS)).layout.size.signExtend
        (truncateBits tagW (BitVec.ofNat 128 disc)) =
      .ok (signExtendBits tagW (truncateBits tagW (BitVec.ofNat 128 disc))) := by
    dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refScalarLayoutData,
      refBaseLayoutData]
    rw [h_int_w]
    exact size_signExtend_eq tagW (truncateBits tagW (BitVec.ofNat 128 disc))
  have h_vfd :
      (refDiscriminantLeaves types).variantForDiscriminant c
        (tyIdFor types (.enum ety)) (BitVec.ofNat 128 disc) st =
      .ok (some variant) st := by
    dsimp only [refDiscriminantLeaves]
    rw [h_res]
    dsimp only
    rw [h_find]
  have h_uninh :
      (refLocalLayoutForTy types (.enum ety)).layout.isVariantUninhabited variant =
        false := by
    dsimp only [refLocalLayoutForTy, refLayoutDataForTy]
    exact refEnum_isVariantUninhabited_false ety tagW tagS variant h_tr h_v_lt
  change (EStateM.bind
    (EStateM.pure (Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
      (miriScalar tagW (BitVec.ofNat 128 disc)))) _ st) = .ok variant st
  rw [eStateM_bind_pure]
  change (EStateM.bind
    (EStateM.pure (ScalarIntCastResult.integer
      (miriScalar tagW (BitVec.ofNat 128 disc)))) _ st) = .ok variant st
  rw [eStateM_bind_pure]
  dsimp only
  rw [h_tb]
  change (EStateM.bind
    (EStateM.pure (truncateBits tagW (BitVec.ofNat 128 disc))) _ st) = .ok variant st
  rw [eStateM_bind_pure]
  change (EStateM.bind (match (Miri.ABI.Scalar.Union (value := .Int (toMiriInteger tagW) tagS)).validRange
      RuntimeTargetDataLayout.default with
    | .ok v => EStateM.pure v
    | .error _ => _) _ st) = .ok variant st
  rw [h_vr]
  dsimp only
  rw [eStateM_bind_pure, wrappingRange_full_contains_truncateBits tagW (BitVec.ofNat 128 disc),
    ite_not_true_eq]
  cases tagS with
  | false =>
    rw [ite_false_eq, eStateM_bind_pure]
    rw [ite_false_eq] at h_discr_trunc
    have h_dt :
        (refScalarLayoutData ety.discrWidth ety.discrSigned).size.truncate
          (truncateBits tagW (BitVec.ofNat 128 disc)) =
        .ok (BitVec.ofNat 128 disc) := h_discr_trunc
    rw [h_dt]
    change (EStateM.bind (EStateM.pure (BitVec.ofNat 128 disc)) _ st) = .ok variant st
    rw [eStateM_bind_pure, eStateM_bind_ok h_vfd]
    dsimp only
    rw [eStateM_bind_pure, h_uninh, ite_false_eq]
    rfl
  | true =>
    rw [ite_true_eq, h_se]
    change (EStateM.bind (EStateM.pure (signExtendBits tagW (truncateBits tagW (BitVec.ofNat 128 disc)))) _ st) =
      .ok variant st
    rw [eStateM_bind_pure, eStateM_bind_pure]
    rw [ite_true_eq] at h_discr_trunc
    have h_dt :
        (refScalarLayoutData ety.discrWidth ety.discrSigned).size.truncate
          (BitVec.ofInt 128 (signExtendBits tagW (truncateBits tagW (BitVec.ofNat 128 disc)))) =
        .ok (BitVec.ofNat 128 disc) := h_discr_trunc
    rw [h_dt]
    change (EStateM.bind (EStateM.pure (BitVec.ofNat 128 disc)) _ st) = .ok variant st
    rw [eStateM_bind_pure, eStateM_bind_ok h_vfd]
    dsimp only
    rw [eStateM_bind_pure, h_uninh, ite_false_eq]
    rfl

private theorem readDiscriminant_validity_local_scalar_enum
    (types : List MirTy) (c : Choice) (ety : EnumTy) (tagW : IntWidth)
    (tagS : Bool) (variant disc : Nat)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_adm : enumAdmitted ety = true)
    (h_res : resolveTy types (tyIdFor types (.enum ety)) = some (.enum ety))
    (h_get_d : MirSemantics.getElem? ety.discriminants variant = some disc)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    Miri.Interpreter.Discriminant.readDiscriminant
        (refValidityDiscriminantHooks types) c
        ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))),
          refLocalLayoutForTy types (.enum ety)⟩ st =
      .ok variant st := by
  have h_proj :
      Miri.Interpreter.OperandMachine.field (refValidityOperandHooks types) c
        ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))),
          refLocalLayoutForTy types (.enum ety)⟩ 0 st =
      .ok ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))),
          refLocalLayoutForTy types (.int tagW tagS)⟩ st := by
    dsimp only [Miri.Interpreter.OperandMachine.field, refValidityOperandHooks,
      refBaseCompilerHooks, bind, Bind.bind, EStateM.bind, pure, Pure.pure,
      EStateM.pure]
    have h_pf : Miri.Interpreter.projectField (refProjectionCx types)
        ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))),
          refLocalLayoutForTy types (.enum ety)⟩ 0 =
        .ok ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))),
          refLocalLayoutForTy types (.int tagW tagS)⟩ := by
      dsimp only [Miri.Interpreter.projectField, refProjectionCx,
        refProjectFieldLayout, refLocalLayoutForTy, refLayoutDataForTy,
        refEnumLayoutData]
      rw [h_res]
      dsimp only
      rw [h_tr]
      cases tagW <;> cases tagS <;> rfl
    rw [h_pf]
    rfl
  have h_ri :
      Miri.Interpreter.PlaceMachine.readImmediate
        { refAccessConfig with ghostMode := true, deinitMovedPlace := false }
        ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))),
          refLocalLayoutForTy types (.int tagW tagS)⟩ st =
      .ok ⟨.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))),
          refLocalLayoutForTy types (.int tagW tagS)⟩ st := by
    cases st with
    | mk stack machine =>
      cases machine with
      | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
          user pendingMoveDeinit =>
        dsimp only at h_pmd
        subst h_pmd
        cases tagW <;> cases tagS <;> rfl
  exact readDiscriminant_validity_scalar_enum types c ety tagW tagS variant disc
    _ _ st h_tr h_adm h_res h_get_d h_proj h_ri

private theorem resolveTy_tyIdFor_int (types : List MirTy) (w : IntWidth)
    (s : Bool) :
    resolveTy types (tyIdFor types (.int w s)) = some (.int w s) := by
  cases w <;> cases s <;> exact resolveTy_tyIdFor_of_aux (h := rfl)

private theorem forIn_empty_array {ε σ α β : Type} (init : β)
    (f : α → β → EStateM ε σ (ForInStep β)) (st : σ) :
    forIn ((Array.mk []) : Array α) init f st = .ok init st := rfl

private theorem forIn_singleton_array {ε σ α β : Type} (x : α) (init : β)
    (f : α → β → EStateM ε σ (ForInStep β)) (st : σ) :
    forIn ((Array.mk [x]) : Array α) init f st =
      (match f x init st with
      | .ok (.done b) s => .ok b s
      | .ok (.yield b) s => .ok b s
      | .error e s => .error e s) := by
  have h : forIn ((Array.mk [x]) : Array α) init f = forIn ([x] : List α) init f :=
    (Array.forIn_toList (xs := (Array.mk [x])) (b := init) (f := f)).symm
  rw [h]
  dsimp only [forIn, forIn', List.forIn', List.forIn'.loop,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  cases f x init st with
  | ok r s => cases r <;> rfl
  | error e s => rfl

private theorem validatePlace_shallow_local_step (types : List MirTy)
    (c : Choice) (place : RuntimePlace Miri.Memory.Provenance)
    (imm : Immediate Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_toOp : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
      c place st = .ok ⟨.immediate imm, place.layout⟩ st)
    (h_vis :
      let initSess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
        path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := none
      }
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c 8
        initSess place st = .ok initSess st) :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooks types) c 8
        place false true st = .ok () st := by
  dsimp only [Miri.Interpreter.ValidityVisitor.validatePlace,
    bind, Bind.bind, EStateM.bind]
  rw [refValHooks_typeName]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    ite_true, ite_false]
  rw [refValHooks_withGhostValidation, ite_true_eq]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_toOp, h_toOp]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [ite_false_eq, h_vis]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [Miri.Interpreter.ValidityVisitor.resetPadding_no_ranges _ _ _ _ rfl]
  rfl

private theorem validatePlace_shallow_local_ub_step (types : List MirTy)
    (c : Choice) (place : RuntimePlace Miri.Memory.Provenance)
    (imm : Immediate Miri.Memory.Provenance)
    (st st' : Miri.Interpreter.MachineHooks.State Unit RefUser) (msg : String)
    (h_toOp : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
      c place st = .ok ⟨.immediate imm, place.layout⟩ st)
    (h_vis :
      let initSess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
        path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := none
      }
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c 8
        initSess place st = .error (.undefinedBehavior msg) st') :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooks types) c 8
        place false true st = .error (.undefinedBehavior msg) st' := by
  dsimp only [Miri.Interpreter.ValidityVisitor.validatePlace,
    bind, Bind.bind, EStateM.bind]
  rw [refValHooks_typeName]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    ite_true, ite_false]
  rw [refValHooks_withGhostValidation, ite_true_eq]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_toOp, h_toOp]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [ite_false_eq, h_vis]

private theorem visit_local_fieldless_enum (types : List MirTy) (c : Choice)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (place : RuntimePlace Miri.Memory.Provenance) (ety : EnumTy) (variant : Nat)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_ty : place.layout.ty = tyIdFor types (.enum ety))
    (h_res : resolveTy types (tyIdFor types (.enum ety)) = some (.enum ety))
    (h_fields : place.layout.layout.fields = .Arbitrary (Array.mk []) (Array.mk []))
    (h_vars : place.layout.layout.variants = .Single variant)
    (h_rt : session.ctfeMode = none) :
    Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
        session place st = .ok session st := by
  have h_ne_box :
      (Miri.Interpreter.ValidityVisitor.TypeKind.aggregate false false true == .box) =
        false := rfl
  dsimp only [Miri.Interpreter.ValidityVisitor.visit,
    bind, Bind.bind, EStateM.bind]
  rw [h_ty, refValHooks_classify, h_res]
  dsimp only
  change (match (EStateM.Result.ok none st :
      EStateM.Result StepError (Miri.Interpreter.MachineHooks.State Unit RefUser)
        (Option (Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance))) with
    | EStateM.Result.ok a s => _
    | EStateM.Result.error e s => EStateM.Result.error e s) = _
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_rt, h_ne_box, ite_false_eq, h_fields, h_vars]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [forIn_empty_array]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_opsemInhabited, h_res]
  dsimp only
  rw [refValHooks_debugAssertions]
  cases session with
  | mk path flags mode tracking bytes =>
    cases flags with
    | mk rst md =>
      dsimp only at h_rt
      subst h_rt
      rfl

private theorem visit_local_int_ok (types : List MirTy) (c : Choice)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (place : RuntimePlace Miri.Memory.Provenance) (w : IntWidth) (s : Bool)
    (bits : BitVec 128)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_lay : place.layout = refLocalLayoutForTy types (.int w s))
    (h_res : resolveTy types (tyIdFor types (.int w s)) = some (.int w s))
    (h_db : session.dataBytes = none)
    (h_toOp : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
      c place st = .ok ⟨.immediate (.scalar (.fromScalarInt (miriScalar w bits))),
        refLocalLayoutForTy types (.int w s)⟩ st) :
    Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
        session place st = .ok session st := by
  cases session with
  | mk path flags mode tracking bytes =>
    cases flags with
    | mk rst md =>
      dsimp only at h_db
      subst h_db
      have h_toOp' : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
          c place st = .ok ⟨.immediate (.scalar (.fromScalarInt (miriScalar w bits))),
            place.layout⟩ st := by
        rw [h_lay]; exact h_toOp
      have h_ri : (refValHooks types).readImmediate c place .integer st =
          .ok ⟨.scalar (.fromScalarInt (miriScalar w bits)),
            refLocalLayoutForTy types (.int w s)⟩ st := by
        rw [refValHooks_readImmediate]
        dsimp only [bind, Bind.bind, EStateM.bind]
        rw [h_toOp]
        exact validityMemory_readImmediate_imm_scalar types (.int w s)
          (.fromScalarInt (miriScalar w bits)) .integer st (Or.inr ⟨w, s, rfl⟩)
      dsimp only [Miri.Interpreter.ValidityVisitor.visit,
        bind, Bind.bind, EStateM.bind]
      rw [h_lay, refLocalLayoutForTy_ty, refValHooks_classify, h_res]
      dsimp only
      change (EStateM.bind (EStateM.bind ((refValHooks types).readImmediate c place .integer) _) _ st) = _
      dsimp only [EStateM.bind]
      rw [h_ri]
      cases rst with
      | false => rfl
      | true =>
        change (EStateM.bind (EStateM.bind ((refValHooks types).clearProvenance c place) _) _ st) = _
        dsimp only [EStateM.bind]
        rw [refValHooks_clearProvenance,
          clearPlaceProvenance_imm_no_prov types c place
            (.scalar (.fromScalarInt (miriScalar w bits))) st h_toOp' rfl]
        rfl

private theorem visit_local_int_uninit_ub (types : List MirTy) (c : Choice)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (place : RuntimePlace Miri.Memory.Provenance) (w : IntWidth) (s : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_lay : place.layout = refLocalLayoutForTy types (.int w s))
    (h_res : resolveTy types (tyIdFor types (.int w s)) = some (.int w s))
    (h_toOp : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
      c place st = .ok ⟨.immediate .uninit, refLocalLayoutForTy types (.int w s)⟩ st) :
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
          session place st = .error (.undefinedBehavior msg) st := by
  let ⟨msg, h_u⟩ := validityMemory_readImmediate_imm_uninit types (.int w s)
    .integer st (Or.inr ⟨w, s, rfl⟩)
  have h_ri : (refValHooks types).readImmediate c place .integer st =
      .error (.undefinedBehavior msg) st := by
    rw [refValHooks_readImmediate]
    dsimp only [bind, Bind.bind, EStateM.bind]
    rw [h_toOp]
    exact h_u
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.ValidityVisitor.visit,
    bind, Bind.bind, EStateM.bind]
  rw [h_lay, refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind ((refValHooks types).readImmediate c place .integer) _) _ st) = _
  dsimp only [EStateM.bind]
  rw [h_ri]

private theorem visit_local_bool_ok (types : List MirTy) (c : Choice)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (place : RuntimePlace Miri.Memory.Provenance) (b : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_lay : place.layout = refLocalLayoutForTy types .bool)
    (h_res : resolveTy types (tyIdFor types .bool) = some .bool)
    (h_rst : session.flags.resetProvenanceAndPadding = true)
    (h_db : session.dataBytes = none)
    (h_toOp : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
      c place st = .ok ⟨.immediate (.scalar (.fromBool b)),
        refLocalLayoutForTy types .bool⟩ st) :
    Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
        session place st = .ok session st := by
  cases session with
  | mk path flags mode tracking bytes =>
    cases flags with
    | mk rst md =>
      dsimp only at h_rst h_db
      subst h_rst h_db
      have h_toOp' : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
          c place st = .ok ⟨.immediate (.scalar (.fromBool b)), place.layout⟩ st := by
        rw [h_lay]; exact h_toOp
      have h_ri : (refValHooks types).readImmediate c place .boolean st =
          .ok ⟨.scalar (.fromBool b), refLocalLayoutForTy types .bool⟩ st := by
        rw [refValHooks_readImmediate]
        dsimp only [bind, Bind.bind, EStateM.bind]
        rw [h_toOp]
        exact validityMemory_readImmediate_imm_scalar types .bool
          (.fromBool b) .boolean st (Or.inl rfl)
      dsimp only [Miri.Interpreter.ValidityVisitor.visit,
        bind, Bind.bind, EStateM.bind]
      rw [h_lay, refLocalLayoutForTy_ty, refValHooks_classify, h_res]
      dsimp only
      change (EStateM.bind (EStateM.bind ((refValHooks types).readImmediate c place .boolean) _) _ st) = _
      dsimp only [EStateM.bind]
      rw [h_ri]
      cases b with
      | false =>
        change (EStateM.bind (EStateM.bind ((refValHooks types).clearProvenance c place) _) _ st) = _
        dsimp only [EStateM.bind]
        rw [refValHooks_clearProvenance,
          clearPlaceProvenance_imm_no_prov types c place (.scalar (.fromBool false)) st
            h_toOp' rfl]
        rfl
      | true =>
        change (EStateM.bind (EStateM.bind ((refValHooks types).clearProvenance c place) _) _ st) = _
        dsimp only [EStateM.bind]
        rw [refValHooks_clearProvenance,
          clearPlaceProvenance_imm_no_prov types c place (.scalar (.fromBool true)) st
            h_toOp' rfl]
        rfl

private theorem visit_local_bool_uninit_ub (types : List MirTy) (c : Choice)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (place : RuntimePlace Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_lay : place.layout = refLocalLayoutForTy types .bool)
    (h_res : resolveTy types (tyIdFor types .bool) = some .bool)
    (h_toOp : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
      c place st = .ok ⟨.immediate .uninit, refLocalLayoutForTy types .bool⟩ st) :
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
          session place st = .error (.undefinedBehavior msg) st := by
  let ⟨msg, h_u⟩ := validityMemory_readImmediate_imm_uninit types .bool .boolean
    st (Or.inl rfl)
  have h_ri : (refValHooks types).readImmediate c place .boolean st =
      .error (.undefinedBehavior msg) st := by
    rw [refValHooks_readImmediate]
    dsimp only [bind, Bind.bind, EStateM.bind]
    rw [h_toOp]
    exact h_u
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.ValidityVisitor.visit,
    bind, Bind.bind, EStateM.bind]
  rw [h_lay, refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind ((refValHooks types).readImmediate c place .boolean) _) _ st) = _
  dsimp only [EStateM.bind]
  rw [h_ri]

private theorem visit_local_never_ub (types : List MirTy) (c : Choice)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (place : RuntimePlace Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_lay : place.layout = refLocalLayoutForTy types .never)
    (h_res : resolveTy types (tyIdFor types .never) = some .never) :
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
          session place st = .error (.undefinedBehavior msg) st := by
  dsimp only [Miri.Interpreter.ValidityVisitor.visit,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_lay, refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  exact ⟨_, rfl⟩

private theorem visit_local_scalar_enum_ok (types : List MirTy) (c : Choice)
    (fuel k : Nat) (h_fuel : fuel = k + 1) (localId : LocalId) (ety : EnumTy)
    (tagW : IntWidth) (tagS : Bool) (variant disc : Nat)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_adm : enumAdmitted ety = true)
    (h_res : resolveTy types (tyIdFor types (.enum ety)) = some (.enum ety))
    (h_get_d : MirSemantics.getElem? ety.discriminants variant = some disc)
    (h_frames : st.stack.frames = (Array.mk [frame]))
    (h_dr : frame.extra.dataRace = none)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))))),
        some (refLocalLayoutForTy types (.enum ety))⟩) :
    let initSess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := none
    }
    Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
        initSess
        ⟨.local 0 localId none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types (.enum ety)⟩ st = .ok initSess st := by
  have h_ne_box :
      (Miri.Interpreter.ValidityVisitor.TypeKind.aggregate false false true == .box) =
        false := rfl
  have h_fields : (refLocalLayoutForTy types (.enum ety)).layout.fields =
      .Arbitrary (Array.mk [Size.ZERO]) (Array.mk [0]) := by
    dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
    rw [h_tr]
  have h_vars : (refLocalLayoutForTy types (.enum ety)).layout.variants =
      .Multiple (.Union (value := .Int (toMiriInteger tagW) tagS)) .Direct 0
        (ety.discriminants.map (fun _ => refInhabitedVariantLayout)).toArray := by
    dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
    rw [h_tr]
  have h_v_lt : variant < ety.discriminants.length :=
    mirGetElem?_lt_of_some h_get_d
  have h_toOp := placeToOp_local_immediate types c localId (.enum ety)
    (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))))
    frame st h_frames h_dr h_get
  have h_ms_sz :
      (Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
        (miriScalar tagW (BitVec.ofNat 128 disc))).size = toMiriSize tagW := by
    cases tagW <;> rfl
  have h_toOp_f0 := placeToOp_local_field0_scalar_enum types c localId
    ety tagW tagS
    (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))))
    frame st h_tr h_frames h_dr h_get (Or.inr ⟨_, rfl, h_ms_sz⟩)
  have h_res_tag :
      resolveTy types (tyIdFor types (.int tagW tagS)) =
        some (.int tagW tagS) :=
    resolveTy_tyIdFor_int types tagW tagS
  have h_pf0 :
      Miri.Interpreter.PlaceDynamic.field (refBasePlaceProjectionHooks types) c
        ⟨.local 0 localId none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types (.enum ety)⟩ 0 st =
      .ok ⟨.local 0 localId (some Size.ZERO) (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types (.int tagW tagS)⟩ st := by
    dsimp only [Miri.Interpreter.PlaceDynamic.field,
      Miri.Interpreter.PlaceDynamic.offsetWithMeta,
      refBasePlaceProjectionHooks, refProjectFieldLayout,
      refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [h_res]
    dsimp only
    rw [h_tr]
    cases tagW <;> cases tagS <;> rfl
  have h_dc :
      Miri.Interpreter.PlaceDynamic.downcast (refBasePlaceProjectionHooks types) c
        ⟨.local 0 localId none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types (.enum ety)⟩ variant st =
      .ok ⟨.local 0 localId (some Size.ZERO) (LocalsIdentity.ofAllocationToken 0),
          ⟨tyIdFor types (.enum ety),
            { refUnitLayoutData with variants := .Single variant }⟩⟩ st := by
    have h_blt : Nat.blt variant ety.discriminants.length = true :=
      Nat.ble_eq_true_of_le h_v_lt
    dsimp only [Miri.Interpreter.PlaceDynamic.downcast,
      Miri.Interpreter.PlaceDynamic.offsetWithMeta,
      refBasePlaceProjectionHooks, refProjectVariantLayout,
      refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [h_res]
    dsimp only
    rw [h_blt, h_tr]
    cases tagW <;> cases tagS <;> rfl
  have h_rd_discr := readDiscriminant_validity_local_scalar_enum types c
    ety tagW tagS variant disc st h_tr h_adm h_res h_get_d h_pmd
  dsimp only [Miri.Interpreter.ValidityVisitor.visit,
    bind, Bind.bind, EStateM.bind]
  rw [refValHooks_classify, refLocalLayoutForTy_ty, h_res]
  dsimp only
  change (match (EStateM.Result.ok none st :
      EStateM.Result StepError (Miri.Interpreter.MachineHooks.State Unit RefUser)
        (Option (Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance))) with
    | EStateM.Result.ok a s => _
    | EStateM.Result.error e s => EStateM.Result.error e s) = _
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ne_box, ite_false_eq, h_fields, h_vars]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_projection, forIn_singleton_array]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_pf0]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_fieldPath]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_fuel, visit_local_int_ok types c k _ _ tagW tagS (BitVec.ofNat 128 disc)
    st rfl h_res_tag rfl h_toOp_f0]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_toOp, refValHooks_discriminant, h_toOp]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_rd_discr]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_dc]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_variantPath]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [visit_local_fieldless_enum types c k _ _ ety variant st rfl h_res
    rfl rfl rfl]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  have h_inh : (refValHooks types).opsemInhabited c (tyIdFor types (.enum ety)) st =
      .ok true st := by
    rw [refValHooks_opsemInhabited, h_res]
  rw [h_inh]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [ite_true_eq, refValHooks_debugAssertions, ite_false_eq]
  rfl

private theorem visit_local_scalar_enum_uninit_ub (types : List MirTy)
    (c : Choice) (fuel k : Nat) (h_fuel : fuel = k + 1) (localId : LocalId)
    (ety : EnumTy) (tagW : IntWidth) (tagS : Bool)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_res : resolveTy types (tyIdFor types (.enum ety)) = some (.enum ety))
    (h_frames : st.stack.frames = (Array.mk [frame]))
    (h_dr : frame.extra.dataRace = none)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate .uninit),
        some (refLocalLayoutForTy types (.enum ety))⟩) :
    let initSess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := none
    }
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
          initSess
          ⟨.local 0 localId none (LocalsIdentity.ofAllocationToken 0),
            refLocalLayoutForTy types (.enum ety)⟩ st =
        .error (.undefinedBehavior msg) st := by
  have h_ne_box :
      (Miri.Interpreter.ValidityVisitor.TypeKind.aggregate false false true == .box) =
        false := rfl
  have h_fields : (refLocalLayoutForTy types (.enum ety)).layout.fields =
      .Arbitrary (Array.mk [Size.ZERO]) (Array.mk [0]) := by
    dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
    rw [h_tr]
  have h_toOp_f0 := placeToOp_local_field0_scalar_enum types c localId
    ety tagW tagS .uninit frame st h_tr h_frames h_dr h_get (Or.inl rfl)
  have h_res_tag :
      resolveTy types (tyIdFor types (.int tagW tagS)) =
        some (.int tagW tagS) :=
    resolveTy_tyIdFor_int types tagW tagS
  have h_pf0 :
      Miri.Interpreter.PlaceDynamic.field (refBasePlaceProjectionHooks types) c
        ⟨.local 0 localId none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types (.enum ety)⟩ 0 st =
      .ok ⟨.local 0 localId (some Size.ZERO) (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types (.int tagW tagS)⟩ st := by
    dsimp only [Miri.Interpreter.PlaceDynamic.field,
      Miri.Interpreter.PlaceDynamic.offsetWithMeta,
      refBasePlaceProjectionHooks, refProjectFieldLayout,
      refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [h_res]
    dsimp only
    rw [h_tr]
    cases tagW <;> cases tagS <;> rfl
  let ⟨msg, h_vis_f0⟩ := visit_local_int_uninit_ub types c k
    { path := (⟨"", (Array.mk [])⟩ : ValidationPath).push .enumTag,
      flags := ⟨true, false || false⟩, ctfeMode := none,
      refTracking := none, dataBytes := none }
    ⟨.local 0 localId (some Size.ZERO) (LocalsIdentity.ofAllocationToken 0),
      refLocalLayoutForTy types (.int tagW tagS)⟩
    tagW tagS st rfl h_res_tag h_toOp_f0
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.ValidityVisitor.visit,
    bind, Bind.bind, EStateM.bind]
  rw [refValHooks_classify, refLocalLayoutForTy_ty, h_res]
  dsimp only
  change (match (EStateM.Result.ok none st :
      EStateM.Result StepError (Miri.Interpreter.MachineHooks.State Unit RefUser)
        (Option (Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance))) with
    | EStateM.Result.ok a s => _
    | EStateM.Result.error e s => EStateM.Result.error e s) = _
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ne_box, ite_false_eq, h_fields]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_projection, forIn_singleton_array]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_pf0]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_fieldPath]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_fuel, h_vis_f0]

/-- `ValidityVisitor.validatePlace` on an initialized Day-1 `.local` holding
`valToMiriImmediate ty v` with `checkVal v ty = true` succeeds without
mutating state. -/
theorem validatePlace_local_ok (types : List MirTy) (c : Choice)
    (localId : LocalId) (ty : MirTy) (v : Val)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_frames : st.stack.frames = (Array.mk [frame]))
    (h_dr : frame.extra.dataRace = none)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate (valToMiriImmediate ty v)),
        some (refLocalLayoutForTy types ty)⟩)
    (h_cv : checkVal v ty = true)
    (h_res : resolveTy types (tyIdFor types ty) = some ty) :
    Miri.Interpreter.ValidityVisitor.validatePlace
        (Miri.Interpreter.TypedMachineBindings.bindValidity
          (refValidityHooks types) refRetagHooks 8)
        c 8
        ⟨.local 0 localId none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types ty⟩
        false true st = .ok () st := by
  have h_toOp := placeToOp_local_immediate types c localId ty
    (valToMiriImmediate ty v) frame st h_frames h_dr h_get
  refine validatePlace_shallow_local_step types c _ _ st h_toOp ?_
  cases checkVal_eq_true_inv h_cv with
  | inl h_i =>
    let ⟨w, s, bits, hty, hv, _⟩ := h_i
    subst hty hv
    exact visit_local_int_ok types c 7 _ _ w s bits st rfl h_res rfl h_toOp
  | inr h_rest =>
    cases h_rest with
    | inl h_b =>
      let ⟨b, hty, hv⟩ := h_b
      subst hty hv
      exact visit_local_bool_ok types c 7 _ _ b st rfl h_res rfl rfl h_toOp
    | inr h_rest2 =>
      cases h_rest2 with
      | inl h_u =>
        let ⟨hty, hv⟩ := h_u
        subst hty hv
        exact Miri.Interpreter.ValidityVisitor.visit_fieldless
          (refValHooks types) c 7 _ _ st 0
          (by rw [refValHooks_classify]; dsimp only [refLocalLayoutForTy]; rw [h_res])
          (by rw [refValHooks_opsemInhabited]; dsimp only [refLocalLayoutForTy]; rw [h_res])
          rfl rfl rfl rfl
      | inr h_e =>
        let ⟨ety, variant, hty, hv, h_adm, h_v_lt⟩ := h_e
        subst hty hv
        cases h_tr : ety.tagRepr with
        | zeroSized =>
          exact visit_local_fieldless_enum types c 7 _ _ ety 0 st rfl h_res
            (by dsimp only [refLocalLayoutForTy, refLayoutDataForTy,
                  refEnumLayoutData]; rw [h_tr]; rfl)
            (by dsimp only [refLocalLayoutForTy, refLayoutDataForTy,
                  refEnumLayoutData]; rw [h_tr]; rfl)
            rfl
        | scalar tagW tagS =>
          let ⟨disc, h_get_d⟩ := mirGetElem?_some_of_lt h_v_lt
          have h_val_eq :
              valToMiriImmediate (.enum ety) (.enumVal ety variant) =
                .scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))) := by
            dsimp only [valToMiriImmediate]
            rw [h_tr, h_get_d]
          rw [h_val_eq] at h_get
          exact visit_local_scalar_enum_ok types c 7 6 rfl localId ety tagW tagS
            variant disc frame st h_tr h_adm h_res h_get_d h_frames h_dr h_pmd
            h_get

/-- `ValidityVisitor.validatePlace` on an uninitialized non-ZST Day-1 `.local`
fails with `.undefinedBehavior`. -/
theorem validatePlace_local_uninit_ub (types : List MirTy) (c : Choice)
    (localId : LocalId) (ty : MirTy)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_frames : st.stack.frames = (Array.mk [frame]))
    (h_dr : frame.extra.dataRace = none)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate .uninit), some (refLocalLayoutForTy types ty)⟩)
    (h_sm : SlotMatchesTy ty (.live none))
    (h_supp : isSupportedScalarOrUnitTy ty = true)
    (h_res : resolveTy types (tyIdFor types ty) = some ty) :
    ∃ msg st',
      Miri.Interpreter.ValidityVisitor.validatePlace
          (Miri.Interpreter.TypedMachineBindings.bindValidity
            (refValidityHooks types) refRetagHooks 8)
          c 8
          ⟨.local 0 localId none (LocalsIdentity.ofAllocationToken 0),
            refLocalLayoutForTy types ty⟩
          false true st = .error (.undefinedBehavior msg) st' := by
  have h_toOp := placeToOp_local_immediate types c localId ty .uninit frame st
    h_frames h_dr h_get
  let initSess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
    path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
    refTracking := none, dataBytes := none
  }
  cases ty with
  | unit => exact False.elim (h_sm.1 rfl)
  | never =>
    let ⟨msg, h_vis⟩ := visit_local_never_ub types c 7 initSess
      ⟨.local 0 localId none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy types .never⟩ st rfl h_res
    exact ⟨msg, st, validatePlace_shallow_local_ub_step types c _ _ st st msg h_toOp h_vis⟩
  | bool =>
    let ⟨msg, h_vis⟩ := visit_local_bool_uninit_ub types c 7 initSess
      ⟨.local 0 localId none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy types .bool⟩ st rfl h_res h_toOp
    exact ⟨msg, st, validatePlace_shallow_local_ub_step types c _ _ st st msg h_toOp h_vis⟩
  | int w s =>
    let ⟨msg, h_vis⟩ := visit_local_int_uninit_ub types c 7 initSess
      ⟨.local 0 localId none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy types (.int w s)⟩ w s st rfl h_res h_toOp
    exact ⟨msg, st, validatePlace_shallow_local_ub_step types c _ _ st st msg h_toOp h_vis⟩
  | enum ety =>
    cases h_tr : ety.tagRepr with
    | zeroSized =>
      have h_zst := h_sm.2 ety rfl
      dsimp only [isZstEnumTy] at h_zst
      rw [h_tr] at h_zst
      dsimp only [isSupportedScalarOrUnitTy] at h_supp
      rw [h_supp] at h_zst
      cases h_zst
    | scalar tagW tagS =>
      let ⟨msg, h_vis⟩ := visit_local_scalar_enum_uninit_ub types c 7 6 rfl localId
        ety tagW tagS frame st h_tr h_res h_frames h_dr h_get
      exact ⟨msg, st, validatePlace_shallow_local_ub_step types c _ _ st st msg h_toOp h_vis⟩
  | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases h_supp

/-! ## Section 5: Return-Place Memory Write, Validation, and `copyReturn` -/

private def retAllocId : Miri.Memory.AllocId := ⟨1, by decide⟩

private def retPtr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
  ⟨Size.ZERO, some (.concrete retAllocId Miri.Memory.BorTag.one)⟩

private def retMemPlace : Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
  ⟨retPtr, .none, none⟩

private theorem singleton_live_find
    (entry : Miri.Memory.LocalAllocation Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit) :
    ((Array.mk [(retAllocId, entry)])).find? (fun row => row.1 == retAllocId) =
      some (retAllocId, entry) := rfl

private theorem singleton_live_filter_push
    (entry1 entry2 : Miri.Memory.LocalAllocation Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit) :
    (((Array.mk [(retAllocId, entry1)])).filter (fun row => row.1 != retAllocId)).push
        (retAllocId, entry2) =
      (Array.mk [(retAllocId, entry2)]) := rfl

private theorem singleton_setLiveAllocation
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc1 alloc2 : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree) :
    ({ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc1⟩)]) } :
        Miri.Memory.MemoryState Miri.Memory.Provenance
          Miri.TreeBorrows.BorrowTree Unit).setLiveAllocation
        retAllocId alloc2 =
      .ok { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc2⟩)]) } := by
  rw [Miri.Memory.MemoryState.setLiveAllocation_of_find _ retAllocId
    ⟨.stack, alloc1⟩ alloc2 (singleton_live_find _)]
  rw [singleton_live_filter_push]

private theorem sizeAsI64_toMiriSize (w : IntWidth) :
    Miri.Memory.sizeAsI64 (toMiriSize w) = .ok (toMiriSize w).bytes.toNat := by
  cases w <;> rfl

private theorem toMiriSize_ne_zero (w : IntWidth) :
    ((toMiriSize w).bytes.toNat : Int) ≠ 0 := by
  cases w <;> decide

private theorem int_pow_eq_ofNat (b : Nat) :
    ∀ n : Nat, HPow.hPow (Int.ofNat b) n = Int.ofNat (HPow.hPow b n)
  | 0 => rfl
  | n + 1 => by
    rw [Int.pow_succ, int_pow_eq_ofNat b n, Nat.pow_succ]
    rfl

private theorem fitsI64_of_le16 (n : Nat) (hn : n ≤ 16) :
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

private theorem checkedBounds_retPlace (w : IntWidth) :
    Miri.Memory.checkedBounds ⟨Size.ofBytes 8⟩ retAllocId (toMiriSize w)
        Size.ZERO (toMiriSize w).bytes.toNat .memoryAccess =
      .ok () := by
  have h_le16 : (toMiriSize w).bytes.toNat ≤ 16 := by cases w <;> decide
  have h_fits := fitsI64_of_le16 (toMiriSize w).bytes.toNat h_le16
  dsimp only [Miri.Memory.checkedBounds]
  change
    (if (!((Neg.neg (HPow.hPow (2 : Int) (63 : Nat)) ≤
              Int.ofNat (toMiriSize w).bytes.toNat) &&
            (Int.ofNat (toMiriSize w).bytes.toNat <
              HPow.hPow (2 : Int) (63 : Nat)))) = true
     then _ else _) = Except.ok ()
  rw [h_fits]
  cases w <;> rfl

private noncomputable def singleDataRange (w : IntWidth) :
    Miri.Memory.Validity.DataRangeSet :=
  match Miri.Memory.Validity.DataRangeSet.empty.addRange Size.ZERO (toMiriSize w) with
  | .ok rs => rs
  | .error _ => .empty

private theorem dataRangeSet_empty_addRange_zero (w : IntWidth) :
    Miri.Memory.Validity.DataRangeSet.empty.addRange Size.ZERO (toMiriSize w) =
      .ok (singleDataRange w) := by
  cases w <;> rfl

private theorem singleDataRange_toArray (w : IntWidth) :
    (singleDataRange w).toArray = (Array.mk [allocRange Size.ZERO (toMiriSize w)]) := by
  cases w <;> rfl

private theorem scalar_tryToScalarInt_fromScalarInt (s : ScalarInt) :
    (Scalar.fromScalarInt (Prov := Miri.Memory.Provenance) s).tryToScalarInt =
      .ok (.integer s) := rfl

private theorem eStateM_bind_bind_ok {ε σ α β γ : Type} {m : EStateM ε σ α}
    {f : α → EStateM ε σ β} {g : β → EStateM ε σ γ} {a : α} {st st' : σ}
    (h : m st = .ok a st') :
    EStateM.bind (EStateM.bind m f) g st = EStateM.bind (f a) g st' := by
  dsimp only [EStateM.bind]; rw [h]

private theorem eStateM_bind_bind_err {ε σ α β γ : Type} {m : EStateM ε σ α}
    {f : α → EStateM ε σ β} {g : β → EStateM ε σ γ} {e : ε} {st st' : σ}
    (h : m st = .error e st') :
    EStateM.bind (EStateM.bind m f) g st = .error e st' := by
  dsimp only [EStateM.bind]; rw [h]

private theorem placeMemoryOffset_retPlace_zero
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    Miri.Interpreter.placeMemoryOffset refPointerArithmetic
        refResolvePointerPure mem.getAllocInfo retMemPlace Size.ZERO
        .inbounds .none st =
      .ok retMemPlace st := rfl

private theorem scalar_fromBool_eq (b : Bool) :
    Scalar.fromBool (Prov := Miri.Memory.Provenance) b =
      .fromScalarInt (miriScalar .i8 (if b then 1 else 0)) := by
  cases b <;> rfl

private theorem miriScalar_size (w : IntWidth) (bits : BitVec 128) :
    (Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
      (miriScalar w bits)).size = toMiriSize w := by
  cases w <;> rfl

private theorem subrange_self_toMiriSize (w : IntWidth) :
    (allocRange Size.ZERO (toMiriSize w)).subrange
        (allocRange Size.ZERO (toMiriSize w)) =
      .ok (allocRange Size.ZERO (toMiriSize w)) := by
  cases w <;> rfl

private theorem getPtrAllocMut_retPlace_nonGhost (w : IntWidth)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (h_sz : alloc.byteSize = toMiriSize w)
    (h_mut : alloc.mutability = .Mut)
    (h_extra : alloc.extra =
      Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize w))
    (h_dr : machine.dataRace = none) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Memory.AllocationAccess.getPtrAllocMut mem ⟨machine, none⟩
        ⟨Size.ofBytes 8⟩ retPtr (toMiriSize w) false none
        refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig) =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩)⟩ := by
  intro mem
  exact Miri.Memory.AllocationAccess.live_mut_of_edges mem ⟨machine, none⟩
    ⟨Size.ofBytes 8⟩ retPtr (toMiriSize w) none refAccessConfig.globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
    retAllocId ⟨.stack, alloc⟩ (.concrete Miri.Memory.BorTag.one)
    (toMiriSize w).bytes.toNat
    (sizeAsI64_toMiriSize w)
    (toMiriSize_ne_zero w)
    (Miri.Interpreter.PlaceMachine.resolvePointer_ok refAccessConfig mem machine
      retPtr _ _ rfl)
    (singleton_live_find _)
    h_mut
    rfl
    (by rw [h_sz]; exact checkedBounds_retPlace w)
    rfl
    (by
      dsimp only [Miri.Interpreter.PlaceMachine.accessHooks]
      rw [h_extra]
      exact Miri.Interpreter.PlaceMachine.memoryAccess_fresh_write
        refAccessConfig machine retAllocId Miri.Memory.BorTag.one
        (toMiriSize w) h_dr rfl rfl rfl)
    (singleton_live_filter_push _ _)

private theorem getPtrAlloc_retPlace_ghost_gen (w : IntWidth) (signedSize : Int)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_res : cfg.resolvePointer = refResolvePointer)
    (h_gh : cfg.globalHooks = refGlobalAllocationHooks)
    (h_sz : alloc.byteSize = toMiriSize w)
    (h_sa : Miri.Memory.sizeAsI64 (toMiriSize w) = .ok signedSize)
    (h_nz : (signedSize != 0) = true)
    (h_bounds : Miri.Memory.checkedBounds ⟨Size.ofBytes 8⟩ retAllocId
      (toMiriSize w) Size.ZERO signedSize .memoryAccess = .ok ()) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Memory.AllocationAccess.getPtrAlloc mem ⟨machine, none⟩
        ⟨Size.ofBytes 8⟩ retPtr (toMiriSize w) true none
        cfg.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks cfg) =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩)⟩ := by
  intro mem
  have h_raw : Miri.Memory.MemoryLifecycle.getAllocRaw mem ⟨machine, none⟩
      retAllocId none cfg.globalHooks = ⟨mem, ⟨machine, none⟩, .ok alloc⟩ := by
    dsimp only [Miri.Memory.MemoryLifecycle.getAllocRaw]
    rw [h_gh]
    dsimp only [refGlobalAllocationHooks, mem, Id.run, bind, Bind.bind,
      pure, Pure.pure]
    rw [singleton_live_find]
  have h_rp : (Miri.Interpreter.PlaceMachine.accessHooks cfg).resolvePointer
      mem ⟨machine, none⟩ retPtr signedSize =
      ⟨⟨machine, none⟩,
        .ok (.ok ⟨retAllocId, Size.ZERO, .concrete Miri.Memory.BorTag.one⟩)⟩ := by
    dsimp only [Miri.Interpreter.PlaceMachine.accessHooks]
    rw [h_res]
    rfl
  dsimp only [Miri.Memory.AllocationAccess.getPtrAlloc]
  change (match Miri.Memory.sizeAsI64 (toMiriSize w) with
    | Except.ok _ => _ | Except.error _ => _) = _
  rw [h_sa]
  change (if (signedSize != 0) = true then _ else _) = _
  rw [h_nz, ite_true_eq]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_rp]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [ite_false_eq, h_raw]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_sz, h_bounds]
  rfl

private theorem getPtrAlloc_retPlace_ghost (w : IntWidth)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_res : cfg.resolvePointer = refResolvePointer)
    (h_gh : cfg.globalHooks = refGlobalAllocationHooks)
    (h_sz : alloc.byteSize = toMiriSize w) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Memory.AllocationAccess.getPtrAlloc mem ⟨machine, none⟩
        ⟨Size.ofBytes 8⟩ retPtr (toMiriSize w) true none
        cfg.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks cfg) =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩)⟩ :=
  getPtrAlloc_retPlace_ghost_gen w (toMiriSize w).bytes.toNat mem1 alloc machine cfg
    h_res h_gh h_sz (sizeAsI64_toMiriSize w) (by cases w <;> decide)
    (checkedBounds_retPlace w)

private theorem getPtrAllocMut_retPlace_ghost_gen (w : IntWidth) (signedSize : Int)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (h_sz : alloc.byteSize = toMiriSize w)
    (h_mut : alloc.mutability = .Mut)
    (h_sa : Miri.Memory.sizeAsI64 (toMiriSize w) = .ok signedSize)
    (h_nz : (signedSize != 0) = true)
    (h_bounds : Miri.Memory.checkedBounds ⟨Size.ofBytes 8⟩ retAllocId
      (toMiriSize w) Size.ZERO signedSize .memoryAccess = .ok ()) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Memory.AllocationAccess.getPtrAllocMut mem ⟨machine, none⟩
        ⟨Size.ofBytes 8⟩ retPtr (toMiriSize w) true none
        refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig) =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩)⟩ := by
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
  have h_rp : (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig).resolvePointer
      mem ⟨machine, none⟩ retPtr signedSize =
      ⟨⟨machine, none⟩,
        .ok (.ok ⟨retAllocId, Size.ZERO, .concrete Miri.Memory.BorTag.one⟩)⟩ :=
    Miri.Interpreter.PlaceMachine.resolvePointer_ok refAccessConfig mem machine
      retPtr _ _ rfl
  dsimp only [Miri.Memory.AllocationAccess.getPtrAllocMut]
  change (match Miri.Memory.sizeAsI64 (toMiriSize w) with
    | Except.ok _ => _ | Except.error _ => _) = _
  rw [h_sa]
  change (if (signedSize != 0) = true then _ else _) = _
  rw [h_nz, ite_true_eq]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_rp]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [ite_true_eq, h_raw]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_sz, h_bounds]
  rfl

private theorem getPtrAllocMut_retPlace_ghost (w : IntWidth)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (h_sz : alloc.byteSize = toMiriSize w)
    (h_mut : alloc.mutability = .Mut) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Memory.AllocationAccess.getPtrAllocMut mem ⟨machine, none⟩
        ⟨Size.ofBytes 8⟩ retPtr (toMiriSize w) true none
        refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig) =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩)⟩ :=
  getPtrAllocMut_retPlace_ghost_gen w (toMiriSize w).bytes.toNat mem1 alloc machine
    h_sz h_mut (sizeAsI64_toMiriSize w) (by cases w <;> decide)
    (checkedBounds_retPlace w)

private theorem getPlaceAlloc_sized_of_access_poly {P E K H X : Type}
    [DecidableEq K]
    (memory : Miri.Memory.MemoryState P E K) (hooks : H)
    (place : Miri.Interpreter.MemoryOperandPlace P)
    (ghost : Bool) (kind : Option K)
    (global : Miri.Memory.GlobalAllocationHooks P E K H)
    (access : Miri.Memory.AllocationAccessHooks P E K H X)
    (dynamic : Miri.Interpreter.DynamicLayoutResolver P E K H)
    (reference : Miri.Memory.AllocationAccessRef P E)
    (sized : place.layout.backendRepr.isUnsized = false)
    (aligned : place.mplace.misaligned = none)
    (actual : Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
      ⟨Size.ofBytes 8⟩ place.mplace.ptr place.layout.size ghost kind global access =
      ⟨memory, hooks, some reference, .ok (some reference)⟩) :
    Miri.Interpreter.getPlaceAlloc memory hooks place
        RuntimeTargetDataLayout.default ghost kind global access dynamic =
      ⟨memory, hooks, some reference, .ok (some reference)⟩ := by
  cases place with
  | mk mplace layout =>
    cases mplace with
    | mk ptr metaVal misaligned =>
      dsimp only at aligned
      subst aligned
      cases layout with
      | mk sz al repr cty =>
        dsimp only at sized actual
        cases repr with
        | Scalar _ | ScalarPair | SimdVector | SimdScalableVector =>
          change (match (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
              ⟨Size.ofBytes 8⟩ ptr sz ghost kind global access).outcome with
            | Except.error error => _
            | Except.ok reference? => _) = _
          rw [actual]
          dsimp only [pure, Pure.pure, RuntimeTargetDataLayout.default,
            RuntimeTargetDataLayout.defaultAddressSpacePointerSpec]
          rw [actual]
        | @Memory isSized =>
          cases isSized with
          | false => cases sized
          | true =>
            change (match (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                ⟨Size.ofBytes 8⟩ ptr sz ghost kind global access).outcome with
              | Except.error error => _
              | Except.ok reference? => _) = _
            rw [actual]
            dsimp only [pure, Pure.pure, RuntimeTargetDataLayout.default,
              RuntimeTargetDataLayout.defaultAddressSpacePointerSpec]
            rw [actual]

private theorem getPlaceAllocMut_sized_of_access_poly {P E K H X : Type}
    [DecidableEq K]
    (memory : Miri.Memory.MemoryState P E K) (hooks : H)
    (place : Miri.Interpreter.MemoryOperandPlace P)
    (ghost : Bool) (kind : Option K)
    (global : Miri.Memory.GlobalAllocationHooks P E K H)
    (access : Miri.Memory.AllocationAccessHooks P E K H X)
    (dynamic : Miri.Interpreter.DynamicLayoutResolver P E K H)
    (reference : Miri.Memory.AllocationAccessRef P E)
    (sized : place.layout.backendRepr.isUnsized = false)
    (aligned : place.mplace.misaligned = none)
    (actual : Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
      ⟨Size.ofBytes 8⟩ place.mplace.ptr place.layout.size ghost kind global access =
      ⟨memory, hooks, some reference, .ok (some reference)⟩) :
    Miri.Interpreter.getPlaceAllocMut memory hooks place
        RuntimeTargetDataLayout.default ghost kind global access dynamic =
      ⟨memory, hooks, some reference, .ok (some reference)⟩ := by
  cases place with
  | mk mplace layout =>
    cases mplace with
    | mk ptr metaVal misaligned =>
      dsimp only at aligned
      subst aligned
      cases layout with
      | mk sz al repr cty =>
        dsimp only at sized actual
        cases repr with
        | Scalar _ | ScalarPair | SimdVector | SimdScalableVector =>
          change (match (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
              ⟨Size.ofBytes 8⟩ ptr sz ghost kind global access).outcome with
            | Except.error error => _
            | Except.ok reference? => _) = _
          rw [actual]
          dsimp only [pure, Pure.pure, RuntimeTargetDataLayout.default,
            RuntimeTargetDataLayout.defaultAddressSpacePointerSpec]
          rw [actual]
        | @Memory isSized =>
          cases isSized with
          | false => cases sized
          | true =>
            change (match (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
                ⟨Size.ofBytes 8⟩ ptr sz ghost kind global access).outcome with
              | Except.error error => _
              | Except.ok reference? => _) = _
            rw [actual]
            dsimp only [pure, Pure.pure, RuntimeTargetDataLayout.default,
              RuntimeTargetDataLayout.defaultAddressSpacePointerSpec]
            rw [actual]

private theorem getPlaceAlloc_retPlace_ghost (w : IntWidth)
    (memLayout : Miri.Interpreter.MemoryOperandLayout)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_rt : cfg.runtime = Miri.ABI.RuntimeTargetDataLayout.default)
    (h_gk : cfg.globalKind = none)
    (h_res : cfg.resolvePointer = refResolvePointer)
    (h_gh : cfg.globalHooks = refGlobalAllocationHooks)
    (h_uns : memLayout.backendRepr.isUnsized = false)
    (h_lsz : memLayout.size = toMiriSize w)
    (h_sz : alloc.byteSize = toMiriSize w) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Interpreter.getPlaceAlloc mem ⟨machine, none⟩
        ⟨retMemPlace, memLayout⟩ cfg.runtime true cfg.globalKind
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩)⟩ := by
  intro mem
  rw [h_rt, h_gk]
  have h_ptr := getPtrAlloc_retPlace_ghost w mem1 alloc machine cfg h_res h_gh h_sz
  exact getPlaceAlloc_sized_of_access_poly mem ⟨machine, none⟩
    ⟨retMemPlace, memLayout⟩ true none cfg.globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks cfg) cfg.dynamicLayout
    ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩
    h_uns rfl (by dsimp only; rw [h_lsz]; exact h_ptr)

private theorem getPlaceAllocMut_retPlace_ghost (w : IntWidth)
    (memLayout : Miri.Interpreter.MemoryOperandLayout)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alloc : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (h_uns : memLayout.backendRepr.isUnsized = false)
    (h_lsz : memLayout.size = toMiriSize w)
    (h_sz : alloc.byteSize = toMiriSize w)
    (h_mut : alloc.mutability = .Mut) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
    Miri.Interpreter.getPlaceAllocMut mem ⟨machine, none⟩
        ⟨retMemPlace, memLayout⟩ refAccessConfig.runtime true none
        refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩)⟩ := by
  intro mem
  have h_ptr := getPtrAllocMut_retPlace_ghost w mem1 alloc machine h_sz h_mut
  exact getPlaceAllocMut_sized_of_access_poly mem ⟨machine, none⟩
    ⟨retMemPlace, memLayout⟩ true none refAccessConfig.globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
    refAccessConfig.dynamicLayout
    ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩
    h_uns rfl (by dsimp only; rw [h_lsz]; exact h_ptr)

private theorem writeMemory_retPlace_scalar (w : IntWidth)
    (layout : LocalLayout) (abi : Miri.ABI.Scalar) (bits : BitVec 128)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_backend : (localMemoryLayout layout).backendRepr = .Scalar abi)
    (h_lsz : layout.layout.size = toMiriSize w)
    (h_prim : Miri.ABI.Primitive.size abi.primitive refAccessConfig.runtime =
      .ok (toMiriSize w))
    (h_nonptr : match abi.primitive with | .Pointer _ => True | _ => True)
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (toMiriSize w) Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, rawAlloc.withExtra
          (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize w))⟩)]) })
    (h_dr : st.machine.dataRace = none) :
    ∃ after,
      let mem' := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      Miri.Interpreter.PlaceMachine.writeMemory refAccessConfig (fun _ => true)
          (.scalar (.fromScalarInt (miriScalar w bits)))
          ⟨retMemPlace, layout⟩ st =
        .ok () { st with machine := { st.machine with memory := mem' } } ∧
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false =
        .ok (.fromScalarInt (miriScalar w bits)) ∧
      Allocation.clearProvenance (allocRange Size.ZERO (toMiriSize w))
          (Size.ofBytes 8) after = .ok () after ∧
      after.byteSize = toMiriSize w ∧
      after.mutability = .Mut ∧
      after.align = Align.ONE := by
  let _ := h_nonptr
  let ⟨_, h_raw_eq, h_rsz, _, _, h_rmut, _⟩ :=
    Allocation.tryNew_replicate_full (P := Miri.Memory.Provenance)
      (toMiriSize w) Align.ONE 1 (by decide) (by decide)
  rw [h_raw] at h_raw_eq
  injection h_raw_eq with h_raw_id
  subst h_raw_id
  let alloc := rawAlloc.withExtra
    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize w))
  let ⟨after, h_w, h_rd, h_cp, h_asz, h_amut, h_aal, _⟩ :=
    tryNew_writeScalar_readScalar w bits h_raw
  have h_sc_sz : (Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
      (miriScalar w bits)).size = toMiriSize w := miriScalar_size w bits
  have h_lml_sz : (localMemoryLayout layout).size = toMiriSize w := h_lsz
  have h_uns : (localMemoryLayout layout).backendRepr.isUnsized = false := by
    rw [h_backend]; rfl
  have h_ptr_acc := getPtrAllocMut_retPlace_nonGhost w mem1 alloc st.machine
    h_rsz h_rmut rfl h_dr
  have h_place_acc :
      Miri.Interpreter.getPlaceAllocMut
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
        ⟨st.machine, none⟩
        ⟨retMemPlace, localMemoryLayout layout⟩
        refAccessConfig.runtime false none refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (localMemoryLayout layout).size, alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (localMemoryLayout layout).size, alloc⟩)⟩ := by
    refine Miri.Interpreter.getPlaceAllocMut_sized_of_access _ _ _ _
      (Size.ofBytes 8) none _ _ _ _ h_uns rfl rfl ?_
    rw [h_lml_sz]
    exact h_ptr_acc
  have h_wm_op :
      Miri.Interpreter.writeImmediateToMplaceNoValidate
        st.machine.memory ⟨st.machine, none⟩
        (.scalar (.fromScalarInt (miriScalar w bits)))
        ⟨retMemPlace, localMemoryLayout layout⟩
        refAccessConfig.runtime refAccessConfig.ghostMode
        refAccessConfig.globalKind refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout (fun _ => true) =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (localMemoryLayout layout).size, after⟩,
        .ok ()⟩ := by
    rw [h_mem]
    refine Miri.Interpreter.writeImmediate_scalar_of_access
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      ⟨st.machine, none⟩
      ⟨retMemPlace, localMemoryLayout layout⟩
      refAccessConfig.runtime none refAccessConfig.globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
      refAccessConfig.dynamicLayout (fun _ => true)
      (.fromScalarInt (miriScalar w bits)) abi retAllocId alloc after
      h_backend
      (by rw [h_sc_sz]; exact h_prim)
      (by cases abi.primitive with | Pointer _ => exact True.intro | _ => rfl)
      (by rw [h_sc_sz, h_lml_sz]; exact Nat.le_refl _)
      h_place_acc
      (by rw [h_sc_sz]; exact h_w)
      (singleton_setLiveAllocation mem1 alloc after)
  exact ⟨after,
    Miri.Interpreter.PlaceMachine.writeMemory_of_result refAccessConfig
      (fun _ => true) (.scalar (.fromScalarInt (miriScalar w bits)))
      ⟨retMemPlace, layout⟩ st
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      _ rfl h_wm_op,
    h_rd, h_cp, h_asz, h_amut, h_aal⟩

private theorem writeUninit_of_access_poly {P E K H X : Type}
    [DecidableEq K] [DecidableEq P] [PointerProvenance P]
    (memory afterMemory : Miri.Memory.MemoryState P E K) (hooks : H)
    (place : Miri.Interpreter.MemoryOperandPlace P)
    (runtime : RuntimeTargetDataLayout) (ghost : Bool) (kind : Option K)
    (global : Miri.Memory.GlobalAllocationHooks P E K H)
    (access : Miri.Memory.AllocationAccessHooks P E K H X)
    (dynamic : Miri.Interpreter.DynamicLayoutResolver P E K H)
    (later : Miri.Interpreter.MemoryOperandLayout → Bool)
    (ref : Miri.Memory.AllocationAccessRef P E) (after : Allocation P E)
    (sized : place.layout.backendRepr.isUnsized = false)
    (actual : Miri.Interpreter.getPlaceAllocMut memory hooks place runtime
      ghost kind global access dynamic =
      ⟨memory, hooks, some ref, .ok (some ref)⟩)
    (written : Allocation.writeUninit ref.range runtime.pointerSize
      ref.allocation = .ok () after)
    (committed : memory.setLiveAllocation ref.allocId after = .ok afterMemory) :
    Miri.Interpreter.writeImmediateToMplaceNoValidate memory hooks .uninit
        place runtime ghost kind global access dynamic later =
      ⟨afterMemory, hooks, some { ref with allocation := after }, .ok ()⟩ := by
  dsimp only [Miri.Interpreter.writeImmediateToMplaceNoValidate, Id.run,
    bind, Bind.bind, pure, Pure.pure]
  rw [sized]
  simp only [Bool.false_eq_true, ite_false]
  change (match (if place.layout.backendRepr.isUnsized = true then
      Except.error Miri.Interpreter.MemoryOperandError.unsizedImmediateWrite
      else Except.ok ()) with
    | Except.error error => _
    | Except.ok () => _) = _
  rw [sized]
  simp only [Bool.false_eq_true, ite_false]
  rw [actual]
  dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  change (match (memory.setLiveAllocation ref.allocId
      (match Allocation.writeUninit ref.range runtime.pointerSize ref.allocation with
       | EStateM.Result.ok _ a => a
       | EStateM.Result.error _ a => a)) with
    | Except.ok next => _
    | Except.error error => _) = _
  rw [written]
  dsimp only
  rw [committed]
  rfl

private theorem writeMemory_retPlace_uninit (w : IntWidth)
    (layout : LocalLayout)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    {rawAlloc : Allocation Miri.Memory.Provenance Unit}
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_uns : (localMemoryLayout layout).backendRepr.isUnsized = false)
    (h_lsz : layout.layout.size = toMiriSize w)
    (h_raw : Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (toMiriSize w) Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc)
    (h_mem : st.machine.memory =
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, rawAlloc.withExtra
          (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize w))⟩)]) })
    (h_dr : st.machine.dataRace = none) :
    ∃ after info,
      let mem' := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      Miri.Interpreter.PlaceMachine.writeMemory refAccessConfig (fun _ => true)
          .uninit ⟨retMemPlace, layout⟩ st =
        .ok () { st with machine := { st.machine with memory := mem' } } ∧
      after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false =
        .error (.invalidUninitBytes info) ∧
      after.byteSize = toMiriSize w ∧
      after.mutability = .Mut ∧
      after.align = Align.ONE := by
  let ⟨_, h_raw_eq, h_rsz, _, _, h_rmut, _⟩ :=
    Allocation.tryNew_replicate_full (P := Miri.Memory.Provenance)
      (toMiriSize w) Align.ONE 1 (by decide) (by decide)
  rw [h_raw] at h_raw_eq
  injection h_raw_eq with h_raw_id
  subst h_raw_id
  let alloc := rawAlloc.withExtra
    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one (toMiriSize w))
  let ⟨after, info, h_wu, h_rd, h_asz, h_amut, h_aal, _⟩ :=
    tryNew_writeUninit_readUninit w h_raw
  have h_lml_sz : (localMemoryLayout layout).size = toMiriSize w := h_lsz
  have h_ptr_acc := getPtrAllocMut_retPlace_nonGhost w mem1 alloc st.machine
    h_rsz h_rmut rfl h_dr
  have h_place_acc :
      Miri.Interpreter.getPlaceAllocMut
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
        ⟨st.machine, none⟩
        ⟨retMemPlace, localMemoryLayout layout⟩
        refAccessConfig.runtime false none refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩)⟩ := by
    have h_p := Miri.Interpreter.getPlaceAllocMut_sized_of_access
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
      ⟨st.machine, none⟩
      ⟨retMemPlace, localMemoryLayout layout⟩
      refAccessConfig.runtime (Size.ofBytes 8) none refAccessConfig.globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
      refAccessConfig.dynamicLayout
      ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩
      h_uns rfl rfl (by rw [h_lml_sz]; exact h_ptr_acc)
    exact h_p
  have h_wm_op :
      Miri.Interpreter.writeImmediateToMplaceNoValidate
        st.machine.memory ⟨st.machine, none⟩ .uninit
        ⟨retMemPlace, localMemoryLayout layout⟩
        refAccessConfig.runtime refAccessConfig.ghostMode
        refAccessConfig.globalKind refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout (fun _ => true) =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
        .ok ()⟩ := by
    rw [h_mem]
    exact writeUninit_of_access_poly
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, alloc⟩)]) }
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      ⟨st.machine, none⟩ ⟨retMemPlace, localMemoryLayout layout⟩
      refAccessConfig.runtime refAccessConfig.ghostMode
      refAccessConfig.globalKind refAccessConfig.globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
      refAccessConfig.dynamicLayout (fun _ => true)
      ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), alloc⟩ after
      h_uns h_place_acc h_wu (singleton_setLiveAllocation mem1 alloc after)
  exact ⟨after, info,
    Miri.Interpreter.PlaceMachine.writeMemory_of_result refAccessConfig
      (fun _ => true) .uninit ⟨retMemPlace, layout⟩ st
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      _ rfl h_wm_op,
    h_rd, h_asz, h_amut, h_aal⟩

private theorem readImmediateFromMplaceRaw_retPlace_I8
    (s : Bool) (al : Align) (vr : Miri.ABI.WrappingRange) (cty : Option Nat)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_acc :
      let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      let layout : Miri.Interpreter.MemoryOperandLayout :=
        ⟨Size.ofBytes 1, al,
          .Scalar (.Initialized (value := .Int .I8 s) (validRange := vr)), cty⟩
      Miri.Interpreter.getPlaceAlloc mem ⟨machine, none⟩
          ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
          cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
          cfg.dynamicLayout =
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 1), after⟩,
          .ok (some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 1), after⟩)⟩) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let layout : Miri.Interpreter.MemoryOperandLayout :=
      ⟨Size.ofBytes 1, al,
        .Scalar (.Initialized (value := .Int .I8 s) (validRange := vr)), cty⟩
    Miri.Interpreter.readImmediateFromMplaceRaw mem ⟨machine, none⟩
        ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (Size.ofBytes 1)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 1), after⟩,
          .ok (some ⟨.scalar sc, layout⟩)⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 1), after⟩,
          .error (.allocation err)⟩ := by
  intro mem layout
  dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run, pure,
    Pure.pure, bind, Bind.bind, layout, Miri.ABI.BackendRepr.isUnsized]
  rw [h_acc]
  simp only [Bool.false_eq_true, ite_false]
  change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
    (Except.mapError Miri.Interpreter.MemoryOperandError.allocation
      (after.readScalar RuntimeTargetDataLayout.default.base
        (allocRange Size.ZERO (Size.ofBytes 1)) false)) _ _ = _
  cases after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (Size.ofBytes 1)) false <;> rfl

private theorem readImmediateFromMplaceRaw_retPlace_I16
    (s : Bool) (al : Align) (vr : Miri.ABI.WrappingRange) (cty : Option Nat)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_acc :
      let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      let layout : Miri.Interpreter.MemoryOperandLayout :=
        ⟨Size.ofBytes 2, al,
          .Scalar (.Initialized (value := .Int .I16 s) (validRange := vr)), cty⟩
      Miri.Interpreter.getPlaceAlloc mem ⟨machine, none⟩
          ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
          cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
          cfg.dynamicLayout =
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 2), after⟩,
          .ok (some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 2), after⟩)⟩) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let layout : Miri.Interpreter.MemoryOperandLayout :=
      ⟨Size.ofBytes 2, al,
        .Scalar (.Initialized (value := .Int .I16 s) (validRange := vr)), cty⟩
    Miri.Interpreter.readImmediateFromMplaceRaw mem ⟨machine, none⟩
        ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (Size.ofBytes 2)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 2), after⟩,
          .ok (some ⟨.scalar sc, layout⟩)⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 2), after⟩,
          .error (.allocation err)⟩ := by
  intro mem layout
  dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run, pure,
    Pure.pure, bind, Bind.bind, layout, Miri.ABI.BackendRepr.isUnsized]
  rw [h_acc]
  simp only [Bool.false_eq_true, ite_false]
  change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
    (Except.mapError Miri.Interpreter.MemoryOperandError.allocation
      (after.readScalar RuntimeTargetDataLayout.default.base
        (allocRange Size.ZERO (Size.ofBytes 2)) false)) _ _ = _
  cases after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (Size.ofBytes 2)) false <;> rfl

private theorem readImmediateFromMplaceRaw_retPlace_I32
    (s : Bool) (al : Align) (vr : Miri.ABI.WrappingRange) (cty : Option Nat)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_acc :
      let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      let layout : Miri.Interpreter.MemoryOperandLayout :=
        ⟨Size.ofBytes 4, al,
          .Scalar (.Initialized (value := .Int .I32 s) (validRange := vr)), cty⟩
      Miri.Interpreter.getPlaceAlloc mem ⟨machine, none⟩
          ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
          cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
          cfg.dynamicLayout =
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 4), after⟩,
          .ok (some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 4), after⟩)⟩) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let layout : Miri.Interpreter.MemoryOperandLayout :=
      ⟨Size.ofBytes 4, al,
        .Scalar (.Initialized (value := .Int .I32 s) (validRange := vr)), cty⟩
    Miri.Interpreter.readImmediateFromMplaceRaw mem ⟨machine, none⟩
        ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (Size.ofBytes 4)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 4), after⟩,
          .ok (some ⟨.scalar sc, layout⟩)⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 4), after⟩,
          .error (.allocation err)⟩ := by
  intro mem layout
  dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run, pure,
    Pure.pure, bind, Bind.bind, layout, Miri.ABI.BackendRepr.isUnsized]
  rw [h_acc]
  simp only [Bool.false_eq_true, ite_false]
  change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
    (Except.mapError Miri.Interpreter.MemoryOperandError.allocation
      (after.readScalar RuntimeTargetDataLayout.default.base
        (allocRange Size.ZERO (Size.ofBytes 4)) false)) _ _ = _
  cases after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (Size.ofBytes 4)) false <;> rfl

private theorem readImmediateFromMplaceRaw_retPlace_I64
    (s : Bool) (al : Align) (vr : Miri.ABI.WrappingRange) (cty : Option Nat)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_acc :
      let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      let layout : Miri.Interpreter.MemoryOperandLayout :=
        ⟨Size.ofBytes 8, al,
          .Scalar (.Initialized (value := .Int .I64 s) (validRange := vr)), cty⟩
      Miri.Interpreter.getPlaceAlloc mem ⟨machine, none⟩
          ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
          cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
          cfg.dynamicLayout =
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 8), after⟩,
          .ok (some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 8), after⟩)⟩) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let layout : Miri.Interpreter.MemoryOperandLayout :=
      ⟨Size.ofBytes 8, al,
        .Scalar (.Initialized (value := .Int .I64 s) (validRange := vr)), cty⟩
    Miri.Interpreter.readImmediateFromMplaceRaw mem ⟨machine, none⟩
        ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (Size.ofBytes 8)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 8), after⟩,
          .ok (some ⟨.scalar sc, layout⟩)⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 8), after⟩,
          .error (.allocation err)⟩ := by
  intro mem layout
  dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run, pure,
    Pure.pure, bind, Bind.bind, layout, Miri.ABI.BackendRepr.isUnsized]
  rw [h_acc]
  simp only [Bool.false_eq_true, ite_false]
  change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
    (Except.mapError Miri.Interpreter.MemoryOperandError.allocation
      (after.readScalar RuntimeTargetDataLayout.default.base
        (allocRange Size.ZERO (Size.ofBytes 8)) false)) _ _ = _
  cases after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (Size.ofBytes 8)) false <;> rfl

private theorem readImmediateFromMplaceRaw_retPlace_I128
    (s : Bool) (al : Align) (vr : Miri.ABI.WrappingRange) (cty : Option Nat)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_acc :
      let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      let layout : Miri.Interpreter.MemoryOperandLayout :=
        ⟨Size.ofBytes 16, al,
          .Scalar (.Initialized (value := .Int .I128 s) (validRange := vr)), cty⟩
      Miri.Interpreter.getPlaceAlloc mem ⟨machine, none⟩
          ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
          cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
          cfg.dynamicLayout =
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 16), after⟩,
          .ok (some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 16), after⟩)⟩) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let layout : Miri.Interpreter.MemoryOperandLayout :=
      ⟨Size.ofBytes 16, al,
        .Scalar (.Initialized (value := .Int .I128 s) (validRange := vr)), cty⟩
    Miri.Interpreter.readImmediateFromMplaceRaw mem ⟨machine, none⟩
        ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (Size.ofBytes 16)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 16), after⟩,
          .ok (some ⟨.scalar sc, layout⟩)⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (Size.ofBytes 16), after⟩,
          .error (.allocation err)⟩ := by
  intro mem layout
  dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run, pure,
    Pure.pure, bind, Bind.bind, layout, Miri.ABI.BackendRepr.isUnsized]
  rw [h_acc]
  simp only [Bool.false_eq_true, ite_false]
  change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
    (Except.mapError Miri.Interpreter.MemoryOperandError.allocation
      (after.readScalar RuntimeTargetDataLayout.default.base
        (allocRange Size.ZERO (Size.ofBytes 16)) false)) _ _ = _
  cases after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (Size.ofBytes 16)) false <;> rfl

private theorem readImmediateFromMplaceRaw_retPlace_int_aux
    (w : IntWidth) (s : Bool) (al : Align) (vr : Miri.ABI.WrappingRange)
    (cty : Option Nat)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_acc :
      let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      let layout : Miri.Interpreter.MemoryOperandLayout :=
        ⟨toMiriSize w, al,
          .Scalar (.Initialized (value := .Int (toMiriInteger w) s)
            (validRange := vr)),
          cty⟩
      Miri.Interpreter.getPlaceAlloc mem ⟨machine, none⟩
          ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
          cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
          cfg.dynamicLayout =
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩)⟩) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let layout : Miri.Interpreter.MemoryOperandLayout :=
      ⟨toMiriSize w, al,
        .Scalar (.Initialized (value := .Int (toMiriInteger w) s)
          (validRange := vr)),
        cty⟩
    Miri.Interpreter.readImmediateFromMplaceRaw mem ⟨machine, none⟩
        ⟨retMemPlace, layout⟩ RuntimeTargetDataLayout.default true none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .ok (some ⟨.scalar sc, layout⟩)⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .error (.allocation err)⟩ := by
  cases w with
  | i8 => exact readImmediateFromMplaceRaw_retPlace_I8 s al vr cty mem1 after machine cfg h_acc
  | i16 => exact readImmediateFromMplaceRaw_retPlace_I16 s al vr cty mem1 after machine cfg h_acc
  | i32 => exact readImmediateFromMplaceRaw_retPlace_I32 s al vr cty mem1 after machine cfg h_acc
  | i64 => exact readImmediateFromMplaceRaw_retPlace_I64 s al vr cty mem1 after machine cfg h_acc
  | i128 => exact readImmediateFromMplaceRaw_retPlace_I128 s al vr cty mem1 after machine cfg h_acc
  | isize => exact readImmediateFromMplaceRaw_retPlace_I64 s al vr cty mem1 after machine cfg h_acc

private theorem readImmediateFromMplaceRaw_retPlace_core (types : List MirTy)
    (w : IntWidth) (ty : MirTy)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_rt : cfg.runtime = Miri.ABI.RuntimeTargetDataLayout.default)
    (h_gk : cfg.globalKind = none)
    (h_res : cfg.resolvePointer = refResolvePointer)
    (h_gh : cfg.globalHooks = refGlobalAllocationHooks)
    (h_ty : (ty = .bool ∧ w = .i8) ∨ (∃ s, ty = .int w s))
    (h_sz : after.byteSize = toMiriSize w) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    Miri.Interpreter.readImmediateFromMplaceRaw mem ⟨machine, none⟩
        ⟨retMemPlace, localMemoryLayout (refLocalLayoutForTy types ty)⟩
        RuntimeTargetDataLayout.default true none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .ok (some ⟨.scalar sc, localMemoryLayout (refLocalLayoutForTy types ty)⟩)⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .error (.allocation err)⟩ := by
  intro mem
  have h_uns : (localMemoryLayout (refLocalLayoutForTy types ty)).backendRepr.isUnsized = false := by
    cases h_ty with
    | inl h => rw [h.1]; rfl
    | inr h => let ⟨s, hs⟩ := h; rw [hs]; cases w <;> cases s <;> rfl
  have h_lsz : (localMemoryLayout (refLocalLayoutForTy types ty)).size = toMiriSize w := by
    cases h_ty with
    | inl h => rw [h.1, h.2]; rfl
    | inr h => let ⟨s, hs⟩ := h; rw [hs]; rfl
  have h_acc := getPlaceAlloc_retPlace_ghost w
    (localMemoryLayout (refLocalLayoutForTy types ty))
    mem1 after machine cfg h_rt h_gk h_res h_gh h_uns h_lsz h_sz
  rw [h_rt, h_gk] at h_acc
  cases h_ty with
  | inl h =>
    let ⟨hty, hw⟩ := h
    subst hty hw
    dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run, pure,
      Pure.pure, bind, Bind.bind]
    rw [h_acc]
    dsimp only [localMemoryLayout, refLocalLayoutForTy, refLayoutDataForTy,
      refBoolLayoutData, refBaseLayoutData, Miri.ABI.BackendRepr.isUnsized]
    simp only [Bool.false_eq_true, ite_false]
    change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
      (Except.mapError Miri.Interpreter.MemoryOperandError.allocation
        (after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize .i8)) false)) _ _ = _
    cases after.readScalar RuntimeTargetDataLayout.default.base
        (allocRange Size.ZERO (toMiriSize .i8)) false <;> rfl
  | inr h =>
    let ⟨s, hty⟩ := h
    subst hty
    exact readImmediateFromMplaceRaw_retPlace_int_aux w s
      (Miri.ABI.AbiAlign.new Align.ONE).abi
      (refFullWrappingRangeSize (toMiriSize w))
      (some (tyIdFor types (.int w s)))
      mem1 after machine cfg h_acc

private theorem readImmediate_mem_retPlace_core (types : List MirTy)
    (w : IntWidth) (ty : MirTy)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_rt : cfg.runtime = Miri.ABI.RuntimeTargetDataLayout.default)
    (h_gk : cfg.globalKind = none)
    (h_res : cfg.resolvePointer = refResolvePointer)
    (h_gh : cfg.globalHooks = refGlobalAllocationHooks)
    (h_ty : (ty = .bool ∧ w = .i8) ∨ (∃ s, ty = .int w s))
    (h_sz : after.byteSize = toMiriSize w) :
    let mem := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    Miri.Interpreter.readImmediate mem ⟨machine, none⟩
        (.indirect retMemPlace)
        (localMemoryLayout (refLocalLayoutForTy types ty))
        cfg.runtime true cfg.globalKind cfg.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks cfg) cfg.dynamicLayout =
      match after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (toMiriSize w)) false with
      | .ok sc =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .ok ⟨.scalar sc, localMemoryLayout (refLocalLayoutForTy types ty)⟩⟩
      | .error err =>
        ⟨mem, ⟨machine, none⟩,
          some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
          .error (.allocation err)⟩ := by
  intro mem
  have h_raw := readImmediateFromMplaceRaw_retPlace_core types w ty mem1 after
    machine cfg h_rt h_gk h_res h_gh h_ty h_sz
  rw [h_rt, h_gk]
  cases h_ty with
  | inl h =>
    let ⟨hty, hw⟩ := h
    subst hty hw
    dsimp only [Miri.Interpreter.readImmediate, Miri.Interpreter.readImmediateRaw,
      Id.run, pure, Pure.pure, bind, Bind.bind]
    rw [h_raw]
    cases after.readScalar RuntimeTargetDataLayout.default.base
        (allocRange Size.ZERO (toMiriSize .i8)) false <;> rfl
  | inr h =>
    let ⟨s, hty⟩ := h
    subst hty
    cases w <;> cases s <;> (
      dsimp only [Miri.Interpreter.readImmediate, Miri.Interpreter.readImmediateRaw,
        Id.run, pure, Pure.pure, bind, Bind.bind]
      rw [h_raw]
      cases after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO _) false <;> rfl)

private theorem validityMemory_readImmediate_mem_scalar (types : List MirTy)
    (w : IntWidth) (ty : MirTy) (sc : Scalar Miri.Memory.Provenance)
    (expected : ExpectedValue)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_ty : (ty = .bool ∧ w = .i8) ∨ (∃ s, ty = .int w s))
    (h_mem : st.machine.memory = { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize w)
    (h_rd : after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (toMiriSize w)) false = .ok sc) :
    Miri.Interpreter.ValidityMemory.readImmediate refValidityMemoryEnv
        ⟨.indirect retMemPlace, refLocalLayoutForTy types ty⟩ expected st =
      .ok ⟨.scalar sc, refLocalLayoutForTy types ty⟩ st := by
  have h_core := readImmediate_mem_retPlace_core types w ty mem1 after
    st.machine refAccessConfig rfl rfl rfl rfl h_ty h_sz
  rw [h_rd] at h_core
  dsimp only [Miri.Interpreter.ValidityMemory.readImmediate,
    refValidityMemoryEnv, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_mem]
  have h_core' :
      Miri.Interpreter.readImmediate
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
        ⟨st.machine, none⟩ (.indirect retMemPlace)
        (localMemoryLayout (refLocalLayoutForTy types ty))
        refAccessConfig.runtime true none refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
        .ok ⟨.scalar sc, localMemoryLayout (refLocalLayoutForTy types ty)⟩⟩ := h_core
  rw [h_core']
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_mem
      subst h_mem
      rfl

private theorem validityMemory_readImmediate_mem_uninit (types : List MirTy)
    (w : IntWidth) (ty : MirTy) (info : Option Miri.Memory.BadBytesAccess)
    (expected : ExpectedValue)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_ty : (ty = .bool ∧ w = .i8) ∨ (∃ s, ty = .int w s))
    (h_mem : st.machine.memory = { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize w)
    (h_rd : after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (toMiriSize w)) false = .error (.invalidUninitBytes info)) :
    ∃ msg,
      Miri.Interpreter.ValidityMemory.readImmediate refValidityMemoryEnv
          ⟨.indirect retMemPlace, refLocalLayoutForTy types ty⟩ expected st =
        .error (.undefinedBehavior msg) st := by
  have h_core := readImmediate_mem_retPlace_core types w ty mem1 after
    st.machine refAccessConfig rfl rfl rfl rfl h_ty h_sz
  rw [h_rd] at h_core
  dsimp only [Miri.Interpreter.ValidityMemory.readImmediate,
    refValidityMemoryEnv, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_mem]
  have h_core' :
      Miri.Interpreter.readImmediate
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
        ⟨st.machine, none⟩ (.indirect retMemPlace)
        (localMemoryLayout (refLocalLayoutForTy types ty))
        refAccessConfig.runtime true none refAccessConfig.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig)
        refAccessConfig.dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
        .error (.allocation (.invalidUninitBytes info))⟩ := h_core
  rw [h_core']
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_mem
      subst h_mem
      exact ⟨_, rfl⟩

private theorem placeMachine_readImmediate_mem_scalar_ghost (types : List MirTy)
    (tagW : IntWidth) (tagS : Bool) (sc : Scalar Miri.Memory.Provenance)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_mem : st.machine.memory = { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize tagW)
    (h_rd : after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (toMiriSize tagW)) false = .ok sc) :
    Miri.Interpreter.PlaceMachine.readImmediate
        { refAccessConfig with ghostMode := true, deinitMovedPlace := false }
        ⟨.indirect retMemPlace, refLocalLayoutForTy types (.int tagW tagS)⟩ st =
      .ok ⟨.scalar sc, refLocalLayoutForTy types (.int tagW tagS)⟩ st := by
  let cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser :=
    { refAccessConfig with ghostMode := true, deinitMovedPlace := false }
  have h_core := readImmediate_mem_retPlace_core types tagW (.int tagW tagS)
    mem1 after st.machine cfg rfl rfl rfl rfl (Or.inr ⟨tagS, rfl⟩) h_sz
  rw [h_rd] at h_core
  have h_take : Miri.Interpreter.PlaceMachine.takePendingMoveDeinit false st =
      .ok false st := by
    cases st with
    | mk stack machine =>
      cases machine with
      | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
          user pendingMoveDeinit =>
        dsimp only at h_pmd
        subst h_pmd
        rfl
  change Miri.Interpreter.PlaceMachine.readImmediate cfg
      ⟨.indirect retMemPlace, refLocalLayoutForTy types (.int tagW tagS)⟩ st = _
  dsimp only [Miri.Interpreter.PlaceMachine.readImmediate]
  change (EStateM.bind (Miri.Interpreter.PlaceMachine.takePendingMoveDeinit false) _ st) = _
  rw [eStateM_bind_ok h_take]
  dsimp only [get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_mem]
  have h_core' :
      Miri.Interpreter.readImmediate
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
        ⟨st.machine, none⟩ (.indirect retMemPlace)
        (localMemoryLayout (refLocalLayoutForTy types (.int tagW tagS)))
        cfg.runtime cfg.ghostMode cfg.globalKind cfg.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks cfg) cfg.dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize tagW), after⟩,
        .ok ⟨.scalar sc, localMemoryLayout (refLocalLayoutForTy types (.int tagW tagS))⟩⟩ := h_core
  rw [h_core']
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_mem
      subst h_mem
      rfl

private theorem clearPlaceProvenance_mem_step {K P E H X S C Extra : Type}
    [DecidableEq K] [PointerProvenance P]
    (env : Miri.Interpreter.ValidityMemory.Environment P E K H X S)
    (placeHooks : Miri.Interpreter.PlaceHooks P S C Extra) (choice : C)
    (valInProg : Miri.Interpreter.ValidityMemory.M S Bool)
    (afterWrite : Miri.MIR.LocalId → Bool → Miri.Interpreter.ValidityMemory.M S Unit)
    (mplace : Miri.Interpreter.MemPlace P) (layout : LocalLayout) (st st1 : S)
    (mem' : Miri.Memory.MemoryState P E K) (hooks' : H)
    (ref : Miri.Memory.AllocationAccessRef P E)
    (h_acc : Miri.Interpreter.getPlaceAllocMut (env.memory st) (env.hooks st)
        ⟨mplace, localMemoryLayout layout⟩ env.context.runtime true
        env.context.globalKind env.context.globalHooks
        env.context.accessHooks env.context.dynamicLayout =
      ⟨mem', hooks', some ref, .ok (some ref)⟩)
    (h_st1 : env.putTouched (env.putMemoryHooks st mem' hooks') (some ref) = st1)
    (entry : Miri.Memory.AllocId × Miri.Memory.LocalAllocation P E K)
    (h_find : (env.memory st1).live.find? (fun e => e.1 == ref.allocId) = some entry)
    (after : Allocation P E)
    (h_cp : Allocation.clearProvenance ref.range env.context.runtime.pointerSize
        entry.2.allocation = .ok () after)
    (mem'' : Miri.Memory.MemoryState P E K)
    (h_set : (env.memory st1).setLiveAllocation ref.allocId after = .ok mem'') :
    Miri.Interpreter.ValidityMemory.clearPlaceProvenance env placeHooks choice
        valInProg afterWrite ⟨.memory mplace, layout⟩ st =
      .ok () (env.putTouched (env.putMemoryHooks st1 mem'' (env.hooks st1))
        (some ⟨ref.allocId, ref.range, after⟩)) := by
  dsimp only [Miri.Interpreter.ValidityMemory.clearPlaceProvenance,
    Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
    Miri.Interpreter.asMplaceOrMutableLocal,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  change ((match
      (Miri.Interpreter.getPlaceAllocMut (env.memory st) (env.hooks st)
        ⟨mplace, localMemoryLayout layout⟩ env.context.runtime true
        env.context.globalKind env.context.globalHooks
        env.context.accessHooks env.context.dynamicLayout).outcome with
      | Except.ok reference => (fun s => _ : S → EStateM.Result StepError S Unit)
      | Except.error error => (fun s => _ : S → EStateM.Result StepError S Unit))
      (env.putTouched (env.putMemoryHooks st
        (Miri.Interpreter.getPlaceAllocMut (env.memory st) (env.hooks st)
          ⟨mplace, localMemoryLayout layout⟩ env.context.runtime true
          env.context.globalKind env.context.globalHooks
          env.context.accessHooks env.context.dynamicLayout).memory
        (Miri.Interpreter.getPlaceAllocMut (env.memory st) (env.hooks st)
          ⟨mplace, localMemoryLayout layout⟩ env.context.runtime true
          env.context.globalKind env.context.globalHooks
          env.context.accessHooks env.context.dynamicLayout).hooks)
        (Miri.Interpreter.getPlaceAllocMut (env.memory st) (env.hooks st)
          ⟨mplace, localMemoryLayout layout⟩ env.context.runtime true
          env.context.globalKind env.context.globalHooks
          env.context.accessHooks env.context.dynamicLayout).touched)) = _
  rw [h_acc]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_st1]
  change ((match
      (env.memory st1).live.find?
        (fun (e : Miri.Memory.AllocId × Miri.Memory.LocalAllocation P E K) =>
          e.1 == ref.allocId) with
    | some entry => (fun s => _ : S → EStateM.Result StepError S Unit)
    | _ => (fun s => _ : S → EStateM.Result StepError S Unit)) st1) = _
  rw [h_find]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_cp]
  dsimp only
  rw [h_set]
  rfl

private theorem clearPlaceProvenance_mem_retPlace (types : List MirTy)
    (c : Choice) (w : IntWidth) (ty : MirTy)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_ty : (ty = .bool ∧ w = .i8) ∨ (∃ s, ty = .int w s))
    (h_mem : st.machine.memory = { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize w)
    (h_mut : after.mutability = .Mut)
    (h_cp : Allocation.clearProvenance (allocRange Size.ZERO (toMiriSize w))
      (Size.ofBytes 8) after = .ok () after) :
    (refValHooks types).clearProvenance c
        ⟨.memory retMemPlace, refLocalLayoutForTy types ty⟩ st =
      .ok () st := by
  have h_uns : (localMemoryLayout (refLocalLayoutForTy types ty)).backendRepr.isUnsized = false := by
    cases h_ty with
    | inl h => rw [h.1]; rfl
    | inr h => let ⟨s, hs⟩ := h; rw [hs]; cases w <;> cases s <;> rfl
  have h_lsz : (localMemoryLayout (refLocalLayoutForTy types ty)).size = toMiriSize w := by
    cases h_ty with
    | inl h => rw [h.1, h.2]; rfl
    | inr h => let ⟨s, hs⟩ := h; rw [hs]; rfl
  have h_acc := getPlaceAllocMut_retPlace_ghost w
    (localMemoryLayout (refLocalLayoutForTy types ty))
    mem1 after st.machine h_uns h_lsz h_sz h_mut
  have h_st_eq :
      ({ st with machine := { st.machine with
          memory := { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) } } } :
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
        ⟨retMemPlace, localMemoryLayout (refLocalLayoutForTy types ty)⟩
        refValidityMemoryEnv.context.runtime true refValidityMemoryEnv.context.globalKind
        refValidityMemoryEnv.context.globalHooks refValidityMemoryEnv.context.accessHooks
        refValidityMemoryEnv.context.dynamicLayout =
      ⟨{ mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) },
        ⟨st.machine, none⟩,
        some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩,
        .ok (some ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩)⟩ := by
    dsimp only [refValidityMemoryEnv]
    rw [h_mem]
    exact h_acc
  rw [refValHooks_clearProvenance]
  have h_res := clearPlaceProvenance_mem_step refValidityMemoryEnv
    (refBasePlaceProjectionHooks types).place
    c (fun st => .ok false st) (fun _ _ st => .ok () st)
    retMemPlace (refLocalLayoutForTy types ty) st st
    { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    ⟨st.machine, none⟩
    ⟨retAllocId, allocRange Size.ZERO (toMiriSize w), after⟩
    h_env_acc h_st_eq (retAllocId, ⟨.stack, after⟩)
    (by dsimp only [refValidityMemoryEnv]; rw [h_mem]; exact singleton_live_find ⟨.stack, after⟩)
    after h_cp { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    (by dsimp only [refValidityMemoryEnv]; rw [h_mem]; exact singleton_setLiveAllocation mem1 after after)
  rw [h_res]
  dsimp only [refValidityMemoryEnv]
  rw [h_st_eq]

private theorem visit_mem_int_ok (types : List MirTy) (c : Choice) (fuel : Nat)
    (path : Miri.Memory.ValidationPath) (w : IntWidth) (s : Bool)
    (sc : Scalar Miri.Memory.Provenance)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types (.int w s)) = some (.int w s))
    (h_mem : st.machine.memory = { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize w)
    (h_mut : after.mutability = .Mut)
    (h_rd : after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (toMiriSize w)) false = .ok sc)
    (h_cp : Allocation.clearProvenance (allocRange Size.ZERO (toMiriSize w))
      (Size.ofBytes 8) after = .ok () after) :
    let sess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := path, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := some .empty
    }
    Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
        sess ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩ st =
      .ok { sess with dataBytes := some (singleDataRange w) } st := by
  intro sess
  have h_ri : (refValHooks types).readImmediate c
      ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩
      ExpectedValue.integer st =
      .ok ⟨.scalar sc, refLocalLayoutForTy types (.int w s)⟩ st := by
    rw [refValHooks_readImmediate]
    dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    exact validityMemory_readImmediate_mem_scalar types w (.int w s) sc
      ExpectedValue.integer mem1 after st (Or.inr ⟨s, rfl⟩) h_mem h_sz h_rd
  have h_clr := clearPlaceProvenance_mem_retPlace types c w (.int w s)
    mem1 after st (Or.inr ⟨s, rfl⟩) h_mem h_sz h_mut h_cp
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind, EStateM.bind]
  rw [refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind ((refValHooks types).readImmediate c
    ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩
    ExpectedValue.integer) _) _ st) = _
  rw [eStateM_bind_bind_ok h_ri]
  change (EStateM.bind (EStateM.bind (EStateM.pure sc) _) _ st) = _
  dsimp only [EStateM.bind, EStateM.pure, bind, Bind.bind, pure, Pure.pure]
  have h_ib : (Miri.Interpreter.ValidityVisitor.TypeKind.integer == .boolean) = false := rfl
  have h_ic : (Miri.Interpreter.ValidityVisitor.TypeKind.integer == .character) = false := rfl
  rw [h_ib, ite_false_eq, h_ic, ite_false_eq, ite_true_eq]
  change (EStateM.bind (EStateM.bind ((refValHooks types).clearProvenance c
    ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩) _) _ st) = _
  rw [eStateM_bind_bind_ok h_clr]
  dsimp only [EStateM.bind, EStateM.pure, bind, Bind.bind, pure, Pure.pure,
    refValHooks_toOp, Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
    refLocalLayoutForTy, refLayoutDataForTy, refScalarLayoutData, refBaseLayoutData]
  cases w <;> rfl

private theorem visit_mem_int_uninit_ub (types : List MirTy) (c : Choice) (fuel : Nat)
    (sess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (w : IntWidth) (s : Bool) (info : Option Miri.Memory.BadBytesAccess)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types (.int w s)) = some (.int w s))
    (h_mem : st.machine.memory = { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize w)
    (h_rd : after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (toMiriSize w)) false = .error (.invalidUninitBytes info)) :
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
          sess ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩ st =
        .error (.undefinedBehavior msg) st := by
  let ⟨msg, h_ri_raw⟩ := validityMemory_readImmediate_mem_uninit types w
    (.int w s) info ExpectedValue.integer mem1 after st (Or.inr ⟨s, rfl⟩)
    h_mem h_sz h_rd
  have h_ri : (refValHooks types).readImmediate c
      ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩
      ExpectedValue.integer st = .error (.undefinedBehavior msg) st := by
    rw [refValHooks_readImmediate]
    dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    exact h_ri_raw
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind, EStateM.bind]
  rw [refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind ((refValHooks types).readImmediate c
    ⟨.memory retMemPlace, refLocalLayoutForTy types (.int w s)⟩
    ExpectedValue.integer) _) _ st) = _
  rw [eStateM_bind_bind_err h_ri]

private theorem visit_mem_bool_ok (types : List MirTy) (c : Choice) (fuel : Nat)
    (path : Miri.Memory.ValidationPath) (b : Bool)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types .bool) = some .bool)
    (h_mem : st.machine.memory = { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize .i8)
    (h_mut : after.mutability = .Mut)
    (h_rd : after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (toMiriSize .i8)) false =
      .ok (.fromScalarInt (miriScalar .i8 (if b then 1 else 0))))
    (h_cp : Allocation.clearProvenance (allocRange Size.ZERO (toMiriSize .i8))
      (Size.ofBytes 8) after = .ok () after) :
    let sess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := path, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := some .empty
    }
    Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
        sess ⟨.memory retMemPlace, refLocalLayoutForTy types .bool⟩ st =
      .ok { sess with dataBytes := some (singleDataRange .i8) } st := by
  intro sess
  have h_ri : (refValHooks types).readImmediate c
      ⟨.memory retMemPlace, refLocalLayoutForTy types .bool⟩
      ExpectedValue.boolean st =
      .ok ⟨.scalar (.fromScalarInt (miriScalar .i8 (if b then 1 else 0))),
        refLocalLayoutForTy types .bool⟩ st := by
    rw [refValHooks_readImmediate]
    dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    exact validityMemory_readImmediate_mem_scalar types .i8 .bool _
      ExpectedValue.boolean mem1 after st (Or.inl ⟨rfl, rfl⟩) h_mem h_sz h_rd
  have h_clr := clearPlaceProvenance_mem_retPlace types c .i8 .bool
    mem1 after st (Or.inl ⟨rfl, rfl⟩) h_mem h_sz h_mut h_cp
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind, EStateM.bind]
  rw [refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind ((refValHooks types).readImmediate c
    ⟨.memory retMemPlace, refLocalLayoutForTy types .bool⟩
    ExpectedValue.boolean) _) _ st) = _
  rw [eStateM_bind_bind_ok h_ri]
  change (EStateM.bind (EStateM.bind (EStateM.pure
    (Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
      (miriScalar .i8 (if b then 1 else 0)))) _) _ st) = _
  dsimp only [EStateM.bind, EStateM.pure, bind, Bind.bind, pure, Pure.pure]
  have h_bb : (Miri.Interpreter.ValidityVisitor.TypeKind.boolean == .boolean) = true := rfl
  have h_bc : (Miri.Interpreter.ValidityVisitor.TypeKind.boolean == .character) = false := rfl
  rw [h_bb, ite_true_eq]
  cases b <;> (
    dsimp only [EStateM.bind, EStateM.pure, bind, Bind.bind, pure, Pure.pure]
    rw [h_bc, ite_false_eq, ite_true_eq]
    change (EStateM.bind (EStateM.bind ((refValHooks types).clearProvenance c
      ⟨.memory retMemPlace, refLocalLayoutForTy types .bool⟩) _) _ st) = _
    rw [eStateM_bind_bind_ok h_clr]
    rfl)

private theorem visit_mem_bool_uninit_ub (types : List MirTy) (c : Choice) (fuel : Nat)
    (sess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (info : Option Miri.Memory.BadBytesAccess)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types .bool) = some .bool)
    (h_mem : st.machine.memory = { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize .i8)
    (h_rd : after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (toMiriSize .i8)) false = .error (.invalidUninitBytes info)) :
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
          sess ⟨.memory retMemPlace, refLocalLayoutForTy types .bool⟩ st =
        .error (.undefinedBehavior msg) st := by
  let ⟨msg, h_ri_raw⟩ := validityMemory_readImmediate_mem_uninit types .i8
    .bool info ExpectedValue.boolean mem1 after st (Or.inl ⟨rfl, rfl⟩)
    h_mem h_sz h_rd
  have h_ri : (refValHooks types).readImmediate c
      ⟨.memory retMemPlace, refLocalLayoutForTy types .bool⟩
      ExpectedValue.boolean st = .error (.undefinedBehavior msg) st := by
    rw [refValHooks_readImmediate]
    dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    exact h_ri_raw
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind, EStateM.bind]
  rw [refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind ((refValHooks types).readImmediate c
    ⟨.memory retMemPlace, refLocalLayoutForTy types .bool⟩
    ExpectedValue.boolean) _) _ st) = _
  rw [eStateM_bind_bind_err h_ri]

private theorem placeDynamic_field0_mem_scalar_enum (types : List MirTy)
    (c : Choice) (ety : EnumTy) (tagW : IntWidth) (tagS : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_res : resolveTy types (tyIdFor types (.enum ety)) = some (.enum ety)) :
    Miri.Interpreter.PlaceDynamic.field (refBasePlaceProjectionHooks types) c
        ⟨.memory retMemPlace, refLocalLayoutForTy types (.enum ety)⟩ 0 st =
      .ok ⟨.memory retMemPlace, refLocalLayoutForTy types (.int tagW tagS)⟩ st := by
  have h_fo : (refLocalLayoutForTy types (.enum ety)).layout.fields.offset 0 =
      .ok Size.ZERO := by
    dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
    rw [h_tr]; rfl
  have h_fl : (refBasePlaceProjectionHooks types).field c
      (refLocalLayoutForTy types (.enum ety)) 0 st =
      .ok (refLocalLayoutForTy types (.int tagW tagS)) st := by
    dsimp only [refBasePlaceProjectionHooks, refProjectFieldLayout,
      refLocalLayoutForTy]
    rw [h_res]; dsimp only; rw [h_tr]; rfl
  have h_sz : (refLocalLayoutForTy types (.int tagW tagS)).layout.isSized = true :=
    refLayoutDataForTy_isSized (.int tagW tagS)
  dsimp only [Miri.Interpreter.PlaceDynamic.field, bind, Bind.bind, EStateM.bind]
  rw [h_fo]
  change (EStateM.bind ((refBasePlaceProjectionHooks types).field c
    (refLocalLayoutForTy types (.enum ety)) 0) _ st) = _
  rw [eStateM_bind_ok h_fl]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_sz, ite_not_true_eq]
  dsimp only [Miri.Interpreter.PlaceDynamic.offsetWithMeta,
    refBasePlaceProjectionHooks, Miri.Interpreter.PlaceMachine.placeHooks,
    refBaseCompilerHooks, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [placeMemoryOffset_retPlace_zero]

private theorem placeDynamic_downcast_mem_scalar_enum (types : List MirTy)
    (c : Choice) (ety : EnumTy) (variant : Nat)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types (.enum ety)) = some (.enum ety))
    (h_v_lt : variant < ety.discriminants.length) :
    Miri.Interpreter.PlaceDynamic.downcast (refBasePlaceProjectionHooks types) c
        ⟨.memory retMemPlace, refLocalLayoutForTy types (.enum ety)⟩ variant st =
      .ok ⟨.memory retMemPlace,
        ⟨tyIdFor types (.enum ety),
          { refUnitLayoutData with variants := .Single variant }⟩⟩ st := by
  have h_blt : Nat.blt variant ety.discriminants.length = true :=
    Nat.ble_eq_true_of_le h_v_lt
  have h_vl : (refBasePlaceProjectionHooks types).variant c
      (refLocalLayoutForTy types (.enum ety)) variant st =
      .ok ⟨tyIdFor types (.enum ety),
        { refUnitLayoutData with variants := .Single variant }⟩ st := by
    dsimp only [refBasePlaceProjectionHooks, refProjectVariantLayout,
      refLocalLayoutForTy]
    rw [h_res]; dsimp only; rw [h_blt]; rfl
  dsimp only [Miri.Interpreter.PlaceDynamic.downcast, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure]
  change (EStateM.bind ((refBasePlaceProjectionHooks types).variant c
    (refLocalLayoutForTy types (.enum ety)) variant) _ st) = _
  rw [eStateM_bind_ok h_vl]
  change Miri.Interpreter.PlaceDynamic.offsetWithMeta (refBasePlaceProjectionHooks types) c
    ⟨.memory retMemPlace, refLocalLayoutForTy types (.enum ety)⟩ Size.ZERO .inbounds .none
    ⟨tyIdFor types (.enum ety), { refUnitLayoutData with variants := .Single variant }⟩ st = _
  dsimp only [Miri.Interpreter.PlaceDynamic.offsetWithMeta,
    refBasePlaceProjectionHooks, Miri.Interpreter.PlaceMachine.placeHooks,
    refBaseCompilerHooks, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [placeMemoryOffset_retPlace_zero]

private theorem visit_mem_scalar_enum_ok (types : List MirTy) (c : Choice)
    (fuel k : Nat) (h_fuel : fuel = k + 1)
    (ety : EnumTy) (tagW : IntWidth) (tagS : Bool) (variant disc : Nat)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_adm : enumAdmitted ety = true)
    (h_res : resolveTy types (tyIdFor types (.enum ety)) = some (.enum ety))
    (h_get_d : MirSemantics.getElem? ety.discriminants variant = some disc)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_mem : st.machine.memory = { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize tagW)
    (h_mut : after.mutability = .Mut)
    (h_rd : after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (toMiriSize tagW)) false =
      .ok (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))))
    (h_cp : Allocation.clearProvenance (allocRange Size.ZERO (toMiriSize tagW))
      (Size.ofBytes 8) after = .ok () after) :
    let initSess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := some .empty
    }
    Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
        initSess ⟨.memory retMemPlace, refLocalLayoutForTy types (.enum ety)⟩ st =
      .ok { initSess with dataBytes := some (singleDataRange tagW) } st := by
  intro initSess
  have h_v_lt : variant < ety.discriminants.length :=
    mirGetElem?_lt_of_some h_get_d
  have h_ne_box :
      (Miri.Interpreter.ValidityVisitor.TypeKind.aggregate false false true == .box) =
        false := rfl
  have h_fields : (refLocalLayoutForTy types (.enum ety)).layout.fields =
      .Arbitrary (Array.mk [Size.ZERO]) (Array.mk [0]) := by
    dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
    rw [h_tr]
  have h_vars : (refLocalLayoutForTy types (.enum ety)).layout.variants =
      .Multiple (.Union (value := .Int (toMiriInteger tagW) tagS)) .Direct 0
        (ety.discriminants.map (fun _ => refInhabitedVariantLayout)).toArray := by
    dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
    rw [h_tr]
  have h_field0 := placeDynamic_field0_mem_scalar_enum types c ety tagW tagS st
    h_tr h_res
  have h_op_field0 :
      Miri.Interpreter.OperandMachine.field (refValidityOperandHooks types) c
        ⟨.indirect retMemPlace, refLocalLayoutForTy types (.enum ety)⟩ 0 st =
      .ok ⟨.indirect retMemPlace, refLocalLayoutForTy types (.int tagW tagS)⟩ st := by
    dsimp only [Miri.Interpreter.OperandMachine.field, refValidityOperandHooks,
      bind, Bind.bind, EStateM.bind]
    rw [h_field0]
    rfl
  have h_ri_ghost := placeMachine_readImmediate_mem_scalar_ghost types tagW tagS
    (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))
    mem1 after st h_pmd h_mem h_sz h_rd
  have h_rd_discr := readDiscriminant_validity_scalar_enum types c ety tagW tagS
    variant disc (.indirect retMemPlace)
    ⟨.indirect retMemPlace, refLocalLayoutForTy types (.int tagW tagS)⟩
    st h_tr h_adm h_res h_get_d h_op_field0 h_ri_ghost
  have h_dc := placeDynamic_downcast_mem_scalar_enum types c ety variant st
    h_res h_v_lt
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind, EStateM.bind]
  rw [refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (match (EStateM.Result.ok none st :
      EStateM.Result StepError (Miri.Interpreter.MachineHooks.State Unit RefUser)
        (Option (Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance))) with
    | EStateM.Result.ok a s => _
    | EStateM.Result.error e s => EStateM.Result.error e s) = _
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ne_box, ite_false_eq, h_fields, h_vars]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [forIn_singleton_array]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [refValHooks_projection, h_field0]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [refValHooks_fieldPath]
  dsimp only [bind, Bind.bind, EStateM.bind, initSess, Bool.or]
  rw [h_fuel]
  rw [visit_mem_int_ok types c k ({ originalType := "" : Miri.Memory.ValidationPath }.push .enumTag) tagW tagS
    (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))
    mem1 after st (resolveTy_tyIdFor_int types tagW tagS) h_mem h_sz h_mut h_rd h_cp]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_toOp]
  dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_discriminant, h_rd_discr]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [h_dc]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [refValHooks_variantPath]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [visit_local_fieldless_enum types c k _ _ ety variant st rfl h_res rfl rfl rfl]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_opsemInhabited, h_res]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [ite_true_eq, refValHooks_debugAssertions, ite_false_eq]
  rfl

private theorem visit_mem_scalar_enum_uninit_ub (types : List MirTy) (c : Choice)
    (fuel k : Nat) (h_fuel : fuel = k + 1)
    (ety : EnumTy) (tagW : IntWidth) (tagS : Bool)
    (info : Option Miri.Memory.BadBytesAccess)
    (mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (after : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_res : resolveTy types (tyIdFor types (.enum ety)) = some (.enum ety))
    (h_mem : st.machine.memory = { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) })
    (h_sz : after.byteSize = toMiriSize tagW)
    (h_rd : after.readScalar RuntimeTargetDataLayout.default.base
      (allocRange Size.ZERO (toMiriSize tagW)) false =
      .error (.invalidUninitBytes info)) :
    let initSess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := some .empty
    }
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
          initSess ⟨.memory retMemPlace, refLocalLayoutForTy types (.enum ety)⟩ st =
        .error (.undefinedBehavior msg) st := by
  intro initSess
  have h_ne_box :
      (Miri.Interpreter.ValidityVisitor.TypeKind.aggregate false false true == .box) =
        false := rfl
  have h_fields : (refLocalLayoutForTy types (.enum ety)).layout.fields =
      .Arbitrary (Array.mk [Size.ZERO]) (Array.mk [0]) := by
    dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
    rw [h_tr]
  have h_field0 := placeDynamic_field0_mem_scalar_enum types c ety tagW tagS st
    h_tr h_res
  let ⟨msg, h_v0⟩ := visit_mem_int_uninit_ub types c k
    { path := { originalType := "" : Miri.Memory.ValidationPath }.push .enumTag,
      flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := some .empty }
    tagW tagS info mem1 after st (resolveTy_tyIdFor_int types tagW tagS)
    h_mem h_sz h_rd
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.ValidityVisitor.visit, bind, Bind.bind, EStateM.bind]
  rw [refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (match (EStateM.Result.ok none st :
      EStateM.Result StepError (Miri.Interpreter.MachineHooks.State Unit RefUser)
        (Option (Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance))) with
    | EStateM.Result.ok a s => _
    | EStateM.Result.error e s => EStateM.Result.error e s) = _
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ne_box, ite_false_eq, h_fields]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [forIn_singleton_array]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [refValHooks_projection, h_field0]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [refValHooks_fieldPath]
  dsimp only [bind, Bind.bind, EStateM.bind, initSess, Bool.or]
  rw [h_fuel, h_v0]

private theorem validatePlace_mem_zst_step (types : List MirTy) (c : Choice)
    (layout : LocalLayout)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_sz0 : layout.layout.size = Size.ZERO)
    (h_vis :
      let initSess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
        path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := some .empty
      }
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c 8
        initSess ⟨.memory retMemPlace, layout⟩ st = .ok initSess st) :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooks types) c 8
        ⟨.memory retMemPlace, layout⟩ false true st = .ok () st := by
  have h_bp : (refValHooks types).beginPadding c ⟨retMemPlace, layout⟩ Size.ZERO st =
      .ok none st := by
    change Miri.Interpreter.ValidityMemory.beginPadding refValidityMemoryEnv
      ⟨retMemPlace, layout⟩ Size.ZERO st = .ok none st
    exact Miri.Interpreter.ValidityMemory.beginPadding_zero refValidityMemoryEnv
      ⟨retMemPlace, layout⟩ st (by cases st with | mk stack machine => cases machine; rfl)
  have h_sa : (refValHooks types).sizeAndAlign c ⟨retMemPlace, layout⟩ st =
      .ok (some (Size.ZERO, layout.layout.align.abi)) st := by
    change EStateM.Result.ok (some (layout.layout.size, layout.layout.align.abi)) st = _
    rw [h_sz0]
  dsimp only [Miri.Interpreter.ValidityVisitor.validatePlace,
    bind, Bind.bind, EStateM.bind]
  rw [refValHooks_typeName]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    ite_true, ite_false]
  rw [refValHooks_withGhostValidation, ite_true_eq]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_toOp]
  dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [ite_false_eq, h_vis]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [Miri.Interpreter.ValidityVisitor.resetPadding_memory_zero (refValHooks types) c
    _ ⟨retMemPlace, layout⟩ st rfl h_sz0 h_sa h_bp]
  rfl

private theorem validatePlace_mem_scalar_step (types : List MirTy) (c : Choice)
    (w : IntWidth) (layout : LocalLayout)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_lsz : layout.layout.size = toMiriSize w)
    (h_vis :
      let initSess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
        path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := some .empty
      }
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c 8
        initSess ⟨.memory retMemPlace, layout⟩ st =
        .ok { initSess with dataBytes := some (singleDataRange w) } st) :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooks types) c 8
        ⟨.memory retMemPlace, layout⟩ false true st = .ok () st := by
  dsimp only [Miri.Interpreter.ValidityVisitor.validatePlace,
    bind, Bind.bind, EStateM.bind]
  rw [refValHooks_typeName]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    ite_true, ite_false]
  rw [refValHooks_withGhostValidation, ite_true_eq]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_toOp]
  dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [ite_false_eq, h_vis]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  cases layout with
  | mk tid ldata =>
    cases ldata with
    | mk fields variants backendRepr largestNiche abiAlign prefAlign sz maxReprAlign =>
      dsimp only at h_lsz
      subst h_lsz
      cases w <;> rfl

private theorem validatePlace_mem_ub_step (types : List MirTy) (c : Choice)
    (layout : LocalLayout)
    (st st' : Miri.Interpreter.MachineHooks.State Unit RefUser) (msg : String)
    (h_vis :
      let initSess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
        path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := some .empty
      }
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c 8
        initSess ⟨.memory retMemPlace, layout⟩ st =
        .error (.undefinedBehavior msg) st') :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooks types) c 8
        ⟨.memory retMemPlace, layout⟩ false true st =
      .error (.undefinedBehavior msg) st' := by
  dsimp only [Miri.Interpreter.ValidityVisitor.validatePlace,
    bind, Bind.bind, EStateM.bind]
  rw [refValHooks_typeName]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    ite_true, ite_false]
  rw [refValHooks_withGhostValidation, ite_true_eq]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_toOp]
  dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [ite_false_eq, h_vis]

private theorem copyRuntimePlace_imm_to_mem_step (rp : RefProg) (c : Choice)
    (ty : MirTy) (imm : Immediate Miri.Memory.Provenance)
    (mplace : Miri.Interpreter.MemPlace Miri.Memory.Provenance)
    (st st1 : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (res : EStateM.Result StepError
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Unit)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_wm : Miri.Interpreter.PlaceMachine.writeMemory refAccessConfig
      (fun _ => true) imm ⟨mplace, refLocalLayoutForTy rp.types ty⟩ st = .ok () st1)
    (h_val : Miri.Interpreter.ValidityVisitor.validatePlace (refValHooks rp.types) c 8
      ⟨.memory mplace, refLocalLayoutForTy rp.types ty⟩ false true st1 = res) :
    let h := Miri.Interpreter.ExecutionMachine.withValidation
      (refExecutionConfig rp) refLimits
    Miri.Interpreter.copyRuntimePlace
        (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
        ⟨.immediate imm, refLocalLayoutForTy rp.types ty⟩
        ⟨.memory mplace, refLocalLayoutForTy rp.types ty⟩ true st = res := by
  intro h
  have h_take : Miri.Interpreter.PlaceMachine.takePendingMoveDeinit true st =
      .ok false st := by
    cases st with
    | mk stack machine =>
      cases machine with
      | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
          user pendingMoveDeinit =>
        dsimp only at h_pmd
        subst h_pmd
        rfl
  have h_rr : Miri.Interpreter.PlaceMachine.readRaw refAccessConfig
      ⟨.immediate imm, refLocalLayoutForTy rp.types ty⟩ st =
      .ok (.immediate ⟨imm, localMemoryLayout (refLocalLayoutForTy rp.types ty)⟩) st := by
    cases st with
    | mk stack machine =>
      cases machine; rfl
  have h_sz : (refLocalLayoutForTy rp.types ty).layout.isSized = true :=
    refLayoutDataForTy_isSized ty
  have h_compat : h.copy.compatible (refLocalLayoutForTy rp.types ty)
      (refLocalLayoutForTy rp.types ty) = .ok true := by
    dsimp only [h, Miri.Interpreter.ExecutionMachine.withValidation,
      Miri.Interpreter.TypedMachineBindings.bindValidation,
      refExecutionConfig, refPlaceCopyHooks]
    rw [beq_self_eq_true]
  have h_wp :
      Miri.Interpreter.writePlaceImmediateNoValidate
        (Miri.Interpreter.PlaceMachine.placeHooks refAccessConfig refAllocationConfig
          (refCompilerHooks rp.types))
        c imm ⟨.memory mplace, refLocalLayoutForTy rp.types ty⟩ st = .ok () st1 := by
    dsimp only [Miri.Interpreter.writePlaceImmediateNoValidate,
      Miri.Interpreter.asMplaceOrMutableLocal,
      Miri.Interpreter.PlaceMachine.placeHooks,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [h_sz, ite_not_true_eq]
    exact h_wm
  have h_nv :
      Miri.Interpreter.copyRuntimePlaceNoValidate
        (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
        ⟨.immediate imm, refLocalLayoutForTy rp.types ty⟩
        ⟨.memory mplace, refLocalLayoutForTy rp.types ty⟩ true st = .ok () st1 := by
    dsimp only [Miri.Interpreter.copyRuntimePlaceNoValidate,
      Miri.Interpreter.ExecutionMachine.projectionHooks,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [h_compat]
    change (match (EStateM.Result.ok true st :
        EStateM.Result StepError (Miri.Interpreter.MachineHooks.State Unit RefUser) Bool) with
      | EStateM.Result.ok a s => _
      | EStateM.Result.error e s => EStateM.Result.error e s) = _
    dsimp only
    simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
    have h_pad : h.copy.hasPadding (refLocalLayoutForTy rp.types ty) = .ok false := rfl
    rw [h_pad]
    change (EStateM.bind (EStateM.pure false) _ st) = _
    rw [eStateM_bind_pure]
    change (EStateM.bind (Miri.Interpreter.PlaceMachine.takePendingMoveDeinit true) _ st) = _
    rw [eStateM_bind_ok h_take]
    simp only [Bool.false_eq_true, ite_false]
    change (EStateM.bind (Miri.Interpreter.PlaceMachine.readRaw refAccessConfig
      ⟨.immediate imm, refLocalLayoutForTy rp.types ty⟩) _ st) = _
    rw [eStateM_bind_ok h_rr]
    dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [h_sz, bne_self_eq_false]
    exact h_wp
  have h_ev :
      (Miri.Interpreter.ExecutionMachine.projectionHooks h).place.enforceValidity c
        (refLocalLayoutForTy rp.types ty) st1 = .ok true st1 := rfl
  have h_v :
      (Miri.Interpreter.ExecutionMachine.projectionHooks h).place.validate c
        ⟨.memory mplace, refLocalLayoutForTy rp.types ty⟩ st1 =
      Miri.Interpreter.ValidityVisitor.validatePlace (refValHooks rp.types) c 8
        ⟨.memory mplace, refLocalLayoutForTy rp.types ty⟩ false true st1 := rfl
  dsimp only [Miri.Interpreter.copyRuntimePlace, bind, Bind.bind, EStateM.bind]
  rw [h_nv]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ev]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  simp only [ite_true]
  rw [bne_self_eq_false, ite_false_eq, h_v, h_val]

/-- Executing `ExecutionControl.hooks.copyReturn` (`copyRuntimePlace` into the
fresh caller-owned `retPlace` allocation) on an initialized Day-1 return value
`v` succeeds, updates only `st.machine.memory` to `mem'`, and satisfies
`refReadReturnVal mem' retTy retPlace = .ok v`. -/
theorem copyReturn_ok (rp : RefProg) (c : Choice) (retTy : MirTy) (v : Val)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_init : refInitMemoryAndRetPlace rp.types retTy = .ok (mem, retPlace))
    (h_mem : st.machine.memory = mem)
    (h_dr : st.machine.dataRace = none)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_cv : checkVal v retTy = true)
    (h_res : resolveTy rp.types (tyIdFor rp.types retTy) = some retTy) :
    let h := Miri.Interpreter.ExecutionMachine.withValidation
      (refExecutionConfig rp) refLimits
    ∃ mem',
      Miri.Interpreter.copyRuntimePlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
          ⟨.immediate (valToMiriImmediate retTy v),
            refLocalLayoutForTy rp.types retTy⟩
          ⟨.memory retPlace.mplace, retPlace.layout⟩ true st =
        .ok () { st with machine := { st.machine with memory := mem' } } ∧
      refReadReturnVal mem' retTy retPlace = .ok v := by
  let ⟨mem1, rawAlloc, h_raw, _, _, _, _, _, _, h_mem_shape, h_rp_shape⟩ :=
    refInitMemoryAndRetPlace_shape rp.types retTy h_init
  rw [h_mem_shape] at h_mem
  rw [h_rp_shape]
  change let h := Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits
    ∃ mem',
      Miri.Interpreter.copyRuntimePlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
          ⟨.immediate (valToMiriImmediate retTy v),
            refLocalLayoutForTy rp.types retTy⟩
          ⟨.memory retMemPlace, refLocalLayoutForTy rp.types retTy⟩ true st =
        .ok () { st with machine := { st.machine with memory := mem' } } ∧
      refReadReturnVal mem' retTy ⟨retMemPlace, refLocalLayoutForTy rp.types retTy⟩ = .ok v
  cases checkVal_eq_true_inv h_cv with
  | inl h_i =>
    let ⟨w, s, bits, hty, hv, h_trunc⟩ := h_i
    subst hty hv
    let ⟨after, h_wm, h_rd, h_cp, h_asz, h_amut, _⟩ :=
      writeMemory_retPlace_scalar w (refLocalLayoutForTy rp.types (.int w s))
        (.Initialized (value := .Int (toMiriInteger w) s)
          (validRange := refFullWrappingRangeSize (toMiriSize w)))
        bits mem1 st rfl rfl (by cases w <;> cases s <;> rfl) trivial
        h_raw h_mem h_dr
    let mem' : Miri.Memory.MemoryState Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree Unit :=
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let st1 := { st with machine := { st.machine with memory := mem' } }
    have h_val : Miri.Interpreter.ValidityVisitor.validatePlace
        (refValHooks rp.types) c 8
        ⟨.memory retMemPlace, refLocalLayoutForTy rp.types (.int w s)⟩
        false true st1 = .ok () st1 :=
      validatePlace_mem_scalar_step rp.types c w _ st1 rfl
        (visit_mem_int_ok rp.types c 7 ⟨"", (Array.mk [])⟩ w s _ mem1 after st1 h_res
          rfl h_asz h_amut h_rd h_cp)
    refine ⟨mem',
      copyRuntimePlace_imm_to_mem_step rp c (.int w s) _ retMemPlace st st1 _
        h_pmd h_wm h_val, ?_⟩
    dsimp only [refReadReturnVal, retMemPlace, retPtr, mem']
    rw [singleton_live_find]
    dsimp only
    rw [h_rd]
    dsimp only
    rw [scalar_tryToScalarInt_fromScalarInt]
    dsimp only
    rw [miriScalar_data, h_trunc]
  | inr h_rest =>
    cases h_rest with
    | inl h_b =>
      let ⟨b, hty, hv⟩ := h_b
      subst hty hv
      have h_vimm : valToMiriImmediate .bool (.bool b) =
          .scalar (.fromScalarInt (miriScalar .i8 (if b then 1 else 0))) := by
        dsimp only [valToMiriImmediate]
        rw [scalar_fromBool_eq]
      rw [h_vimm]
      let ⟨after, h_wm, h_rd, h_cp, h_asz, h_amut, _⟩ :=
        writeMemory_retPlace_scalar .i8 (refLocalLayoutForTy rp.types .bool)
          (.Initialized (value := .Int .I8 false)
            (validRange := ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 1⟩))
          (if b then 1 else 0) mem1 st rfl rfl rfl trivial h_raw h_mem h_dr
      let mem' : Miri.Memory.MemoryState Miri.Memory.Provenance
          Miri.TreeBorrows.BorrowTree Unit :=
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      let st1 := { st with machine := { st.machine with memory := mem' } }
      have h_val : Miri.Interpreter.ValidityVisitor.validatePlace
          (refValHooks rp.types) c 8
          ⟨.memory retMemPlace, refLocalLayoutForTy rp.types .bool⟩
          false true st1 = .ok () st1 :=
        validatePlace_mem_scalar_step rp.types c .i8 _ st1 rfl
          (visit_mem_bool_ok rp.types c 7 ⟨"", (Array.mk [])⟩ b mem1 after st1 h_res
            rfl h_asz h_amut h_rd h_cp)
      refine ⟨mem',
        copyRuntimePlace_imm_to_mem_step rp c .bool _ retMemPlace st st1 _
          h_pmd h_wm h_val, ?_⟩
      dsimp only [refReadReturnVal, retMemPlace, retPtr, mem']
      rw [singleton_live_find]
      dsimp only
      have h_rd1 : after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (Size.ofBytes 1)) false =
          .ok (.fromScalarInt (miriScalar .i8 (if b then 1 else 0))) := h_rd
      rw [h_rd1]
      cases b <;> rfl
    | inr h_rest2 =>
      cases h_rest2 with
      | inl h_u =>
        let ⟨hty, hv⟩ := h_u
        subst hty hv
        have h_wm : Miri.Interpreter.PlaceMachine.writeMemory refAccessConfig
            (fun _ => true) .uninit
            ⟨retMemPlace, refLocalLayoutForTy rp.types .unit⟩ st = .ok () st :=
          Miri.Interpreter.PlaceMachine.writeMemory_zero_uninit refAccessConfig
            (fun _ => true) ⟨retMemPlace, refLocalLayoutForTy rp.types .unit⟩
            retPtr (some (tyIdFor rp.types .unit)) (Size.ofBytes 8)
            rfl rfl rfl (fun _ => rfl) st
        have h_val : Miri.Interpreter.ValidityVisitor.validatePlace
            (refValHooks rp.types) c 8
            ⟨.memory retMemPlace, refLocalLayoutForTy rp.types .unit⟩
            false true st = .ok () st :=
          validatePlace_mem_zst_step rp.types c _ st rfl
            (Miri.Interpreter.ValidityVisitor.visit_fieldless
              (refValHooks rp.types) c 7 _ _ st 0
              (by rw [refValHooks_classify]; dsimp only [refLocalLayoutForTy]; rw [h_res])
              (by rw [refValHooks_opsemInhabited]; dsimp only [refLocalLayoutForTy]; rw [h_res])
              rfl rfl rfl rfl)
        have h_st_eq :
            ({ st with machine := { st.machine with memory := st.machine.memory } } :
              Miri.Interpreter.MachineHooks.State Unit RefUser) = st := by
          cases st with | mk stack machine => cases machine; rfl
        refine ⟨st.machine.memory, ?_, rfl⟩
        rw [h_st_eq]
        exact copyRuntimePlace_imm_to_mem_step rp c .unit .uninit retMemPlace
          st st _ h_pmd h_wm h_val
      | inr h_e =>
        let ⟨ety, variant, hty, hv, h_adm, h_v_lt⟩ := h_e
        subst hty hv
        cases h_tr : ety.tagRepr with
        | zeroSized =>
          have h_zst : isZstEnumTy ety = true := by
            dsimp only [isZstEnumTy]
            rw [h_adm, h_tr]
          have h_len1 : ety.discriminants.length = 1 := by
            let ⟨_, _, h_tag⟩ := enumAdmitted_parts h_adm
            rw [h_tr] at h_tag
            dsimp only at h_tag
            exact Nat.eq_of_beq_eq_true h_tag
          have h_v0 : variant = 0 := by
            rw [h_len1] at h_v_lt
            cases variant with
            | zero => rfl
            | succ n => exact False.elim (Nat.not_lt_zero n (Nat.lt_of_succ_lt_succ h_v_lt))
          subst h_v0
          have h_vimm : valToMiriImmediate (.enum ety) (.enumVal ety 0) = .uninit := by
            dsimp only [valToMiriImmediate]; rw [h_tr]
          rw [h_vimm]
          have h_lml :
              localMemoryLayout (refLocalLayoutForTy rp.types (.enum ety)) =
                ⟨Size.ZERO, Align.ONE, .Memory (sized := true),
                  some (tyIdFor rp.types (.enum ety))⟩ := by
            dsimp only [localMemoryLayout, refLocalLayoutForTy, refLayoutDataForTy,
              refEnumLayoutData]
            rw [h_tr]; rfl
          have h_wm : Miri.Interpreter.PlaceMachine.writeMemory refAccessConfig
              (fun _ => true) .uninit
              ⟨retMemPlace, refLocalLayoutForTy rp.types (.enum ety)⟩ st =
              .ok () st :=
            Miri.Interpreter.PlaceMachine.writeMemory_zero_uninit refAccessConfig
              (fun _ => true) ⟨retMemPlace, refLocalLayoutForTy rp.types (.enum ety)⟩
              retPtr (some (tyIdFor rp.types (.enum ety))) (Size.ofBytes 8)
              h_lml rfl rfl (fun _ => rfl) st
          have h_sz0 : (refLocalLayoutForTy rp.types (.enum ety)).layout.size =
              Size.ZERO := by
            dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
            rw [h_tr]; rfl
          have h_val : Miri.Interpreter.ValidityVisitor.validatePlace
              (refValHooks rp.types) c 8
              ⟨.memory retMemPlace, refLocalLayoutForTy rp.types (.enum ety)⟩
              false true st = .ok () st :=
            validatePlace_mem_zst_step rp.types c _ st h_sz0
              (visit_local_fieldless_enum rp.types c 7 _ _ ety 0 st rfl h_res
                (by dsimp only [refLocalLayoutForTy, refLayoutDataForTy,
                      refEnumLayoutData]; rw [h_tr]; rfl)
                (by dsimp only [refLocalLayoutForTy, refLayoutDataForTy,
                      refEnumLayoutData]; rw [h_tr]; rfl)
                rfl)
          have h_st_eq :
              ({ st with machine := { st.machine with memory := st.machine.memory } } :
                Miri.Interpreter.MachineHooks.State Unit RefUser) = st := by
            cases st with | mk stack machine => cases machine; rfl
          refine ⟨st.machine.memory, ?_, ?_⟩
          · rw [h_st_eq]
            exact copyRuntimePlace_imm_to_mem_step rp c (.enum ety) .uninit
              retMemPlace st st _ h_pmd h_wm h_val
          · dsimp only [refReadReturnVal]
            rw [h_tr, refIsZstEnumTy_eq, h_zst]
            rfl
        | scalar tagW tagS =>
          let ⟨disc, h_get_d⟩ := mirGetElem?_some_of_lt h_v_lt
          have h_vimm : valToMiriImmediate (.enum ety) (.enumVal ety variant) =
              .scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))) := by
            dsimp only [valToMiriImmediate]
            rw [h_tr, h_get_d]
          rw [h_vimm]
          have h_lsz : (refLocalLayoutForTy rp.types (.enum ety)).layout.size =
              toMiriSize tagW := by
            dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
            rw [h_tr]; rfl
          rw [h_lsz] at h_raw h_mem
          let ⟨after, h_wm, h_rd, h_cp, h_asz, h_amut, _⟩ :=
            writeMemory_retPlace_scalar tagW (refLocalLayoutForTy rp.types (.enum ety))
              (.Union (value := .Int (toMiriInteger tagW) tagS))
              (BitVec.ofNat 128 disc) mem1 st
              (by dsimp only [localMemoryLayout, refLocalLayoutForTy,
                    refLayoutDataForTy, refEnumLayoutData]; rw [h_tr]; rfl)
              h_lsz
              (by cases tagW <;> cases tagS <;> rfl)
              trivial h_raw h_mem h_dr
          let mem' : Miri.Memory.MemoryState Miri.Memory.Provenance
              Miri.TreeBorrows.BorrowTree Unit :=
            { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
          let st1 := { st with machine := { st.machine with memory := mem' } }
          have h_val : Miri.Interpreter.ValidityVisitor.validatePlace
              (refValHooks rp.types) c 8
              ⟨.memory retMemPlace, refLocalLayoutForTy rp.types (.enum ety)⟩
              false true st1 = .ok () st1 :=
            validatePlace_mem_scalar_step rp.types c tagW _ st1 h_lsz
              (visit_mem_scalar_enum_ok rp.types c 7 6 rfl ety tagW tagS variant
                disc mem1 after st1 h_tr h_adm h_res h_get_d h_pmd rfl
                h_asz h_amut h_rd h_cp)
          refine ⟨mem',
            copyRuntimePlace_imm_to_mem_step rp c (.enum ety) _ retMemPlace
              st st1 _ h_pmd h_wm h_val, ?_⟩
          have h_ref_adm : refEnumAdmitted ety = true := by
            rw [refEnumAdmitted_eq]; exact h_adm
          let ⟨_, _, h_tag_all⟩ := enumAdmitted_parts h_adm
          rw [h_tr] at h_tag_all
          have h_tag_ok : tagBitsToDiscrBits tagW tagS ety.discrWidth
              (truncateBits tagW (BitVec.ofNat 128 disc)) = BitVec.ofNat 128 disc :=
            eq_of_beq (list_all_mirGetElem?
              (p := fun d =>
                tagBitsToDiscrBits tagW tagS ety.discrWidth
                  (truncateBits tagW (BitVec.ofNat 128 d)) == BitVec.ofNat 128 d)
              h_tag_all h_get_d)
          dsimp only [refReadReturnVal, retMemPlace, retPtr, mem']
          rw [h_tr]
          dsimp only
          rw [h_ref_adm, ite_not_true_eq, singleton_live_find]
          dsimp only
          rw [h_rd]
          dsimp only
          rw [scalar_tryToScalarInt_fromScalarInt]
          dsimp only
          rw [miriScalar_data, refMiriTagToDiscrBits_eq, h_tag_ok]
          dsimp only
          rw [refFindDiscrVariant?_eq,
            findDiscrVariant?_of_enumAdmitted h_adm h_get_d]

/-- Executing `ExecutionControl.hooks.copyReturn` on an uninitialized non-ZST
return local `_0` fails with `.undefinedBehavior`. -/
theorem copyReturn_uninit_ub (rp : RefProg) (c : Choice) (retTy : MirTy)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_init : refInitMemoryAndRetPlace rp.types retTy = .ok (mem, retPlace))
    (h_mem : st.machine.memory = mem)
    (h_dr : st.machine.dataRace = none)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_sm : SlotMatchesTy retTy (.live none))
    (h_supp : isSupportedScalarOrUnitTy retTy = true)
    (h_res : resolveTy rp.types (tyIdFor rp.types retTy) = some retTy) :
    let h := Miri.Interpreter.ExecutionMachine.withValidation
      (refExecutionConfig rp) refLimits
    ∃ msg st',
      Miri.Interpreter.copyRuntimePlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
          ⟨.immediate .uninit, refLocalLayoutForTy rp.types retTy⟩
          ⟨.memory retPlace.mplace, retPlace.layout⟩ true st =
        .error (.undefinedBehavior msg) st' := by
  let ⟨mem1, rawAlloc, h_raw, _, _, _, _, _, _, h_mem_shape, h_rp_shape⟩ :=
    refInitMemoryAndRetPlace_shape rp.types retTy h_init
  rw [h_mem_shape] at h_mem
  rw [h_rp_shape]
  change let h := Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits
    ∃ msg st',
      Miri.Interpreter.copyRuntimePlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
          ⟨.immediate .uninit, refLocalLayoutForTy rp.types retTy⟩
          ⟨.memory retMemPlace, refLocalLayoutForTy rp.types retTy⟩ true st =
        .error (.undefinedBehavior msg) st'
  let initSess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
    path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
    refTracking := none, dataBytes := some .empty
  }
  cases retTy with
  | unit => exact False.elim (h_sm.1 rfl)
  | never =>
    have h_wm : Miri.Interpreter.PlaceMachine.writeMemory refAccessConfig
        (fun _ => true) .uninit
        ⟨retMemPlace, refLocalLayoutForTy rp.types .never⟩ st = .ok () st :=
      Miri.Interpreter.PlaceMachine.writeMemory_zero_uninit refAccessConfig
        (fun _ => true) ⟨retMemPlace, refLocalLayoutForTy rp.types .never⟩
        retPtr (some (tyIdFor rp.types .never)) (Size.ofBytes 8)
        rfl rfl rfl (fun _ => rfl) st
    let ⟨msg, h_vis⟩ := visit_local_never_ub rp.types c 7 initSess
      ⟨.memory retMemPlace, refLocalLayoutForTy rp.types .never⟩ st rfl h_res
    exact ⟨msg, st, copyRuntimePlace_imm_to_mem_step rp c .never .uninit
      retMemPlace st st _ h_pmd h_wm
      (validatePlace_mem_ub_step rp.types c _ st st msg h_vis)⟩
  | bool =>
    let ⟨after, info, h_wm, h_rd, h_asz, _, _⟩ :=
      writeMemory_retPlace_uninit .i8 (refLocalLayoutForTy rp.types .bool)
        mem1 st rfl rfl h_raw h_mem h_dr
    let mem' : Miri.Memory.MemoryState Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree Unit :=
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let st1 := { st with machine := { st.machine with memory := mem' } }
    let ⟨msg, h_vis⟩ := visit_mem_bool_uninit_ub rp.types c 7 initSess info
      mem1 after st1 h_res rfl h_asz h_rd
    exact ⟨msg, st1, copyRuntimePlace_imm_to_mem_step rp c .bool .uninit
      retMemPlace st st1 _ h_pmd h_wm
      (validatePlace_mem_ub_step rp.types c _ st1 st1 msg h_vis)⟩
  | int w s =>
    let ⟨after, info, h_wm, h_rd, h_asz, _, _⟩ :=
      writeMemory_retPlace_uninit w (refLocalLayoutForTy rp.types (.int w s))
        mem1 st (by cases w <;> cases s <;> rfl) rfl h_raw h_mem h_dr
    let mem' : Miri.Memory.MemoryState Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree Unit :=
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let st1 := { st with machine := { st.machine with memory := mem' } }
    let ⟨msg, h_vis⟩ := visit_mem_int_uninit_ub rp.types c 7 initSess w s info
      mem1 after st1 h_res rfl h_asz h_rd
    exact ⟨msg, st1, copyRuntimePlace_imm_to_mem_step rp c (.int w s) .uninit
      retMemPlace st st1 _ h_pmd h_wm
      (validatePlace_mem_ub_step rp.types c _ st1 st1 msg h_vis)⟩
  | enum ety =>
    cases h_tr : ety.tagRepr with
    | zeroSized =>
      have h_zst := h_sm.2 ety rfl
      dsimp only [isZstEnumTy] at h_zst
      rw [h_tr] at h_zst
      dsimp only [isSupportedScalarOrUnitTy] at h_supp
      rw [h_supp] at h_zst
      cases h_zst
    | scalar tagW tagS =>
      have h_lsz : (refLocalLayoutForTy rp.types (.enum ety)).layout.size =
          toMiriSize tagW := by
        dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
        rw [h_tr]; rfl
      have h_uns :
          (localMemoryLayout (refLocalLayoutForTy rp.types (.enum ety))).backendRepr.isUnsized =
            false := by
        dsimp only [localMemoryLayout, refLocalLayoutForTy, refLayoutDataForTy,
          refEnumLayoutData]
        rw [h_tr]; rfl
      rw [h_lsz] at h_raw h_mem
      let ⟨after, info, h_wm, h_rd, h_asz, _, _⟩ :=
        writeMemory_retPlace_uninit tagW (refLocalLayoutForTy rp.types (.enum ety))
          mem1 st h_uns h_lsz h_raw h_mem h_dr
      let mem' : Miri.Memory.MemoryState Miri.Memory.Provenance
          Miri.TreeBorrows.BorrowTree Unit :=
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      let st1 := { st with machine := { st.machine with memory := mem' } }
      let ⟨msg, h_vis⟩ := visit_mem_scalar_enum_uninit_ub rp.types c 7 6 rfl
        ety tagW tagS info mem1 after st1 h_tr h_res rfl h_asz h_rd
      exact ⟨msg, st1, copyRuntimePlace_imm_to_mem_step rp c (.enum ety) .uninit
        retMemPlace st st1 _ h_pmd h_wm
        (validatePlace_mem_ub_step rp.types c _ st1 st1 msg h_vis)⟩
  | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases h_supp

end Anneal.MirCorrespondence
