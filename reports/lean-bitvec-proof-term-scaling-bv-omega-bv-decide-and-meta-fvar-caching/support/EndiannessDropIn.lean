-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Data.BitVec.Lemmas

namespace Endianness

/-- A finite conjunction supplies one checked proposition for each index. -/
def CheckRange (n : Nat) (p : Nat → Prop) : Prop :=
  Nat.rec (motive := fun _ => (Nat → Prop) → Prop)
    (fun _ => True)
    (fun _ ih q => q 0 ∧ ih (fun i => q (i + 1)))
    n p

theorem checkRange_sound (n : Nat) (p : Nat → Prop)
    (checked : CheckRange n p) : ∀ i, i < n → p i := by
  induction n generalizing p with
  | zero =>
    intro i hi
    exact False.elim (Nat.not_lt_zero i hi)
  | succ n ih =>
    intro i hi
    cases i with
    | zero => exact checked.1
    | succ i => exact ih _ checked.2 i (Nat.lt_of_succ_lt_succ hi)

/-- The bit within each byte stays fixed while the byte order reverses. -/
def reverseByteIndex (bits i : Nat) : Nat :=
  8 * (bits / 8 - 1 - i / 8) + i % 8

/-- Reversal discards bits above the selected width. -/
def ByteReversal (bits : Nat) (input output : BitVec 64) : Prop :=
  ∀ i, i < 64 → output.getLsbD i =
    if i < bits then input.getLsbD (reverseByteIndex bits i) else false

-- These formulas preserve the masks and shifts in the production Rust function.
-- Their correspondence to captured MIR is a separate proof obligation.
def swap8 (x : BitVec 64) : BitVec 64 := x &&& 0xff

def swap16 (x : BitVec 64) : BitVec 64 :=
  let v := x &&& 0xffff
  ((v &&& 0x00ff) <<< (8 : Nat)) ||| ((v &&& 0xff00) >>> (8 : Nat))

def swap32 (x : BitVec 64) : BitVec 64 :=
  let v := x &&& 0xffff_ffff
  ((v &&& 0x0000_00ff) <<< (24 : Nat)) |||
  ((v &&& 0x0000_ff00) <<< (8 : Nat)) |||
  ((v &&& 0x00ff_0000) >>> (8 : Nat)) |||
  ((v &&& 0xff00_0000) >>> (24 : Nat))

def swap64 (x : BitVec 64) : BitVec 64 :=
  ((x &&& 0x0000_0000_0000_00ff) <<< (56 : Nat)) |||
  ((x &&& 0x0000_0000_0000_ff00) <<< (40 : Nat)) |||
  ((x &&& 0x0000_0000_00ff_0000) <<< (24 : Nat)) |||
  ((x &&& 0x0000_0000_ff00_0000) <<< (8 : Nat)) |||
  ((x &&& 0x0000_00ff_0000_0000) >>> (8 : Nat)) |||
  ((x &&& 0x0000_ff00_0000_0000) >>> (24 : Nat)) |||
  ((x &&& 0x00ff_0000_0000_0000) >>> (40 : Nat)) |||
  ((x &&& 0xff00_0000_0000_0000) >>> (56 : Nat))

/-! ### Parameter-Free Closed `Bool` Reflection Engine -/

noncomputable def evalLanes (f : Nat → Bool) (lanes : List (Bool × Nat)) : Bool :=
  List.rec false (fun hd _ ih => (hd.1 && f hd.2) || ih) lanes

noncomputable def allInactive (lanes : List (Bool × Nat)) : Bool :=
  List.rec true (fun hd _ ih => !hd.1 && ih) lanes

noncomputable def checkLanes (lanes : List (Bool × Nat)) (target : Bool × Nat) : Bool :=
  List.rec (!target.1)
    (fun hd tl ih => bif hd.1 then target.1 && Nat.beq hd.2 target.2 && allInactive tl else ih)
    lanes

theorem evalLanes_of_allInactive (f : Nat → Bool) (lanes : List (Bool × Nat)) :
    allInactive lanes = true → evalLanes f lanes = false := by
  induction lanes with
  | nil => intro _; rfl
  | cons hd tl ih =>
    rcases hd with ⟨c, idx⟩
    cases c with
    | true => intro h; cases h
    | false => intro h; exact ih h

theorem checkLanes_sound (f : Nat → Bool) (lanes : List (Bool × Nat)) (target : Bool × Nat) :
    checkLanes lanes target = true → evalLanes f lanes = (target.1 && f target.2) := by
  rcases target with ⟨tc, tidx⟩
  induction lanes with
  | nil =>
    cases tc with
    | false => intro _; rfl
    | true => intro h; cases h
  | cons hd tl ih =>
    rcases hd with ⟨c, idx⟩
    cases c with
    | false => intro h; exact ih h
    | true =>
      cases tc with
      | false => intro h; cases h
      | true =>
        intro h
        have h12 := Bool.and_eq_true_iff.mp h
        have h1 := Bool.and_eq_true_iff.mp h12.1
        have hidx : idx = tidx := Nat.eq_of_beq_eq_true h1.2
        change ((true && f idx) || evalLanes f tl) = (true && f tidx)
        rw [Bool.true_and, Bool.true_and, hidx, evalLanes_of_allInactive f tl h12.2, Bool.or_false]

noncomputable def checkNatPred (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec true (fun k ih => p k && ih) n

theorem checkNatPred_sound (n : Nat) (p : Nat → Bool) (h : checkNatPred n p = true) :
    ∀ i, i < n → p i = true := by
  induction n with
  | zero => intro i hi; exact False.elim (Nat.not_lt_zero i hi)
  | succ k ih =>
    have h12 := Bool.and_eq_true_iff.mp h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · exact ih h12.2 i hlt
    · exact h12.1

theorem decide_lt_eq_ble (a b : Nat) : decide (a < b) = Nat.ble a.succ b := by
  cases h : Nat.ble a.succ b
  · exact decide_eq_false (fun h' => by rw [Nat.ble_eq_true_of_le h'] at h; cases h)
  · exact decide_eq_true (Nat.le_of_ble_eq_true h)

theorem if_lt_eq_ble_and (i bits : Nat) (b : Bool) :
    (if i < bits then b else false) = (Nat.ble i.succ bits && b) := by
  rw [← decide_lt_eq_ble]
  change @ite Bool (i < bits) (Nat.decLt i bits) b false =
    (@Decidable.decide (i < bits) (Nat.decLt i bits) && b)
  cases Nat.decLt i bits with
  | isFalse _ => rfl
  | isTrue _ => exact (Bool.true_and b).symm

theorem checkByteReversal_sound (bits : Nat) (f : Nat → Bool)
    (lanesOf : Nat → List (Bool × Nat))
    (h : checkNatPred 64
      (fun i => checkLanes (lanesOf i) (Nat.ble i.succ bits, reverseByteIndex bits i)) = true) :
    ∀ i, i < 64 → evalLanes f (lanesOf i) =
      (if i < bits then f (reverseByteIndex bits i) else false) := by
  intro i hi
  rw [if_lt_eq_ble_and]
  exact checkLanes_sound f (lanesOf i) _ (checkNatPred_sound 64 _ h i hi)

noncomputable def testBitFast (m idx : Nat) : Bool :=
  !Nat.beq (Nat.land 1 (Nat.shiftRight m idx)) 0

theorem decide_eq_eq_beq (a b : Nat) : decide (a = b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · exact decide_eq_false (Nat.ne_of_beq_eq_false h)
  · exact decide_eq_true (Nat.eq_of_beq_eq_true h)

theorem getLsbD_eq_testBitFast (m : BitVec 64) (idx : Nat) :
    m.getLsbD idx = testBitFast m.toNat idx :=
  congrArg Bool.not (decide_eq_eq_beq (1 &&& (m.toNat >>> idx)) 0)

noncomputable def laneMask (m : BitVec 64) (i : Nat) : Bool × Nat :=
  (testBitFast m.toNat i, i)

noncomputable def laneL (m : BitVec 64) (s i : Nat) : Bool × Nat :=
  (Nat.ble i.succ 64 && !Nat.ble i.succ s && testBitFast m.toNat (Nat.sub i s), Nat.sub i s)

noncomputable def laneR (m : BitVec 64) (s i : Nat) : Bool × Nat :=
  (testBitFast m.toNat (Nat.add s i), Nat.add s i)

theorem getLsbD_laneMask_singleton (x m : BitVec 64) (i : Nat) :
    (x &&& m).getLsbD i = evalLanes x.getLsbD [laneMask m i] := by
  change (x &&& m).getLsbD i = ((testBitFast m.toNat i && x.getLsbD i) || false)
  rw [BitVec.getLsbD_and, getLsbD_eq_testBitFast m, Bool.or_false, Bool.and_comm]

theorem getLsbD_laneL_singleton (x m : BitVec 64) (s i : Nat) :
    ((x &&& m) <<< s).getLsbD i = evalLanes x.getLsbD [laneL m s i] := by
  change ((x &&& m) <<< s).getLsbD i =
    (((Nat.ble i.succ 64 && !Nat.ble i.succ s && testBitFast m.toNat (i - s)) &&
      x.getLsbD (i - s)) || false)
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, decide_lt_eq_ble, decide_lt_eq_ble,
    getLsbD_eq_testBitFast m, Bool.or_false, Bool.and_comm (x.getLsbD (i - s)), ← Bool.and_assoc]

theorem evalLanes_snoc_laneL (x m : BitVec 64) (s i : Nat) (lanes : List (Bool × Nat)) :
    (evalLanes x.getLsbD lanes || ((x &&& m) <<< s).getLsbD i) =
      evalLanes x.getLsbD (laneL m s i :: lanes) := by
  change (evalLanes x.getLsbD lanes || ((x &&& m) <<< s).getLsbD i) =
    (((Nat.ble i.succ 64 && !Nat.ble i.succ s && testBitFast m.toNat (i - s)) &&
      x.getLsbD (i - s)) || evalLanes x.getLsbD lanes)
  rw [Bool.or_comm, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, decide_lt_eq_ble,
    decide_lt_eq_ble, getLsbD_eq_testBitFast m, Bool.and_comm (x.getLsbD (i - s)), ← Bool.and_assoc]

theorem evalLanes_snoc_laneR (x m : BitVec 64) (s i : Nat) (lanes : List (Bool × Nat)) :
    (evalLanes x.getLsbD lanes || ((x &&& m) >>> s).getLsbD i) =
      evalLanes x.getLsbD (laneR m s i :: lanes) := by
  change (evalLanes x.getLsbD lanes || ((x &&& m) >>> s).getLsbD i) =
    ((testBitFast m.toNat (s + i) && x.getLsbD (s + i)) || evalLanes x.getLsbD lanes)
  rw [Bool.or_comm, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and,
    getLsbD_eq_testBitFast m, Bool.and_comm (x.getLsbD (s + i))]

theorem swap8_exact (x : BitVec 64) : ByteReversal 8 x (swap8 x) := by
  intro i hi
  rw [swap8, getLsbD_laneMask_singleton]
  revert i hi
  apply checkByteReversal_sound 8 x.getLsbD
  rfl

theorem swap16_exact (x : BitVec 64) : ByteReversal 16 x (swap16 x) := by
  intro i hi
  rw [swap16, BitVec.and_assoc, BitVec.and_assoc, BitVec.getLsbD_or,
    getLsbD_laneL_singleton, evalLanes_snoc_laneR]
  revert i hi
  apply checkByteReversal_sound 16 x.getLsbD
  rfl

theorem swap32_exact (x : BitVec 64) : ByteReversal 32 x (swap32 x) := by
  intro i hi
  rw [swap32, BitVec.and_assoc, BitVec.and_assoc, BitVec.and_assoc, BitVec.and_assoc,
    BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_or,
    getLsbD_laneL_singleton, evalLanes_snoc_laneL, evalLanes_snoc_laneR, evalLanes_snoc_laneR]
  revert i hi
  apply checkByteReversal_sound 32 x.getLsbD
  rfl

theorem swap64_exact (x : BitVec 64) : ByteReversal 64 x (swap64 x) := by
  intro i hi
  rw [swap64, BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_or,
    BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_or,
    getLsbD_laneL_singleton, evalLanes_snoc_laneL, evalLanes_snoc_laneL, evalLanes_snoc_laneL,
    evalLanes_snoc_laneR, evalLanes_snoc_laneR, evalLanes_snoc_laneR, evalLanes_snoc_laneR]
  revert i hi
  apply checkByteReversal_sound 64 x.getLsbD
  rfl

theorem bits_of_exact {bits : Nat} {x y : BitVec 64}
    (hexact : ByteReversal bits x y) (hbits : Nat.ble bits 64 = true) (i : Nat) :
    y.getLsbD i =
      if i < bits then x.getLsbD (reverseByteIndex bits i) else false :=
  if hi : i < 64 then hexact i hi else by
    have hb : ¬ i < bits := fun h => hi (Nat.lt_of_lt_of_le h (Nat.le_of_ble_eq_true hbits))
    rw [if_lt_eq_ble_and, ← decide_lt_eq_ble, decide_eq_false hb, Bool.false_and]
    exact BitVec.getLsbD_of_ge y i (Nat.le_of_not_gt hi)

theorem swap8_bits (x : BitVec 64) (i : Nat) :
    (swap8 x).getLsbD i =
      if i < 8 then x.getLsbD (reverseByteIndex 8 i) else false :=
  bits_of_exact (swap8_exact x) rfl i

theorem swap16_bits (x : BitVec 64) (i : Nat) :
    (swap16 x).getLsbD i =
      if i < 16 then x.getLsbD (reverseByteIndex 16 i) else false :=
  bits_of_exact (swap16_exact x) rfl i

theorem swap32_bits (x : BitVec 64) (i : Nat) :
    (swap32 x).getLsbD i =
      if i < 32 then x.getLsbD (reverseByteIndex 32 i) else false :=
  bits_of_exact (swap32_exact x) rfl i

theorem swap64_bits (x : BitVec 64) (i : Nat) :
    (swap64 x).getLsbD i =
      if i < 64 then x.getLsbD (reverseByteIndex 64 i) else false :=
  bits_of_exact (swap64_exact x) rfl i

theorem nested_if_lt_eq_evalLanes (f : Nat → Bool) (bits i : Nat) :
    (if i < bits then
      (if reverseByteIndex bits i < bits then
        f (reverseByteIndex bits (reverseByteIndex bits i))
      else false)
    else false) =
      evalLanes f
        [(Nat.ble i.succ bits && Nat.ble (reverseByteIndex bits i).succ bits,
          reverseByteIndex bits (reverseByteIndex bits i))] := by
  change _ = (((Nat.ble i.succ bits && Nat.ble (reverseByteIndex bits i).succ bits) &&
    f (reverseByteIndex bits (reverseByteIndex bits i))) || false)
  rw [if_lt_eq_ble_and, if_lt_eq_ble_and, Bool.or_false, Bool.and_assoc]

theorem involutive_step (bits : Nat) (x y z : BitVec 64) (m : BitVec 64)
    (hy : ∀ k, y.getLsbD k = if k < bits then x.getLsbD (reverseByteIndex bits k) else false)
    (hz : ByteReversal bits y z)
    (hpred : checkNatPred 64 (fun j =>
      checkLanes
        [(Nat.ble j.succ bits && Nat.ble (reverseByteIndex bits j).succ bits,
          reverseByteIndex bits (reverseByteIndex bits j))]
        (testBitFast m.toNat j, j)) = true) :
    z = x &&& m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [hz i hi, hy (reverseByteIndex bits i), nested_if_lt_eq_evalLanes x.getLsbD,
    BitVec.getLsbD_and, getLsbD_eq_testBitFast m, Bool.and_comm (x.getLsbD i)]
  exact checkLanes_sound x.getLsbD _ _ (checkNatPred_sound 64 _ hpred i hi)

theorem swap8_involutive (x : BitVec 64) :
    swap8 (swap8 x) = x &&& 0xff :=
  involutive_step 8 x (swap8 x) (swap8 (swap8 x)) 0xff
    (swap8_bits x) (swap8_exact (swap8 x)) rfl

theorem swap16_involutive (x : BitVec 64) :
    swap16 (swap16 x) = x &&& 0xffff :=
  involutive_step 16 x (swap16 x) (swap16 (swap16 x)) 0xffff
    (swap16_bits x) (swap16_exact (swap16 x)) rfl

theorem swap32_involutive (x : BitVec 64) :
    swap32 (swap32 x) = x &&& 0xffff_ffff :=
  involutive_step 32 x (swap32 x) (swap32 (swap32 x)) 0xffff_ffff
    (swap32_bits x) (swap32_exact (swap32 x)) rfl

theorem swap64_involutive (x : BitVec 64) :
    swap64 (swap64 x) = x := by
  have h := involutive_step 64 x (swap64 x) (swap64 (swap64 x)) (BitVec.allOnes 64)
    (swap64_bits x) (swap64_exact (swap64 x)) rfl
  rw [h, BitVec.and_allOnes]

theorem maskedIdentity16_rejected :
    ¬ ByteReversal 16 (1#64) ((1#64) &&& 0xffff) := by
  intro h
  have bit := h 0 (by decide)
  revert bit
  decide

theorem constantZero16_rejected :
    ¬ ByteReversal 16 (1#64) (0#64) := by
  intro h
  have bit := h 8 (by decide)
  revert bit
  decide

end Endianness
