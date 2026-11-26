-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Init.Data.Int.Basic

public section

/-!
# MSB-First Bit-Cursor, Exp-Golomb (`ue`/`se`), & Dual-Context Lenses

Formalizes the bit-level codec layer and dual-context stateful transcoding
optics above `Anneal.MediaBits.Rbsp`:

1. **MSB-First Fixed-Width `readBits` / `writeBits` & Byte-Bit Packing (`0`
   `._unsafe_rec`, `0` `noncomputable`):**
   - `pow2Nat n`: `@Nat.rec` power-of-two helper (`pow2Nat_pos`).
   - `readBits n bs` / `writeBits n v`: division-free MSB-first `n`-bit
     reader/writer satisfying `writeBits_len`, `readBits_writeBits` (`PutGet`
     preserving arbitrary trailing bits `rest`), `readBits_bounds`, and
     `writeBits_of_readBits` (non-malleable `GetPut`).
   - `bytesToBits` / `bitsToBytesN`: 8-bit byte-stream packing satisfying
     `bytesToBits_len`, `bitsToBytesN_bytesToBits`, and
     `bytesToBits_of_bitsToBytesN`.
2. **ITU-T H.264 §9.1 Unsigned & Signed Exp-Golomb (`ue(v)` / `se(v)`):**
   - `ueSplit v` (division-free `@Nat.rec` computing `(leadingZeros, suffix)`
     with `ueSplit_spec` and `ueSplit_unique`), `encodeUe`, paramorphic
     `List.foldr` `countLeadingFalse`, and `decodeUe`, proving exact
     non-malleable bijection (`decodeUe_encodeUe`, `encodeUe_of_decodeUe`).
   - H.264 Table 9-3 `zigzagEncode` / `zigzagDecode` (`zigzagDecode_encode`,
     `zigzagEncode_decode`) lifting into `encodeSe` / `decodeSe`
     (`decodeSe_encodeSe`, `encodeSe_of_decodeSe`).
3. **Dual-Context Parameterized Transcoding Lenses (`IndexedCodec`,
   `DualContextTranscoder`):**
   - Separates persistent input context `SIn` from persistent output context
     `SOut` so header rewrites (`SIn ↦ SOut`) do not corrupt parsing of
     subsequent upstream packets.
   - `IndexedPutGet`, `IndexedGetPut`, `transcodeOne`, CPS `List.foldr`
     `transcodeStream`, `DownstreamParses`, and
     `dualContext_transcodeStream_sound` proving invariant preservation and
     downstream parseability across arbitrary packet streams.

All definitions use `@Nat.rec` or `List.foldr` (`0` `._unsafe_rec`, `0`
`noncomputable`, `0` `omega`, `0` `decide`) and every declaration compiles
using at most `[propext]` (`0` `Classical.choice`, `0` `Quot.sound`).
-/

namespace Anneal.MediaBits

/-! ## Part I: MSB-First Fixed-Width `readBits` / `writeBits` & Byte Packing -/

/-- Exact power of two `2^n` defined via `@Nat.rec` (`0` `._unsafe_rec`). -/
@[expose] def pow2Nat (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 1 (fun _ ih => ih + ih) n

private theorem pow2Nat_succ (k : Nat) :
    pow2Nat (k + 1) = pow2Nat k + pow2Nat k :=
  rfl

private theorem nil_append_mb {α : Type} (ys : List α) : [] ++ ys = ys :=
  rfl

private theorem cons_append_mb {α : Type} (x : α) (xs ys : List α) :
    (x :: xs) ++ ys = x :: (xs ++ ys) :=
  rfl

/-- Positivity of `pow2Nat n` (`[]` zero axioms). -/
theorem pow2Nat_pos : ∀ n : Nat, 0 < pow2Nat n
  | 0 => Nat.zero_lt_succ 0
  | k + 1 => by
    dsimp only [pow2Nat]
    have h := pow2Nat_pos k
    exact Nat.lt_of_lt_of_le h (Nat.le_add_right (pow2Nat k) (pow2Nat k))

/-- Monotonicity of `pow2Nat` (`[]` zero axioms). -/
theorem pow2Nat_le_pow2Nat_of_le :
    ∀ {a b : Nat}, a ≤ b → pow2Nat a ≤ pow2Nat b
  | _, _, Nat.le.refl => Nat.le_refl _
  | a, _, Nat.le.step h => by
    have ih := pow2Nat_le_pow2Nat_of_le h
    dsimp only [pow2Nat]
    exact Nat.le_trans ih (Nat.le_add_right _ _)

private theorem natBle_true_iff_le :
    ∀ a b : Nat, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => ⟨fun _ => Nat.zero_le _, fun _ => rfl⟩
  | _ + 1, 0 =>
    ⟨fun h => Bool.noConfusion h,
      fun h => False.elim (Nat.not_succ_le_zero _ h)⟩
  | a + 1, b + 1 => by
    dsimp only [Nat.ble]
    exact ⟨fun h => Nat.succ_le_succ ((natBle_true_iff_le a b).mp h),
      fun h => (natBle_true_iff_le a b).mpr (Nat.le_of_succ_le_succ h)⟩

private theorem natBle_false_iff_lt (a b : Nat) :
    Nat.ble a b = false ↔ b < a := by
  constructor
  · intro hFalse
    cases Nat.lt_or_ge b a with
    | inl hLt => exact hLt
    | inr hGe =>
      have hTrue : Nat.ble a b = true := (natBle_true_iff_le a b).mpr hGe
      rw [hFalse] at hTrue
      exact Bool.noConfusion hTrue
  · intro hLt
    cases hBle : Nat.ble a b with
    | false => rfl
    | true =>
      have hLe : a ≤ b := (natBle_true_iff_le a b).mp hBle
      exact False.elim (Nat.not_lt_of_ge hLe hLt)

/-- MSB-first `n`-bit reader over a bit stream `List Bool`, defined via
`@Nat.rec` (`0` `._unsafe_rec`). Returns `none` if fewer than `n` bits remain;
otherwise returns `some (value, remainingBits)`. -/
@[expose] def readBits (n : Nat) (bs : List Bool) :
    Option (Nat × List Bool) :=
  @Nat.rec (fun _ => List Bool → Option (Nat × List Bool))
    (fun rest => some (0, rest))
    (fun k ih rest =>
      match rest with
      | [] => none
      | b :: tail =>
        match ih tail with
        | none => none
        | some (low, rem) =>
          some ((match b with | true => pow2Nat k | false => 0) + low, rem))
    n bs

/-- Division-free MSB-first `n`-bit encoder for `v < 2^n`, defined via
`@Nat.rec` (`0` `._unsafe_rec`). -/
@[expose] def writeBits (n : Nat) (v : Nat) : List Bool :=
  @Nat.rec (fun _ => Nat → List Bool)
    (fun _ => [])
    (fun k ih x =>
      match Nat.ble (pow2Nat k) x with
      | true => true :: ih (x - pow2Nat k)
      | false => false :: ih x)
    n v

private theorem readBits_succ_cons (k : Nat) (b : Bool) (tail : List Bool) :
    readBits (k + 1) (b :: tail) =
      match readBits k tail with
      | none => none
      | some (low, rem) =>
        some ((match b with | true => pow2Nat k | false => 0) + low, rem) :=
  rfl

private theorem writeBits_succ (k v : Nat) :
    writeBits (k + 1) v =
      match Nat.ble (pow2Nat k) v with
      | true => true :: writeBits k (v - pow2Nat k)
      | false => false :: writeBits k v :=
  rfl

/-- `writeBits n v` always emits exactly `n` bits (`[]` zero axioms). -/
theorem writeBits_len : ∀ (n v : Nat), (writeBits n v).length = n
  | 0, _ => rfl
  | k + 1, v => by
    rw [writeBits_succ]
    cases Nat.ble (pow2Nat k) v with
    | true =>
      dsimp only [List.length]
      rw [writeBits_len k (v - pow2Nat k)]
    | false =>
      dsimp only [List.length]
      rw [writeBits_len k v]

/-- Value range and bit-length conservation of `readBits` (`[]` zero axioms):
if `readBits n bs = some (v, rem)`, then `v < 2^n` and
`bs.length = n + rem.length`. -/
theorem readBits_bounds :
    ∀ (n : Nat) (bs : List Bool) (v : Nat) (rem : List Bool),
      readBits n bs = some (v, rem) →
      v < pow2Nat n ∧ bs.length = n + rem.length
  | 0, bs, v, rem, h => by
    dsimp only [readBits] at h
    injection h with hPair
    injection hPair with hv hRem
    rw [← hv, ← hRem, Nat.zero_add]
    exact ⟨pow2Nat_pos 0, rfl⟩
  | k + 1, [], _, _, h => by
    dsimp only [readBits] at h
    nomatch h
  | k + 1, b :: tail, v, rem, h => by
    rw [readBits_succ_cons] at h
    cases hRec : readBits k tail with
    | none =>
      rw [hRec] at h
      nomatch h
    | some p =>
      rw [hRec] at h
      cases p with
      | mk low rem' =>
        dsimp only at h
        injection h with hPair
        injection hPair with hv hRem
        have ih := readBits_bounds k tail low rem' hRec
        rw [← hv, ← hRem]
        refine ⟨?_, ?_⟩
        · cases b with
          | true =>
            dsimp only
            rw [pow2Nat_succ]
            exact Nat.add_lt_add_left ih.1 (pow2Nat k)
          | false =>
            dsimp only
            rw [Nat.zero_add, pow2Nat_succ]
            exact Nat.lt_of_lt_of_le ih.1 (Nat.le_add_right _ _)
        · dsimp only [List.length]
          rw [ih.2, Nat.succ_add]

/-- Fixed-width `PutGet` (`[propext]` only): reading `n` bits from
`writeBits n v ++ rest` recovers `some (v, rest)` whenever `v < 2^n`. -/
theorem readBits_writeBits :
    ∀ (n v : Nat) (rest : List Bool),
      v < pow2Nat n →
      readBits n (writeBits n v ++ rest) = some (v, rest)
  | 0, v, rest, hLt => by
    have hv0 : v = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hLt)
    rw [hv0]
    rfl
  | k + 1, v, rest, hLt => by
    rw [writeBits_succ]
    cases hBle : Nat.ble (pow2Nat k) v with
    | true =>
      have hGe : pow2Nat k ≤ v := (natBle_true_iff_le (pow2Nat k) v).mp hBle
      have hSubLt : v - pow2Nat k < pow2Nat k := by
        rw [pow2Nat_succ] at hLt
        exact Nat.sub_lt_left_of_lt_add hGe hLt
      dsimp only
      rw [cons_append_mb, readBits_succ_cons,
        readBits_writeBits k (v - pow2Nat k) rest hSubLt]
      dsimp only
      rw [Nat.add_sub_of_le hGe]
    | false =>
      have hVlt : v < pow2Nat k := (natBle_false_iff_lt (pow2Nat k) v).mp hBle
      dsimp only
      rw [cons_append_mb, readBits_succ_cons, readBits_writeBits k v rest hVlt]
      dsimp only
      rw [Nat.zero_add]

/-- Fixed-width non-malleable `GetPut` (`[propext]` only): if
`readBits n bs = some (v, rem)`, then `writeBits n v ++ rem = bs`. -/
theorem writeBits_of_readBits :
    ∀ (n : Nat) (bs : List Bool) (v : Nat) (rem : List Bool),
      readBits n bs = some (v, rem) →
      writeBits n v ++ rem = bs
  | 0, bs, v, rem, h => by
    dsimp only [readBits] at h
    injection h with hPair
    injection hPair with _ hRem
    rw [← hRem]
    rfl
  | k + 1, [], _, _, h => by
    dsimp only [readBits] at h
    nomatch h
  | k + 1, b :: tail, v, rem, h => by
    rw [readBits_succ_cons] at h
    cases hRec : readBits k tail with
    | none =>
      rw [hRec] at h
      nomatch h
    | some p =>
      rw [hRec] at h
      cases p with
      | mk low rem' =>
        dsimp only at h
        injection h with hPair
        injection hPair with hv hRem
        have hLowLt := (readBits_bounds k tail low rem' hRec).1
        have ih := writeBits_of_readBits k tail low rem' hRec
        rw [← hv, ← hRem]
        cases b with
        | true =>
          dsimp only
          rw [writeBits_succ]
          have hGe : pow2Nat k ≤ pow2Nat k + low :=
            Nat.le_add_right (pow2Nat k) low
          have hBleTrue : Nat.ble (pow2Nat k) (pow2Nat k + low) = true :=
            (natBle_true_iff_le _ _).mpr hGe
          rw [hBleTrue]
          dsimp only
          rw [cons_append_mb, Nat.add_sub_cancel_left (pow2Nat k) low, ih]
        | false =>
          dsimp only
          rw [Nat.zero_add, writeBits_succ]
          have hBleFalse : Nat.ble (pow2Nat k) low = false :=
            (natBle_false_iff_lt _ _).mpr hLowLt
          rw [hBleFalse]
          dsimp only
          rw [cons_append_mb, ih]

/-- Predicate asserting every byte value in `bs` is `< 256`. -/
@[expose] def AllBytesLt256 (bs : List Nat) : Prop :=
  List.foldr (fun b ih => b < 256 ∧ ih) True bs

/-- MSB-first byte-to-bit-stream packer (`0` `._unsafe_rec`). -/
@[expose] def bytesToBits (bs : List Nat) : List Bool :=
  List.foldr (fun b ih => writeBits 8 b ++ ih) [] bs

/-- Reads `n` consecutive MSB-first 8-bit bytes from a bit stream (`0`
`._unsafe_rec`). -/
@[expose] def bitsToBytesN (n : Nat) (bits : List Bool) :
    Option (List Nat × List Bool) :=
  @Nat.rec (fun _ => List Bool → Option (List Nat × List Bool))
    (fun rest => some ([], rest))
    (fun _ ih rest =>
      match readBits 8 rest with
      | none => none
      | some (b, tail) =>
        match ih tail with
        | none => none
        | some (bs, rem) => some (b :: bs, rem))
    n bits

private theorem bytesToBits_cons (b : Nat) (bs : List Nat) :
    bytesToBits (b :: bs) = writeBits 8 b ++ bytesToBits bs :=
  rfl

private theorem bitsToBytesN_succ (k : Nat) (bits : List Bool) :
    bitsToBytesN (k + 1) bits =
      match readBits 8 bits with
      | none => none
      | some (b, tail) =>
        match bitsToBytesN k tail with
        | none => none
        | some (bs, rem) => some (b :: bs, rem) :=
  rfl

/-- Exact bit length of `bytesToBits bs` (`[propext]` only). -/
theorem bytesToBits_len :
    ∀ bs : List Nat, (bytesToBits bs).length = 8 * bs.length
  | [] => rfl
  | b :: bs => by
    rw [bytesToBits_cons]
    dsimp only [List.length]
    rw [List.length_append, writeBits_len 8 b, bytesToBits_len bs,
      Nat.mul_succ, Nat.add_comm]

private theorem listAppend_assoc_mb {α : Type} :
    ∀ (xs ys zs : List α), (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
  | [], _, _ => rfl
  | x :: xs, ys, zs => by
    rw [cons_append_mb, cons_append_mb, cons_append_mb,
      listAppend_assoc_mb xs ys zs]

/-- Byte-stream `PutGet` (`[propext]` only): unpacking `bs.length` bytes from
`bytesToBits bs ++ rest` recovers `some (bs, rest)` whenever every byte is
`< 256`. -/
theorem bitsToBytesN_bytesToBits :
    ∀ (bs : List Nat) (rest : List Bool),
      AllBytesLt256 bs →
      bitsToBytesN bs.length (bytesToBits bs ++ rest) = some (bs, rest)
  | [], _, _ => rfl
  | b :: bs, rest, hBytes => by
    dsimp only [AllBytesLt256, List.foldr] at hBytes
    dsimp only [List.length]
    rw [bytesToBits_cons, bitsToBytesN_succ,
      listAppend_assoc_mb (writeBits 8 b) (bytesToBits bs) rest]
    have hLt : b < pow2Nat 8 := hBytes.1
    rw [readBits_writeBits 8 b (bytesToBits bs ++ rest) hLt]
    dsimp only
    rw [bitsToBytesN_bytesToBits bs rest hBytes.2]

/-- Byte-stream `GetPut` (`[propext]` only): every successful `bitsToBytesN`
decode repacks identically to the consumed bit prefix and yields `< 256`
bytes. -/
theorem bytesToBits_of_bitsToBytesN :
    ∀ (n : Nat) (bits : List Bool) (bs : List Nat) (rem : List Bool),
      bitsToBytesN n bits = some (bs, rem) →
      bytesToBits bs ++ rem = bits ∧ bs.length = n ∧ AllBytesLt256 bs
  | 0, bits, bs, rem, h => by
    dsimp only [bitsToBytesN] at h
    injection h with hPair
    injection hPair with hBs hRem
    rw [← hBs, ← hRem]
    exact ⟨rfl, rfl, True.intro⟩
  | k + 1, bits, bs, rem, h => by
    rw [bitsToBytesN_succ] at h
    cases hHead : readBits 8 bits with
    | none =>
      rw [hHead] at h
      nomatch h
    | some p1 =>
      rw [hHead] at h
      cases p1 with
      | mk b tail =>
        dsimp only at h
        cases hTail : bitsToBytesN k tail with
        | none =>
          rw [hTail] at h
          nomatch h
        | some p2 =>
          rw [hTail] at h
          cases p2 with
          | mk restBs rem' =>
            dsimp only at h
            injection h with hPair
            injection hPair with hBs hRem
            have hBnd := readBits_bounds 8 bits b tail hHead
            have hPack1 := writeBits_of_readBits 8 bits b tail hHead
            have ih := bytesToBits_of_bitsToBytesN k tail restBs rem' hTail
            rw [← hBs, ← hRem]
            refine ⟨?_, ?_, ?_⟩
            · rw [bytesToBits_cons,
                listAppend_assoc_mb (writeBits 8 b) (bytesToBits restBs) rem',
                ih.1, hPack1]
            · dsimp only [List.length]
              rw [ih.2.1]
            · exact ⟨hBnd.1, ih.2.2⟩

/-! ## Part II: ITU-T H.264 §9.1 Unsigned & Signed Exp-Golomb (`ue` / `se`) -/

/-- Repeats bit `b` exactly `n` times via `@Nat.rec` (`0` `._unsafe_rec`). -/
@[expose] def replicateBool (n : Nat) (b : Bool) : List Bool :=
  @Nat.rec (fun _ => List Bool) [] (fun _ ih => b :: ih) n

private theorem replicateBool_zero (b : Bool) : replicateBool 0 b = [] := rfl

private theorem replicateBool_succ (k : Nat) (b : Bool) :
    replicateBool (k + 1) b = b :: replicateBool k b :=
  rfl

/-- Division-free `@Nat.rec` decomposition of `v + 1 = 2^lz + suf` with
`suf < 2^lz` (`0` `._unsafe_rec`). -/
@[expose] def ueSplit (v : Nat) : Nat × Nat :=
  @Nat.rec (fun _ => Nat × Nat) (0, 0)
    (fun _ ih =>
      match Nat.ble (pow2Nat ih.1) (ih.2 + 1) with
      | true => (ih.1 + 1, 0)
      | false => (ih.1, ih.2 + 1))
    v

private theorem ueSplit_succ (k : Nat) :
    ueSplit (k + 1) =
      match Nat.ble (pow2Nat (ueSplit k).1) ((ueSplit k).2 + 1) with
      | true => ((ueSplit k).1 + 1, 0)
      | false => ((ueSplit k).1, (ueSplit k).2 + 1) :=
  rfl

/-- Specification of `ueSplit v` (`[]` zero axioms):
`pow2Nat (ueSplit v).1 + (ueSplit v).2 = v + 1` and
`(ueSplit v).2 < pow2Nat (ueSplit v).1`. -/
theorem ueSplit_spec :
    ∀ v : Nat,
      pow2Nat (ueSplit v).1 + (ueSplit v).2 = v + 1 ∧
      (ueSplit v).2 < pow2Nat (ueSplit v).1
  | 0 => ⟨rfl, Nat.zero_lt_succ 0⟩
  | k + 1 => by
    have ih := ueSplit_spec k
    rw [ueSplit_succ]
    cases hBle : Nat.ble (pow2Nat (ueSplit k).1) ((ueSplit k).2 + 1) with
    | true =>
      have hGe : pow2Nat (ueSplit k).1 ≤ (ueSplit k).2 + 1 :=
        (natBle_true_iff_le _ _).mp hBle
      have hLe : (ueSplit k).2 + 1 ≤ pow2Nat (ueSplit k).1 :=
        Nat.succ_le_of_lt ih.2
      have hEq : (ueSplit k).2 + 1 = pow2Nat (ueSplit k).1 :=
        Nat.le_antisymm hLe hGe
      refine ⟨?_, pow2Nat_pos ((ueSplit k).1 + 1)⟩
      dsimp only
      rw [pow2Nat_succ, Nat.add_zero, ← ih.1, Nat.add_assoc, hEq]
    | false =>
      have hLt : (ueSplit k).2 + 1 < pow2Nat (ueSplit k).1 :=
        (natBle_false_iff_lt _ _).mp hBle
      refine ⟨?_, hLt⟩
      rw [← Nat.add_assoc, ih.1]

/-- Uniqueness of `(lz, suf)` decomposition (`[propext]` only): any pair
satisfying `2^lz + suf = v + 1` and `suf < 2^lz` equals `ueSplit v`. -/
theorem ueSplit_unique {lz₁ suf₁ lz₂ suf₂ : Nat}
    (hSum : pow2Nat lz₁ + suf₁ = pow2Nat lz₂ + suf₂)
    (hLt₁ : suf₁ < pow2Nat lz₁) (hLt₂ : suf₂ < pow2Nat lz₂) :
    lz₁ = lz₂ ∧ suf₁ = suf₂ := by
  have hEqLz : lz₁ = lz₂ := by
    cases Nat.lt_or_ge lz₁ lz₂ with
    | inl h12 =>
      have hPowLe : pow2Nat (lz₁ + 1) ≤ pow2Nat lz₂ :=
        pow2Nat_le_pow2Nat_of_le (Nat.succ_le_of_lt h12)
      have hStrict : pow2Nat lz₁ + suf₁ < pow2Nat lz₂ + suf₂ := by
        have h1 : pow2Nat lz₁ + suf₁ < pow2Nat lz₁ + pow2Nat lz₁ :=
          Nat.add_lt_add_left hLt₁ (pow2Nat lz₁)
        have h2 : pow2Nat lz₁ + pow2Nat lz₁ ≤ pow2Nat lz₂ := hPowLe
        have h3 : pow2Nat lz₂ ≤ pow2Nat lz₂ + suf₂ := Nat.le_add_right _ _
        exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 h3)
      rw [hSum] at hStrict
      exact False.elim (Nat.lt_irrefl _ hStrict)
    | inr h21 =>
      cases Nat.lt_or_ge lz₂ lz₁ with
      | inl h21Lt =>
        have hPowLe : pow2Nat (lz₂ + 1) ≤ pow2Nat lz₁ :=
          pow2Nat_le_pow2Nat_of_le (Nat.succ_le_of_lt h21Lt)
        have hStrict : pow2Nat lz₂ + suf₂ < pow2Nat lz₁ + suf₁ := by
          have h1 : pow2Nat lz₂ + suf₂ < pow2Nat lz₂ + pow2Nat lz₂ :=
            Nat.add_lt_add_left hLt₂ (pow2Nat lz₂)
          have h2 : pow2Nat lz₂ + pow2Nat lz₂ ≤ pow2Nat lz₁ := hPowLe
          have h3 : pow2Nat lz₁ ≤ pow2Nat lz₁ + suf₁ := Nat.le_add_right _ _
          exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 h3)
        rw [← hSum] at hStrict
        exact False.elim (Nat.lt_irrefl _ hStrict)
      | inr h12Ge =>
        exact Nat.le_antisymm h12Ge h21
  rw [hEqLz] at hSum
  exact ⟨hEqLz, Nat.add_left_cancel hSum⟩

/-- ITU-T H.264 §9.1 unsigned Exp-Golomb encoder `ue(v)` (`0`
`._unsafe_rec`). -/
@[expose] def encodeUe (v : Nat) : List Bool :=
  let p := ueSplit v
  replicateBool p.1 false ++ (true :: writeBits p.1 p.2)

/-- Paramorphic `List.foldr` helper for `countLeadingFalse` carrying
`((leadingCount, remainingSuffix), originalList)` (`0` `._unsafe_rec`). -/
@[expose] def countLeadingFalseAux (bs : List Bool) :
    (Nat × List Bool) × List Bool :=
  List.foldr
    (fun b ih =>
      match b with
      | false => ((ih.1.1 + 1, ih.1.2), false :: ih.2)
      | true => ((0, true :: ih.2), true :: ih.2))
    ((0, []), []) bs

private theorem countLeadingFalseAux_cons_false (tail : List Bool) :
    countLeadingFalseAux (false :: tail) =
      (((countLeadingFalseAux tail).1.1 + 1, (countLeadingFalseAux tail).1.2),
        false :: (countLeadingFalseAux tail).2) :=
  rfl

private theorem countLeadingFalseAux_cons_true (tail : List Bool) :
    countLeadingFalseAux (true :: tail) =
      ((0, true :: (countLeadingFalseAux tail).2),
        true :: (countLeadingFalseAux tail).2) :=
  rfl

private theorem countLeadingFalseAux_snd :
    ∀ bs : List Bool, (countLeadingFalseAux bs).2 = bs
  | [] => rfl
  | false :: tail => by
    rw [countLeadingFalseAux_cons_false, countLeadingFalseAux_snd tail]
  | true :: tail => by
    rw [countLeadingFalseAux_cons_true, countLeadingFalseAux_snd tail]

/-- Counts leading `false` bits and returns `(count, remainingSuffix)` via
paramorphic `List.foldr` (`0` `._unsafe_rec`). -/
@[expose] def countLeadingFalse (bs : List Bool) : Nat × List Bool :=
  (countLeadingFalseAux bs).1

private theorem countLeadingFalse_replicate_true :
    ∀ (lz : Nat) (rest : List Bool),
      countLeadingFalse (replicateBool lz false ++ (true :: rest)) =
        (lz, true :: rest)
  | 0, rest => by
    rw [replicateBool_zero, nil_append_mb]
    dsimp only [countLeadingFalse]
    rw [countLeadingFalseAux_cons_true, countLeadingFalseAux_snd rest]
  | k + 1, rest => by
    rw [replicateBool_succ, cons_append_mb]
    dsimp only [countLeadingFalse]
    rw [countLeadingFalseAux_cons_false]
    have ih := countLeadingFalse_replicate_true k rest
    dsimp only [countLeadingFalse] at ih
    rw [ih]

private theorem countLeadingFalse_reconstruct :
    ∀ (bs : List Bool),
      bs =
        replicateBool (countLeadingFalse bs).1 false ++
          (countLeadingFalse bs).2
  | [] => rfl
  | false :: tail => by
    dsimp only [countLeadingFalse]
    rw [countLeadingFalseAux_cons_false]
    have ih := countLeadingFalse_reconstruct tail
    dsimp only [countLeadingFalse] at ih
    dsimp only
    rw [replicateBool_succ, cons_append_mb, ← ih]
  | true :: tail => by
    dsimp only [countLeadingFalse]
    rw [countLeadingFalseAux_cons_true, countLeadingFalseAux_snd tail]
    rfl

/-- ITU-T H.264 §9.1 unsigned Exp-Golomb decoder `ue(v)` (`0`
`._unsafe_rec`). -/
@[expose] def decodeUe (bs : List Bool) : Option (Nat × List Bool) :=
  let p := countLeadingFalse bs
  match p.2 with
  | true :: afterSep =>
    match readBits p.1 afterSep with
    | none => none
    | some (suf, rem) => some (pow2Nat p.1 + suf - 1, rem)
  | _ => none

/-- Unsigned Exp-Golomb `PutGet` (`[propext]` only): `decodeUe (encodeUe v ++
rest) = some (v, rest)` for all `v : Nat` and trailing bits `rest`. -/
theorem decodeUe_encodeUe (v : Nat) (rest : List Bool) :
    decodeUe (encodeUe v ++ rest) = some (v, rest) := by
  have hSpec := ueSplit_spec v
  dsimp only [encodeUe, decodeUe]
  rw [listAppend_assoc_mb (replicateBool (ueSplit v).1 false)
    (true :: writeBits (ueSplit v).1 (ueSplit v).2) rest, cons_append_mb,
    countLeadingFalse_replicate_true (ueSplit v).1
      (writeBits (ueSplit v).1 (ueSplit v).2 ++ rest)]
  dsimp only
  rw [readBits_writeBits (ueSplit v).1 (ueSplit v).2 rest hSpec.2]
  dsimp only
  rw [hSpec.1, Nat.add_sub_cancel]

/-- Unsigned Exp-Golomb non-malleable `GetPut` (`[propext]` only): every
accepted Exp-Golomb bit prefix is the unique canonical `encodeUe v`. -/
theorem encodeUe_of_decodeUe {bs rest : List Bool} {v : Nat}
    (h : decodeUe bs = some (v, rest)) :
    encodeUe v ++ rest = bs := by
  have hRecon := countLeadingFalse_reconstruct bs
  dsimp only [decodeUe] at h
  cases hRem : (countLeadingFalse bs).2 with
  | nil =>
    rw [hRem] at h
    nomatch h
  | cons b afterSep =>
    rw [hRem] at h
    cases b with
    | false =>
      dsimp only at h
      nomatch h
    | true =>
      dsimp only at h
      cases hRead : readBits (countLeadingFalse bs).1 afterSep with
      | none =>
        rw [hRead] at h
        nomatch h
      | some p =>
        rw [hRead] at h
        cases p with
        | mk suf rem =>
          dsimp only at h
          injection h with hPair
          injection hPair with hv hRest
          have hBnd :=
            readBits_bounds (countLeadingFalse bs).1 afterSep suf rem hRead
          have hPack :=
            writeBits_of_readBits (countLeadingFalse bs).1 afterSep suf rem
              hRead
          have hPos : 1 ≤ pow2Nat (countLeadingFalse bs).1 + suf :=
            Nat.le_trans (pow2Nat_pos (countLeadingFalse bs).1)
              (Nat.le_add_right _ _)
          have hSum1 : pow2Nat (countLeadingFalse bs).1 + suf = v + 1 := by
            rw [← hv, Nat.sub_add_cancel hPos]
          have hSpec := ueSplit_spec v
          have hUniq :=
            ueSplit_unique (hSum := Eq.trans hSpec.1 hSum1.symm)
              hSpec.2 hBnd.1
          dsimp only [encodeUe]
          rw [hUniq.1, hUniq.2, ← hRest,
            listAppend_assoc_mb (replicateBool (countLeadingFalse bs).1 false)
              (true :: writeBits (countLeadingFalse bs).1 suf) rem,
            cons_append_mb, hPack, ← hRem, ← hRecon]

/-- H.264 Table 9-3 signed-to-unsigned Exp-Golomb zigzag bijection
(`0 ↦ 0, +1 ↦ 1, -1 ↦ 2, +2 ↦ 3, -2 ↦ 4, ...`). -/
@[expose] def zigzagEncode : Int → Nat
  | Int.ofNat 0 => 0
  | Int.ofNat (k + 1) => 2 * k + 1
  | Int.negSucc k => 2 * k + 2

/-- Single-step zigzag successor on `Int` (`0 ↦ +1 ↦ -1 ↦ +2 ↦ -2 ↦ ...`). -/
@[expose] def zigzagStep : Int → Int
  | Int.ofNat 0 => Int.ofNat 1
  | Int.ofNat (k + 1) => Int.negSucc k
  | Int.negSucc k => Int.ofNat (k + 2)

/-- Division-free inverse of `zigzagEncode` via `@Nat.rec` (`0`
`._unsafe_rec`). -/
@[expose] def zigzagDecode (n : Nat) : Int :=
  @Nat.rec (fun _ => Int) (Int.ofNat 0) (fun _ ih => zigzagStep ih) n

private theorem zigzagDecode_succ (k : Nat) :
    zigzagDecode (k + 1) = zigzagStep (zigzagDecode k) :=
  rfl

private theorem zigzagEncode_step :
    ∀ z : Int, zigzagEncode (zigzagStep z) = zigzagEncode z + 1
  | Int.ofNat 0 => rfl
  | Int.ofNat (_ + 1) => rfl
  | Int.negSucc k => by
    dsimp only [zigzagStep, zigzagEncode]
    rw [Nat.mul_succ]

/-- `zigzagEncode (zigzagDecode n) = n` (`[]` zero axioms). -/
theorem zigzagEncode_decode : ∀ n : Nat, zigzagEncode (zigzagDecode n) = n
  | 0 => rfl
  | k + 1 => by
    rw [zigzagDecode_succ, zigzagEncode_step, zigzagEncode_decode k]

private theorem zigzagDecode_ofNat_succ :
    ∀ k : Nat, zigzagDecode (2 * k + 1) = Int.ofNat (k + 1)
  | 0 => rfl
  | k + 1 => by
    rw [Nat.mul_succ, zigzagDecode_succ, zigzagDecode_succ,
      zigzagDecode_ofNat_succ k]
    rfl

private theorem zigzagDecode_negSucc (k : Nat) :
    zigzagDecode (2 * k + 2) = Int.negSucc k := by
  rw [zigzagDecode_succ, zigzagDecode_ofNat_succ k]
  rfl

/-- `zigzagDecode (zigzagEncode z) = z` (`[]` zero axioms). -/
theorem zigzagDecode_encode : ∀ z : Int, zigzagDecode (zigzagEncode z) = z
  | Int.ofNat 0 => rfl
  | Int.ofNat (k + 1) => zigzagDecode_ofNat_succ k
  | Int.negSucc k => zigzagDecode_negSucc k

/-- Signed Exp-Golomb encoder `se(z)` (`0` `._unsafe_rec`). -/
@[expose] def encodeSe (z : Int) : List Bool :=
  encodeUe (zigzagEncode z)

/-- Signed Exp-Golomb decoder `se(z)` (`0` `._unsafe_rec`). -/
@[expose] def decodeSe (bs : List Bool) : Option (Int × List Bool) :=
  match decodeUe bs with
  | none => none
  | some (k, rem) => some (zigzagDecode k, rem)

/-- Signed Exp-Golomb `PutGet` (`[propext]` only). -/
theorem decodeSe_encodeSe (z : Int) (rest : List Bool) :
    decodeSe (encodeSe z ++ rest) = some (z, rest) := by
  dsimp only [encodeSe, decodeSe]
  rw [decodeUe_encodeUe (zigzagEncode z) rest]
  dsimp only
  rw [zigzagDecode_encode z]

/-- Signed Exp-Golomb non-malleable `GetPut` (`[propext]` only). -/
theorem encodeSe_of_decodeSe {bs rest : List Bool} {z : Int}
    (h : decodeSe bs = some (z, rest)) :
    encodeSe z ++ rest = bs := by
  dsimp only [decodeSe] at h
  cases hUe : decodeUe bs with
  | none =>
    rw [hUe] at h
    nomatch h
  | some p =>
    rw [hUe] at h
    cases p with
    | mk k rem =>
      dsimp only at h
      injection h with hPair
      injection hPair with hz hRest
      dsimp only [encodeSe]
      rw [← hz, zigzagEncode_decode k, ← hRest]
      exact encodeUe_of_decodeUe hUe

/-! ## Part III: Dual-Context Parameterized Transcoding Lenses -/

/-- State-indexed bitstream codec `(get, put)` threading persistent grammar
context `S` across syntax units `A` and wire representations `B`. -/
structure IndexedCodec (S A B : Type) where
  get : S → B → Option (S × A)
  put : S → A → Option (S × B)

/-- Indexed `PutGet` law: serializing `a` from state `s` to `(s', b)` implies
parsing `b` from `s` recovers `(s', a)`. -/
@[expose] def IndexedPutGet {S A B : Type} (c : IndexedCodec S A B) : Prop :=
  ∀ (s : S) (a : A) (s' : S) (b : B),
    c.put s a = some (s', b) → c.get s b = some (s', a)

/-- Strict indexed `GetPut` law: parsing `b` from state `s` to `(s', a)`
implies serializing `a` from `s` reproduces `(s', b)`. -/
@[expose] def IndexedGetPut {S A B : Type} (c : IndexedCodec S A B) : Prop :=
  ∀ (s : S) (b : B) (s' : S) (a : A),
    c.get s b = some (s', a) → c.put s a = some (s', b)

/-- Quotient indexed `GetPut` law up to wire equivalence `equivB`. -/
@[expose] def IndexedQuotientGetPut {S A B : Type} (c : IndexedCodec S A B)
    (equivB : B → B → Prop) : Prop :=
  ∀ (s : S) (b : B) (s' : S) (a : A),
    c.get s b = some (s', a) →
    ∃ b' : B, c.put s a = some (s', b') ∧ equivB b b'

/-- Dual-context bitstream filter separating upstream parser context `SIn`
from downstream serializer context `SOut` (preventing header rewrites from
corrupting subsequent upstream parses). -/
structure DualContextTranscoder (SIn SOut A B : Type) where
  inCodec : IndexedCodec SIn A B
  outCodec : IndexedCodec SOut A B
  rewrite : SIn → SOut → A → Option A

/-- Single-unit dual-context transcoding step: parses `raw` under `sIn`,
rewrites the AST against `(sIn', sOut)`, and serializes under `sOut`. -/
@[expose] def transcodeOne {SIn SOut A B : Type}
    (t : DualContextTranscoder SIn SOut A B)
    (sIn : SIn) (sOut : SOut) (raw : B) : Option (SIn × SOut × B) :=
  match t.inCodec.get sIn raw with
  | none => none
  | some (sIn', aIn) =>
    match t.rewrite sIn' sOut aIn with
    | none => none
    | some aOut =>
      match t.outCodec.put sOut aOut with
      | none => none
      | some (sOut', rawOut) => some (sIn', sOut', rawOut)

/-- Multi-unit dual-context stream transcoder via CPS `List.foldr` (`0`
`._unsafe_rec`). -/
@[expose] def transcodeStream {SIn SOut A B : Type}
    (t : DualContextTranscoder SIn SOut A B)
    (sIn : SIn) (sOut : SOut) (pkts : List B) :
    Option (SIn × SOut × List B) :=
  List.foldr
    (fun raw ih curIn curOut =>
      match transcodeOne t curIn curOut raw with
      | none => none
      | some (nextIn, nextOut, outRaw) =>
        match ih nextIn nextOut with
        | none => none
        | some (finIn, finOut, outTail) =>
          some (finIn, finOut, outRaw :: outTail))
    (fun curIn curOut => some (curIn, curOut, []))
    pkts sIn sOut

private theorem transcodeStream_cons {SIn SOut A B : Type}
    (t : DualContextTranscoder SIn SOut A B)
    (sIn : SIn) (sOut : SOut) (raw : B) (rest : List B) :
    transcodeStream t sIn sOut (raw :: rest) =
      match transcodeOne t sIn sOut raw with
      | none => none
      | some (nextIn, nextOut, outRaw) =>
        match transcodeStream t nextIn nextOut rest with
        | none => none
        | some (finIn, finOut, outTail) =>
          some (finIn, finOut, outRaw :: outTail) :=
  rfl

/-- Propositional witness that every packet in `outPkts` parses cleanly under
`codec.get` starting from `sOut`, landing in final output state `sOutFin`. -/
@[expose] def DownstreamParses {SOut A B : Type}
    (codec : IndexedCodec SOut A B)
    (sOut : SOut) (outPkts : List B) (sOutFin : SOut) : Prop :=
  List.foldr
    (fun raw ih curOut =>
      ∃ (nextOut : SOut) (a : A),
        codec.get curOut raw = some (nextOut, a) ∧ ih nextOut)
    (fun curOut => curOut = sOutFin)
    outPkts sOut

private theorem downstreamParses_cons {SOut A B : Type}
    (codec : IndexedCodec SOut A B)
    (sOut : SOut) (raw : B) (rest : List B) (sOutFin : SOut) :
    DownstreamParses codec sOut (raw :: rest) sOutFin =
      (∃ (nextOut : SOut) (a : A),
        codec.get sOut raw = some (nextOut, a) ∧
        DownstreamParses codec nextOut rest sOutFin) :=
  rfl

/-- Single-step coupling invariant for a dual-context transcoder under
simulation relation `R : SIn → SOut → Prop`. -/
@[expose] def DualContextRelStep {SIn SOut A B : Type}
    (t : DualContextTranscoder SIn SOut A B)
    (R : SIn → SOut → Prop) : Prop :=
  ∀ (sIn sIn' : SIn) (sOut sOut' : SOut) (raw outRaw : B),
    R sIn sOut →
    transcodeOne t sIn sOut raw = some (sIn', sOut', outRaw) →
    R sIn' sOut'

/-- Single-unit soundness (`[]` zero axioms): under `IndexedPutGet t.outCodec`
and `DualContextRelStep t R`, any successful `transcodeOne` from contexts
satisfying `R` lands in contexts `(sIn', sOut')` satisfying `R`, and its
emitted packet `outRaw` parses under `t.outCodec.get` from `sOut` into the
output context `sOut'` with some AST `aOut`. The statement does not relate
`aOut` to the upstream AST or to `t.rewrite`. -/
theorem dualContext_transcodeOne_sound {SIn SOut A B : Type}
    {t : DualContextTranscoder SIn SOut A B} {R : SIn → SOut → Prop}
    (hPutGet : IndexedPutGet t.outCodec)
    (hStep : DualContextRelStep t R)
    {sIn sIn' : SIn} {sOut sOut' : SOut} {raw outRaw : B}
    (hR : R sIn sOut)
    (hOne : transcodeOne t sIn sOut raw = some (sIn', sOut', outRaw)) :
    R sIn' sOut' ∧
      ∃ aOut : A, t.outCodec.get sOut outRaw = some (sOut', aOut) := by
  have hR' := hStep sIn sIn' sOut sOut' raw outRaw hR hOne
  dsimp only [transcodeOne] at hOne
  cases hGet : t.inCodec.get sIn raw with
  | none =>
    rw [hGet] at hOne
    nomatch hOne
  | some pIn =>
    rw [hGet] at hOne
    cases pIn with
    | mk sInMid aIn =>
      dsimp only at hOne
      cases hRw : t.rewrite sInMid sOut aIn with
      | none =>
        rw [hRw] at hOne
        nomatch hOne
      | some aOut =>
        rw [hRw] at hOne
        dsimp only at hOne
        cases hPut : t.outCodec.put sOut aOut with
        | none =>
          rw [hPut] at hOne
          nomatch hOne
        | some pOut =>
          rw [hPut] at hOne
          cases pOut with
          | mk sOutMid rawMid =>
            dsimp only at hOne
            injection hOne with hPair
            injection hPair with _ hTail
            injection hTail with hOutEq hRawEq
            rw [hOutEq, hRawEq] at hPut
            exact ⟨hR', aOut, hPutGet sOut aOut sOut' outRaw hPut⟩

/-- Multi-packet stream soundness (`[]` zero axioms): under
`IndexedPutGet t.outCodec` and `DualContextRelStep t R`, any successful
`transcodeStream` preserves `R` at the final contexts and guarantees every
emitted packet parses cleanly under `t.outCodec.get`. -/
theorem dualContext_transcodeStream_sound {SIn SOut A B : Type}
    {t : DualContextTranscoder SIn SOut A B} {R : SIn → SOut → Prop}
    (hPutGet : IndexedPutGet t.outCodec)
    (hStep : DualContextRelStep t R) :
    ∀ (pkts : List B) (sIn sInFin : SIn) (sOut sOutFin : SOut)
      (outPkts : List B),
      R sIn sOut →
      transcodeStream t sIn sOut pkts = some (sInFin, sOutFin, outPkts) →
      R sInFin sOutFin ∧
        DownstreamParses t.outCodec sOut outPkts sOutFin ∧
        outPkts.length = pkts.length
  | [], sIn, sInFin, sOut, sOutFin, outPkts, hR, hRun => by
    dsimp only [transcodeStream, List.foldr] at hRun
    injection hRun with hPair
    injection hPair with hInEq hTail
    injection hTail with hOutEq hListEq
    rw [← hInEq, ← hOutEq, ← hListEq]
    exact ⟨hR, rfl, rfl⟩
  | raw :: rest, sIn, sInFin, sOut, sOutFin, outPkts, hR, hRun => by
    rw [transcodeStream_cons] at hRun
    cases hOne : transcodeOne t sIn sOut raw with
    | none =>
      rw [hOne] at hRun
      nomatch hRun
    | some p1 =>
      rw [hOne] at hRun
      cases p1 with
      | mk nextIn p1r =>
        cases p1r with
        | mk nextOut outRaw =>
          dsimp only at hRun
          cases hRest : transcodeStream t nextIn nextOut rest with
          | none =>
            rw [hRest] at hRun
            nomatch hRun
          | some p2 =>
            rw [hRest] at hRun
            cases p2 with
            | mk finIn p2r =>
              cases p2r with
              | mk finOut outTail =>
                dsimp only at hRun
                injection hRun with hPair
                injection hPair with hInEq hTailEq
                injection hTailEq with hOutEq hListEq
                have hOneSound :=
                  dualContext_transcodeOne_sound hPutGet hStep hR hOne
                have ih :=
                  dualContext_transcodeStream_sound hPutGet hStep rest
                    nextIn finIn nextOut finOut outTail hOneSound.1 hRest
                rw [← hInEq, ← hOutEq, ← hListEq, downstreamParses_cons]
                refine ⟨ih.1, ?_, ?_⟩
                · cases hOneSound.2 with
                  | intro aOut haOut =>
                    exact ⟨nextOut, aOut, haOut, ih.2.1⟩
                · dsimp only [List.length]
                  rw [ih.2.2]

end Anneal.MediaBits

end
