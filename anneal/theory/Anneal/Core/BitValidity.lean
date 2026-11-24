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
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Init.Control.Except
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Layout
public import Trusted.MirSemantics.Bytes
public import Anneal.InitLemmas

public section

namespace Anneal.Core

open Trusted.MirAst Trusted.MirSemantics
open Anneal.InitLemmas

/-!
# Zerocopy Bit-Validity Predicates and Trait Theorems (`Core.BitValidity`)

Connects the Profile v1 MIR byte codec (`Trusted.MirSemantics.Bytes`:
`encodeVal`, `decodeVal`, `initBytes?`) and type layouts
(`Trusted.MirSemantics.Layout`: `layoutOfTy`, `TargetEndian`) to semantic
specifications for `zerocopy`'s core marker traits:

1. **Byte-sequence validity modes (`ValidityMode`, `AllBytesInit`,
   `NoProvBytes`, `ByteSeqValid`):** Classifies byte sequences along the
   uninitialized, `AsInitialized`, initialized, and bit-valid axes, together
   with provenance absence (`NoProvBytes`).
2. **Trait models (`IsTryFromBytes`, `IsExactTryFromBytes`, `IsFromZeros`,
   `IsFromBytes`, `IsIntoBytes`, `IsUnaligned`, `ZerocopyTrait`,
   `ValidForTrait`):** Models the trait obligations parameterized over
   `endian : TargetEndian` (`TryFromBytes` through an explicit byte validator
   modeling `is_safe`, and every trait only for types with an addressable
   layout, `addressableLayoutOfTy`), establishes their implication
   and non-implication hierarchy, and proves sound equal-size byte
   transmutation (`transmute_sound_of_into_from_bytes` and
   `transmute_sound_noProv_of_into_from_bytes`).
3. **Profile v1 type coverage (`∀ endian : TargetEndian`):** Classifies all
   admitted Day-1 types (`.int w s`, `.unit`, `.never`, `.bool`, `.char`,
   `.ordering`, overflow pairs `.tuple [.int w s, .bool]`, and admitted
   fieldless `.enum ety` descriptors), including exact `TryFromBytes`
   validators, decidable checkers `isFromZerosEnum` and `isFromBytesEnum` with
   soundness theorems, and concrete equal-size `transmute_sound` corollaries.
   `DecodeTyped` lemmas characterize the values each type decodes to.
-/

/-! ## 1. Byte-Sequence Validity Modes and `AllocByte` Helpers -/

/-- Byte-sequence validity modes for raw memory reads, casts, and conversions.
-/
inductive ValidityMode : Type where
  /-- Arbitrary byte sequence of the type's byte size (`.uninit` permitted). -/
  | uninit
  /-- Byte sequence initialized at every offset where every bit-valid byte
      sequence that agrees with it on all earlier offsets is initialized
      (`zerocopy`'s `AsInitialized`). -/
  | asInitialized
  /-- Byte sequence of the type's byte size with no `.uninit` bytes. -/
  | initialized
  /-- Byte sequence that decodes via `decodeVal` to a valid `Val`. -/
  | bitValid
  /-- Byte sequence that decodes to a valid `Val`. Profile v1 models no safety
      invariants, so `ByteSeqValid endian ty .valid` reduces definitionally to
      `.bitValid`. -/
  | valid

/-- Whether every byte in `bs` is initialized (`AllocByte.init`), defined via
`List.foldr` (`0` `._unsafe_rec` auxiliaries). -/
@[expose] def allBytesInit (bs : List AllocByte) : Bool :=
  bs.foldr
    (fun b acc => match b with | .uninit => false | .init _ _ => acc)
    true

/-- Propositional wrapper for `allBytesInit bs = true`. -/
@[expose] def AllBytesInit (bs : List AllocByte) : Prop :=
  allBytesInit bs = true

@[simp] theorem allBytesInit_nil : allBytesInit [] = true := rfl

@[simp] theorem allBytesInit_uninit (rest : List AllocByte) :
    allBytesInit (.uninit :: rest) = false := rfl

@[simp] theorem allBytesInit_init (b : UInt8) (prov : Option AllocId)
    (rest : List AllocByte) :
    allBytesInit (.init b prov :: rest) = allBytesInit rest := rfl

theorem allBytesInit_append :
    ∀ xs ys : List AllocByte,
      allBytesInit (xs ++ ys) = (allBytesInit xs && allBytesInit ys)
  | [], ys => by
    change allBytesInit ys = (true && allBytesInit ys)
    rw [Bool.true_and]
  | .uninit :: _, _ => rfl
  | .init b prov :: rest, ys => by
    change allBytesInit (rest ++ ys) = (allBytesInit rest && allBytesInit ys)
    exact allBytesInit_append rest ys

theorem AllBytesInit_append {xs ys : List AllocByte}
    (hx : AllBytesInit xs) (hy : AllBytesInit ys) :
    AllBytesInit (xs ++ ys) := by
  dsimp [AllBytesInit]
  rw [allBytesInit_append, hx, hy]
  rfl

@[simp] theorem allBytesInit_map_init_none {α : Type} (f : α → UInt8) :
    ∀ xs : List α,
      allBytesInit (xs.map (fun x => AllocByte.init (f x) none)) = true
  | [] => rfl
  | _ :: rest => allBytesInit_map_init_none f rest

@[simp] theorem allBytesInit_replicate_uninit :
    ∀ n : Nat, allBytesInit (List.replicate (n + 1) AllocByte.uninit) = false
  | _ => rfl

/-- Byte `i` inside `bs` is initialized (`.init _ _`). -/
@[expose] def ByteInitAt (bs : List AllocByte) (i : Nat) : Prop :=
  match bs[i]? with
  | some (.init _ _) => True
  | _ => False

theorem byteInitAt_of_allBytesInit :
    ∀ (i : Nat) (bs : List AllocByte),
      i < bs.length → AllBytesInit bs → ByteInitAt bs i
  | _, [], hLt, _ => False.elim (Nat.not_lt_zero _ hLt)
  | _, .uninit :: _, _, hInit => nomatch hInit
  | 0, .init _ _ :: _, _, _ => trivial
  | i + 1, .init _ _ :: rest, hLt, hInit =>
    byteInitAt_of_allBytesInit i rest (Nat.lt_of_succ_lt_succ hLt) hInit

/-- Whether every initialized byte in `bs` carries `none` provenance, defined
via `List.foldr` (`0` `._unsafe_rec` auxiliaries). -/
@[expose] def noProvBytes (bs : List AllocByte) : Bool :=
  bs.foldr
    (fun b acc =>
      match b with
      | .uninit => acc
      | .init _ none => acc
      | .init _ (some _) => false)
    true

/-- Propositional wrapper for `noProvBytes bs = true`. -/
@[expose] def NoProvBytes (bs : List AllocByte) : Prop :=
  noProvBytes bs = true

@[simp] theorem noProvBytes_nil : noProvBytes [] = true := rfl

@[simp] theorem noProvBytes_uninit (rest : List AllocByte) :
    noProvBytes (.uninit :: rest) = noProvBytes rest := rfl

@[simp] theorem noProvBytes_init_none (b : UInt8) (rest : List AllocByte) :
    noProvBytes (.init b none :: rest) = noProvBytes rest := rfl

@[simp] theorem noProvBytes_init_some (b : UInt8) (aid : AllocId)
    (rest : List AllocByte) :
    noProvBytes (.init b (some aid) :: rest) = false := rfl

theorem noProvBytes_append :
    ∀ xs ys : List AllocByte,
      noProvBytes (xs ++ ys) = (noProvBytes xs && noProvBytes ys)
  | [], ys => by
    change noProvBytes ys = (true && noProvBytes ys)
    rw [Bool.true_and]
  | .uninit :: rest, ys => by
    change noProvBytes (rest ++ ys) = (noProvBytes rest && noProvBytes ys)
    exact noProvBytes_append rest ys
  | .init b none :: rest, ys => by
    change noProvBytes (rest ++ ys) = (noProvBytes rest && noProvBytes ys)
    exact noProvBytes_append rest ys
  | .init _ (some _) :: _, _ => rfl

theorem NoProvBytes_append {xs ys : List AllocByte}
    (hx : NoProvBytes xs) (hy : NoProvBytes ys) :
    NoProvBytes (xs ++ ys) := by
  dsimp [NoProvBytes]
  rw [noProvBytes_append, hx, hy]
  rfl

@[simp] theorem noProvBytes_map_init_none {α : Type} (f : α → UInt8) :
    ∀ xs : List α,
      noProvBytes (xs.map (fun x => AllocByte.init (f x) none)) = true
  | [] => rfl
  | _ :: rest => noProvBytes_map_init_none f rest

@[simp] theorem noProvBytes_replicate_uninit :
    ∀ n : Nat, noProvBytes (List.replicate n AllocByte.uninit) = true
  | 0 => rfl
  | n + 1 => noProvBytes_replicate_uninit n

/-- Construct `n` zero-initialized bytes (`0x00` with no provenance) via
`@Nat.rec` (`0` `._unsafe_rec` auxiliaries). -/
@[expose] def zeroInitBytes (n : Nat) : List AllocByte :=
  @Nat.rec (fun _ => List AllocByte) [] (fun _ acc => .init 0 none :: acc) n

@[simp] theorem length_zeroInitBytes :
    ∀ n : Nat, (zeroInitBytes n).length = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (length_zeroInitBytes n)

@[simp] theorem allBytesInit_zeroInitBytes :
    ∀ n : Nat, allBytesInit (zeroInitBytes n) = true
  | 0 => rfl
  | n + 1 => allBytesInit_zeroInitBytes n

@[simp] theorem noProvBytes_zeroInitBytes :
    ∀ n : Nat, noProvBytes (zeroInitBytes n) = true
  | 0 => rfl
  | n + 1 => noProvBytes_zeroInitBytes n

theorem zeroInitBytes_take :
    ∀ m n : Nat, m ≤ n → (zeroInitBytes n).take m = zeroInitBytes m
  | 0, _, _ => rfl
  | _ + 1, 0, h => by nomatch h
  | m + 1, n + 1, h => by
    have hLe : m ≤ n := Nat.le_of_succ_le_succ h
    exact congrArg (List.cons (.init 0 none)) (zeroInitBytes_take m n hLe)

theorem zeroInitBytes_drop :
    ∀ m n : Nat, (zeroInitBytes n).drop m = zeroInitBytes (n - m)
  | 0, n => by
    have hSub : n - 0 = n := Nat.sub_zero n
    rw [hSub]
    rfl
  | m + 1, 0 => by
    have hSub : 0 - (m + 1) = 0 := Nat.zero_sub (m + 1)
    change ([] : List AllocByte) = zeroInitBytes (0 - (m + 1))
    rw [hSub]
    rfl
  | m + 1, n + 1 => by
    have hSub : n + 1 - (m + 1) = n - m := Nat.succ_sub_succ_eq_sub n m
    rw [hSub]
    exact zeroInitBytes_drop m n

theorem zeroInitBytes_add :
    ∀ m n : Nat, zeroInitBytes (m + n) = zeroInitBytes m ++ zeroInitBytes n
  | 0, n => by
    have hZ : 0 + n = n := Nat.zero_add n
    rw [hZ]
    rfl
  | m + 1, n => by
    have hS : (m + 1) + n = (m + n) + 1 := Nat.succ_add m n
    rw [hS]
    exact congrArg (List.cons (.init 0 none)) (zeroInitBytes_add m n)

theorem initBytes?_zeroInitBytes :
    ∀ n : Nat, initBytes? (zeroInitBytes n) = some (List.replicate n 0)
  | 0 => rfl
  | n + 1 => by
    change (match initBytes? (zeroInitBytes n) with
      | some bs => some ((0 : UInt8) :: bs)
      | none => none) = some ((0 : UInt8) :: List.replicate n 0)
    rw [initBytes?_zeroInitBytes n]

theorem initBytes?_isSome_of_allBytesInit :
    ∀ bs : List AllocByte,
      AllBytesInit bs →
      ∃ raw : List UInt8, initBytes? bs = some raw ∧ raw.length = bs.length
  | [], _ => ⟨[], rfl, rfl⟩
  | .uninit :: _, h => by nomatch h
  | .init b _ :: rest, h => by
    have ⟨raw, hRaw, hLen⟩ := initBytes?_isSome_of_allBytesInit rest h
    refine ⟨b :: raw, ?_, congrArg Nat.succ hLen⟩
    change (match initBytes? rest with
      | some bs => some (b :: bs)
      | none => none) = some (b :: raw)
    rw [hRaw]

theorem allBytesInit_of_initBytes?_eq_some :
    ∀ {bs : List AllocByte} {raw : List UInt8},
      initBytes? bs = some raw → AllBytesInit bs ∧ raw.length = bs.length
  | [], _, h => by
    injection h with hRaw
    subst hRaw
    exact ⟨rfl, rfl⟩
  | .uninit :: _, _, h => by nomatch h
  | .init b _ :: rest, raw, h => by
    change (match initBytes? rest with
      | some bs => some (b :: bs)
      | none => none) = some raw at h
    cases hRest : initBytes? rest with
    | none =>
      rw [hRest] at h
      nomatch h
    | some tl =>
      rw [hRest] at h
      injection h with hRaw
      subst hRaw
      have ⟨hInit, hLen⟩ := allBytesInit_of_initBytes?_eq_some hRest
      exact ⟨hInit, congrArg Nat.succ hLen⟩

theorem initBytes?_map_init_none {α : Type} (f : α → UInt8) :
    ∀ xs : List α,
      initBytes? (xs.map (fun x => AllocByte.init (f x) none)) =
        some (xs.map f)
  | [] => rfl
  | x :: rest => by
    change (match initBytes? (rest.map (fun y => AllocByte.init (f y) none)) with
      | some bs => some (f x :: bs)
      | none => none) = some (f x :: rest.map f)
    rw [initBytes?_map_init_none f rest]

private theorem list_length_reverseAux {α : Type} (xs acc : List α) :
    (List.reverseAux xs acc).length = xs.length + acc.length := by
  induction xs generalizing acc with
  | nil =>
    rw [List.reverseAux_nil, List.length_nil, Nat.zero_add]
  | cons _ _ ih =>
    rw [List.reverseAux_cons, ih, List.length_cons, List.length_cons,
        Nat.succ_add, Nat.add_succ]

private theorem list_length_reverse {α : Type} (xs : List α) :
    xs.reverse.length = xs.length := by
  unfold List.reverse
  rw [list_length_reverseAux, List.length_nil, Nat.add_zero]

private theorem list_reverse_append {α : Type} (xs ys : List α) :
    (xs ++ ys).reverse = ys.reverse ++ xs.reverse := by
  induction xs with
  | nil =>
    rw [List.nil_append, List.reverse_nil, List.append_nil]
  | cons a rest ih =>
    rw [List.cons_append, List.reverse_cons, List.reverse_cons, ih,
        List.append_assoc]

private theorem list_reverse_reverse {α : Type} (xs : List α) :
    xs.reverse.reverse = xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    rw [List.reverse_cons, list_reverse_append, ih]
    rfl

private theorem list_replicate_succ_append {α : Type} (x : α) :
    ∀ n : Nat, List.replicate (n + 1) x = List.replicate n x ++ [x]
  | 0 => rfl
  | n + 1 => congrArg (List.cons x) (list_replicate_succ_append x n)

private theorem list_reverse_replicate {α : Type} (x : α) :
    ∀ n : Nat, (List.replicate n x).reverse = List.replicate n x
  | 0 => rfl
  | n + 1 => by
    change (x :: List.replicate n x).reverse = List.replicate (n + 1) x
    rw [List.reverse_cons, list_reverse_replicate x n,
        ← list_replicate_succ_append x n]

private theorem nat_two_pow_eight : Nat.pow 2 8 = 256 := rfl

private theorem nat_two_pow_succ_mul_eight (n : Nat) :
    Nat.pow 2 ((n + 1) * 8) = 256 * Nat.pow 2 (n * 8) := by
  rw [Nat.succ_mul, nat_pow_add, nat_two_pow_eight, Nat.mul_comm]

private theorem bv_eq_of_toNat_eq {w : Nat} {a b : BitVec w}
    (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | ofFin fa =>
    cases b with
    | ofFin fb =>
      exact congrArg BitVec.ofFin (Fin.eq_of_val_eq h)

private theorem bv_toNat_ofNat (w n : Nat) :
    (BitVec.ofNat w n).toNat = HMod.hMod n (Nat.pow 2 w) :=
  rfl

private theorem nat_mod_mul_split_pos (v a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    HMod.hMod v (a * b) = HMod.hMod v a + a * HMod.hMod (HDiv.hDiv v a) b := by
  have hmod_lt : HMod.hMod v a < a := Nat.mod_lt v ha
  have hdiv_lt : HMod.hMod (HDiv.hDiv v a) b < b := Nat.mod_lt (HDiv.hDiv v a) hb
  have hmul_pos : 0 < a * b := Nat.mul_pos ha hb
  have hrem_lt : HMod.hMod v a + a * HMod.hMod (HDiv.hDiv v a) b < a * b := by
    have h1 : HMod.hMod v a + a * HMod.hMod (HDiv.hDiv v a) b <
        a + a * HMod.hMod (HDiv.hDiv v a) b :=
      Nat.add_lt_add_right hmod_lt (a * HMod.hMod (HDiv.hDiv v a) b)
    have h2 : a + a * HMod.hMod (HDiv.hDiv v a) b =
        a * (HMod.hMod (HDiv.hDiv v a) b + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [h2] at h1
    exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_left a hdiv_lt)
  have hv_split :
      (a * b) * HDiv.hDiv (HDiv.hDiv v a) b +
        (HMod.hMod v a + a * HMod.hMod (HDiv.hDiv v a) b) = v := by
    have hda : b * HDiv.hDiv (HDiv.hDiv v a) b +
        HMod.hMod (HDiv.hDiv v a) b = HDiv.hDiv v a :=
      Nat.div_add_mod (HDiv.hDiv v a) b
    have hdv : a * HDiv.hDiv v a + HMod.hMod v a = v :=
      Nat.div_add_mod v a
    rw [← hda, Nat.mul_add, ← Nat.mul_assoc] at hdv
    rw [Nat.add_assoc,
        Nat.add_comm (a * HMod.hMod (HDiv.hDiv v a) b) (HMod.hMod v a)] at hdv
    exact hdv
  have hmod := congrArg (fun z => HMod.hMod z (a * b)) hv_split
  rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hrem_lt] at hmod
  exact hmod.symm

private theorem nat_mod_mul_split (v a b : Nat) :
    HMod.hMod v (a * b) = HMod.hMod v a + a * HMod.hMod (HDiv.hDiv v a) b := by
  cases a with
  | zero =>
    rw [Nat.zero_mul, Nat.mod_zero, Nat.zero_mul, Nat.add_zero]
  | succ a' =>
    cases b with
    | zero =>
      rw [Nat.mul_zero, Nat.mod_zero, Nat.mod_zero, Nat.add_comm,
          Nat.div_add_mod]
    | succ b' =>
      exact nat_mod_mul_split_pos v (Nat.succ a') (Nat.succ b')
        (Nat.zero_lt_succ a') (Nat.zero_lt_succ b')

theorem list_take_append_left {α : Type} :
    ∀ (xs ys : List α), (xs ++ ys).take xs.length = xs
  | [], _ => rfl
  | x :: xs, ys =>
    congrArg (List.cons x) (list_take_append_left xs ys)

theorem list_drop_append_left {α : Type} :
    ∀ (xs ys : List α), (xs ++ ys).drop xs.length = ys
  | [], _ => rfl
  | _ :: xs, ys => list_drop_append_left xs ys

theorem length_map_eq {α β : Type} (f : α → β) :
    ∀ xs : List α, (xs.map f).length = xs.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (length_map_eq f rest)

theorem length_replicate_eq {α : Type} (x : α) :
    ∀ n : Nat, (List.replicate n x).length = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (length_replicate_eq x n)

theorem length_leBytesOfNat :
    ∀ n value : Nat, (leBytesOfNat n value).length = n
  | 0, _ => rfl
  | n + 1, value =>
    congrArg Nat.succ (length_leBytesOfNat n (Nat.div value 256))

theorem length_encodeUInt (endian : TargetEndian) (n value : Nat) :
    (encodeUInt endian n value).length = n := by
  cases endian with
  | little => exact length_leBytesOfNat n value
  | big =>
    unfold encodeUInt
    rw [list_length_reverse, length_leBytesOfNat]

theorem natOfLeBytes_lt :
    ∀ bs : List UInt8, natOfLeBytes bs < Nat.pow 2 (bs.length * 8)
  | [] => Nat.zero_lt_one
  | b :: rest => by
    have hb : b.toNat < 256 := b.toBitVec.isLt
    have ih := natOfLeBytes_lt rest
    have h1 : b.toNat + 256 * natOfLeBytes rest <
        256 + 256 * natOfLeBytes rest :=
      Nat.add_lt_add_right hb (256 * natOfLeBytes rest)
    have h2 : 256 + 256 * natOfLeBytes rest =
        256 * (natOfLeBytes rest + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [h2] at h1
    have h3 : 256 * (natOfLeBytes rest + 1) ≤
        256 * Nat.pow 2 (rest.length * 8) :=
      Nat.mul_le_mul_left 256 ih
    have hPow : Nat.pow 2 ((rest.length + 1) * 8) =
        256 * Nat.pow 2 (rest.length * 8) :=
      nat_two_pow_succ_mul_eight rest.length
    change b.toNat + 256 * natOfLeBytes rest <
      Nat.pow 2 ((rest.length + 1) * 8)
    rw [hPow]
    exact Nat.lt_of_lt_of_le h1 h3

theorem decodeUInt_lt (endian : TargetEndian) (bs : List UInt8) :
    decodeUInt endian bs < Nat.pow 2 (bs.length * 8) := by
  cases endian with
  | little => exact natOfLeBytes_lt bs
  | big =>
    unfold decodeUInt
    have h := natOfLeBytes_lt bs.reverse
    rw [list_length_reverse] at h
    exact h

theorem natOfLeBytes_leBytesOfNat :
    ∀ n k : Nat,
      natOfLeBytes (leBytesOfNat n k) = HMod.hMod k (Nat.pow 2 (n * 8))
  | 0, k => by
    change 0 = HMod.hMod k (Nat.pow 2 (0 * 8))
    rw [Nat.zero_mul, nat_pow_zero, Nat.mod_one]
  | n + 1, k => by
    change (UInt8.ofNat (Nat.mod k 256)).toNat +
        256 * natOfLeBytes (leBytesOfNat n (Nat.div k 256)) =
      HMod.hMod k (Nat.pow 2 ((n + 1) * 8))
    have hU8 : (UInt8.ofNat (Nat.mod k 256)).toNat = Nat.mod k 256 := by
      change (BitVec.ofNat 8 (Nat.mod k 256)).toNat = Nat.mod k 256
      rw [bv_toNat_ofNat, nat_two_pow_eight]
      exact Nat.mod_eq_of_lt (Nat.mod_lt k (by decide : 0 < 256))
    rw [hU8, natOfLeBytes_leBytesOfNat n (Nat.div k 256),
        nat_two_pow_succ_mul_eight]
    exact Eq.symm (nat_mod_mul_split k 256 (Nat.pow 2 (n * 8)))

theorem decodeUInt_encodeUInt_lt (endian : TargetEndian) (n k : Nat)
    (hk : k < Nat.pow 2 (n * 8)) :
    decodeUInt endian (encodeUInt endian n k) = k := by
  cases endian with
  | little =>
    unfold decodeUInt encodeUInt
    dsimp only
    rw [natOfLeBytes_leBytesOfNat]
    exact Nat.mod_eq_of_lt hk
  | big =>
    unfold decodeUInt encodeUInt
    dsimp only
    rw [list_reverse_reverse, natOfLeBytes_leBytesOfNat]
    exact Nat.mod_eq_of_lt hk

theorem natOfLeBytes_replicate_zero :
    ∀ n : Nat, natOfLeBytes (List.replicate n 0) = 0
  | 0 => rfl
  | n + 1 => by
    change (0 : UInt8).toNat + 256 * natOfLeBytes (List.replicate n 0) = 0
    rw [natOfLeBytes_replicate_zero n]
    rfl

theorem decodeUInt_replicate_zero (endian : TargetEndian) (n : Nat) :
    decodeUInt endian (List.replicate n 0) = 0 := by
  cases endian with
  | little => exact natOfLeBytes_replicate_zero n
  | big =>
    unfold decodeUInt
    rw [list_reverse_replicate]
    exact natOfLeBytes_replicate_zero n

theorem intWidth_bitWidth_eq (w : IntWidth) :
    w.byteSize * 8 = w.bitWidth := rfl

theorem intWidth_bitWidth_pos (w : IntWidth) : 0 < w.bitWidth := by
  cases w <;> decide

theorem intWidth_bitWidth_le_128 (w : IntWidth) : w.bitWidth ≤ 128 := by
  cases w <;> decide

theorem intWidth_byteSize_pos (w : IntWidth) : 0 < w.byteSize := by
  cases w <;> decide

theorem bitWidth_sub_one_add_one (w : IntWidth) :
    w.bitWidth - 1 + 1 = w.bitWidth := by
  cases w <;> rfl

theorem bitVec128_beq_self (x : BitVec 128) : (x == x) = true :=
  beq_self_eq_true x

theorem bitVec128_bne_self (x : BitVec 128) : (x != x) = false := by
  simp

theorem bitVec128_eq_of_bne_false {x y : BitVec 128}
    (h : (x != y) = false) : x = y := by
  simp at h
  exact h

private theorem bool_ite_true {α : Type} (a b : α) :
    (if true = true then a else b) = a := rfl

private theorem bool_ite_false {α : Type} (a b : α) :
    (if false = true then a else b) = b := rfl

private theorem list_map_id {α : Type} :
    ∀ xs : List α, List.map id xs = xs
  | [] => rfl
  | x :: rest => congrArg (List.cons x) (list_map_id rest)

theorem truncateBits_of_lt (w : IntWidth) (n : Nat)
    (hn : n < Nat.pow 2 w.bitWidth) :
    truncateBits w (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
  have hPowLe : Nat.pow 2 w.bitWidth ≤ Nat.pow 2 128 :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (intWidth_bitWidth_le_128 w)
  have hn128 : n < Nat.pow 2 128 := Nat.lt_of_lt_of_le hn hPowLe
  have hMod128 : (BitVec.ofNat 128 n).toNat = n := by
    rw [bv_toNat_ofNat]
    exact Nat.mod_eq_of_lt hn128
  unfold truncateBits bvExtractLsb bvExtractLsb' bvZeroExtend
  rw [hMod128]
  have hShift : Nat.shiftRight n 0 = n := rfl
  rw [hShift]
  apply bv_eq_of_toNat_eq
  rw [bv_toNat_ofNat, bv_toNat_ofNat, Nat.sub_zero, bitWidth_sub_one_add_one w]
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hn128]
  exact Eq.symm hMod128

/-- Every byte sequence emitted by `encodeVal` is provenance-free. -/
theorem noProvBytes_encodeVal (endian : TargetEndian) (ty : MirTy) (v : Val)
    (bs : List AllocByte) (hEnc : encodeVal endian ty v = .ok bs) :
    NoProvBytes bs := by
  unfold encodeVal at hEnc
  cases hChk : checkVal v ty with
  | false =>
    rw [hChk] at hEnc
    nomatch hEnc
  | true =>
    rw [hChk] at hEnc
    cases ty with
    | int w s =>
      cases v with
      | scalar sv =>
        injection hEnc with hBs
        rw [← hBs]
        exact noProvBytes_map_init_none _ _
      | ptr _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _
      | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
      | array _ | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc
    | bool =>
      cases v with
      | bool b =>
        injection hEnc with hBs
        rw [← hBs]
        rfl
      | scalar _ | ptr _ | char _ | ordering _ | unit | enumVal _ _ | tuple _
      | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
      | array _ | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc
    | char =>
      cases v with
      | char c =>
        injection hEnc with hBs
        rw [← hBs]
        exact noProvBytes_map_init_none _ _
      | scalar _ | ptr _ | bool _ | ordering _ | unit | enumVal _ _ | tuple _
      | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
      | array _ | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc
    | ordering =>
      cases v with
      | ordering ord =>
        injection hEnc with hBs
        rw [← hBs]
        exact noProvBytes_map_init_none _ _
      | scalar _ | ptr _ | bool _ | char _ | unit | enumVal _ _ | tuple _
      | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
      | array _ | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc
    | unit =>
      cases v with
      | unit =>
        injection hEnc with hBs
        rw [← hBs]
        rfl
      | scalar _ | ptr _ | bool _ | char _ | ordering _ | enumVal _ _ | tuple _
      | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
      | array _ | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc
    | enum ety =>
      cases v with
      | enumVal _ variant =>
        simp at hEnc
        cases hTr : ety.tagRepr with
        | zeroSized =>
          rw [hTr] at hEnc
          injection hEnc with hBs
          rw [← hBs]
          rfl
        | scalar tagW tagS =>
          rw [hTr] at hEnc
          dsimp only at hEnc
          cases hGet : Trusted.MirSemantics.getElem? ety.discriminants variant with
          | none =>
            rw [hGet] at hEnc
            nomatch hEnc
          | some disc =>
            rw [hGet] at hEnc
            injection hEnc with hBs
            rw [← hBs]
            exact noProvBytes_map_init_none _ _
      | scalar _ | ptr _ | bool _ | char _ | ordering _ | unit | tuple _
      | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
      | array _ | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc
    | tuple fs =>
      cases fs with
      | nil => nomatch hEnc
      | cons f0 fs1 =>
        cases f0 with
        | int w s =>
          cases fs1 with
          | nil => nomatch hEnc
          | cons f1 fs2 =>
            cases f1 with
            | bool =>
              cases fs2 with
              | nil =>
                cases v with
                | tuple vs =>
                  cases vs with
                  | nil => nomatch hEnc
                  | cons v0 vs1 =>
                    cases v0 with
                    | scalar sv =>
                      cases vs1 with
                      | nil => nomatch hEnc
                      | cons v1 vs2 =>
                        cases v1 with
                        | bool b =>
                          cases vs2 with
                          | nil =>
                            injection hEnc with hBs
                            rw [← hBs]
                            apply NoProvBytes_append
                            · exact NoProvBytes_append
                                (noProvBytes_map_init_none _ _) rfl
                            · exact noProvBytes_replicate_uninit _
                          | cons _ _ => nomatch hEnc
                        | scalar _ | ptr _ | char _ | ordering _ | unit
                        | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _
                        | optionVal _ | array _ | enumVal _ _ | tuple _
                        | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc
                    | ptr _ | bool _ | char _ | ordering _ | unit | enumVal _ _
                    | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _
                    | optionVal _ | array _ | tuple _
                    | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc
                | scalar _ | ptr _ | bool _ | char _ | ordering _ | unit
                | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _
                | optionVal _ | array _ | enumVal _ _
                | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc
              | cons _ _ => nomatch hEnc
            | int _ _ | unit | never | char | ordering | enum _ | tuple _
            | slice _ | str | array _ _ | rangeTo _ | rangeFrom _ | range _
            | option _ | ref _ _ | rawPtr _ _ | unsupported | box _ | vec _ =>
              nomatch hEnc
        | bool | unit | never | char | ordering | enum _ | tuple _ | ref _ _
        | slice _ | str | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _
        | rawPtr _ _ | unsupported | box _ | vec _ => nomatch hEnc
    | slice _ | str | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _
    | never | ref _ _ | rawPtr _ _ | unsupported | box _ | vec _ => nomatch hEnc

/-- Byte position `i` of a `size`-byte sequence of type `ty` whose first `i`
bytes are `pre` must be initialized under `zerocopy`'s `AsInitialized`: either
every valid instance is initialized at `i` (first clause), or some valid
instance starts with `pre` and every such instance is initialized at `i`
(second clause). -/
@[expose] def InitRequiredAt (endian : TargetEndian) (ty : MirTy) (size : Nat)
    (pre : List AllocByte) (i : Nat) : Prop :=
  (∀ (bs' : List AllocByte) (v : Val),
      bs'.length = size →
      decodeVal endian ty bs' = .ok (some v) →
      ByteInitAt bs' i) ∨
    ((∃ (bs' : List AllocByte) (v : Val),
        bs'.length = size ∧
        bs'.take i = pre ∧
        decodeVal endian ty bs' = .ok (some v)) ∧
      ∀ (bs' : List AllocByte) (v : Val),
        bs'.length = size →
        bs'.take i = pre →
        decodeVal endian ty bs' = .ok (some v) →
        ByteInitAt bs' i)

/-- Whether byte sequence `bs` satisfies `mode` at `ty` under `endian`.

`.asInitialized` models `zerocopy::pointer::invariant::AsInitialized`
(`zerocopy/src/pointer/invariant.rs`), which requires, at every offset `b` in
`[0, len)`:

> - If, in any instance `t: T` of length `len`, the byte at offset `b` in `t`
>   is initialized, then the byte at offset `b` within `*ptr` must be
>   initialized.
> - Let `c` be the contents of the byte range `[0, b)` in `*ptr`. Let `S` be
>   the subset of valid instances of `T` of length `len` which contain `c` in
>   the offset range `[0, b)`. If, in any instance of `t: T` in `S`, the byte
>   at offset `b` in `t` is initialized, then the byte at offset `b` in `*ptr`
>   must be initialized.

`InitRequiredAt` states the two bullets as alternative reasons a byte must be
initialized, reading them as follows:

- "In any instance" means "in every instance". An existential reading would
  force padding bytes, which some valid instances leave uninitialized, to be
  initialized, erasing the distinction between `AsInitialized` and
  `Initialized`.
- The second bullet applies only when `S` is nonempty. Its purpose is to follow
  valid enum discriminants ("if ... the enum discriminant stored in `*ptr`
  corresponds to a valid variant"); reading it vacuously when no valid
  instance contains `c` would also force padding after an invalid field to be
  initialized (`byteSeqValid_asInitialized_overflowPair_invalidBool`). -/
@[expose] def ByteSeqValid (endian : TargetEndian) (ty : MirTy) (mode : ValidityMode)
    (bs : List AllocByte) : Prop :=
  match mode with
  | .uninit =>
    ∃ layout, layoutOfTy ty = some layout ∧ bs.length = layout.size
  | .asInitialized =>
    ∃ layout,
      layoutOfTy ty = some layout ∧
      bs.length = layout.size ∧
      ∀ i : Nat, i < layout.size →
        InitRequiredAt endian ty layout.size (bs.take i) i → ByteInitAt bs i
  | .initialized =>
    ∃ layout,
      layoutOfTy ty = some layout ∧
      bs.length = layout.size ∧
      AllBytesInit bs
  | .bitValid | .valid =>
    ∃ layout v,
      layoutOfTy ty = some layout ∧
      bs.length = layout.size ∧
      decodeVal endian ty bs = .ok (some v)

theorem byteSeqValid_bitValid_implies_uninit (endian : TargetEndian) (ty : MirTy)
    (bs : List AllocByte) (h : ByteSeqValid endian ty .bitValid bs) :
    ByteSeqValid endian ty .uninit bs := by
  let ⟨layout, _, hLay, hLen, _⟩ := h
  exact ⟨layout, hLay, hLen⟩

theorem byteSeqValid_bitValid_implies_asInitialized (endian : TargetEndian)
    (ty : MirTy) (bs : List AllocByte)
    (h : ByteSeqValid endian ty .bitValid bs) :
    ByteSeqValid endian ty .asInitialized bs := by
  let ⟨layout, v, hLay, hLen, hDec⟩ := h
  refine ⟨layout, hLay, hLen, fun _ _ hReq => ?_⟩
  cases hReq with
  | inl hAll => exact hAll bs v hLen hDec
  | inr hS => exact hS.2 bs v hLen rfl hDec

theorem byteSeqValid_initialized_implies_asInitialized (endian : TargetEndian)
    (ty : MirTy) (bs : List AllocByte)
    (h : ByteSeqValid endian ty .initialized bs) :
    ByteSeqValid endian ty .asInitialized bs := by
  let ⟨layout, hLay, hLen, hInit⟩ := h
  exact ⟨layout, hLay, hLen, fun i hi _ =>
    byteInitAt_of_allBytesInit i bs (by rw [hLen]; exact hi) hInit⟩

theorem byteSeqValid_asInitialized_implies_uninit (endian : TargetEndian)
    (ty : MirTy) (bs : List AllocByte)
    (h : ByteSeqValid endian ty .asInitialized bs) :
    ByteSeqValid endian ty .uninit bs := by
  let ⟨layout, hLay, hLen, _⟩ := h
  exact ⟨layout, hLay, hLen⟩

theorem byteSeqValid_initialized_implies_uninit (endian : TargetEndian)
    (ty : MirTy) (bs : List AllocByte)
    (h : ByteSeqValid endian ty .initialized bs) :
    ByteSeqValid endian ty .uninit bs := by
  let ⟨layout, hLay, hLen, _⟩ := h
  exact ⟨layout, hLay, hLen⟩

theorem byteSeqValid_valid_iff_bitValid (endian : TargetEndian) (ty : MirTy)
    (bs : List AllocByte) :
    ByteSeqValid endian ty .valid bs ↔ ByteSeqValid endian ty .bitValid bs :=
  ⟨fun h => h, fun h => h⟩

/-- The unconditional first bullet of `AsInitialized`: a byte initialized in
every bit-valid sequence of the type's size is initialized in every
`.asInitialized` sequence. -/
theorem byteSeqValid_asInitialized_static (endian : TargetEndian) (ty : MirTy)
    (bs : List AllocByte) (h : ByteSeqValid endian ty .asInitialized bs) :
    ∃ layout,
      layoutOfTy ty = some layout ∧
      ∀ i : Nat, i < layout.size →
        (∀ (bs' : List AllocByte) (v : Val),
          bs'.length = layout.size →
          decodeVal endian ty bs' = .ok (some v) → ByteInitAt bs' i) →
        ByteInitAt bs i := by
  let ⟨layout, hLay, _, hReq⟩ := h
  exact ⟨layout, hLay, fun i hi hAll => hReq i hi (.inl hAll)⟩

/-- Witness that `.initialized` does not imply `.bitValid` in general:
initialized byte `0x02` is not a valid `bool`. -/
theorem byteSeqValid_initialized_not_implies_bitValid_bool
    (endian : TargetEndian) :
    ByteSeqValid endian .bool .initialized [.init (UInt8.ofNat 2) none] ∧
      ¬ ByteSeqValid endian .bool .bitValid [.init (UInt8.ofNat 2) none] := by
  constructor
  · exact ⟨⟨1, 0⟩, rfl, rfl, rfl⟩
  · intro h
    let ⟨_, _, _, _, hDec⟩ := h
    cases endian <;> nomatch hDec

/-- Witness that `.asInitialized` does not imply `.bitValid`, even on fully
initialized bytes: initialized byte `0x02` satisfies `.asInitialized` at `bool`
but is not a valid `bool`. -/
theorem byteSeqValid_asInitialized_not_implies_bitValid_bool
    (endian : TargetEndian) :
    ByteSeqValid endian .bool .asInitialized [.init (UInt8.ofNat 2) none] ∧
      ¬ ByteSeqValid endian .bool .bitValid [.init (UInt8.ofNat 2) none] :=
  let h := byteSeqValid_initialized_not_implies_bitValid_bool endian
  ⟨byteSeqValid_initialized_implies_asInitialized endian .bool _ h.1, h.2⟩

private theorem overflowPair_u32_decode_byteInitAt_zero
    (endian : TargetEndian) :
    ∀ (bs : List AllocByte) (v : Val),
      bs.length = 8 →
      decodeVal endian (.tuple [.int .i32 false, .bool]) bs = .ok (some v) →
      ByteInitAt bs 0
  | [.init _ _, _, _, _, _, _, _, _], _, _, _ => trivial
  | [.uninit, _, _, _, _, _, _, _], _, _, hDec => nomatch hDec

/-- Witness that `.bitValid` does not imply `.initialized` on padding-bearing
types: an encoded `(u32, bool)` overflow pair contains 3 `.uninit` padding bytes
yet decodes to a valid pair. -/
theorem byteSeqValid_bitValid_not_implies_initialized_overflowPair
    (endian : TargetEndian) :
    ∃ bs : List AllocByte,
      encodeVal endian (.tuple [.int .i32 false, .bool])
          (.tuple [.scalar ⟨.i32, false, 0⟩, .bool false]) = .ok bs ∧
        ByteSeqValid endian (.tuple [.int .i32 false, .bool]) .bitValid bs ∧
        ¬ ByteSeqValid endian (.tuple [.int .i32 false, .bool])
            .initialized bs := by
  cases endian with
  | little =>
    refine ⟨[AllocByte.init 0 none, AllocByte.init 0 none, AllocByte.init 0 none,
        AllocByte.init 0 none, AllocByte.init 0 none,
        AllocByte.uninit, AllocByte.uninit, AllocByte.uninit],
      rfl, ⟨⟨8, 2⟩, .tuple [.scalar ⟨.i32, false, 0⟩, .bool false], rfl, rfl, rfl⟩,
      ?_⟩
    intro h
    let ⟨_, _, _, hInit⟩ := h
    nomatch hInit
  | big =>
    refine ⟨[AllocByte.init 0 none, AllocByte.init 0 none, AllocByte.init 0 none,
        AllocByte.init 0 none, AllocByte.init 0 none,
        AllocByte.uninit, AllocByte.uninit, AllocByte.uninit],
      rfl, ⟨⟨8, 2⟩, .tuple [.scalar ⟨.i32, false, 0⟩, .bool false], rfl, rfl, rfl⟩,
      ?_⟩
    intro h
    let ⟨_, _, _, hInit⟩ := h
    nomatch hInit

private theorem overflowPair_padded_bitValid (endian : TargetEndian) :
    ByteSeqValid endian (.tuple [.int .i32 false, .bool]) .bitValid
      [.init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
        .uninit, .uninit, .uninit] := by
  cases endian <;>
    exact ⟨⟨8, 2⟩, .tuple [.scalar ⟨.i32, false, 0⟩, .bool false],
      rfl, rfl, rfl⟩

/-- An encoded `(u32, bool)` overflow pair `(0, false)` with 3 `.uninit` padding
bytes satisfies `.asInitialized`: padding is not required to be initialized. -/
theorem byteSeqValid_asInitialized_overflowPair_padded (endian : TargetEndian) :
    ByteSeqValid endian (.tuple [.int .i32 false, .bool]) .asInitialized
      [.init 0 none, .init 0 none, .init 0 none, .init 0 none, .init 0 none,
        .uninit, .uninit, .uninit] :=
  byteSeqValid_bitValid_implies_asInitialized endian _ _
    (overflowPair_padded_bitValid endian)

/-- `.asInitialized` rejects 8 `.uninit` bytes at the `(u32, bool)` overflow
pair: every valid pair initializes its `u32` bytes, so byte `0` is required to
be initialized. -/
theorem byteSeqValid_asInitialized_overflowPair_uninit_false
    (endian : TargetEndian) :
    ¬ ByteSeqValid endian (.tuple [.int .i32 false, .bool]) .asInitialized
        (List.replicate 8 AllocByte.uninit) := by
  intro h
  let ⟨layout, hLay, _, hReq⟩ := h
  have hLayEq : layout = ⟨8, 2⟩ := Option.some.inj (hLay.symm.trans rfl)
  subst hLayEq
  exact hReq 0 (Nat.zero_lt_succ _) (.inl (fun bs' v hLen hDec =>
    overflowPair_u32_decode_byteInitAt_zero endian bs' v hLen hDec))

/-- No valid `(u32, bool)` overflow pair has `bool` byte `0x02`. -/
private theorem overflowPair_invalidBool_not_valid (endian : TargetEndian) :
    ∀ (bs : List AllocByte) (v : Val),
      bs.length = 8 →
      bs.take 5 = [.init 0 none, .init 0 none, .init 0 none, .init 0 none,
        .init (UInt8.ofNat 2) none] →
      decodeVal endian (.tuple [.int .i32 false, .bool]) bs ≠ .ok (some v)
  | [_, _, _, _, _, _, _, _], _, _, hPre, hDec => by
    cases hPre
    cases endian <;> nomatch hDec

private theorem overflowPair_invalidBool_byteInitAt (endian : TargetEndian) :
    ∀ i : Nat, i < 8 →
      InitRequiredAt endian (.tuple [.int .i32 false, .bool]) 8
        ([.init 0 none, .init 0 none, .init 0 none, .init 0 none,
          .init (UInt8.ofNat 2) none, .uninit, .uninit, .uninit].take i) i →
      ByteInitAt [.init 0 none, .init 0 none, .init 0 none, .init 0 none,
        .init (UInt8.ofNat 2) none, .uninit, .uninit, .uninit] i
  | 0, _, _ | 1, _, _ | 2, _, _ | 3, _, _ | 4, _, _ => trivial
  | 5, _, .inl hAll | 6, _, .inl hAll | 7, _, .inl hAll =>
    match overflowPair_padded_bitValid endian with
    | ⟨_, vp, _, _, hDecP⟩ =>
      hAll [.init 0 none, .init 0 none, .init 0 none, .init 0 none,
        .init 0 none, .uninit, .uninit, .uninit] vp rfl hDecP
  | 5, _, .inr ⟨⟨bs', v, hLen, hPre, hDec⟩, _⟩ =>
    overflowPair_invalidBool_not_valid endian bs' v hLen hPre hDec
  | 6, _, .inr ⟨⟨[_, _, _, _, _, _, _, _], v, hLen, hPre, hDec⟩, _⟩ => by
    cases hPre
    exact overflowPair_invalidBool_not_valid endian _ v hLen rfl hDec
  | 7, _, .inr ⟨⟨[_, _, _, _, _, _, _, _], v, hLen, hPre, hDec⟩, _⟩ => by
    cases hPre
    exact overflowPair_invalidBool_not_valid endian _ v hLen rfl hDec
  | n + 8, hi, _ => absurd hi (Nat.not_lt_of_le (Nat.le_add_left 8 n))

/-- `.asInitialized` does not require padding after an invalid field: a
`(u32, bool)` overflow pair with `bool` byte `0x02` and 3 `.uninit` padding
bytes satisfies `.asInitialized` (no valid instance shares its first `5` bytes,
and some valid instance leaves the padding uninitialized) without being
`.bitValid`. -/
theorem byteSeqValid_asInitialized_overflowPair_invalidBool
    (endian : TargetEndian) :
    ByteSeqValid endian (.tuple [.int .i32 false, .bool]) .asInitialized
        [.init 0 none, .init 0 none, .init 0 none, .init 0 none,
          .init (UInt8.ofNat 2) none, .uninit, .uninit, .uninit] ∧
      ¬ ByteSeqValid endian (.tuple [.int .i32 false, .bool]) .bitValid
        [.init 0 none, .init 0 none, .init 0 none, .init 0 none,
          .init (UInt8.ofNat 2) none, .uninit, .uninit, .uninit] :=
  ⟨⟨⟨8, 2⟩, rfl, rfl, overflowPair_invalidBool_byteInitAt endian⟩,
   fun ⟨_, v, _, _, hDec⟩ =>
    overflowPair_invalidBool_not_valid endian _ v rfl rfl hDec⟩

/-! ## 2. Semantic Models of `zerocopy` Marker Traits and Transmutation -/

/-- `ty` has a layout and every `.ok (some v)` output of `decodeVal endian ty`
satisfies `validPred`. This types the trusted decoder's outputs; the byte-level
`zerocopy::TryFromBytes` contract is `IsTryFromBytes`. -/
@[expose] def DecodeTyped (endian : TargetEndian) (ty : MirTy)
    (validPred : Val → Prop) : Prop :=
  ∃ layout,
    layoutOfTy ty = some layout ∧
    ∀ bs v, decodeVal endian ty bs = .ok (some v) → validPred v

/-- Layout of `ty` for values that may live in addressable memory with a layout
Rust guarantees. Every `zerocopy` trait below concerns such memory (references,
slices, and `Ptr`s), so each requires an addressable layout. Profile v1
overflow pairs `(T, bool)` have none: Rust guarantees no `repr(Rust)` tuple
layout, and `overflowPairLayout` models a non-addressable local slot that
capture never checks against `rustc` (see
`Trusted.MirSemantics.isSupportedV2LocalTy`). `zerocopy` validates tuples by
projecting fields at compiler-selected offsets, which Profile v1 does not
capture. -/
@[expose] noncomputable def addressableLayoutOfTy (ty : MirTy) :
    Option LayoutData :=
  match isOverflowPairTy ty with
  | true => none
  | false => layoutOfTy ty

theorem layoutOfTy_of_addressableLayoutOfTy {ty : MirTy} {layout : LayoutData}
    (h : addressableLayoutOfTy ty = some layout) :
    layoutOfTy ty = some layout := by
  unfold addressableLayoutOfTy at h
  cases hP : isOverflowPairTy ty with
  | true =>
    rw [hP] at h
    nomatch h
  | false =>
    rw [hP] at h
    exact h

theorem addressableLayoutOfTy_of_not_overflowPair {ty : MirTy}
    {layout : LayoutData} (hP : isOverflowPairTy ty = false)
    (h : layoutOfTy ty = some layout) :
    addressableLayoutOfTy ty = some layout := by
  unfold addressableLayoutOfTy
  rw [hP]
  exact h

/-- Semantic model of `zerocopy::TryFromBytes` with validator `check`, modeling
the safety contract of `TryFromBytes::is_safe` (`zerocopy/src/lib.rs`):

> Unsafe code may assume that, if `is_safe(candidate)` returns true,
> `*candidate` contains a valid `Self`.

`is_safe` receives a `Maybe<Self>`, whose referent is `Initialized`
(`zerocopy/src/pointer/mod.rs`), so candidates are initialized byte sequences
of the type's size. Soundness alone admits a validator that rejects every
candidate (`isTryFromBytes_false`); `IsExactTryFromBytes` also requires `check`
to accept every bit-valid candidate. -/
@[expose] def IsTryFromBytes (endian : TargetEndian) (ty : MirTy)
    (check : List AllocByte → Bool) : Prop :=
  ∃ layout,
    addressableLayoutOfTy ty = some layout ∧
    ∀ bs,
      ByteSeqValid endian ty .initialized bs →
      check bs = true →
      ByteSeqValid endian ty .bitValid bs

/-- `check` is an exact `TryFromBytes` validator for `ty`: it accepts exactly
the bit-valid candidates among initialized byte sequences of the type's size.
-/
@[expose] def IsExactTryFromBytes (endian : TargetEndian) (ty : MirTy)
    (check : List AllocByte → Bool) : Prop :=
  ∃ layout,
    addressableLayoutOfTy ty = some layout ∧
    ∀ bs,
      ByteSeqValid endian ty .initialized bs →
      (check bs = true ↔ ByteSeqValid endian ty .bitValid bs)

/-- Semantic model of `zerocopy::FromZeros`: `ty` has an addressable layout and
all-zero initialized bytes of `layout.size` decode to a valid `Val`. -/
@[expose] def IsFromZeros (endian : TargetEndian) (ty : MirTy) : Prop :=
  ∃ layout v,
    addressableLayoutOfTy ty = some layout ∧
    decodeVal endian ty (zeroInitBytes layout.size) = .ok (some v)

/-- Semantic model of `zerocopy::FromBytes`: `ty` has an addressable layout and
every initialized byte sequence of `layout.size` decodes to a valid `Val`. -/
@[expose] def IsFromBytes (endian : TargetEndian) (ty : MirTy) : Prop :=
  ∃ layout,
    addressableLayoutOfTy ty = some layout ∧
    ∀ bs,
      bs.length = layout.size →
      AllBytesInit bs →
      ∃ v, decodeVal endian ty bs = .ok (some v)

/-- Semantic model of `zerocopy::IntoBytes`: `ty` has an addressable layout
and every valid `encodeVal` encoding has exact length `layout.size` and no
uninitialized padding bytes. -/
@[expose] def IsIntoBytes (endian : TargetEndian) (ty : MirTy) : Prop :=
  ∃ layout,
    addressableLayoutOfTy ty = some layout ∧
    ∀ v bs,
      encodeVal endian ty v = .ok bs →
      bs.length = layout.size ∧ AllBytesInit bs

/-- Semantic model of `zerocopy::Unaligned`: an addressable layout with ABI
alignment of `1` byte (`alignLog2 = 0`). -/
@[expose] def IsUnaligned (ty : MirTy) : Prop :=
  ∃ layout, addressableLayoutOfTy ty = some layout ∧ layout.alignLog2 = 0

/-- Core `zerocopy` marker traits modeled by `BitValidity`; `tryFromBytes`
carries its validator. -/
inductive ZerocopyTrait : Type where
  | tryFromBytes (check : List AllocByte → Bool)
  | fromZeros
  | fromBytes
  | intoBytes
  | unaligned

/-- Unified trait-validity predicate dispatching on `ZerocopyTrait`. -/
@[expose, reducible]
def ValidForTrait (tr : ZerocopyTrait) (endian : TargetEndian) (ty : MirTy) :
    Prop :=
  match tr with
  | .tryFromBytes check => IsTryFromBytes endian ty check
  | .fromZeros => IsFromZeros endian ty
  | .fromBytes => IsFromBytes endian ty
  | .intoBytes => IsIntoBytes endian ty
  | .unaligned => IsUnaligned ty

theorem layoutOfTy_unique {ty : MirTy} {a b : LayoutData}
    (ha : layoutOfTy ty = some a) (hb : layoutOfTy ty = some b) : a = b :=
  Option.some.inj (ha.symm.trans hb)

/-- Soundness of a `TryFromBytes` validator: an accepted initialized candidate
is bit-valid. -/
theorem try_from_bytes_sound {endian : TargetEndian} {ty : MirTy}
    {check : List AllocByte → Bool} (h : IsTryFromBytes endian ty check)
    {bs : List AllocByte} (hInit : ByteSeqValid endian ty .initialized bs)
    (hCheck : check bs = true) : ByteSeqValid endian ty .bitValid bs :=
  let ⟨_, _, hSound⟩ := h
  hSound bs hInit hCheck

theorem isExactTryFromBytes_implies_isTryFromBytes {endian : TargetEndian}
    {ty : MirTy} {check : List AllocByte → Bool}
    (h : IsExactTryFromBytes endian ty check) :
    IsTryFromBytes endian ty check :=
  let ⟨layout, hLay, hIff⟩ := h
  ⟨layout, hLay, fun bs hInit hCheck => (hIff bs hInit).1 hCheck⟩

/-- Soundness alone does not pin down a validator: rejecting every candidate is
sound for every type with an addressable layout. -/
theorem isTryFromBytes_false (endian : TargetEndian) {ty : MirTy}
    {layout : LayoutData} (hLay : addressableLayoutOfTy ty = some layout) :
    IsTryFromBytes endian ty (fun _ => false) :=
  ⟨layout, hLay, fun _ _ hCheck => nomatch hCheck⟩

/-- The validator that accepts every candidate is sound exactly for
`FromBytes` types. -/
theorem isTryFromBytes_true_iff_isFromBytes (endian : TargetEndian)
    (ty : MirTy) :
    IsTryFromBytes endian ty (fun _ => true) ↔ IsFromBytes endian ty := by
  constructor
  · intro ⟨layout, hLay, hSound⟩
    refine ⟨layout, hLay, fun bs hLen hInit => ?_⟩
    let ⟨_, v, _, _, hDec⟩ :=
      hSound bs
        ⟨layout, layoutOfTy_of_addressableLayoutOfTy hLay, hLen, hInit⟩ rfl
    exact ⟨v, hDec⟩
  · intro ⟨layout, hLay, hDec⟩
    refine ⟨layout, hLay, fun bs ⟨l, hL, hLen, hInit⟩ _ => ?_⟩
    have hEq := layoutOfTy_unique hL (layoutOfTy_of_addressableLayoutOfTy hLay)
    subst hEq
    let ⟨v, hv⟩ := hDec bs hLen hInit
    exact ⟨l, v, hL, hLen, hv⟩

theorem isFromBytes_implies_isExactTryFromBytes (endian : TargetEndian)
    (ty : MirTy) (h : IsFromBytes endian ty) :
    IsExactTryFromBytes endian ty (fun _ => true) :=
  let ⟨layout, hLay, hSound⟩ :=
    (isTryFromBytes_true_iff_isFromBytes endian ty).2 h
  ⟨layout, hLay, fun bs hInit =>
    ⟨fun hCheck => hSound bs hInit hCheck, fun _ => rfl⟩⟩

theorem isFromBytes_implies_isTryFromBytes (endian : TargetEndian) (ty : MirTy)
    (h : IsFromBytes endian ty) : IsTryFromBytes endian ty (fun _ => true) :=
  (isTryFromBytes_true_iff_isFromBytes endian ty).2 h

theorem decodeTyped_mono {endian : TargetEndian} {ty : MirTy}
    {P Q : Val → Prop} (hPQ : ∀ v, P v → Q v)
    (h : DecodeTyped endian ty P) :
    DecodeTyped endian ty Q := by
  let ⟨layout, hLay, hPred⟩ := h
  exact ⟨layout, hLay, fun bs v hv => hPQ v (hPred bs v hv)⟩

theorem isFromBytes_implies_isFromZeros (endian : TargetEndian) (ty : MirTy)
    (h : IsFromBytes endian ty) : IsFromZeros endian ty := by
  let ⟨layout, hLay, hDec⟩ := h
  let ⟨v, hv⟩ := hDec (zeroInitBytes layout.size)
    (length_zeroInitBytes layout.size) (allBytesInit_zeroInitBytes layout.size)
  exact ⟨layout, v, hLay, hv⟩

/-- Soundness of safe byte transmutation (`zerocopy::transmute!`): encoding any
valid value of an `IsIntoBytes` source type produces a byte sequence that
decodes without UB at any equal-size `IsFromBytes` destination type. -/
theorem transmute_sound_of_into_from_bytes (endian : TargetEndian)
    (srcTy dstTy : MirTy)
    (hInto : IsIntoBytes endian srcTy)
    (hFrom : IsFromBytes endian dstTy)
    (hSizeEq :
      (layoutOfTy srcTy).map LayoutData.size =
        (layoutOfTy dstTy).map LayoutData.size)
    (v : Val) (bs : List AllocByte)
    (hEnc : encodeVal endian srcTy v = .ok bs) :
    ∃ v', decodeVal endian dstTy bs = .ok (some v') := by
  let ⟨srcLay, hSrcLay, hEncProps⟩ := hInto
  let ⟨dstLay, hDstLay, hDecProps⟩ := hFrom
  rw [layoutOfTy_of_addressableLayoutOfTy hSrcLay,
    layoutOfTy_of_addressableLayoutOfTy hDstLay] at hSizeEq
  dsimp only [Option.map] at hSizeEq
  injection hSizeEq with hSzEq
  have ⟨hLen, hInit⟩ := hEncProps v bs hEnc
  rw [hSzEq] at hLen
  exact hDecProps bs hLen hInit

/-- Provenance-free companion to `transmute_sound_of_into_from_bytes`: the
encoded byte sequence also satisfies `NoProvBytes`. -/
theorem transmute_sound_noProv_of_into_from_bytes (endian : TargetEndian)
    (srcTy dstTy : MirTy)
    (hInto : IsIntoBytes endian srcTy)
    (hFrom : IsFromBytes endian dstTy)
    (hSizeEq :
      (layoutOfTy srcTy).map LayoutData.size =
        (layoutOfTy dstTy).map LayoutData.size)
    (v : Val) (bs : List AllocByte)
    (hEnc : encodeVal endian srcTy v = .ok bs) :
    NoProvBytes bs ∧ ∃ v', decodeVal endian dstTy bs = .ok (some v') :=
  ⟨noProvBytes_encodeVal endian srcTy v bs hEnc,
   transmute_sound_of_into_from_bytes endian srcTy dstTy hInto hFrom hSizeEq
     v bs hEnc⟩

/-- Byte-validity view of `transmute_sound_noProv_of_into_from_bytes`: the
encoded bytes satisfy `ByteSeqValid endian dstTy .bitValid bs` and carry no
provenance. -/
theorem transmute_sound_byteSeqValid (endian : TargetEndian)
    (srcTy dstTy : MirTy)
    (hInto : IsIntoBytes endian srcTy)
    (hFrom : IsFromBytes endian dstTy)
    (hSizeEq :
      (layoutOfTy srcTy).map LayoutData.size =
        (layoutOfTy dstTy).map LayoutData.size)
    (v : Val) (bs : List AllocByte)
    (hEnc : encodeVal endian srcTy v = .ok bs) :
    ByteSeqValid endian dstTy .bitValid bs ∧ NoProvBytes bs := by
  have ⟨hNoProv, v', hv'⟩ :=
    transmute_sound_noProv_of_into_from_bytes endian srcTy dstTy hInto hFrom
      hSizeEq v bs hEnc
  let ⟨srcLay, hSrcLay, hEncProps⟩ := hInto
  let ⟨dstLay, hDstLay, _⟩ := hFrom
  have hDstLay' := layoutOfTy_of_addressableLayoutOfTy hDstLay
  rw [layoutOfTy_of_addressableLayoutOfTy hSrcLay, hDstLay'] at hSizeEq
  dsimp only [Option.map] at hSizeEq
  injection hSizeEq with hSzEq
  have ⟨hLen, _⟩ := hEncProps v bs hEnc
  rw [hSzEq] at hLen
  exact ⟨⟨dstLay, v', hDstLay', hLen, hv'⟩, hNoProv⟩

/-! ## 3. Profile v1 Type Theorems (`∀ endian : TargetEndian`) -/

/-! ### 3a. Primitive Integers (`.int w s`: `i8..i128/isize`, `u8..u128/usize`)
-/

theorem int_isFromBytes (endian : TargetEndian) (w : IntWidth) (s : Bool) :
    IsFromBytes endian (.int w s) := by
  refine ⟨intLayout w, rfl, ?_⟩
  intro bs hLen hInit
  have ⟨raw, hRaw, hRawLen⟩ := initBytes?_isSome_of_allBytesInit bs hInit
  have hDecLt : decodeUInt endian raw < Nat.pow 2 w.bitWidth := by
    have h1 := decodeUInt_lt endian raw
    have hLenRaw : raw.length = w.byteSize := by
      rw [hRawLen, hLen]
      cases w <;> rfl
    rw [hLenRaw, intWidth_bitWidth_eq] at h1
    exact h1
  have hTrunc :
      truncateBits w (BitVec.ofNat 128 (decodeUInt endian raw)) =
        BitVec.ofNat 128 (decodeUInt endian raw) :=
    truncateBits_of_lt w (decodeUInt endian raw) hDecLt
  have hNe :
      (truncateBits w (BitVec.ofNat 128 (decodeUInt endian raw)) !=
        BitVec.ofNat 128 (decodeUInt endian raw)) = false := by
    rw [hTrunc]
    exact bitVec128_bne_self _
  have hLayLen : Nat.beq bs.length (intLayout w).size = true := by
    rw [hLen]
    exact nat_beq_refl _
  have hLayNz : Nat.beq (intLayout w).size 0 = false := by
    cases w <;> rfl
  refine ⟨.scalar ⟨w, s, BitVec.ofNat 128 (decodeUInt endian raw)⟩, ?_⟩
  unfold decodeVal layoutOfTy
  simp [hLayLen, hLayNz, hRaw]
  unfold evalConstLit
  simp [hTrunc]

theorem int_isFromZeros (endian : TargetEndian) (w : IntWidth) (s : Bool) :
    IsFromZeros endian (.int w s) :=
  isFromBytes_implies_isFromZeros endian (.int w s)
    (int_isFromBytes endian w s)

theorem int_isIntoBytes (endian : TargetEndian) (w : IntWidth) (s : Bool) :
    IsIntoBytes endian (.int w s) := by
  refine ⟨intLayout w, rfl, ?_⟩
  intro v bs hEnc
  unfold encodeVal at hEnc
  cases hChk : checkVal v (.int w s) with
  | false =>
    rw [hChk] at hEnc
    nomatch hEnc
  | true =>
    rw [hChk] at hEnc
    cases v with
    | scalar sv =>
      injection hEnc with hBs
      rw [← hBs, length_map_eq, length_encodeUInt]
      have hWSize : (intLayout w).size = w.byteSize := by cases w <;> rfl
      exact ⟨hWSize.symm, allBytesInit_map_init_none _ _⟩
    | ptr _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _
    | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
    | array _ | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc

theorem int_decodeTyped (endian : TargetEndian) (w : IntWidth)
    (s : Bool) :
    DecodeTyped endian (.int w s)
      (fun v =>
        ∃ sv : ScalarVal,
          v = .scalar sv ∧ sv.width = w ∧ sv.signed = s ∧ sv.wf = true) := by
  refine ⟨intLayout w, rfl, ?_⟩
  intro bs v hDec
  unfold decodeVal layoutOfTy at hDec
  dsimp only at hDec
  cases hLen : Nat.beq bs.length (intLayout w).size with
  | false =>
    rw [hLen] at hDec
    nomatch hDec
  | true =>
    rw [hLen] at hDec
    have hNz : Nat.beq (intLayout w).size 0 = false := by cases w <;> rfl
    simp [hNz] at hDec
    cases hRaw : initBytes? bs with
    | none =>
      rw [hRaw] at hDec
      nomatch hDec
    | some raw =>
      rw [hRaw] at hDec
      dsimp only at hDec
      unfold evalConstLit at hDec
      dsimp only at hDec
      cases hTrunc :
          (truncateBits w (BitVec.ofNat 128 (decodeUInt endian raw)) !=
            BitVec.ofNat 128 (decodeUInt endian raw)) with
      | true =>
        rw [hTrunc] at hDec
        nomatch hDec
      | false =>
        rw [hTrunc] at hDec
        injection hDec with hOpt
        injection hOpt with hV
        rw [← hV]
        have hEqProp := bitVec128_eq_of_bne_false hTrunc
        refine ⟨⟨w, s, truncateBits w
            (BitVec.ofNat 128 (decodeUInt endian raw))⟩,
          rfl, rfl, rfl, ?_⟩
        unfold ScalarVal.wf
        rw [hEqProp, hEqProp]
        exact bitVec128_beq_self _

theorem int_i8_isUnaligned (s : Bool) : IsUnaligned (.int .i8 s) :=
  ⟨⟨1, 0⟩, rfl, rfl⟩

theorem int_not_isUnaligned_of_ne_i8 {w : IntWidth} (hw : w ≠ .i8)
    (s : Bool) : ¬ IsUnaligned (.int w s) := by
  intro h
  let ⟨layout, hLay, hAlign⟩ := h
  injection hLay with hEq
  rw [← hEq] at hAlign
  cases w with
  | i8 => exact hw rfl
  | i16 | i32 | i64 | i128 | isize => nomatch hAlign

theorem int_isUnaligned_iff (w : IntWidth) (s : Bool) :
    IsUnaligned (.int w s) ↔ w = .i8 := by
  constructor
  · intro h
    cases w with
    | i8 => rfl
    | i16 | i32 | i64 | i128 | isize =>
      exact False.elim (int_not_isUnaligned_of_ne_i8 (fun hE => by nomatch hE) s h)
  · intro hw
    rw [hw]
    exact int_i8_isUnaligned s

/-! ### 3b. Unit `.unit` and Never `.never` -/

theorem unit_decodeTyped_eq (endian : TargetEndian) :
    DecodeTyped endian .unit (fun v => v = .unit) := by
  refine ⟨⟨0, 0⟩, rfl, ?_⟩
  intro bs v hDec
  unfold decodeVal layoutOfTy at hDec
  dsimp only at hDec
  cases hLen : Nat.beq bs.length 0 with
  | false =>
    rw [hLen] at hDec
    nomatch hDec
  | true =>
    simp [hLen] at hDec
    injection hDec with hOpt
    injection hOpt with hV
    exact hV.symm

theorem unit_isFromZeros (endian : TargetEndian) : IsFromZeros endian .unit :=
  ⟨⟨0, 0⟩, .unit, rfl, rfl⟩

theorem unit_isFromBytes (endian : TargetEndian) : IsFromBytes endian .unit := by
  refine ⟨⟨0, 0⟩, rfl, ?_⟩
  intro bs hLen _
  cases bs with
  | nil => exact ⟨.unit, rfl⟩
  | cons _ _ => nomatch hLen

theorem unit_isIntoBytes (endian : TargetEndian) : IsIntoBytes endian .unit := by
  refine ⟨⟨0, 0⟩, rfl, ?_⟩
  intro v bs hEnc
  unfold encodeVal at hEnc
  cases hChk : checkVal v .unit with
  | false =>
    rw [hChk] at hEnc
    nomatch hEnc
  | true =>
    rw [hChk] at hEnc
    cases v with
    | unit =>
      injection hEnc with hBs
      rw [← hBs]
      exact ⟨rfl, rfl⟩
    | scalar _ | ptr _ | bool _ | char _ | ordering _ | enumVal _ _ | tuple _
    | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
    | array _ | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc

theorem unit_isUnaligned : IsUnaligned .unit :=
  ⟨⟨0, 0⟩, rfl, rfl⟩

theorem never_decodeTyped_empty (endian : TargetEndian) :
    DecodeTyped endian .never (fun _ => False) := by
  refine ⟨⟨0, 0⟩, rfl, ?_⟩
  intro bs v hDec
  nomatch hDec

theorem never_isIntoBytes (endian : TargetEndian) :
    IsIntoBytes endian .never := by
  refine ⟨⟨0, 0⟩, rfl, ?_⟩
  intro v bs hEnc
  unfold encodeVal at hEnc
  cases hChk : checkVal v .never <;> rw [hChk] at hEnc <;> nomatch hEnc

theorem never_isUnaligned : IsUnaligned .never :=
  ⟨⟨0, 0⟩, rfl, rfl⟩

theorem never_not_isFromZeros (endian : TargetEndian) :
    ¬ IsFromZeros endian .never := by
  intro h
  let ⟨layout, _, hLay, hDec⟩ := h
  injection hLay with hEq
  rw [← hEq] at hDec
  nomatch hDec

theorem never_not_isFromBytes (endian : TargetEndian) :
    ¬ IsFromBytes endian .never := by
  intro h
  let ⟨layout, hLay, hDec⟩ := h
  injection hLay with hEq
  have ⟨_, hv⟩ := hDec [] (by rw [← hEq]; rfl) rfl
  nomatch hv

/-! ### 3c. Boolean `.bool` -/

theorem bool_isIntoBytes (endian : TargetEndian) : IsIntoBytes endian .bool := by
  refine ⟨⟨1, 0⟩, rfl, ?_⟩
  intro v bs hEnc
  unfold encodeVal at hEnc
  cases hChk : checkVal v .bool with
  | false =>
    rw [hChk] at hEnc
    nomatch hEnc
  | true =>
    rw [hChk] at hEnc
    cases v with
    | bool _ =>
      injection hEnc with hBs
      rw [← hBs]
      exact ⟨rfl, rfl⟩
    | scalar _ | ptr _ | char _ | ordering _ | unit | enumVal _ _ | tuple _
    | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
    | array _ | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc

theorem bool_isFromZeros (endian : TargetEndian) : IsFromZeros endian .bool := by
  cases endian with
  | little => exact ⟨⟨1, 0⟩, .bool false, rfl, rfl⟩
  | big => exact ⟨⟨1, 0⟩, .bool false, rfl, rfl⟩

theorem bool_isUnaligned : IsUnaligned .bool :=
  ⟨⟨1, 0⟩, rfl, rfl⟩

theorem bool_decodeTyped (endian : TargetEndian) :
    DecodeTyped endian .bool (fun v => v = .bool false ∨ v = .bool true) := by
  refine ⟨⟨1, 0⟩, rfl, ?_⟩
  intro bs v hDec
  unfold decodeVal layoutOfTy at hDec
  dsimp only at hDec
  cases hLen : Nat.beq bs.length 1 with
  | false =>
    rw [hLen] at hDec
    nomatch hDec
  | true =>
    simp [hLen] at hDec
    cases hRaw : initBytes? bs with
    | none =>
      rw [hRaw] at hDec
      nomatch hDec
    | some raw =>
      rw [hRaw] at hDec
      dsimp only at hDec
      unfold evalConstLit at hDec
      dsimp only at hDec
      cases hTrunc :
          (truncateBits .i8 (BitVec.ofNat 128 (decodeUInt endian raw)) !=
            BitVec.ofNat 128 (decodeUInt endian raw)) with
      | true =>
        rw [hTrunc] at hDec
        nomatch hDec
      | false =>
        rw [hTrunc, bool_ite_false] at hDec
        cases h0 :
            (UInt8.ofNat
                (truncateBits .i8
                  (BitVec.ofNat 128 (decodeUInt endian raw))).toNat == 0) with
        | true =>
          rw [h0, bool_ite_true] at hDec
          injection hDec with hOpt
          injection hOpt with hV
          exact Or.inl hV.symm
        | false =>
          rw [h0, bool_ite_false] at hDec
          cases h1 :
              (UInt8.ofNat
                  (truncateBits .i8
                    (BitVec.ofNat 128 (decodeUInt endian raw))).toNat == 1) with
          | true =>
            rw [h1, bool_ite_true] at hDec
            injection hDec with hOpt
            injection hOpt with hV
            exact Or.inr hV.symm
          | false =>
            rw [h1, bool_ite_false] at hDec
            nomatch hDec

theorem bool_not_isFromBytes (endian : TargetEndian) :
    ¬ IsFromBytes endian .bool := by
  intro h
  let ⟨layout, hLay, hDec⟩ := h
  injection hLay with hEq
  have ⟨_, hv⟩ :=
    hDec [.init (UInt8.ofNat 2) none] (by rw [← hEq]; rfl) rfl
  cases endian <;> nomatch hv

/-! ### 3d. Unicode Scalar `.char` -/

theorem char_isIntoBytes (endian : TargetEndian) : IsIntoBytes endian .char := by
  refine ⟨⟨4, 2⟩, rfl, ?_⟩
  intro v bs hEnc
  unfold encodeVal at hEnc
  cases hChk : checkVal v .char with
  | false =>
    rw [hChk] at hEnc
    nomatch hEnc
  | true =>
    rw [hChk] at hEnc
    cases v with
    | char c =>
      injection hEnc with hBs
      rw [← hBs, length_map_eq, length_encodeUInt]
      exact ⟨rfl, allBytesInit_map_init_none _ _⟩
    | scalar _ | ptr _ | bool _ | ordering _ | unit | enumVal _ _ | tuple _
    | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
    | array _ | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc

theorem char_isFromZeros (endian : TargetEndian) : IsFromZeros endian .char := by
  cases endian with
  | little => exact ⟨⟨4, 2⟩, .char (Char.ofNat 0), rfl, rfl⟩
  | big => exact ⟨⟨4, 2⟩, .char (Char.ofNat 0), rfl, rfl⟩

theorem char_decodeTyped (endian : TargetEndian) :
    DecodeTyped endian .char
      (fun v =>
        ∃ n : Nat, isUnicodeScalar n = true ∧ v = .char (Char.ofNat n)) := by
  refine ⟨⟨4, 2⟩, rfl, ?_⟩
  intro bs v hDec
  unfold decodeVal layoutOfTy at hDec
  dsimp only at hDec
  cases hLen : Nat.beq bs.length 4 with
  | false =>
    rw [hLen] at hDec
    nomatch hDec
  | true =>
    simp [hLen] at hDec
    cases hRaw : initBytes? bs with
    | none =>
      rw [hRaw] at hDec
      nomatch hDec
    | some raw =>
      rw [hRaw] at hDec
      dsimp only at hDec
      unfold evalConstLit at hDec
      dsimp only at hDec
      cases hTrunc :
          (truncateBits .i32 (BitVec.ofNat 128 (decodeUInt endian raw)) !=
            BitVec.ofNat 128 (decodeUInt endian raw)) with
      | true =>
        rw [hTrunc] at hDec
        nomatch hDec
      | false =>
        simp [hTrunc] at hDec
        cases hUni :
            isUnicodeScalar (BitVec.ofNat 128 (decodeUInt endian raw)).toNat with
        | false =>
          rw [hUni] at hDec
          nomatch hDec
        | true =>
          rw [hUni] at hDec
          injection hDec with hOpt
          injection hOpt with hV
          exact ⟨(BitVec.ofNat 128 (decodeUInt endian raw)).toNat, hUni, hV.symm⟩

theorem char_not_isFromBytes (endian : TargetEndian) :
    ¬ IsFromBytes endian .char := by
  intro h
  let ⟨layout, hLay, hDec⟩ := h
  injection hLay with hEq
  cases endian with
  | little =>
    have ⟨_, hv⟩ :=
      hDec [.init 0x00 none, .init 0xD8 none, .init 0x00 none, .init 0x00 none]
        (by rw [← hEq]; rfl) rfl
    nomatch hv
  | big =>
    have ⟨_, hv⟩ :=
      hDec [.init 0x00 none, .init 0x00 none, .init 0xD8 none, .init 0x00 none]
        (by rw [← hEq]; rfl) rfl
    nomatch hv

theorem char_not_isUnaligned : ¬ IsUnaligned .char := by
  intro h
  let ⟨layout, hLay, hAlign⟩ := h
  injection hLay with hEq
  rw [← hEq] at hAlign
  nomatch hAlign

/-! ### 3e. `core::cmp::Ordering` (`.ordering`) -/

theorem ordering_isIntoBytes (endian : TargetEndian) :
    IsIntoBytes endian .ordering := by
  refine ⟨⟨1, 0⟩, rfl, ?_⟩
  intro v bs hEnc
  unfold encodeVal at hEnc
  cases hChk : checkVal v .ordering with
  | false =>
    rw [hChk] at hEnc
    nomatch hEnc
  | true =>
    rw [hChk] at hEnc
    cases v with
    | ordering ord =>
      injection hEnc with hBs
      rw [← hBs, length_map_eq, length_encodeUInt]
      exact ⟨rfl, allBytesInit_map_init_none _ _⟩
    | scalar _ | ptr _ | bool _ | char _ | unit | enumVal _ _ | tuple _
    | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
    | array _ | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc

theorem ordering_isFromZeros (endian : TargetEndian) :
    IsFromZeros endian .ordering := by
  cases endian with
  | little => exact ⟨⟨1, 0⟩, .ordering .equal, rfl, rfl⟩
  | big => exact ⟨⟨1, 0⟩, .ordering .equal, rfl, rfl⟩

theorem ordering_isUnaligned : IsUnaligned .ordering :=
  ⟨⟨1, 0⟩, rfl, rfl⟩

theorem ordering_decodeTyped (endian : TargetEndian) :
    DecodeTyped endian .ordering (fun v => ∃ ord, v = .ordering ord) := by
  refine ⟨⟨1, 0⟩, rfl, ?_⟩
  intro bs v hDec
  unfold decodeVal layoutOfTy at hDec
  dsimp only at hDec
  cases hLen : Nat.beq bs.length 1 with
  | false =>
    rw [hLen] at hDec
    nomatch hDec
  | true =>
    simp [hLen] at hDec
    cases hRaw : initBytes? bs with
    | none =>
      rw [hRaw] at hDec
      nomatch hDec
    | some raw =>
      rw [hRaw] at hDec
      dsimp only at hDec
      unfold evalConstLit at hDec
      dsimp only at hDec
      cases hTrunc :
          (truncateBits .i8 (BitVec.ofNat 128 (decodeUInt endian raw)) !=
            BitVec.ofNat 128 (decodeUInt endian raw)) with
      | true =>
        rw [hTrunc] at hDec
        nomatch hDec
      | false =>
        simp [hTrunc] at hDec
        cases hOrd :
            orderingOfTagBits
              (BitVec.ofNat 128 (decodeUInt endian raw)).toNat with
        | none =>
          rw [hOrd] at hDec
          nomatch hDec
        | some ord =>
          rw [hOrd] at hDec
          injection hDec with hOpt
          injection hOpt with hV
          exact ⟨ord, hV.symm⟩

theorem ordering_not_isFromBytes (endian : TargetEndian) :
    ¬ IsFromBytes endian .ordering := by
  intro h
  let ⟨layout, hLay, hDec⟩ := h
  injection hLay with hEq
  have ⟨_, hv⟩ := hDec [.init 2 none] (by rw [← hEq]; rfl) rfl
  cases endian <;> nomatch hv

/-! ### 3f. Overflow Pairs (`.tuple [.int w s, .bool]`)

`overflowPairLayout` models Profile v1's internal, non-addressable local-slot
representation of the `(T, bool)` results of checked arithmetic; Rust
guarantees no layout for `repr(Rust)` tuples. Overflow pairs therefore satisfy
none of the modeled `zerocopy` traits (`overflowPair_not_validForTrait`), even
though `zerocopy` implements `TryFromBytes`, `FromZeros`, and `FromBytes` for
tuples by projecting fields at compiler-selected offsets, which Profile v1 does
not capture. The `ByteSeqValid`, `DecodeTyped`, `decodeVal`, and `encodeVal`
results below (`overflowPair_localSlot_*`,
`overflowPair_encodeVal_allBytesInit_iff`) describe only the local-slot
representation. -/

theorem overflowPair_size_pos (w : IntWidth) :
    w.byteSize + 1 + (w.byteSize - 1) = (overflowPairLayout w).size := by
  cases w <;> rfl

/-- Not every initialized local-slot byte sequence decodes: a `bool` byte `0x02`
is invalid. This is the local-slot analog of `¬ FromBytes`. -/
theorem overflowPair_localSlot_not_allInitDecode (endian : TargetEndian)
    (w : IntWidth) (s : Bool) :
    ¬ ∀ bs,
        bs.length = (overflowPairLayout w).size →
        AllBytesInit bs →
        ∃ v, decodeVal endian (.tuple [.int w s, .bool]) bs = .ok (some v) := by
  intro hDec
  let badBs : List AllocByte :=
    zeroInitBytes w.byteSize ++ [.init 2 none] ++ zeroInitBytes (w.byteSize - 1)
  have hBadLen : badBs.length = (overflowPairLayout w).size := by
    dsimp [badBs]
    rw [List.length_append, List.length_append, length_zeroInitBytes,
        List.length_cons, List.length_nil, length_zeroInitBytes]
    exact overflowPair_size_pos w
  have hBadInit : AllBytesInit badBs := by
    apply AllBytesInit_append
    · exact AllBytesInit_append (allBytesInit_zeroInitBytes _) rfl
    · exact allBytesInit_zeroInitBytes _
  have ⟨_, hv⟩ := hDec badBs hBadLen hBadInit
  have hLayBeq :
      Nat.beq badBs.length (overflowPairLayout w).size = true := by
    rw [hBadLen]
    exact nat_beq_refl _
  have hTake :
      badBs.take w.byteSize = zeroInitBytes w.byteSize := by
    have hAssoc :
        badBs = zeroInitBytes w.byteSize ++
          ([AllocByte.init 2 none] ++ zeroInitBytes (w.byteSize - 1)) :=
      List.append_assoc _ _ _
    rw [hAssoc]
    have hLeft := list_take_append_left (zeroInitBytes w.byteSize)
      ([AllocByte.init 2 none] ++ zeroInitBytes (w.byteSize - 1))
    rw [length_zeroInitBytes] at hLeft
    exact hLeft
  have hDropTake :
      (badBs.drop w.byteSize).take 1 = [AllocByte.init 2 none] := by
    have hAssoc :
        badBs = zeroInitBytes w.byteSize ++
          ([AllocByte.init 2 none] ++ zeroInitBytes (w.byteSize - 1)) :=
      List.append_assoc _ _ _
    rw [hAssoc]
    have hDrop := list_drop_append_left (zeroInitBytes w.byteSize)
      ([AllocByte.init 2 none] ++ zeroInitBytes (w.byteSize - 1))
    rw [length_zeroInitBytes] at hDrop
    rw [hDrop]
    rfl
  unfold decodeVal at hv
  simp [hLayBeq, hTake, hDropTake, initBytes?_zeroInitBytes] at hv
  have hBoolInit :
      initBytes? [AllocByte.init 2 none] = some [2] := rfl
  rw [hBoolInit] at hv
  dsimp only at hv
  have hZeroLt :
      decodeUInt endian (List.replicate w.byteSize 0) < Nat.pow 2 w.bitWidth := by
    rw [decodeUInt_replicate_zero]
    exact nat_two_pow_pos _
  have hTruncZero :
      truncateBits w
          (BitVec.ofNat 128 (decodeUInt endian (List.replicate w.byteSize 0))) =
        BitVec.ofNat 128 (decodeUInt endian (List.replicate w.byteSize 0)) :=
    truncateBits_of_lt w _ hZeroLt
  have hNeZero :
      (truncateBits w
          (BitVec.ofNat 128 (decodeUInt endian (List.replicate w.byteSize 0))) !=
        BitVec.ofNat 128 (decodeUInt endian (List.replicate w.byteSize 0))) =
        false := by
    rw [hTruncZero]
    exact bitVec128_bne_self _
  unfold evalConstLit at hv
  simp [hNeZero] at hv
  cases endian <;> nomatch hv

theorem overflowPair_decodeTyped (endian : TargetEndian)
    (w : IntWidth) (s : Bool) :
    DecodeTyped endian (.tuple [.int w s, .bool])
      (fun v =>
        ∃ sv b, v = .tuple [.scalar sv, .bool b] ∧
          sv.width = w ∧ sv.signed = s ∧ sv.wf = true) := by
  refine ⟨overflowPairLayout w, rfl, ?_⟩
  intro bs v hDec
  unfold decodeVal at hDec
  dsimp only at hDec
  cases hLen : Nat.beq bs.length (overflowPairLayout w).size with
  | false =>
    rw [hLen] at hDec
    nomatch hDec
  | true =>
    simp [hLen] at hDec
    cases hIntRaw : initBytes? (bs.take w.byteSize) with
    | none =>
      rw [hIntRaw] at hDec
      nomatch hDec
    | some intRaw =>
      cases hBoolRaw : initBytes? ((bs.drop w.byteSize).take 1) with
      | none =>
        rw [hIntRaw, hBoolRaw] at hDec
        nomatch hDec
      | some boolRaw =>
        rw [hIntRaw, hBoolRaw] at hDec
        dsimp only at hDec
        cases hIntEv : evalConstLit (.int w s)
            (.scalar (BitVec.ofNat 128 (decodeUInt endian intRaw))) with
        | error _ =>
          rw [hIntEv] at hDec
          nomatch hDec
        | ok intVal =>
          rw [hIntEv] at hDec
          dsimp only at hDec
          cases hBoolEv : evalConstLit .bool
              (.scalar (BitVec.ofNat 128 (decodeUInt endian boolRaw))) with
          | error _ =>
            rw [hBoolEv] at hDec
            nomatch hDec
          | ok boolVal =>
            rw [hBoolEv] at hDec
            injection hDec with hOpt
            injection hOpt with hV
            unfold evalConstLit at hIntEv
            dsimp only at hIntEv
            cases hTruncI :
                (truncateBits w (BitVec.ofNat 128 (decodeUInt endian intRaw)) !=
                  BitVec.ofNat 128 (decodeUInt endian intRaw)) with
            | true =>
              rw [hTruncI] at hIntEv
              nomatch hIntEv
            | false =>
              rw [hTruncI] at hIntEv
              injection hIntEv with hIv
              have hEqI := bitVec128_eq_of_bne_false hTruncI
              unfold evalConstLit at hBoolEv
              dsimp only at hBoolEv
              cases hTruncB :
                  (truncateBits .i8
                      (BitVec.ofNat 128 (decodeUInt endian boolRaw)) !=
                    BitVec.ofNat 128 (decodeUInt endian boolRaw)) with
              | true =>
                rw [hTruncB] at hBoolEv
                nomatch hBoolEv
              | false =>
                rw [hTruncB, bool_ite_false] at hBoolEv
                cases hB0 :
                    (UInt8.ofNat
                        (truncateBits .i8
                          (BitVec.ofNat 128
                            (decodeUInt endian boolRaw))).toNat == 0) with
                | true =>
                  rw [hB0, bool_ite_true] at hBoolEv
                  injection hBoolEv with hBv
                  rw [← hV, ← hIv, ← hBv]
                  refine ⟨⟨w, s, truncateBits w
                      (BitVec.ofNat 128 (decodeUInt endian intRaw))⟩,
                    false, rfl, rfl, rfl, ?_⟩
                  unfold ScalarVal.wf
                  rw [hEqI, hEqI]
                  exact bitVec128_beq_self _
                | false =>
                  rw [hB0, bool_ite_false] at hBoolEv
                  cases hB1 :
                      (UInt8.ofNat
                          (truncateBits .i8
                            (BitVec.ofNat 128
                              (decodeUInt endian boolRaw))).toNat == 1) with
                  | true =>
                    rw [hB1, bool_ite_true] at hBoolEv
                    injection hBoolEv with hBv
                    rw [← hV, ← hIv, ← hBv]
                    refine ⟨⟨w, s, truncateBits w
                        (BitVec.ofNat 128 (decodeUInt endian intRaw))⟩,
                      true, rfl, rfl, rfl, ?_⟩
                    unfold ScalarVal.wf
                    rw [hEqI, hEqI]
                    exact bitVec128_beq_self _
                  | false =>
                    rw [hB1, bool_ite_false] at hBoolEv
                    nomatch hBoolEv

/-- All-zero local-slot bytes decode to `(0, false)`: the local-slot analog of
`FromZeros`. -/
theorem overflowPair_localSlot_zero_decodes (endian : TargetEndian)
    (w : IntWidth) (s : Bool) :
    ∃ v, decodeVal endian (.tuple [.int w s, .bool])
      (zeroInitBytes (overflowPairLayout w).size) = .ok (some v) := by
  cases endian <;> cases w <;>
    exact ⟨.tuple [.scalar ⟨_, s, 0⟩, .bool false], rfl⟩

private theorem overflowPair_i8_encodeVal_allBytesInit (endian : TargetEndian)
    (s : Bool) :
    ∀ v bs,
      encodeVal endian (.tuple [.int .i8 s, .bool]) v = .ok bs →
      AllBytesInit bs := by
  intro v bs hEnc
  unfold encodeVal at hEnc
  cases hChk : checkVal v (.tuple [.int .i8 s, .bool]) with
  | false =>
    rw [hChk] at hEnc
    nomatch hEnc
  | true =>
    rw [hChk] at hEnc
    cases v with
    | tuple vs =>
      cases vs with
      | nil => nomatch hEnc
      | cons v0 vs1 =>
        cases v0 with
        | scalar sv =>
          cases vs1 with
          | nil => nomatch hEnc
          | cons v1 vs2 =>
            cases v1 with
            | bool b =>
              cases vs2 with
              | nil =>
                injection hEnc with hBs
                rw [← hBs]
                have hInit :
                    AllBytesInit
                      ((encodeUInt endian IntWidth.i8.byteSize sv.bits.toNat).map
                          (fun byte => AllocByte.init byte none) ++
                        [AllocByte.init (if b then 1 else 0) none] ++
                        List.replicate (IntWidth.i8.byteSize - 1)
                          AllocByte.uninit) := by
                  apply AllBytesInit_append
                  · exact AllBytesInit_append
                      (allBytesInit_map_init_none _ _) rfl
                  · rfl
                exact hInit
              | cons _ _ => nomatch hEnc
            | scalar _ | ptr _ | char _ | ordering _ | unit | enumVal _ _
            | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
            | array _ | tuple _ | bytes _ | boxPtr _ _ | vec _ _ _ =>
              nomatch hEnc
        | ptr _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _
        | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
        | array _ | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc
    | scalar _ | ptr _ | bool _ | char _ | ordering _ | unit | enumVal _ _
    | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
    | array _ | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc

private theorem overflowPair_encodeVal_uninit_of_ne_i8 (endian : TargetEndian)
    {w : IntWidth} (hw : w ≠ .i8) (s : Bool) :
    ¬ ∀ v bs,
        encodeVal endian (.tuple [.int w s, .bool]) v = .ok bs →
        AllBytesInit bs := by
  intro hEncProps
  let witness : Val := .tuple [.scalar ⟨w, s, BitVec.ofNat 128 0⟩, .bool false]
  let wbs : List AllocByte :=
    (encodeUInt endian w.byteSize 0).map (fun byte => AllocByte.init byte none) ++
      [AllocByte.init 0 none] ++
      List.replicate (w.byteSize - 1) AllocByte.uninit
  have hChk :
      checkVal (Val.tuple [Val.scalar ⟨w, s, BitVec.ofNat 128 0⟩, Val.bool false])
          (MirTy.tuple [MirTy.int w s, MirTy.bool]) = true := by
    cases w <;> cases s <;> rfl
  have hEnc : encodeVal endian (.tuple [.int w s, .bool]) witness = .ok wbs := by
    unfold encodeVal
    dsimp [witness, wbs]
    rw [hChk]
    simp [List.append_assoc]
  have hInit := hEncProps witness wbs hEnc
  have hFalse : allBytesInit wbs = false := by
    dsimp [wbs]
    rw [allBytesInit_append, allBytesInit_append, allBytesInit_map_init_none]
    cases w with
    | i8 => exact False.elim (hw rfl)
    | i16 | i32 | i64 | i128 | isize => rfl
  rw [hInit] at hFalse
  nomatch hFalse

/-- Profile v1's overflow-pair local-slot encoding (`overflowPairLayout`) has no
uninitialized padding exactly when the integer is `8` bits wide. This describes
the internal representation only; overflow pairs have no addressable layout and
are neither `IsIntoBytes` nor `IsUnaligned`. -/
theorem overflowPair_encodeVal_allBytesInit_iff (endian : TargetEndian)
    (w : IntWidth) (s : Bool) :
    (∀ v bs,
        encodeVal endian (.tuple [.int w s, .bool]) v = .ok bs →
        AllBytesInit bs) ↔
      w = .i8 := by
  constructor
  · intro h
    cases w with
    | i8 => rfl
    | i16 | i32 | i64 | i128 | isize =>
      exact False.elim
        (overflowPair_encodeVal_uninit_of_ne_i8 endian
          (fun he => by nomatch he) s h)
  · intro hw
    rw [hw]
    exact overflowPair_i8_encodeVal_allBytesInit endian s

theorem overflowPair_not_addressable (w : IntWidth) (s : Bool) :
    addressableLayoutOfTy (.tuple [.int w s, .bool]) = none :=
  rfl

/-- No overflow pair is `IntoBytes`, whatever its integer width: Rust guarantees
no tuple layout, so `(u8, bool)` cannot be transmuted to `u16`. -/
theorem overflowPair_not_isIntoBytes (endian : TargetEndian) (w : IntWidth)
    (s : Bool) : ¬ IsIntoBytes endian (.tuple [.int w s, .bool]) :=
  fun ⟨_, hLay, _⟩ => nomatch hLay

/-- No overflow pair is `Unaligned`, whatever its integer width. -/
theorem overflowPair_not_isUnaligned (w : IntWidth) (s : Bool) :
    ¬ IsUnaligned (.tuple [.int w s, .bool]) :=
  fun ⟨_, hLay, _⟩ => nomatch hLay

theorem overflowPair_not_isFromZeros (endian : TargetEndian) (w : IntWidth)
    (s : Bool) : ¬ IsFromZeros endian (.tuple [.int w s, .bool]) :=
  fun ⟨_, _, hLay, _⟩ => nomatch hLay

theorem overflowPair_not_isFromBytes (endian : TargetEndian) (w : IntWidth)
    (s : Bool) : ¬ IsFromBytes endian (.tuple [.int w s, .bool]) :=
  fun ⟨_, hLay, _⟩ => nomatch hLay

theorem overflowPair_not_isTryFromBytes (endian : TargetEndian) (w : IntWidth)
    (s : Bool) (check : List AllocByte → Bool) :
    ¬ IsTryFromBytes endian (.tuple [.int w s, .bool]) check :=
  fun ⟨_, hLay, _⟩ => nomatch hLay

/-- No overflow pair satisfies any modeled `zerocopy` trait: each requires an
addressable layout. -/
theorem overflowPair_not_validForTrait (tr : ZerocopyTrait)
    (endian : TargetEndian) (w : IntWidth) (s : Bool) :
    ¬ ValidForTrait tr endian (.tuple [.int w s, .bool]) := by
  cases tr with
  | tryFromBytes check => exact overflowPair_not_isTryFromBytes endian w s check
  | fromZeros => exact overflowPair_not_isFromZeros endian w s
  | fromBytes => exact overflowPair_not_isFromBytes endian w s
  | intoBytes => exact overflowPair_not_isIntoBytes endian w s
  | unaligned => exact overflowPair_not_isUnaligned w s

/-! ### 3g. Trait Non-Implication Separation Witnesses -/

theorem isFromBytes_not_implies_isUnaligned_witness (endian : TargetEndian) :
    IsFromBytes endian (.int .i32 false) ∧
      ¬ IsUnaligned (.int .i32 false) :=
  ⟨int_isFromBytes endian .i32 false,
   int_not_isUnaligned_of_ne_i8 (fun h => by nomatch h) false⟩

theorem isIntoBytes_not_implies_isFromBytes_witness (endian : TargetEndian) :
    IsIntoBytes endian .bool ∧ ¬ IsFromBytes endian .bool :=
  ⟨bool_isIntoBytes endian, bool_not_isFromBytes endian⟩

theorem isFromZeros_not_implies_isFromBytes_witness (endian : TargetEndian) :
    IsFromZeros endian .bool ∧ ¬ IsFromBytes endian .bool :=
  ⟨bool_isFromZeros endian, bool_not_isFromBytes endian⟩

theorem isUnaligned_not_implies_isFromBytes_witness (endian : TargetEndian) :
    IsUnaligned .bool ∧ ¬ IsFromBytes endian .bool :=
  ⟨bool_isUnaligned, bool_not_isFromBytes endian⟩

/-! ## 4. Admitted Fieldless Enums (`.enum ety`) -/

theorem zstEnum_decodeTyped_eq (endian : TargetEndian) (ety : EnumTy)
    (hAdm : enumAdmitted ety = true) (hRepr : ety.tagRepr = .zeroSized) :
    DecodeTyped endian (.enum ety) (fun v => v = .enumVal ety 0) := by
  have hLay : layoutOfTy (.enum ety) = some ⟨0, 0⟩ := by
    unfold layoutOfTy
    simp [hAdm, hRepr]
  refine ⟨⟨0, 0⟩, hLay, ?_⟩
  intro bs v hDec
  unfold decodeVal at hDec
  rw [hLay] at hDec
  dsimp only at hDec
  cases hLen : Nat.beq bs.length 0 with
  | false =>
    rw [hLen] at hDec
    nomatch hDec
  | true =>
    simp [hLen] at hDec
    unfold evalConstLit isZstEnumTy at hDec
    simp [hRepr, hAdm] at hDec
    exact hDec.symm

theorem zstEnum_isFromZeros (endian : TargetEndian) (ety : EnumTy)
    (hAdm : enumAdmitted ety = true) (hRepr : ety.tagRepr = .zeroSized) :
    IsFromZeros endian (.enum ety) := by
  have hLay : layoutOfTy (.enum ety) = some ⟨0, 0⟩ := by
    unfold layoutOfTy
    simp [hAdm, hRepr]
  refine ⟨⟨0, 0⟩, .enumVal ety 0, hLay, ?_⟩
  unfold decodeVal
  rw [hLay]
  simp
  unfold evalConstLit isZstEnumTy
  simp [hRepr, hAdm]

theorem zstEnum_isFromBytes (endian : TargetEndian) (ety : EnumTy)
    (hAdm : enumAdmitted ety = true) (hRepr : ety.tagRepr = .zeroSized) :
    IsFromBytes endian (.enum ety) := by
  have hLay : layoutOfTy (.enum ety) = some ⟨0, 0⟩ := by
    unfold layoutOfTy
    simp [hAdm, hRepr]
  refine ⟨⟨0, 0⟩, hLay, ?_⟩
  intro bs hLen _
  cases bs with
  | nil =>
    refine ⟨.enumVal ety 0, ?_⟩
    unfold decodeVal
    rw [hLay]
    simp
    unfold evalConstLit isZstEnumTy
    simp [hRepr, hAdm]
  | cons _ _ => nomatch hLen

theorem zstEnum_isIntoBytes (endian : TargetEndian) (ety : EnumTy)
    (hAdm : enumAdmitted ety = true) (hRepr : ety.tagRepr = .zeroSized) :
    IsIntoBytes endian (.enum ety) := by
  have hLay : layoutOfTy (.enum ety) = some ⟨0, 0⟩ := by
    unfold layoutOfTy
    simp [hAdm, hRepr]
  refine ⟨⟨0, 0⟩, hLay, ?_⟩
  intro v bs hEnc
  unfold encodeVal at hEnc
  cases hChk : checkVal v (.enum ety) with
  | false =>
    rw [hChk] at hEnc
    nomatch hEnc
  | true =>
    rw [hChk] at hEnc
    cases v with
    | enumVal _ variant =>
      simp [hRepr] at hEnc
      rw [← hEnc]
      exact ⟨rfl, rfl⟩
    | scalar _ | ptr _ | bool _ | char _ | ordering _ | unit | tuple _
    | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
    | array _ | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc

theorem zstEnum_isUnaligned (ety : EnumTy)
    (hAdm : enumAdmitted ety = true) (hRepr : ety.tagRepr = .zeroSized) :
    IsUnaligned (.enum ety) := by
  have hLay : layoutOfTy (.enum ety) = some ⟨0, 0⟩ := by
    unfold layoutOfTy
    simp [hAdm, hRepr]
  exact ⟨⟨0, 0⟩, hLay, rfl⟩

theorem findDiscrVariantAux_lt :
    ∀ (ds : List Nat) (idx : Nat) (bits : BitVec 128) (v : Nat),
      findDiscrVariantAux idx bits ds = some v →
      idx ≤ v ∧ v < idx + ds.length
  | [], _, _, _, h => by nomatch h
  | d :: ds, idx, bits, v, h => by
    unfold findDiscrVariantAux at h
    cases hEq : (BitVec.ofNat 128 d == bits) with
    | true =>
      rw [hEq] at h
      injection h with hV
      rw [← hV]
      refine ⟨Nat.le_refl idx, ?_⟩
      have hPos : 0 < ds.length + 1 := Nat.zero_lt_succ ds.length
      have hAdd := Nat.add_lt_add_left hPos idx
      rw [Nat.add_zero] at hAdd
      exact hAdd
    | false =>
      rw [hEq] at h
      have ⟨hGe, hLt⟩ := findDiscrVariantAux_lt ds (idx + 1) bits v h
      have hAssoc : idx + 1 + ds.length = idx + (ds.length + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 ds.length]
      rw [hAssoc] at hLt
      exact ⟨Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self idx) hGe), hLt⟩

theorem scalarEnum_isIntoBytes (endian : TargetEndian) (ety : EnumTy)
    (tagW : IntWidth) (tagS : Bool)
    (hAdm : enumAdmitted ety = true)
    (hRepr : ety.tagRepr = .scalar tagW tagS) :
    IsIntoBytes endian (.enum ety) := by
  have hLay : layoutOfTy (.enum ety) = some (intLayout tagW) := by
    unfold layoutOfTy
    simp [hAdm, hRepr]
  refine ⟨intLayout tagW, hLay, ?_⟩
  intro v bs hEnc
  unfold encodeVal at hEnc
  cases hChk : checkVal v (.enum ety) with
  | false =>
    rw [hChk] at hEnc
    nomatch hEnc
  | true =>
    rw [hChk] at hEnc
    cases v with
    | enumVal _ variant =>
      simp [hRepr] at hEnc
      cases hGet : Trusted.MirSemantics.getElem? ety.discriminants variant with
      | none =>
        rw [hGet] at hEnc
        nomatch hEnc
      | some disc =>
        rw [hGet] at hEnc
        injection hEnc with hBs
        rw [← hBs, length_map_eq, length_encodeUInt]
        have hWSize : (intLayout tagW).size = tagW.byteSize := by
          cases tagW <;> rfl
        exact ⟨hWSize.symm, allBytesInit_map_init_none _ _⟩
    | scalar _ | ptr _ | bool _ | char _ | ordering _ | unit | tuple _
    | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
    | array _ | bytes _ | boxPtr _ _ | vec _ _ _ => nomatch hEnc

theorem scalarEnum_isUnaligned_iff (ety : EnumTy) (tagW : IntWidth)
    (tagS : Bool) (hAdm : enumAdmitted ety = true)
    (hRepr : ety.tagRepr = .scalar tagW tagS) :
    IsUnaligned (.enum ety) ↔ tagW = .i8 := by
  have hLay : layoutOfTy (.enum ety) = some (intLayout tagW) := by
    unfold layoutOfTy
    simp [hAdm, hRepr]
  constructor
  · intro h
    let ⟨layout, hL, hAlign⟩ := h
    have hL' := layoutOfTy_of_addressableLayoutOfTy hL
    rw [hLay] at hL'
    injection hL' with hEq
    rw [← hEq] at hAlign
    cases tagW with
    | i8 => rfl
    | i16 | i32 | i64 | i128 | isize => nomatch hAlign
  · intro hw
    rw [hw] at hLay
    exact ⟨⟨1, 0⟩, addressableLayoutOfTy_of_not_overflowPair rfl hLay, rfl⟩

theorem scalarEnum_decodeTyped (endian : TargetEndian) (ety : EnumTy)
    (tagW : IntWidth) (tagS : Bool)
    (hAdm : enumAdmitted ety = true)
    (hRepr : ety.tagRepr = .scalar tagW tagS) :
    DecodeTyped endian (.enum ety)
      (fun v =>
        ∃ idx, idx < ety.discriminants.length ∧ v = .enumVal ety idx) := by
  have hLay : layoutOfTy (.enum ety) = some (intLayout tagW) := by
    unfold layoutOfTy
    simp [hAdm, hRepr]
  refine ⟨intLayout tagW, hLay, ?_⟩
  intro bs v hDec
  unfold decodeVal at hDec
  rw [hLay] at hDec
  dsimp only at hDec
  cases hLen : Nat.beq bs.length (intLayout tagW).size with
  | false =>
    rw [hLen] at hDec
    nomatch hDec
  | true =>
    rw [hLen] at hDec
    have hNz : Nat.beq (intLayout tagW).size 0 = false := by
      cases tagW <;> rfl
    simp [hNz] at hDec
    cases hRaw : initBytes? bs with
    | none =>
      rw [hRaw] at hDec
      nomatch hDec
    | some raw =>
      rw [hRaw] at hDec
      dsimp only at hDec
      unfold evalConstLit at hDec
      dsimp only at hDec
      rw [hRepr, hAdm] at hDec
      dsimp only at hDec
      cases hTrunc :
          (truncateBits tagW (BitVec.ofNat 128 (decodeUInt endian raw)) !=
            BitVec.ofNat 128 (decodeUInt endian raw)) with
      | true =>
        simp [hTrunc] at hDec
      | false =>
        simp [hTrunc] at hDec
        cases hFind :
            findDiscrVariant?
              (tagBitsToDiscrBits tagW tagS ety.discrWidth
                (BitVec.ofNat 128 (decodeUInt endian raw)))
              ety.discriminants with
        | none =>
          rw [hFind] at hDec
          nomatch hDec
        | some idx =>
          rw [hFind] at hDec
          injection hDec with hOpt
          injection hOpt with hV
          have ⟨_, hLt⟩ :=
            findDiscrVariantAux_lt ety.discriminants 0 _ idx hFind
          rw [Nat.zero_add] at hLt
          exact ⟨idx, hLt, hV.symm⟩

/-- Decidable `FromZeros` checker for fieldless enums: `ety` is admitted and
either `.zeroSized` or its `0` tag bit pattern resolves to a declared variant.
-/
@[expose] noncomputable def isFromZerosEnum (ety : EnumTy) : Bool :=
  enumAdmitted ety &&
    match ety.tagRepr with
    | .zeroSized => true
    | .scalar tagW tagS =>
      (findDiscrVariant?
        (tagBitsToDiscrBits tagW tagS ety.discrWidth (BitVec.ofNat 128 0))
        ety.discriminants).isSome

theorem enum_isFromZeros_iff (endian : TargetEndian) (ety : EnumTy) :
    IsFromZeros endian (.enum ety) ↔ isFromZerosEnum ety = true := by
  cases hAdm : enumAdmitted ety with
  | false =>
    have hNone : layoutOfTy (.enum ety) = none := by
      unfold layoutOfTy
      simp [hAdm]
    constructor
    · intro h
      let ⟨_, _, hLay, _⟩ := h
      have hLay' := layoutOfTy_of_addressableLayoutOfTy hLay
      rw [hNone] at hLay'
      nomatch hLay'
    · intro h
      unfold isFromZerosEnum at h
      rw [hAdm] at h
      nomatch h
  | true =>
    cases hRepr : ety.tagRepr with
    | zeroSized =>
      constructor
      · intro _
        unfold isFromZerosEnum
        rw [hAdm, hRepr]
        rfl
      · intro _
        exact zstEnum_isFromZeros endian ety hAdm hRepr
    | scalar tagW tagS =>
      have hLay : layoutOfTy (.enum ety) = some (intLayout tagW) := by
        unfold layoutOfTy
        simp [hAdm, hRepr]
      have hZeroLt :
          decodeUInt endian (List.replicate tagW.byteSize 0) <
            Nat.pow 2 tagW.bitWidth := by
        rw [decodeUInt_replicate_zero]
        exact nat_two_pow_pos _
      have hTrunc0 :
          truncateBits tagW (BitVec.ofNat 128 0) = BitVec.ofNat 128 0 :=
        truncateBits_of_lt tagW 0 (nat_two_pow_pos _)
      have hNe0 :
          (truncateBits tagW (BitVec.ofNat 128 0) != BitVec.ofNat 128 0) =
            false := by
        rw [hTrunc0]
        exact bitVec128_bne_self _
      have hSizeEq : (intLayout tagW).size = tagW.byteSize := by
        cases tagW <;> rfl
      have hWNe0 : tagW.byteSize ≠ 0 := by cases tagW <;> decide
      constructor
      · intro h
        let ⟨layout, v, hL, hDec⟩ := h
        have hL' := layoutOfTy_of_addressableLayoutOfTy hL
        rw [hLay] at hL'
        injection hL' with hEq
        rw [← hEq] at hDec
        unfold decodeVal at hDec
        rw [hLay] at hDec
        simp [initBytes?_zeroInitBytes, hSizeEq, decodeUInt_replicate_zero,
            hWNe0] at hDec
        unfold evalConstLit at hDec
        simp [hRepr, hAdm, hNe0] at hDec
        cases hFind :
            findDiscrVariant?
              (tagBitsToDiscrBits tagW tagS ety.discrWidth (BitVec.ofNat 128 0))
              ety.discriminants with
        | none =>
          rw [hFind] at hDec
          nomatch hDec
        | some _ =>
          unfold isFromZerosEnum
          simp [hAdm, hRepr, hFind]
      · intro h
        unfold isFromZerosEnum at h
        rw [hAdm, hRepr] at h
        dsimp only at h
        cases hFind :
            findDiscrVariant?
              (tagBitsToDiscrBits tagW tagS ety.discrWidth (BitVec.ofNat 128 0))
              ety.discriminants with
        | none =>
          rw [hFind] at h
          nomatch h
        | some idx =>
          refine ⟨intLayout tagW, .enumVal ety idx,
            addressableLayoutOfTy_of_not_overflowPair rfl hLay, ?_⟩
          unfold decodeVal
          rw [hLay]
          simp [initBytes?_zeroInitBytes, hSizeEq, decodeUInt_replicate_zero,
              hWNe0]
          unfold evalConstLit
          simp [hRepr, hAdm, hNe0, hFind]

/-- Check whether raw tag integer `k` decodes to some variant of `ety`. -/
@[expose] noncomputable def checkTagBitsCovered (tagW : IntWidth) (tagS : Bool)
    (ety : EnumTy) (k : Nat) : Bool :=
  (findDiscrVariant?
    (tagBitsToDiscrBits tagW tagS ety.discrWidth (BitVec.ofNat 128 k))
    ety.discriminants).isSome

/-- Scan `[idx, idx + rem)` upward so incomplete enums fail fast. -/
@[expose] noncomputable def checkAllTagBitsFrom (tagW : IntWidth) (tagS : Bool)
    (ety : EnumTy) (idx : Nat) : Nat → Bool
  | 0 => true
  | rem + 1 =>
    checkTagBitsCovered tagW tagS ety idx &&
      checkAllTagBitsFrom tagW tagS ety (idx + 1) rem

/-- Decidable `FromBytes` checker for admitted fieldless enums: accepts
`.zeroSized` enums and exhaustive `.scalar` enums whose tag width is at most
`16` bits (`u8`/`i8`/`u16`/`i16`). -/
@[expose] noncomputable def isFromBytesEnum (ety : EnumTy) : Bool :=
  enumAdmitted ety &&
    match ety.tagRepr with
    | .zeroSized => true
    | .scalar tagW tagS =>
      Nat.ble tagW.bitWidth 16 &&
        checkAllTagBitsFrom tagW tagS ety 0 (Nat.pow 2 tagW.bitWidth)

theorem checkAllTagBitsFrom_spec (tagW : IntWidth) (tagS : Bool)
    (ety : EnumTy) :
    ∀ (rem idx k : Nat),
      checkAllTagBitsFrom tagW tagS ety idx rem = true →
      idx ≤ k →
      k < idx + rem →
      checkTagBitsCovered tagW tagS ety k = true
  | 0, idx, k, _, hGe, hLt => by
    rw [Nat.add_zero] at hLt
    exact False.elim (Nat.not_lt_of_ge hGe hLt)
  | rem + 1, idx, k, h, hGe, hLt => by
    unfold checkAllTagBitsFrom at h
    have hHead := bool_and_left h
    have hTail := bool_and_right h
    cases hEq : Nat.beq k idx with
    | true =>
      have hk : k = idx := nat_eq_of_beq hEq
      rw [hk]
      exact hHead
    | false =>
      have hkNe : k ≠ idx := fun hEqProp => by
        rw [hEqProp, nat_beq_refl] at hEq
        nomatch hEq
      have hkLt : idx < k := Nat.lt_of_le_of_ne hGe (fun he => hkNe he.symm)
      have hAssoc : idx + (rem + 1) = (idx + 1) + rem := by
        rw [Nat.add_assoc, Nat.add_comm 1 rem]
      rw [hAssoc] at hLt
      exact checkAllTagBitsFrom_spec tagW tagS ety rem (idx + 1) k hTail hkLt hLt

theorem isFromBytesEnum_sound (endian : TargetEndian) (ety : EnumTy)
    (h : isFromBytesEnum ety = true) : IsFromBytes endian (.enum ety) := by
  unfold isFromBytesEnum at h
  have hAdm := bool_and_left h
  have hBody := bool_and_right h
  cases hRepr : ety.tagRepr with
  | zeroSized =>
    exact zstEnum_isFromBytes endian ety hAdm hRepr
  | scalar tagW tagS =>
    rw [hRepr] at hBody
    have hScan := bool_and_right hBody
    have hLay : layoutOfTy (.enum ety) = some (intLayout tagW) := by
      unfold layoutOfTy
      simp [hAdm, hRepr]
    refine ⟨intLayout tagW, hLay, ?_⟩
    intro bs hLen hInit
    have ⟨raw, hRaw, hRawLen⟩ := initBytes?_isSome_of_allBytesInit bs hInit
    have hDecLt : decodeUInt endian raw < Nat.pow 2 tagW.bitWidth := by
      have h1 := decodeUInt_lt endian raw
      have hWSize : (intLayout tagW).size = tagW.byteSize := by
        cases tagW <;> rfl
      rw [hRawLen, hLen, hWSize, intWidth_bitWidth_eq] at h1
      exact h1
    have hCov :
        checkTagBitsCovered tagW tagS ety (decodeUInt endian raw) = true := by
      have h0Le : 0 ≤ decodeUInt endian raw := Nat.zero_le _
      have hLt0 : decodeUInt endian raw < 0 + Nat.pow 2 tagW.bitWidth := by
        rw [Nat.zero_add]
        exact hDecLt
      exact checkAllTagBitsFrom_spec tagW tagS ety (Nat.pow 2 tagW.bitWidth)
        0 (decodeUInt endian raw) hScan h0Le hLt0
    unfold checkTagBitsCovered at hCov
    cases hFind :
        findDiscrVariant?
          (tagBitsToDiscrBits tagW tagS ety.discrWidth
            (BitVec.ofNat 128 (decodeUInt endian raw)))
          ety.discriminants with
    | none =>
      rw [hFind] at hCov
      nomatch hCov
    | some idx =>
      have hTrunc :
          truncateBits tagW (BitVec.ofNat 128 (decodeUInt endian raw)) =
            BitVec.ofNat 128 (decodeUInt endian raw) :=
        truncateBits_of_lt tagW _ hDecLt
      have hNe :
          (truncateBits tagW (BitVec.ofNat 128 (decodeUInt endian raw)) !=
            BitVec.ofNat 128 (decodeUInt endian raw)) = false := by
        rw [hTrunc]
        exact bitVec128_bne_self _
      have hLayBeq : Nat.beq bs.length (intLayout tagW).size = true := by
        rw [hLen]
        exact nat_beq_refl _
      have hNz : Nat.beq (intLayout tagW).size 0 = false := by
        cases tagW <;> rfl
      refine ⟨.enumVal ety idx, ?_⟩
      unfold decodeVal
      rw [hLay]
      simp [hLayBeq, hNz, hRaw]
      unfold evalConstLit
      simp [hRepr, hAdm, hNe, hFind]

theorem scalarEnum_not_isFromBytes_of_invalid_tag (endian : TargetEndian)
    (ety : EnumTy) (tagW : IntWidth) (tagS : Bool)
    (hAdm : enumAdmitted ety = true)
    (hRepr : ety.tagRepr = .scalar tagW tagS)
    (k : Nat) (hk : k < Nat.pow 2 tagW.bitWidth)
    (hNone :
      findDiscrVariant?
        (tagBitsToDiscrBits tagW tagS ety.discrWidth (BitVec.ofNat 128 k))
        ety.discriminants = none) :
    ¬ IsFromBytes endian (.enum ety) := by
  intro h
  have hLay : layoutOfTy (.enum ety) = some (intLayout tagW) := by
    unfold layoutOfTy
    simp [hAdm, hRepr]
  let ⟨layout, hL, hDec⟩ := h
  have hL' := layoutOfTy_of_addressableLayoutOfTy hL
  rw [hLay] at hL'
  injection hL' with hEq
  rw [← hEq] at hDec
  let raw : List UInt8 := encodeUInt endian tagW.byteSize k
  let bs : List AllocByte := raw.map (fun b => AllocByte.init b none)
  have hWSize : (intLayout tagW).size = tagW.byteSize := by
    cases tagW <;> rfl
  have hBsLen : bs.length = (intLayout tagW).size := by
    dsimp [bs, raw]
    rw [length_map_eq, length_encodeUInt, hWSize]
  have hBsInit : AllBytesInit bs := allBytesInit_map_init_none _ _
  have ⟨_, hv⟩ := hDec bs hBsLen hBsInit
  have hInitBs : initBytes? bs = some raw := by
    have hMapId : List.map id raw = raw := list_map_id raw
    have h1 := initBytes?_map_init_none id raw
    rw [hMapId] at h1
    exact h1
  have hDecRaw : decodeUInt endian raw = k := by
    dsimp [raw]
    rw [← intWidth_bitWidth_eq] at hk
    exact decodeUInt_encodeUInt_lt endian tagW.byteSize k hk
  have hTrunc :
      truncateBits tagW (BitVec.ofNat 128 k) = BitVec.ofNat 128 k :=
    truncateBits_of_lt tagW k hk
  have hNe :
      (truncateBits tagW (BitVec.ofNat 128 k) != BitVec.ofNat 128 k) =
        false := by
    rw [hTrunc]
    exact bitVec128_bne_self _
  have hLayBeq : Nat.beq bs.length (intLayout tagW).size = true := by
    rw [hBsLen]
    exact nat_beq_refl _
  have hNz : Nat.beq (intLayout tagW).size 0 = false := by
    cases tagW <;> rfl
  unfold decodeVal at hv
  rw [hLay] at hv
  simp [hLayBeq, hNz, hInitBs, hDecRaw] at hv
  unfold evalConstLit at hv
  simp [hRepr, hAdm, hNe, hNone] at hv

/-- Construct the contiguous integer list `[idx, idx + n)` via `@Nat.rec`
(`0` `._unsafe_rec` auxiliaries). -/
@[expose] def natRangeFrom (idx n : Nat) : List Nat :=
  @Nat.rec (fun _ => Nat → List Nat)
    (fun _ => [])
    (fun _ ih i => i :: ih (i + 1))
    n idx

theorem natRangeFrom_zero (idx : Nat) :
    natRangeFrom idx 0 = [] := rfl

theorem natRangeFrom_succ (idx n : Nat) :
    natRangeFrom idx (n + 1) = idx :: natRangeFrom (idx + 1) n := rfl

theorem length_natRangeFrom :
    ∀ n idx : Nat, (natRangeFrom idx n).length = n
  | 0, _ => rfl
  | n + 1, idx => by
    rw [natRangeFrom_succ]
    exact congrArg Nat.succ (length_natRangeFrom n (idx + 1))

theorem natNotElem_natRangeFrom (x : Nat) :
    ∀ (n lo : Nat), x < lo → natNotElem x (natRangeFrom lo n) = true
  | 0, _, _ => rfl
  | n + 1, lo, hx => by
    rw [natRangeFrom_succ]
    unfold natNotElem
    have hNe : Nat.beq x lo = false := by
      cases hEq : Nat.beq x lo with
      | false => rfl
      | true =>
        have hEqNat : x = lo := nat_eq_of_beq hEq
        rw [hEqNat] at hx
        exact False.elim (Nat.lt_irrefl lo hx)
    have ih := natNotElem_natRangeFrom x n (lo + 1) (Nat.lt_succ_of_lt hx)
    simp [hNe, ih]

theorem natListPairwiseNe_natRangeFrom :
    ∀ n lo : Nat, natListPairwiseNe (natRangeFrom lo n) = true
  | 0, _ => rfl
  | n + 1, lo => by
    rw [natRangeFrom_succ]
    unfold natListPairwiseNe
    have hHead := natNotElem_natRangeFrom lo n (lo + 1) (Nat.lt_succ_self lo)
    have hTail := natListPairwiseNe_natRangeFrom n (lo + 1)
    simp [hHead, hTail]

theorem listAll_natRangeFrom (P : Nat → Bool) :
    ∀ (n lo : Nat),
      (∀ k : Nat, lo ≤ k → k < lo + n → P k = true) →
      (natRangeFrom lo n).all P = true
  | 0, _, _ => rfl
  | n + 1, lo, h => by
    rw [natRangeFrom_succ]
    unfold List.all
    have h0 : P lo = true := by
      have hLt : lo < lo + (n + 1) := by
        have hPos : 0 < n + 1 := Nat.zero_lt_succ n
        have hA := Nat.add_lt_add_left hPos lo
        rw [Nat.add_zero] at hA
        exact hA
      exact h lo (Nat.le_refl lo) hLt
    have ih : (natRangeFrom (lo + 1) n).all P = true :=
      listAll_natRangeFrom P n (lo + 1) (fun k hk1 hk2 => by
        have hAssoc : (lo + 1) + n = lo + (n + 1) := by
          rw [Nat.add_assoc, Nat.add_comm 1 n]
        rw [hAssoc] at hk2
        exact h k (Nat.le_trans (Nat.le_succ lo) hk1) hk2)
    change (P lo && (natRangeFrom (lo + 1) n).all P) = true
    rw [h0, ih]
    rfl

theorem findDiscrVariantAux_natRangeFrom (x : Nat) :
    ∀ (n lo idx : Nat),
      lo ≤ x →
      x < lo + n →
      (findDiscrVariantAux idx (BitVec.ofNat 128 x)
        (natRangeFrom lo n)).isSome = true
  | 0, lo, _, hLo, hHi => by
    rw [Nat.add_zero] at hHi
    exact False.elim (Nat.not_lt_of_ge hLo hHi)
  | n + 1, lo, idx, hLo, hHi => by
    rw [natRangeFrom_succ]
    unfold findDiscrVariantAux
    cases hEq : (BitVec.ofNat 128 lo == BitVec.ofNat 128 x) with
    | true => rfl
    | false =>
      have hxNe : lo ≠ x := fun hE => by
        rw [hE, bitVec128_beq_self] at hEq
        nomatch hEq
      have hSuccLe : lo + 1 ≤ x := Nat.lt_of_le_of_ne hLo hxNe
      have hAssoc : lo + (n + 1) = (lo + 1) + n := by
        rw [Nat.add_assoc, Nat.add_comm n 1]
      rw [hAssoc] at hHi
      exact findDiscrVariantAux_natRangeFrom x n (lo + 1) (idx + 1) hSuccLe hHi

theorem checkAllTagBitsFrom_intro (tagW : IntWidth) (tagS : Bool)
    (ety : EnumTy) :
    ∀ (rem idx : Nat),
      (∀ k : Nat, idx ≤ k → k < idx + rem →
        checkTagBitsCovered tagW tagS ety k = true) →
      checkAllTagBitsFrom tagW tagS ety idx rem = true
  | 0, _, _ => rfl
  | rem + 1, idx, h => by
    unfold checkAllTagBitsFrom
    have hHead : checkTagBitsCovered tagW tagS ety idx = true := by
      have hLt : idx < idx + (rem + 1) := by
        have hPos : 0 < rem + 1 := Nat.zero_lt_succ rem
        have hA := Nat.add_lt_add_left hPos idx
        rw [Nat.add_zero] at hA
        exact hA
      exact h idx (Nat.le_refl idx) hLt
    have hTail : checkAllTagBitsFrom tagW tagS ety (idx + 1) rem = true :=
      checkAllTagBitsFrom_intro tagW tagS ety rem (idx + 1) (fun k hk1 hk2 => by
        have hAssoc : (idx + 1) + rem = idx + (rem + 1) := by
          rw [Nat.add_assoc, Nat.add_comm 1 rem]
        rw [hAssoc] at hk2
        exact h k (Nat.le_trans (Nat.le_succ idx) hk1) hk2)
    rw [hHead, hTail]
    rfl

private theorem tagBitsToDiscrBits_u8_of_lt (discrW : IntWidth) (k : Nat)
    (hk : k < Nat.pow 2 8) :
    tagBitsToDiscrBits .i8 false discrW (BitVec.ofNat 128 k) =
      BitVec.ofNat 128 k := by
  have h8Le : IntWidth.i8.bitWidth ≤ discrW.bitWidth := by
    cases discrW <;> decide
  have hPowLe : Nat.pow 2 8 ≤ Nat.pow 2 discrW.bitWidth :=
    Nat.pow_le_pow_right (by decide : 0 < 2) h8Le
  have hkDiscr : k < Nat.pow 2 discrW.bitWidth := Nat.lt_of_lt_of_le hk hPowLe
  unfold tagBitsToDiscrBits
  dsimp only
  rw [bool_ite_false, truncateBits_of_lt .i8 k hk,
      truncateBits_of_lt discrW k hkDiscr]

/-- Any `EnumTy` with `tagRepr = .scalar .i8 false` and full discriminant
table `natRangeFrom 0 256` is admitted (`enumAdmitted = true`). -/
theorem u8ExhaustiveEnum_enumAdmitted (ety : EnumTy)
    (hRepr : ety.tagRepr = .scalar .i8 false)
    (hDiscrs : ety.discriminants = natRangeFrom 0 256) :
    enumAdmitted ety = true := by
  have h8Le : IntWidth.i8.bitWidth ≤ ety.discrWidth.bitWidth := by
    cases ety.discrWidth <;> decide
  have hPowLe : Nat.pow 2 8 ≤ Nat.pow 2 ety.discrWidth.bitWidth :=
    Nat.pow_le_pow_right (by decide : 0 < 2) h8Le
  have hAllBlt :
      (natRangeFrom 0 256).all
          (fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth)) = true :=
    listAll_natRangeFrom _ 256 0 (fun k _ hk => by
      have hk256 : k < Nat.pow 2 8 := hk
      have hkW : k < Nat.pow 2 ety.discrWidth.bitWidth :=
        Nat.lt_of_lt_of_le hk256 hPowLe
      exact Nat.blt_eq.mpr hkW)
  have hAllTag :
      (natRangeFrom 0 256).all (fun d =>
        let dBits := BitVec.ofNat 128 d
        tagBitsToDiscrBits .i8 false ety.discrWidth
          (truncateBits .i8 dBits) == dBits) = true :=
    listAll_natRangeFrom _ 256 0 (fun k _ hk => by
      have hk256 : k < Nat.pow 2 8 := hk
      dsimp only
      rw [truncateBits_of_lt .i8 k hk256,
          tagBitsToDiscrBits_u8_of_lt ety.discrWidth k hk256]
      exact bitVec128_beq_self _)
  have hLenBlt :
      Nat.blt (natRangeFrom 0 256).length (Nat.pow 2 32) = true := by
    rw [length_natRangeFrom]
    decide
  have hNonEmpty : (natRangeFrom 0 256).isEmpty = false := by
    rw [natRangeFrom_succ]
    rfl
  unfold enumAdmitted
  rw [hDiscrs, hRepr]
  simp [hNonEmpty, hLenBlt, hAllBlt, natListPairwiseNe_natRangeFrom, hAllTag]

/-- Any `EnumTy` with `tagRepr = .scalar .i8 false` and `natRangeFrom 0 256`
passes the decidable `isFromBytesEnum` checker in `O(1)` kernel depth. -/
theorem u8ExhaustiveEnum_isFromBytesEnum (ety : EnumTy)
    (hRepr : ety.tagRepr = .scalar .i8 false)
    (hDiscrs : ety.discriminants = natRangeFrom 0 256) :
    isFromBytesEnum ety = true := by
  have hAdm := u8ExhaustiveEnum_enumAdmitted ety hRepr hDiscrs
  have hScan :
      checkAllTagBitsFrom .i8 false ety 0 (Nat.pow 2 IntWidth.i8.bitWidth) =
        true :=
    checkAllTagBitsFrom_intro .i8 false ety 256 0 (fun k _ hk => by
      have hk256 : k < Nat.pow 2 8 := hk
      unfold checkTagBitsCovered
      rw [hDiscrs, tagBitsToDiscrBits_u8_of_lt ety.discrWidth k hk256]
      exact findDiscrVariantAux_natRangeFrom k 256 0 0 (Nat.zero_le k) hk)
  unfold isFromBytesEnum
  rw [hAdm, hRepr]
  simp [hScan]
  decide

/-! ## 4b. Exact `TryFromBytes` Validators

Concrete byte validators (models of `TryFromBytes::is_safe`) for every
addressable Profile v1 type, each proved exact (`IsExactTryFromBytes`), plus an
exact recognizer for overflow pairs' local-slot bytes. Exactness rules out the
validator that rejects every candidate of an inhabited type, and soundness rules
out the validator that accepts every candidate of a type that is not
`FromBytes` (`isTryFromBytes_true_iff_isFromBytes`). -/

/-- Validator that reads an initialized byte sequence as an unsigned integer in
byte order `endian` and accepts when `valid` holds for it. -/
@[expose] noncomputable def scalarCheck (endian : TargetEndian)
    (valid : Nat → Bool) (bs : List AllocByte) : Bool :=
  match initBytes? bs with
  | some raw => valid (decodeUInt endian raw)
  | none => false

/-- `bool` byte value test: the byte is `0` or `1`. -/
@[expose] def boolValid (n : Nat) : Bool :=
  UInt8.ofNat n == 0 || UInt8.ofNat n == 1

/-- `Ordering` tag test: the `i8` tag is `-1` (`255`), `0`, or `1`. -/
@[expose] def orderingValid (n : Nat) : Bool :=
  Nat.beq n 255 || Nat.beq n 0 || Nat.beq n 1

/-- Fieldless-enum tag test: the tag bits resolve to a declared discriminant. -/
@[expose] noncomputable def enumTagValid (ety : EnumTy) (tagW : IntWidth)
    (tagS : Bool) (n : Nat) : Bool :=
  (findDiscrVariant? (tagBitsToDiscrBits tagW tagS ety.discrWidth
    (BitVec.ofNat 128 n)) ety.discriminants).isSome

/-- Local-slot overflow-pair recognizer: the `bool` byte after the integer bytes
is `0` or `1`. On initialized local-slot bytes the integer bytes are always
valid, and the padding bytes are unconstrained. -/
@[expose] noncomputable def overflowPairCheck (endian : TargetEndian)
    (w : IntWidth) (bs : List AllocByte) : Bool :=
  match initBytes? ((bs.drop w.byteSize).take 1) with
  | some raw => boolValid (decodeUInt endian raw)
  | none => false

theorem isExactTryFromBytes_scalarCheck (endian : TargetEndian) (ty : MirTy)
    (layout : LayoutData) (valid : Nat → Bool)
    (hLay : addressableLayoutOfTy ty = some layout)
    (hIff : ∀ bs raw,
      bs.length = layout.size →
      initBytes? bs = some raw →
      ((∃ v, decodeVal endian ty bs = .ok (some v)) ↔
        valid (decodeUInt endian raw) = true)) :
    IsExactTryFromBytes endian ty (scalarCheck endian valid) := by
  refine ⟨layout, hLay, fun bs ⟨l, hL, hLen, hInit⟩ => ?_⟩
  have hEq := layoutOfTy_unique hL (layoutOfTy_of_addressableLayoutOfTy hLay)
  subst hEq
  have ⟨raw, hRaw, _⟩ := initBytes?_isSome_of_allBytesInit bs hInit
  have hChk : scalarCheck endian valid bs = valid (decodeUInt endian raw) := by
    unfold scalarCheck
    rw [hRaw]
  rw [hChk]
  constructor
  · intro hV
    let ⟨v, hv⟩ := (hIff bs raw hLen hRaw).2 hV
    exact ⟨l, v, hL, hLen, hv⟩
  · intro ⟨_, v, _, _, hv⟩
    exact (hIff bs raw hLen hRaw).1 ⟨v, hv⟩

private theorem decodeUInt_lt_of_length (endian : TargetEndian)
    {raw : List UInt8} {k : Nat} (h : raw.length = k) :
    decodeUInt endian raw < Nat.pow 2 (k * 8) := by
  rw [← h]
  exact decodeUInt_lt endian raw

private theorem bv128_toNat_ofNat_of_lt {n k : Nat} (h : n < Nat.pow 2 k)
    (hk : k ≤ 128) : (BitVec.ofNat 128 n).toNat = n := by
  rw [bv_toNat_ofNat]
  exact Nat.mod_eq_of_lt
    (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hk))

private theorem except_ok_ne_error {α : Type} {a : α} {k : FaultKind} :
    (Except.ok a : Except FaultKind α) ≠ .error k :=
  fun h => nomatch h

theorem evalConstLit_int_ok (w : IntWidth) (s : Bool) (n : Nat)
    (hn : n < Nat.pow 2 w.bitWidth) :
    evalConstLit (.int w s) (.scalar (BitVec.ofNat 128 n)) =
      .ok (.scalar ⟨w, s, BitVec.ofNat 128 n⟩) := by
  unfold evalConstLit
  dsimp only
  rw [truncateBits_of_lt w n hn, bitVec128_bne_self]
  rfl

theorem evalConstLit_bool_ok_iff (n : Nat) (hn : n < Nat.pow 2 8) :
    (∃ v, evalConstLit .bool (.scalar (BitVec.ofNat 128 n)) = .ok v) ↔
      boolValid n = true := by
  have hT := truncateBits_of_lt .i8 n hn
  have hN : (BitVec.ofNat 128 n).toNat = n :=
    bv128_toNat_ofNat_of_lt hn (by decide)
  unfold evalConstLit boolValid
  dsimp only
  rw [hT, bitVec128_bne_self, bool_ite_false, hN]
  cases h0 : (UInt8.ofNat n == 0) with
  | true =>
    rw [bool_ite_true]
    exact ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩
  | false =>
    rw [bool_ite_false]
    cases h1 : (UInt8.ofNat n == 1) with
    | true =>
      rw [bool_ite_true]
      exact ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩
    | false =>
      rw [bool_ite_false]
      exact ⟨(fun ⟨_, h⟩ => nomatch h), (fun h => nomatch h)⟩

theorem evalConstLit_char_ok_iff (n : Nat) (hn : n < Nat.pow 2 32) :
    (∃ v, evalConstLit .char (.scalar (BitVec.ofNat 128 n)) = .ok v) ↔
      isUnicodeScalar n = true := by
  have hT := truncateBits_of_lt .i32 n hn
  have hN : (BitVec.ofNat 128 n).toNat = n :=
    bv128_toNat_ofNat_of_lt hn (by decide)
  unfold evalConstLit
  dsimp only
  rw [hT, bitVec128_bne_self, bool_ite_false, hN]
  cases h : isUnicodeScalar n with
  | true =>
    rw [bool_ite_true]
    exact ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩
  | false =>
    rw [bool_ite_false]
    exact ⟨(fun ⟨_, h⟩ => nomatch h), (fun h => nomatch h)⟩

theorem evalConstLit_ordering_ok_iff (n : Nat) (hn : n < Nat.pow 2 8) :
    (∃ v, evalConstLit .ordering (.scalar (BitVec.ofNat 128 n)) = .ok v) ↔
      orderingValid n = true := by
  have hT := truncateBits_of_lt .i8 n hn
  have hN : (BitVec.ofNat 128 n).toNat = n :=
    bv128_toNat_ofNat_of_lt hn (by decide)
  unfold evalConstLit orderingValid
  dsimp only
  rw [hT, bitVec128_bne_self, bool_ite_false, hN]
  unfold orderingOfTagBits
  cases h255 : Nat.beq n 255 with
  | true =>
    rw [bool_ite_true]
    exact ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩
  | false =>
    rw [bool_ite_false]
    cases h0 : Nat.beq n 0 with
    | true =>
      rw [bool_ite_true]
      exact ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩
    | false =>
      rw [bool_ite_false]
      cases h1 : Nat.beq n 1 with
      | true =>
        rw [bool_ite_true]
        exact ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩
      | false =>
        rw [bool_ite_false]
        exact ⟨(fun ⟨_, h⟩ => nomatch h), (fun h => nomatch h)⟩

theorem evalConstLit_scalarEnum_ok_iff (ety : EnumTy) (tagW : IntWidth)
    (tagS : Bool) (hAdm : enumAdmitted ety = true)
    (hRepr : ety.tagRepr = .scalar tagW tagS) (n : Nat)
    (hn : n < Nat.pow 2 tagW.bitWidth) :
    (∃ v, evalConstLit (.enum ety) (.scalar (BitVec.ofNat 128 n)) = .ok v) ↔
      enumTagValid ety tagW tagS n = true := by
  have hT := truncateBits_of_lt tagW n hn
  have hCond :
      (!enumAdmitted ety ||
          truncateBits tagW (BitVec.ofNat 128 n) != BitVec.ofNat 128 n) =
        false := by
    rw [hAdm, hT, bitVec128_bne_self]
    rfl
  unfold evalConstLit enumTagValid
  dsimp only
  rw [hRepr]
  dsimp only
  rw [hCond, bool_ite_false]
  cases h : findDiscrVariant?
      (tagBitsToDiscrBits tagW tagS ety.discrWidth (BitVec.ofNat 128 n))
      ety.discriminants with
  | some _ => exact ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩
  | none => exact ⟨(fun ⟨_, h⟩ => nomatch h), (fun h => nomatch h)⟩

/-- Reduces `∃ v, decodeVal … = .ok (some v)` on a decoder result of the form
`match e with | .ok v => .ok (some v) | .error k => .error k`. -/
private theorem exists_match_ok_iff (e : Except FaultKind Val) :
    (∃ v : Val, (match e with
      | .ok v => (.ok (some v) : Except FaultKind (Option Val))
      | .error k => .error k) = .ok (some v)) ↔ ∃ v : Val, e = .ok v := by
  cases e with
  | ok v => exact ⟨fun _ => ⟨v, rfl⟩, fun _ => ⟨v, rfl⟩⟩
  | error k => exact ⟨(fun ⟨_, h⟩ => nomatch h), (fun ⟨_, h⟩ => nomatch h)⟩

theorem bool_isExactTryFromBytes (endian : TargetEndian) :
    IsExactTryFromBytes endian .bool (scalarCheck endian boolValid) := by
  refine isExactTryFromBytes_scalarCheck endian .bool ⟨1, 0⟩ boolValid rfl ?_
  intro bs raw hLen hRaw
  have hRawLen : raw.length = 1 :=
    (allBytesInit_of_initBytes?_eq_some hRaw).2.trans hLen
  have hL : Nat.beq bs.length 1 = true := by rw [hLen]; rfl
  have hDec :
      decodeVal endian .bool bs =
        match evalConstLit .bool
            (.scalar (BitVec.ofNat 128 (decodeUInt endian raw))) with
        | .ok v => .ok (some v)
        | .error k => .error k := by
    unfold decodeVal layoutOfTy
    dsimp only
    rw [hL, hRaw]
    rfl
  rw [hDec, exists_match_ok_iff]
  exact evalConstLit_bool_ok_iff _ (decodeUInt_lt_of_length endian hRawLen)

theorem char_isExactTryFromBytes (endian : TargetEndian) :
    IsExactTryFromBytes endian .char (scalarCheck endian isUnicodeScalar) := by
  refine isExactTryFromBytes_scalarCheck endian .char ⟨4, 2⟩ isUnicodeScalar
    rfl ?_
  intro bs raw hLen hRaw
  have hRawLen : raw.length = 4 :=
    (allBytesInit_of_initBytes?_eq_some hRaw).2.trans hLen
  have hL : Nat.beq bs.length 4 = true := by rw [hLen]; rfl
  have hDec :
      decodeVal endian .char bs =
        match evalConstLit .char
            (.scalar (BitVec.ofNat 128 (decodeUInt endian raw))) with
        | .ok v => .ok (some v)
        | .error k => .error k := by
    unfold decodeVal layoutOfTy
    dsimp only
    rw [hL, hRaw]
    rfl
  rw [hDec, exists_match_ok_iff]
  exact evalConstLit_char_ok_iff _ (decodeUInt_lt_of_length endian hRawLen)

theorem ordering_isExactTryFromBytes (endian : TargetEndian) :
    IsExactTryFromBytes endian .ordering (scalarCheck endian orderingValid) := by
  refine isExactTryFromBytes_scalarCheck endian .ordering ⟨1, 0⟩ orderingValid
    rfl ?_
  intro bs raw hLen hRaw
  have hRawLen : raw.length = 1 :=
    (allBytesInit_of_initBytes?_eq_some hRaw).2.trans hLen
  have hL : Nat.beq bs.length 1 = true := by rw [hLen]; rfl
  have hDec :
      decodeVal endian .ordering bs =
        match evalConstLit .ordering
            (.scalar (BitVec.ofNat 128 (decodeUInt endian raw))) with
        | .ok v => .ok (some v)
        | .error k => .error k := by
    unfold decodeVal layoutOfTy
    dsimp only
    rw [hL, hRaw]
    rfl
  rw [hDec, exists_match_ok_iff]
  exact evalConstLit_ordering_ok_iff _ (decodeUInt_lt_of_length endian hRawLen)

theorem scalarEnum_isExactTryFromBytes (endian : TargetEndian) (ety : EnumTy)
    (tagW : IntWidth) (tagS : Bool)
    (hAdm : enumAdmitted ety = true)
    (hRepr : ety.tagRepr = .scalar tagW tagS) :
    IsExactTryFromBytes endian (.enum ety)
      (scalarCheck endian (enumTagValid ety tagW tagS)) := by
  have hLay : layoutOfTy (.enum ety) = some (intLayout tagW) := by
    unfold layoutOfTy
    simp [hAdm, hRepr]
  refine isExactTryFromBytes_scalarCheck endian (.enum ety) (intLayout tagW)
    (enumTagValid ety tagW tagS)
    (addressableLayoutOfTy_of_not_overflowPair rfl hLay) ?_
  intro bs raw hLen hRaw
  have hSize : (intLayout tagW).size = tagW.byteSize := by cases tagW <;> rfl
  have hRawLen : raw.length = tagW.byteSize :=
    (allBytesInit_of_initBytes?_eq_some hRaw).2.trans (hLen.trans hSize)
  have hL : Nat.beq bs.length (intLayout tagW).size = true := by
    rw [hLen]
    exact nat_beq_refl _
  have hNz : Nat.beq (intLayout tagW).size 0 = false := by cases tagW <;> rfl
  have hDec :
      decodeVal endian (.enum ety) bs =
        match evalConstLit (.enum ety)
            (.scalar (BitVec.ofNat 128 (decodeUInt endian raw))) with
        | .ok v => .ok (some v)
        | .error k => .error k := by
    unfold decodeVal
    rw [hLay]
    dsimp only
    rw [hL, hNz, hRaw]
    rfl
  rw [hDec, exists_match_ok_iff]
  have hLt : decodeUInt endian raw < Nat.pow 2 tagW.bitWidth := by
    rw [← intWidth_bitWidth_eq]
    exact decodeUInt_lt_of_length endian hRawLen
  exact evalConstLit_scalarEnum_ok_iff ety tagW tagS hAdm hRepr _ hLt

theorem int_isExactTryFromBytes (endian : TargetEndian) (w : IntWidth)
    (s : Bool) : IsExactTryFromBytes endian (.int w s) (fun _ => true) :=
  isFromBytes_implies_isExactTryFromBytes endian _ (int_isFromBytes endian w s)

theorem unit_isExactTryFromBytes (endian : TargetEndian) :
    IsExactTryFromBytes endian .unit (fun _ => true) :=
  isFromBytes_implies_isExactTryFromBytes endian _ (unit_isFromBytes endian)

theorem zstEnum_isExactTryFromBytes (endian : TargetEndian) (ety : EnumTy)
    (hAdm : enumAdmitted ety = true) (hRepr : ety.tagRepr = .zeroSized) :
    IsExactTryFromBytes endian (.enum ety) (fun _ => true) :=
  isFromBytes_implies_isExactTryFromBytes endian _
    (zstEnum_isFromBytes endian ety hAdm hRepr)

/-- `!` has no valid instance, so the exact validator rejects everything. -/
theorem never_isExactTryFromBytes (endian : TargetEndian) :
    IsExactTryFromBytes endian .never (fun _ => false) :=
  ⟨⟨0, 0⟩, rfl, fun _ _ =>
    ⟨(fun h => nomatch h), (fun ⟨_, _, _, _, hDec⟩ => nomatch hDec)⟩⟩

private theorem allBytesInit_take :
    ∀ (k : Nat) (bs : List AllocByte), AllBytesInit bs → AllBytesInit (bs.take k)
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | _ + 1, .uninit :: _, h => nomatch h
  | k + 1, .init _ _ :: rest, h => allBytesInit_take k rest h

private theorem allBytesInit_drop :
    ∀ (k : Nat) (bs : List AllocByte), AllBytesInit bs → AllBytesInit (bs.drop k)
  | 0, _, h => h
  | _ + 1, [], _ => rfl
  | _ + 1, .uninit :: _, h => nomatch h
  | k + 1, .init _ _ :: rest, h => allBytesInit_drop k rest h

private theorem length_take_of_le {α : Type} :
    ∀ (k : Nat) (xs : List α), k ≤ xs.length → (xs.take k).length = k
  | 0, _, _ => rfl
  | _ + 1, [], h => nomatch h
  | k + 1, _ :: rest, h =>
    congrArg Nat.succ (length_take_of_le k rest (Nat.le_of_succ_le_succ h))

private theorem length_drop_eq {α : Type} :
    ∀ (k : Nat) (xs : List α), (xs.drop k).length = xs.length - k
  | 0, _ => rfl
  | _ + 1, [] => (Nat.zero_sub _).symm
  | k + 1, _ :: rest => by
    rw [List.drop_succ_cons, length_drop_eq k rest, List.length_cons,
      Nat.add_sub_add_right]

/-- `overflowPairCheck` recognizes exactly the bit-valid initialized local-slot
byte sequences. Overflow pairs are not `TryFromBytes`
(`overflowPair_not_isTryFromBytes`); this is the local-slot analog of
`IsExactTryFromBytes`. -/
theorem overflowPair_localSlotCheck_exact (endian : TargetEndian)
    (w : IntWidth) (s : Bool) :
    ∀ bs,
      ByteSeqValid endian (.tuple [.int w s, .bool]) .initialized bs →
      (overflowPairCheck endian w bs = true ↔
        ByteSeqValid endian (.tuple [.int w s, .bool]) .bitValid bs) := by
  intro bs ⟨l, hL, hLen, hInit⟩
  have hEq : l = overflowPairLayout w := Option.some.inj (hL.symm.trans rfl)
  subst hEq
  have hSize := overflowPair_size_pos w
  have hkLe : w.byteSize ≤ bs.length := by
    rw [hLen, ← hSize, Nat.add_assoc]
    exact Nat.le_add_right _ _
  have hDropLen : 1 ≤ (bs.drop w.byteSize).length := by
    rw [length_drop_eq, hLen, ← hSize, Nat.add_assoc, Nat.add_sub_cancel_left]
    exact Nat.le_add_right _ _
  have ⟨intRaw, hI, hILen⟩ := initBytes?_isSome_of_allBytesInit _
    (allBytesInit_take w.byteSize bs hInit)
  have ⟨boolRaw, hB, hBLen⟩ := initBytes?_isSome_of_allBytesInit _
    (allBytesInit_take 1 _ (allBytesInit_drop w.byteSize bs hInit))
  rw [length_take_of_le _ _ hkLe] at hILen
  rw [length_take_of_le _ _ hDropLen] at hBLen
  have hIntLt : decodeUInt endian intRaw < Nat.pow 2 w.bitWidth := by
    rw [← intWidth_bitWidth_eq]
    exact decodeUInt_lt_of_length endian hILen
  have hBeq : Nat.beq bs.length (overflowPairLayout w).size = true := by
    rw [hLen]
    exact nat_beq_refl _
  have hDec :
      decodeVal endian (.tuple [.int w s, .bool]) bs =
        match evalConstLit .bool
            (.scalar (BitVec.ofNat 128 (decodeUInt endian boolRaw))) with
        | .error k => .error k
        | .ok boolVal =>
          .ok (some (.tuple [.scalar ⟨w, s,
            BitVec.ofNat 128 (decodeUInt endian intRaw)⟩, boolVal])) := by
    unfold decodeVal
    dsimp only
    rw [hBeq, hI, hB]
    dsimp only
    rw [evalConstLit_int_ok w s _ hIntLt]
    rfl
  have hChk :
      overflowPairCheck endian w bs = boolValid (decodeUInt endian boolRaw) := by
    unfold overflowPairCheck
    rw [hB]
  rw [hChk]
  have hBool :=
    evalConstLit_bool_ok_iff (decodeUInt endian boolRaw)
      (decodeUInt_lt_of_length endian hBLen)
  constructor
  · intro hV
    let ⟨bv, hbv⟩ := hBool.2 hV
    refine ⟨overflowPairLayout w,
      .tuple [.scalar ⟨w, s, BitVec.ofNat 128 (decodeUInt endian intRaw)⟩, bv],
      rfl, hLen, ?_⟩
    rw [hDec, hbv]
  · intro ⟨_, v, _, _, hv⟩
    rw [hDec] at hv
    apply hBool.1
    cases hE : evalConstLit .bool
        (.scalar (BitVec.ofNat 128 (decodeUInt endian boolRaw))) with
    | error k =>
      rw [hE] at hv
      nomatch hv
    | ok bv => exact ⟨bv, rfl⟩

/-- The validator that accepts every candidate is not a sound `bool` validator:
initialized byte `0x02` is not a valid `bool`. -/
theorem bool_not_isTryFromBytes_true (endian : TargetEndian) :
    ¬ IsTryFromBytes endian .bool (fun _ => true) :=
  fun h => bool_not_isFromBytes endian
    ((isTryFromBytes_true_iff_isFromBytes endian .bool).1 h)

/-- The validator that rejects every candidate is sound but not exact for
`bool`: byte `0x00` is a valid `bool`. -/
theorem bool_not_isExactTryFromBytes_false (endian : TargetEndian) :
    ¬ IsExactTryFromBytes endian .bool (fun _ => false) := by
  intro ⟨_, _, hIff⟩
  have hValid : ByteSeqValid endian .bool .bitValid [.init 0 none] := by
    cases endian <;> exact ⟨⟨1, 0⟩, .bool false, rfl, rfl, rfl⟩
  exact nomatch (hIff [.init 0 none] ⟨⟨1, 0⟩, rfl, rfl, rfl⟩).2 hValid

/-! ## 5. Concrete Equal-Size `transmute_sound` Corollaries -/

theorem transmute_bool_to_i8_sound (endian : TargetEndian) (s : Bool)
    (v : Val) (bs : List AllocByte)
    (hEnc : encodeVal endian .bool v = .ok bs) :
    NoProvBytes bs ∧ ∃ v', decodeVal endian (.int .i8 s) bs = .ok (some v') :=
  transmute_sound_noProv_of_into_from_bytes endian .bool (.int .i8 s)
    (bool_isIntoBytes endian) (int_isFromBytes endian .i8 s) rfl v bs hEnc

theorem transmute_ordering_to_i8_sound (endian : TargetEndian) (s : Bool)
    (v : Val) (bs : List AllocByte)
    (hEnc : encodeVal endian .ordering v = .ok bs) :
    NoProvBytes bs ∧ ∃ v', decodeVal endian (.int .i8 s) bs = .ok (some v') :=
  transmute_sound_noProv_of_into_from_bytes endian .ordering (.int .i8 s)
    (ordering_isIntoBytes endian) (int_isFromBytes endian .i8 s) rfl v bs hEnc

theorem transmute_scalarEnum_i8_to_i8_sound (endian : TargetEndian)
    (ety : EnumTy) (tagS s : Bool)
    (hAdm : enumAdmitted ety = true)
    (hRepr : ety.tagRepr = .scalar .i8 tagS)
    (v : Val) (bs : List AllocByte)
    (hEnc : encodeVal endian (.enum ety) v = .ok bs) :
    NoProvBytes bs ∧ ∃ v', decodeVal endian (.int .i8 s) bs = .ok (some v') := by
  have hLay : layoutOfTy (.enum ety) = some ⟨1, 0⟩ := by
    unfold layoutOfTy
    simp [hAdm, hRepr]
    rfl
  exact transmute_sound_noProv_of_into_from_bytes endian (.enum ety) (.int .i8 s)
    (scalarEnum_isIntoBytes endian ety .i8 tagS hAdm hRepr)
    (int_isFromBytes endian .i8 s) (by rw [hLay]; rfl) v bs hEnc

theorem transmute_char_to_i32_sound (endian : TargetEndian) (s : Bool)
    (v : Val) (bs : List AllocByte)
    (hEnc : encodeVal endian .char v = .ok bs) :
    NoProvBytes bs ∧ ∃ v', decodeVal endian (.int .i32 s) bs = .ok (some v') :=
  transmute_sound_noProv_of_into_from_bytes endian .char (.int .i32 s)
    (char_isIntoBytes endian) (int_isFromBytes endian .i32 s) rfl v bs hEnc

theorem transmute_int_to_int_sound (endian : TargetEndian)
    (w₁ w₂ : IntWidth) (s₁ s₂ : Bool)
    (hEqSize : w₁.byteSize = w₂.byteSize)
    (v : Val) (bs : List AllocByte)
    (hEnc : encodeVal endian (.int w₁ s₁) v = .ok bs) :
    NoProvBytes bs ∧
      ∃ v', decodeVal endian (.int w₂ s₂) bs = .ok (some v') := by
  have hSizeEq :
      (layoutOfTy (.int w₁ s₁)).map LayoutData.size =
        (layoutOfTy (.int w₂ s₂)).map LayoutData.size := by
    cases w₁ <;> cases w₂ <;> first | rfl | nomatch hEqSize
  exact transmute_sound_noProv_of_into_from_bytes endian (.int w₁ s₁)
    (.int w₂ s₂) (int_isIntoBytes endian w₁ s₁)
    (int_isFromBytes endian w₂ s₂) hSizeEq v bs hEnc

theorem transmute_zstEnum_to_unit_sound (endian : TargetEndian) (ety : EnumTy)
    (hAdm : enumAdmitted ety = true) (hRepr : ety.tagRepr = .zeroSized)
    (v : Val) (bs : List AllocByte)
    (hEnc : encodeVal endian (.enum ety) v = .ok bs) :
    NoProvBytes bs ∧ ∃ v', decodeVal endian .unit bs = .ok (some v') := by
  have hLay : layoutOfTy (.enum ety) = some ⟨0, 0⟩ := by
    unfold layoutOfTy
    simp [hAdm, hRepr]
  exact transmute_sound_noProv_of_into_from_bytes endian (.enum ety) .unit
    (zstEnum_isIntoBytes endian ety hAdm hRepr)
    (unit_isFromBytes endian) (by rw [hLay]; rfl) v bs hEnc

theorem transmute_unit_to_zstEnum_sound (endian : TargetEndian) (ety : EnumTy)
    (hAdm : enumAdmitted ety = true) (hRepr : ety.tagRepr = .zeroSized)
    (v : Val) (bs : List AllocByte)
    (hEnc : encodeVal endian .unit v = .ok bs) :
    NoProvBytes bs ∧ ∃ v', decodeVal endian (.enum ety) bs = .ok (some v') := by
  have hLay : layoutOfTy (.enum ety) = some ⟨0, 0⟩ := by
    unfold layoutOfTy
    simp [hAdm, hRepr]
  exact transmute_sound_noProv_of_into_from_bytes endian .unit (.enum ety)
    (unit_isIntoBytes endian)
    (zstEnum_isFromBytes endian ety hAdm hRepr) (by rw [hLay]; rfl) v bs hEnc

end Anneal.Core

end
