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
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Init.Control.Except
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Layout
public import Trusted.MirSemantics.Bytes
public import Anneal.InitLemmas
public import Anneal.LeBytes
public import Anneal.ListChunks
public import Anneal.Core.BitValidity

public section

namespace Anneal.Core

open Trusted.MirAst Trusted.MirSemantics
open Anneal.InitLemmas Anneal.LeBytes Anneal.ListChunks

/-!
# Prefix-Free Fixed-Width Byte Codecs and Padding Laws (`Core.FixedByteCodec`)

Pure typed `List AllocByte` codecs (`FixedByteCodec α n`) over Anneal's
`AllocByte`, `TargetEndian`, and `MirTy`/`Val` model, paired with compositional
combinators, `Anneal.LeBytes` / `Trusted.MirSemantics.Bytes` bridges, and
`Core.BitValidity` trait and transmutation soundness theorems:

1. **Core `FixedByteCodec α n`:** Prefix-free fixed-width `AllocByte` codecs
   with `ofRoundTrip`, encoding injectivity (`encode_injective`), framing and
   slicing (`take_drop_append_encode`, `decode_slice_at_append`, `sliceBytes`),
   inherent exact-width decoding (`decode_length`, with `rejects_short` and
   `rejects_long` for truncated `< n` and trailing `> n` buffers including
   `n = 0`), byte-validity predicates
   (`IsInitCodec`, `NoProvCodec`, `IsSurjectiveInitDecoder`, `HasZeroValid`),
   and isomorphism transport (`imap`).
2. **Combinators:** Zero-byte ZST (`zst`), contiguous pairs (`prod` with
   a single `take`/`drop` pair for field projection and slice laws),
   uninitialized padding (`padUninit`, `padLeft`, `padRight` preserving
   `HasZeroValid` and `IsSurjectiveInitDecoder` while refuting
   `IsInitCodec` whenever `0 < pad`), homogeneous fixed-length arrays
   (`array : FixedByteCodec (Subtype (fun xs : List α => xs.length = k))`
   `(k * n)` with `ListChunks.chunksOf` and per-element slice laws), and
   decidable niche refinement (`refineNiche`).
3. **Endian-Parametric Primitives:** `∀ endian : TargetEndian` codecs for
   `()` (`unitCodec`), `Bool` (`boolCodec`), arbitrary positive-width
   `BitVec (sz * 8)` (`uintBvCodec`, connecting `Anneal.LeBytes` to
   `encodeUInt`/`decodeUInt`), `u8`/`u16`/`u32`/`u64`/`u128`/`usize` and
   general `MirTy.int w s` (`intBvCodec`), plus `(int, bool)` overflow pairs
   (`overflowPairCodec`), with pointwise agreement against `encodeVal` and
   `decodeVal`.
4. **`MirBytesCodec` & `BitValidity` Trait Bridges:** Connects `FixedByteCodec`
   to `IsExactTryFromBytes` (validator `(codec.decode bs).isSome`),
   `DecodeTyped`, `IsFromZeros`, `IsFromBytes`, and `IsIntoBytes`,
   proves compositional `CodecTransmuteSound` and cross-domain
   `FixedByteCodec <-> MirTy` transmutation theorems, and characterizes why
   padding (`0 < pad`) blocks sound `MirTy` decoding (`decodeVal = .ok none`)
   and breaks `IntoBytes` while preserving `FromZeros` and `FromBytes`.
-/

/-! ## 0. Private Helpers and Pure `AllocByte` Slicing (`0` `noncomputable`) -/

private theorem fbc_two_pow_eight : Nat.pow 2 8 = 256 := rfl

private theorem fbc_false_ne_true (h : false = true) : False := by nomatch h

private theorem fbc_if_true {α : Type} (a b : α) :
    (if true = true then a else b) = a := rfl

private theorem fbc_if_false {α : Type} (a b : α) :
    (if false = true then a else b) = b := rfl

private theorem fbc_if_not_true {α : Type} (a b : α) :
    (if (!true) = true then a else b) = b := rfl

private theorem fbc_if_not_false {α : Type} (a b : α) :
    (if (!false) = true then a else b) = a := rfl

/-- Computable byte size of `IntWidth` (avoids `IntWidth.byteSize`'s
`noncomputable` tag). -/
@[expose] def fbcByteSize : IntWidth → Nat
  | .i8 => 1
  | .i16 => 2
  | .i32 => 4
  | .i64 | .isize => 8
  | .i128 => 16

/-- Computable bit width of `IntWidth`. -/
@[expose] def fbcBitWidth (w : IntWidth) : Nat :=
  fbcByteSize w * 8

theorem fbcByteSize_eq (w : IntWidth) : fbcByteSize w = w.byteSize := by
  cases w <;> rfl

theorem fbcBitWidth_eq (w : IntWidth) : fbcBitWidth w = w.bitWidth := by
  cases w <;> rfl

theorem fbcByteSize_pos (w : IntWidth) : 0 < fbcByteSize w := by
  cases w <;> decide

theorem fbcBitWidth_le_128 (w : IntWidth) : fbcBitWidth w ≤ 128 := by
  cases w <;> decide

private theorem intWidth_eq_of_beq :
    ∀ {a b : IntWidth}, IntWidth.beq a b = true → a = b
  | .i8, .i8, _ | .i16, .i16, _ | .i32, .i32, _
  | .i64, .i64, _ | .i128, .i128, _ | .isize, .isize, _ => rfl

private theorem fbc_bv_eq_of_toNat_eq {w : Nat} {a b : BitVec w}
    (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | ofFin fa =>
    cases b with
    | ofFin fb =>
      exact congrArg BitVec.ofFin (Fin.eq_of_val_eq h)

private theorem fbc_bv_toNat_ofNat (w n : Nat) :
    (BitVec.ofNat w n).toNat = HMod.hMod n (Nat.pow 2 w) := rfl

private theorem fbc_uint8_eq_of_toNat_eq {x y : UInt8}
    (h : x.toNat = y.toNat) : x = y := by
  cases x with
  | ofBitVec bx =>
    cases y with
    | ofBitVec by_ =>
      cases bx with
      | ofFin fx =>
        cases by_ with
        | ofFin fy =>
          cases fx with
          | mk vx _ =>
            cases fy with
            | mk vy _ =>
              change vx = vy at h
              subst h
              rfl

private theorem fbc_length_drop {α : Type} (n : Nat) (xs : List α) :
    (xs.drop n).length = xs.length - n := by
  induction n generalizing xs with
  | zero => rw [List.drop_zero, Nat.sub_zero]
  | succ n ih =>
    cases xs with
    | nil => rw [List.drop_nil, List.length_nil, Nat.zero_sub]
    | cons _ rest => rw [List.drop_succ_cons, List.length_cons, ih, Nat.succ_sub_succ]

private theorem fbc_length_take_eq {α : Type} (n : Nat) (xs : List α) :
    (xs.take n).length = if n ≤ xs.length then n else xs.length := by
  induction n generalizing xs with
  | zero => rw [List.take_zero, List.length_nil, ite_true_of (Nat.zero_le _)]
  | succ n ih =>
    cases xs with
    | nil =>
      rw [List.take_nil, List.length_nil, ite_false_of (Nat.not_succ_le_zero n)]
    | cons _ rest =>
      rw [List.take_succ_cons, List.length_cons, List.length_cons, ih]
      cases Nat.lt_or_ge rest.length n with
      | inl hlt =>
        rw [ite_false_of (Nat.not_le_of_gt hlt),
            ite_false_of (Nat.not_le_of_gt (Nat.succ_lt_succ hlt))]
      | inr hge =>
        rw [ite_true_of hge, ite_true_of (Nat.succ_le_succ hge)]

private theorem fbc_length_take_of_le {α : Type} {n : Nat} {xs : List α}
    (h : n ≤ xs.length) : (xs.take n).length = n := by
  rw [fbc_length_take_eq, ite_true_of h]

private theorem fbc_take_all_of_le {α : Type} :
    ∀ (n : Nat) (xs : List α), xs.length ≤ n → xs.take n = xs
  | 0, [], _ => rfl
  | 0, _ :: _, h => by nomatch h
  | _ + 1, [], _ => rfl
  | n + 1, x :: xs, h =>
    congrArg (List.cons x)
      (fbc_take_all_of_le n xs (Nat.le_of_succ_le_succ h))

private theorem fbc_drop_all_of_le {α : Type} :
    ∀ (n : Nat) (xs : List α), xs.length ≤ n → xs.drop n = []
  | 0, [], _ => rfl
  | 0, _ :: _, h => by nomatch h
  | _ + 1, [], _ => rfl
  | n + 1, _ :: xs, h =>
    fbc_drop_all_of_le n xs (Nat.le_of_succ_le_succ h)

private theorem fbc_drop_drop {α : Type} (m n : Nat) (xs : List α) :
    (xs.drop m).drop n = xs.drop (m + n) := by
  induction m generalizing xs with
  | zero => rw [List.drop_zero, Nat.zero_add]
  | succ m ih =>
    cases xs with
    | nil => rw [List.drop_nil, List.drop_nil, List.drop_nil]
    | cons _ rest => rw [List.drop_succ_cons, Nat.succ_add, List.drop_succ_cons, ih]

private theorem fbc_take_append_left_eq {α : Type} {n : Nat}
    (xs ys : List α) (hLen : xs.length = n) :
    (xs ++ ys).take n = xs := by
  rw [← hLen]
  exact list_take_append_left xs ys

private theorem fbc_drop_append_left_eq {α : Type} {n : Nat}
    (xs ys : List α) (hLen : xs.length = n) :
    (xs ++ ys).drop n = ys := by
  rw [← hLen]
  exact list_drop_append_left xs ys

private theorem fbc_reverse_append {α : Type} (xs ys : List α) :
    (xs ++ ys).reverse = ys.reverse ++ xs.reverse := by
  induction xs with
  | nil => rw [List.nil_append, List.reverse_nil, List.append_nil]
  | cons a rest ih =>
    rw [List.cons_append, List.reverse_cons, List.reverse_cons, ih,
        List.append_assoc]

private theorem fbc_reverse_reverse {α : Type} (xs : List α) :
    xs.reverse.reverse = xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    rw [List.reverse_cons, fbc_reverse_append, ih]
    rfl

private theorem fbc_map_append {α β : Type} (f : α → β) :
    ∀ xs ys : List α, (xs ++ ys).map f = xs.map f ++ ys.map f
  | [], _ => rfl
  | x :: rest, ys => congrArg (List.cons (f x)) (fbc_map_append f rest ys)

private theorem fbc_map_reverse {α β : Type} (f : α → β) :
    ∀ xs : List α, (xs.map f).reverse = xs.reverse.map f
  | [] => rfl
  | x :: rest => by
    change (f x :: rest.map f).reverse = (x :: rest).reverse.map f
    rw [List.reverse_cons, List.reverse_cons, fbc_map_append,
        fbc_map_reverse f rest]
    rfl

private theorem fbc_map_comp {α β γ : Type} (g : β → γ) (f : α → β) :
    ∀ xs : List α, (xs.map f).map g = xs.map (fun x => g (f x))
  | [] => rfl
  | x :: rest => congrArg (List.cons (g (f x))) (fbc_map_comp g f rest)

private theorem fbc_map_id {α : Type} : ∀ xs : List α, xs.map id = xs
  | [] => rfl
  | x :: rest => congrArg (List.cons x) (fbc_map_id rest)

private theorem fbc_allBytesInit_take :
    ∀ (n : Nat) (bs : List AllocByte),
      AllBytesInit bs → AllBytesInit (bs.take n)
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | n + 1, .uninit :: _, h => by nomatch h
  | n + 1, .init b prov :: rest, h => by
    change allBytesInit (.init b prov :: rest.take n) = true
    exact fbc_allBytesInit_take n rest h

private theorem fbc_allBytesInit_drop :
    ∀ (n : Nat) (bs : List AllocByte),
      AllBytesInit bs → AllBytesInit (bs.drop n)
  | 0, _, h => h
  | _ + 1, [], _ => rfl
  | n + 1, .uninit :: _, h => by nomatch h
  | n + 1, .init _ _ :: rest, h => fbc_allBytesInit_drop n rest h

private theorem fbc_allBytesInit_append_false_left (xs ys : List AllocByte)
    (hx : allBytesInit xs = false) :
    allBytesInit (xs ++ ys) = false := by
  rw [allBytesInit_append, hx]
  rfl

private theorem fbc_allBytesInit_append_false_right (xs ys : List AllocByte)
    (hy : allBytesInit ys = false) :
    allBytesInit (xs ++ ys) = false := by
  rw [allBytesInit_append, hy]
  cases allBytesInit xs <;> rfl

private theorem fbc_allBytesInit_replicate_uninit_pos {n : Nat} (hPos : 0 < n) :
    allBytesInit (List.replicate n AllocByte.uninit) = false := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 hPos)
  | succ k => exact allBytesInit_replicate_uninit k

/-- Pure checked byte-slice extraction on `List AllocByte`, returning
`some ((bs.drop off).take len)` iff `off + len ≤ bs.length`. -/
@[expose] def sliceBytes (bs : List AllocByte) (off len : Nat) :
    Option (List AllocByte) :=
  if Nat.ble (off + len) bs.length then
    some ((bs.drop off).take len)
  else
    none

theorem sliceBytes_length {bs sub : List AllocByte} {off len : Nat}
    (h : sliceBytes bs off len = some sub) : sub.length = len := by
  unfold sliceBytes at h
  cases hBle : Nat.ble (off + len) bs.length with
  | false =>
    rw [hBle] at h
    nomatch h
  | true =>
    rw [hBle] at h
    injection h with hSub
    subst hSub
    have hLe : off + len ≤ bs.length := Nat.ble_eq.mp hBle
    rw [fbc_length_take_of_le]
    rw [fbc_length_drop]
    exact Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hLe)

theorem sliceBytes_append_exact (pre mid post : List AllocByte) :
    sliceBytes (pre ++ mid ++ post) pre.length mid.length = some mid := by
  have hLe : pre.length + mid.length ≤ (pre ++ mid ++ post).length := by
    rw [List.length_append, List.length_append]
    exact Nat.le_add_right _ _
  have hBle :
      Nat.ble (pre.length + mid.length) (pre ++ mid ++ post).length = true :=
    Nat.ble_eq.mpr hLe
  unfold sliceBytes
  rw [hBle, fbc_if_true]
  rw [List.append_assoc, list_drop_append_left pre (mid ++ post),
      list_take_append_left mid post]

theorem sliceBytes_append_exact_len (pre mid post : List AllocByte)
    (len : Nat) (hLen : mid.length = len) :
    sliceBytes (pre ++ mid ++ post) pre.length len = some mid := by
  subst hLen
  exact sliceBytes_append_exact pre mid post

theorem allBytesInit_of_sliceBytes {bs sub : List AllocByte} {off len : Nat}
    (hInit : AllBytesInit bs) (hSlice : sliceBytes bs off len = some sub) :
    AllBytesInit sub := by
  unfold sliceBytes at hSlice
  cases hBle : Nat.ble (off + len) bs.length with
  | false =>
    rw [hBle] at hSlice
    nomatch hSlice
  | true =>
    rw [hBle] at hSlice
    injection hSlice with hSub
    subst hSub
    exact fbc_allBytesInit_take len (bs.drop off) (fbc_allBytesInit_drop off bs hInit)

theorem sliceBytes_eq_none_of_lt {bs : List AllocByte} {off len : Nat}
    (hLt : bs.length < off + len) : sliceBytes bs off len = none := by
  have hFalse : Nat.ble (off + len) bs.length = false := by
    cases hB : Nat.ble (off + len) bs.length with
    | false => rfl
    | true => exact False.elim (Nat.not_le_of_gt hLt (Nat.ble_eq.mp hB))
  unfold sliceBytes
  rw [hFalse]
  rfl

/-! ## 1. Core Prefix-Free Fixed-Width Byte Codec (`FixedByteCodec`) -/

/-- A prefix-free fixed-width codec between values of type `α` and `n`-byte
`List AllocByte` sequences. -/
structure FixedByteCodec (α : Type) (n : Nat) : Type where
  /-- Serialize `x` into an exact `n`-byte sequence. -/
  encode : α → List AllocByte
  /-- Deserialize an `α` from an `n`-byte slice. Returns `none` on ill-sized
  inputs (`decode_length`) and on codec-specific invalid bit patterns or
  uninitialized value bytes; padding and tagged codecs such as `padUninit`
  intentionally accept `.uninit` at padding or inactive bytes. -/
  decode : List AllocByte → Option α
  /-- Every encoded value has exact length `n`. -/
  encode_length : ∀ x : α, (encode x).length = n
  /-- Exact round-trip on `encode x`. -/
  decode_encode : ∀ x : α, decode (encode x) = some x
  /-- Decoding succeeds only on buffers of exact length `n`. -/
  decode_length : ∀ ⦃bs : List AllocByte⦄ ⦃x : α⦄, decode bs = some x → bs.length = n

namespace FixedByteCodec

/-- Construct a `FixedByteCodec α n` from `encode`, `decode`, `encode_length`,
`decode_encode`, and `decode_length`. -/
@[expose] def ofRoundTrip {α : Type} {n : Nat}
    (encode : α → List AllocByte)
    (decode : List AllocByte → Option α)
    (encode_length : ∀ x : α, (encode x).length = n)
    (decode_encode : ∀ x : α, decode (encode x) = some x)
    (decode_length :
      ∀ ⦃bs : List AllocByte⦄ ⦃x : α⦄, decode bs = some x → bs.length = n) :
    FixedByteCodec α n where
  encode := encode
  decode := decode
  encode_length := encode_length
  decode_encode := decode_encode
  decode_length := decode_length

/-- Prefix-free round-trip: trailing bytes after the `n`-byte prefix are
stripped by `take n`. -/
theorem decode_take_append {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (x : α) (rest : List AllocByte) :
    c.decode ((c.encode x ++ rest).take n) = some x := by
  rw [fbc_take_append_left_eq (c.encode x) rest (c.encode_length x)]
  exact c.decode_encode x

/-- Encoding is injective for every `FixedByteCodec`. -/
theorem encode_injective {α : Type} {n : Nat} (c : FixedByteCodec α n)
    {x y : α} (h : c.encode x = c.encode y) : x = y := by
  have hx := c.decode_encode x
  rw [h, c.decode_encode y] at hx
  exact Option.some.inj hx.symm

/-- Taking `n` bytes of `c.encode x ++ rest` yields `c.encode x`. -/
theorem take_append_encode {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (x : α) (rest : List AllocByte) :
    (c.encode x ++ rest).take n = c.encode x :=
  fbc_take_append_left_eq (c.encode x) rest (c.encode_length x)

/-- Dropping `n` bytes of `c.encode x ++ rest` yields `rest`. -/
theorem drop_append_encode {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (x : α) (rest : List AllocByte) :
    (c.encode x ++ rest).drop n = rest :=
  fbc_drop_append_left_eq (c.encode x) rest (c.encode_length x)

/-- Slicing `pre ++ c.encode x ++ post` at `pre.length` for `n` bytes recovers
`c.encode x` verbatim. -/
theorem take_drop_append_encode {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (pre post : List AllocByte) (x : α) :
    ((pre ++ c.encode x ++ post).drop pre.length).take n = c.encode x := by
  rw [List.append_assoc, list_drop_append_left pre (c.encode x ++ post),
      c.take_append_encode x post]

/-- Decoding the `n`-byte window starting at `pre.length` inside
`pre ++ c.encode x ++ post` yields `some x`. -/
theorem decode_slice_at_append {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (pre post : List AllocByte) (x : α) :
    c.decode (((pre ++ c.encode x ++ post).drop pre.length).take n) = some x := by
  rw [c.take_drop_append_encode pre post x]
  exact c.decode_encode x

/-- `sliceBytes` extracts `some (c.encode x)` from `pre ++ c.encode x ++ post`
at offset `pre.length` and width `n`. -/
theorem sliceBytes_append_encode {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (pre post : List AllocByte) (x : α) :
    sliceBytes (pre ++ c.encode x ++ post) pre.length n = some (c.encode x) :=
  sliceBytes_append_exact_len pre (c.encode x) post n (c.encode_length x)

/-- Binding `c.decode` onto
`sliceBytes (pre ++ c.encode x ++ post) pre.length n` returns `some x`. -/
theorem decode_sliceBytes_append {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (pre post : List AllocByte) (x : α) :
    (sliceBytes (pre ++ c.encode x ++ post) pre.length n).bind c.decode =
      some x := by
  rw [c.sliceBytes_append_encode pre post x]
  exact c.decode_encode x

/-- Any buffer whose length differs from `n` is rejected (`decode_length`). -/
theorem rejects_ne {α : Type} {n : Nat} (c : FixedByteCodec α n)
    {bs : List AllocByte} (hNe : bs.length ≠ n) : c.decode bs = none := by
  cases hDec : c.decode bs with
  | none => rfl
  | some _ => exact False.elim (hNe (c.decode_length hDec))

/-- Truncated buffers (`bs.length < n`) fail `c.decode`. -/
theorem rejects_short {α : Type} {n : Nat} (c : FixedByteCodec α n)
    {bs : List AllocByte} (hShort : bs.length < n) : c.decode bs = none :=
  c.rejects_ne (Nat.ne_of_lt hShort)

/-- Buffers with trailing bytes (`n < bs.length`) fail `c.decode`. -/
theorem rejects_long {α : Type} {n : Nat} (c : FixedByteCodec α n)
    {bs : List AllocByte} (hLong : n < bs.length) : c.decode bs = none :=
  c.rejects_ne (Nat.ne_of_gt hLong)

/-- Any non-empty buffer fails a zero-byte (`n = 0`) codec. -/
theorem rejects_nonempty_of_zero {α : Type} (c : FixedByteCodec α 0)
    {bs : List AllocByte} (hNe : bs ≠ []) : c.decode bs = none := by
  cases bs with
  | nil => exact False.elim (hNe rfl)
  | cons _ _ => exact c.rejects_long (Nat.zero_lt_succ _)

/-- Every encoded byte sequence contains only initialized bytes (modeling
`IntoBytes` initialization freedom from `.uninit` padding). -/
@[expose] def IsInitCodec {α : Type} {n : Nat} (c : FixedByteCodec α n) : Prop :=
  ∀ x : α, AllBytesInit (c.encode x)

/-- Every encoded byte sequence carries `none` provenance on all bytes. -/
@[expose] def NoProvCodec {α : Type} {n : Nat} (c : FixedByteCodec α n) : Prop :=
  ∀ x : α, NoProvBytes (c.encode x)

/-- Every initialized `n`-byte sequence decodes to `some x` (modeling
`FromBytes` total bit-pattern validity across all initialized `n`-byte inputs).
-/
@[expose] def IsSurjectiveInitDecoder {α : Type} {n : Nat} (c : FixedByteCodec α n) :
    Prop :=
  ∀ bs : List AllocByte, bs.length = n → AllBytesInit bs → ∃ x : α, c.decode bs = some x

/-- Zero-initialized `n`-byte buffer decodes cleanly (modeling `FromZeros`). -/
@[expose] def HasZeroValid {α : Type} {n : Nat} (c : FixedByteCodec α n) : Prop :=
  ∃ x : α, c.decode (zeroInitBytes n) = some x

/-- `IsSurjectiveInitDecoder` implies `HasZeroValid`. -/
theorem IsSurjectiveInitDecoder.hasZeroValid {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hSurj : c.IsSurjectiveInitDecoder) :
    c.HasZeroValid :=
  hSurj (zeroInitBytes n) (length_zeroInitBytes n) (allBytesInit_zeroInitBytes n)

/-- Transport a `FixedByteCodec α n` across a type isomorphism
`(toβ, ofβ)`. -/
@[expose] def imap {α β : Type} {n : Nat}
    (c : FixedByteCodec α n)
    (toβ : α → β)
    (ofβ : β → α)
    (left_inv : ∀ a : α, ofβ (toβ a) = a)
    (right_inv : ∀ b : β, toβ (ofβ b) = b) :
    FixedByteCodec β n :=
  let _ := left_inv
  ofRoundTrip
    (fun b => c.encode (ofβ b))
    (fun bs => (c.decode bs).map toβ)
    (fun b => c.encode_length (ofβ b))
    (fun b => by
      rw [c.decode_encode (ofβ b)]
      dsimp only [Option.map]
      exact congrArg some (right_inv b))
    (by
      intro bs _ h
      cases hc : c.decode bs with
      | none =>
        rw [hc] at h
        nomatch h
      | some _ => exact c.decode_length hc)

theorem imap_encode_to {α β : Type} {n : Nat}
    (c : FixedByteCodec α n) (toβ : α → β) (ofβ : β → α)
    (hL : ∀ a, ofβ (toβ a) = a) (hR : ∀ b, toβ (ofβ b) = b) (a : α) :
    (c.imap toβ ofβ hL hR).encode (toβ a) = c.encode a :=
  congrArg c.encode (hL a)

theorem imap_isInitCodec {α β : Type} {n : Nat}
    (c : FixedByteCodec α n) (toβ : α → β) (ofβ : β → α)
    (hL : ∀ a, ofβ (toβ a) = a) (hR : ∀ b, toβ (ofβ b) = b)
    (hInit : c.IsInitCodec) :
    (c.imap toβ ofβ hL hR).IsInitCodec :=
  fun b => hInit (ofβ b)

theorem imap_noProvCodec {α β : Type} {n : Nat}
    (c : FixedByteCodec α n) (toβ : α → β) (ofβ : β → α)
    (hL : ∀ a, ofβ (toβ a) = a) (hR : ∀ b, toβ (ofβ b) = b)
    (hNoProv : c.NoProvCodec) :
    (c.imap toβ ofβ hL hR).NoProvCodec :=
  fun b => hNoProv (ofβ b)

theorem imap_isSurjectiveInitDecoder {α β : Type} {n : Nat}
    (c : FixedByteCodec α n) (toβ : α → β) (ofβ : β → α)
    (hL : ∀ a, ofβ (toβ a) = a) (hR : ∀ b, toβ (ofβ b) = b)
    (hSurj : c.IsSurjectiveInitDecoder) :
    (c.imap toβ ofβ hL hR).IsSurjectiveInitDecoder := by
  intro bs hLen hInit
  have ⟨a, ha⟩ := hSurj bs hLen hInit
  refine ⟨toβ a, ?_⟩
  unfold imap ofRoundTrip
  dsimp only
  rw [ha]
  rfl

theorem imap_hasZeroValid {α β : Type} {n : Nat}
    (c : FixedByteCodec α n) (toβ : α → β) (ofβ : β → α)
    (hL : ∀ a, ofβ (toβ a) = a) (hR : ∀ b, toβ (ofβ b) = b)
    (hZero : c.HasZeroValid) :
    (c.imap toβ ofβ hL hR).HasZeroValid := by
  have ⟨a, ha⟩ := hZero
  refine ⟨toβ a, ?_⟩
  unfold imap ofRoundTrip
  dsimp only
  rw [ha]
  rfl

/-! ## 2. Compositional Combinators (`zst`, `prod`, Padding, `array`, Niche) -/

/-! ### 2a. Zero-Sized Type Codec (`zst`) -/

/-- Zero-byte codec for `Unit`, accepting only `[]`. -/
@[expose] def zst : FixedByteCodec Unit 0 :=
  ofRoundTrip
    (fun _ => [])
    (fun bs => match bs with | [] => some () | _ :: _ => none)
    (fun _ => rfl)
    (fun ⟨⟩ => rfl)
    (by
      intro bs _ h
      cases bs with
      | nil => rfl
      | cons _ _ => nomatch h)

theorem zst_encode_eq (u : Unit) : zst.encode u = [] := rfl

theorem zst_decode_nil : zst.decode [] = some () := rfl

theorem zst_decode_cons (b : AllocByte) (rest : List AllocByte) :
    zst.decode (b :: rest) = none := rfl

theorem zst_isInitCodec : zst.IsInitCodec := fun _ => rfl

theorem zst_noProvCodec : zst.NoProvCodec := fun _ => rfl

theorem zst_isSurjectiveInitDecoder : zst.IsSurjectiveInitDecoder := by
  intro bs hLen _
  cases bs with
  | nil => exact ⟨(), rfl⟩
  | cons _ _ => nomatch hLen

theorem zst_hasZeroValid : zst.HasZeroValid := ⟨(), rfl⟩

/-! ### 2b. Contiguous Product Codec (`prod`) -/

/-- Contiguous sequential product codec `FixedByteCodec (α × β) (m + n)`. -/
@[expose] def prod {α β : Type} {m n : Nat}
    (c₁ : FixedByteCodec α m) (c₂ : FixedByteCodec β n) :
    FixedByteCodec (α × β) (m + n) :=
  ofRoundTrip
    (fun p => c₁.encode p.1 ++ c₂.encode p.2)
    (fun bs =>
      if Nat.beq bs.length (m + n) then
        match c₁.decode (bs.take m), c₂.decode (bs.drop m) with
        | some a, some b => some (a, b)
        | _, _ => none
      else
        none)
    (fun ⟨a, b⟩ => by
      rw [List.length_append, c₁.encode_length a, c₂.encode_length b])
    (fun ⟨a, b⟩ => by
      have hLen :
          (c₁.encode a ++ c₂.encode b).length = m + n := by
        rw [List.length_append, c₁.encode_length a, c₂.encode_length b]
      have hBeq : Nat.beq (c₁.encode a ++ c₂.encode b).length (m + n) = true :=
        (nat_beq_iff _ _).mpr hLen
      dsimp only
      rw [ite_true_of hBeq,
          fbc_take_append_left_eq (c₁.encode a) (c₂.encode b) (c₁.encode_length a),
          fbc_drop_append_left_eq (c₁.encode a) (c₂.encode b) (c₁.encode_length a),
          c₁.decode_encode a, c₂.decode_encode b])
    (by
      intro bs _ h
      cases hBeq : Nat.beq bs.length (m + n) with
      | false =>
        rw [hBeq] at h
        nomatch h
      | true => exact nat_eq_of_beq hBeq)

theorem prod_encode_eq {α β : Type} {m n : Nat}
    (c₁ : FixedByteCodec α m) (c₂ : FixedByteCodec β n) (a : α) (b : β) :
    (prod c₁ c₂).encode (a, b) = c₁.encode a ++ c₂.encode b := rfl

/-- `take` first-field projection of `(prod c₁ c₂).encode`. -/
theorem prod_encode_take_fst {α β : Type} {m n : Nat}
    (c₁ : FixedByteCodec α m) (c₂ : FixedByteCodec β n) (a : α) (b : β) :
    ((prod c₁ c₂).encode (a, b)).take m = c₁.encode a :=
  fbc_take_append_left_eq (c₁.encode a) (c₂.encode b) (c₁.encode_length a)

/-- `drop` second-field projection of `(prod c₁ c₂).encode`. -/
theorem prod_encode_drop_snd {α β : Type} {m n : Nat}
    (c₁ : FixedByteCodec α m) (c₂ : FixedByteCodec β n) (a : α) (b : β) :
    ((prod c₁ c₂).encode (a, b)).drop m = c₂.encode b :=
  fbc_drop_append_left_eq (c₁.encode a) (c₂.encode b) (c₁.encode_length a)

/-- Decoding `(prod c₁ c₂)` implies decoding the `take m` and `drop m` slices.
-/
theorem prod_decode_projections {α β : Type} {m n : Nat}
    (c₁ : FixedByteCodec α m) (c₂ : FixedByteCodec β n)
    {bs : List AllocByte} {a : α} {b : β}
    (hDec : (prod c₁ c₂).decode bs = some (a, b)) :
    bs.length = m + n ∧
      c₁.decode (bs.take m) = some a ∧ c₂.decode (bs.drop m) = some b := by
  unfold prod ofRoundTrip at hDec
  dsimp only at hDec
  cases hBeq : Nat.beq bs.length (m + n) with
  | false =>
    rw [hBeq] at hDec
    nomatch hDec
  | true =>
    rw [hBeq] at hDec
    have hLen : bs.length = m + n := nat_eq_of_beq hBeq
    cases h1 : c₁.decode (bs.take m) with
    | none =>
      rw [h1] at hDec
      nomatch hDec
    | some a' =>
      rw [h1] at hDec
      cases h2 : c₂.decode (bs.drop m) with
      | none =>
        rw [h2] at hDec
        nomatch hDec
      | some b' =>
        rw [h2] at hDec
        injection hDec with hPair
        injection hPair with ha hb
        subst ha
        subst hb
        exact ⟨hLen, by first | exact rfl | exact h1, by first | exact rfl | exact h2⟩

theorem prod_decode_of_chunks {α β : Type} {m n : Nat}
    (c₁ : FixedByteCodec α m) (c₂ : FixedByteCodec β n)
    {bs : List AllocByte} {a : α} {b : β}
    (hLen : bs.length = m + n)
    (h1 : c₁.decode (bs.take m) = some a)
    (h2 : c₂.decode (bs.drop m) = some b) :
    (prod c₁ c₂).decode bs = some (a, b) := by
  unfold prod ofRoundTrip
  dsimp only
  have hBeq : Nat.beq bs.length (m + n) = true := (nat_beq_iff _ _).mpr hLen
  rw [ite_true_of hBeq, h1, h2]

/-- First-field slice extraction inside `pre ++ (prod c₁ c₂).encode (a, b)
++ post`. -/
theorem prod_sliceBytes_fst {α β : Type} {m n : Nat}
    (c₁ : FixedByteCodec α m) (c₂ : FixedByteCodec β n)
    (pre post : List AllocByte) (a : α) (b : β) :
    sliceBytes (pre ++ (prod c₁ c₂).encode (a, b) ++ post) pre.length m =
      some (c₁.encode a) := by
  rw [prod_encode_eq, List.append_assoc, List.append_assoc (c₁.encode a),
      ← List.append_assoc pre (c₁.encode a)]
  exact sliceBytes_append_exact_len pre (c₁.encode a) (c₂.encode b ++ post) m
    (c₁.encode_length a)

/-- Second-field slice extraction at `pre.length + m` inside
`pre ++ (prod c₁ c₂).encode (a, b) ++ post`. -/
theorem prod_sliceBytes_snd {α β : Type} {m n : Nat}
    (c₁ : FixedByteCodec α m) (c₂ : FixedByteCodec β n)
    (pre post : List AllocByte) (a : α) (b : β) :
    sliceBytes (pre ++ (prod c₁ c₂).encode (a, b) ++ post)
        (pre.length + m) n =
      some (c₂.encode b) := by
  rw [prod_encode_eq, ← List.append_assoc pre (c₁.encode a) (c₂.encode b)]
  have hLen : (pre ++ c₁.encode a).length = pre.length + m := by
    rw [List.length_append, c₁.encode_length a]
  rw [← hLen]
  exact sliceBytes_append_exact_len (pre ++ c₁.encode a) (c₂.encode b) post n
    (c₂.encode_length b)

theorem prod_isInitCodec {α β : Type} {m n : Nat}
    {c₁ : FixedByteCodec α m} {c₂ : FixedByteCodec β n}
    (h₁ : c₁.IsInitCodec) (h₂ : c₂.IsInitCodec) :
    (prod c₁ c₂).IsInitCodec :=
  fun ⟨a, b⟩ => AllBytesInit_append (h₁ a) (h₂ b)

theorem prod_noProvCodec {α β : Type} {m n : Nat}
    {c₁ : FixedByteCodec α m} {c₂ : FixedByteCodec β n}
    (h₁ : c₁.NoProvCodec) (h₂ : c₂.NoProvCodec) :
    (prod c₁ c₂).NoProvCodec :=
  fun ⟨a, b⟩ => NoProvBytes_append (h₁ a) (h₂ b)

theorem prod_isSurjectiveInitDecoder {α β : Type} {m n : Nat}
    {c₁ : FixedByteCodec α m} {c₂ : FixedByteCodec β n}
    (h₁ : c₁.IsSurjectiveInitDecoder) (h₂ : c₂.IsSurjectiveInitDecoder) :
    (prod c₁ c₂).IsSurjectiveInitDecoder := by
  intro bs hLen hInit
  have hmLe : m ≤ bs.length := by
    rw [hLen]
    exact Nat.le_add_right m n
  have hTakeLen : (bs.take m).length = m := fbc_length_take_of_le hmLe
  have hDropLen : (bs.drop m).length = n := by
    rw [fbc_length_drop, hLen, Nat.add_sub_cancel_left]
  have ⟨a, ha⟩ := h₁ (bs.take m) hTakeLen (fbc_allBytesInit_take m bs hInit)
  have ⟨b, hb⟩ := h₂ (bs.drop m) hDropLen (fbc_allBytesInit_drop m bs hInit)
  exact ⟨(a, b), prod_decode_of_chunks c₁ c₂ hLen ha hb⟩

theorem prod_hasZeroValid {α β : Type} {m n : Nat}
    {c₁ : FixedByteCodec α m} {c₂ : FixedByteCodec β n}
    (h₁ : c₁.HasZeroValid) (h₂ : c₂.HasZeroValid) :
    (prod c₁ c₂).HasZeroValid := by
  have ⟨a, ha⟩ := h₁
  have ⟨b, hb⟩ := h₂
  refine ⟨(a, b), prod_decode_of_chunks c₁ c₂ (length_zeroInitBytes (m + n)) ?_ ?_⟩
  · rw [zeroInitBytes_add m n, fbc_take_append_left_eq _ _ (length_zeroInitBytes m)]
    exact ha
  · rw [zeroInitBytes_add m n, fbc_drop_append_left_eq _ _ (length_zeroInitBytes m)]
    exact hb

theorem prod_decode_eq_none_of_fst_none {α β : Type} {m n : Nat}
    (c₁ : FixedByteCodec α m) (c₂ : FixedByteCodec β n)
    {bs : List AllocByte} (hFst : c₁.decode (bs.take m) = none) :
    (prod c₁ c₂).decode bs = none := by
  unfold prod ofRoundTrip
  dsimp only
  cases Nat.beq bs.length (m + n) with
  | false => rfl
  | true => rw [fbc_if_true, hFst]

theorem prod_decode_eq_none_of_snd_none {α β : Type} {m n : Nat}
    (c₁ : FixedByteCodec α m) (c₂ : FixedByteCodec β n)
    {bs : List AllocByte} (hSnd : c₂.decode (bs.drop m) = none) :
    (prod c₁ c₂).decode bs = none := by
  unfold prod ofRoundTrip
  dsimp only
  cases Nat.beq bs.length (m + n) with
  | false => rfl
  | true =>
    cases c₁.decode (bs.take m) with
    | none => rfl
    | some _ => rw [fbc_if_true, hSnd]

/-! ### 2c. Uninitialized Padding Combinators (`padUninit`, `padLeft`,
`padRight`) -/

/-- Uninitialized padding codec of width `pad`: encodes `()` to
`List.replicate pad .uninit` and accepts any `pad`-length `AllocByte` slice on
`decode`. -/
@[expose] def padUninit (pad : Nat) : FixedByteCodec Unit pad :=
  ofRoundTrip
    (fun _ => List.replicate pad AllocByte.uninit)
    (fun bs => if Nat.beq bs.length pad then some () else none)
    (fun _ => length_replicate_eq AllocByte.uninit pad)
    (fun _ => by
      have hBeq :
          Nat.beq (List.replicate pad AllocByte.uninit).length pad = true :=
        (nat_beq_iff _ _).mpr (length_replicate_eq AllocByte.uninit pad)
      exact ite_true_of hBeq)
    (by
      intro bs _ h
      cases hBeq : Nat.beq bs.length pad with
      | false =>
        rw [hBeq] at h
        nomatch h
      | true => exact nat_eq_of_beq hBeq)

theorem padUninit_encode_eq (pad : Nat) :
    (padUninit pad).encode () = List.replicate pad AllocByte.uninit := rfl

theorem padUninit_decode_of_length_eq (pad : Nat) {bs : List AllocByte}
    (hLen : bs.length = pad) : (padUninit pad).decode bs = some () := by
  unfold padUninit ofRoundTrip
  dsimp only
  exact ite_true_of ((nat_beq_iff _ _).mpr hLen)

theorem padUninit_noProvCodec (pad : Nat) : (padUninit pad).NoProvCodec :=
  fun _ => noProvBytes_replicate_uninit pad

theorem padUninit_isSurjectiveInitDecoder (pad : Nat) :
    (padUninit pad).IsSurjectiveInitDecoder := by
  intro bs hLen _
  exact ⟨(), @padUninit_decode_of_length_eq pad bs hLen⟩

theorem padUninit_hasZeroValid (pad : Nat) : (padUninit pad).HasZeroValid :=
  (padUninit_isSurjectiveInitDecoder pad).hasZeroValid

theorem padUninit_zero_isInitCodec : (padUninit 0).IsInitCodec :=
  fun _ => rfl

theorem padUninit_not_isInitCodec {pad : Nat} (hPos : 0 < pad) :
    ¬ (padUninit pad).IsInitCodec := by
  intro hInit
  have hTrue : allBytesInit ((padUninit pad).encode ()) = true := hInit ()
  rw [padUninit_encode_eq, fbc_allBytesInit_replicate_uninit_pos hPos] at hTrue
  nomatch hTrue

/-- Prepend `pad` padding bytes before `c`, encoding `.uninit` padding while
accepting any `pad`-byte prefix on decode. -/
@[expose] def padLeft {α : Type} {n : Nat} (pad : Nat) (c : FixedByteCodec α n) :
    FixedByteCodec α (pad + n) :=
  (prod (padUninit pad) c).imap Prod.snd (fun x => ((), x))
    (fun p => by cases p with | mk u x => cases u; rfl)
    (fun _ => rfl)

/-- Append `pad` padding bytes after `c`, encoding `.uninit` padding while
accepting any `pad`-byte suffix on decode. -/
@[expose] def padRight {α : Type} {n : Nat} (c : FixedByteCodec α n) (pad : Nat) :
    FixedByteCodec α (n + pad) :=
  (prod c (padUninit pad)).imap Prod.fst (fun x => (x, ()))
    (fun p => by cases p with | mk x u => cases u; rfl)
    (fun _ => rfl)

theorem padLeft_encode_eq {α : Type} {n : Nat} (pad : Nat)
    (c : FixedByteCodec α n) (x : α) :
    (padLeft pad c).encode x = List.replicate pad AllocByte.uninit ++ c.encode x :=
  rfl

theorem padRight_encode_eq {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (pad : Nat) (x : α) :
    (padRight c pad).encode x = c.encode x ++ List.replicate pad AllocByte.uninit :=
  rfl

theorem padLeft_decode_of_length_eq {α : Type} {n : Nat} (pad : Nat)
    (c : FixedByteCodec α n) {bs : List AllocByte}
    (hLen : bs.length = pad + n) :
    (padLeft pad c).decode bs = c.decode (bs.drop pad) := by
  unfold padLeft imap prod padUninit ofRoundTrip
  dsimp only
  have hBeq : Nat.beq bs.length (pad + n) = true := (nat_beq_iff _ _).mpr hLen
  rw [ite_true_of hBeq]
  have hTakeLen : (bs.take pad).length = pad := by
    apply fbc_length_take_of_le
    rw [hLen]
    exact Nat.le_add_right pad n
  have hPadBeq : Nat.beq (bs.take pad).length pad = true :=
    (nat_beq_iff _ _).mpr hTakeLen
  rw [ite_true_of hPadBeq]
  cases c.decode (bs.drop pad) <;> rfl

theorem padRight_decode_of_length_eq {α : Type} {n : Nat}
    (c : FixedByteCodec α n) (pad : Nat) {bs : List AllocByte}
    (hLen : bs.length = n + pad) :
    (padRight c pad).decode bs = c.decode (bs.take n) := by
  unfold padRight imap prod padUninit ofRoundTrip
  dsimp only
  have hBeq : Nat.beq bs.length (n + pad) = true := (nat_beq_iff _ _).mpr hLen
  rw [ite_true_of hBeq]
  have hDropLen : (bs.drop n).length = pad := by
    rw [fbc_length_drop, hLen, Nat.add_sub_cancel_left]
  have hPadBeq : Nat.beq (bs.drop n).length pad = true :=
    (nat_beq_iff _ _).mpr hDropLen
  rw [ite_true_of hPadBeq]
  cases c.decode (bs.take n) <;> rfl

theorem padLeft_noProvCodec {α : Type} {n : Nat} (pad : Nat)
    {c : FixedByteCodec α n} (hNoProv : c.NoProvCodec) :
    (padLeft pad c).NoProvCodec :=
  imap_noProvCodec _ _ _ _ _
    (prod_noProvCodec (padUninit_noProvCodec pad) hNoProv)

theorem padRight_noProvCodec {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (pad : Nat) (hNoProv : c.NoProvCodec) :
    (padRight c pad).NoProvCodec :=
  imap_noProvCodec _ _ _ _ _
    (prod_noProvCodec hNoProv (padUninit_noProvCodec pad))

/-- Padding on the left preserves total decoding of initialized buffers
(`FromBytes`-style closure under padding). -/
theorem padLeft_isSurjectiveInitDecoder {α : Type} {n : Nat} (pad : Nat)
    {c : FixedByteCodec α n} (hSurj : c.IsSurjectiveInitDecoder) :
    (padLeft pad c).IsSurjectiveInitDecoder :=
  imap_isSurjectiveInitDecoder _ _ _ _ _
    (prod_isSurjectiveInitDecoder (padUninit_isSurjectiveInitDecoder pad) hSurj)

/-- Padding on the right preserves total decoding of initialized buffers
(`FromBytes`-style closure under padding). -/
theorem padRight_isSurjectiveInitDecoder {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (pad : Nat) (hSurj : c.IsSurjectiveInitDecoder) :
    (padRight c pad).IsSurjectiveInitDecoder :=
  imap_isSurjectiveInitDecoder _ _ _ _ _
    (prod_isSurjectiveInitDecoder hSurj (padUninit_isSurjectiveInitDecoder pad))

/-- Padding on the left preserves `HasZeroValid` (`FromZeros` closure). -/
theorem padLeft_hasZeroValid {α : Type} {n : Nat} (pad : Nat)
    {c : FixedByteCodec α n} (hZero : c.HasZeroValid) :
    (padLeft pad c).HasZeroValid :=
  imap_hasZeroValid _ _ _ _ _
    (prod_hasZeroValid (padUninit_hasZeroValid pad) hZero)

/-- Padding on the right preserves `HasZeroValid` (`FromZeros` closure). -/
theorem padRight_hasZeroValid {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (pad : Nat) (hZero : c.HasZeroValid) :
    (padRight c pad).HasZeroValid :=
  imap_hasZeroValid _ _ _ _ _
    (prod_hasZeroValid hZero (padUninit_hasZeroValid pad))

/-- Positive left padding always emits uninitialized bytes (`allBytesInit =
false`). -/
theorem allBytesInit_padLeft_encode_eq_false {α : Type} {n pad : Nat}
    (hPos : 0 < pad) (c : FixedByteCodec α n) (x : α) :
    allBytesInit ((padLeft pad c).encode x) = false := by
  rw [padLeft_encode_eq]
  exact fbc_allBytesInit_append_false_left _ (c.encode x)
    (fbc_allBytesInit_replicate_uninit_pos hPos)

/-- Positive right padding always emits uninitialized bytes (`allBytesInit =
false`). -/
theorem allBytesInit_padRight_encode_eq_false {α : Type} {n pad : Nat}
    (c : FixedByteCodec α n) (hPos : 0 < pad) (x : α) :
    allBytesInit ((padRight c pad).encode x) = false := by
  rw [padRight_encode_eq]
  exact fbc_allBytesInit_append_false_right (c.encode x) _
    (fbc_allBytesInit_replicate_uninit_pos hPos)

/-- Any inhabited codec with `0 < pad` left padding violates `IsInitCodec`. -/
theorem padLeft_not_isInitCodec {α : Type} {n pad : Nat}
    (hPos : 0 < pad) (c : FixedByteCodec α n) (x₀ : α) :
    ¬ (padLeft pad c).IsInitCodec := by
  intro hInit
  have hTrue : allBytesInit ((padLeft pad c).encode x₀) = true := hInit x₀
  rw [allBytesInit_padLeft_encode_eq_false hPos c x₀] at hTrue
  nomatch hTrue

/-- Any inhabited codec with `0 < pad` right padding violates `IsInitCodec`.
-/
theorem padRight_not_isInitCodec {α : Type} {n pad : Nat}
    (c : FixedByteCodec α n) (hPos : 0 < pad) (x₀ : α) :
    ¬ (padRight c pad).IsInitCodec := by
  intro hInit
  have hTrue : allBytesInit ((padRight c pad).encode x₀) = true := hInit x₀
  rw [allBytesInit_padRight_encode_eq_false c hPos x₀] at hTrue
  nomatch hTrue

theorem padLeft_zero_isInitCodec {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hInit : c.IsInitCodec) :
    (padLeft 0 c).IsInitCodec :=
  imap_isInitCodec _ _ _ _ _
    (prod_isInitCodec padUninit_zero_isInitCodec hInit)

theorem padRight_zero_isInitCodec {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hInit : c.IsInitCodec) :
    (padRight c 0).IsInitCodec :=
  imap_isInitCodec _ _ _ _ _
    (prod_isInitCodec hInit padUninit_zero_isInitCodec)

/-- Exact characterization of `IsInitCodec` for `padLeft` over an inhabited
type. -/
theorem padLeft_isInitCodec_iff {α : Type} {n pad : Nat}
    (c : FixedByteCodec α n) (x₀ : α) :
    (padLeft pad c).IsInitCodec ↔ pad = 0 ∧ c.IsInitCodec := by
  cases pad with
  | zero =>
    constructor
    · intro hInit
      refine ⟨rfl, fun x => ?_⟩
      have hx : allBytesInit ((padLeft 0 c).encode x) = true := hInit x
      rw [padLeft_encode_eq, List.replicate_zero, List.nil_append] at hx
      exact hx
    · intro hPair
      exact padLeft_zero_isInitCodec hPair.2
  | succ k =>
    constructor
    · intro hInit
      exact False.elim (padLeft_not_isInitCodec (Nat.zero_lt_succ k) c x₀ hInit)
    · intro hPair
      nomatch hPair.1

/-- Exact characterization of `IsInitCodec` for `padRight` over an inhabited
type. -/
theorem padRight_isInitCodec_iff {α : Type} {n pad : Nat}
    (c : FixedByteCodec α n) (x₀ : α) :
    (padRight c pad).IsInitCodec ↔ pad = 0 ∧ c.IsInitCodec := by
  cases pad with
  | zero =>
    constructor
    · intro hInit
      refine ⟨rfl, fun x => ?_⟩
      have hx : allBytesInit ((padRight c 0).encode x) = true := hInit x
      rw [padRight_encode_eq, List.replicate_zero, List.append_nil] at hx
      exact hx
    · intro hPair
      exact padRight_zero_isInitCodec hPair.2
  | succ k =>
    constructor
    · intro hInit
      exact False.elim (padRight_not_isInitCodec c (Nat.zero_lt_succ k) x₀ hInit)
    · intro hPair
      nomatch hPair.1

/-! ### 2d. Fixed-Count Homogeneous Array Codec (`array`) -/

/-- Encode a list of elements sequentially by concatenating `c.encode` using
`List.foldr` (`0` `._unsafe_rec` auxiliaries). -/
@[expose] def encodeElems {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (xs : List α) : List AllocByte :=
  xs.foldr (fun x acc => c.encode x ++ acc) []

@[simp] theorem encodeElems_nil {α : Type} {n : Nat}
    (c : FixedByteCodec α n) : encodeElems c [] = [] := rfl

@[simp] theorem encodeElems_cons {α : Type} {n : Nat}
    (c : FixedByteCodec α n) (x : α) (xs : List α) :
    encodeElems c (x :: xs) = c.encode x ++ encodeElems c xs := rfl

theorem length_encodeElems {α : Type} {n : Nat} (c : FixedByteCodec α n) :
    ∀ xs : List α, (encodeElems c xs).length = xs.length * n
  | [] => by rw [encodeElems_nil, List.length_nil, List.length_nil, Nat.zero_mul]
  | x :: xs => by
    rw [encodeElems_cons, List.length_append, c.encode_length x,
        length_encodeElems c xs, List.length_cons, Nat.succ_mul, Nat.add_comm n]

theorem allBytesInit_encodeElems {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hInit : c.IsInitCodec) :
    ∀ xs : List α, AllBytesInit (encodeElems c xs)
  | [] => rfl
  | x :: xs => AllBytesInit_append (hInit x) (allBytesInit_encodeElems hInit xs)

theorem noProvBytes_encodeElems {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hNoProv : c.NoProvCodec) :
    ∀ xs : List α, NoProvBytes (encodeElems c xs)
  | [] => rfl
  | x :: xs => NoProvBytes_append (hNoProv x) (noProvBytes_encodeElems hNoProv xs)

/-- Decode `k` consecutive `n`-byte chunks into
`Subtype (fun xs : List α => xs.length = k)` using `@Nat.rec` (`0`
`._unsafe_rec` auxiliaries). -/
@[expose] def decodeChunks {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (k : Nat) (bs : List AllocByte) :
    Option (Subtype (fun xs : List α => xs.length = k)) :=
  @Nat.rec
    (fun m => List AllocByte → Option (Subtype (fun xs : List α => xs.length = m)))
    (fun cur => match cur with | [] => some ⟨[], rfl⟩ | _ :: _ => none)
    (fun _ ih cur =>
      if Nat.ble n cur.length then
        match c.decode (cur.take n), ih (cur.drop n) with
        | some x, some ⟨xs, hxs⟩ => some ⟨x :: xs, congrArg Nat.succ hxs⟩
        | _, _ => none
      else
        none)
    k bs

theorem decodeChunks_zero_nil {α : Type} {n : Nat} (c : FixedByteCodec α n) :
    decodeChunks c 0 [] = some ⟨[], rfl⟩ := rfl

theorem decodeChunks_zero_cons {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (b : AllocByte) (rest : List AllocByte) :
    decodeChunks c 0 (b :: rest) = none := rfl

theorem decodeChunks_succ {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (k : Nat) (bs : List AllocByte) :
    decodeChunks c (k + 1) bs =
      (if Nat.ble n bs.length then
        match c.decode (bs.take n), decodeChunks c k (bs.drop n) with
        | some x, some ⟨xs, hxs⟩ => some ⟨x :: xs, congrArg Nat.succ hxs⟩
        | _, _ => none
      else
        none) := rfl

theorem decodeChunks_encodeElems {α : Type} {n : Nat}
    (c : FixedByteCodec α n) :
    ∀ (k : Nat) (xs : List α) (hLen : xs.length = k),
      decodeChunks c k (encodeElems c xs) = some ⟨xs, hLen⟩
  | 0, [], _ => rfl
  | 0, _ :: _, hLen => by nomatch hLen
  | k + 1, x :: xs, hLen => by
    have hTail : xs.length = k := Nat.succ.inj hLen
    subst hTail
    rw [encodeElems_cons, decodeChunks_succ]
    have hGe : n ≤ (c.encode x ++ encodeElems c xs).length := by
      rw [List.length_append, c.encode_length x]
      exact Nat.le_add_right n _
    rw [ite_true_of (Nat.ble_eq.mpr hGe),
        c.take_append_encode x (encodeElems c xs),
        c.drop_append_encode x (encodeElems c xs),
        c.decode_encode x,
        decodeChunks_encodeElems c xs.length xs rfl]

theorem decodeChunks_length_eq {α : Type} {n : Nat} (c : FixedByteCodec α n) :
    ∀ {k : Nat} {bs : List AllocByte}
      {res : Subtype (fun xs : List α => xs.length = k)},
      decodeChunks c k bs = some res → bs.length = k * n
  | 0, [], _, _ => by rw [List.length_nil, Nat.zero_mul]
  | 0, _ :: _, _, hDec => by nomatch hDec
  | k + 1, bs, _, hDec => by
    rw [decodeChunks_succ] at hDec
    cases hBle : Nat.ble n bs.length with
    | false =>
      rw [ite_false_of (by rw [hBle]; exact fbc_false_ne_true)] at hDec
      nomatch hDec
    | true =>
      rw [ite_true_of hBle] at hDec
      cases hHead : c.decode (bs.take n) with
      | none =>
        rw [hHead] at hDec
        nomatch hDec
      | some _ =>
        rw [hHead] at hDec
        cases hTail : decodeChunks c k (bs.drop n) with
        | none =>
          rw [hTail] at hDec
          nomatch hDec
        | some tailSub =>
          have hLe : n ≤ bs.length := Nat.ble_eq.mp hBle
          have hDropLen : (bs.drop n).length = k * n :=
            decodeChunks_length_eq c hTail
          rw [fbc_length_drop] at hDropLen
          have hAdd : bs.length - n + n = k * n + n :=
            congrArg (fun z => z + n) hDropLen
          rw [Nat.sub_add_cancel hLe] at hAdd
          rw [hAdd, Nat.succ_mul]

/-- Homogeneous fixed-length array codec of `k` elements (`k * n` bytes). -/
@[expose] def array {α : Type} {n : Nat} (k : Nat) (c : FixedByteCodec α n) :
    FixedByteCodec (Subtype (fun xs : List α => xs.length = k)) (k * n) :=
  ofRoundTrip
    (fun xs => encodeElems c xs.val)
    (fun bs => decodeChunks c k bs)
    (fun xs => by rw [length_encodeElems c xs.val, xs.property])
    (fun ⟨xs, hLen⟩ => decodeChunks_encodeElems c k xs hLen)
    (fun _ _ h => decodeChunks_length_eq c h)

theorem array_isInitCodec {α : Type} {n : Nat} (k : Nat)
    {c : FixedByteCodec α n} (hInit : c.IsInitCodec) :
    (array k c).IsInitCodec :=
  fun xs => allBytesInit_encodeElems hInit xs.val

theorem array_noProvCodec {α : Type} {n : Nat} (k : Nat)
    {c : FixedByteCodec α n} (hNoProv : c.NoProvCodec) :
    (array k c).NoProvCodec :=
  fun xs => noProvBytes_encodeElems hNoProv xs.val

theorem array_isSurjectiveInitDecoder {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hSurj : c.IsSurjectiveInitDecoder) :
    ∀ k : Nat, (array k c).IsSurjectiveInitDecoder
  | 0 => fun bs hLen _ => by
    rw [Nat.zero_mul] at hLen
    cases bs with
    | nil => exact ⟨⟨[], rfl⟩, rfl⟩
    | cons _ _ => nomatch hLen
  | k + 1 => fun bs hLen hInit => by
    have hMul : (k + 1) * n = n + k * n := by
      rw [Nat.succ_mul, Nat.add_comm (k * n) n]
    have hLe : n ≤ bs.length := by
      rw [hLen, hMul]
      exact Nat.le_add_right n _
    have hTakeLen : (bs.take n).length = n := fbc_length_take_of_le hLe
    have hDropLen : (bs.drop n).length = k * n := by
      rw [fbc_length_drop, hLen, hMul, Nat.add_sub_cancel_left]
    have ⟨x, hx⟩ := hSurj (bs.take n) hTakeLen (fbc_allBytesInit_take n bs hInit)
    have ⟨⟨xs, hxs⟩, hRest⟩ :=
      array_isSurjectiveInitDecoder hSurj k (bs.drop n) hDropLen
        (fbc_allBytesInit_drop n bs hInit)
    refine ⟨⟨x :: xs, congrArg Nat.succ hxs⟩, ?_⟩
    change decodeChunks c (k + 1) bs = some ⟨x :: xs, congrArg Nat.succ hxs⟩
    rw [decodeChunks_succ, ite_true_of (Nat.ble_eq.mpr hLe), hx]
    have hRestChunks : decodeChunks c k (bs.drop n) = some ⟨xs, hxs⟩ := hRest
    rw [hRestChunks]

theorem array_hasZeroValid {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hZero : c.HasZeroValid) :
    ∀ k : Nat, (array k c).HasZeroValid
  | 0 =>
    ⟨⟨[], rfl⟩, by
      have hZ : zeroInitBytes (0 * n) = [] := by
        rw [Nat.zero_mul]
        rfl
      change decodeChunks c 0 (zeroInitBytes (0 * n)) = some ⟨[], rfl⟩
      rw [hZ]
      rfl⟩
  | k + 1 => by
    have ⟨x, hx⟩ := hZero
    have ⟨⟨xs, hxs⟩, hRest⟩ := array_hasZeroValid hZero k
    have hMul : (k + 1) * n = n + k * n := by
      rw [Nat.succ_mul, Nat.add_comm (k * n) n]
    refine ⟨⟨x :: xs, congrArg Nat.succ hxs⟩, ?_⟩
    change
      decodeChunks c (k + 1) (zeroInitBytes ((k + 1) * n)) =
        some ⟨x :: xs, congrArg Nat.succ hxs⟩
    rw [hMul, zeroInitBytes_add n (k * n), decodeChunks_succ]
    have hGe : n ≤ (zeroInitBytes n ++ zeroInitBytes (k * n)).length := by
      rw [List.length_append, length_zeroInitBytes]
      exact Nat.le_add_right n _
    rw [ite_true_of (Nat.ble_eq.mpr hGe),
        fbc_take_append_left_eq _ _ (length_zeroInitBytes n),
        fbc_drop_append_left_eq _ _ (length_zeroInitBytes n), hx]
    have hRestChunks :
        decodeChunks c k (zeroInitBytes (k * n)) = some ⟨xs, hxs⟩ := hRest
    rw [hRestChunks]

theorem array_decode_eq_none_of_head_none {α : Type} {n : Nat}
    (k : Nat) (c : FixedByteCodec α n) {bs : List AllocByte}
    (hHead : c.decode (bs.take n) = none) :
    (array (k + 1) c).decode bs = none := by
  change decodeChunks c (k + 1) bs = none
  rw [decodeChunks_succ]
  cases Nat.ble n bs.length with
  | false => exact fbc_if_false _ _
  | true =>
    rw [fbc_if_true, hHead]

theorem array_decode_eq_none_of_tail_none {α : Type} {n : Nat}
    (k : Nat) (c : FixedByteCodec α n) {bs : List AllocByte}
    (hTail : (array k c).decode (bs.drop n) = none) :
    (array (k + 1) c).decode bs = none := by
  change decodeChunks c (k + 1) bs = none
  have hTailChunks : decodeChunks c k (bs.drop n) = none := hTail
  rw [decodeChunks_succ]
  cases Nat.ble n bs.length with
  | false => exact fbc_if_false _ _
  | true =>
    rw [fbc_if_true]
    cases c.decode (bs.take n) with
    | none => rfl
    | some _ => rw [hTailChunks]

/-- Chunking `(encodeElems c xs)` with `ListChunks.chunksOf n` recovers
`xs.map c.encode` whenever `0 < n`. -/
theorem chunksOf_encodeElems {α : Type} {n : Nat} (hn : 0 < n)
    (c : FixedByteCodec α n) :
    ∀ xs : List α, chunksOf n (encodeElems c xs) = xs.map c.encode
  | [] => by rw [encodeElems_nil, chunksOf_nil, List.map_nil]
  | x :: xs => by
    rw [encodeElems_cons, chunksOf_append_exact hn (c.encode x) (encodeElems c xs)
        (by rw [c.encode_length x, Nat.mod_self])]
    have hSingle : chunksOf n (c.encode x) = [c.encode x] := by
      cases hBs : c.encode x with
      | nil =>
        have hLen := c.encode_length x
        rw [hBs, List.length_nil] at hLen
        rw [← hLen] at hn
        exact False.elim (Nat.lt_irrefl 0 hn)
      | cons b rest =>
        have hLen : (b :: rest).length = n := by rw [← hBs, c.encode_length x]
        rw [chunksOf_cons hn, fbc_take_all_of_le n (b :: rest) (Nat.le_of_eq hLen),
            fbc_drop_all_of_le n (b :: rest) (Nat.le_of_eq hLen), chunksOf_nil]
    rw [hSingle, chunksOf_encodeElems hn c xs, List.map_cons]
    rfl

/-- Element-level `ListChunks` indexing law for `(array k c).encode`. -/
theorem chunksOf_array_encode_getElem? {α : Type} {n : Nat} (hn : 0 < n)
    (k : Nat) (c : FixedByteCodec α n)
    (xs : Subtype (fun xs : List α => xs.length = k)) (i : Nat) :
    (chunksOf n ((array k c).encode xs))[i]? = (xs.val[i]?).map c.encode := by
  change (chunksOf n (encodeElems c xs.val))[i]? = _
  rw [chunksOf_encodeElems hn c xs.val]
  induction xs.val generalizing i with
  | nil =>
    cases i <;> rfl
  | cons x rest ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change ((c.encode x :: rest.map c.encode)[i + 1]?) =
        ((x :: rest)[i + 1]?).map c.encode
      exact ih i

/-- Element `drop`/`take` slice projection of `encodeElems c xs` (for every
element width `n`, including `n = 0`). -/
theorem encodeElems_drop_take_of_getElem? {α : Type} {n : Nat}
    (c : FixedByteCodec α n) :
    ∀ {i : Nat} {xs : List α} {x : α},
      xs[i]? = some x →
      ((encodeElems c xs).drop (i * n)).take n = c.encode x
  | 0, [], _, h => by nomatch h
  | 0, y :: rest, x, h => by
    have hyx : some y = some x := h
    injection hyx with hy
    subst hy
    rw [Nat.zero_mul, List.drop_zero, encodeElems_cons]
    exact c.take_append_encode y (encodeElems c rest)
  | i + 1, [], _, h => by nomatch h
  | i + 1, y :: rest, x, h => by
    have hRest : rest[i]? = some x := h
    rw [Nat.succ_mul, Nat.add_comm (i * n) n, ← fbc_drop_drop, encodeElems_cons,
        c.drop_append_encode y (encodeElems c rest)]
    exact encodeElems_drop_take_of_getElem? c hRest

/-- Decoding element `i` directly via `(bs.drop (i * n)).take n` agrees with
`(array k c).decode bs` at index `i`. -/
theorem decode_array_elem_of_getElem? {α : Type} {n : Nat}
    (c : FixedByteCodec α n) :
    ∀ {k i : Nat} {bs : List AllocByte}
      {xs : Subtype (fun xs : List α => xs.length = k)} {x : α},
      (array k c).decode bs = some xs →
      xs.val[i]? = some x →
      c.decode ((bs.drop (i * n)).take n) = some x
  | 0, i, [], ⟨[], _⟩, _, _, hGet => by cases i <;> nomatch hGet
  | 0, _, _ :: _, _, _, hDec, _ => by nomatch hDec
  | k + 1, i, bs, ⟨xs, hxs⟩, x, hDec, hGet => by
    change decodeChunks c (k + 1) bs = some ⟨xs, hxs⟩ at hDec
    rw [decodeChunks_succ] at hDec
    cases hBle : Nat.ble n bs.length with
    | false =>
      rw [ite_false_of (by rw [hBle]; exact fbc_false_ne_true)] at hDec
      nomatch hDec
    | true =>
      rw [ite_true_of hBle] at hDec
      cases hHead : c.decode (bs.take n) with
      | none =>
        rw [hHead] at hDec
        nomatch hDec
      | some y =>
        rw [hHead] at hDec
        cases hTail : decodeChunks c k (bs.drop n) with
        | none =>
          rw [hTail] at hDec
          nomatch hDec
        | some tailSub =>
          rw [hTail] at hDec
          injection hDec with hSub
          cases tailSub with
          | mk ys hys =>
            dsimp only at hSub
            have hListEq : y :: ys = xs := congrArg Subtype.val hSub
            subst hListEq
            cases i with
            | zero =>
              have hyx : some y = some x := hGet
              injection hyx with hy
              subst hy
              rw [Nat.zero_mul, List.drop_zero]
              exact hHead
            | succ i =>
              have hTailArr :
                  (array k c).decode (bs.drop n) = some ⟨ys, hys⟩ := hTail
              have hGetTail : ys[i]? = some x := hGet
              rw [Nat.succ_mul, Nat.add_comm (i * n) n, ← fbc_drop_drop]
              exact decode_array_elem_of_getElem? c hTailArr hGetTail

/-! ### 2e. Niche Refinement (`refineNiche`) -/

/-- Refine `c` by a decidable predicate `P : α → Bool`, capturing Rust niche
types (`bool`, `NonZero*`, enums whose discriminants do not cover every bit
pattern). -/
@[expose] def refineNiche {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (P : α → Bool) : FixedByteCodec (Subtype (fun x : α => P x = true)) n :=
  ofRoundTrip
    (fun sub => c.encode sub.val)
    (fun bs =>
      match c.decode bs with
      | none => none
      | some x => if h : P x = true then some ⟨x, h⟩ else none)
    (fun sub => c.encode_length sub.val)
    (fun ⟨x, hx⟩ => by
      dsimp only
      rw [c.decode_encode x]
      exact dite_true_of hx)
    (by
      intro bs _ h
      cases hc : c.decode bs with
      | none =>
        rw [hc] at h
        nomatch h
      | some _ => exact c.decode_length hc)

theorem refineNiche_isInitCodec {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (P : α → Bool) (hInit : c.IsInitCodec) :
    (c.refineNiche P).IsInitCodec :=
  fun sub => hInit sub.val

theorem refineNiche_noProvCodec {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (P : α → Bool) (hNoProv : c.NoProvCodec) :
    (c.refineNiche P).NoProvCodec :=
  fun sub => hNoProv sub.val

theorem refineNiche_decode_rejects_false {α : Type} {n : Nat}
    (c : FixedByteCodec α n) (P : α → Bool)
    {bs : List AllocByte} {x : α}
    (hDec : c.decode bs = some x) (hFalse : P x = false) :
    (c.refineNiche P).decode bs = none := by
  unfold refineNiche ofRoundTrip
  dsimp only
  rw [hDec]
  exact dite_false_of (by rw [hFalse]; exact fbc_false_ne_true)

theorem refineNiche_not_isSurjectiveInitDecoder {α : Type} {n : Nat}
    (c : FixedByteCodec α n) (P : α → Bool)
    {bs : List AllocByte} (hLen : bs.length = n) (hInit : AllBytesInit bs)
    {x : α} (hDec : c.decode bs = some x) (hFalse : P x = false) :
    ¬ (c.refineNiche P).IsSurjectiveInitDecoder := by
  intro hSurj
  have ⟨sub, hSub⟩ := hSurj bs hLen hInit
  rw [refineNiche_decode_rejects_false c P hDec hFalse] at hSub
  nomatch hSub

end FixedByteCodec

/-! ## 3. Endian-Parametric Primitives, `LeBytes`, and `MirSemantics.Bytes` -/

/-- Total computable extraction of raw `UInt8` bytes from initialized
`List AllocByte` via `List.foldr` (`0` `._unsafe_rec`), agreeing with
`Trusted.MirSemantics.initBytes?`. -/
@[expose] def rawBytes? (bs : List AllocByte) : Option (List UInt8) :=
  bs.foldr
    (fun ab acc =>
      match ab with
      | .uninit => none
      | .init b _ =>
        match acc with
        | some tl => some (b :: tl)
        | none => none)
    (some [])

theorem rawBytes?_eq_initBytes? :
    ∀ bs : List AllocByte, rawBytes? bs = initBytes? bs
  | [] => rfl
  | .uninit :: _ => rfl
  | .init b _ :: rest => by
    change
      (match rawBytes? rest with | some tl => some (b :: tl) | none => none) =
        (match initBytes? rest with | some tl => some (b :: tl) | none => none)
    rw [rawBytes?_eq_initBytes? rest]

theorem rawBytes?_map_init_none (bs : List UInt8) :
    rawBytes? (bs.map (fun b => AllocByte.init b none)) = some bs := by
  rw [rawBytes?_eq_initBytes?]
  have h := initBytes?_map_init_none id bs
  rw [fbc_map_id] at h
  exact h

private theorem ui8_ofBitVec_ofNat (v : Nat) :
    UInt8.ofBitVec (BitVec.ofNat 8 v) = UInt8.ofNat (HMod.hMod v 256) := by
  apply fbc_uint8_eq_of_toNat_eq
  change (BitVec.ofNat 8 v).toNat = (UInt8.ofNat (HMod.hMod v 256)).toNat
  rw [fbc_bv_toNat_ofNat, fbc_two_pow_eight]
  change HMod.hMod v 256 = (BitVec.ofNat 8 (HMod.hMod v 256)).toNat
  rw [fbc_bv_toNat_ofNat, fbc_two_pow_eight,
      Nat.mod_eq_of_lt (Nat.mod_lt v (by decide : 0 < 256))]

theorem toLeBytesAux_map_ofBitVec_eq_leBytesOfNat :
    ∀ n v : Nat,
      (toLeBytesAux n v).map UInt8.ofBitVec = leBytesOfNat n v
  | 0, _ => rfl
  | n + 1, v => by
    rw [toLeBytesAux_succ, List.map_cons, ui8_ofBitVec_ofNat,
        toLeBytesAux_map_ofBitVec_eq_leBytesOfNat n (HDiv.hDiv v 256)]
    rfl

theorem toLeBytes_eq_encodeUInt_little (n : Nat) (x : BitVec (n * 8)) :
    (toLeBytes n x).map UInt8.ofBitVec = encodeUInt .little n x.toNat :=
  toLeBytesAux_map_ofBitVec_eq_leBytesOfNat n x.toNat

theorem toBeBytes_eq_encodeUInt_big (n : Nat) (x : BitVec (n * 8)) :
    (toBeBytes n x).map UInt8.ofBitVec = encodeUInt .big n x.toNat := by
  unfold toBeBytes encodeUInt
  rw [← fbc_map_reverse, toLeBytes_eq_encodeUInt_little]
  rfl

theorem natOfLeBytes_eq_fromLeBytes :
    ∀ bs : List UInt8, natOfLeBytes bs = fromLeBytes (bs.map UInt8.toBitVec)
  | [] => rfl
  | b :: rest => by
    change b.toNat + 256 * natOfLeBytes rest =
      b.toBitVec.toNat + 256 * fromLeBytes (rest.map UInt8.toBitVec)
    rw [natOfLeBytes_eq_fromLeBytes rest]
    rfl

theorem decodeUInt_eq_fromBytes (endian : TargetEndian) (bs : List UInt8) :
    decodeUInt endian bs =
      match endian with
      | .little => fromLeBytes (bs.map UInt8.toBitVec)
      | .big => fromBeBytes (bs.map UInt8.toBitVec) := by
  cases endian with
  | little => exact natOfLeBytes_eq_fromLeBytes bs
  | big =>
    unfold decodeUInt fromBeBytes
    rw [fbc_map_reverse, natOfLeBytes_eq_fromLeBytes bs.reverse]

/-- Computable `0`-byte `Unit` codec matching `MirTy.unit`. -/
@[expose] def unitCodec : FixedByteCodec Unit 0 := FixedByteCodec.zst

/-- Computable `1`-byte Rust `bool` codec (`0x00 ↦ false`, `0x01 ↦ true`,
rejecting `≥ 2` and `.uninit`). -/
@[expose] def boolCodec : FixedByteCodec Bool 1 :=
  FixedByteCodec.ofRoundTrip
    (fun b => [AllocByte.init (if b then 1 else 0) none])
    (fun bs =>
      match bs with
      | [.init b _] =>
        if Nat.beq b.toNat 0 then some false
        else if Nat.beq b.toNat 1 then some true
        else none
      | _ => none)
    (fun b => by cases b <;> rfl)
    (fun b => by cases b <;> rfl)
    (by
      intro bs _ h
      cases bs with
      | nil => nomatch h
      | cons b0 rest =>
        cases b0 with
        | uninit => nomatch h
        | init _ _ =>
          cases rest with
          | nil => rfl
          | cons _ _ => nomatch h)

theorem boolCodec_isInitCodec : boolCodec.IsInitCodec := by
  intro b
  cases b <;> rfl

theorem boolCodec_noProvCodec : boolCodec.NoProvCodec := by
  intro b
  cases b <;> rfl

theorem boolCodec_hasZeroValid : boolCodec.HasZeroValid :=
  ⟨false, rfl⟩

theorem boolCodec_decode_invalid_of_ge_two (b : UInt8)
    (prov : Option AllocId) (hGe : 2 ≤ b.toNat) :
    boolCodec.decode [.init b prov] = none := by
  have hNe0 : Nat.beq b.toNat 0 = false := by
    cases h0 : Nat.beq b.toNat 0 with
    | false => rfl
    | true =>
      rw [nat_eq_of_beq h0] at hGe
      nomatch hGe
  have hNe1 : Nat.beq b.toNat 1 = false := by
    cases h1 : Nat.beq b.toNat 1 with
    | false => rfl
    | true =>
      rw [nat_eq_of_beq h1] at hGe
      nomatch hGe
  unfold boolCodec FixedByteCodec.ofRoundTrip
  dsimp only
  rw [ite_false_of (by rw [hNe0]; exact fbc_false_ne_true),
      ite_false_of (by rw [hNe1]; exact fbc_false_ne_true)]

theorem boolCodec_not_isSurjectiveInitDecoder :
    ¬ boolCodec.IsSurjectiveInitDecoder := by
  intro hSurj
  have ⟨_, hDec⟩ := hSurj [.init 2 none] rfl rfl
  nomatch hDec

private theorem fromLeBytes_map_ofBitVec (bs : List (BitVec 8)) :
    fromLeBytes ((bs.map UInt8.ofBitVec).map UInt8.toBitVec) = fromLeBytes bs := by
  rw [fbc_map_comp]
  have hId : (fun b : BitVec 8 => (UInt8.ofBitVec b).toBitVec) = id := by
    funext b
    rfl
  rw [hId, fbc_map_id]

private theorem encodeUInt_bv_bytes (endian : TargetEndian) (sz : Nat)
    (x : BitVec (sz * 8)) :
    (match endian with
     | .little => toLeBytes sz x
     | .big => toBeBytes sz x).map (fun b => AllocByte.init (UInt8.ofBitVec b) none) =
      (encodeUInt endian sz x.toNat).map (fun b => AllocByte.init b none) := by
  cases endian with
  | little =>
    rw [← toLeBytes_eq_encodeUInt_little sz x, fbc_map_comp]
  | big =>
    rw [← toBeBytes_eq_encodeUInt_big sz x, fbc_map_comp]

/-- Endian-parametric computable `FixedByteCodec` for any positive byte width
`sz` over `BitVec (sz * 8)` backed by `Anneal.LeBytes`. -/
@[expose] def uintBvCodec (endian : TargetEndian) (sz : Nat) (hPos : 0 < sz) :
    FixedByteCodec (BitVec (sz * 8)) sz :=
  let _ := hPos
  FixedByteCodec.ofRoundTrip
    (fun x =>
      let raw :=
        match endian with
        | .little => toLeBytes sz x
        | .big => toBeBytes sz x
      raw.map (fun b => AllocByte.init (UInt8.ofBitVec b) none))
    (fun bs =>
      if Nat.beq bs.length sz then
        match rawBytes? bs with
        | none => none
        | some raw =>
          let n :=
            match endian with
            | .little => fromLeBytes (raw.map UInt8.toBitVec)
            | .big => fromBeBytes (raw.map UInt8.toBitVec)
          some (BitVec.ofNat (sz * 8) n)
      else
        none)
    (fun x => by
      cases endian with
      | little => rw [length_map_eq, toLeBytes_length]
      | big => rw [length_map_eq, toBeBytes_length])
    (fun x => by
      cases endian with
      | little =>
        have hLen :
            ((toLeBytes sz x).map
              (fun b => AllocByte.init (UInt8.ofBitVec b) none)).length = sz := by
          rw [length_map_eq, toLeBytes_length]
        have hBeq : Nat.beq _ sz = true := (nat_beq_iff _ _).mpr hLen
        dsimp only
        rw [ite_true_of hBeq,
            ← fbc_map_comp (fun b => AllocByte.init b none) UInt8.ofBitVec
              (toLeBytes sz x),
            rawBytes?_map_init_none]
        dsimp only
        rw [fromLeBytes_map_ofBitVec, fromLeBytes_toLeBytes]
        exact congrArg some (fbc_bv_eq_of_toNat_eq (by
          rw [fbc_bv_toNat_ofNat]
          exact Nat.mod_eq_of_lt x.isLt))
      | big =>
        have hLen :
            ((toBeBytes sz x).map
              (fun b => AllocByte.init (UInt8.ofBitVec b) none)).length = sz := by
          rw [length_map_eq, toBeBytes_length]
        have hBeq : Nat.beq _ sz = true := (nat_beq_iff _ _).mpr hLen
        dsimp only
        rw [ite_true_of hBeq,
            ← fbc_map_comp (fun b => AllocByte.init b none) UInt8.ofBitVec
              (toBeBytes sz x),
            rawBytes?_map_init_none]
        dsimp only
        unfold fromBeBytes
        rw [fbc_map_comp]
        have hId : (fun b : BitVec 8 => (UInt8.ofBitVec b).toBitVec) = id := by
          funext b
          rfl
        rw [hId, fbc_map_id]
        unfold toBeBytes
        rw [fbc_reverse_reverse, fromLeBytes_toLeBytes]
        exact congrArg some (fbc_bv_eq_of_toNat_eq (by
          rw [fbc_bv_toNat_ofNat]
          exact Nat.mod_eq_of_lt x.isLt)))
    (by
      intro bs _ h
      cases hBeq : Nat.beq bs.length sz with
      | false =>
        rw [ite_false_of (by rw [hBeq]; exact fbc_false_ne_true)] at h
        nomatch h
      | true => exact nat_eq_of_beq hBeq)

theorem uintBvCodec_encode_little (sz : Nat) (hPos : 0 < sz)
    (x : BitVec (sz * 8)) :
    (uintBvCodec .little sz hPos).encode x =
      (toLeBytes sz x).map (fun b => AllocByte.init (UInt8.ofBitVec b) none) := rfl

theorem uintBvCodec_encode_big (sz : Nat) (hPos : 0 < sz)
    (x : BitVec (sz * 8)) :
    (uintBvCodec .big sz hPos).encode x =
      (toBeBytes sz x).map (fun b => AllocByte.init (UInt8.ofBitVec b) none) := rfl

theorem uintBvCodec_encode_eq_encodeUInt (endian : TargetEndian) (sz : Nat)
    (hPos : 0 < sz) (x : BitVec (sz * 8)) :
    (uintBvCodec endian sz hPos).encode x =
      (encodeUInt endian sz x.toNat).map (fun b => AllocByte.init b none) :=
  encodeUInt_bv_bytes endian sz x

theorem uintBvCodec_isInitCodec (endian : TargetEndian) (sz : Nat)
    (hPos : 0 < sz) : (uintBvCodec endian sz hPos).IsInitCodec := by
  intro x
  exact allBytesInit_map_init_none _ _

theorem uintBvCodec_noProvCodec (endian : TargetEndian) (sz : Nat)
    (hPos : 0 < sz) : (uintBvCodec endian sz hPos).NoProvCodec := by
  intro x
  exact noProvBytes_map_init_none _ _

theorem uintBvCodec_isSurjectiveInitDecoder (endian : TargetEndian) (sz : Nat)
    (hPos : 0 < sz) : (uintBvCodec endian sz hPos).IsSurjectiveInitDecoder := by
  intro bs hLen hInit
  have ⟨raw, hRaw, _⟩ := initBytes?_isSome_of_allBytesInit bs hInit
  rw [← rawBytes?_eq_initBytes?] at hRaw
  refine ⟨BitVec.ofNat (sz * 8)
    (match endian with
     | .little => fromLeBytes (raw.map UInt8.toBitVec)
     | .big => fromBeBytes (raw.map UInt8.toBitVec)), ?_⟩
  unfold uintBvCodec FixedByteCodec.ofRoundTrip
  dsimp only
  rw [ite_true_of ((nat_beq_iff _ _).mpr hLen), hRaw]

theorem uintBvCodec_hasZeroValid (endian : TargetEndian) (sz : Nat)
    (hPos : 0 < sz) : (uintBvCodec endian sz hPos).HasZeroValid :=
  (uintBvCodec_isSurjectiveInitDecoder endian sz hPos).hasZeroValid

private theorem ui8_replicate_succ_append :
    ∀ q : Nat, List.replicate q (0 : UInt8) ++ [0] = List.replicate (q + 1) (0 : UInt8)
  | 0 => rfl
  | r + 1 => congrArg (List.cons (0 : UInt8)) (ui8_replicate_succ_append r)

private theorem ui8_replicate_map_zero :
    ∀ m : Nat,
      (List.replicate m (0 : UInt8)).map (fun b => AllocByte.init b none) =
        zeroInitBytes m
  | 0 => rfl
  | q + 1 =>
    congrArg (List.cons (AllocByte.init (0 : UInt8) none))
      (ui8_replicate_map_zero q)

private theorem encodeUInt_zero (endian : TargetEndian) (sz : Nat) :
    encodeUInt endian sz 0 = List.replicate sz 0 := by
  have hLe : ∀ q : Nat, leBytesOfNat q 0 = List.replicate q 0 := by
    intro q
    induction q with
    | zero => rfl
    | succ q' ihq =>
      change UInt8.ofNat 0 :: leBytesOfNat q' 0 = 0 :: List.replicate q' 0
      rw [ihq]
      rfl
  cases endian with
  | little => exact hLe sz
  | big =>
    unfold encodeUInt
    dsimp only
    rw [hLe sz]
    induction sz with
    | zero => rfl
    | succ q ihq =>
      change (0 :: List.replicate q 0).reverse =
        List.replicate (q + 1) (0 : UInt8)
      rw [List.reverse_cons, ihq]
      exact ui8_replicate_succ_append q

theorem uintBvCodec_decode_zeroInitBytes (endian : TargetEndian) (sz : Nat)
    (hPos : 0 < sz) :
    (uintBvCodec endian sz hPos).decode (zeroInitBytes sz) =
      some (BitVec.ofNat (sz * 8) 0) := by
  have hEnc :
      (uintBvCodec endian sz hPos).encode (BitVec.ofNat (sz * 8) 0) =
        zeroInitBytes sz := by
    rw [uintBvCodec_encode_eq_encodeUInt]
    have h0 : (BitVec.ofNat (sz * 8) 0).toNat = 0 := by
      rw [fbc_bv_toNat_ofNat, Nat.zero_mod]
    rw [h0, encodeUInt_zero]
    exact ui8_replicate_map_zero sz
  rw [← hEnc]
  exact (uintBvCodec endian sz hPos).decode_encode _

/-- Endian-parametric integer codec for every `IntWidth`
(`i8..i128` / `isize` and `u8..u128` / `usize`). -/
@[expose] def intBvCodec (endian : TargetEndian) (w : IntWidth) :
    FixedByteCodec (BitVec (fbcBitWidth w)) (fbcByteSize w) :=
  uintBvCodec endian (fbcByteSize w) (fbcByteSize_pos w)

/-- Endian-parametric `u8` codec (`1` byte). -/
abbrev u8Codec (endian : TargetEndian) : FixedByteCodec (BitVec 8) 1 :=
  intBvCodec endian .i8

/-- Endian-parametric `u16` codec (`2` bytes). -/
abbrev u16Codec (endian : TargetEndian) : FixedByteCodec (BitVec 16) 2 :=
  intBvCodec endian .i16

/-- Endian-parametric `u32` codec (`4` bytes). -/
abbrev u32Codec (endian : TargetEndian) : FixedByteCodec (BitVec 32) 4 :=
  intBvCodec endian .i32

/-- Endian-parametric `u64` codec (`8` bytes). -/
abbrev u64Codec (endian : TargetEndian) : FixedByteCodec (BitVec 64) 8 :=
  intBvCodec endian .i64

/-- Endian-parametric `u128` codec (`16` bytes). -/
abbrev u128Codec (endian : TargetEndian) : FixedByteCodec (BitVec 128) 16 :=
  intBvCodec endian .i128

/-- Endian-parametric `usize` codec on 64-bit targets (`8` bytes). -/
abbrev usizeCodec (endian : TargetEndian) : FixedByteCodec (BitVec 64) 8 :=
  intBvCodec endian .isize

theorem u16Codec_encode_little (x : BitVec 16) :
    (u16Codec .little).encode x =
      (u16ToLeBytes x).map (fun b => AllocByte.init (UInt8.ofBitVec b) none) :=
  rfl

theorem u32Codec_encode_little (x : BitVec 32) :
    (u32Codec .little).encode x =
      (u32ToLeBytes x).map (fun b => AllocByte.init (UInt8.ofBitVec b) none) :=
  rfl

theorem u64Codec_encode_little (x : BitVec 64) :
    (u64Codec .little).encode x =
      (u64ToLeBytes x).map (fun b => AllocByte.init (UInt8.ofBitVec b) none) :=
  rfl

theorem u128Codec_encode_little (x : BitVec 128) :
    (u128Codec .little).encode x =
      (u128ToLeBytes x).map (fun b => AllocByte.init (UInt8.ofBitVec b) none) :=
  rfl

/-! ### 3a. Pointwise Agreement with `Trusted.MirSemantics.Bytes` -/

theorem encodeVal_unit_eq_unitCodec (endian : TargetEndian) :
    encodeVal endian .unit .unit = .ok (unitCodec.encode ()) := rfl

theorem decodeVal_unit_eq_unitCodec (endian : TargetEndian)
    (bs : List AllocByte) :
    decodeVal endian .unit bs =
      if Nat.beq bs.length 0 then
        .ok ((unitCodec.decode bs).map (fun _ => Val.unit))
      else
        .error .unsupported := by
  unfold decodeVal layoutOfTy
  dsimp only
  cases hLen : Nat.beq bs.length 0 with
  | false => rfl
  | true =>
    have hNil : bs = [] := by
      cases bs with
      | nil => rfl
      | cons _ _ => nomatch hLen
    subst hNil
    rfl

theorem encodeVal_bool_eq_boolCodec (endian : TargetEndian) (b : Bool) :
    encodeVal endian .bool (.bool b) = .ok (boolCodec.encode b) := rfl

theorem decodeVal_bool_eq_boolCodec (endian : TargetEndian)
    (bs : List AllocByte) :
    decodeVal endian .bool bs =
      match bs with
      | [.init b _] =>
        if Nat.beq b.toNat 0 || Nat.beq b.toNat 1 then
          .ok ((boolCodec.decode bs).map Val.bool)
        else
          .error .undefined
      | [.uninit] => .ok none
      | _ => .error .unsupported := by
  cases bs with
  | nil => rfl
  | cons b0 rest =>
    cases rest with
    | cons b1 tail =>
      have hBeq : Nat.beq (b0 :: b1 :: tail).length 1 = false := by
        rw [List.length_cons, List.length_cons]
        cases hB : Nat.beq (tail.length + 1 + 1) 1 with
        | false => rfl
        | true =>
          have hEq := nat_eq_of_beq hB
          have hGe : 2 ≤ tail.length + 1 + 1 :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
          rw [hEq] at hGe
          nomatch hGe
      unfold decodeVal layoutOfTy
      dsimp only
      rw [hBeq, fbc_if_not_false]
      cases b0 <;> rfl
    | nil =>
      cases b0 with
      | uninit => rfl
      | init b prov =>
        have hTrunc :
            truncateBits .i8
                (BitVec.ofNat 128 (decodeUInt endian [b])) =
              BitVec.ofNat 128 (decodeUInt endian [b]) := by
          apply truncateBits_of_lt
          have hLt : decodeUInt endian [b] < Nat.pow 2 IntWidth.i8.bitWidth := by
            rw [← intWidth_bitWidth_eq]
            exact decodeUInt_lt endian [b]
          exact hLt
        have hNe :
            (truncateBits .i8
                (BitVec.ofNat 128 (decodeUInt endian [b])) !=
              BitVec.ofNat 128 (decodeUInt endian [b])) = false := by
          rw [hTrunc]
          exact bitVec128_bne_self _
        have hU8Nat :
            (UInt8.ofNat
              (truncateBits .i8
                (BitVec.ofNat 128 (decodeUInt endian [b]))).toNat).toNat =
              b.toNat := by
          rw [hTrunc]
          have hDec : decodeUInt endian [b] = b.toNat := by
            cases endian <;> simp [decodeUInt, natOfLeBytes]
          rw [hDec, fbc_bv_toNat_ofNat]
          have hB : b.toNat < Nat.pow 2 128 :=
            Nat.lt_trans b.toBitVec.isLt (by decide : Nat.pow 2 8 < Nat.pow 2 128)
          rw [Nat.mod_eq_of_lt hB]
          change (BitVec.ofNat 8 b.toNat).toNat = b.toNat
          rw [fbc_bv_toNat_ofNat, fbc_two_pow_eight]
          exact Nat.mod_eq_of_lt b.toBitVec.isLt
        have hU8 :
            UInt8.ofNat
              (truncateBits .i8
                (BitVec.ofNat 128 (decodeUInt endian [b]))).toNat = b :=
          fbc_uint8_eq_of_toNat_eq hU8Nat
        unfold decodeVal layoutOfTy
        dsimp only
        have hInit : initBytes? [AllocByte.init b prov] = some [b] := rfl
        rw [hInit]
        dsimp only
        unfold evalConstLit
        dsimp only
        rw [hNe]
        rw [hU8]
        unfold boolCodec FixedByteCodec.ofRoundTrip
        dsimp only
        cases h0 : Nat.beq b.toNat 0 with
        | true =>
          have hb0 : b = 0 := fbc_uint8_eq_of_toNat_eq (nat_eq_of_beq h0)
          subst hb0
          rfl
        | false =>
          cases h1 : Nat.beq b.toNat 1 with
          | true =>
            have hb1 : b = 1 := fbc_uint8_eq_of_toNat_eq (nat_eq_of_beq h1)
            subst hb1
            rfl
          | false =>
            have hBeq0 : (b == 0) = false := by
              cases hEq : (b == 0) with
              | false => rfl
              | true =>
                have hb0 : b = 0 := eq_of_beq hEq
                rw [hb0] at h0
                nomatch h0
            have hBeq1 : (b == 1) = false := by
              cases hEq : (b == 1) with
              | false => rfl
              | true =>
                have hb1 : b = 1 := eq_of_beq hEq
                rw [hb1] at h1
                nomatch h1
            rw [fbc_if_false, hBeq0, fbc_if_false, hBeq1, fbc_if_false]
            rfl

private theorem scalarVal_of_bv_wf (w : IntWidth) (s : Bool)
    (x : BitVec (fbcBitWidth w)) :
    checkVal (.scalar ⟨w, s, BitVec.ofNat 128 x.toNat⟩) (.int w s) = true := by
  have hLt : x.toNat < Nat.pow 2 w.bitWidth := by
    rw [← fbcBitWidth_eq w]
    exact x.isLt
  have hTrunc :
      truncateBits w (BitVec.ofNat 128 x.toNat) = BitVec.ofNat 128 x.toNat :=
    truncateBits_of_lt w x.toNat hLt
  have hWf : ScalarVal.wf ⟨w, s, BitVec.ofNat 128 x.toNat⟩ = true := by
    unfold ScalarVal.wf
    rw [hTrunc]
    exact bitVec128_beq_self _
  unfold checkVal Val.ty?
  dsimp only
  rw [ite_true_of hWf]
  cases w <;> cases s <;> rfl

theorem encodeVal_int_eq_intBvCodec (endian : TargetEndian) (w : IntWidth)
    (s : Bool) (x : BitVec (fbcBitWidth w)) :
    encodeVal endian (.int w s) (.scalar ⟨w, s, BitVec.ofNat 128 x.toNat⟩) =
      .ok ((intBvCodec endian w).encode x) := by
  unfold encodeVal
  rw [scalarVal_of_bv_wf w s x, fbc_if_not_true]
  dsimp only
  have hMod : (BitVec.ofNat 128 x.toNat).toNat = x.toNat := by
    have hPowLe : Nat.pow 2 (fbcBitWidth w) ≤ Nat.pow 2 128 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (fbcBitWidth_le_128 w)
    rw [fbc_bv_toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt hPowLe)
  rw [hMod, ← fbcByteSize_eq w]
  exact congrArg Except.ok (uintBvCodec_encode_eq_encodeUInt endian
    (fbcByteSize w) (fbcByteSize_pos w) x).symm

private theorem decodeUInt_fromLeBytes_bv (raw : List UInt8) (bits : Nat)
    (hLt : decodeUInt .little raw < Nat.pow 2 bits) :
    (BitVec.ofNat bits (fromLeBytes (raw.map UInt8.toBitVec))).toNat =
      decodeUInt .little raw := by
  have hEq := decodeUInt_eq_fromBytes .little raw
  dsimp only at hEq
  rw [← hEq, fbc_bv_toNat_ofNat]
  exact Nat.mod_eq_of_lt hLt

private theorem decodeUInt_fromBeBytes_bv (raw : List UInt8) (bits : Nat)
    (hLt : decodeUInt .big raw < Nat.pow 2 bits) :
    (BitVec.ofNat bits (fromBeBytes (raw.map UInt8.toBitVec))).toNat =
      decodeUInt .big raw := by
  have hEq := decodeUInt_eq_fromBytes .big raw
  dsimp only at hEq
  rw [← hEq, fbc_bv_toNat_ofNat]
  exact Nat.mod_eq_of_lt hLt

theorem decodeVal_int_eq_intBvCodec (endian : TargetEndian) (w : IntWidth)
    (s : Bool) (bs : List AllocByte) :
    decodeVal endian (.int w s) bs =
      if Nat.beq bs.length (fbcByteSize w) then
        .ok (((intBvCodec endian w).decode bs).map
          (fun x => Val.scalar ⟨w, s, BitVec.ofNat 128 x.toNat⟩))
      else
        .error .unsupported := by
  have hWSize : (intLayout w).size = fbcByteSize w := by cases w <;> rfl
  have hNz : Nat.beq (intLayout w).size 0 = false := by cases w <;> rfl
  unfold decodeVal layoutOfTy
  dsimp only
  rw [hWSize]
  cases hLen : Nat.beq bs.length (fbcByteSize w) with
  | false => rfl
  | true =>
    have hLenEq : bs.length = fbcByteSize w := nat_eq_of_beq hLen
    have hNzW : Nat.beq (fbcByteSize w) 0 = false := by cases w <;> rfl
    rw [fbc_if_not_true, hNzW, fbc_if_false]
    unfold intBvCodec uintBvCodec FixedByteCodec.ofRoundTrip
    dsimp only
    rw [rawBytes?_eq_initBytes?]
    rw [ite_true_of hLen]
    cases hRaw : initBytes? bs with
    | none => rfl
    | some raw =>
      dsimp only
      have ⟨_, hRawLen⟩ := allBytesInit_of_initBytes?_eq_some hRaw
      have hDecLtFbc : decodeUInt endian raw < Nat.pow 2 (fbcBitWidth w) := by
        have h1 := decodeUInt_lt endian raw
        rw [hRawLen, hLenEq, fbcByteSize_eq w, intWidth_bitWidth_eq,
            ← fbcBitWidth_eq w] at h1
        exact h1
      have hDecLt : decodeUInt endian raw < Nat.pow 2 w.bitWidth := by
        rw [← fbcBitWidth_eq w]
        exact hDecLtFbc
      have hTrunc :
          truncateBits w (BitVec.ofNat 128 (decodeUInt endian raw)) =
            BitVec.ofNat 128 (decodeUInt endian raw) :=
        truncateBits_of_lt w _ hDecLt
      have hNe :
          (truncateBits w (BitVec.ofNat 128 (decodeUInt endian raw)) !=
            BitVec.ofNat 128 (decodeUInt endian raw)) = false := by
        rw [hTrunc]
        exact bitVec128_bne_self _
      unfold fbcBitWidth at hDecLtFbc
      unfold evalConstLit
      dsimp only
      rw [ite_false_of (by rw [hNe]; exact fbc_false_ne_true), hTrunc,
          fbc_if_true]
      cases endian with
      | little =>
        change
          Except.ok
              (some (Val.scalar ⟨w, s, BitVec.ofNat 128 (decodeUInt .little raw)⟩)) =
            Except.ok
              (some
                (Val.scalar
                  ⟨w, s,
                    BitVec.ofNat 128
                      (BitVec.ofNat (fbcByteSize w * 8)
                        (fromLeBytes (raw.map UInt8.toBitVec))).toNat⟩))
        rw [decodeUInt_fromLeBytes_bv raw (fbcByteSize w * 8) hDecLtFbc]
      | big =>
        change
          Except.ok
              (some (Val.scalar ⟨w, s, BitVec.ofNat 128 (decodeUInt .big raw)⟩)) =
            Except.ok
              (some
                (Val.scalar
                  ⟨w, s,
                    BitVec.ofNat 128
                      (BitVec.ofNat (fbcByteSize w * 8)
                        (fromBeBytes (raw.map UInt8.toBitVec))).toNat⟩))
        rw [decodeUInt_fromBeBytes_bv raw (fbcByteSize w * 8) hDecLtFbc]

/-- Computable codec for Profile v1 overflow pairs `.tuple [.int w _, .bool]`
via `padRight (prod (intBvCodec endian w) boolCodec) (fbcByteSize w - 1)`: zero
padding for `w = .i8`, `w.byteSize - 1 > 0` padding bytes otherwise. -/
@[expose] def overflowPairCodec (endian : TargetEndian) (w : IntWidth) :
    FixedByteCodec (BitVec (fbcBitWidth w) × Bool)
      (fbcByteSize w + 1 + (fbcByteSize w - 1)) :=
  FixedByteCodec.padRight
    (FixedByteCodec.prod (intBvCodec endian w) boolCodec)
    (fbcByteSize w - 1)

theorem overflowPairCodec_size_eq (w : IntWidth) :
    fbcByteSize w + 1 + (fbcByteSize w - 1) = (overflowPairLayout w).size := by
  rw [fbcByteSize_eq w]
  exact overflowPair_size_pos w

theorem encodeVal_overflowPair_eq (endian : TargetEndian) (w : IntWidth)
    (s : Bool) (x : BitVec (fbcBitWidth w)) (b : Bool) :
    encodeVal endian (.tuple [.int w s, .bool])
        (.tuple [.scalar ⟨w, s, BitVec.ofNat 128 x.toNat⟩, .bool b]) =
      .ok ((overflowPairCodec endian w).encode (x, b)) := by
  have hLt : x.toNat < Nat.pow 2 w.bitWidth := by
    rw [← fbcBitWidth_eq w]
    exact x.isLt
  have hWf : ScalarVal.wf ⟨w, s, BitVec.ofNat 128 x.toNat⟩ = true := by
    unfold ScalarVal.wf
    rw [truncateBits_of_lt w x.toNat hLt]
    exact bitVec128_beq_self _
  have hChk :
      checkVal (.tuple [.scalar ⟨w, s, BitVec.ofNat 128 x.toNat⟩, .bool b])
          (.tuple [.int w s, .bool]) = true := by
    unfold checkVal Val.ty?
    dsimp only
    rw [ite_true_of hWf]
    cases w <;> cases s <;> rfl
  have hMod : (BitVec.ofNat 128 x.toNat).toNat = x.toNat := by
    have hPowLe : Nat.pow 2 (fbcBitWidth w) ≤ Nat.pow 2 128 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (fbcBitWidth_le_128 w)
    rw [fbc_bv_toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt hPowLe)
  unfold encodeVal
  rw [hChk, fbc_if_not_true]
  dsimp only
  rw [hMod]
  unfold overflowPairCodec
  rw [FixedByteCodec.padRight_encode_eq, FixedByteCodec.prod_encode_eq,
      ← fbcByteSize_eq w]
  change
    Except.ok
      ((encodeUInt endian (fbcByteSize w) x.toNat).map
          (fun byte => AllocByte.init byte none) ++
        [AllocByte.init (if b then 1 else 0) none] ++
        List.replicate (fbcByteSize w - 1) AllocByte.uninit) =
      Except.ok
        ((intBvCodec endian w).encode x ++ boolCodec.encode b ++
          List.replicate (fbcByteSize w - 1) AllocByte.uninit)
  have hInt :
      (intBvCodec endian w).encode x =
        (encodeUInt endian (fbcByteSize w) x.toNat).map
          (fun byte => AllocByte.init byte none) :=
    uintBvCodec_encode_eq_encodeUInt endian (fbcByteSize w)
      (fbcByteSize_pos w) x
  rw [hInt]
  cases b <;> rfl

/-! ## 4. `MirBytesCodec` and Formal `BitValidity` Trait Composition Bridges -/

/-- Typed bridge connecting a `FixedByteCodec α sz` to `Trusted.MirSemantics`
(`encodeVal`/`decodeVal` and `layoutOfTy`) under `endian : TargetEndian`. -/
structure MirBytesCodec (endian : TargetEndian) (ty : MirTy) (α : Type)
    (sz : Nat) : Type where
  /-- Underlying prefix-free `sz`-byte codec. -/
  codec : FixedByteCodec α sz
  /-- Embed typed value `α` into runtime `Val`. -/
  toVal : α → Val
  /-- Recover typed value `α` from runtime `Val`. -/
  ofVal : Val → Option α
  /-- Left-inverse witness. -/
  ofVal_toVal : ∀ x : α, ofVal (toVal x) = some x
  /-- Target layout of `ty` in Profile v1. -/
  layout : LayoutData
  /-- `layoutOfTy ty` resolves to `some layout`. -/
  layout_eq : layoutOfTy ty = some layout
  /-- `layout.size` equals the codec width `sz`. -/
  size_eq : layout.size = sz
  /-- Encoding `toVal x` at `ty` emits `codec.encode x`. -/
  encode_toVal :
    ∀ x : α, encodeVal endian ty (toVal x) = .ok (codec.encode x)
  /-- Every successful `encodeVal` at `ty` equals `codec.encode x` for some
  `x : α`. -/
  encode_canonical :
    ∀ (v : Val) (bs : List AllocByte),
      encodeVal endian ty v = .ok bs → ∃ x : α, bs = codec.encode x
  /-- Decoding at `ty` agrees with `(codec.decode bs).map toVal` on every
  initialized `sz`-byte buffer. -/
  decode_ok_of_init :
    ∀ bs : List AllocByte,
      bs.length = sz →
      AllBytesInit bs →
      match codec.decode bs with
      | some x => decodeVal endian ty bs = .ok (some (toVal x))
      | none => ¬ ∃ v, decodeVal endian ty bs = .ok (some v)
  /-- Zero-initialized `sz`-byte decoding agrees with `codec.decode`. -/
  decode_zero :
    match codec.decode (zeroInitBytes sz) with
    | some x => decodeVal endian ty (zeroInitBytes sz) = .ok (some (toVal x))
    | none => ¬ ∃ v, decodeVal endian ty (zeroInitBytes sz) = .ok (some v)
  /-- `decodeVal` soundness characterization on all `.ok (some v)` outputs. -/
  decode_sound :
    ∀ (bs : List AllocByte) (v : Val),
      decodeVal endian ty bs = .ok (some v) →
      ∃ x : α, v = toVal x ∧ ofVal v = some x
  /-- `ty` is not a Profile v1 overflow pair, so it has an addressable layout
  (`addressableLayoutOfTy`). -/
  not_overflowPair : isOverflowPairTy ty = false

namespace MirBytesCodec

/-- Every `MirBytesCodec` target has an addressable layout. -/
theorem addressable_eq {endian : TargetEndian} {ty : MirTy}
    {α : Type} {sz : Nat} (m : MirBytesCodec endian ty α sz) :
    addressableLayoutOfTy ty = some m.layout :=
  addressableLayoutOfTy_of_not_overflowPair m.not_overflowPair m.layout_eq

/-- Every `MirBytesCodec` types its decoded values: each is `m.toVal x` for
some `x` with `m.ofVal v = some x`. -/
theorem decodeTyped {endian : TargetEndian} {ty : MirTy}
    {α : Type} {sz : Nat} (m : MirBytesCodec endian ty α sz) :
    DecodeTyped endian ty
      (fun v => ∃ x : α, v = m.toVal x ∧ m.ofVal v = some x) :=
  ⟨m.layout, m.layout_eq, m.decode_sound⟩

/-- The codec's decoder is an exact `TryFromBytes` validator: on initialized
candidates of the type's size it succeeds exactly on bit-valid ones. -/
theorem isExactTryFromBytes {endian : TargetEndian} {ty : MirTy}
    {α : Type} {sz : Nat} (m : MirBytesCodec endian ty α sz) :
    IsExactTryFromBytes endian ty (fun bs => (m.codec.decode bs).isSome) := by
  refine ⟨m.layout, m.addressable_eq, fun bs ⟨l, hL, hLen, hInit⟩ => ?_⟩
  have hEq := layoutOfTy_unique hL m.layout_eq
  subst hEq
  have hLenSz : bs.length = sz := by rw [hLen, m.size_eq]
  have hDec := m.decode_ok_of_init bs hLenSz hInit
  change (m.codec.decode bs).isSome = true ↔ _
  cases hC : m.codec.decode bs with
  | some x =>
    rw [hC] at hDec
    exact ⟨fun _ => ⟨m.layout, m.toVal x, hL, hLen, hDec⟩, fun _ => rfl⟩
  | none =>
    rw [hC] at hDec
    exact ⟨(fun h => nomatch h),
      (fun ⟨_, v, _, _, hv⟩ => absurd ⟨v, hv⟩ hDec)⟩

/-- `HasZeroValid` lifts cleanly through `MirBytesCodec` to `IsFromZeros`. -/
theorem isFromZeros {endian : TargetEndian} {ty : MirTy}
    {α : Type} {sz : Nat} (m : MirBytesCodec endian ty α sz)
    (hZero : m.codec.HasZeroValid) : IsFromZeros endian ty := by
  have ⟨x, hx⟩ := hZero
  have hDec := m.decode_zero
  rw [hx] at hDec
  have hDec' :
      decodeVal endian ty (zeroInitBytes m.layout.size) =
        .ok (some (m.toVal x)) := by
    rw [m.size_eq]
    exact hDec
  exact ⟨m.layout, m.toVal x, m.addressable_eq, hDec'⟩

/-- `IsSurjectiveInitDecoder` lifts cleanly through `MirBytesCodec` to
`IsFromBytes`. -/
theorem isFromBytes {endian : TargetEndian} {ty : MirTy}
    {α : Type} {sz : Nat} (m : MirBytesCodec endian ty α sz)
    (hSurj : m.codec.IsSurjectiveInitDecoder) : IsFromBytes endian ty := by
  refine ⟨m.layout, m.addressable_eq, ?_⟩
  intro bs hLen hInit
  rw [m.size_eq] at hLen
  have ⟨x, hx⟩ := hSurj bs hLen hInit
  have hDec := m.decode_ok_of_init bs hLen hInit
  rw [hx] at hDec
  exact ⟨m.toVal x, hDec⟩

/-- `IsInitCodec` lifts cleanly through `MirBytesCodec` to `IsIntoBytes`. -/
theorem isIntoBytes {endian : TargetEndian} {ty : MirTy}
    {α : Type} {sz : Nat} (m : MirBytesCodec endian ty α sz)
    (hInit : m.codec.IsInitCodec) : IsIntoBytes endian ty := by
  refine ⟨m.layout, m.addressable_eq, ?_⟩
  intro v bs hEnc
  have ⟨x, hBs⟩ := m.encode_canonical v bs hEnc
  subst hBs
  rw [m.size_eq]
  exact ⟨m.codec.encode_length x, hInit x⟩

theorem not_isFromZeros_of_zero_none {endian : TargetEndian} {ty : MirTy}
    {α : Type} {sz : Nat} (m : MirBytesCodec endian ty α sz)
    (hNone : m.codec.decode (zeroInitBytes sz) = none) :
    ¬ IsFromZeros endian ty := by
  intro ⟨lay, v, hLay, hDec⟩
  rw [m.addressable_eq] at hLay
  injection hLay with hEq
  subst hEq
  rw [m.size_eq] at hDec
  have hNeg := m.decode_zero
  rw [hNone] at hNeg
  exact hNeg ⟨v, hDec⟩

theorem not_isFromBytes_of_rejected_init {endian : TargetEndian} {ty : MirTy}
    {α : Type} {sz : Nat} (m : MirBytesCodec endian ty α sz)
    {bs : List AllocByte} (hLen : bs.length = sz) (hInit : AllBytesInit bs)
    (hNone : m.codec.decode bs = none) :
    ¬ IsFromBytes endian ty := by
  intro ⟨lay, hLay, hDec⟩
  rw [m.addressable_eq] at hLay
  injection hLay with hEq
  subst hEq
  rw [m.size_eq] at hDec
  have ⟨v, hv⟩ := hDec bs hLen hInit
  have hNeg := m.decode_ok_of_init bs hLen hInit
  rw [hNone] at hNeg
  exact hNeg ⟨v, hv⟩

theorem not_isIntoBytes_of_uninit {endian : TargetEndian} {ty : MirTy}
    {α : Type} {sz : Nat} (m : MirBytesCodec endian ty α sz)
    (x : α) (hUninit : allBytesInit (m.codec.encode x) = false) :
    ¬ IsIntoBytes endian ty := by
  intro ⟨_, _, hProps⟩
  have ⟨_, hInit⟩ := hProps (m.toVal x) (m.codec.encode x) (m.encode_toVal x)
  change allBytesInit (m.codec.encode x) = true at hInit
  rw [hUninit] at hInit
  nomatch hInit

/-- Concrete `MirBytesCodec` for `MirTy.unit`. -/
@[expose] def unit (endian : TargetEndian) :
    MirBytesCodec endian .unit Unit 0 where
  codec := unitCodec
  toVal _ := .unit
  ofVal v := match v with | .unit => some () | _ => none
  ofVal_toVal u := by cases u; rfl
  layout := ⟨0, 0⟩
  layout_eq := rfl
  size_eq := rfl
  encode_toVal u := by cases u; rfl
  encode_canonical v bs hEnc := by
    unfold encodeVal at hEnc
    cases hChk : checkVal v .unit with
    | false =>
      rw [hChk, fbc_if_not_false] at hEnc
      nomatch hEnc
    | true =>
      rw [hChk, fbc_if_not_true] at hEnc
      cases v with
      | unit =>
        injection hEnc with hBs
        exact ⟨(), hBs.symm⟩
      | scalar _ | ptr _ | bool _ | char _ | ordering _ | enumVal _ _
      | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _
      | tuple _ | bytes _ => nomatch hEnc
  decode_ok_of_init bs hLen _ := by
    cases bs with
    | nil => exact rfl
    | cons _ _ => nomatch hLen
  decode_zero := rfl
  not_overflowPair := rfl
  decode_sound bs v hDec := by
    unfold decodeVal layoutOfTy at hDec
    dsimp only at hDec
    cases hLen : Nat.beq bs.length 0 with
    | false =>
      rw [hLen, fbc_if_not_false] at hDec
      nomatch hDec
    | true =>
      have h00 : Nat.beq 0 0 = true := rfl
      rw [hLen, fbc_if_not_true, h00, fbc_if_true] at hDec
      injection hDec with hOpt
      injection hOpt with hV
      subst hV
      exact ⟨(), rfl, rfl⟩

/-- Concrete `MirBytesCodec` for `MirTy.bool`. -/
@[expose] def bool (endian : TargetEndian) :
    MirBytesCodec endian .bool Bool 1 where
  codec := boolCodec
  toVal := Val.bool
  ofVal v := match v with | .bool b => some b | _ => none
  ofVal_toVal _ := rfl
  layout := ⟨1, 0⟩
  layout_eq := rfl
  size_eq := rfl
  encode_toVal b := encodeVal_bool_eq_boolCodec endian b
  encode_canonical v bs hEnc := by
    unfold encodeVal at hEnc
    cases hChk : checkVal v .bool with
    | false =>
      rw [hChk, fbc_if_not_false] at hEnc
      nomatch hEnc
    | true =>
      rw [hChk, fbc_if_not_true] at hEnc
      cases v with
      | bool b =>
        injection hEnc with hBs
        exact ⟨b, hBs.symm⟩
      | scalar _ | ptr _ | char _ | ordering _ | unit | enumVal _ _
      | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _
      | tuple _ | bytes _ => nomatch hEnc
  decode_ok_of_init bs hLen hInit := by
    cases bs with
    | nil => nomatch hLen
    | cons b0 rest =>
      cases rest with
      | cons _ _ => nomatch hLen
      | nil =>
        cases b0 with
        | uninit => nomatch hInit
        | init b prov =>
          have hEq := decodeVal_bool_eq_boolCodec endian [.init b prov]
          dsimp only at hEq
          cases h0 : Nat.beq b.toNat 0 with
          | true =>
            have hb0 : b = 0 := fbc_uint8_eq_of_toNat_eq (nat_eq_of_beq h0)
            subst hb0
            rw [hEq]
            rfl
          | false =>
            cases h1 : Nat.beq b.toNat 1 with
            | true =>
              have hb1 : b = 1 := fbc_uint8_eq_of_toNat_eq (nat_eq_of_beq h1)
              subst hb1
              rw [hEq]
              rfl
            | false =>
              have hFalse : (Nat.beq b.toNat 0 || Nat.beq b.toNat 1) = false := by
                rw [h0, h1]
                rfl
              rw [ite_false_of (by rw [hFalse]; exact fbc_false_ne_true)] at hEq
              have hDecNone : boolCodec.decode [.init b prov] = none := by
                unfold boolCodec FixedByteCodec.ofRoundTrip
                dsimp only
                rw [ite_false_of (by rw [h0]; exact fbc_false_ne_true),
                    ite_false_of (by rw [h1]; exact fbc_false_ne_true)]
              rw [hDecNone]
              intro ⟨v, hv⟩
              rw [hEq] at hv
              nomatch hv
  decode_zero := by cases endian <;> rfl
  not_overflowPair := rfl
  decode_sound bs v hDec := by
    have ⟨_, _, hPred⟩ := bool_decodeTyped endian
    have hv := hPred bs v hDec
    cases hv with
    | inl hf => exact ⟨false, hf, by rw [hf]⟩
    | inr ht => exact ⟨true, ht, by rw [ht]⟩

/-- Concrete `MirBytesCodec` for every MIR integer type `.int w s`
(`u8`/`i8`..`u128`/`i128`, `usize`/`isize`). -/
@[expose] noncomputable def int (endian : TargetEndian) (w : IntWidth) (s : Bool) :
    MirBytesCodec endian (.int w s) (BitVec (fbcBitWidth w))
      (fbcByteSize w) where
  codec := intBvCodec endian w
  toVal x := .scalar ⟨w, s, BitVec.ofNat 128 x.toNat⟩
  ofVal v :=
    match v with
    | .scalar sv =>
      if sv.wf && IntWidth.beq sv.width w && (sv.signed == s) then
        some (BitVec.ofNat (fbcBitWidth w) sv.bits.toNat)
      else
        none
    | _ => none
  ofVal_toVal x := by
    have hLt : x.toNat < Nat.pow 2 w.bitWidth := by
      rw [← fbcBitWidth_eq w]
      exact x.isLt
    have hWf : ScalarVal.wf ⟨w, s, BitVec.ofNat 128 x.toNat⟩ = true := by
      unfold ScalarVal.wf
      rw [truncateBits_of_lt w x.toNat hLt]
      exact bitVec128_beq_self _
    have hW : IntWidth.beq w w = true := by cases w <;> rfl
    have hS : (s == s) = true := by cases s <;> rfl
    have hCond : (ScalarVal.wf ⟨w, s, BitVec.ofNat 128 x.toNat⟩ &&
        IntWidth.beq w w && (s == s)) = true := by
      rw [hWf, hW, hS]
      rfl
    dsimp only
    rw [ite_true_of hCond]
    have hPowLe : Nat.pow 2 (fbcBitWidth w) ≤ Nat.pow 2 128 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (fbcBitWidth_le_128 w)
    have hMod128 : (BitVec.ofNat 128 x.toNat).toNat = x.toNat := by
      rw [fbc_bv_toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt hPowLe)
    rw [hMod128]
    exact congrArg some (fbc_bv_eq_of_toNat_eq (by
      rw [fbc_bv_toNat_ofNat]
      exact Nat.mod_eq_of_lt x.isLt))
  layout := intLayout w
  layout_eq := rfl
  size_eq := by cases w <;> rfl
  encode_toVal x := encodeVal_int_eq_intBvCodec endian w s x
  encode_canonical v bs hEnc := by
    unfold encodeVal at hEnc
    cases hChk : checkVal v (.int w s) with
    | false =>
      rw [hChk, fbc_if_not_false] at hEnc
      nomatch hEnc
    | true =>
      rw [hChk, fbc_if_not_true] at hEnc
      cases v with
      | scalar sv =>
        injection hEnc with hBs
        have hTrunc : truncateBits w sv.bits = sv.bits := by
          unfold checkVal Val.ty? ScalarVal.wf at hChk
          dsimp only at hChk
          cases hWf : (truncateBits sv.width sv.bits == sv.bits) with
          | false =>
            rw [ite_false_of (by rw [hWf]; exact fbc_false_ne_true)] at hChk
            nomatch hChk
          | true =>
            rw [ite_true_of hWf] at hChk
            dsimp only at hChk
            have hWEq : sv.width = w :=
              intWidth_eq_of_beq (bool_and_left hChk)
            subst hWEq
            exact eq_of_beq hWf
        have hLt : sv.bits.toNat < Nat.pow 2 w.bitWidth := by
          unfold truncateBits bvExtractLsb bvExtractLsb' bvZeroExtend at hTrunc
          have h128 :
              (BitVec.ofNat 128
                (BitVec.ofNat (w.bitWidth - 1 - 0 + 1)
                  (Nat.shiftRight sv.bits.toNat 0)).toNat).toNat =
                sv.bits.toNat :=
            congrArg BitVec.toNat hTrunc
          have hS0 : Nat.shiftRight sv.bits.toNat 0 = sv.bits.toNat := rfl
          rw [hS0, Nat.sub_zero, bitWidth_sub_one_add_one w] at h128
          have hWLe : Nat.pow 2 w.bitWidth ≤ Nat.pow 2 128 :=
            Nat.pow_le_pow_right (by decide : 0 < 2) (intWidth_bitWidth_le_128 w)
          have hInner :
              HMod.hMod sv.bits.toNat (Nat.pow 2 w.bitWidth) <
                Nat.pow 2 w.bitWidth :=
            Nat.mod_lt sv.bits.toNat (nat_two_pow_pos w.bitWidth)
          have hModLt := Nat.lt_of_lt_of_le hInner hWLe
          change
            (BitVec.ofNat 128
                (HMod.hMod sv.bits.toNat (Nat.pow 2 w.bitWidth))).toNat =
              sv.bits.toNat at h128
          rw [fbc_bv_toNat_ofNat, Nat.mod_eq_of_lt hModLt] at h128
          rw [← h128]
          exact hInner
        refine ⟨BitVec.ofNat (fbcBitWidth w) sv.bits.toNat, ?_⟩
        rw [← hBs]
        change
          (encodeUInt endian w.byteSize sv.bits.toNat).map
              (fun b => AllocByte.init b none) =
            (uintBvCodec endian (fbcByteSize w) (fbcByteSize_pos w)).encode
              (BitVec.ofNat (fbcBitWidth w) sv.bits.toNat)
        have hLtFbc : sv.bits.toNat < Nat.pow 2 (fbcByteSize w * 8) := by
          rw [← fbcBitWidth_eq w] at hLt
          exact hLt
        unfold fbcBitWidth
        rw [← fbcByteSize_eq w, uintBvCodec_encode_eq_encodeUInt,
            fbc_bv_toNat_ofNat, Nat.mod_eq_of_lt hLtFbc]
      | ptr _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _
      | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _
      | bytes _ => nomatch hEnc
  decode_ok_of_init bs hLen hInit := by
    have hEq := decodeVal_int_eq_intBvCodec endian w s bs
    rw [ite_true_of ((nat_beq_iff _ _).mpr hLen)] at hEq
    have ⟨x, hx⟩ :=
      uintBvCodec_isSurjectiveInitDecoder endian (fbcByteSize w)
        (fbcByteSize_pos w) bs hLen hInit
    change (intBvCodec endian w).decode bs = some x at hx
    rw [hx]
    rw [hx] at hEq
    exact hEq
  decode_zero := by
    have hLen := length_zeroInitBytes (fbcByteSize w)
    have hEq :=
      decodeVal_int_eq_intBvCodec endian w s (zeroInitBytes (fbcByteSize w))
    rw [ite_true_of ((nat_beq_iff _ _).mpr hLen)] at hEq
    have hDecZ :
        (intBvCodec endian w).decode (zeroInitBytes (fbcByteSize w)) =
          some (BitVec.ofNat (fbcByteSize w * 8) 0) :=
      uintBvCodec_decode_zeroInitBytes endian (fbcByteSize w)
        (fbcByteSize_pos w)
    rw [hDecZ]
    rw [hDecZ] at hEq
    exact hEq
  not_overflowPair := rfl
  decode_sound bs v hDec := by
    have hEq := decodeVal_int_eq_intBvCodec endian w s bs
    cases hLen : Nat.beq bs.length (fbcByteSize w) with
    | false =>
      rw [ite_false_of (by rw [hLen]; exact fbc_false_ne_true)] at hEq
      rw [hDec] at hEq
      nomatch hEq
    | true =>
      rw [ite_true_of hLen] at hEq
      rw [hDec] at hEq
      cases hDecC : (intBvCodec endian w).decode bs with
      | none =>
        rw [hDecC] at hEq
        nomatch hEq
      | some x =>
        rw [hDecC] at hEq
        injection hEq with hOpt
        injection hOpt with hV
        refine ⟨x, hV, ?_⟩
        rw [hV]
        have hLt : x.toNat < Nat.pow 2 w.bitWidth := by
          rw [← fbcBitWidth_eq w]
          exact x.isLt
        have hWf : ScalarVal.wf ⟨w, s, BitVec.ofNat 128 x.toNat⟩ = true := by
          unfold ScalarVal.wf
          rw [truncateBits_of_lt w x.toNat hLt]
          exact bitVec128_beq_self _
        have hW : IntWidth.beq w w = true := by cases w <;> rfl
        have hS : (s == s) = true := by cases s <;> rfl
        have hCond : (ScalarVal.wf ⟨w, s, BitVec.ofNat 128 x.toNat⟩ &&
            IntWidth.beq w w && (s == s)) = true := by
          rw [hWf, hW, hS]
          rfl
        dsimp only
        rw [ite_true_of hCond]
        have hPowLe : Nat.pow 2 (fbcBitWidth w) ≤ Nat.pow 2 128 :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (fbcBitWidth_le_128 w)
        have hMod128 : (BitVec.ofNat 128 x.toNat).toNat = x.toNat := by
          rw [fbc_bv_toNat_ofNat]
          exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt hPowLe)
        rw [hMod128]
        exact congrArg some (fbc_bv_eq_of_toNat_eq (by
          rw [fbc_bv_toNat_ofNat]
          exact Nat.mod_eq_of_lt x.isLt))

end MirBytesCodec

/-! ### 4a. Trait Composition, Transmutation Soundness, and Padding Laws -/

/-- Byte-level transmutation soundness between two equal-width
`FixedByteCodec`s: every `src`-encoded value emits provenance-free bytes that
decode cleanly under `dst`. -/
@[expose] def CodecTransmuteSound {α β : Type} {n : Nat}
    (src : FixedByteCodec α n) (dst : FixedByteCodec β n) : Prop :=
  ∀ x : α, NoProvBytes (src.encode x) ∧ ∃ y : β, dst.decode (src.encode x) = some y

/-- Any `IsInitCodec` + `NoProvCodec` source codec transmutes soundly into any
equal-width `IsSurjectiveInitDecoder` destination codec. -/
theorem codecTransmute_sound {α β : Type} {n : Nat}
    (src : FixedByteCodec α n) (dst : FixedByteCodec β n)
    (hInit : src.IsInitCodec) (hNoProv : src.NoProvCodec)
    (hSurj : dst.IsSurjectiveInitDecoder) :
    CodecTransmuteSound src dst :=
  fun x => ⟨hNoProv x, hSurj (src.encode x) (src.encode_length x) (hInit x)⟩

/-- Sound transmutation from any compositional `IsInitCodec` + `NoProvCodec`
`FixedByteCodec` into an equal-size Profile v1 `IsFromBytes` MIR type. -/
theorem transmute_codec_to_mirTy_sound (endian : TargetEndian)
    {α : Type} {n : Nat} (src : FixedByteCodec α n) (dstTy : MirTy)
    (dstLay : LayoutData)
    (hInit : src.IsInitCodec) (hNoProv : src.NoProvCodec)
    (hFrom : IsFromBytes endian dstTy)
    (hLay : layoutOfTy dstTy = some dstLay) (hSize : dstLay.size = n)
    (x : α) :
    NoProvBytes (src.encode x) ∧
      ∃ v', decodeVal endian dstTy (src.encode x) = .ok (some v') := by
  have ⟨lay, hLay', hDec⟩ := hFrom
  have hLay'' := layoutOfTy_of_addressableLayoutOfTy hLay'
  rw [hLay] at hLay''
  injection hLay'' with hEq
  subst hEq
  rw [hSize] at hDec
  exact ⟨hNoProv x, hDec (src.encode x) (src.encode_length x) (hInit x)⟩

/-- Sound transmutation from a Profile v1 `IsIntoBytes` MIR type into any
equal-width `IsSurjectiveInitDecoder` `FixedByteCodec`. -/
theorem transmute_mirTy_to_codec_sound (endian : TargetEndian)
    (srcTy : MirTy) (srcLay : LayoutData) {β : Type} {n : Nat}
    (dst : FixedByteCodec β n)
    (hInto : IsIntoBytes endian srcTy)
    (hSurj : dst.IsSurjectiveInitDecoder)
    (hLay : layoutOfTy srcTy = some srcLay) (hSize : srcLay.size = n)
    (v : Val) (bs : List AllocByte)
    (hEnc : encodeVal endian srcTy v = .ok bs) :
    NoProvBytes bs ∧ ∃ y : β, dst.decode bs = some y := by
  have ⟨lay, hLay', hEncProps⟩ := hInto
  have hLay'' := layoutOfTy_of_addressableLayoutOfTy hLay'
  rw [hLay] at hLay''
  injection hLay'' with hEq
  subst hEq
  rw [hSize] at hEncProps
  have ⟨hLen, hInit⟩ := hEncProps v bs hEnc
  exact ⟨noProvBytes_encodeVal endian srcTy v bs hEnc, hSurj bs hLen hInit⟩

/-- Positive vs. negative padding dichotomy matching `zerocopy`'s padding rules:
when `0 < pad`, `(padRight c pad)` preserves `NoProvCodec`, `HasZeroValid`
(`FromZeros`), and `IsSurjectiveInitDecoder` (`FromBytes`), yet
strictly refutes `IsInitCodec` (`IntoBytes`) whenever `α` is inhabited. -/
theorem padRight_preserves_fromBytes_not_intoBytes {α : Type} {n pad : Nat}
    (c : FixedByteCodec α n) (hPos : 0 < pad)
    (hNoProv : c.NoProvCodec)
    (hSurj : c.IsSurjectiveInitDecoder) (x₀ : α) :
    (FixedByteCodec.padRight c pad).NoProvCodec ∧
      (FixedByteCodec.padRight c pad).HasZeroValid ∧
      (FixedByteCodec.padRight c pad).IsSurjectiveInitDecoder ∧
      ¬ (FixedByteCodec.padRight c pad).IsInitCodec :=
  ⟨FixedByteCodec.padRight_noProvCodec pad hNoProv,
   FixedByteCodec.padRight_hasZeroValid pad hSurj.hasZeroValid,
   FixedByteCodec.padRight_isSurjectiveInitDecoder pad hSurj,
   FixedByteCodec.padRight_not_isInitCodec c hPos x₀⟩

/-- Because `(FixedByteCodec.padRight c pad).encode x` contains `.uninit` bytes
whenever `0 < pad`, decoding it as any equal-size MIR integer `.int w s` yields
`.ok none` (fails to materialize a valid initialized `Val`). -/
theorem decodeVal_int_padRight_eq_none {α : Type} {n pad : Nat}
    (endian : TargetEndian) (w : IntWidth) (s : Bool)
    (c : FixedByteCodec α n) (hPos : 0 < pad)
    (hSize : n + pad = w.byteSize) (x : α) :
    decodeVal endian (.int w s)
        ((FixedByteCodec.padRight c pad).encode x) = .ok none := by
  have hFalse :
      allBytesInit ((FixedByteCodec.padRight c pad).encode x) = false :=
    FixedByteCodec.allBytesInit_padRight_encode_eq_false c hPos x
  have hInitNone :
      initBytes? ((FixedByteCodec.padRight c pad).encode x) = none := by
    cases hInit : initBytes? ((FixedByteCodec.padRight c pad).encode x) with
    | none => rfl
    | some _ =>
      have ⟨hTrue, _⟩ := allBytesInit_of_initBytes?_eq_some hInit
      have hTrue' :
          allBytesInit ((FixedByteCodec.padRight c pad).encode x) = true :=
        hTrue
      rw [hFalse] at hTrue'
      nomatch hTrue'
  have hLen :
      ((FixedByteCodec.padRight c pad).encode x).length = w.byteSize := by
    rw [FixedByteCodec.encode_length, hSize]
  have hLenBeq :
      Nat.beq ((FixedByteCodec.padRight c pad).encode x).length w.byteSize =
        true :=
    (nat_beq_iff _ _).mpr hLen
  have hWSize : (intLayout w).size = w.byteSize := by cases w <;> rfl
  have hNz : Nat.beq w.byteSize 0 = false := by cases w <;> rfl
  unfold decodeVal layoutOfTy
  dsimp only
  rw [hWSize, hLenBeq, fbc_if_not_true, hNz, fbc_if_false, hInitNone]

end Anneal.Core

end
