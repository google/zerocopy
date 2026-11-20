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
import Init.Data.Fin.Basic
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic

namespace Anneal.LeBytes

/-!
# Reusable 3-Axiom Byte-Order Serialization Library (`Anneal.LeBytes`)

Kernel-checked, width-parametric little-endian and big-endian byte
serialization over `BitVec` and `Nat`, built strictly on Anneal's 51-module
`foundation-lock.json` foundation (no `omega`, no `bv_decide`, no `Std.*`,
and zero `_unsafe_rec` auxiliaries).

Operations use `HDiv.hDiv`, `HMod.hMod`, and `HPow.hPow` directly so every
statement matches standard `/`, `%`, and `^` syntax under `rw` and `simp` in
downstream proofs while staying within `allowedTheorySyntaxKinds`.

1. **Core Definitions:** structural `@Nat.rec` `toLeBytesAux`, `toLeBytes`,
   `List.foldr`-based `fromLeBytes`, `fromLeBytesBv`, big-endian `toBeBytes`
   and `fromBeBytes`, and fixed-width `u16`/`u32`/`u64`/`u128` aliases.
2. **Length & Bounds:** exact output lengths and `< 2^(8 * bs.length)` range
   bounds for decoded integers.
3. **Round-Trip & Injectivity:** exact left/right inverses between `toLeBytes`
   and `fromLeBytes`, injectivity for little-endian, big-endian, and
   concatenated byte sequences, and zero-byte identities.
4. **Byte Indexing, Concatenation & Closed Forms:** `getElem?` / `GetElem`
   byte formulas, append decomposition, and explicit 2-, 4-, and 8-byte
   expansions for `u16`, `u32`, and `u64`.
-/

/-! ## Part 0: Foundation-Only `Nat`, `BitVec`, and `List` Helpers -/

private theorem nat_pow_zero (a : Nat) : HPow.hPow a 0 = 1 := rfl

private theorem nat_pow_succ (a n : Nat) :
    HPow.hPow a (n + 1) = HPow.hPow a n * a :=
  Nat.pow_succ a n

private theorem nat_pow_add (a m n : Nat) :
    HPow.hPow a (m + n) = HPow.hPow a m * HPow.hPow a n := by
  induction n with
  | zero =>
    rw [Nat.add_zero, nat_pow_zero, Nat.mul_one]
  | succ n ih =>
    rw [Nat.add_succ, nat_pow_succ, nat_pow_succ, ih, Nat.mul_assoc]

private theorem nat_two_pow_eight : HPow.hPow (2 : Nat) 8 = 256 := rfl

private theorem nat_two_pow_succ_mul_eight (n : Nat) :
    HPow.hPow (2 : Nat) ((n + 1) * 8) = 256 * HPow.hPow (2 : Nat) (n * 8) := by
  rw [Nat.succ_mul, Nat.add_comm (n * 8) 8, nat_pow_add, nat_two_pow_eight]

private theorem nat_two_pow_mul_eight_succ (i : Nat) :
    HPow.hPow (2 : Nat) (8 * (i + 1)) = 256 * HPow.hPow (2 : Nat) (8 * i) := by
  rw [Nat.mul_succ, Nat.add_comm (8 * i) 8, nat_pow_add, nat_two_pow_eight]

private theorem nat_mod_mul_split_pos (v a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    HMod.hMod v (a * b) =
      HMod.hMod v a + a * HMod.hMod (HDiv.hDiv v a) b := by
  have hdiv_q : HDiv.hDiv v a = b * HDiv.hDiv (HDiv.hDiv v a) b +
      HMod.hMod (HDiv.hDiv v a) b :=
    Eq.symm (Nat.div_add_mod (HDiv.hDiv v a) b)
  have hv_split : v = HMod.hMod v a + a * HMod.hMod (HDiv.hDiv v a) b +
      (a * b) * HDiv.hDiv (HDiv.hDiv v a) b := by
    have h1 : v = a * HDiv.hDiv v a + HMod.hMod v a :=
      Eq.symm (Nat.div_add_mod v a)
    rw [hdiv_q, Nat.mul_add, ← Nat.mul_assoc] at h1
    rw [Nat.add_comm (a * b * HDiv.hDiv (HDiv.hDiv v a) b)
        (a * HMod.hMod (HDiv.hDiv v a) b),
      Nat.add_assoc,
      Nat.add_comm (a * b * HDiv.hDiv (HDiv.hDiv v a) b) (HMod.hMod v a),
      ← Nat.add_assoc,
      Nat.add_comm (a * HMod.hMod (HDiv.hDiv v a) b) (HMod.hMod v a)] at h1
    exact h1
  have hrem_lt :
      HMod.hMod v a + a * HMod.hMod (HDiv.hDiv v a) b < a * b := by
    have hma : HMod.hMod v a < a := Nat.mod_lt v ha
    have hmb : HMod.hMod (HDiv.hDiv v a) b < b := Nat.mod_lt (HDiv.hDiv v a) hb
    have h1 : HMod.hMod v a + a * HMod.hMod (HDiv.hDiv v a) b <
        a + a * HMod.hMod (HDiv.hDiv v a) b :=
      Nat.add_lt_add_right hma (a * HMod.hMod (HDiv.hDiv v a) b)
    have h2 : a + a * HMod.hMod (HDiv.hDiv v a) b =
        a * (HMod.hMod (HDiv.hDiv v a) b + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [h2] at h1
    exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_left a hmb)
  have hmod := congrArg (fun z => HMod.hMod z (a * b)) hv_split
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem_lt] at hmod
  exact hmod

private theorem nat_mod_mul_split (v a b : Nat) :
    HMod.hMod v (a * b) =
      HMod.hMod v a + a * HMod.hMod (HDiv.hDiv v a) b := by
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

private theorem bv_eq_of_toNat_eq {w : Nat} {a b : BitVec w}
    (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | ofFin fa =>
    cases b with
    | ofFin fb =>
      exact congrArg BitVec.ofFin (Fin.eq_of_val_eq h)

private theorem bv_toNat_ofNat (w n : Nat) :
    (BitVec.ofNat w n).toNat = HMod.hMod n (HPow.hPow (2 : Nat) w) :=
  rfl

private theorem list_length_reverseAux {α : Type} (xs acc : List α) :
    (List.reverseAux xs acc).length = xs.length + acc.length := by
  induction xs generalizing acc with
  | nil =>
    rw [List.reverseAux_nil, List.length_nil, Nat.zero_add]
  | cons a rest ih =>
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
  | nil =>
    rfl
  | cons a rest ih =>
    rw [List.reverse_cons, list_reverse_append, ih]
    rfl

private theorem list_append_inj_of_length_eq {α : Type} :
    ∀ {l₁ l₂ r₁ r₂ : List α},
      l₁.length = l₂.length → l₁ ++ r₁ = l₂ ++ r₂ → l₁ = l₂ ∧ r₁ = r₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ r₁ r₂ hlen happ
    cases l₂ with
    | nil =>
      exact ⟨rfl, happ⟩
    | cons _ _ =>
      nomatch hlen
  | cons a rest ih =>
    intro l₂ r₁ r₂ hlen happ
    cases l₂ with
    | nil =>
      nomatch hlen
    | cons b rest₂ =>
      rw [List.cons_append, List.cons_append] at happ
      injection happ with hab htail
      have hlen' : rest.length = rest₂.length := Nat.succ.inj hlen
      have hrec := ih hlen' htail
      have hhead : a :: rest = b :: rest₂ := by
        rw [hab, hrec.1]
      exact ⟨hhead, hrec.2⟩

/-! ## Part 1: Core Definitions and Fixed-Width Aliases -/

/-- Produce `n` little-endian bytes from the low `n * 8` bits of `v`. Using
`@Nat.rec` avoids compiler `_unsafe_rec` auxiliaries while remaining
`rfl`-reducible on `0` and `n + 1`. -/
def toLeBytesAux (n : Nat) (v : Nat) : List (BitVec 8) :=
  @Nat.rec (fun _ => Nat → List (BitVec 8))
    (fun _ => [])
    (fun _ ih k => BitVec.ofNat 8 k :: ih (HDiv.hDiv k 256))
    n v

/-- Base equation of `toLeBytesAux` at zero bytes. -/
@[simp] theorem toLeBytesAux_nil (v : Nat) : toLeBytesAux 0 v = [] := rfl

/-- Step equation of `toLeBytesAux` at `n + 1` bytes. -/
@[simp] theorem toLeBytesAux_succ (n v : Nat) :
    toLeBytesAux (n + 1) v =
      BitVec.ofNat 8 v :: toLeBytesAux n (HDiv.hDiv v 256) :=
  rfl

/-- Encode an `(n * 8)`-bit bitvector into `n` little-endian bytes. -/
def toLeBytes (n : Nat) (x : BitVec (n * 8)) : List (BitVec 8) :=
  toLeBytesAux n x.toNat

/-- Decode a list of little-endian bytes into a natural number. Using
`List.foldr` avoids compiler `_unsafe_rec` auxiliaries while remaining
`rfl`-reducible on `[]` and `b :: rest`. -/
def fromLeBytes (bs : List (BitVec 8)) : Nat :=
  bs.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- Base equation of `fromLeBytes` on the empty byte list. -/
@[simp] theorem fromLeBytes_nil : fromLeBytes [] = 0 := rfl

/-- Step equation of `fromLeBytes` on a non-empty byte list. -/
@[simp] theorem fromLeBytes_cons (b : BitVec 8) (rest : List (BitVec 8)) :
    fromLeBytes (b :: rest) = b.toNat + 256 * fromLeBytes rest :=
  rfl

/-- Decode a list of little-endian bytes into a bitvector of width
`bs.length * 8`. -/
def fromLeBytesBv (bs : List (BitVec 8)) : BitVec (bs.length * 8) :=
  BitVec.ofNat (bs.length * 8) (fromLeBytes bs)

/-- Encode an `(n * 8)`-bit bitvector into `n` big-endian bytes. -/
def toBeBytes (n : Nat) (x : BitVec (n * 8)) : List (BitVec 8) :=
  (toLeBytes n x).reverse

/-- Decode a list of big-endian bytes into a natural number. -/
def fromBeBytes (bs : List (BitVec 8)) : Nat :=
  fromLeBytes bs.reverse

/-- Encode a 16-bit bitvector into 2 little-endian bytes. -/
abbrev u16ToLeBytes (x : BitVec 16) : List (BitVec 8) :=
  toLeBytes 2 x

/-- Encode a 32-bit bitvector into 4 little-endian bytes. -/
abbrev u32ToLeBytes (x : BitVec 32) : List (BitVec 8) :=
  toLeBytes 4 x

/-- Encode a 64-bit bitvector into 8 little-endian bytes. -/
abbrev u64ToLeBytes (x : BitVec 64) : List (BitVec 8) :=
  toLeBytes 8 x

/-- Encode a 128-bit bitvector into 16 little-endian bytes. -/
abbrev u128ToLeBytes (x : BitVec 128) : List (BitVec 8) :=
  toLeBytes 16 x

/-- Decode little-endian bytes into a 16-bit bitvector (modulo `2^16`). -/
abbrev u16FromLeBytes (bs : List (BitVec 8)) : BitVec 16 :=
  BitVec.ofNat 16 (fromLeBytes bs)

/-- Decode little-endian bytes into a 32-bit bitvector (modulo `2^32`). -/
abbrev u32FromLeBytes (bs : List (BitVec 8)) : BitVec 32 :=
  BitVec.ofNat 32 (fromLeBytes bs)

/-- Decode little-endian bytes into a 64-bit bitvector (modulo `2^64`). -/
abbrev u64FromLeBytes (bs : List (BitVec 8)) : BitVec 64 :=
  BitVec.ofNat 64 (fromLeBytes bs)

/-- Decode little-endian bytes into a 128-bit bitvector (modulo `2^128`). -/
abbrev u128FromLeBytes (bs : List (BitVec 8)) : BitVec 128 :=
  BitVec.ofNat 128 (fromLeBytes bs)

/-! ## Part 2: Length and Range Bounds -/

/-- `toLeBytesAux n v` always produces exactly `n` bytes. -/
@[simp] theorem toLeBytesAux_length (n v : Nat) :
    (toLeBytesAux n v).length = n := by
  induction n generalizing v with
  | zero =>
    rfl
  | succ n ih =>
    rw [toLeBytesAux_succ, List.length_cons, ih]

/-- `toLeBytes n x` always produces exactly `n` bytes. -/
@[simp] theorem toLeBytes_length (n : Nat) (x : BitVec (n * 8)) :
    (toLeBytes n x).length = n :=
  toLeBytesAux_length n x.toNat

/-- `toBeBytes n x` always produces exactly `n` bytes. -/
@[simp] theorem toBeBytes_length (n : Nat) (x : BitVec (n * 8)) :
    (toBeBytes n x).length = n := by
  unfold toBeBytes
  rw [list_length_reverse, toLeBytes_length]

/-- Every little-endian byte list decodes strictly below `2^(bs.length * 8)`.
-/
theorem fromLeBytes_lt (bs : List (BitVec 8)) :
    fromLeBytes bs < HPow.hPow (2 : Nat) (bs.length * 8) := by
  induction bs with
  | nil =>
    exact Nat.zero_lt_one
  | cons b rest ih =>
    rw [fromLeBytes_cons, List.length_cons, nat_two_pow_succ_mul_eight]
    have hb : b.toNat < 256 := b.isLt
    have h1 : b.toNat + 256 * fromLeBytes rest <
        256 + 256 * fromLeBytes rest :=
      Nat.add_lt_add_right hb (256 * fromLeBytes rest)
    have h2 : 256 + 256 * fromLeBytes rest = 256 * (fromLeBytes rest + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [h2] at h1
    exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_left 256 ih)

/-- Every big-endian byte list decodes strictly below `2^(bs.length * 8)`. -/
theorem fromBeBytes_lt (bs : List (BitVec 8)) :
    fromBeBytes bs < HPow.hPow (2 : Nat) (bs.length * 8) := by
  unfold fromBeBytes
  have h := fromLeBytes_lt bs.reverse
  rw [list_length_reverse] at h
  exact h

/-- `fromLeBytesBv` preserves the exact natural value of `fromLeBytes`. -/
@[simp] theorem fromLeBytesBv_toNat (bs : List (BitVec 8)) :
    (fromLeBytesBv bs).toNat = fromLeBytes bs := by
  unfold fromLeBytesBv
  rw [bv_toNat_ofNat]
  exact Nat.mod_eq_of_lt (fromLeBytes_lt bs)

/-! ## Part 3: Round-Trip, Injectivity, and Zero-Byte Identities -/

/-- Decoding `toLeBytesAux n v` recovers `v mod 2^(n * 8)`. -/
@[simp] theorem fromLeBytes_toLeBytesAux (n v : Nat) :
    fromLeBytes (toLeBytesAux n v) =
      HMod.hMod v (HPow.hPow (2 : Nat) (n * 8)) := by
  induction n generalizing v with
  | zero =>
    rw [toLeBytesAux_nil, fromLeBytes_nil, Nat.zero_mul, nat_pow_zero,
      Nat.mod_one]
  | succ n ih =>
    rw [toLeBytesAux_succ, fromLeBytes_cons, ih, bv_toNat_ofNat,
      nat_two_pow_eight, nat_two_pow_succ_mul_eight]
    exact Eq.symm (nat_mod_mul_split v 256 (HPow.hPow (2 : Nat) (n * 8)))

/-- Decoding `toLeBytes n x` recovers `x.toNat`. -/
@[simp] theorem fromLeBytes_toLeBytes (n : Nat) (x : BitVec (n * 8)) :
    fromLeBytes (toLeBytes n x) = x.toNat := by
  unfold toLeBytes
  rw [fromLeBytes_toLeBytesAux, Nat.mod_eq_of_lt x.isLt]

/-- Decoding `toBeBytes n x` in big-endian order recovers `x.toNat`. -/
@[simp] theorem fromBeBytes_toBeBytes (n : Nat) (x : BitVec (n * 8)) :
    fromBeBytes (toBeBytes n x) = x.toNat := by
  unfold fromBeBytes toBeBytes
  rw [list_reverse_reverse, fromLeBytes_toLeBytes]

/-- Re-encoding `fromLeBytes bs` at width `bs.length` recovers `bs`. -/
@[simp] theorem toLeBytesAux_fromLeBytes (bs : List (BitVec 8)) :
    toLeBytesAux bs.length (fromLeBytes bs) = bs := by
  induction bs with
  | nil =>
    rfl
  | cons b rest ih =>
    rw [List.length_cons, fromLeBytes_cons, toLeBytesAux_succ]
    have hhead : BitVec.ofNat 8 (b.toNat + 256 * fromLeBytes rest) = b := by
      apply bv_eq_of_toNat_eq
      rw [bv_toNat_ofNat, nat_two_pow_eight, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt b.isLt]
    have hdiv : HDiv.hDiv (b.toNat + 256 * fromLeBytes rest) 256 =
        fromLeBytes rest := by
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 256),
        Nat.div_eq_of_lt b.isLt, Nat.zero_add]
    rw [hhead, hdiv, ih]

/-- `toLeBytes n` is injective on `BitVec (n * 8)`. -/
theorem toLeBytes_injective {n : Nat} {a b : BitVec (n * 8)}
    (h : toLeBytes n a = toLeBytes n b) : a = b := by
  apply bv_eq_of_toNat_eq
  rw [← fromLeBytes_toLeBytes n a, ← fromLeBytes_toLeBytes n b, h]

/-- `toBeBytes n` is injective on `BitVec (n * 8)`. -/
theorem toBeBytes_injective {n : Nat} {a b : BitVec (n * 8)}
    (h : toBeBytes n a = toBeBytes n b) : a = b := by
  unfold toBeBytes at h
  have hrev := congrArg List.reverse h
  rw [list_reverse_reverse, list_reverse_reverse] at hrev
  exact toLeBytes_injective hrev

/-- `fromLeBytes` is injective among equal-length byte lists. -/
theorem fromLeBytes_injective {xs ys : List (BitVec 8)}
    (hlen : xs.length = ys.length) (h : fromLeBytes xs = fromLeBytes ys) :
    xs = ys := by
  rw [← toLeBytesAux_fromLeBytes xs, ← toLeBytesAux_fromLeBytes ys, hlen, h]

/-- `fromBeBytes` is injective among equal-length byte lists. -/
theorem fromBeBytes_injective {xs ys : List (BitVec 8)}
    (hlen : xs.length = ys.length) (h : fromBeBytes xs = fromBeBytes ys) :
    xs = ys := by
  unfold fromBeBytes at h
  have hlen_rev : xs.reverse.length = ys.reverse.length := by
    rw [list_length_reverse, list_length_reverse, hlen]
  have hrev := fromLeBytes_injective hlen_rev h
  have hrev2 := congrArg List.reverse hrev
  rw [list_reverse_reverse, list_reverse_reverse] at hrev2
  exact hrev2

/-- Round-trip identity for `u16FromLeBytes ∘ u16ToLeBytes`. -/
@[simp] theorem u16FromLeBytes_u16ToLeBytes (x : BitVec 16) :
    u16FromLeBytes (u16ToLeBytes x) = x := by
  apply bv_eq_of_toNat_eq
  rw [bv_toNat_ofNat, fromLeBytes_toLeBytes 2 x, Nat.mod_eq_of_lt x.isLt]

/-- Round-trip identity for `u32FromLeBytes ∘ u32ToLeBytes`. -/
@[simp] theorem u32FromLeBytes_u32ToLeBytes (x : BitVec 32) :
    u32FromLeBytes (u32ToLeBytes x) = x := by
  apply bv_eq_of_toNat_eq
  rw [bv_toNat_ofNat, fromLeBytes_toLeBytes 4 x, Nat.mod_eq_of_lt x.isLt]

/-- Round-trip identity for `u64FromLeBytes ∘ u64ToLeBytes`. -/
@[simp] theorem u64FromLeBytes_u64ToLeBytes (x : BitVec 64) :
    u64FromLeBytes (u64ToLeBytes x) = x := by
  apply bv_eq_of_toNat_eq
  rw [bv_toNat_ofNat, fromLeBytes_toLeBytes 8 x, Nat.mod_eq_of_lt x.isLt]

/-- Round-trip identity for `u128FromLeBytes ∘ u128ToLeBytes`. -/
@[simp] theorem u128FromLeBytes_u128ToLeBytes (x : BitVec 128) :
    u128FromLeBytes (u128ToLeBytes x) = x := by
  apply bv_eq_of_toNat_eq
  rw [bv_toNat_ofNat, fromLeBytes_toLeBytes 16 x, Nat.mod_eq_of_lt x.isLt]

/-- Encoding zero produces `n` zero bytes. -/
@[simp] theorem toLeBytesAux_zero (n : Nat) :
    toLeBytesAux n 0 = List.replicate n (BitVec.ofNat 8 0) := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [toLeBytesAux_succ, List.replicate_succ, Nat.zero_div, ih]

/-- Decoding `n` zero bytes yields zero. -/
@[simp] theorem fromLeBytes_replicate_zero (n : Nat) :
    fromLeBytes (List.replicate n (BitVec.ofNat 8 0)) = 0 := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [List.replicate_succ, fromLeBytes_cons, ih, Nat.mul_zero, Nat.add_zero]
    rfl

/-! ## Part 4: Byte Indexing, Concatenation, and Closed Forms -/

/-- Optional lookup of the `i`-th little-endian byte of `toLeBytesAux n v`. -/
theorem toLeBytes_getElem? (n v i : Nat) (hi : i < n) :
    (toLeBytesAux n v)[i]? =
      some (BitVec.ofNat 8 (HDiv.hDiv v (HPow.hPow (2 : Nat) (8 * i)))) := by
  induction n generalizing v i with
  | zero =>
    exact False.elim (Nat.not_lt_zero i hi)
  | succ n ih =>
    rw [toLeBytesAux_succ]
    cases i with
    | zero =>
      rw [Nat.mul_zero, nat_pow_zero, Nat.div_one]
      rfl
    | succ i =>
      have hstep :
          (BitVec.ofNat 8 v :: toLeBytesAux n (HDiv.hDiv v 256))[i + 1]? =
            (toLeBytesAux n (HDiv.hDiv v 256))[i]? :=
        rfl
      rw [hstep, ih (HDiv.hDiv v 256) i (Nat.lt_of_succ_lt_succ hi),
        Nat.div_div_eq_div_mul, ← nat_two_pow_mul_eight_succ]

/-- Direct indexed lookup of the `i`-th little-endian byte of `toLeBytes n x`
(definitionally equal to `(toLeBytes n x)[i]'hi`). -/
theorem toLeBytes_getElem (n : Nat) (x : BitVec (n * 8)) (i : Nat)
    (hi : i < (toLeBytes n x).length) :
    GetElem.getElem (toLeBytes n x) i hi =
      BitVec.ofNat 8 (HDiv.hDiv x.toNat (HPow.hPow (2 : Nat) (8 * i))) := by
  have hi' : i < n := by
    rw [toLeBytes_length] at hi
    exact hi
  have hopt : (toLeBytes n x)[i]? =
      some (BitVec.ofNat 8
        (HDiv.hDiv x.toNat (HPow.hPow (2 : Nat) (8 * i)))) :=
    toLeBytes_getElem? n x.toNat i hi'
  have hdef :
      (toLeBytes n x)[i]? = some (GetElem.getElem (toLeBytes n x) i hi) :=
    getElem?_pos (toLeBytes n x) i hi
  rw [hdef] at hopt
  injection hopt

/-- Little-endian decoding distributes over list concatenation with a
`2^(xs.length * 8)` radix shift. -/
theorem fromLeBytes_append (xs ys : List (BitVec 8)) :
    fromLeBytes (xs ++ ys) =
      fromLeBytes xs + HPow.hPow (2 : Nat) (xs.length * 8) * fromLeBytes ys := by
  induction xs with
  | nil =>
    rw [List.nil_append, fromLeBytes_nil, List.length_nil, Nat.zero_mul,
      nat_pow_zero, Nat.one_mul, Nat.zero_add]
  | cons b rest ih =>
    rw [List.cons_append, fromLeBytes_cons, fromLeBytes_cons, List.length_cons,
      ih, Nat.mul_add, ← Nat.add_assoc, ← Nat.mul_assoc,
      ← nat_two_pow_succ_mul_eight]

/-- Splitting `toLeBytesAux (m + n) v` into its low `m` bytes and high `n`
bytes. -/
theorem toLeBytesAux_add (m n v : Nat) :
    toLeBytesAux (m + n) v =
      toLeBytesAux m v ++
        toLeBytesAux n (HDiv.hDiv v (HPow.hPow (2 : Nat) (m * 8))) := by
  induction m generalizing v with
  | zero =>
    rw [Nat.zero_add, toLeBytesAux_nil, List.nil_append, Nat.zero_mul,
      nat_pow_zero, Nat.div_one]
  | succ m ih =>
    rw [Nat.succ_add, toLeBytesAux_succ, toLeBytesAux_succ, List.cons_append,
      ih (HDiv.hDiv v 256), Nat.div_div_eq_div_mul,
      ← nat_two_pow_succ_mul_eight]

/-- Concatenation of two fixed-width little-endian encodings is jointly
injective. -/
theorem toLeBytes_append_injective {m n : Nat}
    {a₁ a₂ : BitVec (m * 8)} {b₁ b₂ : BitVec (n * 8)}
    (h : toLeBytes m a₁ ++ toLeBytes n b₁ = toLeBytes m a₂ ++ toLeBytes n b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hlen : (toLeBytes m a₁).length = (toLeBytes m a₂).length := by
    rw [toLeBytes_length, toLeBytes_length]
  have hsplit := list_append_inj_of_length_eq hlen h
  exact ⟨toLeBytes_injective hsplit.1, toLeBytes_injective hsplit.2⟩

/-- Explicit 2-byte little-endian expansion for `BitVec 16`. -/
theorem toLeBytes_u16_eq (x : BitVec 16) :
    u16ToLeBytes x =
      [ BitVec.ofNat 8 x.toNat,
        BitVec.ofNat 8 (HDiv.hDiv x.toNat (HPow.hPow (2 : Nat) 8)) ] :=
  rfl

/-- Explicit 4-byte little-endian expansion for `BitVec 32`. -/
theorem toLeBytes_u32_eq (x : BitVec 32) :
    u32ToLeBytes x =
      [ BitVec.ofNat 8 x.toNat,
        BitVec.ofNat 8 (HDiv.hDiv x.toNat (HPow.hPow (2 : Nat) 8)),
        BitVec.ofNat 8 (HDiv.hDiv x.toNat (HPow.hPow (2 : Nat) 16)),
        BitVec.ofNat 8 (HDiv.hDiv x.toNat (HPow.hPow (2 : Nat) 24)) ] := by
  unfold u32ToLeBytes toLeBytes
  rw [toLeBytesAux_succ, toLeBytesAux_succ, toLeBytesAux_succ,
    toLeBytesAux_succ, toLeBytesAux_nil]
  repeat rw [Nat.div_div_eq_div_mul]

/-- Explicit 8-byte little-endian expansion for `BitVec 64`. -/
theorem toLeBytes_u64_eq (x : BitVec 64) :
    u64ToLeBytes x =
      [ BitVec.ofNat 8 x.toNat,
        BitVec.ofNat 8 (HDiv.hDiv x.toNat (HPow.hPow (2 : Nat) 8)),
        BitVec.ofNat 8 (HDiv.hDiv x.toNat (HPow.hPow (2 : Nat) 16)),
        BitVec.ofNat 8 (HDiv.hDiv x.toNat (HPow.hPow (2 : Nat) 24)),
        BitVec.ofNat 8 (HDiv.hDiv x.toNat (HPow.hPow (2 : Nat) 32)),
        BitVec.ofNat 8 (HDiv.hDiv x.toNat (HPow.hPow (2 : Nat) 40)),
        BitVec.ofNat 8 (HDiv.hDiv x.toNat (HPow.hPow (2 : Nat) 48)),
        BitVec.ofNat 8 (HDiv.hDiv x.toNat (HPow.hPow (2 : Nat) 56)) ] := by
  unfold u64ToLeBytes toLeBytes
  rw [toLeBytesAux_succ, toLeBytesAux_succ, toLeBytesAux_succ,
    toLeBytesAux_succ, toLeBytesAux_succ, toLeBytesAux_succ,
    toLeBytesAux_succ, toLeBytesAux_succ, toLeBytesAux_nil]
  repeat rw [Nat.div_div_eq_div_mul]

end Anneal.LeBytes
