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
public import Init.Data.Option.Basic
public import Anneal.MediaBits.BitCursor

public section

/-!
# Canonical Parse-and-Reserialize Filters (`Anneal.CanonicalDiode`)

A filter that sits between an untrusted producer and a downstream consumer can
parse each message into an AST and emit a fresh canonical encoding of that AST
instead of forwarding the original bytes. The downstream consumer then only
ever sees encodings that the filter's own serializer produced. This module
states the laws such a filter needs and proves that they compose:

1. **Whole-input codec laws (`Codec`):** `DecEnc` (`dec (enc a) = some a`),
   `EncDec` (`dec b = some a → enc a = b`), and `DecInj` (at most one accepted
   wire value per AST). `lawful_iff_decEnc_and_decInj` shows that `EncDec` is
   exactly `DecInj` once `DecEnc` holds. `DecEnc` alone permits several wire
   values for one AST; the canaries exhibit such a codec.
2. **Prefix codecs (`PrefixCodec`):** decoders that return the unconsumed
   suffix. `PrefixDecEnc` implies `PrefixFree` (an encoding followed by any
   suffix, `enc a ++ rest`, determines both `a` and `rest`), and
   `PrefixCodec.whole` lifts the prefix laws to whole-input `DecEnc` and
   `EncDec`.
3. **Framed sequences (`listCodec`):** the greedy concatenation decoder for a
   prefix codec runs with an explicit iteration budget. For a prefix codec
   satisfying both prefix laws with non-empty encodings, `listCodec` is
   lawful and injective, and an input of length `n` needs at most `n + 1`
   decoder iterations (`listDecFuel_linear`). Non-empty encodings are also
   necessary (`nonEmptyEnc_of_listCodec_decEnc`). Each successful element
   decode consumes at least one token (`PrefixCodec.dec_length_lt`), so the
   remaining input length strictly decreases on every iteration. That length
   can serve as the credit measure of `Anneal.StepBound.v2_loop_byte_credit`
   (not imported here), which also needs a bound on the MIR steps of each
   iteration of a compiled decode loop.
4. **Canonical filters (`CanonicalDiode`):** an upstream parser paired with a
   canonical codec, packaged as an `Anneal.MediaBits.DualContextTranscoder`
   with unit contexts. `CanonicalDiode.filter_sound` proves that every emitted
   message decodes, under the canonical decoder, to the AST the upstream parser
   produced, and that it equals the canonical encoding of that AST.
   `CanonicalDiode.filter_eq_iff` proves that two emitted messages are equal
   exactly when their inputs parsed to the same AST.
   `CanonicalDiode.stream_sound` lifts these per-message facts to packet
   streams through `Anneal.MediaBits.dualContext_transcodeStream_sound`.

Definitions use `Nat.rec` and `List.foldr` (`0` `._unsafe_rec`), and every
declaration depends on at most `propext`.
-/

namespace Anneal.CanonicalDiode

/-! ## Part I: Whole-input codec laws -/

/-- A whole-input codec: a total encoder and a partial decoder that rejects
malformed wire values with `none`. -/
structure Codec (A B : Type) where
  enc : A → B
  dec : B → Option A

/-- Decode-after-encode: every encoded value decodes back to itself. -/
@[expose] def DecEnc {A B : Type} (c : Codec A B) : Prop :=
  ∀ a : A, c.dec (c.enc a) = some a

/-- Encode-after-decode (canonicality): every accepted wire value is the
encoding of the value it decodes to. -/
@[expose] def EncDec {A B : Type} (c : Codec A B) : Prop :=
  ∀ (b : B) (a : A), c.dec b = some a → c.enc a = b

/-- Decoder injectivity: at most one accepted wire value decodes to any given
value. -/
@[expose] def DecInj {A B : Type} (c : Codec A B) : Prop :=
  ∀ (b₁ b₂ : B) (a : A), c.dec b₁ = some a → c.dec b₂ = some a → b₁ = b₂

/-- Both round-trip laws. -/
@[expose] def Lawful {A B : Type} (c : Codec A B) : Prop :=
  DecEnc c ∧ EncDec c

theorem decInj_of_encDec {A B : Type} {c : Codec A B} (h : EncDec c) :
    DecInj c :=
  fun b₁ b₂ a h₁ h₂ => (h b₁ a h₁).symm.trans (h b₂ a h₂)

theorem encDec_of_decEnc_decInj {A B : Type} {c : Codec A B}
    (hde : DecEnc c) (hinj : DecInj c) : EncDec c :=
  fun b a h => hinj (c.enc a) b a (hde a) h

/-- Given `DecEnc`, canonicality (`EncDec`) is equivalent to decoder
injectivity (`DecInj`). -/
theorem lawful_iff_decEnc_and_decInj {A B : Type} (c : Codec A B) :
    Lawful c ↔ DecEnc c ∧ DecInj c :=
  ⟨fun h => ⟨h.1, decInj_of_encDec h.2⟩,
   fun h => ⟨h.1, encDec_of_decEnc_decInj h.1 h.2⟩⟩

/-- `DecEnc` makes the encoder injective. -/
theorem enc_injective_of_decEnc {A B : Type} {c : Codec A B} (hde : DecEnc c)
    {a₁ a₂ : A} (h : c.enc a₁ = c.enc a₂) : a₁ = a₂ := by
  have h1 := hde a₁
  rw [h, hde a₂] at h1
  injection h1 with h1
  exact h1.symm

/-! ## Part II: Prefix codecs -/

/-- A prefix codec over token lists: `dec` parses one value from the front of
its input and returns the unconsumed suffix. -/
structure PrefixCodec (A T : Type) where
  enc : A → List T
  dec : List T → Option (A × List T)

/-- Decoding an encoding followed by any suffix returns the value and leaves
the suffix untouched. -/
@[expose] def PrefixDecEnc {A T : Type} (p : PrefixCodec A T) : Prop :=
  ∀ (a : A) (rest : List T), p.dec (p.enc a ++ rest) = some (a, rest)

/-- Every successful decode consumes exactly the canonical encoding of the
decoded value. -/
@[expose] def PrefixEncDec {A T : Type} (p : PrefixCodec A T) : Prop :=
  ∀ (bs : List T) (a : A) (rest : List T),
    p.dec bs = some (a, rest) → p.enc a ++ rest = bs

/-- A concatenation `enc a ++ rest` determines both `a` and `rest`. -/
@[expose] def PrefixFree {A T : Type} (p : PrefixCodec A T) : Prop :=
  ∀ (a₁ a₂ : A) (r₁ r₂ : List T),
    p.enc a₁ ++ r₁ = p.enc a₂ ++ r₂ → a₁ = a₂ ∧ r₁ = r₂

/-- No value encodes to the empty token list. -/
@[expose] def NonEmptyEnc {A T : Type} (p : PrefixCodec A T) : Prop :=
  ∀ a : A, p.enc a ≠ []

/-- Under `PrefixEncDec` and `NonEmptyEnc`, every successful decode consumes at
least one token. -/
theorem PrefixCodec.dec_length_lt {A T : Type} {p : PrefixCodec A T}
    (hed : PrefixEncDec p) (hne : NonEmptyEnc p) {bs : List T} {a : A}
    {rest : List T} (h : p.dec bs = some (a, rest)) :
    rest.length < bs.length := by
  have he := hed bs a rest h
  rw [← he, List.length_append]
  cases hEnc : p.enc a with
  | nil => exact absurd hEnc (hne a)
  | cons t ts =>
    rw [List.length_cons, Nat.add_comm (ts.length + 1)]
    exact Nat.lt_add_of_pos_right (Nat.succ_pos ts.length)

theorem prefixFree_of_prefixDecEnc {A T : Type} {p : PrefixCodec A T}
    (h : PrefixDecEnc p) : PrefixFree p := by
  intro a₁ a₂ r₁ r₂ heq
  have h1 := h a₁ r₁
  rw [heq, h a₂ r₂] at h1
  injection h1 with h1
  injection h1 with ha hr
  exact ⟨ha.symm, hr.symm⟩

/-- Whole-input codec accepting exactly one encoded value and no trailing
tokens. -/
@[expose] def PrefixCodec.whole {A T : Type} (p : PrefixCodec A T) :
    Codec A (List T) where
  enc := p.enc
  dec bs := (p.dec bs).bind (fun r => List.casesOn (motive := fun _ => Option A)
    r.2 (some r.1) (fun _ _ => none))

theorem PrefixCodec.whole_decEnc {A T : Type} {p : PrefixCodec A T}
    (h : PrefixDecEnc p) : DecEnc p.whole := by
  intro a
  have h1 := h a []
  rw [List.append_nil] at h1
  dsimp only [PrefixCodec.whole]
  rw [h1]
  rfl

theorem PrefixCodec.whole_encDec {A T : Type} {p : PrefixCodec A T}
    (h : PrefixEncDec p) : EncDec p.whole := by
  intro bs a hdec
  dsimp only [PrefixCodec.whole] at hdec
  dsimp only [PrefixCodec.whole]
  cases hp : p.dec bs with
  | none =>
    rw [hp] at hdec
    nomatch hdec
  | some r =>
    rw [hp] at hdec
    cases r with
    | mk a' rest =>
      cases rest with
      | nil =>
        injection hdec with ha
        have h1 := h bs a' [] hp
        rw [List.append_nil] at h1
        rw [← ha]
        exact h1
      | cons t ts =>
        nomatch hdec

/-! ## Part III: Framed sequences with a linear iteration budget -/

/-- Concatenated encoding of a list of values. -/
@[expose] def listEnc {A T : Type} (p : PrefixCodec A T) (as : List A) :
    List T :=
  List.foldr (fun a acc => p.enc a ++ acc) [] as

/-- Greedy concatenation decoder with an explicit iteration budget `fuel`.
Each iteration either accepts the exhausted input or decodes one value from
the front; running out of budget rejects. -/
@[expose] def listDecFuel {A T : Type} (p : PrefixCodec A T) (fuel : Nat) :
    List T → Option (List A) :=
  Nat.rec (motive := fun _ => List T → Option (List A))
    (fun _ => none)
    (fun _ ih bs =>
      List.casesOn (motive := fun _ => Option (List A)) bs
        (some [])
        (fun _ _ =>
          (p.dec bs).bind (fun r => (ih r.2).map (fun as => r.1 :: as))))
    fuel

/-- Whole-input codec for lists of values, decoding with budget
`bs.length + 1`. -/
@[expose] def listCodec {A T : Type} (p : PrefixCodec A T) :
    Codec (List A) (List T) where
  enc := listEnc p
  dec bs := listDecFuel p (bs.length + 1) bs

theorem listEnc_nil {A T : Type} (p : PrefixCodec A T) : listEnc p [] = [] :=
  rfl

theorem listEnc_cons {A T : Type} (p : PrefixCodec A T) (a : A)
    (as : List A) : listEnc p (a :: as) = p.enc a ++ listEnc p as :=
  rfl

theorem listDecFuel_zero {A T : Type} (p : PrefixCodec A T) (bs : List T) :
    listDecFuel p 0 bs = none :=
  rfl

theorem listDecFuel_succ_nil {A T : Type} (p : PrefixCodec A T) (f : Nat) :
    listDecFuel p (f + 1) [] = some [] :=
  rfl

theorem listDecFuel_succ_cons {A T : Type} (p : PrefixCodec A T) (f : Nat)
    (t : T) (ts : List T) :
    listDecFuel p (f + 1) (t :: ts) =
      (p.dec (t :: ts)).bind
        (fun r => (listDecFuel p f r.2).map (fun as => r.1 :: as)) :=
  rfl

theorem listDecFuel_succ_of_ne_nil {A T : Type} (p : PrefixCodec A T)
    (f : Nat) {bs : List T} (h : bs ≠ []) :
    listDecFuel p (f + 1) bs =
      (p.dec bs).bind
        (fun r => (listDecFuel p f r.2).map (fun as => r.1 :: as)) := by
  cases bs with
  | nil => exact absurd rfl h
  | cons t ts => rfl

/-- Under `NonEmptyEnc`, a list of `n` values encodes to at least `n` tokens. -/
theorem length_le_listEnc_length {A T : Type} {p : PrefixCodec A T}
    (hne : NonEmptyEnc p) : ∀ as : List A, as.length ≤ (listEnc p as).length
  | [] => Nat.le_refl 0
  | a :: as => by
    rw [listEnc_cons, List.length_append, List.length_cons]
    have ih := length_le_listEnc_length hne as
    cases hEnc : p.enc a with
    | nil => exact absurd hEnc (hne a)
    | cons t ts =>
      have h2 : (listEnc p as).length + 1 ≤
          ts.length + 1 + (listEnc p as).length := by
        rw [Nat.add_comm ts.length 1, Nat.add_assoc, Nat.add_comm 1]
        exact Nat.succ_le_succ (Nat.le_add_left _ _)
      rw [List.length_cons]
      exact Nat.le_trans (Nat.succ_le_succ ih) h2

/-- `PrefixDecEnc` and `NonEmptyEnc` make every budget above the list length
sufficient to decode its encoding. -/
theorem listDecFuel_listEnc {A T : Type} {p : PrefixCodec A T}
    (hde : PrefixDecEnc p) (hne : NonEmptyEnc p) :
    ∀ (as : List A) (fuel : Nat),
      as.length < fuel → listDecFuel p fuel (listEnc p as) = some as
  | [], 0, h => absurd h (Nat.not_lt_zero 0)
  | [], f + 1, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_lt_zero _)
  | a :: as, f + 1, h => by
    have hlt : as.length < f := Nat.lt_of_succ_lt_succ h
    have hne' : listEnc p (a :: as) ≠ [] := by
      rw [listEnc_cons]
      cases hEnc : p.enc a with
      | nil => exact absurd hEnc (hne a)
      | cons t ts =>
        intro hnil
        nomatch hnil
    rw [listDecFuel_succ_of_ne_nil p f hne', listEnc_cons, hde a (listEnc p as)]
    rw [Option.bind_some]
    dsimp only
    rw [listDecFuel_listEnc hde hne as f hlt]
    rfl

/-- `PrefixEncDec` makes every accepted input the canonical encoding of the
decoded list, for any budget. -/
theorem listEnc_of_listDecFuel {A T : Type} {p : PrefixCodec A T}
    (hed : PrefixEncDec p) :
    ∀ (fuel : Nat) (bs : List T) (as : List A),
      listDecFuel p fuel bs = some as → listEnc p as = bs
  | 0, _, _, h => by
    rw [listDecFuel_zero] at h
    nomatch h
  | f + 1, [], as, h => by
    rw [listDecFuel_succ_nil] at h
    injection h with h
    rw [← h]
    rfl
  | f + 1, t :: ts, as, h => by
    rw [listDecFuel_succ_cons] at h
    cases hp : p.dec (t :: ts) with
    | none =>
      rw [hp] at h
      nomatch h
    | some r =>
      rw [hp, Option.bind_some] at h
      cases r with
      | mk a rest =>
        dsimp only at h
        cases hRest : listDecFuel p f rest with
        | none =>
          rw [hRest] at h
          nomatch h
        | some as' =>
          rw [hRest, Option.map_some] at h
          injection h with h
          rw [← h, listEnc_cons, listEnc_of_listDecFuel hed f rest as' hRest]
          exact hed (t :: ts) a rest hp

/-- Linear iteration bound: whenever some budget decodes `bs`, the budget
`bs.length + 1` decodes it to the same list, and the list has at most
`bs.length` elements. -/
theorem listDecFuel_linear {A T : Type} {p : PrefixCodec A T}
    (hde : PrefixDecEnc p) (hed : PrefixEncDec p) (hne : NonEmptyEnc p)
    {fuel : Nat} {bs : List T} {as : List A}
    (h : listDecFuel p fuel bs = some as) :
    listDecFuel p (bs.length + 1) bs = some as ∧ as.length ≤ bs.length := by
  have hbs := listEnc_of_listDecFuel hed fuel bs as h
  have hlen := length_le_listEnc_length hne as
  rw [hbs] at hlen
  refine ⟨?_, hlen⟩
  have hdec := listDecFuel_listEnc hde hne as (bs.length + 1)
    (Nat.lt_succ_of_le hlen)
  rw [hbs] at hdec
  exact hdec

theorem listCodec_decEnc {A T : Type} {p : PrefixCodec A T}
    (hde : PrefixDecEnc p) (hne : NonEmptyEnc p) : DecEnc (listCodec p) :=
  fun as => listDecFuel_listEnc hde hne as _
    (Nat.lt_succ_of_le (length_le_listEnc_length hne as))

theorem listCodec_encDec {A T : Type} {p : PrefixCodec A T}
    (hed : PrefixEncDec p) : EncDec (listCodec p) :=
  fun bs as h => listEnc_of_listDecFuel hed (bs.length + 1) bs as h

theorem listCodec_lawful {A T : Type} {p : PrefixCodec A T}
    (hde : PrefixDecEnc p) (hed : PrefixEncDec p) (hne : NonEmptyEnc p) :
    Lawful (listCodec p) :=
  ⟨listCodec_decEnc hde hne, listCodec_encDec hed⟩

theorem listCodec_decInj {A T : Type} {p : PrefixCodec A T}
    (hed : PrefixEncDec p) : DecInj (listCodec p) :=
  decInj_of_encDec (listCodec_encDec hed)

/-- Non-empty encodings are necessary: if some value encodes to `[]`, then
`[a]` and `[]` share the wire value `[]` and `listCodec` cannot satisfy
`DecEnc`. -/
theorem nonEmptyEnc_of_listCodec_decEnc {A T : Type} {p : PrefixCodec A T}
    (h : DecEnc (listCodec p)) : NonEmptyEnc p := by
  intro a hEnc
  have h1 := h [a]
  have hwire : (listCodec p).enc [a] = [] := by
    dsimp only [listCodec]
    rw [listEnc_cons, listEnc_nil, hEnc]
    rfl
  rw [hwire] at h1
  have h2 : (listCodec p).dec [] = some [] := rfl
  rw [h2] at h1
  injection h1 with h1
  nomatch h1

/-! ## Part IV: Canonical filters as dual-context transcoders -/

/-- Stateless `IndexedCodec` view of a whole-input codec. -/
@[expose] def Codec.toIndexed {A B : Type} (c : Codec A B) :
    MediaBits.IndexedCodec Unit A B where
  get _ b := (c.dec b).map (fun a => ((), a))
  put _ a := some ((), c.enc a)

theorem Codec.toIndexed_putGet {A B : Type} {c : Codec A B}
    (h : DecEnc c) : MediaBits.IndexedPutGet c.toIndexed := by
  intro s a s' b hput
  cases s
  cases s'
  dsimp only [Codec.toIndexed] at hput
  dsimp only [Codec.toIndexed]
  injection hput with hput
  injection hput with _ hb
  rw [← hb, h a]
  rfl

theorem Codec.toIndexed_getPut {A B : Type} {c : Codec A B}
    (h : EncDec c) : MediaBits.IndexedGetPut c.toIndexed := by
  intro s b s' a hget
  cases s
  cases s'
  dsimp only [Codec.toIndexed] at hget
  dsimp only [Codec.toIndexed]
  cases hd : c.dec b with
  | none =>
    rw [hd] at hget
    nomatch hget
  | some a' =>
    rw [hd, Option.map_some] at hget
    injection hget with hget
    injection hget with _ ha
    rw [← ha, h b a' hd]

/-- A canonical filter: an upstream parser, which may accept several wire
forms of one AST, paired with the canonical codec used to re-emit it. -/
structure CanonicalDiode (A B : Type) where
  parse : B → Option A
  canon : Codec A B

/-- Parse with the upstream parser, then emit the canonical encoding. -/
@[expose] def CanonicalDiode.filter {A B : Type} (d : CanonicalDiode A B)
    (raw : B) : Option B :=
  (d.parse raw).map d.canon.enc

/-- The filter as a dual-context transcoder with unit contexts and the
identity rewrite. -/
@[expose] def CanonicalDiode.transcoder {A B : Type} (d : CanonicalDiode A B) :
    MediaBits.DualContextTranscoder Unit Unit A B where
  inCodec :=
    { get := fun _ b => (d.parse b).map (fun a => ((), a))
      put := fun _ a => some ((), d.canon.enc a) }
  outCodec := d.canon.toIndexed
  rewrite _ _ a := some a

theorem CanonicalDiode.transcodeOne_eq {A B : Type} (d : CanonicalDiode A B)
    (raw : B) :
    MediaBits.transcodeOne d.transcoder () () raw =
      (d.filter raw).map (fun out => ((), (), out)) := by
  unfold MediaBits.transcodeOne CanonicalDiode.filter
  cases hp : d.parse raw with
  | none =>
    dsimp only [CanonicalDiode.transcoder]
    rw [hp]
    rfl
  | some a =>
    dsimp only [CanonicalDiode.transcoder]
    rw [hp]
    rfl

/-- Per-message soundness: every emitted message decodes, under the canonical
decoder, to the AST that the upstream parser produced, and equals the
canonical encoding of that AST. -/
theorem CanonicalDiode.filter_sound {A B : Type} {d : CanonicalDiode A B}
    (hde : DecEnc d.canon) {raw out : B} (h : d.filter raw = some out) :
    ∃ a : A, d.parse raw = some a ∧ d.canon.dec out = some a ∧
      d.canon.enc a = out := by
  dsimp only [CanonicalDiode.filter] at h
  cases hp : d.parse raw with
  | none =>
    rw [hp] at h
    nomatch h
  | some a =>
    rw [hp, Option.map_some] at h
    injection h with h
    refine ⟨a, rfl, ?_, h⟩
    rw [← h]
    exact hde a

/-- Two emitted messages are equal exactly when their inputs parsed to the
same AST: distinct ASTs never collide on the output, and distinct input
encodings of one AST leave no trace in the output. -/
theorem CanonicalDiode.filter_eq_iff {A B : Type} {d : CanonicalDiode A B}
    (hde : DecEnc d.canon) {r₁ r₂ o₁ o₂ : B}
    (h₁ : d.filter r₁ = some o₁) (h₂ : d.filter r₂ = some o₂) :
    o₁ = o₂ ↔ d.parse r₁ = d.parse r₂ := by
  have s₁ := CanonicalDiode.filter_sound hde h₁
  have s₂ := CanonicalDiode.filter_sound hde h₂
  cases s₁ with
  | intro a₁ s₁ =>
    cases s₂ with
    | intro a₂ s₂ =>
      rw [s₁.1, s₂.1]
      constructor
      · intro ho
        have he : d.canon.enc a₁ = d.canon.enc a₂ := by
          rw [s₁.2.2, s₂.2.2]
          exact ho
        rw [enc_injective_of_decEnc hde he]
      · intro ha
        injection ha with ha
        rw [← s₁.2.2, ← s₂.2.2, ha]

/-- If the upstream parser accepts canonical encodings, filtering an emitted
message reproduces it. -/
theorem CanonicalDiode.filter_idempotent {A B : Type} {d : CanonicalDiode A B}
    (hagree : ∀ a : A, d.parse (d.canon.enc a) = some a) {raw out : B}
    (h : d.filter raw = some out) : d.filter out = some out := by
  dsimp only [CanonicalDiode.filter] at h
  dsimp only [CanonicalDiode.filter]
  cases hp : d.parse raw with
  | none =>
    rw [hp] at h
    nomatch h
  | some a =>
    rw [hp, Option.map_some] at h
    injection h with h
    rw [← h, hagree a]
    rfl

/-- Filter every message of a stream, failing if any message fails. -/
@[expose] def CanonicalDiode.filterAll {A B : Type} (d : CanonicalDiode A B)
    (pkts : List B) : Option (List B) :=
  List.foldr
    (fun raw acc => (d.filter raw).bind (fun out => acc.map (fun outs => out :: outs)))
    (some []) pkts

theorem CanonicalDiode.filterAll_cons {A B : Type} (d : CanonicalDiode A B)
    (raw : B) (rest : List B) :
    d.filterAll (raw :: rest) =
      (d.filter raw).bind
        (fun out => (d.filterAll rest).map (fun outs => out :: outs)) :=
  rfl

private theorem transcodeStream_cons_unit {A B : Type}
    (d : CanonicalDiode A B) (raw : B) (rest : List B) :
    MediaBits.transcodeStream d.transcoder () () (raw :: rest) =
      (MediaBits.transcodeOne d.transcoder () () raw).bind (fun r =>
        (MediaBits.transcodeStream d.transcoder () () rest).map
          (fun q => ((), (), r.2.2 :: q.2.2))) := by
  cases h2 : MediaBits.transcodeStream d.transcoder () () rest with
  | none =>
    cases h1 : MediaBits.transcodeOne d.transcoder () () raw with
    | none =>
      dsimp only [MediaBits.transcodeStream, List.foldr] at h2
      dsimp only [MediaBits.transcodeStream, List.foldr]
      rw [h1]
      rfl
    | some r =>
      cases r with
      | mk i r' =>
        cases r' with
        | mk o out =>
          cases i
          cases o
          dsimp only [MediaBits.transcodeStream, List.foldr] at h2
          dsimp only [MediaBits.transcodeStream, List.foldr]
          rw [h1]
          dsimp only
          rw [h2]
          rfl
  | some q =>
    cases h1 : MediaBits.transcodeOne d.transcoder () () raw with
    | none =>
      dsimp only [MediaBits.transcodeStream, List.foldr] at h2
      dsimp only [MediaBits.transcodeStream, List.foldr]
      rw [h1]
      rfl
    | some r =>
      cases r with
      | mk i r' =>
        cases r' with
        | mk o out =>
          cases i
          cases o
          cases q with
          | mk qi q' =>
            cases q' with
            | mk qo qouts =>
              cases qi
              cases qo
              dsimp only [MediaBits.transcodeStream, List.foldr] at h2
              dsimp only [MediaBits.transcodeStream, List.foldr]
              rw [h1]
              dsimp only
              rw [h2]
              rfl

theorem CanonicalDiode.transcodeStream_eq {A B : Type} (d : CanonicalDiode A B) :
    ∀ pkts : List B,
      MediaBits.transcodeStream d.transcoder () () pkts =
        (d.filterAll pkts).map (fun outs => ((), (), outs))
  | [] => rfl
  | raw :: rest => by
    have ih := CanonicalDiode.transcodeStream_eq d rest
    rw [transcodeStream_cons_unit, CanonicalDiode.transcodeOne_eq,
      CanonicalDiode.filterAll_cons, ih]
    cases d.filter raw with
    | none => rfl
    | some out =>
      rw [Option.map_some, Option.bind_some, Option.bind_some]
      cases d.filterAll rest with
      | none => rfl
      | some outs => rfl

/-- Stream fidelity and canonicality of `filterAll`: position by position, the
canonical decoder sees exactly the ASTs the upstream parser produced, and
every emitted message re-encodes to itself. -/
theorem CanonicalDiode.filterAll_sound {A B : Type} {d : CanonicalDiode A B}
    (hde : DecEnc d.canon) :
    ∀ (pkts outs : List B), d.filterAll pkts = some outs →
      pkts.map d.parse = outs.map d.canon.dec ∧
        outs.map (fun o => (d.canon.dec o).map d.canon.enc) = outs.map some
  | [], outs, h => by
    injection h with h
    rw [← h]
    exact ⟨rfl, rfl⟩
  | raw :: rest, outs, h => by
    rw [CanonicalDiode.filterAll_cons] at h
    cases hf : d.filter raw with
    | none =>
      rw [hf] at h
      nomatch h
    | some out =>
      rw [hf, Option.bind_some] at h
      cases hRest : d.filterAll rest with
      | none =>
        rw [hRest] at h
        nomatch h
      | some outs' =>
        rw [hRest, Option.map_some] at h
        injection h with h
        have ih := CanonicalDiode.filterAll_sound hde rest outs' hRest
        have s := CanonicalDiode.filter_sound hde hf
        cases s with
        | intro a s =>
          rw [← h, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
            ih.1, ih.2, s.1, s.2.1, Option.map_some, s.2.2]
          exact ⟨rfl, rfl⟩

/-- End-to-end stream soundness for the transcoder view of a canonical filter:
every emitted packet parses under the canonical decoder (via
`Anneal.MediaBits.dualContext_transcodeStream_sound`), the packet count is
preserved, decoded ASTs match the upstream parse position by position, and
every emitted packet is canonical. -/
theorem CanonicalDiode.stream_sound {A B : Type} {d : CanonicalDiode A B}
    (hde : DecEnc d.canon) {pkts outs : List B}
    (h : MediaBits.transcodeStream d.transcoder () () pkts = some ((), (), outs)) :
    MediaBits.DownstreamParses d.canon.toIndexed () outs () ∧
      outs.length = pkts.length ∧
      pkts.map d.parse = outs.map d.canon.dec ∧
      outs.map (fun o => (d.canon.dec o).map d.canon.enc) = outs.map some := by
  have hlib := MediaBits.dualContext_transcodeStream_sound
    (t := d.transcoder) (R := fun _ _ => True)
    (Codec.toIndexed_putGet hde) (fun _ _ _ _ _ _ _ _ => True.intro)
    pkts () () () () outs True.intro h
  have hall : d.filterAll pkts = some outs := by
    rw [CanonicalDiode.transcodeStream_eq] at h
    cases hf : d.filterAll pkts with
    | none =>
      rw [hf] at h
      nomatch h
    | some outs' =>
      rw [hf, Option.map_some] at h
      injection h with h
      injection h with _ h
      injection h with _ h
      rw [h]
  have hs := CanonicalDiode.filterAll_sound hde pkts outs hall
  exact ⟨hlib.2.1, hlib.2.2, hs.1, hs.2⟩

end Anneal.CanonicalDiode

end
