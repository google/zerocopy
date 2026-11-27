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
public import Anneal.CanonicalDiode

public section

/-!
# Binary-Frame Canaries for `Anneal.CanonicalDiode`

A self-contained bit-level framing exercises every layer of
`Anneal.CanonicalDiode` on concrete data:

1. **Frame codec (`frameCodec`):** a payload `List Bool` is sent as one
   `[true, b]` pair per payload bit followed by a single `false` terminator.
   `frameCodec` satisfies `PrefixDecEnc`, `PrefixEncDec`, `NonEmptyEnc`, and
   hence `PrefixFree`, all proved for every payload.
2. **Frame streams (`frameStream`):** `listCodec frameCodec` is lawful and
   injective, and its decoder obeys the `bs.length + 1` iteration budget
   (`frameStream_linear`). `canary_iteration_budget_tight` shows the
   two-frame message `raw1` needs exactly three iterations.
3. **Malleable upstream parser (`lenientParse`):** decodes frames greedily and
   silently drops trailing bits that do not form a frame, so `raw1` and
   `raw2 = raw1 ++ [true]` parse to the same AST.
   `canary_lenient_decEnc_not_decInj` shows that pairing this parser with
   `frameStream.enc` satisfies `DecEnc` for every message list but is neither
   injective nor canonical.
4. **Canonical filter (`diode`):** pairs `lenientParse` with `frameStream`.
   `canary_diode_collapses_trailing_bits` shows that both inputs are emitted
   as the canonical `raw1`, which the strict decoder accepts while rejecting
   `raw2`, and instantiates `CanonicalDiode.filter_sound` and
   `CanonicalDiode.filter_idempotent`. `canary_diode_separates_asts`
   instantiates `CanonicalDiode.filter_eq_iff` to conclude that inputs with
   distinct ASTs yield distinct outputs. `canary_diode_stream` runs the
   `Anneal.MediaBits.DualContextTranscoder` view over `[raw1, raw2]` and
   instantiates every conjunct of `CanonicalDiode.stream_sound`.
5. **Necessity of non-empty encodings (`canary_empty_encoding_breaks_lists`):**
   a codec that encodes a value to `[]` cannot yield a `DecEnc` list codec.
-/

namespace Anneal.CanonicalDiode.Canaries

open Anneal.CanonicalDiode

/-! ## Frame codec -/

/-- Each payload bit `b` becomes `[true, b]`; a final `false` ends the frame. -/
@[expose] def frameEnc (bits : List Bool) : List Bool :=
  List.foldr (fun b acc => true :: b :: acc) [false] bits

/-- Frame decoder with an explicit iteration budget. -/
@[expose] def frameDecFuel (fuel : Nat) :
    List Bool → Option (List Bool × List Bool) :=
  Nat.rec (motive := fun _ => List Bool → Option (List Bool × List Bool))
    (fun _ => none)
    (fun _ ih bs =>
      List.casesOn (motive := fun _ => Option (List Bool × List Bool)) bs
        none
        (fun t ts =>
          Bool.casesOn (motive := fun _ => Option (List Bool × List Bool)) t
            (some ([], ts))
            (List.casesOn (motive := fun _ => Option (List Bool × List Bool)) ts
              none
              (fun b rest => (ih rest).map (fun r => (b :: r.1, r.2))))))
    fuel

/-- Frame decoder with budget `bs.length`, enough because every iteration
consumes at least one bit. -/
@[expose] def frameDec (bs : List Bool) : Option (List Bool × List Bool) :=
  frameDecFuel bs.length bs

/-- The frame codec as a prefix codec over bits. -/
@[expose] def frameCodec : PrefixCodec (List Bool) Bool where
  enc := frameEnc
  dec := frameDec

theorem frameEnc_nil : frameEnc [] = [false] :=
  rfl

theorem frameEnc_cons (b : Bool) (bs : List Bool) :
    frameEnc (b :: bs) = true :: b :: frameEnc bs :=
  rfl

theorem frameDecFuel_succ_nil (f : Nat) : frameDecFuel (f + 1) [] = none :=
  rfl

theorem frameDecFuel_succ_false (f : Nat) (ts : List Bool) :
    frameDecFuel (f + 1) (false :: ts) = some ([], ts) :=
  rfl

theorem frameDecFuel_succ_true_nil (f : Nat) :
    frameDecFuel (f + 1) [true] = none :=
  rfl

theorem frameDecFuel_succ_true_cons (f : Nat) (b : Bool) (rest : List Bool) :
    frameDecFuel (f + 1) (true :: b :: rest) =
      (frameDecFuel f rest).map (fun r => (b :: r.1, r.2)) :=
  rfl

theorem length_lt_frameEnc_length :
    ∀ bits : List Bool, bits.length < (frameEnc bits).length
  | [] => Nat.zero_lt_one
  | b :: bs => by
    rw [frameEnc_cons, List.length_cons, List.length_cons, List.length_cons]
    exact Nat.lt_succ_of_lt (Nat.succ_lt_succ (length_lt_frameEnc_length bs))

theorem frameDecFuel_frameEnc :
    ∀ (bits rest : List Bool) (f : Nat),
      bits.length < f → frameDecFuel f (frameEnc bits ++ rest) = some (bits, rest)
  | [], _, 0, h => absurd h (Nat.not_lt_zero 0)
  | [], rest, f + 1, _ => by
    rw [frameEnc_nil, List.cons_append, List.nil_append, frameDecFuel_succ_false]
  | _ :: _, _, 0, h => absurd h (Nat.not_lt_zero _)
  | b :: bs, rest, f + 1, h => by
    rw [frameEnc_cons, List.cons_append, List.cons_append,
      frameDecFuel_succ_true_cons,
      frameDecFuel_frameEnc bs rest f (Nat.lt_of_succ_lt_succ h)]
    rfl

theorem frameEnc_of_frameDecFuel :
    ∀ (f : Nat) (bs bits rest : List Bool),
      frameDecFuel f bs = some (bits, rest) → frameEnc bits ++ rest = bs
  | 0, _, _, _, h => nomatch h
  | f + 1, [], _, _, h => by
    rw [frameDecFuel_succ_nil] at h
    nomatch h
  | f + 1, false :: ts, bits, rest, h => by
    rw [frameDecFuel_succ_false] at h
    injection h with h
    injection h with hb hr
    rw [← hb, ← hr]
    rfl
  | f + 1, [true], _, _, h => by
    rw [frameDecFuel_succ_true_nil] at h
    nomatch h
  | f + 1, true :: b :: ts, bits, rest, h => by
    rw [frameDecFuel_succ_true_cons] at h
    cases hr : frameDecFuel f ts with
    | none =>
      rw [hr] at h
      nomatch h
    | some r =>
      rw [hr, Option.map_some] at h
      injection h with h
      injection h with hb hrest
      cases r with
      | mk bits' rest' =>
        have ih := frameEnc_of_frameDecFuel f ts bits' rest' hr
        rw [← hb, ← hrest, frameEnc_cons, List.cons_append, List.cons_append]
        dsimp only
        rw [ih]

theorem frameCodec_prefixDecEnc : PrefixDecEnc frameCodec := by
  intro bits rest
  have hlen : bits.length < (frameEnc bits ++ rest).length := by
    rw [List.length_append]
    exact Nat.lt_of_lt_of_le (length_lt_frameEnc_length bits)
      (Nat.le_add_right _ _)
  exact frameDecFuel_frameEnc bits rest _ hlen

theorem frameCodec_prefixEncDec : PrefixEncDec frameCodec :=
  fun bs bits rest h => frameEnc_of_frameDecFuel bs.length bs bits rest h

theorem frameCodec_nonEmptyEnc : NonEmptyEnc frameCodec := by
  intro bits
  cases bits with
  | nil =>
    intro h
    nomatch h
  | cons b bs =>
    intro h
    nomatch h

theorem frameCodec_prefixFree : PrefixFree frameCodec :=
  prefixFree_of_prefixDecEnc frameCodec_prefixDecEnc

/-! ## Frame streams -/

/-- Concatenated frames, decoded with the linear iteration budget. -/
@[expose] def frameStream : Codec (List (List Bool)) (List Bool) :=
  listCodec frameCodec

theorem frameStream_decEnc : DecEnc frameStream :=
  listCodec_decEnc frameCodec_prefixDecEnc frameCodec_nonEmptyEnc

theorem frameStream_lawful : Lawful frameStream :=
  listCodec_lawful frameCodec_prefixDecEnc frameCodec_prefixEncDec
    frameCodec_nonEmptyEnc

theorem frameStream_decInj : DecInj frameStream :=
  listCodec_decInj frameCodec_prefixEncDec

theorem frameStream_linear {fuel : Nat} {bs : List Bool}
    {msgs : List (List Bool)} (h : listDecFuel frameCodec fuel bs = some msgs) :
    listDecFuel frameCodec (bs.length + 1) bs = some msgs ∧
      msgs.length ≤ bs.length :=
  listDecFuel_linear frameCodec_prefixDecEnc frameCodec_prefixEncDec
    frameCodec_nonEmptyEnc h

/-! ## Malleable upstream parser and canonical filter -/

/-- Greedy frame decoder that stops at the first position where no frame
parses and drops the remaining bits. -/
@[expose] def lenientFuel (fuel : Nat) : List Bool → List (List Bool) :=
  Nat.rec (motive := fun _ => List Bool → List (List Bool))
    (fun _ => [])
    (fun _ ih bs => (frameCodec.dec bs).elim [] (fun r => r.1 :: ih r.2))
    fuel

/-- Lenient upstream parser: accepts every input. -/
@[expose] def lenientParse (bs : List Bool) : Option (List (List Bool)) :=
  some (lenientFuel (bs.length + 1) bs)

theorem lenientFuel_succ (f : Nat) (bs : List Bool) :
    lenientFuel (f + 1) bs =
      (frameCodec.dec bs).elim [] (fun r => r.1 :: lenientFuel f r.2) :=
  rfl

theorem lenientFuel_listEnc :
    ∀ (msgs : List (List Bool)) (f : Nat),
      msgs.length < f → lenientFuel f (listEnc frameCodec msgs) = msgs
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_lt_zero _)
  | m :: ms, f + 1, h => by
    rw [listEnc_cons, lenientFuel_succ,
      frameCodec_prefixDecEnc m (listEnc frameCodec ms)]
    exact congrArg (List.cons m)
      (lenientFuel_listEnc ms f (Nat.lt_of_succ_lt_succ h))

/-- `lenientParse` recovers every message list from its canonical encoding. -/
theorem lenientParse_frameStream_enc (msgs : List (List Bool)) :
    lenientParse (frameStream.enc msgs) = some msgs :=
  congrArg some (lenientFuel_listEnc msgs _
    (Nat.lt_succ_of_le (length_le_listEnc_length frameCodec_nonEmptyEnc msgs)))

/-- Canonical filter re-emitting the lenient parse through `frameStream`. -/
@[expose] def diode : CanonicalDiode (List (List Bool)) (List Bool) where
  parse := lenientParse
  canon := frameStream

/-- Two frames: payloads `[true]` and `[false, true]`. -/
@[expose] def msgs : List (List Bool) := [[true], [false, true]]

/-- Canonical wire form of `msgs`. -/
@[expose] def raw1 : List Bool := frameStream.enc msgs

/-- `raw1` followed by one trailing bit that does not form a frame. -/
@[expose] def raw2 : List Bool := raw1 ++ [true]

theorem raw1_eq : raw1 = [true, true, false, true, false, true, true, false] :=
  rfl

/-- The two-frame message needs exactly three decoder iterations: two
decode a frame each and the third accepts the exhausted input. -/
theorem canary_iteration_budget_tight :
    listDecFuel frameCodec 2 raw1 = none ∧
      listDecFuel frameCodec 3 raw1 = some msgs ∧
      listDecFuel frameCodec (raw1.length + 1) raw1 = some msgs ∧
      msgs.length ≤ raw1.length := by
  have hlin := frameStream_linear (fuel := 3) (bs := raw1) (msgs := msgs) rfl
  exact ⟨rfl, rfl, hlin.1, hlin.2⟩

/-- Paired with `frameStream.enc`, `lenientParse` satisfies `DecEnc`, but it
maps the distinct inputs `raw1` and `raw2` to the same AST, so it is neither
injective nor canonical. -/
theorem canary_lenient_decEnc_not_decInj :
    DecEnc (Codec.mk frameStream.enc lenientParse) ∧
      ¬ DecInj (Codec.mk frameStream.enc lenientParse) ∧
      ¬ EncDec (Codec.mk frameStream.enc lenientParse) := by
  have hne : raw1 ≠ raw2 := by decide
  refine ⟨lenientParse_frameStream_enc, ?_, ?_⟩
  · intro h
    exact hne (h raw1 raw2 msgs rfl rfl)
  · intro h
    exact hne (h raw2 msgs rfl)

/-- The filter maps `raw2`, which differs from `raw1` only by a stray trailing
bit, to the canonical `raw1`. The strict decoder accepts the emitted message
and rejects `raw2`. `CanonicalDiode.filter_sound` shows that the emitted
message decodes to the AST of `raw2`, and `CanonicalDiode.filter_idempotent`
shows that filtering the emitted message reproduces it. -/
theorem canary_diode_collapses_trailing_bits :
    raw1 ≠ raw2 ∧
      diode.filter raw2 = some raw1 ∧
      frameStream.dec raw1 = some msgs ∧
      frameStream.dec raw2 = none ∧
      (∃ a, diode.parse raw2 = some a ∧ diode.canon.dec raw1 = some a ∧
        diode.canon.enc a = raw1) ∧
      diode.filter raw1 = some raw1 := by
  have hne : raw1 ≠ raw2 := by decide
  have h2 : diode.filter raw2 = some raw1 := rfl
  exact ⟨hne, h2, rfl, rfl,
    CanonicalDiode.filter_sound frameStream_decEnc h2,
    CanonicalDiode.filter_idempotent lenientParse_frameStream_enc h2⟩

/-- Canonical wire form of a single frame with payload `[false]`. -/
@[expose] def raw3 : List Bool := frameStream.enc [[false]]

/-- `raw1` and `raw3` parse to distinct ASTs, so `CanonicalDiode.filter_eq_iff`
forces their filtered outputs apart. -/
theorem canary_diode_separates_asts :
    diode.filter raw3 = some raw3 ∧
      diode.parse raw1 ≠ diode.parse raw3 ∧
      raw1 ≠ raw3 := by
  have h1 : diode.filter raw1 = some raw1 := rfl
  have h3 : diode.filter raw3 = some raw3 := rfl
  have hparse : diode.parse raw1 ≠ diode.parse raw3 := by decide
  refine ⟨h3, hparse, ?_⟩
  intro heq
  exact hparse ((CanonicalDiode.filter_eq_iff frameStream_decEnc h1 h3).mp heq)

/-- The dual-context transcoder view of the filter maps the stream
`[raw1, raw2]` to `[raw1, raw1]`, and `CanonicalDiode.stream_sound` yields
downstream parseability, count preservation, positionwise AST fidelity, and
canonicality for it. -/
theorem canary_diode_stream :
    MediaBits.transcodeStream diode.transcoder () () [raw1, raw2] =
        some ((), (), [raw1, raw1]) ∧
      MediaBits.DownstreamParses diode.canon.toIndexed () [raw1, raw1] () ∧
      [raw1, raw1].length = [raw1, raw2].length ∧
      [raw1, raw2].map diode.parse = [raw1, raw1].map diode.canon.dec ∧
      [raw1, raw1].map (fun o => (diode.canon.dec o).map diode.canon.enc) =
        [raw1, raw1].map some := by
  have h : MediaBits.transcodeStream diode.transcoder () () [raw1, raw2] =
      some ((), (), [raw1, raw1]) := rfl
  have hs := CanonicalDiode.stream_sound frameStream_decEnc h
  exact ⟨h, hs⟩

/-! ## Necessity of non-empty encodings -/

/-- A prefix codec that encodes its only value to `[]`. -/
@[expose] def emptyCodec : PrefixCodec Unit Bool where
  enc _ := []
  dec bs := some ((), bs)

/-- `emptyCodec` satisfies both prefix laws, yet its list codec fails
`DecEnc`. -/
theorem canary_empty_encoding_breaks_lists :
    PrefixDecEnc emptyCodec ∧ PrefixEncDec emptyCodec ∧
      ¬ DecEnc (listCodec emptyCodec) := by
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · intro bs a rest h
    injection h with h
    injection h with _ hr
    rw [← hr]
    rfl
  · intro h
    exact nonEmptyEnc_of_listCodec_decEnc h () rfl

end Anneal.CanonicalDiode.Canaries

end
