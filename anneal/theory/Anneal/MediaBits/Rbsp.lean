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
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic

public section

/-!
# Strict `0x000003` RBSP Emulation-Prevention Bijection & Expansion Bounds

Formalizes the byte-stuffing layer between Raw Byte Sequence Payloads (RBSP)
and Encapsulated Byte Sequence Payloads (EBSP) per ITU-T Rec. H.264 §§7.3.1
and 7.4.1 (`0x00 0x00 0x03` emulation-prevention three-byte):

1. **3-State Escape & 4-State Strict Unescape DFA (`0` `._unsafe_rec`, `0`
   `noncomputable`):**
   - `ZeroRun` (`.z0`, `.z1`, `.z2`) tracks consecutive `0x00` bytes.
   - `rbspEscapeFrom` / `rbspEscape` inserts `0x03` before any byte `b ≤ 3`
     immediately following `0x00 0x00`, resetting the zero-run state to `.z0`
     before emitting `b`. At end of input, it appends a final `0x03` when the
     payload ends in `0x00 0x00`. H.264 §7.4.1 appends a final `0x03` when
     the last RBSP byte is `0x00`, which in a well-formed RBSP occurs only
     after a trailing `cabac_zero_word` (`0x00 0x00`); `rbsp_stop_one_bit`
     rules out a lone trailing `0x00`. Over arbitrary byte lists, a lone
     trailing `0x00` is left unescaped, which keeps the bijection total.
   - `UnescState` (`.run z` | `.expectEscaped`) and
     `rbspUnescapeStrictFrom` / `rbspUnescapeStrict` reject unescaped
     `0x00 0x00 {0,1,2}` and non-canonical `0x00 0x00 0x03 b` with `b ≥ 4`.
     At end of input, they accept a trailing `0x00 0x00 0x03` as an escaped
     `cabac_zero_word`, stripping it to `0x00 0x00` (the §7.3.1 `nal_unit`
     loop discards an `emulation_prevention_three_byte` in final position),
     and reject a trailing unescaped `0x00 0x00`, which `rbspEscape` never
     emits.
2. **Exact Non-Malleable Bijection (`[]` zero axioms):**
   - `rbspUnescapeStrict_escape` (Total `PutGet`):
     `rbspUnescapeStrict (rbspEscape p) = some p`.
   - `rbspEscape_of_unescapeStrict_some` (Strict Non-Malleable `GetPut`):
     `rbspUnescapeStrict e = some p → rbspEscape p = e`.
   - `rbspEscape_injective`: injectivity of `rbspEscape`.
   - `rbspUnescapeStrict_injective`: injectivity of `rbspUnescapeStrict` on
     valid EBSPs.
3. **Tight Length Bounds (`|p| ≤ |escape(p)| ≤ ⌊3|p|/2⌋`):**
   - `rbspEscape_len_ge` (`[]` zero axioms): `p.length ≤ (rbspEscape p).length`.
   - `rbspEscape_potential` & `rbspEscape_two_mul_len_le` (`[]` zero axioms):
     potential invariant `2 * |escape(z, p)| ≤ 3 * |p| + w(z)` (the final
     `0x03` emitted from `.z2` is paid for by `w(.z2) = 2`) yielding
     `2 * (rbspEscape p).length ≤ 3 * p.length`.
   - `rbspEscape_len_le_div2` (`[propext]` only):
     `(rbspEscape p).length ≤ Nat.div (3 * p.length) 2`.
   - `rbspUnescapeStrict_len_le` (`[]` zero axioms):
     `rbspUnescapeStrict e = some p → p.length ≤ e.length`.
4. **Lenient Unescaper Malleability Counterexample (`[]` zero axioms):**
   - `rbspUnescapeLenient` strips `0x03` after `0x00 0x00` without verifying
     that the following byte is `≤ 3`, violating strict `GetPut` on
     `[0, 0, 3, 4]` (`rbspUnescapeLenient_breaks_getPut`).

All definitions use `List.foldr` (`0` `._unsafe_rec`, `0` `noncomputable`, `0`
`omega`, `0` `decide`) and every declaration compiles using at most `[propext]`
(`0` `Classical.choice`, `0` `Quot.sound`).
-/

namespace Anneal.MediaBits

/-! ## Part I: 3-State Escape & 4-State Strict Unescape DFAs -/

/-- Number of consecutive `0x00` bytes seen immediately before the next input
byte, capped at `2`. -/
inductive ZeroRun where
  | z0
  | z1
  | z2

/-- Numeric potential weight of a `ZeroRun` state (`0`, `1`, or `2`). -/
@[expose] def zeroRunWeight : ZeroRun → Nat
  | .z0 => 0
  | .z1 => 1
  | .z2 => 2

/-- Stateful RBSP-to-EBSP byte-stuffing encoder starting from zero-run `z`,
implemented via CPS `List.foldr` (`0` `._unsafe_rec`). Inserts `0x03` before
any byte `b ≤ 3` that follows `0x00 0x00`, and appends a final `0x03` when the
input ends in zero-run state `.z2` (H.264 §7.4.1 `cabac_zero_word` rule). -/
@[expose] def rbspEscapeFrom (z : ZeroRun) (xs : List Nat) : List Nat :=
  List.foldr
    (fun b ih curZ =>
      match curZ with
      | .z0 => b :: ih (if Nat.beq b 0 then .z1 else .z0)
      | .z1 => b :: ih (if Nat.beq b 0 then .z2 else .z0)
      | .z2 =>
        match Nat.ble b 3 with
        | true => 3 :: b :: ih (if Nat.beq b 0 then .z1 else .z0)
        | false => b :: ih .z0)
    (fun curZ =>
      match curZ with
      | .z0 => []
      | .z1 => []
      | .z2 => [3])
    xs z

/-- Total RBSP-to-EBSP emulation-prevention encoder (`z = .z0`). -/
@[expose] def rbspEscape (xs : List Nat) : List Nat :=
  rbspEscapeFrom .z0 xs

/-- 4-state strict EBSP-to-RBSP decoder state: `.run z` expects a normal byte
after `z` consecutive zeros; `.expectEscaped` just consumed `0x03` after
`0x00 0x00` and requires the next byte to exist and satisfy `b ≤ 3`. -/
inductive UnescState where
  | run (z : ZeroRun)
  | expectEscaped

/-- Stateful strict EBSP-to-RBSP decoder starting from `st`, implemented via
CPS `List.foldr` (`0` `._unsafe_rec`). Rejects unescaped `0x00 0x00 {0,1,2}`,
non-canonical `0x00 0x00 0x03 b` (`b ≥ 4`), and a trailing unescaped
`0x00 0x00`; accepts a trailing `0x00 0x00 0x03` as an escaped
`cabac_zero_word` (H.264 §§7.3.1, 7.4.1). -/
@[expose] def rbspUnescapeStrictFrom (st : UnescState) (es : List Nat) :
    Option (List Nat) :=
  List.foldr
    (fun e ih curSt =>
      match curSt with
      | .run .z0 =>
        match ih (.run (if Nat.beq e 0 then .z1 else .z0)) with
        | some ps => some (e :: ps)
        | none => none
      | .run .z1 =>
        match ih (.run (if Nat.beq e 0 then .z2 else .z0)) with
        | some ps => some (e :: ps)
        | none => none
      | .run .z2 =>
        match Nat.ble e 2 with
        | true => none
        | false =>
          match Nat.beq e 3 with
          | true => ih .expectEscaped
          | false =>
            match ih (.run .z0) with
            | some ps => some (e :: ps)
            | none => none
      | .expectEscaped =>
        match Nat.ble e 3 with
        | true =>
          match ih (.run (if Nat.beq e 0 then .z1 else .z0)) with
          | some ps => some (e :: ps)
          | none => none
        | false => none)
    (fun curSt =>
      match curSt with
      | .run .z0 => some []
      | .run .z1 => some []
      | .run .z2 => none
      | .expectEscaped => some [])
    es st

/-- Strict non-malleable EBSP-to-RBSP decoder (`st = .run .z0`). -/
@[expose] def rbspUnescapeStrict (es : List Nat) : Option (List Nat) :=
  rbspUnescapeStrictFrom (.run .z0) es

/-! ## Part II: Exact Non-Malleable Bijection (`PutGet` & `GetPut`) -/

private theorem natBle2_false_of_ble3_false {b : Nat}
    (h : Nat.ble b 3 = false) : Nat.ble b 2 = false := by
  cases b with
  | zero => exact Bool.noConfusion h
  | succ b1 =>
    cases b1 with
    | zero => exact Bool.noConfusion h
    | succ b2 =>
      cases b2 with
      | zero => exact Bool.noConfusion h
      | succ _ => rfl

private theorem natBeq3_false_of_ble3_false {b : Nat}
    (h : Nat.ble b 3 = false) : Nat.beq b 3 = false := by
  cases b with
  | zero => exact Bool.noConfusion h
  | succ b1 =>
    cases b1 with
    | zero => exact Bool.noConfusion h
    | succ b2 =>
      cases b2 with
      | zero => exact Bool.noConfusion h
      | succ b3 =>
        cases b3 with
        | zero => exact Bool.noConfusion h
        | succ _ => rfl

private theorem natBle3_false_of_ble2_false_beq3_false {b : Nat}
    (h2 : Nat.ble b 2 = false) (h3 : Nat.beq b 3 = false) :
    Nat.ble b 3 = false := by
  cases b with
  | zero => exact Bool.noConfusion h2
  | succ b1 =>
    cases b1 with
    | zero => exact Bool.noConfusion h2
    | succ b2 =>
      cases b2 with
      | zero => exact Bool.noConfusion h2
      | succ b3 =>
        cases b3 with
        | zero => exact Bool.noConfusion h3
        | succ _ => rfl

private theorem natEq3_of_beq3_true {b : Nat}
    (h : Nat.beq b 3 = true) : b = 3 := by
  cases b with
  | zero => exact Bool.noConfusion h
  | succ b1 =>
    cases b1 with
    | zero => exact Bool.noConfusion h
    | succ b2 =>
      cases b2 with
      | zero => exact Bool.noConfusion h
      | succ b3 =>
        cases b3 with
        | zero => rfl
        | succ _ => exact Bool.noConfusion h

private theorem rbspEscapeFrom_cons_z0 (b : Nat) (bs : List Nat) :
    rbspEscapeFrom .z0 (b :: bs) =
      b :: rbspEscapeFrom (if Nat.beq b 0 then .z1 else .z0) bs :=
  rfl

private theorem rbspEscapeFrom_cons_z1 (b : Nat) (bs : List Nat) :
    rbspEscapeFrom .z1 (b :: bs) =
      b :: rbspEscapeFrom (if Nat.beq b 0 then .z2 else .z0) bs :=
  rfl

private theorem rbspEscapeFrom_cons_z2 (b : Nat) (bs : List Nat) :
    rbspEscapeFrom .z2 (b :: bs) =
      match Nat.ble b 3 with
      | true => 3 :: b :: rbspEscapeFrom (if Nat.beq b 0 then .z1 else .z0) bs
      | false => b :: rbspEscapeFrom .z0 bs :=
  rfl

private theorem rbspUnescapeStrictFrom_cons_z0 (e : Nat) (es : List Nat) :
    rbspUnescapeStrictFrom (.run .z0) (e :: es) =
      match rbspUnescapeStrictFrom
          (.run (if Nat.beq e 0 then .z1 else .z0)) es with
      | some ps => some (e :: ps)
      | none => none :=
  rfl

private theorem rbspUnescapeStrictFrom_cons_z1 (e : Nat) (es : List Nat) :
    rbspUnescapeStrictFrom (.run .z1) (e :: es) =
      match rbspUnescapeStrictFrom
          (.run (if Nat.beq e 0 then .z2 else .z0)) es with
      | some ps => some (e :: ps)
      | none => none :=
  rfl

private theorem rbspUnescapeStrictFrom_cons_z2 (e : Nat) (es : List Nat) :
    rbspUnescapeStrictFrom (.run .z2) (e :: es) =
      match Nat.ble e 2 with
      | true => none
      | false =>
        match Nat.beq e 3 with
        | true => rbspUnescapeStrictFrom .expectEscaped es
        | false =>
          match rbspUnescapeStrictFrom (.run .z0) es with
          | some ps => some (e :: ps)
          | none => none :=
  rfl

private theorem rbspUnescapeStrictFrom_cons_expect (e : Nat) (es : List Nat) :
    rbspUnescapeStrictFrom .expectEscaped (e :: es) =
      match Nat.ble e 3 with
      | true =>
        match rbspUnescapeStrictFrom
            (.run (if Nat.beq e 0 then .z1 else .z0)) es with
        | some ps => some (e :: ps)
        | none => none
      | false => none :=
  rfl

/-- Generalized stateful `PutGet` (`[]` zero axioms): decoding the output of
`rbspEscapeFrom z p` from `.run z` recovers `some p`. -/
theorem rbspUnescapeStrictFrom_escapeFrom :
    ∀ (p : List Nat) (z : ZeroRun),
      rbspUnescapeStrictFrom (.run z) (rbspEscapeFrom z p) = some p
  | [], z => by
    cases z <;> rfl
  | b :: bs, .z0 => by
    rw [rbspEscapeFrom_cons_z0, rbspUnescapeStrictFrom_cons_z0,
      rbspUnescapeStrictFrom_escapeFrom bs (if Nat.beq b 0 then .z1 else .z0)]
  | b :: bs, .z1 => by
    rw [rbspEscapeFrom_cons_z1, rbspUnescapeStrictFrom_cons_z1,
      rbspUnescapeStrictFrom_escapeFrom bs (if Nat.beq b 0 then .z2 else .z0)]
  | b :: bs, .z2 => by
    rw [rbspEscapeFrom_cons_z2]
    cases hLe3 : Nat.ble b 3 with
    | true =>
      dsimp only
      rw [rbspUnescapeStrictFrom_cons_z2]
      dsimp only [Nat.ble, Nat.beq]
      rw [rbspUnescapeStrictFrom_cons_expect, hLe3]
      dsimp only
      rw [rbspUnescapeStrictFrom_escapeFrom bs
        (if Nat.beq b 0 then .z1 else .z0)]
    | false =>
      have hLe2 : Nat.ble b 2 = false := natBle2_false_of_ble3_false hLe3
      have hEq3 : Nat.beq b 3 = false := natBeq3_false_of_ble3_false hLe3
      dsimp only
      rw [rbspUnescapeStrictFrom_cons_z2, hLe2, hEq3]
      dsimp only
      rw [rbspUnescapeStrictFrom_escapeFrom bs .z0]

/-- Total `PutGet` (`[]` zero axioms): `rbspUnescapeStrict (rbspEscape p) =
some p` for every byte sequence `p`. -/
theorem rbspUnescapeStrict_escape (p : List Nat) :
    rbspUnescapeStrict (rbspEscape p) = some p :=
  rbspUnescapeStrictFrom_escapeFrom p .z0

/-- Generalized stateful `GetPut` (`[]` zero axioms): every EBSP accepted by
`rbspUnescapeStrictFrom st e = some p` is canonically produced by
`rbspEscapeFrom`. -/
theorem rbspEscapeFrom_of_unescapeStrictFrom_some :
    ∀ (e : List Nat) (st : UnescState) (p : List Nat),
      rbspUnescapeStrictFrom st e = some p →
      match st with
      | .run z => rbspEscapeFrom z p = e
      | .expectEscaped => rbspEscapeFrom .z2 p = 3 :: e
  | [], .run .z0, p, h => by
    dsimp only [rbspUnescapeStrictFrom, List.foldr] at h
    injection h with hEq
    rw [← hEq]
    rfl
  | [], .run .z1, p, h => by
    dsimp only [rbspUnescapeStrictFrom, List.foldr] at h
    injection h with hEq
    rw [← hEq]
    rfl
  | [], .run .z2, _, h => by
    dsimp only [rbspUnescapeStrictFrom, List.foldr] at h
    nomatch h
  | [], .expectEscaped, p, h => by
    dsimp only [rbspUnescapeStrictFrom, List.foldr] at h
    injection h with hEq
    rw [← hEq]
    rfl
  | b :: es, .run .z0, p, h => by
    rw [rbspUnescapeStrictFrom_cons_z0] at h
    cases hRec :
        rbspUnescapeStrictFrom (.run (if Nat.beq b 0 then .z1 else .z0)) es with
    | none =>
      rw [hRec] at h
      nomatch h
    | some ps =>
      rw [hRec] at h
      injection h with hEq
      dsimp only
      rw [← hEq, rbspEscapeFrom_cons_z0]
      have ih :=
        rbspEscapeFrom_of_unescapeStrictFrom_some es
          (.run (if Nat.beq b 0 then .z1 else .z0)) ps hRec
      dsimp only at ih
      rw [ih]
  | b :: es, .run .z1, p, h => by
    rw [rbspUnescapeStrictFrom_cons_z1] at h
    cases hRec :
        rbspUnescapeStrictFrom (.run (if Nat.beq b 0 then .z2 else .z0)) es with
    | none =>
      rw [hRec] at h
      nomatch h
    | some ps =>
      rw [hRec] at h
      injection h with hEq
      dsimp only
      rw [← hEq, rbspEscapeFrom_cons_z1]
      have ih :=
        rbspEscapeFrom_of_unescapeStrictFrom_some es
          (.run (if Nat.beq b 0 then .z2 else .z0)) ps hRec
      dsimp only at ih
      rw [ih]
  | b :: es, .run .z2, p, h => by
    rw [rbspUnescapeStrictFrom_cons_z2] at h
    cases hLe2 : Nat.ble b 2 with
    | true =>
      rw [hLe2] at h
      nomatch h
    | false =>
      rw [hLe2] at h
      dsimp only at h
      cases hEq3 : Nat.beq b 3 with
      | true =>
        rw [hEq3] at h
        dsimp only at h
        have hb3 : b = 3 := natEq3_of_beq3_true hEq3
        have ih :=
          rbspEscapeFrom_of_unescapeStrictFrom_some es .expectEscaped p h
        dsimp only at ih
        dsimp only
        rw [hb3]
        exact ih
      | false =>
        rw [hEq3] at h
        dsimp only at h
        cases hRec : rbspUnescapeStrictFrom (.run .z0) es with
        | none =>
          rw [hRec] at h
          nomatch h
        | some ps =>
          rw [hRec] at h
          injection h with hEq
          dsimp only
          rw [← hEq, rbspEscapeFrom_cons_z2]
          have hLe3 : Nat.ble b 3 = false :=
            natBle3_false_of_ble2_false_beq3_false hLe2 hEq3
          rw [hLe3]
          dsimp only
          have ih :=
            rbspEscapeFrom_of_unescapeStrictFrom_some es (.run .z0) ps hRec
          dsimp only at ih
          rw [ih]
  | b :: es, .expectEscaped, p, h => by
    rw [rbspUnescapeStrictFrom_cons_expect] at h
    cases hLe3 : Nat.ble b 3 with
    | false =>
      rw [hLe3] at h
      nomatch h
    | true =>
      rw [hLe3] at h
      dsimp only at h
      cases hRec :
          rbspUnescapeStrictFrom
            (.run (if Nat.beq b 0 then .z1 else .z0)) es with
      | none =>
        rw [hRec] at h
        nomatch h
      | some ps =>
        rw [hRec] at h
        injection h with hEq
        dsimp only
        rw [← hEq, rbspEscapeFrom_cons_z2, hLe3]
        dsimp only
        have ih :=
          rbspEscapeFrom_of_unescapeStrictFrom_some es
            (.run (if Nat.beq b 0 then .z1 else .z0)) ps hRec
        dsimp only at ih
        rw [ih]

/-- Strict non-malleable `GetPut` (`[]` zero axioms): if
`rbspUnescapeStrict e = some p`, then `rbspEscape p = e`. -/
theorem rbspEscape_of_unescapeStrict_some {e p : List Nat}
    (h : rbspUnescapeStrict e = some p) : rbspEscape p = e :=
  rbspEscapeFrom_of_unescapeStrictFrom_some e (.run .z0) p h

/-- Injectivity of `rbspEscape` (`[]` zero axioms). -/
theorem rbspEscape_injective {p₁ p₂ : List Nat}
    (h : rbspEscape p₁ = rbspEscape p₂) : p₁ = p₂ := by
  have h1 := rbspUnescapeStrict_escape p₁
  have h2 := rbspUnescapeStrict_escape p₂
  rw [h, h2] at h1
  injection h1 with hEq
  exact hEq.symm

/-- Injectivity of `rbspUnescapeStrict` on valid EBSPs (`[]` zero axioms). -/
theorem rbspUnescapeStrict_injective {e₁ e₂ p : List Nat}
    (h₁ : rbspUnescapeStrict e₁ = some p)
    (h₂ : rbspUnescapeStrict e₂ = some p) : e₁ = e₂ := by
  rw [← rbspEscape_of_unescapeStrict_some h₁,
    ← rbspEscape_of_unescapeStrict_some h₂]

/-! ## Part III: Tight Length Bounds (`|p| ≤ |escape(p)| ≤ ⌊3|p|/2⌋`) -/

/-- Lower length bound (`[]` zero axioms): emulation-prevention byte stuffing
never shrinks the payload. -/
theorem rbspEscapeFrom_len_ge :
    ∀ (p : List Nat) (z : ZeroRun), p.length ≤ (rbspEscapeFrom z p).length
  | [], _ => Nat.zero_le _
  | b :: bs, .z0 => by
    rw [rbspEscapeFrom_cons_z0]
    exact Nat.succ_le_succ
      (rbspEscapeFrom_len_ge bs (if Nat.beq b 0 then .z1 else .z0))
  | b :: bs, .z1 => by
    rw [rbspEscapeFrom_cons_z1]
    exact Nat.succ_le_succ
      (rbspEscapeFrom_len_ge bs (if Nat.beq b 0 then .z2 else .z0))
  | b :: bs, .z2 => by
    rw [rbspEscapeFrom_cons_z2]
    cases Nat.ble b 3 with
    | true =>
      exact Nat.le_trans
        (Nat.succ_le_succ
          (rbspEscapeFrom_len_ge bs (if Nat.beq b 0 then .z1 else .z0)))
        (Nat.le_succ _)
    | false =>
      exact Nat.succ_le_succ (rbspEscapeFrom_len_ge bs .z0)

/-- Lower length bound for `rbspEscape` (`[]` zero axioms). -/
theorem rbspEscape_len_ge (p : List Nat) :
    p.length ≤ (rbspEscape p).length :=
  rbspEscapeFrom_len_ge p .z0

private theorem two_mul_succ (k : Nat) : 2 * (k + 1) = 2 * k + 2 := by
  rw [Nat.mul_succ]

private theorem three_mul_succ (k : Nat) : 3 * (k + 1) = 3 * k + 3 := by
  rw [Nat.mul_succ]

/-- One potential step: an emitted chunk costing `c` (twice its byte count)
is paid for by one consumed input byte (`3`) plus the weight drop
`w + 3 - w'`. -/
private theorem potential_step {L n w' c w : Nat}
    (ih : 2 * L ≤ 3 * n + w') (h : w' + c ≤ 3 + w) :
    2 * L + c ≤ 3 * (n + 1) + w := by
  rw [three_mul_succ, Nat.add_assoc (3 * n) 3 w]
  apply Nat.le_trans (Nat.add_le_add_right ih c)
  rw [Nat.add_assoc (3 * n) w' c]
  exact Nat.add_le_add_left h (3 * n)

private theorem potential_step1 {L n w' w : Nat}
    (ih : 2 * L ≤ 3 * n + w') (h : w' + 2 ≤ 3 + w) :
    2 * (L + 1) ≤ 3 * (n + 1) + w := by
  rw [two_mul_succ]
  exact potential_step ih h

private theorem potential_step2 {L n w' w : Nat}
    (ih : 2 * L ≤ 3 * n + w') (h : w' + 4 ≤ 3 + w) :
    2 * (L + 1 + 1) ≤ 3 * (n + 1) + w := by
  rw [two_mul_succ, two_mul_succ, Nat.add_assoc (2 * L) 2 2]
  exact potential_step ih h

/-- Potential invariant (`[]` zero axioms) proving tight `⌊3n/2⌋` expansion:
`2 * |rbspEscapeFrom z p| ≤ 3 * |p| + zeroRunWeight z`. The weight
`zeroRunWeight .z2 = 2` pays for the final `0x03` that `rbspEscapeFrom`
appends when the input ends in zero-run state `.z2`. -/
theorem rbspEscape_potential :
    ∀ (p : List Nat) (z : ZeroRun),
      2 * (rbspEscapeFrom z p).length ≤ 3 * p.length + zeroRunWeight z
  | [], .z0 => Nat.le_of_ble_eq_true rfl
  | [], .z1 => Nat.le_of_ble_eq_true rfl
  | [], .z2 => Nat.le_of_ble_eq_true rfl
  | b :: bs, .z0 => by
    rw [rbspEscapeFrom_cons_z0]
    dsimp only [List.length]
    cases Nat.beq b 0 with
    | true =>
      exact potential_step1 (rbspEscape_potential bs .z1)
        (Nat.le_of_ble_eq_true rfl)
    | false =>
      exact potential_step1 (rbspEscape_potential bs .z0)
        (Nat.le_of_ble_eq_true rfl)
  | b :: bs, .z1 => by
    rw [rbspEscapeFrom_cons_z1]
    dsimp only [List.length]
    cases Nat.beq b 0 with
    | true =>
      exact potential_step1 (rbspEscape_potential bs .z2)
        (Nat.le_of_ble_eq_true rfl)
    | false =>
      exact potential_step1 (rbspEscape_potential bs .z0)
        (Nat.le_of_ble_eq_true rfl)
  | b :: bs, .z2 => by
    rw [rbspEscapeFrom_cons_z2]
    cases Nat.ble b 3 with
    | true =>
      dsimp only [List.length]
      cases Nat.beq b 0 with
      | true =>
        exact potential_step2 (rbspEscape_potential bs .z1)
          (Nat.le_of_ble_eq_true rfl)
      | false =>
        exact potential_step2 (rbspEscape_potential bs .z0)
          (Nat.le_of_ble_eq_true rfl)
    | false =>
      dsimp only [List.length]
      exact potential_step1 (rbspEscape_potential bs .z0)
        (Nat.le_of_ble_eq_true rfl)

/-- Tight multiplicative expansion bound (`[]` zero axioms):
`2 * (rbspEscape p).length ≤ 3 * p.length`. -/
theorem rbspEscape_two_mul_len_le (p : List Nat) :
    2 * (rbspEscape p).length ≤ 3 * p.length := by
  have hPot := rbspEscape_potential p .z0
  dsimp only [zeroRunWeight] at hPot
  rw [Nat.add_zero] at hPot
  exact hPot

/-- Tight ceiling-free `⌊3n/2⌋` expansion bound (`[propext]` only):
`(rbspEscape p).length ≤ Nat.div (3 * p.length) 2`. -/
theorem rbspEscape_len_le_div2 (p : List Nat) :
    (rbspEscape p).length ≤ Nat.div (3 * p.length) 2 := by
  have hMul := rbspEscape_two_mul_len_le p
  rw [Nat.mul_comm] at hMul
  exact (Nat.le_div_iff_mul_le (Nat.zero_lt_succ 1)).mpr hMul

/-- Unescaping never increases byte length (`[]` zero axioms). -/
theorem rbspUnescapeStrict_len_le {e p : List Nat}
    (h : rbspUnescapeStrict e = some p) : p.length ≤ e.length := by
  rw [← rbspEscape_of_unescapeStrict_some h]
  exact rbspEscape_len_ge p

/-! ## Part IV: Lenient Unescaper Malleability Counterexample -/

/-- Lenient EBSP-to-RBSP decoder that strips `0x03` after `0x00 0x00` without
checking whether the following byte is `≤ 3` (`0` `._unsafe_rec`). -/
@[expose] def rbspUnescapeLenientFrom (z : ZeroRun) (es : List Nat) :
    List Nat :=
  List.foldr
    (fun e ih curZ =>
      match curZ with
      | .z0 => e :: ih (if Nat.beq e 0 then .z1 else .z0)
      | .z1 => e :: ih (if Nat.beq e 0 then .z2 else .z0)
      | .z2 =>
        match Nat.beq e 3 with
        | true => ih .z0
        | false => e :: ih (if Nat.beq e 0 then .z2 else .z0))
    (fun _ => []) es z

/-- Lenient EBSP-to-RBSP decoder starting at `z = .z0`. -/
@[expose] def rbspUnescapeLenient (es : List Nat) : List Nat :=
  rbspUnescapeLenientFrom .z0 es

/-- Malleability refutation (`[]` zero axioms): on `[0, 0, 3, 4]`, strict
unescaping rejects the non-canonical emulation-prevention byte (`none`), while
lenient unescaping accepts `[0, 0, 4]` and breaks strict `GetPut` (shrinking
byte length from `4` to `3`). -/
theorem rbspUnescapeLenient_breaks_getPut :
    let e := [0, 0, 3, 4]
    rbspUnescapeStrict e = none ∧
    rbspUnescapeLenient e = [0, 0, 4] ∧
    rbspEscape (rbspUnescapeLenient e) = [0, 0, 4] ∧
    rbspEscape (rbspUnescapeLenient e) ≠ e := by
  intro e
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro hEq
  injection hEq with _ h1
  injection h1 with _ h2
  injection h2 with h34 _
  exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj h34)))

end Anneal.MediaBits

end
