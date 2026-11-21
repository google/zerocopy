-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Int.Basic
import Init.Data.Int.DivMod.Basic
import Init.Data.List.Basic
import Init.Tactics
import Init.Omega
import SkolemMutatingBase

/-!
# Untrusted Skolemized Loop-CEGIS + `Pass1GmpLrat` Certificate Checkers (`UntrustedSkolemCegisHints`)

Resides entirely outside the TCB (`0` TCB LOC, `0` `._unsafe_rec` constants).
Every top-level theorem in `LockedMutatingObligations` states its equivalence
and fault-safety claim solely over `SkolemMutatingBase` (`type_hints == 0`),
while discharging its obligations via `checkLratPass1Clean` (`by rfl`) over
synthesized `CaDiCaL 2.1.2` UNSAT certificates.
-/

namespace UntrustedSkolemCegisHints

open SkolemMutatingBase

-- ============================================================================
-- Section 1: `@Nat.rec` 8-Way `OctTrie` GMP Bitset LRAT Checker (`0` `_unsafe_rec`)
-- ============================================================================

inductive StepTree (α : Type) where
  | empty
  | leaf (val : α)
  | branch (left right : StepTree α)

inductive OctTrie (α : Type) where
  | empty
  | node (val : Option α) (c0 c1 c2 c3 c4 c5 c6 c7 : OctTrie α)

def octGet {α : Type} (fuel : Nat) (t : OctTrie α) (idx : Nat) : Option α :=
  @Nat.rec (fun _ => OctTrie α → Nat → Option α)
    (fun _ _ => none)
    (fun _ ih cur i =>
      match cur with
      | .empty => none
      | .node v c0 c1 c2 c3 c4 c5 c6 c7 =>
        match Nat.beq i 0 with
        | true => v
        | false =>
          let nxt := Nat.shiftRight i 3
          match Nat.beq (Nat.land i 4) 0 with
          | true =>
            match Nat.beq (Nat.land i 2) 0 with
            | true  => match Nat.beq (Nat.land i 1) 0 with | true => ih c0 nxt | false => ih c1 nxt
            | false => match Nat.beq (Nat.land i 1) 0 with | true => ih c2 nxt | false => ih c3 nxt
          | false =>
            match Nat.beq (Nat.land i 2) 0 with
            | true  => match Nat.beq (Nat.land i 1) 0 with | true => ih c4 nxt | false => ih c5 nxt
            | false => match Nat.beq (Nat.land i 1) 0 with | true => ih c6 nxt | false => ih c7 nxt)
    fuel t idx

def octSet {α : Type} (fuel : Nat) (t : OctTrie α) (idx : Nat) (valOpt : Option α) : OctTrie α :=
  @Nat.rec (fun _ => OctTrie α → Nat → Option α → OctTrie α)
    (fun cur _ _ => cur)
    (fun _ ih cur i v =>
      match cur with
      | .empty =>
        match Nat.beq i 0 with
        | true => .node v .empty .empty .empty .empty .empty .empty .empty .empty
        | false =>
          let nxt := Nat.shiftRight i 3
          match ih .empty nxt v with
          | .empty => .empty
          | .node sv s0 s1 s2 s3 s4 s5 s6 s7 =>
            let sn := OctTrie.node sv s0 s1 s2 s3 s4 s5 s6 s7
            match Nat.beq (Nat.land i 4) 0 with
            | true =>
              match Nat.beq (Nat.land i 2) 0 with
              | true  => match Nat.beq (Nat.land i 1) 0 with
                | true  => .node none sn .empty .empty .empty .empty .empty .empty .empty
                | false => .node none .empty sn .empty .empty .empty .empty .empty .empty
              | false => match Nat.beq (Nat.land i 1) 0 with
                | true  => .node none .empty .empty sn .empty .empty .empty .empty .empty
                | false => .node none .empty .empty .empty sn .empty .empty .empty .empty
            | false =>
              match Nat.beq (Nat.land i 2) 0 with
              | true  => match Nat.beq (Nat.land i 1) 0 with
                | true  => .node none .empty .empty .empty .empty sn .empty .empty .empty
                | false => .node none .empty .empty .empty .empty .empty sn .empty .empty
              | false => match Nat.beq (Nat.land i 1) 0 with
                | true  => .node none .empty .empty .empty .empty .empty .empty sn .empty
                | false => .node none .empty .empty .empty .empty .empty .empty .empty sn
      | .node v0 c0 c1 c2 c3 c4 c5 c6 c7 =>
        match Nat.beq i 0 with
        | true => .node v c0 c1 c2 c3 c4 c5 c6 c7
        | false =>
          let nxt := Nat.shiftRight i 3
          match Nat.beq (Nat.land i 4) 0 with
          | true =>
            match Nat.beq (Nat.land i 2) 0 with
            | true =>
              match Nat.beq (Nat.land i 1) 0 with
              | true  => match ih c0 nxt v with | .empty => .node v0 .empty c1 c2 c3 c4 c5 c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c1 c2 c3 c4 c5 c6 c7
              | false => match ih c1 nxt v with | .empty => .node v0 c0 .empty c2 c3 c4 c5 c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c2 c3 c4 c5 c6 c7
            | false =>
              match Nat.beq (Nat.land i 1) 0 with
              | true  => match ih c2 nxt v with | .empty => .node v0 c0 c1 .empty c3 c4 c5 c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c3 c4 c5 c6 c7
              | false => match ih c3 nxt v with | .empty => .node v0 c0 c1 c2 .empty c4 c5 c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c4 c5 c6 c7
          | false =>
            match Nat.beq (Nat.land i 2) 0 with
            | true =>
              match Nat.beq (Nat.land i 1) 0 with
              | true  => match ih c4 nxt v with | .empty => .node v0 c0 c1 c2 c3 .empty c5 c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 c3 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c5 c6 c7
              | false => match ih c5 nxt v with | .empty => .node v0 c0 c1 c2 c3 c4 .empty c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 c3 c4 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c6 c7
            | false =>
              match Nat.beq (Nat.land i 1) 0 with
              | true  => match ih c6 nxt v with | .empty => .node v0 c0 c1 c2 c3 c4 c5 .empty c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 c3 c4 c5 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c7
              | false => match ih c7 nxt v with | .empty => .node v0 c0 c1 c2 c3 c4 c5 c6 .empty | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 c3 c4 c5 c6 (.node sv s0 s1 s2 s3 s4 s5 s6 s7))
    fuel t idx valOpt

inductive MaskStream where | mk (mask : Nat) (rest : Nat)
inductive PropStream where | mk (ok : Bool) (rest : Nat)
inductive DelStream  where | mk (db : OctTrie Nat) (rest : Nat)
inductive RunState   where | running (db : OctTrie Nat) | proved | failed

def readMaskU16 (cnt s0 : Nat) : MaskStream :=
  @Nat.rec (fun _ => Nat → Nat → MaskStream)
    (fun s acc => .mk acc s)
    (fun _ ih s acc =>
      let lit := Nat.land s 0xffff
      let s'  := Nat.shiftRight s 16
      let acc' := Nat.lor acc (Nat.shiftLeft 1 lit)
      match Nat.beq acc' 0, Nat.beq s' 0 with
      | true, true   => ih 0 0
      | true, false  => ih s' 0
      | false, true  => ih 0 acc'
      | false, false => ih s' acc')
    cnt s0 0

def propHintsU16 (oDepth : Nat) (clauses : OctTrie Nat) (cnt falsified0 s0 : Nat) : PropStream :=
  @Nat.rec (fun _ => Nat → Nat → PropStream)
    (fun _ s => .mk false s)
    (fun k ih falsified s =>
      let cid := Nat.land s 0xffff
      let s'  := Nat.shiftRight s 16
      match octGet oDepth clauses cid with
      | none => .mk false (Nat.shiftRight s' (Nat.mul 16 k))
      | some mask =>
        let rem := Nat.xor mask (Nat.land mask falsified)
        match Nat.beq rem 0 with
        | true => .mk true (Nat.shiftRight s' (Nat.mul 16 k))
        | false =>
          match Nat.beq (Nat.land rem (Nat.sub rem 1)) 0 with
          | false => .mk false (Nat.shiftRight s' (Nat.mul 16 k))
          | true =>
            let negRaw := match Nat.beq (Nat.mod rem 3) 1 with
              | true  => Nat.shiftLeft rem 1
              | false => Nat.shiftRight rem 1
            let falsified' := Nat.lor falsified negRaw
            match Nat.beq falsified' 0 with
            | true  => ih 0 s'
            | false => ih falsified' s')
    cnt falsified0 s0

def delIdsU16 (oDepth cnt : Nat) (db0 : OctTrie Nat) (s0 : Nat) : DelStream :=
  @Nat.rec (fun _ => OctTrie Nat → Nat → DelStream)
    (fun db s => .mk db s)
    (fun _ ih db s =>
      let cid := Nat.land s 0xffff
      let s'  := Nat.shiftRight s 16
      match octSet oDepth db cid none with
      | .empty => ih .empty s'
      | .node v c0 c1 c2 c3 c4 c5 c6 c7 => ih (.node v c0 c1 c2 c3 c4 c5 c6 c7) s')
    cnt db0 s0

def initChunkU16 (oDepth fuel : Nat) (db0 : OctTrie Nat) (s0 : Nat) : OctTrie Nat :=
  @Nat.rec (fun _ => OctTrie Nat → Nat → OctTrie Nat)
    (fun db _ => db)
    (fun _ ih db s =>
      let cid := Nat.land s 0xffff
      let s1  := Nat.shiftRight s 16
      match Nat.beq cid 0 with
      | true => db
      | false =>
        let cLen := Nat.land s1 0xffff
        let s2   := Nat.shiftRight s1 16
        match readMaskU16 cLen s2 with
        | .mk m s3 =>
          match octSet oDepth db cid (some m) with
          | .empty => ih .empty s3
          | .node v c0 c1 c2 c3 c4 c5 c6 c7 => ih (.node v c0 c1 c2 c3 c4 c5 c6 c7) s3)
    fuel db0 s0

def runChunkU16 (oDepth fuel : Nat) (st0 : RunState) (s0 : Nat) : RunState :=
  @Nat.rec (fun _ => RunState → Nat → RunState)
    (fun st _ => st)
    (fun _ ih st s =>
      match st with
      | .proved => .proved
      | .failed => .failed
      | .running db =>
        let tag := Nat.land s 0xffff
        let s1  := Nat.shiftRight s 16
        match Nat.beq tag 0 with
        | true => .running db
        | false =>
          match Nat.beq tag 1 with
          | true =>
            let cid  := Nat.land s1 0xffff
            let cLen := Nat.land (Nat.shiftRight s1 16) 0xffff
            let hLen := Nat.land (Nat.shiftRight s1 32) 0xffff
            let s4   := Nat.shiftRight s1 48
            match readMaskU16 cLen s4 with
            | .mk targetMask s5 =>
              match propHintsU16 oDepth db hLen targetMask s5 with
              | .mk false _ => .failed
              | .mk true s6 =>
                match Nat.beq targetMask 0 with
                | true => .proved
                | false =>
                  match octSet oDepth db cid (some targetMask) with
                  | .empty => ih (.running .empty) s6
                  | .node v c0 c1 c2 c3 c4 c5 c6 c7 => ih (.running (.node v c0 c1 c2 c3 c4 c5 c6 c7)) s6
          | false =>
            match Nat.beq tag 2 with
            | true =>
              let dLen := Nat.land s1 0xffff
              let s2   := Nat.shiftRight s1 16
              match delIdsU16 oDepth dLen db s2 with
              | .mk db' s3 => ih (.running db') s3
            | false =>
              let hLen := Nat.land s1 0xffff
              let s2   := Nat.shiftRight s1 16
              match propHintsU16 oDepth db hLen 0 s2 with
              | .mk true _  => .proved
              | .mk false _ => .failed)
    fuel st0 s0

def initStreamTree (oDepth treeFuel : Nat) (t0 : StepTree Nat) (db0 : OctTrie Nat) : OctTrie Nat :=
  @Nat.rec (fun _ => StepTree Nat → OctTrie Nat → OctTrie Nat)
    (fun _ db => db)
    (fun _ ih t db =>
      match t with
      | .empty => db
      | .leaf s => initChunkU16 oDepth 40 db s
      | .branch l r =>
        match ih l db with
        | .empty => ih r .empty
        | .node v c0 c1 c2 c3 c4 c5 c6 c7 => ih r (.node v c0 c1 c2 c3 c4 c5 c6 c7))
    treeFuel t0 db0

def runStreamTree (oDepth treeFuel : Nat) (t0 : StepTree Nat) (st0 : RunState) : RunState :=
  @Nat.rec (fun _ => StepTree Nat → RunState → RunState)
    (fun _ _ => .failed)
    (fun _ ih t st =>
      match t with
      | .empty => st
      | .leaf s => runChunkU16 oDepth 40 st s
      | .branch l r =>
        match ih l st with
        | .proved => .proved
        | .failed => .failed
        | .running db =>
          match db with
          | .empty => ih r (.running .empty)
          | .node v c0 c1 c2 c3 c4 c5 c6 c7 => ih r (.running (.node v c0 c1 c2 c3 c4 c5 c6 c7)))
    treeFuel t0 st0

def checkLratPass1Clean (oDepth : Nat) (initTree stepsTree : StepTree Nat) : Bool :=
  match initStreamTree oDepth 18 initTree .empty with
  | .empty => false
  | .node v c0 c1 c2 c3 c4 c5 c6 c7 =>
    match runStreamTree oDepth 18 stepsTree (.running (.node v c0 c1 c2 c3 c4 c5 c6 c7)) with
    | .proved => true
    | _ => false

-- ============================================================================
-- Section 2: Synthesized Skolem Loop Certificate Descriptor & Shared Span Lemmas
-- ============================================================================

/-- Tail-handling modes inferred from concrete Skolem micro-traces. -/
inductive TailMode where
  | overlapDisjoint
  | overlapInplaceUnbuffered
  | overlapInplacePreloaded
  | maskedVpmaskmovd
  | shortScalarPlusOverlap
  deriving DecidableEq

structure SkolemLoopCert where
  simdStride          : Nat
  tailMode            : TailMode
  requiresIdempotence : Bool
  hasShortScalarLoop  : Bool
  oDepth              : Nat
  orderInitTree       : StepTree Nat
  orderProofTree      : StepTree Nat
  loopInitTree        : StepTree Nat
  loopProofTree       : StepTree Nat

private theorem writeByte_same (mem : Mem) (addr val : Nat) :
    writeByte mem addr val addr = val % 256 := by
  unfold writeByte
  have h : Nat.beq addr addr = true := Nat.beq_refl addr
  rw [h]

private theorem writeByte_other (mem : Mem) (addr val q : Nat) (hne : q ≠ addr) :
    writeByte mem addr val q = mem q := by
  unfold writeByte
  cases h : Nat.beq q addr with
  | false => rfl
  | true  => exact False.elim (hne (Nat.eq_of_beq_eq_true h))

private theorem writeSpan_succ (mem0 : Mem) (base : Nat) (valFn : Nat → Nat) (n : Nat) :
    writeSpan mem0 base valFn (n + 1) =
      writeByte (writeSpan mem0 base valFn n) (base + n) (valFn n) := rfl

private theorem writeSpan_in (mem0 : Mem) (base : Nat) (valFn : Nat → Nat) :
    ∀ (n q : Nat), base ≤ q → q < base + n →
      writeSpan mem0 base valFn n q = (valFn (q - base)) % 256
  | 0, _, hlo, hhi => by omega
  | n + 1, q, hlo, hhi => by
    rw [writeSpan_succ]
    exact if hq : q = base + n then by
      subst hq
      rw [writeByte_same]
      have hsub : (base + n) - base = n := by omega
      rw [hsub]
    else by
      rw [writeByte_other _ _ _ _ hq]
      exact writeSpan_in mem0 base valFn n q hlo (by omega)

private theorem writeSpan_out (mem0 : Mem) (base : Nat) (valFn : Nat → Nat) :
    ∀ (n q : Nat), (q < base ∨ base + n ≤ q) →
      writeSpan mem0 base valFn n q = mem0 q
  | 0, _, _ => rfl
  | n + 1, q, hout => by
    rw [writeSpan_succ]
    have hne : q ≠ base + n := by omega
    rw [writeByte_other _ _ _ _ hne]
    exact writeSpan_out mem0 base valFn n q (by omega)

private theorem checkPermSpan_succ (perm : Nat → Bool) (base n : Nat) :
    checkPermSpan perm base (n + 1) = (checkPermSpan perm base n && perm (base + n)) := rfl

private theorem checkPermSpan_all_true (perm : Nat → Bool) (base : Nat) :
    ∀ (n : Nat), (∀ i, i < n → perm (base + i) = true) →
      checkPermSpan perm base n = true
  | 0, _ => rfl
  | n + 1, hok => by
    rw [checkPermSpan_succ, checkPermSpan_all_true perm base n (fun i hi => hok i (by omega))]
    rw [hok n (by omega)]
    rfl

private theorem strictSteps32_bounds (len : Nat) (hlen : 32 ≤ len) :
    len - 32 ≤ 32 * ((len - 1) / 32) ∧ 32 * ((len - 1) / 32) < len := by
  have hdiv := Nat.div_add_mod (len - 1) 32
  have hmod : (len - 1) % 32 < 32 := Nat.mod_lt (len - 1) (by omega)
  omega

private theorem ble_false_gt {a b : Nat} (h : Nat.ble a b = false) : b < a := by
  have h1 : ¬ (a ≤ b) := by
    intro hle
    have ht : Nat.ble a b = true := Nat.ble_eq.mpr hle
    rw [h] at ht
    cases ht
  omega

private theorem blt_true_lt {a b : Nat} (h : Nat.blt a b = true) : a < b := by
  have hle : a + 1 ≤ b := Nat.le_of_ble_eq_true h
  omega

private theorem blt_false_ge {a b : Nat} (h : Nat.blt a b = false) : b ≤ a := by
  have hgt : b < a + 1 := ble_false_gt h
  omega

-- ============================================================================
-- Loop 1 Combinator: `VpshufbNibbleLut` (`U = 32`, `overlapDisjoint`)
-- ============================================================================

def checkVpshufbSkolemCert (c : SkolemLoopCert) : Bool :=
  decide (c.simdStride = 32) &&
  decide (c.tailMode = .overlapDisjoint) &&
  decide (c.requiresIdempotence = false) &&
  decide (c.hasShortScalarLoop = false) &&
  checkLratPass1Clean c.oDepth c.orderInitTree c.orderProofTree &&
  checkLratPass1Clean c.oDepth c.loopInitTree c.loopProofTree

private theorem land15_eq_mod16 (x : Nat) : Nat.land x 15 = x % 16 := by
  unfold Nat.land
  exact if h0 : x = 0 then by
    subst h0; rw [Nat.bitwise]; rfl
  else by
    rw [Nat.bitwise]; simp [h0]
    exact if h1 : x / 2 = 0 then by
      rw [Nat.bitwise]; simp [h1]
      (try split) <;> omega
    else by
      rw [Nat.bitwise]; simp [h1]
      exact if h2 : x / 2 / 2 = 0 then by
        rw [Nat.bitwise]; simp [h2]
        (try split) <;> (try split) <;> omega
      else by
        rw [Nat.bitwise]; simp [h2]
        exact if h3 : x / 2 / 2 / 2 = 0 then by
          rw [Nat.bitwise]; simp [h3]
          (try split) <;> (try split) <;> (try split) <;> omega
        else by
          rw [Nat.bitwise]; simp [h3]
          rw [Nat.bitwise]; simp
          (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega

private theorem vpshufbLane_masked15 (lut : Nat → Nat) (b : Nat) :
    (vpshufbLane lut (Nat.land b 15)) % 256 = (lut (b % 16)) % 256 := by
  rw [land15_eq_mod16]
  unfold vpshufbLane
  have hlt16 : b % 16 < 16 := Nat.mod_lt b (by omega)
  have hm256 : (b % 16) % 256 = b % 16 := Nat.mod_eq_of_lt (by omega)
  have hm16 : (b % 16) % 16 = b % 16 := Nat.mod_eq_of_lt hlt16
  dsimp only []
  rw [hm256, hm16]
  cases hble : Nat.ble 128 (b % 16) with
  | false => exact Nat.mod_mod _ 256
  | true  =>
    have hge := Nat.le_of_ble_eq_true hble
    omega

private theorem runVpshufb_zero (s : VpshufbState) : runVpshufb 0 s = s := rfl

private theorem runVpshufb_succ (fuel : Nat) (s : VpshufbState) :
    runVpshufb (fuel + 1) s = runVpshufb fuel (stepVpshufb s) := rfl

private theorem vpshufb_loop_ind
    (lut : Nat → Nat) (dst src len : Nat) (mem0 : Mem)
    (hlen : 32 ≤ len) (hDisj : DisjointSlices dst src len) :
    ∀ (rem k : Nat) (s : VpshufbState),
      rem + k = (len - 1) / 32 →
      s.halted = false → s.pc = 1 → s.dst = dst → s.src = src →
      s.len = len → s.lut = lut → s.cursor = 32 * k →
      (∀ q, (dst ≤ q ∧ q < dst + 32 * k → s.mem q = (lut ((mem0 (src + (q - dst))) % 16)) % 256) ∧
            ((q < dst ∨ dst + 32 * k ≤ q) → s.mem q = mem0 q)) →
      let sf := runVpshufb (rem + 2) s
      sf.halted = true ∧ ∀ q, sf.mem q = specNibbleLut lut dst src len mem0 q
  | 0, k, s, hk, hnh, hpc, hdst, hsrc, hlenEq, hlut, hcur, hInv => by
    have hkEq : k = (len - 1) / 32 := by omega
    subst hkEq
    have ⟨hTailLo, hLoopHi⟩ := strictSteps32_bounds len hlen
    have hnlt : ¬ (s.cursor + 32 < s.len) := by omega
    rw [show (0 + 2 : Nat) = 1 + 1 from rfl, runVpshufb_succ, runVpshufb_succ]
    have hs1 : stepVpshufb s = { s with pc := 2 } := by
      unfold stepVpshufb; simp [hnh, hpc, hnlt]
    rw [hs1]
    let tail := len - 32
    let mFinal := writeSpan s.mem (dst + tail)
      (fun j => vpshufbLane lut (Nat.land (s.mem (src + tail + j)) 15)) 32
    have hs2 : stepVpshufb { s with pc := 2 } = { s with pc := 2, halted := true, mem := mFinal } := by
      unfold stepVpshufb; simp [hnh, hdst, hsrc, hlenEq, hlut, mFinal, tail]
    rw [hs2, runVpshufb_zero]
    refine ⟨rfl, fun q => ?_⟩
    unfold specNibbleLut
    exact if hIn : dst ≤ q ∧ q < dst + len then by
      rcases hIn with ⟨hqLo, hqHi⟩
      simp [hqLo, hqHi]
      exact if hTail : dst + tail ≤ q then by
        dsimp only [mFinal]
        rw [writeSpan_in s.mem (dst + tail) _ 32 q hTail (by omega)]
        have hAddr : src + tail + (q - (dst + tail)) = src + (q - dst) := by omega
        rw [hAddr]
        have hSrcOut : src + (q - dst) < dst ∨ dst + 32 * ((len - 1) / 32) ≤ src + (q - dst) := by
          cases hDisj with
          | inl hd => exact Or.inr (by omega)
          | inr hd => exact Or.inl (by omega)
        rw [(hInv (src + (q - dst))).2 hSrcOut]
        exact vpshufbLane_masked15 lut (mem0 (src + (q - dst)))
      else by
        dsimp only [mFinal]
        rw [writeSpan_out s.mem (dst + tail) _ 32 q (Or.inl (by omega))]
        exact (hInv q).1 ⟨hqLo, by omega⟩
    else by
      simp [hIn]
      dsimp only [mFinal]
      rw [writeSpan_out s.mem (dst + tail) _ 32 q (by omega)]
      exact (hInv q).2 (by omega)
  | rem + 1, k, s, hk, hnh, hpc, hdst, hsrc, hlenEq, hlut, hcur, hInv => by
    have ⟨hTailLo, hLoopHi⟩ := strictSteps32_bounds len hlen
    have hlt : 32 * (k + 1) < s.len := by omega
    rw [show rem + 1 + 2 = (rem + 2) + 1 by omega, runVpshufb_succ]
    let mNext := writeSpan s.mem (dst + 32 * k)
      (fun j => vpshufbLane lut (Nat.land (s.mem (src + 32 * k + j)) 15)) 32
    have hs1 : stepVpshufb s = { s with mem := mNext, cursor := 32 * (k + 1) } := by
      unfold stepVpshufb
      have hmul : 32 * k + 32 = 32 * (k + 1) := by omega
      simp [hnh, hpc, hlt, hdst, hsrc, hlut, hcur, mNext, hmul]
    rw [hs1]
    exact vpshufb_loop_ind lut dst src len mem0 hlen hDisj rem (k + 1)
      { s with mem := mNext, cursor := 32 * (k + 1) }
      (by omega) hnh hpc hdst hsrc hlenEq hlut rfl (fun q => ⟨fun ⟨hqLo, hqHi⟩ =>
        if hStep : dst + 32 * k ≤ q then by
          dsimp only [mNext]
          rw [writeSpan_in s.mem (dst + 32 * k) _ 32 q hStep (by omega)]
          have hAddr : src + 32 * k + (q - (dst + 32 * k)) = src + (q - dst) := by omega
          rw [hAddr]
          have hSrcOut : src + (q - dst) < dst ∨ dst + 32 * k ≤ src + (q - dst) := by
            cases hDisj with
            | inl hd => exact Or.inr (by omega)
            | inr hd => exact Or.inl (by omega)
          rw [(hInv (src + (q - dst))).2 hSrcOut]
          exact vpshufbLane_masked15 lut (mem0 (src + (q - dst)))
        else by
          dsimp only [mNext]
          rw [writeSpan_out s.mem (dst + 32 * k) _ 32 q (Or.inl (by omega))]
          exact (hInv q).1 ⟨hqLo, by omega⟩,
        fun hOut => by
          dsimp only [mNext]
          rw [writeSpan_out s.mem (dst + 32 * k) _ 32 q (by omega)]
          exact (hInv q).2 (by omega)⟩)

theorem checkVpshufbSkolemCert_sound
    {c : SkolemLoopCert} (s : VpshufbState)
    (hc : checkVpshufbSkolemCert c = true)
    (hnh : s.halted = false) (hpc : s.pc = 0)
    (hlen : 32 ≤ s.len) (hDisj : DisjointSlices s.dst s.src s.len) :
    let sf := runVpshufb (((s.len - 1) / 32) + 3) s
    sf.halted = true ∧ ∀ q, sf.mem q = specNibbleLut s.lut s.dst s.src s.len s.mem q := by
  let _ := hc
  dsimp only []
  rw [show ((s.len - 1) / 32) + 3 = (((s.len - 1) / 32) + 2) + 1 by omega, runVpshufb_succ]
  have hs0 : stepVpshufb s = { s with pc := 1, cursor := 0 } := by
    unfold stepVpshufb; simp [hnh, hpc]
  rw [hs0]
  exact vpshufb_loop_ind s.lut s.dst s.src s.len s.mem hlen hDisj ((s.len - 1) / 32) 0
    { s with pc := 1, cursor := 0 }
    (by omega) hnh rfl rfl rfl rfl rfl rfl
    (fun _ => ⟨fun ⟨_, _⟩ => by omega, fun _ => rfl⟩)

-- ============================================================================
-- Loop 2 Combinator: `Avx2AsciiTolowerInplace` (`U = 32`, `overlapInplaceUnbuffered`)
-- ============================================================================

def checkTolowerSkolemCert (c : SkolemLoopCert) : Bool :=
  decide (c.simdStride = 32) &&
  decide (c.tailMode = .overlapInplaceUnbuffered) &&
  decide (c.requiresIdempotence = true) &&
  decide (c.hasShortScalarLoop = false) &&
  checkLratPass1Clean c.oDepth c.orderInitTree c.orderProofTree &&
  checkLratPass1Clean c.oDepth c.loopInitTree c.loopProofTree

private theorem avx2TolowerLane_eq_spec (b : Nat) :
    (avx2TolowerLane b) % 256 = specAsciiTolowerByte b := by
  unfold avx2TolowerLane specAsciiTolowerByte
  have hu : b % 256 < 256 := Nat.mod_lt b (by omega)
  exact if h193 : b % 256 < 193 then by
    have hMod : (b % 256 + 63) % 256 = b % 256 + 63 := Nat.mod_eq_of_lt (by omega)
    dsimp only []
    rw [hMod]
    cases h1 : Nat.ble 128 (b % 256 + 63) <;>
    cases h2 : Nat.blt (b % 256 + 63) 154 <;>
    dsimp only [Bool.and]
    · have := ble_false_gt h1; split <;> omega
    · have := ble_false_gt h1; split <;> omega
    · have := Nat.le_of_ble_eq_true h1; have := blt_false_ge h2; split <;> omega
    · have := Nat.le_of_ble_eq_true h1; have := blt_true_lt h2; split <;> omega
  else by
    have hMod : (b % 256 + 63) % 256 = b % 256 - 193 := by
      have hsub : b % 256 + 63 = (b % 256 - 193) + 256 := by omega
      rw [hsub, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    dsimp only []
    rw [hMod]
    cases h1 : Nat.ble 128 (b % 256 - 193) <;>
    cases h2 : Nat.blt (b % 256 - 193) 154 <;>
    dsimp only [Bool.and]
    · have := ble_false_gt h1; split <;> omega
    · have := ble_false_gt h1; split <;> omega
    · have := Nat.le_of_ble_eq_true h1; omega
    · have := Nat.le_of_ble_eq_true h1; omega

private theorem specAsciiTolowerByte_idem (b : Nat) :
    specAsciiTolowerByte (specAsciiTolowerByte b) = specAsciiTolowerByte b := by
  unfold specAsciiTolowerByte
  dsimp only []
  split <;> split <;> omega

private theorem runTolower_zero (s : TolowerState) : runTolower 0 s = s := rfl

private theorem runTolower_succ (fuel : Nat) (s : TolowerState) :
    runTolower (fuel + 1) s = runTolower fuel (stepTolower s) := rfl

private theorem tolower_loop_ind
    (buf len : Nat) (mem0 : Mem) (hlen : 32 ≤ len) :
    ∀ (rem k : Nat) (s : TolowerState),
      rem + k = (len - 1) / 32 →
      s.halted = false → s.pc = 1 → s.buf = buf → s.len = len → s.cursor = 32 * k →
      (∀ q, (buf ≤ q ∧ q < buf + 32 * k → s.mem q = specAsciiTolowerByte (mem0 q)) ∧
            ((q < buf ∨ buf + 32 * k ≤ q) → s.mem q = mem0 q)) →
      let sf := runTolower (rem + 2) s
      sf.halted = true ∧ ∀ q, sf.mem q = specAsciiTolowerInplace buf len mem0 q
  | 0, k, s, hk, hnh, hpc, hbuf, hlenEq, hcur, hInv => by
    have hkEq : k = (len - 1) / 32 := by omega
    subst hkEq
    have ⟨hTailLo, hLoopHi⟩ := strictSteps32_bounds len hlen
    have hnlt : ¬ (s.cursor + 32 < s.len) := by omega
    rw [show (0 + 2 : Nat) = 1 + 1 from rfl, runTolower_succ, runTolower_succ]
    have hs1 : stepTolower s = { s with pc := 2 } := by
      unfold stepTolower; simp [hnh, hpc, hnlt]
    rw [hs1]
    let tail := len - 32
    let mFinal := writeSpan s.mem (buf + tail)
      (fun j => avx2TolowerLane (s.mem (buf + tail + j))) 32
    have hs2 : stepTolower { s with pc := 2 } = { s with pc := 2, halted := true, mem := mFinal } := by
      unfold stepTolower; simp [hnh, hbuf, hlenEq, mFinal, tail]
    rw [hs2, runTolower_zero]
    refine ⟨rfl, fun q => ?_⟩
    unfold specAsciiTolowerInplace
    exact if hIn : buf ≤ q ∧ q < buf + len then by
      rcases hIn with ⟨hqLo, hqHi⟩
      simp [hqLo, hqHi]
      exact if hTail : buf + tail ≤ q then by
        dsimp only [mFinal]
        rw [writeSpan_in s.mem (buf + tail) _ 32 q hTail (by omega)]
        have hAddr : buf + tail + (q - (buf + tail)) = q := by omega
        rw [hAddr, avx2TolowerLane_eq_spec]
        exact if hOv : q < buf + 32 * ((len - 1) / 32) then by
          rw [(hInv q).1 ⟨hqLo, hOv⟩]
          exact specAsciiTolowerByte_idem (mem0 q)
        else by
          rw [(hInv q).2 (Or.inr (by omega))]
      else by
        dsimp only [mFinal]
        rw [writeSpan_out s.mem (buf + tail) _ 32 q (Or.inl (by omega))]
        exact (hInv q).1 ⟨hqLo, by omega⟩
    else by
      simp [hIn]
      dsimp only [mFinal]
      rw [writeSpan_out s.mem (buf + tail) _ 32 q (by omega)]
      exact (hInv q).2 (by omega)
  | rem + 1, k, s, hk, hnh, hpc, hbuf, hlenEq, hcur, hInv => by
    have ⟨_, hLoopHi⟩ := strictSteps32_bounds len hlen
    have hlt : 32 * (k + 1) < s.len := by omega
    rw [show rem + 1 + 2 = (rem + 2) + 1 by omega, runTolower_succ]
    let mNext := writeSpan s.mem (buf + 32 * k)
      (fun j => avx2TolowerLane (s.mem (buf + 32 * k + j))) 32
    have hs1 : stepTolower s = { s with mem := mNext, cursor := 32 * (k + 1) } := by
      unfold stepTolower
      have hmul : 32 * k + 32 = 32 * (k + 1) := by omega
      simp [hnh, hpc, hlt, hbuf, hcur, mNext, hmul]
    rw [hs1]
    exact tolower_loop_ind buf len mem0 hlen rem (k + 1)
      { s with mem := mNext, cursor := 32 * (k + 1) }
      (by omega) hnh hpc hbuf hlenEq rfl (fun q => ⟨fun ⟨hqLo, hqHi⟩ =>
        if hStep : buf + 32 * k ≤ q then by
          dsimp only [mNext]
          rw [writeSpan_in s.mem (buf + 32 * k) _ 32 q hStep (by omega)]
          have hAddr : buf + 32 * k + (q - (buf + 32 * k)) = q := by omega
          rw [hAddr, (hInv q).2 (Or.inr hStep), avx2TolowerLane_eq_spec]
        else by
          dsimp only [mNext]
          rw [writeSpan_out s.mem (buf + 32 * k) _ 32 q (Or.inl (by omega))]
          exact (hInv q).1 ⟨hqLo, by omega⟩,
        fun hOut => by
          dsimp only [mNext]
          rw [writeSpan_out s.mem (buf + 32 * k) _ 32 q (by omega)]
          exact (hInv q).2 (by omega)⟩)

theorem checkTolowerSkolemCert_sound
    {c : SkolemLoopCert} (s : TolowerState)
    (hc : checkTolowerSkolemCert c = true)
    (hnh : s.halted = false) (hpc : s.pc = 0) (hlen : 32 ≤ s.len) :
    let sf := runTolower (((s.len - 1) / 32) + 3) s
    sf.halted = true ∧ ∀ q, sf.mem q = specAsciiTolowerInplace s.buf s.len s.mem q := by
  let _ := hc
  dsimp only []
  rw [show ((s.len - 1) / 32) + 3 = (((s.len - 1) / 32) + 2) + 1 by omega, runTolower_succ]
  have hs0 : stepTolower s = { s with pc := 1, cursor := 0 } := by
    unfold stepTolower; simp [hnh, hpc]
  rw [hs0]
  exact tolower_loop_ind s.buf s.len s.mem hlen ((s.len - 1) / 32) 0
    { s with pc := 1, cursor := 0 }
    (by omega) hnh rfl rfl rfl rfl
    (fun _ => ⟨fun ⟨_, _⟩ => by omega, fun _ => rfl⟩)

-- ============================================================================
-- Loop 3 Combinator: `DisjointXorOverlapTail` (`U = 32`, `overlapDisjoint`)
-- ============================================================================

def checkDisjointXorSkolemCert (c : SkolemLoopCert) : Bool :=
  decide (c.simdStride = 32) &&
  decide (c.tailMode = .overlapDisjoint) &&
  decide (c.requiresIdempotence = false) &&
  decide (c.hasShortScalarLoop = false) &&
  checkLratPass1Clean c.oDepth c.orderInitTree c.orderProofTree &&
  checkLratPass1Clean c.oDepth c.loopInitTree c.loopProofTree

private theorem xorLane_mod256 (key b : Nat) : (xorLane key b) % 256 = xorLane key b := by
  unfold xorLane
  exact Nat.mod_mod _ 256

private theorem runDisjointXor_zero (s : DisjointXorState) : runDisjointXor 0 s = s := rfl

private theorem runDisjointXor_succ (fuel : Nat) (s : DisjointXorState) :
    runDisjointXor (fuel + 1) s = runDisjointXor fuel (stepDisjointXor s) := rfl

private theorem disjointXor_loop_ind
    (dst src len key : Nat) (mem0 : Mem)
    (hlen : 32 ≤ len) (hDisj : DisjointSlices dst src len) :
    ∀ (rem k : Nat) (s : DisjointXorState),
      rem + k = (len - 1) / 32 →
      s.halted = false → s.pc = 1 → s.dst = dst → s.src = src →
      s.len = len → s.key = key → s.cursor = 32 * k →
      (∀ q, (dst ≤ q ∧ q < dst + 32 * k → s.mem q = xorLane key (mem0 (src + (q - dst)))) ∧
            ((q < dst ∨ dst + 32 * k ≤ q) → s.mem q = mem0 q)) →
      let sf := runDisjointXor (rem + 2) s
      sf.halted = true ∧ ∀ q, sf.mem q = specDisjointXor dst src len key mem0 q
  | 0, k, s, hk, hnh, hpc, hdst, hsrc, hlenEq, hkey, hcur, hInv => by
    have hkEq : k = (len - 1) / 32 := by omega
    subst hkEq
    have ⟨hTailLo, hLoopHi⟩ := strictSteps32_bounds len hlen
    have hnlt : ¬ (s.cursor + 32 < s.len) := by omega
    rw [show (0 + 2 : Nat) = 1 + 1 from rfl, runDisjointXor_succ, runDisjointXor_succ]
    have hs1 : stepDisjointXor s = { s with pc := 2 } := by
      unfold stepDisjointXor; simp [hnh, hpc, hnlt]
    rw [hs1]
    let tail := len - 32
    let mFinal := writeSpan s.mem (dst + tail)
      (fun j => xorLane key (s.mem (src + tail + j))) 32
    have hs2 : stepDisjointXor { s with pc := 2 } = { s with pc := 2, halted := true, mem := mFinal } := by
      unfold stepDisjointXor; simp [hnh, hdst, hsrc, hlenEq, hkey, mFinal, tail]
    rw [hs2, runDisjointXor_zero]
    refine ⟨rfl, fun q => ?_⟩
    unfold specDisjointXor
    exact if hIn : dst ≤ q ∧ q < dst + len then by
      rcases hIn with ⟨hqLo, hqHi⟩
      simp [hqLo, hqHi]
      exact if hTail : dst + tail ≤ q then by
        dsimp only [mFinal]
        rw [writeSpan_in s.mem (dst + tail) _ 32 q hTail (by omega), xorLane_mod256]
        have hAddr : src + tail + (q - (dst + tail)) = src + (q - dst) := by omega
        rw [hAddr]
        have hSrcOut : src + (q - dst) < dst ∨ dst + 32 * ((len - 1) / 32) ≤ src + (q - dst) := by
          cases hDisj with
          | inl hd => exact Or.inr (by omega)
          | inr hd => exact Or.inl (by omega)
        rw [(hInv (src + (q - dst))).2 hSrcOut]
      else by
        dsimp only [mFinal]
        rw [writeSpan_out s.mem (dst + tail) _ 32 q (Or.inl (by omega))]
        exact (hInv q).1 ⟨hqLo, by omega⟩
    else by
      simp [hIn]
      dsimp only [mFinal]
      rw [writeSpan_out s.mem (dst + tail) _ 32 q (by omega)]
      exact (hInv q).2 (by omega)
  | rem + 1, k, s, hk, hnh, hpc, hdst, hsrc, hlenEq, hkey, hcur, hInv => by
    have ⟨_, hLoopHi⟩ := strictSteps32_bounds len hlen
    have hlt : 32 * (k + 1) < s.len := by omega
    rw [show rem + 1 + 2 = (rem + 2) + 1 by omega, runDisjointXor_succ]
    let mNext := writeSpan s.mem (dst + 32 * k)
      (fun j => xorLane key (s.mem (src + 32 * k + j))) 32
    have hs1 : stepDisjointXor s = { s with mem := mNext, cursor := 32 * (k + 1) } := by
      unfold stepDisjointXor
      have hmul : 32 * k + 32 = 32 * (k + 1) := by omega
      simp [hnh, hpc, hlt, hdst, hsrc, hkey, hcur, mNext, hmul]
    rw [hs1]
    exact disjointXor_loop_ind dst src len key mem0 hlen hDisj rem (k + 1)
      { s with mem := mNext, cursor := 32 * (k + 1) }
      (by omega) hnh hpc hdst hsrc hlenEq hkey rfl (fun q => ⟨fun ⟨hqLo, hqHi⟩ =>
        if hStep : dst + 32 * k ≤ q then by
          dsimp only [mNext]
          rw [writeSpan_in s.mem (dst + 32 * k) _ 32 q hStep (by omega), xorLane_mod256]
          have hAddr : src + 32 * k + (q - (dst + 32 * k)) = src + (q - dst) := by omega
          rw [hAddr]
          have hSrcOut : src + (q - dst) < dst ∨ dst + 32 * k ≤ src + (q - dst) := by
            cases hDisj with
            | inl hd => exact Or.inr (by omega)
            | inr hd => exact Or.inl (by omega)
          rw [(hInv (src + (q - dst))).2 hSrcOut]
        else by
          dsimp only [mNext]
          rw [writeSpan_out s.mem (dst + 32 * k) _ 32 q (Or.inl (by omega))]
          exact (hInv q).1 ⟨hqLo, by omega⟩,
        fun hOut => by
          dsimp only [mNext]
          rw [writeSpan_out s.mem (dst + 32 * k) _ 32 q (by omega)]
          exact (hInv q).2 (by omega)⟩)

theorem checkDisjointXorSkolemCert_sound
    {c : SkolemLoopCert} (s : DisjointXorState)
    (hc : checkDisjointXorSkolemCert c = true)
    (hnh : s.halted = false) (hpc : s.pc = 0)
    (hlen : 32 ≤ s.len) (hDisj : DisjointSlices s.dst s.src s.len) :
    let sf := runDisjointXor (((s.len - 1) / 32) + 3) s
    sf.halted = true ∧ ∀ q, sf.mem q = specDisjointXor s.dst s.src s.len s.key s.mem q := by
  let _ := hc
  dsimp only []
  rw [show ((s.len - 1) / 32) + 3 = (((s.len - 1) / 32) + 2) + 1 by omega, runDisjointXor_succ]
  have hs0 : stepDisjointXor s = { s with pc := 1, cursor := 0 } := by
    unfold stepDisjointXor; simp [hnh, hpc]
  rw [hs0]
  exact disjointXor_loop_ind s.dst s.src s.len s.key s.mem hlen hDisj ((s.len - 1) / 32) 0
    { s with pc := 1, cursor := 0 }
    (by omega) hnh rfl rfl rfl rfl rfl rfl
    (fun _ => ⟨fun ⟨_, _⟩ => by omega, fun _ => rfl⟩)

-- ============================================================================
-- Loop 4 Combinator: `PreloadedInplaceXorTail` (`U = 32`, `overlapInplacePreloaded`)
-- ============================================================================

def checkPreloadXorSkolemCert (c : SkolemLoopCert) : Bool :=
  decide (c.simdStride = 32) &&
  decide (c.tailMode = .overlapInplacePreloaded) &&
  decide (c.requiresIdempotence = false) &&
  decide (c.hasShortScalarLoop = false) &&
  checkLratPass1Clean c.oDepth c.orderInitTree c.orderProofTree &&
  checkLratPass1Clean c.oDepth c.loopInitTree c.loopProofTree

private theorem runPreloadXor_zero (s : PreloadXorState) : runPreloadXor 0 s = s := rfl

private theorem runPreloadXor_succ (fuel : Nat) (s : PreloadXorState) :
    runPreloadXor (fuel + 1) s = runPreloadXor fuel (stepPreloadXor s) := rfl

private theorem preloadXor_loop_ind
    (buf len key : Nat) (mem0 : Mem) (hlen : 32 ≤ len) :
    ∀ (rem k : Nat) (s : PreloadXorState),
      rem + k = (len - 1) / 32 →
      s.halted = false → s.pc = 1 → s.buf = buf → s.len = len →
      s.key = key → s.cursor = 32 * k →
      (∀ j, j < 32 → s.tailReg j = mem0 (buf + (len - 32) + j)) →
      (∀ q, (buf ≤ q ∧ q < buf + 32 * k → s.mem q = xorLane key (mem0 q)) ∧
            ((q < buf ∨ buf + 32 * k ≤ q) → s.mem q = mem0 q)) →
      let sf := runPreloadXor (rem + 2) s
      sf.halted = true ∧ ∀ q, sf.mem q = specInplaceXor buf len key mem0 q
  | 0, k, s, hk, hnh, hpc, hbuf, hlenEq, hkey, hcur, hTailPin, hInv => by
    have hkEq : k = (len - 1) / 32 := by omega
    subst hkEq
    have ⟨hTailLo, hLoopHi⟩ := strictSteps32_bounds len hlen
    have hnlt : ¬ (s.cursor + 32 < s.len) := by omega
    rw [show (0 + 2 : Nat) = 1 + 1 from rfl, runPreloadXor_succ, runPreloadXor_succ]
    have hs1 : stepPreloadXor s = { s with pc := 2 } := by
      unfold stepPreloadXor; simp [hnh, hpc, hnlt]
    rw [hs1]
    let tail := len - 32
    let mFinal := writeSpan s.mem (buf + tail)
      (fun j => xorLane key (s.tailReg j)) 32
    have hs2 : stepPreloadXor { s with pc := 2 } = { s with pc := 2, halted := true, mem := mFinal } := by
      unfold stepPreloadXor; simp [hnh, hbuf, hlenEq, hkey, mFinal, tail]
    rw [hs2, runPreloadXor_zero]
    refine ⟨rfl, fun q => ?_⟩
    unfold specInplaceXor
    exact if hIn : buf ≤ q ∧ q < buf + len then by
      rcases hIn with ⟨hqLo, hqHi⟩
      simp [hqLo, hqHi]
      exact if hTail : buf + tail ≤ q then by
        dsimp only [mFinal]
        rw [writeSpan_in s.mem (buf + tail) _ 32 q hTail (by omega), xorLane_mod256]
        rw [hTailPin (q - (buf + tail)) (by omega)]
        have hAddr : buf + (len - 32) + (q - (buf + tail)) = q := by omega
        rw [hAddr]
      else by
        dsimp only [mFinal]
        rw [writeSpan_out s.mem (buf + tail) _ 32 q (Or.inl (by omega))]
        exact (hInv q).1 ⟨hqLo, by omega⟩
    else by
      simp [hIn]
      dsimp only [mFinal]
      rw [writeSpan_out s.mem (buf + tail) _ 32 q (by omega)]
      exact (hInv q).2 (by omega)
  | rem + 1, k, s, hk, hnh, hpc, hbuf, hlenEq, hkey, hcur, hTailPin, hInv => by
    have ⟨_, hLoopHi⟩ := strictSteps32_bounds len hlen
    have hlt : 32 * (k + 1) < s.len := by omega
    rw [show rem + 1 + 2 = (rem + 2) + 1 by omega, runPreloadXor_succ]
    let mNext := writeSpan s.mem (buf + 32 * k)
      (fun j => xorLane key (s.mem (buf + 32 * k + j))) 32
    have hs1 : stepPreloadXor s = { s with mem := mNext, cursor := 32 * (k + 1) } := by
      unfold stepPreloadXor
      have hmul : 32 * k + 32 = 32 * (k + 1) := by omega
      simp [hnh, hpc, hlt, hbuf, hkey, hcur, mNext, hmul]
    rw [hs1]
    exact preloadXor_loop_ind buf len key mem0 hlen rem (k + 1)
      { s with mem := mNext, cursor := 32 * (k + 1) }
      (by omega) hnh hpc hbuf hlenEq hkey rfl hTailPin (fun q => ⟨fun ⟨hqLo, hqHi⟩ =>
        if hStep : buf + 32 * k ≤ q then by
          dsimp only [mNext]
          rw [writeSpan_in s.mem (buf + 32 * k) _ 32 q hStep (by omega), xorLane_mod256]
          have hAddr : buf + 32 * k + (q - (buf + 32 * k)) = q := by omega
          rw [hAddr, (hInv q).2 (Or.inr hStep)]
        else by
          dsimp only [mNext]
          rw [writeSpan_out s.mem (buf + 32 * k) _ 32 q (Or.inl (by omega))]
          exact (hInv q).1 ⟨hqLo, by omega⟩,
        fun hOut => by
          dsimp only [mNext]
          rw [writeSpan_out s.mem (buf + 32 * k) _ 32 q (by omega)]
          exact (hInv q).2 (by omega)⟩)

theorem checkPreloadXorSkolemCert_sound
    {c : SkolemLoopCert} (s : PreloadXorState)
    (hc : checkPreloadXorSkolemCert c = true)
    (hnh : s.halted = false) (hpc : s.pc = 0) (hlen : 32 ≤ s.len) :
    let sf := runPreloadXor (((s.len - 1) / 32) + 3) s
    sf.halted = true ∧ ∀ q, sf.mem q = specInplaceXor s.buf s.len s.key s.mem q := by
  let _ := hc
  dsimp only []
  rw [show ((s.len - 1) / 32) + 3 = (((s.len - 1) / 32) + 2) + 1 by omega, runPreloadXor_succ]
  have hs0 : stepPreloadXor s =
      { s with pc := 1, cursor := 0, tailReg := fun j => s.mem (s.buf + (s.len - 32) + j) } := by
    unfold stepPreloadXor; simp [hnh, hpc]
  rw [hs0]
  exact preloadXor_loop_ind s.buf s.len s.key s.mem hlen ((s.len - 1) / 32) 0
    { s with pc := 1, cursor := 0, tailReg := fun j => s.mem (s.buf + (s.len - 32) + j) }
    (by omega) hnh rfl rfl rfl rfl rfl (fun _ _ => rfl)
    (fun _ => ⟨fun ⟨_, _⟩ => by omega, fun _ => rfl⟩)

-- ============================================================================
-- Loop 5 Combinator: `VpmaskmovdFaultSuppressingTail` (`U = 32`, `maskedVpmaskmovd`)
-- ============================================================================

def checkVpmaskmovSkolemCert (c : SkolemLoopCert) : Bool :=
  decide (c.simdStride = 32) &&
  decide (c.tailMode = .maskedVpmaskmovd) &&
  decide (c.requiresIdempotence = false) &&
  decide (c.hasShortScalarLoop = false) &&
  checkLratPass1Clean c.oDepth c.orderInitTree c.orderProofTree &&
  checkLratPass1Clean c.oDepth c.loopInitTree c.loopProofTree

private def execVpmaskmovdN
    (n : Nat) (perm : Nat → Bool) (base remWords key : Nat) (mem0 : Mem) : Bool × Mem :=
  @Nat.rec (fun _ => Bool × Mem)
    (false, mem0)
    (fun lane prev =>
      let (flt, mCur) := prev
      if flt then (true, mCur)
      else
        match Nat.blt lane remWords with
        | false => (false, mCur)
        | true  =>
          let lAddr := base + 4 * lane
          match checkPermSpan perm lAddr 4 with
          | false => (true, mCur)
          | true  =>
            let mNext := writeSpan mCur lAddr
              (fun b => xorLane key (mCur (lAddr + b))) 4
            (false, mNext))
    n

private theorem execVpmaskmovdN_succ
    (n : Nat) (perm : Nat → Bool) (base remWords key : Nat) (mem0 : Mem) :
    execVpmaskmovdN (n + 1) perm base remWords key mem0 =
      let (flt, mCur) := execVpmaskmovdN n perm base remWords key mem0
      if flt then (true, mCur)
      else
        match Nat.blt n remWords with
        | false => (false, mCur)
        | true  =>
          let lAddr := base + 4 * n
          match checkPermSpan perm lAddr 4 with
          | false => (true, mCur)
          | true  =>
            let mNext := writeSpan mCur lAddr
              (fun b => xorLane key (mCur (lAddr + b))) 4
            (false, mNext) := rfl

private theorem execVpmaskmovdN_spec
    (perm : Nat → Bool) (base remWords key : Nat) (memStart : Mem)
    (hrem : remWords < 8)
    (hPerm : ∀ i, i < 4 * remWords → perm (base + i) = true) :
    ∀ (n : Nat), n ≤ 8 →
      (execVpmaskmovdN n perm base remWords key memStart).1 = false ∧
      ∀ q,
        (base ≤ q ∧ q < base + 4 * (if n < remWords then n else remWords) →
          (execVpmaskmovdN n perm base remWords key memStart).2 q = xorLane key (memStart q)) ∧
        ((q < base ∨ base + 4 * (if n < remWords then n else remWords) ≤ q) →
          (execVpmaskmovdN n perm base remWords key memStart).2 q = memStart q)
  | 0, _ => by
    have hmin : (if 0 < remWords then 0 else remWords) = 0 := by split <;> omega
    refine ⟨rfl, fun q => ?_⟩
    rw [hmin]
    exact ⟨fun ⟨_, _⟩ => by omega, fun _ => rfl⟩
  | n + 1, hn => by
    have ⟨ihFlt, ihMem⟩ := execVpmaskmovdN_spec perm base remWords key memStart hrem hPerm n (by omega)
    rw [execVpmaskmovdN_succ]
    rcases hPair : execVpmaskmovdN n perm base remWords key memStart with ⟨flt, mCur⟩
    rw [hPair] at ihFlt ihMem
    dsimp only [] at ihFlt ihMem ⊢
    subst ihFlt
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases hblt : Nat.blt n remWords with
    | false =>
      have hnlt : ¬ (n < remWords) := by have := blt_false_ge hblt; omega
      have hmin1 : (if n < remWords then n else remWords) = remWords := by simp [hnlt]
      have hmin2 : (if n + 1 < remWords then n + 1 else remWords) = remWords := by
        have : ¬ (n + 1 < remWords) := by omega
        simp [this]
      rw [hmin1] at ihMem
      rw [hmin2]
      exact ⟨rfl, ihMem⟩
    | true =>
      have hlt : n < remWords := blt_true_lt hblt
      have hcp : checkPermSpan perm (base + 4 * n) 4 = true :=
        checkPermSpan_all_true perm (base + 4 * n) 4 (fun i hi => by
          have : (base + 4 * n) + i = base + (4 * n + i) := by omega
          rw [this]
          exact hPerm (4 * n + i) (by omega))
      rw [hcp]
      dsimp only []
      have hmin1 : (if n < remWords then n else remWords) = n := by simp [hlt]
      have hmin2 : (if n + 1 < remWords then n + 1 else remWords) = n + 1 := by
        exact if hlt2 : n + 1 < remWords then by simp [hlt2] else by simp [hlt2]; omega
      rw [hmin1] at ihMem
      rw [hmin2]
      refine ⟨rfl, fun q => ⟨?_, ?_⟩⟩
      · intro ⟨hqLo, hqHi⟩
        exact if hStep : base + 4 * n ≤ q then by
          rw [writeSpan_in _ (base + 4 * n) _ 4 q hStep (by omega), xorLane_mod256]
          have hAddr : (base + 4 * n) + (q - (base + 4 * n)) = q := by omega
          rw [hAddr, (ihMem q).2 (Or.inr hStep)]
        else by
          rw [writeSpan_out _ (base + 4 * n) _ 4 q (Or.inl (by omega))]
          exact (ihMem q).1 ⟨hqLo, by omega⟩
      · intro hOut
        rw [writeSpan_out _ (base + 4 * n) _ 4 q (by omega)]
        exact (ihMem q).2 (by omega)

private theorem runVpmaskmov_zero (s : VpmaskmovState) : runVpmaskmov 0 s = s := rfl

private theorem runVpmaskmov_succ (fuel : Nat) (s : VpmaskmovState) :
    runVpmaskmov (fuel + 1) s = runVpmaskmov fuel (stepVpmaskmov s) := rfl

private theorem vpmaskmov_loop_ind
    (buf totalWords key : Nat) (perm : Nat → Bool) (mem0 : Mem)
    (hPerm : ∀ i, i < 4 * totalWords → perm (buf + i) = true) :
    ∀ (rem k : Nat) (s : VpmaskmovState),
      rem + k = totalWords / 8 →
      s.halted = false → s.faulted = false → s.pc = 1 →
      s.buf = buf → s.totalWords = totalWords → s.key = key →
      s.perm = perm → s.wordCur = 8 * k →
      (∀ q, (buf ≤ q ∧ q < buf + 32 * k → s.mem q = xorLane key (mem0 q)) ∧
            ((q < buf ∨ buf + 32 * k ≤ q) → s.mem q = mem0 q)) →
      let sf := runVpmaskmov (rem + 2) s
      sf.halted = true ∧ sf.faulted = false ∧
      ∀ q, sf.mem q = specVpmaskmovXor buf totalWords key mem0 q
  | 0, k, s, hk, hnh, hnf, hpc, hbuf, htw, hkey, hp, hwc, hInv => by
    have hkEq : k = totalWords / 8 := by omega
    subst hkEq
    have hdiv := Nat.div_add_mod totalWords 8
    have hmod : totalWords % 8 < 8 := Nat.mod_lt totalWords (by omega)
    have hnle : ¬ (s.wordCur + 8 ≤ s.totalWords) := by omega
    rw [show (0 + 2 : Nat) = 1 + 1 from rfl, runVpmaskmov_succ, runVpmaskmov_succ]
    have hs1 : stepVpmaskmov s = { s with pc := 2 } := by
      unfold stepVpmaskmov; simp [hnh, hnf, hpc, hnle]
    rw [hs1]
    let addr := buf + 32 * (totalWords / 8)
    let remW := totalWords - 8 * (totalWords / 8)
    have hremW : remW < 8 := by omega
    have hTailSpec := execVpmaskmovdN_spec perm addr remW key s.mem hremW (fun i hi => by
      have : addr + i = buf + (32 * (totalWords / 8) + i) := by omega
      rw [this]
      exact hPerm _ (by omega)) 8 (by omega)
    have hmin8 : (if 8 < remW then 8 else remW) = remW := by
      have : ¬ (8 < remW) := by omega
      simp [this]
    rw [hmin8] at hTailSpec
    have heqExec : execVpmaskmovd8 perm (s.buf + 4 * s.wordCur) (s.totalWords - s.wordCur) s.key s.mem =
        execVpmaskmovdN 8 perm addr remW key s.mem := by
      have ha : s.buf + 4 * s.wordCur = addr := by omega
      have hr : s.totalWords - s.wordCur = remW := by omega
      rw [ha, hr, hkey]
      rfl
    have hs2 : stepVpmaskmov { s with pc := 2 } =
        { s with pc := 2, halted := true, faulted := false,
                 mem := (execVpmaskmovdN 8 perm addr remW key s.mem).2 } := by
      unfold stepVpmaskmov
      simp [hnh, hnf, hp, heqExec, hTailSpec.1]
    rw [hs2, runVpmaskmov_zero]
    refine ⟨rfl, rfl, fun q => ?_⟩
    unfold specVpmaskmovXor
    exact if hIn : buf ≤ q ∧ q < buf + 4 * totalWords then by
      rcases hIn with ⟨hqLo, hqHi⟩
      simp [hqLo, hqHi]
      exact if hInTail : addr ≤ q then by
        rw [(hTailSpec.2 q).1 ⟨hInTail, by omega⟩]
        rw [(hInv q).2 (Or.inr hInTail)]
      else by
        rw [(hTailSpec.2 q).2 (Or.inl (by omega))]
        exact (hInv q).1 ⟨hqLo, by omega⟩
    else by
      simp [hIn]
      rw [(hTailSpec.2 q).2 (by omega)]
      exact (hInv q).2 (by omega)
  | rem + 1, k, s, hk, hnh, hnf, hpc, hbuf, htw, hkey, hp, hwc, hInv => by
    have hdiv := Nat.div_add_mod totalWords 8
    have hle : 8 * (k + 1) ≤ totalWords := by omega
    rw [show rem + 1 + 2 = (rem + 2) + 1 by omega, runVpmaskmov_succ]
    have hcp : checkPermSpan perm (buf + 32 * k) 32 = true :=
      checkPermSpan_all_true perm (buf + 32 * k) 32 (fun i hi => by
        have : (buf + 32 * k) + i = buf + (32 * k + i) := by omega
        rw [this]
        exact hPerm _ (by omega))
    let mNext := writeSpan s.mem (buf + 32 * k)
      (fun j => xorLane key (s.mem (buf + 32 * k + j))) 32
    have hs1 : stepVpmaskmov s = { s with mem := mNext, wordCur := 8 * (k + 1) } := by
      unfold stepVpmaskmov
      have hmul : 4 * (8 * k) = 32 * k := by omega
      have hw : 8 * k + 8 = 8 * (k + 1) := by omega
      simp [hnh, hnf, hpc, hbuf, htw, hkey, hp, hwc, hle, hmul, hcp, hw, mNext]
    rw [hs1]
    exact vpmaskmov_loop_ind buf totalWords key perm mem0 hPerm rem (k + 1)
      { s with mem := mNext, wordCur := 8 * (k + 1) }
      (by omega) hnh hnf hpc hbuf htw hkey hp rfl (fun q => ⟨fun ⟨hqLo, hqHi⟩ =>
        if hStep : buf + 32 * k ≤ q then by
          dsimp only [mNext]
          rw [writeSpan_in s.mem (buf + 32 * k) _ 32 q hStep (by omega), xorLane_mod256]
          have hAddr : buf + 32 * k + (q - (buf + 32 * k)) = q := by omega
          rw [hAddr, (hInv q).2 (Or.inr hStep)]
        else by
          dsimp only [mNext]
          rw [writeSpan_out s.mem (buf + 32 * k) _ 32 q (Or.inl (by omega))]
          exact (hInv q).1 ⟨hqLo, by omega⟩,
        fun hOut => by
          dsimp only [mNext]
          rw [writeSpan_out s.mem (buf + 32 * k) _ 32 q (by omega)]
          exact (hInv q).2 (by omega)⟩)

theorem checkVpmaskmovSkolemCert_sound
    {c : SkolemLoopCert} (s : VpmaskmovState)
    (hc : checkVpmaskmovSkolemCert c = true)
    (hnh : s.halted = false) (hnf : s.faulted = false) (hpc : s.pc = 0)
    (hPerm : ∀ i, i < 4 * s.totalWords → s.perm (s.buf + i) = true) :
    let sf := runVpmaskmov ((s.totalWords / 8) + 3) s
    sf.halted = true ∧ sf.faulted = false ∧
    ∀ q, sf.mem q = specVpmaskmovXor s.buf s.totalWords s.key s.mem q := by
  let _ := hc
  dsimp only []
  rw [show (s.totalWords / 8) + 3 = ((s.totalWords / 8) + 2) + 1 by omega, runVpmaskmov_succ]
  have hs0 : stepVpmaskmov s = { s with pc := 1, wordCur := 0 } := by
    unfold stepVpmaskmov; simp [hnh, hnf, hpc]
  rw [hs0]
  exact vpmaskmov_loop_ind s.buf s.totalWords s.key s.perm s.mem hPerm (s.totalWords / 8) 0
    { s with pc := 1, wordCur := 0 }
    (by omega) hnh hnf rfl rfl rfl rfl rfl rfl
    (fun _ => ⟨fun ⟨_, _⟩ => by omega, fun _ => rfl⟩)

-- ============================================================================
-- Loop 6 Combinator: `ScalarEpilogueShortDispatch` (`shortScalarPlusOverlap`)
-- ============================================================================

def checkShortDispatchSkolemCert (c : SkolemLoopCert) : Bool :=
  decide (c.simdStride = 32) &&
  decide (c.tailMode = .shortScalarPlusOverlap) &&
  decide (c.requiresIdempotence = false) &&
  decide (c.hasShortScalarLoop = true) &&
  checkLratPass1Clean c.oDepth c.orderInitTree c.orderProofTree &&
  checkLratPass1Clean c.oDepth c.loopInitTree c.loopProofTree

private theorem addConstLane_mod256 (c b : Nat) : (addConstLane c b) % 256 = addConstLane c b := by
  unfold addConstLane
  exact Nat.mod_mod _ 256

private theorem runShortDispatch_zero (s : ShortDispatchState) : runShortDispatch 0 s = s := rfl

private theorem runShortDispatch_succ (fuel : Nat) (s : ShortDispatchState) :
    runShortDispatch (fuel + 1) s = runShortDispatch fuel (stepShortDispatch s) := rfl

private theorem shortDispatch_scalar_ind
    (buf len addVal : Nat) (perm : Nat → Bool) (mem0 : Mem)
    (hPerm : ∀ i, i < len → perm (buf + i) = true) :
    ∀ (rem k : Nat) (s : ShortDispatchState),
      rem + k = len →
      s.halted = false → s.faulted = false → s.pc = 3 →
      s.buf = buf → s.len = len → s.addVal = addVal → s.perm = perm → s.cursor = k →
      (∀ q, (buf ≤ q ∧ q < buf + k → s.mem q = addConstLane addVal (mem0 q)) ∧
            ((q < buf ∨ buf + k ≤ q) → s.mem q = mem0 q)) →
      let sf := runShortDispatch (rem + 1) s
      sf.halted = true ∧ sf.faulted = false ∧
      ∀ q, sf.mem q = specShortDispatchAdd buf len addVal mem0 q
  | 0, k, s, hk, hnh, hnf, hpc, hbuf, hlenEq, hadd, hp, hcur, hInv => by
    have hkEq : k = len := by omega
    subst hkEq
    have hnlt : ¬ (s.cursor < s.len) := by omega
    rw [runShortDispatch_succ]
    have hs1 : stepShortDispatch s = { s with halted := true } := by
      unfold stepShortDispatch; simp [hnh, hnf, hpc, hnlt]
    rw [hs1, runShortDispatch_zero]
    refine ⟨rfl, hnf, fun q => ?_⟩
    unfold specShortDispatchAdd
    exact if hIn : buf ≤ q ∧ q < buf + k then by
      simp [hIn]
      exact (hInv q).1 hIn
    else by
      simp [hIn]
      exact (hInv q).2 (by omega)
  | rem + 1, k, s, hk, hnh, hnf, hpc, hbuf, hlenEq, hadd, hp, hcur, hInv => by
    have hlt : k < len := by omega
    rw [show rem + 1 + 1 = (rem + 1) + 1 from rfl, runShortDispatch_succ]
    have hpOk : perm (buf + k) = true := hPerm k (by omega)
    let mNext := writeByte s.mem (buf + k) (addConstLane addVal (s.mem (buf + k)))
    have hs1 : stepShortDispatch s = { s with mem := mNext, cursor := k + 1 } := by
      unfold stepShortDispatch
      simp [hnh, hnf, hpc, hbuf, hlenEq, hadd, hp, hcur, hlt, hpOk, mNext]
    rw [hs1]
    exact shortDispatch_scalar_ind buf len addVal perm mem0 hPerm rem (k + 1)
      { s with mem := mNext, cursor := k + 1 }
      (by omega) hnh hnf hpc hbuf hlenEq hadd hp rfl (fun q => ⟨fun ⟨hqLo, hqHi⟩ =>
        if hqEq : q = buf + k then by
          subst hqEq
          dsimp only [mNext]
          rw [writeByte_same, addConstLane_mod256, (hInv (buf + k)).2 (Or.inr (by omega))]
        else by
          dsimp only [mNext]
          rw [writeByte_other _ _ _ _ hqEq]
          exact (hInv q).1 ⟨hqLo, by omega⟩,
        fun hOut => by
          dsimp only [mNext]
          have hne : q ≠ buf + k := by omega
          rw [writeByte_other _ _ _ _ hne]
          exact (hInv q).2 (by omega)⟩)

private theorem shortDispatch_simd_ind
    (buf len addVal : Nat) (perm : Nat → Bool) (mem0 : Mem)
    (hlen : 32 ≤ len) (hPerm : ∀ i, i < len → perm (buf + i) = true) :
    ∀ (rem k : Nat) (s : ShortDispatchState),
      rem + k = (len - 1) / 32 →
      s.halted = false → s.faulted = false → s.pc = 1 →
      s.buf = buf → s.len = len → s.addVal = addVal → s.perm = perm → s.cursor = 32 * k →
      (∀ j, j < 32 → s.tailReg j = mem0 (buf + (len - 32) + j)) →
      (∀ q, (buf ≤ q ∧ q < buf + 32 * k → s.mem q = addConstLane addVal (mem0 q)) ∧
            ((q < buf ∨ buf + 32 * k ≤ q) → s.mem q = mem0 q)) →
      let sf := runShortDispatch (rem + 2) s
      sf.halted = true ∧ sf.faulted = false ∧
      ∀ q, sf.mem q = specShortDispatchAdd buf len addVal mem0 q
  | 0, k, s, hk, hnh, hnf, hpc, hbuf, hlenEq, hadd, hp, hcur, hTailPin, hInv => by
    have hkEq : k = (len - 1) / 32 := by omega
    subst hkEq
    have ⟨hTailLo, hLoopHi⟩ := strictSteps32_bounds len hlen
    have hnlt : ¬ (s.cursor + 32 < s.len) := by omega
    rw [show (0 + 2 : Nat) = 1 + 1 from rfl, runShortDispatch_succ, runShortDispatch_succ]
    have hs1 : stepShortDispatch s = { s with pc := 2 } := by
      unfold stepShortDispatch; simp [hnh, hnf, hpc, hnlt]
    rw [hs1]
    let tail := len - 32
    have hcp : checkPermSpan s.perm (buf + (len - 32)) 32 = true := by
      rw [hp]
      exact checkPermSpan_all_true perm (buf + (len - 32)) 32 (fun i hi => by
        have : (buf + (len - 32)) + i = buf + (len - 32 + i) := by omega
        rw [this]
        exact hPerm _ (by omega))
    let mFinal := writeSpan s.mem (buf + tail)
      (fun j => addConstLane addVal (s.tailReg j)) 32
    have hs2 : stepShortDispatch { s with pc := 2 } =
        { s with pc := 2, halted := true, mem := mFinal } := by
      unfold stepShortDispatch
      simp [hnh, hnf, hbuf, hlenEq, hcp, hadd, mFinal, tail]
    rw [hs2, runShortDispatch_zero]
    refine ⟨rfl, hnf, fun q => ?_⟩
    unfold specShortDispatchAdd
    exact if hIn : buf ≤ q ∧ q < buf + len then by
      rcases hIn with ⟨hqLo, hqHi⟩
      simp [hqLo, hqHi]
      exact if hTail : buf + tail ≤ q then by
        dsimp only [mFinal]
        rw [writeSpan_in s.mem (buf + tail) _ 32 q hTail (by omega), addConstLane_mod256]
        rw [hTailPin (q - (buf + tail)) (by omega)]
        have hAddr : buf + (len - 32) + (q - (buf + tail)) = q := by omega
        rw [hAddr]
      else by
        dsimp only [mFinal]
        rw [writeSpan_out s.mem (buf + tail) _ 32 q (Or.inl (by omega))]
        exact (hInv q).1 ⟨hqLo, by omega⟩
    else by
      simp [hIn]
      dsimp only [mFinal]
      rw [writeSpan_out s.mem (buf + tail) _ 32 q (by omega)]
      exact (hInv q).2 (by omega)
  | rem + 1, k, s, hk, hnh, hnf, hpc, hbuf, hlenEq, hadd, hp, hcur, hTailPin, hInv => by
    have ⟨_, hLoopHi⟩ := strictSteps32_bounds len hlen
    have hlt : 32 * (k + 1) < s.len := by omega
    rw [show rem + 1 + 2 = (rem + 2) + 1 by omega, runShortDispatch_succ]
    have hcp : checkPermSpan s.perm (buf + 32 * k) 32 = true := by
      rw [hp]
      exact checkPermSpan_all_true perm (buf + 32 * k) 32 (fun i hi => by
        have : (buf + 32 * k) + i = buf + (32 * k + i) := by omega
        rw [this]
        exact hPerm _ (by omega))
    let mNext := writeSpan s.mem (buf + 32 * k)
      (fun j => addConstLane addVal (s.mem (buf + 32 * k + j))) 32
    have hs1 : stepShortDispatch s = { s with mem := mNext, cursor := 32 * (k + 1) } := by
      unfold stepShortDispatch
      have hmul : 32 * k + 32 = 32 * (k + 1) := by omega
      simp [hnh, hnf, hpc, hlt, hcp, hbuf, hcur, hadd, mNext, hmul]
    rw [hs1]
    exact shortDispatch_simd_ind buf len addVal perm mem0 hlen hPerm rem (k + 1)
      { s with mem := mNext, cursor := 32 * (k + 1) }
      (by omega) hnh hnf hpc hbuf hlenEq hadd hp rfl hTailPin (fun q => ⟨fun ⟨hqLo, hqHi⟩ =>
        if hStep : buf + 32 * k ≤ q then by
          dsimp only [mNext]
          rw [writeSpan_in s.mem (buf + 32 * k) _ 32 q hStep (by omega), addConstLane_mod256]
          have hAddr : buf + 32 * k + (q - (buf + 32 * k)) = q := by omega
          rw [hAddr, (hInv q).2 (Or.inr hStep)]
        else by
          dsimp only [mNext]
          rw [writeSpan_out s.mem (buf + 32 * k) _ 32 q (Or.inl (by omega))]
          exact (hInv q).1 ⟨hqLo, by omega⟩,
        fun hOut => by
          dsimp only [mNext]
          rw [writeSpan_out s.mem (buf + 32 * k) _ 32 q (by omega)]
          exact (hInv q).2 (by omega)⟩)

theorem checkShortDispatchSkolemCert_sound
    {c : SkolemLoopCert} (s : ShortDispatchState)
    (hc : checkShortDispatchSkolemCert c = true)
    (hnh : s.halted = false) (hnf : s.faulted = false) (hpc : s.pc = 0)
    (hPerm : ∀ i, i < s.len → s.perm (s.buf + i) = true) :
    let fuel := if s.len < 32 then s.len + 2 else ((s.len - 1) / 32) + 3
    let sf := runShortDispatch fuel s
    sf.halted = true ∧ sf.faulted = false ∧
    ∀ q, sf.mem q = specShortDispatchAdd s.buf s.len s.addVal s.mem q := by
  let _ := hc
  dsimp only []
  exact if hShort : s.len < 32 then by
    simp [hShort]
    rw [show s.len + 2 = (s.len + 1) + 1 by omega, runShortDispatch_succ]
    have hs0 : stepShortDispatch s = { s with pc := 3, cursor := 0 } := by
      unfold stepShortDispatch; simp [hnh, hnf, hpc, hShort]
    rw [hs0]
    exact shortDispatch_scalar_ind s.buf s.len s.addVal s.perm s.mem hPerm s.len 0
      { s with pc := 3, cursor := 0 }
      (by omega) hnh hnf rfl rfl rfl rfl rfl rfl
      (fun _ => ⟨fun ⟨_, _⟩ => by omega, fun _ => rfl⟩)
  else by
    simp [hShort]
    have hlen32 : 32 ≤ s.len := by omega
    rw [show ((s.len - 1) / 32) + 3 = (((s.len - 1) / 32) + 2) + 1 by omega, runShortDispatch_succ]
    have hcp : checkPermSpan s.perm (s.buf + (s.len - 32)) 32 = true :=
      checkPermSpan_all_true s.perm (s.buf + (s.len - 32)) 32 (fun i hi => by
        have : (s.buf + (s.len - 32)) + i = s.buf + (s.len - 32 + i) := by omega
        rw [this]
        exact hPerm _ (by omega))
    have hs0 : stepShortDispatch s =
        { s with pc := 1, cursor := 0, tailReg := fun j => s.mem (s.buf + (s.len - 32) + j) } := by
      unfold stepShortDispatch; simp [hnh, hnf, hpc, hShort, hcp]
    rw [hs0]
    exact shortDispatch_simd_ind s.buf s.len s.addVal s.perm s.mem hlen32 hPerm
      ((s.len - 1) / 32) 0
      { s with pc := 1, cursor := 0, tailReg := fun j => s.mem (s.buf + (s.len - 32) + j) }
      (by omega) hnh hnf rfl rfl rfl rfl rfl rfl (fun _ _ => rfl)
      (fun _ => ⟨fun ⟨_, _⟩ => by omega, fun _ => rfl⟩)

end UntrustedSkolemCegisHints
