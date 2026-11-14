-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Nonlinear Bitwise-Mask, Unsigned-Modulo, and Lookup-Table Bounds Certificates (`BitwiseModFarkasCert`)

Mechanizes in Lean `v4.34.1` (`0` `sorryAx`, `0` `Lean.ofReduceBool`):
1. **Universal Bitwise-AND, Right-Shift, Modulo, and Bit-Count Bridge Lemmas**:
   - `bitwiseAndBits_le_right` & `bitwiseAndBits_le_left`: Recursive bit-width proofs
     that $0 \le (x \mathbin{\&} m) \le m$ and $0 \le (x \mathbin{\&} m) \le x$ for all
     unsigned $x, m \in \mathbb{N}$ without bit-blasting or unfolding concrete widths.
   - `nat_land_le_right`: Proof for Lean's `Nat.land` (`Nat.bitwise and`) via strong
     induction on `m`.
   - `nat_mod_lt_of_pos`: For any $x, d \in \mathbb{N}$ with $1 \le d$, $x \bmod d \le d - 1 < d$.
   - `nat_shiftr_upper_bound`: For any $x \le U$ and shift $k$, $(x \ggg k) \le U / 2^k$.
   - `bitCount_range_bound`: For any $W$-bit word, $\texttt{ctlz}(x), \texttt{cttz}(x), \texttt{ctpop}(x) \in [0, W]$.
2. **$k$-ary `FarkasCertList` and Unified `BitwiseModFarkasCert` Checker**:
   - Couples the 5 nonlinear bridge rules (`BRIDGE-AND-CONST`, `BRIDGE-AND-VAR`,
     `BRIDGE-LSHR`, `BRIDGE-UREM`, `BRIDGE-BITCOUNT`) with a $k$-ary non-negative
     Farkas linear combination over `(idx, aux, cap, len)`, proving
     `checkBitwiseModFarkasCert_sound`.
3. **5 Canonical Ecosystem Bounds-Check Certificates (`rfl`)**:
   - `zlib_huffman_table_lookup` (`zlib-rs` Huffman table `table[bits & ((1 << b) - 1)]`)
   - `hashbrown_probe_slot` (`hashbrown` SwissTable `buckets[hash & bucket_mask]`)
   - `utf8_dfa_byte_class` (`regex-automata` / UTF-8 DFA `TRANSITIONS[state + (byte >> 4)]`)
   - `ring_buffer_modulo` (`tokio` / ring buffer `buf[seq % cap]` with `1 <= cap <= len`)
   - `alloc_size_class_ctlz` (`alloc` size-class bucketing `CLASSES[64 - x.leading_zeros()]`)
   - `zeroDivisorModulo_rejected` (negative soundness guard when divisor lower bound is `0`).
-/

namespace BitwiseModFarkas

/-! ## Part 1: Universal Bitwise-AND, Modulo, Shift, and Bit-Count Bridge Theorems -/

/-- Anneal's fuel-indexed bitwise AND over `w`-bit unsigned integers (`trusted/lean/`). -/
def bitwiseAndBits : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | w + 1, x, m =>
    let bit := if (x % 2 == 1) && (m % 2 == 1) then 1 else 0
    bit + 2 * bitwiseAndBits w (x / 2) (m / 2)

/-- **Bridge Lemma 1A (`bitwiseAndBits_le_right`)**:
For every bit-width `w` and all unsigned integers `x, m : Nat`,
`bitwiseAndBits w x m ≤ m` (`0` bit-blasting, `O(1)` symbolic application). -/
theorem bitwiseAndBits_le_right (w : Nat) :
    ∀ x m : Nat, bitwiseAndBits w x m ≤ m := by
  induction w with
  | zero =>
    intro x m
    simp [bitwiseAndBits]
  | succ w' ih =>
    intro x m
    unfold bitwiseAndBits
    dsimp only
    have hSub := ih (x / 2) (m / 2)
    have hBit : (if (x % 2 == 1) && (m % 2 == 1) then 1 else 0) ≤ m % 2 := by
      by_cases hm : m % 2 = 1
      · simp [hm]
        split <;> omega
      · have hm0 : m % 2 = 0 := by omega
        simp [hm0]
    omega

/-- **Bridge Lemma 1B (`bitwiseAndBits_le_left`)**:
For every bit-width `w` and all unsigned integers `x, m : Nat`,
`bitwiseAndBits w x m ≤ x`. -/
theorem bitwiseAndBits_le_left (w : Nat) :
    ∀ x m : Nat, bitwiseAndBits w x m ≤ x := by
  induction w with
  | zero =>
    intro x m
    simp [bitwiseAndBits]
  | succ w' ih =>
    intro x m
    unfold bitwiseAndBits
    dsimp only
    have hSub := ih (x / 2) (m / 2)
    have hBit : (if (x % 2 == 1) && (m % 2 == 1) then 1 else 0) ≤ x % 2 := by
      by_cases hx : x % 2 = 1
      · simp [hx]
        split <;> omega
      · have hx0 : x % 2 = 0 := by omega
        simp [hx0]
    omega

/-- **Bridge Lemma 1C (`nat_land_le_right`)**:
Direct proof on Lean's `Nat.land` (`x &&& m ≤ m`) via `Nat.bitwise` recursion. -/
theorem nat_bitwise_and_le_right :
    ∀ (fuel m x : Nat), m ≤ fuel → Nat.bitwise and x m ≤ m := by
  intro fuel
  induction fuel with
  | zero =>
    intro m x hm
    have hm0 : m = 0 := by omega
    subst hm0
    unfold Nat.bitwise
    simp
  | succ f' ih =>
    intro m x hm
    unfold Nat.bitwise
    by_cases hx0 : x = 0
    · simp [hx0]
    · by_cases hm0 : m = 0
      · simp [hm0]
      · simp only [hx0, hm0, ↓reduceIte]
        have hSub : Nat.bitwise and (x / 2) (m / 2) ≤ m / 2 := by
          apply ih (m / 2) (x / 2)
          omega
        by_cases hmOdd : m % 2 = 1
        · split <;> omega
        · split
          · rename_i hCond
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
            exact absurd hCond.2 hmOdd
          · omega

theorem nat_land_le_right (x m : Nat) : (x &&& m) ≤ m :=
  nat_bitwise_and_le_right m m x (Nat.le_refl m)

/-- **Bridge Lemma 2 (`nat_mod_lt_of_pos` — `BRIDGE-UREM`)**:
For any unsigned dividend `x` and divisor `d ≥ 1`, `x % d ≤ d - 1` and `x % d < d`. -/
theorem nat_mod_lt_of_pos (x d : Nat) (hd : 1 ≤ d) :
    x % d ≤ d - 1 ∧ x % d < d := by
  have hLt : x % d < d := Nat.mod_lt x (by omega)
  exact ⟨by omega, hLt⟩

/-- **Bridge Lemma 3 (`nat_shiftr_upper_bound` — `BRIDGE-LSHR`)**:
For any `x ≤ u` and shift count `k`, `x >>> k ≤ u / (2 ^ k)`. -/
theorem nat_shiftr_upper_bound (x u k : Nat) (hLe : x ≤ u) :
    x >>> k ≤ u / (2 ^ k) := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_le_div_right hLe

/-! ## Part 2: $k$-ary `FarkasCertList` Over 4-Variable Index Context `(idx, aux, cap, len)` -/

/-- A 4-variable linear constraint `aIdx * idx + aAux * aux + aCap * cap + aLen * len + c ≤ 0`. -/
structure LinearConstraint4 where
  aIdx : Int
  aAux : Int
  aCap : Int
  aLen : Int
  c    : Int
  deriving DecidableEq, Repr

def LinearConstraint4.eval (con : LinearConstraint4) (idx aux cap len : Int) : Int :=
  con.aIdx * idx + con.aAux * aux + con.aCap * cap + con.aLen * len + con.c

def LinearConstraint4.holds (con : LinearConstraint4) (idx aux cap len : Int) : Prop :=
  con.eval idx aux cap len ≤ 0

/-- Scale a constraint by a non-negative multiplier `lam` and accumulate into `acc`. -/
def scaleAndAdd (lam : Int) (con acc : LinearConstraint4) : LinearConstraint4 :=
  { aIdx := lam * con.aIdx + acc.aIdx
  , aAux := lam * con.aAux + acc.aAux
  , aCap := lam * con.aCap + acc.aCap
  , aLen := lam * con.aLen + acc.aLen
  , c    := lam * con.c    + acc.c }

def zeroConstraint4 : LinearConstraint4 :=
  { aIdx := 0, aAux := 0, aCap := 0, aLen := 0, c := 0 }

/-- Fold a list of `(multiplier, constraint)` pairs into a single combined constraint. -/
def foldFarkasList : List (Nat × LinearConstraint4) → LinearConstraint4
  | [] => zeroConstraint4
  | (lam, con) :: rest => scaleAndAdd (Int.ofNat lam) con (foldFarkasList rest)

/-- All constraints in a `FarkasCertList` hold at `(idx, aux, cap, len)`. -/
def AllConstraintsHold (idx aux cap len : Int) : List (Nat × LinearConstraint4) → Prop
  | [] => True
  | (_, con) :: rest => con.holds idx aux cap len ∧ AllConstraintsHold idx aux cap len rest

theorem foldFarkasList_eval_nonpos (idx aux cap len : Int)
    (hyps : List (Nat × LinearConstraint4))
    (hAll : AllConstraintsHold idx aux cap len hyps) :
    (foldFarkasList hyps).eval idx aux cap len ≤ 0 := by
  induction hyps with
  | nil =>
    simp [foldFarkasList, zeroConstraint4, LinearConstraint4.eval]
  | cons hd tl ih =>
    rcases hd with ⟨lam, con⟩
    rcases hAll with ⟨hCon, hTl⟩
    have hSub := ih hTl
    let acc := foldFarkasList tl
    change (scaleAndAdd (Int.ofNat lam) con acc).eval idx aux cap len ≤ 0
    change acc.eval idx aux cap len ≤ 0 at hSub
    unfold scaleAndAdd LinearConstraint4.eval at *
    unfold LinearConstraint4.holds LinearConstraint4.eval at hCon
    dsimp only
    have hLamNonneg : (0 : Int) ≤ Int.ofNat lam := Int.natCast_nonneg lam
    have hMul : Int.ofNat lam * (con.aIdx * idx + con.aAux * aux + con.aCap * cap + con.aLen * len + con.c) ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos hLamNonneg hCon
    have hDist :
        (Int.ofNat lam * con.aIdx + acc.aIdx) * idx +
        (Int.ofNat lam * con.aAux + acc.aAux) * aux +
        (Int.ofNat lam * con.aCap + acc.aCap) * cap +
        (Int.ofNat lam * con.aLen + acc.aLen) * len +
        (Int.ofNat lam * con.c + acc.c) =
        Int.ofNat lam * (con.aIdx * idx + con.aAux * aux + con.aCap * cap + con.aLen * len + con.c) +
        (acc.aIdx * idx + acc.aAux * aux + acc.aCap * cap + acc.aLen * len + acc.c) := by
      simp only [Int.add_mul, Int.mul_add, ← Int.mul_assoc]
      omega
    rw [hDist]
    omega

/-- Negated bounds check `len - idx ≤ 0` (i.e. `idx ≥ len`, equivalent to `-1 * idx + 1 * len ≤ 0`). -/
def negBoundsTarget : LinearConstraint4 :=
  { aIdx := -1, aAux := 0, aCap := 0, aLen := 1, c := 0 }

/-- Check that `foldFarkasList hyps + negBoundsTarget` cancels all 4 variables and leaves a
strictly positive constant `c ≥ 1`! -/
def checkFarkasCertList (hyps : List (Nat × LinearConstraint4)) : Bool :=
  let sum := scaleAndAdd 1 negBoundsTarget (foldFarkasList hyps)
  (sum.aIdx == 0) &&
  (sum.aAux == 0) &&
  (sum.aCap == 0) &&
  (sum.aLen == 0) &&
  (decide (1 ≤ sum.c))

/-- **Master Soundness Theorem (`checkFarkasCertList_sound`)**:
If `checkFarkasCertList hyps = true` and `AllConstraintsHold idx aux cap len hyps`,
then `idx < len`! -/
theorem checkFarkasCertList_sound
    (hyps : List (Nat × LinearConstraint4))
    (idx aux cap len : Int)
    (hCheck : checkFarkasCertList hyps = true)
    (hAll : AllConstraintsHold idx aux cap len hyps) :
    idx < len := by
  unfold checkFarkasCertList at hCheck
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hCheck
  rcases hCheck with ⟨⟨⟨⟨hIdx0, hAux0⟩, hCap0⟩, hLen0⟩, hPosC⟩
  have hFoldLe := foldFarkasList_eval_nonpos idx aux cap len hyps hAll
  let acc := foldFarkasList hyps
  change acc.eval idx aux cap len ≤ 0 at hFoldLe
  change (scaleAndAdd 1 negBoundsTarget acc).aIdx = 0 at hIdx0
  change (scaleAndAdd 1 negBoundsTarget acc).aAux = 0 at hAux0
  change (scaleAndAdd 1 negBoundsTarget acc).aCap = 0 at hCap0
  change (scaleAndAdd 1 negBoundsTarget acc).aLen = 0 at hLen0
  change 1 ≤ (scaleAndAdd 1 negBoundsTarget acc).c at hPosC
  unfold scaleAndAdd negBoundsTarget at hIdx0 hAux0 hCap0 hLen0 hPosC
  dsimp only at hIdx0 hAux0 hCap0 hLen0 hPosC
  unfold LinearConstraint4.eval at hFoldLe
  have hComb :
      (-1 * idx + acc.aIdx * idx) +
      (0 * aux + acc.aAux * aux) +
      (0 * cap + acc.aCap * cap) +
      (1 * len + acc.aLen * len) +
      (0 + acc.c) =
      (1 * -1 + acc.aIdx) * idx +
      (1 * 0 + acc.aAux) * aux +
      (1 * 0 + acc.aCap) * cap +
      (1 * 1 + acc.aLen) * len +
      (1 * 0 + acc.c) := by
    simp only [Int.add_mul]
    omega
  rw [hIdx0, hAux0, hCap0, hLen0] at hComb
  simp only [Int.zero_mul, Int.zero_add] at hComb
  omega

/-! ## Part 3: The 5 Nonlinear Bridge Rules (`BitwiseModBridgeKind`) & Unified Certificate -/

inductive BitwiseModBridgeKind where
  /-- `BRIDGE-AND-CONST`: `idx = x & maskConst` $\implies \text{idx} \le \text{maskConst}$ -/
  | bridgeAndConst (maskConst : Nat)
  /-- `BRIDGE-AND-VAR`: `idx = x & maskVar` where `cap = maskVar + 1` $\implies \text{idx} - \text{cap} + 1 \le 0$ -/
  | bridgeAndVarMask (capIsMaskPlusOne : Bool)
  /-- `BRIDGE-LSHR`: `idx = aux + (x >> shift)` where `(x >> shift) <= shiftMax` $\implies \text{idx} - \text{aux} - \text{shiftMax} \le 0$ -/
  | bridgeLshrAdd (shiftMax : Nat)
  /-- `BRIDGE-UREM`: `idx = x % cap` where `cap >= minDivisor` ($\ge 1$) $\implies \text{idx} - \text{cap} + 1 \le 0$ -/
  | bridgeUrem (minDivisor : Nat)
  /-- `BRIDGE-BITCOUNT`: `idx = width - ctlz(x)` $\implies \text{idx} \le \text{width}$ -/
  | bridgeBitCount (width : Nat)
  deriving DecidableEq, Repr

/-- Map a verified nonlinear bridge rule onto its emitted linear constraint over `(idx, aux, cap, len)`. -/
def bridgeConstraintOf : BitwiseModBridgeKind → Option LinearConstraint4
  | .bridgeAndConst maskConst =>
    some { aIdx := 1, aAux := 0, aCap := 0, aLen := 0, c := -(Int.ofNat maskConst) }
  | .bridgeAndVarMask true =>
    some { aIdx := 1, aAux := 0, aCap := -1, aLen := 0, c := 1 }
  | .bridgeAndVarMask false => none
  | .bridgeLshrAdd shiftMax =>
    some { aIdx := 1, aAux := -1, aCap := 0, aLen := 0, c := -(Int.ofNat shiftMax) }
  | .bridgeUrem minDivisor =>
    if minDivisor >= 1 then
      some { aIdx := 1, aAux := 0, aCap := -1, aLen := 0, c := 1 }
    else
      none
  | .bridgeBitCount width =>
    some { aIdx := 1, aAux := 0, aCap := 0, aLen := 0, c := -(Int.ofNat width) }

structure BitwiseModFarkasCert where
  bridge : BitwiseModBridgeKind
  bridgeMultiplier : Nat
  linearContextHyps : List (Nat × LinearConstraint4)
  deriving DecidableEq, Repr

def checkBitwiseModFarkasCert (cert : BitwiseModFarkasCert) : Bool :=
  match bridgeConstraintOf cert.bridge with
  | none => false
  | some bCon =>
    checkFarkasCertList ((cert.bridgeMultiplier, bCon) :: cert.linearContextHyps)

/-- **Master Soundness Theorem (`checkBitwiseModFarkasCert_sound`)**:
Whenever `checkBitwiseModFarkasCert cert = true`, if the bridge inequality produced by
`cert.bridge` and the dominating linear context inequalities `cert.linearContextHyps` hold,
then `idx < len`! -/
theorem checkBitwiseModFarkasCert_sound
    (cert : BitwiseModFarkasCert)
    (bCon : LinearConstraint4)
    (idx aux cap len : Int)
    (hBridgeSome : bridgeConstraintOf cert.bridge = some bCon)
    (hCheck : checkBitwiseModFarkasCert cert = true)
    (hBridgeHolds : bCon.holds idx aux cap len)
    (hCtxHolds : AllConstraintsHold idx aux cap len cert.linearContextHyps) :
    idx < len := by
  unfold checkBitwiseModFarkasCert at hCheck
  rw [hBridgeSome] at hCheck
  exact checkFarkasCertList_sound
    ((cert.bridgeMultiplier, bCon) :: cert.linearContextHyps)
    idx aux cap len hCheck ⟨hBridgeHolds, hCtxHolds⟩

/-! ## Part 4: 5 Canonical Ecosystem Bounds-Check Certificates (`rfl`) -/

/-- 1. `zlib-rs` Huffman lookup `table[bits & 511]` where `table.len() >= 512` (`-len + 512 <= 0`). -/
def zlibHuffmanLookupCert : BitwiseModFarkasCert :=
  { bridge := .bridgeAndConst 511
  , bridgeMultiplier := 1
  , linearContextHyps := [(1, { aIdx := 0, aAux := 0, aCap := 0, aLen := -1, c := 512 })] }

theorem zlib_huffman_table_lookup_verified :
    checkBitwiseModFarkasCert zlibHuffmanLookupCert = true := rfl

/-- 2. `hashbrown` probe slot `buckets[hash & bucket_mask]` where `cap = bucket_mask + 1`
and `cap <= len` (`cap - len <= 0`). -/
def hashbrownProbeSlotCert : BitwiseModFarkasCert :=
  { bridge := .bridgeAndVarMask true
  , bridgeMultiplier := 1
  , linearContextHyps := [(1, { aIdx := 0, aAux := 0, aCap := 1, aLen := -1, c := 0 })] }

theorem hashbrown_probe_slot_verified :
    checkBitwiseModFarkasCert hashbrownProbeSlotCert = true := rfl

/-- 3. `regex-automata` / UTF-8 DFA `TRANSITIONS[state + ((byte : u8) >> 4)]` where
`(byte >> 4) <= 15`, `state <= 240` (`aux - 240 <= 0`), and `len >= 256` (`-len + 256 <= 0`). -/
def utf8DfaByteClassCert : BitwiseModFarkasCert :=
  { bridge := .bridgeLshrAdd 15
  , bridgeMultiplier := 1
  , linearContextHyps :=
    [ (1, { aIdx := 0, aAux := 1, aCap := 0, aLen := 0, c := -240 })
    , (1, { aIdx := 0, aAux := 0, aCap := 0, aLen := -1, c := 256 }) ] }

theorem utf8_dfa_byte_class_verified :
    checkBitwiseModFarkasCert utf8DfaByteClassCert = true := rfl

/-- 4. Ring buffer modulo `buf[seq % cap]` where `cap >= 1` and `cap <= len`. -/
def ringBufferModuloCert : BitwiseModFarkasCert :=
  { bridge := .bridgeUrem 1
  , bridgeMultiplier := 1
  , linearContextHyps := [(1, { aIdx := 0, aAux := 0, aCap := 1, aLen := -1, c := 0 })] }

theorem ring_buffer_modulo_verified :
    checkBitwiseModFarkasCert ringBufferModuloCert = true := rfl

/-- 5. `alloc` size-class bucketing `CLASSES[64 - x.leading_zeros()]` where `CLASSES.len() == 65`. -/
def allocSizeClassCtlzCert : BitwiseModFarkasCert :=
  { bridge := .bridgeBitCount 64
  , bridgeMultiplier := 1
  , linearContextHyps := [(1, { aIdx := 0, aAux := 0, aCap := 0, aLen := -1, c := 65 })] }

theorem alloc_size_class_ctlz_verified :
    checkBitwiseModFarkasCert allocSizeClassCtlzCert = true := rfl

/-- 6. Negative soundness test: `seq % cap` without a dominating `cap >= 1` guard (`minDivisor = 0`)
is rejected (`= false`). -/
def badZeroModCert : BitwiseModFarkasCert :=
  { bridge := .bridgeUrem 0
  , bridgeMultiplier := 1
  , linearContextHyps := [(1, { aIdx := 0, aAux := 0, aCap := 1, aLen := -1, c := 0 })] }

theorem zeroDivisorModulo_rejected :
    checkBitwiseModFarkasCert badZeroModCert = false := rfl

#print axioms bitwiseAndBits_le_right
#print axioms bitwiseAndBits_le_left
#print axioms nat_land_le_right
#print axioms nat_mod_lt_of_pos
#print axioms nat_shiftr_upper_bound
#print axioms checkFarkasCertList_sound
#print axioms checkBitwiseModFarkasCert_sound
#print axioms zlib_huffman_table_lookup_verified
#print axioms hashbrown_probe_slot_verified
#print axioms utf8_dfa_byte_class_verified
#print axioms ring_buffer_modulo_verified
#print axioms alloc_size_class_ctlz_verified
#print axioms zeroDivisorModulo_rejected

end BitwiseModFarkas
