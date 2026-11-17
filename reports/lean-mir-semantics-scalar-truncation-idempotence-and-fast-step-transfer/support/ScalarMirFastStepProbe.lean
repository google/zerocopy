-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Standalone Lean 4.34.1 probe: Scalar MIR semantics WHNF barriers, fast-step cures, and mutation latency

Self-contained (Lean core `Init` only; zero external imports, zero `sorry`, zero
`native_decide`). Pinned toolchain: `leanprover/lean4` `v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`).
-/

namespace MirTransferProbe

namespace M

inductive IntWidth where
  | i8 | i16 | i32 | i64 | i128 | isize

namespace IntWidth
noncomputable def byteSize : IntWidth → Nat
  | .i8 => 1
  | .i16 => 2
  | .i32 => 4
  | .i64 | .isize => 8
  | .i128 => 16
noncomputable def bitWidth (w : IntWidth) : Nat := w.byteSize * 8
end IntWidth

noncomputable def IntWidth.beq : IntWidth → IntWidth → Bool
  | .i8, .i8 => true
  | .i16, .i16 => true
  | .i32, .i32 => true
  | .i64, .i64 => true
  | .i128, .i128 => true
  | .isize, .isize => true
  | _, _ => false

inductive BinOp where
  | add | addUnchecked | addWithOverflow
  | sub | subUnchecked | subWithOverflow
  | mul | mulUnchecked | mulWithOverflow
  | div | rem
  | bitXor | bitAnd | bitOr
  | shl | shlUnchecked | shr | shrUnchecked
  | eq | lt | le | ne | ge | gt
  | offset

namespace BinOp
noncomputable def isShift : BinOp → Bool
  | .shl | .shlUnchecked | .shr | .shrUnchecked => true
  | _ => false
noncomputable def isUnchecked : BinOp → Bool
  | .addUnchecked | .subUnchecked | .mulUnchecked
  | .shlUnchecked | .shrUnchecked => true
  | _ => false
end BinOp

noncomputable def intEmod : Int → Int → Int
  | .ofNat m, n => .ofNat (Nat.mod m (Int.natAbs n))
  | .negSucc m, n =>
    Int.subNatNat (Int.natAbs n) (Nat.succ (Nat.mod m (Int.natAbs n)))

noncomputable def intTdiv : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (Nat.div m n)
  | .ofNat m, .negSucc n => Int.neg (.ofNat (Nat.div m (Nat.succ n)))
  | .negSucc m, .ofNat n => Int.neg (.ofNat (Nat.div (Nat.succ m) n))
  | .negSucc m, .negSucc n => .ofNat (Nat.div (Nat.succ m) (Nat.succ n))

noncomputable def intTmod : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (Nat.mod m n)
  | .ofNat m, .negSucc n => .ofNat (Nat.mod m (Nat.succ n))
  | .negSucc m, .ofNat n => Int.neg (.ofNat (Nat.mod (Nat.succ m) n))
  | .negSucc m, .negSucc n =>
    Int.neg (.ofNat (Nat.mod (Nat.succ m) (Nat.succ n)))

noncomputable def intShiftRight : Int → Nat → Int
  | .ofNat n, s => .ofNat (Nat.shiftRight n s)
  | .negSucc n, s => .negSucc (Nat.shiftRight n s)

noncomputable def intShiftLeft : Int → Nat → Int
  | .ofNat n, s => .ofNat (Nat.shiftLeft n s)
  | .negSucc n, s => .negSucc ((Nat.shiftLeft (n + 1) s) - 1)

noncomputable def bvExtractLsb' {n : Nat} (start len : Nat) (x : BitVec n) :
    BitVec len :=
  BitVec.ofNat len (Nat.shiftRight x.toNat start)

noncomputable def bvExtractLsb {n : Nat} (hi lo : Nat) (x : BitVec n) :
    BitVec (hi - lo + 1) :=
  bvExtractLsb' lo (hi - lo + 1) x

noncomputable def bvToInt {n : Nat} (x : BitVec n) : Int :=
  if 2 * x.toNat < Nat.pow 2 n then
    Int.ofNat x.toNat
  else
    Int.ofNat x.toNat - Int.ofNat (Nat.pow 2 n)

noncomputable def bvOfInt (n : Nat) (i : Int) : BitVec n :=
  BitVec.ofNat n (intEmod i (Int.ofNat (Nat.pow 2 n))).toNat

noncomputable def bvZeroExtend {w : Nat} (v : Nat) (x : BitVec w) : BitVec v :=
  BitVec.ofNat v x.toNat

noncomputable def bvSignExtend {w : Nat} (v : Nat) (x : BitVec w) : BitVec v :=
  bvOfInt v (bvToInt x)

noncomputable def truncateBits (w : IntWidth) (value : BitVec 128) :
    BitVec 128 :=
  let low := bvExtractLsb (w.bitWidth - 1) 0 value
  bvZeroExtend 128 low

noncomputable def signExtendBits (w : IntWidth) (value : BitVec 128) : Int :=
  let low := bvExtractLsb (w.bitWidth - 1) 0 value
  bvToInt (bvSignExtend 128 low)

noncomputable def bvAnd (x y : BitVec 128) : BitVec 128 :=
  BitVec.ofNat 128 (Nat.land x.toNat y.toNat)

noncomputable def bvOr (x y : BitVec 128) : BitVec 128 :=
  BitVec.ofNat 128 (Nat.lor x.toNat y.toNat)

noncomputable def bvXor (x y : BitVec 128) : BitVec 128 :=
  BitVec.ofNat 128 (Nat.xor x.toNat y.toNat)

noncomputable def signedMinInt : IntWidth → Int
  | .i8 => Neg.neg (HPow.hPow (2 : Int) 7)
  | .i16 => Neg.neg (HPow.hPow (2 : Int) 15)
  | .i32 => Neg.neg (HPow.hPow (2 : Int) 31)
  | .i64 => Neg.neg (HPow.hPow (2 : Int) 63)
  | .i128 => Neg.neg (HPow.hPow (2 : Int) 127)
  | .isize => Neg.neg (HPow.hPow (2 : Int) 63)

inductive FaultKind where
  | undefined
  | unsupported

structure ScalarVal where
  width : IntWidth
  signed : Bool
  bits : BitVec 128

noncomputable def ScalarVal.wf (v : ScalarVal) : Bool :=
  truncateBits v.width v.bits == v.bits

noncomputable def decodeScalar (sv : ScalarVal) : Int :=
  let trunc := truncateBits sv.width sv.bits
  if sv.signed then
    signExtendBits sv.width trunc
  else
    Int.ofNat trunc.toNat

noncomputable def truncateScalar (w : IntWidth) (s : Bool) (value : Int) :
    Except FaultKind (ScalarVal × Bool) :=
  if s then
    let wrapped := bvToInt (bvOfInt 128 value)
    if decide (wrapped < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (wrapped ≥ HPow.hPow (2 : Int) 127) then
      .error .unsupported
    else
      let raw := bvOfInt 128 wrapped
      let trunc := truncateBits w raw
      let decoded := signExtendBits w trunc
      .ok (⟨w, s, trunc⟩, decoded != wrapped)
  else
    let raw := bvOfInt 128 value
    let trunc := truncateBits w raw
    .ok (⟨w, s, trunc⟩, trunc != raw)

/-- Reduced `MirTy` (upstream also has `never`, `enum`, `tuple`, pointers). -/
inductive MirTy where
  | bool
  | int (w : IntWidth) (signed : Bool)
  | unit

noncomputable def MirTy.beq : MirTy → MirTy → Bool
  | .bool, .bool => true
  | .int w₁ s₁, .int w₂ s₂ => IntWidth.beq w₁ w₂ && (s₁ == s₂)
  | .unit, .unit => true
  | _, _ => false

/-- Reduced `Val` (upstream also has `ptr`, `enumVal`, `tuple`, `bytes`). -/
inductive Val where
  | scalar (v : ScalarVal)
  | bool (b : Bool)
  | unit

noncomputable def Val.ty? : Val → Option MirTy
  | .scalar sv => if sv.wf then some (.int sv.width sv.signed) else none
  | .bool _ => some .bool
  | .unit => some .unit

noncomputable def checkVal (v : Val) (ty : MirTy) : Bool :=
  match v.ty? with
  | some vTy => MirTy.beq vTy ty
  | none => false

noncomputable def evalShiftOp (op : BinOp) (w : IntWidth) (s : Bool)
    (l r : Int) : Except FaultKind Val :=
  let amount := intEmod r (Int.ofNat w.bitWidth)
  let overflow := amount != r
  let result := match op with
    | .shl | .shlUnchecked => intShiftLeft l amount.toNat
    | _ => intShiftRight l amount.toNat
  match truncateScalar w s result with
  | .error k => .error k
  | .ok (res, _) =>
    if overflow && op.isUnchecked then
      .error .undefined
    else
      .ok (.scalar res)

noncomputable def evalArithOp (op : BinOp) (w : IntWidth) (s : Bool)
    (l r : Int) : Except FaultKind Val :=
  let isDivOrRem := match op with | .div | .rem => true | _ => false
  if isDivOrRem && r == 0 then
    .error .undefined
  else if s && isDivOrRem && (l == signedMinInt w && r == Neg.neg 1) then
    .error .undefined
  else
    let res? : Option Int := match op with
      | .add | .addUnchecked => some (l + r)
      | .sub | .subUnchecked => some (l - r)
      | .mul | .mulUnchecked => some (l * r)
      | .div => some (intTdiv l r)
      | .rem => some (intTmod l r)
      | _ => none
    match res? with
    | none => .error .unsupported
    | some result =>
      let hostOverflow : Bool :=
        if s then
          decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||
            decide (result ≥ HPow.hPow (2 : Int) 127)
        else
          decide (result < 0) || decide (result ≥ HPow.hPow (2 : Int) 128)
      match truncateScalar w s result with
      | .error k => .error k
      | .ok (val, lossy) =>
        if (hostOverflow || lossy) && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar val)

noncomputable def evalBinOp (op : BinOp) (lhs rhs : Val) :
    Except FaultKind Val :=
  match lhs, rhs with
  | .scalar l, .scalar r =>
    let lInt := decodeScalar l
    let rInt := decodeScalar r
    let w := l.width
    let s := l.signed
    if op.isShift then
      evalShiftOp op w s lInt rInt
    else if !(IntWidth.beq l.width r.width && (l.signed == r.signed)) then
      .error .unsupported
    else
      match op with
      | .eq => .ok (.bool (lInt == rInt))
      | .ne => .ok (.bool (lInt != rInt))
      | .lt => .ok (.bool (decide (lInt < rInt)))
      | .le => .ok (.bool (decide (lInt ≤ rInt)))
      | .gt => .ok (.bool (decide (lInt > rInt)))
      | .ge => .ok (.bool (decide (lInt ≥ rInt)))
      | .bitAnd =>
        let lb := truncateBits w l.bits
        let rb := truncateBits r.width r.bits
        .ok (.scalar ⟨w, s, truncateBits w (bvAnd lb rb)⟩)
      | .bitOr =>
        let lb := truncateBits w l.bits
        let rb := truncateBits r.width r.bits
        .ok (.scalar ⟨w, s, truncateBits w (bvOr lb rb)⟩)
      | .bitXor =>
        let lb := truncateBits w l.bits
        let rb := truncateBits r.width r.bits
        .ok (.scalar ⟨w, s, truncateBits w (bvXor lb rb)⟩)
      | .add | .sub | .mul | .div | .rem
      | .addUnchecked | .subUnchecked | .mulUnchecked =>
        evalArithOp op w s lInt rInt
      | _ => .error .unsupported
  | .bool l, .bool r =>
    match op with
    | .eq => .ok (.bool (l == r))
    | .ne => .ok (.bool (l != r))
    | .lt => .ok (.bool (!l && r))
    | .le => .ok (.bool (!l || r))
    | .gt => .ok (.bool (l && !r))
    | .ge => .ok (.bool (l || !r))
    | .bitAnd => .ok (.bool (l && r))
    | .bitOr => .ok (.bool (l || r))
    | .bitXor => .ok (.bool (bne l r))
    | _ => .error .unsupported
  | _, _ => .error .unsupported

/-- Spec-side helpers in the style of an Anneal `Spec.lean`: canonical
truncated scalar constructors and wrapping binary-operator denotations. -/
noncomputable def constScalar (w : IntWidth) (s : Bool) (n : Nat) : ScalarVal :=
  ⟨w, s, truncateBits w (BitVec.ofNat 128 n)⟩
noncomputable def u32Sym (x : BitVec 32) : ScalarVal := constScalar .i32 false x.toNat
noncomputable def i32Sym (x : BitVec 32) : ScalarVal := constScalar .i32 true x.toNat
noncomputable def usizeSym (x : BitVec 64) : ScalarVal := constScalar .isize false x.toNat
noncomputable def binAdd (l r : ScalarVal) : ScalarVal :=
  ⟨l.width, l.signed, truncateBits l.width (bvOfInt 128 (decodeScalar l + decodeScalar r))⟩
noncomputable def binSub (l r : ScalarVal) : ScalarVal :=
  ⟨l.width, l.signed, truncateBits l.width (bvOfInt 128 (decodeScalar l - decodeScalar r))⟩
noncomputable def binMul (l r : ScalarVal) : ScalarVal :=
  ⟨l.width, l.signed, truncateBits l.width (bvOfInt 128 (decodeScalar l * decodeScalar r))⟩
noncomputable def binShlConst (l : ScalarVal) (k : Nat) : ScalarVal :=
  ⟨l.width, l.signed, truncateBits l.width (bvOfInt 128 (intShiftLeft (decodeScalar l) k))⟩
noncomputable def binShrConst (l : ScalarVal) (k : Nat) : ScalarVal :=
  ⟨l.width, l.signed, truncateBits l.width (bvOfInt 128 (intShiftRight (decodeScalar l) k))⟩

end M

/-! ## 1. Barrier W1 — `signExtendBits` on symbolic signed scalars

Measured (Lean 4.34.1, default `maxHeartbeats 200000`, standalone file = §0 +
one goal): `decodeScalar (i32Sym x) = x.toInt := by rfl` and
`decide (decodeScalar (i32Sym x) > 0) = decide (x.toInt > 0) := by rfl` both end
in `(deterministic) timeout at whnf` after ~16 s, with `set_option diagnostics
true` attributing the work to structural `Nat.pow`/`Nat.rec` unfolding
(`Nat.rec` ↦ 78,661, `Nat.pow` ↦ 19,330, `Add.add` ↦ 18,056,
`IntWidth.byteSize` ↦ 2,600 within 20,000 heartbeats), whereas the closed
instance is decided instantly. Cure without touching `trusted/`: prove once (in
untrusted code) that the trusted definition equals a fast form, then rewrite. -/

namespace M

/-- Untrusted fast form of `signExtendBits`: two's-complement value of the low
`w.bitWidth` bits, via Lean core `BitVec.setWidth` / `BitVec.toInt`. -/
noncomputable def signExtendBitsFast (w : IntWidth) (value : BitVec 128) : Int :=
  (value.setWidth w.bitWidth).toInt

theorem bitVec_eq_of_toNat_eq {n : Nat} {a b : BitVec n} (h : a.toNat = b.toNat) :
    a = b :=
  BitVec.eq_of_toNat_eq h

theorem bvToInt_eq_toInt {n : Nat} (x : BitVec n) : bvToInt x = x.toInt := by
  unfold bvToInt BitVec.toInt
  rfl

theorem intEmod_eq_emod (a b : Int) : intEmod a b = a % b := by
  cases a <;> rfl

theorem pow128_eq : Nat.pow 2 128 = 340282366920938463463374607431768211456 := by
  decide

/-- `bvOfInt 128` followed by `bvToInt` is the identity on `[-2^127, 2^127)`. -/
theorem bvToInt_bvOfInt_128_of_range (i : Int)
    (h1 : -(170141183460469231731687303715884105728 : Int) ≤ i)
    (h2 : i < 170141183460469231731687303715884105728) :
    bvToInt (bvOfInt 128 i) = i := by
  unfold bvToInt bvOfInt
  rw [intEmod_eq_emod, pow128_eq, BitVec.toNat_ofNat]
  have hpow : (2 : Nat) ^ 128 = 340282366920938463463374607431768211456 := by decide
  rw [hpow]
  simp only [Int.ofNat_eq_natCast]
  split <;> omega

theorem toInt_range_of_le {n : Nat} (x : BitVec n) (hn : n ≤ 128) :
    -(170141183460469231731687303715884105728 : Int) ≤ x.toInt ∧
      x.toInt < 170141183460469231731687303715884105728 := by
  have hx : x.toNat < 2 ^ n := x.isLt
  have hp : 2 ^ n ≤ 2 ^ 128 := Nat.pow_le_pow_right (by decide) hn
  have hpow : (2 : Nat) ^ 128 = 340282366920938463463374607431768211456 := by decide
  rw [hpow] at hp
  unfold BitVec.toInt
  split <;> omega

theorem signExtendBits_eq_fast (w : IntWidth) (v : BitVec 128) :
    signExtendBits w v = signExtendBitsFast w v := by
  have hw : w.bitWidth - 1 - 0 + 1 ≤ 128 := by cases w <;> decide
  unfold signExtendBits bvSignExtend signExtendBitsFast
  dsimp only
  rw [bvToInt_eq_toInt (bvExtractLsb (w.bitWidth - 1) 0 v)]
  have hr := toInt_range_of_le (bvExtractLsb (w.bitWidth - 1) 0 v) hw
  rw [bvToInt_bvOfInt_128_of_range _ hr.1 hr.2]
  cases w <;> simp [BitVec.toInt, bvExtractLsb, bvExtractLsb', IntWidth.bitWidth,
    IntWidth.byteSize, BitVec.toNat_setWidth, Nat.shiftRight_zero]

end M

/-! ## 2. Barrier W2 — `ScalarVal.wf` in `writePlace`/`checkVal`

`writePlace` (MirSemantics L1213-1224) first evaluates `checkVal val dstTy`,
and `Val.ty?` (L497-505) tests `sv.wf = (truncateBits w bits == bits)`. For a
symbolic payload `bits = truncateBits w e` this `BEq (BitVec 128)` test does not
reduce by `rfl` (measured: immediate "not definitionally equal", both on the
isolated `checkVal` goal and on a whole-body `run` over the real
`Trusted.MirSemantics`). Cure: `truncateBits_idem` + `scalarWf_truncateBits`,
and an untrusted `checkValFast` that omits the `wf` test, equal to `checkVal`
whenever the value is well formed. -/

namespace M

theorem truncateBits_idem_width (w : IntWidth) (x : BitVec 128)
    (h_le : 2 ^ w.bitWidth ≤ 2 ^ 128) :
    truncateBits w (truncateBits w x) = truncateBits w x := by
  let b : BitVec (w.bitWidth - 1 - 0 + 1) := bvExtractLsb (w.bitWidth - 1) 0 x
  have h_bw : w.bitWidth - 1 - 0 + 1 = w.bitWidth := by cases w <;> rfl
  have hb : (bvZeroExtend 128 b).toNat = b.toNat := by
    change Nat.mod b.toNat (Nat.pow 2 128) = b.toNat
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_lt_of_le b.isLt (by rw [h_bw]; exact h_le)
  have hb_eq : BitVec.ofNat (w.bitWidth - 1 - 0 + 1)
      (Nat.shiftRight (bvZeroExtend 128 b).toNat 0) = b := by
    apply bitVec_eq_of_toNat_eq
    change Nat.mod (Nat.shiftRight (bvZeroExtend 128 b).toNat 0)
      (Nat.pow 2 (w.bitWidth - 1 - 0 + 1)) = b.toNat
    have h_shr : Nat.shiftRight (bvZeroExtend 128 b).toNat 0 =
        (bvZeroExtend 128 b).toNat := rfl
    rw [h_shr, hb]
    exact Nat.mod_eq_of_lt b.isLt
  change bvZeroExtend 128 (BitVec.ofNat (w.bitWidth - 1 - 0 + 1)
      (Nat.shiftRight (bvZeroExtend 128 b).toNat 0)) = bvZeroExtend 128 b
  rw [hb_eq]

theorem truncateBits_idem (w : IntWidth) (x : BitVec 128) :
    truncateBits w (truncateBits w x) = truncateBits w x := by
  apply truncateBits_idem_width
  cases w <;> decide

@[simp]
theorem scalarWf_truncateBits (w : IntWidth) (s : Bool) (x : BitVec 128) :
    ScalarVal.wf ⟨w, s, truncateBits w x⟩ = true := by
  unfold ScalarVal.wf
  dsimp only
  rw [truncateBits_idem]
  exact beq_self_eq_true _

theorem intWidth_beq_refl (w : IntWidth) : IntWidth.beq w w = true := by
  cases w <;> rfl

theorem checkVal_truncScalar (w : IntWidth) (s : Bool) (x : BitVec 128) :
    checkVal (.scalar ⟨w, s, truncateBits w x⟩) (.int w s) = true := by
  simp only [checkVal, Val.ty?, scalarWf_truncateBits, ite_true]
  cases w <;> cases s <;> rfl

/-- Untrusted fast check: identical to `checkVal` except that the
`ScalarVal.wf` test is dropped for scalars. -/
noncomputable def checkValFast (v : Val) (ty : MirTy) : Bool :=
  match v with
  | .scalar sv => MirTy.beq (.int sv.width sv.signed) ty
  | other => checkVal other ty

theorem checkVal_eq_fast_of_wf (sv : ScalarVal) (ty : MirTy) (h : sv.wf = true) :
    checkVal (.scalar sv) ty = checkValFast (.scalar sv) ty := by
  simp only [checkVal, checkValFast, Val.ty?, h, ite_true]

/-- error: Tactic `rfl` failed: The left-hand side -/
#guard_msgs (substring := true) in
-- W2 receipt: with a symbolic payload the trusted check is not closed by `rfl`
-- (immediate definitional mismatch); `checkVal_truncScalar` proves it and the
-- fast check closes by `rfl` (next example).
example (x : BitVec 128) :
    checkVal (.scalar ⟨.i32, false, truncateBits .i32 x⟩) (.int .i32 false) = true := by
  rfl

example (x : BitVec 128) :
    checkValFast (.scalar ⟨.i32, false, truncateBits .i32 x⟩) (.int .i32 false) = true :=
  rfl

/-! ### W1 consumers (need `truncateBits_idem`) -/

theorem decode_const_i32_zero : decodeScalar (constScalar .i32 true 0) = 0 := by
  decide

/-- Closed instance: decided by kernel evaluation (`0xFFFF_FFF1 ↦ -15`). -/
theorem decode_i32_neg15 : decodeScalar (i32Sym 0xFFFFFFF1#32) = -15 := by
  decide

theorem truncate_i32_setWidth (x : BitVec 32) :
    (truncateBits .i32 (BitVec.ofNat 128 x.toNat)).setWidth 32 = x := by
  apply bitVec_eq_of_toNat_eq
  have hx : x.toNat < 2 ^ 32 := x.isLt
  simp [truncateBits, bvZeroExtend, bvExtractLsb, bvExtractLsb', BitVec.toNat_setWidth,
    IntWidth.bitWidth, IntWidth.byteSize, Nat.shiftRight_zero]
  omega

/-- W1 cure: universal signed decode of a symbolic `i32`, proved by rewriting
with `truncateBits_idem` and the untrusted `signExtendBits_eq_fast`. -/
theorem decode_i32Sym_eq_toInt (x : BitVec 32) : decodeScalar (i32Sym x) = x.toInt := by
  unfold decodeScalar i32Sym constScalar
  dsimp only
  rw [truncateBits_idem]
  change signExtendBits .i32 (truncateBits .i32 (BitVec.ofNat 128 x.toNat)) = x.toInt
  rw [signExtendBits_eq_fast]
  unfold signExtendBitsFast
  exact congrArg BitVec.toInt (truncate_i32_setWidth x)

/-- error: (deterministic) timeout at `whnf`, maximum number of heartbeats (4000) has been reached -/
#guard_msgs (substring := true) in
-- W1 receipt: `rfl` on the statement of `decode_i32Sym_eq_toInt` exhausts the
-- heartbeat budget in `whnf` (bounded to 4000 here; with the default 200000 the
-- same timeout takes ~16 s).
set_option maxHeartbeats 4000 in
example (x : BitVec 32) : decodeScalar (i32Sym x) = x.toInt := by
  rfl

/-- Specification-level consequence (`DataFormat::from_window_bits`, `w > 0`). -/
theorem gt_zero_i32Sym (x : BitVec 32) :
    decide (decodeScalar (i32Sym x) > decodeScalar (constScalar .i32 true 0)) =
      decide (x.toInt > 0) := by
  rw [decode_i32Sym_eq_toInt, decode_const_i32_zero]

/-- Alternative that never reduces `signExtendBits` on symbolic input: a
specification that mirrors the trusted comparison term syntactically closes by
`rfl` (the stuck subterm `decodeScalar (i32Sym x)` occurs identically on both
sides). -/
theorem gt_mirror_rfl (x : BitVec 32) :
    evalBinOp .gt (.scalar (i32Sym x)) (.scalar (constScalar .i32 true 0)) =
      .ok (.bool (decide (decodeScalar (i32Sym x) > decodeScalar (constScalar .i32 true 0)))) :=
  rfl

end M

/-! ## 3. Barrier W3 — `evalArithOp` / `evalShiftOp` / `truncateScalar`

For wrapping `add`/`sub`/`mul` the trusted evaluator still computes
`hostOverflow` and the `lossy` flag and branches on
`(hostOverflow || lossy) && op.isUnchecked`; `Bool.and`/`Bool.or` match on their
*first* argument, so the symbolic `hostOverflow` blocks reduction even though
`op.isUnchecked = false` (measured: immediate "not definitionally equal" for
`u32 add` and `usize sub`). Signed results additionally pass through the
`truncateScalar` range test on `bvToInt (bvOfInt 128 value)`, which ends in the
same structural `Nat.pow` whnf timeout as W1 (measured: `i32 shl 1`, ~22 s).
Unsigned shifts by a constant reduce by `rfl` unchanged (control). Cure:
`truncateScalar_total` (via `bvToInt_128_in_range` and `bvOfInt_bvToInt_128`)
and an untrusted `evalBinOpFast` proved equal to `evalBinOp`. -/

namespace M

theorem bvToInt_128_in_range (x : BitVec 128) :
    (decide (bvToInt x < Neg.neg (HPow.hPow (2 : Int) 127)) ||
     decide (bvToInt x ≥ HPow.hPow (2 : Int) 127)) = false := by
  have hx : x.toNat < 2 ^ 128 := x.isLt
  unfold bvToInt
  change (decide ((if 2 * x.toNat < 2 ^ 128 then (x.toNat : Int)
      else (x.toNat : Int) - ((2 ^ 128 : Nat) : Int)) < -(2 ^ 127 : Int)) ||
    decide ((if 2 * x.toNat < 2 ^ 128 then (x.toNat : Int)
      else (x.toNat : Int) - ((2 ^ 128 : Nat) : Int)) ≥ (2 ^ 127 : Int))) = false
  split <;> rename_i h
  · have h1 : ¬ ((x.toNat : Int) < -(2 ^ 127 : Int)) := by omega
    have h2 : ¬ ((x.toNat : Int) ≥ (2 ^ 127 : Int)) := by omega
    rw [decide_eq_false h1, decide_eq_false h2]; rfl
  · have h1 : ¬ ((x.toNat : Int) - ((2 ^ 128 : Nat) : Int) < -(2 ^ 127 : Int)) := by omega
    have h2 : ¬ ((x.toNat : Int) - ((2 ^ 128 : Nat) : Int) ≥ (2 ^ 127 : Int)) := by omega
    rw [decide_eq_false h1, decide_eq_false h2]; rfl

theorem intEmod_sub_self (N k : Nat) (hk : k < N) :
    (intEmod ((k : Int) - (N : Int)) (Int.ofNat N)).toNat % N = k := by
  rw [intEmod_eq_emod]
  have h : ((k : Int) - (N : Int)) % (Int.ofNat N) = (k : Int) := by
    have h1 : (k : Int) - (N : Int) = (k : Int) + (N : Int) * (-1) := by omega
    have h2 : (k : Int) % (N : Int) = (k : Int) := by
      change Int.ofNat (k % N) = Int.ofNat k
      rw [Nat.mod_eq_of_lt hk]
    change ((k : Int) - (N : Int)) % (N : Int) = (k : Int)
    rw [h1, Int.add_mul_emod_self_left, h2]
  rw [h]
  exact Nat.mod_eq_of_lt hk

theorem bvOfInt_bvToInt_128 (x : BitVec 128) : bvOfInt 128 (bvToInt x) = x := by
  have hx : x.toNat < 2 ^ 128 := x.isLt
  apply bitVec_eq_of_toNat_eq
  unfold bvOfInt bvToInt
  split <;> rename_i h
  · unfold intEmod
    change (x.toNat % (2 ^ 128)) % (2 ^ 128) = x.toNat
    rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hx]
  · exact intEmod_sub_self (2 ^ 128) x.toNat hx

theorem truncateScalar_signed_ok (w : IntWidth) (value : Int) :
    truncateScalar w true value =
      .ok (⟨w, true, truncateBits w (bvOfInt 128 value)⟩,
        signExtendBits w (truncateBits w (bvOfInt 128 value)) !=
          bvToInt (bvOfInt 128 value)) := by
  unfold truncateScalar
  dsimp only
  rw [bvToInt_128_in_range (bvOfInt 128 value)]
  change Except.ok
      (ScalarVal.mk w true (truncateBits w (bvOfInt 128 (bvToInt (bvOfInt 128 value)))),
        signExtendBits w (truncateBits w (bvOfInt 128 (bvToInt (bvOfInt 128 value)))) !=
          bvToInt (bvOfInt 128 value)) = _
  rw [bvOfInt_bvToInt_128 (bvOfInt 128 value)]

/-- `truncateScalar` never faults and always returns the wrapped payload; only
the `lossy` flag stays symbolic. -/
theorem truncateScalar_total (w : IntWidth) (s : Bool) (value : Int) :
    ∃ lossy : Bool,
      truncateScalar w s value = .ok (⟨w, s, truncateBits w (bvOfInt 128 value)⟩, lossy) := by
  cases s with
  | false => exact ⟨_, rfl⟩
  | true => exact ⟨_, truncateScalar_signed_ok w value⟩

/-- Untrusted fast evaluator: wrapping `shl`/`shr`/`add`/`sub`/`mul` return the
truncated payload directly; every other case defers to the trusted `evalBinOp`. -/
noncomputable def evalBinOpFast (op : BinOp) (lhs rhs : Val) : Except FaultKind Val :=
  match lhs, rhs with
  | .scalar l, .scalar r =>
    let lInt := decodeScalar l
    let rInt := decodeScalar r
    let w := l.width
    let s := l.signed
    match op with
    | .shl =>
      .ok (.scalar ⟨w, s, truncateBits w (bvOfInt 128
        (intShiftLeft lInt (intEmod rInt (Int.ofNat w.bitWidth)).toNat))⟩)
    | .shr =>
      .ok (.scalar ⟨w, s, truncateBits w (bvOfInt 128
        (intShiftRight lInt (intEmod rInt (Int.ofNat w.bitWidth)).toNat))⟩)
    | .add =>
      if !(IntWidth.beq l.width r.width && (l.signed == r.signed)) then .error .unsupported
      else .ok (.scalar ⟨w, s, truncateBits w (bvOfInt 128 (lInt + rInt))⟩)
    | .sub =>
      if !(IntWidth.beq l.width r.width && (l.signed == r.signed)) then .error .unsupported
      else .ok (.scalar ⟨w, s, truncateBits w (bvOfInt 128 (lInt - rInt))⟩)
    | .mul =>
      if !(IntWidth.beq l.width r.width && (l.signed == r.signed)) then .error .unsupported
      else .ok (.scalar ⟨w, s, truncateBits w (bvOfInt 128 (lInt * rInt))⟩)
    | other => evalBinOp other (.scalar l) (.scalar r)
  | otherL, otherR => evalBinOp op otherL otherR

theorem evalBinOp_eq_fast (op : BinOp) (lhs rhs : Val) :
    evalBinOp op lhs rhs = evalBinOpFast op lhs rhs := by
  cases lhs <;> cases rhs <;> try rfl
  case scalar.scalar l r =>
    cases op with
    | shl =>
      unfold evalBinOp evalShiftOp evalBinOpFast
      simp only [BinOp.isShift, BinOp.isUnchecked, ite_true]
      rcases truncateScalar_total l.width l.signed
        (intShiftLeft (decodeScalar l)
          (intEmod (decodeScalar r) (Int.ofNat l.width.bitWidth)).toNat) with ⟨lossy, htr⟩
      rw [htr]
      simp only [Bool.and_false, Bool.false_eq_true, ite_false]
    | shr =>
      unfold evalBinOp evalShiftOp evalBinOpFast
      simp only [BinOp.isShift, BinOp.isUnchecked, ite_true]
      rcases truncateScalar_total l.width l.signed
        (intShiftRight (decodeScalar l)
          (intEmod (decodeScalar r) (Int.ofNat l.width.bitWidth)).toNat) with ⟨lossy, htr⟩
      rw [htr]
      simp only [Bool.and_false, Bool.false_eq_true, ite_false]
    | add =>
      unfold evalBinOp evalArithOp evalBinOpFast
      dsimp only [BinOp.isShift, BinOp.isUnchecked]
      cases (IntWidth.beq l.width r.width && (l.signed == r.signed))
      · rfl
      · rcases truncateScalar_total l.width l.signed (decodeScalar l + decodeScalar r)
          with ⟨lossy, htr⟩
        simp only [Bool.not_true, Bool.false_eq_true, ite_false, htr, Bool.and_false,
          Bool.false_and]
    | sub =>
      unfold evalBinOp evalArithOp evalBinOpFast
      dsimp only [BinOp.isShift, BinOp.isUnchecked]
      cases (IntWidth.beq l.width r.width && (l.signed == r.signed))
      · rfl
      · rcases truncateScalar_total l.width l.signed (decodeScalar l - decodeScalar r)
          with ⟨lossy, htr⟩
        simp only [Bool.not_true, Bool.false_eq_true, ite_false, htr, Bool.and_false,
          Bool.false_and]
    | mul =>
      unfold evalBinOp evalArithOp evalBinOpFast
      dsimp only [BinOp.isShift, BinOp.isUnchecked]
      cases (IntWidth.beq l.width r.width && (l.signed == r.signed))
      · rfl
      · rcases truncateScalar_total l.width l.signed (decodeScalar l * decodeScalar r)
          with ⟨lossy, htr⟩
        simp only [Bool.not_true, Bool.false_eq_true, ite_false, htr, Bool.and_false,
          Bool.false_and]
    | _ => rfl

/-- 32-bit wrapping add over symbolic operands (e.g. Adler-32 `u16 → u32` folds). -/
theorem add_u32_fast (a b : BitVec 32) :
    evalBinOp .add (.scalar (u32Sym a)) (.scalar (u32Sym b)) =
      .ok (.scalar (binAdd (u32Sym a) (u32Sym b))) := by
  rw [evalBinOp_eq_fast]; rfl

/-- 64-bit wrapping sub (e.g. `out_len - out_pos` slack guards). -/
theorem sub_usize_fast (a b : BitVec 64) :
    evalBinOp .sub (.scalar (usizeSym a)) (.scalar (usizeSym b)) =
      .ok (.scalar (binSub (usizeSym a) (usizeSym b))) := by
  rw [evalBinOp_eq_fast]; rfl

/-- 32-bit wrapping mul by a constant (e.g. `(v >> 16) * 15` modular folds). -/
theorem mul_u32_fast (a : BitVec 32) :
    evalBinOp .mul (.scalar (u32Sym a)) (.scalar (constScalar .i32 false 15)) =
      .ok (.scalar (binMul (u32Sym a) (constScalar .i32 false 15))) := by
  rw [evalBinOp_eq_fast]; rfl

/-- Signed `i32` shift-left by a constant (e.g. Kraft `left << 1`). -/
theorem shl_i32_fast (l : BitVec 32) :
    evalBinOp .shl (.scalar (i32Sym l)) (.scalar (constScalar .i32 true 1)) =
      .ok (.scalar (binShlConst (i32Sym l) 1)) := by
  rw [evalBinOp_eq_fast]; rfl

/-- Signed Kraft step `(left << 1) - count` composed from two fast steps. -/
theorem kraft_step_i32_fast (l c : BitVec 32) :
    evalBinOp .sub (.scalar (binShlConst (i32Sym l) 1)) (.scalar (i32Sym c)) =
      .ok (.scalar (binSub (binShlConst (i32Sym l) 1) (i32Sym c))) := by
  rw [evalBinOp_eq_fast]; rfl

/-- Control: unsigned shift by a constant reduces with the trusted evaluator. -/
theorem shr_u32_trusted_rfl (e : BitVec 32) :
    evalBinOp .shr (.scalar (u32Sym e)) (.scalar (constScalar .i32 true 16)) =
      .ok (.scalar (binShrConst (u32Sym e) 16)) :=
  rfl

/-- error: Tactic `rfl` failed: The left-hand side -/
#guard_msgs (substring := true) in
-- W3 receipt (unsigned wrapping add): immediate definitional mismatch.
example (a b : BitVec 32) :
    evalBinOp .add (.scalar (u32Sym a)) (.scalar (u32Sym b)) =
      .ok (.scalar (binAdd (u32Sym a) (u32Sym b))) := by
  rfl

/-- error: (deterministic) timeout at `whnf`, maximum number of heartbeats (4000) has been reached -/
#guard_msgs (substring := true) in
-- W3 receipt (signed shift): `whnf` timeout (default budget: ~22 s).
set_option maxHeartbeats 4000 in
example (l : BitVec 32) :
    evalBinOp .shl (.scalar (i32Sym l)) (.scalar (constScalar .i32 true 1)) =
      .ok (.scalar (binShlConst (i32Sym l) 1)) := by
  rfl

end M

/-! ## 4. Mutation oracle — `huff_entry_len` (`entry >> 16`) mutated to `>> 15`

Measured on the real `Trusted.MirSemantics` (31b91b61b) with the untrusted
`fastRun`: the mutated body against the unmutated specification is rejected by
`rfl` with an immediate "Type mismatch"/"not definitionally equal" (≈0.3 s above
the 0.51 s file baseline), not by a heartbeat timeout; the same holds for the
single-step reduction below. A concrete witness refutes the mutant by kernel
evaluation in milliseconds. -/

namespace M

noncomputable def okBitsNat : Except FaultKind Val → Nat
  | .ok (.scalar sv) => sv.bits.toNat
  | _ => 0

theorem shr16_at_0x18000 :
    okBitsNat (evalBinOp .shr (.scalar (u32Sym 0x18000#32))
      (.scalar (constScalar .i32 true 16))) = 1 := by
  decide

theorem shr15_at_0x18000 :
    okBitsNat (evalBinOp .shr (.scalar (u32Sym 0x18000#32))
      (.scalar (constScalar .i32 true 15))) = 3 := by
  decide

theorem spec16_at_0x18000 :
    okBitsNat (.ok (.scalar (binShrConst (u32Sym 0x18000#32) 16))) = 1 := by
  decide

/-- The mutant is refuted universally by one concrete witness. -/
theorem huffEntryLen_mutation_refuted :
    ¬ ∀ e : BitVec 32,
      evalBinOp .shr (.scalar (u32Sym e)) (.scalar (constScalar .i32 true 15)) =
        .ok (.scalar (binShrConst (u32Sym e) 16)) := by
  intro h
  have h1 := congrArg okBitsNat (h 0x18000#32)
  rw [shr15_at_0x18000, spec16_at_0x18000] at h1
  exact absurd h1 (by decide)

/-- error: Tactic `rfl` failed: The left-hand side -/
#guard_msgs (substring := true) in
-- Mutation receipt: the symbolic `rfl` attempt on the mutant fails with an
-- immediate definitional mismatch (no heartbeat bound needed).
example (e : BitVec 32) :
    evalBinOp .shr (.scalar (u32Sym e)) (.scalar (constScalar .i32 true 15)) =
      .ok (.scalar (binShrConst (u32Sym e) 16)) := by
  rfl

end M


/-! ## 5. Axiom receipts -/

end MirTransferProbe
