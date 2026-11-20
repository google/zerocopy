-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted.MirAst
import Trusted.MirModel

namespace Trusted.MirSemantics

open Trusted.MirAst

/-!
# Scalar Arithmetic and Operator Semantics (`Trusted.MirSemantics.Ops`)

Pure bitvector/integer helpers, scalar decoding and truncation, and binary and
unary operator evaluation rules for $M_{\text{anneal}}$.
-/

/-- Euclidean integer modulo (`x % m` with `m > 0`) over
`Init.Data.Int.Basic`, matching Rust's `rem_euclid` used for shift-amount
masking in `compiler/rustc_const_eval/src/interpret/operator.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "let rem = shift_amount.rem_euclid(l_bits.into());" -/
noncomputable def intEmod : Int → Int → Int
  | .ofNat m, n => .ofNat (Nat.mod m (Int.natAbs n))
  | .negSucc m, n =>
    Int.subNatNat (Int.natAbs n) (Nat.succ (Nat.mod m (Int.natAbs n)))

/-- Truncated integer division towards zero (`intTdiv`) over
`Init.Data.Int.Basic`, matching Rust's integer `/` operator
(`i128::overflowing_div` / `u128::overflowing_div` in
`compiler/rustc_const_eval/src/interpret/operator.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
noncomputable def intTdiv : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (Nat.div m n)
  | .ofNat m, .negSucc n => Int.neg (.ofNat (Nat.div m (Nat.succ n)))
  | .negSucc m, .ofNat n => Int.neg (.ofNat (Nat.div (Nat.succ m) n))
  | .negSucc m, .negSucc n => .ofNat (Nat.div (Nat.succ m) (Nat.succ n))

/-- Truncated integer remainder towards zero (`intTmod`) over
`Init.Data.Int.Basic`, matching Rust's integer `%` operator
(`i128::overflowing_rem` / `u128::overflowing_rem` in
`compiler/rustc_const_eval/src/interpret/operator.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
noncomputable def intTmod : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (Nat.mod m n)
  | .ofNat m, .negSucc n => .ofNat (Nat.mod m (Nat.succ n))
  | .negSucc m, .ofNat n => Int.neg (.ofNat (Nat.mod (Nat.succ m) n))
  | .negSucc m, .negSucc n =>
    Int.neg (.ofNat (Nat.mod (Nat.succ m) (Nat.succ n)))

/-- Arithmetic right shift on `Int` over `Init.Data.Nat.Bitwise.Basic`,
matching `l.checked_shr(shift_amount)` in
`compiler/rustc_const_eval/src/interpret/operator.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
noncomputable def intShiftRight : Int → Nat → Int
  | .ofNat n, s => .ofNat (Nat.shiftRight n s)
  | .negSucc n, s => .negSucc (Nat.shiftRight n s)

/-- Left shift on `Int` over `Init.Data.Nat.Bitwise.Basic`, matching
`l.checked_shl(shift_amount)` in
`compiler/rustc_const_eval/src/interpret/operator.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
noncomputable def intShiftLeft : Int → Nat → Int
  | .ofNat n, s => .ofNat (Nat.shiftLeft n s)
  | .negSucc n, s => .negSucc ((Nat.shiftLeft (n + 1) s) - 1)

/-- Bitwise complement (`!x = -x - 1`) on mathematical `Int`, matching
`UnOp::Not` in `compiler/rustc_const_eval/src/interpret/operator.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
noncomputable def intNot : Int → Int
  | .ofNat n => .negSucc n
  | .negSucc n => .ofNat n

/-- Extract `len` bits starting at bit `start` (`BitVec.extractLsb'`) using
only `Init.Data.BitVec.BasicAux`. -/
noncomputable def bvExtractLsb' {n : Nat} (start len : Nat) (x : BitVec n) :
    BitVec len :=
  BitVec.ofNat len (Nat.shiftRight x.toNat start)

/-- Extract bits `hi` down to `lo` inclusive (`BitVec.extractLsb`). -/
noncomputable def bvExtractLsb {n : Nat} (hi lo : Nat) (x : BitVec n) :
    BitVec (hi - lo + 1) :=
  bvExtractLsb' lo (hi - lo + 1) x

/-- Two's-complement signed integer interpretation of `BitVec n`
(`BitVec.toInt`). -/
noncomputable def bvToInt {n : Nat} (x : BitVec n) : Int :=
  if 2 * x.toNat < Nat.pow 2 n then
    Int.ofNat x.toNat
  else
    Int.ofNat x.toNat - Int.ofNat (Nat.pow 2 n)

/-- Wrap mathematical `Int` into `BitVec n` (`BitVec.ofInt`). -/
noncomputable def bvOfInt (n : Nat) (i : Int) : BitVec n :=
  BitVec.ofNat n (intEmod i (Int.ofNat (Nat.pow 2 n))).toNat

/-- Zero-extend `BitVec w` to width `v` (`BitVec.zeroExtend` for `w ≤ v`). -/
noncomputable def bvZeroExtend {w : Nat} (v : Nat) (x : BitVec w) : BitVec v :=
  BitVec.ofNat v x.toNat

/-- Sign-extend `BitVec w` to width `v` (`BitVec.signExtend`). -/
noncomputable def bvSignExtend {w : Nat} (v : Nat) (x : BitVec w) : BitVec v :=
  bvOfInt v (bvToInt x)

/-- Truncate a 128-bit bitvector to the low `w.bitWidth` bits, zero-extended
back to `BitVec 128`, matching `rustc_abi::Size::truncate`
(`compiler/rustc_abi/src/lib.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and `Miri.ABI.Size.truncate`
(`vendor/lean-miri/Miri/ABI/Size.lean`):

> "pub fn truncate(self, value: u128) -> u128" -/
noncomputable def truncateBits (w : IntWidth) (value : BitVec 128) :
    BitVec 128 :=
  let low := bvExtractLsb (w.bitWidth - 1) 0 value
  bvZeroExtend 128 low

/-- Sign-extend the low `w.bitWidth` bits of `value` to a mathematical `Int`,
matching `rustc_abi::Size::sign_extend` (`compiler/rustc_abi/src/lib.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.ABI.Size.signExtend` (`vendor/lean-miri/Miri/ABI/Size.lean`):

> "pub fn sign_extend(self, value: u128) -> i128" -/
noncomputable def signExtendBits (w : IntWidth) (value : BitVec 128) : Int :=
  let low := bvExtractLsb (w.bitWidth - 1) 0 value
  bvToInt (bvSignExtend 128 low)

/-- Bitwise AND on `BitVec 128` over `Init.Data.Nat.Bitwise.Basic`. -/
noncomputable def bvAnd (x y : BitVec 128) : BitVec 128 :=
  BitVec.ofNat 128 (Nat.land x.toNat y.toNat)

/-- Bitwise OR on `BitVec 128` over `Init.Data.Nat.Bitwise.Basic`. -/
noncomputable def bvOr (x y : BitVec 128) : BitVec 128 :=
  BitVec.ofNat 128 (Nat.lor x.toNat y.toNat)

/-- Bitwise XOR on `BitVec 128` over `Init.Data.Nat.Bitwise.Basic`. -/
noncomputable def bvXor (x y : BitVec 128) : BitVec 128 :=
  BitVec.ofNat 128 (Nat.xor x.toNat y.toNat)

/-- Minimum signed integer representable at width `w` (`-2^(w.bitWidth - 1)`),
matching `rustc_abi::Size::signed_int_min` (`compiler/rustc_abi/src/lib.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.ABI.Size.signedIntMin` (`vendor/lean-miri/Miri/ABI/Size.lean`):

> "pub fn signed_int_min(&self) -> i128" -/
noncomputable def signedMinInt (w : IntWidth) : Int :=
  Neg.neg (HPow.hPow (2 : Int) (w.bitWidth - 1))

namespace ScalarVal

/-- Check that `v.bits` fits within `v.width.bitWidth` bits
(`truncateBits v.width v.bits == v.bits`), matching `ScalarInt::check_data`
(`compiler/rustc_middle/src/ty/consts/int.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "debug_assert_eq!(self.size().truncate(self.data), { self.data }, ...);" -/
noncomputable def wf (v : ScalarVal) : Bool :=
  truncateBits v.width v.bits == v.bits

end ScalarVal

/-- Decode the mathematical integer value of `sv` after masking to `sv.width`
bits, matching `ScalarInt::to_int` and `ScalarInt::to_uint`
(`compiler/rustc_middle/src/ty/consts/int.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.IntegerOps.decode`
(`vendor/lean-miri/Miri/Interpreter/IntegerOps.lean`). -/
noncomputable def decodeScalar (sv : ScalarVal) : Int :=
  let trunc := truncateBits sv.width sv.bits
  if sv.signed then
    signExtendBits sv.width trunc
  else
    Int.ofNat trunc.toNat

/-- Truncate mathematical integer `value` to `(w, s)` and report whether
truncation was lossy, matching `ScalarInt::truncate_from_int` and
`ScalarInt::truncate_from_uint` (`compiler/rustc_middle/src/ty/consts/int.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.IntegerOps.truncate`
(`vendor/lean-miri/Miri/Interpreter/IntegerOps.lean`):

> "pub fn truncate_from_uint(i: impl Into<u128>, size: Size) -> (Self, bool)"
> "pub fn truncate_from_int(i: impl Into<i128>, size: Size) -> (Self, bool)"

In the signed branch, `wrapped := bvToInt (bvOfInt 128 value)` always lies in
$[-2^{127}, 2^{127})$; the explicit range guard is unreachable and retained for
syntactic lockstep with `Miri.Memory.ScalarInt.truncateFromInt`. -/
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

/-- Evaluate a bit-shift operator (`.shl`, `.shr`, `.shlUnchecked`,
`.shrUnchecked`) in lockstep with
`compiler/rustc_const_eval/src/interpret/operator.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.IntegerOps.shift`
(`vendor/lean-miri/Miri/Interpreter/IntegerOps.lean`):

> "let rem = shift_amount.rem_euclid(l_bits.into());
> (rem, rem != shift_amount)"
> "if overflow && let Some(intrinsic) = throw_ub_on_overflow {
>     throw_ub!(ShiftOverflow { ... });
> }"
> (`compiler/rustc_const_eval/src/interpret/operator.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
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

/-- Evaluate an integer arithmetic operator (`.add`, `.sub`, `.mul`, `.div`,
`.rem`, `.addUnchecked`, `.subUnchecked`, `.mulUnchecked`) in lockstep with
`compiler/rustc_const_eval/src/interpret/operator.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.IntegerOps.arithmetic`
(`vendor/lean-miri/Miri/Interpreter/IntegerOps.lean`):

> "// We need a special check for overflowing Rem and Div since they are *UB*
> // on overflow, which can happen with \"int_min $OP -1\"."
> (`compiler/rustc_const_eval/src/interpret/operator.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
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

/-- Evaluate a binary operator across all 6 integer widths (`i8`..`i128`,
`isize`), signedness modes, shift operators, and booleans in lockstep with
`compiler/rustc_const_eval/src/interpret/operator.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.IntegerOps.{binary, binaryBool}`:

> "pub fn binary_op(&self, bin_op: mir::BinOp, left: &ImmTy<'tcx,
> M::Provenance>, right: &ImmTy<'tcx, M::Provenance>) -> InterpResult<'tcx,
> ImmTy<'tcx, M::Provenance>>"
> (`compiler/rustc_const_eval/src/interpret/operator.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

- Non-shift integer ops require matching `(width, signed)`.
- Shift ops (`.shl`, `.shr`, `.shlUnchecked`, `.shrUnchecked`) accept any
  integer RHS `(r.width, r.signed)`, mask the shift amount modulo `w.bitWidth`,
  fault with `.undefined` on `.shlUnchecked`/`.shrUnchecked` when `r < 0`
  or `r ≥ w.bitWidth`, and perform arithmetic right shift on signed `l`.
- Signed `.div` and `.rem` fault with `.undefined` on `INT_MIN / -1` and
  `INT_MIN % -1` as well as `r == 0`. -/
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

/-- Evaluate a unary operator (`not` and `neg`) in lockstep with
`compiler/rustc_const_eval/src/interpret/operator.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.ScalarOps.unary` / `Miri.Interpreter.IntegerOps.unary`:

> "pub fn unary_op(&self, un_op: mir::UnOp, val: &ImmTy<'tcx, M::Provenance>)
> -> InterpResult<'tcx, ImmTy<'tcx, M::Provenance>>"
> (`compiler/rustc_const_eval/src/interpret/operator.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

- `.not` on `.bool b` returns `.bool (!b)`.
- `.not` on `.scalar sv` returns bitwise complement `intNot (decodeScalar sv)`
  truncated to `(sv.width, sv.signed)`.
- `.neg` on signed `.scalar sv` returns wrapping `-decodeScalar sv`
  (`-INT_MIN == INT_MIN`); `.neg` on unsigned `.scalar sv` returns
  `.error .unsupported`. -/
noncomputable def evalUnOp (op : UnOp) (v : Val) : Except FaultKind Val :=
  match op, v with
  | .not, .bool b => .ok (.bool (!b))
  | .not, .scalar sv =>
    let integer := decodeScalar sv
    match truncateScalar sv.width sv.signed (intNot integer) with
    | .ok (res, _) => .ok (.scalar res)
    | .error k => .error k
  | .neg, .scalar sv =>
    let integer := decodeScalar sv
    if sv.signed then
      match truncateScalar sv.width sv.signed (Neg.neg integer) with
      | .ok (res, _) => .ok (.scalar res)
      | .error k => .error k
    else
      .error .unsupported
  | _, _ => .error .unsupported

end Trusted.MirSemantics
