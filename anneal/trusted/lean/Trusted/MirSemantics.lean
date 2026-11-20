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

namespace Trusted.MirSemantics

open Trusted.MirAst

/-!
# Anneal MIR Small-Step Operational Semantics (`Trusted.MirSemantics`)

## Human-Comprehension Priority

`Trusted.MirSemantics` defines Anneal's small-step operational semantics
($M_{\text{anneal}}$), the top-level execution predicates (`initState`,
`evalStep`, `Step`, `Reaches`, `ReachesResult`, `WellFormed`, `Behavior`,
`Diverges`, and `SatisfiesPost`) referenced directly by `CorrespondenceClaim`
and `FaultEquivalenceClaim` in `Trusted.Correspondence`, the per-body,
program, proof-unit, and crate verification judgments (`BodyStaticAdmitted`,
`BodyVerified`, `Specs`, `Crate`, `ProgramVerified`, `CrateTheorem`, and
`UnitTheorem`), and the Pass 1 audited claim propositions (`WpSoundnessClaim`,
`WpFaultSoundnessClaim`, and the 19 `Canary*Claim` propositions).

Human comprehension is therefore the primary design requirement for every
definition in this module:

1. **Direct, transparent mathematical meaning:** Every state transition and
   execution predicate is stated directly in terms of elementary step relations
   without clever encodings, hidden fuel parameters in top-level predicates, or
   non-obvious state invariants. A human auditor reading `WellFormed`,
   `Behavior`, `Diverges`, `SatisfiesPost`, `BodyVerified`, `ProgramVerified`,
   `CrateTheorem`, `UnitTheorem`, `WpSoundnessClaim`, or
   `WpFaultSoundnessClaim` can verify immediately that each predicate means in
   mathematical terms what it means in intuitive operational terms.
2. **Explicit fail-closed boundaries (`FaultKind`):** Any unmodeled MIR
   construct, type, or target/profile configuration steps explicitly to
   `FaultKind.unsupported`, and any modeled Rust Undefined Behavior steps
   explicitly to `FaultKind.undefined`. Both fault kinds falsify `WellFormed`.
3. **Pinned upstream citations:** Core semantic helpers and transition rules
   cite (and, for key MIR/interpreter definitions, quote verbatim) the
   corresponding implementation in `compiler/rustc_const_eval/src/interpret/`
   (`rust-lang/rust` commit `8144389c895da997dbdecaa635e41d6a50be6ffd`) and the
   Rust Reference (`rust-lang/reference` commit
   `a286e1ecb8ce193d50056e4bb042eea9b23876ef`, pinned by
   `rust-lang/rust@8144389c`'s `src/doc/reference` submodule).

## Correspondence with `rustc_const_eval::interpret` and Rust Reference

Transition rules in $M_{\text{anneal}}$ follow `rustc_const_eval::interpret`
(`rust-lang/rust` commit `8144389c895da997dbdecaa635e41d6a50be6ffd`) and Miri
(`rust-lang/miri` commit `7fa591d7d4dd9af8154becbc8332f8096f8323b1`), as
mechanized in `vendor/lean-miri`, with one intentional semantic difference:
- `Operand.move` deliberately and conservatively deinitializes non-ZST local
  storage upon evaluation (matching `lean-miri`'s opt-in
  `deinitMovedPlace = true` mode; see item 2 below).

For unprojected sized locals, `StatementKind.assign` destination-liveness
timing matches `rustc` (`eval_rvalue_into_place` / `local_to_place` /
`write_immediate_no_validate`) and `lean-miri` (`Place.lean` / `Rvalue.lean`),
both of which evaluate the RHS before raising `DeadLocal` at write time. Fault
kinds can still differ when an RHS outside $M_{\text{anneal}}$'s modeled
fragment returns `.unsupported` before write-time `DeadLocal` fires; for
`.use`, $M_{\text{anneal}}$ checks uninitialized input before writing while
`rustc`'s `copy_op` validates after writing (both producing `.undefined`).

Key semantic correspondence points:

1. **Two-pole fault classification (`FaultKind`):**
   - `FaultKind.undefined`: Modeled Rust Undefined Behavior, such as reading
     uninitialized or moved storage, accessing a dead local, dividing or taking
     remainder by zero, signed `INT_MIN / -1` or `INT_MIN % -1` overflow,
     unchecked arithmetic or shift overflow, or executing
     `TerminatorKind.unreachable` (`src/behavior-considered-undefined.md`,
     `rust-lang/reference` `a286e1ecb8ce193d50056e4bb042eea9b23876ef`, and
     `compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
     `8144389c895da997dbdecaa635e41d6a50be6ffd`):

     > "Rust code is incorrect if it exhibits any of the behaviors in the
     > following list. ... Producing an [invalid value][invalid-values]."
     > (`src/behavior-considered-undefined.md`, `rust-lang/reference`
     > `a286e1ecb8ce193d50056e4bb042eea9b23876ef`)
     >
     > "For integer types, division by zero is UB, as is `MIN / -1` for signed."
     > "For integer types, using zero as the modulus (second operand) is UB,
     > as is `MIN % -1` for signed."
     > (`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
     > `8144389c895da997dbdecaa635e41d6a50be6ffd`)

   - `FaultKind.unsupported`: Unmodeled MIR construct, malformed body/type
     invariant, or out-of-scope runtime feature. Both fault kinds falsify
     `WellFormed`, ensuring that $M_{\text{anneal}}$ fails closed on any
     unmodeled construct while distinguishing modeled UB from incomplete model
     coverage in canary proofs and downstream semantic-equivalence checks.

2. **Two-stage operand evaluation (`evalOperandToSlot` vs.
   `evalPrimitiveOperand`):**
   In `compiler/rustc_const_eval/src/interpret/operand.rs` (`rust-lang/rust`
   `8144389c895da997dbdecaa635e41d6a50be6ffd`), `eval_operand` resolves a
   `mir::Operand` to an `OpTy` before the caller either copies and validates
   the value (`Rvalue::Use` via `place.rs:copy_op`, which delegates to
   `copy_op_inner` / `copy_op_no_validate` followed by `validate_place`) or
   reads a primitive scalar (`read_immediate` in `operand.rs`):

   > "pub fn eval_operand(
   >     &self,
   >     mir_op: &mir::Operand<'tcx>,
   >     layout: Option<TyAndLayout<'tcx>>,
   > ) -> InterpResult<'tcx, OpTy<'tcx, M::Provenance>>"
   > (`compiler/rustc_const_eval/src/interpret/operand.rs`, `rust-lang/rust`
   > `8144389c895da997dbdecaa635e41d6a50be6ffd`)

   Upstream `compiler/rustc_middle/src/mir/syntax.rs` (`rust-lang/rust`
   `8144389c895da997dbdecaa635e41d6a50be6ffd`) leaves `Operand::Move`
   deinitialization open:

   > "This *may* additionally overwrite the place with `uninit` bytes, depending
   > on how we decide in [UCG#188]. You should not emit MIR that may attempt a
   > subsequent second load of this place without first re-initializing it."
   >
   > "**Needs clarification:** The operational impact of `Move` is unclear.
   > Currently (both in Miri and codegen) it has no effect at all unless it
   > appears in an argument to `Call`"
   > (`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
   > `8144389c895da997dbdecaa635e41d6a50be6ffd`)

   As a deliberate, conservative over-approximation (matching `lean-miri`'s
   opt-in `deinitMovedPlace = true` mode), $M_{\text{anneal}}$ always
   deinitializes non-ZST storage when evaluating `Operand.move`; this is sound
   because deinitializing causes any subsequent read without re-initialization
   to fault with `.undefined`, rejecting strictly more programs than upstream
   `rustc_const_eval::interpret`. Separating `evalOperandToSlot` (which
   resolves `(ty, optVal)` and applies this conservative `Operand.move`
   deinitialization) from `evalPrimitiveOperand` preserves exact left-to-right
   operand evaluation and fault ordering in `Rvalue.use` and `Rvalue.binaryOp`.

3. **Inhabited zero-sized local initialization (`MirTy.unit` and 1-variant
   `.zeroSized` `MirTy.enum`):**
   In `rustc_const_eval::interpret` and `lean-miri`
   (`Miri/Interpreter/Immediate.lean`, `ValidityVisitor.lean`, and
   `Discriminant.lean`), an inhabited 0-byte zero-sized type (`MirTy.unit` or
   an admitted `.zeroSized` 1-variant fieldless enum,
   `Variants::Single { index: 0 }`, `Size.ZERO`) requires zero initialized
   bytes in memory. Consequently, any live `.unit` or admitted `.zeroSized`
   1-variant `.enum` local slot (at frame entry, after `StorageLive`, or after
   `Operand.move`) remains inhabited by its unique value:
   `liveUninitSlot .unit = .live (some .unit)`, and
   `liveUninitSlot (.enum ety) = .live (some (.enumVal ety 0))` whenever
   `isZstEnumTy ety`.

4. **Explicit arithmetic applications:**
   `TrustedBoundary.lean`'s closed notation allowlist admits `+`, binary `-`,
   `*`, and comparisons, but not `^`, prefix `-`, or `>>>`. This module
   therefore writes those operations as explicit applications. `HPow.hPow`
   and `Neg.neg` elaborate to the same kernel terms as `^` and prefix `-`
   (`Neg.neg (HPow.hPow (2 : Int) 127)` is `-(2 ^ 127 : Int)`), which keeps
   bounds such as the `i128` range check syntactically identical to
   `vendor/lean-miri`. `Nat.pow` and `Nat.shiftRight` are the definitions that
   `Nat`'s `^` and `>>>` instances unfold to.

5. **Declaration modifiers (`noncomputable`):**
   Every `def` and term-level `abbrev` carries `noncomputable`, following the
   rule explained in `Trusted.MirAst` ("Declaration Modifiers"):
   `TrustedBoundary.validateRepoConstant` rejects the `partial`
   `._unsafe_rec` helper that Lean adds for a computable recursive definition,
   non-recursive value definitions calling `noncomputable` helpers require it
   transitively, and `TrustedBoundary.inspectNodeKind` forbids
   `noncomputable section`.
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

/-- Operational fault classification in $M_{\text{anneal}}$, corresponding to
`InterpErrorKind` in `compiler/rustc_middle/src/mir/interpret/error.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum InterpErrorKind<'tcx> {
>     UndefinedBehavior(UndefinedBehaviorInfo<'tcx>),
>     InvalidProgram(InvalidProgramInfo<'tcx>),
>     Unsupported(UnsupportedOpInfo),
>     ResourceExhaustion(ResourceExhaustionInfo),
>     MachineStop(Box<dyn MachineStopType>),
> }"

- `undefined`: Modeled Rust Undefined Behavior (`UndefinedBehavior`).
- `unsupported`: Unmodeled MIR construct, type, or runtime feature
  (`Unsupported` / `InvalidProgram`).
Both falsify `WellFormed`, while remaining distinct in non-vacuity canaries
and any downstream soundness or refinement reasoning. -/
inductive FaultKind where
  | undefined
  | unsupported

/-- Single-step transition outcome of $M_{\text{anneal}}$. -/
inductive StepResult (State Out : Type) where
  | step (next : State)
  | done (out : Out)
  | fault (kind : FaultKind)

/-- Canonical scalar value with explicit width, signedness, and 128-bit payload,
corresponding to `rustc_middle::ty::ScalarInt` paired with its integer
`TyAndLayout` (`compiler/rustc_middle/src/ty/consts/int.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub struct ScalarInt { data: u128, size: NonZero<u8> }"

Well-formed scalars satisfy `truncateBits width bits == bits`. -/
structure ScalarVal where
  width : IntWidth
  signed : Bool
  bits : BitVec 128

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

/-- Canonical pointer/reference value (`AllocId` provenance + byte offset),
corresponding to `rustc_const_eval::interpret::Pointer`
(`compiler/rustc_middle/src/mir/interpret/pointer.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
structure PtrVal where
  allocId : Option AllocId
  offsetBytes : UInt64
  width : IntWidth := .isize

/-- Abstract byte in memory: uninitialized or initialized `UInt8` with optional
allocation provenance `AllocId`. -/
inductive AllocByte where
  | uninit
  | init (byte : UInt8) (prov : Option AllocId := none)

/-- Check that `x` does not occur in `ys`. -/
noncomputable def natNotElem (x : Nat) : List Nat → Bool
  | [] => true
  | y :: ys => !Nat.beq x y && natNotElem x ys

/-- Check that all elements of a `List Nat` are pairwise distinct. -/
noncomputable def natListPairwiseNe : List Nat → Bool
  | [] => true
  | x :: xs => natNotElem x xs && natListPairwiseNe xs

/-- Pure structural UTF-8 byte equality on `String`, defined over the locked
foundation primitives (`String.toByteArray`, `Array.toList`, and `List.beq`
over `UInt8`) without expanding `foundation-lock.json` to import
`Init.Data.String.Basic` (`String.decEq`). -/
noncomputable def stringBeq (a b : String) : Bool :=
  List.beq a.toByteArray.data.toList b.toByteArray.data.toList

/-- Check that `x` does not occur in `ys` under `stringBeq`. -/
noncomputable def stringNotElem (x : String) : List String → Bool
  | [] => true
  | y :: ys => !stringBeq x y && stringNotElem x ys

/-- Check that all strings in a `List String` are pairwise distinct. -/
noncomputable def stringListPairwiseNe : List String → Bool
  | [] => true
  | x :: xs => stringNotElem x xs && stringListPairwiseNe xs

/-- Extend or truncate an in-memory scalar enum tag `tagBits` of primitive
representation `(tagW, tagS)` to the enum's discriminant bit width `discrW`,
matching `read_discriminant` (`int_to_int_or_float`) in
`compiler/rustc_const_eval/src/interpret/discriminant.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.Discriminant.readDiscriminant`
(`vendor/lean-miri/Miri/Interpreter/Discriminant.lean`):

> "let discr_val = self.int_to_int_or_float(&tag_val, discr_layout).unwrap();
> let discr_bits = discr_val.to_scalar().to_bits(discr_layout.size)?;" -/
noncomputable def tagBitsToDiscrBits (tagW : IntWidth) (tagS : Bool)
    (discrW : IntWidth) (tagBits : BitVec 128) : BitVec 128 :=
  let extended :=
    if tagS then
      bvOfInt 128 (signExtendBits tagW tagBits)
    else
      truncateBits tagW tagBits
  truncateBits discrW extended

/-- Check that a fieldless enum descriptor `ety : EnumTy` is statically
well-formed:
1. `ety.discriminants` is non-empty and has fewer than $2^{32}$ variants,
   matching `lean-miri`'s `< 2^32` variant-index bound (used on `Niche`
   paths in `vendor/lean-miri/Miri/Interpreter/Discriminant.lean`). In `rustc`,
   `rustc_abi::VariantIdx` (`rustc_index::newtype_index!` in
   `compiler/rustc_abi/src/layout.rs`, with default `max` value `0xFFFF_FF00`
   supplied by `compiler/rustc_index_macros/src/newtype.rs:98`,
   `rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`) caps variant
   indices at `0xFFFF_FF00`; the small extra admitted range
   `[0xFFFF_FF01, 2^32)` cannot occur in real `rustc` MIR:

   > "rustc_index::newtype_index! {
   >     ...
   >     pub struct VariantIdx {
   >         /// Equivalent to `VariantIdx(0)`.
   >         const FIRST_VARIANT = 0;
   >     }
   > }"

2. Every entry `d ∈ ety.discriminants` fits unsigned in `ety.discrWidth`
   (`d < Nat.pow 2 ety.discrWidth.bitWidth`, matching `Discr.val` in
   `compiler/rustc_middle/src/ty/util.rs`).
3. All entries in `ety.discriminants` are pairwise distinct, matching the Rust
   Reference (`src/items/enumerations.md`, `rust-lang/reference`
   `a286e1ecb8ce193d50056e4bb042eea9b23876ef`):

   > "It is an error when two variants share the same discriminant."

4. `ety.tagRepr` accurately encodes every declared discriminant:
   - `.zeroSized` requires exactly 1 variant (`Variants::Single { index: 0 }`);
   - `.scalar tagW tagS` requires that truncating each `d` to `tagW` and
     re-extending via `tagBitsToDiscrBits tagW tagS ety.discrWidth` recovers
     `d` losslessly (`TagEncoding::Direct` in `tag_for_variant` /
     `read_discriminant`). -/
noncomputable def enumAdmitted (ety : EnumTy) : Bool :=
  !ety.discriminants.isEmpty &&
    Nat.blt ety.discriminants.length (Nat.pow 2 32) &&
    ety.discriminants.all
      (fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth)) &&
    natListPairwiseNe ety.discriminants &&
    match ety.tagRepr with
    | .zeroSized => Nat.beq ety.discriminants.length 1
    | .scalar tagW tagS =>
      ety.discriminants.all (fun d =>
        let dBits := BitVec.ofNat 128 d
        tagBitsToDiscrBits tagW tagS ety.discrWidth
          (truncateBits tagW dBits) == dBits)

/-- Check whether `ety` is an admitted 0-byte ZST 1-variant fieldless enum
(`Variants::Single { index: 0 }`). -/
noncomputable def isZstEnumTy (ety : EnumTy) : Bool :=
  match ety.tagRepr with
  | .zeroSized => enumAdmitted ety
  | .scalar _ _ => false

/-- Linear search from `idx` for the unique variant index whose declared
discriminant bit pattern equals `discrBits`. -/
noncomputable def findDiscrVariantAux (idx : Nat) (discrBits : BitVec 128) :
    List Nat → Option Nat
  | [] => none
  | d :: ds =>
    if BitVec.ofNat 128 d == discrBits then
      some idx
    else
      findDiscrVariantAux (idx + 1) discrBits ds

/-- Resolve a `discrWidth`-truncated discriminant bit pattern `discrBits` to its
0-based declaration variant index in `ds`, matching
`adt.discriminants(*self.tcx).find(|(_, var)| var.val == discr_bits)` in
`read_discriminant` (`compiler/rustc_const_eval/src/interpret/discriminant.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
noncomputable def findDiscrVariant? (discrBits : BitVec 128)
    (ds : List Nat) : Option Nat :=
  findDiscrVariantAux 0 discrBits ds

/-- Canonical boundary value used in `Query`, `Out`, and `TerminalOut` of
$M_{\text{anneal}}$. -/
inductive Val where
  | scalar (v : ScalarVal)
  | ptr (p : PtrVal)
  | bool (b : Bool)
  | unit
  | enumVal (ty : EnumTy) (variant : Nat)
  | tuple (fields : List Val)
  | bytes (data : List AllocByte)

namespace Val

/-- Intrinsic type and well-formedness of a runtime value `Val`: returns
`some ty` iff `v` is a well-formed scalar, boolean, unit, or fieldless enum
value of type `ty`. -/
noncomputable def ty? : Val → Option MirTy
  | .scalar sv => if sv.wf then some (.int sv.width sv.signed) else none
  | .bool _ => some .bool
  | .unit => some .unit
  | .enumVal ety v =>
    if enumAdmitted ety && Nat.blt v ety.discriminants.length then
      some (.enum ety)
    else
      none
  | _ => none

end Val

/-- Caller-visible memory allocation descriptor. -/
structure Allocation where
  allocId : AllocId
  alignLog2 : Nat
  mutability : Mutability
  bytes : List AllocByte
  live : Bool := true

/-- Snapshot of caller-visible allocations. -/
structure CallerMemory where
  allocations : List Allocation := []

/-- Per-invocation input query: function arguments and initial caller-visible
memory. -/
structure Query where
  args : List Val
  callerMem : CallerMemory := ⟨[]⟩

/-- Per-invocation normal return output: return value in `_0` and final
caller-visible memory. -/
structure Out where
  ret : Val
  callerMem : CallerMemory := ⟨[]⟩

/-- Observable terminal outcome of a well-formed execution. -/
inductive TerminalOut where
  | returned (out : Out)
  | unwound (callerMem : CallerMemory := ⟨[]⟩)

/-- Local slot state in an active stack frame
(`compiler/rustc_const_eval/src/interpret/stack.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub(super) enum LocalValue<Prov: Provenance = CtfeProvenance> {
>     ...
>     Dead,
>     ...
>     Live(Operand<Prov>),
> }"

- `dead`: Storage is not currently allocated (`LocalValue::Dead`).
- `live none`: Storage is allocated (`StorageLive`) but uninitialized
  (`LocalValue::Live(Operand::Immediate(Immediate::Uninit))`).
- `live (some val)`: Storage is allocated and holds initialized value `val`. -/
inductive LocalSlot where
  | dead
  | live (val : Option Val)

/-- Active execution frame of $M_{\text{anneal}}$, corresponding to
`rustc_const_eval::interpret::Frame`
(`compiler/rustc_const_eval/src/interpret/stack.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
structure FrameState where
  defId : DefId
  blockIdx : BasicBlockId
  stmtIdx : Nat
  locals : List LocalSlot

/-- Running machine state of $M_{\text{anneal}}$ (factored cleanly from
`initState` so `State` carries only active execution frames and caller
memory, with no synthetic pre-entry variant). -/
structure State where
  frames : List FrameState
  callerMem : CallerMemory := ⟨[]⟩

/-- Demonic nondeterministic choice input for a single step. -/
abbrev Choice := Nat

/-- Admissible demonic choice predicate at state `s`. -/
noncomputable def ValidChoice (_p : Program) (_s : State) (c : Choice) : Prop :=
  c = 0

/-- Total list lookup by index without `Decidable` bounds proofs. -/
noncomputable def getElem? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => getElem? xs n

/-- Total list update by index, returning `none` when `n` is out of bounds. -/
noncomputable def setElem? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v =>
    match setElem? xs n v with
    | some xs' => some (x :: xs')
    | none => none

/-- Whether statement `stmt` is a `StorageLive` or `StorageDead` marker for
`localId`. -/
noncomputable def stmtHasStorageMarker (localId : LocalId) :
    StatementKind → Bool
  | .storageLive id | .storageDead id => Nat.beq id localId
  | _ => false

/-- Whether any basic block in `body` contains a `StorageLive` or `StorageDead`
annotation for `localId`.

Corresponds to `always_storage_live_locals` in
`compiler/rustc_mir_dataflow/src/impls/storage_liveness.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "Some locals have no `StorageLive` or `StorageDead` statements within the
> entire MIR body. These locals are implicitly allocated for the full duration
> of the function."
> (`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

and `Miri.Interpreter.CallMachine.alwaysLiveVarsAndTemps`: locals without any
`StorageLive`/`StorageDead` annotation in the body are live for the entire
function activation, whereas annotated non-argument locals start `.dead`. -/
noncomputable def hasStorageAnnotation (body : Body) (localId : LocalId) :
    Bool :=
  body.basicBlocks.any (fun bb =>
    bb.statements.any (stmtHasStorageMarker localId))

/-- Check that every `StorageLive` and `StorageDead` local index in `body` is
strictly less than `body.locals.length`, matching the entry check in
`Miri.Interpreter.CallMachine.alwaysLiveVarsAndTemps`. -/
noncomputable def storageAnnotationsInBounds (body : Body) : Bool :=
  let numLocals := body.locals.length
  body.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .storageLive id | .storageDead id => Nat.blt id numLocals
      | _ => true))

/-- Check that runtime value `v` has a well-formed intrinsic type equal to
`ty`. -/
noncomputable def checkVal (v : Val) (ty : MirTy) : Bool :=
  match v.ty? with
  | some vTy => MirTy.beq vTy ty
  | none => false

/-- Check that argument list `vs` matches parameter type list `tys` in length
and element types. -/
noncomputable def checkArgsMatch : List Val → List MirTy → Bool
  | [], [] => true
  | v :: vs, ty :: tys => checkVal v ty && checkArgsMatch vs tys
  | _, _ => false

/-- Check whether `ty` belongs to the supported local-variable type fragment
(`.bool`, `.int`, `.unit`, uninhabited `.never`, or admitted fieldless
`.enum`). The fragment is wider than the name suggests; downstream proof
modules refer to the predicate by this name. -/
noncomputable def isSupportedScalarOrUnitTy : MirTy → Bool
  | .bool | .int _ _ | .unit | .never => true
  | .enum ety => enumAdmitted ety
  | _ => false

/-- Initial state of a newly live local slot of type `ty`:
In `rustc_const_eval`
(`compiler/rustc_const_eval/src/interpret/discriminant.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and `lean-miri`
(`Miri/Interpreter/Immediate.lean`, `OperandMachine.lean`, and
`Discriminant.lean`), an inhabited 0-byte ZST (`MirTy.unit` or an admitted
`.zeroSized` 1-variant fieldless enum `Variants::Single { index: 0 }`) requires
zero initialized bytes in memory:

> "Variants::Single { index } => {
>     if op.layout().is_uninhabited() {
>         ...
>         throw_ub!(UninhabitedEnumVariantRead(Some(index)));
>     }
>     ...
>     return interp_ok(index);
> }"

Accordingly, live `.unit` locals start inhabited by `Val.unit` and live
`.zeroSized` fieldless enum locals start inhabited by `Val.enumVal ety 0` (and
`Operand.move` preserves their inhabited ZST value). All other local types
start uninitialized (`.live none`). -/
noncomputable def liveUninitSlot : MirTy → LocalSlot
  | .unit => .live (some .unit)
  | .enum ety =>
    if isZstEnumTy ety then .live (some (.enumVal ety 0)) else .live none
  | _ => .live none

/-- Initialize the local slots of `body` at function entry (`idx = 0 ..
body.locals.length - 1`), matching `Miri.Interpreter.CallMachine` (`pushRaw`,
`alwaysLiveVarsAndTemps`, `pushDone`) and
`compiler/rustc_const_eval/src/interpret/stack.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "self.storage_live(mir::RETURN_PLACE)?;
> let body = self.body();
> let always_live = always_storage_live_locals(body);
> for local in body.vars_and_temps_iter() {
>     if always_live.contains(local) {
>         self.storage_live(local)?;
>     }
> }"
> (`compiler/rustc_const_eval/src/interpret/stack.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

- `_0` (return place): `liveUninitSlot ty`.
- `_1 .. _argumentCount` (parameters): `.live (some arg)`.
- `> argumentCount`: `.dead` if `hasStorageAnnotation body idx`, else
  `liveUninitSlot ty`. -/
noncomputable def initLocalsLoop (body : Body) (args : List Val) :
    Nat → List MirTy → List LocalSlot
  | _, [] => []
  | idx, ty :: rest =>
      let slot : LocalSlot :=
        if Nat.beq idx 0 then
          liveUninitSlot ty
        else if Nat.ble idx body.argumentCount then
          match getElem? args (idx - 1) with
          | some v => .live (some v)
          | none => .dead
        else if hasStorageAnnotation body idx then
          .dead
        else
          liveUninitSlot ty
      slot :: initLocalsLoop body args (idx + 1) rest

/-- Entry initialization (`initState p q`):
Validates the 64-bit target layout (`p.pointerWidthBits = 64`), the MIR
semantic profile version (`p.mirProfileVersion = 1`; see
`Trusted.MirAst.Program`), entry body existence, non-empty basic blocks,
in-bounds storage annotations, supported local types, empty `callerMem`, and
well-typed `q.args`. Returns `.error .unsupported` if any static/entry
precondition fails. -/
noncomputable def initState (p : Program) (q : Query) :
    Except FaultKind State :=
  if !Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1 then
    .error .unsupported
  else if !q.callerMem.allocations.isEmpty then
    .error .unsupported
  else
    match getElem? p.bodies p.entryDefId with
    | none => .error .unsupported
    | some body =>
      if body.basicBlocks.isEmpty then
        .error .unsupported
      else if !Nat.blt body.argumentCount body.locals.length then
        .error .unsupported
      else if !storageAnnotationsInBounds body then
        .error .unsupported
      else if !body.locals.all isSupportedScalarOrUnitTy then
        .error .unsupported
      else
        let paramTys := (body.locals.drop 1).take body.argumentCount
        if !checkArgsMatch q.args paramTys then
          .error .unsupported
        else
          let locals := initLocalsLoop body q.args 0 body.locals
          let frame : FrameState := {
            defId := p.entryDefId
            blockIdx := 0
            stmtIdx := 0
            locals := locals
          }
          .ok { frames := [frame], callerMem := q.callerMem }

/-- Check whether `ty : MirTy` has a primitive-readable `BackendRepr.Scalar`
layout in `Miri.Interpreter.MemoryOperand.readImmediate`
(`Miri/Interpreter/MemoryOperand.lean`). -/
noncomputable def isPrimitiveReadableTy : MirTy → Bool
  | .bool | .int _ _ => true
  | _ => false

/-- Decode a typed constant literal `ConstLit` into a runtime `Val`, matching
`ScalarInt::try_from_uint` and `ScalarInt::try_to_bool` in
`compiler/rustc_middle/src/ty/consts/int.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and `Miri.Memory.ScalarInt`
(`vendor/lean-miri/Miri/Memory/ScalarInt.lean`):

> "pub fn try_from_uint(i: impl Into<u128>, size: Size) -> Option<Self> {
>     let (r, overflow) = Self::truncate_from_uint(i, size);
>     if overflow { None } else { Some(r) }
> }"
> "pub fn try_to_bool(self) -> Result<bool, ()> {
>     match self.to_u8() {
>         0 => Ok(false),
>         1 => Ok(true),
>         _ => Err(()),
>     }
> }"
> (`compiler/rustc_middle/src/ty/consts/int.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

A 1-byte `.bool` scalar whose value is neither `0` nor `1` triggers
`ScalarIntError.invalidBool`, which `Miri.Interpreter.ScalarOps.scalarError`
maps to `.undefinedBehavior`, so `evalConstLit` returns `.error .undefined`.

For fieldless enums (`.enum ety`), constant decoding matches `op_to_const`
(`compiler/rustc_const_eval/src/const_eval/eval_queries.rs:258`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`read_discriminant` (`compiler/rustc_const_eval/src/interpret/discriminant.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "let discr_val = self.int_to_int_or_float(&tag_val, discr_layout).unwrap();
> let discr_bits = discr_val.to_scalar().to_bits(discr_layout.size)?;
> ...
> adt.discriminants(*self.tcx).find(|(_, var)| var.val == discr_bits)
> ...
> .ok_or_else(|| err_ub!(InvalidTag(Scalar::from_uint(tag_bits,
>     tag_layout.size))))?;"

- Admitted 1-variant ZST enums (`ety.tagRepr = .zeroSized`) decode
  `ConstLit.zeroSized` to `.ok (.enumVal ety 0)`.
- Admitted direct-tagged enums (`ety.tagRepr = .scalar tagW tagS`) validate
  that `bits` fits in `tagW`, extend/truncate `bits` to `ety.discrWidth` via
  `tagBitsToDiscrBits`, and resolve the matching declaration index via
  `findDiscrVariant?` (returning `.error .undefined` on an invalid tag bit
  pattern not matching any declared discriminant). -/
noncomputable def evalConstLit : MirTy → ConstLit → Except FaultKind Val
  | .int w s, .scalar bits =>
    if truncateBits w bits != bits then
      .error .unsupported
    else
      .ok (.scalar ⟨w, s, truncateBits w bits⟩)
  | .bool, .scalar bits =>
    if truncateBits .i8 bits != bits then
      .error .unsupported
    else
      let v := UInt8.ofNat (truncateBits .i8 bits).toNat
      if v == 0 then
        .ok (.bool false)
      else if v == 1 then
        .ok (.bool true)
      else
        .error .undefined
  | .unit, .zeroSized => .ok .unit
  | .enum ety, .zeroSized =>
    if isZstEnumTy ety then .ok (.enumVal ety 0) else .error .unsupported
  | .enum ety, .scalar bits =>
    match ety.tagRepr with
    | .zeroSized => .error .unsupported
    | .scalar tagW tagS =>
      if !enumAdmitted ety || truncateBits tagW bits != bits then
        .error .unsupported
      else
        let discrBits := tagBitsToDiscrBits tagW tagS ety.discrWidth bits
        match findDiscrVariant? discrBits ety.discriminants with
        | some v => .ok (.enumVal ety v)
        | none => .error .undefined
  | _, _ => .error .unsupported

/-- Stage 1 of operand evaluation (`eval_operand` in
`compiler/rustc_const_eval/src/interpret/operand.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`, and
`Miri.Interpreter.OperandMachine.evalOperand` in
`vendor/lean-miri/Miri/Interpreter/OperandMachine.lean` with opt-in
`deinitMovedPlace = true`):

> "let op = match mir_op {
>     // FIXME: do some more logic on `move` to invalidate the old location
>     &Copy(place) | &Move(place) => self.eval_place_to_op(place, layout)?,
>     ...
>     Constant(constant) => {
>         ... self.eval_mir_constant(&c, constant.span, layout)?
>     }
> };"
> (`compiler/rustc_const_eval/src/interpret/operand.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

Note that upstream `eval_operand` currently leaves move invalidation
unimplemented (as recorded in the `FIXME` above). As a deliberate, conservative
over-approximation (sound because deinitializing can only introduce faults on
subsequent reads), `evalOperandToSlot` resolves an `Operand` to
`(ty : MirTy, optVal : Option Val, locals' : List LocalSlot)` without yet
requiring `optVal` to be initialized (`some v`), and deinitializes moved
non-ZST locals:
- `.copy place`: reads `(ty, optVal)` without mutating `locals`.
- `.move place`: reads `(ty, optVal)` and conservatively transitions
  `locals[place.localId]` to `liveUninitSlot ty` (preserving
  `.live (some .unit)` on `MirTy.unit` and `.live (some (.enumVal ety 0))` on
  admitted 1-variant `.zeroSized` `MirTy.enum`, and setting all other local
  types to `.live none`, matching `OperandMachine.evalOperand` with opt-in
  `deinitMovedPlace = true`).
- `.constant c`: decodes constant literal without mutating `locals`. -/
noncomputable def evalOperandToSlot (bodyLocals : List MirTy)
    (locals : List LocalSlot) :
    Operand → Except FaultKind (MirTy × Option Val × List LocalSlot)
  | .copy place =>
    if !place.projection.isEmpty then
      .error .unsupported
    else
      match getElem? bodyLocals place.localId,
          getElem? locals place.localId with
      | some ty, some (.live optVal) => .ok (ty, optVal, locals)
      | some _, some .dead => .error .undefined
      | _, _ => .error .unsupported
  | .move place =>
    if !place.projection.isEmpty then
      .error .unsupported
    else
      match getElem? bodyLocals place.localId,
          getElem? locals place.localId with
      | some ty, some (.live optVal) =>
        match setElem? locals place.localId (liveUninitSlot ty) with
        | some locals' => .ok (ty, optVal, locals')
        | none => .error .unsupported
      | some _, some .dead => .error .undefined
      | _, _ => .error .unsupported
  | .constant c =>
    match evalConstLit c.ty c.lit with
    | .ok v => .ok (c.ty, some v, locals)
    | .error k => .error k

/-- Stage 2 of operand evaluation (`evalOperandToSlot` followed by
`read_immediate` in
`compiler/rustc_const_eval/src/interpret/operand.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`, and
`Miri.Interpreter.MemoryOperand.readImmediate` in
`vendor/lean-miri/Miri/Interpreter/MemoryOperand.lean`):

> "if !matches!(
>     op.layout().backend_repr,
>     BackendRepr::Scalar(abi::Scalar::Initialized { .. })
>         | BackendRepr::ScalarPair { ... }
> ) {
>     span_bug!(
>         self.cur_span(),
>         \"primitive read not possible for type: {}\",
>         op.layout().ty
>     );
> }
> let imm = self.read_immediate_raw(op)?.right().unwrap();
> if matches!(*imm, Immediate::Uninit) {
>     throw_ub!(InvalidUninitBytes(None));
> }"
> (`compiler/rustc_const_eval/src/interpret/operand.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

Used by `.binaryOp`, `.unaryOp`, and `.switchInt`. Checks
`isPrimitiveReadableTy ty` on the static type first (`.unsupported` on
non-primitives such as `.unit`), and then checks initialization (`optVal = some
v`, faulting with `.undefined` on uninitialized storage). -/
noncomputable def evalPrimitiveOperand (bodyLocals : List MirTy)
    (locals : List LocalSlot) (opnd : Operand) :
    Except FaultKind (Val × List LocalSlot) :=
  match evalOperandToSlot bodyLocals locals opnd with
  | .error k => .error k
  | .ok (ty, optVal, locals') =>
    if !isPrimitiveReadableTy ty then
      .error .unsupported
    else
      match optVal with
      | some v => .ok (v, locals')
      | none => .error .undefined

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

/-- Evaluate an `Rvalue` for a destination of type `dstTy`, following the RHS
cases of `eval_rvalue_into_place`
(`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.Rvalue.evalRvalueIntoPlace` (`Miri/Interpreter/Rvalue.lean`),
together with Anneal's conservative `Operand.move` deinitialization
(`evalOperandToSlot`). `evalStatement` evaluates this RHS before checking
destination liveness and writing `dst` in `writePlace`, matching `rustc` and
`lean-miri` for unprojected sized locals (where `local_to_place` does not check
liveness and `DeadLocal` fires at write time; an unmodeled RHS can return
`.unsupported` before write-time `DeadLocal`, and `.use` checks uninitialized
input before writing while `rustc`'s `copy_op` validates after writing, with
both producing `.undefined`):
- `.use opnd`: resolves `(srcTy, optVal, locals₁) ← evalOperandToSlot`, checks
  `srcTy = dstTy` (`copyRuntimePlaceNoValidate`), then checks `optVal = some v`
  (validity check in `copy_op` / `copyRuntimePlace`).
- `.binaryOp op lhs rhs`: evaluates `lhs` and then `rhs` left-to-right via
  `evalPrimitiveOperand` (threading `locals₁` from `lhs` into `rhs`), then
  applies `evalBinOp`.
- `.unaryOp op opnd`: evaluates `opnd` via `evalPrimitiveOperand`, then applies
  `evalUnOp`.
- `.discriminant place`: reads the active variant of an unprojected local of
  admitted fieldless enum type `.enum ety` and returns its declared
  discriminant as a scalar of `(ety.discrWidth, ety.discrSigned)`, matching
  `read_discriminant` and `discriminant_for_variant` in
  `compiler/rustc_const_eval/src/interpret/discriminant.rs` (`rust-lang/rust`
  `8144389c895da997dbdecaa635e41d6a50be6ffd`) and
  `Miri.Interpreter.Discriminant`:

  > "let discr_layout = self.layout_of(ty.discriminant_ty(*self.tcx))?;
  > let discr_value = match ty.discriminant_for_variant(*self.tcx, variant) {
  >     Some(discr) => {
  >         ...
  >         assert_eq!(discr.ty, discr_layout.ty);
  >         Scalar::from_uint(discr.val, discr_layout.size)
  >     }
  >     ...
  > };
  > interp_ok(ImmTy::from_scalar(discr_value, discr_layout))"

  Reading `.discriminant` from a `.dead` local or from an uninitialized
  (`.live none`) scalar-tagged enum local faults with `.error .undefined`,
  whereas an inhabited 1-variant ZST enum (`ety.tagRepr = .zeroSized`,
  `Variants::Single { index: 0 }`) returns `ety.discriminants[0]` without
  reading tag bytes. -/
noncomputable def evalRvalue (bodyLocals : List MirTy) (locals : List LocalSlot)
    (dstTy : MirTy) : Rvalue → Except FaultKind (Val × List LocalSlot)
  | .use opnd =>
    match evalOperandToSlot bodyLocals locals opnd with
    | .error k => .error k
    | .ok (srcTy, optVal, locals₁) =>
      if !(MirTy.beq srcTy dstTy) then
        .error .unsupported
      else
        match optVal with
        | some v => .ok (v, locals₁)
        | none => .error .undefined
  | .binaryOp op lhs rhs =>
    match evalPrimitiveOperand bodyLocals locals lhs with
    | .error k => .error k
    | .ok (lVal, locals₁) =>
      match evalPrimitiveOperand bodyLocals locals₁ rhs with
      | .error k => .error k
      | .ok (rVal, locals₂) =>
        match evalBinOp op lVal rVal with
        | .error k => .error k
        | .ok res => .ok (res, locals₂)
  | .unaryOp op opnd =>
    match evalPrimitiveOperand bodyLocals locals opnd with
    | .error k => .error k
    | .ok (v, locals₁) =>
      match evalUnOp op v with
      | .error k => .error k
      | .ok res => .ok (res, locals₁)
  | .discriminant place =>
    if !place.projection.isEmpty then
      .error .unsupported
    else
      match getElem? bodyLocals place.localId,
          getElem? locals place.localId with
      | some (.enum ety), some slot =>
        if !enumAdmitted ety then
          .error .unsupported
        else
          -- For 1-variant `.zeroSized` enums, `Miri`'s `readDiscriminant`
          -- (`Variants::Single { index: 0 }`) returns variant `0` without
          -- reading tag bytes even if a slot holds `.live none` (`Uninit`),
          -- preserving universal 1-step lockstep over arbitrary `FrameState`s.
          match ety.tagRepr, slot with
          | _, .dead => .error .undefined
          | .zeroSized, .live none =>
            match getElem? ety.discriminants 0 with
            | some disc =>
              .ok (.scalar ⟨ety.discrWidth, ety.discrSigned,
                truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩, locals)
            | none => .error .unsupported
          | .zeroSized, .live (some (.enumVal ety' v)) =>
            if EnumTy.beq ety ety' && Nat.beq v 0 then
              match getElem? ety.discriminants 0 with
              | some disc =>
                .ok (.scalar ⟨ety.discrWidth, ety.discrSigned,
                  truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩, locals)
              | none => .error .unsupported
            else
              .error .unsupported
          | .zeroSized, .live (some _) => .error .unsupported
          | .scalar _ _, .live none => .error .undefined
          | .scalar _ _, .live (some (.enumVal ety' v)) =>
            if EnumTy.beq ety ety' && Nat.blt v ety.discriminants.length then
              match getElem? ety.discriminants v with
              | some disc =>
                .ok (.scalar ⟨ety.discrWidth, ety.discrSigned,
                  truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩, locals)
              | none => .error .unsupported
            else
              .error .unsupported
          | .scalar _ _, .live (some _) => .error .unsupported
      | _, _ => .error .unsupported
  | _ => .error .unsupported

/-- Write `val` into an unprojected `dst : Place` of known `dstTy : MirTy` in
`locals`: checks `checkVal val dstTy` first (matching
`Rvalue.assertRvalueLayout`), then checks `dst` liveness (matching
`Place.writePlaceImmediate`). -/
noncomputable def writePlace (locals : List LocalSlot) (dstLocalId : LocalId)
    (dstTy : MirTy) (val : Val) : Except FaultKind (List LocalSlot) :=
  if !checkVal val dstTy then
    .error .unsupported
  else
    match getElem? locals dstLocalId with
    | none => .error .unsupported
    | some .dead => .error .undefined
    | some (.live _) =>
      match setElem? locals dstLocalId (.live (some val)) with
      | some locals' => .ok locals'
      | none => .error .unsupported

/-- Evaluate a single `StatementKind` in `frame`, matching `eval_statement` in
`compiler/rustc_const_eval/src/interpret/step.rs` and `storage_live` /
`storage_dead` in `compiler/rustc_const_eval/src/interpret/stack.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub fn eval_statement(&mut self, stmt: &mir::Statement<'tcx>) ->
> InterpResult<'tcx> {
>     ...
>     match &stmt.kind {
>         Assign((place, rvalue)) => self.eval_rvalue_into_place(rvalue,
>             *place)?,
>         ...
>         StorageLive(local) => { self.storage_live(*local)?; }
>         StorageDead(local) => { self.storage_dead(*local)?; }
>         ...
>     }
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)
>
> "assert!(local != mir::RETURN_PLACE, \"Cannot make return place dead\");"
> (`compiler/rustc_const_eval/src/interpret/stack.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

- `.storageLive localId` sets `locals[localId] := liveUninitSlot localTy` for
  any in-bounds `localId < frame.locals.length` (and faults with `.unsupported`
  on out-of-bounds `localId`).
- `.storageDead 0` or out-of-bounds `.storageDead localId` faults with
  `.unsupported` (`StackError.cannotMakeReturnPlaceDead` /
  `StackError.invalidLocal`).
- `.assign dst rvalue` resolves `dst`'s local bounds and `dstTy` first, then
  evaluates `rvalue` (yielding `(val, localsAfterRval)`), then checks
  `checkVal` and `dst` liveness in `writePlace`, matching `rustc` and
  `lean-miri` for unprojected sized locals (where `local_to_place` does not
  check liveness and `DeadLocal` fires at write time; an unmodeled RHS can
  fault `.unsupported` before write-time `DeadLocal`, and `.use` checks
  uninitialized input before writing while `rustc`'s `copy_op` validates after
  writing, both producing `.undefined`). -/
noncomputable def evalStatement (body : Body) (frame : FrameState)
    (callerMem : CallerMemory) (stmt : StatementKind) :
    StepResult State TerminalOut :=
  match stmt with
  | .nop =>
    .step { frames := [{ frame with stmtIdx := frame.stmtIdx + 1 }], callerMem }
  | .storageLive localId =>
    match getElem? body.locals localId with
    | none => .fault .unsupported
    | some localTy =>
      match setElem? frame.locals localId (liveUninitSlot localTy) with
      | some locals' =>
        .step {
          frames := [{
            frame with
            stmtIdx := frame.stmtIdx + 1
            locals := locals'
          }]
          callerMem
        }
      | none => .fault .unsupported
  | .storageDead localId =>
    if Nat.beq localId 0 then
      .fault .unsupported
    else
      match setElem? frame.locals localId .dead with
      | some locals' =>
        .step {
          frames := [{
            frame with
            stmtIdx := frame.stmtIdx + 1
            locals := locals'
          }]
          callerMem
        }
      | none => .fault .unsupported
  | .assign dst rvalue =>
    if !dst.projection.isEmpty then
      .fault .unsupported
    else
      match getElem? body.locals dst.localId with
      | none => .fault .unsupported
      | some dstTy =>
        match evalRvalue body.locals frame.locals dstTy rvalue with
        | .error k => .fault k
        | .ok (val, localsAfterRval) =>
          match writePlace localsAfterRval dst.localId dstTy val with
          | .error k => .fault k
          | .ok localsAfterWrite =>
            .step {
              frames := [{
                frame with
                stmtIdx := frame.stmtIdx + 1
                locals := localsAfterWrite
              }]
              callerMem
            }
  | .unsupported => .fault .unsupported

/-- Evaluate a `SwitchTargets` branch list against discriminant bits `discrBits`
at width `w`, matching `SwitchInt` in
`compiler/rustc_const_eval/src/interpret/step.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`), `ScalarInt::try_from_uint` in
`compiler/rustc_middle/src/ty/consts/int.rs`, and `compareSwitchCase`
(`Scalar.fromUInt` -> `ScalarInt.tryFromUInt`) in
`Miri.Interpreter.ExecutionMachine.stepHooks`
(`vendor/lean-miri/Miri/Interpreter/ExecutionMachine.lean`):

> "for (const_int, target) in targets.iter() {
>     ...
>     let res = self.binary_op(
>         mir::BinOp::Eq,
>         &discr,
>         &ImmTy::from_uint(const_int, discr.layout),
>     )?;
>     if res.to_scalar().to_bool()? {
>         target_block = target;
>         break;
>     }
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

> "pub fn try_from_uint(i: impl Into<u128>, size: Size) -> Option<Self> {
>     let (r, overflow) = Self::truncate_from_uint(i, size);
>     if overflow { None } else { Some(r) }
> }"
> (`compiler/rustc_middle/src/ty/consts/int.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

If `caseBits` overflows width `w` (`truncateBits w caseBits != caseBits`),
`Scalar.fromUInt` throws `.scalarInt (.integerConversionOverflow _)`, which
`ScalarOps.scalarError` maps to `.invalidProgram` (`.error .unsupported`);
otherwise `evalSwitchBranches` compares `truncateBits w discrBits ==
truncateBits w caseBits` up to the first matching branch, returning `.ok
otherwise` when no branch matches. -/
noncomputable def evalSwitchBranches (w : IntWidth) (discrBits : BitVec 128)
    (otherwise : BasicBlockId) :
    List (BitVec 128 × BasicBlockId) → Except FaultKind BasicBlockId
  | [] => .ok otherwise
  | (caseBits, target) :: rest =>
    if truncateBits w caseBits != caseBits then
      .error .unsupported
    else if truncateBits w discrBits == truncateBits w caseBits then
      .ok target
    else
      evalSwitchBranches w discrBits otherwise rest

/-- Evaluate a `SwitchTargets` branch list against a boolean discriminant
`discr`, matching `compareSwitchCase` in
`Miri.Interpreter.ExecutionMachine.stepHooks`
(`vendor/lean-miri/Miri/Interpreter/ExecutionMachine.lean`), where each case
value is checked at 1-byte layout via `Scalar.fromUInt`
(`ScalarInt.tryFromUInt`) and compared via `ScalarOps.binary .Eq`
(`Scalar.toBool` on both operands):
- `caseBits` overflowing 1 byte (`truncateBits .i8 caseBits != caseBits`) fails
  `Scalar.fromUInt` with `.invalidProgram` (`.error .unsupported`);
- `0` (`false`) and `1` (`true`) match `!discr` and `discr`;
- `2..255` trigger `ScalarIntError.invalidBool` and fault with `.error
  .undefined`. -/
noncomputable def evalBoolSwitchBranches (discr : Bool)
    (otherwise : BasicBlockId) :
    List (BitVec 128 × BasicBlockId) → Except FaultKind BasicBlockId
  | [] => .ok otherwise
  | (caseBits, target) :: rest =>
    match evalConstLit .bool (.scalar caseBits) with
    | .ok (.bool false) =>
      if !discr then .ok target else evalBoolSwitchBranches discr otherwise rest
    | .ok (.bool true) =>
      if discr then .ok target else evalBoolSwitchBranches discr otherwise rest
    | .error k =>
      .error k
    | .ok _ =>
      .error .unsupported

/-- Assign the frame location to `(target, 0)`, matching
`Miri.Interpreter.ControlFlow.goToBlock` (`Miri/Interpreter/ControlFlow.lean`:
target block existence is checked at the start of the next step in `evalStep` /
`Step.step`). -/
noncomputable def jumpToBlock (frame : FrameState) (callerMem : CallerMemory)
    (target : BasicBlockId) : StepResult State TerminalOut :=
  .step {
    frames := [{ frame with blockIdx := target, stmtIdx := 0 }]
    callerMem
  }

/-- Evaluate a basic block's `TerminatorKind` when
`frame.stmtIdx == bb.statements.length`, matching `eval_terminator` in
`compiler/rustc_const_eval/src/interpret/step.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "fn eval_terminator(&mut self, terminator: &mir::Terminator<'tcx>) ->
> InterpResult<'tcx> {
>     ...
>     match terminator.kind {
>         Return => {
>             self.return_from_current_stack_frame(/* unwinding */ false)?
>         }
>         Goto { target, loop_hint_attrs: _ } => self.go_to_block(target),
>         SwitchInt { ref discr, ref targets } => { ... }
>         ...
>         Unreachable => throw_ub!(Unreachable),
>         ...
>     }
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def evalTerminator (body : Body) (bb : BasicBlock)
    (frame : FrameState) (callerMem : CallerMemory) :
    StepResult State TerminalOut :=
  match bb.terminator with
  | .goto target => jumpToBlock frame callerMem target
  | .return_ =>
    if bb.cleanup then
      .fault .unsupported
    else
      match getElem? frame.locals 0 with
      | some (.live (some retVal)) =>
        .done (.returned ⟨retVal, callerMem⟩)
      | some (.live none) | some .dead => .fault .undefined
      | none => .fault .unsupported
  | .unreachable =>
    .fault .undefined
  | .switchInt discr targets =>
    match evalPrimitiveOperand body.locals frame.locals discr with
    | .error k => .fault k
    | .ok (discrVal, localsAfterDiscr) =>
      let targetRes : Except FaultKind BasicBlockId :=
        match discrVal with
        | .scalar sv =>
          evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches
        | .bool b =>
          evalBoolSwitchBranches b targets.otherwise targets.branches
        | _ => .error .unsupported
      match targetRes with
      | .error k => .fault k
      | .ok target =>
        jumpToBlock { frame with locals := localsAfterDiscr } callerMem target
  | .unwindResume | .assert _ _ _ _ _ | .call _ _ _ _ _ | .unsupported =>
    .fault .unsupported

/-- Total single-step evaluator of $M_{\text{anneal}}$ over running `State`s,
matching `InterpCx::step` in `compiler/rustc_const_eval/src/interpret/step.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub fn step(&mut self) -> InterpResult<'tcx, bool> {
>     if self.stack().is_empty() {
>         return interp_ok(false);
>     }
>     ...
>     let basic_block = &self.body().basic_blocks[loc.block];
>     if let Some(stmt) = basic_block.statements.get(loc.statement_index) {
>         ...
>         self.eval_statement(stmt)?;
>         ...
>         self.frame_mut().loc.as_mut().left().unwrap().statement_index += 1;
>         return interp_ok(true);
>     }
>     ...
>     let terminator = basic_block.terminator();
>     self.eval_terminator(terminator)?;
>     ...
>     interp_ok(true)
> }"

Out-of-bounds `frame.blockIdx` faults with `.fault .unsupported` (matching
`Miri.Interpreter.Step.step` `StepError.invalidBlock`). -/
noncomputable def evalStep (p : Program) (_c : Choice) (s : State) :
    StepResult State TerminalOut :=
  match s.frames with
  | [frame] =>
    match getElem? p.bodies frame.defId with
    | none => .fault .unsupported
    | some body =>
      match getElem? body.basicBlocks frame.blockIdx with
      | none => .fault .unsupported
      | some bb =>
        match getElem? bb.statements frame.stmtIdx with
        | some stmt => evalStatement body frame s.callerMem stmt
        | none =>
          if Nat.beq frame.stmtIdx bb.statements.length then
            evalTerminator body bb frame s.callerMem
          else
            .fault .unsupported
  | _ => .fault .unsupported

/-- Relational small-step transition quantifying over admissible demonic
choices. -/
noncomputable def Step (p : Program) (s : State)
    (res : StepResult State TerminalOut) : Prop :=
  ∃ c : Choice, ValidChoice p s c ∧ evalStep p c s = res

/-- Unbounded finite-step reachability of intermediate states from `s₁` to
`s₂`. -/
inductive Reaches (p : Program) : State → State → Prop where
  | refl (s : State) : Reaches p s s
  | tail {s₁ s₂ s₃ : State} :
      Reaches p s₁ s₂ →
      Step p s₂ (.step s₃) →
      Reaches p s₁ s₃

/-- Outcome `res` is reached from `(p, q)` (either at entry via
`initState p q = .error k` or in finitely many steps from `s₀` when
`initState p q = .ok s₀`). -/
noncomputable def ReachesResult (p : Program) (q : Query)
    (res : StepResult State TerminalOut) : Prop :=
  match initState p q with
  | .error k => res = .fault k
  | .ok s₀ => ∃ s : State, Reaches p s₀ s ∧ Step p s res

/-- All-prefix well-formedness in $M_{\text{anneal}}$:
1. `initState p q = .ok s₀` and every reachable state has at least one
   admissible choice (`ValidChoice p s c`), preventing vacuous demonic choice;
   and
2. No reachable step (including `initState`) faults with `.undefined` or
   `.unsupported`. -/
noncomputable def WellFormed (p : Program) (q : Query) : Prop :=
  (∃ s₀ : State, initState p q = .ok s₀ ∧
    ∀ s : State, Reaches p s₀ s → ∃ c : Choice, ValidChoice p s c) ∧
  (∀ k : FaultKind, ¬ ReachesResult p q (.fault k))

/-- Observable terminal behavior of `(p, q)` in $M_{\text{anneal}}$. -/
noncomputable def Behavior (p : Program) (q : Query) (out : TerminalOut) :
    Prop :=
  ReachesResult p q (.done out)

/-- Divergence of `(p, q)` in $M_{\text{anneal}}$: from the initial state `s₀`,
there exists a single coherent infinite execution trace `trace : Nat → State`
starting at `s₀` (`trace 0 = s₀`) in which every transition
`trace n → trace (n + 1)` is a valid non-terminating step.

`Behavior` and `ReachesResult` describe only finite executions that stop, so
two semantics with the same finite outcomes could still differ in whether an
execution runs forever. `Diverges` makes non-termination observable alongside
finite outcomes so downstream equivalence proofs can relate both. -/
noncomputable def Diverges (p : Program) (q : Query) : Prop :=
  ∃ s₀ : State,
    initState p q = .ok s₀ ∧
    ∃ trace : Nat → State,
      trace 0 = s₀ ∧
      ∀ n : Nat, Step p (trace n) (.step (trace (n + 1)))

/-- Universal partial-correctness contract satisfaction in
$M_{\text{anneal}}$. -/
noncomputable def SatisfiesPost (p : Program) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  WellFormed p q ∧ ∀ out : TerminalOut, Behavior p q out → post out

/-!
## Multi-Body Program, Crate, and Proof-Unit Verification Judgments

The definitions below state the top-level per-body (`BodyVerified`),
program-wide (`ProgramVerified`), and captured-artifact (`CrateTheorem` and
`UnitTheorem`) obligations targeted by Anneal's verification pipeline.

Explicit semantic scoping notes for human auditors:
1. **Value-only entry memory (`callerMem = ⟨[]⟩`):** `BodyVerified` and
   `Specs.safety` quantify over value arguments `args : List Val` paired with
   empty caller memory `{ args := args, callerMem := ⟨[]⟩ }`, matching
   `initState`'s rejection of non-empty `callerMem` while pointer and reference
   entry parameters remain outside the supported domain.
2. **Interprocedural calls fail closed:** `entryProgForBody p defId` retains
   `p.bodies` so the program environment carries all sibling definitions, while
   any reachable `TerminatorKind.call` steps to `.fault .unsupported` and
   therefore refutes `WellFormed` fail-closed.
3. **Fault-freedom vs. termination (`WellFormed` vs. `Diverges`):**
   `WellFormed` establishes absence of `.fault .undefined` (UB) and
   `.fault .unsupported` (unmodeled constructs) across all executions while
   permitting infinite loops (`Diverges`); termination or functional
   input-output contracts are expressed in `Specs.property`.
4. **Whole-crate completeness is an external producer obligation:**
   `CrateTheorem` checks `c.program.scope = .crate` and `ProgramVerified` over
   every body in `c.program.bodies`. Guaranteeing that `c.program.bodies`
   actually includes every executable body and reachable callee in the compiled
   crate is an external obligation of the capture producer (such as a future
   `anneal-rustc-capture` emitter), not checked by `Trusted.MirSemantics`
   alone. -/

/-- Override `entryDefId` of `p` to execute body `defId` as the root function in
`initState` / `WellFormed` / `Behavior`. -/
noncomputable def entryProgForBody (p : Program) (defId : DefId) : Program :=
  { p with entryDefId := defId }

/-- Check that `args` matches the parameter types `locals[1..=argumentCount]` of
`body` in length and well-formed `Val.ty?`. -/
noncomputable def ValidEntryArgs (body : Body) (args : List Val) : Prop :=
  checkArgsMatch args ((body.locals.drop 1).take body.argumentCount) = true

/-- Check that all bodies in `bodies` carry non-empty, pairwise-distinct
`identity` keys so two functions can never collide in `Specs.safety`. -/
noncomputable def bodiesHaveUniqueIdentities (bodies : List Body) : Bool :=
  bodies.all (fun b => !stringBeq b.identity "") &&
    stringListPairwiseNe (bodies.map (fun b => b.identity))

/-- Unconditional static admission predicate for `(p, body)`: checks 64-bit
target layout, MIR semantic profile version 1, non-empty `body.identity`,
non-empty basic blocks, `argumentCount < locals.length`, in-bounds storage
annotations, and supported local types (`isSupportedScalarOrUnitTy`) even when
`body` has uninhabited (`MirTy.never`) parameters and `ValidEntryArgs body args`
is vacuously empty. -/
noncomputable def BodyStaticAdmitted (p : Program) (body : Body) : Bool :=
  Nat.beq p.pointerWidthBits 64 &&
    Nat.beq p.mirProfileVersion 1 &&
    !stringBeq body.identity "" &&
    !body.basicBlocks.isEmpty &&
    Nat.blt body.argumentCount body.locals.length &&
    storageAnnotationsInBounds body &&
    body.locals.all isSupportedScalarOrUnitTy

/-- Verification judgment for a single MIR function body `body` at index `defId`
in `p`:
1. `getElem? p.bodies defId = some body` binds `body` to the indexed function
   body in `p` (preventing callers from passing an unrelated `body`—such as an
   uninhabited `MirTy.never`-parameter stub—while executing `p.bodies[defId]`);
2. `BodyStaticAdmitted p body = true` holds unconditionally (independent of
   whether `ValidEntryArgs body args` is inhabited); and
3. For every well-typed argument list `args` (with empty `callerMem := ⟨[]⟩`),
   assuming `safetyPre args` only when `body.isUnsafe = true`, executing
   `entryProgForBody p defId` on `{ args := args }` is `WellFormed` (never
   reaches `.fault .undefined` or `.fault .unsupported`; non-terminating loops
   remain permitted unless ruled out by `Specs.property`). -/
noncomputable def BodyVerified (p : Program) (defId : DefId) (body : Body)
    (safetyPre : List Val → Prop) : Prop :=
  getElem? p.bodies defId = some body ∧
  BodyStaticAdmitted p body = true ∧
  ∀ args : List Val,
    ValidEntryArgs body args →
    (body.isUnsafe = true → safetyPre args) →
    WellFormed (entryProgForBody p defId) { args := args }

/-- Specification bundle for a captured MIR crate or proof unit:
- `safety identity args`: caller-obligation safety precondition (over value
  arguments `args` with `callerMem = ⟨[]⟩`) for an `unsafe` function with
  canonical path `identity` (ignored on safe functions, where
  `body.isUnsafe = false`);
- `property p`: functional correctness or termination specification over `p`. -/
structure Specs where
  safety : String → List Val → Prop := fun _ _ => True
  property : Program → Prop := fun _ => True

/-- Captured MIR verification subject pairing `program : Program` with its
reviewed specification bundle `specs : Specs`, so top-level obligations
(`CrateTheorem` and `UnitTheorem`) take a single captured `Crate` value. -/
structure Crate where
  program : Program
  specs : Specs := ⟨fun _ _ => True, fun _ => True⟩

/-- Verification judgment for a non-empty program `p` and `specs`:
1. `p.pointerWidthBits = 64` and `p.mirProfileVersion = 1`;
2. `p.bodies` is non-empty and `p.entryDefId < p.bodies.length` (preventing
   vacuous satisfaction on empty body lists or dangling `entryDefId`s);
3. Every body in `p.bodies` has a non-empty, pairwise-distinct `identity`
   (`bodiesHaveUniqueIdentities p.bodies = true`);
4. Every body `(defId, body)` in `p.bodies` satisfies `BodyVerified` under
   `specs.safety body.identity`; and
5. `specs.property p` holds. -/
noncomputable def ProgramVerified (p : Program) (specs : Specs) : Prop :=
  Nat.beq p.pointerWidthBits 64 = true ∧
  Nat.beq p.mirProfileVersion 1 = true ∧
  !p.bodies.isEmpty = true ∧
  Nat.blt p.entryDefId p.bodies.length = true ∧
  bodiesHaveUniqueIdentities p.bodies = true ∧
  (∀ (defId : DefId) (body : Body),
    getElem? p.bodies defId = some body →
    BodyVerified p defId body (specs.safety body.identity)) ∧
  specs.property p

/-- Top-level one-argument verification obligation for a whole-crate capture
(`c.program.scope = .crate`). Completeness of `c.program.bodies` with respect
to the compiled Rust crate (including every executable body and reachable
callee) is an external obligation of the capture producer (such as a future
`anneal-rustc-capture` emitter), not checked by this predicate alone. -/
noncomputable def CrateTheorem (c : Crate) : Prop :=
  c.program.scope = .crate ∧ ProgramVerified c.program c.specs

/-- Top-level one-argument verification obligation for a selected proof-unit
capture (`c.program.scope = .unit`). -/
noncomputable def UnitTheorem (c : Crate) : Prop :=
  c.program.scope = .unit ∧ ProgramVerified c.program c.specs

/-!
## Audited Pass 1 Weakest-Precondition and Non-Vacuity Canary Claims

The definitions below state the exact mathematical propositions that
`Anneal.MirWp` must prove and that `TrustedBoundary.lean` enforces via exact
`Expr` equality (`ci.type == .const claimName []` or the parameterized claim
application) together with claim-body constant checks. Keeping these claim
propositions in `Trusted.MirSemantics` ensures that no future change outside
`trusted/` can silently drift a pinned soundness or canary claim statement.
`anneal-audit` enforces only the exact theorem statements (not the internal
proof route); the closed canary claims witness non-vacuity of the operational
semantics (`WellFormed`, `Behavior`, and `ReachesResult`), and `Anneal.MirWp`
currently discharges them via `wpProg` / `wpFaultProg` and
`wellFormed_and_spec_of_wp` / `reaches_fault_and_exclusive_of_wpFault`.
-/

/-- Trusted total-correctness and productivity claim for
`Anneal.MirWp.wpProg`.

Requires partial correctness (`SatisfiesPost`), all-path termination
(`¬ Diverges`), and at least one terminating execution satisfying `post`. -/
noncomputable def WpSoundnessClaim
    (wpProgFn : Program → Nat → Query → (TerminalOut → Prop) → Prop) : Prop :=
  ∀ (p : Program) (q : Query) (fuel : Nat) (post : TerminalOut → Prop),
    wpProgFn p fuel q post →
    SatisfiesPost p q post ∧
    ¬ Diverges p q ∧
    (∃ out, Behavior p q out ∧ post out)

/-- Trusted fault-soundness, termination, and exclusivity claim for
`Anneal.MirWp.wpFaultProg`.

Requires that `(p, q)` reaches `.fault expected`, cannot reach any other fault
or normal terminal outcome, cannot diverge along any execution path
(`¬ Diverges`), and is not `WellFormed`. -/
noncomputable def WpFaultSoundnessClaim
    (wpFaultProgFn : Program → Nat → Query → FaultKind → Prop) : Prop :=
  ∀ (p : Program) (q : Query) (fuel : Nat) (expected : FaultKind),
    wpFaultProgFn p fuel q expected →
    ReachesResult p q (.fault expected) ∧
    (∀ k : FaultKind, k ≠ expected → ¬ ReachesResult p q (.fault k)) ∧
    (∀ out : TerminalOut, ¬ ReachesResult p q (.done out)) ∧
    ¬ Diverges p q ∧
    ¬ WellFormed p q

/-- Standard positive canary proposition: `(p, q)` is well-formed and returns
`expectedRet` with empty `callerMem`. -/
noncomputable def PositiveCanaryClaim (p : Program) (q : Query)
    (expectedRet : Val) : Prop :=
  WellFormed p q ∧ Behavior p q (.returned ⟨expectedRet, ⟨[]⟩⟩)

/-- Standard negative fault canary proposition: `(p, q)` reaches
`.fault expectedFault`, does not reach `.fault otherFault`, and is not
`WellFormed`. -/
noncomputable def NegativeCanaryClaim (p : Program) (q : Query)
    (expectedFault otherFault : FaultKind) : Prop :=
  ReachesResult p q (.fault expectedFault) ∧
  ¬ ReachesResult p q (.fault otherFault) ∧
  ¬ WellFormed p q

/-- `u32` type descriptor (`IntWidth.i32`, unsigned). -/
noncomputable def u32Ty : MirTy := .int .i32 false

/-- `u8` type descriptor (`IntWidth.i8`, unsigned). -/
noncomputable def u8Ty : MirTy := .int .i8 false

/-- `i8` type descriptor (`IntWidth.i8`, signed). -/
noncomputable def i8Ty : MirTy := .int .i8 true

/-- Construct a scalar `Val` of width `w` and signedness `s` from raw bit
pattern `bits : Nat`. -/
noncomputable def scalarNatVal (w : IntWidth) (s : Bool) (bits : Nat) : Val :=
  .scalar ⟨w, s, BitVec.ofNat 128 bits⟩

/-- Construct a `u32` scalar `Val` from `n : Nat`. -/
noncomputable def u32Val (n : Nat) : Val := scalarNatVal .i32 false n

/-- Construct an `i8` scalar `Val` from its raw 8-bit unsigned
representation. -/
noncomputable def i8Val (bits : Nat) : Val := scalarNatVal .i8 true bits

/-- Construct a `u8` scalar `Val` from `n : Nat`. -/
noncomputable def u8Val (n : Nat) : Val := scalarNatVal .i8 false n

/-- Single-block binary-operator test program:
`fn binop(a: lhsTy, b: rhsTy) -> retTy { _0 = op(copy _1, copy _2); return }` -/
noncomputable def mkBinOpProg (op : BinOp) (retTy lhsTy rhsTy : MirTy) :
    Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [retTy, lhsTy, rhsTy]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp op (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Single-block unary-operator test program:
`fn unop(a: ty) -> ty { _0 = op(copy _1); return }` -/
noncomputable def mkUnOpProg (op : UnOp) (ty : MirTy) : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [ty, ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.unaryOp op (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Canary `D1` (`ok` pole):
`fn add(a: u32, b: u32) -> u32 { _0 = a + b; return }` -/
noncomputable def progAddU32 : Program :=
  mkBinOpProg .add u32Ty u32Ty u32Ty

/-- Input query `(30u32, 12u32)` for `progAddU32`. -/
noncomputable def queryAdd30_12 : Query :=
  { args := [u32Val 30, u32Val 12] }

/-- Trusted claim for `Anneal.MirWp.canary_positive_add_anneal`. -/
noncomputable def CanaryPositiveAddAnnealClaim : Prop :=
  PositiveCanaryClaim progAddU32 queryAdd30_12 (u32Val 42)

/-- Canary `D2` (`ok` pole):
`fn empty() { return }` (`_0 : ()` live-initialized as a 0-byte ZST). -/
noncomputable def progEmptyUnitFn : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [{
      statements := []
      terminator := .return_
    }]
  }]

/-- Empty input query `()` for 0-argument test programs. -/
noncomputable def queryEmpty : Query := { args := [] }

/-- Trusted claim for `Anneal.MirWp.canary_positive_empty_unit_fn`. -/
noncomputable def CanaryPositiveEmptyUnitFnClaim : Prop :=
  PositiveCanaryClaim progEmptyUnitFn queryEmpty .unit

/-- Multi-block control-flow and statement canary program exercising
`StatementKind.nop`, `StatementKind.storageLive`, `StatementKind.storageDead`
(followed by re-allocation via `storageLive` and assignment),
`TerminatorKind.goto`, and `TerminatorKind.switchInt` across both a matched
branch arm (`10u32 -> bb2 -> 100u32`) and the `otherwise` fallback arm
(`_ -> bb3 -> 200u32`). -/
noncomputable def progStmtsAndCf : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    basicBlocks := [
      -- bb0: nop, StorageLive(_2), StorageDead(_2), StorageLive(_2),
      -- _2 = copy _1, Goto(bb1)
      {
        statements := [
          .nop,
          .storageLive 2,
          .storageDead 2,
          .storageLive 2,
          .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩))
        ]
        terminator := .goto 1
      },
      -- bb1: SwitchInt(move _2) [10 -> bb2, otherwise -> bb3]
      {
        statements := []
        terminator := .switchInt (.move ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 10, 2)]
          otherwise := 3
        }
      },
      -- bb2 (matched branch): _0 = const 100u32; StorageDead(_2); Return
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 100)⟩)),
          .storageDead 2
        ]
        terminator := .return_
      },
      -- bb3 (otherwise branch): _0 = const 200u32; StorageDead(_2); Return
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 200)⟩)),
          .storageDead 2
        ]
        terminator := .return_
      }
    ]
  }]

/-- Trusted claim for `Anneal.MirWp.canary_positive_stmts_and_cf_anneal`:
exercises `nop`, `storageLive`, `storageDead`, `goto`, and both matched and
`otherwise` arms of `switchInt`. -/
noncomputable def CanaryPositiveStmtsAndCfAnnealClaim : Prop :=
  PositiveCanaryClaim progStmtsAndCf { args := [u32Val 10] } (u32Val 100) ∧
  PositiveCanaryClaim progStmtsAndCf { args := [u32Val 99] } (u32Val 200)

/-- Trusted claim for `Anneal.MirWp.canary_positive_unop_anneal`:
exercises `UnOp.not` on `bool` (`!true = false`, `!false = true`), `UnOp.not`
on `u8` (`!0x0fu8 = 0xf0u8 = 240u8`), and `UnOp.neg` on signed `i8`
(`-(42i8) = -42i8`, raw bits `214`, and wrapping `-(-128i8) = -128i8`, raw
bits `128`). -/
noncomputable def CanaryPositiveUnopAnnealClaim : Prop :=
  PositiveCanaryClaim (mkUnOpProg .not .bool) { args := [.bool true] }
    (.bool false) ∧
  PositiveCanaryClaim (mkUnOpProg .not .bool) { args := [.bool false] }
    (.bool true) ∧
  PositiveCanaryClaim (mkUnOpProg .not u8Ty) { args := [u8Val 15] }
    (u8Val 240) ∧
  PositiveCanaryClaim (mkUnOpProg .neg i8Ty) { args := [i8Val 42] }
    (i8Val 214) ∧
  PositiveCanaryClaim (mkUnOpProg .neg i8Ty) { args := [i8Val 128] }
    (i8Val 128)

/-- Trusted claim for `Anneal.MirWp.canary_positive_all_binops_anneal`:
exercises every supported `BinOp` variant at boundary values across unsigned
integers, signed integers, shifts, and booleans. -/
noncomputable def CanaryPositiveAllBinopsAnnealClaim : Prop :=
  -- Wrapping `.add`, `.sub`, `.mul` (including unsigned wrap on `u8`):
  PositiveCanaryClaim (mkBinOpProg .add u8Ty u8Ty u8Ty)
    { args := [u8Val 255, u8Val 1] } (u8Val 0) ∧
  PositiveCanaryClaim (mkBinOpProg .sub u8Ty u8Ty u8Ty)
    { args := [u8Val 0, u8Val 1] } (u8Val 255) ∧
  PositiveCanaryClaim (mkBinOpProg .mul u8Ty u8Ty u8Ty)
    { args := [u8Val 16, u8Val 16] } (u8Val 0) ∧
  -- In-bounds `.addUnchecked`, `.subUnchecked`, `.mulUnchecked`:
  PositiveCanaryClaim (mkBinOpProg .addUnchecked u8Ty u8Ty u8Ty)
    { args := [u8Val 200, u8Val 55] } (u8Val 255) ∧
  PositiveCanaryClaim (mkBinOpProg .subUnchecked u8Ty u8Ty u8Ty)
    { args := [u8Val 55, u8Val 55] } (u8Val 0) ∧
  PositiveCanaryClaim (mkBinOpProg .mulUnchecked u8Ty u8Ty u8Ty)
    { args := [u8Val 15, u8Val 17] } (u8Val 255) ∧
  -- Signed `.div` and `.rem` (truncated towards zero on negative dividend):
  PositiveCanaryClaim (mkBinOpProg .div i8Ty i8Ty i8Ty)
    { args := [i8Val 249, i8Val 2] } (i8Val 253) ∧
  PositiveCanaryClaim (mkBinOpProg .rem i8Ty i8Ty i8Ty)
    { args := [i8Val 249, i8Val 2] } (i8Val 255) ∧
  -- Bitwise `.bitXor`, `.bitAnd`, `.bitOr` on integers, and `.bitXor` on
  -- booleans:
  PositiveCanaryClaim (mkBinOpProg .bitXor u8Ty u8Ty u8Ty)
    { args := [u8Val 170, u8Val 85] } (u8Val 255) ∧
  PositiveCanaryClaim (mkBinOpProg .bitAnd u8Ty u8Ty u8Ty)
    { args := [u8Val 170, u8Val 15] } (u8Val 10) ∧
  PositiveCanaryClaim (mkBinOpProg .bitOr u8Ty u8Ty u8Ty)
    { args := [u8Val 160, u8Val 5] } (u8Val 165) ∧
  PositiveCanaryClaim (mkBinOpProg .bitXor .bool .bool .bool)
    { args := [.bool true, .bool true] } (.bool false) ∧
  -- Shifts `.shl`, `.shr` (including shift amount >= bitWidth masked mod 8 and
  -- signed arithmetic right shift on `-8i8` (`248`) >> `2u32` = `-2i8`
  -- (`254`)), plus `.shlUnchecked` and `.shrUnchecked` at max valid shift `7`:
  PositiveCanaryClaim (mkBinOpProg .shl u8Ty u8Ty u32Ty)
    { args := [u8Val 1, u32Val 9] } (u8Val 2) ∧
  PositiveCanaryClaim (mkBinOpProg .shr i8Ty i8Ty u32Ty)
    { args := [i8Val 248, u32Val 2] } (i8Val 254) ∧
  PositiveCanaryClaim (mkBinOpProg .shlUnchecked u8Ty u8Ty u32Ty)
    { args := [u8Val 1, u32Val 7] } (u8Val 128) ∧
  PositiveCanaryClaim (mkBinOpProg .shrUnchecked u8Ty u8Ty u32Ty)
    { args := [u8Val 128, u32Val 7] } (u8Val 1) ∧
  -- All 6 comparisons (`.eq`, `.ne`, `.lt`, `.le`, `.gt`, `.ge`) on signed `i8`
  -- (`-1i8` = `255` < `1i8` = `1`), plus `.lt` on unsigned high-bit `u8`
  -- (`1u8 < 255u8 = true` and `255u8 < 1u8 = false`, distinguishing unsigned
  -- comparison from signed two's-complement comparison) and booleans
  -- (`false < true`):
  PositiveCanaryClaim (mkBinOpProg .eq .bool i8Ty i8Ty)
    { args := [i8Val 255, i8Val 255] } (.bool true) ∧
  PositiveCanaryClaim (mkBinOpProg .ne .bool i8Ty i8Ty)
    { args := [i8Val 255, i8Val 1] } (.bool true) ∧
  PositiveCanaryClaim (mkBinOpProg .lt .bool i8Ty i8Ty)
    { args := [i8Val 255, i8Val 1] } (.bool true) ∧
  PositiveCanaryClaim (mkBinOpProg .le .bool i8Ty i8Ty)
    { args := [i8Val 255, i8Val 255] } (.bool true) ∧
  PositiveCanaryClaim (mkBinOpProg .gt .bool i8Ty i8Ty)
    { args := [i8Val 1, i8Val 255] } (.bool true) ∧
  PositiveCanaryClaim (mkBinOpProg .ge .bool i8Ty i8Ty)
    { args := [i8Val 1, i8Val 255] } (.bool true) ∧
  PositiveCanaryClaim (mkBinOpProg .lt .bool u8Ty u8Ty)
    { args := [u8Val 1, u8Val 255] } (.bool true) ∧
  PositiveCanaryClaim (mkBinOpProg .lt .bool u8Ty u8Ty)
    { args := [u8Val 255, u8Val 1] } (.bool false) ∧
  PositiveCanaryClaim (mkBinOpProg .lt .bool .bool .bool)
    { args := [.bool false, .bool true] } (.bool true)

/-- Helper proposition for a single integer width `w`:
1. Unsigned `MAX + 1` wraps modulo $2^{\text{bitWidth}}$ to `0`.
2. Signed `INT_MAX + 1` wraps to `INT_MIN` (`2^(bitWidth - 1)`). -/
noncomputable def IntWidthBoundaryCanary (w : IntWidth) : Prop :=
  let uTy : MirTy := .int w false
  let sTy : MirTy := .int w true
  let uMax : Nat := Nat.pow 2 w.bitWidth - 1
  let sMax : Nat := Nat.pow 2 (w.bitWidth - 1) - 1
  let sMinBits : Nat := Nat.pow 2 (w.bitWidth - 1)
  PositiveCanaryClaim (mkBinOpProg .add uTy uTy uTy)
    { args := [scalarNatVal w false uMax, scalarNatVal w false 1] }
    (scalarNatVal w false 0) ∧
  PositiveCanaryClaim (mkBinOpProg .add sTy sTy sTy)
    { args := [scalarNatVal w true sMax, scalarNatVal w true 1] }
    (scalarNatVal w true sMinBits)

/-- Trusted claim for `Anneal.MirWp.canary_positive_all_int_widths_anneal`:
exercises all six `IntWidth` variants (`.i8`, `.i16`, `.i32`, `.i64`, `.i128`,
`.isize`) in both signed and unsigned modes at their width boundaries. -/
noncomputable def CanaryPositiveAllIntWidthsAnnealClaim : Prop :=
  IntWidthBoundaryCanary .i8 ∧
  IntWidthBoundaryCanary .i16 ∧
  IntWidthBoundaryCanary .i32 ∧
  IntWidthBoundaryCanary .i64 ∧
  IntWidthBoundaryCanary .i128 ∧
  IntWidthBoundaryCanary .isize

/-- Canary `D3` (`undefined` pole):
`fn div_zero(a: u32) -> u32 { _0 = a / 0; return }` -/
noncomputable def progDivByZero : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .div (.copy ⟨1, []⟩)
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Input query `(10u32)` for `progDivByZero`. -/
noncomputable def queryDivByZero : Query := { args := [u32Val 10] }

/-- Trusted claim for `Anneal.MirWp.canary_negative_ub_div_zero_anneal`. -/
noncomputable def CanaryNegativeUbDivZeroAnnealClaim : Prop :=
  NegativeCanaryClaim progDivByZero queryDivByZero .undefined .unsupported

/-- Canary `D4` (`undefined` pole):
signed `(-128i8) % (-1i8)` remainder overflow UB. -/
noncomputable def progSignedRemOverflowI8 : Program :=
  mkBinOpProg .rem i8Ty i8Ty i8Ty

/-- Input query `(-128i8, -1i8)` for `progSignedRemOverflowI8`. -/
noncomputable def querySignedRemOverflowI8 : Query :=
  { args := [i8Val 128, i8Val 255] }

/-- Trusted claim for
`Anneal.MirWp.canary_negative_ub_signed_rem_overflow_i8`. -/
noncomputable def CanaryNegativeUbSignedRemOverflowI8Claim : Prop :=
  NegativeCanaryClaim progSignedRemOverflowI8 querySignedRemOverflowI8
    .undefined .unsupported

/-- Canary `D5` (`unsupported` pole):
unmodeled statement `.unsupported` steps to `.fault .unsupported`. -/
noncomputable def progUnsupported : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [{
      statements := [.unsupported]
      terminator := .return_
    }]
  }]

/-- Trusted claim for `Anneal.MirWp.canary_negative_unsupported_anneal`. -/
noncomputable def CanaryNegativeUnsupportedAnnealClaim : Prop :=
  NegativeCanaryClaim progUnsupported queryEmpty .unsupported .undefined

/-- Unchecked-overflow canary program (`undefined` pole):
`fn add_unchecked(a: u32, b: u32) -> u32 { _0 = AddUnchecked(a, b); return }` -/
noncomputable def progAddUncheckedU32 : Program :=
  mkBinOpProg .addUnchecked u32Ty u32Ty u32Ty

/-- Input query `(u32::MAX, 1u32)`, whose mathematical sum overflows `u32`. -/
noncomputable def queryU32MaxPlusOne : Query :=
  { args := [u32Val 4294967295, u32Val 1] }

/-- Trusted claim for
`Anneal.MirWp.canary_negative_ub_add_unchecked_overflow_u32`. -/
noncomputable def CanaryNegativeUbAddUncheckedOverflowU32Claim : Prop :=
  NegativeCanaryClaim progAddUncheckedU32 queryU32MaxPlusOne
    .undefined .unsupported ∧
  PositiveCanaryClaim progAddU32 queryU32MaxPlusOne (u32Val 0)

/-- Trusted claim for
`Anneal.MirWp.canary_negative_ub_shift_unchecked_at_bitwidth_anneal`:
1. `BinOp.shlUnchecked` on `u32` with shift amount `32 == u32.bitWidth` faults
   with `.undefined`.
2. `BinOp.shrUnchecked` on `u32` with negative signed shift amount `-1i8`
   (`i8Val 255`) faults with `.undefined`. -/
noncomputable def CanaryNegativeUbShiftUncheckedAtBitwidthAnnealClaim : Prop :=
  NegativeCanaryClaim (mkBinOpProg .shlUnchecked u32Ty u32Ty u32Ty)
    { args := [u32Val 1, u32Val 32] } .undefined .unsupported ∧
  NegativeCanaryClaim (mkBinOpProg .shrUnchecked u32Ty u32Ty i8Ty)
    { args := [u32Val 1, i8Val 255] } .undefined .unsupported

/-- Program reading a local after `StatementKind.storageDead`:
`StorageLive(_1); _1 = const 7u32; StorageDead(_1); _0 = copy _1; return`. -/
noncomputable def progStorageDeadReadUb : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 7)⟩)),
        .storageDead 1,
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirWp.canary_negative_ub_storage_dead_read_anneal`. -/
noncomputable def CanaryNegativeUbStorageDeadReadAnnealClaim : Prop :=
  NegativeCanaryClaim progStorageDeadReadUb queryEmpty .undefined .unsupported

/-- Program executing `StatementKind.storageDead 0` on the return place `_0`. -/
noncomputable def progStorageDeadReturnPlaceUb : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [{
      statements := [.storageDead 0]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirWp.canary_negative_ub_storage_dead_return_place_anneal`:
Anneal conservatively rejects `StatementKind.storageDead 0` on the return
place `_0` as `.fault .unsupported` (rather than `.fault .undefined`),
matching `lean-miri`'s `StepError.stack StackError.cannotMakeReturnPlaceDead`
/ malformed-MIR rejection (and `rustc`'s `assert!(local != mir::RETURN_PLACE,
"Cannot make return place dead")`). Note that despite the `NegativeUb`
identifier prefix, this claim pins `.fault .unsupported` (and rules out
`.fault .undefined`). -/
noncomputable def CanaryNegativeUbStorageDeadReturnPlaceAnnealClaim : Prop :=
  NegativeCanaryClaim progStorageDeadReturnPlaceUb queryEmpty
    .unsupported .undefined

/-- Program executing `TerminatorKind.unreachable`. -/
noncomputable def progUnreachableUb : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [{
      statements := []
      terminator := .unreachable
    }]
  }]

/-- Trusted claim for
`Anneal.MirWp.canary_negative_ub_unreachable_anneal`. -/
noncomputable def CanaryNegativeUbUnreachableAnnealClaim : Prop :=
  NegativeCanaryClaim progUnreachableUb queryEmpty .undefined .unsupported

/-- Trusted claim for
`Anneal.MirWp.canary_negative_unsupported_unsigned_neg_anneal`:
executing `UnOp.neg` on an unsigned integer (`u32`) reaches
`.fault .unsupported` (and not `.fault .undefined`). -/
noncomputable def CanaryNegativeUnsupportedUnsignedNegAnnealClaim : Prop :=
  NegativeCanaryClaim (mkUnOpProg .neg u32Ty) { args := [u32Val 1] }
    .unsupported .undefined

/-- Explicit-repr fieldless enum `#[repr(u8)] enum ReprU8 { A = 10, B = 20 }`
with non-index discriminants and `u8` discriminant/tag width. -/
noncomputable def canaryReprU8EnumTy : EnumTy := {
  id := 1
  discrWidth := .i8
  discrSigned := false
  tagRepr := .scalar .i8 false
  discriminants := [10, 20]
}

/-- Signed-tag fieldless enum `enum SignedTag { Neg = -1, Pos = 1 }` with 1-byte
signed `i8` in-memory tag (`0xff = 255` for `-1`) and 64-bit signed `isize`
discriminant (`2^64 - 1`). -/
noncomputable def canarySignedTagEnumTy : EnumTy := {
  id := 2
  discrWidth := .isize
  discrSigned := true
  tagRepr := .scalar .i8 true
  discriminants := [Nat.pow 2 64 - 1, 1]
}

/-- Positive canary program decoding `const ReprU8::B` (`.scalar 20`, variant 1)
and reading `Rvalue.discriminant` into a `u8` return place `_0`. -/
noncomputable def progEnumExplicitReprU8 : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u8Ty, .enum canaryReprU8EnumTy]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩ (.use (.constant
          ⟨.enum canaryReprU8EnumTy, .scalar (BitVec.ofNat 128 20)⟩)),
        .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩),
        .storageDead 1
      ]
      terminator := .return_
    }]
  }]

/-- Positive canary program decoding `const SignedTag::Neg` (1-byte signed tag
`0xff = 255`, sign-extended to `-1isize = 2^64 - 1`) and reading
`Rvalue.discriminant` into an `isize` return place `_0`. -/
noncomputable def progEnumSignedTagIsize : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.int .isize true, .enum canarySignedTagEnumTy]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩ (.use (.constant
          ⟨.enum canarySignedTagEnumTy, .scalar (BitVec.ofNat 128 255)⟩)),
        .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩),
        .storageDead 1
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirWp.canary_positive_enum_explicit_repr_anneal`:
exercises explicit-repr `#[repr(u8)]` non-index enum constant tag decoding and
`u8` `Rvalue.discriminant` alongside signed `i8` -> `isize` tag sign-extension.
-/
noncomputable def CanaryPositiveEnumExplicitReprAnnealClaim : Prop :=
  PositiveCanaryClaim progEnumExplicitReprU8 queryEmpty (u8Val 20) ∧
  PositiveCanaryClaim progEnumSignedTagIsize queryEmpty
    (scalarNatVal .isize true (Nat.pow 2 64 - 1))

/-- Single-variant inhabited ZST fieldless enum `enum Single { Only = 42 }`
(`Variants::Single { index: 0 }`, `Size::ZERO`). -/
noncomputable def canarySingleZstEnumTy : EnumTy := {
  id := 3
  discrWidth := .isize
  discrSigned := true
  tagRepr := .zeroSized
  discriminants := [42]
}

/-- Positive canary `fn() -> Single { return }` returning an inhabited ZST
1-variant enum without an explicit assignment to `_0`. -/
noncomputable def progZstSingleEnumImplicitRet : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.enum canarySingleZstEnumTy]
    basicBlocks := [{
      statements := []
      terminator := .return_
    }]
  }]

/-- Positive canary exercising `StorageLive`, `Operand.move` (non-deinitializing
on ZST), `ConstLit.zeroSized`, and `Rvalue.discriminant` on `Single`. -/
noncomputable def progZstSingleEnumMoveAndDiscr : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [
      .int .isize true,
      .enum canarySingleZstEnumTy,
      .enum canarySingleZstEnumTy,
      .enum canarySingleZstEnumTy
    ]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .storageLive 2,
        .storageLive 3,
        .assign ⟨2, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨3, []⟩ (.use (.constant
          ⟨.enum canarySingleZstEnumTy, .zeroSized⟩)),
        .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩),
        .storageDead 3,
        .storageDead 2,
        .storageDead 1
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for `Anneal.MirWp.canary_positive_zst_single_enum_anneal`. -/
noncomputable def CanaryPositiveZstSingleEnumAnnealClaim : Prop :=
  PositiveCanaryClaim progZstSingleEnumImplicitRet queryEmpty
    (.enumVal canarySingleZstEnumTy 0) ∧
  PositiveCanaryClaim progZstSingleEnumMoveAndDiscr queryEmpty
    (scalarNatVal .isize true 42)

/-- Negative UB canary: `ConstLit.scalar 1` on `ReprU8 { A = 10, B = 20 }` is an
invalid enum tag (not variant index 1!) and faults with `.undefined`. -/
noncomputable def progEnumInvalidTagConstUb : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u8Ty, .enum canaryReprU8EnumTy]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩ (.use (.constant
          ⟨.enum canaryReprU8EnumTy, .scalar (BitVec.ofNat 128 1)⟩)),
        .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩)
      ]
      terminator := .return_
    }]
  }]

/-- Negative UB canary: reading `Rvalue.discriminant` from an uninitialized
scalar-tagged enum local faults with `.undefined`. -/
noncomputable def progEnumUninitDiscrUb : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u8Ty, .enum canaryReprU8EnumTy]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩)
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirWp.canary_negative_ub_enum_invalid_tag_and_uninit_anneal`. -/
noncomputable def CanaryNegativeUbEnumInvalidTagAndUninitAnnealClaim : Prop :=
  NegativeCanaryClaim progEnumInvalidTagConstUb queryEmpty
    .undefined .unsupported ∧
  NegativeCanaryClaim progEnumUninitDiscrUb queryEmpty
    .undefined .unsupported

/-- Safe 0-arg unit body for `CanaryCrateAndBodyVerifiedAnnealClaim`. -/
noncomputable def canarySafeUnitBody : Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{ statements := [], terminator := .return_ }]
  isUnsafe := false
  identity := "canary::safe_unit"
}

/-- `unsafe fn(flag: bool) -> u32` body that returns `42` when `flag = true` and
executes `unreachable` when `flag = false`. -/
noncomputable def canaryUnsafeGuardedBody (isUnsafeFlag : Bool) : Body := {
  argumentCount := 1
  locals := [u32Ty, .bool]
  basicBlocks := [
    {
      statements := []
      terminator := .switchInt (.copy ⟨1, []⟩) {
        branches := [(BitVec.ofNat 128 1, 1)]
        otherwise := 2
      }
    },
    {
      statements := [
        .assign ⟨0, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩))
      ]
      terminator := .return_
    },
    {
      statements := []
      terminator := .unreachable
    }
  ]
  isUnsafe := isUnsafeFlag
  identity := "canary::unsafe_guarded"
}

/-- Safe `fn(x: !) -> ()` body exercising uninhabited `MirTy.never` parameter
verification while enforcing `BodyStaticAdmitted`. -/
noncomputable def canaryNeverParamBody (badStorage : Bool) : Body := {
  argumentCount := 1
  locals := [.unit, .never]
  basicBlocks := [{
    statements := if badStorage then [.storageLive 9] else []
    terminator := .unreachable
  }]
  isUnsafe := false
  identity := "canary::never_param"
}

/-- Valid 3-body crate combining a safe body (with `safety = False` ignored),
an `unsafe` body guarded by `safety`, and an uninhabited `!`-parameter body. -/
noncomputable def canaryValidCrate : Crate := {
  program := {
    scope := .crate
    pointerWidthBits := 64
    mirProfileVersion := 1
    bodies := [
      canarySafeUnitBody,
      canaryUnsafeGuardedBody true,
      canaryNeverParamBody false
    ]
  }
  specs := {
    safety := fun id args =>
      if stringBeq id "canary::unsafe_guarded" then
        args = [.bool true]
      else
        False
    property := fun p => Nat.beq p.bodies.length 3 = true
  }
}

/-- Trusted claim for `Anneal.MirWp.canary_crate_and_body_verified_anneal`:
1. `CrateTheorem canaryValidCrate` and `UnitTheorem` on a valid `.unit` capture
   both hold;
2. Marking `canaryUnsafeGuardedBody` safe (`isUnsafe = false`) refutes
   `BodyVerified` even under `safetyPre := fun _ => False`;
3. An invalid `MirTy.never` body (`badStorage = true`) refutes `BodyVerified`
   via `BodyStaticAdmitted` even though `ValidEntryArgs` is empty;
4. Mismatching `body` against `p.bodies[defId]` (including passing an admitted
   `MirTy.never` body against a faulty `p.bodies[0]`) refutes `BodyVerified`;
5. Empty `bodies := []`, out-of-bounds `entryDefId`, and duplicate `identity`
   strings each refute `CrateTheorem` / `UnitTheorem`;
6. A crate containing a non-`BodyVerified` body (even alongside a valid body)
   refutes `CrateTheorem`;
7. A false `specs.property` (`fun _ => False`) refutes both `CrateTheorem` and
   `UnitTheorem`; and
8. `.crate` vs. `.unit` scope mismatches refute both `CrateTheorem` (on a
   `.unit` capture) and `UnitTheorem` (on `canaryValidCrate`). -/
noncomputable def CanaryCrateAndBodyVerifiedAnnealClaim : Prop :=
  CrateTheorem canaryValidCrate ∧
  UnitTheorem {
      program := {
        scope := .unit
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canarySafeUnitBody]
      }
      specs := {
        property := fun p => Nat.beq p.bodies.length 1 = true
      }
    } ∧
  ¬ BodyVerified {
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canaryUnsafeGuardedBody false]
    } 0
      (canaryUnsafeGuardedBody false) (fun _ => False) ∧
  ¬ BodyVerified {
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canaryNeverParamBody true]
    } 0
      (canaryNeverParamBody true) (fun _ => True) ∧
  ¬ BodyVerified {
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody, canaryUnsafeGuardedBody false]
    } 0
      (canaryUnsafeGuardedBody false) (fun _ => True) ∧
  ¬ BodyVerified {
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canaryUnsafeGuardedBody false]
    } 0
      (canaryNeverParamBody false) (fun _ => True) ∧
  ¬ CrateTheorem {
      program := {
        scope := .crate
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := []
      }
    } ∧
  ¬ UnitTheorem {
      program := {
        scope := .unit
        entryDefId := 5
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canarySafeUnitBody]
      }
    } ∧
  ¬ CrateTheorem {
      program := {
        scope := .crate
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canarySafeUnitBody, canarySafeUnitBody]
      }
    } ∧
  ¬ CrateTheorem {
      program := {
        scope := .crate
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canarySafeUnitBody, canaryUnsafeGuardedBody false]
      }
    } ∧
  ¬ CrateTheorem {
      program := {
        scope := .crate
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canarySafeUnitBody]
      }
      specs := {
        property := fun _ => False
      }
    } ∧
  ¬ UnitTheorem {
      program := {
        scope := .unit
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canarySafeUnitBody]
      }
      specs := {
        property := fun _ => False
      }
    } ∧
  ¬ CrateTheorem {
      program := {
        scope := .unit
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canarySafeUnitBody]
      }
    } ∧
  ¬ UnitTheorem canaryValidCrate

end Trusted.MirSemantics

namespace Trusted

/-- Top-level captured crate + specification bundle alias (`Trusted.Crate`). -/
abbrev Crate := Trusted.MirSemantics.Crate

/-- Top-level one-argument whole-crate verification obligation
(`Trusted.CrateTheorem`). -/
noncomputable abbrev CrateTheorem := Trusted.MirSemantics.CrateTheorem

/-- Top-level one-argument proof-unit verification obligation
(`Trusted.UnitTheorem`). -/
noncomputable abbrev UnitTheorem := Trusted.MirSemantics.UnitTheorem

end Trusted
