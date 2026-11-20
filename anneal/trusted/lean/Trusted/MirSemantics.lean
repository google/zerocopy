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
`WpFaultSoundnessClaim`, and the 20 `Canary*Claim` propositions).

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
   resolves `(ty, sv)` and applies this conservative `Operand.move`
   deinitialization) from `evalPrimitiveOperand` preserves exact left-to-right
   operand evaluation and fault ordering in `Rvalue.use` and `Rvalue.binaryOp`.

   A move deinitializes exactly the storage that its place selects. Each
   field of a tuple local carries its own initialization state (`SlotVal`), so
   `move (_8.1: bool)` deinitializes field `1` of `_8` and leaves field `0`
   readable, as the `(T, bool)` results of `AddWithOverflow` require:

   > "_8 = AddWithOverflow(copy _3, const 1_usize);
   > assert(!move (_8.1: bool), ...) -> [success: bb4, unwind continue];
   > bb4: _0 = move (_8.0: usize);"

3. **Inhabited zero-sized local initialization (`MirTy.unit` and 1-variant
   `.zeroSized` `MirTy.enum`):**
   In `rustc_const_eval::interpret` and `lean-miri`
   (`Miri/Interpreter/Immediate.lean`, `ValidityVisitor.lean`, and
   `Discriminant.lean`), an inhabited 0-byte zero-sized type (`MirTy.unit` or
   an admitted `.zeroSized` 1-variant fieldless enum,
   `Variants::Single { index: 0 }`, `Size.ZERO`) requires zero initialized
   bytes in memory. Consequently, any live `.unit` or admitted `.zeroSized`
   1-variant `.enum` storage (at frame entry, after `StorageLive`, or after
   `Operand.move`, whether it is a whole local or a tuple field) remains
   inhabited by its unique value: `uninitSlotVal .unit = .unit`, and
   `uninitSlotVal (.enum ety) = .enumVal ety 0` whenever `isZstEnumTy ety`.

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

/-- Inclusive wrapping-range membership check matching
`Miri.ABI.WrappingRange.contains`
(`vendor/lean-miri/Miri/ABI/WrappingRange.lean`). -/
noncomputable def wrappingRangeContains (start end_ value : BitVec 128) :
    Bool :=
  if Nat.ble start.toNat end_.toNat then
    Nat.ble start.toNat value.toNat && Nat.ble value.toNat end_.toNat
  else
    Nat.ble start.toNat value.toNat || Nat.ble value.toNat end_.toNat

/-- Per-variant payload field types of `ety` at 0-based variant index `v`. -/
noncomputable def fieldsForVariant? (ety : EnumTy) (v : Nat) :
    Option (List MirTy) :=
  if !Nat.blt v ety.discriminants.length ||
      !Nat.beq ety.variantFields.length ety.discriminants.length then
    none
  else
    getElem? ety.variantFields v

/-- True iff `ety` declares at least one variant with a non-empty payload field
list. -/
noncomputable def hasEnumPayloadFields (ety : EnumTy) : Bool :=
  ety.variantFields.any (fun fs => !fs.isEmpty)

mutual
  /-- Structural uninhabitedness predicate matching `LayoutData.isUninhabited`
  in `compiler/rustc_abi/src/layout.rs` and `Miri.ABI.LayoutData`:
  - `.never` (`!`) is uninhabited;
  - `.adtStruct` and `.tuple` are uninhabited iff any field is uninhabited;
  - `.array elemTy len` is uninhabited iff `len > 0` and `elemTy` is
    uninhabited (`[!; 0]` is inhabited);
  - `.enum` is uninhabited iff it has zero variants or every variant has an
    uninhabited field. -/
  noncomputable def isTypeUninhabited : MirTy → Bool
    | .bool | .int _ _ | .unit => false
    | .never => true
    | .adtStruct ⟨_, fs⟩ => anyFieldUninhabited fs
    | .enum ⟨_, _, _, _, ds, vf⟩ =>
      if ds.isEmpty || !Nat.beq vf.length ds.length then
        true
      else
        allVariantsUninhabited vf
    | .tuple fs => anyFieldUninhabited fs
    | .array elemTy len => !Nat.beq len 0 && isTypeUninhabited elemTy
    | _ => true

  /-- True iff at least one type in `tys` is uninhabited. -/
  noncomputable def anyFieldUninhabited : List MirTy → Bool
    | [] => false
    | ty :: tys => isTypeUninhabited ty || anyFieldUninhabited tys

  /-- True iff every variant field list in `vss` contains an uninhabited
  field. -/
  noncomputable def allVariantsUninhabited : List (List MirTy) → Bool
    | [] => true
    | fs :: fss => anyFieldUninhabited fs && allVariantsUninhabited fss
end

/-- True iff variant `v` of `ety` is out of bounds or contains an uninhabited
field, matching `LayoutData.isVariantUninhabited`
(`vendor/lean-miri/Miri/ABI/Layout.lean`). -/
noncomputable def isVariantUninhabited (ety : EnumTy) (v : Nat) : Bool :=
  match fieldsForVariant? ety v with
  | none => true
  | some fs => anyFieldUninhabited fs

mutual
  /-- Structural 0-byte ZST predicate (`Size::ZERO` in `rustc_abi`): `.unit`,
  `.never`, 0-length arrays, arrays of ZSTs, structs/tuples of ZSTs,
  `.zeroSized` fieldless enums, and `.single v` enums whose active variant `v`
  has only ZST fields. -/
  noncomputable def isZeroSizedTy : MirTy → Bool
    | .unit | .never => true
    | .bool | .int _ _ => false
    | .adtStruct ⟨_, fs⟩ => areAllZeroSizedTys fs
    | .enum ⟨_, _, _, tagRepr, ds, vf⟩ =>
      let zstFlags := variantZeroSizedFlags vf
      match tagRepr with
      | .zeroSized =>
        Nat.beq ds.length 1 && Nat.beq vf.length 1 &&
          !(zstFlags.any (fun b => !b))
      | .single v =>
        if !Nat.blt v ds.length || !Nat.beq vf.length ds.length then
          false
        else
          match getElem? zstFlags v with
          | some b => b
          | none => false
      | .scalar _ _ | .niche _ _ _ _ _ _ _ _ _ => false
    | .tuple fs => areAllZeroSizedTys fs
    | .array elemTy len => Nat.beq len 0 || isZeroSizedTy elemTy
    | _ => false

  /-- True iff every type in `tys` is a 0-byte ZST. -/
  noncomputable def areAllZeroSizedTys : List MirTy → Bool
    | [] => true
    | ty :: tys => isZeroSizedTy ty && areAllZeroSizedTys tys

  /-- Per-variant ZST flag list (`areAllZeroSizedTys` mapped structurally). -/
  noncomputable def variantZeroSizedFlags : List (List MirTy) → List Bool
    | [] => []
    | fs :: fss => areAllZeroSizedTys fs :: variantZeroSizedFlags fss
end

/-- Follow a field/element index path `path` inside a `MirTy` to resolve the
leaf scalar type of an `EnumTagRepr.niche` layout. -/
noncomputable def nicheResolveFromTy : MirTy → List Nat → Option MirTy
  | ty, [] => some ty
  | .adtStruct sty, idx :: rest =>
    match getElem? sty.fields idx with
    | some fTy => nicheResolveFromTy fTy rest
    | none => none
  | .tuple fs, idx :: rest =>
    match getElem? fs idx with
    | some fTy => nicheResolveFromTy fTy rest
    | none => none
  | .array elemTy len, idx :: rest =>
    if Nat.blt idx len then nicheResolveFromTy elemTy rest else none
  | _, _ :: _ => none

/-- Resolve a non-empty `nichePath` starting from the payload fields of an
`untagged` enum variant. -/
noncomputable def nicheLeafTy? (nichePath : List Nat) (varFields : List MirTy) :
    Option MirTy :=
  match nichePath with
  | [] => none
  | idx :: rest =>
    match getElem? varFields idx with
    | some fTy => nicheResolveFromTy fTy rest
    | none => none

/-- Check that the leaf type reached by `nichePath` carries a scalar tag with
primitive integer representation `(tagW, tagS)`. -/
noncomputable def nicheLeafMatchesTag (tagW : IntWidth) (tagS : Bool) :
    MirTy → Bool
  | .bool => IntWidth.beq tagW .i8 && !tagS
  | .int w s => IntWidth.beq w tagW && (s == tagS)
  | .enum innerEty =>
    match innerEty.tagRepr with
    | .scalar w s =>
      !hasEnumPayloadFields innerEty && IntWidth.beq w tagW && (s == tagS)
    | _ => false
  | _ => false

/-- Check via `@Nat.rec` that every niche tag `nicheStart + k` (`0 ≤ k < count`)
truncated to `tagW` lies inside the wrapping valid range `[vs, ve]`. -/
noncomputable def allNicheTagsInValidRange (tagW : IntWidth)
    (vs ve nicheStart : BitVec 128) (count : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun k ih =>
      ih &&
        wrappingRangeContains vs ve
          (truncateBits tagW (BitVec.ofNat 128 k + nicheStart)))
    count

/-- Check via `@Nat.rec` that every variant `k < total` with `k ≠ singleVar` is
uninhabited (`Variants::Single { index: singleVar }`). -/
noncomputable def otherVariantsUninhabited (ety : EnumTy) (singleVar : Nat)
    (total : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun k ih => ih && (Nat.beq k singleVar || isVariantUninhabited ety k))
    total

/-- Check via `@Nat.rec` that every variant `k < total` with `k ≠ untagged` is
either uninhabited or niche-encoded (`start ≤ k ≤ last` with ZST-only fields).
-/
noncomputable def otherVariantsValidForNiche (ety : EnumTy)
    (untagged start last total : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun k ih =>
      let okK : Bool :=
        if Nat.beq k untagged then
          true
        else if isVariantUninhabited ety k then
          true
        else
          Nat.ble start k &&
            Nat.ble k last &&
            match fieldsForVariant? ety k with
            | some fs => areAllZeroSizedTys fs
            | none => false
      ih && okK)
    total

/-- Core non-recursive layout and discriminant invariant of `ety : EnumTy`
(paired with recursive field-type admission in `enumAdmitted`). -/
noncomputable def enumAdmittedCore (ety : EnumTy) : Bool :=
  !ety.discriminants.isEmpty &&
    Nat.blt ety.discriminants.length (Nat.pow 2 32) &&
    Nat.beq ety.variantFields.length ety.discriminants.length &&
    ety.discriminants.all (fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth)) &&
    natListPairwiseNe ety.discriminants &&
    match ety.tagRepr with
    | .zeroSized =>
      Nat.beq ety.discriminants.length 1 && !hasEnumPayloadFields ety
    | .single v =>
      Nat.blt v ety.discriminants.length &&
        otherVariantsUninhabited ety v ety.discriminants.length
    | .scalar tagW tagS =>
      ety.discriminants.all (fun d =>
        let dBits := BitVec.ofNat 128 d
        tagBitsToDiscrBits tagW tagS ety.discrWidth
          (truncateBits tagW dBits) == dBits)
    | .niche tagW tagS vs ve nichePath untagged start last nicheStart =>
      !nichePath.isEmpty &&
        Nat.blt untagged ety.discriminants.length &&
        Nat.blt last ety.discriminants.length &&
        Nat.ble start last &&
        (truncateBits tagW vs == vs) &&
        (truncateBits tagW ve == ve) &&
        (truncateBits tagW nicheStart == nicheStart) &&
        Nat.blt (last - start) (Nat.pow 2 tagW.bitWidth) &&
        allNicheTagsInValidRange tagW vs ve nicheStart (last - start + 1) &&
        otherVariantsValidForNiche ety untagged start last
          ety.discriminants.length &&
        match fieldsForVariant? ety untagged with
        | none => false
        | some uFields =>
          match nicheLeafTy? nichePath uFields with
          | some leafTy => nicheLeafMatchesTag tagW tagS leafTy
          | none => false

mutual
  /-- Check whether `ty` belongs to the supported local-variable type fragment
  (`.bool`, `.int`, `.unit`, `.never`, `.adtStruct`, admitted `.enum`,
  non-empty `.tuple`, or fixed `.array` with `len < 2^64`). -/
  noncomputable def isSupportedScalarOrUnitTy : MirTy → Bool
    | .bool | .int _ _ | .unit | .never => true
    | .adtStruct ⟨_, fs⟩ => areSupportedFieldTys fs
    | .enum ⟨id, dw, ds, tr, d, vf⟩ =>
      enumAdmittedCore ⟨id, dw, ds, tr, d, vf⟩ &&
        areSupportedVariantFieldLists vf
    | .tuple fields => !fields.isEmpty && areSupportedFieldTys fields
    | .array elemTy len =>
      Nat.blt len (Nat.pow 2 64) && isSupportedScalarOrUnitTy elemTy
    | _ => false

  /-- Check that every type in a field list belongs to the supported
  local-variable type fragment (`isSupportedScalarOrUnitTy`). -/
  noncomputable def areSupportedFieldTys : List MirTy → Bool
    | [] => true
    | ty :: tys => isSupportedScalarOrUnitTy ty && areSupportedFieldTys tys

  /-- Check that every variant's field list belongs to the supported
  local-variable type fragment. -/
  noncomputable def areSupportedVariantFieldLists : List (List MirTy) → Bool
    | [] => true
    | fs :: fss =>
      areSupportedFieldTys fs && areSupportedVariantFieldLists fss
end

/-- Check that an enum descriptor `ety : EnumTy` is statically well-formed and
every payload field type belongs to the supported type fragment. -/
noncomputable def enumAdmitted (ety : EnumTy) : Bool :=
  enumAdmittedCore ety && areSupportedVariantFieldLists ety.variantFields

/-- Check whether `ety` is an admitted 0-byte ZST 1-variant fieldless enum
(`Variants::Single { index: 0 }`). -/
noncomputable def isZstEnumTy (ety : EnumTy) : Bool :=
  match ety.tagRepr with
  | .zeroSized => enumAdmitted ety
  | _ => false

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

/-- Decode a niche-encoded tag bit pattern `bits` at width `tagW` into a
variant index, matching the `TagEncoding::Niche` arm of
`Miri.Interpreter.Discriminant.readDiscriminant`
(`vendor/lean-miri/Miri/Interpreter/Discriminant.lean`). -/
noncomputable def decodeNicheTagBits (tagW : IntWidth)
    (validStart validEnd : BitVec 128) (untagged start last : Nat)
    (nicheStart : BitVec 128) (variantCount : Nat)
    (bits : BitVec 128) : Except FaultKind Nat :=
  let cleanBits := truncateBits tagW bits
  let relative := truncateBits tagW (cleanBits - nicheStart)
  if Nat.ble relative.toNat (last - start) then
    let index := start + relative.toNat
    if !Nat.blt index (Nat.pow 2 32) || !Nat.blt index variantCount then
      .error .unsupported
    else if !wrappingRangeContains validStart validEnd cleanBits then
      .error .unsupported
    else if Nat.beq index untagged then
      .error .undefined
    else
      .ok index
  else if !wrappingRangeContains validStart validEnd cleanBits then
    .error .undefined
  else
    .ok untagged

/-- Canonical boundary value used in `Query`, `Out`, and `TerminalOut` of
$M_{\text{anneal}}$. -/
inductive Val where
  | scalar (v : ScalarVal)
  | ptr (p : PtrVal)
  | bool (b : Bool)
  | unit
  | structVal (sty : StructTy) (fields : List Val)
  | enumVal (ty : EnumTy) (variant : Nat) (fields : List Val)
  | tuple (fields : List Val)
  | array (elemTy : MirTy) (elems : List Val)
  | bytes (data : List AllocByte)

/-- Extract the raw scalar bits at `path` inside a `Val` for niche tag
validation. -/
noncomputable def extractValNicheBits : Val → List Nat → Option (BitVec 128)
  | .bool b, [] => some (BitVec.ofNat 128 (if b then 1 else 0))
  | .scalar sv, [] => some (truncateBits sv.width sv.bits)
  | .enumVal innerEty innerVar [], [] =>
    match innerEty.tagRepr, getElem? innerEty.discriminants innerVar with
    | .scalar w _, some d => some (truncateBits w (BitVec.ofNat 128 d))
    | _, _ => none
  | .structVal _ fs, idx :: rest =>
    match getElem? fs idx with
    | some fVal => extractValNicheBits fVal rest
    | none => none
  | .tuple fs, idx :: rest =>
    match getElem? fs idx with
    | some fVal => extractValNicheBits fVal rest
    | none => none
  | .array _ elems, idx :: rest =>
    match getElem? elems idx with
    | some eVal => extractValNicheBits eVal rest
    | none => none
  | _, _ => none

/-- Extract the raw scalar bits along non-empty `nichePath` inside `fields :
List Val`. -/
noncomputable def extractValNicheBitsFromFields (nichePath : List Nat)
    (fields : List Val) : Option (BitVec 128) :=
  match nichePath with
  | [] => none
  | idx :: rest =>
    match getElem? fields idx with
    | some fVal => extractValNicheBits fVal rest
    | none => none

/-- Check whether `fields : List Val` satisfies any niche-tag validity
constraint of `ety` at `variant`. -/
noncomputable def enumValNicheValid (ety : EnumTy) (variant : Nat)
    (fields : List Val) : Bool :=
  match ety.tagRepr with
  | .niche tagW _ vs ve nichePath untagged start last nicheStart =>
    if Nat.beq variant untagged then
      match extractValNicheBitsFromFields nichePath fields with
      | none => false
      | some bits =>
        match decodeNicheTagBits tagW vs ve untagged start last nicheStart
            ety.discriminants.length bits with
        | .ok decoded => Nat.beq decoded untagged
        | .error _ => false
    else
      Nat.ble start variant && Nat.ble variant last
  | .single v => Nat.beq variant v
  | .zeroSized => Nat.beq variant 0
  | .scalar _ _ => true

namespace Val

mutual
  /-- Intrinsic type and well-formedness of a runtime value `Val`: returns
  `some ty` iff `v` is a well-formed scalar, boolean, unit, struct, enum,
  non-empty tuple, or fixed array value of supported type `ty`. -/
  noncomputable def ty? : Val → Option MirTy
    | .scalar sv => if sv.wf then some (.int sv.width sv.signed) else none
    | .bool _ => some .bool
    | .unit => some .unit
    | .structVal sty fields =>
      if !areSupportedFieldTys sty.fields || isTypeUninhabited (.adtStruct sty)
      then
        none
      else
        match tys? fields with
        | some tys =>
          if MirTy.beqList tys sty.fields then some (.adtStruct sty) else none
        | none => none
    | .enumVal ety v fields =>
      if !enumAdmitted ety || isVariantUninhabited ety v ||
          !enumValNicheValid ety v fields then
        none
      else
        match fieldsForVariant? ety v, tys? fields with
        | some expectedTys, some actualTys =>
          if MirTy.beqList actualTys expectedTys then
            some (.enum ety)
          else
            none
        | _, _ => none
    | .tuple fields =>
      if fields.isEmpty then
        none
      else
        match tys? fields with
        | some tys => some (.tuple tys)
        | none => none
    | .array elemTy elems =>
      if !isSupportedScalarOrUnitTy elemTy ||
          !Nat.blt elems.length (Nat.pow 2 64) ||
          (!Nat.beq elems.length 0 && isTypeUninhabited elemTy) then
        none
      else if !checkElemsHaveTy elemTy elems then
        none
      else
        some (.array elemTy elems.length)
    | _ => none

  /-- Intrinsic types of a list of values, in order: `some tys` iff every
  value has a type (`Val.ty?`). -/
  noncomputable def tys? : List Val → Option (List MirTy)
    | [] => some []
    | v :: vs =>
      match ty? v, tys? vs with
      | some ty, some tys => some (ty :: tys)
      | _, _ => none

  /-- Check that every element of `elems` has intrinsic type `elemTy`. -/
  noncomputable def checkElemsHaveTy (elemTy : MirTy) : List Val → Bool
    | [] => true
    | v :: vs =>
      match ty? v with
      | some vTy => MirTy.beq vTy elemTy && checkElemsHaveTy elemTy vs
      | none => false
end

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

/-- Contents of a live local slot: a `Val` in which any part may be
uninitialized.

`SlotVal` has one constructor for each constructor of `Val`, plus `.uninit`
for storage that holds no value. A tuple slot is always `.tuple fields` with
one `SlotVal` per field, so each field carries its own initialization state:
`move (_8.1: bool)` leaves `_8` as `.tuple [.scalar x, .uninit]`, and a later
`move (_8.0: usize)` still reads `x`. This is the only representation of a
live slot. A wholly uninitialized tuple is the `.tuple` of its uninitialized
fields (`uninitSlotVal`), never a bare `.uninit`.

`Val.toSlotVal` embeds every `Val` as a fully initialized `SlotVal`, and
`SlotVal.toVal?` recovers it; `SlotVal.toVal?` returns `none` exactly when
some part of the slot is `.uninit`. -/
inductive SlotVal where
  | uninit
  | scalar (v : ScalarVal)
  | ptr (p : PtrVal)
  | bool (b : Bool)
  | unit
  | structVal (sty : StructTy) (fields : List SlotVal)
  | enumVal (ty : EnumTy) (variant : Nat) (fields : List SlotVal)
  | enumUntagged (ty : EnumTy) (variant : Nat) (fields : List SlotVal)
  | tuple (fields : List SlotVal)
  | array (elemTy : MirTy) (elems : List SlotVal)
  | bytes (data : List AllocByte)

mutual
  /-- Embed a value as fully initialized slot contents. -/
  noncomputable def Val.toSlotVal : Val → SlotVal
    | .scalar v => .scalar v
    | .ptr p => .ptr p
    | .bool b => .bool b
    | .unit => .unit
    | .structVal sty fields => .structVal sty (Val.toSlotVals fields)
    | .enumVal ty variant fields =>
      .enumVal ty variant (Val.toSlotVals fields)
    | .tuple fields => .tuple (Val.toSlotVals fields)
    | .array elemTy elems => .array elemTy (Val.toSlotVals elems)
    | .bytes data => .bytes data

  /-- Embed each value of a list as fully initialized slot contents. -/
  noncomputable def Val.toSlotVals : List Val → List SlotVal
    | [] => []
    | v :: vs => Val.toSlotVal v :: Val.toSlotVals vs
end

mutual
  /-- Read slot contents as a value: `some v` iff every part of the slot is
  initialized (and, for enums, has an active discriminant tag rather than
  `enumUntagged`), and `none` if any part is `.uninit` or untagged. -/
  noncomputable def SlotVal.toVal? : SlotVal → Option Val
    | .uninit => none
    | .enumUntagged _ _ _ => none
    | .scalar v => some (.scalar v)
    | .ptr p => some (.ptr p)
    | .bool b => some (.bool b)
    | .unit => some .unit
    | .structVal sty fields =>
      match SlotVal.toVals? fields with
      | some vs => some (.structVal sty vs)
      | none => none
    | .enumVal ty variant fields =>
      match SlotVal.toVals? fields with
      | some vs => some (.enumVal ty variant vs)
      | none => none
    | .tuple fields =>
      match SlotVal.toVals? fields with
      | some vs => some (.tuple vs)
      | none => none
    | .array elemTy elems =>
      match SlotVal.toVals? elems with
      | some vs => some (.array elemTy vs)
      | none => none
    | .bytes data => some (.bytes data)

  /-- Read each slot of a list as a value: `some vs` iff every slot is fully
  initialized. -/
  noncomputable def SlotVal.toVals? : List SlotVal → Option (List Val)
    | [] => some []
    | sv :: svs =>
      match SlotVal.toVal? sv, SlotVal.toVals? svs with
      | some v, some vs => some (v :: vs)
      | _, _ => none
end

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
- `live val`: Storage is allocated (`StorageLive`) and holds `val`. A scalar
  slot that holds no value is `live .uninit`
  (`LocalValue::Live(Operand::Immediate(Immediate::Uninit))`); see `SlotVal`
  for tuples. -/
inductive LocalSlot where
  | dead
  | live (val : SlotVal)

/-- Caller-frame return and unwind continuation saved on every non-root callee
frame, corresponding to `ReturnContinuation::Goto { ret, unwind }` paired with
`Frame::return_place` (`compiler/rustc_const_eval/src/interpret/stack.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
structure ReturnContinuation where
  dst : Place
  target : Option BasicBlockId
  unwind : UnwindAction

/-- Active execution frame of $M_{\text{anneal}}$, corresponding to
`rustc_const_eval::interpret::Frame`
(`compiler/rustc_const_eval/src/interpret/stack.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`).

`returnCont` is `none` on the root entry frame and `some cont` on every callee
frame pushed by `TerminatorKind.call`. -/
structure FrameState where
  defId : DefId
  blockIdx : BasicBlockId
  stmtIdx : Nat
  locals : List LocalSlot
  returnCont : Option ReturnContinuation := none

/-- Running machine state of $M_{\text{anneal}}$ (factored cleanly from
`initState` so `State` carries only active execution frames and caller
memory, with no synthetic pre-entry variant).

`frames` stores the active call stack with the current (innermost) frame at
the head (`frame :: callers`), the root entry frame at the tail
(`returnCont = none`), and every non-root callee frame carrying
`returnCont = some cont`. -/
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

/-- Replicate `v : Val` `n` times via `@Nat.rec` (avoiding `_unsafe_rec`
helpers). -/
noncomputable def replicateVal (n : Nat) (v : Val) : List Val :=
  @Nat.rec (fun _ => List Val) [] (fun _ ih => v :: ih) n

/-- Replicate `sv : SlotVal` `n` times via `@Nat.rec` (avoiding `_unsafe_rec`
helpers). -/
noncomputable def replicateSlotVal (n : Nat) (sv : SlotVal) : List SlotVal :=
  @Nat.rec (fun _ => List SlotVal) [] (fun _ ih => sv :: ih) n

mutual
  /-- Contents of a newly live slot of type `ty` that no statement has written
  yet.

  In `rustc_const_eval`
  (`compiler/rustc_const_eval/src/interpret/discriminant.rs`, `rust-lang/rust`
  `8144389c895da997dbdecaa635e41d6a50be6ffd`) and `lean-miri`
  (`Miri/Interpreter/Immediate.lean`, `OperandMachine.lean`, and
  `Discriminant.lean`), an inhabited 0-byte ZST (`MirTy.unit`, a ZST struct,
  `[T; 0]`, or an admitted `.zeroSized` / ZST `.single` enum) requires zero
  initialized bytes in memory. Compound struct, tuple, array, and `.single`
  enum slots recursively initialize their subfields with `uninitSlotVal` so
  ZST subfields start inhabited while non-ZST subfields start `.uninit`. -/
  noncomputable def uninitSlotVal : MirTy → SlotVal
    | .unit => .unit
    | .adtStruct ⟨id, fs⟩ => .structVal ⟨id, fs⟩ (uninitSlotVals fs)
    | .enum ⟨id, dw, ds, tr, d, vf⟩ =>
      let ety : EnumTy := ⟨id, dw, ds, tr, d, vf⟩
      let initVfs := uninitVariantSlotLists vf
      match tr with
      | .zeroSized =>
        if enumAdmittedCore ety && areSupportedVariantFieldLists vf then
          .enumVal ety 0 []
        else
          .uninit
      | .single v =>
        if !(enumAdmittedCore ety && areSupportedVariantFieldLists vf) ||
            isTypeUninhabited (.enum ety) then
          .uninit
        else
          match getElem? initVfs v with
          | some initFs => .enumVal ety v initFs
          | none => .uninit
      | _ => .uninit
    | .tuple fields => .tuple (uninitSlotVals fields)
    | .array elemTy len =>
      .array elemTy (replicateSlotVal len (uninitSlotVal elemTy))
    | _ => .uninit

  /-- Contents of newly live fields, one per field type (`uninitSlotVal`). -/
  noncomputable def uninitSlotVals : List MirTy → List SlotVal
    | [] => []
    | ty :: tys => uninitSlotVal ty :: uninitSlotVals tys

  /-- Contents of newly live variant field lists (`uninitSlotVals`). -/
  noncomputable def uninitVariantSlotLists :
      List (List MirTy) → List (List SlotVal)
    | [] => []
    | fs :: fss => uninitSlotVals fs :: uninitVariantSlotLists fss
end

/-- Initial state of a newly live local slot of type `ty`: allocated storage
holding `uninitSlotVal ty`. -/
noncomputable def liveUninitSlot (ty : MirTy) : LocalSlot :=
  .live (uninitSlotVal ty)

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
- `_1 .. _argumentCount` (parameters): `.live arg.toSlotVal`.
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
          | some v => .live v.toSlotVal
          | none => .dead
        else if hasStorageAnnotation body idx then
          .dead
        else
          liveUninitSlot ty
      slot :: initLocalsLoop body args (idx + 1) rest

/-- Static body-entry admission predicate shared by `initState` and
`TerminatorKind.call`: checks non-empty basic blocks,
`argumentCount < locals.length`, in-bounds storage annotations, and supported
local types (`isSupportedScalarOrUnitTy`). -/
noncomputable def bodyEntryAdmitted (body : Body) : Bool :=
  !body.basicBlocks.isEmpty &&
    Nat.blt body.argumentCount body.locals.length &&
    storageAnnotationsInBounds body &&
    body.locals.all isSupportedScalarOrUnitTy

/-- Entry initialization (`initState p q`):
Validates the 64-bit target layout (`p.pointerWidthBits = 64`), the MIR
semantic profile version (`p.mirProfileVersion = 1`; see
`Trusted.MirAst.Program`), entry body existence, `bodyEntryAdmitted`, empty
`callerMem`, and well-typed `q.args`. Returns `.error .unsupported` if any
static/entry precondition fails. -/
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
      if !bodyEntryAdmitted body then
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
  | .adtStruct sty, .zeroSized =>
    if areSupportedFieldTys sty.fields && areAllZeroSizedTys sty.fields &&
        !isTypeUninhabited (.adtStruct sty) then
      match (uninitSlotVal (.adtStruct sty)).toVal? with
      | some v => .ok v
      | none => .error .unsupported
    else
      .error .unsupported
  | .array elemTy 0, .zeroSized =>
    if isSupportedScalarOrUnitTy elemTy then
      .ok (.array elemTy [])
    else
      .error .unsupported
  | .enum ety, .zeroSized =>
    if isZstEnumTy ety then
      .ok (.enumVal ety 0 [])
    else
      match ety.tagRepr with
      | .single v₀ =>
        if enumAdmitted ety && !isVariantUninhabited ety v₀ then
          match fieldsForVariant? ety v₀ with
          | some [] => .ok (.enumVal ety v₀ [])
          | _ => .error .unsupported
        else
          .error .unsupported
      | _ => .error .unsupported
  | .enum ety, .scalar bits =>
    if !enumAdmitted ety then
      .error .unsupported
    else
      match ety.tagRepr with
      | .scalar tagW tagS =>
        if truncateBits tagW bits != bits then
          .error .unsupported
        else
          let discrBits := tagBitsToDiscrBits tagW tagS ety.discrWidth bits
          match findDiscrVariant? discrBits ety.discriminants with
          | some v =>
            if isVariantUninhabited ety v then
              .error .undefined
            else
              match fieldsForVariant? ety v with
              | some [] => .ok (.enumVal ety v [])
              | _ => .error .unsupported
          | none => .error .undefined
      | .niche tagW _ vs ve _ untagged start last nicheStart =>
        if truncateBits tagW bits != bits then
          .error .unsupported
        else
          match decodeNicheTagBits tagW vs ve untagged start last nicheStart
              ety.discriminants.length bits with
          | .error k => .error k
          | .ok v =>
            if isVariantUninhabited ety v then
              .error .undefined
            else
              match fieldsForVariant? ety v with
              | some [] => .ok (.enumVal ety v [])
              | _ => .error .unsupported
      | _ => .error .unsupported
  | _, _ => .error .unsupported

/-- Intermediate projected place type matching `rustc_middle::mir::tcx::PlaceTy`
(`compiler/rustc_middle/src/mir/tcx.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`): either a standalone type `.ty t`
or a downcasted enum variant `.variant ety variantIdx` awaiting `.field`. -/
inductive PlaceTy where
  | ty (t : MirTy)
  | variant (ety : EnumTy) (variantIdx : Nat)

/-- Step-by-step static type projection over `PlaceTy` for `.field`,
`.downcast`, `.constantIndex`, and `.index`. -/
noncomputable def projectPlaceTy? :
    PlaceTy → List ProjectionElem → Option PlaceTy
  | pty, [] => some pty
  | .ty (.tuple fieldTys), .field idx fieldTy :: rest =>
    match getElem? fieldTys idx with
    | some ty' =>
      if MirTy.beq ty' fieldTy then projectPlaceTy? (.ty ty') rest else none
    | none => none
  | .ty (.adtStruct sty), .field idx fieldTy :: rest =>
    match getElem? sty.fields idx with
    | some ty' =>
      if MirTy.beq ty' fieldTy then projectPlaceTy? (.ty ty') rest else none
    | none => none
  | .variant ety v, .field idx fieldTy :: rest =>
    match fieldsForVariant? ety v with
    | some varFields =>
      match getElem? varFields idx with
      | some ty' =>
        if MirTy.beq ty' fieldTy then projectPlaceTy? (.ty ty') rest else none
      | none => none
    | none => none
  | .ty (.enum ety), .downcast v :: rest =>
    if enumAdmitted ety && Nat.blt v ety.discriminants.length then
      projectPlaceTy? (.variant ety v) rest
    else
      none
  | .ty (.array elemTy len), .constantIndex _ _ _ :: rest =>
    if Nat.blt len (Nat.pow 2 64) then
      projectPlaceTy? (.ty elemTy) rest
    else
      none
  | .ty (.array elemTy len), .index _ :: rest =>
    if Nat.blt len (Nat.pow 2 64) then
      projectPlaceTy? (.ty elemTy) rest
    else
      none
  | _, _ :: _ => none

/-- Static type of the place reached from `ty` by `proj`, or `none` if `proj`
is ill-typed or ends in a bare `.downcast` without a subsequent `.field`. -/
noncomputable def projectTy? (ty : MirTy) (proj : List ProjectionElem) :
    Option MirTy :=
  match projectPlaceTy? (.ty ty) proj with
  | some (.ty resTy) => some resTy
  | _ => none

/-- Evaluate `ProjectionElem.constantIndex offset minLength fromEnd` on an
array of length `len` (`len < 2^64`), matching `Miri.Interpreter.project` and
`Miri.Interpreter.projectConstantIndex`
(`vendor/lean-miri/Miri/Interpreter/Projection.lean`):
- `offset >= 2^64` or `minLength >= 2^64`: `.error .unsupported`;
- `len < minLength`: `.error .undefined` (`ProjectionError.bounds`);
- `fromEnd = true`: checks `offset > 0` and `offset <= minLength`
  (`.unsupported` otherwise) and `offset <= len` (`.undefined` otherwise)
  before subtracting `len - offset` (preventing `Nat` subtraction saturation);
- `fromEnd = false`: checks `offset < minLength` (`.unsupported` otherwise) and
  `offset < len` (`.undefined` otherwise). -/
noncomputable def evalConstantIndex (len offset minLength : Nat)
    (fromEnd : Bool) : Except FaultKind Nat :=
  if !Nat.blt offset (Nat.pow 2 64) ||
      !Nat.blt minLength (Nat.pow 2 64) then
    .error .unsupported
  else if Nat.blt len minLength then
    .error .undefined
  else if fromEnd then
    if Nat.beq offset 0 || Nat.blt minLength offset then
      .error .unsupported
    else if Nat.blt len offset then
      .error .undefined
    else
      .ok (len - offset)
  else if !Nat.blt offset minLength then
    .error .unsupported
  else if !Nat.blt offset len then
    .error .undefined
  else
    .ok offset

/-- Validate and canonicalize an already-static projection path (without
dynamic `.index` elements) against `pty : PlaceTy`, used when writing a callee
return value into a `ReturnContinuation.dst` whose dynamic indices were already
resolved at call entry. -/
noncomputable def resolveStaticProjPath :
    PlaceTy → List ProjectionElem → Except FaultKind (List ProjectionElem)
  | .ty _, [] => .ok []
  | .variant _ _, [] => .error .unsupported
  | .ty (.tuple fieldTys), .field idx fieldTy :: rest =>
    match getElem? fieldTys idx with
    | some ty' =>
      if MirTy.beq ty' fieldTy then
        match resolveStaticProjPath (.ty ty') rest with
        | .ok rest' => .ok (.field idx fieldTy :: rest')
        | .error k => .error k
      else
        .error .unsupported
    | none => .error .unsupported
  | .ty (.adtStruct sty), .field idx fieldTy :: rest =>
    match getElem? sty.fields idx with
    | some ty' =>
      if MirTy.beq ty' fieldTy then
        match resolveStaticProjPath (.ty ty') rest with
        | .ok rest' => .ok (.field idx fieldTy :: rest')
        | .error k => .error k
      else
        .error .unsupported
    | none => .error .unsupported
  | .variant ety v, .field idx fieldTy :: rest =>
    match fieldsForVariant? ety v with
    | some varFields =>
      match getElem? varFields idx with
      | some ty' =>
        if MirTy.beq ty' fieldTy then
          match resolveStaticProjPath (.ty ty') rest with
          | .ok rest' => .ok (.field idx fieldTy :: rest')
          | .error k => .error k
        else
          .error .unsupported
      | none => .error .unsupported
    | none => .error .unsupported
  | .ty (.enum ety), .downcast v :: rest =>
    if enumAdmitted ety && Nat.blt v ety.discriminants.length then
      match resolveStaticProjPath (.variant ety v) rest with
      | .ok rest' => .ok (.downcast v :: rest')
      | .error k => .error k
    else
      .error .unsupported
  | .ty (.array elemTy len), .constantIndex offset minLength fromEnd :: rest =>
    if !Nat.blt len (Nat.pow 2 64) then
      .error .unsupported
    else
      match evalConstantIndex len offset minLength fromEnd with
      | .error k => .error k
      | .ok idx =>
        match resolveStaticProjPath (.ty elemTy) rest with
        | .ok rest' => .ok (.constantIndex idx (idx + 1) false :: rest')
        | .error k => .error k
  | _, _ :: _ => .error .unsupported

/-- Resolve dynamic `.index` and `.constantIndex` steps along `proj` into
canonical in-bounds `.constantIndex idx (idx + 1) false` steps, reading each
`idxLocal` as a `usize` without moving it (matching `Miri.Interpreter.project`
in `vendor/lean-miri/Miri/Interpreter/Projection.lean`). -/
noncomputable def resolveProjPath (bodyLocals : List MirTy)
    (locals : List LocalSlot) :
    PlaceTy → List ProjectionElem → Except FaultKind (List ProjectionElem)
  | .ty _, [] => .ok []
  | .variant _ _, [] => .error .unsupported
  | .ty (.tuple fieldTys), .field idx fieldTy :: rest =>
    match getElem? fieldTys idx with
    | some ty' =>
      if MirTy.beq ty' fieldTy then
        match resolveProjPath bodyLocals locals (.ty ty') rest with
        | .ok rest' => .ok (.field idx fieldTy :: rest')
        | .error k => .error k
      else
        .error .unsupported
    | none => .error .unsupported
  | .ty (.adtStruct sty), .field idx fieldTy :: rest =>
    match getElem? sty.fields idx with
    | some ty' =>
      if MirTy.beq ty' fieldTy then
        match resolveProjPath bodyLocals locals (.ty ty') rest with
        | .ok rest' => .ok (.field idx fieldTy :: rest')
        | .error k => .error k
      else
        .error .unsupported
    | none => .error .unsupported
  | .variant ety v, .field idx fieldTy :: rest =>
    match fieldsForVariant? ety v with
    | some varFields =>
      match getElem? varFields idx with
      | some ty' =>
        if MirTy.beq ty' fieldTy then
          match resolveProjPath bodyLocals locals (.ty ty') rest with
          | .ok rest' => .ok (.field idx fieldTy :: rest')
          | .error k => .error k
        else
          .error .unsupported
      | none => .error .unsupported
    | none => .error .unsupported
  | .ty (.enum ety), .downcast v :: rest =>
    if enumAdmitted ety && Nat.blt v ety.discriminants.length then
      match resolveProjPath bodyLocals locals (.variant ety v) rest with
      | .ok rest' => .ok (.downcast v :: rest')
      | .error k => .error k
    else
      .error .unsupported
  | .ty (.array elemTy len), .constantIndex offset minLength fromEnd :: rest =>
    if !Nat.blt len (Nat.pow 2 64) then
      .error .unsupported
    else
      match evalConstantIndex len offset minLength fromEnd with
      | .error k => .error k
      | .ok idx =>
        match resolveProjPath bodyLocals locals (.ty elemTy) rest with
        | .ok rest' => .ok (.constantIndex idx (idx + 1) false :: rest')
        | .error k => .error k
  | .ty (.array elemTy len), .index idxLocal :: rest =>
    if !Nat.blt len (Nat.pow 2 64) then
      .error .unsupported
    else
      match getElem? bodyLocals idxLocal, getElem? locals idxLocal with
      | some (.int .isize false), some (.live (.scalar sv)) =>
        let idx := (truncateBits .isize sv.bits).toNat
        if Nat.blt idx len then
          match resolveProjPath bodyLocals locals (.ty elemTy) rest with
          | .ok rest' => .ok (.constantIndex idx (idx + 1) false :: rest')
          | .error k => .error k
        else
          .error .undefined
      | some (.int .isize false), some (.live .uninit) => .error .undefined
      | some (.int .isize false), some .dead => .error .undefined
      | _, _ => .error .unsupported
  | _, _ :: _ => .error .unsupported

/-- Read the subslot of `sv` selected by a canonicalized projection `proj`
starting at `pty : PlaceTy`. -/
noncomputable def readPlaceSlotPath? :
    PlaceTy → SlotVal → List ProjectionElem → Option SlotVal
  | .ty _, sv, [] => some sv
  | .variant _ _, _, [] => none
  | .ty (.tuple fieldTys), .tuple fields, .field idx _ :: rest =>
    match getElem? fieldTys idx, getElem? fields idx with
    | some fTy, some field => readPlaceSlotPath? (.ty fTy) field rest
    | _, _ => none
  | .ty (.adtStruct sty), .structVal sty' fields, .field idx _ :: rest =>
    if !StructTy.beq sty sty' then
      none
    else
      match getElem? sty.fields idx, getElem? fields idx with
      | some fTy, some field => readPlaceSlotPath? (.ty fTy) field rest
      | _, _ => none
  | .ty (.enum ety), sv, .downcast v :: rest =>
    if Nat.blt v ety.discriminants.length then
      readPlaceSlotPath? (.variant ety v) sv rest
    else
      none
  | .variant ety v, sv, .field idx _ :: rest =>
    match fieldsForVariant? ety v with
    | none => none
    | some varFields =>
      match getElem? varFields idx with
      | none => none
      | some fTy =>
        match sv with
        | .uninit =>
          readPlaceSlotPath? (.ty fTy) (uninitSlotVal fTy) rest
        | .enumVal ety' v' fields =>
          if !EnumTy.beq ety ety' then
            none
          else if Nat.beq v' v then
            match getElem? fields idx with
            | some field => readPlaceSlotPath? (.ty fTy) field rest
            | none => none
          else
            match fieldsForVariant? ety v' with
            | some activeFieldTys =>
              if areAllZeroSizedTys activeFieldTys then
                readPlaceSlotPath? (.ty fTy) (uninitSlotVal fTy) rest
              else
                none
            | none => none
        | .enumUntagged ety' v' fields =>
          if EnumTy.beq ety ety' && Nat.beq v' v then
            match getElem? fields idx with
            | some field => readPlaceSlotPath? (.ty fTy) field rest
            | none => none
          else
            none
        | _ => none
  | .ty (.array elemTy len), .array elemTy' elems,
      .constantIndex idx _ false :: rest =>
    if !MirTy.beq elemTy elemTy' || !Nat.beq elems.length len then
      none
    else
      match getElem? elems idx with
      | some elem => readPlaceSlotPath? (.ty elemTy) elem rest
      | none => none
  | _, _, _ :: _ => none

/-- Update the subslot of `sv` selected by a canonicalized projection `proj`
starting at `pty : PlaceTy` with `new`, leaving sibling fields and array
elements untouched. Writing through `.downcast v` into `.uninit` or a
different active `enumVal` initializes a partial `.enumUntagged ety v` shell
for variant `v`; writing through `.downcast v` into a mismatched
`.enumUntagged ety v'` (`v' ≠ v`) fails closed (`none`). -/
noncomputable def writePlaceSlotPath? :
    PlaceTy → SlotVal → List ProjectionElem → SlotVal → Option SlotVal
  | .ty _, _, [], new => some new
  | .variant _ _, _, [], _ => none
  | .ty (.tuple fieldTys), .tuple fields, .field idx _ :: rest, new =>
    match getElem? fieldTys idx, getElem? fields idx with
    | some fTy, some field =>
      match writePlaceSlotPath? (.ty fTy) field rest new with
      | some field' =>
        match setElem? fields idx field' with
        | some fields' => some (.tuple fields')
        | none => none
      | none => none
    | _, _ => none
  | .ty (.adtStruct sty), .structVal sty' fields, .field idx _ :: rest, new =>
    if !StructTy.beq sty sty' then
      none
    else
      match getElem? sty.fields idx, getElem? fields idx with
      | some fTy, some field =>
        match writePlaceSlotPath? (.ty fTy) field rest new with
        | some field' =>
          match setElem? fields idx field' with
          | some fields' => some (.structVal sty fields')
          | none => none
        | none => none
      | _, _ => none
  | .ty (.enum ety), sv, .downcast v :: rest, new =>
    if Nat.blt v ety.discriminants.length then
      writePlaceSlotPath? (.variant ety v) sv rest new
    else
      none
  | .variant ety v, sv, .field idx _ :: rest, new =>
    match fieldsForVariant? ety v with
    | none => none
    | some varFields =>
      match getElem? varFields idx with
      | none => none
      | some fTy =>
        match sv with
        | .uninit =>
          let initFields := uninitSlotVals varFields
          match getElem? initFields idx with
          | none => none
          | some field =>
            match writePlaceSlotPath? (.ty fTy) field rest new with
            | some field' =>
              match setElem? initFields idx field' with
              | some fields' => some (.enumUntagged ety v fields')
              | none => none
            | none => none
        | .enumUntagged ety' v' fields =>
          if !(EnumTy.beq ety ety' && Nat.beq v' v) then
            none
          else
            match getElem? fields idx with
            | none => none
            | some field =>
              match writePlaceSlotPath? (.ty fTy) field rest new with
              | some field' =>
                match setElem? fields idx field' with
                | some fields' => some (.enumUntagged ety v fields')
                | none => none
              | none => none
        | .enumVal ety' v' fields =>
          if !EnumTy.beq ety ety' then
            none
          else if Nat.beq v' v then
            match getElem? fields idx with
            | none => none
            | some field =>
              match writePlaceSlotPath? (.ty fTy) field rest new with
              | some field' =>
                match setElem? fields idx field' with
                | some fields' => some (.enumVal ety v fields')
                | none => none
              | none => none
          else
            let initFields := uninitSlotVals varFields
            match getElem? initFields idx with
            | none => none
            | some field =>
              match writePlaceSlotPath? (.ty fTy) field rest new with
              | some field' =>
                match setElem? initFields idx field' with
                | some fields' => some (.enumUntagged ety v fields')
                | none => none
              | none => none
        | _ => none
  | .ty (.array elemTy len), .array elemTy' elems,
      .constantIndex idx _ false :: rest, new =>
    if !MirTy.beq elemTy elemTy' || !Nat.beq elems.length len then
      none
    else
      match getElem? elems idx with
      | some elem =>
        match writePlaceSlotPath? (.ty elemTy) elem rest new with
        | some elem' =>
          match setElem? elems idx elem' with
          | some elems' => some (.array elemTy elems')
          | none => none
        | none => none
      | none => none
  | _, _, _ :: _, _ => none

/-- Read the storage at `place` for `Operand.copy` (`isMove = false`) or
`Operand.move` (`isMove = true`), returning the place's type, its contents,
and the updated locals.

The base local must be declared and live: a dead local faults with
`.undefined` before the projection is examined, matching `local_to_op`, which
`eval_place_to_op` runs before it applies any projection. Dynamic `.index` and
`.constantIndex` projections are then resolved via `resolveProjPath` (faulting
with `.undefined` on out-of-bounds indices or dead/uninitialized index locals),
and `readPlaceSlotPath?` reads the projected subslot. When `isMove = true`,
only that subslot is overwritten with `uninitSlotVal ty`. -/
noncomputable def evalPlaceOperand (bodyLocals : List MirTy)
    (locals : List LocalSlot) (place : Place) (isMove : Bool) :
    Except FaultKind (MirTy × SlotVal × List LocalSlot) :=
  match getElem? bodyLocals place.localId, getElem? locals place.localId with
  | some localTy, some (.live root) =>
    match projectTy? localTy place.projection with
    | none => .error .unsupported
    | some ty =>
      match resolveProjPath bodyLocals locals (.ty localTy)
          place.projection with
      | .error k => .error k
      | .ok resolvedProj =>
        match readPlaceSlotPath? (.ty localTy) root resolvedProj with
        | none => .error .unsupported
        | some sv =>
          if !isMove then
            .ok (ty, sv, locals)
          else
            match writePlaceSlotPath? (.ty localTy) root resolvedProj
                (uninitSlotVal ty) with
            | some root' =>
              match setElem? locals place.localId (.live root') with
              | some locals' => .ok (ty, sv, locals')
              | none => .error .unsupported
            | none => .error .unsupported
  | some _, some .dead => .error .undefined
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
`(ty : MirTy, sv : SlotVal, locals' : List LocalSlot)` without yet requiring
`sv` to be initialized, and deinitializes moved non-ZST storage:
- `.copy place`: reads `(ty, sv)` at `place` without mutating `locals`
  (`evalPlaceOperand` with `isMove = false`).
- `.move place`: reads `(ty, sv)` at `place` and conservatively overwrites the
  storage at `place` with `uninitSlotVal ty` (`evalPlaceOperand` with
  `isMove = true`), matching `OperandMachine.evalOperand` with opt-in
  `deinitMovedPlace = true`.
- `.constant c`: decodes constant literal without mutating `locals`. -/
noncomputable def evalOperandToSlot (bodyLocals : List MirTy)
    (locals : List LocalSlot) :
    Operand → Except FaultKind (MirTy × SlotVal × List LocalSlot)
  | .copy place => evalPlaceOperand bodyLocals locals place false
  | .move place => evalPlaceOperand bodyLocals locals place true
  | .constant c =>
    match evalConstLit c.ty c.lit with
    | .ok v => .ok (c.ty, v.toSlotVal, locals)
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

Used by `.binaryOp`, `.unaryOp`, `.cast`, `.switchInt`, and `.assert`. Checks
`isPrimitiveReadableTy ty` on the static type first (`.unsupported` on
non-primitives such as `.unit`), and then checks initialization
(`sv.toVal? = some v`, faulting with `.undefined` on uninitialized storage). -/
noncomputable def evalPrimitiveOperand (bodyLocals : List MirTy)
    (locals : List LocalSlot) (opnd : Operand) :
    Except FaultKind (Val × List LocalSlot) :=
  match evalOperandToSlot bodyLocals locals opnd with
  | .error k => .error k
  | .ok (ty, sv, locals') =>
    if !isPrimitiveReadableTy ty then
      .error .unsupported
    else
      match sv.toVal? with
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

/-- Evaluate an overflowing integer arithmetic operator (`.addWithOverflow`,
`.subWithOverflow`, `.mulWithOverflow`) to the two-field tuple
`(wrapped, overflowed)`, in lockstep with
`compiler/rustc_const_eval/src/interpret/operator.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.IntegerOps.arithmetic`
(`vendor/lean-miri/Miri/Interpreter/IntegerOps.lean`):

> "let with_overflow = bin_op.is_overflowing();"
> ...
> "let res = ImmTy::from_scalar_int(result, left.layout);
> return interp_ok(if with_overflow {
>     let overflow = ImmTy::from_bool(overflow, *self.tcx);
>     ImmTy::from_pair(res, overflow, self)
> } else {
>     res
> });"
> (`compiler/rustc_const_eval/src/interpret/operator.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

The first field is the mathematical result `result` wrapped to `(w, s)`. The
second field is `true` iff `result` is not representable at `(w, s)`:
`truncateScalar` reports this as `lossy` whenever `result` fits the 128-bit
host integer, and `hostOverflow` covers a `result` outside that host range
(as in `evalArithOp`). These operators never fault on overflow. -/
noncomputable def evalOverflowingArithOp (op : BinOp) (w : IntWidth) (s : Bool)
    (l r : Int) : Except FaultKind Val :=
  let res? : Option Int := match op with
    | .addWithOverflow => some (l + r)
    | .subWithOverflow => some (l - r)
    | .mulWithOverflow => some (l * r)
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
      .ok (.tuple [.scalar val, .bool (hostOverflow || lossy)])

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
  `INT_MIN % -1` as well as `r == 0`.
- `.addWithOverflow`, `.subWithOverflow`, and `.mulWithOverflow` return the
  tuple `.tuple [.scalar wrapped, .bool overflowed]`
  (`evalOverflowingArithOp`) and never fault on overflow. -/
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
      | .addWithOverflow | .subWithOverflow | .mulWithOverflow =>
        evalOverflowingArithOp op w s lInt rInt
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

/-- Evaluate a `CastKind.intToInt` cast of `src` to the integer type `castTy`,
in lockstep with `cast_from_int_like` in
`compiler/rustc_const_eval/src/interpret/cast.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.IntegerCast.cast`
(`vendor/lean-miri/Miri/Interpreter/IntegerCast.lean`):

> "// Let's make sure v is sign-extended *if* it has a signed type.
> let signed = src_layout.backend_repr.is_signed();
> ...
> let v = match src_layout.ty.kind() {
>     ty::Uint(_) | ty::RawPtr(..) | ty::FnPtr(..) =>
>         scalar.to_uint(src_layout.size)?,
>     ty::Int(_) => scalar.to_int(src_layout.size)? as u128,
>     ty::Bool => scalar.to_bool()?.into(),
>     ty::Char => scalar.to_char()?.into(),
>     ...
> };
>
> interp_ok(match *cast_ty.kind() {
>     // int -> int
>     ty::Int(_) | ty::Uint(_) => {
>         let size = match *cast_ty.kind() { ... };
>         let v = size.truncate(v);
>         Scalar::from_uint(v, size)
>     }
>     ...
> })"
> (`compiler/rustc_const_eval/src/interpret/cast.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

- An integer source is widened to 128 bits by sign extension when its type is
  signed and by zero extension otherwise (`bvOfInt 128 (decodeScalar sv)`).
- A `bool` source is widened to `0` (`false`) or `1` (`true`).
- The widened bits are truncated to the target width (`truncateBits w`), so a
  narrowing cast keeps the low bits (`300u64 as u8 = 44u8`).

A target type that is not an integer type, or a source that is neither an
integer nor a `bool`, returns `.error .unsupported`. -/
noncomputable def evalIntToIntCast (src : Val) (castTy : MirTy) :
    Except FaultKind Val :=
  match castTy with
  | .int w s =>
    match src with
    | .scalar sv =>
      .ok (.scalar ⟨w, s, truncateBits w (bvOfInt 128 (decodeScalar sv))⟩)
    | .bool b =>
      .ok (.scalar
        ⟨w, s, truncateBits w (BitVec.ofNat 128 (if b then 1 else 0))⟩)
    | _ => .error .unsupported
  | _ => .error .unsupported

/-- Return `true` iff two non-downcast projection steps may alias the same
subplace: two `.field` steps alias iff they select the same field index, two
`.constantIndex` steps with matching `fromEnd` polarity alias iff their offsets
match, and any other pair is treated conservatively as potentially aliasing. -/
noncomputable def projElemMayAlias : ProjectionElem → ProjectionElem → Bool
  | .field i _, .field j _ => Nat.beq i j
  | .constantIndex o₁ _ false, .constantIndex o₂ _ false => Nat.beq o₁ o₂
  | .constantIndex o₁ _ true, .constantIndex o₂ _ true => Nat.beq o₁ o₂
  | _, _ => true

/-- Return `true` iff projection `p` may be a prefix of projection `q`
(`projElemMayAlias`, treating distinct `.downcast` variants as overlapping in
memory). -/
noncomputable def projPrefixMayAlias :
    List ProjectionElem → List ProjectionElem → Bool
  | [], _ => true
  | _ :: _, [] => false
  | .downcast v₁ :: as, .downcast v₂ :: bs =>
    if Nat.beq v₁ v₂ then projPrefixMayAlias as bs else true
  | .downcast _ :: _, _ :: _ => true
  | _ :: _, .downcast _ :: _ => true
  | a :: as, b :: bs => projElemMayAlias a b && projPrefixMayAlias as bs

/-- Conservative place-overlap predicate: `true` iff `a` and `b` address the
same local and either projection may be a prefix of the other. -/
noncomputable def placesMayOverlap (a b : Place) : Bool :=
  Nat.beq a.localId b.localId &&
    (projPrefixMayAlias a.projection b.projection ||
      projPrefixMayAlias b.projection a.projection)

/-- Return `true` iff `opnd` reads a place that may overlap `dst`. -/
noncomputable def operandMayOverlapPlace (dst : Place) : Operand → Bool
  | .copy src => placesMayOverlap dst src
  | .move src => placesMayOverlap dst src
  | .constant _ => false

/-- Return `true` iff any operand in `ops` reads a place that may overlap
`dst`. -/
noncomputable def anyOperandMayOverlapPlace (dst : Place) :
    List Operand → Bool
  | [] => false
  | opnd :: rest =>
    operandMayOverlapPlace dst opnd || anyOperandMayOverlapPlace dst rest

/-- Return `true` iff `opnd` is a `.move` whose source place may overlap `dst`.
In `rustc` (`compiler/rustc_const_eval/src/interpret/call.rs`,
`move_definitely_disjoint` + `init_stack_frame`) and `lean-miri`
(`Miri/Interpreter/Call.lean`, `moveDefinitelyDisjoint` + `passArgument` +
`protectArgument`), passing a `.move` argument whose local overlaps the call
destination disables `move_definitely_disjoint`, forces the argument in-place,
and applies Tree Borrows / Stacked Borrows protectors to both the moved
argument and `dst`, causing immediate UB even for scalars. -/
noncomputable def moveOperandMayOverlapPlace (dst : Place) : Operand → Bool
  | .move src => placesMayOverlap dst src
  | .copy _ => false
  | .constant _ => false

/-- Return `true` iff any `.move` operand in `ops` may overlap `dst`. -/
noncomputable def anyMoveOperandMayOverlapPlace (dst : Place) :
    List Operand → Bool
  | [] => false
  | opnd :: rest =>
    moveOperandMayOverlapPlace dst opnd ||
      anyMoveOperandMayOverlapPlace dst rest

/-- Return `true` iff `ty` is a tuple type (`MirTy.tuple _`). -/
noncomputable def isTupleTy : MirTy → Bool
  | .tuple _ => true
  | _ => false

/-- Return `true` iff `ty` is a compound destination type whose `Rvalue.use`
rejects overlapping source/destination places (`.tuple`, non-ZST `.adtStruct`,
non-ZST payload `.enum`, or non-ZST `.array`). -/
noncomputable def isCompoundOverlapProtectedTy (ty : MirTy) : Bool :=
  match ty with
  | .tuple _ => true
  | .adtStruct _ | .array _ _ => !isZeroSizedTy ty
  | .enum ety => !isZeroSizedTy (.enum ety) && hasEnumPayloadFields ety
  | _ => false

/-- Fail-closed aliasing guard for `StatementKind.assign dst rvalue` at
destination type `dstTy`:
- `Rvalue.use opnd` on a compound non-ZST destination (`.tuple`, non-ZST
  `.adtStruct`, non-ZST payload `.enum`, or non-ZST `.array`) whose operand
  overlaps `dst`.
- `Rvalue.aggregate _ ops` where any operand overlaps `dst` (across all
  aggregate kinds: `.tuple`, `.adtStruct`, `.adtEnum`, and `.array`).

Returning `true` causes `evalStatement` to fault with `.fault .unsupported`
before evaluating any operand or writing `dst`. -/
noncomputable def assignHasUnsupportedOverlap (dst : Place) (dstTy : MirTy) :
    Rvalue → Bool
  | .use opnd =>
    isCompoundOverlapProtectedTy dstTy && operandMayOverlapPlace dst opnd
  | .aggregate _ ops => anyOperandMayOverlapPlace dst ops
  | .repeat_ opnd _ => operandMayOverlapPlace dst opnd
  | _ => false

/-- Extract the raw scalar bits at `path` inside a `SlotVal` for niche-tag
discriminant reading (`Except FaultKind (BitVec 128)`, faulting with
`.undefined` when the niche scalar is `.uninit`). -/
noncomputable def extractSlotNicheBits :
    SlotVal → List Nat → Except FaultKind (BitVec 128)
  | .uninit, _ => .error .undefined
  | .enumUntagged _ _ _, _ => .error .undefined
  | .bool b, [] => .ok (BitVec.ofNat 128 (if b then 1 else 0))
  | .scalar sv, [] => .ok (truncateBits sv.width sv.bits)
  | .enumVal innerEty innerVar [], [] =>
    match innerEty.tagRepr, getElem? innerEty.discriminants innerVar with
    | .scalar w _, some d => .ok (truncateBits w (BitVec.ofNat 128 d))
    | _, _ => .error .unsupported
  | .structVal _ fs, idx :: rest =>
    match getElem? fs idx with
    | some fSv => extractSlotNicheBits fSv rest
    | none => .error .unsupported
  | .tuple fs, idx :: rest =>
    match getElem? fs idx with
    | some fSv => extractSlotNicheBits fSv rest
    | none => .error .unsupported
  | .array _ elems, idx :: rest =>
    match getElem? elems idx with
    | some eSv => extractSlotNicheBits eSv rest
    | none => .error .unsupported
  | _, _ => .error .unsupported

/-- Extract the raw scalar bits along non-empty `nichePath` inside `fields :
List SlotVal`. -/
noncomputable def extractSlotNicheBitsFromFields (nichePath : List Nat)
    (fields : List SlotVal) : Except FaultKind (BitVec 128) :=
  match nichePath with
  | [] => .error .unsupported
  | idx :: rest =>
    match getElem? fields idx with
    | some fSv => extractSlotNicheBits fSv rest
    | none => .error .unsupported

/-- Read the active 0-based variant index of an admitted enum `ety` from slot
contents `sv`, matching `Miri.Interpreter.Discriminant.readDiscriminant`
(`vendor/lean-miri/Miri/Interpreter/Discriminant.lean`). -/
noncomputable def evalReadDiscriminantVariant (ety : EnumTy) (sv : SlotVal) :
    Except FaultKind Nat :=
  match ety.tagRepr with
  | .zeroSized =>
    let res : Except FaultKind Nat :=
      if isTypeUninhabited (.enum ety) then .error .undefined else .ok 0
    match sv with
    | .uninit => res
    | .enumVal ety' v [] =>
      if EnumTy.beq ety ety' && Nat.beq v 0 then
        res
      else
        .error .unsupported
    | _ => .error .unsupported
  | .single v₀ =>
    let res : Except FaultKind Nat :=
      if isTypeUninhabited (.enum ety) then .error .undefined else .ok v₀
    match sv with
    | .uninit => res
    | .enumVal ety' v _ | .enumUntagged ety' v _ =>
      if EnumTy.beq ety ety' && Nat.beq v v₀ then
        res
      else
        .error .unsupported
    | _ => .error .unsupported
  | .scalar _ _ =>
    match sv with
    | .uninit | .enumUntagged _ _ _ => .error .undefined
    | .enumVal ety' v _ =>
      if EnumTy.beq ety ety' && Nat.blt v ety.discriminants.length then
        if isVariantUninhabited ety v then
          .error .undefined
        else
          .ok v
      else
        .error .unsupported
    | _ => .error .unsupported
  | .niche tagW _ vs ve nichePath untagged start last nicheStart =>
    match sv with
    | .uninit => .error .undefined
    | .enumVal ety' v fields =>
      if !EnumTy.beq ety ety' then
        .error .unsupported
      else if Nat.beq v untagged then
        match extractSlotNicheBitsFromFields nichePath fields with
        | .error k => .error k
        | .ok bits =>
          match decodeNicheTagBits tagW vs ve untagged start last nicheStart
              ety.discriminants.length bits with
          | .error k => .error k
          | .ok idx =>
            if isVariantUninhabited ety idx then
              .error .undefined
            else
              .ok idx
      else if Nat.ble start v && Nat.ble v last then
        if isVariantUninhabited ety v then
          .error .undefined
        else
          .ok v
      else
        .error .unsupported
    | .enumUntagged ety' v fields =>
      if !EnumTy.beq ety ety' then
        .error .unsupported
      else if Nat.beq v untagged then
        match extractSlotNicheBitsFromFields nichePath fields with
        | .error k => .error k
        | .ok bits =>
          match decodeNicheTagBits tagW vs ve untagged start last nicheStart
              ety.discriminants.length bits with
          | .error k => .error k
          | .ok idx =>
            if isVariantUninhabited ety idx then
              .error .undefined
            else
              .ok idx
      else
        .error .undefined
    | _ => .error .unsupported

/-- Evaluate an `Rvalue` for a destination of type `dstTy`, following the RHS
cases of `eval_rvalue_into_place`
(`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.Rvalue.evalRvalueIntoPlace` (`Miri/Interpreter/Rvalue.lean`),
together with Anneal's conservative `Operand.move` deinitialization
(`evalOperandToSlot`). Aggregates (`.aggregate`) are handled directly by
`evalStatement` via `writeAggregate` so each field is written immediately after
evaluating its operand. -/
noncomputable def evalRvalue (bodyLocals : List MirTy) (locals : List LocalSlot)
    (dstTy : MirTy) : Rvalue → Except FaultKind (Val × List LocalSlot)
  | .use opnd =>
    match evalOperandToSlot bodyLocals locals opnd with
    | .error k => .error k
    | .ok (srcTy, sv, locals₁) =>
      if !(MirTy.beq srcTy dstTy) then
        .error .unsupported
      else
        match sv.toVal? with
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
    match evalPlaceOperand bodyLocals locals place false with
    | .error k => .error k
    | .ok (srcTy, sv, locals₁) =>
      match srcTy with
      | .enum ety =>
        if !enumAdmitted ety then
          .error .unsupported
        else
          match evalReadDiscriminantVariant ety sv with
          | .error k => .error k
          | .ok v =>
            match getElem? ety.discriminants v with
            | some disc =>
              .ok (.scalar ⟨ety.discrWidth, ety.discrSigned,
                truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩, locals₁)
            | none => .error .unsupported
      | _ => .error .unsupported
  | .repeat_ opnd count =>
    match dstTy with
    | .array elemTy len =>
      if !Nat.beq count len || !Nat.blt len (Nat.pow 2 64) then
        .error .unsupported
      else
        match evalOperandToSlot bodyLocals locals opnd with
        | .error k => .error k
        | .ok (srcTy, sv, locals₁) =>
          if !(MirTy.beq srcTy elemTy) then
            .error .unsupported
          else if Nat.beq count 0 then
            .ok (.array elemTy [], locals₁)
          else
            match sv.toVal? with
            | none => .error .undefined
            | some v => .ok (.array elemTy (replicateVal count v), locals₁)
    | _ => .error .unsupported
  | .cast kind opnd castTy =>
    match evalPrimitiveOperand bodyLocals locals opnd with
    | .error k => .error k
    | .ok (v, locals₁) =>
      match kind with
      | .unsupported => .error .unsupported
      | .intToInt =>
        if !(MirTy.beq castTy dstTy) then
          .error .unsupported
        else
          match evalIntToIntCast v castTy with
          | .error k => .error k
          | .ok res => .ok (res, locals₁)
  | _ => .error .unsupported

/-- Write `val` into a canonicalized `dst` of type `dstTy` whose base local has
declared type `localTy`: checks `checkVal val dstTy`, checks base-local
liveness, and updates the subslot via `writePlaceSlotPath?`. -/
noncomputable def writePlaceWithLocalTy (localTy : MirTy)
    (locals : List LocalSlot) (dst : Place) (dstTy : MirTy) (val : Val) :
    Except FaultKind (List LocalSlot) :=
  if !checkVal val dstTy then
    .error .unsupported
  else
    match getElem? locals dst.localId with
    | none => .error .unsupported
    | some .dead => .error .undefined
    | some (.live root) =>
      match writePlaceSlotPath? (.ty localTy) root dst.projection
          val.toSlotVal with
      | none => .error .unsupported
      | some root' =>
        match setElem? locals dst.localId (.live root') with
        | some locals' => .ok locals'
        | none => .error .unsupported

/-- Update the active discriminant tag of a resolved destination place
`resolvedDst` (of type `dstTy` inside base local of type `localTy`) to
`variantIdx`, matching `Miri.Interpreter.Discriminant.writeDiscriminant`
(`vendor/lean-miri/Miri/Interpreter/Discriminant.lean`):
- For non-enum `dstTy` (`Variants::Single { index: 0 }`), writing `variantIdx =
  0` on a live inhabited place is a no-op, while uninhabited types, dead
  locals, or `variantIdx ≠ 0` fault with `.error .undefined`
  (`UninhabitedEnumVariantWritten`).
- For enum `dstTy`, uninhabited or out-of-bounds `variantIdx` faults with
  `.error .undefined` (`UninhabitedEnumVariantWritten`).
- On `EnumTagRepr.niche`, setting `untagged` validates that the niche scalar
  inside the current slot already decodes to `untagged` (`.error .undefined`
  otherwise, `InvalidNichedEnumVariantWritten`).
- Preserves payload fields when `curSv` already targets `variantIdx`, and
  initializes `uninitSlotVals varFields` when switching from `.uninit` or a
  different variant. -/
noncomputable def evalSetDiscriminantResolved (localTy : MirTy)
    (locals : List LocalSlot) (resolvedDst : Place) (dstTy : MirTy)
    (variantIdx : Nat) : Except FaultKind (List LocalSlot) :=
  match dstTy with
  | .enum ety =>
    if !enumAdmitted ety then
      .error .unsupported
    else if isVariantUninhabited ety variantIdx then
      match getElem? locals resolvedDst.localId with
      | none => .error .unsupported
      | some _ => .error .undefined
    else
      match getElem? locals resolvedDst.localId with
      | none => .error .unsupported
      | some .dead => .error .undefined
      | some (.live root) =>
        match readPlaceSlotPath? (.ty localTy) root resolvedDst.projection,
            fieldsForVariant? ety variantIdx with
        | some curSv, some varFields =>
          let nextFields? : Option (List SlotVal) :=
            match curSv with
            | .uninit => some (uninitSlotVals varFields)
            | .enumUntagged ety' v' fs =>
              if EnumTy.beq ety ety' && Nat.beq v' variantIdx then
                some fs
              else
                none
            | .enumVal ety' v' fs =>
              if !EnumTy.beq ety ety' then
                none
              else if Nat.beq v' variantIdx then
                some fs
              else
                some (uninitSlotVals varFields)
            | _ => none
          match nextFields? with
          | none => .error .unsupported
          | some nextFields =>
            let tagCheck : Except FaultKind Unit :=
              match ety.tagRepr with
              | .zeroSized =>
                if Nat.beq variantIdx 0 then .ok () else .error .undefined
              | .single v₀ =>
                if Nat.beq variantIdx v₀ then .ok () else .error .undefined
              | .scalar _ _ => .ok ()
              | .niche _ _ _ _ _ untagged start last _ =>
                if Nat.beq variantIdx untagged then
                  match evalReadDiscriminantVariant ety curSv with
                  | .error k => .error k
                  | .ok actual =>
                    if Nat.beq actual variantIdx then
                      .ok ()
                    else
                      .error .undefined
                else if Nat.ble start variantIdx &&
                    Nat.ble variantIdx last then
                  .ok ()
                else
                  .error .unsupported
            match tagCheck with
            | .error k => .error k
            | .ok () =>
              let newEnumSv : SlotVal := .enumVal ety variantIdx nextFields
              match writePlaceSlotPath? (.ty localTy) root
                  resolvedDst.projection newEnumSv with
              | none => .error .unsupported
              | some root' =>
                match setElem? locals resolvedDst.localId (.live root') with
                | some locals' => .ok locals'
                | none => .error .unsupported
        | _, _ => .error .unsupported
  | _ =>
    match getElem? locals resolvedDst.localId with
    | none => .error .unsupported
    | some .dead => .error .undefined
    | some (.live root) =>
      match readPlaceSlotPath? (.ty localTy) root resolvedDst.projection with
      | none => .error .unsupported
      | some _ =>
        if isTypeUninhabited dstTy || !Nat.beq variantIdx 0 then
          .error .undefined
        else
          .ok locals

/-- Write the operands `ops` of a tuple, struct, or enum aggregate left to
right into `baseProj ++ [.field idx fieldTy]`, matching the per-field loop in
`Miri.Interpreter.writeAggregate`
(`vendor/lean-miri/Miri/Interpreter/Aggregate.lean`). -/
noncomputable def writeAggregateFields (bodyLocals : List MirTy)
    (localTy : MirTy) (dstLocal : LocalId) (baseProj : List ProjectionElem) :
    Nat → List LocalSlot → List Operand → List MirTy →
      Except FaultKind (List LocalSlot)
  | _, locals, [], [] => .ok locals
  | idx, locals, opnd :: ops, fieldTy :: fieldTys =>
    let fieldDst : Place :=
      { localId := dstLocal, projection := baseProj ++ [.field idx fieldTy] }
    match evalOperandToSlot bodyLocals locals opnd with
    | .error k => .error k
    | .ok (srcTy, sv, locals₁) =>
      if !(MirTy.beq srcTy fieldTy) then
        .error .unsupported
      else
        match sv.toVal? with
        | none => .error .undefined
        | some v =>
          match writePlaceWithLocalTy localTy locals₁ fieldDst fieldTy v with
          | .error k => .error k
          | .ok locals₂ =>
            writeAggregateFields bodyLocals localTy dstLocal baseProj
              (idx + 1) locals₂ ops fieldTys
  | _, _, _, _ => .error .unsupported

/-- Write the operands `ops` of a fixed-array aggregate left to right into
`baseProj ++ [.constantIndex idx (idx + 1) false]`. -/
noncomputable def writeAggregateArrayElems (bodyLocals : List MirTy)
    (localTy : MirTy) (dstLocal : LocalId) (baseProj : List ProjectionElem)
    (elemTy : MirTy) :
    Nat → List LocalSlot → List Operand → Except FaultKind (List LocalSlot)
  | _, locals, [] => .ok locals
  | idx, locals, opnd :: ops =>
    let elemDst : Place := {
      localId := dstLocal
      projection := baseProj ++ [.constantIndex idx (idx + 1) false]
    }
    match evalOperandToSlot bodyLocals locals opnd with
    | .error k => .error k
    | .ok (srcTy, sv, locals₁) =>
      if !(MirTy.beq srcTy elemTy) then
        .error .unsupported
      else
        match sv.toVal? with
        | none => .error .undefined
        | some v =>
          match writePlaceWithLocalTy localTy locals₁ elemDst elemTy v with
          | .error k => .error k
          | .ok locals₂ =>
            writeAggregateArrayElems bodyLocals localTy dstLocal baseProj
              elemTy (idx + 1) locals₂ ops

/-- Execute an aggregate assignment `dst := Aggregate(kind, ops)` for canonical
destination `resolvedDst` of type `dstTy` (inside base local of type
`localTy`), matching `Miri.Interpreter.writeAggregate`
(`vendor/lean-miri/Miri/Interpreter/Aggregate.lean`). -/
noncomputable def writeAggregate (bodyLocals : List MirTy) (localTy : MirTy)
    (locals : List LocalSlot) (resolvedDst : Place) (dstTy : MirTy)
    (kind : AggregateKind) (ops : List Operand) :
    Except FaultKind (List LocalSlot) :=
  match kind, dstTy with
  | .tuple, .unit =>
    if !ops.isEmpty then
      .error .unsupported
    else
      writePlaceWithLocalTy localTy locals resolvedDst .unit .unit
  | .tuple, .tuple fieldTys =>
    if fieldTys.isEmpty || !Nat.beq ops.length fieldTys.length then
      .error .unsupported
    else
      writeAggregateFields bodyLocals localTy resolvedDst.localId
        resolvedDst.projection 0 locals ops fieldTys
  | .adtStruct sty, .adtStruct dstSty =>
    if !StructTy.beq sty dstSty || !Nat.beq ops.length sty.fields.length ||
        !areSupportedFieldTys sty.fields || isTypeUninhabited (.adtStruct sty)
    then
      .error .unsupported
    else if ops.isEmpty then
      writePlaceWithLocalTy localTy locals resolvedDst dstTy
        (.structVal sty [])
    else
      writeAggregateFields bodyLocals localTy resolvedDst.localId
        resolvedDst.projection 0 locals ops sty.fields
  | .adtEnum ety variantIdx, .enum dstEty =>
    if !EnumTy.beq ety dstEty || !enumAdmitted ety then
      .error .unsupported
    else
      match fieldsForVariant? ety variantIdx with
      | none => .error .unsupported
      | some varFieldTys =>
        if !Nat.beq ops.length varFieldTys.length then
          .error .unsupported
        else
          let variantProj := resolvedDst.projection ++ [.downcast variantIdx]
          match writeAggregateFields bodyLocals localTy resolvedDst.localId
              variantProj 0 locals ops varFieldTys with
          | .error k => .error k
          | .ok locals₁ =>
            evalSetDiscriminantResolved localTy locals₁ resolvedDst (.enum ety)
              variantIdx
  | .array elemTy, .array dstElemTy len =>
    if !MirTy.beq elemTy dstElemTy || !Nat.beq ops.length len ||
        !isSupportedScalarOrUnitTy elemTy || !Nat.blt len (Nat.pow 2 64) then
      .error .unsupported
    else if ops.isEmpty then
      writePlaceWithLocalTy localTy locals resolvedDst dstTy (.array elemTy [])
    else
      writeAggregateArrayElems bodyLocals localTy resolvedDst.localId
        resolvedDst.projection elemTy 0 locals ops
  | _, _ => .error .unsupported

/-- Evaluate a single `StatementKind` in `frame`, matching `eval_statement` in
`compiler/rustc_const_eval/src/interpret/step.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and `Miri.Interpreter.Step`. -/
noncomputable def evalStatement (body : Body) (frame : FrameState)
    (callers : List FrameState) (callerMem : CallerMemory)
    (stmt : StatementKind) : StepResult State TerminalOut :=
  match stmt with
  | .nop =>
    .step {
      frames := { frame with stmtIdx := frame.stmtIdx + 1 } :: callers
      callerMem
    }
  | .storageLive localId =>
    match getElem? body.locals localId with
    | none => .fault .unsupported
    | some localTy =>
      match setElem? frame.locals localId (liveUninitSlot localTy) with
      | some locals' =>
        .step {
          frames := {
            frame with
            stmtIdx := frame.stmtIdx + 1
            locals := locals'
          } :: callers
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
          frames := {
            frame with
            stmtIdx := frame.stmtIdx + 1
            locals := locals'
          } :: callers
          callerMem
        }
      | none => .fault .unsupported
  | .setDiscriminant place variantIdx =>
    match getElem? body.locals place.localId with
    | none => .fault .unsupported
    | some localTy =>
      match projectTy? localTy place.projection with
      | none => .fault .unsupported
      | some dstTy =>
        match resolveProjPath body.locals frame.locals (.ty localTy)
            place.projection with
        | .error k => .fault k
        | .ok resolvedProj =>
          match evalSetDiscriminantResolved localTy frame.locals
              ⟨place.localId, resolvedProj⟩ dstTy variantIdx with
          | .error k => .fault k
          | .ok localsAfterWrite =>
            .step {
              frames := {
                frame with
                stmtIdx := frame.stmtIdx + 1
                locals := localsAfterWrite
              } :: callers
              callerMem
            }
  | .assign dst rvalue =>
    match getElem? body.locals dst.localId with
    | none => .fault .unsupported
    | some localTy =>
      match projectTy? localTy dst.projection with
      | none => .fault .unsupported
      | some dstTy =>
        if assignHasUnsupportedOverlap dst dstTy rvalue then
          .fault .unsupported
        else
          match resolveProjPath body.locals frame.locals (.ty localTy)
              dst.projection with
          | .error k => .fault k
          | .ok resolvedProj =>
            let resolvedDst : Place := ⟨dst.localId, resolvedProj⟩
            match rvalue with
            | .aggregate kind ops =>
              match writeAggregate body.locals localTy frame.locals resolvedDst
                  dstTy kind ops with
              | .error k => .fault k
              | .ok localsAfterWrite =>
                .step {
                  frames := {
                    frame with
                    stmtIdx := frame.stmtIdx + 1
                    locals := localsAfterWrite
                  } :: callers
                  callerMem
                }
            | _ =>
              match evalRvalue body.locals frame.locals dstTy rvalue with
              | .error k => .fault k
              | .ok (val, localsAfterRval) =>
                match writePlaceWithLocalTy localTy localsAfterRval resolvedDst
                    dstTy val with
                | .error k => .fault k
                | .ok localsAfterWrite =>
                  .step {
                    frames := {
                      frame with
                      stmtIdx := frame.stmtIdx + 1
                      locals := localsAfterWrite
                    } :: callers
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

/-- Assign the active frame location to `(target, 0)` while keeping suspended
`callers` intact, matching `Miri.Interpreter.ControlFlow.goToBlock`
(`Miri/Interpreter/ControlFlow.lean`: target block existence is checked at the
start of the next step in `evalStep` / `Step.step`). -/
noncomputable def jumpToBlock (frame : FrameState) (callers : List FrameState)
    (callerMem : CallerMemory) (target : BasicBlockId) :
    StepResult State TerminalOut :=
  .step {
    frames := { frame with blockIdx := target, stmtIdx := 0 } :: callers
    callerMem
  }

/-- Deinitialize canonicalized `place` of type `ty` (inside base local of type
`localTy`) in `locals` on call entry (`writePlaceSlotPath?`), matching the
`place_to_op(destination)` liveness check and
`protect_in_place_function_argument` (`write_uninit`) in `init_stack_frame`
(`compiler/rustc_const_eval/src/interpret/call.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.Call.initStackFrame` /
`Miri.Interpreter.MachineHooks.protectInPlaceFunctionArgument`
(`vendor/lean-miri/Miri/Interpreter/{Call,MachineHooks}.lean`). -/
noncomputable def deinitPlaceWithLocalTy (localTy : MirTy)
    (locals : List LocalSlot) (place : Place) (ty : MirTy) :
    Except FaultKind (List LocalSlot) :=
  match getElem? locals place.localId with
  | none => .error .unsupported
  | some .dead => .error .undefined
  | some (.live root) =>
    match writePlaceSlotPath? (.ty localTy) root place.projection
        (uninitSlotVal ty) with
    | none => .error .unsupported
    | some root' =>
      match setElem? locals place.localId (.live root') with
      | some locals' => .ok locals'
      | none => .error .unsupported

/-- Stage 1 left-to-right call argument evaluation via `evalOperandToSlot`,
threading `locals` across conservative `Operand.move` deinitializations in
argument order, matching `eval_callee_and_args` in
`compiler/rustc_const_eval/src/interpret/call.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.Call.evalCalleeAndArgs`
(`vendor/lean-miri/Miri/Interpreter/Call.lean`). -/
noncomputable def evalCallArgs (bodyLocals : List MirTy)
    (locals : List LocalSlot) :
    List Operand → Except FaultKind (List (MirTy × SlotVal) × List LocalSlot)
  | [] => .ok ([], locals)
  | opnd :: rest =>
    match evalOperandToSlot bodyLocals locals opnd with
    | .error k => .error k
    | .ok (ty, sv, locals₁) =>
      match evalCallArgs bodyLocals locals₁ rest with
      | .error k => .error k
      | .ok (pairs, locals₂) => .ok ((ty, sv) :: pairs, locals₂)

/-- Stage 2 left-to-right call argument validation against callee parameter
types `paramTys`, matching `pass_argument` (`copy_op_allow_transmute` +
validity checking) in `compiler/rustc_const_eval/src/interpret/call.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.Call.passArgument`
(`vendor/lean-miri/Miri/Interpreter/Call.lean`).

Static type mismatches and malformed values fault with `.unsupported`; reading
an uninitialized or moved-out argument faults with `.undefined`. -/
noncomputable def validateCallArgs :
    List (MirTy × SlotVal) → List MirTy → Except FaultKind (List Val)
  | [], [] => .ok []
  | (argTy, sv) :: restArgs, paramTy :: restTys =>
    if !(MirTy.beq argTy paramTy) then
      .error .unsupported
    else
      match sv.toVal? with
      | none => .error .undefined
      | some v =>
        if !checkVal v paramTy then
          .error .unsupported
        else
          match validateCallArgs restArgs restTys with
          | .error k => .error k
          | .ok vs => .ok (v :: vs)
  | _, _ => .error .unsupported

/-- Stage 2 primitive-operand reading for `CoreBuiltin` argument lists: checks
`isPrimitiveReadableTy ty` (`.unsupported` on non-primitives) and full
initialization `sv.toVal?` (`.undefined` on uninitialized storage) left to
right. -/
noncomputable def readPrimitiveArgs :
    List (MirTy × SlotVal) → Except FaultKind (List Val)
  | [] => .ok []
  | (ty, sv) :: rest =>
    if !isPrimitiveReadableTy ty then
      .error .unsupported
    else
      match sv.toVal? with
      | none => .error .undefined
      | some v =>
        match readPrimitiveArgs rest with
        | .error k => .error k
        | .ok vs => .ok (v :: vs)

/-- Evaluate saturating integer addition (`isAdd = true`) or subtraction
(`isAdd = false`) in lockstep with `saturating_arith` in
`compiler/rustc_const_eval/src/interpret/intrinsics.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.IntegerArithmeticIntrinsic.saturatingArith`
(`vendor/lean-miri/Miri/Interpreter/IntegerCast.lean`):

On overflow, signed operations clamp to `T::MAX` when `lhs ≥ 0` and `T::MIN`
when `lhs < 0`, while unsigned operations clamp to `T::MAX` for addition and
`0` for subtraction. -/
noncomputable def evalSaturatingOp (isAdd : Bool) (lhs rhs : Val) :
    Except FaultKind Val :=
  match lhs, rhs with
  | .scalar l, .scalar r =>
    if !(IntWidth.beq l.width r.width && (l.signed == r.signed)) then
      .error .unsupported
    else
      let op : BinOp := if isAdd then .addWithOverflow else .subWithOverflow
      match evalOverflowingArithOp op l.width l.signed
          (decodeScalar l) (decodeScalar r) with
      | .ok (.tuple [.scalar wrapped, .bool false]) => .ok (.scalar wrapped)
      | .ok (.tuple [.scalar _, .bool true]) =>
        let bits : BitVec 128 :=
          if l.signed then
            if decide (decodeScalar l ≥ 0) then
              BitVec.ofNat 128 (Nat.pow 2 (l.width.bitWidth - 1) - 1)
            else
              BitVec.ofNat 128 (Nat.pow 2 (l.width.bitWidth - 1))
          else if isAdd then
            BitVec.ofNat 128 (Nat.pow 2 l.width.bitWidth - 1)
          else
            BitVec.ofNat 128 0
        .ok (.scalar ⟨l.width, l.signed, bits⟩)
      | .error k => .error k
      | .ok _ => .error .unsupported
  | _, _ => .error .unsupported

/-- Count consecutive leading zero bits of `raw` across the low `width` bits
using structural `@Nat.rec` (avoiding compiler `_unsafe_rec` helpers).
Matches `core::intrinsics::ctlz` (`library/core/src/intrinsics/mod.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.IntegerIntrinsic.run .ctlz`
(`vendor/lean-miri/Miri/Interpreter/IntegerCast.lean`). -/
noncomputable def countLeadingZerosNat (raw width : Nat) : Nat :=
  @Nat.rec (fun _ => Nat)
    0
    (fun k ih => if Nat.testBit raw k then 0 else ih + 1)
    width

/-- Count consecutive trailing zero bits of `raw` across the low `width` bits
using structural `@Nat.rec` (avoiding compiler `_unsafe_rec` helpers).
Matches `core::intrinsics::cttz` (`library/core/src/intrinsics/mod.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.IntegerIntrinsic.run .cttz`
(`vendor/lean-miri/Miri/Interpreter/IntegerCast.lean`). -/
noncomputable def countTrailingZerosNat (raw width : Nat) : Nat :=
  @Nat.rec (fun _ => Nat)
    0
    (fun k ih => if Nat.testBit raw (width - 1 - k) then 0 else ih + 1)
    width

/-- Stage 2 argument reader for `CoreBuiltin` calls: `.fromLeBytes` accepts a
single `[u8; N]` fixed byte array (`MirTy.array (.int .i8 false) _`, faulting
with `.undefined` if any element is `.uninit`), while all other builtins
require primitive scalar/bool arguments (`readPrimitiveArgs`). -/
noncomputable def readBuiltinArgs (builtin : CoreBuiltin)
    (pairs : List (MirTy × SlotVal)) : Except FaultKind (List Val) :=
  match builtin with
  | .fromLeBytes =>
    match pairs with
    | [(.array (.int .i8 false) len, sv)] =>
      if !Nat.blt len (Nat.pow 2 64) then
        .error .unsupported
      else
        match sv.toVal? with
        | none => .error .undefined
        | some v => .ok [v]
    | _ => .error .unsupported
  | _ => readPrimitiveArgs pairs

/-- Check that `ety` has the canonical 2-variant `core::option::Option<T>`
payload shape (`variant 0 = None` with `[]`, `variant 1 = Some(T)` with
`[innerTy]`). -/
noncomputable def isOptionEnumForTy (ety : EnumTy) (innerTy : MirTy) : Bool :=
  enumAdmitted ety &&
    Nat.beq ety.discriminants.length 2 &&
    match fieldsForVariant? ety 0, fieldsForVariant? ety 1 with
    | some [], some [fTy] => MirTy.beq fTy innerTy
    | _, _ => false

/-- Evaluate `checked_{add,sub,mul}` into `dstTy = .enum ety` (`Option<T>`),
returning `None` (`.enumVal ety 0 []`) on overflow and `Some(wrapped)`
(`.enumVal ety 1 [.scalar wrapped]`) otherwise. -/
noncomputable def evalCheckedArithOp (op : BinOp) (dstTy : MirTy)
    (l r : ScalarVal) : Except FaultKind Val :=
  match dstTy with
  | .enum ety =>
    if !isOptionEnumForTy ety (.int l.width l.signed) then
      .error .unsupported
    else
      match evalBinOp op (.scalar l) (.scalar r) with
      | .ok (.tuple [.scalar wrapped, .bool false]) =>
        let res : Val := .enumVal ety 1 [.scalar wrapped]
        if checkVal res (.enum ety) then .ok res else .error .unsupported
      | .ok (.tuple [.scalar _, .bool true]) =>
        let res : Val := .enumVal ety 0 []
        if checkVal res (.enum ety) then .ok res else .error .unsupported
      | .error k => .error k
      | .ok _ => .error .unsupported
  | _ => .error .unsupported

/-- Produce `n` little-endian `BitVec 8` bytes from the low `n * 8` bits of `v`
using structural `@Nat.rec` (definitionally identical to
`Anneal.LeBytes.toLeBytesAux`). -/
noncomputable def scalarToLeBytesAux (n : Nat) (v : Nat) : List (BitVec 8) :=
  @Nat.rec (fun _ => Nat → List (BitVec 8))
    (fun _ => [])
    (fun _ ih k => BitVec.ofNat 8 k :: ih (HDiv.hDiv k 256))
    n v

/-- Map a list of `BitVec 8` bytes to `u8` runtime scalar `Val`s. -/
noncomputable def u8BytesToVals : List (BitVec 8) → List Val
  | [] => []
  | b :: bs => .scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩ :: u8BytesToVals bs

/-- Extract validated `BitVec 8` bytes from a list of `u8` runtime `Val`s. -/
noncomputable def valsToU8Bytes? : List Val → Option (List (BitVec 8))
  | [] => some []
  | .scalar ⟨.i8, false, bits⟩ :: rest =>
    if truncateBits .i8 bits != bits then
      none
    else
      match valsToU8Bytes? rest with
      | some bs => some (BitVec.ofNat 8 bits.toNat :: bs)
      | none => none
  | _ :: _ => none

/-- Reassemble a list of little-endian `BitVec 8` bytes into a `Nat` via
`List.foldr` (definitionally identical to `Anneal.LeBytes.fromLeBytes`). -/
noncomputable def scalarFromLeBytes (bs : List (BitVec 8)) : Nat :=
  bs.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- Evaluate a recognized `CoreBuiltin` on evaluated arguments for destination
type `dstTy`, matching `library/core/src/num/{int_macros,uint_macros}.rs`,
`library/core/src/intrinsics/mod.rs`, and `library/core/src/cmp.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
noncomputable def evalCoreBuiltin (builtin : CoreBuiltin) (dstTy : MirTy)
    (args : List Val) : Except FaultKind Val :=
  match builtin, args with
  | .wrappingAdd, [.scalar l, .scalar r] =>
    evalBinOp .add (.scalar l) (.scalar r)
  | .wrappingSub, [.scalar l, .scalar r] =>
    evalBinOp .sub (.scalar l) (.scalar r)
  | .wrappingMul, [.scalar l, .scalar r] =>
    evalBinOp .mul (.scalar l) (.scalar r)
  | .wrappingShl, [.scalar l, .scalar r] =>
    if IntWidth.beq r.width .i32 && !r.signed then
      evalBinOp .shl (.scalar l) (.scalar r)
    else
      .error .unsupported
  | .wrappingShr, [.scalar l, .scalar r] =>
    if IntWidth.beq r.width .i32 && !r.signed then
      evalBinOp .shr (.scalar l) (.scalar r)
    else
      .error .unsupported
  | .overflowingAdd, [.scalar l, .scalar r] =>
    evalBinOp .addWithOverflow (.scalar l) (.scalar r)
  | .overflowingSub, [.scalar l, .scalar r] =>
    evalBinOp .subWithOverflow (.scalar l) (.scalar r)
  | .overflowingMul, [.scalar l, .scalar r] =>
    evalBinOp .mulWithOverflow (.scalar l) (.scalar r)
  | .saturatingAdd, [lhs, rhs] => evalSaturatingOp true lhs rhs
  | .saturatingSub, [lhs, rhs] => evalSaturatingOp false lhs rhs
  | .checkedAdd, [.scalar l, .scalar r] =>
    evalCheckedArithOp .addWithOverflow dstTy l r
  | .checkedSub, [.scalar l, .scalar r] =>
    evalCheckedArithOp .subWithOverflow dstTy l r
  | .checkedMul, [.scalar l, .scalar r] =>
    evalCheckedArithOp .mulWithOverflow dstTy l r
  | .leadingZeros, [.scalar sv] =>
    let raw := (truncateBits sv.width sv.bits).toNat
    let count := countLeadingZerosNat raw sv.width.bitWidth
    .ok (.scalar ⟨.i32, false, truncateBits .i32 (BitVec.ofNat 128 count)⟩)
  | .trailingZeros, [.scalar sv] =>
    let raw := (truncateBits sv.width sv.bits).toNat
    let count := countTrailingZerosNat raw sv.width.bitWidth
    .ok (.scalar ⟨.i32, false, truncateBits .i32 (BitVec.ofNat 128 count)⟩)
  | .isMultipleOf, [.scalar l, .scalar r] =>
    if l.signed || r.signed || !IntWidth.beq l.width r.width then
      .error .unsupported
    else
      let lNat := (truncateBits l.width l.bits).toNat
      let rNat := (truncateBits r.width r.bits).toNat
      if Nat.beq rNat 0 then
        .ok (.bool (Nat.beq lNat 0))
      else
        .ok (.bool (Nat.beq (Nat.mod lNat rNat) 0))
  | .toLeBytes, [.scalar sv] =>
    match dstTy with
    | .array (.int .i8 false) len =>
      if !Nat.beq len sv.width.byteSize then
        .error .unsupported
      else
        let raw := (truncateBits sv.width sv.bits).toNat
        let bytes := scalarToLeBytesAux sv.width.byteSize raw
        .ok (.array (.int .i8 false) (u8BytesToVals bytes))
    | _ => .error .unsupported
  | .fromLeBytes, [.array (.int .i8 false) elems] =>
    match dstTy with
    | .int w s =>
      if !Nat.beq elems.length w.byteSize then
        .error .unsupported
      else
        match valsToU8Bytes? elems with
        | none => .error .unsupported
        | some bs =>
          let raw := scalarFromLeBytes bs
          .ok (.scalar ⟨w, s, truncateBits w (BitVec.ofNat 128 raw)⟩)
    | _ => .error .unsupported
  | .cmpMin, [.scalar l, .scalar r] =>
    if !(IntWidth.beq l.width r.width && (l.signed == r.signed)) then
      .error .unsupported
    else if decide (decodeScalar l ≤ decodeScalar r) then
      .ok (.scalar ⟨l.width, l.signed, truncateBits l.width l.bits⟩)
    else
      .ok (.scalar ⟨r.width, r.signed, truncateBits r.width r.bits⟩)
  | .cmpMax, [.scalar l, .scalar r] =>
    if !(IntWidth.beq l.width r.width && (l.signed == r.signed)) then
      .error .unsupported
    else if decide (decodeScalar l ≥ decodeScalar r) then
      .ok (.scalar ⟨l.width, l.signed, truncateBits l.width l.bits⟩)
    else
      .ok (.scalar ⟨r.width, r.signed, truncateBits r.width r.bits⟩)
  | _, _ => .error .unsupported

/-- Propagate an unwind starting at `(frame, callers)` along `unwind`,
recursing structurally over `callers` on `.continue_` until reaching a cleanup
block, an `.unreachable`/`.terminate` boundary, or exiting the root frame
(`.done (.unwound callerMem)`), matching `unwind_to_block` and
`return_from_current_stack_frame(/* unwinding */ true)`
(`compiler/rustc_const_eval/src/interpret/{eval_context,call}.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.ControlFlow.{unwindToBlock, returnFromCurrentFrame}`. -/
noncomputable def unwindFrame (callerMem : CallerMemory) :
    FrameState → List FrameState → UnwindAction → StepResult State TerminalOut
  | frame, callers, .cleanup block =>
    jumpToBlock frame callers callerMem block
  | _, _, .unreachable => .fault .undefined
  | _, _, .terminate => .fault .unsupported
  | frame, [], .continue_ =>
    match frame.returnCont with
    | none => .done (.unwound callerMem)
    | some _ => .fault .unsupported
  | frame, caller :: rest, .continue_ =>
    match frame.returnCont with
    | some cont => unwindFrame callerMem caller rest cont.unwind
    | none => .fault .unsupported

/-- Whether a failing `Assert` with message `msg` panics through a panic
function that takes no operand, so that $M_{\text{anneal}}$ can model the
panic without evaluating the operands that `AssertKind` drops.

`Miri`'s `assert_panic` (`src/shims/panic.rs`, `rust-lang/miri`
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`) evaluates the message operands of
`BoundsCheck` and `MisalignedPointerDereference` and calls every other
message's operand-free lang item:

> "BoundsCheck { index, len } => {
>     // Forward to `panic_bounds_check` lang item.
>
>     // First arg: index.
>     let index = this.read_immediate(&this.eval_operand(index, None)?)?;
>     // Second arg: len.
>     let len = this.read_immediate(&this.eval_operand(len, None)?)?;
>     ...
> }
> MisalignedPointerDereference { required, found } => { ... }
>
> _ => {
>     // Call the lang item associated with this message.
>     let fn_item =
>         this.tcx.require_lang_item(msg.panic_function(), this.tcx.span);
>     let instance = ty::Instance::mono(this.tcx.tcx, fn_item);
>     this.call_function(
>         instance,
>         ExternAbi::Rust,
>         &[],
>         None,
>         ReturnContinuation::Goto { ret: None, unwind },
>     )?;
> }"

`AssertKind::panic_function` (`compiler/rustc_middle/src/mir/terminator.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`) names that lang
item only for the seven binary operators that can overflow:

> "Overflow(BinOp::Add, _, _) => LangItem::PanicAddOverflow,
> Overflow(BinOp::Sub, _, _) => LangItem::PanicSubOverflow,
> Overflow(BinOp::Mul, _, _) => LangItem::PanicMulOverflow,
> Overflow(BinOp::Div, _, _) => LangItem::PanicDivOverflow,
> Overflow(BinOp::Rem, _, _) => LangItem::PanicRemOverflow,
> OverflowNeg(_) => LangItem::PanicNegOverflow,
> Overflow(BinOp::Shr, _, _) => LangItem::PanicShrOverflow,
> Overflow(BinOp::Shl, _, _) => LangItem::PanicShlOverflow,
> Overflow(op, _, _) => bug!("{:?} cannot overflow", op),
> DivisionByZero(_) => LangItem::PanicDivZero,
> RemainderByZero(_) => LangItem::PanicRemZero,
> ...
> NullPointerDereference => LangItem::PanicNullPointerDereference,"

Accordingly this predicate holds for `.overflow op` with `op` one of `.add`,
`.sub`, `.mul`, `.div`, `.rem`, `.shl`, and `.shr`, and for `.overflowNeg`,
`.divByZero`, `.remByZero`, and `.nullPtrDeref`. It rejects `.boundsCheck` and
`.misalignedPtrDeref` (whose panic functions read operands), `.overflow op`
for any other `op`, and `.unsupported`. -/
noncomputable def isOperandFreeAssertKind : AssertKind → Bool
  | .overflow op =>
    match op with
    | .add | .sub | .mul | .div | .rem | .shl | .shr => true
    | _ => false
  | .overflowNeg | .divByZero | .remByZero | .nullPtrDeref => true
  | .boundsCheck | .misalignedPtrDeref | .unsupported => false

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
>         Assert { ref cond, expected, ref msg, target, unwind } => {
>             let ignored =
>                 M::ignore_optional_overflow_checks(self)
>                     && msg.is_optional_overflow_check();
>             let cond_val =
>                 self.read_scalar(&self.eval_operand(cond, None)?)?.to_bool()?;
>             if ignored || expected == cond_val {
>                 self.go_to_block(target);
>             } else {
>                 M::assert_panic(self, msg, unwind)?;
>             }
>         }
>         ...
>         // When we encounter Resume, we've finished unwinding
>         // cleanup for the current stack frame. We pop it in order
>         // to continue unwinding the next frame
>         UnwindResume => {
>             ...
>             self.return_from_current_stack_frame(/* unwinding */ true)?;
>             return interp_ok(());
>         }
>         ...
>         Unreachable => throw_ub!(Unreachable),
>         ...
>     }
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

**Panics and unwinding.** A panic is not Undefined Behavior. An execution that
unwinds out of the entry function ends with `.done (.unwound callerMem)`, not
with a fault, so a safe function that can panic (such as a checked division
that panics on a zero divisor) can still satisfy `WellFormed` and
`BodyVerified`.

- `.assert cond expected msg target unwind` evaluates `cond` with
  `evalPrimitiveOperand` (a dead local or uninitialized storage faults with
  `.undefined`; a non-`bool` operand faults with `.unsupported`) and keeps the
  locals that this evaluation leaves. If the condition equals `expected`, the
  frame jumps to `target`. Otherwise the assertion fails and the frame panics:
  1. `msg` must satisfy `isOperandFreeAssertKind`; any other message faults
     with `.unsupported`, so the model never skips the evaluation of a message
     operand.
  2. The panic then unwinds along `unwind`, following `unwind_to_block`
     (`compiler/rustc_const_eval/src/interpret/eval_context.rs`,
     `rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

     > "mir::UnwindAction::Cleanup(block) => Left(block.start_location()),
     > mir::UnwindAction::Continue => Right(self.frame_mut().body.span),
     > mir::UnwindAction::Unreachable => {
     >     throw_ub_format!(
     >         \"unwinding past a stack frame that does not allow unwinding\");
     > }
     > mir::UnwindAction::Terminate(reason) => {
     >     self.frame_mut().loc = Right(self.frame_mut().body.span);
     >     M::unwind_terminate(self, reason)?;
     >     ...
     > }"

     - `.continue_`: unwinds out of the current frame via `unwindFrame`: on the
       root frame (`returnCont = none`, `callers = []`) this exits with
       `.done (.unwound callerMem)`; on a callee frame
       (`returnCont = some cont`, `callers = caller :: rest`) it propagates
       along `cont.unwind` in `caller`.
     - `.cleanup block`: the frame jumps to the cleanup block `block`.
     - `.unreachable`: unwinding out of a frame that does not allow it is
       Undefined Behavior: `.fault .undefined`.
     - `.terminate`: aborting the process is unmodeled: `.fault .unsupported`.

  The model abstracts the panic runtime between the failed assertion and the
  start of unwinding (the call to the panic lang item, the panic hook, and the
  payload allocation), and it assumes the `unwind` panic strategy. Under
  `-C panic=abort` a panic aborts the process instead of unwinding; the model
  then over-approximates by reporting `.unwound`, a cleanup jump, or (for
  `.unreachable`) a fault where the compiled program aborts.
  `Trusted.MirAst.TerminatorKind` records the producer obligation for sessions
  that disable overflow checks.
- `.unwindResume` ends a cleanup block by propagating the unwind out of the
  current frame via `unwindFrame` (exiting with `.done (.unwound callerMem)` at
  the root frame or propagating along `cont.unwind` in the caller). Outside a
  cleanup block (`bb.cleanup = false`) it faults with `.unsupported`, matching
  the `return_from_current_stack_frame` assertion that unwinding returns only
  from cleanup blocks (as `.return_` faults with `.unsupported` inside one).
- `.call callee args dst target unwind` rejects `.move` arguments that may
  overlap `dst` (`anyMoveOperandMayOverlapPlace`), resolves `dst`'s static type
  in the caller, evaluates `args` left-to-right (`evalCallArgs`), checks
  `callee`'s existence, `bodyEntryAdmitted`, argument arity, and return-type
  compatibility against `dst`, deinitializes `dst` on call entry
  (`deinitPlaceWithLocalTy`), validates `args` left-to-right
  (`validateCallArgs`), initializes the callee locals (`initLocalsLoop`), and
  pushes the callee frame with `returnCont = some ⟨dst, target, unwind⟩` onto
  the call stack above the caller frame with deinitialized `dst`.
- `.callBuiltin builtin args dst target _unwind` rejects `.move` arguments that
  may overlap `dst` (`anyMoveOperandMayOverlapPlace`), resolves `dst`'s static
  type, evaluates `args` left-to-right (`evalCallArgs` + `readBuiltinArgs`),
  evaluates `evalCoreBuiltin`, writes the result into `dst`
  (`writePlaceWithLocalTy`), and jumps to `target` (or faults with `.undefined`
  when `target = none`). -/
noncomputable def evalTerminator (p : Program) (body : Body) (bb : BasicBlock)
    (frame : FrameState) (callers : List FrameState)
    (callerMem : CallerMemory) : StepResult State TerminalOut :=
  match bb.terminator with
  | .goto target => jumpToBlock frame callers callerMem target
  | .return_ =>
    if bb.cleanup then
      .fault .unsupported
    else
      match getElem? frame.locals 0 with
      | some (.live sv) =>
        match sv.toVal? with
        | some retVal =>
          match frame.returnCont, callers with
          | none, [] => .done (.returned ⟨retVal, callerMem⟩)
          | some cont, caller :: rest =>
            match getElem? p.bodies caller.defId with
            | none => .fault .unsupported
            | some callerBody =>
              match getElem? callerBody.locals cont.dst.localId with
              | none => .fault .unsupported
              | some localTy =>
                match projectTy? localTy cont.dst.projection with
                | none => .fault .unsupported
                | some dstTy =>
                  match resolveStaticProjPath (.ty localTy)
                      cont.dst.projection with
                  | .error k => .fault k
                  | .ok resolvedProj =>
                    match writePlaceWithLocalTy localTy caller.locals
                        ⟨cont.dst.localId, resolvedProj⟩ dstTy retVal with
                    | .error k => .fault k
                    | .ok callerLocals' =>
                      match cont.target with
                      | some nextBb =>
                        jumpToBlock { caller with locals := callerLocals' }
                          rest callerMem nextBb
                      | none => .fault .undefined
          | _, _ => .fault .unsupported
        | none => .fault .undefined
      | some .dead => .fault .undefined
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
        jumpToBlock { frame with locals := localsAfterDiscr } callers
          callerMem target
  | .assert cond expected msg target unwind =>
    match evalPrimitiveOperand body.locals frame.locals cond with
    | .error k => .fault k
    | .ok (condVal, localsAfterCond) =>
      match condVal with
      | .bool b =>
        if expected == b then
          jumpToBlock { frame with locals := localsAfterCond } callers
            callerMem target
        else if !isOperandFreeAssertKind msg then
          .fault .unsupported
        else
          unwindFrame callerMem { frame with locals := localsAfterCond }
            callers unwind
      | _ => .fault .unsupported
  | .unwindResume =>
    if bb.cleanup then
      unwindFrame callerMem frame callers .continue_
    else
      .fault .unsupported
  | .call callee args dst target unwind =>
    if anyMoveOperandMayOverlapPlace dst args then
      .fault .unsupported
    else
      match getElem? body.locals dst.localId with
      | none => .fault .unsupported
      | some localTy =>
        match projectTy? localTy dst.projection with
        | none => .fault .unsupported
        | some dstTy =>
          match resolveProjPath body.locals frame.locals (.ty localTy)
              dst.projection with
          | .error k => .fault k
          | .ok resolvedProj =>
            let resolvedDst : Place := ⟨dst.localId, resolvedProj⟩
            match evalCallArgs body.locals frame.locals args with
            | .error k => .fault k
            | .ok (argPairs, localsAfterArgs) =>
              match getElem? p.bodies callee with
              | none => .fault .unsupported
              | some calleeBody =>
                if !bodyEntryAdmitted calleeBody then
                  .fault .unsupported
                else if !Nat.beq argPairs.length calleeBody.argumentCount then
                  .fault .unsupported
                else
                  match getElem? calleeBody.locals 0 with
                  | none => .fault .unsupported
                  | some calleeRetTy =>
                    if !MirTy.beq calleeRetTy dstTy then
                      .fault .unsupported
                    else
                      match deinitPlaceWithLocalTy localTy localsAfterArgs
                          resolvedDst dstTy with
                      | .error k => .fault k
                      | .ok localsAfterDeinit =>
                        let paramTys :=
                          (calleeBody.locals.drop 1).take
                            calleeBody.argumentCount
                        match validateCallArgs argPairs paramTys with
                        | .error k => .fault k
                        | .ok argVals =>
                          let calleeLocals :=
                            initLocalsLoop calleeBody argVals 0
                              calleeBody.locals
                          let callerFrame' : FrameState :=
                            { frame with locals := localsAfterDeinit }
                          let calleeFrame : FrameState := {
                            defId := callee
                            blockIdx := 0
                            stmtIdx := 0
                            locals := calleeLocals
                            returnCont := some ⟨resolvedDst, target, unwind⟩
                          }
                          .step {
                            frames := calleeFrame :: callerFrame' :: callers
                            callerMem
                          }
  | .callBuiltin builtin args dst target _ =>
    if anyMoveOperandMayOverlapPlace dst args then
      .fault .unsupported
    else
      match getElem? body.locals dst.localId with
      | none => .fault .unsupported
      | some localTy =>
        match projectTy? localTy dst.projection with
        | none => .fault .unsupported
        | some dstTy =>
          match resolveProjPath body.locals frame.locals (.ty localTy)
              dst.projection with
          | .error k => .fault k
          | .ok resolvedProj =>
            let resolvedDst : Place := ⟨dst.localId, resolvedProj⟩
            match evalCallArgs body.locals frame.locals args with
            | .error k => .fault k
            | .ok (argPairs, localsAfterArgs) =>
              match readBuiltinArgs builtin argPairs with
              | .error k => .fault k
              | .ok argVals =>
                match evalCoreBuiltin builtin dstTy argVals with
                | .error k => .fault k
                | .ok resVal =>
                  match writePlaceWithLocalTy localTy localsAfterArgs
                      resolvedDst dstTy resVal with
                  | .error k => .fault k
                  | .ok localsAfterWrite =>
                    match target with
                    | some nextBb =>
                      jumpToBlock { frame with locals := localsAfterWrite }
                        callers callerMem nextBb
                    | none => .fault .undefined
  | .unsupported =>
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
  | frame :: callers =>
    match getElem? p.bodies frame.defId with
    | none => .fault .unsupported
    | some body =>
      match getElem? body.basicBlocks frame.blockIdx with
      | none => .fault .unsupported
      | some bb =>
        match getElem? bb.statements frame.stmtIdx with
        | some stmt => evalStatement body frame callers s.callerMem stmt
        | none =>
          if Nat.beq frame.stmtIdx bb.statements.length then
            evalTerminator p body bb frame callers s.callerMem
          else
            .fault .unsupported
  | [] => .fault .unsupported

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
2. **Direct crate-local calls and core builtins:** `entryProgForBody p defId`
   retains `p.bodies` so direct crate-local `TerminatorKind.call` terminators
   push callee frames and return or unwind across sibling definitions, while
   recognized `TerminatorKind.callBuiltin` terminators execute core numeric and
   comparison operations directly. Uncaptured callees and indirect calls step
   to `.fault .unsupported` and refute `WellFormed` fail-closed.
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
  variantFields := [[], []]
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
  variantFields := [[], []]
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
  variantFields := [[]]
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
    (.enumVal canarySingleZstEnumTy 0 []) ∧
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

/-- Three-variant niche enum with `untagged = 1` strictly inside `0..=2` and
two niche variants (`0` at tag `2`, `2` at tag `4`; `1` carries `bool`). -/
noncomputable def canaryTriNicheEnumTy : EnumTy := {
  id := 20
  discrWidth := .isize
  discrSigned := true
  tagRepr := .niche .i8 false (BitVec.ofNat 128 0) (BitVec.ofNat 128 4)
    [0] 1 0 2 (BitVec.ofNat 128 2)
  discriminants := [10, 20, 30]
  variantFields := [[], [.bool], []]
}

/-- Signed `Ordering`-like enum (`Less = -1`, `Equal = 0`, `Greater = 1`). -/
noncomputable def canaryOrderingEnumTy : EnumTy := {
  id := 21
  discrWidth := .i8
  discrSigned := true
  tagRepr := .scalar .i8 true
  discriminants := [255, 0, 1]
  variantFields := [[], [], []]
}

/-- `Option<Ordering>` with wrapping valid range `0xFF..=0x02` (`None = 0` at
niche tag `2`, `Some(Ordering) = 1` untagged). -/
noncomputable def canaryOptOrderingEnumTy : EnumTy := {
  id := 22
  discrWidth := .isize
  discrSigned := true
  tagRepr := .niche .i8 true (BitVec.ofNat 128 255) (BitVec.ofNat 128 2)
    [0] 1 0 0 (BitVec.ofNat 128 2)
  discriminants := [0, 1]
  variantFields := [[], [.enum canaryOrderingEnumTy]]
}

/-- Niche `Option<bool>` for Pass 1 partial-move niche-leaf UB canary. -/
noncomputable def canaryOptBoolNicheEnumTy : EnumTy := {
  id := 23
  discrWidth := .isize
  discrSigned := true
  tagRepr := .niche .i8 false (BitVec.ofNat 128 0) (BitVec.ofNat 128 2)
    [0] 1 0 0 (BitVec.ofNat 128 2)
  discriminants := [0, 1]
  variantFields := [[], [.bool]]
}

/-- `.single 1` payload enum (variant `0` uninhabited `!`, variant `1` carries
`u32`). -/
noncomputable def canarySinglePayloadEnumTy : EnumTy := {
  id := 24
  discrWidth := .isize
  discrSigned := true
  tagRepr := .single 1
  discriminants := [7, 9]
  variantFields := [[.never], [u32Ty]]
}

/-- Nested struct carrying a `.single` payload enum and a `u8`. -/
noncomputable def canaryNestedWrapStructTy : StructTy := {
  id := 25
  fields := [.enum canarySinglePayloadEnumTy, u8Ty]
}

/-- Direct-tagged `Option<i8>` for signed checked arithmetic canaries. -/
noncomputable def canaryOptI8EnumTy : EnumTy := {
  id := 26
  discrWidth := .isize
  discrSigned := true
  tagRepr := .scalar .i8 false
  discriminants := [0, 1]
  variantFields := [[], [.int .i8 true]]
}

/-- Direct-tagged `Option<u64>` (`64`-bit tag) for checked ops & `None` const.
-/
noncomputable def canaryOptU64EnumTy : EnumTy := {
  id := 27
  discrWidth := .isize
  discrSigned := true
  tagRepr := .scalar .i64 false
  discriminants := [0, 1]
  variantFields := [[], [.int .i64 false]]
}

/-- Pass 1 positive canary exercising `canaryTriNicheEnumTy` (`untagged` inside
`start..=last` with `> 1` niche variants). -/
noncomputable def progTier2TriNiche : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [
      .tuple [.int .isize true, .int .isize true, .int .isize true],
      .enum canaryTriNicheEnumTy,
      .enum canaryTriNicheEnumTy,
      .enum canaryTriNicheEnumTy,
      .int .isize true,
      .int .isize true,
      .int .isize true
    ]
    basicBlocks := [{
      statements := [
        .setDiscriminant ⟨1, []⟩ 0,
        .assign ⟨2, [.downcast 1, .field 0 .bool]⟩
          (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 1)⟩)),
        .setDiscriminant ⟨2, []⟩ 1,
        .setDiscriminant ⟨3, []⟩ 2,
        .assign ⟨4, []⟩ (.discriminant ⟨1, []⟩),
        .assign ⟨5, []⟩ (.discriminant ⟨2, []⟩),
        .assign ⟨6, []⟩ (.discriminant ⟨3, []⟩),
        .assign ⟨0, []⟩
          (.aggregate .tuple [.move ⟨4, []⟩, .move ⟨5, []⟩, .move ⟨6, []⟩])
      ]
      terminator := .return_
    }]
  }]

/-- Pass 1 positive canary exercising wrapping valid range (`Option<Ordering>`
`0xFF..=0x02`) and niche unit-variant constant (`None`). -/
noncomputable def progTier2WrappingNicheAndConst : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [
      .tuple [.int .isize true, .int .isize true],
      .enum canaryOptOrderingEnumTy,
      .enum canaryOptOrderingEnumTy,
      .int .isize true,
      .int .isize true
    ]
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩ (.use (.constant
          ⟨.enum canaryOptOrderingEnumTy, .scalar (BitVec.ofNat 128 2)⟩)),
        .assign ⟨2, [.downcast 1, .field 0 (.enum canaryOrderingEnumTy)]⟩
          (.use (.constant
            ⟨.enum canaryOrderingEnumTy, .scalar (BitVec.ofNat 128 255)⟩)),
        .setDiscriminant ⟨2, []⟩ 1,
        .assign ⟨3, []⟩ (.discriminant ⟨1, []⟩),
        .assign ⟨4, []⟩ (.discriminant ⟨2, []⟩),
        .assign ⟨0, []⟩ (.aggregate .tuple [.move ⟨3, []⟩, .move ⟨4, []⟩])
      ]
      terminator := .return_
    }]
  }]

/-- Pass 1 negative UB canary: partial move of a niche leaf followed by
`Rvalue.discriminant` faults with `.undefined`. -/
noncomputable def progTier2NicheLeafMoveDiscrUb : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.int .isize true, .enum canaryOptBoolNicheEnumTy, .bool]
    basicBlocks := [{
      statements := [
        .assign ⟨1, [.downcast 1, .field 0 .bool]⟩
          (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 1)⟩)),
        .setDiscriminant ⟨1, []⟩ 1,
        .assign ⟨2, []⟩ (.use (.move ⟨1, [.downcast 1, .field 0 .bool]⟩)),
        .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩)
      ]
      terminator := .return_
    }]
  }]

/-- Pass 1 positive canary exercising `.single` payload enum nested inside a
struct inside a fixed array `[Wrap; 2]`. -/
noncomputable def progTier2NestedSingleEnumInArray : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [
      u32Ty,
      .array (.adtStruct canaryNestedWrapStructTy) 2,
      u32Ty,
      .int .isize true
    ]
    basicBlocks := [{
      statements := [
        .assign ⟨1, [
            .constantIndex 1 2 false,
            .field 0 (.enum canarySinglePayloadEnumTy),
            .downcast 1,
            .field 0 u32Ty
          ]⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩)),
        .assign ⟨2, []⟩ (.use (.copy ⟨1, [
            .constantIndex 1 2 false,
            .field 0 (.enum canarySinglePayloadEnumTy),
            .downcast 1,
            .field 0 u32Ty
          ]⟩)),
        .assign ⟨3, []⟩ (.discriminant ⟨1, [
            .constantIndex 1 2 false,
            .field 0 (.enum canarySinglePayloadEnumTy)
          ]⟩),
        .assign ⟨0, []⟩ (.use (.move ⟨2, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Pass 1 positive canary exercising `[u8; 0]`, `[(); 3]`, and `Rvalue.repeat`
(`[0u8; 4]` and `[x; 0]`). -/
noncomputable def progTier2ZstArraysAndRepeat : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [
      .array u8Ty 4,
      .array u8Ty 0,
      .array .unit 3,
      u8Ty
    ]
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩ (.repeat_ (.copy ⟨3, []⟩) 0),
        .assign ⟨2, []⟩ (.repeat_ (.constant ⟨.unit, .zeroSized⟩) 3),
        .assign ⟨0, []⟩ (.repeat_ (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 7)⟩) 4)
      ]
      terminator := .return_
    }]
  }]

/-- Pass 1 negative UB canaries for `Index` with uninit, dead, or moved index
local and `ConstantIndex` `fromEnd` with `offset = 0`. -/
noncomputable def progTier2IndexUninitIdxUb : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u8Ty, .array u8Ty 2, .int .isize false]
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩
          (.repeat_ (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 1)⟩) 2),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, [.index 2]⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progTier2IndexDeadIdxUb : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u8Ty, .array u8Ty 2, .int .isize false]
    basicBlocks := [{
      statements := [
        .storageDead 2,
        .assign ⟨1, []⟩
          (.repeat_ (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 1)⟩) 2),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, [.index 2]⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progTier2IndexMovedIdxUb : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u8Ty, .array u8Ty 2, .int .isize false, .int .isize false]
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩
          (.use (.constant ⟨.int .isize false, .scalar (BitVec.ofNat 128 0)⟩)),
        .assign ⟨3, []⟩ (.use (.move ⟨2, []⟩)),
        .assign ⟨1, []⟩
          (.repeat_ (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 1)⟩) 2),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, [.index 2]⟩))
      ]
      terminator := .return_
    }]
  }]

noncomputable def progTier2FromEndZeroUb : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u8Ty, .array u8Ty 2]
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩
          (.repeat_ (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 1)⟩) 2),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, [.constantIndex 0 2 true]⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Pass 1 positive canary exercising `Index` in a direct call destination. -/
noncomputable def progTier2CallDstIndex : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 0
      locals := [.array u8Ty 2, .int .isize false]
      basicBlocks := [
        {
          statements := [
            .assign ⟨0, []⟩
              (.repeat_ (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 1)⟩) 2),
            .assign ⟨1, []⟩
              (.use (.constant ⟨.int .isize false, .scalar (BitVec.ofNat 128 1)⟩))
          ]
          terminator := .call 1 [] ⟨0, [.index 1]⟩ (some 1) .continue_
        },
        { statements := [], terminator := .return_ }
      ]
    },
    {
      argumentCount := 0
      locals := [u8Ty]
      basicBlocks := [{
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 9)⟩))
        ]
        terminator := .return_
      }]
    }
  ]

/-- Pass 1 positive canary helper for binary `CoreBuiltin` calls. -/
noncomputable def mkTier2BinBuiltinProg (b : CoreBuiltin)
    (dstTy lhsTy rhsTy : MirTy) : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [dstTy, lhsTy, rhsTy]
    basicBlocks := [
      {
        statements := []
        terminator := .callBuiltin b [.copy ⟨1, []⟩, .copy ⟨2, []⟩]
          ⟨0, []⟩ (some 1) .continue_
      },
      { statements := [], terminator := .return_ }
    ]
  }]

/-- Pass 1 positive canary helper for unary `CoreBuiltin` calls. -/
noncomputable def mkTier2UnaryBuiltinProg (b : CoreBuiltin)
    (dstTy argTy : MirTy) : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [dstTy, argTy]
    basicBlocks := [
      {
        statements := []
        terminator := .callBuiltin b [.copy ⟨1, []⟩] ⟨0, []⟩ (some 1) .continue_
      },
      { statements := [], terminator := .return_ }
    ]
  }]

/-- Pass 1 positive canary for direct-tagged payload-enum unit constant
(`Option<u64>::None`). -/
noncomputable def progTier2OptionU64NoneConst : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.enum canaryOptU64EnumTy]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.use (.constant
          ⟨.enum canaryOptU64EnumTy, .scalar (BitVec.ofNat 128 0)⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Pass 1 negative UB canary: `fromLeBytes` reading an array with an
uninitialized element faults with `.undefined`. -/
noncomputable def progTier2FromLeBytesUninitElemUb : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.int .i16 false, .array u8Ty 2]
    basicBlocks := [
      {
        statements := [
          .assign ⟨1, [.constantIndex 0 2 false]⟩
            (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .callBuiltin .fromLeBytes [.copy ⟨1, []⟩]
          ⟨0, []⟩ (some 1) .continue_
      },
      { statements := [], terminator := .return_ }
    ]
  }]

/-- Trusted claim for
`Anneal.MirWp.canary_tier2_adt_array_and_builtins_anneal`: Pass 1 coverage for
Tier 2 niche layouts (untagged inside `start..=last`, `> 1` niche variants,
wrapping valid range `Option<Ordering>`, niche-leaf partial-move UB), `.single`
payload enum nested in struct/array, `[T; 0]`/`[(); N]`/`Rvalue.repeat`,
`Index` edge cases (uninit/dead/moved idx, call dst, `fromEnd` offset `0`),
unsigned/signed `checkedSub`/`checkedMul`/`checkedAdd`, payload-enum `None`
constants, `toLeBytes` on negative signed/`u8`/`usize`/`i128`, and
`fromLeBytes` uninit-element UB. -/
noncomputable def CanaryTier2AdtArrayAndBuiltinsAnnealClaim : Prop :=
  let i8Ty : MirTy := .int .i8 true
  let i16Ty : MirTy := .int .i16 true
  let i128Ty : MirTy := .int .i128 true
  let usizeTy : MirTy := .int .isize false
  let u64Ty : MirTy := .int .i64 false
  let optI8Ty : MirTy := .enum canaryOptI8EnumTy
  let optU64Ty : MirTy := .enum canaryOptU64EnumTy
  PositiveCanaryClaim progTier2TriNiche queryEmpty
    (.tuple [scalarNatVal .isize true 10, scalarNatVal .isize true 20,
      scalarNatVal .isize true 30]) ∧
  PositiveCanaryClaim progTier2WrappingNicheAndConst queryEmpty
    (.tuple [scalarNatVal .isize true 0, scalarNatVal .isize true 1]) ∧
  NegativeCanaryClaim progTier2NicheLeafMoveDiscrUb queryEmpty
    .undefined .unsupported ∧
  PositiveCanaryClaim progTier2NestedSingleEnumInArray queryEmpty (u32Val 42) ∧
  PositiveCanaryClaim progTier2ZstArraysAndRepeat queryEmpty
    (.array u8Ty [u8Val 7, u8Val 7, u8Val 7, u8Val 7]) ∧
  NegativeCanaryClaim progTier2IndexUninitIdxUb queryEmpty
    .undefined .unsupported ∧
  NegativeCanaryClaim progTier2IndexDeadIdxUb queryEmpty
    .undefined .unsupported ∧
  NegativeCanaryClaim progTier2IndexMovedIdxUb queryEmpty
    .undefined .unsupported ∧
  NegativeCanaryClaim progTier2FromEndZeroUb queryEmpty
    .unsupported .undefined ∧
  PositiveCanaryClaim progTier2CallDstIndex queryEmpty
    (.array u8Ty [u8Val 1, u8Val 9]) ∧
  PositiveCanaryClaim
    (mkTier2BinBuiltinProg .checkedSub optU64Ty u64Ty u64Ty)
    { args := [scalarNatVal .i64 false 0, scalarNatVal .i64 false 1] }
    (.enumVal canaryOptU64EnumTy 0 []) ∧
  PositiveCanaryClaim
    (mkTier2BinBuiltinProg .checkedMul optU64Ty u64Ty u64Ty)
    { args := [scalarNatVal .i64 false 6, scalarNatVal .i64 false 7] }
    (.enumVal canaryOptU64EnumTy 1 [scalarNatVal .i64 false 42]) ∧
  PositiveCanaryClaim
    (mkTier2BinBuiltinProg .checkedAdd optI8Ty i8Ty i8Ty)
    { args := [scalarNatVal .i8 true 127, scalarNatVal .i8 true 1] }
    (.enumVal canaryOptI8EnumTy 0 []) ∧
  PositiveCanaryClaim
    (mkTier2BinBuiltinProg .checkedSub optI8Ty i8Ty i8Ty)
    { args := [scalarNatVal .i8 true 128, scalarNatVal .i8 true 1] }
    (.enumVal canaryOptI8EnumTy 0 []) ∧
  PositiveCanaryClaim
    (mkTier2BinBuiltinProg .checkedMul optI8Ty i8Ty i8Ty)
    { args := [scalarNatVal .i8 true 128, scalarNatVal .i8 true 255] }
    (.enumVal canaryOptI8EnumTy 0 []) ∧
  PositiveCanaryClaim progTier2OptionU64NoneConst queryEmpty
    (.enumVal canaryOptU64EnumTy 0 []) ∧
  PositiveCanaryClaim
    (mkTier2UnaryBuiltinProg .toLeBytes (.array u8Ty 2) i16Ty)
    { args := [scalarNatVal .i16 true 65534] }
    (.array u8Ty [u8Val 254, u8Val 255]) ∧
  PositiveCanaryClaim
    (mkTier2UnaryBuiltinProg .toLeBytes (.array u8Ty 1) u8Ty)
    { args := [u8Val 171] }
    (.array u8Ty [u8Val 171]) ∧
  PositiveCanaryClaim
    (mkTier2UnaryBuiltinProg .toLeBytes (.array u8Ty 8) usizeTy)
    { args := [scalarNatVal .isize false 0x0102030405060708] }
    (.array u8Ty [u8Val 8, u8Val 7, u8Val 6, u8Val 5,
      u8Val 4, u8Val 3, u8Val 2, u8Val 1]) ∧
  PositiveCanaryClaim
    (mkTier2UnaryBuiltinProg .toLeBytes (.array u8Ty 16) i128Ty)
    { args := [scalarNatVal .i128 true (Nat.pow 2 128 - 1)] }
    (.array u8Ty (replicateVal 16 (u8Val 255))) ∧
  NegativeCanaryClaim progTier2FromLeBytesUninitElemUb queryEmpty
    .undefined .unsupported

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
