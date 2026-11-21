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
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics.Ops
import Trusted.MirSemantics.Enum
import Trusted.MirSemantics.State
import Trusted.MirSemantics.Step
import Trusted.MirSemantics.Boundary
import Trusted.MirSemantics.CanaryFixtures

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

/-- Trusted claim for `Anneal.MirWp.canary_positive_add_anneal`. -/
noncomputable def CanaryPositiveAddAnnealClaim : Prop :=
  PositiveCanaryClaim progAddU32 queryAdd30_12 (u32Val 42)

/-- Trusted claim for `Anneal.MirWp.canary_positive_empty_unit_fn`. -/
noncomputable def CanaryPositiveEmptyUnitFnClaim : Prop :=
  PositiveCanaryClaim progEmptyUnitFn queryEmpty .unit

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

/-- Trusted claim for `Anneal.MirWp.canary_negative_ub_div_zero_anneal`. -/
noncomputable def CanaryNegativeUbDivZeroAnnealClaim : Prop :=
  NegativeCanaryClaim progDivByZero queryDivByZero .undefined .unsupported

/-- Trusted claim for
`Anneal.MirWp.canary_negative_ub_signed_rem_overflow_i8`. -/
noncomputable def CanaryNegativeUbSignedRemOverflowI8Claim : Prop :=
  NegativeCanaryClaim progSignedRemOverflowI8 querySignedRemOverflowI8
    .undefined .unsupported

/-- Trusted claim for `Anneal.MirWp.canary_negative_unsupported_anneal`. -/
noncomputable def CanaryNegativeUnsupportedAnnealClaim : Prop :=
  NegativeCanaryClaim progUnsupported queryEmpty .unsupported .undefined

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

/-- Trusted claim for
`Anneal.MirWp.canary_negative_ub_storage_dead_read_anneal`. -/
noncomputable def CanaryNegativeUbStorageDeadReadAnnealClaim : Prop :=
  NegativeCanaryClaim progStorageDeadReadUb queryEmpty .undefined .unsupported

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

/-- Trusted claim for
`Anneal.MirWp.canary_positive_enum_explicit_repr_anneal`:
exercises explicit-repr `#[repr(u8)]` non-index enum constant tag decoding and
`u8` `Rvalue.discriminant` alongside signed `i8` -> `isize` tag sign-extension.
-/
noncomputable def CanaryPositiveEnumExplicitReprAnnealClaim : Prop :=
  PositiveCanaryClaim progEnumExplicitReprU8 queryEmpty (u8Val 20) ∧
  PositiveCanaryClaim progEnumSignedTagIsize queryEmpty
    (scalarNatVal .isize true (Nat.pow 2 64 - 1))

/-- Trusted claim for `Anneal.MirWp.canary_positive_zst_single_enum_anneal`. -/
noncomputable def CanaryPositiveZstSingleEnumAnnealClaim : Prop :=
  PositiveCanaryClaim progZstSingleEnumImplicitRet queryEmpty
    (.enumVal canarySingleZstEnumTy 0) ∧
  PositiveCanaryClaim progZstSingleEnumMoveAndDiscr queryEmpty
    (scalarNatVal .isize true 42)

/-- Trusted claim for
`Anneal.MirWp.canary_negative_ub_enum_invalid_tag_and_uninit_anneal`. -/
noncomputable def CanaryNegativeUbEnumInvalidTagAndUninitAnnealClaim : Prop :=
  NegativeCanaryClaim progEnumInvalidTagConstUb queryEmpty
    .undefined .unsupported ∧
  NegativeCanaryClaim progEnumUninitDiscrUb queryEmpty
    .undefined .unsupported

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
