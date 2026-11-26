-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
module
prelude
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Ops
public import Trusted.MirSemantics.Enum
public import Trusted.MirSemantics.Layout
public import Trusted.MirSemantics.Memory
public import Trusted.MirSemantics.Bytes
public import Trusted.MirSemantics.State
public import Trusted.MirSemantics.Step
public import Trusted.MirSemantics.Boundary
public import Trusted.MirSemantics.CanaryFixtures
public import Trusted.MirSemantics.Contract

@[expose] public section

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
`UnitTheorem`), their Profile v2 counterparts (`initStateV2`, `evalStepV2`,
`StepV2`, `ReachesV2`, `ReachesResultV2`, `WellFormedV2`, `BehaviorV2`,
`DivergesV2`, `SatisfiesPostV2`, `BodyVerifiedV2`, `SpecsV2`, `CrateV2`,
`ProgramVerifiedV2`, `CrateTheoremV2`, and `UnitTheoremV2`), and the Pass 1
audited claim propositions (`WpSoundnessClaim`, `WpFaultSoundnessClaim`,
`ExecSoundnessClaimV2`, `SafeContractSoundnessClaimV2`, and the 26
`Canary*Claim` propositions).

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

For an unprojected `Sized` local, capture lowers
`StatementKind::PlaceMention(place)` to `StatementKind.nop`, matching Miri's
operational semantics (`rustc_const_eval`'s `local_to_place` and
`vendor/lean-miri`'s `localToPlace`), which check only local bounds without
calling `.access()` or checking allocation/liveness for `Sized` locals; although
`compiler/rustc_middle/src/mir/syntax.rs` states for `StorageLive` /
`StorageDead` that "Using a local in any way (not only reading/writing from it)
while it is unallocated is UB.", both Miri engines treat bare `PlaceMention` of
a `Sized` local as a no-op (see `Trusted/MirAst/Statements.lean`).

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
   `liveUninitSlot .unit = .immediate (some .unit)`, and
   `liveUninitSlot (.enum ety) = .immediate (some (.enumVal ety 0))` whenever
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

6. **Byte-level memory and indirect locals (`Trusted.MirSemantics.Layout`,
   `Trusted.MirSemantics.Memory`, `Trusted.MirSemantics.Bytes`):**
   `State.mem` holds stack allocations, and `LocalSlot.indirect` locals read
   and write their bytes there, as `rustc` does after `force_allocation`.
   Profile version 1 has no statement that forces an allocation, so
   `CanaryMemoryLifecycleAnnealClaim` applies `forceAllocation` between steps
   to exercise these rules.

7. **`char`, `core::cmp::Ordering`, overflow pairs, and integer casts:**
   `MirTy.char` values are Lean `Char`s (exactly the Unicode scalar values),
   and an invalid `char` constant, memory value, or `switchInt` case is
   `.undefined`. `BinOp.cmp` returns `MirTy.ordering` values on integers and
   `char`s (`.unsupported` on `bool`), and `Rvalue.discriminant` of an
   `Ordering` is its `i8` tag. `BinOp.{add,sub,mul}WithOverflow` return the
   overflow pair `.tuple [.int w s, .bool]` (the only executable tuple type).
   `Rvalue.cast .intToInt` converts integers, `bool`, and `char` to integers
   and `u8`-range values to `char`; every other cast kind is `.unsupported`.
-/

/-!
## Audited Pass 1 Weakest-Precondition and Non-Vacuity Canary Claims

The definitions below state the exact mathematical propositions that
`Anneal.MirWp` (the 2 parameterized WP soundness claims and the Profile v2
`ExecSoundnessClaimV2` and `SafeContractSoundnessClaimV2` claims) and decoupled
`Anneal.MirWp.Canaries` (the 26 closed
non-vacuity and parameter-boundary canary claims) must prove, enforced by
`TrustedBoundary.lean` via exact `Expr` equality (`ci.type == .const claimName
[]` or the parameterized claim application) together with claim-body constant
checks. Keeping these claim
propositions in `Trusted.MirSemantics` ensures that no change outside
`trusted/` can silently drift a pinned soundness or canary claim statement.
`anneal-audit` enforces only the exact theorem statements (not the internal
proof route); the closed canary claims witness non-vacuity of the operational
semantics (`WellFormed`, `Behavior`, and `ReachesResult`), and
`Anneal.MirWp.Canaries` discharges them (without importing `Anneal.MirWp`) via
`Anneal.MirWp.positiveCanary_of_exec` and
`Anneal.MirWp.negativeCanary_of_execFault` (built on
`Anneal.MirWp.wellFormed_and_spec_of_wp_base` and
`Anneal.MirWp.reaches_fault_and_exclusive_of_wpFault_base`, all in module
`Anneal.MirWp.Core`), `Anneal.MirWp.checkVal_never_false` (module
`Anneal.MirWp.Reflection`), structural case analysis, and kernel `rfl`
reduction.
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

/-- Trusted total-correctness and productivity claim for the Profile v2
execution predicate `Anneal.MirWp.execProgV2`, the Profile v2 counterpart of
`WpSoundnessClaim` over `initStateV2` and `StepV2`.

Requires partial correctness (`SatisfiesPostV2`), all-path termination
(`¬ DivergesV2`), and at least one terminating execution satisfying `post`.
`SpecsV2.property` statements describe Profile v2 results with `BehaviorV2`
(and may use `DivergesV2` or `SatisfiesPostV2`), so `TrustedBoundary.lean`
requires this claim to name all three and requires `Anneal.MirWp` to prove it
for `execProgV2`, the executor that Profile v2 proofs use to establish
`BehaviorV2`. -/
noncomputable def ExecSoundnessClaimV2
    (execProgFn : Program → Nat → Query → (TerminalOut → Prop) → Prop) : Prop :=
  ∀ (p : Program) (q : Query) (fuel : Nat) (post : TerminalOut → Prop),
    execProgFn p fuel q post →
    SatisfiesPostV2 p q post ∧
    ¬ DivergesV2 p q ∧
    (∃ out, BehaviorV2 p q out ∧ post out)

/-- Trusted contract-soundness claim tying the `SafeContractV2` and
`EffectMaskV2` specification vocabulary to `Anneal.MirWp.execProgV2`:
1. `execProgV2` establishes `SatisfiesSafeContractV2` for any `contract` whose
   `SafeContractV2.post` holds on the fuel-bounded execution result;
2. `BodySatisfiesSafeContractV2` follows from per-query `execProgV2` witnesses;
3. `EffectMaskV2.noAbort` forbids `.aborted` outcomes in `SafeContractV2.post`
   for every `SafeContractV2` using `effects := EffectMaskV2.noAbort`.

`TrustedBoundary.lean` requires this claim to name all six vocabulary
declarations (`EffectMaskV2`, `EffectMaskV2.noAbort`, `SafeContractV2`,
`SafeContractV2.post`, `SatisfiesSafeContractV2`, and
`BodySatisfiesSafeContractV2`) and requires `Anneal.MirWp` to prove it for
`execProgV2`. -/
noncomputable def SafeContractSoundnessClaimV2
    (execProgFn : Program → Nat → Query → (TerminalOut → Prop) → Prop) : Prop :=
  (∀ (p : Program) (q : Query) (fuel : Nat) (contract : SafeContractV2),
    (contract.behaviorPre q → execProgFn p fuel q (contract.post q)) →
    SatisfiesSafeContractV2 p q contract) ∧
  (∀ (p : Program) (defId : DefId) (body : Body) (contract : SafeContractV2),
    getElem? p.bodies defId = some body →
    BodyStaticAdmittedV2 p body = true →
    (∀ q : Query, ValidEntryArgsV2 body q → contract.behaviorPre q →
      ∃ fuel : Nat,
        execProgFn (entryProgForBody p defId) fuel q (contract.post q)) →
    BodySatisfiesSafeContractV2 p defId body contract) ∧
  (∀ (mask : EffectMaskV2) (pre : Query → Prop) (postRet : Query → Out → Prop)
      (postAb : Query → CallerMemory → Prop) (q : Query) (cm : CallerMemory),
    mask = EffectMaskV2.noAbort →
    ¬ SafeContractV2.post
        { behaviorPre := pre, effects := mask,
          postReturn := postRet, postAbort := postAb }
        q (.aborted cm))

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
      scope := .unit
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canaryUnsafeGuardedBody false]
    } 0
      (canaryUnsafeGuardedBody false) (fun _ => False) ∧
  ¬ BodyVerified {
      scope := .unit
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canaryNeverParamBody true]
    } 0
      (canaryNeverParamBody true) (fun _ => True) ∧
  ¬ BodyVerified {
      scope := .unit
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody, canaryUnsafeGuardedBody false]
    } 0
      (canaryUnsafeGuardedBody false) (fun _ => True) ∧
  ¬ BodyVerified {
      scope := .unit
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

/-- The four big-endian bytes of `0x01020304u32` (`profileTargetEndian`). -/
noncomputable def canaryBytes01020304 : List AllocByte :=
  [.init 1 none, .init 2 none, .init 3 none, .init 4 none]

/-- Trusted claim for `Anneal.MirWp.canary_memory_lifecycle_anneal`, which
exercises `.indirect` locals and `MemoryState` on `progMemLifecycle`
(`StorageLive(_2); _2 = copy _1; _0 = copy _2; StorageDead(_2); return`) and
`progMemUninitRead` (`StorageLive(_1); _0 = copy _1; return`):
1. Without `forceAllocation`, `progMemLifecycle` returns its argument
   `0x01020304`.
2. Moving the initialized `_2` into memory after `_2 = copy _1` allocates a
   fresh stack allocation with id `2` (id `1` is the reserved return place),
   stores the value's big-endian bytes (`canaryBytes01020304`), reads them back
   in `_0 = copy _2`, deallocates the allocation at `StorageDead(_2)` (so a
   later read through the old place faults with `.undefined`), and returns
   `0x01020304`.
3. Moving the uninitialized `_2` into memory right after `StorageLive(_2)`
   allocates four uninitialized bytes; `_2 = copy _1` then writes the value's
   bytes through the place, and execution returns `0x01020304`.
4. Moving the uninitialized `_1` of `progMemUninitRead` into memory and then
   reading it (`_0 = copy _1`) faults with `.undefined`, as does reading it
   after its allocation is deallocated.
5. On `progMemIndirectOps` (`_0 = move _1; StorageLive(_1); return`), with
   `_1` (allocation `2`) and `_0` (allocation `3`) moved into memory first:
   `_0 = move _1` copies the bytes into `_0`'s allocation and deinitializes
   `_1`'s bytes; `StorageLive(_1)` deallocates `_1`'s allocation; and
   `return` reads the result from `_0`'s allocation.
6. On `progEnumExplicitReprU8` (`_1 = const ReprU8::B; _0 =
   discriminant(_1)`), with `_1` moved into memory after the assignment, the
   tag byte `20` is stored in allocation `2`, `discriminant(_1)` reads it
   back, `StorageDead(_1)` deallocates it, and execution returns `20u8`.
7. Type checks precede memory reads: copying a `bool` `.indirect` local into
   a `u32` (`progMemIllTypedUse`) and applying `Not` to an enum `.indirect`
   local (`progMemNonPrimitiveUnOp`) fault with `.unsupported` even after
   the local's allocation is deallocated. -/
def CanaryMemoryLifecycleAnnealClaim : Prop :=
  PositiveCanaryClaim progMemLifecycle queryMemLifecycle
    (u32Val 16909060) ∧
  (∃ (s₀ s₁ s₂ s₃ s₄ s₅ : State) (place : MemPlace),
    initState progMemLifecycle queryMemLifecycle = .ok s₀ ∧
    evalStep progMemLifecycle 0 s₀ = .step s₁ ∧
    evalStep progMemLifecycle 0 s₁ = .step s₂ ∧
    forceAllocation progMemLifecycle s₂ 2 = .ok (s₃, place) ∧
    place = ⟨2, 0⟩ ∧
    readBytes s₃.mem place 4 2 = .ok canaryBytes01020304 ∧
    evalStep progMemLifecycle 0 s₃ = .step s₄ ∧
    evalStep progMemLifecycle 0 s₄ = .step s₅ ∧
    readBytes s₅.mem place 4 2 = .error .undefined ∧
    evalStep progMemLifecycle 0 s₅ =
      .done (.returned ⟨u32Val 16909060, ⟨[]⟩⟩)) ∧
  (∃ (t₀ t₁ t₂ t₃ t₄ t₅ : State) (place : MemPlace),
    initState progMemLifecycle queryMemLifecycle = .ok t₀ ∧
    evalStep progMemLifecycle 0 t₀ = .step t₁ ∧
    forceAllocation progMemLifecycle t₁ 2 = .ok (t₂, place) ∧
    readBytes t₂.mem place 4 2 = .ok (List.replicate 4 .uninit) ∧
    evalStep progMemLifecycle 0 t₂ = .step t₃ ∧
    readBytes t₃.mem place 4 2 = .ok canaryBytes01020304 ∧
    evalStep progMemLifecycle 0 t₃ = .step t₄ ∧
    evalStep progMemLifecycle 0 t₄ = .step t₅ ∧
    evalStep progMemLifecycle 0 t₅ =
      .done (.returned ⟨u32Val 16909060, ⟨[]⟩⟩)) ∧
  (∃ (u₀ u₁ u₂ : State) (place : MemPlace) (m : MemoryState),
    initState progMemUninitRead queryEmpty = .ok u₀ ∧
    evalStep progMemUninitRead 0 u₀ = .step u₁ ∧
    forceAllocation progMemUninitRead u₁ 1 = .ok (u₂, place) ∧
    evalStep progMemUninitRead 0 u₂ = .fault .undefined ∧
    deallocateStack u₂.mem place = .ok m ∧
    evalStep progMemUninitRead 0 { u₂ with mem := m } = .fault .undefined) ∧
  (∃ (v₀ v₁ v₂ v₃ v₄ : State),
    initState progMemIndirectOps queryMemLifecycle = .ok v₀ ∧
    forceAllocation progMemIndirectOps v₀ 1 = .ok (v₁, ⟨2, 0⟩) ∧
    forceAllocation progMemIndirectOps v₁ 0 = .ok (v₂, ⟨3, 0⟩) ∧
    readBytes v₂.mem ⟨2, 0⟩ 4 2 = .ok canaryBytes01020304 ∧
    readBytes v₂.mem ⟨3, 0⟩ 4 2 = .ok (List.replicate 4 .uninit) ∧
    evalStep progMemIndirectOps 0 v₂ = .step v₃ ∧
    readBytes v₃.mem ⟨2, 0⟩ 4 2 = .ok (List.replicate 4 .uninit) ∧
    readBytes v₃.mem ⟨3, 0⟩ 4 2 = .ok canaryBytes01020304 ∧
    evalStep progMemIndirectOps 0 v₃ = .step v₄ ∧
    readBytes v₄.mem ⟨2, 0⟩ 4 2 = .error .undefined ∧
    evalStep progMemIndirectOps 0 v₄ =
      .done (.returned ⟨u32Val 16909060, ⟨[]⟩⟩)) ∧
  (∃ (d₀ d₁ d₂ d₃ d₄ d₅ : State),
    initState progEnumExplicitReprU8 queryEmpty = .ok d₀ ∧
    evalStep progEnumExplicitReprU8 0 d₀ = .step d₁ ∧
    evalStep progEnumExplicitReprU8 0 d₁ = .step d₂ ∧
    forceAllocation progEnumExplicitReprU8 d₂ 1 = .ok (d₃, ⟨2, 0⟩) ∧
    readBytes d₃.mem ⟨2, 0⟩ 1 0 = .ok [.init 20 none] ∧
    evalStep progEnumExplicitReprU8 0 d₃ = .step d₄ ∧
    evalStep progEnumExplicitReprU8 0 d₄ = .step d₅ ∧
    readBytes d₅.mem ⟨2, 0⟩ 1 0 = .error .undefined ∧
    evalStep progEnumExplicitReprU8 0 d₅ =
      .done (.returned ⟨u8Val 20, ⟨[]⟩⟩)) ∧
  (∃ (w₀ w₁ w₂ : State) (place : MemPlace) (m : MemoryState),
    initState progMemIllTypedUse queryEmpty = .ok w₀ ∧
    evalStep progMemIllTypedUse 0 w₀ = .step w₁ ∧
    forceAllocation progMemIllTypedUse w₁ 1 = .ok (w₂, place) ∧
    deallocateStack w₂.mem place = .ok m ∧
    evalStep progMemIllTypedUse 0 { w₂ with mem := m } =
      .fault .unsupported) ∧
  (∃ (x₀ x₁ x₂ : State) (place : MemPlace) (m : MemoryState),
    initState progMemNonPrimitiveUnOp queryEmpty = .ok x₀ ∧
    evalStep progMemNonPrimitiveUnOp 0 x₀ = .step x₁ ∧
    forceAllocation progMemNonPrimitiveUnOp x₁ 1 = .ok (x₂, place) ∧
    deallocateStack x₂.mem place = .ok m ∧
    evalStep progMemNonPrimitiveUnOp 0 { x₂ with mem := m } =
      .fault .unsupported)

/-- Trusted claim for `Anneal.MirWp.canary_positive_char_and_cmp_anneal`:
1. `char` comparisons compare Unicode scalar values (`'a' < 'b'`,
   `'a' == 'a'`, and `'a' >= '\u{1f600}'` is `false`).
2. `BinOp.cmp` returns `core::cmp::Ordering` on `char` (`'b'.cmp('a')` is
   `Greater`), on signed integers (`-1i8.cmp(1i8)` is `Less`, distinguishing
   signed from unsigned comparison of the bits `255`), on unsigned integers
   (`255u8.cmp(1u8)` is `Greater`), and on equal values (`Equal`).
3. `Rvalue.discriminant` of the `Ordering` `Less` is `-1i8` (raw bits `255`).
4. `switchInt` on a `char` takes the matching case (`'a'` returns `1u32`) and
   otherwise falls through (`'b'` returns `2u32`). -/
noncomputable def CanaryPositiveCharAndCmpAnnealClaim : Prop :=
  PositiveCanaryClaim (mkBinOpProg .lt .bool .char .char)
    { args := [charVal 97, charVal 98] } (.bool true) ∧
  PositiveCanaryClaim (mkBinOpProg .eq .bool .char .char)
    { args := [charVal 97, charVal 97] } (.bool true) ∧
  PositiveCanaryClaim (mkBinOpProg .ge .bool .char .char)
    { args := [charVal 97, charVal 0x1f600] } (.bool false) ∧
  PositiveCanaryClaim (mkBinOpProg .cmp .ordering .char .char)
    { args := [charVal 98, charVal 97] } (.ordering .greater) ∧
  PositiveCanaryClaim (mkBinOpProg .cmp .ordering i8Ty i8Ty)
    { args := [i8Val 255, i8Val 1] } (.ordering .less) ∧
  PositiveCanaryClaim (mkBinOpProg .cmp .ordering u8Ty u8Ty)
    { args := [u8Val 255, u8Val 1] } (.ordering .greater) ∧
  PositiveCanaryClaim (mkBinOpProg .cmp .ordering u32Ty u32Ty)
    { args := [u32Val 7, u32Val 7] } (.ordering .equal) ∧
  PositiveCanaryClaim (mkCmpDiscriminantProg i8Ty)
    { args := [i8Val 255, i8Val 1] } (i8Val 255) ∧
  PositiveCanaryClaim progCharSwitch { args := [charVal 97] } (u32Val 1) ∧
  PositiveCanaryClaim progCharSwitch { args := [charVal 98] } (u32Val 2)

/-- Trusted claim for `Anneal.MirWp.canary_negative_char_and_cmp_anneal`:
1. The constant `0xD800 as char` (a surrogate) is an invalid `char` and
   faults with `.undefined`.
2. A `char` switch case `0xD800` faults with `.undefined` when compared.
3. `BinOp.cmp` on `bool` faults with `.unsupported`, as in
   `Miri.Interpreter.IntegerOps.binaryBool`.
4. `UnOp.not` on `char` faults with `.unsupported`. -/
noncomputable def CanaryNegativeCharAndCmpAnnealClaim : Prop :=
  NegativeCanaryClaim progInvalidCharConstUb queryEmpty
    .undefined .unsupported ∧
  NegativeCanaryClaim progInvalidCharSwitchCaseUb { args := [charVal 97] }
    .undefined .unsupported ∧
  NegativeCanaryClaim (mkBinOpProg .cmp .ordering .bool .bool)
    { args := [.bool false, .bool true] } .unsupported .undefined ∧
  NegativeCanaryClaim (mkUnOpProg .not .char) { args := [charVal 97] }
    .unsupported .undefined

/-- Trusted claim for `Anneal.MirWp.canary_positive_overflow_ops_anneal`:
`BinOp.{addWithOverflow, subWithOverflow, mulWithOverflow}` return the wrapped
result and the overflow flag as a `(T, bool)` pair:
1. `255u8 + 1` is `(0, true)` and `200u8 + 55` is `(255, false)`.
2. `-128i8 - 1` is `(127, true)` (raw bits `128 - 1 = 127`).
3. `65536u32 * 65536` is `(0, true)`, and `-6i8 * 5` is `(-30, false)` (raw
   bits `250 * 5 = 226`).
4. `2^126 * 2` on `i128` overflows the signed 128-bit range and is
   `(-2^127, true)` (raw bits `2^127`). -/
noncomputable def CanaryPositiveOverflowOpsAnnealClaim : Prop :=
  PositiveCanaryClaim
    (mkBinOpProg .addWithOverflow (overflowPairTy u8Ty) u8Ty u8Ty)
    { args := [u8Val 255, u8Val 1] } (.tuple [u8Val 0, .bool true]) ∧
  PositiveCanaryClaim
    (mkBinOpProg .addWithOverflow (overflowPairTy u8Ty) u8Ty u8Ty)
    { args := [u8Val 200, u8Val 55] } (.tuple [u8Val 255, .bool false]) ∧
  PositiveCanaryClaim
    (mkBinOpProg .subWithOverflow (overflowPairTy i8Ty) i8Ty i8Ty)
    { args := [i8Val 128, i8Val 1] } (.tuple [i8Val 127, .bool true]) ∧
  PositiveCanaryClaim
    (mkBinOpProg .mulWithOverflow (overflowPairTy u32Ty) u32Ty u32Ty)
    { args := [u32Val 65536, u32Val 65536] } (.tuple [u32Val 0, .bool true]) ∧
  PositiveCanaryClaim
    (mkBinOpProg .mulWithOverflow (overflowPairTy i8Ty) i8Ty i8Ty)
    { args := [i8Val 250, i8Val 5] } (.tuple [i8Val 226, .bool false]) ∧
  PositiveCanaryClaim
    (mkBinOpProg .mulWithOverflow (overflowPairTy (.int .i128 true))
      (.int .i128 true) (.int .i128 true))
    { args := [scalarNatVal .i128 true (Nat.pow 2 126),
        scalarNatVal .i128 true 2] }
    (.tuple [scalarNatVal .i128 true (Nat.pow 2 127), .bool true])

/-- Trusted claim for `Anneal.MirWp.canary_positive_int_to_int_cast_anneal`:
`CastKind.intToInt` sign-extends signed sources (`-1i8 as u32` is
`0xFFFF_FFFF` and `-1i64 as i128` is `-1i128`), zero-extends unsigned sources
(`255u8 as i32` is `255`), truncates to the target width (`300u32 as u8` is
`44`), converts `bool` (`true as i32` is `1`) and `char` (`'\u{1f600}' as u8` is
`0`), and converts `u8` to `char` (`200u8 as char` is `'\u{c8}'`). -/
noncomputable def CanaryPositiveIntToIntCastAnnealClaim : Prop :=
  PositiveCanaryClaim (mkIntToIntCastProg i8Ty u32Ty) { args := [i8Val 255] }
    (u32Val 4294967295) ∧
  PositiveCanaryClaim (mkIntToIntCastProg (.int .i64 true) (.int .i128 true))
    { args := [scalarNatVal .i64 true (Nat.pow 2 64 - 1)] }
    (scalarNatVal .i128 true (Nat.pow 2 128 - 1)) ∧
  PositiveCanaryClaim (mkIntToIntCastProg u8Ty (.int .i32 true))
    { args := [u8Val 255] } (scalarNatVal .i32 true 255) ∧
  PositiveCanaryClaim (mkIntToIntCastProg u32Ty u8Ty) { args := [u32Val 300] }
    (u8Val 44) ∧
  PositiveCanaryClaim (mkIntToIntCastProg .bool (.int .i32 true))
    { args := [.bool true] } (scalarNatVal .i32 true 1) ∧
  PositiveCanaryClaim (mkIntToIntCastProg .char u8Ty)
    { args := [charVal 0x1f600] } (u8Val 0) ∧
  PositiveCanaryClaim (mkIntToIntCastProg u8Ty .char) { args := [u8Val 200] }
    (charVal 200)

/-- Trusted claim for `Anneal.MirWp.canary_negative_int_to_int_cast_anneal`:
1. `300u32 as char` faults with `.unsupported`: only `u8` values convert to
   `char`, and `u8::try_from(300).unwrap()` panics.
2. `-1i8 as char` faults with `.unsupported` (its sign-extended intermediate
   exceeds `255`).
3. An `IntToInt` cast to `bool` faults with `.unsupported`.
4. Casting an uninitialized `u8` local faults with `.undefined`. -/
noncomputable def CanaryNegativeIntToIntCastAnnealClaim : Prop :=
  NegativeCanaryClaim (mkIntToIntCastProg u32Ty .char) { args := [u32Val 300] }
    .unsupported .undefined ∧
  NegativeCanaryClaim (mkIntToIntCastProg i8Ty .char) { args := [i8Val 255] }
    .unsupported .undefined ∧
  NegativeCanaryClaim (mkIntToIntCastProg u8Ty .bool) { args := [u8Val 1] }
    .unsupported .undefined ∧
  NegativeCanaryClaim progCastUninitSourceUb queryEmpty .undefined .unsupported

/-- Trusted claim for `Anneal.MirWp.canary_contract_anneal`:
1. `scalarAsInt` sign-extends signed scalars and zero-extends unsigned ones;
2. `ContractSpecs` discharges `UnitTheorem` on an `unsafe` guarded body with
   matching `ContractSignature`, while `isUnsafe = false` refutes
   `BodyContractSatisfied`, and parameter, unsafety, and return-type
   signature mismatches refute `bodySatisfiesContractEntry` for that same
   body and satisfiable contract, and a `postReturn` the normal return
   violates refutes `BodyContractSatisfied`;
3. in a two-body program, an entry's contract is checked against the body
   its identity names: `canary::safe_unit` with `partialAnyExit` holds,
   `canary::contract_loop` with `totalNormal` is refuted because that loop
   diverges, an entry naming no body is refuted, and a list whose second
   entry is violated refutes `ContractEntriesSatisfied`;
4. `terminates = true` refutes `BodyContractSatisfied` on a `goto 0` loop while
   `terminates = false` permits divergence;
5. `requireInhabited = true` enforces `ContractPreInhabited` inside
   `UnitTheorem`, `requireInhabited = false` waives it, and neither a `False`
   behavioral precondition, a `False` safety precondition on an `unsafe`
   body, nor an uninhabited `!` parameter is `ContractPreInhabited`; and
6. `ContractSpecs` rejects duplicate entry identities and indexes multiple
   entries for $O(\log N)$ safety lookup, and each lookup applies that
   entry's own safety precondition, while an identity with no entry has the
   trivial safety precondition. -/
noncomputable def CanaryContractAnnealClaim : Prop :=
  scalarAsInt { width := .i8, signed := true, bits := BitVec.ofNat 128 255 } =
    Int.negSucc 0 ∧
  scalarAsInt { width := .i8, signed := false, bits := BitVec.ofNat 128 200 } =
    (200 : Int) ∧
  scalarAsInt { width := .i8, signed := true, bits := BitVec.ofNat 128 511 } =
    Int.negSucc 0 ∧
  (∀ s : ScalarVal, scalarAsInt s = decodeScalar s) ∧
  UnitTheorem {
      program := {
        scope := .unit
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canaryContractUnsafeGuardBody true]
      }
      specs := ContractSpecs [{
        identity := "canary::contract_unsafe_guard"
        contract := {
          safetyPre := fun q => q.args = [.bool true]
          postReturn := fun _ out => out.ret = .unit
          effects := EffectMask.totalNormal
        }
        signature := some {
          isUnsafe := true
          params := [.bool]
          ret := .unit
        }
      }]
    } ∧
  (∀ c : FnContract,
      c = {
        safetyPre := fun q => q.args = [.bool true]
        postReturn := fun _ out => out.ret = .unit
        effects := EffectMask.totalNormal
      } →
      ¬ BodyContractSatisfied {
        scope := .unit
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canaryContractUnsafeGuardBody false]
      } 0 (canaryContractUnsafeGuardBody false) c) ∧
  ¬ BodyContractSatisfied {
      scope := .unit
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canaryContractLoopBody]
    } 0 canaryContractLoopBody {
      effects := { terminates := true, noUnwind := true }
    } ∧
  BodyContractSatisfied {
      scope := .unit
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canaryContractLoopBody]
    } 0 canaryContractLoopBody {
      effects := EffectMask.partialAnyExit
    } ∧
  ¬ UnitTheorem {
      program := {
        scope := .unit
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canarySafeUnitBody]
      }
      specs := ContractSpecs [{
        identity := "canary::safe_unit"
        contract := {
          behaviorPre := fun _ => False
          effects := EffectMask.totalNormal
        }
        requireInhabited := true
      }]
    } ∧
  (∀ e : ContractEntry,
      e = {
        identity := "canary::safe_unit"
        contract := {
          behaviorPre := fun _ => False
          effects := EffectMask.totalNormal
        }
        requireInhabited := false
      } →
      UnitTheorem {
        program := {
          scope := .unit
          pointerWidthBits := 64
          mirProfileVersion := 1
          bodies := [canarySafeUnitBody]
        }
        specs := ContractSpecs [e]
      }) ∧
  ¬ ContractPreInhabited canarySafeUnitBody {
      behaviorPre := fun _ => False
      effects := EffectMask.totalNormal
    } ∧
  (∀ e : ContractEntry,
      e = {
        identity := "canary::safe_unit"
        contract := { effects := EffectMask.totalNormal }
      } →
      ¬ UnitTheorem {
        program := {
          scope := .unit
          pointerWidthBits := 64
          mirProfileVersion := 1
          bodies := [canarySafeUnitBody]
        }
        specs := ContractSpecs [e, e]
      }) ∧
  ¬ bodySatisfiesContractEntry {
      scope := .unit
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canaryContractUnsafeGuardBody true]
    } {
      identity := "canary::contract_unsafe_guard"
      contract := {
        safetyPre := fun q => q.args = [.bool true]
        postReturn := fun _ out => out.ret = .unit
        effects := EffectMask.totalNormal
      }
      signature := some {
        isUnsafe := true
        params := [.int .i8 false]
        ret := .unit
      }
      requireInhabited := false
    } ∧
  ¬ bodySatisfiesContractEntry {
      scope := .unit
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canaryContractUnsafeGuardBody true]
    } {
      identity := "canary::contract_unsafe_guard"
      contract := {
        safetyPre := fun q => q.args = [.bool true]
        postReturn := fun _ out => out.ret = .unit
        effects := EffectMask.totalNormal
      }
      signature := some {
        isUnsafe := false
        params := [.bool]
        ret := .unit
      }
      requireInhabited := false
    } ∧
  ¬ bodySatisfiesContractEntry {
      scope := .unit
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canaryContractUnsafeGuardBody true]
    } {
      identity := "canary::contract_unsafe_guard"
      contract := {
        safetyPre := fun q => q.args = [.bool true]
        postReturn := fun _ out => out.ret = .unit
        effects := EffectMask.totalNormal
      }
      signature := some {
        isUnsafe := true
        params := [.bool]
        ret := .bool
      }
      requireInhabited := false
    } ∧
  ¬ BodyContractSatisfied {
      scope := .unit
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canaryContractUnsafeGuardBody true]
    } 0 (canaryContractUnsafeGuardBody true) {
      safetyPre := fun q => q.args = [.bool true]
      postReturn := fun _ out => out.ret = .bool true
      effects := EffectMask.totalNormal
    } ∧
  bodySatisfiesContractEntry {
      scope := .unit
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody, canaryContractLoopBody]
    } {
      identity := "canary::safe_unit"
      contract := { effects := EffectMask.partialAnyExit }
      requireInhabited := false
    } ∧
  ¬ bodySatisfiesContractEntry {
      scope := .unit
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody, canaryContractLoopBody]
    } {
      identity := "canary::missing"
      contract := { effects := EffectMask.partialAnyExit }
      requireInhabited := false
    } ∧
  ¬ ContractPreInhabited (canaryNeverParamBody false) {
      effects := EffectMask.totalNormal
    } ∧
  ¬ bodySatisfiesContractEntry {
      scope := .unit
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody, canaryContractLoopBody]
    } {
      identity := "canary::contract_loop"
      contract := { effects := EffectMask.totalNormal }
      requireInhabited := false
    } ∧
  ¬ ContractEntriesSatisfied {
      scope := .unit
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody, canaryContractLoopBody]
    } [
      { identity := "canary::safe_unit"
        contract := { effects := EffectMask.partialAnyExit }
        requireInhabited := false },
      { identity := "canary::contract_loop"
        contract := { effects := EffectMask.totalNormal }
        requireInhabited := false }
    ] ∧
  ¬ ContractPreInhabited (canaryContractUnsafeGuardBody true) {
      safetyPre := fun _ => False
      effects := EffectMask.totalNormal
    } ∧
  (∀ specs : Specs,
      specs = ContractSpecs [
        { identity := "canary::first"
          contract := {
            safetyPre := fun _ => False
            effects := EffectMask.totalNormal
          } },
        { identity := "canary::second"
          contract := {
            safetyPre := fun q => q.args = [.bool true]
            effects := EffectMask.totalNormal
          } }
      ] →
      specs.safety "canary::second" [.bool true] ∧
      ¬ specs.safety "canary::second" [.bool false] ∧
      ¬ specs.safety "canary::first" [] ∧
      specs.safety "canary::unlisted" []) ∧
  bodyMatchesContractSignature (canaryContractUnsafeGuardBody true) ({
      isUnsafe := true
      params := [.bool]
      ret := .unit
    } : ContractSignature) = true ∧
  (contractEntryRbLookup .empty "canary::missing").isNone = true

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

/-- Profile v2 captured crate + specification bundle alias
(`Trusted.CrateV2`). -/
abbrev CrateV2 := Trusted.MirSemantics.CrateV2

/-- Profile v2 whole-crate verification obligation
(`Trusted.CrateTheoremV2`). -/
noncomputable abbrev CrateTheoremV2 := Trusted.MirSemantics.CrateTheoremV2

/-- Profile v2 proof-unit verification obligation (`Trusted.UnitTheoremV2`). -/
noncomputable abbrev UnitTheoremV2 := Trusted.MirSemantics.UnitTheoremV2

end Trusted

end
