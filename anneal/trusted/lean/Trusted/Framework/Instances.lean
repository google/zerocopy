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
public import Init.Data.List.Basic
public import Trusted.Framework
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Enum
public import Trusted.MirSemantics.Ops
public import Trusted.MirSemantics.Boundary

@[expose] public section

namespace Trusted.Framework

open Trusted.MirAst Trusted.MirSemantics

/-!
# MIR ExecutionModel Instances (`Trusted.Framework.Instances`)

Connects `Trusted.Framework.ExecutionModel` and `FnContract` directly to
`Trusted.MirSemantics` without wrapping inner small-step transitions:

1. **ABI and signature pinning (`AbiKind`, `MirSignature`):** Binds contract
   entries to explicit `isUnsafe`, calling-convention `AbiKind`, parameter
   `MirTy` list, and return `MirTy`.
2. **Profile-parametric MIR model builder (`mkMirExecutionModel`):** Shares one
   `(Query, Val, CallerMemory)` contract representation across Profile v1
   (`MirProfileV1`, bridged to `vendor/lean-miri` under
   `deinitMovedPlace := true` via
   `.biFaultEquiv "lean_miri_v1_deinit_moved_place"`, requiring
   `.configuredReferenceScope` whenever `existsWitness` is claimed) and
   Profile v2 (`MirProfileV2`, unbridged via `.unbridged "mir_profile_v2"`,
   requiring `.callerMemoryThreadIsolation "mir_profile_v2"` unconditionally
   and `.callerRawPtrAliasing "mir_profile_v2"` whenever a body has raw-pointer
   locals), with both profiles requiring `defaultMirDownstreamGaps` via
   `modelGaps`, eliminating per-profile contract duplication while projecting
   `wellFormed` directly to `WellFormed` / `WellFormedV2` with zero WHNF
   overhead.
-/

/-- Function calling-convention ABI tag, corresponding to the admitted
`ExternAbi::Rust` variant in `compiler/rustc_abi/src/extern_abi.rs` lines
20-32 (`rust-lang/rust` commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

```rust
pub enum ExternAbi {
    ...
    /// that's us!
    Rust,
```

Only `rust` (`ExternAbi::Rust`, `extern "Rust"`) is admitted by
`anneal-rustc-capture`; foreign ABI constructors will be added once
`Trusted.MirAst.Body` records per-body ABIs. -/
inductive AbiKind where
  | rust

/-- Structural equality on `AbiKind` without `Decidable` synthesis. -/
def AbiKind.beq : AbiKind → AbiKind → Bool
  | .rust, .rust => true

/-- Mandatory MIR signature pinned on every contract, stub, and refutation
entry, checking `isUnsafe`, calling convention `abi`, parameter types
(`locals[1..=argumentCount]`), and return type (`locals[0]`). -/
structure MirSignature where
  isUnsafe : Bool
  abi      : AbiKind
  params   : List MirTy
  ret      : MirTy

/-- Validate a captured `Body` against `sig`. Until `Trusted.MirAst.Body`
records per-body foreign ABIs (`anneal-rustc-capture` rejects
`abi != ExternAbi::Rust` at extraction time), only `AbiKind.rust` matches
admitted captured bodies. -/
noncomputable def bodyMatchesMirSignature (body : Body)
    (sig : MirSignature) : Bool :=
  (body.isUnsafe == sig.isUnsafe) &&
    AbiKind.beq .rust sig.abi &&
    Nat.beq body.argumentCount sig.params.length &&
    MirTy.beqList ((body.locals.drop 1).take body.argumentCount) sig.params &&
    match body.locals with
    | retTy :: _ => MirTy.beq retTy sig.ret
    | [] => false

/-- Project `Trusted.MirSemantics.TerminalOut` into
`TerminalOutcome Val CallerMemory`. -/
noncomputable def mapMirTerminalOut :
    TerminalOut → TerminalOutcome Val CallerMemory
  | .returned out => .returned out.ret out.callerMem
  | .unwound mem => .unwound mem
  | .aborted mem => .aborted mem

/-- Lift a `TerminalOut` behavior relation to
`TerminalOutcome Val CallerMemory`. -/
@[reducible] def MirProduces
    (behaviorFn : Program → Query → TerminalOut → Prop)
    (p : Program) (q : Query) (res : TerminalOutcome Val CallerMemory) : Prop :=
  ∃ out : TerminalOut, behaviorFn p q out ∧ mapMirTerminalOut out = res

/-- Check that a returned Profile v1 `(ret, mem)` matches `body.locals[0]` and
preserves Profile v1's empty caller-memory invariant (`mem = ⟨[]⟩`). -/
def ValidMirReturnVal (body : Body) (ret : Val)
    (mem : CallerMemory) : Prop :=
  match MirSemantics.getElem? body.locals 0 with
  | some retTy => checkVal ret retTy = true ∧ mem = ⟨[]⟩
  | none => False

/-- Return `true` iff `p` is a selected proof-unit capture (`.unit`) rather
than a whole-crate capture (`.crate`). -/
def mirProgramIsPartialScope (p : Program) : Bool :=
  match p.scope with
  | .unit => true
  | .crate => false

/-- Shared program-level static header admission check parameterized by
`profileVersion`. Per-body static admission (`bodyAdmitted`) is checked
directly in `EnvelopeCommonValid` via `M.bodyAt` rather than via a linear-depth
list fold, avoiding `O(bodies.length)` reduction depth on crate-scale captures.
-/
noncomputable def mirProgramAdmitted (profileVersion : Nat)
    (p : Program) : Bool :=
  Nat.beq p.pointerWidthBits 64 &&
    Nat.beq p.mirProfileVersion profileVersion &&
    !p.bodies.isEmpty &&
    Nat.blt p.entryDefId p.bodies.length

/-- Canonical downstream compilation and hardware execution stages outside a
Pass-1 post-cleanup MIR proof. -/
@[reducible] def defaultMirDownstreamGaps : List DisclosedGap :=
  [ .unverifiedDownstream "rustc_mir_opt",
    .unverifiedDownstream "llvm_codegen",
    .unverifiedDownstream "linker",
    .unverifiedDownstream "microarch_timing" ]

/-- Construct a profile-parametric MIR `ExecutionModel` over
`(Program, Body, MirSignature, Query, Val, CallerMemory)`. `MirProfileV1` and
`MirProfileV2` instantiate this builder below, and additional MIR profiles plug
in their per-profile static admission, entry-domain, well-formedness, behavior,
divergence, and required-gap predicates without duplicating contract or
envelope definitions. -/
@[reducible] noncomputable def mkMirExecutionModel
    (profileId : String)
    (profileVersion : Nat)
    (oracleGrade : OracleGrade)
    (bodyAdmitted : Program → Body → Bool)
    (bodyIsExternal : Body → Bool)
    (modelGaps : List DisclosedGap)
    (requiredGaps : Body → List DisclosedGap)
    (claimShapeGaps : ClaimShape → List DisclosedGap)
    (entryDom : Body → Query → Prop)
    (returnValid : Body → Val → CallerMemory → Prop)
    (memValid : CallerMemory → Prop)
    (wellFormedFn : Program → Query → Prop)
    (behaviorFn : Program → Query → TerminalOut → Prop)
    (divergesFn : Program → Query → Prop)
    (faultsUBFn : Program → Query → Prop) :
    ExecutionModel Program Body MirSignature Query Val CallerMemory :=
  { profileId := profileId
    oracleGrade := oracleGrade
    programAdmitted := mirProgramAdmitted profileVersion
    bodyAdmitted := bodyAdmitted
    isPartialScope := mirProgramIsPartialScope
    bodyAt := fun p defId => MirSemantics.getElem? p.bodies defId
    uniqueIdentities := fun p => bodiesHaveUniqueIdentities p.bodies
    bodyIdentity := Body.identity
    bodyIsUnsafe := Body.isUnsafe
    bodyIsExternal := bodyIsExternal
    bodyMatchesSig := bodyMatchesMirSignature
    modelGaps := modelGaps
    requiredGaps := requiredGaps
    claimShapeGaps := claimShapeGaps
    entryDom := entryDom
    returnValid := returnValid
    memValid := memValid
    execForBody := entryProgForBody
    wellFormed := wellFormedFn
    produces := MirProduces behaviorFn
    diverges := divergesFn
    faultsUB := faultsUBFn }

/-- Claim-shape gaps required by Profile v1: `Operand.move` deinitialization is
a conservative over-approximation of upstream `rustc_const_eval`
(`Trusted.MirSemantics`), so Pass-2 `FaultEquivalenceClaim` certifies
`existsWitness` refutations only relative to the patched
`deinitMovedPlace := true` `lean-miri` configuration (`docs/trust-model.md`).
Universal safety and termination remain sound without additional disclosure. -/
def mirProfileV1ClaimShapeGaps : ClaimShape → List DisclosedGap
  | .existsWitness =>
      [.configuredReferenceScope "lean_miri_v1_deinit_moved_place"]
  | _ => []

/-- Profile v1 MIR `ExecutionModel` projecting directly onto
`BodyStaticAdmitted`, `ValidEntryArgs` (with empty `callerMem := ⟨[]⟩`),
`WellFormed`, `Behavior`, `Diverges`, and
`ReachesResult ... (.fault .undefined)` under bidirectional correspondence
against the `deinitMovedPlace := true` `lean-miri` configuration
(`OracleGrade.biFaultEquiv "lean_miri_v1_deinit_moved_place"`, requiring
`defaultMirDownstreamGaps` unconditionally and
`DisclosedGap.configuredReferenceScope` whenever `existsWitness` is claimed).
-/
@[reducible] noncomputable def MirProfileV1 :
    ExecutionModel Program Body MirSignature Query Val CallerMemory :=
  mkMirExecutionModel
    "mir_profile_v1"
    1
    (.biFaultEquiv "lean_miri_v1_deinit_moved_place")
    BodyStaticAdmitted
    (fun _ => false)
    defaultMirDownstreamGaps
    (fun _ => [])
    mirProfileV1ClaimShapeGaps
    (fun body q => ValidEntryArgs body q.args ∧ q.callerMem = ⟨[]⟩)
    ValidMirReturnVal
    (fun mem => mem = ⟨[]⟩)
    WellFormed
    Behavior
    Diverges
    (fun p q => ReachesResult p q (.fault .undefined))

/-- Check that a returned Profile v2 `(ret, mem)` satisfies `checkValV2` on
`body.locals[0]`, `validCallerMemory`, caller-memory reference confinement
(`refsStayInCallerMem`), pointee validity (`refsValidInMem`), and mutable
borrow disjointness (`spansPairwiseDisjoint`). -/
def ValidMirReturnValV2 (body : Body) (ret : Val)
    (mem : CallerMemory) : Prop :=
  match MirSemantics.getElem? body.locals 0 with
  | some retTy =>
    checkValV2 ret retTy = true ∧
    validCallerMemory mem = true ∧
    refsStayInCallerMem mem retTy ret = true ∧
    refsValidInMem (entryMemoryWithCaller mem) retTy ret = true ∧
    spansPairwiseDisjoint (refAccessSpans retTy ret) = true
  | none => False

/-- Per-body semantic gaps required by Profile v2 (`mir_profile_v2`): every
Profile v2 verification assumes every memory location the body touches,
including caller memory, is isolated from other threads for the call's duration
(no foreign writes to memory it reads or writes, and no foreign reads of memory
it writes; see `docs/trust-model.md` §Concurrency,
`DisclosedGap.callerMemoryThreadIsolation "mir_profile_v2"`), and bodies
containing raw-pointer locals also omit intra-body aliasing checks
(`DisclosedGap.callerRawPtrAliasing "mir_profile_v2"`). -/
noncomputable def mirProfileV2RequiredGaps (body : Body) :
    List DisclosedGap :=
  if tyListHasRawPtrV2 body.locals then
    [.callerMemoryThreadIsolation "mir_profile_v2",
     .callerRawPtrAliasing "mir_profile_v2"]
  else
    [.callerMemoryThreadIsolation "mir_profile_v2"]

/-- Profile v2 MIR `ExecutionModel` projecting directly onto
`BodyStaticAdmittedV2`, `ValidEntryArgsV2`, `ValidMirReturnValV2`,
`WellFormedV2`, `BehaviorV2`, `DivergesV2`, and
`ReachesResultV2 ... (.fault .undefined)` under
`OracleGrade.unbridged "mir_profile_v2"` (requiring `defaultMirDownstreamGaps`
unconditionally) until Pass-2 Profile v2 `lean-miri` correspondence lands. -/
@[reducible] noncomputable def MirProfileV2 :
    ExecutionModel Program Body MirSignature Query Val CallerMemory :=
  mkMirExecutionModel
    "mir_profile_v2"
    2
    (.unbridged "mir_profile_v2")
    BodyStaticAdmittedV2
    (fun _ => false)
    defaultMirDownstreamGaps
    mirProfileV2RequiredGaps
    (fun _ => [])
    ValidEntryArgsV2
    ValidMirReturnValV2
    (fun mem => validCallerMemory mem = true)
    WellFormedV2
    BehaviorV2
    DivergesV2
    (fun p q => ReachesResultV2 p q (.fault .undefined))

/-- Unified MIR verified contract entry alias used by
`MirEnvelopeTheoremV1`/`MirEnvelopeTheoremV2`. -/
abbrev MirVerifiedEntry := VerifiedEntry MirSignature Query Val CallerMemory

/-- Unified MIR external callee stub alias used by
`MirEnvelopeTheoremV1`/`MirEnvelopeTheoremV2`. -/
abbrev MirAssumedStub := AssumedStub MirSignature Query Val CallerMemory

/-- Unified MIR existential UB refutation entry alias used by
`MirEnvelopeTheoremV1`/`MirEnvelopeTheoremV2`. -/
abbrev MirRefutationEntry := RefutationEntry MirSignature Query

/-- Unified MIR verification envelope alias. -/
abbrev MirVerificationEnvelope :=
  VerificationEnvelope Program Body MirSignature Query Val CallerMemory

end Trusted.Framework

end
