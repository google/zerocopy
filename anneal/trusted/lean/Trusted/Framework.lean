-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:refinement
module
prelude
public import Init.NotationExtra
public import Init.Data.List.Basic

@[expose] public section

namespace Trusted.Framework

/-!
# Profile-Parametric Verification Envelope (`Trusted.Framework`)

Thin, tactic-free claim and correspondence spine wrapping Anneal's outer
verification boundary without wrapping inner small-step execution transitions:

1. **Claim-shape and transfer-license discipline (`ClaimShape`,
   `OracleGrade`):** Encodes the closed five-shape property vocabulary and
   upper-triangular transfer license (`OracleGrade.licenses`), ensuring one-way
   forward simulations never license existential UB refutations
   (`existsWitness`) or `termination` transfer, configured-reference
   refutations disclose `DisclosedGap.configuredReferenceScope`, and unbridged
   profiles disclose `DisclosedGap.unbridgedSemantics`.
2. **Closed-constructor assumption ledger (`DisclosedGap`,
   `VerificationEnvelope`):** Restricts `VerificationEnvelope` to two audited
   constructors (`structured` via `mkEnvelope` and `legacy` via
   `mkLegacyEnvelope`, making mixed or unvetted envelope states unrepresentable
   while preserving full `@[expose]` WHNF reduction in Lean 4 `module` mode),
   keeping scope limits, unbridged profiles, raw-pointer aliasing assumptions,
   external callee stubs, waived inhabitation checks, and unmodeled downstream
   toolchain stages explicit in the root theorem statement.
3. **Profile-parametric contracts (`ExecutionModel`, `EffectMask`,
   `FnContract`, `NonVacuousEntry`, `StubRealizable`):** Parameterizes function
   contracts over `(Query, Ret, Mem)` with uniform positive-polarity 3-bit
   `EffectMask` fields (no implicit field defaults), `isUnsafe`-gated safety
   preconditions, constructive parameter-domain non-vacuity, and external stub
   realizability.
-/

/-- Uniform terminal outcome across value-only, memory-aware, abort-aware, and
machine-level semantic profiles. -/
inductive TerminalOutcome (Ret Mem : Type) where
  | returned (ret : Ret) (mem : Mem)
  | unwound  (mem : Mem)
  | aborted  (mem : Mem)

/-- Closed five-shape claim vocabulary in canonical lexicographical order. -/
inductive ClaimShape where
  | existsWitness
  | forallSafety
  | generalHyper
  | subsetHyper
  | termination

/-- Reference-oracle correspondence grade licensing claim shapes:
- `unbridged profileId`: No Pass-2 correspondence proof; permits safety and
  termination claims inside the model only when `.unbridgedSemantics profileId`
  is disclosed in `VerificationEnvelope.gaps`.
- `forwardSim oracleId`: Reference UB implies model fault and reference outcomes
  are contained in model outcomes under well-founded stutter or lockstep
  simulation; licenses universal safety and subset-closed hyperproperties, never
  `termination` (model termination alone does not rule out a divergent
  reference execution without divergence reflection) or existential
  `existsWitness` refutations.
- `biFaultEquiv oracleId`: Bidirectional fault equivalence plus behavioral and
  divergence equivalence; additionally licenses `existsWitness` refutations and
  `termination`, while still excluding stuttering-sensitive `generalHyper`. -/
inductive OracleGrade where
  | unbridged    (profileId : String)
  | forwardSim   (oracleId : String)
  | biFaultEquiv (oracleId : String)

/-- Upper-triangular claim-shape license check for `OracleGrade`. -/
def OracleGrade.licenses : OracleGrade → ClaimShape → Bool
  | .unbridged _,    .forallSafety  => true
  | .unbridged _,    .termination   => true
  | .unbridged _,    _              => false
  | .forwardSim _,   .forallSafety  => true
  | .forwardSim _,   .subsetHyper   => true
  | .forwardSim _,   _              => false
  | .biFaultEquiv _, .existsWitness => true
  | .biFaultEquiv _, .forallSafety  => true
  | .biFaultEquiv _, .subsetHyper   => true
  | .biFaultEquiv _, .termination   => true
  | .biFaultEquiv _, .generalHyper  => false

/-- Machine-extracted assumption and scope-gap ledger carried on the root
verification obligation (`VerificationEnvelope.gaps`). -/
inductive DisclosedGap where
  | unbridgedSemantics          (profileId : String)
  | callerRawPtrAliasing        (profileId : String)
  | callerMemoryThreadIsolation (profileId : String)
  | configuredReferenceScope    (oracleId : String)
  | assumedExternalCallee       (identity : String)
  | waivedInhabitation          (identity : String)
  | selectedUnitScope
  | rawLegacySpec
  | unverifiedDownstream        (stage : String)

/-- Profile-parametric operational or denotational model plugging directly into
concrete semantics without wrapping inner step transitions. -/
structure ExecutionModel (Prog Body Sig Query Ret Mem : Type) where
  profileId        : String
  oracleGrade      : OracleGrade
  programAdmitted  : Prog → Bool
  bodyAdmitted     : Prog → Body → Bool
  isPartialScope   : Prog → Bool
  bodyAt           : Prog → Nat → Option Body
  uniqueIdentities : Prog → Bool
  bodyIdentity     : Body → String
  bodyIsUnsafe     : Body → Bool
  bodyIsExternal   : Body → Bool
  bodyMatchesSig   : Body → Sig → Bool
  modelGaps        : List DisclosedGap
  requiredGaps     : Body → List DisclosedGap
  claimShapeGaps   : ClaimShape → List DisclosedGap
  entryDom         : Body → Query → Prop
  returnValid      : Body → Ret → Mem → Prop
  memValid         : Mem → Prop
  execForBody      : Prog → Nat → Prog
  wellFormed       : Prog → Query → Prop
  produces         : Prog → Query → TerminalOutcome Ret Mem → Prop
  diverges         : Prog → Query → Prop
  faultsUB         : Prog → Query → Prop

/-- Constructive parameter-domain non-vacuity: either a valid entry `q`
satisfies `pre q`, or `entryDom` is structurally uninhabited (such as `!`).
Avoids `Classical.choice` while rejecting contradictory preconditions on
inhabited parameter domains. -/
def NonVacuousEntry {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem)
    (body : Body) (pre : Query → Prop) : Prop :=
  (∃ q : Query, M.entryDom body q ∧ pre q) ∨
    (∀ q : Query, ¬ M.entryDom body q)

/-- Explicit 3-bit positive-polarity effect guarantee mask (`true` = stronger
guarantee / narrower permitted non-normal outcomes) with zero field defaults so
every specification states all three effect bits explicitly.

Note that `terminates = true` only rules out `M.diverges` (infinite step
traces). Under MIR `--panic abort`, `.aborted` is modeled as a terminal outcome
even though an unverified panic hook or runtime may diverge, so a literal
termination claim under `--panic abort` also requires `noAbort = true`. -/
structure EffectMask where
  terminates : Bool
  noUnwind   : Bool
  noAbort    : Bool

/-- Unified function contract parameterized over `(Query, Ret, Mem)`, serving
both value-only and memory-aware MIR profiles without type duplication. -/
structure FnContract (Query Ret Mem : Type) where
  safetyPre   : Query → Prop := fun _ => True
  behaviorPre : Query → Prop := fun _ => True
  postReturn  : Query → Ret → Mem → Prop := fun _ _ _ => True
  postUnwind  : Query → Mem → Prop := fun _ _ => True
  postAbort   : Query → Mem → Prop := fun _ _ => True
  effects     : EffectMask

/-- Safe functions structurally ignore `safetyPre`: caller safety preconditions
take effect only when `isUnsafe = true`. -/
def FnContract.effectiveSafetyPre {Q R M : Type}
    (c : FnContract Q R M) (isUnsafe : Bool) (q : Q) : Prop :=
  isUnsafe = true → c.safetyPre q

/-- Combined precondition gating functional postconditions and effect
obligations across safe and unsafe functions. -/
def FnContract.effectiveBehaviorPre {Q R M : Type}
    (c : FnContract Q R M) (isUnsafe : Bool) (q : Q) : Prop :=
  c.effectiveSafetyPre isUnsafe q ∧ c.behaviorPre q

/-- External callee stub summary paired with its expected signature. -/
structure AssumedStub (Sig Query Ret Mem : Type) where
  identity : String
  sig      : Sig
  contract : FnContract Query Ret Mem

/-- Realizability guard ensuring an inconsistent external callee summary (such
as `postReturn := False` when `terminates`, `noUnwind`, and `noAbort` are all
`true`) cannot prove `False`. -/
def StubRealizable {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem)
    (body : Body) (c : FnContract Query Ret Mem) : Prop :=
  ∀ q : Query,
    M.entryDom body q →
    c.effectiveBehaviorPre (M.bodyIsUnsafe body) q →
    (c.effects.terminates = false) ∨
    (∃ r m, M.returnValid body r m ∧ c.postReturn q r m) ∨
    (c.effects.noUnwind = false ∧ ∃ m, M.memValid m ∧ c.postUnwind q m) ∨
    (c.effects.noAbort = false ∧ ∃ m, M.memValid m ∧ c.postAbort q m)

/-- Path- and signature-pinned verified function contract entry. -/
structure VerifiedEntry (Sig Query Ret Mem : Type) where
  identity         : String
  sig              : Sig
  contract         : FnContract Query Ret Mem
  requireInhabited : Bool := true

/-- Path- and signature-pinned existential UB refutation entry (`existsWitness`,
licensed only when `M.oracleGrade` proves bidirectional fault equivalence). For
`unsafe` bodies (`M.bodyIsUnsafe body = true`), `safetyPre` pins the caller
safety contract that any valid UB witness must satisfy so expected caller
misuse cannot be reported as a counterexample (no default, forcing explicit
specification). -/
structure RefutationEntry (Sig Query : Type) where
  identity   : String
  sig        : Sig
  safetyPre  : Query → Prop
  witnessPre : Query → Prop := fun _ => True

/-- First-order pairwise-distinct non-empty identity predicate preventing
duplicate or overlapping item declarations across `entries`, `stubs`, and
`refutations`. Marked `noncomputable` so Lean emits no partial `._unsafe_rec`
helper. -/
noncomputable def NoDupStrings : List String → Prop
  | [] => True
  | s :: rest => s ≠ "" ∧ (∀ t, t ∈ rest → s ≠ t) ∧ NoDupStrings rest

/-- Per-body verification judgment for a `VerifiedEntry` at index `defId`,
restricted to non-external captured bodies (`M.bodyIsExternal body = false`).
-/
def BodySatisfiesEntry {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem)
    (prog : Prog) (defId : Nat) (gaps : List DisclosedGap)
    (body : Body) (e : VerifiedEntry Sig Query Ret Mem) : Prop :=
  let ep := M.execForBody prog defId
  let isU := M.bodyIsUnsafe body
  M.bodyIsExternal body = false ∧
  M.bodyIdentity body = e.identity ∧
  M.bodyMatchesSig body e.sig = true ∧
  (∀ g, g ∈ M.requiredGaps body → g ∈ gaps) ∧
  (∀ q, M.entryDom body q → e.contract.effectiveSafetyPre isU q →
    M.wellFormed ep q) ∧
  (∀ q, M.entryDom body q → e.contract.effectiveBehaviorPre isU q →
    (e.contract.effects.terminates = true → ¬ M.diverges ep q) ∧
    (∀ r m, M.produces ep q (.returned r m) →
      M.returnValid body r m ∧ e.contract.postReturn q r m) ∧
    (∀ m, M.produces ep q (.unwound m) →
      M.memValid m ∧ e.contract.effects.noUnwind = false ∧
      e.contract.postUnwind q m) ∧
    (∀ m, M.produces ep q (.aborted m) →
      M.memValid m ∧ e.contract.effects.noAbort = false ∧
      e.contract.postAbort q m)) ∧
  ((e.requireInhabited = true ∧
      NonVacuousEntry M body (e.contract.effectiveBehaviorPre isU)) ∨
    (e.requireInhabited = false ∧ .waivedInhabitation e.identity ∈ gaps))

/-- Per-body assumption judgment for an `AssumedStub`. Requires
`M.bodyIsExternal body = true` so captured local bodies can never be waived as
assumed external callees. -/
def BodySatisfiesStub {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem)
    (gaps : List DisclosedGap) (body : Body)
    (s : AssumedStub Sig Query Ret Mem) : Prop :=
  M.bodyIsExternal body = true ∧
  M.bodyIdentity body = s.identity ∧
  M.bodyMatchesSig body s.sig = true ∧
  (∀ g, g ∈ M.requiredGaps body → g ∈ gaps) ∧
  .assumedExternalCallee s.identity ∈ gaps ∧
  StubRealizable M body s.contract

/-- Per-body existential UB refutation judgment (`ClaimShape.existsWitness`,
restricted to non-external captured bodies). Requires a well-typed entry witness
`q` satisfying `r.witnessPre` and, when `M.bodyIsUnsafe body = true`, the
caller safety contract `r.safetyPre` before reaching `M.faultsUB`. -/
def BodyRefutesUB {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem)
    (prog : Prog) (defId : Nat) (gaps : List DisclosedGap)
    (body : Body) (r : RefutationEntry Sig Query) : Prop :=
  M.bodyIsExternal body = false ∧
  M.bodyIdentity body = r.identity ∧
  M.bodyMatchesSig body r.sig = true ∧
  (∀ g, g ∈ M.requiredGaps body → g ∈ gaps) ∧
  ∃ q : Query,
    M.entryDom body q ∧
    (M.bodyIsUnsafe body = true → r.safetyPre q) ∧
    r.witnessPre q ∧
    M.faultsUB (M.execForBody prog defId) q

/-- Per-body legacy `Specs` safety wrapper judgment, permitted only for
non-external captured bodies when `DisclosedGap.rawLegacySpec` is recorded in
`gaps`. -/
@[reducible] def LegacyBodySatisfied
    {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem)
    (prog : Prog) (defId : Nat) (gaps : List DisclosedGap)
    (safetyFn : String → Query → Prop) (body : Body) : Prop :=
  M.bodyIsExternal body = false ∧
  (∀ g, g ∈ M.requiredGaps body → g ∈ gaps) ∧
  ∀ q : Query,
    M.entryDom body q →
    (M.bodyIsUnsafe body = true → safetyFn (M.bodyIdentity body) q) →
    M.wellFormed (M.execForBody prog defId) q

/-- Closed two-constructor verification envelope ensuring every obligation is
either a structured contract envelope (`structured`, built via `mkEnvelope`) or
an explicit legacy `Specs` compatibility envelope (`legacy`, built via
`mkLegacyEnvelope` and forced by `EnvelopeTheorem` to disclose
`DisclosedGap.rawLegacySpec`). Unvetted or mixed states are unrepresentable,
and all projections unfold transparently across Lean 4 `module` boundaries. -/
inductive VerificationEnvelope (Prog Body Sig Query Ret Mem : Type) where
  | structured
      (model : ExecutionModel Prog Body Sig Query Ret Mem)
      (program : Prog)
      (entries : List (VerifiedEntry Sig Query Ret Mem))
      (stubs : List (AssumedStub Sig Query Ret Mem))
      (refutations : List (RefutationEntry Sig Query))
      (claimShapes : List ClaimShape)
      (gaps : List DisclosedGap)
  | legacy
      (model : ExecutionModel Prog Body Sig Query Ret Mem)
      (program : Prog)
      (safetyFn : String → Query → Prop)
      (propertyFn : Prog → Prop)
      (claimShapes : List ClaimShape)
      (gaps : List DisclosedGap)

/-- Audited constructor for structured `VerifiedEntry` / `AssumedStub` /
`RefutationEntry` verification envelopes. -/
@[reducible] def mkEnvelope {Prog Body Sig Query Ret Mem : Type}
    (model : ExecutionModel Prog Body Sig Query Ret Mem)
    (program : Prog)
    (entries : List (VerifiedEntry Sig Query Ret Mem))
    (stubs : List (AssumedStub Sig Query Ret Mem) := [])
    (refutations : List (RefutationEntry Sig Query) := [])
    (claimShapes : List ClaimShape)
    (gaps : List DisclosedGap) :
    VerificationEnvelope Prog Body Sig Query Ret Mem :=
  .structured model program entries stubs refutations claimShapes gaps

/-- Audited compatibility constructor wrapping legacy `Specs` bundles
(`EnvelopeTheorem` enforces `.rawLegacySpec ∈ gaps`). -/
@[reducible] def mkLegacyEnvelope
    {Prog Body Sig Query Ret Mem : Type}
    (model : ExecutionModel Prog Body Sig Query Ret Mem)
    (program : Prog)
    (safetyFn : String → Query → Prop)
    (propertyFn : Prog → Prop)
    (claimShapes : List ClaimShape)
    (gaps : List DisclosedGap) :
    VerificationEnvelope Prog Body Sig Query Ret Mem :=
  .legacy model program safetyFn propertyFn claimShapes gaps

/-- Require unbridged semantic profiles to match `profileId` and disclose
`.unbridgedSemantics profileId` in `gaps`, and require bridged grades to carry
non-empty oracle identifiers. -/
@[reducible] def EnvelopeGradeDisclosed
    (profileId : String) (grade : OracleGrade) (gaps : List DisclosedGap) :
    Prop :=
  match grade with
  | .unbridged pid    => pid = profileId ∧ .unbridgedSemantics pid ∈ gaps
  | .forwardSim oid   => oid ≠ ""
  | .biFaultEquiv oid => oid ≠ ""

/-- Shared model, program, scope, oracle-grade, and claim-shape invariants
enforced identically across `structured` and `legacy` envelopes. Note that
`claimShapes` declares an upper bound of licensed claim shapes; receipt
consumers must intersect `claimShapes` with the envelope's actual `entries` and
`refutations` rather than treating `claimShapes` alone as a non-empty witness
set. -/
@[reducible] def EnvelopeCommonValid
    {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem)
    (program : Prog) (claimShapes : List ClaimShape)
    (gaps : List DisclosedGap) : Prop :=
  M.profileId ≠ "" ∧
  M.programAdmitted program = true ∧
  (∀ (defId : Nat) (body : Body),
    M.bodyAt program defId = some body →
    M.bodyAdmitted program body = true) ∧
  M.uniqueIdentities program = true ∧
  (M.isPartialScope program = true → .selectedUnitScope ∈ gaps) ∧
  EnvelopeGradeDisclosed M.profileId M.oracleGrade gaps ∧
  (∀ cs, cs ∈ claimShapes →
    M.oracleGrade.licenses cs = true ∧
    (∀ g, g ∈ M.claimShapeGaps cs → g ∈ gaps)) ∧
  (∀ g, g ∈ M.modelGaps → g ∈ gaps)

/-- Generic profile-parametric verification envelope obligation enforcing static
program admission, unique body and entry identities, model-wide gap disclosure
(`modelGaps`), partial-scope disclosure, unbridged-profile disclosure,
claim-shape licensing against `M.oracleGrade` (as an upper bound; backing any
bridged `M.oracleGrade` requires a separate Pass-2 correspondence certificate
pinned to concrete simulation claims), constructive non-vacuity, external-only
stub admission (`bodyIsExternal`) and realizability, and complete bidirectional
body accounting. Pass-1 target verification roots must pin `ExecutionModel`
inside `Trusted.*` (via `Trusted.MirEnvelopeTheoremV1`,
`Trusted.MirEnvelopeTheoremV2`, or `Trusted.{Crate,Unit}EnvelopeTheorem{,V2}`)
rather than letting specification or proof modules choose an arbitrary model.
-/
@[reducible] def EnvelopeTheorem
    {Prog Body Sig Query Ret Mem : Type}
    (env : VerificationEnvelope Prog Body Sig Query Ret Mem) : Prop :=
  match env with
  | .structured M program entries stubs refutations claimShapes gaps =>
    let entryIds := entries.map VerifiedEntry.identity
    let stubIds := stubs.map AssumedStub.identity
    let refIds := refutations.map RefutationEntry.identity
    let allDeclaredIds := entryIds ++ stubIds ++ refIds
    EnvelopeCommonValid M program claimShapes gaps ∧
    (∀ e, e ∈ entries →
      ClaimShape.forallSafety ∈ claimShapes ∧
      (e.contract.effects.terminates = true →
        ClaimShape.termination ∈ claimShapes)) ∧
    NoDupStrings allDeclaredIds ∧
    (∀ e, e ∈ entries →
      ∃ (defId : Nat) (body : Body),
        M.bodyAt program defId = some body ∧
        BodySatisfiesEntry M program defId gaps body e) ∧
    (∀ s, s ∈ stubs →
      ∃ (defId : Nat) (body : Body),
        M.bodyAt program defId = some body ∧
        BodySatisfiesStub M gaps body s) ∧
    (∀ r, r ∈ refutations →
      ClaimShape.existsWitness ∈ claimShapes ∧
      ∃ (defId : Nat) (body : Body),
        M.bodyAt program defId = some body ∧
        BodyRefutesUB M program defId gaps body r) ∧
    (∀ (defId : Nat) (body : Body),
      M.bodyAt program defId = some body →
      M.bodyIdentity body ∈ allDeclaredIds)
  | .legacy M program safetyFn propertyFn claimShapes gaps =>
    EnvelopeCommonValid M program claimShapes gaps ∧
    DisclosedGap.rawLegacySpec ∈ gaps ∧
    ClaimShape.forallSafety ∈ claimShapes ∧
    (∀ (defId : Nat) (body : Body),
      M.bodyAt program defId = some body →
      LegacyBodySatisfied M program defId gaps safetyFn body) ∧
    propertyFn program

end Trusted.Framework

end
