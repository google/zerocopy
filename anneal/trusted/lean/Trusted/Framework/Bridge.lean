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
public import Trusted.Framework.Instances
public import Trusted.MirSemantics.Boundary

@[expose] public section

namespace Trusted.Framework

open Trusted.MirAst Trusted.MirSemantics

/-!
# Oracle Certificate Interface & `@[reducible]` Compatibility Bridges
(`Trusted.Framework.Bridge`)

1. **Offline Pass-2 oracle certificate (`OracleCertificate`):** Parameterizes
   reference-oracle certification over `forwardSimClaim` and
   `biFaultEquivClaim` propositions so offline Pass-2 correspondence binds
   `MirProfileV1` to `Trusted.Correspondence.CorrespondenceClaim` and
   `Trusted.Correspondence.FaultEquivalenceClaim` without importing
   `vendor/lean-miri` into the runtime Pass-1 bundle. Because those two claim
   parameters are free `Prop` arguments here, `OracleCertificate` carries force
   only when instantiated against concrete Pass-2 correspondence claims.
2. **Model-pinned structured Pass-1 roots (`MirEnvelopeTheoremV1`,
   `MirEnvelopeTheoremV2`) and legacy `@[reducible]` compatibility bridges
   (`CrateEnvelopeTheorem`, `UnitEnvelopeTheorem`, `CrateEnvelopeTheoremV2`,
   `UnitEnvelopeTheoremV2`):** Fixes `ExecutionModel` inside `Trusted.*` to
   `MirProfileV1` or `MirProfileV2` so neither specification nor proof modules
   can substitute a synthetic `ExecutionModel`. Wraps existing `Crate`
   (`Specs`) and `CrateV2` (`SpecsV2`) obligations into `VerificationEnvelope`
   with explicit profile, downstream-stage, scope, raw-pointer aliasing, and
   `rawLegacySpec` gap disclosures, unfolding directly to
   `WellFormed`/`WellFormedV2` and `specs.property` over `(Query, CallerMemory)`
   and proved propositionally equivalent to `CrateTheorem`, `UnitTheorem`,
   `CrateTheoremV2`, and `UnitTheoremV2` in `Anneal.Framework`.
-/

/-- Pass-2 correspondence certificate record associating an `ExecutionModel`'s
declared `oracleGrade` with `forwardSimClaim` and (when `biFaultEquiv`)
`biFaultEquivClaim`, while rejecting `.unbridged` grades fail-closed. Because
`forwardSimClaim` and `biFaultEquivClaim` are free `Prop` parameters, the bare
structure guarantees nothing until a Pass-2 root instantiates them with
concrete correspondence propositions (such as `CorrespondenceClaim` and
`FaultEquivalenceClaim`). -/
structure OracleCertificate {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem)
    (grade : OracleGrade)
    (forwardSimClaim : Prop)
    (biFaultEquivClaim : Prop) : Prop where
  grade_eq      : M.oracleGrade = grade
  non_unbridged : ∀ pid : String, grade ≠ .unbridged pid
  forward_sim   : forwardSimClaim
  fault_equiv   : (∃ oid : String, grade = .biFaultEquiv oid) →
                    biFaultEquivClaim

/-- Default disclosed gaps for a legacy whole-crate `Crate` verification. -/
@[reducible] def legacyCrateGaps : List DisclosedGap :=
  .rawLegacySpec :: defaultMirDownstreamGaps

/-- Default disclosed gaps for a legacy selected-unit `Crate` verification. -/
@[reducible] def legacyUnitGaps : List DisclosedGap :=
  .selectedUnitScope :: .rawLegacySpec :: defaultMirDownstreamGaps

/-- Wrap a Profile v1 whole-crate `Crate` into a `MirVerificationEnvelope`. -/
@[reducible] noncomputable def legacyCrateEnvelope (c : Crate) :
    MirVerificationEnvelope :=
  mkLegacyEnvelope
    MirProfileV1
    c.program
    (fun id q => c.specs.safety id q.args)
    c.specs.property
    [.forallSafety]
    legacyCrateGaps

/-- Wrap a Profile v1 selected-unit `Crate` into a `MirVerificationEnvelope`. -/
@[reducible] noncomputable def legacyUnitEnvelope (c : Crate) :
    MirVerificationEnvelope :=
  mkLegacyEnvelope
    MirProfileV1
    c.program
    (fun id q => c.specs.safety id q.args)
    c.specs.property
    [.forallSafety]
    legacyUnitGaps

/-- `@[reducible]` whole-crate envelope obligation equivalent to
`Trusted.MirSemantics.CrateTheorem`. -/
@[reducible] def CrateEnvelopeTheorem (c : Crate) : Prop :=
  c.program.scope = .crate ∧ EnvelopeTheorem (legacyCrateEnvelope c)

/-- `@[reducible]` selected-unit envelope obligation equivalent to
`Trusted.MirSemantics.UnitTheorem`. -/
@[reducible] def UnitEnvelopeTheorem (c : Crate) : Prop :=
  c.program.scope = .unit ∧ EnvelopeTheorem (legacyUnitEnvelope c)

/-- Program-level semantic, thread-isolation, and raw-pointer aliasing gap
disclosures for Profile v2 (`unbridgedSemantics` and
`callerMemoryThreadIsolation` unconditionally, plus `callerRawPtrAliasing`
whenever any body contains a non-fake raw-pointer local, checked via
`bodyHasRawPtrLocalV2`). -/
@[reducible] noncomputable def profileV2ProgramGaps (p : Program) :
    List DisclosedGap :=
  if p.bodies.any bodyHasRawPtrLocalV2 then
    [.unbridgedSemantics "mir_profile_v2",
     .callerMemoryThreadIsolation "mir_profile_v2",
     .callerRawPtrAliasing "mir_profile_v2"]
  else
    [.unbridgedSemantics "mir_profile_v2",
     .callerMemoryThreadIsolation "mir_profile_v2"]

/-- Default disclosed gaps for a legacy Profile v2 whole-crate `CrateV2`
verification. -/
@[reducible] noncomputable def legacyCrateGapsV2 (p : Program) :
    List DisclosedGap :=
  profileV2ProgramGaps p ++ legacyCrateGaps

/-- Default disclosed gaps for a legacy Profile v2 selected-unit `CrateV2`
verification. -/
@[reducible] noncomputable def legacyUnitGapsV2 (p : Program) :
    List DisclosedGap :=
  profileV2ProgramGaps p ++ legacyUnitGaps

/-- Wrap a Profile v2 whole-crate `CrateV2` into a
`MirVerificationEnvelope`. -/
@[reducible] noncomputable def legacyCrateEnvelopeV2 (c : CrateV2) :
    MirVerificationEnvelope :=
  mkLegacyEnvelope
    MirProfileV2
    c.program
    c.specs.safety
    c.specs.property
    [.forallSafety]
    (legacyCrateGapsV2 c.program)

/-- Wrap a Profile v2 selected-unit `CrateV2` into a
`MirVerificationEnvelope`. -/
@[reducible] noncomputable def legacyUnitEnvelopeV2 (c : CrateV2) :
    MirVerificationEnvelope :=
  mkLegacyEnvelope
    MirProfileV2
    c.program
    c.specs.safety
    c.specs.property
    [.forallSafety]
    (legacyUnitGapsV2 c.program)

/-- `@[reducible]` Profile v2 whole-crate envelope obligation equivalent to
`Trusted.MirSemantics.CrateTheoremV2`. -/
@[reducible] def CrateEnvelopeTheoremV2 (c : CrateV2) : Prop :=
  c.program.scope = .crate ∧ EnvelopeTheorem (legacyCrateEnvelopeV2 c)

/-- `@[reducible]` Profile v2 selected-unit envelope obligation equivalent to
`Trusted.MirSemantics.UnitTheoremV2`. -/
@[reducible] def UnitEnvelopeTheoremV2 (c : CrateV2) : Prop :=
  c.program.scope = .unit ∧ EnvelopeTheorem (legacyUnitEnvelopeV2 c)

/-- Model-pinned structured Profile v1 Pass-1 root obligation, fixing
`ExecutionModel` to `MirProfileV1` inside `Trusted.*` so neither specification
nor proof modules can substitute a synthetic `ExecutionModel`. -/
@[reducible] def MirEnvelopeTheoremV1
    (program : Program)
    (entries : List MirVerifiedEntry)
    (stubs : List MirAssumedStub)
    (refutations : List MirRefutationEntry)
    (claimShapes : List ClaimShape)
    (gaps : List DisclosedGap) : Prop :=
  EnvelopeTheorem
    (mkEnvelope MirProfileV1 program entries stubs refutations
      claimShapes gaps)

/-- Model-pinned structured Profile v2 Pass-1 root obligation, fixing
`ExecutionModel` to `MirProfileV2` inside `Trusted.*` so neither specification
nor proof modules can substitute a synthetic `ExecutionModel`. -/
@[reducible] def MirEnvelopeTheoremV2
    (program : Program)
    (entries : List MirVerifiedEntry)
    (stubs : List MirAssumedStub)
    (refutations : List MirRefutationEntry)
    (claimShapes : List ClaimShape)
    (gaps : List DisclosedGap) : Prop :=
  EnvelopeTheorem
    (mkEnvelope MirProfileV2 program entries stubs refutations
      claimShapes gaps)

end Trusted.Framework

namespace Trusted

/-- Top-level model-pinned structured Profile v1 envelope obligation alias. -/
abbrev MirEnvelopeTheoremV1 :=
  Trusted.Framework.MirEnvelopeTheoremV1

/-- Top-level model-pinned structured Profile v2 envelope obligation alias. -/
abbrev MirEnvelopeTheoremV2 :=
  Trusted.Framework.MirEnvelopeTheoremV2

/-- Top-level `@[reducible]` whole-crate envelope obligation alias. -/
abbrev CrateEnvelopeTheorem :=
  Trusted.Framework.CrateEnvelopeTheorem

/-- Top-level `@[reducible]` selected-unit envelope obligation alias. -/
abbrev UnitEnvelopeTheorem :=
  Trusted.Framework.UnitEnvelopeTheorem

/-- Top-level `@[reducible]` Profile v2 whole-crate envelope obligation
alias. -/
abbrev CrateEnvelopeTheoremV2 :=
  Trusted.Framework.CrateEnvelopeTheoremV2

/-- Top-level `@[reducible]` Profile v2 selected-unit envelope obligation
alias. -/
abbrev UnitEnvelopeTheoremV2 :=
  Trusted.Framework.UnitEnvelopeTheoremV2

end Trusted

end
