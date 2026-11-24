/-
  Self-contained kernel-checked Lean 4 mechanization of the Profile-Parametric
  Verification Envelope ("Thin Claim-Boundary Spine") accompanying
  `epistemology-and-defense-in-depth-soundness-for-ai-accelerated-semantics`.

  Depends strictly on `Init` (`0` `sorryAx`, `0` `Classical.choice`, `0` custom axioms).
-/

namespace VerificationEnvelopeSpec

/-- Uniform terminal outcome across value-only, memory-aware, and machine-level profiles. -/
inductive TerminalOutcome (Ret Mem : Type) where
  | returned (ret : Ret) (mem : Mem)
  | unwound  (mem : Mem)
  | aborted  (mem : Mem)

/-- Closed claim-shape vocabulary distinguishing universal safety, termination,
    existential UB refutation, and 2-trace relational hyperproperties. -/
inductive ClaimShape where
  | forallSafety
  | termination
  | refutationUB
  | hyper2Safety
  deriving DecidableEq, Repr

/-- Reference-oracle correspondence grade licensing downstream claim shapes. -/
inductive OracleGrade where
  | unbridged (profileId : String)
  | forwardSim (oracleId : String)
  | biFaultEquiv (oracleId : String)
  deriving DecidableEq, Repr

/-- Upper-triangular transfer license:
    - `forwardSim` (an over-approximating model where reference UB implies model fault)
      licenses universal safety and termination, NEVER existential `refutationUB`
      (because a stricter-than-reference check can fault spuriously on valid programs).
    - `biFaultEquiv` (bidirectional `.undefined <-> .ub` equivalence) additionally
      licenses `refutationUB`.
    - `unbridged` licenses safety/termination ONLY when accompanied by an explicit
      `.unbridgedSemantics` disclosure in the envelope's gap ledger. -/
def OracleGrade.licenses : OracleGrade → ClaimShape → Bool
  | .unbridged _,    .forallSafety => true
  | .unbridged _,    .termination  => true
  | .unbridged _,    _             => false
  | .forwardSim _,   .forallSafety => true
  | .forwardSim _,   .termination  => true
  | .forwardSim _,   _             => false
  | .biFaultEquiv _, .forallSafety => true
  | .biFaultEquiv _, .termination  => true
  | .biFaultEquiv _, .refutationUB => true
  | .biFaultEquiv _, .hyper2Safety => false

/-- Machine-extracted assumption and scope-gap ledger carried on the root obligation. -/
inductive DisclosedGap where
  | unbridgedSemantics (profileId : String)
  | callerRawPtrAliasing (profileId : String)
  | assumedExternalCallee (identity : String)
  | waivedInhabitation (identity : String)
  | selectedUnitScope
  | unverifiedDownstream (stage : String)
  deriving DecidableEq, Repr

/-- Profile-parametric operational model plugging directly into concrete semantics
    without wrapping inner small-step execution transitions. -/
structure ExecutionModel (Prog Body Sig Query Ret Mem : Type) where
  profileId        : String
  oracleGrade      : OracleGrade
  programAdmitted  : Prog → Bool
  bodiesOf         : Prog → List Body
  uniqueIdentities : Prog → Bool
  bodyIdentity     : Body → String
  bodyIsUnsafe     : Body → Bool
  bodyMatchesSig   : Body → Sig → Bool
  requiredGaps     : Body → List DisclosedGap
  entryDom         : Body → Query → Prop
  returnValid      : Body → Ret → Mem → Prop
  execForBody      : Prog → String → Prog
  wellFormed       : Prog → Query → Prop
  produces         : Prog → Query → TerminalOutcome Ret Mem → Prop
  diverges         : Prog → Query → Prop
  faultsUB         : Prog → Query → Prop

/-- Constructive parameter-domain non-vacuity:
    Either a valid entry `q` satisfies `pre q`, OR `entryDom` is uninhabited (e.g. `!`).
    Avoids `Classical.choice` while rejecting contradictory `requires(x > 10 ∧ x < 5)`. -/
def NonVacuousEntry {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem) (body : Body) (pre : Query → Prop) : Prop :=
  (∃ q : Query, M.entryDom body q ∧ pre q) ∨ (∀ q : Query, ¬ M.entryDom body q)

/-- Explicit 3-bit positive-polarity effect mask with zero implicit field defaults. -/
structure EffectMask where
  terminates : Bool
  noUnwind   : Bool
  noAbort    : Bool
  deriving DecidableEq, Repr

/-- Unified function contract parameterized over `Query`, `Ret`, and `Mem`,
    serving both value-only and caller-memory-aware MIR profiles without duplication. -/
structure FnContract (Query Ret Mem : Type) where
  safetyPre   : Query → Prop := fun _ => True
  behaviorPre : Query → Prop := fun _ => True
  postReturn  : Query → Ret → Mem → Prop := fun _ _ _ => True
  postUnwind  : Query → Mem → Prop := fun _ _ => True
  postAbort   : Query → Mem → Prop := fun _ _ => True
  effects     : EffectMask

/-- Safe functions structurally ignore `safetyPre`: caller safety preconditions
    only take effect when `isUnsafe = true`. -/
def FnContract.effectiveSafetyPre {Q R M : Type}
    (c : FnContract Q R M) (isUnsafe : Bool) (q : Q) : Prop :=
  isUnsafe = true → c.safetyPre q

def FnContract.effectiveBehaviorPre {Q R M : Type}
    (c : FnContract Q R M) (isUnsafe : Bool) (q : Q) : Prop :=
  c.effectiveSafetyPre isUnsafe q ∧ c.behaviorPre q

/-- External callee stub summary guarded by `StubRealizable` so an inconsistent
    callee postcondition (`postReturn := False` with `terminates = true`) cannot prove `False`. -/
structure AssumedStub (Sig Query Ret Mem : Type) where
  identity : String
  sig      : Sig
  contract : FnContract Query Ret Mem

def StubRealizable {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem)
    (body : Body) (c : FnContract Query Ret Mem) : Prop :=
  ∀ q : Query, M.entryDom body q → c.effectiveBehaviorPre (M.bodyIsUnsafe body) q →
    (c.effects.terminates = false) ∨
    (∃ r m, M.returnValid body r m ∧ c.postReturn q r m) ∨
    (c.effects.noUnwind = false ∧ ∃ m, c.postUnwind q m) ∨
    (c.effects.noAbort = false ∧ ∃ m, c.postAbort q m)

structure VerifiedEntry (Sig Query Ret Mem : Type) where
  identity         : String
  sig              : Sig
  contract         : FnContract Query Ret Mem
  requireInhabited : Bool := true

/-- Constructor-gated verification envelope (`private mk ::`) ensuring untrusted proof
    modules must construct obligations through audited constructors. -/
structure VerificationEnvelope (Prog Body Sig Query Ret Mem : Type) where
  private mk ::
  model       : ExecutionModel Prog Body Sig Query Ret Mem
  program     : Prog
  entries     : List (VerifiedEntry Sig Query Ret Mem)
  stubs       : List (AssumedStub Sig Query Ret Mem)
  claimShapes : List ClaimShape
  gaps        : List DisclosedGap

def mkEnvelope {Prog Body Sig Query Ret Mem : Type}
    (model : ExecutionModel Prog Body Sig Query Ret Mem)
    (program : Prog)
    (entries : List (VerifiedEntry Sig Query Ret Mem))
    (stubs : List (AssumedStub Sig Query Ret Mem))
    (claimShapes : List ClaimShape)
    (gaps : List DisclosedGap) : VerificationEnvelope Prog Body Sig Query Ret Mem :=
  { model, program, entries, stubs, claimShapes, gaps }

def BodySatisfiesEntry {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem)
    (prog : Prog) (gaps : List DisclosedGap)
    (body : Body) (e : VerifiedEntry Sig Query Ret Mem) : Prop :=
  let ep := M.execForBody prog e.identity
  let isU := M.bodyIsUnsafe body
  M.bodyIdentity body = e.identity ∧
  M.bodyMatchesSig body e.sig = true ∧
  (∀ g, g ∈ M.requiredGaps body → g ∈ gaps) ∧
  (∀ q, M.entryDom body q → e.contract.effectiveSafetyPre isU q → M.wellFormed ep q) ∧
  (∀ q, M.entryDom body q → e.contract.effectiveBehaviorPre isU q →
    (e.contract.effects.terminates = true → ¬ M.diverges ep q) ∧
    (∀ r m, M.produces ep q (.returned r m) → e.contract.postReturn q r m) ∧
    (∀ m, M.produces ep q (.unwound m) →
      e.contract.effects.noUnwind = false ∧ e.contract.postUnwind q m) ∧
    (∀ m, M.produces ep q (.aborted m) →
      e.contract.effects.noAbort = false ∧ e.contract.postAbort q m)) ∧
  ((e.requireInhabited = true ∧
      NonVacuousEntry M body (e.contract.effectiveBehaviorPre isU)) ∨
    (e.requireInhabited = false ∧ .waivedInhabitation e.identity ∈ gaps))

def EnvelopeGradeDisclosed (grade : OracleGrade) (gaps : List DisclosedGap) : Prop :=
  match grade with
  | .unbridged pid => .unbridgedSemantics pid ∈ gaps
  | .forwardSim _  => True
  | .biFaultEquiv _ => True

/-- Root kernel obligation enforcing complete body accounting, constructive non-vacuity,
    stub realizability, unbridged-profile disclosure, and claim-shape licensing. -/
def EnvelopeTheorem {Prog Body Sig Query Ret Mem : Type}
    (env : VerificationEnvelope Prog Body Sig Query Ret Mem) : Prop :=
  let M := env.model
  M.programAdmitted env.program = true ∧
  M.uniqueIdentities env.program = true ∧
  EnvelopeGradeDisclosed M.oracleGrade env.gaps ∧
  (∀ cs, cs ∈ env.claimShapes → M.oracleGrade.licenses cs = true) ∧
  (∀ e, e ∈ env.entries → e.contract.effects.terminates = true →
    ClaimShape.termination ∈ env.claimShapes) ∧
  (∀ body, body ∈ M.bodiesOf env.program →
    (∃ e, e ∈ env.entries ∧ BodySatisfiesEntry M env.program env.gaps body e) ∨
    (∃ s, s ∈ env.stubs ∧
      M.bodyIdentity body = s.identity ∧
      M.bodyMatchesSig body s.sig = true ∧
      .assumedExternalCallee s.identity ∈ env.gaps ∧
      StubRealizable M body s.contract))

/-! ### Key Structural Soundness Theorems (`0` axioms) -/

/-- Forward simulation alone NEVER licenses existential UB refutation claims (`refutationUB`),
    preventing stricter-than-reference checks from certifying false UB witnesses. -/
theorem forwardSim_rejects_refutationUB (oid : String) :
    (OracleGrade.forwardSim oid).licenses .refutationUB = false :=
  rfl

/-- Bidirectional fault equivalence (`biFaultEquiv`) licenses `refutationUB`. -/
theorem biFaultEquiv_licenses_refutationUB (oid : String) :
    (OracleGrade.biFaultEquiv oid).licenses .refutationUB = true :=
  rfl

/-- Safe functions structurally ignore `safetyPre`: even `safetyPre := False` reduces to
    `True` when `isUnsafe = false`, blocking vacuous safety preconditions on safe APIs. -/
theorem safe_fn_ignores_false_safetyPre {Q R M : Type} (c : FnContract Q R M) (q : Q) :
    c.effectiveSafetyPre false q := by
  intro h
  cases h

/-- Functions taking uninhabited parameter domains (such as `Infallible` / `!`) satisfy
    `NonVacuousEntry` constructively without waivers or `Classical.choice`. -/
theorem uninhabited_domain_nonVacuous {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem) (body : Body) (pre : Query → Prop)
    (hEmpty : ∀ q : Query, ¬ M.entryDom body q) :
    NonVacuousEntry M body pre :=
  Or.inr hEmpty

/-- Any unbridged profile (`OracleGrade.unbridged pid`) cannot satisfy `EnvelopeTheorem`
    unless `DisclosedGap.unbridgedSemantics pid` is explicitly present in `env.gaps`. -/
theorem unbridged_envelope_requires_gap {Prog Body Sig Query Ret Mem : Type}
    (env : VerificationEnvelope Prog Body Sig Query Ret Mem) (pid : String)
    (hGrade : env.model.oracleGrade = .unbridged pid)
    (hThm : EnvelopeTheorem env) :
    DisclosedGap.unbridgedSemantics pid ∈ env.gaps := by
  rcases hThm with ⟨_, _, hDisc, _⟩
  rw [hGrade] at hDisc
  exact hDisc

end VerificationEnvelopeSpec
