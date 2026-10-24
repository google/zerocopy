import AnnealResearch.PR94AuditCounterexamples

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 1600000

namespace AnnealResearch.Post96Consumer

open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.CargoWorkspaceIntegration
open AnnealResearch.StatefulGenericLibraryH3H7
open AnnealResearch.PR86AuditRepairs
open AnnealResearch.CharonNativeAndControlsR3R4
open AnnealResearch.OpenHashMultiCrateR5R6R9R10

/-- This research interface is semantic data, not a transport format or an addition to Trusted.
    The Python adapter supplies these records from raw inputs. Its capture/transcription fidelity
    remains an explicit producer/adapter premise; the checks below do not prove host OS events. -/
inductive SubjectKind where
  | nominalPair | sliceTailLayout | endorsedPackage | strictCharon | legacyH3
  deriving DecidableEq, Repr

inductive AcquisitionClass where
  | postRunReported | strictCharonTranslation | legacyReviewed
  deriving DecidableEq, Repr

structure SourceClaim where
  reportedPath : String
  reportedByteCount : Nat
  reportedSha256 : String
  deriving DecidableEq, Repr

structure CaptureContext where
  crateName : String
  targetTriple : List Nat
  svh : Option (Nat × Nat)
  sources : List SourceClaim
  deriving DecidableEq, Repr

/-- Complete source keys remain available alongside the bounded old C2 carrier projection.
    In the nominalPair family only non-generic `::[]` entries are supported by the adapter. -/
structure NominalRecord where
  instanceKey : String
  owner : String
  entry : OpenAdtTableEntryC2
  deriving DecidableEq, Repr

structure Envelope where
  schemaVersion : Nat
  kind : SubjectKind
  acquisition : AcquisitionClass
  context : CaptureContext
  companionSha256 : String
  packageSha256 : String
  monoComplete : Bool
  preserveUb : Bool
  ubChecks : Bool
  postRunVerified : Option Bool
  outputWriteSucceeded : Option Bool
  expectedFp16 : Nat × Nat
  packageBytes : List Nat
  nominalRecords : List NominalRecord
  packetLayout : Option QueriedLayoutRecord
  deriving DecidableEq, Repr

/-- These identities are supplied by the outer manifest, not inferred authenticity claims.
    Full digest strings are compared; SHA-256 computation is performed outside Lean. -/
structure ExpectedSubject where
  kind : SubjectKind
  acquisition : AcquisitionClass
  context : CaptureContext
  companionSha256 : String
  packageSha256 : String
  deriving DecidableEq, Repr

def checkIdentity (expected : ExpectedSubject) (e : Envelope) : Bool :=
  (e.schemaVersion == 1) && (e.kind == expected.kind) &&
  (e.acquisition == expected.acquisition) && (e.context == expected.context) &&
  (e.companionSha256 == expected.companionSha256) &&
  (e.packageSha256 == expected.packageSha256)

def checkAcquisitionClaims (e : Envelope) : Bool :=
  match e.acquisition with
  | .postRunReported =>
      (e.postRunVerified == some true) && (e.outputWriteSucceeded == some true)
  | .strictCharonTranslation =>
      (e.kind == .strictCharon) && (e.postRunVerified == none)
  | .legacyReviewed =>
      (e.kind == .legacyH3) && (e.postRunVerified == none)

/-- Crate names in this bounded adapter are ASCII; character codes are exactly UTF-8 bytes.
    This list conversion kernel-reduces on literals in the pinned Lean version, unlike the
    ByteArray.toList path used by String.toUTF8. -/
def asciiCrateBytes (name : String) : List Nat := name.toList.map Char.toNat

def checkAsciiCrateName (name : String) : Bool :=
  !name.toList.isEmpty && (asciiCrateBytes name).all (fun n => Nat.blt n 128)

/-- The D2 package-consistency formula parameterized by actual crate bytes. The previous
    `verifyPostRunEndorsedArtifactHeaderConsistentC2` fixes r5ClientAppCrateNameBytes and its
    record also asserts OS facts. This version consumes only fields present in the raw capture. -/
def checkHeaderConsistency (e : Envelope) : Bool :=
  checkAsciiCrateName e.context.crateName &&
  match parseWirePackage e.packageBytes with
  | .accepted p =>
      (p.defaultPhase == .runtimePostCleanup) &&
      p.monoComplete && (p.monoComplete == e.monoComplete) &&
      p.preserveUb && (p.preserveUb == e.preserveUb) &&
      (p.ubChecks == e.ubChecks) &&
      ((p.fpHi, p.fpLo) == e.expectedFp16) &&
      (computeCargoPayloadFp16 (asciiCrateBytes e.context.crateName)
        (e.packageBytes.drop 10) == e.expectedFp16)
  | _ => false

def checkSubjectSemantics (expected : ExpectedSubject) (e : Envelope) : Bool :=
  let bodies := decodePackageBodies e.packageBytes
  match e.kind with
  | .nominalPair =>
      checkRuntimeClosedBodies bodies &&
      checkNominalPairClientBoundToOpenAdtTableC2 (e.nominalRecords.map (·.entry)) bodies
  | .sliceTailLayout =>
      match e.packetLayout with
      | none => false
      | some d =>
          checkCapturedSliceTailDstLayoutAgainstReprCC2
            expected.context.targetTriple e.context.targetTriple
            [(4, 4), (2, 2)] 4 4 d
  | .endorsedPackage => checkRuntimeClosedBodies bodies
  | .strictCharon => verifyCharonNativeInspectorClosureCompleteC2 e.packageBytes
  | .legacyH3 =>
      -- The retained H3 JSON has neither post-run endorsement nor a u32 layout query.
      -- Do not fabricate either. This family admits the raw graph only and exposes the
      -- reviewed legacy acquisition class. No operational/layout contract follows here.
      e.nominalRecords.isEmpty && e.packetLayout.isNone

def checkEnvelope (expected : ExpectedSubject) (e : Envelope) : Bool :=
  checkIdentity expected e && checkAcquisitionClaims e &&
  isAdmittedPackageBytes e.packageBytes && checkHeaderConsistency e &&
  checkSubjectSemantics expected e

structure AcceptedSubject where
  envelope : Envelope
  bodies : List WireBody
  deriving DecidableEq, Repr

/-- One public consumer path. Companion projections and the interpreted graph originate in
    the same envelope; the caller cannot substitute a separately checked package afterward. -/
def accept (expected : ExpectedSubject) (e : Envelope) : Option AcceptedSubject :=
  bif checkEnvelope expected e then
    some { envelope := e, bodies := decodePackageBodies e.packageBytes }
  else none

theorem checkEnvelope_sound (expected : ExpectedSubject) (e : Envelope)
    (h : checkEnvelope expected e = true) :
    checkIdentity expected e = true ∧ checkAcquisitionClaims e = true ∧
    isAdmittedPackageBytes e.packageBytes = true ∧ checkHeaderConsistency e = true ∧
    checkSubjectSemantics expected e = true := by
  unfold checkEnvelope at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨hi, ha⟩, hp⟩, hh⟩, hs⟩
  exact ⟨hi, ha, hp, hh, hs⟩

theorem accept_sound (expected : ExpectedSubject) (e : Envelope) (accepted : AcceptedSubject)
    (h : accept expected e = some accepted) :
    accepted.envelope = e ∧ accepted.bodies = decodePackageBodies e.packageBytes ∧
    checkIdentity expected e = true ∧ checkAcquisitionClaims e = true ∧
    isAdmittedPackageBytes e.packageBytes = true ∧ checkHeaderConsistency e = true ∧
    checkSubjectSemantics expected e = true := by
  unfold accept at h
  cases hc : checkEnvelope expected e with
  | false => rw [hc] at h; contradiction
  | true =>
      rw [hc] at h
      injection h with hAccepted
      subst accepted
      exact ⟨rfl, rfl, checkEnvelope_sound expected e hc⟩

theorem nominal_acceptance_uses_consumed_table (expected : ExpectedSubject) (e : Envelope)
    (hKind : e.kind = .nominalPair) (h : checkEnvelope expected e = true) :
    checkNominalPairClientBoundToOpenAdtTableC2 (e.nominalRecords.map (·.entry))
      (decodePackageBodies e.packageBytes) = true := by
  have hs := (checkEnvelope_sound expected e h).2.2.2.2
  unfold checkSubjectSemantics at hs
  rw [hKind] at hs
  simp only [Bool.and_eq_true] at hs
  exact hs.2

theorem charon_acceptance_uses_complete_gate (expected : ExpectedSubject) (e : Envelope)
    (hKind : e.kind = .strictCharon) (h : checkEnvelope expected e = true) :
    verifyCharonNativeInspectorClosureCompleteC2 e.packageBytes = true := by
  have hs := (checkEnvelope_sound expected e h).2.2.2.2
  simpa only [checkSubjectSemantics, hKind] using hs

#print axioms accept_sound
#print axioms nominal_acceptance_uses_consumed_table
#print axioms charon_acceptance_uses_complete_gate

end AnnealResearch.Post96Consumer
