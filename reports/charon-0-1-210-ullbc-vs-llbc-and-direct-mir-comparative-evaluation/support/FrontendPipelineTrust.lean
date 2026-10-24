import Std
import AnnealResearch.Execution

set_option Elab.async false

/-!
Wave A mechanized model for FE-01 ("Comparable subjects, claims, and trust
boundaries") and FE-02 ("Information and transformations before replacement")
from live Issue #45 (`<!-- anneal-frontend-evaluation-program-2026-10-16 -->`).

Memory discipline for the Linux `x86_64` `-M768` envelope:
- `set_option Elab.async false`
- Imports only `Std` and `AnnealResearch.Execution`
- Zero `deriving Repr` and zero `deriving DecidableEq`
- Value definitions marked `noncomputable def` to skip LCNF compilation
-/

namespace AnnealResearch.FrontendPipelineTrust

/-- Five-arrow obligation chain from configured compiler subject to executable endpoint:
    `ConfiguredSubject -> CapturedData -> EncodedBytes -> ParsedLeanRep ->
     OperationalMeaningAndProperty -> ExecutableEndpoint`. -/
structure ArrowChainCert where
  captureFidelity : Bool
  wireDecodeSound : Bool
  structuralAdmissionValid : Bool
  operationalAdequacyAndNoUB : Bool
  executableBindingJustified : Bool

noncomputable def allFiveArrowsHold (c : ArrowChainCert) : Bool :=
  c.captureFidelity &&
  c.wireDecodeSound &&
  c.structuralAdmissionValid &&
  c.operationalAdequacyAndNoUB &&
  c.executableBindingJustified

/-- Three-aspect specimen descriptor (`call_write_and_cleanup`) tracking:
    1. `calleeId`: resolved implementation/call target,
    2. `writtenLoc`, `writtenVal`: memory write footprint,
    3. `unwindsOnErr`, `scalarReturn`, `hasIntermediateFault`: normal/unwind exit and intermediate safety. -/
structure ProbeSpec where
  calleeId : Nat
  writtenLoc : Nat
  writtenVal : Nat
  unwindsOnErr : Bool
  scalarReturn : Nat
  hasIntermediateFault : Bool

abbrev ProbeState : Type := Nat

def initProbeState : ProbeState := 0
def normalExitState : ProbeState := 1
def unwindExitState : ProbeState := 2
def faultState : ProbeState := 3

def probeStep (p : ProbeSpec) (s t : ProbeState) : Prop :=
  (s = initProbeState ∧ p.hasIntermediateFault = true ∧ t = faultState) ∨
  (s = initProbeState ∧ p.unwindsOnErr = false ∧ t = normalExitState) ∨
  (s = initProbeState ∧ p.unwindsOnErr = true ∧ t = unwindExitState)

def probeBad (s : ProbeState) : Prop :=
  s = faultState

/-- Operational system `(Step, Bad)` for a `ProbeSpec`, connecting directly to
    `AnnealResearch.Execution.NoUB`. -/
def probeSys (p : ProbeSpec) : (ProbeState → ProbeState → Prop) × (ProbeState → Prop) :=
  (probeStep p, probeBad)

def subjectExecutionSys (p : ProbeSpec) : (ProbeState → ProbeState → Prop) × (ProbeState → Prop) :=
  probeSys p

/-- Complete frontend claim requiring all-prefix UB freedom (`Execution.NoUB`) and
    exact preservation of call target, memory footprint, unwind behavior, and scalar return. -/
def FullFrontendClaim (p : ProbeSpec)
    (expectedCallee expectedLoc expectedVal expectedRet : Nat)
    (expectedUnwind : Bool) : Prop :=
  Execution.NoUB (probeSys p).1 (probeSys p).2 initProbeState ∧
  p.calleeId = expectedCallee ∧
  p.writtenLoc = expectedLoc ∧
  p.writtenVal = expectedVal ∧
  p.unwindsOnErr = expectedUnwind ∧
  p.scalarReturn = expectedRet

theorem noUB_of_no_intermediate_fault (p : ProbeSpec)
    (hfault : p.hasIntermediateFault = false) :
    Execution.NoUB (probeSys p).1 (probeSys p).2 initProbeState := by
  apply Execution.invariant_noUB (Invariant := fun s => s ≠ faultState)
  · intro h; cases h
  · intro s t _ hstep
    rcases hstep with ⟨_, hbad, _⟩ | ⟨_, _, ht⟩ | ⟨_, _, ht⟩
    · cases (Eq.trans (Eq.symm hfault) hbad)
    · subst ht; intro h; cases h
    · subst ht; intro h; cases h
  · intro s hinv hbad
    exact hinv hbad

/-- Semantic bridge hypotheses corresponding to the five pipeline arrows. -/
def FiveArrowBridge (c : ArrowChainCert)
    (configuredSubject capturedData parsedRep admittedModel : ProbeSpec) : Prop :=
  (c.captureFidelity = true → capturedData = configuredSubject) ∧
  (c.wireDecodeSound = true → parsedRep = capturedData) ∧
  (c.structuralAdmissionValid = true → admittedModel = parsedRep) ∧
  (c.operationalAdequacyAndNoUB = true → admittedModel.hasIntermediateFault = false) ∧
  (c.executableBindingJustified = true → configuredSubject.scalarReturn = admittedModel.scalarReturn)

/-- 1. When all five arrows of the frontend chain hold and the admitted model satisfies
    the expected behavior, the configured subject satisfies `Execution.NoUB` and `FullFrontendClaim`. -/
theorem complete_five_arrow_chain_transfers_claim
    (c : ArrowChainCert)
    (configuredSubject capturedData parsedRep admittedModel : ProbeSpec)
    (expectedCallee expectedLoc expectedVal expectedRet : Nat)
    (expectedUnwind : Bool)
    (hc : c.captureFidelity = true ∧ c.wireDecodeSound = true ∧
          c.structuralAdmissionValid = true ∧ c.operationalAdequacyAndNoUB = true ∧
          c.executableBindingJustified = true)
    (hbridge : FiveArrowBridge c configuredSubject capturedData parsedRep admittedModel)
    (hmodel : admittedModel.calleeId = expectedCallee ∧
              admittedModel.writtenLoc = expectedLoc ∧
              admittedModel.writtenVal = expectedVal ∧
              admittedModel.unwindsOnErr = expectedUnwind ∧
              admittedModel.scalarReturn = expectedRet) :
    configuredSubject = admittedModel ∧
    Execution.NoUB (subjectExecutionSys configuredSubject).1
      (subjectExecutionSys configuredSubject).2 initProbeState ∧
    FullFrontendClaim configuredSubject
      expectedCallee expectedLoc expectedVal expectedRet expectedUnwind := by
  rcases hc with ⟨hc1, hc2, hc3, hc4, _⟩
  rcases hbridge with ⟨hb1, hb2, hb3, hb4, _⟩
  have hcap : capturedData = configuredSubject := hb1 hc1
  have hparse : parsedRep = capturedData := hb2 hc2
  have hadm : admittedModel = parsedRep := hb3 hc3
  have heq : configuredSubject = admittedModel :=
    Eq.trans (Eq.symm hcap) (Eq.trans (Eq.symm hparse) (Eq.symm hadm))
  have hsafeModel : Execution.NoUB (probeSys admittedModel).1 (probeSys admittedModel).2 initProbeState :=
    noUB_of_no_intermediate_fault admittedModel (hb4 hc4)
  subst heq
  exact ⟨rfl, hsafeModel, ⟨hsafeModel, hmodel.1, hmodel.2.1, hmodel.2.2.1, hmodel.2.2.2.1, hmodel.2.2.2.2⟩⟩

/-- Canonical positive three-aspect specimen (`call_write_and_cleanup`). -/
noncomputable def intendedProbe : ProbeSpec :=
  { calleeId := 1
    writtenLoc := 1
    writtenVal := 42
    unwindsOnErr := true
    scalarReturn := 7
    hasIntermediateFault := false }

noncomputable def mirPostCleanupTrace (p : ProbeSpec) : ProbeSpec := p
noncomputable def ullbcRetainedTrace (p : ProbeSpec) : ProbeSpec := p

/-- 2. Faithful `mirPostCleanupTrace` and faithful `ullbcRetainedTrace` preserve all
    three aspects (call target, memory write footprint, normal/unwind exit) and `Execution.NoUB`. -/
theorem positive_probe_preserved_across_faithful_routes :
    FullFrontendClaim (mirPostCleanupTrace intendedProbe) 1 1 42 7 true ∧
    FullFrontendClaim (ullbcRetainedTrace intendedProbe) 1 1 42 7 true ∧
    Execution.NoUB (probeSys intendedProbe).1 (probeSys intendedProbe).2 initProbeState := by
  have hsafe : Execution.NoUB (probeSys intendedProbe).1 (probeSys intendedProbe).2 initProbeState :=
    noUB_of_no_intermediate_fault intendedProbe rfl
  exact ⟨⟨hsafe, rfl, rfl, rfl, rfl, rfl⟩, ⟨hsafe, rfl, rfl, rfl, rfl, rfl⟩, hsafe⟩

/-- Pinned compiler identity `(commitHash, targetTriple)`. -/
structure CompilerPin where
  commitHash : Nat
  targetTriple : Nat

inductive PinComparisonClass where
  | matchedDirectComparison
  | requiresSeparateCompatibilityBridge

noncomputable def MatchedComparisonAdmissible (pinA pinB : CompilerPin) : Bool :=
  (pinA.commitHash == pinB.commitHash) && (pinA.targetTriple == pinB.targetTriple)

noncomputable def classifyPinComparison (pinA pinB : CompilerPin) : PinComparisonClass :=
  if MatchedComparisonAdmissible pinA pinB then
    .matchedDirectComparison
  else
    .requiresSeparateCompatibilityBridge

/-- Pinned extraction compiler for the `google/zerocopy` PR #3882 prototype (`nightly-2026-09-17`). -/
noncomputable def charonNightly20260917 : CompilerPin :=
  { commitHash := 20260917, targetTriple := 1 }

/-- Pinned compiler for `joshlf/anneal` MIR captures (`rustc 1.99.0 (b940084d7 2026-09-28)`). -/
noncomputable def annealRustc1990_20260928 : CompilerPin :=
  { commitHash := 20260928, targetTriple := 1 }

/-- 3. Comparing `charonNightly20260917` with `annealRustc1990_20260928` returns
    `MatchedComparisonAdmissible = false` and classifies as `.requiresSeparateCompatibilityBridge`. -/
theorem compiler_pin_compatibility_gate :
    MatchedComparisonAdmissible charonNightly20260917 annealRustc1990_20260928 = false ∧
    classifyPinComparison charonNightly20260917 annealRustc1990_20260928 =
      .requiresSeparateCompatibilityBridge ∧
    MatchedComparisonAdmissible annealRustc1990_20260928 annealRustc1990_20260928 = true ∧
    classifyPinComparison annealRustc1990_20260928 annealRustc1990_20260928 =
      .matchedDirectComparison :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Proof-carrying layout record requiring positive alignment and size divisible by alignment,
    without any Lean `axiom` declaration. -/
structure LayoutCert where
  size : Nat
  align : Nat
  alignPos : 0 < align
  sizeAligned : size % align = 0

noncomputable def u32Layout : LayoutCert :=
  { size := 4, align := 4, alignPos := Nat.zero_lt_succ 3, sizeAligned := rfl }

noncomputable def u8PairLayout : LayoutCert :=
  { size := 2, align := 1, alignPos := Nat.zero_lt_succ 0, sizeAligned := rfl }

def TypeLayoutCorrespondence (rustTypeId expectedSize expectedAlign : Nat)
    (cert : LayoutCert) : Prop :=
  rustTypeId = rustTypeId ∧ cert.size = expectedSize ∧ cert.align = expectedAlign

/-- 4. Both `u32Layout` (`4, 4`) and `u8PairLayout` (`2, 1`) inhabit `LayoutCert` without
    axioms, proving that a well-formed layout record without `TypeLayoutCorrespondence`
    does not determine a Rust type's layout. -/
theorem layout_record_without_type_bridge_insufficient :
    0 < u32Layout.align ∧
    u32Layout.size % u32Layout.align = 0 ∧
    0 < u8PairLayout.align ∧
    u8PairLayout.size % u8PairLayout.align = 0 ∧
    u32Layout.size ≠ u8PairLayout.size ∧
    TypeLayoutCorrespondence 1 4 4 u32Layout ∧
    ¬ TypeLayoutCorrespondence 1 4 4 u8PairLayout := by
  refine ⟨u32Layout.alignPos, u32Layout.sizeAligned, u8PairLayout.alignPos, u8PairLayout.sizeAligned, ?_, ⟨rfl, rfl, rfl⟩, ?_⟩
  · intro h; cases h
  · intro h; cases h.2.1

noncomputable def faithfulParser (encoded : ProbeSpec) : ProbeSpec := encoded

noncomputable def wrongExportedBody : ProbeSpec :=
  { intendedProbe with calleeId := 2 }

/-- 5. Even when `wireDecodeSound = true` (`faithfulParser w = w` for all wire payloads),
    if `captureFidelity = false` (the exporter emitted `wrongExportedBody`), the parsed
    representation fails `FullFrontendClaim` for `intendedProbe`. -/
theorem proved_parser_without_exporter_fidelity_insufficient :
    let cert : ArrowChainCert :=
      { captureFidelity := false
        wireDecodeSound := true
        structuralAdmissionValid := true
        operationalAdequacyAndNoUB := true
        executableBindingJustified := true }
    allFiveArrowsHold cert = false ∧
    (∀ w, faithfulParser w = w) ∧
    (faithfulParser wrongExportedBody).calleeId ≠ intendedProbe.calleeId ∧
    ¬ FullFrontendClaim (faithfulParser wrongExportedBody) 1 1 42 7 true := by
  refine ⟨rfl, fun _ => rfl, ?_, ?_⟩
  · intro h; cases h
  · intro h; cases h.2.1

def DropSlotProvenEmpty (slotHasNontrivialDropEffect : Bool) : Prop :=
  slotHasNontrivialDropEffect = false

def UnwindUnreachable (unwindsOnErr : Bool) : Prop :=
  unwindsOnErr = false

noncomputable def probeWithDropAndUnwind
    (slotHasNontrivialDropEffect unwindsOnErr : Bool) : ProbeSpec :=
  { calleeId := 1
    writtenLoc := 1
    writtenVal := 42
    unwindsOnErr := unwindsOnErr
    scalarReturn := 7
    hasIntermediateFault := slotHasNontrivialDropEffect }

noncomputable def eraseDropAndUnwind (p : ProbeSpec) : ProbeSpec :=
  { p with unwindsOnErr := false, hasIntermediateFault := false }

/-- 6. Erasing a conditional drop and unwind edge preserves `FullFrontendClaim` (with
    `expectedUnwind = false`) on `probeWithDropAndUnwind` if and only if both
    `DropSlotProvenEmpty` and `UnwindUnreachable` hold. -/
theorem transformation_contract_necessary_for_erased_pass
    (slotHasNontrivialDropEffect unwindsOnErr : Bool) :
    FullFrontendClaim (probeWithDropAndUnwind slotHasNontrivialDropEffect unwindsOnErr) 1 1 42 7 false ↔
    (DropSlotProvenEmpty slotHasNontrivialDropEffect ∧ UnwindUnreachable unwindsOnErr) := by
  constructor
  · intro hclaim
    rcases hclaim with ⟨hnoub, _, _, _, hunwind, _⟩
    refine ⟨?_, hunwind⟩
    cases slotHasNontrivialDropEffect with
    | false => rfl
    | true =>
      exfalso
      apply hnoub faultState
      · exact Execution.Reach.tail (Execution.Reach.refl initProbeState) (Or.inl ⟨rfl, rfl, rfl⟩)
      · rfl
  · rintro ⟨hdrop, hunwind⟩
    have hsafe : Execution.NoUB
        (probeSys (probeWithDropAndUnwind slotHasNontrivialDropEffect unwindsOnErr)).1
        (probeSys (probeWithDropAndUnwind slotHasNontrivialDropEffect unwindsOnErr)).2
        initProbeState :=
      noUB_of_no_intermediate_fault _ hdrop
    exact ⟨hsafe, rfl, rfl, rfl, hunwind, rfl⟩

#print axioms AnnealResearch.FrontendPipelineTrust.complete_five_arrow_chain_transfers_claim
#print axioms AnnealResearch.FrontendPipelineTrust.positive_probe_preserved_across_faithful_routes
#print axioms AnnealResearch.FrontendPipelineTrust.compiler_pin_compatibility_gate
#print axioms AnnealResearch.FrontendPipelineTrust.layout_record_without_type_bridge_insufficient
#print axioms AnnealResearch.FrontendPipelineTrust.proved_parser_without_exporter_fidelity_insufficient
#print axioms AnnealResearch.FrontendPipelineTrust.transformation_contract_necessary_for_erased_pass

end AnnealResearch.FrontendPipelineTrust
