import AnnealResearch.Execution

set_option Elab.async false

/-!
Ordinary-Rust integration binding and essential-vs-incidental partition for `R-ADEV-06`
(live `#32` `R-ADEV-06`, motivating live `#1` Section 21 `A-ADEV-07`, `E-ADEV-05`,
and `E-ADEV-06`), grounded in `experiments/configured-admission` (`probe.rs` `3ada61...`,
`check-results.json` `1ab5d8...`) and `experiments/cleanup-binding` (`cleanup.rs`
`982e10...`, `results.json` `fb6716...`).
-/

namespace AnnealResearch.IntegrationBinding

instance instDecidableEqProd {α β : Type} [DecidableEq α] [DecidableEq β] :
    DecidableEq (α × β) :=
  fun p q => decidable_of_iff (p.1 = q.1 ∧ p.2 = q.2)
    ⟨fun ⟨h1, h2⟩ => Prod.ext h1 h2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

/-- `(sourceHash, expandedInputHash, cfgFlags, targetTriple, ownerSymbol, resolvedCalleeInstance, constGenericArg, evaluatedConstChecksPassed)`. -/
abbrev EssentialBinding : Type :=
  Nat × Nat × Nat × Nat × Nat × Nat × Nat × Bool

/-- `(defPathDisambiguatorSalt, mirTempNumberingEpoch, spanLineOffset, uninstantiatedGenericMention)`. -/
abbrev IncidentalAdapterMetadata : Type :=
  Nat × Nat × Nat × Nat

/-- `(phase, producerExitZero, artifactPresent, artifactBytes, artifactDigest, essential, incidental)`. -/
abbrev CaptureArtifact : Type :=
  Nat × Bool × Bool × Nat × Nat × EssentialBinding × IncidentalAdapterMetadata

/-- `(boundSubject, incidentalBaseline, claimedReturn)`. -/
abbrev VerifiedClaimCert : Type :=
  EssentialBinding × IncidentalAdapterMetadata × Nat

/-- Sound admission requires producer exit `0`, physical artifact presence, passed
required const checks, and exact equality of all essential semantic bindings. -/
noncomputable def AdmissibleBinding (cert : VerifiedClaimCert) (art : CaptureArtifact) : Bool :=
  art.2.1 &&
  art.2.2.1 &&
  art.2.2.2.2.2.1.2.2.2.2.2.2.2 &&
  decide (art.2.2.2.2.2.1 = cert.1)

/-- Partition an observed capture relative to `cert` into:
`0 = validReused`, `1 = incidentalAdapterRefreshOnly`, `2 = rejectedProducerFailure`,
`3 = rejectedStaleSourceOrExpansion`, `4 = rejectedStaleCfgOrInstance`. -/
noncomputable def classifyIntegrationChange (cert : VerifiedClaimCert) (art : CaptureArtifact) : Nat :=
  if AdmissibleBinding cert art then
    if decide (art.2.2.2.2.2.2 = cert.2.1) then 0 else 1
  else if !(art.2.1 && art.2.2.1 && art.2.2.2.2.2.1.2.2.2.2.2.2.2) then 2
  else if !(decide (art.2.2.2.2.2.1.1 = cert.1.1) &&
            decide (art.2.2.2.2.2.1.2.1 = cert.1.2.1)) then 3
  else 4

/-- `observations/a1-mir/probe.mir` (`1,846` B, `1419d6...`): `--cfg probe_case="a1"`, exit `0`. -/
noncomputable def captureA0Mir : CaptureArtifact :=
  (0, true, true, 1846, 0, (0, 0, 0, 0, 0, 0, 1, true), (1, 1, 0, 0))

/-- `observations/a1-llvm-ir/probe.ll` (`2,145` B, `6e8a72...`): `--cfg probe_case="a1"`, exit `0`. -/
noncomputable def captureA0Llvm : CaptureArtifact :=
  (1, true, true, 2145, 1, (0, 0, 0, 0, 0, 0, 1, true), (1, 1, 0, 0))

/-- Counterfactual `--cfg probe_case="a1" --cfg alt_impl` MIR capture at fixed `N = 1`. -/
noncomputable def captureA1Mir : CaptureArtifact :=
  (0, true, true, 1846, 9, (0, 0, 1, 0, 0, 1, 1, true), (1, 1, 0, 0))

/-- `observations/b0-mir/probe.mir` (`1,846` B, `b8f503...`): `--cfg probe_case="b0"`, exit `0`. -/
noncomputable def captureB0Mir : CaptureArtifact :=
  (0, true, true, 1846, 2, (0, 0, 2, 0, 0, 2, 0, true), (1, 1, 0, 0))

/-- `observations/b1-mir/probe.mir` (`1,846` B, `f01001...`): exit `1` (`E0080`), file present. -/
noncomputable def captureB1Mir : CaptureArtifact :=
  (0, false, true, 1846, 4, (0, 0, 3, 0, 0, 3, 1, false), (1, 1, 0, 0))

/-- `observations/unused_b1-mir/probe.mir` (`2,083` B, `5ed88e...`): uninstantiated `never_instantiated<U>()`. -/
noncomputable def obsUnusedB1Mir : CaptureArtifact :=
  (0, true, true, 2083, 6, (0, 0, 4, 0, 0, 2, 0, true), (1, 1, 0, 1))

/-- Counterfactual stale `include!`/build-script expansion under unchanged `probe.rs` source hash. -/
noncomputable def captureMacroStaleMir : CaptureArtifact :=
  (0, true, true, 1846, 9, (0, 2, 0, 0, 0, 5, 1, true), (1, 1, 0, 0))

/-- Verified claim certificate for baseline `A0` (`captureA0Mir` / `captureA0Llvm`, claiming `0xA1`). -/
noncomputable def certA0 : VerifiedClaimCert :=
  ((0, 0, 0, 0, 0, 0, 1, true), (1, 1, 0, 0), 0xA1)

/-- Operational step relation for `AnnealResearch.Execution.NoUB` and `Execution.Verified`.
States `(tag, returnVal)`: `(0, 0)` init, `(1, val)` returned, `(2, 0)` const-check UB,
`(3, 0)` unverified producer fault. -/
def runSelectedCallee (art : CaptureArtifact) (before after : Nat × Nat) : Prop :=
  before = (0, 0) ∧
  after =
    if !art.2.2.2.2.2.1.2.2.2.2.2.2.2 then (2, 0)
    else if !art.2.1 || !art.2.2.1 then (3, 0)
    else if art.2.2.2.2.2.1.2.2.2.2.2.1 = 0 then (1, 0xA1)
    else if art.2.2.2.2.2.1.2.2.2.2.2.1 = 1 then (1, 0xA2)
    else if art.2.2.2.2.2.1.2.2.2.2.2.1 = 2 then (1, 0xB0)
    else if art.2.2.2.2.2.1.2.2.2.2.2.1 = 4 then (1, 42)
    else (3, 0)

/-- Theorem 1: Exact characterization of `AdmissibleBinding` and its equivalence to
`classifyIntegrationChange` returning `0` (`validReused`) or `1` (`incidentalAdapterRefreshOnly`). -/
theorem admissible_iff_reused_or_incidental_refresh
    (cert : VerifiedClaimCert) (art : CaptureArtifact) :
    (AdmissibleBinding cert art = true ↔
      (art.2.1 = true ∧ art.2.2.1 = true ∧
       art.2.2.2.2.2.1.2.2.2.2.2.2.2 = true ∧ art.2.2.2.2.2.1 = cert.1)) ∧
    (AdmissibleBinding cert art = true ↔
      (classifyIntegrationChange cert art = 0 ∨ classifyIntegrationChange cert art = 1)) := by
  constructor
  · unfold AdmissibleBinding
    cases art.2.1 <;> cases art.2.2.1 <;> cases art.2.2.2.2.2.1.2.2.2.2.2.2.2
    · exact ⟨fun h => Bool.noConfusion h, fun ⟨h, _, _, _⟩ => Bool.noConfusion h⟩
    · exact ⟨fun h => Bool.noConfusion h, fun ⟨h, _, _, _⟩ => Bool.noConfusion h⟩
    · exact ⟨fun h => Bool.noConfusion h, fun ⟨h, _, _, _⟩ => Bool.noConfusion h⟩
    · exact ⟨fun h => Bool.noConfusion h, fun ⟨h, _, _, _⟩ => Bool.noConfusion h⟩
    · exact ⟨fun h => Bool.noConfusion h, fun ⟨_, h, _, _⟩ => Bool.noConfusion h⟩
    · exact ⟨fun h => Bool.noConfusion h, fun ⟨_, h, _, _⟩ => Bool.noConfusion h⟩
    · exact ⟨fun h => Bool.noConfusion h, fun ⟨_, _, h, _⟩ => Bool.noConfusion h⟩
    · exact ⟨fun h => ⟨rfl, rfl, rfl, of_decide_eq_true h⟩,
             fun ⟨_, _, _, h⟩ => decide_eq_true h⟩
  · unfold classifyIntegrationChange
    cases AdmissibleBinding cert art
    · cases (art.2.1 && art.2.2.1 && art.2.2.2.2.2.1.2.2.2.2.2.2.2)
      · exact ⟨fun h => Bool.noConfusion h,
               fun h => Or.elim h
                 (fun (h0 : 2 = 0) => Nat.noConfusion h0)
                 (fun (h1 : 2 = 1) => Nat.noConfusion h1 Nat.noConfusion)⟩
      · cases (decide (art.2.2.2.2.2.1.1 = cert.1.1) &&
               decide (art.2.2.2.2.2.1.2.1 = cert.1.2.1))
        · exact ⟨fun h => Bool.noConfusion h,
                 fun h => Or.elim h
                   (fun (h0 : 3 = 0) => Nat.noConfusion h0)
                   (fun (h1 : 3 = 1) => Nat.noConfusion h1 Nat.noConfusion)⟩
        · exact ⟨fun h => Bool.noConfusion h,
                 fun h => Or.elim h
                   (fun (h0 : 4 = 0) => Nat.noConfusion h0)
                   (fun (h1 : 4 = 1) => Nat.noConfusion h1 Nat.noConfusion)⟩
    · cases decide (art.2.2.2.2.2.2 = cert.2.1)
      · exact ⟨fun _ => Or.inr rfl, fun _ => rfl⟩
      · exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩

/-- Theorem 2: `certA0` admits both `captureA0Mir` (`a1-mir`) and `captureA0Llvm` (`a1-llvm-ir`). -/
theorem a0_cert_admits_a0_captures :
    AdmissibleBinding certA0 captureA0Mir = true ∧
    AdmissibleBinding certA0 captureA0Llvm = true ∧
    classifyIntegrationChange certA0 captureA0Mir = 0 ∧
    classifyIntegrationChange certA0 captureA0Llvm = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Theorem 3: Changing only `IncidentalAdapterMetadata` (including the
`cleanup-binding` relative-vs-absolute path witness `b5fd9b...` vs `30ef69...`)
preserves `AdmissibleBinding` and classifies as `1`. -/
theorem incidental_renumbering_preserves_essential_admission
    (cert : VerifiedClaimCert) (art : CaptureArtifact)
    (inc' : IncidentalAdapterMetadata)
    (hAdm : AdmissibleBinding cert art = true)
    (hDiff : inc' ≠ cert.2.1) :
    let art' : CaptureArtifact :=
      (art.1, art.2.1, art.2.2.1, art.2.2.2.1, art.2.2.2.2.1, art.2.2.2.2.2.1, inc')
    let certCleanup : VerifiedClaimCert :=
      ((1, 1, 5, 0, 1, 4, 0, true), (1, 1, 0, 0), 42)
    let obsCleanupRel : CaptureArtifact :=
      (0, true, true, 57370, 7, (1, 1, 5, 0, 1, 4, 0, true), (1, 1, 0, 0))
    let obsCleanupAbs : CaptureArtifact :=
      (0, true, true, 57910, 8, (1, 1, 5, 0, 1, 4, 0, true), (1, 1, 12, 0))
    AdmissibleBinding cert art' = true ∧
    classifyIntegrationChange cert art' = 1 ∧
    AdmissibleBinding certCleanup obsCleanupRel = true ∧
    AdmissibleBinding certCleanup obsCleanupAbs = true ∧
    classifyIntegrationChange certCleanup obsCleanupAbs = 1 := by
  refine ⟨hAdm, ?_, rfl, rfl, rfl⟩
  have hAdm' :
      AdmissibleBinding cert
        (art.1, art.2.1, art.2.2.1, art.2.2.2.1, art.2.2.2.2.1, art.2.2.2.2.2.1, inc') = true :=
    hAdm
  have hInc : decide (inc' = cert.2.1) = false := by
    cases hDec : decide (inc' = cert.2.1)
    · rfl
    · exact False.elim (hDiff (of_decide_eq_true hDec))
  unfold classifyIntegrationChange
  rw [hAdm']
  change (if decide (inc' = cert.2.1) = true then 0 else 1) = 1
  rw [hInc]
  rfl

/-- Theorem 4: `certA0` rejects `captureA1Mir` (`--cfg=alt_impl` at fixed `N = 1`) with status `4`. -/
theorem cfg_alt_impl_change_invalidates_a0_cert :
    captureA1Mir.2.2.2.2.2.1.1 = certA0.1.1 ∧
    captureA1Mir.2.2.2.2.2.1.2.2.2.2.1 = certA0.1.2.2.2.2.1 ∧
    captureA1Mir.2.2.2.2.2.1.2.2.2.2.2.2.1 = certA0.1.2.2.2.2.2.2.1 ∧
    AdmissibleBinding certA0 captureA1Mir = false ∧
    classifyIntegrationChange certA0 captureA1Mir = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Theorem 5: `certA0` rejects `captureB0Mir` (`--cfg probe_case="b0"`) with status `4`. -/
theorem cfg_variant_b_change_invalidates_a0_cert :
    captureB0Mir.2.2.2.2.2.1.1 = certA0.1.1 ∧
    captureB0Mir.2.2.2.2.2.1.2.2.2.2.1 = certA0.1.2.2.2.2.1 ∧
    AdmissibleBinding certA0 captureB0Mir = false ∧
    classifyIntegrationChange certA0 captureB0Mir = 4 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Theorem 6: `captureB1Mir` (`artifactPresent = true`, `producerExitZero = false`) is rejected
with status `2` (`rejectedProducerFailure`) for every certificate. -/
theorem failed_producer_with_present_mir_file_rejected (cert : VerifiedClaimCert) :
    captureB1Mir.2.2.1 = true ∧
    captureB1Mir.2.1 = false ∧
    AdmissibleBinding cert captureB1Mir = false ∧
    classifyIntegrationChange cert captureB1Mir = 2 ∧
    AdmissibleBinding certA0 captureB1Mir = false ∧
    classifyIntegrationChange certA0 captureB1Mir = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Theorem 7: Admissible binding under `certA0` transfers operational `Execution.NoUB`,
`Execution.Verified`, and return state `(1, 0xA1)` to `runSelectedCallee art`, whereas
`captureA1Mir` steps to `(1, 0xA2)`, `captureB0Mir` steps to `(1, 0xB0)`, and `captureB1Mir`
violates `Execution.NoUB`. -/
theorem admissible_binding_transfers_callee_safety (art : CaptureArtifact)
    (hAdm : AdmissibleBinding certA0 art = true) :
    let bad : (Nat × Nat) → Prop := fun s => s.1 = 2 ∨ s.1 = 3
    let allowed : (Nat × Nat) → Prop := fun s => s.1 = 1
    Execution.NoUB (runSelectedCallee art) bad (0, 0) ∧
    Execution.Verified (runSelectedCallee art) bad allowed (0, 0) ∧
    runSelectedCallee art (0, 0) (1, 0xA1) ∧
    runSelectedCallee captureA1Mir (0, 0) (1, 0xA2) ∧
    runSelectedCallee captureB0Mir (0, 0) (1, 0xB0) ∧
    ¬ Execution.NoUB (runSelectedCallee captureB1Mir) bad (0, 0) := by
  rcases (admissible_iff_reused_or_incidental_refresh certA0 art).1.mp hAdm with
    ⟨hExit, hPres, _, hEss⟩
  have hStepA0 : ∀ s t, runSelectedCallee art s t ↔ (s = (0, 0) ∧ t = (1, 0xA1)) := by
    intro s t
    unfold runSelectedCallee
    rw [hExit, hPres, hEss]
    exact Iff.rfl
  have hVer :
      Execution.Verified (runSelectedCallee art)
        (fun s => s.1 = 2 ∨ s.1 = 3) (fun s => s.1 = 1) (0, 0) := by
    apply Execution.invariant_verified
      (Invariant := fun s => s = (0, 0) ∨ s = (1, 0xA1)) (Or.inl rfl)
    · intro s t _ hStep
      exact Or.inr ((hStepA0 s t).mp hStep).2
    · intro s hInv
      rcases hInv with rfl | rfl
      · exact fun h => Or.elim h
          (fun (h2 : 0 = 2) => Nat.noConfusion h2)
          (fun (h3 : 0 = 3) => Nat.noConfusion h3)
      · exact fun h => Or.elim h
          (fun (h2 : 1 = 2) => Nat.noConfusion h2 Nat.noConfusion)
          (fun (h3 : 1 = 3) => Nat.noConfusion h3 Nat.noConfusion)
    · intro s hInv
      rcases hInv with rfl | rfl
      · exact Or.inr ⟨(1, 0xA1), (hStepA0 (0, 0) (1, 0xA1)).mpr ⟨rfl, rfl⟩⟩
      · exact Or.inl rfl
  have hBadB1 :
      ¬ Execution.NoUB (runSelectedCallee captureB1Mir)
        (fun s => s.1 = 2 ∨ s.1 = 3) (0, 0) :=
    Execution.bad_prefix_not_noUB (Bad := fun s => s.1 = 2 ∨ s.1 = 3)
      (Execution.Reach.tail (Execution.Reach.refl (0, 0)) ⟨rfl, rfl⟩)
      (Or.inl rfl)
  exact ⟨hVer.1, hVer, (hStepA0 (0, 0) (1, 0xA1)).mpr ⟨rfl, rfl⟩,
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, hBadB1⟩

#print axioms admissible_iff_reused_or_incidental_refresh
#print axioms a0_cert_admits_a0_captures
#print axioms incidental_renumbering_preserves_essential_admission
#print axioms cfg_alt_impl_change_invalidates_a0_cert
#print axioms cfg_variant_b_change_invalidates_a0_cert
#print axioms failed_producer_with_present_mir_file_rejected
#print axioms admissible_binding_transfers_callee_safety

end AnnealResearch.IntegrationBinding
