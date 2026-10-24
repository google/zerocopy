import AnnealResearch.RealCaptureAudit

set_option Elab.async false

/-!
# Negative and Adversarial Controls for Real Compiler Capture (`FE-F2`)

This module mechanizes the six negative and adversarial controls from the Follow-Up 2
(`FE-F2`) matched compiler capture probe on `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`
and `charon 0.1.210`:

1. **`provisional_flag_or_stop_after_analysis_control`**: Accepting an exporter-written
   `provisional_hook_written == true` flag (`ProvisionalFlagOnlyOracle`) or a
   `stop_after_analysis` exit-zero check (`StopAfterAnalysisExitZeroOracle`, without
   `monoCollectionCompleted == true`) falsely accepts
   `probe_b1_direct_stop_after_analysis`, `probe_b1_direct_full` (under
   `ProvisionalFlagOnlyOracle`), and `probe_b1_charon_poly` (`exitCode = 0` despite
   post-monomorphization `E0080`).
2. **`charon_associated_const_monomorphize_bypass_control`**: On `const_probe.rs`
   (SHA-256 `13a15e1e35b658aafd143b9d77aa16a99a863011807ab42be34f6507983f57f9`,
   recorded in `capture-corr-v2-ledger.json` runs `const_probe_case_ok_direct_full`,
   `const_probe_case_ok_charon_mono`, `const_probe_case_fail_reachable_direct_full`, and
   `const_probe_case_fail_reachable_charon_mono`), user-space monomorphization
   (`charon rustc --ullbc --monomorphize` under `--cfg case_fail_reachable`,
   `const_probe_case_fail_reachable_mono.ullbc`, SHA-256
   `f9dca9adb7ac1f302582134d121e8466334fe94f006449dee1dda5929fdba22d`) substitutes
   `N = 0` into `RequireNonZero::<0>::VALID` (`1usize ub./ 0usize` left as an
   unevaluated body) without invoking `tcx` CTFE evaluation and exits with code `0`,
   whereas `tcx.collect_and_partition_mono_items` (`const_probe_case_fail_reachable_direct_full`,
   `out_const_case_fail_reachable_full.json`, SHA-256
   `aad27b9dbc2982db8515019c1379a2bf74aa4719e0ae902b428d6641c3f5c233`) exits with code `1` (`E0080`).
3. **`all_owners_const_prerequisite_overapproximation_control`**: Requiring every
   polymorphic HIR owner's mentioned consts to evaluate (`never_instantiated<U>()` in
   `unused_b1` mentioning `checked::<B, 1>`) falsely rejects
   `probe_unused_b1_direct_full`.
4. **`def_path_hash_only_dep_binding_control`**: Checking only local `sourceSha256`,
   `ownerDefPathHash`, and `calleeDefPathHash` without `externalCrateSvh` falsely
   accepts `dep_control_rlib_substituted`.
5. **`non_inline_external_callee_missing_mir_control`**: On
   `dep_provider::dep_non_inline`, `nonInlineMirAvailable = false` in both `.rmeta`
   (`dep_control_rmeta_only`) and `.rlib` (`dep_control_rlib_orig`); treating missing
   external MIR as a trivial `True` safety contract is unsound (`¬ Execution.NoUB`).
6. **`cfg_changed_instance_control`**: Under changed `--cfg` selection on `probe.rs`
   (`<A as Bound>::marker` with `[A, 1_usize]` vs `<B as Bound>::marker` with
   `[B, 1_usize]` / `[B, 0_usize]`, and `probe_a0_direct_full` vs
   `probe_a1_direct_full`), `sourceSha256` and `entry` `defPathHash`
   (`Fingerprint(17723421528714699607, 4570208110444831709)`) are identical while
   the `entry -> checked` call's generic arguments and `collectedMonoItems` differ.

*Authored by an AI agent acting on joshlf's behalf.*
-/

namespace AnnealResearch.RealCaptureControls

open AnnealResearch.RealCaptureAudit

/-! ## Control 1: Provisional Hook Flag or `stop_after_analysis` Oracle -/

/-- Weak oracle that accepts a capture whenever `provisionalHookWritten == true`
on disk, ignoring whether `collect_and_partition_mono_items` finished or `rustc`
exited with `0`. -/
noncomputable def ProvisionalFlagOnlyOracle (r : ProbeCaptureRun) : Bool :=
  r.provisionalHookWritten

/-- Weak oracle that accepts `processExitCode == 0` and `!hasErrorsAtAfterAnalysis`
(as satisfied by `Compilation::Stop` in `after_analysis` or polymorphic
`charon rustc --ullbc`) without requiring `monoCollectionCompleted == true`. -/
noncomputable def StopAfterAnalysisExitZeroOracle (r : ProbeCaptureRun) : Bool :=
  Nat.beq r.processExitCode 0 && !r.hasErrorsAtAfterAnalysis

/-- `probe_b1_charon_poly` (`probe_b1_poly.ullbc`,
SHA-256 `925d2966e7bd44803b4a00f5d0217753961803bca7b4fad47d0482e60412fc9f`):
`charon rustc --ullbc` without `--monomorphize` exits with `0` and writes a
34,184-byte `.ullbc` file on `b1` because polymorphic extraction stops before
monomorphization evaluates `checked::{constant#0}` for `<B, 1>`. -/
noncomputable def probeB1CharonPoly : ProbeCaptureRun :=
  { probeB1DirectStopAfterAnalysis with
    runId := 16 }

/-- **Control 1 (`FE-F2`)**: Accepting `provisionalHookWritten == true` or
`stop_after_analysis` (`processExitCode == 0` without `monoCollectionCompleted`)
falsely accepts `probe_b1_direct_stop_after_analysis`, `probe_b1_direct_full`
(under `ProvisionalFlagOnlyOracle`), and `probe_b1_charon_poly`, whereas
`IndependentCompletionOracle` rejects all three. -/
theorem provisional_flag_or_stop_after_analysis_control :
    ProvisionalFlagOnlyOracle probeB1DirectStopAfterAnalysis = true ∧
    ProvisionalFlagOnlyOracle probeB1DirectFull = true ∧
    StopAfterAnalysisExitZeroOracle probeB1DirectStopAfterAnalysis = true ∧
    StopAfterAnalysisExitZeroOracle probeB1CharonPoly = true ∧
    IndependentCompletionOracle probeB1DirectStopAfterAnalysis = false ∧
    IndependentCompletionOracle probeB1DirectFull = false ∧
    IndependentCompletionOracle probeB1CharonPoly = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Control 2: User-Space Associated-Const Monomorphization Bypass in Charon -/

/-- Observed capture record for `const_probe.rs`
(SHA-256 `13a15e1e35b658aafd143b9d77aa16a99a863011807ab42be34f6507983f57f9`)
recorded in `capture-corr-v2-ledger.json` across `--cfg case_ok` (`N = 4`) and
`--cfg case_fail_reachable` (`N = 0`, where `entry_point` calls `checked_kernel::<0>`
reading associated constant `RequireNonZero::<0>::VALID = 1 / 0`). -/
structure AssociatedConstMonoProbe where
  routeId : Nat
  processExitCode : Nat
  destArtifactWritten : Bool
  invokesTcxMonoCtfe : Bool
  leavesDivByZeroAsUnevaluatedBody : Bool
  divisorConstArg : Nat

/-- `const_probe_case_ok_direct_full` (`out_const_case_ok_full.json`,
SHA-256 `26ead9d9eba970b987c90ff73b8822a04ab095f1a9e1eb2c566a3916657014be`, paired with
`const_probe_case_ok_charon_mono` `const_probe_case_ok_mono.ullbc`
SHA-256 `ec770d6c3e6a04c746ed8d925cb269ee3698d741c676d18a3ed6a55b7219f36c`):
`tcx.collect_and_partition_mono_items` evaluates `RequireNonZero::<4>::VALID = 1 / 4`
and exits with code `0`. -/
noncomputable def constProbeOkTcxMono : AssociatedConstMonoProbe :=
  { routeId := 0
    processExitCode := 0
    destArtifactWritten := true
    invokesTcxMonoCtfe := true
    leavesDivByZeroAsUnevaluatedBody := false
    divisorConstArg := 4 }

/-- `const_probe_case_fail_reachable_charon_mono` (`const_probe_case_fail_reachable_mono.ullbc`,
SHA-256 `f9dca9adb7ac1f302582134d121e8466334fe94f006449dee1dda5929fdba22d`):
user-space monomorphization in `charon rustc --ullbc --monomorphize` substitutes
`0usize` into the copied body of `RequireNonZero::<0>::VALID` (`1usize ub./ 0usize`
in `Fun 5` / `Global 0`) without invoking `tcx` CTFE evaluation, exiting with code
`0` (`has_errors = false`). -/
noncomputable def constProbeFailReachableCharonMono : AssociatedConstMonoProbe :=
  { routeId := 1
    processExitCode := 0
    destArtifactWritten := true
    invokesTcxMonoCtfe := false
    leavesDivByZeroAsUnevaluatedBody := true
    divisorConstArg := 0 }

/-- `const_probe_case_fail_reachable_direct_full` (`out_const_case_fail_reachable_full.json`,
SHA-256 `aad27b9dbc2982db8515019c1379a2bf74aa4719e0ae902b428d6641c3f5c233`):
compiler-driven monomorphization via `tcx.collect_and_partition_mono_items`
evaluates `RequireNonZero::<0>::VALID` via CTFE and aborts compilation with `E0080`
(`attempt to divide 1_usize by zero`, `processExitCode = 1`, provisional hook receipt
written with `mono_collection_completed = false`). -/
noncomputable def constProbeFailReachableTcxMono : AssociatedConstMonoProbe :=
  { routeId := 2
    processExitCode := 1
    destArtifactWritten := false
    invokesTcxMonoCtfe := true
    leavesDivByZeroAsUnevaluatedBody := false
    divisorConstArg := 0 }

/-- Naive oracle that trusts `processExitCode == 0 && destArtifactWritten` from a
user-space monomorphizer without requiring `invokesTcxMonoCtfe`. -/
noncomputable def UserSpaceMonoExitZeroOracle (p : AssociatedConstMonoProbe) : Bool :=
  Nat.beq p.processExitCode 0 && p.destArtifactWritten

/-- Sound monomorphization oracle requiring `processExitCode == 0` from `tcx`
monomorphization collection (`invokesTcxMonoCtfe == true`) and non-zero divisor on
`RequireNonZero::<N>::VALID`. -/
noncomputable def TcxMonoCtfeOracle (p : AssociatedConstMonoProbe) : Bool :=
  Nat.beq p.processExitCode 0 &&
  p.invokesTcxMonoCtfe &&
  !p.leavesDivByZeroAsUnevaluatedBody &&
  Nat.ble 1 p.divisorConstArg

/-- **Control 2 (`FE-F2`)**: On `const_probe.rs`, `TcxMonoCtfeOracle` accepts
`constProbeOkTcxMono` (`case_ok`), whereas on `case_fail_reachable`, user-space
monomorphization without `tcx` CTFE evaluation (`constProbeFailReachableCharonMono`)
exits `0` (`1usize ub./ 0usize` left as an unevaluated body) and passes
`UserSpaceMonoExitZeroOracle`, while `tcx` monomorphization
(`constProbeFailReachableTcxMono`) exits `1` (`E0080`) and `TcxMonoCtfeOracle`
rejects both `case_fail_reachable` runs. -/
theorem charon_associated_const_monomorphize_bypass_control :
    TcxMonoCtfeOracle constProbeOkTcxMono = true ∧
    constProbeFailReachableCharonMono.processExitCode = 0 ∧
    constProbeFailReachableCharonMono.leavesDivByZeroAsUnevaluatedBody = true ∧
    constProbeFailReachableTcxMono.processExitCode = 1 ∧
    UserSpaceMonoExitZeroOracle constProbeFailReachableCharonMono = true ∧
    TcxMonoCtfeOracle constProbeFailReachableCharonMono = false ∧
    TcxMonoCtfeOracle constProbeFailReachableTcxMono = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Control 3: Overapproximating Const Prerequisites Across Uninstantiated Owners -/

/-- Overapproximating gate that requires every polymorphic HIR owner's mentioned
const instantiations (including `never_instantiated<U>()` mentioning `checked::<B, 1>`)
to satisfy `N <= <T as Bound>::LIMIT` (`1 <= 0`). -/
noncomputable def AllOwnersConstPrerequisiteGate (r : ProbeCaptureRun) : Bool :=
  EntryScopedMonoObligationsHold r &&
  (!r.includesNeverInstantiatedOwner || Nat.ble 1 0)

/-- **Control 3 (`FE-F2`)**: Requiring every polymorphic owner's mentioned consts to
evaluate (`AllOwnersConstPrerequisiteGate`) falsely rejects
`probe_unused_b1_direct_full`, whereas `IndependentCompletionOracle` and
`EntryScopedMonoObligationsHold` accept it. -/
theorem all_owners_const_prerequisite_overapproximation_control :
    probeUnusedB1DirectFull.includesNeverInstantiatedOwner = true ∧
    IndependentCompletionOracle probeUnusedB1DirectFull = true ∧
    EntryScopedMonoObligationsHold probeUnusedB1DirectFull = true ∧
    AllOwnersConstPrerequisiteGate probeUnusedB1DirectFull = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Control 4: `DefPathHash`-Only Dependency Binding Without `externalCrateSvh` -/

/-- Weak dependency check that verifies local `sourceSha256`, `ownerDefPathHash`,
and both `calleeDefPathHash` fingerprints, but omits `externalCrateSvh`. -/
noncomputable def DefPathHashOnlyDepCheck (b : DepCaptureBinding) : Bool :=
  Nat.beq b.sourceSha256Hi depControlRlibOrig.sourceSha256Hi &&
  Nat.beq b.ownerDefPathHashHi depControlRlibOrig.ownerDefPathHashHi &&
  Nat.beq b.ownerDefPathHashLo depControlRlibOrig.ownerDefPathHashLo &&
  Nat.beq b.calleeNonInlineDefPathHashHi depControlRlibOrig.calleeNonInlineDefPathHashHi &&
  Nat.beq b.calleeNonInlineDefPathHashLo depControlRlibOrig.calleeNonInlineDefPathHashLo &&
  Nat.beq b.calleeInlinedDefPathHashHi depControlRlibOrig.calleeInlinedDefPathHashHi &&
  Nat.beq b.calleeInlinedDefPathHashLo depControlRlibOrig.calleeInlinedDefPathHashLo

/-- **Control 4 (`FE-F2`)**: Checking only `sourceSha256`, `ownerDefPathHash`, and
`calleeDefPathHash` without `externalCrateSvh` (`DefPathHashOnlyDepCheck`) falsely
accepts `dep_control_rlib_substituted`, whereas `AdmissibleDepCrateBinding` rejects it. -/
theorem def_path_hash_only_dep_binding_control :
    DefPathHashOnlyDepCheck depControlRlibOrig = true ∧
    DefPathHashOnlyDepCheck depControlRlibSubstituted = true ∧
    AdmissibleDepCrateBinding 16377899976409579846 depControlRlibOrig = true ∧
    AdmissibleDepCrateBinding 16377899976409579846 depControlRlibSubstituted = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Control 5: Treating Missing Non-Inline External MIR as a Trivial Contract -/

/-- Unsound capture gate that checks `CombinedHookAndDemandCaptures`,
`EntryScopedMonoObligationsHold`, and `AdmissibleDepCrateBinding`, but treats a
callee with `is_mir_available == false` (`dep_provider::dep_non_inline`) as
satisfying a trivial `True` contract without requiring `externalCalleeBodiesVerified`. -/
noncomputable def MissingMirTrivialContractGate
    (expectedSvh : Nat) (s : CapturedEntrySubject) : Bool :=
  CombinedHookAndDemandCaptures s.modeRun &&
  EntryScopedMonoObligationsHold s.probeRun &&
  AdmissibleDepCrateBinding expectedSvh s.depBinding

/-- Faulting cross-crate subject where `dep_provider::dep_non_inline` has
`nonInlineMirAvailable = false`, no external-crate verification was performed
(`externalCalleeBodiesVerified = false`), and the unverified external call triggers
runtime UB (`entryHasRuntimeUB = true`). -/
noncomputable def faultingMissingExternalMirSubject : CapturedEntrySubject :=
  { modeRun := runCleanupDefault
    probeRun := probeA1DirectFull
    depBinding := depControlRlibOrig
    externalCalleeBodiesVerified := false
    capturedModelHasUB := false
    entryHasRuntimeUB := true }

/-- **Control 5 (`FE-F2`)**: On `dep_provider::dep_non_inline`,
`nonInlineMirAvailable = false` in both `.rmeta` (`depControlRmetaOnly`) and `.rlib`
(`depControlRlibOrig`); treating missing external MIR as a trivial `True` contract
(`MissingMirTrivialContractGate`) admits `faultingMissingExternalMirSubject` which
violates `Execution.NoUB`, whereas `AdmissibleCaptureBinding` rejects it. -/
theorem non_inline_external_callee_missing_mir_control :
    depControlRmetaOnly.nonInlineMirAvailable = false ∧
    depControlRlibOrig.nonInlineMirAvailable = false ∧
    MissingMirTrivialContractGate 16377899976409579846
      faultingMissingExternalMirSubject = true ∧
    AdmissibleCaptureBinding 16377899976409579846
      faultingMissingExternalMirSubject = false ∧
    ¬ Execution.NoUB (capturedEntryStep faultingMissingExternalMirSubject)
        capturedEntryBad initEntryExecState := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  have hReach :
      Execution.Reach (capturedEntryStep faultingMissingExternalMirSubject)
        initEntryExecState (1, true) :=
    Execution.Reach.tail (Execution.Reach.refl initEntryExecState) ⟨rfl, rfl⟩
  have hBad : capturedEntryBad (1, true) := rfl
  exact Execution.bad_prefix_not_noUB (Bad := capturedEntryBad) hReach hBad

/-! ## Control 6: `--cfg`-Changed Instance Under Identical Source and Owner `DefPathHash` -/

/-- Counterfactual/configured variant comparison under identical `probe.rs`
`sourceSha256` and identical `entry` `DefPathHash`
(`Fingerprint(17723421528714699607, 4570208110444831709)`). -/
noncomputable def SourceAndEntryDefPathHashOnlyMatch
    (r1 r2 : ProbeCaptureRun) : Bool :=
  Nat.beq r1.sourceSha256Hi r2.sourceSha256Hi &&
  Nat.beq r1.entryDefPathHashHi r2.entryDefPathHashHi &&
  Nat.beq r1.entryDefPathHashLo r2.entryDefPathHashLo

/-- Instance-aware check that binds the generic arguments of `entry -> checked`
(`entryCheckedTypeArgId`, `entryCheckedConstArg`), the resolved `<Selected as Bound>::marker`
`DefPathHash`, and `collectedMonoItems`. -/
noncomputable def ExactEntryInstanceAndMonoMatch
    (r1 r2 : ProbeCaptureRun) : Bool :=
  SourceAndEntryDefPathHashOnlyMatch r1 r2 &&
  Nat.beq r1.entryCheckedTypeArgId r2.entryCheckedTypeArgId &&
  Nat.beq r1.entryCheckedConstArg r2.entryCheckedConstArg &&
  Nat.beq r1.selectedMarkerDefPathHashLo r2.selectedMarkerDefPathHashLo &&
  Nat.beq r1.collectedMonoItemsCount r2.collectedMonoItemsCount &&
  (r1.monoHasEntry == r2.monoHasEntry) &&
  (r1.monoHasCheckedA1 == r2.monoHasCheckedA1) &&
  (r1.monoHasCheckedB0 == r2.monoHasCheckedB0)

/-- **Control 6 (`FE-F2`)**: Across `probe_a0_direct_full`, `probe_a1_direct_full`
(`[A, 1_usize]`, `<A as Bound>::marker`), `probe_b1_direct_full` (`[B, 1_usize]`,
`<B as Bound>::marker`), and `probe_b0_direct_full` (`[B, 0_usize]`,
`<B as Bound>::marker`), `sourceSha256` and `entry` `defPathHash` are identical
(`SourceAndEntryDefPathHashOnlyMatch = true`), while the `entry -> checked` call's
generic argument (`[A, 1_usize]` vs `[B, 1_usize]` / `[B, 0_usize]`), resolved
`<T as Bound>::marker` `DefPathHash`, and `collectedMonoItems` differ
(`ExactEntryInstanceAndMonoMatch = false`). -/
theorem cfg_changed_instance_control :
    SourceAndEntryDefPathHashOnlyMatch probeA0DirectFull probeA1DirectFull = true ∧
    SourceAndEntryDefPathHashOnlyMatch probeA1DirectFull probeB1DirectFull = true ∧
    SourceAndEntryDefPathHashOnlyMatch probeA1DirectFull probeB0DirectFull = true ∧
    probeA1DirectFull.entryCheckedTypeArgId = 1 ∧
    probeB1DirectFull.entryCheckedTypeArgId = 2 ∧
    probeA1DirectFull.entryCheckedConstArg = 1 ∧
    probeB1DirectFull.entryCheckedConstArg = 1 ∧
    probeA0DirectFull.collectedMonoItemsCount = 2 ∧
    probeA1DirectFull.collectedMonoItemsCount = 4 ∧
    probeA1DirectFull.monoHasCheckedA1 = true ∧
    probeB0DirectFull.monoHasCheckedA1 = false ∧
    probeB0DirectFull.monoHasCheckedB0 = true ∧
    ExactEntryInstanceAndMonoMatch probeA0DirectFull probeA1DirectFull = false ∧
    ExactEntryInstanceAndMonoMatch probeA1DirectFull probeB1DirectFull = false ∧
    ExactEntryInstanceAndMonoMatch probeA1DirectFull probeB0DirectFull = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms provisional_flag_or_stop_after_analysis_control
#print axioms charon_associated_const_monomorphize_bypass_control
#print axioms all_owners_const_prerequisite_overapproximation_control
#print axioms def_path_hash_only_dep_binding_control
#print axioms non_inline_external_callee_missing_mir_control
#print axioms cfg_changed_instance_control

end AnnealResearch.RealCaptureControls
