import AnnealResearch.CargoWorkspaceIntegration
import AnnealResearch.SemanticVerticalSliceCore

set_option maxRecDepth 65536

namespace AnnealResearch.CargoWorkspaceIntegrationControls

open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.SemanticVerticalSlice
open AnnealResearch.CargoWorkspaceIntegration

/-!
# Cargo Workspace & Build-Graph Negative Controls (.amir v3)

Proves the 4 mandatory build-graph and `.amir` v3 wire-level negative controls
for `joshlf/anneal#61`:
1. **Substituted `.rlib` / SVH mismatch**: Substituting an external `.rlib` or `.amir` v3
   package whose SVH / header fingerprint (`rustcHi`/`rustcLo` or `svhFingerprintLo`)
   differs from the dependency SVH recorded when `app_verifier_subject` was compiled
   is rejected.
2. **Missing transitive `.amir` v3 / unencoded cross-crate body**: A workspace build where a
   transitive dependency `.amir` v3 body (`symId = 53` `dep_non_inline_check`) or `.rlib`
   body is missing is rejected.
3. **Stale feature `.amir` v3 paired with strict binary**: Pairing the default-feature
   `dep_default.amir` (`fp16 = [248, 73]`, `STRICT_ALIGN_BONUS = 0`) with the strict-feature
   `app_strict.amir` (`fp16 = [93, 31]`, `STRICT_ALIGN_BONUS = 8`) is rejected both by
   `verifyWorkspaceBuildGraph` and by `evalWireWorkspaceCallGraph` (`none`).
4. **Incomplete / provisional compilation (`cargo check` / failing reachable post-mono const)**:
   Artifacts produced under `cargo check` (`--emit=dep-info,metadata`, where
   `collect_and_partition_mono_items` did not run and `amir_v3_status = "rejected_incomplete_compilation"`)
   or with post-monomorphization const-eval errors (`alpha::<()>()`) are rejected, while
   an uninstantiated/unused generic post-mono const (`alpha::<u64>()`, `post_mono_unused_accepted.amir`)
   is accepted.
-/

/-- Negative Control 1 (Package level): `dep_layout_core` `.rlib` substituted with a different SVH. -/
def substitutedRlibDepPkg : CrateArtifactPackage :=
  { depLayoutCoreAlwaysEncodePkg with
    svhFingerprintLo := 9999999999999999999 }

/-- Negative Control 1 (Wire level): `dep_default.amir` header corrupted with mismatched compiler/SVH tag. -/
def substitutedSvhHeaderAmirV3Bytes : List Nat :=
  match depDefaultAmirV3Bytes with
  | m0 :: m1 :: m2 :: m3 :: ver :: _ :: lo :: rest =>
    m0 :: m1 :: m2 :: m3 :: ver :: 99 :: lo :: rest
  | other => other

theorem control1_substituted_rlib_svh_mismatch_rejected :
    verifyWorkspaceBuildGraph substitutedRlibDepPkg appVerifierAlwaysEncodePkg = false ∧
    evalWorkspaceCallGraph substitutedRlibDepPkg appVerifierAlwaysEncodePkg 1 = none ∧
    isAcceptedWirePackage (parseWirePackage substitutedSvhHeaderAmirV3Bytes) = false ∧
    evalWireWorkspaceCallGraph substitutedSvhHeaderAmirV3Bytes appDefaultAmirV3Bytes 1 = none := by
  decide

/-- Negative Control 2 (Package & Wire level): Missing transitive `.amir` v3 dependency
    (empty bytes or stripped `dep_non_inline_check` body `symId = 53`). -/
def depMissingNonInlineBodyAmirV3Bytes : List Nat :=
  match parseWirePackage depDefaultAmirV3Bytes with
  | .accepted pkg =>
    specEncodePackage { pkg with bodies := pkg.bodies.filter (fun b => b.symId != 53) }
  | _ => []

theorem control2_missing_transitive_amir_rejected :
    verifyWorkspaceBuildGraph depLayoutCoreDefaultPkg appVerifierDefaultPkg = false ∧
    evalWorkspaceCallGraph depLayoutCoreDefaultPkg appVerifierDefaultPkg 1 = none ∧
    evalWireWorkspaceCallGraph [] appDefaultAmirV3Bytes 1 = none ∧
    evalWireWorkspaceCallGraph depMissingNonInlineBodyAmirV3Bytes appDefaultAmirV3Bytes 1 = none := by
  decide

/-- Negative Control 3 (Package & Wire level): Stale feature `.amir` v3 (`dep_default.amir`,
    `STRICT_ALIGN_BONUS = 0`, `fp16 = [248, 73]`) paired with `--features strict_align`
    binary (`app_strict.amir`, `STRICT_ALIGN_BONUS = 8`, `fp16 = [93, 31]`), or vice versa. -/
def forgedSvhStaleFeatureAppPkg : CrateArtifactPackage :=
  { appVerifierStrictAlignPkg with
    externalDepSvhs :=
      [ ("core", 3402364753734922174)
      , ("dep_layout_core", depLayoutCoreAlwaysEncodePkg.svhFingerprintLo)
      ] }

theorem control3_stale_feature_amir_rejected :
    verifyWorkspaceBuildGraph depLayoutCoreAlwaysEncodePkg appVerifierStrictAlignPkg = false ∧
    verifyWorkspaceBuildGraph depLayoutCoreStrictAlignPkg appVerifierAlwaysEncodePkg = false ∧
    verifyWorkspaceBuildGraph depLayoutCoreAlwaysEncodePkg forgedSvhStaleFeatureAppPkg = false ∧
    evalWireWorkspaceCallGraph depDefaultAmirV3Bytes appStrictAmirV3Bytes 1 = none ∧
    evalWireWorkspaceCallGraph depStrictAmirV3Bytes appDefaultAmirV3Bytes 1 = none ∧
    evalWireDirectCallGraph depDefaultAmirV3Bytes appStrictAmirV3Bytes 13 = none ∧
    evalWireDirectCallGraph depStrictAmirV3Bytes appDefaultAmirV3Bytes 13 = none := by
  decide

/-- Negative Control 4: Incomplete/provisional compilation (`cargo check` without mono collector,
    or reachable post-monomorphization const-eval failure) is rejected, whereas an unused/uninstantiated
    failing post-mono const (`postMonoUnusedAcceptedAmirV3Bytes`) is accepted. -/
def postMonoReachableErrorPkg : CrateArtifactPackage :=
  { appVerifierAlwaysEncodePkg with
    completeness := .rejectedHasErrors }

theorem control4_incomplete_provisional_compilation_rejected :
    verifyWorkspaceBuildGraph depLayoutCoreAlwaysEncodePkg appVerifierCheckFastPkg = false ∧
    evalWorkspaceCallGraph depLayoutCoreAlwaysEncodePkg appVerifierCheckFastPkg 1 = none ∧
    verifyWorkspaceBuildGraph depLayoutCoreAlwaysEncodePkg postMonoReachableErrorPkg = false ∧
    evalWorkspaceCallGraph depLayoutCoreAlwaysEncodePkg postMonoReachableErrorPkg 1 = none ∧
    isAcceptedWirePackage (parseWirePackage postMonoUnusedAcceptedAmirV3Bytes) = true := by
  decide

/-- Negative Control 5 (`#64` §6.3 / `H6`/`H7`): Per-field negative controls for
    `verifyCargoInvocationBinding`, proving that mutating ANY individual field of
    `CargoInvocationBindingRecord` (`crateName`, `role`, `features`, `cfgFlags`,
    `alwaysEncodeMir`, `preserveUb`, `svhFingerprintLo`, `externalDepSvhs`,
    `sourceContentSha256Hi64`, `generatedOutDirFileDigestTag`, `completeness`, or `expectedFp16`)
    causes `verifyCargoInvocationBinding` to reject! -/
theorem control5_per_field_cargo_invocation_binding_rejections :
    verifyCargoInvocationBinding depDefaultExpectedContext
      { depDefaultInvocationBinding with crateName := "wrong_crate" }
      depLayoutCoreCrateBytes depDefaultAmirV3Bytes = false ∧
    verifyCargoInvocationBinding depDefaultExpectedContext
      { depDefaultInvocationBinding with role := .hostBuildScript }
      depLayoutCoreCrateBytes depDefaultAmirV3Bytes = false ∧
    verifyCargoInvocationBinding depDefaultExpectedContext
      { depDefaultInvocationBinding with features := ["strict_align"] }
      depLayoutCoreCrateBytes depDefaultAmirV3Bytes = false ∧
    verifyCargoInvocationBinding depDefaultExpectedContext
      { depDefaultInvocationBinding with cfgFlags := ["feature=\"strict_align\""] }
      depLayoutCoreCrateBytes depDefaultAmirV3Bytes = false ∧
    verifyCargoInvocationBinding depDefaultExpectedContext
      { depDefaultInvocationBinding with alwaysEncodeMir := false }
      depLayoutCoreCrateBytes depDefaultAmirV3Bytes = false ∧
    verifyCargoInvocationBinding depDefaultExpectedContext
      { depDefaultInvocationBinding with preserveUb := false }
      depLayoutCoreCrateBytes depDefaultAmirV3Bytes = false ∧
    verifyCargoInvocationBinding depDefaultExpectedContext
      { depDefaultInvocationBinding with svhFingerprintLo := 9999999999999999999 }
      depLayoutCoreCrateBytes depDefaultAmirV3Bytes = false ∧
    verifyCargoInvocationBinding depDefaultExpectedContext
      { depDefaultInvocationBinding with externalDepSvhs := [("core", 1111111111111111111)] }
      depLayoutCoreCrateBytes depDefaultAmirV3Bytes = false ∧
    verifyCargoInvocationBinding depDefaultExpectedContext
      { depDefaultInvocationBinding with sourceContentSha256Hi64 := 0xdeadbeefcafebabe }
      depLayoutCoreCrateBytes depDefaultAmirV3Bytes = false ∧
    verifyCargoInvocationBinding depDefaultExpectedContext
      { depDefaultInvocationBinding with generatedOutDirFileDigestTag := some 0x123456789abcdef0 }
      depLayoutCoreCrateBytes depDefaultAmirV3Bytes = false ∧
    verifyCargoInvocationBinding depDefaultExpectedContext
      { depDefaultInvocationBinding with generatedOutDirFileDigestTag := none }
      depLayoutCoreCrateBytes depDefaultAmirV3Bytes = false ∧
    verifyCargoInvocationBinding depDefaultExpectedContext
      { depDefaultInvocationBinding with completeness := .rejectedIncompleteCheckOnly }
      depLayoutCoreCrateBytes depDefaultAmirV3Bytes = false ∧
    verifyCargoInvocationBinding depDefaultExpectedContext
      { depDefaultInvocationBinding with expectedFp16 := (86, 21) }
      depLayoutCoreCrateBytes depDefaultAmirV3Bytes = false := by
  decide

/-!
## 6. `#68` §6 `N5`: Open-Hash Non-Spelling-Specific Acquisition & External `.rlib` `optimized_mir` vs `Runtime(PostCleanup)` Sidecar Discriminator

1. **Open-hash non-spelling-specific acquisition (`--driver-open-hash-mode`)**:
   - `n5_ring_window_probe.amir` (`391` B, SHA-256 `161494ccd84729b08628408f26419cb924be623d6c9b907a6fe62a0d81db542c`)
     and `n5_ring_window_probe_refactored.amir` (`391` B, SHA-256 `c65e8a8f9ac95a63bb1a570c63776d1df40dd9ee106aa15ae220059ed55d5efa`)
     are captured from `ring_window_probe.rs` and `ring_window_probe_refactored.rs`, whose crate/type/function
     names (`ring_window_probe`, `QuotaCell`, `advance_quota`, `verify_two_instances`) do not appear anywhere in
     `direct_mir_driver_v4.rs`.
   - Keying symbol allocation on `(tcx.def_path_hash(def_id), erased_substs)` assigns invariant symbol IDs across
     both the baseline and the local-binding/expression-order refactoring:
     `verify_two_instances = 170`, `advance_quota::<u32, 4> = 93`, `advance_quota::<u64, 8> = 218`,
     `core::mem::align_of::<u32> = 211`, and `core::mem::align_of::<u64> = 162`.
   - Both decoded packages evaluate `verify_two_instances(true, true, 10)` via `SemanticVerticalSliceCore.runSteps`
     to `.returned (.scalar 39)` (`10 + (4 + 2 + 4) + (8 + 3 + 8) = 39`) and fail with `.failed .invalidPtrDeref`
     whenever either raw pointer (`p32` or `p64`) is invalid (`false`).
   - Swapping the selected monomorphized generic instance in `verify_two_instances` (`advance_quota::<u64, 8>` `218`
     substituted for `advance_quota::<u32, 4>` `93`) while preserving function count and CFG shape falsifies the
     operational contract (`47 ≠ 39`).
2. **External `.rlib` `optimized_mir` (`0x04`) vs `Runtime(PostCleanup)` sidecar (`0x03`) discriminator**:
   - `n5_ext_phase_lib_sidecar.amir` (`58` B, SHA-256 `3a5a05a63e5de0e02565a3bdd94976f2c51dce6d11100bce45b8fc5ee7578aef`)
     captures `ext_probe_mention_and_storage` (`symId = 222`) at `MirPhaseTag.runtimePostCleanup` (`0x03`),
     preserving `PlaceMention((*_1))` and `StorageLive`/`StorageDead`.
   - `n5_ext_phase_client_from_default_rlib.amir` (`107` B, SHA-256 `f636e4d00a29a545177addfb26f0424d9cb8ebf8396012ef0e26a4032149b286`)
     reads `ext_probe_mention_and_storage` (`symId = 222`) from the external `.rlib`'s `tcx.optimized_mir(def_id)`
     at `MirPhaseTag.runtimeOptimized` (`0x04`), where `RemovePlaceMention` and `RemoveStorageMarkers` stripped
     `PlaceMention((*_1))` and all storage markers. Consequently, on `ptrValid = false, x = 20`, executing
     `client_rlib_vs_sidecar_entry` (`symId = 220`) against the `.rlib` `optimized_mir` body erroneously returns
     `.returned (.scalar 34)` instead of `.failed .invalidPtrDeref`!
   - Even when the external `.rlib` is compiled with `-Z mir-preserve-ub`
     (`n5_ext_phase_client_from_preserve_ub_rlib.amir`, `110` B, SHA-256 `8d417d10f90ec2ce3729a1cc2c2a4528693f84cc68141ceeda666b5aa0969d4d`),
     its `.rlib`-encoded body has `mirPhase = .runtimeOptimized` (`0x04`), `localCount = 3`, and `0` storage markers
     (vs `mirPhase = .runtimePostCleanup` `0x03`, `localCount = 5`, and `4` storage markers in the sidecar).
-/

def n5RingWindowProbeAmirV3Bytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 181, 149, 5, 1, 170, 1, 3, 10, 3, 3, 4, 5, 5, 4, 4, 5, 4, 4, 5, 4, 0, 5, 32, 4, 32, 5, 17, 5, 0, 1, 0, 32, 6, 17, 6, 0, 3, 0, 76, 93, 4, 0, 1, 252, 69, 0, 70, 0, 130, 2, 0, 7, 33, 6, 33, 5, 32, 7, 32, 8, 17, 8, 0, 2, 0, 32, 9, 17, 9, 0, 4, 0, 76, 218, 7, 0, 2, 252, 72, 0, 73, 0, 130, 3, 0, 5, 33, 9, 33, 8, 17, 0, 0, 7, 0, 33, 7, 33, 4, 64, 2, 93, 1, 3, 12, 3, 5, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 48, 1, 4, 32, 4, 73, 211, 4, 0, 1, 252, 0, 5, 32, 5, 32, 6, 17, 6, 0, 2, 0, 32, 7, 17, 7, 0, 4, 0, 75, 40, 5, 0, 2, 252, 70, 0, 71, 0, 0, 7, 33, 7, 33, 6, 32, 8, 32, 9, 17, 9, 0, 5, 0, 32, 10, 17, 10, 0, 3, 0, 75, 40, 8, 0, 3, 252, 73, 0, 74, 0, 0, 4, 33, 10, 33, 9, 32, 11, 17, 11, 0, 8, 0, 75, 40, 0, 0, 4, 252, 75, 0, 130, 4, 0, 4, 33, 11, 33, 8, 33, 5, 33, 4, 64, 3, 218, 1, 3, 12, 3, 5, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 48, 1, 4, 32, 4, 73, 162, 4, 0, 1, 252, 0, 5, 32, 5, 32, 6, 17, 6, 0, 2, 0, 32, 7, 17, 7, 0, 4, 0, 75, 40, 5, 0, 2, 252, 70, 0, 71, 0, 0, 7, 33, 7, 33, 6, 32, 8, 32, 9, 17, 9, 0, 5, 0, 32, 10, 17, 10, 0, 3, 0, 75, 40, 8, 0, 3, 252, 73, 0, 74, 0, 0, 4, 33, 10, 33, 9, 32, 11, 17, 11, 0, 8, 0, 75, 40, 0, 0, 4, 252, 75, 0, 130, 8, 0, 4, 33, 11, 33, 8, 33, 5, 33, 4, 64, 4, 211, 2, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64, 5, 162, 2, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 8, 64]

def n5RingWindowProbeRefactoredAmirV3Bytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 74, 149, 5, 1, 170, 1, 3, 10, 3, 3, 4, 5, 5, 4, 4, 5, 4, 4, 5, 4, 0, 5, 32, 4, 32, 5, 17, 5, 0, 1, 0, 32, 6, 17, 6, 0, 3, 0, 76, 93, 4, 0, 1, 252, 69, 0, 70, 0, 130, 2, 0, 7, 33, 6, 33, 5, 32, 7, 32, 8, 17, 8, 0, 2, 0, 32, 9, 17, 9, 0, 4, 0, 76, 218, 7, 0, 2, 252, 72, 0, 73, 0, 130, 3, 0, 5, 33, 9, 33, 8, 17, 0, 0, 7, 0, 33, 7, 33, 4, 64, 2, 93, 1, 3, 12, 3, 5, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 48, 1, 4, 32, 4, 73, 211, 4, 0, 1, 252, 0, 5, 32, 5, 32, 6, 17, 6, 0, 2, 0, 32, 7, 17, 7, 0, 3, 0, 75, 40, 5, 0, 2, 252, 70, 0, 71, 0, 0, 7, 33, 7, 33, 6, 32, 8, 32, 9, 17, 9, 0, 5, 0, 32, 10, 17, 10, 0, 4, 0, 75, 40, 8, 0, 3, 252, 73, 0, 74, 0, 0, 4, 33, 10, 33, 9, 32, 11, 17, 11, 0, 8, 0, 75, 40, 0, 0, 4, 252, 75, 0, 130, 4, 0, 4, 33, 11, 33, 8, 33, 5, 33, 4, 64, 3, 218, 1, 3, 12, 3, 5, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 48, 1, 4, 32, 4, 73, 162, 4, 0, 1, 252, 0, 5, 32, 5, 32, 6, 17, 6, 0, 2, 0, 32, 7, 17, 7, 0, 3, 0, 75, 40, 5, 0, 2, 252, 70, 0, 71, 0, 0, 7, 33, 7, 33, 6, 32, 8, 32, 9, 17, 9, 0, 5, 0, 32, 10, 17, 10, 0, 4, 0, 75, 40, 8, 0, 3, 252, 73, 0, 74, 0, 0, 4, 33, 10, 33, 9, 32, 11, 17, 11, 0, 8, 0, 75, 40, 0, 0, 4, 252, 75, 0, 130, 8, 0, 4, 33, 11, 33, 8, 33, 5, 33, 4, 64, 4, 211, 2, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64, 5, 162, 2, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 8, 64]

def n5ExtPhaseLibSidecarAmirV3Bytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 96, 214, 1, 1, 222, 1, 3, 5, 2, 2, 4, 5, 4, 4, 4, 0, 4, 48, 1, 4, 32, 3, 32, 4, 17, 4, 0, 2, 0, 75, 40, 3, 0, 1, 252, 68, 0, 130, 4, 0, 3, 33, 4, 17, 0, 0, 3, 0, 33, 3, 64]

def n5ExtPhaseClientDefaultRlibAmirV3Bytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 62, 67, 2, 1, 220, 1, 3, 7, 2, 3, 4, 5, 4, 4, 5, 4, 4, 0, 5, 32, 3, 32, 4, 17, 4, 0, 1, 0, 32, 5, 17, 5, 0, 2, 0, 75, 222, 3, 0, 1, 252, 68, 0, 69, 0, 0, 4, 33, 5, 33, 4, 32, 6, 17, 6, 0, 3, 0, 75, 40, 0, 0, 2, 252, 70, 0, 130, 10, 0, 2, 33, 6, 33, 3, 64, 2, 222, 3, 4, 3, 2, 2, 4, 5, 4, 0, 0, 75, 40, 0, 0, 1, 252, 2, 0, 130, 4, 0, 0, 64]

def n5ExtPhaseClientPreserveUbRlibAmirV3Bytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 70, 87, 2, 1, 220, 1, 3, 7, 2, 3, 4, 5, 4, 4, 5, 4, 4, 0, 5, 32, 3, 32, 4, 17, 4, 0, 1, 0, 32, 5, 17, 5, 0, 2, 0, 75, 222, 3, 0, 1, 252, 68, 0, 69, 0, 0, 4, 33, 5, 33, 4, 32, 6, 17, 6, 0, 3, 0, 75, 40, 0, 0, 2, 252, 70, 0, 130, 10, 0, 2, 33, 6, 33, 3, 64, 2, 222, 3, 4, 3, 2, 2, 4, 5, 4, 0, 1, 48, 1, 4, 75, 40, 0, 0, 1, 252, 2, 0, 130, 4, 0, 0, 64]

def decodePackageBodies (bytes : List Nat) : List WireBody :=
  match parseWirePackage bytes with
  | .accepted pkg => pkg.bodies
  | _ => []

def n5RingWindowProbeBodies : List WireBody :=
  decodePackageBodies n5RingWindowProbeAmirV3Bytes

def n5RingWindowProbeRefactoredBodies : List WireBody :=
  decodePackageBodies n5RingWindowProbeRefactoredAmirV3Bytes

def evalVerifyTwoInstances (bodies : List WireBody) (p32Valid p64Valid : Bool) (init : Nat) : ExecStatus :=
  let initSt := initEntryStateWithHeap bodies 170
    [.extPtr p32Valid, .extPtr p64Valid, .scalar init] []
  (runSteps bodies 32 initSt).status

/-- Negative control for `N5`: swapping the monomorphized generic instance callee in
    `verify_two_instances` (`symId = 170`, replacing `advance_quota::<u32, 4>` `93` with
    `advance_quota::<u64, 8>` `218`) while keeping function count, symbol IDs, and CFG
    shape identical. -/
def n5SwappedGenericInstanceBodies : List WireBody :=
  n5RingWindowProbeBodies.map (fun b =>
    if b.symId == 170 then
      { b with blocks := b.blocks.map (fun blk =>
          match blk.term with
          | .call3 93 dst target unwind a1 a2 a3 =>
            { blk with term := .call3 218 dst target unwind a1 a2 a3 }
          | _ => blk) }
    else b)

theorem n5_open_hash_ring_window_probe_and_refactor_verified :
    isAdmittedPackageBytes n5RingWindowProbeAmirV3Bytes = true ∧
    isAdmittedPackageBytes n5RingWindowProbeRefactoredAmirV3Bytes = true ∧
    n5RingWindowProbeAmirV3Bytes ≠ n5RingWindowProbeRefactoredAmirV3Bytes ∧
    (n5RingWindowProbeBodies.map (fun b => b.symId)) = [170, 93, 218, 211, 162] ∧
    (n5RingWindowProbeRefactoredBodies.map (fun b => b.symId)) = [170, 93, 218, 211, 162] ∧
    evalVerifyTwoInstances n5RingWindowProbeBodies true true 10 = .returned (.scalar 39) ∧
    evalVerifyTwoInstances n5RingWindowProbeRefactoredBodies true true 10 = .returned (.scalar 39) ∧
    evalVerifyTwoInstances n5RingWindowProbeBodies false true 10 = .ub ∧
    evalVerifyTwoInstances n5RingWindowProbeRefactoredBodies false true 10 = .ub ∧
    evalVerifyTwoInstances n5RingWindowProbeBodies true false 10 = .ub ∧
    evalVerifyTwoInstances n5RingWindowProbeRefactoredBodies true false 10 = .ub ∧
    evalVerifyTwoInstances n5SwappedGenericInstanceBodies true true 10 = .returned (.scalar 47) ∧
    evalVerifyTwoInstances n5SwappedGenericInstanceBodies true true 10 ≠ .returned (.scalar 39) := by
  decide

def n5ExtPhaseLibSidecarBodies : List WireBody :=
  decodePackageBodies n5ExtPhaseLibSidecarAmirV3Bytes

def n5ExtClientDefaultRlibBodies : List WireBody :=
  decodePackageBodies n5ExtPhaseClientDefaultRlibAmirV3Bytes

def n5ExtClientPreserveUbRlibBodies : List WireBody :=
  decodePackageBodies n5ExtPhaseClientPreserveUbRlibAmirV3Bytes

/-- Linked workspace bodies pairing the local client body (`symId = 220`) with the
    `Runtime(PostCleanup)` (`0x03`) dependency sidecar (`symId = 222`) instead of the
    `.rlib`'s `Runtime(Optimized)` (`0x04`) body. -/
def n5ExtClientLinkedWithPostCleanupSidecarBodies : List WireBody :=
  (n5ExtClientDefaultRlibBodies.filter (fun b => b.symId == 220)) ++ n5ExtPhaseLibSidecarBodies

def evalClientRlibVsSidecarEntry (bodies : List WireBody) (ptrValid : Bool) (x : Nat) : ExecStatus :=
  let initSt := initEntryStateWithHeap bodies 220
    [.extPtr ptrValid, .scalar x] []
  (runSteps bodies 24 initSt).status

/-- Phase-aware admission predicate requiring non-shim bodies to be captured at
    `MirPhaseTag.runtimePostCleanup` (`0x03`), rejecting `.rlib`-recovered `Runtime(Optimized)` (`0x04`)
    bodies when pre-optimization safety/storage observations are required. -/
def checkAllNonShimBodiesPostCleanup (bodies : List WireBody) : Bool :=
  bodies.all (fun b =>
    match b.originKind with
    | .compilerShim => true
    | _ => b.mirPhase == .runtimePostCleanup)

def countBodyStorageMarkers (b : WireBody) : Nat :=
  b.blocks.foldl (fun acc blk =>
    acc + (blk.stmts.filter (fun s =>
      match s with
      | .storageLive _ => true
      | .storageDead _ => true
      | _ => false)).length) 0

theorem n5_external_rlib_optimized_mir_vs_postcleanup_sidecar_discriminator :
    isAdmittedPackageBytes n5ExtPhaseLibSidecarAmirV3Bytes = true ∧
    isAdmittedPackageBytes n5ExtPhaseClientDefaultRlibAmirV3Bytes = true ∧
    isAdmittedPackageBytes n5ExtPhaseClientPreserveUbRlibAmirV3Bytes = true ∧
    checkAllNonShimBodiesPostCleanup n5ExtClientLinkedWithPostCleanupSidecarBodies = true ∧
    checkAllNonShimBodiesPostCleanup n5ExtClientDefaultRlibBodies = false ∧
    checkAllNonShimBodiesPostCleanup n5ExtClientPreserveUbRlibBodies = false ∧
    evalClientRlibVsSidecarEntry n5ExtClientLinkedWithPostCleanupSidecarBodies true 20 = .returned (.scalar 34) ∧
    evalClientRlibVsSidecarEntry n5ExtClientLinkedWithPostCleanupSidecarBodies false 20 = .ub ∧
    evalClientRlibVsSidecarEntry n5ExtClientDefaultRlibBodies false 20 = .returned (.scalar 34) ∧
    evalClientRlibVsSidecarEntry n5ExtClientDefaultRlibBodies false 20 ≠ .ub ∧
    (match findBodyBySym n5ExtPhaseLibSidecarBodies 222, findBodyBySym n5ExtClientPreserveUbRlibBodies 222 with
     | some sidecarBody, some rlibBody =>
       sidecarBody.mirPhase == .runtimePostCleanup &&
       rlibBody.mirPhase == .runtimeOptimized &&
       sidecarBody.localCount == 5 &&
       rlibBody.localCount == 3 &&
       countBodyStorageMarkers sidecarBody == 4 &&
       countBodyStorageMarkers rlibBody == 0
     | _, _ => false) = true := by
  decide

#print axioms control1_substituted_rlib_svh_mismatch_rejected
#print axioms control2_missing_transitive_amir_rejected
#print axioms control3_stale_feature_amir_rejected
#print axioms control4_incomplete_provisional_compilation_rejected
#print axioms control5_per_field_cargo_invocation_binding_rejections
#print axioms n5_open_hash_ring_window_probe_and_refactor_verified
#print axioms n5_external_rlib_optimized_mir_vs_postcleanup_sidecar_discriminator

end AnnealResearch.CargoWorkspaceIntegrationControls
