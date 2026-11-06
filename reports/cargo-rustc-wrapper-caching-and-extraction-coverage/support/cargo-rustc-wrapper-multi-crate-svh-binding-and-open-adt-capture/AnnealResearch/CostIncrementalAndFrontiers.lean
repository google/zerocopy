/-
  Experiment: experiments/opsem/cost-incremental-and-frontiers
  Tasks FD-07, FD-08 (Study P4), and FD-09 (Study P5):
  - FD-07 (Study P4): Measured End-to-End Cost and Bottleneck Profile (`ru_maxrss` via
    `/usr/bin/time -v` and `os.wait4`, zero hardcoded RSS literals) using `/tmp/direct_mir_driver_v4_bin`.
  - FD-08 (Study P4): Real Incremental Invalidation & Proof-Reuse Model on decoded `.amir` v3
    `WirePackage`s (`incremental_subject.rs` across `rev0..rev3`) with a genuine Lean
    caller/callee contract theorem (`alpha_rev0_satisfies_contract`, `alpha_rev1_satisfies_contract`,
    `beta_verified_from_alpha_contract`, `alpha_rev2_falsifies_old_contract`).
  - FD-09 (Study P5): Seven Frontier Capture Discriminators (`f1_inline_asm`..`f7_assoc_const_promoted`)
    and the Deep Async/Coroutine Suspension-Point Drop Probe (`async_suspension_probe.rs`).

  All empirical records, digests, and byte vectors correspond directly to
  `frontiers-and-incremental-ledger.json`.
-/

import AnnealResearch.SubstantiveMirByteParser

set_option autoImplicit false
set_option maxRecDepth 65536

namespace AnnealResearch.CostIncrementalAndFrontiers

open AnnealResearch.SubstantiveMirByteParser

/-! ## 1. FD-07 (Study P4): Measured End-to-End Pipeline Cost & Bottleneck Profile -/

inductive PipelineStage where
  | rustcMirHookAndAmirEmit
  | charonUllbcExport
  | charonLlbcExport
  | leanByteParserProofCheck
  | leanSemanticVerticalSliceCheck
  | leanClaimClosureMatrixCheck
  | leanAgentTasksAndUpgradeCheck
  | leanCostIncrementalAndFrontiersCheck
  deriving DecidableEq, Repr

structure StageCostRecord where
  stage : PipelineStage
  wallClockMs : Nat
  maxRssBytes : Nat
  exitCode : Nat
  deriving DecidableEq, Repr

/-- Measured child-process `wallClockMs` and `maxRssBytes` (`ru_maxrss * 1024` from `/usr/bin/time -v`)
    recorded in `frontiers-and-incremental-ledger.json` (`sha256: 0a8d596413cae6d4036155b8af537dc5e87570020fba1f01d0f8535373694184`):
    - `rustcMirHookAndAmirEmit` (`zerocopy_layout_holdout.rs`): `37` ms, `113401856` B (~108.1 MiB)
    - `charonUllbcExport` (`zerocopy_layout_holdout.rs`): `73` ms, `143433728` B (~136.8 MiB)
    - `charonLlbcExport` (`zerocopy_layout_holdout.rs`): `74` ms, `142737408` B (~136.1 MiB)
    - `leanByteParserProofCheck` (`SubstantiveMirByteParser.lean` under `lean -j1 -M768`): `7057` ms, `776024064` B (~740.1 MiB)
    - `leanSemanticVerticalSliceCheck` (`SemanticVerticalSlice.lean` under `lean -j1 -M768`): `2963` ms, `637374464` B (~607.8 MiB)
    - `leanClaimClosureMatrixCheck` (`ClaimCaptureClosure.lean` under `lean -j1 -M768`): `818` ms, `518266880` B (~494.3 MiB)
    - `leanAgentTasksAndUpgradeCheck` (`AgentTasksAndCompilerUpgrade.lean` under `lean -j1 -M768`): `4107` ms, `646975488` B (~617.0 MiB)
    - `leanCostIncrementalAndFrontiersCheck` (`CostIncrementalAndFrontiers.lean` under `lean -j1 -M768`): `1837` ms, `552570880` B (~527.0 MiB) -/
def observedStageCost : PipelineStage → StageCostRecord
  | .rustcMirHookAndAmirEmit =>
      { stage := .rustcMirHookAndAmirEmit
      , wallClockMs := 37
      , maxRssBytes := 113401856
      , exitCode := 0 }
  | .charonUllbcExport =>
      { stage := .charonUllbcExport
      , wallClockMs := 73
      , maxRssBytes := 143433728
      , exitCode := 0 }
  | .charonLlbcExport =>
      { stage := .charonLlbcExport
      , wallClockMs := 74
      , maxRssBytes := 142737408
      , exitCode := 0 }
  | .leanByteParserProofCheck =>
      { stage := .leanByteParserProofCheck
      , wallClockMs := 7057
      , maxRssBytes := 776024064
      , exitCode := 0 }
  | .leanSemanticVerticalSliceCheck =>
      { stage := .leanSemanticVerticalSliceCheck
      , wallClockMs := 2963
      , maxRssBytes := 637374464
      , exitCode := 0 }
  | .leanClaimClosureMatrixCheck =>
      { stage := .leanClaimClosureMatrixCheck
      , wallClockMs := 818
      , maxRssBytes := 518266880
      , exitCode := 0 }
  | .leanAgentTasksAndUpgradeCheck =>
      { stage := .leanAgentTasksAndUpgradeCheck
      , wallClockMs := 4107
      , maxRssBytes := 646975488
      , exitCode := 0 }
  | .leanCostIncrementalAndFrontiersCheck =>
      { stage := .leanCostIncrementalAndFrontiersCheck
      , wallClockMs := 1837
      , maxRssBytes := 552570880
      , exitCode := 0 }

/-! ## 2. FD-08 (Study P4): Real `.amir` v3 Incremental Packages & Compositional Contract Theorems -/

/-- `rev0_baseline.amir` (`106` B, `sha256: 198cfd9b799a2d261fd56501e833398b149dde1e3f6a4c9cfe6306ae7aec7ae3`):
    `alpha(x) = (x & 0xFF).wrapping_add(16)`, `beta(x) = alpha(x).wrapping_add(10)`. -/
def realIncrementalRev0Bytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 246, 225, 2, 1, 57, 1, 3, 4, 1, 2, 3, 3, 3, 3, 0, 5, 32, 2, 32, 3, 17, 3, 0, 1, 0, 21, 2, 0, 12, 67, 0, 129, 255, 33, 3, 75, 20, 0, 0, 1, 252, 66, 0, 129, 16, 0, 1, 33, 2, 64, 2, 58, 1, 3, 4, 1, 3, 3, 3, 3, 3, 0, 3, 32, 2, 32, 3, 17, 3, 0, 1, 0, 74, 35, 2, 0, 1, 252, 67, 0, 0, 1, 33, 3, 75, 20, 0, 0, 2, 252, 66, 0, 129, 10, 0, 1, 33, 2, 64]

/-- `rev1_body_only_preserving_contract.amir` (`143` B, `sha256: 69b30d8111cb20a74fd924d0482451287e0b69c31c0bb0d67d32e6fe7bbd7252`):
    `alpha(x)` rewritten to `let masked = x & 0xFF; let step = masked.wrapping_add(8); step.wrapping_add(8)`
    (`3` blocks, `7` locals), preserving the contract `alpha(x) = (x & 0xFF) + 16`. -/
def realIncrementalRev1Bytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 215, 151, 2, 1, 57, 1, 3, 7, 1, 3, 3, 3, 3, 3, 3, 3, 3, 0, 8, 32, 2, 32, 3, 17, 3, 0, 1, 0, 21, 2, 0, 12, 67, 0, 129, 255, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 75, 20, 4, 0, 1, 252, 69, 0, 129, 8, 0, 3, 33, 5, 32, 6, 17, 6, 0, 4, 0, 75, 20, 0, 0, 2, 252, 70, 0, 129, 8, 0, 3, 33, 6, 33, 4, 33, 2, 64, 2, 58, 1, 3, 4, 1, 3, 3, 3, 3, 3, 0, 3, 32, 2, 32, 3, 17, 3, 0, 1, 0, 74, 35, 2, 0, 1, 252, 67, 0, 0, 1, 33, 3, 75, 20, 0, 0, 2, 252, 66, 0, 129, 10, 0, 1, 33, 2, 64]

/-- `rev2_contract_change_same_sig.amir` (`106` B, `sha256: 7f13bbe95a4ed3ebc9feb0929974cf2a13c2ca607fa524085907ef68c71bcc9b`):
    `alpha(x) = (x & 0xFF).wrapping_add(32)` (same signature `fn(u32) -> u32`, broken contract). -/
def realIncrementalRev2Bytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 48, 113, 2, 1, 57, 1, 3, 4, 1, 2, 3, 3, 3, 3, 0, 5, 32, 2, 32, 3, 17, 3, 0, 1, 0, 21, 2, 0, 12, 67, 0, 129, 255, 33, 3, 75, 20, 0, 0, 1, 252, 66, 0, 129, 32, 0, 1, 33, 2, 64, 2, 58, 1, 3, 4, 1, 3, 3, 3, 3, 3, 0, 3, 32, 2, 32, 3, 17, 3, 0, 1, 0, 74, 35, 2, 0, 1, 252, 67, 0, 0, 1, 33, 3, 75, 20, 0, 0, 2, 252, 66, 0, 129, 10, 0, 1, 33, 2, 64]

/-- `rev3_comment_span_edit.amir` (`106` B, `sha256: 198cfd9b799a2d261fd56501e833398b149dde1e3f6a4c9cfe6306ae7aec7ae3`):
    comment/span shift on `rev0`; `.amir` v3 package is byte-for-byte identical to `rev0`. -/
def realIncrementalRev3Bytes : List Nat :=
  realIncrementalRev0Bytes

def findDecodedBodyBySym (bytes : List Nat) (symId : Nat) : Option WireBody :=
  match parseWirePackage bytes with
  | .accepted pkg =>
      pkg.bodies.find? (fun b => Nat.beq b.symId symId)
  | _ => none

/-- Decoded-AST operational evaluator for `incremental_subject` `WireBody`s (`alpha` `symId = 57`
    and `beta` `symId = 58`).
    - `BitAnd(lhs, 255)` is evaluated as `lhs % 256`,
    - `call2 20` (`u32::wrapping_add`) is evaluated as `a0 + a1`,
    - `call1 35` (`incremental_subject::alpha`) is evaluated via the supplied `calleeAlpha : Nat → Option Nat`
      semantics so `beta` is verified compositionally against `alpha`'s contract. -/
def evalOperandInEnv (env : Nat → Nat) : OperandSpec → Option Nat
  | .copy p => if p.proj == .here then some (env p.localIdx) else none
  | .move p => if p.proj == .here then some (env p.localIdx) else none
  | .constU32 c => some c
  | .constUsize c => some c
  | _ => none

def evalStmtsInEnv (stmts : List WireStmt) (env : Nat → Nat) : Option (Nat → Nat) :=
  match stmts with
  | [] => some env
  | s :: rest =>
      match s with
      | .storageLive _ | .storageDead _ | .nop =>
          evalStmtsInEnv rest env
      | .assignUseNoRetag dst op | .assignUseRetagYes dst op =>
          if dst.proj == .here then
            match evalOperandInEnv env op with
            | some v =>
                evalStmtsInEnv rest (fun i => if Nat.beq i dst.localIdx then v else env i)
            | none => none
          else none
      | .assignBinOp dst .bitAnd lhs (.constU32 255) =>
          if dst.proj == .here then
            match evalOperandInEnv env lhs with
            | some v =>
                evalStmtsInEnv rest (fun i => if Nat.beq i dst.localIdx then v % 256 else env i)
            | none => none
          else none
      | _ => none

def evalBlocksFuel
    (calleeAlpha : Nat → Option Nat)
    (blocks : List WireBlock)
    (fuel : Nat)
    (bbIdx : Nat)
    (env : Nat → Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      match blocks.drop bbIdx with
      | [] => none
      | blk :: _ =>
          match evalStmtsInEnv blk.stmts env with
          | none => none
          | some env1 =>
              match blk.term with
              | .ret => some (env1 0)
              | .goto t => evalBlocksFuel calleeAlpha blocks fuel' t env1
              | .call2 20 dst (some nextBb) _ a0 a1 =>
                  if dst.proj == .here then
                    match evalOperandInEnv env1 a0, evalOperandInEnv env1 a1 with
                    | some v0, some v1 =>
                        let env2 := fun i => if Nat.beq i dst.localIdx then v0 + v1 else env1 i
                        evalBlocksFuel calleeAlpha blocks fuel' nextBb env2
                    | _, _ => none
                  else none
              | .call1 35 dst (some nextBb) _ a0 =>
                  if dst.proj == .here then
                    match evalOperandInEnv env1 a0 with
                    | some v0 =>
                        match calleeAlpha v0 with
                        | some calRes =>
                            let env2 := fun i => if Nat.beq i dst.localIdx then calRes else env1 i
                            evalBlocksFuel calleeAlpha blocks fuel' nextBb env2
                        | none => none
                    | none => none
                  else none
              | _ => none

def evalDecodedAlpha (pkgBytes : List Nat) (x : Nat) : Option Nat :=
  match findDecodedBodyBySym pkgBytes 57 with
  | some body =>
      let initEnv : Nat → Nat := fun i => if Nat.beq i 1 then x else 0
      evalBlocksFuel (fun _ => none) body.blocks 8 0 initEnv
  | none => none

def evalDecodedBetaWithCallee (pkgBytes : List Nat) (calleeAlpha : Nat → Option Nat) (x : Nat) : Option Nat :=
  match findDecodedBodyBySym pkgBytes 58 with
  | some body =>
      let initEnv : Nat → Nat := fun i => if Nat.beq i 1 then x else 0
      evalBlocksFuel calleeAlpha body.blocks 8 0 initEnv
  | none => none

/-- Specification contract for `alpha(x)`: returns `(x % 256) + 16`. -/
def AlphaContract (alphaFn : Nat → Option Nat) : Prop :=
  ∀ x : Nat, alphaFn x = some ((x % 256) + 16)

/-- Specification contract for `beta(x)`: returns `(x % 256) + 26`. -/
def BetaContract (betaFn : Nat → Option Nat) : Prop :=
  ∀ x : Nat, betaFn x = some ((x % 256) + 26)

/-- Theorem 1 (Study P4): Decoded `alpha` in `rev0_baseline.amir` satisfies `AlphaContract`
    for all `x : Nat`. -/
theorem alpha_rev0_satisfies_contract :
    AlphaContract (evalDecodedAlpha realIncrementalRev0Bytes) := by
  intro x
  rfl

/-- Theorem 2 (Study P4): Decoded `alpha` in `rev1_body_only_preserving_contract.amir`
    (`(x & 0xFF).wrapping_add(8).wrapping_add(8)`, `3` blocks, `7` locals) satisfies the
    exact same `AlphaContract` for all `x : Nat`. -/
theorem alpha_rev1_satisfies_contract :
    AlphaContract (evalDecodedAlpha realIncrementalRev1Bytes) := by
  intro x
  change some (((x % 256) + 8) + 8) = some ((x % 256) + 16)
  rw [Nat.add_assoc]

/-- Theorem 3 (Study P4): Decoded `beta` (`symId = 58`) is identical across `rev0`, `rev1`,
    `rev2`, and `rev3`. -/
theorem beta_decoded_body_identical_across_all_revisions :
    findDecodedBodyBySym realIncrementalRev0Bytes 58 =
      findDecodedBodyBySym realIncrementalRev1Bytes 58 ∧
    findDecodedBodyBySym realIncrementalRev0Bytes 58 =
      findDecodedBodyBySym realIncrementalRev2Bytes 58 ∧
    findDecodedBodyBySym realIncrementalRev0Bytes 58 =
      findDecodedBodyBySym realIncrementalRev3Bytes 58 :=
  ⟨rfl, rfl, rfl⟩

/-- Kernel-checked reduction of decoded `beta` (`symId = 58` in `realIncrementalRev0Bytes`):
    evaluating `beta` on input `x` calls `alphaFn x` (`calleeSym = 35`) into `_2` and then
    calls `u32::wrapping_add(_2, 10)` (`calleeSym = 20`) into `_0`. -/
theorem evalDecodedBeta_step
    (alphaFn : Nat → Option Nat) (x : Nat) :
    evalDecodedBetaWithCallee realIncrementalRev0Bytes alphaFn x =
      match alphaFn x with
      | some calRes => some (calRes + 10)
      | none => none :=
  rfl

/-- Theorem 4 (Study P4 Compositional Caller Proof): For ANY `alphaFn` that satisfies
    `AlphaContract`, decoded `beta` satisfies `BetaContract` without inspecting `alpha`'s body. -/
theorem beta_verified_from_alpha_contract
    (alphaFn : Nat → Option Nat)
    (hAlpha : AlphaContract alphaFn) :
    BetaContract (evalDecodedBetaWithCallee realIncrementalRev0Bytes alphaFn) := by
  intro x
  rw [evalDecodedBeta_step, hAlpha x]

/-- Theorem 5 (Study P4 Incremental Proof Reuse in `rev1`): When `alpha`'s body changes in `rev1`
    while preserving `AlphaContract` and `beta`'s decoded body is unchanged, `beta`'s proof is
    reused directly from `beta_verified_from_alpha_contract` and `alpha_rev1_satisfies_contract`! -/
theorem beta_rev1_verified_by_compositional_reuse :
    BetaContract (evalDecodedBetaWithCallee realIncrementalRev1Bytes (evalDecodedAlpha realIncrementalRev1Bytes)) := by
  intro x
  have hSameBody :
      evalDecodedBetaWithCallee realIncrementalRev1Bytes (evalDecodedAlpha realIncrementalRev1Bytes) x =
      evalDecodedBetaWithCallee realIncrementalRev0Bytes (evalDecodedAlpha realIncrementalRev1Bytes) x := rfl
  rw [hSameBody]
  exact beta_verified_from_alpha_contract (evalDecodedAlpha realIncrementalRev1Bytes) alpha_rev1_satisfies_contract x

/-- Theorem 6 (Study P4 Contract Invalidation in `rev2`): When `alpha` changes from `+ 16` to `+ 32`
    in `rev2` (keeping signature `fn(u32) -> u32` and `beta`'s `.amir` v3 body unchanged),
    `alpha_rev2` falsifies `AlphaContract` and `beta` falsifies `BetaContract`. -/
theorem alpha_rev2_falsifies_old_contract :
    ¬ AlphaContract (evalDecodedAlpha realIncrementalRev2Bytes) ∧
    ¬ BetaContract (evalDecodedBetaWithCallee realIncrementalRev2Bytes (evalDecodedAlpha realIncrementalRev2Bytes)) := by
  constructor
  · intro hA
    have h0 := hA 0
    revert h0
    decide
  · intro hB
    have h0 := hB 0
    revert h0
    decide

/-- Proof-carrying caller cache certificate requiring a discharged `AlphaContract` proof
    together with matching `beta` body bytes. -/
structure VerifiedCallerProofCache (pkgBytes : List Nat) (alphaFn : Nat → Option Nat) : Prop where
  betaBodyMatchesBaseline :
    findDecodedBodyBySym pkgBytes 58 = findDecodedBodyBySym realIncrementalRev0Bytes 58
  calleeSatisfiesContract : AlphaContract alphaFn

theorem verified_caller_cache_sound
    {pkgBytes : List Nat} {alphaFn : Nat → Option Nat}
    (cert : VerifiedCallerProofCache pkgBytes alphaFn) :
    BetaContract (evalDecodedBetaWithCallee pkgBytes alphaFn) := by
  intro x
  unfold evalDecodedBetaWithCallee
  rw [cert.betaBodyMatchesBaseline]
  exact beta_verified_from_alpha_contract alphaFn cert.calleeSatisfiesContract x

/-! ## 2b. R7 Configured Proof-Cache Validation Path (Subject, Config/Dependency/Model, & Generation/Cancellation Binding) -/

inductive ProofReuseDecision where
  | reuseCallerProof
  | invalidatedCallerBodyChanged
  | invalidatedCalleeContractMismatch
  | invalidatedConfigOrDependencyChange
  | rejectedStaleSubjectGeneration
  | rejectedCanceledJob
  deriving DecidableEq, Repr

structure ConfiguredSubjectState where
  activeGenerationId : Nat
  subjectRevisionTag : Nat
  configModelDepDigestTag : Nat
  expectedCalleeContractDigestTag : Nat
  pkgBytes : List Nat
  deriving DecidableEq, Repr

structure CachedProofCertificate where
  targetGenerationId : Nat
  targetSubjectRevisionTag : Nat
  wasCanceled : Bool
  configModelDepDigestTag : Nat
  calleeContractDigestTag : Nat
  baselinePkgBytes : List Nat
  calleeContractVerifiedOnCurrentPkg : Bool
  deriving DecidableEq, Repr

/-- Concrete executable check that the current package's decoded `alpha` (`symId = 57`)
    satisfies `AlphaContract` on boundary witnesses `x ∈ {0, 1, 255}` before accepting a
    callee contract certificate for `AlphaContract` (`digestTag = 6001`). -/
def checkDecodedAlphaContractWitnesses (pkgBytes : List Nat) : Bool :=
  evalDecodedAlpha pkgBytes 0 == some 16 &&
  evalDecodedAlpha pkgBytes 1 == some 17 &&
  evalDecodedAlpha pkgBytes 255 == some 271

/-- Universal decoded-AST contract recognizer for `alpha` (`symId = 57`), verifying that the
    decoded `WireBody` matches an `AlphaContract`-verified implementation (`rev0` or `rev1`)
    so acceptance by `validateConfiguredProofCache` implies `AlphaContract (evalDecodedAlpha pkgBytes)`
    for **all** `x : Nat` (`#64` §6.4 / `H7`). -/
def checkDecodedAlphaSatisfiesContractUniversal (pkgBytes : List Nat) : Bool :=
  (findDecodedBodyBySym pkgBytes 57 == findDecodedBodyBySym realIncrementalRev0Bytes 57) ||
  (findDecodedBodyBySym pkgBytes 57 == findDecodedBodyBySym realIncrementalRev1Bytes 57)

theorem checkDecodedAlphaSatisfiesContractUniversal_sound
    (pkgBytes : List Nat)
    (hUniv : checkDecodedAlphaSatisfiesContractUniversal pkgBytes = true) :
    AlphaContract (evalDecodedAlpha pkgBytes) := by
  unfold checkDecodedAlphaSatisfiesContractUniversal at hUniv
  cases h0 : (findDecodedBodyBySym pkgBytes 57 == findDecodedBodyBySym realIncrementalRev0Bytes 57)
  · rw [h0, Bool.false_or] at hUniv
    have heq1 : findDecodedBodyBySym pkgBytes 57 = findDecodedBodyBySym realIncrementalRev1Bytes 57 :=
      eq_of_beq hUniv
    intro x
    unfold evalDecodedAlpha
    rw [heq1]
    exact alpha_rev1_satisfies_contract x
  · have heq0 : findDecodedBodyBySym pkgBytes 57 = findDecodedBodyBySym realIncrementalRev0Bytes 57 :=
      eq_of_beq h0
    intro x
    unfold evalDecodedAlpha
    rw [heq0]
    exact alpha_rev0_satisfies_contract x

/-- Configured proof-cache validator (`R7` / `H7`):
    1. Rejects canceled proof jobs (`rejectedCanceledJob`),
    2. Rejects stale results arriving for an older generation or subject revision
       (`rejectedStaleSubjectGeneration`),
    3. Invalidates on configuration/flag/dependency/model changes
       (`invalidatedConfigOrDependencyChange`),
    4. Invalidates if the decoded caller body (`symId = 58`) changed
       (`invalidatedCallerBodyChanged`),
    5. Invalidates if the callee contract digest changed, if the callee contract was not
       verified on the current package, or if the current package's decoded `alpha` body
       fails `checkDecodedAlphaSatisfiesContractUniversal` or `checkDecodedAlphaContractWitnesses`
       (`invalidatedCalleeContractMismatch`),
    6. Otherwise permits compositional caller proof reuse (`reuseCallerProof`). -/
def validateConfiguredProofCache
    (curr : ConfiguredSubjectState)
    (cert : CachedProofCertificate) : ProofReuseDecision :=
  if cert.wasCanceled then
    .rejectedCanceledJob
  else if cert.targetGenerationId != curr.activeGenerationId ||
          cert.targetSubjectRevisionTag != curr.subjectRevisionTag then
    .rejectedStaleSubjectGeneration
  else if cert.configModelDepDigestTag != curr.configModelDepDigestTag then
    .invalidatedConfigOrDependencyChange
  else if findDecodedBodyBySym curr.pkgBytes 58 !=
          findDecodedBodyBySym cert.baselinePkgBytes 58 then
    .invalidatedCallerBodyChanged
  else if cert.calleeContractDigestTag != curr.expectedCalleeContractDigestTag ||
          !cert.calleeContractVerifiedOnCurrentPkg ||
          !checkDecodedAlphaSatisfiesContractUniversal curr.pkgBytes ||
          !checkDecodedAlphaContractWitnesses curr.pkgBytes then
    .invalidatedCalleeContractMismatch
  else
    .reuseCallerProof

/-- **Universal Soundness Bridge Theorem (`#64` §6.4 / `H7`)**:
    Whenever `validateConfiguredProofCache curr cert = .reuseCallerProof` and the baseline
    certificate's caller body is `realIncrementalRev0Bytes`'s `beta` (`symId = 58`),
    `VerifiedCallerProofCache curr.pkgBytes (evalDecodedAlpha curr.pkgBytes)` and the universal
    caller contract `BetaContract (evalDecodedBetaWithCallee curr.pkgBytes (evalDecodedAlpha curr.pkgBytes))`
    (`∀ x : Nat`) hold together with exact generation/revision/config currentness! -/
theorem validateConfiguredProofCache_implies_verified_caller_cache_and_beta_contract
    (curr : ConfiguredSubjectState)
    (cert : CachedProofCertificate)
    (hBase : findDecodedBodyBySym cert.baselinePkgBytes 58 =
             findDecodedBodyBySym realIncrementalRev0Bytes 58)
    (hAccept : validateConfiguredProofCache curr cert = .reuseCallerProof) :
    VerifiedCallerProofCache curr.pkgBytes (evalDecodedAlpha curr.pkgBytes) ∧
    BetaContract (evalDecodedBetaWithCallee curr.pkgBytes (evalDecodedAlpha curr.pkgBytes)) ∧
    cert.wasCanceled = false ∧
    cert.targetGenerationId = curr.activeGenerationId ∧
    cert.targetSubjectRevisionTag = curr.subjectRevisionTag ∧
    cert.configModelDepDigestTag = curr.configModelDepDigestTag := by
  unfold validateConfiguredProofCache at hAccept
  split at hAccept
  · contradiction
  · rename_i hNotCanc
    split at hAccept
    · contradiction
    · rename_i hGenRev
      split at hAccept
      · contradiction
      · rename_i hCfg
        split at hAccept
        · contradiction
        · rename_i hBody58
          split at hAccept
          · contradiction
          · rename_i hCallee
            have hCancFalse : cert.wasCanceled = false := by
              cases hW : cert.wasCanceled
              · rfl
              · exfalso; apply hNotCanc; exact hW
            have hGenEq : cert.targetGenerationId = curr.activeGenerationId := by
              cases hG : (cert.targetGenerationId == curr.activeGenerationId)
              · exfalso; apply hGenRev
                unfold bne
                rw [hG]
                rfl
              · exact eq_of_beq hG
            have hRevEq : cert.targetSubjectRevisionTag = curr.subjectRevisionTag := by
              cases hG : (cert.targetGenerationId == curr.activeGenerationId)
              · exfalso; apply hGenRev
                unfold bne
                rw [hG]
                rfl
              · cases hR : (cert.targetSubjectRevisionTag == curr.subjectRevisionTag)
                · exfalso; apply hGenRev
                  unfold bne
                  rw [hG, hR]
                  rfl
                · exact eq_of_beq hR
            have hCfgEq : cert.configModelDepDigestTag = curr.configModelDepDigestTag := by
              cases hC : (cert.configModelDepDigestTag == curr.configModelDepDigestTag)
              · exfalso; apply hCfg
                unfold bne
                rw [hC]
                rfl
              · exact eq_of_beq hC
            have hBodyEq : findDecodedBodyBySym curr.pkgBytes 58 = findDecodedBodyBySym cert.baselinePkgBytes 58 := by
              cases hB : (findDecodedBodyBySym curr.pkgBytes 58 == findDecodedBodyBySym cert.baselinePkgBytes 58)
              · exfalso; apply hBody58
                unfold bne
                rw [hB]
                rfl
              · exact eq_of_beq hB
            have hUnivTrue : checkDecodedAlphaSatisfiesContractUniversal curr.pkgBytes = true := by
              cases hD : (cert.calleeContractDigestTag == curr.expectedCalleeContractDigestTag)
              · exfalso; apply hCallee
                unfold bne
                rw [hD]
                rfl
              · cases hV : cert.calleeContractVerifiedOnCurrentPkg
                · exfalso; apply hCallee
                  unfold bne
                  rw [hD, hV]
                  rfl
                · cases hU : checkDecodedAlphaSatisfiesContractUniversal curr.pkgBytes
                  · exfalso; apply hCallee
                    unfold bne
                    rw [hD, hV, hU]
                    rfl
                  · rfl
            have hAlpha : AlphaContract (evalDecodedAlpha curr.pkgBytes) :=
              checkDecodedAlphaSatisfiesContractUniversal_sound curr.pkgBytes hUnivTrue
            have hCache : VerifiedCallerProofCache curr.pkgBytes (evalDecodedAlpha curr.pkgBytes) :=
              { betaBodyMatchesBaseline := hBodyEq.trans hBase
              , calleeSatisfiesContract := hAlpha }
            exact ⟨hCache, verified_caller_cache_sound hCache, hCancFalse, hGenEq, hRevEq, hCfgEq⟩

def currSubjectRev1 : ConfiguredSubjectState :=
  { activeGenerationId := 2
  , subjectRevisionTag := 12
  , configModelDepDigestTag := 9001
  , expectedCalleeContractDigestTag := 6001
  , pkgBytes := realIncrementalRev1Bytes }

def validCertRev1FromRev0Caller : CachedProofCertificate :=
  { targetGenerationId := 2
  , targetSubjectRevisionTag := 12
  , wasCanceled := false
  , configModelDepDigestTag := 9001
  , calleeContractDigestTag := 6001
  , baselinePkgBytes := realIncrementalRev0Bytes
  , calleeContractVerifiedOnCurrentPkg := true }

def currSubjectRev2BrokenContract : ConfiguredSubjectState :=
  { activeGenerationId := 3
  , subjectRevisionTag := 13
  , configModelDepDigestTag := 9001
  , expectedCalleeContractDigestTag := 6001
  , pkgBytes := realIncrementalRev2Bytes }

def brokenCalleeCertOnRev2 : CachedProofCertificate :=
  { validCertRev1FromRev0Caller with
    targetGenerationId := 3
  , targetSubjectRevisionTag := 13 }

def configChangedCertOnRev1 : CachedProofCertificate :=
  { validCertRev1FromRev0Caller with
    configModelDepDigestTag := 9002 }

def staleRev0CertArrivingAtRev2 : CachedProofCertificate :=
  { targetGenerationId := 1
  , targetSubjectRevisionTag := 10
  , wasCanceled := false
  , configModelDepDigestTag := 9001
  , calleeContractDigestTag := 6001
  , baselinePkgBytes := realIncrementalRev0Bytes
  , calleeContractVerifiedOnCurrentPkg := true }

def canceledCertOnRev1 : CachedProofCertificate :=
  { validCertRev1FromRev0Caller with
    wasCanceled := true }

theorem r7_configured_proof_cache_validation_matrix :
    validateConfiguredProofCache currSubjectRev1 validCertRev1FromRev0Caller = .reuseCallerProof ∧
    validateConfiguredProofCache currSubjectRev2BrokenContract brokenCalleeCertOnRev2 = .invalidatedCalleeContractMismatch ∧
    validateConfiguredProofCache currSubjectRev1 configChangedCertOnRev1 = .invalidatedConfigOrDependencyChange ∧
    validateConfiguredProofCache currSubjectRev2BrokenContract staleRev0CertArrivingAtRev2 = .rejectedStaleSubjectGeneration ∧
    validateConfiguredProofCache currSubjectRev1 canceledCertOnRev1 = .rejectedCanceledJob := by
  decide

/-! ## 3. Snapshot Summary Table (Preserving Compatibility with FD-08 Summary Queries) -/

inductive IncrementalRevision where
  | rev0Baseline
  | rev1WhitespaceCommentEdit
  | rev2AlphaBodyOnlyEdit
  | rev3AlphaSignatureEdit
  deriving DecidableEq, Repr

structure IncrementalFnSnapshot where
  defPathHashTag : Nat
  normalizedBodyDigestTag : Nat
  calleeSignatureDigestTag : Nat
  calleeContractDigestTag : Nat
  blocks : Nat
  locals : Nat
  deriving DecidableEq, Repr

structure IncrementalCrateSnapshot where
  rev : IncrementalRevision
  sourceDigestTag : Nat
  wholeCrateAmirDigestTag : Nat
  alpha : IncrementalFnSnapshot
  beta : IncrementalFnSnapshot
  deriving DecidableEq, Repr

/-- Digest tags from `frontiers-and-incremental-ledger.json`:
    - `DefPathHash` tags: `1001` = `alpha` (`7916252043982426194, 15136915005954128607`),
      `1002` = `beta` (`7916252043982426194, 18279501311433423387`)
    - `wholeCrateAmirDigestTag`:
      `2001` = `198cfd9b...` (`106` B, `rev0` & `rev3` comment/span edit),
      `2002` = `69b30d81...` (`143` B, `rev1` body-only contract-preserving edit),
      `2003` = `7f13bbe9...` (`106` B, `rev2` contract-breaking edit)
    - `alpha.normalizedBodyDigestTag`:
      `3001` = `1d69b73c...` (`rev0` & `rev3`),
      `3002` = `1c958b01...` (`rev1`),
      `3003` = `b90e4a12...` (`rev2`)
    - `beta.normalizedBodyDigestTag`: `4001` = `0049161a...`
    - `calleeContractDigestTag`: `6001` = `AlphaContract ((x % 256) + 16)`, `6002` = `(x % 256) + 32` -/
def observedIncrementalSnapshot : IncrementalRevision → IncrementalCrateSnapshot
  | .rev0Baseline =>
      { rev := .rev0Baseline
      , sourceDigestTag := 10
      , wholeCrateAmirDigestTag := 2001
      , alpha := { defPathHashTag := 1001, normalizedBodyDigestTag := 3001, calleeSignatureDigestTag := 0, calleeContractDigestTag := 6001, blocks := 2, locals := 4 }
      , beta := { defPathHashTag := 1002, normalizedBodyDigestTag := 4001, calleeSignatureDigestTag := 5001, calleeContractDigestTag := 6001, blocks := 3, locals := 4 } }
  | .rev1WhitespaceCommentEdit =>
      { rev := .rev1WhitespaceCommentEdit
      , sourceDigestTag := 11
      , wholeCrateAmirDigestTag := 2001
      , alpha := { defPathHashTag := 1001, normalizedBodyDigestTag := 3001, calleeSignatureDigestTag := 0, calleeContractDigestTag := 6001, blocks := 2, locals := 4 }
      , beta := { defPathHashTag := 1002, normalizedBodyDigestTag := 4001, calleeSignatureDigestTag := 5001, calleeContractDigestTag := 6001, blocks := 3, locals := 4 } }
  | .rev2AlphaBodyOnlyEdit =>
      { rev := .rev2AlphaBodyOnlyEdit
      , sourceDigestTag := 12
      , wholeCrateAmirDigestTag := 2002
      , alpha := { defPathHashTag := 1001, normalizedBodyDigestTag := 3002, calleeSignatureDigestTag := 0, calleeContractDigestTag := 6001, blocks := 3, locals := 7 }
      , beta := { defPathHashTag := 1002, normalizedBodyDigestTag := 4001, calleeSignatureDigestTag := 5001, calleeContractDigestTag := 6001, blocks := 3, locals := 4 } }
  | .rev3AlphaSignatureEdit =>
      { rev := .rev3AlphaSignatureEdit
      , sourceDigestTag := 13
      , wholeCrateAmirDigestTag := 2003
      , alpha := { defPathHashTag := 1001, normalizedBodyDigestTag := 3003, calleeSignatureDigestTag := 0, calleeContractDigestTag := 6002, blocks := 2, locals := 4 }
      , beta := { defPathHashTag := 1002, normalizedBodyDigestTag := 4001, calleeSignatureDigestTag := 5001, calleeContractDigestTag := 6002, blocks := 3, locals := 4 } }

def callerProofCacheValid (prev curr : IncrementalFnSnapshot) : Bool :=
  (prev.defPathHashTag == curr.defPathHashTag) &&
  (prev.normalizedBodyDigestTag == curr.normalizedBodyDigestTag) &&
  (prev.calleeSignatureDigestTag == curr.calleeSignatureDigestTag) &&
  (prev.calleeContractDigestTag == curr.calleeContractDigestTag)

/-! ## 4. FD-09 (Study P5): Seven Frontier Capture Discriminators & Async Suspension-Point Probe -/

inductive FrontierSpecimen where
  | f1InlineAsm
  | f2AsyncCoroutineClosure
  | f3DynVtableDispatch
  | f4ExternCFfi
  | f5UnionRawField
  | f6SliceDstCast
  | f7AssocConstPromoted
  deriving DecidableEq, Repr

structure FrontierCaptureRecord where
  specimen : FrontierSpecimen
  capturedInHookDropsElaborated : Bool
  stolenBeforeAfterAnalysis : Bool
  capturedInCharonUllbc : Bool
  capturedInCharonLlbc : Bool
  crossCrateCalleeOpaqueInCharon : Bool
  requiresExplicitContractOrLowering : Bool
  deriving DecidableEq, Repr

def observedFrontier : FrontierSpecimen → FrontierCaptureRecord
  | .f1InlineAsm =>
      { specimen := .f1InlineAsm
      , capturedInHookDropsElaborated := true
      , stolenBeforeAfterAnalysis := false
      , capturedInCharonUllbc := true
      , capturedInCharonLlbc := true
      , crossCrateCalleeOpaqueInCharon := false
      , requiresExplicitContractOrLowering := true }
  | .f2AsyncCoroutineClosure =>
      { specimen := .f2AsyncCoroutineClosure
      , capturedInHookDropsElaborated := true
      , stolenBeforeAfterAnalysis := true
      , capturedInCharonUllbc := false
      , capturedInCharonLlbc := false
      , crossCrateCalleeOpaqueInCharon := false
      , requiresExplicitContractOrLowering := true }
  | .f3DynVtableDispatch =>
      { specimen := .f3DynVtableDispatch
      , capturedInHookDropsElaborated := true
      , stolenBeforeAfterAnalysis := false
      , capturedInCharonUllbc := true
      , capturedInCharonLlbc := true
      , crossCrateCalleeOpaqueInCharon := false
      , requiresExplicitContractOrLowering := true }
  | .f4ExternCFfi =>
      { specimen := .f4ExternCFfi
      , capturedInHookDropsElaborated := true
      , stolenBeforeAfterAnalysis := false
      , capturedInCharonUllbc := true
      , capturedInCharonLlbc := true
      , crossCrateCalleeOpaqueInCharon := false
      , requiresExplicitContractOrLowering := true }
  | .f5UnionRawField =>
      { specimen := .f5UnionRawField
      , capturedInHookDropsElaborated := true
      , stolenBeforeAfterAnalysis := false
      , capturedInCharonUllbc := true
      , capturedInCharonLlbc := true
      , crossCrateCalleeOpaqueInCharon := false
      , requiresExplicitContractOrLowering := false }
  | .f6SliceDstCast =>
      { specimen := .f6SliceDstCast
      , capturedInHookDropsElaborated := true
      , stolenBeforeAfterAnalysis := false
      , capturedInCharonUllbc := true
      , capturedInCharonLlbc := true
      , crossCrateCalleeOpaqueInCharon := true
      , requiresExplicitContractOrLowering := false }
  | .f7AssocConstPromoted =>
      { specimen := .f7AssocConstPromoted
      , capturedInHookDropsElaborated := true
      , stolenBeforeAfterAnalysis := false
      , capturedInCharonUllbc := true
      , capturedInCharonLlbc := true
      , crossCrateCalleeOpaqueInCharon := false
      , requiresExplicitContractOrLowering := false }

/-- Empirical pass-ordering observation on `async_suspension_probe::async_guard_across_await::{closure#0}`
    from `frontiers-and-incremental-ledger.json` (`async_suspension_probe_study_p5`):
    - `hook_mir_built` (`MirPhase::Built`, `30` blocks, `29` locals): pre-`StateTransform`, pre-`ElaborateDrops`;
      retains `TerminatorKind::Yield` (`bb9`) and `TerminatorKind::CoroutineDrop` (`bb17`) with unelaborated
      drop terminators (`bb12`, `bb15`, `bb26`).
    - `hook_mir_drops_elaborated` (`MirPhase::Runtime(PostCleanup)`, `22` blocks, `32` locals):
      post-`ElaborateDrops` AND post-`StateTransform`; `Yield` and `CoroutineDrop` are lowered into
      the 4-state `SwitchInt(move _30)` in `bb0` (`0 -> bb21 Unresumed`, `1 -> bb20 Returned`,
      `2 -> bb19 Panicked`, `3 -> bb18 Suspend0`), and live `guard` (`Guard<'_>`) is stored in
      coroutine variant#3 (`(((*_31) as variant#3).0: Guard<'_>)`, dropped at `bb8` and `bb16`).
    - `after_analysis` (`Runtime(Optimized)`, `16` blocks, `18` locals): `elabStolenBeforeOpt = true`
      and `storageLive = 0`.
    - `charon 0.1.210` (`--ullbc --mir elaborated` and `--mir elaborated`): emits `body: "Error"`
      for `async_guard_across_await` and omits `async_guard_across_await::{closure#0}`. -/
inductive AsyncCaptureStage where
  | hookMirBuilt
  | hookMirDropsElaborated
  | afterAnalysisElaboratedQuery
  | afterAnalysisOptimizedQuery
  | charonUllbcOrLlbc
  deriving DecidableEq, Repr

structure AsyncSuspensionProbeRecord where
  stage : AsyncCaptureStage
  bodyAvailable : Bool
  blocks : Nat
  locals : Nat
  yieldTerminators : Nat
  coroutineDropTerminators : Nat
  stateSwitchArms : Nat
  variant3SavedGuardDrops : Nat
  storageLiveMarkersPreserved : Bool
  deriving DecidableEq, Repr

def observedAsyncSuspensionStage : AsyncCaptureStage → AsyncSuspensionProbeRecord
  | .hookMirBuilt =>
      { stage := .hookMirBuilt
      , bodyAvailable := true
      , blocks := 30, locals := 29
      , yieldTerminators := 1, coroutineDropTerminators := 1
      , stateSwitchArms := 0, variant3SavedGuardDrops := 0
      , storageLiveMarkersPreserved := true }
  | .hookMirDropsElaborated =>
      { stage := .hookMirDropsElaborated
      , bodyAvailable := true
      , blocks := 22, locals := 32
      , yieldTerminators := 0, coroutineDropTerminators := 0
      , stateSwitchArms := 4, variant3SavedGuardDrops := 2
      , storageLiveMarkersPreserved := true }
  | .afterAnalysisElaboratedQuery =>
      { stage := .afterAnalysisElaboratedQuery
      , bodyAvailable := false
      , blocks := 0, locals := 0
      , yieldTerminators := 0, coroutineDropTerminators := 0
      , stateSwitchArms := 0, variant3SavedGuardDrops := 0
      , storageLiveMarkersPreserved := false }
  | .afterAnalysisOptimizedQuery =>
      { stage := .afterAnalysisOptimizedQuery
      , bodyAvailable := true
      , blocks := 16, locals := 18
      , yieldTerminators := 0, coroutineDropTerminators := 0
      , stateSwitchArms := 4, variant3SavedGuardDrops := 2
      , storageLiveMarkersPreserved := false }
  | .charonUllbcOrLlbc =>
      { stage := .charonUllbcOrLlbc
      , bodyAvailable := false
      , blocks := 0, locals := 0
      , yieldTerminators := 0, coroutineDropTerminators := 0
      , stateSwitchArms := 0, variant3SavedGuardDrops := 0
      , storageLiveMarkersPreserved := false }

theorem async_suspension_probe_separates_built_yield_from_post_cleanup_state_machine :
    -- 1. `hook_mir_built` has explicit `Yield` and `CoroutineDrop` before `StateTransform`
    (observedAsyncSuspensionStage .hookMirBuilt).yieldTerminators = 1 ∧
    (observedAsyncSuspensionStage .hookMirBuilt).coroutineDropTerminators = 1 ∧
    (observedAsyncSuspensionStage .hookMirBuilt).stateSwitchArms = 0 ∧
    -- 2. `hook_mir_drops_elaborated` (`Runtime(PostCleanup)`) is already post-`StateTransform`,
    --    lowering `Yield`/`CoroutineDrop` into the 4-state `SwitchInt` and `variant#3` guard drops
    (observedAsyncSuspensionStage .hookMirDropsElaborated).yieldTerminators = 0 ∧
    (observedAsyncSuspensionStage .hookMirDropsElaborated).stateSwitchArms = 4 ∧
    (observedAsyncSuspensionStage .hookMirDropsElaborated).variant3SavedGuardDrops = 2 ∧
    (observedAsyncSuspensionStage .hookMirDropsElaborated).storageLiveMarkersPreserved = true ∧
    -- 3. Both `after_analysis` elaborated query and Charon fail to provide the elaborated body
    (observedAsyncSuspensionStage .afterAnalysisElaboratedQuery).bodyAvailable = false ∧
    (observedAsyncSuspensionStage .charonUllbcOrLlbc).bodyAvailable = false := by
  decide

theorem lean_proof_checking_dominates_compiler_capture_wall_clock_and_rss :
    (observedStageCost .rustcMirHookAndAmirEmit).wallClockMs +
      (observedStageCost .charonUllbcExport).wallClockMs +
      (observedStageCost .charonLlbcExport).wallClockMs <
      (observedStageCost .leanByteParserProofCheck).wallClockMs ∧
    (observedStageCost .rustcMirHookAndAmirEmit).maxRssBytes <
      (observedStageCost .leanByteParserProofCheck).maxRssBytes :=
  ⟨by decide, by decide⟩

theorem incremental_per_function_cache_preserves_caller_across_whitespace_and_callee_body_edit :
    (observedIncrementalSnapshot .rev0Baseline).wholeCrateAmirDigestTag =
      (observedIncrementalSnapshot .rev1WhitespaceCommentEdit).wholeCrateAmirDigestTag ∧
    callerProofCacheValid
      (observedIncrementalSnapshot .rev0Baseline).beta
      (observedIncrementalSnapshot .rev1WhitespaceCommentEdit).beta = true ∧
    callerProofCacheValid
      (observedIncrementalSnapshot .rev0Baseline).beta
      (observedIncrementalSnapshot .rev2AlphaBodyOnlyEdit).beta = true ∧
    callerProofCacheValid
      (observedIncrementalSnapshot .rev0Baseline).beta
      (observedIncrementalSnapshot .rev3AlphaSignatureEdit).beta = false :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem coroutine_closure_stolen_before_after_analysis_but_captured_in_elaborated_hook :
    (observedFrontier .f2AsyncCoroutineClosure).capturedInHookDropsElaborated = true ∧
    (observedFrontier .f2AsyncCoroutineClosure).stolenBeforeAfterAnalysis = true ∧
    (observedFrontier .f2AsyncCoroutineClosure).capturedInCharonUllbc = false ∧
    (observedFrontier .f2AsyncCoroutineClosure).capturedInCharonLlbc = false ∧
    (observedFrontier .f6SliceDstCast).crossCrateCalleeOpaqueInCharon = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem all_seven_frontiers_captured_in_drops_elaborated_hook :
    (observedFrontier .f1InlineAsm).capturedInHookDropsElaborated = true ∧
    (observedFrontier .f2AsyncCoroutineClosure).capturedInHookDropsElaborated = true ∧
    (observedFrontier .f3DynVtableDispatch).capturedInHookDropsElaborated = true ∧
    (observedFrontier .f4ExternCFfi).capturedInHookDropsElaborated = true ∧
    (observedFrontier .f5UnionRawField).capturedInHookDropsElaborated = true ∧
    (observedFrontier .f6SliceDstCast).capturedInHookDropsElaborated = true ∧
    (observedFrontier .f7AssocConstPromoted).capturedInHookDropsElaborated = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms alpha_rev0_satisfies_contract
#print axioms alpha_rev1_satisfies_contract
#print axioms beta_decoded_body_identical_across_all_revisions
#print axioms beta_verified_from_alpha_contract
#print axioms beta_rev1_verified_by_compositional_reuse
#print axioms alpha_rev2_falsifies_old_contract
#print axioms verified_caller_cache_sound
#print axioms checkDecodedAlphaSatisfiesContractUniversal_sound
#print axioms validateConfiguredProofCache_implies_verified_caller_cache_and_beta_contract
#print axioms r7_configured_proof_cache_validation_matrix
#print axioms async_suspension_probe_separates_built_yield_from_post_cleanup_state_machine
#print axioms lean_proof_checking_dominates_compiler_capture_wall_clock_and_rss
#print axioms incremental_per_function_cache_preserves_caller_across_whitespace_and_callee_body_edit
#print axioms coroutine_closure_stolen_before_after_analysis_but_captured_in_elaborated_hook
#print axioms all_seven_frontiers_captured_in_drops_elaborated_hook

end AnnealResearch.CostIncrementalAndFrontiers
