# Verification Claim Anti-Circularity, Certificate Reuse Gates, and Multi-Toolchain Compiler Upgrade Assurance

## Summary

A formal verification system that allows an automated agent or developer to edit both the implementation and the specification/proof script faces a fundamental assurance hazard: **green-build claim weakening**, where a proof succeeds only because the theorem statement, precondition domain, observation projection, or compiler extraction flags were silently weakened. Across 30 machine-checked Lean 4 modules and empirical trials spanning 4 nightly Rust toolchains (`1.95.0-nightly` through `1.98.0-nightly`) and 2 Charon releases (`0.1.174` and `0.1.210`), we establish eight orthogonal assurance gates:

1. **Non-vacuous specification challenge and discriminative strengthening (`SpecValidation.lean`, `SpecChallengeResolution.lean`)**: Weak postconditions that check only final root images admit both rollback-omitting (`commitOnlyOnOk`) and alias-clobbering (`overwriteInPlace`) mutants (`weak_contract_admits_all_three_candidates`). Only a joint contract enforcing active-value preservation on error and closed-alias frame preservation across both normal and error paths discriminates the exact defect of each mutant while remaining non-vacuous on admitted heap states (`strong_contract_discriminates_exact_reasons`, `vacuous_domain_control`).
2. **Semantic claim-change detection over structured claim records (`ClaimChangeResolution.lean`, `ClaimChangeResolutionControls.lean`)**: Comparing verification revisions via syntax similarity, theorem counts, or self-referential exporter flags is unsound (`self_oracle_circularity_control`, `syntax_similarity_control`). A sound claim-change classifier decomposes each claim into `(subjectId, domainPred, obsMap, postRel, execCoverage)` and requires a kernel-checked equivalence proof before reporting `"unchanged"`, classifying any unproved predicate edit as `"unknown"` and any single-field weakening (such as universal-to-existential trace coverage) as `"weakened"` (`single_field_weakening_rejects_preservation`, `universal_to_single_execution_admits_unsafe_machine`).
3. **Prefix-conformance vs. completed-trace conformance in design-model transfer (`DesignModelTransfer.lean`, `DesignModelControls.lean`)**: Checking that an implementation matches a high-level design model only on completed terminal states fails to transfer `NoUB` when an implementation faults or diverges on an intermediate prefix (`completed_conformance_fails_to_transfer_noUB`, `fault_before_divergence_counterexample`). Transferring `NoUB` from a design model requires step-wise prefix simulation (`prefix_conformance_transfers_noUB`).
4. **Frozen-claim optimization preservation (`OptimizationPreservation.lean`, `OptimizationControls.lean`)**: Evaluating an optimization pass requires separating logical cost reduction (`fusedValidOpt_strictly_reduces_logical_cost`) from frozen-claim satisfaction (`fusedValidOpt_satisfies_frozen_claim`), rejecting candidates that match return values and `NoUB` while clobbering out-of-frame memory (`footprintClobber_rejected_by_frozen_claim`), leaking secret branches (`secretBranch_rejected_by_frozen_claim`), or introducing late-prefix UB (`latePrefixUb_rejected_by_frozen_claim`).
5. **Typed certificate reuse and Rust compilation-unit binding (`FactReuseValidation.lean`, `FactReuseControls.lean`, `IntegrationBinding.lean`, `IntegrationBindingControls.lean`)**: Compositional reuse of layout, validity (`validBoolByte`), and callee safety certificates is sound across implementation swaps and incidental local-index renumberings (`fresh_and_reused_endpoints_equivalent`, `incidental_renumbering_preserves_essential_admission`), but must fail closed when `#[cfg]` flags (`cfg_alt_impl`, `cfg_variant_b`), monomorphization instances, or caller preconditions change (`config_or_instance_change_invalidates_codec_cert`, `premise_strengthening_invalidates_caller_reuse`).
6. **Claim-pinned agent repair evaluation (`AgentTaskEvaluation.lean`, `AgentTaskControls.lean`, `AgentTasksAndCompilerUpgrade.lean`, `AgentTasksAndUpgradeControls.lean`)**: In bounded agent repair tasks (such as localizing a seeded `DstLayout::extend` alignment-choice bug in basic block `bb12` via `mir_built` `var_debug_info` joins), unpinned checkers and theorem-count metrics reward contract-weakening traps (`tempting_contract_weakening_passes_unpinned_checker`, `theorem_count_metric_rewards_inflated_weak_submission`), whereas pinning the original `C0` oracle rejects all three weakening traps (`task4_all_three_weakening_traps_rejected`): postcondition weakening (Trap A), dropping `-Z mir-preserve-ub` (Trap B), and routing unwind obligations through unverified LLBC (Trap C).
7. **Explicit execution outcome classification vs. status-erasing `Option` projections (`IndependentSliceHoldoutH11.lean`)**: On an independent slice-window validation holdout (`validate_slice_window`, `guarded_window_commit`), projecting operational execution outcomes to `Option (Option Nat)` conflates normal `Option::None` returns with infinite loops (`.fuelExhausted`) and stuck/malformed returns (`.malformedOrStuck`), whereas the 8-way `SliceWindowExecOutcome` sum type rejects both mutants and localizes the exact single-byte `Lt` (`0x03`) vs. `Le` (`0x04`) boundary bug at `.amir` offset `403` (`bb7` statement 10) (`control_n4_status_erasing_projection_accepts_faulting_and_nonterminating_none_mutants_while_explicit_outcome_rejects`, `independent_holdout_buggy_bb7_localized_lt_vs_le`).
8. **Multi-toolchain compiler upgrade maintenance (`1.95.0-nightly` $\to$ `1.98.0-nightly`) vs. Charon / `rustc_public`**: Across four nightly Rust toolchains, a single portable `rustc_driver` ([`support/direct_mir_driver_portable.rs`](support/direct_mir_driver_portable.rs)) bridges all internal `rustc_middle` API changes in 5 `#[cfg]` blocks (36 conditional LOC; 21 net adapter lines), including the `1.97` $\to$ `1.98` folding of `StatementKind::Retag` (`0x31`) into `Rvalue::Use(_, WithRetag)` (`0x10`/`0x11`), proven semantically equivalent in `retag_stmt_0x31_after_use_no_retag_0x10_equiv_folded_use_retag_yes_0x11`. Over the same window, Charon `0.1.174` $\to$ `0.1.210` required 5 upstream `rustc`-bump commits touching 37 `charon-driver` files (`+9,026 / -1,827` lines), and `rustc_public` broke across the `1.97` $\to$ `1.98` `WithRetag` transition (`rustc_public_did_not_insulate_against_1_98_with_retag_breakage`).

## Applicability

These findings apply to machine-checked Rust verification pipelines, automated proof-repair agents, and compiler-frontend adapters:

- **Rust Toolchains Evaluated**:
  - `1.95.0-nightly (efc9e1b50 2026-02-06)` (`rustc` SHA-256 `695da1df6ac1e5c463770020c78b218680c1588bfe3c00eff7a3c251f274a0b2`)
  - `1.96.0-nightly (02c7f9bec 2026-04-10)` (`rustc` SHA-256 `246056779cdc44dff63aa9a0c249bf5c3e1dc90262e27f7bed12f8d1966eeb8f`)
  - `1.97.0-nightly (bf4fbfb7a 2026-04-11)` (`rustc` SHA-256 `d016bff4364bfd554a6d94aa269f3e5e6a9b65e1bd461a3567e7b26299626eb8`)
  - `1.98.0-nightly (f8a08b688 2026-05-30)` (`rustc` SHA-256 `c0575015cb2b0648bff9042dc2e68f139fb0b16c981cdca96efba2e91ac409d8`)
- **Comparison Extractors Evaluated**:
  - `charon 0.1.174` (commit `5096e36339dc62d885fb3b7bf6e1bd98000514e0`, binary SHA-256 `bcdc1ef536f863f21367973bd639e5557d36872cd9135d4b13ff84c2bc6df836`)
  - `charon 0.1.210` (commit `1e08453924610c19d74c245a7308f17c1008e2db`, binary SHA-256 `88542ca0b2bf52429fd5b9f2bf29f0f1183ba2279854567ab13d82bc789a8d47`)
- **Proof Assistant**: Lean `4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`), verified with `lean -j1 -M2048 -DElab.async=false`.

## Findings

### 1. Specification Challenge, Claim-Change Detection, and Prefix-Conformance Transfer Gates

**Basis: source | execution | derived**

Across [`support/AnnealResearch/SpecValidation.lean`](support/AnnealResearch/SpecValidation.lean), [`support/AnnealResearch/SpecChallengeResolution.lean`](support/AnnealResearch/SpecChallengeResolution.lean), [`support/AnnealResearch/ClaimChangeResolution.lean`](support/AnnealResearch/ClaimChangeResolution.lean), [`support/AnnealResearch/ClaimChangeResolutionControls.lean`](support/AnnealResearch/ClaimChangeResolutionControls.lean), [`support/AnnealResearch/DesignModelTransfer.lean`](support/AnnealResearch/DesignModelTransfer.lean), and [`support/AnnealResearch/DesignModelControls.lean`](support/AnnealResearch/DesignModelControls.lean), we formalize the conditions under which a specification or design-model refinement can be trusted:

1. **Specification Challenge Against Mutant Implementations (`SpecChallengeResolution.lean`)**:
   - In a nested heap mutation model (`HelperValueHeap.lean`, `HelperNestedMutation.lean`, `HelperValueControls.lean`), a weak contract (`WeakContract`) that specifies only the normal-return root value image admits the intended transactional implementation (`nested_satisfies_weak`) alongside two buggy implementations: `commitOnlyOnOk` (which leaves partial leaf mutations uncommitted/corrupted on error) and `overwriteInPlace` (which clobbers aliased cells outside the mutable frame) (`weak_contract_admits_all_three_candidates`).
   - Strengthening only the error-path active value (`overwriteInPlace_satisfies_activeStrengthened`) or only the alias frame (`commitOnlyOnOk_satisfies_aliasStrengthened`) fails to reject both mutants (`partial_strengthenings_insufficient`).
   - The full contract `StrongContract` rejects `commitOnlyOnOk` specifically for violating `errorActiveValue` (`commitOnlyOnOk_violates_errorActiveValue`), rejects `overwriteInPlace` specifically for violating `closedAliases` (`overwriteInPlace_violates_closedAliases_on_ok_and_error`), admits `nested` (`nested_satisfies_strong`), and proves domain non-vacuity (`positive_nonvacuous_witness`) while flagging unsatisfiable preconditions (`vacuous_domain_control`).
2. **Non-Circular Claim-Change Classification (`ClaimChangeResolution.lean`, `ClaimChangeResolutionControls.lean`)**:
   - When an agent edits a proof repository, the claim-change auditor compares the baseline `ClaimRecord` against the revised `ClaimRecord`:
     - Pure proof-script edits with an identical `ClaimRecord` are classified `"unchanged"` (`proof_script_only_edit_preserves_claim`).
     - Equivalent reformulations accompanied by a kernel-checked equivalence witness (`DischargedEquiv`) are classified `"unchanged"` (`discharged_equivalence_preserves_claim`).
     - Predicate edits without a discharged equivalence proof are classified `"unknown"` (`unproved_predicate_change_reports_unknown`).
     - Weakening any single dimension—domain restriction, observation projection coarsening (`observation_marginal_weakening_exposed`), postcondition relaxation, or replacing universal execution coverage (`ExecCoverage.allExecutions`) with existential single-trace coverage (`ExecCoverage.existsExecution`)—is classified `"weakened"` (`single_field_weakening_rejects_preservation`, `universal_to_single_execution_admits_unsafe_machine`).
   - Negative controls prove that omitting a field from the claim record (`omitted_field_generator_control`), trusting a self-reported boolean flag (`self_oracle_circularity_control`), or relying on token/AST similarity (`syntax_similarity_control`) allows weakened claims to pass undetected.
3. **Step-Wise Prefix Simulation for Design-Model Safety Transfer (`DesignModelTransfer.lean`, `DesignModelControls.lean`)**:
   - Proving that a low-level implementation conforms to a verified lease design model only on completed executions (`CompletedConformance`) is satisfied by an implementation that triggers a transient UB fault and then diverges or masks the fault before completion (`transient_fault_impl_satisfies_completed_conformance`, `completed_conformance_fails_to_transfer_noUB`, `fault_before_divergence_counterexample`).
   - `prefix_conformance_transfers_noUB` proves that step-wise prefix conformance (`PrefixConformance`)—where every reachable implementation prefix maps to a reachable model prefix and preserves step-enabledness—soundly transfers `NoUB` from the design model to the implementation (`faithful_impl_noUB_transferred`).

### 2. Optimization Preservation, Typed Certificate Reuse, and Compilation-Unit Binding

**Basis: source | execution | derived**

[`support/AnnealResearch/OptimizationPreservation.lean`](support/AnnealResearch/OptimizationPreservation.lean), [`support/AnnealResearch/OptimizationControls.lean`](support/AnnealResearch/OptimizationControls.lean), [`support/AnnealResearch/FactReuseValidation.lean`](support/AnnealResearch/FactReuseValidation.lean), [`support/AnnealResearch/FactReuseControls.lean`](support/AnnealResearch/FactReuseControls.lean), [`support/AnnealResearch/IntegrationBinding.lean`](support/AnnealResearch/IntegrationBinding.lean), and [`support/AnnealResearch/IntegrationBindingControls.lean`](support/AnnealResearch/IntegrationBindingControls.lean) formalize preservation across optimizations and modular certificate reuse:

- **Frozen-Claim Optimization Preservation (`OptimizationPreservation.lean`, `OptimizationControls.lean`)**:
  - A valid loop/stage fusion optimization (`fusedValidOpt`) strictly reduces the logical step cost relative to the unoptimized baseline (`fusedValidOpt_strictly_reduces_logical_cost`) while satisfying the frozen specification (`fusedValidOpt_satisfies_frozen_claim`).
  - Three negative optimization candidates demonstrate why the frozen claim must cover frame footprints, observation traces, and all execution prefixes (`complete_candidate_classification`):
    1. `footprintClobber`: Produces the exact expected return value and is `NoUB`, but writes to an out-of-frame scratch slot (`footprintClobber_matches_output_and_noUB_but_violates_footprint`, `footprintClobber_rejected_by_frozen_claim`).
    2. `secretBranch`: Branches on secret data, violating constant-time observation policy (`secretBranch_violates_observation_policy`, `secretBranch_rejected_by_frozen_claim`).
    3. `latePrefixUb`: Agrees on small step bounds but triggers UB on a later prefix (`latePrefixUb_rejected_by_frozen_claim`).
  - If an optimization workflow is permitted to repair the contract to match the optimized code (`weakened_repair_admits_rejected_candidates`), `footprintClobber` and `secretBranch` are falsely accepted; pinning the frozen oracle blocks self-selected contract repair (`frozen_oracle_rejects_self_selected_contract_repair`).
- **Typed Certificate Reuse and Validity Preconditions (`FactReuseValidation.lean`, `FactReuseControls.lean`)**:
  - Layout certificates (`LayoutCert`) and byte-validity certificates (`CodecCert` for `validBoolByte b ↔ b = 0 ∨ b = 1`) compose with caller proofs (`checked_decoder_safe_for_all_bytes_via_reuse`, `unchecked_decoder_safe_under_validBoolByte_via_reuse`) and remain valid across callee implementation swaps that preserve the certificate interface (`implementation_swap_reuses_layout_cert`) and across client edits (`client_edit_reuses_layout_and_codec_certs`).
  - Negative controls verify that feeding byte `2` to an unchecked boolean decoder triggers immediate UB even if the decoded boolean is subsequently discarded (`admitted_invalid_bool_byte2_exposes_ub`, `discarded_invalid_bool_still_ub`), and that changing `#[cfg]` layout configurations or strengthening a callee's precondition invalidates cached certificates (`config_or_instance_change_invalidates_codec_cert`, `premise_strengthening_invalidates_caller_reuse`).
- **Essential vs. Incidental Compilation-Unit Binding (`IntegrationBinding.lean`, `IntegrationBindingControls.lean`)**:
  - Partitioning capture metadata into **essential identity** (`crateName`, `cfgFlags`, `macroExpansionHash`, `monoInstanceSet`, `mirBodyHash`, `producerSucceeded = true`) and **incidental numbering** (`compilerTempBase`, `defIdTableOffset`) allows certificates to survive alpha-equivalent compiler temporary renumbering (`incidental_renumbering_preserves_essential_admission`) while rejecting `--cfg alt_impl` or `--cfg variant_b` changes (`cfg_alt_impl_change_invalidates_a0_cert`, `cfg_variant_b_change_invalidates_a0_cert`), stale files left behind by a failed producer (`failed_producer_with_present_mir_file_rejected`), unexpanded macro token loaders (`unexpanded_macro_token_loader_control`), and un-monomorphized generic mentions (`unused_generic_mention_not_monomorphized_control`).

### 3. Live Agent Task Evaluation, Source-Name `var_debug_info` Joins, and Holdout Outcome Separation

**Basis: source | execution | derived**

[`support/agent-tasks-ledger.json`](support/agent-tasks-ledger.json), [`support/h11-holdout-ledger.json`](support/h11-holdout-ledger.json), [`support/AnnealResearch/AgentTasksAndCompilerUpgrade.lean`](support/AnnealResearch/AgentTasksAndCompilerUpgrade.lean), [`support/AnnealResearch/AgentTasksAndUpgradeControls.lean`](support/AnnealResearch/AgentTasksAndUpgradeControls.lean), and [`support/AnnealResearch/IndependentSliceHoldoutH11.lean`](support/AnnealResearch/IndependentSliceHoldoutH11.lean) evaluate concrete agent proof authoring, bug localization, refactor maintenance, and anti-weakening gates on real `.amir` v3 artifacts:

1. **Closing the Post-Cleanup Variable-Anonymity Gap via `mir_built` `var_debug_info` Joins**:
   - In post-cleanup `runtime_mir`, `rustc`'s `ClearStorageMarkers` / debug-clearing passes clear `local_decls[i].local_info` (`post_cleanup_local_info: "Cleared"`), leaving anonymous register indices (`_1`, `_7`, `_17`, `_21`) (`control_anonymous_post_cleanup_loses_source_variable_localization`).
   - By joining `mir_built.var_debug_info` with `runtime_mir` locals in the driver sidecar ([`support/agent-tasks-ledger.json`](support/agent-tasks-ledger.json), `var_debug_local_join.json` SHA-256 `d3e46348...`), every user variable (`size -> _1`, `align -> _2`, `offset -> _7`, `max_align -> _17`, `new_size -> _21`) is uniquely mapped (`UniqueUserVar`) alongside synthesized temporaries (`SynthesizedPassTemp`, `SynthesizedDropFlag`) (`built_local_info_sidecar_closes_agent_localization_while_preserving_soundness`).
   - When `align_to` is refactored by introducing an intermediate binding (`aligned_rem`), shifting `rem` from `_8` to `_12` and `pad` from `_15` to `_16`, raw local-index invariants break (`control_raw_local_index_invariants_break_under_behavior_preserving_refactor`), whereas invariants phrased over the `var_debug_info` source-name join transfer automatically (`task3_source_name_join_absorbs_local_index_shift_under_refactor`).
2. **Seeded Bug Localization and Weakening-Trap Rejection (`task2` & `task4`)**:
   - In `DstLayout::extend` (`zerocopy_layout_holdout.rs`), seeding a bug that passes `self.align` instead of `next.align` when aligning the trailing field offset compiles to a 2,154-byte `.amir` (`44285675...`) that differs only in basic block `bb12` (`task2_seeded_bug_falsifies_c0_contract_and_repaired_block_restores_it`). Repairing `bb12` restores the canonical holdout `.amir` (`c9a0965e...`, `task2_repaired_extend_bb12_matches_decoded_holdout_package`).
   - `task4_all_three_weakening_traps_rejected` and its negative controls verify that all three agent "cheat" strategies are caught:
     - **Trap A (`control_trap_a_weakened_extend_and_cleanup_contracts_unsound`)**: Weakening `DstLayout::extend`'s postcondition to check only `Result::is_ok` or weakening `cleanup_subject` to check only return scalars admits the buggy `.amir` artifacts.
     - **Trap B (`control_trap_b_dropped_preserve_ub_rejected_at_boundary3_and_boundary5`)**: Dropping `-Z mir-preserve-ub` on `place_mention_probe.rs` (`b8ca252c...`, header `flags_bitmask` bit `0 = 0`) is rejected at both `B3` compilation binding and `B5` raw-pointer adequacy.
     - **Trap C (`control_trap_c_unproved_assumption` / `control_trap_c_unverified_charon_routes_fail_c0_cleanup_gate`)**: Substituting Charon LLBC (which drops unwind cleanup edges) or raw ULLBC (which omits implicit drop glue) fails the `C0` unwind/drop oracle.
3. **Independent Holdout Slice-Window Localization and Outcome Status Separation (`IndependentSliceHoldoutH11.lean`)**:
   - On an independent slice-window verifier subject (`independent_slice_holdout.rs`, 936-byte `.amir` `e12e3957...`) vs. an off-by-one mutant (`independent_slice_holdout_buggy.rs`, `if end < cap` instead of `if end <= cap`, 936-byte `.amir` `fa322048...`), the two `.amir` binaries differ at exactly one payload byte: offset `403` (`BinOpTag.le = 0x04` vs. `BinOpTag.lt = 0x03`, inside `bb7` statement 10 of `validate_slice_window`), plus the 2-byte header fingerprint at offsets `7..8` (`independent_holdout_buggy_bb7_localized_lt_vs_le`, `independent_holdout_buggy_falsifies_exact_cap_boundary`).
   - Furthermore, `control_n4_status_erasing_projection_accepts_faulting_and_nonterminating_none_mutants_while_explicit_outcome_rejects` proves that a legacy evaluator projecting non-`Some` outcomes to `Option.none` falsely accepts both an infinite self-loop mutant (`mutantValidateSliceWindowElemZeroInfiniteLoopBytes`, which exhausts fuel `.fuelExhausted`) and a stuck aggregate-tag mutant (`mutantValidateSliceWindowElemZeroStuckReturnBytes`, which halts in `.malformedOrStuck`), whereas `SliceWindowExecOutcome` (`classifySliceWindowStatus_normalNone_iff`) accepts only genuine `Option::None` returns (`.normalNone`).

### 4. Four-Toolchain Nightly Rust Upgrade Trial (`1.95` $\to$ `1.98`) vs. Charon and `rustc_public`

**Basis: source | execution | derived**

[`support/upgrade-trial-ledger.json`](support/upgrade-trial-ledger.json), [`support/direct_mir_driver_portable.rs`](support/direct_mir_driver_portable.rs), [`support/AnnealResearch/FrontendPropertyAndUpgrade.lean`](support/AnnealResearch/FrontendPropertyAndUpgrade.lean), [`support/AnnealResearch/FrontendPropertyUpgradeControls.lean`](support/AnnealResearch/FrontendPropertyUpgradeControls.lean), and [`support/AnnealResearch/AgentTasksAndCompilerUpgrade.lean`](support/AnnealResearch/AgentTasksAndCompilerUpgrade.lean) measure the engineering and semantic maintenance cost of tracking `rustc` across four nightly toolchains (`1.95.0-nightly`, `1.96.0-nightly`, `1.97.0-nightly`, `1.98.0-nightly`):

| Toolchain | `rustc` Commit & Date | `rustc_middle::mir` Change | Portable Driver Build (`ms`) | `place_mention_probe.amir` SHA-256 | `cleanup_subject.amir` SHA-256 | `zerocopy_layout_holdout.amir` SHA-256 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `1.95.0-nightly` | `efc9e1b50` (`2026-02-06`) | Baseline (`Rvalue::Use(op)`, `StatementKind::Retag`, `resolve_drop_in_place`) | `2,133 ms` | `7e96e186...` (194 B) | `10ba3162...` (1,067 B) | `c9a0965e...` (2,154 B) |
| `1.96.0-nightly` | `02c7f9bec` (`2026-04-10`) | `#[derive(Eq)]` helper renamed (`assert_receiver_is_total_eq` $\to$ `assert_fields_are_eq`) | `2,135 ms` | `7e96e186...` (194 B) | `10ba3162...` (1,067 B) | `c9a0965e...` (2,154 B) |
| `1.97.0-nightly` | `bf4fbfb7a` (`2026-04-11`) | Same MIR representation as `1.96` | `2,149 ms` | `7e96e186...` (194 B) | `10ba3162...` (1,067 B) | `c9a0965e...` (2,154 B) |
| `1.98.0-nightly` | `f8a08b688` (`2026-05-30`) | `StatementKind::Retag` (`0x31`) folded into `Rvalue::Use(op, WithRetag)` (`0x10`/`0x11`); `resolve_drop_in_place` $\to$ `resolve_drop_glue` | `2,105 ms` | `7e96e186...` (194 B) | `d6244df6...` (1,066 B) | `c9a0965e...` (2,154 B) |

Key findings from the 4-toolchain upgrade trial:

- **36-LOC (`5` `#[cfg]` blocks) Portable `rustc_driver` Adapter (`portable_driver_bridges_four_nightly_toolchains_with_21_line_adapter`)**:
  - [`support/direct_mir_driver_portable.rs`](support/direct_mir_driver_portable.rs) compiles cleanly against all four nightly toolchains using 5 conditional compilation blocks totaling 36 lines.
  - Between `1.97.0-nightly` and `1.98.0-nightly`, `rustc` removed the standalone `StatementKind::Retag` statement (`0x31`) and folded retag semantics into `Rvalue::Use(operand, WithRetag)` (`0x10` for `WithRetag::No`, `0x11` for `WithRetag::Yes`).
  - `retag_stmt_0x31_after_use_no_retag_0x10_equiv_folded_use_retag_yes_0x11` ([`support/AnnealResearch/AgentTasksAndCompilerUpgrade.lean`](support/AnnealResearch/AgentTasksAndCompilerUpgrade.lean)) proves in Lean 4 that executing `Assign(dst, Use(op, NoRetag))` (`0x10`) followed by `Retag(dst)` (`0x31`) is operationally equivalent to executing the folded `Assign(dst, Use(op, WithRetag::Yes))` (`0x11`), discharging the 1-byte `cleanup_subject.amir` delta (`1,067 B` $\to$ `1,066 B`) without weakening any `C0` specification (`fe12_upgrade_acceptance_requires_independent_semantic_delta_check`, `visible_structural_change_repaired_without_claim_weakening`).
- **Comparison Against `rustc_public` and Charon `0.1.174` $\to$ `0.1.210`**:
  - `rustc_public` (`stable_mir`) did not insulate callers from the `1.97` $\to$ `1.98` `WithRetag` breakage because `rustc_public`'s internal conversion tables failed to compile until updated for `WithRetag` (`rustc_public_did_not_insulate_against_1_98_with_retag_breakage`, `control_rustc_public_breaks_across_1_97_to_1_98_transition`).
  - Prebuilt `charon-driver` binaries are dynamically linked against a specific `librustc_driver-<hash>.so` and fail with exit code `127` when invoked across toolchain bumps (`prebuilt_charon_0_1_210_probe` on `1.95.0-nightly` in [`support/upgrade-trial-ledger.json`](support/upgrade-trial-ledger.json)). Moving Charon from `0.1.174` (`1.95.0-nightly`) to `0.1.210` (`1.98.0-nightly`) required 5 upstream `rustc`-bump commits modifying 37 files in `charon-driver` (`+9,026` insertions, `-1,827` deletions).
- **Silent Semantic Drift vs. Syntax/Snapshot Oracles (`silent_semantic_drift_passes_syntax_and_snapshot_oracle_control`)**:
  - [`support/AnnealResearch/FrontendPropertyUpgradeControls.lean`](support/AnnealResearch/FrontendPropertyUpgradeControls.lean) proves that a compiler upgrade that alters operational semantics while preserving surface syntax or coarse block-count snapshots passes syntax/snapshot checks (`control_r6_structure_preserving_drift_rejected_by_decoded_ast_c0_oracle`), demonstrating why compiler upgrades must re-run the decoded AST against the pinned operational oracle (`fe12_upgrade_acceptance_requires_independent_semantic_delta_check`).

## Boundaries

- **`not examined`**:
  - Nightly `rustc` toolchains prior to `1.95.0-nightly (2026-02-06)` or subsequent to `1.100.0-nightly`.
  - Automated LLM synthesis of arbitrary loop invariants without human-provided or template-guided `var_debug_info` invariant predicates.
- **`unknown`**:
  - Whether future `rustc` changes to `mir_drops_elaborated_and_const_checked` will alter drop-flag lowering structure enough to require new structural equivalence lemmas beyond `retag_stmt_0x31_after_use_no_retag_0x10_equiv_folded_use_retag_yes_0x11`.
- **`known not to apply`**:
  - Completed-trace conformance (`CompletedConformance`) does not transfer `NoUB` from a design model to an implementation that can fault and then diverge (`completed_conformance_fails_to_transfer_noUB`).
  - Status-erasing `Option` projections (`legacyStatusErasingSuiteCheck`) do not distinguish genuine `Option::None` returns from fuel exhaustion or stuck states (`control_n4_status_erasing_projection_accepts_faulting_and_nonterminating_none_mutants_while_explicit_outcome_rejects`).
  - Theorem-count metrics and unpinned specification checkers do not prevent agent contract weakening (`tempting_contract_weakening_passes_unpinned_checker`, `theorem_count_metric_rewards_inflated_weak_submission`).
- **`unsupported`**:
  - Polymorphic call targets with unresolved type parameters initially failed closed in `direct_mir_driver_v4.rs` (`UnsupportedCallee(core::mem::align_of with substs [T/#0])`, exit code `2`) until `ParamTy` `T/#0` was explicitly mapped alongside concrete monomorphizations in the driver (`task1_spec_proof_authoring` in [`support/agent-tasks-ledger.json`](support/agent-tasks-ledger.json)).

## Evidence

| Artifact | Path | Description & SHA-256 |
| :--- | :--- | :--- |
| Lean Execution Ledger | [`support/lean-execution-ledger.json`](support/lean-execution-ledger.json) | Fresh Lean `4.34.1` (`-j1 -M2048 -DElab.async=false`) verification ledger across all 30 modules in topological order (`exit_code: 0`). |
| Spec Challenge & Value-Heap Helpers | [`support/AnnealResearch/HelperValueHeap.lean`](support/AnnealResearch/HelperValueHeap.lean), [`support/AnnealResearch/HelperNestedMutation.lean`](support/AnnealResearch/HelperNestedMutation.lean), [`support/AnnealResearch/HelperValueControls.lean`](support/AnnealResearch/HelperValueControls.lean), [`support/AnnealResearch/SpecValidation.lean`](support/AnnealResearch/SpecValidation.lean), [`support/AnnealResearch/SpecChallengeResolution.lean`](support/AnnealResearch/SpecChallengeResolution.lean) | Value-heap nested mutation model, `commitOnlyOnOk` and `overwriteInPlace` mutant discriminators, and non-vacuity proofs. |
| Claim-Change & Design-Model Transfer Gates | [`support/AnnealResearch/ClaimChangeResolution.lean`](support/AnnealResearch/ClaimChangeResolution.lean), [`support/AnnealResearch/ClaimChangeResolutionControls.lean`](support/AnnealResearch/ClaimChangeResolutionControls.lean), [`support/AnnealResearch/DesignModelTransfer.lean`](support/AnnealResearch/DesignModelTransfer.lean), [`support/AnnealResearch/DesignModelControls.lean`](support/AnnealResearch/DesignModelControls.lean) | Structured `ClaimRecord` diffing, anti-circularity controls, and prefix-conformance vs. completed-trace safety transfer theorems. |
| Optimization, Certificate Reuse & Binding | [`support/AnnealResearch/OptimizationPreservation.lean`](support/AnnealResearch/OptimizationPreservation.lean), [`support/AnnealResearch/OptimizationControls.lean`](support/AnnealResearch/OptimizationControls.lean), [`support/AnnealResearch/FactReuseValidation.lean`](support/AnnealResearch/FactReuseValidation.lean), [`support/AnnealResearch/FactReuseControls.lean`](support/AnnealResearch/FactReuseControls.lean), [`support/AnnealResearch/IntegrationBinding.lean`](support/AnnealResearch/IntegrationBinding.lean), [`support/AnnealResearch/IntegrationBindingControls.lean`](support/AnnealResearch/IntegrationBindingControls.lean) | Frozen-claim optimization preservation, footprint/secret-branch/late-UB controls, typed `LayoutCert`/`CodecCert` reuse, and essential vs. incidental compilation-unit binding. |
| Agent Tasks, Compiler Upgrade & Holdout H11 | [`support/AnnealResearch/AgentTaskEvaluation.lean`](support/AnnealResearch/AgentTaskEvaluation.lean), [`support/AnnealResearch/AgentTaskControls.lean`](support/AnnealResearch/AgentTaskControls.lean), [`support/AnnealResearch/FrontendPropertyAndUpgrade.lean`](support/AnnealResearch/FrontendPropertyAndUpgrade.lean), [`support/AnnealResearch/FrontendPropertyUpgradeControls.lean`](support/AnnealResearch/FrontendPropertyUpgradeControls.lean), [`support/AnnealResearch/AgentTasksAndCompilerUpgrade.lean`](support/AnnealResearch/AgentTasksAndCompilerUpgrade.lean), [`support/AnnealResearch/AgentTasksAndUpgradeControls.lean`](support/AnnealResearch/AgentTasksAndUpgradeControls.lean), [`support/AnnealResearch/IndependentSliceHoldoutH11.lean`](support/AnnealResearch/IndependentSliceHoldoutH11.lean) | Claim-pinned agent evaluation, `var_debug_info` local-shift absorption, Trap A/B/C rejections, `Retag` (`0x31`) $\leftrightarrow$ `WithRetag` (`0x11`) equivalence, and H11 slice-window localization + `SliceWindowExecOutcome` separation. |
| Portable Driver & Empirical Ledgers | [`support/direct_mir_driver_portable.rs`](support/direct_mir_driver_portable.rs), [`support/upgrade-trial-ledger.json`](support/upgrade-trial-ledger.json), [`support/agent-tasks-ledger.json`](support/agent-tasks-ledger.json), [`support/h11-holdout-ledger.json`](support/h11-holdout-ledger.json), [`support/run_upgrade_trial.py`](support/run_upgrade_trial.py), [`support/run_agent_tasks.py`](support/run_agent_tasks.py) | 4-toolchain portable `rustc_driver` (`aec4749f...`), Charon `0.1.174` $\to$ `0.1.210` diff study, agent task localization traces, and H11 binary diff ledger. |

## Revalidation

To re-verify the complete 30-module Lean 4 closure in [`support/AnnealResearch/`](support/AnnealResearch/) using Lean `4.34.1`:

```bash
mkdir -p /tmp/r18-build/AnnealResearch
for mod in \
  HelperValueHeap \
  HelperNestedMutation \
  HelperValueControls \
  SpecValidation \
  SpecChallengeResolution \
  Execution \
  ClaimChangeResolution \
  ClaimChangeResolutionControls \
  DesignModelTransfer \
  DesignModelControls \
  OptimizationPreservation \
  OptimizationControls \
  FactReuseValidation \
  FactReuseControls \
  IntegrationBinding \
  IntegrationBindingControls \
  AgentTaskEvaluation \
  AgentTaskControls \
  FrontendPropertyAndUpgrade \
  FrontendPropertyUpgradeControls \
  SubstantiveMirByteParser \
  SemanticVerticalSliceCore \
  SemanticVerticalSliceZerocopy \
  SemanticVerticalSlice \
  SubstantiveMirByteParserControls \
  SemanticVerticalSliceControlsCleanup \
  SemanticVerticalSliceControls \
  AgentTasksAndCompilerUpgrade \
  AgentTasksAndUpgradeControls \
  IndependentSliceHoldoutH11; do
  LEAN_PATH=/tmp/r18-build lean -j1 -M2048 -DElab.async=false \
    -o "/tmp/r18-build/AnnealResearch/${mod}.olean" \
    "support/AnnealResearch/${mod}.lean"
done
```

Expected outcome: Every module compiles with exit code `0` (`children_maxrss_kb <= 984464`), matching [`support/lean-execution-ledger.json`](support/lean-execution-ledger.json).
