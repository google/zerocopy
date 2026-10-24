# Verified AMIR Binary Wire Format, Two-Sided Built-to-Post-Cleanup Lowering Validation, and Sound Structured Proof Views

## Summary

Verifying Rust operational semantics from compiler-emitted Mid-Level Intermediate Representation (MIR) without an unverified text/JSON frontend parser requires three coupled mechanisms:

1. **A canonical, length-delimited binary wire format (`AMIRv2` / `AMIRv3`) paired with a total, deterministic byte parser verified in Lean 4**: Rather than starting formal proofs at an already-parsed JSON AST, the verifier ingests raw `List Nat` / `ByteArray` payloads (`AMIR\x03\x00\x00\x00`), enforces physical byte-range (`b < 256`), exact end-of-input consumption (`pos == bytes.length`), canonical FNV-1a payload hashing, and structural well-formedness (`wfPackage` + `closedCallersPackage`), and proves universal round-trip, injectivity, and canonical encoding uniqueness (`universal_accepted_byte_soundness`, `universal_accepted_package_canonical_unique`).
2. **A three-stage compilation-binding predicate (`endorsedCompilationBinding`)**: Syntactic and structural byte acceptance (`B1` + `B2`) ensures that a byte stream decodes to a well-formed, call-closed MIR package, whereas compilation binding (`B3`: `Stage3a` internal header integrity, `Stage3b` sidecar SHA-256 endorsement, `Stage3c` trusted compiler driver invocation with `-Z mir-preserve-ub`) binds those accepted bytes to a specific `rustc` invocation and flag configuration.
3. **A two-sided `mir_built`-to-post-cleanup lowering validator and environment-parameterized structured proof views**: Because `rustc` lowers conditional `StorageDead` / drop obligations in `mir_built` into explicit post-elaboration cleanup paths (`ElaborateDrops`), the verifier pairs post-cleanup `runtime_mir` with `mir_built` and validates behavioral equivalence across both normal and unwind paths (`validateBuiltToPostCleanupAdmittedQ1_sound`). Above the raw post-cleanup CFG, a sound environment-parameterized structured view recognizer (`reconstructVerifiedStructuredViewInEnv`) enables compositional weakest-precondition (`wpStateSteps`) proofs while rejecting control-flow and event-ordering mutations that a naive signature-only recognizer accepts.

## Applicability

These findings apply to formal verification pipelines that extract Rust MIR via custom `rustc_driver` callbacks (`after_analysis`) and verify operational properties inside the Lean 4 kernel:

- **Rust Toolchain**: `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `x86_64-unknown-linux-gnu`), with comparison artifacts extracted by `charon 0.1.210` (binary SHA-256 `88542ca0b2bf52429fd5b9f2bf29f0f1183ba2279854567ab13d82bc789a8d47`).
- **Proof Assistant**: Lean `4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`), checked under `lean -j1 -M768` with zero `sorry` / `admit` tokens and only standard Lean kernel axioms (`propext`, `Quot.sound`).
- **Target Verification Domain**: Unsafe raw-pointer alignment/slice manipulation (`zerocopy`-style alignment prefixes, metadata count validation, and `#[repr(C)]` / `#[repr(C, packed(2))]` unsized tail packets), unwind/drop cleanup ordering (`ElaborateDrops`), and stateful generic library contracts.

## Findings

### 1. Canonical Binary Wire Format (`AMIRv2` / `AMIRv3`) Eliminates the Unverified JSON Parser Gap

**Basis: source | execution | derived**

Starting verification from an in-memory AST produced by an unverified JSON parser leaves the byte-to-AST decoding step outside the kernel's trusted computing base (`json_ast_start_leaves_bytes_to_json_unproved_control` in [`support/AnnealResearch/MirWireParserControls.lean`](support/AnnealResearch/MirWireParserControls.lean)). In [`support/AnnealResearch/MirWireParser.lean`](support/AnnealResearch/MirWireParser.lean) and [`support/AnnealResearch/SubstantiveMirByteParser.lean`](support/AnnealResearch/SubstantiveMirByteParser.lean), the binary wire formats (`AMIRv2` and `AMIRv3`) replace text parsing with an explicit, tag-delimited, little-endian `u32` byte grammar:

- **Magic and Header (`AMIRv3`, 28 bytes)**:
  - Bytes `0..8`: ASCII magic `"AMIR"` (`[0x41, 0x4D, 0x49, 0x52]`) followed by format version `3` (`u32` little-endian `[0x03, 0x00, 0x00, 0x00]`).
  - Bytes `8..12`: `flags_bitmask` (`bit 0 = mir_preserve_ub`, `bit 1 = overflow_checks`).
  - Bytes `12..16`: `toolchain_id` (`0x01980001` for the pinned `rustc 1.98.0-nightly` toolchain).
  - Bytes `16..20`: `subject_id` identifying the target compilation unit.
  - Bytes `20..24`: `payload_len` (exact byte length of the serialized `typeTable`, `layoutTable`, and `bodies` sections).
  - Bytes `24..28`: `payload_fnv1a32` (32-bit FNV-1a checksum computed over the payload bytes).
- **Substantive Body Grammar (`SubstantiveMirByteParser.lean`)**:
  - Encodes full basic-block CFGs (`BasicBlock`, `Stmt`, `Term`, `Rvalue`, `Operand`, `Place`, `ProjElem`) with no basic-block count cap (`real_cleanup_subject_preserve_ub_bytes_accepted_without_block_truncation`, `real_zerocopy_layout_holdout_bytes_accepted_without_block_truncation`, and `real_limit_32_positive_bytes_accepted_at_exact_32_block_bound`).
  - Every `Encode*` function is paired with a state-monad `parse* : List Nat → Nat → Option (α × Nat)` function that advances a cursor `pos` and fails closed on truncated input, unknown tags, non-physical byte values (`∃ b ∈ bytes, b ≥ 256`), or trailing bytes (`pos != bytes.length`).

Universal parser soundness and canonical uniqueness are machine-checked over all byte lists `bytes : List Nat`:

- `parsePacket_complete_roundtrip` and `parsePacket_sound_injective` ([`support/AnnealResearch/MirWireParser.lean`](support/AnnealResearch/MirWireParser.lean)): Every well-formed `AMIRv2` packet round-trips (`parsePacket (encodePacket pkt) = DecodeResult.ok pkt`) and `encodePacket` is injective across all well-formed packets.
- `universal_accepted_byte_soundness` ([`support/AnnealResearch/SubstantiveMirByteParser.lean`](support/AnnealResearch/SubstantiveMirByteParser.lean)): For all `bytes : List Nat` and `pkg : MirPackage`, if `parseAcceptedMirPackageBytes bytes = some pkg`, then all elements of `bytes` are physical bytes (`< 256`), `wfPackage pkg = true`, `closedCallersPackage pkg = true`, and `encodeMirPackageBytes pkg = bytes`.
- `universal_accepted_package_canonical_unique` ([`support/AnnealResearch/SubstantiveMirByteParser.lean`](support/AnnealResearch/SubstantiveMirByteParser.lean)): Any two byte sequences accepted as the same `MirPackage` are byte-for-byte identical (`bytes1 = bytes2`).

### 2. Three-Stage Compilation Binding (`B1`, `B2`, `B3`) Separates Structural Validity from Provenance

**Basis: source | execution | derived**

[`support/AnnealResearch/SubstantiveMirByteParserControls.lean`](support/AnnealResearch/SubstantiveMirByteParserControls.lean) proves that byte-level grammar and structural validation (`B1` + `B2`) must be composed with a three-stage provenance binding predicate (`B3`) to prevent body substitution or flag-spoofing attacks:

| Validation Stage | Predicate / Check | Rejects | Witness Theorem in `SubstantiveMirByteParserControls.lean` |
| :--- | :--- | :--- | :--- |
| **B1: Syntactic Byte Grammar** | `parseMirPackageBytes` (`allPhysicalBytes`, magic/version, exact `payload_len`, `fnv1a32`, supported tags, no trailing bytes) | Non-physical `Nat >= 256`, truncated streams, trailing garbage, unsupported inline assembly tags (`0xFE`) | `control_b1_non_physical_byte_rejected`, `control_b1_truncated_rejected`, `control_b1_trailing_bytes_rejected`, `control_b1_unsupported_inline_asm_rejected` |
| **B2a: Intra-Body Well-Formedness** | `wfBody` (`localCount` bounds, basic block target bounds, projection validity) | Out-of-bounds local indices (`localIdx >= localCount`) or invalid block edges | `control_b2_out_of_bounds_local_rejected` |
| **B2b: Package Call Closure** | `wfPackage && closedCallersPackage` | Duplicate symbol IDs (`symId`), missing required entry bodies, unresolved internal call targets | `control_b2b_duplicate_sym_id_rejected`, `control_b2b_missing_required_body_rejected` |
| **B3 (`Stage3a`): Header Self-Consistency** | `checkStage3aHeaderSelfConsistency` | Header/payload length mismatch or FNV-1a mismatch | `control_b3_spoofed_header_payload_passes_stage3a_and_rejected_at_stage3b` |
| **B3 (`Stage3b`): Sidecar Hash Binding** | `checkStage3bSidecarConsistency` | Spoofed `.amir` payload with recomputed FNV-1a header that disagrees with the driver's JSON sidecar SHA-256 (`amir_v3_sha256`) | `control_b3_spoofed_header_payload_passes_stage3a_and_rejected_at_stage3b`, `control_b3_recomputed_header_mutant_passes_stage3b_and_rejected_at_stage3c` |
| **B3 (`Stage3c`): Trusted Invocation Binding** | `endorsedCompilationBinding` (`trustedProducer`, `driver_exit_code == 0`, `mono_collector_ran`, `amir_v3_write_succeeded`, matching `subject_id` and `flags_bitmask`) | Recomputed `.amir` + sidecar pair from a mutated body, wrong compilation subject, missing `-Z mir-preserve-ub`, incomplete `--driver-stop-after-analysis` run, or failed output write | `endorsed_compilation_binding_sound_under_trusted_producer`, `control_b3_wrong_subject_passes_b1_b2_and_rejected_at_b3`, `control_b3_wrong_flag_config_passes_b1_b2_and_rejected_at_b3`, `control_b3_incomplete_or_failed_write_rejected_at_stage3c` |

Furthermore, `control_b3_untrusted_metadata_cannot_alter_accepted_ast` proves that sidecar metadata cannot alter the decoded `MirPackage` AST: the operational semantics depends exclusively on the verified byte parser's output (`parseAcceptedMirPackageBytes bytes`), while the sidecar serves strictly as an admission gate.

### 3. Semantic Necessity of `-Z mir-preserve-ub` and Post-Cleanup Unwind Edges (`runtime_mir`)

**Basis: source | execution | derived**

Empirical capture via [`support/direct_mir_driver_v4.rs`](support/direct_mir_driver_v4.rs) (recorded in [`support/capture-v4-ledger.json`](support/capture-v4-ledger.json)) and Lean proofs across [`support/AnnealResearch/SemanticVerticalSliceCore.lean`](support/AnnealResearch/SemanticVerticalSliceCore.lean), [`support/AnnealResearch/SemanticVerticalSliceZerocopy.lean`](support/AnnealResearch/SemanticVerticalSliceZerocopy.lean), [`support/AnnealResearch/SemanticVerticalSlice.lean`](support/AnnealResearch/SemanticVerticalSlice.lean), and [`support/AnnealResearch/SemanticVerticalSliceControls.lean`](support/AnnealResearch/SemanticVerticalSliceControls.lean) establish two critical compiler-boundary invariants:

1. **Wildcard and Underscore Raw-Pointer Reads Require `-Z mir-preserve-ub`**:
   - When `place_mention_probe.rs` (`let _ = *ptr; let _x = *ptr;`) is compiled under default MIR flags (`place_mention_default.amir`, 185 bytes, SHA-256 `b8ca252c24df2356eca374f992f70c6c8d86b2111e5297c2645abc8b59a2b765`), `rustc` elides `PlaceMention(*ptr)` statements for wildcard reads (`real_place_mention_default_bytes_accepted_and_drops_wildcard_mentions`).
   - Consequently, default MIR passes syntactic/structural byte checks (`B1` + `B2`) yet fails raw-pointer UB adequacy (`control_b5_default_mir_passes_b1_b2_but_fails_raw_ptr_adequacy`, `direct_mir_place_mention_default_misses_wildcard_and_underscore_ub`).
   - Compiling with `-Z mir-preserve-ub` (`place_mention_preserve_ub.amir`, 194 bytes, SHA-256 `7e96e186ff83c62741007819c7429fd22811011a11ac0b5cf00e135c85a8376d`) retains both `PlaceMention(Deref)` statements (`real_place_mention_preserve_ub_bytes_accepted_and_preserves_mentions`, `direct_mir_place_mention_preserve_ub_satisfies_c0`).
2. **Post-Cleanup `runtime_mir` vs. Charon ULLBC / LLBC Drop and Unwind Fidelity**:
   - Direct post-cleanup `runtime_mir` (`cleanup_subject_preserve_ub.amir`, 1,066 bytes, SHA-256 `d6244df6c9e113e6e91b520d26425ce55d7d5778bca94f81debf551369eabed2`) explicitly represents reverse-declaration drop ordering (`Guard(2)` then `Guard(1)`), early moves before panics, partial reinitialization, and unwind cleanup transitions (`direct_mir_cleanup_suite_satisfies_c0_all_cases`).
   - In contrast, raw Charon `0.1.210` ULLBC (`--ullbc`) omits implicit drop glue (`charon_ullbc_raw_decoded_and_fails_missing_drop_glue`), and structured LLBC drops unwind cleanup paths (`charon_llbc_remedy_r2_passes_normal_and_loses_unwind_cleanup`, `charon_llbc_falsifies_c0_unwind_cleanup_spec`). Only ULLBC paired with `--mir elaborated` (`charon_ullbc_remedy_r2_satisfies_all_c0_cleanup_cases`) recovers the drop and unwind semantics on the single-crate slice.
3. **Zerocopy Alignment, Slice Count Validation, and Unsized Tail Layouts**:
   - [`support/AnnealResearch/SemanticVerticalSliceZerocopy.lean`](support/AnnealResearch/SemanticVerticalSliceZerocopy.lean) verifies `zerocopy_layout_holdout.amir` (2,154 bytes, SHA-256 `c9a0965ec8ad242321716375c3d5dfe0d5a5b823acaaea1fb8886096f0916bd3`) end-to-end from raw `.amir` bytes (`direct_mir_zerocopy_align_extend_satisfies_c0`, `direct_mir_zerocopy_validate_count_satisfies_c0`, `direct_mir_zerocopy_suite_satisfies_c0_all_cases`), while rejecting mutated alignment/extension bodies (`mutant5_accepted_by_byte_parser_and_falsifies_c0_align_to`, `mutant6_accepted_by_byte_parser_and_falsifies_c0_extend`).
   - [`support/AnnealResearch/PR86AuditRepairs.lean`](support/AnnealResearch/PR86AuditRepairs.lean) extends layout verification to `u32` wire-range layout table entries (`encodeLayoutEntryBytes_preserves_size_and_align_when_in_range_q2`, `q2_full_range_layout_binding_controls_verified`) and proves universal dynamic offset/size laws for unsized slice-tail structs under both `#[repr(C)]` (`PacketWithTail`: header `u16` + `u32` at offsets `0` and `4`, tail `[u16]` at offset `8`, stride `2`, overall alignment `4`, padded size $4 \cdot \lceil (8 + 2n)/4 \rceil$) and `#[repr(C, packed(2))]` (`PacketWithTailPacked2`: header at offsets `0` and `2`, tail at offset `6`, stride `2`, alignment `2`, size $6 + 2n$) in `q5_r10_packet_with_tail_repr_c_universal_law`, `q5_r10_packet_with_tail_packed2_universal_law`, and `q5_r10_joined_specimen_and_footprint_boundaries_verified`.

### 4. Fail-Closed Two-Sided `mir_built`-to-Post-Cleanup Lowering Validation and Sound Structured Views

**Basis: source | execution | derived**

[`support/AnnealResearch/StatefulGenericLibraryH3H7.lean`](support/AnnealResearch/StatefulGenericLibraryH3H7.lean), [`support/AnnealResearch/StatefulGenericLibraryH3H7Controls.lean`](support/AnnealResearch/StatefulGenericLibraryH3H7Controls.lean), and [`support/AnnealResearch/PR86AuditRepairs.lean`](support/AnnealResearch/PR86AuditRepairs.lean) evaluate how pre-elaboration `mir_built` relates to post-cleanup `runtime_mir` and how structured proof obligations are discharged above the raw CFG:

- **Conditional vs. Unconditional Drop Elaboration (`n3_built_graph_conditional_vs_unconditional_drop_semantics_and_elaboration_agreement`)**: In `mir_built`, a drop edge following a conditional move requires dynamic drop-flag tracking; `rustc`'s `ElaborateDrops` pass lowers this into explicit conditional branches in `runtime_mir`.
- **Two-Sided Behavioral Equivalence Validator (`validateBuiltToPostCleanupAdmittedQ1_sound`)**: Rather than trusting compiler passes between `mir_built` and `runtime_mir` blindly or checking only a one-sided implication, `validateBuiltToPostCleanupAdmittedQ1` checks both `wfDualBodyPackage`, structural lowering correspondence (`validateBuiltToPostCleanupPackage`), and two-sided behavioral equivalence across all bounded initial states and unwind flags (`checkBuiltToPostCleanupBehavioralEquivFailClosed_sound`). Four negative controls in `h6_all_four_lowering_validator_controls_verified` confirm that omitted drops, altered unwind targets, dropped `PlaceMention` statements, or mismatched `mir_built` / `runtime_mir` pairs are rejected.
- **Three-Layer Proof Ergonomics and Sound Structured Views (`h5_three_layer_proof_comparison_and_structured_view_correspondence`, `reconstructVerifiedStructuredViewInEnv_general_step_slot_sound`, `reconstructVerifiedStructuredViewInEnv_general_client_contract_sound`)**:
  - Proving `step_generic_slot` and `client_contract_user` directly over raw basic-block steps (`runSteps`), over a weakest-precondition calculus (`wpStateSteps_sound_on_transactional_step`), and over a reconstructed `StructuredStmt` tree yields identical operational contracts.
  - Crucially, `control_n6_naive_structured_recognizer_unsound_on_event_mutation_repaired_by_verified_recognizer` ([`support/AnnealResearch/StatefulGenericLibraryH3H7Controls.lean`](support/AnnealResearch/StatefulGenericLibraryH3H7Controls.lean)) demonstrates that a naive structured-view recognizer that checks only entry/exit signatures accepts a CFG whose event log order is mutated, whereas `reconstructVerifiedStructuredViewInEnv` ([`support/AnnealResearch/PR86AuditRepairs.lean`](support/AnnealResearch/PR86AuditRepairs.lean)) verifies symbolic path equivalence against `evalBodySymbolicInEnv` for arbitrary caller environments and rejects the mutated CFG.
- **Explicit Taxonomy of Architectural vs. Operational Claims (`CompilerIntegrationDossier.lean`, `CompilerIntegrationDossierControls.lean`)**:
  - [`support/AnnealResearch/CompilerIntegrationDossier.lean`](support/AnnealResearch/CompilerIntegrationDossier.lean) and [`support/AnnealResearch/CompilerIntegrationDossierControls.lean`](support/AnnealResearch/CompilerIntegrationDossierControls.lean) formalize the architectural comparison across acquisition layers (`rustc_driver` vs. Charon vs. `rustc_public`), semantic boundaries (`mir_built` + `runtime_mir` with `-Z mir-preserve-ub`), interchange formats (`AMIRv3`), and proof representations, while enforcing via `control_n0_eight_status_taxonomy_never_conflates_meta_or_stopped_with_universal_operational` and `control_c1_boolean_architecture_catalog_classified_as_meta_model_with_explicit_d1_to_d5_residual_premises` that finite architectural trade-off tables are classified as `MetaModel` rather than universal operational theorems.

## Boundaries

- **`not examined`**:
  - Unsized coercions beyond single-slice tails (`[T]`), `dyn Trait` vtable layout entries, and inline assembly (`asm!`) semantics (inline assembly is explicitly rejected at `B1` by `control_b1_unsupported_inline_asm_rejected`).
  - General cyclic `StructuredStmt` reconstruction for arbitrary irreducible multi-exit loops (the verified `reconstructVerifiedStructuredViewInEnv` recognizer covers acyclic transactional control flow, while bounded and unbounded single-latch loops are verified directly on the CFG via `unbounded_period4_all_prefixes_running_and_enabled`).
- **`unknown`**:
  - Stability of `rustc_middle::mir` internal data structures across future nightly releases beyond `1.98.0-nightly` / `1.100.0-nightly` without updating the thin `direct_mir_driver_v4.rs` adapter.
- **`known not to apply`**:
  - Default `rustc` MIR compilation (without `-Z mir-preserve-ub`) does not preserve wildcard/underscore raw-pointer dereference statements (`let _ = *ptr;`) and therefore cannot be used for raw-pointer validity proofs (`control_b5_default_mir_passes_b1_b2_but_fails_raw_ptr_adequacy`).
  - External `.rlib` metadata MIR (`optimized_mir`) cannot discharge pre-optimization UB or `StorageLive` / `StorageDead` obligations because MIR optimizations elide dead reads and storage markers (`control_external_rlib_optimized_mir_rejected_for_pre_optimization_ub_and_storage_obligations`).
- **`unsupported`**:
  - The `direct_mir_driver_v4.rs` v4 exporter fails closed (exit code `2`, deleting any stale `.amir` output) when encountering constructs outside the supported operational subset, as verified by empirical negative controls in [`support/capture-v4-ledger.json`](support/capture-v4-ledger.json): unsupported `Rvalue` variants (`control_unsupported_rvalue_reject`), unsupported pointer casts (`control_unsupported_rvalue_cast_reject`), non-`Guard` drop types (`control_wrong_drop_u32_reject`), unsupported projections (`control_unsupported_projection_reject`), and unsupported terminators (`control_unsupported_terminator_reject`).

## Evidence

| Artifact | Path | Description & SHA-256 |
| :--- | :--- | :--- |
| Lean Execution Ledger | [`support/lean-execution-ledger.json`](support/lean-execution-ledger.json) | Fresh Lean `4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) verification ledger across all 17 modules in topological dependency order (`exit_code: 0`, zero custom axioms). |
| `AMIRv2` Wire Parser & Controls | [`support/AnnealResearch/MirWireParser.lean`](support/AnnealResearch/MirWireParser.lean), [`support/AnnealResearch/MirWireParserControls.lean`](support/AnnealResearch/MirWireParserControls.lean) | Total `AMIRv2` binary wire parser (`9fa2f09b...`) and negative controls (`50f8cd59...`). |
| `AMIRv3` Substantive Byte Parser & Controls | [`support/AnnealResearch/SubstantiveMirByteParser.lean`](support/AnnealResearch/SubstantiveMirByteParser.lean), [`support/AnnealResearch/SubstantiveMirByteParserControls.lean`](support/AnnealResearch/SubstantiveMirByteParserControls.lean) | Full `AMIRv3` CFG byte parser (`9e24337c...`) and `B1`/`B2`/`B3`/`B5` compilation-binding controls (`270774cc...`). |
| Semantic Vertical Slice & Controls | [`support/AnnealResearch/SemanticVerticalSliceCore.lean`](support/AnnealResearch/SemanticVerticalSliceCore.lean), [`support/AnnealResearch/SemanticVerticalSliceZerocopy.lean`](support/AnnealResearch/SemanticVerticalSliceZerocopy.lean), [`support/AnnealResearch/SemanticVerticalSlice.lean`](support/AnnealResearch/SemanticVerticalSlice.lean), [`support/AnnealResearch/SemanticVerticalSliceControlsCleanup.lean`](support/AnnealResearch/SemanticVerticalSliceControlsCleanup.lean), [`support/AnnealResearch/SemanticVerticalSliceControls.lean`](support/AnnealResearch/SemanticVerticalSliceControls.lean) | End-to-end operational proofs from decoded `.amir` bytes for cleanup/unwind, `PlaceMention`, unbounded period-4 loops, and `zerocopy` alignment/count slices, plus 8 negative mutant controls. |
| Lowering Validator & Structured Views | [`support/AnnealResearch/StatefulGenericLibraryH3H7Core.lean`](support/AnnealResearch/StatefulGenericLibraryH3H7Core.lean), [`support/AnnealResearch/StatefulGenericLibraryH3H7.lean`](support/AnnealResearch/StatefulGenericLibraryH3H7.lean), [`support/AnnealResearch/StatefulGenericLibraryH3H7Controls.lean`](support/AnnealResearch/StatefulGenericLibraryH3H7Controls.lean), [`support/AnnealResearch/PR86AuditRepairs.lean`](support/AnnealResearch/PR86AuditRepairs.lean) | Two-sided `mir_built`-to-post-cleanup validator, 3-layer proof comparison, environment-parameterized structured view recognizer (`reconstructVerifiedStructuredViewInEnv`), and `#[repr(C)]` / `#[repr(C, packed(2))]` unsized tail layout laws. |
| Frontend Dossier & Controls | [`support/AnnealResearch/CompilerIntegrationDossier.lean`](support/AnnealResearch/CompilerIntegrationDossier.lean), [`support/AnnealResearch/CompilerIntegrationDossierControls.lean`](support/AnnealResearch/CompilerIntegrationDossierControls.lean) | Formalized frontend architecture decision matrix and 8-status claim taxonomy controls. |
| Rust `AMIRv3` Exporter Driver | [`support/direct_mir_driver_v4.rs`](support/direct_mir_driver_v4.rs) | `rustc_driver` implementation (`0159d185414df33e373d6a8982ef34cfc7af7bc019e2724856830b8c73ae93c8`) emitting `.amir` v3 binary packages and JSON sidecars. |
| Empirical Capture & Check Ledgers | [`support/capture-v4-ledger.json`](support/capture-v4-ledger.json), [`support/substantive-mir-byte-parser-check-results.json`](support/substantive-mir-byte-parser-check-results.json), [`support/substantive-mir-byte-parser-protocol.md`](support/substantive-mir-byte-parser-protocol.md) | Empirical `rustc` capture ledger (`98b30bcb...`) covering 7 positive runs, 10 fail-closed driver controls, and 15 byte/semantic mutant artifacts, plus protocol specification. |

## Revalidation

To re-verify the complete 17-module Lean 4 proof closure from the copied sources in [`support/AnnealResearch/`](support/AnnealResearch/) using Lean `4.34.1`:

```bash
mkdir -p /tmp/r16-build/AnnealResearch
for mod in \
  Execution \
  MirWireParser \
  MirWireParserControls \
  SubstantiveMirByteParser \
  SubstantiveMirByteParserControls \
  SemanticVerticalSliceCore \
  SemanticVerticalSliceZerocopy \
  SemanticVerticalSlice \
  SemanticVerticalSliceControlsCleanup \
  SemanticVerticalSliceControls \
  CargoWorkspaceIntegration \
  StatefulGenericLibraryH3H7Core \
  StatefulGenericLibraryH3H7 \
  StatefulGenericLibraryH3H7Controls \
  PR86AuditRepairs \
  CompilerIntegrationDossier \
  CompilerIntegrationDossierControls; do
  LEAN_PATH=/tmp/r16-build lean -j1 -M768 \
    -o "/tmp/r16-build/AnnealResearch/${mod}.olean" \
    "support/AnnealResearch/${mod}.lean"
done
```

Expected outcome: Every invocation exits with code `0`, emits `#print axioms` lines referencing at most `[propext, Quot.sound]`, and matches the module SHA-256 digests recorded in [`support/lean-execution-ledger.json`](support/lean-execution-ledger.json).
