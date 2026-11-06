# Verified AMIR Binary Wire Format, LLBC Decoding and Binding Boundaries, and Parser Admission Contracts

## Summary

Eliminating unverified text/JSON parsing and schema-only AST decoding from a formal Rust verification pipeline requires separating syntactic byte recognition, structural graph closure, and compilation provenance binding across three complementary layers:

1. **Verified Canonical Binary Wire Format (`AMIRv2` / `AMIRv3`), Two-Sided Lowering Validation, and Sound Structured Proof Views**: Rather than starting Lean 4 proofs at an already-parsed JSON AST (`json_ast_start_leaves_bytes_to_json_unproved_control`), the `AMIRv2` and `AMIRv3` binary wire formats (`support/AnnealResearch/MirWireParser.lean`, `support/AnnealResearch/SubstantiveMirByteParser.lean`) encode compiler-extracted Mid-Level Intermediate Representation (MIR) as canonical little-endian byte streams (`AMIR\x03\x00\x00\x00`) with physical byte bounds (`b < 256`), exact end-of-input consumption (`pos == bytes.length`), 32-bit FNV-1a payload checksums, and structural/call-closure checks (`wfPackage && closedCallersPackage`), machine-checked in Lean `4.34.1` for universal round-trip, injectivity, and canonical byte uniqueness (`universal_accepted_byte_soundness`, `universal_accepted_package_canonical_unique`). A three-stage compilation-binding predicate (`endorsedCompilationBinding`: `Stage3a` header self-consistency, `Stage3b` sidecar SHA-256 binding, `Stage3c` trusted `rustc_driver` invocation with `-Z mir-preserve-ub`) binds accepted bytes to the exact compilation unit and flags. Above the decoded CFG, a fail-closed two-sided `mir_built`-to-post-cleanup validator (`validateBuiltToPostCleanupAdmittedQ1_sound`) and an environment-parameterized structured view recognizer (`reconstructVerifiedStructuredViewInEnv`) verify normal and unwind drop semantics (`ElaborateDrops`), wildcard raw-pointer reads (`PlaceMention`), and `zerocopy` alignment/slice/unsized-tail layout laws (`#[repr(C)]` and `#[repr(C, packed(2))]`).
2. **Charon LLBC JSON Decoding, Envelope Information Loss, and Best-Effort Checking Boundaries (`1aebab5f` vs. `9e95cf31` and Aeneas `21345f80`)**: At both Aeneas's compatible Charon pin (`AeneasVerif/charon@1aebab5f03a58067e5dc0ede2fec584117f54964`) and upstream comparison pin (`AeneasVerif/charon@9e95cf318e3a2964fcf5e03104cde5b718f98ea5`, both reporting `supported_charon_version = "0.1.291"`), the OCaml top-level JSON decoder (`OfJson.crate_of_json`) matches `` `Assoc [("charon_version", charon_version); ("translated", translated); _] `` and **discards the third field (`has_errors`)**, preventing Aeneas (`AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`) from recovering the crate-level partial-extraction indicator from the returned `crate` record. Generated decoders (`Generated_OfJson.ml`), generative integer identifier wrappers (`Identifiers.IdGen()`), de Bruijn binder representations (`de_bruijn_var`), and Rust's best-effort post-translation typechecker (`typecheck_and_unify.rs`) recognize constructor shapes and catch selected mismatches without establishing declaration closure, index-map uniqueness, or intrinsic typing, while Aeneas erases body regions (`erase_body_regions`) before later implied-bound checks and defaults `sanity_checks` and `type_check_pure_code` to `false`.
3. **Prior-Art Verified Parser Contracts (Œuf, Narcissus, Verdict, EverParse)**: Verified serialization and parsing systems prove distinct formal propositions: Œuf (`uwplse/oeuf@f3e4d236465ba872d1f1b8229548fa0edf8f7a3f`) proves a serializer-produced AST round trip (`parse_print_id`, `parse_pretty_id`); Narcissus (`mit-plv/fiat@b7757d28f68c39c3c58192a27f217064b0b35e3b`, ICFP 2019) relates source views, prefix-plus-remainder byte decompositions, and stateful encoder/decoder caches (`CorrectDecoder`, `CorrectEncoder`, `CorrectDecoderNone`); Verdict (`secure-foundations/verdict@9bc18bc5a287c1608dcb74a6eee7b9ca94a62b67`, USENIX Security 2025) proves X.509 DER soundness, completeness, non-malleability (byte uniqueness), and nonempty-suffix rejection (`parse_x509_der`); and EverParse (`project-everest/everparse@ad9414befa0241e8b3a9c84f9ee979445bad85d4`) separates default prefix validation from `--complete_wrappers` buffer exhaustion, machine-arithmetic overflow obligations (`EverParse3d.Prelude.fsti`), and strong vs. weak/in-place hash-checking modes (`HashCheck.fs`). An exhaustive 256-value finite witness (`serialization_witness.py`) demonstrates that round-trip inversion alone does not force trailing-byte rejection or duplicate-key rejection.

## Applicability

This report synthesizes three investigations across verified MIR binary wire parsing, Charon/Aeneas LLBC decoding and binding, and prior-art verified parser contracts:

1. **Verified `AMIRv2` / `AMIRv3` Binary Wire Format, Lowering Validation, and Structured Proof Views (`2026-10-24`)**:
   - **Rust Toolchain**: `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `x86_64-unknown-linux-gnu`, binary SHA-256 `c0575015cb2b0648bff9042dc2e68f139fb0b16c981cdca96efba2e91ac409d8`), compared against `charon 0.1.210` (`1e08453924610c19d74c245a7308f17c1008e2db`, binary SHA-256 `88542ca0b2bf52429fd5b9f2bf29f0f1183ba2279854567ab13d82bc789a8d47`).
   - **Proof Assistant**: Lean `4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`, binary SHA-256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`), verified across all 17 modules under `lean -j1 -M768` with zero `sorry`/`admit` tokens and only `[propext, Quot.sound]`.
2. **Charon LLBC Decoding, Binding, and Partial-Result Admission (`2026-10-15`)**:
   - Directly examines `AeneasVerif/charon@1aebab5f03a58067e5dc0ede2fec584117f54964` (pinned by `AeneasVerif/aeneas` `charon-pin`), `AeneasVerif/charon@9e95cf318e3a2964fcf5e03104cde5b718f98ea5` (upstream comparison), `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77` (`Main.ml`, `Translate.ml`, `PrePasses.ml`, `Extract.ml`, `TypesAnalysis.ml`, `SymbolicToPureTypes.ml`), and Lean `4.35.0` (`leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) collection refinement laws (`HashMap`, `DHashMap`, `ExtHashMap`, `TreeMap`, `Array`).
   - At both Charon pins, the selected OCaml decoder/generated representations, identifier/substitution modules, and Rust `export.rs`/`bodies.rs`/`vars.rs`/`substitute.rs` blobs are byte-identical, whereas `charon/src/transform/typecheck_and_unify.rs` differs between pins and is analyzed at both revisions. Aeneas `Main.ml` loads `.llbc` via `OfJson.crate_of_json_file` (which explicitly rejects Postcard files, lines 55–67).
3. **Prior-Art Verified Parser Round Trips, Admission, and Byte Meaning (`2026-10-14`)**:
   - Examines `uwplse/oeuf@f3e4d236465ba872d1f1b8229548fa0edf8f7a3f`, `mit-plv/fiat@b7757d28f68c39c3c58192a27f217064b0b35e3b` (Narcissus, plus Delaware et al., ICFP 2019 Article 82, DOI `10.1145/3341686`), `secure-foundations/verdict@9bc18bc5a287c1608dcb74a6eee7b9ca94a62b67` (plus USENIX Security 2025), and `project-everest/everparse@ad9414befa0241e8b3a9c84f9ee979445bad85d4` (plus EverParse 3d manual for releases `2025.05.20` or later), paired with `serialization_witness.py` executed under Python `3.14.8 -B -I`.

## Findings

### 1. Canonical Binary Wire Format (`AMIRv2` / `AMIRv3`), Compilation Binding, and Sound Structured Proof Views

#### 1.1 Canonical Binary Wire Format (`AMIRv2` / `AMIRv3`) Eliminates the Unverified JSON Parser Gap

`Basis: source + execution + derived`

Starting verification from an in-memory AST produced by an unverified JSON parser leaves byte-to-AST decoding outside the kernel's trusted computing base (`json_ast_start_leaves_bytes_to_json_unproved_control` in [`support/AnnealResearch/MirWireParserControls.lean`](support/AnnealResearch/MirWireParserControls.lean)). In [`support/AnnealResearch/MirWireParser.lean`](support/AnnealResearch/MirWireParser.lean) and [`support/AnnealResearch/SubstantiveMirByteParser.lean`](support/AnnealResearch/SubstantiveMirByteParser.lean), the binary wire formats (`AMIRv2` and `AMIRv3`) replace text parsing with an explicit, tag-delimited, little-endian `u32` byte grammar:

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

#### 1.2 Three-Stage Compilation Binding (`B1`, `B2`, `B3`) Separates Structural Validity from Provenance

`Basis: source + execution + derived`

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

#### 1.3 Semantic Necessity of `-Z mir-preserve-ub`, Post-Cleanup Unwind Edges (`runtime_mir`), and `zerocopy` Tail Layouts

`Basis: source + execution + derived`

Empirical capture via [`support/direct_mir_driver_v4.rs`](support/direct_mir_driver_v4.rs) (recorded in [`support/capture-v4-ledger.json`](support/capture-v4-ledger.json)) and Lean proofs across [`support/AnnealResearch/SemanticVerticalSliceCore.lean`](support/AnnealResearch/SemanticVerticalSliceCore.lean), [`support/AnnealResearch/SemanticVerticalSliceZerocopy.lean`](support/AnnealResearch/SemanticVerticalSliceZerocopy.lean), [`support/AnnealResearch/SemanticVerticalSlice.lean`](support/AnnealResearch/SemanticVerticalSlice.lean), and [`support/AnnealResearch/SemanticVerticalSliceControls.lean`](support/AnnealResearch/SemanticVerticalSliceControls.lean) establish three compiler-boundary invariants:

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

#### 1.4 Fail-Closed Two-Sided `mir_built`-to-Post-Cleanup Lowering Validation and Sound Structured Views

`Basis: source + execution + derived`

[`support/AnnealResearch/StatefulGenericLibraryH3H7.lean`](support/AnnealResearch/StatefulGenericLibraryH3H7.lean), [`support/AnnealResearch/StatefulGenericLibraryH3H7Controls.lean`](support/AnnealResearch/StatefulGenericLibraryH3H7Controls.lean), and [`support/AnnealResearch/PR86AuditRepairs.lean`](support/AnnealResearch/PR86AuditRepairs.lean) evaluate how pre-elaboration `mir_built` relates to post-cleanup `runtime_mir` and how structured proof obligations are discharged above the raw CFG:

- **Conditional vs. Unconditional Drop Elaboration (`n3_built_graph_conditional_vs_unconditional_drop_semantics_and_elaboration_agreement`)**: In `mir_built`, a drop edge following a conditional move requires dynamic drop-flag tracking; `rustc`'s `ElaborateDrops` pass lowers this into explicit conditional branches in `runtime_mir`.
- **Two-Sided Behavioral Equivalence Validator (`validateBuiltToPostCleanupAdmittedQ1_sound`)**: `validateBuiltToPostCleanupAdmittedQ1` checks `wfDualBodyPackage`, structural lowering correspondence (`validateBuiltToPostCleanupPackage`), and two-sided behavioral equivalence across all bounded initial states and unwind flags (`checkBuiltToPostCleanupBehavioralEquivFailClosed_sound`). Four negative controls in `h6_all_four_lowering_validator_controls_verified` confirm that omitted drops, altered unwind targets, dropped `PlaceMention` statements, or mismatched `mir_built` / `runtime_mir` pairs are rejected.
- **Three-Layer Proof Ergonomics and Sound Structured Views (`h5_three_layer_proof_comparison_and_structured_view_correspondence`, `reconstructVerifiedStructuredViewInEnv_general_step_slot_sound`, `reconstructVerifiedStructuredViewInEnv_general_client_contract_sound`)**:
  - Proving `step_generic_slot` and `client_contract_user` directly over raw basic-block steps (`runSteps`), over a weakest-precondition calculus (`wpStateSteps_sound_on_transactional_step`), and over a reconstructed `StructuredStmt` tree yields identical operational contracts.
  - `control_n6_naive_structured_recognizer_unsound_on_event_mutation_repaired_by_verified_recognizer` ([`support/AnnealResearch/StatefulGenericLibraryH3H7Controls.lean`](support/AnnealResearch/StatefulGenericLibraryH3H7Controls.lean)) demonstrates that a naive structured-view recognizer checking only entry/exit signatures accepts a CFG whose event log order is mutated, whereas `reconstructVerifiedStructuredViewInEnv` ([`support/AnnealResearch/PR86AuditRepairs.lean`](support/AnnealResearch/PR86AuditRepairs.lean)) verifies symbolic path equivalence against `evalBodySymbolicInEnv` for arbitrary caller environments and rejects the mutated CFG.
- **Explicit Taxonomy of Architectural vs. Operational Claims (`CompilerIntegrationDossier.lean`, `CompilerIntegrationDossierControls.lean`)**:
  - [`support/AnnealResearch/CompilerIntegrationDossier.lean`](support/AnnealResearch/CompilerIntegrationDossier.lean) and [`support/AnnealResearch/CompilerIntegrationDossierControls.lean`](support/AnnealResearch/CompilerIntegrationDossierControls.lean) formalize the architectural comparison across acquisition layers (`rustc_driver` vs. Charon vs. `rustc_public`), semantic boundaries (`mir_built` + `runtime_mir` with `-Z mir-preserve-ub`), interchange formats (`AMIRv3`), and proof representations, enforcing via `control_n0_eight_status_taxonomy_never_conflates_meta_or_stopped_with_universal_operational` and `control_c1_boolean_architecture_catalog_classified_as_meta_model_with_explicit_d1_to_d5_residual_premises` that finite architectural trade-off tables are classified as `MetaModel` rather than universal operational theorems.

---

### 2. Charon LLBC Decoding, Binding, and Partial-Result Admission at `1aebab5f` and `9e95cf31`

#### 2.1 Top-Level JSON Envelope Information Loss (`has_errors` Discarded in `OfJson.crate_of_json`)

`Basis: source + documentation + derived`

In Charon's Rust exporter ([`charon/src/export.rs` at compatible pin `1aebab5f`](https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon/src/export.rs), lines 14–83, and [upstream pin `9e95cf31`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/export.rs), lines 14–83), `CrateData` serializes `charon_version`, `translated`, and `has_errors` (taken from `TransformCtx.has_errors()`, documenting that `has_errors = true` means the crate is only a partial description of the input). However, the OCaml top-level JSON decoder ([`charon-ml/src/OfJson.ml` at `1aebab5f`](https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon-ml/src/OfJson.ml), lines 21–53, and [`9e95cf31`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon-ml/src/OfJson.ml), lines 21–53; [`CharonVersion.ml`](https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon-ml/src/CharonVersion.ml), lines 1–3) pattern-matches:

```ocaml
`Assoc [("charon_version", charon_version); ("translated", translated)]
`Assoc [("charon_version", charon_version); ("translated", translated); _]
```

It checks `charon_version = CharonVersion.supported_charon_version` (`"0.1.291"` at both pins, showing that the version string cannot distinguish commits), decodes `translated`, and **ignores both the key and value of the third field (`has_errors`)**. Furthermore, `translated_crate_of_json` ([`charon-ml/src/generated/Generated_OfJson.ml`](https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon-ml/src/generated/Generated_OfJson.ml), lines 4021–4123) parses `runtime_checks` and `files`, but the wrapper constructs a reduced client `crate` record containing only options, target information, names, ordered declarations, and declaration maps. When Aeneas ([`src/Main.ml`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Main.ml), lines 583–602, 755–812; [`charon-pin`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/charon-pin)) loads the returned `crate`, its final `has_errors` flag is computed from Aeneas's own `Errors.error_list` after translation rather than the discarded upstream envelope flag.

#### 2.2 Structural Schema Recognition vs. Semantic Well-Formedness, Body Variants, and Identifier/Binder Discipline

`Basis: source + documentation + derived`

In [`Generated_OfJson.ml`](https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon-ml/src/generated/Generated_OfJson.ml) (provenance lines 1–27, `dedup_val_of_json` lines 25–50, `opt_indexed_map_of_json` lines 61–69, `binder_of_json` lines 315–329, `de_bruijn_var_of_json` lines 692–715, `index_vec_of_json` lines 965–976, `trait_ref_kind_of_json` lines 1535–1617, `body_of_json` lines 2347–2382, `fun_decl_of_json` lines 2825–2845, `index_map_of_json` lines 3074–3087, `item_meta_of_json` lines 3163–3209) and [`DeserializationCtx.ml`](https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon-ml/src/DeserializationCtx.ml) (lines 23–42):

| Representation case | Checked by the inspected decoder | Still requires separate evidence |
| --- | --- | --- |
| Scalar identifier | JSON integer and identifier-specific wrapper | Nonnegative/range constraints and reference validity |
| Index vector | List of values; index decoder parameter unused | Each reference is in range and each stored declaration ID agrees with its slot |
| Optional indexed map | List of optional values, converted to map keyed by list positions | Meaning of holes, closure of references to absent entries, key/record-ID coherence |
| Index map | List of key/value pairs | Key uniqueness or semantic consistency of target mappings |
| Binder | Parameter record and payload decoded; serialized `kind` ignored in this decoder | Scope correctness and compatibility of uses under that binder |
| Trait reference | Proof-form constructor plus claimed trait declaration reference decoded | The proof form establishes that claimed trait with the instantiated arguments |

- **Body Variants and Per-Item Error Metadata**: Rust [`charon/src/ast/bodies.rs`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/ast/bodies.rs) (lines 27–81) and OCaml `body_of_json` distinguish structured bodies, unstructured bodies, `TargetDispatch`, extern/intrinsic bodies, intentionally opaque bodies, missing bodies, and translation-error bodies, while `item_meta_of_json` preserves per-item `has_errors`, opacity, and attributes. In Aeneas, [`src/Translate.ml`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Translate.ml) (`translate_function_to_symbolics`, lines 22–51) symbolically executes `StructuredBody` and turns `TargetDispatchBody` into `SymbolicAst.TargetDispatch`; [`src/PrePasses.ml`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/PrePasses.ml) (lines 2343–2364) replaces failing bodies with `ErrorBody`; and [`src/extract/Extract.ml`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/extract/Extract.ml) (lines 703–741) can emit `sorry`/admission forms when a pure body is absent.
- **Identifiers, Binders, and Substitution**: [`charon-ml/src/Identifiers.ml`](https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon-ml/src/Identifiers.ml) (lines 3–31, 174–297) uses generative `IdGen()` functors to separate identifier kinds in OCaml types, but decodes IDs via `OfJsonBasic.int_of_json` without nonnegativity or bounds checks. [`Generated_Types.ml`](https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon-ml/src/generated/Generated_Types.ml) (lines 45–84) represents `de_bruijn_var` as `Bound (depth, variable_id) | Free variable_id`. Rust [`charon/src/ast/type_level/vars.rs`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/ast/type_level/vars.rs) (`get_var`, lines 475–496), OCaml [`charon-ml/src/Substitute.ml`](https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon-ml/src/Substitute.ml) (`shift_subst` and `error_sb_subst`, lines 74–211), and Rust [`charon/src/ast/type_level/substitute.rs`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/ast/type_level/substitute.rs) (lines 74–113, 252–328) implement depth-tracking substitution and runtime lookup (`Option` / `GenericsMismatch`) without intrinsic scope witnesses.
- **Best-Effort Rust Typechecker (`typecheck_and_unify.rs`) and Aeneas Information-Erasing Prepasses**: In Charon's [`typecheck_and_unify.rs` at `1aebab5f`](https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon/src/transform/typecheck_and_unify.rs) (lines 769–844) and [`9e95cf31`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/transform/typecheck_and_unify.rs) (permissive ADT matching lines 95–142, `match_trait_ref_against_itself` lines 175–236, binding checks lines 510–555, builtin trait exceptions lines 610–658, pass entry lines 779–853), `Check::PostTranslation` and `PostTransformation` skip items where `item_meta.has_errors` is already set, unify body regions in-place, and explicitly err toward acceptance in `match_tys` and unhandled trait forms. In Aeneas, [`PrePasses.ml`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/PrePasses.ml) (`erase_body_regions`, lines 44–87) erases region variables and local types before later higher-ranked/free lifetime guards ([`src/llbc/TypesAnalysis.ml`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/llbc/TypesAnalysis.ml), lines 978–1082), while pure-variable closure (`sanity_checks` in [`Translate.ml`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Translate.ml), lines 53–98) and pure expression type-checking (`type_check_pure_code` in [`src/symbolic/SymbolicToPureTypes.ml`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/symbolic/SymbolicToPureTypes.ml), lines 1293–1303) both default to `false`.

#### 2.3 Representation Trade-Offs and Collection Refinement Laws

`Basis: source + derived`

| Representation style | What it can make explicit | Remaining obligation/tradeoff |
| --- | --- | --- |
| Intrinsically typed/scoped syntax | Constructors carry typing/scope indices, preventing many malformed internal terms | Decoding must produce witnesses; transformations transport indices; richer dependent invariants can complicate efficient graph operations. |
| Raw syntax paired with well-formedness proofs | Existing simple storage plus a separately stated contextual predicate | Every consumer must retain the witness and every transformation preserve it; reflection/checker correctness still needs proof. |
| Raw syntax with verified validators | Efficient decoding/storage, with a small acceptance theorem tied to validator success | The validator must cover the precise semantic preconditions and completeness policy; a shape decoder alone is insufficient. |
| Inspected OCaml/Rust implementation | Kind-separated IDs, binder-aware helpers, selected dynamic checks, typed annotations, error recovery | These safeguards do not intrinsically attach a verified membership/typing witness to every term. |

The companion [`finite-map-graph-comparison.md`](support/llbc-decoding-binding-admission-1aebab5f-9e95cf31/finite-map-graph-comparison.md) and [`finite-map-laws.json`](support/llbc-decoding-binding-admission-1aebab5f-9e95cf31/finite-map-laws.json) map Charon/Aeneas OCaml container wrappers against Lean `4.35.0` (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) `HashMap`, `DHashMap`, `ExtHashMap`, `TreeMap`, and `Array` lookup, domain-preservation, quotient-equality, ordered-enumeration, and SCC laws.

---

### 3. Prior-Art Verified Parser Round Trips, Admission Contracts, and Byte Meaning

`Basis: source + documentation + execution + derived`

1. **Œuf Serializer-to-Parser Round Trip (`uwplse/oeuf@f3e4d236465ba872d1f1b8229548fa0edf8f7a3f`)**:
   - `src/Pretty.v:2258-2281` (blob `f7b0b57b135771118ba4faff82c0a7e93d702372`) defines `print`/`pretty` and `parse` for `compilation_unit` and proves `parse_print_id` and `parse_pretty_id` (parsing a serializer-generated string returns `Some` of the same AST; invoked by `src/OeufDriver.ml:374-378`, blob `c246fd446d5d7e12bf151938d4d98d1d3af11211`, with unpinned `PrettyParsing` clone in `scripts/build_pretty_parsing.sh`, blob `3051bd7d32c65a04ad93c2b7a0c6141ae0406143`). Parse-after-print preserves trusted serializer outputs but does not by itself enforce canonical byte uniqueness or reject trailing bytes on arbitrary inputs.
2. **Narcissus Relational Formats and Stateful Caches (`mit-plv/fiat@b7757d28f68c39c3c58192a27f217064b0b35e3b`)**:
   - In the [Narcissus ICFP 2019 paper](https://adam.chlipala.net/papers/NarcissusICFP19/NarcissusICFP19.pdf) (§2.2, Definitions 2.1–2.2, Theorems 2.3–2.4, pp. 10–11) and `src/Narcissus/Common/Specs.v:40-110` (blob `49a3488b0bfe1bcc6f2b3d07ac3bd93e6c6741ec`), `CorrectDecoder` (lines 40–68), `CorrectEncoder` (lines 70–79), and `CorrectDecoderNone` (lines 87–110) relate a view `V`, consumed byte prefix + remainder decomposition, `View_Predicate`, and encoder/decoder cache invariants (allowing intentionally non-unique padding or compressed back-references unless format uniqueness is proved).
3. **Verdict Complete X.509 DER Non-Malleability and Prefix Security (`secure-foundations/verdict@9bc18bc5a287c1608dcb74a6eee7b9ca94a62b67`)**:
   - In `verdict-parser/src/lib.rs:43-96` (blob `5a8584d6cc0564513207cdbde2f4f5188995f2bf`, over `common/vest.rs` blob `76216c3455a479363eb449a22117284506523331`) and the [Verdict USENIX Security 2025 paper](https://verified.how/papers/verdict.pdf) (§4.1, PDF p. 6), `parse_x509_der` combines soundness and completeness with respect to `spec_parse_x509_der`, **non-malleability** (any two byte slices fitting `usize::MAX` that decode to the same spec value are byte-identical), and **prefix security** (any non-empty suffix appended to a valid encoding fitting `usize::MAX` fails).
4. **EverParse Prefix vs. Complete-Buffer Wrappers, Machine Arithmetic, and Hash-Checking Modes (`project-everest/everparse@ad9414befa0241e8b3a9c84f9ee979445bad85d4`)**:
   - In the [EverParse 3d language manual](https://project-everest.github.io/everparse/3d-lang.html), [3d API manual](https://project-everest.github.io/everparse/3d.html), and `lib/everparse/3d/EverParse3d.Prelude.fsti:270-299` (blob `27c2231886003b7e253781a178b19106cfff1347`), default entrypoint wrappers validate a prefix of the supplied buffer, whereas `--complete_wrappers` rejects trailing bytes (for buffer streams only), and integer constraints require machine-arithmetic overflow freedom. In [hash-checking mode](https://project-everest.github.io/everparse/3d.html#alternate-mode-hash-checking) (`src/3d/hashchk/HashCheck.fs:6-36`, blob `8195de81df3fa443b578f7ec6220ff3b000e98f1`), `strong` mode compares both source and generated C output hashes, whereas `weak`/`inplace` modes check only the source hash and explicitly void verification guarantees if the generated C output is modified.
5. **Certificate Admission Taxonomy and Exhaustive 256-Value Serialization Witness (`serialization_witness.py`)**:

| Input issue | Required admission rule |
|---|---|
| Truncation/trailing bytes | Chosen complete-input or framed-stream policy |
| Duplicate fields or identifiers | Reject ambiguity or define one explicit meaning and prove consumer agreement |
| Unknown fields/versions | Reject or implement a stated compatibility rule |
| Integer lengths/counts | Checked bounds and representation conversion before allocation/indexing |
| Cross-references | Resolved identity, existence, type and scope; cycle rules where relevant |
| Noncanonical byte encodings | Decide whether semantic equality suffices or unique bytes are required |
| Filesystem/stream changes | Relate consumed bytes and events to the artifacts named by the checker |

   - `serialization_witness.py` (`serialization-results.json`) exhaustively checks a 256-value domain: both a prefix decoder and a complete decoder invert the canonical 2-byte encoder (`parse(encode(v)) == v`), but the prefix decoder accepts arbitrary trailing bytes while only the complete decoder rejects them, and Python's standard JSON loader accepts duplicate keys (`{"a": 1, "a": 2}`) unless a strict object-pairs hook rejects duplicates.

## Boundaries

- **Known not to apply**:
  - Default `rustc` MIR compilation without `-Z mir-preserve-ub` drops wildcard/underscore raw-pointer reads (`PlaceMention(*ptr)`) and cannot discharge raw-pointer validity obligations (`control_b5_default_mir_passes_b1_b2_but_fails_raw_ptr_adequacy`).
  - External `.rlib` `optimized_mir` cannot discharge pre-optimization UB or `StorageLive`/`StorageDead` obligations (`control_external_rlib_optimized_mir_rejected_for_pre_optimization_ub_and_storage_obligations`).
  - Charon's OCaml JSON decoder (`OfJson.crate_of_json`) discards the top-level `has_errors` envelope field and therefore cannot by itself certify that an extracted crate had zero upstream errors.
  - Round-trip parser inversion (`parse(encode(x)) = Some x`) does not imply trailing-byte rejection, canonical byte uniqueness, duplicate-key rejection, or cross-reference graph closure unless those properties are proved explicitly (as in `SubstantiveMirByteParser.lean` and Verdict's `parse_x509_der`).
- **Unsupported in the inspected paths**:
  - `direct_mir_driver_v4.rs` fails closed (exit code `2`) on inline assembly (`0xFE`), unsupported `Rvalue` variants, unsupported pointer casts, non-`Guard` drop types, unsupported projections, and unsupported terminators (`support/capture-v4-ledger.json`).
  - Aeneas `OfJson.crate_of_json_file` rejects Postcard-encoded `.llbc` files (`OfJson.ml:55-67`).
- **Not examined**:
  - Unsized coercions beyond single-slice tails (`[T]`), `dyn Trait` vtable layout entries, general cyclic `StructuredStmt` reconstruction for arbitrary irreducible multi-exit loops, Charon's separate Postcard deserializer, and fresh execution of Œuf, Narcissus, Verdict, or EverParse toolchains.

## Evidence

| Artifact | Path | Description |
| :--- | :--- | :--- |
| Lean Execution Ledger | [`support/lean-execution-ledger.json`](support/lean-execution-ledger.json) | Fresh Lean `4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) verification ledger across all 17 `AnnealResearch` modules (`exit_code: 0`, zero custom axioms). |
| `AMIRv2` & `AMIRv3` Byte Parsers & Controls | [`support/AnnealResearch/MirWireParser.lean`](support/AnnealResearch/MirWireParser.lean), [`support/AnnealResearch/MirWireParserControls.lean`](support/AnnealResearch/MirWireParserControls.lean), [`support/AnnealResearch/SubstantiveMirByteParser.lean`](support/AnnealResearch/SubstantiveMirByteParser.lean), [`support/AnnealResearch/SubstantiveMirByteParserControls.lean`](support/AnnealResearch/SubstantiveMirByteParserControls.lean) | Total `AMIRv2`/`AMIRv3` binary wire parsers, universal round-trip/injectivity/canonical-uniqueness theorems, and `B1`/`B2`/`B3`/`B5` compilation-binding controls. |
| Semantic Vertical Slice & Lowering Proofs | [`support/AnnealResearch/SemanticVerticalSliceCore.lean`](support/AnnealResearch/SemanticVerticalSliceCore.lean), [`support/AnnealResearch/SemanticVerticalSliceZerocopy.lean`](support/AnnealResearch/SemanticVerticalSliceZerocopy.lean), [`support/AnnealResearch/SemanticVerticalSlice.lean`](support/AnnealResearch/SemanticVerticalSlice.lean), [`support/AnnealResearch/SemanticVerticalSliceControlsCleanup.lean`](support/AnnealResearch/SemanticVerticalSliceControlsCleanup.lean), [`support/AnnealResearch/SemanticVerticalSliceControls.lean`](support/AnnealResearch/SemanticVerticalSliceControls.lean), [`support/AnnealResearch/StatefulGenericLibraryH3H7Core.lean`](support/AnnealResearch/StatefulGenericLibraryH3H7Core.lean), [`support/AnnealResearch/StatefulGenericLibraryH3H7.lean`](support/AnnealResearch/StatefulGenericLibraryH3H7.lean), [`support/AnnealResearch/StatefulGenericLibraryH3H7Controls.lean`](support/AnnealResearch/StatefulGenericLibraryH3H7Controls.lean), [`support/AnnealResearch/PR86AuditRepairs.lean`](support/AnnealResearch/PR86AuditRepairs.lean), [`support/AnnealResearch/CargoWorkspaceIntegration.lean`](support/AnnealResearch/CargoWorkspaceIntegration.lean), [`support/AnnealResearch/Execution.lean`](support/AnnealResearch/Execution.lean) | End-to-end operational proofs from decoded `.amir` bytes, two-sided `mir_built`-to-post-cleanup validator, environment-parameterized structured view recognizer, and `#[repr(C)]` / `#[repr(C, packed(2))]` unsized tail layout laws. |
| Frontend Dossier & Rust Exporter | [`support/AnnealResearch/CompilerIntegrationDossier.lean`](support/AnnealResearch/CompilerIntegrationDossier.lean), [`support/AnnealResearch/CompilerIntegrationDossierControls.lean`](support/AnnealResearch/CompilerIntegrationDossierControls.lean), [`support/direct_mir_driver_v4.rs`](support/direct_mir_driver_v4.rs), [`support/capture-v4-ledger.json`](support/capture-v4-ledger.json), [`support/substantive-mir-byte-parser-check-results.json`](support/substantive-mir-byte-parser-check-results.json), [`support/substantive-mir-byte-parser-protocol.md`](support/substantive-mir-byte-parser-protocol.md) | Formalized frontend architecture matrix, `rustc_driver` `AMIRv3` exporter, and empirical capture/mutant ledgers. |
| Charon / Aeneas LLBC Admission & Collection Matrices | [`support/llbc-decoding-binding-admission-1aebab5f-9e95cf31/source-reading.json`](support/llbc-decoding-binding-admission-1aebab5f-9e95cf31/source-reading.json), [`support/llbc-decoding-binding-admission-1aebab5f-9e95cf31/supplement-source-reading.json`](support/llbc-decoding-binding-admission-1aebab5f-9e95cf31/supplement-source-reading.json), [`support/llbc-decoding-binding-admission-1aebab5f-9e95cf31/admission-matrix.json`](support/llbc-decoding-binding-admission-1aebab5f-9e95cf31/admission-matrix.json), [`support/llbc-decoding-binding-admission-1aebab5f-9e95cf31/finite-map-graph-comparison.md`](support/llbc-decoding-binding-admission-1aebab5f-9e95cf31/finite-map-graph-comparison.md), [`support/llbc-decoding-binding-admission-1aebab5f-9e95cf31/finite-map-laws.json`](support/llbc-decoding-binding-admission-1aebab5f-9e95cf31/finite-map-laws.json) | Exact Git blob comparisons across Charon `1aebab5f` and `9e95cf31`, Aeneas `21345f80`, and Lean `4.35.0` collection laws. |
| Prior-Art Parser & Round-Trip Witness | [`support/parser-roundtrips-admission-and-byte-meaning/serialization_witness.py`](support/parser-roundtrips-admission-and-byte-meaning/serialization_witness.py), [`support/parser-roundtrips-admission-and-byte-meaning/serialization-results.json`](support/parser-roundtrips-admission-and-byte-meaning/serialization-results.json) | Exhaustive 256-value prefix vs. complete-buffer and duplicate-JSON-key witness. |

## Revalidation

1. **Re-verify the 17-module Lean `4.34.1` `AMIRv2`/`AMIRv3` wire parser, lowering validator, and structured proof view closure**:
   ```bash
   BUILD_DIR="${BUILD_DIR:-build/amir-verify}"
   mkdir -p "${BUILD_DIR}/AnnealResearch"
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
     LEAN_PATH="${BUILD_DIR}" lean -j1 -M768 \
       -o "${BUILD_DIR}/AnnealResearch/${mod}.olean" \
       "support/AnnealResearch/${mod}.lean"
   done
   ```
   Every invocation must exit with code `0`, emit `#print axioms` lines referencing at most `[propext, Quot.sound]`, and match [`support/lean-execution-ledger.json`](support/lean-execution-ledger.json).
2. **Re-verify the finite serialization witness and Charon/Aeneas/prior-art parser coordinates**:
   - Run `python3 -B -I support/parser-roundtrips-admission-and-byte-meaning/serialization_witness.py` and compare output against [`support/parser-roundtrips-admission-and-byte-meaning/serialization-results.json`](support/parser-roundtrips-admission-and-byte-meaning/serialization-results.json).
   - Diff `OfJson.crate_of_json`, `CharonVersion.ml`, `export.rs`, `Generated_OfJson.ml`, `typecheck_and_unify.rs`, and Aeneas `Main.ml`/`PrePasses.ml`/`Translate.ml` against the blob hashes in [`support/llbc-decoding-binding-admission-1aebab5f-9e95cf31/source-reading.json`](support/llbc-decoding-binding-admission-1aebab5f-9e95cf31/source-reading.json) whenever updating the Charon or Aeneas pin.
