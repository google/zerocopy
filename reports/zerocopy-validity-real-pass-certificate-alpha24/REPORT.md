# A real zerocopy scalar predicate through captured Charon and Aeneas boundaries

## Summary

The unchanged scalar-validity module from the PR stack was compiled in a small wrapper crate using the official legacy toolchain. Actual raw ULLBC, structured LLBC and emitted Lean definitions are retained. A checked certificate relates the selected Boolean predicate's complete imported instruction sequence to its emitted result for every byte input, retaining outside local values and liveness. Separate emitted Boolean and nonzero specifications were kernel checked.

The experiment now uses an actual zerocopy example. Its trusted import/capture boundary and small selected grammar remain explicit; it does not certify the whole crate or every internal pass.

## Applicability

The source is [zerocopy's validity module](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/zerocopy/src/util/validity/mod.rs), SHA-256 `b13d798f9bd7fc10f72256f5467d14deeaccd7e3dcb9247ee3f13944804eca76`. Its bytes were compared with the exact Git object before copying. The owned wrapper calls its Boolean, nonzero and slice-byte helpers; selected function ID 3 is bool_encoding. The wrapper crate changes the crate root/name and visibility context, so this is not the expanded, feature-configured whole zerocopy compilation unit.

The producer is the official alpha24 macOS aarch64 bundle, with Charon 0.1.210, bundled rustc 1.98.0-nightly f8a08b688 and Aeneas binary SHA-256 244397c4178329f2b8ab48240cd19dafd6511efb6c4e78be6345011ca8786f8e. Lean checking uses its 4.30.0-rc2 backend. This is different from the current patched Charon/Aeneas stack. The task-local loader recovery described in the [pair-update report](../aeneas-pair-returned-update-alpha24/REPORT.md) also applies; original producer code and checks were unchanged.

## Findings

### Exact production source and actual stage artifacts

Basis: source + execution.

The source Boolean predicate is `byte < 2` on its full u8 candidate domain. Its documentation keeps the raw integer until validation; physical reading through Maybe is a separate safety argument. The source module also contains `n != 0` and slice indexing helpers. No source annotations or function bodies were rewritten for extraction.

Both `raw-mir --ullbc` and `aeneas` preset captures used requested promoted MIR, no serialized-AST deduplication and error-on-warnings; both exited zero with has_errors false. The Aeneas capture prints original ULLBC, post-micro-pass ULLBC and final LLBC to stdout, with built LLBC in stderr. Aeneas emits six definitions, exiting zero. The package retains these actual artifacts and original hashes with explicit nonsemantic path normalization.

The selected helper has three locals: Boolean result 0, u8 argument 1 and u8 temporary 2. Its complete raw block is StorageLive(2), copy 1 to 2, less-than assignment moving 2 against u8 literal 2, StorageDead(2), return. The final structured body has exactly those five operations. The selected raw/final kind lists were compared, including the return; a plausible changed literal differs from the selected artifact. Other source functions and the wrapper call/unwind edges are retained provenance, not certified here.

### Imported state to emitted result

Basis: original definitions + kernel execution.

ImportedBool.lean interprets the selected instruction kinds with initialized local values, liveness and an event list. Copy requires live source/destination and initialized contents. The comparison consumes the temporary, produces a Boolean, then storage-dead clears it. The entry relation accepts every U8 argument, arbitrary prior result/temporary values and temporary liveness, arbitrary outside locals/liveness and prior events; result/argument locals have the declared live function-entry status.

`captured_raw_final` equates the actual selected unstructured and structured operation lists under that interpretation. `imported_emitted` relates their returned observation to the exact emitted bool_encoding definition for every such entry. `raw_domain` derives true exactly on integer representations zero or one. `frame_preserved` proves that every local other than 0, 1 and 2 retains its outside value/liveness. These are logical local-store facts, not a physical allocation/heap frame theorem. Source events are explicit in the imported interpretation; the pure returned observation hides private temporary/storage events.

`CapturedProofs.lean` additionally proves the emitted nonzero predicate on every Usize value. These endpoints report propext, Classical.choice and Quot.sound only, with successful exit and empty stderr; no sorryAx, native-computation axiom or new producer axiom is present. Those foundational assumptions and the precompiled backend dependencies remain part of the checking policy.

The actual source-to-import meaning, JSON parsing, exact-data-to-Lean term binding and selected scalar operation meaning remain trusted. A theorem containing an artifact fingerprint does not prove that those bytes denote a term. This experiment demonstrates a checked post-import relation with exact actual endpoints; it does not close the earlier frontend boundary.

### Fit with per-pass certification

Basis: derived from actual artifacts and checked propositions.

This completes a bounded P128 real-zerocopy pass-sequence experiment: source-bound artifacts expose ULLBC/LLBC and emitted-value seams, and a small state certificate fits them. This helper has no loop, raw pointer operation, call, allocation or destructor. The raw/final selected operation identity makes that seam cheap; the emitted bridge additionally justifies eliminating local state from the returned observation. Internal transformations whose endpoints did not change this helper are not independently proved.

A useful next interface would serialize the complete selected operation data, require a consumer-owned decoder/binding theorem, and apply generic local-state/denotation lemmas. New calls, hidden cleanup, machine widths, projections or invalid representations require new premises and grammar. The slice helper's successful extraction alone does not prove physical byte reads or bounds correspondence. The nonzero model's host Usize width cannot silently become a different target's width.

This is therefore evidence for an incremental milestone, with compiler import and native-memory primitives still visible. It supplies no realistic multi-target proof-cost benchmark or proof-produced executable checker.

## Boundaries

**Known checker boundary (source reviewed 2026-10-14):** the recorded Lean 4.31 and legacy 4.30rc2 runs are observations conditional on checker soundness. Their pinned `src/kernel/inductive.cpp` lacks the final nested-parameter validation added by [fix a39eab69](https://github.com/leanprover/lean4/commit/a39eab69e1eee9ad38f4efe507907b1026a77808). The [official 4.32.2 notes](https://lean-lang.org/doc/reference/latest/releases/v4.32.2/) describe arbitrary false-theorem acceptance and a combined external-checker exploit. This source finding does not establish exact exploit portability or invalidate these owned terms, but successful exit and a clean axiom list do not establish sound acceptance of arbitrary producer proofs. No exploit was executed, toolchain upgraded, or recorded result rewritten. A deployment needs a separately justified checker/version and dependency policy; presence of the fix in 4.34.1 is not a universal soundness theorem.

Known not to establish: Rust parsing/elaboration or MIR adequacy, current patched admission, every intermediate micro-pass, exact native stack/storage/provenance semantics, open-library root closure, slice-byte primitive soundness, or all target layouts.

Unsupported by the selected certificate interpretation: calls, exceptional edges, loops, generic dictionaries, raw pointers and new instruction kinds. The retained wrapper's calls are outside the selected body theorem. The nonzero endpoint is a model theorem, not a second complete local-state certificate. No native UB example was run.

## Evidence

All evidence was acquired 2026-10-14. Support preserves the licensed exact source module, wrapper, selected declarations, normalized complete exports and stage logs, emitted definitions, three Lean units, assumption/status output and artifact/tool identities. CapturedModule adapts only source-path comments; its executable definitions are the emitted definitions. The backend import points to the same bundled Aeneas library. Original and preserved artifact identity distinctions are recorded in observation-normalization.json.

Source roles are the actual Rust/extraction/Lean artifacts; execution roles are producer/checker statuses; the local-state interpretation and milestone assessment are derived. Source-to-model safety is an explicit residual premise rather than an inference from extraction success.

## Revalidation

Compare validity.rs with the named Git object, decode both selected declaration trees completely, and check the four instruction kinds plus return. Recompile CapturedModule, CapturedProofs and ImportedBool with the exact bundle Lean and precompiled backend/package imports in fresh scratch. Confirm the actual printed foundational assumptions and successful statuses. A new artifact, target, compiler, builtin or instruction requires a new binding/semantic review; the old certificate cannot certify it by name.

*Authored by an AI agent acting on joshlf's behalf.*
