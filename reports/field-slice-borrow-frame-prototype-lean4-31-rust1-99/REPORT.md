# Two-field and length-two slice borrow, update, and frame certificates

## Summary

A checked Lean certificate changes the selected byte field, preserves the other field, and restores modeled root authority. A length-two slice model preserves every distinct cell and returns no update outside its bounds. The theorems have an explicit root-entry premise.

Safe native Rust controls passed for all 65,536 two-byte field states and 196,608 two-byte slice/index cases at fixed delta 3. The Rust-reference-to-model bridge remains trusted; the authority tag is not a proved physical ownership semantics.

## Applicability

Report-owned artifacts are identified in REPORT.json and support/artifact-index.json. Exact environments: Lean 4.31.0 at 68218e876d2a38b1985b8590fff244a83c321783 and Rust 1.99.0 at b940084d7eb6a299eb4bfeb8e34901bc051e7ac4. Executable hashes/versions are preserved. Host Darwin 27 arm64; Rust edition 2024, opt-level 0.

The native field function takes &mut Pair, reborrows left, updates it with wrapping_add, then reads right. The native slice function uses get_mut(index), updates a valid selected element, and returns Some(updated) or None. Native testing restricts slice length to 2, delta to 3, and indices to 0,1,2.

Logical theorems quantify over all byte fields/deltas, Slice2 : Fin 2→Byte, and natural indices. Root authority and the mapping from Rust references/usize to those representations are explicit frontier assumptions. This contributes to P129/R063/R064/R096/T076 at the tested subset.

## Findings

### A replayable field plan preserves the endpoint and authority

Basis: **source** + **execution**.

BorrowModel.lean defines Byte=Fin 256, modulo-256 addition, Pair, Authority, FieldState, FieldOp, and runField. Authority has root, splitFields, and selected sliceCell states. Splitting requires root; field writes and restoration require splitFields.

The captured functional field operation updates left and preserves right. The plan split; writeLeft(delta); restore is a checked correspondence certificate. field_correspondence proves that, given entryOwn : entry=root, replay returns exactly the captured update with root restored. field_frame proves right is unchanged.

fieldConsumerAccepted includes the selected native source-hash index and quantifies the correspondence over all modeled states/deltas/root entries. Its dependency list is empty. The hash index is externally bound; it is not a theorem about parsing actual Rust references.

field-certificate.json records the data-only plan used to emit providedPlan in BorrowCertificate.lean. providedCertificate has no axioms and proves the same endpoint. The JSON-to-term mapping is trusted consumer generation; the emitted typed witness is kernel checked.

### A slice certificate exposes bounds and the frame

Basis: **source** + **execution**.

updateCell changes only the selected Fin 2 cell; slice_frame proves every j≠i is unchanged. capturedSlice checks index<2. transformedSlice borrows from root, writes under sliceCell(index), and restores root. slice_correspondence proves agreement with capturedSlice paired with root under the entry premise.

slice_oob proves None outside the modeled bounds. wrong_authority proves writing under root without the selected child permission returns None. sliceConsumerAccepted includes the source-hash index and universal correspondence; its only axiom is propext.

This relates numerical index distinction to preservation of a modeled cell. It does not establish physical non-overlap for arbitrary Rust subobjects, zero-sized types, or layouts.

### Native finite-domain controls pass

Basis: **execution**.

borrow_native.rs covers all 256×256 field states, checking the actual safe function's new left, unchanged right, and returned right against mathematical modulo-256 arithmetic.

For every two-byte state, it also checks slice indices 0,1,2. Valid indices verify the selected update and unchanged other element; index 2 verifies None and unchanged whole input. The result is field_cases=65536, slice_cases=196608, fixed_delta=3, FNV64 f2ed1041187b6325. Independent Python aggregation over the same domain matches that digest.

The run exits 0. Three process samples were 0.0565, 0.00642, and 0.00615 seconds; native compilation was about 0.382 seconds. These local times include startup and uncontrolled OS effects. They do not establish production performance or compiler correctness.

### A wrong-field witness fails a material endpoint

Basis: **execution**.

BorrowWrongField.lean uses writeRight while requesting the left-update result. From pair (0,0), delta 1, it requests (1,0), which differs from that plan's result. Kernel decide fails and the file exits 1. It is not an accepted correspondence proof; valid generic declarations printed from the shared prefix are separate.

BorrowCertificate.lean exits 0, reports no axioms for providedCertificate, and contains no sorryAx. The positive and negative statuses and outputs are retained.

### Permission bookkeeping has a defined limit

Basis: **derived**.

The authority state makes this replay's entry, suspension/splitting, child write, and restoration visible. It is not a global separation algebra or an interpretation of every Rust alias: ordinary Lean values can contain multiple tags, and no global exclusivity invariant is proved.

A spatial extension needs a resource interpretation and adequacy bridge for source references/reborrows. This experiment establishes a checked local transformation/frame endpoint at a named initial trusted frontier.

## Boundaries

**Known checker boundary (source reviewed 2026-10-14):** the recorded Lean 4.31 and legacy 4.30rc2 runs are observations conditional on checker soundness. Their pinned `src/kernel/inductive.cpp` lacks the final nested-parameter validation added by [fix a39eab69](https://github.com/leanprover/lean4/commit/a39eab69e1eee9ad38f4efe507907b1026a77808). The [official 4.32.2 notes](https://lean-lang.org/doc/reference/latest/releases/v4.32.2/) describe arbitrary false-theorem acceptance and a combined external-checker exploit. This source finding does not establish exact exploit portability or invalidate these owned terms, but successful exit and a clean axiom list do not establish sound acceptance of arbitrary producer proofs. No exploit was executed, toolchain upgraded, or recorded result rewritten. A deployment needs a separately justified checker/version and dependency policy; presence of the fix in 4.34.1 is not a universal soundness theorem.

**Answered:** representative modeled field/slice correspondence; explicit root entry/restoration; unchanged-state proofs; a wrong-field negative; actual safe native controls over the stated finite domains.

**Research still open:** reference/usize capture adequacy, global aliasing/ownership, arbitrary slice lengths, overlapping/ZST footprints, escaping references, lifetime extension, casts, and correspondence with a real functionalizing frontend.

**Native coverage:** exhaustive two-byte states at fixed delta 3 and three indices. All logical deltas/natural indices are theorem coverage, not exhaustive native execution.

**No full spatial-memory claim:** no Iris/RustBelt adequacy, concurrent resource algebra, physical-byte semantics, or arbitrary Rust UB-freedom result follows.

## Evidence

support/experiments/ preserves safe Rust source, BorrowModel.lean, data-only plans, emitted/wrong-field certificates, theorem and actual-axiom output, compiler/native output, execution-results.json, and borrow-certificate-results.json. artifact-index.json hashes report-owned artifacts.

The indexed native source hash is 996f70f543d0bad10d09464b2f4f8df566bc556c8a8f0fdcc8c4b9f796f7797b. Source identity is externally bound; the frontend bridge is trusted. No compiled binary or upstream source mirror is included.

## Revalidation

Run exact Lean 4.31.0 on BorrowModel.lean and BorrowCertificate.lean and require the recorded successful empty/propext dependency lists. BorrowWrongField.lean must fail at its wrong endpoint. Compile/run borrow_native.rs with the recorded Rust flags and compare counts/digest.

For another subject, re-establish capture, entry permission, field/index interpretation, and restoration. More native cases alone cannot establish omitted global aliasing/lifetime semantics.



*Authored by an AI agent acting on joshlf's behalf.*
