# Three checked correspondence routes for a captured safe-byte fragment

## Summary

Three implemented routes prove the same consumer-selected claim: every u8 input gives the same result in a captured source tree and proposed byte IR, with a fixed original-source hash as an index. The routes use instrumented native trace rows, a post-hoc structural decoder, and an output witness for a proved constructive translator. All three check with the exact task-local Lean 4.31.0 and report only propext.

The Rust-source-to-tree capture and primitive wrapping-arithmetic interpretation remain an explicit trusted frontier. Native Rust 1.99.0 agrees on all 256 inputs of the exact safe fixture and corroborates that frontier; it is not a kernel proof of the Rust compiler or parser.

## Applicability

This is a report-owned prototype, identified by artifact hashes in REPORT.json and support/artifact-index.json. The safe source contains one concrete scale(u8) helper multiplying by 5 and subject(u8) that adds 3, calls scale, and adds 7 using wrapping operations. The trusted capture accepts a narrow whole-file grammar and maps the helper to the corresponding byte-expression subtree. It does not process arbitrary Rust crates, macros, unsafe operations, dynamic dispatch, references, or optimization passes.

The exact environments are Lean 4.31.0, commit 68218e876d2a38b1985b8590fff244a83c321783, and rustc 1.99.0, commit b940084d7eb6a299eb4bfeb8e34901bc051e7ac4. Both executable hashes and reported versions are retained. The host was Darwin 27 arm64; Lean reports an arm64-apple-darwin24.6.0 Release target. Rust controls used edition 2024 and opt-level 0. Transitive libraries/shared runtime were not fully hashed.

Research scope: an actual relative-to-frontier experiment for P127/P132/T111–T114 and partial evidence for P136. No P128 result or proof-produced executable binary is claimed.

## Findings

### One semantics and one claim across the three routes

Basis: **source** + **execution**.

ArithmeticModel.lean defines Byte as Fin 256, wrapping addition/multiplication as natural arithmetic modulo 256, separate Source/IR tree datatypes, and their total evaluators. No producer-defined expected-output predicate supplies the goal.

The independently selected challenge fixes original source bytes/hash, captured source, all-u8 domain, equality property, wrapping-byte-tree-v1 semantics, concrete helper inventory/instance, target, flags, toolchain revisions, and assumption policy. Producer JSON carries a proposed IR and route-specific witness. The companion wrapper checks the original source hash and trusted capture against the consumer's challenge before inserting validated data into its proof template.

Every successful route proves the same Claim expectedSourceHash actualSourceHash capturedSource proposedIR:

- the two indexed source hashes are equal;
- for every x : Fin 256, evalIR proposedIR x = evalSource capturedSource x.

The hash equality inside the theorem is an equality of selected string indices. The wrapper, rather than a proved Lean SHA/parser frontend, binds those indices and the source tree to real input bytes. This is the initial trusted frontier.

### Concrete routes and their reusable endpoints

Basis: **source** + **execution**.

| Route | Witness and checking endpoint | Resulting theorem |
| --- | --- | --- |
| Instrumented | Rust emits input/a/b/output rows; checkInstrumented requires 256 rows and checks every Fin 256 input, intermediates, source output, and IR output | instrumented_sound yields the all-input evaluator equality |
| Post-hoc | checkPosthoc checks decode(proposedIR)=capturedSource using structural equality | decode_eval and posthoc_sound yield the same all-input equality |
| Constructive | proposedIR=construct(capturedSource) is checked by the kernel | construct_eval, proved by induction on Source, yields the same all-input equality |

The instrumented path validates a complete finite family of observed per-input derivations. The post-hoc route validates the proposed IR's source-shaped representation after production. The constructive route uses a generic proof about the Lean model-level translator plus a checked per-output equality witness. The Python producer is not thereby a verified executor; its output must still equal the proved construction.

The structural post-hoc checker is sufficient, not complete for semantic equivalence: an algebraically equivalent IR with a different tree may be rejected. The instrumented checker is tied to the selected concrete intermediate operations (add 3, multiply 5); extending that trace schema requires a new or generalized intermediate interpretation.

The generated consumerAccepted declarations and all three generic soundness endpoints report propext only. No native_decide or sorryAx occurs in a successful acceptance proof. The post-hoc fixture also evaluates checkPosthoc natively with #eval and records true; that observation is not used to discharge its kernel-checked acceptance theorem.

### Native exhaustive control

Basis: **execution**.

The Rust harness compiles the original subject together with an instrumented version and invokes both on all values 0–255. It asserts that the instrumented final output equals the uninstrumented subject and preserves input/a/b/output rows. The recorded rows also agree with independently computed modulo-256 arithmetic.

The run exits 0 and preserves exactly 256 ordered rows. This is exhaustive for the declared input domain of the observed native fixture. The compiler, native runtime, and trusted primitive interpretation remain named assumptions when relating those observations to the logical tree model.

### Measured checking cost and implementation burden

Basis: **execution** + **derived**.

Three sequential process samples per route yielded:

| Route | Median seconds | Min–max seconds | Whole Lean fixture bytes |
| --- | ---: | ---: | ---: |
| Instrumented | 2.411 | 2.353–6.369 | 10,659 |
| Post-hoc | 0.809 | 0.775–0.812 | 4,442 |
| Constructive | 0.785 | 0.729–0.800 | 4,433 |

These times include Lean startup, imports, model elaboration, kernel checking, and printing. OS cache state and concurrent host load were uncontrolled; n=3 is a small local sample. The post-hoc/constructive difference is too small to support a useful general ranking. The instrumented route rechecks 256 rows in this fixture; that domain-sized payload and work differ from a structural witness checked through a generic theorem.

All routes share the byte semantics and claim interface. Instrumentation adds a trace schema and complete input enumeration. Post-hoc checking maintains a decoder and its soundness theorem, and admits only the decoder's structural correspondence relation. Constructive translation maintains the translator correctness theorem and checks output equality to it. These are concrete maintenance obligations visible in the code; human development hours and industrial pipeline integration effort were not measured.

### What this establishes for a later pipeline

Basis: **derived**.

The prototype exhibits the minimum separation between a consumer-selected source/domain/property, a capture frontier, an untrusted generated artifact, and a reusable checked correspondence theorem. A pipeline may use per-run witnesses without proving its external implementation, or expose a proved model-level transformation and validate that a produced output matches it.

Neither route verifies a source-language parser, Charon, Aeneas, the Rust compiler, or a machine-code emitter. Lean compilation/typechecking produces accepted proof declarations here; it does not produce a verified native checker binary.

## Boundaries

**Known checker boundary (source reviewed 2026-10-14):** the recorded Lean 4.31 and legacy 4.30rc2 runs are observations conditional on checker soundness. Their pinned `src/kernel/inductive.cpp` lacks the final nested-parameter validation added by [fix a39eab69](https://github.com/leanprover/lean4/commit/a39eab69e1eee9ad38f4efe507907b1026a77808). The [official 4.32.2 notes](https://lean-lang.org/doc/reference/latest/releases/v4.32.2/) describe arbitrary false-theorem acceptance and a combined external-checker exploit. This source finding does not establish exact exploit portability or invalidate these owned terms, but successful exit and a clean axiom list do not establish sound acceptance of arbitrary producer proofs. No exploit was executed, toolchain upgraded, or recorded result rewritten. A deployment needs a separately justified checker/version and dependency policy; presence of the fix in 4.34.1 is not a universal soundness theorem.

**Answered:** an actual three-way comparison on one property and domain, concrete reusable soundness/translation endpoints, complete native controls for the fixed unary u8 fixture, and measured local proof-checking samples.

**Research still open:** proof of Rust capture/primitive adequacy; correspondence for real Charon/Aeneas artifacts; a proved executable checker/verified compiler path; optimization, control flow, richer source constructs, and broader cost evaluation.

**Known trusted frontier:** the narrow Python capture, source-to-model interpretation, consumer wrapper/template, Lean kernel/import/runtime path, and rustc/native execution for corroborating controls. Imported standard-library/shared-runtime identity was not exhaustively established.

**No extension beyond the tested subject:** no P128 full result, no verified Rust compiler, and no P136 proof-produced binary. Native control of all 256 inputs does not prove a general Rust-language importer.

## Evidence

All model/source/IR/proof fixtures are report-owned material under support/experiments/. ArithmeticModel.lean contains the exact semantics and generic theorem endpoints. The three Arithmetic-*.lean files retain generated declarations, stdout/stderr, source-hash indices, and actual axiom lists. challenge.json and baseline-candidate.json retain selected bindings and data-only artifacts. native-rows.json and native-observation.json preserve native coverage, binary identity, and outputs. execution-results.json records the nine timed Lean invocations and their sample scope; toolchain-identities.json records exact executable hashes/versions.

support/bootstrap.py records capture/generation/native harness construction. It is revalidation code for this specific prototype, not a generic Rust frontend. There are no upstream source mirrors or compiled native binaries in the package.

## Revalidation

Use the exact Lean 4.31.0 executable and Rust 1.99.0 identity. Run each Arithmetic-*.lean file and compare exit 0, consumerAccepted's type, and its propext-only dependency list. Compile/run arithmetic_native.rs with the recorded flags and compare all 256 rows. Inspect bootstrap.py's whole-file grammar and helper interpretation before admitting a new source subject.

For a portable rebuild, set LEAN_BINARY to the exact Lean executable when running support/bootstrap.py. Run from a task-owned copy if preserving the recorded evidence. A new frontend or exported IR must supply its own byte binding and semantic correspondence evidence; this report's trusted capture cannot be silently reused as a full Rust parser.



*Authored by an AI agent acting on joshlf's behalf.*
