# Aeneas/Charon functionalization and spatial boundaries

## Summary

The modeled LLBC borrow-checking result, the implemented rustc/Charon/Aeneas pipeline, and the new Lean spatial model are distinct assurance layers. The 2024 theorem allows divergence and panic and assumes that the entire function environment borrow-checks. It does not prove the generated functional translation. At the inspected Aeneas implementation pin, raw-pointer dereference remains rejected. The latest separate spatial draft adds typed-slot heap reasoning and allocation identity, while retaining substantial gaps before byte-level unsafe Rust.

## Applicability

Implementation observations apply to Aeneas ca282ec2312a96f6a985a4d23a663690816d3f3e and Charon cf02e3f228f97ee7be3a415be56989053063326d. The independently observed PR 1352 head 92552f503cd19ca023ae9897cf521db49ee8d887 is a separate open/draft subject, not part of that Aeneas main pin or Anneal's selected dependency. Paper results apply to versioned 2022 and 2024 formal models. No continuity from a paper's semantics to all current implementation passes is assumed.

This answers the bounded mechanism and boundary inventory behind R013, P067/P073/P077, and much of R049/T069/T070. It does not perform the actual pipeline prototypes requested by P128/P129.

## Findings

### What the formal results conclude

**Basis: primary papers.** The 2022 choose example splits a returned mutable borrow into a forward selector and a backward function: the latter receives the final borrowed value and returns the original pair with the selected component updated. Region termination triggers reconstruction. Its §7 still lists soundness of semantics and translation as future work. The 2024 long paper's Theorem 4.1 assumes all environment functions borrow-check and related concrete/symbolic states, then permits concrete divergence, panic, or a related returned/control-flow outcome. Panic counts as safe in that theorem. Theorem 4.2 relates PL execution to LLBC under borrow checking and initial-state relations, including divergence. The paper explicitly leaves functional-translation correctness to future work. [2022 paper](https://arxiv.org/pdf/2206.07185v2), [2024 long paper](https://arxiv.org/pdf/2404.02680v2).

These are substantial semantic results: they justify an ownership-centric execution view and symbolic abstraction over its modeled pointer language. They are not proof certificates for the emitted Lean function, a verification of rustc's MIR export, or a Rust abstract-machine theorem about arbitrary raw-memory code. A memory-safety result that permits panic also cannot by itself establish an Anneal specification that forbids panic.

### The implemented pipeline has several independent interfaces

**Basis: source.** Charon's transform/mod.rs runs an imported-ULLBC pass sequence, including pre/post type consistency checks, drop normalization, control-flow reconstruction, replacement of builtins, associated-type normalization, partial monomorphization, layout facts, and declaration reordering. Lines97–100 can print original ULLBC before these passes; this is a debugging observation rather than a checked semantic connection to final LLBC.

Charon's export.rs defines CrateData with charon_version, translated, and has_errors. The last field identifies an output containing only a partial description after errors. Its version-equality check protects representation compatibility. Neither the schema nor those checks supplies a proof that transformations preserve all observations.

Aeneas Translate.ml:15–34 generates symbolic ASTs; lines 129–168 convert them into pure ASTs. Pure rewriting and backend extraction are subsequent interfaces. Config.ml:49–58 distinguishes borrow-check-only mode from code generation, so acceptance by the former is not evidence that pure functionalization or printing succeeded. ExtractErrors.ml stores extraction errors and can emit target admission text for diagnostics; integrations must retain process/error status and audit final proof dependencies.

An inventory for incremental certification is therefore:

| Interface | Evidence needed for a source-level claim |
|---|---|
| Rust source/configuration to rustc MIR | Exact compilation subject and a justified source/MIR semantic relation |
| MIR import to original ULLBC | Imported-body correspondence, including failure/unwind and external calls |
| Each ULLBC/LLBC pass | Relation over the actual before/after ASTs plus a semantic theorem for that relation |
| Symbolic execution and joins | Concrete/symbolic state relation and sound treatment of paths, loops, and signature assumptions |
| Symbolic borrow state to pure functions | Forward/backward reconstruction theorem, including failure and later updates |
| Pure rewriting and printing | Denotational preservation and binding to actual emitted definitions |
| Library models and effects | Concrete operation/specification correspondence and caller discharge |

The rows are **derived obligations**, not assertions that current tools emit those certificates. The selected source observations identify executable interfaces and validation checks, not a complete proof-producing implementation.

### Raw pointers remain outside the inspected source interpreter

**Basis: source.** At both the assigned main pin and latest draft head, InterpPaths.ml:111–112 rejects Deref of TRawPtr. Both revisions have the same source blob 3197a7b0367f2037611f20456d781b2ebb0739e0. At the main pin, Std/RawPtr.lean wraps a value of type T and its scalar cast returns fail undef. The wrapper is not an allocation-backed representation of a Rust pointer.

Consequently, a hand-authored Lean raw-pointer model cannot be counted as implementation support for translating a Rust dereference. An explicitly registered external operation could have its own contract, but that contract would require an independent source/model argument. Model availability and source operational coverage are separate questions.

### The latest spatial draft has allocation identity and typed slots

**Basis: source, latest draft.** Heap.lean models locations as allocation ID plus natural offset and cells as dependent type/value pairs. It retains freed slots so allocation IDs are not reused and includes end markers tracking whether whole-allocation deallocation is allowed. This is actual allocation-identity/provenance machinery; an older claim that the model has no provenance would be too broad.

The source header expressly excludes uninitialized memory, byte representation/type punning, pointer/integer casts, higher-order store, permissions in the heap model, and the byte allocator/Layout API. Allocation identity does not supply Rust aliasing/provenance rules, byte layout, padding validity, or partial initialization. Permissions are supplied by assertions rather than automatically encoded in pointer values.

IProp.lean:19–21 defines affine predicates closed under heap extension. owns describes a subheap and separation splits compatible fragments. Thus data identity and exclusive access assertions are distinct.

### Frames and failure are part of the spatial judgment

**Basis: source, latest draft.** WPDef.lean's effectWP interprets guardedModify by requiring a witness of its actual heap precondition, applying its state transformer, and satisfying the continuation. Failure has weakest precondition False. ispec uses DWP and dispec uses DWLP while universally preserving an arbitrary separating frame. WP.lean:49–67 exposes the equivalent quantified judgments; ispec_dispec:69–74 proves the total-to-partial implication.

ITreeWP/DWP.lean defines total DWP as the least fixed point of FunctionalWP and proves that DWP of divergence is false. ITreeWP/DWLP.lean:19/36 instead defines the liberal judgment by a greatest fixed point with divergence allowed. Both use the same effect interpretation, whose explicit failure rule is False. Thus permitting nontermination does not erase the modeled failure obligation. These statements concern interaction-tree effects and heaps. They do not justify that an arbitrary Rust instruction is translated into the intended effect, or that the slot model refines byte-level Rust memory execution.

### Derived Anneal adoption and maintenance gates

Backward functions carry an update obligation that successful forward result equality misses. For a representative returned borrow, require a certificate that explains the selected referent, the lifetime end, the updated container, and preservation of all unselected components. A joins/loops theorem should retain failure and input-domain information before any pure cleanup.

For a spatial extension, keep three separately reviewable assertions: byte/layout representation; allocation/lifetime identity; permission to perform the operation. A typed-slot points-to predicate can serve some ownership proofs while still being unsuitable for unaligned byte access or partially initialized Rust objects.

The next engineering gate is a real before/after artifact pair and a checked correspondence proposition. This report provides the source inventory and discriminating proposition shape, not the requested P128/P129 prototypes. No finite toy example is presented as a certificate for the deployed pipeline.

Maintenance costs include rustc-internal changes, Charon pass relations, symbolic join behavior, backward reconstruction, model registries, backend transformations, target failure semantics, and theorem dependency policy. Type checking, target compilation, and clean logical axioms are valuable independent checks; each answers a different question from source correspondence.

## Boundaries

No rustc, Charon, Aeneas, or Lean build/run was performed. No actual zerocopy intermediate sequence or new borrow certificate was produced. Paper proof arguments were inspected; no mechanized artifact or complete implementation proof was inferred from them. Selected source scripts were read, not kernel replayed. The latest spatial PR was open/draft when observed; no current CI verdict was acquired.

The assigned main and draft pins are distinct from Anneal's selected toolchain. The read-only PR documents already state that valid incoming references and reviewed borrow translation remain premises and that general raw pointers, drops, callbacks, statics, and foreign ABIs are outside its admitted fragment.

## Evidence

- Aeneas papers: DOI 10.1145/3547647, arXiv 2206.07185v2 (43pages), §2.3/PDF p 6 and §7/PDF p 38; arXiv 2404.02680v2 (86pages), §1/PDF p 3, Theorem 4.1/PDF p 18, Theorem 4.2/PDF p 22.
- Aeneas main paths/blobs: src/interp/InterpPaths.ml, 3197a7b0367f2037611f20456d781b2ebb0739e0; backends/lean/Aeneas/Std/RawPtr.lean, 79de0729e3f3f755e10852c33de2d5f4e60f6124; src/Translate.ml, 2b9c4b5f8db404d2250b0ba2fe7e9b3ea1914c46; src/Config.ml, 6ac7f87ac268041a0c92cdcf47b3540c919a8da5; src/extract/ExtractErrors.ml, 9169ab076be376ee6150ef7f04b298b92a840965. Narrow symbols/ranges appear in Findings.
- Charon paths/blobs: charon/src/transform/mod.rs, 6fc5af78e919be7c23f882d0a250a9735326117f; charon/src/export.rs, 825319eeb8317127c61de7da83aaaeda05364518.
- Draft paths under backends/lean/Aeneas: Std/Heap.lean, 9ddd88e92d101232654988167443ac147de1bf3f; SepLogic/IProp.lean, 3e6957f5f1dcbd0eeeaf6e04275ea6536442ea1f; Std/WPDef.lean, c3dbdaffe8008be2065f214a05733454edf3a783; Std/WP.lean, 2e4d0f3f4492608bf8618b03263e0eae01777858; Data/Coinductive/ITreeWP/DWP.lean, 0049da5e2933a9d750e3cac477a5e17c6290e473; Data/Coinductive/ITreeWP/DWLP.lean, b3f96020f77199d80c939aa31189fbb3244a436c. [Draft PR](https://github.com/AeneasVerif/aeneas/pull/1352).
- Acquired2026-10-14 using versioned primary papers, pinned public files, PR metadata, and read-only Anneal documents at cce761ad53785973ec2f4a6b13715b770b340c87. No source mirrors or PDF byte hashes stored.

## Revalidation

Retrieve exact source paths and blobs, resolve paper proof/artifact identities, and replay selected theorem scripts before making checked-artifact claims. Exercise an actual returned-borrow update and compare original ULLBC, final LLBC, symbolic representation, and emitted Lean. For the spatial draft, test a source dereference and a registered library operation separately; neither may inherit support solely from the existence of a Lean heap model.


*Authored by an AI agent acting on joshlf's behalf.*
