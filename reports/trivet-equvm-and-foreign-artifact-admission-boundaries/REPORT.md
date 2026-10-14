# Trivet, current EquiVM and foreign-interface artifact admission boundaries

## Summary

Trivet’s paper supplies a precise refinement/acceptance architecture, but the authors’ executable artifact could not be identified in bounded retrieval. Current EquiVM has inspectable Stele refinement definitions, a concrete ERC20 capstone and resolved dependencies; its gas/failure/observation and native-evaluation allowances delimit the claim. VeriFFI supplies separately relevant C/Gallina interface facts, with an older compiler gitlink and a current unfinished foundational connection. These are three different subjects.

## Applicability

P027/T028 concerns Trivet’s exact `2609.19583v1` paper and the unresolved implementation identity. P028 concerns EquiVM’s original `2607.26306v1` paper and current repository commit `fc74a6466b92113a6fe16d577de0f553ee46f7cf`; current names/definitions are Stele, so they are not silently substituted for the paper’s Sol⁻ revision. VeriFFI commit `7e8cd8e7b631be066407f86c82ff60b6fc63ae0b` is supplementary P109/T043 evidence.

No framework/toolchain was installed or built. EquiVM’s selected source requests Lean 4.29.0; the original Lean 4.31 specimens in other packages are not an EquiVM replay. No kernel-soundness audit of its 4.29 subject was performed. The parent’s separate 4.31 kernel finding does not establish immunity or affectedness for this different subject.

## Findings

### F1. Trivet’s paper policy is stronger than tactic success

Basis: primary paper; no executable enforcement observation.

Trivet generates refinement and refutation scaffolds. Its definition permits any target behavior after immediate source UB and more-defined target values after source poison. For a defined source value, the target must return the same value without immediate UB. Paper acceptance requires kernel checking, no holes, standard axioms and unchanged source/target definitions and theorem statement. Its integer formalization excludes undef, memory and floating point; loop handling is restricted. [Definition2.1, §§3.1–3.4](https://arxiv.org/html/2609.19583v1).

This is useful proof-generation research: LLM search remains outside logical authority, while the scaffold fixes the requested relation. It is also a refinement direction that can accept a safe target for an unsafe source. Anneal source-safety certification needs a separate failure-reflecting relation rather than infer it from this LLVM convention.

The inspected primary paper has no implementation/artifact link. Exact-name/author/Lean-MLIR searches and repository discovery did not identify the authors’ source. Similarly named repositories were not adopted as evidence. This is a bounded identity/retrieval limitation, not a conclusion that the artifact does not exist. Its actual theorem-statement/axiom/definition enforcement, parser/lowering path, dependency pins and executable status remain unexamined.

### F2. Current EquiVM’s exact relation exposes its exceptions

Basis: source.

`Stele/Refine.lean:163–183` defines runtimeRefinementFor with two constructors: a concrete EVM execution plus related Stele execution/outcomes, or EVM out-of-gas with no specification requirement. Lines221–233 universally close over account maps, original state, gas, substate and execution environment under exact bytecode identity and calldata length below the word-domain size. WithWF additionally requires selected storage/gas predicates. [Exact relation](https://github.com/argotorg/EquiVM/blob/fc74a6466b92113a6fe16d577de0f553ee46f7cf/Stele/Refine.lean#L163).

The result relation treats return values/account maps, revert/decoding/no-entry outcomes, invalid halt and static-mode violations explicitly. [lines82–118](https://github.com/argotorg/EquiVM/blob/fc74a6466b92113a6fe16d577de0f553ee46f7cf/Stele/Refine.lean#L82). The README identifies excluded gas-cost, logs/substate and revert-payload comparisons. [README:245–247](https://github.com/argotorg/EquiVM/blob/fc74a6466b92113a6fe16d577de0f553ee46f7cf/README.md#L245).

Derived conclusion: this is a chosen artifact/specification refinement, with a declared input domain and exceptional allowances. It is not equality of every EVM observation, termination reflection or source-Rust UB freedom. A producer-supplied gas/storage restriction must be independently justified before a consumer treats it as caller coverage. The relation’s out-of-gas escape cannot be used to prove a stronger successful-output or resource guarantee.

### F3. A concrete theorem endpoint and its dependency frontier

Basis: source + documentation; proof scripts were not replayed.

`Examples/ERC20/Correct.lean:344` states runtimeRefinement for its exact configuration, bytecode and contract. Lines953–961 package constructor/runtime refinement and the surface specification equality. The imports explicitly include bytecode, Spec/SpecSyntax, six function proofs, dispatcher/stepping/ABI/initcode/memory reasoning and mathlib tactics. [Current capstone](https://github.com/argotorg/EquiVM/blob/fc74a6466b92113a6fe16d577de0f553ee46f7cf/Examples/ERC20/Correct.lean#L344).

The resolved manifest pins EVMLean `fd4f5e6d6d6b4a18eb73f5a71ae2df909ac2b542` and mathlib `8a178386ffc0f5fef0b77738bb5449d50efeea95` plus auxiliary dependencies. Its declarative lakefile still names a moving EVMLean branch, so the manifest is the stronger examined build coordinate. [Manifest](https://github.com/argotorg/EquiVM/blob/fc74a6466b92113a6fe16d577de0f553ee46f7cf/lake-manifest.json), [lakefile](https://github.com/argotorg/EquiVM/blob/fc74a6466b92113a6fe16d577de0f553ee46f7cf/lakefile.toml#L47).

The README’s stated TCB includes theorem/specification identity, EVM model faithfulness, Lean and native evaluation facts. The bytecode file contains a native_decide fact. [TCB](https://github.com/argotorg/EquiVM/blob/fc74a6466b92113a6fe16d577de0f553ee46f7cf/README.md#L228), [bytecode fact:299](https://github.com/argotorg/EquiVM/blob/fc74a6466b92113a6fe16d577de0f553ee46f7cf/Examples/ERC20/Bytecode.lean#L299). The proof prompt permits documented native facts and explicitly authorized contract-specific assumptions isolated in Trusted.lean. [Policy:235–251](https://github.com/argotorg/EquiVM/blob/fc74a6466b92113a6fe16d577de0f553ee46f7cf/Misc/prompt.md#L235).

These source facts identify a real proof subject and required closure. They do not compute the capstone’s built transitive axiom set, prove all imported native facts, enforce the prompt as a checker policy, or bind a deployed bytecode independently of a producer. A fresh build/assumption audit is a separate adoption check. A human/LLM-generated specification also needs independent intended-property interpretation; a valid refinement theorem can faithfully implement the wrong selected specification.

### F4. VeriFFI is a different conditional composition interface

Basis: primary publication + source.

VeriFFI generates VST specifications from Gallina models/types; users prove the C bodies against those specs, and clients rely on the agreed model. Its publication scopes correctness apart from termination. [POPL2025 DOI10.1145/3704860](https://doi.org/10.1145/3704860).

At the current pin, the README still describes the fully foundational connection as work in progress. FnDesc.v:89 contains an active admitted graph instance; local int63 add/multiply semax_body scripts appear at c/verif_int63.v:16/39. The default _CoqProject is an explicit module list; no default-build/transitive dependency claim follows merely from a proof script’s presence. [README](https://github.com/CertiRocq/VeriFFI/blob/7e8cd8e7b631be066407f86c82ff60b6fc63ae0b/README.md), [instance](https://github.com/CertiRocq/VeriFFI/blob/7e8cd8e7b631be066407f86c82ff60b6fc63ae0b/generator/FnDesc.v#L89), [local proof](https://github.com/CertiRocq/VeriFFI/blob/7e8cd8e7b631be066407f86c82ff60b6fc63ae0b/c/verif_int63.v#L16).

The gitlinks identify CertiCoq `f0e1554d57fa683829c253570995e71b70e0083f` and CertiGraph `a2db4cf823730a104ddbde7f170627a47fc2f1b7`. They are distinct from the current CertiRocq subject in the companion report. The source of those submodules and the complete built VST/runtime/GC closure were not audited here.

Derived FFI adoption rule: bind the exact model/type/graph representation, generated spec, actual C function and its body proof; retain GC/allocation, caller/callback/resource, ABI and outcome assumptions. Source-level local proof scripts cannot justify every instantiated mixed-language application. This mechanism informs P109/T043, and supplies no substitute answer for EquiVM’s P028.

### F5. A narrow executable-admission gate

Basis: derived.

For any proof-generating artifact, independently select its source/model/configuration and exact theorem, freeze semantic definitions, then inspect or replay the transitive proof/dependency closure under a declared computation/assumption policy. A prompting instruction, clean source grep or kernel exit alone is insufficient. Bind raw artifact bytes, imports, verifier mode and success status separately from the semantic theorem.

Maintenance includes schema/language evolution, parser/IR conversions, definition equality, native facts, optional assumptions, semantic dependency revisions, toolchain versions and linked external contracts. Missing artifact identity blocks an implementation claim locally; the examined paper mechanism remains reusable research evidence.

## Boundaries

Not examined: actual Trivet implementation, EquiVM build/capstone axiom closure/full EVM adequacy, complete unknown-code implementation path, VeriFFI submodule source and full compiled C/GC/FFI chain. Unknown: artifact-specific enforcement of each prompting/admission policy. No general unsafe Rust, verified native checker or cryptographic-source-security conclusion follows.

The source/library comparison and exact relation endpoints answer their mechanism questions. Obtaining/replaying an unidentified artifact or computing its actual proof closure remains named artifact research; building future Anneal integration is separate engineering.

## Evidence

`REPORT.json` and `source-identities.json` preserve exact paper versions, repository pins, source paths and resolved dependency identities. Bounded failed artifact/PDF retrieval and guessed-path 404s are recorded in the wave checkpoint; they are not domain exclusions. Original EquiVM paper and current Stele source are not claimed byte-identical. No upstream sources are mirrored. Evidence acquired 2026-10-14.

## Revalidation

Acquire an author-linked Trivet artifact before auditing executable acceptance. For EquiVM, diff Refine/result definitions and the exact capstone/imports, preserve the resolved manifest/toolchain, build the selected module and print its actual assumptions. Inspect native-fact and optional-contract-assumption policy separately. For VeriFFI, use its gitlinks and selected project modules, replay the actual endpoint and resolve its runtime/foreign/body representation premises.

*Authored by an AI agent acting on joshlf's behalf.*
