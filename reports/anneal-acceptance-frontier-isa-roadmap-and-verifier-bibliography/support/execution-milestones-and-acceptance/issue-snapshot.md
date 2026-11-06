# Execute the remaining Anneal experiments and proof goals

The research reports in #3873/#3874 are published. This issue tracks the additional execution, prototype and mechanized-proof work requested afterward. The [published synthesis](https://github.com/google/zerocopy/blob/32f279dc7f8faa27ded717ba664c5d30df5503a2/reports/anneal-minirust-assembly-coverage-and-adoption-synthesis-2026/REPORT.md) and its [52-question frontier crosswalk](https://github.com/google/zerocopy/blob/32f279dc7f8faa27ded717ba664c5d30df5503a2/reports/anneal-minirust-assembly-coverage-and-adoption-synthesis-2026/coverage-matrix.json) provide the exact starting evidence. All 52 MR/AS topics remain represented below. R095/P127/P131 also remain in #3865/#3867.

## Why this work remains

Existing model proofs, bounded native/compiler experiments and literature findings leave separate source/import, logic adequacy, resource/ABI, ISA/access and executable-identity connections. Each milestone names an actual execution or theorem that can close one of those gaps. Backend alternatives remain separately evaluated; compatible theorem domains and assumptions must be established before comparison or composition.

## Acceptance and execution discipline

An experiment requires actual recorded execution and appropriate controls; a proof requires a checked theorem at the stated source/model/resource/artifact domain. Partial results, failed runs and research reports do not close stronger proof milestones. If a goal is false or inaccessible, preserve evidence and keep its required resolution explicit; do not silently weaken it.

Keep actual upstream execution, owned models, source inspection, native observations and checked theorems distinct. Record immutable subjects, full commands/statuses and useful inputs/outputs, exact theorem directions/quantifiers/axioms, negative controls, scope and revalidation. Publish reviewed coherent results to `reference`. Mark individual milestones only after authoritative evidence is published and read back. A missing tool, inaccessible artifact or failed proof is not successful completion. Retain the original broader goal when a narrower prototype succeeds.

## Execution milestones

- [ ] **E01 — Restore and verify required pinned toolchains and build environments.** (experiment; MR03, MR05, MR19, MR20, AS01, AS18, AS19, AS20, AS21, AS22) Record exact component/source identities and successful version/build checks in isolated environments, with disk/build limits and no silent version substitution.

- [ ] **E02 — Obtain previously inaccessible exact formal artifacts.** (experiment; MR03, MR11, MR12, MR19) Acquire Specr2, lambdaTB and relevant Simuliris artifacts at identified revisions; inspect actual theorem statements/dependencies. An access failure remains open, separately recorded.

- [ ] **E03 — Replay selected existing mechanizations and assumption closures.** (experiment; MR01, MR12, MR18, MR19, AS01, AS19, AS22) Freshly check the actual modular-effects/Rust logic/ISA proof artifacts, recording kernels, imports, axioms, admissions and scope. Source Qed and successful builds alone do not meet theorem-replay acceptance.

- [ ] **E04 — Implement independently bound configured-source capture.** (prototype; MR05, MR21, MR22, AS06, AS12, AS24) Bind source, target, features, resolved implementations/instances, expanded and compiler-generated owners, constants and reachable dependencies; wrong-item/configuration/instance and omitted-owner controls reject.

- [ ] **E05 — Run the actual pinned minimize pipeline on paired source cases.** (experiment; MR02, MR03, MR05, MR07, MR16, MR17, MR20) Preserve Rust, MIR/pass settings, generated MiniRust and actual outcomes for representation, aliasing, library and cleanup cases; include erasure/omission controls and classify operational failure separately.

- [ ] **E06 — Run real MiniRust/Miri disagreement comparisons.** (experiment; MR08, MR11, MR13, MR14, MR20) Execute matched cases with recorded model/target/options and outcome interpretation, covering retags, protectors, provenance, allocation reuse, zero-sized/dead ranges and races; bounded execution is not universal equivalence.

- [ ] **E07 — Execute a-mir-formality judgments and code generation.** (experiment; MR05, MR21, MR22) Exercise generic dispatch/normalization, safe/unsafe calls and trusted-body versus codegen rejection; retain feature/generated-body census and actual accepted/rejected judgments.

- [ ] **E08 — Extend real target and layout observations.** (experiment; MR09, MR10, MR21) Run a big-endian target and relevant integer, FP, DST, niche, vtable and mask cases; bind compiler/layout/target identities and distinguish emulation, compilation and native execution.

- [ ] **E09 — Execute selected standard-library and environment routes.** (experiment; MR05, MR16, MR17, MR22) Inspect actual minimize for unaligned access, copies, allocation/reallocation, required constants and Drop; exercise allocation failure and foreign callback cases with safe bounds and explicit environment contracts.

- [ ] **E10 — P127: certify a real minimal Rust-source-to-model fragment.** (proof; MR02, MR05, MR21, MR24) Check a theorem for the actual independently selected pre-optimization Rust fragment and its translation, including first-bad-prefix/source-safety reflection and exact artifact/claim binding. A hand-imported model premise does not close this goal.

- [ ] **E11 — Provide a verified Specr elaboration/import route.** (proof; MR02, MR03, MR19) Specify accepted source/recursive definitions, resolution and supported effects; check translation correctness/coverage with unsupported constructs rejected. Rust typechecking of generated code is insufficient.

- [ ] **E12 — Exercise actual exposed-provenance and mixed-choice cases.** (experiment; MR04, MR08, MR20) Run the real implementation where supported and preserve unsupported predict behavior explicitly; test bad demonic branches, continuation-sensitive angelic witnesses and empty behavior without conflating sampling with validity.

- [ ] **E13 — Give predictive mixed-choice semantics and adequate checking.** (proof; MR03, MR04, MR08) Mechanize the required game/continuation semantics, UB/divergence/empty behavior distinctions and sound certificate rules over all required choices.

- [ ] **E14 — Instantiate modular handlers for MiniRust state and effects.** (proof; MR12, MR14, MR19) Check concrete handlers, coupled byte/alias/race state invariants, composition and adequacy; preserve environmental/nondeterministic quantifiers.

- [ ] **E15 — Establish general representation/copy laws with justified invariants.** (proof; MR06, MR07, MR10) Prove scalar/array/enum/union codec and typed/byte-copy laws over the selected full semantic fragment; justify enum tagger/discriminator and wide-pointer chunk invariants from actual imports.

- [ ] **E16 — Verify dynamic layout, niches and validity extraction.** (proof; MR06, MR09, MR10, AS06) Relate compiler layout/vtables and recursive DST/niche/mask facts to accepted model definitions, including initialization, padding and invalid values.

- [ ] **E17 — Prove joint provenance/alias/allocation correspondence.** (proof; MR08, MR10, MR11, AS07) Handle wildcard/exposed provenance, liveness, deallocation/reuse, address bounds and zero-size behavior without deriving authority from numeric equality.

- [ ] **E18 — Prove unbounded Tree Borrows and memory simulation.** (proof; MR11, MR12, MR13) Connect actual selected MiniRust/Miri/calculus transitions, trees, retags, ranges and protectors; finite table transcriptions do not discharge operational equivalence.

- [ ] **E19 — P131: connect an actual memory operation to storage and initialization.** (proof; MR06, MR07, MR17, MR24, AS07) Prove the selected Rust load/store/copy operation implements byte/storage/provenance/initialization laws under independently justified live-resource premises; pure encoding equality alone is insufficient.

- [ ] **E20 — Construct a byte- and alias-sensitive MiniRust lifetime logic.** (proof; MR01, MR12, MR13, MR18) Mechanize state interpretation, resources, protectors, UnsafeCell masks and adequacy for the required MiniRust fragment, identifying every imported model relation.

- [ ] **E21 — Establish alias/race composition and machine adequacy.** (proof; MR11, MR14, MR15) Prove race access completeness/commutation or the appropriate replacement relation, including implicit alias effects and complete widths.

- [ ] **E22 — Construct the required relaxed-memory resource logic.** (proof; MR14, MR15, AS25) Extend byte/alias semantics with views, atomicity, interference and synchronization; justify Rust-specific premises and a reclamation example rather than transferring C11 theorems by name.

- [ ] **E23 — Port real allocation, splitting and interior-mutability APIs.** (experiment; MR01, MR12, MR13, MR18, MR22) Check concrete allocation, split/recombine, recursive-reborrow, Cell/callback and returned-reference proofs in the selected logic; preserve underlying implementation identities and failed ports.

- [ ] **E24 — Establish functional/spatial proof transport and safe-client soundness.** (proof; MR01, MR18, MR22, MR24, AS15) Prove the selected API abstraction for every permitted safe client, lifetime and implementation/trait instance; provide the actual operational/resource relation between adopted semantics.

- [ ] **E25 — Prove source Drop/unwind and exceptional resource restoration.** (proof; MR13, MR16, MR17, MR22, AS13) Cover generated cleanup, protector exits, normal return, panic/abort and double-panic/runtime policy for the declared fragment; restore caller invariants on every permitted exit.

- [ ] **E26 — Extend source elaboration and library coverage.** (proof; MR02, MR05, MR16, MR17, MR21, MR22) Mechanize required traits/GATs, macros/configuration, temporaries/patterns, closures/generated async/drop, intrinsics, allocator/runtime and safe/foreign caller contracts; explicit partial support does not close broader claims.

- [ ] **E27 — Replay Kraken on its requested toolchain and extend ISA validation.** (experiment; AS01, AS04, AS08, AS17, AS28) Check selected actual proofs on the recorded requested nightly, and extend independent/reference/native validation to motivated X64/A64 forms, faults, overlaps and SIMD with exact supported scope.

- [ ] **E28 — Build checked assembly parsing/layout/byte certificates.** (proof; AS02, AS03, AS16, AS17) Prove the admitted source/parser/preprocessor/printer and AST/encoding/decoding/layout relations; bind exact entry, ranges, labels and unsupported syntax. Data/directive erasure must not silently change subjects.

- [ ] **E29 — Connect selected Kraken instructions to a reference ISA.** (proof; AS01, AS04, AS18, AS19) Prove the required universal instruction-state relation, including flags, access/fault outcomes and widths; finite native agreement does not meet this proof goal.

- [ ] **E30 — Prove complete access production and permissions.** (proof; AS05, AS07, AS09, AS24) Connect every actual memory operation to full trace/permission spans and frames; repair or reject vector-width mismatches and relate modeled authority to the chosen Rust/page resources.

- [ ] **E31 — Execute generated-model and cross-foundation proof ports.** (experiment; AS18, AS19, AS20, AS21, AS22, AS23, AS28) Build a selected Sail model and proof, inspect generated dependencies; run relevant Isla/Islaris, Jasmin, Vale/F*/Dafny, HOL/s2n and selected ACL2/K/Bedrock/HOL ports on comparable claims, recording real unsupported cases and costs.

- [ ] **E32 — Check compiler/configuration and trace-coverage bridges.** (proof; AS18, AS19, AS20, AS21, AS22, AS23) Discharge adopted generator/backend/support assumptions, feasible-path coverage, compiler pass/external-call premises and lifting guards. An upstream theorem must be instantiated at the actual configuration.

- [ ] **E33 — Implement and validate ABI witnesses/classification.** (prototype; AS06, AS11, AS12) Export actual FnAbi/layout/attributes or independently check named C ABI classification, including hidden results, stack, varargs, vector and shadow-space facts where required; reject stale target/instance evidence.

- [ ] **E34 — Prove inline operand/options/continuation contracts.** (proof; AS08, AS09, AS10, AS12) Cover universal legal register allocations and overlap, subregisters, implicit state, effects, stack, flags, labels, nonreturn, duplication/motion and unwind restrictions for the supported domain.

- [ ] **E35 — Construct the actual MiniRust/machine ABI-resource relation.** (proof; MR23, AS06, AS07, AS11, AS12, AS13, AS15) Relate values, live allocations, provenance, initialization, borrows and stack/return resources at entry, every execution prefix and each permitted exit, including pointer returns.

- [ ] **E36 — Prove behavioral/contextual Rust-assembly replacement.** (proof; MR23, AS10, AS13, AS14, AS15) Establish the declared refinement/equivalence directions and observations for pure Rust versus assembly, including overflow, safety, failure, divergence and permitted contexts/callbacks.

- [ ] **E37 — Bind final deployed bytes, relocations and dispatch paths.** (proof; AS03, AS16, AS17, AS24) Verify the adopted decoder/loader or explicit checked boundary, relocations, symbol ranges and selected dispatch branches; prove fixed-fragment and required host/loop/escape composition with stale/changed-code rejection.

- [ ] **E38 — Run actual weak-memory model and concurrent-wrapper controls.** (experiment; MR15, AS09, AS25) Execute pinned herd/rmem and rustc atomic mappings, missing-fence/effect annotation controls and an actual selected concurrent assembly wrapper; record model configurations and observed graph/outcome evidence.

- [ ] **E39 — Prove Rust/compiler/hardware weak-memory compatibility.** (proof; MR15, AS09, AS25) Connect byte-range race/access rules, LLVM/compiler effects, atomic/RMW/fence events and selected hardware consistency/refinement; discharge complete-wrapper and mixed-width premises.

- [ ] **E40 — Exercise actual permitted platform unwind/callee chains.** (experiment; MR16, AS11, AS13, AS27) Run selected valid helper/callback and native unwind cases, bind final metadata/registration and cleanup; retain metadata-only negatives without executing undefined Rust.

- [ ] **E41 — Prove platform recovery, personality and cleanup contracts.** (proof; MR16, AS13, AS27) Verify relevant partial prologues/body/epilogues, metadata production/loading, callee/callback composition and restored Rust resources on each permitted exceptional exit; forced unwind/nonlocal jumps require their own justified scope.

- [ ] **E42 — Establish required security properties.** (proof; AS14, AS26) Prove selected two-run leakage/constant-time claims for the actual pilot; develop explicit speculation, physical side-channel and fault models for any advertised stronger guarantees.

- [ ] **E43 — Establish required platform/environment extensions.** (proof; AS10, AS13, AS23, AS27) Implement and prove motivated interrupt/signal/TLS/context-switch/probe/VM/MMIO/syscall/DMA/self-modification/control-flow-protection contracts and Rust ownership transfer, with omitted-effect controls.

- [ ] **E44 — Build an actual small proof-evidence consumer.** (prototype; MR24, AS09, AS24) Separate untrusted producer/search from consumer-owned program/property/domain/assumption selection and complete checking; reject malformed, changed-subject, omitted-premise and weakened-domain artifacts.

- [ ] **E45 — Prove certificate acceptance soundness and binding.** (proof; MR03, MR24, AS24) Connect the executable/parsed certificate checker to its logic and actual consumer claim; justify import/definition/axiom/computation policy, complete dependency checking and resource semantics.

- [ ] **E46 — Extend the complete shared pilot corpus.** (experiment; MR23, MR24, AS04, AS11, AS14, AS28) Perform multiply/carry/byte-swap/load/store/copy/pointer-return/inline-label/C-ABI/helper and justified SIMD cases on both architectures, with real zerocopy operations and negative controls.

- [ ] **E47 — R095: finish strict SMT acceptance of all four original byte laws.** (proof; MR06, MR24, AS24) Obtain complete accepted certificates for unchanged guarded IntoBytes/write/Boolean/array laws with exact root/domain binding and all invalid variants rejected; no holes, admissions or replacement by frame-only projections.

- [ ] **E48 — Measure matched proof production/checking/reuse/repair and select conditionally.** (experiment; MR24, AS24, AS28) Compare viable routes on the same claim/domain/observations; separately measure capture/import, search/generation, certificates, kernel/checker/dependency work, warm/cold reuse and controlled source/ABI/model upgrades. Publish residual TCB and justified adoption decisions.

- [ ] **E49 — Establish target-parametric numeric and floating-point semantics.** (proof; MR09, MR10, MR21) Mechanize bounded integer/shift/cast/overflow rules and the required full MiniRust floating-point extension, including IEEE choices, NaNs and target parameters; prove the declared all-target semantic laws and importer correspondence. Compiler observations and layout classification do not discharge this goal.

## Initial dependencies and resource use

Start real frontend/Miri work, strict byte-certificate completion and a checked scalar assembly adapter in isolated scratch spaces. Restore only necessary exact toolchain components; share read-only inputs and serialize large builds under current disk limits. Then use the first complete byte/alias and assembly paths to drive logic ports, extended domains and matched measurements. Grouping may change while retaining stable milestone/question identities and the stated acceptance goals.

*Authored by an AI agent acting on joshlf's behalf.*
