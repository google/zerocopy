# MiniRust and assembly research: coverage and conditional adoption

## Summary

The 52 stable MR/AS research bundles are covered by 26 research reports, including this synthesis, plus the agenda. The grouping is many-to-many and remains adjustable. The [question crosswalk](question-crosswalk.md) names each answered scope; `coverage-matrix.json` retains all 167 report bindings and the unperformed or unestablished frontier for every entry. Completion means these research reports are written and their bounded findings reviewed. It does not mean every suggested prototype was implemented, every inaccessible artifact obtained, or every desired soundness theorem proved.

The central design constraint is now concrete: reuse requires checked semantic connections. RustBelt's value-cell language, concrete Radium, MiniRust's representation/alias models, Kraken's machine state, a platform ABI and deployed instruction bytes are different subjects. Existing proof frameworks can organize their connection; sharing Iris, Lean, an architecture name or a successful build does not establish it.

Three performed findings particularly constrain adoption. Current MiniRust WF alone admits an enum that changes variant through storage; generic codec laws need tagger/discriminator coherence. A shortened wide-pointer union chunk loses metadata in the actual generated interpreter; the related minimize source candidate remains distinct from unexecuted importer output. Kraken's default access interpretation ignores permissions, and selected vector helpers request eight bytes before accessing larger vectors. A scalar leaf's checked full footprint does not repair that generic producer mismatch.

## Applicability

This synthesis concerns the exact questions preserved in the [agenda](../anneal-minirust-assembly-research-agenda-2026/REPORT.md) and tracked in [#3873](https://github.com/google/zerocopy/issues/3873) and [#3874](https://github.com/google/zerocopy/issues/3874). Each underlying report supplies its own immutable subjects, source/paper versus execution roles, theorem direction/domain, unsupported/unknown cases and revalidation. This synthesis does not broaden them.

Core subjects are MiniRust `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, Specr `15200eb5e676e2ee91f43bd79e674f8fc32e5348`, Kraken `8af78062037bc237b341d20252aafd1797c1bcb7`, Reference `2dafab96d919d6ab2884488e970bf95610ff83eb`, Rust 1.99 `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` and Lean 4.34.1 `5045d0056413266e57c625dcd7c365b10e377c52`. The real MiniRust core additionally uses its requested 1.97 nightly compiler; the Kraken experiments use installed 4.34.1 rather than its requested nightly. Model target, compiler host, library version and physical execution are kept separate.

The earlier 89-report initiative is complete at its own scope. Its stronger R095/P127/P131 outcomes remain in #3865/#3867. This new research does not close them by renaming model-level proofs as source or physical-access proofs.

## Findings

### A revisable grouping that follows semantic obligations

Basis: integrated **source**, **documentation**, **execution** and explicitly **derived** synthesis.

| Report family | Why these questions share work | Main bundles |
|---|---|---|
| Source/import and proof reuse | Static resolution, Specr elaboration and a safe-client theorem choose the program and claim being proved | MR01–05, MR18, MR21–22 |
| Representation and memory | Codec, copy, layout, provenance, borrow and race rules interact at the same byte/resource operations | MR06–15, MR17 |
| Control, handlers and evidence | Cleanup, coupled effects and outcome classification determine what an interpreter/proof result means | MR04, MR16, MR19–20 |
| Assembly models and artifacts | Parser/layout, instruction behavior, effect production and actual bytes are independent connections | AS01–05, AS16–23 |
| Rust/assembly boundaries | Operand timing, ABI placement, caller resources and observations determine replacement inside Rust | MR23, AS06–15 |
| Extended environments and security | Atomic ordering, unwinding, devices and leakage require explicit additional observations/interference | AS13, AS25–27 |
| Adoption and trust | Compare discharged obligations, residual assumptions and measured work under the same claim | MR24, AS24, AS28 |

`report-grouping.json` gives the current 26 packages; the crosswalk gives every association. Regrouping may merge common source investigations or split a newly discovered premise, while retaining MR/AS identities. The focused hardware-mapping and platform-unwind reports were added because normative language rules and toy examples alone did not answer those narrower questions. They address the gaps without pretending to supply complete Rust/hardware or unwinder theorems.

### The chain of claims a design must expose

A useful final acceptance claim needs the following connections, for the supported domain:

1. Source/configuration capture selects the actual expanded items, generated owners, implementations and generic instances.
2. Static elaboration and lowering preserve the safety-relevant source behavior. Preserving behavior conditional on source safety cannot independently establish that safety.
3. Imported semantic definitions agree with the identified specification, including recursive definitions, byte representation, state effects and demonic/angelic choices.
4. Program-logic rules and their adequacy relate proved contracts to all required executions, prefixes and clients of that semantics.
5. Machine entry/exit relates values **and resources** through a named ABI. Registers and bytes alone omit liveness, provenance, initialization and borrow permissions.
6. Instruction/access semantics and the chosen environment cover each relevant operation, width, fault, ordering and control exit.
7. Parser/decoder/layout/link/load evidence binds the proved subject to the executed code and every selected dispatch path.
8. The surrounding context resumes with its invariants and selected observations intact.

These are separate proof or declared-assumption interfaces. The architecture can use a verified translator, proof-producing import, independently checked certificate, logical relation, mixed-language module or a restricted trusted adapter for an arrow. It must state which. A kernel-valid theorem about a narrowed domain or wrong program does not establish the independently required claim.

### MiniRust adoption alternatives

Basis: primary-grounded reports plus **derived** conditional assessment. The rows are alternatives to evaluate, not selected implementations.

| Route | Reusable evidence now | New obligation before an Anneal source-safety claim | Internal trust and cost boundary |
|---|---|---|---|
| Direct Iris/Rocq formalization | Iris/lifetime methods, original RustBelt adequacy, concrete Radium work, simplified λTB and actual handler interfaces | Byte/provenance/full-borrow semantics, coupled-state rules, adequate safe-client relation and source bridge | Rocq kernel/axioms plus definitions/import; full MiniRust port and maintenance cost unmeasured |
| Direct Lean embedding | Checked owned codec, quantifier, handler and context fragments; actual Kraken proofs in the same prover | Faithful complete MiniRust embedding and adequacy, not an identification with the owned fragments | Lean kernel/dependencies and semantic definitions; prototype checks do not measure whole-verifier cost |
| Checked Specr import | Exact transpiler/source/effect audit and reproduced real generation/core execution | Accepted Specr semantics, resolution/coverage and checked recursive/effect translation; predictive-choice interpretation | Producer can be untrusted only with adequate checked output; no applicable verified formal backend established in inspected artifacts |
| Translate into concrete existing Rust semantics | Radium/RefinedRust representation and semantic-type infrastructure; other surveyed frontend/library interfaces | Relation between chosen MiniRust operations and the actual concrete semantics, including alias/layout/feature/exit scope | Reuse does not erase the importer or model relation; library proof transport unmeasured |
| Mixed backend certificates | Kernel-checkable terms, reflection/certificate patterns and matched-law research from the earlier corpus | Exact claim reconstruction, shared semantic interpretation and checked cross-logic resource/assumption transport | Solvers/tactics may be untrusted; bridge/checker and kernel assumptions remain explicit; no full matched API ranking |

The first implementation discriminator should use the same byte/alias API and independently fixed caller domain. It should reject an invalid Boolean, incoherent enum or shortened chunk, omitted bad nondeterministic branch, stale instance, erased alias effect and insufficient access span. The actual findings show these are consequential boundaries rather than an abstract feature checklist.

### Assembly alternatives close different parts of the chain

| Route | Substantive available endpoint | Important residual boundary |
|---|---|---|
| Kraken scalar adapter | Actual parsed X64/AArch64 leaf theorems; full modeled frame/return; exact scalar effect predicate; finite native instruction comparison | ISA/refinement and AST-byte relation, full effect production, platform ABI and Rust resources remain separate |
| Generated Sail semantics | Actual Lean backend/support/configuration source and richer architecture interfaces | Generator/model/support/interpreter configuration and adequacy; no fresh generated-model proof in this work |
| Isla/Islaris trace logic | Actual trace adequacy and published architecture-specific validation methodology | Trace origin/feasible-path coverage; optional published RISC-V result does not establish the admitted experimental Arm bridge |
| Jasmin controlled source | Formal source-to-assembly relation with source/target, architecture, print-hook and external premises | Trusted stages and final bytes; Rust callers are outside the theorem |
| Vale/Dafny/F* procedure proofs | Selected procedure/state/instruction contracts and explicit trusted specification discipline | Backend/instruction assumptions, solver/output/wrapper path and Rust inline interface; no new port executed |
| HOL/s2n byte proof route | Inspected literal/object/subroutine statements and real 185-byte object match; established lifting/synthesis patterns in corpus | No fresh HOL replay here; functional frame does not supply access/security proof or deployed caller relation |
| ACL2/K/HOL lifting | Decoder, rewrite/co-simulation and guarded binary-lifting mechanisms with identified scopes | Concrete interpretation, validation versus proof, guards, dependencies and exact Rust bridge must be checked |
| Bedrock2/RISC-V | Actual phase/call relation and configurable environment interfaces | Supported source/instance and external contracts; abstract machine constructors can be rejected by a concrete instance |

For imported existing assembly, byte binding and semantic coverage dominate different work than generating a controlled low-level program. A C ABI scalar wrapper provides a practical initial contract, but still requires Rust validity/resources. Native Rust entry needs compiler-pinned structured passing evidence. Neither route warrants an all-ABI or arbitrary-client claim from this pilot.

### Performed evidence and cost observations

This matrix keeps actual upstream execution, owned models, checked theorems, compiler observations and source-only results distinct. Detailed commands, hashes and single-run times live in each package; these are not matched backend benchmarks.

| Workload | Performed result | What was not measured or proved |
|---|---|---|
| MiniRust source/generation/core | Exact pins;5 generated files/288411B; requested-nightly build;23 upstream tests;8 owned core cases reproduced from package inputs | Minimize/Miri or universal allocation-choice/source-safety result |
| Byte/alias transcriptions | 81915 per-location traces agree;6400 race-range pairs expose198 empty-range differences | Full tree/race simulation or operational upstream comparison |
| Numeric/layout portability | 32 safe cases each on native ARM64 and wasm32; explicit FP/cast/layout differences; corrected direct-compiler replay has13 successful phases | Big-endian execution, all targets or MiniRust FP semantics |
| Actual zerocopy reuse | Prior two-target corpus: 256 Boolean and65536 pair encodings, width/ZST/endian/alignment/write controls | New proof generation or source/machine correspondence; these earlier runs were reviewed, not rerun by this synthesis |
| Rust/inline/naked AArch64 | 8292 arithmetic pairs×2 assembly routes atO0/O3;256 live-byte loads and10 exclusive stores per configuration | Universal Rust allocation contract, pointer resource bridge or load/store trace theorem |
| Actual Kraken leaf proofs | Universal modeled data/return frames on both architectures; X64 return-cell/permission/short-stack/clobber controls and fixed-host two-step composition | Complete ABI, arbitrary host/loop/callback or byte decoder theorem |
| Selected AArch64 ISA | 1290 cases agree between actual model, independent oracle and nativeO0/O3, includingNZCV;8 discriminators | Universal ISA relation or independently executed ASL/Sail semantics |
| Artifact/upgrade controls | MachO object+two linked ranges; ELF 185-byte complete literal match; byte/target/symbol/truncation controls; actual ADD→SUB old-claim invalidation | Verified loader/decoder, arbitrary relocations or new correctness by changing expected bytes |
| Static/open API | Wrong-instance/unsafe-law/domain and resource protocol controls; safe cfg/GAT/drop/callback/returned-view cases and emittedMIR | Full formality execution, frontend adequacy or arbitrary library soundness |
| Atomics/platform unwinding | Named-model/specification analysis and compile-only concrete target/metadata witnesses in focused reports | Executed weak-memory model, concurrent wrapper proof or real platform unwinder verification |

The common sum observation also differs by interface: the X64/AArch64 leaves return it in RAX/X0, whereas the s2n one-limb specialization stores it in output memory and returns the carry in RAX. Equal low64-bit mathematics is therefore not matched ABI/trace behavior or measured cross-backend proof cost.

The real MiniRust core build's observed 10.43s and package-only replay's7.37s include different compilation/reuse work. The parent AArch64 replay records roughly 3.97s proof checking/elaboration/import,0.385/0.183s native compilation and about0.05s execution for each optimization configuration. The X64 report separately records per-process elaboration/checking. These single-host observations do not establish relative verifier throughput, variance, proof-search cost or maintenance superiority.

For a comparative benchmark, separately measure capture/import, obligation generation, proof production, certificate bytes, kernel/dependency checking, negative latency, cache reuse and repair under a controlled source/ABI/model change. Require the same domain and theorem first. Most full proof-production/upgrade costs remain unmeasured; reporting an unmeasured cell is preferable to ranking unrelated successful examples.

### Internal TCB and conditional engineering gates

From an external user's perspective all of Anneal can remain in the trust boundary. Internally, large tactics, solvers and compiler heuristics can be untrusted producers if a small consumer reconstructs the required claim and checks adequate evidence. That consumer must bind source/configuration/instance, semantic version/parameters, exact program/bytes/layout, ABI, public resource domain, observation relation and transitive assumptions.

Keep logical admission, semantic definitions, import/binding, language/resource boundaries and hardware/environment assumptions visible. Selected axiom lists distinguish admitted examples, native verification premises and ordinary kernel-checked proofs. They do not verify the kernel implementation, correct a wrong semantic model or prove every dependency/physical assumption. The previous TCB literature remains applicable at its precise subjects.

A conditional development sequence follows from the observed seams:

- Start with explicit byte/scalar and register-only contracts; justify representation/choice/import laws before broad library proof reuse.
- Strengthen accepted enum/chunk invariants or prove an importer always supplies them. Current WF alone is insufficient for the demonstrated generic laws.
- Interpret full scalar accesses and preserve caller resources before admitting pointer-bearing assembly. Deny unsupported state/footprints rather than treat them as inert.
- Bind one actual C ABI leaf through exact bytes, then prove entry/prefix/exit/context connections separately. Additional compiler observations are evidence for those connections, not theorems replacing them.
- Extend to concurrency, unwinding, callbacks or devices only with the named language/hardware/environment relation and every required exit/resource rule.
- Use the shared discriminators on a candidate checker; do not let producer-supplied domains, expected formulas or premise lists define acceptance by themselves.

These are derived gates for future designs, not implementation tasks completed by this research. The scalar domain is an attractive first test because several interfaces are simpler and have actual evidence; no architecture adoption is mandated.

## Boundaries

Every proposed report topic has a substantive bounded investigation and a linked answer scope. Several exact formal artifacts remain inaccessible; several relations are source-inspected without fresh prover replay. Full RustBelt/λTB/RefinedRust proof ports, actual minimize/Miri comparisons, generated-ISA proof ports, complete library/ABI/context theorems, physical security and matched whole-system costs are unperformed or unestablished as recorded. A topic's report can be complete while its motivating future theorem is not.

The crosswalk must not be read as all suggested experiments having run. Each entry retains its stronger/unperformed frontier. The old R095/P127/P131 questions remain separate, and no current report supplies a whole unsafe-Rust or arbitrary assembly acceptance theorem. Unknown sources, explicit unsupported operations, model-level counterexamples, operational failures and native evidence are not interchangeable outcomes.

## Evidence

- `coverage-matrix.json`: 52 exact stable identities, source-question hashes, 167 report bindings, answered scopes and retained frontiers.
- [question-crosswalk.md](question-crosswalk.md): human-readable per-question navigation; `report-grouping.json`: revisable grouping.
- `report-index.json`: final report and metadata hashes, subject identities and supporting coverage locations.
- Each linked report's actual sources, proof statements, raw outcomes and narrow revalidation; the existing zerocopy, HOL and TCB corpus is reused at its recorded subjects.

No new semantic experiment is claimed by this synthesis. Whole-corpus structural/catalog validation and crosswalk checks supplement full prose, source and independent evidence review; they do not establish semantic coverage by counting files or identifiers.

## Revalidation

Reconcile an edited checklist against preserved question hashes before reusing this crosswalk. For a changed source, model, target, compiler, kernel or deployment, follow the specific affected report's revalidation and update its applicability; do not infer compatibility from adjacent versions.

A new design should instantiate the shared domain/observation/resource obligations and rerun the corresponding bad-branch, invalid-representation, resource/frame, ABI and artifact mutants against its actual consumer. Update the conditional matrix only with evidence that closes the named connection, preserving any residual assumptions. Publish a coherent validated tree and verify its actual remote identity before changing issue completion state.

*Authored by an AI agent acting on joshlf's behalf.*
