# Resource logics, effects, and compilation interfaces

## Summary

Resource reasoning, proof automation, and compilation are separate interfaces. VST and Bedrock2 expose concrete safety or machine-execution propositions under external/world and installation assumptions. RefinedC's Lithium constructs proofs in Iris; CN's published soundness concerns an explicitly annotated kernel calculus. PulseCore embeds an intrinsically specified effectful computation in F*, with a partial-correctness interpreter. These mechanisms can guide Anneal without supplying a Rust-to-resource-model correspondence by themselves.

## Applicability

Current source observations concern pinned VST, Bedrock2, CN documentation, and F*'s migrated Pulse implementation. The RefinedC, CN, Low*, Steel, and PulseCore paper results are treated as publication-specific subjects. No general continuity from historical formal models to every current executable is assumed. The old FStarLang/pulse repository now contains only a migration notice; current source was followed into FStarLang/FStar.

This is a bounded resource/effect architecture comparison for R055–R059/T038 and adjacent R049/R057. It does not evaluate all alternative logics on real Anneal programs, implement a new logic, or certify an extracted checker binary.

## Findings

### Compare propositions before comparing automation

| System/interface | Inspected endpoint | Premises that remain visible |
|---|---|---|
| VST Verifiable C | Whole-program step-indexed safety under Espec | Function specifications, initialization, external-call semantics, formal Clight |
| Bedrock2 compiler | Modeled machine runsTo preserving a supplied source postcondition | Valid functions, successful compile, source call specification, enough stack, machine_ok |
| RefinedC/Lithium | Program proof in Iris over the modeled C semantics | Frontend/semantics correspondence, correct specification, kernel assumptions |
| CN kernel | Progress and preservation for annotated Core/resource configurations | Correct logical entailments, explicit witnesses/resources, modeled Core semantics |
| Low* formal route | Safety and trace preservation through modeled compilation | Safe source, selected transformations, primitive/trace semantics |
| PulseCore | If a specified effectful computation returns, invariant/postcondition holds | State interpretation, action contracts, F* checking, actual extraction path |

The table summarizes the narrow findings below. It does not rank the systems or claim equivalent coverage.

### VST: quantified safety under an external specification

**Basis: source.** At PrincetonUniversity/VST 3c37c2e2b574e23aee8fdd1684aa0ffed227491e, veric/semax_prog.v:1967–1989 states semax_prog_rule. It requires postcondition_allows_exit, semax_prog, and successful initial memory construction. It supplies an entry core and, for every n, a juicy memory of level n satisfying jsafeN under OK_spec Espec, function-specification matching, and initialization/invariant conditions.

The universal step-index quantifier is an unbounded safety argument, not a test up to one selected finite bound. It does not establish termination. Its explicit Espec boundary makes foreign behavior a semantic premise; a caller cannot obtain arbitrary external-function safety from a proved local C body alone.

The source theorem is about formal Clight/juicy execution. A C parser, emitted AST binding, CompCert configuration, ABI, external implementation, and installed executable require their own applicable evidence.

### CompCert: compose with proved source safety

**Basis: source.** At AbsInt/CompCert 74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6, driver/Compiler.v:446–452 states that successful transf_c_program yields backward_simulation from Csem.semantics to Asm.semantics. In common/Smallstep.v:1298–1312, the final-state, progress, and target-step matching clauses assume safe L1 for the related source state. The compiler theorem preserves an already-established source property; it does not establish safety of arbitrary source C. [Pinned compiler statement](https://github.com/AbsInt/CompCert/blob/74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6/driver/Compiler.v#L446), [Pinned simulation premises](https://github.com/AbsInt/CompCert/blob/74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6/common/Smallstep.v#L1298).

Composing a VST proof with this route requires the appropriate Clight/Csem relation, common program subject, external behavior, and target configuration. Source parsing, assembly, linking, loading and native ABI correspondence remain independently applicable interfaces. A sound Rust-to-C route adds a Rust/C relation preserving the required failures and resources before invoking this composition.

### Bedrock2: resources reach modeled RISC-V execution

**Basis: source.** At mit-plv/bedrock2 757f17c6083bf8d43b5293a0db545c8d0aa32a13, compiler/src/compiler/Pipeline.v:682–730 requires valid source functions, successful compilation, a source execution establishing a postcondition, sufficient aligned stack, entry/return addresses, argument registers, and machine_ok. Its conclusion is runsTo on a MetricRiscvMachine: return values satisfy the source postcondition, traces/metrics relate, non-caller-saved registers remain unchanged, control returns to ret_addr, and machine_ok holds for the resulting memory.

compiler_correct_wp:764 onward packages a source call specification for the same route. WeakestPrecondition.v separately makes memory, locals, trace, function environment, and external interactions explicit. This is a useful program-to-machine interface with actual resource premises. It is not a source Rust or full ISO C theorem, nor evidence about physical RISC-V execution without the model/installation bridge.

### RefinedC and CN have different checking foundations

**Basis: primary RefinedC paper, §§3/5.** RefinedC interprets refined ownership typing in Iris over its modeled C semantics. Lithium performs structured proof search and produces Iris proofs, so the search implementation is not assumed correct merely because it chose a rule. The paper's adequacy argument ultimately yields a statement about the operational semantics; frontend and semantic encoding remain separate concerns. [Paper](https://plv.mpi-sws.org/refinedc/paper.pdf).

**Basis: primary CN paper and formal supplements.** CN uses Cerberus-based Core semantics and resource/refinement typing. Its kernel formalization is a let-normalized, explicitly annotated calculus: quantifiers have instantiations, existentials have witnesses, and resource manipulation has proof terms; logical entailments remain SMT premises. The soundness supplement proves resource-term progress/preservation plus overall progress and type preservation. The formal definition explicitly distinguishes this kernel from implementation inference and footprint analysis. A kernel type-safety result must not be reported as a mechanically verified current whole analyzer. [CN paper](https://www.cl.cam.ac.uk/~cp526/popl23.pdf), [Kernel definitions](https://www.cs.ox.ac.uk/people/christopher.pulte/popl23_defns.pdf), [Soundness supplement](https://www.cs.ox.ac.uk/people/christopher.pulte/popl23_soundness.pdf).

Current rems-project/cn b4a2f009234d9c80380dbf95a9b2325e36a4705d README confirms its Cerberus relationship and current source identity. This investigation did not audit its complete executable inference/SMT path or obtain a current RefinedC source snapshot.

### Low*: the formal compilation result and implementation boundary

**Basis: primary Low* long paper, §§3.2–3.3/4.1 and AppendixD/E.** TheoremD.6 preserves safety from the modeled lambda-low* source to C*; D.7 gives bisimulation. E.27 preserves safe C*2 traces into Clight under primitive semantics. Later passes alter representations and require separate trace arguments. The implemented KreMLin route includes F* normalization/erasure, additional AST transformations, and printing beyond that formal core. Its publication theorem must not be promoted into a proof of every current KaRaMeL executable path or hardware-level constant-time behavior. [Versioned paper](https://arxiv.org/pdf/1703.00053v6).

The publication also flags a native ABI limitation: its structure-argument erasure uses fields, while System V x86 requires the byte sequence including padding (footnote 12, PDF p63). This is separate from preservation in the modeled languages.

A modeled buffer/lifetime contract can establish a safe low-level program while still leaving its physical representation, extracted C, external primitives, and compiler security observations to the composition proof. Source safety preservation is useful only after its premise has been established.

### Steel/PulseCore: scoped soundness and intrinsic effect interfaces

**Basis: primary PulseCore paper, §1/PDF p 2 and §4/PDF p 18.** The paper uses stratified heap propositions to avoid circular higher-order store/invariants. It narrowly identifies an older SteelCore monotonic-state axiom as incompatible with certain classical axioms; this is not a blanket current Steel/F* verdict. Its main run signature interprets a specified computation from an invariant/precondition state into a potentially divergent function whose returned value/state satisfy postcondition and invariant. [PulseCore paper](https://fstar-lang.org/papers/pulsecore.pdf), [Steel paper](https://www.fstar-lang.org/papers/steel/steel.pdf).

**Basis: current source.** At FStarLang/FStar e2b5042ffd8272ad6287e4ad8748d8e52dadd93d, pulse/lib/core/PulseCore.Semantics.fst:127 onward defines computation m indexed by pre/post; its Act continuation may diverge. run_alt:248–258 has an initial interpreted precondition/invariant and returns in Dv with interpreted postcondition/invariant, using a state budget/fuel premise. This is an intrinsic model-side partial-correctness interface.

pulse/src/checker/Pulse.Checker.Base.fsti:208–235 carries result type, universe, precondition, and postcondition equalities through checker results and contextual typing. A declaration of that interface is not a fresh verification of the whole elaborator, SMT solver, extraction, or native plugin. Its proof terms and selected dependencies still need actual checking and an artifact-specific trust analysis.

### Derived Anneal architecture and maintenance implications

Choose the assertion language from concrete operations. First-order ownership assertions may handle disjoint byte buffers and frames. Higher-order predicates, stored contracts, callbacks, concurrency, and dynamically allocated invariants can require a stronger resource model. A familiar notation or type named IProp does not establish the same semantics as Iris.

Separate three questions for every operation: which representation denotes its data; which assertion grants access; and which event changes or transfers that authority. A C or typed-slot proof can satisfy its own assertions while omitting a Rust provenance rule. An extraction route must connect that operational rule before reusing the resource proof as a Rust theorem.

Automation can be untrusted when it constructs independently checked evidence. An SMT-validity premise, a foundational kernel proof, an intrinsic F* refinement, and a handwritten semantic argument require different checking and implementation bridges. Making effects explicit helps expose failure and environmental assumptions; it does not independently certify their source translation.

Maintenance includes semantic definitions, operation rules, frame/authority laws, normalizers, foreign specifications, proof dependencies, target serialization, and compiler configuration. Adoption should begin with an operation whose value/layout is correct but whose ownership or initialization precondition fails. The selected logic must reject or expose that case for the intended reason before broader interface work.

## Boundaries

No Rocq, Iris, CN, F*, Pulse, KaRaMeL, Bedrock2, or compiler build/run was performed. Source observations are selected statements and interfaces; complete theorem dependencies and executable-path verification were not audited. Current RefinedC implementation evidence and a concrete comparison of alternative logics on Anneal examples remain unexamined research, not merely future integration work.

The SteelCore caveat is conditional on the stated old model/axiom combination. The current Pulse source was identified after migration and was not assumed to reproduce the older paper model identically. Hardware, native plugins, resource exhaustion, parsing, unsafe Rust semantics, and mixed-language execution remain outside any unqualified conclusion.

## Evidence

- VST veric/semax_prog.v, blob 874d708d61f1d25c6ae2c1f7be263806cceec1f3 at the pin above; semax_prog_rule:1967–1989.
- CompCert driver/Compiler.v, blob 60fc74fec1411216425004f6d63567354e146e9c, transf_c_program_correct:446–452; common/Smallstep.v, blob cefab134fdce4f3ea2f970db49a99d987c05d3a1, safe-source backward obligations:1298–1312.
- Bedrock2 compiler/src/compiler/Pipeline.v, blob 06aefd8036a84df20aa55dfcb4244236414cdff1, compiler_correct:682–730/compiler_correct_wp:764 onward; bedrock2/src/bedrock2/WeakestPrecondition.v, blob 69c03ca41f35a13712b1872e18eb6873eb68f7e9, source call/WP interface.
- RefinedC PLDI 2021 DOI 10.1145/3453483.3454036,17-page author PDF §§3/5. CN POPL 2023,32-page author PDF;107-page definitions §§A1/A5 and 44-page soundness supplement §§B1/B9/B10. CN README blob 157c56b6676383397c3b86750b76ff34e18a717c.
- Low* arXiv 1703.00053v6 (2018-12-11), 88 pages; §§3/4, D.6/D.7 PDF p37, E.27 PDF p66, ABI footnote 12 PDF p63; publication identity distinguished from current code-generation paths.
- PulseCore 27-page author PDF; current pulse/lib/core/PulseCore.Semantics.fst, blob 666734d2513c6cb188dcb02d23c01bca7073c640; pulse/src/checker/Pulse.Checker.Base.fsti, blob 3c79eb8c41def0fa2b13850ac63a95b7dbd7735c. Old Pulse migration README.md, blob 7590d2607e4ea2536a21a2b58a73e7060a43625e.
- Primary acquisition 2026-10-14. No PDF hashes or source mirrors stored; repository pins and narrow source/paper coordinates retain reproducible identities. Unversioned author PDFs are publication-scoped evidence without a stronger byte identity; they are not immutable executable artifacts.

## Revalidation

Read and replay the specific logic theorem and its dependencies under compatible pins. Verify that external specifications, primitive semantics, source representation, and installed code match the claimed execution. Inspect current RefinedC/CN implementation evidence before extending their paper results to deployed analyzers. For Anneal, compare a byte-buffer ownership failure, callback invariant, and failing effect under the same source/caller contract rather than comparing syntax alone.


*Authored by an AI agent acting on joshlf's behalf.*
