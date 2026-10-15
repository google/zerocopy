# Rust semantic domains, spatial contracts and effect composition

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

A functional model, a resource interpretation and a concrete Rust execution describe different things. They compose when the value relation, ownership interpretation, permitted context and observable effects agree. Sharing an AST family, a proof assistant or Iris does not establish that agreement. For zero-copy code, retaining the returned value alone is insufficient: byte validity, initialization, physical layout, provenance, alias authority and allocation lifetime can determine whether reaching that value was legal.

Existing RustBelt and RustHornBelt results explain how verified unsafe abstractions can serve clients through semantic interfaces. The inspected RefinedRust corpus provides a more concrete byte-resource account. MiniRust provides an independently developed operational target, but its selected memory implementation and nondeterministic choices remain part of the subject. Corten offers a source-oriented WP architecture with useful control-flow mechanisms, while its versioned paper explicitly lists pending adequacy rules. None supplies an automatic theorem connecting every current Rust/Charon/Aeneas execution to these models.

This report answers A02/A24/A25/A35 by giving a semantic-domain comparison and a concrete contract decomposition for value, memory, concurrent, asynchronous and assembly boundaries. It distinguishes reusable mechanisms from already proved connections. No upstream execution or new mechanized theorem is claimed.

## Applicability

The reused corpus is `google/zerocopy` reference revision `fa65b241fd0cb2c791c841eace86d43d724359bc`. Every relative report link below refers to a package in that identified corpus; its original subject identities and evidence remain controlling. This is a new synthesis of those findings, not fresh reproduction of their execution results.

Important inherited subjects are MiniRust `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`; the LambdaRust POPL18 archive SHA-256 `b35bf71ccf43367493a18db9af428279a4c56e3a2e7d57fbbc90a2de1cbe3996`; RustHornBelt's 2022 archive SHA-256 `7e67c2d49b3b655113675c0d517d76589d615c9622eac2d91417d99263959121`; and RefinedRust's 2026 artifact SHA-256 `34573bac60de68c3597c23136cd5221a7129f89a24b69340f8e361750f331d53`. These are separate operational/formal subjects.

Fresh primary reading covers Corten `arXiv:2609.04372v1`, Rust core source `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` for Pin/Future/Send/Sync, and Anneal design/model documentation at `cce761ad53785973ec2f4a6b13715b770b340c87`. The latter records a design and its bounded claimed implementation; it is not a new assertion about the current repository or deployed product. Current Charon observations are separately pinned in [the CFG/MiniRust report](../charon-llbc-cfg-minirust-9e95cf3/REPORT.md); its MiniRust Gitlink is a different revision from the reused MiniRust corpus.

## Findings

### A02: comparison must identify both language and resource interpretation

Basis: **source/documentation** through the linked exact-subject reports; **derived** comparisons.

| Subject | Semantic objects and theorem domain | Resource/representation content | Connection that is still separate |
| --- | --- | --- | --- |
| Original RustBelt | LambdaRust semantic typing and finite-execution non-stuck/nonracing safety | Ownership/sharing predicates and lifetime logic over modeled value cells | Current Rust extraction, byte representation and chosen alias model |
| RustHornBelt | Semantic predicate transformers with current/final mutable-borrow values and parametric prophecies | Ownership/lifetime/continuation resources underpinning first-order contracts | Concrete verifier contract language and source/frontend correspondence |
| RefinedRust 2026 artifact | Radium finite-thread-pool adequacy under typed-entry/layout premises | Byte fragments, poison, allocation identity, permissions and liveness resources | Rust-to-Radium correctness and agreement with a selected external memory model |
| MiniRust corpus pin | Operational execution with chosen target/memory/alias implementation | Initialized/uninitialized bytes, representation operations, provenance and memory transitions | Universal safety proof, frontend correctness and correspondence to current Rust |
| Aeneas 2024 paper's PL/LLBC | Borrow-checking and execution correspondence under a borrow-checked environment | Ownership-oriented pointer/value abstraction | Functional-translation correctness and concrete Rust representation correspondence |
| Corten v1 | THIR-oriented WP and interaction-tree adequacy work | Abstract fractional forest-of-values interface | Pending rule adequacy and concrete memory/frontend connections |

The RustBelt [unsafe-abstraction report](../rustbelt-unsafe-abstraction-model-popl-2018/REPORT.md) identifies the fundamental theorem plus semantic library obligations; it also records modeling concessions such as absent relaxed atomics and simplified destruction. The [contract bridge](../rustbelt-rusthornbelt-contract-bridge-2022/REPORT.md) inspects the actual semantic judgments and prophecy consistency. Their safety claims concern their languages and premises, not a current rustc acceptance bit.

The [Aeneas paper/source comparison](../aeneas-charon-functionalization-and-spatial-boundaries/REPORT.md) keeps the 2024 PL/LLBC theorem separate from implemented functionalization and byte-level unsafe reasoning; its theorem permits panic and divergence. Those outcomes require an explicit policy in any application contract.

The [RefinedRust audit](../refinedrust-radium-proof-boundary-2026-v2/REPORT.md) records byte/provenance resources and an adequacy endpoint parameterized by a layout algorithm; it does not prove its rustc frontend. Its generated-proof and assumed-spec modes also show why available proof syntax is a separate fact from a checked proof closure. These are narrower, more useful claims than labeling a complete toolchain “foundational.”

### Corten supplies a useful architecture with an explicit proof frontier

Basis: **documentation**, [Corten v1](https://arxiv.org/html/2609.04372v1), §3, Appendix C and Appendix G/H.

Corten embeds THIR into Rocq and uses an Iris WP layer with defunctionalized continuations. Its abstract memory interface keeps fractional ownership and structured-value paths. Appendix C states that no concrete memory implementation is provided there. Appendix G marks literals/operators and expression/let statements complete against its interaction-tree denotation, while variable/borrow/aggregate/control/call/pattern rules remain pending axioms. Its validation oracle is hand-authored specifications, not independent execution. Appendix H includes rustc and the hax/hax2rocq transpiler in the trusted base. The reported synthetic proof-size improvement is two-to-fourfold; it is not a runtime or complete-adequacy result.

The transferable distinction is between a compositional semantic construction and completeness of its proved instances. A clear interface can make a missing proof local without making it disappear. An abstract ownership model can support allocator invariants while leaving byte-exposing operations outside that argument. This gives a useful comparison point for the other systems without treating the abstract interface as an implementation of MiniRust.

### Independence means an external obligation can disagree with the producer

Basis: **derived**.

For a common interface, fix an explicit parameter package: scalar widths and endianness; layout and representation laws; allocation identity and liveness; memory and alias transitions; nondeterministic choices; external effects; observable outcomes. Each revision or instantiation needs a checked implementation of the interface and a relation from its concrete state. Versioning only the interface's name leaves its meaning underdetermined.

The important direction for safety is concrete-bad-execution reflection. If a concrete Rust execution can encounter UB, the proved model must either represent that failure or establish an invariant excluding the execution. A model that merely implements one successful source behavior is too weak: choosing a favorable nondeterministic result or forgetting an invalid access could make every model theorem true while leaving source safety false. Divergence and panic policy must be stated separately from UB.

The [spatial-linking corpus report](../minirust-rustbelt-spatial-linking-obligations-2026/REPORT.md) gives the transfer direction and counterexamples to erasing bytes/alias authority. This synthesis uses that result to separate source capture, state abstraction and contextual linking. It does not import that report's owned Lean fragment as a mechanization of any upstream semantics.

### A24: a functional/spatial API needs a relation plus authority

Basis: **derived** contract analysis.

Let `Rep_T(v, p, r)` relate a mathematical value `v` to the concrete representation at pointer `p` with resource state `r`. It must say more than “decoding bytes gives v.” The following components have different roles:

| Component | What it supplies | What it cannot substitute for |
| --- | --- | --- |
| Numerical geometry | extent, stride, offset and alignment arithmetic | Pointer provenance or permission to access |
| Initialization | which bytes may be read, including partial initialization | Validity of every typed interpretation |
| Representation validity | allowed bit patterns and metadata for a type | Allocation liveness or alias permissions |
| Provenance | allocation/function identity and permitted pointer derivation | Exclusive ownership or shared-access permission |
| Resource authority | ownership, fractions, borrows, invariants and frame | Physical byte/layout agreement |
| Lifetime/retag state | duration and interference restrictions for access | A guarantee of termination or panic freedom |
| Value abstraction | logical contents and allowed update relation | Correctness of implementation effects |

A spatial implementation theorem should preserve the caller's frame, return the specified value relation and transfer precisely the advertised resources. A functional theorem about `f(v)` can then discharge the pure part of that contract. The logical equation and the resource transition are complementary premises. Neither becomes stronger when stated in the same theorem prover.

For a read-only parser, the relation might retain initialized readable bytes and their stable extent while returning an optional abstract value. Creating a borrowed typed view has stronger conditions: the reference's complete referent must be valid, aligned and live under the selected alias model, and its sharing predicate must remain valid over the allowed context. A parser returning copied values may admit weaker input ownership than a view returning references. This distinction matters even if both APIs compute the same decoded record.

### Representation cases expose why the bridge is substantive

Basis: **source/documentation** through [MiniRust representation laws](../minirust-representation-copy-provenance-laws-d821c6e/REPORT.md), followed by **derived** consequences.

At its corpus pin, MiniRust distinguishes byte information, pointer provenance and representation decoding. Its codec obligations include an information-order deflation law rather than byte equality, allowing forgotten padding/provenance information under stated conditions. Pointer decoding, dereferenceability and alias-sensitive access are different checks. This is evidence for keeping those predicates separate; it is not a theorem that arbitrary Rust copies preserve all source bytes.

Consequently zero-copy reasoning needs operation-specific observations. If an API promises byte-for-byte copying, a value-equivalence theorem that forgets padding is insufficient. If it promises only a typed result, preserving arbitrary padding may be irrelevant, but constructing that typed result still needs validity. Union storage and transmute require an explicit treatment of active data, initialized ranges and allowed observations rather than an appeal to an ordinary product type.

UnsafeCell and interior mutability require a sharing interpretation that permits designated mutations while protecting the surrounding invariant. “Shared” cannot universally mean immutable bytes. Creating a new shared reference may impose validity and access restrictions that a raw access lacked; proof of a fresh variable name or correct integer arithmetic does not discharge them.

### A25: concurrency requires an interference-aware contract

Basis: **source/documentation** through [the race/alias/weak-memory report](../minirust-race-alias-and-weak-memory-boundaries-d821c6e/REPORT.md), plus **derived** contract analysis.

The corpus MiniRust wrapper records explicit load/store ranges and compares adjacent machine steps; its atomic mode is SC-oriented. Retag/protector events affect the underlying alias state but are not the same as the wrapper's recorded access events. The report distinguishes a particular schedule from the all-schedules safety question and retains the missing commutation/adequacy argument. It also identifies differences from Rust's partial-overlap atomic contract. These findings apply to its exact pin, not every MiniRust revision.

A sequential functional postcondition can compose with a concurrent library only through a contract exposing the chosen atomicity/interference abstraction. Possible boundaries include exclusive access for the whole operation, a lock invariant, linearization points, or an abstract history. Each has different admissible clients. Replacing a concurrent operation by a pure function without specifying when its result is observed and which interference is permitted loses the required context.

The pinned [Rust marker source](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/marker.rs) declares unsafe auto traits Send/Sync and describes Sync through shared-reference transfer. An unsafe implementation must justify its thread-transfer/sharing invariant; copying a compiler-resolved dictionary into a logical model is not a proof of that invariant.

### Suspension, cancellation and pinning change the state relation

Basis: **source/documentation** for API requirements; **derived** requirements for composition.

The pinned [Future API](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/future/future.rs) uses pinned mutable access for polling and distinguishes Pending from Ready; clients should not repoll a completed future. The [Pin documentation](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/pin.rs) describes address-sensitive invariants, Unpin and destruction obligations. The [Reference's drop rules](https://doc.rust-lang.org/reference/destructors.html), read 2026-10-15, distinguish initialized fields and nested drop scopes.

A suspended computation needs a relation over the stored future state, not just the next returned value. That relation must describe which borrows/resources survive suspension, which are temporarily lent to an awaited computation, and which may be recovered upon resume. Cancellation by destruction is another control-flow exit; every suspension state that can be dropped needs a valid cleanup/resource transition.

Pinning cannot be represented merely by prohibiting an assignment in a source syntax subset. It concerns the location and lifetime of an address-sensitive value, including projections and destruction. The relation must track which parts are structurally pinned and whether movement is permitted by Unpin. An abstract functional state can be used if its interpretation carries those concrete invariants; an address-erasing model alone cannot state them.

### A35: Anneal's obligations separate into six connected interfaces

Basis: **documentation** for the pinned repository's declared scope; **derived** synthesis.

The pinned [shared-model README](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/anneal/lean/README.md) separates pure layout/byte/storage mathematics from runtime access authority. Its [semantics document](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/verification/aeneas/SEMANTICS.md) retains explicit compiler/type/target premises. Its [admission design](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/verification/aeneas/ADMISSION_DESIGN.md) describes a restricted value/borrow fragment and rejected richer effects. Those documents must not be read as existing arbitrary-unsafe-Rust certification.

| Interface | Useful evidence | Missing fact if only the neighboring layer is proved |
| --- | --- | --- |
| Layout arithmetic | universal size/offset/stride laws with bounded conversions | Agreement with actual instantiated Rust layouts |
| Byte/value validity | exact decoder domain and rejection behavior | Permission to construct/access a typed view |
| Unsafe operation | concrete pre/post resource contract over chosen memory semantics | Open-context safety of every caller |
| Functional model | pure result/update relation, with failure policy | Concrete implementation/refinement and frame preservation |
| Rust/assembly boundary | ABI/register/stack/memory-footprint contract | Matching actual instruction bytes and source resources |
| Deployment binding | exact source/configuration/artifact identity | Semantic correctness of those bound artifacts |

For casts, slices and initialization, preserve the old/new types, metadata, extent, stride, alignment, initialization state and failure path. Preserve concrete unsafe-call identity and its instantiated contract. For mutable results, preserve the final-update relationship and resource ownership returned to callers. If an extraction intentionally omits one of these, the theorem must explain why it is irrelevant to the selected property.

Assembly needs more than a function taking and returning integers. A useful contract specifies argument/result encoding, register clobbers, stack discipline, complete read/write footprint, allocation/provenance interpretation, call/return and unwind policy, and allowed architectural effects. Its precondition must be obtainable from Rust resources, and its postcondition must restore the Rust abstraction. [The assembly-frontier report](../assembly-tcb-concurrency-security-platform-frontiers/REPORT.md) and [Sail/Islaris/CompCert foundations](../sail-islaris-compcert-access-foundations/REPORT.md) document why ISA behavior, access authority and ABI linking remain distinct.

The resulting division is practical: reuse pure byte/layout theorems where their premises fit, retain spatial contracts at unsafe boundaries, and keep the source/target behavioral relation explicit. The evidence supports that decomposition; it does not select one existing logic as a complete solution.

## Boundaries

**Not examined:** current complete implementations of Corten, RustBelt, RustHornBelt or RefinedRust; a new universal Rust semantics; current async support across all tools; any native experiment, proof build or reproduction of corpus executions. No new MiniRust execution occurred.

**Unknown:** a complete operational correspondence between the listed models, a proved Rust/assembly ownership bridge for the repository, and scalable checking costs for a combined pipeline. A missing theorem in this evidence is not proof that no theorem exists elsewhere.

**Known not to apply:** transferring a LambdaRust theorem directly to all current Rust; identifying numerical bounds with provenance/permissions; treating Corten's pending rules as completed adequacy; inferring concurrent or cancellation correctness from a sequential return-value proof.

This report's proposed predicates and interfaces are derived semantic requirements, not code, checked theorems or product claims. Paper claims, corpus source audits and current documentation retain their own subjects.

## Evidence

[evidence.json](evidence.json) records the exact corpus report identities and fresh source/paper coordinates. [coverage.json](coverage.json) gives A02/A24/A25/A35 dispositions. The fresh primary Corten locations are §3, Appendix C, Appendix G Table 4 and Appendix H. Rust source paths are pin.rs, future/future.rs and marker.rs at the named commit. Anneal document blobs are respectively `9799e4c04818c085ac9b3e95bb79dc7ddbe78cc5`, `d89909750724dbafb76715e673626023b6cd49fd` and `bb01b1d5df63f53dd427f9f3dbde84cfa8dd5cdf`.

Acquisition/reconciliation occurred 2026-10-15. Original corpus dates and executions remain in the linked reports.

## Revalidation

First identify the exact desired statement: source memory safety, value correctness, contextual library soundness, concurrency, termination or an assembly contract. Then revisit only the corresponding source theorem and semantic interface. Check the memory implementation, target/layout assumptions, failure policy and quantifiers before carrying a theorem to another revision.

For Corten, reread Appendix G's rule-status table and the concrete memory/frontend trust boundary; a larger test suite alone does not change adequacy status. For a RefinedRust/RustBelt bridge, inspect the actual resource algebra and adequacy premises. For MiniRust, use the separately pinned representation/alias/concurrency reports and compare their controlling definitions, by source comparison.

For Anneal, rebind the documented source/configuration, retained IR and external-call contract set. Review any newly admitted effect for resource transfer, failure and context interference. Revalidation here is source/theorem comparison; it supplies neither execution evidence nor missing semantic proofs.
