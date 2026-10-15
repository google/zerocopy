# Certifying translations and related verification techniques

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Verified translation, per-run validation, hinted replay and proof-producing compilation remove different implementations from the trusted path. Their common useful endpoint is an explicit proposition binding a concrete input, output and semantic relation. A proof about generated code alone establishes that target theorem; it does not automatically establish that the target describes the intended Rust execution.

Existing systems supply concrete mechanisms for different seams: verified symbolic execution in Katamaran, hinted replay in Foundational VeriFast, value/state/layout refinement in Cogent and Dargent, simulation composition in CompCert, proof-producing synthesis and verified compilation in CakeML, and independent typechecking in Lean4Lean. Their assumptions differ. Current hax Lean documentation explicitly routes through Charon/Aeneas; this route is not an independent translation justification.

The comparison below separates producer/search, checker, semantic adequacy, partiality/resources and measured costs. It then derives witness interfaces for borrow operations, joins, loops and pure rewrites. These proposed interfaces are not claimed to exist in current Aeneas. No upstream build or execution occurred.

## Applicability

This report reuses exact packages in the `google/zerocopy` reference corpus at `fa65b241fd0cb2c791c841eace86d43d724359bc`. Relative links preserve the original report's pins and evidence roles. In particular, source declarations inspected by an earlier report are not newly checked theorems in this investigation.

Fresh reading includes Katamaran's ICFP 2022 paper, DOI `10.1145/3547628`; the author-hosted 59-page CakeML backend manuscript dated 2018-11-19; Lean4Lean `arXiv:2403.14064v3`; and hax documentation files at `cryspen/hax@cc6da074ca754ca9d406ec922daad3221aacbce5`. Electrolysis's README was read as blob `670746012e99efc7b239bc5cd41f9ee2d967997b` from the default branch on 2026-10-15; a complete commit identity was not established, so claims about it are documentation-only and limited.

Inherited subjects include Foundational VeriFast `0a83dba42db7ce0b445034ece5298afe980e57dc`, CompCert 3.18 `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`, Creusot `c4e9770ac1371ac4274bfe02145266d315c2fb86`, the Cogent/Dargent papers and the exact RustHornBelt/RefinedRust artifacts recorded in their linked reports. “Current” documentation means observed at the acquisition date, not an applicability range across future versions.

This report answers A28 and A34. The accompanying [semantic-domain synthesis](../rust-semantic-domains-spatial-composition-3886/REPORT.md) handles Corten and safe/unsafe/spatial composition; the separate current Aeneas and Lean reports control claims about those implementations.

## Findings

### A28: assurance architectures differ by the accepted proposition

Basis: **documentation/source** in [the certification survey](../proof-producing-versus-validating-translations-1997-2022/REPORT.md), followed by **derived** classification.

| Architecture | Accepted evidence | Producer allowed to get wrong | Acceptance obligation |
| --- | --- | --- | --- |
| Verified transformation | application of a proved transformation theorem | Nothing outside the theorem's actual implementation/domain | Correct executable realization and all theorem premises |
| Verified validator | acceptance of an input/output relation checker | Search, heuristics and transformation choices | Soundness of accepted relation and fail-closed wrapper |
| Proof-producing translation | proof/certificate for a concrete translation | Any generation step whose result is independently checked | Kernel/checker proof tied to the exact programs |
| Guided replay | recorded choices plus reconstructed obligations | Path/chunk/invariant guesses | Every hint's semantic rule and all residual obligations |
| Interpreter specialization | generated computation related to a defined interpreter | Specialization/search if checked afterward | Denotation preservation plus interpreter adequacy |
| Target-only proof | theorem of generated target definitions | Search tactics | This does not remove the source/model relation |

The historical literature supplies examples of these distinctions: proof-carrying code checks a target safety policy; verified scheduling validators check a translation relation; certifying compiler schemes attach program-specific correspondence evidence. Those claims have different endpoints even when all artifacts are called certificates.

### A34: comparison of actual systems and proof boundaries

Basis: exact-subject reports and primary papers linked in the system column. “Transfers” below are **derived** uses of a mechanism, not claims of existing integration.

| System | Theorem domain and semantic/trust boundary | Evidence seam; partiality/resources | Transfer and missing bridge |
| --- | --- | --- | --- |
| [Foundational VeriFast](../foundational-verifast-hinted-mirroring-2026-10-14/REPORT.md) | Replay soundness into an Iris axiomatic semantics at the inspected pin; primitive/storage admissions remain | Recorded symbolic choices checked against bodies/contracts; bounded/rejecting replay | Reuse search hints; still need concrete Rust adequacy and complete source closure |
| [Katamaran](https://katamaran-project.github.io/articles/2022-08-symbolic-execution-vcgen.pdf) | Symbolic VC implies shallow VC, then program logic/operational result for its language and contracts | Deep formulas, scope/path worlds, spatial chunks; default partial correctness | Reuse proved symbolic/shallow decomposition; supply Rust operation/resource interpretation |
| [RustHornBelt](../rustbelt-rusthornbelt-contract-bridge-2022/REPORT.md) | LambdaRust semantic transformers and prophecy/lifetime resources | Current/final borrow values and proved consistency; tool contract integration remains distinct | Reuse future-value contract discipline; connect actual client contract language and frontend |
| [RefinedRust](../refinedrust-radium-proof-boundary-2026-v2/REPORT.md) | Radium adequacy under typed-entry/layout premises; frontend/model assumptions explicit | Generated Rocq obligations plus maintained proofs and possible assumptions | Reuse byte-resource and proof-maintenance structure; no automatic MiniRust equivalence |
| [Creusot/Coma](../creusot-permission-coma-trust-c4e9770/REPORT.md) | Coma's VC/semantic theorem is separate from Rust extraction, trusted primitive models and solver acceptance | Permission-carrying APIs, Why3/prover chain | Reuse explicit permission/specification boundary; checked solver/source correspondence still matters |
| [Cogent/Dargent](../cogent-dargent-memory-value-layout-certificates-2021-2023/REPORT.md) | Functional/update/C state refinement and layout accessors for the papers' languages | Isabelle program-specific proofs and frame/layout obligations; Cogent core is total | Reuse value-memory refinement factoring; Rust alias/validity and actual layout are additional |
| [CompCert 3.18](../verified-compiler-pass-composition-compcert-3-18-popl-2008/REPORT.md) | Successful C compilation and trace simulations under stated semantic side conditions | Reusable pass proofs, verified-validator option; stuttering/divergence explicit | Reuse relation composition; C semantics does not supply Rust source/borrow bridge |
| [CakeML backend](https://cakeml.org/jfp19.pdf) | HOL4 source-to-machine behavioral refinement with configuration, FFI and resource-limit qualifications | Verified compiler, runtime and in-logic bootstrap; exceptions/divergence represented | Reuse executable/checker compilation route; Rust frontend and cross-logic correspondence remain separate |
| [Lean4Lean v3](https://arxiv.org/abs/2403.14064v3) | An external Lean typechecker; correctness proved for parts of its kernel implementation | Rechecks proof objects; theory/export/runtime still require accounting | Reuse checker diversity; it does not establish Rust specification or model adequacy |

### Hinted replay and verified execution pay different proof costs

Basis: **source/documentation** in [the pinned VeriFast report](../foundational-verifast-hinted-mirroring-2026-10-14/REPORT.md).

The inspected replay checks chunk selection and pointer/type equalities rather than accepting search choices as facts. Its final no-UB-named proposition is defined through an axiomatic program semantics. Admitted primitives and explicitly unsound storage rules prevent reading it as complete operational Rust safety. Unsupported inputs, missing specifications and replay fuel exhaustion generate failure obligations. These facts concern the inspected pin; they do not invalidate the architecture.

Basis: **documentation**, [Katamaran](https://katamaran-project.github.io/articles/2022-08-symbolic-execution-vcgen.pdf), §§2–6.

Katamaran relates symbolic execution to a shallow specification-monad interpreter with a Kripke logical relation, then connects the logic to an Iris operational interpretation. Lemma 6.1 gives partial correctness for pure contracts when all function VCs hold. Its world/substitution discipline supports scope growth and path simplification. This is a once-for-all verified symbolic-executor route, not evidence that a Rust extractor or arbitrary external solver has been verified.

**Derived comparison:** replay records enough search decisions to avoid rediscovery; verified execution proves the algorithm that makes them. Replay therefore needs a stable hint semantics while allowing producer heuristics to change. A verified executor needs its implementation and theorem kept aligned. Either can fail conservatively. Neither architecture permits an unknown primitive summary or unproved storage erasure merely because its main proof-search component is outside the trusted base.

### Functional and memory refinements must preserve distinct observations

Basis: **documentation** in [Cogent/Dargent](../cogent-dargent-memory-value-layout-certificates-2021-2023/REPORT.md) and [HOL synthesis](../hol-proof-producing-synthesis-and-binary-lifting/REPORT.md).

Cogent separates value/update correspondence, writable-footprint framing and concrete nonfailure. Dargent adds generated layout accessor relations; its paper explicitly leaves the analogous generic setter theorem unfinished while proving other setter properties. CakeML synthesis relates HOL values or monadic transitions to program expressions. These are different proof statements, not interchangeable claims that all generated code is safe.

**Derived result:** a pure rewrite can be validated denotationally without modeling bytes when a separate state relation justifies the abstraction. A memory rewrite needs the frame and representation relation as well. A layout certificate must identify physical-format meaning: getter/setter algebra alone admits consistently wrong offsets or endianness. An abstract functional decoder need not be injective or have an encoder for every value; it must retain the observations promised by its contract.

### Simulation composition controls direction, stuttering and failure

Basis: **source** through [CompCert 3.18 composition](../verified-compiler-pass-composition-compcert-3-18-popl-2008/REPORT.md).

CompCert's pass simulations compose with explicit intermediate states and measures. Its whole-compiler backward result additionally uses source receptiveness, target determinacy and event factoring. The theorem is conditional on successful compilation. These side conditions explain why “every stage preserves something” is not a sufficient composition proof.

**Derived application:** define the desired observable set first. For source safety, preserving only successful return values is too weak if the model omits bad source executions. For termination, a relation that allows unlimited administrative stuttering is too weak. For failure recovery, collapsing UB and panic can be wrong even when both are forbidden at a narrower no-failure boundary. For concurrent or foreign calls, an isolated trace relation needs an environment/linking condition.

### hax and Electrolysis clarify extraction versus justification

Basis: **documentation/source**.

At [hax's pinned architecture file](https://github.com/cryspen/hax/blob/cc6da074ca754ca9d406ec922daad3221aacbce5/docs/dev/architecture.md), the Lean backend delegates to Charon/Aeneas, while legacy routes use a frontend/engine phase pipeline. The [Lean quick start](https://github.com/cryspen/hax/blob/cc6da074ca754ca9d406ec922daad3221aacbce5/docs/manual/lean/quick_start.md) describes partial extraction and separate generated, handwritten and assumption directories. The [panic tutorial](https://github.com/cryspen/hax/blob/cc6da074ca754ca9d406ec922daad3221aacbce5/docs/manual/lean/tutorial/panic-freedom.md) explains that successful typechecking permits panicking RustM code and even template sorry proofs; the stated specification still needs proof.

Electrolysis's [README](https://github.com/Kha/electrolysis/blob/master/README.md), acquired as the named blob, describes Rust-to-Lean transpilation using rustc private APIs and points to a stored binary-search extraction/proof. This supplies a historical functional-purification comparison and a concrete stored output, not current Rust coverage or a general verified-translator theorem.

**Derived result:** a different command or wrapper does not create an independent semantic oracle when it invokes the same underlying translation. Conversely an older distinct translator can provide useful design evidence without providing a compatible modern toolchain. Extraction coverage, translated-definition well-formedness, target proofs and source correspondence should remain separate acceptance fields.

### Witness interfaces for the Aeneas investigation

Basis: **derived** from the compared proof seams. No implementation or theorem is claimed.

| Boundary | Candidate finite evidence | What the checker must establish |
| --- | --- | --- |
| Borrow creation/end/reborrow | resource IDs, lifetime inclusions, affected places, continuation/update relation | Correct authority transfer, alias conditions and restoration; no duplicated ownership |
| Abstraction change | before/after state relation and substitution map | Both represent related concrete states under the same environment |
| Join | branch-state injections and common abstract state | Every feasible incoming state is represented; branches/resources are not dropped |
| Loop | invariant, entry proof, body preservation and exit proof | All iterations and exits satisfy the invariant; termination requires a separate measure |
| Pure transformation | typed binder/substitution witness or local rewrite derivation | Result/failure equivalence under the target denotation and correct variable binding |
| CFG reconstruction | positional copy/edge map with administrative-step ranks | Normal/unwind edges and divergence match, including synthetic loops |
| Primitive/model call | exact symbol/instantiation and proved contract | Actual operation refines the model with complete frame/failure conditions |

For loops and recursion, a partial-correctness witness can be valid without a termination measure. The result should state this instead of manufacturing a finite bound. Conversely a bounded exploration artifact must record its residual paths or unwinding obligations. The [bounded-symbolic comparison](../rust-symbolic-completeness-boundaries-2026/REPORT.md) documents why process exit status alone cannot encode completeness; at its Soteria pin, a partial outcome can exit successfully.

Interpreter specialization offers another seam. Given a defined evaluator and an adequacy theorem, one can prove a program-specific equation between the evaluator applied to a fixed AST and a generated function. The equation removes trust in specialization only for that exact AST, evaluator, effects and result domain. If the evaluator already forgets failure or alias state, specializing it preserves that omission. Thus this technique changes how correspondence is proved, not what semantics it must preserve.

### Cost evidence: compare measured tasks, not architecture labels

Basis: **documentation**, original published measurements; no new benchmark.

| Source/task | Reported observation | What it does not estimate |
| --- | --- | --- |
| Katamaran §6.2/Table 1 | appendloop explores 34 shallow branches versus 3 symbolic; reported symbolic VC time 0.034 seconds | Rust extraction, general loop solving or portable certificate storage |
| Same experiment | Coq 8.15.2 on Ryzen 9 5950X; in-kernel evaluation plus VC proof, not an extracted executor | Stand-alone verified checker runtime |
| CakeML backend §12 | bootstrap translation about 9 hours, in-logic evaluation 24–30 hours | Ordinary per-program proof checking or current machines/releases |
| Lean4Lean v3 abstract | external checker 20–50% slower than reference; usable on mathlib | Rust model adequacy or speed of a new certificate language |

The [Katamaran paper](https://katamaran-project.github.io/articles/2022-08-symbolic-execution-vcgen.pdf), [CakeML manuscript](https://cakeml.org/jfp19.pdf) and [Lean4Lean v3](https://arxiv.org/abs/2403.14064v3) describe different workloads. Ratios between their numbers would have no defensible meaning. For hinted replay, the inspected corpus did not measure replay size/time; for the proposed borrow/join certificates, both size and checking cost remain unknown.

**Derived cost model:** total acceptance cost consists of capture/binding, producer search, witness construction, parsing/checking, residual proof discharge and trusted closure loading. Per-run proof production can lower repeated search yet increase certificate I/O. Reflection may shrink explicit proof terms yet move work into kernel computation. Reusable pass theorems amortize metatheory but do not eliminate instantiation and model-binding checks. Changes that reduce one term can increase another.

### Independent checking addresses proof validity

Lean4Lean's external typechecking and partial implementation proofs concern checking assurance. The corpus [independent-checker report](../independent-kernels-and-model-checking-certificates/REPORT.md) separately records exact export/conversion boundaries. **Derived:** two checkers can agree on a valid proof of a weak or wrongly selected statement. Proof validity, statement identity, model adequacy and deployed artifact identity remain separate obligations.

## Boundaries

**Not examined:** a fresh build or proof replay for any upstream system; complete current implementation audits beyond the named files/reused reports; a new borrow-certificate checker; direct cross-prover proof import; end-to-end Rust/assembly certification.

**Unknown:** certificate size/time for current Aeneas symbolic states, joins and loops; whole-pipeline scalability under adversarial inputs; full correspondence between production LLBC and the external operational subjects. Unknowns are not negative results.

**Known not to apply:** interpreting a target proof as an automatic Rust correspondence theorem; describing hax's default Lean route as independent of Charon/Aeneas; treating a replay theorem over admitted semantics as complete concrete adequacy; treating partial correctness as termination.

CakeML's paper explicitly permits matching source behavior up to resource-limit termination under its stated machine/FFI premises. This qualification prevents using its compiler theorem as an unqualified total-result preservation rule. The corpus source claims keep their exact historical revisions; this report does not assert those limitations persist in every later release.

## Evidence

[evidence.json](evidence.json) binds reused report metadata/hashes and fresh primary source coordinates. [coverage.json](coverage.json) records A28/A34 answer scope. Primary Katamaran locations are Lemmas 2.1/5.1/6.1 and §6.2/Table 1. CakeML locations are §§2.3–2.4, 10–12; the acquired manuscript is identified by its author URL, 59-page count and printed date, without a new PDF byte hash. Lean4Lean is explicitly v3, not a moving abstract.

Pinned hax file blobs are architecture `4491c64185044fc3dce318b4b02031be9a88b0a3`, quick start `715bd5bc5cfa4c96d60bdb0ff5b8552ec812b1e2`, and panic tutorial `c5622ab470f2e7164ca16b09fad41864c04e1acb`. These are fresh immutable documentation reads, not executions of their examples.

Evidence was acquired/reconciled 2026-10-15. No command from a copied README/tutorial was executed. Factual summaries are bounded; the longer tables and interface arguments are explicitly original cross-system analysis rather than a substitute edition of any paper.

## Revalidation

For a chosen seam, identify its acceptance proposition and exact concrete subject before comparing tool versions. Diff the relation, checker rejection branches, primitive assumptions and proof dependencies. A new hint constructor needs a semantic rule; a faster producer need not affect acceptance if the evidence language and sound checker remain fixed.

For hax, recheck architecture/routing, assumption directory behavior and proof-obligation import policy. For hinted replay, inspect concrete semantic admissions and storage rules independently of replay soundness. For verified execution, inspect the implementation/theorem match and solver contract. For independent kernels, bind the exported theorem and conversion rules as well as the checker binary.

Reuse published costs only with their workload/configuration; a later measurement should separate certificate size and checking time. No native experiment or proof build was performed in this investigation.
