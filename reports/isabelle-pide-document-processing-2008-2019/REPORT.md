# Isabelle/PIDE: replacing the prover command loop with versioned document processing

## Summary

Isabelle/PIDE did not obtain responsive proof editing by putting a richer GUI in front of the traditional prover command loop. Its central reform was to make the prover itself process a family of explicitly versioned documents asynchronously. Edits create new immutable document versions; prover commands and results are associated with document structure rather than a unique current prompt; obsolete work may be cancelled; parallel evaluation proceeds independently of editor input; and semantic markup is accumulated against a particular document state for the front-end to render. The editor can therefore keep accepting edits while the prover catches up, and it can present semantic information from a well-identified snapshot rather than pretending that every message describes the newest buffer contents.

That architecture depended on changes inside Isabelle. Parallel functional evaluation, persistent contexts, prover-native document updates, interruptible work, and semantic markup were not properties that an external editor protocol could manufacture. The 2013 PIDE/Coq experiment makes the boundary unusually clear: reimplementing the PIDE transport and connecting an editor was enough for lexical processing, but the paper says full proof processing still required Coq itself to move toward the relevant timeless/stateless processing model. The 2019 retrospective likewise reports that the Coq/PIDE experiment did not become an end-user system and that maintaining separate PIDE back-ends would require substantial continuing effort.

For Anneal, the transferable lesson is therefore narrower than “build PIDE.” Anneal can and should consider explicit source/version identity, asynchronous work, cancellation, snapshot-qualified diagnostics, and freshness checks as orchestration contracts above existing tools. Those mechanisms directly support Anneal's existing requirement that a successful result identify the program and scope to which its evidence applies. But Anneal cannot honestly infer PIDE-style semantic incrementality, persistent proof-state reuse, or source-accurate markup merely by assigning version numbers to opaque Charon, Aeneas, or Lean subprocesses. Where an upstream stage exposes only whole-input processing, the conservative analogue is a versioned whole-input job whose results are accepted only for the exact input/environment identity that produced them. Deeper reuse should require a corresponding upstream semantic contract or independently validated adapter.

This is a conditional cross-project judgment, not an Anneal design decision. PIDE's strongest benefits came from a prover architecture that Isabelle could change internally; Anneal spans independently evolving Rust, translation, proof, editor, and process boundaries and may rationally keep stronger process isolation than PIDE preferred.

## Applicability

The historical account is primarily about Isabelle/PIDE from the first parallel/document-processing work around 2008–2010 through the 2019 retrospective. The early system description in `arXiv:1207.3441v1` describes Isabelle2011-1, the first stable Isabelle/jEdit release in October 2011. `arXiv:1307.1944v1` explains the reform of the classic read-eval-print model. `arXiv:1304.6626v1` is a deliberately limited Coq integration experiment. `arXiv:1905.01735v1` looks back after more than ten years of PIDE development and explicitly discusses original aims, successes, failures, and changes. The 2019 Isabelle/HOL retrospective supplies a separate first-party historical summary from Paulson, Nipkow, and Wenzel.

The Anneal applicability judgment is against `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, specifically `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`. Those documents require verification success to have precise subject/scope identity, forbid missing evidence or tool failure from silently acquiring the meaning of success, and deliberately leave the detailed process/tool boundary undecided. PIDE is evidence about one successful interaction architecture; it is not authority for Anneal's mechanism choices.

The report distinguishes four layers that PIDE papers sometimes discuss together:

1. **Document semantics:** versions, edits, command identities, dependencies, and snapshots.
2. **Execution policy:** parallel scheduling, cancellation, prioritization by editor perspective, and retention of old states.
3. **Presentation:** semantic markup attached to source and output, rendered by an editor.
4. **Transport/integration:** the ML/Scala split and the private protocol that moves document edits and markup between the prover and front-end.

These layers do not transfer equally. An orchestrator can add explicit job/version identity without reproducing prover-native document semantics. Conversely, a transport protocol that can move edits does not imply that the back-end knows how to maintain semantically meaningful persistent versions.

## Findings

### PIDE's decisive change was semantic, not graphical

The early PIDE papers frame the problem as a limitation of the synchronous command loop, not merely an outdated editor. Proof General improved usability but retained a single checked frontier and the prover's sequential prompt discipline. The 2012 Isabelle/jEdit description explicitly contrasts that model with continuous checking: the user may edit freely while the prover provides semantic information incrementally in the background. The later Isabelle/HOL retrospective reports that Isabelle discontinued both its REPL and Proof General mode in 2014 and moved exclusively to document-oriented PIDE interaction.

The 2012 asynchronous-processing account describes the underlying reform more precisely. A document is a persistent entity updated functionally. Edits create fresh version identifiers; several related versions can coexist and share structure; prover results are associated with commands in a particular document version instead of with one global toplevel prompt. The editor therefore need not block on the current command, and the prover is free to schedule available work in parallel.

Basis: **documentation** (first-party architecture papers) + **derived** comparison.

The derived point is that an asynchronous UI is not enough. If the only semantic state remains “whatever the subprocess currently has loaded,” then allowing the editor to run ahead merely creates a stale-result problem. PIDE makes the version relation part of the back-end model, which gives later markup and query answers a state to be about.

### A document version is both an identity boundary and a scheduling boundary

By 2019, Wenzel describes a PIDE document as a large expression evaluated as a parallel functional program. Continued editing may cancel work that is no longer relevant and replace it with work for a new version. Editor/prover communication is expressed as document edits; the visible editor “perspective” is also sent as a hint about which parts deserve processing. Markup is accumulated over source text and output trees and rendered from a snapshot of a document state.

This yields three distinct properties that are easy to conflate:

- **Identity:** a result can be attributed to the document version and command that produced it.
- **Freshness policy:** the front-end can decide whether that version is current enough to display or act upon.
- **Execution policy:** the prover may prioritize visible regions or cancel obsolete computations.

PIDE combines them, but Anneal need not. An Anneal result can carry exact source/environment identity even if the underlying checker cannot reuse computation across edits. Likewise, cancellation can be an efficiency policy without changing which completed result is valid.

Basis: **documentation** + **derived** decomposition.

This separation aligns closely with Anneal's current design contract: verification success requires enough identity and scope to make its promise meaningful, while partial or incremental information must remain distinguishable from an ordinary successful result. PIDE supplies a concrete precedent for treating “which version is this about?” as semantic state rather than UI metadata.

### Semantic markup works because the prover, not the editor, knows the language state

The Isabelle/jEdit design delegates semantic interpretation to the prover and lets the editor render resulting markup as highlighting, squiggles, tooltips, hyperlinks, status, and active output. The 2012 system description emphasizes that most coloring beyond basic static keywords comes from the logical context. The 2019 overview describes XML markup accumulated over input sources and output trees and rendered without waiting for the entire prover computation to finish.

This matters for Anneal because source-oriented diagnostics are part of its stated user model. PIDE shows the value of preserving semantic provenance through the processing pipeline: the UI does not reconstruct meaning from text alone. But the precedent does not show that Anneal can recover Rust source intent from generated Lean diagnostics after the fact. That requires explicit source correspondence through Charon/Aeneas/Lean or another justified mapping layer.

Basis: **documentation** + **derived** Anneal applicability.

### PIDE's parallelism depended on Isabelle's internal functional architecture

The historical record ties PIDE closely to Isabelle's move to multi-threaded ML and parallel proof processing around 2008. The 2019 retrospective says an initial motivation for PIDE was to connect an IDE properly to a parallel proof engine. PIDE could let user-space tools participate in parallel processing because Isabelle's contexts, futures, and functional programming conventions were designed to support such execution.

The same record exposes costs. Shared-memory parallelism requires thread-safe tools and substantial resources; the 2019 overview notes that large live documents can require many cores and large memory, and that scaling to the whole AFP was still not automatic. It also reports accumulated conceptual and implementation complexity after a decade of PIDE development.

Basis: **documentation**.

The Anneal implication is conditional. A scheduler above Lean can run independent jobs concurrently, but that does not make hidden Lean/Aeneas state persistent, shareable, or safely reusable. Before Anneal models an internal dependency edge as reusable incremental state, the producing stage needs semantics that justify that reuse. Process-level parallelism and immutable content-addressed artifacts may be a cheaper substitute when such semantics are absent.

Basis for implication: **derived**.

### Protocol connectivity did not create document semantics in Coq

The Coq/PIDE experiment is the strongest negative control in this history. Wenzel reports that the core PIDE protocol was reimplemented in OCaml and connected successfully, but the semantic payload was restricted to lexical analysis. The paper explicitly separates that connectivity proof from full proof processing: obtaining the latter would require changes in Coq's own processing model, independently of the protocol mechanics.

The 2019 retrospective adds a maintenance outcome from the same author's perspective: the Coq/PIDE project did not reach end users and fell years behind subsequent PIDE development. It attributes the broader difficulty to the burden of maintaining distinct PIDE implementations for different provers. That retrospective is evidence of project outcome and author interpretation, not controlled evidence that one architectural choice caused the outcome.

Basis: **documentation** + **derived** evidence qualification.

For Anneal, the corresponding warning is direct: a versioned MCP/LSP/API layer can make state identity explicit, but it cannot manufacture incremental semantic states that Lean, Aeneas, or Charon do not expose. A protocol should not promise stronger freshness or reuse semantics than its back-end can establish.

### PIDE did support a weaker integration pattern for external tools

The 2019 paper's Naproche example demonstrates a useful middle ground. A non-Isabelle tool can participate in PIDE when treated approximately as a function from versioned input to source-positioned messages. Wenzel lists practical conditions: avoid hidden global filesystem state, report precise text offsets, start and finish quickly or be interruptible, and stream results incrementally when work is long-running. The Naproche integration kept a long-running server with an internal cache, but edits still produced a new text version and the service was responsible for avoiding redundant rechecking of unchanged sub-elements.

This is closer to Anneal's likely integration problem than Isabelle's native proof engine. It suggests two legitimate tiers:

- a **stateless or restartable stage** that consumes a complete immutable input version and emits version-qualified results; and
- a **stateful accelerator** that may cache or incrementally process work internally but must preserve the same external version/result semantics.

The second tier is an optimization of the first contract, not a reason to weaken it. If a warm service cannot establish that its answer belongs to the requested source/environment version, Anneal should prefer the slower path whose identity it can justify.

Basis: **documentation** + **derived** abstraction.

### PIDE's own integration strategy changed over time

The 2019 retrospective is valuable because it does not present the original plan as fixed. Isabelle/Scala began as an add-on integration layer but became an equal partner with Isabelle/ML. The private PIDE protocol started relatively simple and accumulated complexity. The initial ambition to retarget the same PIDE back-end protocol to other provers did not become a maintained multi-prover ecosystem, while headless/public APIs and alternative front-ends emerged instead.

That evolution weakens a simplistic lesson such as “define one generic prover protocol early.” PIDE's stable value was the document-processing model inside Isabelle; exact protocol shape and integration boundaries evolved around it. Anneal should therefore treat source/version/result semantics as the durable candidate contract and leave transport boundaries replaceable where practical.

Basis: **documentation** + **derived** judgment.

### Process boundaries are a genuine point of non-transfer

Early PIDE work argues that cutting conceptual components at process boundaries can expose accidental protocol details and make integration harder. That is a reasonable account of Isabelle's own ML/JVM integration problem. It is not a universal rule for Anneal.

Anneal has additional reasons to preserve process boundaries: independently versioned toolchains, native plugins, failure containment, resource accounting, environment isolation, and the need to make the trusted/external tool surface explicit. PIDE itself later discussed remote back-ends and headless interaction, and its Naproche example uses an external service. The transferable principle is therefore to avoid making transport accidents into semantic API promises, not to eliminate processes.

Basis: **documentation** + **derived** counterargument.

### Conditional judgment for Anneal

Given the current Anneal design contract, the strongest defensible transfer is:

1. **Make version identity explicit at every user-visible result boundary.** A diagnostic, proof state, or successful verification result should identify the Rust/source snapshot and other environment inputs whose evidence it represents. Do not use “latest” as an implicit semantic identity.
2. **Separate validity from scheduling.** Cancellation, prioritizing visible files, worker pools, and warm-state reuse are latency mechanisms. They must not determine whether a result is semantically attributable to the requested version.
3. **Allow provisional snapshots without promoting them to success.** PIDE can render whatever markup is available for a snapshot; Anneal can likewise expose partial diagnostics or proof-search state if it remains clearly provisional under the design contract.
4. **Treat stateful stages as accelerators behind a versioned contract.** The conservative reference behavior is full processing of a fully identified input/environment. A cache, prepared session, or long-running prover may answer faster only when Anneal can validate that it preserves the same meaning.
5. **Do not claim semantic incrementality above an opaque boundary.** If a translator or prover exposes only whole-file commands, use whole-file versioned jobs or seek an upstream contract. A coordinator-side DAG is not evidence that the upstream computation itself can be safely reused at those nodes.
6. **Carry semantic provenance for Rust-facing feedback.** PIDE's markup works because the prover supplies meaning tied to source regions. Anneal needs an analogous justified chain from Rust operation to generated obligation to Lean evidence; editor decoration alone cannot reconstruct it.
7. **Keep transport replaceable.** LSP, MCP, subprocess RPC, or an in-process library may carry the same versioned operations. Anneal should avoid promising raw Lean/Aeneas lifecycle details when a smaller semantic operation can remain stable.

These rules do not imply that Anneal needs PIDE's full document graph, one shared runtime, or fine-grained command transactions. A simpler versioned job scheduler with exact input/environment identity is the fallback and should remain a serious competitor until interactive latency evidence demonstrates that deeper stateful integration is necessary.

Basis: **derived** from the historical evidence and current Anneal design contract.

## Boundaries

The PIDE papers are predominantly first-party accounts by Makarius Wenzel, sometimes with other Isabelle authors. They are primary evidence for stated goals, mechanisms, and the authors' interpretation of project history. They are weaker evidence for causal claims such as why Coq/PIDE failed to reach users or why one integration boundary was globally superior. This report preserves those as attributed accounts and does not treat adoption as proof of optimality.

The report did not inspect every Isabelle source revision from 2008–2019. Its mechanism reconstruction is literature-driven. The strongest claims about versioned documents, asynchronous processing, cancellation, perspective, markup, and protocol evolution are documented directly in the cited papers and manuals; source-level implementation details outside those claims were not independently reconstructed.

The report does not claim that a PIDE document version is equivalent to an Anneal verification result, a Git commit, a content-addressed artifact, or an LSP document version. PIDE versions are internal states in a specific prover architecture. The transferable claim is about explicit semantic attribution, not identifier representation.

The report does not establish that fine-grained incremental checking is necessary for Anneal's first interactive workflow. PIDE demonstrates that it can support high-quality continuous proof editing when the prover is designed for it. It does not establish that this complexity beats whole-input jobs plus caching for Anneal's workload.

The report does not establish that process isolation is harmful. PIDE's early papers criticize protocols that expose accidental process-boundary details, but Anneal's heterogeneous and security-sensitive toolchain creates different isolation incentives. A process boundary can be appropriate if the semantic contract crossing it is small and explicit.

No fresh Isabelle execution was performed. Performance figures and scaling observations are author-reported historical observations, not measurements reproduced for this report.

## Evidence

Primary public evidence examined on 2026-09-30:

- Makarius Wenzel, **Isabelle/jEdit — a Prover IDE within the PIDE framework**, `arXiv:1207.3441v1`, 2012, https://arxiv.org/html/1207.3441v1 . Relevant sections: §1 overview, §2 system use, §3 implemented concepts. This describes Isabelle2011-1, continuous proof checking, editor/prover decoupling, semantic markup, and the first stable Prover IDE release.
- Makarius Wenzel, **Asynchronous Proof Processing with Isabelle/Scala and Isabelle/jEdit**, DOI `10.1016/j.entcs.2012.06.009`, UITP 2010 / ENTCS 285 (2012), pp. 101–114. Public author/index copies expose §2's persistent document versions, fresh version identifiers, command association, and asynchronous result delivery. This is the clearest early description of version semantics.
- Makarius Wenzel, **READ-EVAL-PRINT in Parallel and Asynchronous Proof-checking**, `arXiv:1307.1944v1`, DOI `10.4204/EPTCS.118.4`, 2013, https://arxiv.org/abs/1307.1944 . This frames PIDE as a deliberate break from the synchronous LCF read-eval-print loop.
- Makarius Wenzel, **PIDE as front-end technology for Coq**, `arXiv:1304.6626v1`, 2013, https://arxiv.org/abs/1304.6626 . The abstract and paper distinguish successful PIDE protocol connectivity and lexical payload from the prover reforms required for actual proof processing.
- Makarius Wenzel, **Interaction with Formal Mathematical Documents in Isabelle/PIDE**, `arXiv:1905.01735v1`, 2019, https://arxiv.org/html/1905.01735v1 . Relevant sections: §1.1, §1.2, §2, §3.1–§3.3. This retrospective explicitly discusses original aims, successes, failures, changed plans, document edits/versions, perspective, cancellation, snapshots, Naproche external-tool integration, protocol evolution, and the outcome of Coq/PIDE.
- Lawrence C. Paulson, Tobias Nipkow, Makarius Wenzel, **From LCF to Isabelle/HOL**, DOI `10.1007/s00165-019-00492-1`, Formal Aspects of Computing 31 (2019), pp. 675–698, https://doi.org/10.1007/s00165-019-00492-1 . §9.2 reports the 2008 parallel-ML transition, the conflict between parallelism and the traditional single-focus REPL, and Isabelle's 2014 discontinuation of REPL/Proof General interaction.
- Isabelle/jEdit manual, Isabelle2022 archived documentation, https://isabelle.in.tum.de/website-Isabelle2022/dist/library/Doc/JEdit/JEdit.html . The concepts section describes current PIDE as parallel/asynchronous document processing natively supported by the Isabelle/ML proof engine, and documents editor perspective as a processing hint. This is corroborative documentation, not the historical basis by itself.
- `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`. These are Anneal design authority for the applicability judgment: precise success identity/scope, no silent promotion of missing evidence, Rust-oriented diagnostics, explicit trust, and minimally sufficient mechanisms.

Evidence roles are **documentation** for first-party papers/manuals, **source** for the pinned Anneal design documents, and **derived** for the cross-project Anneal judgment. There is no fresh **execution** evidence.

## Revalidation

For a future Isabelle/PIDE architecture report, the cheapest historical revalidation is bibliographic: confirm that the immutable arXiv versions and DOI publications remain the cited subjects. The historical findings do not become false merely because current Isabelle evolves.

For transfer to a future Anneal design, revalidate the premises instead:

1. Read the then-current Anneal `PRINCIPLES.md` and `DESIGN.md` and check whether result identity, partial-result semantics, or tool-boundary constraints changed.
2. Inventory the actual APIs of the then-pinned Charon, Aeneas, Lean server, and any proof-session service. For each stage, record whether it accepts whole inputs or incremental edits; whether state is immutable/versioned; how dependencies are identified; how cancellation works; and how outputs identify their source/environment version.
3. For every proposed warm-state reuse path, compare a fresh isolated run with the warm path on matched inputs and deliberate edits. Agreement is useful evidence but not proof of semantic independence; inspect the implementation contract that makes reuse valid.
4. Inject an edit while an older job is running. Verify that the old result remains attributable to the old version and cannot be promoted to success for the new version. Repeat across cancellation, restart, and process-pool reuse.
5. Test source correspondence by forcing a known Rust-level obligation and confirming that any editor diagnostic is derived from preserved translation/proof provenance rather than heuristic text matching.
6. If Anneal proposes a PIDE-like fine-grained document engine, identify the upstream semantic operations that justify each incremental edge. If those operations do not exist, compare against the simpler versioned whole-input scheduler before adding an emulation layer.

A future upstream API that exposes immutable snapshots, precise dependency invalidation, interruptible evaluation, and source-positioned semantic results would materially strengthen the case for deeper PIDE-style integration. Conversely, if whole-input jobs with prepared sessions meet latency and resource goals, that evidence should favor deleting finer-grained orchestration machinery rather than reproducing PIDE for architectural resemblance.