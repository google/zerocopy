# Isabelle/PIDE: from command loop to document processing

## Summary

Isabelle/PIDE did not obtain responsive interactive proof merely by putting a protocol in front of the old prover loop. Its central architectural change was to make an evolving proof document, rather than a command prompt, the unit of interaction. Edits create explicitly identified document versions; the prover may evaluate them asynchronously and in parallel; results remain associated with the document material that produced them; obsolete work may be cancelled; and semantic markup accumulates while processing continues. By 2014 this model had displaced Isabelle's traditional TTY interaction rather than coexisting as a thin front end.

The history matters because it separates two classes of ideas that can otherwise be conflated when applying PIDE to Anneal.

Anneal can adopt several **outer orchestration invariants** without recreating Isabelle internally: give source/model generations explicit identities; attach diagnostics and interactive answers to the generation and source region that produced them; let computation proceed asynchronously; treat cancellation and prioritization as scheduling rather than correctness; preserve exact inputs needed to reconstruct service state; and keep stale results distinguishable from current verification evidence. These rules fit Anneal's existing requirement that successful verification have precise identity and scope.

PIDE's strongest benefits, however, depend on **semantic machinery inside the tool being reused**. Isabelle's prover owns persistent semantic contexts, command transactions, dependency structure, incremental snapshots, parallel futures, interruption, and semantic markup. A wrapper around a batch translator cannot infer those structures from paths, exit codes, or text output. Wenzel's Coq/PIDE experiment made that boundary explicit: implementing protocol connectivity and lexical markup was straightforward, while actual proof processing still required a reform of the prover toward document-oriented, "timeless and stateless" processing. The later Isabelle/Naproche integration shows an intermediate case: a batch-like external checker can participate if it behaves sufficiently like an explicit function from source to messages, but a heavy tool still required significant changes to become a persistent, interruptible, cache-bearing service.

The resulting Anneal judgment is conditional. **Borrow PIDE's explicit versioned-document discipline at orchestration boundaries, but do not turn PIDE into a mandate for one universal incremental engine.** Reuse incremental semantic state only where an upstream component can state and enforce its own reuse contract. Across Charon, Aeneas, Lake, and Lean, Anneal should retain explicit stage identities and conservative replacement boundaries until those tools expose narrower incremental semantics that Anneal can justify. Lean's existing language server can supply prover-internal snapshot semantics for Lean documents; Anneal can layer project/model generations around it. That does not make a Charon or Aeneas process, or the whole verification pipeline, a PIDE document processor by analogy.

Basis: primary PIDE papers and Isabelle documentation + current Anneal design authority + derived cross-project judgment.

## Applicability

This report addresses J018 of `google/zerocopy#3732`: the historical reform from command-loop interaction to Isabelle/PIDE document processing, the evolution of document versions, parallel checking, and semantic markup, and the boundary between ideas Anneal can adopt through orchestration and capabilities that require changes inside a prover or translator.

The historical account is anchored in Makarius Wenzel's 2019 retrospective, *Interaction with Formal Mathematical Documents in Isabelle/PIDE* (`arXiv:1905.01735v1`). That paper states that work on PIDE began in 2008, uses the 2009 Dagstuhl presentation as an early historical checkpoint, and evaluates successes, failures, and changes after roughly a decade. Earlier papers supply contemporary evidence for the initial document model and the transition away from synchronous READ-EVAL-PRINT. The 2013 Coq experiment supplies adverse portability evidence: a front-end protocol can be transplanted without thereby transplanting semantic document processing.

"Isabelle/PIDE" in this report therefore denotes an architectural lineage, not one frozen release. Mechanism claims are tied to the named papers or releases that state them. The report does not infer that an Isabelle2019 mechanism already existed in Isabelle2009, or that a proposal in an early paper necessarily survived unchanged.

The Anneal applicability analysis uses `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, especially `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`. Those documents require successful verification to identify its program or behavior, promises, and trusted assumptions precisely, but deliberately leave component boundaries and concrete mechanisms undecided. Statements below about what Anneal *should* borrow from PIDE are derived analysis, not adopted Anneal policy.

Several current `reference` reports already establish adjacent facts and should not be replaced by this history:

- `reports/lsp-proof-assistant-architecture-2026-09-27` explains modern LSP synchronization and Lean's concrete worker/snapshot architecture.
- `reports/anneal-interactive-pipeline-invalidation-graph-main-41f5b37` separates the freshness domains across Rust, Charon, Aeneas, generated Lean, Lake artifacts, and Lean server state.
- `reports/lean-generated-file-interactive-workflows-v4-30-0-rc2` explains the difference between generated filesystem bytes, open LSP document text, and imported Lean dependency state.

This report uses those as current Anneal context. Its new contribution is historical and comparative: why PIDE abandoned the prompt-centered model, which invariants made the document model work, what costs and failed transfers appeared, and which parts are portable above existing tools.

No Isabelle, Coq, Naproche, Charon, Aeneas, Lake, or Lean process was executed for this report. It does not measure latency, scaling, cancellation behavior, or cache effectiveness.

## Findings

### The architectural break was from prompt state to document history

The old interaction model made the prover prompt the synchronization boundary. A client sent one command, waited for the prover to read and evaluate it, consumed the response, and then sent the next command. That model exposes one advancing mutable state and makes editor responsiveness depend on command completion. It also frustrates parallel proof checking: even if the prover can evaluate independent work concurrently, a command-at-a-time interface serializes the user interaction around the prompt.

The early PIDE work replaced that boundary with a persistent document. The 2012 asynchronous-processing account describes explicit document versions created by purely functional updates. Commands are defined as identifiable source fragments and edits insert or remove them to produce a fresh version. Related versions can share substructure. Results arrive later and are associated with commands in a particular version rather than being delimited by the next prompt. The editor does not need to wait for the prover before accepting more edits.

This change matters more than the choice of transport. The user now interacts with a history of source states while the prover independently schedules semantic work. The protocol communicates *changes to a document model*; it is not merely a faster REPL.

Basis: **documentation/historical primary account** in Wenzel, *Asynchronous Proof Processing with Isabelle/Scala and Isabelle/jEdit*, DOI `10.1016/j.entcs.2012.06.009`; **documentation/historical primary account** in `arXiv:1207.3441v1`.

The 2013 READ-EVAL-PRINT paper makes the same transition explicit from the prover side. Its stated project is to break apart the classic loop and retrofit READ, EVAL, and PRINT into parallel and asynchronous processing. Between Isabelle2011-1 and Isabelle2012/2013, even the boundary between READ and EVAL changed: full outer-syntax parsing moved from READ to EVAL, allowing a theory to extend its own command language without relying on externally generated keyword tables. This is evidence against treating a familiar phase decomposition as a permanent semantic interface. PIDE retained the user-visible document abstraction while changing where work occurred internally.

Basis: **documentation/historical primary account** in Wenzel, *READ-EVAL-PRINT in Parallel and Asynchronous Proof-checking*, `arXiv:1307.1944v1`, DOI `10.4204/EPTCS.118.4`.

**Derived Anneal implication:** a stable outer identity can outlive a changing internal pipeline decomposition. Anneal can profit from explicit source/model generations without promising that "Charon stage", "Aeneas stage", or "Lean stage" will always correspond to one fixed cache, process, or protocol phase. Conversely, naming a current process or file path does not provide the historical property that PIDE got from explicit document versions.

### Document versions make concurrency observable without making every computation authoritative

By the 2019 retrospective, PIDE describes a document as a large expression of embedded sublanguages evaluated as a parallel functional program. User edits create new document versions; editing may cancel obsolete executions; and the editor sends a "perspective" that tells the prover which document portions are currently important to the user. Scrolling can therefore change scheduling priority without changing the document's logical meaning.

This is a useful separation of concerns:

- a **version** says which source state a result belongs to;
- **evaluation state** says what work has completed for that version;
- **perspective** says which useful work should be prioritized;
- **cancellation** suppresses work that is no longer worth finishing.

None of these alone establishes that a result is the current accepted theorem or verification outcome.

Basis: **documentation/historical primary account** in `arXiv:1905.01735v1`, §2.

PIDE's model also acknowledges that old versions consume resources. The 2013 READ-EVAL-PRINT account describes pruning document history periodically in Isabelle2013 rather than retaining every version forever. The design therefore did not get persistence "for free" from immutability; it still needed a lifetime and collection policy.

Basis: **documentation/historical primary account** in `arXiv:1307.1944v1`.

**Derived Anneal implication:** Anneal can use the same separation even when a stage remains one-shot. An immutable job or source generation can name what a query is about; scheduler priority can follow an editor or agent's current focus; cancellation can reduce obsolete work; and collection can reclaim old generations. The acceptance boundary should still check that the evidence being promoted belongs to the intended current verification subject. This is stronger than "cancel the old subprocess" and weaker than "make every stage incrementally persistent."

A serious alternative is a single mutable "current workspace" with a global ready flag. It is simpler to expose, and PIDE does not prove that every application needs multiple live versions. For Anneal, however, a global flag loses information when generation `G` is still answering an old query while generation `G+1` is being prepared, or when Rust, generated Lean, and imported artifacts advance at different times. The current Anneal corpus already records those separate freshness domains. Explicit generations therefore solve a concrete ambiguity, not merely an aesthetic preference for immutable data.

### Semantic markup is a product of the prover's semantic execution, not decoration inferred by the editor

PIDE continuously accumulates structured markup over source text while the prover processes the document. Isabelle/jEdit uses that markup for semantic coloring, underlines, tooltips, hyperlinks, active output, and other conventional IDE presentations. The 2019 retrospective explicitly distinguishes that semantic rendering from plain editor syntax highlighting.

The architecture puts an important burden on the backend. Source positions and semantic entities must survive long enough for output to be attached to the relevant source. When PIDE integrates external tools, Wenzel requires precise source offsets rather than line numbers and recommends incremental result streams so early approximate markup can appear before slower semantic checks finish.

Basis: **documentation/historical primary account** in `arXiv:1207.3441v1`; `arXiv:1905.01735v1`, §§1.1, 1.2, 2.4.

This distinction limits what an orchestration layer can synthesize. Anneal can always tag a batch diagnostic with the model generation and invocation that emitted it. It cannot, without additional evidence, reconstruct the semantic entity, proof context, or source-level cause that an upstream tool did not expose. A text parser that guesses which generated declaration an error "probably" refers to is not equivalent to prover-produced semantic markup.

**Derived Anneal implication:** preserve structured provenance whenever Charon, Aeneas, Lean, or a future service exposes it, and let specialists reach the underlying evidence. Use wrapper-generated structure only for facts the wrapper actually knows: stage identity, exact inputs, invocation, generation, file mapping that Anneal itself created, and acceptance status. Rich source-oriented explanations may require upstream contracts rather than increasingly clever scraping.

### PIDE's parallelism worked because the prover already exposed functional semantic structure

PIDE was motivated partly by the need to connect an IDE to Isabelle's parallel proof engine. The retrospective reports parallel Isabelle/ML as routinely available from 2008 and describes asynchronous interaction as the front-end counterpart to that engine. Document processing relies on immutable values, monotonic theory contexts, futures, command transactions, and a theory DAG. These structures let the prover decide what can run in parallel and what can be reused.

The same retrospective also records limits. In 2019, practical Isabelle/AFP development still required users to focus sessions manually; loading all of AFP blindly could cost roughly two orders of magnitude more resources than a large analysis session. Parallel Isabelle/ML scaled usefully on ordinary multicore machines, but anticipated consumer machines with very high core counts did not materialize, and NUMA made large shared-memory servers non-uniform. PIDE therefore demonstrates substantial parallel interactive checking, not cost-free whole-library liveness.

Basis: **documentation/historical primary account** in `arXiv:1905.01735v1`, §§1.1, 2.1, 3.3.

A tempting transfer would be to model the whole Anneal pipeline as one PIDE-style parallel functional program. The evidence does not support that. Isabelle's scheduler understands Isabelle semantic transactions because those transactions are represented inside the prover. Charon and Aeneas have their own process, filesystem, dependency, and translation boundaries. A generic Anneal scheduler can parallelize independent jobs, but it does not thereby know that two partially translated semantic states can be merged or reused soundly.

**Derived Anneal implication:** serialize authority changes only where correctness requires it, and allow independent computation to run concurrently. Let each upstream own semantic parallelism and incremental reuse that depends on its internals. At Anneal's boundary, require explicit immutable inputs and outputs or a documented service protocol before treating cached state as reusable.

### PIDE made unsaved and generated inputs first-class by removing ambient file reads from semantic commands

The document model has to process intermediate editor states, including unsaved buffers. In the 2019 account, PIDE-managed auxiliary files are attached to command tokens; the command implementation receives their source rather than reopening the global filesystem. This lets the prover check the editor's actual document version rather than an older saved file.

The same design appears in output handling. Isabelle2019 session exports publish generated blobs into session-managed storage rather than allowing arbitrary document commands to write globally visible physical files. Wenzel's rationale is concurrency: several document versions can be processed at once, so an uncontrolled write to one physical path would have no well-defined version ownership.

Basis: **documentation/historical primary account** in `arXiv:1905.01735v1`, §§2.1 and 2.3.

PIDE did not solve arbitrary external project graphs in this layer. The retrospective explicitly lists limitations for auxiliary-file handling: a load command handled one referenced file, and transitive exploration of an external language's include graph remained future work. This is a useful counterexample to an over-broad claim that "document orientation" automatically captures every dependency.

**Derived Anneal implication:** if Anneal offers live unsaved Rust or generated Lean, it should make those bytes part of an explicit input generation rather than relying on ambient path contents to happen to match. But Anneal still needs Cargo, Charon, Aeneas, Lake, and Lean dependency identities separately. A document snapshot is not by itself a proof that all transitive inputs have been captured.

### Naproche demonstrates a useful middle ground between full prover integration and one-shot batch orchestration

The Isabelle/Naproche case is unusually informative for Anneal because Naproche-SAD was an external Haskell checker rather than Isabelle's own proof engine. Wenzel describes it initially as a plain function from text to messages. In 2018 the authors reworked it for roughly two months into a reactive service. On each new PIDE text version the whole source is sent again, while the long-running backend caches results for unchanged sub-elements.

The integration depended on explicit engineering properties:

- invocation-local input/output instead of uncontrolled filesystem-global state;
- precise text offsets in diagnostics;
- low startup/latency for short tools;
- interruptibility for long-running work;
- incremental output for useful early feedback; and
- for the heavy Naproche process, a persistent service and internal cache.

The retrospective says the Haskell program had to change significantly to reach that service shape.

Basis: **documentation/historical primary account** in `arXiv:1905.01735v1`, §1.2.

This case weakens two extreme conclusions.

First, PIDE does **not** imply that an upstream tool must expose Isabelle-like command transactions before it can support responsive editing. A tool can remain conceptually close to a whole-input function and still gain responsiveness through process persistence, internal sub-result caching, interruption, and streamed messages.

Second, orchestration alone is **not** always enough. When startup dominates, diagnostics lack precise positions, global filesystem state leaks across versions, or work cannot be interrupted, the adapter cannot manufacture those missing properties. Naproche required backend work specifically because the useful interactive contract crossed the process boundary.

**Derived Anneal implication:** Charon or Aeneas could support a PIDE-like outer experience without adopting Isabelle's internal architecture. A modest upstream service contract might be enough: accept an explicit immutable input/model identity, emit position- or declaration-associated results, be interruptible, and optionally retain cache state whose validity rules are explicit. Anneal should measure whether such an upstream change buys enough latency or provenance to justify its maintenance cost. Until then, whole-stage recomputation on immutable inputs remains a coherent conservative boundary.

### The Coq experiment shows that transport portability is not semantic portability

The 2013 PIDE/Coq experiment deliberately separated protocol connectivity from proof processing. It reimplemented the core PIDE protocol layer in OCaml and used only lexical analysis as the semantic payload. That was sufficient as a proof of concept for connecting the front end. Wenzel then stated that actual proof processing required improving Coq toward "timeless and stateless" processing independently of PIDE's technical protocol.

Basis: **documentation/historical primary account** in `arXiv:1304.6626v1`.

The 2019 retrospective supplies the later outcome. Maintaining different PIDE backend implementations for different provers was judged cumbersome; the Coq/PIDE project had not reached end users and lagged later PIDE development. Meanwhile the once-basic private PIDE protocol itself accumulated complexity and sophistication.

Basis: **documentation/first-party retrospective** in `arXiv:1905.01735v1`, §3.2.

This is the strongest negative evidence against treating "thin adapter" as a universal solution. A protocol can standardize edits, requests, and rendering while leaving the hard semantic transition inside each backend. If the backend's natural state machine is incompatible with versioned asynchronous processing, an adapter either exposes weaker semantics or becomes a second implementation of the backend's hidden state.

**Derived Anneal implication:** a common Anneal service API should standardize what Anneal can own—identity, lifecycle, cancellation requests, result provenance, publication and acceptance—not pretend that Charon extraction, Aeneas translation, and Lean elaboration all support the same incremental operation. Backends may implement richer optional capabilities. A small common protocol should not make fake substitutability a correctness dependency.

### The architecture evolved by moving the integration boundary, not by preserving an original layering

PIDE began with Isabelle/Scala as a system-integration layer around Isabelle/ML. By 2019 Wenzel judged that conception insufficient: Isabelle/Scala and Isabelle/ML had become equal partners in the infrastructure, with parallel modules and complementary responsibilities. This change is not incidental. The IDE needed capabilities that crossed the original "prover versus integration shell" boundary.

The private protocol evolved similarly. Its initial conception was simple, then accumulated sophistication as the document model grew. The cost was real: two implementation languages increased the conceptual burden for users and developers, and retargeting the backend protocol to another prover demanded continuing maintenance.

Basis: **documentation/first-party retrospective** in `arXiv:1905.01735v1`, §§3.1–3.2.

This history argues against freezing Anneal's first convenient ownership boundary into a principle. It also argues against speculative generality. PIDE's mature boundary reflects more than a decade of pressure from a specific semantic engine and editor workload. Copying its component count or protocol vocabulary before Anneal has the same pressures would transfer costs without the evidence that justified them.

**Derived Anneal implication:** preserve low-cost seams that let an upstream translator or prover expose a richer service later, but keep today's interface minimally sufficient. An opaque backend capability such as "prepare explicit input generation", "query semantic state", or "cancel work" can grow without requiring Anneal to model prover-internal futures or command transactions prematurely.

### Semantic liveness and durable verification identity should remain distinct

PIDE document versions solve an interactive problem: they let the user continue editing while semantic processing of several related source states is in flight. Anneal's verification-success identity solves a stronger acceptance problem: it must make clear which Rust program or behavior, promises, evidence, and trusted assumptions a successful result covers.

The two identities can be related without being identical. An Anneal interactive generation may contain a PIDE/LSP document version as one coordinate. A final result may instead identify saved Rust inputs, compiler/translation identities, generated model digests, proof artifacts, and the TCB. The fact that a prover can display semantically checked markup for one live document snapshot does not by itself establish that Anneal has captured the complete verification subject required by its design contract.

Basis: **derived** from the PIDE historical model and `anneal/DESIGN.md`.

This distinction also clarifies stale results. PIDE can legitimately render partial markup as it becomes available. Anneal may similarly show provisional diagnostics or proof-state information from an older interactive generation when clearly labeled. But a stale or partial answer cannot acquire the meaning of successful verification merely because it is useful to the user.

### Conditional decision rule for Anneal

The evidence supports a boundary based on who can state the reuse invariant.

**Use orchestration-level versioning when Anneal itself can identify the relevant inputs and results.** This includes immutable Rust/model generations, stage invocation identities, generated-tree digests, prepared-environment identities, open-document versions, result provenance, cancellation, process replacement, and fail-closed publication.

**Use upstream incremental state when the upstream component exposes the semantic contract needed to know what remains valid.** Lean's own language server is the clearest current example because Lean owns its parser/elaborator snapshots and edit invalidation. A future Charon or Aeneas service could qualify if it similarly defines its accepted inputs, retained state, invalidation, outputs, and interruption semantics.

**Do not emulate hidden incremental semantics in the wrapper merely to resemble PIDE.** If the only safe contract is "run this version of the tool on this complete input and obtain this complete output," that is a legitimate backend boundary. Anneal can still schedule those runs asynchronously, cancel obsolete processes, cache immutable outputs, and keep the UI responsive.

**Ask for an upstream change when a concrete user-visible benefit requires a semantic fact the wrapper cannot know.** Examples include declaration-level invalidation, precise semantic source correspondence, persistent heavy caches, or reliable interruption within a long translation. Naproche shows that such a change may be much smaller than adopting a full PIDE architecture; Coq/PIDE shows that protocol glue alone is not the change.

This rule preserves PIDE's deepest lesson—the interaction model must match semantic state—without making Isabelle's implementation structure an architectural requirement.

Basis: **derived synthesis**.

## Boundaries

- **No causal monopoly.** The papers document motivations and first-party judgments, but they do not prove that PIDE's eventual success was caused by document versions rather than by Isabelle's existing proof language, implementation quality, staffing continuity, bundled distribution, or other factors. This report uses mechanisms and recorded design reasoning, not a single-cause success narrative.
- **No performance generalization.** Reported Isabelle parallelism, AFP resource use, or Naproche latency observations are historical workload data, not performance predictions for Anneal. No benchmark was reproduced.
- **No claim that every PIDE version is immutable forever.** The model exposes persistent versions to interaction, while implementations prune history and reclaim resources.
- **No claim that cancellation rolls back effects.** PIDE's design reduces uncontrolled effects specifically because concurrent obsolete versions can exist. External subprocesses and plugins can still require explicit cleanup or isolation.
- **No claim that PIDE captured every dependency.** The 2019 retrospective itself identifies incomplete support for multi-file and transitive external-language dependencies.
- **No claim that semantic markup is acceptance evidence.** Markup is structured feedback associated with document processing. Whether a particular result is logically authoritative depends on the prover and application contract.
- **No claim that protocol reuse yields semantic reuse.** The Coq experiment is evidence for the opposite boundary: connectivity can be demonstrated while full proof processing remains unimplemented.
- **No claim that a persistent process is inherently better.** Naproche used persistence because startup and checking were expensive enough that caching mattered. Cheap deterministic stages may be simpler and safer as one-shot processes.
- **No claim that Charon or Aeneas currently expose PIDE-like incremental contracts.** This report did not inspect their newest service APIs for that question and does not convert analogy into a current capability claim.
- **No claim that Lean's document version is Anneal's whole verification identity.** Current Anneal must also account for the Rust compilation subject, translator/model inputs, imported artifacts, tool identities, and trust/coverage relevant to the reported promise.
- **No recommendation to adopt Isabelle's ML/Scala split or private protocol.** The retrospective records both their benefits and their maintenance/conceptual costs.
- **No adopted Anneal policy.** The recommendations are conditional derived analysis under J018. `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` remain authoritative.

## Evidence

### PIDE retrospective: mechanisms, later changes, successes, and failures

Makarius Wenzel, *Interaction with Formal Mathematical Documents in Isabelle/PIDE*, `arXiv:1905.01735v1`, 2019-05-05.

Primary version: https://arxiv.org/html/1905.01735v1  
Record: https://arxiv.org/abs/1905.01735

Evidence role: **documentation / first-party retrospective**.

Material locations:

- Introduction and §1.1: work began in 2008; 2009 as an early design checkpoint; non-PIDE Isabelle interaction discontinued in October 2014; PIDE streams protocol messages and semantic markup while checking continues.
- §1.2: Isabelle/Naproche conversion from command-line checker to reactive service; whole-text resend plus cached unchanged sub-elements; requirements on filesystem state, offsets, startup, interruption, and streaming; significant backend changes for the persistent service.
- §2: edits create new document versions; cancelled obsolete evaluation; perspective-driven scheduling; XML semantic markup.
- §§2.1 and 2.3: theory DAG and monotonic context structure; session exports as controlled outputs under concurrent version processing; auxiliary source passed to commands rather than reread from ambient filesystem; stated limits for multi-file/transitive external-language loading.
- §2.4: online semantic markup is accumulated and rendered from a snapshot of current PIDE document state.
- §§3.1–3.3: Isabelle/Scala evolved from add-on integration layer to equal infrastructure partner; PIDE protocol gained complexity; Coq/PIDE maintenance did not reach end users; parallel Isabelle motivated asynchronous interaction; recorded hardware/scaling limits.
- Conclusion: interactive theorem proving imposes demanding execution-management requirements involving interruption, real-time feedback, parallelism, and external processes.

### Early asynchronous document model

Makarius Wenzel, *Asynchronous Proof Processing with Isabelle/Scala and Isabelle/jEdit*, Electronic Notes in Theoretical Computer Science 285 (2012), 101–114, DOI `10.1016/j.entcs.2012.06.009`.

Bibliographic/accessible record: https://doi.org/10.1016/j.entcs.2012.06.009

Evidence role: **documentation / contemporary design account**.

Material claims used here: explicit begin/end document scope in Isabelle2009/2009-1; persistent purely functional document updates; explicit version identifiers and version history; separately defined command-source identities; edit operations creating fresh versions; results associated with command/version rather than a prompt; editor-side history pointers; asynchronous editing that does not block on prover completion; unfinished proof attempts as first-class versions. The paper also records early limitations, including an initially single-theory history model.

### Isabelle/jEdit reference application

Makarius Wenzel, *Isabelle/jEdit --- a Prover IDE within the PIDE framework*, `arXiv:1207.3441v1`, submitted 2012-07-14.

Record: https://arxiv.org/abs/1207.3441

Evidence role: **documentation / contemporary design account**.

The abstract records continuous proof checking with semantic information arriving incrementally through an asynchronous protocol that neither blocks the editor nor prevents multicore parallelism. It also records semantic rendering through ordinary IDE affordances.

### Reformed READ-EVAL-PRINT

Makarius Wenzel, *READ-EVAL-PRINT in Parallel and Asynchronous Proof-checking*, `arXiv:1307.1944v1`, EPTCS 118 (2013), 57–71, DOI `10.4204/EPTCS.118.4`.

Record: https://arxiv.org/abs/1307.1944  
DOI: https://doi.org/10.4204/EPTCS.118.4

Evidence role: **documentation / contemporary architectural account**.

Material claims used here: deliberate decomposition of the synchronous REPL into asynchronous phases; persistent document history; periodic history pruning in Isabelle2013; protocol interpreter requirements for short, total protocol operations; and the historical move of full outer-syntax parsing from READ in Isabelle2011-1 into EVAL in Isabelle2012/2013 so command syntax could evolve inside theories.

### PIDE/Coq portability experiment

Makarius Wenzel, *PIDE as front-end technology for Coq*, `arXiv:1304.6626v1`, submitted 2013-04-24.

Record: https://arxiv.org/abs/1304.6626

Evidence role: **documentation / contemporary experiment account**.

The abstract distinguishes reimplementation of the PIDE protocol in OCaml and lexical-analysis payload from actual proof processing. It states that real proof processing requires reforming Coq toward document-oriented "timeless and stateless" processing independently of protocol mechanics. The 2019 retrospective supplies the later assessment that maintaining another PIDE backend was cumbersome and the Coq integration did not reach end users.

### Isabelle user documentation

Isabelle/jEdit manual source, Isabelle2022, `Theory JEdit`.

Published HTML: https://isabelle.in.tum.de/website-Isabelle2022/dist/library/Doc/JEdit/JEdit.html

Evidence role: **documentation**.

The manual describes Isabelle/jEdit as combining parallel proof checking with asynchronous interaction and document-oriented continuous proof processing. It is supporting evidence that the document-oriented account remained part of Isabelle's user-facing architecture after the 2019 retrospective, not an immutable implementation revision used for source-level claims.

### Anneal authority and adjacent corpus evidence

Repository: `google/zerocopy`  
Revision: `cc135f46155b72e4b51188525c2974a3b84acf92`

- `anneal/PRINCIPLES.md`
- `anneal/DESIGN.md`

Evidence role: **normative for Anneal**. These files supply the requirement for precise verification meaning, fail-closed results, explicit trust, minimally sufficient mechanisms, and the deliberate non-decision about exact component boundaries.

Current `reference` reports consulted for overlap:

- `reports/lsp-proof-assistant-architecture-2026-09-27`
- `reports/anneal-interactive-pipeline-invalidation-graph-main-41f5b37`
- `reports/lean-generated-file-interactive-workflows-v4-30-0-rc2`

Evidence role: **existing reference synthesis/source analysis**. They establish current protocol and Anneal pipeline facts that this historical report does not re-investigate.

## Revalidation

This report is mostly historical. Revalidation should therefore distinguish changing Anneal context from fixed historical claims.

For the PIDE history, first re-read the exact archived publications named in `REPORT.json`. Their central historical claims do not become stale when current Isabelle changes. If a later primary retrospective corrects the chronology, reports a materially different reason for a design change, or supplies contrary evidence about the Coq/Naproche outcomes, compare that source explicitly rather than silently replacing the older first-party account.

For current Isabelle applicability, inspect the current Isabelle/PIDE manual and implementation only if the engineering question depends on whether a historical mechanism still exists. In particular, re-check how current document versions, cancellation, dependency handling, semantic markup, and headless interfaces are represented before treating the 2019 architecture as a present API contract.

For Anneal applicability, re-read current `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`, then re-check the reference reports that own present Charon/Aeneas/Lean freshness and interaction semantics. The judgment changes materially if, for example, Charon or Aeneas acquires an upstream incremental service with explicit invalidation/provenance contracts, or if Anneal adopts a different authoritative verification-subject model.

The cheapest discriminating check for the report's main conclusion is:

1. identify the state Anneal itself can version without guessing;
2. identify any reuse that depends on hidden semantic state inside an upstream tool;
3. ask whether that tool exposes a documented validity/invalidation contract for the reuse;
4. if not, keep Anneal's boundary at immutable complete inputs/outputs even if scheduling around that boundary is asynchronous;
5. if yes, evaluate the service contract on its own evidence rather than assuming PIDE's internal model transfers.

New benchmarks would be useful only for questions such as latency, memory, restart cost, or the benefit of persistent caches. They are not required to re-establish the architectural distinction between orchestration-owned identity and backend-owned semantic reuse.