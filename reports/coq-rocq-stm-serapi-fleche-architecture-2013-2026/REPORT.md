# Coq/Rocq document processing: STM, SerAPI, Flèche, and semantic-service boundaries

## Summary

Coq/Rocq's interactive architecture evolved through three distinct layers that are easy to collapse into one story: a prover-internal document model, a machine-facing protocol over that model, and a later reusable incremental document engine. Their differences matter more to Anneal than the shared fact that each can sit behind an editor or client.

The first major change was semantic, not transport-level. Coq's State Transaction Machine (STM) replaced the classic single-focus command loop with a document graph whose edges are commands and whose nodes represent prover states. Proof tasks could then be separated from the document spine, delayed, prioritized, and in suitable cases checked out of order. The 2015 STM paper reports large responsiveness and parallel-checking improvements on the Odd Order development, but those gains came only after Coq itself learned which work was independent, which commands had global effects, how to restore state, and how to execute commands atomically. A client protocol could not infer those facts from command text alone.

SerAPI made that machinery much easier to automate. It serialized Coq's internal structures and exposed document operations such as `Add`, `Exec`, `Cancel`, and `Query`. That was a major interface improvement, but it did not turn the underlying state machine into immutable snapshots. SerAPI's own protocol documentation says that parsing an added sentence depends on its parent state, because commands such as `Notation` can change parsing; it also records a hard STM limitation where cancelling an unexecuted suffix can force execution of earlier work. State or sentence identifiers were therefore handles into a semantic machine, not self-contained proofs that a result described a particular immutable document version.

Rocq LSP and its Flèche engine move further toward a document service. At the pinned current revision, Flèche explicitly stores a document URI, language identifier, integer version, contents, node list, completion status, external environment, and root Rocq state. Individual nodes retain full Rocq states and cache statistics. The service supports continuous or on-demand checking, positional requests keyed by `VersionedTextDocumentIdentifier`, cache-aware recovery, interruptions, multiple workspaces, and a lower-latency Petanque interface. Project configuration is part of the environment: Rocq LSP reads `_RocqProject` or `_CoqProject`, and Flèche's document environment carries workspace and file state used to build the root prover state.

This progression supports a narrow conclusion for Anneal. Anneal can and should own **external context identity and result authority**: exact source/model snapshot, toolchain and plugin identity, project/build configuration, generated inputs, requested operation, process generation, supersession, cancellation of obsolete work, and the rule that decides whether a result may be accepted or published. It should not manufacture **prover- or translator-internal reuse semantics** above an opaque command interface. Reusing a long-lived Charon, Aeneas, Lean, or other semantic process is sound only to the extent that the upstream interface defines the lifetime, invalidation, dependency, interruption, and version semantics needed for the claim Anneal is making. Where that contract is absent or too weak, versioned whole-input execution remains the conservative backend.

The same boundary applies to interactive recovery. Flèche deliberately keeps partially broken documents useful and may automatically admit unfinished proof fragments for editor continuity. That is good IDE behavior and bad evidence for an ordinary Anneal success unless a separate authoritative check establishes the final result. Responsiveness state and verification state must therefore remain different concepts even when both are produced by one daemon.

## Applicability

This report addresses #3732 **J019 — Coq/Rocq: transaction machines, SerAPI, and language servers**. It asks what the Coq/Rocq history says about asynchronous checking, transaction/document semantics, machine protocols, and later language-server architecture, and then applies that history to Anneal's process and component boundaries.

The historical evidence is pinned to the following primary identities:

- Barras, Tankink, and Tassi, *Asynchronous Processing of Coq Documents: From the Kernel up to the User Interface*, ITP 2015, arXiv:1506.05605, DOI 10.1007/978-3-319-22102-1_4;
- Wenzel, *PIDE as front-end technology for Coq*, arXiv:1304.6626v1 (2013);
- `rocq-archive/coq-serapi@6196f9f572ef9dd3749b885cabce7a57406cedb9`, the current archived SerAPI `main` revision observed on 2026-09-30;
- `rocq-community/rocq-lsp@2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe`, the current Rocq LSP `main` revision observed on 2026-09-30; and
- `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, the current Anneal design revision observed on 2026-09-30.

The report is architectural history, not a benchmark. It reconstructs documented mechanisms and author-reported outcomes and uses those as evidence for a conditional design judgment. It does not claim that Rocq LSP is the optimal document engine, that Coq's specific state model transfers directly to Lean or Aeneas, or that the 2015 performance results predict Anneal's latency.

The current `reference` corpus already contains reports on proof-assistant protocols, trust, caching, and interactive verification. At reference revision `249263d6b8c2aed57a3d2757947458e636f126c0`, catalog metadata contains Rocq as a subject in broader reports but no direct package/topic/subject match for the STM–SerAPI–Flèche architectural history and judgment developed here. That metadata check is an overlap accelerator, not proof that every report body is semantically disjoint.

## Findings

### 1. The STM was a semantic redesign of document execution, not a new wire protocol

The classic interactive-prover model is a command loop: send one command, mutate the current prover state, receive output, repeat. Undo is possible if the prover saves enough state, but the command stream itself does not necessarily explain dependencies, independent work, or which earlier state a later result belongs to.

The STM work changed that representation. The 2015 paper describes a directed acyclic graph in which nodes are system states and edges are commands. The term *transaction* refers to atomic command execution: there is no represented partially executed command. Static analysis classifies commands so proofs can be separated from global document structure and treated as tasks when their dependencies permit it.

That distinction matters because concurrency is downstream of semantics. The system can prioritize or reorder proof tasks only after it knows what can be moved without changing meaning. In particular, the paper treats global-effect commands separately instead of assuming that every proof-language command is a pure independent computation. Parallel execution is therefore not something a generic scheduler can safely recover from a byte stream of commands.

The authors report that the redesigned system was about ten times more reactive on the full Odd Order development and that full checking on a twelve-core machine was about four times faster than before. Those figures are evidence that the semantic redesign enabled useful scheduling; they are not evidence that a particular worker count, task granularity, or daemon architecture is universally optimal.

**Anneal implication.** If an Anneal stage exposes only “feed this command into the current process,” Anneal cannot safely infer a hidden dependency graph merely because commands look separate. Fine-grained reuse or out-of-order evaluation must come from a contract that identifies the semantic units, their dependencies, and their invalidation rules—or Anneal must use a coarser unit that it can validate independently.

### 2. Parser state is part of semantic state

SerAPI makes a subtle dependency explicit. A sentence has a parent state, and the parent matters even for parsing because earlier commands such as `Notation` can change how later text is parsed. `Add` is therefore not equivalent to a pure `parse(text)` call independent of prior document state.

This is a concrete counterexample to a common orchestration shortcut: keying semantic work only by source bytes. If the interpretation of a source fragment depends on prior declarations, imports, notation, configuration, or environment, then text identity alone is insufficient to identify the result.

Rocq LSP's later architecture reinforces the point at a larger scale. Its user manual reads `_RocqProject` or `_CoqProject` from a project root, and Flèche's document environment contains the initial Rocq state, workspace, and file state used to construct the document root. The document's `version` and `contents` live alongside that environment rather than replacing it.

**Anneal implication.** The semantic cache key for a translator or prover result must cover every upstream input that can change meaning, not merely the Rust, LLBC, or Lean text. Depending on the stage, this may include toolchain/plugin revisions, crate/build configuration, feature/cfg selections, imported artifacts, workspace state, environment assumptions, and generated inputs. A version number is useful only when its relationship to those inputs is defined.

### 3. Atomic command transactions do not imply ACID-style rollback or immutable snapshots

STM terminology can mislead readers familiar with databases. In this architecture, a transaction is primarily an atomic prover command/state transition. It says that clients do not observe half of one command's execution. It does not automatically imply durable commits, isolation among arbitrary concurrent clients, an immutable snapshot API, or cheap rollback of all uncommitted work.

SerAPI's cancellation caveat shows the difference. The protocol exposes `Cancel` and reports which sentence IDs are no longer valid, but its pinned interface documentation says cancelling a non-executed part is poorly supported by the underlying checking algorithm and can force execution up to the previous sentence. It calls this a hard limitation of the STM. A client that treated `Cancel` as database rollback would therefore infer a stronger semantic contract than the implementation provides.

**Anneal implication.** Process controls such as interrupt, cancel, reset, request ID, or “state ID” should be interpreted according to the upstream contract, not their names. Cancellation can be useful for responsiveness while still being unsuitable as evidence that every effect of obsolete work was rolled back. Anneal's acceptance rule must instead bind a returned result to the exact context it was asked to describe and reject stale or mismatched results regardless of what happened internally during cancellation.

### 4. SerAPI improved machine access without creating a new semantic document model

SerAPI's main contribution was machine-friendly access: serialization and deserialization of core Coq structures plus a document-building/query protocol. Its README identifies IDEs, code-analysis tools, and machine learning as target use cases. `Add`, `Exec`, `Cancel`, `Query`, and `Print` expose operations that previously required clients to depend on less structured interfaces.

This is a major engineering improvement, but the protocol's semantics are inherited from the underlying Coq document machinery. `Exec sid` checks a sentence and its dependencies. Queries name a sentence/state ID and do not necessarily force that state to execute. `Cancel` invalidates states according to STM behavior. The interface makes the semantic machine addressable; it does not make every handle an immutable value.

The current archived SerAPI README now says development has stopped and that SerAPI has been succeeded by coq-lsp, which addresses longstanding issues and feature requests. That is a maintainer account of succession, not an experiment proving that all SerAPI limitations caused the later architecture. Still, it is consistent with the source-level difference: Rocq LSP is built around Flèche, described as a new document-checking engine, rather than merely repackaging the same command protocol behind LSP messages.

**Anneal implication.** A structured JSON/S-expression/RPC protocol is not by itself a semantic service contract. It can make orchestration cleaner while leaving all state-lifetime and invalidation questions unchanged. Anneal should evaluate a persistent backend by the semantics it exposes, not by whether the transport is typed or machine-readable.

### 5. PIDE-to-Coq is a useful negative control for “protocol connectivity equals integration”

Wenzel's 2013 PIDE-to-Coq experiment deliberately separated protocol connectivity from prover-side document processing. The experiment reimplemented the core PIDE protocol layer in OCaml and was sufficient for lexical processing and proof-of-concept connectivity. The paper then says that actual proof processing would require Coq to move toward the timeless/stateless style of document processing that PIDE relied on.

This is strong architectural evidence because it holds the front-end infrastructure relatively constant while exposing the missing semantic ingredient. The front end could exchange document edits and render semantic output, but the prover still needed an internal model that gave those edits stable meaning and supported asynchronous processing.

It would be too strong to conclude that all generic protocols are weak or that every integration must copy Isabelle/PIDE. The narrower lesson is that transport cannot supply semantic invariants that the backend does not already expose or enforce.

**Anneal implication.** Wrapping an opaque Charon/Aeneas/Lean invocation in a daemon, LSP, or RPC layer may reduce process startup and parsing overhead. It does not, without additional semantics, justify reuse across changing Rust inputs, generated artifacts, build configurations, or proof states.

### 6. Flèche makes document identity, semantic state, and external environment explicit

At `rocq-community/rocq-lsp@2e0c43c...`, Flèche's `Doc.t` contains:

- document URI and language identifier;
- an integer document `version`;
- the document `contents`;
- a list of document nodes;
- completion status and document table of contents;
- an external environment containing an initial Rocq state, workspace, and files; and
- a root Rocq state derived from that environment.

Each node contains its source range, previous node, optional AST, full Rocq state, diagnostics/messages, and timing/cache information. That is substantially more semantic structure than a transport-level request sequence number. It gives the engine a place to define what state corresponds to a source range and document version, what environment produced it, and what can be reused.

The engine also records completion states such as fully checked, stopped, workspace-updated, and failed. Those distinctions matter because a document can have useful partial semantic state without being a successfully checked whole document.

**Anneal implication.** If Anneal relies on an upstream incremental engine, it should prefer an interface whose versioned objects correspond to semantic contexts, not merely wire requests. Even then, Anneal should preserve its own external context identity and acceptance fence so an upstream cache remains an implementation detail rather than the sole source of result identity.

### 7. Rocq LSP separates scheduling policy from document semantics

Rocq LSP offers continuous checking and on-demand checking. In continuous mode it eagerly checks open documents; in on-demand mode it can remain idle until a client asks for information such as goals. A viewport-guided mode can prioritize what is visible. The same semantic document engine therefore supports different scheduling policies.

The `proof/goals` request illustrates the contract. Requests use a `VersionedTextDocumentIdentifier` plus a source position, and the server may execute the document up to that position to answer. The answer carries the versioned document identity and position as well. This is a more useful boundary than “request 42 succeeded”: the question and answer are tied to a source version and semantic location.

The design also has a Petanque protocol intended for low-latency programmatic interaction. The existence of a specialized low-latency surface alongside LSP is further evidence that transport shape and semantic engine are separable design choices.

**Anneal implication.** Anneal can safely own queueing priorities—foreground vs background, current vs superseded work, interactive vs batch—without owning prover-internal semantics. A single upstream semantic engine can support several scheduling policies if it defines the meaning of the states being scheduled.

### 8. Incremental reuse has an explicit correctness and invalidation cost

The benefit of an incremental document engine is reuse: unchanged work can be retained while changed portions are recomputed. Rocq LSP advertises incremental checking and records cache statistics at document nodes. But its own README also notes that incremental support is still being refined and asks users to report unnecessary rechecking. Flèche recognizes workspace updates as a distinct completion state and can recreate a document after a full workspace update.

This illustrates the two failure directions of a cache:

- **under-reuse** recomputes valid work and hurts latency or throughput;
- **over-reuse** retains state whose dependencies changed and threatens correctness.

The first is mostly performance. The second is semantic. A cache policy is therefore part of the trusted behavioral boundary whenever stale reuse can change an authoritative result.

**Anneal implication.** Anneal should avoid reverse-engineering fine-grained dependency validity from opaque tool state. If an upstream engine owns and documents its dependency graph, Anneal can treat that engine as part of the relevant trust boundary and key the service instance by Anneal's external semantic context. If it does not, stable artifact caching or whole-input reruns are safer than speculative state reuse.

### 9. Project/workspace configuration is a semantic dependency, not editor decoration

Rocq LSP loads project configuration from `_RocqProject` or `_CoqProject`, supports multiple workspaces, and places workspace/files in the external document environment. Those settings affect the root state from which document checking begins.

That makes workspace changes qualitatively different from moving an editor pane. A new load path, library mapping, implicit import, or project root can change how the same document text is interpreted. Flèche's explicit `WorkspaceUpdated` state is therefore not merely UI bookkeeping.

**Anneal implication.** Persistent processes must be invalidated or re-keyed when configuration that contributes to semantic interpretation changes. For Rust verification, that includes build configuration and selected dependency/toolchain worlds. An editor-style “same file path, new text” identity is too weak for authoritative verification unless all other semantic inputs are already fixed by the process generation.

### 10. Error recovery deliberately produces useful states that are not verification success

Rocq LSP is intentionally tolerant while a user edits. Its documentation says it can continue checking documents that are only partially working, recognizes proof structure during recovery, and can automatically admit unfinished proof fragments so later parts remain usable.

This behavior is desirable for an IDE: it preserves feedback instead of turning every transient edit into a dead document. But an automatically admitted proof is precisely the kind of state that cannot silently acquire the meaning of a completed proof.

Anneal's current design contract makes the distinction explicit. Missing evidence, unsupported semantics, omitted coverage, or a tool failure cannot become verification success because the pipeline continued. Development and incremental modes may expose partial information, but their meaning must remain different from an ordinary successful result.

**Anneal implication.** A persistent semantic service may return two broad classes of information:

1. **advisory/editor state**, useful even when the current input is incomplete or recovered; and
2. **authoritative verification evidence**, accepted only after the full Anneal success predicate is satisfied.

The same process can produce both, but they need separate result types or acceptance states. Freshness alone is not enough.

### 11. Interruption is a responsiveness mechanism, not a proof of rollback

Rocq LSP supports real-time interruption and uses interruption to keep continuous checking responsive. Flèche represents an interrupted check as a stopped document at a particular valid token range and can later resume checking.

That is a useful operational contract: obsolete work need not monopolize a worker, and the system can preserve a valid prefix. It still does not imply that every internal side effect is transactionally rolled back or that a cancelled request could never have affected caches. Those stronger properties would need their own specification.

**Anneal implication.** Anneal may aggressively cancel superseded computations for latency while treating cancellation as an optimization only. Correctness should come from result identity plus a fail-closed publication fence: a result is usable only if it matches the still-current requested context and satisfies the relevant validation predicate.

### 12. The engineering cost of a semantic document service is upstream coupling

A Flèche-like service offers the best responsiveness when it can retain and reuse meaningful prover state. The cost is that it must understand the prover deeply. Its nodes hold full Rocq states. Its parser and evaluator handle interruption and diagnostics. Its environment knows workspaces and imported files. Its cache and error recovery understand proof structure.

This is not accidental complexity around LSP. It is the machinery required to answer questions such as “which old state is still valid after this edit?” without replaying everything.

An external orchestration layer has a different advantage: it can remain independent of prover internals and evolve around stable process/file interfaces. That independence is lost if it tries to recreate prover-specific semantic incrementality by inspecting undocumented internal behavior.

**Anneal implication.** Put fine-grained semantic reuse where the semantic knowledge already lives. Anneal should prefer upstream changes or supported semantic APIs when it needs fine-grained persistent-state reuse. It should keep generic orchestration mechanisms—workspace construction, process generations, queues, cancellation, artifact caches, validation, and publication—outside.

### 13. Serious alternatives form a continuum, not a daemon/no-daemon binary

There are at least four viable architectural points:

**Whole-input one-shot execution.** Each authoritative request starts from an explicit complete context and runs to completion. This has the simplest validity model and makes process state disposable. Its cost is startup and recomputation latency, plus weaker interactive queries.

**Persistent process with command replay.** A long-lived process can amortize startup and expose richer queries without promising fine-grained semantic reuse. Anneal can reset or restart it at conservative boundaries. This can improve latency while keeping a relatively coarse correctness model, but any retained state still needs a generation/context boundary.

**Upstream semantic document service.** A Flèche-like engine exposes versioned documents, internal states, dependency-aware reuse, interruptions, and positional queries. This offers the best fine-grained responsiveness when its semantics are trustworthy. The cost is upstream-specific complexity, memory, lifecycle management, and tighter coupling to the prover/translator's internal state model.

**Stable artifact cache between one-shot stages.** Instead of retaining live semantic state, cache independently identifiable artifacts—parsed modules, translated IR, compiled libraries, proof objects—whose validity can be keyed and checked. This sacrifices some fine-grained reuse but can give a much stronger cross-process identity and reproducibility boundary.

A hybrid is often best: persistent services for advisory interaction, stable artifacts for durable reuse, and whole-input authoritative checks at the boundary where upstream incremental semantics are not strong enough.

### 14. Conditional judgment for Anneal: own the envelope, borrow semantic incrementality

The Coq/Rocq history does not justify a general rule that Anneal should or should not use daemons. It supports a property-relative boundary.

Anneal should own the **envelope** around every semantic computation:

- exact source/model and generated-input identity;
- build/project configuration and toolchain/plugin identity;
- process or service generation;
- operation identity and requested position/unit when relevant;
- scheduling, prioritization, and cancellation of obsolete work;
- freshness/supersession checks on returned results;
- stable artifact identity and durable caches where applicable; and
- the acceptance/publication fence that decides whether a result counts as verification success.

Anneal should **borrow semantic incrementality** from an upstream component only when that component defines enough of the following to make reuse meaningful:

- document or snapshot version identity;
- semantic dependencies, including configuration/environment dependencies;
- state lifetime and invalidation;
- meaning of cancellation/interruption;
- treatment of partial/recovered states;
- relation between positional/advisory answers and fully checked outputs; and
- any artifact or proof object needed to make the result independently checkable.

If those properties are underspecified, Anneal should fall back to a coarser boundary rather than infer them. A persistent process can still be used as an implementation optimization, but its opaque live state should not become authority for whether a result applies to the current Rust program.

This preserves Anneal's current design constraints. It keeps verification identity explicit, avoids silently strengthening evidence, makes trust visible, and allows stronger upstream services to replace conservative whole-input execution later without changing the meaning of successful results.

## Boundaries

- No Coq/Rocq, SerAPI, Flèche, or Petanque binary was executed for this report. Mechanism claims come from primary publications and pinned first-party source/documentation.
- The 2015 performance figures are author-reported on selected Coq workloads. They are evidence that the redesigned architecture enabled useful responsiveness/parallelism, not a benchmark for Anneal or a universal speedup claim.
- The word *transaction* in STM is used in Coq's command-execution sense. This report does not attribute ACID database semantics to the STM.
- The PIDE-to-Coq experiment was deliberately limited. It demonstrates that protocol connectivity and prover-side semantic reform are distinct; it does not prove that PIDE is the only or best architecture for other provers.
- SerAPI and Rocq LSP evidence spans different generations of Coq/Rocq. The report treats that evolution as documented architectural history, not as a controlled experiment where only one variable changed.
- The archived SerAPI README's claim that coq-lsp solves longstanding issues is an author/maintainer characterization. The report does not infer which particular issues causally required Flèche unless pinned source or documentation supports the mechanism.
- Rocq LSP's recovery behavior is explicitly interactive. Automatically admitted or partially checked states are not treated here as evidence of theorem validity.
- Catalog metadata was used only to screen for obvious overlap in the current `reference` corpus. A later coordinated adoption must reread current report bodies and competing candidate salvage before treating this package as J019 coverage.
- Anneal implications are derived engineering analysis. They are not an adopted Anneal design decision, and `anneal/DESIGN.md` deliberately leaves component boundaries undecided.

## Evidence

### E1 — Coq STM paper: semantic document graph and asynchronous checking

**Identity:** Bruno Barras, Carst Tankink, Enrico Tassi, *Asynchronous Processing of Coq Documents: From the Kernel up to the User Interface*, ITP 2015, arXiv:1506.05605, DOI 10.1007/978-3-319-22102-1_4.

**Primary locator:** https://arxiv.org/abs/1506.05605

**Role:** historical rationale and implementation account for redesigning Coq document processing; DAG/state-transaction model; proof-task separation; global-effect handling; task reordering; author-reported responsiveness and parallel-checking outcomes.

**Interpretation boundary:** author intent and reported outcomes are attributed to the paper. The Anneal boundary conclusions are derived analysis.

### E2 — PIDE-to-Coq experiment: connectivity without full semantic processing

**Identity:** Makarius Wenzel, *PIDE as front-end technology for Coq*, arXiv:1304.6626v1 (2013).

**Primary locator:** https://arxiv.org/abs/1304.6626

**Role:** negative control separating implementation of the PIDE protocol/front-end connection from prover-side reforms needed for actual asynchronous proof processing.

**Interpretation boundary:** the experiment implemented a limited payload, so it is evidence about architectural separation, not a performance comparison of PIDE and later Coq interfaces.

### E3 — SerAPI archived source and protocol

**Identity:** `rocq-archive/coq-serapi@6196f9f572ef9dd3749b885cabce7a57406cedb9`.

**Files:**

- `README.md`, blob `85c5708fe72147f103c87e2316403697f4c51214`;
- `serapi/serapi_protocol.mli`, blob `ed3ed38c409d0dc778709c7eeb73bd290f67c006`.

**Permalinks:**

- https://github.com/rocq-archive/coq-serapi/blob/6196f9f572ef9dd3749b885cabce7a57406cedb9/README.md
- https://github.com/rocq-archive/coq-serapi/blob/6196f9f572ef9dd3749b885cabce7a57406cedb9/serapi/serapi_protocol.mli

**Observed mechanisms:** machine-oriented serialization; document-building API; parent-state-sensitive parsing; separate `Add` and `Exec`; `Cancel` invalidation; query-by-state ID; explicit caveat that cancelling a non-executed part can force execution to the previous sentence and is a hard STM limitation.

### E4 — SerAPI technical report

**Identity:** Emilio Jesús Gallego Arias, *SerAPI: Machine-Friendly, Data-Centric Serialization for Coq*, HAL `hal-01384408` (2016).

**Locator recorded by the project:** https://hal-mines-paristech.archives-ouvertes.fr/hal-01384408

**Role:** project motivation and intended machine-facing/data-centric interface. Pinned repository source is preferred for exact current archived protocol behavior.

### E5 — Rocq LSP / Flèche current repository

**Identity:** `rocq-community/rocq-lsp@2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe`, current `main` observed 2026-09-30.

**Files:**

- `README.md`, blob `37b132ed9c7e15bb4e11205e110d592a1503a6b6`;
- `etc/doc/USER_MANUAL.md`, blob `2b989fcf528d08ef3c58b115f45248d2cf4e0bcc`;
- `etc/doc/PROTOCOL.md`, blob `30d2b18cefd1d2b6fdd3493b744426c29b482c57`;
- `fleche/doc.ml`, blob `2cb236a36a17acf610c971308e8c9962b341e74f`.

**Permalinks:**

- https://github.com/rocq-community/rocq-lsp/blob/2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe/README.md
- https://github.com/rocq-community/rocq-lsp/blob/2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe/etc/doc/USER_MANUAL.md
- https://github.com/rocq-community/rocq-lsp/blob/2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe/etc/doc/PROTOCOL.md
- https://github.com/rocq-community/rocq-lsp/blob/2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe/fleche/doc.ml

**Observed mechanisms:** continuous and on-demand checking; incremental/cache-aware behavior; proof-structured recovery; automatic admission of unfinished interactive proof fragments; multiple workspaces; `_RocqProject`/`_CoqProject` configuration; versioned positional goal requests; Petanque low-latency interaction; full Rocq state on document nodes; document version/contents/environment/root-state identity; stopped/workspace-updated/failed completion states.

### E6 — Anneal normative context

**Identity:** `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`.

**Files:**

- `anneal/PRINCIPLES.md`, blob `d5339a95254eae14ac201139d07d9d36d48a19fb`;
- `anneal/DESIGN.md`, blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`.

**Permalinks:**

- https://github.com/google/zerocopy/blob/cc135f46155b72e4b51188525c2974a3b84acf92/anneal/PRINCIPLES.md
- https://github.com/google/zerocopy/blob/cc135f46155b72e4b51188525c2974a3b84acf92/anneal/DESIGN.md

**Role:** Anneal requires precise result identity/scope, fail-closed success, explicit/shrinkable trust, and faithful abstraction boundaries while deliberately leaving the exact component boundary undecided. These constraints, rather than any Rocq-specific mechanism, govern the applicability judgment.

## Revalidation

Re-run this report when any meaning-bearing identity changes or when Anneal is about to rely on a stronger property than this report establishes.

1. **Rocq LSP / Flèche:** compare the then-current `rocq-community/rocq-lsp` revision with `2e0c43c...`. Recheck `README.md`, `USER_MANUAL.md`, `PROTOCOL.md`, and `fleche/doc.ml` for document identity, project/workspace handling, recovery, interruption, cache/invalidation, and positional request semantics.
2. **SerAPI:** the repository is archived, but if a maintained successor or fork becomes relevant, do not transfer `Add`/`Exec`/`Cancel` semantics by name. Re-read its actual protocol and state model.
3. **Historical evidence:** retain arXiv/DOI identities for the 2013 PIDE-to-Coq and 2015 STM papers. If stronger historical claims are needed, inspect the full papers rather than relying on abstracts or later retrospectives.
4. **Anneal:** compare current `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` with `cc135f...`. If verification identity, success semantics, trust accounting, or component-boundary policy changes, re-derive the applicability section rather than preserving this recommendation mechanically.
5. **Native overlap:** before adoption/publication, search the then-current `reference` catalog and report bodies for J019-equivalent Coq/Rocq/STM/SerAPI/Flèche analysis and reconcile semantically with all candidate-only salvage.
6. **Execution evidence:** if Anneal decisions depend on latency or resource thresholds rather than architecture, add a separate reproducible benchmark. This report's historical performance numbers are not sufficient to set such thresholds.
7. **Authoritative acceptance:** if Anneal adopts a persistent or recovery-capable semantic service, test the exact acceptance path with stale responses, changed project configuration, interrupted work, partial/recovered documents, and service restarts. The required invariant is that no advisory or mismatched result can be published as ordinary verification success.