# RLS to rust-analyzer: why an interactive analyzer became a separate engine

## Summary

Rust's transition from the Rust Language Server (RLS) to rust-analyzer is a useful counterexample to the rule that an IDE should simply reuse the batch compiler. RLS deliberately reused `rustc` and therefore inherited highly accurate compiler semantics when compilation completed. Its problem was not a lack of semantic authority. Its problem was that the unit, lifetime, and scheduling of compiler work were poorly matched to an editor: whole-crate compilation and post-compilation analysis were too coarse for keystroke-scale latency, while incomplete programs and rapidly superseded requests are normal IDE states.

rust-analyzer chose the opposite architecture. It maintains a long-lived, demand-driven semantic database; parses broken code without treating parse failure as a terminal state; invalidates narrowly; cancels stale work; and exposes immutable analysis snapshots over transactionally updated state. This made useful interactive answers possible before the full compiler could be made equally IDE-friendly. The cost was real semantic duplication. RFC 2912 explicitly accepted that rust-analyzer could lag `rustc`, return approximate answers where RLS was precise, and temporarily maintain a second implementation of parts of the Rust language.

The transition therefore supports a conditional, not categorical, judgment. A separate live engine is justified when the interactive workload requires a materially different evaluation model, and forcing the authoritative batch engine into that role would delay or degrade the product. But the separation should not be confused with semantic independence. The Rust plan was to share libraries where their contracts fit both hosts, while allowing the batch compiler and IDE to keep different storage, invalidation, lifetime, and recovery strategies. The history also shows that retrofitting those shared boundaries is expensive: a 2021 rust-analyzer parser-sharing issue reported that, after years of effort, only the lexer was shared and described substantial interface and organizational obstacles.

For Anneal, the closest reusable lesson is to separate **authority** from **responsiveness**. If live analysis must tolerate partial edits, rapidly changing inputs, cancellable work, and stale-but-useful intermediate state, a dedicated live host can be the right architecture even when batch verification remains authoritative. Shared semantic libraries, common artifact identities, and explicit conformance checks should keep the two paths aligned. The live path should not silently inherit the authority of the batch verifier merely because both speak about the same source program.

## Applicability

This report addresses #3732 J009: the RLS-to-rust-analyzer transition, with emphasis on why sharing the compiler was insufficient for the editor workload, when a separate analysis engine was justified, and what divergence that decision introduced.

The evidence spans four periods that must not be collapsed into one design state:

- RFC 1317, proposed in 2015 and tracked in 2016, describes the intended RLS architecture before the implementation matured.
- The archived RLS repository preserves the later implementation architecture used for the 2019 IDE-planning discussion. Its archival tip is pinned here, but `architecture.md` describes the system at that earlier point.
- RFC 2912, accepted in 2020, records the explicit tradeoff made when Rust decided to move toward rust-analyzer.
- rust-analyzer's current architecture documentation at revision `03fcb77246f2568adb0e9b2fa60d19c6cc1686f4` records the mature design as observed on 2026-09-30.

The report also uses two dated primary project statements: rust-analyzer's 2020 first-release retrospective and the Rust project's 2022 RLS deprecation announcement. Those are evidence of project rationale and transition outcome, not controlled performance measurements.

The Anneal discussion is derived analysis. It does not establish an adopted Anneal architecture, nor does it claim that Anneal's proof checker, OCaml frontend, Lean environment, editor integration, or artifact store have the same constraints as Rust tooling.

## Findings

### 1. RLS already tried the apparently conservative answer: reuse the authoritative compiler

RFC 1317 did not propose a weak side analyzer. It proposed a long-running language service that would use the existing compiler internally. The motivation recognized both requirements that later drove rust-analyzer: IDE feedback has to be very fast, and the program is often invalid while the user is typing. The initial plan therefore tried to retain compiler-derived semantics while changing how compilation was scheduled and exposed.

The mature RLS architecture stayed close to that goal. Its 2019-era architecture document describes a pipeline in which RLS effectively performs `cargo check`, runs `rustc` in process for crates of interest, obtains compiler analysis data, lowers that data into a cross-crate index, and answers LSP queries from the resulting database. For unchanged dependencies it could cache save-analysis data instead of recompiling them each time.

That arrangement had a strong property: when RLS had fresh compiler data, the semantic facts came from `rustc` itself. RFC 2912 later described this as an advantage of the save-analysis design: results were generally current with the compiler and accurate for what the compilation had successfully analyzed.

The important failure mode was therefore architectural rather than epistemic. The path to an answer was still tied to compilation boundaries. RLS could optimize compilation, debounce builds, keep some compiler work in process, and cache dependencies, but semantic refresh still meant scheduling compiler work and then replacing or re-indexing crate analysis. The editor, meanwhile, generates a stream of changes in which many intermediate states will never become buildable and many requested answers become stale before a compilation finishes.

Basis: normative RFC 1317 + RLS implementation documentation + RFC 2912 retrospective.

### 2. RLS's fallback structure exposed the mismatch between authoritative data and interactive latency

The archived RLS README and architecture describe two semantic sources. Where compiler/save-analysis data were available, RLS preferred them because they were precise. Where compilation was too slow or the needed data were unavailable, especially for completion, it used Racer as a fallback. Hover and go-to-definition could also fall back to Racer when save-analysis data were unavailable.

That hybrid is revealing. It shows that "reuse the compiler" did not eliminate the need for a second, editor-oriented reasoning path. It instead placed the second path behind an authoritative-but-coarse first path. The result had two kinds of answers with different precision and freshness properties, selected partly by whether the compiler had caught up.

This is not evidence that RLS was badly designed for its time. RFC 1317 anticipated lazy compilation, a persistent compiler, cancellation, and incremental work. The problem was that those features required deep compiler refactoring. The RFC explicitly notes that keeping the compiler in memory would require invalidating already-computed data and preserving a consistent state after cancellation. Those are exactly the lifecycle problems that a traditional batch compiler can avoid by terminating a process after a run.

The RLS history therefore narrows the lesson. Sharing an implementation is valuable only when the shared implementation also exposes the evaluation boundaries that the second host needs. A compiler API that provides accurate final facts after a coarse batch is not equivalent to an incremental semantic substrate.

Basis: RFC 1317 design/alternatives + archived RLS README/architecture. The characterization of the hybrid as a lifecycle mismatch is derived.

### 3. rust-analyzer changed the unit of computation, not just the implementation language or protocol

RFC 2912 describes the architectural divide as save-analysis versus fully incremental, on-demand queries. rust-analyzer's 2020 first-release retrospective makes the operational contrast concrete: RLS compiled the project and emitted broad analysis, while rust-analyzer kept a persistent analysis process and tried to recompute only the facts demanded by changed/open code.

The current architecture makes that distinction more precise.

At the syntax layer, parsing is deliberately non-failing: the parser returns a tree plus errors rather than making malformed input a fatal result. Syntax trees are allowed to be incomplete. This is not merely nicer error recovery. It means the rest of the IDE can continue to extract structure from a file while the user is in the middle of an edit.

At the semantic layer, rust-analyzer uses an incremental query database. Its HIR crates are explicitly designed so that editing one function body does not invalidate unrelated global derived data. The ground state abstracts over Cargo and filesystem details rather than baking a specific build invocation into every semantic fact.

At the API boundary, `AnalysisHost` receives changes transactionally while `Analysis` provides an immutable snapshot. This gives requests a coherent view while allowing the underlying state to advance. When an edit makes an in-flight computation stale, rust-analyzer cancels that computation instead of insisting that every request run to completion.

At the project boundary, the current documentation says IDE functionality should remain partially available when the build is broken. Cargo/rustc invocation still exists, notably through project loading and flycheck for compiler errors, but it is not the sole source of the IDE's semantic state.

These are workload-specific semantics. They say that partiality, cancellation, snapshots, narrow invalidation, and long-lived state are first-class behavior rather than error cases around a batch compiler.

Basis: rust-analyzer current architecture documentation + RFC 2912 + 2020 project retrospective.

### 4. The separate engine was justified partly by sequencing: useful IDE architecture could arrive before rustc was refactored end to end

RFC 2912 considered the most obvious alternative: stop rust-analyzer and reimplement its ideas within `rustc`, producing an LSP server over one compiler codebase. The RFC acknowledges the appeal. `rustc` was itself moving toward demand-driven queries, and one implementation would avoid semantic duplication.

The rejection was practical and architectural. Refactoring `rustc` was expected to move slowly because of its size, age, build system, and existing constraints. More importantly, making one subsystem IDE-friendly would not deliver an IDE if the surrounding name resolution, type checking, state management, and host lifecycle were still batch-oriented. rust-analyzer could use provisional or simplified implementations to connect the entire interactive pipeline sooner, then replace pieces with shared libraries as suitable boundaries emerged.

This is a strong reason for a parallel engine when the desired architecture cuts across many layers. It permits a different order of work. A separate host can establish the end-to-end interaction model first and improve semantic fidelity incrementally. Requiring the authoritative compiler to be fully refactored before users see any benefit makes architectural sequencing a product dependency.

That freedom is also the source of divergence. The RFC explicitly calls the embedded prototype algorithms both a benefit and a maintenance cost. The justification was not that duplicate semantics were intrinsically good; it was that they made experimentation and delivery possible while the common substrate was unfinished.

Basis: RFC 2912 rationale and alternatives. The sequencing characterization is derived directly from the RFC's stated tradeoff.

### 5. Rust deliberately accepted temporary semantic divergence, including wrong or approximate IDE answers

RFC 2912 is unusually explicit about the cost of the decision. At acceptance time, rust-analyzer shared little code with `rustc`. The RFC warned that new syntax or semantics could reach `rustc` before rust-analyzer and that rust-analyzer sometimes returned approximate answers where RLS could be precise, including navigation operations. It did not require feature parity before beginning the transition because temporary compatibility code would have slowed movement toward the demand-driven architecture.

The 2020 first-release post reports another side of the same boundary: because rust-analyzer did not directly use `rustc` for its main semantic engine, compiler-quality diagnostics were incomplete, so background `cargo check` remained a separate path. The 2022 deprecation announcement nevertheless says the Rust project ultimately chose rust-analyzer because RLS's architecture made low-latency, high-quality interaction difficult.

These statements should not be read as a claim that current rust-analyzer is semantically approximate in the same ways as the 2020 implementation. The system changed substantially. The pinned 2026 architecture includes a `rustc-dependencies` wrapper for `rustc_*` crates and separate Cargo/flycheck integration. What persists is the architectural distinction: rust-analyzer owns an IDE-specific semantic model and lifecycle rather than treating completed `rustc` runs as its entire database.

The durable lesson is that a second engine needs an explicit authority model. Some answers can be speculative or approximate and still be useful, but callers must know which results are editor assistance and which results constitute authoritative acceptance. If the boundary is implicit, the system risks converting latency optimizations into unsound authority claims.

Basis: RFC 2912 drawbacks/transition plan + 2020 first-release post + 2022 Rust deprecation announcement + current architecture documentation. The authority-model conclusion is derived.

### 6. The intended end state was selective sharing, not permanent semantic duplication

RFC 2912 paired adoption of rust-analyzer with "library-ification": factor compiler functionality into libraries that both `rustc` and rust-analyzer could use. The important qualifier is that the two hosts were still expected to use shared logic differently.

The RFC gives concrete examples. A batch compiler can profit from arena-like or globally interned data that are all freed at the end of compilation; a long-lived IDE may need a different ownership strategy. A batch compiler may stream query-dependency information to disk for the next invocation; an IDE needs dependency information immediately after the next keypress. The same semantic algorithms can therefore sit behind different memory, invalidation, and host policies.

This is a more useful target than "one process" or "one codebase" as an architectural slogan. Share the parts whose contracts are truly common. Specialize the evaluation substrate where the workloads differ.

The history also warns that common boundaries are hard to extract after two large implementations have grown. In rust-analyzer issue #10765, opened in 2021, the project lead described years of work toward a shared parser with meager results and said the lexer was the principal shared part. The issue lists technical obstacles such as global state, token models, tree representation, recovery requirements, and parser interfaces, while also attributing delay partly to organizational prioritization. This is author interpretation rather than a normative Rust decision, but it is direct evidence that "we will share this later" carries substantial integration risk.

The current rust-analyzer repository has more `rustc` dependencies than the 2020 RFC snapshot, so the historical "lexer only" description must not be projected onto 2026. The broader point survives: sharing increased incrementally, and the IDE retained its own architecture rather than collapsing back into completed batch compilations.

Basis: RFC 2912 library-ification plan + rust-analyzer issue #10765 (author account) + current architecture documentation.

### 7. The useful boundary is between semantic logic and evaluation policy

The Rust case suggests three layers that are easy to conflate:

1. **Language semantics**: parsing rules, name resolution, type relations, macro semantics, trait solving, and other facts about Rust programs.
2. **Evaluation policy**: what to compute now, what to cache, what an edit invalidates, how partial input is represented, when stale work is cancelled, and how snapshots are made coherent.
3. **Product projection**: completions, navigation, diagnostics, refactors, code actions, and other editor-facing features.

RLS maximized reuse at layer 1 by driving `rustc`, but much of the available machinery still carried batch assumptions at layer 2. rust-analyzer established an IDE-native layer 2 and then reimplemented enough of layer 1 to make it useful. The long-term library-ification plan tried to reduce duplication at layer 1 without erasing the justified differences at layer 2.

This decomposition explains why "why didn't they just share the compiler?" is the wrong question. They did share the compiler in RLS. The stronger question is whether the compiler exposes semantic components independently of the batch evaluation policy. In 2016-2020, enough of Rust's compiler did not.

Basis: cross-source synthesis; derived from RFC 1317, RLS architecture, RFC 2912, and current rust-analyzer architecture.

### 8. Separate live analysis works best when broken states are ordinary values rather than exceptional failures

A batch compiler is normally invoked on a candidate program whose success or failure is the result. An editor spends much of its life between candidates: a user has typed half an expression, renamed a definition but not its callers, or edited a manifest while background project discovery is still catching up.

rust-analyzer's current invariants encode this directly. Parsing yields a tree even with errors. Syntax nodes may be structurally incomplete. The service is intended to remain partially available even when project reload or the build is broken. Internal analysis treats malformed source as data to analyze, not as a reason the semantic service itself failed.

That distinction matters for any live proof or verification environment. If the live engine treats every transient incomplete state as a failed batch verification, it will either spend excessive work rebuilding global state or become unavailable during exactly the period when interactive guidance is most valuable. A live engine instead needs explicit partial states and scoped unknowns.

This does not imply that partial results are safe to publish as verified artifacts. It implies only that the analysis API should be able to represent useful non-final information without pretending it passed the final checker.

Basis: current rust-analyzer architecture; Anneal conclusion derived.

### 9. Cancellation and snapshots are semantic interface properties, not implementation details

The current rust-analyzer design exposes immutable `Analysis` snapshots over a transactionally changed `AnalysisHost`. It also cancels computations whose inputs have changed. Those choices prevent a request from accidentally combining facts from multiple editor revisions and prevent old expensive work from blocking newer input indefinitely.

A batch system can often avoid this problem by associating one process invocation with one immutable input tree. A long-running live system cannot. Once multiple requests overlap with edits, revision identity becomes part of the correctness story.

For Anneal, this is more than a performance analogy. Any live proof state, goal display, semantic hover, or background obligation attached to source must carry enough identity to establish which source/artifact/environment revision it describes. Cancellation is then a safe response to supersession, while immutable snapshots prevent mixed-revision answers. Final publication or proof acceptance can require a stronger batch check over a fully identified artifact.

Basis: current rust-analyzer architecture; Anneal mapping derived.

### 10. A defensible Anneal split is "live advisory engine + authoritative acceptance path," not "two equal compilers"

The Rust history does not support blindly maintaining two semantic implementations forever. It supports a narrower architecture when live and batch workloads genuinely differ.

For Anneal, a plausible split would give the live path responsibility for editor-rate tasks: parsing partial source, maintaining dependency/index state, cheaply recomputing local consequences, presenting provisional goals or diagnostics, and cancelling superseded analysis. The authoritative path would own acceptance: checking a fully identified source/environment/artifact combination and producing the result that may be published or relied on by downstream automation.

Where both paths implement the same semantic rule, shared libraries or shared checkable artifacts reduce divergence. Where the live path necessarily approximates, the approximation should be explicit in its API and never promoted to the authority of the final checker. Where a complex live computation can emit a compact witness or candidate that the authoritative path can check, that arrangement has the same attractive asymmetry seen in other verifier architectures: optimize generation for responsiveness and keep acceptance narrow.

This judgment is conditional on Anneal actually having editor-rate requirements that conflict with the batch engine's lifecycle. If Anneal's authoritative engine can already provide partial, incremental, cancellable, revisioned queries at the needed latency, a second semantic engine would add divergence without buying the architectural freedom that justified rust-analyzer.

Basis: derived synthesis from the full historical record.

## Boundaries

- **No controlled performance comparison was performed.** The report relies on project architecture documents, RFC rationale, and official transition statements. It does not quantify RLS versus rust-analyzer latency or memory use.
- **Reported project success is not causal proof.** rust-analyzer's adoption and RLS's deprecation establish the project's decision and outcome, not that architecture alone caused user preference.
- **Historical rust-analyzer limitations are time-bound.** RFC 2912 and the 2020 first-release post describe an early implementation that lacked features and used approximations. Those limitations must not be attributed wholesale to the 2026 codebase.
- **The RLS architecture document is historical content preserved at a later archival tip.** The pinned repository revision is immutable, but the document itself was written for the 2019 planning context.
- **The 2021 shared-parser issue is an author account, not a normative project promise or measured organizational study.** It is evidence that sharing proved difficult and why one maintainer thought so.
- **Current rust-analyzer does use some `rustc` crates and invokes Cargo/rustc-related tooling.** "Separate engine" here means that its core IDE semantic database and lifecycle are not merely the output of completed `rustc` compilations; it does not mean zero code or process interaction with `rustc`.
- **The report does not determine the correct Anneal implementation boundary.** It does not choose whether parsing, elaboration, Lean environment construction, dependency tracking, theorem checking, or artifact storage should be shared or duplicated.
- **The report does not establish soundness of approximate live answers.** Any Anneal live approximation needs its own explicit contract and must not be treated as proof acceptance unless a sound checker establishes that fact.
- **No source-level audit of every shared `rustc` component in the 2026 rust-analyzer tree was performed.** Current documentation is enough to establish the architectural host split, not to inventory all shared semantics.

## Evidence

### E1 — RFC 1317: original RLS design

Repository: `rust-lang/rfcs`  
Revision: `82d48b36568286b93fc2ce55f89594024f421a3b`  
Path: `text/1317-ide.md`  
URL: https://github.com/rust-lang/rfcs/blob/82d48b36568286b93fc2ce55f89594024f421a3b/text/1317-ide.md

Relevant headings: Summary; Motivation; Detailed design / Architecture; Compilation / Lazy compilation; Keeping the compiler in memory; Alternatives.

Role: normative accepted design rationale for RLS. Establishes that RLS intended to reuse the compiler, already recognized invalid/incomplete editor states and low-latency requirements, and identified invalidation/cancellation as obstacles to a persistent compiler.

### E2 — RLS implementation architecture

Repository: `rust-lang/rls`  
Revision: `04afefab3f993d6c59ecaaf9f3fcf7a5b8f6d2bc`  
Path: `architecture.md`  
URL: https://github.com/rust-lang/rls/blob/04afefab3f993d6c59ecaaf9f3fcf7a5b8f6d2bc/architecture.md

Relevant headings: High-level overview; Information flow; `rustc_save_analysis`; `rls_analysis`; Build scheduling; VFS.

Role: implementation documentation. Establishes the mature compiler/save-analysis/index pipeline, build orchestration, in-process compiler use, and whole-crate replacement/indexing behavior.

### E3 — RLS archived README

Repository: `rust-lang/rls`  
Revision: `04afefab3f993d6c59ecaaf9f3fcf7a5b8f6d2bc`  
Path: `README.md`  
URL: https://github.com/rust-lang/rls/blob/04afefab3f993d6c59ecaaf9f3fcf7a5b8f6d2bc/README.md

Role: project documentation. Establishes the compiler-versus-Racer fallback model: compiler data preferred for precision, Racer used for completion and as fallback when save-analysis is unavailable.

### E4 — RFC 2912: transition to rust-analyzer

Repository: `rust-lang/rfcs`  
Revision: `b6fffdf18f8b867648de0d95657cc13a64cae4e2`  
Path: `text/2912-rust-analyzer.md`  
URL: https://github.com/rust-lang/rfcs/blob/b6fffdf18f8b867648de0d95657cc13a64cae4e2/text/2912-rust-analyzer.md

Relevant headings: Architectural divide; Challenges; library-ification; batch compilation versus IDE needs; Drawbacks; Rationale and alternatives; feature parity.

Role: normative project decision and explicit tradeoff record. Establishes why save-analysis was considered unsuitable for latency-sensitive completion, why a separate implementation was adopted, what divergence costs were accepted, and why library-ification rather than a single host process was the intended convergence path.

### E5 — rust-analyzer first release retrospective

Publication: rust-analyzer project blog, 2020-04-20  
URL: https://rust-analyzer.github.io/blog/2020/04/20/first-release.html

Role: contemporaneous author account. Establishes the project's operational explanation of the RLS/rust-analyzer difference and records early rust-analyzer limits, including reliance on separate `cargo check` for compiler diagnostics.

### E6 — Rust project RLS deprecation announcement

Publication: Rust Blog, 2022-07-01  
URL: https://blog.rust-lang.org/2022/07/01/RLS-deprecation/

Role: official transition outcome. Establishes that Rust deprecated RLS in favor of rust-analyzer and characterized RLS's architecture as limiting low-latency, high-quality interactive responses.

### E7 — current rust-analyzer architecture

Repository: `rust-lang/rust-analyzer`  
Revision: `03fcb77246f2568adb0e9b2fa60d19c6cc1686f4`  
Path: `docs/book/src/contributing/architecture.md`  
URL: https://github.com/rust-lang/rust-analyzer/blob/03fcb77246f2568adb0e9b2fa60d19c6cc1686f4/docs/book/src/contributing/architecture.md

Relevant invariants: parser returns tree plus errors; syntax trees may be incomplete; salsa-backed incremental analysis; function-body edits do not invalidate unrelated global derived data; immutable `Analysis` snapshots over transactionally updated `AnalysisHost`; partial availability when builds fail; cancellation of stale computations; Cargo/flycheck compiler diagnostics; `rustc-dependencies` wrapper.

Role: current implementation documentation. Establishes which parts of the interactive architecture survived into 2026 and prevents projecting 2020 limitations onto the current system.

### E8 — shared parser library issue

Repository: `rust-lang/rust-analyzer`  
Issue: `#10765`, opened 2021-11-14  
URL: https://github.com/rust-lang/rust-analyzer/issues/10765

Role: primary maintainer account of an attempted convergence effort. Establishes that parser sharing remained difficult years after rust-analyzer began and records technical/interface obstacles. This is not normative evidence about project-wide causality.

## Revalidation

A cheap revalidation should answer two separate questions.

First, has the historical account changed? RFC 1317, RFC 2912, the archived RLS repository, and the dated 2020/2022 project posts are immutable enough for this report's historical claims. Revalidation normally needs only to confirm that the cited revisions still resolve and that no correction to their interpretation has been published.

Second, has the current rust-analyzer boundary changed? At a newer `rust-lang/rust-analyzer` revision, inspect `docs/book/src/contributing/architecture.md` for these discriminating invariants:

1. whether parsing still represents malformed source as a tree plus errors;
2. whether core semantic analysis remains demand-driven/incremental rather than a cache of completed `rustc` compilations;
3. whether `AnalysisHost`/snapshot or an equivalent revisioned API remains the change boundary;
4. whether stale computations are cancellable;
5. whether IDE features remain available independently of a successful build;
6. how compiler diagnostics and `rustc_*` dependencies are integrated; and
7. whether a new shared compiler library has eliminated a material duplicated semantic subsystem.

If item 7 changes substantially, update the present-day portion of this report without rewriting the historical judgment. A future convergence can reduce today's divergence cost without making the original RLS-to-rust-analyzer transition irrational.

For Anneal reuse, revalidate the workload premise rather than copying the implementation. Measure or otherwise establish whether the authoritative batch path can answer partial, rapidly changing, revisioned queries with acceptable latency and cancellation. If it can, the Rust case provides little support for a duplicate live semantic engine. If it cannot, evaluate a split architecture with explicit result authority, shared semantic components where contracts align, and a final check over immutable artifact/environment identity.