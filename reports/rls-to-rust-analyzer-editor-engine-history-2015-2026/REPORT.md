# From RLS to rust-analyzer: why compiler sharing was not the decisive boundary

## Summary

Rust's IDE history is a useful counterexample to the claim that an interactive service should use the batch compiler directly merely to maximize semantic sharing. The original Rust Language Server (RLS) was explicitly designed around rustc. Its 2015 design called the service an alternate compiler that would internally use the existing compiler, and it already understood the hard requirements: very low latency, incomplete programs, cancellation, a project-wide database, lazy compilation, and eventually a compiler process that could stay alive. The architecture that shipped achieved substantial sharing with rustc, but not the fine-grained invalidation model the interactive workload required. By 2019 the RLS still rebuilt dirty crates through rustc, extracted compiler facts through save-analysis, rebuilt an index, and used Racer where compilation was too slow or unsuitable for completion.

rust-analyzer chose the opposite implementation order. It built an editor-oriented compiler front end around persistent, explicit inputs; error-tolerant syntax; on-demand queries; fine-grained invalidation; cancellable snapshots; and a long-lived semantic database. In 2020 the Rust project accepted that this gave a materially better interactive architecture even though it duplicated compiler logic and could return approximate or incomplete semantic answers that rustc would not. RFC 2912 therefore did **not** conclude that divergence was harmless. It accepted divergence as a cost, proposed extracting shared libraries to reduce it, and retained the distinction between editor analysis and compiler acceptance. The project deprecated RLS in 2022 after concluding that its architecture limited low-latency, high-quality interactive responses.

The central lesson for Anneal is conditional. **Share semantic definitions and trusted acceptance machinery where that sharing preserves the workload each path needs; do not require the same long-lived engine to serve both speculative interactive queries and authoritative acceptance merely because code sharing feels safer.** An interactive Anneal service may optimize for incomplete edits, low latency, cancellation, and reusable state. A publication or verification-success path must optimize for exact captured inputs, complete checking, deterministic reconstruction, and the meaning of Anneal's success promise. If both can use the same engine without weakening either contract, one engine is simpler. If not, the safer architecture is two operational paths connected by explicit identities and a conformance/acceptance boundary, not an assumption that a live result is authoritative because some implementation code is shared.

This conclusion is stronger than "use two engines." The RLS history also supports the strongest competing account: RLS failed to reach its original lazy/persistent design partly because rustc of the period was not structured for it. A compiler designed from the beginning for incremental interactive use can plausibly serve both workloads. Anneal should therefore decide by observable contracts and matched experiments, not by analogy alone.

## Applicability

This report answers issue #3732 J009. It reconstructs three periods separately:

1. **Design intent, 2015–2016.** RFC 1317 specified the RLS before the later save-analysis implementation settled. It proposed compiler reuse, a project database and work queue, cancellation, lazy compilation, and possibly keeping rustc alive. Claims about this period describe intended architecture, not what the final RLS implemented.
2. **Implemented RLS and the transition decision, 2019–2022.** The archived RLS architecture document records the implementation around the 2019 IDE discussion: Cargo discovers invocations, rustc runs in process for changed crates, save-analysis facts feed a cross-crate database, dependency analysis is cached, a VFS supplies unsaved buffers, builds are debounced/squashed, and Racer supplies completion/fallback behavior. RFC 2912 and project announcements record why Rust nevertheless chose rust-analyzer and what costs it knowingly accepted.
3. **The surviving rust-analyzer model, inspected at `03fcb77246f2568adb0e9b2fa60d19c6cc1686f4` on 2026-09-30.** Current architecture documentation still describes a persistent analysis host with explicit in-memory inputs, lazy derived state, error-tolerant syntax, incremental semantic queries, immutable analysis snapshots, and separate integration with Cargo/compiler checking. This establishes architectural continuity, not a claim that every 2020 limitation remains today.

The Anneal comparison uses `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`. `anneal/PRINCIPLES.md` makes verification success a high-stakes promise, and `anneal/DESIGN.md` requires partial or development information to remain distinguishable from ordinary verification success. Those documents do not decide whether interactive and batch work use one process, one executable, shared libraries, or separate implementations. The conclusions below are therefore derived design analysis, not Anneal policy.

No runtime experiment was performed. Existing `reference` reports already contain component-level evidence about rust-analyzer snapshots and Anneal/Lean interactive boundaries. This package supplies the missing historical judgment: why direct compiler reuse lost to a separate editor-oriented engine, what the replacement sacrificed, and what that does and does not imply for Anneal.

## Findings

### RLS started with the right interactive requirements but an implementation dependency on rustc

[RFC 1317](https://rust-lang.github.io/rfcs/1317-ide.html), started in October 2015 and accepted in February 2016, did not naively propose "run the normal compiler on every keystroke." It identified the core mismatch from the beginning. An IDE needs answers quickly while the program is often incomplete; a full project compilation is too slow. The RFC therefore proposed a long-running server with three conceptual components: compiler, database, and work queue. Compilation requests could cancel older ones, while queries would read a coherent project-wide database. **Basis: normative historical design.**

The RFC's latency proposals are especially important because they show that the later RLS limitations were not invisible at design time. It proposed two further steps beyond ordinary incremental compilation:

- **Lazy compilation:** compile a requested item and only the dependencies needed for the query, while a fuller compilation could continue later.
- **Keeping the compiler in memory:** avoid startup, reparsing, and reloading incremental state on every request.

The same text immediately states the cost of the second idea: rustc would need significant refactoring because computed data could not simply be invalidated, and cancellation would no longer be implemented by killing a compiler process and releasing all state. **Basis: normative historical design.** This is the key architectural fork. RLS wanted persistent fine-grained reuse, but its chosen semantic engine did not yet expose the invalidation and lifecycle properties needed to make that design cheap.

The original RFC also separated compiler semantics from some editor mechanics. It expected IDEs might use their own lexer/parser for immediate syntax feedback and asked the RLS to provide deeper name-resolution and type information. Its database was deliberately distinct from the compiler's internal data structures because project-wide queries such as find-all-references crossed crate boundaries and needed a stable queryable representation. Thus "reuse rustc" never meant "the editor is just a thin RPC shim over one untouched batch compiler invocation." The design already required a separate long-lived state model and adapter boundary.

### The shipped RLS shared rustc semantics but still rebuilt at crate granularity

The [archived RLS architecture document](https://github.com/rust-lang/rls/blob/04afefab3f993d6c59ecaaf9f3fcf7a5b8f6d2bc/architecture.md) describes the mature implementation as a pipeline:

`rustc -> rustc_save_analysis -> rls_data -> rls_analysis -> rls`

RLS used Cargo to discover the crate graph and exact compiler invocations. For primary/path crates it reran rustc in process, received `rls_data::Analysis`, lowered and cross-referenced those facts into a multi-crate index, and updated that index as changed crates completed. Less frequently changing dependency data could be dumped to JSON and cached. A VFS supplied unsaved editor buffers through rustc's `FileLoader`; build requests were buffered and squashed when typing made an imminent result obsolete. **Basis: implementation documentation at archived revision `04afefab...`.**

These mechanisms were not trivial. They avoided some process and serialization overhead, supported unsaved text, reused dependency results, and attempted to keep compiler-derived answers truthful. The RLS README explicitly described the policy: use compiler data where possible because it is precise and complete, and fall back to Racer where compilation was too slow or unsuitable, especially completion. **Basis: implementation documentation.**

But the invalidation unit remained much larger than the interactive query. On a normal change, RLS mapped dirty files to dirty crates, topologically sorted the dirty crates, and ran rustc for them. Save-analysis then represented facts extracted from compilation; the database could replace and reindex a crate, but it was not the compiler's own persistent query graph answering a cursor-local request. This matters more than the fact that rustc ran in process. The expensive semantic lifecycle was still organized around compilation and crate updates.

A November 2019 Rust IDE team meeting summarized the tradeoff without hindsight: rust-analyzer's advantage was greater performance from a fully lazy compilation model and a more flexible analysis API; RLS's advantage was precision because it used rustc. The same project account called save-analysis an unstable, high-level static representation of compiled code. **Basis: contemporary project account, 2019-12-04.** That framing is more precise than "RLS was slow because it used JSON." RLS often passed analysis in memory for changed crates. The deeper problem was that compiler-produced post-analysis facts and crate-oriented rebuilding were a poor primary abstraction for frequent local queries over transient, often invalid code.

### rust-analyzer optimized the semantic lifecycle for editing, not merely the transport

rust-analyzer began in early 2018 with syntax architecture that deliberately tolerated invalid input and used persistent-tree ideas. By late 2018 its architecture notes already described a stateful analysis layer that incorporates changes and hands out immutable snapshots, backed by on-demand query machinery. **Basis: historical source commits.** Those choices target an editor's dominant workload: tiny changes, many queries, frequent invalid states, cancellation, and reuse of unaffected derived data.

The [2020 first-release account](https://rust-analyzer.github.io/blog/2020/04/20/first-release.html) states the contrast directly. RLS ran a compiler over the project and produced a large body of derived facts; rust-analyzer maintained a persistent compiler process and analyzed code on demand as it changed. The author characterized a keystroke as causing RLS to revisit every function body, while rust-analyzer generally processed the open file and reused unaffected name-resolution results. **Basis: project-author account, 2020-04-20.** The exact performance profile depended on the project and revisions, but the architectural difference is clear: the query/invalidation graph became the primary product rather than an optimization around a batch compilation.

Current rust-analyzer architecture at `03fcb772...` preserves that model:

- Source text and project structure are explicit input state held in memory; derived semantic state is recomputed lazily after small deltas.
- Parsing intentionally does not fail on incomplete syntax. Syntax trees are file-local value-like structures rather than containers for global semantic state.
- HIR/query layers explicitly care about incrementality. The documented core invariant is that editing one function body should not invalidate global derived data about another function.
- `AnalysisHost` is the mutable state to which changes are applied; `Analysis` is an immutable snapshot used for a query. Outstanding work can be canceled when input revisions advance.
- The language server should remain partially useful when the build is broken.
- Cargo/project-model/flycheck integration is a separate outer layer, and proc macros are run in another process because they can panic, crash, or behave nondeterministically.

**Basis: current architecture documentation/source narrative.** These properties form a coherent editor-oriented contract. None depends on LSP as the semantic boundary; in fact the `ide` API is deliberately kept independent of LSP serialization.

### The replacement knowingly bought semantic divergence in exchange for the right workload shape

A simplistic reading of the transition would be "RLS reused rustc and lost; therefore reimplementation is better." RFC 2912 rejects that conclusion. The RFC explicitly treated rust-analyzer's separate compiler implementation as its largest cost. In 2020 rust-analyzer was missing some precise diagnostics/navigation that RLS could obtain from rustc, and the first-release announcement described `cargo check` on save as a separate path for compiler diagnostics. rust-analyzer could return missing completions, wrong navigation, or false-positive diagnostics because its analysis was incomplete. **Basis: RFC 2912 and first-release project account.**

Rust therefore accepted two kinds of semantic work in parallel:

1. an editor-oriented engine optimized for persistent incremental queries and useful answers under incomplete code; and
2. rustc as the authoritative compiler, including compiler-driven checking where exact diagnostics or acceptance mattered.

The project did not intend permanent gratuitous duplication. RFC 2912 proposed "library-ification": extract production-ready compiler components so rustc and rust-analyzer could share more implementation while retaining two front ends. It cited the lexer as already shared and described possible common trait-solving/type libraries. Crucially, the RFC also explains why **shared libraries do not imply identical hosts**. Batch compilation and IDE interaction can need different allocation lifetimes and query-dependency retention. A batch compiler can free interned state at process end or stream dependency information to disk for the next build; a long-lived IDE may need to reclaim state incrementally and keep dependency information immediately available for the next keypress. **Basis: RFC 2912.**

This is the most transferable part of the history. The project sought semantic sharing at abstractions where sharing fit, while allowing different lifecycle policies at the host level. The architecture question was not "one codebase or two" in the abstract; it was "which state model and invalidation rules can satisfy each workload without giving up semantic conformance?"

### The serious alternative was to move the editor architecture back into rustc

RFC 2912 considered the strongest alternative: stop rust-analyzer development and port its lessons into rustc, yielding an LSP server based directly on rustc's increasingly query-oriented architecture. The RFC acknowledged the appeal: one codebase, less divergence, and rustc itself was moving toward demand-driven queries. It rejected the alternative pragmatically rather than theoretically. Existing rust-analyzer users would regress while parity was rebuilt, and refactoring rustc was expected to move slowly because of the compiler's age, size, and nonstandard build complexity. **Basis: RFC 2912 rationale and alternatives.**

The RFC also rejected requiring immediate feature parity with RLS before adoption. That would have forced throwaway implementations of features that rust-analyzer could not yet provide in the desired on-demand way and would slow progress toward the target architecture. Instead, the project chose a feedback period and accepted a temporarily mixed quality profile. **Basis: RFC 2912.**

This competing account survives the later outcome. The [2022 RLS deprecation announcement](https://blog.rust-lang.org/2022/07/01/RLS-deprecation/) says RLS's architecture had limitations for low-latency, high-quality interactive responses, but it does not prove that *any* rustc-based language server must fail. A compiler built from the beginning with robust persistent invalidation, incomplete-code semantics, cancellation, memory reclamation, and editor-facing APIs could plausibly serve both roles. The history discriminates against **assuming implementation sharing is sufficient**; it does not establish **separate semantic engines are inherently necessary**.

### Sharing acceptance semantics is more important than sharing every query implementation

For Anneal, the analogous distinction is between the meaning of a result and the mechanism used to obtain intermediate feedback.

Current Anneal principles say that a no-error verification result carries a precise conditional correctness promise. The design contract also says partial information, unsupported semantics, or failed tools must not silently acquire the meaning of verification success. That makes Anneal unlike an ordinary IDE in one important respect: an approximate interactive answer can be useful, but it cannot become a successful verification result merely because the interactive service produced it. **Basis: current Anneal authority plus derived application.**

The RLS/rust-analyzer history therefore supports a two-level contract:

| Concern | Interactive path may optimize for | Authoritative acceptance path must preserve |
| --- | --- | --- |
| Input state | unsaved/incomplete edits, frequent tiny deltas | exact captured Rust/model/proof/environment identity |
| Reuse | persistent caches and fine-grained dependency reuse | reproducible derivation or an attested reusable environment |
| Cancellation | aggressively discard superseded queries | never mistake canceled/stale work for accepted evidence |
| Diagnostics/goals | useful partial or approximate feedback | complete checking required by the reported promise |
| Failure tolerance | remain useful while project/build/proof is broken | fail closed for a verification-success result |
| Native extensions/tools | isolate or restart opaque helpers as needed | record the trusted/checked boundary and exact consumed inputs |
| Semantics | may use a specialized service if conformance is known/bounded | final success is decided by the designated accepted checker |

The table is **derived**, not a claim that Anneal already has two engines. It also does not require different executables. One Lean server process plus a fresh batch invocation can constitute two operational paths even when both use the same Lean elaborator; conversely, two binaries can still share most semantic libraries.

### A shared core should be judged by invalidation and lifetime contracts, not source-code percentage

The Rust transition shows three distinct kinds of sharing that are easy to conflate:

- **Semantic-source sharing:** the same parser, type representation, trait solver, or other library code is reused.
- **Acceptance sharing:** both paths are checked against the same authoritative language/verification contract, perhaps by running one path through the other before publishing a result.
- **Runtime-state sharing:** the same long-lived process, query database, or cache instance serves both workloads.

RLS maximized the first category around rustc but did not obtain the needed third-category behavior at a sufficiently fine granularity. rust-analyzer initially sacrificed much of the first category, retained the compiler as a separate precision/acceptance channel, and optimized the third category for editing. RFC 2912's library-ification plan tried to regain semantic-source sharing without giving up the editor host's lifecycle. **Derived taxonomy from the historical evidence.**

For Anneal, runtime-state sharing should therefore be a consequence of compatible lifecycle semantics, not a default. If Lean's long-lived server and batch checker can consume the same captured source/import generation, expose exact document/environment identity, cancel stale work, and produce equivalent acceptance on the required domain, sharing the engine is attractive. If a live server carries ambient state that is hard to attest or invalidate, a fresh authoritative checker may be cheaper to reason about even if it repeats computation. Conversely, duplicating elaboration logic in a separate Anneal-specific "fast checker" would introduce a Rust-analyzer-like divergence cost and would need a conformance story strong enough for Anneal's higher-stakes promise.

### The Rust case favors one source of truth for acceptance, not one implementation for every interaction

The strongest conditional judgment is:

**Anneal should not make "one engine performs batch and live work" an architectural invariant. It should make the accepted verification semantics and input identity explicit, allow an interactive service to specialize for responsiveness, and require a fresh or otherwise attested authoritative acceptance step before an interactive result can become verification success.**

That choice follows from four observations:

1. RLS demonstrates that direct reuse of an authoritative compiler can still have the wrong update granularity and state lifecycle for interactive use.
2. rust-analyzer demonstrates that an editor-oriented persistent query engine can deliver a better workload shape while tolerating some semantic incompleteness or approximation.
3. RFC 2912 demonstrates that a mature project can deliberately combine separate hosts with shared libraries rather than requiring one host to satisfy incompatible memory/invalidation policies.
4. Anneal's success promise makes semantic divergence more expensive than it is for completion or navigation, so any specialized interactive path needs an explicit acceptance fence.

This is not a recommendation to implement a second Lean or Rust semantics engine. The least-cost design is still preferable: first test whether the existing Lean/rustc/translation components can expose the required persistent snapshots, invalidation, and identity. Only introduce a semantically distinct interactive implementation if measured latency or robustness needs justify its continuing conformance cost.

## Boundaries

- **No execution evidence in this package.** No RLS, rust-analyzer, rustc, Lean, Charon, Aeneas, or Anneal process was run. Performance statements are project-authored historical claims or architectural consequences, not new benchmarks.
- **RLS was not simply a JSON pipeline.** Mature RLS used in-memory rustc callbacks for changed crates and JSON mainly for cached dependency analysis. Blaming serialization alone would misstate the evidence. The relevant limitation was the compiler/save-analysis lifecycle and crate-scale recomputation relative to editor queries.
- **RFC 1317 intent is not RLS outcome.** The RFC proposed lazy compilation and keeping rustc alive; the archived architecture documents a different practical endpoint. Their gap is part of the history, not evidence that the RFC authors overlooked interactive requirements.
- **rust-analyzer's 2020 weaknesses are historical.** This report does not claim that current rust-analyzer still has the exact missing diagnostics or navigation approximations listed in 2020. Current evidence is used only for architectural continuity: persistent explicit inputs, error-tolerant syntax, incremental semantic state, snapshots/cancellation, partial availability, and separate toolchain/flycheck boundaries.
- **Current divergence frequency is unknown here.** The current rust-analyzer architecture remains distinct from rustc and uses some rustc-derived components, but this package does not measure semantic mismatch rates. The 2020 RFC establishes divergence as a recognized cost at the transition point, not its 2026 magnitude.
- **Library-ification was a direction, not a theorem.** RFC 2912's goal of shared compiler libraries does not prove that all planned sharing arrived or that shared components make the two front ends observationally equivalent.
- **Rust IDE correctness is not Anneal verification correctness.** A wrong completion or navigation target is usually recoverable user-facing behavior. A false successful verification result would violate Anneal's core promise. The analogy therefore supports workload separation only when paired with a stronger acceptance fence in Anneal.
- **One-engine architectures remain viable.** If a single engine demonstrably offers low-latency incremental queries, incomplete-input robustness, bounded memory, cancellation, exact environment identity, and authoritative acceptance, the Rust history supplies no reason to split it merely for symmetry.
- **Process boundaries are orthogonal.** rust-analyzer's current proc-macro isolation is a useful example of containing crash-prone/nondeterministic extensions, but this report does not infer that every Anneal stage must be a subprocess. Isolation and semantic-engine count are separate decisions.
- **Selection bias:** Rust had a particular legacy compiler, ecosystem, staffing history, and editor workload. The transition may partly reflect migration economics and implementation maturity rather than a universal compiler-design law.

## Evidence

Primary evidence and immutable identities are summarized in `evidence-ledger.json`.

- [RFC 1317 — Rust Language Server](https://rust-lang.github.io/rfcs/1317-ide.html), accepted as `rust-lang/rfcs@4e4c756e6df95167dda553251cc37a75a294f002`: original goals and proposed lazy/persistent compiler design.
- [RLS architecture](https://github.com/rust-lang/rls/blob/04afefab3f993d6c59ecaaf9f3fcf7a5b8f6d2bc/architecture.md) at the archived repository tip, blob `a7bde5799d73cbaf7319dad2773fd58a89a978a8`: implemented rustc/save-analysis/build-scheduling/VFS mechanism. The repository's final README records deprecation and Racer fallback.
- [2019-11-18 IDE team meeting](https://blog.rust-lang.org/inside-rust/2019/12/04/ide-future/), published 2019-12-04: contemporary comparison of rust-analyzer's lazy performance/flexible API with RLS's rustc-derived precision.
- [rust-analyzer first release](https://rust-analyzer.github.io/blog/2020/04/20/first-release.html), 2020-04-20: author account of persistent on-demand analysis, RLS recomputation, rust-analyzer limitations, and compiler checking as a separate channel.
- [RFC 2912](https://rust-lang.github.io/rfcs/2912-rust-analyzer.html), recorded in `rust-lang/rfcs@ba27c4c027704c716fcc1f54be601939fdc29c57`, blob `9f5986eeacafbea1ad99c6cbc4c24d2eab278c99`: official transition rationale, costs, library-ification goal, distinct batch/IDE lifecycle needs, and alternatives.
- [RLS deprecation](https://blog.rust-lang.org/2022/07/01/RLS-deprecation/), 2022-07-01: project outcome and stated architectural limitation.
- [Current rust-analyzer architecture](https://github.com/rust-lang/rust-analyzer/blob/03fcb77246f2568adb0e9b2fa60d19c6cc1686f4/docs/book/src/contributing/architecture.md), blob `8b6ea56c851650cac23c27cc1ffb0a7f1b2a854c`: surviving persistent-input/query/snapshot architecture and current outer tool/process boundaries.
- [Early rust-analyzer architecture commit](https://github.com/rust-lang/rust-analyzer/commit/5e21ae9418380b8c183c4663ca03bd63dd240aa9), 2018-01-10, plus the 2018 architecture update `6d14bb0cd0af55fe45711ac048236f9dd9d24a3f`: early error-tolerant syntax and stateful/on-demand analysis direction.
- Anneal applicability authority: `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, `anneal/PRINCIPLES.md` blob `d5339a...` and `anneal/DESIGN.md` blob `0e8170...`.
- Adjacent `reference` evidence: `anneal-3730-upstream-api-projection-precedents-2026-09-29` already inspects `AnalysisHost` snapshots at the same current rust-analyzer revision and derives a separate editor-observation versus acceptance rule. This report does not rerun that work; it supplies the RLS-to-rust-analyzer historical rationale J009 asks for.

Evidence roles are kept distinct above. RFCs show design intent and accepted project rationale; repository architecture documents show implementation structure; release/deprecation posts report project judgments and outcomes; Anneal conclusions are derived analysis.

## Revalidation

Revisit this conclusion when either the Rust precedent or Anneal's relevant workload changes materially.

For the Rust precedent, inspect the then-current rust-analyzer architecture and any rustc/rust-analyzer shared-component changes. The conclusion would weaken if the two front ends converge to one persistent query engine with the same observable semantics while retaining editor responsiveness. It would strengthen if current mismatch measurements show that separate analysis continues to produce material semantic drift despite shared components.

For Anneal, the discriminating experiment is not a generic throughput benchmark. Use one pinned Rust/model/proof fixture and compare the candidate live path with the authoritative batch path across: incomplete edits, rapid superseding edits, import/environment changes, cancellation, process restart, stale replies, and successful final proof. Record exact source, generated artifact, imported environment, worker/session, and result identities. Measure both latency and semantic outcomes. A one-engine design wins if it can provide the live latency/cancellation properties **and** exact final acceptance under those identities without fragile hidden state. A split operational design wins if the live path needs different state/lifetime semantics but can be fenced cheaply by an authoritative final check. A semantically distinct second implementation should be considered only if those experiments show that adapting the authoritative engine cannot meet the interactive requirement at reasonable cost.

If a future Anneal architecture adopts a live result directly as verification success without a fresh or attested authoritative acceptance step, revalidate this report against that exact mechanism. The Rust precedent does not justify such promotion: its strongest lesson is that editor usefulness and compiler authority are different contracts even when the project wants to share as much compiler logic as possible.