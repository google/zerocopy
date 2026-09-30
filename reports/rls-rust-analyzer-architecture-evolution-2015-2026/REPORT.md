# RLS to rust-analyzer: why compiler reuse was not enough

## Summary

Rust's IDE history is evidence against a simple rule that the batch compiler should also be the interactive engine. The original Rust Language Server (RLS) was explicitly designed around compiler reuse. Its accepted 2015 design put `rustc` inside a long-running service, intended lazy and incremental compilation, and stored compiler-produced semantic facts in a project-wide database. The mature implementation still obtained high-fidelity facts from `rustc`, but its unit of semantic refresh was largely a crate compilation: dirty files caused dirty crates to be rebuilt, `rustc_save_analysis` exported a broad fact set, and the RLS replaced the affected crate's indexed analysis. It added a virtual file system, request scheduling, build squashing, Cargo orchestration, and Racer fallbacks, but those layers did not change the basic cost model.

rust-analyzer succeeded by changing that cost model rather than by merely wrapping `rustc` differently. It made the long-lived analysis database the primary semantic engine, accepted explicit source/project inputs, parsed incomplete code without failing, and computed semantic facts lazily and incrementally. Its architecture deliberately separated editor-facing APIs from LSP and from filesystem/build-system ownership. That bought responsiveness and a better interface for IDE features, but initially duplicated compiler semantics and sometimes returned approximate or incomplete answers where RLS inherited `rustc` precision. RFC 2912 accepted that trade temporarily because waiting for `rustc` to be refactored into an IDE-ready engine would constrain development order and delay a working IDE.

The long-term response was not to choose permanent duplication or to force one process to do both jobs. The Rust project pursued *library-ification*: factor semantic mechanisms into reusable libraries and let rustc and rust-analyzer remain different front-ends around the parts that genuinely need different state models. At the 2026 subject revisions, rust-analyzer reuses multiple `rustc_*` crates, including the next-generation trait solver through an abstraction layer, while still retaining its own salsa-backed interner and error-tolerant, frequently changing source-to-HIR machinery. This is a concrete example of **shared acceptance semantics without identical interactive implementation**.

For Anneal, the strongest transferable judgment is conditional: an interactive proof/analysis service should be free to use a persistent, editor-oriented engine or state model when that materially improves latency and incomplete-input behavior, while authoritative verification success remains tied to an exact accepted subject and checking boundary. Share semantic libraries and representations where they are stable enough to be common; do not make process identity or one global cache the correctness argument. Any live engine that can diverge from the acceptance path needs explicit snapshot identity, cancellation/freshness rules, and differential tests. This is a derived Anneal judgment, not an adopted design decision.

## Applicability

This report answers issue #3732 J009. It reconstructs the path from RFC 1317 (2015/2016), through the mature RLS architecture and the 2019 RLS/rust-analyzer comparison, to RFC 2912 (2020), RLS deprecation (2022), and the current 2026 rust-analyzer/rustc sharing structure. The exact Git revisions directly inspected are listed in `REPORT.json`; dated Rust and rust-analyzer project posts are identified in `source-map.json`.

The RLS repository subject is its archived head, `04afefab3f993d6c59ecaaf9f3fcf7a5b8f6d2bc`. Its `architecture.md` describes the mature design in the context of the 2019 Rust All-Hands and links some implementation examples to older file revisions. Claims here about the RLS's architectural mechanism come from that document and RFC 1317, not from executing the archived server.

The rust-analyzer source subject is `03fcb77246f2568adb0e9b2fa60d19c6cc1686f4` (2026-09-27). Its architecture document describes current invariants, while its checked-in historical guide explicitly says its narrative describes the 2024-01-01 release. This report uses the current architecture document for current structural claims and uses historical posts/RFCs for historical rationale. The rustc sharing account is the rustc developer guide at `0fb89036f8e46a80ee815ed99ff7d9dae9d172ae` (2026-09-27).

The report does **not** claim that rust-analyzer and rustc accept exactly the same set of programs, emit identical diagnostics, or implement the same semantics at the inspected revisions. The evidence establishes selective code sharing and explicit architectural accommodation of distinct front-end state models. Nor does the report claim that Anneal should copy rust-analyzer's particular parser, salsa database, LSP boundary, or process topology. The Anneal implications are derived from the relationship among responsiveness, semantic authority, and divergence.

An adjacent corpus package, `anneal-3730-upstream-api-projection-precedents-2026-09-29`, already records the current rust-analyzer `AnalysisHost`/`Analysis` input-and-snapshot API as a precedent for explicit input ownership and cancellation. This report does not replace that result. It adds the historical judgment J009 asks for: why a compiler-backed language server was not enough, why a separate engine was accepted despite divergence, which alternatives were considered, and how later sharing narrowed the duplication without erasing the architectural split.

## Findings

### 1. RLS began with the same aspiration that a naive "just use the compiler" proposal has

RFC 1317 did not propose a one-shot wrapper around `rustc`. It described a long-running service that would include the compiler as a library, maintain a database and work queue, serve concurrent asynchronous requests, compile in-memory edits, and eventually make compilation lazy and incremental. It explicitly identified whole-project compilation as too slow for IDE feedback and incomplete source as normal editor input. It also anticipated keeping the compiler in memory, while noting that doing so required a way to invalidate compiler state safely and cancel obsolete work.

**Basis: normative project decision.** RFC 1317 at `rust-lang/rfcs@4e4c756e6df95167dda553251cc37a75a294f002`, especially `Motivation`, `Detailed design / Architecture`, `Compilation / Lazy compilation`, and `Keeping the compiler in memory`.

This matters because the later move away from RLS cannot be reduced to "the first design forgot incrementality" or "the first design spawned rustc for every keystroke." The desired properties were known early. The hard part was fitting them to the compiler's actual architecture and to Rust's project/language semantics.

RFC 1317's database was also a deliberate semantic boundary. Compiler runs would update project-wide analysis facts; queries would read the database rather than retain all compiler state. That made cross-crate queries and concurrent access tractable, but it also made freshness depend on when a compilation had successfully produced replacement facts. The RFC's proposed lazy compiler would have reduced the cost of producing those facts, but the mature RLS did not become the fully fine-grained persistent compiler envisioned there.

**Derived interpretation:** the RLS history separates *reuse of semantic authority* from *reuse of an execution architecture*. A batch compiler can be the best semantic oracle and still expose the wrong granularity of invalidation, cancellation, and partial-input recovery for live interaction.

### 2. The mature RLS was compiler-precise where it had compiler facts, but refresh remained build-shaped

The archived RLS architecture describes the information path as:

`rustc -> rustc_save_analysis -> rls_data -> rls_analysis -> rls`

At initialization, RLS ran a Cargo check-like build to discover the crate graph and exact compiler invocations. For primary/path crates it then ran rustc in-process and received `rls_data::Analysis` directly; for relatively stable dependencies it could dump JSON save-analysis and load it later. `rls_analysis` lowered each crate's facts into a cross-crate index and replaced a crate's prior definitions when fresh analysis arrived.

**Basis: source documentation.** `rust-lang/rls@04afefab3f993d6c59ecaaf9f3fcf7a5b8f6d2bc:architecture.md`, sections `High-level overview`, `Information flow`, `rls_analysis`, and `rls`.

For ordinary edits, RLS marked files dirty, mapped them to dirty crates, topologically ordered those crates, and re-ran rustc for them. Changes with wider build implications—initialization, configuration, `Cargo.toml`, build directory changes, `build.rs`, or files outside the known compiled set—triggered a Cargo-priority rebuild. RLS buffered/squashed builds when newer edits arrived. A VFS supplied unsaved buffers to rustc through its file-loader abstraction, so using compiler semantics did not require saving every edit first.

**Basis: source documentation.** Same RLS architecture, `Build scheduling` and `I/O / VFS`.

The accuracy story was therefore real but conditional. The archived README says RLS preferred compiler data because it was precise and complete, but used Racer when compiler-derived analysis was unavailable or too slow; Racer was the completion backend and a fallback for hover and goto-definition. The architecture also ran Cargo, build scripts, and proc macros to preserve regular build behavior. Thus "compiler-backed" already included multiple semantic modes and external effects.

**Basis: documentation.** `rust-lang/rls` archived README and `architecture.md`.

The 2019 IDE-team account makes the trade explicit. Save-analysis was valued because it came directly from compiler internal data, but it was produced for a whole crate at once. rust-analyzer's query model, by contrast, was lazy across the crate graph and more fine-grained both within files and across crates. The account characterized RLS's advantage as precision and rust-analyzer's as performance plus a more flexible analysis API.

**Basis: project-team historical account.** Rust Inside post `2019-11-18 IDE team meeting`, published 2019-12-04.

A concrete later complaint illustrates the residual unit-of-work cost: RLS issue #1714 (2021) asked for filtering which workspace packages were rebuilt because changing one package could rebuild downstream users. That issue is an experience report rather than a controlled benchmark, but it is consistent with the architecture's crate/build-shaped scheduling.

**Basis: issue report + architectural consistency; not a performance measurement in this report.** `rust-lang/rls#1714`.

### 3. rust-analyzer changed the primary semantic representation to fit editor work

The 2020 first-release account describes the contrast directly: RLS ran a compiler over the project and exported a broad fact set, while rust-analyzer kept a persistent compiler-like process and analyzed code on demand as it changed. The account says RLS could re-typecheck every function body after an edit, while rust-analyzer generally restricted work to opened files and reused name-resolution results where possible.

**Basis: project-author historical account.** rust-analyzer `First Release`, 2020-04-20.

The current architecture makes the state model precise. The analyzer accepts source files plus a `CrateGraph` as ground input, keeps that input in memory, performs no I/O inside the semantic core, and derives a resolved semantic model. A client can apply a small input delta and obtain a fresh model. Salsa provides lazy, incremental recomputation. The build system is intentionally outside this ground-state abstraction: Cargo features are lowered by the client into cfg flags, and file paths are represented behind opaque file IDs at the database boundary.

**Basis: current source documentation.** `rust-lang/rust-analyzer@03fcb77246f2568adb0e9b2fa60d19c6cc1686f4:docs/book/src/contributing/architecture.md`, `Bird's Eye View` and `crates/base-db`.

That boundary is not just an implementation convenience. It means an IDE host owns discovery and external state, while the semantic engine owns deterministic derivation from explicit inputs. This differs from RLS's choice to make the server itself a build orchestrator that runs Cargo, build scripts, proc macros, rustc, formatting, linting, and Racer.

**Derived interpretation:** rust-analyzer's responsiveness comes partly from a narrower semantic-core contract. Moving I/O/build ownership outward does not remove consistency obligations; it makes them explicit inputs rather than hidden ambient behavior of semantic queries.

### 4. Incomplete source forced a different front-end contract, not just a faster cache

rust-analyzer's parser is intentionally error-tolerant: parsing returns a tree plus errors rather than failing. Its syntax trees are per-file, fully determined by syntax contents, and deliberately carry no semantic context. AST accessors may return `None` even for shapes that well-formed grammar would require. These invariants support refactoring and analysis while the user is partway through an edit.

**Basis: current source documentation.** Current rust-analyzer architecture, `crates/parser` and `crates/syntax` architecture invariants.

The current rustc developer guide states the deeper reason this cannot simply be hidden behind one shared concrete compiler representation. rust-analyzer must handle frequently changing, partially invalid or incomplete source, so the layers between source and HIR—including types and their interner—need infrastructure different from rustc. The shared `rustc_type_ir` therefore defines abstractions over those differences; rustc uses `TyCtxt`, while rust-analyzer supplies a salsa-backed `DbInterner`.

**Basis: current documentation.** `rust-lang/rustc-dev-guide@0fb89036f8e46a80ee815ed99ff7d9dae9d172ae:src/solve/sharing-crates-with-rust-analyzer.md`, `The Abstraction Layer` and `trait Interner`.

This is a stronger result than "two implementations happen to exist." The sharing layer explicitly models that the two front-ends require different concrete contexts while allowing common semantic algorithms above the abstraction. In other words, the divergence is architecturally represented, not merely tolerated as debt.

### 5. Fine-grained queries solve an invalidation problem, but they create their own costs and assumptions

The 2020 `Three Architectures for a Responsive IDE` account explains why Rust is unusually hostile to simpler IDE strategies. Macro expansion can create top-level items from other crates; a source file can participate in multiple semantic module instances; cfg and crate-graph context affect meaning; and a whole crate is often too large as the minimum lazy unit. The article argues that for Rust, laziness alone is insufficient, so rust-analyzer combines it with fine-grained incremental dependency tracking via salsa.

**Basis: project-author architecture analysis.** rust-analyzer, `Three Architectures for a Responsive IDE`, 2020-07-20.

The cost is not free. That same analysis identifies extra complexity and CPU/memory overhead from fine-grained dependency tracking. rust-analyzer's 2020 first-release account also recorded significant startup and memory costs because caches were then in-memory only. The exact 2020 cost figures do not describe the 2026 implementation, but they document the trade accepted to get the desired interaction model.

The query model also depends on assumptions that batch compilation can often treat more casually. The 2021 `IDEs and Macros` account notes that rust-analyzer runs procedural macros out of process for availability and that nondeterministic macros can violate assumptions used to discard and later reconstruct derived state. A batch compiler can often assume a macro run completes deterministically enough for one compilation; a persistent IDE must survive repeated execution, cancellation, and partial failure.

**Basis: project-author architecture analysis.** rust-analyzer, `IDEs and Macros`, 2021-11-21.

Current rust-analyzer continues to refine rather than abandon the incremental model. A March 2025 release moved more state, including the crate graph, onto a newer salsa implementation so dependency changes invalidate affected crates rather than the entire workspace. This is evolutionary evidence, not proof that every current operation is optimally incremental.

**Basis: project release note.** rust-analyzer changelog #277, 2025-03-17.

### 6. The separate engine knowingly introduced semantic divergence

The most important historical correction is that the Rust project did not pretend the new engine was immediately as authoritative as rustc. The 2020 first-release account says rust-analyzer was not then using rustc directly and therefore had limited error detection; it could miss completions, return wrong definitions, or show false-positive errors. RFC 2912 likewise lists approximate find-usages/goto-definition/rename behavior, inability at that time to report some diagnostics without saving, and lack of persisted caches as known gaps relative to RLS.

**Basis: project-author account + accepted RFC.** rust-analyzer `First Release` and RFC 2912 at `rust-lang/rfcs@ba27c4c027704c716fcc1f54be601939fdc29c57`.

RFC 2912 accepted rust-analyzer as the future official LSP despite these differences. It did **not** claim that editor answers were interchangeable with compiler acceptance. Its rationale was comparative: rust-analyzer's architecture produced a substantially better interactive trajectory, and insisting on short-term feature parity would encourage throwaway mechanisms that delayed the intended architecture.

The RFC identifies duplicate compiler logic as its primary drawback and explicitly warns about lag between new rustc syntax/semantics and IDE support. This is the central cost of the separate-engine decision.

**Basis: accepted RFC.** RFC 2912, `Drawbacks` and `Require feature parity between the existing RLS and rust-analyzer`.

The later official RLS deprecation announcement (2022-07-01) attributes the transition to architectural limits that made low-latency, high-quality interactive responses difficult and says rust-analyzer uses a fundamentally different approach rather than directly relying on rustc. This is the project's retrospective account of the decision, not an independent benchmark.

**Basis: Rust Dev Tools Team announcement.** `RLS Deprecation`, 2022-07-01.

### 7. "Rebuild rust-analyzer inside rustc" was considered and rejected as an ordering constraint

RFC 2912 directly considers the clean alternative: stop rust-analyzer work and port its lessons into rustc, yielding one codebase and avoiding divergence. The RFC calls this technically plausible because rustc itself was becoming more query-oriented.

It rejects that route as the primary transition strategy for practical and architectural reasons. Existing rust-analyzer users would regress while the port caught up; refactoring rustc was comparatively slow because of its size, age, and non-standard build; and, crucially, forcing all IDE improvements to wait for upstream compiler layers to become IDE-ready constrained development order. rust-analyzer could use provisional implementations to experiment with a shared component such as Chalk before all surrounding rustc layers were ready.

**Basis: accepted RFC.** RFC 2912, `Rationale and alternatives / Reimplement rust-analyzer within rustc`.

This is a useful design principle beyond Rust: one-engine architectures can create *sequencing coupling*. Even if the desired final semantics are shared, requiring every interactive experiment to land through the authoritative batch engine can delay learning at higher layers. A separate engine can serve as a laboratory, provided the system makes the resulting semantic authority limits explicit.

**Derived interpretation.** The historical evidence supports accepting temporary or scoped semantic duplication when it buys a substantially better experimentation/latency frontier and when there is a credible path to share mature semantic components. It does not support unconstrained permanent forks.

### 8. The 2019 hybrid proposal shows that the design space was not binary

The 2019 IDE-team meeting proposed a hybrid in which rust-analyzer would remain the interactive engine but could consume save-analysis for operations such as find-usages and rename where compiler precision mattered. The same account paired this with longer-term rustc library-ification.

**Basis: project-team historical account.** Rust Inside, 2019-12-04.

The eventual project history did not preserve RLS/save-analysis as the official editor architecture: RFC 2912 selected rust-analyzer, the Rust organization adopted it in 2022, and RLS was deprecated later that year. This report did not reconstruct every intermediate experiment needed to prove why the specific 2019 save-analysis fallback did or did not ship in each form. The important architectural lesson is narrower: hybrid authority was considered; the project was willing to combine a responsive approximate engine with more authoritative compiler-derived results rather than demand a single mechanism for every IDE operation.

**Boundary on inference:** absence of save-analysis from the inspected 2026 rust-analyzer architecture is not by itself evidence that every hybrid experiment failed for one reason. The report therefore does not assign a single causal explanation to that proposal's fate.

### 9. The long-term convergence mechanism became shared libraries, not one shared front-end state machine

RFC 2912 proposed aggressive compiler library-ification so rustc and rust-analyzer could share production semantic components while retaining separate front-ends. At that time the RFC cited a shared lexer and work toward shared trait solving as early examples.

By the 2026 rustc developer-guide subject, that direction is concrete. rust-analyzer consumes several rustc-derived crates, including `rustc_abi`, `rustc_ast_ir`, `rustc_lexer`, `rustc_next_trait_solver`, `rustc_pattern_analysis`, and `rustc_type_ir`. Trait solving is shared over generic interfaces. rustc and rust-analyzer provide different concrete contexts and interners because their surrounding requirements differ. The guide also lists remaining duplicated logic, such as parts of obligation handling and coercion, that maintainers would still like to unify.

**Basis: current documentation.** `rust-lang/rustc-dev-guide@0fb89036f8e46a80ee815ed99ff7d9dae9d172ae`, `Shared Crates`, `The Abstraction Layer`, and `Long-term plans for supporting rust-analyzer`.

This outcome is the strongest evidence in J009. The project found a stable middle point between two extremes:

| Extreme | Benefit | Failure mode exposed by the history |
| --- | --- | --- |
| One compiler process/state model for batch and live work | Minimal semantic duplication; direct authority | Interactive granularity, cancellation, incomplete-input recovery, and development ordering become constrained by batch architecture |
| Fully independent IDE compiler | Maximum freedom to optimize the editor | Semantic drift, duplicated maintenance, delayed support for language changes, approximate answers |
| Shared semantic libraries + distinct front-end state models | Reuse authoritative algorithms where abstraction is mature while preserving editor-specific state/invalidation | Requires carefully designed abstractions, differential validation, and continuing work to decide what can actually be shared |

**Basis for table:** first two columns summarize cited source/RFC tradeoffs; the third row is a derived synthesis of RFC 2912 and the 2026 rustc sharing design.

### 10. rust-analyzer also separates semantic snapshots from protocol transport

Current rust-analyzer treats `ide` as an API boundary independent of LSP. `AnalysisHost` is mutable host state; applying a change creates a new semantic revision, while `Analysis` is an immutable snapshot used to answer requests. When state changes, ongoing salsa-based computations can be canceled as stale. The outer `rust-analyzer` crate owns LSP serialization and the server event loop rather than making protocol types the semantic API.

**Basis: current source documentation.** Current rust-analyzer architecture, `crates/ide` and `crates/rust-analyzer`.

This boundary is relevant to Anneal because an MCP or LSP protocol need not become the proof engine's semantic identity. A protocol request can point at a captured snapshot/generation; the semantic layer can provide Rust/Lean-oriented domain objects; and authoritative acceptance can still occur through a separate exact checking path. This is a derived structural analogy, not evidence that rust-analyzer's API can be reused for Anneal.

### 11. Anneal should separate "useful live answer" from "successful verification claim"

Anneal's current design contract says successful verification must identify the covered program/behavior, the promises established, and the trusted code/assumptions on which they depend; missing evidence cannot silently acquire the meaning of success. J009's history fits that constraint well.

A rust-analyzer-like live engine can legitimately optimize for incomplete source, rapid cancellation, approximate navigation, or a persistent semantic database **if** its outputs are classified as live assistance rather than silently substituted for the authoritative proof result. For proof authoring, a goal state computed against a captured editor snapshot may be useful even if it is not itself a verification witness. For final acceptance, Anneal must bind the proof to the exact generated model/import environment and checking boundary required by its promise.

**Basis: derived from the cited Rust history plus Anneal's current `DESIGN.md`; this is not adopted project policy.**

The corresponding architecture rule is not "always have two engines." It is:

1. Define the authority required by each operation.
2. Let interactive operations use the cheapest engine whose semantics are sufficient for that operation.
3. Give every live answer a snapshot/generation identity and cancel or discard it when its inputs change.
4. Re-check stronger claims at the authoritative boundary unless equivalence between the live and batch paths has itself been established.
5. Share semantic libraries beneath both paths when the abstraction is stable enough to preserve each path's required state model.

This is deliberately operation-sensitive. Completion, hover, tactic exploration, and speculative proof repair can tolerate different failure modes from "verification succeeded." Treating all of them as one global ready/not-ready state would recreate the architectural coupling that rust-analyzer escaped.

### 12. Host-owned external state is part of the correctness boundary even when the semantic core is pure

rust-analyzer's core database does no I/O, but that does not mean project configuration disappears. A host must still derive the crate graph, cfg flags, generated files, build-script outputs, and procedural-macro environment and feed them into analysis. The current architecture explicitly keeps build-system notions out of `base-db`; the client lowers them into semantic inputs.

RLS chose the other direction and orchestrated Cargo/build scripts itself. Each approach must answer the same question: *which external state determined the semantic world being queried?*

For Anneal, this is particularly important around Charon/Aeneas/Lean generation and Lake state. A narrow interactive engine can be deterministic over explicit inputs only if the adapter captures all semantically relevant external state. Moving preparation into a host is not a soundness improvement by itself; soundness comes from identifying, validating, and versioning the inputs that cross the boundary.

**Basis: derived from RLS build orchestration and rust-analyzer's explicit-input architecture.**

### 13. Semantic divergence should be managed as an engineering object, not denied

The RLS/rust-analyzer transition gives three practical mechanisms for managing divergence:

- **Explicitly document authority differences.** RFC 2912 recorded operations where rust-analyzer could be approximate instead of claiming parity.
- **Differentially share mature components.** Current rustc/rust-analyzer sharing puts common trait-solving logic behind abstractions while leaving different front-end contexts intact.
- **Preserve an authoritative fallback.** Historically rust-analyzer used `cargo check` for diagnostics that its own analysis could not yet provide; more generally, an interactive engine can defer stronger claims to an authoritative checker.

The exact mechanisms have changed over time, but the pattern is durable. For Anneal, a live Lean/annotation service should have a documented semantic envelope: which answers are exact for the captured snapshot, which are heuristic or partial, and which operations trigger or require authoritative checking. Differential tests should deliberately search for disagreement at the boundary instead of treating disagreement as impossible by construction.

**Derived Anneal judgment.** This is a recommendation to preserve the option of separate live machinery while making its authority explicit. It does not decide whether Anneal V2 should initially implement one process, two processes, an LSP adapter, an MCP adapter, or a shared library.

## Boundaries

- **No RLS or rust-analyzer execution.** This report is architecture/history research. It did not benchmark latency, memory, cancellation, or result quality, and it did not replay historical toolchains.
- **Historical descriptions have dates.** The 2019 and 2020 project posts are evidence of design rationale and then-observed behavior, not current implementation specifications. Current structural claims use the 2026 repository/documentation subjects.
- **RLS architecture is documented, not exhaustively source-audited here.** The archived `architecture.md` embeds links to older implementation revisions and is the primary description used. This report did not re-open every linked implementation line.
- **RFC intent is not implementation evidence.** RFC 1317 is especially important because it shows that lazy/persistent compilation was contemplated early; it does not prove those mechanisms were completed as written.
- **The 2019 save-analysis hybrid is not fully reconstructed.** The meeting account proposed combining rust-analyzer with compiler save-analysis for selected operations. This report establishes the proposal and later official transition, but does not claim a single proven reason for every intermediate experiment's outcome.
- **Current sharing is selective, not equivalence.** The 2026 rustc developer guide establishes shared crates and abstraction layers; it explicitly leaves duplicated logic. No claim of full rustc/rust-analyzer semantic parity is made.
- **Approximation is operation-specific.** Historical examples of wrong goto-definition or missing diagnostics establish that divergence existed. They do not imply that current rust-analyzer is approximate on those same operations or at the same rate.
- **Project posts are author/team accounts.** `Three Architectures for a Responsive IDE`, `First Release`, and `IDEs and Macros` are primary rationale from rust-analyzer developers, but they are not independent comparative studies.
- **Anneal transfer is derived.** Rust IDE behavior does not prove that the same split is optimal for Charon, Aeneas, Lean, or Anneal. The transfer depends on Anneal needing both low-latency incomplete-input interaction and a stronger exact acceptance contract.
- **No adopted design policy.** Recommendations about separate authority levels, snapshot generations, differential tests, or host boundaries are research conclusions for later design work, not decisions made by this report.

## Evidence

The primary source ledger is preserved in `source-map.json`. The highest-value evidence is:

1. `rust-lang/rfcs@4e4c756e6df95167dda553251cc37a75a294f002:text/1317-ide.md` — accepted RLS design: compiler-as-library, database/work queue, in-memory edits, lazy compilation, persistent compiler ambitions, and invalidation/cancellation difficulty.
2. `rust-lang/rls@04afefab3f993d6c59ecaaf9f3fcf7a5b8f6d2bc:architecture.md` — mature RLS information flow, save-analysis, crate-oriented rebuild scheduling, Cargo/build-script/proc-macro integration, VFS, and analysis replacement.
3. Rust Inside, `2019-11-18 IDE team meeting` (published 2019-12-04) — project-team comparison of RLS precision/save-analysis with rust-analyzer's lazy query model, plus the then-proposed hybrid and library-ification direction.
4. rust-analyzer, `First Release` (2020-04-20) — first-release comparison, persistent on-demand architecture, then-current semantic limitations, memory/startup costs, and project rationale.
5. `rust-lang/rfcs@ba27c4c027704c716fcc1f54be601939fdc29c57:text/2912-rust-analyzer.md` — accepted transition, duplicate-semantics drawback, library-ification goal, considered alternative of implementing the IDE inside rustc, and intentional acceptance of temporary feature/precision gaps.
6. rust-analyzer, `Three Architectures for a Responsive IDE` (2020-07-20) — why Rust frustrates simpler indexing/header strategies and why fine-grained incremental queries were chosen, including costs.
7. rust-analyzer, `IDEs and Macros` (2021-11-21) — persistent-IDE availability/determinism constraints around proc macros.
8. Rust Blog, `rust-analyzer joins the Rust organization!` (2022-02-21) and `RLS Deprecation` (2022-07-01) — official transition history and retrospective statement that RLS architecture limited low-latency/high-quality interaction.
9. `rust-lang/rust-analyzer@03fcb77246f2568adb0e9b2fa60d19c6cc1686f4:docs/book/src/contributing/architecture.md` — current explicit-input semantic core, error-tolerant syntax, salsa-backed incremental model, snapshot/cancellation, and LSP-independent IDE API boundary.
10. `rust-lang/rustc-dev-guide@0fb89036f8e46a80ee815ed99ff7d9dae9d172ae:src/solve/sharing-crates-with-rust-analyzer.md` — current concrete compiler-library sharing, separate interners/contexts for rustc and rust-analyzer, and remaining duplicated semantic logic.

Adjacent corpus evidence used only for scope comparison: `reports/anneal-3730-upstream-api-projection-precedents-2026-09-29/REPORT.md` at the current `reference` branch already cites rust-analyzer's pinned `AnalysisHost` API to support explicit editor-input ownership. Its finding is compatible with this history but does not answer J009 by itself.

`timeline.json` preserves the main design transitions and marks which are intent, implementation accounts, official decisions, or current structure. `judgment-matrix.json` preserves the report's derived comparison so later agents can reuse the reasoning without treating it as upstream fact.

## Revalidation

For a cheap historical revalidation, the 2015/2016 RFC 1317 and 2020 RFC 2912 acceptance commits are immutable; verify only that cited sections still correspond to the recorded revisions. The RLS repository is archived, so revalidation normally means confirming `architecture.md` and README at `04afefab3f993d6c59ecaaf9f3fcf7a5b8f6d2bc` rather than repeating implementation archaeology.

For current rust-analyzer architecture, diff `docs/book/src/contributing/architecture.md` from `03fcb77246f2568adb0e9b2fa60d19c6cc1686f4`, concentrating on `Bird's Eye View`, parser/syntax invariants, `base-db`, `ide`, cancellation, and the LSP boundary. If rust-analyzer replaces salsa, changes its explicit-input/I/O boundary, or adopts rustc's front-end state directly, revisit the judgment that separate state models remain structurally necessary.

For current compiler sharing, diff `src/solve/sharing-crates-with-rust-analyzer.md` in `rust-lang/rustc-dev-guide` from `0fb89036f8e46a80ee815ed99ff7d9dae9d172ae`, and verify the listed shared crates against rust-analyzer's dependency manifests. A major change that eliminates the separate `DbInterner`/front-end context or moves parsing/name resolution/type inference wholesale behind a common state model would materially change this report's present-day conclusion.

For Anneal applicability, re-read current `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`, then classify each proposed interactive operation by authority: editor hint, exact snapshot query, or verification acceptance. Revalidate with a discriminating experiment rather than a generic latency benchmark: mutate an incomplete proof/source buffer while holding an older live snapshot, request a live semantic result, then compare the finalized source under the authoritative batch checker. The experiment should record source/model/import identities and demonstrate that stale or approximate live results cannot be mistaken for verification success. If Anneal establishes machine-checked equivalence between a persistent live engine and the batch acceptance path for a particular operation, this report's recommended fallback recheck can be narrowed for that operation.