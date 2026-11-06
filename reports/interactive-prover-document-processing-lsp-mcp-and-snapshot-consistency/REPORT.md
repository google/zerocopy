# Interactive Prover Document Processing, LSP/MCP Protocols, and Snapshot Consistency

## Summary

This report synthesizes nine primary-source studies and current-source delta reviews covering interactive theorem-prover document models, client/server synchronization protocols, concurrency-control and transaction semantics, and persistent-snapshot memory/storage costs:

1. **Isabelle/PIDE's Shift from Synchronous Command Loops to Asynchronous Versioned Document Processing (2008–2019)**: Isabelle/PIDE (`arXiv:1207.3441v1`, `10.1016/j.entcs.2012.06.009`, `arXiv:1307.1944v1`, `arXiv:1304.6626v1`, `arXiv:1905.01735v1`, `10.1007/s00165-019-00492-1`) replaced the LCF/Proof General single-focus READ-EVAL-PRINT prompt with a family of explicitly versioned immutable documents evaluated as a parallel functional program. Edits create new document versions; commands and prover results attach to document structure rather than a global prompt; the editor sends a visible `perspective` hint to prioritize evaluation and cancel obsolete work; and XML semantic markup accumulates against a specific snapshot state. Crucially, the 2013 Coq/PIDE portability experiment (`arXiv:1304.6626v1`) proved that transplanting the PIDE wire protocol into OCaml yielded only lexical connectivity—full asynchronous proof checking required reforming the prover's own internal execution model toward timeless, stateless document processing. Conversely, the 2018 Isabelle/Naproche integration (`arXiv:1905.01735v1` §1.2) showed a middle ground: an external Haskell checker could participate by resending whole-text versions to a persistent, interruptible, cache-bearing service free of ambient filesystem state.
2. **Coq/Rocq's Three-Layer Evolution (`STM` -> `SerAPI` -> `Flèche` / `rocq-lsp`) and Current-Source Identity**: Coq/Rocq evolved across three distinct architectural layers: (a) the **State Transaction Machine (`STM`)** (`arXiv:1506.05605`, 2015), which represented a document as a DAG of prover states and atomic command edges, separating opaque proof tasks from global-effect commands to achieve ~10x interactivity and ~4x 12-core speedup on the Odd Order development; (b) **`SerAPI`** (`rocq-archive/coq-serapi@6196f9f572ef9dd3749b885cabce7a57406cedb9`, HAL `hal-01384408`), which added machine-friendly S-expression/JSON serialization over the STM (`Add`, `Exec`, `Cancel`, `Query`) while inheriting STM's stateful limits (parent-state-dependent parsing for `Notation` and a hard STM limitation where `Cancel` on an unexecuted suffix can force execution up to the preceding sentence); and (c) **`Flèche` / `rocq-lsp`** (`rocq-community/rocq-lsp@2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe`), a dedicated incremental document engine whose `Doc.t` (`fleche/doc.ml`) binds `uri`, `version`, `contents`, node list (each storing source range, optional AST, full Rocq state, diagnostics, and cache metrics), completion status (`Stopped`, `WorkspaceUpdated`, `Failed`), `_RocqProject`/`_CoqProject` workspace environment, versioned positional `proof/goals` queries, Petanque low-latency RPC, and proof-structured error recovery (including automatic admission of unfinished proof fragments for editor continuity). Current-source verification confirms that both `rocq-archive/coq-serapi` and `rocq-community/rocq-lsp` default branches remain at those exact pinned commits (`zero_forward_commits`).
3. **LSP 3.18 Synchronization Boundaries and Lean 4 (`v4.30.0-rc2`) Watchdog/Worker Snapshot Architecture**: The Language Server Protocol (`microsoft/language-server-protocol@de9a671ae6ba374cc748a29c1c620cbc536302ff`, specification `3.18`) is a text-synchronization protocol, not a proof-session protocol: `textDocument/didOpen` transfers URI content ownership to the client's in-memory buffer (forbidding server filesystem re-reads until `didClose`), `didChange` advances post-change `VersionedTextDocumentIdentifier` numbers, request `id`s correlate single JSON-RPC turns without carrying expected document versions on standard queries, and `$/cancelRequest` is advisory best-effort. Lean `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) realizes this with one `Watchdog.lean` process managing one `FileWorker.lean` subprocess per open file, retaining open-document text in the watchdog for crash reconstruction, reusing command-level parser/elaborator snapshot trees (`Lean.lean`), cancelling pending requests on edit via a dedicated edit-cancellation token (`RequestCancellation.lean`), and isolating open files from unsaved edits in imported modules until those imports are saved and rebuilt.
4. **Stateless Per-Request Semantics in Model Context Protocol (`MCP 2026-07-28`)**: MCP `2026-07-28` (`modelcontextprotocol/modelcontextprotocol@5f5440bb26a62e2cf3440b92da5a667efa03b267`) abolished protocol-level sessions, `initialize` handshakes, server-initiated requests, and SSE stream resumption from the legacy `2025-11-25` era. Every request is self-contained (`server/discover` is optional), stdio multiplexes interleaved requests without process-session affinity, Streamable HTTP sends independent `POST` requests without `Mcp-Session-Id`, multi-round-trip inputs return `InputRequiredResult` with integrity-protected `requestState` echoed under a new request ID, and stateful proof tools must pass explicit server-minted handles (`workspace_id`, `snapshot_id`) as ordinary tool arguments.
5. **MVCC, Snapshot Isolation, Write Skew, and Optimistic Semantic Transactions (1981–2026)**: Combining Kung & Robinson's Optimistic Concurrency Control (`10.1145/319566.319567`, 1981), Herlihy & Wing's Linearizability (`10.1145/78969.78972`, 1990), Berenson et al.'s Snapshot Isolation critique (`10.1145/223784.223785`, MSR-TR-95-51, 1995), Ports & Grittner's PostgreSQL Serializable Snapshot Isolation (`PVLDB` 5(12), 2012), Horwitz-Prins-Reps semantics-based program integration (`10.1145/65979.65980`, 1989), HTTP `If-Match` (`RFC 9110`), Git `update-ref` (`git/git@a018953688f1b10bddf91bff8747068f5f4746a4`), and LSP `TextDocumentEdit` (`microsoft/language-server-protocol@9a247101dc088557ae56adef8fecbdc86c9a93ca`) establishes that: (a) read-only goal queries need a **coherent named project generation**, not global locking; (b) per-file version numbers do not prevent mixed-generation reads across multi-file Charon/Aeneas/Lean outputs; (c) snapshot isolation's first-committer-wins rule does not prevent **write skew** across disjoint files when a cross-resource proof invariant spans them; and (d) query-derived edits are **optimistic semantic transactions** whose apply boundary must atomically validate the full semantic dependency basis and write authority—treating textual rebasing as candidate construction that requires fresh verification rather than inherited proof authority.
6. **Persistent Data Structures, Copy-on-Write Snapshots, Arenas, and Hash-Consing Space Costs (1989–2026)**: Grounded in Driscoll, Sarnak, Sleator, and Tarjan (`10.1016/0022-0000(89)90034-2`, 1989), Lean 4's 32-way `PersistentArray` (`516fb0ce50651c1ef39cccdca48663335dac7790`), 32-way `PersistentHashMap` (`f963f3a3f3cfc8c262e14bfcf56d21fc3a55442d`), and `ShareCommon` maximal sharing (`4692b83a1939718e215918261cb5666e2ef9c88a`, `d64141f8e6e026170f0fa4089e0cd2e43f9d47bb`), Lean reference-counted destructive array updates, OpenZFS copy-on-write snapshot/hold accounting, Rust `typed_arena` (`2.0.2`), and OCaml `fix` (`20250919`) weak hash-consing, persistent snapshots are cheap in proportion to **divergence × retention lifetime × reclamation granularity**, not in proportion to snapshot count. Retaining old roots disables Lean's in-place destructive array mutation on shared paths and can pin arbitrarily large unreachable subtrees, arenas, interning tables, or CoW disk blocks unless bounded by explicit reader leases and per-layer reclamation policies.

---

## Applicability

These findings govern interactive verification orchestration, LSP/MCP server design, concurrent agent editing, and snapshot lifecycle management in Anneal (`google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, `anneal/PRINCIPLES.md` blob `d5339a95254eae14ac201139d07d9d36d48a19fb` and `anneal/DESIGN.md` blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`):

1. **Own the External Context Envelope; Borrow Semantic Incrementality Only Where Upstream Contracts Exist**:
   - Anneal must own exact source/model/environment generation identity, build/toolchain/plugin configuration, scheduling priority, cancellation of superseded jobs, and the fail-closed acceptance fence.
   - Do not fabricate sub-file incremental reuse above opaque whole-file stages (such as batch Charon or Aeneas invocations); rely on Lean's language server (`Watchdog`/`FileWorker` snapshot trees) or future upstream service contracts only for the specific incremental invariants those engines explicitly guarantee.
2. **Never Conflate Advisory Interactive Recovery with Verification Acceptance**:
   - Prover IDEs (`Flèche`/`rocq-lsp`, `Isabelle/PIDE`, `Lean 4` server) intentionally continue past broken tactics or automatically admit incomplete proof fragments so downstream goals remain inspectable. Anneal's acceptance gate must strictly separate provisional/advisory IDE snapshots from authoritative verification success.
3. **Carry Explicit Workspace, Generation, and Document Handles Across LSP and Stateless MCP (`2026-07-28`)**:
   - Because MCP `2026-07-28` is per-request stateless and LSP `didOpen` makes open buffers client-owned in-memory snapshots that ignore underlying disk replacements, any agent-facing proof tool must pass explicit `(workspace_generation, document_uri, document_version, obligation_id)` handles and synchronize regenerated `.lean` files through LSP `didChange`/`didOpen` rather than overwriting files behind the server's back.
4. **Enforce Operation-Specific Consistency Contracts and Semantic Preconditions on Edits**:
   - Bind read-only goal queries to a coherent named project generation; bind query-derived edits to an atomic compare-and-swap over their semantic basis and write authority; and serialize or validate concurrent multi-file mutations to prevent write skew.
5. **Pair Structural Sharing with Bounded History, Reader Leases, and Per-Layer Storage Selection**:
   - Use persistent in-memory maps (`PersistentHashMap`/`PersistentArray`) for localized metadata and scratch forks, content-addressed immutable blobs for coarse artifacts (`.llbc`, generated `.lean`, `.olean`), short-lived arenas for single-generation transient graphs, and weak or generation-scoped interning tables so old roots cannot silently pin unbounded memory or disk.

---

## Findings

### 1. Isabelle/PIDE: Replacing the Synchronous Command Loop with Asynchronous Versioned Document Processing (2008–2019)

*(Coalescing `isabelle-pide-document-processing-2008-2019` and `isabelle-pide-document-processing-evolution-2009-2019`)*

#### 1.1 From Prompt-Centered REPL (`Proof General`) to Immutable Document Versions
Across Makarius Wenzel's foundational PIDE papers (`arXiv:1207.3441v1` on Isabelle2011-1/jEdit, `10.1016/j.entcs.2012.06.009` on Isabelle/Scala asynchronous proof processing, `arXiv:1307.1944v1` on reforming READ-EVAL-PRINT, and `arXiv:1905.01735v1` on the 10-year retrospective) and the 2019 Isabelle/HOL history by Paulson, Nipkow, and Wenzel (`10.1007/s00165-019-00492-1`, §9.2):
1. **Why the Synchronous Prompt Failed**: Traditional LCF and Proof General interaction locked the editor and prover in a sequential single-point frontier: send one command, wait for evaluation, advance the prompt. Even after Isabelle introduced parallel ML evaluation in 2008, a single-prompt interface serialized human and machine interaction. In October 2014, Isabelle permanently discontinued both its TTY REPL and Proof General support in favor of PIDE document processing.
2. **Purely Functional Document Updates and Version History**: In PIDE, a document is a persistent value updated functionally by inserting or removing command fragments to produce a fresh version identifier (`10.1016/j.entcs.2012.06.009` §2). Multiple related versions coexist and share unchanged substructure; prover outputs and error messages are attributed to `(document_version, command_id)` rather than a global prompt; and Isabelle2013 (`arXiv:1307.1944v1`) added periodic history pruning so retained versions do not grow without bound.
3. **Internal Phase Evolution Behind a Stable Outer Document Model**: Between Isabelle2011-1 and Isabelle2012/2013 (`arXiv:1307.1944v1`), full outer-syntax parsing moved out of the front-end `READ` phase into the prover's parallel `EVAL` phase so theories could dynamically define new command syntax without pre-generated static keyword tables—demonstrating that an outer versioned-document contract can remain stable while internal pipeline boundaries shift.
4. **Separation of Identity, Evaluation State, Perspective, and Cancellation (`arXiv:1905.01735v1` §2)**:
   - **Version Identity**: Which source state a semantic fact describes.
   - **Evaluation State**: Which futures/command transactions have completed for that version.
   - **Editor Perspective**: Which visible text ranges should be prioritized by the parallel scheduler (scrolling changes scheduling priority without altering logical document meaning).
   - **Cancellation**: Interrupting obsolete evaluations superseded by newer edits.
5. **First-Class Unsaved Auxiliary Files and Session Exports (`arXiv:1905.01735v1` §§2.1, 2.3)**: To prevent concurrent document versions from racing on physical filesystem paths, PIDE attaches unsaved auxiliary file contents directly to command tokens (avoiding ambient filesystem reads) and routes generated outputs into session-managed export blobs rather than arbitrary disk writes.
6. **Prover-Generated Semantic Markup (`arXiv:1207.3441v1`, `arXiv:1905.01735v1` §2.4)**: Semantic coloring, tooltips, hyperlinks, and proof state are accumulated as XML trees over precise character offsets by the prover's logical context and rendered from a coherent snapshot without waiting for whole-document completion.

#### 1.2 Two Crucial Boundary Controls: Coq/PIDE (2013) vs Isabelle/Naproche (2018)
| Integration Experiment | Architecture & Mechanism | Documented Outcome & Architectural Lesson |
| :--- | :--- | :--- |
| **PIDE-to-Coq Experiment (2013)** (`arXiv:1304.6626v1` & `arXiv:1905.01735v1` §3.2) | Reimplemented the PIDE protocol layer in OCaml and connected Isabelle/jEdit to Coq using lexical analysis as the payload. | **Negative Control for Thin Protocol Wrappers**: Connectivity and lexical markup worked, but Wenzel explicitly concluded that full proof processing required reforming Coq itself toward "timeless and stateless" document execution. The prototype never reached end users and fell behind PIDE evolution. |
| **Isabelle/Naproche-SAD Integration (2018)** (`arXiv:1905.01735v1` §1.2) | Reworked an external Haskell natural-language proof checker over ~2 months from a one-shot CLI into a persistent, interruptible, cache-bearing server integrated with PIDE. | **Validated Middle Ground for External Stages**: On each edit PIDE sends the full text version; Naproche avoids ambient filesystem state, reports exact byte offsets, streams incremental diagnostics, supports interruption, and caches unchanged sub-elements internally. |

---

### 2. Coq/Rocq Document Processing: `STM`, `SerAPI`, `Flèche` / `rocq-lsp`, and Current-Source Review (2013–2026)

*(Coalescing `coq-rocq-stm-serapi-fleche-architecture-2013-2026` and `rocq-serapi-fleche-current-source-review`)*

#### 2.1 The Three-Generation Progression in Coq/Rocq
1. **Generation 1 — Coq State Transaction Machine (`STM`, `arXiv:1506.05605`, DOI `10.1007/978-3-319-22102-1_4`, 2015)**:
   - Barras, Tankink, and Tassi redesigned Coq's sequential loop into a **DAG of system states** connected by atomic command edges.
   - Static classification distinguishes pure local proof steps (`Proof ... Qed`, whose opaque bodies do not alter the global environment and can be checked out of order or in parallel worker processes) from global-effect commands.
   - On the Feit–Thompson Odd Order formalization, the STM authors reported roughly **10x faster interactive reactivity** and **4x faster batch checking on 12 cores**—gains that depended entirely on Coq's internal state classification and state-restoration machinery.
2. **Generation 2 — `SerAPI` (`rocq-archive/coq-serapi@6196f9f572ef9dd3749b885cabce7a57406cedb9`, HAL `hal-01384408`, 2016–2026)**:
   - Inspected at `README.md` (`85c5708fe72147f103c87e2316403697f4c51214`) and `serapi/serapi_protocol.mli` (`ed3ed38c409d0dc778709c7eeb73bd290f67c006`), `SerAPI` provided data-centric OCaml S-expression/JSON serialization of internal Coq ASTs and states alongside explicit document commands (`Add`, `Exec`, `Cancel`, `Query`, `Print`).
   - However, `serapi_protocol.mli` documents two fundamental STM constraints that a wire protocol cannot hide:
     - **State-Dependent Parsing**: `Add` parses a sentence relative to a parent state ID (`ontop`) because commands like `Notation` mutate the active grammar. Source bytes alone do not determine a parse tree.
     - **Non-Rollback Cancellation (`Cancel`)**: `serapi_protocol.mli` explicitly warns that cancelling a non-executed sentence suffix is poorly supported by the STM checking algorithm and **can force execution up to the previous sentence** ("a hard limitation of the STM"). Thus `STM` "transactions" are atomic single-command transitions, not ACID rollback snapshots.
3. **Generation 3 — `Flèche` and `rocq-lsp` (`rocq-community/rocq-lsp@2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe`)**:
   - Inspected at `README.md` (`37b132ed9c7e15bb4e11205e110d592a1503a6b6`), `etc/doc/USER_MANUAL.md` (`2b989fcf528d08ef3c58b115f45248d2cf4e0bcc`), `etc/doc/PROTOCOL.md` (`30d2b18cefd1d2b6fdd3493b744426c29b482c57`), and `fleche/doc.ml` (`2cb236a36a17acf610c971308e8c9962b341e74f`), `Flèche` replaces `SerAPI` with a dedicated incremental document engine:
     - **Explicit `Doc.t` Representation (`fleche/doc.ml`)**: Stores `uri`, `languageId`, integer `version`, `contents`, `nodes` (each holding source `range`, `prev` node, optional parsed `ast`, full `state : Rocq.State.t`, `diags`, and cache/timing info), `completed` status (`Yes range`, `Stopped range`, `Failed range`, `WorkspaceUpdated`), table of contents `toc`, external `env` (`init`, `workspace`, `files` from `_RocqProject`/`_CoqProject`), and `root : Rocq.State.t`.
     - **Decoupled Scheduling Modes & `proof/goals` / `Petanque`**: Supports continuous checking, on-demand checking, and viewport-guided checking over the same `Doc.t` model; `proof/goals` binds both request and response to a `VersionedTextDocumentIdentifier` and position; and `Petanque` exposes a low-latency programmatic agent interface over the same engine.
     - **Interactive Error Recovery vs Soundness Authority**: `Flèche` recognizes proof structure during broken edits and **automatically admits unfinished proof fragments** so downstream theorems remain interactive. This makes `Flèche` node states suitable for advisory IDE feedback, while requiring an explicit completion (`Completed.Yes`) and admission check before treating any proof as authoritative verification evidence.

| Architectural Layer | Representative System | Primary Unit of State | Key Limitation for External Orchestration |
| :--- | :--- | :--- | :--- |
| **Prover-Internal Execution DAG** | Coq `STM` (`arXiv:1506.05605`) | DAG of prover states & atomic command edges; delayed proof tasks | Cannot be inferred externally from raw command text without prover-side effect classification |
| **Machine-Facing Serialization Protocol** | `SerAPI` (`rocq-archive/coq-serapi@6196f9f572ef`) | Mutable sentence IDs (`sid`) in STM (`Add`, `Exec`, `Cancel`, `Query`) | Parsing depends on parent `Notation` state; `Cancel` on unexecuted sentences can force prior execution |
| **Incremental Semantic Document Engine** | `Flèche` / `rocq-lsp` (`rocq-community/rocq-lsp@2e0c43c34af6`) | Versioned `Doc.t` with per-node `Rocq.State.t`, `env` (`_RocqProject`), and `Completion.t` | Interactive recovery auto-admits unfinished proofs; requires explicit acceptance fencing |

#### 2.2 Current-Source Review of `SerAPI` and `rocq-lsp` / `Flèche` (`2026-09-30`)
As verified in `support/rocq-serapi-fleche-current-source-review/matrix.json`, `support/rocq-serapi-fleche-current-source-review/official-source-observation.json`, `support/rocq-serapi-fleche-current-source-review/serapi-refs.txt`, and `support/rocq-serapi-fleche-current-source-review/rocq-lsp-refs.txt`:
- At the September 30, 2026 observation, official `HEAD` and `refs/heads/main` of `rocq-archive/coq-serapi` still pointed to `6196f9f572ef9dd3749b885cabce7a57406cedb9` (0 forward commits; identical blobs for `README.md` `85c5708fe72147f103c87e2316403697f4c51214` and `serapi/serapi_protocol.mli` `ed3ed38c409d0dc778709c7eeb73bd290f67c006`, preserved in `support/rocq-serapi-fleche-current-source-review/snapshots/serapi/`).
- Official `HEAD` and `refs/heads/main` of `rocq-community/rocq-lsp` still pointed to `2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe` (0 forward commits; identical blobs for `README.md` `37b132ed9c7e15bb4e11205e110d592a1503a6b6`, `etc/doc/USER_MANUAL.md` `2b989fcf528d08ef3c58b115f45248d2cf4e0bcc`, `etc/doc/PROTOCOL.md` `30d2b18cefd1d2b6fdd3493b744426c29b482c57`, and `fleche/doc.ml` `2cb236a36a17acf610c971308e8c9962b341e74f`, preserved in `support/rocq-serapi-fleche-current-source-review/snapshots/rocq-lsp/`).

---

### 3. LSP 3.18 and Lean 4 (`v4.30.0-rc2`) Proof-Assistant Server Architecture

*(From `lsp-proof-assistant-architecture`)*

#### 3.1 Normative LSP 3.18 Boundaries (`microsoft/language-server-protocol@de9a671ae6ba374cc748a29c1c620cbc536302ff`)
Inspection of the LSP 3.18 specification files (`_specifications/lsp/3.18/{specification.md,general/initialize.md,textDocument/didOpen.md,textDocument/didChange.md,textDocument/didClose.md,workspace/workspaceFolders.md}`) establishes four protocol invariants:
1. **In-Memory Client Ownership of Open Documents (`didOpen.md` blob `f2bc2141ca7b4efdc1521493470cc631cf083d99`)**: Once `textDocument/didOpen` is sent for a URI, the client owns the truth of that document's text in memory, and the server **must not** re-read the filesystem URI until `textDocument/didClose` (`e8c956a6402a8a7ff031839fa58fba5d39c11f6d`) returns content mastery to disk. Consequently, if an external generator (such as Aeneas) overwrites a `.lean` file on disk while it is open in LSP, the server will continue evaluating the old in-memory text unless the client sends `didChange` or `didClose`/`didOpen`.
2. **Request ID vs Document Version (`didChange.md` blob `81e7475181818d44229c10dbcc25de7f3de83c69`)**: A JSON-RPC request `id` correlates a single request/response pair, whereas `VersionedTextDocumentIdentifier` orders post-change document snapshots. Because standard LSP queries address `(uri, position)` without carrying an expected document version token, the client must synchronize `didChange` before issuing queries and layer its own version-barrier check if it requires proof-state reproducibility.
3. **Advisory Cancellation (`specification.md` blob `2c33357fc28b47a7090655cc93b227968c459b4a`)**: `$/cancelRequest` is implementation-dependent and best-effort; it never guarantees rollback or prevents a completed response from racing with cancellation.
4. **Process-Topology Neutrality (`initialize.md` blob `177eb366b7e7769527007cbd652b6372a03aa789`, `workspaceFolders.md` blob `005d024417ed5bed246f9ee4a0fe5fdf67f7d414`)**: LSP does not define a proof session or server process layout; if a server crashes, the client must reconstruct open-document state.

#### 3.2 Concrete Realization in Lean `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`)
Inspection of `src/Lean/Server/{Watchdog.lean,FileWorker.lean,ProtocolOverview.lean,RequestCancellation.lean,README.md}` and `src/Lean/Language/Lean.lean` establishes Lean 4's server architecture:
1. **Watchdog + Per-File Worker Isolation (`Watchdog.lean` blob `68ed22f9178c9ae917c595c364d23df902d9478f`)**: One central watchdog process spawns one OS worker subprocess per open file (`didOpen`). The watchdog retains the latest full text and version of every open document; each worker receives `initialize`, a single initial `didOpen` with the current text, and subsequent `didChange` deltas. If a worker crashes (e.g., in user metaprogramming), other open files are unaffected and the watchdog reconstructs the worker on the next `didChange` from its retained snapshot.
2. **Incremental Snapshot Trees and Edit-Driven Cancellation (`FileWorker.lean` blob `c803034ed8810f13a5ef38a603a21e610efca2bc`, `RequestCancellation.lean` blob `7d310d0cd941641334a799828d4746c08e6a89d1`, `Lean.lean` blob `124d4739bc910eb30ec35844348c785bf9f6c70a`)**: Inside a file worker, Lean saves command-level and nested parser/elaborator snapshots across versions, reusing valid prefix/subtree tasks when syntax/snapshot comparisons permit (accounting for grammar extensions that can invalidate earlier than a raw byte offset). When a `didChange` arrives, the worker immediately cancels all pending requests bound to the superseded document version via a dedicated `cancelledByEdit` cancellation path distinct from explicit `$/cancelRequest`.
3. **Isolation Between Open Files and Imported Modules (`Server/README.md`)**: While an open file re-elaborates immediately on `didChange` from in-memory text, imported modules are loaded from compiled `.olean` artifacts. Editing an open dependency does **not** automatically re-elaborate open dependent files against unsaved buffer text; saving/rebuilding the dependency and refreshing/restarting the dependent workers is required to advance the import environment.

---

### 4. Model Context Protocol (`MCP 2026-07-28`) State, Lifecycle, and Concurrency Boundaries

*(From `mcp-proof-assistant-architecture`)*

Inspection of `modelcontextprotocol/modelcontextprotocol@5f5440bb26a62e2cf3440b92da5a667efa03b267` (`docs/specification/2026-07-28/{index.mdx,changelog.mdx,architecture/index.mdx,basic/index.mdx,basic/versioning.mdx,basic/patterns/mrtr.mdx,basic/patterns/subscriptions.mdx,basic/patterns/progress.mdx,basic/patterns/cancellation.mdx,basic/transports/stdio.mdx,basic/transports/streamable-http.mdx,server/discover.mdx,server/tools.mdx,server/resources.mdx}` and `schema/2026-07-28/schema.ts`) establishes the constraints of the modern stateless MCP era:

1. **Mandatory Per-Request Statelessness (`basic/index.mdx` blob `dfe11ecc1443b7dec051b1b1b9a93982b735c647`, `versioning.mdx` blob `fcfea9f0a150923ffd6637ff53fadc8240eefedf`, `changelog.mdx` blob `dc5c9a9cf3e6895504534cf3f300514394d8c6ae`)**:
   - Unlike legacy MCP (`2025-11-25` and earlier), `2026-07-28` has **no `initialize` handshake and no `Mcp-Session-Id`**. Every request carries its own protocol version and client capabilities (`server/discover` is optional).
   - A server **must not** infer conversation, workspace, or proof-session context from an existing connection or stdio subprocess. Any state that spans requests must be named by an explicit identifier supplied by the client on every call (`server/tools.mdx` blob `449020f54a6582122607b4869129bec5f1035f37`).
2. **Transport Semantics (`stdio.mdx` blob `b03ac10081d7a7a92516b5b074e4c843bc75d473` vs `streamable-http.mdx` blob `7b9813d67a9d8b90a496a6c251193a70ce79c657`)**:
   - Over **stdio**, one subprocess handles a shared bidirectional stream on which unrelated requests from multiple tasks or workspaces may be interleaved; the server must not send independent JSON-RPC requests to the client.
   - Over **Streamable HTTP**, each request is an independent HTTP `POST` returning a single JSON response or a request-scoped SSE stream; SSE stream resumption was removed in `2026-07-28`, so a broken stream loses the in-flight request and requires retrying with a brand-new JSON-RPC request `id`.
3. **Six Narrow Correlation Primitives Instead of an Ambient Session**:

| MCP `2026-07-28` Primitive | Pinned Spec Source | Exact Protocol Scope & Proof-Assistant Implication |
| :--- | :--- | :--- |
| **JSON-RPC Request `id`** | `basic/index.mdx` (`dfe11ecc1443`) | Correlates one active request/response turn; must change on retry; never identifies a workspace or proof session |
| **`progressToken`** | `patterns/progress.mdx` (`f6dc5c041b0b`) | Correlates optional progress notifications for one in-flight request; does not create a durable background task |
| **`io.modelcontextprotocol/subscriptionId`** | `patterns/subscriptions.mdx` (`866898e18ca4`) | Equals the JSON-RPC `id` of `subscriptions/listen`; lost on disconnect (client must re-subscribe and re-query authoritative state) |
| **Resource `uri`** | `server/resources.mdx` (`f49dd8e6be3f`) | Application-defined URI; MCP adds no built-in document-version, byte-offset, or elaboration-generation semantics |
| **MRTR `requestState`** | `patterns/mrtr.mdx` (`a66d667094e7`) | Returned inside `InputRequiredResult` and echoed by the client on a retry with a new request `id`; must be integrity-protected and short-lived |
| **Stateful Tool Handle** | `server/tools.mdx` (`449020f54a65`, non-normative) | Server-minted opaque handle (`workspace_id`, `snapshot_id`) passed as an ordinary tool argument; server owns lifetime, routing, and per-call authorization |

---

### 5. MVCC, Snapshot Isolation, Write Skew, and Optimistic Semantic Transactions for Proof Workspaces

*(Coalescing `mvcc-snapshot-isolation-proof-work-consistency-1981-2026` and `optimistic-edits-semantic-transactions-1981-2026`)*

#### 5.1 Separating Four Classical Concurrency Guarantees
1. **Optimistic Concurrency Control (Kung & Robinson 1981, DOI `10.1145/319566.319567`)**: Splits execution into a lock-free **read/compute phase**, an atomic **validation phase**, and a **write phase**. Speculative work is admitted only if the read set (semantic basis) observed during computation has not conflicted with intervening committed writes.
2. **Linearizability (Herlihy & Wing 1990, DOI `10.1145/78969.78972`)**: Requires each single-object operation to take effect atomically at a linearization point between invocation and response, preserving real-time order. Necessary when an API promises "the current selected generation right now," but unnecessary for queries explicitly scoped to a named historical generation $G$, and insufficient by itself for multi-object transaction serializability.
3. **Snapshot Isolation and the Write-Skew Hazard (Berenson et al. 1995, SIGMOD / MSR-TR-95-51, DOI `10.1145/223784.223785`)**: Gives each transaction a coherent start-time snapshot and enforces first-committer-wins on overlapping writes to the same item. However, two concurrent agents reading the same consistent snapshot and writing **disjoint files** (e.g., Agent 1 edits a Rust helper annotation or proof lemma in File A while Agent 2 edits a coupled invariant or configuration in File B) both pass per-file conflict checks while jointly violating a cross-file verification invariant (**write skew**).
4. **Serializable Snapshot Isolation Costs (Ports & Grittner 2012, `PVLDB` 5(12))**: Recovering full serializability over snapshots requires tracking rw-antidependency conflict structures (`rw`-conflicts), paying memory and false-positive abort costs. For Anneal, rather than importing a heavy general-purpose database transaction manager, authority-changing operations should cross a narrow serialized or compare-and-swap validation boundary over an explicit semantic generation manifest.

#### 5.2 Why Per-File Versions and Textual Rebasing Fail Without Semantic Closure
1. **Mixed-Generation Hazard in Multi-File Translation Pipelines**:
   - In the reference corpus's real-generation publication experiments on Lean `v4.30.0-rc2` (`google/zerocopy@30b9d5749aed6049d949f4f582dd64c70088d07a`, `anneal/PRINCIPLES.md`, `anneal/DESIGN.md`, and the finite identity/publication probes), in-place replacement of a seven-file Charon/Aeneas/Lean artifact family produced intermediate mixed old/new file inventories. In four mixed states, a fresh Lean process **still accepted the old proof** because the compiled function artifact had not yet been replaced even though upstream inputs had already changed.
   - Similarly, resolving a mutable `current` symlink twice across two file reads mixed generations $A$ and $B$, whereas resolving an immutable generation root once yielded a coherent snapshot.
   - Furthermore, content identity is weaker than causal generation identity: under an $A \to B \to A$ edit recurrence, file bytes return to $A$'s content while causal generation and server incarnation tags have advanced.
2. **Compare-and-Swap Protects Only What the Precondition Names (`RFC 9110` `If-Match`, Git `update-ref`, LSP 3.18 `TextDocumentEdit`)**:
   - HTTP `If-Match` (`RFC 9110` §§13.1.1, 13.2, returning `412 Precondition Failed`), Git `update-ref <ref> <new> <old>` (`git/git@a018953688f1b10bddf91bff8747068f5f4746a4`, `Documentation/git-update-ref.adoc` blob `37a5019a8bc75e29f23decb8b1b70c28c9412771`), and LSP 3.18 `TextDocumentEdit` (`microsoft/language-server-protocol@9a247101dc088557ae56adef8fecbdc86c9a93ca`, `versionedTextDocumentIdentifier.md` blob `2eef90f025383db3f0bfd1a33579333c796a5221` and `textDocumentEdit.md` blob `433259b148f8ce8a6b09684174521954e786d574`) all validate only the named target representation.
   - As shown by Horwitz, Prins, and Reps (*Integrating Noninterfering Versions of Programs*, TOPLAS 1989, DOI `10.1145/65979.65980`), conflict-free textual merging or rebasing does **not** establish semantic noninterference. In Anneal, a proof edit can apply cleanly at the same line/byte offset while the underlying Rust model, imported `.olean` artifact, obligation proposition, or write-scope authorization has changed.

#### 5.3 Operation-Specific Consistency and Optimistic Semantic Transaction Matrix
*(Synthesizing `support/mvcc-snapshot-isolation-proof-work-consistency-1981-2026/evidence-map.json` and `support/optimistic-edits-semantic-transactions-1981-2026/decision-matrix.json`)*

| Operation Class | Minimum Coherent Precondition / Basis | Required Action on Precondition Mismatch | Why Text-Only or Per-File Checks Are Insufficient |
| :--- | :--- | :--- | :--- |
| **Background Navigation, Indexing, or Cache Warming** | Coherent named project generation $G$ (staleness allowed if labeled) | Continue or drop if superseded | Advisory only; never mutates authority |
| **Goal / Tactic Query Scoped to Generation $G$** | Coherent generation $G$ + response tagged with $G$ | Return $G$-scoped answer (do not label as "current" if $G+1$ was published) | A pinned server on $G$ produces valid $G$-answers after $G+1$ exists |
| **Goal / Tactic Query Promised as "Current"** | Coherent generation $G$ + linearization/validation check against `current` pointer before returning | Re-run against $G+1$ or downgrade label to historical $G$ | Generation selection can advance while the query is in flight |
| **Pure Text Transform (Formatting) Independent of Semantic Query** | Target document URI, version/hash, and write-scope authorization | **Reject** or **Recompute** transform on latest text | Sufficient only when derivation never inspected model or goal state |
| **Query-Derived Proof or Source Edit** | Document identity + full semantic closure (Rust source, model, imports, obligation ID) + write-scope authorization (or one root generation manifest committing to all of them) | **Reject**, **Recompute** from a fresh query, or save as an explicit non-current **Fork** (if textually **Rebased**, treat as an unverified candidate requiring fresh checking) | Identical file text and byte offset can denote a different obligation or generated model after upstream rebuilds |
| **Concurrent Multi-File Refactor / Cross-Resource Mutation** | Coherent project generation manifest + atomic validation/serialization across all coupled resources and write authorities | **Reject**, **Recompute**, or **Fork** | Disjoint per-file `If-Match`/version checks allow write skew across coupled files |
| **Verification Acceptance & Environment Publication** | Complete coherent source/model/environment generation + full checker success on that exact generation + current publication CAS fence | **Reject** stale/mixed result; re-verify on current coherent generation | Prevents accepting an old proof that passed against a mixed in-place artifact inventory |

---

### 6. Persistent Data Structures, Copy-on-Write Snapshots, Arenas, and Hash-Consing Space Costs

*(From `persistent-data-structures-snapshot-space-costs-1989-2026`)*

#### 6.1 Reachability Cost Model vs Snapshot Count
Grounded in Driscoll, Sarnak, Sleator, and Tarjan (*Making Data Structures Persistent*, JCSS 38(1), 1989, DOI `10.1016/0022-0000(89)90034-2`—fat-node vs node-copying with $O(1)$ amortized space/time overhead per update step for bounded in-degree structures), creating an immutable snapshot root is cheap, but **total resident space across retained history is not the size of one version**:
$$\text{Resident Space} \approx \text{Shared Live Base} + \bigcup_{g \in \text{LiveGenerations}} \text{UniqueDeltas}(g) + \text{Roots/Metadata} + \text{Intern/Index Tables} + \text{Pinned Arenas/CoW Blocks} + \text{Materialized External Views}$$
The governing quantity is **$\text{divergence} \times \text{retention lifetime} \times \text{reclamation granularity}$**, not how many version IDs exist.

#### 6.2 Concrete Runtime Mechanisms in Lean 4, Arenas, Hash-Consing, and Copy-on-Write Filesystems
1. **Lean 4's 32-Way Persistent Collections and Reference-Counted Destructive Updates (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`)**:
   - `src/Lean/Data/PersistentArray.lean` (`516fb0ce50651c1ef39cccdca48663335dac7790`) implements a 32-way branching tree plus a tail buffer; `setAux` copies only the spine to the modified leaf, and `push` appends to the tail before flushing full tails into the tree.
   - `src/Lean/Data/PersistentHashMap.lean` (`f963f3a3f3cfc8c262e14bfcf56d21fc3a55442d`) implements a 32-way hash-array mapped trie (`insertAux` / `eraseAux` copying only the path along the hash prefix).
   - **Interaction with Lean's Reference-Counted Heap**: Lean's runtime updates arrays destructively in place when their reference count is `1` (uniquely owned) and copies them only when shared (`RC > 1`). Retaining an old snapshot root increments reference counts along shared subtrees, converting what would have been in-place destructive updates in the current generation into path allocations while pinning the old path nodes until the old root is dropped.
2. **Maximal Sharing / Hash-Consing vs Interner Retention (`Lean.Util.ShareCommon` & OCaml `fix`)**:
   - In Lean 4 (`src/Init/ShareCommon.lean` blob `4692b83a1939718e215918261cb5666e2ef9c88a`, `src/Lean/Util/ShareCommon.lean` blob `d64141f8e6e026170f0fa4089e0cd2e43f9d47bb`), maximal sharing deduplicates structurally equal subterms constructed along independent paths using either ephemeral hash tables or `PersistentHashMap`/`PersistentHashSet`.
   - However, a strong global interning table permanently retains every canonicalized object for the lifetime of the table. As demonstrated by the OCaml `fix` package (`release 20250919`, `HashCons.ml`), **weak hash-consing** (or generation-scoped interning) is required when canonicalized proof/syntax terms must be garbage-collected once no live generation references them.
3. **Arena Allocation Granularity (`typed_arena 2.0.2`)**:
   - An arena (`typed_arena`) provides fast bump allocation and bulk destruction when the entire arena is dropped, but cannot free individual objects early. Mixing long-lived cross-generation shared nodes with short-lived scratch nodes in the same arena allows a single surviving pointer to pin the entire dead arena.
4. **Copy-on-Write Filesystem Snapshots (`OpenZFS`)**:
   - OpenZFS copy-on-write never overwrites active blocks; creating a snapshot is $O(1)$ because it merely retains a block-tree root reference. As the live dataset mutates, however, old snapshots pin every overwritten or deleted block, and ZFS holds or dependent clones block snapshot reclamation until released—mirroring how one forgotten reader lease or scratch fork in Anneal can pin gigabytes of superseded `.llbc`/`.olean` build trees.

#### 6.3 Layer-Specific Storage and Reclamation Selection for Anneal
| State Layer / Workload | Recommended Representation | Reclamation & Retention Policy |
| :--- | :--- | :--- |
| **In-Process Generation Metadata, Subject-to-Artifact Maps, & Scratch Forks** | Persistent data structures (32-way tries / structural sharing) | Bounded recent-history ring + explicit reader leases; release old roots promptly so uniquely owned paths can update in place |
| **Coarse Stage Outputs (`.llbc`, generated `.lean`, `.olean`, logs)** | Content-addressed immutable blobs referenced by compact generation manifests | Garbage-collect unreferenced blobs outside active generation leases and durable audit pins |
| **Generation-Local Transient Analysis Graphs** | Per-generation or per-request arena (`typed_arena` pattern) | Drop entire arena immediately when the single-generation pass completes; never store cross-generation pointers into the arena |
| **High-Repetition Normalized Types / Expressions** | Selective hash-consing (`ShareCommon` / weak table pattern) | Scope the interner to a generation epoch or use weak references so the table never becomes a permanent memory leak |
| **Materialized File Trees for Opaque External Subprocesses** | Declared-input generation directory or platform CoW clone | Release reader lease on subprocess exit and delete/reclaim unreferenced materialized directories |

---

## Boundaries

1. **Literature and Pinned-Source Scope vs Live Execution**:
   - No Isabelle, Coq/Rocq, `SerAPI`, `Flèche`, `Petanque`, Lean, Lake, or MCP server binary was newly executed for this synthesis. Historical speedups (such as Coq STM's ~10x reactivity and ~4x 12-core speedup on Odd Order in `arXiv:1506.05605`) and scaling limits (Isabelle2019 AFP manual session focusing in `arXiv:1905.01735v1`) are cited as author-reported measurements on their respective workloads.
   - Concrete Anneal mixed-generation and old-proof acceptance findings are bounded to the preserved corpus experiments on `google/zerocopy` (`reference@30b9d5749aed6049d949f4f582dd64c70088d07a`).
2. **Protocol Version Specificity**:
   - LSP findings are bound to specification `3.18` (`microsoft/language-server-protocol@de9a671ae6ba374cc748a29c1c620cbc536302ff` and `9a247101dc088557ae56adef8fecbdc86c9a93ca`), and Lean server findings are bound to `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`).
   - MCP findings are strictly bound to the modern stateless `2026-07-28` specification (`modelcontextprotocol/modelcontextprotocol@5f5440bb26a62e2cf3440b92da5a667efa03b267`); legacy `2025-11-25` designs using `Mcp-Session-Id`, `initialize`, or resumable SSE do not apply to `2026-07-28`.
3. **Database & Filesystem Analogies**:
   - Citing Kung–Robinson OCC, Berenson et al. Snapshot Isolation, Ports–Grittner PostgreSQL SSI, and OpenZFS copy-on-write establishes formal consistency and retention invariants; it does not recommend embedding an SQL database or requiring ZFS in Anneal deployments.

---

## Evidence

### Primary Publications, Specifications, and Pinned Repositories
1. **Isabelle/PIDE Lineage**:
   - Makarius Wenzel, *Isabelle/jEdit — a Prover IDE within the PIDE framework*, `arXiv:1207.3441v1`, DOI `10.1007/978-3-642-31374-5_38` (2012).
   - Makarius Wenzel, *Asynchronous Proof Processing with Isabelle/Scala and Isabelle/jEdit*, ENTCS 285, pp. 101–114, DOI `10.1016/j.entcs.2012.06.009` (2012).
   - Makarius Wenzel, *READ-EVAL-PRINT in Parallel and Asynchronous Proof-checking*, `arXiv:1307.1944v1`, EPTCS 118, pp. 57–71, DOI `10.4204/EPTCS.118.4` (2013).
   - Makarius Wenzel, *PIDE as front-end technology for Coq*, `arXiv:1304.6626v1` (2013).
   - Makarius Wenzel, *Interaction with Formal Mathematical Documents in Isabelle/PIDE*, `arXiv:1905.01735v1`, DOI `10.48550/arXiv.1905.01735` (2019).
   - Lawrence C. Paulson, Tobias Nipkow, and Makarius Wenzel, *From LCF to Isabelle/HOL*, Formal Aspects of Computing 31, pp. 675–698, DOI `10.1007/s00165-019-00492-1` (2019).
2. **Coq/Rocq (`STM`, `SerAPI`, `Flèche` / `rocq-lsp`)**:
   - Bruno Barras, Carst Tankink, and Enrico Tassi, *Asynchronous Processing of Coq Documents: From the Kernel up to the User Interface*, ITP 2015, `arXiv:1506.05605`, DOI `10.1007/978-3-319-22102-1_4`.
   - Emilio Jesús Gallego Arias, *SerAPI: Machine-Friendly, Data-Centric Serialization for Coq*, HAL `hal-01384408` (2016).
   - `rocq-archive/coq-serapi@6196f9f572ef9dd3749b885cabce7a57406cedb9`: `README.md` (`85c5708fe72147f103c87e2316403697f4c51214`), `serapi/serapi_protocol.mli` (`ed3ed38c409d0dc778709c7eeb73bd290f67c006`).
   - `rocq-community/rocq-lsp@2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe`: `README.md` (`37b132ed9c7e15bb4e11205e110d592a1503a6b6`), `etc/doc/USER_MANUAL.md` (`2b989fcf528d08ef3c58b115f45248d2cf4e0bcc`), `etc/doc/PROTOCOL.md` (`30d2b18cefd1d2b6fdd3493b744426c29b482c57`), `fleche/doc.ml` (`2cb236a36a17acf610c971308e8c9962b341e74f`).
3. **LSP 3.18, Lean 4 (`v4.30.0-rc2`), and MCP (`2026-07-28`)**:
   - `microsoft/language-server-protocol@de9a671ae6ba374cc748a29c1c620cbc536302ff` and `9a247101dc088557ae56adef8fecbdc86c9a93ca` (LSP 3.18 specification files).
   - `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`): `Watchdog.lean` (`68ed22f9178c9ae917c595c364d23df902d9478f`), `FileWorker.lean` (`c803034ed8810f13a5ef38a603a21e610efca2bc`), `ProtocolOverview.lean` (`4f493fc900319113e00a0a9c0f5eac4c3e5bb8e5`), `RequestCancellation.lean` (`7d310d0cd941641334a799828d4746c08e6a89d1`), `Lean.lean` (`124d4739bc910eb30ec35844348c785bf9f6c70a`), `PersistentArray.lean` (`516fb0ce50651c1ef39cccdca48663335dac7790`), `PersistentHashMap.lean` (`f963f3a3f3cfc8c262e14bfcf56d21fc3a55442d`), `Init/ShareCommon.lean` (`4692b83a1939718e215918261cb5666e2ef9c88a`), `Lean/Util/ShareCommon.lean` (`d64141f8e6e026170f0fa4089e0cd2e43f9d47bb`).
   - `modelcontextprotocol/modelcontextprotocol@5f5440bb26a62e2cf3440b92da5a667efa03b267` (`2026-07-28` specification and `schema/2026-07-28/schema.ts` blob `9b55feeb412bc3ae877f2eac10b5c01ba29a2eed`).
4. **Concurrency Control, Semantic Merging, and Persistent Data Structures**:
   - H. T. Kung and J. T. Robinson, *On Optimistic Methods for Concurrency Control*, ACM TODS 6(2), 1981, DOI `10.1145/319566.319567`.
   - M. P. Herlihy and J. M. Wing, *Linearizability: A Correctness Condition for Concurrent Objects*, ACM TOPLAS 12(3), 1990, DOI `10.1145/78969.78972`.
   - H. Berenson et al., *A Critique of ANSI SQL Isolation Levels*, SIGMOD 1995 / MSR-TR-95-51, DOI `10.1145/223784.223785`.
   - D. R. K. Ports and K. Grittner, *Serializable Snapshot Isolation in PostgreSQL*, PVLDB 5(12), 2012.
   - S. Horwitz, J. Prins, and T. Reps, *Integrating Noninterfering Versions of Programs*, ACM TOPLAS 11(3), 1989, DOI `10.1145/65979.65980`.
   - J. R. Driscoll, N. Sarnak, D. D. Sleator, and R. E. Tarjan, *Making Data Structures Persistent*, JCSS 38(1), 1989, DOI `10.1016/0022-0000(89)90034-2`.
   - RFC 9110 (*HTTP Semantics*, §§13.1.1, 13.2); `git/git@a018953688f1b10bddf91bff8747068f5f4746a4` (`Documentation/git-update-ref.adoc` blob `37a5019a8bc75e29f23decb8b1b70c28c9412771`); OpenZFS Copy-on-Write and Snapshots documentation; `typed_arena` `2.0.2`; OCaml `fix` `20250919` (`HashCons.ml`).
   - `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92` (`anneal/PRINCIPLES.md` `d5339a95254eae14ac201139d07d9d36d48a19fb`, `anneal/DESIGN.md` `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`) and reference corpus execution evidence at `30b9d5749aed6049d949f4f582dd64c70088d07a`.

### Staged `support/` Artifacts
- **Isabelle/PIDE**:
  - `support/isabelle-pide-document-processing-2008-2019/evidence-map.json`
  - `support/isabelle-pide-document-processing-evolution-2009-2019/evidence-map.json`
- **Coq/Rocq (`STM`, `SerAPI`, `Flèche`) & Current-Source Review**:
  - `support/coq-rocq-stm-serapi-fleche-architecture-2013-2026/evidence-map.json`
  - `support/rocq-serapi-fleche-current-source-review/baseline-report-paths.txt`
  - `support/rocq-serapi-fleche-current-source-review/check_matrix.py`
  - `support/rocq-serapi-fleche-current-source-review/frozen-cohort.csv`
  - `support/rocq-serapi-fleche-current-source-review/matrix.json`
  - `support/rocq-serapi-fleche-current-source-review/official-source-observation.json`
  - `support/rocq-serapi-fleche-current-source-review/rocq-lsp-refs.txt`
  - `support/rocq-serapi-fleche-current-source-review/serapi-refs.txt`
  - `support/rocq-serapi-fleche-current-source-review/snapshots/rocq-lsp/README.md`
  - `support/rocq-serapi-fleche-current-source-review/snapshots/rocq-lsp/etc/doc/PROTOCOL.md`
  - `support/rocq-serapi-fleche-current-source-review/snapshots/rocq-lsp/etc/doc/USER_MANUAL.md`
  - `support/rocq-serapi-fleche-current-source-review/snapshots/rocq-lsp/fleche/doc.ml`
  - `support/rocq-serapi-fleche-current-source-review/snapshots/serapi/README.md`
  - `support/rocq-serapi-fleche-current-source-review/snapshots/serapi/serapi/serapi_protocol.mli`
  - `support/rocq-serapi-fleche-current-source-review/version-inventory-ebcdcad-581.csv`
- **LSP 3.18 & MCP `2026-07-28`**:
  - `support/lsp-proof-assistant-architecture/architecture-model.json`
  - `support/lsp-proof-assistant-architecture/source-map.json`
  - `support/mcp-proof-assistant-architecture/source-map.json`
- **MVCC, Optimistic Semantic Transactions, & Persistent Snapshot Space Costs**:
  - `support/mvcc-snapshot-isolation-proof-work-consistency-1981-2026/evidence-map.json`
  - `support/optimistic-edits-semantic-transactions-1981-2026/decision-matrix.json`
  - `support/optimistic-edits-semantic-transactions-1981-2026/evidence-map.json`
  - `support/persistent-data-structures-snapshot-space-costs-1989-2026/evidence-map.json`

---

## Revalidation

1. **Coq/Rocq (`SerAPI` and `rocq-lsp` / `Flèche`)**:
   - Run `python3 support/rocq-serapi-fleche-current-source-review/check_matrix.py` to verify the frozen hashes and preserved source snapshots, and compare `rocq-community/rocq-lsp` `main` against `2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe` (`README.md`, `USER_MANUAL.md`, `PROTOCOL.md`, `fleche/doc.ml`) if newer upstream commits land.
2. **LSP and Lean 4 Server Architecture**:
   - When upgrading the pinned Lean toolchain past `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) or LSP past `3.18`, diff `Watchdog.lean`, `FileWorker.lean`, `RequestCancellation.lean`, `Lean.lean`, `PersistentArray.lean`, `PersistentHashMap.lean`, and `ShareCommon.lean` to verify whether per-file worker isolation, edit-driven cancellation, imported-module `.olean` boundaries, and 32-way persistent collection layouts changed.
3. **MCP Specification Evolution**:
   - For any MCP revision after `2026-07-28` (`5f5440bb26a62e2cf3440b92da5a667efa03b267`), diff `basic/index.mdx`, `basic/versioning.mdx`, `changelog.mdx`, `patterns/mrtr.mdx`, `server/tools.mdx`, and `schema.ts` to check whether per-request statelessness, explicit tool handles, or the Tasks extension changed.
4. **Concurrency, Optimistic Edits, and Snapshot Retention Probes**:
   - Execute the five concurrency and stale-semantic verification checks whenever Anneal's workspace/edit surface changes: (a) read-snapshot isolation under concurrent generation publication, (b) multi-file generation pinning vs in-place replacement, (c) optimistic edit rejection/recomputation when upstream model or obligation identities advance, (d) write-skew prevention across coupled disjoint files, and (e) resident memory and disk reclamation after releasing reader leases and scratch forks.
