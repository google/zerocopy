# Existing Lean MCP implementations span several distinct proof-interaction models

## Summary

Current public Lean-facing MCP implementations do not converge on one server architecture. They fall into four useful families: LSP-backed editor bridges, warm or directly hosted Lean evaluators, compiler/proof-search services, and retrieval-only or infrastructure servers. That distinction matters more than the common MCP wrapper.

For interactive proof work, at least five examined implementations expose tactic or goal state, but they identify the queried state differently. `oOo0oOo/lean-lsp-mcp`, `RIvance/lean4-mcp`, and `r-irbe/lean4-lsp-mcp` query a live Lean language server at a file position. `lean-host-mcp` deliberately avoids cursor coordinates in its public API and resolves a declaration plus proof-position selector against a supervised direct Lean worker. LeanProbe instead creates an explicit proof session from code containing `sorry` and advances server-local proof-state identifiers tactic by tactic. These are not interchangeable state models.

Server reuse is likewise implementation-specific. LSP bridges keep `lake serve` processes and document state alive. LeanProbe keeps a Lean REPL warm. `lean-host-mcp` serializes calls through one worker owner per Lake project while allowing different projects to run concurrently. Job-oriented systems such as leanforge-mcp and Axiomatic Prover persist asynchronous proof jobs rather than editor state. Retrieval servers such as LeanExplore need no live elaborator state at all.

The strongest reusable conclusion for an interactive Anneal design is therefore architectural: MCP can expose exact tactic-state queries, edit/check loops, long-lived prover processes, and proof-search jobs, but MCP does not supply a common Lean snapshot identity. Anneal still needs to choose and encode its own identities for generated source, document revision, declaration/proof position, prover generation, and any mutable proof session.

Basis: documentation + source-oriented architecture documentation + derived comparison.

## Applicability

This report is a source-and-documentation snapshot of the exact Git revisions listed in `REPORT.json`, observed on 2026-09-27. It covers public repositories found by targeted GitHub searches for Lean 4 + MCP and then selected because they materially illustrate proof interaction, tactic-state retrieval, edit/check loops, process reuse, or adjacent MCP infrastructure.

The comparison is intentionally not an exhaustive census. GitHub search returns many forks of `oOo0oOo/lean-lsp-mcp`; forks were not counted as independent architectures unless their public surface materially diverged. Search-only servers and an MCP SDK are included as boundary cases because they clarify which capabilities do not require a live Lean process. Hosted services are described only to the extent their checked-in public documentation exposes architecture and tool semantics.

No server was executed for this report. Claims about supported tools, transport, reuse, mutability, and state lifetimes come from the identified repository revisions. Performance numbers advertised by projects are not adopted as findings here unless needed only to explain an architectural choice.

The report does not claim that these revisions are mutually compatible, that their MCP protocol revisions match, or that one can substitute for another without changing semantics. In particular, `RIvance/lean4-mcp` documents the legacy MCP protocol version `2024-11-05`, while newer servers may use newer SDKs or transports.

## Findings

### The implementation landscape is architectural, not merely a tool-name taxonomy

The examined projects divide into several distinct families:

| Project | Lean backend | Primary model-facing surface | Mutability | Reuse/state model |
| --- | --- | --- | --- | --- |
| `oOo0oOo/lean-lsp-mcp` | Lean LSP via `lake serve` and `leanclient` | editor queries, goals, term goals, diagnostics, code actions, snippets, tactic screening | mostly query/check; agent applies file edits | persistent LSP plus scratch documents; optional REPL path for selected tools |
| `RIvance/lean4-mcp` | Lean LSP | open documents, diagnostics, goal state, document edits | MCP can replace/apply edits to open documents | live LSP workspaces and open-document state |
| `r-irbe/lean4-lsp-mcp` | persistent `lake serve` plus direct `.ilean` reads | plain goals, term goals, definitions, module DAG, code actions, C FFI navigation | query/navigation surface | persistent Lake server process manager plus offline compiled indexes |
| `jcreinhold/lean-host-mcp` | direct Lean elaborator/kernel in supervised worker child | declaration-centric context, non-mutating proof trials, verification, lookup | read-only | one serialized worker owner per project; multiple projects concurrent; worker restart is explicit runtime state |
| LeanProbe | warm LeanInteract REPL | snippet/declaration checks plus explicit tactic sessions | never edits source files | warm REPL; proof `session_id` and state IDs live in the running process |
| LeanTool | Lean executable plus Pantograph | compile/check loop, goal extraction from `sorry`, plugin tools | submitted code is transient tool input | process/tool-call loop rather than editor document model |
| `lean-proof-auto-mcp` | reusable Lean server adapters and source-splice harnesses | theorem scanning, automation probing, candidate validation, context extraction | analyses and validates candidates; workspace modes exist | Lean servers reused by project root |
| leanforge-mcp | repeated `lake env lean` compiles in a persistent Lake workspace | asynchronous proof-search jobs and compiler-feedback trajectories | proof jobs generate candidate source in temporary files | SQLite-persisted jobs/attempts; independent proof-search agents |
| Axiomatic Prover MCP | hosted Mathlib-enabled compiler/prover service | async compile/prove jobs plus status polling | remote submitted code | server-side job IDs, not local editor/prover sessions |
| LeanExplore | indexed declaration corpus | structured theorem/declaration search | read-only | index/cache state; no live elaborator required |
| LeanMCP SDK | native Lean library implementing MCP machinery | infrastructure for building arbitrary Lean-native MCP servers | application-defined | application-defined; stdio dispatcher supplied by SDK |

Basis: documentation.

This classification avoids a misleading conclusion from the shared word “MCP.” An agent that needs a goal at a cursor position depends on live document elaboration semantics. An agent that needs to test a candidate declaration may only need a prepared environment and isolated elaboration. A proof-search service can instead expose a durable job ID and hide all intermediate prover state. These choices determine invalidation, concurrency, and recovery requirements upstream of MCP itself.

### Exact tactic-state retrieval is already implemented through at least three different identity schemes

`oOo0oOo/lean-lsp-mcp` exposes `lean_goal` at a line or line-and-column in a Lean file, plus `lean_term_goal` at a line-and-column. Its tool documentation also exposes diagnostics, hover, references, completions, code actions, widgets, and a `lean_multi_attempt` operation that can test multiple tactics at a proof position. Position-sensitive attempts use the LSP path; some line-based attempts can use an optional REPL path. The README states that the server runs `lake serve` in the project root for most tools.

Basis: documentation.

`RIvance/lean4-mcp` exposes `get_goal_state` at a cursor position and couples it with explicit document operations: open a disk or in-memory document, replace a document, apply a range edit, read the current text, close the document, inspect processing status, and list open documents. Its README says the Rust proxy translates MCP calls to the Lean 4 language server over stdio MCP protocol version `2024-11-05`.

Basis: documentation.

`r-irbe/lean4-lsp-mcp` exposes `lean_plain_goal` and `lean_plain_term_goal`, backed by Lean's `$/lean/plainGoal` and `$/lean/plainTermGoal` requests against persistent `lake serve` children. It combines those live queries with direct `.ilean` parsing for definition navigation and module dependency queries. Its public design therefore separates queries that require live elaboration from queries answerable from compiled artifacts.

Basis: documentation.

`lean-host-mcp` makes the opposite public-API choice. Its architecture document states that agents name a declaration and, where needed, a proof position inside it; agents do not name cursor coordinates, source spans, byte offsets, or replacement ranges. The host translates that semantic selector into a bounded read-only job against a supervised Lean worker. This is evidence that a proof-assistant MCP does not have to expose the LSP coordinate model even when it supports proof-position queries.

Basis: documentation.

LeanProbe uses yet another scheme. `lean_proof_state` accepts code containing `sorry` and returns a `session_id` plus proof-state IDs. `lean_tactic` advances one proof state; `lean_close_proof` releases the session. The project's skill explicitly says these session and state IDs live only in the running server process and must be recreated after restart.

Basis: documentation.

**Derived implication for Anneal.** “Query tactic state” is not a complete interface contract. Anneal must decide whether a query names a generated-file document revision and source position, a declaration and semantic proof selector, or an explicit transient proof-session state. If more than one mode exists, the response should identify which state model was used so an agent cannot accidentally treat one identity as another.

### Edit/check loops range from document mutation to intentionally read-only experimentation

`RIvance/lean4-mcp` is the most explicitly editor-like examined surface. The MCP server owns open-document text and exposes targeted range edits and whole-document replacement before subsequent diagnostics or goal queries. This mirrors an IDE client and makes the live language-server document revision part of the effective proof state.

Basis: documentation.

`oOo0oOo/lean-lsp-mcp` keeps file queries and proof experimentation separate from agent-side source mutation. `lean_code_actions` returns resolved edits for “Try this” suggestions, but its documentation says the agent applies those edits using its own editing tools. `lean_multi_attempt` screens alternatives without requiring the client to commit them to the source file, while `lean_run_code` handles isolated snippets through a REPL or scratch document.

Basis: documentation.

`lean-host-mcp` is deliberately non-mutating. Its public tools read source and elaborate in memory. `lean_trial` provides proof-step and command experiments while preserving a read-only server contract. This makes “try a tactic” an evaluation request rather than an edit operation.

Basis: documentation.

LeanProbe follows the same non-mutating principle but presents it differently: `lean_check_target` can check a complete replacement declaration against prepared prior context, while tactic exploration uses a temporary proof session. The project tells callers to apply accepted code themselves and reserve `lake build` as the final project-wide gate.

Basis: documentation.

LeanTool and `lean-proof-auto-mcp` are more checker-oriented. LeanTool submits code to Lean and can use Pantograph-derived goal states from `sorry`; `lean-proof-auto-mcp` exposes theorem/file analysis, automated tactic probes, candidate-proof validation, and theorem-context extraction. Neither public README centers a live editor-document mutation protocol.

Basis: documentation.

**Derived implication for Anneal.** Editing generated Lean through a long-lived server and testing a candidate proof without mutating the canonical generated source should be separate operations unless Anneal deliberately chooses one model. The first needs document-version and external-file-change rules; the second needs an exact input snapshot and result provenance.

### Long-lived process reuse is common, but implementations put the serialization boundary in different places

`oOo0oOo/lean-lsp-mcp` keeps Lean language-server state alive through `lake serve`. Its configuration exposes a scratch-slot count for parallel snippet trials and a build-concurrency policy. That is evidence that a single MCP process can own multiple internal Lean interaction lanes rather than mapping one MCP call to one new Lean process.

Basis: documentation.

`r-irbe/lean4-lsp-mcp` likewise documents a Lake server process manager that retains persistent `lake serve` children. It supplements live LSP requests with offline `.ilean` reads, allowing some requests to bypass elaboration entirely.

Basis: documentation.

`lean-host-mcp` makes serialization explicit in its architecture. A `ProjectBroker` owns an LRU pool keyed by canonical Lake root. Each `LeanProject` owns a dedicated controller thread that is the sole owner of one worker host handle. Calls for one project are submitted one at a time in FIFO order through a bounded queue, while different projects can run concurrently up to the configured project-worker limit. Worker death and restart remain structured runtime events rather than transport identity.

Basis: documentation.

LeanProbe reuses a warm LeanInteract REPL and prepared environment. Its public usage contract says the initial import load can be expensive while later same-file checks reuse the warm environment. Explicit tactic sessions are process-local, so restart invalidates them.

Basis: documentation.

leanforge-mcp instead persists proof-search state above Lean. Its architecture describes a persistent Lake workspace, temporary `.lean` files compiled with `lake env lean`, independent search agents, and SQLite tables for durable jobs and attempts. The durable identity is a job and attempt trajectory; Lean compiler processes are implementation details below that boundary.

Basis: documentation.

Axiomatic Prover exposes the same high-level pattern as a hosted service: `lean4_build` and `lean4_prove_theorems` return a `job_id`, and `lean4_get_job_status` polls it. Its public MCP contract does not expose the underlying Lean process identity.

Basis: documentation.

**Derived implication for Anneal.** A long-lived Lean process is a performance/resource-management choice, not a sufficient semantic identity. Cache reuse should be guarded by explicit project/toolchain/source state. If calls are serialized per project, the queueing and restart generation should be observable enough to diagnose stale-state failures. Parallelism should be introduced at an explicit layer—different projects, scratch documents, or isolated workers—rather than assuming arbitrary requests against one Lean runtime are independent.

### Existing servers expose three materially different recovery models

LSP-backed bridges recover by reconstructing workspace/document state and restarting the language server. Their exact recovery semantics are not uniform in the examined public documentation, but open documents and document contents are clearly part of the relevant state for editor-style bridges.

LeanProbe explicitly invalidates proof-session identifiers when its server process dies; callers recreate the proof session. `lean-host-mcp` surfaces worker death, session loss, and restart recovery as structured runtime failures while the project broker remains the higher-level owner. Job-oriented services persist enough state above Lean to survive or report process interruptions independently of a single prover process.

Basis: documentation + derived comparison.

For Anneal, that suggests separating at least three identities if an interactive service is added: a durable project/generated-source identity, a replaceable prover-process generation, and any transient proof-session identity. Conflating those layers makes restart recovery and cache invalidation ambiguous.

### Search-only servers and SDKs show useful boundaries

LeanExplore is an MCP-backed search engine over extracted Lean declarations. Its current README describes both hosted and local MCP backends and states that all MCP tools are read-only. It is valuable to an agent without maintaining a live Lean elaborator or proof state.

Basis: documentation.

The `drhodes/lean-mcp` repository is a native Lean 4 MCP SDK rather than a theorem-proving server. It supplies JSON-RPC types, stdio transport, and an asynchronous thread-safe dispatcher. A future Anneal component written in Lean could use such infrastructure without inheriting any of the proof-state semantics discussed above.

Basis: documentation.

These boundary cases support a useful decomposition: theorem retrieval, protocol hosting, live proof-state inspection, candidate evaluation, and asynchronous proof search are independently composable capabilities. A single monolithic MCP server is not required.

### The current ecosystem already demonstrates the tactic-state capabilities Anneal is likely to need

The public tool surfaces establish feasibility for several concrete interactions:

- goal/local-context retrieval at a line/column through Lean's LSP;
- expected-term queries at a source position;
- diagnostics and hover/reference queries on live documents;
- resolved code-action extraction for tactic suggestions;
- testing multiple tactics without permanently editing the source file;
- direct elaborator/kernel queries that avoid exposing raw cursor coordinates;
- explicit tactic-by-tactic proof sessions against a warm REPL;
- project-local server reuse with bounded serialization and restart handling; and
- asynchronous whole-theorem proof search with durable job IDs.

Basis: documentation.

What these projects do **not** establish is a common cross-server state or source-identity protocol. Each project invents the layer above MCP according to its backend. Anneal therefore cannot delegate its Rust → LLBC → generated Lean → proof-position identity problem to “MCP support” in general.

Basis: derived comparison.

## Boundaries

**Not examined:** The servers were not installed or executed. No latency, memory footprint, concurrency behavior, crash behavior, or correctness property was independently measured.

**Not examined:** This report does not enumerate every GitHub fork, private/internal integration, editor plugin, hosted service, or repository that happens to expose one Lean-related MCP tool. Search results were curated for distinct architectures relevant to Anneal.

**Not examined:** Source-level protocol conformance was not audited. In particular, the report does not claim that every server implements the current MCP `2026-07-28` protocol. One examined repository, `RIvance/lean4-mcp`, explicitly documents `2024-11-05`.

**Unknown:** The exact server-side state retained by hosted Axiomatic Prover between job polls is not exposed by the checked-in README, beyond the public job-ID interface.

**Unknown:** Public docs for several projects do not completely specify how externally modified files are synchronized with already-open Lean LSP documents. That question needs a separate generated-file/LSP workflow investigation.

**Known not to apply:** LeanExplore does not provide live tactic-state interaction; it is a declaration-search service. LeanMCP is protocol infrastructure, not a proof-state server. They are included only to mark architectural boundaries.

**Known not to apply:** LeanProbe explicitly does not edit project files. `lean-host-mcp` is deliberately read-only. Their proof experiments therefore do not establish semantics for an MCP server that mutates the canonical generated Lean source.

**Unsupported as a corpus conclusion:** No evidence here establishes that a long-lived LSP server and a batch Lean invocation are semantically equivalent. The projects demonstrate reuse patterns; equivalence and invalidation require their own report.

## Evidence

Evidence was acquired on 2026-09-27 from immutable Git revisions.

### LSP-backed interactive servers

- `oOo0oOo/lean-lsp-mcp@bb176c58a4f895061561685318e92b8db446f1b5`
  - `README.md`, blob `123429a8ab2a008237513d26f2e89de5a89b5583`: project architecture, `lake serve`, MCP setup, transport/configuration and process-reuse knobs.
  - `docs/tools.md`, blob `b68e2977c2f214d2a049cc7a007c32d7115b2d72`: `lean_goal`, `lean_term_goal`, diagnostics, code actions, `lean_multi_attempt`, snippet checking, and other tool semantics.
- `RIvance/lean4-mcp@b749d9ca766e97020563e9ee72a7f0bbbddd690e`
  - `README.md`, blob `e729e839cca17ade4f5bb0034ee87962749bbe81`: Rust Lean-LSP proxy; document lifecycle/edit tools; cursor goal queries; stdio MCP protocol `2024-11-05`.
- `r-irbe/lean4-lsp-mcp@e7ab346852aad2e1fb54f2aeceefff608122945e`
  - `README.md`, blob `5ef2ca7124d0ccb3f32b73f0e96e7cc119495b83`: persistent `lake serve` process manager, `$/lean/plainGoal`, `$/lean/plainTermGoal`, direct `.ilean` navigation, and tool surface.

### Direct/warm Lean interaction

- `jcreinhold/lean-host-mcp@248d043e674518ad45f1e64c1c9c16647625ad5d`
  - `README.md`, blob `9f9a4885d7c8c4b2296e58de8f8ecfc53139abde`: read-only direct elaborator/kernel surface, transports, project routing, concurrency, response trust identity.
  - `docs/architecture.md`, blob `8e922ae7013ada8ce5eb1b3292a411fc7a679d02`: declaration-centric selectors, broker/project/worker ownership, serialization, restart and cache boundaries.
- `epfl-lara/LeanProbe@646cb0ee3d428562b13740649aa7c1689ec0720a`
  - `README.md`, blob `212fa45ede8d33578307939730a664f76f1e30da`: warm LeanInteract REPL, six MCP tools, read-only operation.
  - `src/lean_probe/skill/SKILL.md`, blob `973f97809d6978ff60a629a8aa6d7a1223a42b80`: exact tool workflow, process-local session/state IDs, restart behavior, replacement checking, final build boundary.
- `GasStationManager/LeanTool@1a4b5ef12ac593202df195d9924981d62608423e`
  - `README.md`, blob `2e69417eb339cfdeb0038bc46a161eb368520294`: compiler/check loop, Pantograph goal extraction, MCP server modes, and plugin surface.
- `padieul/lean-proof-auto-mcp@8d829ecf8e25ac7597fd5cc41b043a40aa404ec1`
  - `README.md`: theorem/file scanning, automated probes, proof-attempt validation, proof-context extraction, Lean-server reuse by project root, and workspace modes.

### Proof-search/job services

- `sandraschi/leanforge-mcp@568aafbd4a8f27efa5a4d49f65039cbd5e2754cd`
  - `README.md`, blob `65f68349fa60f0feecfaa07193e8507855356b71`: async job tools and public proof-loop surface.
  - `docs/ARCHITECTURE.md`, blob `4729a2199565d62779ff6877dd608fa87af98fee`: compiler-feedback loop, independent agents, SQLite job/attempt persistence, persistent Lake workspace and temp-file compiles.
- `Axiomatic-AI/ax-prover-base-mcp@5ade6ba077f7f2e10abcd6a64f124a69fe2bc6ca`
  - `README.md`, blob `6206f36e5fbe76e569627b5414e8356607ec6fa1`: hosted Streamable HTTP service, OAuth, async compile/prove jobs, `job_id` polling contract.

### Boundary implementations

- `justincasher/lean-explore@6b25f8632cc3387cf85f7730375a690a1f1dfb79`
  - `README.md`, blob `ba91509ab68ce642584449e90ce2f73012c6f484`: hosted/local read-only MCP declaration search and indexed Lean ecosystem.
- `drhodes/lean-mcp@76d23b4146e24860a90fb0d9e1f5f0a43ff455f1`
  - `README.md`, blob `d29105002fdd2fa508baba156ce9294cc6639b54`: native Lean 4 MCP SDK, JSON-RPC, line-framed stdio, and thread-safe asynchronous dispatch.

The accompanying `source-map.json` preserves the subject/commit/path/blob coordinates and the architectural role assigned in this synthesis.

## Revalidation

For a later snapshot, revalidate cheaply in this order:

1. Resolve each included repository's intended current release/default revision and diff the evidence files above. Do not infer continuity from a version bump.
2. For LSP-backed servers, check whether goal/term-goal tools still route through the same Lean LSP requests and whether document mutation/reuse semantics changed.
3. For `lean-host-mcp`, diff the transport boundary, project broker/controller, and public selector contract; changes there can alter serialization or state identity without changing tool names.
4. For LeanProbe, diff the tool contract around `session_id`, proof-state IDs, restart behavior, and warm-environment reuse.
5. For job-oriented services, check whether `job_id`/attempt persistence or Lean-process ownership changed materially.
6. Re-run targeted GitHub repository searches for `lean mcp`, `lean4 mcp`, and `Lean theorem prover MCP`; add only projects that introduce a materially distinct architecture or tool surface.
7. If Anneal needs a claim stronger than documentation—for example exact LSP document-version behavior, concurrent request ordering, crash reconstruction, or batch/server equivalence—run a separate focused execution study rather than extending this report by inference.
