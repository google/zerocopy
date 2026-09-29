## Goal

Build the evidence needed to design an Anneal V2 architecture that can later support interactive LSP and MCP workflows across Rust/Charon, Aeneas, Lake, and Lean without weakening batch correctness, cache consistency, source correspondence, or parallel-test scalability.

The motivating design is roughly:

```text
CLI / LSP / MCP
      |
      v
Anneal workspace / snapshot engine
      |
      +--> Charon backend
      +--> Aeneas backend
      +--> Lake / prepared-environment layer
      +--> Lean server backend
```

For Lean-authored Anneal annotations, especially proofs embedded in Rust source, a stronger form is relevant:

```text
Rust source snapshot
    |
    +-- ordinary Rust
    |
    +-- embedded Lean annotation
            |
            | exact projection + provenance
            v
      projected Lean document
            |
            +-- generated/imported Aeneas model
            +-- Anneal scaffolding
            +-- user-authored Lean proof
            |
            v
       Lean language server
```

This issue is a **research backlog**, not adopted architecture. The point is to confirm, falsify, or refine the design before its assumptions harden into V2 interfaces.

It complements #3720, #3725, and #3668. The current reference corpus already contains substantial component-level work on Charon/Aeneas incrementality, Lean tactic-state APIs, Lean workspace isolation, Lake state/cache ownership, generated-file synchronization, source correspondence, and concurrency. Do not duplicate those surveys. Before starting an item below, check the current `reference` tip and either:

- extend an existing report with stronger evidence;
- add a new report for a genuinely distinct subject;
- record that the question is already answered; or
- narrow the investigation to the remaining uncertainty.

## Why more work is needed

Two existing execution reports already show why composition-level evidence matters:

- A successful wait for an **older** Lean document version can be followed by a goal result for a **newer** version; `plainGoal` is not itself version-bound.
- In a generated V1 workspace, rebuilding an imported generated module, notifying the server, and resending the proof at a newer document version still left the same server accepting a proof that a fresh server and batch Lean rejected.

So a correct interactive design cannot equate any one of these with semantic freshness:

- current pathname;
- current document version;
- successful Lake build;
- a live Lean process;
- a stable generated module name;
- an artifact-cache hit;
- or a successful tactic-state query.

The central research problem is to identify the **minimum sufficient cross-layer identity and synchronization contract** that makes interactive results trustworthy while keeping normal proof edits fast and parallel workloads cheap.

## Evidence discipline

Each investigation should state:

1. the exact subject revisions/configuration;
2. the architectural hypothesis being tested;
3. what would confirm it;
4. what would falsify it;
5. the strongest feasible evidence type:
   - **S** — source/specification analysis;
   - **X** — executed probe or measurement;
   - **M** — machine-checked proof/model;
   - **U** — user/agent workflow evaluation;
6. which design choice would change based on the result.

For race, cache, and concurrency questions, one successful run is not enough to establish safety. Use negative controls and interruption/failure injection where practical.

For equivalence questions, distinguish byte equality, build-system freshness, elaboration equivalence, theorem acceptance, semantic equivalence, and source-level claim equivalence.

---

# A. Snapshot identity and end-to-end freshness

These are the most architecture-critical investigations.

### A01. Define the minimum sufficient interactive generation identity [S/X]

Determine the smallest state tuple that prevents stale results across Rust, LLBC, generated Lean, Lake artifacts, and Lean workers.

Candidate dimensions include:

- Cargo compilation-subject identity;
- Rust source snapshot identity;
- Charon configuration/tool identity;
- LLBC digest/generation;
- Aeneas configuration/tool identity;
- generated-Lean tree digest/generation;
- Lake workspace/prepared-environment identity;
- relevant import artifact traces/hashes;
- projected Lean document URI/version/hash;
- Lean server generation;
- Lean file-worker incarnation;
- RPC-session incarnation.

Use mutation experiments to remove one dimension at a time and find counterexamples.

**Design impact:** defines the internal key carried by diagnostics, tactic states, verification results, caches, and agent handles.

### A02. Distinguish locator identity from semantic generation across every stage [S/X]

Construct cases where paths/names stay constant while contents change:

- same Cargo target slug, changed Rust;
- same `.llbc` pathname, changed LLBC;
- same generated `.lean` pathname, changed Aeneas output;
- same `.olean` pathname, changed imported environment;
- same proof URI/version reset after reopen;
- same MCP workspace handle after server restart.

Record where stable locators are useful and where treating them as freshness tokens fails.

**Design impact:** prevents stable path/name APIs from accidentally becoming cache-validity APIs.

### A03. Mixed-generation race matrix [X]

Deliberately overlap:

- Rust edit while Charon is running;
- LLBC replacement while Aeneas is running;
- generated-Lean publication while Lake is building;
- Lake rebuild while Lean is elaborating;
- proof edit while dependency regeneration completes;
- MCP goal request while any upstream generation advances.

Require that every returned result is attributable to one coherent generation or explicitly stale/cancelled.

**Design impact:** validates the proposed snapshot/revision fence rather than relying on best-effort cancellation.

### A04. Old-result publication after cancellation [X]

Force each stage to complete after cancellation or supersession:

- Charon child process;
- Aeneas process/library call;
- Lake build/setup;
- Lean LSP request;
- MCP task.

Verify that late completion cannot overwrite current state.

**Design impact:** establishes whether cancellation is an optimization or mistakenly part of correctness.

### A05. Snapshot retention versus recomputation [X]

Measure the cost of retaining:

- source text only;
- source + projected Lean;
- generated Lean tree;
- Lake workspace-local state;
- live Lean worker;
- compiled generated-module artifacts.

Evaluate 1/2/4/8/16 retained generations.

**Design impact:** informs whether historical-query support is practical or whether old generations should normally expire.

### A06. Historical query semantics [S/X]

Test whether Anneal should support “goal at revision N” after revision N+1 exists.

Compare:

- retaining the old worker;
- reconstructing an old projected document against old imports;
- restarting a worker against retained old artifacts;
- refusing historical queries.

**Design impact:** determines whether MCP revision handles are durable snapshot handles or merely optimistic guards for the current generation.

### A07. Cross-process reconstruction of one generation [X]

Create an interactive generation, destroy all live processes, then reconstruct the same claimed generation from retained state.

Compare diagnostics, goals, imported identities, and batch checking.

**Design impact:** tests whether semantic identity is encoded in explicit state rather than hidden process history.

### A08. Content-hash versus monotonic-revision identity [S/X]

Create edit sequences that:

- change and revert text;
- produce byte-identical generated Lean from different upstream histories;
- produce semantically equivalent but byte-different generated Lean;
- preserve proof text while changing imports.

Determine which uses need monotonic causality, which can use content identity, and where both are required.

**Design impact:** informs cache keys and stale-result fencing.

---

# B. Embedded Lean annotation projection and editing

### B01. Specify the exact projection model [S]

Enumerate all transformations from Rust-hosted annotation text to the Lean document:

- doc-comment prefixes;
- block comments;
- indentation normalization;
- fence removal;
- escaping/unescaping;
- inserted namespace/import/scaffolding text;
- concatenation of multiple annotation regions;
- line-ending normalization.

For each, classify it as lossless, invertible, partially invertible, or synthetic.

**Design impact:** defines the contract for cursor mapping and edits.

### B02. Executed round-trip projection corpus [X]

Build a fixture corpus covering:

- ASCII;
- multibyte UTF-8;
- combining characters;
- wide characters;
- tabs;
- CRLF;
- blank lines;
- nested Markdown fences;
- Lean comments containing fence-like text;
- escaped Rust doc strings;
- block documentation attributes.

For every source position in user Lean text, round-trip Rust → projected Lean → Rust.

**Design impact:** validates exact edit mapping independently of Charon/Aeneas source spans.

### B03. LSP UTF-16 conversion stress test [X]

Exercise source positions before/inside/after surrogate-pair characters and combining sequences.

Compare:

- Rust byte offsets;
- projected Lean byte offsets;
- Lean internal raw positions;
- LSP UTF-16 positions;
- returned diagnostic/goal positions.

**Design impact:** prevents subtle cursor/edit corruption from cross-coordinate conversion.

### B04. Incremental projection update algorithm [S/X]

Compare full-document regeneration with range-local projection updates for proof-only edits.

Measure:

- correctness;
- generated edit ranges;
- Lean incremental reuse;
- implementation complexity;
- behavior around edits that change annotation delimiters or indentation.

**Design impact:** decides whether initial interactive mode should always send full-content `didChange` or support fine-grained changes.

### B05. Projection invalidation after edits outside the annotation [X]

Change Rust text before an unchanged Lean annotation so all physical source positions shift.

Verify:

- projected Lean contents stay stable;
- Rust↔Lean mapping updates correctly;
- in-flight tactic-state results are rejected or remapped safely.

**Design impact:** separates proof-content identity from host-file coordinate identity.

### B06. Annotation delimiter corruption and partial syntax [X]

Interactively edit opening/closing fences, doc-comment markers, or structural annotation syntax until the Lean payload becomes temporarily undiscoverable.

Determine what state remains queryable and what diagnostics should survive.

**Design impact:** defines editor behavior during ordinary half-typed states.

### B07. Multiple Lean annotations in one Rust item/file [S/X]

Test whether projected documents should:

- compose all annotations into one module;
- use one virtual document per annotation;
- use one per Rust item;
- use one per Cargo target.

Measure cross-annotation references and invalidation scope.

**Design impact:** determines virtual-document granularity.

### B08. Cross-annotation name visibility and namespaces [X]

Create annotations that depend on declarations from earlier/later annotations, local namespaces, opened namespaces, section variables, and generated helper names.

**Design impact:** tests whether independently projected fragments can preserve batch semantics.

### B09. Lean import-header ownership for embedded annotations [S/X]

Determine whether users may author imports/options inside annotations and, if so, how those interact with Anneal-generated imports and Lake `setup-file`.

Test unsaved changes to import headers.

**Design impact:** determines whether a proof-only edit can alter prepared-environment requirements.

### B10. User edits versus generated scaffolding edits [S/X]

Probe editor/MCP operations whose Lean range crosses:

- user-authored source;
- synthetic Anneal scaffolding;
- Aeneas-generated code.

Define which transformations are accepted, split, or rejected.

**Design impact:** ensures a generated-code responsibility anchor never silently authorizes a source edit.

### B11. Code actions and rename through projection [S/X]

Exercise Lean:

- code actions;
- rename;
- completion insertion;
- import suggestions;
- go-to-definition.

Determine which returned edits can be safely projected back to Rust-hosted Lean.

**Design impact:** scopes future LSP feature support beyond goals/diagnostics.

### B12. Hover/completion/semantic-token projection [X]

Compare projected positions and ranges for:

- hover;
- completion;
- signature help;
- semantic tokens;
- inlay hints;
- references.

**Design impact:** determines whether the same mapping abstraction suffices for all editor features or whether some need feature-specific rules.

### B13. Diagnostic responsibility versus editable correspondence [S/X]

Construct diagnostics in:

- copied user Lean;
- Anneal-generated theorem names;
- generated binders;
- generated tactics;
- Aeneas-generated terms;
- imported models.

Record which can map exactly to Rust bytes and which only admit a responsibility anchor.

**Design impact:** validates separate “editable projection” and “diagnostic provenance” abstractions.

### B14. Macro-generated or transformed Rust annotations [S/X]

Test annotations produced or modified through:

- `cfg_attr`;
- attribute macros;
- proc macros;
- `include!`;
- generated files.

Determine whether Anneal can offer an editable Lean projection when the source text is not a simple user-owned Rust span.

**Design impact:** defines when interactive editing is supported versus read-only or unavailable.

### B15. Unsaved Rust host buffer as the canonical proof source [X]

Keep the disk file old while the editor buffer contains a new Lean annotation.

Drive the projected Lean document entirely from the unsaved Rust buffer and verify that tactic state follows the buffer rather than disk.

**Design impact:** confirms that future LSP integration can support normal editor semantics without materializing Rust saves.

---

# C. Lean tactic-state, worker, and RPC semantics

### C01. Version-bound goal wrapper protocol [X]

Prototype an Anneal wrapper around `plainGoal` / `getInteractiveGoals` that records:

- request-start document hash/version;
- worker incarnation;
- environment generation;
- response-time current state.

Exercise edits before, during, and after the Lean request.

**Design impact:** validates the proposed snapshot guard.

### C02. Rich RPC versus `plainGoal` stability [S/X]

Compare the two goal-query surfaces for:

- before/after tactic selection;
- nested tactics;
- term proofs;
- syntax errors;
- incomplete elaboration;
- worker restart;
- RPC reconnect.

**Design impact:** chooses whether MCP should expose the simple or rich surface internally.

### C03. Worker restart freshness barrier [X]

After an imported dependency changes, test several refresh strategies:

- watched-file notification only;
- resend proof document;
- close/reopen proof;
- refresh dependencies;
- restart file worker;
- restart entire server;
- new workspace/server generation.

Compare each to fresh batch Lean.

**Design impact:** finds the minimum reliable dependency-change barrier.

### C04. `lake serve` versus `lake env lean --server` invalidation behavior [X]

Repeat the stale-import experiment under both launch paths with identical generated projects.

**Design impact:** determines whether the V1 stale-state result is specific to one launch configuration.

### C05. Changed `.olean`, unchanged source [X]

Replace an imported compiled artifact while leaving its source path and timestamp scenarios varied.

Test whether any server mechanism observes the new environment without worker replacement.

**Design impact:** clarifies whether artifact identity alone must force restart.

### C06. Changed source, byte-identical rebuilt artifact [X]

Create upstream changes that rebuild but produce byte-identical semantic artifacts.

Determine whether restarting is necessary for correctness or only conservatively triggered.

**Design impact:** informs future fine-grained environment equivalence.

### C07. Import graph addition/removal/rename [X]

Regenerate Aeneas output so modules appear, disappear, or move.

Test existing open proofs and server setup.

**Design impact:** validates package-generation replacement rather than file-by-file overwrite.

### C08. RPC object lifetime and handle invalidation [X]

Exercise:

- worker restart;
- server restart;
- reconnect;
- document close/reopen;
- environment swap;
- idle timeout.

Record behavior of stale RPC references and session IDs.

**Design impact:** determines whether any Lean-side reference can escape as a durable MCP object.

### C09. Multiple simultaneous goal queries in one document [X]

Issue queries at many positions while edits occur.

Check ordering, cancellation, completion, and stale-response behavior.

**Design impact:** informs MCP concurrency limits and request bookkeeping.

### C10. Multiple open proof documents importing one generated model [X]

Edit proofs independently, then mutate the shared model.

Verify all affected workers refresh correctly while unrelated workers remain valid.

**Design impact:** tests dependency fan-out invalidation.

### C11. One proof importing another live proof module [S/X]

Explore whether user-authored proof modules may import each other and what “unsaved upstream proof” should mean.

**Design impact:** decides whether live-document dependencies are supported or only compiled saved modules.

### C12. Semantic-ready barrier alternatives [S/X]

Compare:

- `waitForDiagnostics`;
- file-progress completion;
- RPC-specific readiness;
- command-snapshot completion;
- custom server RPC returning current document/environment identities.

**Design impact:** chooses the barrier used before agent actions.

### C13. Partial-file elaboration semantics [X]

Query goals before the entire file has elaborated and while later commands are failing.

Determine which local states are valid for editing versus sufficient for verification claims.

**Design impact:** separates useful interactive feedback from terminal verification.

### C14. Diagnostics/goal disagreement cases [X]

Construct cases where:

- the local goal looks solved but the file has errors elsewhere;
- diagnostics are stale but goal state is fresh;
- imports are out of date;
- theorem closes with warnings or admissions.

**Design impact:** prevents “no goals” from becoming verification success.

### C15. Crash recovery and retained open-document text [X]

Crash a file worker after unsaved proof edits.

Verify reconstruction from watchdog/client state and correct generation association.

**Design impact:** validates recovery semantics for long-lived agent sessions.

---

# D. Charon and Rust live-state boundary

### D01. Saved-only Rust versus unsaved overlay feasibility [S/X]

Compare three possible first interactive contracts:

1. Charon operates only on saved Rust;
2. Anneal materializes an overlay workspace;
3. Anneal integrates at a rustc/Charon API layer that can consume virtual source.

Test build scripts, proc macros, `include!`, path dependencies, and diagnostics.

**Design impact:** decides whether interactive Rust edits can be supported without a save boundary.

### D02. Overlay materialization path sensitivity [X]

If materializing snapshots, vary:

- workspace location;
- symlinks;
- `CARGO_MANIFEST_DIR`;
- `OUT_DIR`;
- relative include paths;
- build-script paths;
- proc-macro behavior.

**Design impact:** determines whether snapshot copies preserve the compiled program.

### D03. Cargo incremental reuse under snapshot materialization [X]

Measure whether isolated overlay workspaces can reuse Cargo/rustc incremental state without cross-generation corruption or huge disk growth.

**Design impact:** affects feasibility of unsaved-Rust support.

### D04. Charon process lifetime versus semantic state [X]

Compare:

- one-shot process;
- reused wrapper process that launches rustc repeatedly;
- any usable in-process/library path.

Measure startup cost and detect process-global state leakage.

**Design impact:** chooses backend lifecycle without changing Anneal’s logical API.

### D05. Charon full-snapshot determinism under concurrency [X]

Run identical translations repeatedly and concurrently.

Compare LLBC semantically and bytewise where meaningful.

**Design impact:** determines whether LLBC content hashes are stable cache identities.

### D06. Charon cancellation/termination cleanup [X]

Terminate extraction at multiple phases.

Check for:

- partial LLBC files;
- stale temp files;
- corrupted shared Cargo state;
- later successful retries.

**Design impact:** informs staging and atomic-publication requirements.

### D07. Compilation-subject invalidation matrix [X]

Change individually:

- Rust body;
- module;
- Cargo feature;
- target;
- profile;
- `cfg`;
- build-script output;
- proc macro;
- dependency version;
- toolchain.

Observe which Charon subjects actually change.

**Design impact:** validates the subject key used above the LLBC boundary.

### D08. Annotation-only host edits that should not rerun Charon [X]

Change only Lean annotation text in Rust comments/doc attributes.

Confirm whether rustc/Charon output is byte/semantic-identical and whether the compiler invocation can be skipped safely.

**Design impact:** validates the proof-only fast path at the Rust boundary.

### D09. Annotation syntax that affects compilation [S/X]

Identify cases where modifying an “annotation region” can indirectly change Rust compilation—for example via attributes/macros/doc processing assumptions.

**Design impact:** defines the proof-only classifier’s safety conditions.

### D10. Stable semantic item correspondence across Rust edits [S/X]

Track compiler-resolved items across whitespace, movement, module changes, renames, and macro expansion.

**Design impact:** determines whether source-level annotation ownership can survive edits without rerunning broad discovery.

---

# E. Aeneas translation and generated-model generations

### E01. Warm-process Aeneas latency without semantic reuse [X]

Measure repeated whole-crate translations while retaining only process/library initialization, not old semantic results.

**Design impact:** determines whether a daemon is worthwhile before incremental translation exists.

### E02. Process-global state reset audit [S/X]

Exercise consecutive translations with different:

- backends/options;
- namespaces;
- output directories;
- crate names;
- error conditions.

Detect leaked module-global configuration or accumulators.

**Design impact:** determines whether one long-lived Aeneas process may safely serve multiple requests.

### E03. Aeneas concurrent-request safety [S/X]

Attempt parallel translations in one process/library context and in separate processes.

**Design impact:** decides whether the backend must serialize per-process requests.

### E04. Generated-tree transactional replacement [X]

Interrupt Aeneas during split-file generation.

Compare:

- direct overwrite;
- temp-directory generation;
- atomic generation-pointer swap.

Check for stale declarations from the previous generation.

**Design impact:** selects the publication mechanism for generated models.

### E05. Declaration deletion and rename [X]

Remove/rename Rust declarations and verify the new generated model contains no stale Lean declaration or stale import.

**Design impact:** validates whole-generation replacement semantics.

### E06. Same-input generated-source determinism under parallel settings [X]

Extend existing determinism work to the exact options/layout Anneal intends to use interactively.

**Design impact:** informs generated-tree hashing and cache identity.

### E07. Generated source semantically identical but textually unstable [X]

Find benign changes in ordering/comments/formatting and test their impact on Lake and Lean incremental reuse.

**Design impact:** determines whether raw generated-source hashes are too coarse as environment identities.

### E08. Aeneas output-to-model manifest [S/X]

Prototype a machine-readable generation manifest containing:

- crate/tool identities;
- source LLBC digest;
- generated file list;
- module/import graph;
- declaration identities;
- coarse source provenance.

Do not assume newer upstream `translation.json` exists at the pinned release.

**Design impact:** evaluates whether Anneal needs its own model-generation manifest.

### E09. Generated model versus user-maintained external models [X]

Mutate each independently and verify ownership/invalidation behavior.

**Design impact:** prevents Aeneas regeneration from overwriting or misclassifying user source.

### E10. External-model change with unchanged generated source [X]

Change a user model imported by generated Lean while Aeneas output remains byte-identical.

**Design impact:** proves generated-tree identity alone is insufficient as proof-environment identity.

### E11. Finer-grained future Aeneas invalidation prototype [S/X]

For one restricted class of body-only edits, experimentally reuse unaffected function translations while checking against clean whole-crate output.

**Design impact:** identifies the metadata a future incremental Aeneas API would require, without adopting it prematurely.

### E12. Aeneas failure mid-generation and old-generation visibility [X]

Cause translation/extraction failures after a previous successful generation exists.

Verify that consumers either retain the complete prior generation as stale or observe no current generation—not a hybrid.

**Design impact:** validates fail-closed publication.

---

# F. Lake prepared-environment and cache contract

### F01. Exact “prepared environment” schema [S]

Enumerate everything required for:

- batch build;
- `lake env lean --json`;
- `lake serve`;
- `setup-file`;
- InfoView/RPC;
- native plugins/dynlibs.

Separate immutable producer state from consumer-owned state.

**Design impact:** defines the environment identity Anneal can safely pool.

### F02. Real archive read-only server probe [X]

Using the actual current Anneal omnibus archive, create a fresh consumer and run:

- build;
- `setup-file`;
- Lean server open/query;
- RPC goal query;
- dependency refresh.

Make the archive physically read-only and inventory all attempted writes.

**Design impact:** replaces synthetic evidence with the real consumer contract.

### F03. Current pinned Lake versus Lean 4.31+ ownership comparison [S/X]

The corpus records a configuration-ownership change after 4.30. Execute the same Anneal-style consumer matrix under both revisions.

**Design impact:** identifies v2 workarounds that can disappear after a toolchain upgrade.

### F04. Manifest-before-first-load necessity in real archive [X]

Repeat the synthetic missing-manifest failure against the actual Aeneas/Mathlib tree.

**Design impact:** decides whether manifest seeding is a hard consumer-construction invariant.

### F05. Prepared-environment identity collision matrix [X]

Create consumers that differ only by:

- assigned dependency name;
- package index;
- relative root;
- `-K` options;
- server options;
- platform;
- Lean hash.

Observe which prepared state can actually be shared.

**Design impact:** determines pool/cache key dimensions.

### F06. Server-specific artifact completeness [X]

Delete one class at a time:

- `.olean`;
- `.olean.server`;
- `.olean.private`;
- `.ilean`;
- native plugin;
- dynlib;
- trace/hash sidecar.

Compare batch build and interactive setup.

**Design impact:** defines what the archive must retain for interactive mode.

### F07. `--no-build --no-cache` fail-closed semantics in real Anneal workspace [X]

Use Lean’s dependency-build-never path with deliberately stale imports.

Confirm that interactive queries fail rather than elaborate against stale or missing imports.

**Design impact:** tests whether Anneal can make the server a read-only semantic consumer while the scheduler owns builds.

### F08. Lake build completion versus server-readiness [X]

Build successfully, then immediately open/query through the server.

Find any additional preparation/rebuild that occurs.

**Design impact:** validates the two-layer “environment prepared / document prepared” model.

### F09. Unsaved import-header changes [X]

Change only an open proof’s import header in memory.

Observe `setup-file`, dependency building, worker restart, and cache behavior.

**Design impact:** classifies when a nominal proof edit ceases to be Lean-only.

### F10. Cache hit observability [S/X]

Determine how Anneal can know whether Lake:

- reused local artifact;
- restored artifact cache;
- rebuilt;
- reconfigured;
- resolved dependency;
- touched network;
- wrote shared state.

If no structured interface exists, quantify how reliable filesystem/process inference is.

**Design impact:** determines what regression tests can assert.

### F11. Artifact-cache concurrent writer crash consistency [X]

Run many identical and different writers; kill writers during publication.

Validate subsequent readers and cache-map integrity.

**Design impact:** decides whether Anneal may share a writable artifact cache across integration tests.

### F12. Shared package-directory writer crash consistency [X]

Demonstrate the failure modes of concurrent writes to one package build directory under interruption.

**Design impact:** establishes a negative invariant against accidental shared writable package trees.

### F13. Read-only producer plus writable consumer stress [X]

Run 2/4/8/16/32 consumers concurrently against one real prepared dependency universe.

Measure writes, failures, rebuilds, latency, disk, and memory.

**Design impact:** validates the intended integration-test storage architecture.

### F14. Relocation after complete server preparation [X]

Relocate:

1. consumer workspace only;
2. toolchain/archive only;
3. both together.

Then run batch and interactive setup/query.

**Design impact:** finds location-bearing state that prevents generation directories from being moved after preparation.

### F15. Publish-in-final-location versus atomic rename [X]

Compare generation preparation at a final stable path with preparation in a staging path followed by rename.

**Design impact:** selects a transactional publication design compatible with Lake path-bearing metadata.

### F16. Network-denied consumer proof [X]

Use OS-level network denial, not only Lake flags.

Exercise batch and interactive paths.

**Design impact:** proves whether prepared environments are genuinely hermetic consumers.

### F17. User cache contamination [X]

Run with:

- empty HOME/XDG;
- populated unrelated Lake/Mathlib caches;
- deliberately incompatible caches.

Compare outcomes.

**Design impact:** identifies hidden global inputs to environment identity.

### F18. Mtime perturbation matrix [X]

Alter source/config/artifact mtimes without changing bytes and vice versa.

Exercise `--old`, normal build, setup-file, and server startup.

**Design impact:** quantifies how much the current architecture still relies on timestamp conventions.

### F19. Clean-build oracle for interactive setup [X]

Extend optimized-vs-clean equivalence beyond archive artifacts to:

- `ModuleSetup`;
- imported artifact paths/hashes;
- server options;
- diagnostics;
- goal queries;
- navigation/reference behavior.

**Design impact:** validates that a fast prepared environment behaves like an independently constructed clean one.

### F20. Generated-module rebuild isolation [X]

Ensure rebuilding project-generated modules never writes into the immutable dependency universe.

**Design impact:** verifies the producer/consumer ownership boundary.

---

# G. MCP-facing architecture

### G01. Stateless MCP workspace-handle prototype [S/X]

Prototype explicit operations such as:

- create/open workspace;
- publish/update source snapshot;
- query current generation;
- query goal;
- run verification;
- close/release handle.

Do not bind correctness to transport-session lifetime.

**Design impact:** validates compatibility with current stateless MCP semantics.

### G02. Handle expiry and stale-generation errors [X]

Exercise:

- server restart;
- process crash;
- workspace GC;
- model regeneration;
- document replacement.

Ensure stale handles fail explicitly rather than being rebound to current state.

**Design impact:** defines durable versus ephemeral MCP identifiers.

### G03. MCP task semantics for long verification work [S/X]

Prototype long-running Charon/Aeneas/Lake verification as MCP tasks with cancellation/progress.

**Design impact:** decides what belongs in synchronous tools versus task-backed operations.

### G04. MCP subscription semantics for diagnostics/progress [S/X]

Evaluate whether subscriptions are useful for:

- generation changes;
- diagnostics;
- proof readiness;
- verification completion.

**Design impact:** determines whether polling should remain the primary correctness path.

### G05. Concurrent agents against one workspace [X]

Run two agents that:

- issue read-only queries;
- propose different proof edits;
- race edits;
- start verification simultaneously.

Define compare-and-swap or expected-revision behavior.

**Design impact:** prevents last-writer-wins corruption.

### G06. Agent proof patch transaction [X]

Implement:

1. query goal at snapshot G;
2. synthesize tactic;
3. apply patch only if G is still current;
4. wait for G+1;
5. re-query.

Inject unrelated edits between every step.

**Design impact:** validates the basic agent loop.

### G07. Scratch tactic trials against projected documents [X]

Clone a projected proof into virtual scratch documents and test tactics without touching canonical source.

Measure warm-prefix reuse and cleanup.

**Design impact:** evaluates an Anneal equivalent of Lean MCP multi-attempt tools.

### G08. Scratch trial environment fidelity [X]

Verify scratch documents see exactly the same imports/options/models as the canonical proof.

**Design impact:** prevents successful experiments in a subtly different environment.

### G09. Read-only versus mutating MCP tool taxonomy [S/X]

Classify:

- goal queries;
- diagnostics;
- scratch trials;
- proof edits;
- regeneration;
- verification;
- cache/environment preparation.

Test that read-only tools cannot trigger hidden source or shared-environment mutations.

**Design impact:** improves safety and agent composability.

### G10. MCP process multiplexing and isolation [X]

Measure one MCP server serving:

- many sessions for one Anneal environment;
- many Anneal environments;
- many independent repositories.

Map the process tree and resource ownership.

**Design impact:** determines whether MCP is one global daemon, one process per workspace, or a lightweight adapter over an external engine.

### G11. Authorization boundary for agent edits [S]

Separate:

- proof-source edit;
- Rust-source edit;
- generated-file edit;
- environment rebuild;
- toolchain setup.

**Design impact:** ensures the protocol does not make generated/cache state appear user-editable.

### G12. MCP response provenance schema [S/X]

Prototype a result envelope that can carry:

- workspace/generation identity;
- source and projected positions;
- stale/current status;
- environment identity;
- diagnostic/goal payload;
- optional verification status.

**Design impact:** determines whether protocol adapters can remain thin over the engine.

### G13. MCP retry/idempotency behavior [X]

Retry identical goal, build, and mutation requests after dropped responses.

**Design impact:** identifies which operations need request IDs or compare-and-swap semantics.

### G14. MCP cancellation races [X]

Cancel before start, during Lean query, during Lake setup, during Aeneas, and immediately after completion.

**Design impact:** validates cleanup and late-result fencing.

### G15. Agent navigation across Rust ↔ Lean boundaries [X/U]

Give an agent tools to move from:

- Rust annotation;
- projected Lean proof;
- generated Aeneas declaration;
- imported model;
- back to owning Rust item.

Measure whether the identity/provenance model is sufficient without exposing brittle filesystem details.

**Design impact:** tests the architecture as an actual agent interface.

---

# H. LSP/editor-facing architecture

### H01. Virtual-document URI strategy [S/X]

Compare file URIs, custom `anneal:` URIs, hidden materialized files, and generated workspace files with Lean’s requirement that queried documents be opened.

**Design impact:** determines whether the Lean server can work directly with virtual projections or needs filesystem-backed paths for setup.

### H02. Custom URI compatibility with Lake `setup-file` [X]

Test whether Lean/Lake can prepare a non-file URI or whether Anneal must provide a real shadow path while exposing a virtual user-facing URI.

**Design impact:** may force a split between Lean’s internal URI/path and the editor-facing document identity.

### H03. Shadow-file synchronization without source-of-truth inversion [X]

If filesystem backing is required, keep an unsaved annotation authoritative while mirroring projected Lean to a shadow file.

Test crash/restart and stale-shadow scenarios.

**Design impact:** prevents disk mirrors from accidentally becoming canonical.

### H04. One editor Rust document, hidden Lean document lifecycle [X]

Open/close/edit a Rust file and trace hidden Lean document creation, updates, server workers, and cleanup.

**Design impact:** validates practical LSP ownership.

### H05. Multiple editor clients on one Anneal workspace [X]

Connect two clients with different unsaved buffers.

Determine whether they require independent workspace snapshots rather than one shared “current document.”

**Design impact:** prevents cross-client buffer contamination.

### H06. Editor save versus unsaved proof model generation [X]

Save the Rust host file while Lean projection already reflects the same or newer buffer.

Ensure no duplicate generation or version reversal occurs.

**Design impact:** defines filesystem watcher interactions.

### H07. File rename/move with open proof state [X]

Rename a Rust file or module while its annotation proof is open.

Track source maps, virtual document identity, imported module names, and worker reuse.

**Design impact:** determines whether document identity is path-based or logical.

### H08. Workspace folder/project switch [X]

Move/open files across Cargo/Lake workspace boundaries while an editor remains connected.

**Design impact:** tests server-pool routing and Lean’s lack of independent multi-workspace configuration inside one server.

### H09. LSP cancellation mapping to Anneal scheduler [S/X]

Trace editor cancellation through:

- projection;
- Lean queries;
- upstream regeneration tasks.

**Design impact:** avoids over-canceling shared work when one editor request is abandoned.

### H10. Incremental diagnostics presentation during regeneration [X/U]

When Rust changes invalidate the model, compare UI states:

- retain old diagnostics as stale;
- hide them;
- show “model rebuilding”;
- show proof-only diagnostics against old model with explicit generation.

**Design impact:** informs semantics of interactive partial information.

---

# I. Batch/interactive equivalence and verification semantics

### I01. Same proof, batch versus live server equivalence corpus [X]

For a matrix of valid/invalid proofs, compare:

- batch Lean;
- fresh live server;
- warmed live server;
- server after proof edits;
- server after dependency changes/restart.

Normalize only presentation differences whose irrelevance is justified.

**Design impact:** provides the regression oracle for interactive correctness.

### I02. Same generated model, batch versus live import environment [X]

Record exact imported artifacts/options/plugins in both modes.

**Design impact:** checks that “same source” actually means same proof environment.

### I03. Interactive success followed by clean verification [X]

Require every agent proof accepted interactively to pass a fresh batch verification of the same generation.

Classify mismatches.

**Design impact:** gives an end-to-end safety net during early interactive implementation.

### I04. Batch success followed by interactive query [X]

Open a freshly batch-verified generation and ensure the server reaches compatible goals/diagnostics without rebuilding shared immutable prerequisites unexpectedly.

**Design impact:** tests cold interactive startup.

### I05. Verification-result scope during live edits [S/X]

Define and test transitions among:

- verified generation G;
- current edited generation G+1 not yet rebuilt;
- G+1 Lean projection against stale model G;
- G+1 model prepared but proof incomplete;
- G+1 fully verified.

**Design impact:** determines which states can be surfaced without violating Anneal’s success semantics.

### I06. “No goals” versus theorem/file/project success [X]

Construct:

- solved local goal + error later in file;
- solved theorem + failing sibling theorem;
- solved proof + stale imported model;
- solved proof + admitted dependency;
- solved proof + unsupported upstream translation.

**Design impact:** formally prevents tactic state from being promoted into a verification result.

### I07. Trust/TCB identity under interactive reuse [S/X]

Change model libraries, toolchain, plugins, or trusted assumptions while proof text stays fixed.

Verify cached interactive results cannot survive a TCB-relevant environment change.

**Design impact:** integrates interactive state with the TCB audit model.

### I08. Incremental/development-mode taint [S/X]

If Anneal exposes stale-model proof editing or partial upstream regeneration for productivity, define explicit taint and test that it cannot be mistaken for ordinary success.

**Design impact:** aligns interactive UX with the design contract’s partial-information boundary.

---

# J. Parallel integration testing and resource scaling

### J01. Realistic 1/2/4/8/16/32-worker generated-project disk scaling [X]

Use the actual prepared Anneal toolchain and generated projects.

Measure:

- physical disk allocated;
- logical apparent size;
- inode count;
- per-workspace `.lake`;
- generated sources;
- build outputs;
- shared cache growth.

**Design impact:** tests whether V2 actually avoids V1’s disk amplification.

### J02. Identify every per-worker copied byte [X]

For a representative test, classify workspace files as:

- unavoidable mutable state;
- generated test state;
- copy that could be shared immutable state;
- accidental duplicate cache/build product.

**Design impact:** turns disk optimization into an ownership audit rather than another cloning workaround.

### J03. Concurrent Lean-server memory scaling with real Anneal imports [X]

Repeat 1/2/4/8/16 servers or independent workspaces using realistic Aeneas/Mathlib imports and proof files.

Measure peak RSS and, where possible, unique/private footprint.

**Design impact:** determines practical server-pool limits.

### J04. One server with many proof files versus many servers [X]

For one prepared environment, compare N open files in one watchdog against N independent servers.

**Design impact:** determines where process reuse actually saves memory.

### J05. Scratch-document pool scaling [X]

Measure memory/latency for 1/2/4/8/... prewarmed scratch documents used for agent tactic trials.

**Design impact:** sizes agent proof-search concurrency.

### J06. Nested parallelism budget [X]

Run many integration tests while allowing:

- Cargo jobs;
- Charon parallelism;
- Aeneas domains;
- Lake jobs;
- Lean workers;
- MCP scratch trials.

Measure oversubscription.

**Design impact:** informs a global scheduler/resource semaphore rather than independent stage-level parallelism.

### J07. Cold-start versus warm-start latency decomposition [X]

Measure:

- workspace construction;
- Charon;
- Aeneas;
- generated-module build;
- server launch;
- `setup-file`;
- first goal;
- subsequent proof edit/goal.

**Design impact:** identifies which long-lived resources are worth retaining.

### J08. Test-fixture sharing granularity [X]

Compare one workspace per test, one per fixture with many phases, and one per logical suite.

**Design impact:** informs replacement of heavyweight independent sandboxes where isolation is unnecessary.

### J09. Concurrency under failure/interruption [X]

Kill random workers during a high-parallel run.

Check:

- shared dependency immutability;
- cache integrity;
- orphan process cleanup;
- subsequent tests;
- disk leaks.

**Design impact:** tests whether the architecture remains simple under CI failures.

### J10. Long-running daemon resource drift [X]

Keep Lean/MCP/Anneal processes alive through hundreds or thousands of edits and generations.

Measure memory, file descriptors, temp files, process count, and cache growth.

**Design impact:** decides recycle policies.

### J11. Generation GC correctness [X]

Delete old generated workspaces/artifacts while unrelated workers and current generation remain live.

**Design impact:** establishes safe cleanup ownership.

### J12. Cross-test contamination sentinel [X]

Give each test a unique model definition or option whose accidental reuse is obvious.

Run heavily in parallel.

**Design impact:** detects incorrect environment/server pooling.

### J13. High-parallel cache miss storm [X]

Start many fresh consumers that all discover the same missing cache artifact.

Compare:

- shared cache writer behavior;
- serialized producer build;
- isolated build then publish.

**Design impact:** determines the correct cold-cache coordination mechanism.

### J14. Filesystem-specific scaling [X]

Where CI supports it, compare APFS, ext4, overlay/container filesystems, and networked/remote runners for cloning, hardlinks, reflinks, and shared read-only trees.

**Design impact:** avoids relying on a storage optimization unavailable on supported CI hosts.

### J15. Resource limits as correctness tests [X]

Run under deliberate low:

- disk;
- inode;
- memory;
- file-descriptor;
- process limits.

Verify clean failure rather than stale-success fallback.

**Design impact:** strengthens fail-closed behavior under resource exhaustion.

---

# K. Source/model provenance for interactive tooling

### K01. Exact user-proof source map independent of Charon spans [S/X]

Prototype a sidecar that stores exact Rust byte ranges for user-authored Lean before any compiler translation.

**Design impact:** avoids depending on Charon’s lossy display-column representation for proof edits.

### K02. Cross-layer declaration identity manifest [S/X]

Relate:

- compiler-resolved Rust item;
- Charon declaration;
- Aeneas pure declaration;
- generated Lean declaration;
- Anneal proof obligation.

Include one-to-many generated helpers.

**Design impact:** supports navigation and invalidation without path/name heuristics.

### K03. Provenance after macro expansion [S/X]

Test user annotations attached to macro-generated/transformed items and identify what exact source location can responsibly own diagnostics and edits.

**Design impact:** defines interactive limits around macros.

### K04. Generated scaffolding blame policy evaluation [X/U]

Create controlled failures in different synthetic constructs and compare candidate Rust-facing blame anchors.

**Design impact:** informs diagnostics without pretending synthetic text is directly editable source.

### K05. Path normalization and relocation in interactive diagnostics [X]

Move workspace/toolchain paths and compare diagnostics/navigation/source-map identity.

**Design impact:** prevents absolute generated paths from leaking into persistent handles.

### K06. Deleted source range while old query is in flight [X]

Delete or restructure the annotation owning a query position before the response arrives.

**Design impact:** validates stale-response rejection when no valid reverse mapping remains.

### K07. Source map under formatter/rustfmt changes [X]

Run rustfmt or otherwise reflow doc-comment indentation while preserving Lean content.

**Design impact:** tests whether content identity can preserve proof state across host formatting changes.

### K08. Provenance persistence across generated-model regeneration [X]

Regenerate Aeneas output while user proof text stays unchanged.

Ensure proof-source identity remains stable while environment generation changes.

**Design impact:** keeps authoring state independent from generated-model state.

---

# L. Backend API and implementation-boundary validation

### L01. Prototype structured stage result types [S/X]

Build a thin experimental API for Charon/Aeneas/Lake stages that returns:

- output identity;
- diagnostics;
- provenance;
- timing/resource metadata;
- cancellation/stale status.

Keep CLI rendering outside it.

**Design impact:** tests whether the proposed engine/backend separation fits real component behavior.

### L02. Filesystem side effects inventory per backend call [X]

Run each backend in an instrumented temporary environment and record every write.

**Design impact:** determines what must be staged/owned by Anneal versus hidden global state.

### L03. Progress reporting without backend-owned UI [S/X]

Capture structured progress from each stage or derive it safely.

**Design impact:** ensures future CLI/LSP/MCP adapters can share the engine without stage code depending on progress bars or stderr.

### L04. Backend cancellation abstraction fit [X]

Map one Anneal cancellation token to:

- child-process kill;
- process-group kill;
- Lean JSON-RPC cancellation;
- task cancellation.

**Design impact:** tests whether one logical interface is expressive enough without pretending all backends cancel identically.

### L05. Backend crash/restart state recovery [X]

Crash each backend and retry the same request.

Verify no hidden state is required for semantic correctness.

**Design impact:** validates replaceable process/library implementations.

### L06. Backend version/capability negotiation [S/X]

Prototype explicit capabilities such as:

- accepts unsaved source;
- supports concurrent requests;
- supports cancellation;
- deterministic output;
- requires filesystem materialization;
- supports persistent process;
- supports fine-grained invalidation.

**Design impact:** prevents the engine from assuming future backend capabilities prematurely.

### L07. Batch shell over the same engine [X]

Implement a minimal batch runner over the structured engine and compare against the current CLI behavior.

**Design impact:** confirms batch need not remain a separate pipeline.

### L08. Interactive shell over the same engine [X]

Implement a minimal in-process driver that repeatedly edits one proof and queries goals without an MCP/LSP transport.

**Design impact:** isolates engine correctness from protocol adapters.

### L09. Direct Lean backend versus external Lean-MCP bridge [S/X]

Compare Anneal speaking Lean LSP/RPC itself with delegating Lean-specific operations to an existing MCP bridge.

Evaluate state identity, cancellation, source projection, environment ownership, and observability.

**Design impact:** determines whether Lean MCP should be a dependency, inspiration, or irrelevant implementation detail.

### L10. Aeneas library embedding prototype [X]

If feasible on a capable surface, call the Aeneas library repeatedly in one host process and compare with the executable.

**Design impact:** informs whether subprocess isolation is merely convenient or currently necessary.

---

# M. Upgrade and revalidation strategy

### M01. Re-run all interactive invariants on Lean 4.31/current candidate [S/X]

Focus on:

- config-cache ownership;
- server workspace behavior;
- dependency refresh;
- goal versioning;
- server setup;
- cache artifacts.

**Design impact:** prevents V2 from encoding 4.30-specific workarounds unnecessarily.

### M02. Minimal interactive upgrade checklist [S]

Extract the small set of properties that must be revalidated whenever Lean/Lake changes.

**Design impact:** makes toolchain upgrades cheaper and safer.

### M03. Charon upgrade invalidation checklist for interactive mode [S/X]

Check:

- LLBC schema;
- source-span units;
- process/server behavior;
- deterministic output;
- translation subject identity.

**Design impact:** protects snapshot/cache assumptions across Charon upgrades.

### M04. Aeneas upgrade invalidation checklist for interactive mode [S/X]

Check:

- global mutable state;
- generated package layout;
- naming;
- source provenance;
- determinism;
- incremental/library APIs.

**Design impact:** protects generated-model and daemon assumptions.

### M05. Golden replay suite across toolchain tuple upgrades [X]

Take a small set of retained interactive transcripts and replay them on candidate toolchain tuples.

**Design impact:** catches protocol/invalidation drift before upgrading Anneal.

### M06. Detect obsolete Lake workarounds [S/X]

For every Anneal-side manifest/trace/mtime/rewrite workaround, maintain the exact upstream behavior that currently requires it and a probe for deletion.

**Design impact:** prevents V1-era cache complexity from becoming permanent folklore.

---

# N. Architectural falsification experiments

These should be treated as deliberate attempts to disprove the leading design.

### N01. Try to make path identity sufficient [X]

Construct the strongest plausible path-based cache scheme and find the smallest counterexample.

### N02. Try to make document version sufficient [X]

Attempt to key all interactive queries only by URI/version and use dependency mutations as adversarial controls.

Expected current evidence suggests this should fail; retain the minimal counterexample.

### N03. Try to avoid worker restart after imported changes [X]

Explore every supported refresh mechanism before adopting restart as the baseline.

If one is reliable, characterize its exact preconditions.

### N04. Try to share one Lean server across two independent Lake workspaces [X]

Use intentionally conflicting definitions/options/plugins so accidental success is impossible.

### N05. Try to share one writable generated build directory across consumers [X]

Stress and interrupt it.

Retain the negative result if unsafe.

### N06. Try to make the Lake artifact cache alone reconstruct the environment [X]

Start with only sources/control-plane minimum plus cache and identify every missing class.

### N07. Try to publish a generated generation by renaming a prepared directory [X]

Use relocation-sensitive metadata to find whether this is actually valid.

### N08. Try to use generated Lean as the canonical proof source [X]

Regenerate after user proof edits and demonstrate whether user state is preserved or lost.

### N09. Try to infer editable Rust ranges from Charon/Aeneas spans alone [X]

Use Unicode, macros, and generated scaffolding as adversarial cases.

### N10. Try to make proof-only edits always bypass upstream stages [X]

Find the boundary cases—especially import/configuration-affecting annotation edits—where this classification becomes false.

### N11. Try to use “no goals” as an agent success condition [X]

Create counterexamples involving stale imports, later file errors, admissions, and failed upstream coverage.

### N12. Try to make cancellation alone prevent stale state [X]

Force canceled tasks to complete late and demonstrate whether revision fencing remains necessary.

---

# O. Synthesis reports after the probes

These reports are worth writing only after enough component investigations above have execution evidence.

### O01. Anneal interactive state machine

Produce one explicit state machine covering:

- source snapshots;
- generated-model generations;
- prepared environments;
- open projected documents;
- Lean workers;
- verification states;
- stale/tainted states.

Include legal transitions and invariants.

### O02. Anneal invalidation matrix

For every relevant change class, record which stages are:

- unchanged;
- reusable;
- invalidated;
- rebuilt;
- restarted;
- reverified.

Base this on executed evidence, not architectural preference.

### O03. Anneal interactive identity model

Define all user-visible and internal identities:

- workspace;
- source snapshot;
- artifact subject;
- model generation;
- environment;
- document;
- worker;
- verification result.

State which are stable and which are ephemeral.

### O04. Anneal generated-source ownership and projection contract

Document:

- canonical user source;
- generated source;
- projected source;
- editable mappings;
- diagnostic responsibility mappings;
- persistence/regeneration rules.

### O05. Anneal prepared-toolchain producer/consumer contract

Specify what setup prepares once, what every consumer owns, what is read-only, what may be shared writable, and what operations must fail closed.

### O06. Anneal interactive proof-query contract

Specify what an answer to “goal at this Rust position” means, including snapshot/environment identity and stale-result behavior.

### O07. Anneal MCP semantic API

Describe MCP operations in terms of the engine’s explicit state model rather than Lean/Lake process details.

### O08. Anneal LSP semantic API

Describe how ordinary editor document lifecycle maps to the same engine and where virtual Lean documents are internal implementation state.

### O09. Anneal integration-test resource architecture

Specify the intended sharing/isolation model and measured scaling envelope for disk, memory, processes, and nested parallelism.

### O10. Batch/interactive equivalence contract

State which observations must agree between batch and live operation, which differences are intentional, and which clean-build or fresh-process oracle detects stale state.

---

## Suggested sequencing

A useful initial order is:

1. **A01, A03, C03, C04, F02, F07, I01** — establish the correctness boundary around stale interactive state.
2. **B01–B03, B15, K01** — establish exact user-proof projection.
3. **F04–F06, F13, J01–J06** — establish the real prepared-environment and scalability contract.
4. **G01, G05–G08, G12** — test the MCP state/agent loop over those established semantics.
5. **D08–D10, E01–E04** — sharpen the proof-only fast path and backend lifetimes.
6. **N01–N12** — actively attack the resulting design.
7. **O01–O10** — synthesize stable design documentation only after the empirical boundaries are known.

Several items can be combined when one harness answers them cleanly. In particular:

- C03/C04/C05/C07 can share a dependency-refresh harness.
- F02/F04/F06/F07/F08/F14/F16 can share a real-archive consumer harness.
- J01/J02/J06/J09/J13 can share a parallel integration-test harness.
- B02/B03/K01 can share a projection/coordinate harness.
- G05/G06/G13/G14 can share a concurrent MCP-agent harness.

## Success criterion for this backlog

The research is mature enough to freeze V2 scaffolding when we can answer, with pinned evidence:

1. What exactly identifies the source/model/environment against which an interactive result was computed?
2. How does Anneal prove that a result is current rather than stale?
3. Which edits can remain Lean-only, and which invalidate Charon/Aeneas/Lake state?
4. How are embedded Lean positions and edits mapped exactly back to canonical Rust-hosted source?
5. What shared state is immutable, what mutable state is per-consumer, and what may be shared writable?
6. What must restart when imported generated state changes?
7. How do batch and live checking cross-check one another?
8. How can many tests/agents run concurrently without duplicating the dependency universe or corrupting shared state?
9. Which handles/results are durable across process restart, and which must expire?
10. Which of these conclusions are properties of the current pinned versions versus architectural requirements Anneal should preserve across upgrades?

Until those questions have evidence-backed answers, implementation experiments should remain replaceable and should not silently turn a convenient current mechanism into an Anneal-wide semantic contract.
