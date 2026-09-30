# Reconciliation loops, event streams, and repairable watcher state

## Summary

A reliable reactive tool should separate **what wakes work up** from **what makes the resulting state true**. Kubernetes makes this separation explicit: controller events enqueue a key, but reconciliation is level-based and rereads current state rather than interpreting the event as the authoritative transition. Its client caches use an event stream for efficiency, but they are built around a recoverable snapshot-plus-version protocol: if watch history is unavailable, the client rebuilds from a fresh list. Linux inotify supplies the complementary local-filesystem lesson: events may be coalesced, its queue can overflow and lose events, and its own documentation recommends consistency checks and cache rebuilding.

For Anneal, these mechanisms support a narrower design than a Kubernetes-like control plane. File-system and protocol notifications should normally be **hints that mark a semantic scope dirty and trigger validation or reconciliation**. The reconciler should reread the authority appropriate to the operation—saved source, an editor document snapshot, imported artifact identity, or a canonical publication pointer—before deciding what work is needed. Duplicate hints may be coalesced. Uncertain gaps, watcher overflow, reconnects, or process reincarnation should force a scoped rescan rather than attempting to reconstruct truth from missing deltas.

This does not imply that every Anneal operation should be a perpetual controller or that every cache needs a durable event log. A single-user local tool can usually keep one canonical publication authority, use in-memory dirty queues and immutable generation artifacts, and perform explicit revalidation at session/open/reconnect/publication boundaries. Reconciliation repairs observation drift; it does not by itself resolve competing writers, prove semantic freshness, or make a side effect idempotent. Those obligations still require operation-specific identity, compare-before-publish/fencing, and safe staging.

## Applicability

This report answers issue #3732 J054: when to prefer declarative reconciliation over event-by-event synchronization, how to reason about lost and duplicate notifications, and what should transfer to Anneal without importing an unnecessary distributed control plane.

The Kubernetes subjects provide two related but distinct mechanisms. `controller-runtime` describes the **controller contract**: events enqueue reconciliation requests, identical requests can be deduplicated, and the reconciler compares actual state with desired state. `client-go`'s Reflector and the Kubernetes API documentation describe the **cache/feed contract** underneath many controllers: obtain or stream a coherent initial state, remember a resource version, consume subsequent changes, and recover by rebuilding when the remembered history is unavailable. KEP 3157 records a historical mechanism change—moving initial informer population toward a streaming watch-list for scale—while preserving the need for a consistency point and fallback repair.

Linux inotify is used as a local-filesystem counterexample to treating notifications as a durable event log. Its guarantees and failure modes are Linux-specific; this report does not claim that macOS FSEvents or Windows change notifications have identical semantics. The relevant transfer is narrower: a common production file-notification API explicitly allows coalescing and loss and tells robust cache users to detect inconsistency and rebuild.

The Anneal subjects identify current project authority and existing bounded evidence. At `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, `anneal/README.md` says the top-level implementation is the current redesign and `anneal/v1/` is historical. `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` require sound success claims, explicit trust, and compositionality while leaving many concrete mechanisms open. The current redesign does not yet expose a general watcher/controller architecture; the visible CLI in `anneal/src/main.rs` is still centered on setup. The reference report `anneal-3730-editor-save-format-watch-loop-2026-09-29` is a bounded experiment, not current architecture: it demonstrates that open-buffer state, disk state, watcher triggers, build success, and published artifact identity can diverge.

The derived Anneal recommendations therefore apply to the design of future interactive/watch-driven behavior. They do not describe a presently adopted Anneal controller implementation.

## Findings

### 1. Reconciliation makes the event a scheduling hint, not the truth

`controller-runtime` states the rule directly. Its `Reconciler` documentation says reconciliation is **level-based**: action is driven by actual cluster state read from the API server or a local cache, not by the contents of the individual event that triggered the call. A delete event does not need to carry a durable semantic transition; the reconciler discovers absence by reading state. The package overview likewise says controllers do not handle events directly. Events enqueue requests; multiple events can be batched or deduplicated; the reconciler reads full state for the object and tries to make actual state match specified state.

Basis: documentation + source.

This changes which failures are correctness failures. If two update events collapse into one queue entry, a level-based reconciler can still converge because the one execution reads the latest state. A duplicated event can cause an extra execution without changing the intended result. By contrast, an event-by-event state machine that applies `+1`, `delete`, or `rename` deltas to a private model can become permanently wrong if one event is lost, duplicated, or interpreted after a restart without the preceding history.

The important precondition is that the reconciler can reread a state source that is more authoritative than the trigger stream. Reconciliation is not magic if the “current state” read is itself an unvalidated stale cache. Kubernetes therefore pairs level-based controller logic with cache protocols that have explicit snapshot and version semantics.

Derived Anneal implication: most file-watch or external-change notifications should identify **what might need another look**, not carry the proof that a source/model/artifact transition occurred. A notification can enqueue a file, crate, obligation family, workspace, or imported environment for reconsideration. The subsequent operation should reread the relevant authority and derive work from that state.

### 2. Efficient event-driven caches need a repair path

Kubernetes does not reject event-driven caching. It makes the cache recoverable.

The Kubernetes API documentation says watch history is finite. When a requested resource version is no longer available, a server can return `410 Gone`; clients must tolerate that case by clearing their local cache, obtaining a fresh `GET` or `LIST`, and starting a new watch from the returned resource version. The standard Go-client abstraction for this pattern is Reflector.

Current Reflector source embodies the same rule. It records `lastSyncResourceVersion`, watches forward from that version, and detects expired or otherwise unavailable versions. Its `list` path explicitly retries from a reset resource version when the previous version is expired or too large, then replaces the store contents with the returned list. The newer `watchList` path streams a consistent initial snapshot into a temporary store, waits for a bookmark establishing the snapshot boundary, replaces the live store, and then reuses the same stream for later events. On an unusable remembered version it resets and reconstructs a fresh snapshot.

Basis: normative API documentation + source.

This is a useful hybrid: **snapshot for truth, stream for latency, version for continuity, rebuild for repair**. The stream can remain the common fast path without being the only way to know what exists.

For Anneal, the analogous pattern does not require a Kubernetes API server. A file-backed or generated-artifact cache can use a much smaller protocol:

1. Establish a coherent basis for the operation: for example, enumerate relevant source files and record their identities, or load the explicit project/model manifest.
2. Compute/cache derived state from that basis.
3. Use file watcher, editor, RPC, or subprocess notifications to mark a scope dirty and wake recomputation quickly.
4. Before a result becomes authoritative, compare the operation's recorded basis with the current basis that matters for that result.
5. If the notification channel reports overflow, reconnects, restarts, or otherwise loses continuity, discard any assumption that every transition was observed and perform a scoped rescan.

The word “scoped” matters. A missing watcher event for one source subtree does not justify rebuilding every independent proof in every workspace if Anneal has a dependency model that identifies the affected closure. Reconciliation defines a correctness path; the dependency graph defines how much must be rechecked.

### 3. Kubernetes changed the transport without abandoning the consistency boundary

KEP 3157 provides a useful historical check against cargo-culting one particular list/watch implementation. It was proposed in 2022, became alpha in Kubernetes 1.27, beta in 1.32, and records general availability in 1.38. Its motivation is largely performance: traditional initial LIST requests can create very high temporary memory use on the API server. The KEP uses the existing watch stream to send initial objects, but adds an explicit consistency target and bookmark so the client knows when the initial snapshot is complete. It also specifies fallback to regular list/watch behavior when the feature is unavailable or fails.

Basis: design history + current source.

The stable idea is therefore not “always perform an HTTP LIST before watching.” The stable idea is that a cache must know **which coherent state it has established**, **how subsequent events extend that state**, and **how to recover when continuity cannot be proven**. Kubernetes was able to change the mechanism for building the initial snapshot because those semantic obligations remained explicit.

Derived Anneal implication: Anneal should specify its freshness/recovery obligations separately from any first implementation. A future implementation might use polling, OS file notifications, editor protocol notifications, a daemon-held dependency graph, or a content-addressed manifest. If each mechanism can establish the same operation-specific current basis and recovery rule, Anneal can change implementations without changing the user-facing verification claim.

### 4. Linux inotify is explicitly not a reliable event log

Linux `inotify(7)` documents three details that matter for a watch-driven local tool.

First, successive identical unread events may be coalesced into one event. The manual explicitly says applications cannot use inotify to reliably count filesystem events. Second, the event queue can overflow; events are then lost, and robust applications may need to rebuild part or all of their cache. Third, adding a watch to a newly created directory races with changes beneath that directory; files may already exist before the recursive watch is installed, so the manual recommends scanning after adding the watch. More generally, the manual advises cache users to perform consistency checking and rebuild when inconsistency is detected.

Basis: documentation for Linux man-pages 6.19.

These are not obscure corner cases layered on top of an otherwise durable log. They define the API category. A file watcher can efficiently tell a process that something changed, but it cannot universally prove that the process observed every mutation needed to replay filesystem history.

Derived Anneal implication: a file notification such as “`foo.rs` changed” should normally wake source-identity validation. It should not be treated as evidence that Anneal saw the only change, saw every intermediate content, or can safely update semantic state by replaying the event. If the current result depends only on current file contents, rereading the file is both simpler and stronger than trying to reconstruct its edit history. If intermediate transitions themselves matter—for audit, user intent, or transactional semantics—Anneal needs an event source with a stronger contract than a normal filesystem watcher.

### 5. Duplicate suppression is an optimization only when work is level-based

`controller-runtime` explicitly deduplicates identical reconcile requests. This is safe because the request names the object to reconcile rather than encoding a unique state transition that must be applied exactly once. The reconciler then performs a full current-state comparison.

Basis: source + documentation.

Anneal can exploit the same distinction. Suppose a user saves a Rust file three times while an older proof job is still running. A dirty-set queue can collapse all three “reconsider module X” hints into one pending key if the next job rereads the current authorized source/model basis. It must **not** collapse three semantically distinct commands if the commands themselves are the authority—for example, three explicit user actions that each produce a separately named artifact or three transactional edits whose intermediate ordering is part of the requested behavior.

This gives a practical rule: coalesce **invalidation notifications**, not **authoritative mutations**. The former say a cached conclusion may need repair. The latter require their own transactional semantics.

### 6. Reconciliation repairs drift; it does not solve writer authority

A control loop can repeatedly make actual state approach desired state, but that says nothing by itself about who is allowed to define desired state. Two controllers that are both authorized to impose incompatible values can oscillate forever. Kubernetes has additional ownership, API-server concurrency, and resource-version machinery; the reconciliation pattern is only one layer.

Basis: derived from the separation between controller-runtime reconciliation and Kubernetes API resource-version semantics.

Anneal therefore should not use “eventual reconciliation” as a substitute for a publication protocol. If two workers can publish the canonical proof family, report a model current, or update a shared source-derived pointer, one authority must serialize that transition or each write must carry a compare-before-write/fencing precondition. A later reconciliation pass can detect drift, but it cannot retroactively make an unauthorized or stale publication safe.

J051 and J052 own the deeper optimistic-transaction and fencing analysis. The J054-specific conclusion is only that the reconciliation loop should consume **current authorized state**, not arbitrate authority implicitly through last-writer-wins behavior.

### 7. Idempotence should mean convergent repair, not “repeat every side effect blindly”

Declarative controllers work best when repeated reconciliation is harmless or convergent: compare desired with observed state and perform only the missing transition. That does not require every low-level action to be intrinsically idempotent. A controller can make a non-idempotent external call safe by first observing whether the desired object already exists, by attaching a stable request identity, or by staging private work and publishing a pointer only once.

Basis: derived from the controller contract and Anneal's current artifact/publication concerns.

For Anneal, expensive compiler/prover runs can remain ordinary jobs. The repair loop can key a job by its semantic inputs and avoid launching it when a valid result for the same basis already exists. A retry can write to a private generation. Only verified output should become canonical, and publication should be an explicit state transition with a current-basis precondition. This gives retryability without requiring a prover invocation itself to be transactional.

### 8. The authority to reread depends on the operation

“Reread current state” is not synonymous with “read the filesystem.” The existing Anneal save/format/watch-loop reference experiment shows a live Lean server continuing to diagnose an unsaved/open version while disk had been externally overwritten and successfully compiled. Closing and reopening reconciled the LSP view with disk. The same experiment showed duplicate disk events being suppressed, failed or killed builds leaving the consumed artifact pointer unchanged, and a later successful build updating that pointer.

Basis: execution evidence already published in the reference branch.

The lesson is that Anneal needs an operation-specific authority model:

- An editor diagnostic may legitimately be about the editor's versioned in-memory document, even when disk differs.
- A batch verification command may legitimately use the saved project snapshot or an explicitly supplied source snapshot.
- A generated artifact should be associated with the exact source/model/environment basis from which it was built, not whichever bytes happen to be on disk when the artifact is later consumed.
- A canonical “current artifact” pointer is a publication state of its own and should not move merely because a watcher fired.

A reconciliation loop must therefore ask “current according to which authority for this operation?” before it decides that two states disagree.

### 9. Event-by-event synchronization is still appropriate under a stronger source contract

Level-based reconciliation is not universally superior. Applying a stream of deltas can be the right design when all of the following hold:

- the event producer is authoritative for the state being modeled;
- events are ordered within the scope that matters;
- the consumer has a durable or otherwise reliable cursor/version;
- gaps are detectable;
- history can be replayed far enough to close a detected gap, or a snapshot replacement exists;
- each event carries enough information to apply the intended transition unambiguously.

Basis: derived comparison using Kubernetes watch/resource-version semantics and inotify's documented counterexample.

Kubernetes itself uses this hybrid: versioned watch events efficiently extend a cache, but a finite history window means the client must sometimes replace the cache from a snapshot. Inotify lacks the stronger replay contract, so a filesystem cache must be prepared to rescan instead.

For Anneal, an ordered versioned editor session can sometimes support incremental document updates more strongly than a raw filesystem watcher. But the session still needs a reset boundary: on reconnect, process replacement, or version discontinuity, the receiver must reacquire a complete document/project basis rather than assuming continuity from an old process incarnation. A normal watcher should remain a wake-up hint unless Anneal deliberately builds and specifies a stronger replay protocol.

### 10. A small local repair architecture is sufficient for the current problem

J054 explicitly asks not to import a distributed control plane merely because several processes communicate. The evidence supports a compact local design:

**Authoritative state.** Keep explicit current identities for the inputs and published artifacts that affect a verification claim. These may be source snapshots, model/import identities, toolchain/environment identities, and canonical artifact pointers.

**Dirty triggers.** Convert watcher, editor, process, or RPC notifications into bounded “scope X may have changed” work. Coalesce duplicate dirty keys freely when the reconciliation step rereads the current basis.

**Reconciliation.** For a dirty scope, read the operation's authoritative current state, compare it with the state underlying cached/generated results, and schedule only missing or invalid work.

**Private preparation.** Build or verify into a private generation. Failure, cancellation, or duplicate execution does not disturb the current published generation.

**Checked publication.** Before making a result current, validate that the semantic basis and publication authority still match. Then move a single canonical pointer/ref using a compare-before-write or fenced transition.

**Repair boundaries.** A watcher overflow, protocol reconnect, daemon restart, unexplained version gap, or corruption signal invalidates continuity assumptions and triggers a scoped full reconciliation. An explicit user “rescan/rebuild” operation should provide the same recovery path.

**No unnecessary durable event bus.** Nothing in the evidence requires Anneal to retain every local filesystem notification, run a consensus system, model every file as a Kubernetes resource, or maintain desired/observed state in an external database. The durable things should be the facts needed for verification provenance and safe publication, not the transient wake-up stream.

Basis: derived synthesis.

### 11. The strongest safety property is convergence to a fresh rescan, not perfect event delivery

For a local watch-driven workflow, a useful testable invariant is:

> After notifications quiesce, or after continuity is explicitly declared uncertain, the state that Anneal treats as current should converge to the state that a fresh authoritative rescan/reload would produce for the same operation basis.

Basis: derived synthesis from Kubernetes snapshot/watch repair and inotify cache-rebuild guidance.

This invariant tolerates harmless duplicate/coalesced notifications and makes missed-event recovery testable. It also exposes where more than convergence is required. If a particular operation promises to preserve every user command or every intermediate state, then a current-state rescan is insufficient and that operation needs a transactional/event-log contract. Anneal should make that stronger contract local to the operation that needs it rather than imposing it on every watcher-driven cache.

## Boundaries

**No Anneal controller implementation was examined because the current redesign does not yet present one as an adopted architecture.** The report derives requirements for future interactive/watch-driven behavior from current principles/design authority plus external mechanisms and existing reference evidence.

**No new execution was performed.** Kubernetes, Linux inotify, and Anneal were not run for this report. Kubernetes claims come from pinned current source/design/documentation; inotify claims come from Linux man-pages 6.19; Anneal behavioral evidence is the already-published bounded watch-loop experiment.

**Linux-specific watcher details do not automatically generalize to macOS or Windows.** The report uses inotify to refute the universal assumption that filesystem notifications form a lossless replay log. A production cross-platform Anneal watcher still needs platform-specific analysis and probes.

**Kubernetes cache consistency is not Anneal's required consistency model.** Kubernetes resource versions, API-server watches, informers, and controller queues solve a multi-node API-control-plane problem. Anneal can transfer the snapshot/continuity/repair distinctions without reproducing those mechanisms.

**Reconciliation does not prove semantic correctness.** A loop can faithfully converge to a wrong desired state or recompute from an incorrectly identified model. Anneal still needs Rust/model/proposition correctness arguments and backend verification according to its current design contract.

**Reconciliation does not solve authority or transactionality.** Competing writers, stale query-derived edits, and worker reincarnation need compare-and-swap/fencing/identity rules. J051 and J052 analyze those mechanisms more directly.

**Periodic polling is not required.** Kubernetes often has persistent controllers because cluster state changes independently and indefinitely. Anneal may be able to reconcile only on hints plus explicit lifecycle boundaries such as open, reconnect, command start, and pre-publication validation. The appropriate cadence is a performance/liveness decision, not established here.

**Transition history can matter.** The recommendation to reread current state applies when the desired result is a function of current authoritative state. Audit trails, ordered user commands, and other history-sensitive operations need a stronger event/transaction source and should not be collapsed into a level-based cache.

**The existing Anneal watch-loop reference report is deliberately narrow.** Its Python hash poll is not a production OS watcher; it did not test missed/coalesced OS notifications, multi-client editor ownership, or the future Anneal pipeline. It is evidence for state distinctions, not proof of a complete watcher design.

## Evidence

### Kubernetes controller contract

- Repository: `kubernetes-sigs/controller-runtime`
- Revision: `8564dc352deed83f3dfcd5c5e47d1fed6c6dd28b`
- `pkg/reconcile/reconcile.go`, around lines 102-119: reconciliation is level-based, reads actual cluster state, and workqueue requests are deduplicated.
- `pkg/doc.go`, around lines 38-50 and 184-205: controllers enqueue requests rather than handle event contents directly; multiple events can batch; reconciliation rereads state.
- Immutable source URL: `https://github.com/kubernetes-sigs/controller-runtime/blob/8564dc352deed83f3dfcd5c5e47d1fed6c6dd28b/pkg/reconcile/reconcile.go`

Evidence role: documentation + source.

### Kubernetes API and cache repair

- Repository: `kubernetes/website`
- Revision: `367a7a21bbef6b2d3c57d5fe113bee9bdb658889`
- `content/en/docs/reference/using-api/api-concepts.md`, around the watch/resource-version section near source line 456: watch history is finite; `410 Gone` requires clearing local cache, relisting, and restarting watch from the returned resource version.
- `content/en/docs/concepts/architecture/controller.md`, desired-versus-current-state section: controllers move current state toward desired state.
- Immutable API concepts URL: `https://github.com/kubernetes/website/blob/367a7a21bbef6b2d3c57d5fe113bee9bdb658889/content/en/docs/reference/using-api/api-concepts.md`

Evidence role: normative-style project API documentation + documentation.

### Kubernetes Reflector implementation

- Repository: `kubernetes/kubernetes`
- Revision: `6d1d025050cb63ae5b8e53037aced205e6a28410`
- Path: `staging/src/k8s.io/client-go/tools/cache/reflector.go`
- Relevant regions: `watch`, `list`, `watchList`, `syncWith`, and resource-version recovery logic. The inspected current source retries/backs off watch failures, recognizes expired/unavailable versions, can reset the remembered version, replaces the store from a list/snapshot, and uses a temporary store plus bookmark to establish the initial `watchList` state.
- Immutable source URL: `https://github.com/kubernetes/kubernetes/blob/6d1d025050cb63ae5b8e53037aced205e6a28410/staging/src/k8s.io/client-go/tools/cache/reflector.go`

Evidence role: source.

### WatchList design history

- Repository: `kubernetes/enhancements`
- Revision: `914ed6950576832c8579899f092909d27623492e`
- Path: `keps/sig-api-machinery/3157-watch-list/README.md`
- The KEP describes a consistent initial snapshot carried over WATCH, a resource-version/bookmark boundary, fallback to ListAndWatch, and the risk of “going back in time” when a stale watch cache initializes a client. Its implementation history records proposal on 2022-01-14, alpha in v1.27, beta in v1.32, and GA in v1.38.
- Immutable source URL: `https://github.com/kubernetes/enhancements/blob/914ed6950576832c8579899f092909d27623492e/keps/sig-api-machinery/3157-watch-list/README.md`

Evidence role: design history + documentation.

### Linux file-notification failure behavior

- Linux man-pages 6.19, `inotify(7)`, dated 2026-02-14; HTML obtained from the 6.19 tarball according to the page colophon.
- URL: `https://www.man7.org/linux/man-pages/man7/inotify.7.html`
- Relevant sections: general cache-consistency advice; event coalescing; queue overflow; recursive-watch race notes. The page says identical unread events can coalesce, queue overflow loses events, and robust applications may need to rebuild cache state.

Evidence role: platform documentation.

Identity limitation: the observed HTML page is identified by the stated man-pages 6.19 release rather than an immutable Git object. Future revalidation should compare the corresponding release source or a newer man-pages release if stronger pinning is required.

### Historical context for declarative cluster management

- Brendan Burns, Brian Grant, David Oppenheimer, Eric Brewer, John Wilkes, “Borg, Omega, and Kubernetes,” ACM Queue 14 (2016), pp. 70-93.
- Google Research record: `https://research.google.com/pubs/pub44843.html`
- The publication is used only as historical context that Kubernetes was developed in the lineage of prior Google cluster-management systems and distilled lessons from them. The concrete J054 mechanism claims come from the pinned Kubernetes controller/watch sources above.

Evidence role: literature/history.

### Anneal authority and current implementation status

- Repository: `google/zerocopy`
- Revision: `cc135f46155b72e4b51188525c2974a3b84acf92`
- `anneal/PRINCIPLES.md`: correctness and justified success claims are non-negotiable; support programmers first; preserve promises; explicit trust.
- `anneal/DESIGN.md`: current durable contract and explicit mechanism non-decisions.
- `anneal/README.md`: top-level implementation is the current redesign; `anneal/v1/` is historical.
- `anneal/src/main.rs`: current visible CLI surface remains small and does not establish a watcher/controller architecture.

Evidence role: normative project design + source/documentation.

### Existing Anneal watch-loop experiment

- Repository: `google/zerocopy`, `reference` branch observed at `2cec790eeec883e83ac66dcfa021c51ad65ad4f1`.
- Package: `reports/anneal-3730-editor-save-format-watch-loop-2026-09-29/`
- `REPORT.md` blob: `ca2c4e0f92eb9432002b240a986073417a177b48`
- The preserved experiment demonstrates an open Lean document diverging from disk, successful disk compilation while the old open buffer still reports diagnostics, duplicate event suppression in the harness, failure/cancellation leaving a consumed-artifact pointer unchanged, and later successful publication changing that pointer.

Evidence role: execution evidence from an existing reference report + derived interpretation.

## Revalidation

For Kubernetes controller semantics, diff these exact regions against the newer subject: `controller-runtime/pkg/reconcile/reconcile.go`, `controller-runtime/pkg/doc.go`, and client-go `tools/cache/reflector.go`. The discriminating questions are whether reconciliation is still level-based, whether events still primarily enqueue keys rather than carry authoritative deltas, and whether cache continuity failure still has a snapshot/relist repair path.

For Kubernetes watch semantics, check the current API concepts documentation for resource-version expiry/recovery and KEP 3157 or its successor for any change to the consistency/bookmark/fallback contract. A transport optimization that still establishes a coherent snapshot and recoverable cursor does not invalidate this report's core distinction.

For Linux watcher semantics, check the current `inotify(7)` release for event coalescing, `IN_Q_OVERFLOW`, recursive-watch races, and the cache-rebuild guidance. If Anneal targets macOS or Windows watchers directly, add separate reports or support evidence for those APIs rather than assuming Linux details.

For Anneal, first check whether `anneal/DESIGN.md` has adopted a watcher/controller/cache authority model since revision `cc135f46155b72e4b51188525c2974a3b84acf92`. Then inspect any new implementation for four properties: (1) events identify dirty scope rather than silently becoming semantic truth; (2) every cache has a current-basis identity and a repair path; (3) reconnect/overflow/restart forces resynchronization when continuity cannot be established; and (4) canonical publication has an authority/freshness precondition independent of the watcher.

A high-value future execution probe should deliberately inject duplicate notifications, suppress one notification, trigger watcher overflow or simulate it, perform rename/replace saves, restart the watcher between changes, create an A→B→A content cycle, and create an editor-buffer/disk split. After each fault, compare Anneal's eventual “current” state with a clean process that performs a fresh authoritative rescan. The test should separately verify that stale or failed private generations never move the canonical artifact pointer. Passing such a probe would validate the recovery property for the exercised implementation; it would not prove all platform watchers or all semantic dependency discovery correct.