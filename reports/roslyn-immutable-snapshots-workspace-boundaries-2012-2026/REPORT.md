# Roslyn immutable snapshots: what they simplify, and what they leave mutable

## Summary

Roslyn's useful architectural unit is not an immutable process or an immutable IDE. It is an immutable *semantic snapshot* embedded in a mutable host.

The original Roslyn API design made syntax trees, compilations, and solution models stable values. A consumer can retain one such value and know that later edits will not change what that value means. Structural sharing and lazy realization make this practical: a new snapshot can reuse most old representation, while semantic work and caches are populated on demand. The mutable `Workspace` remains responsible for tracking which snapshot is current, serializing host-driven updates, applying edits, raising events, and supplying host services.

The later out-of-process architecture makes the boundary even sharper. A `Solution` object cannot simply be treated as shared state across processes. Roslyn assigns a checksum to a solution state, synchronizes changed subtrees through a typed Merkle structure, pins snapshots while requests use them, retains hot assets in mutable caches, and purges old data. These mechanisms are part of the cost of preserving snapshot semantics across a process boundary. They are not evidence that the whole system became immutable.

A second limit is more important for Anneal: an internally coherent snapshot is not automatically the right snapshot of the external world. Roslyn's Edit-and-Continue code explicitly handles cases where the design-time workspace snapshot differs from the source that produced the running binary, because the build and workspace lack a reliable synchronization edge. It checks PDB/source checksums and tracks out-of-sync state rather than treating snapshot immutability as freshness proof.

For Anneal, the transferable rule is therefore conditional: use immutable, identity-bearing snapshots for the inputs whose stable meaning a verification operation needs, and keep mutable ownership, cache lifetime, process state, editor state, and publication outside that value. The smallest likely useful snapshot is a versioned verification-input/environment description plus identities of the artifacts that determine the result, not a universal clone of every subsystem. Cross-process use should carry explicit content/version identity and lifetime. None of this makes one snapshot the authority for whether upstream source, build outputs, tool configuration, or published results are current; those relationships need explicit synchronization and validation.

Basis: historical design account + current documentation + current source + historical source change + derived Anneal comparison.

## Applicability

The Roslyn findings apply to the public design and implementation represented by `dotnet/roslyn` revision `7ec1fa8b6d8a43c88bca0dbb376090d219ebc43b`, interpreted with two historical anchors: the repository's original imported `Roslyn-Overview.md` at `4a74095f0e3598e514f3147479beee208c0ad7ed`, and the commit `c141605a972871644cc43f2caec597c88e9662db` that introduced the early RemoteWorkspace/ServiceHub machinery. Eric Lippert's 2012-06-08 red/green-tree article is used as a contemporary author account of the syntax-tree rationale; it is a dated web publication rather than an immutable repository artifact.

The Anneal transfer analysis is derived against `google/zerocopy` revision `cc135f46155b72e4b51188525c2974a3b84acf92`, especially `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`. Those files require successful verification to have precise identity and scope, make the TCB explicit, and prefer general, minimally sufficient mechanisms, but deliberately do not choose the atomic verification subject or architecture. The judgments below are therefore research conclusions, not adopted Anneal design policy.

Roslyn and Anneal have materially different workloads. Roslyn serves a large, continuously changing IDE solution and many concurrent language-service requests. Anneal may be able to satisfy its first workflows with much smaller snapshots, fewer retained versions, and simpler process boundaries. This report transfers invariants and failure modes, not Roslyn's subsystem count or vocabulary.

## Findings

### 1. Immutability was chosen to make a compiler model usable as a long-lived service value

Roslyn's early overview describes the compiler as a platform rather than a batch-only black box. Its compiler layer exposes a single compiler invocation as an immutable snapshot containing source files, references, and options; syntax trees are immutable and thread-safe snapshots; compilations can be forked by small changes; and a `Solution` obtained from `Workspace.CurrentSolution` never changes. A changed solution is a new value that must be explicitly applied back to the workspace.

That distinction solves a specific concurrency and reasoning problem. A consumer can hold a syntax tree, compilation, project, document, or solution and reason about that value without a concurrent keystroke changing its meaning. The host can still advance to a new current state.

The design did not require copying the world on each edit. Lippert's contemporary explanation describes the syntax representation as a persistent green tree with no parents or absolute positions plus a red facade that supplies navigation context on demand. The absence of contextual fields lets unchanged green nodes survive edits even when their absolute positions move. Current Roslyn documentation still describes this red/green structure and subtree sharing.

This history supports a narrower claim than "immutability is simpler": immutable semantic values are attractive when many readers need stable views while a producer continues to advance the live world. Roslyn paid representation complexity to make that abstraction efficient.

Basis: documentation + historical author account + current source.

### 2. Roslyn's public immutability is semantic, not physical

Current source is explicit that a `Compilation` is immutable *and* on-demand: it realizes and caches data as necessary, and a derived compilation can reuse information from its predecessor. The current `Solution` implementation likewise contains lazily populated dictionaries and `AsyncLazy` caches. `SolutionCompilationState` contains compilation trackers, generator-driver caches, weak tables, and a lazily computed checksum. Some of those fields are updated or populated internally even though the public snapshot's semantic contents do not change.

This is an important cost model. Roslyn protects the proposition "this snapshot denotes the same program/configuration" rather than the stronger proposition "no memory reachable from this object ever mutates." The latter would forbid useful memoization and would make large semantic models unnecessarily expensive. The implementation instead confines mutation so that it changes performance and reachability, not the logical answer associated with the snapshot.

The pattern also means snapshot retention has nontrivial consequences. Holding an old `Solution` can keep structurally shared states and lazily realized semantic objects reachable; producing a new value is cheap partly because old and new values share structure. "Cheap fork" and "cheap indefinite retention" are different claims.

For Anneal, this argues against making purity of cache implementation an architectural objective. The relevant correctness boundary is that a verification-input snapshot has stable semantic identity and that memoized state is keyed and invalidated so it cannot change what that identity means.

Basis: source + derived comparison.

### 3. The mutable workspace is the authority for "current," and it serializes mutation

`Workspace` documents its `CurrentSolution` as an immutable snapshot, but `CurrentSolution` itself may change as the environment changes or `TryApplyChanges` succeeds. Current source maintains `_latestSolution` as mutable state, uses a semaphore to serialize host mutation calls, protects other mutable fields with a lock, and raises ordered change events after updates.

This division of responsibility is more informative than the slogan "Roslyn uses immutable solutions." The immutable `Solution` is a value. The mutable `Workspace` answers a different question: which value currently represents the host environment, and how does the system move from one value to the next?

Collapsing those responsibilities would lose useful semantics. If the solution object itself mutated, old readers could not retain a stable view. If the whole workspace were represented only as persistent values with no current-state authority, the system would still need some external pointer, event source, or transaction mechanism to decide which snapshot editors and services should use. Roslyn makes that mutable ownership explicit.

Anneal has the same conceptual split even if its first implementation is much smaller. A stable description of a verification attempt should not itself be the mechanism that decides which editor buffer is latest, whether a build has completed, whether a cache entry can be evicted, or which result is published. Those are ownership and lifecycle transitions around the snapshot.

Basis: source + derived comparison.

### 4. Crossing a process boundary turns snapshot identity into a synchronization protocol

Roslyn's out-of-process history shows that immutable in-process objects do not eliminate distributed-state problems. The early OOP integration commit added solution checksums, serialization, a remote host client, `RemoteWorkspace`, and ServiceHub plumbing. The current architecture uses a typed checksum/Merkle tree for solution state. Requests identify the desired snapshot by checksum; the remote process compares checksum subtrees and fetches only changed assets.

Current OOP code then adds lifetime machinery. The host pins the assets for an operation's snapshot. The remote workspace maintains reference-counted in-flight computations by solution checksum so concurrent requests can share one reconstruction. A mutable `SolutionAssetCache` retains recently used assets and periodically purges unpinned ones. `RemoteWorkspaceManager` currently configures a 30-second cleanup interval and a one-minute unused-asset purge window while exempting current and in-flight solutions.

These details show three distinct identities that are easy to conflate:

1. the logical immutable solution snapshot;
2. the serialized/content identity used to reconstruct that snapshot elsewhere; and
3. the mutable lifetime of concrete objects and cached bytes that implement it.

A process boundary therefore does not merely require "serialize the immutable value." It requires an identity scheme, transfer protocol, pinning rules, cancellation behavior, cache retention, and a decision about which snapshot a request names. Roslyn's Merkle machinery is one implementation optimized for large incremental solutions; the general requirement is explicit identity plus lifecycle, not necessarily a Merkle tree.

For Anneal, a subprocess or future remote service should receive an explicit version/content identity for the source/configuration/artifacts it is asked to analyze. If the needed inputs are small, a simple manifest plus immutable artifact digests may be sufficient. If repeated large snapshots dominate cost, structural checksums and differential transfer become an option rather than a prerequisite.

Basis: historical source change + documentation + source + derived comparison.

### 5. An immutable snapshot can still be stale with respect to the fact that matters

Roslyn's Edit-and-Continue implementation records a concrete failure mode. At debugging start it captures the current solution snapshot, but that snapshot may differ from the source actually used to build the module in the debuggee. The source comment attributes this to the lack of reliable synchronization between the design-time build and the Roslyn workspace; file-change notifications may arrive after the debugger has attached and the snapshot has been captured.

Roslyn does not resolve this by asserting that `CurrentSolution` is authoritative. It compares current source with checksums in the PDB, records documents as out-of-sync or indeterminate when necessary, and only treats a document as matching build output when the evidence supports it.

This is the strongest caution for Anneal. Snapshot immutability answers "can this value change under me?" It does not answer "does this value correspond to the build, generated translation, Lean environment, editor buffer, or publication that the user thinks I am checking?" Those are cross-system correspondence claims.

Anneal's current design contract already requires a successful result to identify the program or behavior to which it applies and forbids silently strengthening evidence. Roslyn suggests a concrete implementation discipline: treat missing synchronization as a state to detect and report, and use content/version evidence at boundaries rather than assuming that two subsystems' notions of "current" coincide.

Basis: source + Anneal design contract + derived comparison.

### 6. Persistence and host services remain outside the immutable model

Current Roslyn source contains mutable persistent-storage machinery used across runtime sessions, including a lock-protected current database and recovery that may delete and recreate a corrupted database. At the same time, the old public `IPersistentStorageService` API is now obsolete with the explicit statement that Roslyn no longer exports arbitrary persistence and consumers needing it must provide their own semantics.

This reinforces the boundary: the immutable solution model is not a universal container for every optimization or durable fact. Persistence has its own failure, versioning, ownership, and recovery semantics. Roslyn can associate cached data with solution/project/document identities without pretending the cache itself is part of the immutable semantic snapshot.

For Anneal, proof environments and translated artifacts may deserve durable identities, but cache directories, process-local memoization, worker pools, and eviction policy should normally remain implementation state. If a cached artifact is necessary evidence for a successful result, its content identity and provenance belong in the result's dependency/evidence graph; the mutable cache entry holding the bytes does not.

Basis: source + derived comparison.

### 7. The serious alternatives clarify what Roslyn's pattern actually buys

A single mutable object graph is simpler at first. It can avoid persistent-value APIs and explicit snapshot construction. Its cost appears when long-running or concurrent operations need a stable historical view: readers need locks, copies, restart-on-change behavior, or acceptance of mixed-version observations. For an interactive analysis system, that is exactly the pressure Roslyn's snapshots address.

A physically immutable whole system goes too far in the other direction. It would make caches, current-state pointers, lifecycle counters, remote asset retention, and host integration awkward or expensive without strengthening the semantic guarantee users need. Roslyn's implementation demonstrates that logical immutability composes with carefully scoped internal mutation.

A universal solution snapshot that purports to include every external fact is also insufficient. Roslyn's build/workspace mismatch shows why: an external process can produce a different artifact even while each internal snapshot is perfectly immutable. Making the snapshot larger moves the boundary; it does not remove the need to justify correspondence across the remaining boundary.

The competitive architecture for Anneal is therefore not "Roslyn-style immutable world" versus "mutable world." It is a smaller design in which authoritative mutable hosts produce explicit immutable verification-input values, operations name those values, and durable results identify the exact inputs/evidence they cover. Structural sharing, remote Merkle synchronization, and aggressive multi-version retention should be added only where measured workload justifies them.

Basis: derived comparison from the preceding evidence.

### 8. Conditional Anneal judgment

Anneal should adopt the *semantic split* Roslyn demonstrates, but not assume Roslyn's snapshot granularity.

A promising minimal contract is:

- A verification operation runs against an immutable, identity-bearing input snapshot. The snapshot includes or identifies every source/configuration/tool-derived input whose difference can change the reported promise.
- A mutable host/coordinator owns "current" state and creates new snapshots as source, configuration, or prepared environments change. Existing operations keep their original input identity unless explicitly canceled or restarted.
- Process boundaries carry explicit snapshot/artifact identities. Receivers must not infer freshness from connection/session identity or filesystem paths alone.
- Cache entries and prepared runtime objects may mutate in lifetime and lazily populate internally, but reuse is permitted only when their keys establish equivalence for the semantic result being requested.
- Publication binds a successful result to the exact verification subject and evidence it checked. Advancing "current" publication is a separate, fenced transition.

The important unresolved choice is the snapshot's *unit*. Roslyn's whole `Solution` is justified by its project-system and language-service workload. Anneal should start smaller: likely an explicit verification-subject/environment manifest plus immutable artifact identities, with per-stage products referenced rather than copied. If later interactive workflows repeatedly need coherent multi-file or multi-proof views, the snapshot can grow. If cross-process transfer becomes a bottleneck, content-addressed differential synchronization can be added without changing the semantic contract.

This judgment should change if Anneal's experiments show either that operations do not need stable multi-version views at all, in which case a simpler single-current-version pipeline may suffice, or that correctness-relevant state cannot be captured by a bounded manifest/artifact graph without effectively naming a larger workspace. Performance evidence could also justify Roslyn-like structural sharing sooner, but performance is not itself a correctness reason to enlarge the snapshot.

Basis: derived from Roslyn evidence + Anneal `PRINCIPLES.md`/`DESIGN.md`.

## Boundaries

**Not examined:** Roslyn performance telemetry or independent benchmarks for snapshot creation, memory retention, incremental parsing, remote synchronization, or cache hit rates. This report therefore makes no quantitative claim that Roslyn's machinery is cheap for Anneal's workload.

**Not examined:** every historical Roslyn design change. The report uses the early public overview, a contemporary red/green-tree rationale, the initial OOP integration commit, and current implementation. This is sufficient to establish the architectural evolution from in-process immutable values to explicit remote snapshot synchronization, but not to assign a single cause to every later refactoring.

**Unknown:** how much of current Roslyn's complexity is essential at its present workload versus accumulated compatibility and product constraints. Current source establishes that the mechanisms exist and what invariants their comments state; it does not establish that a greenfield system would choose the same implementation today.

**Known not to follow:** immutable solution values do not establish synchronization with build outputs. The current Edit-and-Continue implementation explicitly handles counterexamples.

**Known not to follow:** public semantic immutability does not imply absence of mutable caches or lazy realization. Current `Compilation`, `Solution`, `SolutionCompilationState`, `Workspace`, remote cache, and persistence source contain such state.

**Unsupported stronger conclusion:** Roslyn does not establish that Anneal needs one solution-wide snapshot, red/green trees, a Merkle synchronization protocol, persistent IDE processes, or one shared semantic engine. Those are workload-dependent mechanisms.

**Evidence-role caution:** source comments and design documents express implementation contracts and author intent; they are not independent outcome evaluations. The Anneal recommendations are derived architectural judgments, not source-project claims.

## Evidence

- `dotnet/roslyn` revision `4a74095f0e3598e514f3147479beee208c0ad7ed`, `Roslyn-Overview.md`. The commit adds the early overview to the public repository. Relevant sections: **Compiler APIs**, **Syntax Trees**, **Compilation**, **Workspace**, and **Solutions, Projects and Documents**. It describes compiler invocations, syntax trees, compilations, and solutions as immutable snapshots while the workspace tracks the changing host environment.
- Eric Lippert, **Persistence, façades and Roslyn's red-green trees**, published 2012-06-08, `https://ericlippert.com/2012/06/08/red-green-trees/`. Contemporary Roslyn-team account of the persistent green tree and on-demand red facade. This is historical author testimony, not an immutable repository source.
- `dotnet/roslyn` revision `7ec1fa8b6d8a43c88bca0dbb376090d219ebc43b`, `docs/wiki/Roslyn-Overview.md`, especially **Syntax Trees**, **Compilation**, **Workspace**, and **Solutions, Projects and Documents**. Current retained conceptual account of immutable snapshots and mutable workspace ownership.
- Same revision, `docs/compilers/Design/Red-Green Trees.md`, especially **The Red/Green Pattern**, **Benefits of Position-Free, Parent-Free Nodes**, and **Incremental Parsing and Subtree Reuse**. Current implementation-oriented account of structural sharing and facade cost.
- Same revision, `src/Compilers/Core/Portable/Compilation/Compilation.cs`, `Compilation` class summary. It states that the compilation is an immutable single-invocation representation while realizing and caching data on demand and reusing old compilation data in new compilations.
- Same revision, `src/Workspaces/Core/Portable/Workspace/Solution/Solution.cs`, `Solution` fields and constructor. It contains lock-protected on-demand project wrappers, cached frozen solutions, and per-document frozen-solution caches inside the logically immutable value.
- Same revision, `src/Workspaces/Core/Portable/Workspace/Solution/SolutionCompilationState.cs`, class fields and `Branch`. It separates green `SolutionState` from semantic compilation trackers, contains lazy/weak caches, and reuses tracker/cache structures across branches.
- Same revision, `src/Workspaces/Core/Portable/Workspace/Workspace.cs`, `Workspace`, `CurrentSolution`, and `SetCurrentSolution*`. It identifies the current solution as an immutable snapshot while maintaining mutable `_latestSolution`, serialization/state locks, environment-driven updates, and ordered events.
- `dotnet/roslyn` revision `c141605a972871644cc43f2caec597c88e9662db`, commit message **porting OOP to preview 4 branch** and patch. The change explicitly adds solution checksum/serialization, a remote host client, `RemoteWorkspace`, and ServiceHub components, providing a historical anchor for the move from in-process snapshots to synchronized remote snapshots.
- `dotnet/roslyn` revision `7ec1fa8b6d8a43c88bca0dbb376090d219ebc43b`, `docs/ide/api-designs/Out-of-Process Synchronization.md`. It describes checksum-based typed Merkle synchronization, incremental checksum reuse, host and OOP pinning, in-flight solution sharing, and cache lifecycle for remote snapshots.
- Same revision, `src/Workspaces/Remote/ServiceHub/Host/RemoteWorkspace.cs`, especially `RunWithSolutionAsync` and in-flight solution acquisition. Requests name a `SolutionChecksum`, share pinned computation for identical checksums, and release it after operation completion.
- Same revision, `src/Workspaces/Remote/ServiceHub/Host/SolutionAssetCache.cs`, cache and cleanup logic. The remote side stores mutable checksum-keyed assets, updates recency, protects pinned solution assets, and purges old entries.
- Same revision, `src/Workspaces/Remote/ServiceHub/Host/RemoteWorkspaceManager.cs`, default cache construction and timing rationale. Current product defaults scan every 30 seconds and purge unused, unpinned assets after one minute.
- Same revision, `src/Features/Core/Portable/EditAndContinue/CommittedSolution.cs`, `CommittedSolution` and `_documentState` comments. The source explicitly records that a captured current workspace snapshot may not match the source used to build the running module because the build and workspace lack reliable synchronization, and describes checksum-based recovery against PDB information.
- Same revision, `src/Workspaces/Core/Portable/Workspace/Host/PersistentStorage/IPersistentStorageService.cs`. The old public arbitrary-persistence service is obsolete; the comment says consumers needing persistence must supply their own semantics.
- Same revision, `src/Workspaces/Core/Portable/Storage/AbstractPersistentStorageService.cs`. Internal persistent storage is mutable, lock-protected, keyed by `SolutionKey`, and has recovery behavior that can delete and recreate a failed database.
- `google/zerocopy` revision `cc135f46155b72e4b51188525c2974a3b84acf92`, `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`. Transfer basis: success needs precise identity/scope and must not outrun evidence; trust must remain explicit; architecture should prefer general, minimally sufficient mechanisms; the atomic verification subject remains deliberately undecided.

## Revalidation

For a newer Roslyn revision, first inspect `Workspace.CurrentSolution` and the `Compilation`, `Solution`, and `SolutionCompilationState` class summaries/fields. The core conclusion survives if public semantic snapshots remain immutable while current-state ownership and lazy caches remain separate.

Then inspect `docs/ide/api-designs/Out-of-Process Synchronization.md`, `RemoteWorkspace`, `SolutionAssetCache`, and `RemoteWorkspaceManager`. Revalidate whether remote requests still name coherent snapshot identities, how they reconstruct/pin them, and whether retention remains explicitly mutable. A replacement protocol can preserve the report's conclusion even if checksums, Merkle trees, or cache timings change.

Finally inspect `CommittedSolution` or its successor. The key discriminating question is whether Roslyn can now prove direct build/workspace synchronization, or still needs content evidence to detect mismatch. If the project system introduces an authoritative end-of-build synchronization contract, revise the stale-snapshot example rather than assuming the old failure mode persists.

For Anneal, reread current `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` before reusing the transfer judgment. If the atomic verification subject, editor consistency contract, or prepared-environment identity has since been adopted, compare that decision directly with the conditional snapshot contract here. Revisit Roslyn-like structural sharing or differential synchronization only when measured Anneal workloads make snapshot construction, transfer, or multi-version retention a material cost.