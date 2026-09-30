# Persistent snapshots are cheap in proportion to change, not in proportion to their names

## Summary

Persistent data structures make an important promise about snapshots: old logical states can remain accessible without copying the entire state on every edit. They do **not** make retained history free. The classic persistence literature gets its space bounds by sharing unchanged structure and allocating only enough new structure to represent changes. Modern copy-on-write filesystems exhibit the same shape at a different layer: creating a snapshot is almost free, but an old snapshot can later pin arbitrarily much storage as the live state diverges. Arenas and hash-consing change the constants and reclamation behavior again; neither removes the need for an explicit retention policy.

The most useful cost model for Anneal is therefore reachability-based rather than snapshot-count-based. For a set of live generations, resident state is approximately the union of data reachable from those generations, plus roots/version metadata, interning or indexing tables, caches, arenas or filesystem blocks pinned by any live root, and materialized external artifacts. With structural sharing, an edit usually pays for the changed path or changed blocks rather than the whole snapshot. With retention, old versions continue to own the old paths or blocks until every relevant root, reader, hold, cache, or clone releases them. A single long-lived old generation can therefore dominate memory or disk even when creating the generation itself was cheap.

Lean 4 provides a directly relevant implementation example. At the exact Lean revision already selected by Anneal's current toolchain evidence, `PersistentArray` is a 32-way tree plus a tail, and `PersistentHashMap` is a 32-way hash trie. Updates construct a new root by modifying one path; unchanged subtrees are reused. Lean's runtime reference counting can mutate unshared arrays in place and must preserve shared arrays, so keeping old roots changes when path arrays can be updated destructively. Lean also has explicit maximal-sharing machinery backed by ordinary or persistent hash tables, showing that structural sharing and hash-consing are separate mechanisms with separate state and costs.

For Anneal, the conditional judgment is to use persistent logical structures only where they buy a concrete capability: coherent generations, cheap scratch forks, historical queries, or stable identities for in-process semantic state. Keep the authoritative generation identity small, and make retention/reclamation a first-class policy. Do not represent every layer with one "snapshot" abstraction. An immutable in-memory graph, a copied workspace, a copy-on-write filesystem snapshot, and a content-addressed generated artifact have different isolation and lifetime semantics. Opaque tools that consume files may still require a materialized immutable view even if Anneal's own metadata is persistent in memory.

The default architecture should therefore prefer short-lived shared generations with explicit reader leases and bounded history, plus durable content-addressed artifacts only where future reuse or auditability justifies them. Fine-grained hash-consing, long-lived arenas, and filesystem-level copy-on-write should be adopted selectively after measurements show that their saved copies or computation exceed the cost of hashing, indirection, fragmentation, retained memory, and garbage collection.

## Applicability

This report addresses J040's question about the space cost of immutable snapshots. It combines four kinds of evidence:

- the classic persistence construction of Driscoll, Sarnak, Sleator, and Tarjan;
- exact current-source inspection of Lean 4's persistent arrays, persistent hash maps, and maximal-sharing support at the Lean revision already used by Anneal evidence;
- contemporary implementation documentation for arena allocation and weak hash-consing; and
- OpenZFS documentation as a concrete copy-on-write filesystem analogue.

The persistence paper proves asymptotic results for linked structures under stated structural assumptions. It does not give memory measurements for Anneal, Lean, Rust, or modern allocators. Lean source establishes mechanisms at the inspected revision, not a benchmark or a guarantee about Anneal's workload. OpenZFS illustrates block-level copy-on-write and retention accounting; it is not a model of Lean object layout or a recommendation that Anneal depend on ZFS. `typed_arena` illustrates whole-arena reclamation semantics; Anneal does not currently use that crate by virtue of this report. The OCaml `fix` hash-consing implementation supplies a practical example of weak retention; it is not evidence that one hash-consing policy is universally best.

The Anneal judgment is derived against `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, especially `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`. Those documents require precise verification identity and scope, distinguish partial information from verification success, keep trust explicit, and prefer general minimally sufficient mechanisms. They deliberately leave the atomic verification subject, result format, and lower-level mechanisms undecided. This report does not turn a snapshot representation or reclamation strategy into adopted design policy.

Terminology matters:

- A **logical snapshot** is an immutable value or root that denotes one coherent state.
- **Structural sharing** means two logical snapshots point to common immutable substructure.
- A **copied workspace** is a physically distinct file tree created by copying bytes.
- A **copy-on-write filesystem snapshot or clone** initially shares physical blocks and allocates new blocks as either side changes.
- A **content-addressed artifact** is immutable data named by content identity and normally reusable across roots that refer to that identity.
- An **arena** is a lifetime/allocation region whose members are reclaimed together.
- **Hash-consing** canonicalizes equal values so equal structure can share one representative.

These are composable techniques, not synonyms.

## Findings

### 1. Persistence changes the unit of copying; it does not abolish copying

Driscoll et al. define persistent structures by preserving access to previous versions after updates. Their central contribution is not "versions cost nothing." It is that, for important classes of pointer structures, persistence can be implemented with bounded overhead relative to the ephemeral update.

Their partially persistent constructions make the distinction explicit. The fat-node method records new field values with version stamps inside existing nodes. It can achieve constant additional space per update step, but versioned access pays an extra logarithmic factor to find the right field value. Their node-copying method instead copies a node when its bounded modification capacity is exhausted and repairs incoming pointers as needed. Under bounded in-degree assumptions, the amortized extra space per update step and the amortized time overhead can both be constant. Persistent red-black trees then retain logarithmic operation time while total space is linear in the number of updates.

The relevant engineering interpretation is:

`space_after_m_updates ≠ space_of_one_version`

even when

`marginal_space_per_update << size_of_one_version`.

A snapshot root can be tiny while the history reachable through all roots grows with the edits that distinguish those versions. That is the core reason "immutable" is compatible with efficient history but not equivalent to "free history."

Basis: Driscoll, Sarnak, Sleator, and Tarjan (1989), primary publication; derived Anneal interpretation.

### 2. The correct mental model is the union of reachable state

For Anneal, a useful qualitative resident-space model is:

`resident ≈ shared_live_base
          + union(unique_deltas_reachable_from_live_generations)
          + roots_and_version_metadata
          + interning/index/dependency tables
          + caches_and_arenas_pinned_by_live_roots
          + materialized_external_views_and_artifacts`.

This is deliberately not a byte-precise equation. Its purpose is to expose which variables matter.

If ten generations differ by one small path each, structural sharing can make their incremental cost small. If one generation preserves a deleted 5 GiB generated tree or holds a generation arena containing it, that one root can dominate retention. If many versions all refer to the same canonical proof term, hash-consing can reduce the union. If an interning table owns strong references to every canonical term, the table can itself prevent reclamation. If a persistent process keeps caches keyed by dead generations, dropping Anneal's visible root may not release the memory at all.

This model also separates **allocated over time** from **resident now**. A persistent data structure may allocate a new path on every update while reference counting or garbage collection promptly frees superseded paths once no live root points to them. Conversely, a low-update workload can retain large resident state indefinitely if old roots remain live.

The quantity that predicts space is therefore closer to `divergence × retention lifetime × reclamation granularity` than to the number of version labels.

Basis: synthesis of the persistence construction, Lean reference-counted persistent structures, arena lifetime semantics, weak hash-consing, and OpenZFS snapshot accounting.

### 3. Lean's persistent collections show what path copying looks like in a relevant runtime

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `Lean.Data.PersistentArray` uses a branching factor of 32 and stores a persistent tree plus a tail. `setAux` descends to one leaf and returns a new chain of modified ancestors; `set` then returns a new `PersistentArray` root. `push` normally extends the tail and moves full tails into the tree. This means a logical update need not duplicate every element. Its changed structural footprint is proportional to the tree path plus tail behavior, while untouched nodes remain reachable from both roots.

The exact same revision's `Lean.Data.PersistentHashMap` is a 32-way hash trie with bounded trie depth and collision nodes. `insertAux` follows one hash-derived branch and reconstructs the nodes along that path. `eraseAux` does the corresponding path-local rewrite. Again, the logical mechanism is structural sharing rather than whole-map copying.

Lean's runtime representation adds an important second layer. Lean documentation explains that arrays can be updated destructively when uniquely referenced and must be copied when shared. Thus logical immutability does not imply that every update allocates all path arrays in all circumstances: reference counting lets a uniquely owned node reuse storage. Retaining an old version changes that optimization boundary because nodes reachable from both versions are no longer uniquely owned. The exact allocation cost therefore depends on ownership/reference-count state as well as the abstract persistent structure.

Two consequences follow for Anneal.

First, a broad immutable `VerificationSnapshot` can be cheap *if* it is mostly a small root over persistent substructures and edits touch localized paths. Second, keeping many historical roots can reduce opportunities for destructive update and retain more path nodes. "Lean uses persistent collections" is therefore evidence that this representation is practical, not evidence that arbitrary history depth is costless.

Basis: exact Lean 4 source at the pinned revision plus Lean reference-counting/array documentation; derived Anneal application.

### 4. Snapshot granularity should follow the shape of edits

A wide-trie or persistent-map representation earns its cost when a typical edit changes a small part of a much larger logical state. It is less attractive when every edit naturally replaces most of the state.

For an Anneal generation, plausible persistent substructures include:

- maps from source identity to file/content identity;
- maps from proof subject to selected model/artifact identities;
- diagnostic or obligation indexes keyed by stable subject identifiers;
- dependency edges or stage-result metadata whose updates are localized; and
- editor-facing lookup indexes that need coherent historical roots.

Large opaque blobs—LLBC files, generated Lean modules, compiled `.olean` files, tool stdout, logs—are different. Treating their bytes as nodes in a fine-grained persistent tree may add complexity without exposing useful mutation structure. Naming the entire blob by content identity and sharing that immutable artifact across generation roots is often simpler.

That suggests a two-level design: structurally shared metadata points at coarse immutable artifacts. The metadata can fork cheaply; unchanged artifacts are reused exactly; changed artifacts are replaced as units. More detailed structure should appear only when an operation can exploit it.

Basis: persistent-structure mechanisms + Anneal's minimally-sufficient-mechanism constraint; derived judgment.

### 5. Arenas optimize allocation and reclamation together, which makes lifetime grouping decisive

The `typed_arena` documentation describes the canonical arena tradeoff: allocation is fast, individual objects are not deallocated while the arena is alive, and all objects are destroyed when the arena is destroyed.

For snapshot systems this is useful and dangerous in the same way. A per-generation arena can make reclamation extremely simple: once no reader can reach the generation, discard one arena. But if a generation shares arena-owned objects with another generation, whole-generation reclamation and structural sharing pull in opposite directions. If every generation gets an independent arena, cross-generation sharing is lost. If many generations share one arena, one live reference can pin unrelated dead objects until the whole arena becomes unreachable.

The practical answer is normally lifetime segmentation rather than one universal arena. Examples include:

- short-lived scratch-generation arenas;
- generation-local transient indexes that can be dropped wholesale;
- separately owned immutable shared artifacts for data meant to outlive one generation; and
- smaller arena epochs or slabs when a single long-lived reader must not pin an unbounded history.

An arena therefore changes the **reclamation granularity**. It does not make retention disappear. For Anneal, the lifetime grouping should be chosen from actual generation/read patterns rather than from allocator convenience alone.

Basis: `typed_arena` 2.0.2 documentation + derived lifetime analysis.

### 6. Hash-consing can share equal structure across unrelated update paths, at the price of a table and a lifetime policy

Path-copying shares nodes because one version was derived from another. Hash-consing can share nodes for a stronger reason: two separately constructed values are structurally equal. That can be valuable for repeated syntax, types, expressions, proof terms, or normalized metadata that would otherwise be duplicated.

Lean exposes this idea directly. At the inspected revision, `Init.ShareCommon` describes maximal-sharing primitives implemented with maps and sets of Lean objects. `Lean.Util.ShareCommon` provides both ordinary and persistent factories: the persistent factory uses `PersistentHashMap` and `PersistentHashSet` for the sharing state. The important point is architectural, not that Anneal should invoke these exact APIs. Canonicalization requires a stateful index, equality/hash work, and a decision about how long representatives remain interned.

The OCaml `fix` package illustrates the lifetime issue. Its weak hash-consing implementation uses a weak table so the table can forget a canonical value after users have forgotten it. This preserves sharing among live users without turning the interning table into a permanent owner of every object ever interned.

A strong global interner has the opposite property: it can convert otherwise collectible history into process-lifetime state. That may be acceptable for a bounded symbol universe and unacceptable for arbitrary generated proof terms.

For Anneal, hash-consing should therefore be selective. Use it where repeated values are common, equality is stable and cheap enough to compute, and the resulting canonical identity is useful. Prefer weak or generation-scoped retention where the interner should not own history forever. Measure table size, hit rate, and hashing/equality cost before extending the technique to large values.

Basis: exact Lean sharing source + `fix` weak hash-consing implementation; derived judgment.

### 7. Copy-on-write filesystems demonstrate why "snapshot creation cost" and "snapshot retention cost" are different questions

OpenZFS is a useful physical analogue because its documentation makes both sides explicit.

A write never overwrites an in-use block. ZFS writes the changed block, then writes new parent blocks up to a new root. Unchanged blocks remain shared. A snapshot is initially just a reference that keeps the old tree reachable, so snapshot creation is nearly instantaneous and initially consumes essentially no extra data space. But as the live dataset diverges, blocks only the snapshot still references cannot be freed. OpenZFS explicitly notes that one old snapshot can pin an arbitrary amount of space.

This is the same reachability shape as persistent in-memory structures, but with different constants and semantics. It also illustrates why per-snapshot `used` numbers are not additive: several snapshots may share blocks. The storage released by deleting one root depends on whether other roots still reference the same blocks.

ZFS holds and clones add a second relevant lesson. A named hold or dependent clone can prevent snapshot destruction; deferred destruction only completes after the last dependency disappears. Anneal's reader leases, outstanding jobs, scratch forks, or published artifacts have the same lifecycle problem in abstract form: "generation no longer current" is not sufficient to reclaim it if another authorized reader can still reach it.

OpenZFS is not evidence that Anneal should require ZFS. It is evidence against a misleading cost model. Cheap root creation is compatible with expensive long-term retention.

Basis: current OpenZFS copy-on-write and snapshot documentation observed 2026-09-30; analogy to Anneal is derived.

### 8. A filesystem snapshot, a logical snapshot, and a copied workspace solve different isolation problems

An immutable in-memory generation says Anneal's own data structures will not change. It does not freeze a directory that an external process reads later. A shared mutable filesystem path can therefore violate coherence even when Anneal's metadata root is immutable.

There are several distinct ways to bridge that boundary:

**Copy the workspace.** This gives a simple physically separate tree. Initial time and space are proportional to copied bytes unless the platform or copy primitive provides hidden copy-on-write behavior. It is portable conceptually and expensive for large trees.

**Use a copy-on-write filesystem snapshot or clone.** Initial materialization can be close to root creation, and unchanged blocks remain shared. The price is platform/filesystem dependence, block-level divergence costs, snapshot/clone retention, and the need to understand which non-file inputs the tool can still observe.

**Materialize only declared inputs into a generation directory.** This can be much smaller than copying a repository if the upstream dependency closure is known. If the closure is incomplete, the resulting isolation claim is incomplete.

**Avoid filesystem materialization through an upstream immutable API.** This can be best when the tool exposes a true snapshot/value interface, but it requires that the API's identity and dependency semantics are strong enough for Anneal's use.

These are deployment choices around an external-tool boundary. Internally persistent maps do not select among them. Conversely, a perfect filesystem snapshot does not automatically capture environment variables, process-local caches, network state, clocks, plugin state, or external services.

For Anneal, the clean separation is: a logical generation names the exact source/model/tool/environment inputs that matter; each stage adapter chooses the least expensive materialization that faithfully realizes that generation for the upstream tool.

Basis: OpenZFS semantics + Anneal design authority + derived boundary analysis.

### 9. Historical queries and scratch forks need different retention policies

A persistent root makes two user-visible features easy to describe but not automatically cheap to keep forever.

**Historical queries.** If an agent asks what Anneal believed for generation `g-12`, retaining the generation root can make the answer direct. But long history converts transient editor state into a storage product. A bounded in-memory ring, time-based expiration, or explicit pin can provide recent history while allowing old roots to disappear. Durable accepted results can be stored separately as compact manifests plus content-addressed evidence rather than by keeping an entire live worker graph.

**Scratch forks.** An agent can fork the current root, make speculative edits, and discard the fork. Structural sharing makes this an especially attractive use of persistence: unchanged state is shared and the scratch branch pays only for its delta. But scratch authority must remain separate from publication authority. A cheap fork is not evidence that a speculative result belongs to the current accepted generation.

These workloads have opposite natural lifetimes. Scratch state is branchy but short-lived; audit/history state can be long-lived but should usually be compact and deliberately selected. A single retention class for both will either reclaim useful history too soon or keep speculative state too long.

Basis: derived application of persistence mechanics and Anneal's result-authority constraints.

### 10. Generation reclamation needs roots, readers, and derived stores to agree

A robust reclamation protocol needs more than "drop the old generation from the current pointer."

One workable conceptual model is:

1. A generation root is immutable after publication.
2. Current state holds one root reference.
3. Jobs/readers acquire scoped leases or strong references to the generation they use.
4. Scratch forks hold their parent/shared nodes only as long as the fork lives.
5. When a generation is no longer current and has no readers/pins, its root is released.
6. Runtime reference counting or garbage collection reclaims unreachable shared nodes.
7. Separate stores—arenas, content-addressed blobs, filesystem snapshots, subprocess caches—reclaim their objects according to their own reachability or retention policy.

Step 7 is where simplistic designs fail. An in-memory root can disappear while a filesystem clone still pins blocks, an interning table still owns nodes, an arena still retains dead objects, or a persistent worker cache still owns artifacts. Reclamation needs either one shared reachability model or explicit per-store ownership and metrics.

A generation record should therefore be able to answer, at least operationally, "what resources may this generation keep alive?" It need not enumerate every heap object, but it should identify owned/pinned coarse resources well enough to debug retention.

Basis: synthesis of reference-counted sharing, arena lifetime, weak interning, and ZFS holds/clone dependencies.

### 11. The realistic qualitative cost model differs by workload

The following cost model is more useful than calling snapshots "cheap" or "expensive."

| Workload | Persistent logical state | Full copy | Filesystem CoW | Important retention risk |
| --- | --- | --- | --- | --- |
| Small edit to large semantic map | New root + changed paths; most nodes shared | Copies whole represented state | Changed blocks + metadata paths | Old roots pin pre-edit paths |
| Many recent editor generations | Good if deltas localized and history bounded | High copy bandwidth/space | Good for file-heavy external stages if available | Ring/history size and old-reader leases |
| Long historical archive | Shared history can still grow with cumulative edits | Predictably large | Old snapshots can pin arbitrary deleted data | Silent unbounded retention |
| Scratch fork from current | Root fork is cheap; delta-only updates | Full duplicate | Clone can be cheap initially | Forgotten forks/leases |
| Large opaque generated artifact changed wholesale | Little benefit from internal path persistence unless structured reuse exists | One new blob either way | CoW may save unchanged physical blocks | Keeping many artifact generations |
| Repeated equal semantic nodes | Hash-consing may reduce union | Copies repeat | Filesystem dedup not guaranteed | Intern table can become owner |
| Generation-local transient graph | Arena can make allocation/drop cheap | N/A | N/A | Coarse arena pins dead members |

The table is qualitative because Anneal lacks representative memory profiles for these alternatives. The correct next measurement is not "how many snapshot objects can we allocate?" It is resident memory/disk versus edit sequence, history depth, scratch-fork fanout, reader lifetime, and generated-artifact churn.

Basis: derived synthesis; no Anneal benchmark was performed.

### 12. The serious alternatives are layer-specific, not one global winner

There are at least five credible strategies.

**One mutable current graph, recompute history.** Lowest retained-memory complexity. Historical queries are slower or unavailable. This is strong when only the current generation matters.

**Whole-state copies.** Easy isolation and simple ownership. Cost grows with represented state size. This is often a good baseline because its semantics are easy to test.

**Persistent in-memory structures.** Best when state is mostly shared, edits are localized, and cheap forks/history matter. Costs include extra indirection, persistent-structure implementation complexity, old-root retention, and potentially reduced destructive-update opportunities.

**Copy-on-write filesystem snapshots/clones.** Strong fit for opaque file-oriented tools where the platform provides them. Costs include platform coupling, fragmentation/block retention, and mismatch with non-filesystem inputs.

**Content-addressed immutable artifacts with small manifests.** Strong fit for coarse stage outputs and auditability. Costs include hashing, storage/index/garbage collection, and lack of fine-grained sharing inside a changed blob.

The likely Anneal architecture is a composition. A persistent in-memory manifest can point to content-addressed LLBC/Lean artifacts; a short-lived filesystem clone can materialize one generation for an opaque subprocess; accepted results can keep compact immutable manifests after interactive state is reclaimed. The benchmark should compare this composition against a simple copy/recompute baseline rather than against an imaginary "zero-cost snapshot."

Basis: derived conditional judgment.

### 13. Conditional judgment for Anneal

Adopt three design rules unless measurements or stronger upstream contracts justify something else.

**First, separate identity from retention.** A generation identifier should remain stable even after its hot in-memory representation is gone. Keep enough durable metadata to explain an accepted result, but do not keep the whole live graph solely because a generation once existed.

**Second, make the common transient path cheap and bounded.** Use structural sharing for localized in-process metadata updates and scratch forks; retain only a bounded recent history by default; use reader leases/pins for explicit exceptions. Reclaim aggressively when a generation is neither current nor referenced.

**Third, choose the storage mechanism per boundary.** Use coarse immutable/content-addressed blobs for large stage artifacts, persistent maps/arrays for metadata whose edits are genuinely local, arenas for same-lifetime transient objects, and filesystem copy-on-write only where an external file-oriented stage benefits enough to justify its platform and retention semantics. Hash-cons only high-repetition structures with an explicit interner lifetime.

Evidence that should change this judgment includes:

- memory profiles showing persistent path copies or old roots dominate interactive use;
- measured demand for deep historical queries that makes bounded recent history insufficient;
- high scratch-fork fanout where persistent roots save substantial work;
- evidence that generated artifacts contain enough stable internal structure to justify sub-blob persistence;
- a strong upstream Aeneas or Lean snapshot API that removes filesystem materialization;
- measured high hash-cons hit rates on costly semantic nodes; or
- deployment constraints that make filesystem copy-on-write universally available or categorically unavailable.

Anneal should not decide those questions from persistence theory alone.

## Boundaries

- No Anneal, Charon, Aeneas, Lean, or Lake performance experiment was run for this report.
- No byte-precise memory model is claimed. Lean object headers, allocator behavior, reference-count traffic, cache sizes, and the distribution of Anneal edits were not measured.
- Driscoll et al.'s asymptotic bounds require the structural assumptions in the paper. They are not direct guarantees for Lean's 32-way tries or arbitrary Anneal object graphs.
- Lean source inspection establishes logical update structure at `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. It does not establish current runtime memory consumption under Anneal workloads.
- The report does not claim Lean's persistent collections always allocate only one node per level. The concrete runtime may update uniquely owned arrays destructively or copy shared arrays, and collision/tail cases have their own costs.
- OpenZFS is an analogy for copy-on-write reachability and retention, not a recommendation or proof of portability. Anneal must work according to its actual target filesystems and external-tool semantics.
- `typed_arena` is an example of whole-arena lifetime semantics, not a dependency recommendation.
- Weak hash-consing avoids one class of retention, but weak tables have lookup/rebuild/GC costs and do not make canonicalization free.
- Content-addressed storage can deduplicate exact bytes; it does not imply semantic equivalence of distinct bytes or guarantee cheap garbage collection.
- A logical immutable root does not freeze ambient filesystem, environment, process, plugin, network, or clock state.
- A filesystem snapshot does not by itself establish source/model correspondence, tool correctness, or verification authority.
- Reader leases and generation pins are a derived lifecycle proposal, not current Anneal policy.
- The report does not settle J041's dataflow/materialized-view question or J043's Skyframe/hermeticity question.
- Anneal implications are derived conditional analysis. `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` remain authoritative.

## Evidence

### Driscoll, Sarnak, Sleator, and Tarjan, *Making Data Structures Persistent* (1989)

Primary publication landing page: https://www.cs.cmu.edu/~sleator/papers/Persistence.htm  
Primary PDF: https://www.cs.cmu.edu/~sleator/papers/making-data-structures-persistent.pdf  
DOI: 10.1016/0022-0000(89)90034-2

The paper formalizes partial and full persistence for linked data structures. It analyzes fat-node and node-copying techniques, including the tradeoff between per-update space and access time and the bounded-in-degree result that permits constant amortized persistence overhead for update steps. It is the primary basis for the distinction between a small marginal update and the total space of retained history.

Basis: primary publication.

### Lean 4 persistent arrays and hash maps at the Anneal-relevant pin

Repository: https://github.com/leanprover/lean4  
Revision: `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`  
Files:
- `src/Lean/Data/PersistentArray.lean` blob `516fb0ce50651c1ef39cccdca48663335dac7790`
- `src/Lean/Data/PersistentHashMap.lean` blob `f963f3a3f3cfc8c262e14bfcf56d21fc3a55442d`
- `src/Init/ShareCommon.lean` blob `4692b83a1939718e215918261cb5666e2ef9c88a`
- `src/Lean/Util/ShareCommon.lean` blob `d64141f8e6e026170f0fa4089e0cd2e43f9d47bb`

The source establishes the 32-way persistent array/tree representation, the 32-way persistent hash trie, path-local updates, and the separate maximal-sharing/hash-consing machinery. It is mechanism evidence, not workload measurement.

Basis: exact primary source revision.

### Lean reference counting and arrays

Lean language/reference documentation:
- https://lean-lang.org/doc/reference/latest/Basic-Types/Reference-Counting/
- https://lean-lang.org/doc/reference/latest/Basic-Types/Array/

The documentation describes Lean's reference-counted heap and the optimization that can update uniquely referenced arrays destructively while preserving shared arrays by copying when needed. This explains why abstract persistent structure and physical allocation behavior are related but not identical.

Basis: first-party language documentation observed 2026-09-30.

### OpenZFS copy-on-write and snapshots

OpenZFS documentation:
- https://openzfs.github.io/openzfs-docs/Basic%20Concepts/Copy-on-write.html
- https://openzfs.github.io/openzfs-docs/Basic%20Concepts/Datasets/Snapshots%20and%20Clones.html

The documentation states that ZFS never overwrites an in-use block, that updates create new blocks along the changed path to a new root, and that snapshots initially add almost no data space because they keep the old tree referenced. It also documents the later retention cost: old snapshots pin blocks as the live dataset diverges, and one old snapshot can pin an arbitrary amount of space. Holds and clones can prevent destruction.

Basis: first-party implementation documentation observed 2026-09-30.

### `typed_arena` 2.0.2

Documentation: https://docs.rs/typed-arena/2.0.2/typed_arena/

The crate documents arena allocation where individual values are not freed while the arena is alive and all values are destroyed together when the arena is destroyed. This is used only to establish the generic reclamation-granularity tradeoff.

Basis: first-party crate documentation.

### OCaml `fix` hash-consing

Package documentation/source: https://ocaml.org/p/fix/latest/doc/src/fix/HashCons.ml.html

The implementation exposes hash-consing variants including a weak-table form. The weak table can forget a canonical datum after users no longer retain it, demonstrating one practical way to avoid an interning table becoming permanent ownership of all canonicalized values.

Basis: public implementation documentation/source observed 2026-09-30.

### Anneal design authority

Repository: https://github.com/google/zerocopy  
Revision: `cc135f46155b72e4b51188525c2974a3b84acf92`  
Files:
- `anneal/PRINCIPLES.md` blob `d5339a95254eae14ac201139d07d9d36d48a19fb`
- `anneal/DESIGN.md` blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`

These documents supply the normative constraints used for the derived Anneal judgment: precise result identity/scope, evidence-bounded success, explicit trust, and preference for general minimally sufficient mechanisms. They do not adopt a persistence, arena, interning, or filesystem-snapshot design.


## Revalidation

Revalidate this report at the layer whose retention policy may have changed rather than repeating the whole survey. For Lean-backed in-memory persistence, inspect the then-current implementations of `PersistentArray`, `PersistentHashMap`, `ShareCommon`, and the runtime array/reference-counting rules; the discriminating question is whether updates still preserve old roots by sharing unchanged structure and what lifetime owns any interning state. For filesystem-backed generations, check the actual deployment filesystem's snapshot/clone semantics and measure referenced space while a retained generation diverges from the current one. For arena or interning proposals, inspect the exact owner and reclamation rule: one retained owner that keeps otherwise-dead objects alive is enough to invalidate the report's assumed reclamation granularity.

For an Anneal design change, measure at least four workloads with the proposed mechanism and the simplest copy/recompute baseline: a small localized edit, a sequence of edits with bounded recent history, a scratch fork that diverges and is discarded, and a pinned historical generation while current work continues. Record peak resident memory, retained artifact bytes after reclamation, allocation/copy volume, and latency. If those measurements show that old roots, path copies, arenas, intern tables, or filesystem snapshots dominate the cost, revise the layer-specific recommendation rather than treating structural sharing as a fixed requirement. If a newer Aeneas or Lean API supplies an immutable snapshot with a documented lifetime and input boundary, re-evaluate whether Anneal still needs to materialize or retain the corresponding layer itself.

The qualitative conclusion needs no update merely because constants change. It should be reconsidered if a relevant mechanism stops using structural sharing, if ownership/reclamation semantics change, if Anneal adopts materially deeper history or fork requirements, or if measurements establish that another representation has a better cost/assurance tradeoff for the actual workload.