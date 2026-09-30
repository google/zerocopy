# MVCC, snapshot isolation, and consistency contracts for interactive proof work

## Summary

Database concurrency models separate several guarantees that an interactive proof service should also keep separate. A coherent snapshot says which state a read observed. Linearizability additionally gives an operation a single point between invocation and response and preserves real-time order. Serializability constrains a group of reads and writes to behave like some serial transaction order. Optimistic concurrency control allows work to proceed speculatively and validates before an authority-changing write. Snapshot isolation gives each transaction a coherent start-time snapshot and prevents overlapping writes to the same item, but it can still admit write skew across disjoint items.

For Anneal, the useful transfer is not a database implementation. It is an operation-specific consistency contract. A side-effect-free goal query can legitimately run against an older immutable project generation if the response names that generation and callers do not mistake it for current state. A query-then-edit operation should carry the generation and dependency state on which the edit was derived and validate them atomically before applying the edit. Verification acceptance and publication need an exact coherent source/model/environment generation plus a current authority fence. Per-file versions are sufficient only when they can be shown to belong to one admitted coherent project snapshot; independent version labels do not themselves create one.

Current Anneal reference experiments make the last distinction concrete. In-place replacement of a multi-file Charon/Aeneas/Lean family exposed mixed old/new inventories, and an old proof could still pass while earlier semantic inputs had already changed. Resolving one immutable generation before a multi-file read avoided the corresponding mixed-generation observation. Those experiments motivate snapshot identity, but the database literature supplies the stronger judgment: snapshot coherence alone is not enough for concurrent authority-changing work when different writers can preserve their own local checks while jointly violating a cross-resource invariant.

## Applicability

The database findings are literature results, not measurements of Anneal. They apply to the concurrency models identified in `REPORT.json` and are used here as conceptual precedents. In particular, this report does not claim that Anneal currently implements MVCC, snapshot isolation, serializable transactions, or optimistic concurrency control.

The Anneal-specific analysis is derived from current design authority at `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92` and from execution reports preserved on `reference@30b9d5749aed6049d949f4f582dd64c70088d07a`. The relevant existing experiments concern immutable generation directories, mutable selection pointers, open-document state, and multi-file generated artifacts. They establish concrete state-coherence hazards, not a general concurrency theorem.

The term **project generation** below means an immutable identity for the complete semantic input set needed by the operation being discussed. Depending on the operation, that set can include Rust source, Cargo subject and configuration, translated LLBC, generated Lean source and compiled imports, toolchain identity, proof files, and other declared semantic dependencies. A single scalar generation ID is one possible representation. A vector or manifest of component versions can provide the same logical guarantee if it is itself admitted as one coherent snapshot and validated as such. The conclusion is about coherence and validation, not about one required encoding.

The term **authority-changing operation** means a transition whose success can change what Anneal or its clients treat as current or accepted: applying an edit, selecting a generated environment, recording verification success, or publishing a result. Advisory reads and background cache fills need not have the same guarantee.

## Findings

### The guarantees answer different questions

Kung and Robinson's 1981 optimistic method divides a transaction into read, validation, and write phases. Reads and tentative writes can proceed without locking; the write is admitted only after validation establishes that the speculative computation remains consistent with intervening transactions. Their treatment explicitly includes query results among outputs whose correctness depends on validation. The important mechanism for Anneal is the separation between **computing from a snapshot** and **authorizing a consequence of that computation**.

Basis: **primary literature** + **derived** Anneal mapping.

Herlihy and Wing's 1990 linearizability condition addresses a different problem. Each concurrent operation must appear to take effect at one point between its invocation and response, while respecting real-time precedence. It is a local correctness property for concurrent objects. Linearizability is therefore useful when an API promises a read of "the current selection" or a compare-and-swap against the current generation. It is stronger than merely returning a coherent older snapshot, and it is not a substitute for transaction-level serializability across several resources.

Basis: **primary literature** + **derived** distinction.

Berenson et al.'s 1995 snapshot-isolation model gives a transaction the committed state as of its start and uses a first-committer-wins rule for overlapping writes. The paper also shows that this does not imply serializability. Two transactions can read the same consistent snapshot, write different items, and jointly violate an invariant that neither writer violates in its own snapshot. This is the write-skew failure mode.

Basis: **primary literature**.

Ports and Grittner's PostgreSQL work shows one practical way to recover serializability while retaining snapshot-based reads: detect dependency patterns that could participate in a serialization anomaly and abort some transactions. Their implementation also records the costs of the stronger guarantee. Dependency tracking consumes memory, dangerous-structure detection can cause false-positive aborts, and read-only work can avoid some overhead only when it is known to run on a safe snapshot. The lesson is not that Anneal should copy PostgreSQL SSI. It is that stronger consistency requires explicit conflict information, validation, serialization, or a comparably strong invariant at the mutation boundary.

Basis: **primary implementation paper** + **derived** Anneal mapping.

### A goal query usually needs a coherent named snapshot, not a globally latest read

A pure goal query answers a question about semantic state. If its contract says "goal at position P in project generation G," the response can be correct even when a newer generation G+1 becomes current during the query. The necessary conditions are that all semantic dependencies used by the query belong to one coherent generation and that the response carries enough identity to prevent callers from silently treating G as G+1.

Requiring every such read to be linearizable against the mutable current-generation pointer would add synchronization without strengthening the answer's meaning under this explicit-snapshot contract. A caller that truly asks "what is the goal in whatever generation is current when this response returns?" has requested a different operation. That operation needs a current-generation validation point, or an equivalent linearizable admission rule, before the answer can be labeled current.

This distinction is already visible in current Anneal evidence. `anneal-3731-real-generation-publication-v4-30-0-rc2` kept an old Lean server pinned to generation A while generation B became selected. The old server still produced a valid A-scoped answer after B publication; the report correctly labels that answer noncurrent rather than calling it invalid. `lsp-proof-assistant-architecture-2026-09-27` likewise separates client-owned document versions from dependency/project generations. An answer can be internally valid for its snapshot without being the latest project answer.

Basis: **derived**, supported by current Anneal **execution/source evidence**.

### Query-then-edit needs validation at the authority boundary

Suppose an agent queries a proof state in generation G, reasons from that state, and proposes an edit. The proposal is speculative work. Before Anneal applies it to the current workspace, the host should validate that the semantic dependencies on which the proposal relied are still the ones for which the edit was derived. If they are not, the safe outcomes are to reject, rebase, or recompute; silently applying the edit to a different semantic state changes the operation's meaning.

This is the optimistic-concurrency pattern in local form:

1. pin a coherent generation G;
2. perform the expensive query and synthesis against G;
3. submit the resulting edit with G, and preferably the narrower dependency identities actually relied on;
4. atomically validate those identities against the mutation target; and
5. apply only if validation succeeds.

A single compare-and-swap on an immutable project-generation root can implement this contract when every authority-relevant dependency is below that root. A dependency vector can also work if validation is atomic and the vector names a coherent cut. Neither mechanism requires a database.

Basis: **derived** from optimistic-concurrency literature and Anneal's generation/publication evidence.

### Snapshot isolation is too weak for cross-resource invariants

Snapshot isolation catches two concurrent writers that update the same item, but it can allow two writers whose write sets are disjoint. That matters whenever correctness is expressed over a relation among several mutable objects rather than over each object independently.

An abstract proof-workspace example illustrates the risk. Assume a project invariant requires at least one of two independently editable guards to remain enabled. Two agents start from the same snapshot where both guards are enabled. One disables the first; the other disables the second. Each writes a different file, so first-committer-wins on file identity sees no write/write collision. Both local decisions were justified by the same old snapshot, yet the combined state violates the invariant. This is a direct analogue of write skew, not a claim that Anneal currently has this particular invariant.

The same structure can appear without human-visible files. A source edit and a proof-environment transition, or two changes to separate configuration records, can each be locally valid while jointly invalidating an assumption that spans them. If Anneal exposes concurrent authority-changing operations over such state, it needs either one serialized authority boundary, serializable validation over the relevant dependency relation, or an invariant-specific mechanism that is demonstrably equivalent for the accepted operations.

Basis: **derived** from the snapshot-isolation write-skew result.

### Per-file versions do not by themselves make a project snapshot

Versioning each file solves identity only if the versions are known to constitute one coherent semantic state. A client can otherwise observe `A@2` together with `B@1` even when no admitted project generation ever contained that pair. Adding more individual version fields makes the mixture easier to describe; it does not make the mixture valid.

Current Anneal execution evidence demonstrates the concrete analogue. During controlled in-place replacement of a seven-file Charon/Aeneas/Lean family, several intermediate inventories matched neither generation A nor generation B. In four such mixed states, a fresh Lean process still accepted the old proof because the old compiled function artifact had not yet been replaced, even though earlier inputs had changed. A reader that treated successful proof checking as a universal coherence oracle could therefore mislabel a mixed generation as current.

The companion publication probes show a narrower filesystem version of the same problem: opening one file through a mutable `current` pointer, changing the pointer, and opening a second file can mix generations. Resolving the pointer once and reading both files from the immutable resolved directory yields one coherent older generation instead.

The right invariant is therefore not "every file has a version." It is "every authoritative operation is bound to a set of inputs that Anneal can establish came from one admitted semantic snapshot." A scalar immutable generation root is a convenient way to establish that fact. A vector is also sufficient when construction and validation prove it names a coherent cut.

Basis: current Anneal **execution evidence** + **derived** concurrency interpretation.

### Authority-changing operations need stronger guarantees than advisory reads

The minimum useful contract differs by operation:

| Operation | Minimum consistency contract | Why |
| --- | --- | --- |
| Background navigation, indexing, or cache warming | Coherent named snapshot; staleness may be acceptable if explicit | No authority changes, so a useful older result need not block newer work. |
| Goal/query response explicitly scoped to generation G | Coherent G plus response identity | Correctness is about G, not the mutable notion of "latest." |
| Goal/query response promised as current | Coherent snapshot plus a validation/linearization point against current selection before labeling it current | Otherwise G can become stale during computation. |
| Query-then-edit | Coherent base snapshot plus atomic optimistic validation of all relevant dependencies before applying | Prevents applying reasoning from G to a materially different target. |
| Concurrent edits with cross-resource invariants | Serializable effect, serialized mutation boundary, or an invariant-specific equivalent | Snapshot isolation / disjoint-file conflict checks admit write skew. |
| Verification acceptance or generated-environment publication | Exact source/model/environment identity, complete-generation validation, and current publication fence | An accepted success result changes authority and must not be assembled from mixed or superseded inputs. |

This table describes semantic requirements, not an API commitment. In particular, "serializable effect" does not require SQL transactions. A single-threaded coordinator, a generation-root compare-and-swap, or a small critical section can provide a serial order if it covers every authority-changing state transition that can violate the invariant.

Basis: **derived synthesis**.

### Stronger consistency has visible costs, so it should be applied where meaning requires it

Four serious implementation strategies occupy different points in the design space:

- **Serialize or lock all work.** This can make mutation semantics simple, but it needlessly blocks long read-only proof queries and can turn one slow tool invocation into global latency. The database literature developed snapshot and optimistic techniques partly to avoid such contention.
- **Use immutable snapshots for everything and never validate.** This makes reads simple and reproducible, but only answers questions about old snapshots. It does not justify applying a derived edit or reporting a stale proof as current.
- **Use snapshot isolation / first-committer-wins.** This rejects direct write/write conflicts but leaves cross-object write skew. It is sufficient only when the application's invariants decompose along the conflict keys or another mechanism checks the remaining invariants.
- **Validate or serialize only authority-changing transitions.** Readers can remain cheap and snapshot-oriented while edits, generation selection, and acceptance cross a narrow compare-and-swap or validation boundary. This is attractive for Anneal because expensive compiler/prover work can run outside the critical section, but it is sound only if the dependency set being validated is complete and hidden ambient inputs are excluded or explicitly trusted.

PostgreSQL SSI is useful counterevidence to any claim that serializability is free: its paper discusses dependency-state memory, false-positive aborts, and special treatment for read-only safe snapshots. Anneal should therefore not demand one strongest global consistency level by default. It should state the guarantee required by each operation and pay the synchronization/tracking cost where that guarantee affects correctness.

Basis: **primary literature** + **derived** engineering judgment.

### Conditional Anneal judgment

The defensible default is a snapshot-oriented read path plus a narrow validated authority path:

- represent each semantic query against one immutable, coherent project/prepared-environment generation;
- return that generation identity with the result, and allow older-generation answers when the caller requested or can tolerate them;
- distinguish a snapshot-valid answer from a **current** answer, and validate against current selection only when the latter matters;
- treat query-derived edits as optimistic transactions whose base generation/dependencies must still match at apply time;
- serialize or validate concurrent authority-changing operations strongly enough to exclude cross-resource write skew;
- require verification acceptance and publication to bind exact source/model/environment identity and a current generation fence; and
- keep the critical consistency mechanism small: immutable manifests/generation directories, atomic root selection, and compare-and-swap validation can realize these contracts without importing database machinery.

This judgment is conditional on Anneal being able to identify the semantic dependency closure of each operation. If opaque tools, plugins, environment variables, filesystem state, or native libraries can affect the result without appearing in the generation identity or trusted assumptions, a transaction protocol over the visible files cannot repair the missing input model. That is an input-closure problem, not a concurrency-control problem.

Basis: **derived** from the cited literature, current Anneal design authority, and existing generation/publication experiments. This is not adopted Anneal policy.

## Boundaries

- **Not examined:** a production Anneal implementation of generation-root compare-and-swap, multi-agent editing, transaction retries, or conflict resolution. No Anneal concurrency benchmark or new execution probe was run for this report.
- **Not established:** that a scalar project generation is the uniquely correct representation. A coherent and atomically validated dependency vector can provide the same semantic guarantee.
- **Not established:** that every goal query may be stale. Whether staleness is acceptable is an operation contract; a caller may legitimately require a current/linearized answer.
- **Known not to apply:** snapshot isolation alone is not a serializability guarantee. First-committer-wins on overlapping writes does not prevent write skew over disjoint writes.
- **Known not to apply:** per-file monotonic version numbers alone do not establish that the selected versions coexisted in one coherent semantic state.
- **Known not to apply:** cancellation of stale computation is not itself a commit/rollback protocol. Correctness still depends on validating the generation of any result that reaches an authority-changing boundary.
- **Unknown:** the smallest complete dependency manifest for every future Anneal operation. Existing source/toolchain/generation reports constrain pieces of that closure, but opaque upstream and host dependencies remain a separate research problem.
- **Unsupported inference:** the PostgreSQL SSI implementation does not imply that Anneal needs predicate locks, a transaction manager, or MVCC storage. Its relevance is the demonstrated distinction between coherent snapshots and serializable multi-object effects, plus the engineering cost of enforcing the stronger property.

## Evidence

### Optimistic concurrency control

Kung, H. T. and Robinson, J. T. “On Optimistic Methods for Concurrency Control.” *ACM Transactions on Database Systems* 6(2), 1981. DOI `10.1145/319566.319567`.

Primary PDF: `https://db.cs.cmu.edu/papers/1981/kung-tods1981.pdf`.

The read/validation/write phase structure and restart-on-failed-validation rule are used as the primary basis for the query-then-edit analogy. Evidence role: **primary literature**.

### Linearizability

Herlihy, M. P. and Wing, J. M. “Linearizability: A Correctness Condition for Concurrent Objects.” *ACM Transactions on Programming Languages and Systems* 12(3), 1990. DOI `10.1145/78969.78972`.

Primary PDF: `https://cs.brown.edu/people/mph/HerlihyW90/p463-herlihy.pdf`.

The report uses the paper's operation-level real-time consistency definition and locality result. It does not equate linearizability with transaction serializability. Evidence role: **primary literature**.

### Snapshot isolation and write skew

Berenson, H.; Bernstein, P.; Gray, J.; Melton, J.; O'Neil, E.; O'Neil, P. “A Critique of ANSI SQL Isolation Levels.” SIGMOD 1995 / Microsoft Research MSR-TR-95-51. DOI `10.1145/223784.223785`.

Primary report: `https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-95-51.pdf`.

The report uses the paper's snapshot-isolation definition, first-committer-wins rule, and non-serializable write-skew examples. Evidence role: **primary literature**.

### Serializable Snapshot Isolation in PostgreSQL

Ports, D. R. K. and Grittner, K. “Serializable Snapshot Isolation in PostgreSQL.” *Proceedings of the VLDB Endowment* 5(12), 2012.

Primary paper: `https://www.vldb.org/pvldb/vol5/p1850_danrkports_vldb2012.pdf`.

The report uses the PostgreSQL authors' description of dangerous-structure detection, abort/false-positive tradeoffs, read-only safe snapshots, and memory costs. These are implementation and author-evaluation facts for PostgreSQL SSI, not Anneal measurements. Evidence role: **primary implementation paper**.

### Anneal design authority

Repository: `google/zerocopy`
Revision: `cc135f46155b72e4b51188525c2974a3b84acf92`

- `anneal/PRINCIPLES.md`, blob `d5339a95254eae14ac201139d07d9d36d48a19fb`: Anneal's success promise, explicit trust, and fail-closed direction.
- `anneal/DESIGN.md`, blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`: precise result identity/scope, evidence limits, abstraction-boundary semantics, and deliberate non-decisions about mechanisms.

Evidence role: **project design authority** for applicability only. The MVCC/OCC mechanism choice remains derived analysis.

### Existing Anneal generation and interactive evidence

Repository: `google/zerocopy`
Reference revision: `30b9d5749aed6049d949f4f582dd64c70088d07a`

- `reports/anneal-3731-real-generation-publication-v4-30-0-rc2/REPORT.md`, blob `41015b04602e083e1266c2281d49918317d022d8`: staged complete-generation publication, mixed in-place inventories, and old-proof acceptance during several mixed states.
- `reports/anneal-interactive-model-probes-2026-09-29/REPORT.md`, blob `b8a3bcfe788a8c18b873caa540824b69d79c58f0`: content identity versus causal generation and controlled mixed-generation reads through a mutable pointer versus a pinned immutable generation.
- `reports/lsp-proof-assistant-architecture-2026-09-27/REPORT.md`: client-owned open-document snapshots, document versions, dependency-generation separation, cancellation boundaries, and reconstruction semantics.

Evidence role: **execution/source evidence already preserved by the reference corpus**. These reports demonstrate concrete Anneal-relevant coherence hazards. They do not themselves establish the J050 database-theory judgment.

### Evidence-role separation

The database papers define or analyze concurrency models. Current Anneal reports establish bounded source/execution facts about generation and interactive state. The operation matrix and recommended Anneal consistency contracts are **derived** by combining those sources. No source claims that its own mechanism should be adopted by Anneal.

## Revalidation

For the literature layer, revalidation is cheap because the identified papers are immutable publications. A future correction should revisit the cited definitions if this report begins to equate linearizability, serializability, and snapshot isolation, or if it attributes stronger anomaly prevention to first-committer-wins than the papers establish.

For Anneal, revalidate the conclusion whenever the project changes how it names semantic generations, applies edits, publishes generated environments, accepts verification results, or permits concurrent writers. The narrow checks are:

1. **Read snapshot:** start a query on generation A, publish B while it runs, and verify that the result is either explicitly A-scoped or rejected before being labeled current.
2. **Mixed generation:** attempt to observe a multi-component semantic state while publication changes the selected generation; verify that an authoritative reader pins one admitted generation rather than mixing components.
3. **Optimistic edit:** query under A, advance the relevant dependency to B, then submit the A-derived edit. The apply boundary must reject/rebase/recompute rather than silently applying under B.
4. **Write skew:** construct two concurrent authority-changing operations with disjoint write keys but one cross-resource invariant. Verify that both cannot commit if their combined result violates the invariant.
5. **Hidden dependency:** perturb a semantic input not represented by the proposed generation/dependency identity. If an authoritative result changes without invalidation, the input model is incomplete and stronger transaction isolation will not fix it.

When these checks can be satisfied by immutable generation manifests, atomic root selection, and compare-and-swap validation, adding a database or general transaction engine would be unnecessary mechanism. If future Anneal state becomes independently mutable at many authorities, revisit whether the narrow boundary still supplies a serial order or whether a richer transaction/coordination layer has become justified.