# Netstack3 architecture evolution: boundaries, lifecycle, static state, and concurrency

## Summary

Netstack3's history supports a narrower architectural lesson than either "make
invalid states unrepresentable" or "put every subsystem behind an asynchronous
service." Four choices survived substantial change:

1. protocol semantics and platform integration remain separated even though the
   original single core crate became a collection of core crates and the exact
   context traits changed;
2. identity, operational eligibility, and object lifetime are treated as
   different concerns, with strong/weak references, destruction markers, and
   deferred removal where a name can outlive permission to start new work;
3. static types are used aggressively for stable local invariants, but Netstack3
   has deliberately collapsed typestate-like socket identities when stateful
   identities had to survive transitions across APIs; and
4. authority over shared protocol state is serialized at specific lock/critical
   sections while computation, bindings work, and state projection can proceed
   concurrently. Netstack3 did not replace ordinary core calls with actors at
   every layer.

Those conclusions matter to Anneal only conditionally. Anneal can preserve a
semantic boundary between verification state and orchestration without binding
that boundary to one crate, trait hierarchy, process, or RPC interface. It can
also distinguish a stable workspace or generation identity from a liveness
handle and from permission to publish new work. Types are most valuable for
durable invariants such as validated identities and capability classes; mutable
lifecycle states are better represented dynamically when callers need one stable
identity across transitions. Finally, Anneal has evidence for serializing
authority-changing transitions—publishing a generation, moving the current
pointer, retiring a prepared environment—without serializing all proof and build
computation or requiring mailbox semantics between every stage.

The history does **not** show that these are universal rules. Networking has
hard real-time ordering, teardown, packet-flow, and watcher requirements that
Anneal does not share. Netstack3 also paid real costs for trait indirection,
public-path churn, lock ordering, reference-counted lifetime machinery, and
dynamic error states. The transferable lesson is to preserve semantic ownership
and explicit lifecycle/ordering contracts while allowing the mechanism that
implements them to change.

This report provides judgment-driven coverage for google/zerocopy issue #3732
questions J001-J004.

## Applicability

The report combines a current architectural snapshot with selected historical
changes that discriminate among competing explanations of Netstack3's design.

The current design evidence is from Fuchsia revision
`c480400b0e6cb9a9b36384935639fb3e6566bd68`, observed on 2026-09-30, especially
the Netstack3 design documents under
`src/connectivity/network/netstack3/docs/`. Those documents include older
wording—for example, `CORE_BINDINGS.md` still describes "two crates" even though
the current source tree contains multiple core crates. This report therefore
uses the documents for stated goals and decision rationale, but checks
implementation evolution against historical commits and later source.

The historical evidence spans:

- `4ccfe9e3c10662b8dea3ccbf020553ebfa179ff3` (2023-06-01), which deliberately
  replaced multiple UDP socket IDs with one opaque ID and introduced runtime
  invalid-operation errors;
- `40ce8a08f2ffa1e9babc8e5b6aaa14cf486c0c6d` (2023-07-08), which moved TCP
  handshake status from bindings into core because core was the source of truth;
- the 2024 extraction of IP and device functionality into `netstack3_ip` and
  `netstack3_device`, including Fuchsia revisions
  `afe2e7ac4506c2f272c1b4a940cd2206b5756c19` and
  `a06fa769e2417889de925accc793d4e527280bc1`;
- `1e9fb101ed58968f5b4cf0b67a439f8cb0479b9d` (2024-07-23), which represented
  multicast-forwarding enablement as dynamic enum state so disabling it purges
  all forwarding state; and
- `09c560576ca357ffc0853c6251048af2a61b1543` (2026-06-23) plus nearby 2026
  source, which shows strong/weak resource references and deferred socket
  destruction as live production concerns.

"Core" in this report means the platform-independent protocol/state side of the
architectural boundary, not one specific Cargo crate. "Bindings" means the
platform integration side that connects core semantics to Fuchsia execution,
FIDL, host resources, and other platform-specific behavior.

The Anneal judgments below are derived comparisons. They are not decisions
adopted by Anneal's `PRINCIPLES.md` or `DESIGN.md`. Netstack3's workload differs
materially from Anneal's: it handles long-lived concurrent network resources,
packets, timers, and externally observable state streams, while Anneal's
dominant objects are source revisions, generated artifacts, proof environments,
verification jobs, and publication generations.

## Findings

### J001 — The semantic core/bindings boundary survived; its crate shape did not

Netstack3's core/bindings document states a clear original separation. Core owns
most protocol logic and is platform-agnostic. Bindings connect that logic to a
concrete platform and decide when to call core functions. The document compares
the design with a functional-core/imperative-shell architecture, but immediately
qualifies the analogy: core itself has mutable state. The stated benefits are
testability through fake environments, early input validation, and freedom for
bindings to choose an execution model subject to the thread-safety constraints
of core's data structures.

Basis: **documentation** at Fuchsia
`c480400b0e6cb9a9b36384935639fb3e6566bd68`,
`src/connectivity/network/netstack3/docs/CORE_BINDINGS.md`.

That semantic separation persisted even as its implementation ceased to fit the
document's "two crates" description. In 2024 Netstack3 split IP functionality
into a separate `netstack3_ip` crate and device functionality into
`netstack3_device`. The cleanup after the IP split explicitly reorganized the
old core IP module because IP was now a separate crate. The device split also
introduced new lock-ordering relationships and supporting base definitions.
Current source imports protocol-specific crates such as `netstack3_ip`,
`netstack3_tcp`, `netstack3_device`, and `netstack3_base` while the top-level
Fuchsia netstack still serves as bindings.

Basis: **source/history**; Fuchsia revisions
`afe2e7ac4506c2f272c1b4a940cd2206b5756c19` and
`a06fa769e2417889de925accc793d4e527280bc1`, with the corresponding public
integration-roll records preserving the original Fuchsia revisions.

This history is evidence against treating crate boundaries as architectural
authority. The useful boundary is ownership of semantic facts and external
effects. Netstack3's own current tenets say to define API boundaries by asking
which module owns the state and what work is being performed. Context traits
enumerate dependencies such as state access, timers, packet transmission, and
counters so an implementation need not know the rest of the stack.

Basis: **documentation** at current Fuchsia revision,
`TENETS_AND_DESIGN_DECISIONS.md`, "Define API boundaries with traits".

The boundary also moved when semantic ownership demanded it. In 2023 TCP
handshake status moved from bindings into core. The change states its reason
directly: core had become the source of truth for connection status, so bindings
no longer needed to maintain a second typed view of that state. The move also
enabled later socket-ID simplification.

Basis: **source/history**, Fuchsia
`40ce8a08f2ffa1e9babc8e5b6aaa14cf486c0c6d`.

A competing account would say that Netstack3 mainly demonstrates the value of a
stable platform-independent library API. That is only partly supported. The
current tenets explicitly accept brittleness in the public module hierarchy
while the project is in a monorepo because code movement can be fixed
atomically. Netstack3 preserved the responsibility split more consistently than
it preserved public Rust paths, crate membership, or trait taxonomy.

Basis: **documentation**,
`TENETS_AND_DESIGN_DECISIONS.md`, "Core crate public API".

**Conditional judgment for Anneal (J001).** Anneal should preserve semantic
ownership boundaries, not mechanically preserve a current crate/process/trait
layout. A useful boundary says which component owns verification meaning,
artifact identity, publication authority, or platform orchestration and which
direction information may cross. That contract can survive moving code between
crates or changing an in-process trait to an out-of-process protocol. Conversely,
if only one layer can maintain a fact coherently—as core eventually did for TCP
connection status—keeping a shadow copy across a historical boundary is worse
than moving ownership.

The analogy is strongest for facts whose authoritative owner is unambiguous:
current-generation identity, proof-result meaning, artifact provenance, and
publication state. It is weaker for merely convenient implementation grouping.
Nothing in the Netstack3 evidence implies that Anneal's Rust/Charon/Aeneas/Lean
boundaries should match its software-module boundaries.

### J002 — Identity, liveness, operational eligibility, and reclamation are separate

Early Netstack3 documentation records a simple ownership-friendly strategy:
pass `HashMap` keys where another language might pass pointers. This avoids
having aliases into map entries while whole state is mutably borrowed, but it
requires repeated map lookups. The same document considered
`Rc<RefCell<T>>` as a faster direct-reference alternative and called out its
heap-allocation and cache-locality costs.

Basis: **documentation**, current `IMPROVEMENTS.md`, "Pervasive use of
`HashMap`s". The document labels these as speculative improvement ideas rather
than implemented commitments.

Later/current code uses explicit primary, strong, and weak references for
long-lived resources. TCP socket IDs contain a strong reference; they can be
downgraded to weak IDs. The socket set owns a primary reference. Destruction can
remove the primary while strong users remain, in which case final destruction is
deferred. A weak reference can continue to identify the resource for
notification/debugging without keeping it alive.

Basis: **source** around 2026 Netstack3 TCP and resource-reference code,
including `src/connectivity/network/netstack3/core/tcp/src/socket.rs` and
`core/base/src/resource_references.rs`; **history** in
`09c560576ca357ffc0853c6251048af2a61b1543`.

TCP teardown has an additional operational state that is neither "object exists"
nor "object is fully gone." The socket-set `DeadOnArrival` entry handles a race
where an accepted connection is closing before the listener has finished
inserting it into the global socket set. Current code also marks a resource for
destruction and may report `RemoveResourceResult::Deferred` until outstanding
references drain. The primary reference must be dropped under the socket-set
lock to avoid a race that could leave the wrong entry behind.

Basis: **source** in 2026 TCP socket code; the comments describe the race and
the lock requirement directly.

This gives four concepts that are easy to conflate:

1. **identity** — which resource is being named;
2. **retention/liveness** — whether a reference keeps the resource allocated;
3. **operational eligibility** — whether new operations/upgrades are still
   accepted after destruction begins; and
4. **reclamation completion** — whether the last retaining user has drained and
   state can be destroyed.

A resource can therefore remain identifiable while it no longer accepts new
work, and physical reclamation can occur later still.

Basis: **derived** from the primary/strong/weak and deferred-destruction
mechanisms above.

The networking-specific mechanism is not itself a general prescription. TCP has
races between passive-open insertion, close, demultiplexing, timers, and
diagnostic observers. Anneal does not automatically need per-object reference
counting or an exact analog of `DeadOnArrival`.

**Conditional judgment for Anneal (J002).** Anneal should nevertheless keep the
four concepts separate. A workspace ID or generation ID should name an object;
it need not itself retain every backing resource. A worker/environment handle can
serve as a liveness lease. Retirement should prevent new authority-bearing work
from being attached to an old generation before storage is necessarily deleted.
Garbage collection should wait for the readers/handles whose semantics require
that generation.

For in-process state, Rust ownership/refcounts may implement that contract. For
cross-process workers, caches, or durable artifacts, refcounts are insufficient:
Anneal may need generations, leases, durable reachability, or explicit garbage
collection. Netstack3's transferable lesson is the separation of responsibilities,
not its exact `PrimaryRc` implementation.

### J003 — Static types won for durable invariants, not for every protocol state

Netstack3's static-typing document gives a strong positive case for invariant
types. `AddrSubnet<A>` packages related address/subnet constraints. Once a caller
has constructed that value, deeper functions can rely on the invariant instead
of repeatedly validating raw fields. Fallible construction also pushes validation
toward the external-input boundary and prevents distant panics from becoming
denial-of-service paths.

Basis: **documentation**, current `STATIC_TYPING.md`.

Context traits offer a different use of static structure. They enumerate the
capabilities and state dependencies a module needs. This limits accidental access,
improves testability, and makes assumptions auditable.

Basis: **documentation**, current `TENETS_AND_DESIGN_DECISIONS.md`.

Those successes did not produce a rule that every operational state belongs in
a distinct Rust type. In June 2023 Netstack3 deliberately combined previously
distinct UDP socket IDs into one opaque `UdpSocketId`. The commit message says
what was lost: invalid transitions such as binding an already-connected socket
had previously been prevented by the type system, so the unified identity
required new runtime error types.

Basis: **source/history**, Fuchsia
`4ccfe9e3c10662b8dea3ccbf020553ebfa179ff3`.

That change was part of a broader simplification. The immediately preceding work
temporarily removed ICMP socket bindings rather than forcing an unrelated
protocol through the same transformation while UDP identity was being
restructured. In July 2023 TCP handshake status moved from bindings to core so
bindings would no longer need to remember a socket's state-specific type,
explicitly helping a later TCP socket-ID merge.

Basis: **history**, including
`495c194f4a8aabce4b04c7565a7a9d06a8a5462c` and
`40ce8a08f2ffa1e9babc8e5b6aaa14cf486c0c6d`.

The later multicast-forwarding design shows a middle ground. Enabling/disabling
forwarding is represented as an enum holding all forwarding state. Disabling
switches the dynamic value and thereby purges the route/pending tables. The
invariant is strong, but the operational state is a runtime variant rather than
a typestate parameter propagated through callers.

Basis: **source/history**, Fuchsia
`1e9fb101ed58968f5b4cf0b67a439f8cb0479b9d`.

The strongest competing account is that the UDP change was merely an ergonomic
exception to an otherwise static-typing-first architecture. The evidence supports
part of that claim: Netstack3 still uses static types heavily. But the exception
is architecturally informative because the commit knowingly trades compile-time
transition exclusion for one stable opaque identity plus runtime errors. The
project's actual choice is therefore conditional, not ideological.

**Conditional judgment for Anneal (J003).** Anneal should use static types for
states whose invariant is stable, local, and valuable to downstream reasoning:
a validated digest, an immutable artifact handle, a capability that can only be
constructed after verification, or a distinction between trusted and untrusted
inputs. It should be cautious about a typestate product over mutable lifecycle
phases such as `pending × prepared × current × stale × failed × retired`,
especially when clients must retain one logical identity across transitions.

A dynamic enum plus explicit transition checks can be stronger overall when it
centralizes the state machine and keeps identity stable. Anneal should choose
between the two based on who must carry the distinction and how frequently the
state changes, not on a blanket preference for "more static" modeling.

### J004 — Netstack3 serializes specific authority transitions, not the whole architecture

The older control-flow design prioritized synchronous call chains. A worker
observed an event source and processed one event through ordinary function calls
that updated core state, emitted outputs, and scheduled timers before returning.
The advantage was direct control flow instead of pervasive callbacks or
schedulers. The original execution model was intentionally simple and
single-threaded.

Basis: **documentation**, `CONTROL_FLOW.md` and `IMPROVEMENTS.md`.

`IMPROVEMENTS.md` also records the cost anticipated from the beginning:
long-running state changes could stall the event loop, and high packet volume
could exceed a single thread's throughput. Read-copy-update or other read-optimized
designs were listed as possibilities, but the document explicitly says those are
ideas without concrete plans. It also notes that even an RCU-style system would
still need mutation/synchronization around connection-local state such as TCP.

Basis: **documentation**, current `IMPROVEMENTS.md`, with its explicit speculative
status.

The project subsequently moved away from the assumption of exclusive whole-stack
state. Current tenets explain that early Netstack3 passed one state structure by
shared or mutable reference because it assumed a single-threaded environment,
and that the project was actively moving to shared state. API boundaries should
not require exclusive access; callback-style `with_state` access can hide
interior-mutability/guard mechanics. Current lock-order guidance is based on
contention rather than a simplistic "fine before coarse" hierarchy.

Basis: **documentation**, current `TENETS_AND_DESIGN_DECISIONS.md`.

This evolution still did not make core an actor graph. Ordinary core APIs remain
direct function calls over context/state capabilities. Asynchronous channels are
used selectively where they solve a concrete projection problem. Core emits
state-delta events inside critical sections so their order is linear with the
state change; bindings typically enqueue those events into an order-preserving
channel and reconstruct FIDL-visible state later without holding core locks. The
same design document explicitly warns that these event handlers are state-keeping
observers, not callbacks for arbitrary side effects.

Basis: **documentation**, current `TENETS_AND_DESIGN_DECISIONS.md`, "Expose state
deltas through events dispatched from Core".

The TCP destruction race gives a more concrete current example. The socket-set
lock serializes primary-reference removal and the `DeadOnArrival` transition
because releasing that lock at the wrong point can leave an inconsistent socket
entry. Other work around the socket proceeds independently. This is localized
serialization around authority/state transition, not global single-threading.

Basis: **source**, 2026 TCP socket code.

A competing design would put each resource or subsystem behind an actor/mailbox.
That can simplify exclusive ownership and failure isolation, but it also moves
ordering, backpressure, cancellation, and state duplication into asynchronous
protocols. Netstack3 uses channels for some observable-state projection precisely
where those semantics help, while preserving direct synchronous calls for most
protocol logic. Its evidence therefore argues against treating either "everything
under one lock" or "everything is an actor" as a default architectural law.

**Conditional judgment for Anneal (J004).** Anneal has a similar opportunity to
serialize small authority-changing transitions while retaining concurrency
elsewhere. Publication of a new current generation, movement of a current pointer,
retirement of an environment, or commitment of a durable result should have an
explicit linearization point. Translation, proof search, validation, and queries
against immutable snapshots can remain concurrent when their inputs are fixed.

Events/messages can project a committed transition to UI or monitoring consumers,
but Anneal does not need to make Rust parsing, Charon, Aeneas, Lean, and every
workspace manager separate actors merely to gain concurrency. Actor/process
boundaries should be justified by ownership, fault isolation, cancellation, or
resource-control needs that synchronous calls cannot satisfy.

### The four questions reinforce one model without collapsing into one mechanism

J001-J004 share a common pattern: preserve the **meaning** of a boundary while
allowing its representation to evolve.

- The core/bindings boundary persisted while core crate decomposition changed.
- Resource identity persisted while ownership changed from map keys toward
  primary/strong/weak references and deferred reclamation.
- Static invariant types persisted while some protocol typestates were collapsed
  into stable IDs plus runtime states.
- Ordered authority transitions persisted while whole-stack exclusive access gave
  way to finer-grained shared state and lock ordering.

That pattern is stronger than any individual Netstack3 mechanism. It supports
Anneal designing explicit semantic ownership, lifecycle, and linearization
contracts first and choosing crates, enums, generics, locks, processes, or
channels second.

Basis: **derived synthesis** of the evidence above.

## Boundaries

**This is not a performance study.** The report does not establish that current
Netstack3's concurrency architecture outperforms its original single-threaded
model, nor that an actor implementation would be slower. The early RCU discussion
was speculative and is preserved as an alternative considered, not an implemented
benchmark result.

**The current docs contain historical wording.** `CORE_BINDINGS.md` still describes
one core crate and one bindings crate even though current Netstack3 has several
core crates. This report treats that discrepancy as evidence that the semantic
boundary outlived the crate topology, not as proof that the documentation is
fully current in every implementation detail.

**No claim that static typing was abandoned.** Netstack3 still explicitly favors
invariant-carrying types and context traits. The UDP socket-ID change demonstrates
a limit to typestate/state-specific identities, not a rejection of static typing.

**No claim that runtime errors are preferable in general.** The socket-ID merge
accepted runtime invalid-operation errors to simplify a stateful identity surface.
That tradeoff is only useful where a stable identity across transitions is worth
more than compile-time exclusion at every call site.

**Reference counting is not a durable distributed lease.** Netstack3's
primary/strong/weak reference machinery is in-process Rust state. Anneal cannot
infer cross-process cache or artifact liveness from the same mechanism.

**Network lifecycle is unusually demanding.** TCP teardown races, packet
demultiplexing, timers, route changes, and FIDL watchers impose ordering and
draining constraints that may not exist for an Anneal artifact. The report
transfers the conceptual separation of identity/liveness/eligibility/reclamation,
not every state transition.

**Current code changes rapidly.** Current-source claims are pinned to the cited
2026 snapshots and current design-doc revision. Later Fuchsia changes should be
revalidated rather than inferred continuous.

**The report does not settle Anneal architecture.** Its Anneal judgments are
conditional applications of Netstack3 history under the current Anneal
principles/design constraints. They do not create policy in `anneal/PRINCIPLES.md`
or `anneal/DESIGN.md`.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-30.

### Current architectural documentation

Fuchsia repository `fuchsia/fuchsia`, current snapshot observed at
`c480400b0e6cb9a9b36384935639fb3e6566bd68`:

- `src/connectivity/network/netstack3/docs/CORE_BINDINGS.md` — stated
  core/bindings responsibilities, functional-core analogy and its mutability
  caveat, testability, early validation, and bindings-owned execution model.
- `src/connectivity/network/netstack3/docs/STATIC_TYPING.md` — invariant types,
  fallible construction, and validation-at-input-boundary rationale.
- `src/connectivity/network/netstack3/docs/TENETS_AND_DESIGN_DECISIONS.md` —
  mutable tenets; context-trait boundaries; move away from exclusive state;
  ordered core-emitted state deltas; Netstack2 compatibility; public module-path
  tradeoff; contention-aware lock ordering.
- `src/connectivity/network/netstack3/docs/IMPROVEMENTS.md` — explicitly
  speculative single-thread performance concerns, RCU/read-optimized
  alternative, and HashMap-key versus reference-counted-pointer tradeoffs.
- `src/connectivity/network/netstack3/docs/CONTROL_FLOW.md` — direct
  event-to-synchronous-call-chain design and historical single-threaded model.

The docs directory tree was also observed directly under `refs/heads/main`.
These documents state rationale but are not assumed to describe every current
crate or implementation detail literally.

### Historical implementation changes

- Fuchsia `4ccfe9e3c10662b8dea3ccbf020553ebfa179ff3`,
  `[netstack3] Combine UDP socket IDs`, 2023-06-01. The commit explicitly says
  the unified opaque ID requires runtime errors for operations previously
  rejected by the type system.
- Fuchsia `495c194f4a8aabce4b04c7565a7a9d06a8a5462c`, 2023-05-31,
  temporary ICMP-bindings removal in service of the UDP/socket-ID overhaul.
- Fuchsia `40ce8a08f2ffa1e9babc8e5b6aaa14cf486c0c6d`,
  `[netstack3] Move handshake status tracking from Bindings to Core`,
  2023-07-08. The commit states that core is the source of truth and the move
  helps merge TCP socket IDs.
- Fuchsia `afe2e7ac4506c2f272c1b4a940cd2206b5756c19`, 2024-05,
  cleanup after splitting IP into `netstack3_ip`; public integration history
  preserves this original revision.
- Fuchsia `a06fa769e2417889de925accc793d4e527280bc1`, 2024-05,
  device-crate extraction; public integration history preserves this original
  Fuchsia revision.
- Fuchsia `1e9fb101ed58968f5b4cf0b67a439f8cb0479b9d`,
  `[netstack3] Support enabling multicast forwarding`, 2024-07-23. The commit
  stores forwarding state in an enabled/disabled enum so disabling purges all
  forwarding state.
- Fuchsia `09c560576ca357ffc0853c6251048af2a61b1543`,
  `[netstack3] Add socket destruction notifications API`, 2026-06-23. The
  change touches shared resource-reference, TCP/UDP/datagram, bindings, and
  diagnostics code and shows deferred destruction/reference lifecycle remains
  an active production concern.

### Implementation snapshots

- TCP socket implementation at Fuchsia
  `d8e2be4f1380f1bcd25f1f1b4f9909f10760485c`,
  `src/connectivity/network/netstack3/core/tcp/src/socket.rs`: `PrimaryRc`,
  `StrongRc`, `WeakRc`, `TcpSocketSetEntry::DeadOnArrival`, destruction
  marking, and deferred removal.
- A nearby 2026 TCP implementation snapshot
  `a3c17a4d6b3140f9175d6cf6ac4eb4e775f8dea8` contains the same
  primary/strong/weak ownership model and detailed destruction-race comments.
- `09c560576ca357ffc0853c6251048af2a61b1543` adds public socket-destruction
  notification plumbing across base/core/bindings and is used as historical
  confirmation that deferred destruction is not merely old test machinery.

### Evidence-role distinctions

The current design documents are **documentation**: they describe intended
architecture and rationale but some implementation nouns are stale. The exact
commits and source files are **source/history** evidence. The Anneal conclusions
are **derived**. No new Netstack3 benchmark or runtime experiment was executed
for this report.

## Revalidation

For a later Netstack3 revision, revalidate the four conclusions with narrow
checks rather than repeating the whole history.

1. **Boundary survival (J001).**
   - Read the latest `CORE_BINDINGS.md` and current top-level/core crate graph.
   - Locate the top-level bindings context and protocol-facing core APIs.
   - Check where platform/FIDL/execution state lives and where protocol truth
     lives.
   - If a formerly bindings-owned semantic fact has moved, inspect the commit
     rationale rather than treating movement itself as boundary erosion.

2. **Identity/liveness (J002).**
   - Search for `PrimaryRc`, `StrongRc`, `WeakRc`, destruction markers, and
     `RemoveResourceResult`.
   - Inspect device and TCP/UDP resource-ID implementations and one removal path.
   - Confirm whether weak IDs can identify resources after new operations have
     been prohibited and whether reclamation can still be deferred.

3. **Static versus dynamic state (J003).**
   - Recheck invariant types such as `AddrSubnet`.
   - Inspect current socket IDs and multicast/other enablement state.
   - Search history for any reintroduction of state-specific socket IDs or
     replacement of runtime state errors with typestate. If that happens, revisit
     the cost judgment rather than assuming the 2023 choice generalized.

4. **Concurrency model (J004).**
   - Read the current exclusive-access tenet and lock-order guidance.
   - Inspect whether core calls remain direct/synchronous and where channels are
     used.
   - Check a resource teardown transition and a state-delta event path for the
     actual linearization mechanism.
   - If Netstack3 adopts RCU, pervasive actors, or another ownership model, compare
     the implementation and measured motivation with the speculative
     `IMPROVEMENTS.md` proposal rather than treating the proposal as precedent.

For Anneal, the cheapest revalidation is not to track Netstack3 mechanically.
Revisit this report only when an Anneal design decision depends on one of its
conditional judgments: moving a semantic boundary, choosing handle/liveness
semantics, encoding lifecycle state in types, or deciding where to linearize
concurrent authority changes.