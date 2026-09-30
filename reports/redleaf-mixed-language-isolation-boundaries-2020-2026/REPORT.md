# Isolation boundaries across RedLeaf, Rust-for-Linux, and Anneal tool processes

## Summary

"Isolation" names several different guarantees. RedLeaf's OSDI 2020 design separates them unusually clearly: Rust memory safety is the starting point, but fault isolation also needs a restricted component language, validated cross-domain interfaces, mediated sharing, ownership tracking, liveness checks, panic containment, and resource reclamation. Its lesson is therefore not that a safe language eliminates isolation machinery. It is that a language can replace some hardware protection only when the entire communication and resource model is designed around the language's guarantees.

The Linux kernel's Rust architecture draws a different boundary. Leaf Rust code is kept away from raw C bindings and uses reviewed, as-safe-as-possible abstractions. Current `ForeignOwnable` APIs make the remaining foreign ownership protocol explicit: a raw pointer may cross into C, but uniqueness, borrow lifetimes, and eventual reclamation remain safety obligations that the Rust type system cannot enforce while C owns the value. This concentrates unsafety without pretending the foreign implementation has become safe by type annotation.

For Anneal, these systems support a conditional judgment. An opaque Charon, Aeneas, Lean, OCaml, C, or native-plugin stage should default to an operating-system process boundary when crash containment and reset semantics matter. A process boundary is robust to implementation-language unsafety, but it is not a complete sandbox and it does not establish result freshness, artifact identity, or cleanup of external effects. Anneal should pair process isolation with generation-scoped inputs and outputs, explicit source/model identities, process-tree cleanup, and fenced publication. In-process integration is reasonable only when the embedded component's mutable global state, FFI/native surface, reentrancy, cleanup, and reset semantics are understood well enough to replace the coarse process-lifetime contract.

The transferable abstraction is thus a **narrow checked boundary**, not a specific mechanism. RedLeaf shows what extra machinery is required before a language boundary can carry fault-isolation claims. Rust-for-Linux shows how to localize foreign unsafety behind explicit contracts. Process isolation supplies a conservative reset and address-space boundary for opaque tools. None of the three, by itself, proves that an Anneal result belongs to the current Rust source or current proof environment.

## Applicability

The RedLeaf findings apply first to the architecture described in *RedLeaf: Isolation and Communication in a Safe Operating System*, OSDI 2020, USENIX paper 258949. The paper remains the authority for publication-era mechanism, rationale, and evaluation claims. The public `mars-research/redleaf` repository also has a branch named `osdi20_camera_ready`; on 2026-09-30 that branch pointed to immutable commit `08753faee652495f55fc8cbb420e5123a183affc`. That commit is useful source-level corroboration of the paper's boundary machinery, but it was committed on 2021-02-20 and the branch name itself is mutable. This report therefore does not treat it as the exact OSDI 2020 artifact or use it to silently strengthen historical claims beyond the paper.

The Linux findings apply to `torvalds/linux@551c722f40809618230001baccf219193e22fc5a`, specifically the Rust documentation and interfaces identified under **Evidence**. This is a contemporary comparison, not a claim that current Linux Rust architecture caused or descended from RedLeaf.

The Anneal judgment is derived against `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, especially `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`. Those files remain authoritative over this report. The recommendation here is analysis for issue #3732 J007, not adopted Anneal design policy.

"Process isolation" in the comparison means a separately managed operating-system process with a lifecycle boundary that Anneal can terminate and recreate. It does not imply a security sandbox, separate machine, container, seccomp policy, namespace policy, privilege drop, or protection from a hostile same-user process unless those mechanisms are separately configured and justified.

The report also uses current `reference` corpus component evidence at `google/zerocopy@e1c4cf18da52136936eec8d6361607a9036adcb9`. The four cited adjacent packages were reread at that tip on 2026-09-30. Those probes establish bounded behavior of Anneal's selected tools. They do not convert the broader architectural comparison into an execution result.

## Findings

### Memory safety, fault containment, authority confinement, and freshness are different properties

A useful comparison starts by separating four questions that are often collapsed into "isolation."

1. **Memory and crash containment:** can one component corrupt another component's memory or crash it directly?
2. **Authority confinement:** which files, devices, syscalls, network endpoints, handles, or other resources can the component affect?
3. **Ownership and cleanup:** after cancellation or failure, who can reclaim resources, and which shared or transferred objects remain valid?
4. **Semantic/session freshness:** can a result from an old source version, environment, generation, or request be mistaken for the current one?

RedLeaf primarily addresses the first and third questions within a single address space, with a controlled communication architecture. Rust-for-Linux primarily narrows the unsafe foreign-interface boundary and makes ownership contracts reviewable. An ordinary subprocess gives a coarse answer to memory/crash containment and a useful lifetime boundary, but its ambient authority may still be broad. Anneal's generation and source/model correspondence rules address the fourth question.

These mechanisms are complementary. Choosing one does not discharge the others.

Basis: RedLeaf published architecture + Linux documentation/source + Anneal design contract + derived comparison.

### RedLeaf explicitly rejects the inference that safe Rust alone provides fault isolation

RedLeaf begins from a stronger premise than Anneal can assume for arbitrary compiler components: domains are constrained to safe Rust, while unsafe Rust is confined to a small microkernel and trusted low-level libraries. Even under that premise, the paper says language safety alone is insufficient for mutually distrusting computations.

The reason is state after failure. A panic can leave a domain's internal state inconsistent. Objects may have been transferred into or out of the domain. Kernel resources may have been allocated. Other threads may be in cross-domain calls. Fault isolation therefore requires a protocol for stopping entry, unwinding active calls, preserving objects that have left the failed domain, reclaiming resources still owned by it, and making later calls fail rather than silently entering damaged state.

This is the first important negative result for Anneal: **memory-safe implementation is not a substitute for a failure and ownership protocol**. Even a hypothetical all-Rust translator still needs explicit request lifetime, shared-state, cancellation, and stale-result semantics if Anneal expects it to behave like an isolated service.

Basis: RedLeaf OSDI 2020 sections on design requirements, fault isolation, and recovery; derived Anneal implication.

### RedLeaf's language-based domains work because communication is constrained and mediated

RedLeaf does not let arbitrary safe Rust references cross a domain boundary and then infer isolation from the compiler. It introduces a domain abstraction with a deliberately constrained exchange model.

The paper's mechanism combines:

- heap isolation between domains;
- exchangeable cross-domain types;
- IDL-generated interface validation and proxy code;
- runtime liveness checks at domain calls;
- ownership bookkeeping around cross-domain transfers;
- panic catching and unwinding at domain boundaries; and
- explicit accounting for resources owned by a domain.

A thread migrates across a domain boundary rather than sending every operation through a separate process. The proxy and continuation machinery therefore preserves a direct-call programming style while adding the checks required by the isolation model.

This architecture explains both RedLeaf's low communication overhead and the price of that result. The type system is one component of a larger trusted protocol. If a caller can bypass the validated interface, if unsafe code violates the assumptions, if ownership bookkeeping is wrong, or if an external resource is not represented in that bookkeeping, the language boundary no longer establishes the advertised fault-isolation property.

For Anneal, the analogous lesson is to ask what the boundary *forbids* and what must mediate every crossing. A Rust trait around a translator is not equivalent to RedLeaf's domain boundary unless it also closes the relevant escape hatches.

Basis: RedLeaf published mechanism; derived boundary comparison.

### The paper-associated RedLeaf source makes the bookkeeping cost concrete

The `osdi20_camera_ready` branch supplies source-level corroboration of the paper's description at commit `08753faee652495f55fc8cbb420e5123a183affc`, while remaining too late to serve as an exact publication artifact. Its implementation makes the cost of a language-based fault boundary visible.

`RRef<T>` is not an ordinary Rust reference. It stores a pointer to the current owner-domain ID, a borrow-count pointer, and a raw value pointer into a shared heap. The `RRefable` auto trait explicitly excludes raw pointers, references, mutable references, and slices from the exchangeable set. Kernel heap code keeps a global table of shared allocations, records each allocation's domain owner and type identity, and implements `drop_domain` by removing allocations still owned by the failed domain, recursively invoking registered cleanup, and deallocating their bookkeeping and storage. The same source tree contains explicit proxy interfaces, continuation/unwind machinery, and an `RpcError` variant for a panicked and unwound callee.

That source supports the paper's central architectural point: zero-copy communication across a language boundary still needs explicit ownership, liveness, cleanup, and failure machinery. The ordinary Rust type system does not infer those properties from the fact that domain code is written in safe Rust.

The source also exposes residual implementation obligations. `RRef::move_to` directly writes the owner-domain field and carries a `TODO: race here` comment at this revision; the RRef implementation and trusted kernel use `unsafe` operations to implement the abstraction. Those facts do not refute the paper's architecture or establish an exploitable bug. They show why the abstraction's trusted mediation belongs in the fault-isolation argument instead of disappearing behind a safe-looking call site.

For Anneal, the transferable lesson is narrower than "use Rust types." If a handle can move between workers or generations, its transfer, liveness, cancellation, cleanup, and publication semantics need one authoritative protocol. A checked API can concentrate those obligations, but the implementation behind that API remains part of the evidence for the guarantees it claims.

Basis: RedLeaf paper + `mars-research/redleaf@08753faee652495f55fc8cbb420e5123a183affc` source + derived Anneal application.

### Mutable sharing is harder to recover than immutable sharing

RedLeaf's treatment of references is especially relevant to prepared proof environments and generated artifacts. The design avoids lending an ordinary mutable borrow across a crashable domain boundary. If the callee mutates an object and then fails, the caller cannot safely assume the object's invariant still holds. RedLeaf instead structures mutable ownership as transfer and return, while immutable sharing admits stronger recovery behavior because the failed callee could not have mutated the shared object through that reference.

The general lesson survives outside RedLeaf's heap model. Recovery is easiest when shared state is immutable or content-addressed, and when mutable state has a single explicit owner. A crash boundary cannot repair a logical invariant that several parties were allowed to mutate without a recovery protocol.

For Anneal, prepared dependencies and published generation artifacts should therefore be attractive sharing units when they are immutable. Mutable scratch output should remain generation-private until validation and publication. If an in-process backend mutates shared caches or global tables, those caches become part of its recovery and invalidation contract rather than "just an optimization."

Basis: RedLeaf sharing/recovery design + derived Anneal application.

### RedLeaf's recovery is a protocol, not rollback magic

RedLeaf demonstrates transparent device-driver recovery using additional indirection and replay. That result depends on a shadow driver that records enough initialization interaction to reconstruct the driver after failure. It does not establish that arbitrary domain state or external device state can be rolled back automatically.

The distinction matters for compiler orchestration. Restarting a process reclaims its private address space, but does not undo files already written, subprocesses that escaped the managed process tree, remote requests, device effects, or other external state. Recovery therefore needs an operation-specific account of effects.

Anneal's current component evidence already exhibits this distinction. The cross-tool cancellation probe killed observed Cargo, Charon, Aeneas, Lake, and Lean process groups and successfully retried bounded fixtures, but some interrupted stages left partial filesystem state. The report explicitly does not claim cleanup of a daemonized descendant, watcher, remote worker, or output that escaped the private directory. Process lifetime is a useful cleanup primitive, not a transactional filesystem or world-state rollback.

Basis: RedLeaf driver-recovery evaluation + `anneal-3730-cross-tool-stage-cancellation-cleanup-2026-09-29` + derived comparison.

### Nested calls are supported by RedLeaf machinery, but that is not a general reentrancy theorem

RedLeaf's call model allows migrating threads to make cross-domain calls through proxies, and the runtime tracks cross-domain continuations. Interface values can themselves participate in cross-domain communication. This is evidence that the architecture was designed for nested call structure rather than a one-way RPC graph.

The paper does not establish that arbitrary shared component state is reentrant under every callback pattern. Its safety argument depends on the validated interface and runtime protocol. A stronger "language isolation makes components reentrant" conclusion would not follow.

This boundary matters directly to Anneal. Reentrancy is a property of the component's state machine, not of whether the call is in-process or out-of-process. The current Aeneas architecture report, for example, finds process-global mutable configuration and error accumulators in the pinned OCaml library and no ready-made multi-request server lifecycle. Embedding the library can remove serialization and startup costs, but it also makes request overlap and callbacks questions that the host must answer explicitly.

Basis: RedLeaf proxy/continuation design + `aeneas-library-process-architecture-nightly-2026-06-03` + derived comparison.

### Rust-for-Linux localizes foreign unsafety instead of claiming the foreign side is safe

Current Linux Rust documentation gives a deliberately narrower promise than RedLeaf. Leaf modules such as drivers should not use generated C bindings directly. Subsystems should expose "as-safe-as-possible" Rust abstractions; direct interaction with C APIs is concentrated in reviewed abstraction code. The documentation states the condition precisely: users of a sound abstraction avoid introducing undefined behavior only if the abstraction itself is correct and its `unsafe` operations and `unsafe impl`s satisfy their documented safety contracts.

This is an architectural placement of proof obligations. It moves C ABI details, resource lifetime rules, and unchecked preconditions behind a smaller interface. It does not prove the C implementation's functional behavior, availability, or freedom from memory corruption.

That distinction is a good model for Anneal host adapters. A narrow Rust API can prevent ordinary engine code from misusing an Aeneas process, a Lean worker, a generated artifact handle, or an FFI object. The adapter still belongs in the trust or evidence accounting for every guarantee that depends on its unchecked behavior.

Basis: Linux `Documentation/rust/general-information.rst` at the pinned revision; derived Anneal application.

### Current `ForeignOwnable` makes cross-language ownership obligations explicit

Linux's `rust/kernel/types.rs` defines `ForeignOwnable` as an unsafe trait for moving ownership from Rust into foreign code and later reclaiming it. The interface exposes exactly the sort of gap that a language boundary cannot close on its own.

`into_foreign` returns a raw `void *` representation. The documentation warns that, beyond the stated guarantees, using that pointer except through the trait's defined recovery/borrow operations can cause undefined behavior. `from_foreign` requires that the pointer came from a prior transfer and not be reclaimed more than once. Borrowing requires the Rust-side lifetime to end before reclamation; mutable borrowing additionally requires non-overlap with other borrows.

The Rust compiler can enforce those rules only while the value is represented by the Rust API. Once C holds the raw pointer, correctness depends on the foreign caller obeying the protocol. Marking the trait unsafe makes the obligation visible; it does not eliminate it.

This is directly analogous to an Anneal opaque tool handle. A typed `PreparedEnvironment` or `GenerationHandle` can prevent many local mistakes, but if a foreign process or plugin can mutate the named resource outside the type system, the type must not be treated as proof that the underlying bytes or semantic environment are unchanged. Stable identity and freshness need their own evidence.

Basis: Linux `rust/kernel/types.rs::ForeignOwnable` at the pinned revision + derived Anneal application.

### Safety comments and contracts are evidence about a boundary, not evidence about a callee's semantics

Current Linux Rust coding guidelines distinguish a public `# Safety` contract from a local `// SAFETY:` justification. The former states what callers or implementors must uphold; the latter explains why a particular unchecked operation satisfies that contract.

This discipline is valuable because it exposes the residual assumption instead of hiding it inside an unsafe wrapper. The same principle applies to Anneal: a boundary wrapper should state which process, file, environment, artifact identity, or source correspondence it requires. A local proof that the wrapper obeys that contract does not prove that the external tool's output has the semantic meaning Anneal assigns to it.

The existing reference report `ffi-specification-trust-patterns-2019-2026` reaches the same conclusion from Rust, CompCert, and CakeML: declaration, ABI/native binding, semantic behavior, resource framing, implementation adequacy, and execution environment are separate obligations.

Basis: Linux coding guidelines + existing reference synthesis + derived Anneal application.

### An operating-system process is a conservative reset boundary for opaque components

A separate process has one important advantage over language-based isolation for Anneal: it does not require the component to be written in a memory-safe subset or to participate in a special ownership runtime. A memory bug in an OCaml runtime, C library, native plugin, or compiler internals does not directly overwrite the host's address space if the operating system enforces ordinary process separation.

Process exit also gives Anneal a coarse reset primitive. Private process memory and language-runtime globals disappear without requiring each upstream library to expose a complete reset API. That matters where current components were designed as one-shot tools rather than reentrant services.

Current reference evidence supports this only within bounded fixtures. Four independent Lean server processes survived a peer's malformed buffer and process-group kill; the killed worker could be reconstructed from saved valid source. Separate cancellation probes successfully killed and retried selected CLI processes. Those results support process failure containment for the exercised configurations, not a theorem about every child process, plugin, filesystem effect, or production workload.

The cost is equally real: serialization, IPC, startup, duplicate runtime state, and potentially duplicated caches. Moving a component in-process may be worthwhile when those costs dominate, but doing so exchanges a coarse operating-system reset boundary for a finer lifecycle contract that Anneal must own.

Basis: operating-system process model + current reference probes + derived tradeoff judgment.

### A process boundary is not a complete sandbox

Linux's seccomp documentation is explicit that syscall filtering is not, by itself, a sandbox. It reduces the exposed kernel surface; policy for logical behavior and information flow requires additional mechanisms. This is a useful warning against treating "subprocess" as a security property stronger than it is.

A child process may inherit filesystem visibility, environment variables, credentials, sockets, writable directories, or other authority. Process separation also does not prevent a deliberately malicious same-user process from affecting resources to which both processes have access.

Anneal's immediate architectural reason for subprocesses may be correctness isolation rather than adversarial containment: crash separation, lifecycle reset, and ownership of private scratch state. If the threat model later includes hostile generated code, plugins, build scripts, or compromised tool binaries, authority confinement must be designed separately. Seccomp, namespaces, sandbox profiles, containers, privilege separation, or remote workers are possible mechanisms, but this report does not select among them.

Basis: Linux `Documentation/userspace-api/seccomp_filter.rst` at the pinned revision + derived Anneal boundary.

### Anneal should not infer currentness from isolation

Neither RedLeaf's domain abstraction, Rust-for-Linux's safe wrappers, nor a Unix process answers whether an output corresponds to the current Rust source and proof environment. A perfectly isolated worker can finish stale work after a newer generation becomes authoritative.

Anneal's design contract requires successful results to carry enough identity and scope to make the user promise meaningful. Existing reference probes separately model stale-result fencing by generation, source hash, worker epoch, or document version. Those are semantic authority checks, not memory-isolation checks.

The resulting design rule is simple: **isolate computation, and fence authority separately**. A worker may compute concurrently or even finish after cancellation; only a result whose source/model/environment identity matches the current acceptance predicate may become authoritative.

Basis: Anneal `DESIGN.md` + current stale-result-fence component probes + derived synthesis.

### Conditional judgment for Anneal

The evidence favors a three-part default architecture rather than one universal isolation technique.

**Use process boundaries for opaque execution backends by default.** Charon, Aeneas, Lean, and any native dependencies should be assumed capable of hidden mutable state and process-wide failure unless a narrower boundary has been established. Separate processes provide a language-independent crash/reset boundary and match the one-shot lifecycle of some current tools.

**Put environment preparation and publication behind narrow checked host interfaces.** The host should own generation identity, source/model identity, private scratch placement, process-tree lifecycle, and the transition from validated private output to current published output. This resembles Rust-for-Linux's abstraction placement: ordinary engine code should not manipulate raw process/filesystem capabilities any more than a Rust driver should manipulate raw C bindings.

**Share only what has a stable, explicit ownership story.** Immutable prepared dependencies and content-identified artifacts are safer sharing units than mutable build state. If mutable caches are shared, their synchronization, invalidation, corruption, and recovery semantics become part of the boundary contract.

An in-process backend is a reasonable optimization when evidence establishes all of the following:

- mutable global state and cache ownership are inventoried;
- concurrent and nested calls have defined semantics or are prevented;
- unsafe/FFI/native-extension surfaces are bounded and audited;
- cancellation and reset restore a documented state;
- external effects are private, transactional, or explicitly reconciled; and
- the host still performs independent source/model/environment identity checks before acceptance.

RedLeaf suggests that these conditions are not incidental details. They are the machinery required to make a finer isolation boundary honest.

A stronger recommendation would require workload data. If process startup or duplication proves material for Anneal's interactive latency or memory goals, the next step is to measure those costs and compare them against the engineering cost of an in-process lifecycle contract. This report does not assume that the safer coarse boundary is always the fastest or cheapest design.

Basis: derived judgment from all evidence above. This is not adopted Anneal policy.

## Boundaries

- No RedLeaf, Linux, Charon, Aeneas, Lean, or Anneal execution was performed for this report.
- An exact immutable source artifact for the published OSDI 2020 RedLeaf system was not established. Selected mechanisms were source-audited at `mars-research/redleaf@08753faee652495f55fc8cbb420e5123a183affc`, the observed tip of the branch named `osdi20_camera_ready`; that commit dates to 2021-02-20, so historical publication claims continue to come from the paper rather than from this later source revision.
- RedLeaf's performance numbers are workload- and platform-specific. This report does not use them to predict Anneal IPC or in-process overhead.
- RedLeaf constrains domains to safe Rust and trusts the compiler, microkernel, selected low-level libraries, interface machinery, and compilation environment. Its isolation argument does not transfer to arbitrary unsafe Rust, OCaml, C, native plugins, or compiler subprocesses.
- RedLeaf's nested-call machinery does not establish unrestricted reentrancy of arbitrary domain state.
- Rust-for-Linux's as-safe-as-possible abstractions are a memory-safety architecture, not proof that the underlying C subsystem is functionally correct, available, isolated, or semantically modeled.
- `ForeignOwnable` demonstrates an explicit ownership protocol; it does not cover every Rust/C sharing pattern in Linux.
- A process boundary does not imply seccomp, namespaces, privilege separation, confidential execution, or protection from malicious same-user code.
- Process termination does not undo filesystem writes, remote actions, device state, or escaped child processes. Existing Anneal probes observed bounded cleanup and retries only.
- The current Aeneas and Lean component reports are evidence about selected pins and bounded fixtures. They do not prove that future tool versions have the same lifecycle behavior.
- This report does not choose a specific sandbox, IPC transport, process-pool size, artifact digest format, generation schema, or in-process embedding strategy.
- Anneal implications are derived analysis under current principles and design authority, not project policy.

## Evidence

### RedLeaf

**Published architecture and evaluation:** Vikram Narayanan, Tianjiao Huang, David Detweiler, Dan Appel, Zhaofeng Li, Gerd Zellweger, and Anton Burtsev, *RedLeaf: Isolation and Communication in a Safe Operating System*, 14th USENIX Symposium on Operating Systems Design and Implementation (OSDI 20), 2020, pages 21–39, USENIX paper 258949.

USENIX landing page:

`https://www.usenix.org/conference/osdi20/presentation/narayanan-vikram`

Evidence used from the paper includes:

- the motivation for language-based isolation and the claim that safe-language mechanisms alone do not supply fault isolation;
- domain restrictions to safe Rust and the trusted low-level boundary;
- heap isolation, exchangeable types, generated proxies, ownership transfer, and liveness checks;
- panic handling and domain cleanup;
- immutable versus mutable cross-domain sharing and recovery;
- shadow-driver replay for a concrete driver-recovery path; and
- the trust/threat-model limits, including unsafe extensions and side channels.

Role: **published primary evidence** for RedLeaf's stated design, implementation, evaluation, and limitations; Anneal comparisons are **derived**.

### RedLeaf paper-associated source corroboration

**Repository:** `mars-research/redleaf@08753faee652495f55fc8cbb420e5123a183affc`, observed on 2026-09-30 as the tip of branch `osdi20_camera_ready`. The commit date is 2021-02-20, after the OSDI 2020 publication, so the branch name is context rather than proof that this commit is the exact paper artifact.

- `lib/core/rref/src/rref.rs`, blob `187e9245408bf70b19cdd2f2bc178ac39568da8c`: shared-heap `RRef<T>` representation, owner-domain and borrow-count bookkeeping, transfer via `move_to`, cleanup on drop, and the explicit `TODO: race here` on owner transfer.
- `lib/core/rref/src/traits.rs`, blob `1fd1dc9ffc7f4d85b224539e2cc10464d556938f`: `RRefable` exchangeability boundary and negative implementations for raw pointers and Rust references.
- `kernel/src/heap.rs`, blob `b643a13b29ee2e3fe52718cd7d871932c7e948ca`: global shared-allocation table and `drop_domain` ownership-based recursive cleanup.
- `kernel/src/unwind.rs`, blob `f71d4d3cc02412353d44ae70c5f6aa9dee8587b3`: saved continuation state and explicit unwind restoration machinery.
- `lib/core/interfaces/proxy/src/lib.rs`, blob `98ea00b1b83b2fa966ced6b8e047b825ffd298af`, and `lib/core/interfaces/create/src/lib.rs`, blob `decd5dd72173f93a0e1f1c0a93c914edc5a25155`: typed proxy and domain-construction interfaces.
- `lib/core/interfaces/usr/src/rpc.rs`, blob `9d8941864ced9d749ea31803ff727596e5a55518`: explicit RPC panic/unwind error representation.

Role: **source corroboration** for the boundary machinery visible at this immutable revision. It does not replace the OSDI paper as publication-era authority, and no build or execution of this revision was performed.

### Linux Rust boundary

**Repository:** `torvalds/linux@551c722f40809618230001baccf219193e22fc5a`.

- `Documentation/rust/general-information.rst`, blob `09234bed272c2897e0c5487f3005b61757209a6e`: abstractions versus bindings; leaf modules should avoid raw C bindings; as-safe-as-possible wrappers; soundness conditions; constructor/destructor treatment of resources.
- `rust/kernel/interop.rs`, blob `3b371d782a592f2e85749cc35503c20fa79fd23a`: low-level unsafe Rust/C interop infrastructure is not a driver-facing interface.
- `rust/kernel/types.rs`, blob `132dd428c1f6918c5a7625a7cc4c27e0aeaa83fd`: `ForeignOwnable`, transfer/reclaim/borrow protocol, raw-pointer guarantees, and non-overlap obligations.
- `Documentation/rust/coding-guidelines.rst`, blob `3198be3a6d63fa555b3d6c12e222c7cc2cefd9ef`: distinction between `# Safety` contracts and `// SAFETY:` justifications.

Role: **documentation + source** for the current Linux Rust abstraction and ownership boundary; Anneal comparison is **derived**.

### Linux process-authority boundary

**Repository:** `torvalds/linux@551c722f40809618230001baccf219193e22fc5a`.

- `Documentation/userspace-api/seccomp_filter.rst`, blob `cff0fa7f3175e4d2482aafd0ad4ed3b7045a437a`: seccomp reduces exposed syscall surface but explicitly is not a complete sandbox; additional policy mechanisms are required for broader logical behavior and information-flow constraints.

Role: **documentation** for the limit of one common subprocess hardening mechanism; the conclusion about Anneal threat-model separation is **derived**.

### Anneal authority

**Repository:** `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`.

- `anneal/PRINCIPLES.md`, blob `d5339a95254eae14ac201139d07d9d36d48a19fb`: fail-closed verification promise, explicit TCB, usability/completeness priorities, and extensibility principles.
- `anneal/DESIGN.md`, blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`: successful-result identity and scope, source/model correspondence, compositional abstraction, explicit/shrinkable trust, and deliberate non-selection of an integration mechanism.

Role: **project authority** constraining the derived Anneal judgment.

### Adjacent current reference evidence

Observed against `google/zerocopy@reference` at commit `e1c4cf18da52136936eec8d6361607a9036adcb9`; the cited report files were reread on 2026-09-30.

- `reports/anneal-3730-cross-tool-stage-cancellation-cleanup-2026-09-29`, `REPORT.md` blob `14e91986e6a25cc19f83929652613f8efa02ab44`: actual pinned CLI process-group cancellation/retry; bounded descendant cleanup; partial filesystem state; explicit limits around escaped descendants and external effects.
- `reports/anneal-3730-lean-pool-failure-isolation-2026-09-29`, `REPORT.md` blob `d95b0ddc1607be1127efe17d329a44fc331dcb1d`: four independent Lean servers; peer isolation after malformed input and one worker kill/restart; bounded stale-fence model.
- `reports/aeneas-library-process-architecture-nightly-2026-06-03`, `REPORT.md` blob `90a1fa6186050cca40b0546ed4e426ba974f059c`: public OCaml library plus one-shot CLI; process-global mutable configuration/error state; no ready-made long-lived multi-request service contract.
- `reports/ffi-specification-trust-patterns-2019-2026`, `REPORT.md` blob `5146996abe426e1680aa2f7120e3e5c78de4dba7`: foreign declaration, ABI/native identity, semantic behavior, resource framing, implementation adequacy, and environment are separate trust layers.

Role: **existing source/execution-grounded corpus evidence** for Anneal's selected components. The cross-system judgment remains **derived**.

## Revalidation

For a future RedLeaf-based comparison, first check whether an exact immutable source artifact corresponding to the published OSDI 2020 system has been identified. Also reread the live `osdi20_camera_ready` branch rather than assuming it still points to `08753faee652495f55fc8cbb420e5123a183affc`. If that 2021 commit remains relevant, the cheapest source revalidation is to diff the RRef representation and `RRefable` boundary, `kernel/src/heap.rs::drop_domain`, the proxy/create interfaces, and the unwind/RPC failure path. Re-examine the owner-transfer synchronization around `RRef::move_to`; do not promote the current `TODO: race here` into either a fixed invariant or a confirmed bug without further analysis. The paper remains the publication-era authority unless a stronger artifact-to-paper correspondence is established.

For Linux, diff the four pinned source/documentation regions above. The discriminating questions are whether leaf Rust code still avoids direct bindings, whether unsafe contracts remain localized, whether foreign ownership still exposes explicit reclaim/borrow obligations, and whether the seccomp documentation still rejects the "complete sandbox" interpretation.

For Anneal, revalidate the selected tool lifecycle reports when Charon, Aeneas, Lean, Lake, or the host architecture changes. A cheap discriminating probe for a proposed in-process backend should run A/B/A requests in one process while varying configuration and injected failure, check concurrent and nested calls where supported, and verify that cancellation/reset returns all mutable state to the documented baseline. Preserve source/tool identities and negative results.

For a proposed process backend, rerun bounded failure injection with private scratch roots and actual child-process trees. Kill during phases that can write output; inventory surviving files and descendants; retry; then prove that only a result carrying the current generation/source/environment identity can cross the publication boundary. If sandboxing is part of the threat model, test authority separately from crash isolation.

The architectural decision should be revisited if measured interactive latency or memory duplication makes process isolation materially unacceptable, or if an upstream component develops a documented, reentrant, resettable service/library contract that removes the assumptions currently supplied by process lifetime.