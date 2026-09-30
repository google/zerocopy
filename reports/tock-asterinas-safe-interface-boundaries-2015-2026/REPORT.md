# Tock and Asterinas: what a safe interface can and cannot isolate

## Summary

Tock and Asterinas both put a comparatively small set of privileged mechanisms behind safe Rust interfaces, but neither system treats a safe interface as a general correctness or fault-isolation boundary. Their strongest common lesson is narrower and more useful: **a mechanism can safely delegate policy when it retains control of every resource whose misuse would violate the property being protected, and it validates untrusted policy outputs before acting on them**.

Tock divides its kernel between privileged core code and Rust capsules. Capsules cannot use `unsafe`; sensitive operations require capabilities that trusted initialization code alone can mint. Grants tie capsule-owned per-process state to process lifetime. This provides low-cost, language-enforced memory-safety and authority boundaries inside one address space, but Tock's own retrospective and current design material distinguish that from hardware isolation: a capsule can still contain functional bugs, panic, or monopolize a cooperatively scheduled kernel. Tock also had to redesign its userspace buffer/callback interface when an apparently narrow API failed to encode the lifetime and aliasing conditions Rust safety required. Narrowness was not sufficient; the interface had to capture the right invariant.

Asterinas makes the split more explicit. OSTD is the privileged framework that contains `unsafe`; the ordinary kernel is safe Rust. Its current soundness documentation defines the claim as absence of undefined behavior, not correct scheduling, file-system behavior, networking behavior, deadlock freedom, or availability. Asterinas goes beyond merely trusting safe policy code: for schedulers and allocators, OSTD rechecks the concrete values returned by a potentially wrong policy before those values can affect memory safety. A policy may make a bad decision, but the mechanism is intended to keep that bad decision from becoming undefined behavior. The same documentation also classifies CPU, memory, and device resources by whether misuse can break the target safety property, retaining sensitive resources inside OSTD and exposing only mediated forms of insensitive resources.

For Anneal, this supports a conditional architecture rather than a blanket analogy. Environment preparation and publication can be concentrated behind narrow checked host interfaces **if** the host actually controls the relevant authority: which source/configuration/tool identities are admitted, which artifact bytes are named, which results are current, and which canonical reference may advance. Scheduling, heuristics, proof-search strategy, and backend selection can then be treated as policy whose mistakes cause rejection, wasted work, or a wrong proposal rather than silent corruption of canonical state.

The analogy stops at execution that escapes the host's resource model. Lean, OCaml, compiler plugins, native libraries, package managers, subprocesses, filesystem state, environment variables, and network-visible dependencies are not confined by Rust's type system merely because a Rust wrapper launches them. A safe Rust API around such code does not imply crash containment, cleanup, determinism, semantic freshness, or even memory safety inside the foreign process. Anneal should therefore keep process or equivalent OS isolation for opaque execution backends unless a specific backend can satisfy stronger in-process assumptions. Source/model/environment identity fencing and publication validation remain necessary even when execution is isolated.

The resulting design rule is: **minimize and harden the mechanism that owns irreversible authority; make everything else propose values to it.** Do not infer from “safe Rust” that the proposal is semantically correct, live, fresh, or side-effect free. Recheck every property that canonical publication depends on at the authority boundary.

## Applicability

This report addresses #3732 J006, **Tock and Asterinas: small trusted mechanisms, large safe interfaces**. It compares two concrete systems because they expose different versions of the same design move: concentrate memory-safety-sensitive operations in a smaller privileged substrate while letting much larger safe Rust components implement policy and functionality.

The Tock evidence has two roles. The 2025 SOSP retrospective is the primary source for historical changes and for the project's interpretation of what worked over roughly a decade. Current source at `tock/tock` revision `78862168a64a4f9ce61c9c17370272770c4a7cbb` is used to check that the capsule and capability mechanisms discussed by the retrospective are still represented in the code examined on 2026-09-30. The report does not infer that every current mechanism existed unchanged throughout Tock's history.

The Asterinas evidence likewise has two roles. The 2025 USENIX ATC paper is the primary published account of the framekernel architecture, its evaluation, and its claimed memory-safety TCB. Current source and soundness documentation at `asterinas/asterinas` revision `a5238eb6a965a4616ce07a48f5dfbc8042c4cd44` are used for the more precise current claim boundary: OSTD's safe API, sensitivity classification, injected policy interfaces, and the explicit distinction between undefined behavior and higher-level correctness. The current documentation is stronger and more detailed than the ATC paper in some places; those current statements are not backdated to the paper implementation without evidence.

The comparison is property-relative. Four properties are kept separate throughout:

1. **memory safety / absence of undefined behavior** — whether untrusted extension code can violate the language/runtime memory model;
2. **authority confinement** — whether code can perform a sensitive operation without being handed the corresponding authority;
3. **availability and fault containment** — whether a crash, panic, loop, deadlock, or resource exhaustion is contained;
4. **semantic correctness and freshness** — whether a result is the right result for the intended source, model, configuration, and current session.

Tock and Asterinas provide useful evidence for the first two. They provide counterexamples to treating those as equivalent to the latter two. Anneal's mixed-language process-isolation comparison is addressed more directly by J007; this report uses process isolation only as an alternative boundary needed where J006's same-language assumptions do not hold.

No Tock, Asterinas, Lean, OCaml, or Anneal execution was performed for this report. Anneal implications are derived architectural judgments, not adopted project policy.

## Findings

### 1. “Safe interface” is meaningful only after naming the property it protects

Both systems deliberately use safe Rust to make large components unable to violate a smaller substrate's memory-safety invariants, but they do not claim that safe code becomes correct in every other sense.

Tock's current and retrospective descriptions separate user processes, capsules, and privileged kernel mechanisms. User processes receive hardware isolation and a narrow syscall boundary. Capsules execute in the kernel address space and are isolated primarily by the Rust type system and by the APIs they are given. That makes capsules substantially cheaper to call than processes, but the guarantee is weaker: safe Rust prevents a capsule from directly manufacturing arbitrary references or invoking forbidden `unsafe` operations; it does not prevent an infinite loop, panic, bad sensor policy, wrong network behavior, or misuse of an authority the capsule legitimately received.

Asterinas states the distinction even more directly. Its current “What Soundness Means” document defines the target as absence of undefined behavior under interaction with safe kernel services, injected policies, userspace, and peripherals. The same document explicitly permits a safe service to contain logic bugs and an injected policy to make arbitrarily bad decisions. Its separate 2025 article closes by treating logic and concurrency bugs as work beyond the memory-safety result, and the companion Converos work reports deadlocks, livelocks, panics, and other concurrency failures found through model checking.

The comparison therefore rules out a tempting but incorrect transitive argument:

> safe Rust interface -> safe component -> isolated component -> correct result.

The evidence supports only a property-specific edge. A safe Rust interface can prevent certain memory-safety violations **when the trusted side owns the relevant unsafe resources and the API preserves the required invariants**. Other properties need other mechanisms.

**Basis:** Tock retrospective + current source/documentation; Asterinas ATC 2025 + current soundness documentation + current source. The four-property decomposition is derived.

### 2. Tock converts `unsafe` from an all-or-nothing privilege into narrower authorities

Tock's current `kernel/src/capabilities.rs` explains the motivation explicitly: Rust's `unsafe` marker distinguishes code that may use all unsafe language mechanisms from code that may use none, which is too coarse for operations that are sensitive without being language-unsafe themselves. Tock represents those authorities as `unsafe` traits. Trusted code that can use `unsafe` implements a zero-sized capability type; ordinary functions demand a reference to the appropriate capability.

The capability set is deliberately finer than “kernel privilege.” Current source distinguishes, among others, general process management, starting a process, entering the main loop, memory allocation, external process construction, storage authority, UDP-specific authority, and network-capability creation. The `ProcessStartCapability` is separate from general process management because starting a process also requires enforcing uniqueness of the application identifier. That is a useful detail: the boundary is drawn around a **semantic invariant**, not around a module name.

Capsule crates such as `capsules/core` compile with `#![forbid(unsafe_code)]`. Board components likewise forbid `unsafe`; their documentation says operations such as capability construction must remain visible in trusted board configuration rather than being hidden inside a reusable component. This makes authority distribution auditable at composition time. Safe code can hold and exercise a capability it has been given, but it cannot mint one through ordinary safe Rust.

For Anneal, the analogous move is not necessarily to introduce literal Rust capability traits. The transferable idea is to separate authorities that are easy to conflate:

- ability to prepare or inspect an environment;
- ability to propose an artifact/result;
- ability to declare a source/model/configuration identity;
- ability to accept a result as current;
- ability to advance a canonical published ref.

A worker that can propose bytes need not possess publication authority. A backend that can run a prover need not decide that its environment matches the requested proof context. Publication code should accept an explicit, narrow authority plus checkable inputs, not ambient “trusted worker” status.

**Basis:** source inspection of `tock/tock@78862168...` `kernel/src/capabilities.rs`, `capsules/core/src/lib.rs`, and `boards/components/README.md`; derived Anneal mapping.

### 3. Tock grants show that resource lifetime can be part of the safe boundary

Tock's grant mechanism lets a capsule maintain process-specific state without giving the capsule an unconstrained kernel heap. A `Grant<T>` is created at boot with a unique grant identity and type. Entering it for a process causes the core kernel to allocate `T` in that process's grant region and gives the capsule temporary structured access. Upcalls and allowed-buffer references are held in kernel-managed grant metadata. The allocation is therefore associated with the process whose lifetime justifies it rather than with an immortal global allocator.

The 2025 retrospective links this mechanism to a broader resource-isolation decision: avoiding a general kernel heap made it harder for one application to exhaust kernel memory through a capsule. The historical cost was architectural complexity. State that might otherwise live in a global data structure had to be organized around process lifetime and explicit grants.

This is relevant to Anneal because daemonized proof services and editor integrations are prone to “global cache” designs. A Tock-like lesson is to decide which state belongs to a specific source/configuration/generation and make that identity part of the access path. Prepared environments, temporary projections, diagnostic streams, and proof attempts should be reclaimable when their owning job/session generation is no longer live. A global cache may still exist, but immutable cache entries and mutable session state should not share one undifferentiated lifetime.

This does not imply that Tock grants should be copied mechanically. Anneal's dominant resources are filesystem artifacts, subprocesses, memory-heavy prover instances, and external caches rather than microcontroller process memory. The transferable invariant is that **resource ownership and reclamation follow a durable identity that the trusted mechanism controls**.

**Basis:** Tock current `kernel/src/grant.rs` + 2025 retrospective; Anneal conclusion derived.

### 4. Tock's userspace-buffer redesign is evidence against trusting API narrowness by itself

The retrospective records a more important negative lesson. Earlier Tock system-call interfaces let capsules retain application buffer/callback objects in ways that later proved incompatible with Rust's aliasing and lifetime requirements. Repair required a substantial interface redesign: the kernel retained ownership of the underlying user resources and exposed only temporary accesses under rules the core could enforce. The change also contributed to a hard userspace ABI break because carrying both versions was too expensive for the target systems.

That history matters because “small trusted core, safe extensions” can sound self-validating. It is not. The safe side is safe only if the trusted interface encodes all preconditions that unsafe implementation code relies upon. An omitted lifetime, ownership, reentrancy, uniqueness, or aliasing condition can make a narrow interface unsound.

The Anneal parallel is exact enough to be actionable. A publication API of the form `publish(path)` is narrow but under-specified if the actual invariant is “publish these exact validated bytes produced from this source/model/config/tool identity, only if the canonical ref still has this expected predecessor, and only if no newer accepted generation supersedes this result.” The interface should carry the invariants explicitly, even if that makes it wider in data.

Conversely, an interface should not force every upstream detail into its type merely to look rigorous. Tock's historical lesson is to encode conditions that affect the protected invariant. Anneal should expose source/config/tool identities, generation/freshness, content hashes, validation evidence, and expected publication predecessor when those determine acceptance; it need not expose internal proof-search choices that cannot change what publication is allowed to accept.

**Basis:** Tock 2025 retrospective; derived Anneal comparison.

### 5. Asterinas makes the trusted-substrate contract explicit: OSTD owns `unsafe`, services use safe APIs

Asterinas's framekernel runs the kernel in one address space but divides it logically. OSTD is the privileged framework. Ordinary OS services implement Linux behavior above OSTD using safe Rust. The current top-level kernel crate contains `#![deny(unsafe_code)]`, while OSTD contains the architecture-, memory-, task-, DMA-, and other low-level unsafe operations that establish safe abstractions.

The USENIX ATC 2025 paper reports this as an intra-kernel privilege separation and measures the memory-safety TCB at about 14% of the codebase under its counting method. The result is important, but the percentage is not the architectural invariant. The invariant is that the code outside OSTD cannot invoke arbitrary unsafe operations and receives hardware-sensitive resources only through OSTD abstractions. Compiler/core libraries, OSTD, boot/firmware, CPU behavior, memory controller, and IOMMU behavior remain assumptions in the current trust model.

That makes the Asterinas boundary more like a reference monitor than a style convention. The safe service layer may be large, but it cannot directly construct the sensitive low-level states on which OSTD's memory-safety claim depends.

For Anneal, a comparable host mechanism would be the component that owns canonical source/environment identity and publication authority. The volume of agent, scheduler, UI, and proof-strategy code outside that component is not itself a problem if none of it can bypass the acceptance checks. A small publication module is useful only when alternate write paths, ambient credentials, and mutable shared files cannot silently perform the same transition behind its back.

**Basis:** Asterinas ATC 2025; current `asterinas/asterinas@a5238eb...` `kernel/src/lib.rs`, OSTD soundness overview, and trust-model documentation; derived Anneal mapping.

### 6. Asterinas's strongest reusable pattern is adversarial-policy validation, not “safe Rust is trusted”

Asterinas's current safe-policy documentation deliberately assumes policy can be wrong. The task scheduler may return a task already running elsewhere. The frame allocator may return a frame already allocated or outside the usable range. The slab allocator may return an invalid slot. OSTD places a second check at the point where the proposed value would cross into a memory-safety-sensitive operation.

Examples in the current documentation include:

- task switching guarded by per-task state so a bad scheduler choice does not put one kernel stack on two CPUs simultaneously;
- frame construction checking frame metadata so an allocator cannot create two live frame handles to one physical page;
- heap allocation validating slot provenance, size, and alignment before treating a returned slot as backing a Rust allocation.

This is stronger than saying “the policy is written in safe Rust.” Safe Rust constrains what the policy can do directly; **validation constrains what the trusted mechanism will do with the policy's output**. That is the most direct Anneal analogue.

A useful Anneal split is:

| Anneal concern | Policy may propose | Trusted mechanism must decide/check |
| --- | --- | --- |
| backend scheduling | worker/tool choice, priority, retry | whether requested source/config/generation is still eligible |
| environment construction | dependency set, paths, flags | resolved immutable identities, allowed external inputs, complete provenance |
| proof/translation | artifact bytes, diagnostics, candidate proof | content identity, parser/validator result, model/source correspondence evidence |
| caching | reuse candidate | exact cache key covers all semantic inputs; immutable bytes match key |
| publication | candidate result | freshness, expected predecessor, validation, non-forced atomic transition |

A wrong policy should therefore be able to waste time, choose a slow prover, or propose a candidate that fails validation. It should not be able to make stale bytes canonical merely because it is an “authorized agent.”

**Basis:** Asterinas current `safe-policy-injection.md`; table and Anneal judgment derived.

### 7. Sensitivity classification explains when a small trusted mechanism is actually possible

Asterinas's current soundness design classifies CPU, memory, and device resources by whether misuse can violate kernel memory safety. Kernel control registers, trap configuration, code/stack/heap/page-table/frame-metadata memory, interrupt controllers, and IOMMU state are kept inside OSTD. User-visible registers, user virtual memory, explicitly untyped physical memory, and mediated peripheral resources can be exposed because OSTD either strips sensitive bits or restricts the address/resource range first.

This is a useful answer to “what belongs in the trusted core?” The answer is not “whatever is low level.” It is “whatever must remain controlled for the protected property to hold.” A peripheral MMIO range can be outside the trusted core if the privileged mechanism first proves that the range is insensitive. A page-table page cannot.

Anneal can apply the same method to state rather than hardware. For the property “published result names the exact validated proof context,” likely sensitive resources include:

- the mapping from logical proof target to source/model/configuration identity;
- mutable environment variables or search paths that influence resolution;
- the tool and plugin identities used to construct the result;
- mutable generated files used as proof input;
- the acceptance generation/freshness state;
- the canonical ref or database entry that makes a result authoritative.

An immutable content-addressed artifact whose hash and provenance are already fixed can be treated more like an insensitive resource: many workers can read it without gaining authority to change its meaning. A mutable workspace directory cannot be treated that way merely because its path is hidden behind a safe method.

The boundary shrinks only after classification. If a backend can still discover unrecorded plugins through a global search path or observe mutable files outside the prepared environment, those are sensitive semantic inputs that escaped the mechanism.

**Basis:** Asterinas current sensitivity-classification documentation; Anneal classification derived.

### 8. Same-address-space language isolation trades stronger failure containment for lower crossing cost

Tock and Asterinas both deliberately avoid putting every internal extension behind a hardware address-space boundary. That removes IPC/context-switch costs and permits direct typed interfaces. It also gives up properties that an address-space or process boundary can provide.

Tock's retrospective describes capsules as cheap, language-isolated kernel components and separately retains hardware-isolated userspace processes for untrusted applications. Capsules are semi-trusted for liveness: a cooperatively scheduled capsule that never yields can deny service. The language boundary is therefore an efficient fit for code that is permitted to share kernel fate but should not be able to violate memory safety.

Asterinas makes the same basic performance trade in a more Linux-like setting. The ATC paper presents the framekernel as avoiding the hardware isolation overhead of a microkernel while using the safe API as the intra-kernel memory-safety boundary. Its evaluation reports performance broadly comparable to Linux for the measured workloads, but the evidence is bounded: the paper's evaluation is single-core in important experiments, the system lacked some Linux optimizations/features, and the network stack differed from Linux. The paper's “about 14% TCB” is similarly a code-count result under its methodology, not a proof that 14% is sufficient under every future architecture/configuration.

For Anneal, the choice should follow the failure model rather than an aesthetic preference for in-process services. An in-process safe Rust component is attractive when:

- all memory-unsafe operations stay behind a reviewed host abstraction;
- extension code cannot load arbitrary native code or escape through ambient FFI;
- cancellation and panic behavior are acceptable in the host process;
- mutable global state and reentrancy are explicit;
- resource exhaustion by the component is either tolerable or independently bounded.

A Lean server, OCaml translator, compiler plugin, or arbitrary native extension generally fails one or more of these premises. A process boundary therefore remains the conservative default for opaque backends. This does not make the subprocess semantically trustworthy; it only gives the host a stronger reset/crash/resource boundary.

**Basis:** Tock retrospective; Asterinas ATC 2025; current project material. Anneal conditions derived.

### 9. A narrow trusted mechanism does not remove ambient configuration from the trust boundary

Both systems work because the privileged mechanism has unusually strong control over the environment in which its safety claim is interpreted. Tock builds one statically composed embedded kernel. Trusted board initialization decides which capsules and capabilities exist. Asterinas's OSTD owns or mediates the CPU, memory, and device resources whose corruption could break its target safety property.

Anneal's toolchain environment is less closed. A proof or translation can depend on:

- executable and dynamic-library resolution;
- environment variables and current directory;
- compiler/prover configuration files;
- package-manager state and dependency lockfiles;
- generated source or build artifacts;
- native plugins and foreign runtimes;
- filesystem contents outside a nominal project root;
- services reached through sockets or the network;
- version-specific behavior of an editor/server protocol.

A Rust host can expose only `fn prove(input: PreparedInput) -> Result<Artifact>` and still fail to control those inputs if the implementation delegates to a process that consults ambient state. The API is narrow syntactically while the semantic input surface remains broad.

The corresponding Anneal rule is: **the preparation boundary must close over all material ambient inputs or record them as assumptions**. Immutable tool archives, explicit environment construction, isolated working directories, content-addressed generated artifacts, disabled or pinned network access, and recorded plugin identities are methods for doing that. Where closure is infeasible, provenance should state the residual ambient dependency rather than pretending the host interface removed it.

**Basis:** comparison of the resource-control premises in Tock/Asterinas with Anneal's external-tool architecture; derived.

### 10. Capability boundaries and process boundaries solve different problems

A process boundary can keep a crashing backend from corrupting host memory and can make termination/restart/resource accounting more enforceable. It does not, by itself, decide whether a worker should be allowed to publish a result. Conversely, a capability or checked publication API can prevent an ordinary worker from advancing a canonical ref, but it does not stop that worker's in-process backend from deadlocking the host or corrupting memory through FFI.

The two boundaries are therefore complementary:

- **process/OS isolation** contains execution failures and some ambient authority;
- **capability/checked host interfaces** confine semantic and publication authority;
- **content/provenance identity** determines what bytes and environment a result actually refers to;
- **freshness/generation fencing** determines whether an otherwise valid result is still current.

This decomposition is especially important for Anneal because a proof artifact can be mathematically valid yet unacceptable for the requested operation: it may prove an old source snapshot, use the wrong model revision, or come from a toolchain whose generated input no longer matches the editor buffer. None of those are memory-safety failures.

**Basis:** derived comparison of Tock/Asterinas boundaries with Anneal's source/model/environment problem.

### 11. The main alternatives are stronger isolation or a larger trusted service; each moves a different cost

There are at least three serious architectural alternatives to the small-mechanism/large-safe-interface pattern.

**Hardware/process isolation everywhere.** This gives clearer crash and memory-fault containment and naturally accommodates multiple languages. Tock uses hardware isolation for applications rather than capsules; microkernels generalize the pattern. The cost is IPC, serialization, duplicated state, lifecycle complexity, and potentially higher latency. For Anneal's coarse proof jobs, those costs are often acceptable, so process isolation is a stronger default than it is for a microcontroller kernel fast path.

**One large trusted in-process service.** This reduces protocol and synchronization overhead and can make shared incremental state cheap. The cost is a larger failure domain and a larger set of implementation details that must satisfy every protected invariant. If a native plugin or unsafe subsystem is loaded into that process, a nominally safe high-level API does not restore isolation.

**Message-passing/brokered authority between all components.** This can make ownership transitions explicit and centralize access checks. It also risks turning every local call into orchestration machinery and can create a central bottleneck. The historical Tock material is relevant here: its design repeatedly prefers static typing/direct calls for cheap local composition while using explicit capabilities only where authority needs restriction. Asterinas similarly keeps direct safe calls for deprivileged services and concentrates checks at privileged transitions rather than making the entire kernel an actor system.

For Anneal, the hybrid is the defensible default: processes for opaque execution; immutable artifacts for sharing; direct in-process logic for host-owned pure operations; explicit authority and validation only at transitions that can make a result current or mutate canonical state.

**Basis:** documented Tock/Asterinas design choices + derived comparative judgment.

### 12. Conditional Anneal judgment

The Tock/Asterinas pattern is worth adopting for Anneal **only at boundaries where the host can enumerate and mediate the resources that determine the claimed property**.

A concrete architecture would make the trusted host responsible for five things:

1. **Preparation authority.** Resolve source, model, configuration, toolchain, generated inputs, and permitted ambient dependencies into an immutable prepared-environment identity.
2. **Execution envelope.** Start an opaque backend in a bounded process/container-like environment when its language/runtime cannot satisfy the host's in-process isolation assumptions.
3. **Proposal interface.** Let workers/backends return artifacts, diagnostics, witnesses, or candidate publication records without granting them canonical mutation authority.
4. **Acceptance checks.** Revalidate content identity, source/model correspondence evidence, validator/checker results, expected generation, and any policy-specific prerequisites at the moment a result crosses into accepted state.
5. **Publication authority.** Serialize the final state transition and require the expected predecessor/current-state fence so stale or concurrent proposals fail closed.

This is deliberately analogous to Asterinas's injected-policy design. The scheduler or proof agent is allowed to be wrong about strategy. The trusted mechanism must make it difficult for that wrong strategy to become a violation of the publication invariant. It is also analogous to Tock's capability design: a worker receives only the authority needed for its role, and stronger authority is minted and consumed at an explicit boundary.

The architecture should be rejected or expanded when any of these conditions fail:

- a backend can mutate canonical state through another path;
- material tool inputs remain ambient and unrecorded;
- a “safe” extension can load arbitrary native/unsafe code into the trusted process;
- reset/cancellation/resource exhaustion of one backend can wedge unrelated work and that availability coupling is unacceptable;
- the acceptance predicate depends on semantic facts that the host cannot check or bind to evidence.

A full capability framework is also unnecessary when ordinary ownership and module privacy already make the authority non-forgeable. Tock's lesson is granular authority, not ceremony. The smallest mechanism that makes bypass impossible and invariants explicit is preferable.

**Basis:** derived judgment from the preceding findings. It is not a current Anneal design decision.

## Boundaries

This report does **not** establish that either operating system is free of memory-safety bugs. Tock's architecture and `forbid(unsafe_code)` boundaries reduce what capsules can do; unsafe code, compiler behavior, hardware behavior, and the correctness of safe abstractions remain relevant. Asterinas's paper and documentation argue a soundness boundary and report testing/evaluation, but this report did not reproduce that argument mechanically or inspect every OSTD unsafe block.

The Asterinas ATC 2025 TCB percentage is not directly comparable to Tock's codebase without normalizing what code, generated material, architecture support, and dependencies each study counts. It is evidence that the authors obtained a substantially smaller unsafe/privileged substrate under their methodology, not a universal numeric ranking.

The Asterinas performance claims are bounded by the paper's evaluated hardware/configuration/workloads and the system's 2025 feature set. This report uses them only to show that the authors measured the cost of avoiding intra-kernel hardware isolation; it does not infer that framekernel overhead is negligible for arbitrary workloads.

Tock's SOSP 2025 retrospective describes historical designs and lessons. Current source confirms several mechanisms but does not prove every historical statement, and this report does not reconstruct each intermediate release. In particular, the userspace buffer/callback redesign is retained as a historical design lesson rather than a line-by-line current-code audit.

Asterinas current soundness documents include implementation links that in some places point to an earlier source revision. This report treats the prose at current revision `a5238eb6...` as current project documentation and uses only separately inspected current source for claims stated as current-source facts.

Safe Rust does not imply termination, bounded resource use, deadlock freedom, race-free high-level behavior, protocol correctness, deterministic output, confidentiality, integrity of data legitimately writable by the component, or freshness of a result relative to changing source/configuration. Those omissions are central to the comparison, not incidental caveats.

Process isolation is not a complete sandbox. A subprocess can still consume disk, mutate shared files, contact external services, inherit credentials, or produce semantically stale output unless those channels are independently controlled. J007 should carry the deeper mixed-language/process-isolation analysis.

The Anneal mappings are derived architectural analysis. No source examined says Anneal should use capabilities, grants, Asterinas-style policy injection, or a particular process topology.

## Evidence

### Tock

- Leon Schuermann, Brad Campbell, Branden Ghena, Philip Levis, Amit Levy, and Pat Pannuto, **“Tock: From Research to Securing 10 Million Computers,” SOSP 2025**, DOI `10.1145/3731569.3764828`. Primary historical and rationale source. Public copy: <https://tockos.org/assets/papers/2025-sosp-tock-decade.pdf>.
- `tock/tock` revision `78862168a64a4f9ce61c9c17370272770c4a7cbb`, `kernel/src/capabilities.rs`, blob `dddcedda97d0e4010dc368182fff8d5181815eaa`. Direct source for the capability model and current capability classes.
- Same revision, `capsules/core/src/lib.rs`, blob `3528b00f039cb9f5142d2fd5d9e51a4b6bdbc4d5`. Direct source for `#![forbid(unsafe_code)]` on the core capsule crate.
- Same revision, `kernel/src/grant.rs`, blob `1d5cdd9788f923e17ef668ffb79acf06725794f5`. Direct source for current grant ownership/allocation semantics.
- Same revision, `boards/components/README.md`, current source documentation stating that components forbid `unsafe` and privileged setup such as capability provision belongs in trusted board configuration.

### Asterinas

- Yuke Peng et al., **“ASTERINAS: A Linux ABI-Compatible, Rust-Based Framekernel OS with a Small and Sound TCB,” USENIX ATC 2025**, pp. 307-323, ISBN `978-1-939133-48-9`. Primary published architecture/evaluation source: <https://www.usenix.org/conference/atc25/presentation/peng-yuke> and paper <https://www.usenix.org/system/files/atc25-peng-yuke.pdf>.
- `asterinas/asterinas` revision `a5238eb6a965a4616ce07a48f5dfbc8042c4cd44`, `kernel/src/lib.rs`, blob `62268709b2bf43da148c61faf4e73e8b52605ee2`. Direct source for the current top-level kernel's `#![deny(unsafe_code)]` boundary.
- Same revision, `book/src/ostd/soundness/README.md`, blob `114f4b15ef0cd77825fd607bb0d320b31bd2335e`. Current project statement of OSTD as the privileged unsafe-containing framework and its public safe API as the privilege boundary.
- Same revision, `book/src/ostd/soundness/what-soundness-means.md`, blob `3be761f6c0f341c351302948f12d98154cfa70e0`. Current definition of the memory-safety/soundness claim and trusted/untrusted components.
- Same revision, `book/src/ostd/soundness/sensitivity-classification.md`, blob `87319a518492d7a853c0b1ba1132a637349e869a`. Current resource-classification rationale.
- Same revision, `book/src/ostd/soundness/safe-policy-injection.md`, blob `1d9db11917f249374813862830882055d5aa854f`. Current project account of validating scheduler/frame/slab policy outputs and of liveness-only failure cases for some callbacks.
- Hongliang Tian, **“Asterinas: A Rust-Based Framekernel to Reimagine Linux in the 2020s,”** USENIX ;login:, 2025. Useful author interpretation of the memory-safety boundary and explicit statement that logic/concurrency remain further work: <https://www.usenix.org/publications/loginonline/asterinas-rust-based-framekernel-reimagine-linux-2020s>.
- Ruize Tang et al., **“Converos: Practical Model Checking for Verifying Rust OS Kernel Concurrency,” USENIX ATC 2025**. Corroborating evidence that safe-Rust memory safety does not settle deadlock/livelock/concurrency correctness: <https://www.usenix.org/conference/atc25/presentation/tang>.

### Evidence roles and limits

The papers and current project documentation are **documentation** and author-reported evaluation; repository files are direct **source** evidence for the inspected revision. Historical causal claims about why Tock changed are attributed to the retrospective rather than inferred from current code. Anneal recommendations are **derived** from those sources. No benchmark, fault injection, model check, compiler run, or OS execution was performed in this investigation.

## Revalidation

For Tock, first inspect the current capsule crate roots for `forbid(unsafe_code)`, then diff `kernel/src/capabilities.rs`, `kernel/src/grant.rs`, and board-component guidance from `78862168a64a4f9ce61c9c17370272770c4a7cbb`. If capability minting, grant lifetime, or the capsule unsafe policy changed, reread the current architecture documentation before carrying this report forward. Historical claims about the buffer/callback redesign should continue to be checked against the SOSP 2025 retrospective rather than inferred from a newer source tree.

For Asterinas, diff the current OSTD soundness documentation and top-level kernel unsafe policy from `a5238eb6a965a4616ce07a48f5dfbc8042c4cd44`. The cheapest discriminating checks are whether the ordinary kernel still denies unsafe, whether OSTD remains the sole intended unsafe-containing framework, whether sensitivity classification still defines the resource boundary, and whether injected policies still pass through mechanism-side validation. If any of those premises changes, re-evaluate the mechanism/policy conclusion rather than merely updating a version number.

For Anneal, revalidate the derived judgment against a concrete implementation by constructing a bypass matrix. For every claimed trusted transition, enumerate all ways a worker/backend can affect the same protected resource. A narrow checked interface is adequate only if alternate paths are absent or equally checked. Then fault the policy side deliberately: stale generation, wrong content hash, wrong environment identity, duplicate publication predecessor, invalid cache entry, backend crash, timeout, and resource exhaustion. The expected result is rejection or contained failure without making an invalid candidate current. Passing such probes would validate the concrete mechanism, not the general architecture indefinitely.