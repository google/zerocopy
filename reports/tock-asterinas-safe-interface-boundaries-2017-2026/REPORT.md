# Tock and Asterinas: where narrow safe interfaces work—and where they stop

## Summary

Tock and Asterinas both concentrate dangerous mechanisms behind Rust interfaces, but they establish narrower guarantees than the phrase “safe interface” can suggest.

Tock combines several boundaries. Its small core kernel may use `unsafe`; ordinary capsules are safe Rust and are constrained by the types and references the core exposes; sensitive operations that are not memory-unsafe are additionally gated by explicit capabilities; and arbitrary-language processes are separated by hardware protection. The design therefore does not ask one mechanism to provide memory safety, system authority, fault isolation, and availability at once. Tock's later threat model makes the remaining distinctions explicit: a capsule can be memory-safe while still denying service, board configuration determines which authorities are handed out, and process isolation is stronger than same-address-space language isolation.

Asterinas draws a sharper same-address-space line. Its OSTD framework is the privileged layer allowed to use `unsafe`; the large OS-services layer is compiled with `#![deny(unsafe_code)]`. Current Asterinas documentation defines OSTD soundness precisely: any safe client may behave arbitrarily without causing undefined behavior. It then keeps complex policies such as scheduling and allocation outside OSTD and independently validates their outputs before those outputs can violate memory-safety invariants. That is a strong example of a narrow trusted mechanism succeeding because the property is local enough to re-establish at the boundary.

Neither project establishes the broader rule that logic implemented through a safe API is correct. Tock's retrospective explicitly separates type safety from logic correctness. Asterinas says a sound OS service may still crash, deadlock, starve work, corrupt filesystem state, or implement a protocol incorrectly. Both projects also retain trust or configuration outside the narrow mechanism: Tock's board setup mints and distributes capabilities and its hardware/software process boundary is a separate mechanism; Asterinas trusts its Rust toolchain, OSTD, boot/firmware, core hardware, and the correspondence between those components and the assumptions used by OSTD.

The transferable Anneal rule is therefore conditional. Concentrate preparation, publication, and other authority-changing effects behind a small checked interface **when the relevant acceptance property can be completely mediated and revalidated at that interface**. Pass explicit capabilities and identities rather than ambient authority, and make the boundary reject bad caller or backend outputs instead of assuming the caller's policy is correct. Do not infer freshness, semantic correspondence, liveness, logical correctness, or isolation of native/foreign code from that interface unless those properties are separately checked. If a plugin, subprocess, filesystem, configuration source, or native extension can mutate promise-relevant state outside the boundary, either bring that state into the checked protocol or use a stronger isolation/acceptance boundary.

This is a derived architectural judgment for Anneal, not adopted Anneal policy.

## Applicability

This report addresses #3732 J006, **Tock and Asterinas: small trusted mechanisms, large safe interfaces**. It compares the projects as evidence about where a narrow checked mechanism can support a much larger implementation surface without inheriting all of that surface's memory-safety risk.

The current source snapshots examined are:

- Tock kernel source at `tock/tock@eaae5cbf62df2bc24ee809ff9d2c7ca124e42e73`;
- Tock architecture and threat-model documentation at `tock/book@760025b0d8a1d5ff14d6015c1c50ac4e30490923`;
- Asterinas source and architecture documentation at `asterinas/asterinas@a5238eb6a965a4616ce07a48f5dfbc8042c4cd44`.

Historical interpretation also uses the Tock SOSP 2017 paper, the Tock SOSP 2025 retrospective, and the Asterinas USEN ATC 2025 paper. Those papers describe different historical states from the current revisions. Where the current documentation sharpens a claim beyond a paper-era result, this report treats the newer text as current project intent and the paper as historical evidence rather than silently merging them.

For Anneal, “checked interface” below means an interface whose implementation owns enough authority and observations to reject inputs or outputs that would violate the property being claimed. It does not mean that every operation is in-process, nor that the implementation itself is formally verified. A subprocess boundary can be checked; a Rust function can fail to be one if it trusts ambient state it does not observe.

Anneal's current design contract at `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92` is an applicability constraint, not evidence about Tock or Asterinas. In particular, Anneal promises more than memory safety alone: a successful result must identify the program and promise it applies to, expose trust and assumptions, and preserve semantics relevant to that promise. The implications below therefore distinguish “this boundary prevents UB” from “this boundary is sufficient for Anneal's end-to-end acceptance claim.”

## Findings

### 1. Both projects separate a small dangerous mechanism from a larger safe layer, but they do not draw the same boundary

Tock's architecture has at least three relevant classes. The core kernel contains most of the `unsafe` code. Capsules are kernel extensions written in safe Rust; current capsule crates use `#![forbid(unsafe_code)]`. User processes may be written in any language and are separated from the kernel and each other using the MPU. The current Tock overview describes this as language-based isolation inside the kernel plus hardware isolation for processes.

Asterinas uses a same-address-space “framekernel” split. OSTD is the OS framework and is allowed to contain `unsafe`; the OS-services layer, including the main kernel, is safe Rust. The current kernel root has `#![deny(unsafe_code)]`. The project describes OSTD's public safe API as the privilege boundary and argues that memory safety of the larger kernel reduces to soundness of that framework plus the explicitly trusted environment.

The common mechanism is not “Rust makes the whole system safe.” It is **authority concentration plus constrained representation**: dangerous resources are constructed or manipulated inside a smaller layer, then exposed through values and operations that safe code cannot arbitrarily forge or reinterpret.

The difference matters. Tock deliberately retains hardware process isolation for arbitrary-language applications and language isolation for capsules. Asterinas aims to keep the whole kernel in one address space and make safe Rust plus OSTD's API sufficient for kernel memory safety. The two systems therefore provide useful competing points on the isolation/performance spectrum rather than independent proof of one universal architecture.

Basis: **documentation + source + historical source** — Tock current overview and capsule crate roots; Tock SOSP 2017; Asterinas current framekernel documentation, `kernel/src/lib.rs`, and ATC 2025.

### 2. Tock's capabilities show why memory safety and system authority must be modeled separately

Tock's kernel documentation names a recurring case: some operations are not inherently memory-unsafe but are still too powerful to expose to every capsule. Starting the main loop twice, restarting processes, allocating privileged resources, or constructing certain kernel objects can violate system invariants without necessarily violating Rust's aliasing or validity rules.

Tock initially could have used `unsafe` as a coarse authority gate, because capsules cannot use `unsafe`. Current documentation rejects that conflation. The `kernel::capabilities` module uses unsafe traits whose implementations can be created only by trusted code, while ordinary sensitive functions take references to objects implementing a particular capability. This lets a board hand a capsule one specific authority without giving it the ability to invoke all `unsafe` operations.

This is a stronger design lesson than “use capability types.” It establishes that **a language-safety marker is the wrong vocabulary for non-language invariants**. A function can be memory-safe for all inputs and still require authority because it affects global lifecycle, configuration, or availability. Conversely, a caller can possess authority to perform an operation without being allowed arbitrary memory access.

For Anneal, preparation and publication should be treated the same way. A Rust caller's memory safety does not imply it should be able to publish a result, replace a prepared environment, retire a generation, or interpret one workspace's artifact as another's. Those operations need explicit authority and identity checks even when all participating Rust code is safe.

Basis: **documentation + source + derived** — `tock/tock` `kernel/src/lib.rs`, `kernel/src/capabilities.rs`, and Tock soundness documentation. Anneal application is derived.

### 3. Tock's process/capsule split demonstrates that “safe code” and “isolated code” are different promises

Current Tock threat-model documentation is unusually direct about the distinction. Safe-Rust capsules are isolated by the type system and API shape, but they execute cooperatively with trusted kernel code and can deny service. Tock describes this language-based capsule isolation as weaker than the hardware-backed isolation used for processes. Processes may contain arbitrary code; the MPU protects kernel and process memory across that stronger boundary.

The same threat model also distinguishes confidentiality, integrity, and availability. Process memory confidentiality and integrity are protected against other processes and capsules subject to explicit sharing. Availability has exceptions for finite resources. Capsule code is not trusted for memory isolation but can still starve trusted kernel code.

This defeats a tempting transfer to Anneal: putting code behind a safe Rust trait or API does not by itself make that code non-blocking, crash-contained, deterministic, semantically correct, or unable to retain scarce resources. These are separate dimensions with separate enforcement mechanisms.

If Anneal runs a backend in-process behind a safe trait, that interface can prevent memory corruption caused by safe Rust but cannot by itself prevent deadlock, unbounded allocation, global-state mutation through permitted APIs, or semantic lies in a returned result. A process boundary or a checked result protocol may still be required when those failures matter to the caller's promise.

Basis: **documentation + historical source + derived** — Tock current threat model and capsule-isolation documentation; Tock SOSP 2017/2025. Anneal application is derived.

### 4. Tock moved ownership-sensitive state toward the core boundary after discovering that a convenient API was unsound

Tock's 2025 retrospective describes a concrete architectural correction to its userspace/kernel ABI. Earlier interfaces exposed process buffers and callbacks to capsules in a form whose ownership did not compose soundly with Rust userspace and process termination. The redesigned ABI moved the durable ownership and revocation responsibility into the core kernel. Capsules receive temporary references whose lifetime is constrained to a call or grant entry rather than retaining arbitrary aliases to process-owned state.

The current grant implementation reflects the same ownership discipline. A `Grant` is a typed handle to per-process state. Entering it produces scoped access, and the kernel checks that the process is still valid; custom-grant access fails after process restart or death. The core uses unsafe implementation details, but the capsule-facing API constrains how the references can outlive process lifecycle transitions.

Two conclusions follow. First, concentrating unsafe code is not sufficient unless the safe interface encodes the lifecycle needed for soundness. Second, a narrow boundary can **reduce caller obligations by owning revocation and validation itself**. That is stronger than documenting “do not retain this after reset.”

For Anneal, a prepared proof environment or published result should similarly avoid exposing raw objects whose validity depends on an external generation continuing to exist. Prefer handles whose use rechecks generation/identity or scoped borrows whose lifetime cannot cross invalidation. A comment saying that a caller must not use a stale backend handle is the weaker design.

Basis: **historical source + source + derived** — Tock SOSP 2025 retrospective; current `kernel/src/grant.rs`. Anneal application is derived.

### 5. Tock keeps board configuration visibly privileged instead of pretending configuration is a safe-library implementation detail

Tock components exist to make board configuration less repetitive and less error-prone. Their current documentation says the components crate forbids `unsafe` specifically so that sensitive operations are not hidden inside helper components. Capability creation and other unsafe setup stay visible in the board's main setup function; the trusted configuration code then passes only the needed authority into the component.

This is an important boundary condition. The capsule API may be safe, but the **choice of which capsule receives which capability** is outside that API. The board integrator can assemble a secure or insecure authority graph. Tock's threat model therefore treats deployment configuration and application loading as part of the security story rather than attributing the whole result to the capsule type system.

For Anneal, environment preparation has a similar distributed-configuration risk. A narrow `PreparedEnvironment` constructor is only as authoritative as the inputs it observes. If Cargo configuration, environment variables, filesystem overlays, Lean plugins, toolchain lookup, or an external process can change the effective environment after construction, the abstraction has not actually mediated the relevant state. Either capture and identify those inputs, restrict the operating mode, or retain them as explicit trust/freshness assumptions.

Basis: **documentation + derived** — Tock `boards/components/README.md` and current threat model. Anneal application is derived.

### 6. Asterinas makes the boundary claim unusually strong—and unusually narrow

Current Asterinas documentation defines OSTD soundness as: no sequence of calls through OSTD's safe public API, combined with arbitrary behavior by safe-Rust kernel services, userspace, and peripherals, can trigger undefined behavior, subject to the project's trusted compiler, boot, firmware, and hardware assumptions. This is much stronger than “we try to put unsafe code in one crate.” It states what adversarial behavior the interface must tolerate.

The boundary is also explicitly narrow. The same document says a sound OSTD does not make the OS correct. Safe OS services may implement system calls incorrectly, corrupt filesystem state logically, violate network protocols, crash, deadlock, or otherwise behave badly without causing Rust UB. That distinction is central to the framekernel argument: memory safety is the property the framework owns; policy correctness is intentionally outside it.

This is the best transferable criterion in the comparison: a narrow trusted mechanism is credible only when its postcondition is stated precisely enough that **every behavior of untrusted callers outside that postcondition is allowed**. If the mechanism requires callers to “mostly behave” for the claimed property to hold, the trust boundary is larger than advertised.

For Anneal, an effect boundary can plausibly own “never publish an artifact whose checked identity does not match the requested source/model generation.” It cannot plausibly own “the proof means the right thing about Rust” unless it also has evidence for source/model correspondence. A single “safe backend” label would collapse those different claims.

Basis: **documentation + source + derived** — Asterinas current soundness analysis and `kernel/src/lib.rs`; Anneal application is derived.

### 7. Asterinas policy injection shows the strongest form of “do not trust the provider; validate what crosses the boundary”

Asterinas keeps several complex policies outside OSTD: the task scheduler, frame allocator, and slab allocator are supplied through safe traits. The current soundness analysis does not assume those policies make good choices. Instead, OSTD re-establishes the memory-safety invariant when it consumes their outputs.

Examples in the project documentation make the structure concrete. A scheduler can return a task that is already running elsewhere; OSTD uses task state and an atomic transition before switching so the policy cannot make one stack execute simultaneously on two CPUs. A frame allocator can return an already-used or invalid frame; OSTD checks metadata before constructing the trusted frame handle. Heap-allocation paths validate size, alignment, ownership, and lifetime conditions before using returned slots.

The architecture separates **proposal authority** from **acceptance authority**. Policy code is free to be sophisticated, buggy, or replaceable because the small mechanism does not let an unchecked proposal directly become trusted state.

Anneal should prefer the same structure when a backend or planner is replaceable. A backend may propose a prepared environment, generated artifact, proof result, cache hit, or publication candidate. The boundary that turns it into an authoritative handle/result should independently check the identity, generation, provenance, and other invariants needed for the claimed operation. This is stronger than requiring each backend implementation to remember the invariant itself.

Basis: **documentation + source + derived** — Asterinas current `safe-policy-injection.md` and OSTD source. Anneal application is derived.

### 8. Output validation works only for properties the boundary can actually observe

Asterinas's policy-validation examples succeed because the memory-safety invariants are locally checkable at the point where an untrusted policy's choice becomes dangerous. A frame has metadata recording whether it is already in use. A task carries state that can prevent simultaneous execution. A heap slot can be checked for address, size, alignment, and ownership before it is accepted.

That does not mean every policy property can be recovered by post-hoc checks. A scheduler that starves one task may never violate the “one task on at most one CPU” invariant. A filesystem implementation can return a semantically wrong directory entry while using memory safely. A logger callback can deadlock even though it cannot corrupt memory. Current Asterinas documentation explicitly classifies such failures outside the soundness guarantee.

The corresponding Anneal test is: **what evidence is available at the point of acceptance?** Artifact hash, source identity, toolchain identity, generation, parent ref, expected branch tip, and proof-checker result can often be checked. “This external translator preserved every Rust semantic observation” may not be checkable from the returned bytes unless Anneal has a translation validator or certificate. “This worker will eventually terminate” usually cannot be established by a type. “This plugin did not read ambient files” cannot be inferred from its result unless it ran in an environment that made the claim enforceable.

A narrow checked boundary therefore shrinks trust only for properties it can mediate or validate. Everything else remains a trusted assumption, requires a stronger sandbox/protocol, or needs independent evidence.

Basis: **documentation + derived** — Asterinas policy-injection and soundness docs; Anneal application is derived.

### 9. Asterinas's small memory-safety TCB is not its whole operational TCB

The ATC 2025 paper reports a substantially smaller unsafe/TBC fraction for the framekernel than for the comparison kernels under the authors' counting method and snapshot. It also reports Linux ABI coverage and application benchmarks that were competitive with Linux in the selected workloads. These outcomes support the claim that concentrating memory-unsafe mechanisms need not require a microkernel-style IPC boundary for every kernel service.

But neither the paper nor the current documentation says OSTD is the only thing that must be trusted for every claim. Current Asterinas documentation explicitly lists the Rust compiler and core libraries, OSTD, bootloader/firmware, CPU, memory controller, and IOMMU among the trusted components for its soundness argument. Device behavior is treated adversarially only where the framework configures the IOMMU and related resources to make that safe. The ATC artifact and KERNMIRI evaluation give concrete evidence against classes of OSTD bugs, but they are testing evidence, not an exhaustive proof that every unsafe path is sound for every environment.

This is directly relevant to Anneal's TCB accounting. Moving file I/O, process spawning, cache publication, or unsafe Rust into one small crate can make audit scope smaller. It does not remove the operating system, filesystem semantics, subprocess implementation, toolchain, plugins, or external translation assumptions from an end-to-end verification claim if the result still depends on them.

Basis: **historical source + documentation + derived** — Asterinas ATC 2025 and current OSTD soundness docs. Anneal application is derived.

### 10. Tock's history argues against treating the first safe boundary as final architecture

Tock's 2017 architecture already had the core/capsule/process split, but the 2025 retrospective documents substantial corrections and refinements made as the project confronted Rust soundness and deployment requirements. The userspace ABI changed to make ownership valid under Rust's model. Capabilities became a first-class way to separate system authority from the unsafe keyword. Later threat-model work documented confidentiality, integrity, availability, side-channel exclusions, deployment variation, and application-identity assumptions more explicitly.

This history cuts two ways. It supports the long-term value of a semantic boundary—Tock retained the distinction between a trusted core and safer extensions—but it rejects the idea that the exact first API shape was proven by the architecture diagram. The useful invariant survived while the mechanism changed.

Asterinas is younger. Its ATC 2025 paper presents the framekernel and a measured implementation; in March 2026 the project added a much more systematic written soundness analysis, and later documentation continued to update concrete API references. That is evidence of the same healthy pattern: the project is strengthening the argument and exposing more of the assumptions over time. It is not evidence that every current safe API has been machine-proved sound.

For Anneal, the boundary should therefore be specified by the invariant it owns—what must be checked before a prepared environment or publication becomes authoritative—not by an accidental v1 trait hierarchy or crate split. The mechanism can evolve as upstream constraints become clearer.

Basis: **historical source + repository history + derived** — Tock SOSP 2017/2025 and 2024–2026 book history; Asterinas ATC 2025 and the March 2026 soundness-analysis addition. Anneal application is derived.

### 11. The strongest competing design is stronger isolation, not a larger safe interface

Tock itself supplies the competing architecture. When code may be arbitrary-language or when stronger fault containment is required, Tock uses an MPU process boundary instead of relying on same-address-space Rust. Asterinas chooses the opposite point for kernel services: one address space and direct calls, with a safe-language framework intended to remove memory-safety risk while avoiding IPC overhead.

For Anneal, this suggests a decision rule rather than a winner. Controlled Rust components whose behavior is completely mediated by a checked API are good candidates for in-process composition. Native extensions, OCaml/C components, compiler plugins, third-party binaries, or backends whose ambient filesystem/process behavior matters cannot inherit the same assurance from a Rust trait. A process boundary can contain memory corruption and some global-state interference, but it introduces serialization, lifecycle, cancellation, resource-accounting, and protocol costs. It also does not by itself establish semantic correctness: a perfectly isolated subprocess can return a false answer.

The boundary choice should therefore follow the failure being contained:

- use safe in-process interfaces to prevent language-level memory violations and accidental authority spread;
- use explicit capabilities/identity checks for system-level authority;
- use process or sandbox isolation for code that cannot be constrained by the host language or that needs fault/resource containment;
- use independent semantic checking for results whose truth cannot be guaranteed by isolation alone.

This layered answer is better supported by the evidence than either “everything should be a subprocess” or “one small safe Rust API makes the whole engine trustworthy.”

Basis: **documentation + historical source + derived** — Tock current threat model and both Tock architecture papers; Asterinas framekernel documentation and ATC 2025. Anneal architecture rule is derived.

### 12. Conditional Anneal guidance: concentrate authority, revalidate at handoff, and keep escaped assumptions visible

The comparison supports the following conditional rule for Anneal.

**Use a narrow checked preparation/publication boundary when:**

- all state that can invalidate the accepted property is observed or controlled by the boundary;
- caller/backend output can be validated before it becomes authoritative;
- the boundary can issue opaque or generation-checked handles rather than exposing raw mutable state;
- the promise is stated narrowly enough that arbitrary safe caller behavior cannot invalidate it; and
- effects that cannot be mediated are explicitly outside the promise or separately isolated.

**Inside that boundary:**

- mint capabilities for authority-changing operations instead of making possession of a generic context equivalent to permission;
- validate identities, generations, hashes, expected parent refs, and result invariants at the point of acceptance;
- own revocation/retirement rules rather than requiring every caller to remember them;
- distinguish a provider's proposed state from authoritative state; and
- fail closed when promise-relevant evidence is missing.

**Do not infer from the boundary alone:**

- semantic correctness of Charon/Aeneas/Lean transformations;
- freshness of ambient files or configuration that were not captured;
- liveness, bounded resource usage, or absence of deadlock;
- safety of arbitrary native/foreign extensions outside the mediated API;
- confidentiality or process-level fault isolation; or
- correctness of policy choices that are merely memory-safe.

This aligns with Anneal's existing design contract: trust must remain explicit, a successful result must not claim more than its evidence supports, and source/model correspondence is an additional obligation. The Tock/Asterinas evidence gives a mechanism-level reason to keep those requirements separate rather than compressing them into a generic “safe backend” abstraction.

Basis: **derived**, from the project evidence above and current Anneal design constraints.

## Boundaries

This report does not establish that every Tock capsule is benign or that every Tock deployment satisfies the same threat model. Tock explicitly allows board-specific configuration and documents isolation strength as deployment-dependent. Safe capsules can still contain logic bugs and can deny service to trusted kernel code. Hardware process isolation depends on the configured MPU and the correctness of the core kernel and hardware.

This report does not establish that every Asterinas safe API is formally proved sound. The current project documentation presents a systematic soundness argument and the ATC 2025 work includes empirical KERNMIRI evidence, but that is not the same thing as a machine-checked end-to-end theorem covering all current OSTD code and hardware assumptions. Treat the project claim and evidence at their stated level.

The report does not reproduce the Asterinas paper's unsafe-code percentages as timeless facts about Tock, Theseus, RedLeaf, or Linux. They are the Asterinas authors' measurements under their counting method and source snapshots. They are useful as evidence for the authors' motivation and reported TCB comparison, not as a current audit of those other projects.

The report does not claim that a capability type is a security boundary against arbitrary native code. Tock capabilities rely on trusted code being the only code able to construct the unsafe capability traits and on safe code being unable to forge equivalent authority. If a native extension can corrupt memory or manufacture representations, that premise is lost.

The report does not claim process isolation is sufficient for Anneal correctness. It can contain faults and authority, but the returned artifact still needs semantic and identity validation before it supports a Rust-level proof claim.

The report does not measure the performance cost of candidate Anneal boundaries. Asterinas and Tock supply architectural examples and project-specific measurements, not a benchmark of Anneal's Rust/OCaml/Lean workflow. If in-process versus subprocess placement is performance-sensitive, that remains an empirical Anneal question.

The report does not adjudicate every J006-adjacent project. RedLeaf, Rust-for-Linux, seL4, language-server process architectures, and capability-security literature can sharpen the isolation comparison, but the requested Tock/Asterinas pair is sufficient to establish the main conditional judgment without pretending those other systems have been reviewed here.

## Evidence

### Tock current source and documentation

**Tock kernel source.** `tock/tock@eaae5cbf62df2bc24ee809ff9d2c7ca124e42e73`.

- `kernel/src/lib.rs`, blob `49f9ca34fcb2683eec5765a8364ed43423f04d16`: core-kernel unsafe boundary, limited public interfaces, capability-gated sensitive operations, external extension interfaces.
- `kernel/src/capabilities.rs`, blob `dddcedda97d0e4010dc368182fff8d5181815eaa`: capability traits, trusted construction, and fine-grained authority model.
- `kernel/src/grant.rs`, blob `1d5cdd9788f923e17ef668ffb79acf06725794f5`: typed process-owned grant state, scoped access, process-lifecycle checks.
- `capsules/core/src/lib.rs`, blob `3528b00f039cb9f5142d2fd5d9e51a4b6bdbc4d5`: `#![forbid(unsafe_code)]` on a representative core capsule crate.
- `boards/components/README.md`, blob `b0436be7f565778880c0938ac22df58a2dfc085b`: components deliberately keep unsafe/capability creation visible in board setup instead of hiding it.

**Tock book.** `tock/book@760025b0d8a1d5ff14d6015c1c50ac4e30490923`.

- `src/doc/overview.md`, blob `21246fe6c30792b332d4ee790e9b0334cb20c790`: core/capsule/process architecture and MPU requirement.
- `src/doc/threat_model/threat_model.md`, blob `02a0a0d4a58bdb70ab6fcfab5bdc8d3661e38bff`: confidentiality/integrity/availability split, deployment dependence, side-channel and launch limitations.
- `src/doc/threat_model/capsule_isolation.md`, blob `811684cc0e33f07783cbb05c24f1b0db7ba6b574`: weaker language isolation for capsules, cooperative-scheduling DoS, board-integrator audit responsibility, capability guidance.
- `src/doc/soundness.md`, blob `eef0494587a4231fb9e70c24de45ea0fe99b4518`: distinction between memory unsafety and privileged system operations; capability rationale. Git history shows this document was introduced by commit `a3aa5fe717f6257dc2d50400a9baaba4680a3781` on 2024-01-06.

Primary URLs are recorded in `source-map.json`.

### Tock historical papers

**Amit Levy et al., “Multiprogramming a 64 kB Computer Safely and Efficiently.”** SOSP 2017, DOI `10.1145/3132747.3132786`. This is the early architectural source for the core/capsule/process split, grants, type-based capsule isolation, and hardware process protection.

**Tock project authors, “Tock: From Research to Securing 10 Million Computers.”** SOSP 2025, DOI `10.1145/3731569.3764828`. The retrospective is used for architectural evolution: soundness-driven ABI changes, capabilities, unsafe-code maintenance, logic bugs outside type safety, and author-reported deployment experience. Reported adoption and causal explanations are treated as the authors' retrospective account, not independent outcome verification.

The Tock papers index also preserves earlier 2015/2017 design material. Its current description of the 2015 “Ownership is Theft” paper warns readers that the authors later overcame several reported difficulties without the Rust language changes proposed there. That is relevant historical counterevidence against turning an early architecture limitation into a permanent language requirement.

### Asterinas current source and documentation

**Asterinas source and book.** `asterinas/asterinas@a5238eb6a965a4616ce07a48f5dfbc8042c4cd44`.

- `kernel/src/lib.rs`, blob `62268709b2bf43da148c61faf4e73e8b52605ee2`: top-level kernel uses `#![deny(unsafe_code)]`.
- `ostd/src/lib.rs`, blob `c8c1219b61357a703c0fc3b70ba7018178aa5d09`: privileged OSTD implementation contains the low-level unsafe initialization and hardware-facing mechanisms.
- `book/src/kernel/the-framekernel-architecture.md`, blob `dd077b771efe76a4758b82681597305509fc24d5`: mechanism/policy split, one address space, soundness/expressiveness/minimalism/efficiency requirements.
- `book/src/ostd/soundness/README.md`, blob `114f4b15ef0cd77825fd607bb0d320b31bd2335e`: current statement that OSTD is the memory-safety TCB and its public safe API is the privilege boundary.
- `book/src/ostd/soundness/what-soundness-means.md`, blob `3be761f6c0f341c351302948f12d98154cfa70e0`: explicit soundness goal, trusted/untrusted components, and the separation between UB freedom and functional/liveness correctness.
- `book/src/ostd/soundness/safe-policy-injection.md`, blob `1d9db11917f249374813862830882055d5aa854f`: independently validated scheduler/frame/slab policy outputs and callback/liveness limits.

Repository history identifies commit `cef80ffa56d85e546144aa1747485ff2bc406da0` (merged 2026-03-18) as the addition of the systematic OSTD soundness-analysis section. Later commits update API references; the current revision above is the report's source identity.

### Asterinas historical paper and evaluation

**Yuke Peng et al., “ASTERINAS: A Linux ABI-Compatible, Rust-Based Framekernel OS with a Small and Sound TCB.”** 2025 USENIX Annual Technical Conference, pp. 307–323. The paper provides the framekernel rationale, paper-era code/TCB measurements, Linux-ABI scope, selected Linux-relative benchmarks, and KERNMIRI evaluation. The report uses those measurements only as paper-era reported outcomes.

The paper's KERNMIRI evaluation is evidence that the authors exercised and found defects in unsafe OSTD behavior under its unit-test corpus. It is not treated as a proof that every current OSTD unsafe path is sound. The current 2026 documentation is the stronger source for the project's present stated soundness argument and trust model.

### Anneal applicability source

**Anneal principles and design contract.** `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, `anneal/PRINCIPLES.md` blob `d5339a95254eae14ac201139d07d9d36d48a19fb` and `anneal/DESIGN.md` blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`. These are used only to constrain transfer: successful Anneal results must not claim more than their evidence, source/model correspondence is separate from target theorem validity, and trust must remain explicit. The Tock/Asterinas-derived guidance in this report is not an adopted design decision.

## Revalidation

For a later Tock revision, the cheapest discriminating checks are:

1. inspect representative capsule crate roots for the `forbid(unsafe_code)` policy;
2. inspect `kernel/src/lib.rs` and `kernel/src/capabilities.rs` for the current core/capability boundary;
3. reread the current threat-model and capsule-isolation pages for availability and deployment assumptions; and
4. inspect grants/process-buffer ownership if the lifecycle analogy matters.

If those boundaries changed, do not infer continuity from the project name.

For a later Asterinas revision:

1. confirm whether `kernel/` still denies unsafe code and whether OSTD remains the unique privileged unsafe framework;
2. reread the current soundness goal and trust model;
3. inspect policy-injection validation for scheduler/frame/heap outputs; and
4. distinguish changes to documentation from a new formal or empirical assurance result.

For Anneal architecture work, revalidate the derived rule by asking one concrete question at each proposed boundary: **what promise-relevant bad value or state could a caller/backend produce, and what check at this boundary prevents it from becoming authoritative?** If the answer depends on ambient state the boundary cannot observe, the Tock/Asterinas analogy does not justify calling that state safe. Capture the state, retain it as explicit trust, or move to a stronger isolation/validation mechanism.