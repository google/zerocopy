# Summary

Tock and Asterinas reach a similar architectural conclusion from different starting points: a large body of safe Rust can be treated as less trusted for **memory safety** only when a smaller layer owns every mechanism that can invalidate the language's assumptions and exposes interfaces that make those assumptions unavoidable. The useful pattern is not merely "put unsafe code in one crate." The narrow layer must also own the authority to manipulate sensitive resources, validate values returned by less-trusted policy, and keep resource lifetime and execution-environment invariants true even when clients are buggy.

The two systems also show why that pattern must be scoped to a specific promise. Tock capsules are memory- and type-isolated by Rust but can still deny service because they execute cooperatively. Asterinas states the distinction even more sharply: its OSTD framework is intended to remain free of undefined behavior even if safe-Rust OS services schedule badly, waste memory, deadlock, crash, or otherwise behave incorrectly. Neither system treats memory safety as equivalent to logical correctness, availability, or semantic isolation. Hardware/process isolation remains stronger when failure containment or untrusted native code matters.

For Anneal, the strongest transferable lesson is therefore conditional: **centralize authority and boundary validation, not all policy or all semantics**. Environment preparation and publication are good candidates for narrow checked interfaces when the interface can completely validate the invariant it claims to establish. For example, a preparer can turn immutable source/tool/config identities into a checked prepared artifact, and a publisher can accept only a validated result whose provenance, scope, and TCB identity have already been checked. Tool selection, proof strategy, scheduling, and other policy can remain outside that boundary if the checked layer treats their outputs as untrusted and revalidates everything relevant to the reported promise.

That boundary cannot make inherently distributed facts disappear. Native extensions, Lean plugins, compiler or translator behavior, external executables, mutable filesystem state, toolchain semantics, and cross-process environment effects remain trusted or require stronger isolation unless Anneal can validate their effects at the boundary. A safe Rust wrapper around such behavior does not by itself shrink the TCB. This follows both from the systems evidence and from Anneal's current design contract, which says that moving an unchecked assumption behind another helper does not reduce trust.

The resulting design heuristic is:

1. Name the exact invariant the boundary protects.
2. Put only the mechanisms needed to enforce that invariant behind the boundary.
3. Give less-trusted code policy freedom through safe or constrained interfaces.
4. Treat policy outputs as hostile to the invariant and validate them again before use.
5. Keep liveness, logical correctness, semantic fidelity, and native-extension trust separate unless the boundary independently enforces those properties too.
6. Prefer process or hardware isolation, or explicit TCB admission, for behavior that cannot be constrained and checked at a language/API boundary.

This is an architectural inference for Anneal, not adopted Anneal policy.

# Applicability

This report addresses issue #3732 J006: the comparison between Tock and Asterinas as examples of small trusted mechanisms supporting larger safe interfaces, with emphasis on unsafe, extension, execution, and resource boundaries. It asks what those systems actually guarantee, what they deliberately do not guarantee, how their boundaries evolved under production pressure, and what follows for Anneal's environment-preparation and publication architecture.

The report uses three kinds of evidence.

- **Current implementation and project documentation** are pinned to exact 2026 revisions. These establish what the projects currently expose and claim about their trust boundaries.
- **Historical papers and release history** explain why those boundaries changed and report deployment, performance, and maintenance outcomes. These are primarily author accounts, not independent proofs of correctness.
- **Anneal implications** are derived analysis against the current Anneal principles and design contract. They do not change Anneal's design authority.

The comparison is intentionally narrower than a general OS-security survey. Tock and Asterinas are useful because both place large safe-Rust components next to a smaller unsafe or privileged substrate, yet they make different choices about hardware isolation, scheduling, resource ownership, and how aggressively the trusted layer revalidates policy. Those differences expose where the analogy to Anneal is strong and where it breaks.

The report does not attempt to prove either OS sound. It did not execute either kernel, rerun published benchmarks, or independently reproduce the papers' measurements. It also does not treat a small memory-safety TCB as a complete security TCB. Cryptographic correctness, authorization policy, confidentiality, availability, semantic correctness, compiler correctness, firmware, and hardware can remain trusted or outside the guarantee depending on the system.

# Findings

## 1. Tock uses several trust tiers because one boundary is not enough

Tock's architecture combines a small trusted kernel, language-isolated in-kernel capsules, and hardware-isolated user processes. Its current design documentation says that, to a first approximation, components are mutually distrustful, but the mechanism used to contain them depends on the component. Capsules run in privileged mode and rely on Rust's type and module systems; processes run with reduced privilege and rely on an MPU.

This split exists because the mechanisms buy different properties at different costs. Safe Rust gives capsules fine-grained memory/type isolation with essentially no per-component address-space or context-switch overhead. It does **not** give preemption or fault containment. Capsules participate in Tock's cooperative kernel event loop, so a capsule that spins or panics can stop useful system progress. Tock's current threat-model documentation explicitly calls the capsule boundary weaker than hardware-backed process isolation and says capsules can deny service to the rest of the system.

The process boundary is consequently not redundant. Processes can contain arbitrary-language code, can be dynamically loaded, and are isolated by hardware. They are preemptively scheduled, so the kernel does not trust a process to yield. This is a direct demonstration that "safe language" and "semantic/fault isolation" are different claims. A component can be unable to forge a Rust reference while still monopolizing execution, exhausting a first-come resource, returning nonsense, or violating an application-level protocol.

Tock therefore offers an important negative lesson for Anneal: a narrow safe API is not a universal sandbox. It can remove classes of memory-safety authority while leaving availability, native execution, and semantic behavior outside the protected property.

## 2. Tock distinguishes language unsafety from semantically sensitive authority

Tock's `unsafe` boundary is not its only privilege boundary. The kernel's `capabilities.rs` explains why. Rust's `unsafe` mechanism is coarse: code that may use `unsafe` can potentially perform any unsafe operation, while some operations are security-sensitive even though they do not violate Rust's language-level safety rules. Stopping an arbitrary process is the canonical kind of example: it may be entirely memory safe but should not be callable by any capsule.

Tock therefore represents sensitive authority with capability traits. Trusted code uses `unsafe` only to mint a value implementing a capability; ordinary APIs then require that capability in their signatures. This converts ambient privilege into an explicit object that can be distributed narrowly. The boundary protects *who may ask for an effect*, while Rust safety protects *which memory operations the implementation may perform*.

This separation maps well onto Anneal publication. A publication capability can answer "who is allowed to advance a reference or emit an authoritative result?" It cannot answer "is this result correct, complete, or derived from the right source and toolchain?" Authorization and validation are distinct mechanisms. Treating possession of an effect capability as evidence of result correctness would repeat the category error Tock's capability design is meant to avoid.

## 3. Tock's grant design makes resource ownership part of the safe interface

Tock avoids a general kernel heap because one capsule's allocations could otherwise exhaust memory needed by unrelated kernel work. Yet capsules need per-process state. Grants solve the tension by allocating that state from the requesting process's memory. The core kernel controls the grant machinery, ties references to process lifetime, and can reclaim the memory when the process exits.

This is more than a memory-safety trick. It aligns resource consumption with the principal that induced it. The 2017 SOSP paper evaluates grants against a faster unsafe pointer-based design and reports a modest cost for the lifetime checks. The current documentation emphasizes the stronger invariant: capsules do not get persistent unchecked references into process memory, and one process's demand does not silently become an unbounded global kernel allocation obligation.

Anneal can borrow the resource-accounting pattern without pretending it is a proof mechanism. Job-local work directories, per-verification quotas, content-addressed immutable artifacts, and requester-attributed temporary state can reduce cross-job contamination and bound certain denial-of-service modes. They do not establish proof correctness. The analogy is strongest for operational reliability and cleanup discipline.

## 4. Tock's history shows that a boundary has to own lifetime, not merely check inputs once

The most relevant Tock historical change is the Tock 2.0 system-call redesign. The 2025 retrospective explains that earlier buffer and callback sharing semantics did not fit Rust's ownership requirements. Tock ultimately moved responsibility for holding and managing shared application buffers and callbacks into the core kernel; capsules receive only temporary references through closures and cannot take ownership. The authors report that this required a complete rewrite of the core kernel loop and a breaking system-call redesign.

The architectural point is stronger than "add another validation check." A check at the moment a pointer crosses the boundary would not establish that the pointer remains valid after a process exits, replaces a buffer, or revokes a callback. The trusted mechanism had to own the lifetime transition and shape the client interface so stale ownership could not be expressed.

This is directly applicable to Anneal if preparation or publication spans mutable phases. If a "prepared" object is just a path into a directory that later tools may rewrite, or if a "validated" result can be paired with a different source tree at publication time, then a one-time check is insufficient. The checked layer needs an identity that survives the transition: immutable bytes, a content digest, a sealed artifact, or another binding that publication can revalidate. The boundary should own the transition from untrusted mutable state to a publishable immutable result, not merely inspect state and return a boolean.

## 5. Tock's production history also shows that the narrow layer remains a maintenance burden

Tock's retrospective reports that the amount of unsafe code stayed roughly steady while the system grew, but it also describes repeated redesign around the unsafe boundary. Current release history records security-relevant architecture bugs: a RISC-V PMP implementation could leave stale protection regions active across application switches, and Cortex-M exception handling could return an application in privileged mode. These are exactly the kinds of failures Rust's safe subset cannot prevent, because the correctness of hardware protection configuration is part of the execution environment rather than the ordinary type system.

The retrospective also says Tock would, in hindsight, have built more abstractions around unsafe operations. External dependencies remain difficult because an unsafe third-party dependency can invalidate the assumptions of every safe caller above it. Tock makes limited exceptions for high-value dependencies such as cryptographic libraries, but the authors still describe trusting general third-party libraries in this setting as an open problem.

For Anneal, a narrow boundary should therefore be evaluated by *audit surface and invariant ownership*, not by line count or crate placement alone. The layer may be small and still contain the hardest assumptions in the system. Native libraries, compiler plugins, kernel-like process launchers, filesystem mutation, and effectful FFI should not be called "outside the TCB" merely because safe Rust code invokes them through a wrapper.

## 6. Asterinas turns the same intuition into an explicit memory-safety privilege model

Asterinas's framekernel architecture makes the protected property unusually explicit. OSTD is the privileged framework and may contain unsafe Rust. Higher-level OS services, including the Asterinas kernel services, are intended to be written in safe Rust; the top-level kernel crate currently uses `#![deny(unsafe_code)]`. OSTD exposes safe abstractions for the low-level mechanisms needed to build the OS.

The current soundness documentation defines the target guarantee as: no sequence of calls to OSTD's safe public API, together with arbitrary user-space and peripheral-device behavior, should trigger undefined behavior in a safe-Rust client. It immediately distinguishes this from correctness. A scheduler may starve tasks; an allocator may make terrible choices; the OS may crash, deadlock, or behave incorrectly. The promise is that these failures do not become memory corruption, type confusion, or other UB.

This scope discipline is central to why the architecture is useful. It lets Asterinas remove a large amount of complex policy from the memory-safety TCB without pretending that policy has become correct.

The 2025 ATC paper reports that the resulting memory-safety TCB is about 14% of the Asterinas codebase and that more than 210 Linux system calls were implemented at the time of evaluation. Those are author-reported evaluation results tied to that paper's code and methodology, not an independent verification of the current tree. The current 0.18.1 documentation has since made the intended soundness argument more explicit.

## 7. Asterinas classifies resources before deciding what can leave the trusted layer

Asterinas's "sensitivity classification" is more instructive than a simple unsafe-code rule. It classifies CPU state, memory, and device resources by whether misuse can compromise kernel memory safety. Kernel page tables, stack/heap memory, interrupt-controller state, and IOMMU configuration remain sensitive. User memory, untyped frames, and carefully constrained peripheral resources can be exposed through safe interfaces when their misuse cannot corrupt the protected Rust execution environment.

The important move is to classify by consequence to the invariant, not by subsystem name. A peripheral MMIO region may be safe to expose if arbitrary writes can only break that device, while an interrupt controller is not safe to expose because it can affect global execution. Similarly, untyped physical memory can be handed to less-trusted code while typed frames that contain Rust objects remain protected.

Anneal can use the same reasoning for environment state. Some state can be treated as "insensitive" to verification soundness after normalization or sealing: a temporary log directory, a UI preference, perhaps scheduling priority. Other state can change the meaning of the proof and is therefore sensitive: source bytes, compiler/translator version, crate feature selection, target configuration, generated-model identity, trusted axioms, proof checker identity, or the exact bytes being published. A useful preparation interface should expose only the former as free policy and bind the latter into the checked artifact or TCB record.

## 8. Asterinas safe policy injection demonstrates the missing half of "move policy out"

Asterinas deliberately moves complex policies such as scheduling and allocation outside OSTD through safe traits. But OSTD does not trust the returned values merely because they came through a safe method. It protects the invariant again at the mechanism boundary.

For example, a buggy scheduler can select a task that is already running on another CPU. OSTD maintains a private execution-state flag and checks it before context switching, preventing one task from executing on two CPUs simultaneously. A frame allocator can return an already allocated or otherwise invalid frame; OSTD checks frame metadata before constructing a trusted frame handle. Similar checks defend heap slot size, alignment, ownership, and liveness.

This is the most direct analogy for Anneal policy. A proof-search strategy, backend selector, cache, build scheduler, or report assembler can be outside the core TCB **only if the trusted mechanism can check everything that policy contributes which matters to the promise**. If a scheduler chooses a toolchain, the final result needs to record and validate that identity. If an adapter returns a model, the checker needs a sound correspondence or an explicit trust entry. If a collector returns a set of proof obligations, the boundary must know whether omission is possible; otherwise the collector remains trusted for coverage.

In other words, "safe plugin API" is insufficient when plugin output can silently change verification meaning. Asterinas gets the reduction because the mechanism can recheck the policy output against private invariant state. Anneal should demand the same property before declaring a component non-TCB.

## 9. The strongest shared pattern is an invariant-complete choke point

Tock and Asterinas differ substantially, but the overlap can be stated precisely:

| Question | Tock | Asterinas | Anneal implication |
| --- | --- | --- | --- |
| What is protected by the language boundary? | Capsule access to kernel memory/resources, subject to kernel API design | OSTD memory-safety invariants against safe-Rust OS-service behavior | State the exact verification invariant before assigning trust |
| Is safe code fully trusted? | No for memory isolation, but capsules remain trusted for liveness and audited for malicious behavior | No for memory safety; safe policy may be arbitrarily wrong | Safe code can leave one TCB while remaining relevant to other promises |
| How is sensitive authority exposed? | Explicit capabilities plus unsafe-only construction | Sensitive resources stay in OSTD; safe APIs expose only constrained resources | Separate effect authority from validation; expose only state whose misuse cannot change verification meaning |
| Can policy return unchecked values? | Interfaces and core machinery constrain/lifetime-manage resources | Policy injection is followed by independent mechanism checks | Treat backend/scheduler/collector output as untrusted until invariant-complete checks pass |
| What handles stronger fault isolation? | Hardware MPU processes | Framekernel focuses primarily on intra-kernel memory safety; userspace/hardware boundaries remain | Use process isolation for untrusted native extensions or failures a safe API cannot contain |
| What happens when the original abstraction is not strong enough? | Breaking ABI/kernel-loop redesign; new ownership mechanisms | OSTD evolves abstractions and moves only insensitive policy outward | Boundary design is iterative; preserve explicit TCB entries until evidence justifies shrinking them |

The common abstraction is an **invariant-complete choke point**: a place where every transition capable of invalidating a named invariant either occurs inside trusted code or is checked before the trusted state changes. The choke point is useful only if "every" is true for that invariant.

## 10. Anneal preparation is a good candidate for such a boundary, with strict conditions

Environment preparation determines which program is being verified and under which semantics. That makes several inputs sensitive to Anneal's promise: source identity, dependency graph, features and target, translator/checker versions, trusted assumptions, and any generated artifacts that the proof consumes.

A narrow preparer can reduce distributed setup risk if it produces a value whose identity is stronger than a directory path. One possible abstract interface is:

- input: immutable source/dependency/tool/config identities plus explicit requested policy;
- action: construct or locate the environment, normalize it, and check that observed contents match those identities;
- output: a sealed `PreparedEnvironment` carrying content identities and an audit record;
- downstream rule: later stages can only consume that object, not rediscover arbitrary ambient state.

The preparer can remain small if build scheduling, downloading, caching, and tool selection are policy outside the trusted mechanism **and** the preparer can verify their outputs. A downloader can choose a mirror; the preparer checks the digest. A cache can choose a hit; the preparer checks content identity. A scheduler can choose when to run; it cannot change the bound inputs. This resembles Asterinas policy injection.

The pattern fails when preparation depends on facts the boundary cannot reconstruct or validate. If a tool reads undeclared environment variables, dynamically loads native plugins, consults a mutable registry, or executes code that mutates the source tree while translation is running, then a sealed manifest produced beforehand may not capture the actual execution. Those behaviors either need containment plus measurement, must remain explicit TCB assumptions, or require a different architecture.

## 11. Anneal publication is an even stronger fit because it is an authority transition

Publication changes an authoritative external state: a branch, result registry, cache recognized as verified, or another native projection. The operation is both semantically sensitive and irreversible enough to deserve a narrow gate.

A publication boundary should combine two ideas from the systems evidence:

- **Tock-style capability:** only holders of explicit publication authority may attempt the effect.
- **Asterinas-style revalidation:** the publisher independently checks the result object against the private invariants that make publication safe.

A useful abstract sequence is:

1. Build a result from immutable prepared inputs.
2. Check proof/model/coverage obligations and materialize a `ValidatedResult` whose fields bind program identity, promise, TCB, assumptions, and exact report bytes.
3. Let policy choose whether and where an otherwise valid result should be proposed.
4. At the publication gate, recheck identity and current native preconditions, then perform the atomic update.
5. Read back the native state and verify that the bytes/commit/effect are the intended ones.

Possession of a capability without step 2 is too weak. Step 2 without atomic native-state reconciliation is also too weak. The two solve different problems.

This structure aligns with Anneal's current principle that successful verification has a precise meaning and its design requirement that a result identify the program, promise, TCB, and assumptions. It also aligns with the current reference publication protocol, which rebuilds from the latest tip, validates the exact candidate, advances only by fast-forward, and verifies by readback.

## 12. Native extensions are where the safe-interface analogy breaks most sharply

Tock's external-dependency experience and Asterinas's resource model both warn against treating native code as ordinary safe policy. A Rust API can prevent its caller from expressing invalid Rust references, but it cannot make an arbitrary C library, Lean native plugin, compiler extension, process-injected shared object, or external binary obey the Rust abstract machine or Anneal's semantic assumptions.

There are only a few principled ways to handle such behavior:

- **Isolate it behind an OS/process boundary** and validate a narrow serialized artifact or protocol on return. This is closest to Tock's process tier. It adds process-launch, IPC, serialization, and resource costs, but it gives stronger fault containment and can support non-Rust code.
- **Admit it explicitly to the TCB**, pin its identity, and surface the assumption in the audit log. This may be appropriate for a compiler, theorem prover kernel, translator, or native dependency that cannot yet be independently checked.
- **Replace it with checkable evidence**, such as proof certificates, content hashes, independently validated model artifacts, or a smaller checker. This is the ideal long-term way to shrink trust when practical.

A safe wrapper is not a fourth option. It can constrain how callers invoke the extension, but unless it can validate all extension effects that matter to the promise, the extension's unchecked correctness remains in the TCB.

## 13. Distributed configuration is another escape hatch from a too-narrow boundary

Both systems depend on configuration that sits outside the obvious safe API. Tock's actual isolation depends on correct MPU/PMP programming, board integration, hardware descriptions, and which capsules are admitted. Asterinas explicitly trusts bootloader/firmware descriptions and core hardware, and its safe resource allocation depends on sensitive ranges having been classified and removed correctly during initialization.

Anneal has analogous distributed configuration: Cargo metadata, target features, rustc/Charon/Aeneas/Lean versions, build scripts, proc macros, environment variables, filesystem layout, and code generation. If any of these can change the program or semantics after preparation, then they are part of the trusted transition. A narrow interface can help only when it captures or revalidates the relevant state.

This argues for explicit, content-oriented identities rather than ambient conventions. A path, process ID, or tool name is not an identity if its meaning can change underneath the pipeline. The boundary should prefer digests, exact revisions, explicit feature sets, declared environment inputs, and serialized manifests. Where exact capture is impossible, Anneal should preserve the gap as an assumption instead of silently treating the helper as proof that the environment was stable.

## 14. Serious alternatives make different tradeoffs

### Hardware/process isolation around adapters

Anneal could run each translator, prover adapter, or untrusted extension in its own process or sandbox and exchange only serialized artifacts. This offers stronger crash, memory, and native-code containment than a same-process safe API. It can also impose resource quotas more naturally.

The costs are startup and IPC overhead, serialization complexity, duplicated state, weaker in-process ergonomic integration, and the need to define a sufficiently rich protocol. More importantly, process isolation does not establish semantic correctness. A sandboxed translator can still emit the wrong theorem. The receiver must validate the artifact or trust the translator for correspondence.

### Distributed backend-specific trusted code

Anneal could let each backend own its environment preparation, model translation, and publication details. This can be locally simple because the code sits next to the semantics it understands, and it may expose features faster.

The cost is a larger, heterogeneous TCB with repeated effect code and more places where ambient state can influence a result. Auditing becomes a property of many adapters rather than one protocol. This is appropriate when the required invariants are genuinely backend-specific and cannot be checked centrally, but the trust should stay explicit rather than being hidden behind a nominal common interface.

### One large trusted orchestrator

Anneal could place the entire pipeline inside one trusted coordinator that prepares environments, invokes tools, assembles results, and publishes. This minimizes interface design and makes authority location obvious.

The cost is that policy and mechanism grow together. New backend features, scheduling strategies, caches, UI behavior, and recovery logic enlarge the TCB even when they are irrelevant to verification soundness. Asterinas's safe-policy-injection result is a strong counterexample to assuming complex policy must live with the mechanism. The orchestrator is defensible early in a prototype, but it should not be called a minimal TCB unless its responsibilities are later split by checkable invariants.

### Fully proof-producing components

At the other extreme, Anneal could require each stage to emit proof or certificate evidence checked by a small kernel. This offers the cleanest trust reduction when the certificate is complete and cheap to check.

The cost is proof-system and certificate complexity, especially for source-to-model correspondence, build behavior, and effects. It may impose richer machinery on cases where simpler validation is sufficient, contrary to Anneal's preference for minimally sufficient mechanisms. The right target is selective proof production where it removes otherwise material trust, not proof objects for every mundane orchestration fact.

## 15. Conditional judgment for Anneal

The comparison supports a narrow design rule rather than a wholesale architecture transplant.

**Anneal should concentrate environment-preparation and publication authority in narrow checked interfaces when those interfaces can completely enforce the invariant they claim to protect.** Preparation should bind mutable ambient state into immutable, explicit identities. Publication should accept only a validated result, reconcile current native state, perform the minimum authorized effect, and verify it by readback. Scheduling, caching, selection, and other policy should stay outside those boundaries when the trusted mechanism can validate their outputs.

Anneal should **not** infer that all backend behavior can therefore leave the TCB. Native extensions, semantic translators, obligation collectors, proof-generating adapters, and distributed configuration remain trusted for any property the narrow layer cannot independently check. Process isolation can reduce memory/fault authority but not semantic trust. Safe Rust can remove language-level UB authority but not logical correctness or liveness authority. Explicit effect capabilities can limit who publishes but do not prove what they publish.

This conditional design matches Anneal's current contract: abstraction is legitimate only when it preserves every semantic fact relevant to the promise, and trust shrinks only when unchecked correctness is replaced by evidence. It also leaves room to evolve. A component that is trusted today can later move outside the TCB if Anneal gains a checker strong enough to validate its outputs, without changing user-facing contracts.

# Boundaries

The evidence supports the findings above with several important limits.

**Memory-safety scope.** Tock and Asterinas primarily illuminate memory/type safety and privilege separation. Their mechanisms do not automatically prove application-level functional correctness, cryptographic correctness, authorization policy, confidentiality, or availability. This report avoids treating their "safe" layers as fully untrusted in every security dimension.

**Tock trust terminology changes by layer.** Tock sometimes describes capsules as isolated or mutually distrustful while its threat model also requires integrators to audit capsules for malicious behavior and explicitly trusts them for liveness. Those statements are compatible only when the protected property is named. This report interprets "untrusted" property-by-property rather than as an absolute label.

**Asterinas soundness is a project claim with supporting analysis, not a theorem reproduced here.** The 2025 paper uses KERNMIRI testing and architectural argumentation; the current 0.18.1 book contains a more detailed soundness analysis. This run did not reproduce that testing, formally verify OSTD, or inspect every unsafe operation. The report uses Asterinas as evidence about architecture and intended invariants, not as independently established proof that the implementation is bug-free.

**Reported quantitative outcomes are revision-bound.** Asterinas's roughly 14% memory-safety TCB and performance results come from the ATC 2025 evaluation, not the 2026 main revision used for current interface analysis. Tock's deployment and unsafe-code history likewise come from the SOSP 2025 retrospective. They show practical experience but should not be read as current benchmark measurements.

**Hardware assumptions remain real.** Both architectures rely on trusted compiler/toolchain behavior and some hardware/firmware correctness. Asterinas explicitly includes the Rust compiler/core libraries, bootloader/firmware, CPU, memory controller, and IOMMU in its trust model. Tock's hardware isolation depends on correct MPU/PMP configuration. These systems do not demonstrate that a language boundary can eliminate environmental assumptions.

**No fresh execution evidence.** This report is based on exact-revision source and documentation, primary papers, and release history. It did not boot Tock or Asterinas, measure fault containment, run KERNMIRI, or reproduce historical vulnerabilities.

**Anneal implications are derived.** The recommendations about `PreparedEnvironment`, `ValidatedResult`, process isolation, capabilities, and publication gates are architectural analysis. Current Anneal documents deliberately leave many concrete integration boundaries undecided. This report must not be treated as adopting those names or interfaces.

# Evidence

## Tock

- **Documentation; current architecture.** Tock Book `design.md` at `tock/book@760025b0d8a1d5ff14d6015c1c50ac4e30490923` describes the small trusted kernel, safe-Rust capsules, MPU-isolated processes, cooperative capsule scheduling, grants, HILs, external dependency policy, unsafe boundaries, and capabilities. https://github.com/tock/book/blob/760025b0d8a1d5ff14d6015c1c50ac4e30490923/src/doc/design.md
- **Documentation; current threat model.** `capsule_isolation.md` at the same revision states that capsule isolation bans `unsafe`, depends on audited dependencies/compiler behavior, is weaker than hardware-backed isolation, and does not protect availability. https://github.com/tock/book/blob/760025b0d8a1d5ff14d6015c1c50ac4e30490923/src/doc/threat_model/capsule_isolation.md
- **Documentation; current threat model.** `threat_model.md` and `virtualization.md` document process and capsule isolation and the resource-sharing/virtualization model. https://github.com/tock/book/blob/760025b0d8a1d5ff14d6015c1c50ac4e30490923/src/doc/threat_model/threat_model.md and https://github.com/tock/book/blob/760025b0d8a1d5ff14d6015c1c50ac4e30490923/src/doc/threat_model/virtualization.md
- **Source; language boundary.** `capsules/core/src/lib.rs` at `tock/tock@78862168a64a4f9ce61c9c17370272770c4a7cbb` uses `#![forbid(unsafe_code)]`. https://github.com/tock/tock/blob/78862168a64a4f9ce61c9c17370272770c4a7cbb/capsules/core/src/lib.rs
- **Source; capability boundary.** `kernel/src/capabilities.rs` explains that `unsafe` is too coarse for all sensitive operations and defines unsafe-minted capability traits required by restricted safe APIs. https://github.com/tock/tock/blob/78862168a64a4f9ce61c9c17370272770c4a7cbb/kernel/src/capabilities.rs
- **Source; resource/lifetime boundary.** `kernel/src/grant.rs` documents and implements per-process grant state and controlled access to process-owned memory. https://github.com/tock/tock/blob/78862168a64a4f9ce61c9c17370272770c4a7cbb/kernel/src/grant.rs
- **Source; hardware isolation authority.** `kernel/src/platform/mpu.rs` marks MPU configuration as an unsafe contract because an incorrect implementation can expose kernel/private memory or peripherals. https://github.com/tock/tock/blob/78862168a64a4f9ce61c9c17370272770c4a7cbb/kernel/src/platform/mpu.rs
- **Documentation/history.** `CHANGELOG.md` records Tock 2.x ownership/API redesigns and security-relevant PMP/exception-handler fixes. https://github.com/tock/tock/blob/78862168a64a4f9ce61c9c17370272770c4a7cbb/CHANGELOG.md
- **Author paper; original mechanism and costs.** Levy et al., "Multiprogramming a 64 kB Computer Safely and Efficiently," SOSP 2017, DOI 10.1145/3132747.3132786. The paper introduces grants and evaluates their overhead against an unsafe pointer-based design. https://tockos.org/assets/papers/tock-sosp2017.pdf
- **Author retrospective; historical changes and reported outcomes.** Schuermann et al., "Tock: From Research to Securing 10 Million Computers," SOSP 2025, DOI 10.1145/3731569.3764828. The paper documents the Tock 2.0 system-call/core-loop redesign, external-dependency tension, long-term unsafe-code containment, production adoption, and lessons about unsafe abstractions. https://tockos.org/assets/papers/2025-sosp-tock-decade.pdf

## Asterinas

- **Documentation; architecture.** `book/src/kernel/the-framekernel-architecture.md` at `asterinas/asterinas@a5238eb6a965a4616ce07a48f5dfbc8042c4cd44` describes privileged OSTD mechanisms and de-privileged safe-Rust OS services. https://github.com/asterinas/asterinas/blob/a5238eb6a965a4616ce07a48f5dfbc8042c4cd44/book/src/kernel/the-framekernel-architecture.md
- **Documentation; current soundness goal.** `book/src/ostd/soundness/what-soundness-means.md` distinguishes UB-freedom from logical correctness and names trusted and untrusted components for the memory-safety argument. https://github.com/asterinas/asterinas/blob/a5238eb6a965a4616ce07a48f5dfbc8042c4cd44/book/src/ostd/soundness/what-soundness-means.md
- **Documentation; resource classification.** `sensitivity-classification.md` classifies CPU, memory, and device resources by whether misuse can break kernel memory safety. https://github.com/asterinas/asterinas/blob/a5238eb6a965a4616ce07a48f5dfbc8042c4cd44/book/src/ostd/soundness/sensitivity-classification.md
- **Documentation; mechanism/policy split.** `safe-policy-injection.md` describes safe scheduler and allocator injection plus independent OSTD checks that preserve private safety invariants despite bad policy. https://github.com/asterinas/asterinas/blob/a5238eb6a965a4616ce07a48f5dfbc8042c4cd44/book/src/ostd/soundness/safe-policy-injection.md
- **Documentation; device boundary.** `safe-kernel-peripheral-interactions.md` describes untyped DMA buffers, IOMMU enforcement, sensitive MMIO/PIO removal, and the limits when IOMMU is absent. https://github.com/asterinas/asterinas/blob/a5238eb6a965a4616ce07a48f5dfbc8042c4cd44/book/src/ostd/soundness/safe-kernel-peripheral-interactions.md
- **Source; safe service layer.** `kernel/src/lib.rs` uses `#![deny(unsafe_code)]`. https://github.com/asterinas/asterinas/blob/a5238eb6a965a4616ce07a48f5dfbc8042c4cd44/kernel/src/lib.rs
- **Source; privileged mechanism layer.** `ostd/src/lib.rs` contains unsafe initialization and low-level architecture setup whose safety comments name bootstrap and one-time-use invariants. https://github.com/asterinas/asterinas/blob/a5238eb6a965a4616ce07a48f5dfbc8042c4cd44/ostd/src/lib.rs
- **Documentation/history.** `RELEASES.md` shows continued movement of policy/mechanism boundaries, including moving PCI out of OSTD, soundness fixes, DMA refactoring, and the addition of the OSTD soundness analysis. https://github.com/asterinas/asterinas/blob/a5238eb6a965a4616ce07a48f5dfbc8042c4cd44/RELEASES.md
- **Author paper; architecture and evaluation.** Peng et al., "ASTERINAS: A Linux ABI-Compatible, Rust-Based Framekernel OS with a Small and Sound TCB," USENIX ATC 2025, pp. 307-323; arXiv:2506.03876. The paper reports the framekernel design, safe policy injection, a memory-safety TCB around 14% of evaluated code, more than 210 system calls, performance measurements, and KERNMIRI testing. https://www.usenix.org/conference/atc25/presentation/peng-yuke and https://arxiv.org/abs/2506.03876

## Anneal

- **Normative project authority.** `anneal/PRINCIPLES.md` at `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92` states the no-fail-open promise, explicit TCB audit log, always-on UB-freedom, extensibility, and preference for depth over point solutions. https://github.com/google/zerocopy/blob/cc135f46155b72e4b51188525c2974a3b84acf92/anneal/PRINCIPLES.md
- **Normative project authority.** `anneal/DESIGN.md` at the same revision requires precise result identity/scope, justified Rust semantics, sound abstraction boundaries, an explicit and shrinkable TCB, and minimally sufficient mechanisms. It explicitly warns that moving an unchecked assumption into a helper does not reduce trust. https://github.com/google/zerocopy/blob/cc135f46155b72e4b51188525c2974a3b84acf92/anneal/DESIGN.md
- **Derived analysis.** The preparation/publication architecture, capability split, process-isolation recommendation, and invariant-complete-choke-point terminology in this report are interpretations of the systems evidence under Anneal's current constraints. They are not statements from the cited projects and are not current Anneal design decisions.

# Revalidation

Revalidate this report when any of the following changes materially:

- Anneal decides the concrete boundary among Rust, Charon, Aeneas, Lean, environment preparation, result validation, and publication.
- Anneal adopts a certificate or correspondence checker that can independently validate outputs currently treated as trusted.
- Anneal introduces native plugins, in-process FFI extensions, build isolation, or a sandbox model whose authority differs from the assumptions analyzed here.
- The Tock threat model, capsule `unsafe` policy, capability model, grant ownership model, or hardware-isolation model changes materially from the pinned 2026 revisions.
- Asterinas changes the OSTD/OS-service privilege boundary, its definition of soundness, safe policy injection, or its sensitive-resource classification.
- New independent evidence materially weakens the author-reported claims about the systems' boundaries or evaluation results.

A future revalidation should compare semantic changes, not merely update commit hashes. In particular, check whether the named invariant is still the same, whether less-trusted policy outputs are still independently validated, and whether any new extension mechanism introduces unchecked behavior that crosses the boundary.