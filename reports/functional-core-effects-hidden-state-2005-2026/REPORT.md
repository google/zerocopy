# Functional cores do not make external effects disappear

## Summary

Functional-core/imperative-shell, ports-and-adapters, effect systems, and sans-I/O all improve a system by making some effects cross an explicit boundary. They differ in what the boundary means. A functional core tries to make important computation depend only on values. Ports and adapters organize external conversations by purpose rather than technology. Sans-I/O turns a protocol implementation into a caller-driven state machine. Effect systems can make a language-level set of effects part of a computation's static interface. None of these techniques, by itself, makes an opaque compiler or prover subprocess a pure function.

That distinction matters for Anneal. A subprocess may observe source and dependency files, search paths, environment variables, its working directory, plugins or dynamically loaded code, executable and library versions, clocks, randomness, network services, process-global caches, or state left by earlier requests. If any of those observations can change the Rust-level claim, they are semantic inputs even when they are absent from the function signature used to launch the process. If they affect only whether or when a result is produced, they are still operational effects that the engine must control well enough to avoid stale publication, cross-request interference, or incorrect cache reuse.

The strongest useful pattern is therefore **property-relative effect closure**, not purity by naming. Anneal should keep deterministic transformations and acceptance predicates as value-oriented as practical, and should put external interactions behind explicit host/backend boundaries. At each boundary it should classify effects into at least four groups: semantic inputs that must be captured or trusted, execution policy such as timeout and cancellation, observational output such as progress and diagnostics, and authority-changing effects such as artifact installation or publication. An opaque backend may be treated *as if* it were a repeatable function only when its material input environment is captured or isolated tightly enough for that claim, or when the remaining ambient behavior is explicitly accepted into the result's trust boundary.

The Remote Execution API provides a useful counterpoint. Its `Action` makes command identity, an input-root digest, timeout, and platform requirements part of a repeatable execution description, while `Command` separately records arguments, environment variables, output paths, and working directory. Yet the same specification leaves some worker environment, including available system libraries and mounted filesystems, implementation-specific; its PATH lookup rules also changed in API v2.3. Even an API designed around repeatable actions therefore needs an explicit residual environment contract. Anneal should expect at least that much discipline before caching or reusing an opaque Charon/Aeneas/Lean execution as though it were pure.

The conditional recommendation is not to impose a general effect framework everywhere. Use simple value-passing where it is faithful; use purpose-defined ports for host authority; use event/state-machine APIs where upstream tools naturally support them; and use process isolation plus captured environment identity where they do not. A language effect system could strengthen Anneal's own in-process interfaces, but it cannot statically account for arbitrary behavior behind FFI, plugins, or subprocesses without modeling or mediating those boundaries. The main architectural invariant is that hidden state must not be allowed to become hidden *semantic authority*.

Basis: **documentation + normative protocol/source + literature + existing Anneal execution reports + derived comparison**.

## Applicability

This report addresses #3732 J030: where effects and hidden state should live in a verification orchestration architecture. It is not a claim that Anneal must use one of the named patterns literally, nor that the named patterns are equivalent.

The historical comparison covers four related but different ideas:

- Alistair Cockburn's 2005 Ports and Adapters description, which moves UI, databases, feeds, and other external technologies outside an application boundary and connects them through purpose-defined ports;
- Gary Bernhardt's 2012 *Boundaries* account, which emphasizes simple values at subsystem boundaries and is the public source associated with the functional-core/imperative-shell formulation;
- the 2016-era Python sans-I/O guidance preserved at `brettcannon/sans-io@b4679927d555cb27d9960ae203c0ecd0d8209771`, which removes network I/O and asynchronous flow control from protocol implementations and has the caller drive them with bytes/events; and
- algebraic effects/effect handlers and row-polymorphic effect typing, using Plotkin and Pretnar 2009 and Leijen 2014 as representative formal accounts of making computational effects explicit in a language semantics or type.

The subprocess comparison uses the Remote Execution API at `bazelbuild/remote-apis@adbf4a27c86fbea4a37637a6cbcacef372406fe7`. It is not offered as a complete build-system survey. It supplies one mature example where repeatability is valuable enough that command, input-root, environment, platform, timeout, and cache behavior are represented explicitly, while some executor environment remains outside the action description.

The Anneal application is derived against `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, especially `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`. Those documents require meaningful source/result identity, justified Rust semantics, faithful accounting for behavior relevant to the promise, explicit trust, and minimally sufficient mechanisms. They deliberately do not choose the exact boundary among Anneal, Rust, Charon, Aeneas, Lean, and reusable proof libraries. The recommendations below are therefore design analysis, not adopted Anneal policy.

The report also reuses two current reference-corpus results as evidence rather than re-running them. `anneal-3730-rust-input-snapshot-2026-09-29` demonstrates that a principal Rust source file does not close Cargo's semantic input set: an included file, active feature set, and manifest defaults can change compiled behavior while that source file is unchanged. `anneal-3730-fault-model-2026-09-29` demonstrates, in a bounded model and one fake-subprocess replay, why generation, ownership, result completeness, status, and request correlation matter before publication. Those reports do not by themselves establish J030's architectural judgment.

## Findings

### The four approaches make different promises about the boundary

The phrase “move effects to the edge” hides several distinct mechanisms.

**Functional core / imperative shell** is primarily a decomposition heuristic. Bernhardt's *Boundaries* presentation argues for simple values between components and associates the approach with a functional core surrounded by an imperative shell. The core becomes easier to reason about because its inputs and outputs are ordinary values rather than calls into a web of mutable collaborators. The shell still performs effects. Nothing in that decomposition alone proves that the shell has found every effect the core's result depends on.

For Anneal, this is most useful for code such as request normalization, derivation of identity manifests, invalidation calculations, result classification, and publication predicates. Given explicit inputs, those functions can be deterministic. It is much less meaningful to call `run_charon(request) -> llbc` or `query_lean(document) -> goals` a pure core simply because the Rust wrapper has a value-shaped signature. The child process or server may consult state not represented in `request`.

Basis: **documentation** for Bernhardt's boundary/value framing; **derived** application to Anneal.

**Ports and adapters** is about dependency direction and substitutable conversations, not necessarily purity. Cockburn's original article says the application should be usable without a UI or database, should be drivable by users, programs, tests, or batch scripts, and should communicate with external entities through ports whose adapters translate particular technologies. The important abstraction is the *purpose* of the conversation. A database port, for example, can have a real adapter or an in-memory testing adapter.

That is directly relevant to Anneal because it suggests naming ports after semantic authority rather than current products: a source-snapshot provider, environment preparer, model extractor, proof checker, result publisher, or clock/cancellation service can be more stable boundaries than modules named only `charon`, `aeneas`, or `lean`. But a port can still expose an underspecified effect. A “run translator” port whose contract says nothing about filesystem search, environment discovery, plugins, or output ownership has moved the effect behind an interface without controlling it.

Basis: **documentation** from Cockburn 2005; **derived** application to Anneal.

**Sans-I/O** is a stronger operational transformation for a suitable domain. The Python guidance defines a sans-I/O protocol implementation as one that performs no network I/O and no asynchronous flow control. The caller supplies bytes; the protocol implementation parses them, updates protocol state, emits bytes or semantic events, and returns synchronously. The guidance explicitly argues that this reduces control-flow and I/O failure complexity and lets synchronous, threaded, and asynchronous shells reuse the same protocol state machine. Its integration section is equally important: actual I/O still has to happen somewhere, and pushing the pattern through a larger codebase requires a deliberately small nucleus that owns I/O and flow control.

The analogy to Anneal is useful only where an upstream interface can be expressed as a sufficiently complete state machine. A parser, obligation graph, scheduler transition function, or protocol decoder may fit. A compiler process that discovers files, loads plugins, reads process environment, invokes build scripts, and consults on-disk caches does not become sans-I/O because the parent exchanges JSON with it. The parent has only moved *transport I/O* out of sight; the child's semantic I/O remains.

Basis: **documentation/source** at `brettcannon/sans-io@b4679927d555cb27d9960ae203c0ecd0d8209771`; **derived** limit for opaque tools.

**Effect systems and handlers** give a language-level account rather than merely an architectural convention. Plotkin and Pretnar's algebraic-effect work treats operations such as state, I/O, nondeterminism, concurrency, and time as effects with handlers that interpret computations. Koka's row-polymorphic effect types make the potential effects of a function visible in its type and prove properties tied to that effect discipline—for example, the cited 2014 paper gives a semantic guarantee for the absence of an unhandled exception when the exception effect is absent.

This is stronger than a naming convention inside the language being typed. It is not automatically an end-to-end account of an opaque process. If an effect-typed Anneal function calls an FFI shim whose implementation reads `$HOME`, loads a plugin, or launches a compiler that reads undeclared files, the type system can describe the *call operation* but cannot infer all of the foreign implementation's ambient dependencies unless those dependencies are represented in the language model and mediated by the handler. The trusted boundary has moved to the handler/foreign operation contract.

Basis: **literature** — Plotkin and Pretnar 2009, DOI `10.1007/978-3-642-00590-9_7`; Leijen 2014, DOI `10.4204/EPTCS.153.8`; foreign-boundary conclusion is **derived**.

The approaches therefore form no simple ladder from weak to strong. Ports can improve architectural ownership without purity. Sans-I/O can produce a deterministic protocol core without a type-and-effect system. Effect typing can prove a static property about in-language code while saying little about undeclared behavior of a foreign implementation. Functional-core decomposition can be valuable even in a language with no purity tracking. Anneal should select the mechanism that makes the relevant effect boundary *true*, not the one with the strongest-sounding vocabulary.

### A subprocess is not a pure function unless its environment is part of the contract

The Remote Execution API makes the missing contract concrete. At revision `adbf4a27c86fbea4a37637a6cbcacef372406fe7`, an `Action` contains the digest of a `Command`, the digest of the complete input-root directory, a timeout, cache policy, optional salt, and platform requirements. `Command` contains arguments, explicit environment variables, output paths, and a working directory. The protocol describes an Action as capturing the information needed to reproduce an execution and makes its serialized digest the cache identity.

But the same protocol documents residual ambient state. Unless constrained elsewhere, the worker's available system libraries, binaries, mounted filesystems, and other environment are implementation-specific. PATH lookup is especially instructive: the comment records that v2.3 changed command-resolution rules because v2.2's stricter rule did not match what many implementations already did. Platform properties can constrain OS family and ISA, but servers may define additional properties and environment setup.

So even a protocol designed for content-addressed repeatable execution does not obtain purity merely from `Action -> ActionResult`. It obtains useful repeatability by making a large input closure explicit and by placing the remaining environment behind a documented executor contract. When residual state matters, clients need stronger platform constraints, sandboxing, explicit inputs, disabled caching, salt/namespace separation, or some equivalent mechanism.

For Anneal, the direct lesson is that a backend request is not a semantic cache key until the engine can explain the closure behind it. A tuple such as `(source_hash, tool_version)` is insufficient if the tool can see a different Cargo feature selection, included file, search path, imported `.olean`, plugin, dynamic library, environment variable, or process-local generation. Current reference evidence already has concrete counterexamples for some of those categories.

Basis: **normative protocol/source** — `remote_execution.proto` and `platform.md` at `bazelbuild/remote-apis@adbf4a27c86fbea4a37637a6cbcacef372406fe7`; **execution** from the existing Anneal Cargo input-closure report; Anneal cache conclusion is **derived**.

### “Explicit effects” should be separated into semantic inputs, policy, observation, and authority

A single undifferentiated `Effects` object would make Anneal more explicit while still obscuring the properties that matter. The engine needs at least four distinctions.

| Effect class | Examples | What Anneal needs from it |
| --- | --- | --- |
| Semantic input | source/dependency bytes, cfg/features, generated files, tool/config identity, imported proof environment, plugin code/config, material environment/search paths | Capture in the verification subject/environment identity, validate on use, or state as explicit trusted assumptions. A change that can change the claimed semantics cannot be silently hidden behind a cache key. |
| Execution policy | timeout, cancellation, retry, worker selection, memory/CPU limits | Control and fence it so policy cannot authorize stale or partial publication. Include it in semantic/action identity when it can change reusable output; otherwise keep it separate from the claimed program meaning. |
| Observation | progress, logs, diagnostics, timing measurements | Preserve origin/request identity where users or automation consume it, but do not treat observation alone as acceptance evidence unless the acceptance contract says so. |
| Authority-changing effect | installation, shared-cache mutation, generated-artifact replacement, “current” pointer/ref update, publication | Serialize or fence the authority transition and verify the complete artifact/result being selected. A deterministic computation that *decides* what to publish does not make publication itself pure. |

The boundaries are property-relative. Time illustrates this. A wall clock used only to timestamp a log is observational. A deadline can be execution policy. A timeout included in a cacheable remote `Action` becomes part of execution identity because a shorter timeout can turn a would-have-succeeded run into failure. A compiler plugin that calls the clock and embeds the time in generated code makes the clock a semantic input. The same external resource can therefore occupy different classes in different stages.

Cancellation likewise should not be modeled as a universal semantic input. In the ideal case it only withdraws demand for work. But if cancellation kills a process after it has mutated a shared cache or written a partial artifact, it has authority and cleanup consequences. The existing Anneal fault-model report found a bounded counterexample when one consumer's cancellation killed a shared job still owned by another, and it separately required complete output plus generation/status/request fences before publication. That is evidence for treating cancellation ownership and publication as explicit state transitions rather than exceptions from an otherwise pure call graph.

Basis: **normative protocol/source** for Remote Execution timeout identity; **execution** from `anneal-3730-fault-model-2026-09-29`; taxonomy and transfer are **derived**.

### Filesystem and environment effects are semantic when they influence translation or checking

The temptation to place filesystem reads in an imperative shell and call the resulting compiler invocation pure works only if the shell has captured everything the compiler can semantically observe. Current corpus evidence shows why this is a real obligation rather than stylistic caution.

`anneal-3730-rust-input-snapshot-2026-09-29` kept one principal Rust source unchanged while changing an `include_str!` payload, Cargo feature activation, or manifest defaults and observed different compiled behavior. Its report explicitly leaves many other dimensions unclosed: environment variables, target triples, build scripts, dependency resolution, external models, generated artifacts, and native links. That means an Anneal source snapshot cannot be just “the `.rs` files the editor knows about” if later stages delegate compilation semantics to Cargo/rustc/Charon under broader inputs.

The same pattern applies downstream. If Lean imports are resolved through a search path, the proof environment includes the actual imported artifacts and resolution context, not only the text of the current proof document. If Aeneas loads configuration or model files, they are part of the stage's semantic environment. If any stage permits plugins or native extensions, their binaries/configuration and the ambient resources they may inspect become part of the trust/input story unless the host mediates them more tightly.

The right architectural question is therefore not “did the effect happen in the shell?” It is “could this observation change what claim the stage's output justifies?” If yes, the resulting identity/TCB must account for it somewhere.

Basis: **execution** from current reference input-closure and Lean environment reports; **derived** criterion.

### Sans-I/O shows how to externalize a real effect; it also shows the cost

The sans-I/O guidance is valuable because it does more than wrap an I/O API behind a trait. It changes the protocol implementation's state machine: the caller provides bytes and drives flow control, while the core exposes events and output bytes. The approach gains portability because the core no longer chooses sockets, threads, or async runtime behavior.

That transformation has a cost. The integration layer must now own the state machine's progress: reads, writes, backpressure, connection lifecycle, timeouts, scheduling, and errors. The guidance notes that a whole application can push these primitives to a tiny nucleus, but doing so requires sustained discipline and may feel less native to a given I/O framework. Existing h11 source notes also place timeout control at a higher layer rather than in the HTTP/1.1 state machine.

That cost is instructive for Anneal. A genuinely sans-I/O Charon or Lean API would require upstream behavior to be exposed as explicit state plus requests/events, with file contents/import results/time/cancellation supplied by the host as data or operations. If the upstream implementation instead owns file opening, module resolution, worker spawning, or process-global caches, Anneal has not obtained the sans-I/O property. Building a large mirror layer to simulate it from outside may cost more and be less reliable than using one-shot processes or a purpose-built upstream service API.

Sans-I/O also provides no logical-correctness theorem by itself. h11 is a mature bring-your-own-I/O HTTP state machine, yet its project published a 2025 security advisory for malformed chunked-encoding acceptance that could contribute to request smuggling when composed with differently buggy peers. The point is not that sans-I/O failed. It is that removing transport I/O narrowed the state space and improved testability without proving the remaining parser semantics correct.

Basis: **documentation/source** at `brettcannon/sans-io@b4679927d555cb27d9960ae203c0ecd0d8209771`, `python-hyper/h11@62c5068c971579d61fa1b55373390e12f25fd856`, and h11 advisory `GHSA-vqfr-h8mv-ghfj`; architecture/correctness distinction is **derived**.

### Ports should be named after authority, not merely after products

A product-shaped boundary is sometimes appropriate: a `LeanBackend` really does need Lean-specific operations. But Cockburn's original motivation suggests a more durable first cut for Anneal's host responsibilities.

For example, “prepare an environment in which model X and proof document Y resolve against these exact dependencies” is a purpose. Local-process, containerized, remote-execution, and eventually in-process implementations could all be adapters if they can satisfy the same contract. “Publish this complete result only if generation G still owns the current subject” is another purpose. A Git-tree publisher and a local immutable-cache publisher might implement different versions of that authority boundary. Conversely, a single generic `Backend::run(bytes) -> bytes` port says almost nothing about the guarantees its adapters must preserve.

This also avoids overpromising substitutability. Charon, Aeneas, and Lean have different failure modes, incremental-state semantics, and trust roles. One trait can be convenient without meaning the components are behaviorally interchangeable. Purpose-specific ports let common orchestration live above them while preserving stage-specific contracts underneath.

Basis: **documentation** from Cockburn 2005; **derived** Anneal application.

### Effect typing is most useful inside the host, not as a substitute for environment capture

An effect-aware API could help Anneal's own implementation. A function whose type makes it clear that it may read an environment snapshot, allocate an artifact, query a clock, or request cancellation can be easier to test and review than one with ambient globals. Algebraic handlers also suggest a clean test strategy: production handlers perform real effects, while test handlers supply controlled responses.

The strongest formal claims, however, stop at the language boundary unless foreign operations carry adequate semantics. An effect label such as `Process` can reveal that a function launches a process; it does not state which files that process reads, whether it consults `$PATH`, which plugins it loads, whether it is reentrant, or whether two invocations share state. Splitting `Process` into more labels improves documentation only to the extent that the wrapper can actually enforce the distinction.

For Anneal this argues against making an effect framework the first architectural dependency. First establish the semantic and authority contracts that backends must obey. Then an effect system, capability types, or ordinary explicit parameters can encode those contracts where it reduces mistakes. A runtime environment validator or sandbox may still be required for facts that another process can violate after the host's Rust types have been checked.

Basis: **literature** on algebraic effects and Koka effect types; **derived** foreign-process limit.

### Opaque tools admit three defensible levels of effect control

The literature and execution evidence do not force one answer for every stage. They support three useful operating points.

**1. Captured/hermetic execution.** The host constructs a closed or tightly bounded input tree, pins the executable/toolchain, passes an explicit environment, restricts external filesystem/network access, records platform-sensitive properties, and owns outputs. This makes content-addressed reuse and cross-worker execution most defensible. It is also the most engineering-intensive and may be difficult for tools whose normal operation expects a rich host installation.

**2. Controlled but trusted ambient execution.** The host pins the major tool/configuration identities, isolates output directories and request generations, records known ambient assumptions in the TCB/result, and does not claim cache equivalence across environments it cannot justify. This can be a pragmatic initial posture for Charon/Aeneas/Lean while keeping uncertainty explicit. It sacrifices some reuse and reproducibility rather than pretending hidden inputs do not exist.

**3. Ephemeral one-shot execution.** The host starts a fresh process for each semantic request, supplies the intended request inputs, isolates writable outputs, and discards the process afterward. This does not close ambient filesystem/environment effects, but it sharply reduces process-local cross-request state and makes cleanup/failure boundaries simpler. It may be the correct conservative default where persistent-worker state is poorly specified and latency is acceptable.

A persistent worker is not a fourth semantic model. It is an optimization that can be layered on one of these levels if the host can name and validate the worker/environment generation, reset or partition mutable state, and fence late results. If it cannot, persistence changes the semantic risk rather than merely the performance profile.

Basis: **normative protocol/source + existing Anneal execution evidence + derived design comparison**.

### The minimum effect surface is determined by the claim, not by implementation convenience

Anneal's design contract says that every operation and behavior relevant to the reported promise must be accounted for rather than disappearing because the model or proof interface omitted it. Applied to orchestration, this yields a practical test for every candidate hidden effect:

1. Can varying this value or event while holding the declared request fixed change the Rust behavior being claimed, the generated model/obligation, the proof environment, or the acceptance decision?
2. If yes, can Anneal capture it as identified input or independently validate that it is irrelevant?
3. If neither is practical, is the remaining dependency explicit in the result's TCB/assumptions and excluded from unsafe cache equivalence?
4. Can the effect mutate shared state or authority even if it does not change the mathematical claim?
5. If yes, what generation/ownership/atomicity rule prevents stale or partial state from becoming current?

This is deliberately stricter than “make side effects explicit.” It asks explicit *for which property*. A log write may not enter source/model identity. A plugin discovery path almost certainly must if plugins can alter translation. A monotonic clock may be irrelevant to proof semantics but essential to cancellation/resource accounting. A publication pointer is not semantic input to a proof, yet selecting it is a high-authority effect.

Basis: **Anneal design authority + derived synthesis**.

### Conditional Anneal architecture

The evidence supports the following architecture if Anneal continues to combine Rust-hosted orchestration with Charon/Aeneas/Lean processes or servers.

Keep a **value-oriented engine core** for request identities, dependency/invalidation calculations, job ownership, acceptance predicates, and proposed state transitions. These computations should consume explicit immutable records rather than reach into the filesystem or global process state when practical.

Put external behavior behind a small set of **authority-bearing host ports**: source/workspace capture, environment preparation, backend execution, clock/cancellation/resource control, artifact storage, and publication. Define each port by the invariants it must preserve, not by the name of today's tool.

Have environment preparation produce an explicit **execution manifest** or equivalent handle that binds the material source/model/dependency/tool/plugin configuration known to the host. The manifest need not prove perfect hermeticity on day one. It must distinguish captured facts from residual trusted ambient assumptions so later sandboxing or upstream APIs can shrink that trust without redesigning the user contract.

Treat Charon/Aeneas/Lean adapters as **effectful** until their actual contracts justify stronger claims. A persistent service should return outputs tied to a request/environment/document generation. A one-shot process should still have isolated writable output and explicit environment capture where feasible. The engine should never infer “pure” merely from a deterministic-looking RPC signature.

Represent **cancellation and timeout as execution policy plus ownership state**, not as silent exceptions in backend calls. If they can change cacheability or reusable outputs, incorporate them into action identity as the Remote Execution API does for timeout; otherwise keep them out of semantic subject identity but retain fences that prevent cancelled, failed, partial, or stale work from publishing.

Treat **plugins and native extensions as first-class trust/environment inputs** unless Anneal can mediate them. A plugin that can execute arbitrary host code escapes an in-process effect discipline and a simple source snapshot. Either isolate/disable it, capture its identity and material configuration, or make its unchecked behavior visible in the result's TCB.

Do not require a general algebraic-effect implementation merely to achieve this. Ordinary Rust value types, capability objects, runtime manifests, isolated processes, and generation checks may be sufficient. Adopt a stronger effect system only where it materially improves enforcement or reasoning rather than duplicating a contract that still depends on runtime foreign behavior.

Basis: **derived conditional judgment** from all evidence above. This is not adopted Anneal design policy.

## Boundaries

**No empirical performance comparison.** This report does not benchmark functional-core, ports-and-adapters, effect handlers, sans-I/O, one-shot processes, sandboxing, or persistent workers. It cannot say whether the proposed boundaries are fast enough for Anneal's live workflow.

**The named architecture sources are not outcome studies.** Cockburn 2005 and Bernhardt 2012 are first-party design accounts, not controlled experiments proving maintenance or defect-rate improvements. The sans-I/O document gives design rationale and examples, not causal measurements across matched implementations.

**Effect-system theorems are language-relative.** Koka's static effect guarantees and the algebraic-effect literature concern programs interpreted under their formal language semantics. They do not establish that arbitrary native code, FFI, a compiler subprocess, or a plugin obeys a corresponding effect discipline.

**Sans-I/O is narrower than “pure.”** A state machine can have internal mutable state while doing no I/O. It can also contain logic bugs. Conversely, a function can perform an abstract effect through a handler while remaining tractable to formal reasoning. This report does not equate I/O-freedom, immutability, determinism, referential transparency, and correctness.

**Hermetic execution is not fully specified by the examined Remote Execution API.** The API identifies input roots, commands, environment variables, platform requirements, timeout, and outputs, but explicitly leaves parts of worker environment implementation-specific. A concrete executor/sandbox contract must be examined before claiming full hermeticity.

**No claim that timeout always belongs in semantic identity.** The Remote Execution API includes timeout in `Action` identity for its caching semantics. Anneal may reasonably separate policy identity from program/model identity when a timeout only determines whether a result arrives. The requirement is to prevent a policy difference from causing invalid reuse or publication, not to copy the API field structure.

**No complete enumeration of Anneal inputs.** Existing Cargo and Lean reports show that obvious source paths are incomplete, but this report does not establish the final closure of Rust, Charon, Aeneas, Lake, Lean, linker, plugin, OS, or network inputs for every supported subject.

**No upstream reentrancy claim.** The report does not establish that current Charon, Aeneas, or Lean APIs can be safely embedded, reset, replayed, or transformed into sans-I/O state machines. Where that matters, exact upstream source and execution need separate investigation.

**Selection bias.** The report chose successful, recognizable architectural patterns because they expose distinctions relevant to Anneal. h11's security advisory is one deliberate unfavorable case, but this is not a systematic empirical review of failed effect architectures.

**Anneal implications are derived.** `PRINCIPLES.md` and `DESIGN.md` remain authoritative. Nothing here adopts a backend API, cache key, sandbox, effect library, plugin policy, or process topology.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-30.

### Ports and adapters

Alistair Cockburn, *Hexagonal architecture the original 2005 article*, HaT Technical Report 2005.02, version 0.9, dated 2005-09-04: <https://alistair.cockburn.us/hexagonal-architecture/>. The report uses the article for the inside/outside distinction, purpose-defined ports, technology-specific adapters, replaceability with mocks/test drivers, and the goal of running application logic without the final UI/database devices.

Basis: **documentation / first-party design account**.

### Functional core / value boundaries

Gary Bernhardt, *Boundaries*, SCNA 2012: <https://www.destroyallsoftware.com/talks/boundaries/>. The public talk page describes simple values as component/subsystem boundaries and identifies the associated Functional Core, Imperative Shell material. The report does not infer a formal purity theorem from the talk.

Basis: **documentation / first-party design account**.

### Sans-I/O

Repository `brettcannon/sans-io`, revision `b4679927d555cb27d9960ae203c0ecd0d8209771`, especially `how-to-sans-io.rst` blob `afaddd4bb36c6268d1e77bcb6d9e618cd271478f`. It defines an I/O-free protocol implementation, explains caller-provided bytes/events and external flow control, and discusses the benefits and integration cost of moving I/O to a small outer nucleus.

Repository `python-hyper/h11`, revision `62c5068c971579d61fa1b55373390e12f25fd856`, `README.rst` blob `5f2861600c543733424127ed0baa70e62c647373` and `notes.org` blob `36fd741bdac7294c42a1bb41f25c93821a39fdb3`. h11 is a concrete bring-your-own-I/O HTTP/1.1 implementation; its notes place timeout concerns above the low-level protocol implementation.

GitHub Security Advisory `GHSA-vqfr-h8mv-ghfj`, published 2025-04-24, documents malformed chunked-encoding acceptance in h11 through 0.15.0 and the 0.16.0 fix. It is used only to demonstrate that sans-I/O organization is not a logical-correctness proof.

Basis: **source/documentation + first-party security advisory**.

### Effect systems and handlers

Gordon D. Plotkin and Matija Pretnar, *Handlers of Algebraic Effects*, ESOP 2009, DOI `10.1007/978-3-642-00590-9_7`. The paper treats handlers as interpretations for algebraic effects including nondeterminism, interactive I/O, concurrency, state, and time.

Daan Leijen, *Koka: Programming with Row Polymorphic Effect Types*, EPTCS 153 (2014), DOI `10.4204/EPTCS.153.8`. The paper presents row-polymorphic effect inference in which potential side effects appear in types and proves semantic properties tied to the effect discipline.

Andrej Bauer and Matija Pretnar, *An Effect System for Algebraic Effects and Handlers*, Logical Methods in Computer Science 10(4), 2014, DOI `10.2168/LMCS-10(4:9)2014`, was consulted as corroborating formal context for language-level effect safety; no stronger foreign-process conclusion is attributed to it.

Basis: **peer-reviewed literature**.

### Repeatable subprocess actions

Repository `bazelbuild/remote-apis`, revision `adbf4a27c86fbea4a37637a6cbcacef372406fe7` (2026-09-22):

- `build/bazel/remote/execution/v2/remote_execution.proto`, blob `8f83bc9351182a305e5f13ff8471dc28740640e5`, especially `Action`, `Command`, `Command.EnvironmentVariable`, and the comments describing reproducibility, cache identity, timeout, PATH lookup, worker environment, input-root digest, working directory, and output paths;
- `build/bazel/remote/execution/v2/platform.md`, blob `56a11af92e96401fe41d5d945f2c33a7637461d4`, for standardized `OSFamily` and `ISA` platform properties.

Basis: **normative protocol/source**.

### Anneal authority and existing execution evidence

Repository `google/zerocopy`, revision `cc135f46155b72e4b51188525c2974a3b84acf92`, `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`. Relevant durable constraints are meaningful identity/scope, justified Rust semantics, complete accounting for behavior relevant to the promise, explicit/shrinkable trust, and preference for minimally sufficient mechanisms.

Current reference corpus at the research boundary was inspected for overlapping evidence. In particular:

- `reports/anneal-3730-rust-input-snapshot-2026-09-29/REPORT.md`, blob `8d1ca9ff320e216be72abbca267c4372fcb8d0e1`, for the Cargo input-closure counterexamples and its explicit list of still-unclosed input classes;
- `reports/anneal-3730-fault-model-2026-09-29/REPORT.md`, blob `b11f3bab8082ebe52ca47a2d10eb9f44d6f0832c`, for bounded cancellation/ownership/publication counterexamples; and
- `reports/anneal-3730-architecture-contracts-2026-09-29/REPORT.md`, blob `d532b9fe321f547efe355a9044b707a06727ed65`, for the existing distinction among semantic request identity, process policy, stage result, publication, and proof acceptance. This J030 report uses that prior table as evidence and extends it into a literature-backed effect-placement judgment rather than treating the earlier synthesis as sufficient J030 coverage.

Basis: **source + previously preserved execution/source synthesis**.

No new Charon, Aeneas, Lean, Cargo, or remote-execution process was run for this report.

## Revalidation

For the architectural sources, revalidation is cheap: confirm that the cited Cockburn/Bernhardt pages still represent the same historical material; compare later sans-I/O guidance against `brettcannon/sans-io@b4679927d555cb27d9960ae203c0ecd0d8209771`; and revisit effect-system literature only if Anneal adopts a concrete effect language or runtime whose guarantees differ materially from the representative papers here.

For repeatable subprocess execution, diff `remote_execution.proto` from `adbf4a27c86fbea4a37637a6cbcacef372406fe7`, focusing on `Action`, `Command`, environment defaults, PATH resolution, platform properties, timeout, and caching. A protocol change in those areas can change the comparison even if Anneal itself is unchanged.

For Anneal, re-run the architectural judgment whenever one of these changes occurs:

- Anneal adopts a concrete source/environment manifest or sandbox contract;
- Charon, Aeneas, or Lean gains an upstream API that lets the host supply or attest previously ambient inputs;
- persistent workers become authoritative for acceptance rather than an optimization behind a fresh validation path;
- plugins/native extensions become part of the supported ordinary path; or
- a new execution report establishes that an assumed ambient input is irrelevant or exposes another hidden dependency.

The cheapest discriminating probe for a proposed cache/purity boundary is a **fixed-declared-request perturbation test**: hold the claimed request identity constant while varying one ambient input class (filesystem dependency, environment variable, search path, clock, plugin, worker generation, or process-local state). If accepted output or claim changes, that class is not outside the semantic/effect closure. If it does not change in one probe, record only that bounded result; do not infer global irrelevance without a source or semantic argument.