# Functional cores and explicit effect boundaries for a verification engine

## Summary

Functional-core/imperative-shell, ports-and-adapters, effect systems, and sans-I/O all separate computation from interaction, but they separate different things. Functional core/imperative shell moves decisions toward value-oriented code and leaves real-world mutation in a shell. Ports and adapters make the inside/outside dependency boundary explicit and let several technologies implement one purposeful conversation. Effect systems make side effects part of the program description, while effect handlers separate an effectful operation from the code that interprets it. Sans-I/O libraries keep protocol state and rules in a reusable in-memory component while callers perform transport I/O.

None of these approaches makes an opaque compiler or prover subprocess a pure mathematical function. Anneal can treat such a tool *as if* it were referentially transparent only after it either controls, captures, or explicitly trusts every input and effect that can change the reported promise. Existing Anneal-adjacent evidence already shows why: unchanged principal Rust source can compile differently when other inputs change; cancellation can leave partial output; loaded native plugins can outlive changes to the pathname that selected them; and task completion does not itself authorize publication as the current result.

The useful transfer is therefore a hybrid boundary, not ideological purity. Keep subject selection, job planning, invalidation decisions, provenance comparison, result classification, and publication eligibility as value-oriented state transitions where practical. Put filesystem/environment preparation, external tool execution, plugin loading, cancellation, and publication behind a small set of explicit host operations. Treat clocks as two different concerns: semantic time must be injected, captured, or trusted if it affects the verified behavior, while scheduler deadlines and leases may remain operational state and must not masquerade as semantic identity. Treat cancellation as lifecycle control plus cleanup and generation fencing, not as rollback. Treat publication as its own fenced effect.

For opaque tools, the minimum useful effect vocabulary should be semantic rather than syscall-complete. A single `invoke external computation` operation can hide thousands of syscalls if its request fixes the relevant tool, subject, environment, input snapshot, output scope, and generation, and its result records the outcome, artifacts, diagnostics, cleanup state, and residual trust. The evidence does not establish the exact Anneal API or prove that this vocabulary is complete. It does establish that pretending a subprocess is `Input -> Output` while leaving ambient filesystem, environment, time, plugins, cancellation, or publication authority unnamed would be stronger than the evidence supports.

## Applicability

This report addresses issue #3732 J030. It is an architectural and literature study, with targeted current-source inspection of `python-hyper/h11` and comparison against already-published Anneal reference experiments. It does not benchmark a proposed Anneal implementation and does not adopt an architecture for Anneal.

The historical architecture sources play different evidentiary roles. Gary Bernhardt's 2012 *Boundaries* talk and *Functional Core, Imperative Shell* screencast are practitioner accounts of a code-organization technique. Alistair Cockburn's 2005 hexagonal-architecture report is a design pattern for isolating application logic from external devices. Lucassen and Gifford's 1988 effect system and Plotkin and Pretnar's 2009 algebraic effect handlers are programming-languages mechanisms with formal semantics. Cory Benfield's 2015 Hyper account and current h11 source document a concrete sans-I/O lineage. The report compares these approaches; it does not claim that they are interchangeable or that one historically caused another.

The h11 source observation applies to `python-hyper/h11@62c5068c971579d61fa1b55373390e12f25fd856`. Its README calls h11 a bring-your-own-I/O library: callers provide received bytes and obtain protocol events, then provide outbound events and obtain bytes to write. Its `Connection` object nevertheless stores protocol state, request information, receive buffers, and flow-control state. That distinction matters here: *sans I/O* means that transport I/O is outside the component, not that the component has no mutable state.

The Anneal design context applies to `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, especially `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`. The current contract requires precise success scope, justified Rust semantics, explicit trust, and preservation of any effect relevant to the promised property; it deliberately leaves concrete mechanisms undecided. The Anneal implications below are derived constraints and design judgments under that contract, not project policy.

Existing execution reports are used only within their stated bounds. In particular, the Rust input-snapshot report is a small Cargo/rustc fixture, the cancellation report is a set of component CLI trials plus a synthetic fence, the Lake prepared-environment report is a tiny Lean/Lake fixture, and the native-plugin mapping report is one Lean process-lifecycle experiment. They are evidence against stronger assumptions about hidden state; they are not end-to-end Anneal results.

## Findings

### The four approaches expose different boundaries

The approaches in J030 agree that interaction should not leak everywhere, but their units of abstraction differ.

| Approach | What it makes explicit | Main benefit for Anneal | What it does not establish by itself | Characteristic cost |
| --- | --- | --- | --- | --- |
| Functional core / imperative shell | A placement boundary between value-oriented decisions and imperative interaction | Pure or immutable planning/classification code is easy to replay, unit-test, and reason about | That the shell is small, hermetic, deterministic, or semantically complete | External concerns can accumulate in a large shell; forcing everything into the core can create artificial encodings |
| Ports and adapters | Purpose-defined application ports and technology-specific adapters | Dependency direction, replaceable test/real adapters, explicit host-facing interfaces | That two adapters have the same failure, freshness, cancellation, or trust semantics | An interface can hide meaningful differences; port granularity is a judgment call |
| Effect systems / handlers | Which computations may perform effects, and/or the operations through which effects are interpreted | Auditability and composition of state, I/O, time, nondeterminism, cancellation-like operations | What an uninstrumented external process actually read, wrote, loaded, or retained | Type/API complexity; foreign boundaries still need runtime controls or assumptions |
| Sans-I/O | Protocol/state-machine computation separated from transport I/O | Reusable deterministic protocol logic across synchronous/asynchronous runtimes | Statelessness, whole-application completeness, or semantic closure of arbitrary tools | Caller owns driving, timers, lifecycle, and transport integration |

This comparison is **derived** from the sources below. It is not a ranking. Anneal can use more than one pattern at once: a functional planner may call ports whose operations are represented as effects; one adapter may itself be a sans-I/O state machine.

### Functional core / imperative shell is a placement rule, not a hermeticity proof

Bernhardt's 2012 material places application decisions in a functional core and real-world interaction in an imperative shell. His published screencast description is explicit about the division: the example core manages data and rendering while the shell manipulates standard input/output, a database, and the network. The stated benefits are local reasoning and isolated testing of the functional pieces; the shell has relatively little branching because the core makes the decisions.

The important property is **where choices happen**. A value-oriented core can take an immutable request plus known facts and return a plan or classification without reading ambient process state. That shape fits Anneal well for operations such as selecting a verification subject, comparing captured identities, computing which stages are invalid, deciding whether a result is stale, or deciding whether a completed result is *eligible* for publication.

The pattern does not prove that the shell has no hidden state. A shell that runs `cargo`, `charon`, Aeneas, Lake, or Lean can still depend on environment variables, current directory, inherited file descriptors, filesystem contents, loaded plugins, process-global caches, clocks, child processes, and prior requests. Moving those calls to the edge improves code organization but does not turn their behavior into a function of the Rust values named by the caller.

A second limitation follows from scale. The useful design is not “one giant pure core plus one miscellaneous shell.” The more unrelated authority the shell accumulates, the less the boundary says. Anneal should therefore prefer several narrow effect operations with stated semantics over a generic `run closure with host access` escape hatch. This is a **derived** Anneal judgment from the architecture pattern and Anneal's existing fail-closed contract, not a claim Bernhardt made about verification engines.

Basis: Bernhardt 2012 **historical practitioner account**; Anneal transfer is **derived**.

### Ports and adapters make dependency direction explicit but cannot manufacture substitutability

Cockburn's 2005 report draws an application boundary and gives external technologies adapters to purpose-defined ports. The motivating goal is that the same application can run against a real database, a mock database, a GUI, a batch driver, or another program without making the application's business rules depend on those technologies. The port represents the conversation's purpose; the adapter translates that conversation to a device or technology.

For Anneal, this is a useful ownership rule. The engine can define ports such as “resolve a captured compilation subject,” “prepare a verification environment,” “execute a verifier stage,” or “publish a fenced result” without making core scheduling code depend directly on process APIs, filesystem APIs, or a particular Lean client library.

The hazard is **fake substitutability**. Two adapters can implement the same Rust trait or message schema while differing materially in semantics. A one-shot subprocess adapter may start from a fresh address space; an in-process library adapter may retain globals; a long-lived server may preserve caches and native plugins; a remote adapter may add retries and transport failure; a test fake may never fork children or write partial files. The common port does not prove that these adapters share reset, cancellation, diagnostic, freshness, or trust behavior.

Cockburn's pattern also leaves port granularity to design judgment. That is an advantage here: Anneal does not need one port per syscall, nor one universal “backend” port that erases all distinctions. The stable port should express a semantic capability whose contract can actually be shared. Implementation-specific lifecycle facts can remain in a narrower adapter contract or result envelope rather than being falsely normalized away.

Basis: Cockburn 2005 **historical architecture pattern**; adapter-semantic warning is **derived** and corroborated by current Anneal process/plugin evidence.

### Effect systems turn effects into part of the computation's description

Lucassen and Gifford's 1988 system separates the value type of an expression from an *effect* describing side effects and a *region* describing where they may occur. Its stated soundness property makes the statically computed effects a conservative approximation of actual effects. The work also allows effects that are unobservable outside a region to be masked. This is a formal example of a principle Anneal needs even if Anneal never adopts an effect-typed Rust API: a computation's result type alone does not tell a caller enough about the state it may inspect or change.

Plotkin and Pretnar's 2009 algebraic handlers make a complementary separation. Their examples include nondeterminism, interactive I/O, concurrency, state, and time. An effectful computation invokes operations; a handler gives those operations an interpretation. The reusable design lesson is that the core can name *what interaction it requires* without hard-coding *how the host performs it*.

For internal Anneal code, an effect-aware API could make operations such as filesystem access, environment lookup, time, process launch, plugin loading, cancellation, and publication visible at call sites or in capability objects. But a static effect annotation on the wrapper cannot attest what an opaque subprocess actually did. If `invoke_tool` is typed as one effect, its implementation still needs runtime containment, input capture, output validation, or an explicit trust premise for the external behavior hidden behind that operation.

This yields a useful two-level rule. Use static types/capabilities where Anneal controls the implementation and the type can constrain authority. At foreign or opaque boundaries, use a coarse semantic effect whose *runtime contract* names the inputs, outputs, allowed ambient dependencies, lifecycle behavior, and trust assumptions. Do not confuse “all host interaction goes through one typed function” with “the external program is pure.”

Basis: Lucassen/Gifford 1988 and Plotkin/Pretnar 2009 **formal literature**; Anneal split is **derived**.

### Sans-I/O externalizes transport; it does not eliminate state

Benfield's 2015 account explains the historical motivation for Hyper-h2: a monolithic HTTP/2 implementation tied protocol work to one I/O model, so each synchronous, threaded, event-driven, or asynchronous stack risked reimplementing the same framing and state-machine logic. Hyper-h2 moved protocol machinery into an in-memory core; callers performed socket I/O. Benfield also stressed that the core was not a complete client or server. It enforced protocol rules and serialized/deserialized data while the application decided what requests and responses meant.

Current h11 preserves the same idea. Its README says h11 contains no I/O code and describes a call pattern in which the host supplies network bytes, receives protocol events, supplies outbound events, and receives bytes to transmit. Yet `h11.Connection` stores a connection state machine, receive buffer, request method, peer HTTP version, and flow-control state. The library is sans-I/O but intentionally stateful.

That distinction transfers directly to Anneal. A sans-I/O-style API is useful for components whose environment can naturally be reduced to explicit events and state: an LSP/MCP framing layer, a job-state machine, a freshness classifier, or a publication fence. It is less naturally a recipe for an existing compiler or proof tool whose semantics include filesystem discovery, dynamic loading, process globals, build scripts, or other ambient behavior.

The design goal should therefore be **explicit driving**, not “everything must be a pure function.” A stateful engine can still be auditable if the caller owns its lifecycle, inputs arrive through explicit operations, the retained state has a named generation/session identity, and the engine cannot silently consult a second source of truth that is absent from the request contract.

Basis: Benfield 2015 **historical design account** + `python-hyper/h11@62c5068c...` **current documentation/source**; Anneal transfer is **derived**.

### A subprocess is an external effect relation unless its closure is enforced

A tempting abstraction is:

```text
verification_output = verify(source_snapshot)
```

That abstraction is valid only if `source_snapshot` closes over every input that can change the meaning of `verification_output`, or if omitted inputs are explicit trusted premises. Existing reference evidence gives direct counterexamples to a source-only interpretation. In `anneal-3730-rust-input-snapshot-2026-09-29`, the same principal `main.rs` bytes produced different output when an included file, selected Cargo feature, or manifest default changed. A macro-visible documentation edit also changed generated code. The report does not identify the complete production input closure, but it is enough to rule out “principal source bytes are the function argument” as a general contract.

A better abstraction resembles the external-call models already surveyed in `ffi-specification-trust-patterns-2019-2026`: an external computation relates an explicit pre-state/request to an outcome, outputs, observable events, and a post-state, under named environment assumptions. Anneal does not need to model every syscall to use this structure. It can choose a coarser boundary such as:

```text
InvokeTool {
    tool_identity,
    subject_identity,
    captured_inputs,
    cwd_and_environment,
    prepared_environment_identity,
    plugin_or_extension_identity,
    output_scope,
    generation,
    lifecycle_policy,
} -> {
    status,
    output_manifest,
    diagnostics,
    evidence,
    cleanup_state,
    residual_assumptions,
}
```

The field list is illustrative, not a proposed wire format. Its purpose is to show what a value-level call has to preserve before the caller may reason as if a tool invocation were repeatable. Some fields can collapse into one authenticated snapshot or prepared-environment identity. Some can be denied by sandbox policy instead of recorded. Some can remain trusted if Anneal's result says so. What cannot happen under Anneal's design contract is for a promise-relevant dependency to disappear merely because the adapter API returns one `Output` value.

Basis: existing Rust input fixture and FFI reference **execution/formal synthesis**; API shape is **derived**.

### The minimum effect interface is semantic, not a syscall log

Anneal needs enough effect accounting to justify a verification result, but a syscall-by-syscall event algebra would usually be the wrong level. The minimal useful categories are those that can change the result's meaning or currentness.

| Effect class | Why Anneal must account for it | Minimally useful control/evidence | What may stay hidden |
| --- | --- | --- | --- |
| Input resolution and reads | Source, manifests, includes, dependencies, generated inputs, and proof artifacts can alter the subject | Captured subject/input closure or an environment identity whose construction is controlled and auditable | Individual `open`/`read` calls when the enclosing immutable snapshot is sufficient |
| Environment and configuration | `cwd`, selected toolchain, flags, environment variables, search/load paths, locale or configuration may affect behavior | Constructed environment with an allowlist or captured identity; omitted ambient variables denied or trusted explicitly | Host details proven irrelevant to the operation |
| External computation | Compiler/prover subprocesses can fail, diverge, retain state, fork children, or emit partial output | Exact executable/tool identity, args, controlled inputs/env, private output scope, explicit outcome and output manifest | Internal syscalls and implementation steps when the external contract is adequate |
| Plugins and native extensions | Loaded code can change semantics and may persist in a process after the selecting path changes | Exact artifact identity plus load/session generation, or expendable process isolation; ABI/config/trust recorded | Internal plugin implementation when deliberately trusted |
| Time and nondeterminism | Semantic clock/randomness can change program/tool behavior; deadlines can change which work completes | Inject/capture/forbid semantic time/randomness; separately record operational timeout policy | Wall-clock scheduler timestamps that do not affect the claimed semantics |
| Cancellation and process lifecycle | A signal may race with descendants or output writes; cancelled work may finish late | Request ownership, process/session identity, cleanup/termination outcome, generation fence, retry policy | Exact signal mechanics when the lifecycle contract has been established |
| Publication/currentness | Correct stale work can still be wrong to present as current | Compare-and-swap or equivalent generation/source/session fence; immutable complete output identity | Storage implementation details that cannot violate atomic selection |

This table is a **derived candidate interface**, not a completeness theorem. Concurrency, network access, devices, credentials, and FFI may require additional categories when Anneal supports promises that depend on them. Conversely, a prepared environment may combine several rows into one capability if its construction proves the required closure.

### Filesystem and environment effects should be concentrated at preparation and result boundaries

The cleanest way to simplify downstream calls is to spend complexity once at environment preparation. `anneal-3730-lake-prepared-contract-2026-09-29` shows a bounded example: after a tiny Lean/Lake environment was fully prepared with a complete manifest, selected no-build and batch operations could run after relocation against a frozen producer under an isolated home and denied network. The same report also shows the limit: a source-only non-writable consumer failed when Lake needed to create `.lake`, and cache/artifact acceptance was operation-specific.

For Anneal, the general pattern is to prepare an immutable or tightly controlled input tree, assign it a durable identity, and give a tool a private scratch/output area. If the tool reads only the prepared inputs and writes only private output, the core need not model each filesystem operation. At the boundary, Anneal validates and admits a complete output manifest by content identity. This is closer to a coarse effect handler than to pretending the filesystem does not exist.

The remaining burden is proving the boundary. A sandbox policy, read-only tree, traced manifest, or upstream-supported explicit input API can provide different strengths of evidence. Merely passing an absolute path is not evidence that the process did not also inspect `$HOME`, a sibling manifest, a build-script result, a plugin search path, or another file reachable through configuration.

Basis: Lake prepared-environment **execution** + Rust input-snapshot **execution**; architectural transfer is **derived**.

### Clocks have semantic and operational roles that should not share one identity field

“Clock” hides two different effects.

A **semantic clock** is data that can affect the behavior being verified or the tool's semantic result: a program reads current time, a build script emits time-dependent data, a generated input embeds a timestamp, or a verifier intentionally consults time. Anneal must inject, capture, forbid, or trust that value just like any other input. Re-running the same source at a later wall-clock time is not the same mathematical computation if the clock can affect the result.

An **operational clock** drives scheduling: timeout after 30 seconds, expire a worker lease, debounce edits, or decide when to retry. Those times need not become part of the verified program's semantic identity if they cannot alter which semantic result is accepted. They do affect liveness and lifecycle. A timeout must therefore produce an explicit incomplete/failed status, not a weaker success, and a late completion must still pass the current generation/publication fence.

This distinction avoids two opposite mistakes. Anneal should not salt every cache key with wall-clock time merely because its scheduler uses deadlines. It should also not call a time-sensitive external computation pure because the clock was read outside the wrapper's type signature.

Basis: effect-handler literature includes **time** as an effect; Anneal timing split is **derived** from the design contract and publication/cancellation evidence.

### Plugins turn path identity into process-state identity

The native-plugin mapping report demonstrates a concrete hidden-state problem. A stable plugin pathname was redirected from v1 to v2. The existing Lean watchdog still mapped v1 while a newly opened file worker mapped v2. After a forced restart, a fresh watchdog and worker mapped v1 again. The report does not prove all plugin-loading behavior, but it is enough to reject “current pathname -> current plugin semantics” as a general identity rule for a live process.

For an in-process or persistent-worker Anneal backend, plugin identity therefore has at least two layers: the bytes/configuration the host *intended* to load and the code already resident in the worker or descendants. A safe adapter can handle this by using expendable processes, by giving workers an immutable plugin/environment generation and routing only matching requests to them, or by establishing an upstream reset/unload contract with evidence. A Rust type that says `PluginPath` cannot make old mapped code disappear.

This is an instance of the broader rule that facts another process can invalidate or retain require runtime validation or lifecycle protocol. It also shows why backend substitutability has limits: an in-process plugin backend and a fresh subprocess backend may implement the same logical operation while requiring different freshness evidence.

Basis: native-plugin mapping report **execution**; Anneal response is **derived**.

### Cancellation is an effect on ownership and lifecycle, not transactional rollback

The cross-tool cancellation report sent stop/kill signals to actual pinned Cargo, Charon, Aeneas, Lake, and Lean CLI process groups. Delayed Cargo and Lake trials left partial files before the kill; same-directory retries then succeeded. The report explicitly does not prove cleanup for daemonized descendants or all tool phases. It does prove enough to reject a transactional reading of cancellation: “cancelled” does not mean “the external world is unchanged.”

Anneal therefore needs at least three distinct facts:

1. **request ownership** — whether any consumer still wants the work;
2. **execution lifecycle** — whether the process/worker and relevant descendants have actually stopped or been abandoned; and
3. **publication authority** — whether any result from that generation may become current.

A cancellation request can remove ownership without immediately stopping a shared job. A killed job can leave private partial files that should be discarded or cleaned. A process can complete successfully after its request became stale. The `anneal-3730-fault-model-2026-09-29` bounded model independently finds counterexamples when ownership, status, generation, worker, RPC, completeness, or current-input fences are removed. The model is not a production proof, but it makes the separations concrete.

Treating cancellation as an explicit effect means the core can say “consumer X no longer owns generation G” and the shell can decide how to stop or reuse execution resources. Publication still checks G against current authority after completion. This is stronger than adding `Cancelled` to a subprocess return enum while allowing the subprocess to write to a shared canonical destination.

Basis: cross-tool cancellation **execution** + fault model **execution/model**; architecture is **derived**.

### Publication is a separate effect even when computation is pure

Suppose a verification computation is perfectly deterministic over a fully captured snapshot. It can still finish after a newer edit, after its worker has been replaced, or after its last consumer has cancelled. The output remains a valid result *for its captured snapshot* but may not be valid to select as *current*.

This distinction means publication does not belong inside the fiction that `verify(snapshot)` is one atomic pure call. The compute result should carry provenance. A separate publication operation checks current source/environment/generation authority and atomically selects the complete immutable result. Existing Anneal finite models and stale-result probes motivate this fence independently of tool semantics.

The split also improves crash handling. A worker may write private or content-addressed artifacts without holding authority to mutate the current pointer. Publication can be retried or reconciled as a smaller native effect. This report does not choose a particular storage system or prove crash durability; it identifies publication authority as a distinct semantic responsibility.

Basis: existing fault/publication models **execution/model**; Anneal recommendation is **derived**.

### Serious alternatives trade different risks

**Make the whole engine a functional core.** This maximizes replayability: the core consumes a complete world value and produces a complete result value. The difficulty is constructing that world. If the “world” becomes an opaque handle that lets a shell answer arbitrary filesystem/process/time queries, the design has only moved hidden state behind one argument. If it snapshots every potentially relevant byte eagerly, cost and invalidation can become excessive. This is attractive for the orchestration state machine, less obviously for arbitrary compiler internals.

**Use ports and adapters without an explicit effect model.** This is operationally cheap and idiomatic. It may be enough when each port has a precise semantic contract and all adapters are validated against it. It fails when a shared trait merely groups commands whose failure, freshness, or retained-state semantics differ. Anneal should not infer equivalence from a common interface name.

**Encode host effects in Rust types or algebraic handlers.** This can make internal authority reviewable and can enable deterministic tests. Its cost is API/type complexity, especially if every incidental operation becomes a type-level distinction. It also stops at opaque boundaries unless the wrapper contains or validates the external effect. The strongest use is to make *Anneal-owned authority* explicit, not to claim static knowledge of arbitrary child-process behavior.

**Run every stage in a fresh hermetic subprocess and call that a function.** This is a strong baseline if the process receives a closed immutable input set, has no unmodeled ambient reads/network, writes only to a private area, and returns a validated manifest. Fresh processes also reset many globals and loaded plugins. Costs include startup, memory, serialization, and loss of incremental state. Hermeticity itself must be established; a fresh process with inherited environment and broad filesystem access is not a closed function.

**Keep persistent in-process or server backends.** This can retain expensive compiler/prover state and improve latency. It turns caches, plugins, current document/import state, and reset behavior into explicit session semantics. The backend needs a session/environment generation and a policy for reconstruction after changes. Persistent state is not disqualifying; unnamed persistent state is.

**Use sans-I/O state machines wherever possible.** This is strong for protocol, scheduling, and publication machinery because the caller can drive explicit events and own the external runtime. It can become counterproductive if Anneal reimplements mature compiler/build behavior merely to achieve a stylistic purity goal. The right question is whether the component exposes a natural state-machine boundary, not whether “sans I/O” is architecturally fashionable.

These alternatives are not mutually exclusive. A practical design can begin with fresh private subprocesses for opaque stages, preserve a value-oriented scheduler/publication core, and later introduce a persistent backend only after its reset/identity/resource advantages are measured and its additional state is made explicit.

### Conditional judgment for Anneal

The evidence favors the following default until a more specific architecture earns stronger assumptions:

1. **Keep the core's authority decisions explicit and replayable.** Subject identity, captured generation, invalidation, job ownership, result provenance, and publication eligibility should be represented as values and state transitions rather than inferred from ambient filesystem/process state.
2. **Give the core a small semantic effect interface.** The host should expose preparation/input capture, external computation, plugin/extension execution where needed, cancellation/lifecycle control, and publication as distinct operations. Time/randomness should be explicit only where they can affect semantic results; scheduler time remains operational state.
3. **Use coarse external effects for opaque tools.** Do not model every syscall. Constrain or capture the environment around a subprocess, give it private output, and return a complete outcome/evidence envelope. Anything result-relevant outside that contract stays an explicit trust premise or makes the operation unsupported.
4. **Default opaque stateful backends to process isolation when reset matters.** A fresh process is not magically hermetic, but it gives a comprehensible lifetime boundary for globals, plugins, crashes, and descendants. Move a backend in-process or keep it persistent only when the state/reset contract and measured benefit justify the additional complexity.
5. **Never let cancellation imply rollback or completion imply currentness.** Cleanup/retry and publication fencing remain separate obligations.
6. **Do not turn this interface into a universal effect IR.** Anneal's design contract prefers minimally sufficient machinery. Add effect structure when a promised property needs it, and keep richer semantics open for later rather than baking every possible external behavior into today's scheduler API.

The central criterion is: **Anneal may hide an effect behind an abstraction only when the abstraction preserves every aspect of that effect that can change the claimed verification result, and when any remaining dependency is denied or visible as trust.** That criterion is stronger than “the code is in the shell” and weaker than “model the whole operating system.”

Basis: **derived synthesis** from the historical/formal sources, current h11 source, current Anneal design contract, and bounded Anneal reference evidence.

## Boundaries

- No new Anneal, Cargo, Charon, Aeneas, Lake, Lean, h11, Hyper-h2, effect-system, or operating-system execution was performed for this report. The current h11 repository was inspected as source/documentation; historical architecture sources were read as design accounts.
- The report does not prove that the seven effect classes in its candidate table are complete. Network access, devices, credentials, concurrency, signals, FFI callbacks, randomness, locale, kernel state, or future proof mechanisms may need separate representation when a promise depends on them.
- The report does not propose a concrete Rust trait hierarchy, algebraic-effect implementation, capability type system, sandbox technology, syscall tracer, remote-execution protocol, or serialized result schema.
- Bernhardt's and Cockburn's material are engineering patterns, not formal soundness results. They support placement and dependency arguments, not claims that an implementation is hermetic or deterministic.
- Lucassen/Gifford and Plotkin/Pretnar provide formal effect-system/handler models, but Anneal's operating-system and compiler effects are not formalized in those systems here. The report transfers structural distinctions, not their exact calculi.
- h11's state machine is an HTTP protocol implementation. Its success as a sans-I/O component does not establish that compiler/prover internals can or should expose the same architecture.
- Existing Anneal reference reports provide bounded component evidence. The Rust input fixture does not enumerate production input closure; the cancellation fixture does not prove all descendant cleanup; the Lake fixture is tiny; the plugin mapping report is platform/tool-specific; the finite fault model is bounded and synthetic.
- Process isolation is not a complete sandbox, does not prove deterministic execution, and does not undo filesystem or external effects after cancellation.
- An immutable input snapshot can support computation reuse, but it does not by itself authorize a stale writer or stale result to mutate current state. Content identity and causal/currentness authority remain distinct.
- The Anneal implications are conditional derived analysis. `anneal/DESIGN.md` deliberately leaves implementation boundaries and mechanisms undecided.

## Evidence

**Functional core / imperative shell.** Gary Bernhardt, *Boundaries*, SCNA 2012: `https://www.destroyallsoftware.com/talks/boundaries`. The current page describes simple values as component/subsystem boundaries and explicitly points to the Functional Core, Imperative Shell material. Gary Bernhardt, *Functional Core, Imperative Shell*, published 2012-07-12: `https://www.destroyallsoftware.com/screencasts/catalog/functional-core-imperative-shell`. The published description identifies a functional application core surrounded by imperative stdin/stdout/database/network code and states the testing/control-flow rationale. These are **historical practitioner accounts**.

**Ports and adapters.** Alistair Cockburn, *Hexagonal architecture the original 2005 article*, HaT Technical Report 2005.02, dated 2005-09-04: `https://alistair.cockburn.us/hexagonal-architecture`. It states the intent of running/testing the application independently of UI/database, defines purpose-oriented ports with technology-specific adapters, and explicitly treats the number of ports as a design choice. This is a **historical architecture-pattern source**.

**Effect systems.** John M. Lucassen and David K. Gifford, *Polymorphic effect systems*, POPL 1988, DOI `10.1145/73560.73564`; IBM Research record: `https://research.ibm.com/publications/polymorphic-effect-systems`. The abstract distinguishes value types, effects, and regions and states conservative effect soundness. Gordon Plotkin and Matija Pretnar, *Handlers of Algebraic Effects*, ESOP 2009, DOI `10.1007/978-3-642-00590-9_7`; University of Edinburgh record: `https://www.research.ed.ac.uk/en/publications/handlers-of-algebraic-effects/`. The abstract covers handlers for nondeterminism, interactive I/O, concurrency, state, time, and combinations. These are **formal programming-languages literature**.

**Sans-I/O history.** Cory Benfield, *The New Hyper*, 2015-10-15: `https://lukasa.co.uk/2015/10/The_New_Hyper/`. It explains the move from a monolithic implementation to reusable components and describes Hyper-h2 as an in-memory HTTP/2 core with external socket I/O. This is a **historical practitioner design account**.

**Sans-I/O current source.** `python-hyper/h11@62c5068c971579d61fa1b55373390e12f25fd856`:

- `README.rst`, blob `5f2861600c543733424127ed0baa70e62c647373`: bring-your-own-I/O API and motivation.
- `h11/_connection.py`, blob `e37d82a82a882c072cb938a90eb4486b51cdad99`: `Connection` state machine, buffering, request/peer state, and flow-control state.

This is **current documentation/source**. No h11 behavior was executed.

**Anneal design authority.** `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`:

- `anneal/PRINCIPLES.md`: fail-closed promise, explicit TCB, depth of understanding.
- `anneal/DESIGN.md`: precise verification success, justified Rust semantics, effect-preserving abstraction boundaries, explicit/shrinkable trust, and minimally sufficient mechanisms.

These files are **current project design authority** for the derived Anneal constraints in this report.

**Existing Anneal reference evidence, reread at `refs/heads/reference` head `6b0acaee13124bc17bef31c764693836a93ff25a`:**

- `reports/anneal-3730-rust-input-snapshot-2026-09-29/REPORT.md`, blob `8d1ca9ff320e216be72abbca267c4372fcb8d0e1`: same principal source with different included file/feature/manifest or macro-visible documentation inputs; separate content identity and edit authority.
- `reports/anneal-3730-cross-tool-stage-cancellation-cleanup-2026-09-29/REPORT.md`, blob `14e91986e6a25cc19f83929652613f8efa02ab44`: process-group cancellation, partial stage state, same-directory retry, and a separate synthetic generation fence.
- `reports/anneal-3730-lake-prepared-contract-2026-09-29/REPORT.md`, blob `02adb1a0c60642109951c6ab0b328d8f180c13f1`: bounded prepared/read-only environment behavior and operation-specific artifact acceptance.
- `reports/ffi-specification-trust-patterns-2019-2026/REPORT.md`: external-call behavior, resources, implementation adequacy, and environment trust treated as distinct layers using Rust, CompCert, and CakeML evidence.
- `reports/anneal-3731-i125-i154-native-plugin-mapped-workers-2026-09-30/REPORT.md`, blob `0d504ae7388111b56ac307ee657c1ba6ff746881`: stable plugin path resolving to different bytes while existing/new Lean processes retain different mapped versions.
- `reports/anneal-3730-fault-model-2026-09-29/REPORT.md`, blob `b11f3bab8082ebe52ca47a2d10eb9f44d6f0832c`: bounded publication model separating current input, generation/process identity, ownership/status, completeness, and selection.

Those reports remain authoritative for their exact experiments and limitations. This report uses them as **existing execution/model evidence** and derives a cross-cutting effect-boundary judgment; it does not broaden their direct observations.

## Revalidation

If Anneal adopts an engine/backend interface, revalidate this report by auditing each operation against a concrete effect inventory rather than by checking that the code “looks functional.” For every operation, answer: what external state can it read; what state can it mutate; what retained process/session state can influence later calls; which of those facts can change the promised verification result; and which facts are denied, injected, captured, validated, or explicitly trusted.

For a subprocess backend, use a discriminating fixture rather than only repeatability on one happy path. Hold the principal source constant while varying an allowed environment variable, included/configuration file, working directory/search path, and plugin identity; verify that each promise-relevant change either changes the captured request identity, is blocked by the environment policy, or is listed as trust. Kill the tool during output, verify descendant/process cleanup and private-output disposal, then allow a late result and confirm the publication fence rejects it if its generation is no longer current.

For a persistent or in-process backend, add A→B→A tests across configuration and plugin bytes, process restart, worker reuse, cancellation, and external input replacement. Record the exact session/environment generation in every accepted result. If the backend claims a reset operation, compare it with a fresh-process oracle on the same request set before relying on reset for currentness or trust reduction.

For the value-oriented core, replay saved requests and effect responses without host access. The same captured values should produce the same plan, invalidation, classification, and publication-eligibility decisions. If replay needs ambient time, filesystem, process-global state, or an unrecorded plugin, the claimed core boundary is incomplete.

When the Anneal design or toolchain pin changes, reread `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`, then rerun the narrow existing source/input, cancellation, prepared-environment, and plugin-lifetime probes whose assumptions the new design relies on. Revisit the literature only if Anneal's abstraction problem changes materially; the historical pattern descriptions do not require periodic version refresh.