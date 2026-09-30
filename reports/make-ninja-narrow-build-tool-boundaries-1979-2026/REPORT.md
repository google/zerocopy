# Make and Ninja: narrow execution, displaced policy, and the boundary around a verifier

## Summary

Make and Ninja support the same broad architectural lesson for Anneal only at a high level: a small execution engine can be valuable when it receives an explicit dependency plan and leaves domain policy elsewhere. They reach that point by different routes, and flattening them into one "small build tool" pattern would hide the useful distinction.

The original Make model is a dependency graph plus recipes. Make decides *when* a target needs work and invokes a user-supplied recipe; it does not understand what that recipe means. GNU Make later accumulated a substantial human-authored language—variables, functions, implicit rules, includes, recursion, shell expansion, and many compatibility features—so its narrowness is semantic rather than syntactic. The engine remains largely ignorant of the commands' domain semantics, but configuration, graph construction, policy, and execution can all be interleaved in one Makefile language.

Ninja made a more radical split. Its documented design deliberately removes most policy and build-time decision making from the executor. A generator such as GN or CMake computes a concrete build graph; Ninja consumes that graph quickly. That split was motivated by Chromium's edit-build latency after generated non-recursive Makefiles still took about ten seconds before compilation began. The important historical qualification is that Ninja did not stay a featureless timestamp walker. It added executor-level mechanisms when correctness or resource control required them: command-line change tracking, compiler-discovered dependencies, dependency logs, `restat`, pools, dynamic dependencies, validations, and later GNU jobserver participation. The stable dividing line is therefore not "all decisions outside the executor." It is closer to "project policy outside; execution facts that determine correctness, freshness, or safe scheduling inside or through a narrow protocol."

For Anneal, the defensible conditional judgment is similar. A stable batch verification command can remain the authoritative checked boundary while a richer host or daemon owns discovery, watching, project configuration, interactive feedback, and plan construction. But a narrow verifier may not delegate away the meaning of verification success. Exact source/model/environment/tool identity, trusted assumptions, unsupported behavior, the evidence required for the claimed promise, and the authority to publish a result must either be checked at the narrow boundary or explicitly enter the result's trust basis. An all-in-one daemon is justified when persistent state materially improves interactive latency or enables useful incremental work that a batch path cannot provide economically; even then, a reproducible plan/result boundary is valuable for revalidation and publication.

This is a derived architecture judgment, not adopted Anneal policy. The source histories show mechanisms and tradeoffs; they do not demonstrate that a Make-like, Ninja-like, or daemon-centered split is universally optimal.

## Applicability

This report answers issue #3732 question J042: what Make and Ninja intentionally keep inside or outside the build engine, why those boundaries exist, what complexity is displaced into callers, and how that history bears on the division between Anneal orchestration and a stable batch verifier.

The historical Make subject is Stuart Feldman's 1979 publication describing a system already in use since 1975. Current Make behavior is taken from GNU Make 4.4.1, released 2023-02-26. GNU Make is not treated as identical to 1970s Make: its language and compatibility surface are much richer. The historical source establishes the original problem and dependency/recipe model; the 4.4.1 manual establishes the mature implementation contract discussed here.

Ninja is examined at repository revision `4e4df1e567eb3c1475a51af261cba2bfff60b4be`, whose `doc/manual.asciidoc` blob is `81ecf7d388f899a1481df9f25ec1065710de679d`. Historical intent is cross-checked against Evan Martin's 2011 Chromium note and a 2013-era manual preserved at Chromium Git revision `a9071772ead9522d7ebb21048da08c8ea22cec21`. The current manual is important because it shows which mechanisms survived and which executor responsibilities grew over roughly fifteen years.

Anneal applicability is anchored to `google/zerocopy` revision `cc135f46155b72e4b51188525c2974a3b84acf92`, specifically `anneal/PRINCIPLES.md` blob `d5339a95254eae14ac201139d07d9d36d48a19fb` and `anneal/DESIGN.md` blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`. Those documents constrain result meaning, source-to-model justification, abstraction, user-facing Rust orientation, explicit trust, and minimally sufficient mechanisms, but intentionally do not choose a concrete process or daemon boundary. The Anneal conclusions below are therefore design analysis under those constraints, not a report of an existing implementation.

This report is about architectural responsibility, not build-system performance benchmarking. It does not claim that verification resembles compilation in all relevant respects. In particular, Anneal's successful result has a proof/trust meaning stronger than ordinary "target is up to date" build freshness, so some build-system patterns transfer only after adding explicit identity and evidence requirements.

## Findings

### 1. Make's original core separated dependency knowledge from command semantics

Feldman's 1979 paper describes Make as a response to a practical consistency problem: a program is produced by chains of tools over many pieces, and after edits the required update sequence is easy to get wrong manually. The central mechanism is a set of relationships among files plus commands for restoring consistency. The paper describes Make as having been in use on UNIX since 1975.

GNU Make 4.4.1 retains that recognizable core. A rule names targets, prerequisites, and a recipe. A file target is normally out of date if it is missing or older than a prerequisite, and Make runs the recipe after bringing prerequisites up to date. Crucially, the manual says that Make does not know how recipes work: the author must supply recipes that actually update their targets.

Basis: historical publication + current official documentation.

That division is narrow in one important sense. Make reasons about declared dependency structure and timestamps; it does not infer the semantic inputs and outputs of arbitrary shell commands. If a recipe reads an undeclared configuration file, environment variable, directory listing, network response, compiler plugin, or other ambient state, Make does not automatically turn that influence into a dependency. Correctness therefore depends on the Makefile author exposing enough of the real dependency relation.

Derived implication: a small scheduler can be correct only relative to the dependency model it sees. Smallness does not eliminate hidden inputs; it changes where responsibility for exposing them sits.

### 2. Mature GNU Make is not a policy-austere executor

GNU Make should not be used as evidence that successful build tools must have a tiny input language. Its current manual includes variables and functions, implicit and pattern rules, directory search, conditional behavior, included makefiles, recursive invocation, parallelism controls, automatic dependency generation, shell interaction, and many compatibility features. Built-in implicit rules can choose compilers and commands from conventional variables such as `CC`, `CFLAGS`, and `CPPFLAGS`.

This makes GNU Make materially different from Ninja's declared philosophy. A project can use Make as both a graph executor and a fairly expressive configuration/meta-build language. Many projects also put still more policy into shell commands, generated include files, Autoconf/Automake, or recursive sub-makes.

Basis: GNU Make 4.4.1 manual.

The benefit is locality and incremental adoption: a small project can write one human-readable file without first building a separate plan generator. The cost is that policy construction, dependency declaration, shell execution, and scheduling can be interleaved. That makes it easy for a build description to depend on facts that are hard for the scheduler to observe or to partition the graph in ways that hide dependencies.

The recursive-Make literature illustrates the latter failure mode. Peter Miller's account argues that recursive directory-local builds can present each Make process with an incomplete dependency graph; the resulting problems include overbuilding, underbuilding, unstable ordering, and lost parallelism. This is not evidence that recursion is always wrong, nor is the paper a formal proof about every Makefile. It is useful here because it isolates the architectural point: a correct local executor cannot compensate for dependency structure that an upstream decomposition never reveals to it.

Basis: current documentation + engineering analysis of recursive Make. The recursive-Make account is interpretive/engineering evidence, not a normative GNU Make specification.

### 3. Ninja was created after a generated-Make approach still made the executor too expensive

Evan Martin's 2011 account gives a concrete origin story. Chromium had moved through SCons and then carefully generated non-recursive Makefiles. The generated Make path improved build times substantially, but the build system could still spend roughly ten seconds deciding what to do after a one-file change before starting compilation. Martin attributes part of the cost to Make's feature and compatibility surface, including work that Chromium did not need, and describes building a conceptually Make-like system with very few features; the initial goal was sub-second startup on Chromium's graph.

Ninja's manual preserves this rationale. It says that where other build systems are high-level languages, Ninja aims to be an "assembler." It intentionally lacks the syntax for complex decisions and expects a separate generator to make configuration and policy decisions up front. The current manual explicitly lists hand-written convenience, built-in compiler rules, build-time customization, conditionals, and search paths as non-goals. It describes GN, CMake, and other meta-build systems as the intended partners and says Ninja alone is unlikely to be useful for most projects.

Basis: project-author historical account + exact current repository documentation.

The design is therefore a compiled-plan architecture:

1. A generator interprets the human/project policy and environment and emits a concrete graph.
2. Ninja loads that graph and decides which edges are dirty.
3. Ninja schedules commands and records selected execution metadata.

The split is an optimization as well as a modularity choice. It amortizes expensive project decisions into generation so the repeated edit-build loop can operate on a simpler representation.

### 4. Ninja's narrowness moves complexity; it does not remove it

The current manual is unusually explicit about the transfer. Compiler flags, debug-versus-release choices, output-layout policy, packaging concepts, and similar decisions belong in the generator. The executor becomes fast partly because the generator has already committed to those choices.

This produces at least four costs that a comparison with an all-in-one system must count.

**First, generator correctness becomes part of build correctness.** If the generator omits an edge or computes the wrong command, Ninja can faithfully execute the wrong graph. The execution engine cannot recover policy it was never given.

**Second, there are two evolving interfaces.** The project/configuration language talks to the generator, and the generated manifest talks to Ninja. This can be a feature—the manifest is a debuggable intermediate representation—but it creates versioning and regeneration obligations.

**Third, regeneration itself is stateful work.** Ninja has a `generator` rule attribute and special handling for generator-produced files. The build description is not magically outside the graph; a practical system needs a way to decide when the plan itself is stale and regenerate it.

**Fourth, some dependencies are not knowable during initial graph generation.** Compiler header dependencies and Fortran module relationships are canonical examples. Ninja therefore has constrained runtime mechanisms such as depfiles/dependency logs and `dyndep` rather than insisting that every edge be fixed before execution.

Basis: exact Ninja manual at revision `4e4df1e...`.

The architectural lesson is not "generate everything once." It is "put each kind of decision where it can be represented cheaply and correctly, and define protocols for facts that become known later."

### 5. Ninja's evolution shows which responsibilities resisted displacement

The original philosophy survives in the 2026 manual, but the executor gained features where leaving responsibility entirely to generators or shell recipes would compromise correctness, incrementality, or resource coordination.

Several examples are instructive:

- Ninja records the command used to build an output, so a command-line change can make the output dirty. A pure timestamp DAG that ignored command identity would silently reuse outputs across changed compilation policy.
- `depfile`/`deps` support imports dependencies discovered by the compiler. These dependencies are semantically inputs even though the generator may not know them before compilation.
- `restat` lets Ninja observe that a command ran without changing an output and then prune downstream work. This is executor-observed change information, not project policy.
- `dyndep`, available since Ninja 1.10, lets a build discover additional implicit inputs/outputs before dependent work runs. The protocol is deliberately constrained: a dyndep file may affect only dependent portions of the graph rather than arbitrarily rewiring unrelated up-to-date work.
- `validations`, available since Ninja 1.11, allow checks such as static analysis to be required without making their freshness determine the main artifact's dirty state. This separates "must run" from "produces the value this output depends on."
- pools and GNU Make jobserver integration put resource coordination in the executor. The current manual says Ninja can join a GNU Make 4.4+ jobserver as a client from version 1.13 and, in the current post-1.13 development manual, can act as a server through the documented 1.14 interface. This is inherently runtime coordination across concurrent processes.

Basis: exact current Ninja manual; release notes for v1.13 corroborate the jobserver-client addition.

These additions do not overturn Ninja's generator/executor split. They refine it. The executor accepts mechanisms that are (a) execution-time facts, (b) needed to decide freshness correctly, or (c) needed to schedule safely. It continues to reject broad project-policy evaluation.

This distinction matters more than raw line count. A "small" core can justifiably grow if the added mechanism closes a correctness hole at the core's own boundary. Conversely, moving such a mechanism outward merely to keep the core small can make the total system harder to reason about.

### 6. Make and Ninja embody different answers to where human-facing policy belongs

The comparison can be stated as a responsibility matrix:

| Responsibility | GNU Make tendency | Ninja tendency | Architectural consequence |
| --- | --- | --- | --- |
| Human-authored graph/policy | Often directly in Makefiles | Expected in separate generator | Ninja makes the generated graph an explicit intermediate interface |
| Command semantics | Opaque recipes | Opaque commands | Both require declared/captured inputs for sound freshness |
| Built-in domain conventions | Many implicit rules/conventional variables | Explicit non-goal | Make trades executor complexity for convenience |
| Configuration decisions | Can occur while reading/evaluating Makefiles | Intended before Ninja runs | Ninja removes repeated decision cost from the hot loop |
| Compiler-discovered dependencies | Commonly generated Make fragments / explicit techniques | First-class depfile/deps support | Runtime facts need a protocol somewhere |
| Command identity | User techniques possible | Recorded by Ninja | Executor owns a freshness fact it can observe cheaply |
| Dynamic graph additions | Expressive Make evaluation/recursive techniques | Constrained `dyndep` protocol | Ninja prefers bounded mutation over a general runtime language |
| Parallel resources | `-j` and GNU jobserver | pools plus jobserver interoperability | Cross-process resources are runtime state, not static project policy |

Basis: GNU Make 4.4.1 manual + Ninja manual at exact revision; table is derived synthesis.

Neither side is a universal optimum. Make's integrated language is attractive when the project is small enough that an extra generator would cost more in complexity than it saves, or when users value hand-written build logic. Ninja's split is attractive when the project model is already generated and repeated executor latency matters enough to justify a compiled representation.

### 7. The strongest argument for a narrow Anneal batch boundary is reproducible authority, not implementation smallness

Anneal's current design contract gives verification success a precise conditional meaning. A successful result must identify the program or behavior to which it applies, the promises established, and the trusted code and assumptions on which those promises depend. Missing evidence or unsupported semantics cannot silently acquire the meaning of success.

That requirement changes the analogy with build systems. A build executor can often assume its manifest is the desired plan. Anneal can also accept a prepared plan, but if the plan determines what source was verified, which obligations were generated, which tool/model versions were used, or which assumptions were trusted, then that plan is part of the semantic basis of the result. The boundary cannot make those facts disappear.

Basis: Anneal `PRINCIPLES.md` and `DESIGN.md` at `cc135f...` + derived comparison.

A useful narrow batch interface would therefore receive or reconstruct a *verification plan* with enough identity to make its result meaningful. At minimum, depending on the eventual design, that likely includes:

- the exact source snapshot or content identities in scope;
- selected configuration/target/model/toolchain identities that can change semantics;
- the promises/properties being checked;
- explicit assumptions and trusted components relevant to the result;
- declared inputs or a conservative capture of ambient inputs used by opaque tools;
- output/result identity sufficient to prevent a stale result from being published for a different snapshot.

This list is a derived requirement class, not a proposed final serialization. The design contract explicitly leaves the result schema and division among Rust, Charon, Aeneas, Lean, and Anneal undecided.

The critical point is that moving preparation into a daemon does not remove it from the trust/evidence story. If the batch runner blindly trusts a daemon-generated plan, the plan generator's correctness is part of the TCB for the resulting claim unless some later check makes its mistakes detectable.

### 8. Anneal can separate user/project policy from verification-success semantics

A Ninja-like boundary is most plausible if the richer host owns decisions whose mistakes should produce a rejected or differently scoped plan rather than silently strengthen a successful theorem claim.

Good candidates for the host/orchestration side include:

- discovering workspaces and watching files;
- translating user-facing project configuration into an explicit plan;
- selecting which units to attempt next;
- maintaining interactive caches and low-latency advisory state;
- presenting progress and diagnostics;
- choosing resource budgets and scheduling independent verification jobs;
- invoking a stable batch verifier with explicit inputs;
- retaining multiple snapshots for editor or agent workflows.

By contrast, the authoritative boundary should retain or explicitly validate facts that define the meaning of success:

- source/model/tool identity for the claim;
- complete obligation coverage for the advertised promise;
- unsupported/assumed semantics classification;
- TCB/trust accounting;
- association of proof evidence with the exact subject;
- publication fencing so a valid result for one generation cannot authorize another.

Basis: derived application of Anneal design constraints to the Make/Ninja boundary history.

This is analogous to Ninja keeping correctness-relevant execution facts—command identity and discovered dependencies—inside its executor model even though high-level build policy lives in the generator.

### 9. A stable batch command and an interactive daemon need not be rival semantic engines

The Make/Ninja history argues against framing the decision as either "everything in one daemon" or "the batch executable must independently discover everything." A two-level design can share semantics while assigning different operational roles.

One plausible shape is:

1. A project/interactive service maintains snapshots, user configuration, discovery state, caches, and scheduling.
2. It constructs an explicit verification plan or invokes shared libraries that construct one.
3. A batch-capable verification core checks the plan against exact inputs, runs or verifies required stages, and emits a result whose identity/trust scope is explicit.
4. Interactive feedback may use partial or cached work, but it cannot silently relabel advisory state as authoritative success for publication.

Basis: derived architecture, consistent with current Anneal design constraints but not selected by them.

This arrangement differs from naive duplication. The daemon and CLI can share libraries or a plan representation while differing in lifecycle, caching, and latency policy. J009's RLS/rust-analyzer history is a separate question about when one semantic engine cannot satisfy an editor workload; J042 contributes a narrower point: operational orchestration can be layered over a reusable authoritative command without forcing every convenience feature into that command.

### 10. The case for an all-in-one daemon is operational, and it should be measured against its state costs

An integrated daemon can be the better design when persistent state provides a material benefit that a generated-plan/batch split cannot cheaply reproduce. Examples include fine-grained incremental translation, reusable proof environments, snapshot-sensitive IDE feedback, expensive process initialization, or coordinated cancellation across a large dependency graph.

Those benefits come with costs that the Make/Ninja split avoids or makes more explicit:

- daemon state needs a freshness model across source, configuration, toolchain, environment, and upstream artifacts;
- cancellation is not rollback, so stale in-flight work must be prevented from acquiring current authority;
- reentrancy and concurrency expand the state machine;
- bugs in project discovery and cached dependency state can contaminate many requests;
- reproducing a result later is harder if the decisive plan was implicit in mutable process state;
- deployment and version skew become coupled to the long-lived service lifecycle.

Basis: derived. These are architecture risks, not measured failures of a current Anneal daemon.

A daemon is therefore justified when its retained state earns its complexity through measured or otherwise compelling workload needs. It need not be authoritative for publication merely because it is the best interactive host. A stable batch/revalidation path can remain the final authority, or the daemon can expose a snapshot/plan boundary that makes its authoritative operation reproducible.

### 11. Counting displaced complexity changes the apparent simplicity result

Ninja is intentionally small *because* a smarter meta-build system exists. Calling Ninja simple while ignoring GN/CMake would compare a subsystem with a whole system. The same accounting applies to Anneal.

If Anneal keeps a tiny batch core but requires every caller to independently discover toolchains, normalize project configuration, calculate source closure, handle retries, classify partial results, fence publication, and maintain TCB identity, then the system may be simpler only on paper. Conversely, if those responsibilities are genuinely policy/convenience concerns and a shared host provides them once behind explicit interfaces, a narrow verifier can reduce semantic coupling.

Derived criterion: evaluate a proposed boundary by *total responsibility and duplicated knowledge*, not by process count or the size of one component. Ask which module must change when a source of truth, environment rule, result-identity rule, or user workflow changes. A boundary is useful when it localizes those changes without hiding inputs the other side needs for correctness.

### 12. Conditional judgment for Anneal

A defensible default is:

- preserve a stable, scriptable batch verification boundary;
- allow richer orchestration, including a daemon, to prepare explicit work and optimize interactive use;
- keep success semantics, trust/assumption accounting, and subject identity at or below a boundary that does not depend on ambient daemon state being interpreted correctly after the fact;
- expose runtime-discovered semantic dependencies through explicit protocols rather than pretending all inputs are statically knowable;
- keep resource scheduling/cancellation close to the runtime that actually owns those resources;
- add persistent or incremental machinery only when its workload benefit is demonstrated enough to justify a larger freshness/state model.

This is closer to Ninja's generator/executor split than to a single giant Makefile, but the analogy stops before saying Anneal should literally generate a static DAG. Verification may have richer dynamic dependencies, proof-state reuse, unsupported-semantics handling, and source/model correspondence requirements than a build graph. The valuable transfer is the responsibility rule: move policy outward, but keep correctness-relevant facts observable at the boundary that grants authority.

## Boundaries

**No performance experiment was run.** This report does not measure GNU Make, Ninja, or any prospective Anneal architecture. Martin's historical Chromium timings are contemporaneous author reports explaining Ninja's origin, not reproduced benchmarks.

**Make and GNU Make are not one frozen design.** Feldman's 1979 paper establishes the original dependency/recipe mechanism and motivation; GNU Make 4.4.1 has decades of additional features. Claims about mature Make behavior are grounded in the GNU manual, not projected backward onto the 1975 implementation.

**Ninja's stated philosophy is project documentation, not proof of optimality.** The generator/executor split has strong deployment evidence, but the sources do not establish that it is globally superior to integrated build systems.

**The current Ninja revision is post-v1.13 development.** The exact repository revision documents some features marked for 1.14. Where chronology matters, this report labels versions as the manual does instead of implying they were all present in the latest stable release at the same date.

**Recipe opacity is not the same as hermeticity.** Neither Make nor Ninja automatically makes an arbitrary shell command hermetic. A declared graph can still omit environment, filesystem, plugin, network, clock, or toolchain inputs.

**Generated plans can be wrong.** Ninja's executor cannot validate arbitrary project-policy decisions made by GN, CMake, or another generator. The split changes the trust boundary; it does not eliminate it.

**Dynamic-dependency support is bounded.** Ninja's `dyndep` protocol permits additions only within dependent regions of the original graph. It is evidence that runtime discovery can coexist with a mostly precomputed plan, not evidence that every dynamic verifier dependency fits that model.

**Build freshness is weaker than proof authority.** A timestamp or command-hash match can be sufficient for a build system's configured notion of up-to-date output. Anneal's user promise requires justified subject identity, obligation coverage, and trust accounting. The report therefore does not recommend copying Ninja's freshness algorithm.

**No final Anneal API is proposed.** The verification-plan fields and host/core split are derived requirement categories. Current Anneal design explicitly leaves command names, schemas, process boundaries, and Rust/Charon/Aeneas/Lean ownership undecided.

**Adjacent campaign work is distinct.** J034 concerns build-system scheduling models broadly, J038 concerns dynamic/negative dependencies, J039 concerns early-cutoff equality, and J043 concerns Skyframe/hermetic graph discipline. This report uses only enough of those themes to explain the historical Make/Ninja boundary and does not claim to fulfill those questions.

## Evidence

### Make origin

- Stuart I. Feldman, "Make — a program for maintaining computer programs," *Software: Practice and Experience* 9(4), April 1979, pp. 255-265, DOI `10.1002/spe.4380090402`. Observed 2026-09-30. The abstract states that Make tracks relationships among program parts and issues commands needed to restore consistency, and that it had been in use on UNIX since 1975. Primary historical publication.
- Wiley landing/PDF endpoint: `https://onlinelibrary.wiley.com/doi/10.1002/spe.4380090402` and `/doi/pdf/10.1002/spe.4380090402`.

### GNU Make 4.4.1

- GNU Make manual, `https://www.gnu.org/software/make/manual/make.html`, observed 2026-09-30. Relevant sections include 2.1 "What a Rule Looks Like," 2.3 "How make Processes a Makefile," 3.7 parsing, 4 "Writing Rules," 5.7 recursive use, implicit rules, parallel execution, and functions. The manual directly states that Make does not know how recipes work and that the user must supply recipes that update targets.
- GNU Make 4.4.1 release announcement by Paul Smith, 2023-02-26: `https://lists.gnu.org/archive/html/info-gnu/2023-02/msg00011.html`. It identifies stable version 4.4.1 and MD5 `c8469a3713cbbe04d955d4ae4be23eeb` for `make-4.4.1.tar.gz`.
- Peter Miller, "Recursive Make Considered Harmful," engineering account preserved at `https://accu.org/journals/overload/14/71/miller_2004/`, observed 2026-09-30. Used only for the incomplete-DAG argument and reported engineering consequences, not as a normative Make specification.

### Ninja origin and current architecture

- Evan Martin, "Ninja, a new build system," 2011-02-06, `https://www.neugierig.org/software/chromium/notes/2011/02/ninja.html`, observed 2026-09-30. Project-author historical account of SCons, generated non-recursive Makefiles, Chromium startup latency, and the motivation for a low-feature executor.
- `ninja-build/ninja` revision `4e4df1e567eb3c1475a51af261cba2bfff60b4be`, `doc/manual.asciidoc` blob `81ecf7d388f899a1481df9f25ec1065710de679d`, observed 2026-09-30. Primary current project documentation. Relevant regions: "Philosophical overview," "Design goals," "Comparison to Make," generator usage, logs, dependency types, depfiles/deps, `restat`, pools, `dyndep`, validations, and GNU jobserver support.
- Historical Ninja manual at Chromium Git revision `a9071772ead9522d7ebb21048da08c8ea22cec21`, `https://chromium.googlesource.com/external/martine/ninja/+/a9071772ead9522d7ebb21048da08c8ea22cec21/doc/manual.asciidoc`, observed 2026-09-30. Used to check that the generator/assembler philosophy was present early rather than being a recent retrospective.
- Ninja release listing, `https://github.com/ninja-build/ninja/releases`, observed 2026-09-30. The v1.13.0 release notes identify automatic GNU Make jobserver client support as a new feature; current exact manual documents the later server interface as version 1.14.

### Anneal constraints

- `google/zerocopy` revision `cc135f46155b72e4b51188525c2974a3b84acf92`, `anneal/PRINCIPLES.md` blob `d5339a95254eae14ac201139d07d9d36d48a19fb`, observed 2026-09-30. Primary project authority for Anneal's user promise and decision principles.
- Same revision, `anneal/DESIGN.md` blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`, observed 2026-09-30. Primary current design contract: successful-result identity/scope, source/model justification, compositional boundaries, explicit/shrinkable trust, Rust-oriented ordinary interface, minimally sufficient mechanisms, and deliberate non-decisions about process/API ownership.
- `google/zerocopy#3732`, updated `2026-09-30T04:53:10Z`, J042. Native research agenda for this comparison. The report leaves issue progress unchanged.

### Evidence-role separation

The upstream manuals and project-author notes establish stated mechanisms and rationale. The historical latency numbers establish what Martin reported, not a controlled benchmark. The responsibility matrix and all Anneal recommendations are derived analysis. No source claims that Anneal should adopt a Ninja-like architecture.

## Revalidation

For a later GNU Make release, re-read the official manual sections governing rules/recipes, implicit rules, recursive make, parallel/jobserver operation, and any new dependency-discovery mechanisms. The report's key Make conclusion changes only if the engine begins deriving semantic dependencies from arbitrary recipes or substantially moves project policy out of the Make language by design.

For a later Ninja revision, diff `doc/manual.asciidoc` from `4e4df1e567eb3c1475a51af261cba2bfff60b4be`. The cheapest discriminating checks are the philosophical overview/non-goals plus the sections for generator rules, command/dependency logs, depfiles, `restat`, pools, `dyndep`, validations, and jobserver support. New features matter to this report when they move substantial project-policy evaluation into Ninja or change which runtime correctness/resource facts the executor owns.

For the historical rationale, retain the 2011 Martin note and early manual as fixed evidence. A later retrospective may add context but does not alter what those sources said at the time.

For Anneal, re-read `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` at the target revision and inspect any adopted architecture that defines plan/result identities, daemon state, incremental execution, or publication semantics. Re-evaluate the derived judgment if Anneal chooses a result model in which preparation errors are independently machine-detectable, or if measured workloads establish that persistent in-process state is either essential or unnecessary.

A practical architecture experiment, if one becomes necessary, should compare whole-system complexity rather than only batch-command size: enumerate which component owns project discovery, source/model/environment identity, hidden-input capture, scheduling, cancellation, cache invalidation, trust accounting, result authority, and publication fencing. A split is successful only if those responsibilities are explicit and not duplicated or silently omitted.