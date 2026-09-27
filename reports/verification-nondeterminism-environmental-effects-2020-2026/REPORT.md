# Nondeterminism and environmental effects in program verification

## Summary

A verification model must say where choices come from and what a proof quantifies over. Nondeterminism and environmental effects are therefore semantic structure, not incidental noise to erase before verification.

Three representative mechanized designs make the useful distinctions explicit. CompCert describes a program by possible observable behaviors: termination, silent divergence, reactive divergence, or going wrong, each carrying a finite or infinite trace of externally visible events. Its external calls are relations rather than functions, so a call such as input may have more than one admissible result; a separate deterministic-world construction can then instantiate those environmental choices. Interaction Trees (ITrees) instead represent interaction directly as uninterpreted visible events whose continuations depend on an environment response; event handlers give those effects meaning. Choice Trees (CTrees) add explicit internal nondeterministic branching alongside external events, so internal choice and environment interaction remain different semantic phenomena.

The reusable rule is that verification should preserve the relevant *set or structure of possible behaviors*, or make the assumptions that reduce that set explicit. Choosing one result for an environmental input, one scheduling choice, or one outcome of an underspecified operation is not a sound simplification merely because the resulting model is easier to prove. Likewise, an unmodeled effect is not automatically equivalent to arbitrary nondeterminism: it may instead be outside the theorem's scope, represented by an abstract event with a handler obligation, or constrained by a relation or protocol.

For Anneal, this distinction matters whenever a Rust operation, Charon/Aeneas translation step, or Lean model can interact with state not represented by a pure function. A future adequacy or translation-correctness story should state whether such behavior is rejected, abstracted as an effect, parameterized by an environment, or related by a refinement that quantifies over possible outcomes. Silently collapsing it to one deterministic value would strengthen the model without a corresponding source-level justification.

## Applicability

This report is a focused synthesis of three representative semantic architectures, not an exhaustive survey of nondeterminism in verification.

The first subject is CompCert 3.18 at `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`. The directly inspected source files are `common/Events.v`, `common/Determinism.v`, and `common/Behaviors.v`. The report uses CompCert to show a relational operational-semantics design in which observable traces, environmental responses, whole-program outcomes, and simulation/refinement are explicit.

The second subject is Xia et al., “Interaction Trees: Representing Recursive and Impure Programs in Coq,” POPL 2020, DOI `10.1145/3371119`. It supplies a coinductive denotational design for recursive effectful programs in which events are left uninterpreted until handlers give them semantics.

The third subject is Chappe et al., “Choice Trees: Representing Nondeterministic, Recursive, and Impure Programs in Coq,” POPL 2023, DOI `10.1145/3571254`. It extends the interaction-tree style with explicit nondeterministic branching and associated bisimulation/refinement tools.

These subjects are compared for one issue #3720 inventory item: **Nondeterminism and environmental effects**. The report does not claim that CompCert, ITrees, or CTrees is the right semantic foundation for Anneal. It extracts distinctions that an Anneal proof architecture should preserve regardless of the particular formalism chosen.

## Findings

### A deterministic implementation model and a deterministic environment are different assumptions

CompCert makes external behavior relational. At the examined 3.18 revision, `extcall_sem` relates the global symbol environment, argument values, pre-call memory, generated trace, result value, and post-call memory. The external-call contract then requires properties including receptiveness to matching traces and determinism *up to matching traces*. This structure does not define an external call as a single pure function from arguments to result.

`common/Determinism.v` names one source of nondeterminism directly: system-call results are left unspecified. It introduces a coinductive `world` whose `io`, volatile-load, and volatile-store components determine what response and next world follow each external interaction. `possible_trace` and `possible_traceinf` then ask whether a finite or infinite trace is compatible with one such world.

The important separation is conceptual. A semantics may admit many environment responses, while a particular environment model resolves those responses deterministically. Proving a property under one deterministic world is therefore not automatically a proof for every environment allowed by the more general semantics. Conversely, quantifying over all allowed worlds is stronger than testing or proving one fixed response sequence.

Basis: **source** — CompCert 3.18 `common/Events.v`, `extcall_sem` and `extcall_properties`; `common/Determinism.v`, `world`, `possible_trace`, and `possible_behavior`.

### Observable effects belong in behaviors, not merely in final return values

CompCert 3.18 represents four whole-program outcomes: termination with a finite trace and exit code, silent divergence after a finite trace, reactive divergence with an infinite trace, and going wrong after a finite trace. Its event vocabulary includes system calls, volatile loads and stores, and annotations. Thus two executions that return the same value can still have different observable behaviors.

This matters for verification because a property stated only over final values can erase exactly the interactions that distinguish correct from incorrect executions. I/O ordering, values read from an external device, writes to a volatile location, and infinite reactive behavior are all examples where the trace is semantically relevant.

CompCert's `behavior_improves` and simulation theorems make this explicit at the compiler boundary: the correctness argument relates source and target *behaviors*, not just returned data. For a source behavior that is not `Goes_wrong`, the forward-simulation result recovers the same safe behavior in the target; the more general relation allows target behavior to improve on source undefined behavior.

Basis: **source** — CompCert 3.18 `common/Events.v` event/trace definitions and `common/Behaviors.v` `program_behavior`, `behavior_improves`, and `forward_simulation_behavior_improves`.

### Environment interaction and internal nondeterminism should not be conflated

Interaction Trees model recursive effectful programs using uninterpreted events and continuations. An event states that the program is asking its environment to perform an effect and provide a response; an event handler later interprets that request as a concrete monadic action. The semantics therefore separates a program's structure from the chosen implementation or model of its environment.

Choice Trees were introduced specifically to add nondeterministic branching to this style of semantics. Their nodes distinguish external events from internal branching, and their theory includes simulation, bisimulation, and trace-equivalence relations. This is evidence that “the environment can answer in several ways” and “the program itself has several internal next steps” are usefully modeled as separate dimensions even when both ultimately produce multiple possible executions.

For a verification architecture, preserving that distinction prevents assumptions from moving silently across the boundary. For example, replacing a nondeterministic scheduler with a deterministic handler is a different modeling step from supplying a handler for a file-read event. The resulting proof obligations and refinement directions need not be the same.

Basis: **source** — Xia et al. 2020, DOI `10.1145/3371119`; Chappe et al. 2023, DOI `10.1145/3571254`.

### Nondeterminism changes the shape of refinement

When a semantics maps one program to multiple possible behaviors, equality of one observed run is too weak to establish semantic preservation. A useful correctness relation must quantify over possible outcomes in the direction required by the theorem.

CompCert's source makes this concrete. `program_behaves` is a relation from a program semantics to a behavior, not a function returning one behavior. Its forward-simulation theorem says that for each source behavior there exists a target behavior that is equal or an allowed improvement from source undefined behavior. The theorem is therefore quantified over behaviors admitted by the source relation.

CTrees likewise provides simulation/refinement relations over nondeterministic trees rather than reducing the tree to one selected path. ITrees provides equivalence up to weak bisimulation for interactive computations. These formalisms differ, but all preserve the branching or interactive structure needed to state a meaningful relation between systems with more than one possible execution.

Derived consequence: before adopting a relation such as equality, forward simulation, backward simulation, trace inclusion, bisimulation, or contextual refinement, an Anneal design must identify which side is allowed to have more behaviors. “Equivalent” is underspecified until the allowed direction of nondeterminism is fixed.

Basis: **source** — CompCert 3.18 `common/Behaviors.v`; Xia et al. 2020; Chappe et al. 2023. **Derived** for the Anneal design consequence.

### Abstracting an effect is different from deleting it

ITrees' use of uninterpreted events provides a reusable pattern for abstraction. A computation can expose an event without committing to one concrete operating-system, device, oracle, or runtime implementation. A handler later assigns semantics to that event. The abstract program can therefore be reasoned about compositionally while still recording that an environmental interaction occurs.

CompCert's external-call relation provides another form of abstraction: it does not erase the interaction, but constrains what traces, values, and memory transitions count as an admissible call. A deterministic world may then instantiate the external responses.

Both patterns differ from replacing an effectful operation by an arbitrary pure value or by an opaque axiom with no behavioral contract. An abstraction remains sound only relative to the relation, handler, protocol, or assumption that defines the allowed behavior. If a translator has no semantics for an operation, the honest outcomes are therefore to reject it, leave an explicit proof assumption, or translate it to a suitably specified abstract effect. Treating unsupported behavior as a convenient deterministic function would silently strengthen the theorem.

Basis: **source** — CompCert 3.18 `common/Events.v` and `common/Determinism.v`; Xia et al. 2020. **Derived** for the translation-design consequence.

### Environmental assumptions are part of the theorem boundary

A deterministic external world can turn an otherwise relational environment into a single response sequence, but that world is then part of the proof context. Likewise, an ITree handler determines what an event means, and a CTree refinement relation determines which branches must be matched.

This means an environmental assumption is not ancillary test configuration. It is part of the semantic boundary of the theorem. A proof under “reads return this stream,” “the allocator returns these addresses,” “the scheduler chooses this thread,” or “this foreign call satisfies this relation” establishes a conditional property unless a separate theorem quantifies or abstracts over those choices.

For Anneal, source-to-model adequacy should therefore make environmental parameters visible in one of three places: the modeled state/effect signature, explicit theorem hypotheses, or the refinement relation itself. If the parameter disappears entirely, a later proof reader has no way to distinguish “proved for all admissible environments” from “proved after fixing one convenient environment.”

Basis: **derived** from the three subjects' explicit separation between computation and environment/choice semantics.

### Nontermination and environmental interaction can coexist

CompCert distinguishes silent divergence from reactive divergence. The former eventually performs no further observable I/O; the latter produces an infinite trace of observable events. ITrees are coinductive and explicitly designed for potentially nonterminating computations that continue to interact with their environments.

This prevents a common simplification error: “diverges” is not one behavior class if the property of interest includes external effects. A server that runs forever while servicing requests is observably different from a computation that silently loops after its last event. Correctness statements for interactive or systems code may therefore need trace-sensitive liveness or safety properties in addition to termination-sensitive functional results.

Basis: **source** — CompCert 3.18 `common/Behaviors.v`; Xia et al. 2020.

### A useful Anneal adequacy checklist follows from these distinctions

For every Rust/Charon/Aeneas construct that is not a pure deterministic function of modeled state, an adequacy argument should answer four questions:

1. **Choice owner:** Is variability internal to the program semantics, supplied by an environment, or both?
2. **Observable surface:** Which events, state changes, errors, divergence modes, or return values are observable to the property being proved?
3. **Allowed outcomes:** What relation, handler, protocol, or assumption defines the admissible responses and branches?
4. **Preservation direction:** Must translation preserve all source behaviors, forbid new target behaviors, establish bisimulation, or satisfy another refinement relation?

A fifth question applies when the construct is unsupported: does the pipeline reject it, preserve an explicit assumption/effect, or accidentally choose a behavior? Only the first two can be understood without a hidden strengthening of semantics.

Basis: **derived** synthesis from CompCert, ITrees, and CTrees.

## Boundaries

- **Not examined:** this report does not survey probabilistic semantics, quantitative probability distributions, randomized algorithms, or probabilistic program logics. Probabilistic choice is not interchangeable with ordinary nondeterministic choice.
- **Not examined:** concurrency memory models, weak-memory reorderings, fairness, scheduler semantics, and data-race reasoning are separate subjects. CTrees includes concurrency case studies, but this report uses it only for the internal-choice versus external-event distinction.
- **Not examined:** this report does not define an operational semantics for Rust, Charon LLBC, Aeneas Lean, or Anneal annotations.
- **Not examined:** no fresh CompCert, Coq/Rocq, ITree, or CTree proof development was executed. The CompCert findings are source inspection; the ITree/CTree findings come from the published papers and their stated mechanically verified constructions.
- **Known not to apply:** CompCert's exact event vocabulary and `behavior_improves` relation are CompCert-specific. They are examples of a semantic architecture, not requirements for Anneal.
- **Known not to apply:** ITrees by themselves are not the same abstraction as CTrees' explicit internal nondeterministic branching. The CTree work was motivated in part by representing nondeterministic choice more directly.
- **Unknown:** which environmental or nondeterministic Rust behaviors Anneal V2 will ultimately choose to support rather than reject. This report supplies questions and modeling patterns, not that policy decision.
- **Unknown:** whether Aeneas' current functional translation has specific hidden assumptions about I/O, concurrency, allocator behavior, or other external state beyond the separate source reports already in this corpus. That must be established from Aeneas' exact supported-language boundary rather than inferred from this theory report.
- An opaque or unsupported operation is **not** automatically modeled as arbitrary nondeterminism. The semantic consequence depends on the actual translation or logic rule.

## Evidence

### CompCert 3.18 source

Repository: `AbsInt/CompCert`  
Revision/tag: `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` / `3.18`  
Release commit message: `CompCert 3.18 source snapshot`.

`common/Events.v`, blob `ac8d1bb42e4e9d2e04bc6d7c1c27ea87fbc95564`:

- event values and events: `eventval`, `event`;
- finite and infinite traces: `trace`, `traceinf`;
- external-call semantic relation: `extcall_sem`;
- external-call constraints: `extcall_properties`, especially `ec_trace_length`, `ec_receptive`, and `ec_determ`.

Evidence role: **source**.

`common/Determinism.v`, blob `7c2f99cb801bacd9432c94494edb0c538a61a2f7`:

- explicit explanation that unspecified system-call results are a source of nondeterminism;
- deterministic `world` with I/O and volatile-load/store response functions;
- `possible_event`, `possible_trace`, `possible_traceinf`, and `possible_behavior`.

Evidence role: **source**.

`common/Behaviors.v`, blob `822b08832f491e82fefc5b60251c13a63ef71301`:

- `program_behavior`: `Terminates`, `Diverges`, `Reacts`, `Goes_wrong`;
- relational `program_behaves`;
- `behavior_improves`;
- `forward_simulation_behavior_improves` and `forward_simulation_same_safe_behavior`.

Evidence role: **source**.

### Interaction Trees

Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur, Gregory Malecha, Benjamin C. Pierce, and Steve Zdancewic. “Interaction Trees: Representing Recursive and Impure Programs in Coq.” *Proceedings of the ACM on Programming Languages* 4 (POPL), Article 51, 2020. DOI `10.1145/3371119`.

Stable identifiers and access points:

- DOI: `https://doi.org/10.1145/3371119`
- arXiv: `1906.00046`

The paper defines interaction trees from uninterpreted events and continuations, interpreters from event handlers, recursive/nonterminating computations, and equivalence up to weak bisimulation. It includes a termination-sensitive compiler-correctness case study.

Evidence role: **source**.

### Choice Trees

Nicolas Chappe, Paul He, Ludovic Henrio, Yannick Zakowski, and Steve Zdancewic. “Choice Trees: Representing Nondeterministic, Recursive, and Impure Programs in Coq.” *Proceedings of the ACM on Programming Languages* 7 (POPL), 1770–1800, 2023. DOI `10.1145/3571254`.

Stable identifiers and access points:

- DOI: `https://doi.org/10.1145/3571254`
- arXiv: `2211.06863`

The paper introduces CTrees for nondeterministic, recursive, impure computations. It distinguishes external events from two forms of nondeterministic branching, supplies bisimulation/refinement machinery, and connects CTrees to the ITree infrastructure through a monad morphism used to implement nondeterministic effects.

Evidence role: **source**.

No fresh **execution** evidence was produced.

## Revalidation

For a newer CompCert release, the cheap discriminating check is source-level:

1. inspect `common/Events.v` for the event vocabulary, `extcall_sem`, and the receptiveness/determinism conditions on external calls;
2. inspect `common/Determinism.v` for `world`, `possible_trace`, and `possible_behavior`;
3. inspect `common/Behaviors.v` for the whole-program behavior type and the refinement/simulation theorems;
4. compare those definitions with the exact examined 3.18 revision before carrying this report's details forward.

For Interaction Trees, revalidation should check whether the event/continuation representation, handler-based interpretation, and weak-bisimulation reasoning used by the target development still match DOI `10.1145/3371119` or the precise ITree library revision in use. A newer library can add relations or effects without changing the original paper's subject.

For Choice Trees, revalidate the exact library/paper revision used by a downstream design, especially the distinction between external-event nodes and nondeterministic branching and the chosen simulation/equivalence relation. Do not infer current-library details from the 2023 paper merely because the name remains CTrees.

For Anneal, the cheapest architecture review is not a large experiment. Build a table of every effectful or nondeterministic construct admitted by the intended Rust/Charon/Aeneas subset and fill in the five questions from the Findings section: choice owner, observable surface, allowed outcomes, preservation direction, and unsupported-operation handling. Any blank cell is a concrete adequacy obligation. Then use minimal source/translation specimens only where the current tools' behavior is not already established by pinned source or existing reference reports.