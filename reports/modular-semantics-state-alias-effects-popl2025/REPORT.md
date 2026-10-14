# Modular semantics: actual handler adequacy and state-effect limits

## Summary

Program Logics à la Carte supplies a concrete ITree/Iris interface for composing logical effect handlers and proving adequacy. Its source contains both universal demonic and existential angelic logical handlers, operational state-machine adequacy premises and a separate HeapLang bridge to small-step safety. These results can organize a MiniRust formalization, but do not make byte storage, alias transitions or Specr import correctness automatic.

The separate Logical Relations à la Carte thesis has a narrower extension interface: its expression steps do not update state. That limit matters for MiniRust, where reads can change alias state. Our checked sequential fragment proves that an explicit permission-update handler matches a direct interpreter for every finite trace; treating the same read as state-free permits a later write that the coupled model rejects.

## Applicability

The directly inspected primary artifact is Zenodo record 14180355, version v2 (published 2024-11-20), `the_artifact.zip`: 1,480,438 bytes, SHA-256 `bf5d86d5fef425b6031640391dddda4f60b3b029d680019ddaedefd17e4d3378`, MD5 matching upstream `c9a0543a0c06d4abcc56b25222fa2811`. Its expanded source is 5,420,269 bytes. The artifact's `iris-itree/` contains the investigated framework; bundled Iris/stdpp are separately identified by the archive bytes. No upstream Git revision is inferred from the archive.

The comparison thesis is Jonas Maier, *Logical relations à la carte*, March 2026. Its URL contains 2025, but the actual title page supplies March 2026. The appendix cites ETH GitLab commit `5ed76562ee78badeb8768e7cb00c1ea37557b709`; that source was inaccessible to the web reader here. Thesis results below are documentary, not direct artifact inspection or fresh theorem checking.

MiniRust is pinned at `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`. The executed subject is our `support/Effects.lean`, checked with Lean 4.34.1 `5045d0056413266e57c625dcd7c365b10e377c52`. No Rocq installation, 1.4GB artifact VM, native upstream execution or complete MiniRust effect embedding was attempted.

## Findings

### 1. A logical handler is a proof-relevant event contract

In `iris-itree/src/handler.v:11–24`, `iHandler` interprets an event given continuation propositions and a spawning continuation. Its `ihandler_mono` obligation preserves implication in these arguments. `sumH` delegates sum events to their corresponding handlers. `inH` requires logical equivalence between a subhandler and the combined handler on the injected events; sharing an event constructor name is insufficient.

This interface supports local reuse because a generic bind/frame rule can quantify over the handler's interpretation. It does not establish that a new handler describes the intended concrete state transition. That connection is supplied by the additional adequacy interface.

`wpi.v:wpi_translation` gives a separate event-translation theorem. Its premise quantifies over each event, result type, continuation and postcondition, requiring a proof that the target event computation under the target handler satisfies the source logical contract. Thus translating an event into several lower-level operations is an actual proof obligation. A smaller sequential specialization has a weaker premise that the source comments say typically does not hold for events that spawn threads.

Basis: **source**, `handler.v` and `wpi.v:653–705+`; **derived**, MiniRust integration consequence.

### 2. State-machine adequacy retains operational transitions and a coupled invariant

`exec.v:533–555` defines `eHandlerAdequate` and `seHandlerAdequate`. The sequential class supplies an invariant on concrete handler state. For every event, state, continuation relation and logical continuation propositions, an operational handler step plus the logical event contract and invariant must produce a suitable result/state, preserve the invariant and establish the result's logical continuation.

`wpi_adequate` at lines 707–724 consumes an `exec` relation, WP proof and initial handler invariant, and produces a related reached state plus invariant and continuation/thread-pool facts. `wpi_adequate_pure` additionally exposes a ghost-state-parametric route to a pure conclusion. These are actual source theorem interfaces, with retained masks and concurrency bookkeeping; this report did not recheck them in Rocq.

`sumSEH` at lines 830–841 uses a product of the two handler states. An event from the first component changes only the first state; an event from the second changes only the second. `sumSEH_adequate` at lines 880–894 composes their invariants using separating conjunction.

That product construction is useful for independent state components. It does not directly describe an alias-sensitive memory access that must consult and update both bytes and permissions. Such an access needs a joint handler or an explicitly verified sequence of events with a shared invariant and appropriate atomicity. A generic sum theorem cannot supply the missing byte/permission interaction premise.

The source's `stateH` interprets Get/Set via an explicit `stateInterp` invariant. Its relational state-elimination adequacy assumes the surrounding handler is `Sequential`. Concurrency has a different thread-pool path. Therefore a sequential handler-elimination argument cannot simply be reused for arbitrary concurrent interleavings.

Basis: **source**, `exec.v`, `state.v:47–63,112–118`; **derived**, interaction and concurrency obligations.

### 3. Demonic, angelic and UB effects are distinct supported modules

`choice.v:demonicH` requires the continuation for every answer. `angelic_choice.v:angelicH` requires an existential answer, and its WP rule proves the choice from a selected continuation proof. `ub.v:ubH` interprets UB as False; its operational interpreter returns a separately tagged `UbCrash`.

There is a concrete domain mismatch for a direct MiniRust import. This artifact's `EDemonic` constructor requires `EqDecision A` and `Inhabited A`; the comment explains that inhabitedness supports existence of the interpretation function. MiniRust's semantic `pick` explicitly allows an empty allowed set, representing no behavior. The artifact's ordinary choice module therefore cannot represent every such MiniRust operation by simply choosing the predicate subtype without an additional empty-choice construction or domain restriction.

The convenience `angelic_choice` also requests decidability/inhabitedness, whereas the underlying `EAngelic` constructor and `wpi_angelic_vis` are more general. A formal import should inspect the exact constructor/rule it uses rather than infer one global limitation from the helper. No theorem in this report connects the artifact's state-machine angelic interpretation to MiniRust's full predictive exposed-provenance semantics.

Basis: **source**, `choice.v:20–32,50–56`, `angelic_choice.v`, `ub.v`; MiniRust pinned README; **derived**, import-domain gap.

### 4. Recursion, divergence and small-step adequacy have explicit interfaces

The framework's WP is defined using a least fixed point. `step.v:9–16` explains that this makes it termination-sensitive by default. Step events and a selected `Later` versus `Identity` modality support different reasoning modes. Recursion in the case-study denotations uses ITree's `rec` combinator; a recursive interpreter being expressible does not by itself prove that its logical reasoning ignores divergence correctly.

The artifact's own paper-to-code map distinguishes several levels. The introductory `LangAdequate` statement is not separately formalized there; it points to the concurrent `examplelang/adequacy.v:wp_adequacy_irel`. The latter explicitly composes thread-pool, UB, state and demonic interpretation relations, and distinguishes normal return, safe last-thread termination and crash.

For HeapLang, `partially_adequate_opsem_adequate` at `heaplang/opsem_adequacy.v:1558–1581` bridges interpretational adequacy to Iris `adequate NotStuck`. `wp_later_opsem_adequate` and `wp_total_opsem_adequate` follow at lines 1584–1603. This separate operational bridge is the component a MiniRust port would have to replace or instantiate. The generic ITree WP does not already prove MiniRust's executable transition relation or a Rust-to-core lowering.

Basis: **source**, `wpi.v`, `step.v`, case-study adequacy and mapping document; **derived**, MiniRust bridge boundary.

### 5. The Logical Relations thesis restricts stateful expression extensions

The March 2026 thesis reports compositional syntax/typing/step and compatibility results for extensions satisfying its interface. Its expression compatibility relation has shape `E → E → Prop`, so extensions cannot update state. The imperative example permits read-dependent expression evaluation while separate statements update globally scoped, preinitialized variables. It has no expression-level state update or encapsulation mechanism there.

The thesis also restricts extension binders and expression-dependent values; custom advanced value relations remain future work. It reports propositional extensionality, dependent functional extensionality and `eq_rect_eq` assumptions. These are statements of the thesis, not independently checked assumption closures.

MiniRust's mutable memory receiver for loads means a read may update alias permissions. Encoding such a read as one of this thesis's existing state-free extension steps would discard a relevant effect. One may instead move the operation to a stateful base language or generalize the interface, but then the old compatibility theorem requires a new applicability argument.

Basis: thesis **documentation**, §§6.6,7.6–7.7,9.3,10.1; MiniRust memory-interface **source**; **derived**, model mismatch. The cited source commit remains inaccessible rather than nonexistent.

### 6. A checked interacting-effect fragment separates representation from proof reuse

`Effects.lean` models a natural-number byte and one sibling writer-permission bit. A read leaves the numeric byte unchanged but disables the writer; a write is allowed only while that permission remains. This is a deliberately small interaction witness, not a Tree Borrows implementation.

The direct interpreter performs the coupled transition. A second interpreter first processes a permission event, then the byte event. `event_agreement` proves both implementations agree for every operation and state. `trace_agreement` lifts that equality to every finite operation list and state. The result preserves rejection as well as final state; it is stronger than checking equal returned byte values in successful examples.

`read_effect_matters` then checks the negative control: read followed by write rejects in the coupled model but succeeds when reads are approximated as state-free. Thus the explicit handler split can be correct, while deleting the cross-effect update is not. The generic framework could support a proved implementation along this pattern; no artifact integration or MiniRust simulation is claimed.

Lean checks all three final endpoints. Event/trace agreement use `propext`; the concrete counterexample uses no axioms. No external solver or native theorem prover artifact was used.

Basis: **execution**, owned Lean fragment and log; **derived**, the specific analogy to MiniRust interaction.

### 7. Reusable source proofs retain a nontrivial trust boundary

The artifact declares dependencies on ITree 5.1.2, Elpi 2.2.3, Paco 4.2.1 and a selected Iris development. Its README and `axioms.v` explicitly declare functional choice, UIP/`eq_rect_eq` and strong-bisimulation-implies-equality for ITrees. The inspected framework/case-study source scan found no `Admitted` command, but a textual scan does not determine per-theorem assumptions or prove dependency completeness.

The source files end relevant proofs in `Qed`; this is source evidence of proof developments, not evidence of a fresh successful kernel run. The artifact's mapping document explicitly preserves mask/later/timeless side conditions omitted from paper presentations. Those conditions belong to any imported theorem.

For a maintainable MiniRust formalization, the useful modular boundary is therefore: fixed event syntax and semantics, explicit logical handler/resource invariant, checked event translation and adequacy, then a separate link to MiniRust/Specr/source Rust. Updating one module can reuse the framework while still requiring revalidation of interaction and translation premises.

Basis: **source/documentation**, artifact README, opam, axioms and paper-to-code map; **derived**, conditional adoption interface.

## Boundaries

- **Established:** direct source-artifact audit of actual handler/adequacy/choice/state interfaces, documented thesis limits, checked owned direct-versus-handler equivalence and a state-effect omission counterexample.
- **Unestablished:** a MiniRust ITree encoding, byte/provenance/Tree Borrows handler adequacy, full mixed-choice predictive semantics, Specr import theorem, source Rust linking theorem or a measured proof-maintenance cost comparison.
- **Not run:** artifact Rocq/Coq proofs, dependency installation, VM, ITree extraction or Islaris case-study execution. The source archive and printed theorem statements are not fresh kernel evidence.
- **Inaccessible:** the Logical Relations thesis's exact ETH source commit. No absence claim about that repository or later work follows.
- **Not examined:** full concurrent handler composition, relaxed memory, full library proof porting, totality/termination of a MiniRust interpreter or every inherited axiom's theorem-specific use.

## Evidence

Acquired 2026-10-14. Primary artifact: [Zenodo14180355 source package](https://zenodo.org/records/14180355), SHA-256 above. `source-evidence.json` binds selected members, hashes and symbols. `support/theorem-excerpts.txt` preserves exact narrow interfaces so that the report does not rely on an unretained local extraction. The accompanying license identifies these excerpts as source evidence.

The [official project page](https://plf.inf.ethz.ch/research/popl25-itree-program-logic.html) identifies the POPL2025 work, and the [Logical Relations thesis](https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/MasterTheses/2025-Jonas-Thesis.pdf) supplies its separate March2026 interface. `support/Effects.lean` and `lean.log` retain the performed mechanization.

## Revalidation

Reacquire only the small exact source archive, verify its digest, inspect the indexed handler/adequacy definitions and mapping document, and rerun the owned Lean fragment. A full Rocq recheck requires the declared dependency closure and per-theorem assumption inspection; it was deliberately not substituted with a successful Lean analogy.

Before applying the framework to MiniRust, implement one byte/alias operation with its exact combined state and prove both event adequacy and operational correspondence. Recheck empty choice and divergence separately. If using the thesis framework, first account for its state-update and custom-value-relation restrictions.

*Authored by an AI agent acting on joshlf's behalf.*

