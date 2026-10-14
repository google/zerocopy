# Gillian-Rust resource automation and the Creusot contract bridge

## Summary

Gillian-Rust implements a symbolic memory/resource state and translates a Pearlite contract fragment into separation-logic specifications alongside Creusot annotations. That provides a concrete safe/unsafe contract-exchange architecture. Its engine and Rust instantiation remain trusted implementations; the inspected paper explicitly leaves foundational gaps in the later/prophecy justification.

The reusable boundary is a matched specification and representation relation, with unsafe implementation obligations on one side and client obligations on the other. Common annotation syntax or a successful symbolic run does not by itself establish semantic equivalence or an independently replayable certificate.

## Applicability

Source is `GillianPlatform/gillian-rust@83d739e83034d71162fb66b569041cf301123df7`, dated 2025-05-21. The declared Rust toolchain is `nightly-2024-05-10`; the opam file pins Gillian `25c97535e513be63b4de3a0fc98e4ac096e75c0f` and simple-smt `b88c4b0685f6ec989e8b4c911e296c4087768db8`. The README describes a prototype and a tested Z3 4.12.4 environment. These are declared/documented requirements, not a fresh successful installation.

The separate formal/documentary subject is the [extended PLDI 2025 paper](https://arxiv.org/pdf/2403.15122v3), released 2025-04-10, SHA-256 `695533020d0ae8ea9d50ba6dc9c27316a417bc0b4163c3cc29dadfc94ea01094`. Current 2026 Creusot is not identified with the bridge's historical Creusot dependency. Both subjects were inspected on 2026-10-14; no compiler, symbolic engine, solver or client verifier was executed.

## Findings

### The Rust instantiation retains a structured heap and logical resource state

`symbolic/memory.ml:16–39` stores the type environment, layout knowledge, prophecy state, heap, lifetime context and observation context. This is more than pure input/output functionalization. The compiler's `MemoryAction` explicitly carries Rust types with allocation, load/store, deinitialization, free and discriminant operations. Loads include a copy/move flag. Thin pointers are encoded as a location plus a projection list; fat pointers add metadata. These representations and operations are the selected implementation subject. Basis: **source**, `codegen/memory.rs:12–40`, `heap.ml:21–49`.

Typed heap/predicate reasoning can justify operations exposed by this model, including partially initialized structures. It must not be confused with a complete byte-address/provenance/alias specification for arbitrary Rust operations. Those relationships need inspection of the relevant primitive and layout rules; this package does not invent them from the presence of raw-pointer syntax. Basis: **derived** boundary from the explicit representation.

### Lifetime and prophecy actions enforce local resource conditions

`lft_ctx.ml` represents lifetime liveness in a Boolean map. Consuming a live token removes it, while dead evidence persists; producing duplicate live evidence fails, and killing an absent/already dead lifetime reports a distinct error. This directly implements a live/dead consistency boundary. It does not establish fractional/shared-borrow support throughout the tool. Basis: **source**, `lft_ctx.ml:5–44`.

The prophecy state separates persistent value knowledge from observer/controller authority. Reading an absent prophecy value creates a symbolic variable; producing another value learns equality with the existing value. Assignment requires both observer and controller, rejecting missing resources, and updates their controlled value. Allocation creates fresh identifiers and symbolic values. Basis: **source**, `prophecies.ml:142–197`.

These mechanisms are source evidence for concrete symbolic resource transitions. Their consistency with a parametric prophecy logic still requires the separate metatheory conditions; satisfying local ownership checks does not establish absence of global causal loops.

### Creusillian emits two interpretations of one restricted contract

`creusillian/src/anf.rs` defines an explicit supported Pearlite fragment containing current/final expressions, models, calls, pattern matching, logical connectives and quantifiers. It lowers through `CoreTerm` and `PreGil` into separation-logic specification material. The emitter's `encode_specs` places the original clauses under Creusot attributes and the elaborated specification under Gillian attributes according to compilation configuration. Thus the bridge is a real translation pass, not merely two tools both recognizing `requires`. Basis: **source**, `anf.rs:12–47,234–370,581–652`, `lib.rs:201–216`.

The boundary additionally uses ownership predicates for the concrete representation and its abstract logical values. A safe client's pre/postconditions become obligations for the unsafe implementation's resources and logical value relation. Exact input/output ownership and current/final relationships must be preserved by that elaboration; independently chosen contracts with the same names would not suffice. This is a **derived** composition requirement grounded in the inspected emitter and contract elaboration.

The emitter references the older `creusot_contracts` API. Compatibility with the separately pinned 2026 Creusot, whose library is named `creusot-std`, was not built or assumed. Porting/testing that handshake is an integration task, not evidence the historical architecture was absent.

### The publication explicitly leaves foundation and language gaps

The extended paper §8 identifies omitted later modalities and an unproved connection between predicate dataflow and the absence of prophecy causal loops. It reports no shared-reference ownership/fractured-borrow treatment, concurrency constructs or Send/Sync proof obligations, and no Stacked Borrows/Tree Borrows model. Specification lifetimes are limited, preventing the demonstrated iterator case, and MIR closure support is incomplete. It also explains that borrow-extraction rules generate a trusted conclusion lemma alongside a proved premise lemma, justified by an external rule argument. These are material stated limits of the investigated prototype, rather than a completed foundational Rust theorem. Basis: **documentation**, §4/§8 of the pinned paper.

No Rocq or Lean proof source was present in the recursively inspected Rust repository tree. That narrow absence observation does not prove no external development exists, nor does it imply the Gillian framework's general metatheory is false. It does mean a RustHornBelt citation alone cannot replace the missing instantiation/translation justification in this package. Basis: **source** tree inspection + **derived** evidentiary boundary.

### Replay would need primitive and entailment evidence as well as symbolic paths

The inspected engine source mutates resource states and accumulates pure constraints, with solver-dependent delayed branching. A trace of selected symbolic states can aid debugging/reproduction, but accepting it without trusting the engine needs a defined operational-step and entailment checker. The Rust memory/borrow/prophecy primitives, predicate unfolding, trusted lemmas and source-to-GIL compilation must also be justified. Basis: **source** + **derived** requirements.

The selected prophecy serializer emits `Null` and its deserializer reports not implemented. This is evidence about that serializer, not proof that Gillian has no other tracing or certificate facilities. No independently replayable Rust verification derivation or checked certificate language was established by the inspected interfaces. That original inspection left a concrete derivation-interface gap. The added source-specific replay appendix supplies the researched interface and a selected primitive adapter; implementing a full exporter/checker and proving its Rust/resource adequacy remain explicit obligations.

### A hybrid acceptance boundary should share meaning and record assumptions

For Anneal, this architecture answers a design question: a lightweight first-order client contract can be connected to a richer unsafe resource proof through an explicit representation/ownership predicate. The acceptance rule must retain the exact contract translation, permitted callers, linked bodies, model semantics, trusted lemmas and solver assumptions. Current Creusot's own permission facilities may change the practical division of work; the 2025 paper's safe-only comparison should not be carried forward as a current exclusion.

Implementing that boundary, checking it in Lean, or measuring annotation/runtime cost is future engineering/measurement. Research still required includes exact compatibility with current tools and the foundational gaps identified above. These are distinct from reconstructing the existing prototype's exchange mechanism, which this source investigation does establish.

### A source-specific replay contract for Gillian-Rust

Basis: **source**, **derived** conditional soundness interface, and an original small **execution** control. Rust subject: `GillianPlatform/gillian-rust@83d739e83034d71162fb66b569041cf301123df7`. Its [locked dependency](https://github.com/GillianPlatform/gillian-rust/blob/83d739e83034d71162fb66b569041cf301123df7/Gillian-Rust/gillian-rust.opam.locked#L114) selects Gillian engine `25c97535e513be63b4de3a0fc98e4ac096e75c0f`. These exact subjects replace a generic proposal to “log symbolic execution.”

#### Existing reports and proof commands are useful inputs, not independent evidence

The engine's [Matcher.mli](https://github.com/GillianPlatform/gillian/blob/25c97535e513be63b4de3a0fc98e4ac096e75c0f/GillianCore/engine/Abstraction/Matcher.mli) explicitly distinguishes postcondition, fold, call, invariant, logic-command and predicate-guard matching. It exposes assertion/matching/result records carrying substitutions, states, plans and remaining cases. It separately provides produce, consume, fold/unfold and wand-packaging interfaces. These are actual instrumentation seams.

At this pin, [Verifier.ml](https://github.com/GillianPlatform/gillian/blob/25c97535e513be63b4de3a0fc98e4ac096e75c0f/GillianCore/engine/Abstraction/Verifier.ml#L516) checks the results returned by the symbolic interpreter and matches postconditions. An empty procedure result list is an operational error; successful matching is over those returned results. This is not an independently checked theorem that the interpreter covered every required execution. For a lemma with no proof, the branch rejects when `Config.lemma_proof` is enabled and otherwise returns true. The exact flag and allowed trusted lemmas must therefore be part of a replay policy; no default-configuration claim is inferred here.

The Rust compiler's [lemma.rs](https://github.com/GillianPlatform/gillian-rust/blob/83d739e83034d71162fb66b569041cf301123df7/lib_rust_to_gil/src/logic/lemma.rs#L87) turns trusted lemmas into hypothesis/conclusion records with `proof: None`. Other lemma bodies become GIL proof commands, including lemma application, separating assertion and assumption commands. Replaying a command that adds a producer-chosen assumption is insufficient: the consumer must justify it from the initial domain, a checked path guard, or an explicit permitted assumption.

#### What the primitive replay interface must actually check

| Selected source seam | Required certificate meaning |
| --- | --- |
| [memory.ml: execute_load/store](https://github.com/GillianPlatform/gillian-rust/blob/83d739e83034d71162fb66b569041cf301123df7/Gillian-Rust/gillian_rust/lib/symbolic/memory.ml#L64) | Exact type/projection/location, copy-versus-move choice, entry resource/initialization/layout facts, resulting value/heap and preserved frame; primitive implementation/model adequacy is a separate proved interface. |
| [lft_ctx.ml: cons/produce/kill](https://github.com/GillianPlatform/gillian-rust/blob/83d739e83034d71162fb66b569041cf301123df7/Gillian-Rust/gillian_rust/lib/symbolic/lft_ctx.ml) | Consuming live evidence removes it; dead evidence persists; producing duplicate live evidence fails; killing absent/dead evidence fails. Replaying only a numerical lifetime identifier loses linearity. |
| [prophecies.ml: consume/produce/assign](https://github.com/GillianPlatform/gillian-rust/blob/83d739e83034d71162fb66b569041cf301123df7/Gillian-Rust/gillian_rust/lib/symbolic/prophecies.ml) | Track persistent future-value information separately from linear observer/controller authority. Assignment needs both. Producing a missing observer/controller may add equality constraints; allocation needs freshness. Substitution/merging must preserve the interpreted resources, not merely combine Boolean fields. |
| [obs_ctx.ml: cons/prod_observation](https://github.com/GillianPlatform/gillian-rust/blob/83d739e83034d71162fb66b569041cf301123df7/Gillian-Rust/gillian_rust/lib/symbolic/obs_ctx.ml) | Consumption checks entailment; production checks satisfiability and adds observations. Replace solver decisions with checked formula evidence under the exact quoted context. An unchecked UNSAT answer cannot prune a required branch. A SAT witness establishes consistency only; authorizing a new observation additionally requires the selected ghost-update theorem and causal/dataflow premises. |
| [Matcher.ml: fold/unfold/package_wand](https://github.com/GillianPlatform/gillian/blob/25c97535e513be63b4de3a0fc98e4ac096e75c0f/GillianCore/engine/Abstraction/Matcher.ml#L2257) | Bind predicate definitions and substitutions; consume the right resources and return the exact residual frame. Wand introduction needs a hypothetical disjoint extension and a derivation of its RHS, not a successful assertion that one convenient state matches. |

The selected prophecy serializer emits `Null` and its inverse is unimplemented. Core JSON logging therefore does not, by itself, supply a complete replayable Rust resource witness. That is a narrow serialization fact, not a claim that Gillian has no useful logs or any possible exporter.

#### A concrete certificate schema and conditional soundness argument

The proposed consumer fixes the GIL program, predicate/primitive environment, permitted entries, outcome/property policy and original statement. Rust-to-GIL import remains a named premise unless separately certified. Candidate data contains typed expression/formula ASTs, exact rule IDs, source/target program counters, variable substitutions, resource splits and residuals, plus child references. It does not contain arbitrary executable tactics or a new trusted primitive definition.

A suitable small judgment is `Γ;Σ ⊢ D : {P} code {Q}`, interpreted over the selected concrete GIL/resource semantics. Its rule contracts are:

1. **Pure:** check a proof that the current constraints entail the proposed formula under the fixed expression interpretation. Fresh existential witnesses use checked sorts and capture-free substitution.
2. **Resource entailment:** splits must satisfy the actual separation composition; unfolding uses a fixed predicate equation; folding proves its body; updates use an admitted rule with an adequacy proof. Residual resources remain explicit. Recursive predicates require a justified inductive/guarded interpretation.
3. **Primitive:** apply a checked semantic rule for the exact typed action. Its premises establish access/resource conditions and all represented outcomes; the theorem must not assume the whole original program already safe.
4. **Branch:** retain both guarded continuations, or a proof of infeasibility for an omitted branch. Their disjunction covers the input interpretation. One successful trace or all *returned* engine branches is insufficient.
5. **Call/loop:** calls consume exact callee contracts with implementation/dependency evidence; loops supply initialization, preservation and exit entailments. These rules can establish partial safety/results without claiming termination. Termination additionally needs a rank/progress rule; recursive calls need a simultaneous or guarded composition rule.
6. **Finish:** check the independently required postcondition/outcome and original-subject binding. Missing nodes, cycles without a justified rule, unsupported constructors and operational failures deny ordinary acceptance.

More precisely, require each admitted rule to map every concrete configuration represented by its precondition through every relevant concrete step into a covered child interpretation, while excluding or explicitly classifying bad steps under the fixed policy. Entailment rules preserve the represented resource proposition. Initial interpretation covers the consumer's permitted domain. Induction on finite executions, using checked branch coverage and loop/call closure, then gives the required prefix/result property. This is a researched conditional soundness argument, not an implemented full Gillian checker theorem. It identifies exactly which primitive, logic and translation theorems a production proof must instantiate. Search scheduling, unfolding choice, solver heuristics and recovery tactics can then remain outside acceptance authority.

#### Borrow extraction and prophecy metatheory are explicit rule obligations

The [extended Gillian-Rust paper](https://arxiv.org/pdf/2403.15122v3), §4.4/Appendix C, gives borrow extraction with persistence, a lifetime token and a wand-restoration premise; the prophetic rule additionally needs an injective representation update and current/future equations. The macro [extract_lemmas.rs](https://github.com/GillianPlatform/gillian-rust/blob/83d739e83034d71162fb66b569041cf301123df7/gilogic_proc/src/extract_lemmas.rs#L266) produces the premise proof obligation and a trusted conclusion stub. A replay kernel should register the external rule theorem and check its exact instantiated premises, instead of accepting that stub by name. The paper's §8 explicitly leaves omitted-later and causal-loop/dataflow justification gaps. Rechecking local maps does not close them. An admissible fragment may exclude those features or use a justified deep assertion/dataflow interpretation; claiming arbitrary prophetic adequacy requires that additional theorem.

#### An original checked adapter exercises one real boundary

`support/focused-replay-and-encoding/ProphecyReplay.lean` implements a data-only plan for three selected existing-block operations: consume observer, restore observer, and assign. The independent `Primitive` relation requires the corresponding authority/equality premises. `apply_sound`, `run_sound` and `check_sound` connect executable checking to that relation and a separately defined trace. `trace_frame` preserves the persistent future-value field across every accepted step.

The concrete-valuation model follows these selected source cases: consuming an observer removes its token; restoring it rejects duplication and, when a controller exists, requires equality with the controller's current value; assignment requires both tokens. It excludes missing-block creation, symbolic expression allocation, learned-constraint solving, lifetime/borrow extraction, global causal-loop reasoning and the Rust frontend. Thus it is a small derivation adapter for an actual primitive boundary, not a claim to replay an existing complete Gillian run.

One positive and five negative controls check a consume/restore/assign sequence, assignment without authority, duplicate restoration, mismatched restoration, a wrong initial resource and changed persistent future data. Lean 4.34.1 `5045d0056413266e57c625dcd7c365b10e377c52` exits zero with empty stderr. Main soundness endpoints print only `propext`; the frame theorem prints no axioms. Initial ordinary elaboration errors are preserved and were not accepted proof evidence. This is a separate current-checker observation, not a rewrite of historical 4.31 runs or a universal checker-soundness claim.

The answer to T037 is consequently conditional **yes**: engine-independent replay is feasible when these exact semantic judgments and coverage/policy obligations are checked. The inspected implementation currently uses engine matching, solver decisions and explicitly trusted lemma interfaces; its logs alone are not that independent replay contract. Implementing a complete exporter/checker and instantiating the listed adequacy premises is future engineering. The named causal-loop/later limitations remain explicit applicability boundaries rather than a vague demand to verify all Rust first.

Revalidation: compare the selected engine/primitive/generator branches at the two exact pins; reconstruct the proposed replay judgment before extending its claim. With `LEAN_BINARY` selecting the recorded Lean4.34.1, run `"$LEAN_BINARY" ProphecyReplay.lean` in owned scratch and retain exit/stdout/stderr. Require every positive/negative endpoint and printed assumptions; use a separately identified observation for a changed checker or model.

## Boundaries

- **Known constraints:** prototype language/resource omissions and metatheory simplifications stated above; no operational SB/TB alias model is claimed.
- **Not examined:** every heap primitive/unsafe operation, full predicate-translation correctness, solver dependency closure, external foundational artifacts or exact current Creusot compatibility.
- **Unknown:** a complete Rust source-safety reflection theorem or replayable certificate sufficient to remove the symbolic engine from trust.
- **Execution scope:** Gillian stored tests/expected outputs remain source artifacts; its publication timings were not reproduced. The new owned Lean4.34 adapter is separately executed, not an actual Gillian frontend replay.
- **Integration condition:** ordinary safe callers need the proved semantic/representation interface and linking assumptions. One verified client is not unrestricted unsafe-caller coverage.

## Evidence

`source-evidence.json` binds selected source files to the full commit and Git blob identities. The inspected recursive tree had no `.v` or `.lean` members. Paper version and acquired digest pin its stated formal scope and limitations; its prototype claims are not assigned to a hypothetical future tool. Evidence consists of source/documentation and explicitly derived implications, without fresh Gillian proof checking/execution. The added selected adapter retains its separate Lean4.34 source/log/runtime observation.

## Revalidation

Recheck ProphecyReplay.lean under the identified Lean4.34 pin and compare all six controls/assumptions. Inspect the exact locked engine lemma/matching and Rust observer/controller branches before extending the replay grammar; register primitive/rule interpretation proofs and retain all branch/initial-domain/prophecy metatheory premises.

Pin the Rust compiler, Gillian engine, SMT layer and both specification frontends. Compare emitted client clauses and unsafe ownership/predicate obligations for one concrete API, including its mutable-reference final values and caller restrictions. Retain all trusted extraction/borrow lemmas. Before independent replay, require a complete checked derivation format covering symbolic steps and spatial entailments; before foundational acceptance, close the later/prophecy and source-to-model arguments rather than inferring them from ancestry.


*Authored by an AI agent acting on joshlf's behalf.*
