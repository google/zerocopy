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

The selected prophecy serializer emits `Null` and its deserializer reports not implemented. This is evidence about that serializer, not proof that Gillian has no other tracing or certificate facilities. No independently replayable Rust verification derivation or checked certificate language was established by the inspected interfaces. The replay/certificate question therefore has a concrete remaining research gap: find or design a proof-bearing derivation interface and identify which primitive/resource rules its checker validates.

### A hybrid acceptance boundary should share meaning and record assumptions

For Anneal, this architecture answers a design question: a lightweight first-order client contract can be connected to a richer unsafe resource proof through an explicit representation/ownership predicate. The acceptance rule must retain the exact contract translation, permitted callers, linked bodies, model semantics, trusted lemmas and solver assumptions. Current Creusot's own permission facilities may change the practical division of work; the 2025 paper's safe-only comparison should not be carried forward as a current exclusion.

Implementing that boundary, checking it in Lean, or measuring annotation/runtime cost is future engineering/measurement. Research still required includes exact compatibility with current tools and the foundational gaps identified above. These are distinct from reconstructing the existing prototype's exchange mechanism, which this source investigation does establish.

## Boundaries

- **Known constraints:** prototype language/resource omissions and metatheory simplifications stated above; no operational SB/TB alias model is claimed.
- **Not examined:** every heap primitive/unsafe operation, full predicate-translation correctness, solver dependency closure, external foundational artifacts or exact current Creusot compatibility.
- **Unknown:** a complete Rust source-safety reflection theorem or replayable certificate sufficient to remove the symbolic engine from trust.
- **No execution evidence:** stored tests and expected outputs were read as source artifacts only; publication case-study timings were not reproduced.
- **Integration condition:** ordinary safe callers need the proved semantic/representation interface and linking assumptions. One verified client is not unrestricted unsafe-caller coverage.

## Evidence

`source-evidence.json` binds selected source files to the full commit and Git blob identities. The inspected recursive tree had no `.v` or `.lean` members. Paper version and acquired digest pin its stated formal scope and limitations; its prototype claims are not assigned to a hypothetical future tool. Evidence consists of source/documentation and explicitly derived implications, with no fresh proof checking or execution.

## Revalidation

Pin the Rust compiler, Gillian engine, SMT layer and both specification frontends. Compare emitted client clauses and unsafe ownership/predicate obligations for one concrete API, including its mutable-reference final values and caller restrictions. Retain all trusted extraction/borrow lemmas. Before independent replay, require a complete checked derivation format covering symbolic steps and spatial entailments; before foundational acceptance, close the later/prophecy and source-to-model arguments rather than inferring them from ancestry.


*Authored by an AI agent acting on joshlf's behalf.*
