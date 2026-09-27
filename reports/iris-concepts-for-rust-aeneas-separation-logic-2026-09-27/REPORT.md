# Iris concepts needed for current Rust and Aeneas separation-logic work

## Summary

The Iris ideas most useful for reading current Rust/Aeneas separation-logic work fall into three layers that should not be conflated.

At the **spatial-resource layer**, separation-logic propositions describe ownership of resources. Separating conjunction `P ∗ Q` means the owned resource can be split into compatible pieces satisfying `P` and `Q`; points-to assertions connect logical ownership to memory; framing explains why code that touches one owned piece can be reasoned about independently of unrelated owned state. Affinity and persistence then answer two separate questions: may an owned assertion be discarded, and may it be duplicated?

At the **logical-state layer**, Iris generalizes resources beyond physical heaps. Cameras/resource algebras encode compatible composition, validity, splitting, authoritative-versus-fragment views, and ghost protocols. Frame-preserving updates are the admissible changes to ghost state: an update is allowed only when it remains compatible with every possible resource frame held elsewhere. Iris internalizes those updates with update modalities. Invariants and fancy updates add controlled temporary access to shared resources; masks prevent unsound nested reopening. The later modality and step-indexing make guarded recursive predicates, higher-order ghost state, and impredicative invariants sound.

At the **program-logic layer**, Iris defines weakest preconditions in terms of the operational semantics and proves adequacy: an Iris proof must imply an external semantic property of program executions. This bridge is what turns resource bookkeeping into a claim about actual programs. RustBelt then uses Iris as a substrate for a semantic model of Rust types and derives a lifetime logic whose resources include lifetime tokens and several forms of borrow propositions.

The current Aeneas draft in PR #1352 deliberately implements only a much smaller, first-order sequential slice of that conceptual space. Its `IProp` is an affine, upward-closed predicate over a typed slot heap. It has separating conjunction, points-to, an explicit frame-preserving specification discipline, total and partial interaction-tree specifications, and Iris/Iris-Lean-inspired notation and proof-mode names. It does **not** import Iris-Lean or instantiate the full Iris logic. In the inspected exact head, it does not provide Iris cameras, general ghost state, impredicative invariants, fancy-update masks, or the Iris later/step-indexed `iProp` model. The code itself says that the public vocabulary follows Iris-Lean while the implementation is standalone.

That distinction is the main architectural lesson for Anneal. Familiar Iris syntax does not establish Iris semantics, and a Lean theorem about a modeled raw-pointer operation does not establish a Rust-level claim until there is a validated source-to-model mapping and an adequacy/correspondence argument. Conversely, the absence of full Iris machinery is not a defect for the draft's current scope: its direct heap-splitting model is enough to express exclusive points-to resources and frame-preserving sequential heap operations. Full Iris concepts become essential when reasoning about RustBelt-style lifetime abstraction, persistent shared state, higher-order recursive interpretations, concurrency, atomic invariants, or a foundational end-to-end safety theorem.

For Anneal readers, the most useful order is:

1. resource ownership, `∗`, points-to, and framing;
2. affinity versus persistence;
3. frame-preserving updates and frame-preserving program specifications;
4. cameras/resource algebras and authoritative ghost state;
5. invariants, fancy updates, and masks;
6. later/step-indexing and guarded recursion;
7. weakest preconditions and adequacy;
8. RustBelt's lifetime tokens and borrow propositions.

The first three concepts map directly onto the current Aeneas draft. The middle three explain machinery that RustBelt and full Iris need but Aeneas PR #1352 currently avoids. Adequacy is the key boundary Anneal must require before turning any modeled proof into a claim about Rust.

## Applicability

This report is a conceptual reference for Anneal development. It is not an attempt to specify every Iris connective or every RustBelt theorem.

Primary fixed references are:

- **Iris 3.1:** Jung, Krebbers, Jourdan, Bizjak, Birkedal, and Dreyer, *Iris from the Ground Up: A Modular Foundation for Higher-Order Concurrent Separation Logic*, DOI `10.1017/S0956796818000151`.
- **RustBelt:** Jung, Jourdan, Krebbers, and Dreyer, *RustBelt: Securing the Foundations of the Rust Programming Language*, DOI `10.1145/3158154`.
- **Aeneas separation-logic draft:** `AeneasVerif/aeneas` PR #1352 at exact head `75fb1479040d32d43d31b74510167ee3b873d28a`.
- **Iris-Lean existence/status:** `leanprover-community/iris-lean@04b7689c294bb1dd6401e2dd53b337871934ea47`.

The report also relies on the existing Anneal reference package `aeneas-separation-logic-status-2026-09-26` for the current integration status and Rust-source translation boundary. That package establishes that Anneal's selected Aeneas release predates this separation-logic work, that PR #1352 is draft-only, and that the same exact PR head still rejects source-level raw-pointer dereference in Aeneas' symbolic interpreter.

"Iris" below means the conceptual and semantic framework characterized by Iris 3.1 unless a later feature is named explicitly. "Aeneas draft" means PR #1352 at the exact revision above, not current `main`, not Anneal's selected Aeneas release, and not a claim about a future merged design.

## Findings

### Separation logic turns state into owned resources

The first idea to internalize is that a separation-logic assertion is more than a Boolean statement about a global state. It describes a resource the proof owns.

A points-to assertion such as `ℓ ↦ v` therefore carries two pieces of meaning:

- the physical or modeled location contains `v`; and
- the proof has the resource required to use the location according to the logic's rules.

Separating conjunction `P ∗ Q` says that the currently owned resource can be decomposed into compatible parts satisfying `P` and `Q`. This is what makes local reasoning possible: a proof of code operating on the `P` portion can be extended with an unrelated `Q` frame.

This is the conceptual origin of `iframe`. Framing is not just a tactic for clearing matching hypotheses. It reflects a semantic noninterference principle: operations proven against one resource fragment remain valid while compatible resources are held elsewhere.

In the current Aeneas draft, this idea is unusually concrete. `IProp` is a predicate over `Heap`; `sep` existentially splits a heap into compatible fragments; and `Ref.pointsTo` is ownership of a singleton typed heap. The theorem `Ref.pointsTo_exclusive` proves that two points-to assertions for the same slot compose to false. The model therefore gets the central separation property directly from disjoint heap composition rather than from a generic Iris camera.

For Anneal, this is the first useful mental model for unsafe memory proofs: a pointer value and the right to access the pointed-to storage are separate things. The Aeneas raw-pointer draft follows that separation: the pointer identifies an address, while the `↦` assertion carries the permission.

Basis: **Iris foundational paper**, **Aeneas exact source**, and existing Anneal synthesis.

### Affinity and persistence answer different structural questions

Two structural properties recur in Iris and RustBelt discussions.

**Affinity** means a resource may be discarded. If a logic is affine, owning `P` does not force the proof to account for `P` forever. This is distinct from duplication.

**Persistence** means an assertion may be duplicated/reused without consuming a linear resource. Pure facts, facts about ended lifetimes, type relationships, and certain shared-state facts are often persistent.

The current Aeneas draft is explicitly affine. Its `IProp` is upward-closed under `Heap.Sub`; `emp` holds on every heap; and every assertion entails `emp`. Thus resources can be dropped. That does not make points-to duplicable: two copies of the same exclusive points-to assertion are still incompatible.

RustBelt needs both distinctions. For example, a lifetime's full "alive" token is a resource whose fractions are tracked and eventually recovered, while the dead-lifetime token is persistent and can be reused to recover multiple inherited resources. RustBelt's sharing predicates for copyable/shared values are also required to be persistent.

A common reading mistake is to treat "shared" as "duplicable physical ownership." Separation logic instead usually duplicates a *persistent proposition* whose semantics controls access to an underlying resource through another protocol.

Basis: **Aeneas exact source** and **RustBelt**.

### Cameras/resource algebras generalize ownership beyond heaps

Iris does not hard-code the heap as its only resource. It lets clients define logical or ghost resources with an algebra of composition and validity.

In Iris 3.1, cameras are the step-indexed generalization of resource algebras. At a high level they provide:

- a composition operation describing how separately owned pieces combine;
- a validity predicate describing which combined states are legal;
- a core operation representing duplicable/persistent content;
- an inclusion relation for extension/containment; and
- enough step-indexed structure to support higher-order ghost state.

This is how Iris represents protocols that are not literally memory: permissions, tokens, histories, state machines, capabilities, authoritative state, agreement facts, and lifetime bookkeeping.

The most useful recurring pattern is **authoritative plus fragment ownership**. One logical party owns the authoritative view of some abstract state, while clients hold compatible fragments. Validity links the fragments to the authoritative state. Iris uses this pattern even in its ordinary heap program logic: the weakest-precondition machinery owns the authoritative logical heap corresponding to the physical program state, while points-to assertions are fragments.

For Rust verification, this abstraction matters because many safe APIs do not correspond to a simple partition of bytes. A lock, reference count, borrow, lifetime, iterator protocol, or typestate transition often needs logical resources that summarize allowed future behavior rather than just current memory contents.

The Aeneas PR #1352 draft does **not** need cameras for its present first-order heap model. Its heap itself is the separation algebra. That is a deliberate simplification, not evidence that ghost protocols are unnecessary for richer unsafe-Rust reasoning.

Basis: **Iris 3.1** and **derived mapping to the Aeneas draft**.

### Frame-preserving updates explain safe logical state transitions

If different proof components can own compatible pieces of a logical resource, one component must not update its piece in a way that silently invalidates resources owned by others.

Iris captures this with a **frame-preserving update**. An update from logical state `a` to `b` is allowed only if every frame compatible with `a` remains compatible with `b`. Intuitively, the update cannot "step on anybody else's toes."

Iris internalizes these updates using the basic update modality and, with invariants, the fancy update modality. The important conceptual point is more general than the notation: state transitions are permitted because they preserve the validity of all possible disjoint ownership held elsewhere.

The current Aeneas draft encodes a closely related idea at the program-specification level rather than through a generic ghost-state update modality. Its `iwp`/specification layer quantifies over an arbitrary heap frame and requires execution to preserve that frame. The raw-pointer read/write/free proofs explicitly carry a compatible frame through the modeled heap operation.

That resemblance should not be overstated. Aeneas' frame quantification is over its concrete typed heap model. Iris frame-preserving updates range over arbitrary camera resources and can power abstract ghost protocols. Still, the same reasoning principle is visible: an operation's proof must remain valid in the presence of arbitrary compatible state it does not own.

Basis: **Iris 3.1**, **Aeneas exact source**, and existing Anneal report.

### Invariants turn exclusive resources into controlled shared protocols

An Iris invariant packages a proposition that must remain true globally but may be temporarily opened under controlled conditions. This is a standard way to reason about shared mutable state.

The conceptual pattern is:

1. put exclusive resources and a protocol state inside an invariant;
2. give clients a persistent handle naming the invariant;
3. when the logic permits, temporarily open the invariant;
4. perform a permitted state transition; and
5. restore the invariant before leaving the allowed opening scope.

Iris' invariant machinery is impredicative: invariant contents may themselves mention invariants and higher-order propositions. This expressive power is why the logic needs stronger semantic machinery than ordinary first-order heap separation.

RustBelt relies on this style of reasoning for shared and interior-mutable abstractions. Its mutex model, for example, uses a persistent borrow whose invariant has different states depending on whether the lock is held; acquiring/releasing the lock transfers ownership of the protected content through that protocol.

The Aeneas PR #1352 report describes the prototype as first-order and sequential. The inspected core `IProp` is just an upward-closed heap predicate. There is no basis at this exact head for reading `IProp` notation as implying Iris-style impredicative invariants.

For Anneal, invariants become relevant when proving abstractions whose safe API permits aliasing or shared mutation, especially if concurrency is in scope. A points-to-only discipline can prove exclusive-memory routines but cannot by itself express every safe shared protocol.

Basis: **Iris 3.1**, **RustBelt**, and **Aeneas exact-source boundary**.

### Fancy updates and masks make invariant opening compositional

Opening an invariant is dangerous: naively allowing a proof to open the same invariant recursively can duplicate exclusive ownership and make the logic inconsistent.

Iris' **fancy update** modality tracks an invariant mask. The mask represents which invariants are currently enabled. Opening an invariant removes its name from the enabled set; closing it restores that name. Proof rules enforce that the resource borrowed from the invariant is returned before the mask is restored.

The mask is therefore not cosmetic proof-mode state. It is part of the semantic protocol preventing unsound reentrancy.

Fancy updates also subsume frame-preserving ghost updates and connect them to weakest preconditions. They let program proofs combine physical steps, ghost-state transitions, and controlled access to invariants.

This is a full-Iris concept that current Aeneas readers should understand mainly as a **non-feature boundary**: the PR #1352 first-order sequential logic does not become a concurrent Iris-style logic merely because it uses `IProp`, `∗`, `↦`, and `iframe` notation.

Basis: **Iris 3.1**.

### The later modality and step-indexing make circular semantic definitions sound

Rust's type semantics is recursively structured. Types may contain pointers to values whose types recursively mention other types; higher-order mutable state and impredicative invariants create similar semantic cycles.

Iris handles this with step-indexing and the **later** modality `▷`. Guarded recursive definitions may refer to themselves only below a later. Informally, `▷ P` says that `P` holds one logical step later; semantically, the guard breaks circular definitions by decreasing the step index.

The later is also essential to Iris' invariant soundness. Iris 3.1 shows that giving unrestricted immediate access to impredicative invariant contents would be inconsistent; invariant access therefore exposes the resource under a later, with "timeless" propositions providing important escape hatches.

RustBelt explicitly relies on guarded recursion. Its semantic type interpretations are Iris predicates, and the paper notes that recursive references must be guarded by later or another suitable guard. Later modalities appear in the ownership/sharing interpretation and in the lifetime logic.

Aeneas PR #1352 should not be mentally upgraded to this model. Its `IProp` is a first-order predicate over a typed heap. The fact that the draft's program-result semantics uses coinductive interaction trees is a different construction from Iris' step-indexed `iProp` and later modality.

This distinction matters for future Anneal design. A recursive proof object in Lean, a coinductive execution tree, and a step-indexed separation-logic proposition solve different problems.

Basis: **Iris 3.1**, **RustBelt**, and **Aeneas exact-source comparison**.

### Weakest precondition is where logical resources meet program execution

Iris defines a weakest-precondition connective `wp e {Φ}` rather than taking Hoare triples as primitive. At a high level, the weakest precondition states enough to ensure that `e` executes safely and, if it returns a value, that the result satisfies `Φ`.

The implementation of Iris' weakest precondition ties together:

- the language's operational semantics;
- the physical machine/program state;
- an authoritative logical representation of that state;
- the resources owned by the current proof;
- spawned-thread obligations; and
- admissible logical updates.

Hoare triples are then defined from weakest preconditions.

This architecture gives a useful checklist for Anneal. A separation-logic notation is not enough. To support a claim about Rust execution, one needs a program judgment connected to the relevant semantics and a proof that the judgment means what it is supposed to mean.

The Aeneas draft has its own specification judgments over its `Result` interaction tree and heap handler. Those can be strong and useful internal specifications. They are not automatically the same as Iris `wp`, and their adequacy target is the modeled Aeneas execution, not source Rust unless a separate translation/correspondence result closes the gap.

Basis: **Iris 3.1**, **Aeneas exact source**, and **derived Anneal criterion**.

### Adequacy is the theorem that turns a proof system into an external semantic claim

Iris 3.1 proves adequacy for weakest preconditions: if the logic proves an appropriate weakest precondition, then concrete executions satisfy the corresponding safety/postcondition statement.

This is the most important concept for Anneal to retain from Iris even if Anneal never embeds full Iris.

Without adequacy, one can prove theorems inside a beautifully designed model while remaining uncertain whether the model matches the execution whose safety matters. Adequacy need not always be one monolithic theorem; a trustworthy architecture can compose several justified correspondences. But some chain must connect:

`Rust source` → `rustc/Charon representation` → `Aeneas translation` → `Lean model/specification` → `proved property`

Each arrow needs a stated trust or proof boundary. The existing Aeneas separation-logic report identifies a concrete current break in that chain: PR #1352 supplies Lean raw-pointer operations and proofs, while the same exact Aeneas translator still rejects source-level raw-pointer dereference.

Therefore "there is a theorem for `RawPtr.read`" and "Anneal proved this Rust raw-pointer dereference safe" are categorically different claims.

Basis: **Iris 3.1 adequacy theorem**, **Aeneas exact source**, and existing Anneal report.

### RustBelt uses Iris to define semantic Rust types, not merely to prove functions locally

RustBelt's central move is semantic type soundness. A Rust type is interpreted by Iris propositions describing what it means to own values of the type and, separately, what it means for values to be safely shared.

This makes Iris ownership part of the semantic meaning of Rust types. Unsafe library implementations can then be shown to satisfy the semantic contract required by their safe API, even though they cannot be justified by the safe syntactic typing rules alone.

This is why RustBelt needs more than a heap-splitting Hoare logic. Its semantics must talk about:

- temporary ownership;
- shared/persistent access;
- higher-order values;
- recursive type interpretations;
- thread transfer;
- interior mutability; and
- extension of the language by unsafe libraries.

For Anneal, RustBelt is best read as a model of the *kind of semantic obligation* required at safe/unsafe abstraction boundaries, not as a drop-in proof library for Aeneas.

Basis: **RustBelt**.

### Lifetime tokens and borrow propositions are derived logical resources

RustBelt builds a custom **lifetime logic** inside Iris.

A full borrow of proposition `P` at lifetime `κ` represents temporary ownership of `P` until `κ` ends. A lifetime token witnesses that a lifetime is still alive. The token can be fractionally split so several simultaneous proofs can witness that the same lifetime remains active.

The protocol forces proofs to close outstanding borrows before the lifetime can end. When the full alive token is consumed to end the lifetime, a persistent dead-lifetime token is produced. That persistent evidence can then be reused to recover resources whose restoration was delayed until the lifetime ended.

Lifetime inclusion is also represented semantically. Intuitively, if a shorter lifetime is alive, then the longer lifetime containing it must be alive; if the longer has ended, the shorter must have ended. RustBelt expresses this through transformations on lifetime tokens, wrapped in a persistent assertion.

This is a concrete example of why ghost resources matter for Rust. A lifetime is not a physical heap cell, but proofs need linear/fractional tokens and state transitions that mirror the language's borrowing discipline.

The current Aeneas separation-logic draft does not thereby inherit RustBelt's lifetime logic. Similar notation or points-to assertions cannot substitute for these derived protocols. A future Aeneas/Anneal memory model that wants RustBelt-like semantic borrowing must state how its own borrow/lifetime semantics corresponds.

Basis: **RustBelt**.

### Persistent borrows show how Rust sharing depends on access protocol

RustBelt derives different forms of borrow for different sharing needs.

A fractured borrow is persistent but grants only fractional access, which suffices for ordinary read-only sharing. A non-atomic persistent borrow can grant full access, but only to a proof carrying a thread-local token, preventing simultaneous access from two threads. Atomic persistent borrows restrict opening to an atomic step and are used for thread-safe shared state such as mutexes.

This is a useful design pattern for Anneal even if the exact RustBelt construction is not reused: "shared reference" is not one universal permission. The semantic permission depends on the type's safe API and the interference protocol.

It also explains why `UnsafeCell`, atomics, locks, and plain shared references cannot all be reduced to the same raw points-to rule.

Basis: **RustBelt**.

### Aeneas' current prototype intentionally stops before full Iris

The exact PR #1352 source is unusually explicit about its relationship to Iris.

`Aeneas.SepLogic.Basic` calls itself an "Iris-compatible first-order separation logic." It says the public vocabulary follows Iris-Lean but that it deliberately does not import Iris-Lean or instantiate Iris-Lean with the Aeneas model. Its `IProp` is a structure containing a `Heap → Prop` predicate plus closure under heap extension.

The consequences are concrete:

- separating conjunction is literal compatible heap splitting;
- points-to is literal ownership of a singleton typed heap;
- affinity comes from upward closure;
- proofs use ordinary Lean propositions, not Iris' step-indexed proposition model;
- there is no generic camera parameter underlying `IProp`;
- there is no general Iris invariant/fancy-update/later infrastructure implied by the notation.

That smaller model is sufficient for the draft's direct sequential heap examples. Its `Result` effects mutate the typed heap under a guarded operation, and its specification layer proves that framed resources survive. For allocation/read/write/free routines, this gives an intelligible and checkable spatial contract without importing the semantic weight of full Iris.

The right comparison is therefore "Aeneas borrows a useful spatial vocabulary and proof discipline from Iris" rather than "Aeneas has implemented Iris."

Basis: **Aeneas exact source**.

### Iris-Lean exists, but its existence does not change the Aeneas boundary

At `leanprover-community/iris-lean@04b7689c294bb1dd6401e2dd53b337871934ea47`, the project describes itself as a Lean 4 port of Iris and reports support for MoSeL, `IProp`, HeapLang, invariants, later credits, and other Iris resources.

This matters because a future Lean-based Anneal/Aeneas design has at least two architectural options:

- maintain a purpose-built first-order spatial logic, as PR #1352 currently does; or
- use/instantiate a fuller Iris implementation in Lean where its additional machinery is justified.

The current draft has chosen the former. Its source explicitly says clients could switch implementations while keeping surface vocabulary, but no such substitution should be assumed to preserve semantics automatically. The proof obligations, model assumptions, adequacy theorem, and feature set would have to be re-established for the chosen implementation.

Basis: **Iris-Lean exact README** and **Aeneas exact source**.

### A practical concept map for Anneal

For reading current code and papers, the following mapping is useful:

| Concept | Full Iris/RustBelt role | Current Aeneas PR #1352 analogue | Anneal relevance |
| --- | --- | --- | --- |
| Ownership / `∗` / points-to | local resource ownership and disjoint composition | direct typed-heap split and singleton ownership | immediate |
| Affinity | resources may be discarded | built into upward-closed `IProp` | immediate |
| Persistence | duplicable assertions | ordinary Lean facts plus no full Iris persistence modality in the inspected core | important for shared abstractions |
| Frame rule | unrelated owned resources survive local reasoning | explicit frame quantification/spec lemmas | immediate |
| Cameras / resource algebras | arbitrary physical and ghost resource protocols | no generic camera layer; heap is the separation algebra | future richer protocols |
| Authoritative/fragments | connect canonical abstract state with client fragments | no generic counterpart | useful for stateful abstractions/adequacy |
| Frame-preserving update | change logical state without invalidating others' frames | concrete framed heap transitions | immediate principle, narrower implementation |
| Invariants | persistent handles to temporarily accessible shared resources | no full Iris invariant layer | required for shared/concurrent protocols |
| Fancy updates / masks | controlled invariant opening and ghost updates | no counterpart | required with Iris-style invariants |
| Later / step-indexing | guarded recursion, higher-order ghost state, invariant soundness | no Iris step-indexed `IProp`; coinductive execution is distinct | needed for RustBelt-style semantic recursion |
| Weakest precondition | program judgment tied to operational semantics | custom ITree `ispec`/`dispec` judgments | immediate architectural comparison |
| Adequacy | proof implies external execution property | requires separate Aeneas/Rust correspondence story | critical |
| Lifetime logic | semantic Rust borrowing via tokens/borrows | not inherited from notation | critical for Rust-level borrow semantics |
| Proof mode | tactics manipulate spatial contexts | `iframe`/`iintro`/`irewrite` inspired by Iris vocabulary | ergonomic, not semantic evidence |

This table should be treated as an architectural map, not a claim of formal equivalence.

## Boundaries

**This is not an Iris specification.** Iris has many additional connectives, resource constructions, proof-mode details, and later developments. The report selects concepts needed to understand the current Rust/Aeneas work.

**Iris 3.1 is a conceptual baseline, not the latest release.** It was selected because it gives a coherent published account of cameras, updates, invariants, weakest preconditions, step-indexing, and adequacy. Later Iris versions add or refine facilities such as later credits. Revalidate version-specific implementation claims against the current technical reference when needed.

**Aeneas PR #1352 is a moving draft.** Claims here are pinned to `75fb1479040d32d43d31b74510167ee3b873d28a`. The upstream branch may have changed.

**No claim that Aeneas' `IProp` is semantically equivalent to Iris' `iProp`.** It intentionally shares vocabulary while using a simpler first-order heap-predicate implementation.

**No claim that Aeneas' coinductive interaction trees replace Iris step-indexing.** They address different semantic problems.

**No claim that Iris-Lean is suitable for Anneal without evaluation.** The exact README establishes existence and broad feature support. Performance, version compatibility, trust, proof ergonomics, and integration with Aeneas remain separate questions.

**No fresh execution.** No Rocq/Iris, Lean/Iris-Lean, Aeneas, Charon, or Anneal build was run.

**RustBelt is not full current Rust.** Its λRust model deliberately abstracts from parts of production Rust, and later work extends several boundaries. The report uses RustBelt to explain the semantic role of Iris concepts, not to claim a complete Rust semantics.

**Concurrency is outside the current Aeneas draft claim.** Full Iris invariants and concurrent reasoning should not be inferred from PR #1352's spatial notation.

**End-to-end adequacy remains separate.** The current Aeneas draft's Lean model is not by itself evidence that arbitrary source-level unsafe Rust is translated into that model. Existing Anneal reference work records the raw-pointer-translation gap.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

### Iris 3.1

Primary publication:

- Ralf Jung, Robbert Krebbers, Jacques-Henri Jourdan, Aleš Bizjak, Lars Birkedal, Derek Dreyer, *Iris from the Ground Up: A Modular Foundation for Higher-Order Concurrent Separation Logic*, Journal of Functional Programming 28:e20, DOI `10.1017/S0956796818000151`.
- The Iris project site identifies this paper as the extensive description of the rules and model of Iris.

High-signal sections used:

- introduction and separation-logic ownership;
- resource algebras/cameras and validity;
- frame-preserving updates and update modalities;
- weakest-precondition construction;
- adequacy of weakest preconditions;
- fancy updates and invariant masks;
- later modality, guarded recursion, and the impredicative-invariant paradox.

Evidence role: **published semantics**.

### RustBelt

Primary publication:

- Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer, *RustBelt: Securing the Foundations of the Rust Programming Language*, POPL 2018, DOI `10.1145/3158154`.

High-signal sections used:

- motivation for Iris as an ownership logic with higher-order ghost state and impredicative invariants;
- semantic ownership and sharing predicates for Rust types;
- guarded recursion and later;
- lifetime logic;
- full/fractured/persistent borrows;
- lifetime tokens, lifetime end, and inclusion;
- `Cell`/mutex examples showing different access protocols for shared state.

Evidence role: **published Rust semantic model**.

### Aeneas draft separation logic

Exact repository subject:

- `AeneasVerif/aeneas` PR #1352 head `75fb1479040d32d43d31b74510167ee3b873d28a`.

Key exact files:

- `backends/lean/Aeneas/SepLogic/Basic.lean`, blob `5b50eb4a1532251386955d754bb5d711600d384b`: standalone first-order `IProp`, affine upward closure, separating conjunction, points-to, exclusivity, explicit statement that it does not import/instantiate Iris-Lean.
- `backends/lean/Aeneas/Std/Heap.lean`, blob `d635192c03e4b49ab57f6581e4f93a2a17ed265c`: typed slot heap and disjoint composition.
- `backends/lean/Aeneas/Std/WP.lean`, blob `134d8b9f7dfb24e8afdefd730cae547ba540d2ce`: frame-quantified `iwp`, total/partial separation specifications, frame/monotonicity/bind integration.
- `backends/lean/Aeneas/Std/RawPtr.lean`, blob `33e3dc4b7c06c9b7c46703ec19199d991d023ed1`: pointer operations and points-to specifications.
- existing native reference package `reports/aeneas-separation-logic-status-2026-09-26`, report blob `f085a0657973482693efa5d1e661881525c9911d`: integration status and the continuing source-translation gap.

Evidence role: **exact source** plus **existing corpus synthesis**.

### Iris-Lean

Exact observed repository state:

- `leanprover-community/iris-lean@04b7689c294bb1dd6401e2dd53b337871934ea47`.
- `readme.md`, blob `79dc0231e655921cfeed3d7156299226c6bed54b`: identifies the project as a Lean 4 port of Iris and lists support for MoSeL, `IProp`, HeapLang, invariants, later credits, and additional resources.

Evidence role: **exact project documentation**.

## Revalidation

For the conceptual core, revalidation should distinguish *published Iris semantics* from *current implementation state*.

To refresh Iris itself:

1. read the current Iris project technical reference and current formalization version;
2. confirm the current names/rules for resources, update modalities, invariants, weakest preconditions, adequacy, and later;
3. record later-version changes rather than silently projecting Iris 3.1 implementation details forward.

To refresh Rust relevance:

1. identify which RustBelt/RustHornBelt/RefinedRust-style semantic layer the proposed Anneal design actually wants;
2. record whether lifetime/borrow reasoning is inherited, reimplemented, or deliberately out of scope;
3. separate sequential unsafe-memory reasoning from concurrency and relaxed-memory reasoning.

To refresh Aeneas:

1. resolve the current separation-logic branch or merged revision;
2. inspect `SepLogic/Basic.lean` to see whether `IProp` remains a first-order heap predicate or now uses Iris-Lean/full Iris machinery;
3. inspect `Std/WP.lean` and the effect semantics to identify the exact frame and adequacy story;
4. inspect the Rust/LLBC translator for raw-pointer and unsafe-memory support;
5. inspect the root imports and Lake dependencies for an actual Iris-Lean dependency rather than inferring one from notation;
6. rerun the existing end-to-end discriminator: translate a small Rust raw-pointer read/write program and preserve Rust, LLBC, generated Lean, proof, and execution/elaboration artifacts.

For an Anneal architecture review, ask four explicit questions:

1. **What is the owned resource?** Bytes, typed slots, abstract protocol state, or a product of several resources?
2. **What transitions are legal?** Are they justified by frame preservation against arbitrary compatible ownership?
3. **What sharing protocol exists?** Exclusive points-to, persistent invariant, lifetime borrow, atomic protocol, or another abstraction?
4. **What is the adequacy chain?** Which theorem or trusted boundary connects the final Lean proposition to the Rust execution property Anneal claims?

If any answer is "the syntax looks like Iris," the architecture has not yet supplied the semantic argument.
