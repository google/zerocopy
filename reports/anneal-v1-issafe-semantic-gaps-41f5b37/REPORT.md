# Anneal V1 `isSafe`: predicate generation without unsafe-impl enforcement

## Summary

At retained Anneal V1 revision `41f5b37afe7060fd9fe08c00b200672cd76d77b9`, an `isSafe` annotation on an unsafe Rust trait generates a Lean proposition class `Trait.Safe Self inst`. The implementation does **not** connect that proposition to Rust `unsafe impl` declarations, and it does **not** automatically add `Trait.Safe` evidence when a function has a Rust trait bound.

The source therefore implements a useful *explicit logical predicate*, not the end-to-end unsafe-trait contract described in the V1 design document. A proof may rely on `isSafe` only when the specification explicitly asks for `Trait.Safe` evidence, as the checked-in anatomy example does. The existence of a Rust `unsafe impl` by itself supplies no Anneal proof that the implementation satisfies the trait invariant.

This distinction is the central V1 semantic gap: the Lean predicate can express the intended safety condition, but V1 does not automatically establish it at implementation sites or propagate it from Rust trait bounds to consumers.

## Applicability

These findings apply to the retained V1 implementation under `anneal/v1` at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`. They are source-derived. No fresh Anneal, Charon, Aeneas, Lean, or rustc execution was performed.

The report concerns V1's own parsing and Lean-generation path for trait invariants. Rust's underlying unsafe-trait contract is documented separately in the reference corpus, and Charon/Aeneas preservation of trait metadata is a separate boundary. Current Anneal V2 design is out of scope.

## Findings

### `isSafe` creates a proposition indexed by the translated trait dictionary

For an annotated trait, `generate_trait` emits a Lean `Safe` class parameterized by `Self`, the trait's generic parameters, and an explicit translated trait dictionary `inst : Trait Self ...`. The fields of that class are the user-authored `isSafe` clauses.

This is an appropriate representation for a per-implementation safety proposition: distinct trait dictionaries can, in principle, carry distinct safety evidence.

Basis: source.

### V1 has no generated unsafe-impl proof obligation

The parser representation for an annotated `impl` contains only common context. `ImplAnnealBlock::parse_from_attrs` rejects both `isValid` and `isSafe` clauses on impl blocks. More importantly, the generator dispatch ignores `ParsedItem::Impl` entirely.

The source scanner also processes an item only when it contains an Anneal annotation. Thus an ordinary Rust `unsafe impl Trait for Type` without an Anneal block is not turned into an Anneal item at all; an annotated impl can carry only common context, and the generator does not emit that impl item.

Derived consequence: there is no V1 code path in these components that converts a Rust unsafe implementation into a proof obligation or a Lean instance of `Trait.Safe Type trait_dictionary`. The design-document statement that an `unsafe impl` must prove `isSafe` is therefore not implemented by this retained V1 path.

Basis: source + derived.

### A Rust trait bound contributes the trait dictionary, not `Safe` evidence

`extract_generic_params` lowers affirmative Rust trait bounds to explicit Aeneas-style dictionary parameters such as `TraitInst : Trait T`; the dictionary identifier is also threaded into translated calls. It does not add a corresponding `Trait.Safe T TraitInst` parameter or precondition.

The generator's exhaustive trait-bound tests assert the presence of dictionary arguments such as `TraitInst : Trait F`. They do not expect `Safe` evidence. This matches the current agent-facing V1 documentation, which warns that generic functions with the trait bound do not automatically receive the mathematical safety assumption.

This directly contradicts the older design document's stronger claim that a bound such as `T: FromBytes` automatically gives the generated spec an `hSafe` hypothesis.

Basis: source + checked-in tests + documentation comparison.

### The supported V1 pattern is an explicit specification precondition

The checked-in `examples/anatomy.rs` shows the actual consumer pattern. A generic function with `T: Unaligned` explicitly adds

`requires (h_is_safe): Unaligned.Safe T Inst`

and then applies that hypothesis to the Aeneas-supplied `UnalignedInst` dictionary before using the `isSafe` field.

This mechanism is internally coherent: a theorem can demand the safety proposition and use it. But the proposition is now a logical precondition of that theorem. Anneal has not shown that every Rust implementation of `Unaligned` provides it, nor that a Rust trait bound alone implies it.

Basis: source + checked-in example.

### The gap is enforcement, not merely naming

The missing link matters at both sides of the intended unsafe-trait contract:

1. **Implementation side:** Rust permits an `unsafe impl` only because its author asserts the trait's extra safety requirements. V1 does not generate an Anneal theorem that discharges the corresponding `Trait.Safe` proposition for that implementation.
2. **Consumer side:** generic Rust code receives a trait dictionary from `T: Trait`, but V1 does not derive or inject `Trait.Safe T TraitInst`. Consumers that need the invariant must strengthen their Anneal specification with an explicit precondition.

Accordingly, `isSafe` is not a machine-enforced mirror of Rust's unsafe-trait contract in this V1 revision. It is an opt-in proposition that proofs may assume when the surrounding specification explicitly supplies it.

This does not mean Lean proves the invariant from nothing. On the contrary, the explicit-precondition form is conservative: without `Safe` evidence, the proof does not receive the invariant. The unsatisfied goal is *coverage of the Rust contract*: the verification model does not establish that all actual Rust unsafe implementations satisfy the proposition or make that fact automatically available from the Rust trait bound.

Basis: derived from the parser/generator data flow above.

### The checked-in documentation records two incompatible mental models

`docs/design/design.md` says both that unsafe implementations must prove `isSafe` and that generic trait bounds automatically receive an `hSafe` hypothesis. The current agent syntax guide says implementers must prove `isSafe`, but correctly states that generic functions do **not** automatically receive it and must request it explicitly. The anatomy example follows the latter call-site behavior.

For this revision, source behavior should be treated as authoritative over the stronger design prose. Neither documentation variant accurately states the whole implementation: the agent guide matches consumer propagation, but its implementation-site proof claim is not backed by the inspected parser/generator path.

Basis: documentation + source.

## Boundaries

- **Not examined:** no fresh execution was used to demonstrate the gap dynamically. The source path is direct enough to establish the generator behavior, but an execution probe would provide a useful regression specimen.
- **Not examined:** this report does not inventory every possible way a user could manually introduce a `Trait.Safe` theorem or instance in arbitrary Lean context. Such a manual theorem would not, by itself, create the missing automatic connection to the corresponding Rust `unsafe impl`.
- **Separate concern:** correctness of Aeneas trait-dictionary translation is not established here. The report only observes how Anneal V1 consumes the dictionary interface it expects.
- **Separate concern:** the report does not assess V1 `isValid`, `unsafe(axiom)`, lifetime erasure, source-scanner completeness, or current V2 semantics.
- **Known not to follow from this evidence:** a Rust trait bound must not be treated as proof of `Trait.Safe` in V1 merely because the underlying Rust trait is declared `unsafe`.

## Evidence

Primary source was read at immutable `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` on 2026-09-27.

- `anneal/v1/src/generate.rs`, blob `f087023d08011a90d56bcbdc759e6cbc90c344b5`: generator dispatch, `generate_trait`, generic-bound lowering, and trait-bound generator tests.
- `anneal/v1/src/parse/attr.rs`, blob `9f352d511ca964e8c58d24206a3088608cb8aaf6`: `ImplAnnealBlock`, trait parsing, and rejection of `isSafe` on impl blocks.
- `anneal/v1/src/parse/mod.rs`, blob `5f630310199c6abaafa6eee5ea674730bffd773f`: annotation-gated item scanning plus trait/impl visitation.
- `anneal/v1/examples/anatomy.rs`, blob `e77e257b20108989b246d8e9574e14ba11d3cbd6`: explicit `Unaligned.Safe T Inst` consumer precondition and use with `UnalignedInst`.
- `anneal/v1/docs/design/design.md`, blob `f09bf3c9ecd828fb457006853632bc824b1218df`: stronger intended implementation-site and call-site semantics.
- `anneal/v1/docs/agent/04_specifications_and_syntax.md`, blob `1b5a7a8c9f7cc25b6549bc4f2697040c72e14f71`: explicit-precondition call-site guidance and the remaining implementation-site claim.

`source-map.json` records narrow line ranges and the role of each source. `semantic-gap-matrix.json` records the intended-versus-implemented contract in compact form.

## Revalidation

For a later V1 revision, the cheapest source check is to inspect four links:

1. whether impl blocks have gained an `isSafe` proof representation;
2. whether `ParsedItem::Impl` now emits a theorem/instance connecting an Aeneas trait dictionary to `Trait.Safe`;
3. whether generic trait-bound lowering now also introduces `Trait.Safe` evidence; and
4. whether the explicit-precondition anatomy pattern or documentation changed accordingly.

A minimal execution probe can then confirm the source reading: define an annotated unsafe trait with a nontrivial `isSafe`, provide an `unsafe impl` with no Anneal proof, and generate a spec for a generic function bounded by that trait. The discriminating outputs are whether generation rejects the unproved implementation and whether the generic theorem receives `Trait.Safe` without an explicit `requires` clause. Passing only one of those checks does not establish the full intended contract.
