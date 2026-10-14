# GAT families, coinductive markers, and selected implementation evidence

## Summary

A generic associated type denotes a family indexed by its own parameters. A proof about one normalized associated type or one compiled method is not automatically a proof about that family. Rust's special coinductive auto-trait resolution does not supply arbitrary unsafe-trait laws. Specialization makes the final selected item and its substitutions part of the evidence interface.

## Applicability

This report compares the pinned Rust Reference, compiler and development-guide source, selected trait translation in the RefinedRust 2026 artifact, and three original compiler controls. These are distinct subjects. The compiler controls used Rust 1.101.0-nightly at `1d81eb4ad9cd207e3e638bd32b17ec4fce8412a6`, edition 2024, optimization level 1, on `aarch64-apple-darwin`. The successful control enables `min_specialization`; it does not establish stable specialization support. The current compiler source inspected at `f6c1107f8be13e48465e12c0fd26e6a39fe18e4f` is a separate, later snapshot.

## Findings

### F1. A GAT contract is a conditional family law

Basis: normative + derived.

The Reference permits associated-type parameters and where clauses. Its lending example declares `Lender<'a> where Self: 'a`; an implementation supplies the corresponding family at each permitted lifetime. `<T as Trait>::Assoc<'a>` uses the selected implementation with that lifetime substituted. Associated-type bounds constrain implementations, while a trait's method declaration constrains the method signature. Neither declaration itself establishes a user-defined safety invariant.

A feasible semantic dictionary therefore contains an interpretation `Assoc(T, args)`, its type-validity/ownership laws under the declared where predicates, and the method contract quantified over the same arguments. For borrowing families, that contract must preserve the relevant lifetime token, access authority, and restoration condition. An equality at one lifetime is insufficient to justify a function quantified over all permitted lifetimes. Additional variance or lifetime-monotonicity laws should be required only when the consumer actually uses them; GAT syntax does not assert arbitrary monotonicity.

The successful `lend<'a, F: Family>` compiler control borrows a four-byte `Buffer` through its `Borrow<'a> = &'a [u8]` implementation. This is a particular generic declaration with one exercised implementation, not universal semantic verification.

### F2. Coinduction for auto traits is not a cyclic proof of arbitrary contracts

Basis: documentation + source + execution + derived.

The pinned unstable-book description permits cyclic matching for auto traits and forbids their methods, associated items, and supertraits. The development guide describes current coinductive goals as auto traits, `Sized`, and well-formedness, with ordinary inductive cycles yielding overflow; its broader future intention is not a current rule. In `consider_auto_trait_candidate`, the next solver considers positive goals, checks possible explicit implementations first, and checks structural constituents. It also treats opaque types and their defining scopes specially. Structural inference is not a blanket default when an explicit implementation could apply.

The recursive `Link { next: Option<Box<Link>> }` satisfies the observed compiler's `Send` requirement. The separate ordinary-trait self-cycle is rejected with E0275. This discriminates the two compiler treatments; it does not identify which solver mode every language feature uses.

A semantic unsafe-trait proof must instead justify the laws of its dictionary and any recursive dependency. A circular assumption that the desired law holds is not made sound by the compiler's successful marker-trait cycle. Where a semantic interpretation genuinely needs coinduction, its guardedness/fixed-point argument belongs to that interpretation, independently of Rust trait resolution.

### F3. Default bodies, blanket implementations, and specialization select different evidence

Basis: normative + documentation + source + execution.

A default trait method body applies when the implementation does not replace it. A blanket implementation is a separate implementation over its parameters. The Reference's coherence/orphan rules constrain legal implementations, but do not prove their semantic contracts. Nightly specialization permits an ordered family of overlapping implementations; the development guide distinguishes the most specialized implementation currently known to apply from the final code-generation choice when inference variables remain. Associated-type projection is consequently restricted when a default can still be overridden.

The control gives a trait default body returning 1, a blanket implementation with a default method returning 2, and a specialized `u8` implementation returning 3. A generic caller prints `selected_u8=3 selected_u16=2`. Substituting the trait default's specification for either selected body would describe the wrong code.

RefinedRust's inspected `resolve_assoc_item` uses compiler implementation resolution and specialization ancestors' `leaf_def`. When the leaf is not final and the trait reference remains further specializable, it retains the original item and substitutions; otherwise it rebases/translates arguments to the selected defining node. A nearby FIXME about bypassing implementation resolution is in commented code, not the active path. The active builtin branch examined handles closures and contains an `unimplemented!()` fallback for other cases; no control here executed that branch.

### F4. The framework interface has useful laws but no measured GAT acceptance here

Basis: source + derived.

In the selected RefinedRust artifact, trait specifications have named associated-type entries and method specifications. `make_semantic_decl` emits an optional user semantic interpretation, quantified over refinement/type parameters and trait lifetimes, as a proposition. Separate method and specification-subsumption obligations supply the bridge from an implementation to an abstract contract. These are useful modular interfaces; optional emission of a semantic declaration is not automatic proof of its contents.

The inspected associated-type lookup takes an item ID and selects a literal parameter or `make_assoc_type_use` by associated-item index. That method supplies a constrained type or a literal parameter. This narrow interface does not exhibit a full representation of an associated item's own lifetime/type/const arguments. It does not establish that all other frontend paths lack such support. A GAT translation acceptance test and its generated family law remain unexamined; lack of a search hit is not an unsupported-feature verdict.

### F5. Dynamic and open-client closure must preserve the callable environment

Basis: normative + execution + derived.

The Reference's dyn-compatibility rules exclude associated types with generics. `gat_dyn_rejected.rs` receives E0038 for exactly that case. A GAT generic contract therefore cannot be repackaged as that ordinary trait object under this rule.

For a permitted object or callback interface, a feasible certificate separately binds the concrete callable identity, environment ownership/lifetime, substituted signature, and semantic contract. For a statically selected generic method, it binds the trait/item ID, implementation ID, substitutions, associated-family equations, and the proven method/unsafe-trait laws. Downstream implementation closure can be conditional on supplying those laws at each implementation boundary; it need not enumerate every future crate. Conversely, a finite set of monomorphized tests does not prove that conditional universal theorem. This report does not measure vtable or closure translation acceptance.

## Boundaries

The Reference explicitly leaves some unsafe semantics unresolved; compiler type checking is not a complete unsafe-code soundness theorem. The source comparison answers the mechanism and certificate-design questions for GATs, marker coinduction, and selected implementation identities. RefinedRust acceptance/generated obligations for a GAT family remain an actual research gap. Full arbitrary downstream-client closure is a future proof/engineering obligation, not a prerequisite for the mechanism comparison. Const-generic family acceptance, recursive semantic unsafe-trait proofs, higher-ranked callback extraction, and dynamic-dispatch proof execution were not tested here. No general RefinedRust GAT or specialization unsupported claim follows.

## Evidence

All observations were acquired on 2026-10-14. Original inputs and exact status/output are preserved as `generics.rs`, `gat_dyn_rejected.rs`, `ordinary_cycle_rejected.rs`, and `execution.json`.

- [Rust Reference](https://github.com/rust-lang/reference/tree/2dafab96d919d6ab2884488e970bf95610ff83eb): `src/items/associated-items.md`, associated-type declaration/definition and lending family (lines 200–300); `src/items/traits.md`, default bodies, dyn compatibility, unsafe traits; `src/items/implementations.md`, coherence and orphan rules; `src/special-types-and-traits.md`, automatic and negative auto-trait implementations.
- [Compiler source](https://github.com/rust-lang/rust/blob/f6c1107f8be13e48465e12c0fd26e6a39fe18e4f/compiler/rustc_next_trait_solver/src/solve/trait_goals.rs): `consider_auto_trait_candidate`, lines 206 onward; matching unstable-book `auto-traits.md`, automatic implementations and coinduction.
- [Development guide](https://github.com/rust-lang/rustc-dev-guide/tree/bfbca953b5d4a3596081360a1c79ad88f31e7d60): `src/solve/coinduction.md`, current goal classes versus future work; `src/traits/specialization.md`, selection and associated-type normalization.
- [RefinedRust artifact](https://zenodo.org/records/21636474), `artifact.tar.gz`, SHA-256 in metadata. Selected paths and SHA-256 identities are in `trait-source-identities.json`: `traits/registry.rs:get_associated_type_use` lines 146–167, `traits/resolution.rs:resolve_assoc_item` lines 281–336, and Radium `specs/traits.rs:make_assoc_type_use` lines 453–461 and `make_semantic_decl` lines 1029–1055. Upstream source retains authority; the package does not mirror it.

## Revalidation

Compile the three preserved controls with an explicitly selected existing compiler and record its full `-vV` identity and statuses. Confirm the family borrow succeeds, ordinary cycle and GAT trait object fail for the intended reasons, and selected generic calls return 3 and 2. Reinspect auto-trait candidate guards and final associated-item resolution on changed compiler/framework snapshots. To resolve the framework GAT gap, use one lending family with its own lifetime parameter, inspect the generated family interpretation/where premises, and check the resulting proof obligations; successful Rust compilation alone does not answer it.

*Authored by an AI agent acting on joshlf's behalf.*
