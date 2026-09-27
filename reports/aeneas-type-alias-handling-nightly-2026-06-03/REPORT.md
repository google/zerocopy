# Aeneas type-alias handling at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, ordinary Rust type aliases do not become Lean type aliases. The paired Charon revision, `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, preserves each selected alias declaration as a top-level `TypeDeclKind::Alias(Ty)`, but Rust/rustc has already made uses of an ordinary alias transparent: Charon's own AST documentation says alias declarations appear only in the top-level item list because rustc inlines alias uses elsewhere. Aeneas then deliberately removes those top-level alias declarations before concrete interpretation, borrow checking, or Rust-to-Lean translation.

The Aeneas boundary is explicit. `PrePasses.filter_type_aliases` deletes every `Alias` entry from `crate.type_decls` and removes the corresponding nonrecursive type declaration group from `crate.declarations`. Later type analysis and pure-type translation treat a surviving alias as an internal error: both say that type aliases "should have been removed earlier." Aeneas therefore relies on Charon's transparent-use representation instead of carrying an alias identity through its semantic translation.

Preserved generated Lean artifacts show the consequence. `tests/src/mini_tree.rs` defines `type OptNode = Option<Box<Node>>`; `tests/lean/MiniTree.lean` contains no `OptNode` declaration and represents the relevant fields directly as `Option Node` after Aeneas also erases `Box`. `tests/src/hashmap.rs` defines `Key = usize` and `Hash = usize`; the generated `Hashmap/Types.lean` has no `Key` or `Hash` declaration and uses `Std.Usize` directly where those aliases appeared in Rust.

Charon still does useful work on alias declarations before Aeneas drops them. It translates the alias right-hand side, retains the alias's generics and item metadata, adds missing trait clauses needed by associated-type uses, and can lift associated types in aliases. Checked-in Charon LLBC fixtures preserve this top-level alias form. Those facts matter for Charon-facing source correspondence, but they do not survive as alias declarations in Aeneas's pure AST or generated Lean.

For Anneal, the practical boundary is clear: if proofs or diagnostics need the programmer's ordinary alias name, alias declaration span, alias-specific generic/bound spelling, or an alias chain, that information must be preserved before Aeneas's pre-pass or recovered independently from Rust/Charon source metadata. It cannot be reconstructed from the generated Lean type alone in general. The semantic type remains available through the inlined underlying type.

No fresh Charon, Aeneas, Lean, or rustc execution was performed. The report uses exact pinned source plus checked-in Charon and Aeneas generated artifacts. Those artifacts are preserved upstream execution evidence, not execution performed on this surface.

## Applicability

- Aeneas: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, release `nightly-2026.06.03`.
- Paired Charon: `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, version `0.1.210`.
- Anneal context: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`; current Anneal selects this Aeneas release.

This report uses **ordinary type alias** for a free Rust alias such as `type Bytes<'a> = &'a [u8]`. It does not use that term for a trait associated type, a trait alias, or an opaque type produced by `impl Trait` syntax. Those constructs share some Rust syntax or compiler terminology but have different semantic and translation paths.

The companion corpus report `rust-type-alias-lowering-nightly-2026-05-31` establishes the upstream Rust/rustc boundary: ordinary aliases retain declaration identity in frontend representations but normally lower to the instantiated underlying semantic type. This report begins at the Charon/Aeneas boundary and establishes what additional alias information is retained or discarded there.

## Findings

### Charon preserves the alias declaration but not alias use-site type identity

The pinned Charon AST contains `TypeDeclKind::Alias(Ty)`. Its documentation is unusually direct: an alias appears only in the top-level list of items because rustc inlines uses of type aliases everywhere else.

That gives Charon two different views of the same source construct:

- the alias declaration remains a named item with `ItemMeta`, generics, source span, and a translated right-hand-side type;
- a field, local, function signature, or other type use generally carries the underlying semantic type rather than a reference to that alias declaration.

This is consistent with the pinned rustc report in this corpus. A Charon consumer can inspect the declaration item to learn that the source alias existed, but it cannot infer an arbitrary source alias spelling from a use-site `Ty` after that spelling has been normalized away.

Basis: pinned Charon **source** plus the companion rustc **source** report.

### Charon translates selected aliases as first-class top-level type declarations

`translate_items.rs` handles `FullDefKind::TyAlias` explicitly. For a visible alias it translates the alias body with `translate_ty` and stores the result as `TypeDeclKind::Alias`. The resulting `TypeDecl` also carries the alias item's translated generics and metadata.

This is not merely a dormant AST variant. The checked-in `issue-395-failed-to-normalize.out` fixture contains two emitted aliases:

- `Alias<T> = Option<<T as Trait>::AssocType>` becomes a top-level `pub type Alias<T> ... = Option<...>` declaration in final LLBC;
- `S2<I, F> = S<I, F>` becomes a second top-level `pub type S2<I,F> ... = S<I,F>` declaration.

The alias declaration therefore remains available at Charon's serialized output boundary when selected for extraction.

Basis: pinned Charon **source** + preserved Charon **execution** artifact.

### Charon repairs alias-specific trait-clause gaps before serialization

Rust permits ordinary type aliases to mention associated types without requiring all corresponding trait bounds to be written on the alias. Charon's `add_missing_alias_clauses` pass exists specifically for that mismatch. Its module comment says that when an alias contains a projection such as `<T as Trait>::Assoc` without a `T: Trait` clause, translation may otherwise leave an unknown trait reference.

The pass visits every `TypeDeclKind::Alias`, extracts such trait references from the alias type, adds clauses to the alias generic parameters, and rewrites those references to clause-based proofs. The transformation pipeline runs this pass before associated-type expansion.

This means the final LLBC alias declaration can contain inferred proof/bound structure that was not written literally in the Rust alias declaration. That structure is Charon's semantic repair for its own representation; it should not be mistaken for exact source syntax.

Basis: pinned Charon **source**.

### Associated-type lifting can rewrite the alias declaration before Aeneas sees it

The pinned Charon pipeline also runs `expand_associated_types`. Its implementation tracks whether the current item is a type alias because alias bounds have special failure behavior: Rust allows aliases to use unproved trait facts, and Charon may report that the programmer must add the relevant bound if it cannot compute an associated type.

The preserved `lift-assoc-ty-in-alias` fixture shows a successful case. Rust source defines:

`type Alias<B> = <B as HasAssoc>::Assoc`.

With associated-type lifting enabled, final LLBC contains an alias parameterized by a new lifted type parameter and a trait clause, with the alias body reduced to that lifted parameter. The alias item survives, but its final LLBC form is a semantic normalization rather than a verbatim rendering of the Rust declaration.

This distinction matters when using alias declarations for source correspondence: Charon preserves the item identity and span, but its type/generic structure may already reflect transformations.

Basis: pinned Charon **source** + preserved Charon **execution** artifact.

### Aeneas removes all ordinary alias declarations in a crate-wide pre-pass

Aeneas's `PrePasses.filter_type_aliases` identifies every `type_decl` whose kind is `Alias`. It then performs two changes together:

1. filters those entries out of `crate.type_decls`;
2. removes the corresponding `TypeGroup (NonRecGroup id)` entries from `crate.declarations`.

The same code treats an alias in a recursive type group as unexpected and raises an error rather than silently filtering it. Ordinary aliases are expected to be standalone declaration groups.

The filter does not replace type occurrences with the alias body. It does not need to: the Charon representation already contains underlying types at ordinary use sites. Aeneas is deleting the now-unneeded top-level declaration, not performing source-level textual alias expansion itself.

Basis: pinned Aeneas **source**, `src/PrePasses.ml`.

### Alias removal happens before interpretation, borrow checking, and Lean translation

The Aeneas driver loads the LLBC crate and then calls `Aeneas.PrePasses.apply_passes`. Only after those passes does it either run concrete-interpreter tests, borrow-check the crate, or call `Aeneas.Translate.translate_crate` for extraction.

Inside `apply_passes`, `filter_type_aliases` runs after per-function pre-passes and before the returned crate is handed to those later stages. Alias declarations are therefore absent from the crate consumed by Aeneas's main semantic translation path.

This is a stronger claim than saying the Lean printer happens not to emit aliases. The declarations have already been removed from the working LLBC crate before pure translation starts.

Basis: pinned Aeneas **source**, `src/Main.ml` and `src/PrePasses.ml`.

### Downstream Aeneas analyses treat any surviving alias as an invariant violation

The pinned implementation has explicit guards at later stages:

- `src/llbc/TypesAnalysis.ml` raises `"type aliases should have been removed earlier"` if it encounters `Alias _` while analyzing a nonopaque type declaration;
- `src/symbolic/SymbolicToPureTypes.ml` raises the same message if pure-type translation receives an `Alias _` declaration.

These checks show the intended architecture. Aeneas does not carry aliases through a parallel semantic path. The pre-pass establishes an invariant that later analyses rely on.

Basis: pinned Aeneas **source**.

### Generated Lean for `OptNode` contains the underlying type and no alias declaration

The pinned Aeneas test `tests/src/mini_tree.rs` contains:

`type OptNode = Option<Box<Node>>`.

Both `Node.child` and `Tree.root` use `OptNode` in Rust. The preserved generated `tests/lean/MiniTree.lean` contains no `OptNode` declaration. Instead:

- `Node` stores `Option Node` directly;
- `Tree.root` has type `Option Node` directly.

Two transformations contribute to that final type shape. The ordinary alias name has disappeared before pure translation, and Aeneas's separate type translation erases `Box`. The artifact therefore demonstrates the end-to-end result but should not be read as saying alias removal itself erases `Box`.

Basis: preserved Aeneas Rust input + generated Lean **execution** artifact, interpreted with pinned Aeneas **source**.

### Generated Lean for `Key` and `Hash` similarly uses `Std.Usize` directly

`tests/src/hashmap.rs` defines:

- `pub type Key = usize`;
- `pub type Hash = usize`.

The Rust `AList<T>` constructor stores a `Key`, and other public functions use both aliases. In the preserved generated `tests/lean/Hashmap/Types.lean`, there is no `Key` or `Hash` type declaration. `AList.Cons` takes `Std.Usize` directly, and other generated declarations use the translated underlying scalar type.

This gives a second, simpler witness where no `Box` elimination is needed to explain the alias disappearance.

Basis: preserved Aeneas Rust input + generated Lean **execution** artifact.

### Generic aliases are removed by the same Aeneas rule

`filter_type_aliases` does not special-case nongeneric aliases. Any LLBC `Alias _` declaration is removed from the type map and declaration list. Charon's preserved `S2<I,F>` fixture shows that generic aliases can reach the LLBC boundary as top-level declarations, complete with generic parameters and clauses.

Aeneas therefore does not generate a corresponding generic Lean alias merely because Charon preserved one. Uses have already been represented through the underlying type, with generic arguments instantiated where needed upstream.

Basis: pinned Aeneas and Charon **source** + preserved Charon **execution** artifact.

### Alias-specific source identity is lost at the Aeneas-to-Lean boundary

After `filter_type_aliases`, the alias's `TypeDeclId`, item name, source span, generic parameter list, alias-body declaration, and alias-level metadata are no longer present as a type declaration in the Aeneas crate used for translation. The semantic underlying types at use sites remain.

Consequently, generated Lean generally cannot answer source-oriented questions such as:

- Did the programmer spell this field as `usize`, `Key`, or another alias of `usize`?
- Which alias declaration in a chain was written at a particular use site?
- What alias-specific documentation, attributes, or source span should a diagnostic cite?

Those questions require data from an earlier representation or an independent source map. Equal Lean types do not encode the erased alias path.

Basis: **derived** from pinned Charon/Aeneas source and preserved generated artifacts.

### Associated types are a separate mechanism and do not disappear through this filter

Aeneas's alias filter matches LLBC `TypeDeclKind::Alias`. Trait associated types are represented through trait declarations, trait clauses, and associated-type machinery rather than ordinary top-level alias declarations. Charon may lift associated types into explicit type parameters before Aeneas receives the crate, and Aeneas's trait/type translation handles the surviving trait structure separately.

Therefore the rule established here is not “all Rust `type` declarations disappear.” It is specifically about ordinary free type aliases represented by Charon as top-level `Alias` declarations.

Trait aliases and opaque types likewise need their own representation analysis. This report does not generalize ordinary-alias behavior to them.

Basis: pinned Charon/Aeneas **source** + corpus trait/type reports.

### The alias boundary is useful for deciding where Anneal must preserve source correspondence

For semantic verification, Aeneas's choice is economical: carrying a second alias declaration into Lean would add a source-level name after Rust's semantic type system has already made ordinary aliases transparent. Proofs can operate directly on the underlying translated type.

For diagnostics and annotations, however, source spelling can still matter. If an Anneal annotation names a source alias, or a diagnostic should point to that alias declaration rather than only to its underlying type, the generated Lean term is too late to recover the distinction reliably.

The durable engineering implication is not that Aeneas should necessarily change. It is that any future Anneal source-correspondence layer that cares about ordinary aliases needs an explicit earlier anchor—rustc/Charon item identity and span metadata, or another source map—rather than assuming the Lean type retains the alias name.

Basis: **derived** from the established representation boundaries. This is a constraint on source-correlation information flow, not a selection of Anneal architecture.

## Boundaries

- No fresh Charon, Aeneas, Lean, Lake, Cargo, or rustc execution was performed.
- Checked-in `.out` and `.lean` files are preserved upstream artifacts from the pinned repositories, not fresh execution by this report.
- The report covers ordinary free type aliases represented by Charon as `TypeDeclKind::Alias`.
- Trait associated types are discussed only to distinguish them from ordinary free aliases. Aeneas trait translation is a separate research subject.
- Trait aliases are not characterized here.
- Type-alias `impl Trait` / opaque-type behavior is not characterized here; the companion rustc report explains why opaque aliases are semantically different upstream.
- The report does not claim that every Charon configuration selects every source alias declaration for output. Selection/opacity rules are separate concerns.
- Charon can transform an alias declaration before serialization, especially around associated-type clauses. This report does not inventory every alias transformation or every failure mode.
- Aeneas removes alias declarations from its working crate, but this does not prove that every log message, input file, or auxiliary diagnostic facility is incapable of mentioning an alias name. The claim concerns the semantic crate passed to interpretation/translation and the generated Lean declarations.
- Alias erasure does not imply ABI/layout erasure by itself. Layout and alias transparency are separate questions.
- The generated `MiniTree.lean` example also reflects Aeneas's independent `Box` erasure; only the disappearance of `OptNode` itself is evidence about alias handling.
- No claim is made for adjacent Aeneas or Charon revisions.

## Evidence

**Source — Aeneas.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.

- `src/PrePasses.ml`, blob `dc0ab803c26dafb14caf0da1bcc73e3499716835`: `filter_type_aliases`; deletion from `type_decls` and `declarations`; recursive-group invariant; placement of the filter in `apply_passes`.
- `src/Main.ml`, pinned source: `PrePasses.apply_passes` runs before concrete tests, borrow checking, or `Translate.translate_crate`.
- `src/llbc/TypesAnalysis.ml`, blob `4b80030bddd0fc7d044894a85fe332c8d3bdb5d9`: downstream alias encounter is an error because aliases should already be removed.
- `src/symbolic/SymbolicToPureTypes.ml`, blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`: pure type-declaration translation rejects a surviving alias with the same invariant message.

**Source — paired Charon.** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

- `charon/src/ast/types.rs`, blob `548be29762fdc4f4d1cd652537db6f54065ff6ee`: `TypeDeclKind::Alias(Ty)` and the contract that alias declarations appear only at top level because rustc inlines uses elsewhere.
- `charon/src/bin/charon-driver/translate/translate_items.rs`, blob `7964644be017856c6d165545a67bd6ef06e0c85c`: explicit translation of `FullDefKind::TyAlias` to an alias declaration while preserving item metadata/generics.
- `charon/src/transform/add_missing_info/add_missing_alias_clauses.rs`, blob `ce8ad412edd7a95c612020c97c37bbd2796a8f49`: repair of missing trait clauses inside type-alias bodies.
- `charon/src/transform/normalize/expand_associated_types.rs`, blob `04c0d0c3ec2d883be87845ae30f198ff0372dd33`: alias-specific associated-type normalization and error handling.
- `charon/src/transform/mod.rs`, blob `8d9ec016c3b6e42ba0cbac180546551d4a52587a`: ordering of the missing-alias-clause and associated-type-expansion passes.

**Preserved Charon artifacts.** Same Charon revision.

- `charon/tests/ui/issue-395-failed-to-normalize.rs`, blob `08ec48928d42366324f2337fdf04aaaf893d951e`, with `.out` blob `0fd678541b9c51aa81a123793d56cda629c32665`: top-level generic aliases survive into final LLBC with translated/inferred clauses.
- `charon/tests/ui/associated_types/lift-assoc-ty-in-alias.rs`, blob `ed86667309d0d01370cb5b284407db1127494d7c`, with `.out` blob `37885333c8011fcab23fb647a7b2668ca6740db6`: associated-type lifting rewrites the alias's generic/body representation while preserving the top-level alias item.

**Preserved Aeneas artifacts.** Same Aeneas revision.

- `tests/src/mini_tree.rs`, blob `fbed6893fb840c0f0bc21bbf3b4e58b69db5ab6c`, with `tests/lean/MiniTree.lean`, blob `ae54d4543872edac62862c999a2f91a227489b2f`: source `OptNode` alias is absent from generated Lean; uses become the translated underlying type.
- `tests/src/hashmap.rs`, blob `fc18963eba56b3228132126c8ea985a04b2ea46f`, with `tests/lean/Hashmap/Types.lean`, blob `57fd95233a6b5e6fef75ab00e04e9673ef7a085a`: source `Key` and `Hash` aliases are absent from generated Lean and uses become `Std.Usize`.

**Corpus cross-reference.** `reports/rust-type-alias-lowering-nightly-2026-05-31/` on the zerocopy `reference` branch establishes the preceding Rust/rustc alias-transparency boundary and distinguishes ordinary aliases from projections and opaque aliases.

No evidence in this report is fresh **execution**.

## Revalidation

For a later Aeneas/Charon pair, first inspect the representation boundary rather than starting with generated Lean.

1. In Charon, inspect `TypeDeclKind` and the translation of free type aliases. Confirm whether use-site types still inline ordinary aliases and whether top-level alias declarations are emitted.
2. Inspect Charon's alias-specific transformation passes, especially trait-clause repair and associated-type normalization, because they determine what alias declaration reaches serialization.
3. In Aeneas, inspect `PrePasses.filter_type_aliases` or its successor and confirm when it runs relative to borrow checking and pure translation.
4. Inspect downstream type analysis and pure extraction to determine whether aliases remain forbidden there or have become semantic target declarations.

On an execution-capable surface, use one compact crate containing:

- `type A = u32` and a field/function using `A`;
- `type Pair<T> = (T, T)` and a generic use;
- an alias chain `type B = A`;
- an alias whose body contains an associated-type projection, both with and without an explicit corresponding bound;
- one associated type and one opaque `impl Trait` control that must not be conflated with the ordinary aliases.

Preserve the exact Rust source, Charon LLBC before Aeneas, Aeneas generated Lean, diagnostics, commands, revisions, and hashes. Check which alias declarations exist in LLBC, whether any use-site type points to an alias declaration, which alias declarations survive into Lean, and whether the associated/opaque controls take different paths.

That experiment establishes the concrete boundary for the tested toolchain. It does not make source alias spellings part of Rust semantic type identity or establish a cross-version compatibility guarantee.