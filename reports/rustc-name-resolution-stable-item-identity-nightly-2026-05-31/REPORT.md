# rustc name resolution and stable item identity at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler revision behind Anneal's pinned Charon toolchain, a source spelling is not an item identity. Rust name resolution maps a use of a name to a semantic resolution. Ordinary definitions resolve to a `DefId`; local bindings resolve to a local HIR identity. Namespaces, scopes, imports, aliases, impl disambiguators, and compiler-generated definitions mean that identical text can identify different entities and different text can identify the same entity.

A `DefId` is the direct handle inside one compilation session. For cross-session compiler bookkeeping, rustc derives a `DefPathHash` from the definition's crate identity and disambiguated definition path. rustc describes that hash as stable across crate and compilation-session boundaries and uses it to recover the current session's `DefId` during incremental compilation. That stability is conditional rather than permanent: the crate component includes the crate name, `-Cmetadata`, crate kind, and rustc version, while the path component includes the parent path, definition kind/name, and a sibling disambiguator. Source changes that alter those inputs can change the hash.

Imports and re-exports demonstrate why spelling and identity must remain separate. A resolver import binding follows its source binding to the target `Res`, so an imported alias can name the same target `DefId` through another path. A type alias is different: the alias declaration has its own `DefId` and definition path, even though the Rust Reference defines it as a new name for an existing type rather than a new nominal type.

Nested and anonymous constructs also receive compiler identities. Block-local item declarations are ordinary items under the containing definition; closures, anonymous constants, inline constants, opaque types, and synthetic coroutine bodies have dedicated definition kinds and definition-path components even when no stable source spelling exists. Ordinary local variables are the important contrast: they resolve as local HIR nodes rather than `DefId` definitions.

For an Anneal-style consumer, the durable distinction is therefore: use compiler semantic identity to decide which definition an occurrence denotes, and use source/display paths for presentation and lookup assistance. Charon adds another item-ID/name layer after rustc; its separate reference report documents that boundary. This report does not select an Anneal identity schema.

No fresh rustc execution was performed. The findings come from the exact pinned Rust compiler source and Rust Reference.

## Applicability

This report applies to:

- Rust compiler source `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the Rust revision used by the Charon toolchain pinned to nightly 2026-05-31.
- Rust Reference `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

The report distinguishes four identities that are easy to conflate:

1. a **source spelling or path**, such as `Foo`, `crate::m::Foo`, or an imported alias;
2. a **name-resolution result**, represented by rustc's `Res`;
3. a **session definition handle**, `DefId`, for entities that are definitions;
4. a **cross-session compiler key**, `DefPathHash`, used to recover a current `DefId` when the corresponding definition still exists.

These are rustc implementation concepts at this exact revision. `DefId` and `DefPathHash` are not presented here as stable public Rust APIs, and "stable" in `DefPathHash` does not mean invariant under arbitrary source, metadata, target, or compiler-version changes.

## Findings

### Name resolution produces semantic results, not canonical strings

The resolver crate states that it resolves module structure plus paths in imports, expressions, types, patterns, macros, labels, and lifetimes. Its primary result type is `Res`.

For ordinary user-defined definitions, `Res::Def` carries both a `DefKind` and a `DefId`. rustc's own example distinguishes this from locals: a reference to `String`, `String::from`, or a free function resolves to `Res::Def(..., DefId)`, while a local variable resolves to `Res::Local`.

The important consequence is that the text used to reach an item is not the result of name resolution. Once a path resolves, downstream compiler phases can refer to the semantic definition handle rather than replaying source spelling.

Basis: **source**.

### Rust namespaces make spelling alone ambiguous by construction

The Rust Reference defines separate type, value, macro, lifetime, and label namespaces. Context determines which namespace a use searches.

A tuple struct illustrates the problem directly: the same spelling names the struct in the type namespace and its constructor in the value namespace. rustc represents those as different definition kinds. `DefKind::Struct` is the type-side definition; `DefKind::Ctor` is the synthesized constructor definition. Macros and lifetime parameters can reuse the same textual name in their own namespaces.

rustc's definition-path representation preserves these distinctions with components such as `TypeNs(Symbol)`, `ValueNs(Symbol)`, `MacroNs(Symbol)`, and `LifetimeNs(Symbol)`.

A consumer that identifies an item only by a string such as `Foo` therefore loses information that rustc uses to disambiguate legal programs.

Basis: **normative** Rust Reference + **source**.

### Scope and shadowing can change what one spelling denotes within one function

The Reference gives item names module/block scopes and local bindings lexical scopes. Local bindings can shadow item declarations. Its example has one occurrence of `foo` resolve to a function and a later occurrence of the same spelling resolve to a local closure after a `let foo = ...`.

rustc represents the distinction structurally: the function occurrence can resolve to `Res::Def(..., DefId)`; the local binding resolves to `Res::Local(HirId)`.

Source spelling plus crate/module path is therefore still insufficient for occurrences inside bodies. Position and scope affect resolution.

Basis: **normative** + **source**.

### `DefId` is the direct definition handle for one compilation session

`DefId` contains a `CrateNum` and a `DefIndex`. rustc describes it as identifying one particular definition. `DefIndex` is an index into a crate's definition data and is described as an interned shorthand for a definition path.

The numeric pair is a compiler-session handle. It is useful and unambiguous while that compilation's crate store and definition tables are alive, but its numeric values should not be persisted as if they were stable source identities.

For local HIR nodes that are not definitions, rustc uses `HirId`, which combines the closest item-like owner's `LocalDefId` with an owner-local node index. That distinction is why a local variable does not need to become a top-level `DefId` merely to participate in name resolution.

Basis: **source**.

### `DefPathHash` is rustc's cross-session definition key

rustc defines `DefPathHash` as a fixed-size representation of a `DefPath` that is stable across crate and compilation-session boundaries. It contains:

- a `StableCrateId`, identifying the defining crate;
- a crate-local hash for the definition path.

The compiler uses `def_path_hash_to_def_id` to map a deserialized `DefPathHash` back to the corresponding current-session `DefId` if the definition still exists. The source explicitly names incremental compilation as a consumer.

This is the strongest directly documented rustc identity in the inspected source for carrying a definition across sessions. It is still a compiler-internal identity, not a promise that arbitrary edits or compiler upgrades preserve a key.

Basis: **source**.

### Stable crate identity depends on compilation identity inputs

`StableCrateId` is not just a hash of the crate's source name. At this revision its constructor hashes the crate name, sorted/deduplicated `-Cmetadata` values, executable-versus-library status, and the rustc version string.

This matters for any external system tempted to serialize a `DefPathHash` as a forever-stable project item ID. A rebuild that changes the compiler version or Cargo/rustc metadata can change the crate portion even when a source item still looks identical.

The right interpretation is narrower: rustc has a stable-key mechanism for the compiler contexts whose identity inputs agree, and it deliberately includes compilation identity in that key.

Basis: **source** + **derived** consequence.

### Definition paths contain kind/name data plus sibling disambiguators

A local definition has a `DefKey` made from:

- its parent definition index;
- a `DisambiguatedDefPathData`.

The disambiguated data contains one `DefPathData` plus an integer disambiguator. Named definition-path components encode their namespace and symbol; anonymous components encode kinds such as impl, closure, anonymous constant, opaque type, or synthetic coroutine body.

The disambiguator is normally zero. rustc increments it when siblings would otherwise have the same parent and path data. The source explicitly notes an artificial ordering dependency and gives two impls for the same type in one module as an example that requires distinct IDs.

The path hash recursively incorporates the parent's local hash, the path-data discriminant, any symbol text, and the disambiguator. Thus even rustc's stable key depends on structural identity, not just a printable qualified name.

Basis: **source**.

### Imports and re-exports create alternate bindings to the same target

The Reference defines a `use` declaration as creating local name bindings synonymous with another path. An `as` import can give a target another local spelling, and a public use can redirect a public path to a definition whose canonical defining path is elsewhere.

The resolver preserves this distinction. `DeclData::res()` returns the definition's `Res` directly for an ordinary declaration; for an import declaration it recursively returns the source declaration's `Res`. The resolver separately retains the re-export chain for diagnostics and metadata.

The `use` syntax item itself still receives a `DefKind::Use` definition for compiler bookkeeping. That definition should not be confused with the identity of the imported target.

Therefore a user-facing path such as `crate::Facade::Thing` may be a valid way to find or display an item without being its defining identity.

Basis: **normative** + **source**.

### Type aliases have their own definition identity even though they do not create nominal types

The Reference states that a type alias defines a new name for an existing type and calls it a synonym. rustc nevertheless collects the alias declaration as `DefKind::TyAlias`, producing its own `DefId` and `TypeNs` definition-path component.

This distinction is useful:

- the **alias declaration** is a real source/compiler definition with its own identity;
- the **underlying type** is the type denoted after alias expansion/normalization.

A source-oriented tool may need the alias definition for diagnostics or annotation attachment while a semantic type analysis needs the normalized underlying type. Treating either spelling or normalized type as the only identity loses one of those facts.

Basis: **normative** + **source**.

### Associated-item paths can remain partially unresolved until type checking

rustc's `PartialRes` documents a deliberate split in path resolution. Module-like prefixes are resolved by the main resolver, while type-relative associated-item segments can remain unresolved until type checking. The resolver crate's module documentation likewise says that methods, fields, and associated-item type-relative resolution occurs in `rustc_hir_analysis`.

A spelling such as `Type::Assoc::method` is therefore not necessarily assigned one final target by the same early path-resolution operation that resolves `crate::module::Type`.

For consumers, this is another reason to use the compiler's eventual semantic item identity rather than reconstructing identity from syntax alone.

Basis: **source**.

### Block-local items are definitions; ordinary local bindings are not

The Reference allows item declarations as statements in blocks and gives such item names block scope. rustc's definition collector visits `Item` nodes regardless of whether the containing module or block supplied them, chooses a `DefKind`, and creates an owned definition under the current parent. A block-local function or type therefore receives a `DefId` and participates in the same definition-path machinery as other items.

Ordinary `let` bindings and function parameters instead resolve as `Res::Local` with HIR identity. The compiler does not flatten both categories into a single string namespace.

Basis: **normative** + **source**.

### Closures and anonymous/generated constructs also receive definition identities

The definition collector explicitly creates definitions for constructs that have no ordinary source item name:

- closures and coroutine closures: `DefKind::Closure`;
- anonymous constants: `DefKind::AnonConst`;
- inline const blocks where applicable: `DefKind::InlineConst`;
- opaque `impl Trait` types: `DefKind::OpaqueTy`;
- synthetic coroutine bodies: `DefKind::SyntheticCoroutineBody`.

Their `DefPathData` variants provide structural components even when there is no user spelling. The collector also creates nested closure definitions for async desugarings.

Thus "item identity" cannot be defined only over user-written named item declarations if a downstream semantic representation can contain generated or anonymous Rust definitions.

Basis: **source**.

### Charon adds a distinct downstream identity layer

At the Aeneas-pinned Charon revision, Charon converts rustc definitions into its own typed item IDs and structured names. The existing corpus report on Charon item identity records that those integer IDs are unambiguous inside one translated crate and that Charon's names deliberately simplify rustc definition paths.

The rustc identity facts in this report therefore answer an earlier question in the pipeline. A future Anneal identity/source-correspondence design would need an explicit relationship between rustc identity, Charon identity, generated Aeneas declarations, and user-facing source paths rather than assuming any one printed spelling survives all layers unchanged.

Basis: **derived** from the pinned rustc source and the separately pinned Charon corpus evidence.

## Boundaries

- No fresh rustc, Cargo, Charon, or incremental-compilation execution was performed.
- `DefId`, `DefPath`, and `DefPathHash` are rustc-internal implementation interfaces. This report does not claim a public compatibility guarantee across rustc releases.
- "Stable across compilation sessions" is rustc's source description of `DefPathHash`; it is not a claim of invariance under arbitrary source edits, crate metadata changes, crate-kind changes, or compiler-version changes.
- Sibling disambiguators introduce an explicit ordering dependency. This report does not empirically catalog which edits perturb which downstream disambiguators.
- Local-variable `HirId` stability is not characterized beyond rustc's owner/local-ID model. It should not be treated as a persistent source identifier without separate study.
- Macro hygiene and expansion identity are not exhaustively covered. Macro-generated named and anonymous definitions still enter the compiler identity machinery, but exact hygiene/source provenance is a separate subject.
- This report distinguishes type-alias declaration identity from underlying type semantics; it does not provide a full type-alias lowering/normalization model.
- Trait selection, method lookup, and associated-item resolution are covered only to establish that type-relative resolution can occur later than module/path resolution.
- The report does not claim Charon preserves rustc `DefPathHash` verbatim. Charon's own ID/name model is documented separately.
- No stable Anneal item-ID format, persistence policy, or source/model correspondence architecture is selected here.

## Evidence

**Normative Rust Reference.** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/names/namespaces.md`, blob `58a96c7fafd7e1c1da37289c948fb1866f6f66f5`: namespace separation and same-spelling examples.
- `src/names/scopes.md`, blob `44c3dbf788e3d8194218cf4ecb9f853226524fd0`: item/local scopes and shadowing.
- `src/items/use-declarations.md`, blob `49781895c82a63671b730bcea80ca3f4845d641b`: synonymous imported bindings, renames, and re-exports.
- `src/items/type-aliases.md`, blob `c21981eb8580b4a17dedd7c286d03605d24df118`: aliases as new names/synonyms rather than nominal types.

**Rust compiler source.** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `compiler/rustc_span/src/def_id.rs`, blob `0ea7da4f2ab8707e5a150d3c447e9ec06690c816`: `DefId`, `DefIndex`, `StableCrateId`, and `DefPathHash`.
- `compiler/rustc_hir/src/definitions.rs`, blob `97e739a7f3893d47d94722be46b6d824b515f4f1`: `DefKey`, `DisambiguatedDefPathData`, `DefPathData`, hash construction, and collision/disambiguation tables.
- `compiler/rustc_hir/src/def.rs`, blob `d275d5a28b88ad73141b684a70c43ca661db809d`: `DefKind`, `Res`, namespace mapping, and `PartialRes`.
- `compiler/rustc_hir_id/src/lib.rs`, blob `07b1cceebaf764689d6d4a2746876c398beb5121`: `HirId` owner/local identity.
- `compiler/rustc_middle/src/ty/context.rs`, blob `8c5421d582df20d955338549739f80f6570d1e94`: definition creation and `def_path_hash_to_def_id`.
- `compiler/rustc_resolve/src/lib.rs`, blob `ffb2181bae3a961118e12db1a6dbc8c3de63f275`: resolver boundary, import bindings, target `Res`, and re-export chains.
- `compiler/rustc_resolve/src/def_collector.rs`, blob `cdc2df5bf294533ad80ba078142fb95295345b79`: creation of item, closure, anonymous-const, inline-const, opaque-type, and async/coroutine definitions.

No evidence above is fresh **execution**.

## Revalidation

For a later Rust pin, the cheapest source-level discriminator is to diff the exact identity-defining regions rather than repeat broad compiler archaeology:

1. `rustc_span/src/def_id.rs`: `DefId`, `StableCrateId::new`, and `DefPathHash`.
2. `rustc_hir/src/definitions.rs`: `DefKey`, `DisambiguatedDefPathData`, `DefPathData`, and stable-hash construction.
3. `rustc_hir/src/def.rs`: `DefKind`, `Res`, namespace assignment, and `PartialRes`.
4. `rustc_middle/src/ty/context.rs`: `create_def` and `def_path_hash_to_def_id`.
5. `rustc_resolve/src/lib.rs` and `def_collector.rs`: import-target resolution and creation of nested/anonymous definitions.
6. The Reference namespace, scope, import, and type-alias chapters.

On a capable execution surface, add one small pinned compiler probe containing: a tuple struct and macro with the same spelling; a `use ... as ...` alias and public re-export; a `type` alias; local shadowing; two sibling impls with same-named methods; a block-local function/type; a closure; and an anonymous const. Instrument a rustc-driver callback or narrow compiler test to print each relevant `Res`, `DefId`, verbose `DefPath`, and `DefPathHash`.

Run the unchanged fixture twice, then separately change an unrelated earlier declaration, insert a same-kind sibling impl, change `-Cmetadata`, and change the compiler revision. Record which `DefId` numerics and `DefPathHash` values change. That experiment establishes the operational stability envelope for those exact changes; it does not turn rustc-internal identity into a public cross-version API.
