# Rust type aliases from resolution through compiler type lowering at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, an ordinary Rust type alias has a compiler item identity but normally does not remain a distinct semantic type after type lowering. Name resolution can identify the alias declaration by its own `DefId`, and HIR preserves a `TyAlias` item with its name, generics, and right-hand-side type. When rustc lowers a use of an ordinary alias into its internal type representation, however, it obtains the alias's lowered right-hand side through `type_of`, instantiates that type with the path's generic arguments, and returns the instantiated underlying type.

That split explains why an alias spelling can be meaningful for source navigation while being misleading as a semantic type identity. The Rust Reference defines a type alias as a new name for an existing type, not a new nominal type. At this compiler revision the normal lowering path implements that transparency directly: for a non-lazy alias, `lower_path_segment` does not construct an alias `Ty`; it substitutes `tcx.type_of(def_id).instantiate(...)`.

There is one source-visible exception that must not be generalized away. With the unstable lazy-type-alias machinery active for a definition, rustc creates `TyKind::Alias` with `AliasTyKind::Free { def_id }`. The type-system source describes this form as a type alias whose bounds are checked and says it can always be normalized away. It is therefore a delayed transparent alias, not evidence that ordinary type aliases are nominal.

Associated types and opaque `impl Trait` types use the same broad internal `Alias` family for different semantics. A trait projection can remain unresolved until normalization, and an opaque type intentionally hides its underlying type outside permitted scopes. Those forms must not be conflated with an ordinary `type Foo = Bar` alias merely because rustc calls each an alias internally.

No fresh rustc, Cargo, Charon, or Anneal execution was performed. This report is based on the pinned Rust Reference and exact rustc implementation source. It establishes where alias declaration identity exists and where ordinary alias identity is erased from the semantic type representation; it does not claim that every diagnostic, debug representation, or downstream tool forgets the source alias spelling.

## Applicability

Primary compiler subject:

- repository: `rust-lang/rust`
- revision: `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`
- relationship: compiler revision behind the Anneal-era Rust/Charon nightly-2026-05-31 toolchain.

Language-reference subject:

- repository: `rust-lang/reference`
- revision: `ad35aca481751a06afeb23820a672b0f3b11a476`
- relationship: `src/doc/reference` revision recorded by the compiler subject.

The main result concerns ordinary free type aliases such as `type Bytes<'a> = &'a [u8]`. The report also records the pinned compiler's unstable lazy-free-alias representation because it is an explicit exception to eager expansion.

Associated types and type-alias `impl Trait` are discussed only to keep their semantics distinct from ordinary transparent aliases. This report does not treat either as equivalent to an ordinary free alias.

The companion corpus package `rustc-name-resolution-stable-item-identity-nightly-2026-05-31` establishes the broader `DefId`/`DefPathHash`, namespace, import, local-item, and generated-item identity model. This report follows one particular definition kind—type aliases—through HIR and semantic type lowering.

Adjacent compiler revisions are outside scope.

## Findings

### The language defines a type alias as another name, not another nominal type

The pinned Rust Reference says that a type alias defines a new name for an existing type in the type namespace. Its example makes `Point` a synonym for `(u8, u8)`; values do not acquire a second runtime or nominal type merely because the alias exists.

The Reference's recursive-type rule reinforces this distinction: recursion must pass through a nominal type such as a struct, enum, or union rather than through only type aliases or other structural types.

This is the language-level reason a source spelling such as `Point` should not be treated as evidence of a distinct nominal semantic type.

Basis: **normative**.

### The alias declaration still has its own item identity before type expansion

Transparency of the aliased type does not erase the declaration itself. HIR contains a distinct `ItemKind::TyAlias(Ident, Generics, Ty)`. The alias therefore has a definition, source span, generic parameters, and the ordinary compiler definition identity assigned to an item.

A path use can resolve to that alias definition before the compiler computes the semantic type denoted by the path. The companion item-identity report establishes the wider rule: a definition `DefId` answers which declaration a name denotes; it is not the same thing as the final semantic `Ty` produced after type lowering.

This distinction is important for source correspondence. A tool can know that the programmer wrote and resolved through alias declaration `A` even if the resulting semantic type is indistinguishable from the type obtained through alias `B` or the underlying spelling.

Basis: **source** + **derived** relation to the pinned resolver identity model.

### HIR preserves the alias right-hand side instead of replacing the declaration immediately

At the pinned revision, `rustc_hir::ItemKind` represents a free alias as `TyAlias(Ident, Generics, Ty)`. HIR therefore retains both the alias declaration and the syntax-lowered type expression on its right-hand side.

This is an intermediate representation boundary. It means "the alias is transparent" does not mean "the frontend deletes every record that an alias declaration existed." The declaration survives as an HIR owner; transparency becomes decisive when a use is lowered into rustc's semantic type representation.

Basis: **source**.

### `type_of` computes an ordinary alias's semantic right-hand-side type

The pinned `rustc_hir_analysis::collect::type_of` implementation handles an HIR `ItemKind::TyAlias` by calling the item-lowering context on the alias's right-hand-side type:

`ItemKind::TyAlias(_, _, self_ty) => icx.lower_ty(self_ty)`.

Thus `tcx.type_of(alias_def_id)` denotes the lowered right-hand-side type of an ordinary alias definition. It is not a nominal wrapper type keyed by the alias declaration.

Generic aliases remain parameterized at the definition. Instantiation happens when a use supplies generic arguments.

Basis: **source**.

### Ordinary alias uses are eagerly replaced by the instantiated underlying type

The decisive path is `HirTyLowerer::lower_path_segment`. After resolving the path to a definition and lowering the path's generic arguments, the normal branch returns:

`tcx.at(span).type_of(def_id).instantiate(tcx, args).skip_norm_wip()`.

For an ordinary type alias, that takes the alias's lowered right-hand side and substitutes the use-site generic arguments. For example, if `type Pair<T> = (T, T)`, the semantic type obtained from `Pair<u32>` is the instantiated tuple type, not an ordinary alias node that still names `Pair`.

Consequently, a consumer operating on these semantic `Ty` values cannot generally infer which transparent source alias spelling led to the type. Different alias chains and a direct spelling can converge on the same underlying semantic type.

Basis: **source** + **derived**.

### Generic substitution is part of transparency

Alias erasure is not merely textual replacement. rustc first lowers the path's generic arguments and then instantiates `type_of(def_id)` with those arguments. The alias declaration's generics therefore determine how parameters in its right-hand side are substituted.

This matters when reconstructing source meaning from a lowered type. Knowing only the underlying type is enough for many semantic operations, but it does not recover the source alias path or the particular generic spelling that produced it.

Basis: **source**.

### Lazy free aliases are an explicit delayed-normalization exception

The same `lower_path_segment` function has a special branch for a `DefKind::TyAlias` whose `type_alias_is_lazy(def_id)` predicate is true. Instead of immediately returning the instantiated `type_of`, rustc creates:

`AliasTyKind::Free { def_id }`

with the lowered generic arguments and wraps it in `Ty::new_alias`.

The source comment explains the purpose: aliases defined under the `lazy_type_alias` feature are encoded as aliases so normalization can later instantiate their where-bounds. The type-IR declaration describes `Free` as a type alias that checks its trait bounds and states that it can always be normalized away.

This representation delays transparency; it does not create nominal type identity. A future consumer must therefore distinguish "ordinary aliases are eagerly transparent at this pin" from the stronger and false statement "rustc can never carry a free-alias node."

Basis: **source**.

### rustc's internal word "alias" covers semantically different categories

`AliasTyKind` at the pinned revision has separate variants for:

- `Projection`: a trait associated-type projection;
- `Inherent`: an associated type in an inherent impl;
- `Opaque`: an opaque type, commonly from `impl Trait`;
- `Free`: the lazy free-type-alias representation above.

These categories normalize under different rules. In particular, an opaque type intentionally controls when its hidden underlying type is available, while a free alias can always normalize away. An associated-type projection can depend on trait selection before its result is known.

A downstream report or implementation that says only "rustc represents aliases as `TyKind::Alias`" therefore hides the distinction needed to reason about semantic identity.

Basis: **source**.

### Associated types are not ordinary free aliases

The Rust Reference uses related `type` syntax for associated types, but their declaration rules differ. The compiler also lowers a resolved associated type into an alias/projection representation rather than taking the eager free-alias path.

This is why a statement such as "type aliases disappear during lowering" needs the qualifier "ordinary free aliases." A trait projection such as `<T as Trait>::Item` may remain as a semantic alias until enough type information exists to normalize it.

Basis: **normative** + **source**.

### Type-alias `impl Trait` introduces an opaque type rather than ordinary transparency

The pinned type IR explicitly describes its `Opaque` alias kind as covering opaque types, including those originating from `impl Trait` in type aliases. The HIR also records `OpaqueTyOrigin::TyAlias`.

An opaque type's central property is intentionally different from a transparent alias: outside allowed normalization scopes, its hidden type is not interchangeable merely because its defining syntax contains `type`.

A source tool must therefore classify the definition kind and lowering result rather than assuming all declarations beginning with `type` have the ordinary free-alias behavior documented above.

Basis: **source**.

### A type alias does not alias value-namespace constructors

The Reference distinguishes a type alias from a `use` alias of a tuple/unit struct constructor. If `struct S(u32)`, then `use S as U; U(1)` can use the constructor binding, while `type T = S; T(1)` is rejected.

That boundary follows from namespace semantics: a type alias creates a name in the type namespace for the existing type; it does not create or re-export the corresponding value-namespace constructor.

This is another reason textual equivalence is unsafe. "Both names denote `S` as a type" does not imply that the names have identical behavior in every syntactic namespace.

Basis: **normative**.

### Source identity can survive after semantic type identity does not

The alias declaration, HIR path, resolved definition, and source span can remain available in compiler structures used for diagnostics or source-oriented tooling even when the semantic `Ty` has already become the underlying type. Conversely, a consumer that receives only the lowered semantic type cannot assume it can reconstruct the source alias chain.

The useful model is therefore two-layered:

1. **source/declaration identity** can say which alias item a path resolved through;
2. **semantic type identity** for an ordinary alias is normally the instantiated underlying type after lowering.

Anneal- or Charon-facing code that needs alias spellings for diagnostics must preserve or recover source/declaration metadata explicitly. It should not use textual type names as the semantic identity of a lowered Rust type.

Basis: **derived** from the pinned source.

## Boundaries

- No fresh rustc, Cargo, Charon, or Anneal execution was performed.
- This report covers ordinary free type aliases and the pinned source-visible lazy-free-alias exception. It does not claim `lazy_type_alias` is stable or enabled in Anneal's ordinary Rust inputs.
- Associated types are discussed only to distinguish their projection/inherent alias semantics from ordinary free aliases.
- Type-alias `impl Trait` is discussed only to distinguish opaque-type semantics from ordinary free aliases.
- The report does not characterize every rustc normalization mode or prove when every projection/opaque alias normalizes.
- It does not claim all compiler diagnostics forget alias spellings. Source/HIR/definition metadata can retain them after semantic type lowering.
- It does not characterize rustdoc, debuginfo, mangling, pretty-printing, or IDE presentation of aliases.
- It does not claim `DefId`, HIR, or `Ty` internals are stable public rustc APIs.
- It does not empirically establish exactly what the pinned Charon serializer emits for every alias example. That would require a dedicated Rust-to-LLBC probe or direct Charon alias-representation study.
- It does not infer behavior for adjacent compiler revisions.

## Evidence

**Normative — Rust Reference.** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/items/type-aliases.md`, blob `c21981eb8580b4a17dedd7c286d03605d24df118`: free and associated type-alias rules; aliases as new names for existing types; constructor-alias counterexample.
- `src/types.md`, blob `8ee8ab00fb7815c1e25a370ab400a5252707d0e9`: type paths and the rule that recursive types cannot be formed through mere type aliases alone.

**Source — rustc.** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `compiler/rustc_hir/src/hir.rs`, blob `59d1b4b5576ee47ea6c994977d40d5a948f139ce`: `ItemKind::TyAlias`, HIR path resolution fields, and opaque-type origins.
- `compiler/rustc_hir_analysis/src/collect/type_of.rs`, blob `3ac603fc715f3071b9930e3a07f23c592a2c9633`: `compute_type_of_item` branch lowering a `TyAlias` right-hand side.
- `compiler/rustc_hir_analysis/src/hir_ty_lowering/mod.rs`, blob `d2c236b5e0a12c535a112f495d2c2ae278f40ae5`: `lower_path_segment`; eager `type_of(...).instantiate(...)` path; `type_alias_is_lazy` exception; associated-item alias lowering.
- `compiler/rustc_type_ir/src/ty_kind.rs`, blob `6f3cea27cafdb097b120c4141c8acd4ca6d58e36`: `AliasTyKind::{Projection, Inherent, Opaque, Free}` and their normalization descriptions.
- `compiler/rustc_middle/src/ty/sty.rs`, blob `9db9b1769ab9c891ef1aa0cdbdc83cde81e2487d`: `Ty::new_alias` and the assertion mapping `Free` aliases to `DefKind::TyAlias`.

**Corpus cross-reference.** `rustc-name-resolution-stable-item-identity-nightly-2026-05-31` records the broader pinned `DefId`/`DefPathHash`, import, namespace, local-item, and generated-item identity model. The primary claims in this report are supported by the upstream sources above rather than by that report alone.

No evidence gathered here is fresh **execution**.

## Revalidation

For another Rust revision, first inspect three source points.

1. In HIR, confirm how a free type alias declaration is represented and whether its definition identity remains an ordinary item.
2. In `type_of`, inspect the branch for free type aliases and determine what type is stored for the alias definition.
3. In HIR-to-type lowering, inspect the path-resolution branch for `DefKind::TyAlias`. Record whether it eagerly instantiates `type_of`, creates a free alias node, or uses a new representation. Then inspect the current alias-kind definitions and normalization rules.

That source diff is the cheapest reliable discriminator for the main result.

On a capable execution surface, preserve one small crate containing:

- a direct alias, `type A = u32`;
- a generic alias, `type Pair<T> = (T, T)`;
- an alias chain, `type B = A`;
- a tuple struct with both a `use` alias and a `type` alias;
- an associated type projection; and
- if the exact compiler supports it, a `lazy_type_alias` control.

Capture HIR output and one downstream semantic artifact such as Charon LLBC for the exact revision. Compare which layers still display the source alias and which contain only the underlying type. If using an unstable compiler dump, record the exact command and compiler commit.

Such a probe establishes the observed representation for those cases. It does not prove a public compatibility guarantee for rustc internals or establish all diagnostic pretty-printing behavior.
