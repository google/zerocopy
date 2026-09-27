# Charon unions at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), Charon has a first-class union type declaration and preserves the field involved in ordinary runtime union construction and field access. A transparent Rust union becomes `TypeDeclKind::Union(fields)`. Constructing `U { field: value }` becomes `AggregateKind::Adt(type_ref, None, Some(field_id))`; projecting `u.field` uses the ordinary ADT field-projection node with the union's `TypeDeclId` and no enum variant. The checked-in `unions.rs` fixture at this exact revision shows those forms surviving into final LLBC.

That representation must not be interpreted as an active-field model. Rust unions have no active field: every read interprets shared storage as the chosen field type, and validity is the programmer's responsibility. Charon's aggregate `FieldId` records which field a construction writes. Later field projections do not carry an active-field check or a union-read-specific unsafe marker. A downstream verifier that wants Rust union semantics must therefore recover that the projected base type is a union and enforce the validity requirements of the accessed field; it cannot treat the constructor's field ID as a persistent tag.

Charon also records layout information for unions, but one detail is intentionally implementation-specific at this pin. The layout translator models a union as one internal layout variant and hardcodes every field offset to zero when rustc reports `FieldsShape::Union`. PR #1160, merged before this revision, explicitly says this matches what Rust does at that point but is not a Rust language guarantee. The pinned Rust Reference likewise says default-representation union fields may have non-zero offsets. Anneal can use the zero offsets as a fact about this pinned rustc/Charon pair only; it must not elevate them into a version-independent Rust theorem.

Union constants have a weaker structural representation than runtime union aggregates at this revision. `ConstantExprKind::Adt` carries an optional enum variant and a list of fields but no union field ID, while `ConstantExprKind::RawMemory` explicitly exists for cases where a structured constant representation is unavailable, including unions. A later post-pin Charon PR titled “Translate union constants” confirms that this area continued to evolve. Code that needs to reason about union constants should revalidate the exact constant path rather than assuming parity with runtime aggregate translation.

No fresh rustc or Charon execution was performed on this surface. The source analysis is pinned to exact blobs, and the checked-in `unions.out` file is preserved upstream execution evidence from the subject repository.

## Applicability

This report applies to:

- `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`;
- Charon `0.1.210`;
- Charon's pinned Rust toolchain `nightly-2026-05-31`;
- the ordinary ULLBC/LLBC representation produced by the translation paths inspected below.

The report covers the #3720 subject **Charon unions**. It focuses on what Charon preserves and omits at the Rust-to-Charon boundary: union declarations, ordinary construction and field projections, layout, opacity, and constant-expression representation. It does not attempt to prove the Rust validity rules themselves or characterize Aeneas's downstream union semantics.

The exact revision matters. Union layout handling changed shortly before this pin in PR #1160, and Charon continued changing union-related ASTs after it. In particular, post-pin issue #1276 proposes splitting the shared `AggregateKind::Adt` representation into separate struct/enum/union variants, and later work added more explicit union-constant handling.

## Findings

### Transparent unions have a first-class type-declaration kind

`TypeDeclKind` has separate `Struct`, `Enum`, and `Union` variants. The union variant stores an indexed vector of fields:

```text
TypeDeclKind::Union(IndexVec<FieldId, Field>)
```

The type translator maps `hax::AdtKind::Union` directly to that variant. Consumers do not need to infer “unionness” from syntax, layout, or naming; the type declaration itself carries the distinction.

Charon internally treats structs and unions as having one layout variant. That internal layout convention is not a Rust active-field model. The type declaration remains `Union(fields)`, not an enum-like collection of alternatives.

Basis: Charon **source**.

### Runtime union construction records the field being written

For a MIR ADT aggregate, Charon inspects rustc's ADT kind. For structs and unions the aggregate has no enum `VariantId`. For a union only, Charon additionally records the MIR `field_index` as a `FieldId`:

```text
AggregateKind::Adt(type_ref, None, Some(field_id))
```

The AST documentation states the intended interpretation directly: if the `VariantId` is present, the aggregate is an enum; if the `FieldId` is present, the aggregate is a union and the aggregate writes that field; otherwise it is a struct.

The pinned `unions.out` fixture demonstrates the result:

```text
one_1 = Foo { one: const 42u64 }
```

This is useful information for a verifier because construction identifies the field whose type determined the write. It is not evidence that Charon tracks a persistent active field after the write.

Basis: Charon **source** + preserved **execution** evidence.

### Union field access uses the ordinary ADT field-projection representation

MIR field projections for an ADT become `ProjectionElem::Field(FieldProjKind::Adt(type_id, variant_id), field_id)`. Charon asserts that structs and unions have no variant ID, while enums do. A union projection is therefore structurally:

```text
Field(Adt(union_type_id, None), field_id)
```

There is no separate `UnionFieldRead` or `UnionFieldWrite` projection node. Whether a projection belongs to a union is recovered by resolving the referenced `TypeDeclId` and seeing `TypeDeclKind::Union`.

The final pinned fixture contains both a write and a read as ordinary field projections:

```text
(one_1).one = const 43u64
_two_2 = copy (one_1).two
```

This matters for Anneal's semantic boundary. A verifier that needs to distinguish Rust's safe union writes from unsafe reads cannot rely on a special Charon projection kind. It must combine the operation context—left-value write versus value-producing read—with the base type declaration.

Basis: Charon **source** + preserved **execution** evidence.

### Charon does not encode a Rust “active field,” which matches the language model

The pinned Rust Reference says unions have no active field. Writing one field overwrites shared storage; reading any field interprets the corresponding bits as that field's type. The programmer must ensure the resulting value is valid, and an invalid read is undefined behavior.

Charon's ordinary runtime representation is compatible with that shape. The union type has fields, construction records which field is written, and later projections name whichever field is accessed. Nothing in `TypeDeclKind::Union`, `AggregateKind::Adt`, or `ProjectionElem::Field` creates a runtime discriminant or persistent active-field state.

This distinction prevents a tempting but incorrect interpretation: `Some(field_id)` in a union aggregate is not a tag that later authorizes reading the same field or rejects reading another one. It identifies the construction field only.

Basis: Rust Reference **normative** text + Charon **source** + **derived** correspondence.

### Rust's union-read validity obligation is not carried as a dedicated Charon AST marker

Rust requires union field reads to be `unsafe` because the bits may not be valid for the accessed field's type. Writes are safe because union fields cannot require implicit drop glue and a write merely overwrites storage.

The inspected Charon expression AST has no union-read-specific unsafe flag. The pinned union fixture's final LLBC likewise prints the read as `copy (one_1).two`, not as a distinct unsafe operation. The base type still reveals that `one_1` is a union, so a downstream semantic layer has enough structural information to recognize the case, but it must supply the Rust validity rule itself.

This is an important trust boundary for Anneal. Translating a union read into an ordinary field projection does not establish that the read is defined. Any Rust-level claim that crosses such a read needs a semantic rule relating the union's raw storage to validity of the requested field type.

Basis: Rust Reference **normative** text + Charon **source** + preserved **execution** evidence + **derived** verification consequence.

### Borrowing different union fields cannot be modeled as independent storage by a Rust-faithful consumer

The Rust Reference states that all fields share storage. Borrow checking consequently treats a borrow of one union field as borrowing the other fields for the same lifetime as well.

Charon's field-projection syntax itself names individual fields just as it does for structs. That syntax alone should not be interpreted to mean that distinct union fields are disjoint places. A consumer that gives field projections an ownership/aliasing semantics must consult the base type kind and preserve union overlap.

This report does not claim that Charon itself performs downstream borrow reasoning at this stage. It identifies the information boundary: the type declaration says “union,” while the generic projection node says “field N.” The semantic consumer is responsible for combining those facts correctly.

Basis: Rust Reference **normative** text + Charon **source** + **derived** consumer requirement.

### Layout extraction models a union as one variant

`Layout` stores size, alignment, an internal discriminator structure, uninhabitedness, per-variant field layouts, and representation options. Its documentation says structs and unions are modeled as having exactly one variant.

PR #1160 fixed union layout extraction before the pinned revision. Its description says union layouts had previously been translated with no variants, which was wrong because Charon's layout model expects a trivial variant 0. The pinned source now handles rustc `FieldsShape::Union` by producing one `VariantLayout`.

This internal variant is a layout data-structure convention. It should not be confused with a Rust union active field, a Rust enum discriminant, or a tag stored in the union's memory.

Basis: Charon **source** + Charon PR/history **documentation**.

### The pinned layout translator hardcodes union field offsets to zero

`translate_layout_data` handles rustc `FieldsShape::Union(n)` by generating `n` zero offsets. PR #1160 explains why: zero offsets matched what Rust did at the time, but the PR explicitly notes that this was not a language guarantee.

The pinned Rust Reference makes the normative boundary explicit: union fields might have non-zero offsets unless a representation such as `repr(C)` fixes the layout. Therefore:

- zero offsets are a pinned rustc/Charon implementation fact for this subject revision;
- they are not a general theorem about default-representation Rust unions;
- a future compiler or Charon revision must be revalidated before Anneal relies on those offsets for Rust-level proofs.

For `repr(C)` unions the Rust representation rules are stronger, but this report does not generalize the default-representation Charon hardcoding into the full `repr(C)` layout theorem.

Basis: Rust Reference **normative** text + Charon **source** + PR #1160 **documentation**.

### Layout size and alignment are preserved separately from field offsets

The union's `Layout` still carries overall size and alignment obtained from rustc's layout query, plus `ReprOptions`. Thus the zero-offset simplification does not mean Charon reduces a union to “just a bag of fields with no layout.” It retains whole-type layout facts and a field-layout vector.

At the same time, the source-level `Layout` documentation says niches are not included. A consumer requiring exact validity or niche semantics must not infer them from this simplified layout object.

Basis: Charon **source**.

### External unions follow the same public-field transparency gate as external structs

When deciding whether an external ADT body may be treated as transparent, Charon always exposes public enum variants, but for structs and unions it checks the unique variant and requires every field to be public. If that condition fails, ordinary opacity rules apply.

This can matter for FFI unions. A public external union type is not automatically enough for Charon to expose its fields: under this path, all fields must satisfy the visibility test unless another configuration or modeling mechanism changes the opacity decision.

Basis: Charon **source**.

### Union constants do not have the runtime aggregate's explicit union-field slot

The runtime `AggregateKind::Adt` has both an optional enum variant and an optional union field ID. `ConstantExprKind::Adt`, by contrast, has only:

```text
Adt(Option<VariantId>, Vec<ConstantExpr>)
```

There is no parallel `Option<FieldId>` for a union constant. The same AST explicitly provides `RawMemory(Vec<Byte>)` for constants that cannot be represented structurally, with unions given as an example.

The pinned constant translator also accepts a raw-memory constant form from hax. This means consumers should not assume that a union constant retains the same selected-field information as an ordinary MIR aggregate.

Later post-pin work titled “Translate union constants” is further evidence that this area was not frozen at the pinned representation. That later work is a revalidation signal, not evidence about behavior already present in 0.1.210.

Basis: Charon **source** + post-pin repository history used only as **revalidation** evidence.

### The checked-in fixture establishes basic declaration, construction, write, and cross-field read translation

`charon/tests/ui/unions.rs` defines:

```rust
union Foo {
    one: u64,
    two: [u32; 2],
}
```

It constructs `Foo` through `one`, writes `one`, then reads `two`. The exact checked-in `.out` file shows:

```text
union Foo {
  one: u64,
  two: [u32; 2usize],
}
...
one_1 = Foo { one: const 42u64 }
(one_1).one = const 43u64
_two_2 = copy (one_1).two
```

That is strong preserved evidence for the basic translation path. It is not a completeness test for generic unions, `repr(C)` layout, references into union fields, patterns, constants, FFI, or invalid-value behavior.

Basis: preserved Charon **execution** output.

### Charon's union support predates this pin, while layout support changed shortly before it

Issue #335, “Support unions,” was closed as completed in September 2024. Discussion at the time characterized Charon-side union extraction as tractable and distinguished it from Aeneas-side support concerns.

PR #1160, merged on May 17, 2026, then corrected union layout variants and field offsets. The exact pinned revision from May 31 contains that new layout code. This history explains why a report about “union support” must distinguish basic AST/body translation from later layout corrections.

Basis: Charon issue/PR **history** + pinned Charon **source**.

### The shared aggregate encoding has intentionally representable impossible states

At this pin, `AggregateKind::Adt` represents structs, enums, and unions with one tuple-shaped variant:

```text
Adt(TypeDeclRef, Option<VariantId>, Option<FieldId>)
```

Correct combinations are enforced by translation logic and assertions rather than by the Rust type system of Charon's AST. A post-pin open issue, #1276, proposes separate `Enum`, `Struct`, and `Union` aggregate variants specifically to make impossible combinations unrepresentable.

For consumers of the pinned AST, this means the three fields must be interpreted together with the referenced `TypeDeclKind`. The shape alone permits combinations that the translator says should never occur.

Basis: pinned Charon **source** + post-pin issue #1276 as **revalidation/design** evidence.

## Boundaries

- No fresh rustc, Charon, ULLBC, LLBC, Aeneas, Lean, or runtime execution was performed.
- The checked-in `unions.out` file is preserved upstream execution evidence, not a fresh observation from this run.
- This report does not prove that every Rust union construct accepted by `nightly-2026-05-31` is translated correctly. The fixture covers a small but important path.
- The report does not establish Aeneas support for union semantics. Historical issue discussion explicitly separated Charon extraction from Aeneas concerns.
- The report does not define a complete Rust validity model for union reads. It records the normative obligation and the Charon information available to a downstream verifier.
- The report does not claim a Rust union has an active field. The constructor field ID records a write, not a tag.
- The pinned Charon layout's zero field offsets are not a version-independent Rust guarantee. Default Rust union layout permits more freedom.
- `Layout` intentionally omits niche information, so the simplified layout object is not a complete validity/layout model.
- Union constants are not established to preserve selected-field identity structurally. Raw-memory fallback is explicitly part of the pinned constant representation.
- Pattern matching on unions was not separately traced through Charon's lowering path. Rust treats it as a read; a future report should test the exact emitted form if Anneal needs source-pattern correspondence.
- References to union fields were not freshly exercised. Rust's borrowing rule treats union fields as overlapping storage; downstream ownership reasoning must preserve that fact.
- `repr(C)`, packed/aligned attributes, generic unions, zero-sized fields, uninhabited field types, and target-specific layout differences were not empirically probed here.
- Post-pin issues and PRs are used only to identify revalidation hazards; they do not change the behavior claimed for `a535e914...`.

## Evidence

**Primary Charon subject:** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

- `charon/src/ast/types.rs`, blob `548be29762fdc4f4d1cd652537db6f54065ff6ee`: `TypeDeclKind::Union`; simplified `Layout`; one-layout-variant convention for structs and unions.
- `charon/src/ast/expressions.rs`, blob `eeb2143c714ee8b429a59c2aaf9f097afb18a940`: ordinary ADT field projections; runtime `AggregateKind::Adt` with optional enum variant and union field; `ConstantExprKind::Adt`; union-relevant `RawMemory` fallback.
- `charon/src/bin/charon-driver/translate/translate_types.rs`, blob `35bef6ea79992c65ea934413765fa95f631274e6`: union declaration translation, external-public-field opacity gate, union layout variant construction, and zero-offset handling for `FieldsShape::Union`.
- `charon/src/bin/charon-driver/translate/translate_bodies.rs`, blob `c03ca8077f131a2ef701e9d27eaa9e69bb617124`: union field projection translation and runtime aggregate translation with `FieldId`.
- `charon/src/bin/charon-driver/translate/translate_constants.rs`, blob `e0b037b340b3ef1b5316f7af472cd7632ba5e89b`: constant ADT and raw-memory translation paths.
- `charon/src/ast/types_utils.rs`, blob `fbbe1caab444ad99d04aa31a5694a3e76c5204e5`: struct/union field lookup and layout utilities.
- `charon/tests/ui/unions.rs`, blob `eebb96e6157cd2e8a0668daa34a8c027a13e903c`, and `charon/tests/ui/unions.out`, blob `28d372db8e5f00d11c5fc7f9e1a58156a98ecc85`: preserved declaration/construction/write/read translation evidence.
- `charon/Cargo.toml`, blob `8c9936202e7bdbdaaefbc19305363da1ab6c0084`: Charon version `0.1.210`.
- `rust-toolchain`, blob `4e348edab20d6bd5b195e758afe20f9d8258a3e1`: `nightly-2026-05-31` pin.

**Normative Rust boundary:** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/items/unions.md`, blob `c330b037007ff36dc2e8475daefc96e176121914`: shared storage, no active field, read validity/unsafety, safe writes, borrowing overlap, and non-guaranteed default field offsets.
- `src/types/union.md`, blob `3ba187d5ad0bc47c9ed6cf92f56e811388ba4b8e`: union accesses as interpretation/transmutation of common storage and unsafe reads.

**Repository history:**

- Charon issue #335, `Support unions`, closed as completed on 2024-09-04; its discussion distinguishes Charon extraction from downstream Aeneas support concerns.
- Charon PR #1160, `Fix union layout variants and field offsets`, merged 2026-05-17; commit `e92460f998cda33aafd8bb3862b70171ea604ab8`. Its description explicitly calls the zero-offset encoding current Rust behavior rather than a language guarantee.
- Charon issue #1276, `Split up AggregateKind::Adt`, opened 2026-06-08 after the pinned revision. It proposes a more type-safe struct/enum/union aggregate representation and is a revalidation signal only.
- Charon PR #1444, `Translate union constants`, opened/closed after the pinned revision in September 2026. It is likewise a revalidation signal rather than evidence for 0.1.210 behavior.

No fresh **execution** evidence was produced in this run.

## Revalidation

For a future Charon revision, first diff these points:

1. `TypeDeclKind::Union` and union field metadata in `ast/types.rs`;
2. `AggregateKind`, `ProjectionElem`, `FieldProjKind`, and constant-expression variants in `ast/expressions.rs`;
3. ADT and layout translation in `translate_types.rs`;
4. MIR field and aggregate translation in `translate_bodies.rs`;
5. union-related constant translation in `translate_constants.rs`;
6. any successor to issue #1276's proposed split aggregate representation;
7. changes derived from later union-constant work;
8. the Rust Reference's union-layout and validity rules for the compiler/toolchain being claimed.

On a capable execution surface, run one pinned matrix that includes:

- a plain default-representation union with fields of different size/alignment;
- the same union under `repr(C)` and relevant alignment/packing attributes;
- construction through each field, safe field writes, and unsafe reads through both the written and a different field;
- a read that would produce an invalid value, without actually executing UB;
- shared and mutable references to different union fields to inspect emitted place structure;
- pattern matching on a union;
- generic and const-generic unions;
- union constants/statics, including cases that const-eval into raw memory;
- nested unions and unions inside `repr(C)` tagged structures;
- multiple compilation targets if Anneal will consume target-specific layout facts.

Preserve source, exact rustc/Charon versions and flags, ULLBC/LLBC, serialized output, diagnostics, and hashes. Compare:

- declaration kind and field IDs;
- constructor field identity;
- read/write field projections;
- whether source unsafe context is represented anywhere downstream;
- size, alignment, field offsets, and representation options per target;
- constant field identity versus raw-memory fallback;
- any transformation that rewrites field accesses or aggregates.

The cheapest discriminator for the most important layout boundary is simple: inspect whether the future Charon source still hardcodes zero offsets for `FieldsShape::Union`, then compare that behavior with the corresponding Rust Reference and pinned rustc layout implementation. If the language guarantee remains weaker than the implementation, Anneal should continue treating the Charon offsets as toolchain-specific evidence rather than a stable Rust semantic axiom.