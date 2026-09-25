# Charon item identity, names, source spans, and comments at Aeneas nightly-2026.06.03

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`,
Charon separates **item identity** from **human-readable names**. Within one
`TranslatedCrate`, top-level semantic items are addressed by typed integer IDs
(`TypeDeclId`, `FunDeclId`, `GlobalDeclId`, `TraitDeclId`,
`TraitImplId`), wrapped by `ItemId`. The crate separately stores a `Name`
for every registered item, including names for items whose translation failed.
The source explicitly says those integer IDs uniquely disambiguate items and that
Charon's names intentionally simplify rustc's more precise definition paths.

A `Name` is a sequence of structured `PathElem` values rather than a plain
Rust path string. Elements can be identifiers with disambiguators, inherent/trait
impl descriptors, generic instantiations, and target qualifiers. The first
element is always the crate name. Charon collapses rustc's type/value/macro
namespaces into one presentation namespace and tries to retain disambiguators
only when necessary. Impl blocks are represented structurally; closures and
compiler-generated anonymous items receive synthetic components such as
`closure`, `{const}`, `{promoted_const}`, `{vtable}`, and related names.
Consequently, a textual Charon `Name` is useful source correspondence and
matching data, but it should not be mistaken for rustc's full stable item
identity.

Source locations are likewise structured. Charon maintains a crate-wide file
table and represents spans as a file ID plus one-based line and zero-based
display-column endpoints. For MIR statements whose source scope came from macro
expansion or inlining, Charon can carry two locations: `Span.data` is rewritten
to the top-most inlined/call-site parent, while `generated_from_span` retains
the lower-level origin. Item metadata also stores a definition span and, when
available, the source text rustc supplied for the item.

Charon normalizes some filenames to reduce machine dependence. Standard-library
paths beneath the sysroot are rewritten under `/rustc`; other toolchain paths
under `/toolchain`; Cargo-home sources under `/cargo`; rustc virtual paths
have the compiler hash stripped when recognized. Local source paths otherwise
remain local paths. Non-real rustc filenames exist in Charon's schema, but span
translation currently rejects them.

Comments have two distinct paths. Rust doc comments are rustc attributes and are
preserved directly as `Attribute::DocComment` in item/field/variant attribute
metadata. Ordinary body comments are **heuristically recovered from source
text**, not carried precisely by MIR: Charon scans lines beginning with `//`,
records line-numbered comment groups, and in a final transformation attaches each
group to the next eligible statement/terminator by source line. The source itself
calls this "a pretty simple heuristic"; the checked-in test deliberately shows
that a `//` sequence inside a multiline string can fool it. Block comments are
not recovered by this body-comment scanner.

No fresh Charon execution was performed for this report. The naming, span, path
normalization, and comment behavior is established from exact source and
checked-in golden tests.

## Applicability

This report applies to Charon
`a535e914f74db4fd9e6be7048f4233270d8945c0`, version `0.1.210`, pinned by
Aeneas `nightly-2026.06.03` at
`ac9f1bc5262a5e4ff1e24ca78617121382202727`.

It describes identities and metadata **inside one Charon-translated crate at
this revision**. It does not claim that numeric Charon IDs remain equal across
separate Charon runs, different translation options, source edits, targets, or
Charon revisions.

It also distinguishes three related concepts:

1. rustc/Hax definition identity, which Charon consumes while extracting;
2. Charon's typed `ItemId` indexes, which uniquely address items inside the
   translated crate;
3. Charon `Name` paths, which are deliberately higher-level names for matching,
   diagnostics, generated output, and consumers.

The report does not establish a stable end-to-end identity from Rust source
through Aeneas-generated Lean. That cross-layer identity remains a separate
diagnostics/source-correspondence subject.

## Findings

### Typed item IDs are the unambiguous in-crate handles

`TranslatedCrate` stores separate indexed maps for types, functions, globals,
trait declarations, and trait implementations. `ItemId` is a tagged union over
their typed indices. Associated types, methods, and constants have separate
associated-item IDs.

The crate also stores `item_names` for every registered `ItemId`, with an
explicit invariant that every existing item ID has a name even if the item
itself failed to translate. This makes names diagnostic/retrieval metadata while
the typed ID is the direct reference used by the AST.

Basis: **source** in `ast/krate.rs`.

### Charon names deliberately simplify rustc definition paths

`ast/names.rs` says rustc paths are more precise than the names exposed in
LLBC: rustc tracks namespaces and disambiguators per definition-path element.
Charon intentionally prefers simple string identifiers, maps type/value/macro
namespaces into one namespace, and keeps disambiguators where needed.

The source also states that items are already uniquely disambiguated by their
integer Charon IDs and that name clashes must still be handled by consumers.
This is direct evidence against treating the display name itself as Charon's
sole identity.

Basis: **source**.

### Names are structured paths, not flat strings

A `Name` contains a vector of `PathElem`. A path element is one of:

- `Ident(String, Disambiguator)`;
- `Impl(ImplElem)`, where the impl is either an inherent impl for a bound type
  or a trait-implementation reference;
- `Instantiated(Binder<GenericArgs>)`, representing a monomorphized or otherwise
  instantiated item;
- `Target(TargetTriple)` in multi-target mode.

The first element is always the crate name.

This structure lets Charon describe items for which ordinary Rust source spelling
is not enough, especially impl methods and instantiated/generated items.

Basis: **source** in `ast/names.rs`.

### Impl methods are named through explicit impl elements

rustc definition paths contain an abstract `Impl` component rather than
literally embedding the self type. Charon resolves that component.

For inherent impls, Charon translates the self type and records it in an
`ImplElem::Ty` binder. For trait impls, the path records the Charon
`TraitImplId`. Methods beneath the impl then extend that structured parent
name.

The implementation retains rustc disambiguators for distinct impl blocks when
needed. The source examples show why two impl blocks for the same type cannot be
safely represented by `crate::Type::method` alone.

Basis: **source** in `translate_meta.rs` and `names.rs`.

### Closures and anonymous/compiler-derived items receive synthetic path elements

Charon's mapping covers definition-path components that do not have normal Rust
identifiers:

- closures become an identifier named `closure` plus rustc's disambiguator;
- anonymous consts become `{const}`;
- promoted consts become `{promoted_const}`;
- `use` definitions can become `{use}`;
- constructors and foreign-module wrappers do not add a separate component;
- derived vtable artifacts receive components such as `{vtable}`,
  `{vtable_method}`, and `{vtable_drop_shim}`;
- closure methods append their synthesized method names;
- instantiated items can append their generic arguments.

These names are Charon conventions, not source spellings.

Basis: **source**.

### Consumer-facing rename attributes do not replace the underlying Charon name

`ItemMeta` includes `AttrInfo.rename`, derived from
`#[charon::rename("...")]`, `#[aeneas::rename("...")]`, or related supported
attributes. Charon's source describes this as a custom name that consumers such
as Aeneas may use.

The checked-in `rename_attribute` golden output still prints the original
"Full name" while the attribute metadata carries the requested alternate name.
Therefore the rename is consumer-facing metadata, not a mutation of the
underlying Charon item path/ID.

Basis: **source** + checked-in **execution artifact** in
`tests/ui/rename_attribute.{rs,out}`.

### Item metadata carries source identity/provenance information separately

Each translated item has `ItemMeta` containing:

- structured `Name`;
- definition `Span`;
- optional source text;
- attributes/visibility;
- whether the item is local to the translated crate;
- opacity;
- optional rustc language/diagnostic-item name.

This makes it possible for a consumer to distinguish an external item from a
local one and to retain both semantic Charon identity and user-source context.

Basis: **source** in `meta.rs` and `translate_meta.rs`.

### Charon spans contain file, line, and display-column ranges

A `SpanData` is:

- a `FileId`;
- beginning location;
- ending location.

Locations use one-based line numbers and zero-based display-column offsets,
derived with rustc's source map.

The file ID indexes `TranslatedCrate.files`. Each file contains Charon's
normalized `FileName`, the crate name rustc associates with that source file,
and optional file contents as rustc saw them.

Basis: **source**.

### MIR source-scope translation can preserve both call-site and generated origin

For ordinary item spans, Charon directly translates the rustc span and leaves
`generated_from_span = None`.

For MIR statements and terminators, `translate_span_from_source_info` walks
`inlined_parent_scope` to the top-most inlined parent. When such a parent
exists, Charon sets:

- `Span.data` to the top-most parent span;
- `generated_from_span` to the original statement/source-info span.

The AST documentation gives a macro example: the primary span points to the
macro invocation written by the user, while `generated_from_span` can identify
the code from the macro definition that generated the statement.

This is valuable dual provenance, but it is not an arbitrary expansion stack:
the schema stores one primary span and one optional generated-origin span.

Basis: **source**.

### File paths are normalized to reduce installation-specific identity

For real rustc filenames with local paths, Charon first normalizes Windows path
separators. It then rewrites recognizable roots:

- Rust source under the sysroot's `lib/rustlib/src/rust` becomes
  `/rustc/<relative-path>`;
- other sysroot paths become `/toolchain/<relative-path>`;
- paths under Cargo home become `/cargo/<relative-path>`;
- other paths remain as local paths.

For rustc real filenames without a local path, Charon uses a virtual name and,
when it matches `/rustc/<40-hex-hash>/...`, removes the compiler hash.

This reduces differences caused by rustup/Nix/cache locations while still
retaining a source path.

Basis: **source** in `translate_filename`.

### Non-real rustc filenames are representable but currently not accepted for translated spans

The `FileName` schema has `Local`, `Virtual`, and `NotReal` variants.
`translate_filename` converts non-real rustc filenames to a debug-formatted
`NotReal` value.

However, `translate_span_data` currently calls `unimplemented!()` for
`NotReal` rather than registering such a file. Therefore the existence of
`FileName::NotReal` in the schema does not mean all rustc synthetic/query
filenames can pass through source-span translation at this revision.

Basis: **source**.

### Local-variable names are best-effort debug information, not stable identity

When translating MIR locals, Charon asks Hax for a source/debug variable name
from MIR `var_debug_info`. If unavailable, the local's name is `None`. The
local itself is addressed by `LocalId` and carries type/span separately.

Checked-in pretty output demonstrates this distinction by rendering source
locals with names such as `sum_2` while compiler-generated temporaries appear
as anonymous locals such as `_7`.

Basis: **source** + checked-in golden output.

### Doc comments are preserved as attributes

rustc encodes doc comments as attributes. Charon translates
`AttributeKind::DocComment` directly to `Attribute::DocComment(String)`.
These comments therefore belong to attribute metadata on the item/field/variant
rather than to the body-comment heuristic described below.

Basis: **source** in `translate_attribute`.

### Ordinary body comments are recovered heuristically from source text

MIR itself does not provide Charon with ordinary source comments. Charon's
`translate_body_comments` instead receives the original source text associated
with the definition and scans it line by line.

The scanner:

1. considers lines whose trimmed text starts with `//`;
2. groups consecutive line comments;
3. assigns absolute source line numbers based on the body's span;
4. stores those groups on the intermediate body.

A final `recover_body_comments` pass traverses final ULLBC or LLBC statements
in translation order and attaches each still-unassigned comment group to the
first eligible statement/terminator whose beginning line is at or after the
comment. It skips `StorageLive` statements specifically because Charon does
not want source comments to attach to inserted storage markers.

This is explicitly described in source as a simple heuristic.

Basis: **source**.

### Comment association is not a semantic/source-map guarantee

The pass states an ideal set of constraints—one statement per comment,
source-order compatibility with control flow, and attachment before the
statement—but immediately says the implementation is only a simple heuristic.

The checked-in `comments.rs` deliberately contains a multiline string with a
line that looks like `// Fooled ya`. The golden output shows Charon incorrectly
recovering text from that string as a comment before a later statement. This is
preserved execution evidence of a known false-positive class.

The scanner also only recognizes `//` after leading whitespace. It does not
parse Rust tokens and therefore does not recover block comments through this
mechanism.

Basis: **source** + checked-in **execution artifact** in
`tests/ui/comments.{rs,out}`.

### Transformation passes preserve comments late rather than tracking them through every rewrite

Raw statements start with empty `comments_before`. Charon retains body-level
line-numbered comment groups while performing its main statement/control-flow
transformations. `recover_body_comments` runs near the end of the transformation
pipeline, after statement-affecting passes, specifically to avoid losing
comments as statements are rewritten.

This improves practical placement, but it also means comment association is
derived from final statement spans and source lines rather than being a precise
provenance edge preserved through each transformation.

Basis: **source**.

## Boundaries

- **Charon integer IDs are not claimed stable across runs.** They are the
  unambiguous handles inside one translated crate, not a documented persistent
  cross-build identity.
- **Charon names are intentionally less precise than rustc definition paths.**
  Charon collapses namespaces and suppresses many disambiguators. The source
  explicitly acknowledges this tradeoff.
- **Only one optional generated-origin span is stored.** This is not a complete
  macro-expansion/inlining stack.
- **Non-real filenames can fail translation.** The schema has a `NotReal`
  variant but `translate_span_data` currently rejects it.
- **Local paths are not universally relocatable identifiers.** Charon normalizes
  recognized sysroot/Cargo paths, while ordinary local project paths remain
  local filesystem paths.
- **Body comments are heuristic.** They are not token-aware, can mistake text
  inside multiline strings for comments, and the scanner covers `//` line
  comments rather than a full Rust comment grammar.
- **Doc comments and body comments have different representations.** Doc comments
  are attributes; ordinary line comments are attached to final statements.
- **No fresh source-map/comment probe was executed.** The observed comment
  false-positive and representative output come from Charon's checked-in golden
  tests.
- **This report does not establish Rust→Aeneas-Lean source identity.** It
  establishes what Charon exposes at its side of that boundary.

## Evidence

**Source — pinned Charon.**
`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`:

- `charon/src/ast/krate.rs`: typed item IDs, item-name maps and translated
  declaration maps.
- `charon/src/ast/names.rs`: `Name`, `PathElem`, impl representation and
  explicit discussion of simplified rustc paths/disambiguation.
- `charon/src/ast/meta.rs`: `Span`, `SpanData`, `FileName`, `File`,
  `ItemMeta`, doc-comment attributes and rename metadata.
- `charon/src/bin/charon-driver/translate/translate_meta.rs`: file-path
  normalization, span translation, inlined-parent handling, rustc definition-
  path translation, closure/anonymous/derived names, attributes and item
  metadata.
- `charon/src/bin/charon-driver/translate/translate_bodies.rs`: MIR local
  naming and source-text `//` comment extraction.
- `charon/src/transform/add_missing_info/recover_body_comments.rs`: final
  comment-to-statement heuristic.
- `charon/src/transform/add_missing_info/compute_short_names.rs`: separate
  computation of presentation-friendly short names.

**Checked-in execution artifacts — pinned Charon tests.**
Same revision:

- `charon/tests/ui/comments.rs` and `comments.out`: representative body
  comment placement plus the intentional multiline-string false positive.
- `charon/tests/ui/rename_attribute.rs` and `rename_attribute.out`: rename
  metadata coexisting with underlying full names.

These golden outputs are preserved results from Charon's own test suite; they
were not freshly executed on this surface.

**Derived.**
Because Charon's typed IDs, structured names and source metadata have separate
roles, a cross-layer consumer should not use a display path alone as proof of
semantic identity. That is a derived constraint, not an Anneal architecture
decision.

## Revalidation

For a later Charon revision:

1. Diff `ast/krate.rs`, `ast/names.rs` and `ast/meta.rs` for changes to
   ID classes, path elements, span structure and file metadata.
2. Diff the naming portion of `translate_meta.rs` for rustc `DefPathItem`
   handling, impl/closure/anonymous-name rules and disambiguator policy.
3. Diff `translate_filename` and span translation for new path-remapping rules,
   non-real filename support, or richer expansion provenance.
4. Diff `translate_attribute` for doc-comment behavior.
5. Diff `translate_body_comments` and `recover_body_comments.rs`; rerun the
   checked-in comments fixture to detect heuristic changes.
6. Diff the rename fixture if consumer-facing name overrides matter.

On a capable execution surface, add one compact provenance fixture containing:

- two same-type inherent impl blocks with potentially colliding method names;
- a trait impl;
- a closure;
- anonymous and promoted consts;
- a macro which emits a statement;
- an item from a dependency and a standard-library call;
- doc comments, line comments, block comments and a multiline string containing
  text beginning with `//`.

Generate JSON LLBC and preserve the item IDs/names, file table, spans,
`generated_from_span`, attributes and attached comments. The fixture can
validate concrete source correspondence at that Charon revision; it still would
not establish that Charon IDs are stable across source edits or revisions.
