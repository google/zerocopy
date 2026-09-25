# Aeneas external and standard-library models at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, external Rust definitions are handled through an explicit Rust-name-pattern-to-backend-definition registry. For Lean, model authors annotate Lean definitions with attributes such as `rust_type`, `rust_fun`, `rust_const`, `rust_trait`, and `rust_trait_impl`. A generator imports the Lean environment, collects those registrations, and regenerates `src/extract/ExtractBuiltinLean.ml`; Aeneas then uses the generated OCaml table during extraction to replace matched external Rust declarations with the registered Lean definitions.

Missing external definitions are not silently invented. With `-split-files`, Aeneas generates template files for missing external types/functions and separate user-maintained model files. The templates carry the relevant `rust_*` annotations, so the intended workflow is to copy the declaration into the maintained external file and fill in its model. If a model is promoted into the Aeneas standard library, `make extract-lean-std` rebuilds the Lean environment and regenerates the OCaml registry.

The model metadata controls more than spelling. Function registrations can filter Rust type parameters and trait clauses, declare whether the model can fail, and control whether a non-failing pure Lean function is lifted into Aeneas's `Result` monad. Type registrations can filter parameters, identify mutable-region positions, rename variants/fields, or mark the backend type as opaque. These settings therefore participate in the semantic interface between extracted Rust and the Lean model.

Coverage is finite and revision-specific. The generated Lean-specific registry at this pin contains 357 literal Rust-name patterns: 35 type registrations, 212 function registrations, 45 trait-declaration registrations, and 65 trait-implementation registrations. Of those literal patterns, 319 begin with `core::`, 37 with `alloc::`, and one with `std::`. The generic backend table in `ExtractBuiltin.ml` additionally contributes generated families and mappings shared across backends. These counts describe registry entries, not proof that the corresponding Rust library behavior is completely or faithfully modeled.

Opaque external declarations and modeled declarations are distinct cases. Aeneas explicitly filters registered builtins from the set of opaque non-builtin declarations when deciding whether external declarations remain unresolved. An unmatched opaque function/type can be emitted as an external declaration/template; a matched builtin is redirected to the registered model. A model is therefore a trust/semantics boundary: matching a Rust item to a Lean definition does not itself prove that the definition implements the Rust item's full semantics.

No fresh Aeneas, Lean, Charon, or model-generation execution was performed. The report uses exact pinned source, checked-in generated registry code, and checked-in generated Lean fixtures.

## Applicability

Primary subject:

- repository: `AeneasVerif/aeneas`
- revision: `ac9f1bc5262a5e4ff1e24ca78617121382202727`
- release: `nightly-2026.06.03`
- Lean toolchain: `leanprover/lean4:v4.30.0-rc2`

Current Anneal at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` selects this release. The report records the exact model registry and extraction mechanism at that pin; adjacent Aeneas revisions may add, remove, or change mappings.

“Builtin” has two related meanings in the Aeneas source:

1. LLBC/pure semantic builtins implemented directly by Aeneas, such as special Box/array/slice operations in `src/llbc/Builtin.ml`;
2. external Rust declarations recognized by name and mapped to backend-library definitions by `src/extract/ExtractBuiltin*.ml`.

This report focuses on the second mechanism but distinguishes it from the first when their roles overlap.

The literal-entry counts below are derived from the checked-in generated `ExtractBuiltinLean.ml` file. They count explicit generated `mk_type`, `mk_fun`, `mk_trait_decl`, and `mk_trait_impl` registrations with literal Rust patterns. They do not count dynamic families synthesized by `ExtractBuiltin.ml`, nor do they deduplicate semantically overlapping patterns across the generic and Lean-specific tables.

## Findings

### Lean definitions register Rust identities through attributes

`backends/lean/Aeneas/Extract/Extract.lean` defines scoped environment attributes for five model kinds:

- `rust_type`;
- `rust_fun`;
- `rust_const`;
- `rust_trait`;
- `rust_trait_impl`.

Each attribute takes a Rust name pattern. The source documentation says the pattern is the one Aeneas emits for a missing definition, so a model author does not need to reverse-engineer the internal matcher syntax.

The attribute machinery records both the Rust pattern and source span of the Lean declaration. The generator later sorts these descriptors and emits OCaml registration code.

Basis: **source**.

### Function models carry semantic extraction metadata

A `rust_fun` registration has a `FunInfo` record with:

- optional extracted name;
- `keepParams`, for filtering Rust type parameters absent from the Lean model;
- `keepTraitClauses`, for filtering trait evidence;
- `canFail`, defaulting to true;
- `lift`, defaulting to true;
- `hasDefault`, used for trait-method defaults.

The attribute documentation explains the `canFail`/`lift` interaction. If a model cannot fail but `lift` remains enabled, Aeneas emits a coercion/lift into `Result` so the call can still participate naturally in the WP/`step` proof style.

Thus a model registration is not just a name alias. It describes how the Rust signature is projected onto the Lean model and how its effect shape participates in generated code.

Basis: **source**.

### Type models can deliberately abstract representation

A `rust_type` registration can filter parameters, rename fields and variants, control variant-name prefixes, identify mutable-region positions, and declare the model body opaque.

When the body is not explicitly opaque, the Lean-side extractor inspects the Lean declaration and checks field/variant metadata against the actual environment. Duplicate or unmatched names produce errors during registry extraction.

This catches some mechanical mismatches between model metadata and the Lean declaration. It does not prove that the model has the same representation or operational semantics as the Rust type.

Basis: **source**.

### The Lean standard-library registry is generated from the Lean environment

The Makefile target `extract-lean-std` runs:

`cd backends/lean && lake exe extract`

then formats the regenerated OCaml source.

The Lean generator imports the model module/environment, reads all registered `rust_*` descriptors, sorts them, and prints OCaml lists for builtin types, constants, functions, trait declarations, and trait implementations. The checked-in `ExtractBuiltinLean.ml` starts from those generated lists and includes comments pointing back to the Lean model file and source line.

This makes the checked-in generated OCaml file an exact registry manifest for the pinned Lean standard library, while the Lean source remains the semantic implementation.

Basis: **source** + checked-in generated artifact.

### The generated Lean-specific table has 357 literal model registrations

At this exact revision, literal pattern registrations in `src/extract/ExtractBuiltinLean.ml` break down as:

| Kind | Literal registrations |
|---|---:|
| Types | 35 |
| Functions | 212 |
| Trait declarations | 45 |
| Trait implementations | 65 |
| Total | 357 |

By first Rust path component, the same 357 patterns divide into 319 `core::` entries, 37 `alloc::` entries, and one `std::` entry.

Representative modeled types include `alloc::vec::Vec`, `alloc::string::String`, `core::option::Option`, `core::result::Result`, ranges, iterator adapters, formatting types, pinning types, and selected atomic types. Representative function families cover scalar operations/conversions, arrays/slices, vectors, iterators, comparisons, formatting, and trait methods.

The count is useful as a pinned coverage fingerprint. It is not a claim that 357 Rust API items are semantically complete: patterns can denote generic families, implementations can be partial abstractions, and the generic `ExtractBuiltin.ml` table adds additional generated/shared mappings.

Basis: checked-in generated **source/artifact** plus deterministic counting of its literal registration syntax.

### Generic backend mappings augment the Lean-generated table

`ExtractBuiltin.ml` defines mappings shared or synthesized across backends. It includes generic type mappings and function families for operations such as `mem::replace`, `mem::take`, Option unwrap, slice indexing, Vec operations, Box dereference, and scalar families.

The same module appends Lean-only lists produced by `ExtractBuiltinLean.ml`. Therefore “the Lean model coverage” is not equal to the generated file alone. The generated file is the Lean-authored registry; the final matcher also contains generic Aeneas mappings.

This is why the 357-entry count should be used as a regression fingerprint for the Lean-specific registry, not as a complete cardinality of every name matcher accepted by the translator.

Basis: **source**.

### Standard-library models are selected by Rust name-pattern matching

The extraction tables are indexed by parsed Rust name patterns through `NameMatcher`. Patterns can include generic placeholders and structured trait/impl names, so one entry can match a family of instantiated Rust declarations.

The matched registration supplies the extracted Lean name plus parameter/trait-clause filtering and effect metadata. Generated Lean fixtures show the result: calls such as Rust clone, conversions, and scalar byte operations become calls to definitions in `Aeneas.Std` rather than copied Rust bodies.

Basis: **source** + preserved generated artifact.

### The checked-in builtin fixture demonstrates actual name redirection

`tests/src/builtin.rs` says explicitly that it exercises builtin definitions to ensure they are detected and mapped to the standard library.

Its checked-in generated Lean output contains examples such as:

- Bool clone mapped to the Aeneas `CloneBool` model;
- integer clone mapped to the corresponding scalar model;
- `Into`/`From` mapped to modeled trait dictionaries;
- `u32::from_le_bytes` and `to_le_bytes` mapped to Aeneas scalar functions.

This is preserved upstream execution evidence that the registry was used when the fixture was generated. It is not fresh execution on this surface.

Basis: preserved upstream **execution** artifact + source fixture.

### Missing external models have an explicit template workflow

The pinned README recommends `-split-files` when a crate references external definitions that Aeneas does not already model. Aeneas can generate:

- automatically generated type/function files;
- `TypesExternal_Template.lean` and `FunsExternal_Template.lean`;
- user-maintained `TypesExternal.lean` and `FunsExternal.lean`.

The generated template declarations include the appropriate `rust_type`, `rust_fun`, and related attributes. The intended handoff is therefore explicit: the user supplies a model rather than relying on an unspecified fallback implementation.

The generated main files import the user-maintained external files. This separation also prevents regeneration from overwriting the user's models.

Basis: upstream **documentation** + **source**.

### Promoting a model into Aeneas's standard library is a reproducible registry update

The README describes a two-stage promotion:

1. add the Lean model to the Aeneas standard library with the appropriate `rust_*` attribute;
2. run `make extract-lean-std`, which rebuilds the Lean library, collects registrations, and regenerates `ExtractBuiltinLean.ml`.

The generated OCaml table then carries the Rust pattern and source location of the model into the extraction binary.

This is a useful revalidation boundary: a future model-coverage comparison can diff the generated registry independently of broad source archaeology.

Basis: upstream **documentation** + **source**.

### Registered models are excluded from the unresolved-opaque inventory

`Translate.ml` has a helper for detecting opaque non-builtin declarations. Its documentation explicitly says that when `filter_builtin` is true, external definitions that will be mapped to standard-library definitions are not considered unresolved opaque declarations.

That establishes the key control-flow distinction:

- matched external declaration → use builtin/model mapping;
- unmatched opaque external declaration → remains an opaque/external obligation and can be emitted for modeling.

This is the concrete relationship between Charon/Aeneas opacity and the model registry at this stage. “Opaque” does not itself mean “modeled”; matching a registered model is an additional condition.

Basis: **source**.

### An unresolved opaque declaration can become an assumption boundary

The extraction context records whether an opaque definition was emitted and comments that extracting an opaque definition means “we generate an axiom.” When opaque declarations are present without split files, Aeneas recommends the split-file workflow.

For Lean projects, that means an unresolved external function/type can become an assumed declaration until a concrete model is supplied. A consumer that treats generated Lean as a proof artifact must therefore distinguish:

- translated definitions with bodies;
- registered standard-library models;
- user-supplied external models;
- unresolved opaque assumptions.

The existence of a Lean declaration is not enough to tell which category it belongs to.

Basis: **source**.

### Model registration is not model validation

The `rust_*` machinery checks names, descriptor structure, and some correspondence between Lean declaration shape and metadata. It does not establish a semantic refinement theorem from the real Rust implementation to the Lean model.

Similarly, the standard-library registry records `canFail`, parameter filtering, and names, but those fields are declarations made by model authors. They are part of the trusted semantic boundary unless separately justified.

This is especially important for Anneal because Rust-level claims require a justified relation to Rust semantics. A proof that depends on an external model inherits whatever assumptions justify that model.

Basis: **source** + **derived** trust-boundary analysis.

### Internal semantic builtins are a separate mechanism

`src/llbc/Builtin.ml` defines Aeneas-internal builtin function IDs and signatures for operations whose behavior is handled specially by the interpreter/translation. Its source comments discuss special evaluation and the possibility of replacing some hard-coded implementations with modeled bodies.

These builtins should not be conflated with the backend external-model registry. The former are part of Aeneas's semantic translation machinery; the latter redirect external Rust identities to backend-library definitions.

A future trust inventory should account for both.

Basis: **source**.

## Boundaries

- No fresh model extraction, Lean build, Aeneas translation, or test execution was performed.
- The 357-entry count covers literal registrations in the checked-in generated Lean-specific table. It does not include dynamic/generated families from `ExtractBuiltin.ml` and is not a count of semantically unique Rust APIs.
- The report does not claim complete coverage of `core`, `alloc`, or `std`. The overwhelming `core` share of the registry should not be read as percentage coverage of Rust's standard library.
- A name match does not prove semantic equivalence between the Rust definition and Lean model.
- Some models intentionally abstract allocator parameters, failure behavior, representation, or trait evidence. Those abstractions require independent justification for a Rust-level theorem.
- The report does not prove whether every unresolved external declaration becomes an axiom in every output configuration; it establishes the pinned extraction source's opaque/assumption path and split-file workflow.
- It does not inventory the semantic correctness of each of the 357 Lean-specific registrations.
- It does not evaluate model coverage for unsafe Rust beyond recording the exact pinned table and the separate resource-semantics boundary.
- The current Aeneas overview contains some simplified descriptions that are not exact for all generated Lean shapes; pinned source and checked-in output take precedence here.
- No Anneal architecture choice is inferred from this mechanism.

## Evidence

**Source — primary Aeneas revision.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.

- `backends/lean/Aeneas/Extract/Extract.lean`, blob `377130a8db02017dd17af1096b025c3a17e63088`: `rust_type`, `rust_fun`, `rust_const`, `rust_trait`, `rust_trait_impl`; descriptor validation; registry generator.
- `src/extract/ExtractBuiltinLean.ml`, blob `433e0fd178f785ec26a9de9b717600c5d2c7a991`: generated Lean-specific registry and source-location comments.
- `src/extract/ExtractBuiltin.ml`, blob `6e28b984b6392fd49601aac6903604248f464955`: generic external-name maps and composition with Lean-specific mappings.
- `src/Translate.ml`, blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`: opaque/transparent translation and filtering of modeled builtins from unresolved opaque declarations.
- `src/extract/ExtractBase.ml`, blob `4fc8a3f35643ba66555f0889790d50993feef1b9`: opaque-extraction state and axiom comment.
- `src/llbc/Builtin.ml`, blob `fec847925d30e0236f4bd5a83b18b270577f7918`: separate internal semantic-builtin mechanism.
- `Makefile`, blob `b547c69dd21e85de6a5eca44690cca6ba4d949d1`: `extract-lean-std`.

**Documentation — same revision.**

- `README.md`, blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`: external-file workflow, standard-library model promotion, registry regeneration.
- `documentation/aeneas-overview.md`, blob `439076012c1ba93c7ec1bf25aca42e0f1ec14756`: split-file anatomy and external model files.

**Preserved generated fixture.**

- `tests/src/builtin.rs`, blob `6190ae93469ba094244298b202855e1ac364ba40`.
- `tests/lean/Builtin.lean`, blob `14f1a5446f0fc4445707da2475b8d1f347e84766`.

The 357-entry fingerprint was derived directly from the literal `mk_type`, `mk_fun`, `mk_trait_decl`, and `mk_trait_impl` registrations in the pinned generated file. No fresh **execution** was used to produce or validate those registrations.

## Revalidation

For a future Aeneas release:

1. resolve the exact Aeneas commit;
2. diff `backends/lean/Aeneas/Extract/Extract.lean` for attribute schemas and defaults;
3. regenerate or inspect `src/extract/ExtractBuiltinLean.ml`;
4. count literal registrations by kind and Rust path root;
5. diff `ExtractBuiltin.ml` for generic mappings and matcher behavior;
6. inspect `Translate.ml` for how modeled builtins are excluded from unresolved opaque declarations;
7. inspect one checked-in builtin fixture to ensure name redirection still matches the registry.

On a capable surface, run `make extract-lean-std` at the exact revision and require the generated `ExtractBuiltinLean.ml` to match the checked-in file byte-for-byte. Then build a tiny crate with three external calls: one existing standard-library model, one user-supplied `rust_fun` model, and one deliberately unmodeled opaque function. Translate with `-split-files` and record the generated files/imports and resulting Lean declarations. Change `canFail` or `lift` on the user model and verify the generated call shape changes as documented.

Those tests establish registry wiring and current output shape. They do not establish that a model is semantically faithful to the actual Rust implementation.
