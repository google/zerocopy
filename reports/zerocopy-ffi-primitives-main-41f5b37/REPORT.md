# FFI-facing primitives used by zerocopy at `main@41f5b37`

## Summary

At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, the production `zerocopy` crate has a narrow FFI-facing surface. The relevant production source does **not** declare or import foreign symbols. A bounded search of `zerocopy/src` found no foreign blocks, `#[link]`/`#[link_name]` use, `core::ffi`/`std::ffi` imports, `libc::` use, or C scalar aliases such as `c_void` or `c_char`.

The FFI primitive zerocopy actually models is the **ABI-bearing function-pointer type**. `zerocopy/src/impls.rs` and `zerocopy/src/util/macros.rs` generate trait implementations for `Option<extern "C" fn(...) -> ...>` and `Option<unsafe extern "C" fn(...) -> ...>` over many argument/return-type combinations. Those implementations rely on Rust's guaranteed representation of optional function pointers: at the Anneal-selected Rust revision, `Option<T>` has the same size, alignment, and function-call ABI as `T` for function pointers, and the all-zero representation is guaranteed to denote `None`. Zerocopy uses that guarantee to implement `FromZeros` and a conservative `TryFromBytes` predicate that accepts the all-zero representation; it separately implements `Immutable`.

This is an FFI-relevant **representation** dependency, not evidence that zerocopy calls foreign code. An `extern "C" fn` type carries a calling convention even when the value is never used to cross a language boundary. The current production source contains no `extern "C" { ... }` declaration and no native link attribute. Vendored dependencies under `zerocopy/vendor` do contain many foreign declarations, but they are not part of the `zerocopy/src` source inventory and must not be conflated with zerocopy's own primitive surface.

For Anneal, the resulting verification obligation is therefore narrower than a general foreign-call model: preserve the identity, safety qualifier, ABI, null/niche validity, and byte-validation semantics of these function-pointer types. Actual foreign-item behavior, native symbol identity, and foreign implementation semantics are separate subjects.

No fresh build, rustc MIR inspection, Charon extraction, Aeneas translation, linker inspection, or runtime FFI call was performed.

## Applicability

This report applies to the production source of the `zerocopy` package at:

- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`;
- the Rust/core semantics at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, corresponding to Anneal's `nightly-2026-05-31` Rust boundary; and
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

"Used by zerocopy" means representation or semantics on which code in `zerocopy/src` directly relies. The primary source inventory excludes:

- vendored dependency source under `zerocopy/vendor`;
- test-only foreign syntax outside `zerocopy/src`;
- platform libraries merely reachable through the wider repository;
- foreign interfaces in unrelated workspace tools; and
- compiler-synthesized lowering that is not visible as a zerocopy source dependency.

`zerocopy-derive/src` was also screened for the same direct FFI markers; the bounded searches described under **Evidence** found none. The report does not claim that no transitive dependency or generated compiler artifact can ever contain an FFI boundary.

The distinction between a foreign **function pointer type** and a foreign **item declaration** is central. `extern "C" fn(...)` is a Rust function-pointer type with the C ABI. An item inside an `extern` block is a declaration of a definition supplied elsewhere. Zerocopy's production source uses the former representation but the bounded source scan found no instance of the latter.

## Findings

### Zerocopy's production FFI surface is type-level, not a native import surface

A repository-scoped code search over `zerocopy/src` for `extern "C"` returned two production files: `src/impls.rs` and `src/util/macros.rs`. Both uses construct or reason about function-pointer **types**.

The same scoped search found no `extern {` foreign block, no `#[link` or `#[link_name` attribute, no `libc::` reference, no `core::ffi` or `std::ffi` path, and no `c_void` or `c_char` token. Searches for `extern "system"`, `extern "C-unwind"`, and `extern "cdecl"` were also empty.

`zerocopy/Cargo.toml` has no normal `libc` dependency. Its only ordinary dependency is optional `zerocopy-derive`, plus a disabled target dependency that pins the matching derive crate version. The manifest's remaining dependencies are development dependencies.

The bounded evidence therefore supports a specific conclusion: current zerocopy production code has no direct source-level native import edge. The FFI-facing primitive is an ABI-qualified function-pointer representation.

Basis: **source** + **derived** from bounded negative source search.

### Zerocopy explicitly generates optional C-ABI function-pointer types

`zerocopy/src/util/macros.rs` defines two relevant type constructors:

```rust
Option<extern "C" fn(...) -> ...>
Option<unsafe extern "C" fn(...) -> ...>
```

The macros are inputs to `unsafe_impl_for_power_set`, which instantiates many function signatures by choosing subsets of generic argument types and a return type.

`zerocopy/src/impls.rs` then uses those constructors to provide:

- `FromZeros` for optional safe C-ABI function pointers;
- `TryFromBytes` for optional safe C-ABI function pointers;
- `FromZeros` for optional unsafe C-ABI function pointers;
- `TryFromBytes` for optional unsafe C-ABI function pointers; and
- `Immutable` for both families.

The `TryFromBytes` implementations use `pointer::is_zeroed` as their validation predicate. They therefore exploit the one representation that the Rust contract proves is valid without claiming that arbitrary non-zero bytes denote a valid callable function pointer.

Basis: **source**.

### The all-zero representation is guaranteed to mean `None`

The pinned `core::option` documentation gives a representation guarantee for function pointers. For qualifying `T`, `Option<T>` has the same size, alignment, and function-call ABI as `T`. For function pointers, it additionally guarantees that transmuting an all-zero byte array into `Option<T>` is sound and yields `None`, and that `None` can be converted back to all-zero bytes.

The table includes `fn` and `extern "C" fn`, and its footnote says the guarantee also covers unsafe variants, arbitrary argument/return types, and other ABI-qualified function-pointer types.

That guarantee explains zerocopy's implementation boundary:

1. all-zero bytes have a specified valid interpretation as `None`;
2. zerocopy can therefore implement `FromZeros`;
3. `TryFromBytes` can safely accept the all-zero candidate without deciding whether any arbitrary non-zero address/bit pattern is a valid function pointer; and
4. the safe/unsafe qualifier and C ABI remain part of the Rust type even though the null representation rule is shared.

This report does not infer a stronger property such as "all non-zero bit patterns are valid function pointers." Zerocopy's use of a zero-only `TryFromBytes` predicate is evidence that it does not need that stronger claim here.

Basis: **documentation** + **source** + **derived** connection.

### `extern "C" fn` is an ABI-qualified function-pointer type even without a foreign call

The pinned Rust Reference defines bare function-pointer types with optional `unsafe` and optional `extern` ABI qualifiers. It states that the `extern` qualifier marks an extern function and that function pointers can be created by coercion from appropriate function items or non-capturing non-async closures.

The Reference separately describes `extern` function **definitions** and foreign declarations. This separation matters for zerocopy. A value of type `extern "C" fn(A) -> B` carries a C calling convention whether its target is Rust-defined or foreign-defined. The type can therefore matter to layout, validity, transmutation, and call semantics without introducing a linker import by itself.

For verification, do not replace this type with an ordinary Rust-ABI `fn(A) -> B` merely because no foreign symbol is involved. The ABI qualifier is semantic type information.

Basis: **normative** + **derived** consequence for translation.

### Safety and ABI are independent qualifiers in the surface zerocopy uses

The macros cover both:

- `extern "C" fn(...) -> ...`; and
- `unsafe extern "C" fn(...) -> ...`.

The Rust Reference grammar likewise makes `unsafe` and `extern` independent function-pointer qualifiers. Zerocopy's representation logic applies to both families, while call-site safety remains distinct.

A verifier therefore needs to preserve two separate facts:

- the ABI/calling-convention qualification; and
- whether invoking the function pointer requires an unsafe-call proof obligation.

Representation compatibility does not erase the safety qualifier.

Basis: **normative** + **source**.

### Zerocopy intentionally relies on a narrower implemented ABI set than the general Rust representation guarantee

The `core::option` guarantee is broader than C ABI: its footnote extends the null-pointer optimization statement to other ABI-qualified function pointers.

Zerocopy's source comment repeats that broader fact. Its concrete macro-generated implementations in this source revision, however, instantiate ordinary Rust function pointers and C-ABI function pointers; a scoped search found no analogous `extern "system"`, `extern "C-unwind"`, or `extern "cdecl"` production type constructor.

Do not turn the broad upstream representation guarantee into a claim that zerocopy currently implements its conversion traits for every Rust ABI. The general Rust property and the current zerocopy implementation surface are different statements.

Basis: **documentation** + **source**.

### Test aliases confirm representation intent, not actual foreign execution

The `impls.rs` test region defines `ECFnManyArgs = extern "C" fn(...) -> ...` and explicitly suppresses `improper_ctypes_definitions` with the comment that the type is not actually being used for FFI. The tests assert the expected zerocopy traits for optional C-ABI function pointers.

This is useful evidence about the intended type-level contract. It is not evidence of a real native call, ABI interoperability test, or linked foreign implementation.

Basis: **source**.

### Vendored foreign declarations are a different compilation subject

Repository-wide searches naturally return many `extern "C"` declarations under `zerocopy/vendor`, including vendored `libc` and platform support crates.

Those files are real FFI code, but they are not evidence that `zerocopy/src` itself declares or calls those foreign symbols. Whether a particular build of the repository compiles a vendored dependency is a Cargo compilation-subject question. The native reference corpus tracks that distinction separately.

For an Anneal proof scoped to the `zerocopy` crate's own source, importing the vendor-wide FFI surface would substantially overstate the primitive set. If a future verification target includes a vendored dependency, inventory that dependency as its own subject.

Basis: **source** + **derived** compilation-boundary distinction.

### The current primitive inventory has four proof dimensions

For the production zerocopy surface observed here, a compact verification model should retain at least:

1. **type identity** — function pointer versus optional function pointer, argument/return types, and safe versus unsafe;
2. **ABI identity** — C ABI is not interchangeable with Rust ABI merely because representations happen to have related niche guarantees;
3. **validity/representation** — zero bytes represent `None`; arbitrary non-zero bytes are not admitted by zerocopy's zero-only `TryFromBytes` path; and
4. **call semantics** — if a `Some` function pointer is eventually invoked, the call must obey its ABI and safety contract.

The first three dimensions are exercised directly by zerocopy's trait implementations. The fourth becomes active when client code calls the pointer; it is not evidence of a foreign implementation or import.

Native symbol identity and foreign behavior are absent from this source-level inventory because the examined code contains no direct foreign declaration.

Basis: **derived** from the source and normative contracts above.

## Boundaries

- **No fresh compilation or execution.** No Cargo build, rustc MIR dump, Charon run, Aeneas run, linker inspection, or foreign call was performed.
- **Bounded source search, not a whole-program reachability theorem.** Negative findings are about the exact scoped searches over `zerocopy/src` and `zerocopy-derive/src` at the identified revision. They do not prove that transitive dependencies, compiler-generated artifacts, or arbitrary downstream code contain no FFI.
- **Vendor source is excluded from the crate-source inventory.** The repository contains extensive vendored FFI declarations. A build that makes those dependencies part of the verification subject needs a separate inventory.
- **No claim that all non-zero function-pointer representations are valid.** The pinned Option guarantee establishes the null/NPO cases used here. Zerocopy's `TryFromBytes` predicate deliberately accepts the zero representation rather than recognizing arbitrary non-zero pointers.
- **No claim that every ABI has zerocopy trait implementations.** Upstream Rust documents the Option representation guarantee broadly, but this zerocopy revision directly generates the relevant conversion traits only for ordinary Rust function pointers and C-ABI function pointers.
- **No foreign implementation semantics.** There is no direct native import in the examined source, and this report supplies no contract for an external C/C++ function.
- **No Charon/Aeneas preservation claim.** Whether the exact ABI, safety qualifier, function-pointer validity, niche, or indirect-call semantics survive translation is a downstream compatibility question. The existing corpus report on Rust extern/foreign items covers foreign declarations, not this complete function-pointer representation obligation.
- **No call-reachability census.** The report identifies types for which zerocopy supplies byte-conversion traits. It does not enumerate downstream users that instantiate or call every generated function-pointer type.
- **C strings and C scalar aliases are not part of the established production surface.** The bounded source searches found no `core::ffi`, `std::ffi`, `libc::`, `c_void`, or `c_char` use in `zerocopy/src`. This does not claim that no downstream consumer can combine zerocopy with those types.

## Evidence

Evidence was materially acquired or revalidated on 2026-09-27.

**Zerocopy source:** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

- `zerocopy/src/impls.rs`, blob `4df786fd2104854e1fa259a63c29cd8781f8a404`, especially the optional function-pointer `FromZeros`, `TryFromBytes`, and `Immutable` implementations around lines 310–386 and the C-ABI test aliases/assertions around the later test section.
- `zerocopy/src/util/macros.rs`, blob `21b9891088c5a07571f789d8d48b8d24395cfaac`, especially `opt_extern_c_fn!` and `opt_unsafe_extern_c_fn!`.
- `zerocopy/Cargo.toml`, blob `4d98fb3f96784bbff0c5c7cb72b800b3a65ed765`, for the ordinary dependency boundary.
- `ffi-surface.json` in this package preserves the bounded repository-search matrix, including the positive and negative scoped queries used to distinguish zerocopy's own source from repository vendor hits.

**Rust/core documentation:** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `library/core/src/option.rs`, blob `a490a26aa0ff3b3b56bb1f5a3c2a74109cbc839d`, representation documentation around lines 116–155: Option NPO, all-zero `None`, function-pointer cases, unsafe variants, and ABI-general footnote.

**Rust Reference:** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/types/function-pointer.md`, blob `08dfbbf235d752de592f4bdf79efa3d355c58eb8`, for bare function-pointer syntax, safety, and extern ABI qualifiers.
- `src/items/functions.md`, blob `362b39b5733c385a18e20a928d75f960f1cd427e`, for extern function definitions and the distinction from external-block declarations.

**Current native reference context:** the existing `rust-extern-foreign-items-nightly-2026-05-31` report at the observed `reference` tip distinguishes foreign declarations from Rust-defined extern functions and records Charon's representation of foreign items. It is adjacent evidence, not a substitute for this zerocopy-specific function-pointer inventory.

There is no fresh **execution** evidence in this package.

## Revalidation

For another zerocopy revision, the cheapest reliable revalidation is a narrow source and representation diff:

1. Search the exact `zerocopy/src` tree for `extern "`, foreign blocks, `#[link`, `#[link_name`, `core::ffi`, `std::ffi`, `libc::`, and C scalar/string types.
2. Diff `src/util/macros.rs` for the optional function-pointer type constructors.
3. Diff the corresponding section of `src/impls.rs` for `FromZeros`, `TryFromBytes`, `Immutable`, their validation predicates, and any newly supported ABIs.
4. Recheck `Cargo.toml` for newly introduced production FFI dependencies.
5. If `zerocopy-derive` remains part of the verification subject, repeat the direct FFI-marker search over its source.
6. At the exact Rust pin used by Anneal, recheck `core::option`'s function-pointer Option representation guarantee and the Reference's function-pointer ABI rules.
7. If the verification claim extends through Charon/Aeneas, add a minimal source fixture containing safe and unsafe `extern "C" fn` pointer values and `Option` wrappers, then preserve the emitted MIR/LLBC/Lean representations. Use zero and a concrete known function pointer as discriminators.
8. If a future zerocopy revision introduces a foreign block or native link attribute, stop treating this report's "type-level only" conclusion as applicable and inventory native item identity, ABI, symbol mapping, and foreign semantic assumptions separately.

A source search remains the best first discriminator because the current finding is structural: the production crate relies on an ABI-qualified pointer representation without owning a native foreign declaration.
