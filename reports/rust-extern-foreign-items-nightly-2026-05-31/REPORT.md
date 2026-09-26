# Rust `extern` declarations and foreign items at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, an item in an `extern` block is a Rust declaration with compiler identity, a Rust-visible type/signature, safety information, and an ABI boundary, but no Rust body. The Rust Reference describes these items as declarations of definitions provided elsewhere. A proof about Rust code can therefore rely on the Rust-side declaration only after making the foreign implementation's behavior an explicit model or trust assumption.

Rust item identity, ABI, and native import identity are separate. `#[link_name]`, Windows `raw-dylib` ordinals, and name-decoration policy can make the linker-facing identity differ from the Rust definition name.

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, Charon represents a foreign function as a `FunDecl` whose body is `Body::Extern(String)`. It preserves the fixed input/output types, safety bit, and ABI spelling. Source inspection also exposes two losses at this pin. `Body::Extern` receives the Rust definition-path name rather than rustc's effective `#[link_name]`/ordinal import identity. Separately, Charon's rustc-facing `TyFnSig` has `c_variadic`, but `translate_fun_sig` omits it and the exported `FunSig` has no variadic field.

No fresh compilation, linking, Charon extraction, or FFI execution was performed.

## Applicability

- Rust Reference: `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.
- rustc: `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`nightly-2026-05-31`).
- Charon: `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210).

This report concerns declarations inside `extern` blocks. A Rust-defined `extern "C" fn f() { ... }` still has a Rust body and is a different case.

The stable Reference page examined here specifies external functions and statics. rustc also represents foreign types; that compiler representation is not evidence that unstable `extern type` is a stable language feature.

## Findings

### The declaration is an interface, not an implementation

The Reference defines external blocks as declarations of items defined elsewhere. External functions have no body; external statics have no Rust initializer.

That means rustc can type-check uses of the declaration without possessing a Rust implementation to verify. Any semantic claim about what the callee or external object does needs a separate model, contract, or trusted premise.

**Evidence:** **normative**.

### Safety is a Rust-side permission boundary

An external function is implicitly unsafe unless declared `safe`; external statics are unsafe to access unless declared safe. For the 2024 edition the block itself is written `unsafe extern`.

Those qualifiers determine whether Rust requires an unsafe context. They do not inspect or prove the absent implementation. The Reference's external-static rules make this visible: foreign code controls initialization, so an invalid bit pattern may violate the Rust type; immutable external statics must be initialized before Rust executes and thereafter cannot be mutated except through `UnsafeCell`.

**Evidence:** **normative**.

### ABI and link identity are distinct from Rust item identity

The external block carries an ABI. Unwind-capable ABI spellings also determine whether unwinding may cross the boundary.

The Rust item separately has a compiler definition identity. `#[link_name]` can select another imported symbol; Windows `raw-dylib` can use `#[link_ordinal]` and target-specific decoration.

A durable verifier identity therefore cannot treat a source path as simultaneously the Rust semantic item, ABI, and native symbol.

**Evidence:** **normative** + rustc **source**.

### rustc preserves the declaration boundary explicitly

Pinned HIR represents the block as `ItemKind::ForeignMod { abi, items }`. Each `ForeignItem` is an HIR owner with its own `OwnerId`, span, identifier, and kind. `OwnerNode::body_id` has no foreign-item arm.

rustc's foreign-module metadata records each module `DefId`, ABI, and foreign-item `DefId`s. Separately, codegen attributes record `#[link_name]` in `CodegenFnAttrs.symbol_name` and `#[link_ordinal]` in `link_ordinal`; native-library construction consults those values.

Thus semantic item identity and linker import identity are separately represented in rustc.

**Evidence:** rustc **source**.

### C-variadicness is semantic boundary information

The Reference permits `...` only for selected C-family foreign ABIs and warns that incorrect variadic arguments can cause undefined behavior. Pinned rustc also consults the variadic bit for some target-specific calling-convention choices.

Variadicness is therefore not presentation-only syntax.

**Evidence:** **normative** + rustc **source**.

### Charon marks foreign functions, but its extern string is not linker-complete

Pinned Charon has `Body::Extern(String)` and retains `FunSig` plus item metadata. `FunSig` preserves safety, ABI spelling, fixed inputs, and output.

`extern_item_symbol_name` derives the `Body::Extern` string from the final Rust definition-path component. The inspected pinned Charon source has no `link_name` handling, while pinned rustc stores effective link name and ordinal elsewhere. Therefore `Body::Extern` is not sufficient evidence for the actual native import identity when those attributes alter it.

This does not claim Charon is intended to perform linking; the string may be a model-facing name.

**Evidence:** Charon and rustc **source** + **derived** comparison.

### Pinned Charon drops C-variadicness

Charon's rustc-facing `TyFnSig` contains `c_variadic: bool`. The exported `FunSig` does not. `translate_fun_sig` copies safety, ABI, inputs, and output while omitting `c_variadic`.

Two otherwise matching signatures that differ only in C-variadicness are therefore indistinguishable in exported `FunSig` at this exact revision.

**Evidence:** Charon **source** + **derived** comparison.

### Verification must make foreign behavior explicit

Rust/rustc establish the Rust-facing declaration and native-call boundary; Charon retains part of it. None of this establishes what the external implementation does. A Rust-level proof that crosses an extern call must therefore identify the model or trusted assumption supplying those semantics.

**Evidence:** **derived**.

## Boundaries

- No fresh compiler, linker, Charon, or runtime experiment was performed.
- No foreign implementation is proved correct here.
- C/C++ semantics, dynamic-loader semantics, and detailed per-target ABI lowering are out of scope.
- `Body::Extern` is not claimed to be intended as a linker key.
- The C-variadic loss is established only for this pinned Charon revision; downstream compensation was not established.
- `extern type` is not treated as stable-language behavior.
- Detailed panic/unwind behavior belongs to the separate panic/unwind report.
- No Anneal architecture or foreign-model policy is selected.

## Evidence

**Normative:** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/items/external-blocks.md`, blob `e1704556b5f000c019cd04df63e7e04692454c42`.
- `src/items/functions.md`, blob `362b39b5733c385a18e20a928d75f960f1cd427e`.

**Source:** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `compiler/rustc_hir/src/hir.rs`, blob `59d1b4b5576ee47ea6c994977d40d5a948f139ce`: foreign modules/items and body lookup.
- `compiler/rustc_hir/src/def.rs`, blob `d275d5a28b88ad73141b684a70c43ca661db809d`: `ForeignMod`/`ForeignTy`.
- `compiler/rustc_metadata/src/foreign_modules.rs`, blob `8a6b2027083d600ab3fbd5c214b92c53cd17b789`: module ABI and item identities.
- `compiler/rustc_codegen_ssa/src/codegen_attrs.rs`, blob `b4626724fd803a3d8bdd021027e7629370b3f6c1`: link name/ordinal attributes.
- `compiler/rustc_metadata/src/native_libs.rs`, blob `b64cb8843ed713f6aa036010aa4a987e045c8eb9`: native import construction.

**Source:** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

- `charon/src/ast/gast.rs`, blob `23044319a8f763d241912c5d693ed94cf597682f`: `Body::Extern` and `FunDecl`.
- `charon/src/ast/types.rs`, blob `548be29762fdc4f4d1cd652537db6f54065ff6ee`: exported `FunSig` and `Abi`.
- `charon/src/bin/charon-driver/hax/types/ty.rs`, blob `470ed2ff4d992efe30f8c4a09a3676111f304003`: rustc-facing `TyFnSig`, including `c_variadic`.
- `charon/src/bin/charon-driver/translate/translate_types.rs`, blob `35bef6ea79992c65ea934413765fa95f631274e6`: `translate_fun_sig`/`translate_abi`.
- `charon/src/bin/charon-driver/translate/translate_meta.rs`, blob `187a703dff83687f369f1903c6646aabdff259d3`: extern recognition and definition-path-derived extern name.
- `charon/src/bin/charon-driver/translate/translate_items.rs`, blob `7964644be017856c6d165545a67bd6ef06e0c85c`: `Body::Extern(name)` construction.

No evidence above is fresh **execution**.

## Revalidation

On a later pin, first diff the exact source surfaces above. Check whether exported Charon `FunSig` retains variadicness and whether foreign identity consults effective link-name/ordinal metadata.

On an execution-capable surface, compile one minimal fixture with unsafe and `safe` foreign functions, foreign statics, `#[link_name]`, a supported C-variadic declaration, and paired `C`/`C-unwind` declarations. Where practical on Windows, add a `raw-dylib` ordinal case. Preserve compiler/Charon commands, target triple, compiler representation, native import evidence, serialized Charon output, and hashes.

Compare Rust item identity/source name, safety, ABI, variadicness, effective imported name or ordinal, and Charon `FunSig`/`Body::Extern`. Use an unrenamed non-variadic C declaration as control. This establishes representation for the tested revisions/targets, not foreign semantic correctness.
