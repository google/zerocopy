# Charon raw pointers and unsafe-operation preservation at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), raw pointers are first-class semantic values. Charon preserves raw-pointer pointee type and const/mut distinction, raw-borrow construction, raw-pointer dereference through places, pointer offset operations, fat-pointer metadata, raw-parts construction, and function-signature unsafety. Its checked-in outputs demonstrate those forms on the exact revision.

Charon does **not** preserve source `unsafe` authorization as a first-class body property. That information has already been consumed before MIR, and Charon generally carries the executable MIR operation instead. Raw-pointer dereference uses the same `ProjectionElem::Deref` as references and boxes; calls use ordinary call nodes; union access uses ordinary field projection. Recognizing why such an operation is safety-relevant therefore requires types, declarations, or other semantic context rather than an `unsafe-operation` bit on the node.

Some source safety distinctions are absent even from Charon's declaration model. `FunSig::is_unsafe` preserves `unsafe fn`, but `TraitDecl` and `TraitImpl` have no structural unsafe flag, and `GlobalDecl`/`GlobalKind` do not distinguish `static` from `static mut`. The checked-in `unsafe.rs` fixture makes the loss visible: its `unsafe trait` and `unsafe impl` print as an ordinary trait and impl, and its `static mut COUNTER` prints as `static COUNTER`. The operations performed through that static still expose raw-pointer mutability in the translated body. Source spans and `ItemMeta` source text may permit source-aware reconstruction; the semantic declaration nodes themselves do not encode these qualifiers.

Raw-pointer casts have another important loss boundary. rustc MIR variants for pointer-to-pointer casts, mut-to-const coercion, array-to-pointer coercion, function-pointer-to-raw-pointer casts, `PointerExposeProvenance`, and `PointerWithExposedProvenance` all map to one Charon `CastKind::RawPtr(source_ty, target_ty)`. Source and destination types remain, but the MIR cast reason does not. A downstream proof that distinguishes strict-provenance operations cannot recover that distinction from `CastKind::RawPtr` alone.

Charon does retain a narrower provenance distinction for constants: its constant translation distinguishes pointers into translated values from pointer-sized integer values with no provenance, and its raw-memory byte model can carry provenance referring to globals, functions, or an unknown source. Those constant forms should not be mistaken for a complete runtime pointer-provenance model.

For Anneal, the durable conclusion is that Charon provides useful semantic structure for raw-pointer operations but is not a complete inventory of Rust source unsafety or pointer-validity obligations. A Rust-level UB proof must interpret Charon operations together with the Rust semantic rules recorded elsewhere in this corpus and must explicitly account for distinctions Charon does not structurally preserve.

No fresh Charon or rustc execution was performed. Checked-in `.out` files at the exact Charon revision provide preserved upstream execution evidence; source inspection establishes how the translator and AST represent the relevant forms.

## Applicability

This report applies to:

- repository `AeneasVerif/charon`;
- revision `a535e914f74db4fd9e6be7048f4233270d8945c0`;
- Charon version `0.1.210`;
- embedded Rust toolchain `nightly-2026-05-31`.

It covers the #3720 subject **Charon raw pointers and unsafe operations**. “Unsafe operation” here means preservation of the Rust/rustc safety-relevant operation shape and authorization metadata at the Charon boundary. It does not mean that every operation discussed necessarily executes UB, or that every UB-relevant transition is syntactically unsafe.

The companion `rustc-mir-unsafe-operations-nightly-2026-05-31` report establishes what rustc MIR preserves after source unsafety checking. The `rust-validity-well-defined-execution-nightly-2026-05-31` and `rust-ub-and-operational-models-nightly-2026-05-31` reports establish the separate Rust semantic obligations around validity, provenance, aliasing, and UB. This report starts at Charon's input/output boundary rather than re-defining those rules.

## Findings

### Raw-pointer types preserve pointee type and const/mut distinction

`TyKind::RawPtr(Ty, RefKind)` is Charon's raw-pointer type. `RefKind` has `Mut` and `Shared` variants; `translate_types.rs` maps rustc/hax mutable raw pointers to `Mut` and const raw pointers to `Shared`.

That reused `RefKind::Shared` name should be read here as Charon's representation of `*const`, not as proof of Rust shared-reference aliasing semantics. Raw pointers remain a distinct `TyKind` from `Ref`.

Basis: Charon **source**.

### Raw borrows are explicit, while raw dereference is a generic place projection

`Rvalue::RawPtr { place, kind, ptr_metadata }` represents taking a raw pointer to a place. The translator maps MIR `Rvalue::RawPtr` to this form, including `RawPtrKind::{Mut, Const}`. Checked-in output for `&raw const a` and `&raw mut COUNTER` prints those raw-borrow forms directly.

Dereference is different. `ProjectionElem::Deref` covers a reference, box, or raw pointer. The checked-in `unsafe.rs` output represents raw-pointer dereference as `copy (*x_1)` with no separate unsafe-dereference marker. A consumer must inspect the projected place's base type to determine that this dereference is through a raw pointer.

This mirrors the rustc boundary recorded by the companion MIR report: source unsafety checking has already happened, and executable place semantics remain.

Basis: Charon **source** + checked-in **execution** evidence.

### Charon models raw fat-pointer metadata explicitly

Charon treats built-in pointers as an address plus metadata. `ProjectionElem::PtrMetadata` reads the metadata component. `Rvalue::RawPtr` carries a metadata operand, and the `insert_ptr_metadata` pass replaces translation-time placeholders by metadata computed from the referenced place.

MIR raw-pointer aggregate construction becomes `AggregateKind::RawPtr(pointee_ty, RefKind)`. With `--ops-to-function-calls`, Charon lowers that aggregate to the builtin `PtrFromParts` function. The checked-in `ptr-from-raw-parts` fixture shows final LLBC constructing a wide raw pointer with `@PtrFromPartsShared` and separately shows a raw borrow used as the data pointer.

This preserves the operational distinction between the data pointer and metadata, but it does not by itself establish whether either component satisfies Rust's validity or provenance requirements.

Basis: Charon **source** + checked-in **execution** evidence.

### Raw-pointer casts collapse several materially different MIR cast reasons

`CastKind::RawPtr` stores only source and destination types. In `translate_bodies.rs`, the following rustc MIR cases all map to that one Charon variant:

- `PtrToPtr`;
- `MutToConstPointer`;
- `ArrayToPointer`;
- `FnPtrToPtr`;
- `PointerExposeProvenance`;
- `PointerWithExposedProvenance`.

This is a semantic normalization boundary. The source and destination types can still distinguish many cases, such as pointer-to-integer versus integer-to-pointer, but the Charon node no longer records which rustc `CastKind` produced the conversion. In particular, Charon does not retain a structural tag distinguishing the two strict/exposed-provenance MIR cast variants from other raw-pointer casts.

The checked-in `ptr_no_provenance` fixture shows a null-pointer implementation as `cast<usize, *const T>(0)`, consistent with this generalized cast representation.

Basis: Charon **source** + checked-in **execution** evidence.

### Pointer offset remains a distinct operation

`BinOp::Offset` is Charon's pointer offset operation; its AST documentation defines the right operand as a count scaled by the pointee size. The checked-in `ptr-offset` fixture preserves `core::ptr::offset` as `_0 = copy self_1 offset copy count_2` and later dereferences the resulting raw pointer.

This gives a downstream semantics an explicit operation to interpret. It does not encode or prove the Rust preconditions for `offset`; those must come from the Rust-level contract/semantics. The same checked-in fixture includes rustc's optional UB precondition-check path, but the core semantic operation remains the Charon `offset` node.

Basis: Charon **source** + checked-in **execution** evidence.

### Function unsafety survives in signatures, but calls do not carry an unsafe-call marker

`FunSig` has `is_unsafe: bool`, and `translate_fun_sig` sets it from the hax/rustc function-signature safety. The checked-in `unsafe.rs` output therefore prints `core::ptr::read` and `core::intrinsics::assume` as `unsafe fn` declarations.

Calls themselves use the ordinary call representation. The fixture's call to `read` is an ordinary function call; its unsafety is recoverable by following the callee's function signature, not from a flag on the call node. Dynamic function-pointer types likewise carry a `FunSig`, so the safety property belongs to the callable type/signature rather than the call statement.

Basis: Charon **source** + checked-in **execution** evidence.

### Source unsafe-block authorization is not a first-class Charon body property

The `unsafe.rs` fixture contains explicit `unsafe { ... }` blocks around an unsafe call, raw-pointer dereference, mutable-static access, union-field access, and `assume`. Its final LLBC contains the translated operations but no corresponding block-safety regions.

That absence is expected from Charon's MIR-facing architecture. The pinned rustc report in this corpus establishes that MIR source scopes no longer contain the earlier HIR/THIR `Safe`/`BuiltinUnsafe`/`ExplicitUnsafe` mode. Charon translates those MIR operations rather than reconstructing source authorization regions.

Spans and source text can still support source correspondence. They are not equivalent to a semantic proof that an operation belonged to a particular user-written unsafe block.

Basis: checked-in **execution** evidence + related rustc **source** evidence already preserved in the corpus.

### Unsafe trait and unsafe impl qualifiers are absent from the semantic trait nodes

At this revision, `TraitDecl` records item metadata, generics, implied clauses, associated constants/types/methods, and an optional vtable. `TraitImpl` records the implemented trait, generics, implied trait proofs, associated items, methods, and an optional vtable. Neither structure has a safety field, and `translate_trait_decl` / `translate_trait_impl` construct those nodes without one.

The checked-in fixture is a direct discriminator: source `unsafe trait Trait {}` becomes `trait Trait<Self>`, and `unsafe impl Trait for () {}` becomes an ordinary `impl` in final LLBC.

This establishes loss in the semantic AST, not necessarily loss of every source clue. `ItemMeta` includes spans/source text that a separate source-aware layer may inspect.

Basis: Charon **source** + checked-in **execution** evidence.

### Static mutability is not a structural property of `GlobalDecl`

`GlobalKind` distinguishes `Static`, `ThreadLocal`, `NamedConst`, and `AnonConst`; `GlobalDecl` contains no separate static-mutability flag. In the checked-in unsafe fixture, source `static mut COUNTER: usize = 0` prints as `static COUNTER: usize`.

The body still exposes mutability where rustc has lowered an access: the same fixture takes `&raw mut COUNTER` and then reads and writes through the resulting raw pointer. A proof can therefore reason about the translated access path, but it must not infer declaration-level `static mut` merely from `GlobalKind::Static`.

As with unsafe traits, source metadata may support reconstruction outside the semantic declaration structure.

Basis: Charon **source** + checked-in **execution** evidence.

### Union-field access remains an ordinary field projection

The unsafe fixture's source reads a union field inside an unsafe block. Final LLBC contains the union declaration and represents the read as `copy (one_1).two`; there is no unsafe-union-read flag on the projection.

A consumer can classify the operation by resolving the base ADT as a union and the projected field. This is a recoverable semantic distinction, but it is contextual rather than local to the projection node.

Basis: checked-in **execution** evidence + Charon AST **source**.

### Selected UB-relevant MIR constructs become explicit Charon effects

When rustc presents `StatementKind::Intrinsic::Assume`, Charon translates it to an `Assert` whose failure action is `AbortKind::UndefinedBehavior`. MIR `TerminatorKind::Unreachable` likewise becomes a Charon abort with `UndefinedBehavior`. MIR `CopyNonOverlapping` gets a dedicated Charon statement.

These are examples where Charon does more than preserve generic syntax: it gives downstream consumers an explicit semantic operation or failure class. Their presence is phase-dependent because rustc may present related source operations in different MIR forms before or after intrinsic lowering.

Basis: Charon translator **source**.

### Constant pointers preserve a limited provenance distinction

Charon's constant representation has `PtrNoProvenance(u128)` for a pointer-sized value with no provenance. Its constant-evaluation bridge distinguishes a dereferenceable pointer from a raw address: a pointer into a value becomes a borrow/raw-borrow constant, while an uninterpretable pointer scalar becomes `PtrNoProvenance`.

The lower-level raw-memory representation can also store `Byte::Provenance`, whose provenance names a global, a function, or an unknown source. These forms record useful CTFE/constant-origin distinctions.

They are not a complete runtime provenance semantics. Runtime raw-pointer types and values do not carry an analogous general provenance object, and the cast translation described above collapses rustc's exposed-provenance cast categories.

Basis: Charon **source**.

### Anneal must separate Charon operation recovery from Rust proof obligations

For the pinned Charon boundary, an Anneal consumer can recover many safety-relevant operations from semantic context:

- raw dereference from `Deref` plus the base type;
- union access from `Field` plus the base ADT kind;
- unsafe calls from the callee/function-pointer signature;
- raw-borrow construction directly from `Rvalue::RawPtr`;
- pointer offset directly from `BinOp::Offset`;
- raw-parts construction and pointer metadata from explicit pointer forms;
- some UB effects from explicit abort/assert/intrinsic translations.

But it cannot treat Charon as a lossless source-unsafety map. Unsafe-block ownership, unsafe-trait/impl qualifiers, static mutability, and the exact rustc raw-pointer cast reason are not all first-class semantic properties at this revision.

The consequence is architectural rather than prescriptive: if an Anneal proof needs one of those distinctions, the pipeline must either derive it soundly from surviving semantic context, recover it through a separately justified source-correspondence channel, or make the missing fact an explicit boundary. Silently assuming that “Charon preserved unsafe” would overstate the evidence.

Basis: **derived** from the representation and preserved execution evidence above.

## Boundaries

- No fresh Charon, rustc, Aeneas, Lean, or runtime execution was performed.
- Checked-in `.out` files are preserved execution artifacts at the exact Charon revision; this run did not reproduce their commands or environment.
- This report describes Charon representation, not a complete Rust unsafe-code semantics. The Rust-level provenance, aliasing, validity, and UB authority boundaries are covered by separate corpus reports.
- It does not prove that Aeneas or another Charon consumer models every preserved raw-pointer operation soundly.
- It does not exhaust every pointer-related library API, intrinsic, MIR phase, or Charon transform.
- `ItemMeta` spans/source text may preserve source spellings that the semantic AST does not encode structurally. This report distinguishes “not a first-class semantic field” from “impossible to recover by any source-aware method.”
- `RefKind::Shared` on raw pointers is Charon's reused mutability/constness representation; this report does not assign shared-reference aliasing rules to `*const T`.
- The exact Rust meaning of pointer provenance is deliberately not inferred from Charon's AST. Charon's constant provenance forms and raw-pointer cast normalization are representation facts only.
- The `PointerExposeProvenance` / `PointerWithExposedProvenance` finding is based on the translator's explicit match arms. No fresh fixture was generated to compare those two MIR cases side by side.
- Inline/global assembly, FFI, unsafe fields, lifetime safety, drop semantics, and target-feature behavior have separate or still-open corpus subjects and are not folded into this report.

## Evidence

**Source — Charon identity and toolchain** at `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`:

- `charon/Cargo.toml`, blob `8c9936202e7bdbdaaefbc19305363da1ab6c0084`: package version `0.1.210`.
- `rust-toolchain`, blob `4e348edab20d6bd5b195e758afe20f9d8258a3e1`: `nightly-2026-05-31`.

**Source — Charon semantic AST** at the same revision:

- `charon/src/ast/types.rs`, blob `548be29762fdc4f4d1cd652537db6f54065ff6ee`: `RefKind`, `TyKind::RawPtr`, `FunSig::is_unsafe`, pointer metadata types.
- `charon/src/ast/expressions.rs`, blob `eeb2143c714ee8b429a59c2aaf9f097afb18a940`: generic `Deref`, `PtrMetadata`, `CastKind::RawPtr`, `BinOp::Offset`, constant pointer/provenance forms, `Rvalue::RawPtr`, and raw-pointer aggregate construction.
- `charon/src/ast/gast.rs`, blob `23044319a8f763d241912c5d693ed94cf597682f`: `GlobalKind`/`GlobalDecl`, `TraitDecl`, `TraitImpl`, and call operands.

**Source — Charon translation and transforms** at the same revision:

- `charon/src/bin/charon-driver/translate/translate_types.rs`, blob `35bef6ea79992c65ea934413765fa95f631274e6`: raw-pointer type translation and function-signature safety.
- `charon/src/bin/charon-driver/translate/translate_bodies.rs`, blob `c03ca8077f131a2ef701e9d27eaa9e69bb617124`: raw borrows, dereference/place translation, cast-kind normalization, pointer metadata access, raw-pointer aggregates, `Assume`, `CopyNonOverlapping`, and UB `Unreachable` translation.
- `charon/src/bin/charon-driver/translate/translate_items.rs`, blob `7964644be017856c6d165545a67bd6ef06e0c85c`: trait/impl construction without a structural safety field.
- `charon/src/bin/charon-driver/translate/translate_constants.rs`, blob `e0b037b340b3ef1b5316f7af472cd7632ba5e89b`: Charon constant pointer forms.
- `charon/src/bin/charon-driver/hax/constant_utils/uneval.rs`, blob `d913bf83ae332dacdbb3752fb48f1cf6cc2886a2`: CTFE pointer versus raw-address classification.
- `charon/src/transform/finish_translation/insert_ptr_metadata.rs`, blob `f4c4ef9437f16a50d574eff2391c31b4a78408be`: delayed raw/reference metadata insertion.
- `charon/src/transform/simplify_output/ops_to_function_calls.rs`, blob `5f8ae571538eeef5fa91fa2c3a914c1ca94f1c52`: raw-pointer aggregate lowering to `PtrFromParts`.

**Execution — checked-in golden fixtures** at the same revision:

- `charon/tests/ui/unsafe.rs`, blob `ac72e704d0688124eaeb39e9d81851bda6f218dc`, and `unsafe.out`, blob `cdc2bd8abaeb1c0b75f2a35bc6854d36d282ed5a`: unsafe calls, raw dereference, unsafe trait/impl, mutable static, union access, and `assume`.
- `charon/tests/ui/ptr-offset.rs`, blob `a49f7e2a6a6310e1e67ce751907bca17e868a9cc`, and `ptr-offset.out`, blob `2a506d150c09c9f247fddc010ebdf7ff0b159b6d`: pointer offset and subsequent dereference.
- `charon/tests/ui/ptr_no_provenance.rs`, blob `2921d82fa1f7f666f97ac8c49b2db457a996c674`, and `ptr_no_provenance.out`, blob `c5541c18e3b8fd54a6d00e6db21bcb6c83ad9bce`: integer-to-pointer/no-provenance null construction.
- `charon/tests/ui/simple/ptr-from-raw-parts.rs`, blob `3cde64ae5837d5a409533e8c834ab6d07caca035`, and `ptr-from-raw-parts.out`, blob `a60250a0c8a9db76af0b6d76ad125b130c36299e`: raw borrow plus wide raw-pointer construction through `PtrFromParts`.

**Related corpus evidence:**

- `rustc-mir-unsafe-operations-nightly-2026-05-31` establishes the source-unsafety-to-MIR boundary that Charon consumes.
- `rust-safety-boundary-completeness-nightly-2026-05-31` establishes why source unsafe operations are not a complete abstraction-invariant slice.
- `rust-validity-well-defined-execution-nightly-2026-05-31` and `rust-ub-and-operational-models-nightly-2026-05-31` establish the separate Rust validity/provenance/aliasing/UB boundary.

No evidence above is fresh **execution**.

## Revalidation

For a later Charon pin, first diff the smallest representation surface that controls these findings:

1. `TyKind::RawPtr`, `RefKind`, `FunSig`, `ProjectionElem`, `CastKind`, `BinOp`, `Rvalue`, `AggregateKind`, `GlobalKind`, `TraitDecl`, and `TraitImpl`;
2. raw-pointer and cast match arms in `translate_types.rs` and `translate_bodies.rs`;
3. trait/global construction in `translate_items.rs`;
4. constant pointer translation in `translate_constants.rs` and hax constant evaluation;
5. pointer-metadata and `PtrFromParts` transforms.

Then rerun the pinned-style fixtures for `unsafe.rs`, `ptr-offset.rs`, `ptr_no_provenance.rs`, and `ptr-from-raw-parts.rs`, preserving exact Charon/rustc revision, command, target, options, and output hashes.

Add one discriminator specifically for cast provenance: produce MIR cases containing `PointerExposeProvenance` and `PointerWithExposedProvenance` and compare the serialized/final Charon forms. If a later Charon revision adds distinct provenance-aware cast variants, this report's cast-normalization finding no longer applies unchanged.

Add another discriminator for source-safety metadata if Anneal begins depending on it: include an unsafe block, unsafe trait, unsafe impl, `static mut`, unsafe function pointer, raw dereference, and union field read, then test both semantic serialized data and any source-correspondence side channel. The relevant question is not whether pretty output contains the token `unsafe`; it is whether the exact fact Anneal intends to rely on is preserved under a documented, stable mapping.