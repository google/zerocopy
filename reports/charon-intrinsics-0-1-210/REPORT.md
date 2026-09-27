# Charon intrinsics at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), “intrinsic” does not correspond to one LLBC representation or one support rule. Charon receives intrinsic behavior through several different rustc/MIR paths, and a downstream verifier must distinguish them.

For an item that rustc identifies as an intrinsic with `tcx.intrinsic(def_id)`, Charon normally preserves the function declaration, signature, generic constraints, item identity, intrinsic name, and argument names, but replaces the body with `Body::Intrinsic { name, arg_names }`. The marker says which compiler intrinsic the item denotes; it does not encode that intrinsic's operational semantics. Checked-in output at this revision shows this form for intrinsics including `ctpop`, `size_of`, `align_of`, and `cold_path`.

Charon gives a few operations stronger dedicated representations. `core::intrinsics::type_id` is special-cased into a generated body that returns `ConstantExprKind::TypeId(T)`. A late resugaring pass recognizes `offset_of` calls with the expected constant ADT/variant/field arguments and rewrites them to `NullOp::OffsetOf`. MIR non-diverging intrinsic statements are translated directly: `assume(cond)` becomes an assertion whose failure is `AbortKind::UndefinedBehavior`, while `CopyNonOverlapping` becomes a dedicated `CopyNonOverlapping` statement in both ULLBC and LLBC. Other compiler-lowered operations can likewise survive as ordinary Charon IR rather than as an intrinsic body marker; examples include transmute casts and pointer-offset binary operations.

The practical rule is therefore not “Charon supports intrinsic X.” For each intrinsic-relevant operation, a consumer must ask which representation reaches Charon at this rustc pin: a named but semantically opaque intrinsic body, a dedicated Charon operation, a Charon-generated synthetic body, an ordinary translated library wrapper around one of those operations, or no usable representation. This distinction is especially important for Anneal: a named `Body::Intrinsic` is evidence that the operation was recognized, not evidence that its Rust semantics or UB preconditions have been modeled downstream.

No fresh rustc or Charon execution was performed in this run. The report uses pinned Charon source plus checked-in golden outputs produced by Charon's upstream test suite.

## Applicability

This report applies to:

- repository `AeneasVerif/charon`;
- revision `a535e914f74db4fd9e6be7048f4233270d8945c0`;
- Charon version `0.1.210`;
- its pinned Rust toolchain `nightly-2026-05-31`.

The report covers how this Charon revision represents rustc-recognized intrinsic functions and MIR operations that originate from or implement intrinsic behavior. It does not assert that every Rust intrinsic is reachable from every source-level API, nor that Charon or a downstream consumer implements the semantics of every `Body::Intrinsic` name.

The set of functions for which the ordinary item translator chooses `Body::Intrinsic` is coupled to this rustc revision because Charon asks `TyCtxt::intrinsic` rather than maintaining an independent closed list in that translation path. Source-level library functions may instead have ordinary MIR bodies containing intrinsic operations; `core::ptr::copy_nonoverlapping` in the pinned checked-in fixture is an example.

## Findings

### Ordinary rustc intrinsic declarations become named intrinsic bodies

When translating a function item, Charon asks rustc `tcx.intrinsic(def_id)` for an intrinsic descriptor. It takes the intrinsic's name and, except for the `type_id` special case, constructs:

```text
Body::Intrinsic { name, arg_names }
```

The surrounding `FunDecl` still carries the translated signature, generics, item metadata, and identity. `Body::Intrinsic` itself carries only the intrinsic name and argument names. Its AST documentation calls it a “Rust intrinsic function,” and the pretty-printer renders it as `<intrinsic:name>`.

This is a semantic boundary, not merely a formatting choice. The ordinary intrinsic-body marker does not contain a Charon expression tree implementing the intrinsic. A consumer that needs operational semantics must recognize the intrinsic name and supply or reject the missing semantics itself.

Basis: Charon **source**.

### The recognized intrinsic set is inherited from rustc

Charon's ordinary intrinsic-item branch is selected by `tcx.intrinsic(def_id)`. The translator does not first compare the definition against a Charon-owned table of intrinsic names. The recognized set and the DefIds carrying intrinsic status are therefore rustc/toolchain-sensitive.

Charon does still special-case individual names after rustc identifies an intrinsic, most notably `type_id`. That does not change the ownership of the initial classification.

Basis: Charon **source** + **derived** toolchain-coupling consequence.

### Checked-in output preserves named markers for `ctpop`, `size_of`, `align_of`, and `cold_path`

The pinned `copy_nonoverlapping.out` fixture contains declarations such as:

```text
pub fn ctpop<T>(x_1: T) -> u32 ...
= <intrinsic:ctpop>

pub fn size_of<T>() -> usize ...
= <intrinsic:size_of>

pub fn align_of<T>() -> usize ...
= <intrinsic:align_of>
```

The pinned pointer-offset fixture similarly includes:

```text
pub fn cold_path()
= <intrinsic:cold_path>
```

These golden outputs confirm that source-visible calls may remain calls to a function whose body is only the named intrinsic marker. In the same output, ordinary library wrappers can use those markers as callees.

Basis: checked-in upstream **execution** fixtures.

### `type_id` is translated to a synthetic Charon body

`type_id` is the explicit exception in the ordinary intrinsic-item branch. `build_type_id_body` extracts the first translated type argument and returns an unstructured Charon body that assigns:

```text
ConstantExprKind::TypeId(type_id_ty)
```

to the return place.

`ConstantExprKind::TypeId(Ty)` is a dedicated constant-expression variant documented as “The `TypeId` value for a type.” A downstream consumer therefore receives a structured Charon operation for `type_id`, not only `<intrinsic:type_id>`.

Basis: Charon **source**.

### `offset_of` is reconstructed from a call into a dedicated nullary operation

The pass named `resugar::reconstruct_intrinsics` currently recognizes calls whose translated callee has lang item `offset_of`. It requires:

- the first type argument to be an ADT;
- the two call arguments to be literal `u32` variant and field IDs;
- the translated type declaration to be available.

For a struct, it discards the variant ID; for an enum it converts that ID to a `VariantId`. It then replaces the call with an assignment of:

```text
Rvalue::NullaryOp(
    NullOp::OffsetOf(type_ref, optional_variant, field_id),
    usize,
)
```

and replaces the call terminator with a `goto` to the normal target.

The pass is deliberately narrow. Its own TODO asks whether related operations such as `size_of` and `align_of` should also move into such a pass; at this revision, checked-in output still shows `size_of` and `align_of` as named intrinsic function bodies in relevant library code.

Basis: Charon **source** + checked-in upstream **execution** fixtures.

### MIR `assume` becomes an explicit UB-producing assertion

Rustc MIR represents non-diverging intrinsic statements separately from ordinary function calls. Charon translates:

```text
mir::StatementKind::Intrinsic(
    mir::NonDivergingIntrinsic::Assume(op)
)
```

into a Charon assertion requiring `op == true`, with:

```text
on_failure: AbortKind::UndefinedBehavior
```

ULLBC's statement documentation explicitly notes that inlined assumes cause UB on failure. The operation therefore reaches Charon as a semantic assertion, not as a call to a `Body::Intrinsic` declaration.

Basis: Charon **source**.

### MIR `CopyNonOverlapping` becomes a dedicated LLBC statement

Charon translates MIR's non-diverging `CopyNonOverlapping { src, dst, count }` intrinsic statement into `StatementKind::CopyNonOverlapping` with those three operands. ULLBC and LLBC both define that statement and describe it as equivalent to `std::intrinsics::copy_nonoverlapping`; Charon does not model it as a function call because it cannot diverge.

The pinned `copy_nonoverlapping.rs` fixture calls the ordinary library API `ptr::copy_nonoverlapping`. Its checked-in LLBC shows the library wrapper's runtime UB-check path followed by:

```text
copy_nonoverlapping(copy src_1, copy dst_2, copy count_3)
```

This demonstrates the two layers clearly: a source-level library function can have a translated MIR body, and the compiler intrinsic used inside that body can appear as a dedicated Charon statement.

Basis: Charon **source** + checked-in upstream **execution** fixture.

### Compiler-lowered intrinsic behavior can appear as ordinary Charon IR operations

Not every operation with intrinsic-like Rust semantics remains labeled `Intrinsic` at the Charon boundary. This revision translates several relevant MIR operations directly into Charon IR:

- `mir::CastKind::Transmute` becomes `CastKind::Transmute(source_ty, target_ty)`;
- MIR pointer-offset binary operations become `BinOp::Offset`;
- rustc runtime-check operands become `NullOp::UbChecks`, `OverflowChecks`, or `ContractChecks`;
- pointer-metadata operations become Charon pointer-metadata projections;
- MIR `Unreachable` and `UnwindAction::Unreachable` become `AbortKind::UndefinedBehavior`.

Charon's AST documents `CastKind::Transmute` as reinterpreting bits exactly as `std::mem::transmute` does, and documents pointer `BinOp::Offset` as offsetting by the element-size-scaled count.

For a verifier, this means an intrinsic inventory based only on `Body::Intrinsic` names is incomplete. Some semantic obligations have already crossed into dedicated Charon nodes before serialization.

Basis: Charon **source**.

### Library wrappers can expose precondition checks separately from the primitive operation

The pinned `ptr-offset.out` fixture shows `core::ptr::const_ptr::{*const T}::offset` as an ordinary translated function. Its body conditionally runs a precondition-check helper when `ub_checks` is enabled, then performs a Charon pointer `offset` operation.

Likewise, the pinned `copy_nonoverlapping.out` fixture shows `core::ptr::copy_nonoverlapping` conditionally invoking a precondition-check helper and then emitting the dedicated `copy_nonoverlapping` statement.

These runtime-check branches are not a semantic substitute for modeling the primitive operation's UB conditions. The library's own diagnostic string says those checks are optional and cannot be relied on for safety. A downstream verifier that wants a Rust-level UB-freedom claim must therefore give the primitive Charon operation an adequate semantic/precondition model even when a translated library wrapper happens to contain a conditional runtime check.

Basis: checked-in upstream **execution** fixtures + **derived** consequence for verification coverage.

### One source-level concept can cross the rustc-to-Charon boundary in several forms

At this revision, the reusable taxonomy is:

1. **Named intrinsic body:** rustc marks an item intrinsic; Charon preserves a `Body::Intrinsic` name but no body semantics.
2. **Synthetic Charon body:** Charon recognizes an intrinsic and constructs a body, as for `type_id`.
3. **Resugared dedicated operation:** a translated call pattern is rewritten to a Charon operation, as for `offset_of`.
4. **MIR intrinsic statement:** rustc has already lowered the operation to a special MIR statement, as for `assume` and `copy_nonoverlapping`, and Charon maps it directly.
5. **Ordinary MIR operation:** rustc exposes the behavior through an ordinary MIR cast/binop/rvalue/terminator that Charon maps to an ordinary Charon node, as for transmute and pointer offset.
6. **Library wrapper around any of the above:** a public Rust API can translate as ordinary code whose body invokes one or more of these lower-level forms.

The category determines what a downstream consumer can recover and what semantics it must provide. A function's Rust name is not enough to infer the category.

Basis: Charon **source**, checked-in upstream **execution** fixtures, and **derived** synthesis.

## Boundaries

- No fresh rustc or Charon execution was performed on this surface.
- The checked-in `.out` files are upstream preserved execution/test evidence for the pinned revision, not observations produced by this run.
- This report does not enumerate every intrinsic name accepted by `nightly-2026-05-31`; rustc owns the ordinary intrinsic classification used by Charon.
- This report does not establish semantics for every `Body::Intrinsic` name. The marker preserves identity, not an implementation.
- The report does not claim that `size_of` and `align_of` are never represented as dedicated operations in every Charon context. It establishes that the inspected generic intrinsic declarations remain named intrinsic bodies in the checked-in fixture, while `NullOp` has `SizeOf` and `AlignOf` variants that can arise through other translation/constant paths.
- `offset_of` reconstruction is pattern-sensitive. Calls that do not meet the inspected ADT plus literal-variant/field pattern are not established here to become `NullOp::OffsetOf`.
- Runtime UB checks in translated core-library wrappers are optional Rust runtime checks. Their presence does not prove that a downstream intrinsic model is sound or complete.
- This report does not cover inline assembly, foreign bodies, unions, raw-pointer semantics as a whole, or the complete unsupported-Rust inventory; #3720 tracks those separately.
- This report records Charon's representation boundary, not the downstream Aeneas semantics of each intrinsic or operation. Aeneas may model, reject, approximate, or otherwise transform these forms separately.

## Evidence

**Primary subject:** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210, rust toolchain `nightly-2026-05-31`).

- `charon/src/bin/charon-driver/translate/translate_items.rs`, blob `7964644be017856c6d165545a67bd6ef06e0c85c`: intrinsic detection through `tcx.intrinsic`; `type_id` special case; ordinary `Body::Intrinsic` construction.
- `charon/src/ast/gast.rs`, blob `23044319a8f763d241912c5d693ed94cf597682f`: `Body::Intrinsic { name, arg_names }`, `Extern`, `Opaque`, `Missing`, and ordinary structured/unstructured bodies.
- `charon/src/bin/charon-driver/translate/translate_bodies.rs`, blob `c03ca8077f131a2ef701e9d27eaa9e69bb617124`: synthetic `type_id` body; MIR `Assume`, `CopyNonOverlapping`, transmute, pointer offset, runtime checks, pointer metadata, and unreachable handling.
- `charon/src/ast/expressions.rs`, blob `eeb2143c714ee8b429a59c2aaf9f097afb18a940`: `NullOp::{SizeOf, AlignOf, OffsetOf, UbChecks, OverflowChecks, ContractChecks}`, `CastKind::Transmute`, `BinOp::Offset`, `ConstantExprKind::TypeId`, and pointer-related expression forms.
- `charon/src/transform/resugar/reconstruct_intrinsics.rs`, blob `f13ec694f9802a02080abd98cb1155a51387c24d`: `offset_of` call recognition and replacement with `NullOp::OffsetOf`.
- `charon/src/transform/mod.rs`, blob `8d9ec016c3b6e42ba0cbac180546551d4a52587a`: placement of intrinsic reconstruction among ULLBC transformations.
- `charon/src/ast/ullbc_ast.rs`, blob `3c6179f10742b2ee82c8ca07e6d51be6c8dc7694`: ULLBC `CopyNonOverlapping` and UB-producing assertion representation.
- `charon/src/ast/llbc_ast.rs`, blob `40f29f8a4b19f98e929b5fe82b8a009d813120ad`: structured LLBC `CopyNonOverlapping` and assertion forms.

**Preserved upstream execution fixtures:**

- `charon/tests/ui/copy_nonoverlapping.rs` and `charon/tests/ui/copy_nonoverlapping.out`: ordinary `core::ptr::copy_nonoverlapping` wrapper, conditional UB-check path, dedicated `copy_nonoverlapping` statement, and named intrinsic bodies including `ctpop`, `size_of`, and `align_of`.
- `charon/tests/ui/ptr-offset.rs` and `charon/tests/ui/ptr-offset.out`: ordinary pointer-offset wrapper, `ub_checks`, dedicated pointer `offset`, transmute operations in helper code, and `<intrinsic:cold_path>`.
- `charon/tests/ui/simple/generic-offset-of.rs` and its checked-in `.out`: `offset_of` represented as a dedicated constant/nullary operation for generic ADTs.

No fresh **execution** evidence was produced in this run.

## Revalidation

For another Charon/rustc revision, first diff these narrow boundaries:

1. the intrinsic branch in `translate_items.rs`;
2. the `Body::Intrinsic` representation in `ast/gast.rs`;
3. `build_type_id_body` and MIR intrinsic/operation cases in `translate_bodies.rs`;
4. `transform/resugar/reconstruct_intrinsics.rs` and its position in `transform/mod.rs`;
5. the dedicated operations in `ast/expressions.rs`, `ullbc_ast.rs`, and `llbc_ast.rs`.

On a capable execution surface, run a compact fixture that exercises at least:

- a direct rustc intrinsic whose declaration remains a named `Body::Intrinsic`;
- `core::intrinsics::type_id`;
- `std::mem::offset_of!` for a struct and enum field;
- `core::intrinsics::assume` through accepted source/library code;
- `ptr::copy_nonoverlapping`;
- `mem::transmute`;
- raw-pointer `offset`;
- `size_of` and `align_of`.

Preserve the exact Rust input, rustc/Charon revisions, Charon flags, ULLBC and LLBC, diagnostics, and hashes. For each operation, classify the observed Charon form using the six categories above and compare it with the pinned report.

That probe establishes representation for the exercised operations. It does not establish complete intrinsic coverage, Rust semantic correctness, or downstream Aeneas/Anneal adequacy.
