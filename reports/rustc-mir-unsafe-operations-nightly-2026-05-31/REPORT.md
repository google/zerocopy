# Safety-relevant operations in rustc MIR at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, rustc checks source safety requirements before MIR construction. HIR distinguishes safe, compiler-generated unsafe, and user-provided unsafe blocks; THIR preserves that distinction; `check_unsafety.rs` combines the current safety context with each safety-relevant operation. MIR then represents executable semantics rather than carrying the source `unsafe { ... }` authorization as a first-class property.

Some facts remain explicit in MIR: raw borrows use `Rvalue::RawPtr`, function-scope assembly uses `TerminatorKind::InlineAsm`, selected intrinsics use dedicated MIR statements, function types retain a safety bit, and static-origin temporaries can retain `LocalInfo::StaticRef`. Other operations reuse generic forms: raw-pointer dereference is `ProjectionElem::Deref`, union-field access is `ProjectionElem::Field`, and unsafe calls use `TerminatorKind::Call`. Their significance comes from types and declaration metadata.

MIR source scopes do not contain the earlier HIR/THIR safety mode. Spans remain, but MIR structure alone does not say that a particular operation was authorized by a particular user-written unsafe block.

No fresh compiler execution was performed.

## Applicability

This report applies to Rust compiler `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, used by the Anneal-era `nightly-2026-05-31`, and Rust Reference `ad35aca481751a06afeb23820a672b0f3b11a476`.

An **unsafe operation** here is a language feature the pinned Reference excludes from Rust's safe subset. That classification is separate from whether a particular execution has undefined behavior.

## Findings

### Safety authorization is consumed before MIR

The Reference identifies raw-pointer dereference, mutable or unsafe external static access, union-field reads, unsafe calls, certain target-feature calls, unsafe trait implementation, unsafe extern declarations, and unsafe attributes as outside the safe subset.

HIR uses `BlockCheckMode` and `UnsafeSource`; THIR maps these to `BlockSafety::{Safe, BuiltinUnsafe, ExplicitUnsafe}`. The THIR unsafety checker uses `UnsafeOpKind` for unsafe calls, assembly, mutable/extern statics, unsafe fields, raw-pointer dereference, union access, target-feature calls, and related operations.

Basis: **normative** + **source**.

### Raw dereference and union access use generic MIR projections

THIR recognizes a raw-pointer dereference from the operand type. MIR lowering uses the generic `ProjectionElem::Deref`; therefore a consumer needs the base type to distinguish raw-pointer from reference dereference.

Likewise, MIR field lowering uses `ProjectionElem::Field`. Recognizing union access requires the base ADT/type metadata; the projection itself has no union-specific flag.

Raw-pointer creation is more explicit: `ExprKind::RawBorrow` lowers to `Rvalue::RawPtr(mutability, place)`.

Basis: **source**.

### Static access keeps some origin information

rustc represents a source static path as a static pointer/reference followed by a dereference. The THIR checker applies the mutable/external-static safety rule there.

For non-thread-local statics, MIR can retain `LocalInfo::StaticRef { def_id, is_thread_local }` on the temporary. Thread-local access has `Rvalue::ThreadLocalRef(DefId)`. `LocalDecl.local_info` is wrapped in `ClearCrossCrate`, so this compiler-internal provenance is not a promised downstream serialization interface.

Basis: **source**.

### Unsafe calls use the ordinary call terminator

THIR call checking reads the callee signature and required target features. MIR's `TerminatorKind::Call` has no unsafe-call flag.

Function type metadata still retains safety: `FnSigKind` packs the safety bit and `FnSig::safety()` exposes it. A rustc-aware consumer can recover the distinction from the callee type or declaration, but not from the call terminator alone. Target-feature safety similarly requires attribute/configuration metadata beyond the MIR call shape.

Basis: **source**.

### Function-scope assembly remains explicit

The pinned Reference distinguishes `asm!`, `naked_asm!`, and `global_asm!`. The MIR builder lowers function-scope assembly to `TerminatorKind::InlineAsm`, preserving the macro kind, template, operands, options, line spans, targets, and unwind behavior.

This is structural preservation, not an ISA semantics. `global_asm!` is a global item rather than the same function-body MIR terminator and requires separate accounting.

Basis: **normative** + **source**.

### Intrinsics are phase-sensitive

The MIR pipeline can initially represent compiler intrinsics as calls. `LowerIntrinsics` rewrites selected cases: `copy_nonoverlapping` and `assume` become dedicated `StatementKind::Intrinsic` forms, while several arithmetic intrinsics become MIR binary operations.

A consumer therefore cannot inventory intrinsic semantics with one phase-independent rule such as searching only for calls.

Basis: **source**.

### MIR source scopes do not retain the source safety mode

`SourceInfo` contains a span and `SourceScope`. `SourceScopeData` contains span, parent, inlining information, and crate-local lint-root data. These structures do not contain `BlockSafety`, `UnsafeSource`, or an equivalent safety-context field.

The explicit HIR/THIR distinction among safe, compiler-generated unsafe, and user-provided unsafe blocks therefore does not survive as a structural MIR source-scope property. Source spans may support later source-aware reconstruction, but that is not the same as preserving the boundary directly.

Basis: **source**.

### Downstream analysis must combine MIR forms with metadata

For this pin, safety-relevant MIR analysis needs operation shape plus types/declarations: `Deref` with its base type, `Field` with ADT metadata, static-origin information, `Call` with function signature/attributes, `InlineAsm`, and phase-specific intrinsic/operator forms.

This is **derived** from the representation. It is not a complete Rust verification semantics.

## Boundaries

- No fresh rustc, Charon, or MIR-dump execution was performed.
- Adjacent rustc revisions may differ.
- This report does not prove these forms are sufficient for sound Rust verification.
- It does not equate language-level unsafe operations with undefined behavior.
- It does not treat spans as a stable replacement for explicit safety-boundary metadata.
- It does not provide ISA semantics for assembly or a full `global_asm!` study.
- It does not exhaustively enumerate all compiler intrinsics.
- It does not establish Charon's representation of every operation described here.

## Evidence

**Normative — Rust Reference.** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`:

- `src/unsafety.md`, blob `7353bcc6004d74b9e8698c71c093b35eebe05a70`.
- `src/inline-assembly.md`, blob `230dee5515749230c87ca37d54b153dec7f9c5ab`.

**Source — rustc** at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`:

- `compiler/rustc_hir/src/hir.rs`, blob `59d1b4b5576ee47ea6c994977d40d5a948f139ce`.
- `compiler/rustc_mir_build/src/thir/cx/block.rs`, blob `ea27252ad6ce8f325fc6021cdbf8d7f82f67048c`.
- `compiler/rustc_mir_build/src/check_unsafety.rs`, blob `f99d8934aa7fa8944e2906c2719e1eb4356c3c09`.
- `compiler/rustc_mir_build/src/thir/cx/expr.rs`, blob `b32d7dce4f4d3fae770d105b51c65810e3b1096d`.
- `compiler/rustc_mir_build/src/builder/expr/as_place.rs`, blob `e92f74722626b0fd77c6e7ef81f1115033d60057`.
- `compiler/rustc_mir_build/src/builder/expr/into.rs`, blob `c9aae29cabc533b609663297afbd83fbe6da3b69`.
- `compiler/rustc_mir_build/src/builder/expr/as_temp.rs`, blob `55296c647c819aecf79f640e8ab370d5b834aba8`.
- `compiler/rustc_middle/src/mir/syntax.rs`, blob `07eaa085fabc9742d0d51c73eeba91dcc9e67d2e`.
- `compiler/rustc_middle/src/mir/mod.rs`, blob `57c2883ef42e45952f42bb2213c59e3a19b8f959`.
- `compiler/rustc_type_ir/src/ty_kind.rs`, blob `6f3cea27cafdb097b120c4141c8acd4ca6d58e36`.
- `compiler/rustc_mir_transform/src/lower_intrinsics.rs`, blob `fe53d301c5574101399b60d38451a57b24c43535`.

No evidence above is fresh **execution**.

## Revalidation

For a future pin, diff the HIR/THIR safety modes, `check_unsafety.rs`, MIR operation variants, source-scope data, local static metadata, function-signature safety, and `lower_intrinsics.rs`. In particular, check whether MIR source scopes gain an explicit safety-context field and whether the intrinsic-lowering set changes.

A later executable probe can compare one preserved fixture's MIR at built, analysis/post-cleanup, and downstream-consumed phases. Preserve exact compiler revision, target, edition, command, and artifact hashes; use the probe to validate representation shape, not as proof of semantic completeness.
