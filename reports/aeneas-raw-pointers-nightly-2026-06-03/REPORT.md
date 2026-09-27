# Aeneas raw pointers at nightly-2026.06.03

## Summary

At Aeneas `nightly-2026.06.03` (`ac9f1bc5262a5e4ff1e24ca78617121382202727`), raw pointers are **representable at type and interface boundaries but do not have a general memory semantics**. Aeneas can carry Charon raw-pointer types into its pure AST and Lean output, and some library models mention raw pointers in their signatures. That support must not be confused with support for Rust raw-pointer execution.

The pinned implementation fails explicitly on raw-pointer dereference, rejects aggregate/raw-pointer construction paths that reach the symbolic interpreter, and does not dispatch Charon's direct `RawPtr` rvalue through the general rvalue evaluator. Raw-pointer casts have narrow translation plumbing, but at this revision the Lean primitive they target always returns `fail .undef`; the implementation itself says the cast can be defined properly only after separation logic exists. The checked-in Lean raw-pointer regression fixture is marked `known-failure` and records an error at the first raw-pointer dereference.

Aeneas also contains higher-level models for some Rust APIs whose implementations use raw pointers. Those models can avoid exposing raw-pointer operations to the interpreter. This is a separate mechanism: it is a trusted or separately justified functional model, not evidence that Aeneas models addresses, allocation identity, provenance, pointer arithmetic, dereference, or aliasing. Anneal therefore cannot infer unsafe-Rust coverage merely because Charon preserved a raw-pointer type or Aeneas produced a Lean type for it.

## Applicability

This report applies to the Aeneas release selected by Anneal, `nightly-2026.06.03`, at commit `ac9f1bc5262a5e4ff1e24ca78617121382202727`. That revision's `charon-pin` selects Charon commit `a535e914f74db4fd9e6be7048f4233270d8945c0`. The raw-pointer input shapes discussed below are the Charon types consumed by that exact Aeneas revision.

The report focuses on the Lean backend because Anneal uses Lean. Where Aeneas's backend-independent pure AST is relevant, the report says so explicitly. The source also defines placeholder raw-pointer names for Coq and F*, but this report does not claim equivalent backend support: raw-pointer cast extraction is explicitly restricted to Lean at this revision.

No fresh Aeneas execution was performed. Behavioral evidence comes from the checked-in regression fixture and its checked-in expected output, both at the pinned Aeneas commit, plus direct source inspection. Claims about what the interpreter rejects are therefore source claims corroborated by preserved test output where noted, not results of a new run.

## Findings

### Raw pointers survive type translation as marker types

Aeneas does not erase a Charon raw-pointer type at the type boundary. `SymbolicToPureTypes.translate` maps Charon `TRawPtr (ty, RMut)` to the pure builtin `TRawPtr Mut`, and maps `RShared` to `TRawPtr Const`, preserving the translated pointee type as the builtin type's single type argument.

Basis: **source**.

This is deliberately only a marker-level representation. The definition of the pure builtin says raw pointers “don't make sense in the pure world,” explains that Aeneas needs to carry them because some declarations contain raw pointers in their signatures, and says the dedicated type exists to mark such pointers while ensuring the corresponding functions are not actually used in translation.

That comment is an important semantic boundary. The presence of `MutRawPtr T` or `ConstRawPtr T` in generated Lean establishes that Aeneas retained a raw-pointer-shaped interface. It does not establish an address-space model or executable pointer semantics.

For the Lean backend, the marker becomes:

```lean
structure RawPtr (T : Type) (M : Mutability) where
  v : T

abbrev MutRawPtr (T : Type) := RawPtr T .Mut
abbrev ConstRawPtr (T : Type) := RawPtr T .Const
```

The single `v : T` field is not a model of a Rust pointer address. The same file says Aeneas does not really use raw pointers yet, and its only cast primitive is explicitly a placeholder. In particular, this structure contains no allocation identity, numeric address, provenance, metadata, liveness, alignment, initialization state, or aliasing state.

Basis: **source + derived**. The absence claim is about this exact Lean representation; it is not a claim that such information never exists elsewhere in the toolchain.

### Dereference is a hard interpreter error

The symbolic interpreter has an explicit raw-pointer-dereference case before ordinary symbolic-value expansion:

```text
| Deref, _, TRawPtr _ ->
    error "Aeneas does not yet support dereferencing raw pointers."
```

The comment explains why this case is early: otherwise the interpreter would try to expand a symbolic raw pointer even though it cannot do so, producing a less useful error.

Basis: **source**.

The pinned regression fixture corroborates this boundary. `tests/src/raw_pointers.rs` is Lean-only and marked `known-failure`. Its first function obtains a pointer from a slice and evaluates `*ptr.add(1)`. The checked-in `raw_pointers.lean.out` records that Aeneas imports the LLBC and then reports:

> Aeneas does not yet support dereferencing raw pointers.

The diagnostic points at the dereference in the Rust fixture and at `InterpPaths.ml`.

Basis: **source + preserved execution artifact**. The `.lean.out` file is checked-in historical output, not a fresh execution performed for this report.

The regression matters because it demonstrates a fail-closed boundary for this concrete pattern: the raw pointer can exist long enough for Aeneas to reach the dereference, but Aeneas does not silently translate the dereference to ordinary functional access.

### Direct raw-pointer rvalues and aggregated raw pointers are not generally interpreted

Charon's LLBC has a `RawPtr` rvalue form. At this Aeneas revision, `eval_rvalue_not_global` dispatches `Use`, ordinary references, unary and binary operations, aggregates, and discriminant reads. It has no `RawPtr` case; every unrecognized rvalue falls through to an `Unsupported operation` error.

`InterpStatements` contains downstream assignment-synthesis scaffolding that recognizes the `RawPtr` variant, but that code runs only after `eval_rvalue_not_global` has successfully evaluated the rvalue. There is no evaluator branch here that makes a direct `RawPtr` rvalue succeed.

Basis: **source + derived**.

A separate aggregation path also rejects `AggregatedRawPtr` with the explicit error `Aggregated raw pointers are not supported yet`.

Basis: **source**.

These facts are narrower than “all raw-pointer construction fails.” A raw-pointer-typed symbolic value may still enter through an opaque or modeled call or another interface. The checked-in regression fixture reaches a raw-pointer dereference after calling slice pointer APIs, for example. The important distinction is that Aeneas has type/interface plumbing for raw pointers but no general interpreter semantics for constructing and manipulating them as Rust memory objects.

### Raw-pointer casts have translation plumbing, but the Lean model has no successful cast semantics

Aeneas recognizes one narrow class of raw-pointer cast in the symbolic-to-pure translation. Both source and target must be raw pointers whose pointee is a Charon literal type. The translation records source and target pointee types and mutabilities as `CastRawPtr`, and marks the cast as potentially failing.

Basis: **source**.

The extraction layer narrows support again. For `CastRawPtr`, it asserts that the backend is Lean. It emits a call to `RawPtr.cast_scalar`, and the target must be an integer scalar type. Other backends are not supported by this path, and HOL4 rejects raw-pointer casts explicitly.

Basis: **source**.

The Lean primitive does not implement Rust pointer casting:

```lean
-- TODO: we can properly define this once we have separation logic
def RawPtr.cast_scalar ... : Result (RawPtr T' M') :=
  .fail .undef
```

Thus the existence of a `CastRawPtr` node does not mean this Aeneas release can establish the result of a Rust raw-pointer cast. The accepted syntax is lowered to an operation whose model always fails. The TODO connects a real definition to future separation-logic support.

Basis: **source**.

This distinction is easy to lose in a compatibility matrix: “parser/translation path exists” and “pointer cast has a usable semantic model” are different facts. At this revision the former is partly true and the latter is not.

### Raw pointers are retained where API signatures require them

The Lean standard-library model uses `ConstRawPtr` and `MutRawPtr` in interface types. For example, the modeled `SliceIndex` trait includes `get_unchecked` and `get_unchecked_mut` methods that consume and return raw-pointer marker types.

Basis: **source**.

The concrete slice-index models do not supply pointer semantics for these methods. Representative `get_unchecked` and `get_unchecked_mut` implementations return `fail .undef` and state that Aeneas does not yet know the model or needs a more stateful computation model.

Basis: **source**.

This matches the pure-AST design comment: raw-pointer types need to survive so declarations remain expressible even when Aeneas does not execute the corresponding pointer operations.

### Higher-level Rust models can bypass raw-pointer implementation details

Aeneas's inability to interpret raw pointers does not imply that every Rust API implemented with raw pointers must be unusable. A library model can replace an implementation with a higher-level functional interface.

The pinned slice model illustrates the mechanism. `core::slice::Slice.get_unchecked` is registered as the model for Rust's slice `get_unchecked`, but its Lean signature takes the modeled slice and index directly and returns the modeled output. The source comments that it should actually use the `SliceIndexInst.get_unchecked` raw-pointer method; at this revision the body is instead admitted with `sorry`.

Basis: **source**.

This example has two consequences for Anneal:

1. A function whose Rust implementation performs raw-pointer operations can sometimes translate because Aeneas substitutes a higher-level model rather than executing those operations.
2. Such translation does not prove that the omitted raw-pointer implementation is sound or faithfully modeled. The justification comes from the model and its trust/proof status. In this specific example, the model body is admitted at the pinned revision.

The raw-pointer boundary is therefore not just a support/no-support switch. A future coverage analysis must distinguish at least three cases: code Aeneas rejects because raw-pointer execution reaches the interpreter, raw-pointer-shaped declarations retained only for interface compatibility, and Rust operations replaced by models that avoid the raw-pointer implementation.

### A raw-pointer type in Lean does not preserve Rust pointer identity or provenance

The generated Lean marker contains the pointee type, mutability marker, and a placeholder `v : T` payload. The inspected raw-pointer translation contains no representation of allocation identity, byte address, provenance, exposed-address state, pointer arithmetic history, alignment proof, initialized-byte state, or aliasing/borrowing relation.

Basis: **source + derived**.

This is the precise reason Anneal must not treat the marker as a Rust memory model. A proof about a `RawPtr T M` value can be meaningful only relative to whatever higher-level model produced it and the assumptions of that model. It cannot, from this representation alone, establish the Rust conditions that make an arbitrary raw-pointer dereference well-defined.

This report does not claim those facts are all absent from Charon. The conclusion is about what survives into and is given semantics by the inspected Aeneas pure/Lean representation.

### The current boundary is intentionally connected to richer memory reasoning

The strongest source comment on future direction is in `RawPtr.cast_scalar`: the cast can be defined properly once Aeneas has separation logic. Slice unchecked-access models likewise mention needing a more stateful computation model.

Basis: **source**.

These comments do not define a finished design, but they explain why the current marker representation is insufficient. Pointer semantics need memory/resource state that ordinary value-level functional translation does not carry.

For Anneal, this is a concrete example of the project principle that a proof boundary may simplify only when it preserves all semantics relevant to the promise. UB-freedom for general unsafe pointer code cannot be justified by the current value-level raw-pointer marker alone.

## Boundaries

**No fresh execution.** This report did not run Aeneas, Charon, Lean, or the regression fixture. The checked-in `raw_pointers.lean.out` is preserved upstream execution evidence at the pinned revision. Revalidation below gives the smallest useful fresh probe.

**Not a complete unsafe-Rust inventory.** This report isolates raw pointers. Unions, intrinsics, FFI, layout, transmute, and other unsafe-relevant mechanisms have separate support boundaries.

**Not a complete model inventory.** The slice models are representative evidence that raw-pointer-shaped APIs can be retained or replaced. This report did not enumerate every `rust_fun`, external model, or opaque function whose Rust implementation may use raw pointers.

**No claim that `fail .undef` is Rust undefined behavior.** It is Aeneas's modeled failure result in the inspected definitions. The important fact is that these definitions do not provide a successful pointer-operation semantics.

**No claim that `RawPtr.v` denotes the pointee in Rust.** Treating the placeholder field as an actual dereference result would contradict the implementation's own boundary comments and explicit dereference rejection.

**No adjacent-version continuity.** Newer Aeneas revisions have continued raw-pointer and separation-logic development. None of those changes are imported into this report merely because they are nearby in history.

**Backend scope.** The type-marker abstraction exists across backends, but the inspected cast extraction is Lean-only. Anneal's relevant backend is Lean; this report does not establish equivalent F*, Coq, or HOL4 operational behavior.

**Model trust is a separate question.** The admitted `slice::get_unchecked` model is relevant because it bypasses raw-pointer implementation details, but the general semantics of `sorry`, axioms, and Aeneas's trusted base belong to their own reference subjects.

## Evidence

All Git source below is from `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` unless stated otherwise.

- **source** — `charon-pin`, pinning Charon `a535e914f74db4fd9e6be7048f4233270d8945c0`:
  https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/charon-pin
- **source** — `src/pure/Pure.ml`, `builtin_ty::TRawPtr`: raw pointers are marker types retained for signatures, not modeled pure values:
  https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/pure/Pure.ml#L83-L98
- **source** — `src/symbolic/SymbolicToPureTypes.ml`, raw-pointer type translation:
  https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/symbolic/SymbolicToPureTypes.ml#L161-L177
- **source** — `backends/lean/Aeneas/Std/RawPtr.lean`: Lean marker representation and always-failing scalar cast placeholder:
  https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/backends/lean/Aeneas/Std/RawPtr.lean
- **source** — `src/interp/InterpPaths.ml`, explicit raw-pointer dereference rejection:
  https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/interp/InterpPaths.ml#L110-L116
- **source** — `src/interp/InterpExpressions.ml`, general rvalue dispatcher and aggregated raw-pointer rejection:
  https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/interp/InterpExpressions.ml#L1311-L1321
  https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/interp/InterpExpressions.ml#L1421-L1442
- **source** — `src/symbolic/SymbolicToPureExpressions.ml`, narrow raw-pointer-cast lowering:
  https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/symbolic/SymbolicToPureExpressions.ml#L549-L589
- **source** — `src/extract/Extract.ml`, Lean-only raw-pointer cast extraction to `RawPtr.cast_scalar`:
  https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/extract/Extract.ml#L508-L545
- **source** — `backends/lean/Aeneas/Std/Slice.lean`, raw-pointer-bearing `SliceIndex` methods, failing unchecked-index models, and the higher-level admitted `Slice.get_unchecked` model:
  https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/backends/lean/Aeneas/Std/Slice.lean#L341-L369
  https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/backends/lean/Aeneas/Std/Slice.lean#L398-L408
  https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/backends/lean/Aeneas/Std/Slice.lean#L549-L559
- **source + preserved execution artifact** — Lean-only known-failure raw-pointer fixture and expected output:
  https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/tests/src/raw_pointers.rs
  https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/tests/src/raw_pointers.lean.out

The preserved fixture is particularly useful because it gives a cheap, stable discriminator for the most important boundary: if a newer Aeneas revision stops reporting the raw-pointer-dereference error, this report's central support characterization needs re-examination.

## Revalidation

For the same Aeneas revision, source identity is sufficient to revalidate this report: verify that the files and commit above are unchanged.

For a newer Aeneas revision, do these checks in order:

1. Read the new revision's `charon-pin`; do not assume the input raw-pointer representation stayed compatible.
2. Inspect `TRawPtr`/the equivalent raw-pointer pure type and the Lean raw-pointer primitive. Determine whether it is still a marker or now carries a real memory/resource semantics.
3. Inspect the interpreter's raw-pointer dereference, direct raw-pointer rvalue, aggregate, and cast paths. Record which cases reject, which produce proof obligations, and which use trusted models.
4. Run the existing `tests/src/raw_pointers.rs` Lean fixture and preserve exact output. If it no longer fails, add focused fixtures for read, write, pointer arithmetic, casts, null/dangling pointers, alignment, and aliasing.
5. Inspect representative standard-library models such as slice unchecked access. Distinguish operations proved through raw-pointer semantics from operations replaced by higher-level models.
6. If separation-logic support is now active, identify the exact state/resource representation and the proof obligation that connects it to Rust pointer validity, provenance, initialization, and aliasing rules.

The cheapest decisive probe is the existing raw-pointer known-failure fixture plus source inspection of `InterpPaths` and `RawPtr.lean`. A successful translation of that fixture would be a strong signal that the boundary moved, but it would not by itself establish complete unsafe-pointer semantics.