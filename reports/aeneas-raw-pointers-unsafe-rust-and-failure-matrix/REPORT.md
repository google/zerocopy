# Aeneas Raw Pointers, Unsafe-Rust Semantic Omissions, Support and Failure Matrix, Panic/Unwind Erasure, Post-Monomorphization Guards, and Nested-Borrow Boundaries

## Summary

At the Aeneas release selected by Anneal (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `nightly-2026.06.03`, paired with `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `0.1.210`, on `rustc` `nightly`), Aeneas's ordinary functional backend targets a structured subset of safe Rust and deliberately omits, rejects, or abstracts the operational dimensions required by general unsafe or concurrent Rust:

1. **Raw pointers as non-operational signature markers (`Pure.ml`, `RawPtr.lean`, `InterpPaths.ml`, `InterpExpressions.ml`)**: Charon raw-pointer types (`TRawPtr (ty, RMut | RShared)`) survive type translation into Aeneas's pure AST (`TRawPtr Mut | Const`) and Lean output (`MutRawPtr T`, `ConstRawPtr T` defined via `structure RawPtr (T : Type) (M : Mutability) where v : T`) solely so external and standard-library function signatures containing raw pointers can be represented. They carry no address space, allocation identity, provenance, alignment, initialization state, or aliasing relation. Symbolic execution fails closed on raw-pointer dereference (`InterpPaths.ml`: `"Aeneas does not yet support dereferencing raw pointers"`, preserved in `tests/src/raw_pointers.lean.out`), rejects `AggregatedRawPtr` (`"Aggregated raw pointers are not supported yet"`), leaves direct `RawPtr` rvalues unhandled in `eval_rvalue_not_global`, and lowers narrow literal-pointee `CastRawPtr` nodes (Lean-only in `Extract.ml`) to `RawPtr.cast_scalar`, which unconditionally returns `.fail .undef` pending future separation-logic support. Standard-library traits (`SliceIndex.get_unchecked` / `get_unchecked_mut`) likewise return `fail .undef`, while higher-level APIs (`core::slice::Slice.get_unchecked`) bypass raw-pointer execution by substituting a modeled (and at this pin `sorry`-admitted) functional specification.
2. **Semantic omissions across memory resources, effects, destructors, I/O, concurrency, and environment (`Pure.ml`, `FunsAnalysis.ml`, `Config.ml`, `Io.lean`, `Atomic.lean`)**: Because ordinary references (`&T`, `&mut T`) and `Box<T>` functionalize into pure values and backward functions, the proof-facing model omits allocation identity, reference identity, Rust pointer provenance (Aeneas's internal `mplace` metadata records only source/symbolic naming origin), and partial byte-initialization heap state. `Pure.fun_effect_info` tracks only `can_fail`, `can_diverge`, and `is_rec` (after a coarse LLBC `stateful` bit in `FunsAnalysis.ml`), omitting I/O traces, destructor side effects (`Config.drop_as_no_op = true` turns LLBC `Drop` statements into immediate `Unit` unless `-eval-drops` is enabled), concurrent schedules, and atomic memory ordering (`AtomicBool` and `AtomicU32` are axiomatic types with TODO markers). Concrete library models reinforce these abstractions: `std::io::stdio::_print` returns `.ok ()` while discarding output, and `Pure.GetTarget` is an axiomatized fallible compilation-target query rather than a general nondeterminism model.
3. **Three-layer support and failure matrix and diagnostic fail-closedness (`Errors.ml`, `Translate.ml`, `Main.ml`, `run_test.ml`)**: Practical support requires passing Charon (`charon cargo --preset=aeneas`, enforced in `src/Main.ml`), Aeneas symbolic execution and functionalization, and Lean type-checking. While 12+ checked-in positive fixture families (`Scalars.lean`, `Adt.lean`, `Arrays.lean`, `NoNestedBorrows.lean`, `NestedBorrows.lean`, `Loops.lean`, `Traits.lean`, `Closures.lean`, `Dyn.lean`, `Constants.lean`, `Static.lean`, `Drop.lean`) establish supported shapes, Aeneas hard-rejects function-pointer calls (`FnOpDynamic`), `binop::offset`, `transmute`, raw-pointer dereference, and outer-loop exits from nested loops. Internally, `Errors.ml` and `Translate.ml` catch `CFailure` per declaration and omit failed items while continuing analysis, but `Main.ml` exits with status `1` whenever `error_list` is non-empty (and `-abort-on-error` sets `fail_hard = true`). By contrast, `Config.warnings_as_errors` defaults to `false`, so warning-level soundness hazards—most notably unlifted associated types on mutually recursive traits (`tests/src/mutually-recursive-traits.lean.out`)—require `-warnings-as-errors` to fail closed.
4. **Panic, abort, and unwind erasure (`ullbc_to_llbc.rs`, `InterpStatements.ml`, `PureMicroPassesGeneral.ml`, `WP.lean`)**: During ULLBC-to-LLBC structuring (`charon/src/transform/control_flow/ullbc_to_llbc.rs`), Charon rewrites `UnwindResume` to `Abort(AbortKind::Panic(None))`, drops normal `Call` `on_unwind` cleanup edges, and summarizes assertion unwind blocks into `on_failure: AbortKind`. Aeneas's `InterpStatements.eval_statement` matches `Abort _` without inspecting `AbortKind`, collapsing `Panic`, `UndefinedBehavior`, and `UnwindTerminate` into one symbolic `SA.Panic` channel (`Result.fail .panic`), while `FunsAnalysis.ml` forces `can_fail = true` for ordinary functions. Pure micro-passes (`intro_massert_visitor` in `PureMicroPassesGeneral.ml`) further rewrite `if b then e else fail panic` into `massert b; e` (`Error.assertionFailure`), and `Aeneas.Std.WP.spec` maps both `spec (fail e) p` and `spec div p` to `False` regardless of the error tag `e`.
5. **Post-monomorphization errors (PMEs) at the Charon/Aeneas boundary (`zerocopy`, `charon/src/options.rs`, `Constants.lean`)**: Zerocopy (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`) relies on PMEs via `static_assert!` (`StaticAssert::ASSERT` associated constants evaluated after monomorphization in `try_transmute`, reference transmutations, and `layout::CastFrom::project`) as compile-time admission guards for unsafe operations. Because Aeneas requires `Preset::Aeneas` (`charon/src/options.rs`), which leaves `monomorphize = false` (unlike `Preset::Soteria`) and extracts polymorphic `mir_promoted` bodies, Aeneas translates generic constants symbolically (`Constants.lean`, `ConstantsLean.lean`) without encoding `rustc`'s post-monomorphization accepted-instantiation set. Sound verification must therefore either prove the stronger polymorphic theorem or carry an explicit admission premise (`P<T>`); Charon's optional `--monomorphize` mode is an unverified candidate bridge.
6. **Nested-borrow support and the historical Hermes flaky fixture (`42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4` vs. `ac9f1bc5262a5e4ff1e24ca78617121382202727`)**: The historical `known_flaky` nested-reference fixture (`pub fn nested(x: &&u32, y: &mut &u32, z: &&mut u32)` in `google/zerocopy@9bdef60f295715bc113419661b376071cc18e2b3`) was observed under Hermes's April 2026 Aeneas pin (`42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`) and does not preserve a failing Aeneas traceback in `expected.stderr`. Anneal's June 3 pin (`ac9f1bc5262a5e4ff1e24ca78617121382202727`) includes Aeneas PR #715 (sub-abstraction levels in `Values.ml` and checked-in `NestedBorrows.lean` for `fn inner_mut<'a, 'b>(x: &'a mut &'b mut u32) -> &'a mut u32`) and PR #1095 (merged 2026-06-01, fixing shared-borrow projector intersections and mutable borrows behind shared borrows like `&&mut u32` in `TypesUtils.ty_get_mutable_regions`), while still retaining explicit `Unimplemented` and `"Nested borrows are not supported yet"` branches in `SymbolicToPureAbs.ml`, `InterpAbs.ml`, and `SymbolicToPureTypes.ml` (and predating the June 30, 2026 closure of Aeneas issue #181).

## Applicability

This report synthesizes evidence across the five subjects recorded in `REPORT.json` and one historical zerocopy fixture commit:

| Subject | Repository & Immutable Revision | Version / Release / Toolchain | Role in this Report |
|---|---|---|---|
| Aeneas selected by Anneal | `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` | `nightly-2026.06.03` (Lean `leanprover/lean4:v4.30.0-rc2`) | Primary Aeneas revision selected by Anneal (`anneal/flake.nix` at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`). Defines raw-pointer translation/rejection, unsafe-Rust semantic omissions, the support and failure matrix, panic/abort/WP translation, symbolic constant extraction, and June 2026 nested-borrow support. |
| Charon pinned by Aeneas | `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` | `0.1.210`, `rust-toolchain` `nightly` | Exact Charon revision recorded in Aeneas's `charon-pin`. Defines `TRawPtr` / `RawPtr` rvalues, `ullbc_to_llbc.rs` unwind-edge erasure and `AbortKind` structuring, `Preset::Aeneas` vs. `--monomorphize` in `charon/src/options.rs`, and `mir_promoted` extraction in `get_mir.rs`. |
| Zerocopy PME guard implementation | `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` | `main` (examined 2026-09-26) | Establishes zerocopy's post-monomorphization `static_assert!` implementation (`macros.rs`, `macro_util.rs`, `layout.rs`, `doctests.rs`) and `anneal/flake.nix` Aeneas pin selection. |
| Historical Hermes Aeneas pin for the flaky nested-reference fixture | `AeneasVerif/aeneas@42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4` | `build-2026.04.07.112215-42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4` | Historical April 2026 Aeneas revision pinned by `hermes/Cargo.toml` at `google/zerocopy@9bdef60f295715bc113419661b376071cc18e2b3` (with Charon `0.1.174`, Lean `v4.28.0-rc1`, and `rustc` `nightly`) when `test_2_6_nested_refs` was marked `known_flaky`. |

### Scope and Version Distinctions

- **Ordinary functional backend vs. developing separation-logic work**: All findings characterize Aeneas's ordinary pure functional Lean translation at `ac9f1bc5262a5e4ff1e24ca78617121382202727`. Upstream comments and README statements referencing ongoing separation-logic support for unsafe and concurrent Rust describe future/separate work, not capabilities active in this functional pipeline.
- **Historical April 2026 Aeneas (`42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`) vs. June 2026 Anneal pin (`ac9f1bc5262a5e4ff1e24ca78617121382202727`)**: The `test_2_6_nested_refs` flakiness observation belongs strictly to the April 2026 toolchain; between `42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4` and `ac9f1bc5262a5e4ff1e24ca78617121382202727`, Aeneas merged PR #1095 (2026-06-01) altering shared/nested-mutable borrow projector intersections. Conversely, Aeneas issue #181 was closed on 2026-06-30, after `ac9f1bc5262a5e4ff1e24ca78617121382202727`, so post-June-3 commits are outside the pinned behavior.

## Findings

### 1. Raw-Pointer Representation, Interpreter Rejection, Casts, and Model Bypass

#### 1.1 Marker-Level Survival in Pure Types and Lean (`Pure.ml`, `SymbolicToPureTypes.ml`, `RawPtr.lean`)

In `src/symbolic/SymbolicToPureTypes.ml` (lines 161–177), Aeneas maps Charon `TRawPtr (ty, RMut)` to the pure builtin `TRawPtr Mut` and `TRawPtr (ty, RShared)` to `TRawPtr Const`, preserving the translated pointee type `T` as the single type argument. In `src/pure/Pure.ml` (lines 83–98), the definition of `builtin_ty::TRawPtr` explicitly states that raw pointers "don't make sense in the pure world" and are carried only because some declarations contain raw pointers in their signatures, marking such pointers while ensuring the corresponding functions are not actually used in translation.

In `backends/lean/Aeneas/Std/RawPtr.lean`, the Lean backend defines:

```lean
structure RawPtr (T : Type) (M : Mutability) where
  v : T

abbrev MutRawPtr (T : Type) := RawPtr T .Mut
abbrev ConstRawPtr (T : Type) := RawPtr T .Const
```

The single `v : T` field is a typing placeholder, not a dereferenceable pointee or Rust memory address. `RawPtr T M` carries no allocation identity, numeric address, provenance, fat-pointer metadata, liveness, alignment, byte-level initialization state, or aliasing relation.

Basis: **source** (`src/pure/Pure.ml#L83-L98`, `src/symbolic/SymbolicToPureTypes.ml#L161-L177`, `backends/lean/Aeneas/Std/RawPtr.lean`) + **derived** representation boundary.

#### 1.2 Hard Interpreter Rejections: Dereference, Direct `RawPtr` Rvalues, and `AggregatedRawPtr`

When raw-pointer operations reach Aeneas's symbolic interpreter:
- **Dereference (`src/interp/InterpPaths.ml`, lines 110–116)**: Before attempting symbolic-value expansion, the place evaluator matches:
  ```ocaml
  | Deref, _, TRawPtr _ ->
      error "Aeneas does not yet support dereferencing raw pointers."
  ```
  The Lean-only regression fixture `tests/src/raw_pointers.rs` (blob `c77fa4735d4e6616fe4450747e4f3a4d108ca624`, marked `//@ [lean] known-failure`), whose first function obtains a pointer from a slice and evaluates `*ptr.add(1)`, fails with this exact message in checked-in `tests/src/raw_pointers.lean.out` (blob `74eb81fcad39eaa685249c66d129e6b01ba5a883`), pointing to `InterpPaths.ml`.
- **Direct `RawPtr` rvalues (`src/interp/InterpExpressions.ml`, lines 1311–1321)**: `eval_rvalue_not_global` dispatches `Use`, ordinary references (`RvRef`), unary and binary operations (`binop::offset` is rejected in `SymbolicToPureExpressions.ml`), aggregates, and discriminant reads, but has no branch for Charon's `RawPtr` rvalue (`&raw const` / `&raw mut`), falling through to `Unsupported operation`. (Downstream assignment-synthesis code in `InterpStatements.ml` mentions `RawPtr` only after `eval_rvalue_not_global` would have returned.)
- **Aggregated raw pointers (`src/interp/InterpExpressions.ml`, lines 1421–1442)**: Explicitly raises `"Aggregated raw pointers are not supported yet"`.

Basis: **source** (`src/interp/InterpPaths.ml#L110-L116`, `src/interp/InterpExpressions.ml#L1311-L1321`, `src/interp/InterpExpressions.ml#L1421-L1442`) + preserved **execution** artifact (`tests/src/raw_pointers.rs`, `tests/src/raw_pointers.lean.out`).

#### 1.3 Narrow Raw-Pointer Cast Plumbing vs. Always-Failing Lean Model (`SymbolicToPureExpressions.ml`, `Extract.ml`, `RawPtr.lean`)

In `src/symbolic/SymbolicToPureExpressions.ml` (lines 549–589), Aeneas translates a raw-pointer cast into `CastRawPtr` only when both source and target are raw pointers whose pointee is a Charon literal type, marking the cast as fallible. In `src/extract/Extract.ml` (lines 508–545), extraction of `CastRawPtr` asserts that the target backend is Lean (HOL4 explicitly rejects raw-pointer casts and other backends are unsupported) and that the target pointee is an integer scalar type, emitting `RawPtr.cast_scalar`. In `backends/lean/Aeneas/Std/RawPtr.lean`, however, that primitive is defined as:

```lean
-- TODO: we can properly define this once we have separation logic
def RawPtr.cast_scalar ... : Result (RawPtr T' M') :=
  .fail .undef
```

Thus, while parser/translator plumbing exists for scalar-pointee raw-pointer casts, the Lean semantics unconditionally returns `.fail .undef`.

Basis: **source** (`src/symbolic/SymbolicToPureExpressions.ml#L549-L589`, `src/extract/Extract.ml#L508-L545`, `backends/lean/Aeneas/Std/RawPtr.lean`).

#### 1.4 Raw-Pointer-Bearing `SliceIndex` Signatures vs. Higher-Level Model Bypass (`Slice.lean`)

In `backends/lean/Aeneas/Std/Slice.lean`:
- The modeled `SliceIndex` trait (lines 341–369) retains `get_unchecked` and `get_unchecked_mut` methods that consume and return `ConstRawPtr` and `MutRawPtr` marker types so the trait interface matches `core::slice::SliceIndex`.
- Concrete `SliceIndex` implementations for `get_unchecked` and `get_unchecked_mut` (lines 398–408) return `fail .undef` with comments stating that Aeneas does not yet know the model or needs a "more stateful" computation model.
- By contrast, the higher-level function registration `core::slice::Slice.get_unchecked` (lines 549–559) takes the modeled `Slice` and index directly and returns the modeled output without exposing raw pointers to the symbolic interpreter; its source comment notes that it should delegate to `SliceIndexInst.get_unchecked`, and its Lean body is admitted with `sorry`.

Consequently, a Rust function whose standard-library callee uses raw pointers internally can translate if Aeneas intercepts the call with a higher-level model, but any theorem over that translation relies entirely on the model's trusted/admitted status rather than verified raw-pointer execution.

Basis: **source** (`backends/lean/Aeneas/Std/Slice.lean#L341-L369`, `Slice.lean#L398-L408`, `Slice.lean#L549-L559`).

---

### 2. Semantic Omissions Relevant to Unsafe and Concurrent Rust

Preserved machine-readable inventories in [`support/aeneas-semantic-omissions-unsafe-rust/omission-matrix.json`](support/aeneas-semantic-omissions-unsafe-rust/omission-matrix.json) and [`support/aeneas-semantic-omissions-unsafe-rust/source-map.json`](support/aeneas-semantic-omissions-unsafe-rust/source-map.json) map each omitted operational dimension at `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` to its exact source location and proof impact:

| Operational Dimension | Pinned Aeneas Mechanism & Source Location | Classification (Omitted / Abstracted / Unsupported) | Proof-Facing Consequence for Anneal |
|---|---|---|---|
| General unsafe and concurrent Rust | `README.md` (blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`) | **Unsupported** in ordinary functional backend | Aeneas explicitly scopes the functional translator to "a subset of safe Rust" and defers unsafe and concurrent Rust to ongoing separation-logic work. |
| Allocation identity and ordinary reference identity | `src/symbolic/SymbolicToPureTypes.ml` (blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`), `src/pure/Pure.ml` (blob `acde8579d6861a08efae086c72f3156283110342`) | **Abstracted / Omitted** | `&T`, `&mut T`, and `Box<T>` become pure referent values `T` plus backward functions; generated Lean cannot state or prove whether two values reside in the same heap allocation or have equal pointer addresses. |
| Pointer provenance vs. `mplace` metadata | `src/pure/Pure.ml` (`mplace` and `TRawPtr`), `src/interp/InterpPaths.ml` (blob `ec23375a5ca0680500daea0248d2372c9901156e`) | **Omitted** (terminology trap) | Aeneas `mplace` "provenance" tracks source/symbolic variable names for code generation, **not** Rust strict/exposed pointer provenance or allocation access permissions. |
| Partial / byte-level initialization state | Pure value representation (`src/pure/Pure.ml`) | **Omitted** | No byte-addressed heap tracks initialized vs. uninitialized bytes or padding; safe values are total pure terms and raw-pointer memory accesses are rejected. |
| Operational effect trace vs. `fun_effect_info` | `src/pure/Pure.ml` (`fun_effect_info`), `src/llbc/FunsAnalysis.ml` (blob `a2678ba12e8baaaf14fc99c3f061b10edae2da86`) | **Abstracted** | `Pure.fun_effect_info` records only `{ can_fail; can_diverge; is_rec }` (and `FunsAnalysis.ml` computes a coarse internal `stateful` boolean not fully used in extraction), omitting I/O, allocation, thread, clock, and scheduler traces. |
| Destructor (`Drop`) execution | `src/Config.ml` (blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`, `drop_as_no_op = true`), `src/interp/InterpStatements.ml` (blob `97452f658bbd773c16386592d31b0bf61da8891f`) | **Abstracted** by default | Default translation turns LLBC `Drop` statements into immediate `Unit`; enabling `-eval-drops` runs symbolic `drop_value` borrow bookkeeping rather than arbitrary user destructor side effects. |
| Standard output / I/O effects | `backends/lean/Aeneas/Std/Std/Io.lean` (blob `c32f89b32297e472aa0128509b572e76cf72a523`) | **Abstracted** | `@[rust_fun "std::io::stdio::_print"] def std.io.stdio._print (_ : core.fmt.Arguments) : Result Unit := .ok ()` succeeds while erasing all output bytes, ordering, and device failure. |
| Concurrency and atomic memory ordering | `README.md`, `backends/lean/Aeneas/Std/Core/Atomic.lean` (blob `d686f3154fe6da9c2b4c1d6694764a1005332958`), `src/llbc/FunsAnalysis.ml` | **Unsupported / Axiomatized** | `AtomicBool` and `AtomicU32` are registered as axiomatic Lean types with TODO markers and no happens-before, interleaving, or `Relaxed`/`Acquire`/`Release`/`SeqCst` semantics. |
| Environment and nondeterministic queries | `src/pure/Pure.ml` (`GetTarget`) | **Axiomatized** (narrow) | `GetTarget` is an axiomatized fallible primitive for multi-target dispatch from whose output "nothing can be deduced," not a general nondeterministic transition system. |

For Anneal, these omissions are **claim-specific**: a proof over Aeneas's pure Lean output suffices only when the target Rust property is invariant under the erased distinctions or when an explicit correspondence theorem / assumption bridges the omitted dimension.

Basis: **documentation** (`README.md`) + **source** (`src/pure/Pure.ml`, `src/symbolic/SymbolicToPureTypes.ml`, `src/llbc/FunsAnalysis.ml`, `src/Config.ml`, `src/interp/InterpStatements.ml`, `src/interp/InterpPaths.ml`, `backends/lean/Aeneas/Std/Std/Io.lean`, `Core/Atomic.lean`, `Slice.lean`) + **derived** proof-ledger obligations.

---

### 3. Aeneas Rust Support and Failure Matrix and Diagnostic Policy

#### 3.1 Three-Layer Boundary, Preset Enforcement, and Test-Runner Protocol

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, an input crate crosses three distinct gates:
1. **Charon extraction (`--preset=aeneas`)**: `src/Main.ml` (blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`) inspects imported LLBC metadata for `preset = Some Aeneas` and rejects any `.llbc` file generated without `--preset=aeneas`. `tests/README.md` (blob `5aa96fab26146514d0ecb2e26fcc40a5a45c94d9`) specifies that tests causing Charon errors belong in the Charon test suite, while Aeneas `known-failure` tests cover failures after Charon succeeds.
2. **Aeneas symbolic execution and pure translation**: Controlled by `tests/test_runner/Input.ml` (blob `042191ed5aecc9f591a7522e0c7d956b14e76842`), `tests/test_runner/run_test.ml` (blob `0a4b726e995dca0132314dae00c421ffd7f3a7a4`), and `tests/test_runner/Backend.ml` (blob `badc72ad55633bd28028df9c5b6908a3cc035aac`), which classify per-backend fixture actions as `Normal` (`run_command_expecting_success` with `-abort-on-error`, `-checks`, `-no-progress-bar`, `-sequential`), `Skip`, or `KnownFailure` (`run_command_expecting_failure` comparing captured `.lean.out` diagnostics).
3. **Target backend verification**: CI parses and type-checks generated Lean files, replays handwritten proofs, and checks that committed outputs match regenerated files.

Basis: **documentation** (`tests/README.md`) + **source** (`src/Main.ml`, `tests/test_runner/Input.ml`, `tests/test_runner/run_test.ml`, `tests/test_runner/Backend.ml`).

#### 3.2 Error Recovery (`CFailure`) vs. Process Exit Status vs. Warnings (`Errors.ml`, `Translate.ml`, `Main.ml`, `Config.ml`)

Aeneas separates per-declaration error recovery from process-level success:
- **Recoverable `CFailure` and partial output (`src/Errors.ml` blob `c135674b8601786616c6c20ad81ec388bb8cbfea`, `src/Translate.ml` blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`, `src/Config.ml` blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`)**: By default, `Config.fail_hard` is `false`. When `Errors.craise` registers an error, it appends to `Errors.error_list` and raises `CFailure`. `Translate.ml` catches `CFailure` around individual functions, globals, signatures, type declarations, and traits, omitting failed items (`None`) while continuing to translate and export the rest of the crate.
- **Process exit status (`src/Main.ml`)**: At completion, `Main.ml` checks whether `Errors.error_list` is non-empty (`has_errors`) and executes `exit 1` if any error was registered. Passing `-abort-on-error` sets `fail_hard = true`, raising a fatal OCaml `Failure` on the first registered error so no partial output is written after the error.
- **Warning-only hazards (`Config.warnings_as_errors = false`)**: Warnings do **not** populate `error_list` or cause a non-zero exit unless `-warnings-as-errors` is passed. In particular, `src/symbolic/SymbolicToPure.ml` (blob `95ba91f539e48009efa420dfa956c4c55581cb3a`) emits a **warning** (not an error) when an associated type survives Charon lifting on a non-builtin trait (as in `tests/src/mutually-recursive-traits.rs`, blob `074ff639d23a8eca640a8f0ea1b639da269cf894`), stating that Aeneas cannot handle the type and "the generated code will likely be incorrect." That fixture fails in `tests/src/mutually-recursive-traits.lean.out` (blob `d7d6c54d81761d6020aa8627592340ef43cc78f4`) only because the test runner passes `-warnings-as-errors`.

Basis: **source** (`src/Errors.ml`, `src/Translate.ml`, `src/Main.ml`, `src/Config.ml`, `src/symbolic/SymbolicToPure.ml`) + preserved known-failure **execution** artifact (`tests/src/mutually-recursive-traits.lean.out`).

#### 3.3 Fixture-Backed Support and Failure Classification Matrix

| Evidence Class | Pinned Representatives & Source / Artifact Witnesses (`ac9f1bc5262a5e4ff1e24ca78617121382202727`) | Semantic Meaning & Boundary |
|---|---|---|
| Fixture-backed accepted shapes | `tests/src/scalars.rs` (`4901accdd5350d23e244208eba767f8488afcc3b`) → `tests/lean/Scalars.lean` (`a3f4d2be02d9ead24aa5a234febb490602573821`); `adt.rs` (`cc31a7085737e5efd8910316d99adbd74d9df32c`) → `Adt.lean` (`f99cbd9c162d060dc55ea2614d7d0b8bfa32ca9e`); `arrays.rs` (`478af7171452826436f56f12c88493debac8e0d0`) → `Arrays.lean` (`00b7716b63b41c4747889b42f2dee3796d3ab12d`); `no_nested_borrows.rs` (`707f7d6e1201d1220380dd565a4178806cf3a9ec`) → `NoNestedBorrows.lean` (`e2a706b744e2e9a105e305cf8a2b353354209dae`); `nested-borrows.rs` (`61d62cf0e0723a4019e024882e35fb8b212a67eb`) → `NestedBorrows.lean` (`61b3b2b31e50555182867a5b73fa510d05106e22`); `loops.rs` (`b6b63ec1a8501046af3d153c51b44f34cdde5798`) → `Loops.lean` (`73df255602485533462c214cd011d66867f6b04f`); `traits.rs` (`a20f6ee91960cbacf99e8899a32e789f7b855671`) → `Traits.lean` (`d234936b72231024fbccf0030a08023836e5eb6e`); `closures.rs` (`525a3f8941c3224ddf32f818d168fef20f8a1b20`) → `Closures.lean` (`e60021de5406f9f21dacf6e994cbea1fb9264fa4`); `dyn.rs` (`fa2b29298fcc157e4b05a61098553525fe867f5d`) → `Dyn.lean` (`1ca9dd626eea93ec47dee2094febb8541d41c2c3`); `constants.rs` (`d75678acc60fd9482090ba8457242dfd801d96e3`) → `Constants.lean` (`9c6e588633544daa10581bd363eabba0fea52b70`); `static.rs` (`fad3770875b1dd3beec5988357fcc993b645abd2`) → `Static.lean` (`9d31798665d488b70730ea60c928e82c790d308b`); `drop.rs` (`7f232241c87e1e53b01dcef82ef99d808c068b0f`) → `Drop.lean` (`a0119232ebcddb64b81d919fa9c363cc56f8ba0b`) | Exercised shapes pass Charon, Aeneas (`-abort-on-error -checks`), and Lean type-checking; neighboring shapes (e.g., mutable `'static` globals, `-borrow-check-globals` with static refs in global initializers, or unsupported `dyn` upcasts) remain restricted. |
| Explicit Aeneas hard rejections (`CFailure`) | Raw-pointer dereference (`InterpPaths.ml`, `raw_pointers.lean.out`); function-pointer calls (`FnOpDynamic` in `InterpStatements.ml`: `"Function pointers are not supported yet"`) and `TFnPtr` types (`SymbolicToPureTypes.ml`); pointer `binop::offset` and `transmute` (`SymbolicToPureExpressions.ml` blob `b24d12a8a8403a5bc8aae7b55c35ce0259b75bc8`); `AggregatedRawPtr` and unsupported rvalues (`InterpExpressions.ml` blob `45fddae6eb4e46edb23a98c790c7edf17c586afa`) | Registers a translation error in `Errors.error_list`, causing `Main.ml` to exit with status `1` (or abort immediately under `-abort-on-error`). |
| Known warning-level soundness hazard | Residual associated types on non-builtin traits (`SymbolicToPure.ml`, `mutually-recursive-traits.lean.out`) | Emits a warning that generated code will likely be incorrect; succeeds with exit status `0` unless `-warnings-as-errors` is enabled. |
| Structural unsupported shapes | GAT `ItemClause`s, complex nested region binders (de Bruijn shifting ignored in `SymbolicToPureTypes.ml`), outer-loop `break`/`continue`/`return` from a nested loop (`README.md`), mutable `'static` references, unsupported `dyn Trait` unsizing/projections, and ADTs with nested mutable borrows | Rejected via `Unsupported`, `Unimplemented`, or assertion paths. |
| Semantic abstractions | Reference/lifetime erasure, `Box<T>` → `T`, `Union`/`Opaque` → `Opaque`, default `drop_as_no_op = true` (`Drop.lean`), `_print := ok ()` | Translation succeeds while omitting source-level representation or effects. |

Basis: **source** + preserved positive and known-failure **execution** artifacts.

---

### 4. Panic, Error Tag Rewriting, Unwind Erasure, and Weakest-Precondition Semantics

#### 4.1 Charon ULLBC-to-LLBC Unwind Erasure (`ullbc_to_llbc.rs`, `llbc_ast.rs`)

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, ULLBC retains a distinct `UnwindResume` terminator and call unwind targets. However, during ULLBC-to-LLBC structuring in `charon/src/transform/control_flow/ullbc_to_llbc.rs` (producing the structured AST in `charon/src/ast/llbc_ast.rs`):
- `UnwindResume` is converted into `Abort(AbortKind::Panic(None))`.
- Normal `Call` terminators match `on_unwind` as `_` and retain only the normal return target, with the explicit source comment `TODO: Have unwinds in the LLBC`.
- `Assert` terminators inspect their unwind target block and summarize it into `Assert { ... on_failure: AbortKind }` (defaulting to `AbortKind::Panic(None)` if the block does not reduce to an abort).
- Structured LLBC has `Assert`, `Call`, `Abort(AbortKind)`, and `Return`, with no `UnwindResume` statement and no unwind cleanup graph.

Basis: **source** (`charon/src/ast/llbc_ast.rs`, `charon/src/transform/control_flow/ullbc_to_llbc.rs`).

#### 4.2 Aeneas `AbortKind` Collapse and `can_fail` Forcing (`InterpStatements.ml`, `FunsAnalysis.ml`, `SymbolicToPure.ml`)

When Aeneas interprets structured LLBC (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`):
- In `src/interp/InterpStatements.ml` (`eval_statement`), Aeneas matches `Abort _` without inspecting the `AbortKind` payload (`Panic`, `UndefinedBehavior`, or `UnwindTerminate`), returning `Panic` in concrete mode and synthesizing `SA.Panic` in symbolic mode. Consequently, Charon's distinction between a Rust panic, an explicit `UndefinedBehavior` abort, and `UnwindTerminate` is erased at the statement-interpreter boundary.
- In `src/symbolic/SymbolicToPure.ml` (`translate_fun_decl_body`), the `mk_panic` callback translates `SA.Panic` into `Result.fail` with `Pure.error_failure_id`, which `src/extract/ExtractBase.ml` prints in Lean as `panic` (`Error.panic`).
- In `src/llbc/FunsAnalysis.ml`, while syntactic/transitive failure propagation tracks `visit_Assert`, `visit_Panic`, fallible operators, and callees, the final pass deliberately forces `can_fail = true` for all ordinary non-global, non-builtin functions (noting that the analysis is not yet used to strip the `Result` monad from infallible extracted functions).

Basis: **source** (`src/interp/InterpStatements.ml`, `src/symbolic/SymbolicToPure.ml`, `src/pure/Pure.ml`, `src/extract/ExtractBase.ml`, `src/llbc/FunsAnalysis.ml`).

#### 4.3 `Error` Tag Rewriting (`intro_massert`) and Weakest-Precondition (`WP.lean`) Disregard of Error Tags

In `backends/lean/Aeneas/Std/Primitives.lean`, `Result` has cases `Result.ok v`, `Result.fail e`, and `Result.div`, where `Error` includes `assertionFailure`, `integerOverflow`, `divisionByZero`, `arrayOutOfBounds`, `maximumSizeExceeded`, `panic`, and `undef`, and `massert b` evaluates to `ok ()` when `b` holds and `fail assertionFailure` otherwise.

The exact `Error` constructor emitted for a Rust panic is not invariant under Aeneas's pure micro-passes:
- In `src/pure/PureMicroPassesGeneral.ml`, `intro_massert_visitor` rewrites `if b then e else fail panic` into `massert b; e`, converting `Error.panic` into `Error.assertionFailure`.
- In checked-in `tests/lean/NoNestedBorrows.lean` (blob `e2a706b744e2e9a105e305cf8a2b353354209dae`), unconditional or match-arm panics (`panic_mut_borrow`, and the `List.Nil` branches of `split_list` and `list_nth_shared`) emit `fail panic`, whereas conditional panics (`test_panic` and `test_panic_msg`) are rewritten to `massert (¬ b)`.

In `backends/lean/Aeneas/Std/WP.lean`, the weakest-precondition predicate `spec` satisfies:
- `spec (ok x) p ↔ p x` (`spec_ok`)
- `spec (fail e) p ↔ False` (`spec_fail`)
- `spec div p ↔ False` (`spec_div`)

Because `spec (fail e) p` simplifies to `False` for every `e : Error`, ordinary WP proofs establish that modeled execution reaches `ok` (neither failing nor diverging) and are unaffected by `panic`-to-`assertionFailure` tag rewrites, at the cost of providing no information about unwind cleanup or `catch_unwind` recovery.

Basis: **source** (`src/pure/PureMicroPassesGeneral.ml`, `backends/lean/Aeneas/Std/Primitives.lean`, `backends/lean/Aeneas/Std/WP.lean`) + preserved **execution** artifact (`tests/lean/NoNestedBorrows.lean`).

---

### 5. Post-Monomorphization Errors (PMEs) at the Charon/Aeneas Boundary

#### 5.1 Zerocopy's `static_assert!` PME Admission Contract (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`)

In `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`:
- `zerocopy/src/util/macros.rs` defines `static_assert!`, which declares a local `StaticAssert` trait with an associated `ASSERT` constant computed via `const_assert!($condition)` and forces evaluation of `ASSERT` at the generic call site. Unlike a runtime check, a false condition triggers a compile-time post-monomorphization error (PME) when `rustc` monomorphizes the caller for concrete type arguments. (`zerocopy/src/doctests.rs` documents that zerocopy tests PMEs via doctests because `trybuild` does not support PME compile-failure testing.)
- Zerocopy uses `static_assert!` and associated-constant PMEs as soundness-critical admission guards on unsafe operations whose trait bounds alone do not enforce layout compatibility, including:
  - `try_transmute<Src, Dst>` (`zerocopy/src/util/macro_util.rs`), asserting `size_of::<Dst>() == size_of::<Src>()` before an unsafe transmutation;
  - reference and mutable-reference transmutation helpers asserting size and alignment relationships; and
  - `layout::CastFrom::project` (`zerocopy/src/layout.rs`), which forces `CastParams::try_compute` through an associated constant that panics during required const evaluation when source and target layouts are incompatible.

Basis: **source** (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`: `zerocopy/src/util/macros.rs`, `zerocopy/src/util/macro_util.rs`, `zerocopy/src/layout.rs`, `zerocopy/src/doctests.rs`).

#### 5.2 Polymorphic `Preset::Aeneas` Extraction vs. Symbolic Constants and PME Admission

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` and `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`:
- **Polymorphic preset (`charon/src/options.rs`, `charon/src/bin/charon-driver/translate/get_mir.rs`)**: Aeneas requires `--preset=aeneas` (`src/Main.ml`). In `charon/src/options.rs`, `Preset::Aeneas` does **not** set `self.monomorphize = true` (whereas `Preset::Soteria` explicitly sets `self.monomorphize = true`) and leaves the default local MIR level at `Promoted` (`mir_promoted` in `get_mir.rs`).
- **Symbolic preservation of generic constants (`translate_constants.rs`, `Constants.lean`, `ConstantsLean.lean`)**: Charon translates generic const parameters as `ConstantExprKind::Var` (`charon/src/bin/charon-driver/translate/translate_constants.rs`), and Aeneas emits polymorphic Lean definitions over symbolic parameters. In `tests/src/constants.rs` → `tests/lean/Constants.lean`, `V<const N: usize, T>::LEN = N` and `use_v<const N, T>` become Lean functions parameterized by `N`; in `tests/src/constants-lean.rs` → `tests/lean/ConstantsLean.lean`, `Wrapper<N, M>::NM = N * M` and trait-associated constants become symbolic Lean definitions or dictionary fields.
- **Verification consequence**: Because the polymorphic LLBC/Lean translation does not encode a predicate restricting type parameters `(Src, Dst)` to the set of concrete monomorphizations accepted by `rustc` codegen after required const evaluation, translating a generic function body through `--preset=aeneas` does not automatically import a PME guard `P<Src, Dst>` as a Lean hypothesis. Sound verification must either:
  1. prove a stronger generic theorem that does not depend on the PME guard (or where the PME computation is evaluated along the modeled runtime path), or
  2. carry an explicit admission hypothesis `P<Src, Dst>` (or connect a const-domain proof of `ASSERT` to the runtime-domain theorem).
- **Status of `--monomorphize`**: Although Charon `0.1.210` provides an independent `--monomorphize` flag that substitutes concrete generic arguments via Hax in `get_mir.rs` and `translate_crate.rs`, pinned source inspection does not establish that `--monomorphize` runs `rustc`'s exact post-monomorphization required-const checks or is compatible with Aeneas's `--preset=aeneas` workflow.

Basis: **source** (`charon/src/options.rs`, `get_mir.rs`, `translate_crate.rs`, `translate_constants.rs`; Aeneas `src/Main.ml`, `tests/lean/Constants.lean`, `tests/lean/ConstantsLean.lean`) + **derived** soundness boundary.

---

### 6. Nested-Borrow Support and the Historical Hermes Flaky Reproducer

#### 6.1 The Historical Hermes Fixture (`42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`) vs. Anneal's Pin (`ac9f1bc5262a5e4ff1e24ca78617121382202727`)

At `google/zerocopy@9bdef60f295715bc113419661b376071cc18e2b3`, `hermes/tests/fixtures/edge_cases_types/test_2_6_nested_refs/source/src/lib.rs` (blob `bbb4c462ef48003ed7926e55e96a31f524c7dfbb`) defines:

```rust
pub fn nested(x: &&u32, y: &mut &u32, z: &&mut u32) {
    let _ = **x;
    let _ = **y;
    let _ = **z;
}
```

which exercises three distinct nested-reference shapes tracked separately by `src/llbc/TypesAnalysis.ml` (lines 21–30, blob `4b80030bddd0fc7d044894a85fe332c8d3bdb5d9`): shared-under-shared (`&&u32`), shared-under-mutable (`&mut &u32`), and mutable-under-shared (`&&mut u32`).

Historical provenance and limitations of that fixture:
- In `hermes/Cargo.toml` at `9bdef60f295715bc113419661b376071cc18e2b3`, Hermes pinned Aeneas `42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4` (`build-2026.04.07.112215-42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`), Charon `0.1.174`, Lean `leanprover/lean4:v4.28.0-rc1`, and `rustc` `nightly`.
- When `hermes/tests/fixtures/edge_cases_types/test_2_6_nested_refs/hermes.toml` (blob `eaf4c1f3fb0e8468fb8f57c6b3f174d80fee5177`) was marked `known_flaky` because Aeneas intermittently failed with an `unimplemented` error, the checked-in `hermes/tests/fixtures/edge_cases_types/test_2_6_nested_refs/expected.stderr` (blob `d15940a498f1a8b11c8d36237745d58a6aeb4414`) preserved only Hermes's `sorry` proof-context warning, **not** the failing Aeneas stderr or OCaml source line.
- Anneal (`anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba` at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`) selects the later June 3 release `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.

Basis: **source** (`google/zerocopy@9bdef60f295715bc113419661b376071cc18e2b3` and `41f5b37afe7060fd9fe08c00b200672cd76d77b9`; `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` `src/llbc/TypesAnalysis.ml#L21-L30`).

#### 6.2 Nested-Borrow Machinery (PR #715, PR #1095) vs. Remaining Unsupported Paths at `ac9f1bc5262a5e4ff1e24ca78617121382202727`

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, nested-borrow support is partial and path-dependent:
- **Positive sub-abstraction machinery (Aeneas PR #715, merged 2026-01-28)**: `src/llbc/Values.ml` (blob `6f7e8bb746adb2fbc6612a1c442100b3c7a39389`) defines sub-abstraction levels (`abs_level`) allowing a region abstraction to end a higher-level borrow layer without ending the entire abstraction. Checked-in `tests/src/nested-borrows.rs` (blob `61d62cf0e0723a4019e024882e35fb8b212a67eb`) and `tests/lean/NestedBorrows.lean` (blob `61b3b2b31e50555182867a5b73fa510d05106e22`) translate `fn inner_mut<'a, 'b>(x: &'a mut &'b mut u32) -> &'a mut u32 { *x }` into a Lean definition with a forward result and two backward functions, alongside loop-carried nested-borrow iterator examples.
- **Mutable-behind-shared borrow projector fix (Aeneas PR #1095, merged 2026-06-01)**: Present in `ac9f1bc5262a5e4ff1e24ca78617121382202727` (unlike `42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`). In `src/llbc/TypesUtils.ml` (`ty_get_mutable_regions`, lines 264–302, blob `c40ef4fccfefed3d18f0d934a852e56515e3af65`), a mutable borrow nested beneath a shared borrow (such as `z: &&mut u32` in `test_2_6_nested_refs`) is treated as effectively shared and stops mutable-region traversal upon entering a shared reference, while borrow-projector intersection accounts separately for shared and non-shared projectors.
- **Coexisting unsupported nested-borrow paths at `ac9f1bc5262a5e4ff1e24ca78617121382202727`**:
  - `docs/user/src/README.md` (lines 9–16, blob `fa1cac5c60ac5fdbd212ad4e9c07a9e0917ebd2c`) still lists "no nested borrows in function signatures" as an active limitation, and `src/interp/InterpBorrows.mli` (lines 118–121, blob `249c1d3aff003a145f55b20ded55e596b00849db`) warns about nested-borrow representation limits.
  - `src/interp/InterpAbs.ml` (lines 20–46, blob `0f67ceffc1584d0a801dde84aee953737f2d187e`) raises `"Nested borrows are not supported yet"` on concrete nested-borrow conversion paths.
  - `src/symbolic/SymbolicToPureAbs.ml` (lines 75–80 and 162–164, blob `7127601439903abb6fb86c56bed2c8f6af103e26`) raises `Unimplemented` for `AEndedIgnoredMutLoan`, `AIgnoredSharedLoan`, and `AIgnoredMutBorrow`, and asserts `abs_level = 0` in several translation helpers (see also `src/symbolic/SymbolicToPureValues.ml`, blob `5da7630a187bd4b19b33aad967591d4effa8524c`).
  - `src/symbolic/SymbolicToPureTypes.ml` (lines 294–300, blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`) explicitly rejects ADT declarations containing nested mutable borrows.
  - Upstream Aeneas issue #181 ("Add support for nested borrows in function signatures") was closed on 2026-06-30—27 days after `ac9f1bc5262a5e4ff1e24ca78617121382202727`—and loop-carried `Option<&T>` borrow issues were split into issue #929.

Basis: **source** (`src/llbc/Values.ml`, `src/llbc/TypesUtils.ml#L264-L302`, `src/interp/InterpBorrows.mli#L118-L121`, `src/interp/InterpAbs.ml#L20-L46`, `src/symbolic/SymbolicToPureAbs.ml#L75-L80`, `SymbolicToPureAbs.ml#L162-L164`, `src/symbolic/SymbolicToPureValues.ml`, `src/symbolic/SymbolicToPureTypes.ml#L294-L300`) + **documentation** (`docs/user/src/README.md#L9-L16`, PR #715, PR #1095, issues #181 and #929) + preserved **execution** artifact (`tests/lean/NestedBorrows.lean`).

## Boundaries

- **Not examined**:
  - Fresh execution of `charon`, `aeneas`, `lake`, or `rustc` across any of the six merged investigations (all behavioral evidence comes from checked-in `.lean` and `.lean.out` repository artifacts).
  - Non-Lean extraction backends (Coq, F*, HOL4) beyond noting that `CastRawPtr` extraction in `Extract.ml` is restricted to Lean and rejected in HOL4.
  - Operational models of `std::panic::catch_unwind`, foreign-exception unwinding ABIs, or Aeneas's separate developing separation-logic backend.
- **Unknown**:
  - Whether Charon's `--monomorphize` flag reproduces `rustc`'s exact post-monomorphization required-const admission checks on zerocopy `static_assert!` guards.
  - Whether the historical `test_2_6_nested_refs` (`pub fn nested(x: &&u32, y: &mut &u32, z: &&mut u32)`) fixture always succeeds, always fails, or remains nondeterministic when executed repeatedly on `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, and which exact OCaml line raised `unimplemented` under `42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`.
- **Unsupported**:
  - Raw-pointer dereference (`InterpPaths.ml`), direct `RawPtr` rvalue evaluation (`InterpExpressions.ml`), `AggregatedRawPtr`, pointer `binop::offset`, and `transmute` (`SymbolicToPureExpressions.ml`).
  - Function-pointer calls (`FnOpDynamic` in `InterpStatements.ml`) and `TFnPtr` types (`SymbolicToPureTypes.ml`).
  - Returning from a nested loop or `break`/`continue` to a labeled outer loop (`README.md`).
  - Generic associated types (`ItemClause`), mutable `'static` references, ADTs containing nested mutable borrows (`SymbolicToPureTypes.ml#L294-L300`), and nested-borrow loan shapes (`AEndedIgnoredMutLoan`, `AIgnoredSharedLoan`, `AIgnoredMutBorrow`, and `abs_level > 0` branches in `SymbolicToPureAbs.ml` and `InterpAbs.ml`).
  - Unsafe memory and concurrency as a general functional backend contract (`README.md`).
- **Known not to apply**:
  - The presence of `RawPtr T M`, `MutRawPtr T`, or `ConstRawPtr T` in generated Lean does not model pointer addresses, provenance, validity, or dereference (`RawPtr.v` is a placeholder field, and `RawPtr.cast_scalar` and `SliceIndex.get_unchecked` return `fail .undef`).
  - Aeneas `mplace` provenance metadata does not represent Rust pointer provenance.
  - Default `Config.drop_as_no_op = true` does not execute `Drop::drop` side effects, and `std.io.stdio._print := .ok ()` does not preserve stdout output.
  - Charon ULLBC-to-LLBC conversion does not preserve ordinary call `on_unwind` cleanup edges or `UnwindResume`, and Aeneas's `Abort _` interpreter branch does not preserve Charon's distinction among `Panic`, `UndefinedBehavior`, and `UnwindTerminate`.
  - Generated `Error` tags (`Error.panic` vs. `Error.assertionFailure`) are not stable across pure micro-passes (`intro_massert_visitor`).
  - Polymorphic translation under `--preset=aeneas` does not automatically import `rustc` post-monomorphization `static_assert!` admission checks into Lean theorems.

## Evidence

### 1. Pinned Aeneas `nightly-2026.06.03` (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, observed 2026-09-26 and 2026-09-27)

- **Support files preserved in this package**:
  - [`support/aeneas-semantic-omissions-unsafe-rust/omission-matrix.json`](support/aeneas-semantic-omissions-unsafe-rust/omission-matrix.json): structured matrix of unsafe-Rust semantic omissions, classifications, and proof consequences.
  - [`support/aeneas-semantic-omissions-unsafe-rust/source-map.json`](support/aeneas-semantic-omissions-unsafe-rust/source-map.json): exact repository, commit, file, and blob coordinates for the omission inventory.
- **Compiler, interpreter, and extractor source (`ac9f1bc5262a5e4ff1e24ca78617121382202727`)**:
  - `charon-pin`: pins `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.
  - `README.md` (blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`), `docs/user/src/README.md` (blob `fa1cac5c60ac5fdbd212ad4e9c07a9e0917ebd2c`, lines 9–16), and `tests/README.md` (blob `5aa96fab26146514d0ecb2e26fcc40a5a45c94d9`).
  - `src/Main.ml` (blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`), `src/Config.ml` (blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`), `src/Errors.ml` (blob `c135674b8601786616c6c20ad81ec388bb8cbfea`), and `src/Translate.ml` (blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`).
  - `src/pure/Pure.ml` (blob `acde8579d6861a08efae086c72f3156283110342`, lines 83–98 for `TRawPtr`, `GetTarget`, `fun_effect_info`, `error_failure_id`) and `src/pure/PureMicroPassesGeneral.ml` (`intro_massert_visitor`).
  - `src/llbc/FunsAnalysis.ml` (blob `a2678ba12e8baaaf14fc99c3f061b10edae2da86`), `src/llbc/TypesAnalysis.ml` (blob `4b80030bddd0fc7d044894a85fe332c8d3bdb5d9`, lines 21–30), `src/llbc/TypesUtils.ml` (blob `c40ef4fccfefed3d18f0d934a852e56515e3af65`, lines 264–302 `ty_get_mutable_regions`), and `src/llbc/Values.ml` (blob `6f7e8bb746adb2fbc6612a1c442100b3c7a39389`).
  - `src/interp/InterpPaths.ml` (blob `ec23375a5ca0680500daea0248d2372c9901156e`, lines 110–116), `src/interp/InterpExpressions.ml` (blob `45fddae6eb4e46edb23a98c790c7edf17c586afa`, lines 1311–1321 and 1421–1442), `src/interp/InterpStatements.ml` (blob `97452f658bbd773c16386592d31b0bf61da8891f`), `src/interp/InterpBorrows.mli` (blob `249c1d3aff003a145f55b20ded55e596b00849db`, lines 118–121), and `src/interp/InterpAbs.ml` (blob `0f67ceffc1584d0a801dde84aee953737f2d187e`, lines 20–46).
  - `src/symbolic/SymbolicToPureTypes.ml` (blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`, lines 161–177 and 294–300), `src/symbolic/SymbolicToPure.ml` (blob `95ba91f539e48009efa420dfa956c4c55581cb3a`), `src/symbolic/SymbolicToPureExpressions.ml` (blob `b24d12a8a8403a5bc8aae7b55c35ce0259b75bc8`, lines 549–589), `src/symbolic/SymbolicToPureAbs.ml` (blob `7127601439903abb6fb86c56bed2c8f6af103e26`, lines 75–80 and 162–164), and `src/symbolic/SymbolicToPureValues.ml` (blob `5da7630a187bd4b19b33aad967591d4effa8524c`).
  - `src/extract/Extract.ml` (blob `52754e4fdb25b50fce63abe2d2184751d69632e8`, lines 508–545) and `src/extract/ExtractBase.ml` (blob `4fc8a3f35643ba66555f0889790d50993feef1b9`).
  - `tests/test_runner/Input.ml` (blob `042191ed5aecc9f591a7522e0c7d956b14e76842`), `tests/test_runner/run_test.ml` (blob `0a4b726e995dca0132314dae00c421ffd7f3a7a4`), and `tests/test_runner/Backend.ml` (blob `badc72ad55633bd28028df9c5b6908a3cc035aac`).
- **Lean backend standard-library models (`ac9f1bc5262a5e4ff1e24ca78617121382202727`)**:
  - `backends/lean/Aeneas/Std/RawPtr.lean`: `RawPtr`, `MutRawPtr`, `ConstRawPtr`, and `RawPtr.cast_scalar := .fail .undef`.
  - `backends/lean/Aeneas/Std/Slice.lean` (blob `cab42e4f6ab768e97df8f5d3d9a5de73079a785c`, lines 341–369, 398–408, 549–559).
  - `backends/lean/Aeneas/Std/Std/Io.lean` (blob `c32f89b32297e472aa0128509b572e76cf72a523`): `std.io.stdio._print := .ok ()`.
  - `backends/lean/Aeneas/Std/Core/Atomic.lean` (blob `d686f3154fe6da9c2b4c1d6694764a1005332958`): `AtomicBool` and `AtomicU32` axioms.
  - `backends/lean/Aeneas/Std/Primitives.lean` and `backends/lean/Aeneas/Std/WP.lean` (`spec`, `spec_ok`, `spec_fail`, `spec_div`).
- **Preserved fixtures (`ac9f1bc5262a5e4ff1e24ca78617121382202727`)**:
  - Known-failure fixtures: `tests/src/raw_pointers.rs` (`c77fa4735d4e6616fe4450747e4f3a4d108ca624`) + `tests/src/raw_pointers.lean.out` (`74eb81fcad39eaa685249c66d129e6b01ba5a883`); `tests/src/mutually-recursive-traits.rs` (`074ff639d23a8eca640a8f0ea1b639da269cf894`) + `tests/src/mutually-recursive-traits.lean.out` (`d7d6c54d81761d6020aa8627592340ef43cc78f4`).
  - Positive fixtures: `Scalars.lean` (`a3f4d2be02d9ead24aa5a234febb490602573821`), `Adt.lean` (`f99cbd9c162d060dc55ea2614d7d0b8bfa32ca9e`), `Arrays.lean` (`00b7716b63b41c4747889b42f2dee3796d3ab12d`), `NoNestedBorrows.lean` (`e2a706b744e2e9a105e305cf8a2b353354209dae`), `NestedBorrows.lean` (`61b3b2b31e50555182867a5b73fa510d05106e22`), `Loops.lean` (`73df255602485533462c214cd011d66867f6b04f`), `Traits.lean` (`d234936b72231024fbccf0030a08023836e5eb6e`), `Closures.lean` (`e60021de5406f9f21dacf6e994cbea1fb9264fa4`), `Dyn.lean` (`1ca9dd626eea93ec47dee2094febb8541d41c2c3`), `Constants.lean` (`9c6e588633544daa10581bd363eabba0fea52b70`), `ConstantsLean.lean`, `Static.lean` (`9d31798665d488b70730ea60c928e82c790d308b`), and `Drop.lean` (`a0119232ebcddb64b81d919fa9c363cc56f8ba0b`).

### 2. Paired Charon `0.1.210` (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, observed 2026-09-26)

- `charon/src/ast/llbc_ast.rs` and `charon/src/transform/control_flow/ullbc_to_llbc.rs`: `UnwindResume` → `Abort(AbortKind::Panic(None))`, `Call` `on_unwind` erasure, and `Assert` unwind-block summarization.
- `charon/src/options.rs`, `charon/src/bin/charon-driver/translate/get_mir.rs`, `charon/src/bin/charon-driver/translate/translate_crate.rs`, and `charon/src/bin/charon-driver/translate/translate_constants.rs`: `Preset::Aeneas` vs. `Preset::Soteria` and `--monomorphize`, `mir_promoted` selection, and symbolic `ConstantExprKind::Var` translation.

### 3. Zerocopy PME Guards and Historical Hermes Nested-Borrow Fixture (`google/zerocopy`)

- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`: `anneal/flake.nix` (blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`), `zerocopy/src/util/macros.rs`, `zerocopy/src/util/macro_util.rs`, `zerocopy/src/layout.rs`, and `zerocopy/src/doctests.rs` (plus historical context from `google/zerocopy` issues `#3030`, `#3199`, `#3208` and Aeneas Zulip message `573180904`).
- `google/zerocopy@9bdef60f295715bc113419661b376071cc18e2b3` (pinned to `AeneasVerif/aeneas@42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4` in `hermes/Cargo.toml`, tracked in `google/zerocopy` issue `#3227` and PR `#3223`):
  - `hermes/tests/fixtures/edge_cases_types/test_2_6_nested_refs/source/src/lib.rs` (blob `bbb4c462ef48003ed7926e55e96a31f524c7dfbb`).
  - `hermes/tests/fixtures/edge_cases_types/test_2_6_nested_refs/hermes.toml` (blob `eaf4c1f3fb0e8468fb8f57c6b3f174d80fee5177`).
  - `hermes/tests/fixtures/edge_cases_types/test_2_6_nested_refs/expected.stderr` (blob `d15940a498f1a8b11c8d36237745d58a6aeb4414`).

## Revalidation

To revalidate these boundaries on a newer Aeneas/Charon toolchain or execution-capable surface:

1. **Raw pointers and unsafe omissions**:
   - Diff `src/pure/Pure.ml` (`TRawPtr`, `fun_effect_info`, `GetTarget`), `src/interp/InterpPaths.ml` (`Deref` on `TRawPtr`), `src/interp/InterpExpressions.ml` (`RawPtr` rvalue and `AggregatedRawPtr`), `src/symbolic/SymbolicToPureExpressions.ml` (`CastRawPtr`), `backends/lean/Aeneas/Std/RawPtr.lean`, `Slice.lean`, `Std/Io.lean`, and `Core/Atomic.lean`.
   - Rerun `tests/src/raw_pointers.rs` and verify whether dereference still aborts in `InterpPaths.ml` or transitions to a separation-logic state obligation.
2. **Support/failure matrix and fail-closed diagnostics**:
   - Diff `src/Errors.ml`, `src/Config.ml` (`fail_hard`, `warnings_as_errors`, `drop_as_no_op`), `src/Main.ml`, and `src/Translate.ml`.
   - Run Aeneas with `-abort-on-error -warnings-as-errors` on positive and negative fixtures (`raw_pointers.rs`, `mutually-recursive-traits.rs`, function-pointer calls, `transmute`, `binop::offset`, outer-loop `break`, and `-eval-drops` vs. default `Drop`).
3. **Panic, abort, and unwind lowering**:
   - Diff Charon's `charon/src/transform/control_flow/ullbc_to_llbc.rs` (`UnwindResume`, `Call` `on_unwind`, `Assert`) and Aeneas's `InterpStatements.eval_statement` (`Abort _`), `PureMicroPassesGeneral.ml` (`intro_massert_visitor`), `Primitives.lean`, and `WP.lean`.
4. **Post-monomorphization errors (PMEs)**:
   - Execute a two-variant minimal PME probe (`fn guarded<T, U>() { static_assert!(T, U => size_of::<T>() == size_of::<U>()); }` with `valid()` calling `guarded::<u32, i32>()` and `invalid()` calling `guarded::<u8, u64>()`) under (a) native `cargo check`, (b) `charon cargo --preset=aeneas`, and (c) `charon cargo --preset=aeneas --monomorphize --start-from ...`, comparing whether `invalid()` is rejected by Charon or emitted as a polymorphic/specialized body without the admission constraint.
5. **Nested-borrow determinism probe (`test_2_6_nested_refs`)**:
   - Generate `.llbc` once from `pub fn nested(x: &&u32, y: &mut &u32, z: &&mut u32)` using the pinned Charon binary, record its SHA-256, and run the pinned Aeneas binary 100 times in fresh processes and output directories on that fixed `.llbc` file (separating Aeneas determinism from Charon), recording exit codes, stderr, and output SHA-256 digests.
