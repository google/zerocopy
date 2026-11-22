# Nominal Recursive MIR ADTs, Segmented Null-Gap Nested Array Columns, Three-Tier SQL Error Lattices, Sterbenz `libm`-Free Float-to-Int Rounding, and `Quot`-Free Relational Bag Proofs

## Summary

Extending a deductive Rust MIR verification framework (`google/zerocopy` `anneal/` at `233d60e7c72e1550c9fcc39cf8a36b4d00d8c4ed`) from flat-struct systems/codec workloads to tree-structured query planners, nested columnar execution engines, and IEEE-754/SQL expression kernels exposes five general verification and semantic boundaries:

1. **Nominal `AdtDefTable` + `PtrMetaKind` indirection vs. inline-tree `MirTy` recursion limits:** Representing Rust structs and enums by embedding field and variant `MirTy` lists inline inside `MirTy` fails closed with unbounded structural expansion on every heap-inductive Rust type (`enum Expr { Add(Box<Expr>, Box<Expr>) }`, recursive schema/type descriptors, nested columnar arrays, and recursive Protobuf messages). Indexing composite types nominally via `Program.adtDecls : List AdtDecl` (`MirTy.adt (id : AdtId)`) while tagging pointer constructors with explicit `PtrMetaKind` (`thin => 8 B`, `sliceLen => 16 B`, `dynVtable => 16 B` so even custom unsized DST struct pointers `*const Dst` return fixed sizes without unfolding `pointee`) resolves valid boxed recursive layouts in bounded inline-value fuel (`boxedRecursiveExpr_layout_24B`) while still rejecting illegal unboxed and zero-length-array value cycles (`struct Weird([Weird; 0])`) fail-closed (`unboxedAndZeroArrayCycles_rejected_failClosed`).
2. **Segmented active-row null-gap nested array invariants vs. Apache Arrow global monotonicity:** Apache Arrow `GenericListArray` (`apache/arrow-rs` `arrow-array/src/array/list_array.rs`) enforces global offset monotonicity `offsets[0] <= offsets[1] <= ... <= offsets[N]` even across `NULL` rows. High-throughput columnar engines that skip writing offsets for `NULL` list/array rows violate global monotonicity whenever two adjacent rows `r - 1` and `r` are both `NULL` (leaving arbitrary slack values in `offsets[r]`) or when the final row `N - 1` is `NULL` (`offsets[N]` unwritten). Sound spatial-memory specs must replace global monotonicity with the per-active-row invariant `isNull[r] = false -> offsets[r] <= offsets[r + 1] <= elements.len` (`naiveArrowCheck_rejects_valid_nullGap_column`, `readNullGapArrayRow_total_of_valid`).
3. **Three-tier SQL error lattice and `AND`/`OR` nondeterminism vs. `CASE`/`IF` left-to-right short-circuiting:** In `google/googlesql@762ca7a16f2b555c85b6f9250c713a82bd1052d6`, `ShouldSuppressError` (`googlesql/reference_impl/evaluation.cc:258-292`) partitions runtime failures into suppressible data-evaluation errors (`OUT_OF_RANGE`, `INVALID_ARGUMENT` — caught by `SAFE`, `IFERROR`, `ISERROR`, `NULLIFERROR` in `value_expr.cc:1645, 1941, 2011, 2209`) and unsuppressible engine/system aborts (`CANCELLED`, `DEADLINE_EXCEEDED`, `RESOURCE_EXHAUSTED`, `INTERNAL` — which must never be swallowed as `NULL` or `FALSE`; `isError_suppresses_userErr_but_propagates_sysAbort`). Furthermore, GoogleSQL specifies unordered/skippable evaluation for `AND`/`OR` (`docs/operators.md:2017-2018`, allowing vectorized engines to absorb `<user_err> AND FALSE == FALSE` while GoogleSQL's eager `ScalarFunctionCallExpr` + `LogicalFunction` in `algebrizer.cc:1141-1144`, `value_expr.cc:1619-1626`, `function.cc:6064-6108` fails on the first argument error) in contrast to strict left-to-right short-circuiting for `CASE` and `IF` (`docs/conditional_expressions.md:16-22`, `AlgebrizeCaseNoValue` in `algebrizer.cc:1185-1206`, `IfExpr::Eval` in `value_expr.cc:1862-1872`; `sqlAnd_false_absorbs_userErr_while_case_propagates_and_sysAbort_wins`).
4. **Sterbenz-exact `libm`-free `f64 -> i64` halfway-away-from-zero rounding:** SQL `CAST(DOUBLE AS INT64)` (`googlesql/public/functions/convert.h:84-94, 449-461`) rounds finite floats halfway away from zero (`round(in)`), whereas Rust `f64::round()` lowers to an external C `libm` foreign call (rejected by zero-host-`libm` MIR boundaries) and naive `(x + 0.5).trunc()` double-rounds `0.5 - 2^-54` (`0x3fdfffffffffffff`) to `1` instead of `0` across the `[0.25, 0.5) -> [0.5, 1.0)` binade boundary (`floorPlusHalf_doubleRounds_preHalf_while_sterbenz_is_exact`). Because every finite binary64 with `|x| >= 2^52` is already an exact integer and `trunc_f64 = (x as i64) as f64` satisfies Sterbenz's condition when `0.5 <= |x| < 2^52`, `rem = x - trunc_f64` has zero IEEE-754 rounding error and `(trunc_i64).wrapping_add((rem >= 0.5) as i64 - (rem <= -0.5) as i64)` is exact across all 64-bit float bit patterns with zero foreign calls (`support/sterbenz_cast_probe.rs`).
5. **`Quot`-free constructive bag equivalence and exact superaccumulator order invariance under closed tactic allowlists:** Under Anneal's Pass-1 syntactic boundary (`anneal/trusted/audit/TrustedBoundary.lean:564-657`, which excludes `termination_by`, `omega`, `rcases`, `rename_i`, `bv_decide`, and `grind`), relational unordered-output (`HashJoin`, `GroupBy`) and sliding-window (`SUM(double)` over 2163-bit integer superaccumulators) proofs discharge cleanly via decidable `countOcc` multiplicity predicates (`BagEquiv`) and `Nat`-fuel structural induction using zero `Quot.sound` or `Classical.choice` axioms (`countOcc_append`, `bagEquiv_swap_adjacent`, `sumExact_swap_adjacent`, `sumExact_window_slide_cancel`).

## Applicability

- **Examined subjects and revisions:**
  - `google/zerocopy` at `233d60e7c72e1550c9fcc39cf8a36b4d00d8c4ed`: `anneal/trusted/lean/Trusted/MirAst/Types.lean`, `anneal/trusted/lean/Trusted/MirSemantics/{Boundary.lean,Step.lean}`, `anneal/trusted/lean/foundation-lock.json`, and `anneal/trusted/audit/TrustedBoundary.lean`.
  - `google/googlesql` at `762ca7a16f2b555c85b6f9250c713a82bd1052d6`: `googlesql/reference_impl/{evaluation.h,evaluation.cc,value_expr.cc,algebrizer.cc,function.cc}`, `googlesql/public/functions/{arithmetics.h,convert.h}`, `googlesql/compliance/testdata/{logical_functions.test,case_statement_queries.test,aggregation_having_modifier_queries.test}`, and `docs/{operators.md,conditional_expressions.md}`.
  - `apache/arrow-rs` at `e02da695a51d1a941fd99beb91a0afbb00d49cdc`: `ListArray` / `OffsetBuffer` monotonicity invariant contrasted with active-row null-gap columnar offsets.
  - `rust-lang/rust` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`: `as i64` float-to-int saturating cast vs. `f64::round` `libm` lowering (`rustc` `1.94.0` empirical verification of `support/sterbenz_cast_probe.rs`).
  - `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`): kernel verification of `support/Wave2ColumnarAdtAndSqlSemantics.lean`.
- **Scope:** Finding 1 applies to any MIR-level verification tool (`Anneal`, `lean-miri`, `Charon`/`Aeneas`) lowering composite Rust types; Finding 2 applies to any columnar engine with nullable variable-length `List`/`Array` columns; Findings 3–4 apply to SQL expression evaluators and JIT compilers implementing GoogleSQL or ANSI SQL `SAFE` error handling and `DOUBLE -> INT64` casts; Finding 5 applies to relational algebra mechanizations in Lean 4 kernels with restricted tactic/axiom policies.

## Findings

### 1. Nominal `AdtDefTable` Indirection Breaks Recursive Rust Type Cycles Without Weakening Unboxed-Cycle Rejection

`Basis: source + formal`

In `anneal/trusted/lean/Trusted/MirAst/Types.lean` (`google/zerocopy@233d60e7c72e1550c9fcc39cf8a36b4d00d8c4ed`), `MirTy` currently models scalars, `.rawPtr (mutability) (pointee : MirTy)`, and fieldless `.enum (ty : EnumTy)`. Extending `MirTy` to general structs and payload-carrying enums via *inline structural trees*—embedding `fields : List MirTy` or `variantFields : List (List MirTy)` directly inside `MirTy`—creates an immediate blocker on recursive heap-allocated Rust types:

- Any self-referential or mutually recursive Rust type behind pointer indirection (`enum PlanNode { Filter { input: Box<PlanNode>, pred: Expr }, ... }`, `enum Column { Array { elements: Box<Column>, ... }, Struct { fields: Vec<Column> } }`, recursive schema descriptors, or recursive Protobuf AST nodes) unfolds infinitely through `Box<T>` -> `Unique<T>` -> `NonNull<T>` -> `*const T` (`MirTy.rawPtr _ pointee`), forcing `rustc-capture` either to emit an infinite Lean term or fail closed at a fixed recursion depth limit (e.g. `depth > 64`), and duplicating full nested struct/enum definitions across every local variable in `Mir.lean`.
- Replacing inline composite trees with a crate-level **nominal `AdtDefTable`** (`Program.adtDecls : List AdtDecl`, `MirTy.adt (id : AdtId)`) and explicit **`PtrMetaKind`** (`thin | sliceLen | dynVtable`) cleanly separates *nominal type identity* from *inline value layout*:
  1. In 64-bit Rust MIR, `.rawPtr` / `.ref` is 8 bytes iff `pointee : Sized`, and 16 bytes not only for `[U]`, `str`, and `dyn Trait`, *but also* for custom unsized DST structs (`struct Dst { hdr: u64, tail: [u8] }`, i.e., `TyKind::Adt(Dst)`). Carrying `PtrMetaKind` directly on `.rawPtr ptrMeta pointee` lets `byteSizeOfTy` (`support/Wave2ColumnarAdtAndSqlSemantics.lean:77-103`) return `some 8` (`thin`) or `some 16` (`sliceLen | dynVtable`) in $O(1)$ without ever unfolding `pointee`, while `rustc-capture` memoizes `(DefId, GenericArgsRef) -> AdtId` *before* lowering field types.
  2. Unfolding `.adt id` or `.array elem len` (even when `len == 0`!) consumes 1 unit of inline-nesting `fuel` (bounded by `table.length`). Valid pointer-recursive types such as `enum Expr { Lit(i64), Add(*const Expr, *const Expr), Slice(*const [Expr]) }` (`sampleAdtTable[0]`) resolve in `fuel = 2` to `some 24` (`boxedRecursiveExpr_layout_24B`), whereas both unboxed enum cycles (`enum Bad { SelfVal(Bad) }`, `sampleAdtTable[1]`) and zero-length array cycles (`struct Weird([Weird; 0])`, `sampleAdtTable[2]`) exhaust inline `fuel` and fail closed with `none` (`unboxedAndZeroArrayCycles_rejected_failClosed`).

### 2. Segmented Null-Gap Nested `Array` Column Offsets vs. Arrow Global Monotonicity

`Basis: source + formal`

Apache Arrow's `OffsetBuffer<O>` (`apache/arrow-rs@e02da695a51d1a941fd99beb91a0afbb00d49cdc`) requires `offsets[i] <= offsets[i + 1]` for *every* `0 <= i < N`, forcing writers of `NULL` list rows to copy forward `offsets[i + 1] = offsets[i]`. Columnar execution engines that populate `offsets[i]` and `offsets[i + 1]` only when row `i` is non-null (`!isNull[i]`) violate Arrow's global monotonicity in two exact positions while remaining 100% memory-safe:

1. **Interior multi-null gaps:** If row `0` is `[10, 20]` (`offsets[0] = 0, offsets[1] = 2`), rows `1` and `2` are both `NULL` (`isNull[1] = true, isNull[2] = true`), and row `3` is `[30]` (`offsets[3] = 2, offsets[4] = 3`), `offsets[2]` is never written by either row `1` or row `3` and may hold an arbitrary recycled `u32` value (e.g. `999999` in `validNullGapCol`, `Wave2ColumnarAdtAndSqlSemantics.lean:154-157`).
2. **Trailing null suffix:** If row `N - 1` is `NULL`, `offsets[N]` is never read and need not equal `elements.len()`.

As proved in `naiveArrowCheck_rejects_valid_nullGap_column` and `readNullGapArrayRow_total_of_valid` (`Wave2ColumnarAdtAndSqlSemantics.lean:159-203`), Arrow's global monotonicity predicate rejects `validNullGapCol` (`false`), whereas the per-active-row spatial invariant:
$$\forall r < N,\; \neg\mathsf{isNull}[r] \implies \mathsf{offsets}[r] \le \mathsf{offsets}[r + 1] \le |\mathsf{elements}|$$
is both necessary and sufficient to prove total, bounds-checked slice projection across all rows `0 .. N - 1`. (Corollary: unlike Arrow `ListArray::values()`, bulk child-column operations over a null-gap `Array` column cannot assume the active child elements form a single contiguous prefix `[offsets[0] .. offsets[N])` unless compacted or gated by active parent spans.)

### 3. Three-Tier SQL Error Lattice: Unsuppressible `sysAbortErr` and `AND`/`OR` Dominant-Value Absorption vs. `CASE`/`IF`

`Basis: source + formal`

Direct inspection of `google/googlesql@762ca7a16f2b555c85b6f9250c713a82bd1052d6` reveals two interacting error-semantics contracts that a single flat `Result<Value, Error>` monad cannot faithfully represent:

1. **Two distinct error tiers (`userEvalErr` vs. `sysAbortErr`):**
   - `IsSafeModeConvertibleError` and `ShouldSuppressError` (`googlesql/reference_impl/evaluation.cc:258-292`, declared at `evaluation.h:526-527`) return `false` for engine/system statuses (`kCancelled`, `kDeadlineExceeded`, `kResourceExhausted`, `kInternal`, `kUnimplemented`, `kAborted`, `kUnavailable`, `kDataLoss`, `kPermissionDenied`, `kUnauthenticated`, `kUnknown`) and `true` only for input-data evaluation errors (such as `kOutOfRange` / `kInvalidArgument` from `1 / 0`, `CAST` overflow, or finite-to-infinite IEEE-754 `CheckFloatOverflow` in `googlesql/public/functions/arithmetics.h:85-95, 122-152`).
   - `ScalarFunctionCallExpr::Eval` (`SAFE.` mode, `value_expr.cc:1645-1649`), `IfErrorExpr::Eval` (`value_expr.cc:1941-1953`), `IsErrorExpr::Eval` (`value_expr.cc:2011-2025`), and `NullIfErrorExpr::Eval` (`value_expr.cc:2209-2219`) all guard error recovery on `ShouldSuppressError`: a query cancellation, deadline timeout, or memory-accountant `RESOURCE_EXHAUSTED` abort (`value_expr.cc:1632-1639`, `evaluation.cc:295-303`) is **never** converted into `NULL`, `TRUE`, or a fallback value (`isError_suppresses_userErr_but_propagates_sysAbort`).
2. **`AND`/`OR` unordered dominant-value absorption vs. `CASE`/`IF` strict left-to-right short-circuiting:**
   - GoogleSQL's language specification for `AND` and `OR` (`docs/operators.md:2017-2018`) states: *"The order of evaluation of operands to `AND` and `OR` can vary, and evaluation can be skipped if unnecessary."* Consequently, when evaluating `a AND b` on a row where `a` raises `userEvalErr` (e.g. `1 / x > 0` for `x = 0`) and `b` evaluates to `FALSE`, a vectorized/SIMD engine or predicate reorderer may legally return `FALSE` (`evalSqlAnd3Tier vUserErr vFalse = vFalse`), **whereas** GoogleSQL's row-at-a-time `reference_impl` lowers `$and`/`$or` to `ScalarFunctionCallExpr(LogicalFunction)` (`algebrizer.cc:1141-1144`, `value_expr.cc:1619-1626`, `function.cc:6064-6108`), which evaluates arguments eagerly left-to-right and fails immediately on the first argument error! Differential compliance harnesses must therefore treat `<user_err> AND FALSE` (and `<user_err> OR TRUE`) as refining the relational set `{dominant_bool, userEvalErr}`, while still requiring `sysAbortErr` to dominate unconditionally (`(evalSqlAnd3Tier vSysCancel vFalse).err = .sysAbortErr`).
   - By contrast, `docs/conditional_expressions.md:16-22` mandates strict left-to-right short-circuiting for `CASE`, `IF`, `COALESCE`, `IFNULL`, and `NULLIF` (`AlgebrizeCaseNoValue` -> nested `IfExpr` in `algebrizer.cc:1185-1206`; `IfExpr::Eval` in `value_expr.cc:1862-1872`): in `CASE WHEN c0 THEN t0 WHEN c1 THEN t1 ELSE els END`, a `userEvalErr` in `c0` **must** fail the query immediately even if `c1` is `TRUE`, while a `userEvalErr` in `t0` **must** be ignored whenever `c0` is `FALSE` or `NULL` (`sqlAnd_false_absorbs_userErr_while_case_propagates_and_sysAbort_wins`).

### 4. Sterbenz-Exact `libm`-Free `f64 -> i64` Halfway-Away-From-Zero Cast

`Basis: source + formal + execution`

In `googlesql/public/functions/convert.h:84-94, 449-461`, `Convert<double, int64_t>` rejects non-finite inputs and values outside `[-2^63, 2^63)` (`CheckFloatToIntRange<double, int64_t>`), then returns `static_cast<int64_t>(round(in))` (C99 `round`: round halfway cases *away from zero*, e.g. `0.5 -> 1`, `-0.5 -> -1`, `2.5 -> 3`).

Implementing this in verified Rust faces two traps:
- Calling `f64::round(x)` lowers to an unverified foreign C `libm` symbol `round`, which is unavailable in `no_std`/self-contained MIR verification boundaries without host `libm` waivers.
- Approximating `round(x)` via `(x + 0.5).trunc()` (for `x >= 0`) suffers **IEEE-754 double-rounding** at `x = 0.5 - 2^-54` (`0x3fdfffffffffffff`, the largest binary64 strictly below `0.5`): because `x` lies in `[0.25, 0.5)` (`1 ULP = 2^-54`) while the exact sum `x + 0.5 = 1.0 - 2^-54` crosses into `[0.5, 1.0)` (`1 ULP = 2^-53`), round-ties-to-even rounds the odd midpoint up to `1.0`, yielding `1` instead of `0` (`floorPlusHalf_doubleRounds_preHalf_while_sterbenz_is_exact` in `Wave2ColumnarAdtAndSqlSemantics.lean:328-358`).

A pure-Rust, branchless, `libm`-free sequence avoids both traps (`sterbenz_round_away_from_zero_to_i64` in `support/sterbenz_cast_probe.rs:21-41`):
```rust
if !x.is_finite() || x < -9_223_372_036_854_775_808.0_f64 || x >= 9_223_372_036_854_775_808.0_f64 {
    return None;
}
let trunc_i64 = x as i64;
let rem = x - (trunc_i64 as f64);
let adj = (rem >= 0.5_f64) as i64 - (rem <= -0.5_f64) as i64;
Some(trunc_i64.wrapping_add(adj))
```
Exactness holds across every binary64 bit pattern:
1. **Range boundary:** `+2^63` (`9223372036854775808.0_f64`, `0x43e0000000000000`) and `-2^63` (`0xc3e0000000000000`) are exact binary64 powers of two; the largest binary64 strictly below `+2^63` is `2^63 - 1024` (`0x43dfffffffffffff`), and the next binary64 below `-2^63` is `-2^63 - 2048` (`0xc3e0000000000001`).
2. **Large integer regime (`2^52 <= |x| <= 2^63`):** Because `1 ULP >= 1.0` for `|x| >= 2^52`, `x` is already an exact integer (`trunc_i64` is exact, `trunc_i64 as f64 == x` even for odd integers in `[2^52, 2^53]` and even integers in `[2^53, 2^63]`, `rem == 0.0`, `adj == 0`), including `x == -2^63` where `trunc_i64 == i64::MIN` and `wrapping_add(0) == i64::MIN`.
3. **Fractional regime (`|x| < 2^52`):** `trunc_i64` has `|trunc_i64| <= 2^52 - 1`, so `trunc_f64 = trunc_i64 as f64` is exact. Whenever `|x| < 1.0`, `trunc_f64 == 0.0`, so `rem = x - 0.0 == x` is exact (`0.5 - 2^-54 < 0.5 -> adj = 0`). Whenever `1.0 <= |x| < 2^52`, `|x| / 2 <= |trunc_f64| <= |x|` with identical sign, so by **Sterbenz's Lemma** `rem = x - trunc_f64` is computed in IEEE-754 binary64 with **zero rounding error**, and comparing `rem >= 0.5` / `rem <= -0.5` decides the exact mathematical fractional part!

### 5. `Quot`-Free Constructive Bag Equivalence and Superaccumulator Invariance Inside `TrustedBoundary.lean`

`Basis: source + formal + execution`

In `anneal/trusted/audit/TrustedBoundary.lean:564-657, 1231-1234` (`google/zerocopy@233d60e7c72e1550c9fcc39cf8a36b4d00d8c4ed`), `allowedCommandSyntaxKinds` excludes `termination_by` / `decreasing_by`, `allowedTheoryTacticKinds` restricts `theory/` proofs to a closed 22-tactic allowlist (excluding `omega`, `rcases`, `rename_i`, `bv_decide`, `grind`, `native_decide`, and `locationType` `at h ⊢`), and Phase-2 `.olean` auditing (`ensureReplayableConstant`) hard-rejects `ci.isUnsafe || ci.isPartial` — catching the `foo._unsafe_rec` auxiliary constant that `leanprover/lean4` `v4.34.1`'s LCNF compiler synthesizes for naive computable equation-compiler recursion over `Nat` or `List`!

`support/Wave2ColumnarAdtAndSqlSemantics.lean` demonstrates how to author **100% computable (`0` `noncomputable`), `0`-`_unsafe_rec`** relational and layout theories that pass both `TrustedBoundary.inspectSource` and Phase-2 `.olean` constant auditing:
- Expressing `Nat`-fuel and `List` recursion via explicit kernel recursors and foundation folds (`@Nat.rec` in `byteSizeOfTy` and `List.foldr` in `sumFieldsSizeWith`, `arrowGlobalMonotonic`, `countOcc`, and `sumExact`) preserves `rfl` / `dsimp` definitional reduction while emitting **zero** `_unsafe_rec` constants (`0` `noncomputable` modifiers required).
- Defining `BagEquiv eqA xs ys := ∀ k, countOcc eqA k xs = countOcc eqA k ys` over boolean key comparator `eqA` (e.g. GoogleSQL's `ValueContentEquals` where `-0.0 == +0.0` and `NaN == NaN`) yields constructive, `Quot`-free partition/append and swap lemmas (`countOcc_append`, `bagEquiv_swap_adjacent`) proved using only `intro`, `dsimp only`, `change`, `rw`, `cases`, `<;>`, and `rfl` (avoiding `at h ⊢` `Lean.Parser.Tactic.locationType`, which `TrustedBoundary.inspectSource` rejects, via `revert h; dsimp only [...]`).
- Modeling fixed-point superaccumulator state over exact integer chunks yields order-independent grouping and exact `Add`+`Remove` sliding-window cancellation (`sumExact_swap_adjacent`, `sumExact_window_slide_cancel`) with axiom footprint `⊆ {propext}` (`0` `Quot.sound`, `0` `Classical.choice`, `0` `sorryAx`, `0` `_unsafe_rec`).

## Boundaries

- **Custom DST tail verification in `Trusted.MirSemantics.Layout`:** While tagging pointer constructors with `PtrMetaKind` (`thin | sliceLen | dynVtable`) avoids unfolding `pointee` during byte-size calculation, a self-auditing MIR semantics that checks well-formedness of `PtrMetaKind` against `AdtDefTable` still computes a structural `unsizedTailKind` pass over `AdtDefTable` (using the same `table.length` fuel bound that rejects unboxed value cycles).
- **Hardware FP control-register state (`MXCSR` / `FPCR`):** The pure-Rust Sterbenz `f64 -> i64` rounding sequence in `support/sterbenz_cast_probe.rs` assumes standard IEEE-754 round-to-nearest-even (`RNE`) without flush-to-zero (`FTZ`) or denormals-are-zero (`DAZ`), and assumes masked IEEE-754 floating-point exceptions (`MXCSR[12:7] = 0x1f80` on x86-64). Host processes that link `-ffast-math` (`crtfastmath.o`) or unmask `FE_INEXACT` / `FE_INVALID` via `feenableexcept` must scrub/restore `MXCSR` at the FFI/JIT entry boundary.
- **Multi-error selection order in `AND`/`OR`:** When *neither* operand of `a AND b` evaluates to `FALSE` and *both* `a` and `b` raise suppressible `userEvalErr` statuses with distinct messages or codes, `docs/operators.md:2017-2018` permits returning *either* operand's error; differential harnesses must therefore check membership in the reachable error set rather than asserting left-to-right error priority on `AND`/`OR`.

## Evidence

- **Upstream sources inspected:**
  - `google/zerocopy` (`233d60e7c72e1550c9fcc39cf8a36b4d00d8c4ed`):
    - `anneal/trusted/lean/Trusted/MirAst/Types.lean` (`MirTy` variants).
    - `anneal/trusted/lean/Trusted/MirSemantics/Boundary.lean:164-240` (`BodyStaticAdmitted`).
    - `anneal/trusted/audit/TrustedBoundary.lean:539-683` (`allowedCommandSyntaxKinds`, `allowedTheoryTacticKinds`, `allowedTheorySyntaxKinds`).
    - `anneal/trusted/lean/foundation-lock.json` (admitted `Init.*` modules).
  - `google/googlesql` (`762ca7a16f2b555c85b6f9250c713a82bd1052d6`):
    - `googlesql/reference_impl/evaluation.h:526-531` and `evaluation.cc:258-303` (`IsSafeModeConvertibleError`, `ShouldSuppressError`, `PeriodicallyVerifyNotAborted`).
    - `googlesql/reference_impl/value_expr.cc:1608-1656` (`ScalarFunctionCallExpr::Eval`), `:1862-1872` (`IfExpr::Eval`), `:1933-1954` (`IfErrorExpr::Eval`), `:2001-2026` (`IsErrorExpr::Eval`), `:2199-2220` (`NullIfErrorExpr::Eval`).
    - `googlesql/reference_impl/algebrizer.cc:978-988, 1141-1144, 1185-1206` (`AlgebrizeCaseNoValue` vs. `LogicalFunction` call lowering) and `function.cc:2465-2468, 6064-6108` (`LogicalFunction::Eval`).
    - `googlesql/public/functions/arithmetics.h:85-95, 122-152` (`CheckFloatOverflow`) and `convert.h:84-94, 449-461` (`CheckFloatToIntRange`, `Convert<double, int64_t>`).
    - `docs/operators.md:2017-2018` (`AND`/`OR` evaluation order and skippability) and `docs/conditional_expressions.md:16-32` (`CASE`/`IF` left-to-right short-circuiting).
- **Preserved artifacts (`support/`):**
  - `support/Wave2ColumnarAdtAndSqlSemantics.lean`: Kernel-checked under `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with `prelude` + `foundation-lock.json`-admitted `Init.*` imports, `-DElab.async=false -Ddebug.skipKernelTC=false`, zero `sorryAx`, zero `Lean.ofReduceBool`, zero `Quot.sound` / `Classical.choice`, and zero `_unsafe_rec` / `partial` constants.
  - `support/sterbenz_cast_probe.rs`: Self-contained Rust x86-64 empirical harness verifying `buggy_floor_plus_half_to_i64` double-rounding at `0x3fdfffffffffffff` / `0xbfdfffffffffffff` (`+/-1` vs. `0`) and exact agreement of `sterbenz_round_away_from_zero_to_i64` with `f64::round()` across subnormals, `+/-0.0`, `0.5 - 2^-54`, `2^52 - 0.5`, `2^52 + 1`, `-2^63`, `2^63 - 1024`, `+2^63`, `-2^63 - 2048`, `NaN`, and `+/-Inf`.

## Revalidation

1. **Re-verify the Lean 4 mechanization (`< 3s`):**
   ```sh
   PKG="reports/nominal-recursive-mir-adts-null-gap-arrays-and-sql-error-dominance/support"
   lean -DElab.async=false -Ddebug.skipKernelTC=false "$PKG/Wave2ColumnarAdtAndSqlSemantics.lean"
   ```
2. **Compile and run the Sterbenz float-to-int x86-64 probe (`< 2s`):**
   ```sh
   PKG="reports/nominal-recursive-mir-adts-null-gap-arrays-and-sql-error-dominance/support"
   rustc -C opt-level=2 "$PKG/sterbenz_cast_probe.rs" -o /tmp/sterbenz_cast_probe && /tmp/sterbenz_cast_probe
   ```
