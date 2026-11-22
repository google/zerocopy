# `rustc` Pattern Types (`TyKind::Pat`), Nested `Option` Niche Stacking, LLVM `range`/`nonnull` Elimination, and the Miri vs. `-Z ub-checks` Validity Cliff

## Summary

In 2026 `rustc` (`rust-lang/rust` revisions `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, and `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), core niche-bearing library types—including `NonNull<T>`, `NonZero<T>`, `Nanoseconds`, `CodePointInner`, `UsizeNoHighBit`, `NotAllOnes<T>`, and (by late 2026) `Box<T>` via `BoxRaw<T>`—are implemented on top of compiler-internal pattern types (`TyKind::Pat` / `std::pat::pattern_type!`), completely replacing the legacy `#[rustc_layout_scalar_valid_range_start]` and `#[rustc_layout_scalar_valid_range_end]` attributes across `core::num::niche_types`, `core::num::nonzero`, and `core::ptr::non_null`.

Six load-bearing invariants and failure boundaries govern how `TyKind::Pat` flows from `core`/`alloc` through layout computation, LLVM optimization, runtime UB checking, `rustc_transmute`, and formal MIR verification:

1. **Transmute-only construction and extraction (`rust-lang/compiler-team#807`).** `core::num::niche_types` constructs and reads pattern-type wrappers exclusively via `core::mem::transmute` (and explicitly implements `StructuralPartialEq` by hand instead of `#[derive(PartialEq)]`) because field projection `.0` into scalar-valid-range types is banned to prevent MIR projection chains from dropping `!range`/`!nonnull` metadata and regressing optimization.
2. **Single-`WrappingRange` layout narrowing and the signed-only `Or`-pattern asymmetry.** `rustc_ty_utils::layout::layout_of_uncached` lowers `PatternKind::Range`, `PatternKind::NotNull`, and two-arm `PatternKind::Or` into a single inclusive modular `rustc_abi::WrappingRange` on `BackendRepr::Scalar` (or field `a` of `BackendRepr::ScalarPair` for wide `!null` pointers). Because `WrappingRange` encodes at most one contiguous circular arc on $\mathbb{Z}/2^w\mathbb{Z}$, `layout.rs` admits two-arm `Or` patterns only on signed integers connected across the signed overflow boundary (`i8 is ..=-1 | 1..`, `size_of::<Option<_>>() == 1`) and rejects unsigned `Or` patterns (`u8 is 250..=255 | 0..=5`) at **layout time** (`only signed integer base types are allowed for or-pattern pattern types at present`).
3. **Iterative `Option` niche stacking follows `Niche::reserve`'s signed-closest-to-zero rule until exhaustion.** For any `w`-bit scalar range `r`, `k` nested `Option` wrappers fit inside the single `w`-bit slot if and only if `k <= 2^w - |valid(r)|`. With `Pat1To10 = pattern_type!(u8 is 1..=10)`, `Niche::reserve` (`count = 1`) allocates `None` tags `0`, `255` (`-1i8`), and `254` (`-2i8`) in sequence, keeping `Option<Option<Option<Pat1To10>>>` at `1` byte; when niches are exhausted (`Option<Option<NonZero<u8>>>` at `k = 2`, `Option<Option<Option<Pat254>>>` at `k = 3`, `Option<Option<NonNull<u8>>>` and `Option<Option<Box<u8>>>` at `k = 2`), pigeonhole forces external tag expansion (`2` bytes or `16` bytes).
4. **LLVM `range(lo, hi)` / `nonnull` erases out-of-range branches at `-O2`, turning invalid raw transmutes into silent miscompilations.** At `OptLevel != No`, `rustc` transmits `WrappingRange` to LLVM via function argument/return `range(iW lo, hi)` and `nonnull` attributes, load `!range`/`!nonnull` metadata, and inline transmute `assume_scalar_range` calls. LLVM 23.1.5 (and LLVM 22.1.6) folds `take_pat_u8` (`if v == 0 || v > 10 { panic!(...) }`) into `ret i8 %x` and `take_pat_nonnull` (`if raw.is_null() { panic!(...) }`) into `ptrtoint; ret`. Passing `transmute::<u8, Pat1To10>(11)` into `take_pat_u8` aborts (`rc = -6`) at `-O0 -Z ub-checks=yes` but silently returns `11` (`rc = 0`) at `-O2 -Z ub-checks=no`.
5. **Sharp validity cliff between Miri and `-Z ub-checks=yes`.** MIR's `CheckEnums` pass (`compiler/rustc_mir_transform/src/check_enums.rs`) checks `Rvalue::Cast(CastKind::Transmute, op, ty)` **only** when `ty` is `ty::Adt(adt_def, _)` with `adt_def.is_enum()`, and `CheckNull` checks only pointer dereferences/borrows. Consequently, under `-O0 -Z ub-checks=yes`, raw `transmute` into `Pat1To10` (`11`), `PatNonNull` (`null`), and `NonZero<u8>` (`0`) all succeed silently (`rc = 0`), whereas Miri flags all three as immediate UB (`rc = 1`, reporting `NonZero<u8>` at projection path `.0.0` through `NonZero -> NonZeroU8Inner -> pattern_type!(u8 is 1..)`). By contrast, `NonZero::<u8>::new_unchecked(0)` aborts (`rc = -6`) under `-Z ub-checks=yes` solely via `core`'s library `assert_unsafe_precondition!(check_language_ub, ...)` (which disables itself under `cfg!(miri)` so Miri reaches `intrinsics::unreachable()`), and `transmute::<u8, Option<Pat1To10>>(99)` aborts (`rc = -6`) because `Option<Pat1To10>` is an enum.
6. **`rustc_transmute` and Anneal both fail closed on `TyKind::Pat`.** `rustc_transmute::layout::tree::Tree::from_ty` has no `ty::Pat` arm and returns `Err::NotYetSupported`, causing `TransmuteFrom` to fail with `E0277` for `Pat1To10 <-> u8` and `NonZero<u8> -> u8` (upstream PR `rust-lang/rust#148449` addresses `NonZero` scalar ranges and remains open). In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst.MirTy` maps `TyKind::Pat` (and non-fieldless ADTs) to `MirTy.unsupported` and `Trusted.MirAst.Rvalue` maps all `Rvalue::Cast` (including `CastKind::Transmute`) to `Rvalue.unsupported`.

All algebraic claims—iterative `Option` niche-stacking disjointness/injectivity (`nestedOption_niche_disjoint_and_injective`), LLVM `range` dead-branch elimination soundness (`llvm_range_elim_sound_under_pat_validity`), subtype widening vs. narrowing necessity (`pat_to_base_always_valid_and_base_to_pat_requires_range_check`), general pigeonhole niche-exhaustion impossibility (`no_injective_encoding_when_niches_exhausted`), and three constructive counterexamples (`ce1_invalid_pat_transmute_miscompiles_under_llvm_range_attr`, `ce2_niche_exhaustion_forces_tag_expansion`, `ce3_ub_checks_bypass_misses_raw_transmute_to_nonzero`)—are mechanized and kernel-checked in `support/PatternTypesNicheAndRangeSoundness.lean` under Lean `v4.34.1` with zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`, zero `partial def`, and zero `._unsafe_rec` constants (`206` declarations, `80` theorems). Model–system relation: the Lean proofs verify the formal `WrappingRange` / `nestOption` / `evalRangeGuarded` / `MirDstTy` specification; alignment with `rustc`, LLVM, and Miri is established via primary-source inspection and empirical execution rather than mechanized compiler extraction.

## Applicability

### Studied Subjects and Relationships

This report combines primary-source audits, empirical execution, and formal mechanization across five durable upstream subjects listed in `REPORT.json`:

| Subject | Repository & Immutable Revision | Role in This Report |
| :--- | :--- | :--- |
| `rustc 1.102.0-nightly` + LLVM `23.1.5` + Miri | `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (2026-11-11) | Primary-source audit and execution evidence for LLVM 23.1.5 IR emission (`range(i8 1, 11)`, `range(i32 1, -2147483648)`, `nonnull`), `BoxRaw<T>`, `-Z ub-checks` vs. Miri validity cliff, signed/unsigned `Or` patterns, and `TransmuteFrom` rejection (`support/probe_results_rustc_1_102_nightly_llvm23.json`). |
| `rust-lang/rust` upstream `master` | `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (2026-11-22) | Primary-source audit confirming current `core`, `alloc`, `rustc_ty_utils`, `rustc_abi`, `rustc_codegen_llvm`, `rustc_codegen_ssa`, `rustc_mir_transform`, `rustc_const_eval`, and `rustc_transmute` implementations, including the Macro 2.0 `pub macro pattern_type` transition. |
| `rustc 1.98.0-nightly` + LLVM `22.1.6` + Miri `0.1.0` | `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (2026-05-31) | Live execution on `x86_64-unknown-linux-gnu` via `support/probe_pattern_types.py` (`support/probe_results_rustc_1_98_nightly.json`), extending the probe with concrete `NICHE_BYTES` extraction, `Pat254` niche-exhaustion boundary, `bad_opt_pat_enum_transmute` `CheckEnums` contrast, `-O2` vs. `-O0` miscompilation execution, and `TransmuteFrom<NonZero<u8>>` rejection. |
| Anneal trusted MIR specification | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Primary-source audit of `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `vendor/lean-miri/Miri/ABI/WrappingRange.lean` to determine Anneal's current trusted-boundary treatment of `TyKind::Pat` and `CastKind::Transmute`. |
| Lean 4 kernel | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Kernel verification of `support/PatternTypesNicheAndRangeSoundness.lean` (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) and environment axiom/`_unsafe_rec` audit. |

### Shared Behavior vs. Version-Specific Deltas

Every architectural finding below was checked across all three `rust-lang/rust` revisions (`14210df0e27c`, `3ef0c22cdb86`, `342d74463af7`).

**Shared across all three `rust-lang/rust` revisions (2026-05-31 through 2026-11-22):**
- `NonNull<T>` wraps `pattern_type!(*const T is !null)`; `NonZero<T>` wraps `T::NonZeroInner`, whose inner types in `library/core/src/num/niche_types.rs` are `#[repr(transparent)]` wrappers around `pattern_type!($int is $pat)` using `transmute` for construction and `.as_inner()` extraction.
- `rustc_ty_utils::layout::layout_of_uncached` lowers `PatternKind::Range`, `PatternKind::NotNull`, and signed two-arm `PatternKind::Or` into a single `WrappingRange` and rejects unsigned `Or` patterns at layout time.
- `Niche::reserve` (`count = 1`) selects the adjacent niche minimizing `size.sign_extend(...).unsigned_abs()` (choosing `0`, then `255`, then `254` for `Pat1To10`).
- LLVM attribute/metadata/assume emission (`range(lo, hi)`, `nonnull`, `!range`, `!nonnull`, `assume_scalar_range`) is gated on `OptLevel != No` and folds out-of-range branches identically across LLVM `22.1.6` and LLVM `23.1.5`.
- `CheckEnums` filters strictly on `ty::Adt(adt_def, _)` with `adt_def.is_enum()`, missing raw `transmute` to `TyKind::Pat` and `NonZero<u8>` while catching `Option<Pat1To10>`.
- `Miri`'s `ValidityVisitor` validates `TyKind::Pat` via `visit_scalar` and reports `NonZero<u8>` invalidity at `.0.0`.
- `rustc_transmute::layout::tree::Tree::from_ty` rejects `TyKind::Pat` (and `NonZero<u8>`) via `_ => Err(Err::NotYetSupported)`.

**Version-specific differences observed across the three revisions:**

| Feature / Mechanism | `1.98.0-nightly` (`14210df0e27c`, 2026-05-31) | `1.102.0-nightly` (`3ef0c22cdb86`, 2026-11-11) | Upstream `master` (`342d74463af7`, 2026-11-22) |
| :--- | :--- | :--- | :--- |
| `pattern_type!` macro definition (`library/core/src/pat.rs:10-18`) | `#[macro_export] #[rustc_builtin_macro(pattern_type)] macro_rules! pattern_type` (`feature = "pattern_type_macro"`); inside `core` imported at `core::pattern_type!`, publicly re-exported at `std::pat::pattern_type!`. | Same `#[macro_export] #[rustc_builtin_macro(pattern_type)] macro_rules! pattern_type`. | Migrated to Macro 2.0 `pub macro pattern_type($($arg:tt)*) { k#pattern_type($($arg)*) }` under `#[allow_internal_unstable(internal_syntax)]` and `#[unstable(feature = "pattern_types", issue = "123646")]`, directly at `core::pat::pattern_type!`. |
| `Box<T, A>` internal pointer wrapper (`library/alloc/src/boxed.rs`) | `pub struct Box<T: ?Sized, A: Allocator = Global>(Unique<T>, A);` (`boxed.rs:234-237`), where `Unique<T>` lives in `core::ptr::unique`. | `pub struct Box<T: ?Sized, A: Allocator = Global>(BoxRaw<T>, A);` (`boxed.rs:308-311`) with `#[repr(transparent)] struct BoxRaw<T: ?Sized> { pointer: NonNull<T>, _marker: PhantomData<T> }` (`boxed.rs:238-241`, citing `#162850`). | Same `BoxRaw<T>` wrapper (`boxed.rs:238-241, 308-311`); `library/core/src/ptr/unique.rs` removed. |
| `Niche::reserve` `bool` guard (`compiler/rustc_abi/src/lib.rs`) | `let is_bool = size.bytes() == 1 && v == WrappingRange { start: 0, end: 1 };` (`lib.rs:2067`). | `if count == 1 && v != (WrappingRange { start: 0, end: 1 })` (`lib.rs:2167`). | Same `v != (WrappingRange { start: 0, end: 1 })` (`lib.rs:2177`). |
| Diagnostic printing of `TyKind::Pat` (Miri & `E0277`) | Prints `(u8) is 1..=10` and `(*const u8) is !null`. | Prints `pattern_type!(u8 is 1..=10)` and `pattern_type!(*const u8 is !null)`. | Same `pattern_type!(...)` pretty-printing. |
| LLVM backend version | LLVM `22.1.6` | LLVM `23.1.5` | LLVM `23.x` |

### Target and Feature-Flag Scope

- **Target architecture:** Empirical execution measurements ran on `x86_64-unknown-linux-gnu` (`64`-bit pointers, `usize`/`isize` = `8` bytes, little-endian). Pointer-size measurements (`PatNonNull = 8`, `Option<NonNull<u8>> = 8`, `Option<Option<NonNull<u8>>> = 16`) scale with pointer width (`4` and `8` bytes on `32`-bit targets).
- **Feature gates:** User-level pattern types require `#![feature(pattern_types, pattern_type_macro)]` (an internal compiler feature emitting `#[warn(internal_features)]`); transmutability trait checks require `#![feature(transmutability)]`. Standard-library consumers (`NonZero<T>`, `NonNull<T>`, `Box<T>`, `Option<T>`) inherit all layout, niche, LLVM `range`/`nonnull`, and Miri/UB-check behaviors on stable Rust without enabling unstable features.
- **Optimization & UB-check flags:** LLVM `range`/`nonnull` attribute, load-metadata, and `assume_scalar_range` emission require `-C opt-level != 0` (`1`, `2`, `3`, `s`, `z`). `CheckEnums`, `CheckNull`, and `assert_unsafe_precondition!(check_language_ub, ...)` are controlled by `-Z ub-checks=yes|no` (defaulting to `yes` with debug assertions and `no` under `-O` unless overridden).

## Findings

### 1. Standard-Library Pattern-Type Architecture: Replacing `#[rustc_layout_scalar_valid_range_*]`

Basis: source (`rust-lang/rust` @ `342d74463af7`, `3ef0c22cdb86`, `14210df0e27c`) + documentation (`rust-lang/compiler-team#807`).

#### 1.1 `library/core/src/pat.rs`: Surface Macro, `RangePattern`, and `!null` Built-In Impls

`library/core/src/pat.rs` provides the compiler-internal entry point for pattern types. At `342d74463af7` (`library/core/src/pat.rs:10-39, 78-89`), the macro and helper trait are defined verbatim as:

```rust
#[allow_internal_unstable(internal_syntax)]
#[unstable(feature = "pattern_types", issue = "123646")]
#[diagnostic::opaque]
pub macro pattern_type($( $arg:tt )*) {
    k#pattern_type($( $arg )*)
}

#[unstable(feature = "pattern_type_range_trait", issue = "123646")]
pub const trait RangePattern {
    #[lang = "RangeMin"]
    const MIN: Self;
    #[lang = "RangeMax"]
    const MAX: Self;
    #[lang = "RangeSub"]
    fn sub_one(self) -> Self;
}
```

`RangePattern` is implemented for all twelve integer primitives (`i8`, `i16`, `i32`, `i64`, `i128`, `isize`, `u8`, `u16`, `u32`, `u64`, `u128`, `usize`) and `char` (`pat.rs:59-76`), normalizing open-ended ranges (`1..`, `..0`) and exclusive endpoints (`..u32::MAX`) into inclusive endpoints during AST-to-HIR/type lowering. In addition, `pat.rs:78-89` supplies five built-in marker and unsized-coercion implementations directly on `!null` raw-pointer pattern types:
- `impl<T: PointeeSized, U: PointeeSized> CoerceUnsized<pattern_type!(*const U is !null)> for pattern_type!(*const T is !null) where T: Unsize<U>`
- `impl<T: DispatchFromDyn<U>, U> DispatchFromDyn<pattern_type!(U is !null)> for pattern_type!(T is !null)`
- `impl<T: PointeeSized> Unpin for pattern_type!(*const T is !null)`
- `unsafe impl<T: PointeeSized> Freeze for pattern_type!(*const T is !null)`
- `unsafe impl<T: PointeeSized> Freeze for pattern_type!(*mut T is !null)`

At earlier 2026 revisions (`14210df0e27c` and `3ef0c22cdb86`), `pat.rs:10-18` instead declared `#[macro_export] #[rustc_builtin_macro(pattern_type)] macro_rules! pattern_type`, placing the macro at `core::pattern_type!` (and re-exporting it at `std::pat::pattern_type!`). Using `std::pat::pattern_type` works uniformly across all three revisions.

#### 1.2 `library/core/src/num/niche_types.rs`: `define_valid_range_type!` and the Field-Projection Ban (`compiler-team#807`)

`library/core/src/num/niche_types.rs` completely eliminates `#[rustc_layout_scalar_valid_range_start]` and `#[rustc_layout_scalar_valid_range_end]` (zero occurrences across `niche_types.rs`, `nonzero.rs`, and `non_null.rs` at all three audited revisions). Instead, `define_valid_range_type!` (`niche_types.rs:13-95`) expands every internal range-restricted scalar wrapper to a `#[repr(transparent)]` tuple struct around `pattern_type!`:

```rust
#[derive(Clone, Copy)]
#[repr(transparent)]
$vis struct $name(pattern_type!($int is $pat));
```

Every operation on `$name` deliberately uses `core::mem::transmute` rather than `.0` field projection (`niche_types.rs:24-57`):
- `new(val)`: checks `if let $pat = val`, then returns `Some(unsafe { $name(crate::mem::transmute(val)) })`.
- `new_unchecked(val)`: returns `unsafe { crate::mem::transmute(val) }`.
- `as_inner(self)`: returns `unsafe { crate::mem::transmute(self) }`, with the explicit comment `// (Not using .0 because that has perf regressions.)`.
- `StructuralPartialEq`, `Eq`, `PartialEq`, `Ord`, `PartialOrd`, `Hash`, `Debug`: implemented manually via `self.as_inner()`, explicitly citing `rust-lang/compiler-team#807`:
  > "This is required to allow matching a constant. We don't get it from a derive because the derived `PartialEq` would do a field projection, which is banned by `<https://github.com/rust-lang/compiler-team/issues/807>`."

**Why `compiler-team#807` bans `.0` field projection:** As established in accepted MCP `rust-lang/compiler-team#807` (and echoed in `library/core/src/num/nonzero.rs:614-635` on `NonZero::get` and `library/core/src/ptr/non_null.rs:410-417` on `NonNull::as_ptr`), collapsing a chain of MIR field projections `((*_1).0).0` through a scalar-valid-range wrapper down to its unrestricted inner scalar produces a single load at the *base* type (`*const u8` or `u8`), making it harder for codegen backends to attach `!nonnull` or `!range` metadata to that load. Moreover, when `NonZero::get` or `as_inner` is MIR-inlined, there is no function-parameter boundary to carry an LLVM `range(...)` attribute. Emitting `Rvalue::Cast(CastKind::Transmute, ...)` forces codegen through `codegen_transmute_scalar` (`compiler/rustc_codegen_ssa/src/mir/rvalue.rs:1141-1149`), which explicitly preserves scalar range knowledge via `assume_scalar_range` (or `to_immediate_scalar` on loads). Because a `TyKind::Pat` value has no user-addressable field to project in the first place, `transmute` is the sole MIR-level boundary for creating or unwrapping pattern types.

The complete inventory of `define_valid_range_type!` instantiations in `library/core/src/num/niche_types.rs:97-164` (`342d74463af7`) is:

| Wrapper Type | Underlying Pattern Type | `WrappingRange` (unsigned bits) | Niches Available | Primary Consumer(s) |
| :--- | :--- | :--- | :--- | :--- |
| `Nanoseconds` | `u32 is 0..=999_999_999` | `0..=999_999_999` | `3,294,967,296` | `core::time::Duration` |
| `NonZeroU{8,16,32,64,128,size}Inner` | `uN is 1..` | `1..=uN::MAX` | `1` (`0`) | `core::num::NonZero<uN>` |
| `NonZeroI{8,16,32,64,128,size}Inner` | `iN is ..0 \| 1..` | `1..=uN::MAX` (wraps across signed `MIN`/`MAX`) | `1` (`0`) | `core::num::NonZero<iN>` |
| `NonZeroCharInner` | `char is '\u{1}'..='\u{10ffff}'` | `1..=0x10ffff` | `4,293,853,185` | `core::num::NonZero<char>` |
| `UsizeNoHighBit` | `usize is 0..=HALF_USIZE` | `0..=(usize::MAX >> 1)` | `2^(ptr_bits - 1)` | `alloc` capacity/length niches |
| `UsizeNoHighBitMinusOne` | `usize is 0..=HALF_USIZE_MINUS_ONE` | `0..=((usize::MAX >> 1) - 1)` | `2^(ptr_bits - 1) + 1` | `alloc` capacity niches |
| `U32NotAllOnes`, `U64NotAllOnes` | `uN is 0..uN::MAX` | `0..=(uN::MAX - 1)` | `1` (`uN::MAX`) | `NotAllOnes<uN>` |
| `I32NotAllOnes`, `I64NotAllOnes` | `iN is ..-1 \| 0..` | `0..=(uN::MAX - 1)` (wraps across signed `MIN`/`MAX`) | `1` (`-1` = `uN::MAX`) | `NotAllOnes<iN>` |
| `CodePointInner` | `u32 is 0..=0x10ffff` | `0..=0x10ffff` | `4,293,853,184` | Unicode scalar/codepoint storage |

Notice the two-layer transparent nesting of `NonZero<T>` (`library/core/src/num/nonzero.rs:109-112`):

```rust
#[repr(transparent)]
#[rustc_nonnull_optimization_guaranteed]
#[rustc_diagnostic_item = "NonZero"]
pub struct NonZero<T: ZeroablePrimitive>(T::NonZeroInner);
```

For `NonZero<u8>`, field `.0` is `NonZeroU8Inner`, and field `.0.0` is `pattern_type!(u8 is 1..)`. This exact two-step field chain directly explains Miri's diagnostic path `at .0.0` (Section 4).

#### 1.3 `NonNull<T>` and `BoxRaw<T>` (`library/core/src/ptr/non_null.rs`, `library/alloc/src/boxed.rs`)

At all three audited revisions, `NonNull<T>` is a single-field `#[repr(transparent)]` wrapper around `pattern_type!(*const T is !null)` (`library/core/src/ptr/non_null.rs:75-80` at `342d74463af7` and `3ef0c22cdb86`; lines `71-76` at `14210df0e27c`):

```rust
#[repr(transparent)]
#[rustc_nonnull_optimization_guaranteed]
#[lang = "non_null"]
pub struct NonNull<#[rustc_assert_variance(covariant)] T: PointeeSized> {
    pointer: crate::pat::pattern_type!(*const T is !null),
}
```

Between `1.98.0-nightly` (`14210df0e27c`) and `1.102.0-nightly` (`3ef0c22cdb86`), `alloc::boxed::Box<T, A>` replaced its internal `core::ptr::Unique<T>` field with a private `#[repr(transparent)]` wrapper `BoxRaw<T>` (`library/alloc/src/boxed.rs:233-246, 308-311`):

```rust
#[repr(transparent)]
struct BoxRaw<T: ?Sized> {
    pointer: NonNull<T>,
    _marker: PhantomData<T>,
}

#[lang = "owned_box"]
pub struct Box<
    #[rustc_assert_variance(covariant)] T: ?Sized,
    A: Allocator = Global,
>(BoxRaw<T>, A);
```

Thus, in late-2026 `rustc`, the non-null niche of `Box<T>` (for both thin `T: Sized` and wide `T: ?Sized` pointers) originates uniformly from `Box<T>` -> `BoxRaw<T>` -> `NonNull<T>` -> `pattern_type!(*const T is !null)`.

---

### 2. Layout Computation, `WrappingRange` Narrowing, Nested `Option` Niche Stacking, and the Signed vs. Unsigned `Or`-Pattern Split

Basis: source (`rust-lang/rust` @ `342d74463af7`, `3ef0c22cdb86`, `14210df0e27c`) + execution (`support/probe_pattern_types.py`) + derived (Lean proofs in `support/PatternTypesNicheAndRangeSoundness.lean`).

#### 2.1 `TyKind::Pat` Layout Computation (`compiler/rustc_ty_utils/src/layout.rs:241-408`)

In `layout_of_uncached`, `ty::Pat(ty, pat)` clones the base type's `LayoutData`, narrows the `valid_range` of its `Scalar` (or first component of `ScalarPair`), updates `layout.largest_niche`, and rewrites `layout.fields` to a single zero-offset field:

```rust
layout.fields = FieldsShape::Arbitrary {
    offsets: [Size::ZERO].into_iter().collect(),
    in_memory_order: [FieldIdx::new(0)].into_iter().collect(),
};
```

The three `ty::PatternKind` arms behave as follows:

1. **`ty::PatternKind::Range { start, end }` (`layout.rs:245-293`):** Requires `BackendRepr::Scalar(scalar)`. Extracts `start` and `end` bit patterns (`u128`), stores them in `scalar.valid_range_mut()`, and rejects wrapping single ranges (`end < start`, using `layout.size.sign_extend(...)` when `scalar.is_signed()` and unsigned `<` otherwise) with `"pattern type ranges cannot wrap: {start}..={end}"`. Publishes `Niche { offset: Size::ZERO, value: scalar.primitive(), valid_range }` as `layout.largest_niche`.
2. **`ty::PatternKind::NotNull` (`layout.rs:294-312`):** Accepts **both** `BackendRepr::Scalar(scalar)` (thin pointers `*const T`, `*mut T`) **and** `BackendRepr::ScalarPair { a: scalar, b: _, b_offset: _ }` (wide pointers `*const [T]`, `*const dyn Trait`, `*const str`). Sets `scalar.valid_range_mut().start = 1` (leaving `end = pointer_max`, i.e., `0xffff_ffff_ffff_ffff` on 64-bit targets) and publishes `layout.largest_niche = Some(Niche { offset: Size::ZERO, .. })`.
3. **`ty::PatternKind::Or(variants)` (`layout.rs:314-397`):** Accepts **only** `PatternKind::Range` sub-patterns on `BackendRepr::Scalar(scalar)` and enforces four strict layout-time gates:
   - **Signed-only gate (`layout.rs:336-342`):**
     ```rust
     if !scalar.is_signed() {
         let guar = tcx.dcx().err(format!(
             "only signed integer base types are allowed for or-pattern pattern types at present"
         ));
         return Err(error(cx, LayoutError::ReferencesError(guar)));
     }
     ```
   - **Exactly two arms (`layout.rs:344-350`):** `variants.len() != 2` errors with `"the only or-pattern types allowed are two range patterns that are directly connected at their overflow site"`.
   - **Non-overlapping signed order (`layout.rs:352-368`):** Identifies `first` as the arm starting at `signed_int_min` (e.g., `-128i8 = 0x80u8`) and checks `sign_extend(first.1) < sign_extend(second.0)`.
   - **Must terminate at `MAX` (`layout.rs:369-376`):** Checks `signed_int_max as u128 == second.1` (e.g., `127i8 = 0x7fu8`).
   - **Wrapping-range synthesis (`layout.rs:378-388`):** Sets `valid_range.start = second.0` and `valid_range.end = first.1`.

**Why `i8 is ..=-1 | 1..` works while `u8 is 250..=255 | 0..=5` fails:**
- For `i8 is ..=-1 | 1..`: the two ranges in unsigned 8-bit representation are `first = (0x80, 0xff)` (`-128..=-1`) and `second = (0x01, 0x7f)` (`1..=127`). Because `0x7f` (`+127`) wraps directly into `0x80` (`-128`) in two's complement, `second.0 ..= first.1` is `0x01 ..= 0xff` (`1..=255`), a single contiguous non-wrapping `WrappingRange` excluding only `0`! Similarly, `i32 is ..-1 | 0..` (`I32NotAllOnes`) has `first = (0x8000_0000, 0xffff_fffe)` and `second = (0x0000_0000, 0x7fff_ffff)`, yielding `0x0000_0000 ..= 0xffff_fffe` (excluding only `-1 = 0xffff_ffff`).
- For `u8 is 250..=255 | 0..=5`: even though `250..=5` **is** representable as a single wrapping `WrappingRange { start: 250, end: 5 }` in `rustc_abi`, `layout.rs:336` explicitly hard-rejects `!scalar.is_signed()` because `Or`-pattern support was implemented narrowly to express `NonZeroI*Inner` (`..0 | 1..`) and `I*NotAllOnes` (`..-1 | 0..`) without generalizing multi-disjunct validity checking.
- **Layout-time vs. metadata-time subtlety (observed empirically):** Because the signed-only rejection resides in `rustc_ty_utils::layout::layout_of_uncached` rather than HIR type lowering, `rustc --emit=metadata` on a library defining `pub type WrapU8 = pattern_type!(u8 is 250..=255 | 0..=5); pub fn size() -> usize { size_of::<Option<WrapU8>>() }` **succeeds** (`rc = 0`) because `size_of` inside a non-`const` function body is not evaluated during metadata-only compilation. Forcing layout via `pub const OPT_SIZE: usize = size_of::<Option<WrapU8>>();` (or codegen `--emit=link`/`obj`) immediately triggers the exact error `only signed integer base types are allowed for or-pattern pattern types at present`.

#### 2.2 Iterative `Option` Niche Stacking (`compiler/rustc_abi/src/lib.rs:2128-2205`, `enum_layout.rs:614-635`)

`rustc_abi::WrappingRange` (`compiler/rustc_abi/src/wrapping_range.rs:19-63`) defines inclusive wrap-around membership:

```rust
pub fn contains(&self, v: u128) -> bool {
    if self.start <= self.end {
        self.start <= v && v <= self.end
    } else {
        self.start <= v || v <= self.end
    }
}
```

For a `w`-bit scalar (`max_value = 2^w - 1`), `Niche::available` (`compiler/rustc_abi/src/lib.rs:2128-2137`) computes the number of unused bit patterns outside `valid_range`:

$$\text{available}(r) = (r.\text{start} - r.\text{end} - 1) \bmod 2^w = 2^w - |\text{valid}(r)|.$$

When `enum_layout.rs:614-615` lays out `Option<T>` (`count = 1` tagless/unit variant `None` alongside data-carrying variant `Some(T)`), it invokes `niche.reserve(dl, 1)` (`compiler/rustc_abi/src/lib.rs:2139-2205`). For `count == 1` (excluding `bool`'s `0..=1`, which keeps `None = 2` due to a miscompilation noted in `rust-lang/rust#155473`), `Niche::reserve` compares the signed two's-complement absolute distance to zero of the two adjacent niche boundaries:

```rust
let next_up   = size.sign_extend(v.end.wrapping_add(1)).unsigned_abs();
let next_down = size.sign_extend(v.start.wrapping_sub(1)).unsigned_abs();
if next_down <= next_up { move_start(v) } else { move_end(v) }
```

Tracing this rule step-by-step on `Pat1To10` (`w = 8`, `valid_range = 1..=10`, `available = 246`) and comparing against live `rustc` execution (`support/probe_results_rustc_1_98_nightly.json` and `support/probe_results_rustc_1_102_nightly_llvm23.json`):

| Type | Valid Range (`WrappingRange`) | `next_down` (`\|sext(start-1)\|`) | `next_up` (`\|sext(end+1)\|`) | Chosen `None` Byte | Remaining Niches | Observed `size_of` (`1.98` & `1.102`) | Observed `None` Byte (`1.98` live) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Pat1To10` | `1..=10` | — | — | — | `246` | `1 B` | — |
| `Option<Pat1To10>` | `0..=10` | `\|0\| = 0` | `\|11\| = 11` | `0` (`move_start`) | `245` | `1 B` | `0` |
| `Option<Option<Pat1To10>>` | `255..=10` (wrapping) | `\|-1\| = 1` | `\|11\| = 11` | `255` (`move_start`) | `244` | `1 B` | `255` (`Some(None) = 0`) |
| `Option<Option<Option<Pat1To10>>>` | `254..=10` (wrapping) | `\|-2\| = 2` | `\|11\| = 11` | `254` (`move_start`) | `243` | `1 B` | `254` |
| `Pat254` (`u8 is 1..=254`) | `1..=254` | — | — | — | `2` | `1 B` | — |
| `Option<Pat254>` | `0..=254` | `\|0\| = 0` | `\|-1\| = 1` | `0` (`move_start`) | `1` | `1 B` | `0` |
| `Option<Option<Pat254>>` | `255..=254` (full!) | `\|-1\| = 1` | `\|-1\| = 1` | `255` (`move_start`) | `0` | `1 B` | `255` |
| `Option<Option<Option<Pat254>>>` | Exhausted (`available = 0`) | — | — | External tag | — | **`2 B`** | N/A (external tag) |
| `Option<NonZero<u8>>` | `0..=255` (full) | `\|0\| = 0` | `\|0\| = 0` | `0` | `0` | `1 B` | `0` |
| `Option<Option<NonZero<u8>>>` | Exhausted | — | — | External tag | — | **`2 B`** | N/A |
| `Option<PatSignedNonZero>` (`i8 is ..=-1 \| 1..`) | `0..=255` (full) | `\|0\| = 0` | `\|0\| = 0` | `0` | `0` | `1 B` | `0` |
| `Option<Option<PatSignedNonZero>>` | Exhausted | — | — | External tag | — | **`2 B`** | N/A |
| `Option<PatNonNull>`, `Option<NonNull<u8>>`, `Option<Box<u8>>` | `0..=u64::MAX` (full) | `0` | `0` | `0` (`null`) | `0` | `8 B` | `0` |
| `Option<Option<NonNull<u8>>>`, `Option<Option<Box<u8>>>` | Exhausted | — | — | External tag | — | **`16 B`** | N/A |
| `Option<PatPosI32>` (`i32 is 1..`) | `0..=2147483647` | `0` | `2147483648` | `0` | `2,147,483,647` | `4 B` | `0` |

Every observed byte and size matches our Lean formalization's `nestOptionIter` evaluation (`pat1To10_three_nested_options_exact_tags` yields `[254, 255, 0]`, `pat254_niche_stacking_and_exhaustion` yields `[255, 0]` then `none`).

---

### 3. LLVM 23 (and LLVM 22) `range(...)` / `nonnull` Lowering and Dead-Branch Elimination

Basis: source (`rust-lang/rust` @ `342d74463af7`, `3ef0c22cdb86`, `14210df0e27c`) + execution (`rustc 1.102.0-nightly`/LLVM `23.1.5` and `rustc 1.98.0-nightly`/LLVM `22.1.6`) + derived (Lean theorem `llvm_range_elim_sound_under_pat_validity`).

#### 3.1 Three Codegen Channels Transmitting `WrappingRange` to LLVM

`rustc` conveys pattern-type validity ranges to LLVM through three distinct mechanisms, **all** of which are disabled at `-C opt-level=0` (`OptLevel::No`):

1. **Function argument and return attributes:**
   - For integer scalars (`Primitive::Int(..)`), `apply_range_attr` (`compiler/rustc_codegen_llvm/src/abi.rs:682-698` at `342d74463af7`; lines `504-520` at `3ef0c22cdb86`; lines `465-481` at `14210df0e27c`) attaches LLVM's `range(iW lo, hi)` attribute via `LLVMRustCreateRangeAttribute` (`compiler/rustc_llvm/llvm-wrapper/RustWrapper.cpp:501-509`, calling `LLVMCreateConstantRangeAttribute`) whenever `optimize != OptLevel::No && !scalar.is_bool() && !scalar.is_always_valid(cx)`. Rust's inclusive `[start, end]` translates to LLVM's half-open modular interval `[start, (end + 1) mod 2^w)`:
     - `Pat1To10` (`1..=10` on `u8`) -> `range(i8 1, 11)`.
     - `PatPosI32` (`1..=2147483647` on `i32`) -> `range(i32 1, -2147483648)` because `(0x7fff_ffff_u32).wrapping_add(1) = 0x8000_0000 = -2147483648i32`.
   - For pointer scalars (`Primitive::Pointer(_)`), `arg_attrs_for_rust_scalar` (`compiler/rustc_ty_utils/src/abi.rs:318-339`) unconditionally sets `ArgAttribute::NonNull` when `!valid_range.contains(0)`, which `compiler/rustc_codegen_llvm/src/abi.rs:50` maps to LLVM `nonnull` (in `OPTIMIZATION_ATTRIBUTES`, also gated on `optimize != OptLevel::No` when applied to function attributes).
2. **Memory load metadata:** `Builder::range_metadata` and `Builder::nonnull_metadata` (`compiler/rustc_codegen_llvm/src/builder.rs:770-788, 862-877`) attach `!range !{iW start, iW end.wrapping_add(1)}` (`MD_range`) and `!nonnull !{}` (`MD_nonnull`) to scalar loads when `optimize != OptLevel::No`.
3. **Inline transmute assumptions:** `assume_scalar_range` (`compiler/rustc_codegen_ssa/src/mir/rvalue.rs:1141-1194`) runs during `codegen_transmute_scalar` when `optimize != OptLevel::No`. Critically, lines `1174-1179` check `if valid_range.contains_range(known_range, scalar.size(bx.cx())) { return; }`—meaning **widening** (`Pat(B, r) -> B`) emits zero `llvm.assume` instructions, whereas **narrowing** (`B -> Pat(B, r)`) emits `assume_integer_range` or `assume_nonnull` (for `AddressSpace::ZERO`), exposing the validity invariant to LLVM even after MIR inlining eliminates the function boundary.

#### 3.2 Empirical LLVM 23.1.5 and LLVM 22.1.6 Dead-Branch Folding

Compiling the four `#[unsafe(no_mangle)] #[inline(never)] pub extern "C"` probe functions under `-C opt-level=2 -Z ub-checks=no` vs. `-C opt-level=0 -Z ub-checks=yes` yields identical dead-branch folding on both LLVM `23.1.5` (`rustc 1.102.0-nightly`) and LLVM `22.1.6` (`rustc 1.98.0-nightly`):

- **`take_pat_u8(x: Pat1To10) -> u8`** (source checks `if v == 0 || v > 10 { panic!(...) }`):
  - LLVM `23.1.5` (`-O2 -Z ub-checks=no`):
    ```llvm
    define dso_local noundef range(i8 1, 11) i8 @take_pat_u8(i8 noundef returned zeroext range(i8 1, 11) %x) ... {
    start:
      ret i8 %x
    }
    ```
  - LLVM `23.1.5` (`-O0 -Z ub-checks=yes`): retains `icmp eq i8 %x, 0`, `icmp ugt i8 %x, 10`, and `invoke void @...core::panicking::panic_fmt` with NO `range` attribute.
- **`ret_pat_u8(x: u8) -> Pat1To10`** (source asserts `(1..=10).contains(&x)` before transmuting):
  - LLVM `23.1.5` (`-O2 -Z ub-checks=no`): retains `%0 = add i8 %x, -1; %or.cond = icmp ult i8 %0, 10; br i1 %or.cond, label %bb2, label %bb3` (cannot erase the entry check because parameter `%x` is unrestricted `u8`), while emitting `define dso_local noundef range(i8 1, 11) i8 @ret_pat_u8(...)` on the return value.
- **`take_pat_pos_i32(x: PatPosI32) -> i32`** (source checks `if v <= 0 { panic!("impossible") }`):
  - LLVM `23.1.5` (`-O2 -Z ub-checks=no`):
    ```llvm
    define dso_local noundef range(i32 1, -2147483648) i32 @take_pat_pos_i32(i32 noundef returned range(i32 1, -2147483648) %x) ... {
    start:
      ret i32 %x
    }
    ```
- **`take_pat_nonnull(p: PatNonNull) -> usize`** (source checks `if raw.is_null() { panic!("impossible null") }`):
  - LLVM `23.1.5` (`-O2 -Z ub-checks=no`):
    ```llvm
    define dso_local noundef i64 @take_pat_nonnull(ptr noundef nonnull %p) ... {
    start:
      %_6 = ptrtoint ptr %p to i64
      ret i64 %_6
    }
    ```
- **MIR preservation (`--emit=mir`):** Both `-O2` and `-O0` MIR dumps retain pattern-type syntax (`has_is_1_10: true`, `has_is_not_null: true` on both `1.98.0-nightly` and `1.102.0-nightly`).

#### 3.3 Observed Miscompilation Under Violated Validity Invariants

Running `bad_pat_u8_11_call_opt` (passing `transmute::<u8, Pat1To10>(black_box(11u8))` to `take_pat_u8`) and `bad_pat_nonnull_call_opt` (passing `transmute::<*const u8, PatNonNull>(black_box(ptr::null()))` to `take_pat_nonnull`) on `rustc 1.98.0-nightly` demonstrates the exact operational divergence:
- Under `-O0 -Z ub-checks=yes`: both abort (`rc = -6`, non-unwinding panic across `extern "C"`) at the explicit source guards (`impossible out-of-range Pat1To10` and `impossible null`).
- Under `-O2 -Z ub-checks=no`: LLVM has deleted both panic branches via `range(i8 1, 11)` and `nonnull`, so both return normally (`rc = 0`) and print `MISCOMPILED_TAKE_PAT_U8=11` and `MISCOMPILED_TAKE_PAT_NN=0x0`!
- Under Miri: both halt with UB (`rc = 1`) at the `transmute` before `take_pat_u8` / `take_pat_nonnull` is even entered.

---

### 4. The Validity Enforcement Cliff: Miri vs. `-Z ub-checks=yes` (`CheckEnums`) vs. Library Preconditions

Basis: source (`rust-lang/rust` @ `342d74463af7`, `3ef0c22cdb86`, `14210df0e27c`) + execution (`rustc 1.102.0-nightly` and `rustc 1.98.0-nightly` + Miri) + derived (Lean counterexample `ce3_ub_checks_bypass_misses_raw_transmute_to_nonzero`).

#### 4.1 Complete Differential Matrix

| Probe Case | Rust Operation | `-O2 -Z ub-checks=no` (`1.102` / `1.98`) | `-O0 -Z ub-checks=yes` (`1.102` / `1.98`) | Miri (`1.102` / `1.98`) | Causal Mechanism |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `bad_pat_u8_11` | `transmute::<u8, Pat1To10>(11)` -> `transmute` back | `rc = 0` (`BAD_PAT_U8=11`) | **`rc = 0`** (`BAD_PAT_U8=11`) | **`rc = 1`**: `constructing invalid value of type ...: encountered 11, but expected something in the range 1..=10` | `CheckEnums` ignores `ty::Pat`; Miri `ValidityVisitor` checks `valid_range.contains(11)`. |
| `bad_pat_nonnull` | `transmute::<*const u8, PatNonNull>(null())` -> back | `rc = 0` (`BAD_PAT_NN=0x0`) | **`rc = 0`** (`BAD_PAT_NN=0x0`) | **`rc = 1`**: `constructing invalid value of type ...: encountered 0, but expected something greater or equal to 1` | Neither `CheckEnums` nor `CheckNull` inspects `CastKind::Transmute` into `ty::Pat(_, NotNull)`. |
| `bad_nonzero_transmute` | `transmute::<u8, NonZero<u8>>(0)` | `rc = 0` (`BAD_NZ_TX=0`) | **`rc = 0`** (`BAD_NZ_TX=0`) | **`rc = 1`**: `constructing invalid value of type std::num::NonZero<u8>: at .0.0, encountered 0, but expected something greater or equal to 1` | `NonZero<u8>` is a `#[repr(transparent)] struct`, not an enum (`!adt_def.is_enum()`). Miri recurses `.0` (`NonZeroU8Inner`) -> `.0.0` (`pattern_type!(u8 is 1..)`). |
| `bad_nonzero_new_unchecked` | `NonZero::<u8>::new_unchecked(0)` | `rc = 0` (`BAD_NZ_NU=0`) | **`rc = -6`** (`SIGABRT`: `unsafe precondition(s) violated: NonZero::new_unchecked requires the argument to be non-zero`) | **`rc = 1`**: `Undefined Behavior: entering unreachable code` | Library `assert_unsafe_precondition!(check_language_ub, ...)` fires at `-O0 -Z ub-checks=yes`, is disabled under `cfg!(miri)` so Miri hits `intrinsics::unreachable()`. |
| `bad_opt_pat_enum_transmute` (`1.98` live) | `transmute::<u8, Option<Pat1To10>>(99)` | `rc = 0` (`BAD_OPT_PAT_IS_SOME=true`) | **`rc = -6`** (`SIGABRT`: `trying to construct an enum from an invalid value 0x63`) | **`rc = 1`**: `constructing invalid value of type std::option::Option<...>: at .<enum-tag>, encountered 0x63, but expected a valid enum tag` | `Option<Pat1To10>` **is** an enum (`adt_def.is_enum() == true`); `CheckEnums::insert_niche_check` validates `0x63` against `WrappingRange { start: 0, end: 10 }`! |
| `bad_pat_u8_11_call_opt` (`1.98` live) | `take_pat_u8(transmute(11u8))` | `rc = 0` (`MISCOMPILED_TAKE_PAT_U8=11`) | `rc = -6` (`impossible out-of-range Pat1To10`) | `rc = 1` (UB at `transmute`) | `-O0` executes explicit user `if v == 0 \|\| v > 10` panic; `-O2` erases it via `range(i8 1, 11)`. |
| `bad_pat_nonnull_call_opt` (`1.98` live) | `take_pat_nonnull(transmute(null()))` | `rc = 0` (`MISCOMPILED_TAKE_PAT_NN=0x0`) | `rc = -6` (`impossible null`) | `rc = 1` (UB at `transmute`) | `-O0` executes explicit user `raw.is_null()` panic; `-O2` erases it via `nonnull`. |

#### 4.2 Root-Cause Code Walkthrough

1. **Compiler MIR UB-check pipeline (`compiler/rustc_mir_transform/src/lib.rs:706-714`):** Only three MIR instrumentation passes execute under `-Z ub-checks=yes`: `CheckAlignment`, `CheckNull`, and `CheckEnums`.
2. **Why `CheckEnums` misses `TyKind::Pat` and `NonZero<u8>` (`compiler/rustc_mir_transform/src/check_enums.rs:167-174`):**
   ```rust
   fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
       if let Rvalue::Cast(CastKind::Transmute, op, ty) = rvalue {
           let ty::Adt(adt_def, _) = ty.kind() else {
               return;
           };
           if !adt_def.is_enum() {
               return;
           }
   ```
   Any destination whose outer `TyKind` is `ty::Pat(..)` fails the `let ty::Adt(..)` guard; any `#[repr(transparent)]` struct (`NonZero<u8>`, `NonNull<T>`, `Nanoseconds`, `CodePointInner`, `BoxRaw<T>`) fails `adt_def.is_enum()`. By contrast, when `ty` is `Option<Pat1To10>` (`TagEncoding::Niche`), `CheckEnums` reaches `insert_niche_check` (`check_enums.rs:466-541`), zero-extends the tag scalar to `u128`, and asserts `u128::wrapping_sub(discr, valid_range.start) <= u128::wrapping_sub(valid_range.end, valid_range.start)` (which remains exact for all sub-128-bit wrapping ranges because `0 <= discr, start, end < 2^w` forces `discr >= start` into `[0, 2^w - 1 - start]` and `discr <= end < start` into `[2^128 - start, 2^128 - (start - end)]`, while invalid values `end < discr < start` fall strictly above `2^128 - (start - end)`).
3. **Why `CheckNull` misses `transmute` to `PatNonNull` / `NonNull` (`compiler/rustc_mir_transform/src/check_null.rs:19-26`):** `CheckNull` delegates to `check_pointers`, which instruments pointer dereferences and reference-creating borrows (`AssertKind::NullReferenceConstructed` / `AssertKind::NullPointerDereference`), never raw `CastKind::Transmute` rvalues.
4. **Why `NonZero::new_unchecked(0)` aborts under `-Z ub-checks=yes` but reports `entering unreachable code` in Miri (`library/core/src/num/nonzero.rs:513-525`, `library/core/src/ub_checks.rs:95-105`):**
   `NonZero::new_unchecked(n)` matches `Self::new(n)` (which transmutes `n` to `Option<Self>`) and on `None` executes:
   ```rust
   ub_checks::assert_unsafe_precondition!(
       check_language_ub,
       "NonZero::new_unchecked requires the argument to be non-zero",
       () => false,
   );
   intrinsics::unreachable()
   ```
   And `ub_checks::check_language_ub()` (`library/core/src/ub_checks.rs:96-105`) is defined via `const_eval_select!` as:
   ```rust
   if const { false } else { !cfg!(miri) && intrinsics::ub_checks() }
   ```
   In compiled runtime binaries with `-Z ub-checks=yes`, `check_language_ub()` returns `true` and triggers a non-unwinding abort (`SIGABRT`, `rc = -6`). Under Miri, `!cfg!(miri)` evaluates to `false` by design ("to not do that when running in the interpreter, as that one has its own language UB checks"), so execution falls straight into `intrinsics::unreachable()`, producing `Undefined Behavior: entering unreachable code`.
5. **How Miri validates `TyKind::Pat` (`compiler/rustc_const_eval/src/interpret/validity.rs:1015-1070, 1497-1535`):** `ValidityVisitor::visit_aggregate` matches `ty::Pat(base, pat)`, first validates the base type (`val.transmute(layout_of(*base))`), and then validates the scalar (or both components of `ScalarPair`) via `visit_scalar`, which tests `valid_range.contains(bits)`. Notably, lines `1508-1514` contain an explicit `FIXME(pattern_types)` warning that `PatternKind::Or` currently relies solely on `layout`'s single `valid_range` and does not independently check disjunct membership—confirming why `layout.rs` currently forbids non-contiguous `Or` patterns that a single `WrappingRange` would over-approximate.

---

### 5. `rustc_transmute` Rejection (`rust-lang/rust#148449`) and Anneal's Trusted-Boundary Gap

Basis: source (`rust-lang/rust` @ `342d74463af7`, `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`) + execution (`rustc 1.102.0-nightly` and `rustc 1.98.0-nightly`) + documentation (`rust-lang/rust#148449`).

#### 5.1 Why `rustc_transmute` Rejects Both `TyKind::Pat` and `NonZero<u8>`

In `compiler/rustc_transmute/src/layout/tree.rs:304-370` (identical at `3ef0c22cdb86` and `342d74463af7`), `Tree::from_ty` dispatches on `ty.kind()` across `Bool`, `Float`, `Int`, `Uint`, `Tuple`, `Array`, `Adt` (non-`Box`), `Ref`, and `Char`, falling through to:

```rust
_ => Err(Err::NotYetSupported), // tree.rs:368
```

There is no arm for `ty::Pat(..)`. Consequently:
- Directly analyzing `Pat1To10 -> u8` or `u8 -> Pat1To10` via `core::mem::TransmuteFrom` immediately hits line `368`, emitting `error[E0277]: ... analyzing the transmutability of pattern_type!(u8 is 1..=10) is not yet supported`.
- Analyzing `NonZero<u8> -> u8` descends through `AdtKind::Struct` (`NonZero<u8>`) -> `NonZeroU8Inner` -> `pattern_type!(u8 is 1..)`, hitting the exact same `Err::NotYetSupported` (`error[E0277]: NonZero<u8> cannot be safely transmuted into u8: analyzing the transmutability of NonZero<u8> is not yet supported`, verified empirically in `support/probe_results_rustc_1_98_nightly.json`).

Upstream PR `rust-lang/rust#148449` (*"transmutability: model NonZero scalar ranges"*, open as of `2026-11-22`) proposes extending `rustc_transmute` to model scalar validity ranges for transparent `std` `NonZero` wrappers (integers and `NonZero<char>`) and scalar-backed `FieldsShape::Primitive` ADTs while threading caller-sensitive visibility/unsafe-field invariants through both old and next trait solvers. General `TyKind::Pat` layout-tree conversion remains unsupported on upstream `master`.

#### 5.2 Anneal's Trusted-Boundary Status (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)

Direct inspection of `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes three precise trusted-boundary facts:

1. **`TyKind::Pat` and niche wrappers fail closed in `Trusted.MirAst.MirTy` (`trusted/lean/Trusted/MirAst.lean:308-321`):**
   ```lean
   inductive MirTy where
     | bool
     | int (width : IntWidth) (signed : Bool)
     | unit
     | never
     | enum (ty : EnumTy)
     | tuple (fields : List MirTy)
     | ref (mutability : Mutability) (pointee : MirTy)
     | rawPtr (mutability : Mutability) (pointee : MirTy)
     | unsupported
   ```
   Lines `308-311` explicitly document that `.unsupported` absorbs `Pat` as well as non-fieldless-enum `Adt`s (`NonZero`, `NonNull`, `Option`, `Box`), causing `Trusted.MirSemantics.isSupportedScalarOrUnitTy` (`trusted/lean/Trusted/MirSemantics.lean:721-724`) to return `false` and `BodyStaticAdmitted` / execution to fail closed with `FaultKind.unsupported`.
2. **`CastKind::Transmute` fails closed in `Trusted.MirAst.Rvalue` (`trusted/lean/Trusted/MirAst.lean:612-628`):**
   All `Rvalue::Cast(CastKind, _, _)` forms—including `CastKind::Transmute`, which under `compiler-team#807` is the *only* MIR operation used to construct or unwrap `TyKind::Pat` values—currently lower to `Rvalue.unsupported`.
3. **Existing `WrappingRange` building block in `vendor/lean-miri`:** Anneal's vendored `vendor/lean-miri/Miri/ABI/WrappingRange.lean:14-60` already formalizes `WrappingRange.contains`, `isFullFor`, `containsRange`, and `smallestRangeContaining`, and `vendor/lean-miri/Miri/Memory/Validity.lean:19` carries `validRange : WrappingRange`.

**Derived architectural consequence for Anneal:** Lifting `TyKind::Pat`, `NonZero<T>`, `NonNull<T>`, or `Option<NonZero<T>>` across Anneal's trusted boundary requires two coupled extensions:
- Adding a `WrappingRange`-annotated scalar/pointer type representation to `Trusted.MirAst.MirTy` and enforcing `r.contains v` inside `Trusted.MirSemantics.checkVal`, entry argument admission (`ValidEntryArgs`), and `writePlace`.
- Modeling `CastKind::Transmute` in `Trusted.MirAst.Rvalue` with Miri-faithful destination validity checking (faulting with `FaultKind.undefined` whenever `r.contains bits = false`), because relying on `rustc`'s `-Z ub-checks=yes` (`CheckEnums`) leaves every invalid raw transmute into `TyKind::Pat` and transparent wrappers unchecked while LLVM optimizes under the assumption that `r.contains bits = true`.

---

### 6. Kernel-Checked Lean 4 Formalization (`support/PatternTypesNicheAndRangeSoundness.lean`)

Basis: derived (kernel-checked in `leanprover/lean4` `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`).

#### 6.1 Core Formal Definitions

`support/PatternTypesNicheAndRangeSoundness.lean` (`1,459` lines, zero external imports, zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`, zero `partial def`, zero `._unsafe_rec`) defines the following core structures and predicates inside `namespace PatternTypesSoundness.WrappingRange`:

```lean
def modulus (w : Nat) : Nat := 2 ^ w

structure WrappingRange where
  start : Nat
  «end» : Nat

def WrappingRange.wf (w : Nat) (r : WrappingRange) : Prop :=
  1 ≤ w ∧ r.start < modulus w ∧ r.end < modulus w

def WrappingRange.contains (r : WrappingRange) (v : Nat) : Bool :=
  if r.start ≤ r.end then
    decide (r.start ≤ v) && decide (v ≤ r.end)
  else
    decide (r.start ≤ v) || decide (v ≤ r.end)

def WrappingRange.containsBV {w : Nat} (r : WrappingRange) (v : BitVec w) : Bool :=
  r.contains v.toNat

def WrappingRange.validCount (w : Nat) (r : WrappingRange) : Nat :=
  if r.start ≤ r.end then r.end - r.start + 1 else (modulus w - r.start) + (r.end + 1)

def WrappingRange.availableNiches (w : Nat) (r : WrappingRange) : Nat :=
  if r.start ≤ r.end then modulus w - (r.end - r.start + 1) else r.start - r.end - 1

def llvmHalfOpenContains (lo hi v : Nat) : Bool :=
  if lo < hi then decide (lo ≤ v) && decide (v < hi) else decide (lo ≤ v) || decide (v < hi)

def nestOption (w : Nat) (r : WrappingRange) : Option (WrappingRange × Nat) :=
  reserveOneDir w r (chooseMoveStart w r)
```

All recursive helpers (`nestOptionIter`, `listGetNat`, `listFindIdxNat`, `miriValid`) are defined via kernel recursors (`Nat.rec`, `List.rec`, `MirDstTy.rec`) with `noncomputable def` and propositional `=` rather than `BEq.beq` (`==`), which simultaneously eliminates all `._unsafe_rec` compiler helpers and avoids `BEq.rfl`'s hidden `Classical.choice` dependency in Lean `v4.34.1`.

#### 6.2 Verified Theorem Inventory, Hypotheses, and Axiom Footprint

Every theorem below was verified with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit 0`, `206` declarations, `80` theorems, `0` bad declarations, `0` forbidden axioms):

| Theorem Name (`PatternTypesSoundness.WrappingRange.*`) | Plain-Language Claim & Explicit Hypotheses | Axioms (`#print axioms`) |
| :--- | :--- | :--- |
| `validCount_add_availableNiches` (`L142`) | For any `r.wf w`, `r.validCount w + r.availableNiches w = 2^w`. | `[]` |
| `llvmHalfOpenContains_eq_contains` (`L274`) | For any `r.wf w` with `0 < r.availableNiches w` and any `v : BitVec w`, LLVM's half-open modular interval `llvmHalfOpenContains r.start ((r.end + 1) % 2^w) v.toNat` equals `r.containsBV v`. | `[propext]` |
| `nestedOption_niche_disjoint_and_injective` (`L873`) | For any `w ≥ 1`, `r.wf w`, and `k ≤ r.availableNiches w`, iterating `nestOption` `k` times succeeds with `(rK, tags)` where `tags.length = k`, `rK.wf w`, `rK.availableNiches w = r.availableNiches w - k`, `rK.validCount w = r.validCount w + k`, `tags` are pairwise distinct, `< 2^w`, and disjoint from `r`, `rK` covers exactly `valid(r) ∪ tags`, and `encodeNestedOption`/`decodeNestedOption` form a left-invertible injective encoding of `NestedOptionVal w r k` into a single `BitVec w` (`1` byte when `w = 8`). | `[propext, Quot.sound]` |
| `llvm_range_elim_sound_under_pat_validity` (`L1039`) | For any `r.wf w`, `0 < r.availableNiches w`, pure body `body : BitVec w → BitVec w`, and valid input `x : BitVec w` (`r.containsBV x = true`), LLVM's half-open range holds and erasing the out-of-range trap (`evalRangeGuarded` / `evalLlvmHalfOpenGuarded` -> `evalLlvmRangeFolded`) preserves exact denotational equivalence. | `[propext]` |
| `pat_to_base_always_valid_and_base_to_pat_requires_range_check` (`L1063`) | For any `r.wf w`: (1) every valid `Pat` bit-vector is unconditionally valid in `WrappingRange.full w` (widening needs zero runtime checks); (2) narrowing `B → Pat(B, r)` is valid iff `r.contains x.toNat = true`; (3) if `0 < r.availableNiches w`, there constructively exists a valid `B` bit-vector `bad` with `r.containsBV bad = false`. | `[propext, Quot.sound]` |
| `no_injective_encoding_when_niches_exhausted` (`L1249`) | Constructive pigeonhole: for any `r.wf w` and `k > r.availableNiches w`, NO injective function `NestedOptionVal w r k → BitVec w` exists (forcing external tag expansion). | `[propext]` |
| `pat1To10_three_nested_options_exact_tags` (`L1395`) | Concrete kernel reduction: `nestOptionIter 8 pat1To10Range 3 = some ({ start := 254, end := 10 }, [254, 255, 0])`, matching live `rustc` `NICHE_BYTES` bit-for-bit. | `[]` |
| `pat254_niche_stacking_and_exhaustion` (`L1399`) | Concrete kernel reduction: `nestOptionIter 8 pat254Range 2 = some ({ start := 255, end := 254 }, [255, 0])` and `nestOptionIter 8 pat254Range 3 = none`. | `[]` |
| `ce1_invalid_pat_transmute_miscompiles_under_llvm_range_attr` (`L1407`) | Constructive counterexample 1: `bad = 11#8` is valid for `u8`, invalid for `Pat1To10`, trapped by `evalRangeGuarded`, yet returned as `.ret 11#8` by `evalLlvmRangeFolded` (`evalRangeGuarded ≠ evalLlvmRangeFolded`). | `[]` |
| `ce2_niche_exhaustion_forces_tag_expansion` (`L1425`) | Constructive counterexample 2: proves exhaustion (`nestOptionIter = none`) and non-existence of any injective `BitVec 8` encoding for both `Option<Option<NonZero<u8>>>` (`k = 2`) and `Option<Option<Option<Pat254>>>` (`k = 3`). | `[propext]` |
| `ce3_ub_checks_bypass_misses_raw_transmute_to_nonzero` (`L1446`) | Constructive counterexample 3: proves `checkEnumsAccepts = true ∧ miriValid = false` for `Pat1To10` at `11`, `PatNonNull` at `0`, and `NonZero<u8>` (`transparentStruct (transparentStruct (patRange 8 {1, 255}))`) at `0`, contrasted with `Option<Pat1To10>` at `99` (`checkEnumsAccepts = false ∧ miriValid = false`). | `[]` |

## Boundaries

The following scope boundaries and negative-space classifications apply to all claims in this report:

- **Known not to apply:**
  - **Model-to-compiler mechanization gap:** The Lean theorems in `support/PatternTypesNicheAndRangeSoundness.lean` prove properties of the abstract `WrappingRange` / `nestOption` / `evalRangeGuarded` / `MirDstTy` formalization, NOT a mechanically verified refinement of `rustc`'s Rust source code or LLVM's C++ optimizer. Alignment with `rustc` and LLVM rests on audited primary source and empirical probes, not a machine-checked extraction.
  - **Non-scalar / multi-field aggregates and uninitialized/provenance-bearing bytes:** The formal model treats initialized, provenance-free `BitVec w` scalars. It does **not** apply to uninitialized memory (`MaybeUninit<T>`), pointer provenance invalidation (Stacked/Tree Borrows), `UnsafeCell`/`UnsafePinned` niche suppression (`NicheOptimizations::Disabled`), or multi-field struct niche-bias layout selection (`NicheBias::Start` vs. `NicheBias::End`).
  - **Multi-variant enums with `count > 1`:** `nestOption` models `Niche::reserve(_, 1)` (binary `Option`-like nesting). Multi-variant niche enums (`count > 1`) take the `else` branches of `compiler/rustc_abi/src/lib.rs:2185-2204`, which avoid crossing zero rather than using `sign_extend(...).unsigned_abs()`.
  - **`bool` niche selection (`w = 8`, `0..=1`):** Explicitly excluded from the closest-to-zero `move_start` branch in `rustc_abi::Niche::reserve` (`lib.rs:2177`), so `Option<bool>::None` uses `2` (`move_end`) rather than `255`.
  - **Non-`-O` codegen:** LLVM `range(lo, hi)`, `!range`, `nonnull` parameter/load attributes, and `assume_scalar_range` are explicitly suppressed at `-C opt-level=0`.
- **Unsupported (by upstream `rustc` and Anneal as of observed revisions):**
  - **Unsigned `Or`-pattern `pattern_type!`:** Explicitly rejected at layout computation (`compiler/rustc_ty_utils/src/layout.rs:336-342`) with `only signed integer base types are allowed for or-pattern pattern types at present`.
  - **General multi-arm or non-overflow-adjacent `Or`-pattern `pattern_type!`:** Explicitly rejected at `layout.rs:344-376` (requires exactly two signed arms meeting at `MIN`/`MAX`).
  - **Safe `TransmuteFrom` analysis of `TyKind::Pat` and `NonZero<T>`:** Unsupported in `compiler/rustc_transmute/src/layout/tree.rs:368` (`Err::NotYetSupported`, `E0277`).
  - **Anneal MIR verification of `TyKind::Pat`, `NonZero<T>`, `NonNull<T>`, and `CastKind::Transmute`:** Unsupported fail-closed in `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`MirTy.unsupported` and `Rvalue.unsupported`).
  - **Runtime `-Z ub-checks=yes` checking of raw `transmute` into `TyKind::Pat` or `#[repr(transparent)]` structs:** Unsupported by `CheckEnums` and `CheckNull`.
- **Not examined:**
  - Non-LLVM codegen backends (`rustc_codegen_cranelift`, `rustc_codegen_gcc`) and their consumption of `Scalar::valid_range`.
  - Wide-pointer `!null` `ScalarPair` metadata behavior (`pattern_type!(*const [u8] is !null)` and `pattern_type!(*const dyn Trait is !null)`) in LLVM IR and Miri execution (source support in `layout.rs:295-299` and `validity.rs:1529` was audited, but only thin `*const u8` was executed in the probe).
  - Non-`x86_64` architectures (`aarch64`, `i686`, `riscv64`, big-endian targets) and `32`-bit pointer sizes in live execution.
  - Non-zero LLVM address spaces (`AddressSpace != ZERO`), where `assume_scalar_range` (`rvalue.rs:1187-1192`) intentionally skips `assume_nonnull`.
  - Direct live execution of the unmerged PR branch for `rust-lang/rust#148449` or of `rust-lang/rust` `342d74463af7` (audited in source; execution evidence covers `3ef0c22cdb86` / LLVM `23.1.5` and `14210df0e27c` / LLVM `22.1.6`).
- **Unknown:**
  - Whether future stabilization of `pattern_types` (`rust-lang/rust#123646`) will extend `CheckEnums` (or introduce a dedicated `CheckValidity` MIR pass under `-Z ub-checks=yes`) to instrument raw `transmute` into `TyKind::Pat` and transparent scalar wrappers.
  - Whether future general `Or`-pattern support will extend Miri's `ValidityVisitor` (`validity.rs:1508-1514`) to validate arbitrary disjunct lists independently of `Scalar::valid_range`, or whether `rustc_abi::Scalar` will remain restricted to a single `WrappingRange`.
  - Whether LLVM 23.1.5's `range` attribute behavior on `i128` wrapping ranges has edge cases not exercised by our `i8`/`u8`/`i32`/`ptr` probes.

## Evidence

### Primary Git Source Citations

All repository commits below were verified against GitHub API metadata on `2026-11-22`:

1. **`rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (upstream `master`, 2026-11-22):**
   - `library/core/src/pat.rs:10-89` — Macro 2.0 `pub macro pattern_type`, `RangePattern` trait (`RangeMin`/`RangeMax`/`RangeSub`), and `CoerceUnsized`/`DispatchFromDyn`/`Unpin`/`Freeze` impls for `!null` raw pointers.
   - `library/core/src/num/niche_types.rs:13-174` — `define_valid_range_type!` using `pattern_type!` and `transmute`; `compiler-team#807` comment at lines `54-57`; `Nanoseconds` (`98`), `NonZero*Inner` (`118-141`), `UsizeNoHighBit*` (`130-131`), `*NotAllOnes` (`135-139`), `CodePointInner` (`162`).
   - `library/core/src/num/nonzero.rs:108-112, 496-525, 614-636` — `NonZero<T>(T::NonZeroInner)`, `new`, `new_unchecked` with `assert_unsafe_precondition!(check_language_ub, ...)` + `intrinsics::unreachable()`, and `get` citing `compiler-team#807`.
   - `library/core/src/ptr/non_null.rs:75-80, 238-248, 410-417` — `NonNull<T>` wrapping `pattern_type!(*const T is !null)`, `new_unchecked` with `assert_unsafe_precondition!`, and `as_ptr` via `transmute`.
   - `library/core/src/ub_checks.rs:95-105` — `check_language_ub()` returning `!cfg!(miri) && intrinsics::ub_checks()` at runtime and `false` in `const`.
   - `library/alloc/src/boxed.rs:233-246, 308-311` — `BoxRaw<T> { pointer: NonNull<T>, _marker: PhantomData<T> }` and `Box<T, A>(BoxRaw<T>, A)` (citing `#162850`).
   - `compiler/rustc_ty_utils/src/layout.rs:241-408` — `ty::Pat` layout narrowing (`Range`, `NotNull`, signed-only `Or` at lines `336-380`, single-field `FieldsShape::Arbitrary` at `403-406`).
   - `compiler/rustc_ty_utils/src/abi.rs:318-339` — `arg_attrs_for_rust_scalar` setting `ArgAttribute::NonNull` when `!valid_range.contains(0)`.
   - `compiler/rustc_abi/src/wrapping_range.rs:19-63` — `WrappingRange` struct and `contains`.
   - `compiler/rustc_abi/src/lib.rs:2115-2205` — `Niche`, `Niche::available`, and `Niche::reserve` (`count = 1` signed-closest-to-zero rule at lines `2177-2185`).
   - `compiler/rustc_abi/src/layout/enum_layout.rs:599-636` — `niche.reserve(dl, count)` in enum niche filling.
   - `compiler/rustc_codegen_llvm/src/abi.rs:48-58, 682-752` — `OPTIMIZATION_ATTRIBUTES` (`NonNull`) and `apply_range_attr` calling `llvm::CreateRangeAttr` gated on `OptLevel != No`.
   - `compiler/rustc_codegen_llvm/src/builder.rs:770-788, 862-877` — `range_metadata` and `nonnull_metadata` on loads.
   - `compiler/rustc_llvm/llvm-wrapper/RustWrapper.cpp:501-509` — `LLVMRustCreateRangeAttribute` wrapping `LLVMCreateConstantRangeAttribute`.
   - `compiler/rustc_codegen_ssa/src/mir/rvalue.rs:1141-1194` — `assume_scalar_range` emitting `llvm.assume` on narrowing transmutes while skipping widening transmutes via `valid_range.contains_range`.
   - `compiler/rustc_mir_transform/src/lib.rs:706-714` — MIR UB-check pass list (`CheckAlignment`, `CheckNull`, `CheckEnums`).
   - `compiler/rustc_mir_transform/src/check_enums.rs:167-237, 466-541` — `EnumFinder::visit_rvalue` filtering strictly on `ty::Adt` + `adt_def.is_enum()`, and `insert_niche_check`.
   - `compiler/rustc_mir_transform/src/check_null.rs:19-26` — `CheckNull` delegating to `check_pointers` (derefs/borrows only).
   - `compiler/rustc_const_eval/src/interpret/validity.rs:990-999, 1015-1070, 1497-1535` — `visit_scalar` and `ty::Pat` validation (including `PatternKind::Or` FIXME at lines `1508-1514`).
   - `compiler/rustc_transmute/src/layout/tree.rs:304-370` — `Tree::from_ty` falling through to `_ => Err(Err::NotYetSupported)` at line `368`.
2. **`rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, 2026-11-11):**
   - Verified identical logic across `niche_types.rs`, `non_null.rs`, `nonzero.rs`, `boxed.rs` (`BoxRaw<T>`), `layout.rs` (`241-408`), `rustc_abi/src/lib.rs` (`2118-2195`), `check_enums.rs` (`167-237`), `validity.rs` (`1012-1067, 1494-1532`), `rustc_codegen_llvm/src/abi.rs` (`504-526, 580`), and `rustc_transmute/src/layout/tree.rs` (`304-368`). Differs from `342d74463af7` only in `library/core/src/pat.rs:10-18` (pre-Macro-2.0 `#[rustc_builtin_macro(pattern_type)] macro_rules!`).
3. **`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, 2026-05-31):**
   - Verified identical `NonNull`, `niche_types.rs`, `layout.rs` signed-only `Or` check (`309-315`), `Niche::reserve` (`2029-2085`, with `size.bytes() == 1` bool guard), `check_enums.rs` (`169-174`), `validity.rs` (`1019, 1501`), `rustc_codegen_llvm/src/abi.rs` (`465-487, 528`), and `rustc_transmute/src/layout/tree.rs` (`290-354`). Differs in `library/alloc/src/boxed.rs:234-237` (pre-`BoxRaw`, using `Unique<T>`) and `library/core/src/pat.rs:10-18`.
4. **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`:**
   - `trusted/lean/Trusted/MirAst.lean:308-321, 612-628` — `MirTy.unsupported` (explicitly listing `Pat` and non-fieldless `Adt`) and `Rvalue.unsupported` (explicitly absorbing `Cast`).
   - `trusted/lean/Trusted/MirSemantics.lean:705-725` — `checkVal` and `isSupportedScalarOrUnitTy`.
   - `vendor/lean-miri/Miri/ABI/WrappingRange.lean:14-150` — `WrappingRange` implementation.
5. **Upstream design and tracking discussions (non-normative provenance):**
   - `https://github.com/rust-lang/compiler-team/issues/807` (MCP #807, closed/accepted 2024-11-28: *"Ban field-projecting into `[rustc_layout_scalar_valid_range_*]` types"*).
   - `https://github.com/rust-lang/rust/pull/148449` (open PR: *"transmutability: model NonZero scalar ranges"*).
   - `https://github.com/rust-lang/rust/issues/123646` (tracking issue for `pattern_types`).

### Preserved Package Support Artifacts

1. **`support/probe_pattern_types.py`** — Standalone Python 3.10+ (stdlib-only) probe harness compiling and executing all layout/niche-byte checks, LLVM IR / MIR inspection (`-O2 -Z ub-checks=no` and `-O0 -Z ub-checks=yes`), 8 runtime validity-cliff modes, `cargo miri run`, signed/unsigned `Or`-pattern layout checks, and `TransmuteFrom` checks.
2. **`support/probe_results_rustc_1_98_nightly.json`** — Scrubbed live execution output captured on `2026-11-22` with `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / LLVM `22.1.6` / `miri 0.1.0 (14210df0e 2026-05-31)` on `x86_64-unknown-linux-gnu`.
3. **`support/probe_results_rustc_1_102_nightly_llvm23.json`** — Scrubbed execution record captured on `2026-11-11` with `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` / LLVM `23.1.5` / Miri on `x86_64-unknown-linux-gnu`, preserving exact LLVM 23.1.5 IR dumps (`range(i8 1, 11)`, `range(i32 1, -2147483648)`, `nonnull`), MIR syntax flags, 4-case validity cliff, signed/unsigned `Or`-pattern split, and `TransmuteFrom` rejection.
4. **`support/PatternTypesNicheAndRangeSoundness.lean`** — Self-contained `1,459`-line Lean `v4.34.1` constructive formalization (`206` declarations, `80` theorems, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`). Verified on `2026-11-22` with:
   ```console
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/PatternTypesNicheAndRangeSoundness.lean
   ```
   exiting with status `0` and zero warnings.

## Revalidation

Each claim in this report admits a cheap, independent revalidation check:

1. **Re-run the empirical `rustc` + LLVM + Miri probe against any newer nightly toolchain:**
   ```console
   python3 support/probe_pattern_types.py --out /tmp/pat_probe_reval.json
   ```
   Check the resulting JSON for five specific discriminators:
   - `opt2_ub_no.ir_fns.take_pat_u8` still folds to `ret i8 %x` with `range(i8 1, 11)` and `take_pat_nonnull` still folds to `ptrtoint; ret` with `nonnull`.
   - `opt0_ub_yes.runtime.bad_pat_u8_11.rc`, `bad_pat_nonnull.rc`, and `bad_nonzero_transmute.rc` vs. `bad_opt_pat_enum_transmute.rc`: if any of the first three changes from `0` to `-6` (panic/abort), `rustc`'s `-Z ub-checks=yes` pipeline has closed the `CheckEnums` gap for `TyKind::Pat` or transparent structs.
   - `opt2_ub_no.runtime.sizes.stdout` (`NICHE_BYTES` line): confirms whether `Niche::reserve` still assigns `0`, `255`, `254` to nested `Option`s over `Pat1To10` and expands `Pat254` at depth `3`.
   - `extra_pat_checks.pat_or_wrapping_range_unsigned.ok`: flipping from `false` to `true` indicates `rustc_ty_utils/src/layout.rs` lifted the signed-only `Or`-pattern restriction.
   - `extra_pat_checks.transmute_from_pat_to_u8.ok` and `transmute_from_nonzero_u8_to_u8.ok`: flipping to `true` indicates `rustc_transmute` gained `TyKind::Pat` / `NonZero` scalar-range support (e.g., landing `rust-lang/rust#148449`).

2. **Re-verify the Lean `v4.34.1` formalization and axiom/safety invariants:**
   ```console
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/PatternTypesNicheAndRangeSoundness.lean
   ```
   To re-audit axioms on any Lean version, append `#print axioms` for `nestedOption_niche_disjoint_and_injective`, `llvm_range_elim_sound_under_pat_validity`, `pat_to_base_always_valid_and_base_to_pat_requires_range_check`, `no_injective_encoding_when_niches_exhausted`, and `ce1`..`ce3` in a temporary copy and confirm the union of axioms is a subset of `{propext, Quot.sound}` with zero `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, or `Lean.trustCompiler`.

3. **Targeted upstream source diffs (avoiding full re-audit):**
   - `git diff <old> <new> -- library/core/src/pat.rs library/core/src/num/niche_types.rs library/core/src/ptr/non_null.rs library/alloc/src/boxed.rs` (tracks `pattern_type!` macro, `NonNull`, `NonZero`, and `BoxRaw` layout architecture).
   - `git diff <old> <new> -- compiler/rustc_ty_utils/src/layout.rs compiler/rustc_abi/src/lib.rs compiler/rustc_mir_transform/src/check_enums.rs compiler/rustc_const_eval/src/interpret/validity.rs compiler/rustc_transmute/src/layout/tree.rs` (tracks `Or`-pattern support, `Niche::reserve` selection, `CheckEnums` coverage, Miri `Or`-pattern validity, and `TransmuteFrom` support).
   - In `joshlf/anneal`, inspect `trusted/lean/Trusted/MirAst.lean` (`inductive MirTy` and `inductive Rvalue`) to check whether `TyKind::Pat` or `CastKind::Transmute` has graduated out of `.unsupported`.
