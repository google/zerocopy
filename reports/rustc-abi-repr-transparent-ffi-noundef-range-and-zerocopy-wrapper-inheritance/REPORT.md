# `#[repr(transparent)]` FFI `extern "C"` ABI, LLVM Attribute Inheritance (`noundef`, `range`, `zeroext`, `nonnull`), `ManuallyDrop` vs. `MaybeUninit` Stripping, and `zerocopy::ReadOnly` vs. `zerocopy::Unalign` Divergence

## Summary

A single-non-ZST `#[repr(transparent)]` struct (or 1-variant enum) inherits not only the C calling convention (`PassMode`) and storage layout of its inner non-1-ZST field, but also its fine-grained LLVM IR parameter and return value validity attributes (`noundef`, `range(...)`, `zeroext i1`, `nonnull`, `align`, `noalias`, `readonly`, `dereferenceable`), making bare primitives (`u32`, `NonZeroU32`, `NonZeroI32`, `bool`, `&u32`), `#[repr(transparent)]` user wrappers, `core::mem::ManuallyDrop<NonZeroU32>`, and `zerocopy::ReadOnly<T>` ABI- and LLVM-IR-identical across `extern "C"` boundaries and eligible for `MergeFunctions` alias deduplication under `-Copt-level=2`. By contrast, `core::mem::MaybeUninit<T>`, `#[repr(C)]` single-field wrappers, and `zerocopy::Unalign<T>` (`#[repr(C, packed)]`) break this equivalence in three sharply distinct ways.

Auditing `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` / `1.98.0-nightly`, upstream `20fe935d50367c0ff8872c2ebfa050c5c99d9201`, and `49d734536222bf28bb6d07d885b3a81d145981da`), `google/zerocopy` (`907b9175fee081872ec883ca4709e6ad922f8ed0` / `0.8.64` and `617bb7bbdca0134bf2a9b79b89b7e991e133275b`), `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`), and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), executing live multi-target `rustc` / `LLVM 22.1.6` / `Miri 0.1.0` probes ([`support/probe_repr_transparent_ffi_abi.py`](support/probe_repr_transparent_ffi_abi.py), [`support/probe_results.json`](support/probe_results.json)), and kernel-checking a 2,323-line standalone `Lean v4.34.1` formalization ([`support/AbiReprTransparentFfiAttributeInheritanceSoundness.lean`](support/AbiReprTransparentFfiAttributeInheritanceSoundness.lean)) establishes five core results:

1. **Bit-for-Bit `#[repr(transparent)]` FFI & Attribute Isomorphism (With One `extern "Rust"` Slice Exception):**
   - Because `#[repr(transparent)]` omits `ReprFlags::ABI_UNOPTIMIZABLE` (`compiler/rustc_abi/src/lib.rs:85,102,213-215`), `LayoutCalculator::univariant` copies the single non-1-ZST field's `BackendRepr::Scalar` (`compiler/rustc_abi/src/layout.rs:1329-1351` in `1.98.0-nightly`) together with its `Scalar::Initialized` `valid_range`, while `TyAndLayout::ty_and_layout_pointee_info_at` recurses transparently into non-Dangling single-field `ty::Adt` wrappers.
   - Across `x86_64`, `aarch64`, and `i686` (`extern "C"` at `-O2`), `WrapU32`, `WrapNz`, `WrapNzI32`, nested `WrapNzNested`, `WrapBool`, `WrapRef<'a>`, and `zerocopy::ReadOnly<T>` emit identical LLVM IR parameter/return attributes to the unwrapped inner type (`noundef`, `range(i32 1, 0)` for both unsigned and wrapped-around signed non-zero 32-bit integers, `zeroext i1`, and `nonnull` + `align 4` + `dereferenceable(4)` + `noalias` + `readonly`), and cross-type `extern "C"` roundtrip calls pass both native execution and `Miri`.
   - **Notable `extern "Rust"` gap:** For `&[u32]` (`PassMode::Pair`), wrapping in `#[repr(transparent)] struct WrapSlice<'a>(&'a [u32], PhantomData<u8>)` changes `*arg.layout.ty.kind()` from `ty::Ref` to `ty::Adt`, suppressing the ad-hoc slice-length `range(i64 0, 2305843009213693952)` emitted on bare `&[u32]` (`compiler/rustc_codegen_llvm/src/abi.rs:552-573` in `1.98.0-nightly`; `770-793` in `20fe935d5`). Under `extern "C"`, both pass identically as `{ i64, i64 }` (`PassMode::Cast`) with no range attribute.
2. **Two-Tier `ManuallyDrop<T>` (`MaybeDangling`) Behavior vs. Total `MaybeUninit<T>` Union Erasure:**
   - `ManuallyDrop<T>` keeps the `#[repr(transparent)]` layout and value-validity scalar invariants (`noundef`, `range(i32 1, 0)` on `ManuallyDrop<NonZeroU32>`; passing uninitialized bytes triggers immediate Miri UB), yet selectively strips pointer-safety attributes (`noalias`, `readonly`, `dereferenceable(4)` — setting `safe: None, size: Size::ZERO`) on `ManuallyDrop<&u32>` while preserving `noundef nonnull align 4` (`compiler/rustc_middle/src/ty/layout.rs:1061-1073` in `1.98.0-nightly`; `1244-1256` in `20fe935d5`).
   - `MaybeUninit<T>` is a `#[repr(transparent)] union`, so `LayoutCalculator::layout_of_union` calls `field.backend_repr.to_union()` (`Scalar::Initialized` $\mapsto$ `Scalar::Union`), marking `is_uninit_valid() == true`, `is_always_valid() == true`, and clearing `pointee_info` (`compiler/rustc_abi/src/layout.rs:438`, `compiler/rustc_abi/src/lib.rs:1591-1630`). This strips **both** `noundef` and `range(...)` (`mu_nz` emits `define i32 @mu_nz(i32 returned %x)`) as well as `nonnull` and `align 4` on `&u32` (`mu_ref` emits `define ptr @mu_ref(ptr readnone returned captures(ret: address, provenance) %x)`), allowing uninitialized or zero bit patterns to cross `extern "C"` boundaries without LLVM IR UB.
3. **Real `zerocopy::ReadOnly<T>` vs. `zerocopy::Unalign<T>` Divergence:**
   - `zerocopy::ReadOnly<T>` (`#[repr(transparent)]` in `google/zerocopy/zerocopy/src/wrappers.rs:626-631`) behaves identically to the unwrapped inner type across all targets and calling conventions, and passes `Miri` substitution with `NonZeroU32`.
   - `zerocopy::Unalign<T>` (`#[repr(C, packed)]` in `google/zerocopy/zerocopy/src/wrappers.rs:117-118`) sets `ReprFlags::IS_C` inside `ReprFlags::ABI_UNOPTIMIZABLE`, forcing `BackendRepr::Memory` **even when `align_of::<T>() == 1`** (verified with `Unalign<NonZeroU8>`, which emits bare `define i8 @zc_unalign_u8_nz(i8 returned %0)` with neither `noundef` nor `range`). Under `extern "C"`, `Unalign<NonZeroU32>` strips `noundef` and `range` on `x86_64`, widens to `range(i64 0, 4294967296) i64` on `aarch64`, and switches from register scalar to stack `sret` + `byval([4 x i8])` (`PassMode::Indirect`) on `i686`. Miri immediately rejects calling `Unalign<NonZeroU32>` as `NonZeroU32` (`Undefined Behavior: calling a function whose parameter #1 has type zerocopy::Unalign<std::num::NonZero<u32>> passing argument of type std::num::NonZero<u32>`). Under `extern "Rust"`, `adjust_for_rust_abi` (`compiler/rustc_target/src/callconv/mod.rs:804-815`) recovers `noundef` via `layout_is_noundef` for `size <= ptr_size`, merging `@zc_rust_unalign_nz` as an alias of `@zc_readonly_u32`, while still dropping `range(i32 1, 0)`.
4. **Optimization-Gate Separation (`-O0` vs. `-O2`):**
   - Directly inspecting `compiler/rustc_codegen_llvm/src/abi.rs:38-107,465-481` (`1.98.0-nightly`) and comparing `-O0` vs. `-O2` IR shows that `pointee_align` (`align 4`) and `ArgExtension` (`zeroext`/`sext`) apply unconditionally at `-O0`, whereas `NoUndef`, `NonNull`, `NoAlias`, `ReadOnly`, `Dereferenceable`, `Captures`, and `range(...)` live inside the `cx.sess().opts.optimize != config::OptLevel::No` gate (except `NoUndef` under MemorySanitizer). Thus `-O0` emits `define i32 @wrap_nz(i32 %x)` (neither `noundef` nor `range`), `define zeroext i1 @wrap_bool(i1 zeroext %x)`, and `define align 4 ptr @wrap_ref(ptr align 4 %x)`.
5. **Machine-Checked Soundness & Substitution Formalization (`Lean v4.34.1`):**
   - [`support/AbiReprTransparentFfiAttributeInheritanceSoundness.lean`](support/AbiReprTransparentFfiAttributeInheritanceSoundness.lean) (`2,323` lines, `95` `noncomputable def`s, `114` explicit theorems, `283` MetaM-audited theorem declarations, `0` `sorry`, `0` `Classical.choice`, `0` `._unsafe_rec`, `0` warnings) mechanizes `LayoutSummary`, `computePassMode`, `computeArgAttrs`, `emitLlvmArgAttrs`, runtime bit/pointer validity, LLVM parameter UB semantics, an attribute-strength lattice `LlvmParamIR.WeakerThan`, and cross-language `FfiBoundaryCompatible`, proving exact isomorphism, `MaybeUninit`/`Unalign` stripping soundness, negative UB countermodels, and opt-level monotonicity.

---

## Applicability

This report establishes exact compiler mechanics, LLVM IR output, Miri runtime behavior, and formal ABI invariants across the following pinned subjects recorded in [`REPORT.json`](REPORT.json):

- **Primary Empirical & Source Toolchain (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):**
  - `rustc 1.98.0-nightly (14210df0e 2026-05-31)` with LLVM `22.1.6` and bundled `miri 0.1.0 (14210df0e2 2026-05-31)`.
  - Audited compiler crates: `compiler/rustc_abi/src/{lib.rs,layout.rs}`, `compiler/rustc_ty_utils/src/abi.rs`, `compiler/rustc_middle/src/ty/layout.rs`, `compiler/rustc_target/src/callconv/{mod.rs,x86_64.rs}`, `compiler/rustc_codegen_llvm/src/abi.rs`, and `library/core/src/mem/manually_drop.rs`.
  - Executed directly on host `x86_64-unknown-linux-gnu` and cross-compiled to `aarch64-unknown-linux-gnu` and `i686-unknown-linux-gnu` using `--edition=2024`.
- **Upstream `rust-lang/rust` Evolution Comparison (`20fe935d50367c0ff8872c2ebfa050c5c99d9201` and `49d734536222bf28bb6d07d885b3a81d145981da`):**
  - Audited source changes between historical `49d734536...`, nightly `14210df0e...`, and upstream `20fe935d5...`. Shared behaviors (transparent newtype unboxing, `to_union()`, `inhibit_newtype_abi_optimization()`, `apply_range_attr` omitting `PassMode::Cast`, and `OPTIMIZATION_ATTRIBUTES` gating of `NoUndef`/`NonNull`) hold across all three revisions. Version-specific implementation mechanics (`Primitive::Bool` first-class variant vs. `is_bool()` on `Int(I8, false)`, `ManuallyDrop<T>` field type `MaybeDangling<T>` vs. `T` + `is_like_maybe_dangling()`, and `NoFree` in `OPTIMIZATION_ATTRIBUTES`) are explicitly distinguished in Findings §2.
- **`zerocopy` Crate (`google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0`, `0.8.64`, compared with `google/zerocopy@617bb7bbdca0134bf2a9b79b89b7e991e133275b`):**
  - `zerocopy/src/wrappers.rs` is byte-identical between `907b9175...` (compiled and tested live under `rustc 1.98.0-nightly`, `--edition=2021`, with `--cfg no_zerocopy_allocator_api_1_100_0` and `CARGO_PKG_VERSION=0.8.64`, plus `Miri 0.1.0`) and `617bb7bb...`.
- **Normative Language Specification (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):**
  - `src/type-layout.md` sections `r[layout.repr.alignment]` and `r[layout.repr.transparent]` establish the normative contract; LLVM IR attributes and `PassMode` internals are implementation choices of `rustc` and LLVM rather than Rust language guarantees except where explicitly promised (e.g., `#[repr(transparent)]` ABI equivalence and `#[repr(C)]` C ABI compatibility).
- **Verified-Rust Framework Consumer Context (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
  - Audited `trusted/lean/Trusted/MirSemantics.lean:717-725` to map where `#[repr(transparent)]` and `#[repr(C, packed)]` wrapper semantics intersect Anneal's supported MIR type boundary (`isSupportedScalarOrUnitTy`).
- **Formal Mechanization (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):**
  - Standalone `Init`-only kernel proof compiled with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

Scope claims are strictly limited to types, wrappers, optimization flags, calling conventions (`extern "C"` and `extern "Rust"`), and architectures examined above; non-examined cases are documented in **Boundaries**.

---

## Findings

### 1. Normative Spec vs. `rustc` Layout Mechanism (`ReprFlags`, `univariant`, `layout_of_union`)

`Basis: normative + source (rust-lang/reference@c9cc32825b03:src/type-layout.md:632-697, rust-lang/rust@14210df0e:compiler/rustc_abi/src/lib.rs, compiler/rustc_abi/src/layout.rs)`

Under the Rust Reference (`src/type-layout.md:682-696`), `#[repr(transparent)]` may only be placed on a `struct` or single-variant `enum` containing:
- any number of fields with size `0` and alignment `1` (1-ZSTs, such as `()`, `PhantomData<T>`, or `[u8; 0]`), and
- at most one other field (`r[layout.repr.transparent.constraint-field]`).

It guarantees that the wrapper has "the same layout and ABI as the only non-size 0 non-alignment 1 field, if present, or unit otherwise" (`r[layout.repr.transparent.layout-abi]`) and forbids combining `transparent` with any other `repr` (`r[layout.repr.transparent.constraint-exclusive]`). By contrast, `#[repr(C)]` gives the type the ABI of a C `struct`, even when it has only a single primitive field (`src/type-layout.md:693`), and `#[repr(C, packed)]` lowers alignment to `1` while retaining `C` representation rules (`src/type-layout.md:636-654`).

Inside `rustc_abi`, these normative constraints map onto bitflags and three distinct code paths:

1. **`ReprFlags` and `inhibit_newtype_abi_optimization()` (`compiler/rustc_abi/src/lib.rs:82-104, 213-215` in `14210df0e`):**
   ```rust
   bitflags! {
       impl ReprFlags: u8 {
           const IS_C               = 1 << 0;
           const IS_SIMD            = 1 << 1;
           const IS_TRANSPARENT     = 1 << 2;
           ...
           const ABI_UNOPTIMIZABLE = ReprFlags::IS_C.bits() | ReprFlags::IS_SIMD.bits();
       }
   }

   pub fn inhibit_newtype_abi_optimization(&self) -> bool {
       self.flags.intersects(ReprFlags::ABI_UNOPTIMIZABLE)
   }
   ```
   Crucially, `IS_C` (set by `#[repr(C)]` and `#[repr(C, packed)]`) sets `ABI_UNOPTIMIZABLE`, making `inhibit_newtype_abi_optimization()` return `true`. Neither `IS_TRANSPARENT` nor default `#[repr(Rust)]` sets `ABI_UNOPTIMIZABLE`.

2. **Struct / Single-Variant Enum Scalar Forwarding (`LayoutCalculator::univariant`):**
   In `compiler/rustc_abi/src/layout.rs:1329-1359` (`14210df0e`; identical logic at lines `833-863` in `20fe935d5` and `1321-1351` in `49d734536`):
   ```rust
   let optimize_abi = !repr.inhibit_newtype_abi_optimization();
   if sized && size.bytes() > 0 {
       let mut non_zst_fields = fields.iter_enumerated().filter(|&(_, f)| !f.is_zst());
       match (non_zst_fields.next(), non_zst_fields.next(), non_zst_fields.next()) {
           (Some((i, field)), None, None) => {
               layout_of_single_non_zst_field = Some(field);
               if offsets[i].bytes() == 0 && align == field.align.abi && size == field.size {
                   match field.backend_repr {
                       BackendRepr::Scalar(_) | BackendRepr::SimdVector { .. }
                           if optimize_abi =>
                       {
                           abi = field.backend_repr;
                       }
                       BackendRepr::ScalarPair(..) => {
                           abi = field.backend_repr;
                       }
                       _ => {}
                   }
               }
           }
           ...
       }
   }
   ```
   Two structural mechanisms govern all wrapper behavior here:
   - **Whole-`BackendRepr` copy for transparent/Rust newtypes:** When `optimize_abi` is `true`, `abi = field.backend_repr` copies `BackendRepr::Scalar(scalar)` **intact**, including both whether `scalar` is `Scalar::Initialized` vs. `Scalar::Union` and its exact `valid_range: WrappingRange` (e.g., `1..=u32::MAX` for `NonZeroU32` and `NonZeroI32`, `0..=1` for `bool`, `1..=usize::MAX` for `&T`).
   - **Asymmetric `ScalarPair` bypass for `#[repr(C)]` vs. `Scalar` blocking:** When `IS_C` is set (`optimize_abi == false`), single `BackendRepr::Scalar` fields **cannot** unpack (`abi` remains `BackendRepr::Memory { sized: true }`), **even when `align == field.align.abi && size == field.size`** (for example, both `#[repr(C)] struct ReprCU32(u32)` and `#[repr(C, packed)] struct Unalign<NonZeroU8>(NonZeroU8)`!). By contrast, `BackendRepr::ScalarPair` unconditionally copies `field.backend_repr` because LLVM/C ABIs pass two-scalar aggregates differently anyway. Furthermore, `LayoutCalculator::univariant` (`layout.rs:1407-1414` in `14210df0e`) forwards `unadjusted_abi_align` from `layout_of_single_non_zst_field` for `repr.transparent()`, while rejecting 0-sized fields with alignment $> 1$ (e.g., `[u32; 0]`) via frontend error `E0690`.

3. **Union Layout & `Scalar::to_union()` Erasure (`LayoutCalculator::layout_of_union`):**
   `core::mem::MaybeUninit<T>` is defined with `#[repr(transparent)] pub union MaybeUninit<T> { uninit: (), value: ManuallyDrop<T> }` (`library/core/src/mem/maybe_uninit.rs:351-358` in `20fe935d5`). Because it is a `union`, layout goes through `LayoutCalculator::layout_of_union` (`compiler/rustc_abi/src/layout.rs:420-495` in `14210df0e` / `405-495` in `20fe935d5`):
   - `uninit: ()` satisfies `field.is_zst()`, so line `431` skips it (`continue`).
   - `value: ManuallyDrop<T>` is the lone non-ZST field, so line `438` runs:
     ```rust
     // Discard valid range information and allow undef
     let field_abi = field.backend_repr.to_union();
     ```
   - For `Scalar`, `Scalar::to_union(&self)` (`compiler/rustc_abi/src/lib.rs:1591-1593` in `14210df0e`; `1646-1648` in `20fe935d5`) constructs `Scalar::Union { value: self.primitive() }`, permanently discarding `valid_range` and changing `is_uninit_valid()` from `false` to `true` and `is_always_valid()` to `true` (`lib.rs:1596-1630`), while preserving `BackendRepr::Scalar` (the machine register primitive size/kind).

---

### 2. Evolution Across `rustc` Revisions: `bool` Primitive Representation and `ManuallyDrop` / `MaybeDangling`

`Basis: source (rust-lang/rust@49d734536222, rust-lang/rust@14210df0e27c, rust-lang/rust@20fe935d5036)`

Although the external LLVM IR observable on `x86_64`, `aarch64`, and `i686` is identical across `14210df0e` (`1.98.0-nightly`) and `20fe935d5` (`main`), comparing `14210df0e`, intermediate snapshot `49d734536`, and `20fe935d5` reveals the exact compiler refactorings governing `bool`, `NoFree`, `#[repr(C)]` tracking, and `ManuallyDrop<T>`:

| Mechanism | `14210df0e` (`1.98.0-nightly`) | `49d734536` (Intermediate Snapshot) | `20fe935d5` (`main` Upstream) | Observable `extern "C"` Effect |
| :--- | :--- | :--- | :--- | :--- |
| **`bool` representation in `rustc_abi`** | `Scalar::Initialized { value: Primitive::Int(I8, false), valid_range: 0..=1 }` matched by `Scalar::is_bool()` (`rustc_abi/src/lib.rs:1563-1572`) | `rustc_abi` not fetched in audit; `apply_range_attr` still guards `&& !scalar.is_bool()` (`rustc_codegen_llvm/src/abi.rs:478`) | Dedicated `Primitive::Bool` variant; `is_bool()` matches `Scalar::Initialized { value: Primitive::Bool, .. }` (`rustc_abi/src/lib.rs:1621-1623`) | Identical (`define noundef zeroext i1 @...(i1 noundef returned zeroext %x)` at `-O2`) |
| **`bool` `NoUndef` + `Zext` generation** | Early return in `arg_attrs_for_rust_scalar`: `if scalar.is_bool() { attrs.ext(ArgExtension::Zext); attrs.set(ArgAttribute::NoUndef); return attrs; }` (`rustc_ty_utils/src/abi.rs:333-337`); `apply_range_attr` checks `!scalar.is_bool()` (`abi.rs:471`) | `arg_attrs_for_rust_scalar` already drops the `is_bool()` early return and sets `NoUndef` uniformly via `!scalar.is_uninit_valid()` (`rustc_ty_utils/src/abi.rs:332-334`) | Same uniform `!scalar.is_uninit_valid()` (`rustc_ty_utils/src/abi.rs:328-330`); `Zext` moved to `extend_integer_width_to` (`callconv/mod.rs:573-575`) & `x86_64` return rule (`x86_64.rs:311-313`); `apply_range_attr` omits `!scalar.is_bool()` (`abi.rs:681-693`) | Identical (`zeroext` + `noundef` on arg & ret; never emits `range(i1 ...)`) |
| **`ManuallyDrop<T>` definition & pointee masking** | `ManuallyDrop<T>` wraps `value: MaybeDangling<T>` (`core/src/mem/manually_drop.rs:161-163`); `ty_and_layout_pointee_info_at` checks `adt_def.is_maybe_dangling()` (`rustc_middle/src/ty/layout.rs:1061-1073`) | *(File not inspected at `49d734536`)* | `ManuallyDrop<T>` reverted to `value: T` (`core/src/mem/manually_drop.rs:156-158`); `ty_and_layout_pointee_info_at` checks `this.ty.is_like_maybe_dangling()` (`rustc_middle/src/ty/layout.rs:1244-1256`) | Both preserve `noundef`, `nonnull`, `align`, and `range(...)` while stripping `safe` (`noalias`, `readonly`) and `size` (`dereferenceable`) on references |
| **`#[repr(C)]` field tracking & `NoFree`** | `LayoutData` has no `repr_c` boolean (`layout.rs:1421-1430`); `OPTIMIZATION_ATTRIBUTES` lists 5 attrs `[NoAlias, NonNull, ReadOnly, NoUndef, Writable]` (`abi.rs:41-47`) | `LayoutData` has no `repr_c` field (`layout.rs:1413-1424`); `OPTIMIZATION_ATTRIBUTES` already adds `NoFree` (`abi.rs:41-51`) | `univariant` computes `repr_c = repr.c() \|\| (repr.transparent() && fields.iter().any(\|f\| f.repr_c))` (`layout.rs:924`); `OPTIMIZATION_ATTRIBUTES` keeps 6 attrs incl. `NoFree` (`abi.rs:48-58`) | `NoUndef` stays optimization-gated across all three; `dereferenceable` gained an LLVM `nofree` version guard comment in `20fe935d5:89-90` |

Note that `49d734536` captures an exact intermediate stage between `14210df0e` (`1.98.0-nightly`) and `20fe935d5` (`main`): `49d734536` had already removed the `is_bool()` early return from `arg_attrs_for_rust_scalar` and added `NoFree` to `OPTIMIZATION_ATTRIBUTES`, before `apply_range_attr` dropped `!scalar.is_bool()` and before `LayoutData` gained `repr_c`. Static-analysis tools inspecting `rustc` internals must therefore key off the exact compiler revision rather than assuming monolithic feature boundaries.

---

### 3. LLVM IR Attribute Inheritance & Stripping Matrix (`-O2`, `MergeFunctions` Aliases, `-O0` Gate)

`Basis: source + execution (compiler/rustc_codegen_llvm/src/abi.rs:38-107,465-583; support/probe_results.json:22-217)`

On `x86_64-unknown-linux-gnu` (`rustc 1.98.0-nightly`, `LLVM 22.1.6`), compiling `PROBE_A_IR_RS` with `-Copt-level=2 -Zmerge-functions=disabled --emit=llvm-ir` (`support/probe_results.json:22-151`) and with default `-Copt-level=2` (`support/probe_results.json:153-165`) yields the following exact IR signatures and alias mergers:

| Wrapper / Function | Rust Signature (`extern "C"` unless noted) | Emitted LLVM 22.1.6 IR (`-O2 -Zmerge-functions=disabled`) | Default `-O2` `MergeFunctions` Alias Target | Inherited / Stripped Summary |
| :--- | :--- | :--- | :--- | :--- |
| `bare_u32` | `fn(u32) -> u32` | `define noundef i32 @bare_u32(i32 noundef returned %x)` | Canonical definition | `noundef` |
| `wrap_u32` | `WrapU32(PhantomData<u8>, u32, [u8; 0])` | `define noundef i32 @wrap_u32(i32 noundef returned %x)` | `@bare_u32` | Identical (`noundef`) |
| `bare_nz` | `fn(NonZeroU32) -> NonZeroU32` | `define noundef range(i32 1, 0) i32 @bare_nz(i32 noundef returned range(i32 1, 0) %x)` | Canonical definition | `noundef` + `range(i32 1, 0)` |
| `wrap_nz` | `WrapNz(PhantomData<*const ()>, NonZeroU32, ())` | `define noundef range(i32 1, 0) i32 @wrap_nz(i32 noundef returned range(i32 1, 0) %x)` | `@bare_nz` | Identical (`noundef range(i32 1, 0)`) |
| `bare_nzi32` / `wrap_nzi32` | `NonZeroI32` / `WrapNzI32(NonZeroI32, PhantomData<u8>)` | `define noundef range(i32 1, 0) i32 @...(i32 noundef returned range(i32 1, 0) %x)` | `@bare_nz` | Identical! Wrap-around unsigned range `[1, 2^32-1]` equals `NonZeroU32` in LLVM |
| `wrap_nz_nested` | `WrapNzNested(WrapNz, [(); 8])` | `define noundef range(i32 1, 0) i32 @wrap_nz_nested(i32 noundef returned range(i32 1, 0) %x)` | `@bare_nz` | Transitive across nested `transparent` layers |
| `bare_bool` / `wrap_bool` | `bool` / `WrapBool((), bool, PhantomData<u16>)` | `define noundef zeroext i1 @...(i1 noundef returned zeroext %x)` | `@wrap_bool` $\to$ `@bare_bool` | Preserves `noundef` + `zeroext` on both param & return |
| `bare_ref` / `wrap_ref` | `&u32` / `WrapRef(&u32, PhantomData<u8>)` | `define noundef nonnull align 4 ptr @...(ptr noalias noundef readonly returned align 4 captures(ret: address, read_provenance) dereferenceable(4) %x)` | `@wrap_ref` $\to$ `@bare_ref` | Preserves all 8 attributes/flags (`noalias`, `noundef`, `nonnull`, `readonly`, `align 4`, `dereferenceable(4)`, `captures`) |
| `md_nz` | `ManuallyDrop<NonZeroU32>` | `define noundef range(i32 1, 0) i32 @md_nz(i32 noundef returned range(i32 1, 0) %x)` | `@bare_nz` | Preserves `noundef` + `range(i32 1, 0)` |
| `md_ref` | `ManuallyDrop<&u32>` | `define noundef nonnull align 4 ptr @md_ref(ptr noundef nonnull readnone returned align 4 captures(ret: address, provenance) %x)` | Separate def (stronger `readnone` / drops `dereferenceable`) | Keeps `noundef`, `nonnull`, `align 4`; **strips** `noalias`, `readonly`, `dereferenceable(4)` |
| `mu_nz` | `MaybeUninit<NonZeroU32>` | `define i32 @mu_nz(i32 returned %x)` | Canonical definition for bare `i32` | **Strips** `noundef` and `range(i32 1, 0)` |
| `mu_ref` | `MaybeUninit<&u32>` | `define ptr @mu_ref(ptr readnone returned captures(ret: address, provenance) %x)` | Separate def | **Strips** `noundef`, `nonnull`, `align 4`, `noalias`, `readonly`, `dereferenceable(4)` |
| `repr_c_u32` / `repr_c_nz` | `#[repr(C)] struct(u32 / NonZeroU32)` | `define i32 @...(i32 returned %0)` | `@mu_nz` | `PassMode::Cast`: **strips** `noundef` & `range` despite `u32` layout match! |
| `bare_slice_len` / `wrap_slice_len` | `extern "C" fn(&[u32] / WrapSlice) -> usize` | `define noundef i64 @...({ i64, i64 } %0)` | `@wrap_slice_len` $\to$ `@bare_slice_len` | `PassMode::Cast { i64, i64 }` on SysV `extern "C"` |
| `bare_slice_len_rust` | `extern "Rust" fn(&[u32]) -> usize` | `define noundef range(i64 0, 2305843009213693952) i64 @bare_slice_len_rust(ptr ..., i64 noundef returned range(i64 0, 2305843009213693952) %s.1)` | Distinct | Ad-hoc `ty::Ref(_, ty::Slice)` range attached |
| `wrap_slice_len_rust` | `extern "Rust" fn(WrapSlice) -> usize` | `define noundef i64 @wrap_slice_len_rust(ptr ..., i64 noundef returned %s.1)` | Distinct | `PassMode::Pair` preserved, **loses** `range(i64 0, ...)`! |

#### Why Signed `NonZeroI32` Produces Identical LLVM `range(i32 1, 0)` and Merges With `NonZeroU32`

Both `NonZeroU32` (`WrappingRange { start: 1, end: 0xFFFF_FFFF }`) and `NonZeroI32` (`[-2^{31}, -1] \cup [1, 2^{31}-1]`) represent the exact same set of non-zero 32-bit patterns in two's complement arithmetic. Because LLVM `range(i32 low, i32 high)` is a modular half-open interval `[low, high) mod 2^32`, `start = 1, end = 0xFFFF_FFFF` has `end + 1 ≡ 0 (mod 2^32)`, yielding `range(i32 1, 0)` in LLVM IR for both (`bare_nz`, `wrap_nz`, `bare_nzi32`, `wrap_nzi32`), which `MergeFunctions` then collapses into `@bare_nzi32 = unnamed_addr alias i32 (i32), ptr @bare_nz`!

#### Exact Mechanism of the `-O0` Optimization Gate (`ABI_AFFECTING_ATTRIBUTES` vs. `OPTIMIZATION_ATTRIBUTES`)

Inspection of `compiler/rustc_codegen_llvm/src/abi.rs:38-107` (`14210df0e`; lines `45-96` in `20fe935d5`) explains every difference observed between `-Copt-level=0` and `-Copt-level=2` (`support/probe_results.json:166-217`):

```rust
const ABI_AFFECTING_ATTRIBUTES: [(ArgAttribute, llvm::AttributeKind); 1] =
    [(ArgAttribute::InReg, llvm::AttributeKind::InReg)];

const OPTIMIZATION_ATTRIBUTES: [(ArgAttribute, llvm::AttributeKind); 5] = [
    (ArgAttribute::NoAlias, llvm::AttributeKind::NoAlias),
    (ArgAttribute::NonNull, llvm::AttributeKind::NonNull),
    (ArgAttribute::ReadOnly, llvm::AttributeKind::ReadOnly),
    (ArgAttribute::NoUndef, llvm::AttributeKind::NoUndef),
    (ArgAttribute::Writable, llvm::AttributeKind::Writable),
];
```
In `get_attrs` (`rustc_codegen_llvm/src/abi.rs:55-105`), `InReg`, `pointee_align` (`align N`), and `arg_ext` (`zeroext`/`sext`) execute unconditionally (including at `-O0`). By contrast, `dereferenceable`, all `OPTIMIZATION_ATTRIBUTES` (**including `NoUndef` and `NonNull`**), `CAPTURES_ATTRIBUTES`, and `apply_range_attr` (`abi.rs:466`) are gated on `cx.sess().opts.optimize != config::OptLevel::No` (unless MemorySanitizer is active, in which case lines `97-104` emit `NoUndef` alone). Our live `-O0` probe (`support/probe_results.json:167-216`) verifies this directly:
- `bare_nz`, `wrap_nz`, `md_nz`, `mu_nz` all collapse to bare `define i32 @...(i32 %x)` at `-O0` (stripping **both** `noundef` and `range`);
- `wrap_bool` retains `zeroext` while stripping `noundef`: `define zeroext i1 @wrap_bool(i1 zeroext %x)`;
- `wrap_ref` retains `align 4` while stripping `noundef`, `nonnull`, `noalias`, `readonly`, `dereferenceable(4)`, and `captures(...)`: `define align 4 ptr @wrap_ref(ptr align 4 %x)`.

A static analyzer or FFI harness probing `-O0` IR therefore **cannot** observe `noundef`, `nonnull`, `range`, or `dereferenceable`, even on bare `NonZeroU32` or `&u32` (absent MSan). Conversely, checking `zeroext` and `align` works reliably even at `-O0`.

---

### 4. `ManuallyDrop<T>` vs. `MaybeUninit<T>` Divergence: Value Validity vs. Reference Pointee Attributes

`Basis: source + execution (rust-lang/rust@14210df0e:compiler/rustc_middle/src/ty/layout.rs:1061-1073, rust-lang/rust@20fe935d5:compiler/rustc_middle/src/ty/layout.rs:1244-1256; support/probe_results.json:89-112,348-363)`

Although both `ManuallyDrop<T>` and `MaybeUninit<T>` suppress automatic destructor execution and carry `#[repr(transparent)]`, `rustc` treats them fundamentally differently across non-reference scalars versus references:

1. **For Non-Reference Scalars (`ManuallyDrop<NonZeroU32>` vs. `MaybeUninit<NonZeroU32>`):**
   - `ManuallyDrop<T>` is a `struct`, so `univariant` runs and copies `BackendRepr::Scalar(Scalar::Initialized { value: Int(I32, false), valid_range: 1..=u32::MAX })` unmodified. Consequently, `md_nz` emits `noundef range(i32 1, 0) i32` and `ManuallyDrop<NonZeroU32>` **retains `T`'s validity invariant** (`ub_manually_drop_nonzero_uninit` triggers `warning: the type std::mem::ManuallyDrop<std::num::NonZero<u32>> does not permit being left uninitialized` and immediate Miri UB: `Undefined Behavior: reading memory at alloc156[0x0..0x4], but memory is uninitialized`).
   - `MaybeUninit<T>` is a `union`, so `layout_of_union` applies `to_union()`, rewriting `Scalar::Initialized` $\mapsto$ `Scalar::Union`. Both `noundef` and `range(i32 1, 0)` disappear (`define i32 @mu_nz(i32 returned %x)`), and Miri accepts `mu_nz_id(MaybeUninit::<NonZeroU32>::uninit())` and `mu_nz_id(MaybeUninit::<NonZeroU32>::zeroed())` cleanly until `.assume_init()` is later called on the zeroed value (`ub_maybe_uninit_assume_init_zero`).

2. **For References (`ManuallyDrop<&u32>` vs. `MaybeUninit<&u32>` vs. `#[repr(transparent)] struct WrapRef(&u32)`):**
   In `compiler/rustc_middle/src/ty/layout.rs:1061-1073` (`14210df0e`) and `1244-1256` (`20fe935d5`), `ty_and_layout_pointee_info_at` intentionally weakens reference pointee guarantees inside `ManuallyDrop` / `MaybeDangling`:
   ```rust
   if this.ty.is_like_maybe_dangling()
       && let Some(info) = result
   {
       result = Some(PointeeInfo {
           // Mark the pointer as raw
           // (thus removing noalias/readonly/etc in case of the llvm backend)
           safe: None,
           // Make sure we don't assert dereferenceability of the pointer.
           size: Size::ZERO,
           // Preserve the alignment assertion! That is required even inside `MaybeDangling`.
           align: info.align,
       });
   }
   ```
   This creates an exact three-rung strict ordering observable in emitted LLVM 22.1.6 IR (`support/probe_results.json:78-112`):
   - **Full guarantees (`&u32` / `WrapRef<&u32>` / `ReadOnly<&u32>`):**
     `define noundef nonnull align 4 ptr @wrap_ref(ptr noalias noundef readonly returned align 4 captures(ret: address, read_provenance) dereferenceable(4) %x)`
   - **Intermediate `MaybeDangling` (`ManuallyDrop<&u32>`):**
     `define noundef nonnull align 4 ptr @md_ref(ptr noundef nonnull readnone returned align 4 captures(ret: address, provenance) %x)`
     Notice why `noundef`, `nonnull`, and `align 4` survive: `noundef` and `nonnull` come from `BackendRepr::Scalar(Scalar::Initialized { value: Pointer, valid_range: 1..=2^64-1 })` (never erased because `ManuallyDrop` is not a union!), and `align: info.align` is explicitly preserved in `PointeeInfo` because alignment and non-nullness remain validity invariants of the pointer bits even if the pointee allocation is later freed (dangling). By contrast, `safe: None, size: Size::ZERO` removes `noalias`, `readonly`, and `dereferenceable(4)` (allowing LLVM to infer `readnone` on the identity function `@md_ref`).
   - **Total erasure (`MaybeUninit<&u32>`):**
     `define ptr @mu_ref(ptr readnone returned captures(ret: address, provenance) %x)`
     All six attributes (`noundef`, `nonnull`, `align 4`, `noalias`, `readonly`, `dereferenceable(4)`) are stripped, allowing `MaybeUninit::<&u32>::zeroed()` (`0x0`, unaligned/null/uninit) without Miri or LLVM UB (`support/probe_results.json:108-111`, probe line `194`).

---

### 5. Real `zerocopy::ReadOnly<T>` vs. `zerocopy::Unalign<T>` (`#[repr(C, packed)]`) Divergence

`Basis: source + execution (google/zerocopy@907b9175fee0:zerocopy/src/wrappers.rs:95-119,608-670; compiler/rustc_abi/src/layout.rs:1329-1359; support/probe_results.json:371-531)`

Evaluating real compiled `zerocopy v0.8.64` (`zerocopy/src/wrappers.rs`, verified byte-identical to `google/zerocopy@617bb7bb...` via `diff -u`) demonstrates how seemingly similar wrapper types diverge sharply in C FFI:

1. **`zerocopy::ReadOnly<T>` (`src/wrappers.rs:626-631`):**
   ```rust
   #[derive(Copy)]
   #[repr(transparent)]
   pub struct ReadOnly<T: ?Sized> {
       inner: T,
   }
   ```
   Because `ReadOnly<T>` uses `#[repr(transparent)]` with a single field `inner: T`, `rustc` treats it as an exact transparent newtype:
   - `zc_readonly_u32`: `define noundef i32 @zc_readonly_u32(i32 noundef returned %x)` (`size = 4, align = 4`)
   - `zc_readonly_nz`: `define noundef range(i32 1, 0) i32 @zc_readonly_nz(i32 noundef returned range(i32 1, 0) %x)`
   - `zc_readonly_ref`: `define noundef nonnull align 4 ptr @zc_readonly_ref(ptr noalias noundef readonly returned align 4 captures(ret: address, read_provenance) dereferenceable(4) %x)`
   Replacing `NonZeroU32` with `ReadOnly<NonZeroU32>` across an `extern "C"` boundary (`call_ro_as_bare`) executes with `RO_SIZE=4 RO_ALIGN=4 RO_VAL=77 RO_VIA_BARE=91 UA_SIZE=4 UA_ALIGN=1 UA_VAL=88` cleanly in both native release code and `Miri 0.1.0` (`support/probe_results.json:516-525`).

2. **`zerocopy::Unalign<T>` (`src/wrappers.rs:117-118`):**
   ```rust
   #[repr(C, packed)]
   pub struct Unalign<T>(T);
   ```
   Because `Unalign<T>` carries `#[repr(C, packed)]`, `ReprFlags::IS_C` sets `inhibit_newtype_abi_optimization() == true` (`optimize_abi = false` in `univariant`), forcing `BackendRepr::Memory { sized: true }` and `align = 1`. Live LLVM 22.1.6 IR (`support/probe_results.json:401-424`) confirms:
   - `zc_unalign_u32`: `define i32 @zc_unalign_u32(i32 returned %0)` (`PassMode::Cast`, **loses `noundef`**)
   - `zc_unalign_nz`: `define i32 @zc_unalign_nz(i32 returned %0)` (**loses both `noundef` and `range(i32 1, 0)`**, and aliases `@zc_unalign_u32` under `MergeFunctions`!)
   - `zc_unalign_u8_nz` (`Unalign<NonZeroU8>`): `define i8 @zc_unalign_u8_nz(i8 returned %0)` — critical proof that even when the inner type **already has `align == 1`** (`align_of::<NonZeroU8>() == align_of::<Unalign<NonZeroU8>>() == 1`), `ReprFlags::IS_C` alone blocks `BackendRepr::Scalar` forwarding (`univariant` lines `1347-1348`), stripping `noundef` and `range(i8 1, 0)`!
   - `zc_unalign_ref` (`Unalign<&u32>`): `define i64 @zc_unalign_ref(i64 returned %0)` — degrades a pointer reference into an opaque 64-bit integer register cast (`i64`), losing `ptr`, provenance/aliasing attributes, `nonnull`, `align`, `noundef`, and `dereferenceable(4)`! (LLVM IR integer casts of pointers are raw bit-transfers rather than typed `ptr` arguments.)
   - **Miri FFI ABI-mismatch rejection (`support/probe_results.json:526-530`):** Attempting to declare an `extern "C"` boundary passing `NonZeroU32` where the callee expects `Unalign<NonZeroU32>` fails `Miri` immediately:
     `Undefined Behavior: calling a function whose parameter #1 has type zerocopy::Unalign<std::num::NonZero<u32>> passing argument of type std::num::NonZero<u32>` (`help: this means these two types are not *guaranteed* to be ABI-compatible across all targets`).

Even though `Unalign<NonZeroU32>` still forbids `0` bits at the Rust validity level (as `Unalign<T>` docs promise identical bit validity to `T`), omitting `noundef` and `range(i32 1, 0)` in LLVM IR is a **sound conservative over-approximation** whenever `Unalign<T>` is passed by value in `PassMode::Cast`: LLVM never treats an integer cast argument as UB on the basis of missing scalar attributes, whereas cross-target struct/scalar ABI mismatch makes direct C-FFI substitution with `T` unsound.

---

### 6. The `extern "Rust"` Wrapper Gaps: Slice-Length Range Bypass & Small-Aggregate Cast Promotion

`Basis: source + execution (rust-lang/rust@14210df0e:compiler/rustc_codegen_llvm/src/abi.rs:546-581, compiler/rustc_target/src/callconv/mod.rs:795-816; support/probe_results.json:139-150,425-443)`

Empirically comparing `extern "C"` against `extern "Rust"` exposes **two asymmetric compiler rules** that violate naive "wrapping is completely invisible in IR" assumptions:

1. **`#[repr(transparent)]` Around `&[T]` Under `extern "Rust"` Loses Slice-Length `range` (`compiler/rustc_codegen_llvm/src/abi.rs:546-575` in `14210df0e`, lines `762-785` in `20fe935d5`):**
   Because computing `scalar_b`'s slice-length range during layout risks query cycles, `rustc_codegen_llvm` injects the upper bound (`0..=isize::MAX / elem_size.bytes()`) ad hoc inside `PassMode::Pair` codegen **only** when matching the outermost `ty::Ty`:
   ```rust
   let scalar_b = if let rustc_abi::Primitive::Int(int, false) = primitive_b
       && let ty::Ref(_, pointee_ty, _) = *arg.layout.ty.kind()
       && let ty::Slice(element_ty) = *pointee_ty.kind()
       && let elem_size = cx.layout_of(element_ty).size
       && elem_size != rustc_abi::Size::ZERO
   ```
   Once `&[u32]` is wrapped in `#[repr(transparent)] struct WrapSlice<'a>(&'a [u32], PhantomData<u8>)`, `univariant` preserves `BackendRepr::ScalarPair` and `PassMode::Pair` (`ptr` + `i64`), **but `*arg.layout.ty.kind()` is now `ty::Adt` instead of `ty::Ref`**! Live LLVM IR (`support/probe_results.json:139-150`) confirms:
   - `bare_slice_len_rust`: `define noundef range(i64 0, 2305843009213693952) i64 @bare_slice_len_rust(..., i64 noundef returned range(i64 0, 2305843009213693952) %s.1)`
   - `wrap_slice_len_rust`: `define noundef i64 @wrap_slice_len_rust(..., i64 noundef returned %s.1)`
   Notice `wrap_slice_len_rust` retains `noundef`, `noalias`, `nonnull`, `readonly`, `align 4`, `captures(none)` on `%s.0` and `noundef` on `%s.1`, while losing `range(i64 0, 2305843009213693952)` on `%s.1` and the return value. Under `extern "C"`, SysV `x86_64` classifies the 16-byte `ScalarPair` as an aggregate into `PassMode::Cast` `{ i64, i64 }` for **both** `bare_slice_len` and `wrap_slice_len` (`@wrap_slice_len = unnamed_addr alias i64 ({ i64, i64 }), ptr @bare_slice_len`).

2. **`extern "Rust"` Restores `noundef` (Still Omitting `range`) on Small `#[repr(C, packed)]` `Unalign<T>` (`compiler/rustc_target/src/callconv/mod.rs:796-816` in `14210df0e`):**
   In `FnAbi::adjust_for_rust_abi`:
   ```rust
   BackendRepr::Memory { .. } => {
       let size = arg.layout.size;
       if arg.layout.is_sized() && size <= Primitive::Pointer(AddressSpace::ZERO).size(cx) {
           let attr = if layout_is_noundef(arg.layout, cx) {
               ArgAttribute::NoUndef
           } else {
               ArgAttribute::default()
           };
           arg.cast_to_with_attrs(Reg { kind: RegKind::Integer, size }, attr.into());
       }
   }
   ```
   Because `Unalign<NonZeroU32>` has `size == 4 <= 8` (`ptr_size`) and `allFieldsNoUndef == true` (`layout_is_noundef`), `extern "Rust"` emits:
   - `zc_rust_unalign_nz`: `define noundef i32 @zc_rust_unalign_nz(i32 noundef returned %0)` — **aliased directly to `@zc_readonly_u32`** under `MergeFunctions` (`support/probe_results.json:431-442`)!
   Unlike `x86_64::compute_abi_info` (`callconv/x86_64.rs:245-247`), which calls bare `arg.cast_to(...)` without `layout_is_noundef`, `extern "Rust"` propagates `noundef` onto small aggregates, yet still omits `range(i32 1, 0)` because `rustc_codegen_llvm/src/abi.rs` only calls `apply_range_attr` on `PassMode::Direct` and `PassMode::Pair`, never `PassMode::Cast` (`abi.rs:509-511, 576-581`).

---

### 7. Cross-Target Divergence Across `x86_64`, `AArch64`, and `i686`

`Basis: source + execution (support/probe_results.json:219-318,444-514)`

Live cross-compilation across `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, and `i686-unknown-linux-gnu` (`-Copt-level=2 -Zmerge-functions=disabled --emit=llvm-ir`) reveals why `#[repr(C)]` (`ReprCNz`, `Unalign<NonZeroU32>`) cannot safely substitute for `#[repr(transparent)]` (`WrapNz`, `ReadOnly<NonZeroU32>`):

| Function / Type (`extern "C"`, `-O2`) | `x86_64-unknown-linux-gnu` | `aarch64-unknown-linux-gnu` | `i686-unknown-linux-gnu` |
| :--- | :--- | :--- | :--- |
| **`bare_nz` / `wrap_nz` / `md_nz` / `zc_readonly_nz`** | `define noundef range(i32 1, 0) i32 @...(i32 noundef returned range(i32 1, 0) %x)` | `define noundef range(i32 1, 0) i32 @...(i32 noundef returned range(i32 1, 0) %x)` | `define noundef range(i32 1, 0) i32 @...(i32 noundef returned range(i32 1, 0) %x)` |
| **`mu_nz`** (`MaybeUninit<NonZeroU32>`) | `define i32 @mu_nz(i32 returned %x)` | `define i32 @mu_nz(i32 returned %x)` | `define i32 @mu_nz(i32 returned %x)` |
| **`wrap_bool`** (`#[repr(transparent)]` `bool`) | `define noundef zeroext i1 @wrap_bool(i1 noundef returned zeroext %x)` | `define noundef zeroext i1 @wrap_bool(i1 noundef returned zeroext %x)` | `define noundef zeroext i1 @wrap_bool(i1 noundef returned zeroext %x)` |
| **`repr_c_nz` / `zc_unalign_nz`** | `define i32 @...(i32 returned %0)` (`PassMode::Cast` 32-bit, no `noundef`, no non-zero range) | `define range(i64 0, 4294967296) i64 @...(i64 %0)` (`PassMode::Cast` widened to `i64` zero-ext hull via `and i64 %0, 4294967295`; **0 allowed**, **no `noundef`**, **no `>= 1` bound**) | `define void @...(ptr dead_on_unwind noalias noundef writable writeonly sret([4 x i8]) align 1/4 ... %_0, ptr noalias noundef readonly byval([4 x i8]) align 4 ... %x)` (**`PassMode::Indirect`!**) |
| **`zc_unalign_u8_nz`** (`Unalign<NonZeroU8>`) | `define i8 @zc_unalign_u8_nz(i8 returned %0)` | `define range(i64 0, 256) i64 @zc_unalign_u8_nz(i64 %0)` | `define void @zc_unalign_u8_nz(ptr ... sret([1 x i8]) align 1 ... %_0, ptr ... byval([1 x i8]) align 4 ... %x)` |
| **`zc_unalign_ref`** (`Unalign<&u32>`) | `define i64 @zc_unalign_ref(i64 returned %0)` | `define i64 @zc_unalign_ref(i64 returned %0)` | `define void @zc_unalign_ref(ptr ... sret([4 x i8]) align 1 ... %_0, ptr ... byval([4 x i8]) align 4 ... %x)` |

Three critical insights emerge from this table:
1. **Bit-identical cross-target invariance for `#[repr(transparent)]`:** Across all three architectures (`x86_64`, `aarch64`, `i686`), `bare_nz`, `wrap_nz`, `md_nz`, `zc_readonly_nz`, `wrap_bool`, and `wrap_ref` emit identical `PassMode::Direct` LLVM IR (`define noundef range(i32 1, 0) i32`, `define noundef zeroext i1`, `define noundef nonnull align 4 ptr`).
2. **Catastrophic calling-convention divergence for `#[repr(C)]` and `Unalign<T>`:** On 32-bit `i686` SysV, C structs — even 1-byte `Unalign<NonZeroU8>` and 4-byte `ReprCNz` / `Unalign<NonZeroU32>` — do **not** return in `%eax`; they allocate a hidden `sret` return pointer as `%arg0` and receive the argument `byval`, completely corrupting stack frames/registers if called via an FFI declaration typed `extern "C" fn(NonZeroU32) -> NonZeroU32`!
3. **`i686` `sret` alignment reflects `unadjusted_abi_align` (`align 4` on `repr_c_nz` vs. `align 1` on `zc_unalign_nz`), while `byval` stays `align 4`:** Observed directly at `probe_results.json:298` vs. `490`! In `i686`, `zc_unalign_nz` sets `sret([4 x i8]) align 1` (due to `packed` lowering struct alignment to 1) while SysV x86 stack-slot promotion sets `byval([4 x i8]) align 4`.

---

### 8. Live Native & Miri Semantics, Negative Controls, and Compiler Rejections

`Basis: execution (support/probe_repr_transparent_ffi_abi.py, support/probe_results.json:320-369,516-531)`

Both native compiled release binaries (`rustc --edition=2024 -Copt-level=2`) and `Miri 0.1.0` confirm runtime semantics cleanly:

1. **Positive Cross-Type FFI Roundtrips (`returncode: 0` in both native `-O2` and `Miri 0.1.0`):**
   - Experiment A (`probe_results.json:332-347`): calling `bare_u32_id` via `WrapU32`, `bare_nz_id` via `WrapNz`, `wrap_nz_id` via `NonZeroU32`, `md_nz_id` via `NonZeroU32`, `wrap_bool_id` via `bool`, `wrap_ref_id` via `&STATIC_VAL`, plus passing `MaybeUninit<NonZeroU32>::uninit()`, `::zeroed()`, and `MaybeUninit<&'static u32>::zeroed()` outputs **`WRAP_U32=99 VIA_BARE=7 VIA_WRAP=42 MD=5 BOOL=true REF=123 MU_INIT=11 MU_SIZE=4`**.
   - Experiment B (`probe_results.json:516-525`): calling `zc_readonly_nz` via both `ReadOnly<NonZeroU32>` and cross-typed `NonZeroU32` alongside `Unalign<NonZeroU32>` outputs **`RO_SIZE=4 RO_ALIGN=4 RO_VAL=77 RO_VIA_BARE=91 UA_SIZE=4 UA_ALIGN=1 UA_VAL=88`**.
2. **Miri Negative Controls (`returncode: 1`, immediate UB):**
   - `ub_manually_drop_nonzero_uninit`: `let bad: ManuallyDrop<NonZeroU32> = unsafe { MaybeUninit::uninit().assume_init() };` fails with `Undefined Behavior: reading memory at alloc156[0x0..0x4], but memory is uninitialized` (alongside compiler lint `std::mem::ManuallyDrop<std::num::NonZero<u32>> does not permit being left uninitialized`).
   - `ub_wrap_nz_zero`: `transmute::<u32, WrapNz>(0)` fails with `Undefined Behavior: constructing invalid value of type WrapNz: at .1.0.0, encountered 0, but expected something greater or equal to 1`.
   - `ub_maybe_uninit_assume_init_zero`: Passing `MaybeUninit::<NonZeroU32>::zeroed()` through `extern "C" fn mu_nz` succeeds, and UB triggers **only at** `passed.assume_init()`: `Undefined Behavior: constructing invalid value of type std::num::NonZero<u32>: at .0.0, encountered 0`.
   - `ub_repr_c_nz_abi_mismatch`: Calling `extern "C" fn bare_nz(NonZeroU32)` with `ReprCNz` triggers `Undefined Behavior: calling a function whose parameter #1 has type std::num::NonZero<u32> passing argument of type ReprCNz`.
   - `miri_unalign_as_bare_nz_mismatch`: Calling `extern "C" fn zc_unalign_nz(Unalign<NonZeroU32>)` with `NonZeroU32` triggers `Undefined Behavior: calling a function whose parameter #1 has type zerocopy::Unalign<std::num::NonZero<u32>> passing argument of type std::num::NonZero<u32>`.
3. **`rustc` Frontend `#[repr(transparent)]` Rejection Checks (`returncode: 1`):**
   - `#[repr(transparent)] pub struct BadTransparent([u32; 0], NonZeroU32);` fails with **`error[E0690]`**: `transparent struct needs at most one field with non-trivial size or alignment, but has 2` (`[u32; 0]` has size `0` yet alignment `4`, so it is NOT a 1-ZST).
   - `#[repr(transparent, C)] pub struct BadReprCombo(u32);` fails with **`error[E0692]`**: `transparent struct cannot have other repr hints`.

---

### 9. Verification Tooling Applicability: Anneal `Trusted/MirSemantics` Boundary

`Basis: source + derived (joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613:trusted/lean/Trusted/MirSemantics.lean:717-753)`

In `joshlf/anneal` (`trusted/lean/Trusted/MirSemantics.lean:721-724`), the Lean MIR interpreter's supported local/scalar boundary is currently:
```lean
noncomputable def isSupportedScalarOrUnitTy : MirTy → Bool
  | .bool | .int _ _ | .unit | .never => true
  | .enum ety => enumAdmitted ety
  | _ => false
```
At present, Anneal's MIR formalization verifies Rust functions whose parameters/locals are primitives (`.bool`, `.int _ _`), `.unit`, `.never`, or admitted fieldless enums, and has not yet modeled `extern "C"` FFI `FnAbi` wrappers, `#[repr(transparent)]` newtypes over `NonZero<T>` / `&T`, `ManuallyDrop<T>` / `MaybeUninit<T>`, or `zerocopy::ReadOnly<T>` / `zerocopy::Unalign<T>`.

The findings in this report establish three exact invariants for extending verified-Rust IR/ABI semantics and zero-cost `zerocopy` proofs:
1. **`#[repr(transparent)]` Wrapper Unwrapping (`WrapNz`, `ReadOnly<T>`):** Structurally stripping arbitrary 1-ZST fields from a `#[repr(transparent)]` ADT and substituting the single non-1-ZST field preserves both value validity and `extern "C"` LLVM attributes (`noundef`, `range`, `zeroext`, `nonnull`, `align`, `noalias`, `readonly`, `dereferenceable`), EXCEPT when lowering `&[T]` in `extern "Rust"` (`PassMode::Pair` slice-length range bypass).
2. **Union / `MaybeUninit<T>` Lowering Rule:** Lowering `MaybeUninit<T>` **must** map `Scalar::Initialized` $\mapsto$ `Scalar::Union` (stripping `noundef`, `range`, `nonnull`, `align`, `noalias`, `readonly`, `dereferenceable`), matching `layout_of_union` and avoiding spurious LLVM UB assumptions on partially uninitialized memory or FFI buffers.
3. **`Unalign<T>` (`#[repr(C, packed)]`) Rule:** Despite `Unalign<T>` sharing bit-validity with `T`, FFI ABI compatibility rules **must not** equate `Unalign<T>` with `T` across `extern "C"` call boundaries (due to `ReprFlags::IS_C` inhibiting scalar unboxing and causing cross-target `Cast` / `Indirect` divergence), whereas `zerocopy::ReadOnly<T>` **is** an exact transparent ABI substitute for `T`.

---

### 10. Kernel-Checked `Lean v4.34.1` Formalization of ABI & Attribute Soundness

`Basis: derived + execution (leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52; support/AbiReprTransparentFfiAttributeInheritanceSoundness.lean)`

[`support/AbiReprTransparentFfiAttributeInheritanceSoundness.lean`](support/AbiReprTransparentFfiAttributeInheritanceSoundness.lean) (`2,323` lines, standalone `Init`-only module inside `namespace AbiReprTransparentSoundness`) formalizes the full `rustc` layout $\to$ `PassMode` $\to$ `ArgAttributes` $\to$ `LlvmParamIR` pipeline across `TargetArch` (`x86_64`, `aarch64`, `i686`), `CallingConv` (`externC`, `externRust`), and `optLevel` (`-O0` vs. `-O2`), together with runtime scalar/pointer validity (`rustValidVal`) and LLVM IR parameter UB semantics (`llvmAttrSatisfied`, `AbiAttrSound`).

**Purity and Kernel Verification Receipts:**
- Compiled via `anneal-lean-run --mode file` with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`: **exit code `0`**, `0` warnings, `0` errors.
- Syntax/token audit: **`95` explicit `noncomputable def` declarations**, `0` plain recursive `def`, `0` `noncomputable section`, `0` `deriving` clauses, **`114` explicit `theorem` declarations**, `0` `sorry`, `0` `Classical`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial`, `0` `unsafe`, `0` `axiom`.
- Lean MetaM kernel inspection (`env.constants` and `Lean.collectAxioms` across all `283` theorem constants under `AbiReprTransparentSoundness`): **`unsafe_rec=0`, `classical=0`, `sorry=0`, `reduce_bool=0`, `bad_axioms=#[]`** (every theorem depends at most on `propext` and `Quot.sound`).

**Four Core Mechanized Theorem Families:**

1. **`#[repr(transparent)]` Exact ABI & Attribute Isomorphism & Slice Bypass (Theorem Family 1):**
   - `reprTransparent_passMode_eq` & `reprTransparent_exact_abi_attr_isomorphism`: For any prefix/suffix list of 1-ZST fields (`zpre zsuf`) and any `inner`, `transparentStruct zpre inner zsuf` preserves `size`, `align`, `unadjustedAbiAlign`, `repr`, `pointee`, `computePassMode`, and under `.externC` emits **bit-for-bit equal** `LlvmParamIR` (`noundef`, `rangeAttr`, `zeroExt`, `signExt`, `nonNull`, `alignAttr`, `dereferenceableAttr`, `noAliasAttr`, `readOnlyAttr`) across all architectures (`x86_64`, `aarch64`, `i686`) and opt-levels.
   - `reprTransparent_llvm_ir_eq_of_scalar`, `readOnly_exact_abi_attr_isomorphism`, & `nested_transparent_isomorphism_externC`: Extend exact equality to any `CallingConv` when `inner` lowers to `BackendRepr.scalar`, to `zerocopy::ReadOnly`, and to arbitrarily nested transparent wrappers.
   - `transparent_wrap_slice_ref_loses_ad_hoc_range`: Mechanizes the empirical `extern "Rust"` slice bug/gap (`sliceIr.sliceLengthRange = some (IntWidth.modulus .i64)` vs. `wrapIr.sliceLengthRange = none` while `wrapIr.noUndef = sliceIr.noUndef`).
   - `manuallyDrop_preserves_scalar_value_attrs`: Proves `ManuallyDrop<T>` (`MaybeDangling<T>`) preserves `carrier`, `passedDirect`, `noUndef`, `zeroExt`, `signExt`, `nonNull`, `rangeAttr`, and `alignAttr`, while forcing `dereferenceableAttr = none`, `noAliasAttr = false`, and `readOnlyAttr = false`.
2. **`MaybeUninit<T>` Union Attribute-Erasure Soundness & Necessity (Theorem Family 2):**
   - `maybeUninit_strips_attributes_preserves_direct_scalar`: Proves `MaybeUninit<T>` retains `passedDirect = true` and `carrier = scalarToLlvmCarrier p`, while erasing `noUndef = false`, `nonNull = false`, `rangeAttr = none`, `alignAttr = none`, `dereferenceableAttr = none`, `noAliasAttr = false`, and `readOnlyAttr = false`.
   - `maybeUninit_int_or_ptr_sound_for_all_values` & `maybeUninit_pointer_sound_for_all_values`: Prove `AbiAttrSound` holds universally across **all** `RuntimeScalar` values (`.uninit`, `.bits 0`, null pointers, arbitrary bits) for `MaybeUninit` over $\ge 32$-bit integers and pointers.
   - `maybeUninit_retaining_noundef_is_unsound` & `maybeUninit_retaining_range_is_unsound`: Negative countermodel theorems proving that retaining **either** `noUndef = true` (refuted by `.uninit`) **or** `rangeAttr = some (nonZero ...)` (refuted by `.bits 0`) violates `AbiAttrSound`, producing immediate LLVM IR UB.
3. **`zerocopy::Unalign<T>` (`#[repr(C, packed)]`) Conservative Stripping & Divergence (Theorem Family 3):**
   - `readonly_vs_unalign_x86_64_divergence`, `externRust_vs_externC_unalign_nz`, `unalign_u8_inhibit_newtype_abi`, & `readonly_vs_unalign_cross_target_divergence`: Formally witness `ReadOnly<NonZeroU32>` vs. `Unalign<NonZeroU32>` divergence (`Direct` vs. `Cast` on `x86_64`, `i64` widening on `aarch64`, `Indirect` on `i686`, `extern "Rust"` `noundef` restoration without `range`, and 1-aligned `Unalign<NonZeroU8>` still blocking `Scalar` forwarding via `ReprFlags.IS_C`).
   - `unalign_conservative_stripping_sound` & `scalar_llvm_attrs_sound`: Prove `AbiAttrSound` holds both for `Unalign<T>` (via omitted attributes cleanly over-approximating `rustValidVal`) and for all primitive scalars (`bool`, `int`, `pointer`, `float32`, `float64`) lifted cleanly across `transparent_preserves_soundness` and `readOnly_preserves_soundness`.
4. **FFI Cross-Language Substitution & Lattice Monotonicity (Theorem Families 4, Sections 7–8):**
   - `ffi_transparent_substitution_interchangeable`, `ffi_readOnly_substitution_interchangeable`, & `ffi_manuallyDrop_nonzero_interchangeable`: Prove symmetric `FfiBoundaryCompatible` interchangeability across `extern "C"` for arbitrary transparent wrappers, `zerocopy::ReadOnly`, and `ManuallyDrop<NonZeroU32>`.
   - `ffi_maybeUninit_not_compatible_with_nonzero`, `ffi_unalign_not_compatible_with_nonzero`, & `ffi_reprC_not_compatible_with_nonzero`: Prove strict FFI incompatibility between `NonZeroU32` and all three attribute/ABI-breaking wrappers.
   - `ref_wrapper_lattice_chain`, `nonzero_wrapper_lattice_chain`, `llvmAttrSatisfied_monotone_under_weaker`, `witness_o0_suppresses_opt_attrs_retains_abi_attrs`, & `opt_level_monotonicity`: Mechanize the partial order `LlvmParamIR.WeakerThan` (`MaybeUninit<&u32> ⊑ ManuallyDrop<&u32> ⊑ ReadOnly<&u32> = WrapRef = &u32`, and `-O0 ⊑ -O2` where `-O0` drops `NoUndef`/`NonNull`/`Range`/`Dereferenceable` while keeping `zeroext`/`align`), proving preservation of satisfaction downward along `WeakerThan`.

---

## Boundaries

Explicit accounting of negative space across this investigation:

1. **Multi-Field Aggregates, Floating-Point Subtypes, and `#[repr(simd)]` (`not examined` / `known not to apply`):**
   - This investigation focused on single-non-1-ZST `#[repr(transparent)]` scalars/references, `&[u32]` (`ScalarPair`), single-field `#[repr(C)]`/`#[repr(C, packed)]` wrappers, and `MaybeUninit`/`ManuallyDrop` unions/structs. Multi-field `#[repr(C)]` structs (`(u32, u32)`), SIMD vector wrappers (`#[repr(simd)]`, which also set `ABI_UNOPTIMIZABLE` in `rustc_abi/src/lib.rs:102`), custom `enum` transparent wrappers, and Rust `extern "C-unwind"` / Windows `win64` vectorcall / macOS Darwin calling conventions were **`not examined`**.
   - Additionally, `#[repr(transparent)]` on multi-non-ZST structs or with aligned ZSTs such as `[u32; 0]` (`align = 4`) is **`known not to apply`** and is statically rejected by `rustc` (`E0690`, verified empirically; combinability with `C` is rejected via `E0692`).
2. **Unsized DST `#[repr(transparent)]` Wrappers Across `extern "C"` (`unsupported`):**
   - While `zerocopy::ReadOnly<T>` supports `T: ?Sized` (such as `ReadOnly<[u8]>` or `ReadOnly<str>`) for Rust references and slices (`src/wrappers.rs:627`), passing an unsized `ReadOnly<[u8]>` directly by value in `extern "C"` is **`unsupported`** in Rust (unsized values cannot be passed by value in `extern "C"`). Even behind `&ReadOnly<[u32]>`, `rustc_codegen_llvm/src/abi.rs:553-554` requires both `ty::Ref` and `*pointee_ty.kind() == ty::Slice(_)`; because `*pointee_ty.kind()` is `ty::Adt`, `&ReadOnly<[u32]>` hits the exact same `ty::Adt` slice-length `range` bypass as `WrapSlice` (`derived` from `abi.rs:553-554`, `&ReadOnly<[u32]>` parameter IR itself `not examined`).
3. **Custom User `#[repr(transparent)] union` Types (`unsupported` on Stable Rust):**
   - `core::mem::MaybeUninit<T>` uses unstable internal attributes/tracking issue `rust-lang/rust#60405` (`maybe_uninit.rs:240-241`). Stable user code cannot define `#[repr(transparent)] union` types without nightly `#![feature(transparent_unions)]` (`unsupported` on stable Rust).
4. **Upstream `google/zerocopy` Allocator-API / Unchecked CFGs (`not examined`):**
   - Compiling `zerocopy v0.8.64` cleanly as a standalone library under `rustc 1.98.0-nightly` passed `--cfg no_zerocopy_allocator_api_1_100_0` with `--edition=2021`. Optional Cargo features (`alloc`, `std`, `simd`, `derive`) do not alter the `#[repr(transparent)]` / `#[repr(C, packed)]` layout attributes of `ReadOnly<T>` (`src/wrappers.rs:626-631`) or `Unalign<T>` (`src/wrappers.rs:117-118`), though downstream feature-gated traits and SIMD types were **`not examined`**.
5. **`-O0` MemorySanitizer (`-Zsanitizer=memory`) Exception (`unknown` empirically, `source`-inspected only):**
   - Source inspection of `compiler/rustc_codegen_llvm/src/abi.rs:97-104` shows `-Zsanitizer=memory` re-enables `NoUndef` at `-O0`. That sanitizer flag combination was **not executed** empirically (`not examined` by execution).
6. **Lean Formalization Scope (`known not to apply` beyond modeled fragment):**
   - `AbiReprTransparentFfiAttributeInheritanceSoundness.lean` formalizes single-non-1-ZST transparent wrappers, single-field C/packed structs, `MaybeDangling`/`ManuallyDrop`, `MaybeUninit`, `Unalign`, scalars, and slice `ScalarPair` across `x86_64`, `aarch64`, and `i686` SysV/AAPCS64. Full Rust MIR operational semantics, LLVM instruction-level IR passes (such as GVN/InstCombine), and `byval`/indirect memory aliasing across stack allocas are **beyond its abstraction boundary** (`unknown` / not modeled inside the standalone ABI soundness model).

---

## Evidence

All primary sources, executable artifacts, and formal verification outputs are preserved with exact coordinates below:

### 1. Package Support Artifacts

1. **Live Multi-Target Probe Script:** [`support/probe_repr_transparent_ffi_abi.py`](support/probe_repr_transparent_ffi_abi.py)
   - Runs strictly inside `tempfile.TemporaryDirectory()`, scrubs all host paths, and exercises:
     - Experiment A (`probe_a`): `x86_64`, `aarch64`, `i686` LLVM IR (`-O2 -Zmerge-functions=disabled`), default `-O2` `MergeFunctions` aliases, `-O0` gate IR, `E0690`/`E0692` negative compiler checks, native execution, `Miri 0.1.0` positive roundtrips, and 4 Miri UB negative controls.
     - Experiment B (`probe_b`): Compiles real `zerocopy v0.8.64` (`google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0`) as an `.rlib`, emits host & cross-target LLVM IR (`extern "C"` and `extern "Rust"`) plus `-O2` aliases for `ReadOnly<T>` and `Unalign<T>`, runs native roundtrip checks, runs `Miri 0.1.0` positive `ReadOnly` substitution, and verifies Miri UB rejection on `Unalign<NonZeroU32>` vs. `NonZeroU32`.
2. **Captured Empirical Output Receipt:** [`support/probe_results.json`](support/probe_results.json) (observed `2026-11-23`, `30,076` bytes).
   - Toolchains captured verbatim: `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`LLVM version: 22.1.6`) and `miri 0.1.0 (14210df0e2 2026-05-31)`.
   - Native & Miri outputs captured verbatim:
     - `WRAP_U32=99 VIA_BARE=7 VIA_WRAP=42 MD=5 BOOL=true REF=123 MU_INIT=11 MU_SIZE=4`
     - `RO_SIZE=4 RO_ALIGN=4 RO_VAL=77 RO_VIA_BARE=91 UA_SIZE=4 UA_ALIGN=1 UA_VAL=88`
     - All 5 Miri negative controls and both `rustc` negative compile checks exited with `returncode: 1` and exact expected error diagnostics.
3. **Standalone Kernel-Checked Lean v4.34.1 Formalization:** [`support/AbiReprTransparentFfiAttributeInheritanceSoundness.lean`](support/AbiReprTransparentFfiAttributeInheritanceSoundness.lean) (`2,323` lines, `95` `noncomputable def`s, `114` explicit `theorem`s, `0` `sorry`, `0` `Classical.choice`, `0` `._unsafe_rec`, `0` warnings under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`).

### 2. Primary Source & Specification Coordinates

- **`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, executed & audited):**
  - `compiler/rustc_abi/src/lib.rs:82-104, 213-215, 1563-1639` (`ReprFlags`, `inhibit_newtype_abi_optimization`, `Scalar::{is_bool, primitive, to_union, valid_range, is_always_valid, is_uninit_valid}`)
  - `compiler/rustc_abi/src/layout.rs:420-518, 1277-1430` (`layout_of_union`, `univariant`)
  - `compiler/rustc_ty_utils/src/abi.rs:322-410, 615-644` (`arg_attrs_for_rust_scalar`, `fn_abi_adjust_for_abi`)
  - `compiler/rustc_middle/src/ty/layout.rs:1061-1073` (`ty_and_layout_pointee_info_at` `MaybeDangling` handling)
  - `compiler/rustc_target/src/callconv/mod.rs:795-817` (`adjust_for_rust_abi` small-aggregate `Cast` with `NoUndef`)
  - `compiler/rustc_target/src/callconv/x86_64.rs:178-265` (`compute_abi_info` calling `cast_to` vs. `extend_integer_width_to`)
  - `compiler/rustc_codegen_llvm/src/abi.rs:38-107, 465-583` (`ABI_AFFECTING_ATTRIBUTES`, `OPTIMIZATION_ATTRIBUTES`, `get_attrs`, `apply_range_attr`, `PassMode::{Direct, Pair, Cast, Indirect}`)
  - `library/core/src/mem/manually_drop.rs:156-163` (`ManuallyDrop` holding `value: MaybeDangling<T>`)
- **`rust-lang/rust@20fe935d50367c0ff8872c2ebfa050c5c99d9201` (`main` upstream source audit):**
  - `compiler/rustc_abi/src/lib.rs:1619-1695` (`Primitive::Bool`, `Scalar::is_bool`)
  - `compiler/rustc_abi/src/layout.rs:405-495, 829-941` (`layout_of_union`, `univariant`, `repr_c`)
  - `compiler/rustc_ty_utils/src/abi.rs:318-365` (`arg_attrs_for_rust_scalar`)
  - `compiler/rustc_middle/src/ty/layout.rs:1244-1256` (`is_like_maybe_dangling`)
  - `compiler/rustc_target/src/callconv/mod.rs:559-595` (`extend_integer_width_to`, `cast_to_maybe_noundef`)
  - `compiler/rustc_target/src/callconv/x86_64.rs:302-315` (`compute_abi_info` bool return zero-extension)
  - `compiler/rustc_codegen_llvm/src/abi.rs:45-90, 681-785` (`NoFree`, `apply_range_attr`, `Pair`, `Cast`)
  - `library/core/src/mem/manually_drop.rs:151-158`, `library/core/src/mem/maybe_uninit.rs:214-246, 351-358`, `library/core/src/num/nonzero.rs:108-112`
- **`rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da` (historical layout/ABI reference anchor):**
  - `compiler/rustc_abi/src/layout.rs:1317-1415`, `compiler/rustc_ty_utils/src/abi.rs:322-365`, `compiler/rustc_codegen_llvm/src/abi.rs:472-488`
- **`google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0` (`0.8.64`) & `google/zerocopy@617bb7bbdca0134bf2a9b79b89b7e991e133275b` (`main`):**
  - `zerocopy/src/wrappers.rs:95-119, 608-670` (`Unalign`, `ReadOnly`, byte-identical across both commits)
- **`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`:**
  - `src/type-layout.md:632-697` (`r[layout.repr.alignment]`, `r[layout.repr.transparent]`)
- **`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:**
  - `trusted/lean/Trusted/MirSemantics.lean:717-753` (`isSupportedScalarOrUnitTy`, `liveUninitSlot`)
- **`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):**
  - Standalone kernel verification of `support/AbiReprTransparentFfiAttributeInheritanceSoundness.lean`.

---

## Revalidation

To revalidate any claim in this report on a newer `rustc`, `Miri`, `zerocopy`, or `Lean` toolchain without repeating the full audit:

1. **Re-run the Live Multi-Target `rustc` + `Miri` + `zerocopy` Probe:**
   ```bash
   python3 support/probe_repr_transparent_ffi_abi.py \
     --zerocopy-dir /path/to/zerocopy/zerocopy \
     --output /tmp/revalidated_probe_results.json
   ```
   Diff `/tmp/revalidated_probe_results.json` against `support/probe_results.json`:
   - Confirm `wrap_nz` and `zc_readonly_nz` still match `bare_nz` (`noundef range(i32 1, 0) i32`), `wrap_bool` still emits `noundef zeroext i1`, and `wrap_ref` still emits `nonnull align 4 ... dereferenceable(4)`.
   - Check whether `wrap_slice_len_rust` begins inheriting `range(i64 0, ...)` (if `compiler/rustc_codegen_llvm/src/abi.rs` fixes its `ty::Adt` slice check or layout sets `scalar_b.valid_range`), or whether `md_ref` / `-O0` `NoUndef` gating changes (`OPTIMIZATION_ATTRIBUTES` vs. `ABI_AFFECTING_ATTRIBUTES`).
   - Confirm all 5 Miri UB negative controls (`ub_*`, `miri_unalign_as_bare_nz_mismatch`) still abort with `returncode == 1` while `ReadOnly<NonZeroU32>` substitution continues passing `Miri`.

2. **Diff Upstream Source Decision Points (`rust-lang/rust` and `google/zerocopy`):**
   - Inspect `compiler/rustc_abi/src/layout.rs` (`layout_of_union` around `to_union()`, `univariant` around `inhibit_newtype_abi_optimization()`), `compiler/rustc_ty_utils/src/abi.rs` (`arg_attrs_for_rust_scalar`), `compiler/rustc_middle/src/ty/layout.rs` (`is_like_maybe_dangling` / `PointeeInfo`), `compiler/rustc_codegen_llvm/src/abi.rs` (`OPTIMIZATION_ATTRIBUTES`, `apply_range_attr`, `PassMode::Pair`, `PassMode::Cast`), and `zerocopy/src/wrappers.rs` (`Unalign`, `ReadOnly`).
   - Any change to `ReprFlags::ABI_UNOPTIMIZABLE` (for instance, allowing `#[repr(C)]` single-field `Scalar` unpacking, or conversely blocking transparent `ScalarPair` forwarding) directly invalidates the corresponding branch in Findings §§1, 5, and 7.

3. **Re-Verify the Standalone Lean Kernel Proof & Purity Invariants:**
   ```bash
   LEAN_SYSROOT=/path/to/lean-v4.34.1 \
     lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/AbiReprTransparentFfiAttributeInheritanceSoundness.lean
   ```
   Verify exit code `0`, `0` occurrences of `sorry`, `Classical`, `omega`, `bv_decide`, `native_decide`, `partial`, `deriving`, and verify via MetaM (`env.constants` + `Lean.collectAxioms`) that all declarations have `0` `._unsafe_rec` helpers and depend strictly on `{propext, Quot.sound}`.
