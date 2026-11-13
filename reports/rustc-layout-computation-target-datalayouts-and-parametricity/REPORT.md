# `rustc_abi` Layout Computation, Eight-Target `TargetDataLayout` Matrix, and Layout-Parametric MIR Reasoning at Rust 1.99.1

## Summary

Determining which layout invariants a verified compiler backend or MIR program
logic can treat layout-parametrically—and which require concrete target and
`rustc_abi` layout facts—requires pinning both the exact layout algorithm in
**Rust 1.99.1** (`rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67`,
`compiler/rustc_abi/src/{lib.rs,layout.rs}` and
`compiler/rustc_ty_utils/src/{layout.rs,layout/invariant.rs}`) and the concrete
`TargetDataLayout` parameters across all eight Tier 1 targets:

1. **Exact `rustc_abi` layout algorithm and `BackendRepr` promotion conditions:**
   - **Struct field reordering and niche bias (`univariant_biased`,
     `compiler/rustc_abi/src/layout.rs:L1081-L1425`):** For `repr(Rust)` structs
     and enum variants (`!repr.inhibit_struct_field_reordering()`), fields
     (excluding any unsizable tail field so `&Struct<Sized>` and
     `&Struct<dyn Trait>` share identical prefix offsets; `L1099-L1133`) are
     sorted by descending `alignment_group_key` (`log2(align.max(size))` capped
     by `max_field_align` when niches exist), then by largest available niche
     (`NicheBias::Start` for structs, `NicheBias::End` for prefixed enum
     variants), and finally by inner niche offset (`L1193-L1233`). When
     `-Zrandomize-layout` is active (`L1116-L1130`), `rustc_abi` (compiled with
     `default = ["nightly", "randomize"]` in `compiler/rustc_abi/Cargo.toml:L21`)
     shuffles fields using `Xoshiro128StarStar` seeded from
     `field_seed.wrapping_add(repr.field_shuffle_seed)`, which can increase a
     struct's total size (for example, `ReprRustStruct { a: u8, b: u32, c: u16, d: u8 }`
     grows from `8 B` to `12 B` under `-Zlayout-seed=2` and `-Zlayout-seed=3`).
   - **Newtype and two-field `BackendRepr::Scalar` / `ScalarPair` promotion
     (`layout.rs:L1323-L1415`):** A sized struct or single-variant enum with
     *one* non-ZST field at offset `0` promotes to `BackendRepr::Scalar` (or
     `SimdVector`) only when `align == field.align.abi && size == field.size`
     and `!repr.inhibit_newtype_abi_optimization()` (`L1335-L1343`; `ScalarPair`
     promotes even under `#[repr(C)]`, `L1346`). Thus an over-aligned ZST field
     (`NewtypeWithAlign8Zst { zst: Align8Zst, inner: u32 }`) forces
     `align = 8 != 4` and demotes the struct to `BackendRepr::Memory { sized: true }`
     (`size = 8 B`), whereas `#[repr(transparent)]` rejects over-aligned ZST
     fields outright with `E0690`.
   - **Enum niche filling vs. direct tag promotion (`layout_of_enum`,
     `layout.rs:L576-L1079`):** For multi-variant enums without
     `repr(C)`/`repr(int)`, `calculate_niche_filling_layout` (`L594-L753`) finds
     `largest_variant_index` and attempts to reserve `count` consecutive values
     from its `largest_niche` (`Niche::reserve` in
     `compiler/rustc_abi/src/lib.rs:L2062-L2096`, which wraps around `0`, e.g.,
     giving `Option<Option<bool>>` a wrapping `valid_range = 255..=2`). It
     chooses `TagEncoding::Niche` over `TagEncoding::Direct` if and only if
     the niche layout is strictly smaller (`nl.size < tl.size`) or equal in size
     with a strictly larger remaining niche (`L1060-L1076`).
   - **Union `Scalar(Union)` promotion (`layout_of_union`,
     `layout.rs:L395-L520`):** A union promotes to `BackendRepr::Scalar(Scalar::Union)`
     or `ScalarPair` if and only if `!repr.inhibits_union_abi_opt()` (not
     `#[repr(C)]`), `align == repr.scalar_platform_align(dl)`, and **all
     non-ZST fields have the exact same `field.backend_repr.to_union()`**
     (`L438-L443`). Because `Primitive::Int(I32, false) != Primitive::Int(I32, true)`,
     `SameSignScalarUnion { a: u32, b: NonZeroU32 }` gets
     `BackendRepr::Scalar(Union(u32))`, whereas `ScalarUnion { a: u32, b: NonZeroU32, c: i32 }`
     (mixing `u32` and `i32`) triggers `AbiMismatch` and falls back to
     `BackendRepr::Memory { sized: true }`!
2. **Eight-target `TargetDataLayout` matrix (`support/tier1_layout_goldens.json`):**
   Across all eight Tier 1 targets in `rustc 1.99.1`, `i128`/`u128` and `f128`
   uniformly have **`16`-byte (`128`-bit) ABI alignment** (`i128:128` in every
   Tier 1 data-layout string), whereas `i64`/`u64` and `f64` have **`4`-byte ABI
   alignment on `i686-unknown-linux-gnu`** (`f64:32:64`, so `(u8, i64)` and
   `(u8, f64)` have size `12 B`, align `4 B`, field offset `4 B`) versus
   **`8`-byte ABI alignment on `i686-pc-windows-msvc`** and all six 64-bit Tier 1
   targets (where `(u8, i64)` and `(u8, f64)` have size `16 B`, align `8 B`,
   field offset `8 B`).
3. **Well-formedness conditions (`layout_sanity_check`) and the exact boundary
   of layout-parametric MIR reasoning:**
   A MIR operational semantics and functional translation can remain
   **layout-parametric** (abstracting over concrete byte sizes, alignments, and
   field offsets) for typed place projections (`Field`, `Deref`, `Index`,
   `Downcast`), aggregate construction, and `size_of`/`align_of` queries **if
   and only if** every type layout satisfies `rustc_ty_utils::layout::invariant::layout_sanity_check`
   (`size % align == 0`, `size <= isize::MAX`, disjoint non-ZST field footprints
   within `[0..size]`, and `TagEncoding` injectivity) **and** the program does
   not perform byte-representation reinterpretation (`CastKind::Transmute`,
   raw-pointer byte-offset casting, union cross-field reads, or C/platform ABI
   register marshaling via `BackendRepr`).

## Applicability

These findings apply to **Rust 1.99.1** (`rust-lang/rust`
`58cf8f9c35b355199727627d07ae34a4e2846d67`), **The Rust Reference**
(`rust-lang/reference` `bcd62f35e8bf480ec5b0fa569b6d12ea5924030c`), the **Unsafe
Code Guidelines** (`rust-lang/unsafe-code-guidelines`
`d809f91e62968913d808e53397fbcf7cea762cce`), and **Anneal** (`joshlf/anneal` at
`a7ac073219f4ec3c813431be8239a0405014d5c1` and
`a4e9b0b39e44ee2c7dcd9b2ae9e3e9cd59613ac7`) across all eight Tier 1 targets.

## Findings

### 1. Complete Tier 1 `TargetDataLayout` Matrix at Rust 1.99.1

Basis: source + execution (`support/s10_layout_extractor.rs`,
`support/tier1_layout_goldens.json`)

Table 1 records the exact LLVM `data_layout` string and parsed `TargetDataLayout`
parameters extracted from `tcx.data_layout` in `rustc 1.99.1` across all eight
Tier 1 targets.

| Tier 1 Target Triple | Endian | Ptr Size / Align | `i8` / `i16` / `i32` Align | **`i64` / `f64` ABI Align** | **`i128` / `f128` ABI Align** | `obj_size_bound` (`isize::MAX + 1`) | LLVM `data_layout` String in `rustc 1.99.1` |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :--- |
| `x86_64-unknown-linux-gnu` | Little | `64b` / `8B` | `1B` / `2B` / `4B` | **`8B` / `8B`** | **`16B` / `16B`** | $2^{63}\text{ B}$ | `e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128` |
| `aarch64-unknown-linux-gnu` | Little | `64b` / `8B` | `1B` / `2B` / `4B` | **`8B` / `8B`** | **`16B` / `16B`** | $2^{63}\text{ B}$ | `e-m:e-p270:32:32-p271:32:32-p272:64:64-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32` |
| `i686-unknown-linux-gnu` | Little | `32b` / `4B` | `1B` / `2B` / `4B` | **`4B` / `4B`** | **`16B` / `16B`** | $2^{31}\text{ B}$ | `e-m:e-p:32:32-p270:32:32-p271:32:32-p272:64:64-i128:128-f64:32:64-f80:32-n8:16:32-S128` |
| `aarch64-apple-darwin` | Little | `64b` / `8B` | `1B` / `2B` / `4B` | **`8B` / `8B`** | **`16B` / `16B`** | $2^{63}\text{ B}$ | `e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32` |
| `x86_64-pc-windows-msvc` | Little | `64b` / `8B` | `1B` / `2B` / `4B` | **`8B` / `8B`** | **`16B` / `16B`** | $2^{63}\text{ B}$ | `e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128` |
| `x86_64-pc-windows-gnu` | Little | `64b` / `8B` | `1B` / `2B` / `4B` | **`8B` / `8B`** | **`16B` / `16B`** | $2^{63}\text{ B}$ | `e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128` |
| `aarch64-pc-windows-msvc` | Little | `64b` / `8B` | `1B` / `2B` / `4B` | **`8B` / `8B`** | **`16B` / `16B`** | $2^{63}\text{ B}$ | `e-m:w-p270:32:32-p271:32:32-p272:64:64-p:64:64-i32:32-i64:64-i128:128-n32:64-S128-Fn32` |
| `i686-pc-windows-msvc` | Little | `32b` / `4B` | `1B` / `2B` / `4B` | **`8B` / `8B`** | **`16B` / `16B`** | $2^{31}\text{ B}$ | `e-m:x-p:32:32-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32-a:0:32-S32` |

---

### 2. Golden Layout Matrix Across Probe Types, Niche Encodings, and `-Zrandomize-layout`

Basis: execution (`support/s10_probe_types.rs`, `support/tier1_layout_goldens.json`)

Table 2 summarizes the computed `LayoutData` across representative types from
 the `50`-field `ProbeCatalog` in `support/tier1_layout_goldens.json`.

| Probe Type | `64`-Bit Targets (`x86_64` / `aarch64`) | `i686-unknown-linux-gnu` | `i686-pc-windows-msvc` | `BackendRepr` & Field / Tag Encoding |
| :--- | :--- | :--- | :--- | :--- |
| `ReprRustStruct { a: u8, b: u32, c: u16, d: u8 }` | `8B` / align `4B` (`offsets=[6, 0, 4, 7]`) | `8B` / align `4B` (`offsets=[6, 0, 4, 7]`) | `8B` / align `4B` (`offsets=[6, 0, 4, 7]`) | `Memory(sized=true)`; under `-Zrandomize-layout -Zlayout-seed=2`, becomes **`12B`** (`offsets=[8, 4, 0, 9]`). |
| `ReprCStruct { a: u8, b: u32, c: u16, d: u8 }` | `12B` / align `4B` (`offsets=[0, 4, 8, 10]`) | `12B` / align `4B` (`offsets=[0, 4, 8, 10]`) | `12B` / align `4B` (`offsets=[0, 4, 8, 10]`) | `Memory(sized=true)`, `mem_order=[0, 1, 2, 3]`. |
| `ReprPacked2Struct { a: u8, b: u32, c: u16 }` | `8B` / align `2B` (`unadjusted_align=2B`) | `8B` / align `2B` | `8B` / align `2B` | `Memory(sized=true)`, `offsets=[0, 2, 6]`. |
| `ReprAlign16Struct { a: u32 }` | `16B` / align `16B` (`unadjusted_align=4B`) | `16B` / align `16B` (`unadjusted_align=4B`) | `16B` / align `16B` (`unadjusted_align=4B`) | `Memory(sized=true)` (because `align 16 != field.align 4`, `Scalar` promotion is inhibited). |
| `TransparentWith1Zst { zst: (), inner: NonZeroU32 }` | `4B` / align `4B` | `4B` / align `4B` | `4B` / align `4B` | `Scalar(Initialized(u32, 1..=4294967295))`, `niche=0..=0`. |
| `NewtypeWithAlign8Zst { zst: Align8Zst, inner: u32 }` | `8B` / align `8B` | `8B` / align `8B` | `8B` / align `8B` | `Memory(sized=true)` (`align 8 != field.align 4` disables newtype `Scalar` ABI). |
| `I64AlignProbe { tag: u8, val: i64 }` (`#[repr(C)]`) | `16B` / align `8B` (`offsets=[0, 8]`) | **`12B` / align `4B` (`offsets=[0, 4]`)** | **`16B` / align `8B` (`offsets=[0, 8]`)** | `ScalarPair(u8, i64, offset=8B)` (`offset=4B` on `i686-linux`). |
| `F64AlignProbe { tag: u8, val: f64 }` (`#[repr(C)]`) | `16B` / align `8B` (`offsets=[0, 8]`) | **`12B` / align `4B` (`offsets=[0, 4]`)** | **`16B` / align `8B` (`offsets=[0, 8]`)** | `ScalarPair(u8, f64, offset=8B)` (`offset=4B` on `i686-linux`). |
| `I128AlignProbe { tag: u8, val: i128 }` (`#[repr(C)]`) | `32B` / align `16B` (`offsets=[0, 16]`) | `32B` / align `16B` (`offsets=[0, 16]`) | `32B` / align `16B` (`offsets=[0, 16]`) | `ScalarPair(u8, i128, offset=16B)` across all 8 Tier 1 targets. |
| `Option<Option<bool>>` | `1B` / align `1B` | `1B` / align `1B` | `1B` / align `1B` | `Scalar(Initialized(u8, 255..=2))`, `Niche(untagged=1, range=0..=0, start=255)`. |
| `NicheCharEnum { V1(char), V2, V3 }` | `4B` / align `4B` | `4B` / align `4B` | `4B` / align `4B` | `Scalar(Initialized(u32, 0..=1114113))`, `Niche(untagged=0, range=1..=2, start=1114112)`. |
| `NicheEnum { V1(NonZeroU32), V2, V3 }` | `8B` / align `4B` | `8B` / align `4B` | `8B` / align `4B` | `ScalarPair(Initialized(u32, 0..=2), Union(u32), offset=4B)`, `TagEncoding::Direct` (1 niche in `NonZeroU32` cannot fit 2 tagless variants). |
| `SameSignScalarUnion { a: u32, b: NonZeroU32 }` | `4B` / align `4B` | `4B` / align `4B` | `4B` / align `4B` | **`Scalar(Union(u32))`** (both fields have `to_union() == Union(u32)`). |
| `ScalarUnion { a: u32, b: NonZeroU32, c: i32 }` | `4B` / align `4B` | `4B` / align `4B` | `4B` / align `4B` | **`Memory(sized=true)`** (`u32` vs. `i32` signedness mismatch in `to_union()` triggers `AbiMismatch`). |

---

### 3. Well-Formedness Conditions for Layout-Parametric Reasoning vs. Concrete Layout Dependencies

Basis: source (`compiler/rustc_ty_utils/src/layout/invariant.rs:L9-L366`,
`joshlf/anneal` `a7ac073219f4ec3c813431be8239a0405014d5c1`
`trusted/lean/Trusted/MirSemantics.lean:L322-L525`) + derived

1. **Sufficient well-formedness axioms for layout-parametric MIR reasoning:**
   A MIR semantics or functional translation can treat layout abstractly as an
   uninterpreted (or partially specified) function
   $\mathcal{L} : \text{Ty} \to \text{Layout}$ when the program is restricted to
   typed lens operations (`ProjectionElem::{Field, Deref, Index, ConstantIndex,
   Subslice, Downcast}`, `Rvalue::{Aggregate, Repeat, Discriminant}`,
   `StatementKind::SetDiscriminant`, and `size_of`/`align_of`), provided
   $\mathcal{L}$ satisfies the five invariants enforced by
   `layout_sanity_check` (`invariant.rs:L9-L366`):
   - **Alignment divisibility and positive power-of-two alignment:**
     $\text{align}(T) = 2^k \ge 1$ and $\text{size}(T) \bmod \text{align}(T) = 0$
     (`invariant.rs:L12-L14`).
   - **`isize::MAX` object size bound:**
     $\text{size}(T) < \text{obj\_size\_bound} = 2^{\text{ptr\_bits} - 1}$
     ($\le \texttt{isize::MAX}$, `invariant.rs:L15-L17`; modeled in Anneal
     `MirSemantics.lean:L326` as `ValidTySizes` / `LocalLayoutsAdmitted`).
   - **Pairwise disjoint in-bounds field footprints for structs and enum
     variants:** For every non-union variant $v$ and distinct non-ZST fields
     $i \ne j$ of $v$,
     $[\text{offset}_v(i), \text{offset}_v(i) + \text{size}(T_i)) \cap [\text{offset}_v(j), \text{offset}_v(j) + \text{size}(T_j)) = \emptyset$
     and $\text{offset}_v(i) + \text{size}(T_i) \le \text{size}(T)$
     (`invariant.rs:L325-L332`). This guarantees the lens laws (`get-put`,
     `put-get`, `put-put`, and frame disjointness across sibling fields)
     independently of field reordering or `-Zrandomize-layout`.
   - **Tag-encoding injectivity and disjointness from active variant fields:**
     For `Variants::Multiple`, reading the tag after
     `SetDiscriminant(place, v)` when variant $v$'s fields hold valid values of
     their respective types (`valid_range` for `TagEncoding::Niche`) uniquely
     recovers $v$, and writing a valid value to any field of $v$ preserves the
     tag of $v$.
   - **Uninhabitedness coherence:** If $T$ is uninhabited (`Variants::Empty` or
     contains an uninhabited field), no valid runtime value of type $T$ exists
     (`invariant.rs:L31-L46, L288-L290`).

2. **Where layout-parametricity breaks and concrete layout facts are required:**
   Table 3 classifies the exact MIR and backend operations that **cannot** keep
   $\mathcal{L}(T)$ abstract.

| Operation / Compiler Pass | Concrete Layout Facts Required | Why Layout-Parametric Reasoning Cannot Abstract It |
| :--- | :--- | :--- |
| `CastKind::Transmute` / `transmute_copy` | Exact `size`, field `offsets`, `in_memory_order`, endianness, `TagEncoding`, and `valid_range` | Reinterprets raw bytes across distinct types; depends on concrete byte offsets and padding placement. |
| Raw pointer byte arithmetic (`ptr.byte_add(k)`, `*const Struct as *const u8`) | Exact field `offsets` and `align` | Maps integer byte offset $k$ back to a specific struct field or padding range. |
| Union cross-field reads (`u.b` after writing `u.a`) | Exact `size`, `BackendRepr::to_union()`, and byte overlap | Reading a different union field reinterprets the shared byte range `[0..size]`. |
| LLVM `!range`, `!nonnull`, `!align`, `!noundef` metadata & `assume_scalar_range` | Exact `BackendRepr::Scalar` / `ScalarPair`, `Scalar::valid_range`, and `PointeeInfo` | Codegen emits `!range` and `@llvm.assume` iff `backend_repr` is `Scalar` or `ScalarPair` with a non-full `valid_range`. |
| Function call ABI lowering (`FnAbi::of_instance`) | `BackendRepr` (`Scalar`, `ScalarPair`, `SimdVector`, `Memory`), `unadjusted_abi_align`, `max_repr_align`, field types | Register vs. stack passing (`PassMode::Direct`, `Pair`, `Cast`, `Indirect`) depends on `BackendRepr` and `unadjusted_abi_align` (e.g., x86_64 eightbyte classification and i686 `i64`/`f64` alignment). |
| `SwitchInt` on niche-encoded `Rvalue::Discriminant` | `TagEncoding::Niche { untagged_variant, niche_variants, niche_start }` and `tag` scalar | Codegen lowers `Rvalue::Discriminant` on a niche enum to a range test `wrapping_sub(tag_val, niche_start) <= niche_count` selecting either the computed variant index or `untagged_variant` (`operand.rs:L640-L715`). |

## Boundaries

- **Scalable vectors (`BackendRepr::SimdScalableVector`, SVE) (`not examined`
  empirically):** Present in `rustc_abi` (`layout.rs:L204-L221`), but requires
  target features (`+sve`) outside baseline Tier 1 target specs.

## Evidence

- **Primary upstream sources:**
  - `rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`:
    - `compiler/rustc_abi/src/lib.rs:L154-L2421` (`ReprOptions`,
      `TargetDataLayout`, `Scalar`, `FieldsShape`, `BackendRepr`, `Variants`,
      `TagEncoding`, `Niche`, `LayoutData`).
    - `compiler/rustc_abi/src/layout.rs:L172-L1525` (`LayoutCalculator`,
      `layout_of_union`, `layout_of_struct`, `layout_of_enum`,
      `univariant_biased`).
    - `compiler/rustc_ty_utils/src/layout/invariant.rs:L9-L366`
      (`layout_sanity_check` and `check_layout_abi`).
  - `joshlf/anneal` @ `a7ac073219f4ec3c813431be8239a0405014d5c1`
    (`trusted/lean/Trusted/MirSemantics.lean:L322-L525`) and
    `a4e9b0b39e44ee2c7dcd9b2ae9e3e9cd59613ac7`
    (`trusted/lean/Trusted/Rustc/V2026_08_01/Layout.lean`).
- **Preserved support artifacts:**
  - [`support/tier1_layout_goldens.json`](support/tier1_layout_goldens.json)
  - [`support/s10_layout_extractor.rs`](support/s10_layout_extractor.rs)
  - [`support/s10_probe_types.rs`](support/s10_probe_types.rs)

## Revalidation

To regenerate and verify the 8-target layout goldens and `-Zrandomize-layout`
probe outputs:

```bash
SYSROOT=$(rustc +1.99.1-x86_64-unknown-linux-gnu --print sysroot)
RUSTC_BOOTSTRAP=1 rustc +1.99.1-x86_64-unknown-linux-gnu -O \
  reports/rustc-layout-computation-target-datalayouts-and-parametricity/support/s10_layout_extractor.rs \
  -C link-args="-Wl,-rpath,$SYSROOT/lib" -o /tmp/s10_layout_extractor
for target in x86_64-unknown-linux-gnu aarch64-unknown-linux-gnu i686-unknown-linux-gnu \
  aarch64-apple-darwin x86_64-pc-windows-msvc x86_64-pc-windows-gnu \
  aarch64-pc-windows-msvc i686-pc-windows-msvc; do
  RUSTC_BOOTSTRAP=1 /tmp/s10_layout_extractor --layout-label "$target" \
    --layout-out "/tmp/layout_${target}.json" --crate-type lib --edition 2021 \
    -A warnings --target "$target" \
    reports/rustc-layout-computation-target-datalayouts-and-parametricity/support/s10_probe_types.rs
done
```
