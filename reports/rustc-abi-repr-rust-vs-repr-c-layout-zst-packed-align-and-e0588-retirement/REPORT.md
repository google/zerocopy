# `rustc_abi` Struct Layout (`#[repr(Rust)]` vs. `#[repr(C)]`), ZST Alignment Propagation, `#[repr(packed)]` / `#[repr(align)]` / `#[repr(transparent)]`, and `E0588` Retirement

## Summary

In `rustc`, every sized or unsizable struct flows through `LayoutCalculator::layout_of_struct` -> `layout_of_univariant` -> `layout_of_univariant_biased` in `compiler/rustc_abi/src/layout.rs`, yet tiny differences in `ReprOptions` bitflags, `alignment_group_key`, zero-sized type (ZST) alignment propagation, and HIR attribute validation separate layout-guaranteed `#[repr(C)]` types from reordered or randomized `#[repr(Rust)]` types. Combining primary-source inspection across `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` at `1.98.0-nightly`, `49d734536222bf28bb6d07d885b3a81d145981da` at `2026-09-11`, `4e99638c7fb697db838c38669709c01bb7cc799a` at `2026-09-14`, and `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` at `1.102.0-nightly`), live `rustc` execution on `x86_64-unknown-linux-gnu` captured in [`support/probe_results.json`](support/probe_results.json), downstream audits of `google/zerocopy` (`e8dcb7f08edbc19485c9e7980333607ebbff5f48` and `99238c633f747763a6ce9d403ab0007ddca72751`) and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), and a constructive kernel-checked Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) formalization in [`support/AbiReprLayoutZstPackedTransparentSoundness.lean`](support/AbiReprLayoutZstPackedTransparentSoundness.lean) (`1,994` lines, `249` theorems, zero `sorry` placeholders, zero `Classical.choice`, zero `omega`/`bv_decide`/`native_decide`/`._unsafe_rec`), this report establishes six core results:

1. **`#[repr(Rust)]` Field Reordering vs. `#[repr(C)]` Declaration Order and `-Zrandomize-layout`.** `ReprOptions::inhibit_struct_field_reordering()` tests `ReprFlags::FIELD_ORDER_UNOPTIMIZABLE | (int.is_some())`, which includes `IS_C`, `IS_SIMD`, `IS_SCALABLE`, and `IS_LINEAR`—and deliberately **excludes** `IS_TRANSPARENT`. When field reordering is permitted (`#[repr(Rust)]`, `#[repr(packed)]`, `#[repr(packed(N))]`, `#[repr(align(N))]`, and `#[repr(transparent)]`), `layout_of_univariant_biased` either shuffles non-tail fields with `Xoshiro128StarStar` under `-Zrandomize-layout` or sorts deterministically by `cmp::Reverse(alignment_group_key(f))` (where `alignment_group_key` uses `align.max(size).trailing_zeros()` when unpacked and `layout.align.min(pack).bytes()` when packed). On `(u8, u64, u8, u16)` in `x86_64-unknown-linux-gnu`, `#[repr(Rust)]` compacts the struct to `16` bytes (`align=8`, offsets `(a:10, b:0, c:11, d:8)`), whereas `#[repr(C)]` retains declaration order at `24` bytes (`align=8`, offsets `(a:0, b:8, c:16, d:18)`). Under `-Zrandomize-layout` (seeds `1`, `42`, `99`), `#[repr(Rust)]` inflates to `24` bytes, `#[repr(packed)]` shuffles field offsets while keeping `size=12, align=1`, `#[repr(packed(2))]` shuffles across `size=12` and `size=14` (`align=2`), and `#[repr(C)]` / `#[repr(C, align(16))]` / `#[repr(C, packed)]` / `#[repr(C, packed(2))]` remain completely invariant.
2. **ZST Alignment Propagation Without Byte Consumption (`is_1zst()` vs. `is_zst()`).** Zero-sized fields occupy `0` bytes of `offset += field.size` cursor advancement yet participate unconditionally in `offset = offset.align_to(field_align)` and `align = align.max(field_align)`. Under `#[repr(C)]`, placing `Align16Zst([u128; 0])` between two `u8` fields (`ReprCZstMid`) inserts `15` bytes of inter-field padding before `.z` and `15` bytes of tail padding (`size=32, align=16, offsets=(a:0, z:16, b:16)`), whereas placing it at the end (`ReprCZstEnd`) collapses to `16` bytes (`offsets=(a:0, b:1, z:16)`). Under `#[repr(Rust)]`, `alignment_group_key` moves all align-16 ZSTs ahead of `[a, b]` to offset `0` (`ReprRustZst`: `size=16, offsets=(a:0, z:0, b:1)`), while leaving a `1-ZST` such as `()` at the tail (`ReprRustMixedZsts`: `offsets=(a:0, z1:0, b:1, z2:2)`). Pure-ZST structs remain `size=0` even under `-Zrandomize-layout` while preserving `align = max(field.align)`.
3. **`#[repr(packed(N))]` / `#[repr(align(N))]` Arithmetic and `E0587`/`E0634`.** Both compiler eras reject conflicting `#[repr(packed(2), packed(4))]` (`E0634`) and `#[repr(packed, align(8))]` on the same type (`E0587`). When valid, `pack` clamps every field's effective alignment via `field_align = min(field.align, pack)` **inside** the placement loop (`layout.rs:780`), whereas `repr.align` applies **only after** field placement via `align = align.max(repr_align)` (`layout.rs:810-811`), leaving `unadjusted_abi_align` (`layout.rs:809`) reflecting `pack` without `repr.align`. We mechanize in Lean 4 that whenever `fields` and `pack` have power-of-two alignments, tightening `pack1 <= pack2` monotonically decreases both aggregate alignment and padded struct size (`packed_monotone_compression`), while `pack >= max(field.align)` is an exact no-op (`packed_ge_all_fields_noop`).
4. **Retirement of `E0588` in `4e99638c7fb697db838c38669709c01bb7cc799a` (`2026-09-14`) and Cross-Version Divergence.** Prior to commit `4e99638c7fb697db838c38669709c01bb7cc799a`—both in `rustc 1.98.0-nightly` (`14210df0e`) and `49d734536` (`2026-09-11`)—`check_packed_inner` rejected **any** non-generic `#[repr(packed)]` struct or union transitively containing a `#[repr(align(N))]` `ty::Adt` field with hard error `E0588`. Starting at `4e99638c7fb697db838c38669709c01bb7cc799a` and present in `rustc 1.102.0-nightly` (`3ef0c22cd`), `E0588` is retired (`"no longer emitted"`): `#[repr(packed)] struct Bad(Aligned8)` compiles silently to `size=8, align=1`, and only `#[repr(C, packed)]` wrapping a `#[repr(C, align(N))]` field emits the deny-by-default lint `aligned_fields_in_packed` (because GCC vs. MSVC C-ABI compatibility diverges). Furthermore, across **both** eras, `check_packed_inner` only matches uninstantiated `ty::Adt`, so generic `#[repr(C, packed)] struct Unalign<T>(T)` instantiated as `Unalign<Aligned8>` compiles cleanly with `size=8, align=1, unadjusted_abi_align=1, max_repr_align=Some(8)`.
5. **`#[repr(transparent)]` Single-Field Non-`1-ZST` Acceptance and `unadjusted_abi_align` Fallback.** Multi-field `#[repr(transparent)]` requires all trivial fields to satisfy `layout.is_1zst()` (`is_sized() && size == 0 && align == 1`) and `is_trivial()` (rejecting `#[repr(C)]` ZSTs and align > 1 ZSTs like `[u32; 0]` via `E0690`). However, `check_transparent` starts with `if variant.fields.len() <= 1 { return; }` (`check.rs:1804-1807`), so single-field `#[repr(transparent)]` over a non-1-aligned ZST (`TransSingleNon1Zst([u32; 0])` or `TransAlign16Zst(Align16Zst)`) compiles cleanly with `align=4` or `16` (contrary to naive reading of the Rust Reference's "or unit otherwise"), and sets `unadjusted_abi_align = align` via the `None => align` branch at `layout.rs:905-911`. Meanwhile, `IS_TRANSPARENT` omits `FIELD_ORDER_UNOPTIMIZABLE`, so `#[repr(transparent)]` structs such as `TransZst(PhantomData<u8>, u64)` still reorder non-ZST ahead of `PhantomData` (`in_memory_order: [1, 0], offsets: [Size(8 bytes), Size(0 bytes)]`) while forwarding `Scalar(I64)` ABI (`inhibit_newtype_abi_optimization() == false`).
6. **Downstream `zerocopy` and `joshlf/anneal` Impact.** `zerocopy::Unalign<T>` (`zerocopy/src/wrappers.rs:117-118`) is `#[repr(C, packed)]` (not `#[repr(transparent)]`, despite an obsolete safety comment inside `Unalign::deref_unchecked` at line `240`) and relies directly on generic `ty::Param` bypass of `check_packed_inner`; `zerocopy::ReadOnly<T>` (`wrappers.rs:626-631`) is `#[repr(transparent)]`; and `DstLayout::for_repr_c_struct` (`zerocopy/src/layout.rs:1153-1197`) matches our mechanized `computeOrderedLayout` on `#[repr(C)]` sized fields (`zcForReprCStruct_eq_computeReprC`). In `joshlf/anneal@c131b320e`, `Trusted.MirAst.MirTy` (`MirAst.lean:312-321`) marks non-fieldless-enum ADTs `.unsupported`, so extending Anneal to verified `#[repr(Rust/C/packed/align/transparent)]` structs requires adding `ReprOptions`, `effFieldAlign`, alignment-only ZST field placement, and opaque field-order permutation invariants to `Trusted.MirAst` and `Trusted.MirSemantics`.

---

## Applicability

This report characterizes nine durable upstream repository revisions and released toolchains pinned in [`REPORT.json`](REPORT.json), distinguishing cross-revision invariants from documented historical transitions:

| Subject | Pinned Immutable Revision | Technical Role in This Report |
| :--- | :--- | :--- |
| `rust-lang/rust` (`1.102.0-nightly`, LLVM `23.1.5`) | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`2026-11-11`) | Authoritative post-`E0588`-retirement primary source across `compiler/rustc_abi/src/{layout.rs, lib.rs}`, `compiler/rustc_middle/src/ty/mod.rs`, `compiler/rustc_attr_parsing/src/attributes/repr.rs`, `compiler/rustc_hir_analysis/src/check/check.rs`, `compiler/rustc_passes/src/{check_attr.rs, diagnostics.rs}`, `compiler/rustc_lint_defs/src/builtin.rs`, and `compiler/rustc_error_codes/src/error_codes/E0588.md`, plus `1.102.0-nightly` compiler execution observations. |
| `rust-lang/rust` (`1.98.0-nightly`, LLVM `22.1.6`) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`2026-05-31`) | Pre-`E0588`-retirement execution toolchain and `rustc-src` tree on `x86_64-unknown-linux-gnu` running all experiments in [`support/probe_repr_layout_zst_packed_align.py`](support/probe_repr_layout_zst_packed_align.py) -> [`support/probe_results.json`](support/probe_results.json). |
| `rust-lang/rust` (`pre-4e99638c7` checkout) | `49d734536222bf28bb6d07d885b3a81d145981da` (`2026-09-11`) | Intermediate baseline documenting `layout_of_univariant_biased` (at lines `1081-1425`) and pre-retirement hard error `E0588` in `check_packed_inner` (`check.rs:1641-1742`). |
| `rust-lang/rust` (`E0588` retirement commit) | `4e99638c7fb697db838c38669709c01bb7cc799a` (`2026-09-14`) | Exact transition commit turning `E0588` into the `#[repr(C)]`-gated `ALIGNED_FIELDS_IN_PACKED` lint (`check.rs`, `E0588.md`, `builtin.rs`). |
| `rust-lang/reference` (`src/type-layout.md`) | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | Normative language reference compared directly against `rustc` implementation and execution behavior (`r[layout.repr.*]`). |
| `google/zerocopy` (`main` + baseline) | `e8dcb7f08edbc19485c9e7980333607ebbff5f48` & `99238c633f747763a6ce9d403ab0007ddca72751` | Downstream customer audited at `zerocopy/src/{wrappers.rs, layout.rs}` (`diff -u` confirms `wrappers.rs` and `layout.rs` are byte-identical across both commits). |
| `joshlf/anneal` (`main`) | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Downstream verification architecture audited at `trusted/lean/Trusted/{MirAst.lean, MirSemantics.lean}`. |
| `leanprover/lean4` (`v4.34.1`) | `5045d0056413266e57c625dcd7c365b10e377c52` | Kernel checker validating [`support/AbiReprLayoutZstPackedTransparentSoundness.lean`](support/AbiReprLayoutZstPackedTransparentSoundness.lean). |

### Cross-Revision Equivalence vs. Version-Specific Behavior

1. **Shared Across All Audited `rustc` Revisions (`14210df0e`, `49d734536`, `3ef0c22cd`):**
   - Struct layout algebra in `LayoutCalculator::{layout_of_univariant, layout_of_univariant_biased}` (`SDefault = 16B`, `SC = 24B`, `SPacked = 12B`, `SPacked2 = 12B`, `SCAlign16 = 32B`), `-Zrandomize-layout` shuffling via `Xoshiro128StarStar` (`SDefault` inflating to `24B` at seeds `1`, `42`, `99`; `SC` / `SCAlign16` remaining invariant), ZST zero-size alignment propagation (`ReprCZstMid = 32B`, `ReprCZstEnd = 16B`, `ReprRustZst = 16B`, `PureZst = 0B align 16`), hard errors `E0587` / `E0634` / `E0692` / `E0690`, single-field `#[repr(transparent)]` acceptance for `[u32; 0]`, and `ty::Param` generic bypass of `check_packed_inner` (`Unalign<Aligned8> = 8B align 1`).
2. **Exact Version-Specific Divergences (`1.98.0-nightly` / `49d734536` vs. `1.102.0-nightly` `3ef0c22cd`):**
   - **Pre-`4e99638c7` (`1.98.0-nightly` `14210df0e` & `49d734536`):** Concrete `#[repr(packed)] struct Bad(Aligned8)` and `#[repr(C, packed)] struct CBad(CAligned8)` both fail compilation with `error[E0588]: packed type cannot transitively contain a #[repr(align)] type`, `#[allow(aligned_fields_in_packed)]` warns `unknown lint`, `rustc --explain E0588` shows the error explanation without retirement notice, and `#[repr(transparent)] struct Bad(u8, CZst)` fails with deny-by-default lint `repr_transparent_non_zst_fields` (`future_incompatible`, issue `#78586`). Additionally, multi-field `E0690` phrasing reads `"transparent struct needs at most one field with non-trivial size or alignment, but has 2"`.
   - **Post-`4e99638c7` (`3ef0c22cd` `1.102.0-nightly`):** `rustc --explain E0588` begins with `"#### Note: this error code is no longer emitted by the compiler."` (`E0588.md:1`), concrete `#[repr(packed)] struct Bad(Aligned8)` compiles with exit status `0` to `size=8 align=1`, `#[repr(C, packed)] struct CBad(CAligned8)` emits deny-by-default lint `ALIGNED_FIELDS_IN_PACKED` (suppressible with `#[allow(aligned_fields_in_packed)]`), `NonTrivialReason::ReprC` reports through the unified `E0690` diagnostic (`check.rs:1852-1907`), and `E0690` wording is shortened to `"transparent struct needs at most one non-trivial field, but has 2"`.
3. **Host and Target Scope:** All live execution measurements target `x86_64-unknown-linux-gnu` (`dl.aggregate_align = 1` byte, `dl.i8_align = 1` byte, `dl.obj_size_bound = 2^61` on 64-bit targets, 64-bit pointers). Notice that `layout.rs` was refactored in line numbering between `49d734536` (where `layout_of_univariant_biased` begins at line `1081`) and `3ef0c22cd` (where `layout_of_univariant_biased` begins at line `590`); all `rustc_abi/src/layout.rs` line citations below explicitly specify the revision when comparing across commits.

---

## Findings

### 1. `layout_of_struct`, `layout_of_univariant_biased`, Field Ordering, and `-Zrandomize-layout`

**Basis:** `normative` (`rust-lang/reference@c9cc32825`) + `source` (`rust-lang/rust@3ef0c22cd`) + `execution` (`rustc 1.98.0-nightly` & `rustc 1.102.0-nightly`) + `derived` (Lean 4)

Every non-enum struct enters `LayoutCalculator::layout_of_struct` (`compiler/rustc_abi/src/layout.rs:540-588` in `3ef0c22cd`), which sets `StructKind::AlwaysSized` when the struct is empty, an enum, or flagged `always_sized`, and `StructKind::MaybeUnsized` otherwise, then delegates to `layout_of_univariant` (`layout.rs:273-341`). `layout_of_univariant` first computes a baseline layout using `NicheBias::Start`, and—except when `kind` is `StructKind::MaybeUnsized` (so `Foo<T>` vs. `Foo<dyn Trait>` unsizing preserves compatible prefix offsets; `layout.rs:292-295`)—retries with `NicheBias::End` when `fields.len() > 1 && head_space != 0 && tail_space > 0`, selecting `alt_layout` if shifting the largest niche brings it closer to either edge of the struct (`layout.rs:296-339`).

Inside `layout_of_univariant_biased` (`compiler/rustc_abi/src/layout.rs:590-935` in `3ef0c22cd`), representation modifiers and reordering rules execute in a strict four-phase sequence:

1. **Initial aggregate alignment & reordering eligibility (`layout.rs:602-616`, `lib.rs:85-110, 228-242`):**
   - `align` starts at `if pack.is_some() { dl.i8_align } else { dl.aggregate_align }` (`1` byte on Linux `x86_64`).
   - For `StructKind::MaybeUnsized`, the last field (`end = fields.len() - 1`) is excluded from reordering and seed accumulation (`layout.rs:608-615`).
   - Reordering occurs iff `!repr.inhibit_struct_field_reordering() && fields.len() > 1`, where:

```rust
// compiler/rustc_abi/src/lib.rs:105-110, 228-242 (3ef0c22cd)
const FIELD_ORDER_UNOPTIMIZABLE = ReprFlags::IS_C.bits()
                         | ReprFlags::IS_SIMD.bits()
                         | ReprFlags::IS_SCALABLE.bits()
                         | ReprFlags::IS_LINEAR.bits();
const ABI_UNOPTIMIZABLE = ReprFlags::IS_C.bits() | ReprFlags::IS_SIMD.bits();

pub fn inhibit_newtype_abi_optimization(&self) -> bool {
    self.flags.intersects(ReprFlags::ABI_UNOPTIMIZABLE)
}
pub fn inhibit_struct_field_reordering(&self) -> bool {
    self.flags.intersects(ReprFlags::FIELD_ORDER_UNOPTIMIZABLE) || self.int.is_some()
}
pub fn can_randomize_type_layout(&self) -> bool {
    !self.inhibit_struct_field_reordering() && self.flags.contains(ReprFlags::RANDOMIZE_LAYOUT)
}
```

   Notice the critical asymmetry in `ReprFlags`: **`IS_TRANSPARENT` is absent from both `FIELD_ORDER_UNOPTIMIZABLE` and `ABI_UNOPTIMIZABLE`**. Consequently, `#[repr(transparent)]` structs allow compiler field reordering (between their sole non-1-ZST field and 1-ZST fields) as well as Scalar/ScalarPair ABI unpacking, whereas `#[repr(C)]` inhibits both.

2. **Randomized shuffling vs. deterministic `alignment_group_key` sorting (`layout.rs:625-747`):**
   - When `repr.can_randomize_type_layout() && cfg!(feature = "randomize")` holds (`-Zrandomize-layout` enabled on the defining crate), `rustc` seeds `rand_xoshiro::Xoshiro128StarStar` with `field_seed.wrapping_add(repr.field_shuffle_seed)` (`layout.rs:632-637`), where `field_shuffle_seed` mixes the crate's `def_path_hash` with `-Zlayout-seed` (`compiler/rustc_middle/src/ty/mod.rs:1643-1650`), and shuffles `optimizing` (non-tail fields).
   - Otherwise, for structs (`StructKind::AlwaysSized | StructKind::MaybeUnsized`), `rustc` sorts `optimizing` stably using `alignment_group_key` (`layout.rs:654-729`):

```rust
// compiler/rustc_abi/src/layout.rs:654-690 (3ef0c22cd)
let alignment_group_key = |layout: &F| {
    if let Some(pack) = pack {
        // Return the packed alignment in bytes.
        layout.align.min(pack).bytes()
    } else {
        let align = layout.align.bytes();
        let size = layout.size.bytes();
        let niche_size = layout.largest_niche.map(|n| n.available(dl)).unwrap_or(0);
        // Group [u8; 4] with align-4 or [u8; 6] with align-2 fields.
        let size_as_align = align.max(size).trailing_zeros();
        let size_as_align = if largest_niche_size > 0 { ... } else { size_as_align };
        size_as_align as u64
    }
};
```

   In normal (unpacked, no-niche) `#[repr(Rust)]` structs, `alignment_group_key` computes `(align.max(size)).trailing_zeros()` and sorts by `cmp::Reverse(...)` (largest alignment/2-adic factor first), placing `u64` (`trailing_zeros(8) = 3`), then `u16` (`trailing_zeros(2) = 1`), then `[u8, u8]` (`trailing_zeros(1) = 0`), while preserving declaration order among ties.

3. **Sequential cursor placement (`layout.rs:764-805`):**
   For each index `i` in `&in_memory_order`:
   - `field_align = if let Some(pack) = pack { field.align.min(pack) } else { field.align }`
   - `offset = offset.align_to(field_align)`
   - `align = align.max(field_align)`
   - `max_repr_align = max_repr_align.max(field.max_repr_align)`
   - `offsets[i] = offset`
   - `offset = offset.checked_add(field.size, dl)?`

4. **Post-placement alignment floor, tail rounding, and ABI unpacking (`layout.rs:809-918`):**
   - `unadjusted_abi_align = align` captures aggregate alignment **after** `pack` clamping and **before** `repr.align`.
   - `if let Some(repr_align) = repr.align { align = align.max(repr_align); }` raises `align` without modifying field offsets, and `size = min_size.align_to(align)` appends tail padding.
   - `optimize_abi = !repr.inhibit_newtype_abi_optimization()` allows single-non-ZST structs (matching size, alignment, and zero offset for that field) to adopt `Scalar` / `SimdVector` under `#[repr(Rust)]` or `#[repr(transparent)]` while forcing `#[repr(C)]` single-scalar newtypes to remain `BackendRepr::Memory { sized: true }` (`layout.rs:841-863`). Note that `ScalarPair` still promotes even when `#[repr(C)]` (`layout.rs:852-853`).
   - Finally, `repr_c = repr.c() || (repr.transparent() && fields.iter().any(|field| field.repr_c))` (`layout.rs:918`).

#### Live Empirical Matrix: `(a: u8, b: u64, c: u8, d: u16)` (`Experiment A`, [`support/probe_results.json`](support/probe_results.json))

| Type & Attributes | Default Run (`rustc 1.98` & `1.102`) | `-Zrandomize-layout -Zlayout-seed=1` (`1.98`) | `-Zrandomize-layout -Zlayout-seed=42` (`1.98`) | `-Zrandomize-layout -Zlayout-seed=99` (`1.98`) | Reorder / Randomize? |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `SDefault` (`#[repr(Rust)]`) | `size=16, align=8`, `(a:10, b:0, c:11, d:8)` | `size=24, align=8`, `(a:0, b:8, c:16, d:2)` | `size=24, align=8`, `(a:1, b:8, c:0, d:16)` | `size=24, align=8`, `(a:18, b:8, c:0, d:16)` | Reordered & Shuffled |
| `SC` (`#[repr(C)]`) | `size=24, align=8`, `(a:0, b:8, c:16, d:18)` | `size=24, align=8`, `(a:0, b:8, c:16, d:18)` | `size=24, align=8`, `(a:0, b:8, c:16, d:18)` | `size=24, align=8`, `(a:0, b:8, c:16, d:18)` | Invariant (`FIELD_ORDER_UNOPTIMIZABLE`) |
| `SPacked` (`#[repr(packed)]`) | `size=12, align=1`, `(a:0, b:1, c:9, d:10)` | `size=12, align=1`, `(a:8, b:0, c:11, d:9)` | `size=12, align=1`, `(a:8, b:0, c:11, d:9)` | `size=12, align=1`, `(a:0, b:3, c:11, d:1)` | **Shuffled!** (`IS_C` absent) |
| `SPacked2` (`#[repr(packed(2))]`) | `size=12, align=2`, `(a:10, b:0, c:11, d:8)` | `size=12, align=2`, `(a:9, b:0, c:8, d:10)` | **`size=14`**, `align=2`, `(a:10, b:2, c:0, d:12)` | **`size=14`**, `align=2`, `(a:10, b:2, c:0, d:12)` | Reordered & Shuffled (`12B` <-> `14B`) |
| `SCAlign16` (`#[repr(C, align(16))]`) | `size=32, align=16`, `(a:0, b:8, c:16, d:18)` | `size=32, align=16`, `(a:0, b:8, c:16, d:18)` | `size=32, align=16`, `(a:0, b:8, c:16, d:18)` | `size=32, align=16`, `(a:0, b:8, c:16, d:18)` | Invariant (`12B` tail pad) |
| `SCPacked` (`#[repr(C, packed)]`) | `size=12, align=1`, `(a:0, b:1, c:9, d:10)` | `size=12, align=1`, `(a:0, b:1, c:9, d:10)` | `size=12, align=1`, `(a:0, b:1, c:9, d:10)` | `size=12, align=1`, `(a:0, b:1, c:9, d:10)` | Invariant |
| `SCPacked2` (`#[repr(C, packed(2))]`) | `size=14, align=2`, `(a:0, b:2, c:10, d:12)` | `size=14, align=2`, `(a:0, b:2, c:10, d:12)` | `size=14, align=2`, `(a:0, b:2, c:10, d:12)` | `size=14, align=2`, `(a:0, b:2, c:10, d:12)` | Invariant (`1B` pad before `b`, `d`) |
| `(u8, u64, u8, u16)` (tuple) | `size=16, align=8`, `(0:8, 1:0, 2:9, 3:10)` | `size=16, align=8`, `(0:8, 1:0, 2:9, 3:10)` | `size=16, align=8`, `(0:8, 1:0, 2:9, 3:10)` | `size=16, align=8`, `(0:8, 1:0, 2:9, 3:10)` | Defined in `core` (not shuffled by bin crate flag) |

Note two high-value subtleties visible in the matrix above:
1. **`#[repr(packed)]` Without `#[repr(C)]` Is Shuffled by `-Zrandomize-layout`:** Because `#[repr(packed)]` alone does not set `IS_C`, `can_randomize_type_layout()` is `true` for `SPacked` and `SPacked2` (on `rustc 1.98.0-nightly`, `SPacked` shifts from `(a:0, b:1, c:9, d:10)` to `(a:8, b:0, c:11, d:9)` under seeds `1` and `42`, and `(a:0, b:3, c:11, d:1)` under seed `99`, while `SPacked2` takes `size=12` at seed `1` and `size=14` at seeds `42, 99`). Even without `-Zrandomize-layout`, `SPacked2` deterministically reorders `[b, d, a, c]` (`12` bytes) because `alignment_group_key` returns `layout.align.min(2) = 2` for `b` and `d` vs. `1` for `a` and `c` (`layout.rs:658-660`). By contrast, `#[repr(C, packed(2))]` (`SCPacked2`) preserves declaration order `[a, b, c, d]`, forcing two `1`-byte internal padding holes (`a:0, pad:1, b:2, c:10, pad:1, d:12`), yielding `size=14`. On `rustc 1.102.0-nightly`, `SPacked` and `SPacked2` also shuffle under `-Zrandomize-layout` (`SPacked2` taking `size=12` at seeds `1, 99` and `size=14` at seed `42` due to per-compiler `def_path_hash` mixing), confirming identical randomization rules.
2. **Tuple `(u8, u64, u8, u16)` Remained Unshuffled:** Anonymous tuples are laid out using `ReprOptions::default()` for tuple types in the current crate when not `RANDOMIZE_LAYOUT`-flagged (`probe_results.json` shows identical offsets `(0:8, 1:0, 2:9, 3:10)` at size `16` across default and seeds `{1, 42, 99}`), though its field ordering `[u64, u8, u8, u16]` already differs from `SDefault`'s `[u64, u16, u8, u8]` due to `alignment_group_key` / niche tie-breaking details and has no stability guarantee across compiler releases.

---

### 2. Zero-Sized Type (ZST) Alignment Propagation and the `is_1zst()` vs. `is_zst()` Split

**Basis:** `source` (`rust-lang/rust@3ef0c22cd`) + `execution` (`probe_results.json`) + `derived` (Lean 4)

`compiler/rustc_abi/src/lib.rs:2396-2425` sharply distinguishes general ZSTs from `1-ZST`s:

```rust
// compiler/rustc_abi/src/lib.rs:2395-2425 (3ef0c22cd)
/// Returns `true` if the type is sized and a 1-ZST (meaning it has size 0 and alignment 1).
pub fn is_1zst(&self) -> bool {
    self.is_sized() && self.size.bytes() == 0 && self.align.bytes() == 1
}

/// Returns `true` if the type is a ZST and not unsized.
///
/// Note that this does *not* imply that the type is irrelevant for layout! It can still have
/// non-trivial alignment constraints. You probably want to use `is_1zst` instead.
pub fn is_zst(&self) -> bool {
    match self.backend_repr {
        BackendRepr::Scalar(_)
        | BackendRepr::ScalarPair { .. }
        | BackendRepr::SimdScalableVector { .. }
        | BackendRepr::SimdVector { .. } => false,
        BackendRepr::Memory { sized } => sized && self.size.bytes() == 0,
    }
}
```

Crucially, the `layout_of_univariant_biased` placement loop (`layout.rs:781-804`) **never special-cases ZSTs**: an aligned ZST advances `offset = offset.align_to(field_align)` and raises `align = align.max(field_align)`, even though `offset + 0 == offset`.

#### Empirical Matrix: ZST Alignment Propagation (`Experiment B`, [`support/probe_results.json`](support/probe_results.json))

| Struct Definition | Observed `size, align` | Observed Offsets & `-Zprint-type-sizes` Decomposition | Mechanism in `layout.rs` |
| :--- | :--- | :--- | :--- |
| `Align16Zst([u128; 0])` & `#[repr(align(16))] Align16ZstAttr` | `size=0, align=16` | `field .0: 0 bytes` | Zero-element `[T; 0]` inherits `T`'s align (`16`) with `size=0`. |
| `OneZstPhantom(PhantomData<u128>)` | `size=0, align=1` | `field .0: 0 bytes` | `PhantomData<T>` is unconditionally a `1-ZST` regardless of `T`'s alignment. |
| `#[repr(C)] ReprCZstMid { a: u8, z: Align16Zst, b: u8 }` | **`size=32`**, `align=16` | `(a:0, z:16, b:16)`: `a(1B) -> pad(15B) -> z(0B @16) -> b(1B @16) -> end_pad(15B)` | Aligning cursor `1` up to `16` inserts `15` bytes of inter-field padding *solely because* `.z` sits at index `1`! |
| `#[repr(C)] ReprCZstEnd { a: u8, b: u8, z: Align16Zst }` | **`size=16`**, `align=16` | `(a:0, b:1, z:16)`: `a(1B) -> b(1B) -> pad(14B) -> z(0B @16)` | Note `.z`'s offset is `16` (`alignUp(2, 16) = 16`, equal to total struct size!). |
| `ReprRustZst { a: u8, z: Align16Zst, b: u8 }` | `size=16, align=16` | `(a:0, z:0, b:1)`: `in_memory_order=[z, a, b] -> end_pad(14B)` | `alignment_group_key(Align16Zst) = (16.max(0)).trailing_zeros() = 4 > 0`, placing `z` at offset `0`. |
| `ReprRustTwoZsts { a: u8, z1: Align16Zst, b: u8, z2: Align16Zst }` | `size=16, align=16` | `(a:0, z1:0, b:1, z2:0)`: `[z1, z2, a, b] -> end_pad(14B)` | Both `Align16Zst` fields sort ahead of `[a, b]` and sit at offset `0`. |
| `ReprRustMixedZsts { a: u8, z1: Align16Zst, b: u8, z2: () }` | `size=16, align=16` | `(a:0, z1:0, b:1, z2:2)`: `[z1, a, b, z2] -> end_pad(14B)` | `z2: ()` has `align=1, size=0` -> `trailing_zeros(1) = 0`, tying `u8` and staying after `[a, b]` at offset `2`. |
| `PureZst { z1: Align16Zst, z2: Align16Zst }` | **`size=0`**, `align=16` | `(z1:0, z2:0)` | Cursor starts at `0`; `align_to(16) = 0`; `0 + 0 = 0`; `align_up(0, 16) = 0`. |
| `Pure1Zst { u: (), p: PhantomData<u64> }` | `size=0, align=1` | `(u:0, p:0)` | Preserved `0B` even under `-Zrandomize-layout` (`lib.rs:96-98`). |

This also resolves an important subtlety when comparing `#[repr(C)]` ZST placement rules: an end-positioned aligned ZST (`ReprCZstEnd`) sits at offset **`16`** (`alignUp(2, 16) == size_of`), which means an offset equal to `size_of::<Struct>()` is well-typed and in-bounds precisely because `field.size == 0` (`offset + 0 <= size`, formalized as `FieldsInBounds` in our Lean proof).

---

### 3. `#[repr(packed(N))]`, `#[repr(align(N))]`, Attribute Checks, and the Retirement of `E0588`

**Basis:** `normative` + `source` (`49d734536`, `4e99638c7`, `3ef0c22cd`) + `execution` (`rustc 1.98` & `1.102`) + `derived` (Lean 4)

#### Attribute Parsing and Same-Type Conflicts

`parse_repr_attr` in `compiler/rustc_attr_parsing/src/attributes/repr.rs:86-144` parses `#[repr(align(N))]` (permitted on `Struct`, `Enum`, `Union`) and `#[repr(packed)]` / `#[repr(packed(N))]` (permitted on `Struct`, `Union`, with bare `packed` defaulting to `ReprPacked(Align::ONE)` at line `110`). Before layout calculation runs, `check_packed` (`compiler/rustc_hir_analysis/src/check/check.rs:1666-1752`) enforces:

- **`E0634` (`check.rs:1680-1695`):** Emitted when multiple `#[repr(packed(...))]` attributes specify distinct alignments (e.g., `#[repr(packed(2), packed(4))]`, `compile_returncode = 1` on both `1.98` and `1.102`).
- **`E0587` (`check.rs:1697-1704`):** Emitted whenever `repr.packed()` and `repr.align.is_some()` coexist on the same type (`#[repr(packed, align(8))]`, `compile_returncode = 1` on both `1.98` and `1.102`).

#### The `E0588` -> `ALIGNED_FIELDS_IN_PACKED` Cross-Version Divergence (`49d734536` / `1.98` vs. `4e99638c7` / `3ef0c22cd`)

Direct primary-source diffing across `49d734536222bf28bb6d07d885b3a81d145981da` (`2026-09-11`), `4e99638c7fb697db838c38669709c01bb7cc799a` (`2026-09-14`, commit title *"turn aligned-in-packed error into lint"*), and `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`2026-11-11`) reveals a breaking diagnostic transition that causes pre-retirement source trees and the Rust Reference (`src/type-layout.md:654`) to disagree with `rustc 1.102.0-nightly`:

1. **Pre-`4e99638c7` (`rustc 1.98.0-nightly` `14210df0e` and `49d734536` `check.rs:1678-1742`):**
   - `check_packed` called `check_packed_inner(tcx, def.did(), &mut vec![])` for **every** packed ADT (`repr(Rust, packed)` and `repr(C, packed)` alike), and `check_packed_inner` inspected uninstantiated `ty::Adt(def, args)` fields without checking `def.repr().c()`, emitting hard error **`E0588`**: `"packed type cannot transitively contain a #[repr(align)] type"`.
   - Crucially, even pre-retirement, `check_packed_inner` matched **only concrete `ty::Adt`** (`check.rs:1729` in `49d734536`), skipping `ty::Param`, tuples, and arrays. Thus `#[repr(C, packed)] struct GenericPacked<T>(T)` instantiated as `GenericPacked<Aligned8>` compiled cleanly even on `1.98.0-nightly` (`size=8, align=1`), whereas direct `#[repr(packed)] struct Bad(Aligned8)` and `#[repr(C, packed)] struct CBad(CAligned8)` failed with `E0588`.
2. **Post-`4e99638c7` (`3ef0c22cd` `1.102.0-nightly`):**
   - `compiler/rustc_error_codes/src/error_codes/E0588.md:1` now begins: `"#### Note: this error code is no longer emitted by the compiler."` (`rustc --explain E0588`).
   - `check_packed` (`check.rs:1705-1750`) gates the check on **`else if repr.c() && let Some(def_spans) = check_packed_inner(...)`** and emits the **deny-by-default lint `ALIGNED_FIELDS_IN_PACKED`** (`rustc_lint_defs/src/builtin.rs:5859-5862`: `` `repr(C, align)` types nested inside `repr(C, packed)` types do not always have a C-compatible layout ``), while `check_packed_inner` (`check.rs:1760`) restricts recursion strictly to `def.repr().c() && (def.is_struct() || def.is_union())`.
   - As `builtin.rs:5854-5858` explains, the sole remaining hazard is C-ABI divergence between GCC (which honors `rustc`'s packing of inner aligned fields) and MSVC (which can honor the inner alignment despite outer packing). For pure `#[repr(packed)]` Rust structs, lowering field alignment via `min(field.align, pack)` is completely well-defined, so `#[repr(packed)] struct Bad(Aligned8)` compiles silently on `rustc 1.102.0-nightly` with `size=8, align=1`.
   - **Normative Lag in `rust-lang/reference@c9cc32825`:** `src/type-layout.md:654` (`r[layout.repr.alignment.constraint-exclusive]`) still states unqualifiedly that *"a `packed` type cannot transitively contain another `align`ed type"*, which disagrees with `rustc 1.102.0-nightly` for non-`repr(C)` packed structs, `#[allow(aligned_fields_in_packed)]` `repr(C, packed)` structs, and generic `ty::Param` instantiations across all revisions.

| Probe Case (`Experiment C`) | `rustc 1.98.0-nightly` (`14210df0e`) | `rustc 1.102.0-nightly` (`3ef0c22cd`) | Upstream Root Mechanism (`3ef0c22cd`) |
| :--- | :--- | :--- | :--- |
| `#[repr(packed, align(8))] struct Bad { x: u32 }` | **Err (`rc=1`) `E0587`** | **Err (`rc=1`) `E0587`** | `check.rs:1697-1704` (`repr.align.is_some()`) |
| `#[repr(packed(2), packed(4))] struct Bad { x: u32 }` | **Err (`rc=1`) `E0634`** | **Err (`rc=1`) `E0634`** | `check.rs:1680-1695` (`pack != &repr_pack`) |
| `#[repr(packed)] struct Bad(Aligned8)` (`#[repr(align(8))]`) | **Err (`rc=1`) `E0588`** | **Ok (`rc=0`) `size=8, align=1`** (no warning!) | `repr.c()` gate in `check.rs:1705, 1760` (`4e99638c7`) |
| `#[repr(C, packed)] struct CBad(CAligned8)` (`#[repr(C, align(8))]`) | **Err (`rc=1`) `E0588`** | **Deny-by-default lint (`aligned_fields_in_packed`)** | `check.rs:1705-1750`, `builtin.rs:5859-5862` |
| `#[allow(aligned_fields_in_packed)] #[repr(C, packed)] struct CBad(CAligned8)` | Warn `unknown lint` + **Err `E0588`** | Allowed when lint suppressed | Post-`4e99638c7` lint registration |
| `#[repr(C, packed)] struct GenericPacked<T>(T)` (`T = Aligned8`) | **Ok (`rc=0`) `size=8, align=1`** | **Ok (`rc=0`) `size=8, align=1`** | `check_packed_inner` skips `ty::Param` (`check.rs:1767`) |

---

### 4. `#[repr(transparent)]` Rules, `is_1zst()`, Single-Field Edge Cases, and `unadjusted_abi_align`

**Basis:** `normative` + `source` (`rust-lang/rust@3ef0c22cd`) + `execution` (`Exp C` & `Exp E`) + `derived` (Lean 4)

Combining `#[repr(transparent)]` with any other representation hint—including `C`, `Rust`, `packed`, `align`, `simd`, `#[repr(<int>)]`, or `#[rustc_pass_indirectly_in_non_rustic_abis]`—triggers **`E0692`** (`"transparent struct cannot have other repr hints"`, `compiler/rustc_passes/src/{check_attr.rs:1047-1064, diagnostics.rs:344-350}`, `rc=1` on both `1.98` and `1.102`).

When `#[repr(transparent)]` appears alone on a single-variant struct or enum, `check_transparent` (`compiler/rustc_hir_analysis/src/check/check.rs:1782-1925`) gates field validity carefully:

1. **Multi-field validation (`variant.fields.len() > 1`, `check.rs:1809-1915`):**
   - Every field is tested for `layout.is_1zst()` (`is_sized() && size == 0 && align == 1`, `check.rs:1873`) AND recursive `is_trivial()` (`check.rs:1829-1861`), which rejects:
     - Generic/unknown layout (`UnknownLayout`)
     - Non-zero size (`NonZeroSized`)
     - ZSTs with `align > 1` such as `[u32; 0]` (`NonTrivialAlignment`) -> **`E0690`** when paired with another non-trivial field (e.g., `(u8, [u32; 0])` fails with `E0690` on both `1.98` and `1.102`).
     - Fields containing external private fields (`PrivateField`), `#[non_exhaustive]` (`NonExhaustive`), or `#[repr(C)]` types (`ReprC { ty }` at `check.rs:1852-1853`, emitted as `deny(repr_transparent_non_zst_fields)` future-incompat error in `1.98` and unified into `E0690` at `3ef0c22cd`).
2. **Single-field bypass (`variant.fields.len() <= 1`, `check.rs:1804-1807`):**

```rust
// compiler/rustc_hir_analysis/src/check/check.rs:1804-1807 (3ef0c22cd)
if variant.fields.len() <= 1 {
    // No need to check when there's at most one field.
    return;
}
```

   Because `check_transparent` exits before checking `is_1zst()` or `is_trivial()` whenever there is at most one field, `#[repr(transparent)] struct TransSingleNon1Zst([u32; 0])` and `#[repr(transparent)] struct TransAlign16Zst(Align16Zst)` **both compile cleanly**!

#### Internal Layout Inspection via `#[rustc_dump_layout(debug)]` (`Experiment E`, `probe_results.json:474-480`)

Dumping the internal `rustc_abi::LayoutData` on `rustc 1.98.0-nightly` exposes three subtle compiler behaviors that are invisible from `size_of` / `align_of` alone:

1. **`TransAlign16Zst(Align16Zst)` sets `unadjusted_abi_align = Align(16)` instead of `1`:** In `layout_of_univariant_biased` (`layout.rs:905-915`):
   - `Align16Zst` (`#[repr(align(16))] struct Align16Zst;`) computes `align = 1` before line `810`, captures `unadjusted_abi_align = 1` (`layout.rs:809`), and then raises `align` to `16`.
   - `TransAlign16Zst(Align16Zst)` has `non_zst_fields` empty (`[z]` filtered by `!f.is_zst()` at `layout.rs:833`), so `layout_of_single_non_zst_field` is `None`. When line `905` executes `if repr.transparent()`, the `None => align` arm (`layout.rs:908-911`) **overwrites** `unadjusted_abi_align` with `align` (`Align(16 bytes)`), directly visible in `Exp E` (`size: Size(0 bytes), align: AbiAlign { abi: Align(16 bytes) }, max_repr_align: Some(Align(16 bytes)), unadjusted_abi_align: Align(16 bytes)`).
   - Likewise, `TransSingleNon1Zst([u32; 0])` yields `size: Size(0 bytes), align: AbiAlign { abi: Align(4 bytes) }, unadjusted_abi_align: Align(4 bytes)`. That refutes a naive reading of `r[layout.repr.transparent.layout-abi]` (`type-layout.md:691`) which says a `transparent` struct with no non-1-ZST field has the layout of `()` (`align = 1`): in reality, a single-field non-1-ZST (`align > 1`, `size = 0`) carries its single field's `align > 1` rather than unit's `align = 1`!
2. **`TransZst(PhantomData<u8>, u64)` reorders fields without `-Zrandomize-layout`:** Because `IS_TRANSPARENT` is absent from `FIELD_ORDER_UNOPTIMIZABLE` (`lib.rs:105-108`), `Exp E` records `TransZst { fields: Arbitrary { offsets: [Size(8 bytes), Size(0 bytes)], in_memory_order: [1, 0] }, backend_repr: Scalar(Initialized { value: Int(I64, false), valid_range: 0..=18446744073709551615 }) }`—the compiler swaps field `1` (`u64`) to offset `0` and pushes `PhantomData<u8>` to offset `8` (and preserves `Scalar(I64)` ABI!).
3. **`ReprCSingle(u64)` vs. `ReprRustSingle(u64)` ABI divergence:** `Exp E` confirms `ReprCSingle(u64)` has `backend_repr: Memory { sized: true }`, whereas `ReprRustSingle(u64)` has `backend_repr: Scalar(Int(I64, false))`—direct runtime proof of `optimize_abi = !repr.inhibit_newtype_abi_optimization()` (`layout.rs:827, 845-848`).

---

### 5. Downstream First-Customer Analysis: `google/zerocopy` and `joshlf/anneal`

**Basis:** `source` (`google/zerocopy@e8dcb7f08`, `joshlf/anneal@c131b320e`) + `execution` (`Exp D`, `Exp E`) + `derived` (Lean 4)

#### `google/zerocopy` (`zerocopy/src/wrappers.rs`, `zerocopy/src/layout.rs`)

1. **`Unalign<T>` (`zerocopy/src/wrappers.rs:117-118`, `239-249`):**
   - `Unalign<T>` is declared **`#[repr(C, packed)] pub struct Unalign<T>(T);`**. On `u64`, `ZcUnalign<u64>` has `size=8, align=1`; embedded inside `#[repr(C)] struct ZcPacketHeader { tag: u8, val: ZcUnalign<u64>, tail: u8 }`, it eliminates all 7+7 inter-field and tail padding bytes (`size=10, align=1, offsets=(tag:0, val:1, tail:9)`).
   - **Generic `ty::Param` Reliance:** When instantiated with an over-aligned type (`ZcUnalign<Aligned8>`), both `1.98.0-nightly` and `1.102.0-nightly` accept it (`size=8, align=1`), with `Exp E` confirming `align: Align(1), backend_repr: Memory { sized: true }, max_repr_align: Some(Align(8 bytes)), unadjusted_abi_align: Align(1 bytes)`.
   - **Source Comment Bug in `zerocopy` (`wrappers.rs:240`):** Inside `Unalign::deref_unchecked`, line `240` contains an inaccurate internal comment: `// SAFETY: Unalign<T> is repr(transparent), so there is a valid T...`. As line `117` proves, `Unalign<T>` is `#[repr(C, packed)]`, **not** `#[repr(transparent)]` (otherwise `align_of::<Unalign<u64>>()` would be `8`, not `1`). Its layout-prefix and no-padding guarantees come from `#[repr(C, packed)]` over a single sized field.
2. **`ReadOnly<T>` (`zerocopy/src/wrappers.rs:626-631`):**
   - Declared **`#[repr(transparent)] pub struct ReadOnly<T: ?Sized> { inner: T }`**, forwarding exact `size`, `align`, and `ScalarPair` / `Scalar` / `Memory` `BackendRepr` (`ZcReadOnly<(u8, u64)>` -> `size=16, align=8`).
3. **`DstLayout::for_repr_c_struct` (`zerocopy/src/layout.rs:1135-1197, 1231-1495`):**
   - Models `#[repr(C)]` struct layout sequentially using `new_zst(repr_align)` -> `extend(field, repr_packed)` -> `pad_to_align()`.
   - Crucially, `layout.rs:1270-1274` computes `field_align = min(field.align, max_align)` and `align = max(self.align, field_align)` in exact algebraic agreement with `rustc_abi::layout_of_univariant_biased` (proven identically equal for sized `#[repr(C)]` fields in Theorem `zcForReprCStruct_eq_computeReprC`), while `layout.rs:1135-1143` explicitly documents the generic `repr(align)`-inside-`repr(packed)` compatibility premise verified here. Notice one subtle boundary: `DstLayout::for_repr_c_struct` checks alignment overflow up to `CURRENT_MAX_ALIGN` and has a Kani harness bound of `<= 3` fields (`layout.rs:1158-1168`), whereas our Lean mechanization (`computeOrderedLayout_soundness`, `zcForReprCStruct_eq_computeReprC`) quantifies universally over arbitrary finite field lists `fields : List FieldSpec`.

#### `joshlf/anneal` (`trusted/lean/Trusted/{MirAst.lean, MirSemantics.lean}`)

- At commit `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst.MirTy` (`MirAst.lean:312-321`) models only `.bool`, `.int width signed`, `.unit`, `.never`, fieldless `.enum ty`, `.tuple fields`, `.ref`, `.rawPtr`, and `.unsupported`, explicitly mapping non-fieldless-enum ADTs (`struct`, `union`, data-carrying `enum`) to `.unsupported` (`FaultKind.unsupported`).
- `MirSemantics.lean` only tracks single-unit / fieldless ZST enums (`isZstEnumTy`, `MirSemantics.lean:523, 751, 902`) alongside 64-bit target configuration (`pointerWidthBits = 64`). It does not yet store `ReprOptions` (`kind`, `pack`, `align`, `randomizeLayout`), field-offset maps (`Offsets`), or `align > 1` ZST alignment constraints.
- **Concrete Trusted-Boundary Guidance for Anneal:** Extending `Trusted.MirAst` and `Trusted.MirSemantics` to structs must (1) treat `#[repr(Rust)]` field offsets and `in_memory_order` as **opaque compiler-chosen permutations** (proving only properties invariant across permutations, such as `perm_invariance_align_and_zst_size` and valid disjoint bounds via `computeOrderedLayout_soundness`), rather than hardcoding declaration or sorted offsets (especially under `-Zrandomize-layout`); (2) model ZST alignment propagation (`Align > 1` ZSTs shifting subsequent `#[repr(C)]` field offsets and struct alignment); (3) separate `effFieldAlign = min(align, pack)` (which modifies offsets and `unadjusted_abi_align`) from `repr.align` (which modifies only aggregate `align` and tail padding); and (4) keep `check_packed_inner`'s `E0588` vs. `ALIGNED_FIELDS_IN_PACKED` compiler-version divergence outside layout arithmetic so generic wrappers like `Unalign<Aligned8>` remain valid once sized field layout is resolved.

---

### 6. Constructive Lean `v4.34.1` Mechanization (`support/AbiReprLayoutZstPackedTransparentSoundness.lean`)

**Basis:** `derived` (`Lean v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`) + `source` + `execution`

[`support/AbiReprLayoutZstPackedTransparentSoundness.lean`](support/AbiReprLayoutZstPackedTransparentSoundness.lean) provides a `1,994`-line self-contained formalization (`249` local theorems, `268` local definitions) verified under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` using **only constructive `{propext, Quot.sound}` axioms** (zero `sorry`, zero `Classical.choice`, zero `omega`/`bv_decide`/`native_decide`, zero `partial`, and zero `._unsafe_rec` constants verified by MetaM constant/axiom traversal).

#### Mechanized Model and Correspondence Contracts

- **Alignment Arithmetic (Section 1):** `paddingNeeded`, `alignUp`, `IsPowerOfTwo`, `IsLeastAlignedGe`, plus constructive `Nat` divisibility/monotonicity lemmas (`alignUp_isLeastAlignedGe`, `pow2_dvd_iff_le`, `pow2_min_dvd_of_le`, `min_dvd_left_pow2`, `min_dvd_right_pow2`).
- **`rustc_abi` & `zerocopy` Model (Sections 2-4):** `PrimKind`, `BackendRepr`, `FieldSpec`, `ReprKind`, `ReprOptions`, `effFieldAlign`, `StructLayout`, `placeFieldsFrom`, `fieldsMaxEffAlign`, `fieldsMaxReprAlign`, `computeBackendRepr`, `computeUnadjustedAbiAlign`, `computeOrderedLayout`, `alignmentGroupKey`, `sortFieldsByAlignGroup`, `computeReprRustLayout`, `zcForReprCStruct`, `CheckPackedEra` (`.pre4e99638` vs. `.post4e99638`), `FieldCheckNode`, `checkPacked`, and `checkTransparent`.

#### Four Universal Theorem Families + Four Empirical Cross-Checks + Two Boundary Counterexamples

| Identifier (`AbiReprLayoutZstPackedTransparentSoundness.lean`) | Statement & Proved Property |
| :--- | :--- |
| **`computeOrderedLayout_soundness`** (L890) | **Family 1:** Under `AllAlignPos fields` and `ReprModifierValid repr`, `L = computeOrderedLayout repr fields` satisfies exact length match, effective-alignment divisibility of every offset (`effFieldAlign repr.pack f.align \| L.offsets[i]`), strict ordered non-overlap and pairwise disjointness (`FieldsDisjoint`), field end in-bounds (`L.offsets[i] + f.size <= L.endOffset <= L.size`), positive aggregate alignment (`0 < L.align`), every effective alignment divides `L.align` when alignments are powers of two (`AllPow2Align`, `ReprModifierPow2`), and `L.size = alignUp L.endOffset L.align` satisfies `IsLeastAlignedGe` (`SizeAlignedMinimal`). |
| **`computeOrderedLayout_all_zst_zero_size`** (L944) | **Family 1 (ZST corollary):** When every field has `size = 0`, all offsets are `0`, `endOffset = 0`, `size = 0`, and `align = max_or(fieldsMaxEffAlign repr.pack 1 fields, repr.align)` (never inflated by tail rounding or `align` modifiers). |
| **`perm_invariance_align_and_zst_size`** (L1030) & **`reprRust_align_eq_declaration_order`** (L1053) | **Family 2a:** Any field permutation `List.Perm fs1 fs2` (covering `-Zrandomize-layout` and `sortFieldsByAlignGroup_perm`) preserves aggregate `align`, `maxReprAlign`, `isReprC`, and pure-ZST `size = 0`. |
| **`reprC_prefix_offsets_invariant`** (L1078) & **`reprC_prefix_monotone`** (L1121) | **Family 2b:** Appending suffix fields `gs` to a `#[repr(C)]`-ordered prefix `fs` leaves every prefix field offset unchanged and monotonically increases `endOffset`, `align`, and `size` (requiring `AllPow2Align`, `ReprModifierPow2`). |
| **`zcForReprCStruct_eq_computeReprC`** (L1185) | **Family 2b (`zerocopy` equivalence):** `DstLayout::for_repr_c_struct` on sized fields yields exact `(align, size)` equality with `computeOrderedLayout` on arbitrary `fields : List FieldSpec`. |
| **`packed1_zero_padding_exact_sum`** (L1266) | **Family 3a:** `#[repr(packed(1))]` yields `align = 1`, `unadjustedAbiAlign = 1`, zero padding (`size = endOffset = totalFieldSize fields`), and exact prefix-sum offsets `offsets[i] = totalFieldSize (fields.take i)`. |
| **`packed_monotone_compression`** (L1373) & **`packed_ge_all_fields_noop`** (L1434) | **Family 3b:** Tightening power-of-two `pack1 <= pack2` (including `none` as infinity) monotonically decreases aggregate `align`, `endOffset`, every offset `i`, and `size`; whenever `∀ f ∈ fields, f.align <= p`, `#[repr(packed(p))]` equals unpacked layout identically. |
| **`unalign_preserves_size_sets_align1`** (L1465) | **Family 3c (`zerocopy::Unalign<T>`):** Wrapping any positive-aligned sized type `t` (including `#[repr(align(N))]`) preserves `size = t.size`, sets `align = 1` and `unadjustedAbiAlign = 1`, places `t` at offset `0`, propagates `t.maxReprAlign`, and returns `checkPacked = .ok` in both `pre4e99638` and `post4e99638` via `FieldCheckNode.genericParam`. |
| **`transparent_all_1zst_identity`** (L1565) & **`transparent_sole_non_1zst_identity`** (L1605) & **`transparent_single_non1zst_accepted_and_unadjusted_align`** (L1716) & **`readonly_transparent_wrapper_identity`** (L1748) | **Family 4 (`a`-`d`):** All-`1-ZST` `transparent` structs yield `(size=0, align=1, unadjustedAbiAlign=1)`. Sole non-`1-ZST` among non-`repr(C)` `1-ZST`s yields `size = fMain.size`, `align = fMain.align`, `fMain` at offset `0`, forwarded `backendRepr` (`Scalar` or `ScalarPair`, since `inhibitNewtypeAbiOpt` tests only `ReprKind.c`), forwarded `unadjustedAbiAlign`, and `isReprC = fMain.isReprC`. Single non-`1-ZST` field passes `checkTransparent` and yields `size = 0, align = z.align, unadjustedAbiAlign = z.align`. Specializes directly to `ReadOnly<T>`. |
| **`xc_expA` .. `xc_expD`** (L1846-1960) | Ground cross-checks reproducing exact numerical offsets/sizes/diagnostics of `Exp A`, `Exp B`, `Exp C` (pre/post `4e99638c7`), and `Exp D`. |
| **`ce5_non_pow2_packed_increases_size`** (L1961) & **`ce6_randomize_layout_scope`** (L1980) | **Negative/sharpness proofs:** (`CE5`) Without power-of-two alignments or pack bounds, smaller pack values can *increase* struct size (e.g., `⟨3, 3⟩` under `packed(2)` -> `4B` > `3B` under `packed(4)`; `[tyU32]` under `packed(3)` -> `6B` > `4B` under `packed(4)`). (`CE6`) `canRandomizeTypeLayout` is `true` for `#[repr(packed)]` (`reprPacked1`) and `#[repr(transparent)]` (`reprTrans`), and `false` **only** when `#[repr(C)]` (`reprCDefault`, `reprCPacked1`) is set. |

---

## Boundaries

To prevent over-generalization beyond observed compiler code, target executions, and formal assumptions, the following negative-space boundaries are explicitly recorded:

1. **Known Not to Apply:**
   - **Enum variants and multi-variant discriminant/niche layout (`layout_of_enum`):** Our Lean mechanization and Experiments A-E model single-variant structs (`layout_of_univariant_biased`); multi-variant niche tagging, scalar-range niches (`NonZero<u64>`, `&T`, `bool`), and niche-biased placement (`NicheBias::End` vs. `NicheBias::Start`) in multi-field enums are outside [`support/AbiReprLayoutZstPackedTransparentSoundness.lean`](support/AbiReprLayoutZstPackedTransparentSoundness.lean), where `FieldSpec` carries only a `hasNiche : Bool` placeholder and `computeOrderedLayout` models deterministic offset arithmetic for fixed orderings (without full niche-offset tracking).
   - **Unsized structs (`StructKind::MaybeUnsized`, DST tails):** `computeOrderedLayout` models sized structs (`AlwaysSized`). Although `DstLayout::for_repr_c_struct` in `zerocopy/src/layout.rs:1153-1495` supports trailing slice DSTs via `SizeInfo::SliceDst(RoundingAlignAndPhase)` (with an aligned trailing DST exempt from `#[repr(Rust)]` tail reordering due to `end = fields.len() - 1` at `layout.rs:608`), our Lean proof of `zcForReprCStruct_eq_computeReprC` covers **sized fields only** (`fields : List FieldSpec`).
   - **Non-x86_64 C/MSVC ABIs and `#[repr(C)]` bit-fields / `#[repr(simd)]`:** All live executions target `x86_64-unknown-linux-gnu` (`dl.aggregate_align = 1`, `dl.i8_align = 1`). On targets where `dl.aggregate_align > 1`, an empty `#[repr(Rust)]` struct without `pack` starts `align` at `dl.aggregate_align` (`layout.rs:604`). Furthermore, GCC vs. MSVC differences on nested `#[repr(C, align)]` inside `#[repr(C, packed)]` (`ALIGNED_FIELDS_IN_PACKED`) were not executed on a Windows MSVC target (`known not to apply` / `not examined`).
   - **Sub-field interior padding / recursive field internals:** `FieldCheckNode` and `FieldSpec` model a struct's direct fields as pre-laid-out `LayoutData` inputs; Rust `#[repr(packed)]` never removes internal padding *inside* a field's own `repr(C)` or `repr(Rust)` sub-struct (`r[layout.repr.alignment.packed-padding]`).
   - **Unaligned reference creation (`&packed.field`) UB and `Miri` runtime checks:** Layout computation of `#[repr(packed)]` / `Unalign<T>` proves offset and alignment arithmetic (`align = 1`), **not** that creating `&T` to an unaligned field is sound—which remains immediate UB (`r[layout.repr.alignment.packed-padding]` note; safe access requires copy, `read_unaligned`, or `&raw const`).
   - **ScalarPair newtype unwrapping on non-opaque C structs:** Notice an attractive stronger claim that does **not** hold in `rustc`: `inhibit_newtype_abi_optimization()` (`layout.rs:845-854`) suppresses `Scalar` and `SimdVector` ABI unwrapping for `#[repr(C)]`, **not** `ScalarPair` (a single-field `#[repr(C)]` wrapper around `(u8, u64)` can retain `ScalarPair` `backend_repr` while `#[repr(C)] struct ReprCSingle(u64)` demotes to `BackendRepr::Memory`).
2. **Unknown / Not Examined:**
   - **Pinned-unpin (`#[pin_v2]` / `PinV2OnPacked`) interaction in `check.rs:1673-1679`:** Present in source on `49d734536` and `3ef0c22cd`, noted for destructor move-to-aligned-slot hazard, not empirically executed in `probe_repr_layout_zst_packed_align.py`.
   - **Experimental `#[repr(linear)]` (`IS_LINEAR`, `lib.rs:91, 108`):** Present in `ReprFlags` and inhibits struct reordering (`FIELD_ORDER_UNOPTIMIZABLE`), without inhibiting ABI optimization (`ABI_UNOPTIMIZABLE`); not probed empirically.
   - **`serde` / FFI targets with `i128` alignment differences across older ABIs** or `#[repr(transparent)]` enums with single variant (`layout.rs` shares the univariant path): `not examined`.
3. **Unsupported (`joshlf/anneal@c131b320e`):**
   - Arbitrary `struct`, `union`, data-carrying `enum`, `#[repr(C)]`, `#[repr(packed)]`, `#[repr(align)]`, and `#[repr(transparent)]` ADTs remain `.unsupported` in `Trusted.MirAst.MirTy` (`MirAst.lean:308-321`) and raise `FaultKind.unsupported` in `Trusted.MirSemantics`.

---

## Evidence

All file/line citations, execution artifacts, and proof verifications are preserved in immutable upstream revisions or directly inside this package's `support/` directory:

### 1. Primary Source Citations (`rust-lang/rust`, `rust-lang/reference`, `google/zerocopy`, `joshlf/anneal`)

- **`rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, `2026-11-11`):**
  - `compiler/rustc_abi/src/layout.rs`: `layout_of_univariant` (`273-341`), `NicheBias::End` `MaybeUnsized` skip (`295`), `layout_of_struct_or_enum` (`343-395`), `layout_of_struct` (`540-588`), `layout_of_univariant_biased` (`590-935`), `Xoshiro128StarStar` (`632-637`), `alignment_group_key` (`654-690`), `Reverse(alignment_group_key)` sort (`719-729`), placement loop (`764-805`), `unadjusted_abi_align` (`809`), `repr.align` (`810-812`), `size = min_size.align_to(align)` (`817-818`), `optimize_abi` (`827-863`), `repr.transparent()` `unadjusted_abi_align` fallback (`905-915`), `repr_c` propagation (`918`).
  - `compiler/rustc_abi/src/lib.rs`: `ReprFlags` (`85-110`: `FIELD_ORDER_UNOPTIMIZABLE` omits `IS_TRANSPARENT`), `ReprOptions::{inhibit_enum_layout_opt, inhibit_newtype_abi_optimization, inhibit_struct_field_reordering, can_randomize_type_layout}` (`224-242`), `LayoutData::{is_1zst, is_zst}` (`2396-2425`).
  - `compiler/rustc_middle/src/ty/mod.rs`: `field_shuffle_seed` (`1638-1665`, XOR of `def_path_hash` and `layout_seed`).
  - `compiler/rustc_attr_parsing/src/attributes/repr.rs`: `parse_repr_attr` (`86-185`, `ReprPacked(Align::ONE)` default at `110`).
  - `compiler/rustc_hir_analysis/src/check/check.rs`: `check_packed` (`1666-1752`: `E0634` `1689`, `E0587` `1701`, `repr.c()`-gated `ALIGNED_FIELDS_IN_PACKED` lint `1705-1750`), `check_packed_inner` (`1754-1780`: `def.repr().c()` and concrete `ty::Adt` check), `check_transparent` (`1782-1925`: `variant.fields.len() <= 1` early exit `1804-1807`, `is_trivial` `1829-1861`, `is_1zst()` `1873`, `E0690` `1907`).
  - `compiler/rustc_passes/src/{check_attr.rs:1046-1064, diagnostics.rs:344-350}`: `TransparentIncompatible` (`E0692`).
  - `compiler/rustc_lint_defs/src/builtin.rs:5845-5863`: `ALIGNED_FIELDS_IN_PACKED` deny-by-default lint (`GCC` vs. `MSVC` rationale).
  - `compiler/rustc_error_codes/src/error_codes/E0588.md:1-26`: `"#### Note: this error code is no longer emitted by the compiler."`.
- **Pre-`E0588`-Retirement `rust-lang/rust` Commits & Transition:**
  - `rust-lang/rust@4e99638c7fb697db838c38669709c01bb7cc799a` (`2026-09-14`): transition commit moving `E0588` to `ALIGNED_FIELDS_IN_PACKED`.
  - `rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da` (`2026-09-11`): pre-retirement `check_packed` / `check_packed_inner` (`check.rs:1641-1742`) and `layout_of_univariant_biased` (`layout.rs:1081-1425`).
  - `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, `2026-05-31`): pre-retirement `rustc-src` (`layout.rs`, `check.rs`) and live compiler binary executed here.
- **`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`:**
  - `src/type-layout.md`: `r[layout.repr.c.struct]` (`240-295`), `r[layout.repr.alignment]` (`632-680`), `r[layout.repr.transparent]` (`682-696`).
- **`google/zerocopy@e8dcb7f08edbc19485c9e7980333607ebbff5f48` (and identical `99238c633f747763a6ce9d403ab0007ddca72751`):**
  - `zerocopy/src/wrappers.rs`: `Unalign<T>` (`100-124`, `239-249`), `ReadOnly<T>` (`625-640`).
  - `zerocopy/src/layout.rs`: `DstLayout::for_repr_c_struct` (`1135-1197`), `extend` (`1231-1280`), `pad_to_align` (`1455-1495`).
- **`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:**
  - `trusted/lean/Trusted/MirAst.lean:272-321` (`MirTy`), `trusted/lean/Trusted/MirSemantics.lean:523, 751, 793-801, 902`.

### 2. Live `rustc` Execution Artifacts (`2026-11-23` & `2026-11-11`)

- **[`support/probe_repr_layout_zst_packed_align.py`](support/probe_repr_layout_zst_packed_align.py):** Self-contained Python harness using `tempfile.TemporaryDirectory()` to execute Experiments `A`-`E` (`-Zprint-type-sizes`, `-Zrandomize-layout -Zlayout-seed={1,42,99}`, `E0587`/`E0634`/`E0690`/`E0692`/`E0588` diagnostics, `zerocopy`-equivalent wrappers, and `#[rustc_dump_layout(debug)]`). Zero local machine paths leak into [`support/probe_results.json`](support/probe_results.json) (temp directories sanitized to `<tmp>`).
- **Comparative `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11, LLVM 23.1.5)` observations:** Direct runs on `x86_64-unknown-linux-gnu` confirmed matching default `SDefault`/`SC`/`SPacked`/`SPacked2`/`SCAlign16` sizes and `-Zrandomize-layout` shuffling (`SDefault = 24B`, `SPacked = 12B`, `SPacked2 = 12B/14B`), identical `ReprCZstMid = 32B` / `ReprCZstEnd = 16B` / `PureZst = 0B align 16`, identical `E0587`/`E0690`/`E0692` errors, `SingleNon1Zst([u32; 0]) = 0B align 4`, `ZcUnalign<Aligned8> = 8B align 1`, and the live `E0588` retirement (`rustc --explain E0588` reporting `"no longer emitted"`, and concrete `#[repr(packed)] struct Bad(Aligned8)` compiling with `rc=0`, `size=8, align=1`).

### 3. Lean `v4.34.1` Formalization and Purity Audit (`2026-11-23`)

- **[`support/AbiReprLayoutZstPackedTransparentSoundness.lean`](support/AbiReprLayoutZstPackedTransparentSoundness.lean)** (`1,994` lines, `95,957` bytes, `249` theorems, `268` definitions):
  - Compiled cleanly (`exit 0`, zero warnings/errors) under `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` on Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).
  - MetaM environment traversal across all `249` module theorems confirmed `AXIOMS_USED = [Quot.sound, propext]`, `BAD_THM_AXIOMS = 0`, `UNSAFE_REC_COUNT = 0`, and zero occurrences of `sorry`, `Classical.choice`, `omega`, `bv_decide`, `native_decide`, `noncomputable section`, `partial `, `deriving`, or `._unsafe_rec`.

---

## Revalidation

To reproduce both the live `rustc` empirical suite and the Lean `v4.34.1` kernel proof check from the package directory (on `x86_64-unknown-linux-gnu` with nightly `rustc` and Lean `v4.34.1` installed):

1. **Re-run the `rustc` empirical matrix (`probe_repr_layout_zst_packed_align.py`):**

   ```bash
   python3 support/probe_repr_layout_zst_packed_align.py
   ```

   Inspect `support/probe_results.json` to confirm:
   - `rustc_version` and whether `experiments.c_illegal_repr_diagnostics.e0588_retired_in_explain` is `false` (pre-`4e99638c7` toolchains such as `1.98.0-nightly`) or `true` (`4e99638c7` / `1.102.0-nightly` and newer, where `packed_containing_align_field_rust_outer` returns `compile_returncode = 0` with `size=8 align=1` and `packed_containing_align_field_c_both_allow_lint` compiles once `#[allow(aligned_fields_in_packed)]` is supplied).
   - `-Zrandomize-layout` mutates `SDefault`, `SPacked`, and `SPacked2` while leaving `SC`, `SCAlign16`, `SCPacked`, `SCPacked2`, and `Pure1Zst` invariant.
   - `Exp E` (`e_rustc_dump_layout_internals`) preserves `unadjusted_abi_align: Align(16 bytes)` on `TransAlign16Zst` and `in_memory_order: [1, 0]` on `TransZst`.

2. **Re-verify the Lean `v4.34.1` kernel proof (`AbiReprLayoutZstPackedTransparentSoundness.lean`):**

   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/AbiReprLayoutZstPackedTransparentSoundness.lean
   ```

   Expected result: exit code `0` with zero diagnostics or warnings. To verify zero `Classical.choice` / `sorryAx` / `._unsafe_rec` leakage, check `#print axioms RustcAbiReprLayout.computeOrderedLayout_soundness` (and `packed_monotone_compression`, `zcForReprCStruct_eq_computeReprC`, `transparent_sole_non_1zst_identity`, `unalign_preserves_size_sets_align1`) against an unmodified Lean `v4.34.1` environment (`<= {propext, Quot.sound}`).

3. **Validate corpus metadata and formatting:**

   From the corpus root:

   ```bash
   python3 tools/reference.py catalog
   python3 tools/reference.py check
   ```

   Both commands must exit `0` with `reference check passed`.
