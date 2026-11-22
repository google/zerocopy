# Multi-Target `rustc_abi` Layout Calculator, `#[repr]` Algebra, and Packed-Align Soundness

## Summary

This report establishes primary-source, multi-target empirical, and kernel-checked Lean `v4.34.1` ground truth for `rustc`'s type layout calculator (`rustc_abi::LayoutCalculator`), `#[repr]` validation (`rustc_hir_analysis`), calling-convention alignment assertions (`rustc_target::callconv::x86_win32`), and layout randomization (`-Z randomize-layout`) across four pinned `rust-lang/rust` revisions (`1.98.0-nightly`, `1.99.1`, `1.102.0-nightly`, and `HEAD` `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), together with the trusted-boundary interface in `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:

1. **Nine-target `TargetDataLayout` alignment laws:** Primitive alignment cannot be inferred solely from pointer width or bit width. Across nine targets, `i686-unknown-linux-gnu` aligns `u64`/`f64` to `4` bytes (making `#[repr(C)] struct C_U8_U64(u8, u64)` `12` bytes, align `4`) while keeping `u128` at `16` bytes (`C_U8_U128 = 32` bytes), whereas `i686-pc-windows-msvc` and `wasm32-unknown-unknown` keep `ptr` at `4` bytes but align `u64`/`f64` to `8` bytes (`C_U8_U64 = 16` bytes) and `u128` to `16` bytes. Conversely, `s390x-unknown-linux-gnu` (`64`-bit pointer) and `thumbv7m-none-eabi` (`32`-bit pointer) omit an explicit `i128` entry from their LLVM data-layout strings, triggering `TargetDataLayout`'s `i64..=128` fallback rule so `u128` aligns to `8` bytes (`C_U8_U128 = 24` bytes, align `8`) rather than `16` bytes (`32` bytes on `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, and `riscv64gc-unknown-none-elf`).
2. **`#[repr(simd, packed)]` power-of-two cliff:** In `vector_type_layout`, `SimdVectorKind::PackedFixed` branches on `!count.is_power_of_two()`. Non-power-of-two lane counts strip tail padding, assign `align = Align::max_aligned_factor(size)` (the greatest power-of-two divisor of byte size), and demote `BackendRepr` from `SimdVector` to `Memory { sized: true }` (`SimdPackedF32x3`: `12 B`, align `4`, `Memory`; `SimdPackedF32x6`: `24 B`, align `8`, `Memory`; `SimdPackedU8x3`: `3 B`, align `1`, `Memory`). Power-of-two lane counts ignore `packed` completely (`SimdPackedF32x4`: `16 B`, align `16`, `SimdVector`, identical to unpacked `SimdF32x4`).
3. **`StructKind::MaybeUnsized` tail pinning vs. `NicheBias::End` suppression:** Marking a struct's final field `?Sized` pins that field at the end (`FixedArrBool([u8; 4], bool)` has offsets `(1, 0)` vs. `MaybeDstArrBool<bool>([u8; 4], bool)` at `(0, 4)`). Tail pinning alone conserves struct `size_of` whenever the sorted prefix is padding-free and the tail's alignment `d` divides both the tail size and target size budget (`alignTo_add_le_iff_of_dvd`). However, `layout_of_univariant` explicitly suppresses the second `NicheBias::End` layout attempt whenever `matches!(kind, StructKind::MaybeUnsized)`. Even with an identical field list and a 0-byte `()` tail (`FixedPureNiche(u32, bool, u8, ())` vs. `MaybeDstPureNiche<()>(u32, bool, u8, ())`), suppressing `NicheBias::End` leaves the `bool` niche at offset `4` instead of `5`, inflating an enclosing 2-variant enum paired with `[u8; 5]` from `8` bytes to `12` bytes.
4. **Non-1-ZST uninhabited variant reservation (`#49298`) and `#[repr(C)]` newtype asymmetry:** `absent(fields)` requires both `uninhabited` AND every field being a `1`-ZST (`size == 0 && align == 1`). Accordingly, `Dead1Zst { Live(u8), Dead(Never) }` collapses to `1 B` (`Scalar(u8)`), while `#[repr(C)] ReprCDead1Zst` inhibits `absent` (`8 B`, align `4`, `ScalarPair(u32, union u8)`), `DeadPayload64 { Live(u8), Dead(Never, [u8; 64]) }` reserves `65 B` (`align 1`, `Memory`), and `DeadAlign16Zst { Live(u8), Dead(Never, Align16Zst) }` reserves `16 B` (`align 16`, `Memory`). For single-field `#[repr(C)]` structs, `inhibit_newtype_abi_optimization()` blocks unpacking `BackendRepr::Scalar` (`ReprCWrapScalar(u64)` -> `Memory`), whereas `BackendRepr::ScalarPair` is unpacked unconditionally (`ReprCWrapTuplePair((u64, u64))` and `ReprCTwoScalars(u64, u64)` both keep `ScalarPair`). For unions, common-primitive scalar ABI forwarding fires only for non-`repr(C)`, non-overpacked unions whose non-ZST fields share identical `Primitive` (including signedness: `u64` + `NonZeroU64` -> `Scalar(Union(I64, false))`, whereas `u64` + `i64` -> `Memory`).
5. **Live `#![forbid(unsafe_code)]` definition-site `check_packed_inner` bypass, `x86_win32.rs` ICE (`rc = 101`), and `layout_of_array_like` `max_repr_align` erasure:** Across all four audited `rust-lang/rust` revisions, `check_packed_inner` runs on uninstantiated identity types and recurses solely into direct `ty::Adt` fields. Wrapping a `#[repr(C, align(8))]` struct inside a `#[repr(C, packed)]` struct via a generic type parameter (`GenericPacked<T>(T)`), a tuple (`TuplePacked((Inner,))`), or a trait projection alias (`AliasPacked(<() as Assoc>::Out)`) bypasses both `E0588` (hard error in `1.98.0-nightly` and `1.99.1`) and `ALIGNED_FIELDS_IN_PACKED` (deny-by-default lint restricted to `repr(C)` in `1.102.0-nightly` and `HEAD`). During layout calculation, `layout_of_univariant_biased` clamps `abi` alignment to `pack = 1` while propagating `max_repr_align = Some(8)`, violating `align >= max_repr_align`. Passing such a type to an `extern "C"` function on `i686-pc-windows-msvc` triggers a live compiler ICE (`rc = 101`) at `x86_win32.rs` (`:69:13` in `1.98.0-nightly`, `:73:13` in `1.99.1` and `1.102.0-nightly`, `:82:13` at `HEAD`), while compiling with `rc = 0` on `x86_64-unknown-linux-gnu`. By contrast, wrapping via an array (`ArrayPacked([Inner; 1])`) also bypasses `check_packed_inner`, but `layout_of_array_like` hardcodes `max_repr_align: None`, silencing the ICE and causing non-packed `#[repr(C)] struct ReprCArrayOuter([Inner; 1])` to be lowered on `i686-pc-windows-msvc` as stack `byval([8 x i8]) align 4` instead of indirect `ptr align 8`.
6. **Deterministic `-Z randomize-layout` and all-ZST invariance:** Layout randomization feeds `field_seed.wrapping_add(repr.field_shuffle_seed)` into `Xoshiro128StarStar` (`field_shuffle_seed = def_path_hash ^ layout_seed`), yielding reproducible per-seed permutations for `repr(Rust)` structs while leaving `#[repr(C)]` field order unchanged and preserving `0`-byte size for all-ZST `repr(Rust)` structs, 1-variant all-ZST enums, and 0-variant enums.
7. **Mechanized soundness & trusted-boundary implications:** `support/RustcAbiLayoutAndReprSoundness.lean` kernel-checks three core theorems (`alignTo_add_le_iff_of_dvd`, `postMonoPackedCheck_implies_abiAlign_ge_maxReprAlign`, `maxAlignedFactor_dvd_size_and_pow2`) and four constructive sharpness counterexamples (`ce1`–`ce4`) in Lean `v4.34.1` with zero `Classical.choice` and zero trust-escaping axioms. Because `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` currently gates `Trusted.MirSemantics` on `pointerWidthBits = 64` and models only primitive scalars and fieldless enums, extending verified compilation or MIR-to-ABI checking across multiple targets requires importing target-parameterized `TargetDataLayout`, `#[repr]` flags, post-monomorphization `PackedAlignWf`, and `max_repr_align` propagation directly into the trusted layout interface.

## Applicability

### Subjects and Relationships

This report studies six durable upstream subjects and their mutual relationships:

| Subject | Repository | Immutable Revision | Role in This Report |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` (`HEAD`) | `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | Primary-source authority for current layout calculator (`rustc_abi/src/layout.rs`, `layout/enum_layout.rs`, `rustc_abi/src/lib.rs`), `rustc_ty_utils/src/layout.rs`, `rustc_hir_analysis/src/check/check.rs`, `rustc_lint_defs/src/builtin.rs`, `rustc_middle/src/ty/mod.rs`, `rustc_target/src/callconv/x86_win32.rs`, and the nine target spec files (`2026-11-22`). |
| `rustc 1.98.0-nightly` | `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | Direct primary-source inspection AND live execution host (`LLVM 22.1.6`) for all seven parts of `support/probe_multi_target_layout_and_repr.py` (`support/probe_results.json`, `2026-11-22`). |
| `rustc 1.99.1` | `rust-lang/rust` | `58cf8f9c35b355199727627d07ae34a4e2846d67` | Direct primary-source verification (`2026-11-22`) plus cross-version stable-channel execution observations (`LLVM 23.1.1`, `2026-11-21`). |
| `rustc 1.102.0-nightly` | `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | Direct primary-source verification (`2026-11-22`) plus cross-version nightly execution observations (`LLVM 23.1.5`, `2026-11-21`), documenting the `AbiAndPrefAlign -> Align` simplification, `layout/enum_layout.rs` split, and `E0588 -> ALIGNED_FIELDS_IN_PACKED` lint downgrade. |
| `joshlf/anneal` | `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Direct source inspection of `trusted/lean/Trusted/MirAst.lean` and `trusted/lean/Trusted/MirSemantics.lean` (`2026-11-22`) to characterize the exact gap between current TCB layout assumptions and `rustc_abi`'s multi-target algebra. |
| Lean `v4.34.1` | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` | Kernel proof checker (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) for the standalone mathematical formalization in `support/RustcAbiLayoutAndReprSoundness.lean` (`2026-11-22`). |

### Version-Shared vs. Version-Specific Behavior

Behaviors **shared identically across all four `rust-lang/rust` revisions** (`1.98.0-nightly`, `1.99.1`, `1.102.0-nightly`, `HEAD`):

- All nine targets' `ptr`, `u64`, `f64`, and `u128` sizes, alignments, and `C_U8_U64` / `C_U8_U128` / `Pair_U8_U64` / `Pair_U8_U128` layouts.
- `vector_type_layout` `PackedFixed` power-of-two dispatch (`!count.is_power_of_two()` -> `Memory` + `Align::max_aligned_factor(size)` vs. power-of-two ignoring `packed`).
- `StructKind::MaybeUnsized` tail pinning (`end = fields.len() - 1`) and `NicheBias::End` suppression (`!matches!(kind, StructKind::MaybeUnsized)`).
- `absent(fields)` definition (`uninhabited && is_1zst`), `#49298` non-1-ZST uninhabited variant reservation, and `repr.inhibit_enum_layout_opt()` suppression for `#[repr(C)]` / `#[repr(int)]`.
- `#[repr(C)]` newtype asymmetry (`BackendRepr::Scalar` / `SimdVector` guarded by `optimize_abi`; `BackendRepr::ScalarPair` and two-scalar structs unguarded) and union ABI optimization rules.
- Definition-site `check_packed_inner` recursing exclusively into direct `ty::Adt` fields (`ty::Param`, `ty::Alias`, `ty::Tuple`, and `ty::Array` all bypass the check), unconditional `max_repr_align = max_repr_align.max(field.max_repr_align)` propagation in `univariant_biased` / `layout_of_univariant_biased`, `max_repr_align: None` reset in `layout_of_array_like`, and the `x86_win32.rs` assertion `align >= max_repr_align` (`rc = 101` ICE on `i686-pc-windows-msvc`).
- `-Z randomize-layout` + `-Z layout-seed` `Xoshiro128StarStar` determinism (within a given compiler revision and crate path hash) and `0`-byte invariance for all-ZST `repr(Rust)` structs and 0/1-variant all-ZST enums.

Behaviors **specific to particular `rust-lang/rust` revisions**:

| Feature / Behavior | `1.98.0-nightly` (`14210df0e`) | `1.99.1` (`58cf8f9c3`) | `1.102.0-nightly` (`3ef0c22cd`) | `HEAD` (`342d74463`) |
| :--- | :--- | :--- | :--- | :--- |
| `LayoutData.align` representation | `AbiAndPrefAlign` / `AbiAlign` (`align.abi`) | `AbiAndPrefAlign` (`align.abi`) | `Align` (single ABI alignment) | `Align` (single ABI alignment) |
| `rustc_abi` enum layout module | Monolithic `compiler/rustc_abi/src/layout.rs` | Monolithic `compiler/rustc_abi/src/layout.rs` | Split into `layout.rs` + `layout/enum_layout.rs` + `layout/simple.rs` | Split into `layout.rs` + `layout/enum_layout.rs` + `layout/simple.rs` |
| `BackendRepr::ScalarPair` debug formatting | `ScalarPair(a, b)` | `ScalarPair(a, b)` | `ScalarPair { a, b, b_offset }` | `ScalarPair { a, b, b_offset }` |
| Nested `#[repr(align)]` inside concrete `#[repr(packed)]` | Hard error `E0588` for all packed structs/unions | Hard error `E0588` for all packed structs/unions | Deny-by-default lint `ALIGNED_FIELDS_IN_PACKED`, restricted to `repr(C)` outer & `repr(C)` inner (`#[allow(aligned_fields_in_packed)]` permits it on `x86_64`) | Same as `1.102.0-nightly` (`check.rs:1707-1782`) |
| `#[repr(packed)]` on `enum` diagnostic | `error[E0517]: attribute should be applied to a struct or union` | `error: the repr(packed) attribute cannot be used on enums` | `error: the repr(packed) attribute cannot be used on enums` | Attribute-parser rejection (no `E0517` code) |
| `x86_win32.rs` `assert!` panic location | `x86_win32.rs:69:13` (`align.abi >= max_repr_align`) | `x86_win32.rs:73:13` (`align.abi >= max_repr_align`) | `x86_win32.rs:73:13` (`align >= max_repr_align`) | `x86_win32.rs:82:13` (`align >= max_repr_align`, shifted by x87 FP return handling) |
| `-Z layout-seed=<N>` exact permutation | Deterministic for fixed crate/rustc; differs from `1.102.0-nightly` because `def_path_hash` / crate metadata hash differs across builds | Stable channel rejects `-Z` without `RUSTC_BOOTSTRAP=1` | Deterministic per seed (tested `seed=1` twice identically) | Same `Xoshiro128StarStar` seeding algorithm (`rustc_middle/src/ty/mod.rs:1761-1768`) |

### Invocation & Scope Constraints

- Multi-target `#[rustc_dump_layout(...)]` probes in `support/probe_multi_target_layout_and_repr.py` use `#![feature(no_core, lang_items, rustc_attrs, repr_simd)]` and `#![no_core]` with `--crate-type=lib --emit=metadata` (or `--emit=llvm-ir` for `i686-pc-windows-msvc` ABI lowering), requiring **no cross-compiled `rust-std` sysroot** for any of the nine targets.
- Runtime `offset_of!` / `size_of` probes (`part_c`, `part_g`) execute natively on `x86_64-unknown-linux-gnu` with standard `std`.
- The Lean `v4.34.1` formalization models the mathematical algorithms of `rustc_abi`, `check_packed_inner`, and `x86_win32` directly in core Lean 4 (`Init` only); its theorems establish properties of that explicit mathematical model, validated against real `rustc` output across all empirical probes.

## Findings

### 1. Nine-Target `TargetDataLayout` Primitive and Pair Alignment Matrix

Basis: source + execution + derived

#### 1.1 LLVM Data-Layout Parsing and the `i128` Fallback Rule

In `compiler/rustc_abi/src/lib.rs` (`HEAD` `342d74463`, lines `357-389` and `507-650`), `TargetDataLayout::parse_from_llvm_datalayout_string` initializes a `Default` layout (`i64_align = 32 bits`, `i128_align = 32 bits`, `f64_align = 64 bits`, `pointer_size = 64 bits`, `pointer_align = 64 bits`, `aggregate_align = 8 bits`) and parses each `-`-separated specification token. Two subtleties govern `u64`, `f64`, and `u128` alignment across targets:

1. **Unlisted `i64` retains `Default` `32`-bit alignment (`4` bytes):** If a target's data-layout string omits `i64:...` (as `i686-unknown-linux-gnu` does), `dl.i64_align` remains the `Default` value of `32` bits (`4` bytes). Simultaneously, `i686-unknown-linux-gnu` explicitly overrides `f64:32:64`, lowering `dl.f64_align` from `64` bits to `32` bits (`4` bytes).
2. **`i128_align` inherits the largest specified `i{64..=128}` alignment when `i128` is omitted:** Lines `510` and `631-636` of `compiler/rustc_abi/src/lib.rs` maintain `let mut i128_align_src = 64;`:
   ```rust
   if bits >= i128_align_src && bits <= 128 {
       // Default alignment for i128 is decided by taking the alignment of
       // largest-sized i{64..=128}.
       i128_align_src = bits;
       dl.i128_align = a;
   }
   ```
   Consequently, any target whose data-layout string specifies `i64:64` without an `i128:...` entry — specifically `s390x-unknown-linux-gnu` and `thumbv7m-none-eabi` — assigns `dl.i128_align = Align(8 bytes)` rather than `16` bytes. By contrast, all seven other audited targets specify `i128:128` explicitly, yielding `Align(16 bytes)`.

#### 1.2 Exact Target Spec Strings (`rust-lang/rust@342d74463`)

Every target spec file under `compiler/rustc_target/src/spec/targets/` was inspected directly at `342d74463`:

| Target Triple | Ptr Width | Verbatim `data_layout` Key Clauses | `ptr` Align | `u64` Align | `f64` Align | `u128` Align |
| :--- | :---: | :--- | :---: | :---: | :---: | :---: |
| `x86_64-unknown-linux-gnu` | `64` | `e-m:e-...-i64:64-i128:128-f80:128-n8:16:32:64-S128` | `8 B` | `8 B` | `8 B` | `16 B` |
| `i686-unknown-linux-gnu` | `32` | `e-m:e-p:32:32-...-i128:128-f64:32:64-f80:32-n8:16:32-S128` (no `i64`) | `4 B` | **`4 B`** | **`4 B`** | `16 B` |
| `i686-pc-windows-msvc` | `32` | `e-m:x-p:32:32-...-i64:64-i128:128-f80:128-n8:16:32-a:0:32-S32` | `4 B` | `8 B` | `8 B` | `16 B` |
| `wasm32-unknown-unknown` | `32` | `e-m:e-p:32:32-p10:8:8-p20:8:8-i64:64-i128:128-n32:64-S128-ni:1:10:20` | `4 B` | `8 B` | `8 B` | `16 B` |
| `s390x-unknown-linux-gnu` | `64` | `E-S64-m:e-i1:8:16-i8:8:16-i64:64-f128:64-v128:64-a:8:16-n32:64` (no `i128`) | `8 B` | `8 B` | `8 B` | **`8 B`** |
| `thumbv7m-none-eabi` | `32` | `e-m:e-p:32:32-Fi8-i64:64-v128:64:128-a:0:32-n32-S64` (no `i128`) | `4 B` | `8 B` | `8 B` | **`8 B`** |
| `aarch64-unknown-linux-gnu` | `64` | `e-m:e-...-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32` | `8 B` | `8 B` | `8 B` | `16 B` |
| `aarch64-apple-darwin` | `64` | `e-m:o-...-i64:64-i128:128-n32:64-S128-Fn32` | `8 B` | `8 B` | `8 B` | `16 B` |
| `riscv64gc-unknown-none-elf` | `64` | `e-m:e-p:64:64-i64:64-i128:128-n32:64-S128` | `8 B` | `8 B` | `8 B` | `16 B` |

#### 1.3 Empirical Nine-Target Pair Matrix (`C_U8_U64`, `Pair_U8_U64`, `C_U8_U128`, `Pair_U8_U128`)

Live execution of `support/probe_multi_target_layout_and_repr.py` (`rustc 1.98.0-nightly`, `2026-11-22`, matching `1.102.0-nightly` observations from `2026-11-21` in every size, alignment, and `ScalarPair` field order) confirms four distinct target equivalence classes across the nine triples:

| Equivalence Class | Targets | `P_Ptr` (sz/al) | `P_U64` / `P_F64` | `P_U128` | `C_U8_U64` (sz/al, `b_off`) | `Pair_U8_U64` (sz/al, order, `b_off`) | `C_U8_U128` (sz/al, `b_off`) | `Pair_U8_U128` (sz/al, order, `b_off`) |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **Class 1 (LP64 / 16B `u128`)** | `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, `riscv64gc-unknown-none-elf` | `8 / 8` | `8 / 8` | `16 / 16` | `16 / 8` (`8`) | `16 / 8` (`u64, u8`, `8`) | `32 / 16` (`16`) | `32 / 16` (`u128, u8`, `16`) |
| **Class 2 (ILP32 / 4B `u64`/`f64`, 16B `u128`)** | `i686-unknown-linux-gnu` | `4 / 4` | **`8 / 4`** | `16 / 16` | **`12 / 4`** (`4`) | **`12 / 4`** (`u64, u8`, `8`) | `32 / 16` (`16`) | `32 / 16` (`u128, u8`, `16`) |
| **Class 3 (ILP32 / 8B `u64`/`f64`, 16B `u128`)** | `i686-pc-windows-msvc`, `wasm32-unknown-unknown` | `4 / 4` | `8 / 8` | `16 / 16` | `16 / 8` (`8`) | `16 / 8` (`u64, u8`, `8`) | `32 / 16` (`16`) | `32 / 16` (`u128, u8`, `16`) |
| **Class 4 (8B `u128`, 64-bit vs 32-bit ptr)** | `s390x-unknown-linux-gnu` (`ptr 8/8`), `thumbv7m-none-eabi` (`ptr 4/4`) | `8/8` / `4/4` | `8 / 8` | **`16 / 8`** | `16 / 8` (`8`) | `16 / 8` (`u64, u8`, `8`) | **`24 / 8`** (`8`) | **`24 / 8`** (`u128, u8`, `16`) |

Two structural consequences follow directly (mechanized in `RustcAbiLayoutAndReprSoundness.nine_target_alignment_laws`):

- **Bit-width does not determine `u64` or `u128` alignment:** `i686-unknown-linux-gnu` and `i686-pc-windows-msvc` share the exact same x86-32 ISA and 32-bit pointer width, yet `C_U8_U64` is `12` bytes on Linux and `16` bytes on MSVC; `x86_64-unknown-linux-gnu` and `s390x-unknown-linux-gnu` share 64-bit pointers, yet `C_U8_U128` is `32` bytes on x86-64 and `24` bytes on s390x.
- **`repr(Rust)` reorders `Pair_U8_U64` and `Pair_U8_U128` on every target, preserving `ScalarPair`:** In all nine targets, `Pair_U8_U64` places `u64` at offset `0` and `u8` at offset `8` (`ScalarPair(u64, u8)`), whereas `C_U8_U64` preserves declaration order `ScalarPair(u8, u64)` with `b_offset = 4` on `i686-unknown-linux-gnu` and `8` elsewhere. Notably, `#[repr(C)]` does **not** inhibit `ScalarPair` for two-scalar structs (see Finding 4.2).

---

### 2. `#[repr(simd)]` vs. `#[repr(simd, packed)]` Power-of-Two Demotion Cliff

Basis: source + execution + derived

#### 2.1 Primary-Source Dispatch in `vector_type_layout`

In `compiler/rustc_ty_utils/src/layout.rs` (`HEAD` `342d74463`, lines `647-698`), a `#[repr(simd)]` ADT must be a single-field struct containing `[T; N]` for a primitive scalar `T`. It dispatches to `LayoutCalculator::layout_of_simd_type(e_ly, e_len, def.repr().packed())` (`compiler/rustc_abi/src/layout.rs:226-239`), which sets `kind = SimdVectorKind::PackedFixed` when `repr_packed` is true and `SimdVectorKind::Fixed` otherwise, then invokes `vector_type_layout` (`layout.rs:979-1035` at `HEAD`, `layout.rs:1476-1534` in `1.98.0-nightly`, `layout.rs:1468-1526` in `1.99.1`):

```rust
let size =
    elt.size.checked_mul(count.as_u64(), dl).ok_or(LayoutCalculatorError::SizeOverflow)?;
let (repr, size, align) = match kind {
    SimdVectorKind::Scalable(number_of_vectors) => ( ... ),
    // Non-power-of-two vectors have padding up to the next power-of-two.
    // If we're a packed repr, remove the padding while keeping the alignment as close
    // to a vector as possible.
    SimdVectorKind::PackedFixed if !count.is_power_of_two() => {
        (BackendRepr::Memory { sized: true }, size, Align::max_aligned_factor(size))
    }
    SimdVectorKind::PackedFixed | SimdVectorKind::Fixed => {
        (BackendRepr::SimdVector { element, count }, size, dl.rust_vector_align(size))
    }
};
let size = size.align_to(align);
```

Where:
- `TargetDataLayout::rust_vector_align(vec_size)` (`compiler/rustc_abi/src/lib.rs:750-753`) checks `c_vector_align(vec_size)` (default entries: `64b -> 64b`, `128b -> 128b`) and otherwise returns `Align::from_bytes(vec_size.bytes().next_power_of_two())`.
- `Align::max_aligned_factor(size)` (`compiler/rustc_abi/src/lib.rs:1221-1223`) computes `Align { pow2: size.bytes().trailing_zeros() as u8 }`, i.e. the greatest power of two $2^{v_2(\text{size})}$ dividing `size`.

#### 2.2 Empirical Verification of the Power-of-Two Cliff

Executed live on `rustc 1.98.0-nightly` (`support/probe_results.json`, `part_b_simd_packed_pow2_vs_nonpow2`, identical to `1.102.0-nightly` observations):

| Type | Definition | Raw Bytes (`elt * N`) | `count.is_power_of_two()` | `size` | `align` | `backend_repr` | Tail Padding |
| :--- | :--- | :---: | :---: | :---: | :---: | :--- | :---: |
| `SimdF32x3` | `#[repr(simd)] struct([f32; 3])` | `12` | `false` | `16 B` | `16 B` | `SimdVector(f32, 3)` | `4 B` |
| `SimdPackedF32x3` | `#[repr(simd, packed)] struct([f32; 3])` | `12` | `false` | **`12 B`** | **`4 B`** (`max_aligned_factor(12)`) | **`Memory { sized: true }`** | `0 B` |
| `SimdF32x4` | `#[repr(simd)] struct([f32; 4])` | `16` | `true` | `16 B` | `16 B` | `SimdVector(f32, 4)` | `0 B` |
| `SimdPackedF32x4` | `#[repr(simd, packed)] struct([f32; 4])` | `16` | `true` | **`16 B`** | **`16 B`** | **`SimdVector(f32, 4)`** | `0 B` |
| `SimdF32x6` | `#[repr(simd)] struct([f32; 6])` | `24` | `false` | `32 B` | `32 B` | `SimdVector(f32, 6)` | `8 B` |
| `SimdPackedF32x6` | `#[repr(simd, packed)] struct([f32; 6])` | `24` | `false` | **`24 B`** | **`8 B`** (`max_aligned_factor(24)`) | **`Memory { sized: true }`** | `0 B` |
| `SimdPackedU8x3` | `#[repr(simd, packed)] struct([u8; 3])` | `3` | `false` | **`3 B`** | **`1 B`** (`max_aligned_factor(3)`) | **`Memory { sized: true }`** | `0 B` |

#### 2.3 Key Semantic Trap and Mechanized Soundness

1. **`#[repr(simd, packed)]` does NOT mean `align(1)`:** Unlike `#[repr(packed)]` on ordinary structs (which forces `pack = Some(Align(1))`), `#[repr(simd, packed)]` does **not** clamp alignment to `1`:
   - When `count` is a power of two (`SimdPackedF32x4`), `packed` is a **complete no-op** — the type retains `align = 16` and `BackendRepr::SimdVector` (NOT `align = 1`, NOT `Memory`).
   - When `count` is not a power of two, `align = Align::max_aligned_factor(raw_size)` can still exceed element alignment (`SimdPackedF32x6` has `elt.align = 4`, yet `max_aligned_factor(24) = 8`, because $24 = 3 \times 8$!).
2. **Exact tail-padding elimination (`maxAlignedFactor_dvd_size_and_pow2` & `vectorTypeLayout_packed_nonpow2_sound`):** Because $2^{v_2(\text{size})}$ is the largest power-of-two divisor of `size`, the final `size.align_to(align)` at `layout.rs:1017` is provably a no-op (`alignTo size (maxAlignedFactor size) = size`), guaranteeing zero tail padding while demoting the ABI from `SimdVector` to `Memory { sized: true }` (affecting calling conventions, e.g. System V AMD64 XMM/YMM register passing).
3. **Note on `unadjusted_abi_align` and `max_repr_align`:** `vector_type_layout` unconditionally sets `max_repr_align: None` and `unadjusted_abi_align: elt.align` (`layout.rs:1030-1031`), even when `align` is `16` or `32`.

---

### 3. `StructKind::MaybeUnsized` Tail Pinning, Divisibility Conservation, and `NicheBias::End` Suppression

Basis: source + execution + derived

#### 3.1 When `StructKind::MaybeUnsized` Activates

In `compiler/rustc_ty_utils/src/layout.rs` (`HEAD` `342d74463`, lines `754-764`), `maybe_unsized` is decided from the **generic definition** of a struct, **not** from whether a monomorphized instantiation happens to be sized:

```rust
let maybe_unsized = def.is_struct()
    && def.non_enum_variant().tail_opt().is_some_and(|last_field| {
        let typing_env = ty::TypingEnv::new(
            tcx.param_env_normalized_for_post_analysis(def.did()),
            cx.typing_env.typing_mode(),
        );
        !tcx.type_of(last_field.did)
            .instantiate_identity()
            .skip_norm_wip()
            .is_sized(tcx, typing_env)
    });
```

Thus, for any struct `struct S<T: ?Sized>(..., T)`, even a fully sized instantiation such as `S<bool>`, `S<u8>`, or `S<()>` receives `StructKind::MaybeUnsized` so that unsizing coercion `&S<T> -> &S<dyn Trait>` preserves identical prefix field offsets (explicitly verified by debug assertions at `rustc_ty_utils/src/layout.rs:783-815`). Non-empty tuples (`ty::Tuple(tys)` with `tys.len() > 0`) likewise pass `StructKind::MaybeUnsized` (`rustc_ty_utils/src/layout.rs:612-616`).

#### 3.2 Effect 1: Tail Pinning and the Pinned-Tail Size Conservation Theorem

In `layout_of_univariant_biased` (`compiler/rustc_abi/src/layout.rs:609-610`):

```rust
let end = if let StructKind::MaybeUnsized = kind { fields.len() - 1 } else { fields.len() };
let optimizing = &mut in_memory_order.raw[..end];
```

Only `fields[..end]` participate in field reordering (`alignment_group_key`, niche bias, or `-Z randomize-layout` shuffling); the final field `fields[end]` is pinned last. Consequently:
- `struct FixedArrBool([u8; 4], bool)` (`AlwaysSized`) reorders `bool` before `[u8; 4]` (due to `NicheBias::Start` clamping `size_as_align` to `max_field_align.trailing_zeros() = 0` when a niche is present, `layout.rs:675-677`), yielding offsets `(1, 0)`.
- `struct MaybeDstArrBool<T: ?Sized>([u8; 4], T)` instantiated at `T = bool` (`MaybeUnsized`) pins `bool` at the tail, yielding offsets `(0, 4)`.

Yet tail pinning **alone** never increases `size_of` when the sorted prefix is padding-free (sum of sizes $P$) and the tail's alignment $d > 0$ divides both $\text{size}(T)$ and the target aligned struct size $M$. Formally (`alignTo_add_le_iff_of_dvd` in `support/RustcAbiLayoutAndReprSoundness.lean`):

$$\forall P, \text{size}(T), M, d \in \mathbb{N},\quad d > 0 \land d \mid \text{size}(T) \land d \mid M \implies \bigl(\operatorname{align\_to}(P, d) + \text{size}(T) \le M \iff P + \text{size}(T) \le M\bigr).$$

**Proof sketch (fully constructive, zero `omega`):** Write $\text{size}(T) = s \cdot d$ and $M = m \cdot d$. The $(\Rightarrow)$ direction is immediate from $P \le \operatorname{align\_to}(P, d)$. For $(\Leftarrow)$, $P + s d \le m d$ gives $s \le m$ and $P \le (m - s) d$. By the Galois closure law of upward alignment ($P \le k d \iff \operatorname{align\_to}(P, d) \le k d$ for $d > 0$), $\operatorname{align\_to}(P, d) \le (m - s) d$, so $\operatorname{align\_to}(P, d) + s d \le (m - s) d + s d = m d = M$. Because every sized Rust type satisfies $\text{align}(T) \mid \text{size}(T)$ and every struct's final size $M$ is a multiple of $\max(\text{prefix\_align}, d)$ (hence divisible by $d$), a padding-free sorted prefix plus a pinned tail achieves the exact same struct `size_of` as an unconstrained sort whenever the unconstrained optimal size $M$ satisfies $P + \text{size}(T) \le M$.

#### 3.3 Effect 2: `NicheBias::End` Suppression and Outer Enum Inflation (`8 B -> 12 B`)

While `StructKind::MaybeUnsized` preserves the inner struct's `size_of = 8 B` in these examples, `layout_of_univariant` (`compiler/rustc_abi/src/layout.rs:286-341` at `HEAD`, lines `278-340` in `1.98.0-nightly`/`1.99.1`) deliberately suppresses its second `NicheBias::End` pass whenever `kind` is `MaybeUnsized`:

```rust
if let Ok(layout) = &layout
    // Don't try to calculate an end-biased layout for unsizable structs,
    // otherwise we could end up with different layouts for
    // Foo<Type> and Foo<dyn Trait> which would break unsizing.
    && !matches!(kind, StructKind::MaybeUnsized)
    && let Some(niche) = layout.largest_niche
    && let head_space = niche.offset.bytes()
    && let niche_len = niche.value.size(dl).bytes()
    && let tail_space = layout.size.bytes() - head_space - niche_len
    && (fields.len() > 1 && head_space != 0 && tail_space > 0)
{
    let alt_layout = self
        .layout_of_univariant_biased(fields, repr, kind, NicheBias::End)
        .expect("alt layout should always work");
    ...
    let prefer_alt_layout = alt_head_space > head_space && alt_head_space > tail_space;
    if prefer_alt_layout { return Ok(alt_layout); }
}
```

Why does this matter for outer enums? In `try_fit_variants_around_niche_tag` (`compiler/rustc_abi/src/layout/enum_layout.rs:480-520`), a secondary variant of size `V` fits into a niche-packed enum of size `S` with niche at `[niche_offset, niche_offset + niche_size)` if and only if either:
- **Before the niche:** `V <= niche_offset`, or
- **After the niche:** `align_to(niche_offset + niche_size, V_align) + V <= S`.

Pushing a 1-byte `bool` niche from offset `4` to offset `5` inside an `8`-byte struct expands the contiguous prefix before the niche from `4` bytes to `5` bytes, enabling a `5`-byte sibling variant (`[u8; 5]`) to pack with zero overhead (`8` bytes total instead of falling back to a `12`-byte tagged enum).

#### 3.4 Live Execution Evidence (`part_c_maybe_unsized_tail_pinning_and_niche_bias`)

Executed live on `rustc 1.98.0-nightly` (`support/probe_results.json`, line `422`), with `FixedPureNiche` vs. `MaybeDstPureNiche<()>` isolating `NicheBias::End` suppression cleanly from tail pinning by using identical field types `(u32, bool, u8, ())` and a 0-byte `()` tail:

| Probe Type | `StructKind` | Observed Field Offsets | Niche (`bool`) Offset | Struct Size | Paired Enum with `B([u8; 5])` | Mechanism Demonstrated |
| :--- | :---: | :---: | :---: | :---: | :---: | :--- |
| `FixedArrBool([u8; 4], bool)` | `AlwaysSized` | `(1, 0)` | `0` | `5 B` | — | `NicheBias::Start` clamps `size_as_align` to `0`, moving `bool` before `[u8; 4]` |
| `MaybeDstArrBool<bool>([u8; 4], bool)` | `MaybeUnsized` | `(0, 4)` | `4` | `5 B` | — | Tail pinning locks `T = bool` at offset `4` (size conserved: `5 B`) |
| `FixedEdge(u32, u8, bool)` | `AlwaysSized` | `(0, 4, 5)` | `5` | `8 B` | **`8 B`** (`EnumFixedEdge`) | `NicheBias::End` beats `Start` (`alt_head 5 > head 4` and `5 > tail 3`) |
| `MaybeDstEdge<u8>(u32, bool, u8)` | `MaybeUnsized` | `(0, 4, 5)` | `4` | `8 B` | **`12 B`** (`EnumMaybeDstEdge`) | Tail pinned + `NicheBias::End` suppressed -> `[u8; 5]` fails before (`5 > 4`) & after (`10 > 8`) |
| `FixedPureNiche(u32, bool, u8, ())` | `AlwaysSized` | **`(0, 5, 4, 5)`** | **`5`** | `8 B` | **`8 B`** (`EnumFixedPureNiche`) | Pure `NicheBias::End` swaps `bool` past `u8` to offset `5` |
| `MaybeDstPureNiche<()>(u32, bool, u8, ())` | `MaybeUnsized` | **`(0, 4, 5, 6)`** | **`4`** | `8 B` | **`12 B`** (`EnumMaybeDstPureNiche`) | Same fields & ZST tail `()`, yet `MaybeUnsized` skips `NicheBias::End`, inflating enum `8 -> 12 B` |
| `NoBool(u8, [u8; 16])` | `AlwaysSized` | `(16, 0)` | none | `17 B` | — | `largest_niche_size == 0` -> `size_as_align = 4` promotes `[u8; 16]` first |
| `WithBool(bool, [u8; 16])` | `AlwaysSized` | `(0, 1)` | `0` | `17 B` | — | `largest_niche_size > 0` -> `NicheBias::Start` clamps `size_as_align` to `0`, keeping `bool` first |
| `EndBias { a: u16, b: bool, c: u8 }` | `AlwaysSized` | `b=3, a=0` (`c=2`) | `3` | `4 B` | — | `NicheBias::End` moves `bool` past `c` to offset `3` (`alt_head 3 > head 2` and `3 > tail 1`) |

(Note: the exact `FIXED_ARR_BOOL_OFF=(1,0)`, `MAYBEDST_ARR_BOOL_OFF=(0,4)`, `FIXED_EDGE_OFF=(0,4,5)`, `MAYBEDST_EDGE_OFF=(0,4,5)`, `ENUM_FIXED_SZ=8`, `ENUM_MAYBEDST_SZ=12`, `NO_BOOL_OFF=(16,0)`, `WITH_BOOL_OFF=(0,1)`, and `END_BIAS_OFF=(3,0)` values match `1.102.0-nightly` identically.)

---

### 4. Non-1-ZST Uninhabited Variant Reservation (`#49298`), `#[repr(C)]` Newtype Asymmetry, and Union ABI Optimization

Basis: source + execution + derived

#### 4.1 `absent` and Non-1-ZST Uninhabited Variants (`#49298`)

In `compiler/rustc_abi/src/layout.rs` (`HEAD` `342d74463`, lines `91-102`; `1.98.0-nightly`/`1.99.1`, lines `89-100`):

```rust
// A variant is absent if it's uninhabited and only has ZST fields.
// Present uninhabited variants only require space for their fields,
// but *not* an encoding of the discriminant (e.g., a tag value).
// See issue #49298 for more details on the need to leave space
// for non-ZST uninhabited data (mostly partial initialization).
fn absent<'a, FieldIdx, VariantIdx, F>(fields: &IndexSlice<FieldIdx, F>) -> bool {
    let uninhabited = fields.iter().any(|f| f.is_uninhabited());
    // We cannot ignore alignment; that might lead us to entirely discard a variant and
    // produce an enum that is less aligned than it should be!
    let is_1zst = fields.iter().all(|f| f.is_1zst());
    uninhabited && is_1zst
}
```

Where `f.is_1zst()` requires `f.is_sized() && f.size == Size::ZERO && f.align == Align::ONE`. In `layout_of_struct_or_enum` (`layout.rs:359-380`), variants satisfying `!repr.inhibit_enum_layout_opt() && absent(v)` are dropped before counting present variants (`inhibit_enum_layout_opt()` returns `self.c() || self.int.is_some()`, `rustc_abi/src/lib.rs:227-229`).

Empirical verification (`support/probe_results.json`, `part_d_uninhabited_non_1zst_variant_reservation`, identical across `1.98.0-nightly` and `1.102.0-nightly` modulo `ScalarPair` debug syntax):

| Enum Definition | `absent(Dead)` | `inhibit_enum_layout_opt` | `size` | `align` | `backend_repr` | Why |
| :--- | :---: | :---: | :---: | :---: | :--- | :--- |
| `enum Dead1Zst { Live(u8), Dead(Never) }` | `true` | `false` | `1 B` | `1 B` | `Scalar(u8)` | `Dead` is absent -> collapses to univariant `Live(u8)` |
| `#[repr(C)] enum ReprCDead1Zst { Live(u8), Dead(Never) }` | `true` (ignored) | **`true`** | **`8 B`** | **`4 B`** | `ScalarPair(u32 is 0..=1, union u8)` (`b_off = 4`) | `#[repr(C)]` forces `(c_int tag, payload union)` and retains `Dead` discriminant |
| `enum DeadPayload64 { Live(u8), Dead(Never, [u8; 64]) }` | **`false`** (`[u8; 64]` not ZST) | `false` | **`65 B`** | `1 B` | `Memory { sized: true }` | `#49298`: space for partial initialization of `[u8; 64]` plus 1-byte tag prefix |
| `enum DeadAlign16Zst { Live(u8), Dead(Never, Align16Zst) }` | **`false`** (`align 16 != 1`) | `false` | **`16 B`** | **`16 B`** | `Memory { sized: true }` | Non-1-ZST alignment cannot be discarded; forces `align 16` and rounds size to `16 B` |

Notice a subtle detail in `calculate_tagged_layout` (`enum_layout.rs:354-357`): for `DeadPayload64` and `DeadAlign16Zst`, `necessary_discriminants` filters out uninhabited variants when `!repr.c()`, so no runtime discriminant value is ever valid for `Dead`, yet `layout_variants` still builds a `StructKind::Prefixed(min_ity.size(), prefix_align)` univariant struct for every variant (`enum_layout.rs:388-406`). Because `min_ity` is `I8` (1 byte) and `Dead(Never, [u8; 64])` is laid out after that 1-byte prefix, `DeadPayload64` occupies `1 + 64 = 65` bytes (`align 1`), and `DeadAlign16Zst` aligns the 1-byte prefix + `Align16Zst` up to `align 16`, occupying `16` bytes (`align 16`).

#### 4.2 `#[repr(C)]` `Scalar` vs. `ScalarPair` Newtype Asymmetry and Union ABI Optimization

In `layout_of_univariant_biased` (`compiler/rustc_abi/src/layout.rs:828-903` at `HEAD`, `layout.rs:1329-1404` in `1.98.0-nightly`), `let optimize_abi = !repr.inhibit_newtype_abi_optimization();` where `inhibit_newtype_abi_optimization()` checks `ReprFlags::ABI_UNOPTIMIZABLE = IS_C | IS_SIMD` (`rustc_abi/src/lib.rs:112, 231-233`). Look at the asymmetric `match` over a single non-ZST field filling the struct (`offsets[i] == 0 && align == field.align && size == field.size`):

```rust
match field.backend_repr {
    // For plain scalars, or vectors of them, we can't unpack
    // newtypes for `#[repr(C)]`, as that affects C ABIs.
    BackendRepr::Scalar(_) | BackendRepr::SimdVector { .. }
        if optimize_abi =>
    {
        abi = field.backend_repr;
    }
    // But scalar pairs are Rust-specific and get
    // treated as aggregates by C ABIs anyway.
    BackendRepr::ScalarPair { .. } => {
        abi = field.backend_repr;
    }
    _ => {}
}
```

Similarly, the two-non-ZST-scalar branch (`layout.rs:862-899`) ignores `optimize_abi` completely: whenever both fields are `BackendRepr::Scalar` and their memory offsets, size, and alignment match `LayoutData::scalar_pair`, `abi` becomes `BackendRepr::ScalarPair` — **even for `#[repr(C)]` structs**.

For unions, `layout_of_union` (`compiler/rustc_abi/src/layout.rs:419-507` at `HEAD`, lines `415-499` in `1.98.0-nightly`) forwards a common non-ZST field `BackendRepr` (after stripping validity ranges via `.to_union()`) **only if all three conditions hold**:
1. `!repr.inhibits_union_abi_opt()` (i.e. `!repr.c()`, `rustc_abi/src/lib.rs:248-250`);
2. Every non-ZST field has the exact same `field.backend_repr.to_union()` (strict `Primitive` equality, including integer signedness — unlike `calculate_common_primitive` in `enum_layout.rs:117`, which merges signed and unsigned integers of equal width!);
3. Alignment matches the scalar's platform alignment (`repr.scalar_platform_align(dl).unwrap() == align`, failing for `#[repr(packed)]` unions).

Empirical verification (`support/probe_results.json`, `part_e_repr_c_scalar_vs_scalarpair_and_union_opt`):

| Type | Definition | `size` | `align` | `backend_repr` | Explaining Rule |
| :--- | :--- | :---: | :---: | :--- | :--- |
| `RustWrapScalar` | `struct(u64)` | `8 B` | `8 B` | `Scalar(u64)` | `optimize_abi = true` unpacks `Scalar` |
| `ReprCWrapScalar` | `#[repr(C)] struct(u64)` | `8 B` | `8 B` | **`Memory { sized: true }`** (`Homogeneous(Reg { Integer, 8 })`) | `optimize_abi = false` blocks `Scalar` unpacking so C ABI treats it as a struct aggregate |
| `ReprCWrapTuplePair` | `#[repr(C)] struct((u64, u64))` | `16 B` | `8 B` | **`ScalarPair(u64, u64)`** | `ScalarPair` branch omits `if optimize_abi` guard |
| `ReprCTwoScalars` | `#[repr(C)] struct(u64, u64)` | `16 B` | `8 B` | **`ScalarPair(u64, u64)`** | Two-scalar branch ignores `optimize_abi` |
| `CommonScalarUnionSamePrim` | `union { a: u64, b: NonZeroU64 }` | `8 B` | `8 B` | **`Scalar(Union { value: Int(I64, false) })`** | Same `Primitive::Int(I64, false)` after `.to_union()`, non-`repr(C)`, aligned |
| `CommonScalarUnionMixedSign` | `union { a: u64, b: i64 }` | `8 B` | `8 B` | **`Memory { sized: true }`** | `Int(I64, false) != Int(I64, true)` triggers `AbiMismatch` |
| `ReprCUnion` | `#[repr(C)] union { a: u64, b: NonZeroU64 }` | `8 B` | `8 B` | **`Memory { sized: true }`** | `repr.inhibits_union_abi_opt() == true` |
| `PackedScalarUnion` | `#[repr(packed)] union { a: u64, b: NonZeroU64 }` | `8 B` | `1 B` | **`Memory { sized: true }`** | `scalar_platform_align (8) != align (1)` |

---

### 5. Live Safe `#![forbid(unsafe_code)]` `check_packed_inner` Bypass, `x86_win32.rs` ICE (`rc = 101`), and `layout_of_array_like` `max_repr_align` Drop

Basis: source + execution + derived

#### 5.1 Root Cause Across Three Compiler Crates

A three-crate invariant mismatch connects HIR attribute checking, `rustc_abi` layout calculation, and `i686-pc-windows-msvc` calling-convention lowering:

1. **Crate 1 (`compiler/rustc_hir_analysis/src/check/check.rs`):**
   - In **`1.98.0-nightly` (`14210df0e:1613-1704`)** and **`1.99.1` (`58cf8f9c3:1622-1723`)**, `check_packed` emits hard error `E0588` ("packed type cannot transitively contain a `#[repr(align)]` type") whenever `check_packed_inner` finds a transitively nested `#[repr(align)]` struct/union.
   - In **`1.102.0-nightly` (`3ef0c22cd:1666-1780`)** and **`HEAD` (`342d74463:1668-1782`)**, `check_packed` downgrades `E0588` to the deny-by-default lint `ALIGNED_FIELDS_IN_PACKED` (`compiler/rustc_lint_defs/src/builtin.rs:5858-5862`), **and restricts both `check_packed` and `check_packed_inner` to `repr.c()`** (`if repr.c() && let Some(...) = check_packed_inner(...)` and `if def.repr().c() && (def.is_struct() || def.is_union())`). Thus, on `1.102.0-nightly`/`HEAD`, `#[allow(aligned_fields_in_packed)]` permits even a concrete `#[repr(C, packed)] struct Outer(Inner)` on `x86_64`, and non-`repr(C)` `#[repr(packed)]` containing `#[repr(align(8))]` emits no diagnostic at all.
   - **Critical definition-site blindness across ALL FOUR revisions:** `check_packed_inner` operates on the uninstantiated identity type `tcx.type_of(def_id).instantiate_identity().skip_norm_wip()` and checks **only** `if let ty::Adt(def, _) = field.ty(tcx, args).skip_norm_wip().kind()`. It does **not** normalize projections (`skip_norm_wip()`), does **not** run post-monomorphization, and does **not** recurse into `ty::Param`, `ty::Alias`, `ty::Tuple`, or `ty::Array`!

2. **Crate 2 (`compiler/rustc_abi/src/layout.rs`):**
   - In `layout_of_univariant_biased` (`HEAD` `342d74463:780-784`, `1.98.0-nightly:1280-1285`), each field computes:
     ```rust
     let field_align =
         if let Some(pack) = pack { field.align.min(pack) } else { field.align };
     offset = offset.align_to(field_align);
     align = align.max(field_align);
     max_repr_align = max_repr_align.max(field.max_repr_align);
     ```
     Notice the inconsistency: `pack` clamps `field_align` (and therefore clamps `layout.align` to `1`), yet `max_repr_align` propagates `field.max_repr_align` **unclamped**! Consequently, `GenericPacked<Inner>`, `TuplePacked((Inner,))`, and `AliasPacked(<() as Assoc>::Out)` all receive `Layout { size: 8, align: Align(1), max_repr_align: Some(Align(8)) }` — breaking the invariant `align >= max_repr_align`.
   - Meanwhile, `layout_of_array_like` (`HEAD` `342d74463:192-204`, `1.98.0-nightly:190-202`) unconditionally sets `max_repr_align: None` instead of `element.max_repr_align`.

3. **Crate 3 (`compiler/rustc_target/src/callconv/x86_win32.rs`):**
   - In `compute_abi_info` (`1.98.0-nightly:59-74`, `1.99.1:63-78`, `1.102.0-nightly:63-78`, `HEAD:72-87`), MSVC x86-32 passes ADTs with explicit `max_repr_align > 4` indirectly (while passing naturally over-aligned types such as `u64`/`f64` via 4-byte `byval` on the stack) and asserts:
     ```rust
     if arg.layout.is_adt()
         && let Some(max_repr_align) = arg.layout.max_repr_align
         && max_repr_align > align_4
     {
         assert!(
             arg.layout.align >= max_repr_align, // .align.abi in <=1.99.1
             "abi alignment {:?} less than requested alignment {max_repr_align:?}",
             arg.layout.align,
         );
         arg.make_indirect();
     }
     ```
   - Whenever any safe `#![forbid(unsafe_code)]` program passes `GenericPacked<Inner>`, `TuplePacked`, or `AliasPacked` as an `extern "C"` argument on `i686-pc-windows-msvc`, `arg.layout.is_adt()` is `true`, `max_repr_align = Some(Align(8)) > Align(4)`, and `Align(1) >= Align(8)` panics with a compiler ICE (`rc = 101`).

#### 5.2 Complete Empirical Matrix of Packed/Align/Transparent Rules & Bypasses

Live execution on `rustc 1.98.0-nightly` (`support/probe_results.json`, `part_f_packed_align_bypass_and_x86_win32_ice`, `2026-11-22`) alongside cross-version observations on `rustc 1.99.1` and `rustc 1.102.0-nightly` (`2026-11-21`):

| Case | Minimal Type Pattern | `x86_64` Layout (`align`, `max_repr_align`) | `1.98.0-nightly` (`2026-11-22`) | `1.99.1` (`2026-11-21`) | `1.102.0-nightly` (`2026-11-21`) |
| :--- | :--- | :---: | :--- | :--- | :--- |
| Same-struct conflict | `#[repr(C, packed, align(8))] struct S(u32)` | — | `rc=1`, `E0587` | `rc=1`, `E0587` | `rc=1`, `E0587` |
| Conflicting pack values | `#[repr(C, packed(1), packed(2))] struct S(u32)` | — | `rc=1`, `E0634` | `rc=1`, `E0634` | `rc=1`, `E0634` |
| Packed enum | `#[repr(packed)] enum E { A(u8), B(u16) }` | — | `rc=1`, `E0517` | `rc=1`, `repr(packed)` enum error | `rc=1`, `repr(packed)` enum error |
| Align outer / packed inner | `#[repr(C, align(8))] struct A(P)` (`P` packed) | — | **`rc=0`** (allowed) | **`rc=0`** (allowed) | **`rc=0`** (allowed) |
| Transparent + `align(16)` ZST + `u8` | `#[repr(transparent)] struct T(u8, Az)` | — | `rc=1`, `E0690` (2 non-trivial) | `rc=1`, `E0690` | `rc=1`, `E0690` |
| Transparent all-ZST + `align(16)` ZST | `#[repr(transparent)] struct T((), Az)` | — | **`rc=0`** (1 non-trivial) | **`rc=0`** | **`rc=0`** |
| Concrete `packed` + `align(8)` (`#[allow(aligned_fields_in_packed)]`) | `#[repr(C, packed)] struct Outer(Inner)` | — | `rc=1`, `E0588` (cannot allow) | `rc=1`, `E0588` (cannot allow) | `x86_64`: **`rc=0`** (lint allowed!) |
| **Generic `ty::Param` bypass** (`#![forbid(unsafe_code)]`) | `#[repr(C, packed)] struct GenericPacked<T>(T)` at `Inner` | `Align(1)`, `Some(Align(8))` | `x86_64`: `rc=0`<br>`i686-msvc`: **`rc=101` ICE (`x86_win32.rs:69:13`)** | `x86_64`: `rc=0`<br>`i686-msvc`: **`rc=101` ICE (`x86_win32.rs:73:13`)** | `x86_64`: `rc=0`<br>`i686-msvc`: **`rc=101` ICE (`x86_win32.rs:73:13`)** |
| **Non-generic `ty::Tuple` bypass** (`#![forbid(unsafe_code)]`) | `#[repr(C, packed)] struct TuplePacked((Inner,))` | `Align(1)`, `Some(Align(8))` | `x86_64`: `rc=0`<br>`i686-msvc`: **`rc=101` ICE (`x86_win32.rs:69:13`)** | Same `check_packed_inner` source (`1710`) | Same `check_packed_inner` source (`1769`) |
| **Non-generic `ty::Alias` bypass** (`#![forbid(unsafe_code)]`) | `#[repr(C, packed)] struct AliasPacked(<() as Assoc>::Out)` | `Align(1)`, `Some(Align(8))` | `x86_64`: `rc=0`<br>`i686-msvc`: **`rc=101` ICE (`x86_win32.rs:69:13`)** | Same `check_packed_inner` source (`1710`) | Same `check_packed_inner` source (`1769`) |
| **Non-generic `ty::Array` bypass** (`#![forbid(unsafe_code)]`) | `#[repr(C, packed)] struct ArrayPacked([Inner; 1])` | `Align(1)`, **`None`** | `x86_64`: `rc=0`<br>`i686-msvc`: **`rc=0`** (no ICE!) | Same `layout_of_array_like` (`max_repr_align: None`) | Same `layout_of_array_like` (`max_repr_align: None`) |

#### 5.3 Secondary ABI Consequence: `layout_of_array_like` Drops `max_repr_align` on Non-Packed `#[repr(C)]` Structs

Inspecting `i686-pc-windows-msvc` LLVM IR emitted live by `support/probe_multi_target_layout_and_repr.py` (`part_f_packed_align_bypass_and_x86_win32_ice.i686_msvc_array_max_repr_align_drop_llvm_ir`) reveals a second consequence of `max_repr_align: None` at `compiler/rustc_abi/src/layout.rs:200`:

- `#[repr(C)] pub struct ReprCDirectOuter(pub Inner)` (`size = 8`, `abi_align = 8`, `max_repr_align = Some(Align(8 bytes))`) lowers to an **indirect pointer parameter**:
  ```llvm
  define void @_RNvCs8inY50FQ4rE_14part_f_arr_abi11take_direct(ptr align 8 %_x) unnamed_addr #0
  ```
- `#[repr(C)] pub struct ReprCArrayOuter(pub [Inner; 1])` (`size = 8`, `abi_align = 8`, **`max_repr_align = None`**) lowers to a **4-byte-aligned stack `byval` parameter**:
  ```llvm
  define void @_RNvCs8inY50FQ4rE_14part_f_arr_abi10take_array(ptr byval([8 x i8]) align 4 %0) unnamed_addr #0
  ```

Thus, wrapping a `#[repr(C, align(8))]` struct in a 1-element array inside a non-packed `#[repr(C)]` struct silently changes its `i686-pc-windows-msvc` `extern "C"` passing convention from indirect `ptr align 8` to `byval align 4` — an FFI ABI hazard for any C struct containing a 1-element array of `__declspec(align(8))` elements.

#### 5.4 Mechanized Soundness Fix (`PackedAlignWf` -> `x86Win32AbiInvariant`)

In `support/RustcAbiLayoutAndReprSoundness.lean`, `postMonoPackedCheck_implies_abiAlign_ge_maxReprAlign` proves constructively that replacing definition-site `check_packed_inner` with a **post-monomorphization** structural invariant `PackedAlignWf` (requiring that every packed ADT has `reprAlign = none` and no transitively reachable `#[repr(align)]` along any `max_repr_align`-propagating path, including through `tuple`, `param` instantiations, and normalized `alias` targets) guarantees `abiAlign ≥ m` for every `maxReprAlign = some m` — and hence unconditionally establishes `x86Win32AbiInvariant`. Conversely, if Rust chooses to permit `#[repr(align)]` inside `#[repr(packed)]` (as `1.102.0-nightly`/`HEAD`'s lint downgrade intends for `#[allow(aligned_fields_in_packed)]` and non-`repr(C)` packed structs), then `layout_of_univariant_biased` and `layout_of_union` must either clamp `max_repr_align` to `pack` or clear `max_repr_align` under `pack.is_some()`, because `x86_win32.rs` cannot simultaneously uphold `assert!(align >= max_repr_align)` and allow unpacked `max_repr_align` propagation inside packed ADTs.

---

### 6. `-Z randomize-layout` Seed Determinism and All-ZST `repr(Rust)` Invariance

Basis: source + execution + derived

#### 6.1 Seed Derivation and PRNG Algorithm

In `compiler/rustc_middle/src/ty/mod.rs` (`HEAD` `342d74463:1753-1768`; `1.98.0-nightly:1513-1520`), `TyCtxt::repr_options_of_def` computes:

```rust
let mut field_shuffle_seed = self.def_path_hash(did.to_def_id()).0.to_smaller_hash();
if let Some(user_seed) = self.sess.opts.unstable_opts.layout_seed {
    field_shuffle_seed ^= user_seed;
}
```

Then in `layout_of_univariant_biased` (`compiler/rustc_abi/src/layout.rs:608-639` at `HEAD`, `1111-1139` in `1.98.0-nightly`):
1. `repr.can_randomize_type_layout()` requires `!repr.inhibit_struct_field_reordering()` (excluding `#[repr(C)]`, `#[repr(simd)]`, `#[repr(int)]`, scalable vectors, and linear types) AND `ReprFlags::RANDOMIZE_LAYOUT`.
2. `field_seed` sums `f.randomization_seed` over `fields_excluding_tail` only (so `Foo<T>` and `Foo<dyn Trait>` receive the same shuffle seed for unsizing compatibility).
3. `Xoshiro128StarStar::seed_from_u64(field_seed.wrapping_add(repr.field_shuffle_seed).as_u64())` shuffles `in_memory_order.raw[..end]`.
4. As documented in `layout.rs:621-625` and `rustc_abi/src/lib.rs:99-101` (citing T-lang decisions `rust-lang/reference#2262` and `#2293`), even if future randomization inserts padding, `repr(Rust)` structs with only ZST fields, 1-variant `repr(Rust)` enums with only ZST fields, and 0-variant `repr(Rust)` enums **must remain `0` bytes**.

#### 6.2 Empirical Determinism and Invariance (`part_g_randomize_layout_seed_and_zst_invariance`)

Executed live on `rustc 1.98.0-nightly` (`support/probe_results.json`, `2026-11-22`) alongside `1.102.0-nightly` observations (`2026-11-21`) on `struct RustFive(u64, u64, u64, u64, u64)`, `#[repr(C)] struct ReprCFive(u64, u64, u64, u64, u64)`, `struct AllZst((), [u8; 0], [(); 16])`, `enum SingleZstEnum { Only((), [u8; 0]) }`, and `enum ZeroVariantEnum {}`:

| Invocation Flags | `1.98.0-nightly` `RustFive` Offsets | `1.102.0-nightly` `RustFive` Offsets | `ReprCFive` Offsets | `AllZst` / `SingleZstEnum` / `ZeroVariantEnum` Size |
| :--- | :---: | :---: | :---: | :---: |
| Default (no `-Z randomize-layout`) | `(0, 8, 16, 24, 32)` | `(0, 8, 16, 24, 32)` | `(0, 8, 16, 24, 32)` | `0 / 0 / 0` |
| `-Z randomize-layout -Z layout-seed=1` (run 1) | `(24, 32, 8, 16, 0)` | `(0, 24, 32, 8, 16)` | `(0, 8, 16, 24, 32)` | `0 / 0 / 0` |
| `-Z randomize-layout -Z layout-seed=1` (run 2) | **`(24, 32, 8, 16, 0)`** (exact repeat) | **`(0, 24, 32, 8, 16)`** (exact repeat) | `(0, 8, 16, 24, 32)` | `0 / 0 / 0` |
| `-Z randomize-layout -Z layout-seed=2` | `(16, 8, 0, 32, 24)` | `(24, 8, 0, 32, 16)` | `(0, 8, 16, 24, 32)` | `0 / 0 / 0` |
| `-Z randomize-layout -Z layout-seed=999` | `(32, 8, 0, 16, 24)` | `(8, 32, 16, 24, 0)` | `(0, 8, 16, 24, 32)` | `0 / 0 / 0` |

Two invariants hold empirically: (1) for fixed compiler revision and crate/item path, `-Z layout-seed=<k>` is **100% deterministic across independent compilations** (`run 1 == run 2`), while varying across distinct compiler/crate hashes because `def_path_hash` is XORed with `layout_seed`; (2) `ReprCFive` is completely invariant across all seeds, and all three guaranteed-zero-sized `repr(Rust)` forms remain `0` bytes.

---

### 7. Kernel-Checked Lean `v4.34.1` Formalization and `joshlf/anneal` Trusted-Boundary Seam

Basis: source + execution + derived

#### 7.1 Mechanized Theorems and Sharpness Counterexamples (`support/RustcAbiLayoutAndReprSoundness.lean`)

`support/RustcAbiLayoutAndReprSoundness.lean` (`935` lines, standalone core Lean `v4.34.1`, checked with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) kernel-checks every theorem with zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`, zero `partial def`, and zero `._unsafe_rec`:

| Declaration | Kind | Formal Statement Summary | Verified `#print axioms` |
| :--- | :---: | :--- | :--- |
| `alignTo_add_le_iff_of_dvd` | Theorem 1 | `0 < d → d ∣ sizeT → d ∣ M → (alignTo P d + sizeT ≤ M ↔ P + sizeT ≤ M)` | `[propext, Quot.sound]` |
| `postMonoPackedCheck_implies_abiAlign_ge_maxReprAlign` | Theorem 2 | `PackedAlignWf ty → x86Win32AbiInvariant (computeMonoLayout ty)` (for every `maxReprAlign = some m`, `m > 4 → abiAlign ≥ m`) | `[propext]` |
| `maxAlignedFactor_dvd_size_and_pow2` | Theorem 3 | `0 < size → IsPow2 (maxAlignedFactor size) ∧ maxAlignedFactor size ∣ size ∧ (∀ p, IsPow2 p → p ∣ size → p ∣ maxAlignedFactor size) ∧ alignTo size (maxAlignedFactor size) = size` | `[propext, Quot.sound]` |
| `vectorTypeLayout_packed_nonpow2_sound` | Corollary | Non-power-of-two `#[repr(simd, packed)]` demotes to `.memory`, assigns `align = maxAlignedFactor rawSize`, and preserves `size = rawSize` | `[propext, Quot.sound]` |
| `nine_target_alignment_laws` | Matrix Law | All 11 defining `(size, align, secondOffset)` entries across the 9 targets (`i686-linux`, `i686-msvc`, `wasm32`, `s390x`, `thumbv7m`, `x86_64`, `aarch64`, `riscv64gc`) | none (`[]`) |
| `ce1_generic_packed_bypasses_def_check_violates_win32_abi_inv` | Counterexample 1 | `ConcretePacked` rejected (`false`), `GenericPacked<T>` passes definition check (`true`), instantiated `GenericPacked<Inner>` yields `⟨1, some 8⟩`, violating `x86Win32AbiInvariant` | `[propext]` |
| `ce1_corollaries_tuple_alias_ice_and_array_mra_drop` | Corollaries | `TuplePacked` and `AliasPacked` bypass `checkPackedDefPasses` and violate `x86Win32AbiInvariant` (`⟨1, some 8⟩`); `ArrayPacked` bypasses check and drops `maxReprAlign` to `none` (`⟨1, none⟩`) | `[propext]` |
| `ce2_simd_packed_pow2_ignores_pack_vs_nonpow2_demotes_memory` | Counterexample 2 | `SimdPackedF32x4 = SimdF32x4 = ⟨16, 16, .simdVector⟩`, whereas `SimdPackedF32x3 = ⟨12, 4, .memory⟩`, `SimdPackedF32x6 = ⟨24, 8, .memory⟩`, `SimdPackedU8x3 = ⟨3, 1, .memory⟩` | none (`[]`) |
| `ce3_maybe_unsized_suppresses_niche_bias_end_inflating_enum_8_to_12` | Counterexample 3 | Identical `[u32, bool, u8, ()]` under `.alwaysSized` gets niche at offset `5` (`enum = 8 B`), under `.maybeUnsized` gets niche at offset `4` (`enum = 12 B`); likewise `FixedEdge` (`8 B`) vs `MaybeDstEdge` (`12 B`) | `[propext]` |
| `ce4_uninhabited_align16_zst_variant_forces_size_16_align_16` | Counterexample 4 | `Dead1Zst = (1, 1)`, `ReprCDead1Zst = (8, 4)`, `DeadPayload64 = (65, 1)`, `DeadAlign16Zst = (16, 16)` | none (`[]`) |

#### 7.2 Trusted-Boundary Interface in `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`

Direct inspection of `trusted/lean/Trusted/MirAst.lean` and `trusted/lean/Trusted/MirSemantics.lean` at `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes the exact scope boundary between `anneal`'s current MIR trusted semantics and `rustc_abi`'s full multi-target layout algebra:

1. **64-bit target lock:** `Trusted.MirSemantics.initState` (`MirSemantics.lean:799-802`) fails closed with `.error .unsupported` unless `p.pointerWidthBits = 64 && p.mirProfileVersion = 1`, and `Trusted.MirAst.IntWidth.byteSize` (`MirAst.lean:165-170`) hardcodes `.isize => 8`. None of the four 32-bit targets (`i686-unknown-linux-gnu`, `i686-pc-windows-msvc`, `wasm32-unknown-unknown`, `thumbv7m-none-eabi`) nor `s390x`'s `8`-byte `u128` alignment are representable without parameterizing `Program` by a `TargetDataLayout` descriptor (`ptrSize`, `i64Align`, `f64Align`, `i128Align`, `aggregateAlign`).
2. **Admitted ADT surface:** `Trusted.MirAst.MirTy` (`MirAst.lean:312-320`) currently models `bool`, `int`, `unit`, `never`, fieldless `enum` (`EnumTy` with explicit `EnumTagRepr`: `.zeroSized` vs `.scalar width signed`), `tuple`, `ref`, and `rawPtr`. All non-fieldless ADTs (`#[repr(C)]` structs, `#[repr(packed)]` / `#[repr(align)]` structs, unions, data-carrying/niche-packed enums, `#[repr(simd)]` types, and floats) map to `MirTy.unsupported` and fail closed (`FaultKind.unsupported`).
3. **Requirements for extending the trusted boundary to multi-target ADTs & FFI:** Any extension of `Trusted.MirAst` / `Trusted.MirSemantics` (or a verified `rustc_abi` layout/FnAbi pass) to structs, unions, SIMD, and data-carrying enums must:
   - Carry target-specific `TargetDataLayout` alignments explicitly rather than deriving alignment from `IntWidth.byteSize`;
   - Distinguish `StructKind::AlwaysSized` from `StructKind::MaybeUnsized` when mirroring `rustc_abi` niche offsets;
   - Preserve `absent(fields) = uninhabited && all is_1zst` (rejecting unsound optimization assumptions that drop non-1-ZST uninhabited variants);
   - Record `max_repr_align` alongside `abi_align` AND either enforce post-monomorphization `PackedAlignWf` or explicitly specify `max_repr_align` clamping under `repr(packed)` and array propagation in `layout_of_array_like` so ABI lowering cannot inherit `rustc`'s `x86_win32` ICE or `ReprCArrayOuter` ABI divergence.

## Boundaries

- **Known not to apply:**
  - `alignTo_add_le_iff_of_dvd` (Theorem 1) does **not** claim that `StructKind::MaybeUnsized` preserves outer enum sizes (explicitly falsified by `ce3`, where `NicheBias::End` suppression inflates `8 B -> 12 B`), nor that tail pinning preserves struct size when the prefix contains internal padding that an unconstrained sort would have filled using the tail field.
  - The `i686-pc-windows-msvc` `rc = 101` ICE (`x86_win32.rs`) does **not** occur on `x86_64-unknown-linux-gnu` (where the same safe `#![forbid(unsafe_code)]` crates compile cleanly with `rc = 0` and emit `align = 1, max_repr_align = Some(8)`), nor does it occur for `ArrayPacked([Inner; 1])` on `i686-pc-windows-msvc` (because `layout_of_array_like` clears `max_repr_align` to `None`).
  - `#[repr(simd, packed)]` does **not** reduce alignment for power-of-two lane counts (`SimdPackedF32x4` remains `16 B`, `align 16`, `SimdVector`).
  - `support/RustcAbiLayoutAndReprSoundness.lean` is a standalone mathematical mechanization of the audited `rustc_abi` / `check_packed_inner` / `x86_win32` algorithms; it does **not** formally verify `rustc`'s Rust implementation binary nor import `joshlf/anneal`'s `Trusted.MirSemantics`.
  - Cross-version `-Z layout-seed=<k>` permutations are **not** stable across distinct `rustc` versions or crate names because `field_shuffle_seed` mixes `def_path_hash(did)` with `layout_seed`.
- **Not examined:**
  - Targets outside the nine listed triples (e.g., 16-bit targets such as `msp430-none-elf`, CHERI fat-pointer data layouts, `powerpc64-unknown-linux-gnu`, `sparc64`, or `avr`), scalable SVE/RVV vectors (`#[rustc_scalable_vector]`), coroutine state-machine layout packing (`layout/coroutine.rs`), and `#[repr(C)]` bitfields or C++ Clang `TargetInfo.cpp` side-by-side comparison for `ReprCArrayOuter`.
  - Live execution of `1.99.1` and `1.102.0-nightly` on the three newly isolated non-generic bypasses (`TuplePacked`, `AliasPacked`, `ArrayPacked`) and `ReprCArrayOuter` LLVM IR: those four variants were executed live on `1.98.0-nightly` (`2026-11-22`) and confirmed by direct source inspection of `check_packed_inner` and `layout_of_array_like` at `1.99.1`, `1.102.0-nightly`, and `HEAD`, while `GenericPacked<Inner>` was empirically verified across `1.98.0-nightly`, `1.99.1`, and `1.102.0-nightly`.
  - Runtime hardware execution of generated `i686-pc-windows-msvc` binaries on Windows to test MSVC C++ caller/callee ABI mismatch for `ReprCArrayOuter([Inner; 1])`.
- **Unknown:**
  - Whether upstream `rust-lang/rust` intends to fix the `x86_win32.rs` ICE by (a) restoring post-monomorphization `PackedAlignWf` rejection, (b) clamping/clearing `max_repr_align` inside packed structs/unions in `rustc_abi/src/layout.rs`, or (c) relaxing the assertion in `x86_win32.rs`, and whether `layout_of_array_like`'s `max_repr_align: None` is intentional or a bug relative to Clang's `X86_32ABIInfo`.
- **Unsupported:**
  - `#[repr(packed)]` on `enum` types (rejected at compile time across all four `rust-lang/rust` revisions and rejected with `LayoutCalculatorError::ReprConflict` in `enum_layout.rs:29-31`).
  - `#[repr(packed, align(N))]` on the same struct/union (`E0587`) and conflicting `#[repr(packed(N), packed(M))]` (`E0634`).
  - Multi-target (`pointerWidthBits != 64`) and non-fieldless ADT types in `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`Trusted.MirSemantics.initState` returns `.error .unsupported`).

## Evidence

### Primary Git Source Citations (`2026-11-22`)

1. **`rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`HEAD`, `2026-11-22T00:04:39Z`):**
   - `compiler/rustc_abi/src/lib.rs`:
     - `ReprFlags` (`ABI_UNOPTIMIZABLE`, `FIELD_ORDER_UNOPTIMIZABLE`, `RANDOMIZE_LAYOUT`), `ReprOptions` (`inhibit_enum_layout_opt`, `inhibit_newtype_abi_optimization`, `inhibit_struct_field_reordering`, `can_randomize_type_layout`, `inhibits_union_abi_opt`): lines `87-250`.
     - `TargetDataLayout` defaults (`i64_align = 32`, `i128_align = 32`, `f64_align = 64`) and `parse_from_llvm_datalayout_string` (`i128_align_src = 64` fallback): lines `322-389`, `507-650`.
     - `TargetDataLayout::rust_vector_align`: lines `750-753`.
     - `Size::align_to`: lines `940-943`; `Align::max_aligned_factor`: lines `1221-1223`.
   - `compiler/rustc_abi/src/layout.rs`:
     - `absent`: lines `91-102`; `enum NicheBias`: lines `105-108`.
     - `LayoutCalculator::layout_of_array_like` (`max_repr_align: None`): lines `183-205` (specifically line `200`).
     - `LayoutCalculator::layout_of_simd_type`: lines `226-239`; `vector_type_layout`: lines `979-1035` (`PackedFixed if !count.is_power_of_two()` at line `1010-1012`).
     - `LayoutCalculator::layout_of_univariant` (`!matches!(kind, StructKind::MaybeUnsized)` `NicheBias::End` guard): lines `274-342` (guard at line `296`).
     - `LayoutCalculator::layout_of_struct_or_enum`: lines `344-403` (`absent` filter at line `361`).
     - `LayoutCalculator::layout_of_union`: lines `405-535` (strict `common_abi != field_abi` at lines `451-453`, alignment gate at lines `489-493`, `max_repr_align` propagation at line `438`).
     - `LayoutCalculator::layout_of_univariant_biased`: lines `591-936` (`end = fields.len() - 1` at line `609`; `Xoshiro128StarStar` randomization & all-ZST comment at lines `621-639`; `NicheBias` alignment group key at lines `655-691`; `field_align` clamped by `pack` while `max_repr_align` propagates unclamped at lines `780-784`; `optimize_abi` asymmetric `Scalar` vs. `ScalarPair` dispatch at lines `828-899`).
   - `compiler/rustc_abi/src/layout/enum_layout.rs`:
     - `layout_of_enum` (packed enum `ReprConflict`): lines `15-58`.
     - `calculate_tagged_layout` (`necessary_discriminants` filter and `StructKind::Prefixed` variant sizing): lines `339-471`.
     - `try_fit_variants_around_niche_tag`: lines `480-520`; `calculate_niche_filling_layout`: lines `558-664`.
   - `compiler/rustc_ty_utils/src/layout.rs`:
     - Tuple `StructKind::MaybeUnsized`: lines `612-617`; SIMD dispatch: lines `647-698`; ADT `maybe_unsized` identity-check and unsizing invariance debug check: lines `754-815`.
   - `compiler/rustc_hir_analysis/src/check/check.rs`:
     - `check_packed` (`E0634`, `E0587`, `repr.c()`-gated `ALIGNED_FIELDS_IN_PACKED` lint): lines `1668-1754`.
     - `check_packed_inner` (`def.repr().c()` + `ty::Adt`-only recursion on `instantiate_identity().skip_norm_wip()`): lines `1756-1782`.
     - `check_transparent` (`E0690`, `is_1zst` check): lines `1784-1930`.
   - `compiler/rustc_lint_defs/src/builtin.rs`:
     - `ALIGNED_FIELDS_IN_PACKED` (`Deny` lint): lines `5858-5862`.
   - `compiler/rustc_middle/src/ty/mod.rs`:
     - `repr_options_of_def` (`field_shuffle_seed = def_path_hash ^ layout_seed`): lines `1753-1768`.
   - `compiler/rustc_target/src/callconv/x86_win32.rs`:
     - `compute_abi_info` (`assert!(arg.layout.align >= max_repr_align, ...)`): lines `72-87` (assertion at line `82`).
   - `compiler/rustc_target/src/spec/targets/*.rs`:
     - `x86_64_unknown_linux_gnu.rs:33-34`, `i686_unknown_linux_gnu.rs:36-38`, `i686_pc_windows_msvc.rs:32-34`, `wasm32_unknown_unknown.rs:46`, `s390x_unknown_linux_gnu.rs:26`, `thumbv7m_none_eabi.rs:15`, `aarch64_unknown_linux_gnu.rs:15`, `aarch64_apple_darwin.rs:15`, `riscv64gc_unknown_none_elf.rs:8`.

2. **Cross-Version `rust-lang/rust` Source Verification (`2026-11-22`):**
   - `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`): `compiler/rustc_abi/src/layout.rs` (`absent`: L89, `layout_of_array_like`: L198, `univariant`: L266, `univariant_biased`: L1094, `Xoshiro128StarStar`: L1131, `optimize_abi`: L1329/1348, `vector_type_layout`: L1476/1510); `compiler/rustc_hir_analysis/src/check/check.rs` (`check_packed`: L1613, `E0588`: L1644, `check_packed_inner`: L1678, `check_transparent`: L1706); `compiler/rustc_target/src/callconv/x86_win32.rs` (`assert!`: L69).
   - `58cf8f9c35b355199727627d07ae34a4e2846d67` (`rustc 1.99.1`, `2026-10-13`): `compiler/rustc_abi/src/layout.rs` (`absent`: L89, `univariant`: L266, `univariant_biased`: L1081, `Xoshiro128StarStar`: L1123, `optimize_abi`: L1321/1340, `vector_type_layout`: L1468/1502); `compiler/rustc_hir_analysis/src/check/check.rs` (`check_packed`: L1622, `E0588`: L1663, `check_packed_inner`: L1697, `check_transparent`: L1725, `E0690`: L1849); `compiler/rustc_target/src/callconv/x86_win32.rs` (`assert!`: L73).
   - `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, `2026-11-11`): `compiler/rustc_abi/src/layout.rs` (`absent`: L90, `layout_of_array_like`: L199, `layout_of_univariant`: L273, `layout_of_univariant_biased`: L590, `Xoshiro128StarStar`: L632, `optimize_abi`: L827/846, `vector_type_layout`: L978/1010); `compiler/rustc_hir_analysis/src/check/check.rs` (`check_packed`: L1666, `ALIGNED_FIELDS_IN_PACKED`: L1708, `check_packed_inner`: L1754, `check_transparent`: L1782, `E0690`: L1907); `compiler/rustc_target/src/callconv/x86_win32.rs` (`assert!`: L73).

3. **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19`, inspected `2026-11-22`):**
   - `trusted/lean/Trusted/MirAst.lean`: `IntWidth.byteSize` (L165–170), `EnumTagRepr` (L222–224), `EnumTy` (L265–270), `MirTy` (L312–320).
   - `trusted/lean/Trusted/MirSemantics.lean`: `initState` (`p.pointerWidthBits = 64 && p.mirProfileVersion = 1`, L799–802), `isPrimitiveReadableTy` (L834–836).

### Retained Support Material and Execution Logs

All support artifacts are self-contained under `support/`:

1. **`support/probe_multi_target_layout_and_repr.py`:** Standalone Python 3.10+ probe harness executing all seven parts (`part_a`–`part_g`) inside a hermetic `tempfile.TemporaryDirectory()` with path scrubbing and zero external Python dependencies.
2. **`support/probe_results.json` (`2026-11-22T09:07:51Z`):** Verbatim JSON output produced by executing `support/probe_multi_target_layout_and_repr.py` on `rustc 1.98.0-nightly (14210df0e 2026-05-31, LLVM 22.1.6)`, recording:
   - All `9 x 8 = 72` target-type layout entries (`part_a`);
   - All `7` SIMD packed vs. unpacked layouts (`part_b`);
   - Native runtime `offset_of!` / `size_of` output including `FixedPureNiche` vs. `MaybeDstPureNiche<()>` (`part_c`);
   - All `4` uninhabited-variant enum layouts (`part_d`);
   - All `8` `#[repr(C)]` newtype and union ABI optimization layouts (`part_e`);
   - All `16` packed/align/transparent diagnostics, `#[rustc_dump_layout(debug)]` `max_repr_align` extracts, `rc = 101` ICE backtrace headers for `GenericPacked`, `TuplePacked`, and `AliasPacked`, and `i686-pc-windows-msvc` LLVM IR signatures for `take_direct` (`ptr align 8`) vs. `take_array` (`ptr byval([8 x i8]) align 4`) (`part_f`);
   - All `5` `-Z randomize-layout` / `-Z layout-seed` runtime outputs (`part_g`).
3. **Prior Cross-Version Execution Observations (`2026-11-21T20:26:59Z`):**
   - `rustc 1.99.1 (58cf8f9c3 2026-10-13, LLVM 23.1.1)`: confirmed `E0588` hard error on concrete `#[allow(aligned_fields_in_packed)]` (`rc = 1`), `GenericPacked<Inner>` `rc = 0` on `x86_64-unknown-linux-gnu`, and `rc = 101` ICE at `/rustc-dev/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_target/src/callconv/x86_win32.rs:73:13`.
   - `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11, LLVM 23.1.5)`: confirmed all nine target layouts (`part_a`), all seven SIMD layouts (`part_b`), `part_c` runtime offsets (`ENUM_FIXED_SZ=8`, `ENUM_MAYBEDST_SZ=12`), `part_d` layouts, `part_e` `ReprCWrapScalar` vs. `ReprCWrapTuplePair`/`ReprCTwoScalars`, `part_f` concrete `#[allow(aligned_fields_in_packed)]` compiling (`rc = 0`) on `x86_64` and `GenericPacked<Inner>` hitting `rc = 101` ICE at `/rustc-dev/3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1/compiler/rustc_target/src/callconv/x86_win32.rs:73:13`, and `part_g` seed determinism (`seed=1` run 1 & run 2 both `RUST=(0,24,32,8,16)`, `REPRC=(0,8,16,24,32)`, `ALLZST_SZ=0`).
4. **`support/RustcAbiLayoutAndReprSoundness.lean` (`2026-11-22`):** `935`-line standalone Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) module verified with exit code `0`, `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, and clean `#print axioms` output (`[]`, `[propext]`, or `[propext, Quot.sound]` only).

### Related Corpus Reports

This package complements (without duplicating) existing layout and ABI reports in this corpus:
- `repr-c-layout-algebra-dst-tails-and-enum-tags`: formal `Nat` algebra for `#[repr(C)]` structs, unions, C-enum tags, and flat slice-tailed DSTs.
- `enum-niche-layout-guarantees-and-validity-invariants`: abstract byte-level niche-layout guarantees and validity invariants.
- `packed-field-projections-aligned-staging-and-alignment-check-completeness-across-shims`: MIR packed-field projection staging and alignment-check completeness across shims.
- `scalarpair-register-lowering-refinement-init-uniform-scalars-and-provenance-boundaries`: `ScalarPair` register lowering and provenance boundaries.

## Revalidation

Each claim class admits a narrow, fast (<10 s) discriminating check against any newer `rust-lang/rust` toolchain or Lean release:

1. **Rerun the complete 7-part multi-target `rustc` probe on any nightly `rustc` (no cross-target `rust-std` required for `part_a`, `part_b`, `part_d`, `part_f`):**
   ```console
   python3 reports/rustc-multi-target-layout-calculator-repr-algebra-and-packed-align-soundness/support/probe_multi_target_layout_and_repr.py --rustc /path/to/nightly/rustc --out /tmp/reval_probe_results.json
   ```
   Diff `/tmp/reval_probe_results.json` against `support/probe_results.json` across `part_a`–`part_g`. Specifically inspect:
   - Whether `part_f.generic_param_bypass__i686-pc-windows-msvc`, `tuple_wrapper_bypass__i686-pc-windows-msvc`, and `alias_wrapper_bypass__i686-pc-windows-msvc` still exit with `rc = 101` (or have been fixed to `rc = 1` post-mono error or `rc = 0` with clamped `max_repr_align`);
   - Whether `part_f.bypass_layout_fields_x86_64.ReprCArrayOuter.max_repr_align` remains `None` and `i686_msvc_array_max_repr_align_drop_llvm_ir.signatures.take_array` remains `byval([8 x i8]) align 4`;
   - Whether `part_f.concrete_packed_containing_align_allow_lint` returns `rc = 1` (`E0588`) or `rc = 0` (`aligned_fields_in_packed` lint);
   - Whether `part_c` still reports `ENUM_FIXED_PURE_SZ=8 ENUM_MAYBEDST_PURE_SZ=12`.

2. **Re-check the Lean `v4.34.1` kernel formalization and `#print axioms` output:**
   ```console
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     reports/rustc-multi-target-layout-calculator-repr-algebra-and-packed-align-soundness/support/RustcAbiLayoutAndReprSoundness.lean
   ```
   Confirm exit code `0`, zero warnings, and that every `#print axioms` line lists at most `[propext, Quot.sound]` (zero `Classical.choice`, zero `sorryAx`, zero `Lean.ofReduceBool`).

3. **Source-diff upstream `rust-lang/rust` hotspots before relying on layout assumptions on newer commits:**
   Diff the following narrow regions against `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`:
   - `compiler/rustc_abi/src/layout.rs` (`absent`, `layout_of_array_like`, `layout_of_univariant`, `layout_of_union`, `layout_of_univariant_biased`, `vector_type_layout`);
   - `compiler/rustc_abi/src/layout/enum_layout.rs` (`try_fit_variants_around_niche_tag`, `calculate_tagged_layout`);
   - `compiler/rustc_hir_analysis/src/check/check.rs` (`check_packed`, `check_packed_inner`, `check_transparent`);
   - `compiler/rustc_target/src/callconv/x86_win32.rs` (`compute_abi_info`);
   - `compiler/rustc_abi/src/lib.rs` (`parse_from_llvm_datalayout_string` `i128_align_src` fallback and `Align::max_aligned_factor`).

4. **Check `joshlf/anneal` trusted-boundary evolution:**
   Inspect `trusted/lean/Trusted/MirAst.lean` (`IntWidth.byteSize`, `MirTy`) and `trusted/lean/Trusted/MirSemantics.lean` (`initState`) for any change lifting the `pointerWidthBits = 64` guard or adding ADT layout descriptors.
