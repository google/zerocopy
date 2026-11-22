# `rustc` `union` Layout, `Scalar::Union` Niche and Validity Erasure, Unconditional Inhabitedness, `#[repr(transparent)]` ABI Forwarding, and Byte-Level Partial Overwrite Semantics

## Summary

In `rustc`, every `union` computes its layout through `LayoutCalculator::layout_of_union`, which preserves register-passing mechanics only across uniformly aligned, representation-compatible non-ZST fields while systematically erasing value-level validity invariants, scalar niches, LLVM `noundef` / `!range` / `nonnull` guarantees, and type-level uninhabitedness. Primary-source inspection of `rust-lang/rust` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM `23.1.5`), live compiler/IR/assembly/`Miri` execution on `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`, `x86_64-unknown-linux-gnu`) captured in [`support/probe_results.json`](support/probe_results.json), and a kernel-checked constructive Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) mechanization in [`support/UnionLayoutValidityAndByteOverwrite.lean`](support/UnionLayoutValidityAndByteOverwrite.lean) (`43` theorems, zero `sorry` placeholders, zero `Classical.choice`, `omega`, `bv_decide`, or `native_decide` dependencies) establish five core invariants:

1. **`Scalar::Union` Niche and `noundef` Erasure Without Intersecting Field Niches (`layout_of_union`).** Every non-ZST field in `layout_of_union` (`compiler/rustc_abi/src/layout.rs:404-534`) is lowered through `field.backend_repr.to_union()` (`compiler/rustc_abi/src/lib.rs:1975-1993`), mapping `Scalar::Initialized { value, valid_range }` to `Scalar::Union { value }`. That transformation sets `is_uninit_valid() == true` and `is_always_valid() == true` (`lib.rs:1661-1675`), suppressing LLVM `noundef`, `range(...)` / `!range`, and `nonnull` attributes at register boundaries (`compiler/rustc_ty_utils/src/abi.rs:318-338`, `compiler/rustc_codegen_llvm/src/abi.rs:504-520`), while `layout_of_union` unconditionally sets `largest_niche: None` (`layout.rs:525`). Even when every field is `NonZero<u64>` (`union TwoNonZero { a: NonZero<u64>, b: NonZero<u64> }`), `size_of::<TwoNonZero>() == 8`, `size_of::<Option<TwoNonZero>>() == 16`, constructing an all-zero or uninitialized `TwoNonZero` value passes `Miri` (`miri_rc = 0`), reading `.a` on all-zero bytes triggers immediate UB (`miri_rc = 1`: `encountered 0, but expected something greater or equal to 1`), and LLVM emits `define i64 @u_sig_1_two_nonzero(i64 %u)` with neither `noundef` nor `range`. Whenever non-ZST fields yield differing `to_union()` ABIs (`Err(AbiMismatch)`), `#[repr(C)]` sets `inhibits_union_abi_opt() == true` (`lib.rs:245-247`), or final union alignment mismatches `repr.scalar_platform_align(dl)` (e.g., `#[repr(align(16))]` or `#[repr(packed)]`), `backend_repr` demotes to `BackendRepr::Memory { sized: true }`.
2. **`#[repr(transparent)]` on `union` vs. `struct` (`MaybeUninit<T>` Semantics).** Unlike a `#[repr(transparent)] struct PlainWrap(NonZero<u64>)`—which computes layout through the struct path, retains `Scalar::Initialized`, has `size_of::<Option<PlainWrap>>() == 8`, fails `Miri` on all-zero construction (`miri_rc = 1`), and lowers to `define noundef range(i64 1, 0) i64 @u_sig_0_plain_wrap(i64 noundef range(i64 1, 0) %w)`—`rustc_ty_utils::layout::layout_of` dispatches ALL `def.is_union()` ADTs directly to `layout_of_union` (`compiler/rustc_ty_utils/src/layout.rs:701-710`), and `ReprOptions::inhibits_union_abi_opt` inspects only `self.c()`. Therefore `#[repr(transparent)]` on a `union` (`core::mem::MaybeUninit<T>` and `#![feature(transparent_unions)]` `TransNonZero` / `TransF64`) forwards the C ABI of its sole non-trivial field (passing `TransNonZero` in integer register `i64` and `TransF64` in SSE `double` `%xmm0`), while **still** calling `.to_union()`, keeping `largest_niche: None` (`size_of::<Option<TransNonZero>>() == 16`, `Option<MaybeUninit<NonZero<u64>>> == 16`), allowing zero/uninit values (`miri_rc = 0`), and omitting parameter `noundef` and `range`. By contrast, `#[repr(C)] union ReprCF64 { f: f64 }` inhibits union ABI optimization (`Memory`), causing `adjust_for_rust_abi` (`size <= ptr_size`) to cast the 8-byte aggregate to `i64 %0` (`movq %rdi, %xmm0`) in Rust calls instead of passing `%xmm0` directly.
3. **Unconditional Union Inhabitedness (`uninhabited: false`).** `layout_of_union` hardcodes `uninhabited: false` (`layout.rs:526`), matching `Ty::inhabited_predicate` (`compiler/rustc_middle/src/ty/inhabitedness/mod.rs:135-136`: `Adt(adt, _) if adt.is_union() => InhabitedPredicate::True`) and `OpsemInhabitedCtx::is_inhabited_adt_ty` (`inhabitedness/mod.rs:355-358`: `return true`). Consequently, `union NeverUnion { f: Infallible }` and `union BangUnion { b: ! }` are **inhabited zero-sized types** (`size_of == 0`, `align == 1`), inflating `Option<NeverUnion>` and `Option<BangUnion>` to `1` byte (`size_of::<Option<Infallible>>() == 0`), allowing `MaybeUninit::<NeverUnion>::uninit().assume_init()` cleanly (`miri_rc = 0`), and deferring uninhabited UB strictly to typed field projections (`unsafe { u.f }` or `unsafe { u.b }`, `miri_rc = 1`).
4. **CTFE / `Miri` `FieldsShape::Union` Validity, Padding Stripping, and Partial Overwrites.** During runtime and CTFE value validation (`ValidityVisitor::visit_union` in `compiler/rustc_const_eval/src/interpret/validity.rs:1307-1337`), unions execute zero recursive field checks (`FieldsShape::Union` never visits fields). Instead, validation computes `union_data_range` (the union of initialized data intervals across all fields; `validity.rs:1178-1246`), stripping pure inter-field padding holes to uninitialized on copy/retag (`union_data_range_covered_byte_preserved_ok`, `miri_rc = 0` on `FullCoverUnion { pair: (u8, u16), raw: [u8; 4] }`; `union_data_range_padding_strip_ub`, `miri_rc = 1` when reading byte `1` after copying `PadHoleUnion { pair: (u8, u16) }`), and rejects `&UnsafeCell` inside a non-ZST `!Freeze` union pointing to read-only memory (`ctfe_mode` check: `const` value `ok`, `&CellUnion` promoted temporary `E0492`, raw-transmuted `static BAD_REF: &CellUnion` `E0080` in read-only memory). Under partial writes (`u.lo_u8 = 0x99` over `u.full_u32 = 0x11223344`, and `p.lo_u8 = 0xEE` over `PairLo { pair: (u32, &'static u8), lo_u8: u8 }`), `Miri` mutates only `[0..1)` and preserves sibling bytes and pointer provenance in `[1..size)`, producing `0x11223399` in both `Miri` and `rustc -O2` (`FULL=0x11223399`), while leaving upper bytes `[1..4)` uninitialized if written into an uninitialized union (`miri_rc = 1` on `u.full_u32`).
5. **SysV x86-64 Eightbyte Classification, Indirect `dead_on_return` Passing, and LLVM 23 `nofree` Evolution.** Under `extern "C"` on `x86_64-unknown-linux-gnu` (`compiler/rustc_target/src/callconv/x86_64.rs:34-119`), `classify_arg` iterates every union field and merges overlapping eightbyte classes via `Ord::min` (`Int < Sse`), classifying `IntOrFloatC { i: u64, f: f64 }` as `i64 %0` (`%rdi`, no `noundef`), while under Rust ABI (`adjust_for_rust_abi`, `callconv/mod.rs:886-894`) small `BackendRepr::Memory` unions (`<= ptr_size`) cast directly to integer `i64` / `i32`. Over-aligned 16-byte unions (`OveralignedU64`) remain `Memory` and pass indirectly via pointer with `ptr dead_on_return noalias noundef readonly align 16 captures(none) dereferenceable(16) %u` on `rustc 1.98.0-nightly` (LLVM `22.1.6`), and add explicit `nofree` on `rust-lang/rust@3ef0c22cd` (`LLVM 23.1.5`: `ptr noalias nofree noundef readonly align 16 captures(none) dead_on_return dereferenceable(16) %u`) because `rustc_target::callconv::indirect_pass_mode` added `ArgAttribute::NoFree` once LLVM 23 decoupled `dereferenceable` from `nofree` (`llvm-project/pull/204795`).

---

## Applicability

This report documents the exact technical relationship across the five durable subjects pinned in [`REPORT.json`](REPORT.json):

| Subject | Pinned Identity | Role in Report |
| :--- | :--- | :--- |
| Compiler source (`rust-lang/rust`) | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | Authoritative primary source for every cited file and line range across `rustc_abi`, `rustc_middle`, `rustc_hir_analysis`, `rustc_ty_utils`, `rustc_target`, `rustc_codegen_llvm`, `rustc_const_eval`, and `core::mem::MaybeUninit`, plus `rustc 1.102.0-nightly` / LLVM `23.1.5` IR/size observations on `x86_64-unknown-linux-gnu`. |
| Live execution toolchain (`rust-lang/rust`) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, LLVM `22.1.6`, `x86_64-unknown-linux-gnu`) | Live execution engine for [`support/probe_union_abi_inhabitedness_and_bytes.py`](support/probe_union_abi_inhabitedness_and_bytes.py) producing [`support/probe_results.json`](support/probe_results.json) (all `12` `Miri` programs, `19` type layouts, `10` `-Zprint-type-sizes` dumps, `6` compile checks, and `12` unmerged/optimized LLVM IR and x86-64 assembly signatures). |
| Anneal (`joshlf/anneal`) | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Downstream verification architecture audited at `trusted/lean/Trusted/MirAst.lean`, `trusted/correspondence/Trusted/Correspondence.lean`, and `vendor/lean-miri/Miri/{ABI/RuntimeLayout.lean, Interpreter/ValidityVisitor.lean}`. |
| `zerocopy` (`google/zerocopy`) | `907b9175fee081872ec883ca4709e6ad922f8ed0` (`v0.8.64`) | Downstream consumer audited at `zerocopy/src/lib.rs` and `zerocopy/zerocopy-derive/src/derive/{from_bytes.rs, into_bytes.rs}` for union soundness and padding contracts. |
| Lean 4 kernel (`leanprover/lean4`) | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Kernel checker verifying [`support/UnionLayoutValidityAndByteOverwrite.lean`](support/UnionLayoutValidityAndByteOverwrite.lean). |

### Cross-Revision Equivalence and Observed Divergence (`14210df0e` vs. `3ef0c22cd`)

1. **Core union layout, inhabitedness, `Scalar::Union`, and `visit_union` semantics:** Identical across `14210df0e` (`LLVM 22.1.6`) and `3ef0c22cd` (`LLVM 23.1.5`). Every overlapping size calculation (`NeverUnion = 0`, `Option<NeverUnion> = 1`, `Option<TwoNonZero> = 16`, `Option<TransNonZero> = 16`), all overlapping `Miri` exit codes (`0` vs. `1`), and register/indirect classifications (`i64` without `noundef` for `TwoNonZero` / `TransNonZero`, `i64` via cast for `IntOrFloatRust` / `IntOrFloatC`) match across both revisions.
2. **LLVM 23 `nofree` decoupling (version-specific IR difference):** Directly comparing `compiler/rustc_target/src/callconv/mod.rs` and `compiler/rustc_codegen_llvm/src/abi.rs` between `14210df0e` (`LLVM 22.1.6`) and `3ef0c22cd` (`LLVM 23.1.5`) explains the exact parameter-attribute delta observed on `OveralignedU64`:
   - At `14210df0e` (`callconv/mod.rs:401-418`, `codegen_llvm/src/abi.rs:75-96`), LLVM `22` still implied `nofree` from `dereferenceable`, so `indirect_pass_mode` set `[NoAlias, CapturesAddress, NonNull, NoUndef]` without `NoFree`, emitting `ptr dead_on_return noalias noundef readonly align 16 captures(none) dereferenceable(16) %u`.
   - At `3ef0c22cd` (`callconv/mod.rs:425-444`, `codegen_llvm/src/abi.rs:82-94`), after `llvm-project/pull/204795` decoupled `dereferenceable` from `nofree` in LLVM `23`, `indirect_pass_mode` added `.set(ArgAttribute::NoFree)` and `codegen_llvm` gated `dereferenceable` on `llvm_version >= (23, 0, 0) || regular.contains(ArgAttribute::NoFree)`, emitting explicit `nofree` alongside `dead_on_return` and `dereferenceable(16)`: `ptr noalias nofree noundef readonly align 16 captures(none) dead_on_return dereferenceable(16) %u`.
3. **Diagnostic wording detail:** In `two_nonzero_union_read_zero_field_ub`, `rustc 1.98.0-nightly` displays `core::num::NonZero<u64>`, while `rustc 1.102.0-nightly` displays `std::num::NonZero<u64>` (alias re-export); both exit with `miri_rc = 1` and cite `at .0.0, encountered 0, but expected something greater or equal to 1`.

### Representation, Target, and Formalization Scope

- **Target architecture:** Empirical probes apply to `x86_64-unknown-linux-gnu` (`64`-bit little-endian pointers, SysV AMD64 C ABI).
- **Type restrictions:** Rust unions cannot have unsized fields (`check_type_defn(..., all_sized = true)` in `compiler/rustc_hir_analysis/src/check/check.rs:122`, `layout_of_union` returning `UnexpectedUnsized` at `layout.rs:433`), cannot simultaneously carry `#[repr(packed)]` and `#[repr(align(N))]` (`rustc_ty_utils/src/layout.rs:702-708`), forbid non-`Copy` fields lacking `ManuallyDrop<T>` (`E0740` unless `BikeshedGuaranteedNoDrop` holds, `check.rs:125-150`), and require nightly `#![feature(transparent_unions)]` for `#[repr(transparent)]` outside `core::mem::MaybeUninit` (`E0658`, `check.rs:1787-1795`).
- **Lean formalization scope:** [`support/UnionLayoutValidityAndByteOverwrite.lean`](support/UnionLayoutValidityAndByteOverwrite.lean) models `#[repr(Rust)]`, `#[repr(C)]`, `#[repr(transparent)]`, `#[repr(packed(P))]`, and `#[repr(align(A))]` unions at byte granularity (`AbstractByte` values `.uninit` and `.bits val prov` with `val < 256`), assuming sized fields starting at offset `0`.

---

## Findings

### 1. `layout_of_union`: `Scalar::Union` Conversion, Alignment-Mismatch Demotion, and Niche Erasure

**Basis:** `source` + `execution` + `derived` (Lean 4)

In `compiler/rustc_abi/src/layout.rs:404-534`, `LayoutCalculator::layout_of_union` computes the layout of the union's single variant (`only_variant = &variants[VariantIdx::new(0)]`) by tracking aggregate size/alignment alongside a single ABI-compatibility accumulator `common_non_zst_repr_and_align`:

```rust
// compiler/rustc_abi/src/layout.rs:420-467
struct AbiMismatch;
let mut common_non_zst_repr_and_align = if repr.inhibits_union_abi_opt() {
    Err(AbiMismatch)
} else {
    Ok(None)
};
for field in only_variant {
    if field.is_unsized() {
        return Err(LayoutCalculatorError::UnexpectedUnsized(*field));
    }
    align = align.max(field.align);
    max_repr_align = max_repr_align.max(field.max_repr_align);
    size = cmp::max(size, field.size);

    if field.is_zst() { continue; }

    if let Ok(common) = common_non_zst_repr_and_align {
        let field_abi = field.backend_repr.to_union();
        if let Some((common_abi, common_align)) = common {
            if common_abi != field_abi {
                common_non_zst_repr_and_align = Err(AbiMismatch);
            } else if !matches!(common_abi, BackendRepr::Memory { .. }) {
                assert_eq!(common_align, field.align);
            }
        } else {
            common_non_zst_repr_and_align = Ok(Some((field_abi, field.align)));
        }
    }
}
```

Four design decisions determine every observable property of Rust unions:

1. **Unconditional niche and validity erasure (`BackendRepr::to_union`):** Before comparing non-ZST fields, `layout_of_union` strips each field's `BackendRepr` via `.to_union()` (`compiler/rustc_abi/src/lib.rs:1975-1993`), which recursively applies `Scalar::to_union()` across `Scalar`, `ScalarPair`, `SimdVector`, and `SimdScalableVector` (`lib.rs:1636-1638`):
   - `Scalar::Initialized { value, valid_range }` converts to `Scalar::Union { value }`, discarding `valid_range` and recording that uninitialized/arbitrary bit patterns are valid at the ABI boundary.
   - Calling `to_union()` therefore makes two fields with matching hardware `Primitive` and alignment ABI-identical **even if their niches differ** (e.g., `NonZero<u64>` and `u64`, or `&'static u8` and `*const u8`), while preserving distinct primitives (`Int` vs. `Float` in `IntOrFloatRust`) as incompatible (`Err(AbiMismatch)`).
   - Once converted, `Scalar::is_uninit_valid()` returns `true` (`lib.rs:1670-1675`), `Scalar::is_always_valid()` returns `true` (`lib.rs:1661-1666`), `Scalar::valid_range()` returns `WrappingRange::full(value.size(cx))` (`lib.rs:1641-1646`), and mutating `valid_range_mut()` panics (`lib.rs:1651-1655`).
2. **Post-loop alignment checks (`scalar_platform_align` mismatch demotion):** After clamping `align` by `repr.pack` (`align = align.min(pack)`) and then raising `align` by `repr.align` (`align = align.max(repr_align)`), `layout_of_union` demotes `Scalar` or `ScalarPair` back to `BackendRepr::Memory { sized: true }` whenever `repr.scalar_platform_align(dl).unwrap() != align` (`layout.rs:488-492`). This single guard demotes **both** under-aligned unions (`#[repr(packed)] union PackedU64 { a: u64 }` where `align == 1 < 8`) **and** over-aligned unions (`#[repr(align(16))] union OveralignedU64 { a: u64 }` where `align == 16 > 8`, padding total `size` to `16` bytes via `size.align_to(align)`). For `SimdVector`, the check is asymmetric (`element.default_align(dl) > align`), so over-aligning a SIMD vector keeps vector ABI whereas packing demotes to `Memory`.
3. **Zero niche export (`largest_niche: None`):** Line `525` of `layout.rs` sets `largest_niche: None` unconditionally—regardless of whether all fields share a valid-range niche (`TwoNonZero`), whether only one non-ZST field exists alongside ZSTs (`TransNonZero`, `MaybeUninit<NonZero<u64>>`), or whether the union carries `#[repr(transparent)]`. Consequently, `Option<U>` and `Result<U, ()>` can **never** exploit a niche inside any `union U`.
4. **Inhibition via `#[repr(C)]` only (`inhibits_union_abi_opt`):** `ReprOptions::inhibits_union_abi_opt(&self)` (`lib.rs:245-247`) is `self.c()`. Even single-field `#[repr(C)] union ReprCF64 { f: f64 }` enters `layout_of_union` with `Err(AbiMismatch)` and settles on `BackendRepr::Memory { sized: true }`, whereas `#[repr(Rust)]`, `#[repr(packed)]`, `#[repr(align(N))]`, and `#[repr(transparent)]` all set `inhibits_union_abi_opt() == false`.

Empirical size, `Miri`, and LLVM IR checks from [`support/probe_results.json`](support/probe_results.json) verify every branch directly:

| Union / Type Definition | `size, align` | `Option<T>` `size, align` | Zeroed / Uninit Value in `Miri` | Reading Typed Field in `Miri` | Unmerged LLVM IR Signature (`rustc 1.98.0` / LLVM `22.1.6`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `#[repr(transparent)] struct PlainWrap(NonZero<u64>)` | `8, 8` | **`8, 8`** (niche kept) | **UB** on `0` (`miri_rc = 1`) | N/A | `define noundef range(i64 1, 0) i64 @u_sig_0_plain_wrap(i64 noundef range(i64 1, 0) %w)` |
| `union TwoNonZero { a: NonZero<u64>, b: NonZero<u64> }` | `8, 8` | **`16, 8`** (niche erased) | **Valid** (`miri_rc = 0`) | **UB** on `0` (`miri_rc = 1`: `u.a`) | `define i64 @u_sig_1_two_nonzero(i64 %u)` |
| `#[repr(transparent)] union TransNonZero { z: (), a: NonZero<u64> }` | `8, 8` | **`16, 8`** (niche erased) | **Valid** (`miri_rc = 0`) | `—` (niche erased on type) | `define i64 @u_sig_2_trans_nonzero(i64 %u)` |
| `MaybeUninit<NonZero<u64>>` | `8, 8` | **`16, 8`** (niche erased) | **Valid** (`miri_rc = 0`) | **UB** on `.assume_init()` (`0`/`uninit`) | `define i64 @u_sig_2b_maybe_uninit_nonzero(i64 %u)` |
| `union NonNullPtrUnion { p: NonNull<u8>, q: *const u8 }` | `8, 8` (target) | `—` (`largest_niche: None`) | `—` (IR probe) | `—` (IR probe) | `define noundef ptr @u_sig_8_ptr_union(ptr %u)` (no `nonnull`, no arg `noundef`) |
| `union HeterogeneousScalar { i: u32, f: f32 }` | `4, 4` (target) | `—` (`largest_niche: None`) | `—` (IR probe) | `—` (IR probe) | `define noundef i32 @u_sig_7_heterogeneous_scalar(i32 %0)` (`Memory` -> cast `i32`) |
| `#[repr(align(16))] union OveralignedU64 { a: u64 }` | `16, 16` | `—` (`largest_niche: None`) | `—` (IR probe) | `—` (IR probe) | `define noundef i64 @u_sig_5_overaligned_u64(ptr dead_on_return noalias noundef readonly align 16 captures(none) dereferenceable(16) %u)` |
| `#[repr(packed)] union PackedU64 { a: u64 }` | `8, 1` | `—` (`largest_niche: None`) | `—` (IR probe) | `—` (IR probe) | `define noundef i64 @u_sig_6_packed_u64(i64 %0)` (`alloca [8 x i8], align 1`) |

Notice the asymmetric parameter-vs-return attributes across these LLVM IR signatures:
- On functions taking and returning a union directly (`u_sig_1_two_nonzero`, `u_sig_2_trans_nonzero`, `u_sig_2b_maybe_uninit_nonzero`), `layout_of_union` sets `Scalar::Union { value: Int(I64, false) }` (`is_uninit_valid() == true`), so `arg_attrs_for_rust_scalar` (`rustc_ty_utils/src/abi.rs:328-333`) omits `noundef` and `range` on **both** the parameter and the return value (`define i64 @...(i64 %u)`).
- On `u_sig_8_ptr_union(u: NonNullPtrUnion) -> *const u8`, parameter `u` has `Scalar::Union { value: Pointer(_) }`, so `arg_attrs_for_rust_scalar` skips `ArgAttribute::NoUndef` and returns early before checking pointer attributes (`nonnull`, `noalias`, `dereferenceable`), emitting bare `ptr %u`; meanwhile the return value `*const u8` has `Scalar::Initialized { value: Pointer(_) }`, emitting `define noundef ptr`.
- Similarly, in `u_sig_5_overaligned_u64`, `u_sig_6_packed_u64`, and `u_sig_7_heterogeneous_scalar`, returning `u64` / `u32` puts `noundef` on the return register while `adjust_for_rust_abi` and `layout_is_noundef` (`FieldsShape::Union(_) => false` at `callconv/mod.rs:947`) omit `noundef` on the cast input register `i64 %0` / `i32 %0`.

---

### 2. `#[repr(transparent)]` on `union` vs. `struct` (`MaybeUninit<T>` ABI Forwarding)

**Basis:** `source` + `execution` + `derived` (Lean 4)

A common misconception when modeling Rust ADTs is equating `#[repr(transparent)] union U` with `#[repr(transparent)] struct S`. In `rustc`, those two constructs diverge sharply inside `rustc_ty_utils::layout::layout_of` (`compiler/rustc_ty_utils/src/layout.rs:701-745`):

1. **Dispatch split before struct/transparent logic:** `layout_of` checks `if def.is_union()` **first** (line `701`) and returns `map_layout(cx.calc.layout_of_union(&def.repr(), &variants))` (line `710`), bypassing `layout_of_struct` (`layout.rs:540-587`), `univariant` niche propagation (`NicheOptimizations`), and uninhabitedness propagation (`layout.variants` uninhabited check).
2. **`#[repr(transparent)] struct` (`PlainWrap(NonZero<u64>)`):** Because `def.is_union()` is false, `layout_of_struct` copies the non-ZST field's `LayoutData` wholesale: `backend_repr = Scalar::Initialized { value: Int(I64, false), valid_range: 1..=u64::MAX }`, `largest_niche = Some(0)`, `uninhabited = false`. Accordingly:
   - `-Zprint-type-sizes` gives `PlainWrap: 8 bytes` and `Option<PlainWrap>: 8 bytes` (single variant `Some` at `8` bytes, `None` at `0` bytes using the zero niche).
   - `MaybeUninit::<PlainWrap>::zeroed().assume_init()` aborts `Miri` (`miri_rc = 1`) with `constructing invalid value of type PlainWrap: at .0.0.0, encountered 0, but expected something greater or equal to 1`.
   - LLVM IR lowers `fn(PlainWrap) -> PlainWrap` to `define noundef range(i64 1, 0) i64 @u_sig_0_plain_wrap(i64 noundef range(i64 1, 0) %w)`.
3. **`#[repr(transparent)] union` (`MaybeUninit<T>`, `TransNonZero`, `TransF64`):** `layout_of_union` receives `ReprOptions` with `repr.transparent() == true`, sets `repr_c = repr.c() || (repr.transparent() && only_variant.iter().any(|field| field.repr_c))` (`compiler/rustc_abi/src/layout.rs:513-514`), leaves `inhibits_union_abi_opt() == false`, applies `.to_union()` to the single non-ZST field, and passes `layout.fields = FieldsShape::Union(1)` + `largest_niche: None` + `uninhabited: false`. `core::mem::MaybeUninit<T>` relies directly on this path (`library/core/src/mem/maybe_uninit.rs`):
   - `MaybeUninit<T>` is declared `#[lang = "maybe_uninit"] #[repr(transparent)] #[rustc_pub_transparent] pub union MaybeUninit<T> { uninit: (), value: ManuallyDrop<T> }`.
   - **Calling-convention forwarding:** Because `inhibits_union_abi_opt()` is false, `TransNonZero` (`a: NonZero<u64>`) passes in `i64` (identical register class to `u64` / `NonZero<u64>`), `MaybeUninit<NonZero<u64>>` passes in `i64`, and `TransF64` (`f: f64`) passes in SSE scalar register `%xmm0` (`define noundef double @u_sig_2c_trans_f64(double %u)`, compiling to a single `retq` instruction on x86-64!).
   - **Contrast with `#[repr(C)] union ReprCF64 { f: f64 }`:** Setting `#[repr(C)]` turns `inhibits_union_abi_opt()` to `true`, forcing `ReprCF64` to `BackendRepr::Memory { sized: true }`. Under the **Rust ABI** (`CanonAbi::Rust`), `adjust_for_rust_abi` (`compiler/rustc_target/src/callconv/mod.rs:886-894`) casts any sized `Memory` aggregate up to pointer size into a `RegKind::Integer` register rather than preserving the underlying `f64` SSE register! Thus `u_sig_2d_repr_c_f64_rust_abi(u: ReprCF64) -> f64` compiles to `define noundef double @u_sig_2d_repr_c_f64_rust_abi(i64 %0)` and executes `movq %rdi, %xmm0; retq`—explicitly transferring from GPR `%rdi` to XMM `%xmm0`! That difference explains why `#![feature(transparent_unions)]` and `#[rustc_pub_transparent]` exist for `MaybeUninit<T>`: C-ABI / primitive register parity (`f64` in `%xmm0` rather than `%rdi`) without retaining scalar `noundef` or `valid_range` invariants (`#[repr(transparent)]` unions still erase both!).
   - Notice also `core::mem::MaybeUninit<T>::zeroed()` / `uninit()` (`library/core/src/mem/maybe_uninit.rs`): `MaybeUninit::<NonZero<u64>>::zeroed()` succeeds cleanly (`miri_rc = 0`, identically to `TransNonZero`), whereas `Option<MaybeUninit<NonZero<u64>>>` is `16` bytes (`-Zprint-type-sizes`: `8`-byte discriminant + `8`-byte payload, identically to `Option<TransNonZero>` and `Option<TwoNonZero>`).

---

### 3. Unconditional Union Inhabitedness (`uninhabited: false`) and `Option` Tag Separation

**Basis:** `source` + `execution` + `derived` (Lean 4)

Unlike structs and single-variant enums—whose inhabitedness is the conjunction of their field types—every `union` in Rust is unconditionally inhabited in both layout calculation and operational semantics, even if every field type is uninhabited (`!` or `core::convert::Infallible`):

1. **Compiler source consistency across three layers:**
   - **ABI layout (`compiler/rustc_abi/src/layout.rs:526`):** `LayoutCalculator::layout_of_union` sets `uninhabited: false` regardless of `only_variant`.
   - **Type-system inhabitedness predicate (`compiler/rustc_middle/src/ty/inhabitedness/mod.rs:135-136`):**
     ```rust
     // For now, unions are always considered inhabited
     Adt(adt, _) if adt.is_union() => InhabitedPredicate::True,
     ```
   - **Operational-semantics inhabitedness (`compiler/rustc_middle/src/ty/inhabitedness/mod.rs:355-358`):**
     ```rust
     if adt_def.is_union() {
         // Unions are always inhabited.
         return true;
     }
     ```
   - **Layout invariant bypass (`compiler/rustc_ty_utils/src/layout/invariant.rs:133-135`):** `layout_sanity_check` skips uninhabitedness and niche sanity checks for `FieldsShape::Union(..)` while verifying that `Option<NeverUnion>` has an inhabited `Some` variant and valid tag layout.
2. **Empirical separation between `Infallible` / `!` and `NeverUnion` / `BangUnion`:**
   - **Sizes & `-Zprint-type-sizes` (`probe_results.json`):**
     - `size_of::<Infallible>() == 0`, `size_of::<Option<Infallible>>() == 0` (single variant `None` with uninhabited `Some` eliminated).
     - `size_of::<NeverUnion>() == 0` (`align == 1`), **`size_of::<Option<NeverUnion>>() == 1`** (`discriminant: 1 bytes`, `None: 0 bytes`, `Some: 0 bytes`). Identically `size_of::<BangUnion>() == 0`, **`size_of::<Option<BangUnion>>() == 1`**. Both `rustc 1.98.0-nightly` and `rustc 1.102.0-nightly` (`3ef0c22cd`) print `NEVER_SZ=0 OPT_NEVER_SZ=1 OPT_TWO_NZ=16 OPT_TRANS_NZ=16`.
   - **Runtime validity separation in `Miri`:**
     - `let u: NeverUnion = unsafe { MaybeUninit::<NeverUnion>::uninit().assume_init() };` (`never_union_inhabited_ok`): **`miri_rc = 0`** (`MaybeUninit::assume_init` invokes `intrinsics::assert_inhabited::<NeverUnion>()` which passes, and value validity runs `visit_union` with zero fields checked!).
     - `MaybeUninit::<Infallible>::uninit().assume_init()` (`infallible_assume_init_ub`): **`miri_rc = 1`**: `constructing invalid value of type core::convert::Infallible: encountered a value of zero-variant enum core::convert::Infallible`.
     - Projecting the field `let _v: Infallible = unsafe { u.f };` (`never_union_infallible_field_read_ub`) or `let _v: ! = unsafe { u.b };` (`never_union_field_read_ub`): **`miri_rc = 1`**, because the MIR projection reads the value at field type `Infallible` / `!`, triggering `ValidityVisitor::visit_value` on an uninhabited enum/never type.

---

### 4. CTFE / `Miri` `FieldsShape::Union` Validity, `union_data_range` Padding Stripping, and Partial Overwrite Semantics

**Basis:** `source` + `execution` + `derived` (Lean 4)

Because a `union` does not record an active variant tag at runtime, `rustc_const_eval`'s abstract machine (`Miri` and CTFE) enforces **representation-preserving byte validity** at union copies and **field-scoped validation** at typed field projections:

#### 4.1 Value Validation (`ValidityVisitor::visit_union` and `union_data_range`)

In `compiler/rustc_const_eval/src/interpret/validity.rs:1307-1337` and `1567-1602`:
- Top-level `ValidityVisitor::visit_value` checks `if cfg!(debug_assertions)` on `BackendRepr::Scalar(scalar_layout)` only when `!scalar_layout.is_uninit_valid()` (`validity.rs:1571`), so `Scalar::Union` values skip scalar validation entirely.
- For `FieldsShape::Union(_fields)` (`validity.rs:1307-1337`), `visit_union` does **NOT** recurse into any field's validity invariant; it performs only two operations:
  1. **CTFE `!Freeze` read-only check (`validity.rs:1313-1325`):** When `self.ctfe_mode.is_some_and(|c| !c.allow_immutable_unsafe_cell())` (static/promoted validation rather than value `const` evaluation), if the union is non-zero-sized and `!val.layout.ty.is_freeze(...)`, it requires `self.in_mutable_memory(val)`, otherwise throwing `encountered UnsafeCell in read-only memory`. Our live compiler diagnostic suite directly confirms this exact boundary across `CtfeValidationMode`:
     - `ctfe_const_cell_union_ok`: `pub const C: CellUnion = CellUnion { n: 0 };` compiles cleanly (`rustc_rc = 0`) because `CtfeValidationMode::Const` permits immutable `UnsafeCell`s in value constants.
     - `ctfe_promoted_cell_union_e0492`: `pub const C_REF: &CellUnion = &CellUnion { n: 0 };` is rejected earlier by borrow/promotion checking with `E0492` (`interior mutable shared borrows of temporaries that have their lifetime extended until the end of the program are not allowed`).
     - `ctfe_unsafe_cell_in_union_readonly_e0080`: `pub static BAD_REF: &CellUnion = unsafe { &*(&0u32 as *const u32 as *const CellUnion) };` bypasses promotion and reaches `visit_union` during static validation, aborting with `E0080: constructing invalid value of type &CellUnion: at .<deref>, encountered UnsafeCell in read-only memory`!
  2. **Padding hole preservation vs. pure union padding stripping (`union_data_range`, `validity.rs:1178-1246, 1326-1335`):** When `reset_provenance_and_padding` is enabled (on typed `Copy`/retag moves of aggregates), `visit_union` calls `Self::union_data_range(self.ecx, val.layout)` to compute the `RangeSet` union of every non-ZST scalar/primitive byte interval across all fields of the union. All bytes covered by *any* field's data range are preserved verbatim (keeping initialized data, pointer provenance, or uninitialized state as-is), whereas bytes covered by **zero** fields' data ranges are stripped to uninitialized (`uninit`).
     - Live `Miri` verification contrasts `PadHoleUnion { pair: PairU8U16 }` (`#[repr(C)] struct PairU8U16(u8, u16)`, size `4`, fields covering byte `0` (`u8`) and bytes `2..4` (`u16`), leaving byte `1` as internal padding in all union fields) against `FullCoverUnion { pair: PairU8U16, raw: [u8; 4] }` (where `[u8; 4]` covers byte `1`). Initializing all `4` bytes via `*(&mut u as *mut _ as *mut [u8; 4]) = [0xAA, 0xBB, 0xCC, 0xDD]` and performing a typed copy `let u2 = typed_copy(u);` strips byte `1` in `PadHoleUnion` (`union_data_range_padding_strip_ub`, `miri_rc = 1`: `reading memory at alloc25[0x1..0x2], but memory is uninitialized at [0x1..0x2]`), whereas `FullCoverUnion` preserves byte `1` (`0xBB`) cleanly (`union_data_range_covered_byte_preserved_ok`, `miri_rc = 0`).

#### 4.2 Partial Sub-Field Writes (`u.lo_u8 = 0x99`), Provenance Preservation, and Destructor Guard (`E0740`)

When writing a sub-field of a `union` (`u.lo_u8 = 0x99`):
- **Offset and backing allocation:** In `rustc_const_eval/src/interpret/place.rs`, writes to scalar-backed locals via sub-field projection force backing allocation (`as_mplace_or_mutable_local` / `force_allocation`) so sub-object writes operate over byte slices `[offset..offset+size]` (`offset = 0` in unions), validating only the written value (`newBytes`) against the target field type `lo_u8: u8` (`write_immediate`).
- **Frame preservation on sibling bytes and pointer provenance:** Because `copy_op_no_validate` and `write_immediate` write strictly `[0..field.size)` without overwriting `[field.size..union.size)`:
  - `partial_overwrite_preserves_sibling_bytes_ok` tests three invariants in one `Miri` run (`miri_rc = 0`): (a) initializing `U32Lo { full_u32: 0x11223344u32.to_le() }`, overwriting `u.lo_u8 = 0x99`, and reading `u32::from_le(u.full_u32)` yields **`0x11223399`** (also verified natively under `rustc -C opt-level=2`: `native_opt2_rc = 0`, `FULL=0x11223399`); (b) writing `u_part.lo_u8 = 0x55` into an uninitialized `U32Lo` allows reading `u_part.lo_u8 == 0x55` cleanly; and (c) initializing `PairLo { pair: (0xAABBCCDD, &VAL), lo_u8: u8 }`, overwriting `p.lo_u8 = 0xEE`, and dereferencing `p.pair.1` returns `*r == 77` with sibling reference provenance intact.
  - `partial_overwrite_uninit_upper_read_ub` (`MaybeUninit::<U32Lo>::uninit().assume_init()`, `u.lo_u8 = 0x99`, then `unsafe { u.full_u32 }`): triggers **`miri_rc = 1`** (`reading memory at alloc26[0x0..0x4], but memory is uninitialized at [0x1..0x4]`), confirming that `[1..4)` remained `.uninit` rather than being zero-filled or initialized by `lo_u8 = 0x99`.
- **Well-formedness guard (`E0740`):** `check_union_fields` (`compiler/rustc_hir_analysis/src/check/check.rs:120, 125-150`) rejects fields whose type neither satisfies `BikeshedGuaranteedNoDrop` / `Copy` nor is wrapped in `ManuallyDrop<T>` (`union_non_copy_e0740`: `rustc_rc = 1`, `error[E0740]: field must implement Copy or be wrapped in ManuallyDrop<...> to be used in a union`; wrapping in `ManuallyDrop<HasDrop>` compiles cleanly with `union_manually_drop_ok`: `rustc_rc = 0`).

---

### 5. SysV x86-64 Eightbyte Classification, Rust ABI Aggregate Casts, and LLVM 23 `dead_on_return` + `nofree`

**Basis:** `source` + `execution`

Union parameter passing splits sharply between `extern "C"` (target psABI) and Rust calls (`CanonAbi::Rust`):

1. **SysV AMD64 C ABI eightbyte classification (`compiler/rustc_target/src/callconv/x86_64.rs:34-210`):**
   - `classify_arg` traverses `0..layout.fields.count()` recursively (line `87-90`) at offset `off + layout.fields.offset(i)` (all `off` for union fields).
   - For `#[repr(C)] pub union IntOrFloatC { i: u64, f: f64 }`, `i: u64` contributes `Class::Int` to eightbyte `0`, and `f: f64` contributes `Class::Sse` to eightbyte `0`.
   - `Class::merge(Class::Int, Class::Sse)` returns `Ord::min(Class::Int, Class::Sse) == Class::Int` (`x86_64.rs:34-40`), classifying the entire union into a single `INTEGER` eightbyte (`i64` in `%rdi`) rather than `SSE` (`%xmm0`).
2. **Rust ABI `adjust_for_rust_abi` vs. direct `Scalar::Union` passing (`compiler/rustc_target/src/callconv/mod.rs:875-898`):**
   - For `BackendRepr::Memory { .. }` arguments of `size <= ptr_size` (8 bytes on x86-64), `adjust_for_rust_abi` invokes `arg.cast_to_maybe_noundef(Reg { kind: RegKind::Integer, size }, cx)`, where `layout_is_noundef` (`mod.rs:947`) explicitly returns **`false`** for `FieldsShape::Union(_)`, ensuring no parameter `noundef` attribute is emitted on cast aggregate registers even when every field would individually be `noundef`.
3. **Complete 12-Function Pre-Merge LLVM IR & x86-64 Assembly Matrix (`probe_results.json`, `rustc 1.98.0-nightly` / LLVM `22.1.6`, `-C opt-level=2 -Zmerge-functions=disabled`):**

| Function Probe (`-Zmerge-functions=disabled`) | Unmerged LLVM IR Header / Body (`LLVM 22.1.6`) | Optimized x86-64 Assembly (`opt2`) | Key Compiler Mechanism |
| :--- | :--- | :--- | :--- |
| `u_sig_0_plain_wrap(w: PlainWrap) -> PlainWrap` | `define noundef range(i64 1, 0) i64 @u_sig_0_plain_wrap(i64 noundef range(i64 1, 0) %w)` | `movq %rdi, %rax; retq` | Struct preserves `Scalar::Initialized` (`noundef` + `range`) |
| `u_sig_1_two_nonzero(u: TwoNonZero) -> TwoNonZero` | `define i64 @u_sig_1_two_nonzero(i64 %u)` | `movq %rdi, %rax; retq` | `to_union()` -> `Scalar::Union` (no `noundef`, no `range`) |
| `u_sig_2_trans_nonzero(u: TransNonZero) -> TransNonZero` | `define i64 @u_sig_2_trans_nonzero(i64 %u)` | `movq %rdi, %rax; retq` | `#[repr(transparent)]` union still runs `to_union()` |
| `u_sig_2b_maybe_uninit_nonzero(u: MaybeUninit<NonZero<u64>>) -> ...` | `define i64 @u_sig_2b_maybe_uninit_nonzero(i64 %u)` | `movq %rdi, %rax; retq` | `MaybeUninit<T>` identical to `TransNonZero` |
| `u_sig_2c_trans_f64(u: TransF64) -> f64` | `define noundef double @u_sig_2c_trans_f64(double %u)` (`ret double %u`) | `retq` (`%xmm0 -> %xmm0`!) | `#[repr(transparent)]` preserves `Float(F64)` in `%xmm0`, arg omits `noundef` |
| `u_sig_2d_repr_c_f64_rust_abi(u: ReprCF64) -> f64` | `define noundef double @u_sig_2d_repr_c_f64_rust_abi(i64 %0)` (`alloca` + `memcpy` + `load double`) | `movq %rdi, %xmm0; retq` | `#[repr(C)]` inhibits union ABI -> `Memory` -> Rust ABI integer cast `%rdi -> %xmm0` |
| `u_sig_3_int_float_rust(u: IntOrFloatRust) -> u64` | `define noundef i64 @u_sig_3_int_float_rust(i64 %0)` (`alloca` + `memcpy` + `load i64`) | `movq %rdi, %rax; retq` | `AbiMismatch` (`I64 != F64`) -> `Memory` -> `adjust_for_rust_abi` cast `i64 %0` |
| `u_sig_4_int_float_sysv_c(u: IntOrFloatC) -> u64` | `define noundef i64 @u_sig_4_int_float_sysv_c(i64 %0)` | `movq %rdi, %rax; retq` | SysV `classify_arg`: `Ord::min(Int, Sse) = Int` (`i64 %0`) |
| `u_sig_5_overaligned_u64(u: OveralignedU64) -> u64` | `define noundef i64 @u_sig_5_overaligned_u64(ptr dead_on_return noalias noundef readonly align 16 captures(none) dereferenceable(16) %u)` (LLVM `23.1.5` adds `nofree`) | `movq (%rdi), %rax; retq` | `scalar_platform_align(8) != 16` -> `Memory` -> `PassMode::Indirect` + `dead_on_return` + deduced `readonly`/`captures(none)` |
| `u_sig_6_packed_u64(u: PackedU64) -> u64` | `define noundef i64 @u_sig_6_packed_u64(i64 %0)` (`%u = alloca [8 x i8], align 1`) | `movq %rdi, %rax; retq` | `scalar_platform_align(8) != 1` -> `Memory` -> cast `i64 %0` |
| `u_sig_7_heterogeneous_scalar(u: HeterogeneousScalar) -> u32` | `define noundef i32 @u_sig_7_heterogeneous_scalar(i32 %0)` (`alloca [4 x i8], align 4`) | `movl %edi, %eax; retq` | `Int(I32) != Float(F32)` -> `Memory` -> cast `i32 %0` |
| `u_sig_8_ptr_union(u: NonNullPtrUnion) -> *const u8` | `define noundef ptr @u_sig_8_ptr_union(ptr %u)` (`ret ptr %u`) | `movq %rdi, %rax; retq` | `Scalar::Union { Pointer }` keeps `ptr %u` without `nonnull` or arg `noundef` |

Look especially at `u_sig_5_overaligned_u64` (`apply_deduced_attributes` + `indirect_pass_mode` + `PassMode::Indirect` codegen):
- `indirect_pass_mode` (`compiler/rustc_target/src/callconv/mod.rs:425-444`) sets `NoAlias`, `CapturesAddress`, `NonNull`, `NoUndef` (and `NoFree` in `3ef0c22cd` for LLVM `>= 23`), plus `pointee_size = 16`, `pointee_align = 16`.
- `apply_deduced_attributes` (`compiler/rustc_ty_utils/src/abi.rs:671-693`) refines `PassMode::Indirect` with MIR-deduced `ArgAttribute::ReadOnly` and `ArgAttribute::CapturesNone` (lowering `CapturesAddress` down to `captures(none)` on non-mutated frozen union arguments).
- `rustc_codegen_llvm/src/abi.rs:583-592` unconditionally appends LLVM `DeadOnReturn` (`dead_on_return`) for `PassMode::Indirect { mode: IndirectMode::Pointer }` whenever optimizing (`opt-level != 0`), asserting that the caller's stack copy may be treated as dead/clobbered on function return.
- Under `rustc 1.102.0-nightly` (`3ef0c22cd`, LLVM `23.1.5`), all five cross-checked headers match structurally, with `u_sig_5_overaligned_u64` emitting:
  `define noundef i64 @u_sig_5_overaligned_u64(ptr noalias nofree noundef readonly align 16 captures(none) dead_on_return dereferenceable(16) %u)`.

---

### 6. Downstream Alignment: `joshlf/anneal` and `google/zerocopy`

**Basis:** `source`

1. **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
   - **Trusted AST boundary (`trusted/lean/Trusted/MirAst.lean`):** Non-fieldless-enum `TyKind::Adt` types—including all `union` types—lower fail-closed to `MirTy.unsupported` (`MirAst.lean:308-311`), and `Rvalue.aggregateTuple` covers only `AggregateKind::Tuple`, lowering `AggregateKind::Adt` fail-closed to `Rvalue.unsupported` (`MirAst.lean:610-618`). Any future extension admitting unions into `MirAst` must explicitly distinguish `FieldsShape::Union` from `#[repr(transparent)]` structs: forwarding union ABI through struct rules would falsely preserve scalar `noundef`/niches (`ce2`), while intersecting field niches would unsoundly reject valid `.uninit`/zeroed union values (`ce1`).
   - **Vendored `lean-miri` (`vendor/lean-miri/Miri/`):** Already encodes three critical upstream invariants identified in this report: `ABI.Scalar.toUnion` and `ABI.Scalar.isUninitValid` (`RuntimeLayout.lean:628-656`), `FieldsShape.Union` in `unionRanges` (`ValidityVisitor.lean:245-270`), and `ValidityVisitor.visit`'s `.Union` CTFE `!Freeze` read-only check + `dataBytes` marking alongside `checkScalarRange`'s `.Union .. => pure ()` skip (`ValidityVisitor.lean:272-275, 428-440`).
2. **`google/zerocopy` (`907b9175fee081872ec883ca4709e6ad922f8ed0`, `v0.8.64`):**
   - **`FromZeros` and `FromBytes` on unions (`zerocopy-derive/src/derive/from_bytes.rs:177-204`):** Both derives require **all** fields to satisfy the corresponding trait bound (`FieldBounds::All(&[TraitBound::Slf])`), aligning with the rule that union values impose zero byte validity while any typed field projection `u.f` validates `f`'s invariant.
   - **`IntoBytes` on unions (`zerocopy/src/lib.rs:5901-5924`, `zerocopy-derive/src/derive/into_bytes.rs:211-259`):** Behind the unstable `--cfg zerocopy_derive_union_into_bytes` opt-in, `derive_into_bytes_union` requires non-generic unions to carry `#[repr(C)]`, `#[repr(packed)]`, or `#[repr(transparent)]` and emits `PaddingCheck::Union`, requiring the union to have zero internal/trailing padding gaps across `union_data_range` (`U64` vs. `[u8; 8]` ok; `PadHoleUnion` has an uncovered hole at byte `1` that `Miri`'s `union_data_range` strips to `.uninit` on copy!). `zerocopy`'s crate-level caution citing `unsafe-code-guidelines#438` explicitly flags that whether copying/interpreting union padding preserves non-covered bytes remains subject to future operational-semantics stabilization, making `union_data_range` padding stripping directly load-bearing for `PaddingCheck::Union`.

---

### 7. Kernel-Checked Lean 4 Formalization and Constructive Counterexamples

**Basis:** `derived` (Lean 4)

[`support/UnionLayoutValidityAndByteOverwrite.lean`](support/UnionLayoutValidityAndByteOverwrite.lean) provides a self-contained `1,189`-line, `43`-theorem Lean `v4.34.1` formalization using solely elementary `Nat` and `List` reasoning over byte buffers `ByteBuffer := List AbstractByte` (with constructors `.uninit` and `.bits (val : Nat) (prov : Option Nat)` governed by `BufferWF`). Its four main theorem groups prove:

1. **Exact `layout_of_union` ABI / Niche / Inhabitedness Invariants (Section 2–4):**
   - `ScalarAbi.toUnion_isUninitValid`, `ScalarAbi.toUnion_isAlwaysValid`, `ScalarAbi.toUnion_idempotent`, `ScalarAbi.toUnion_preserves_primitive`, `ScalarAbi.toUnion_preserves_size`: `.toUnion` strips niches and uninit guards while keeping primitive kind and byte size.
   - `computeUnionLayout_allScalarsUnion`, `computeUnionLayout_largestNiche_none`, `computeUnionLayout_uninhabited_false`: `computeUnionLayout` outputs only union-erased scalars, `largestNiche = none`, and `uninhabited = false`.
   - `overaligned_union_demotes_to_memory` and `reprC_union_demotes_to_memory`: over-aligned (`platformScalarAlign < reprAlign`) and `#[repr(C)]` non-empty unions demote to `BackendRepr.memory`.
   - `argAttrsForScalar_toUnion`, `computeUnionLayout_omits_noundef_and_range`, and `toUnionRepr_register_call_sound`: every union passing through a register boundary omits `hasNoUndef` and `hasRangeCheck`, so `evalRegisterCall` returns `.ok buf` cleanly on **every** `validUnionValue` buffer (including `.uninit` bytes and `0` bytes for `NonZero<u64>`).
2. **`union_data_range` and Exact Byte-Slice Partial Overwrite Frame Law (Section 3 & 5):**
   - `copyUnionWithDataRange_preserves_valid`: copying with `dataMask` resets pure padding holes (`dataMask[i] = false`) to `.uninit` while preserving `validUnionValue` and covered bytes verbatim.
   - `writeUnionField_preserves_valid`, `writeUnionField_reads_back`, and `writeUnionField_preserves_upper_slice`: proves get-put soundness (`readUnionField u f out = .ok newBytes`) and the exact spatial frame invariant (`out.drop f.size = buf.drop f.size` and `∀ i ≥ f.size, out[i]? = buf[i]?`).
   - `u32_writeLo_preserves_upper_bytes` and `u32_0x11223344_write_0x99_eq_0x11223399`: specializes the frame law to `U32Lo`, proving symbolically over all `b0..b3, b0' < 256` and concretely for `0x11223344` -> `0x99` -> `0x11223399` that upper bytes `[1..4)` (including bits, provenance, or `.uninit`) remain unchanged.
3. **Universal Inhabitedness & `Option` Tag Separation (Section 6):**
   - `unionLayout_universally_inhabited` and `uninhabited_field_read_fails_on_valid_union`: even if every field is uninhabited (`bytePred _ = false`, `uninhabited = true`), the union satisfies `uninhabited = false` and accepts `List.replicate u.size .uninit` as valid, while any `readUnionField` fails with `.error .invalidFieldValue`.
   - `option_infallible_size_zero_vs_option_neverUnion_size_one`: proves `optionSizeOf infallibleStructLayout = 0`, `optionSizeOf neverUnionLayout = 1` (`> 0`), `optionSizeOf plainWrapStructLayout = 8`, `optionSizeOf twoNonZeroUnionLayout = 16`, and `optionSizeOf transNonZeroUnionLayout = 16`.
4. **Three Constructive Counterexamples Refuting Naïve Models (Section 7):**
   - `ce1_intersecting_field_niches_on_two_nonzero_union_unsoundly_rejects_uninit_bytes`: proves intersecting field niches (`NonZero<u64> ∩ NonZero<u64>`) unsoundly rejects all-`.uninit` and all-`0` buffers on `TwoNonZero` (`validUnionValue` holds, whereas `buggyIntersectedUnionValid = false`), while confirming `readUnionField` on `0` still fails.
   - `ce2_emitting_llvm_noundef_on_scalar_union_causes_call_boundary_poison_ub`: proves forwarding `#[repr(transparent)]` struct attributes (`hasNoUndef = true, hasRangeCheck = true`) onto `TransNonZero` causes `.callUbPoison` on `.uninit` and `0` inputs, whereas actual `transNonZeroUnionLayout` emits `{ hasNoUndef := false, hasRangeCheck := false }` and returns `.ok`.
   - `ce3_treating_never_field_union_as_uninhabited_miscompiles_valid_assume_init`: proves propagating `Infallible.uninhabited = true` to `NeverUnion` collapses `optionSizeOf` from `1` to `0` and miscompiles valid `assume_init()` into `.ubUnreachable`, whereas `rustc` produces `.ok []`.

---

## Boundaries

The following edges and related constructs fall outside what this report verified directly:

- **Unsized union fields (`unsupported`):** Rust does not support unsized fields inside unions (`check_type_defn(..., all_sized = true)`, `layout.rs:433` `UnexpectedUnsized`); tail-unsized projections are `known not to apply` to `FieldsShape::Union`.
- **SimdVector / SimdScalableVector union fields (`not examined` empirically):** Source inspection confirms `layout_of_union` checks `element.default_align(dl) > align` for `SimdVector` and handles `SimdScalableVector` via `to_union()`, leaving vector register pressure intact even when over-aligned; no vector-field union LLVM IR or `Miri` execution probe was run.
- **Non-x86_64 C ABIs (`not examined`):** SysV eightbyte classification applies specifically to `x86_64-unknown-linux-gnu`. Source inspection of `compiler/rustc_abi/src/callconv.rs:1-194` shows `homogeneous_aggregate` merges union fields sequentially as if they were struct members on architectures using HFA/HVA classification (such as AArch64), and a separate guard notes `powerpc64` checks HFA rules elsewhere; HFA/HVA targets (`aarch64`, `wasm`, Windows MSVC x64) were `not examined` empirically.
- **`ScalarPair` partial-init debug check (`not examined` empirically):** Source inspection of `compiler/rustc_const_eval/src/interpret/validity.rs:1583-1598` shows `ValidityVisitor::visit_value` skips `visit_scalar` in `debug_assertions` checks for `ScalarPair` unless **both** components satisfy `!is_uninit_valid()`, marking a `FIXME` for mixed-init `ScalarPair` values; `ScalarPair` unions (e.g. two `&[u8]` fields or `union` containing `(*const u8, usize)` pairs) were `not examined` empirically.
- **Nightly `BikeshedGuaranteedNoDrop` & `transparent_unions` stability (`known not to apply` to stable Rust):** Stable Rust restricts union fields to `Copy` or `ManuallyDrop<T>` (`E0740`) and rejects `#[repr(transparent)]` on user unions (`E0658`) even though `core::mem::MaybeUninit<T>` uses it internally.
- **`#[derive(IntoBytes)]` on unions without `--cfg zerocopy_derive_union_into_bytes` (`unsupported` by default in `zerocopy` `v0.8.64`):** `zerocopy` refuses union `IntoBytes` derives by default because upstream union bit-validity / padding semantics across copies remain open under Unsafe Code Guidelines `#438`.
- **End-to-end Rust-to-Lean lowering of `union` in `joshlf/anneal` (`unsupported`):** At `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst` rejects non-fieldless-enum `Adt` types (`MirTy.unsupported`), so `Anneal` does not yet ingest real Rust `union` MIR items end-to-end.

---

## Evidence

| Evidence Type | Artifact / Source | Verified Ground Truth Recorded |
| :--- | :--- | :--- |
| Primary compiler source (`source`) | `rust-lang/rust` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`): `compiler/rustc_abi/src/{lib.rs, layout.rs, callconv.rs}`, `compiler/rustc_middle/src/ty/inhabitedness/mod.rs`, `compiler/rustc_hir_analysis/src/check/{check.rs, wfcheck.rs}`, `compiler/rustc_ty_utils/src/{layout.rs, layout/invariant.rs, abi.rs}`, `compiler/rustc_target/src/callconv/{mod.rs, x86_64.rs}`, `compiler/rustc_codegen_llvm/src/abi.rs`, `compiler/rustc_const_eval/src/interpret/{validity.rs, place.rs}`, `library/core/src/mem/maybe_uninit.rs` | Exact implementation of `layout_of_union`, `Scalar::to_union`, `inhibits_union_abi_opt`, `uninhabited: false`, `largest_niche: None`, `arg_attrs_for_rust_scalar`, `apply_deduced_attributes`, `indirect_pass_mode` + `NoFree`, `DeadOnReturn`, SysV `Class::merge`, `ValidityVisitor::visit_union`, and `union_data_range`. |
| Cross-revision diff (`source` + `execution`) | Direct comparison of `callconv/mod.rs` and `codegen_llvm/src/abi.rs` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (LLVM `22.1.6`) vs. `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (LLVM `23.1.5`) | Accounts for explicit `nofree` appearing alongside `dead_on_return` and `dereferenceable(16)` on `OveralignedU64` in LLVM `23.1.5`, while confirming identical sizes (`NEVER_SZ=0 OPT_NEVER_SZ=1 OPT_TWO_NZ=16 OPT_TRANS_NZ=16`), `Miri` RCs, and `i64` register/cast lowering across both revisions. |
| Live empirical probe (`execution`) | [`support/probe_union_abi_inhabitedness_and_bytes.py`](support/probe_union_abi_inhabitedness_and_bytes.py) -> [`support/probe_results.json`](support/probe_results.json) (run on `rustc 1.98.0-nightly` / `miri 0.1.0` / LLVM `22.1.6`, `x86_64-unknown-linux-gnu`, offline `no_std` core sysroot) | `12` `Miri` programs (`5` passing `miri_rc = 0`, `7` deterministic UB `miri_rc = 1`), `19` `size_of`/`align_of` entries, `10` `-Zprint-type-sizes` dumps, `6` compile checks (`E0740`, `E0658`, `const CellUnion` ok, `E0492`, `E0080`), `12` pre-merge and post-opt LLVM IR functions (`-C opt-level=2 -Zmerge-functions=disabled`), and `12` x86-64 disassembly sequences. |
| Lean 4 formalization (`derived`) | [`support/UnionLayoutValidityAndByteOverwrite.lean`](support/UnionLayoutValidityAndByteOverwrite.lean) verified with Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`, `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) | `43` proved theorems (including `ce1`, `ce2`, `ce3` counterexamples), exit code `0`, zero warnings, `#print axioms` clean (`0` `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, or `._unsafe_rec`), `0` `omega`/`bv_decide`/`native_decide`/`partial def`. |
| Downstream consumers (`source`) | `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`Trusted/MirAst.lean`, `Trusted/Correspondence.lean`, `Miri/ABI/RuntimeLayout.lean`, `Miri/Interpreter/ValidityVisitor.lean`) and `google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0` (`src/lib.rs`, `zerocopy-derive/src/derive/{from_bytes.rs, into_bytes.rs}`) | Confirmed `Trusted.MirAst` fail-closed union exclusion vs. `lean-miri` `ABI.Scalar.Union` / `unionRanges` modeling, and `zerocopy`'s `FromBytes`/`FromZeros`/`IntoBytes` union derive bounds. |

---

## Revalidation

Run all three verification commands from the report directory (or repository root for the corpus check) to revalidate every empirical claim, Lean proof, and corpus invariant:

1. **Re-run the live `rustc` + `Miri` + LLVM IR + x86-64 disassembly probe:**
   Requires an active `rustc` nightly toolchain with `miri` and `rust-src` components installed (`rustup component add miri rust-src` on a host with `x86_64-unknown-linux-gnu` target):
   ```bash
   python3 support/probe_union_abi_inhabitedness_and_bytes.py --out union_probe_revalidation.json
   ```
   Confirm exit code `0`, inspect `miri_cases` exit codes (`0` vs `1`) and `llvm_ir_and_asm.llvm_define_headers_pre_merge`, and compare `u_sig_5_overaligned_u64` attributes against the target LLVM version (`>= 23` expects `nofree` alongside `dead_on_return`).

2. **Kernel-check the Lean `v4.34.1` formalization and audit `#print axioms`:**
   ```bash
   ~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
     -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/UnionLayoutValidityAndByteOverwrite.lean
   ```
   Confirm exit code `0` and check that running `#print axioms` across every public theorem in `RustcUnionSemantics` produces zero occurrences of `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, or `._unsafe_rec`.

3. **Validate corpus catalog integrity from the corpus root:**
   ```bash
   python3 tools/reference.py catalog && python3 tools/reference.py check
   ```
   Confirm exit code `0` with `CATALOG.json` synchronized and schema validation passing.

### Revalidation Triggers

Re-run this suite whenever:
- Upstream `rust-lang/rust` alters `LayoutCalculator::layout_of_union`, `ReprOptions::inhibits_union_abi_opt`, `Ty::inhabited_predicate`, `indirect_pass_mode`, `layout_is_noundef`, `ValidityVisitor::visit_union`, or `union_data_range`.
- Upstream LLVM changes pointer argument attribute inference or codegen (`dereferenceable`, `nofree`, `dead_on_return`, `captures(...)`).
- Rust Unsafe Code Guidelines issue `#438` stabilizes union bit-validity/padding rules, `#![feature(transparent_unions)]` or `BikeshedGuaranteedNoDrop` stabilizes, or `joshlf/anneal`'s `Trusted.MirAst` adds union support.
