# `rustc` Scalable Vectors (`BackendRepr::SimdScalableVector`), Live AArch64 SVE Stack-Smashing & `-Znext-solver=globally` `DUMMY_SP` WF-Bypass Soundness Bugs, RISC-V RVV Debuginfo ICE, and `autodiff` / `offload` Codegen Gates

## Summary

`rustc`'s internal `#[rustc_scalable_vector]` representation (`BackendRepr::SimdScalableVector`) exhibits a **live, compiler-verified memory-safety soundness vulnerability** across `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), and `rust-lang/rust` HEAD (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), alongside a live RISC-V RVV debuginfo ICE, a live 1-field scalable-container `delayed_bug` ICE, an AArch64 `element_count = 1` DWARF subrange truncation defect, and strict compiler-flag / unshipped-backend gates on `#![feature(autodiff)]` and `core::intrinsics::offload`:

1. **False `Sized` / `vscale = 1` Layout Illusion (`rustc_abi`, `rustc_ty_utils`, `rustc_next_trait_solver`):**
   `BackendRepr::is_unsized` returns `false` for `BackendRepr::SimdScalableVector` (`compiler/rustc_abi/src/lib.rs:1886-1899` at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), and `vector_type_layout` (`compiler/rustc_abi/src/layout.rs:979-1035`) stores the `vscale = 1` minimum byte width (`elt.size * count * number_of_vectors`, e.g., `16 B` for `#[rustc_scalable_vector(4)] struct SvU32(u32)`) as the type's exact static `LayoutData.size`. Consequently, `SvU32` satisfies `Sized` and `MetaSized`, `core::mem::size_of::<SvU32>() == 16`, `core::alloc::Layout::new::<SvU32>().size() == 16`, `size_of::<GenericPair<SvU32>>() == 32`, and `offset_of!(GenericPair<SvU32>, canary) == 16` even on 256-bit (`32 B`) and 512-bit (`64 B`) SVE hardware.

2. **Three Independent Well-Formedness Bypasses Leading to Silent Corruption and Stack-Frame Smashing in Safe Generic Rust:**
   - **Pre-monomorphization generic ADT bypass (`wfcheck.rs:1039-1051`):** `wfcheck` bans scalable-vector fields in non-container structs, enums, and unions by inspecting uninstantiated `tcx.type_of(field.did).instantiate_identity()`. On a generic field `first: T`, `ty.kind()` is `ty::Param(T)` (not `ty::Adt`), so generic structs (`GenericPair<T>`), generic enums (`GenericEnum<T>`), and generic unions (`GenericUnion<T>`) compile with `rc = 0` under both `-Znext-solver=no` and `-Znext-solver=globally`.
   - **Unconditional array WF bypass (`wf.rs:812-827`):** `WfPredicates` for `ty::Array(subty, len)` checks only `self.require_sized(subty, ...)` and performs no `is_scalable_vector()` check. Both direct monomorphic `[SvU32; 2]` and generic `[T; 2]` compile with `rc = 0` under both solvers, emitting `sret([32 x i8])` with consecutive `store <vscale x 4 x i32>` writes at fixed 16-byte stride (overlapping whenever `vscale >= 2`).
   - **Live `-Znext-solver=globally` `DUMMY_SP` tuple & closure WF regression (`delegate.rs:372-385`, `wf.rs:834-856`):** `WfPredicates` for `ty::Tuple` guards `"scalable vectors cannot be tuple fields"` with `&& !self.span.is_dummy()`. Under `-Znext-solver=no` (default in `1.98.0-nightly`), direct `(SvU32, u64)`, generic `(T, u64)`, and closure captures `move || { let _ = v; canary }` are rejected (`rc = 1`). Under `-Znext-solver=globally`—made the nightly default between `1.98.0-nightly` and `1.102.0-nightly` via `CFG_DEFAULT_NEXT_SOLVER_GLOBALLY=1` (`src/bootstrap/src/core/build_steps/compile.rs:1375-1381`)—`SolverDelegate::well_formed_goals` calls `wf::unnormalized_obligations(..., DUMMY_SP, CRATE_DEF_ID)`, silently disabling the error (`rc = 0`) on all three constructs.
   - **Fixed-size `alloca` codegen seam (`place.rs:111-122`, `builder.rs:687-697`):** `PlaceRef::alloca` emits a scalable `alloca <vscale x 4 x i32>` only when `layout.peel_transparent_wrappers_from_non_1zst(bx)` is itself a scalable vector. Any non-transparent aggregate (`BackendRepr::Memory { sized: true }`) receives a fixed `alloca [32 x i8], align 16` inside a 48-byte AArch64 frame (`sub sp, sp, #0x30`, `canary` at `[sp, #0x10]`, saved `x29`/`x30` at `[sp, #0x20]`), while field assignment lowers to `str z0, [x0]` writing `16 * vscale` bytes. Live `qemu-aarch64 11.1.2` execution of safe generic `overwrite_first_safely(&mut pair, z42)` returns `17` on **SVE-128** (`vscale = 1`), **silently overwrites `pair.canary` and returns `42` with zero trap on SVE-256** (`vscale = 2`), and **smashes saved `x29`/`x30` and crashes with `SIGSEGV` (`rc = -11`) on SVE-512** (`vscale = 4`). Likewise, `Layout::new::<SvU32>().size() == 16` under-allocates heap containers (`Box::new`, `Vec::push`) for all `vscale >= 2`.

3. **Live RISC-V RVV Debuginfo ICE (`rc = 101`), Container Arity Mismatches, and DWARF Subrange Truncation:**
   - `Arch::supports_scalable_vectors` (`compiler/rustc_target/src/spec/mod.rs:1835-1845`) admits `AArch64 | RiscV32 | RiscV64`, so `--target=riscv64gc-unknown-linux-gnu -C target-feature=+v -C debuginfo=0` compiles cleanly (`rc = 0`, `<vscale x 4 x i32>`). Yet `build_scalable_vector_di_node` (`compiler/rustc_codegen_llvm/src/debuginfo/metadata.rs:1214` at HEAD, `1213` at `1.102.0-nightly`, `1158` at `1.98.0-nightly`) asserts `assert_matches!(cx.tcx.sess.target.arch, Arch::AArch64)` and hardcodes AArch64 DWARF `VG` register `46`, panicking with `rc = 101` whenever `-C debuginfo=2` is enabled on `RiscV64` or `RiscV32`.
   - On AArch64 with `-C debuginfo=2`, `metadata.rs:1229` computes `number_of_elements_per_vg = number_of_elements / 2`, causing `#[rustc_scalable_vector(1)] struct SvU64_1(u64)` to emit `DW_OP_constu, 0, DW_OP_bregx, 46, 0, DW_OP_mul, DW_OP_constu, 1, DW_OP_minus` (an unsigned wrap to `-1`).
   - Multi-vector containers `#[rustc_scalable_vector] struct SvU32xN(...)` lower `2..=8` homogeneous vectors to `{ <vscale x 4 x i32>, ... }` (`type_of.rs:34-44`) and reject `N >= 9` (`check.rs:1593-1600`). However, `check_scalable_vector` checks `fields.is_empty()` (`1..=8`) while `NumScalableVectors::from_field_count` (`rustc_abi/src/lib.rs:1814-1818`) admits only `2..=8` (and had an off-by-one `2..8` range in `1.98.0-nightly` that also ICEd at `N = 8`), so `SvU32x1(SvU32)` still triggers a live `delayed_bug` ICE (`rc = 101`).

4. **`#![feature(autodiff)]` and `core::intrinsics::offload` Codegen Gates:**
   Both intrinsics are declared as `pub const fn` in `library/core/src/intrinsics/mod.rs:3223,3263` and gated inside `compiler/rustc_codegen_llvm/src/intrinsic.rs:126-141,1771-1939`. `autodiff` requires `-Z autodiff=Enable`, fat (or linker-plugin) LTO, and an unshipped `libEnzyme-<LLVM_MAJOR>.so` dynamic library searched across sysroot target library paths (`enzyme_ffi.rs:450-479`). `offload` emits both `OffloadWithoutEnable` and `OffloadWithoutFatLTO` unless `-Z offload=<Device|Host=...>` and `-C lto=fat` are passed, and changed arity from 5 arguments in `1.98.0-nightly` to 6 arguments (adding `device_id: i32`) by `1.102.0-nightly`.

5. **Kernel-Checked Lean `v4.34.1` Mechanization & Verified-Compiler Trusted-Boundary Implications:**
   `support/ScalableVectorLayoutAndSizedHierarchySoundness.lean` (874 lines, 34 theorems, zero `sorry`, zero `Classical.choice`, zero `._unsafe_rec`, verified under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) mechanizes both the buggy layout/WF behavior (proving SVE-128 disjointness, SVE-256 silent canary overwrite, SVE-512 frame overflow and `x29`/`x30` smash, universal `vscale >= 2` canary/array/heap failures, `DUMMY_SP` tuple acceptance, RISC-V debuginfo gap, and `N = 1` container gap) and a sound four-tier `SizedHierarchy` (`ConstSized <: RuntimeSized <: MetaSized <: PointeeSized`) proving that requiring `ConstSized` on all non-transparent aggregate constituents and removing `!span.is_dummy()` restores substitution stability, `vscale`-invariance, field/array disjointness, and exact `PlaceRef::alloca` bounds for all `vscale >= 1`. In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst.MirTy` (`trusted/lean/Trusted/MirAst.lean:312-321`) currently maps all unmodeled types (including SIMD and scalable vectors) fail-closed to `.unsupported` (`FaultKind.unsupported`); any future verified-`rustc` extension supporting `SimdScalableVector` must enforce this `ConstSized`/`RuntimeSized` split and post-monomorphization aggregate rejection before codegen.

## Applicability

This report characterizes the interaction among seven durable subjects recorded in `REPORT.json`:

1. **`rust-lang/rust` across three pinned revisions:**
   - **HEAD source snapshot (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`, `2026-11-22`):** Primary-source audit of ABI, layout, HIR WF checking, trait-selection WF obligations, next-solver `SolverDelegate`, SSA/LLVM `alloca`, LLVM type lowering, DWARF debuginfo metadata, target-architecture capability tables, bootstrap nightly defaults, and `autodiff`/`offload` codegen gates.
   - **`rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `2026-11-11`, LLVM `23.1.5`):** Source comparison plus recorded live compilation and `qemu-aarch64 11.1.2 (Debian 1:11.1.2+ds-2)` execution (`support/recorded_1_102_qemu_sve_results.json`) across `aarch64-unknown-linux-gnu` (`+sve`), `riscv64gc-unknown-linux-gnu` (`+v`), and `x86_64-unknown-linux-gnu`.
   - **`rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `2026-05-31`, LLVM `22.1.6`):** Source comparison plus live compilation, LLVM IR emission, static AArch64 SVE ELF linking via bundled `ld.lld`, and `llvm-objdump` disassembly (`support/live_probe_1_98_results.json`) across `aarch64-unknown-linux-gnu`, `riscv64gc-unknown-linux-gnu`, `riscv32imac-unknown-none-elf`, and `x86_64-unknown-linux-gnu`.
2. **Version-specific divergences vs. shared behavior across `1.98.0-nightly`, `1.102.0-nightly`, and HEAD (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`):**

| Property / Behavior | `1.98.0-nightly` (`14210df0e`) | `1.102.0-nightly` (`3ef0c22cd`) | HEAD (`342d74463`) |
| :--- | :--- | :--- | :--- |
| `BackendRepr::SimdScalableVector` `is_unsized() == false` | Present (`lib.rs:1824`) | Present (`lib.rs:1885`) | Present (`lib.rs:1895`) |
| Generic struct/enum/union WF bypass (`wfcheck.rs`) | Live (`rc = 0`, both solvers) | Live (`rc = 0`, both solvers) | Present (`wfcheck.rs:1039`) |
| Direct & generic `[SvU32; 2]` array WF bypass (`wf.rs`) | Live (`rc = 0`, both solvers) | Live (`rc = 0`, both solvers) | Present (`wf.rs:812-827`) |
| `DUMMY_SP` tuple/closure bypass under `-Znext-solver=globally` | Live with explicit flag (`delegate.rs:242`, `wf.rs:781,792`) | **Default on nightly** (`CFG_DEFAULT_NEXT_SOLVER_GLOBALLY=1`) | **Default on nightly** (`compile.rs:1378`, `delegate.rs:381`, `wf.rs:838,849`) |
| Nightly default `-Znext-solver` mode | `coherence` (`compile.rs` omits env var) | `globally` (`compile.rs:1376`) | `globally` (`compile.rs:1378`) |
| `NumScalableVectors::from_field_count` range | `2..8` (`lib.rs:1757`, **`N=8` ICEs!**) | `2..=8` (`lib.rs:1806`, `N=1` still ICEs) | `2..=8` (`lib.rs:1816`, `N=1` still ICEs) |
| RISC-V RVV `-C debuginfo=2` ICE (`assert_matches!(..., Arch::AArch64)`) | Live (`rc = 101`, `metadata.rs:1158`) | Live (`rc = 101`, `metadata.rs:1213`) | Present (`metadata.rs:1214`) |
| `autodiff` Enzyme lookup artifact | `libEnzyme-22` folder in `<sysroot>/lib` | `libEnzyme-23.so` in `lib/rustlib/<host>/lib` | `libEnzyme-<LLVM_MAJOR>.<DLL_EXT>` (`enzyme_ffi.rs:456-458`) |
| `core::intrinsics::offload` arity | 5 arguments (no `device_id`) | 6 arguments (`device_id: i32`) | 6 arguments (`intrinsics/mod.rs:3263-3270`) |

3. **Normative, Verification-Boundary, and Formalization Subjects:**
   - **The Rust Reference (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):** Supplies the normative contract for `Sized` (`r[lang-types.sized.intro]`, `src/special-types-and-traits.md:188-198`) and dynamically sized types (`r[dynamic-sized.intro]`, `src/dynamically-sized-types.md:4-31`), which defines `Sized` strictly as having a compile-time-known fixed size.
   - **Anneal (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Interprets how these `rustc` layout, WF, and intrinsic seams affect a verified Rust MIR/codegen trusted boundary (`trusted/lean/Trusted/MirAst.lean:310-322`, `trusted/lean/Trusted/MirSemantics.lean`, `trusted/rustc-capture/src/driver.rs`).
   - **Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** Kernel-checks the formal model and theorems in `support/ScalableVectorLayoutAndSizedHierarchySoundness.lean`.

4. **Feature-Gate & Hardware Scope:**
   - `#[rustc_scalable_vector]` is an internal compiler attribute gated behind `#![feature(rustc_attrs)]` (intended to back `core::arch::aarch64` SVE types such as `svuint32_t`). However, once a downstream crate or `core::arch` re-exports a `#[rustc_scalable_vector]` type, **the generic struct, enum, union, tuple, array, closure, and `Layout::new` bypasses require zero `unsafe` code at the call site** and trigger on any AArch64 SVE target with `vscale >= 2` (256-bit hardware such as AWS Graviton3 / Arm Neoverse V1, 512-bit hardware such as Fujitsu A64FX, or QEMU `-cpu max,sve256=on` / `sve512=on`) as well as RISC-V RVV targets with `VLEN > 128`.
   - `#![feature(autodiff)]` and `#![feature(core_intrinsics)]` (`offload`) are nightly-only unstable features requiring explicit `-Z` flags (`-Z autodiff=Enable`, `-Z offload=...`) and `-C lto=fat`.

## Findings

### 1. Normative Violation: `BackendRepr::SimdScalableVector` Violates Rust's `Sized` Contract via a `vscale = 1` Layout Lower Bound

Basis: normative + source + execution

The Rust Reference defines `Sized` normatively as compile-time-known fixed size:

> `r[lang-types.sized.intro]`: "The `Sized` trait indicates that the size of this type is known at compile-time; that is, it's not a dynamically sized type." (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/special-types-and-traits.md:188-189`)

> `r[dynamic-sized.intro]`: "Most types have a fixed size that is known at compile time and implement the trait `Sized`. A type with a size that is known only at run-time is called a dynamically sized type (DST) or, informally, an unsized type." (`src/dynamically-sized-types.md:4-5`)

In `rust-lang/rust`, scalable vector types (`#[rustc_scalable_vector(N)] struct SvU32(u32)` and homogeneous container tuples `#[rustc_scalable_vector] struct SvU32xK(SvU32, ...)`) have a runtime byte size equal to `vscale * (count * elem_bytes * number_of_vectors)`, where `vscale >= 1` is a hardware-determined runtime vector-length multiplier (`VL / 128` on AArch64 SVE, where `VL ∈ {128, 256, 384, ..., 2048}` bits, so `vscale ∈ {1, 2, 3, ..., 16}`). Despite having a runtime-only byte size, `rustc` deliberately marks scalable vectors as `Sized` across three coupled compiler subsystems:

1. **ABI Representation (`compiler/rustc_abi/src/lib.rs:1867-1904` at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`; `L1857-1894` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`; `L1796-1833` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):**
   ```rust
   BackendRepr::SimdScalableVector {
       element: Scalar,
       count: BackendLaneCount,
       number_of_vectors: NumScalableVectors,
   },
   ...
   pub fn is_unsized(&self) -> bool {
       match *self {
           BackendRepr::Scalar(_)
           | BackendRepr::ScalarPair { .. }
           // FIXME(rustc_scalable_vector): Scalable vectors are `Sized` while the
           // `sized_hierarchy` feature is not yet fully implemented. After `sized_hierarchy` is
           // fully implemented, scalable vectors will remain `Sized`, they just won't be
           // `const Sized` - whether `is_unsized` continues to return `false` at that point will
           // need to be revisited and will depend on what `is_unsized` is used for.
           | BackendRepr::SimdScalableVector { .. }
           | BackendRepr::SimdVector { .. } => false,
           BackendRepr::Memory { sized } => !sized,
       }
   }
   ```
   Because `is_unsized()` returns `false`, `layout.is_sized()` returns `true` for every `SimdScalableVector` and every aggregate built from one.

2. **Layout Computation (`compiler/rustc_ty_utils/src/layout.rs:628-644` at HEAD & `1.102`, `L587-603` at `1.98`; `compiler/rustc_abi/src/layout.rs:207-224,979-1035` at HEAD):**
   `layout_of_uncached` dispatches `ty::Adt(def, _)` when `def.repr().scalable()` to `ty.scalable_vector_parts(tcx)` (`compiler/rustc_middle/src/ty/sty.rs:1274-1298`), then invokes `cx.calc.layout_of_scalable_vector_type(element_layout, element_count as u64, number_of_vectors)`, which executes `vector_type_layout`:
   ```rust
   let size = elt.size.checked_mul(count.as_u64(), dl).ok_or(LayoutCalculatorError::SizeOverflow)?;
   let (repr, size, align) = match kind {
       SimdVectorKind::Scalable(number_of_vectors) => (
           BackendRepr::SimdScalableVector { element, count, number_of_vectors },
           size.checked_mul(number_of_vectors.0 as u64, dl)
               .ok_or(LayoutCalculatorError::SizeOverflow)?,
           dl.rust_vector_align(size),
       ),
       ...
   };
   let size = size.align_to(align);
   ```
   This writes the **`vscale = 1` base byte size** into `LayoutData.size`: for `#[rustc_scalable_vector(4)] struct SvU32(u32)`, `elt.size = 4 B`, `count = 4`, `number_of_vectors = 1`, yielding `size = 16 B`, `align = 16 B`. Note also that for boolean predicate vectors `#[rustc_scalable_vector(16)] struct SvBool(bool)`, `elt.size = 1 B` yields `size = 16 B, align = 16 B` even though LLVM lowers it to `<vscale x 16 x i1>` (`type_of.rs:27-29`, 2 bytes at `vscale = 1`).

3. **Trait Solver Built-in `Sized` Implementation (`compiler/rustc_next_trait_solver/src/solve/trait_goals.rs:288-306` and `compiler/rustc_next_trait_solver/src/solve/assembly/structural_traits.rs:117-191` at HEAD):**
   `instantiate_constituent_tys_for_sizedness_trait` handles `ty::Adt(def, args)` solely via `def.sizedness_constraint(ecx.cx(), sizedness)`. Because `SvU32(u32)`'s field `u32` is `Sized`, `sizedness_constraint` returns `None`, so the compiler automatically implements both `Sized` and `MetaSized` for `SvU32` (and for `SvU32xK`). Every generic parameter `<T>` carries an implicit `T: Sized` bound (`r[lang-types.sized.implicit-sized]`), which `SvU32` satisfies unconditionally.

4. **Observed Compile-Time Layout Constants (`support/live_probe_1_98_results.json`, `ctfe_layout_sizes_and_offsets`):**
   Compiling on `rustc 1.98.0-nightly` with `--target=aarch64-unknown-linux-gnu -C target-feature=+sve -C opt-level=1 -Z merge-functions=disabled --emit=llvm-ir` emits exact constant folds:
   - `core::mem::size_of::<SvU32>()` -> `ret i64 16`
   - `core::mem::align_of::<SvU32>()` -> `ret i64 16`
   - `core::alloc::Layout::new::<SvU32>().size()` -> `ret i64 16`
   - `core::mem::offset_of!(GenericPair<SvU32>, canary)` -> `ret i64 16`
   - `core::mem::size_of::<GenericPair<SvU32>>()` -> `ret i64 32`

   Because `core::alloc::Layout::new::<SvU32>()` reports `16 B`, safe heap abstractions (`Box::new(sv)`, `Vec::push(sv)`) allocate `16 B` on the heap while subsequent scalable vector stores write `16 * vscale` bytes (`32 B` on SVE-256, `64 B` on SVE-512), constituting an immediate heap-buffer-overflow primitive alongside the stack-buffer-overflow primitive documented below.

---

### 2. Complete Well-Formedness Bypass Matrix: Generic Polymorphism, Unchecked Arrays, and the `-Znext-solver=globally` `DUMMY_SP` Regression

Basis: source + execution + derived

Because `SvU32` implements `Sized`, `rustc` attempts to prevent scalable vectors from appearing inside fixed-offset aggregates through ad-hoc syntactic checks scattered across `wfcheck.rs` and `wf.rs`. Primary-source inspection and live differential compilation reveal **three distinct soundness holes** across those checks:

#### 2.1 Hole A: Pre-Monomorphization Generic ADT Bypass (`wfcheck.rs:1039-1051`)
In `compiler/rustc_hir_analysis/src/check/wfcheck.rs:1030-1051` (HEAD `342d74463`; `L1040-1052` at `1.102`; `L1087-1099` at `1.98`):
```rust
let ty = wfcx.deeply_normalize(
    span,
    WellFormedLoc::None,
    tcx.type_of(field.did).instantiate_identity(),
);
wfcx.register_wf_obligation(span, WellFormedLoc::Ty(field_id), ty.into());

if matches!(ty.kind(), ty::Adt(def, _) if def.repr().scalable())
    && !matches!(adt_def.repr().scalable, Some(ScalableElt::Container))
{
    tcx.dcx().span_err(
        span,
        format!("scalable vectors cannot be fields of a {}", adt_def.variant_descr()),
    );
}
```
This check runs **strictly on the generic definition** (`instantiate_identity()`). When a struct `pub struct GenericPair<T> { pub first: T, pub canary: u64 }`, enum `pub enum GenericEnum<T> { A(T), B(u64) }`, or union `pub union GenericUnion<T: Copy> { pub a: T, pub b: u64 }` is checked, `ty.kind()` is `ty::Param(T)`—so `matches!(ty.kind(), ty::Adt(..))` evaluates to `false`. At monomorphization sites (`GenericPair<SvU32>`, `GenericEnum<SvU32>`, `GenericUnion<SvU32>`), `wfcheck` is never re-invoked, and trait WF only checks `SvU32: Sized`, which holds. All three compile with `rc = 0` under both `-Znext-solver=no` and `-Znext-solver=globally`, emitting fixed-size `sret([32 x i8])` (struct/enum) or `sret([16 x i8])` (union) paired with `store <vscale x 4 x i32>`.

#### 2.2 Hole B: Missing Array Element Check (`wf.rs:808-827`)
In `compiler/rustc_trait_selection/src/traits/wf.rs:808-827` (HEAD `342d74463`; identical logic in `1.102` and `1.98`):
```rust
ty::Slice(subty) => {
    self.require_sized(subty, ObligationCauseCode::SliceOrArrayElem);
}

ty::Array(subty, len) => {
    self.require_sized(subty, ObligationCauseCode::SliceOrArrayElem);
    ...
}
```
Neither `ty::Array` nor `ty::Slice` checks `subty.is_scalable_vector()`. Consequently, **even direct monomorphic arrays** `pub fn direct_arr(a: SvU32, b: SvU32) -> [SvU32; 2] { [a, b] }` bypass WF with **`rc = 0` under both `-Znext-solver=no` and `-Znext-solver=globally`**, emitting:
```llvm
define void @direct_arr(ptr sret([32 x i8]) align 16 %_0, <vscale x 4 x i32> %a, <vscale x 4 x i32> %b) {
  store <vscale x 4 x i32> %a, ptr %0, align 16   ; offset 0, writes [0, 16*vscale)
  store <vscale x 4 x i32> %b, ptr %1, align 16   ; offset 16, writes [16, 16 + 16*vscale)
}
```
At `vscale >= 2`, writing element `0` overlaps element `1` and writing element `1` overflows the `32 B` `sret` buffer by `16 * vscale - 16` bytes.

#### 2.3 Hole C: Live `-Znext-solver=globally` `DUMMY_SP` Tuple & Closure WF Regression (`delegate.rs:372-385`, `wf.rs:834-856`, `compile.rs:1375-1381`)
In `compiler/rustc_trait_selection/src/traits/wf.rs:834-856` (HEAD `342d74463`; `L833-855` at `1.102`; `L777-799` at `1.98`):
```rust
ty::Tuple(tys) => {
    if let Some((last, rest)) = tys.split_last() {
        for &elem in rest {
            self.require_sized(elem, ObligationCauseCode::TupleElem);
            if elem.is_scalable_vector() && !self.span.is_dummy() {
                self.tcx()
                    .dcx()
                    .struct_span_err(self.span, "scalable vectors cannot be tuple fields")
                    .emit();
            }
        }

        if last.is_scalable_vector() && !self.span.is_dummy() {
            self.tcx()
                .dcx()
                .struct_span_err(self.span, "scalable vectors cannot be tuple fields")
                .emit();
        }
    }
}
```
Notice the fatal design flaw: instead of emitting a failing predicate into `self.out`, `wf.rs` performs a side-effecting `struct_span_err` guarded by **`&& !self.span.is_dummy()`** (intended to avoid duplicate diagnostics during spanless internal queries). Under the old solver (`-Znext-solver=no`), `wf::obligations` receives the HIR obligation's real source span, so `!self.span.is_dummy()` is `true` and direct `(SvU32, u64)`, generic-instantiated `mk_pair::<SvU32>(v, 7)`, and closure upvar tuples `move || { let _ = v; canary }` are all rejected with `rc = 1`.

Under `-Znext-solver=globally`, however, `SolverDelegate::well_formed_goals` (`compiler/rustc_trait_selection/src/solve/delegate.rs:372-385` at HEAD & `1.102`; `L233-246` at `1.98`) canonicalizes WF checks by invoking `wf::unnormalized_obligations` with **`DUMMY_SP`**:
```rust
fn well_formed_goals(
    &self,
    param_env: ty::ParamEnv<'tcx>,
    term: ty::Term<'tcx>,
) -> Option<Vec<Goal<'tcx, ty::Predicate<'tcx>>>> {
    crate::traits::wf::unnormalized_obligations(
        &self.0,
        param_env,
        term,
        DUMMY_SP,
        CRATE_DEF_ID,
    )
    .map(|obligations| obligations.into_iter().map(|obligation| obligation.as_goal()).collect())
}
```
Because `DUMMY_SP.is_dummy() == true`, both `if` guards in `wf.rs:838,849` evaluate to `false`, zero error is emitted, and `well_formed_goals` returns only `[Sized(SvU32), Sized(u64)]`, which trivially succeeds! Furthermore, between `1.98.0-nightly` and `1.102.0-nightly`, `src/bootstrap/src/core/build_steps/compile.rs:1375-1381` enabled `cargo.env("CFG_DEFAULT_NEXT_SOLVER_GLOBALLY", "1")` on all nightly compiler builds (read by `NextSolverConfig::default()` in `compiler/rustc_session/src/config.rs:1078-1086`), flipping this `DUMMY_SP` bypass from an opt-in `-Z` flag regression into a **default nightly soundness regression**.

#### 2.4 Complete Empirical Solver Matrix (`1.98.0-nightly` Live + `1.102.0-nightly` Recorded)

| Construct | Rust Expression | `-Znext-solver=no` | `-Znext-solver=globally` | `1.98.0` Default (`coherence`) | `1.102.0` Default (`globally`) | Emitted LLVM IR (when `rc = 0`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| Direct struct field | `struct Bad { v: SvU32, x: u64 }` | `rc = 1` (rejected) | `rc = 1` (rejected) | `rc = 1` | `rc = 1` | — |
| Direct enum field | `enum Bad { A(SvU32), B(u64) }` | `rc = 1` (rejected) | `rc = 1` (rejected) | `rc = 1` | — (same `wfcheck`) | — |
| Direct union field | `union Bad { v: SvU32, x: u64 }` | `rc = 1` (rejected) | `rc = 1` (rejected) | `rc = 1` | — (same `wfcheck`) | — |
| **Direct tuple** | `fn f(v: SvU32) -> (SvU32, u64)` | **`rc = 1`** (rejected) | **`rc = 0` (BYPASS)** | **`rc = 1`** | **`rc = 0` (BYPASS)** | `sret([32 x i8])`, `store <vscale x 4 x i32>` |
| **Generic tuple** | `fn mk<T>(a: T, b: u64) -> (T, u64)` | **`rc = 1`** (rejected) | **`rc = 0` (BYPASS)** | **`rc = 1`** | **`rc = 0` (BYPASS)** | `alloca [32 x i8]`, `sret([32 x i8])`, `store <vscale x 4 x i32>` |
| **Closure capture** | `move \|\| { let _ = v; canary }` | **`rc = 1`** (rejected) | **`rc = 0` (BYPASS)** | **`rc = 1`** | **`rc = 0` (BYPASS)** | Closure env with `<vscale x 4 x i32>` |
| **Direct array** | `fn f(a: SvU32, b: SvU32) -> [SvU32; 2]` | **`rc = 0` (BYPASS)** | **`rc = 0` (BYPASS)** | **`rc = 0`** | **`rc = 0` (BYPASS)** | `sret([32 x i8])`, 2× `store <vscale x 4 x i32>` @ 16 B stride |
| **Generic array** | `fn mk<T>(a: T, b: T) -> [T; 2]` | **`rc = 0` (BYPASS)** | **`rc = 0` (BYPASS)** | **`rc = 0`** | **`rc = 0` (BYPASS)** | `sret([32 x i8])`, 2× `store <vscale x 4 x i32>` @ 16 B stride |
| **Generic struct** | `struct GenericPair<T> { first: T, canary: u64 }` | **`rc = 0` (BYPASS)** | **`rc = 0` (BYPASS)** | **`rc = 0`** | **`rc = 0` (BYPASS)** | `alloca [32 x i8]`, `store <vscale x 4 x i32>` at offset 0 |
| **Generic enum** | `enum GenericEnum<T> { A(T), B(u64) }` | **`rc = 0` (BYPASS)** | **`rc = 0` (BYPASS)** | **`rc = 0`** | — (same `wfcheck`) | `sret([32 x i8])`, `store <vscale x 4 x i32>` |
| **Generic union** | `union GenericUnion<T: Copy> { a: T, b: u64 }` | **`rc = 0` (BYPASS)** | **`rc = 0` (BYPASS)** | **`rc = 0`** | — (same `wfcheck`) | `sret([16 x i8])`, `store <vscale x 4 x i32>` |

---

### 3. Codegen Seam & Live AArch64 SVE-128 / SVE-256 / SVE-512 Stack-Smashing Mechanics

Basis: source + execution

Once any non-transparent aggregate containing `SvU32` passes type checking, `rustc_codegen_ssa` and `rustc_codegen_llvm` lower its stack allocation via `PlaceRef::alloca` (`compiler/rustc_codegen_ssa/src/mir/place.rs:111-122` at HEAD):
```rust
pub fn alloca<Bx: BuilderMethods<'a, 'tcx, Value = V>>(
    bx: &mut Bx,
    layout: TyAndLayout<'tcx>,
) -> Self {
    // FIXME(rustc_scalable_vector/stdarch_aarch64_sve): Scalable vectors aren't actually sized,
    // but we pretend they are. Here we have to hack around that.
    if layout.peel_transparent_wrappers_from_non_1zst(bx).deref().is_scalable_vector() {
        Self::alloca_scalable(bx, layout)
    } else {
        Self::alloca_size(bx, layout.size, layout)
    }
}
```
Only when the **outermost** peeled local is itself a scalable vector does `alloca_scalable` invoke `Builder::alloca_with_ty` (`compiler/rustc_codegen_llvm/src/builder.rs:687-697` at HEAD; `L688-698` at `1.102`; `L612-627` at `1.98`), emitting `LLVMBuildAlloca(bx.llbuilder(), layout.llvm_type(self.cx), UNNAMED)` -> `alloca <vscale x 4 x i32>, align 16`. For `GenericPair<SvU32>`, `(SvU32, u64)`, `[SvU32; 2]`, `GenericEnum<SvU32>`, or a capturing closure, the outer `BackendRepr` is `BackendRepr::Memory { sized: true }`, so `PlaceRef::alloca` falls through to `Self::alloca_size(bx, layout.size, layout)` -> `alloca [32 x i8], align 16`.

#### 3.1 Exact Disassembled AArch64 SVE Machine Code (`support/live_probe_1_98_results.json`)
Compiling the standalone `#![no_std]` reproducer (`GenericPair<T> { first: T, canary: u64 }`, `#[inline(never)] fn overwrite_first_safely<T>(p: &mut GenericPair<T>, v: T) { p.first = v; }`) with `rustc 1.98.0-nightly --target=aarch64-unknown-linux-gnu -C target-feature=+sve -C opt-level=2` and linking with bundled `ld.lld` yields the following exact `llvm-objdump -d --mattr=+sve` disassembly:

```asm
00000000002101f0 <overwrite_first_safely::<SvU32>>:
  2101f0: 25b8c540      mov     z0.s, #0x2a             // splat 42 across all VL/4 32-bit lanes
  2101f4: e5804000      str     z0, [x0]                // store 16 * vscale bytes at [x0 + 0 .. x0 + 16*vscale)
  2101f8: d65f03c0      ret

0000000000210214 <run_test>:
  210214: d100c3ff      sub     sp, sp, #0x30           // fixed 48-byte stack frame
  210218: a9027bfd      stp     x29, x30, [sp, #0x20]   // saved FP (x29) & LR (x30) at [sp+32 .. sp+48)
  21021c: 910083fd      add     x29, sp, #0x20
  210220: 6f00e400      movi    v0.2d, #0000000000000000
  210224: 910003e8      mov     x8, sp
  210228: 52800229      mov     w9, #0x11               // canary = 17
  21022c: 910003e0      mov     x0, sp
  210230: e5804100      str     z0, [x8]                // pair.first = z0 at [sp+0 .. sp+16*vscale)
  210234: f9000be9      str     x9, [sp, #0x10]         // pair.canary = 17 at [sp+16 .. sp+24)
  210238: 97ffffee      bl      <overwrite_first_safely::<SvU32>>
  21023c: 394043e0      ldrb    w0, [sp, #0x10]         // read pair.canary & 0xff
  210240: a9427bfd      ldp     x29, x30, [sp, #0x20]   // restore saved FP & LR from [sp+32 .. sp+48)
  210244: 9100c3ff      add     sp, sp, #0x30
  210248: d65f03c0      ret
```

#### 3.2 Stack-Frame Memory Geometry & Live `qemu-aarch64 11.1.2` Execution Results (`support/recorded_1_102_qemu_sve_results.json`)
The fixed 48-byte frame of `run_test` lays out:
- `[sp + 0,  sp + 16)`: `pair.first` (`SvU32` static `vscale = 1` slot)
- `[sp + 16, sp + 24)`: `pair.canary` (`u64 = 0x11`)
- `[sp + 24, sp + 32)`: 8 bytes tail padding aligning `GenericPair<SvU32>` to 16 B (`size = 32 B`)
- `[sp + 32, sp + 40)`: saved frame pointer `x29`
- `[sp + 40, sp + 48)`: saved return link register `x30`

When `overwrite_first_safely` executes `str z0, [x0]` (`x0 = sp`) with `z0.s = 0x2a` (`42`), the single SVE unpredicated store writes `VL = 16 * vscale` bytes starting at `sp + 0`:

| Hardware SVE Configuration | `vscale` | `VL` (Bytes Written) | CTFE `size_of::<SvU32>()` | Bytes Overwritten Relative to `sp` | Observed Exit Code (`qemu-aarch64 11.1.2` / `rustc 1.102.0`) | Failure Class |
| :--- | ---: | ---: | ---: | :--- | ---: | :--- |
| **SVE-128** (`sve128=on`) | `1` | `16 B` | `16 B` | `[0, 16)` (`pair.first` only) | **`17`** (`0x11`, expected) | Uncorrupted baseline (masks bug on 128-bit CI runners!) |
| **SVE-256** (`sve256=on`, e.g., Graviton3 / Neoverse V1) | `2` | `32 B` | `16 B` | `[0, 32)` (clobbers `canary` at `[16, 24)` with `0x0000002a_0000002a`; stops cleanly before `x29`/`x30` at `32`) | **`42`** (`0x2a`, silent corruption, empty stderr) | **Silent memory corruption (zero crash)** |
| **SVE-512** (`sve512=on`, e.g., Fujitsu A64FX) | `4` | `64 B` | `16 B` | `[0, 64)` (overflows `32 B` local by `32 B` and `48 B` frame by `16 B`, smashing saved `x29`/`x30` at `[32, 48)` with `0x0000002a_0000002a`) | **`-11`** (`qemu: uncaught target signal 11 (Segmentation fault) - core dumped`) | **Control-flow hijacking stack-buffer overflow (`SIGSEGV`)** |

Crucially, because SVE-128 (`vscale = 1`) returns the expected value `17`, any test suite executing on 128-bit SVE hardware (or QEMU defaulting to 128-bit SVE) observes zero anomalies, whereas deploying the exact same compiled binary onto 256-bit SVE silicon silently corrupts adjacent struct fields and deploying onto 512-bit SVE silicon overwrites the saved link register `x30` with attacker/data-controlled vector lanes.

---

### 4. Multi-Vector Scalable Containers (`1..=8` vs `2..=8`), RISC-V RVV `-C debuginfo=2` Live ICE, and AArch64 DWARF `element_count = 1` Truncation

Basis: source + execution

#### 4.1 Multi-Vector Container Lowering and the Live `SvU32x1` ICE
`rustc` supports homogeneous scalable-vector container tuple structs annotated with `#[rustc_scalable_vector]` (without an element count), lowered in `compiler/rustc_codegen_llvm/src/type_of.rs:26-45` (HEAD & `1.102`):
```rust
BackendRepr::SimdScalableVector { ref element, count, number_of_vectors } => {
    let element = if element.is_bool() { cx.type_i1() } else { layout.scalar_llvm_type_at(cx, *element) };
    let vector_type = cx.type_scalable_vector(element, count.as_u64());
    return match number_of_vectors.0 {
        1 => vector_type,
        2 => cx.type_struct(&[vector_type; 2]),
        ...
        8 => cx.type_struct(&[vector_type; 8]),
        _ => bug!("`#[rustc_scalable_vector]` tuple struct with too many fields"),
    };
}
```
Validation is split across two inconsistent bounds:
- **HIR check (`compiler/rustc_hir_analysis/src/check/check.rs:1585-1600`):** rejects `fields.is_empty()` (`"scalable vector tuples must have at least one field"`) and `fields.len() > 8` (`"scalable vector tuples can have at most eight fields"`), accepting **`1..=8`** fields (and requiring all fields to be the identical `ScalableElt::ElementCount` type, rejecting nested containers at `L1638-1644`).
- **ABI / layout (`compiler/rustc_abi/src/lib.rs:1814-1818` at HEAD, `L1804-1808` at `1.102`, `L1755-1759` at `1.98`):** `NumScalableVectors::from_field_count` returns `Some` only for **`2..=8`** at HEAD/`1.102` (and had an off-by-one exclusive range **`2..8`** in `1.98.0-nightly`!).
- **Consequence (`support/live_probe_1_98_results.json`, `support/recorded_1_102_qemu_sve_results.json`):**
  - `SvU32x2(SvU32, SvU32)` compiles with `rc = 0` -> `{ <vscale x 4 x i32>, <vscale x 4 x i32> }`.
  - `SvU32x9(...)` is cleanly rejected (`rc = 1`: `"scalable vector tuples can have at most eight fields"`).
  - **`SvU32x1(SvU32)` passes `check_scalable_vector` yet returns `None` from `scalable_vector_parts` (`compiler/rustc_middle/src/ty/sty.rs:1284`), hitting `delayed_bug("`#[rustc_scalable_vector]` was applied to an invalid type")` in `layout.rs:634` -> live ICE (`rc = 101`) across all three audited revisions!**
  - In `1.98.0-nightly`, `SvU32x8` additionally hit the same `delayed_bug` ICE (`rc = 101`) due to the `2..8` typo (fixed to `2..=8` by `1.102.0-nightly`).

#### 4.2 Architecture Whitelist vs. Live RISC-V RVV `-C debuginfo=2` ICE (`rc = 101`)
AST validation (`compiler/rustc_ast_passes/src/ast_validation.rs:1659-1664`) gates `#[rustc_scalable_vector]` on `Arch::supports_scalable_vectors()` (`compiler/rustc_target/src/spec/mod.rs:1835-1845`):
```rust
pub fn supports_scalable_vectors(&self) -> bool {
    use Arch::*;
    match self {
        AArch64 | RiscV32 | RiscV64 => true,
        AmdGpu | Arm | ... | X86 | X86_64 | Xtensa | Other(_) => false,
    }
}
```
Accordingly, `x86_64-unknown-linux-gnu` fails cleanly at AST validation (`rc = 1`, `"scalable vectors are not supported on this architecture"`), while `--target=riscv64gc-unknown-linux-gnu -C target-feature=+v -C debuginfo=0` compiles cleanly (`rc = 0`, emitting `define <vscale x 4 x i32> @id_rv(<vscale x 4 x i32> %v)`).

However, when debuginfo is enabled (`-C debuginfo=2`), `build_struct_type_di_node` (`compiler/rustc_codegen_llvm/src/debuginfo/metadata.rs:1120-1132`) dispatches to `build_scalable_vector_di_node` (`L1200-1275` at HEAD; `L1199-1274` at `1.102`; `L1144-1219` at `1.98`), which executes:
```rust
assert!(adt_def.repr().scalable());
// This logic is specific to AArch64 for the moment, but can be extended for other architectures
// later.
assert_matches!(cx.tcx.sess.target.arch, Arch::AArch64);
```
Because `RiscV64` and `RiscV32` are accepted by `supports_scalable_vectors()` but rejected by this unconditional assertion, **both `--target=riscv64gc-unknown-linux-gnu -C target-feature=+v -C debuginfo=2` and `--target=riscv32imac-unknown-none-elf -C target-feature=+v -C debuginfo=2` crash `rustc` with `rc = 101`**:
```text
thread 'rustc' panicked at <RUSTC_SRC>/compiler/rustc_codegen_llvm/src/debuginfo/metadata.rs:1213:5:
assertion `left matches right` failed
  left: RiscV64
 right: Arch::AArch64
```
(line `1158:5` on `1.98.0-nightly`, `1213:5` on `1.102.0-nightly`, `1214:5` at HEAD `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`).

#### 4.3 AArch64 DWARF `number_of_elements / 2` Integer-Division Wrap for `element_count = 1`
Inside `build_scalable_vector_di_node` (`metadata.rs:1228-1240`), `rustc` computes the DWARF `DISubrange` upper bound using AArch64's 64-bit vector granule register `VG` (DWARF register `46`, where `VG = VL / 64 = 2 * vscale`):
```rust
let number_of_elements: u64 = (element_count as u64) * (number_of_vectors.0 as u64);
let number_of_elements_per_vg = number_of_elements / 2;
// `($number_of_elements_per_vector_granule * (value_of_register(AArch64::VG) + 0)) - 1`
```
For `SvU32` (`element_count = 4`, `number_of_vectors = 1`), `4 / 2 = 2`, emitting valid `!DISubrange(lowerBound: 0, upperBound: !DIExpression(DW_OP_constu, 2, DW_OP_bregx, 46, 0, DW_OP_mul, DW_OP_constu, 1, DW_OP_minus))` (observed live in `aarch64_sve_debuginfo2_ok`). However, `check_scalable_vector` does not enforce even `element_count`: for `#[rustc_scalable_vector(1)] struct SvU64_1(u64)`, integer division `1 / 2 == 0` emits (verified live in `aarch64_sve_debuginfo2_count1_div2_zero`):
```llvm
!18 = !DISubrange(lowerBound: 0, upperBound: !DIExpression(DW_OP_constu, 0, DW_OP_bregx, 46, 0, DW_OP_mul, DW_OP_constu, 1, DW_OP_minus))
```
which evaluates to `0 * VG - 1 = 0xFFFF_FFFF_FFFF_FFFF` (`-1`) at runtime in any DWARF consumer!

---

### 5. `#![feature(autodiff)]` and `core::intrinsics::offload` Codegen Gates

Basis: source + execution

Both `autodiff` and `offload` enter `rustc_codegen_llvm` through `pub const fn` compiler intrinsics declared in `library/core/src/intrinsics/mod.rs:3221-3270` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`)—notably **neither intrinsic carries an `unsafe` qualifier** (both are gated by `#![feature(core_intrinsics)]` or macro expansion under `#![feature(autodiff)]`):

```rust
#[rustc_nounwind]
#[rustc_intrinsic]
pub const fn autodiff<F, G, T: crate::marker::Tuple, R>(f: F, df: G, args: T) -> R;

#[rustc_nounwind]
#[rustc_intrinsic]
pub const fn offload<F, T: crate::marker::Tuple, R>(
    f: F,
    workgroup_dim: [u32; 3],
    thread_dim: [u32; 3],
    dyn_cache: u32,
    device_id: i32,
    args: T,
) -> R;
```

#### 5.1 `#![feature(autodiff)]` Expansion, LTO Requirement, and Unshipped `libEnzyme` Sysroot Plugin
1. **Macro expansion (`compiler/rustc_builtin_macros/src/autodiff.rs:175-225`):** `#[autodiff_reverse(...)]` / `#[autodiff_forward(...)]` annotate the primal with `#[rustc_autodiff]` and synthesize a differentiated stub whose body calls `std::intrinsics::autodiff(primal, diff_fn, args)`.
2. **Codegen gate (`compiler/rustc_codegen_llvm/src/intrinsic.rs:126-128,1771-1854`):** `codegen_autodiff` checks:
   - `tcx.sess.opts.unstable_opts.autodiff.contains(&AutoDiff::Enable)` -> otherwise emits `AutoDiffWithoutEnable` (`"using the autodiff feature requires -Z autodiff=Enable"`).
   - For executables, `tcx.sess.lto() == Lto::Fat` (for libraries, `Lto::Fat || linker_plugin_lto.enabled()`) -> otherwise emits `AutoDiffWithoutLto` (`"using the autodiff feature requires setting lto=\"fat\" in your Cargo.toml"`).
3. **Three-pass LLVM optimization pipeline (`compiler/rustc_codegen_llvm/src/back/write.rs:538-575`):** Differentiation requires running LLVM optimization in three segments (`PreAD` disabling size-increasing vectorization/unrolling, `DuringAD` invoking Enzyme passes, and `PostAD` re-optimizing the differentiated IR).
4. **Dynamic Enzyme library resolution (`compiler/rustc_codegen_llvm/src/llvm/enzyme_ffi.rs:450-479`):** `EnzymeWrapper` dynamically searches every sysroot target libdir (`filesearch::make_target_lib_path(p, host_tuple())`) for `libEnzyme-<LLVMRustVersionMajor()>.<DLL_EXTENSION>` (e.g., `libEnzyme-23.so` on `1.102.0-nightly` / LLVM `23.1.5`; `libEnzyme-22` folder under `<sysroot>/lib` in `1.98.0-nightly` / LLVM `22.1.6`). Because stock rustup nightlies do not distribute `libEnzyme`, enabling `-Z autodiff=Enable -C lto=fat` fails deterministically with `AutoDiffComponentMissing` (`rc = 1`: `"autodiff backend not found in the sysroot ... note: it will be distributed via rustup in the future"`).

#### 5.2 `core::intrinsics::offload` Safe-Intrinsic Codegen Gates
In `compiler/rustc_codegen_llvm/src/intrinsic.rs:129-141,1860-1939`:
- `sym::offload` checks **both** `tcx.sess.opts.unstable_opts.offload.is_empty()` (`OffloadWithoutEnable`: `"using the offload feature requires -Z offload=<Device or Host=/absolute/path/to/<crate>.ptx or <crate>.elf>"`) **and** `tcx.sess.lto() != Lto::Fat` (`OffloadWithoutFatLTO`: `"using the offload feature requires -C lto=fat"`).
- Note the `rustc` signature evolution confirmed live: `1.98.0-nightly` takes 5 arguments (omitting `device_id: i32` and citing `<crate>/device.bin` in `OffloadWithoutEnable`), whereas `1.102.0-nightly` and HEAD (`342d74463`) take 6 arguments (inserting `device_id: i32` before `args: T` and citing `.ptx` / `.elf`).
- Even though `offload` is marked `pub const fn` (not `unsafe`), invoking it without flags deterministically fails codegen with both errors (`rc = 1`, `2 previous errors`) before reaching `gpu_offload::gen_call_handling`, and device compilation (`-Z offload=Device`) additionally rewrites `offload-kernel` LLVM functions inside `back/write.rs:749-763`.

---

### 6. Kernel-Checked Lean `v4.34.1` Formalization (`support/ScalableVectorLayoutAndSizedHierarchySoundness.lean`)

Basis: source + execution + derived

To eliminate ambiguity about the exact algebraic cause of the stack-smashing bug and prove the exact sufficient typing discipline to restore soundness, `support/ScalableVectorLayoutAndSizedHierarchySoundness.lean` (874 lines, 219 local declarations, 34 theorems, kernel-checked in `Lean v4.34.1` with `0` `sorry`, `0` `Classical.choice`, `0` `Quot.sound`, `0` `Lean.ofReduceBool`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, and `0` `._unsafe_rec` verified via MetaM over `env.constants.map₂`) mechanizes three components:

#### 6.1 Symbolic `vscale >= 1` Layout vs. `rustc`'s Buggy Model
- `Ty` models scalars (`scalar bytes align`), scalable vectors/containers (`sv lanes elemBytes numVecs`), generic type parameters (`param id`), 2-field structs (`struct2 f0 f1`), 2-tuples (`tuple2 f0 f1`), fixed-length arrays (`arr elem len`), and `#[repr(transparent)]` wrappers (`transparent inner`), together with monomorphization substitution `subst (env : Nat -> Ty) : Ty -> Ty`.
- `runtimeSize (vscale : Nat) : Ty -> Nat` computes true hardware byte size (`alignUp (vscale * (lanes * elemBytes) * numVecs) (lanes * elemBytes)` for `sv`, aligned field layout for `struct2`/`tuple2`, `len * runtimeSize vscale elem` for `arr`).
- `staticSizeBuggy t := runtimeSize 1 t`, `staticField1OffsetBuggy f0 f1 := alignUp (staticSizeBuggy f0) (runtimeAlign f1)`, and `allocaBytesBuggy vscale t` (peeling `transparent` wrappers and allocating `runtimeSize vscale t` iff `isScalableVector (peelTransparent t)`, else `staticSizeBuggy t`) faithfully mirror `rustc_abi/src/layout.rs:979-1035` and `rustc_codegen_ssa/src/mir/place.rs:111-122`.
- `wfCheckBuggy (isDummySpan : Bool) : Ty -> Bool` faithfully mirrors `wfcheck.rs:1039` (syntactic `isScalableVector` on uninstantiated struct fields), `wf.rs:812` (no array element check), and `wf.rs:838,849` (`!isDummySpan`-gated tuple check).

#### 6.2 Mechanized Bug & Counterexample Theorems (Axioms: `[propext]` or `[]`)
| Lean Theorem | Formal Statement Summary | Mirrors Empirical Observation |
| :--- | :--- | :--- |
| `generic_pair_wf_bypass_both_solvers` | `∀ isDummy, wfCheckBuggy isDummy genericPairTy = true ∧ wfCheckBuggy isDummy concretePairTy = false` | Generic struct bypasses `wfcheck.rs:1039` under both solvers while direct struct is rejected |
| `direct_tuple_dummysp_next_solver_bypass` | `wfCheckBuggy false directTupleTy = false ∧ wfCheckBuggy true directTupleTy = true` | `-Znext-solver=no` (`rc=1`) vs. `-Znext-solver=globally` `DUMMY_SP` (`rc=0`) |
| `direct_array_unconditional_bypass` | `∀ isDummy, wfCheckBuggy isDummy directArrayTy = true` | Direct `[SvU32; 2]` bypasses WF under both solvers (`wf.rs:812`) |
| `sve128_no_corruption` | At `vscale = 1`: `field0WriteRange 1 svU32` (`[0, 16)`) is disjoint from `canary` (`[16, 24)`) and within `32 B` `alloca` | SVE-128 returns `17` (masks bug on 128-bit hosts) |
| `sve256_silent_canary_overwrite` | At `vscale = 2`: `field0WriteRange 2 svU32` (`[0, 32)`) contains & overlaps `canary` (`[16, 24)`), stays within `32 B` `alloca`, and is disjoint from `savedFpLrSlot 32` (`[32, 48)`) | SVE-256 silently returns `42` with zero crash |
| `sve512_stack_frame_overflow_and_lr_smash` | At `vscale = 4`: `len = 32 + 32`, `¬ withinFrame ... 32`, `¬ withinFrame ... 48`, and `contains ... (savedFpLrSlot 32)` | SVE-512 smashes saved `x29`/`x30` -> `SIGSEGV` (`rc = -11`) |
| `buggy_canary_corrupted_for_all_vscale_ge_2` | `∀ vscale ≥ 2`, `field0WriteRange vscale svU32` contains & overlaps `canary` | All SVE widths `>= 256` bits corrupt adjacent fields |
| `buggy_alloca_overflows_for_all_vscale_ge_3` | `∀ vscale ≥ 3`, `¬ withinFrame (field0WriteRange vscale svU32) 32` | All SVE widths `>= 384` bits overflow the `32 B` local |
| `buggy_array_elem_overlap_for_all_vscale_ge_2` | `∀ vscale ≥ 2`, `[SvU32; 2]` element 0 overlaps element 1 and element 1 overflows `32 B` `alloca` | Direct/generic `[SvU32; 2]` corrupts & overflows for all `vscale >= 2` |
| `buggy_heap_layout_overflow_for_all_vscale_ge_2` | `∀ vscale ≥ 2`, `staticSizeBuggy svU32 < runtimeSize vscale svU32` | `Layout::new::<SvU32>().size() == 16` under-allocates `Box`/`Vec` |
| `riscv_debuginfo_capability_gap` | `supportsScalableVectors` holds on `.riscv64` and `.riscv32` while `debuginfoSupportsScalableVectors` is `false` | Live `rc = 101` ICE at `metadata.rs:1213/1214` |
| `container_x1_check_vs_layout_gap` | `checkScalableContainerArity 1 = true ∧ layoutContainerArity 1 = false` | Live `SvU32x1` `delayed_bug` ICE (`rc = 101`) |

#### 6.3 Sound Four-Tier `SizedHierarchy` Substitution-Stable Discipline Theorem
`SizedTier` stratifies sizedness into `constSized <: runtimeSized <: metaSized <: pointeeSized` (`tierLe`), separating compile-time-constant-size types (`isConstSized Γ`, which returns `false` on `.sv`) from runtime-scalable stack/register types (`isRuntimeSized Γ`, which admits `.sv` and nested `transparent` wrappers around `.sv`). `wfSound Γ t` requires:
- Every non-transparent aggregate constituent (`struct2`, `tuple2`, `arr`) to satisfy `isConstSized Γ` **unconditionally** (zero `Span` parameter -> completely immune to `DUMMY_SP` canonicalization in `-Znext-solver=globally`), and
- Generic instantiations `env` to satisfy `EnvRespects Γ env` (every `env i` is closed and satisfies the tier bound `Γ i`).

Under this discipline, Lean's kernel verifies six universal soundness theorems across **all** `Γ`, **all** bound-respecting `env`, **all** `t : Ty`, and **all** `vscale : Nat`:
1. **`isConstSized_subst_stable` & `wfSound_subst_stable`:** Monomorphization preserves both `isConstSized` and `wfSound` (eliminating pre-monomorphization generic WF bypasses).
2. **`isConstSized_vscale_invariant`:** Every closed `ConstSized` type satisfies `runtimeSize vscale t = staticSizeBuggy t` for every `vscale : Nat`.
3. **`sound_runtimeSized_alloca_exact`:** For **every** `wfSound` type `t` (both `ConstSized` aggregates and `RuntimeSized` scalable vectors / arbitrarily nested `#[repr(transparent)]` wrappers), `allocaBytesBuggy vscale (subst env t) = runtimeSize vscale (subst env t)` for every `vscale : Nat`—proving that `PlaceRef::alloca`'s `peel_transparent_wrappers` lowering is **exact and sound once `ConstSized` guards all non-transparent aggregates**!
4. **`sound_struct2_disjoint_and_in_bounds` & `sound_tuple2_disjoint_and_in_bounds`:** For every `wfSound` struct or tuple, field 0's runtime write is strictly disjoint from field 1's slot, both slots remain within `allocaBytesBuggy`, and total runtime size equals `staticSizeBuggy`.
5. **`sound_array_disjoint_and_in_bounds`:** For every `wfSound` array `[elem; len]` and every `i < j < len`, element `i` and element `j` have strictly disjoint runtime write ranges and stay within `allocaBytesBuggy`.
6. **`sound_discipline_classifies_all_cases`:** `GenericPair<T>` requires `T: ConstSized` (rejected under `T: RuntimeSized`), `SvU32` fails `ConstSized`, direct `(SvU32, u64)` and `[SvU32; 2]` are rejected, while standalone `SvU32` and `#[repr(transparent)]` wrappers around `SvU32` remain permitted.

---

### 7. Implications for Anneal and Verified `rustc` Trusted Boundaries

Basis: source + derived

Inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` confirms that Anneal's current trusted MIR model (`trusted/lean/Trusted/MirAst.lean:310-322`) defines `MirTy` over `{bool, int, unit, never, enum, tuple, ref, rawPtr, unsupported}`, mapping all unmodeled types (including SIMD, scalable vectors, closures, and coroutines) fail-closed to `.unsupported`, which triggers `FaultKind.unsupported` in `trusted/lean/Trusted/MirSemantics.lean` (and `trusted/rustc-capture/src/driver.rs:25,45-47` pins a specific nightly compiler version). This fail-closed posture prevents `SimdScalableVector`, `autodiff`, and `offload` from silently entering Anneal's proof obligations today.

For any verified-`rustc` MIR/codegen pipeline or future Anneal extension that admits scalable vectors, four concrete trusted-boundary invariants follow directly from this audit:
1. **Post-monomorphization layout rejection gate (defense-in-depth):** Never rely solely on HIR-level `wfcheck` or span-guarded `wf.rs` errors. Before lowering MIR or computing fixed field offsets, verify on every monomorphized `TyAndLayout` that no `BackendRepr::Memory` aggregate (struct, enum, union, tuple, array, closure, coroutine) transitively contains a `BackendRepr::SimdScalableVector` field.
2. **Enforce `ConstSized` vs. `RuntimeSized` in the type system and MIR contract:** Reject `core::mem::size_of::<T>()` and `core::alloc::Layout::new::<T>()` for `RuntimeSized` types unless parameterized by symbolic `vscale` (eliminating both stack and heap under-allocation).
3. **Eliminate span-dependent soundness checks:** Treat any `Span::is_dummy()` guard on a soundness-critical diagnostic in trait/WF evaluation as a trusted-boundary violation; emit an explicit unsatisfiable predicate/error term instead so canonicalized solvers (`-Znext-solver=globally`) fail closed.
4. **Target-capability & external-plugin quarantine:** Require `debuginfo` capability parity with `Arch::supports_scalable_vectors()` before admitting RISC-V RVV under `-C debuginfo > 0`, align container arity checks (`2..=8`) across `check_scalable_vector` and `NumScalableVectors::from_field_count`, and treat `sym::autodiff` (external `libEnzyme-*.so` binary plugin) and `sym::offload` (external GPU PTX/ELF linker pipeline) as outside the verified single-target codegen TCB.

## Boundaries

- **Physical AArch64 SVE / RISC-V RVV silicon execution — `not examined`:** Runtime SVE-128/256/512 execution (`17` / `42` / `-11 SIGSEGV`) was observed under `qemu-aarch64 11.1.2 (Debian 1:11.1.2+ds-2)` on `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` (`support/recorded_1_102_qemu_sve_results.json`), corroborated by live static ELF linking and `llvm-objdump` disassembly on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`support/live_probe_1_98_results.json`). No physical Neoverse V1, Graviton3, A64FX, or RVV 1.0 silicon was executed. The host running the `1.98.0-nightly` probe did not have `qemu-aarch64` installed (`"qemu_aarch64_available": false`); `support/probe_scalable_vectors_sve_stack_smash_and_riscv_ice.py` automatically links and executes the static AArch64 ELF under `qemu-aarch64` when present.
- **ARMv9 SME streaming-mode (`ZA`) and Cranelift/GCC codegen backends — `not examined`:** All codegen audits target `rustc_codegen_llvm`. Behavior of `rustc_codegen_cranelift` or `rustc_codegen_gcc` on `BackendRepr::SimdScalableVector`, `autodiff`, or `offload` was not examined.
- **Runtime execution with a locally built `libEnzyme-23.so` or CUDA/AMDGPU offload toolchain — `unsupported` on stock rustup nightlies / `not examined`:** Because stock rustup toolchains do not distribute `libEnzyme-22`/`libEnzyme-23.so` or an LLVM GPU offload backend, this report establishes the exact frontend/codegen gating conditions and failure diagnostics, not differentiated numerical accuracy or GPU kernel execution semantics.
- **Stable Rust without `#![feature(rustc_attrs)]` — `known not to apply` directly to user-defined scalable types:** Defining a `#[rustc_scalable_vector]` type requires nightly `#![feature(rustc_attrs)]`. However, if `core::arch` exposes a scalable vector type on stable or nightly Rust while `SimdScalableVector` still satisfies `Sized`, downstream safe generic code (`GenericPair<T>`, `[T; 2]`, `(T, u64)`, `Box::new`) triggers the overflow without `#![feature(rustc_attrs)]` or `unsafe`.
- **Scope of the Lean `v4.34.1` model — `derived` over an abstract type/layout calculus:** `support/ScalableVectorLayoutAndSizedHierarchySoundness.lean` models 2-field structs, 2-tuples, fixed-length arrays, scalars, scalable vectors, generic parameters, and `#[repr(transparent)]` wrappers, and does not model Rust enum niche discriminants, `#[repr(packed)]`, `async`/coroutine generator layouts, or LLVM register spilling across calls. Its soundness theorems prove the structural layout/disjointness invariants of the `ConstSized`/`RuntimeSized` split within this calculus; extending them to full `rustc` MIR/LLVM codegen additionally requires verifying ABI parameter passing, stack coloring, and callee-saved SVE register spilling (`z8`–`z15`, `p4`–`p15`).
- **Exact commit introducing `CFG_DEFAULT_NEXT_SOLVER_GLOBALLY=1` and fixing `2..8` -> `2..=8` — `unknown`:** Source diffs establish that both changes landed between `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`2026-05-31`) and `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`2026-11-11`), without bisecting the exact intermediate PR commits.

## Evidence

### Primary Source Citations

1. **`rust-lang/rust` HEAD (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`, `2026-11-22`), with cross-revision anchors at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`) and `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`):**
   - `compiler/rustc_abi/src/lib.rs`: `NumScalableVectors::from_field_count` (`L1814-1818` HEAD, `L1804-1808` `1.102`, `L1755-1759` `1.98` with `2..8`), `BackendRepr::SimdScalableVector` (`L1867-1871` HEAD, `L1857-1861` `1.102`, `L1796-1800` `1.98`), `BackendRepr::is_unsized` (`L1886-1899` HEAD, `L1876-1889` `1.102`, `L1815-1828` `1.98`).
   - `compiler/rustc_abi/src/layout.rs`: `layout_of_scalable_vector_type` (`L207-224` HEAD), `vector_type_layout` (`L979-1035` HEAD).
   - `compiler/rustc_ty_utils/src/layout.rs`: scalable vector layout dispatch and `delayed_bug` (`L622-644` HEAD & `1.102`, `L581-603` `1.98`).
   - `compiler/rustc_middle/src/ty/sty.rs`: `Ty::is_scalable_vector` (`L1259-1264` HEAD), `Ty::scalable_vector_parts` (`L1274-1298` HEAD).
   - `compiler/rustc_middle/src/ty/adt.rs`: `AdtDef::can_project_fields` (`L222-226` HEAD).
   - `compiler/rustc_ast_passes/src/ast_validation.rs` (`L1650-1665` HEAD) & `compiler/rustc_ast_passes/src/diagnostics.rs` (`L1197-1209` HEAD): tuple-struct check and `Arch::supports_scalable_vectors()` gate.
   - `compiler/rustc_target/src/spec/mod.rs`: `Arch::supports_scalable_vectors` (`L1834-1845` HEAD: `AArch64 | RiscV32 | RiscV64`).
   - `compiler/rustc_hir_analysis/src/check/check.rs`: `check_scalable_vector` (`L1564-1666` HEAD).
   - `compiler/rustc_hir_analysis/src/check/wfcheck.rs`: concrete ADT field check (`L1030-1052` HEAD, `L1040-1053` `1.102`, `L1087-1100` `1.98`).
   - `compiler/rustc_trait_selection/src/traits/wf.rs`: `wf::obligations` & `wf::unnormalized_obligations` (`L31-123` HEAD), `ty::Slice`/`ty::Array` (`L808-827` HEAD), `ty::Tuple` `!self.span.is_dummy()` guard (`L834-856` HEAD, `L833-855` `1.102`, `L777-799` `1.98`).
   - `compiler/rustc_trait_selection/src/solve/delegate.rs`: `SolverDelegate::well_formed_goals` passing `DUMMY_SP` (`L372-385` HEAD & `1.102`, `L233-246` `1.98`).
   - `compiler/rustc_next_trait_solver/src/solve/trait_goals.rs` (`L288-306` HEAD) & `compiler/rustc_next_trait_solver/src/solve/assembly/structural_traits.rs` (`L117-196` HEAD): built-in `Sized`/`MetaSized` solving via `sizedness_constraint`.
   - `compiler/rustc_session/src/config.rs` (`L1078-1086` HEAD & `1.102`) & `src/bootstrap/src/core/build_steps/compile.rs` (`L1375-1381` HEAD, `L1373-1377` `1.102`; absent in `1.98`): `CFG_DEFAULT_NEXT_SOLVER_GLOBALLY=1` nightly default.
   - `compiler/rustc_codegen_ssa/src/mir/place.rs`: `PlaceRef::alloca` transparent-wrapper peeling (`L111-131` HEAD).
   - `compiler/rustc_codegen_llvm/src/builder.rs`: `Builder::alloca` & `Builder::alloca_with_ty` (`L681-697` HEAD, `L682-698` `1.102`, `L606-627` `1.98`).
   - `compiler/rustc_codegen_llvm/src/type_of.rs`: `SimdScalableVector` LLVM type lowering for `1..=8` (`L26-45` HEAD & `1.102`).
   - `compiler/rustc_codegen_llvm/src/debuginfo/metadata.rs`: `build_scalable_vector_di_node`, `assert_matches!(cx.tcx.sess.target.arch, Arch::AArch64)`, and `number_of_elements / 2` (`L1120-1132,1200-1275` HEAD; `L1119-1131,1199-1274` `1.102` with assertion at `L1213`; `L1064-1076,1144-1219` `1.98` with assertion at `L1158`).
   - `library/core/src/intrinsics/mod.rs`: `pub const fn autodiff` (`L3221-3223` HEAD) and `pub const fn offload` (`L3261-3270` HEAD).
   - `compiler/rustc_builtin_macros/src/autodiff.rs`: `expand_with_mode` (`L175-225` HEAD).
   - `compiler/rustc_codegen_llvm/src/intrinsic.rs`: `sym::autodiff`, `sym::offload`, `codegen_autodiff`, `codegen_offload` (`L126-141,1771-1939` HEAD).
   - `compiler/rustc_codegen_llvm/src/diagnostics.rs`: `AutoDiffComponentMissing`, `AutoDiffWithoutEnable`, `AutoDiffWithoutLto`, `OffloadWithoutEnable`, `OffloadWithoutFatLTO` (`L40-100` HEAD).
   - `compiler/rustc_codegen_llvm/src/back/write.rs` (`L538-575,749-763` HEAD) & `compiler/rustc_codegen_llvm/src/llvm/enzyme_ffi.rs` (`L450-479` HEAD): three-pass AD optimization, `offload-kernel` rewriting, and `libEnzyme-<LLVM_MAJOR>.<DLL_EXT>` sysroot search.

2. **The Rust Reference (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `2026-11-17`):**
   - `src/special-types-and-traits.md` (`L186-198`, `r[lang-types.sized.intro]`–`r[lang-types.sized.relaxation]`).
   - `src/dynamically-sized-types.md` (`L1-31`, `r[dynamic-sized.intro]`–`r[dynamic-sized.tail]`).

3. **Anneal (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `2026-11-19`):**
   - `trusted/lean/Trusted/MirAst.lean` (`L310-322`, `MirTy` fail-closed `.unsupported` catch-all).
   - `trusted/lean/Trusted/MirSemantics.lean` (`L51,103,328-334`, `FaultKind.unsupported`).
   - `trusted/rustc-capture/src/driver.rs` (`L25-48`, pinned compiler-version check).

### Preserved Support Artifacts (`support/`)

- **`support/probe_scalable_vectors_sve_stack_smash_and_riscv_ice.py`**: Standalone Python 3 revalidation harness executing 28 live `rustc` checks (direct ADT/arch rejections, `-Znext-solver=no` vs. `-Znext-solver=globally` solver matrix, direct/generic arrays, generic struct/enum/union/tuple/closure bypasses, CTFE `size_of`/`offset_of`/`Layout::new`, multi-vector `x1`/`x2`/`x7`/`x8`/`x9`, AArch64 DWARF `debuginfo=2` and `element_count=1` wrap, RISC-V 64/32 RVV `-C debuginfo=2` ICEs, `autodiff`/`offload` gates), plus compiling and statically linking the `#![no_std]` AArch64 SVE stack-smash ELF binary with bundled `ld.lld`, disassembling via bundled `llvm-objdump`, and running SVE-128/256/512 execution under `qemu-aarch64` when installed.
- **`support/live_probe_1_98_results.json`**: Complete scrubbed JSON output captured live on `2026-11-22` with `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`), including exact LLVM IR excerpts and the 28-line `llvm-objdump` AArch64 SVE disassembly (`str z0, [x0]` into 48-byte frame).
- **`support/recorded_1_102_qemu_sve_results.json`**: Scrubbed JSON record from `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM `23.1.5`) and `qemu-aarch64 11.1.2 (Debian 1:11.1.2+ds-2)` recording live SVE-128 (`exit 17`), SVE-256 (`exit 42`), SVE-512 (`exit -11`, `SIGSEGV`), default `-Znext-solver=globally` `DUMMY_SP` tuple bypass (`rc = 0`), RISC-V 64 `-C debuginfo=2` ICE at `metadata.rs:1213:5` (`rc = 101`), `libEnzyme-23.so` missing diagnostic, and 6-argument `offload` gate errors.
- **`support/ScalableVectorLayoutAndSizedHierarchySoundness.lean`**: Standalone, zero-import `Lean v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) kernel-checked formalization (874 lines, 219 local constants, 34 theorems, `0` errors/warnings under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, `0` `._unsafe_rec` constants in `env.constants.map₂`, `#print axioms` restricted to `[propext]` or `[]`).

## Revalidation

1. **Rerun the complete empirical `rustc` + AArch64 SVE ELF + optional `qemu-aarch64` probe:**
   ```bash
   python3 support/probe_scalable_vectors_sve_stack_smash_and_riscv_ice.py --out /tmp/sve_reval.json
   ```
   Check the following discriminating fields in `/tmp/sve_reval.json`:
   - **Generic struct & array WF bypasses fixed?** `generic_struct_old_solver_bypass.rc`, `generic_struct_next_solver_bypass.rc`, `direct_array_old_solver_no_bypass.rc`, and `generic_array_bypass.rc` flip from `0` to `1` once `#[rustc_scalable_vector]` is removed from `const Sized` / `Sized`.
   - **`DUMMY_SP` next-solver tuple regression fixed?** `direct_tuple_next_solver_globally_dummysp_bypass.rc`, `generic_tuple_next_solver_globally_bypass.rc`, and `closure_capture_next_solver_globally_bypass.rc` flip from `0` to `1` once `wf.rs:838,849` drops `!self.span.is_dummy()` (or rejects via an unsatisfiable trait bound).
   - **Live SVE-128/256/512 execution (on any host with `qemu-aarch64`):** `aarch64_sve_elf_and_qemu.qemu_runs` directly checks whether `sve_128_vscale_1.exit_code == 17`, `sve_256_vscale_2.exit_code == 42` (corruption), and `sve_512_vscale_4.exit_code == -11` (`SIGSEGV`).
   - **RISC-V RVV debuginfo ICE fixed?** `riscv64_rvv_debuginfo2_live_ice.rc` and `riscv32_rvv_debuginfo2_live_ice.rc` flip from `101` (`is_ice: true`) to `0` once `build_scalable_vector_di_node` supports RISC-V DWARF `vlenb` expressions instead of asserting `Arch::AArch64`.
   - **`SvU32x1` ICE & `element_count = 1` DWARF wrap fixed?** `multi_vector_x1.rc` flips from `101` to `1` (or `0`), and `aarch64_sve_debuginfo2_count1_div2_zero` no longer emits `DW_OP_constu, 0, DW_OP_bregx, 46`.
   - **`autodiff` / `offload` distribution changes:** `autodiff_with_z_enable_missing_enzyme` flips once `libEnzyme-<LLVM_MAJOR>.so` ships in rustup sysroots.

2. **Re-verify the Lean `v4.34.1` kernel formalization and zero-`._unsafe_rec` / clean-axiom invariant:**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/ScalableVectorLayoutAndSizedHierarchySoundness.lean
   ```
   A clean exit (`rc = 0`, zero diagnostics) re-confirms all 34 theorems under Lean's full kernel typechecker without asynchronous elaboration bypasses.

3. **Targeted upstream source diffs (`rust-lang/rust`):**
   Revalidation against a newer `rust-lang/rust` commit only requires inspecting diffs in six narrow regions:
   - `compiler/rustc_abi/src/lib.rs` (`BackendRepr::is_unsized`, `NumScalableVectors::from_field_count`),
   - `compiler/rustc_hir_analysis/src/check/wfcheck.rs` (`def.repr().scalable()`),
   - `compiler/rustc_trait_selection/src/traits/wf.rs` (`ty::Array`, `ty::Tuple` `is_scalable_vector()`),
   - `compiler/rustc_trait_selection/src/solve/delegate.rs` (`well_formed_goals`),
   - `compiler/rustc_codegen_ssa/src/mir/place.rs` (`PlaceRef::alloca`), and
   - `compiler/rustc_codegen_llvm/src/debuginfo/metadata.rs` (`build_scalable_vector_di_node`).
