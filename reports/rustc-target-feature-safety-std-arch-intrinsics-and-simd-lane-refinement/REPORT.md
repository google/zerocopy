# Target-Feature Safety (`#[target_feature]`), `core::arch` Intrinsics, and Portable SIMD Lane/Mask Lowering Refinement

## Summary

In `rustc` (Rust 1.86+ / RFC 2396), safe `#[target_feature(enable = "...")]` functions, `core::arch` vendor SIMD intrinsics, and `core::intrinsics::simd` operations jointly guarantee the absence of hardware illegal-instruction faults (`#UD` / `SIGILL`) and out-of-bounds lane/memory undefined behavior through a three-layer contract spanning HIR/THIR unsafety checking, MIR and LLVM cross-feature inlining gates, and monomorphization-checked SIMD intrinsic lowering:

1. **Dual-view function safety & capability-witness `fn()` pointers**: Lowering rewrites a non-`unsafe` `#[target_feature]` function header (on non-Wasm targets) to `hir::HeaderSafety::SafeTargetFeatures`, which projects to `Safety::Unsafe` in `ty::FnSig` for baseline callers while keeping the function body in `SafetyContext::Safe` (`CodegenFnAttrs.safe_target_features = true`). Direct calls omit `unsafe` if and only if the caller's per-function `body_target_features` (closed under architectural implication, **ignoring** global `-C target-feature` / `-C target-cpu` CLI flags) is a superset of the callee's features (`tcx.is_target_feature_call_safe`). Coercing a `SafeTargetFeatures` function item to a safe `fn()` pointer is rejected in baseline code (`E0308`, `TypeError::TargetFeatureCast`), **yet permitted inside a caller whose `body_target_features` covers the callee** (`tcx.adjust_target_feature_sig`), because runtime reachability of that caller dynamically witnesses that the process's immutable CPU feature set supports the callee for the remainder of program execution.
2. **Asymmetric MIR vs. LLVM cross-feature inlining & hoisting barriers**: The MIR inliner (`rustc_mir_transform/src/inline.rs`) requires **strict feature-set equality** (`callee == caller`), inlining equal-feature `core::arch` wrappers (such as `_mm256_add_epi32` into an `avx2` caller) into raw `simd_*` intrinsics while preserving `Call` terminators to strict-subset helpers (`avx`, `sse4.1`, `sse2`) so vector pass-by-value call ABIs cannot shift silently at MIR level. LLVM then enforces **feature-set inclusion** (`callee ⊆ caller` via `TTI.areInlineCompatible` over emitted `"target-features"` attributes), inlining subset helpers into the specialized kernel while blocking inlining of `avx2`/`avx512f` kernels across runtime `is_x86_feature_detected!` guards into baseline `sse2` callers—preventing Loop-Invariant Code Motion (LICM) or GVN from hoisting VEX/EVEX instructions above a `false` CPUID check (`SIGILL`). To close LLVM `<= 22`'s `AlwaysInliner` bypass of `TTI.areInlineCompatible`, `rustc` `1.98.0-nightly` and `1.99.1` reject `#[inline(always)]` with `#[target_feature]`, whereas `rustc` `1.102.0-nightly` (LLVM `>= 23`) accepts the combination and downgrades `InlineAttr::Always` to `InlineHint` only when compiled against LLVM `< 23`.
3. **Portable SIMD (`core::intrinsics::simd`) & `core::arch` immediate invariants**: `#[rustc_legacy_const_generics]` splices positional integer literals into `AnonConst` generic arguments validated post-monomorphization (`static_assert_uimm_bits!`, `E0080`), while `#[repr(simd)]` bans direct `.0` MIR field projections (MCP#838) and pads non-power-of-two lane counts to the next power-of-two vector size/alignment (`[i16; 10]` = `20` bytes vs. `Simd<i16, 10>` = `32` bytes). `rustc_codegen_llvm` lowers vector masks via MSB right-shift (`lshr (elem_bits - 1)` + `trunc` to `<N x i1>`), packs `simd_bitmask` LSB-first on little-endian and MSB-first on big-endian (zero-extended to `max(8, next_pow2(N))` or `[u8; ceil(N/8)]`), checks `simd_shuffle` indices `< 2 * N` (`E0511`), and lowers `simd_masked_load`/`store` on LLVM `>= 22` to 3-argument `@llvm.masked.load`/`store` intrinsics with `align(A)` pointer parameter attributes that never dereference disabled lanes.

At `joshlf/anneal` revision `c131b320eeeb26ef692e5afd5ec8db49ee518613`, Anneal fails closed on SIMD types (`MirTy.unsupported`), `StatementKind::Intrinsic`, and `TerminatorKind::Call`, while `Body` (`Trusted/MirAst.lean:862-867`) tracks only `isUnsafe : Bool`. Supporting safe `#[target_feature]` and `core::arch` in Anneal requires extending `Body` with `reqFeatures : FeatureSet` (and execution state with `cpuFeatures : FeatureSet`) alongside `simd_*` semantics. All claims are backed by a reproducible compiler/IR/disassembly/silicon probe (`support/probe_target_feature_and_simd.py` -> `support/probe_results.json`) and a standalone kernel-checked `Lean v4.34.1` mechanization (`support/TargetFeatureAndSimdRefinement.lean`, `0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`).

## Applicability

These findings govern the boundary between `rustc` type/unsafety checking, `core::arch` (`stdarch`), MIR optimization, LLVM target-feature and SIMD intrinsic lowering, and Lean 4 MIR verification across the six durable subjects in `REPORT.json`:

1. **Primary compiler & sysroot reference (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`, `1.99.1`)**: Defines the normative source implementation audited for `HeaderSafety::SafeTargetFeatures`, `check_unsafety`, `coercion`, `candidate_assembly`, `X86_FEATURES` / `AARCH64_FEATURES`, MIR inlining, and `rustc_codegen_llvm` SIMD intrinsic lowering.
2. **Executed host toolchain (`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly (2026-05-31)`, LLVM `22.1.6`)**: Produces all compiled MIR, unoptimized and `-O2`/`-O3` LLVM IR, AT&T x86-64 disassembly, cross-target `aarch64-unknown-linux-gnu` LLVM attributes, `core::arch` sysroot census counts, and native Broadwell Xeon (`avx2 = true`, `avx512f = false`) execution and `SIGILL` counterfactuals in `support/probe_results.json`.
3. **LLVM 23 transition toolchain (`rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `rustc 1.102.0-nightly`)**: Captures the removal of the hard compile error on `#[inline(always)]` + `#[target_feature]` once LLVM 23's `AlwaysInliner` respects `TTI.areInlineCompatible`.
4. **Standalone `stdarch` upstream (`rust-lang/stdarch` @ `ca26a96d57b295dcd927622877242940a0f3c02e`)**: Corroborates `crates/core_arch/src/macros.rs` (`simd_ty!`, `static_assert_uimm_bits!`, MCP#838 pointer-cast array projection) mirrored under `library/stdarch` in `rust-lang/rust`.
5. **Verification consumer & theorem prover (`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` `v4.34.1`)**: Establishes Anneal's current `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, and `vendor/lean-miri` target-feature/SIMD seams and kernel-checks `support/TargetFeatureAndSimdRefinement.lean`.

### Version-Specific Divergences Explicitly Distinguished

- **`#[inline(always)]` + `#[target_feature]`**: Hard compile error (`cannot use #[inline(always)] with #[target_feature]`) in `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`) and `58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`), versus accepted (`compile_rc = 0`, emitting `alwaysinline` on LLVM `>= 23` and `inlinehint` on LLVM `< 23`) in `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`).
- **AArch64 `sve` -> `fp16` implication**: In `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`target_features.rs:355`), `sve` implies `&["neon"]` only (calling an `fp16` safe function from an `sve` function fails with `E0133`), whereas in `58cf8f9c35b355199727627d07ae34a4e2846d67` (`target_features.rs:374`), `sve` implies `&["neon", "fp16"]`.
- **LLVM `@llvm.masked.load` / `@llvm.masked.store` signature**: On LLVM `>= 22` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `58cf8f9c35b355199727627d07ae34a4e2846d67`), `rustc_codegen_llvm` emits the 3-argument overload carrying `align A` as a parameter attribute on the pointer operand (`ptr align 1 %src`), whereas LLVM `< 22` passes alignment as a 4th `i32` immediate argument.

## Findings

### Architectural Summary (`L1`–`L6`)

| Layer | Subsystem | Core Invariant / Lowering Rule | Evidentiary Basis |
| :--- | :--- | :--- | :--- |
| `L1` | HIR/THIR Safe `#[target_feature]` (RFC 2396) | `HeaderSafety::SafeTargetFeatures` presents `Safety::Unsafe` externally (`ty::FnSig`) and `SafetyContext::Safe` internally; safe call/coercion iff `callee_features ⊆ caller_body_features`; `Fn*` traits & safe trait impls unconditionally excluded | normative + source + execution + derived |
| `L2` | `x86_64` & `aarch64` Feature Lattices | Transitive closure `implied_target_features` + contrapositive `-feature` disablement; C-ABI fixed vector width gates (`128: sse`, `256: avx`, `512: avx512f`); `sve -> fp16` version split | source + execution |
| `L3` | MIR & LLVM Cross-Feature Inlining + Hoisting | MIR inlines iff `callee_features == caller_features`; LLVM inlines iff `callee_features ⊆ caller_features` (`TTI.areInlineCompatible`); prevents VEX/EVEX LICM hoisting across `is_x86_feature_detected!` (`CE1` `SIGILL`) | source + execution + derived |
| `L4` | `core::arch` Immediates & `#[repr(simd)]` Layout | `#[rustc_legacy_const_generics]` rewrites positional args to `AnonConst` (`E0435` if non-const, `E0080` on OOB `static_assert_uimm_bits!`); MCP#838 bans `.0` field projection; `Simd<T, N>` pads non-pow2 `N` to `next_pow2(N)` | source + execution |
| `L5` | `core::intrinsics::simd` (`75` intrinsics) | MSB `lshr (W-1)` mask extraction; endian-aware `simd_bitmask` (`pmovmskb`); `simd_shuffle` `< 2*N` check (`E0511`); `simd_cast` vs. saturating `simd_as`; 3-arg `@llvm.masked.load`/`store` tail safety | source + execution + derived |
| `L6` | Lean 4 Refinement & Anneal Integration | Kernel-checked No-`SIGILL` type/inline/hoist soundness, `CE1`/`CE2` sharpness, and SIMD lane/mask/memory theorems; `Trusted.MirAst.Body` `reqFeatures` design requirement | source + execution + derived |

Basis: source + execution + derived

### `L1`: Safe `#[target_feature]` Type System, Unsafety Checking, and Capability-Witness `FnPtr` Coercion

In `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), safe `#[target_feature]` (stabilized in Rust 1.86, RFC 2396) is not implemented by adding target-feature sets to `ty::FnSig` or `fn()` pointer types. Instead, `rustc` splits a function's external signature safety from its internal body safety:

1. **AST -> HIR Safety Rewrite (`compiler/rustc_ast_lowering/src/item.rs:1694-1702`, `compiler/rustc_hir/src/hir.rs:4430-4465`)**:
   When lowering a function written without `unsafe` that carries at least one non-forced `#[target_feature(enable = "...")]` on a non-Wasm target (`!tcx.sess.target.is_like_wasm`), `lower_fn_header` rewrites `FnHeader.safety` to `hir::HeaderSafety::SafeTargetFeatures`. Calling `HeaderSafety::safety()` returns **`hir::Safety::Unsafe`**, so `ty::FnSig` records the function item as `unsafe fn(...)` throughout HIR type checking, while `codegen_fn_attrs` sets `CodegenFnAttrs.safe_target_features = true` (`compiler/rustc_codegen_ssa/src/codegen_attrs.rs:109-111`, `compiler/rustc_middle/src/middle/codegen_fn_attrs.rs:98`).
2. **THIR Unsafety Checking vs. HIR Call Typeck (`compiler/rustc_hir_typeck/src/callee.rs:557-625`, `compiler/rustc_mir_build/src/check_unsafety.rs:412-464, 803-824, 1072-1084`)**:
   Note that upstream `rust-lang/rust` relocated THIR unsafety checking from the older `compiler/rustc_mir_build/src/thir/unsafety.rs` path to `compiler/rustc_mir_build/src/check_unsafety.rs`. `confirm_builtin_call` (`callee.rs:557-625`) validates argument types and ABI compatibility without enforcing `unsafe` blocks. Inside `check_unsafety`:
   - Entering a `HeaderSafety::SafeTargetFeatures` body initializes `SafetyContext::Safe` (`check_unsafety.rs:1077`), so raw pointer dereferences, mutable static accesses, and calls to ordinary `unsafe fn` items inside the body still require explicit `unsafe {}` blocks.
   - At a direct call `ExprKind::Call` (`check_unsafety.rs:412-458`), if the callee is `ty::FnDef(def_id, _)` with `safe_target_features == true`, `rustc` skips requiring an `unsafe` block when `tcx.is_target_feature_call_safe(&callee_attrs.target_features, &self.body_target_features)` returns `true` (`compiler/rustc_middle/src/ty/context.rs:1226-1239`):
     ```rust
     self.sess.target.is_like_wasm
         || callee_features.iter().all(|feature| {
             body_features.iter().any(|body_feature| body_feature.name == feature.name)
         })
     ```
   - **Global CLI `-C target-feature` Exclusion (`s03`)**: `self.body_target_features` contains *only* the transitive closure of `#[target_feature]` attributes on the enclosing function (inherited by closures unless marked `#[inline(always)]`, `codegen_attrs.rs:356`), deliberately excluding `sess.unstable_target_features` / `-C target-feature=+avx2` / `-C target-cpu=native`. Consequently, an unannotated function calling a safe `#[target_feature(enable = "avx2")]` function fails with `E0133` even when compiled with `-C target-feature=+avx2` (`check_unsafety.rs:446-456`).
3. **Function-Pointer Coercion & Capability-Witness Reification (`compiler/rustc_hir_typeck/src/coercion.rs:1237-1278`, `compiler/rustc_borrowck/src/type_check/mod.rs:1048-1060`, `context.rs:1243-1258`)**:
   - Coercing a `SafeTargetFeatures` `FnDef` to `unsafe fn(...)` succeeds unconditionally (`s05`), because `sig.safety()` is already `Safety::Unsafe` (`coercion.rs:1267`).
   - Coercing to a safe `fn(...)` pointer calls `tcx.adjust_target_feature_sig(def_id, fn_sig, self.body_def_id.into())`. In baseline code (`s04`), `is_target_feature_call_safe` returns `false`, emitting `E0308` (`TypeError::TargetFeatureCast`).
   - **Capability-witness reification (`s06`)**: Inside `#[target_feature(enable = "avx2")] pub fn avx2_witness_exporter() -> fn(u32) -> u32 { avx2_callee }`, `caller_features` includes `avx2`, so `adjust_target_feature_sig` rewrites the signature safety to `Safety::Safe` (mirrored identically in MIR borrowck `type_check/mod.rs:1048-1060`)! Baseline code that guarded its call to `avx2_witness_exporter()` behind `is_x86_feature_detected!("avx2")` receives an ordinary `fn(u32) -> u32` value and invokes it safely with zero further CPUID checks or `unsafe` blocks (`s06_ok=41`). As proven in Section `L6` (`eval_typed_no_sigill`), this rule is sound **if and only if** `cpuFeatures` is a **process-global, monotone (immutable) hardware capability**; entering `avx2_witness_exporter` proves `avx2 ∈ cpuFeatures` for the entire remaining execution trace.
4. **Unconditional `Fn*` Trait Exclusion & Safe Trait Method Ban (`s07`, `s08`)**:
   - `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs:528-536, 589-597` synthesizes built-in `Fn`/`FnMut`/`FnOnce`/`AsyncFn*` implementations for `ty::FnDef` *only* when `tcx.codegen_fn_attrs(def_id).target_features.is_empty()`. Because trait impls in Rust cannot be parameterized by caller `body_target_features`, passing `avx2_callee` directly to `fn apply_fn<F: Fn(u32) -> u32>(f: F, ...)` fails with `E0277` **even inside an `avx2` caller** (`s07`); the caller must either coerce `avx2_callee as fn(u32) -> u32` (triggering `adjust_target_feature_sig`) or wrap it in a closure `|x| avx2_callee(x)` (which inherits `avx2` from the enclosing body).
   - `compiler/rustc_codegen_ssa/src/target_features.rs:165-175` (`check_target_feature_trait_unsafe`) rejects `#[target_feature]` on any implementation of a safe trait method (`s08`), preventing vtable or generic dispatch from entering a target-feature body from baseline code.

| Probe Specimen (`support/probe_results.json`) | Construct Tested | Compile / Run RC | Observed `rustc` Diagnostic or Runtime Result |
| :--- | :--- | :---: | :--- |
| `s01_avx2_calls_avx2_and_sse41_and_blend_safe` | `avx2` fn calling `avx2`, implied `sse4.1`, and `_mm256_blend_epi32` without `unsafe` | `0` / `0` | `s01_ok=107` |
| `s02_avx2_calls_avx512f_without_unsafe` | `avx2` fn calling safe `avx512f` fn without `unsafe` | `1` / — | `E0133`: `call to function avx512_callee with #[target_feature] is unsafe...` |
| `s03_baseline_calls_avx2_even_with_cli_target_feature` | Unannotated fn calling `avx2` fn under `-C target-feature=+avx2` | `1` / — | `E0133` + note: `build configuration does not remove the requirement to list it in #[target_feature]` |
| `s04_baseline_coerces_avx2_to_safe_fnptr` | Baseline fn coercing `avx2` fn to `fn(u32) -> u32` | `1` / — | `E0308`: `functions with #[target_feature] can only be coerced to unsafe function pointers` |
| `s05_baseline_coerces_avx2_to_unsafe_fnptr` | Baseline fn coercing `avx2` fn to `unsafe fn(u32) -> u32` | `0` / — | Accepted (`FnSig` safety is `Unsafe`) |
| `s06_avx2_reifies_avx2_to_safe_fnptr_witness` | `avx2` fn coercing `avx2` fn to `fn(u32) -> u32` and returning to baseline | `0` / `0` | `s06_ok=41` (`adjust_target_feature_sig` witness) |
| `s07_avx2_fndef_implements_fn_trait_inside_avx2` | Passing `avx2` `FnDef` to `F: Fn(u32) -> u32` inside `avx2` caller | `1` / — | `E0277`: `#[target_feature] functions do not implement the Fn traits` |
| `s08_target_feature_on_safe_trait_impl_method` | `#[target_feature(enable = "avx2")]` on `impl Compute for AvxImpl` | `1` / — | `#[target_feature(..)] cannot be applied to safe trait method` |

Basis: normative + source + execution + derived

### `L2`: `x86_64` and `aarch64` Target-Feature Implication Lattices and ABI Gates

`compiler/rustc_target/src/target_features.rs:1235-1253` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) computes forward transitive closure in `implied_target_features` via a fixed-point worklist, while `parse_rust_feature_list` (`compiler/rustc_codegen_ssa/src/target_features.rs:226-253`) computes the inverse map to enforce contrapositive disablement on `-feature` CLI flags (disabling `-sse2` transitively disables `avx`, `avx2`, `avx512f`, etc.; `#[target_feature]` attributes themselves only permit `enable = "..."`).

- **`x86` / `x86_64` Lattice (`X86_FEATURES`, `target_features.rs:425-559`)**:
  - Core SIMD chain: `avx512bw -> avx512f`, `avx512vl -> avx512f`, `avx512dq -> avx512f`, `avx512cd -> avx512f`; `avx512f -> {avx2, fma, f16c}`; `vaes -> {avx2, aes}`; `vpclmulqdq -> {avx, pclmulqdq}`; `avx2 -> avx`; `fma -> avx`; `f16c -> avx`; `avx -> sse4.2 -> sse4.1 -> ssse3 -> sse3 -> sse2 -> sse`.
  - Fixed-length C-ABI vector register gates (`X86_FEATURES_FOR_CORRECT_FIXED_LENGTH_VECTOR_ABI`, `target_features.rs:1104-1105`): `128`-bit vectors require `"sse"`, `256`-bit vectors require `"avx"`, and `512`-bit vectors require `"avx512f"`. On `x86_64` (`lines 1298-1308`), baseline ABI feature requirements enforce required `["x87", "sse2"]` and reject ABI-incompatible `["soft-float"]`.
  - LLVM translation (`compiler/rustc_llvm/src/llvm_util.rs:239-336`): Rust `"sse4.2"` expands to LLVM `["sse4.2", "crc32"]`, and `"pclmulqdq"` maps to LLVM `"pclmul"`—visible directly in `probe_results.json` where `#[target_feature(enable = "avx2")]` emits `"target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3"`.
- **`aarch64` Lattice (`AARCH64_FEATURES`, `target_features.rs:216-423`, `llvm_util.rs:254-257`, Probe `s12`)**:
  - Core SIMD chain (`1.99.1`, `58cf8f9c35b355199727627d07ae34a4e2846d67`): `sve2 -> sve` (`line 389`), `sve -> {neon, fp16}` (`line 374`), `fp16 -> neon` (`line 277`), tied PAC pair `["paca", "pacg"]` (`line 421`), and LLVM tied feature `"neon"` -> `["neon", "fp-armv8"]` (`llvm_util.rs:254-257`, `"fp16"` -> LLVM `"fullfp16"`).
  - **Cross-version `sve -> fp16` drift (`s12`)**: On `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `target_features.rs:355`), `sve` listed `&["neon"]` without `"fp16"`. Cross-compiling `s12` (`--target=aarch64-unknown-linux-gnu`) confirms `sve2 -> sve -> neon` and `fp16 -> neon` succeed (`compile_rc = 0`, emitting `"+v8a,+outline-atomics,+neon,+fp-armv8,+sve,+sve2"`), `sve` calling `sve2` fails (`E0133`), and `sve` calling `fp16` fails with `E0133` on `1.98.0-nightly` before becoming safe in `1.99.1`.

Basis: source + execution

### `L3`: Three-Tier Cross-Feature Inlining & Instruction-Hoisting Barrier (`CE1` & `CE2`)

Dynamic SIMD dispatch (`if is_x86_feature_detected!("avx2") { unsafe { avx2_kernel(...) } }`) would be catastrophically unsound if an optimizer inlined `avx2_kernel` into its baseline `sse2` caller: once `vmovdqu (%rdi), %ymm0` or `vpxord (%rdi), %zmm0, %zmm0` resides inside the caller's basic blocks, standard intra-function passes (LLVM LICM, GVN, SimplifyCFG speculative `select` conversion, or MachineLICM) treat all pure instructions in that function as legal for the caller's target CPU and hoist them above the runtime CPUID branch. `rustc` and LLVM prevent this through three distinct tiers:

1. **Tier 1 — MIR Inliner Strict Feature-Set Equality (`compiler/rustc_mir_transform/src/inline.rs:841-850`)**:
   ```rust
   let callee_feature_names = callee_attrs.target_features.iter().map(|f| f.name);
   let this_feature_names = this_attrs.target_features.iter().map(|f| f.name);
   if callee_feature_names.ne(this_feature_names) {
       return Err("incompatible target features");
   }
   ```
   Crucially, the MIR inliner checks **equality (`==`), not inclusion (`⊆`)**. Even if an `avx2` function calls an `#[inline]` `avx` or `sse4.1` function, MIR inlining refuses to inline it because splicing a `Call` terminator from an `sse4.1` body into an `avx2` body can alter how pass-by-value vector arguments are lowered under target-dependent call ABIs (`inline.rs:841-843`). Our `-O2`/`-O3` MIR dump (`probe_results.json`, `mir_inliner_observations`) confirms this sharp split inside `avx2_kernel_entry` (`#[target_feature(enable = "avx2")]`):
   - `_mm256_add_epi32` and `_mm256_extracti128_si256::<1>` (both annotated `#[target_feature(enable = "avx2")]`) **are MIR-inlined**, exposing `simd_add` and `simd_shuffle` plus `CastKind::Transmute` directly in `avx2_kernel_entry`'s optimized MIR;
   - `_mm256_castsi256_si128` (`avx`), `_mm_add_epi32` (`sse2`), and `sse41_helper` (`sse4.1`) (all strict subsets of `avx2`) **remain un-inlined MIR `Call` terminators**, deferred to LLVM.
2. **Tier 2 — `#[inline(always)]` Suppression / LLVM 23 Versioning (`s09`)**:
   In LLVM `<= 22`, `AlwaysInlinerPass` inlined `alwaysinline` callees unconditionally without consulting `TargetTransformInfo::areInlineCompatible`. Consequently, `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `codegen_attrs.rs:420-432`) and `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, `codegen_attrs.rs:448-460`) emit a hard error (`cannot use #[inline(always)] with #[target_feature]`, `s09`), while ordinary `#[inline]` emits LLVM `inlinehint`. In `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `compiler/rustc_codegen_llvm/src/attributes.rs:71-78`), `rustc` permits the attribute combination (`compile_rc = 0`), downgrading `InlineAttr::Always` to `InlineHint` when `llvm_util::get_version() < (23, 0, 0)` and emitting `alwaysinline` on LLVM `>= 23` where `AlwaysInliner` enforces `TTI.areInlineCompatible`.
3. **Tier 3 — LLVM `"target-features"` Emission & Live Silicon `SIGILL` Verification (`attributes.rs:423-434, 646-684`)**:
   In `probe_results.json` (`part2_dynamic_dispatch_inlining_and_sigill`), private `#[inline]` kernels `avx2_kernel_entry` (`attributes #3`: `inlinehint`, `"target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3"`) and `avx512_kernel_entry` (`attributes #4`: `inlinehint`, `"+avx,+avx2,+avx512f,+f16c,+fma,..."`) are called from `baseline_dispatch_avx2` and `baseline_dispatch_avx512f` (`"target-features": null`). At both `-O2` and `-O3` on the Broadwell Xeon host (`avx2 = true`, **`avx512f = false`**):
   - LLVM inlines `sse41_helper`, `avx2_same_feat_helper`, `_mm256_castsi256_si128`, and `_mm_add_epi32` *into* `avx2_kernel_entry` (`14` instructions, `7` `%ymm` ops, `13` VEX ops, `0` remaining `call` instructions), and lowers `avx512_kernel_entry` to `15` instructions (`6` `%zmm` EVEX ops including `vpbroadcastd %esi, %zmm0`, `vpxord (%rdi), %zmm0, %zmm0`, `vpternlogd $255, %zmm1, %zmm1, %zmm1`).
   - Neither kernel is inlined into its baseline dispatcher: `baseline_dispatch_avx2` (`29` scalar instructions, `0` `%ymm`/`%zmm`/VEX ops) and `baseline_dispatch_avx512f` (`68` scalar instructions at `-O2`, `40` at `-O3`, `0` `%ymm`/`%zmm`/VEX/EVEX ops) retain cross-function tail jumps (`jmp ...avx2_kernel_entry`, `jmp ...avx512_kernel_entry`) behind the `std_detect` atomic cache check and execute cleanly (`dispatch_avx2=230 dispatch_avx512f=152`, `run_rc = 0`).
   - **Live Hardware Counterfactuals (`CE1` & `CE2`)**:
     1. `ce1_unchecked_cross_feature_inlining_and_licm_hoisting`: Compiling the loop-guarded pure AVX-512 reduction when caller and callee share `+avx512f` (simulating unchecked cross-feature inlining) causes `-O3` LICM to hoist `36` `%zmm` EVEX instructions (`vpbroadcastd %ecx, %zmm0`, `vpxord (%rdx), %zmm0, %zmm0`, ...) into `unchecked_hoisted_caller` *above* a runtime slice of all-`false` guards (`[false, false, false, false]`). Native execution on Broadwell immediately terminates with **`SIGILL` (`returncode = -4`)**.
     2. `ce2_forged_safe_fnptr_coercion_bypass`: Transmuting `safe_avx512_fn` (`unsafe fn(&[i32; 16]) -> i32`) to a safe `fn(&[i32; 16]) -> i32` pointer (simulating removal of `TypeError::TargetFeatureCast`) and passing it to safe `baseline_higher_order` terminates with **`SIGILL` (`returncode = -4`)**.

Basis: source + execution + derived

### `L4`: `core::arch` (`stdarch`) Immediates, MCP#838, and Non-Power-of-Two `#[repr(simd)]` Padding

In production Rust crates, explicit `core::arch` intrinsics represent a major fraction of emitted vector code: across a 4-crate release-build LLVM IR benchmark (`memchr`, `crc32fast`, `base64`, `regex-automata` under `rustc 1.99.1`), `39` explicitly `#[target_feature]`/`std::arch`-annotated functions emit `1,942` of the `4,788` total vector IR instructions (**`40.56%`**), alongside `2,846` (`59.44%`) auto-vectorized instructions across `64` unannotated functions. Scanning the installed `library/stdarch/crates/core_arch/src` sysroot (`probe_results.json`, `part4_sysroot_stdarch_and_simd_census`) quantifies the exact verification surface:

| `core_arch/src` Subdirectory | `.rs` Files | `#[target_feature]` Attrs | `#[rustc_legacy_const_generics]` | `static_assert_uimm_bits!` | Safe `pub fn` Wrappers | `pub unsafe fn` Wrappers |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `x86` | `50` | `6,179` | `1,494` | `887` | `5,586` | `562` |
| `x86_64` | `23` | `139` | `60` | `68` | `92` | `51` |
| `aarch64` | `13` | `7,835` | `597` | `398` | `1,954` | `251` |
| `wasm32` | `5` | `281` | `2` | `0` | `7` | `16` |
| `riscv_shared` + `riscv64` | `6` | `25` | `3` | `0` | `0` | `0` |
| **Total (`6` arch dirs)** | **`97`** | **`14,459`** | **`2,156`** | **`1,353`** | **`7,639`** | **`880`** |

Notice that **`89.7%` (`7,639 / 8,519`)** of matched `pub` vendor intrinsic wrappers across `x86`, `x86_64`, `aarch64`, and `wasm32` are now **safe functions** (via RFC 2396 `SafeTargetFeatures`), leaving `pub unsafe fn` only on raw-pointer load/store/gather/scatter intrinsics! Three representation mechanisms govern `core::arch`:

1. **`#[rustc_legacy_const_generics(idx, ...)]` & Post-Monomorphization Immediate Checks (`s10`, `s11`)**:
   Validated in `compiler/rustc_passes/src/check_attr.rs:1151-1193` (requiring every generic parameter on the `fn` to be a `const` generic matching the attribute index list) and lowered in `compiler/rustc_ast_lowering/src/expr.rs:212-215, 529-604`, which extracts the specified positional call arguments and wraps them as `GenericArg::Const(AnonConst)`. Passing a runtime `i32` variable (`s11`) fails during HIR const-checking with `E0435` (`attempt to use a non-constant value in a constant`). Vendor immediate bit-widths (such as 8-bit `IMM8` on `_mm256_blend_epi32`) are NOT encoded in the Rust parameter type (`const IMM8: i32`); instead, `static_assert_uimm_bits!(IMM8, 8)` (`library/stdarch/crates/core_arch/src/macros.rs:34-50`) expands to an inline `const { assert!(0 <= IMM8 && IMM8 < (1 << 8), ...) }`, failing during post-monomorphization const evaluation (`E0080`: `evaluation panicked: IMM8 doesn't fit in 8 bits (unsigned)`, `s10`) before LLVM's `immarg` requirement is reached.
2. **MCP#838 Ban on `#[repr(simd)]` Field Projection (`validate.rs:82`)**:
   `compiler/rustc_mir_transform/src/validate.rs:82` rejects any MIR `PlaceElem::Field` projection out of a `#[repr(simd)]` ADT (`Projecting into SIMD type U32x4 is banned by MCP#838`, `compile_rc = 101` under `RUSTC_ICE=0`).
3. **Power-of-Two Layout Padding on Non-Power-of-Two `#[repr(simd)]` Vectors**:
   As documented in `library/stdarch/crates/core_arch/src/macros.rs:116-124, 277` and verified live in `probe_results.json` (`repr_simd_nonpow2_padding_i16x10`), `#[repr(simd)] struct I16x10([i16; 10])` pads both size and alignment from `size_of::<[i16; 10]>() == 20` bytes up to **`32` bytes (`<10 x i16>` padded to 256-bit alignment)**. Consequently, `transmute::<I16x10, [i16; 10]>` is statically rejected for size mismatch (`32 != 20`), and `stdarch`'s `as_array(&self) -> &[T; N]` must cast pointers (`unsafe { &*(self as *const Self as *const [T; N]) }`), reading the leading `20` initialized lane bytes while leaving trailing `12` padding bytes untouched.

Basis: source + execution

### `L5`: `core::intrinsics::simd` Lowering and Lane/Mask Refinement (`75` Fixed-Length Intrinsics)

`library/core/src/intrinsics/simd/mod.rs` declares **`75` fixed-length `simd_*` intrinsics** (and `0` scalable intrinsics in `scalable.rs` on `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`). `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs:593-602` delegates all `simd_*` calls to backend `codegen_simd_intrinsic` (`compiler/rustc_codegen_llvm/src/intrinsic.rs:2028-3264`), establishing six exact refinement contracts confirmed in `-O0` LLVM IR, `-O2` x86-64 disassembly, and native parity execution (`probe_results.json`, `part3_portable_simd_intrinsics`):

1. **Mask Representation & `vector_mask_to_bitmask` (`intrinsic.rs:2028-2040`)**:
   Vector masks (`Simd<iN, L>`) carry a strict representation precondition: every lane must be all-zeros (`0`) or all-ones (`-1` / `!0`; e.g., `simd_eq` returns `[-1, 0, -1, 0]`). `vector_mask_to_bitmask` extracts `<L x i1>` by shifting each lane right by `elem_bits - 1` (`bx.lshr(i, bits - 1)`) and truncating (`bx.trunc(shifted, i1_vector)`), rather than comparing `icmp ne 0`. In `-O0` IR (`kernel_avx2_bitmask_u16`), this emits `%1 = lshr <16 x i8> %0, splat (i8 7); %2 = trunc <16 x i8> %1 to <16 x i1>`, which `-O2` folds directly into a single **`vpmovmskb %xmm0, %eax`** (or `pmovmskb` on SSE2) because x86 byte/dword mask-move instructions inspect the MSB sign bit directly.
2. **`simd_bitmask` Endianness & Non-Power-of-Two Zero-Extension (`intrinsic.rs:2346-2397`)**:
   After `bitcast <L x i1> to iL` (preceded on big-endian targets by reversing bit order within each byte, matching `IntrinsicSimd.lean:168-181`), `rustc` zero-extends `iL` to `L.max(8).next_power_of_two()` for integer return types (`u8`..`u64`) or `L.div_ceil(8) * 8` stored/loaded at `Align::ONE` for `[u8; ceil(L/8)]`. On `I16x10` (`10` lanes), `-O0` IR emits `%4 = bitcast <10 x i1> %3 to i10; %_2 = zext i10 %4 to i16`, `-O2` emits `packsswb` + `pmovmskb` + `andl $1023, %ecx`, and `[-1, -1, 0, -1, 0, 0, -1, 0, -1, 0]` evaluates to `0b01_0100_1011u16` (`331`) and `[0b0100_1011, 0b0000_0001]`.
3. **`simd_select` & `simd_select_bitmask` Equivalence (`intrinsic.rs:2051-2088, 2299-2345`)**:
   `simd_select` lowers via `vector_mask_to_bitmask` + `select <L x i1>` (emitting `vpblendvb %xmm0, (%rdx), %xmm1, %xmm0` on `U8x16`), while `simd_select_bitmask` truncates the integer/byte-array mask to `iL`, bitcasts to `<L x i1>` (reversing bits on big-endian), and emits `select <L x i1>` (`vpshufb` + `vpand` + `vpcmpeqb` + `vpblendvb`). Native execution verifies bitwise parity between `simd_select(m, yes, no)` and `simd_select_bitmask(simd_bitmask(m), yes, no)` across all `256` tested byte-mask patterns.
4. **`simd_shuffle` Bounds & Lowering (`intrinsic.rs:2170-2256`)**:
   Validates `idx[i] < 2 * in_len` at monomorphization; `Idx4([0, 4, 7, 8])` on `U32x4` (`limit = 8`) fails closed with `E0511` (`SIMD index #3 is out of bounds (limit 8)`). Valid `[3, 4, 1, 6]` emits `shufflevector <4 x i32> %0, <4 x i32> %1, <4 x i32> <i32 3, i32 4, i32 1, i32 6>` (`pshufd $232` + `pshufd $231` + `punpckldq` on SSE2), producing `[40, 50, 20, 70]` from `[10, 20, 30, 40]` and `[50, 60, 70, 80]`.
5. **`simd_cast` vs. `simd_as` (`intrinsic.rs:2464-2579`)**:
   `simd_cast` preserves value across lane-equal integer sign/zero widenings (`sext <8 x i16> to <8 x i32>` -> `vpmovsxwd`, `zext <8 x i16> to <8 x i32>` -> `vpmovzxwd`), whereas float-to-integer `simd_as` emits **saturating** conversion (`NaN -> 0`, `+inf -> i32::MAX`, `-1.0e20 -> i32::MIN`, `-42.9 -> -42`), matching Rust scalar `as` semantics (`llvm.fptosi.sat` / saturating lowering) whereas out-of-range float-to-int `simd_cast` is immediate UB.
6. **`simd_masked_load` & `simd_masked_store` (`intrinsic.rs:2580-2770`)**:
   Maps const generic `SimdAlign::{Unaligned => 1, Element => elem_align, Vector => vec_align}` to pointer alignment attributes on `@llvm.masked.load.v8i32.p0(ptr align 1 %src, <8 x i1> %3, <8 x i32> %1)` and `@llvm.masked.store.v8i32.p0(<8 x i32> %6, ptr align 1 %dst, <8 x i1> %8)` (`vpmaskmovd` + `vblendvps` on AVX2). Executing against a 5-element slice `[11, 22, 33, 44, 55]` with 8-lane mask `[-1, 0, -1, 0, -1, 0, 0, 0]` loads `[11, 71, 33, 73, 55, 75, 76, 77]` and stores `[11, 901, 33, 903, 55, 905, 906, 907]` without faulting on out-of-bounds lanes `5..7`.

Basis: source + execution + derived

### `L6`: Lean 4 Mechanization (`TargetFeatureAndSimdRefinement.lean`) and Anneal Integration Contract

`support/TargetFeatureAndSimdRefinement.lean` (`1,528` lines, `Lean v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`) mechanizes both the `TargetFeature` capability/inlining/hoisting machine and the `core::intrinsics::simd` lane/mask/memory refinement using `Init` alone:

| Lean 4 Theorem (`TargetFeatureAndSimdRefinement.*`) | Mechanized Statement | Kernel `#print axioms` |
| :--- | :--- | :--- |
| `mirInlineGate_implies_llvmInlineGate` | `eqFeatures callee caller = true → subsetFeatures callee caller = true` | `[propext, Quot.sound]` |
| `mirInlineGate_strictly_stronger_than_llvmInlineGate` | `subsetFeatures sse41Set avx2Set = true ∧ eqFeatures sse41Set avx2Set = false` | `∅` (axiom-free) |
| `no_sigill_soundness_of_typed_and_feature_monotone_inlining` | Any `WellTypedProg` optimized by feature-monotone inlining (`gate callee caller → callee ⊆ caller`) + legal pure hoisting never faults with `Fault.illegalInstruction` on any implication-closed `cpu ⊇ entry.reqFeatures` (including witnessed `safeFnPtr` values returned to baseline code) | `[propext, Quot.sound]` |
| `ce1_sharpness_counterexample` | Well-typed guarded `avx2` dispatch evaluates to `.ok (.int 42)` under `subsetFeatures` inlining on `baselineSse2Cpu`, whereas unchecked cross-feature inlining + pure hoisting evaluates to `.fault .illegalInstruction` | `[propext]` |
| `ce2_sharpness_counterexample` | Baseline safe coercion `reifySafeFnPtr` of an `avx2` fn is rejected by `TypedExpr`, allowed inside `avx2Set`, and faults with `.fault .illegalInstruction` without `unsafe` if permitted in baseline code | `∅` (axiom-free) |
| `simdShuffleChecked_lanewise_eq` / `simdShuffleChecked_oob_rejected` | `simd_shuffle` succeeds iff `∀ i, idx[i] < 2 * n`, matching `if idx[i] < n then x[idx[i]] else y[idx[i] - n]`, and rejects OOB indices | `[propext, Quot.sound]` / `[propext]` |
| `extractMaskBitMSB_encodeMaskLane` | For all lane widths `w + 1`, `((encodeMaskLane w b >>> w).truncate 1 == 1#1) = b` | `[propext]` |
| `simdSelectBitmask_pack_eq_simdSelect` & `nonpow2_10lane_bitmask_little_endian_eq` | For both `.little` and `.big` endianness and all `n` (including `n = 10`, `0b0101001011`), `simdSelectBitmask e (simdBitmaskPack e mask) yes no = simdSelectVec mask yes no` | `[propext, Quot.sound]` / `∅` |
| `simdMaskedLoad_active_inbounds_sound` & `simdMaskedStoreSpec_frame_and_lanes` | Disabled lanes never fault when `base + n > mem.length`, return `passthrough[i]`, and preserve `mem[base + i]` and all out-of-window addresses | `[propext, Quot.sound]` / `[propext]` |

**Anneal (`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`) Integration Requirements**:
1. **`Body.reqFeatures` alongside `Body.isUnsafe`**: Currently `Trusted.MirAst.Body` (`trusted/lean/Trusted/MirAst.lean:862-867`) carries only `isUnsafe : Bool`, and `BodyVerified` (`trusted/lean/Trusted/MirSemantics.lean:1751-1758`) discharges unannotated functions unconditionally (`body.isUnsafe = false`). Because RFC 2396 `SafeTargetFeatures` functions are safe in Rust source yet require `reqFeatures ⊆ cpuFeatures` upon entry, `Body` **must** carry `reqFeatures : FeatureSet`, `State` must carry dynamic `cpuFeatures : FeatureSet` (unlike `vendor/lean-miri/Miri/Interpreter/ExecutionCallLeaves.lean:23-39` and `CompilerTargetFeatures.lean:14-37`, which check against a static compile-time `session.internal_target_features` list and thus cannot model runtime `is_x86_feature_detected!` dispatch across non-enabled host features!), and `BodyVerified` must quantify over `subsetFeatures body.reqFeatures state.cpuFeatures = true`.
2. **Simultaneous `simd_*` + `Call` Support Due to Asymmetric MIR Inlining**: Because `rustc`'s MIR inliner inlines equal-feature `core::arch` functions (`_mm256_add_epi32` -> `simd_add` + `Transmute`) while leaving strict-subset `core::arch` calls (`_mm256_set1_epi32`, `_mm256_castsi256_si128`, `_mm_add_epi32`) as `TerminatorKind::Call`, Anneal cannot verify real `#[target_feature(enable = "avx2")]` bodies by adding `Call` alone or `simd_*` alone—both seams (`MirTy.simdVec` + `StatementKind.intrinsic` / `TerminatorKind.call` with `callee.reqFeatures ⊆ caller_or_guarded_features`) are exercised inside a single `avx2` body.

Basis: source + execution + derived

## Boundaries

The following negative space and non-claims hold strictly from our evidence:

1. **Wasm relaxed target-feature rules (`is_like_wasm`)**: **known not to apply** — `tcx.is_target_feature_call_safe` (`compiler/rustc_middle/src/ty/context.rs:1229`) unconditionally returns `true` on Wasm targets because WebAssembly validation occurs at module instantiation rather than faulting via per-instruction dynamic CPUID dispatch.
2. **Dynamically toggleable modal ISA state (e.g., Armv9 SME `PSTATE.SM` / `PSTATE.ZA` streaming-mode transitions) and negative ABI features (`+soft-float`)**: **known not to apply** — Capability-witness `fn()` pointer reification (`s06`, `tcx.adjust_target_feature_sig`) relies on `cpuFeatures` being an immutable, monotone process-wide capability; features that can be turned off mid-thread or alter scalar calling conventions (`target_features.rs:22-25, 1298-1308`) break monotonicity.
3. **Scalable vector intrinsics (`core::intrinsics::simd::scalable`, SVE/RVV variable-VL vectors)**: **unsupported** / **not examined** — `scalable.rs` exposes `0` intrinsics in the examined `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` sysroot, and our Lean `SimdVec α n` model indexes lanes by fixed `n : Nat`.
4. **Floating-point NaN payload propagation, `simd_fma` / `simd_relaxed_fma`, transcendental `simd_fsin`/`fcos`/`fexp`/`flog`, and `simd_gather`/`scatter` pointer provenance**: **not examined** in Lean mechanization — `TargetFeatureAndSimdRefinement.lean` formalizes `simd_shuffle`, `vector_mask_to_bitmask`, `simd_bitmask`, `simd_select`, `simd_select_bitmask`, `simd_masked_load`, and `simd_masked_store`, while `simd_as` saturation was verified empirically in `probe_results.json` rather than mechanized over IEEE-754 floats.
5. **Native AArch64 and Big-Endian hardware execution**: **not examined** dynamically — `aarch64-unknown-linux-gnu` target-feature lattices and LLVM attributes (`s12`) were verified via `rustc --target=aarch64-unknown-linux-gnu --emit=llvm-ir,metadata` and upstream source, and big-endian `simd_bitmask` lane ordering was verified via source (`rustc_codegen_llvm/src/intrinsic.rs`, `IntrinsicSimd.lean`) and Lean proof (`simdSelectBitmask_pack_eq_simdSelect`), not on physical AArch64 or s390x/powerpc64 hardware.
6. **Current `joshlf/anneal` execution of SIMD or `#[target_feature]` calls**: **unsupported** at `c131b320eeeb26ef692e5afd5ec8db49ee518613`, where `MirAst.lean:308-321, 654-662, 782-795` maps SIMD types, intrinsics, and calls to `.unsupported`.

## Evidence

### Upstream Primary Sources (Line-Pinned)

- **`rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, `1.99.1`)**:
  - `compiler/rustc_ast_lowering/src/item.rs:1694-1702` & `expr.rs:212-215, 529-604`: `HeaderSafety::SafeTargetFeatures` rewrite; `#[rustc_legacy_const_generics]` positional-to-`AnonConst` splicing.
  - `compiler/rustc_hir/src/hir.rs:4430-4465`: `HeaderSafety::SafeTargetFeatures` projecting `safety() -> Safety::Unsafe`.
  - `compiler/rustc_middle/src/ty/context.rs:1226-1258`: `is_target_feature_call_safe` and `adjust_target_feature_sig`.
  - `compiler/rustc_hir_typeck/src/{callee.rs:557-625, coercion.rs:1237-1278}` & `compiler/rustc_borrowck/src/type_check/mod.rs:1048-1060`: call typing and safe `FnPtr` coercion / `TargetFeatureCast`.
  - `compiler/rustc_mir_build/src/check_unsafety.rs:412-464, 803-824, 993-1032, 1072-1084`: THIR safe `#[target_feature]` call gate and `build_enabled` note.
  - `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs:528-536, 589-597`: exclusion of `#[target_feature]` `FnDef` from `Fn*` and `AsyncFn*`.
  - `compiler/rustc_codegen_ssa/src/{codegen_attrs.rs:109-111, 356, 448-460, target_features.rs:165-175, 226-253, mir/intrinsic.rs:593-602}`: `safe_target_features`, closure inheritance, `#[inline(always)]` error, safe trait method ban, contrapositive `-feature` disablement, and `simd_*` dispatch.
  - `compiler/rustc_target/src/target_features.rs:216-423, 425-559, 1104-1105, 1235-1253, 1298-1308`: `AARCH64_FEATURES`, `X86_FEATURES`, vector ABI thresholds, and `implied_target_features`.
  - `compiler/rustc_mir_transform/src/{inline.rs:841-850, validate.rs:82}`: strict feature-equality MIR inlining gate; MCP#838 `#[repr(simd)]` projection ban.
  - `compiler/rustc_passes/src/check_attr.rs:1151-1193`: `#[rustc_legacy_const_generics]` attribute validation.
  - `compiler/rustc_codegen_llvm/src/{attributes.rs:64-85, 423-434, 646-684, intrinsic.rs:2028-3264}` & `compiler/rustc_llvm/src/llvm_util.rs:239-336`: LLVM `"target-features"` emission and `simd_*` LLVM IR lowering.
- **`rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `1.98.0-nightly`, LLVM `22.1.6`)**:
  - `compiler/rustc_target/src/target_features.rs:355`: `sve` implying `&["neon"]` prior to `1.99.1`'s `&["neon", "fp16"]`.
  - `compiler/rustc_codegen_ssa/src/codegen_attrs.rs:420-432`: `#[inline(always)]` + `#[target_feature]` rejection.
- **`rust-lang/rust` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `1.102.0-nightly`)**:
  - `compiler/rustc_codegen_llvm/src/attributes.rs:71-78`: LLVM `< 23` `InlineHint` downgrade vs. LLVM `>= 23` `alwaysinline` acceptance with `#[target_feature]`.
- **`rust-lang/stdarch` (`ca26a96d57b295dcd927622877242940a0f3c02e`)**:
  - `crates/core_arch/src/macros.rs:34-50, 116-124, 277`: `static_assert_uimm_bits!`, `simd_ty!`, and MCP#838 pointer-cast array access.
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)**:
  - `trusted/lean/Trusted/{MirAst.lean:308-321, 654-662, 782-795, 862-867, MirSemantics.lean:1568, 1751-1758}`: `.unsupported` fail-closed lowering and `Body.isUnsafe` / `BodyVerified`.
  - `vendor/lean-miri/Miri/{Interpreter/IntrinsicSimd.lean:75-79, 168-181, 366-383, Interpreter/ExecutionCallLeaves.lean:23-39, Input/CompilerTargetFeatures.lean:14-37}`: Miri SIMD intrinsic semantics and static `internal_target_features` check.

### Preserved Package Artifacts (`2026-11-21`)

1. **`support/probe_target_feature_and_simd.py` and `support/probe_results.json`**: Self-contained Python 3 probe executing all `12` Part 1 type/attribute/lattice checks (`s01`–`s12`), Part 2 `-O2`/`-O3` MIR/LLVM-IR/x86-64 disassembly and live Broadwell `SIGILL` counterfactuals (`CE1`, `CE2`), Part 3 `core::intrinsics::simd` IR/disassembly/256-pattern execution parity + `I16x10` padding + MCP#838 + `E0511` checks, and Part 4 sysroot `core_arch` / `simd` census.
2. **`support/TargetFeatureAndSimdRefinement.lean`**: Standalone `1,528`-line `Lean v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) proof script checked with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit 0`), using strictly `{propext, Quot.sound}` (`0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`).

## Revalidation

1. **Re-run the compiler, IR, disassembly, and execution probe**:
   ```bash
   python3 support/probe_target_feature_and_simd.py --out /tmp/revalidated_probe.json
   ```
   Confirm exit code `0` and inspect `/tmp/revalidated_probe.json`:
   - If testing `rustc >= 1.102.0-nightly` (LLVM `>= 23`), `s09_inline_always_with_target_feature.compile_rc` will flip from `1` to `0`, and `s12_aarch64_sve2_sve_fp16_neon_lattice.sve_calling_fp16_compile_rc` will flip from `1` (`1.98.0-nightly`) to `0` (`>= 1.99.1`), while `baseline_dispatch_avx2` and `baseline_dispatch_avx512f` must continue to report `ymm_insns_count == 0` and `zmm_insns_count == 0`.
   - On CPUs that *do* support `avx512f` (`host_supports_avx512f == true`), `ce1` and `ce2` will execute EVEX instructions without `SIGILL`; re-run under `qemu-x86_64 -cpu Broadwell` (or target `+avx512vp2intersect` on non-TigerLake silicon) to reproduce `returncode == -4` (`SIGILL`).
2. **Re-verify the Lean 4 kernel proofs and axiom footprint**:
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true support/TargetFeatureAndSimdRefinement.lean
   ```
   Confirm exit code `0` with zero warnings and verify via `#print axioms` that all exported theorems depend at most on `[propext, Quot.sound]`.
3. **Diff upstream implementation anchors on toolchain upgrades**: diff `compiler/rustc_middle/src/ty/context.rs` (`is_target_feature_call_safe`, `adjust_target_feature_sig`), `compiler/rustc_mir_build/src/check_unsafety.rs`, `compiler/rustc_mir_transform/src/inline.rs`, `compiler/rustc_target/src/target_features.rs`, and `compiler/rustc_codegen_llvm/src/{attributes.rs, intrinsic.rs}`.
