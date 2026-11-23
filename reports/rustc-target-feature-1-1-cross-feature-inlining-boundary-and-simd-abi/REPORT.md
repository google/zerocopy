# Target Feature 1.1 Safety, Cross-Feature Inlining Boundaries, and SIMD Vector ABI in rustc

## Summary

**Basis:** `source`, `execution`, `derived`.

On x86-64 targets (`x86_64-unknown-linux-gnu`), `#[target_feature]` functions sit at the intersection of four distinct compiler invariants spanning frontend/HIR attribute parsing, THIR/borrowck safety checking, MIR inlining, LLVM optimization and target-transform hooks, and monomorphization-time ABI validation:

1. **Safe target-feature function calls and coercions (`target_feature_11`) (`Basis: source, execution`):** Under Rust 2024 and current nightlies (`rust-lang/rust` revisions `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `49d734536222bf28bb6d07d885b3a81d145981da`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, and `277240238554297f93fa9ee3c7643dfa03ccbbb4`), a safe `#[target_feature(enable = "...")]` function records `safe_target_features = true` in `CodegenFnAttrs` (`compiler/rustc_codegen_ssa/src/codegen_attrs.rs:123-125`). Safe callers may call it without `unsafe` (`E0133`) or coerce its `FnDef` item to a safe `fn` pointer (`E0308`) **iff** `tcx.is_target_feature_call_safe(callee_features, caller_features)` holds — i.e., every feature in `callee_features` appears by name in `caller_features` (`compiler/rustc_middle/src/ty/context.rs:1326-1358`). Baseline functions, non-superset callers (e.g. `sse4.2` calling `avx2`), `main` (`entry.rs:108-114`), and safe trait methods or trait impls (`target_features.rs:176-186`) are rejected; non-`#[inline(always)]` closures inherit their enclosing owner's `target_features` unless desugared as `async fn` / `gen fn` body coroutines (`codegen_attrs.rs:404-417`).
2. **MIR vs. LLVM cross-feature inlining asymmetry (`Basis: source, execution`):** Contrary to informal descriptions (and correcting the imprecise statement in sibling corpus report `target-features-implications-detection-and-abi-effects`, which claimed `rustc`'s MIR inliner allowed `caller >= callee`), `rustc_mir_transform::inline` does **not** permit subset or set-equal inlining. Both `Inline` and `ForceInline` execute `check_codegen_attributes`, which tests `callee_feature_names.ne(this_feature_names)` via ordered iterator comparison over raw `target_features` slices (`compiler/rustc_mir_transform/src/inline.rs:840-849`). Because `parse_tf_attribute` splits comma-separated features in source order without sorting or deduplicating (`compiler/rustc_attr_parsing/src/attributes/codegen_attrs.rs:573-575`), even identical feature sets written in reversed attribute order (`#[target_feature(enable = "avx2,bmi1")]` called from `#[target_feature(enable = "bmi1,avx2")]`), as well as baseline helpers (`#[inline(always)] fn()`) and implied subset helpers (`avx` inside `avx2`), are **refused** by MIR `ForceInline` and `Inline`, yet **inlined** at `-Copt-level=3` by LLVM (`llvm/lib/Target/X86/X86TargetTransformInfo.cpp:6782-6855`) whenever `(RealCallerBits & RealCalleeBits) == RealCalleeBits` and any relocated `CallBase` vector/aggregate argument keeps identical register lowering (`areTypesABICompatible`). Conversely, baseline callers retain a `tail call fastcc` to `avx2` callees.
3. **The `2026-09` to `2026-11` `#[inline(always)]` + `#[target_feature]` divergence (`Basis: source, execution`):** In `14210df0e` (`2026-05-31`, LLVM `22.1.6`, verified live with `rc=1`) and `49d73453` (`2026-09-11`), `rustc_codegen_ssa/src/codegen_attrs.rs:432-444` emitted a hard error (`"cannot use #[inline(always)] with #[target_feature]"`, tracking `rust-lang/rust#145574`) because older LLVM pipelines could inline `alwaysinline` callees without verifying target features (`rust-lang/rust#116573`, `llvm/llvm-project#70563`). By `3ef0c22cd` (`2026-11-11`, LLVM `23.1.5`) and `277240238` (`main`), `codegen_attrs.rs` removed that hard error, while `rustc_codegen_llvm/src/attributes.rs:73-81` guarded `InlineAttr::Always` on `target_features`-bearing functions: downgrading to `InlineHint` when `llvm_util::get_version() < (23, 0, 0)` and emitting LLVM `AlwaysInline` only on LLVM `>= 23`, where `llvm::getAttributeBasedInliningDecision` enforces `!CalleeTTI.areInlineCompatible(Caller, Callee)` **before** honoring `Attribute::AlwaysInline` (`llvm/lib/Analysis/InlineCost.cpp:3203-3217`).
4. **SIMD vector ABI, `AbiErrorDisabledVectorType`, and `2026-11` `<= 128`-bit `extern "Rust"` relaxation (`Basis: source, execution`):** On x86-64 under `extern "C"`, fixed-width SIMD values and single-vector `#[repr(C)]` aggregates (`Wrap256(__m256)`) classify into `Class::Sse` + `Class::SseUp` (`compiler/rustc_target/src/callconv/x86_64.rs:82,176-205,293-295`) and lower via `PassMode::Cast` to `<4 x float>`, `<8 x float>`, `<16 x float>`, or `<32 x i8>` (`rustc_codegen_llvm/src/abi.rs:152-220`). During monomorphization, `rustc_monomorphize/src/mono_checks/abi_check.rs:68-104,171-287` verifies both definition sites (`check_instance_abi`) and call sites (`check_call_site_abi`) against `X86_FEATURES_FOR_CORRECT_FIXED_LENGTH_VECTOR_ABI = &[(128, "sse"), (256, "avx"), (512, "avx512f")]` (`target_features.rs:1172-1173`), emitting `AbiErrorDisabledVectorType` on mismatches while deferring unmonomorphized `--crate-type=lib` items altogether. Under `extern "Rust"`, `14210df0e:839-841` and `49d73453:874-876` passed all `SimdVector` values indirectly (`sret(..., align 16/32/64)`); by `3ef0c22cd:776-789,916-918`, `can_pass_simd_directly` passes `<= 128`-bit vectors directly on non-softfloat `x86_64` (`sse2` baseline), while `>= 256`-bit vectors remain indirect `sret`.

Every theorem establishing `SIGILL`-freedom under superset inlining, the baseline-caller `SIGILL` counterexample, MIR-to-LLVM refinement with strict separations, and `PassMode::Cast` ABI compatibility is mechanized and kernel-checked in `support/TargetFeatureInliningBoundaryAndSimdAbiSoundness.lean` (`2,332` lines, `605` declarations, `0` `sorry`, `0` `Classical.choice`, `0` `ofReduceBool`, `0` `._unsafe_rec`, checked under Lean `v4.34.1` with `-DwarningAsError=true`).

---

## Applicability

**Basis:** `source`, `execution`, `derived`.

### Scope and Version Pinning

| Dimension | Applies To (Verified Anchor) | Notes / Contrast |
| --- | --- | --- |
| Primary target triple | `x86_64-unknown-linux-gnu` (`System V AMD64` psABI, baseline `[sse, sse2]`) | Contrast rules for `wasm*` (`is_like_wasm`), `x86` SSE2, and `aarch64` (`neon`) inspected in `rustc_target` and `rustc_codegen_ssa`. |
| Live execution toolchain | `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `2026-05-31`, LLVM `22.1.6`) | Executed via `support/probe_target_feature_inlining_simd_abi.py`, producing `support/probe_results.json`. |
| Pre-relaxation source snapshot | `rust-lang/rust` `49d734536222bf28bb6d07d885b3a81d145981da` (`2026-09-11`) | Matches `14210df0e` on rejecting `#[inline(always)]` + `#[target_feature]` (`#145574`) and unconditional `make_indirect()` on `SimdVector`. |
| Post-relaxation nightly source & LLVM 23 | `rust-lang/rust` `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, `2026-11-11`) with `rust-lang/llvm-project` `0a5579eb649d3634a9c30ac873300cc2944fa070` (`LLVM 23.1.5`) | Removes `#145574` error from `codegen_attrs.rs`, gates `AlwaysInline` on LLVM `>= 23`, adds `can_pass_simd_directly` for `<= 128`-bit `extern "Rust"` SIMD. |
| Current upstream `main` sources | `rust-lang/rust` `277240238554297f93fa9ee3c7643dfa03ccbbb4`; `llvm/llvm-project` `970a1b012bacd479f450604d34faa52f5ccce5d6` | Confirms continuity of MIR `Inline` check (`inline.rs:840-849`), `attributes.rs:73-81`, `abi_check.rs`, and `X86TTIImpl::areInlineCompatible`. |
| Downstream verifier semantics | `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), `trusted/lean/Trusted/MirSemantics.lean` | Current `M_anneal` step faults `.call` with `.unsupported` (`MirSemantics.lean:1568`). |
| Mechanization kernel | `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) | Kernel-checked standalone under `prelude` + `Init.{Core,NotationExtra,Data.List.Basic,Data.Nat.Basic}`. |

### Negative Space Classification

| Phenomenon | Epistemic Status | Explanation & Location |
| --- | --- | --- |
| Live binary execution of `rustc 1.102.0-nightly (3ef0c22cd)` | **not examined locally** | Local execution in `support/probe_results.json` ran `1.98.0-nightly` (`14210df0e`, LLVM `22.1.6`); `3ef0c22cd` / `277240238` changes are verified via direct primary-source diffs (`codegen_attrs.rs`, `attributes.rs`, `callconv/mod.rs`, `InlineCost.cpp`). |
| Scalable SIMD vectors (`SVE`, `RVV`, `rustc_scalable_vector`) | **not examined empirically** | Source inspection observed `UsesVectorRegisters::ScalableVector` (`abi_check.rs:105-122`) and `FIXME(#161753)` skipping `check_call_site_abi` for rustic ABIs (`abi_check.rs:217-226`); no live SVE/RVV execution was run. |
| `#[rustc_force_inline]` cross-feature inlining override | **known not to apply as bypass** | Inspected `inline.rs:260-280,803-852`: `ForceInline` uses the same `check_codegen_attributes` gate (`callee_feature_names.ne(this_feature_names)`) and therefore rejects cross-feature mismatches just like `Inline`. |
| Uninstantiated `pub extern "C" fn` in `--crate-type=lib` | **observed deferment** | `check_feature_dependent_abi` runs only per monomorphized `Instance` (`abi_check.rs:316-323`); generic or unreferenced `pub` items without `#[no_mangle]`/`#[inline(never)]` may postpone `AbiErrorDisabledVectorType` to downstream crates. |
| Multi-function call stack execution in Anneal `M_anneal` | **unsupported in target verifier** | `joshlf/anneal` (`c131b320e`, `MirSemantics.lean:1568`) returns `.fault .unsupported` on `.call` terminators and does not track hardware `target_features`. |

---

## Findings

### 1. Safe Target-Feature Functions (`target_feature_11`): Capability Lattice, Call Discipline, and Coercions

**Basis:** `source`, `execution`, `derived`.

Prior to the stabilization of `target_feature_11`, applying `#[target_feature(enable = "...")]` outside WebAssembly required the `fn` item itself to be `unsafe`. Across the audited `rust-lang/rust` revisions (`14210df0e2` through `2772402385`), the parser, attribute builder, THIR unsafety checker, HIR typechecker, and MIR borrowchecker form a two-stage capability discipline:

#### 1.1 Parsing and Attribute Construction Preserves List Order

In `compiler/rustc_attr_parsing/src/attributes/codegen_attrs.rs:544-578`, `parse_tf_attribute` parses `enable = "..."` by splitting on `','` verbatim without sorting or deduplicating:

```rust
// rust-lang/rust@3ef0c22cd — compiler/rustc_attr_parsing/src/attributes/codegen_attrs.rs:570-577
        let Some(value_str) = cx.expect_string_literal(value) else {
            return features;
        };
        for feature in value_str.as_str().split(',') {
            features.push((Symbol::intern(feature), item.span()));
        }
    }
    features
}
```

`TargetFeatureParser::ALLOWED_TARGETS` (`codegen_attrs.rs:591-601`) syntactically allows `#[target_feature]` on free functions (`Target::Fn`), inherent methods (`MethodKind::Inherent`), provided trait methods (`MethodKind::Trait { body: true }`), and trait impl methods (`MethodKind::TraitImpl`). Lang items (`#[lang]` / `#[panic_handler]`) are rejected in `finalize_check` unless targeting WebAssembly or `actually_rustdoc` (`codegen_attrs.rs:614-623`).

During `CodegenFnAttrs` construction (`compiler/rustc_codegen_ssa/src/codegen_attrs.rs:118-161`), `rustc` records:

```rust
// rust-lang/rust@3ef0c22cd — compiler/rustc_codegen_ssa/src/codegen_attrs.rs:123-126,150-160
let safe_target_features =
    matches!(sig.header.safety, hir::HeaderSafety::SafeTargetFeatures);
codegen_fn_attrs.safe_target_features = safe_target_features;
...
    check_target_feature_trait_unsafe(tcx, did, *attr_span);
...
from_target_feature_attr(tcx, did, features, *was_forced, rust_target_features, &mut codegen_fn_attrs.target_features);
```

Three downstream constraints immediately fire from this stage:

- **Safe trait methods rejected (`target_features.rs:176-186`):** `check_target_feature_trait_unsafe` emits `TargetFeatureSafeTrait` whenever `DefKind::AssocFn` belongs to a `Trait` or `Impl { of_trait: true }` and has `SafeTargetFeatures` (unless WASM or rustdoc). Thus trait methods marked `#[target_feature]` must still be `unsafe fn`.
- **`main` rejected (`compiler/rustc_hir_analysis/src/check/entry.rs:108-114`):** `entry_fn` emits `TargetFeatureOnMain` if `!tcx.codegen_fn_attrs(main_def_id).target_features.is_empty()` outside WASM / rustdoc.
- **Implied-feature expansion (`target_features.rs:90-147`):** `from_target_feature_attr` pushes each `name` returned by `tcx.implied_target_features(feature)` as `TargetFeatureKind::Implied` (`name != feature`), `TargetFeatureKind::Forced`, or `TargetFeatureKind::Enabled` in iteration order into `codegen_fn_attrs.target_features : Vec<TargetFeature>`, rejecting ABI-incompatible internal features (`InternalOnlyTargetFeatureAttr`) or emitting softfloat warnings (`X86_SOFTFLOAT_SSE`, `AARCH64_SOFTFLOAT_NEON`).

#### 1.2 Closure Inheritance Exception for `#[inline(always)]` vs. `async fn` / `gen fn` Coroutines

Closures inherit their parent owner's `target_features` in `compiler/rustc_codegen_ssa/src/codegen_attrs.rs:404-417`:

```rust
// rust-lang/rust@3ef0c22cd — compiler/rustc_codegen_ssa/src/codegen_attrs.rs:404-417
if tcx.is_closure_like(did.to_def_id())
    && (codegen_fn_attrs.inline != InlineAttr::Always
        || matches!(
            tcx.coroutine_kind(did),
            Some(hir::CoroutineKind::Desugared(_, hir::CoroutineSource::Fn))
        ))
{
    let owner_id = tcx.parent(did.to_def_id());
    if tcx.def_kind(owner_id).has_codegen_attrs() {
        codegen_fn_attrs
            .target_features
            .extend(tcx.codegen_fn_attrs(owner_id).target_features.iter().copied());
    }
}
```

This creates a subtle semantic fork: normal closures inside an `#[target_feature(enable = "avx2")]` function inherit `[..., avx2]` even if passed as callbacks (allowing them to call `avx2` helpers safely), whereas a closure marked `#[inline(always)]` deliberately skips inheriting `target_features` (so boxing it avoids assuming the parent's ISA features) — except desugared `async fn` / `gen fn` body coroutines, which are checked inside the parent's feature context and therefore unconditionally inherit.

#### 1.3 THIR Unsafety Checking (`rustc_mir_build`) and Function-Pointer Coercion (`hir_typeck` & `borrowck`)

Importantly for source navigation across compiler revisions, MIR unsafety checking resides in **`compiler/rustc_mir_build/src/check_unsafety.rs`** (not `rustc_mir_transform`). At direct call sites (`check_unsafety.rs:412-458`):

```rust
// rust-lang/rust@3ef0c22cd — compiler/rustc_mir_build/src/check_unsafety.rs:422-433
if sig.safety().is_unsafe() && !safe_target_features {
    ...
    self.requires_unsafe(expr.span, CallToUnsafeFunction(func_id));
} else if let &ty::FnDef(func_did, _) = fn_ty.kind() {
    if !self
        .tcx
        .is_target_feature_call_safe(callee_features, self.body_target_features)
    {
        ...
        self.requires_unsafe(
            expr.span,
            CallToFunctionWith { function: func_did, missing, build_enabled },
        );
    }
```

Here `is_target_feature_call_safe` (`compiler/rustc_middle/src/ty/context.rs:1326-1339`) checks set-inclusion by symbol name:

```rust
callee_features
    .iter()
    .all(|feature| body_features.iter().any(|f| f.name == feature.name))
```

And symmetrically during `FnDef -> FnPtr` coercion in both HIR typecheck (`compiler/rustc_hir_typeck/src/coercion.rs:1321-1331`) and MIR borrowck (`compiler/rustc_borrowck/src/type_check/mod.rs:1045-1060`):

- If `fn_attrs.safe_target_features` is `true`, `tcx.adjust_target_feature_sig(def_id, sig, self.body_def_id.into())` checks `is_target_feature_call_safe(&fun_features, &caller_features)`.
- If true, `sig` is promoted to `hir::Safety::Safe`, allowing implicit coercion to `fn(...) -> ...` **inside** callers whose own `target_features` subsume the target's features.
- Otherwise, `sig_for_fn_def_coercion` returns `Err(TypeError::TargetFeatureCast(def_id))` when expecting `Safety::Safe`, yielding `E0308` (`cannot coerce functions with #[target_feature] to safe function pointers`), while coercing to `unsafe fn(...) -> ...` remains legal everywhere (`UNSAFE_FP`).

#### 1.4 Empirical Verification (`support/probe_results.json`, Experiment A)

Running the local `rustc 1.98.0-nightly (14210df0e 2026-05-31)` probe suite confirms every rule end-to-end (`support/probe_results.json:5-42`):

| Probe ID | Scenario | `rustc` Result | Key Observed Output |
| --- | --- | --- | --- |
| `A1` `safe_avx2_to_avx2_and_native_exec` | `#[target_feature(enable = "avx2")]` safely calling `avx2_leaf` & `avx_leaf` (`avx ⊆ avx2` implication), coercing to `fn(i32)->i32`, closure inheritance, and native baseline coercion to `unsafe fn` guarded by `is_x86_feature_detected!("avx2")` | `rc=0`, exec `rc=0` | `SAFE_CALL=69 SAFE_FP=69 CLOSURE=53 UNSAFE_FP=52` |
| `A2` `baseline_safe_call_rejected` | Safe baseline function calling `avx2_leaf(x)` without `unsafe` | `rc=1` (`E0133`) | `error[E0133]: call to function 'avx2_leaf' with #[target_feature] is unsafe and requires unsafe block` (`requires the following additional target feature: avx2`) |
| `A3` `baseline_safe_fn_ptr_coercion_rejected` | Safe baseline function coercing `avx2_leaf` to `fn(i32) -> i32` | `rc=1` (`E0308`) | `cannot coerce functions with #[target_feature] to safe function pointers` (`found fn item #[target_features] fn(_) -> _ {avx2_leaf}`) |
| `A4` `non_subset_feature_rejected` | `#[target_feature(enable = "sse4.2")]` calling or coercing `avx2_leaf` (`avx2 ⊈ sse4.2`) | `rc=1` (`E0308`, `E0133`) | Emits both `E0308` coercion rejection and `E0133` missing `avx2` call error |
| `A5` `trait_and_main_rejected` | Safe `#[target_feature]` on required trait method (`fn trait_method(&self);`) and on `fn main()` | `rc=1` (3 errors) | `cannot be used on required trait methods`, `cannot be applied to safe trait method`, and `` `main` function is not allowed to have `#[target_feature]` `` |
| `A6` `inline_always_with_target_feature_probe` | `#[target_feature(enable = "avx2")] #[inline(always)]` in `1.98.0-nightly` (`14210df0e`) | `rc=1` (`#145574`) | `error: cannot use #[inline(always)] with #[target_feature]` (`See this issue for full discussion: https://github.com/rust-lang/rust/issues/145574`) |

This matches the observed `rustc 1.98.0-nightly` (`14210df0e`) diagnostic string `found fn item #[target_features] fn(_) -> _ {avx2_leaf}`, while `coercion.rs:1324-1327` and the `E0133`/`E0308` error codes remain structurally identical in `3ef0c22cd` and `277240238`.

---

### 2. Cross-Feature Inlining Boundary: MIR Exact Ordered-Sequence Equality vs. LLVM Subset Inclusion

**Basis:** `source`, `execution`, `derived`.

#### 2.1 MIR Inliner's Strict Ordered-Sequence Equality Check (`inline.rs:840-849`)

Inside `compiler/rustc_mir_transform/src/inline.rs`, both the cost-driven `Inline` pass and forced `ForceInline` (`#[rustc_force_inline]`) pass delegate legality checks to `check_codegen_attributes` (`inline.rs:803-852`). At lines 840-849, `rustc` inspects the `target_features` slices directly:

```rust
// rust-lang/rust@3ef0c22cd (identical logic in 14210df0e & 277240238) — compiler/rustc_mir_transform/src/inline.rs:840-849
    let callee_feature_names = callee_attrs.target_features.iter().map(|f| f.name);
    let this_feature_names = codegen_fn_attrs.target_features.iter().map(|f| f.name);
    if callee_feature_names.ne(this_feature_names) {
        // In general it is not correct to inline a callee with target features that are a
        // subset of the caller. This is because the callee might contain calls, and the ABI of
        // those calls depends on the target features of the surrounding function. By moving a
        // `Call` terminator from one MIR body to another with more target features, we might
        // change the ABI of that call!
        return Err("incompatible target features");
    }
```

This single conditional exposes **two critical properties** often misunderstood in verification tooling:

1. **Subset rejection (even baseline helpers are rejected):** `rustc` deliberately forbids MIR-level inlining of a baseline helper (`[]`, even if marked `#[inline(always)]`) or an `#[target_feature(enable = "avx")]` helper into an `#[target_feature(enable = "avx2")]` caller, because relocating an internal `Call` terminator from a `Baseline`/`AVX` body into an `AVX2` caller changes the caller feature environment governing `Call` ABI selection (`abi_check` / codegen ABI)!
2. **Ordered sequence comparison (`Iterator::ne`) rather than set equality:** Because `codegen_fn_attrs.target_features` preserves the traversal order from `parse_tf_attribute` + `implied_target_features` without sorting or deduplicating, calling `avx2_bmi1_helper` (`#[target_feature(enable = "avx2,bmi1")]`) from `bmi1_avx2_caller` (`#[target_feature(enable = "bmi1,avx2")]`) yields unequal iterators (`[avx2, avx, ..., bmi1, ...]` vs `[bmi1, ..., avx2, ...]`). Consequently, **MIR `Inline` rejects the call**, even though their semantic feature sets are identical!

#### 2.2 LLVM Backend Superset Inlining + Internal-Call ABI Guard (`X86TTIImpl::areInlineCompatible` & `InlineCost.cpp`)

Once lowered to LLVM IR, inlining is governed by `X86TTIImpl::areInlineCompatible` (`llvm/lib/Target/X86/X86TargetTransformInfo.cpp:6782-6855`) and `llvm::getAttributeBasedInliningDecision` (`llvm/lib/Analysis/InlineCost.cpp:3185-3217`). LLVM uses the orthogonal architecture:

1. **AlwaysInline gate order (`InlineCost.cpp:3203-3217`):** Before checking `Call.hasFnAttr(Attribute::AlwaysInline)`, LLVM executes:
   ```cpp
   if (!IgnoreTTIInlineCompatible &&
       !CalleeTTI.areInlineCompatible(Caller, Callee))
     return InlineResult::failure("conflicting target features");
   ```
   Thus `alwaysinline` **never overrides target-feature incompatibility** in modern LLVM (`22.x` / `23.x` / `main`).
2. **Bitset subset check (`X86TargetTransformInfo.cpp:6794-6799`):** Masking out `InlineIgnoreFeatures`, LLVM checks true bitset inclusion:
   ```cpp
   if ((RealCallerBits & RealCalleeBits) != RealCalleeBits)
     return false;
   ```
   Reordered attributes (`"avx2,bmi1"` vs `"bmi1,avx2"`) normalize to identical `FeatureBitset` bits (`RealCallerBits == RealCalleeBits`), hitting the fast-path `return true` at `L6804-6806` (modulo `useAVX512Regs()` parity).
3. **Relocated `CallBase` ABI compatibility (`X86TargetTransformInfo.cpp:6808-6855`):** When `RealCallerBits` is a *strict* superset of `RealCalleeBits`, LLVM scans every instruction in `Callee`; for any non-inline-asm, non-intrinsic `CallBase` with any non-simple (vector or aggregate) argument or return type, `areTypesABICompatible` checks `CallerTLI->getRegisterTypeForCallingConv(Ctx, CC, VT) == CalleeTLI->getRegisterTypeForCallingConv(Ctx, CC, VT)`. If inlining a baseline helper would shift an internal `<8 x float>` call from split SSE/stack registers into `YMM`, LLVM returns `false` and blocks even subset inlining! Conversely, scalar/ALU calls or intrinsics (`avx_leaf` or `baseline_inline_always_helper` inside `avx2_caller`) pass cleanly and inline.

#### 2.3 Empirical Separation Table (`support/probe_results.json`, Experiment B)

Compiling our 7-function test suite on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` with `-Copt-level=3 -Zdump-mir="Inline | ForceInline" --emit=llvm-ir` (`support/probe_results.json:44-212`) produces an exact separation:

| Caller `->` Callee | Feature Relationship | MIR `ForceInline` (`3-2-003`) | MIR `Inline` (`3-2-004`) | LLVM `-Copt-level=3` IR |
| --- | --- | --- | --- | --- |
| `avx2_calls_avx2_leaf` (`avx2 -> avx2`) | Identical ordered sequence | Not inlined (`avx2_leaf` has `#[inline]`, not `force_inline`) | **Inlined** (`scope 1 (inlined avx2_leaf_helper)`) | **Inlined** (`mul i32 %x, 17; add i32 ..., 5`) |
| `avx2_calls_avx_leaf` (`avx2 -> avx`) | Strict subset (`avx ⊂ avx2`, caller-safe) | **Not inlined** (`_0 = avx_leaf_helper(...)`) | **Not inlined** (`_0 = avx_leaf_helper(...)`) | **Inlined** (`mul i32 %x, 11; add i32 ..., 3`) |
| `bmi1_avx2_calls_avx2_bmi1` (`bmi1,avx2 -> avx2,bmi1`) | Equal sets, reordered attribute list | **Not inlined** | **Not inlined** (`_0 = avx2_bmi1_helper(...)`) | **Inlined** (`mul i32 %x, 23; add i32 ..., 7`) |
| `avx2_calls_baseline_always` (`avx2 -> [] #[inline(always)]`) | Strict subset (`[] ⊂ avx2`) | **Not inlined** (`ForceInline` blocked by `inline.rs:842`) | **Not inlined** | **Inlined** (`xor i32 %x, -1515890086`) |
| `avx2_calls_baseline_inline` (`avx2 -> [] #[inline]`) | Strict subset (`[] ⊂ avx2`) | **Not inlined** | **Not inlined** | **Inlined** (`add i32 %x, 99`) |
| `baseline_calls_avx2_leaf` (`[] -> avx2`, `unsafe`) | Strict superset callee (`avx2 ⊈ []`) | **Not inlined** | **Not inlined** | **Not inlined** (`tail call fastcc @_RNv...avx2_leaf_helper(i32 %x) #4`) |

This establishes empirically that LLVM `areInlineCompatible` is **strictly coarser** than MIR `Inline` on both subset callees and reordered equal sets, while MIR `Inline` refines LLVM on ordered equal lists (because every identical sequence induces equal LLVM `FeatureBitset` and equal `areTypesABICompatible` register types).

---

### 3. Temporal Divergence (`2026-05` / `2026-09` vs. `2026-11`): `#[inline(always)]` + `#[target_feature]` and `<= 128`-Bit SIMD Direct Passing

**Basis:** `source`, `execution`, `derived`.

Comparing primary `rust-lang/rust` snapshots across `14210df0e` (`2026-05-31`, LLVM `22.1.6`), `49d73453` (`2026-09-11`), `3ef0c22cd` (`2026-11-11`, LLVM `23.1.5`), and `277240238` (`main`) reveals **two coordinated backend-safety shifts**:

#### 3.1 `#[inline(always)]` + `#[target_feature]` Relaxation (`#145574` -> LLVM `>= 23` Gate)

In both `14210df0e` (`2026-05-31`) and `49d73453` (`2026-09-11`), `compiler/rustc_codegen_ssa/src/codegen_attrs.rs:432-444` explicitly prohibited `#[inline(always)]` together with `#[target_feature]`:

```rust
// rust-lang/rust@49d73453 — compiler/rustc_codegen_ssa/src/codegen_attrs.rs:432-444
    if !codegen_fn_attrs.target_features.is_empty()
        && matches!(codegen_fn_attrs.inline, InlineAttr::Always)
        && let Some(span) = interesting_spans.inline
    {
        let mut diag = tcx
            .dcx()
            .struct_span_err(span, "cannot use `#[inline(always)]` with `#[target_feature]`");
        diag.note(
            "See this issue for full discussion: \
            https://github.com/rust-lang/rust/issues/145574",
        );
        diag.emit();
    }
```

The comment immediately above (`codegen_attrs.rs:429-431`) specifically cites `rust-lang/rust#116573` and `llvm/llvm-project#70563`, noting that `#[rustc_force_inline]` was exempted only because MIR inlining checked target features whereas LLVM `< 23` `alwaysinline` could bypass backend checks.

In `3ef0c22cd` (`2026-11-11`, LLVM `23.1.5`) and `277240238` (`main`), `codegen_attrs.rs` no longer contains that hard error (`A6` compiles), and `compiler/rustc_codegen_llvm/src/attributes.rs:69-81` introduces an explicit backend LLVM version guard:

```rust
// rust-lang/rust@3ef0c22cd — compiler/rustc_codegen_llvm/src/attributes.rs:69-81
    match inline {
        InlineAttr::Hint => Some(AttributeKind::InlineHint.create_attr(cx.llcx)),
        // LLVM 22 and older may inline a target-featured function into a caller
        // that lacks those features. Keep the function inlineable, but do not force it.
        InlineAttr::Always
            if !codegen_fn_attrs.target_features.is_empty()
                && llvm_util::get_version() < (23, 0, 0) =>
        {
            Some(AttributeKind::InlineHint.create_attr(cx.llcx))
        }
        InlineAttr::Always | InlineAttr::Force { .. } => {
            Some(AttributeKind::AlwaysInline.create_attr(cx.llcx))
        }
```

Notice the defensive two-tier design:
- On `rustc 1.98.0-nightly (14210df0e)` with LLVM `22.1.6`, `support/probe_results.json` (`A6`) confirms compilation still fails with `cannot use #[inline(always)] with #[target_feature]`.
- On `3ef0c22cd` built against LLVM `< 23`, `rustc` compiles cleanly by silently downgrading `InlineAttr::Always` to LLVM `InlineHint` (`inlinehint`), preventing unsound older-LLVM `alwaysinline` hoisting.
- On `3ef0c22cd` built against LLVM `>= 23` (such as `23.1.5`), `rustc` emits LLVM `AttributeKind::AlwaysInline` (`alwaysinline`), relying on `llvm::getAttributeBasedInliningDecision` (`InlineCost.cpp:3203-3217`) calling `CalleeTTI.areInlineCompatible(Caller, Callee)` first — so `+avx2` callers can inline `alwaysinline` `+avx2` callees, while baseline callers fail `areInlineCompatible` and keep an un-inlined call (such as `tail call fastcc` observed for baseline-to-AVX2 calls in `support/probe_results.json`).

#### 3.2 Concatenated Global + Function `"target-features"` Emission (`attributes.rs:450-461`)

A second detail observed directly in both `compiler/rustc_codegen_llvm/src/attributes.rs:450-461` and `support/probe_results.json:350-354` is how LLVM function `"target-features"` attributes are assembled:

```rust
// rust-lang/rust@3ef0c22cd — compiler/rustc_codegen_llvm/src/attributes.rs:450-461
pub(crate) fn target_features_attr<'ll, 'tcx>(
    cx: &SimpleCx<'ll>,
    tcx: TyCtxt<'tcx>,
    function_features: Vec<String>,
) -> Option<&'ll Attribute> {
    let global_features = tcx.sess.global_backend_features.iter().map(String::as_str);
    let function_features = function_features.iter().map(String::as_str);
    let target_features =
        global_features.chain(function_features).intersperse(",").collect::<String>();
    (!target_features.is_empty())
        .then(|| llvm::CreateAttrStringValue(cx.llcx, "target-features", &target_features))
}
```

When `-Ctarget-feature=+avx2` is passed globally on a function that ALSO carries `#[target_feature(enable = "avx2")]`, `probe_results.json:351` directly observes duplicated appended feature flags in LLVM IR:
`"target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3,+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3"`.
Conversely, baseline functions compiled without `-Ctarget-feature` (`attributes #0` / `#2` in `probe_results.json:208,287`) omit `"target-features"` entirely and emit only `"target-cpu"="x86-64"`.

#### 3.3 `extern "Rust"` `<= 128`-Bit SIMD ABI Evolution (`callconv/mod.rs`)

Across the exact same `2026-05` / `2026-09` -> `2026-11` window, `compiler/rustc_target/src/callconv/mod.rs` changed how `extern "Rust"` passes fixed-width `SimdVector` types:

- **In `14210df0e` (`2026-05-31`, line `839-841`) and `49d73453` (`2026-09-11`, line `874-876`):** `adjust_for_rust_abi` checked `if spec.simd_types_indirect { arg.make_indirect(); }` unconditionally for every `BackendRepr::SimdVector`. Live LLVM IR on `1.98.0-nightly` (`support/probe_results.json:230-236`) confirms `__m128` under `extern "Rust"` lowered indirectly via pointer + stack return:
  `define void @_RNvCsh8INqWOoJ6U_5probe14pass_m128_rust(ptr ... sret([16 x i8]) align 16 ..., ptr ... align 16 %v)`.
- **In `3ef0c22cd` (`2026-11-11`, lines `776-789,916-918`):** `adjust_for_rust_abi` introduced `can_pass_simd_directly`:
  ```rust
  // rust-lang/rust@3ef0c22cd — compiler/rustc_target/src/callconv/mod.rs:776-789,916-918
  let can_pass_simd_directly = |arg: &ArgAbi<'_, Ty>| match &spec.arch {
      Arch::X86 if spec.rustc_abi == Some(RustcAbi::X86Sse2) => arg.layout.size.bits() <= 128,
      Arch::X86_64 if spec.rustc_abi != Some(RustcAbi::Softfloat) => {
          arg.layout.size.bits() <= 128
      }
      Arch::AArch64 if spec.rustc_abi != Some(RustcAbi::Softfloat) => {
          arg.layout.size.bits() <= 128
      }
      _ => false,
  };
  ...
  if spec.simd_types_indirect && !can_pass_simd_directly(arg) {
      arg.make_indirect();
  }
  ```
  Because non-softfloat `x86_64` guarantees `sse2` globally in `abi_required_features`, `<= 128`-bit SIMD vectors (`__m128`) are now passed directly (`PassMode::Direct`), whereas `> 128`-bit vectors (`__m256`, `__m512`) continue using `PassMode::Indirect` (`sret([32 x i8]) align 32`, `sret([64 x i8]) align 64`) regardless of per-function `#[target_feature]`.

---

### 4. SIMD Vector Register ABI Lowering, `AbiErrorDisabledVectorType`, and Unmonomorphized `rlib` Deferment

**Basis:** `source`, `execution`, `derived`.

#### 4.1 System V AMD64 `PassMode::Cast` and `Reg::opaque_vector` Lowering

Under non-rustic ABIs such as `extern "C"`, `compiler/rustc_target/src/callconv/x86_64.rs` classifies `BackendRepr::SimdVector` (both raw `__m128`/`__m256`/`__m512` and `#[repr(C)]` single-field aggregates like `struct Wrap256(__m256)`) inside `classify_arg` (`x86_64.rs:82,127-136`):

- All eightbytes up to `MAX_EIGHTBYTES = 512 / 64 = 8` are filled with `[Some(Class::Sse), Some(Class::SseUp), ...]`.
- `reg_component` (`x86_64.rs:176-188`) merges contiguous `[Class::Sse, Class::SseUp*]` chunks when `vec_len > 1` into `Reg::opaque_vector(Size::from_bytes(8) * (vec_len as u64))`. Note that for an aggregate wrapping `__m256`, `arg.layout.is_aggregate()` is `true` and `classify` descends into the field's `SimdVector`, yielding `PassMode::Cast` with `RegKind::Vector { hint_vector_elem: Primitive::Int(Integer::I8, false) }` (because `Reg::opaque_vector` defaults to `i8` element hint) whereas raw `__m256` keeps `RegKind::Vector` with `Float::F32` hint (`x86_64.rs:293-295`, `rustc_codegen_llvm/src/abi.rs:152-179`).
- This explains the exact empirical LLVM signatures in `support/probe_results.json:238-262,395-400`:
  - `pass_m128_baseline(__m128)` -> `<4 x float>`
  - `pass_m256_avx2(__m256)` -> `<8 x float>`
  - `pass_wrap256_avx(Wrap256)` -> `<32 x i8>` (still `RegKind::Vector`, not scalar integers!)
  - `pass_m512_avx512f(__m512)` -> `<16 x float>`

#### 4.2 Monomorphization-Time `AbiErrorDisabledVectorType` and Rustic Call-Site Asymmetry

Before codegen emits LLVM IR, `compiler/rustc_monomorphize/src/mono_checks/abi_check.rs` validates vector ABI register compatibility in `do_check_simd_vector_abi` (`abi_check.rs:54-127`):

```rust
// rust-lang/rust@3ef0c22cd — compiler/rustc_monomorphize/src/mono_checks/abi_check.rs:69-104
        match passes_vectors_by_value(&arg_abi.mode, &arg_abi.layout.backend_repr) {
            UsesVectorRegisters::FixedVector => {
                let unit_size = match &arg_abi.mode {
                    PassMode::Cast { pad_i32_count: _, cast } if cast.prefix.is_empty() => {
                        cast.rest.unit.size
                    }
                    _ => size,
                };

                let feature_def = tcx.sess.target.features_for_correct_fixed_length_vector_abi();
                let feature = match feature_def.iter().find(|(bits, _)| unit_size.bits() <= *bits) { ... };
                if !feature.is_empty() && !have_feature(Symbol::intern(feature)) {
                    ...
                    tcx.dcx().emit_err(diagnostics::AbiErrorDisabledVectorType { ... });
                }
            }
```

On x86/x86-64, `features_for_correct_fixed_length_vector_abi()` returns `X86_FEATURES_FOR_CORRECT_FIXED_LENGTH_VECTOR_ABI = &[(128, "sse"), (256, "avx"), (512, "avx512f")]` (`target_features.rs:1172-1173`). Notice two critical boundary details:

1. **Minimal ABI feature vs. arithmetic feature:** Passing `Wrap256` (`256` bits, `<32 x i8>`) in `extern "C"` requires only `"avx"` (`unit_size.bits() <= 256`), **not** `"avx2"` (`pass_wrap256_avx` compiles cleanly with `#[target_feature(enable = "avx")]` in `probe_results.json:252,289`). Passing `__m512` with only `"avx2"` fails with `requires the avx512f target feature` (`m512_avx2_only_rejected`, `rc=1`).
2. **Call-site check skips rustic ABIs (`abi_check.rs:171-226`) + uninstantiated `rlib` deferment (`probe_results.json:360-370`):**
   - `check_instance_abi` checks both rustic and non-rustic definition sites (necessary for types like scalable vectors or target overrides).
   - `check_call_site_abi` returns early if `extern_abi.is_rustic_abi() || extern_abi == ExternAbi::LlvmIntrinsic` (`abi_check.rs:217-226`), explicitly flagged with `FIXME(#161753)` as potentially unsound for scalable vectors under Rust ABI, though sound on `x86_64` fixed-width vectors because `> 128`-bit `extern "Rust"` vectors pass indirectly via `sret` and `<= 128`-bit vectors only require baseline `sse2`.
   - Because `check_feature_dependent_abi` runs over monomorphized CGU instances, compiling `pub extern "C" fn bad_uninstantiated_m512(v: __m512) -> __m512 { v }` inside `--crate-type=lib` *without* `#[no_mangle]`, `#[inline(never)]`, or a local caller succeeds with `rc=0` and empty LLVM IR (`rlib_uninstantiated_m512_deferred`, `probe_results.json:360-370`) — deferring `AbiErrorDisabledVectorType` until a downstream crate instantiates or re-exports it!

#### 4.3 Empirical Vector ABI Matrix (`support/probe_results.json`, Experiment C)

| Test Case | Flag / Attribute Configuration | Result | Lowered Signature / Error |
| --- | --- | --- | --- |
| `default_baseline_sse2_extern_c_rejected` | Baseline `[sse, sse2]`: `pass_m256_baseline`, `pass_wrap256_baseline`, `caller_baseline_calls_avx2_m256` | `rc=1` (4 errors) | `AbiErrorDisabledVectorType`: requires `avx` on 3 definitions + 1 call site (`unsafe { pass_m256_avx2(v) }`) |
| `pass_m128_baseline` (`extern "C"`) | Baseline `[sse, sse2]` | `rc=0` | `define <4 x float> @...(<4 x float> returned %v)` |
| `pass_m256_avx2` (`extern "C"`) | `#[target_feature(enable = "avx2")]` | `rc=0` | `define <8 x float> @...(<8 x float> returned %v)` (`attributes #1` adds `+avx,+avx2,...`) |
| `pass_wrap256_avx` (`extern "C"`) | `#[target_feature(enable = "avx")]` on `#[repr(C)] struct Wrap256(__m256)` | `rc=0` | `define <32 x i8> @...(<32 x i8> returned %0)` (`PassMode::Cast` via `Reg::opaque_vector`) |
| `pass_m256_rust` / `pass_m256_rust_avx2` / `caller_baseline_rust_calls_avx2_rust` | `extern "Rust"` across baseline <-> `avx2` boundary | `rc=0` | `define void @...(ptr ... sret([32 x i8]) align 32 %_0, ptr ... align 32 %v)`; caller allocates `alloca [32 x i8], align 32` |
| `pass_m128_rust` (`extern "Rust"`, `1.98.0-nightly`) | `14210df0e` (`simd_types_indirect` unconditional) | `rc=0` | `define void @...(ptr ... sret([16 x i8]) align 16 %_0, ptr ... align 16 %v)` (changed to direct in `3ef0c22cd` via `can_pass_simd_directly`) |
| `global_avx2_target_feature_flag` | `-Ctarget-feature=+avx2` | `rc=0` | `pass_m256_baseline` compiles and lowers to `<8 x float>`; `pass_m256_rust` stays `sret([32 x i8]) align 32` |
| `m512_avx2_only_rejected` | `#[target_feature(enable = "avx2")] pub extern "C" fn(__m512)` | `rc=1` | `requires the avx512f target feature, which is not enabled` |
| `pass_m512_avx512f` vs `pass_m512_rust` | `#[target_feature(enable = "avx512f")] extern "C"` vs `extern "Rust"` | `rc=0` | `extern "C"` -> `<16 x float>`; `extern "Rust"` -> `sret([64 x i8]) align 64` |
| `rlib_uninstantiated_m512_deferred` | `--crate-type=lib` with `pub extern "C" fn(__m512)` (no `#[no_mangle]`, no `#[inline(never)]`, no caller) | `rc=0` | Empty LLVM IR (`defines = {}`), proving monomorphization-gated checking |

---

### 5. Mechanized Lean `v4.34.1` Formalization (`TargetFeatureInliningBoundaryAndSimdAbiSoundness.lean`)

**Basis:** `source`, `execution`, `derived`.

To verify these interacting invariants mathematically, `support/TargetFeatureInliningBoundaryAndSimdAbiSoundness.lean` (`2,332` lines, `605` Lean declarations) formalizes:

1. **ISA capability lattice (`Section 1`):** `Feature` (14 representative x86-64 features: `sse`, `sse2`, `sse3`, `ssse3`, `sse41`, `sse42`, `avx`, `avx2`, `bmi1`, `fma`, `f16c`, `avx512f`, `aes`, `pclmulqdq`), ordered list equality `SeqEqFeats` (`seqEqFeatsB`, mirroring `Iterator::ne` in `inline.rs:842`), set inclusion `SubsetFeats` / `SetEqFeats`, and deduplicating bounded transitive implication closure `impliedClosure` (`expandImpliedFuel 10`, with `mem_self_expandStep`, `expandStep_monotone`, `impliedClosure_monotone`, `impliedClosure_extensive`). Constructive theorem `mirSeqEq_strictly_stronger_than_setEq` proves `[.avx2, .bmi1]` and `[.bmi1, .avx2]` are `SetEqFeats` yet `seqEqFeatsB = false`.
2. **SIMD ABI lowering (`Section 2`):** `VecTy` (`m128`, `m256`, `m512`, `wrap256`), `AbiConv` (`externRust`, `externC`), `TargetSpec` (`x86_64Spec2026_09` with `rustSimdPassDirect128 := false` vs. `x86_64Spec2026_11` with `rustSimdPassDirect128 := true`), `passModeFor`, `regClassFor` (modeling `Reg::opaque_vector`, `<4/8/16 x float>`, `<32 x i8>`, `splitOrStack`, and `memPtr`), `regClassHardwareReq`, `abiCheckSide`, and register-match + hardware-legality predicates (`CallAbiMatch`, `RegHardwareLegal`).
3. **Operational semantics and static discipline (`Sections 3-4`):** Non-nested structured `Inst` AST (`nop`, `alu`, `vecOp`, `safeCall`, `unsafeCall`, `reifySafeFnPtr`, `reifyUnsafeFnPtr`, `abiCall`, `seq`, `guardedBranch`), separating `headerFeats` (static `#[target_feature]`) from `branchFeats` (runtime `is_x86_feature_detected!` capability guards) in `InstWellTyped` and `SafeTf11Typed`, parametrized by `AttrPolicy` (`policy2026_09` rejecting `#[inline(always)]` + `#[target_feature]` vs. `policy2026_11` permitting it). Notice that in `validTf11Prog`, `guardedMainFn` guards its `unsafeCall` with `impliedClosure [.avx2]` — modeling that runtime AVX2 CPUID detection simultaneously enables all x86 features implied by AVX2 (`sse3..avx`).

#### 5.1 Theorem Inventory Verified by the Lean `v4.34.1` Kernel

| Theorem Name | Mathematical Statement & Proof Meaning | Axioms Used |
| --- | --- | --- |
| `passModeCast_safe_iff_vector_feature_both_sides` | Under `extern "C"`, `CallAbiMatch` holds AND `caller`'s `regClassFor` does not split (`≠ splitOrStack _`) AND `RegHardwareLegal` holds on `cpu` iff `vecRequiredFeature v` is in `callerFeats`, `calleeFeats`, and `cpu`. | `[propext]` |
| `abiCheckExternC_sound_and_complete` | `abi_check` succeeding on both sides of an `extern "C"` call (`abiCheckSide = true ∧ abiCheckSide = true`) is both necessary and sufficient for register-class agreement, non-splitting, and hardware legality. | `[propext]` |
| `evalInsts_no_sigill_or_abi_fault` | Inductive progress/preservation over `(fuel, Inst)`: well-typed bodies never return `.fault .sigill`, `.fault .abiMismatch`, or `.fault .missingCallee` on CPUs supporting `headerFeats ++ branchFeats`. | `[propext]` |
| `superset_inline_splice_preserves_well_typed` | Splicing a `callee.body` whose `callee.effectiveFeats ⊆ headerFeats` into `(headerFeats, branchFeats)` preserves `InstsWellTyped` (covering both `vecOp` and safe calls/coercions). | `[propext]` |
| `inlineProgramStep_preserves_safe_tf11` | Single-step LLVM-style superset inlining (`callee.effectiveFeats ⊆ caller.effectiveFeats`) on any `safeCall`/`unsafeCall` preserves whole-program `SafeTf11Typed`. | `[propext]` |
| `sigill_freedom_under_safe_tf11_and_superset_inline` | **Theorem 1:** For any finite sequence `inlineSteps` applied via `foldl inlineProgramStep` to a `SafeTf11Typed` program, execution at any `fuel` on any baseline CPU never faults with `.sigill` or `.abiMismatch`. | `[propext]` |
| `baseline_caller_inlining_violates_sigill_freedom` | **Theorem 2:** Concrete counterexample: `validTf11Prog` executes cleanly to `.ok 2` on baseline `[.sse, .sse2]`, whereas unsafely hoisting `avx2LeafFn.body` into baseline `guardedMainFn` (`unsoundlyInlinedProg`) violates `InstsWellTyped` and faults with `.fault .sigill`. | `[propext]` |
| `mir_inline_refines_llvm_subset_inline` | **Theorem 3:** If `EffectiveFeatsConsistent` holds and `mirCanInline caller callee = true` (`SeqEqFeats`), then `llvmCanInline spec caller callee = true` (even when `callee.body` contains ABI-sensitive vector calls!). | `[propext]` |
| `llvm_strictly_coarser_than_mir_three_witnesses` | Three constructive witnesses where MIR `Inline` refuses (`false`) yet LLVM `areInlineCompatible` admits (`true`): `avx ⊂ avx2`, `[] ⊂ avx2` (`#[inline(always)]`), and reordered equal sets `"[avx2, bmi1]"` vs `"[bmi1, avx2]"`. | `[propext]` |
| `llvm_2026_11_alwaysinline_subset_gate` | Models LLVM 23 gate order (`InlineCost.cpp:3203-3217`): `tfInlineAlwaysFn` (`avx2` + `#[inline(always)]`) has `llvmCanInline = true` into `avx2CallerFn` and `false` into baseline `guardedMainFn`. | `[propext]` |
| `llvm_rejects_abi_shifting_subset_inline` | Mechanizes `inline.rs:843-847` and `X86TTIImpl::areTypesABICompatible`: `baselineAbiSensitiveHelperFn` (`[]` with `.abiCall .externC .m256`) satisfies `SubsetFeats` into `avx2CallerFn`, yet `allInternalCallsAbiCompat = false`, blocking `llvmCanInline` (`false`). | `[propext]` |
| `validTf11Prog_is_well_typed` | Concrete constructive proof that the 7-function `validTf11Prog` (modeling `A1` + `B`) satisfies `SafeTf11Typed x86_64Spec2026_11 policy2026_11`. | `[propext]` |
| `e0133_baseline_safe_call_avx2_rejected` | Baseline caller safely invoking `avx2LeafFn` without `unsafe` is rejected (`E0133` analogue). | `[propext]` |
| `e0308_baseline_safe_fn_ptr_coercion_rejected` | Baseline caller coercing `avx2LeafFn` to a safe `fn` pointer is rejected (`E0308` analogue). | `[propext]` |
| `non_subset_sse42_calls_avx2_rejected` | `sse4.2` caller safely calling `avx2LeafFn` (`avx2 ⊈ sse4.2`) is rejected. | `[propext]` |
| `trait_and_main_target_feature_rejected` | Safe `#[target_feature]` rejects `isMain = true` and `isTraitSafe = true` under `AttrValid`. | `[]` |
| `attr_policy_2026_09_rejects_inline_always_2026_11_accepts` | `policy2026_09` rejects `#[inline(always)]` + `avx2`, whereas `policy2026_11` permits it. | `[]` |

#### 5.2 Mechanization Purity Guarantees and Verification Design for Anneal

Per Anneal's Trusted Computing Base (`Trusted/MirSemantics.lean:1568`, where interprocedural `.call` terminators currently fault `.unsupported` prior to full call-stack / cross-feature integration):

1. **Kernel purity:** All `605` Lean constants in `TargetFeatureInliningAndSimdAbi` were checked post-compilation via Lean `MetaM` (`Lean.collectAxioms` and `Environment.constants`), yielding `unsafeCount = 0`, `unsafeRecCount = 0`, `forbiddenAxiomHits = 0` (`Classical.choice = 0`, `sorryAx = 0`, `Lean.ofReduceBool = 0`, `Lean.reduceBool = 0`, `Lean.trustCompiler = 0`), with `propextCount = 180` and `quotSoundCount = 0`. Every `def` uses explicit `noncomputable def`, `Inst` avoids nested inductives (`seq` + single-`Inst` `guardedBranch` rather than nested `List Inst`), and zero `deriving` / `omega` / `bv_decide` / `native_decide` / `partial` constructs appear.
2. **Consequence for Verified MIR Splicing in Anneal:** If Anneal extends `Trusted.MirSemantics` beyond single-body MIR to sound cross-function call splicing (cf. sibling report `anneal-trusted-mir-interprocedural-call-stack-and-mir-inline-splicing`), any sound MIR-level inline pass matching `rustc` must enforce **`callee.target_features == caller.target_features` sequence equality** when copying MIR `Call` terminators verbatim (`mir_inline_refines_llvm_subset_inline`), or else prove call-ABI invariance (`allInternalCallsAbiCompat`) alongside `callee.effectiveFeats ⊆ caller.effectiveFeats` as modeled in `superset_inline_splice_preserves_well_typed`. Ignoring target features when splicing MIR bodies admits `baseline_caller_inlining_violates_sigill_freedom`!

---

## Boundaries

**Basis:** `source`, `execution`, `derived`.

1. **Toolchain Execution vs. Source Coverage Gap:** All empirical artifacts in `support/probe_results.json` were freshly executed on `rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65, 2026-05-31)` linked against `LLVM 22.1.6`. Changes landing between `49d734536222bf28bb6d07d885b3a81d145981da` (`2026-09-11`) and `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`2026-11-11`, `LLVM 23.1.5`) / `277240238554297f93fa9ee3c7643dfa03ccbbb4` (`main`) — specifically removing `#145574`, adding `llvm_util::get_version() < (23, 0, 0)` downgrade in `attributes.rs:73-78`, and enabling `can_pass_simd_directly` in `callconv/mod.rs:776-789` — are established directly from upstream primary source inspection and diff audit rather than local binary re-execution of `1.102.0-nightly` in this sandbox.
2. **ISA, ABI, and Feature Coverage:** Empirical probes and the Lean formalization cover `x86_64-unknown-linux-gnu` fixed-width vectors (`__m128`, `__m256`, `#[repr(C)]` `Wrap256`, `__m512`) under `extern "C"` and `extern "Rust"`. Non-x86 architectures (`aarch64`, `wasm*`, `riscv`), `vectorcall` (`AbiRequiredTargetFeature { sse2 }` in `abi_check.rs:129-137`), multi-field mixed int/SSE aggregates (`x86_64.rs:200-212`), global `-Ctarget-cpu` overrides, `avx512bw`/`avx10` width interactions, scalable vectors (`SVE`/`RVV`), and `asm!` constraints (`asm_target_features` in `target_features.rs:154-172`) were inspected only selectively or excluded from execution (`not examined`).
3. **Formal Model Idealizations:** The Lean development (`support/TargetFeatureInliningBoundaryAndSimdAbiSoundness.lean`) models a structured single-crate instruction AST (`Inst` + `List Inst`) with 14 representative x86 features and explicit `fuel`-bounded execution rather than arbitrary unstructured MIR basic-block CFGs, LLVM `InlineCost` heuristics, cross-crate generic monomorphization reachability, or machine-code register allocation. Runtime `is_x86_feature_detected!` guards are modeled cleanly as `guardedBranch (impliedClosure [...])`, reflecting hardware-implied capabilities; verifying that actual `cpuid` detection code matches hardware semantics lies outside the compiler-model boundary.

---

## Evidence

**Basis:** `source`, `execution`, `derived`.

### Primary Source Artifacts Audited

- **`rust-lang/rust` revisions:**
  - `main` (`277240238554297f93fa9ee3c7643dfa03ccbbb4`)
  - `1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `2026-11-11`)
  - Nightly pre-`#145574` relaxation (`49d734536222bf28bb6d07d885b3a81d145981da`, `2026-09-11`)
  - Live probe toolchain `1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `2026-05-31`)
- **Key compiler files & lines inspected:**
  - `compiler/rustc_attr_parsing/src/attributes/codegen_attrs.rs:544-625` (`parse_tf_attribute`, `TargetFeatureParser`, `ALLOWED_TARGETS`, `finalize_check`)
  - `compiler/rustc_codegen_ssa/src/codegen_attrs.rs:118-161,404-417` (`3ef0c22cd` — `safe_target_features`, closure inheritance & `CoroutineKind::Desugared` exception) and `49d73453` lines `432-444` (`cannot use #[inline(always)] with #[target_feature]`, `#145574`)
  - `compiler/rustc_codegen_ssa/src/target_features.rs:88-186` (`from_target_feature_attr`, `implied_target_features`, `check_target_feature_trait_unsafe`)
  - `compiler/rustc_hir_analysis/src/check/entry.rs:108-114` (`TargetFeatureOnMain`)
  - `compiler/rustc_mir_build/src/check_unsafety.rs:412-458` (`CallToFunctionWith` via `is_target_feature_call_safe`)
  - `compiler/rustc_middle/src/ty/context.rs:1326-1358` (`is_target_feature_call_safe`, `adjust_target_feature_sig`)
  - `compiler/rustc_hir_typeck/src/coercion.rs:1306-1333` & `compiler/rustc_borrowck/src/type_check/mod.rs:1036-1061` (`TypeError::TargetFeatureCast`, `PointerCoercion::ReifyFnPointer`)
  - `compiler/rustc_mir_transform/src/inline.rs:803-852` (`check_codegen_attributes`, `callee_feature_names.ne(this_feature_names)`)
  - `compiler/rustc_codegen_llvm/src/attributes.rs:51-91,450-461` (`inline_attr` LLVM `< (23, 0, 0)` downgrade to `InlineHint` vs `AlwaysInline`, `target_features_attr` global+function chaining)
  - `compiler/rustc_monomorphize/src/mono_checks/abi_check.rs:25-138,171-323` (`passes_vectors_by_value`, `do_check_simd_vector_abi`, `check_instance_abi`, `check_call_site_abi` skipping rustic ABIs)
  - `compiler/rustc_target/src/target_features.rs:1172-1173` (`X86_FEATURES_FOR_CORRECT_FIXED_LENGTH_VECTOR_ABI`)
  - `compiler/rustc_target/src/callconv/mod.rs`: `14210df0e:819-842`, `49d73453:854-878` (unconditional `arg.make_indirect()`), vs. `3ef0c22cd:776-789,900-919` (`can_pass_simd_directly` `<= 128`-bit direct pass)
  - `compiler/rustc_target/src/callconv/x86_64.rs:47-160,176-212,276-295` & `compiler/rustc_codegen_llvm/src/abi.rs:152-220` (`Class::Sse`/`Class::SseUp`, `Reg::opaque_vector`, `CastTarget::llvm_type`)
- **`llvm-project` revisions:**
  - `rust-lang/llvm-project` `0a5579eb649d3634a9c30ac873300cc2944fa070` (`LLVM 23.1.5` submodule of `3ef0c22cd`), `08c84e69a84d95936296dfcab0e38b34100725d5` (`LLVM 22.1.6` submodule of `14210df0e`), and `llvm/llvm-project` `970a1b012bacd479f450604d34faa52f5ccce5d6` (`main`)
  - `llvm/lib/Target/X86/X86TargetTransformInfo.cpp:6782-6855` (`X86TTIImpl::areInlineCompatible`, `areTypesABICompatible`)
  - `llvm/lib/Analysis/InlineCost.cpp:3185-3217` (`getAttributeBasedInliningDecision`, checking `!CalleeTTI.areInlineCompatible(Caller, Callee)` prior to `Attribute::AlwaysInline`)
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
  - `trusted/lean/Trusted/MirSemantics.lean:1568` (`.call` -> `.fault .unsupported`)

### Package Support Files

- [`support/probe_target_feature_inlining_simd_abi.py`](support/probe_target_feature_inlining_simd_abi.py): Standalone hermetic Python driver executing `rustc` probes `A1`-`A6`, `B` (MIR `-Zdump-mir=Inline | ForceInline` + LLVM IR), and `C` (SIMD vector ABI across `extern "C"` / `extern "Rust"`, `Wrap256`, `__m128`/`__m256`/`__m512`, and `rlib` deferment) inside `tempfile.TemporaryDirectory()`.
- [`support/probe_results.json`](support/probe_results.json): Verbatim JSON output captured live on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `LLVM 22.1.6` (`410` lines).
- [`support/TargetFeatureInliningBoundaryAndSimdAbiSoundness.lean`](support/TargetFeatureInliningBoundaryAndSimdAbiSoundness.lean): Self-contained `2,332`-line Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) formalization compiling with `0` errors and `0` warnings under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`; MetaM scan confirms `totalDecls=605`, `unsafeCount=0`, `unsafeRecCount=0`, `forbiddenAxiomHits=0`, `propextCount=180`, `quotSoundCount=0`.

---

## Revalidation

**Basis:** `source`, `execution`.

All empirical checks, upstream SHA pins, Lean proofs, and corpus structural checks can be reproduced independently:

### 1. Re-run Live `rustc` Probes

```bash
TD="$(mktemp -d)"
python3 reports/rustc-target-feature-1-1-cross-feature-inlining-boundary-and-simd-abi/support/probe_target_feature_inlining_simd_abi.py \
  --rustc rustc \
  --out "$TD/reval_probe_results.json"
diff -u reports/rustc-target-feature-1-1-cross-feature-inlining-boundary-and-simd-abi/support/probe_results.json "$TD/reval_probe_results.json"
rm -rf "$TD"
```

Note: When run on `rustc >= 2026-10` / LLVM `>= 23`, probe `A6` (`inline_always_with_target_feature_probe`) will transition from `compile_returncode: 1` (`#145574`) to `compile_returncode: 0` and `pass_m128_rust` in `C` will lower directly rather than via `sret([16 x i8])`.

### 2. Re-verify Lean `v4.34.1` Kernel Check & Zero-Axiom Hygiene

```bash
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  reports/rustc-target-feature-1-1-cross-feature-inlining-boundary-and-simd-abi/support/TargetFeatureInliningBoundaryAndSimdAbiSoundness.lean

grep -En 'sorry|Classical|omega|bv_decide|native_decide|partial def|noncomputable section|deriving' \
  reports/rustc-target-feature-1-1-cross-feature-inlining-boundary-and-simd-abi/support/TargetFeatureInliningBoundaryAndSimdAbiSoundness.lean
```

(Only explanatory comments in header/documentation match any excluded keywords; zero executable uses exist, and compiling with `olean` + MetaM `Lean.collectAxioms` confirms `0` `Classical.choice`, `0` `sorryAx`, `0` `ofReduceBool`, and `0` `._unsafe_rec` across all `605` declarations.)

### 3. Re-verify Upstream Commit Pins

```bash
gh api repos/rust-lang/rust/commits/277240238554297f93fa9ee3c7643dfa03ccbbb4 --jq .sha
gh api repos/rust-lang/rust/commits/3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1 --jq .sha
gh api repos/rust-lang/rust/commits/49d734536222bf28bb6d07d885b3a81d145981da --jq .sha
gh api repos/rust-lang/rust/commits/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65 --jq .sha
gh api repos/llvm/llvm-project/commits/970a1b012bacd479f450604d34faa52f5ccce5d6 --jq .sha
gh api repos/joshlf/anneal/commits/c131b320eeeb26ef692e5afd5ec8db49ee518613 --jq .sha
```

### 4. Re-validate Corpus Schema and Catalog

```bash
python3 tools/reference.py catalog
python3 tools/reference.py check
```
