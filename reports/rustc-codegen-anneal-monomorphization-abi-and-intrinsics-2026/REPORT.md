# `rustc_codegen_anneal`: Post-Cleanup MIR Extraction, Monomorphization, `FnAbi`/`PassMode` Marshaling, and Intrinsic Taxonomy

## Summary

Anneal's verification architecture (`trusted/rustc-capture/src/lib.rs` and
`trusted/lean/Trusted/MirSemantics.lean`) promises to verify Rust programs
against `MirPhase::Runtime(RuntimePhase::PostCleanup)` MIR and compose those
proofs with a verified backend (`rustc_codegen_anneal`). Our source audit of
`rustc` (`compiler/rustc_mir_transform`, `rustc_monomorphize`, `rustc_metadata`,
`rustc_ty_utils`, `rustc_abi`, `rustc_target`, `rustc_codegen_ssa`,
`rustc_codegen_cranelift`, and `library/{core,alloc}`) and our Lean 4.34.1
mechanizations in `support/track1_abi_and_mono_probe.lean` (1,642 lines) and
`support/round2_track1_probe.lean` (877 lines) establish seven foundational
results for `rustc_codegen_anneal`:

1. **`--emit=mir` Phase Mismatch & `Steal<Body>` Lifecycle Contract:**
   `trusted/rustc-capture/src/lib.rs:9-19, 621-633` invokes `rustc --emit=mir`
   without `-Zmir-opt-level=0`. In `rustc`, `--emit=mir` calls
   `tcx.instance_mir(InstanceKind::Item(def_id))` $\to$
   `tcx.optimized_mir(def_id)`, which defaults to `mir_opt_level = 1` under
   `OptLevel::No` (`compiler/rustc_session/src/config.rs:123-128`) and emits
   `MirPhase::Runtime(RuntimePhase::Optimized)` rather than `PostCleanup`.
   Conversely, a `CodegenBackend` cannot naively borrow
   `tcx.mir_drops_elaborated_and_const_checked(def_id)` because (a)
   `tcx.collect_and_partition_mono_items(())` steals that `Steal<Body>` slot
   inside `inner_optimized_mir`, (b) cross-crate `.rmeta` files encode only
   `optimized_mir` and `mir_for_ctfe`, and (c) `inner_optimized_mir` runs
   mandatory pre-codegen steps (`remap_mir_for_const_eval_select`,
   `inline::ForceInline`, and `MentionedItems`). Compiling both the sysroot and
   target crates with `-Copt-level=0 -Cpanic=abort -Zmir-opt-level=0
   -Zvalidate-mir=yes -Zmir-preserve-ub -Zalways-encode-mir=yes
   -Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums,-RemoveUnneededDrops`
   makes `tcx.optimized_mir(def_id)` statement-for-statement identical to
   `PostCleanup` MIR modulo `const_eval_select` remapping and
   `#[rustc_force_inline]` expansion.
2. **The `deduced_param_attrs` `ReadOnly` Phase-Mismatch Soundness Bug:**
   `rustc` has no `-Zdeduce-param-attrs` CLI flag; `tcx.deduced_param_attrs`
   (`compiler/rustc_mir_transform/src/deduce_param_attrs.rs:177-242`) runs
   whenever `tcx.sess.opts.optimize != OptLevel::No &&
   tcx.sess.opts.incremental.is_none()`. If an optimized MIR body eliminates a
   dead store to a `PassMode::Indirect` parameter `_1`, `deduced_param_attrs`
   attaches `ArgAttribute::ReadOnly` in `fn_abi_of_instance`, causing callers to
   elide their scratch stack copy. If codegen then lowers the unoptimized
   `PostCleanup` MIR body (where the dead store to `_1` still executes), the
   callee overwrites the caller's live local in-place! We mechanize this bug as
   a negative refinement canary (`Anneal.deduced_readonly_phase_mismatch_unsound`
   in `support/track1_abi_and_mono_probe.lean`). `rustc_codegen_anneal` must
   both enforce `-Copt-level=0` and query
   `tcx.fn_abi_of_instance_no_deduced_attrs`.
3. **Complete Classification of All 264 `#[rustc_intrinsic]` Declarations and
   the 38/49 Floating-Point Intrinsics:**
   We classify all 264 `#[rustc_intrinsic]` items across `core` and `alloc` into
   four lifecycle groups—27 compile-time-only (`#[rustc_comptime]` / reflection)
   intrinsics, 32 intrinsics lowered before codegen to native MIR constructs by
   `rustc_mir_build`, `LowerIntrinsics`, and `remap_mir_for_const_eval_select`,
   67 intrinsics with Rust fallback bodies (`!must_be_overridden`), and 138
   bodyless intrinsics (`must_be_overridden == true`, partitioned into 37
   mandatory `#![no_std]` primitives, 18 concurrency/unwinding primitives, 11
   float fast/algebraic/cast intrinsics, and 72 rejected SIMD/GPU/autodiff/variadic
   intrinsics). For the 38 floating-point intrinsics with fallback bodies (49
   total including the 11 bodyless float intrinsics), placing the **22 Category
   A** pure-Rust bit-manipulation and IEEE 754 comparison intrinsics (`fmuladd`,
   `fabs`, `copysignf*`, `minimum*`, `maximum*`) into
   `CodegenBackendInit::fallback_intrinsics` inlines them into verified pure MIR
   (`fabsBits64_spec`, `copysignBits64_spec`), while placing the **16 Category
   B/C** `intrinsic_dispatch_on_type!` intrinsics (`sqrt`, `fma`, `floor`,
   `ceil`, `trunc`, `round_ties_even`, `round`, `powi`, `sin`, `cos`, `powf`,
   `exp`, `exp2`, `log`, `log10`, `log2`) into `replaced_intrinsics` prevents
   `rustc_monomorphize` from emitting unverified `extern "C"` `libm` calls.
4. **Direct MIR-to-SSA (`CValue`/`CPlace`) and `FnAbi`/`PassMode` Marshaling:**
   Following `rustc_codegen_cranelift` (`cg_clif`), `rustc_codegen_anneal` can
   reuse `rustc_codegen_ssa::base::codegen_crate` by implementing only
   `CodegenBackend`, `ExtraBackendMethods`, and `WriteBackendMethods` without
   touching `rustc_codegen_ssa::mir` or `BuilderMethods`. We mechanize `CValue`,
   `CPlace`, `PassMode` (`Ignore`, `Direct`, `Pair`, `Cast`, `Indirect`),
   `FnAbi`, `InstanceKind::DropGlue(_, None)` elision, and `ExternAbi::RustCall`
   `spread_arg` tuple unpacking in `support/track1_abi_and_mono_probe.lean`,
   proving `cplace_write_read_roundtrip`, `abi_call_marshaling_refines`,
   `caller_callee_mutate_verified`, `empty_drop_shim_refines`,
   `rust_call_spread_arg_refines`, and the negative canary
   `buggy_indirect_without_caller_copy_unsound`.
5. **Exact `PassMode::Cast` Layout Rules Across `x86_64`, `aarch64`, and
   `riscv64` & Verified `MaskedWord` + `freezeMaskedWord` Lowering:**
   Under both `ExternAbi::Rust` (`adjust_for_rust_abi`, which casts
   `BackendRepr::Memory` aggregates of size $\le 8$ bytes to integer registers
   via `cast_to_maybe_noundef`) and foreign `extern "C"` ABIs on `x86_64` SysV,
   `aarch64` AAPCS64, and `riscv64` LP64D (which classify both
   `BackendRepr::ScalarPair` and `BackendRepr::Memory` as aggregates and pack
   aggregates $\le 16$ bytes via `PassMode::Cast`), whole-word integer loads
   (`load i64`) across uninitialized padding bytes trigger whole-word `poison`
   in `Vellvm`/`Alive2`. Modeling cast words as `MaskedWord := { bits : BitVec
   64, initMask : BitVec 64 }` and applying per-bit `freezeMaskedWord` at the
   lowering boundary satisfies `Trusted.Compiles` (`passModeCast_freeze_compiles`)
   and `Trusted.Compiler.Verified` (`passModeCast_freeze_verified`), whereas
   omitting `freeze` refutes `Compiles` (`canary_whole_word_poison_on_padding_unsound`).
6. **Byte-Offset-Dispatched `BackendRepr::ScalarPair` and Sub-Word Niche
   Extraction:**
   In `rustc_abi::LayoutData::compute`, a niche-encoded `ScalarPair` enum always
   sets `tag_field := FieldIdx::new(0)` with `FieldsShape::Arbitrary { offsets:
   [niche_offset] }`, even when the niche resides in the second scalar
   (`niche_offset = b_offset > 0`). Dispatching `ScalarPair` projections by raw
   `FieldIdx` (as `rustc_codegen_cranelift` does in `value_and_place.rs:182-193`)
   reads `fst` instead of `snd` (`canary_fieldIdx_projection_mismatch_on_niche_in_snd`).
   Dispatching by byte offset (`offset == 0` vs. `offset == b_offset`, matching
   `rustc_codegen_ssa`'s `OperandRef::extract_field`) and extracting sub-word
   niches via `(reg >>> (byteOff * 8)).truncate 8` round-trips all tagged and
   untagged variants (`scalarPair_decode_encode_niche_tagged`,
   `scalarPair_decode_encode_niche_untagged`).
7. **Verified-Mode Sysroot (`-Zbuild-std=core,alloc` + `-Zalways-encode-mir=yes`)
   Two-Tier Caching:**
   Because `rustc_metadata`'s `should_encode_mir` omits `optimized_mir` for
   non-generic, non-`#[inline]` functions unless `-Zalways-encode-mir=yes` is
   passed, `cargo-anneal` must build and cache a content-addressed verified
   sysroot containing Tier 1 `libcore.rmeta` / `liballoc.rmeta` (for on-demand
   generic monomorphization) and Tier 2 pre-extracted `libcore.amir` /
   `liballoc.amir` + pre-verified `Core.olean` / `Alloc.olean` artifacts (for
   zero-reverification reuse of non-generic standard library functions).

---

## Applicability

These findings govern `trusted/rustc-capture`, `rustc_codegen_anneal`,
`trusted/cargo-anneal`, `trusted/lean/Trusted/`, and `theory/Anneal/` across the
following subjects identified in `REPORT.json`:

| Subject | Revision / Digest | Relationship & Scope |
| :--- | :--- | :--- |
| `joshlf/anneal` | `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0` (skeleton worktree `e75556f5767705404404c0675c6d2d9bcee41d6f`) | Governs `trusted/rustc-capture/src/lib.rs`, `trusted/lean/Trusted/{Refinement,StepResult,MirAst,Memory,MirSemantics}.lean`, and `theory/Anneal/{Refinement,StepResult,MirLemmas}.lean`. |
| `rust-lang/rust` | `92b5b8c87c61b20adc9001b41baf587634a74734` (`1.101.0-nightly`), `8006091eb71ae7d9e9bccb66c6122c9d68af4466`, and `58cf8f9c35b355199727627d07ae34a4e2846d67` | Upstream `rustc` source for `rustc_mir_transform`, `rustc_monomorphize`, `rustc_metadata`, `rustc_middle`, `rustc_ty_utils`, `rustc_abi`, `rustc_target`, `rustc_codegen_ssa`, `rustc_codegen_llvm`, `rustc_codegen_cranelift`, `library/core`, `library/alloc`, and `src/tools/miri/cargo-miri`. |
| `rust-lang/reference` | `82da570bafd9efed421bdbae0f8603ede8dd308b` | Normative Rust Reference rules for type layout, calling conventions, and undefined behavior. |
| `leanprover/lean4` | `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) | Kernel verification engine (`lean -j1 -M1024`) used to verify both standalone mechanization probes. |
| `support/track1_abi_and_mono_probe.lean` | SHA-256 `9035399af8255d9f6eb2ba42f69013beb0c014e6f7894bc3435f53ff75466f28` | Round 1 standalone 1,642-line Lean 4.34.1 mechanization of `CValue`/`CPlace`, `PassMode` (`Ignore`, `Direct`, `Pair`, `Cast`, `Indirect`), `FnAbi`, `DropGlue` elision, `RustCall` `spread_arg`, and negative canaries (`buggy_indirect_without_caller_copy_unsound`, `deduced_readonly_phase_mismatch_unsound`). |
| `support/round2_track1_probe.lean` | SHA-256 `7d28a6692348dbbae30e190401f836d72c3922217d9a8bcf99778a7f2c48302a` | Round 2 standalone 877-line Lean 4.34.1 mechanization of `MaskedWord`, `freezeMaskedWord`, `passModeCast_freeze_verified`, `canary_whole_word_poison_on_padding_unsound`, `ScalarPairVal` byte-offset vs. `FieldIdx` dispatch (`canary_fieldIdx_projection_mismatch_on_niche_in_snd`), sub-word niche extraction (`scalarPair_decode_encode_niche_tagged/untagged`), and float bit-manipulation fallbacks (`fabsBits64_spec`, `copysignBits64_spec`). |

---

## Findings

### Finding 1: `rustc_codegen_anneal` Lifecycle, the `--emit=mir` Phase Bug, `Steal<Body>` Hazards, and the Canonical `Runtime(PostCleanup)` Contract

Basis: `source` + `derived`

#### 1.1 The `--emit=mir` `Runtime(Optimized)` Phase Discrepancy in `trusted/rustc-capture`

`trusted/rustc-capture/src/lib.rs:9-19, 621-633` invokes `rustc --emit=mir`
without `-Zmir-opt-level=0`, stating in its module documentation that it
extracts `MirPhase::Runtime(RuntimePhase::PostCleanup)`
(`tcx.mir_drops_elaborated_and_const_checked`).

Direct inspection of `rust-lang/rust@92b5b8c87c61b20adc9001b41baf587634a74734`
establishes that `--emit=mir` does **not** query
`mir_drops_elaborated_and_const_checked`:

1. `compiler/rustc_driver_impl/src/pretty.rs:349-364` (`pretty::emit_mir`) calls
   `rustc_middle::mir::pretty::write_mir_pretty(tcx, None, &mut out)`.
2. `compiler/rustc_middle/src/mir/pretty.rs:317-377` iterates over
   `tcx.mir_keys(())` and calls
   `tcx.instance_mir(ty::InstanceKind::Item(def_id.to_def_id()))` (`pretty.rs:371`).
3. `compiler/rustc_middle/src/ty/mod.rs:1894` (`instance_mir`) dispatches
   `InstanceKind::Item(def)` to `tcx.optimized_mir(def)`.
4. Because `OptLevel::No.mir_opt_level()` defaults to `1`
   (`compiler/rustc_session/src/config.rs:123-128`), `rustc --emit=mir` without
   `-Zmir-opt-level=0` executes the full `mir_opt_level == 1` optimization
   pipeline and emits `MirPhase::Runtime(RuntimePhase::Optimized)`.

#### 1.2 Why `CodegenBackend::codegen_crate` Cannot Directly Borrow `mir_drops_elaborated_and_const_checked`

A custom `CodegenBackend` invoked by `rustc_interface::passes::start_codegen`
(`compiler/rustc_interface/src/passes.rs:1221-1240`) cannot simply call
`tcx.mir_drops_elaborated_and_const_checked(def_id).borrow()` for three
structural reasons:

1. **Destructive query stealing during monomorphization (`Steal<Body>`):**
   The MIR query chain in `compiler/rustc_middle/src/queries.rs:644-677` and
   `compiler/rustc_mir_transform/src/lib.rs:463-835` is a destructive `Steal`
   pipeline:
   ```text
   mir_built(LocalDefId) -> &Steal<Body>
     --(steal)--> mir_promoted(LocalDefId) -> (&Steal<Body>, &Steal<IndexVec<Promoted, Body>>)
     --(steal)--> mir_drops_elaborated_and_const_checked(LocalDefId) -> &Steal<Body>
     --(steal)--> optimized_mir(DefId) -> &Body
   ```
   When a backend invokes `tcx.collect_and_partition_mono_items(())`
   (`compiler/rustc_monomorphize/src/partitioning.rs:1169`), the collector
   visits every reachable function via `collect_items_of_instance`
   (`compiler/rustc_monomorphize/src/collector.rs:1329-1335`), which calls
   `tcx.instance_mir(instance.def)` $\to$ `tcx.optimized_mir(def_id)`. Inside
   `inner_optimized_mir` (`compiler/rustc_mir_transform/src/lib.rs:810`),
   `rustc` executes:
   ```rust
   let body = tcx.mir_drops_elaborated_and_const_checked(did).steal();
   ```
   Once `collect_and_partition_mono_items` returns, every reachable local
   function's `mir_drops_elaborated_and_const_checked` value has been stolen;
   any subsequent `.borrow()` panics with `"attempted to read from stolen
   value"`.
2. **`LocalDefId` keying and cross-crate `.rmeta` serialization:**
   `mir_drops_elaborated_and_const_checked` accepts only a crate-local
   `LocalDefId` (`queries.rs:663`). Cross-crate metadata tables in
   `compiler/rustc_metadata/src/rmeta/mod.rs:680` and
   `compiler/rustc_metadata/src/rmeta/encoder.rs:1949-1975` serialize only
   `optimized_mir` (`encode_mir`) and `mir_for_ctfe`. Instantiating any generic
   or `#[inline]` function from `core`, `alloc`, or an upstream dependency
   requires querying `tcx.optimized_mir(def_id)`.
3. **Mandatory pre-codegen transformations inside `inner_optimized_mir`:**
   Even for crate-local items, `inner_optimized_mir`
   (`compiler/rustc_mir_transform/src/lib.rs:800-834`) performs three non-optional
   transformations after `mir_drops_elaborated_and_const_checked`:
   - `remap_mir_for_const_eval_select(tcx, body, hir::Constness::NotConst)`
     (`lib.rs:244-318, 811`): rewrites `core::intrinsics::const_eval_select(arg_tuple, called_in_const, called_at_rt)`
     into a direct runtime call `called_at_rt(arg_tuple.0, arg_tuple.1, ...)`.
   - `inline::ForceInline` (`lib.rs:719`,
     `compiler/rustc_mir_transform/src/inline.rs:74-96`): carries
     `PassPolicy::Required` (`inline.rs:85`) because `should_codegen_locally`
     (`compiler/rustc_monomorphize/src/collector.rs:1087-1093`) emits a fatal
     delayed bug (`"attempt to codegen #[rustc_force_inline] item"`) if any call
     to a `#[rustc_force_inline]` function survives into monomorphization.
   - `mentioned_items::MentionedItems` (`lib.rs:820`,
     `compiler/rustc_mir_transform/src/mentioned_items.rs:17-31`): populates
     `body.mentioned_items` without mutating statements or terminators, which
     `collect_items_of_instance` (`collector.rs:1384`) iterates over to keep drop
     glue and function pointers alive.

#### 1.3 Complete Audit of `run_runtime_cleanup_passes` and `run_optimization_passes`

Auditing every pass in `run_runtime_cleanup_passes` (`lib.rs:680-687`) and
`run_optimization_passes` (`lib.rs:696-785`) against
`PassManager::should_run_pass`
(`compiler/rustc_mir_transform/src/pass_manager.rs:139-197`) reveals exactly
which passes remain active at `-Zmir-opt-level=0`:

| Pipeline Stage | Pass Name | `PassPolicy` (`pass_manager.rs`) | Active at `-Zmir-opt-level=0`? | Required Flag / Control |
| :--- | :--- | :--- | :--- | :--- |
| `PostCleanup` (`lib.rs:680-687`) | `AbortUnwindingCalls`, `AddRetag`, `Subtyper`, `DropLowering`, `ElaborateDrops`, `Lint` | `Required` / `Optional` | Yes (defines `PostCleanup`) | Keep enabled (`-Cpanic=abort` makes `AbortUnwindingCalls` total; `-Zmir-emit-retag` enables `AddRetag` when borrow-tag checking is active) |
| `PostCleanup` (`lib.rs:685`) | `RemovePlaceMention` | `Optional(!mir_preserve_ub)` (`remove_place_mention.rs:13`) | Yes unless `-Zmir-preserve-ub` | Pass `-Zmir-preserve-ub` (matching Miri in `src/tools/miri/src/lib.rs:196`) |
| `inner_optimized_mir` (`lib.rs:811`) | `remap_mir_for_const_eval_select` | Direct function call (`lib.rs:811`) | Always runs | Required to eliminate `const_eval_select` before runtime codegen |
| `Optimized` (`lib.rs:716-718`) | `CheckAlignment`, `CheckNull`, `CheckEnums` | `Optional(ctx.ub_checks())` (`check_alignment.rs:34`, `check_null.rs:21`, `check_enums.rs:25`) | Yes when `ub_checks` is enabled | Pass `-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums` so MIR compiler-inserted check blocks do not alter raw `PostCleanup` CFGs |
| `Optimized` (`lib.rs:719`) | `ForceInline` | `Required` (`inline.rs:85`) | Always runs (`#[rustc_force_inline]` only) | Required by `rustc_monomorphize` (`collector.rs:1087-1093`) |
| `Optimized` (`lib.rs:722`) | `RemoveUnneededDrops` | `Optional(true)` (`remove_unneeded_drops.rs:44`) | **Yes** (unconditionally enabled at level 0!) | Pass `-Zmir-enable-passes=-RemoveUnneededDrops` |
| `Optimized` (`lib.rs:713-776`) | All 32 other optimization passes (`RevealAll`, `LowerSliceLen`, `SimplifyCfg-*`, `Sroa`, `MatchBranchSimplification`, `MultipleReturnTerminators`, `CopyProp`, `EnumSizeOpt`, `SingleUseConsts`, `InstSimplify-*`, `GVN`, `SimplifyLocals-*`, `DeadStoreElimination-*`, `DataflowConstProp`, `JumpThreading`, `ReferencePropagation`, `PeepholeOptimizations`, `CheckPackedRef`, `Inline`, `DestinationPropagation`) | `Optional(mir_opt_level >= 1..4)` or `Optional(false)` | **No** (skipped at `-Zmir-opt-level=0`) | Disabled by `-Zmir-opt-level=0` |
| `inner_optimized_mir` (`lib.rs:779, 820`) | `CriticalCallEdges`, `MentionedItems` | `Required` (`add_call_guards.rs:130`, `mentioned_items.rs:21`) | Always runs (`CriticalCallEdges` is idempotent because it already ran at `lib.rs:655`; `MentionedItems` is read-only) | Harmless / required for monomorphization |

Therefore, compiling both the sysroot (`core`, `alloc`) and target crates with
the canonical flag contract:

```text
-Copt-level=0
-Cpanic=abort
-Zmir-opt-level=0
-Zvalidate-mir=yes
-Zmir-preserve-ub
-Zalways-encode-mir=yes
-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums,-RemoveUnneededDrops
```

makes `tcx.optimized_mir(def_id)` identical to
`mir_drops_elaborated_and_const_checked(def_id)` modulo `const_eval_select`
lowering and `#[rustc_force_inline]` expansion. `rustc_codegen_anneal` can then
call:
1. `tcx.collect_and_partition_mono_items(())` (`partitioning.rs:1169`),
2. `tcx.instance_mir(instance.def)` (`ty/mod.rs:1891-1907`, which handles both
   `InstanceKind::Item` via `optimized_mir` and all compiler-synthesized shims
   via `tcx.mir_shims` in `compiler/rustc_mir_transform/src/shim.rs:28-206`), and
3. `instance.instantiate_mir_and_normalize_erasing_regions(tcx, ty::TypingEnv::fully_monomorphized(), body)`
   (`compiler/rustc_middle/src/ty/instance.rs:956-970`)
with zero `Steal<Body>` conflicts and full cross-crate polymorphic instantiation.

---

### Finding 2: The `deduced_param_attrs` `ReadOnly` Phase-Mismatch Soundness Bug

Basis: `source` + `execution` + `derived`

Inspecting `compiler/rustc_mir_transform/src/deduce_param_attrs.rs:177-242` and
`compiler/rustc_ty_utils/src/abi.rs:290-315, 643-693` uncovers a subtle
soundness hazard between MIR optimization and `FnAbi` calculation:

1. **No CLI flag disables `deduced_param_attrs` directly:** Searching
   `compiler/rustc_session/src/options.rs` confirms there is no
   `-Zdeduce-param-attrs` option. Instead, `deduced_param_attrs`
   (`deduce_param_attrs.rs:182-185`) is gated directly on `OptLevel`:
   ```rust
   if tcx.sess.opts.optimize == OptLevel::No || tcx.sess.opts.incremental.is_some() {
       return &[];
   }
   ```
   Likewise, `.rmeta` encoding (`compiler/rustc_metadata/src/rmeta/encoder.rs:2005-2017`)
   omits `deduced_param_attrs` only when `tcx.sess.opts.optimize == OptLevel::No`.
2. **How `fn_abi_of_instance` injects `ArgAttribute::ReadOnly`:** In
   `compiler/rustc_ty_utils/src/abi.rs:290-315`, `fn_abi_of_instance_raw`
   queries `tcx.fn_abi_of_instance_no_deduced_attrs(query)` and then invokes
   `fn_abi_adjust_for_deduced_attrs` (`abi.rs:643-693`). For every
   `PassMode::Indirect` parameter on a Rustic ABI (`abi.is_rustic_abi()`), if
   `deduced_param_attrs` reports `read_only: true`,
   `fn_abi_adjust_for_deduced_attrs` inserts `ArgAttribute::ReadOnly` into
   `arg_abi.attrs.regular`.
3. **Why a phase mismatch corrupts caller locals (`Anneal.deduced_readonly_phase_mismatch_unsound`):**
   Suppose an upstream crate or local function is compiled with `-Copt-level=1`
   so `DeadStoreElimination` removes a dead write `_1.0 += 99` to a by-value
   parameter `_1` in `optimized_mir`, causing `deduced_param_attrs` to mark `_1`
   `ArgAttribute::ReadOnly` (`PassMode.indirect true`). If a caller passes a
   live local `slot1` by `Operand::Copy` and elides its caller-side scratch copy
   because `ArgAttribute::ReadOnly` is set (as `rustc_codegen_ssa` does in
   `compiler/rustc_codegen_ssa/src/mir/block.rs:1288-1305`), while codegen
   lowers the unoptimized `PostCleanup` MIR body of the callee (where the dead
   store `_1.0 += 99` still executes), the callee mutates the caller's live
   local `slot1` in-place!
   In `support/track1_abi_and_mono_probe.lean:1557-1640`, we mechanize this
   exact scenario in `deducedReadOnlyMismatchProg` and prove the negative canary
   theorem:
   ```lean
   theorem deduced_readonly_phase_mismatch_unsound :
       ¬ Compiles MirCallLang AbiCallLang (fun b => b)
           deducedReadOnlyMismatchProg deducedReadOnlyMismatchProg
   ```
4. **Defense-in-depth rule for `rustc_codegen_anneal`:** Always enforce
   `-Copt-level=0` across all target crates and sysroot builds, and query
   `tcx.fn_abi_of_instance_no_deduced_attrs` (or strip `ArgAttribute::ReadOnly`
   from `PassMode::Indirect` parameters) so ABI lowering never relies on
   optimization-derived parameter attributes.

---

### Finding 3: Complete 4-Tier Classification of All 264 `#[rustc_intrinsic]` Declarations and the 38/49 Floating-Point Intrinsics

Basis: `source` + `execution` + `derived`

#### 3.1 How `rustc` Determines `must_be_overridden`, `fallback_intrinsics`, and `replaced_intrinsics`

In `compiler/rustc_middle/src/ty/util.rs:1713-1729`, `intrinsic_raw(tcx, def_id)`
inspects the HIR `ItemKind::Fn { has_body, .. }` of a `#[rustc_intrinsic]` item
and constructs `ty::IntrinsicDef` (`compiler/rustc_middle/src/ty/intrinsic.rs:8-14`)
with `must_be_overridden: !has_body`:

- When `must_be_overridden == true` (`!has_body`), `rustc_mir_build`
  (`compiler/rustc_mir_build/src/builder/mod.rs:1052-1057`) synthesizes a dummy
  1-block MIR body ending in `TerminatorKind::Unreachable`.
- When `must_be_overridden == false` (`has_body == true`), `rustc_mir_build`
  (`builder/mod.rs:1072`) builds the normal MIR body of the Rust fallback
  implementation in `library/core/src/intrinsics/`.
- Two session sets in `CodegenBackendInit`
  (`compiler/rustc_session/src/session.rs:535-542`) govern how fallback bodies
  interact with MIR inlining and monomorphization:
  1. **`fallback_intrinsics` (`inline.rs:559-570`):** Intrinsics listed in
     `fallback_intrinsics` are guaranteed **not** to be overridden by the
     backend; the MIR inliner rewrites calls to `InstanceKind::Intrinsic(def_id)`
     into `InstanceKind::Item(def_id)` so their pure-Rust fallback bodies can be
     inlined directly into callers.
  2. **`replaced_intrinsics` (`collector.rs:1017-1034`, `ty_utils/src/instance.rs:94-110`):**
     During monomorphization collection, for any `!must_be_overridden` intrinsic
     **not** in `replaced_intrinsics` (or when `-Zforce-intrinsic-fallback` is
     enabled), `visit_instance_use` (`collector.rs:1017-1034`) pushes
     `MonoItem::Fn(Instance::new_raw(def_id, args))` so the fallback body is
     monomorphized as an ordinary Rust function. Conversely, placing an
     intrinsic in `replaced_intrinsics` prevents `collector.rs` from
     monomorphizing its fallback body and keeps calls as
     `InstanceKind::Intrinsic`.

#### 3.2 Complete 4-Tier Taxonomy of All 264 `#[rustc_intrinsic]` Items in `core` and `alloc`

Across `library/core/src/intrinsics/` (`mod.rs`, `bounds.rs`, `fallback.rs`,
`macros.rs`, `mir.rs`, `reflection.rs`, `simd/mod.rs`, `simd/scalable.rs`) and
`library/alloc/src/intrinsics.rs` at `rust-lang/rust@92b5b8c87c61b20adc9001b41baf587634a74734`,
all **264 `#[rustc_intrinsic]` declarations** partition into four disjoint
lifecycle tiers (note: in downstream pass summaries that group compile-time and
MIR-lowered intrinsics together as "Tier 0 MIR-lowered", our Tier 1 corresponds
to "Tier 0", our Tier 2 corresponds to "Tier 1 fallback bodies", our Tier 3A/3B/3C
correspond to "Tier 2 semantic primitives", and our Tier 3D corresponds to
"Tier 3 rejected/autodiff/SIMD"; the table below preserves the exact counts for
every sub-group):

| Lifecycle Tier | Count | `rustc` Pipeline Stage & Handling | Complete Intrinsic Inventory (264 Total) |
| :--- | :---: | :--- | :--- |
| **Compile-Time-Only (`#[rustc_comptime]` & Reflection)** *(Tier 0A)* | **27** | Evaluated during CTFE or MIR construction; never reach runtime codegen. | **`core::intrinsics` (`mod.rs`, 11):** `needs_drop`, `size_of`, `align_of`, `offset_of`, `field_offset`, `variant_count`, `type_name`, `field_representing_type_actual_type_id`, `field_representing_type_name`, `field_representing_type_offset`, `rustc_peek`.<br>**`core::intrinsics::reflection` (`reflection.rs`, 16):** `type_id`, `type_id_type_of`, `type_id_vtable`, `type_id_is_signed`, `type_id_array_len`, `type_id_element_ty`, `type_id_size_of`, `type_id_variants`, `type_id_variant_name`, `type_id_variant_non_exhaustive`, `type_id_fields`, `type_id_non_exhaustive`, `type_id_generics`, `type_id_field_representing_type`, `type_id_points_to`, `type_id_points_mutably`, `type_id_function_ptr`. |
| **Lowered Before Codegen to First-Class MIR Statements / Rvalues / Terminators** *(Tier 0B / Tier 1)* | **32** | Rewritten into native MIR constructs by `rustc_mir_build` (2), `LowerIntrinsics` (`PassPolicy::Required`, 29), or `remap_mir_for_const_eval_select` (1). | **`rustc_mir_build` (`expr/into.rs:407-485`, 2):** `write_via_move`, `alloc::intrinsics::write_box_via_move` (`*dst = move val`).<br>**`LowerIntrinsics` (`lower_intrinsics.rs:22-336`, 29):** `unreachable` (`TerminatorKind::Unreachable`), `ub_checks` / `overflow_checks` / `contract_checks` (`Rvalue::NullaryOp`), `forget` (no-op `Goto`), `copy_nonoverlapping` (`StatementKind::Intrinsic(CopyNonOverlapping)`), `assume` (`StatementKind::Intrinsic(Assume)`), `wrapping_add` / `wrapping_sub` / `wrapping_mul` (`BinOp::{Add,Sub,Mul}`), `three_way_compare` (`BinOp::Cmp`), `unchecked_add` / `unchecked_sub` / `unchecked_mul` (`BinOp::*Unchecked`), `unchecked_div` / `unchecked_rem` (`BinOp::{Div,Rem}`), `unchecked_shl` / `unchecked_shr` (`BinOp::{Shl,Shr}Unchecked`), `add_with_overflow` / `sub_with_overflow` / `mul_with_overflow` (`BinOp::*WithOverflow`), `read_via_copy` (`Rvalue::Use(Copy(*ptr))`), `discriminant_value` (`Rvalue::Discriminant(*ptr)`), `offset` (`BinOp::Offset`), `slice_get_unchecked` (`(*slice_ptr)[idx]`), `transmute` / `transmute_unchecked` (`CastKind::Transmute`), `aggregate_raw_ptr` (`Rvalue::RawPtr`), `ptr_metadata` (`UnaryOp::PtrMetadata`).<br>**`remap_mir_for_const_eval_select` (`lib.rs:244-318`, 1):** `const_eval_select`. |
| **Intrinsics with Rust Fallback Bodies (`must_be_overridden == false`)** *(Tier 1 / Tier 2)* | **67** | Have a `{ ... }` body in `core::intrinsics`. Routed to `InstanceKind::Item` fallback bodies unless placed in `replaced_intrinsics`. | **Integer & bitwise (`mod.rs`, `fallback.rs`, 9):** `integer_min`, `integer_max`, `disjoint_bitor`, `carrying_mul_add`, `rotate_left`, `rotate_right`, `unchecked_funnel_shl`, `unchecked_funnel_shr`, `carryless_mul`.<br>**Pointer, memory & reflection (3):** `typed_swap_nonoverlapping`, `ptr_guaranteed_cmp`, `reflection::type_id_eq`.<br>**Hints, diagnostics, const-heap & contracts (14):** `prefetch_read_data`, `prefetch_write_data`, `prefetch_read_instruction`, `prefetch_write_instruction`, `resumable_breakpoint`, `codeview_annotation`, `cold_path`, `select_unpredictable`, `is_val_statically_known`, `const_allocate`, `const_deallocate`, `const_make_global`, `contract_check_requires`, `contract_check_ensures`.<br>**Variadic & frame (3):** `va_copy`, `va_end`, `return_address`.<br>**Floating-point with fallback bodies (`mod.rs`, `macros.rs`, 38):** 22 Category A pure-Rust bit/comparison fallbacks + 16 Category B/C `intrinsic_dispatch_on_type!` `libm` fallbacks (detailed in §3.3 below). |
| **Mandatory `#![no_std]` / `core` / `alloc` Semantic Primitives (`must_be_overridden == true`)** *(Tier 2A / Tier 3A)* | **37** | Reach codegen as `InstanceKind::Intrinsic`; must be modeled in `AnMIR`/`AnSSA` and lowered by `rustc_codegen_anneal`. | **Control & trap (2):** `abort_immediate`, `breakpoint`.<br>**Static validity guards (3):** `assert_inhabited`, `assert_zero_valid`, `assert_mem_uninitialized_valid`.<br>**Dynamic layout & vtable metadata (4):** `size_of_val`, `align_of_val`, `vtable_size`, `vtable_align`.<br>**Pointer arithmetic, masking & byte comparison (6):** `arith_offset`, `ptr_offset_from`, `ptr_offset_from_unsigned`, `ptr_mask`, `raw_eq`, `compare_bytes`.<br>**Bulk & volatile memory (10):** `copy`, `write_bytes`, `volatile_copy_nonoverlapping_memory`, `volatile_copy_memory`, `volatile_set_memory`, `volatile_load`, `volatile_store`, `unaligned_volatile_load`, `unaligned_volatile_store`, `nontemporal_store`.<br>**Integer bit-manipulation & arithmetic (10):** `ctpop`, `ctlz`, `ctlz_nonzero`, `cttz`, `cttz_nonzero`, `bswap`, `bitreverse`, `saturating_add`, `saturating_sub`, `exact_div`.<br>**Compiler hints / diagnostics (2):** `black_box`, `caller_location`. |
| **Concurrency & Unwinding Semantic Primitives (`must_be_overridden == true`)** *(Tier 2B / Tier 3B)* | **18** | C++20 atomics and `catch_unwind` (trivial under `-Cpanic=abort`). | **Atomics (17):** `atomic_load`, `atomic_store`, `atomic_xchg`, `atomic_cxchg`, `atomic_cxchgweak`, `atomic_xadd`, `atomic_xsub`, `atomic_and`, `atomic_nand`, `atomic_or`, `atomic_xor`, `atomic_max`, `atomic_min`, `atomic_umax`, `atomic_umin`, `atomic_fence`, `atomic_singlethreadfence`.<br>**Unwinding (1):** `catch_unwind` (under `-Cpanic=abort`, calls `try_fn(data)` and returns `0`). |
| **Bodyless Floating-Point Fast/Algebraic & Cast Intrinsics (`must_be_overridden == true`)** *(Tier 2C / Tier 3C)* | **11** | Float operations without fallback bodies; lowered as `InstanceKind::Intrinsic` when float verification is enabled. | `fadd_fast`, `fsub_fast`, `fmul_fast`, `fdiv_fast`, `frem_fast`, `fadd_algebraic`, `fsub_algebraic`, `fmul_algebraic`, `fdiv_algebraic`, `frem_algebraic`, `float_to_int_unchecked`. |
| **Rejected SIMD, SVE, GPU, Autodiff, Offload, & Variadic Intrinsics (`must_be_overridden == true`)** *(Tier 3 / Tier 3D)* | **72** | Out of scope for verified core; rejected by `rustc_codegen_anneal` with a diagnostic if reached during monomorphization. | `core::intrinsics::simd::*` (61), `core::intrinsics::simd::scalable::sve_tuple_*` (5), `va_arg` (1), `gpu_launch_sized_workgroup_mem` (1), `amdgpu_dispatch_ptr` (1), `autodiff` (1), `offload` (1), `offload_get_num_devices` (1). |

#### 3.3 Exact Partitioning of the 38/49 Floating-Point Intrinsics (`fallback_intrinsics` vs. `replaced_intrinsics`)

Inspecting `library/core/src/intrinsics/macros.rs:1-102`,
`library/core/src/intrinsics/mod.rs:1292-1725, 3087-3545`, and
`library/core/src/num/imp/libm.rs:1-195` reveals a critical distinction among
the **38 floating-point intrinsics with fallback bodies** (49 total including
the 11 bodyless Category D intrinsics):

| Category | Count | Intrinsics (`core::intrinsics::*`) | Fallback Body Implementation in `core` | Required `rustc_codegen_anneal` Configuration |
| :--- | :---: | :--- | :--- | :--- |
| **Category A: Pure-Rust Bit-Manipulation & IEEE 754 Comparison Fallbacks** | **22** | `fmuladd` (`mod.rs:1530`); `fabs` (`mod.rs:3497`); `copysignf{16,32,64,128}` (`mod.rs:3508-3544`); `minimum_number_nsz_f{16,32,64,128}` (`mod.rs:3103-3187`); `maximum_number_nsz_f{16,32,64,128}` (`mod.rs:3305-3389`); `minimumf{16,32,64,128}` (`mod.rs:3201-3287`); `maximumf{16,32,64,128}` (`mod.rs:3403-3485`) | Pure Rust: `a * b + c` (`fmuladd`); `to_bits` / `from_bits` with `SIGN_MASK` (`fabs`, `copysignf*`); IEEE 754 `is_nan()`, `<=`, `<`, `is_sign_negative()`, `+` (`minimum*`, `maximum*`). | **Place all 22 in `fallback_intrinsics`** (and omit from `replaced_intrinsics`). MIR inlining (`inline.rs:564-570`) lowers them to pure-Rust MIR primitives (`BinOp::{Mul, Add, BitAnd, BitOr, Lt, Le}`, `UnOp::Not`), eliminating 22 intrinsic axioms and resolving `fmuladd` fusion nondeterminism! |
| **Category B: IEEE 754 Algebraic & Rounding (`intrinsic_dispatch_on_type!`)** | **7** | `sqrt` (`mod.rs:1299`); `fma` (`mod.rs:1504`); `floor` (`mod.rs:1546`); `ceil` (`mod.rs:1566`); `trunc` (`mod.rs:1586`); `round_ties_even` (`mod.rs:1608`); `round` (`mod.rs:1629`) | Expands via `intrinsic_dispatch_on_type!` (`macros.rs:20-100`) to `impl Dispatch for f16/f32/f64/f128` calling `unsafe extern "C"` `libm` symbols (`libm.rs:18-81`: `sqrtf`, `fmaf`, `floorf`, `ceilf`, `truncf`, `roundevenf`, `roundf`, etc.). | **Place all 7 in `replaced_intrinsics`** (matching `llvm_backend.rs:233-241`) so `collector.rs` never monomorphizes the `extern "C"` `libm` fallback bodies. Intercept `InstanceKind::Intrinsic` in `AnMIR`/`AnSSA` with exact IEEE 754-2019 `Flocq` specifications. |
| **Category C: Transcendental & Power (`intrinsic_dispatch_on_type!`)** | **9** | `powi` (`mod.rs:1315`); `sin` (`mod.rs:1331`); `cos` (`mod.rs:1352`); `powf` (`mod.rs:1373`); `exp` (`mod.rs:1394`); `exp2` (`mod.rs:1415`); `log` (`mod.rs:1436`); `log10` (`mod.rs:1457`); `log2` (`mod.rs:1478`) | Expands via `intrinsic_dispatch_on_type!` to `unsafe extern "C"` `libm::likely_available` / `maybe_available` calls (`libm.rs:11-15, 107-194`). | **Place all 9 in `replaced_intrinsics`** so `collector.rs` does not emit unverified `Dispatch::dispatch` shims. Intercept `InstanceKind::Intrinsic` as target `libm` contract calls (or reject in strict bit-deterministic mode). |
| **Category D: Bodyless Fast, Algebraic, & Unchecked Cast Intrinsics** | **11** | `fadd_fast`, `fsub_fast`, `fmul_fast`, `fdiv_fast`, `frem_fast` (`mod.rs:1643-1675`); `float_to_int_unchecked` (`mod.rs:1683`); `fadd_algebraic`, `fsub_algebraic`, `fmul_algebraic`, `fdiv_algebraic`, `frem_algebraic` (`mod.rs:1692-1724`) | No fallback body (`must_be_overridden == true`). | Handled directly as `InstanceKind::Intrinsic`: `f*_fast` enforces finite inputs and output (`isFinite a ∧ isFinite b ∧ isFinite res`, UB otherwise); `f*_algebraic` refines to IEEE 754 arithmetic; `float_to_int_unchecked` enforces `trunc(value) ∈ [Int::MIN, Int::MAX]`. |

In Section 4 of `support/round2_track1_probe.lean:743-813`, we mechanize the
64-bit bitwise fallback implementations `fabsBits64` (`x &&& ~~~f64SignMask`)
and `copysignBits64` (`(x &&& ~~~f64SignMask) ||| (y &&& f64SignMask)`), proving
`fabsBits64_spec`, `copysignBits64_spec`, and `fabsBits64_eq_copysign_posZero`:
the pure-Rust fallback bodies of `fabs` and `copysignf64` are bit-for-bit
identical to the IEEE 754-2019 `abs` and `copySign` specifications across all
finite, infinite, quiet-NaN, and signaling-NaN bit patterns.

---

### Finding 4: Direct MIR-to-SSA (`CValue`/`CPlace`) and `FnAbi`/`PassMode` Marshaling

Basis: `source` + `execution` + `derived`

#### 4.1 Bypassing `rustc_codegen_ssa::mir` via `CValue` and `CPlace`

`rustc_codegen_ssa::mir` (`FunctionCx`, `LocalRef`, `OperandRef`) is tightly
coupled to 15+ LLVM-oriented builder traits (`BuilderMethods`, `BackendTypes`,
`AbiBuilderMethods`, etc.). By contrast, `rustc_codegen_cranelift`
(`compiler/rustc_codegen_cranelift/src/lib.rs:126-250`, `driver/aot.rs:150-395`,
`base.rs:35-824`, and `value_and_place.rs:58-841`) demonstrates that
`rustc_codegen_anneal` can call `rustc_codegen_ssa::base::codegen_crate` while
implementing only `CodegenBackend`, `ExtraBackendMethods`, and
`WriteBackendMethods` (`ModuleBuffer = Infallible`, `ThinData = Infallible`,
`TargetMachine = ()`) and lowering monomorphized `instance_mir` bodies directly
via two semantic types:

- **`CValue<'tcx>` (`value_and_place.rs:65-69`):**
  - `ByRef(Pointer, Option<Value>)`: memory-backed value at a stack slot or
    heap/stack pointer with optional wide metadata (`len` or `vtable`); ZSTs use
    `ByRef(Pointer::dangling(layout.align.abi), None)` (`value_and_place.rs:97-100`).
  - `ByVal(Value)`: single SSA register (`BackendRepr::Scalar` or `SimdVector`).
  - `ByValPair(Value, Value)`: two SSA registers (`BackendRepr::ScalarPair`).
- **`CPlace<'tcx>` (`value_and_place.rs:428-433`):**
  - `Var(Local, Variable)`: single SSA variable.
  - `VarPair(Local, Variable, Variable)`: pair of SSA variables.
  - `Addr(Pointer, Option<Value>)`: memory address with optional unsized
    metadata (used for all locals whose address is taken or that have
    `BackendRepr::Memory`).

In Section 2 of `support/track1_abi_and_mono_probe.lean:420-542`, we mechanize
`CValue`, `CPlace`, `cplaceToCValue`, and `cplaceWriteCValue`, proving universal
write-then-read round-trip adequacy (`Anneal.cplace_write_read_roundtrip`)
across `.var`, `.varPair`, and `.addr`.

#### 4.2 `PassMode::Indirect` Callee Aliasing vs. Caller Scratch Copies

Comparing `codegen_fn_prelude` (`compiler/rustc_codegen_cranelift/src/abi/mod.rs:259-408`)
and `adjust_arg_for_abi` (`compiler/rustc_codegen_cranelift/src/abi/pass_mode.rs:255-286`)
exposes an essential aliasing invariant:

1. **Callee prelude aliasing (`abi/mod.rs:347-365`):** When an incoming argument
   has `PassMode::Indirect` (`val.try_to_ptr() == Some((addr, None))`) and is
   not an underaligned pointee, `codegen_fn_prelude` binds `mir_local`
   **directly** to `CPlace::for_ptr(addr, arg_abi.layout)` without copying. Any
   in-place mutation of `mir_local` in the callee's MIR body therefore mutates
   the memory at `addr` directly.
2. **Caller call-site scratch copy (`abi/mod.rs:420`, `abi/pass_mode.rs:270-284`):**
   When the call argument is `Operand::Copy(place)` (`!is_owned`), the caller
   **must** allocate a fresh temporary stack slot (`CPlace::new_stack_slot`),
   copy the argument into it, and pass the temporary slot's address.
3. **Mechanized Proofs (`support/track1_abi_and_mono_probe.lean:574-1543`):**
   - `Anneal.abi_call_marshaling_refines` and `Anneal.abi_compiler_soundOn`
     (lines 1137–1190) prove `Compiles MirCallLang AbiCallLang (fun b => b) prog
     prog` and `AbiLoweringCompiler.SoundOn prog` across all valid `PassMode`s
     (`ignore`, `direct`, `pair`, `cast`, `indirect false`) and operand modes
     (`copy`, `move`), even when the callee mutates its parameter local in-place.
   - `Anneal.caller_callee_mutate_verified` (lines 1368–1388) discharges
     end-to-end `VerificationResultOn` with **zero TCB assumptions**
     (`assumptions := []`) for `callerCalleeMutateProg`.
   - `Anneal.buggy_indirect_without_caller_copy_unsound` (lines 1497–1540)
     proves `¬ Compiles MirCallLang BuggyAbiCallLang (fun b => b)
     callerCalleeMutateProg callerCalleeMutateProg` when the caller omits the
     scratch copy on `Operand.copy`.
   - `Anneal.empty_drop_shim_refines` and `Anneal.rust_call_spread_arg_refines`
     (lines 1434–1474) prove refinement for `InstanceKind::DropGlue(_, None)`
     call elision (`abi/mod.rs:492-498`) and `ExternAbi::RustCall` tuple
     spreading (`fx.mir.spread_arg` in `abi/mod.rs:298-317, 530-553`).

---

### Finding 5: `PassMode::Cast` Across `x86_64`, `aarch64`, and `riscv64` & Verified `MaskedWord` + `freezeMaskedWord` Lowering

Basis: `source` + `execution` + `derived`

#### 5.1 `CastTarget` Layout Rules Under `ExternAbi::Rust` vs. Foreign `extern "C"` ABIs

In `compiler/rustc_target/src/callconv/mod.rs:238-404`, `PassMode::Cast {
pad_i32, cast: Box<CastTarget> }` describes register-packed aggregates via
`prefix: ArrayVec<Reg, 8>`, `rest_offset: Option<Size>` (used by RISC-V LP64D
`CastTarget::offset_pair` for heterogeneous `(float, int)` pairs), and `rest:
Uniform { unit: Reg, total: Size, is_consecutive: bool }`.

1. **Rustic ABIs (`FnAbi::adjust_for_rust_abi`, `mod.rs:772-940`):**
   Leaves `BackendRepr::Scalar` as `PassMode::Direct` and `BackendRepr::ScalarPair`
   as `PassMode::Pair` (demoting returns with `size > 2 * ptr_size` to
   `PassMode::Indirect`). For `BackendRepr::Memory` aggregates with `size <=
   cx.pointer_size()`, lines 900–914 invoke
   `arg.cast_to_maybe_noundef(Reg { kind: RegKind::Integer, size }, cx)`, which
   attaches `ArgAttribute::NoUndef` (`mod.rs:570-588, 949-1001`) **if and only
   if** the aggregate has zero inter-field or trailing padding (`offset ==
   cursor` and `cursor == layout.size`), contains no `union`, `UnsafeCell`, or
   multi-variant enum, and satisfies `target.size(cx) == self.layout.size`.
2. **Foreign `extern "C"` ABIs (`TyAndLayout::is_aggregate`,
   `compiler/rustc_abi/src/lib.rs:2299-2306`):**
   Under foreign ABIs, `is_aggregate()` returns `true` for **both**
   `BackendRepr::ScalarPair` and `BackendRepr::Memory`. Moreover, foreign ABI
   classifiers call `arg.cast_to(...)` (`mod.rs:564-568`) rather than
   `cast_to_maybe_noundef`, so foreign `PassMode::Cast` arguments and returns
   **never** carry `ArgAttribute::NoUndef`.

| Aggregate Shape (64-bit Target) | `ExternAbi::Rust` (`adjust_for_rust_abi`) | `x86_64` SysV (`x86_64.rs:29-268`) | `aarch64` AAPCS64 (`aarch64.rs:20-159`) | `riscv64` LP64D (`riscv.rs:39-401`) |
| :--- | :--- | :--- | :--- | :--- |
| `#[repr(C)] struct Padded { a: u8, b: u32 }` (8 B, align 4, `ScalarPair`, bytes 1..3 pad) | `PassMode::Pair(i8 zext, i32)` | `PassMode::Cast(Reg::i64())` (`Class::Int`) | `PassMode::Cast(Uniform::new(Reg::i64(), 8B))` | `PassMode::Cast(Reg::i64())` (`total <= xlen`) |
| `#[repr(C)] struct Three { a: u8, b: u16, c: u32 }` (8 B, align 4, `Memory`, byte 1 pad) | `PassMode::Cast(Reg::i64())` (`NoUndef = false`) | `PassMode::Cast(Reg::i64())` | `PassMode::Cast(Uniform::new(Reg::i64(), 8B))` | `PassMode::Cast(Reg::i64())` |
| `#[repr(C)] struct PackedPair { a: u32, b: u32 }` (8 B, align 4, `ScalarPair`, 0 pad) | `PassMode::Pair(i32, i32)` | `PassMode::Cast(Reg::i64())` | `PassMode::Cast(Uniform::new(Reg::i64(), 8B))` | `PassMode::Cast(Reg::i64())` |
| `#[repr(C)] struct TwoWords { a: u64, b: u32 }` (16 B, align 8, `ScalarPair`, bytes 12..15 pad) | `PassMode::Pair(i64, i32)` | `PassMode::Cast(CastTarget::pair(i64, i32))` (`[Int, Int]`, 2nd reg sized to 4B) | `PassMode::Cast(Uniform::new(Reg::i64(), 16B))` | `PassMode::Cast(Uniform::new(Reg::i64(), 16B))` |
| `#[repr(C)] struct FloatInt { f: f32, i: u32 }` (8 B, align 4, `ScalarPair`, 0 pad) | `PassMode::Pair(f32, i32)` | `PassMode::Cast(Reg::i64())` (`Int.min(Sse) = Int` in same 8B chunk) | `PassMode::Cast(Uniform::new(Reg::i64(), 8B))` (not HFA) | `PassMode::Cast(CastTarget::offset_pair(f32, 4B, i32))` (1 FPR + 1 GPR) |
| `#[repr(C)] struct Hfa3 { x: f32, y: f32, z: f32 }` (12 B, align 4, `Memory`, 0 pad) | `PassMode::Indirect` (`size > 8B`) | `PassMode::Cast(CastTarget::pair(Vector(2xf32), f32))` (`[Sse, Sse]`) | `PassMode::Cast(Uniform::consecutive(f32, 12B))` (HFA $\le 4$ floats) | `PassMode::Cast(Uniform::new(Reg::i64(), 16B))` ($>2$ fields $\to$ GPRs) |
| `#[repr(C)] struct Big { a: [u64; 3] }` (24 B, align 8, `Memory`) | `PassMode::Indirect` (pointer + caller copy) | `PassMode::Indirect { on_stack: true }` (`byval` / `sret`) | `PassMode::Indirect` (pointer + caller copy) | `PassMode::Indirect` (pointer + caller copy) |

#### 5.2 Resolving Whole-Word Padding Poison via `MaskedWord` and `freezeMaskedWord`

In `rustc_codegen_ssa/src/mir/block.rs:2056-2104` and
`rustc_codegen_cranelift/src/abi/pass_mode.rs:207-252`, `PassMode::Cast` copies
the aggregate into a stack slot `%scratch` and executes a whole-word integer
load (`load i64, ptr %scratch`). In formal LLVM semantics (`Vellvm`
`FromBytesToInt` and `Alive2` `Byte::to_int`), loading an `i64` across even a
single uninitialized padding byte taints the entire 64-bit word as `poison`.

In Sections 1 and 2 of `support/round2_track1_probe.lean:126-445`, we resolve
this mismatch by modeling cast words in `AnMIR`/`AnSSA` with an explicit per-bit
initialization mask:

```lean
structure MaskedWord where
  bits : BitVec 64
  initMask : BitVec 64
```

For `PaddedStruct { a : BitVec 8, b : BitVec 32 }` (with 24 bits of
uninitialized padding at bits `8..31`), `paddedStructInitMask =
0xFFFF_FFFF_0000_00FF#64`. At the target lowering boundary, `freezeMaskedWord`
materializes uninitialized bits from a nondeterministic hardware oracle `oracle
: BitVec 64`:

$$\mathsf{freezeMaskedWord}(\mathit{oracle}, w) \;\triangleq\; (w.\mathsf{bits} \mathbin{\&} w.\mathsf{initMask}) \;\mathbin{|}\; (\mathit{oracle} \mathbin{\&} \mathord{\sim}w.\mathsf{initMask})$$

We prove:
- **`unpack_pack_padded_exact` (lines 197–206):** Universal round-trip
  `unpackStructFromMaskedWord (packStructToMaskedWord s padBits) = some s` for
  all `s : PaddedStruct` and `padBits : BitVec 24`.
- **`freezeMaskedWord_preserves_initialized_bits` &
  `unpack_frozen_pack_padded_exact` (lines 240–293):** Proves that
  `freezeMaskedWord` preserves every bit where `initMask = 1` and that unpacking
  the frozen word recovers `some s` for every `oracle : BitVec 64`.
- **`passModeCast_freeze_compiles` & `passModeCast_freeze_verified` (lines
  364–395):** Proves `Trusted.Compiles` and `Trusted.Compiler.Verified` for
  `compilePassModeCast` across all `oracle : BitVec 64`.
- **`canary_whole_word_poison_on_padding_unsound` (lines 430–445):** Proves that
  a naive whole-word `i64` load without per-byte `freeze`
  (`wholeWordLoadWithoutFreeze`, which requires `w.initMask == ~~~0#64`) returns
  `none` on `PaddedStruct` and violates `Trusted.Compiles`.

---

### Finding 6: Byte-Offset-Dispatched `BackendRepr::ScalarPair` and Sub-Word Niche Extraction

Basis: `source` + `execution` + `derived`

#### 6.1 The `tag_field = FieldIdx(0)` vs. `niche_offset = b_offset` Invariant in `rustc_abi`

In `compiler/rustc_abi/src/layout.rs:590-749`, `LayoutData::scalar_pair(cx, a,
b)` places scalar `a` at byte offset `0` and scalar `b` at byte offset
`b_offset = a.size(dl).align_to(b.align(dl).abi) > 0`. When a multi-variant enum
uses `TagEncoding::Niche` and has `BackendRepr::ScalarPair(first, second)`,
lines 711–749 establish two invariants:

1. **Non-niche scalar is reset to `Scalar::Union` (`layout.rs:714-720`):** Only
   the scalar containing the niche is guaranteed initialized in niched variants;
   the other scalar is converted via `.to_union()`.
2. **`tag_field` is always `FieldIdx::new(0)` with byte offset `niche_offset`
   (`layout.rs:734-749`):** The outer enum's `fields` is
   `FieldsShape::Arbitrary { offsets: [niche_offset].into(), memory_index: [0].into() }`
   and `tag_field` is hardcoded to `FieldIdx::new(0)`. Consequently, when the
   niche resides in the **second** scalar (`niche_offset == b_offset > 0`, e.g.,
   `Option<(u64, NonZeroU64)>`), `tag_field` has index `0` (`FieldIdx(0)`) even
   though it lives in the second element (`snd`) of the `ScalarPair`!

In `rustc_codegen_ssa`, `OperandRef::extract_field`
(`compiler/rustc_codegen_ssa/src/mir/operand.rs:383-454`) dispatches on **byte
offset** (`if offset.bytes() == 0 { a_llval } else { b_llval }`), so projecting
`tag_field = FieldIdx(0)` when `niche_offset = b_offset` correctly extracts
`b_llval` (`snd`). By contrast, `rustc_codegen_cranelift`'s
`CValue::value_field` (`value_and_place.rs:182-193`) and `CPlace::place_field`
(`value_and_place.rs:678-686`) dispatch on `field.as_u32()` (`0 => val1, 1 =>
val2`), forcing `cg_clif` (`common.rs:88-105`) to demote all struct/enum
`ScalarPair`s to stack slots. In `support/round2_track1_probe.lean:487-522`,
theorem `canary_fieldIdx_projection_mismatch_on_niche_in_snd` proves that on any
`ScalarPairVal` with `fst ≠ snd`, `extractScalarPairByFieldIdx` (`fieldIdx = 0`)
returns `fst` whereas `extractScalarPairByOffset` (`fieldOffset = 8, bOffset =
8`) returns `snd`.

#### 6.2 Sub-Word Niche Discriminant Extraction and Insertion (`ScalarPairVal`)

When a niche tag occupies a sub-word byte offset `byteOff : Fin 8` inside either
64-bit register (`inSnd : Bool`) of a `ScalarPairVal`, `extractByteAt` and
`insertByteAt` (`support/round2_track1_probe.lean:532-558`) extract and update
the 8-bit field via:

$$\mathsf{extractByteAt}(\mathit{word}, \mathit{byteOff}) \;\triangleq\; \mathsf{truncate}_8\!\left(\mathit{word} \gg (\mathit{byteOff} \times 8)\right)$$

In Section 3 of `support/round2_track1_probe.lean:560-740`, we mechanize a
4-variant enum with a wrapping 8-bit niche `[254, 0]` (`subwordNicheStart =
254#8`, `subwordNicheSpan = 2#8`, `subwordUntaggedVariant = 1#8`) at an
arbitrary `(inSnd : Bool, byteOff : Fin 8)` and prove:
- `extractByteAt_insertByteAt_exact` &
  `extractScalarPairByte_insertScalarPairByte_exact`: extracting the byte at
  `(inSnd, byteOff)` after inserting `b : BitVec 8` recovers `b` for all `pair :
  ScalarPairVal`, `inSnd : Bool`, and `byteOff : Fin 8`.
- `extractByteAt_insertByteAt_other_bytes_preserved` &
  `insertScalarPairByte_preserves_other_reg`: inserting `b` at `(inSnd,
  byteOff)` leaves all other 7 bytes in the target register and all 8 bytes in
  the other register bit-for-bit unchanged.
- `scalarPair_decode_encode_niche_tagged` &
  `scalarPair_decode_encode_niche_untagged`: encoding any tagged variant `v < 4`
  (`v ≠ 1`) or untagged payload byte in `1..=253` at `(inSnd, byteOff)` and
  decoding via modular wrapping subtraction `byte - subwordNicheStart` recovers
  the exact variant index.

---

### Finding 7: Verified-Mode Sysroot (`-Zbuild-std=core,alloc`) and Two-Tier `.rmeta` / `.amir` / `.olean` Caching

Basis: `source` + `derived`

In `compiler/rustc_metadata/src/rmeta/encoder.rs:1177-1207`, `should_encode_mir`
writes `optimized_mir` into `.rmeta` only when:

```rust
let opt = tcx.sess.opts.unstable_opts.always_encode_mir
    || (tcx.sess.opts.output_types.should_codegen()
        && reachable_set.contains(&def_id)
        && (tcx.generics_of(def_id).requires_monomorphization(tcx)
            || tcx.cross_crate_inlinable(def_id)));
```

Consequently, prebuilt `rustup` sysroots (`libcore.rlib`, `liballoc.rlib`) omit
`optimized_mir` for all non-generic, non-`#[inline]` functions
(`tcx.is_item_mir_available(def_id) == false` at `decoder.rs:1410-1412`) and
encode `mir_opt_level >= 1` bodies with `deduced_param_attrs` enabled.

Modeled on `cargo-miri`'s `setup.rs` (`src/tools/miri/cargo-miri/src/setup.rs:16-193`
and `phases.rs:59-535`), `cargo-anneal` must maintain a content-addressed
sysroot cache keyed by `(rustc_commit_hash, anneal_version, target_triple,
verify_mode_flags)` compiled with:

```text
-Copt-level=0
-Cpanic=abort
-Cdebug-assertions=off
-Coverflow-checks=on
-Zub-checks=on
-Zmir-opt-level=0
-Zvalidate-mir=yes
-Zmir-preserve-ub
-Zalways-encode-mir=yes
-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums,-RemoveUnneededDrops
```

This sysroot cache provides a **two-tier verification artifact store**:
1. **Tier 1 (`.rmeta` / `.rlib` for Generic On-Demand Monomorphization):** When
   a downstream crate instantiates a generic `core` or `alloc` function (such as
   `Option::<T>::map` or `Vec::<T>::push`), `tcx.instance_mir(instance.def)`
   loads the unoptimized `PostCleanup`-equivalent body from `libcore.rmeta` /
   `liballoc.rmeta` and `rustc_codegen_anneal` extracts its monomorphized body
   on demand.
2. **Tier 2 (Pre-Extracted `.amir` & Pre-Verified `.olean` for Non-Generic
   Sysroot Items):** During `cargo anneal setup`, non-generic functions in
   `core` and `alloc` are extracted once into `libcore.amir` / `liballoc.amir`
   and compiled into `Core.olean` / `Alloc.olean`, allowing downstream crates to
   `import Core` and `import Alloc` in Lean 4 without re-extracting or
   re-verifying non-generic standard library functions.

---

## Boundaries

1. **`trusted/` vs. `theory/` Separation (`PRINCIPLES.md` and `AGENTS.md`):**
   - `trusted/` contains only the effectful `rustc` capture/codegen driver
     (`trusted/rustc-capture` / `rustc_codegen_anneal`), the CLI orchestrator
     and sysroot builder (`trusted/cargo-anneal`), the `.olean` boundary auditor
     (`trusted/audit`), and the theorem-free specification files in
     `trusted/lean/Trusted/`.
   - All ABI marshaling proofs (`abi_call_marshaling_refines`,
     `passModeCast_freeze_verified`), `ScalarPair` niche round-trip lemmas, and
     intrinsic refinement theorems belong strictly in `theory/Anneal/`.
2. **Exclusions from the Initial Verified Core:**
   - **unsupported in initial verified mode:** Unwinding (`-Cpanic=unwind`) is
     excluded in favor of `-Cpanic=abort`, which makes `AbortUnwindingCalls`
     total and collapses `catch_unwind` to a direct call.
   - **unsupported in initial verified mode:** The 72 domain-specific intrinsics
     (61 `core::intrinsics::simd::*`, 5 SVE `sve_tuple_*`, `va_arg`,
     `gpu_launch_sized_workgroup_mem`, `amdgpu_dispatch_ptr`, `autodiff`,
     `offload`, and `offload_get_num_devices`) are rejected by
     `rustc_codegen_anneal` with a clear diagnostic if reached during
     monomorphization.
   - **not examined:** Foreign C-variadic (`extern "C" fn(..., ...)`) callees
     and inline assembly (`MonoItem::GlobalAsm` / `TerminatorKind::InlineAsm`)
     are outside the pure `PostCleanup` MIR semantics modeled here.

---

## Evidence

### 1. Primary Upstream Source Coordinates (`rust-lang/rust@92b5b8c87c61b20adc9001b41baf587634a74734`)

- **MIR Phases, Query Stealing, and Pass Policies:**
  - `compiler/rustc_driver_impl/src/pretty.rs:349-364` (`pretty::emit_mir`)
  - `compiler/rustc_middle/src/mir/pretty.rs:317-377` (`write_mir_pretty` $\to$ `tcx.instance_mir`)
  - `compiler/rustc_middle/src/ty/mod.rs:1891-1907` (`instance_mir`)
  - `compiler/rustc_middle/src/ty/instance.rs:956-970` (`instantiate_mir_and_normalize_erasing_regions`)
  - `compiler/rustc_middle/src/queries.rs:644-677` (`mir_built`, `mir_promoted`, `mir_drops_elaborated_and_const_checked`, `optimized_mir`)
  - `compiler/rustc_mir_transform/src/lib.rs:244-318, 651-835` (`remap_mir_for_const_eval_select`, `run_runtime_cleanup_passes`, `run_optimization_passes`, `inner_optimized_mir`)
  - `compiler/rustc_mir_transform/src/pass_manager.rs:139-197` (`PassPolicy`, `should_run_pass`)
  - `compiler/rustc_mir_transform/src/remove_unneeded_drops.rs:44` (`PassPolicy::optional(true)`)
  - `compiler/rustc_mir_transform/src/remove_place_mention.rs:13` (`PassPolicy::optional(!ctx.opts.unstable_opts.mir_preserve_ub)`)
  - `compiler/rustc_mir_transform/src/inline.rs:74-96, 559-570` (`ForceInline` `PassPolicy::Required` and `fallback_intrinsics` inlining)
  - `compiler/rustc_mir_transform/src/shim.rs:28-206` (`mir_shims`)
  - `compiler/rustc_monomorphize/src/collector.rs:1006-1039, 1087-1093, 1329-1388` (`visit_instance_use`, `should_codegen_locally`, `collect_items_of_instance`)
  - `compiler/rustc_monomorphize/src/partitioning.rs:1169` (`collect_and_partition_mono_items`)
- **`deduced_param_attrs`, `FnAbi`, `PassMode::Cast`, and `ScalarPair` Layout:**
  - `compiler/rustc_mir_transform/src/deduce_param_attrs.rs:177-242` (`deduced_param_attrs`)
  - `compiler/rustc_ty_utils/src/abi.rs:290-315, 582-693` (`fn_abi_of_instance_no_deduced_attrs`, `fn_abi_new_uncached`, `fn_abi_adjust_for_deduced_attrs`)
  - `compiler/rustc_abi/src/lib.rs:2299-2306` (`TyAndLayout::is_aggregate`)
  - `compiler/rustc_abi/src/layout.rs:590-749` (`LayoutData::scalar_pair`, niche-encoded `ScalarPair` enum layout, `tag_field: FieldIdx::new(0)`)
  - `compiler/rustc_abi/src/callconv/reg.rs:9-95` (`Reg`, `RegKind`)
  - `compiler/rustc_target/src/callconv/mod.rs:238-424, 564-588, 772-1001` (`Uniform`, `CastTarget`, `PassMode`, `cast_to_maybe_noundef`, `adjust_for_rust_abi`, `fields_are_noundef`)
  - `compiler/rustc_target/src/callconv/x86_64.rs:29-268`, `aarch64.rs:20-159`, `riscv.rs:39-401`
- **Direct-MIR Codegen (`rustc_codegen_cranelift` vs. `rustc_codegen_ssa` / `rustc_codegen_llvm`):**
  - `compiler/rustc_codegen_cranelift/src/lib.rs:126-250`, `driver/aot.rs:150-395`, `base.rs:35-824`, `common.rs:88-105`, `analyze.rs:20-34`, `value_and_place.rs:58-841`, `discriminant.rs:95-103`, `abi/mod.rs:259-635`, `abi/pass_mode.rs:58-286`, `abi/returning.rs:10-128`, `constant.rs:370-491`, `unsize.rs:15-169`, `vtable.rs:12-88`
  - `compiler/rustc_codegen_ssa/src/mir/analyze.rs:76-168`, `mir/operand.rs:383-454, 734-965`, `mir/place.rs:297-315`, `mir/block.rs:613-648, 1288-1305, 2056-2104, 2503-2510`
  - `compiler/rustc_codegen_llvm/src/abi.rs:48-55, 193-204, 261-291`, `back/llvm_backend.rs:217-260`
- **Intrinsics and Sysroot `.rmeta` Caching:**
  - `compiler/rustc_middle/src/ty/intrinsic.rs:8-14`, `ty/util.rs:1713-1729` (`must_be_overridden: !has_body`)
  - `compiler/rustc_mir_build/src/builder/mod.rs:1052-1072`, `builder/expr/into.rs:407-485`
  - `compiler/rustc_mir_transform/src/lower_intrinsics.rs:22-336`
  - `compiler/rustc_session/src/session.rs:535-542` (`replaced_intrinsics`, `fallback_intrinsics`)
  - `library/core/src/intrinsics/{mod.rs,bounds.rs,fallback.rs,macros.rs,mir.rs,reflection.rs,simd/mod.rs,simd/scalable.rs}`, `library/core/src/num/imp/libm.rs:1-195`, `library/alloc/src/intrinsics.rs`
  - `compiler/rustc_metadata/src/rmeta/encoder.rs:1177-1207, 1932-2018`, `decoder.rs:1410-1412`, `decoder/cstore_impl.rs:248`
  - `src/tools/miri/src/lib.rs:190-207`, `src/tools/miri/cargo-miri/src/setup.rs:16-193`, `phases.rs:59-535`

### 2. Complete Theorem Inventory for `support/track1_abi_and_mono_probe.lean`

Preserved at `support/track1_abi_and_mono_probe.lean` (1,642 lines, SHA-256
`9035399af8255d9f6eb2ba42f69013beb0c014e6f7894bc3435f53ff75466f28`):

| Declaration Name | Kind | Lines | Role & Guarantee Established | Axioms (`#print axioms`) |
| :--- | :--- | :---: | :--- | :--- |
| `Preorder`, `Partial`, `Language`, `Compiles`, `Compiler`, `Compiler.SoundOn`, `Compiler.Verified`, `VerificationResultOn`, `SmallStepMachine`, `ReachesPrefix` | `class` / `structure` / `inductive` / `def` | 77–330 | Exact Layer 1A and Layer 1B refinement and small-step machine infrastructure (`Trusted/Refinement.lean`, `Trusted/StepResult.lean`). | — |
| `monotone_id`, `specOn_le_wellFormedOn`, `spec_le_wellFormed`, `Compiler.SoundOn.verify`, `Compiler.Verified.mono`, `Compiler.Verified.with_wellFormedOn` | `theorem` | 359–408 | Layer 1A refinement composition lemmas (`theory/Anneal/Refinement.lean`). | `[propext]` |
| `CValue`, `CPlace`, `LoweringStore`, `evalCValue`, `cplaceToCValue`, `cplaceWriteCValue` | `inductive` / `structure` / `def` | 420–498 | Direct-MIR SSA and stack-slot representation matching `rustc_codegen_cranelift/src/value_and_place.rs`. | — |
| `Anneal.cplace_write_read_roundtrip` | `theorem` | 500–540 | **Positive Theorem 1:** Proves write-then-read round-trip adequacy of `cplaceWriteCValue` and `cplaceToCValue` across `.var`, `.varPair`, and `.addr`. | `[propext]` |
| `PassMode`, `FnAbi`, `CalleeAction`, `CallProg`, `CallState`, `valMatchesPassMode`, `initCallState`, `evalMirCallStep`, `marshalByVal`, `evalAbiCallStep`, `MirCallLang`, `AbiCallLang`, `BuggyAbiCallLang` | `inductive` / `structure` / `def` | 574–887 | Models source `PostCleanup` MIR call semantics vs. `FnAbi`/`PassMode` (`ignore`, `direct`, `pair`, `cast`, `indirect readOnly`) marshaling with callee parameter aliasing. | — |
| `marshalByVal_of_matches`, `evalAbiCallStep_pc1_eq_mir`, `reachesPrefix_pc1_abi_to_mir`, `evalAbiCallStep_pc0_exists`, `abi_reachesPrefix_to_mir` | `theorem` | 889–1134 | Step-by-step backward simulation lemmas from `AbiCallMachine true` to `MirCallMachine`. | `[propext]` |
| `Anneal.abi_call_marshaling_refines`, `AbiLoweringCompiler`, `Anneal.abi_compiler_soundOn` | `def` / `theorem` | 1137–1190 | **Positive Theorem 2A/2B:** Proves `Compiles MirCallLang AbiCallLang (fun b => b) prog prog` and `AbiLoweringCompiler.SoundOn prog` across all valid `PassMode`s and operand modes (`copy`, `move`). | `[propext]` |
| `callerCalleeMutateProg`, `EnsuresCallerPreservedAndCalleeBumped`, `callerCalleeMutateProg_satisfies_spec`, `Anneal.caller_callee_mutate_verified` | `def` / `theorem` | 1192–1388 | **Positive Theorem 2C:** Discharges end-to-end `VerificationResultOn` with **zero TCB assumptions** (`assumptions := []`) when the caller passes `_1` by `Operand.copy` under `PassMode.indirect false` and the callee mutates `_1` in-place. | `[propext]` |
| `DropMirMachine`, `DropElidedMachine`, `Anneal.empty_drop_shim_refines` | `def` / `theorem` | 1416–1437 | **Positive Theorem 3A:** Proves refinement for eliding calls to `InstanceKind::DropGlue(_, None)` (`abi/mod.rs:492-498`). | `(none)` |
| `evalRustCallMir`, `evalRustCallSpreadAbi`, `Anneal.rust_call_spread_arg_refines` | `def` / `theorem` | 1444–1471 | **Positive Theorem 3B:** Proves observational equivalence of `ExternAbi::RustCall` tuple argument spreading (`fx.mir.spread_arg`). | `[propext]` |
| `Anneal.buggy_indirect_without_caller_copy_unsound` | `theorem` | 1497–1540 | **Negative Canary Theorem 4A:** Proves `¬ Compiles MirCallLang BuggyAbiCallLang (fun b => b) callerCalleeMutateProg callerCalleeMutateProg` when the caller omits the scratch copy on `Operand.copy`. | `[propext]` |
| `deducedReadOnlyMismatchProg`, `Anneal.deduced_readonly_phase_mismatch_unsound` | `def` / `theorem` | 1557–1637 | **Negative Canary Theorem 4B:** Proves `¬ Compiles MirCallLang AbiCallLang (fun b => b) deducedReadOnlyMismatchProg deducedReadOnlyMismatchProg` when `deduced_param_attrs` attaches `ReadOnly` from `optimized_mir` to a `PostCleanup` MIR callee with a dead parameter store. | `[propext]` |

### 3. Complete Theorem Inventory for `support/round2_track1_probe.lean`

Preserved at `support/round2_track1_probe.lean` (877 lines, SHA-256
`7d28a6692348dbbae30e190401f836d72c3922217d9a8bcf99778a7f2c48302a`):

| Declaration Name | Kind | Lines | Role & Guarantee Established | Axioms (`#print axioms`) |
| :--- | :--- | :---: | :--- | :--- |
| `Trusted.Preorder`, `Trusted.Partial`, `Trusted.Language`, `Trusted.Compiles`, `Trusted.Compiler.Verified` | `class` / `structure` / `def` | 53–110 | Layer 1A refinement infrastructure matching `trusted/lean/Trusted/Refinement.lean`. | — |
| `MaskedWord`, `PaddedStruct`, `paddedStructInitMask`, `packStructToMaskedWord`, `unpackStructFromMaskedWord` | `structure` / `def` | 126–168 | Models 64-bit cast words with per-bit initialization masks (`initMask`) and packs/unpacks `#[repr(C)] struct Padded { a: u8, b: u32 }` with 24 bits of uninitialized padding at bits `8..31`. | — |
| `pack_bits_extract_a`, `pack_bits_extract_b`, `pack_initMask_satisfies_padded` | `theorem` | 170–195 | Helper lemmas proving that packing `PaddedStruct` preserves `s.a` at bits `0..7`, `s.b` at bits `32..63`, and satisfies `paddedStructInitMask`. | `[propext, Quot.sound]` |
| `unpack_pack_padded_exact`, `unpack_pack_padding_irrelevant` | `theorem` | 197–215 | **Universal Round-Trip Theorem:** For all `s : PaddedStruct` and `padBits : BitVec 24`, `unpackStructFromMaskedWord (packStructToMaskedWord s padBits) = some s`. | `[propext, Quot.sound]` |
| `freezeMaskedWord`, `frozenToMaskedWord` | `def` | 229–238 | Per-bit `freeze` operation `(w.bits &&& w.initMask) \|\|\| (oracle &&& ~~~w.initMask)` and hardware `BitVec 64` embedding. | — |
| `freezeMaskedWord_preserves_initialized_bits` | `theorem` | 240–248 | Proves `(freezeMaskedWord oracle w) &&& w.initMask = w.bits &&& w.initMask` for all `oracle` and `w`. | `[propext, Classical.choice, Quot.sound]` |
| `unpack_frozen_pack_padded_exact` | `theorem` | 250–293 | Proves that unpacking a frozen `MaskedWord` recovers `some s` for every `oracle : BitVec 64` and `padBits : BitVec 24`. | `[propext, Classical.choice, Quot.sound]` |
| `CastSourceLang`, `CastTargetLang`, `compilePassModeCast`, `passModeCast_freeze_compiles`, `passModeCast_freeze_verified` | `def` / `theorem` | 325–395 | **Layer 1A Refinement Theorems:** Proves `Trusted.Compiles` and `Trusted.Compiler.Verified` for `PassMode::Cast` `freeze` lowering across all `oracle : BitVec 64`. | `[propext, Classical.choice, Quot.sound]` |
| `wholeWordLoadWithoutFreeze`, `NaiveWholeWordTargetLang`, `canary_whole_word_poison_on_padding_unsound` | `def` / `theorem` | 409–445 | **Negative Canary Theorem:** Proves that a naive whole-word `i64` load without per-byte `freeze` yields `none` (whole-word poison) on `PaddedStruct` and violates `Trusted.Compiles`. | `[propext, Quot.sound]` |
| `ScalarPairVal`, `extractScalarPairByOffset`, `extractScalarPairByFieldIdx`, `canary_fieldIdx_projection_mismatch_on_niche_in_snd` | `structure` / `def` / `theorem` | 487–522 | **`ScalarPair` Projection Canary:** Proves that `FieldIdx` dispatch reads `fst` instead of `snd` when `tag_field = FieldIdx(0)` has `niche_offset = b_offset = 8`, whereas byte-offset dispatch reads `snd`. | `(none)` |
| `extractByteAt`, `insertByteAt`, `extractScalarPairByte`, `insertScalarPairByte` | `def` | 532–558 | Sub-word byte extraction and insertion at `(inSnd : Bool, byteOff : Fin 8)` in `ScalarPairVal`. | — |
| `extractByteAt_insertByteAt_exact`, `extractByteAt_insertByteAt_other_bytes_preserved`, `extractScalarPairByte_insertScalarPairByte_exact`, `insertScalarPairByte_preserves_other_reg` | `theorem` | 560–631 | Proves universal bit-exact round-trip of the written byte and preservation of all other 7 bytes in the selected register (plus preservation of the unselected register) for all `byteOff : Fin 8`. | `[propext, Classical.choice, Quot.sound]` |
| `encodeScalarPairSubwordNiche`, `decodeScalarPairSubwordNiche`, `decode_encode_subword_niche_byte`, `scalarPair_decode_encode_niche_tagged`, `scalarPair_decode_encode_niche_untagged` | `def` / `theorem` | 651–740 | **Sub-Word Niche Round-Trip Theorems:** Proves that sub-word wrapping niche encoding and decoding at any `(inSnd, byteOff)` recovers all tagged variants (`v < 4, v ≠ 1`) and all valid untagged payloads (`1..=253`). | `[propext, Classical.choice, Quot.sound]` / `[propext, Quot.sound]` |
| `f64SignMask`, `fabsBits64`, `copysignBits64`, `fabsBits64_spec`, `copysignBits64_spec`, `fabsBits64_eq_copysign_posZero` | `def` / `theorem` | 759–813 | Proves that the pure-Rust bit-manipulation fallback bodies of `fabs` and `copysignf64` satisfy the exact IEEE 754-2019 sign and payload preservation specifications. | `[propext, Classical.choice, Quot.sound]` |

---

## Revalidation

To revalidate both standalone Lean 4.34.1 mechanization probes from the root of
this report package
(`reports/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/`) and
confirm exit code `0`, zero warnings, zero `sorryAx`, and zero
`Lean.ofReduceBool`, run:

```bash
lean -j1 -M1024 support/track1_abi_and_mono_probe.lean
lean -j1 -M1024 support/round2_track1_probe.lean
```

(using `leanprover/lean4:v4.34.1` at commit
`5045d0056413266e57c625dcd7c365b10e377c52`).

Revalidate this report and its probes whenever:
1. Anneal updates its pinned `rust-lang/rust` commit hash:
   - Check `run_runtime_cleanup_passes` and `run_optimization_passes` in
     `compiler/rustc_mir_transform/src/lib.rs` for any newly added pass whose
     `PassPolicy` is active at `mir_opt_level == 0`.
   - Check `compiler/rustc_mir_transform/src/deduce_param_attrs.rs` and
     `compiler/rustc_ty_utils/src/abi.rs` to verify that `-Copt-level=0` and
     `fn_abi_of_instance_no_deduced_attrs` still suppress all deduced parameter
     attributes.
   - Re-scan `library/core/src/intrinsics/` and `library/alloc/src/intrinsics.rs`
     for any new `#[rustc_intrinsic]` declarations or changes to
     `intrinsic_dispatch_on_type!`.
2. `compiler/rustc_abi/src/layout.rs` or `compiler/rustc_target/src/callconv/`
   alters `LayoutData::scalar_pair`, `TagEncoding::Niche`, or
   `FnAbi::adjust_for_rust_abi`.
