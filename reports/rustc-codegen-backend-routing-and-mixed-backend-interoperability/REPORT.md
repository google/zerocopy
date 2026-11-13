# `rustc` Codegen-Backend Routing Architecture and Mixed-Backend Interoperability

## Summary

`rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`) separates frontend
type-checking, borrow-checking, and `Runtime(PostCleanup)` MIR construction from
machine-code generation through the `CodegenBackend` trait in
`compiler/rustc_codegen_ssa/src/traits/backend.rs`. All three in-tree backends—
`rustc_codegen_llvm` (`LlvmCodegenBackend`), `rustc_codegen_cranelift`
(`CraneliftCodegenBackend` via `driver::aot::AotDriver`), and `rustc_codegen_gcc`
(`GccCodegenBackend`)—feed `rustc_codegen_ssa::base::codegen_crate`, which
partitions monomorphized items into codegen units (`CodegenUnit`) and dispatches
each unit through `ExtraBackendMethods::compile_codegen_unit` and
`WriteBackendMethods::{optimize, codegen}`.

A composite backend can route compilation between a verified backend and an
unverified optimizing backend (such as LLVM 23.1.1,
`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) at three granularities:

1. **Per-crate routing via Cargo profile overrides** (`cargo-features =
   ["codegen-backend"]` with `[profile.<prof>.package.<pkg>] codegen-backend =
   "..."`), which compiles whole `.rlib` crates with distinct backends and links
   their native object files via `link_binary`.
2. **Per-codegen-unit (`CodegenUnit`) routing inside `ExtraBackendMethods` and
   `WriteBackendMethods`**, wrapping backend-specific modules in a sum type
   `enum CompositeModule { Llvm(ModuleLlvm), Alt(AltModule) }` and dispatching
   `compile_codegen_unit`, `optimize`, and `codegen` per unit.
3. **Per-function (`MonoItem::Fn`) routing**, achieved either by splitting routed
   functions into dedicated codegen units during `collect_and_partition_mono_items`
   or by emitting `MonoItem::Fn` declarations (`Linkage::External`,
   `Visibility::Hidden` for formerly `Internal` items) across sibling backend
   modules within the same codegen unit.

Empirical prototyping and 32-seed randomized per-CGU fuzzing of a loadable
composite backend (`CompositeModule { Llvm(ModuleLlvm), Clif(AotModule) }`) on
`rustc` 1.99.1 establish that six cross-backend invariants govern soundness and
linkability when mixing compilation paths:

- **Target configuration parity (`CodegenBackend::target_config`)**: The
  composite backend must report a sound intersection of `has_reliable_f16`,
  `has_reliable_f128`, and target features (`internal_target_features`);
  otherwise ABI checks and `#[cfg(target_feature = "...")]` diverge across
  units (for example, `CraneliftCodegenBackend::target_config` ignores
  `-Ctarget-feature=+avx`, causing `rustc` to reject 256-bit `#[repr(simd)]`
  `extern "C"` signatures).
- **Intrinsic fallback retention (`CodegenBackend::replaced_intrinsics`)**:
  `rustc_monomorphize::collector` skips collecting MIR fallback bodies for every
  symbol in `replaced_intrinsics()`. A composite backend must return the
  **intersection** $\text{Replaced}_A \cap \text{Replaced}_B$, not the union;
  returning `LlvmCodegenBackend::replaced_intrinsics()` (36 symbols including
  `carryless_mul`, `unchecked_funnel_shl`, `carrying_mul_add`, and `f16`/`f32`/
  `f64` math intrinsics) when routing a caller CGU to Cranelift produces
  unresolved-symbol linker errors (`rust-lld: error: undefined symbol:
  core::intrinsics::carryless_mul::<u64>`).
- **Query provider registration (`CodegenBackend::provide`)**: Any composite
  backend that delegates even one CGU to `LlvmCodegenBackend` must register
  `providers.queries.global_backend_features` via `LlvmCodegenBackend::provide`
  and initialize LLVM in `CodegenBackend::init`.
- **Unwind landing-pad and LSDA compatibility**: Walking through frames requires
  `.eh_frame` DWARF CFI (or Windows `.pdata`/`.xdata`), which Cranelift emits
  by default, but executing `Drop` destructors (`UnwindAction::Cleanup`) and
  catching panics (`core::intrinsics::catch_unwind`) requires `.gcc_except_table`
  LSDA landing pads. Because `rustc_codegen_cranelift` disables its `unwinding`
  Cargo feature by default, unwinding from an LLVM CGU through a Cranelift CGU
  reaches an outer LLVM `catch_unwind` frame (`res = true`) while **silently
  skipping `Drop::drop` destructors in the Cranelift frame (`dropped = 0`)**,
  and routing the CGU containing `std::panic::catch_unwind` to Cranelift causes
  uncaught panic aborts in 18 of 32 random CGU assignments.
- **128-bit atomic and SIMD ABI capabilities**: Routing functions that execute
  128-bit atomic RMW operations (`atomic_xadd::<u128, u128, SeqCst>` under
  `+cmpxchg16b` or AArch64 baseline) to Cranelift panics in ISLE instruction
  selection (`Unsupported("should be implemented in ISLE: inst = atomic_rmw.i128
  add ...")`), whereas routing that single CGU to LLVM while keeping the rest of
  the crate on Cranelift compiles and executes cleanly.
- **LTO bitcode boundary (`-Clto=thin`, `-Clto=fat`)**: LLVM Fat LTO and ThinLTO
  require `.llvmbc` bitcode sections (`ModuleBuffer`) in every participating
  in-memory CGU and `.rlib` object. Passing a Cranelift `.rlib` to an LLVM
  `-Clto=thin` or `-Clto=fat` link fails with `error: failed to get bitcode from
  object file for LTO (Can't find section .llvmbc)`, and passing a non-LLVM
  `CompositeModule` into `run_thin_lto` or `optimize_and_codegen_fat_lto` traps
  unless non-LLVM CGUs are partitioned into pre-compiled object modules whose
  referenced symbols are added to `exported_symbols_for_lto`.

## Applicability

- **Primary baseline**: `rust-lang/rust` release `1.99.1`
  (`58cf8f9c35b355199727627d07ae34a4e2846d67`, 2026-10-13) and its pinned
  `rust-lang/llvm-project` submodule (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`,
  LLVM 23.1.1), cross-checked against `1.100.0`
  (`0ef1bc386059596dada8fb65b50425aab2ea637a`) and `nightly-2026-11-12`
  (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).
- **Backends examined**: `rustc_codegen_llvm`, `rustc_codegen_cranelift` (using
  `cranelift-codegen` `0.134.0`), `rustc_codegen_gcc` (`gccjit` `3.3.0`), and a
  prototype composite backend (`librustc_codegen_composite.so`) combining
  `LlvmCodegenBackend` and `CraneliftCodegenBackend`/`AotDriver` inside a single
  `rustc` 1.99.1 process.
- **Scope**: Trait interfaces, dynamic backend loading, monomorphization and CGU
  partitioning hooks, allocator/metadata modules, Cargo per-package backend
  selection, per-function optimization attributes (`#[optimize]`, `#[inline]`),
  and cross-backend ABI/unwinding/atomic/LTO interoperability.

## Findings

### 1. Backend Trait Hierarchy, Loading Protocol, and In-Tree Implementations

`Basis: source + execution`

#### 1.1 `CodegenBackend`, `ExtraBackendMethods`, `WriteBackendMethods`, and Builder Traits

`compiler/rustc_codegen_ssa/src/traits/` divides the backend contract into four
layers:

1. **Driver-level lifecycle (`CodegenBackend`, `traits/backend.rs:36-161`)**:
   Invoked by `rustc_interface::queries::Linker::codegen_and_build_linker` and
   `rustc_driver_impl`. Key methods and their cross-backend roles are:

| Method | Signature (`traits/backend.rs`) | Default Behavior | Role in Multi-Backend / Composite Routing |
| :--- | :--- | :--- | :--- |
| `name` | `fn name(&self) -> &'static str` | (required) | Identifies backend in profiling, diagnostics, and `link_binary`. |
| `init` | `fn init(&self, _sess: &Session)` | No-op | Initializes backend globals (e.g., `llvm_util::init(sess)`, `dlopen("libgccjit.so")`, LTO/coverage flag validation). |
| `provide` | `fn provide(&self, _providers: &mut Providers)` | No-op | Overrides `TyCtxt` queries. `LlvmCodegenBackend` overrides `global_backend_features` (`llvm/src/lib.rs:248-251`). |
| `target_config` | `fn target_config(&self, _sess: &Session) -> TargetConfig` | Empty features; `has_reliable_f16/f128 = true` | Populates `cfg(target_feature = ...)` and `has_reliable_f16`/`f128` (`session.rs`). |
| `replaced_intrinsics` | `fn replaced_intrinsics(&self) -> Vec<Symbol>` | `vec![]` | Tells `rustc_monomorphize::collector` which intrinsic fallback MIR bodies NOT to collect. |
| `fallback_intrinsics` | `fn fallback_intrinsics(&self) -> Vec<Symbol>` | `vec![]` | Tells `rustc_monomorphize` which intrinsic fallback bodies may be MIR-inlined (`vec![sym::type_id_eq]`). |
| `thin_lto_supported` | `fn thin_lto_supported(&self) -> bool` | `true` | Controls whether `Lto::ThinLocal` / `Lto::Thin` runs ThinLTO (`false` in Cranelift and GCC). |
| `metadata_loader` | `fn metadata_loader(&self) -> Box<MetadataLoaderDyn>` | `DefaultMetadataLoader` (native archive/object reader via `object`) | Reads `.rmeta` from `.rlib` and `.so`/`.dylib`/`.dll`. |
| `codegen_crate` | `fn codegen_crate<'tcx>(&self, tcx: TyCtxt<'tcx>) -> Box<dyn Any>` | (required) | Runs monomorphization, CGU partitioning, and parallel codegen coordinator (`OngoingCodegen<B>`). |
| `join_codegen` | `fn join_codegen(&self, ongoing: Box<dyn Any>, ...) -> (CompiledModules, WorkProductMap)` | (required) | Joins background worker threads and returns `CompiledModules` (`modules`, `allocator_module`). |
| `link` | `fn link(&self, sess: &Session, compiled_modules: CompiledModules, ...)` | Calls `link_binary` with `ArArchiveBuilderBuilder` | Packs `.rlib`/`staticlib` archives or invokes the platform linker for executables/dylibs. |

2. **Per-CGU IR generation (`ExtraBackendMethods`, `traits/backend.rs:163-180`)**:
   Requires `type Module` and two methods called from `rustc_codegen_ssa::base::codegen_crate`
   (`base.rs:751-879`):
   - `fn codegen_allocator<'tcx>(&self, tcx: TyCtxt<'tcx>, module_name: &str, methods: &[AllocatorMethod]) -> Self::Module`
   - `fn compile_codegen_unit(&self, tcx: TyCtxt<'_>, cgu_name: Symbol) -> (ModuleCodegen<Self::Module>, u64)`

3. **Back-end optimization, LTO, and object emission (`WriteBackendMethods`,
   `traits/write.rs:16-81`)**:
   Parameterized by associated types `Module: Send + Sync`, `TargetMachine`,
   `ModuleBuffer: ModuleBufferMethods`, and `ThinData: Send + Sync`. Invoked by
   the background worker coordinator in `rustc_codegen_ssa::back::write`:
   - `target_machine_factory(&self, sess: &Session, opt_level: OptLevel, target_features: &[String]) -> TargetMachineFactoryFn<Self>`
   - `optimize(cgcx, prof, shared_emitter, module: &mut ModuleCodegen<Self::Module>, config: &ModuleConfig)`
   - `codegen(cgcx, prof, shared_emitter, module: ModuleCodegen<Self::Module>, config: &ModuleConfig) -> CompiledModule`
   - `serialize_module(module: Self::Module, is_thin: bool) -> Self::ModuleBuffer`
   - `optimize_and_codegen_fat_lto(..., modules: Vec<FatLtoInput<Self>>) -> CompiledModule`
   - `run_thin_lto(..., modules: Vec<ThinLtoInput<Self>>) -> (Vec<ThinModule<Self>>, Vec<WorkProduct>)`
   - `optimize_and_codegen_thin(..., thin: ThinModule<Self>) -> CompiledModule`

4. **MIR-to-SSA lowering builder traits (`traits/mod.rs:34-98`)**:
   Backends that use `rustc_codegen_ssa::mir::codegen_mir` (specifically
   `rustc_codegen_llvm` and `rustc_codegen_gcc`) implement `CodegenCx` traits
   (`BackendTypes`, `AbiBuilderMethods`, `AsmCodegenMethods`,
   `ConstCodegenMethods`, `CoverageInfoBuilderMethods`, `DebugInfoCodegenMethods`,
   `LayoutTypeCodegenMethods`, `MiscCodegenMethods`, `PreDefineCodegenMethods`,
   `StaticCodegenMethods`, `TypeMembershipCodegenMethods`) and `BuilderMethods`
   (`traits/builder.rs`, `AsmBuilderMethods`, `IntrinsicCallBuilderMethods`).
   By contrast, `rustc_codegen_cranelift` does **not** use
   `rustc_codegen_ssa::mir::codegen_mir` or `BuilderMethods`; instead, its
   `driver::aot::AotDriver` (`compiler/rustc_codegen_cranelift/src/driver/aot.rs:267-391`)
   implements `ExtraBackendMethods` and `WriteBackendMethods` directly and lowers
   MIR to Cranelift CLIF IR in `compiler/rustc_codegen_cranelift/src/base.rs`.

#### 1.2 Dynamic Backend Loading (`get_codegen_backend`)

In `compiler/rustc_interface/src/util.rs:320-430`, `get_codegen_backend` resolves
`-Zcodegen-backend=<name_or_path>` (or the target spec's
`default_codegen_backend`):
- Built-in `"llvm"` calls `rustc_codegen_llvm::LlvmCodegenBackend::new()`.
- Any path containing `.` or `/` or `\` is loaded directly via
  `libloading::Library::new(path)`; bare names search
  `<sysroot>/lib/rustlib/<host>/codegen-backends/librustc_codegen_<name>-*.so`.
- The dylib must export:
  ```rust
  pub extern "Rust" fn __rustc_codegen_backend() -> Box<dyn CodegenBackend>
  ```
- Because `librustc_driver-<hash>.so` in the standard `1.99.1` toolchain already
  statically links `rustc_codegen_llvm` and exports
  `rustc_codegen_llvm::LlvmCodegenBackend` symbols (`nm -D librustc_driver-*.so`),
  an external backend dylib compiled with `extern crate rustc_codegen_llvm;` can
  instantiate and delegate to `LlvmCodegenBackend` in-process without
  duplicating LLVM or `rustc` state.

---

### 2. Routing Hook Points and Structural Constraints

`Basis: source + execution`

#### 2.1 Four Candidate Hook Points in the Compilation Pipeline

| Hook Point | Source Location (`s1991`) | Granularity | Capabilities & Limitations |
| :--- | :--- | :--- | :--- |
| **1. Cargo per-package profile override** | `src/tools/cargo/src/cargo/core/profiles.rs` (`cargo-features = ["codegen-backend"]`) | Whole crate (`.rlib`) | Supported today in `cargo +1.99.1` with `RUSTC_BOOTSTRAP=1`. Requires no `rustc` modifications. Cannot split functions within a single crate; generic functions instantiated in a downstream crate are compiled by the downstream crate's backend. |
| **2. CGU partitioning (`collect_and_partition_mono_items`)** | `compiler/rustc_monomorphize/src/partitioning.rs:144-610` | Per-function (`MonoItem`) grouped into backend-tagged CGUs | `place_mono_items` assigns each `MonoItem` (`Fn`, `Static`, `GlobalAsm`) to a `CodegenUnit`. A custom partitioner (or post-pass before `base.rs:737`) can split verified vs. unverified `MonoItem`s into disjoint CGUs, provided cross-CGU `Linkage::Internal` items are promoted to `Linkage::External` + `Visibility::Hidden` (`partitioning.rs:360-440`). |
| **3. Per-CGU dispatch (`ExtraBackendMethods` + `WriteBackendMethods`)** | `compiler/rustc_codegen_ssa/src/base.rs:751-879`, `back/write.rs` | Per `CodegenUnit` (`.rcgu.o`) and allocator module | Cleanest in-process boundary: `compile_codegen_unit(tcx, cgu_name)` returns `ModuleCodegen<CompositeModule>`, and worker threads dispatch `optimize` and `codegen` per variant to produce standard `CompiledModule` `.rcgu.o` files merged by `link_binary`. |
| **4. Intra-CGU `MonoItem` dispatch** | `compiler/rustc_codegen_llvm/src/base.rs:101-145` / `cranelift/src/driver/aot.rs:147-204` | Individual `MonoItem::Fn` | Splits a single `CodegenUnit` into two `.o` files (`<cgu>.llvm.o` and `<cgu>.alt.o`), predefining cross-file items as external declarations with hidden visibility. More invasive than Hook 2 + Hook 3 because `CompiledModule` assumes at most one primary `object: Option<PathBuf>` and one `global_asm_object: Option<PathBuf>` per CGU (`rustc_codegen_ssa/src/lib.rs:67-84`). |

#### 2.2 Allocator-Shim and Metadata Modules

- **Allocator shim (`base.rs:751-762`)**: When `allocator_kind_for_codegen(tcx)`
  is `Some(_)`, `codegen_crate` calls
  `backend.codegen_allocator(tcx, &llmod_id, &allocator_shim_contents(tcx, kind))`
  to emit `__rust_alloc`, `__rust_dealloc`, `__rust_realloc`,
  `__rust_alloc_zeroed`, `__rust_alloc_error_handler`, and
  `__rust_no_alloc_shim_is_unstable_v2`. Both `LlvmCodegenBackend`
  (`llvm/src/allocator.rs`) and `AotDriver` (`cranelift/src/allocator.rs`) emit
  identical C-ABI thin forwarding wrappers, so the allocator module can be
  routed to either backend (note that `<crate>.allocator` is not a registered
  `tcx.codegen_unit(name)` query key, so a router inspecting `tcx.codegen_unit`
  must guard against the allocator module name).
- **Crate metadata (`lib.rmeta`)**: Written by `rustc_codegen_ssa::back::link::link_binary`
  independently of `ExtraBackendMethods` using `ArArchiveBuilderBuilder` /
  `LlvmArchiveBuilderBuilder`, so `.rmeta` generation is completely invariant
  under per-CGU routing.

#### 2.3 Selection Mechanisms and Composition with Inlining and LTO

- **Rust `#[optimize(size | speed | none)]` (`compiler/rustc_codegen_llvm/src/attributes.rs:58-81, 483-495`)**:
  - `OptimizeAttr::DoNotOptimize` (`#[optimize(none)]`) forces
    `InlineAttr::Never` in `inline_attr` (`attributes.rs:62`, emitting LLVM
    `noinline` alongside `optnone`, because LLVM's verifier rejects `optnone`
    without `noinline`) and skips per-function optimization passes in LLVM.
  - However, in `rustc_codegen_cranelift`, `OptimizeAttr` on individual functions
    is **ignored** (`cranelift/src/lib.rs:303-314` sets `opt_level` globally on
    the ISA `TargetIsa` from `sess.opts.optimize`), and in `rustc_mir_transform`,
    MIR inlining (`compiler/rustc_mir_transform/src/inline.rs`) checks
    `codegen_fn_attrs.inline` (`InlineAttr::Never` blocks MIR inlining into or of
    the function, but `OptimizeAttr::DoNotOptimize` alone does not set
    `codegen_fn_attrs.inline = InlineAttr::Never` at the HIR/MIR layer—only
    `rustc_codegen_llvm::attributes::inline_attr` maps `(_, DoNotOptimize) =>
    InlineAttr::Never`!).
  - **Verification consequence**: If a function carries a per-function routing
    attribute (e.g., `#[verified]` or `#[optimize(none)]`), **MIR inlining
    (`-Zinline-mir`) will inline unverified callees into a verified caller (or
    vice versa) prior to `collect_and_partition_mono_items` unless the MIR
    inliner in `compiler/rustc_mir_transform/src/inline.rs` explicitly checks
    that caller and callee share a compatible backend routing domain.**
- **Generic monomorphizations and cross-crate inlining (`#[inline]`)**:
  - Generic functions and `#[inline]` non-generic functions are exported as
    encoded MIR in `lib.rmeta` and instantiated in every downstream crate (and
    every calling CGU when `InstantiationMode::LocalCopy` is chosen by
    `partitioning.rs`). Under per-crate routing, a generic function defined in a
    verified library crate is monomorphized and compiled by the **downstream
    caller crate's backend** unless instantiated through a non-generic wrapper
    or routed per-item at the CGU level.

---

### 3. Empirical Mixed-Backend and Per-CGU Routing Experiments

`Basis: execution + source`

Using `librustc_codegen_composite.so` (a patched build of `rustc_codegen_cranelift`
on `rustc` 1.99.1 that links `rustc_codegen_llvm` and dispatches
`ExtraBackendMethods` and `WriteBackendMethods` per CGU via `CompositeModule`,
preserved in `support/composite_backend_patch.diff` and `support/v1_probe_results.json`),
we executed six targeted experiments and a 32-seed randomized CGU routing fuzz
campaign (`-Ccodegen-units=8 -Copt-level=2`).

| Experiment / Probe (`support/v1_probe_results.json`) | Routing Configuration | Compile Status | Runtime / Link Outcome | Root Cause & Invariant |
| :--- | :--- | :--- | :--- | :--- |
| **1. Cargo per-package mixed workspace** (`clif_dep` on Cranelift + `llvm_app` on LLVM) | `profile.dev.package.clif_dep.codegen-backend = ".../librustc_codegen_cranelift.so"` | `rc = 0` | `cargo test` passes (`1 passed; 0 failed`) across `u128` return pairs and `&dyn Processor` vtable calls | `FnAbi` layout, vtable layout, and `x86_64` SysV calling conventions match for scalars, pairs, structs, and trait objects (`enable_llvm_abi_extensions = true`). |
| **2. Unwind `Drop` destructor across mixed CGUs** (`probe1_unwind_drop.rs`) | `llvm_callee::trigger_panic` on LLVM; `clif_frame::call_with_guard` (with `DropGuard`) on Cranelift | `rc = 0` | `catch_unwind` catches panic (`res = true`), **but `dropped = 0`** (`rc = 101` assertion failure) | Cranelift emits `.eh_frame` DWARF CFI so `libgcc_s` unwinds through the frame, but omits `.gcc_except_table` LSDA landing pads when built without `--features unwinding`. |
| **3. Intrinsic replacement mismatch** (`probe2_intr_fixed.rs`: `carryless_mul`, `unchecked_funnel_shl`, `carrying_mul_add`) | `replaced_intrinsics()` = LLVM's 36 intrinsics (`AN_COMPOSITE_LLVM_INTRINSICS=1`); CGU routed to Cranelift | `rc = 1` (link error) | `rust-lld: error: undefined symbol: core::intrinsics::carryless_mul::<u64>` (and `unchecked_funnel_shl`, `carrying_mul_add`) | `rustc_monomorphize::collector` skips fallback MIR bodies for symbols in `replaced_intrinsics()`. Returning `vec![]` (`AN_COMPOSITE_LLVM_INTRINSICS=0`) or routing `intr_mod` to LLVM succeeds (`rc = 0`, `clmul=127 funnel=16 cmul=(23, 0)`). |
| **4. SIMD vector ABI (`F32x4` vs `F32x8`)** (`probe3_f32x4.rs`, `probe3_simd2.rs`) | `F32x4` (128-bit) and `F32x8` (256-bit) across LLVM and Cranelift CGUs (`extern "Rust"` and `extern "C"`) | `F32x4`: `rc = 0`; `F32x8`: `rc = 1` | `F32x4` passes (`[11.0, 22.0, 33.0, 44.0]`); `F32x8` rejected by `rustc` ABI check even with `-Ctarget-feature=+avx` | `CraneliftCodegenBackend::target_config` hardcodes `[fxsr, sse, sse2, x87]` on `x86_64` and ignores `-Ctarget-feature=+avx`, blocking `F32x8` `extern "C"` ABI checks. |
| **5. 128-bit atomics (`+cmpxchg16b`)** (`probe4_atom128_2.rs`: `atomic_xadd::<u128>`) | `all_clif` vs `llvm_if:bump128` (only `cgu.2` on LLVM, 7 CGUs on Cranelift) | `all_clif`: `rc = 101` (ICE); `llvm_if:bump128`: `rc = 0` | `all_clif` panics in ISLE (`Unsupported("... atomic_rmw.i128 add ...")`); routing `cgu.2` to LLVM runs cleanly (`prev = 100`) | Selective per-CGU routing to LLVM cleanly bypasses backend instruction-selection gaps while keeping the rest of the crate on the alternate backend. |
| **6. 32-seed randomized CGU fuzzer & LTO** (`test_composite.rs`, 8 CGUs) | `hash:0..31` with `-Clto=no`, `-Clto=thin`, `-Clto=fat`; plus Cranelift `.rlib` into LLVM `-Clto=thin/fat` | `-Clto=no`: 32/32 compile; `-Clto=thin/fat`: `rc = 1` / `101` | `-Clto=no`: 14/32 pass, 18/32 abort in `catch_unwind`; `-Clto=thin/fat` fails (`Can't find section .llvmbc` / `Cannot serialize Cranelift AotModule`) | The 14 passing seeds are exactly those where the CGU containing `std::panic::catch_unwind` is assigned to LLVM; LTO requires `.llvmbc` bitcode or pre-LTO partitioning of non-LLVM CGUs. |

#### 3.1 Cross-Crate `deduced_param_attrs` Obligation

In `compiler/rustc_mir_transform/src/deduce_param_attrs.rs:174-239`, when
`tcx.sess.opts.optimize != OptLevel::No` and incremental compilation is disabled,
`rustc` analyzes the `optimized_mir` of every function with indirect parameters,
deduces `ReadOnly`, `CapturesNone`, and `CapturesReadOnly` whenever the MIR body
does not mutate or capture a `Freeze` parameter, and **records `DeducedParamAttrs`
in `lib.rmeta`**. When an LLVM-compiled caller invokes a function compiled by
another backend, `rustc_ty_utils::abi::fn_abi_new_uncached` attaches LLVM
`readonly` and `captures(none)` attributes to the call site based on the callee's
MIR summary. Any alternative backend compiling that callee **must not introduce
hidden writes to by-value indirect parameter stack slots** (such as reusing the
caller's `PassMode::Indirect { on_stack: false }` buffer as scratch space), or
LLVM will miscompile the caller by assuming the caller's memory remains unchanged
across the call.

## Boundaries

- **Cranelift `unwinding` feature (`not examined` in production builds)**:
  `rustc_codegen_cranelift/Cargo.toml` defines an optional `unwinding = []`
  feature (marked `# Not yet included in unstable-features for performance
  reasons`). Standard `rustup` distributions of `rustc-codegen-cranelift-preview`
  do not enable this feature.
- **`rustc_codegen_gcc` per-CGU mixing (`known not to apply` with stock
  `libgccjit.so.15`)**: `rustc_codegen_gcc` implements `ExtraBackendMethods` and
  `WriteBackendMethods`, so the exact same `CompositeModule` architecture applies
  to mixing LLVM and GCC CGUs, but compiling `core` or complex Rust crates with
  `rustc_codegen_gcc` requires the patched `rust-lang/gcc` `libgccjit.so` fork
  (`6f155cc3f5a2dff33afe6cc3ed6c2e0e605ae6a3`), not stock Debian GCC 15
  `libgccjit.so.15`.

## Evidence

- **Primary source citations (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`)**:
  - `compiler/rustc_codegen_ssa/src/traits/backend.rs:20-180` (`BackendTypes`,
    `CodegenBackend`, `ExtraBackendMethods`).
  - `compiler/rustc_codegen_ssa/src/traits/write.rs:16-91`
    (`WriteBackendMethods`, `ModuleBufferMethods`).
  - `compiler/rustc_codegen_ssa/src/base.rs:724-899` (`codegen_crate`,
    `collect_and_partition_mono_items`, `codegen_allocator`,
    `compile_codegen_unit`).
  - `compiler/rustc_interface/src/util.rs:320-430` (`get_codegen_backend`,
    `__rustc_codegen_backend` symbol lookup).
  - `compiler/rustc_codegen_llvm/src/lib.rs:120-460` (`LlvmCodegenBackend`
    implementations of `WriteBackendMethods` and `CodegenBackend`,
    `replaced_intrinsics` at lines 329-361).
  - `compiler/rustc_codegen_cranelift/src/lib.rs:120-247` and
    `compiler/rustc_codegen_cranelift/src/driver/aot.rs:147-391`
    (`CraneliftCodegenBackend` and `AotDriver`).
  - `compiler/rustc_codegen_gcc/src/lib.rs:172-360` (`GccCodegenBackend`).
  - `compiler/rustc_monomorphize/src/partitioning.rs:144-610` (`partition`,
    `place_mono_items`, `internalize_symbols`).
  - `compiler/rustc_mir_transform/src/deduce_param_attrs.rs:174-239`
    (`deduced_param_attrs`).
- **Support artifacts**:
  - `support/composite_backend_patch.diff`: Unified diff against
    `compiler/rustc_codegen_cranelift/src/driver/aot.rs` implementing
    `CompositeModule { Llvm(ModuleLlvm), Clif(AotModule) }` per-CGU routing.
  - `support/v1_probe_results.json`: Machine-readable results from the six
    cross-backend probes and 32-seed randomized CGU fuzzer.

## Revalidation

To revalidate the composite backend routing invariants on a newer `rustc`
revision:

1. Diff `compiler/rustc_codegen_ssa/src/traits/{backend.rs,write.rs}` and
   `compiler/rustc_codegen_llvm/src/lib.rs` (`replaced_intrinsics`) against
   `58cf8f9c35b355199727627d07ae34a4e2846d67`:
   ```console
   git -C <rust-checkout> diff 58cf8f9c35b355199727627d07ae34a4e2846d67 -- \
     compiler/rustc_codegen_ssa/src/traits/backend.rs \
     compiler/rustc_codegen_ssa/src/traits/write.rs \
     compiler/rustc_codegen_llvm/src/lib.rs
   ```
2. Apply `support/composite_backend_patch.diff` to a copy of
   `compiler/rustc_codegen_cranelift`, build with `RUSTC_BOOTSTRAP=1 cargo build
   --release`, and verify that mixed CGU compilation emits both LLVM and
   Cranelift producer strings in `readelf -p .comment` and reproduces the outcomes
   in `support/v1_probe_results.json`.
