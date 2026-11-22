# `rustc_codegen_cranelift` vs. `rustc_codegen_llvm`: Differential `CodegenBackend` Parity, Cross-Backend ABI Interoperability, Unwind/LSDA Asymmetry, and Security-Flag Soundness

## Summary

Comparing `rustc_codegen_cranelift` (`cranelift-codegen 0.137.0`) against `rustc_codegen_llvm` (`LLVM 23.1.5`) in `rust-lang/rust` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, with source continuity confirmed at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` and LLVM revalidation at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) establishes six load-bearing ground-truth properties for any drop-in or verified `rustc` `CodegenBackend`:

1. **100% Non-Panicking Binary ABI Interoperability Across Mixed-Backend Crate Boundaries:** Because both `rustc_codegen_cranelift` and `rustc_codegen_llvm` lower from the exact same `rustc_target::callconv::FnAbi` / `PassMode` / `BackendRepr` descriptors and share `rustc_middle::ty` vtable layouts, all four cells of the 2x2 `(lib ∈ {llvm, cranelift}) × (bin ∈ {llvm, cranelift})` cross-crate matrix execute identically (`rc = 0`, `SRET=60 MIXED=3000000000000000a STR=542 DYN=9077 LINE=11`) across 48-byte `sret` structs, 128-bit `u128` aggregates, `&str` scalar pairs, niche-encoded `Option<NonZeroU64>`, cross-crate `&dyn Trait` vtables, and `#[track_caller]` implicit location arguments.
2. **Asymmetric `.eh_frame`/LSDA Unwinding Causes Silent `Drop` Leaks and Silent `catch_unwind` Bypass:** In `compiler/rustc_codegen_cranelift/Cargo.toml`, the `unwinding` Cargo feature is disabled by default (`unwinding = [] # Not yet included in unstable-features for performance reasons`) and `src/bootstrap/src/core/build_steps/compile.rs` builds `rustc_codegen_cranelift` with no `--features` flags. Yet `UnwindContext::new` and `UnwindContext::add_function` (`debuginfo/unwind.rs`) unconditionally emit valid System V `.eh_frame` CIE/FDE records while gating CIE personality routines, `.gcc_except_table` LSDA call-site/action tables, MIR cleanup blocks (`base.rs:315-318`), `try_call` lowering (`abi/mod.rs:860-862`), `UnwindResume` (`base.rs:577`), and `intrinsics::catch_unwind` (`intrinsics/mod.rs:1437-1447`) behind `cfg!(feature = "unwinding")`. Consequently, under default `-C panic=unwind` with zero compiler diagnostics:
   - **Cranelift callee inside LLVM `catch_unwind` (`lib_cranelift__bin_llvm`):** `libunwind` walks cleanly out of the Cranelift `.eh_frame` FDE into the LLVM caller's landing pad (`CAUGHT=true`, `BIN_DROPS=1`, `rc = 0`), **silently leaking every live `Drop` guard in the Cranelift callee (`LIB_DROPS=0`)**.
   - **LLVM or Cranelift callee inside Cranelift `catch_unwind` (`lib_llvm__bin_cranelift` and `lib_cranelift__bin_cranelift`):** Cranelift lowers `intrinsics::catch_unwind` to a bare `call_indirect` returning `false`, so panics fly straight past `std::panic::catch_unwind` and abort the process (`rc = 101`).
3. **Selective Fail-Open Security Flag Hazard (`-Z sanitizer=address` vs. `-C lto=thin` / `-C instrument-coverage`):** `CraneliftCodegenBackend::init` (`lib.rs:131-162`) fails closed (`rc = 1`) on `-C lto=thin` and `-C instrument-coverage`, but contains **zero** references to `sanitizer`, `stack_protector`, `cf_protection`, `branch_protection`, `control_flow_guard`, or `retpoline` across all 43 source files in `compiler/rustc_codegen_cranelift/src/`. Because `rustc_session` validates `-Z sanitizer=address` exclusively against `sess.target.options.supported_sanitizers` (`rustc_session/src/session.rs:1614-1633`) and `CodegenBackendInit` carries no backend sanitizer capability mask, `rustc -Z codegen-backend=cranelift -Z sanitizer=address` compiles silently (`rc = 0`), even links the ASan runtime via shared `rustc_codegen_ssa::back::link::add_sanitizer_libraries` (`link.rs:1777-1780, 2985`), emits zero ASan memory-access instrumentation, and **silently fails open on a heap out-of-bounds read (`ASAN_SURVIVED_OOB=0`, `rc = 0`)** where LLVM aborts with `AddressSanitizer: heap-buffer-overflow` (`rc = 1`).
4. **Out-of-Line `asm!` Wrapper Synthesis (and Hidden Recursive LLVM Dependency):** `codegen_inline_asm_inner` (`inline_asm.rs:237-295, 880-933`) lowers every `asm!` block by allocating a 16-byte-aligned caller stack slot, emitting a separate external assembly function (`<fn>__inline_asm_<cgu>_n<idx>`), and invoking it via a PIC GOT-indirect `call *%r9`, ignoring `options(pure, nomem, nostack)` (`47 B` across `14` instructions in `add_asm` plus the out-of-line wrapper, versus `7 B` across `3` instructions on LLVM, a `6.71x` caller expansion). Unless built with `CG_CLIF_FORCE_GNU_AS`, `compile_global_asm` (`global_asm.rs:240-291`) assembles these wrappers by recursively spawning `rustc -Zcodegen-backend=llvm --crate-type staticlib --emit obj`, creating a hidden LLVM TCB dependency. Meanwhile `asm! sym` operands, `asm_goto` labels, and `c_variadic` function definitions fail closed (`rc = 1`), whereas `explicit_tail_calls` (`become`) hits `span_bug!` at `base.rs:532` (`rc = 101`) and `core::intrinsics::atomic_xadd::<u128>` hits an x86_64 ISLE panic at `base.rs:222` (`rc = 101`) because `intrinsics/mod.rs` guards `u128` on `atomic_load`/`atomic_store` but omits the guard on `atomic_rmw`/`atomic_cas` intrinsics.
5. **Frontend-Bound Real Crates vs. Codegen-Bound Compute Loops:** On `zerocopy 0.8.48` (`google/zerocopy@aa7c31671cb5ce509551edafa23c6865df83b180`), Cranelift `-O0` (`2.506 s`) is `1.03x` slower than LLVM `-O0` (`2.440 s`) and Cranelift `-O2` (`2.758 s`) achieves only a `1.17x` build-time speedup over LLVM `-O2` (`3.230 s`), because macro/trait/monomorphization frontend work dominates. Conversely, on a compute-heavy loop microbenchmark, Cranelift `-O2` compiles `1.97x` faster (`0.114 s` vs. `0.224 s`) at a **`14.35x` runtime slowdown** (`844.39 ms` vs. `58.84 ms` median, with identical checksum `8d84cae7b21ecec2`), because Cranelift maps every non-zero `-C opt-level` (`1`, `2`, `3`, `s`, `z`) identically to `opt_level = "speed_and_size"` (`lib.rs:306-318`) and performs no loop unrolling or auto-vectorization.
6. **Mechanized Contract (`support/CodegenBackendParityAndUnwindContract.lean`):** Kernel-checked in `Lean v4.34.1` with `-DwarningAsError=true`, zero `sorry`, zero `Classical.choice`, zero `omega`/`bv_decide`/`native_decide`, and at most `[propext]` (zero axioms on 8 of 11 theorems), proving (1) normal mixed-backend ABI call preservation, (2) the exact necessary-and-sufficient (`↔`) `.eh_frame` + LSDA cleanup + LSDA catch completeness theorem for mixed-backend unwind parity, (3) fail-closed security/unwind flag admission soundness, and (4) three constructive counterexamples reproducing the observed `LIB_DROPS=0` leak, uncaught `rc = 101` abort, and silent ASan OOB survival.

## Applicability

This report characterizes the differential behavior, ABI seam, unwind/LSDA semantics, security-flag validation, inline-assembly lowering, feature/ICE boundaries, and performance profile of `rustc_codegen_cranelift` relative to `rustc_codegen_llvm`, and derives the concrete semantic-completeness and performance contract required of any drop-in verified `rustc` `CodegenBackend` (including future verified backends integrated behind Anneal's MIR trusted boundary).

### Examined Subjects and Their Relationships

- **Primary dual-backend comparison baseline (`rust-lang/rust` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, LLVM `23.1.5`, `cranelift-codegen 0.137.0`):** Primary source audit of all 43 files in `compiler/rustc_codegen_cranelift/src/` plus `compiler/rustc_codegen_cranelift/Cargo.toml`, `compiler/rustc_codegen_ssa/src/{traits/backend.rs, back/link.rs}`, `compiler/rustc_session/src/session.rs`, `compiler/rustc_codegen_llvm/src/attributes.rs`, and `src/bootstrap/src/core/build_steps/compile.rs`, paired with complete dual-backend execution on `x86_64-unknown-linux-gnu` (`support/cranelift_vs_llvm_differential_results_1_102_nightly.json`, collected `2026-11-21`).
- **Upstream `main` source continuity (`rust-lang/rust` at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`, `2026-11-22`):** Diffed directly against `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` across `base.rs`, `abi/mod.rs`, `debuginfo/unwind.rs`, `driver/aot.rs`, `config.rs`, `inline_asm.rs`, and `lib.rs`. Six of seven files are byte-for-byte identical; only `lib.rs:158-159` renamed `CodegenBackendInit::{replaced_intrinsics, fallback_intrinsics}` to `{replaced_rustc_intrinsics, fallback_rustc_intrinsics}`. Every mechanism, line number, feature gate, and fail-open behavior documented at `3ef0c22` holds verbatim at `342d744`.
- **LLVM revalidation baseline (`rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM `22.1.6`):** Used on `2026-11-22` to execute and revalidate the standalone probe script `support/probe_cranelift_vs_llvm.py` across the LLVM half of Part A, all 11 Part B cases (including live ASan `heap-buffer-overflow` detection, live `objdump` of `add_asm`, and live `readelf -SW` verification of `.eh_frame` and `.gcc_except_table`), and Part C's compute microbenchmark (`support/llvm_revalidation_1_98_nightly.json`), and verified via `Cargo.toml` at `14210df0e` that `unwinding = []` and `inline_asm_sym = []` feature defaults were already identical on `1.98.0-nightly`.
- **Real-crate compilation workload (`google/zerocopy` at `aa7c31671cb5ce509551edafa23c6865df83b180`, `v0.8.48`):** Compiled as an `rlib` across `{llvm, cranelift} × {-O0, -O2}` on `rustc 1.102.0-nightly` (`3ef0c22`).
- **Anneal MIR trusted boundary (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Inspected `trusted/lean/Trusted/MirAst.lean` and `trusted/rustc-capture/src/driver.rs` to align the derived drop-in backend contract with Anneal's MIR representation (`UnwindAction`, `BasicBlock.cleanup`, `TerminatorKind`) and `rustc_driver::Callbacks` scaffold.
- **Formal mechanization kernel (`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** Used to kernel-check `support/CodegenBackendParityAndUnwindContract.lean` under strict flags (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`).

### Scope Constraints and Generalization Conditions

- **Target architecture and OS:** All empirical executions target `x86_64-unknown-linux-gnu` (System V ELF ABI, PIC enabled by default in Cranelift via `is_pic = "true"` at `lib.rs:278`). Source findings on `debuginfo/unwind.rs`, `abi/pass_mode.rs`, `inline_asm.rs`, and `lib.rs` explicitly note target-specific branches for `aarch64`, `riscv64`, `s390x`, macOS Mach-O, and Windows COFF/MSVC/MinGW where relevant, without claiming empirical execution on those targets.
- **Default `rustc` distribution vs. custom `--features unwinding` builds:** All execution results reflect the default upstream `rustc` bootstrap build of `rustc_codegen_cranelift` (`src/bootstrap/src/core/build_steps/compile.rs:1793-1816`), where `cfg!(feature = "unwinding") == false`, `cfg!(feature = "inline_asm_sym") == false`, and `cfg!(feature = "jit") == false`. Custom developer builds enabling `--features unwinding` change the unwind/LSDA behavior as described by the audited `cfg!(feature = "unwinding")` branches, though they still do not enable ASan, LTO, coverage, `asm_goto`, `become`, `c_variadic` definitions, or `u128` atomic RMW.
- **Standalone formalization scope:** `support/CodegenBackendParityAndUnwindContract.lean` models the abstract architectural invariants of mixed-backend ABI compatibility, System V `.eh_frame`/LSDA unwinding, and fail-closed flag admission; it is a standalone Lean 4 theory characterizing the backend contract, not a machine-code refinement proof of Cranelift's or LLVM's x86_64 emitters.

## Findings

### 1. Shared `CodegenBackend` Seam and Cross-Backend Binary ABI Interoperability

**Basis: source + execution.**

#### 1.1 How `rustc_codegen_cranelift` Plugs Into `rustc`

`rustc` isolates code generation behind the `rustc_codegen_ssa::traits::CodegenBackend` trait (`compiler/rustc_codegen_ssa/src/traits/backend.rs:37-142`), loaded dynamically via `#[unsafe(no_mangle)] pub fn __rustc_codegen_backend() -> Box<dyn CodegenBackend>` (`compiler/rustc_codegen_cranelift/src/lib.rs:380-383`). `CraneliftCodegenBackend` (`lib.rs:121-251`) implements `name`, `init`, `target_config`, `print_version`, `has_mnemonic`, `target_cpu`, `codegen_crate`, and `join_codegen`, while inheriting the default `CodegenBackend::link` method (`rustc_codegen_ssa/src/traits/backend.rs:124-141`), which delegates linking and rlib packaging directly to `rustc_codegen_ssa::back::link::link_binary`.

Within `codegen_crate` (`lib.rs:224-236`), AOT mode invokes `rustc_codegen_ssa::base::codegen_crate(driver::aot::AotDriver, tcx)`. `AotDriver` (`compiler/rustc_codegen_cranelift/src/driver/aot.rs:270-391`) implements `ExtraBackendMethods` and `WriteBackendMethods`:

- `compile_codegen_unit` (`aot.rs:286-312`) walks `cgu.items_in_deterministic_order(tcx)` (`aot.rs:154`), lowers every non-naked `MonoItem::Fn` to Cranelift IR (`CLIF`) via `base::codegen_fn`, every `MonoItem::Static` via `constant::codegen_static`, and every naked function / `MonoItem::GlobalAsm` into `module.global_asm`.
- `WriteBackendMethods::codegen` (`aot.rs:368-386`) runs `compile_cgu` (`aot.rs:209-267`) on worker threads: it compiles each `CodegenedFunction` via `cranelift_object::ObjectModule` wrapped in `UnwindModule<ObjectModule>`, optionally assembles `aot_module.global_asm` into `<cgu>.asm.o`, and emits `<cgu>.o` with an ELF `.comment` producer section (`aot.rs:103-113`).
- `WriteBackendMethods::optimize` (`aot.rs:349-356`) is an empty no-op because Cranelift runs its e-graph optimization pass inside `module.define_function` (`base.rs:195`), and all LTO entrypoints (`optimize_and_codegen_fat_lto`, `run_thin_lto`, `optimize_and_codegen_thin`, `serialize_module`, `aot.rs:325-390`) are `unreachable!()` with `type ModuleBuffer = Infallible; type ThinData = Infallible;` (`aot.rs:317-319`).

#### 1.2 Why Binary ABI Interoperability With `rustc_codegen_llvm` Is 100%

Both `rustc_codegen_cranelift` and `rustc_codegen_llvm` consume the exact same frontend ABI computation (`FullyMonomorphizedLayoutCx(tcx).fn_abi_of_instance`, yielding `rustc_target::callconv::FnAbi<'tcx, Ty<'tcx>>`), the exact same `BackendRepr` (`Scalar`, `ScalarPair`, `SimdVector`, `Memory`), the exact same symbol mangling (`tcx.symbol_name(instance)`), and the exact same vtable slot indices (`ty::COMMON_VTABLE_ENTRIES_{DROPINPLACE,SIZE,ALIGN}`). Specifically, in `compiler/rustc_codegen_cranelift/src/abi/`:

- **Calling Convention & Return Pointer (`abi/mod.rs:39-86`, `abi/pass_mode.rs:99-205`, `abi/returning.rs:10-128`):** `clif_sig_from_fn_abi` maps `CanonAbi::{Rust, RustCold, C}` to `default_call_conv` (`CallConv::SystemV` on `x86_64-unknown-linux-gnu`), with `enable_llvm_abi_extensions = "true"` (`lib.rs:298`) so Cranelift's ABI lowering matches LLVM's `sret`/extension rules.
- **Large Structs (`BigSret`, `PassMode::Indirect`):** `get_abi_return` (`abi/pass_mode.rs:190-199`) emits `AbiParam::special(pointer_ty(tcx), ArgumentPurpose::StructReturn)` as the leading hidden parameter; `codegen_return_param` (`abi/returning.rs:20-24`) binds `RETURN_PLACE` directly to that caller-supplied pointer and `codegen_return` (`abi/returning.rs:105-107`) executes `return_(&[])`.
- **128-bit Scalars and Mixed Aggregates (`u128` / `PassMode::Cast`):** `reg_to_abi_param` (`abi/pass_mode.rs:19-36`) maps 9–16 byte integers to `types::I128`, and `cast_target_to_abi_params` (`abi/pass_mode.rs:46-97`) splits `CastTarget` prefixes/rests into identical register chunks with `to_casted_value`/`from_casted_value` (`abi/pass_mode.rs:207-252`).
- **Wide Pointers (`&str`) and Niche Enums (`Option<NonZeroU64>`):** `&str` has `PassMode::Pair` over `BackendRepr::ScalarPair`, lowered to two consecutive GPRs (`abi/pass_mode.rs:114-124, 172-185`); `Option<NonZeroU64>` has `PassMode::Direct` over `BackendRepr::Scalar(u64)` with `0` encoding `None`, lowered to a single `i64` register (`abi/pass_mode.rs:103-107`).
- **`dyn Trait` Vtables (`abi/mod.rs:568-586`, `vtable.rs:14-88`):** Virtual dispatch loads the method pointer from `vtable + idx * sizeof(usize)` (`vtable.rs:67-74`), overrides the receiver argument with the thin data pointer `ptr.get_addr(fx)`, and calls through `CallTarget::Indirect(sig, method)`. Vtable data objects use the identical layout defined by `rustc_middle::ty` (`data_id_for_vtable`), so an LLVM-built binary can pass `&dyn Trait` into a Cranelift-built rlib and vice versa.
- **`#[track_caller]` (`abi/mod.rs:328-337, 558-562, 812-821`):** Both callers and callees check `instance.def.requires_caller_location(fx.tcx)` and append/consume the implicit trailing `&'static core::panic::Location<'static>` argument in the exact same slot order as LLVM (`rustc_codegen_ssa`).

#### 1.3 Empirical 2x2 Cross-Backend ABI Matrix

Compiling `abi_lib.rs` as an `rlib` and `abi_bin.rs` as a binary across all four `(lib_backend, bin_backend)` pairings on `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `-C opt-level=2`) yields bit-identical output in every cell (with `lib_llvm__bin_llvm` independently revalidated on `rustc 1.98.0-nightly` `14210df0e`):

| Matrix Cell (`lib` / `bin`) | `lib` `rc` | `bin` `rc` | Run `rc` | Observed `stdout` (`abi_no_panic`) |
| :--- | :---: | :---: | :---: | :--- |
| `lib_llvm__bin_llvm` | `0` | `0` | `0` | `SRET=60 MIXED=3000000000000000a STR=542 DYN=9077 LINE=11` |
| `lib_llvm__bin_cranelift` | `0` | `0` | `0` | `SRET=60 MIXED=3000000000000000a STR=542 DYN=9077 LINE=11` |
| `lib_cranelift__bin_llvm` | `0` | `0` | `0` | `SRET=60 MIXED=3000000000000000a STR=542 DYN=9077 LINE=11` |
| `lib_cranelift__bin_cranelift` | `0` | `0` | `0` | `SRET=60 MIXED=3000000000000000a STR=542 DYN=9077 LINE=11` |

Every non-panicking ABI test passes across every mixed-backend boundary.

---

### 2. Asymmetric `.eh_frame`/LSDA Unwinding, Silent `Drop` Leaks, and Silent `catch_unwind` Bypass

**Basis: source + execution + derived.**

#### 2.1 Primary-Source Root Cause: Six `cfg!(feature = "unwinding")` Gates vs. Unconditional `.eh_frame` Emission

The upstream `rustc_codegen_cranelift` crate actually contains an experimental System V Itanium unwinding implementation (`debuginfo/gcc_except_table.rs`, `271` lines; `debuginfo/unwind.rs`, `309` lines), **but it is compiled out of every official `rustc` build**. In `compiler/rustc_codegen_cranelift/Cargo.toml:44-49`:

```toml
[features]
# Enable features not ready to be enabled when compiling as part of rustc
unstable-features = ["jit", "inline_asm_sym"]
jit = ["cranelift-jit", "libloading"]
inline_asm_sym = []
unwinding = [] # Not yet included in unstable-features for performance reasons
```

And in `src/bootstrap/src/core/build_steps/compile.rs:1793-1816`, `CraneliftCodegenBackend::run` invokes Cargo on `compiler/rustc_codegen_cranelift/Cargo.toml` with **no `--features` flags**. Thus, in every shipped `rustc-codegen-cranelift-preview` component, `cfg!(feature = "unwinding")` evaluates to `false`.

Exhaustive audit of all 43 files in `compiler/rustc_codegen_cranelift/src/` reveals **exactly six `cfg!(feature = "unwinding")` gating sites across four files**, combined with **unconditional `.eh_frame` CIE/FDE emission**:

| # | File & Line (`3ef0c22` & `342d744`) | Behavior When `cfg!(feature = "unwinding") == false` (Default Shipped Build) | Behavior When `cfg!(feature = "unwinding") == true` |
| :-: | :--- | :--- | :--- |
| 1 | `debuginfo/unwind.rs:35-110` (`UnwindContext::new`) | Unconditionally creates System V CIE (`module.isa().create_systemv_cie()`) with `fde_address_encoding = DW_EH_PE_pcrel \| DW_EH_PE_sdata4`, **omitting** `cie.lsda_encoding` and `cie.personality` (`DW.ref.rust_eh_personality`). | Attaches `cie.lsda_encoding` and indirect PC-relative `cie.personality` pointing to `rust_eh_personality`. |
| 2 | `debuginfo/unwind.rs:138-227` (`UnwindContext::add_function`) | Unconditionally converts `UnwindInfo::SystemV` to an FDE (`unwind_info.to_fde(...)`) and adds it to `self.frame_table` (emitted to `.eh_frame` in `emit`, lines `235-250`), with `fde.lsda = None` and **no `.gcc_except_table` section**. | Synthesizes `GccExceptTable` (`CallSiteTable`, `ActionTable`, `TypeInfoTable`) mapping `EXCEPTION_HANDLER_CLEANUP = 0` (`action_entry: None`) and `EXCEPTION_HANDLER_CATCH = 1` (`ActionKind::Catch`), emits `.gcc_except_table`, and sets `fde.lsda = Some(...)`. |
| 3 | `base.rs:315-321` (`codegen_fn_body`) | `if bb_data.is_cleanup { if cfg!(not(feature = "unwinding")) { continue; } }` — **silently skips codegen for every MIR cleanup basic block**, emitting zero instructions for local `Drop` glue on unwind paths. | Sets `bcx.set_cold_block(block)` and lowers all cleanup statements and drop terminators. |
| 4 | `abi/mod.rs:860-865` (`codegen_call_with_unwind_action`) | `if cfg!(not(feature = "unwinding")) { unwind = UnwindAction::Unreachable; }` — **silently rewrites `UnwindAction::Cleanup(_)` and `UnwindAction::Terminate(_)` to `UnwindAction::Unreachable`**, emitting bare `call` / `call_indirect` instead of `try_call` / `try_call_indirect`. | Builds Cranelift `ExceptionTableData` tagged `EXCEPTION_HANDLER_CLEANUP` and emits `try_call` / `try_call_indirect` branching to a cold `pre_cleanup_block`. |
| 5 | `base.rs:576-587` (`TerminatorKind::UnwindResume`) | Skips `_Unwind_Resume` libcall and emits only `trap(TrapCode::user(1))`. | Loads `fx.exception_slot` and invokes `_Unwind_Resume(exception_ptr)`. |
| 6 | `intrinsics/mod.rs:1423-1493` (`sym::catch_unwind`) | `if cfg!(not(feature = "unwinding")) \|\| fx.tcx.sess.panic_strategy() == PanicStrategy::Abort` — emits a bare `call_indirect(f_sig, f, &[data])` followed by writing `false` (`0`) to `ret`, **even when `-C panic=unwind` is active**, with zero warning or error. | Emits `try_call_indirect` with `EXCEPTION_HANDLER_CATCH`, invoking `catch_fn(data, exception)` and returning `true` (`1`) on unwind. |

#### 2.2 Why This Produces Asymmetric Cross-Backend Unwind Failure

The combination of **unconditional `.eh_frame` FDE emission** (sites 1–2) with **silently stripped LSDA / cleanup / catch lowering** (sites 1–6) creates a subtle half-working unwinding mechanism:

- Every Cranelift function has a valid `.eh_frame` FDE describing CFA and callee-saved register restoration (`UnwindModule::define_function_with_control_plane` at `unwind_module.rs:95-103` calls `unwind_context.add_function` for every defined function). Therefore, during the Itanium unwinder's search pass and cleanup pass (`_Unwind_RaiseException`), `libunwind` **does not crash or stop** when walking out of a Cranelift frame; it restores callee-saved registers and advances to the caller's return address cleanly.
- However, because the Cranelift FDE has `personality = None` and `lsda = None`, `libunwind` never invokes `rust_eh_personality` on that frame and never executes any cleanup landing pad (indeed, no cleanup block was even codegenned due to `base.rs:316`).
- Equally critically, site 4 (`abi/mod.rs:860`) also erases `UnwindAction::Terminate`, meaning Cranelift-compiled `extern "C"` nounwind boundaries or panics-during-drop lose their terminate pads too (derived from `abi/mod.rs:860, 936-941`).
- Conversely, when the caller is compiled by LLVM, the LLVM frame retains its full `.eh_frame` FDE + `rust_eh_personality` + `.gcc_except_table` LSDA (verified in `support/llvm_revalidation_1_98_nightly.json`: `.eh_frame` = `20,824 B`, `.eh_frame_hdr` = `4,188 B`, `.gcc_except_table` = `11,140 B`).

#### 2.3 Empirical 2x2 Unwind, `Drop` Leak, and `catch_unwind` Matrix

Executing `unwind_bin.rs` (wrapping `abi_lib::panic_with_guard("cross_backend", &lib_drops)` inside `std::panic::catch_unwind` with a caller-side `BinGuard` and callee-side `DropGuard`) across all four pairings on `rustc 1.102.0-nightly` (`3ef0c22`):

| Matrix Cell (`lib` / `bin`) | Compile Warnings | Run `rc` | Observed `stdout` (`unwind_catch_and_drop`) | Semantic Diagnosis |
| :--- | :---: | :---: | :--- | :--- |
| `lib_llvm__bin_llvm` | `0` | `0` | `CAUGHT=true BIN_DROPS=1 LIB_DROPS=1` | Full Rust unwinding semantics: both `Drop` guards run; panic caught cleanly. |
| `lib_llvm__bin_cranelift` | `0` | **`101`** | *(empty; process panicked uncaught)* | Cranelift `catch_unwind` degraded to bare `call_indirect` (`intrinsics/mod.rs:1437`); panic escaped `main` into `libstd` runtime abort. |
| `lib_cranelift__bin_llvm` | `0` | `0` | **`CAUGHT=true BIN_DROPS=1 LIB_DROPS=0`** | **Silent destructor leak:** `libunwind` traversed Cranelift `.eh_frame` into LLVM `catch_unwind`, ran `BinGuard`, caught panic, and **silently leaked `DropGuard` in `abi_lib`**. |
| `lib_cranelift__bin_cranelift` | `0` | **`101`** | *(empty; process panicked uncaught)* | Both `Drop` guards bypassed and `catch_unwind` bypassed; process exited `101`. |

This is worse than a clean compile-time rejection (`-C panic=abort` or `fatal` error): in a mixed-backend workspace (for instance, dev-building dependency crates with LLVM or compiling workspace crates with Cranelift against an LLVM-built test harness / `libstd`), **`lib_cranelift__bin_llvm` exits `0` with `CAUGHT=true` while silently violating RAII cleanup invariants** (leaking mutex guards, file descriptors, heap buffers, or rollback guards inside the Cranelift-compiled crate).

---

### 3. Selective Fail-Open `-Z sanitizer=address` vs. Fail-Closed `-C lto=thin` and `-C instrument-coverage`

**Basis: source + execution + derived.**

#### 3.1 Exhaustive Audit of Flag Validation Across `rustc_session`, `rustc_codegen_ssa`, `rustc_codegen_llvm`, and `rustc_codegen_cranelift`

Tracing how compiler security and optimization flags flow from the CLI through `rustc_session` into the active `CodegenBackend` explains the exact split between fail-closed and fail-open flags:

1. **Flags that fail closed in `CraneliftCodegenBackend::init` (`compiler/rustc_codegen_cranelift/src/lib.rs:131-162`):**
   - **LTO (`lib.rs:134-139`):** Explicitly checks `(sess.target.requires_lto, sess.early_lto())` and calls `sess.dcx().fatal("LTO is not supported by rustc_codegen_cranelift")` for `LtoCli::{Yes, Fat, NoParam, Thin}` (and sets `thin_lto_supported: false` in `CodegenBackendInit`, `lib.rs:160`).
   - **Coverage (`lib.rs:141-144`):** Explicitly checks `sess.opts.cg.instrument_coverage() != InstrumentCoverage::No` and calls ``sess.dcx().fatal("`-Cinstrument-coverage` is LLVM specific and not supported by Cranelift")``.
   - **LLVM args (`config.rs:17-42`):** `BackendConfig::from_opts(&sess.opts.cg.llvm_args)` accepts only `"jit-mode"`, silently ignores `"-import-instr-limit*"` (with an explicit comment explaining rustc's build system passes it during cg_clif testing), and fails closed with `Err(format!("Unknown option `{}`", opt))` -> `fatal` on any other `-C llvm-args` entry.

2. **Why `-Z sanitizer=address` (and other hardening flags) silently fail open:**
   - **`rustc_session` validates sanitizers ONLY against the target triple, never against the `CodegenBackend`:** In `compiler/rustc_session/src/session.rs:1613-1633`, `validate_commandline_args_with_session_available` computes:
     ```rust
     let supported_sanitizers = sess.target.options.supported_sanitizers;
     let mut unsupported_sanitizers = sess.sanitizers() - supported_sanitizers;
     ```
     Because `CodegenBackendInit` (`compiler/rustc_session/src/session.rs:438-450`) contains only four fields (`global_backend_features`, `replaced_intrinsics`, `fallback_intrinsics`, `thin_lto_supported`) and `CodegenBackend` (`rustc_codegen_ssa/src/traits/backend.rs:37-142`) exposes no `supported_sanitizers()` query, `rustc_session` assumes every backend supports every sanitizer declared in `sess.target.options.supported_sanitizers`.
   - **Exhaustive zero-reference check in `rustc_codegen_cranelift`:** Grepping all 43 `.rs` files in `compiler/rustc_codegen_cranelift/src/` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` returns **0 occurrences** of `sanitizer`, `sanitizers`, `SanitizerSet`, `stack_protector`, `cf_protection`, `branch_protection`, `control_flow_guard`, or `retpoline`. Contrast `compiler/rustc_codegen_llvm/src/attributes.rs:154-170, 570-576`, where `sanitize_attrs` reads `tcx.sess.sanitizers()` and attaches `llvm::AttributeKind::SanitizeAddress` to every compiled function (triggering LLVM's `AddressSanitizerPass`).
   - **Deceptive Runtime Linking via Shared `rustc_codegen_ssa` Linker (`compiler/rustc_codegen_ssa/src/back/link.rs:1743-1790, 2985`):** Because `CraneliftCodegenBackend` inherits the default `CodegenBackend::link` method, `link_binary` calls `add_sanitizer_libraries(sess, flavor, crate_type, cmd)` (`link.rs:2985`), which checks `sess.sanitizers().contains(SanitizerSet::ADDRESS)` (`link.rs:1778-1780`) and links `librustc-nightly_rt.asan.a` into the Cranelift output binary! Thus a Cranelift binary compiled with `-Z sanitizer=address` even contains linked ASan runtime symbols (defeating superficial ELF symbol audits for `__asan_init`), while every user function's machine code has **zero** shadow-memory redzone checks.

#### 3.2 Empirical Verification

On `b_sanitizer_address_heap_oob.rs` (`Box::new([0u8; 32])` followed by `#[inline(never)] unsafe fn read_oob(p: *const u8) -> u8 { core::ptr::read_volatile(p.add(32)) }`):

- **LLVM (`rustc -Z sanitizer=address`):** Compiles cleanly (`rc = 0`); at runtime aborts immediately with `rc = 1` and `ERROR: AddressSanitizer: heap-buffer-overflow ... READ of size 1 ... in b_sanitizer_address_heap_oob::read_oob` (observed on both `rustc 1.102.0-nightly` and `rustc 1.98.0-nightly`).
- **Cranelift (`rustc -Z codegen-backend=cranelift -Z sanitizer=address`):** Compiles cleanly with **0 warnings and 0 errors** (`rc = 0`); at runtime **silently survives the heap out-of-bounds read** (`rc = 0`, `stdout = "ASAN_SURVIVED_OOB=0"`).
- **Contrast (`-C lto=thin`, `-C instrument-coverage`):** Both fail closed at compile time (`rc = 1`) with the exact `lib.rs:136` and `lib.rs:143` fatal diagnostics.

---

### 4. Out-of-Line `asm!` Wrapper Synthesis, Feature-Gate Rejections, and Live ICE Boundaries

**Basis: source + execution.**

#### 4.1 Complete Anatomy of `codegen_inline_asm_inner` (`compiler/rustc_codegen_cranelift/src/inline_asm.rs`)

Because Cranelift's CLIF IR has no native inline-assembly instruction, `rustc_codegen_cranelift` lowers every `TerminatorKind::InlineAsm` (`base.rs:536-572`) through `codegen_inline_asm_terminator` (`inline_asm.rs:42-235`) and `codegen_inline_asm_inner` (`inline_asm.rs:237-295`):

1. **Register & Stack-Slot Allocation (`inline_asm.rs:312-528`):** `InlineAssemblyGenerator::allocate_registers` assigns physical registers to operands outside Cranelift's register allocator, and `allocate_stack_slots` lays out a caller-owned buffer for clobber saves, inputs, and outputs (allowing non-`inout` inputs and outputs to share offsets).
2. **External Wrapper Function Synthesis (`inline_asm.rs:261-270, 530-764`):** `generate_asm_wrapper` emits textual assembly defining a global symbol `<fn_symbol>__inline_asm_<cgu>_n<idx>` in its own ELF section `.section .text.<asm_name>,"ax",@progbits` (`inline_asm.rs:536-539`), with a fixed `x86_64` prologue (`push rbp; mov rbp, rsp; push rbx; mov rbx, rdi`, `inline_asm.rs:718-724`), memory loads from `[rbx+offset]`, the raw user template, memory stores back to `[rbx+offset]`, and epilogue (`pop rbx; pop rbp; ret`, `inline_asm.rs:745-749`). Notice the explicit comment at `inline_asm.rs:243`: `// FIXME add .eh_frame unwind info directives` — the synthesized assembly wrapper carries no `.cfi_*` directives.
3. **Caller-Side Stack Frame & PIC GOT-Indirect Call (`inline_asm.rs:880-933`):** `call_inline_asm` unconditionally allocates a 16-byte-aligned stack slot (`fx.create_stack_slot(slot_size.bytes().next_multiple_of(16), 16)`, line `888`), stores every input operand into that stack slot, declares `<asm_name>` as `Linkage::Import` with `CallConv::SystemV` taking the slot pointer (`lines 890-901`), emits `call(inline_asm_func, &[stack_slot_addr])` (`line 917`), and reloads output operands from the stack slot (`lines 919-932`). **Crucially, `options(pure, nomem, nostack)` is never inspected by `call_inline_asm` or `generate_asm_wrapper`** (only `NORETURN` and `ATT_SYNTAX` are checked in `generate_asm_wrapper`, and `MAY_UNWIND` is rejected at `base.rs:545-550`). Because Cranelift compiles ELF objects with `is_pic = "true"` (`lib.rs:278`), calling a `Linkage::Import` function compiles to a RIP-relative GOT load (`mov <disp>(%rip), %r9`) followed by an indirect `call *%r9`.
4. **Hidden Recursive LLVM Assembler Invocation (`global_asm.rs:212-294`, `driver/aot.rs:239-253`):** All generated `inline_asm` strings are concatenated into `aot_module.global_asm` (`base.rs:165`). Unless `rustc_codegen_cranelift` was built with `CG_CLIF_FORCE_GNU_AS` (`global_asm.rs:228`), `compile_global_asm` (`global_asm.rs:240-291`) assembles the wrapper into `<cgu>.asm.o` by spawning `std::env::current_exe()` (`rustc`) with **`-Zcodegen-backend=llvm --crate-type staticlib --emit obj`** feeding `#![no_core] global_asm!(...)` over stdin! Consequently, `rustc_codegen_cranelift` silently re-introduces LLVM into the build pipeline whenever any crate contains `asm!` or `global_asm!`.

#### 4.2 Disassembly Comparison of `add_asm` (`options(pure, nomem, nostack)`)

Compiling `add_asm(mut a: u64, b: u64) -> u64` with `asm!("add {a}, {b}", a = inout(reg) a, b = in(reg) b, options(pure, nomem, nostack))` at `-C opt-level=2`:

- **LLVM (`rustc 1.102.0-nightly` `3ef0c22`, identical instruction sequence on `rustc 1.98.0-nightly` `14210df0e`):** **`3` instructions, `7` bytes** (excluding 1-byte `int3` alignment pad; `has_inline_asm_wrapper_sym = false`):
  ```text
  <add_asm>:
     14c38: 48 89 f8       mov    %rdi,%rax
     14c3b: 48 01 f0       add    %rsi,%rax
     14c3e: c3             ret
  ```
- **Cranelift (`rustc 1.102.0-nightly` `3ef0c22`):** **`14` instructions, `47` bytes** in `<add_asm>` alone (`6.71x` caller byte expansion, plus the separate out-of-line `__inline_asm_*` wrapper symbol with its own frame push/pop/memory traffic; `has_inline_asm_wrapper_sym = true`):
  ```text
  <add_asm>:
     14efb: 55                     push   %rbp
     14efc: 48 89 e5               mov    %rsp,%rbp
     14eff: 48 83 ec 10            sub    $0x10,%rsp
     14f03: 4c 8d 04 24            lea    (%rsp),%r8
     14f07: 48 89 3c 24            mov    %rdi,(%rsp)
     14f0b: 48 89 74 24 08         mov    %rsi,0x8(%rsp)
     14f10: 4c 8b 0d 49 dd 03 00   mov    0x3dd49(%rip),%r9   # GOT entry for __inline_asm_*
     14f17: 4c 89 c7               mov    %r8,%rdi
     14f1a: 41 ff d1               call   *%r9
     14f1d: 48 8b 04 24            mov    (%rsp),%rax
     14f21: 48 83 c4 10            add    $0x10,%rsp
     14f25: 48 89 ec               mov    %rbp,%rsp
     14f28: 5d                     pop    %rbp
     14f29: c3                     ret
  ```

#### 4.3 Complete 11-Case Feature-Gate, ICE, and Fail-Open Parity Matrix

Empirical results on `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM column independently revalidated on `rustc 1.98.0-nightly` `14210df0e`), cross-referenced to exact upstream code locations:

| # | Case | LLVM (`rc` / `stdout`) | Cranelift (`compile_rc` / `run_rc`) | Disposition Class | Exact Upstream Source Anchor (`3ef0c22` & `342d744`) |
| :-: | :--- | :--- | :--- | :--- | :--- |
| 1 | `inline_asm_basic` | `0` / `0` (`ASM=42`, `7 B`, `3` insns) | `0` / `0` (`ASM=42`, `47 B`, `14` insns + wrapper) | Functional parity, heavy wrapper overhead | `inline_asm.rs:237-295, 880-933`; `global_asm.rs:240-291` |
| 2 | `inline_asm_sym` | `0` / `0` (`ASM_SYM=99`) | **`1`** (`error: asm! and global_asm! sym operands are not yet supported`) | **Fail-closed compile error** | `inline_asm.rs:119-124, 168-172` (`cfg!(not(feature = "inline_asm_sym"))`) |
| 3 | `asm_goto_label` | `0` / `0` (`ASM_GOTO=7`) | **`1`** (`error: cranelift doesn't support labels in inline assembly.`) | **Fail-closed compile error** | `base.rs:552-562` (`span_fatal`) |
| 4 | `explicit_tail_calls_become` | `0` / `0` (`TAIL=5050`) | **`101` ICE** (`base.rs:532:57: tail calls are not yet supported in rustc_codegen_cranelift backend`) | **Uncaught compiler ICE** | `base.rs:532-535` (`TerminatorKind::TailCall => span_bug!`) |
| 5 | `c_variadic_def` | `0` / `0` (`VA=42`) | **`1`** (`error: Defining variadic functions is not yet supported by Cranelift`) | **Fail-closed compile error** | `abi/mod.rs:281-286` & `intrinsics/mod.rs:1588-1593` (`span_fatal`) |
| 6 | `atomic_u128_intrinsic` | `0` / `0` (`A128=100 NOW=123`) | **`101` ICE** (`base.rs:222:17: Compilation(Unsupported("should be implemented in ISLE: inst = atomic_rmw.i128 add ..."))`) | **Uncaught compiler ICE** | `intrinsics/mod.rs:870-891` omits `u128`/`i128` guard present in `atomic_load` (`762-777`) & `atomic_store` (`798-813`), crashing in `base.rs:222` (`bug!`) |
| 7 | `f16_f128_arith` | `0` / `0` (`F16=3.75 F128=21`) | `0` / `0` (`F16=3.75 F128=21`) | **Full parity via polyfill** | `codegen_f16_f128.rs:6-120` (`__extendhfsf2`, `__truncsfhf2`, `__eqtf2`, etc.); `lib.rs:194-203` |
| 8 | `portable_simd_and_sse2` | `0` / `0` (`SIMD=[11, 22, 33, 44] SSE2=[6, 8, 10, 12]`) | `0` / `0` (`SIMD=[11, 22, 33, 44] SSE2=[6, 8, 10, 12]`) | **Full parity** | `intrinsics/simd.rs` & `intrinsics/llvm_x86.rs` |
| 9 | `lto_thin_flag` | `0` (compiles) | **`1`** (`error: LTO is not supported by rustc_codegen_cranelift`) | **Fail-closed compile error** | `lib.rs:134-139` (`sess.dcx().fatal`) |
| 10 | `instrument_coverage_flag` | `0` (compiles) | **`1`** (`error: -Cinstrument-coverage is LLVM specific and not supported by Cranelift`) | **Fail-closed compile error** | `lib.rs:141-144` (`sess.dcx().fatal`) |
| 11 | `sanitizer_address_heap_oob` | `0` / **`1`** (`AddressSanitizer: heap-buffer-overflow`) | **`0` / `0`** (`ASAN_SURVIVED_OOB=0`) | **SILENT FAIL-OPEN** | `rustc_session/src/session.rs:1614-1633`; `0` refs in `rustc_codegen_cranelift/src/`; `link.rs:1778-1780` links runtime without codegen instrumentation |

Note also the two subtle nuances verified in primary source for cases 5 and 6:
- **Variadic calls vs. definitions:** While defining a `c_variadic` function fails closed (`abi/mod.rs:281-286`), **calling** a C variadic function IS partially supported (`abi/mod.rs:624-735`, `adjust_call_for_c_variadic`), but fails closed (`span_fatal`) if any variadic argument is non-integer (e.g., `f64`, `abi/mod.rs:721-729`) or non-C ABI (`abi/mod.rs:650-655`).
- **128-bit atomics asymmetry:** `atomic_load` (`intrinsics/mod.rs:761-777`) and `atomic_store` (`intrinsics/mod.rs:797-813`) explicitly guard `ty::Uint(UintTy::U128) | ty::Int(IntTy::I128)` with `span_fatal("128bit atomics not yet supported")` (or `codegen_panic_nounwind` inside `compiler_builtins`). In contrast, `atomic_xchg` (`825-846`), `atomic_cxchg`/`atomic_cxchgweak` (`847-868`), `atomic_xadd` (`870-891`), `atomic_xsub` (`892-913`), and bitwise/min/max RMW intrinsics omit that guard and emit `atomic_rmw.i128` / `atomic_cas.i128` directly into CLIF IR, crashing late during ISLE instruction selection at `base.rs:222`. On LLVM, `atomic_xadd::<u128>` requires `+cmpxchg16b` on `x86_64` for inline `lock cmpxchg16b` lowering (without `+cmpxchg16b`, `rustc 1.98.0-nightly` lowers to an unresolved `__atomic_fetch_add_16` libcall, observed live during probe development).

---

### 5. Compile-Time vs. Runtime Trade-Offs on Real Crates (`zerocopy 0.8.48`) and Compute Loops

**Basis: source + execution + derived.**

#### 5.1 Full-Crate Build Benchmark (`google/zerocopy` `v0.8.48`, `aa7c31671cb5ce509551edafa23c6865df83b180`)

| Configuration (`rustc 1.102.0-nightly`, `3ef0c22`) | Exit Code | Wall Time (s) | Speedup vs. LLVM Same `-O` | `.rlib` Size (bytes) |
| :--- | :---: | :---: | :---: | :---: |
| `llvm -O0` | `0` | `2.4404` | `1.00x` | `8,746,788` |
| `cranelift -O0` | `0` | `2.5062` | `0.97x` (`1.03x` slower) | `8,650,682` |
| `llvm -O2` | `0` | `3.2304` | `1.00x` | `9,442,960` |
| `cranelift -O2` | `0` | `2.7577` | **`1.17x`** (`14.6%` faster) | `9,440,294` |

**Why real Rust library crates see modest Cranelift build-time gains:** `zerocopy` is heavily generic and trait-dense (`FromBytes`, `IntoBytes`, `KnownLayout`, `Immutable`, `TryFromBytes`), meaning most wall-clock compilation time is spent in frontend parsing, macro expansion, trait solving, borrow checking, MIR building, and `rmeta` serialization — compiler steps identical across both backends. Notice also that `.rlib` archive sizes are nearly identical (`9.44 MB` for both LLVM `-O2` and Cranelift `-O2`, within `0.03%`) because `rmeta` metadata dominates generic library `.rlib` files. At `-O0`, LLVM's fast-ISel path is actually slightly faster end-to-end (`2.440 s`) than Cranelift `-O0` (`2.506 s`).

#### 5.2 Compute-Intensive Tight-Loop Microbenchmark

| Configuration (`rustc 1.102.0-nightly`, `3ef0c22`) | Compile Time (s) | Binary Size (bytes) | Checksum | Runtime Samples (ms) | Median Runtime (ms) | Runtime Ratio vs. `llvm -O2` |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `llvm -O0` | `0.1235` | `4,686,856` | `8d84cae7b21ecec2` | `[1977.63, 1755.38, 1948.17]` | `1,948.17` | `33.11x` |
| **`llvm -O2`** | `0.2241` | `4,646,696` | `8d84cae7b21ecec2` | `[76.64, 58.84, 57.91]` | **`58.84`** | **`1.00x`** |
| `cranelift -O0` | `0.1592` | `4,715,376` | `8d84cae7b21ecec2` | `[2428.26, 2038.05, 1879.85]` | `2,038.05` | `34.64x` |
| **`cranelift -O2`** | **`0.1140`** | `4,687,320` | `8d84cae7b21ecec2` | `[779.05, 872.11, 844.39]` | **`844.39`** | **`14.35x`** |

**Architectural explanation (source + derived):**
- **Compile-time gain (`1.97x` at `-O2`):** On codegen-dominated single-file workloads, Cranelift's single acyclic e-graph pass (`opt_level = "speed_and_size"`) avoids LLVM's multi-pass middle-end pipeline, compiling in `0.114 s` vs. LLVM's `0.224 s`. Notice that Cranelift `-O2` (`0.114 s`) is even faster to compile than Cranelift `-O0` (`0.159 s`) because e-graph simplification shrinks the CLIF IR fed into register allocation (`regalloc2`) and emission.
- **Optimization level collapse (`compiler/rustc_codegen_cranelift/src/lib.rs:306-318`):** In `rustc 1.102.0-nightly` (`3ef0c22` and `342d744`), `build_isa` maps `OptLevel::No` to `"none"` and collapses **all five non-zero levels** (`OptLevel::{Less, More, Size, SizeMin, Aggressive}`, i.e. `-O1`, `-O2`, `-O3`, `-Os`, `-Oz`) identically to Cranelift `"speed_and_size"`.
- **Runtime gap (`14.35x` slowdown at `-O2`):** LLVM `-O2` speeds up the compute loop by `33.11x` over `-O0` (`1,948.17 ms` -> `58.84 ms`) via LICM, induction-variable simplification, loop unrolling, scalar replacement of aggregates (SROA), and SIMD/register-resident scheduling. Cranelift `-O2` speeds up the same loop by only `2.41x` (`2,038.05 ms` -> `844.39 ms`), lacking loop unrolling, auto-vectorization, and aggressive cross-block loop optimization.
- **Independent LLVM revalidation (`rustc 1.98.0-nightly`, `14210df0e`):** Running the self-contained 16-word mixing microbenchmark in `support/probe_cranelift_vs_llvm.py` confirmed identical checksums (`10d506cbbf1d1512`) and strong LLVM `-O2` optimization (`751.14 ms` median at `-O0` vs. `115.25 ms` median at `-O2`, `6.52x` speedup on a loop-carried data-dependent recurrence).

---

### 6. Concrete Drop-In Verified `rustc` `CodegenBackend` Contract and Anneal TCB Alignment

**Basis: source + derived.**

Comparing these empirical findings against Anneal's pinned MIR trusted boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, specifically `trusted/lean/Trusted/MirAst.lean:682-814` and `trusted/rustc-capture/src/driver.rs:25-152`) yields five non-negotiable requirements for any verified drop-in `rustc` `CodegenBackend`:

1. **Exact `FnAbi` / Vtable / `#[track_caller]` Compatibility Layer (Sufficient for Normal-Call Interop):** A verified backend must lower directly from `rustc_target::callconv::FnAbi` (`PassMode::{Ignore, Direct, Pair, Cast, Indirect, IndirectUnsized}`) and `rustc_middle::ty` vtable layouts, matching LLVM's register assignment and `sret` convention so verified crates link transparently against prebuilt LLVM `libstd` and unverified dependencies.
2. **All-or-Nothing Unwind Completeness Under `-C panic=unwind`:** In `Trusted/MirAst.lean:693-697, 810-814`, Anneal already preserves `UnwindAction` (`.continue_`, `.unreachable`, `.terminate`, `.cleanup block`) and `BasicBlock.cleanup`. A drop-in backend MUST NOT ship Cranelift's half-implemented `.eh_frame`-without-LSDA state: if `-C panic=unwind` is requested, the backend MUST emit all three of (a) valid `.eh_frame` CFI, (b) `.gcc_except_table` LSDA cleanup pads + lowered MIR cleanup blocks (`Drop` glue) + terminate pads (`UnwindAction::Terminate`), and (c) `intrinsics::catch_unwind` LSDA catch entries — OR fail closed at `CodegenBackend::init` by rejecting `-C panic=unwind` outright (requiring `-C panic=abort`).
3. **Fail-Closed Capability Admission Gate in `CodegenBackend::init`:** Because `rustc_session` validates `-Z sanitizer=*`, `-Z stack-protector=*`, `-Z cf-protection=*`, `-Z branch-protection=*`, and `-C control-flow-guard=*` only against target specs (`rustc_session/src/session.rs:1613-1660`), every alternative or verified `CodegenBackend::init` MUST inspect and reject (`sess.dcx().fatal(...)`) EVERY security, hardening, or instrumentation option it does not soundly implement:
   - `!sess.sanitizers().is_empty()` (when unsupported),
   - `sess.opts.unstable_opts.stack_protector != StackProtector::None` (when unsupported),
   - `sess.opts.unstable_opts.cf_protection != CFProtection::None` / `branch_protection` / `control_flow_guard` (when unsupported),
   - `sess.early_lto()` / `instrument_coverage()` / `panic_strategy() == PanicStrategy::Unwind` (if LSDA unwinding is omitted).
   Never inherit `rustc_codegen_ssa::back::link::add_sanitizer_libraries` without either emitting the corresponding sanitizer instrumentation or rejecting the flag before codegen.
4. **Zero-ICE Unsupported-Construct Boundary and LLVM-Free Assembly Path:** Every unsupported MIR terminator (`TerminatorKind::TailCall`), intrinsic width (`atomic_rmw`/`atomic_cas` for `u128`/`i128`), or `asm!` operand (`sym`, `label`, `MAY_UNWIND`) must produce a structured `span_fatal` / `span_err` diagnostic (`rc = 1`) rather than panicking inside `span_bug!` or ISLE (`rc = 101`). Furthermore, if inline or global assembly is supported in a verified backend, it must NOT silently shell out to `rustc -Zcodegen-backend=llvm` as `global_asm.rs:244-262` does; doing so silently re-admits LLVM into the compilation TCB and introduces opaque out-of-line wrappers without `.cfi_*` unwind directives.
5. **Dual-Tier Performance Expectation:** For developer iteration (`-O0` / `-O1`), matching Cranelift's single-pass speed (`~0.11 s` on small modules, `~1.0–1.2x` on generic crates like `zerocopy`) is feasible without complex optimizations, provided frontend overhead is recognized as the dominant bottleneck on trait-heavy crates. For release parity (`-O2`/`-O3`), a Cranelift-class e-graph-only backend leaves a `14.35x` runtime gap on compute-heavy loops; closing that gap requires verified or translation-validated loop optimization, SROA, and vectorization passes.

---

### 7. Kernel-Checked Lean 4 Formalization (`support/CodegenBackendParityAndUnwindContract.lean`)

**Basis: derived + execution (Lean `v4.34.1` kernel check).**

`support/CodegenBackendParityAndUnwindContract.lean` (`702` lines) mechanizes the mixed-backend execution, unwinding, and security-flag contract in pure constructive Lean 4 (`Lean v4.34.1`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`) with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, **zero `sorry`**, **zero `Classical.choice`**, **zero `Quot.sound`**, **zero `Lean.ofReduceBool`**, **zero `omega`/`bv_decide`/`native_decide`**, and **zero `partial def`**.

#### 7.1 Core Model Definitions

- `BackendProfile` (`lines 39-46`): `{ hasEhFrame, hasLsdaCleanup, hasLsdaCatch : Bool; abiTag : AbiTag; enforcesSanitizer : Bool }`, instantiated for `llvmProfile`, `craneliftDefaultProfile`, `craneliftUnwindingProfile`, and `noEhFrameProfile` (`lines 48-79`).
- `abiCompat` (`lines 82-83`): boolean equivalence on `abiTag`, with reflexivity, symmetry, transitivity, and propositional reflection (`abiCompat_refl`, `abiCompat_symm`, `abiCompat_trans`, `abiCompat_eq_iff`, `lines 85-106`).
- `execNormalStack` vs. `evalNormalRef` (`lines 132-144`): mixed-backend normal call execution checking `abiCompat` at every caller→callee frame transition against pure backend-independent reference semantics.
- `unwindStack` vs. `referenceUnwindStack` (`lines 216-254`): Itanium/System V unwinding over innermost-first `List CallFrame`, tracking `UnwindDisposition` (`.caughtAt frameId`, `.uncaughtAbort`, `.missingEhFrameAbort frameId`), `executedDrops`, `leakedDrops`, and `missedCatches`, with `referenceUnwindStack stack := unwindStack (stack.map toReferenceFrame)`.
- `admitsFlags` vs. `admitsFlagsCraneliftActual` (`lines 477-488`) and `runHeapOobProbe` (`lines 467-468`): formalizing the fail-closed backend gate against Cranelift's actual selective gate (`!req.ltoThin && !req.instrumentCoverage`).

#### 7.2 Verified Theorems and Kernel Axiom Audit

| Theorem / Counterexample (`CodegenBackendParityAndUnwindContract.*`) | Line | Formal Claim | Kernel Axioms (`#print axioms`) |
| :--- | :---: | :--- | :--- |
| `mixed_backend_normal_call_preserves_result` | `153` | If every frame `f ∈ frames` satisfies `abiCompat callerProfile f.profile = true`, then `execNormalStack step callerProfile frames init = .ok (evalNormalRef step frames init)`, independent of unwind LSDA or sanitizer flags. | `[propext]` |
| `mixed_backend_normal_call_full_2x2_parity` | `180` | All 4 pairings of `{llvmProfile, craneliftDefaultProfile}²` return identical `.ok (step binId (step libId init))`. | *(none)* |
| `mixed_unwind_complete_iff_all_frames_lsda` | `373` | **Necessary & sufficient (`↔`):** For any profile assignment `profs`, `∀ stack, stack.map CallFrame.profile = profs → unwindStack stack = referenceUnwindStack stack` iff `∀ p ∈ profs, p.hasEhFrame = true ∧ p.hasLsdaCleanup = true ∧ p.hasLsdaCatch = true`. | `[propext]` |
| `fail_closed_flag_gate_prevents_silent_disable` | `520` | Under truthful `CapabilitiesMatchProfile cap profile`, `admitsFlags cap req = true` guarantees: (1) `req.sanitizerAddress = true → profile.enforcesSanitizer = true ∧ runHeapOobProbe profile = .abortedAsan`; (2) `req.panicUnwind = true → UnwindComplete profile`. | *(none)* |
| `fail_closed_unwind_admitted_stack_has_parity` | `555` | Any mixed-backend stack whose frames are each admitted under `req.panicUnwind = true` by `admitsFlags` achieves exact `unwindStack stack = referenceUnwindStack stack`. | `[propext]` |
| `ce1_eh_frame_without_lsda_leaks_callee_drop_on_cross_backend_unwind` | `592` | Constructive witness (`lib_cranelift__bin_llvm`): both frames have `hasEhFrame = true`, unwind yields `disposition = .caughtAt 1`, `executedDrops = [1]`, `leakedDrops = [0]`, diverging from reference `executedDrops = [0, 1]`, `leakedDrops = []`. | *(none)* |
| `ce2_missing_lsda_catch_turns_catch_unwind_into_uncaught_abort` | `619` | Constructive witness (`lib_llvm__bin_cranelift`): both frames have `hasEhFrame = true`, unwind yields `disposition = .uncaughtAbort`, `executedDrops = [0]`, `leakedDrops = [1]`, `missedCatches = [1]`, while reference yields `.caughtAt 1`. | *(none)* |
| `ce2b_cranelift_both_leaks_all_drops_and_aborts` | `642` | Constructive witness (`lib_cranelift__bin_cranelift`): `disposition = .uncaughtAbort`, `executedDrops = []`, `leakedDrops = [0, 1]`, `missedCatches = [1]`. | *(none)* |
| `ce3_unvalidated_sanitizer_flag_silently_passes_heap_oob` | `658` | Constructive witness: `admitsFlagsCraneliftActual req = true` and `runHeapOobProbe craneliftDefaultProfile = .silentReadSurvived`, while `admitsFlags craneliftDefaultCapabilities req = false` and `runHeapOobProbe llvmProfile = .abortedAsan`. | *(none)* |
| `cranelift_actual_gate_rejects_lto_and_coverage` | `674` | Confirms `admitsFlagsCraneliftActual` rejects `ltoThin = true` and `instrumentCoverage = true`. | *(none)* |
| `no_eh_frame_aborts_even_with_outer_llvm_catch` | `683` | Confirms missing `.eh_frame` yields `.missingEhFrameAbort 0` even when wrapped in an outer LLVM `catch_unwind`. | *(none)* |

## Boundaries

1. **`rustc_codegen_cranelift` custom `--features unwinding` and `--features inline_asm_sym` builds (`not examined` empirically):** Source inspection confirms the exact code paths gated by `cfg!(feature = "unwinding")` (`debuginfo/unwind.rs:45,143`, `base.rs:316,577`, `abi/mod.rs:860`, `intrinsics/mod.rs:1437`) and `cfg!(feature = "inline_asm_sym")` (`inline_asm.rs:119,168`, `global_asm.rs:126,164`), and confirms `bootstrap` does not enable either feature (`compile.rs:1793-1816`). Runtime execution of a custom-compiled `rustc_codegen_cranelift` dylib with `--features unwinding` was **not examined** empirically, so the runtime correctness and overhead of Cranelift's experimental `.gcc_except_table` emission remain unmeasured here.
2. **Non-`x86_64-unknown-linux-gnu` targets (`not examined` empirically; partially `unsupported` in source):** Empirical probes ran only on `x86_64-unknown-linux-gnu`. Source inspection confirms that `debuginfo/unwind.rs:124-130` skips `.eh_frame` emission entirely on `x86_64-apple-darwin` (citing `gimli-rs/object#415`), `debuginfo/unwind.rs:228-231` omits Windows SEH unwind emission (`WindowsX64`/`WindowsArm64` empty arms), `debuginfo/unwind.rs:61-63` panics (`todo!()`) for PIC unwinding on architectures other than `x86_64`/`aarch64`, and `inline_asm.rs:739,761,776,826,875` implements inline-asm wrapper prologues/epilogues only for `X86_64`, `AArch64`, and `RiscV64` (`unimplemented!` elsewhere). 32-bit `i686-*` targets are **unsupported** by Cranelift altogether.
3. **Additional security/hardening flags beyond `-Z sanitizer=address` (`derived` from exhaustive source audit; runtime `not examined`):** Exhaustive grep across all 43 source files in `compiler/rustc_codegen_cranelift/src/` proves zero references to `stack_protector`, `cf_protection`, `branch_protection`, `control_flow_guard`, `retpoline`, or any other `SanitizerSet` member (`THREAD`, `MEMORY`, `LEAK`, `HWADDRESS`, `CFI`, `KCFI`). While `-Z sanitizer=cfi` is blocked indirectly in `rustc_session` by requiring LTO (`session.rs:1656-1660`, which Cranelift rejects), live runtime probes were executed only for `-Z sanitizer=address`; runtime behavior of `-Z stack-protector=strong` or `-Z sanitizer=thread` under Cranelift was **not examined** experimentally.
4. **Local `rustc 1.98.0-nightly` host lacks `rustc-codegen-cranelift-preview` (`known not to apply` to Cranelift cells on that host):** On `2026-11-22`, live execution of `support/probe_cranelift_vs_llvm.py` on `rustc 1.98.0-nightly` (`14210df0e`) revalidated the entire LLVM column (Part A `lib_llvm__bin_llvm`, all 11 Part B LLVM cases including ASan and `objdump`, and Part C LLVM microbenchmark), while gracefully skipping Cranelift cells because that sysroot has no `codegen-backends/` directory. Dual-backend empirical numbers come from the `2026-11-21` run on `rustc 1.102.0-nightly` (`3ef0c22`, preserved in `support/cranelift_vs_llvm_differential_results_1_102_nightly.json`).
5. **Unexamined `UnwindAction::Terminate` empirical probe (`derived` from source, `not examined` at runtime):** Source inspection of `abi/mod.rs:860-862` establishes that `UnwindAction::Terminate` (used for panics crossing `extern "C"` nounwind boundaries or double panics in `Drop`) is silently rewritten to `UnwindAction::Unreachable` alongside `UnwindAction::Cleanup` when `cfg!(not(feature = "unwinding"))`, implying a panic unwinding through a Cranelift `extern "C"` boundary into an LLVM caller would fail to abort at the FFI boundary. This specific `extern "C"` boundary scenario was **not examined** with a separate runtime reproducer.
6. **Overclaiming guard on Lean formalization (`known not to apply` as machine-code verification):** `support/CodegenBackendParityAndUnwindContract.lean` proves exact abstract properties of mixed-backend ABI compatibility, System V `.eh_frame`/LSDA frame unwinding, and fail-closed flag admission; it does **not** formally verify Cranelift's ISLE lowering, `regalloc2`, `gimli` `.eh_frame` byte encoding, or LLVM's `AddressSanitizerPass`. Likewise, `100%` ABI parity on our 5-construct probe (`BigSret`, `u128`, `&str`/`Option<NonZeroU64>`, `&dyn Trait`, `#[track_caller]`) does **not** prove absence of ABI divergences on untested constructs such as `#[repr(simd)]` arguments, exotic calling conventions (`extern "rust-preserve-none"` and `extern "rust-tail"`, which fail closed at `abi/mod.rs:63-65`, or `extern "sysv64"`/`"win64"`), or packed underaligned aggregates.
7. **JIT mode (`unsupported` in shipped builds):** `lib.rs:227-232` fails closed with `"jit support was disabled when compiling rustc_codegen_cranelift"` whenever `jit` Cargo feature is off, so `driver/jit.rs` (`register_jit`) was **not examined** empirically.

## Evidence

### Primary Upstream Source Citations

- **`rust-lang/rust` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`2026-11-11`, verified byte-identical in `base.rs`, `abi/mod.rs`, `debuginfo/unwind.rs`, `driver/aot.rs`, `config.rs`, `inline_asm.rs` at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`, `2026-11-22`):**
  - `compiler/rustc_codegen_cranelift/Cargo.toml:44-49`: `unstable-features = ["jit", "inline_asm_sym"]`, `unwinding = [] # Not yet included in unstable-features for performance reasons`, `cranelift-codegen = "0.137.0"`.
  - `src/bootstrap/src/core/build_steps/compile.rs:1757-1824` (specifically `:1793-1816`): `CraneliftCodegenBackend::run` builds `compiler/rustc_codegen_cranelift/Cargo.toml` with no `--features` flags.
  - `compiler/rustc_codegen_cranelift/src/lib.rs:121-251, 272-383`: `CraneliftCodegenBackend::init` LTO (`:134-139`) and `-C instrument-coverage` (`:141-144`) fail-closed checks; `CodegenBackendInit` (`:156-161`, renamed `replaced_rustc_intrinsics`/`fallback_rustc_intrinsics` at `342d744`); `build_isa` `is_pic = "true"` (`:278`), `enable_llvm_abi_extensions = "true"` (`:298`), and `OptLevel` collapse to `"speed_and_size"` (`:306-318`).
  - `compiler/rustc_codegen_cranelift/src/config.rs:1-43`: `BackendConfig::from_opts` `-C llvm-args` validation (`"jit-mode"`, silently ignoring `"-import-instr-limit*"`, rejecting unknown options).
  - `compiler/rustc_codegen_cranelift/src/debuginfo/unwind.rs:18-250`: Unconditional `create_systemv_cie()` (`:35`) and `add_fde` (`:226`) + `.eh_frame` emission (`:235-250`), vs. `cfg!(feature = "unwinding")`-gated CIE personality/LSDA (`:45-107`) and `.gcc_except_table` emission (`:143-224`).
  - `compiler/rustc_codegen_cranelift/src/debuginfo/gcc_except_table.rs:1-100`: `GccExceptTable`, `CallSiteTable`, `ActionTable`, `TypeInfoTable` DWARF LSDA serializer.
  - `compiler/rustc_codegen_cranelift/src/unwind_module.rs:1-111`: `UnwindModule::define_function_with_control_plane` (`:95-103`) registers every defined function's `.eh_frame` FDE.
  - `compiler/rustc_codegen_cranelift/src/driver/aot.rs:44-391`: `AotDriver`, `make_module` (`UnwindModule`), `codegen_cgu`, `compile_cgu` (separate `.asm.o` assembly at `:239-253`), and `unreachable!()` LTO hooks (`:325-390`).
  - `compiler/rustc_codegen_cranelift/src/base.rs:151-229, 304-322, 531-606`: `compile_fn` ISLE catch-all ICE (`:222`), `bb_data.is_cleanup` silent skip (`:315-318`), `TerminatorKind::TailCall` `span_bug!` ICE (`:532-535`), `InlineAsm` `MAY_UNWIND` & label `span_fatal` (`:545-562`), and `TerminatorKind::UnwindResume` trap fallback (`:576-587`).
  - `compiler/rustc_codegen_cranelift/src/abi/mod.rs:39-100, 259-341, 558-958`: `clif_sig_from_fn_abi`, `conv_to_call_conv`, `c_variadic` definition `span_fatal` (`:281-286`), `#[track_caller]` (`:328-337, 558-562, 812-821`), `dyn Trait` virtual call (`:568-586`), `adjust_call_for_c_variadic` (`:643-735`), and `codegen_call_with_unwind_action` silent rewrite to `UnwindAction::Unreachable` (`:860-862`).
  - `compiler/rustc_codegen_cranelift/src/abi/{pass_mode.rs:19-355, returning.rs:10-128}` and `src/vtable.rs:14-88`: exact `PassMode`, `StructReturn`, `CastTarget`, and vtable dispatch lowering.
  - `compiler/rustc_codegen_cranelift/src/inline_asm.rs:42-295, 435-933` and `src/global_asm.rs:212-294`: `inline_asm_sym` error (`inline_asm.rs:119-124, 168-172`), out-of-line wrapper synthesis (`:530-764`), 16-byte stack slot + `Linkage::Import` call ignoring `pure`/`nomem`/`nostack` (`:880-933`), and recursive `rustc -Zcodegen-backend=llvm` assembly (`global_asm.rs:240-291`).
  - `compiler/rustc_codegen_cranelift/src/intrinsics/mod.rs:755-980, 1423-1493, 1587-1593`: `u128`/`i128` guard present in `atomic_load` (`:762-777`) and `atomic_store` (`:798-813`) but absent in `atomic_xchg`/`atomic_cxchg`/`atomic_xadd`/`atomic_xsub` (`:825-913`); silent `catch_unwind` degradation (`:1437-1447`); `va_arg` `span_fatal` (`:1588-1593`).
  - `compiler/rustc_codegen_cranelift/src/codegen_f16_f128.rs:6-120`: software libcall polyfills (`__extendhfsf2`, `__truncsfhf2`, `__eqtf2`, etc.) explaining `f16`/`f128` parity.
  - `compiler/rustc_session/src/session.rs:438-450, 1613-1660`: `CodegenBackendInit` definition and target-only sanitizer validation (`sess.target.options.supported_sanitizers`).
  - `compiler/rustc_codegen_ssa/src/traits/backend.rs:37-142` and `compiler/rustc_codegen_ssa/src/back/link.rs:1743-1790, 2985`: default `CodegenBackend::link` invoking `add_sanitizer_libraries`.
  - `compiler/rustc_codegen_llvm/src/attributes.rs:151-170, 570-576`: LLVM `SanitizeAddress` attribute attachment.
- **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19`):**
  - `trusted/lean/Trusted/MirAst.lean:682-814`: `UnwindAction`, `AssertKind`, `TerminatorKind`, and `BasicBlock.cleanup` definitions aligned with `rustc_middle::mir`.
  - `trusted/rustc-capture/src/driver.rs:25-152`: pinned compiler verification and `rustc_driver::Callbacks` scaffold.
- **`google/zerocopy` at `aa7c31671cb5ce509551edafa23c6865df83b180` (`v0.8.48`, `2026-03-28`):** Crate benchmarked in Part C.

### Preserved Package Support Artifacts

- [`support/probe_cranelift_vs_llvm.py`](support/probe_cranelift_vs_llvm.py): Standalone, self-contained Python 3.10+ differential probe reproducing Part A (2x2 cross-backend ABI & unwind/drop matrix + `readelf -SW` section audit), Part B (11-case feature-gate, ICE, ASan fail-open matrix + `objdump -d`/`nm` inspection of `add_asm`), and Part C (compute microbenchmark + optional `--zerocopy-dir` full-crate build). Automatically detects whether `rustc_codegen_cranelift` is installed in the active sysroot.
- [`support/cranelift_vs_llvm_differential_results_1_102_nightly.json`](support/cranelift_vs_llvm_differential_results_1_102_nightly.json): Complete dual-backend empirical dataset acquired `2026-11-21` on `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM `23.1.5`, `x86_64-unknown-linux-gnu`), covering all 4 Part A cells, all 11 Part B cases (including `add_asm` disassemblies and Cranelift ICE traces), and Part C (`zerocopy 0.8.48` + compute microbenchmark), scrubbed of ephemeral paths and PIDs.
- [`support/llvm_revalidation_1_98_nightly.json`](support/llvm_revalidation_1_98_nightly.json): Live execution receipt acquired `2026-11-22` by running `support/probe_cranelift_vs_llvm.py` on `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`), confirming exact LLVM execution of Part A (`SRET=60 ... LINE=11`, `CAUGHT=true BIN_DROPS=1 LIB_DROPS=1`, `.gcc_except_table` = `11,140 B`, `.eh_frame` = `20,824 B`), all 11 Part B cases (including `add_asm` `7 B` / `3` instructions and live ASan `heap-buffer-overflow` `rc = 1`), and Part C (`10d506cbbf1d1512`).
- [`support/CodegenBackendParityAndUnwindContract.lean`](support/CodegenBackendParityAndUnwindContract.lean): Kernel-checked `Lean v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) formalization verified `2026-11-22` with exit code `0`, `-DwarningAsError=true`, zero `sorry`, zero `Classical.choice`, zero `omega`/`bv_decide`/`native_decide`, zero `partial def`, and `#print axioms` output confirming at most `[propext]`.

## Revalidation

### 1. Re-run the Differential `rustc` Probe (Dual-Backend or LLVM-Only)

On any `x86_64-unknown-linux-gnu` host with nightly `rustc` (and `rustup component add rustc-codegen-cranelift-preview` for full dual-backend execution; add `--zerocopy-dir <path>` to include the `zerocopy` rlib timing benchmark):

```bash
python3 support/probe_cranelift_vs_llvm.py --output /tmp/clif_vs_llvm_reval.json
```

Discriminating invariants to check in `/tmp/clif_vs_llvm_reval.json`:
- **Part A ABI parity:** All 4 cells emit `SRET=60 MIXED=3000000000000000a STR=542 DYN=9077 LINE=11` with `run_rc == 0`.
- **Part A unwind asymmetry (detects if `unwinding` feature becomes enabled upstream):**
  - If `lib_cranelift__bin_llvm.unwind_catch_and_drop.stdout` changes from `CAUGHT=true BIN_DROPS=1 LIB_DROPS=0` to `LIB_DROPS=1`, or `lib_llvm__bin_cranelift.unwind_catch_and_drop.run_rc` changes from `101` to `0`, then upstream enabled `rustc_codegen_cranelift`'s `unwinding` feature and LSDA emission.
- **Part B fail-open / ICE regressions:**
  - If `sanitizer_address_heap_oob.cranelift.compile_rc` changes from `0` to `1` (fail-closed) or `run_rc` changes from `0` to `1` (ASan enforced), the silent ASan fail-open defect has been fixed.
  - If `explicit_tail_calls_become.cranelift.compile_rc` or `atomic_u128_intrinsic.cranelift.compile_rc` changes from `101` (ICE) to `0` or `1`, those ICE boundaries have been resolved.
  - If `inline_asm_basic.cranelift.has_inline_asm_wrapper_sym` becomes `false`, Cranelift has gained native inline-asm lowering.

### 2. Cheap Upstream Source Diff Checks

Without executing a compiler, diffing four small regions against `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` detects whether any structural finding has changed:

1. `compiler/rustc_codegen_cranelift/Cargo.toml` (`[features]`) and `src/bootstrap/src/core/build_steps/compile.rs` (`impl CommandLineStep for CraneliftCodegenBackend`): check whether `unwinding` or `inline_asm_sym` is enabled in default bootstrap builds.
2. `compiler/rustc_codegen_cranelift/src/lib.rs` (`CraneliftCodegenBackend::init` and `build_isa`) and `compiler/rustc_session/src/session.rs` (`CodegenBackendInit`, `validate_commandline_args_with_session_available`): check whether `sess.sanitizers()` is validated against backend capabilities and whether `OptLevel` still maps all non-zero levels to `"speed_and_size"`.
3. `compiler/rustc_codegen_cranelift/src/base.rs` (`TerminatorKind::TailCall`, `bb_data.is_cleanup`) and `compiler/rustc_codegen_cranelift/src/intrinsics/mod.rs` (`atomic_xadd`, `sym::catch_unwind`): check whether `u128` RMW guards or `TailCall` lowering were added.
4. `compiler/rustc_codegen_cranelift/src/inline_asm.rs` (`call_inline_asm`) and `src/global_asm.rs` (`compile_global_asm`): check whether `asm!` still synthesizes out-of-line wrappers assembled via recursive `rustc -Zcodegen-backend=llvm`.

### 3. Re-verify the Lean 4 Formalization Under Strict Kernel Flags

```bash
LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
  ~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/CodegenBackendParityAndUnwindContract.lean
```

Confirm exit code `0`, zero warnings, and that `#print axioms` lists only `[]` or `[propext]` for all 11 theorems (zero `sorryAx`, zero `Classical.choice`, zero `Lean.ofReduceBool`).
