# rustc Static Allocations, Implicit Rvalue Promotion, ELF Thread-Local Storage, and Linker-Retained Section Initializers

## Summary

On ELF64 GNU/Linux (`x86_64-unknown-linux-gnu`) with `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `LLVM 22.1.6` (`fc4aad7b5db3fff421df9a9637605b9ca5667881`), and `GNU Binutils 2.47`, constant promotion, static placement, ELF TLS access/destruction, and linker section retention obey a single cross-layer mutability, totality, and reachability contract:

1. **Implicit Rvalue Promotion (`promote_consts`):** The MIR pass `PromoteTemps` lifts candidate rvalue temporaries out of runtime function bodies into read-only promoted MIR constants (`InternKind::Promoted` -> `GlobalAlloc::Memory` -> `private unnamed_addr constant` in LLVM IR -> `.rodata`) only when the referenced type is free of both interior mutability (`!HasMutInterior`, unless borrowed exclusively as `&mut [T; 0]`) and destructors (`!NeedsDrop`), its backing value avoids runtime failure paths (`Div`/`Rem` only with known non-zero divisor and no signed `MIN / -1`; array indices proven `idx < len`), and any `const fn` call either carries `#[rustc_promotable]` or sits in an unconditionally executed `START_BLOCK` chain inside a `Static` or non-inline `Const` body. When a `validate_candidate` borrow directly references `&arr[oob]` rather than arithmetic over it, `rustc` still promotes the backing array literal while retaining the runtime bounds `assert` before taking `&(*promoted)[idx]`.
2. **Global Allocation Routing & `RELRO`:** `intern_const_alloc_recursive` partitions interned memory across read-only (`.rodata`), relocation-time read-only (`.data.rel.ro` + `PT_GNU_RELRO` under PIC/PIE), writable `.data` / `.bss`, and per-thread `.tdata` / `.tbss`. Critically, `TargetLoweringObjectFile::isSuitableForBSS` returns `false` whenever `GV->isConstant()`, so even all-zero `Freeze` immutable statics (`[0u8; 64]`) and `#[thread_local]` `Freeze` zero statics emit into `.rodata` and `.tdata` (`PROGBITS`), never `.bss` or `.tbss` (`NOBITS`). Under PIC/PIE, pointer-bearing immutable `Freeze` statics land in writable `.data.rel.ro` inside relocatable `.o` objects and are remapped read-only via `PT_GNU_RELRO` after dynamic relocation (`SIGSEGV` `-11` on runtime writes, identical to `.rodata`), whereas under `-C relocation-model=static` they route straight to `.rodata` with `.rela.rodata` fixups.
3. **ELF `PT_TLS`, 4 TLS Models, and `std::thread_local!` Lifecycle:** Every `PT_TLS` program header defines a thread template of length `p_memsz` consisting of `p_filesz` initialized bytes from `.tdata` followed by `p_memsz - p_filesz` zero bytes for `.tbss`, instantiated disjointly for each OS thread. Pre-link `-Z tls-model` differentiates all four ELF models inside `--crate-type=cdylib` `.o` objects (`global-dynamic` -> `R_X86_64_TLSGD` + `__tls_get_addr`; `local-dynamic` -> `R_X86_64_TLSLD` + `R_X86_64_DTPOFF32`; `initial-exec` -> `R_X86_64_GOTTPOFF` + `%fs:`; `local-exec` -> `R_X86_64_TPOFF32`, which fails linking in `-shared` libraries), whereas `--crate-type=bin` PIE codegen upgrades `global-dynamic` and `local-dynamic` to `InitialExec` via `LLVMRustSetModulePIELevel` before the linker relaxes `IE -> LE` to direct negative `%fs:` offsets. High-level `std::thread_local!` on `cfg(target_thread_local)` selects a 4-cell storage matrix (`const` vs lazy init × `!Drop` vs `Drop`), registering destructors dynamically per accessed slot via weak `__cxa_thread_atexit_impl` (with per-thread `destructors::list` fallback), marking slots `State::Destroyed` prior to running `drop_in_place` (blocking re-entrant `try_with`), and running destructors in strict LIFO access order without touching unaccessed threads.
4. **Linker GC Retention & Archive Boundaries:** `#[used(compiler)]` emits `@llvm.compiler.used` without `SHF_GNU_RETAIN` (`'R'`), surviving LLVM DCE while still being stripped by `rust-lld` and `GNU ld --gc-sections`. By contrast, `codegen_attrs.rs` lowers both `#[used(linker)]` and bare `#[used]` (on non-Illumos ELF targets, contradicting an outdated comment in `consts.rs`) to `@llvm.used`, which LLVM lowers to section flag `SHF_GNU_RETAIN` (`AR` / `WAR`), preserving unreferenced custom sections and `.init_array` entries across `--gc-sections`. However, `.init_array` and `SHF_GNU_RETAIN` inside an `.rlib` static archive member do not force linker extraction if no root-reachable symbol causes the linker to pull that archive member.
5. **Verification Boundary & Lean 4 Mechanization:** Anneal's current minimal MIR verifier AST (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted/MirAst.lean`) admits only scalar and ZST `ConstLit` values and rejects promoted pointer constants and `Rvalue::ThreadLocalRef` as `.unsupported`. All four invariants and two sharpness counterexamples (`ce1_promoting_unsafecell_into_rodata_unsound` and `ce2_used_compiler_dropped_by_linker_gc`) are proved cleanly in `Lean v4.34.1` (`1,311` lines, `19` theorems, zero `sorry`, zero `Classical.choice`, zero `omega`/`bv_decide`/`native_decide`, zero `partial def`, zero `._unsafe_rec`).

## Applicability

This reference covers the interaction between the five pinned upstream software artifacts and two supporting specifications/toolchains identified in `REPORT.json`:

- **Primary Compiler & Runtime Under Study:** `rust-lang/rust` at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`) on host and target `x86_64-unknown-linux-gnu`. Source inspection covers MIR rvalue promotion, const interning, SSA/LLVM backend constant & static codegen, codegen attribute parsing, and `std::sys::thread_local`. Empirical runs exercise both stable constructs and nightly unstable features (`#![feature(thread_local)]`, `#![feature(used_with_arg)]`, `-Z dump-mir=PromoteTemps`, `-Z tls-model=...`, `--emit=llvm-ir`).
- **Backend & Linker Behavior:** `llvm/llvm-project` at commit `fc4aad7b5db3fff421df9a9637605b9ca5667881` (`llvmorg-22.1.6`) and the bundled `rust-lang/llvm-project` fork at `08c84e69a84d95936296dfcab0e38b34100725d5` (`LLVM 22.1.6` / `rust-lld`). Upstream `llvm/llvm-project` matches the exact `22.1.6` release line bundled in the examined `rustc` toolchain; both `rust-lld` and `GNU ld` (`GNU Binutils for Debian 2.47`) are tested directly with `-Clink-arg=-Wl,--gc-sections`.
- **Language Documentation:** `rust-lang/reference` at `ad35aca481751a06afeb23820a672b0f3b11a476` (`src/items/static-items.md`, `src/items/constant-items.md`, `src/destructors.md`, `src/const_eval.md`) supplies normative language rules against which compiler and linker implementation details are compared.
- **Verification Consumer Contract:** `joshlf/anneal` at commit `c131b320eeeb26ef692e5afd5ec8db49ee518613` defines how Rust MIR subsets and kernel-trusted proofs interact (`trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `trusted/audit/TrustedBoundary.lean`). Findings here establish what extension invariants are needed if Anneal broadens `ConstLit` or `Rvalue` lowering beyond scalar/ZST items.
- **Mechanization Kernel:** `leanprover/lean4` at commit `5045d0056413266e57c625dcd7c365b10e377c52` (`Lean v4.34.1`, Linux `x86_64` release) kernel-checks `support/StaticsPromotedsAndTlsSoundness.lean`.

### Scope Qualifications Across Targets and Invocation Modes

- **Target ABI & TLS Architecture:** Findings for `std::sys::thread_local::native` (`#[thread_local]` + `EagerStorage`/`LazyStorage`) and `__cxa_thread_atexit_impl` assume GNU/Linux ELF64 with `cfg(target_thread_local)` and glibc weak `__cxa_thread_atexit_impl`. Targets lacking native ELF TLS fall back to OS keys (`library/std/src/sys/thread_local/os.rs` and `guard/key.rs`). Exact instruction encodings and relocation names (`R_X86_64_TLSGD`, `TLSLD`, `DTPOFF32`, `GOTTPOFF`, `TPOFF32`, `%fs:`) are specific to `x86_64` ELF64; the four abstract `TlsModel` rules apply more broadly across ELF architectures that implement those four models.
- **Bare `#[used]` Target Exception:** While `#[used]` lowers to `USED_LINKER` (`@llvm.used`) on Linux ELF targets, `compiler/rustc_codegen_ssa/src/codegen_attrs.rs:173-185` explicitly special-cases `Os::Illumos` to `USED_COMPILER` (`@llvm.compiler.used`). Do not extrapolate ELF GNU/Linux bare `#[used]` retention behavior to Illumos, Mach-O, COFF, or `#[no_std]` bare-metal linkers lacking `SHF_GNU_RETAIN` / `--gc-sections` support.
- **Relocation Model Sensitivity:** `.data.rel.ro` placement under `PT_GNU_RELRO` applies specifically to relocatable/PIC/PIE builds (`Reloc::PIC_`, the default on modern Linux). Under `-C relocation-model=static`, pointer-bearing immutable `Freeze` statics route into `.rodata` with `.rela.rodata` relocations instead.

## Findings

### 1. MIR Implicit Rvalue Promotion (`PromoteTemps` in `promote_consts.rs`)

Basis: normative documentation (`rust-lang/reference`) + source (`rust-lang/rust`) + execution (`s1_promote_consts_mir`)

`PromoteTemps` (`compiler/rustc_mir_transform/src/promote_consts.rs:37-67`) transforms shared or constant-eligible rvalue temporaries within a MIR body into synthetic `Mir::Promoted` sub-bodies whose address can outlive the enclosing stack frame as `'static` (or outlive a call's lexical scope). The transform executes a single-pass candidate collector followed by bottom-up validation and MIR rewriting (`promote_consts.rs:71-1091`).

#### 1.1 Collector State Machine and Multi-Use Cloning

`TempState` (`promote_consts.rs:71-83`) classifies every temporary local into four states:
- `Undefined`: no defining assignment observed yet.
- `Defined { location, uses, valid }`: a single defining write at `location` with `uses` counted during traversal.
- `Unpromotable`: initialized in multiple places, mutated, moved conditionally, or rejected.
- `PromotedOut`: validated and queued for lifting into a promoted body.

Crucially, `Collector::visit_terminator` / drop inspection (`promote_consts.rs:112`) ignores `TerminatorKind::Drop` uses when counting uses, and `uses > 1` sets `keep_original = true` (`promote_consts.rs:769-771`). As observed in `s1_promote_consts_mir` (`promo_multiuse_temp` and `promo_arith_and_index`), when a promoted constant local is also consumed by non-promoted value arithmetic, `rustc` preserves a local copy for the non-promoted use while still emitting `const Unevaluated(..., promoted: Some(promoted[0]))` for the borrowed reference, reducing `StorageLive` count where pure borrow temporaries disappear (`5 -> 4` in `promo_multiuse_temp`, `7 -> 6` in `promo_arith_and_index`).

#### 1.2 Qualification, Fallibility, and Function-Call Promotion Gateways

`Validator` (`promote_consts.rs:194-683`) enforces a conjunctive set of soundness guards across locals, places, operands, borrows, rvalues, and calls:

1. **Borrow-Kind and Mutability Rules (`validate_ref`, `L393-423`):**
   - `BorrowKind::Shared`: rejects any local/place whose type satisfies `qualifs::HasMutInterior` (`L402-407`), blocking `Cell`, `RefCell`, `UnsafeCell`, and atomics from promotion into `.rodata`.
   - `BorrowKind::Mut` (both default `MutBorrowKind::Default` and delayed-activation mutable borrows): accepts **only** zero-sized empty arrays `[T; 0]` (`L411-419`), making `&mut []` promotable because no mutable byte exists in memory (`promo_empty_mut_slice` in `s1` reduces `StorageLive` `5 -> 4` with `promoted_ref_count = 1`), while rejecting all non-zero-length `&mut [T; N]` literals.
2. **Destructor Exclusion (`validate_local`, `L237-283`):**
   - Any local satisfying `qualifs::NeedsDrop` is rejected (`L244-246`), even if its constructor is pure and trivial (`reject_needs_drop` using `HasDrop(7)` yields `promoted_ref_count = 0`, `StorageLive 2 -> 2`). Promotion elides runtime `StorageLive`/`StorageDead`/`Drop` on the promoted slot (`L1065-1088`), so promoting a `NeedsDrop` value would either suppress destructors or attempt multiple drops of a shared global.
3. **Division, Remainder, and Array Indexing Guards (`validate_rvalue` `L485-518`, `validate_place` `L326-345`, `validate_candidate` `L194-213`):**
   - Integer `BinOp::Div` and `BinOp::Rem` require the divisor operand to be a compile-time constant known non-zero and not equal to `MIN / -1` signed overflow (`L485-518`).
   - `ProjectionElem::Index` inside `validate_place` (`L326-345`) requires a constant index strictly less than array length (`idx < len`).
   - **Subtle Compiler Edge Case (`validate_candidate` vs `validate_place`):** `Validator::validate_candidate` (`L194-213`) checks `validate_local(place.local)` (`L200`) and `validate_ref(*kind, place)` (`L204`) and rejects `ProjectionElem::Deref` (`L208-210`), but does **not** re-run `validate_place` on an outer `ProjectionElem::Index` of the borrowed `place` itself. Consequently, in `s1_promote_consts_mir`:
     - `&([1u32, 2][5])` inside `reject_fallible_div_and_oob` produces `promoted_ref_count = 1` (`promoted[0]` is `[1u32, 2]`), while the runtime MIR keeps `assert(const 5usize < const 2usize)` before evaluating `&(*_21)[_14]`. Thus no panicking computation executes during CTFE—only the pure backing array promotes.
     - By contrast, `&([1u32, 2][5] + 1)` inside `reject_nested_oob_index` places `[1u32, 2][5]` inside an operand rvalue, forcing `validate_place` (`L326-345`) to reject out-of-bounds indexing and yielding `promoted_ref_count = 0` (`StorageLive 6 -> 6`).
   - `Rvalue::ThreadLocalRef` (`L444`), `CastKind::PointerExposeProvenance` (`L447`), raw/function pointer binary ops (`L468-482`), and `Operand::RuntimeChecks` (`L365`) are unconditionally rejected. Union field projections are rejected (`L349-352`).
4. **Const Function Calls and Control-Flow Safety (`validate_call` `L635-683`, `promotion_safe_blocks` `L598-633`):**
   - Ordinary `const fn` calls are **not** promoted inside runtime `fn` items (`reject_const_fn_in_fn` with `checked_pos(5)` gives `promoted_ref_count = 0`, `StorageLive 2 -> 2`). Only calls annotated with `#[rustc_promotable]` are eligible in arbitrary runtime functions (`L650-654`).
   - Inside `ConstContext::Static` or non-inline `Const` items (`L660-663`), arbitrary `const fn` calls promote **only** within basic blocks proved unconditionally executed from `START_BLOCK` along unique non-branching `Goto` / `Assert` / pure `Call` chains (`promotion_safe_blocks`, `L598-633`). In `s1`'s `SAFE_PROMO_IN_CONST`, `&checked_pos(5)` in the entry chain promotes (`promoted_ref_count = 1`, `StorageLive 6 -> 5`), whereas `&checked_pos(0)` inside the dead `if false` branch stays outside the unconditionally executed chain and never evaluates during promotion.
   - `should_evaluate_for_promotion_checks` (`L687-705`) skips promotion evaluation inside `Const::Ty` and `DefKind::InlineConst` to avoid query cycle failures (`#150464`).

| `s1_promote_consts_mir` Item | Rule Tested | `before_lines` -> `after_lines` | `StorageLive` Before -> After | `promoted_ref_count` |
|---|---|---|---|---|
| `promo_arith_and_index` | Valid `idx < len` + non-zero const `Div` (`100 / 4`) | `70 -> 69` | `7 -> 6` | `1` (`[0]`) |
| `promo_empty_mut_slice` | `&mut [u32; 0]` coerced to `&'static mut [u32]` | `46 -> 45` | `5 -> 4` | `1` (`[0]`) |
| `promo_multiuse_temp` | Multi-use value (`uses > 1`, `keep_original = true`) | `44 -> 43` | `5 -> 4` | `1` (`[0]`) |
| `reject_unsafecell` | `HasMutInterior` (`Cell::new(42u32)`) exclusion | `71 -> 71` | `8 -> 8` | `0` |
| `reject_needs_drop` | `NeedsDrop` (`HasDrop(7)`) exclusion | `30 -> 30` | `2 -> 2` | `0` |
| `reject_fallible_div_and_oob` | `1/0`, `MIN/-1`, plus direct `&([1,2][5])` vs `+ 1` | `175 -> 177` | `20 -> 20` | `1` (`[0]` for `[1, 2]`, runtime `assert` kept) |
| `reject_nested_oob_index` | Nested `&([1, 2][5] + 1)` rejected in `validate_place` | `69 -> 69` | `6 -> 6` | `0` |
| `reject_const_fn_in_fn` | Non-`#[rustc_promotable]` `const fn` in runtime `fn` | `29 -> 29` | `2 -> 2` | `0` |
| `SAFE_PROMO_IN_CONST` | `checked_pos(5)` in `START_BLOCK` vs dead `checked_pos(0)` | `64 -> 64` | `6 -> 5` | `1` (`[0]`) |

### 2. Static & Constant Global Allocations (`intern.rs`, `consts.rs`, and ELF Placement)

Basis: source (`rust-lang/rust` + `llvm/llvm-project`) + execution (`s2_global_alloc_and_elf_sections`)

Once a `const`, promoted expression, or `static` evaluates via CTFE into an allocation, `rustc_const_eval::interpret::intern` assigns recursive mutability and memory placement before LLVM codegen maps the allocation to ELF sections.

#### 2.1 `InternKind` Mutability Rules

`intern_const_alloc_recursive` (`compiler/rustc_const_eval/src/interpret/intern.rs:179-240`) computes a triple `(alloc_mutability, inner_ref_mutability, allow_nested_interior_mut)` parameterized by `InternKind`:
- `InternKind::Constant | InternKind::Promoted`: always `(Mutability::Not, Mutability::Not, false)`. Nested allocations under a constant or promoted rvalue cannot retain writable interior mutability.
- `InternKind::Static(Mutability::Not)`: sets `alloc_mutability` to `Mutability::Not` when `is_freeze`, or `Mutability::Mut` when `!is_freeze` (interior mutability such as `Cell` or `AtomicU64`), while keeping read-only inner reference handling (`Not`, with `enforce = true`).
- `InternKind::Static(Mutability::Mut)`: `(Mutability::Mut, Mutability::Mut, true)` for `static mut`.

Nested `static` items inside `#[thread_local]` statics trigger a hard compile error (`NestedStaticInThreadLocal`, `intern.rs:162-164`).

#### 2.2 `GlobalAlloc`, LLVM Global Emission, and the Constant Zero `.bss`/`.tbss` Rule

`compiler/rustc_middle/src/mir/interpret/mod.rs:251-279` classifies compile-time addresses into five `GlobalAlloc` variants: `Function`, `VTable`, `Static(DefId)`, `Memory(ConstAllocation)`, and `TypeId`. During codegen (`compiler/rustc_codegen_ssa/src/mir/constant.rs:1-107` and `operand.rs:150-318`):
- Scalar and zero-sized constants bypass memory emission unless referenced by address.
- Indirect / slice constants invoke `static_addr_of` (`compiler/rustc_codegen_llvm/src/consts.rs:236-286`), emitting `PrivateLinkage` + `UnnamedAddr::Global` globals (`static_addr_of_mut` -> `static_addr_of_impl`, cached in `cx.const_globals`, marked `set_global_constant(gv, true)`).
- Static items execute `codegen_static_item` (`consts.rs:410-539`), calling `set_global_constant(g, true)` iff `alloc.mutability.is_not()` (`consts.rs:474-476`), applying `set_thread_local_mode` for `#[thread_local]` (`consts.rs:480-482`), and assigning `#[link_section]` (`consts.rs:506`).
- `common::scalar_to_backend` (`compiler/rustc_codegen_llvm/src/common.rs:269-365`) asserts `!tcx.is_thread_local_static(def_id)` when resolving `GlobalAlloc::Static` inside a constant scalar pointer, preventing non-TLS statics from baking thread-local pointers into constant memory.

LLVM's target-independent section classifier `TargetLoweringObjectFile::getKindForGlobal` and `isSuitableForBSS` (`llvm/lib/Target/TargetLoweringObjectFile.cpp:82-99, 248-368`), paired with ELF section selection (`llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp:616-632, 871-955`), enforces four empirical rules confirmed in `s2_global_alloc_and_elf_sections`:

| Symbol (`s2`) | Rust Kind & Initializer | LLVM IR Global Form (`rustc --emit=llvm-ir`) | PIC `.o` Section & Flags (`readelf -SW`) | Runtime Mutability Behavior |
|---|---|---|---|---|
| `IMMUT_SCALAR_STATIC` | `static` `[0x42; 64]` (`Freeze`) | `dso_local constant [64 x i8] c"BBB..."` | `.rodata.IMMUT_SCALAR_STATIC` (`PROGBITS`, `A`, `64B`) | Write triggers `SIGSEGV` (`rc = -11`) |
| `ZERO_IMMUT_STATIC` | `static` `[0; 64]` (`Freeze`, all zero) | `dso_local constant [64 x i8] zeroinitializer` | `.rodata.ZERO_IMMUT_STATIC` (`PROGBITS`, `A`, `64B`) | Not `.bss`; `isSuitableForBSS` rejects `isConstant()` |
| `PROMOTED_0x99` | Promoted `&[0x99u8; 32]` | `@alloc_... = private unnamed_addr constant [32 x i8]` | `.rodata` / `.rodata.cst32` (`PROGBITS`, `A`/`AM`) | Mapped in `RO` load segment |
| `RELRO_PTR_STATIC` | `static` `RelroEntry` (`Freeze`, relocs) | `constant <{ [8 x i8], ptr, ptr }>` | PIC: `.data.rel.ro.RELRO_PTR_STATIC` (`WA`, `24B`); Static model: `.rodata` (`A`) + `.rela.rodata` | PIC write after dynamic reloc triggers `SIGSEGV` (`rc = -11`) |
| `MUT_NONZERO_STATIC` | `static` `AtomicU64::new(0x1122...)` | `global [8 x i8] c"..."` | `.data.MUT_NONZERO_STATIC` (`PROGBITS`, `WA`, `8B`) | Writable RW mapping |
| `MUT_ZERO_STATIC` | `static` `AtomicU64::new(0)` | `global [8 x i8] zeroinitializer` | `.bss.MUT_ZERO_STATIC` (`NOBITS`, `WA`, `8B`) | Zero-filled writable RW mapping |
| `TLS_NONZERO_CELL` | `#[thread_local]` `Cell::new(0xDEAD...)` | `thread_local local_unnamed_addr global [8 x i8]` | `.tdata.TLS_NONZERO_CELL` (`PROGBITS`, `WAT`, `8B`) | Writable per-thread slot |
| `TLS_ZERO_CELL` | `#[thread_local]` `Cell::new(0)` | `thread_local local_unnamed_addr global zeroinitializer` | `.tbss.TLS_ZERO_CELL` (`NOBITS`, `WAT`, `8B`) | Zero-initialized per-thread slot |
| `TLS_ZERO_FREEZE` | `#[thread_local]` `u64 = 0` (`Freeze`, zero) | `thread_local local_unnamed_addr constant zeroinitializer` | `.tdata.TLS_ZERO_FREEZE` (`PROGBITS`, `WAT`, `8B`) | Not `.tbss`; `isConstant()` forces `.tdata` |

Both `rust-lld` and `GNU ld 2.47` merge `.data.rel.ro` into `PT_GNU_RELRO` (`flags: R`; `rust-lld`: `filesz 10032`, `memsz 13056`; `GNU ld`: `filesz 9896`, `memsz 9896`), allowing the dynamic loader to apply relocations (`R_X86_64_RELATIVE`, `GLOB_DAT`) before `mprotect(..., PROT_READ)` freezes the region prior to user entry. Invoking the `s2` PIE binary with `write_rodata` or `write_relro` empirically aborts with signal `11` (`SIGSEGV`), confirming read-only protection of both `.rodata` and post-relocation `PT_GNU_RELRO`.

### 3. ELF Thread-Local Storage: Access Models, `PT_TLS`, and `std::thread_local!` Lifecycle

Basis: source (`rust-lang/rust` + `llvm/llvm-project`) + execution (`s3_tls_models_x86_64`, `s5_tls_multithread_and_lifo_drop_order`)

#### 3.1 Compiler Model Selection, PIE Upgrade, Linker Relaxation, and Four ELF TLS Models

`rustc_session::Session::tls_model` (`compiler/rustc_session/src/session.rs:736-746`) resolves `-Z tls-model` against `TlsModel` (`compiler/rustc_target/src/spec/mod.rs:1002-1012, 2404-2406, 2837`), defaulting to `TlsModel::GeneralDynamic`. Codegen initialization (`compiler/rustc_codegen_llvm/src/context.rs:170-178, 252-266, 632-658`) translates this into LLVM's TLS model (`to_llvm_tls_model`) and crucially sets **`LLVMRustSetModulePIELevel`** whenever `CrateType::Executable` is built (`context.rs:252-266`).

Inside LLVM, `TargetMachine::getTLSModel` (`llvm/lib/Target/TargetMachine.cpp:185-287`) inspects PIC vs PIE module flags and `isDSOLocal()` / `isGlobalVariable` preemptability: for `IsSharedLibrary` (`PIC && !IsPIE`) it preserves `GeneralDynamic` or `LocalDynamic`, whereas for executables (`IsPIE || !PIC`) it upgrades dynamic models to `InitialExec` or `LocalExec` (via `max(SelectedModel, Model)` and `dso_local`). Cross-crate references to `#[thread_local]` statics route through `Rvalue::ThreadLocalRef` -> `InstanceKind::ThreadLocalShim` when `needs_thread_local_shim(def_id)` holds (`compiler/rustc_codegen_ssa/src/mir/rvalue.rs:643-658`).

Empirical compilation and inspection of `s3_tls_models_x86_64` across `--crate-type=cdylib` and `--crate-type=bin` PIE demonstrates all four x86-64 ELF TLS access sequences and their link-time transformations:

| `-Z tls-model` | `cdylib` `.o` Relocations & x86-64 Sequence | `cdylib` `.so` Dynamic Relocs (`readelf -rW`) | PIE Executable `.o` Codegen -> Post-Link PIE Relaxation |
|---|---|---|---|
| `global-dynamic` | `2` `R_X86_64_TLSGD`, `2` `PLT32`: `data16 lea 0(%rip),%rdi` + `data16 data16 rex.W call __tls_get_addr` per symbol | `R_X86_64_DTPMOD64: 5`, `R_X86_64_DTPOFF64: 2` (`cdylib_link_rc: 0`) | `LLVMRustSetModulePIELevel` upgrades to `R_X86_64_GOTTPOFF` (`InitialExec`); `lld` relaxes `mov reg, 0(%rip)` -> `mov $0xffffffffffffffa0,%rcx` + `%fs:(%rdx)` (`LE`) |
| `local-dynamic` | `1` `R_X86_64_TLSLD`, `1` `PLT32` (`__tls_get_addr` once for module), `3` `R_X86_64_DTPOFF32` (`0(%rax)`) | `R_X86_64_DTPMOD64: 3`, **`0` `DTPOFF64`** (`cdylib_link_rc: 0`) | LLVM upgrades to `GOTTPOFF` in PIE `.o`; `lld` relaxes to `mov $0xffffffffffffffa0,%rcx` / `-0x38` + `%fs:` |
| `initial-exec` | `2` `R_X86_64_GOTTPOFF`: `mov 0(%rip),%rcx` + `%fs:(%rcx)` (static-TLS GOT offset) | `R_X86_64_DTPMOD64: 3`, `R_X86_64_TPOFF64: 2` (`cdylib_link_rc: 0`) | Identical `GOTTPOFF` in `.o`; `lld` relaxes `IE -> LE` (`mov $0xffffffffffffffa0,%rcx`, `-0x38` in `%rdx`) |
| `local-exec` | `3` `R_X86_64_TPOFF32`: direct `mov %fs:0x0,%rax` (`read/write/add` direct `%fs:` offset) | **`cdylib_link_rc: 1`** (rejected in `-shared` link) | Emits `R_X86_64_TPOFF32` directly in `.o`; linked PIE fixes `%fs:0xffffffffffffffc8` & `%fs:0xffffffffffffffa0` with zero dynamic relocs |

Every PIE executable (`global-dynamic`, `local-dynamic`, `initial-exec`, `local-exec`) runs with `pie_exec_rc = 0` outputting `TLS_MODEL_OK r1=0x102030405060708 r2=0x10203040506070b` against identical `PT_TLS` layout (`filesz_tdata = 40`, `memsz_total = 96`, `tbss_bytes = 56`, `flags = R`).

#### 3.2 `PT_TLS` Template Initialization and `std::thread_local!` Storage Matrix

In `s5_tls_multithread_and_lifo_drop_order`, the linked binary carries `PT_TLS` (`filesz = 96`, `memsz = 344`, `.tbss = 248`) and references the weak libc symbol `__cxa_thread_atexit_impl` (`uses_weak_cxa_thread_atexit_impl_sym = true`). Spawning four worker threads proves each thread receives a fresh copy of `.tdata` (`FAST_TDATA = 0x1000`) and zeroed `.tbss` (`FAST_TBSS = 0`), producing disjoint post-mutation tuples `[(4097, 8193, 70), (4098, 8194, 71), (4099, 8195, 72), (4100, 8196, 73)]` while the main thread still observes `FAST_TDATA == 0x1000` and `FAST_TBSS == 0`.

Source inspection of `library/std/src/sys/thread_local/` establishes the runtime architecture on Linux:
- **Platform Dispatch (`mod.rs:1-222`):** Selects `no_threads`, `native` (`cfg(target_thread_local)`), or `os`. Linux configures `destructors::linux_like` (`L58-80`), `guard::key` (`L85-135`), and `abort_on_dtor_unwind` (`L205-222`).
- **Four-Cell Native Storage Matrix (`native/mod.rs:1-139`):**
  1. `const` init + `!needs_drop::<T>()`: stored directly as a bare `#[thread_local]` `T` with zero state machine or destructor hook.
  2. `const` init + `needs_drop::<T>()` (`native/eager.rs:1-75`): `#[repr(C)] Storage<T> { val: UnsafeCell<T>, state: Cell<State> }`. `get()` lazily calls `destructors::register` on first access (`L43-54`), so unaccessed threads never run destructors.
  3. Lazy runtime init + `!needs_drop::<T>()` (`native/lazy.rs:1-124`): `Storage<T, !>` where the destroyed marker type is `!` (no destructor needed; re-entrant recursive initialization overwrites `State::Alive` and drops any previous temporary without double-registering).
  4. Lazy runtime init + `needs_drop::<T>()` (`native/lazy.rs:1-124`): `Storage<T, ()>` registers destructor once upon transition to `State::Alive`.
- **Pre-Drop `Destroyed` Marking & LIFO Destructor Execution (`eager.rs:70-72`, `lazy.rs:116-121`, `linux_like.rs:1-55`, `list.rs:1-41`):**
  - `destructors::linux_like::register` invokes weak `extern "C" fn __cxa_thread_atexit_impl` with `&__dso_handle`, falling back to `super::list::register` (a `#[thread_local] static DTORS: RefCell<Vec<...>>` drained via `Vec::pop` in a LIFO loop).
  - Crucially, **both** `eager::destroy` (`eager.rs:70-72`) and `lazy::destroy` (`lazy.rs:116-121`) overwrite `state` to `State::Destroyed` **before** calling `ptr::drop_in_place` / `assume_init_drop` inside `abort_on_dtor_unwind`.
  - `s5_tls_multithread_and_lifo_drop_order` empirically verifies all four destructor invariants:
    - Thread A (init `T1` -> `T2` -> `T3`, where `T3::drop` calls `TLS_EAGER_DROP.try_with` and `T1::drop` initializes `TLS_LATE_LAZY`) prints: `events_a = ["drop:T3", "reentrant_t3_ok:false", "drop:T2", "drop:T1", "drop:T_LATE"]`.
    - Thread B (init `T3` -> `T1` -> `T2`) prints: `events_b = ["drop:T2", "drop:T1", "drop:T3", "reentrant_t3_ok:false"]` — LIFO order strictly follows dynamic per-thread first-access order, not declaration order.
    - Re-entrant `TLS_EAGER_DROP.try_with(...)` inside `T3`'s destructor cleanly returns `Err(AccessError)` (`reentrant_t3_ok:false`) rather than observing partially dropped state.
    - Thread C (touching only `TLS_CONST_NODROP`) never registers any destructor (`events_unused = []`).

### 4. Linker-Retained Section Initializers (`#[used]`, `SHF_GNU_RETAIN`, `.init_array`, and `.rlib` Boundaries)

Basis: source (`rust-lang/rust` + `llvm/llvm-project`) + execution (`s4_used_compiler_vs_linker_and_init_array`)

#### 4.1 Resolution of `#[used]`, `#[used(compiler)]`, and `#[used(linker)]` (Plus Documentation Drift Note)

`compiler/rustc_codegen_ssa/src/codegen_attrs.rs:170-186` parses `AttributeKind::Used` into `CodegenFnAttrFlags` (`compiler/rustc_middle/src/middle/codegen_fn_attrs.rs:157-214`):
- `UsedBy::Compiler` -> `CodegenFnAttrFlags::USED_COMPILER` (`1 << 6`)
- `UsedBy::Linker` -> `CodegenFnAttrFlags::USED_LINKER` (`1 << 7`)
- `UsedBy::Default` (bare `#[used]`) -> `if target.os == Os::Illumos { USED_COMPILER } else { USED_LINKER }`.

**Primary-Source Discrepancy Preserved:** A stale comment inside `compiler/rustc_codegen_llvm/src/consts.rs:515-528` discusses bare `#[used]` as though target-specific defaults or historical `USED_COMPILER` distinction still caused `#[used]` to differ from `#[used(linker)]` on some paths. Direct inspection of `codegen_attrs.rs:173-185` and live `--emit=llvm-ir` output from `s4` confirm that on `x86_64-unknown-linux-gnu`, bare `#[used]` assigns `USED_LINKER` (`0x80`), emitting `@USED_BARE` inside `@llvm.used` alongside `USED_LINK` and `INIT_ARRAY_CTOR`:
- `@llvm.used = appending global [3 x ptr] [ptr @INIT_ARRAY_CTOR, ptr @USED_BARE, ptr @USED_LINK], section "llvm.metadata"`
- `@llvm.compiler.used = appending global [1 x ptr] [ptr @USED_COMP], section "llvm.metadata"`
- `PLAIN_UNUSED` (`#[link_section = ".custom_plain"]`, no `#[used]`) is eliminated before LLVM IR codegen completes.

#### 4.2 ELF `SHF_GNU_RETAIN`, `--gc-sections`, `.init_array`, and `.rlib` Extraction

`llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp:729-733, 925-928` checks whether a global appears in `@llvm.used` (`Used.count(GO)`) on binutils >= 2.36 or integrated assembler targets and emits `ELF::SHF_GNU_RETAIN` (`'R'` section flag). In `lld/ELF/MarkLive.cpp:226-243, 382-436`, LLD treats any section carrying `SHF_GNU_RETAIN` (`L383-385`) and any `SHT_INIT_ARRAY` / `SHT_FINI_ARRAY` / `SHT_PREINIT_ARRAY` / `.init_array*` (`L226-243, 422`) as unconditional GC roots.

Live `s4` inspection across object emission, `rust-lld -Wl,--gc-sections`, and `GNU ld 2.47 -Wl,--gc-sections` confirms identical linker behavior:

| `s4` Item | Attributes | `.o` Section & Flags (`readelf -SW`) | `rust-lld` `--gc-sections` Retained? | `GNU ld` `--gc-sections` Retained? |
|---|---|---|---|---|
| `PLAIN_UNUSED` | `#[link_section = ".custom_plain"]` | Absent (dropped pre-`.o`) | `false` | `false` |
| `USED_COMP` | `#[used(compiler)]` + `.custom_comp` | `.custom_comp` (`PROGBITS`, `A`, no `R`) | `false` | `false` |
| `USED_LINK` | `#[used(linker)]` + `.custom_link` | `.custom_link` (`PROGBITS`, **`AR`**) | `true` | `true` |
| `USED_BARE` | `#[used]` + `.custom_bare` | `.custom_bare` (`PROGBITS`, **`AR`**) | `true` | `true` |
| `INIT_ARRAY_CTOR` | `#[used(linker)]` + `.init_array` | `.init_array` (`INIT_ARRAY`, **`WAR`**) | `true` (`24B` `WAo`) | `true` (`24B` `WAo`) |

Executing the linked binary under both linkers produces `CTOR_OBSERVED=0xc070000000000001` (`exec_rc = 0`), proving `.init_array` executes `pre_main_ctor` before `main`.

**Archive Boundary Counterexample (`rlib_member_extraction_boundary` in `s4`):** When `INIT_ARRAY_CTOR` (`dep_ctor`) lives inside an external `.rlib` crate linked as an archive, linking a crate whose `extern crate` reference pulls zero symbols from that `.rlib` produces `unreferenced_rlib_contains_DEP_INIT = false`: ELF static archive resolution extracts an object member only to satisfy an unresolved symbol dependency, so `SHF_GNU_RETAIN` and `SHT_INIT_ARRAY` protect sections *only within object files already loaded into the link*. Once any symbol in that object member is referenced, `dep_ctor` links and runs (`DEP_FLAG=0x77`, `referenced_rlib_exec_rc = 0`).

### 5. Verification Boundary in Anneal (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)

Basis: source (`joshlf/anneal`) + derived

Direct inspection of `trusted/lean/Trusted/MirAst.lean` (`L470-620`) and `trusted/audit/TrustedBoundary.lean` (`L1-220`) establishes that Anneal currently enforces a strict fail-closed trust boundary around promoted rvalues, global pointers, and TLS:
- `ConstLit` (`MirAst.lean:504-506`) defines solely `| scalar (bits : BitVec 128) | zeroSized`; indirect allocations, string/byte slices, and pointer-bearing constants (`GlobalAlloc::Memory`) cannot serialize into `ConstLit`.
- `Operand` (`MirAst.lean:557-560`) and `Rvalue` (`MirAst.lean:580-620`) explicitly reject `Operand::RuntimeChecks`, `Rvalue::Repeat`, `Rvalue::ThreadLocalRef`, casts, and non-tuple aggregates by lowering them to `.unsupported`.
- Consequently, any Anneal MIR extension seeking to model `&'static T` promoted references or `#[thread_local]` statics must carry forward the three proved invariants of Sections 1–3: (a) promoted references map to read-only `.rodata` memory backed by pure `NeedsDrop`-free, `UnsafeCell`-free (except ZST `&mut [T; 0]`) CTFE values whose loads always agree with fresh rvalue evaluation; (b) `Static(Not)` values in `.rodata` and post-relocation `.data.rel.ro` are strictly immutable over every execution step; and (c) each OS thread observes a private `.tdata ++ zeros(.tbss)` slice decoupled from writes on distinct `ThreadId`s and marked `.destroyed` before any destructor body runs.

### 6. Kernel-Checked Lean 4 Formalization (`StaticsPromotedsAndTlsSoundness.lean`)

Basis: derived + execution (`check_lean.py` with `Lean v4.34.1`)

`support/StaticsPromotedsAndTlsSoundness.lean` (`1,311` lines, SHA-256 `7020a5d5433fb68ea8ecfbee994a3e5b07ff4091049c56501a434db4ef552614`) formalizes section classification (`GlobalKind`, `ElfSection`, `PtGNU_Relro`), promotion safety (`canPromoteRef`, `promoExprWellFormed`, `ctfeEvalPromo`, `evalPromotedCalls`, `evalUnpromotedCalls`), per-thread `PT_TLS` template instantiation (`PtTlsTemplate`, `instantiateTlsBlock`), 4 ELF TLS access model semantics (`elfTlsAccessAddr`), LIFO TLS destructor draining (`drainDtorsStepwise`, `DtorSlotState.destroyed` set before callback execution), and linker `--gc-sections` reachability (`linkGcSections`, `runExecOrder`). To guarantee pure structural recursion free of Lean 4 equation-compiler partial helpers, all bounded evaluations and list traversals use `Nat.repeat`, `List.foldr`, and `List.foldl`, yielding `0` `._unsafe_rec` helpers and `0` `is_partial` definitions.

| Theorem (`StaticsPromotedsAndTlsSoundness.*`) | Property Established | Kernel Axioms Reported |
|---|---|---|
| `zero_freeze_static_lands_in_rodata_not_bss` | All-zero `Freeze` immutable non-TLS static maps to `.rodata`, not `.bss` | `[]` (none) |
| `zero_freeze_tls_lands_in_tdata_not_tbss` | All-zero `Freeze` immutable TLS static maps to `.tdata`, not `.tbss` | `[]` (none) |
| `pointer_bearing_freeze_static_lands_in_data_rel_ro_under_pic` | Pointer-bearing `Freeze` static maps to `.data.rel.ro` under PIC and `.rodata` under `staticModel` | `[]` (none) |
| `relro_writable_during_reloc_and_frozen_at_runtime` | Dynamic reloc writes succeed during relocation setup and fault after `PT_GNU_RELRO` freeze | `[]` (none) |
| `running_trace_preserves_rodata_and_dataRelRo` | Arbitrary runtime memory trace leaves `.rodata` and post-reloc `.data.rel.ro` values invariant | `[]` (none) |
| `canPromoteRef_implies_ctfe_total` | Accepted promotion (`canPromoteRef = true`) guarantees total CTFE evaluation without panic | `[propext]` |
| `promote_rvalue_observational_equivalence` | Promoted `.rodata` execution equals fresh-slot unpromoted evaluation with zero `Drop`s (`!HasMutInterior`/`&mut [T;0]`, `!NeedsDrop`) | `[propext]` |
| `pt_tls_instantiate_length` | Instantiated thread TLS block length equals `pFilesz + tbssZeroLen` (`p_memsz`) | `[propext]` |
| `pt_tls_tdata_prefix_exact` | Instantiated indices `< pFilesz` match `.tdata` template bytes | `[propext]` |
| `pt_tls_tbss_zero_exact` | Instantiated indices in `[pFilesz, pFilesz + tbssZeroLen)` equal `0` | `[propext]` |
| `elf_tls_four_models_address_equivalent` | `GeneralDynamic`, `LocalDynamic`, `InitialExec`, and `LocalExec` resolve to the identical thread slot offset | `[]` (none) |
| `pt_tls_spawn_fresh_template_sound` | Thread spawn allocates the unmodified `PT_TLS` template independent of prior mutations in other threads | `[propext]` |
| `pt_tls_cross_thread_noninterference` | Traces whose `targetTid` excludes `t` preserve `projectThreadTls s t` identically | `[propext]` |
| `tls_dtor_lifo_order_and_reentrant_access_safety` | Accesses `T1 -> T2 -> T3` run in LIFO order `[3, 2, 1]` and mark slots `.destroyed` before teardown callbacks | `[propext]` |
| `used_linker_shf_gnu_retain_survives_gc_sections` | `SHF_GNU_RETAIN` (`#[used(linker)]`) unreferenced custom section survives `--gc-sections` | `[propext]` |
| `init_array_section_survives_gc_sections` | `SHT_INIT_ARRAY` section survives `--gc-sections` without incoming call-graph edges | `[propext]` |
| `init_array_runs_before_main` | Pre-main `.init_array` entries execute strictly before `main` | `[propext]` |
| `ce1_promoting_unsafecell_into_rodata_unsound` | Counterexample: promoting an `UnsafeCell` into `.rodata` either triggers a write permission fault or leaks state `0 -> 5 -> 10` across calls instead of fresh `[5, 5]` | `[propext]` |
| `ce2_used_compiler_dropped_by_linker_gc` | Counterexample: `#[used(compiler)]` without `SHF_GNU_RETAIN` survives LLVM IR optimization yet is stripped by `ld --gc-sections`, unlike `#[used(linker)]` | `[propext]` |

## Boundaries

- **not examined:**
  - Non-ELF binary containers (`Mach-O`, `COFF/PE`, `WebAssembly`) and non-`x86_64` ELF architectures (`aarch64`, `riscv64`, `armv7`), including target-specific `TLSDESC` instruction sequences or OS-specific constructor section names (`.mod_init_func`, `.CRT$XCU`).
  - `TlsModel::Emulated` targets lacking native `#[thread_local]` hardware registers (`cfg(not(target_thread_local))`).
  - Bare `#[used]` lowering on `Os::Illumos` (observed in `codegen_attrs.rs:176-180` source logic only, not executed on an Illumos host).
  - Cross-module LTO / ThinLTO internalized static constant merging, dynamic `dlopen`/`dlclose` TLS DTV reclamation and `.fini_array` execution, `static mut` unsoundness/aliasing diagnostics, and Miri execution of specimens `s1`–`s5`.

- **known not to apply:**
  - `local-exec` TLS codegen in `-shared` libraries (`cdylib`): empirically rejected by the linker (`cdylib_link_rc: 1`).
  - `#[used(compiler)]` survival across ELF `--gc-sections`: LLVM preserves `@llvm.compiler.used` in the `.o` file without `SHF_GNU_RETAIN` (`flags: A`), after which both `rust-lld` and `GNU ld` strip the section and symbol (`USED_COMP: false`).
  - `.rlib` static archive inclusion purely from `#[used(linker)]` or `.init_array`: an `.rlib` object member containing zero symbol references from the root crate is not extracted into the final link (`unreferenced_rlib_contains_DEP_INIT: false`).
  - Promotion of `UnsafeCell`, `NeedsDrop`, or runtime non-`#[rustc_promotable]` `const fn` expressions, and placement of all-zero `Freeze` immutable statics/TLS into `.bss`/`.tbss`.

- **unsupported:**
  - Implicit `&mut [T; N]` promotion for `N > 0` (`validate_ref` accepts mutable borrows exclusively for zero-length arrays `[T; 0]`).
  - Nested `static` declarations inside `#[thread_local]` statics (`NestedStaticInThreadLocal`, `intern.rs:162-164`) and compile-time scalar pointers targeting TLS statics (`common.rs` `assert!(!is_thread_local_static)`).
  - Lowering of promoted `&'static T` pointer constants, indirect allocations (`GlobalAlloc::Memory`), or `Rvalue::ThreadLocalRef` within `joshlf/anneal` at commit `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`Trusted/MirAst.lean:504-620` returns `.unsupported`).

- **unknown:**
  - Future stabilization dates or semantic changes for `#![feature(thread_local)]` and `#![feature(used_with_arg)]` beyond `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.
  - Whether future `PromoteTemps` changes will close the `validate_candidate` vs `validate_place` asymmetry on direct out-of-bounds static array borrows (`&([1, 2][5])`).

## Evidence

### Upstream Git Sources (`support/pin_receipt.json`: `37/37` files SHA-256 verified)

1. **`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`:**
   - `compiler/rustc_mir_transform/src/promote_consts.rs` (`L37-167`, `L194-705`, `L769-771`, `L993-1091`): `PromoteTemps`, `TempState`, `Validator`, `promotion_safe_blocks`, `should_evaluate_for_promotion_checks`, `promote_candidates`.
   - `compiler/rustc_const_eval/src/interpret/intern.rs` (`L162-240`): `InternKind`, `NestedStaticInThreadLocal`, `intern_const_alloc_recursive`.
   - `compiler/rustc_middle/src/mir/interpret/mod.rs` (`L251-279`): `GlobalAlloc`.
   - `compiler/rustc_middle/src/middle/codegen_fn_attrs.rs` (`L61-112`, `L157-214`): `CodegenFnAttrs`, `CodegenFnAttrFlags::{THREAD_LOCAL, USED_COMPILER, USED_LINKER}`.
   - `compiler/rustc_codegen_ssa/src/mir/constant.rs` (`L1-107`), `operand.rs` (`L150-318`), `rvalue.rs` (`L643-658`): constant lowering and `ThreadLocalShim`.
   - `compiler/rustc_codegen_ssa/src/codegen_attrs.rs` (`L88-290`): `AttributeKind::LinkSection`, `AttributeKind::Used` (Illumos vs ELF default `USED_LINKER`), `AttributeKind::ThreadLocal`.
   - `compiler/rustc_codegen_llvm/src/{consts.rs, common.rs, context.rs, base.rs}` (`consts.rs:29-137, 236-286, 307-539`, `common.rs:269-365`, `context.rs:170-178, 252-266, 632-658, 701-708`, `base.rs:149-210`): LLVM constant globals, `@llvm.used` vs `@llvm.compiler.used`, PIE level emission.
   - `compiler/rustc_session/src/session.rs` (`L736-746`) & `compiler/rustc_target/src/spec/mod.rs` (`L1002-1012, L2404-2406, L2837`): `TlsModel`.
   - `library/std/src/sys/thread_local/{mod.rs, os.rs, native/mod.rs, native/eager.rs, native/lazy.rs, destructors/linux_like.rs, destructors/list.rs, guard/key.rs, key/racy.rs, key/unix.rs}`: native 4-cell TLS matrix, weak `__cxa_thread_atexit_impl`, LIFO destructor list, `State::Destroyed` pre-drop transition, and OS fallback.
2. **`llvm/llvm-project` @ `fc4aad7b5db3fff421df9a9637605b9ca5667881` (`llvmorg-22.1.6`):**
   - `llvm/lib/Target/TargetLoweringObjectFile.cpp` (`L82-99, L248-368`): `isSuitableForBSS`, `getKindForGlobal` (`.rodata` vs `.data.rel.ro`).
   - `llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp` (`L616-632, L729-733, L871-955`): ELF section selection and `SHF_GNU_RETAIN` flag emission for `@llvm.used`.
   - `llvm/lib/Target/TargetMachine.cpp` (`L185-287`): `getTLSModel` (`PIE` upgrades to `InitialExec`).
   - `lld/ELF/MarkLive.cpp` (`L226-243, L382-436`): `SHT_INIT_ARRAY` and `SHF_GNU_RETAIN` GC roots.
3. **`rust-lang/reference` @ `ad35aca481751a06afeb23820a672b0f3b11a476`:**
   - `src/items/{static-items,constant-items}.md`, `src/destructors.md`, `src/const_eval.md`.
4. **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`:**
   - `trusted/lean/Trusted/MirAst.lean` (`L470-620`), `trusted/lean/Trusted/MirSemantics.lean`, `trusted/audit/TrustedBoundary.lean`.
5. **`leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):**
   - `src/Init/Prelude.lean`.

### Support Artifacts (`support/`)

- `support/specimens/{s1_promote_consts_mir,s2_global_alloc_and_elf_sections,s3_tls_models_x86_64,s4_used_compiler_vs_linker_and_init_array,s5_tls_multithread_and_lifo_drop_order}.rs`: Self-contained Rust test specimens covering all five empirical suites.
- `support/probe_statics_promoteds_and_tls.py` & `support/probe_output/probe_results.json`: Reproducible probe harness and sanitized structured results recorded on `2026-11-21`.
- `support/StaticsPromotedsAndTlsSoundness.lean`, `support/check_lean.py`, & `support/lean_check_receipt.json`: Kernel-checked Lean `v4.34.1` formalization (`1,311` lines, `845` namespace constants, `0` banned source tokens, `0` unsafe/partial/`_unsafe_rec` definitions, `3.9478s` wall clock, `527368` KiB peak RSS, all `19` theorems verified cleanly against `[]` or `[propext]`).
- `support/verify_pins.py` & `support/pin_receipt.json`: Commit & byte-level SHA-256 verification receipt across all `37/37` inspected source files.

## Revalidation

To revalidate the entire package from the package directory inside a checked-out corpus tree:

1. **Re-verify all 37 pinned upstream source files:**
   ```bash
   python3 support/verify_pins.py
   ```
   Confirms byte length and SHA-256 continuity against `support/pin_receipt.json` (`37/37`).

2. **Re-run the live `rustc` / `LLVM` / `readelf` / `objdump` / `rust-lld` / `GNU ld` empirical suite:**
   ```bash
   python3 support/probe_statics_promoteds_and_tls.py
   ```
   Compiles `support/specimens/s1..s5` in a temporary scratch directory, captures fresh MIR dumps (`-Z dump-mir=PromoteTemps`), LLVM IR (`--emit=llvm-ir`), ELF sections/segments/relocations across all 4 `-Z tls-model` values, `GNU ld` vs `rust-lld` `--gc-sections` retention, `.rlib` member behavior, `SIGSEGV` protection faults, and multi-thread LIFO destructor ordering, refreshing `support/probe_output/probe_results.json`.

3. **Re-check the Lean 4 mechanization (`Lean v4.34.1`):**
   ```bash
   python3 support/check_lean.py
   ```
   Runs `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` plus kernel environment inspection (`isUnsafe`, `isPartial`, `._unsafe_rec`, user axioms, `#print axioms`) and updates `support/lean_check_receipt.json`.

4. **Re-validate corpus metadata and formatting from the corpus root:**
   ```bash
   python3 tools/reference.py catalog && python3 tools/reference.py check
   ```

When auditing newer upstream `rustc` commits, the narrowest discriminating diff checks are:
- `compiler/rustc_mir_transform/src/promote_consts.rs` (`validate_candidate`, `validate_place`, `validate_ref`, `promotion_safe_blocks`) for promotion rule shifts;
- `compiler/rustc_codegen_ssa/src/codegen_attrs.rs` (`AttributeKind::Used`) and `compiler/rustc_codegen_llvm/src/consts.rs` for `#[used]` / `#[thread_local]` attribute lowering;
- `library/std/src/sys/thread_local/{native/mod.rs, native/eager.rs, native/lazy.rs, destructors/linux_like.rs}` for destructor ordering and `State::Destroyed` guarantees.
