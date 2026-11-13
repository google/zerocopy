# Rust 1.99.1 Repository Map, IR Inventory, and Internal Interfaces

## Summary

At the Rust `1.99.1` release (`58cf8f9c35b355199727627d07ae34a4e2846d67`, paired
with `rust-lang/llvm-project` `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, LLVM
`23.1.1`), the `compiler/` directory comprises **78 top-level crates** (`83`
`Cargo.toml` manifests including nested workspace subcrates inside
`rustc_codegen_cranelift` and `rustc_codegen_gcc`) totaling **869,824 raw lines**
(**659,410** non-blank, non-comment source lines) plus `4,056` raw lines of C++
in `compiler/rustc_llvm/llvm-wrapper/`. The standard library under `library/`
totals approximately `1,078,000` raw lines (`765,839` SLOC), of which
`library/stdarch` (`core::arch`) accounts for `523,604` raw lines and **8,387**
`link_name = "llvm.*"` intrinsic bindings, and `library/core` declares **316**
`#[rustc_intrinsic]` functions. By contrast, LLVM's `llvm/lib` and
`llvm/include` total **2,443,836 SLOC** (`~3,460,000` raw lines) plus `679,541`
raw lines of TableGen (`.td`) descriptions—roughly `3.7x` the SLOC of the entire
Rust compiler frontend, middle-end, and three codegen backends combined.

All compilation stages after parsing communicate through the on-demand query
system (`compiler/rustc_middle/src/queries.rs`, **326** queries) over a single
arena-interned context (`TyCtxt<'tcx>`). The compiler's five internal
representations—AST, HIR, THIR, MIR (`MirPhase::Built` through
`MirPhase::Runtime(RuntimePhase::Optimized)`), and the backend trait layer
(`rustc_codegen_ssa::traits`, **281** methods across 20 traits)—form explicit
architectural boundaries that determine which components a verified compiler or
certifying backend can reuse, replace, or check.

## Applicability

The measurements, enum variant counts, query inventories, and file-line
coordinates in this report apply directly to `rust-lang/rust` release `1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`) and its pinned `src/llvm-project`
submodule (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, LLVM `23.1.1`), as well
as `rust-lang/rust` `1.100.0` (`0ef1bc386059596dada8fb65b50425aab2ea637a`) where
noted.

Where earlier informal surveys of unmerged developer branches (such as
`transmute-cleanup` at `49d734536222bf28bb6d07d885b3a81d145981da`) reported 80
top-level compiler crates (`rustc_expand_queries` and `rustc_structures`), 9
`ProjectionElem` variants (`PhantomDeref`), or `ItemKind::TestBinderConstraints`,
this report establishes the exact upstream `1.99.1` baseline definitions and
isolates branch-only divergences.

## Findings

### 1. Repository Scale by Subsystem

`Basis: source + execution (support/measure_rustc_baseline_map.py)`

| Subsystem | Path | Tracked Source Files | Raw Lines | Approx. SLOC | Structural Role |
| :--- | :--- | ---: | ---: | ---: | :--- |
| Compiler crates (78 top-level) | `compiler/` | 2,523 | 869,824 | 659,410 | Lexing, parsing, expansion, type/borrow checking, MIR passes, and LLVM/CLIF/GCC backends |
| LLVM C++ wrapper | `compiler/rustc_llvm/llvm-wrapper/` | 8 | 4,056 | 3,147 | C++ shim around LLVM C++ APIs not exposed by LLVM-C |
| Standard library | `library/` | 1,685 | 1,078,112 | 765,839 | `core`, `alloc`, `std`, `proc_macro`, `test`, `stdarch`, `compiler-builtins`, `portable-simd` |
| LLVM core (`lib/` + `include/`) | `src/llvm-project/llvm/` | 6,395 | ~3,460,000 | 2,443,836 | Target-independent IR, analysis, transforms, SelectionDAG/GlobalISel, MC, and 19 target backends |
| LLVM TableGen definitions | `src/llvm-project/llvm/` (`*.td`) | 612 | 679,541 | — | Instruction, register, calling-convention, and scheduling descriptions |
| `lld` linker | `src/llvm-project/lld/` | 384 | 107,656 | — | ELF, Mach-O, COFF, and WebAssembly linkers shipped as `rust-lld` |
| In-tree tools | `src/tools/` | 3,412 | 1,151,389 | — | `rust-analyzer` (585,990 raw), `clippy` (295,112), `miri` (64,619 in `src/`), `rustfmt` (98,845), `compiletest` (15,204), `tidy` (7,812) |
| Documentation generator | `src/librustdoc/` | 103 | 49,392 | 40,179 | `rustdoc` HTML/JSON documentation generator |
| Bootstrap build system | `src/bootstrap/` | 82 | 46,067 | 34,814 | Staged compiler/library/LLVM build orchestrator (`x.py`) |
| Compiler test suites | `tests/` | 43,512 | — | — | `tests/ui` (35,794 files; 21,275 `.rs`), `mir-opt` (1,698), `run-make` (1,630), `codegen-llvm` (862) |

### 2. Compiler Crate Graph and Pipeline Stages

`Basis: source (compiler/*/Cargo.toml)`

The 78 top-level crates in `compiler/` form a directed acyclic dependency graph
whose longest chain spans **22 crate hops**:

```text
rustc-main -> rustc_driver -> rustc_driver_impl -> rustc_interface ->
rustc_codegen_llvm -> rustc_codegen_ssa -> rustc_monomorphize ->
rustc_mir_transform -> rustc_mir_build -> rustc_pattern_analysis ->
rustc_lint -> rustc_trait_selection -> rustc_infer -> rustc_middle ->
rustc_abi -> rustc_target -> rustc_feature -> rustc_Version / rustc_span ->
rustc_data_structures -> rustc_index -> rustc_serialize
```

The most depended-upon crates across the 78 compiler crates are:
1. `rustc_span` (54 internal dependents; `12,118` raw lines)
2. `rustc_data_structures` (50 dependents; `14,792` raw lines)
3. `rustc_macros` (48 dependents; `4,598` raw lines)
4. `rustc_hir` (33 dependents; `8,214` raw lines), `rustc_errors` (33 dependents; `7,310` raw lines), and `rustc_abi` (33 dependents; `6,195` raw lines)
5. `rustc_middle` (32 dependents; `66,684` raw lines) and `rustc_index` (32 dependents; `4,098` raw lines)
6. `rustc_ast` (31 dependents; `12,088` raw lines) and `rustc_session` (30 dependents; `11,984` raw lines)

| Pipeline Stage | Crates and Raw Line Counts at `1.99.1` | Primary Output / Role |
| :--- | :--- | :--- |
| Driver & session setup | `rustc-main` (87), `rustc_driver` (33), `rustc_driver_impl` (2,698), `rustc_interface` (4,295), `rustc_session` (11,984) | `Session`, `TyCtxt<'tcx>`, `Callbacks` |
| Lexing & parsing | `rustc_lexer` (1,692), `rustc_parse` (32,784), `rustc_parse_format` (1,598), `rustc_ast` (12,088), `rustc_ast_ir` (512), `rustc_ast_pretty` (3,812) | Parsed `rustc_ast::ast::Crate` |
| Attribute & macro expansion | `rustc_attr_parsing` (16,095), `rustc_attr_ir` (4,288), `rustc_expand` (13,690), `rustc_builtin_macros` (15,188) | Expanded AST + proc-macro execution |
| Name resolution & AST lowering | `rustc_resolve` (29,280), `rustc_ast_passes` (4,290), `rustc_ast_lowering` (14,385), `rustc_hir` (8,214), `rustc_hir_id` (410), `rustc_hir_pretty` (2,190) | `rustc_hir::hir` indexed by `DefId`/`HirId` |
| Type & trait analysis | `rustc_hir_analysis` (40,390), `rustc_hir_typeck` (49,580), `rustc_infer` (13,290), `rustc_trait_selection` (50,790), `rustc_next_trait_solver` (12,195), `rustc_type_ir` (19,180), `rustc_type_ir_macros` (620), `rustc_traits` (710) | `TypeckResults<'tcx>`, trait selections, normalized types |
| Semantic checks & layout | `rustc_privacy` (1,995), `rustc_passes` (9,190), `rustc_lint` (25,790), `rustc_lint_defs` (3,890), `rustc_pattern_analysis` (5,990), `rustc_ty_utils` (5,395), `rustc_transmute` (3,095) | Exhaustiveness, `TyAndLayout<'tcx>`, `FnAbi<'tcx, Ty<'tcx>>` |
| THIR & MIR construction | `rustc_mir_build` (23,090) | `Steal<Thir<'tcx>>`, `mir_built` (`MirPhase::Built`) |
| Borrow checking & dataflow | `rustc_borrowck` (36,085), `rustc_mir_dataflow` (7,095) | Region inference, move/init checking |
| MIR transformations | `rustc_mir_transform` (35,090) | `mir_promoted`, `mir_drops_elaborated_and_const_checked`, `mir_for_ctfe`, `optimized_mir` |
| Compile-time evaluation | `rustc_const_eval` (22,690) | `ConstValue`, `Allocation`, Miri/CTFE `Machine<'tcx>` |
| Monomorphization & mangling | `rustc_monomorphize` (4,895), `rustc_symbol_mangling` (2,295), `rustc_sanitizers` (1,995) | `MonoItem<'tcx>` graph, `CodegenUnit<'tcx>` partitions |
| Backend-agnostic codegen | `rustc_codegen_ssa` (30,395) | MIR-to-SSA lowering over `BuilderMethods`, archive/linker orchestration |
| Codegen backends | `rustc_codegen_llvm` (31,090), `rustc_llvm` (4,856 Rust+C++), `rustc_codegen_cranelift` (23,590), `rustc_codegen_gcc` (34,090) | Object files, bitcode, LTO, executables |
| Metadata & incremental | `rustc_metadata` (11,695), `rustc_incremental` (2,795), `rustc_query_impl` (2,595) | `.rmeta`, `.rlib`, dependency graph, query cache |
| Public MIR interface | `rustc_public` (11,195), `rustc_public_bridge` (1,495) | External tool callback API (`rustc_public::run!`) |

### 3. Internal Representations and Exact Core Enum Sizes

`Basis: source + execution (support/baseline_map_metrics.json)`

Every IR stage narrows or elaborates surface constructs into explicit semantics:

| IR Layer | Enum Name | Source Location (`58cf8f9c35b355199727627d07ae34a4e2846d67`) | Variant Count | Key Variants / Notes |
| :--- | :--- | :--- | ---: | :--- |
| AST | `ast::ExprKind` | `compiler/rustc_ast/src/ast.rs:1746-1928` | 50 | Surface expressions including macros, `try`, `yeet`, `become`, `FormatArgs` |
| AST | `ast::ItemKind` | `compiler/rustc_ast/src/ast.rs:4122-4201` | 20 | `ExternCrate`, `Use`, `Static`, `Const`, `Fn`, `Mod`, `ForeignMod`, `GlobalAsm`, `TyAlias`, `Enum`, `Struct`, `Union`, `Trait`, `TraitAlias`, `Impl`, `MacCall`, `MacroDef`, `Delegation`, `DelegationMac` |
| AST | `ast::PatKind` | `compiler/rustc_ast/src/ast.rs:872-950` | 20 | Includes `Box`, `Deref`, `Guard`, `Never`, `Err` |
| AST | `ast::TyKind` | `compiler/rustc_ast/src/ast.rs:2510-2573` | 23 | Surface syntax types including `ImplTrait`, `TraitObject`, `UnsafeBinder` |
| HIR | `hir::ExprKind` | `compiler/rustc_hir/src/hir.rs:2571-2707` | 35 | Desugared loops (`Loop`), `Match`, `Closure`, `Yield`, `Become`, `InlineAsm`, `OffsetOf`, `UnsafeBinderCast` |
| HIR | `hir::ItemKind` | `compiler/rustc_hir/src/hir.rs:4470-4538` | 16 | Macro calls eliminated; items indexed by `OwnerId` |
| HIR | `hir::PatKind` | `compiler/rustc_hir/src/hir.rs:1755-1826` | 16 | `Missing`, `Wild`, `Binding`, `Struct`, `TupleStruct`, `Or`, `Path`, `Tuple`, `Box`, `Deref`, `Ref`, `Expr`, `Range`, `Slice`, `Never`, `Guard`, `Err` |
| HIR | `hir::TyKind` | `compiler/rustc_hir/src/hir.rs:3568-3618` | 18 | Lowered type syntax prior to `TyCtxt` interning |
| THIR | `thir::ExprKind` | `compiler/rustc_middle/src/thir.rs:268-566` | 51 | Explicit coercions, auto-deref, overloaded operators, `Scope`, `Deref`, `LogicalOp`, `Use` |
| THIR | `thir::PatKind` | `compiler/rustc_middle/src/thir.rs:764-882` | 15 | Typed patterns consumed by exhaustiveness and MIR match builder |
| THIR | `thir::StmtKind` | `compiler/rustc_middle/src/thir.rs:207-244` | 2 | `Let`, `Expr` |
| MIR | `mir::MirPhase` | `compiler/rustc_middle/src/mir/syntax.rs:152-160` | 3 | `Built`, `Analysis(AnalysisPhase)`, `Runtime(RuntimePhase)` |
| MIR | `mir::AnalysisPhase` | `compiler/rustc_middle/src/mir/syntax.rs:163-166` | 2 | `Initial`, `PostCleanup` |
| MIR | `mir::RuntimePhase` | `compiler/rustc_middle/src/mir/syntax.rs:169-173` | 3 | `Initial`, `PostCleanup`, `Optimized` |
| MIR | `mir::StatementKind` | `compiler/rustc_middle/src/mir/syntax.rs:305-456` | 13 | `Assign`, `FakeRead`, `SetDiscriminant`, `StorageLive`, `StorageDead`, `Retag`, `PlaceMention`, `AscribeUserType`, `Coverage`, `Intrinsic`, `ConstEvalCounter`, `Nop`, `BackwardIncompatibleDropHint` |
| MIR | `mir::NonDivergingIntrinsic` | `compiler/rustc_middle/src/mir/syntax.rs:460-483` | 2 | `Assume`, `CopyNonOverlapping` |
| MIR | `mir::TerminatorKind` | `compiler/rustc_middle/src/mir/syntax.rs:683-968` | 15 | `Goto`, `SwitchInt`, `UnwindResume`, `UnwindTerminate`, `Return`, `Unreachable`, `Drop`, `Call`, `TailCall`, `Assert`, `Yield`, `CoroutineDrop`, `FalseEdge`, `FalseUnwind`, `InlineAsm` |
| MIR | `mir::Rvalue` | `compiler/rustc_middle/src/mir/syntax.rs:1342-1467` | 13 | `Use`, `Repeat`, `Ref`, `ThreadLocalRef`, `RawPtr`, `Cast`, `BinaryOp`, `NullaryOp`, `UnaryOp`, `Discriminant`, `Aggregate`, `CopyForDeref`, `WrapUnsafeBinder` |
| MIR | `mir::Operand` | `compiler/rustc_middle/src/mir/syntax.rs:1282-1314` | 4 | `Copy`, `Move`, `Constant`, `RuntimeChecks` |
| MIR | `mir::ProjectionElem` | `compiler/rustc_middle/src/mir/syntax.rs:1171-1258` | 8 | `Deref`, `Field`, `Index`, `ConstantIndex`, `Subslice`, `Downcast`, `OpaqueCast`, `UnwrapUnsafeBinder` |
| MIR | `mir::CastKind` | `compiler/rustc_middle/src/mir/syntax.rs:1470-1519` | 12 | `PointerExposeProvenance`, `PointerWithExposedProvenance`, `PointerCoercion`, `IntToInt`, `FloatToInt`, `FloatToFloat`, `IntToFloat`, `PtrToPtr`, `FnPtrToPtr`, `Transmute`, `Subtype` |
| MIR | `mir::BinOp` | `compiler/rustc_middle/src/mir/syntax.rs:1608-1698` | 26 | Arithmetic, overflowing (`*WithOverflow`), unchecked (`*Unchecked`), bitwise, `Cmp`, `Offset` |
| MIR | `mir::UnOp` | `compiler/rustc_middle/src/mir/syntax.rs:1590-1604` | 3 | `Not`, `Neg`, `PtrMetadata` |
| MIR | `mir::AggregateKind` | `compiler/rustc_middle/src/mir/syntax.rs:1533-1563` | 7 | `Array`, `Tuple`, `Adt`, `Closure`, `Coroutine`, `CoroutineClosure`, `RawPtr` |
| Types | `ty::TyKind` | `compiler/rustc_type_ir/src/ty_kind.rs:147-347` | 29 | `Bool`, `Char`, `Int`, `Uint`, `Float`, `Adt`, `Foreign`, `Str`, `Array`, `Pat`, `Slice`, `RawPtr`, `Ref`, `FnDef`, `FnPtr`, `UnsafeBinder`, `Dynamic`, `Closure`, `CoroutineClosure`, `Coroutine`, `CoroutineWitness`, `Never`, `Tuple`, `Alias`, `Param`, `Bound`, `Placeholder`, `Infer`, `Error` |
| Mono | `ty::InstanceKind` | `compiler/rustc_middle/src/ty/instance.rs:62-96` | 5 | `Item`, `Intrinsic`, `LlvmIntrinsic`, `Virtual`, `Shim` |
| Mono | `ty::ShimKind` | `compiler/rustc_middle/src/ty/instance.rs:100-198` | 12 | `VTable`, `Reify`, `FnPtr`, `ClosureOnce`, `ConstructCoroutineInClosure`, `ThreadLocal`, `FutureDropPoll`, `DropGlue`, `Clone`, `FnPtrAddr`, `AsyncDropGlueCtor`, `AsyncDropGlue` |

### 4. Query System and Codegen-Consumed Queries

`Basis: source (compiler/rustc_middle/src/queries.rs:1-2940)`

`compiler/rustc_middle/src/queries.rs` declares **326 queries**. Codegen
(`rustc_monomorphize`, `rustc_codegen_ssa`, and `rustc_codegen_llvm`) does not
touch AST, HIR, or THIR queries directly; instead it consumes a bounded slice of
middle-end queries:
- **Monomorphization and partitioning:** `collect_and_partition_mono_items`,
  `symbol_name`, `codegen_fn_attrs`, `codegen_instance_attrs`, `is_mir_available`,
  `cross_crate_inlinable`, `exported_generic_symbols`, `exported_non_generic_symbols`,
  `reachable_non_generics`.
- **Function bodies and shims:** `instance_mir` (which dispatches to
  `optimized_mir` for `InstanceKind::Item`, `mir_for_ctfe` for constructors and
  constants, and `mir_shims` for `InstanceKind::Shim`), `promoted_mir`.
- **Types, layouts, and ABIs:** `type_of`, `layout_of`, `fn_abi_of_instance`,
  `fn_abi_of_fn_ptr`, `vtable_entries`, `vtable_allocation`,
  `instantiate_and_normalize_erasing_regions`.
- **Constants and statics:** `eval_to_const_value_raw`, `eval_to_allocation_raw`,
  `eval_static_initializer`, `global_alloc`.

### 5. Codegen Trait Surface and Backend-to-Frontend Feedback

`Basis: source (compiler/rustc_codegen_ssa/src/traits/*.rs, compiler/rustc_interface/src/interface.rs:440-475)`

`rustc_codegen_ssa::traits` defines **20 traits** with **281 methods** in total:

| Trait | Source File | Method Count | Responsibility |
| :--- | :--- | ---: | :--- |
| `BuilderMethods` | `traits/builder.rs` | 139 | Basic block instruction emission (arithmetic, memory, atomics, calls, landing pads, intrinsics) |
| `ConstCodegenMethods` | `traits/consts.rs` | 25 | Scalar, array, struct, undef/poison, and global constant materialization |
| `CodegenBackend` | `traits/backend.rs` | 21 | Backend lifecycle (`init`, `target_config`, `codegen_crate`, `join_codegen`, `link`) |
| `BaseTypeCodegenMethods` | `traits/type_.rs` | 20 | Primitive, array, pointer, function, and struct backend types |
| `DebugInfoBuilderMethods` | `traits/debuginfo.rs` | 13 | Variable, scope, and source-location debuginfo records |
| `MiscCodegenMethods` | `traits/misc.rs` | 10 | Vtables, `get_fn`, `get_fn_addr`, compiler-used globals, frame pointers |
| `IntrinsicCallBuilderMethods` | `traits/intrinsic.rs` | 9 | Target-independent intrinsic call lowering and `llvm.*` intrinsic dispatch |
| `WriteBackendMethods` | `traits/write.rs` | 9 | Per-CGU optimization, fat/thin LTO, object/bitcode emission |
| `LayoutTypeCodegenMethods` | `traits/type_.rs` | 8 | Mapping `TyAndLayout` to immediate, scalar-pair, and memory backend types |
| `CoverageInfoBuilderMethods` | `traits/coverageinfo.rs` | 6 | Coverage counter and region mapping emission |
| `DebugInfoCodegenMethods` | `traits/debuginfo.rs` | 6 | Module-level debuginfo context initialization and finalization |
| `StaticCodegenMethods` | `traits/statics.rs` | 4 | Static address resolution and section/thread-local codegen |
| `AbiBuilderMethods` | `traits/abi.rs` | 3 | Prologue argument extraction (`get_param`) |
| `AsmBuilderMethods` | `traits/asm.rs` | 2 | Inline assembly (`codegen_inline_asm`) |
| `AsmCodegenMethods` | `traits/asm.rs` | 2 | Module-level `global_asm!` emission |
| `StaticBuilderMethods` | `traits/statics.rs` | 1 | `get_static` inside a function builder |
| `ArgTypeMethods`, `DerivedTypeCodegenMethods`, `BackendTypes`, `CodegenMethods` | `traits/*.rs` | 3 | Supertrait aggregation and associated type bindings (`Value`, `Function`, `BasicBlock`, `Type`, `Funclet`, `DIScope`, `DILocation`, `DIVariable`) |

Crucially, the backend influences frontend `cfg` evaluation before macro
expansion (`compiler/rustc_interface/src/interface.rs:445-470`):
`CodegenBackend::target_config` returns `TargetConfig`, which populates
`cfg(target_feature = "...")` and `cfg(target_has_reliable_f16 / f128)`, while
`CodegenBackend::init` configures `Session::replaced_intrinsics` and
`Session::fallback_intrinsics`.

### 6. Interface to LLVM and `core::arch` Coupling

`Basis: source (compiler/rustc_llvm/build.rs, compiler/rustc_codegen_llvm/src/llvm/ffi.rs, library/stdarch/)`

1. **Linked LLVM components (`compiler/rustc_llvm/build.rs:11-34`):** `rustc_llvm`
   requires `ipo`, `bitreader`, `bitwriter`, `linker`, `asmparser`, `lto`,
   `coverage`, and `instrumentation`, plus up to 19 target backends (`x86`,
   `aarch64`, `arm`, `riscv`, `wasm`, `powerpc`, `systemz`, `mips`, `loongarch`,
   `sparc`, `hexagon`, `nvptx`, `amdgpu`, `bpf`, `avr`, `msp430`, `m68k`,
   `csky`, `xtensa`).
2. **FFI boundary (`compiler/rustc_codegen_llvm/src/llvm/ffi.rs`):** Declares
   **381 `extern "C"` functions** (**249** upstream `LLVM*` C-API functions and
   **132** `LLVMRust*` functions implemented across 8 files and `4,056` raw C++
   lines in `compiler/rustc_llvm/llvm-wrapper/`).
3. **`core::arch` (`library/stdarch`) LLVM intrinsic coupling:** `stdarch`
   declares **8,387** `#[link_name = "llvm.*"]` external functions with
   `extern "unadjusted"` ABI, which `rustc` lowers via
   `InstanceKind::LlvmIntrinsic`. By architecture prefix: `aarch64` (2,858),
   `hexagon` (1,853), `x86` (1,086), `loongarch` (925), `arm` (633), `mips`
   (530), `s390` (167), `ppc` (107), `wasm` (46), `riscv` (41), and target-generic
   `fma`/`ctlz`/`cttz`/`bswap`/prefetch intrinsics (141). Non-LLVM backends must
   emulate these `llvm.*` names directly.

### 7. Configuration Surface at `1.99.1`

`Basis: source + execution (support/measure_rustc_baseline_map.py)`

- **Built-in target specifications:** **331** targets in
  `compiler/rustc_target/src/spec/mod.rs` (`TargetOptions` has **112** fields;
  `compiler/rustc_target/src/callconv/` has **26** calling-convention modules;
  `InlineAsmArch` has **28** architecture variants).
- **CLI codegen and unstable flags:** `compiler/rustc_session/src/options.rs`
  defines **58** `-C` (`CodegenOptions`) flags and **238** `-Z`
  (`UnstableOptions`) flags.
- **Third-party dependency closure:** `Cargo.lock` contains **669** packages;
  `src/tools/tidy/src/deps.rs` bounds the permitted crates.io transitive closure
  for `rustc`, `std`, and `rustc_codegen_cranelift`.

## Boundaries

- **Submodules not checked out in `s1991` worktree:** Uninitialized tool and
  documentation submodules (`src/tools/cargo`, `src/gcc`, `src/tools/enzyme`,
  `src/tools/rustc-perf`, and book submodules under `src/doc/`) were not line-counted
  from the `s1991` worktree; LLVM counts come from the pinned commit
  `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`.
- **Line-count methodology:** `approx_sloc` in `support/measure_rustc_baseline_map.py`
  excludes blank lines and lines starting with `//`, `/*`, or `*` across tracked
  source files; it is a fast deterministic proxy rather than a full lexer-based
  comment stripper.

## Evidence

- **Script and machine-readable output:**
  - `support/measure_rustc_baseline_map.py`
  - `support/baseline_map_metrics.json`
- **Primary upstream source coordinates (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `compiler/rustc_middle/src/mir/syntax.rs:152-1698` (MIR phases and core enums)
  - `compiler/rustc_type_ir/src/ty_kind.rs:147-347` (`TyKind`)
  - `compiler/rustc_middle/src/ty/instance.rs:62-198` (`InstanceKind`, `ShimKind`)
  - `compiler/rustc_middle/src/queries.rs:1-2940` (326 query declarations)
  - `compiler/rustc_codegen_ssa/src/traits/` (20 traits, 281 methods)
  - `compiler/rustc_codegen_llvm/src/llvm/ffi.rs` (381 FFI functions)
  - `compiler/rustc_llvm/llvm-wrapper/` (4,056 raw lines of C++)

## Revalidation

Run `support/measure_rustc_baseline_map.py` against any `rust-lang/rust` checkout:

```bash
python3 reports/rustc-baseline-repository-map-and-internal-interfaces/support/measure_rustc_baseline_map.py \
  --rust-root /path/to/rust \
  --out /tmp/baseline_map_metrics.json
```

Diff `/tmp/baseline_map_metrics.json` against `support/baseline_map_metrics.json`
to detect any added/removed compiler crates, IR enum variants, queries, codegen
trait methods, or LLVM FFI bindings.
