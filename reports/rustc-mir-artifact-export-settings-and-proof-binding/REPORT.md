# Exporting the MIR Artifact: Per-Function Contents, Exporters, Settings Sensitivity, and Proof Binding

## Summary

To compile a Rust crate to machine code or verify its compilation without
querying a live `TyCtxt<'tcx>` session, an exported MIR artifact must include
not only polymorphic or monomorphic MIR bodies at a fixed phase (`Runtime(PostCleanup)`
or `Runtime(Optimized)`), but also synthesized `InstanceKind::Shim` bodies (`12`
`ShimKind` variants), resolved monomorphic `MonoItem<'tcx>` instances, concrete
`TyAndLayout<'tcx>` records (`Size`, `Align`, `BackendRepr`, `FieldsShape`,
`Variants`), `FnAbi<'tcx, Ty<'tcx>>` calling conventions, `VtblEntry<'tcx>`
layouts, CTFE-evaluated `ConstAllocation<'tcx>` byte buffers with provenance
relocations and initialization masks, mangled symbol names, linkage/visibility,
`CodegenFnAttrs`, target specification parameters, and debuginfo scopes
(`SourceScopeData`, `VarDebugInfo`).

None of the existing exporters at Rust `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`)
serializes this complete standalone backend payload out of the box:
1. `.rmeta` (`compiler/rustc_metadata/src/rmeta/encoder.rs:1101-1131, 1812-1860`)
   omits non-generic, non-inlinable function bodies unless `-Zalways-encode-mir`
   is set, encodes `optimized_mir` (not `Runtime(PostCleanup)`), and never encodes
   synthesized shims, monomorphic `FnAbi`, or `MonoItem` partitions.
2. `rustc_public` (`compiler/rustc_public/src/lib.rs:53-130`) derives
   `serde::Serialize` on its public AST/MIR/ABI types, but its handle types
   (`CrateNum`, `DefId`, `Ty`, `Span`, `AllocId`) serialize only thread-local
   session table indices (`serialize_index_impl!`) that cannot be deserialized
   outside the originating `rustc_public::run!` callback without also dumping the
   interner tables.
3. Anneal's capture driver (`trusted/rustc-capture/src/lib.rs` in `joshlf/anneal`
   @ `7abf0691c404393e3e4fc26eb3d4094e3170b5c7`) captures `Runtime(PostCleanup)`
   bodies (`mir_drops_elaborated_and_const_checked`), layouts, and obligations into
   Lean 4 modules, while `.rlib` archives built by `ArArchiveBuilder`
   (`compiler/rustc_codegen_ssa/src/back/archive.rs:545-580`) tolerate arbitrary
   additional archive members (such as `anneal_artifact.mir.bin`) without
   affecting `rustc_metadata::locator` or downstream linking.

## Applicability

These findings apply to `rust-lang/rust` `1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`) and `joshlf/anneal`
(`7abf0691c404393e3e4fc26eb3d4094e3170b5c7`) on `x86_64-unknown-linux-gnu` and
across all Tier 1 targets for MIR phase selection, `.rmeta`/`.rlib` container
layout, session-hash computation, and proof-to-artifact binding.

## Findings

### 1. Complete Per-Function and Per-Crate Backend Artifact Schema

`Basis: source (compiler/rustc_codegen_ssa/src/mir/mod.rs:51-162, compiler/rustc_middle/src/mono.rs:28-130)`

Inspecting every `TyCtxt<'tcx>` query invoked by `rustc_monomorphize` and
`rustc_codegen_ssa::mir::FunctionCx` establishes the exact closure of data a
standalone backend requires to compile a crate without consulting `rustc`:

| Artifact Component | `rustc` Internal Representation | Why a Standalone Backend Needs It |
| :--- | :--- | :--- |
| Fixed-phase MIR body | `mir::Body<'tcx>` at `Runtime(PostCleanup)` or `Runtime(Optimized)` | Control-flow graph (`BasicBlockData`), `StatementKind` (13 variants), `TerminatorKind` (15 variants), `LocalDecl` list |
| Promoted constant bodies | `IndexVec<Promoted, Body<'tcx>>` (`promoted_mir`) | Borrowed constant temporaries (`rvalue` promotions) referenced by `Operand::Constant` |
| Synthesized shims | `InstanceKind::Shim(ShimKind<'tcx>)` via `mir_shims` (`shim.rs:34-160`) | 12 compiler-generated callable bodies (`DropGlue`, `VTable`, `Reify`, `FnPtr`, `ClosureOnce`, `Clone`, `ThreadLocal`, `FnPtrAddr`, `ConstructCoroutineInClosure`, `FutureDropPoll`, `AsyncDropGlueCtor`, `AsyncDropGlue`) |
| Monomorphized instance set | `MonoItem<'tcx>` + `MonoItemData` (`mono.rs:56-60, 367-377`) | Exact set of functions, statics, and `global_asm!` blocks to emit, with `InstantiationMode` (`GloballyShared` vs `LocalCopy`), `Linkage`, and `Visibility` |
| Type layouts | `TyAndLayout<'tcx>` (`rustc_abi::LayoutData`) | Exact byte `size`, `align` (`abi` and `pref`), `BackendRepr` (`Scalar`, `ScalarPair`, `SimdVector`, `Memory`), `FieldsShape` offsets, and `Variants` (single vs tag/niche encoding) |
| Call ABIs | `FnAbi<'tcx, Ty<'tcx>>` (`rustc_target::callconv::FnAbi`) | Per-argument and return `ArgAbi` (`PassMode::Ignore`, `Direct`, `Pair`, `Cast`, `Indirect`), `ArgAttributes` (`NoAlias`, `NonNull`, `ZExt`, `SExt`, `InReg`, `PointeeSize`), `CanonAbi`, `c_variadic`, `can_unwind` |
| Vtable layouts and allocations | `&'tcx [VtblEntry<'tcx>]` + `AllocId` (`vtable.rs:13-26, 84-155`) | Slot indices for virtual calls (`InstanceKind::Virtual(def_id, idx)`) and global constant allocations for `GlobalAlloc::VTable` |
| Evaluated constants & statics | `GlobalAlloc<'tcx>` + `ConstAllocation<'tcx>` (`allocation.rs:95-117`) | Raw bytes, `InitMask` (distinguishing initialized bytes from `undef` padding), `ProvenanceMap` (`AllocId` + offset relocations to `Function`, `VTable`, `Static`, `Memory`, `TypeId`), `Align`, and `Mutability` |
| Symbol names & codegen attrs | `SymbolName<'tcx>` + `CodegenFnAttrs` (`codegen_fn_attrs.rs`) | Mangled symbol string, `#[link_section]`, `#[used]`, `#[naked]`, `#[cold]`, `#[track_caller]`, `target_features`, `instruction_set`, `alignment`, `no_builtins`, `ffi_pure`/`ffi_const` |
| Target & session parameters | `rustc_target::spec::Target` + codegen options | Data layout string, pointer width, endianness, `trap_unreachable`, `panic_strategy`, `relocation_model`, `code_model`, `tls_model`, `function_sections` |
| Debuginfo & span records | `SourceScopeData`, `VarDebugInfo`, `Span` file/line/col | Mapping `SourceInfo` scopes, inlined call sites (`inlined: Option<(Instance, Span)>`), and local variable fragments (`VarDebugInfoFragment`) to DWARF/CodeView |

### 2. Coverage Comparison of Existing Exporters

`Basis: source (compiler/rustc_public/src/lib.rs, compiler/rustc_metadata/src/rmeta/encoder.rs, joshlf/anneal trusted/rustc-capture/)`

| Exporter | MIR Phase Exported | Includes Non-Generic Private Fns? | Includes Shims & Monomorphic Instances? | Includes Concrete `TyAndLayout` & `FnAbi`? | Wire Format & Standalone Usability |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `.rmeta` (`rustc_metadata`) | `Runtime(Optimized)` + `mir_for_ctfe` (`encoder.rs:1101-1131, 1828-1850`) | Only with `-Zalways-encode-mir=yes`; otherwise only generic or `cross_crate_inlinable` items | No (`mir_shims` and `MonoItem` partitions are recomputed downstream) | No (layouts and `FnAbi` are recomputed via `TyCtxt` queries) | Internal `rustc_serialize` binary table format; tied to exact `rustc` commit |
| `rustc_public` (`StableMIR`) | Configurable (`optimized_mir` or `Instance::body` via `rustc_public_bridge`) | Yes (within `rustc_public::run!` callback) | Yes (`MonoItem::collect` and `Instance::body` cover shims) | Yes (`Ty::layout` and `Instance::fn_abi`) | `serde::Serialize` derived on structs, but `Ty`, `DefId`, `Span`, `AllocId` serialize as session table indices (`serialize_index_impl!`) |
| Charon (`ULLBC` / `LLBC`) | `Runtime(PostCleanup)` (`mir_drops_elaborated_and_const_checked`) | Yes | Partial (translates functions and closures; does not export `FnAbi`, vtable byte allocations, or `global_asm!`) | Partial (type/field layouts without target `PassMode::Cast` ABI lowering) | Versioned JSON (`charon` crate schema) for Aeneas/verification |
| Anneal `rustc-capture` | `Runtime(PostCleanup)` (`mir_drops_elaborated_and_const_checked`) | Yes | Captures local functions and obligations | Captures layouts and type definitions needed for Lean 4 proof obligations | Pure Lean 4 `.lean` AST modules (`.anneal/generated/Mir/`) + `.anneal/spec-lock.json` |
| `--emit=mir` / `-Zdump-mir` | Any pass/phase (`-Zdump-mir=all`) | Yes | Yes (when `make_shim` runs) | No (`FnAbi` and raw `Allocation` init masks are omitted or pretty-printed) | Human-readable text / GraphViz DOT; non-invertible (cannot be parsed back) |

### 3. `.rlib` Archive Structure and Extra Member Tolerance

`Basis: source + execution (compiler/rustc_codegen_ssa/src/back/archive.rs:545-580, compiler/rustc_metadata/src/locator.rs:565-640, support/probe_mir_export_and_settings.py)`

1. **What `rustc` writes into an `.rlib`:** `ArArchiveBuilder` writes:
   - `lib.rmeta`: the crate metadata stub (when `-Zembed-metadata=yes` or stubbed);
   - `<crate_name>.<stable_crate_id>-cgu.<N>.rcgu.o`: one object file per codegen unit (containing machine code and, when `-Cembed-bitcode=yes`, an `.llvmbc` and `.llvmcmd` section);
   - `<crate_name>.allocatorshim.rcgu.o` (when needed).
2. **Archive reader and linker tolerance (`support/mir_settings_and_rlib_probe.json`):**
   - `rustc_metadata::locator` locates metadata by reading `lib.rmeta` (the `METADATA_FILENAME` archive entry) and ignores non-`.o`/non-`lib.rmeta` archive entries.
   - When `ar r liblib_probe.rlib anneal_artifact.mir.bin` appends a custom binary MIR artifact member (`['lib.rmeta', 'lib.rmeta-link', 'liblib_probe.lib_probe.3e9e2c9354d0a64-cgu.0.rcgu.o', 'anneal_artifact.mir.bin']`), `rustc +1.99.1` compiles and links a downstream executable against `liblib_probe.rlib` with exit code `0` (and the resulting binary executes with exit code `0`), because the system archive linker (`ld` / `lld`) only extracts archive members that resolve undefined symbol references or have `.o` object headers.
3. **What LTO in a verified backend requires inside `.rlib`:** A verified backend replacing LLVM's `.llvmbc` bitcode LTO needs either an extra archive member `<cgu>.anneal.mir` (Ignored by `rustc_metadata` and system linkers) or an ELF/Mach-O/COFF custom non-allocatable section (`.anneal.mir`, analogous to `.llvmbc`) inside each `.rcgu.o` containing serialized monomorphic/polymorphic MIR, layouts, and proof certificates.

### 4. Settings That Change MIR and Empirical Sensitivity Matrix

`Basis: source + execution (support/probe_mir_export_and_settings.py, support/mir_settings_and_rlib_probe.json)`

Running `support/probe_mir_export_and_settings.py` with `rustc 1.99.1` across 13
flag configurations on `lib_probe.rs` demonstrates how compilation flags alter
the emitted MIR even when source files are identical:

| Configuration Label | CLI Flags | Emitted MIR Lines | Basic Blocks | `assert` Terminators | `debug` Var Decls | `add_checked` Mentions | Cause of MIR Divergence |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | :--- |
| `baseline_O0_m0` | `-Copt-level=0 -Zmir-opt-level=0` | 180 | 14 | 4 | 7 | 2 | Unoptimized runtime MIR; overflow checks enabled by default at `-Copt-level=0` |
| `O0_m1_default_debug` | `-Copt-level=0` (implies `-Zmir-opt-level=1`) | 130 | 14 | 4 | 7 | 2 | `CopyProp`, `SimplifyLocals`, `RemoveZsts`, `RemoveStorageMarkers` shrink statements |
| `O2_m2_default_release` | `-Copt-level=2` (implies `-Zmir-opt-level=2`) | 222 | 6 | 0 | 7 | 1 | Overflow checks disabled; `Inline` inlines `add_checked` into `non_inline_sum`; `GVN`/`SROA`/`JumpThreading` collapse blocks |
| `O2_m0` | `-Copt-level=2 -Zmir-opt-level=0` | 138 | 10 | 0 | 7 | 2 | Disables MIR optimizations (`Inline`, `GVN`, `SROA`) while keeping release overflow-check elision |
| `O2_no_inline_mir` | `-Copt-level=2 -Zinline-mir=no` | 102 | 10 | 0 | 7 | 2 | Suppresses MIR `Inline` pass; `non_inline_sum` retains `Call` terminator to `add_checked` |
| `O2_overflow_checks` | `-Copt-level=2 -Coverflow-checks=yes` | 242 | 9 | 3 | 7 | 1 | `Operand::RuntimeChecks(OverflowChecks)` folds to `true`, keeping ` AddWithOverflow` + `TerminatorKind::Assert` |
| `O2_debug_assertions` | `-Copt-level=2 -Cdebug-assertions=yes` | 260 | 11 | 5 | 7 | 1 | Enables both `RuntimeChecks(DebugAssertions)` and `OverflowChecks` (which default to `debug_assertions`) |
| `O2_ub_checks` | `-Copt-level=2 -Zub-checks=yes` | 240 | 8 | 2 | 7 | 1 | `CheckAlignment` and `CheckNull` insert pointer alignment/non-null checks before `*p` in `ptr_read_aligned` |
| `O2_panic_abort` | `-Copt-level=2 -Cpanic=abort` | 222 | 6 | 0 | 7 | 1 | `AbortUnwindingCalls` converts `UnwindAction::Cleanup` / `Continue` on unwinding calls to `UnwindAction::Terminate` and strips landing pads |
| `O2_debuginfo_2` | `-Copt-level=2 -Cdebuginfo=2` | 260 | 6 | 0 | 35 | 1 | `Inline` preserves callee `VarDebugInfo` and inlined `SourceScopeData` scopes (`dbg=35` vs `7`) |
| `O2_avx2` | `-Copt-level=2 -Ctarget-feature=+avx2` | 222 | 6 | 0 | 7 | 1 | Alters `cfg(target_feature = "avx2")` during expansion and changes SIMD `BackendRepr` ABI classification |

Additional settings that alter MIR:
- **`Runtime(PostCleanup)` vs `Runtime(Optimized)` sensitivity:** At
  `Runtime(PostCleanup)` (`mir_drops_elaborated_and_const_checked`), `-Zmir-opt-level`
  and `-Zinline-mir` have **not yet executed**, making `Runtime(PostCleanup)`
  invariant to optimization-pass flags! However, `Runtime(PostCleanup)` **still**
  depends on:
  1. `--cfg` and `-Ctarget-feature` (which change conditional compilation and
     `BackendRepr` layouts before MIR construction);
  2. `-Cpanic=abort` vs `unwind` (consumed by `AbortUnwindingCalls` and
     `RemoveNoopLandingPads` during `run_analysis_to_runtime_passes`);
  3. `-Coverflow-checks`, `-Cdebug-assertions`, and `-Zub-checks` (because
     `mir_built` emits `Operand::RuntimeChecks`, and `LowerIntrinsics` /
     `InstSimplify` or codegen evaluates them against `Session`).

### 5. Cryptographic Binding Between Proofs, Compilation Settings, and Artifacts

`Basis: source (compiler/rustc_span/src/def_id.rs:97-210, compiler/rustc_data_structures/src/svh.rs:16-41, compiler/rustc_incremental/src/calculate_svh/mod.rs)`

`rustc` provides three built-in stable hashes, each with distinct scope:
1. **`StableCrateId` (`compiler/rustc_span/src/def_id.rs:157-210`):** A 64-bit
   `SipHash128` (`StableHasher`) truncation over `(crate_name, sorted_deduped_C_metadata, is_exe, rustc_version)`. It identifies a crate instance in the dependency graph but does **not** hash source code, MIR bodies, or codegen flags (unless Cargo passes flags via `-Cmetadata`).
2. **`DefPathHash` (`compiler/rustc_span/src/def_id.rs:97-129`):** A 128-bit
   `Fingerprint` combining `(StableCrateId, local_def_path_hash)`. It identifies an item's syntactic path (`foo[0]::bar[1]`) across sessions, independent of the item's body.
3. **`Svh` (`StrictVersionHash`, `compiler/rustc_data_structures/src/svh.rs:16-41` and `compiler/rustc_incremental/src/calculate_svh/mod.rs`):** A 128-bit `Fingerprint` computed over all HIR nodes, source file hashes, upstream crate `Svh`s, and `Session` CLI options marked `[TRACKED]`.

Because `StableCrateId` and `DefPathHash` do not commit to the MIR body, and `Svh` is computed over HIR rather than the exact exported `Runtime(PostCleanup)` MIR AST, a sound verification pipeline (such as Anneal's `.anneal/spec-lock.json` and `trusted/audit`) must bind proofs to artifacts via a two-tier content digest:
- **Per-item MIR + ABI digest:** `SHA-256(CanonicalEncode(DefPathHash, MirPhase, Body, PromotedBodies, TyAndLayoutMap, FnAbi, EvaluatedAllocations))`
- **Session & target configuration digest:** `SHA-256(CanonicalEncode(TargetTriple, DataLayout, EnabledTargetFeatures, PanicStrategy, OverflowChecks, DebugAssertions, UbChecks))`
Embedding this combined `(session_digest, item_mir_digest)` into both the Lean 4 theorem statement (or `.anneal/spec-lock.json`) and the `.rlib` / object section (`.anneal.mir`) ensures that any discrepancy between verifier settings and codegen settings is rejected mechanically at link/audit time.

## Boundaries

- **Cross-version `rustc_serialize` incompatibility:** `.rmeta` uses `rustc`'s internal `TyEncoder`/`TyDecoder`, whose tag numbering changes across compiler commits; a standalone backend that decouples from `rustc` rebuilds must define its own versioned wire schema rather than reading raw `.rmeta` tables directly.

## Evidence

- **Executable probe and results:**
  - `support/probe_mir_export_and_settings.py`
  - `support/mir_settings_and_rlib_probe.json`
- **Primary source citations (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `compiler/rustc_metadata/src/rmeta/encoder.rs:1101-1131, 1812-1860` (`should_encode_mir`, `encode_mir`)
  - `compiler/rustc_metadata/src/locator.rs:525-640` (`extract_one`, `.rlib` metadata extraction)
  - `compiler/rustc_codegen_ssa/src/back/archive.rs:545-580` (`ArArchiveBuilder::add_file`, `build_inner`)
  - `compiler/rustc_public/src/lib.rs:53-130` (`serde::Serialize` and `serialize_index_impl!`)
  - `compiler/rustc_span/src/def_id.rs:97-210` (`DefPathHash`, `StableCrateId`)
  - `compiler/rustc_data_structures/src/svh.rs:16-41` (`Svh`)

## Revalidation

Run `support/probe_mir_export_and_settings.py` with the target toolchain:

```bash
python3 reports/rustc-mir-artifact-export-settings-and-proof-binding/support/probe_mir_export_and_settings.py \
  --toolchain 1.99.1-x86_64-unknown-linux-gnu \
  --out /tmp/mir_settings_and_rlib_probe.json
```

Verify that `rlib_link_exit_code == 0`, `rlib_binary_run_exit_code == 0`, and compare the `settings_matrix` table against `support/mir_settings_and_rlib_probe.json`.
