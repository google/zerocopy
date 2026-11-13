# Verified Drop-In Rust Compiler Research Map, Crate Architecture, and Question Ledger

## Summary

Designing, verifying, and validating a drop-in replacement for **Rust 1.99.1**
(`rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67`, bundled **LLVM
23.1.1** at `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, **Anneal** at
`7abf0691c404393e3e4fc26eb3d4094e3170b5c7`, and **Lean 4 v4.34.1** at
`5045d0056413266e57c625dcd7c365b10e377c52`) spans **17 architectural design
areas** and **114 technical research questions**:

1. **Compiler crate DAG boundary (`compiler/*/Cargo.toml`):** In Rust `1.99.1`,
   the `compiler/` workspace comprises **78 crates** organized in a strict
   directed acyclic graph of **maximum depth 23** (`rustc-main` at depth 23 down
   to 17 leaf crates at depth 0). The target-independent codegen abstraction
   (`rustc_codegen_ssa` at depth 18) sits immediately above `rustc_mir_transform`
   and `rustc_metadata` (depth 17), `rustc_const_eval` and `rustc_sanitizers`
   (depth 16), `rustc_monomorphize` (depth 15), `rustc_symbol_mangling` and
   `rustc_mir_dataflow` (depth 14), `rustc_middle` (depth 13), `rustc_session`
   (depth 12), `rustc_target` (depth 10), and `rustc_abi` (depth 9).
2. **Normative and formal specification baseline:** Table 2 pins the exact
   revisions of the nine external normative and semantic repositories
   (`rust-lang/fls` tag `1.99`, `rust-lang/reference`, `rust-lang/nomicon`,
   `rust-lang/unsafe-code-guidelines`, `minirust/minirust`,
   `rust-lang/opsem-team`, `rust-lang/rfcs`, `joshlf/anneal`, and
   `leanprover/lean4`) that govern source, MIR, and target semantics.
3. **Complete 17-area coverage map and closed 114-question ledger (`0` open questions):**
   `support/roadmap_ledger.json`, `support/verify_roadmap_ledger.py`, and
   `support/query_roadmap.py` index all **107 published
   `compilers/verified-rustc` report packages** (alongside **67 foundational
   Anneal, MiniRust, and Lean 4 packages**, totaling **174 mapped packages**)
   across all 17 design areas. All **114 program research questions** are
   **answered in full (`114` answered fully, `0` answered partly, `0` open)**,
   and the end-to-end designer dry run
   (`verified-rustc-designer-dry-run-and-gap-analysis`) confirms that zero
   unrecorded external facts remain across the 13 architectural decision domains
   and 27 research goals.

## Applicability

This map and question ledger apply to the **Rust 1.99.1** compiler and
standard-library workspace (`58cf8f9c35b355199727627d07ae34a4e2846d67`), its
**LLVM 23.1.1** backend (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), the
**Lean 4 v4.34.1** proof kernel (`5045d0056413266e57c625dcd7c365b10e377c52`),
the **Anneal** verification pipeline (`7abf0691c404393e3e4fc26eb3d4094e3170b5c7`),
and the eight Tier 1 targets (`x86_64-unknown-linux-gnu`,
`x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `aarch64-unknown-linux-gnu`,
`aarch64-apple-darwin`, `aarch64-pc-windows-msvc`, `i686-unknown-linux-gnu`, and
`i686-pc-windows-msvc`):

- **Durable subject discipline:** In accordance with `FORMAT.md`, `REPORT.json`
  pins only immutable external upstream repository revisions, never prior
  commits of the `reference` branch itself. Corpus package handles are listed in
  Section 3, Section 4, and `support/roadmap_ledger.json` as navigation aids
  alongside their canonical topic queries.

## Findings

### 1. Rust 1.99.1 `compiler/` Crate Dependency DAG and Backend Seam

Basis: source + derived

Parsing all 78 `compiler/*/Cargo.toml` manifests in `rust-lang/rust` at
`58cf8f9c35b355199727627d07ae34a4e2846d67` yields a 24-layer dependency DAG
(depths 0 through 23, preserved in `support/roadmap_ledger.json`). Table 1
records the layers from `rustc_abi` (depth 9) up to `rustc-main` (depth 23) that
define the interface between the Rust frontend/middle-end and code generation.

| DAG Depth | `compiler/` Crates in Rust `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) | Role in Drop-In Verified Compilation |
| :--- | :--- | :--- |
| **23** | `rustc-main` | Thin binary entry point invoking `rustc_driver`. |
| **22–20** | `rustc_driver` (22), `rustc_driver_impl` (21), `rustc_interface` (20) | CLI flag parsing, callback hooks (`Callbacks`), query-ctxt initialization, and codegen-backend loading (`-Zcodegen-backend`). |
| **19** | `rustc_codegen_llvm` | Default LLVM 23.1.1 backend implementing `rustc_codegen_ssa::traits::CodegenBackend`; links `rustc_llvm` (depth 0). |
| **18** | `rustc_codegen_ssa`, `rustc_resolve` | Target-independent codegen traits (`BuilderMethods`, `BackendTypes`, `WriteBackendMethods`, `AsmCodegenMethods`), MIR-to-SSA traversal (`rustc_codegen_ssa::mir`), and LTO/linker orchestration (`back::write`, `back::link`). Note that `rustc_codegen_cranelift` and `rustc_codegen_gcc` appear at depth 0 in `compiler/*/Cargo.toml` because they link compiler internals via `rustc_private` extern crates rather than Cargo path dependencies. |
| **17** | `rustc_mir_transform`, `rustc_metadata`, `rustc_hir_typeck`, `rustc_builtin_macros` | Post-borrowck MIR optimization pipeline, `Runtime(PostCleanup)` lowering (`ElaborateDrops`, `LowerIntrinsics`), `.rmeta` cross-crate MIR serialization, and `asm!`/`global_asm!` expansion. |
| **16** | `rustc_borrowck`, `rustc_const_eval`, `rustc_sanitizers`, `rustc_mir_build`, `rustc_ty_utils`, `rustc_expand`, `rustc_hir_analysis`, `rustc_lint`, `rustc_passes`, `rustc_traits` | Miri CTFE engine (`rustc_const_eval::interpret`), Polonius/NLL borrow checking, layout computation (`rustc_ty_utils::layout`), and sanitizer instrumentation. |
| **15** | `rustc_monomorphize`, `rustc_trait_selection`, `rustc_public`, `rustc_ast_lowering`, `rustc_ast_passes`, `rustc_privacy` | Reachability collection (`collector`), CGU partitioning (`partitioning`), and polymorphic instance resolution (`Instance::mono`). |
| **14** | `rustc_symbol_mangling`, `rustc_mir_dataflow`, `rustc_query_impl`, `rustc_incremental`, `rustc_transmute`, `rustc_infer`, `rustc_pattern_analysis`, `rustc_public_bridge`, `rustc_attr_parsing`, `rustc_ty_walk` | `v0` and `legacy` symbol mangling, abstract interpretation over MIR CFGs, and incremental compilation dependency-graph hashing. |
| **13–12** | `rustc_middle` (13), `rustc_hir_pretty` (13), `rustc_parse` (13), `rustc_session` (12), `rustc_hir` (12), `rustc_crate_store` (12) | Central `TyCtxt<'tcx>` arena, `mir::syntax` AST definitions (`Body`, `StatementKind`, `Rvalue`, `TerminatorKind`), and session options (`-C`, `-Z`). |
| **11–9** | `rustc_type_ir` (10), `rustc_target` (10), `rustc_abi` (9) | Target specification structs (`Target`, `TargetOptions`), data-layout strings, `TyAndLayout`, and `FnAbi`/`ArgAbi` calling-convention rules. |

### 2. Pinned Normative and Semantic Authority Repositories

Basis: normative + source

Table 2 records the exact commits of the nine normative and formal specification
repositories inspected alongside `rust-lang/rust` `1.99.1`.

| Repository | Pinned Revision | Commit Date | Authority Scope |
| :--- | :--- | :--- | :--- |
| `rust-lang/fls` | `946eacae5a4a33a89af7832178504692439e7478` (tag `1.99`) | 2026-10-30 | Ferrocene Language Specification for Rust `1.99` (syntax, type system, attributes, ABI, inline assembly, and library contracts). |
| `rust-lang/reference` | `bcd62f35e8bf480ec5b0fa569b6d12ea5924030c` | 2026-11-10 | Upstream Rust Reference defining language constructs, memory model, type layout (`repr(C)`, `repr(Rust)`, `repr(simd)`), and list of behaviors considered undefined. |
| `rust-lang/nomicon` | `b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6` | 2026-10-17 | Unsafe Rust invariants, drop check, unwinding across FFI (`C-unwind`), and subtyping variance. |
| `rust-lang/unsafe-code-guidelines` | `d809f91e62968913d808e53397fbcf7cea762cce` | 2026-05-05 | Operational validity invariants (`Scalar`, padding, uninitialized memory), aliasing, and layout guarantees. |
| `minirust/minirust` | `063d784186d3252bee242217f218223205c0b568` | 2026-11-06 | Mechanized-style operational semantics for MiniRust (`BasicMemory`, `TreeBorrows`, `StackedBorrows`, pointer provenance, and value representation transfers). |
| `rust-lang/opsem-team` | `d462085814030cc5b21dfa0ce831dfc1619d69b1` | 2026-09-14 | Operational Semantics Team decisions and tracking issues on UB, provenance, and concurrency. |
| `rust-lang/rfcs` | `7677feddd580f356f780cb7123aeda6a3708275a` | 2026-11-10 | Design RFCs (`v0` symbol mangling RFC 2603, inline `asm!` RFC 2873, `c_unwind` RFC 2945, Strict Provenance RFC 3559, Float Semantics RFC 3514). |
| `joshlf/anneal` | `7abf0691c404393e3e4fc26eb3d4094e3170b5c7` | 2026-11-12 | `trusted/lean` MIR semantics, `Trusted.CrateTheorem`, `trusted/audit` `.olean` verifier, and `trusted/rustc-capture`. |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | 2026-09-24 | Lean 4 kernel, `bv_decide`/`bv_omega` decision procedures, Lean-to-C compiler, and bundled LLVM `22.1.4` toolchain. |

### 3. Complete 17-Area Coverage Summary (`107` `compilers/verified-rustc` Packages, `114 / 114` Questions Answered)

Basis: source + execution + derived

Table 3 summarizes all **17 design areas** of the verified drop-in `rustc`
replacement, mapping each area to its governing `rustc 1.99.1` crates, count of
`compilers/verified-rustc` packages (plus foundational Anneal/MiniRust/Lean 4
packages), and closed question counts (`114` answered in full, `0` partly
answered, `0` open).

| Area ID & Title | Governing `rustc 1.99.1` Crates | `verified-rustc` Packages (+ Foundational) | Answered (Full / Part) | Open Questions | Key Established Architectural and Quantitative Findings |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **1. `contract`** (Drop-in CLI/JSON, build systems, tooling, deviations) | `rustc_driver`, `rustc_driver_impl`, `rustc_interface`, `rustc_session`, `rustc_errors`, `rustc_feature`, `rustc_lint` | 7 (+ 4) | 7 / 0 | 0 | 38 top-level, 54 `-C`, 238 `-Z`, 21 `--print`, 11 `--emit`, 8 `--crate-type` options; 27-method `CodegenBackend`; 9 build systems (`rustc -vV` + stdin `--print`); 14 backend-dependent observable categories; 5-tier normative map resolving 18 spec disagreements; 292 `known-bug` UI tests; 219 codegen-relevant features; Miri (`-Zmiri-tree-borrows`) & `rust-analyzer` ABI v2 (`version 10`). |
| **2. `end-to-end-theorem`** (Theorem shape, composition, property transfer, 5-link chain) | `rustc_middle`, `rustc_codegen_ssa` (+ Anneal `trusted/lean`) | 5 (+ 8) | 5 / 0 | 0 | `ProductiveCompiles` + `ResourceBSim` transfer all 10 Anneal claim forms; CompCertO/DimSum open simulations with `ModuleSummary`/`ExportList` invariants handle ThinLTO/FatLTO; 5-link Lean `v4.34.1` prototype (`642` LOC, `4.27s`, `0` `sorryAx`) bridges 5 seams from Anneal MIR to 29-byte x86-64 `-O3` machine code. |
| **3. `mir-and-aliasing`** (MIR semantics, aliasing, FP, allocation/provenance, layout) | `rustc_middle`, `rustc_abi`, `rustc_const_eval`, `rustc_mir_dataflow`, `rustc_ty_utils` | 6 (+ 15) | 6 / 0 | 0 | Complete semantics for 12 `StatementKind`, 14 `TerminatorKind`, 13 `Rvalue`, 12 `CastKind` variants; Tree Borrows eliminates `63.0%` (`4,969 / 7,887`) of ecosystem Miri UB failures while preserving `1.14x–1.38x` `noalias` memory-kernel speedups; RFC 3514 4-choice NaN lattice; `alloc::alloc::alloc` elision/coalescing + PNVI-ae-udi provenance; 8-target `TargetDataLayout` goldens. |
| **4. `concurrency`** (Weak memory models, Tier 1 atomic lowerings, hardware litmus) | `rustc_middle`, `rustc_codegen_ssa`, `rustc_codegen_llvm` | 3 (+ 4) | 3 / 0 | 0 | RC11/IMM axiomatic hardware mapping proofs combined with Promising-style thread-local views; exact 8-target atomic/fence instruction tables (including `i686` `cmpxchg8b` and `aarch64` `+lse`/`+rcpc`/`+outline-atomics`); `2.70e6` native `x86_64` hardware litmus runs (`495 / 300k` `SB_Relaxed` weak outcomes, `0 / 300k` `SeqCst`) matching `herd7` 7.58. |
| **5. `platform-conventions`** (Calling conventions, unwinding, TLS, stack, startup, objects, linking) | `rustc_target`, `rustc_abi`, `rustc_codegen_ssa`, `rustc_codegen_llvm`, `rustc_sanitizers` | 13 (+ 5) | 13 / 0 | 0 | 8-target `FnAbi` rules + 16-pair live caller $\times$ callee ABI matrix (`100%` parity); DWARF `.eh_frame`/LSDA, Mach-O `__unwind_info`, Windows `.pdata`/`.xdata` (`__CxxFrameHandler3`), and 32-bit `i686` `fs:[0]` SEH decoded and verified; 4 TLS models; inline/`__chkstk` stack probes; CRT startup; ELF/Mach-O/COFF relocations, archives, dynamic loaders, OS syscalls, and EULA-free Linux-hosted `rust-lld` cross-compilation. |
| **6. `intrinsics-and-assembly`** (Intrinsics, vendor SIMD, target features, inline `asm!`) | `rustc_middle`, `rustc_codegen_ssa`, `rustc_target`, `rustc_builtin_macros` | 7 (+ 2) | 7 / 0 | 0 | 316 `#[rustc_intrinsic]` items, 81 `simd_*` operations, and 8,115 `core_arch` LLVM bindings across 74 x86 and 90 AArch64 target features; Intel XML (`6.7 MB`) and Arm JSON (`5.1 MB`) Lean 4 semantics generator (`100%` match across `32,000` hardware co-execution vectors); `compiler_builtins` libcall table; `asm!`/`naked_asm!`/`global_asm!` specification, census, and Islaris/`s2n-bignum` contract frameworks. |
| **7. `isa-models`** (Formal x86-64, i386, AArch64 models, hardware validation, assemblers/linkers) | `rustc_target` | 4 (+ 4) | 4 / 0 | 0 | Coverage and fidelity evaluation of Arm ASL/Sail, `LNSym`, ACL2 `x86isa`, K-x86, Sail-x86, HOL4 L3, and CompCert; Intel vs. AMD undefined-flag nondeterminism and hardware co-simulation; top 65 x86-64 and 55 AArch64 mnemonics cover `>99.2%` of `-O3` instructions; CompCertELF/CakeML/RockSalt verified encoder/linker foundations. |
| **8. `verified-mode`** (Per-function routing, LLVM attributes, binary origin, attestation, LLVM-free sysroot) | `rustc_codegen_ssa`, `rustc_monomorphize`, `rustc_symbol_mangling`, `rustc_metadata` | 5 (+ 4) | 5 / 0 | 0 | Composite `CodegenBackend` routing per function/CGU; 42 cross-path LLVM attribute obligations cataloged; `98.4%` of executable `.text` traced to Rust CGUs (`74%–89%` stdlib pruned by `--gc-sections`; `--icf=safe` required); non-allocatable `.note.anneal.manifest` + detached bundles; full Tier 1 sysroot built without LLVM. |
| **9. `normal-compilation`** (Wild profiles, PGO, LTO, debuginfo, hardening, size opt) | `rustc_session`, `rustc_codegen_ssa`, `rustc_codegen_llvm`, `rustc_sanitizers` | 6 (+ 0) | 6 / 0 | 0 | Wild `Cargo.toml` profile/flag census; PGO (`INSTR_PROF_RAW_VERSION = 11`, `9.1%–18.4%` speedup, IR-portable CFG profile format); LTO (`No`, `ThinLocal`, `Thin`, `Fat` export-list contracts, `8.4%–14.2%` speedup); DWARF v4/v5 & CodeView/PDB debugger contracts; PIE/RELRO/CET/PAC/BTI/CFG hardening; `-Os`/`-Oz` mapped to `O2` + `optsize`/`minsize` in LLVM 23.1.1 (`26.8%–41.2%` `.text` reduction). |
| **10. `rustc-internals`** (Repository map, MIR export, MIR passes, monomorphization, lowering) | `rustc_middle`, `rustc_mir_transform`, `rustc_monomorphize`, `rustc_const_eval`, `rustc_codegen_ssa`, `rustc_codegen_llvm`, `rustc_symbol_mangling` | 5 (+ 6) | 10 / 0 | 0 | 78-crate DAG and query map; deterministic `.anneal-mir` format + 17 MIR-affecting settings + SHA-256 binding; 67 `MirPass`es (42 in `inner_optimized_mir`, `<0.8%` speed impact at `-O3`); 5 `InstanceKind` + 12 `ShimKind` variants, 3-word vtable headers, `GlobalAlloc` relocations, `v0`/`legacy` mangling, CGU partitioning, and `139` `BuilderMethods` in `rustc_codegen_ssa::mir`. |
| **11. `ecosystem-demand`** (Stdlib demand, download-weighted crate census, CPU time breakdown) | `rustc_middle` (+ `library/*`) | 3 (+ 0) | 3 / 0 | 0 | Complete 8-target `core`/`alloc`/`std`/`compiler_builtins` demand matrix; top-100 download-weighted crates.io census (`1,129`-crate closure, `94.2%` assembly-free); 8-domain runtime profiling (`40` `-O0` `panic_bounds_check` calls $\rightarrow$ `100%` eliminated in slice iterators at `-O3`; `1.18x–2.41x` `x86-64-v3` SIMD speedups). |
| **12. `proof-system-and-irs`** (Certificates, relational logics, IRs, LLVM 23 semantics, e-graphs, prototypes) | Anneal `trusted/lean`, `theory/Anneal` | 9 (+ 8) | 9 / 0 | 0 | `HybridTrace` expresses `12 / 12` (`100%`) `-O3` classes at `24.77 B/step` raw (`12.04 B/step` zstd); Lean `v4.34.1` `checkDeriv_sound` + `checkDeriv_complete` prototype (`691` lines, `2.95x` ratio, `0` `sorryAx`); full sysroot certificates ~`3.6 MB` compressed; LLVM 23.1.1 IR formal semantics; acyclic e-graph refinement proofs; verified `BitVec`/`omega`/interval/FP side-condition checkers. |
| **13. `optimizer`** (LLVM NewPM pipeline, pass ablation, proof obligations, TableGen, backend candidates) | `rustc_codegen_llvm`, `rustc_llvm` | 9 (+ 2) | 11 / 0 | 0 | Complete LLVM 23.1.1 NewPM pipelines; 12-group LOO/AOI pass ablation (`Inlining`, `SROA`, `InstCombine`, `SimplifyCFG`, `LoopOpt/LICM`, `Vectorization` yield `>99%` of the `11.71x` `-O3` speedup); scalar/memory/loop/IPO/codegen proof obligations; Cranelift (`11.95x` slower at `-O3`) vs. GCC vs. LLVM; `684,912` TableGen lines (`18,412` x86, `9,846` AArch64 records) extracted to JSON/Lean 4. |
| **14. `validated-llvm`** (Black-box Alive2 validation vs. derivation-emitting LLVM) | `rustc_codegen_llvm` | 2 (+ 0) | 2 / 0 | 0 | `100%`-accepting (`10 / 10`) `Runtime(PostCleanup)` MIR-to-LLVM-IR SMT validator prototype; `94.4%` (`17 / 18`) Alive2 acceptance on single scalar/memory/CFG LLVM pass groups (`66.7%` LoopVectorize, `44.4%` whole `-O3`); 131 LLVM 23.1.1 pass modules (`574,990` C++ LOC, `4,655` mutation sites) inventoried for remark/certificate instrumentation. |
| **15. `checker-substrate`** (Lean native compilation trust, kernel scaling, standalone checkers, TCB inventory) | Anneal `trusted/audit`, `trusted/cargo-anneal` | 6 (+ 5) | 6 / 0 | 0 | Lean `v4.34.1` `EmitC.lean`/RC/`libgmp` audit; CPS-forced `ReflPacked_NatGMP` kernel reflection checks $10^6$ steps in `11.89s` (`84,118` steps/s, `524 MB` RSS); `nanoda_lib` & `lean4lean` independent checkers; Compiled Lean `4.34.1` (`1.10x` of Rust on `IO.Ref Array` dominators) vs. Rust `1.99.1` (`28.34x` faster on packed `u64` bitsets); 5-stratum TCB inventory; family-stratified tag-record Lean 4 ISA models ($K=2,000$ opcodes in `2.66s–4.30s`). |
| **16. `validation`** (`compiletest`, test classification, fuzzers, Crater, target execution, parity baselines) | `src/tools/compiletest` | 7 (+ 0) | 7 / 0 | 0 | `compiletest` alternate-backend mechanics; machine-readable classification of all `28,412` `rustc 1.99.1` tests; `rustlantis`/`RustSmith`/`abi-cafe` differential fuzzing; Crater & `stage0` $\rightarrow$ `stage2` self-hosting; QEMU/Wine/`remote-test-server` Tier 1 execution; `--shuffle-sections` layout noise floor ($\sigma_{\text{layout}}$ up to `20.57%`) and multi-target parity baselines; Loom/Shuttle/GenMC/Miri concurrency & SIMD harnesses. |
| **17. `program-planning`** (Baseline, corpora, effort, licensing, qualification, future horizons, dry run) | `rustc_driver`, `rustc_middle` | 10 (+ 0) | 10 / 0 | 0 | Pinned `1.99.1` + Lean `v4.34.1` baseline (`rustc-baseline-toolchain-selection-and-manifest`); shared crate/benchmark corpora (`rustc-experimental-corpora-and-harness-conventions`); 20-project effort precedents (`2.4x–4.8x` proof-to-code vs. `0.2x–0.8x` with certificate checkers); clean-room Apache-2.0/MIT licensing & SDK rules; ISO 26262 TCL3 / DO-178C TQL-1 qualification cases; Future Horizons (verified frontend, safe Rust UB-freedom over `14,812` stdlib `unsafe` blocks, cross-language LTO); and zero-gap designer dry run (`verified-rustc-designer-dry-run-and-gap-analysis`). |
| **Total Across All 17 Areas** | **78 `compiler/` Crates** | **107 (+ 67 = 174)** | **114 / 0** | **0** | **100% of all 114 program questions answered; 0 unrecorded external facts.** |

---

### 4. Complete Catalog of All 107 `compilers/verified-rustc` Packages by Design Area

Basis: source + derived

Table 4 lists the exact package directory names under `reports/<package>/` for
all **107 `compilers/verified-rustc` report packages**, organized by the 17
design areas in `support/roadmap_ledger.json`.

| Area ID | Count | Published `compilers/verified-rustc` Report Packages (`reports/<package>/`) |
| :--- | :--- | :--- |
| **1. `contract`** | 7 | `rustc-external-cli-json-and-backend-interface-contract`, `rustc-build-system-and-consumer-invocation-contracts`, `rustc-backend-dependent-observable-behaviors`, `rust-normative-authority-map-and-rustc-deviations`, `rustc-and-llvm-soundness-holes-and-miscompilation-census`, `rust-language-and-library-codegen-feature-inventory`, `miri-rust-analyzer-proc-macro-and-doctest-toolchain-contracts` |
| **2. `end-to-end-theorem`** | 5 | `compiler-correctness-theorem-shapes-and-end-to-end-chains`, `compositional-correctness-linking-and-whole-program-optimization`, `observable-behavior-property-transfer-and-anneal-statement-forms`, `cross-prover-guarantee-composition-and-native-checker-soundness`, `end-to-end-verified-mir-to-isa-refinement-chain-and-seams` |
| **3. `mir-and-aliasing`** | 6 | `rustc-mir-construct-semantics-miri-minirust-and-codegen`, `rust-aliasing-models-stacked-tree-minirust-and-llvm-attributes`, `rust-aliasing-models-ub-prevalence-and-llvm-optimization-value`, `rust-floating-point-semantics-llvm-lowering-and-isa-behavior`, `rust-allocation-provenance-and-stack-lifetime-semantics`, `rustc-layout-computation-target-datalayouts-and-parametricity` |
| **4. `concurrency`** | 3 | `weak-memory-concurrency-models-hardware-mappings-and-optimizations`, `tier1-atomics-and-fences-instruction-lowering`, `weak-memory-hardware-litmus-testing-x86-and-aarch64` |
| **5. `platform-conventions`** | 13 | `tier1-calling-conventions-fnabi-and-llvm-lowering`, `abi-cross-testing-matrix-rustc-llvm-cranelift-gcc-clang`, `unwinding-on-elf-and-macho-targets`, `unwinding-on-windows-targets-and-32bit-seh`, `rust-thread-local-storage-models-and-runtime-contracts`, `rust-stack-discipline-probes-red-zones-and-overflow`, `rust-program-startup-runtime-objects-and-entry-state`, `rustc-object-files-sections-symbols-comdats-and-relocations`, `rustc-static-linking-archive-formats-and-linker-driver`, `rustc-dynamic-linking-loader-contracts-and-code-signing`, `tier1-linux-hosted-cross-compilation-recipes-and-sysroots`, `tier1-default-codegen-settings-and-target-options`, `os-syscall-interfaces-asynchronous-signals-and-environment-models` |
| **6. `intrinsics-and-assembly`** | 7 | `rustc-intrinsics-simd-and-arch-semantic-sources`, `vendor-intrinsic-specifications-stdarch-verification-and-lean-generation`, `llvm-instruction-selection-fallbacks-and-libcall-contracts`, `target-features-implications-detection-and-abi-effects`, `rustc-inline-assembly-specification-llvm-lowering-and-assembler-syntax`, `rust-ecosystem-inline-assembly-global-asm-and-naked-function-census`, `machine-code-verification-frameworks-and-assembly-contracts` |
| **7. `isa-models`** | 4 | `formal-isa-models-x86-64-i386-and-aarch64-coverage`, `isa-model-hardware-validation-divergences-errata-and-resources`, `llvm-compiled-rust-instruction-and-addressing-mode-frequencies`, `verified-assemblers-encoders-linkers-and-object-format-models` |
| **8. `verified-mode`** | 5 | `rustc-codegen-backend-routing-and-mixed-backend-interoperability`, `rustc-llvm-ir-attributes-metadata-and-cross-path-obligations`, `rustc-binary-origin-attribution-gc-sections-and-icf-soundness`, `binary-evidence-packaging-provenance-attestations-and-rustc-reproducibility`, `rustc-llvm-free-sysroot-cranelift-gcc-and-host-tools-audit` |
| **9. `normal-compilation`** | 6 | `cargo-profile-and-compiler-flag-census-in-the-wild`, `rustc-pgo-mechanics-heuristics-value-and-ir-portability`, `rustc-lto-mechanics-symbol-preservation-and-performance-value`, `rustc-dwarf-codeview-debuginfo-emission-and-debugger-contracts`, `rustc-tier1-security-hardening-and-mitigation-codegen`, `rustc-size-optimized-compilation-parity-and-transformations` |
| **10. `rustc-internals`** | 5 | `rustc-baseline-repository-map-and-internal-interfaces`, `rustc-mir-artifact-export-settings-and-proof-binding`, `rustc-mir-optimization-passes-semantics-soundness-and-value`, `rustc-monomorphization-vtables-statics-symbols-and-cgu-partitioning`, `rustc-mir-to-llvm-lowering-and-runtime-visible-semantics` |
| **11. `ecosystem-demand`** | 3 | `rustc-standard-library-codegen-demand-per-target`, `crates-io-download-weighted-codegen-demand-census`, `where-time-goes-in-rust-programs-hot-patterns-and-instruction-mix` |
| **12. `proof-system-and-irs`** | 9 | `proof-producing-compilation-and-certificate-formats-quantitative-survey`, `relational-logics-simulation-techniques-and-completeness-for-compiler-derivations`, `mechanized-compiler-ir-semantics-poison-provenance-and-machine-frames`, `llvm-ir-baseline-formal-semantics-and-ambiguities`, `llvm-o3-derivation-formats-expressiveness-and-checking-cost`, `lean-derivation-checker-soundness-and-completeness-prototype`, `rustc-build-ir-and-pass-transformation-volume-statistics`, `equality-saturation-with-proofs-egraphs-aegraphs-and-refinement-rewriting`, `verified-side-condition-decision-procedures-and-certificate-checkers` |
| **13. `optimizer`** | 9 | `rustc-llvm-pass-pipelines-and-configuration`, `llvm-pass-ablation-speed-and-size-on-rust-code`, `llvm-scalar-memory-and-loop-optimization-proof-obligations`, `llvm-interprocedural-lto-and-codegen-optimization-obligations`, `verified-and-validated-compiler-optimization-precedents`, `candidate-optimizers-llvm-cranelift-and-gcc-backend-comparison`, `proven-baseline-compiler-candidates-and-reusable-verified-backends`, `llvm-tablegen-isa-extraction-and-verified-selector-reuse`, `performance-models-and-microarchitectural-tuning-data` |
| **14. `validated-llvm`** | 2 | `black-box-translation-validation-alive2-and-mir-to-llvm-on-rust`, `llvm-derivation-emission-instrumentation-architecture-and-cost` |
| **15. `checker-substrate`** | 6 | `lean-native-compilation-pipeline-runtime-and-trust-surface`, `lean-kernel-derivation-scale-checking-and-reflection-throughput`, `independent-proof-checkers-and-smaller-trusted-computing-bases`, `compiler-substrate-benchmarks-lean-rust-and-ocaml`, `verified-rustc-delivered-toolchain-trusted-component-inventory`, `lean-large-isa-and-compiler-semantics-scaling` |
| **16. `validation`** | 7 | `rustc-compiletest-bootstrap-and-alternate-backend-test-mechanics`, `rustc-test-suite-machine-readable-classification`, `compiler-differential-testing-fuzzing-reduction-and-bug-records`, `ecosystem-scale-testing-crater-self-hosting-and-flakiness`, `tier1-target-test-execution-emulators-and-combinatorial-coverage`, `rustc-benchmark-methodology-and-speed-size-baselines`, `concurrency-and-simd-compiler-testing-tools-and-harnesses` |
| **17. `program-planning`** | 10 | `rustc-baseline-toolchain-selection-and-manifest`, `rustc-experimental-corpora-and-harness-conventions`, `verified-rustc-research-map-and-open-question-ledger`, `verified-compiler-effort-precedents-and-agent-proof-productivity`, `compiler-isa-sdk-licensing-trademarks-and-upstream-governance`, `compiler-qualification-assurance-cases-and-deviation-policies`, `verified-rust-frontend-approaches-trait-solver-polonius-and-thir-lowering`, `safe-rust-ub-freedom-soundness-and-standard-library-verification`, `cross-language-lto-linker-plugin-bitcode-and-llvm-ir-semantics`, `verified-rustc-designer-dry-run-and-gap-analysis` |

## Boundaries

- **Point-in-time baseline (`Rust 1.99.1`, `LLVM 23.1.1`, `Lean 4 v4.34.1`):**
  All 114 answered questions and 107 `compilers/verified-rustc` packages are
  anchored to the pinned `1.99.1` / `23.1.1` / `v4.34.1` revisions in Table 2.
  Later upstream `rust-lang/rust`, `llvm-project`, or `leanprover/lean4`
  revisions (such as `1.100.0`'s `ProjectionElem::PhantomDeref` MIR change)
  lie outside the pinned v0 replacement target and should be re-evaluated using
  each package's `## Revalidation` probes if a future version migration is
  considered.

## Evidence

- **Compiler crate DAG:** Extracted directly from the 78 `compiler/*/Cargo.toml`
  manifests in `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`.
- **Normative specification revisions:** Verified via `git rev-parse HEAD` across
  the nine upstream repositories listed in Table 2.
- **Preserved support artifacts:**
  - `support/roadmap_ledger.json` — machine-readable 78-crate compiler DAG by
    depth and the 17-area mapping of governing crates, normative sources, topic
    queries, all 107 `compilers/verified-rustc` packages (plus 67 foundational
    packages), and all 114 answered program questions (`0` open questions).
  - `support/verify_roadmap_ledger.py` — automated verification script checking
    that all 17 areas, 114 questions, and 107 `compilers/verified-rustc`
    packages in `CATALOG.json` are completely indexed and answered.
  - `support/query_roadmap.py` — standalone CLI wrapper to query coverage by
    design area.

## Revalidation

To verify that all 17 design areas, 114 program questions, and 107
`compilers/verified-rustc` packages in `CATALOG.json` are indexed with zero
unanswered questions, run:

```console
python3 reports/verified-rustc-research-map-and-open-question-ledger/support/verify_roadmap_ledger.py
python3 reports/verified-rustc-research-map-and-open-question-ledger/support/query_roadmap.py
```
