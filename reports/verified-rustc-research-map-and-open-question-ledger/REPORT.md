# Verified Drop-In Rust Compiler Research Map, Crate Architecture, and Question Ledger

## Summary

Designing, verifying, and validating a drop-in replacement for **Rust 1.99.1**
(`rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67`, bundled **LLVM
23.1.1** at `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, **Anneal** at
`7abf0691c404393e3e4fc26eb3d4094e3170b5c7`, and **Lean 4 v4.34.1** at
`5045d0056413266e57c625dcd7c365b10e377c52`) spans **17 architectural design
areas** and **186 technical research questions**:

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
3. **Complete 17-area coverage map and closed 186-question ledger (`0` open questions):**
   `support/roadmap_ledger.json`, `support/verify_roadmap_ledger.py`, and
   `support/query_roadmap.py` index all **179 published
   `compilers/verified-rustc` report packages** (alongside **67 foundational
   Anneal, MiniRust, and Lean 4 packages**, totaling **246 mapped packages**)
   across all 17 design areas. All **186 program research questions** (`114`
   from Waves 0–4, `40` from Wave 5, and `32` from Wave 6 across `L1_`–`L8_`,
   `O1_`–`O8_`, `M1_`–`M8_`, and `K1_`–`K8_`) are **answered in full (`186`
   answered fully, `0` answered partly, `0` open)**, and the end-to-end designer
   dry run (`verified-rustc-designer-dry-run-and-gap-analysis`) confirms that
   zero unrecorded external facts remain across the 13 architectural decision
   domains and 35 research goals.

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

### 3. Complete 17-Area Coverage Summary (`179` `compilers/verified-rustc` Packages, `186 / 186` Questions Answered)

Basis: source + execution + derived

Table 3 summarizes all **17 design areas** of the verified drop-in `rustc`
replacement, mapping each area to its governing `rustc 1.99.1` crates, count of
`compilers/verified-rustc` packages (plus foundational Anneal/MiniRust/Lean 4
packages), and closed question counts (`186` answered in full, `0` partly
answered, `0` open).

| Area ID & Title | Governing `rustc 1.99.1` Crates | `verified-rustc` Packages (+ Foundational) | Answered (Full / Part) | Open Questions | Representative Wave 0–6 Architectural and Quantitative Findings |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **1. `contract`** (1. Drop-In Compiler Contract, CLI/JSON Surfaces, Build Systems, Tooling, and Deviation Policy) | `rustc_driver`, `rustc_driver_impl`, `rustc_interface`, `rustc_session`, `rustc_errors`, `rustc_feature`, `rustc_lint` | 8 (+ 4) | 8 / 0 | 0 | [C7] Miri (20 rustc_private crates, -Zmiri-tree-borrows), rust-analyzer, proc-macro server ABI v2 (format version 10), and rustdoc --test-builder integration contracts; [K8_] Span-stripped MirItemKey with sideband StmtOrd Span tables (100% cache hit under 50-line comment shifts, 100% exact shifted diagnostic spans) and unified cargo anneal human/JSON/SARIF 2.1.0 diagnostic engine + 513-byte .anneal-repro minidumps |
| **2. `end-to-end-theorem`** (2. End-to-End Compiler Correctness Theorem, Compositional Linking, Cross-Prover Soundness, and Five-Link Prototype) | `rustc_middle`, `rustc_codegen_ssa` | 10 (+ 8) | 10 / 0 | 0 | [O6_] Cross-DSO LinkWorldContract in Lean 4.34.1 proving duplicate vtable addresses across cdylib/dlopen boundaries, two-level DSO vtable+slot guarding (95% hit rate, +22.43% speedup), and CratePrivateTraitInOpenBinary unguarded devirtualization (+52.63% speedup); [O7_] Tarjan SCC greatest-fixpoint certificates (SccGfpCert for nounwind/memory effects) and 2D lexicographic Farkas ranking certificates (SccRankingCert for willreturn) proving 26/26 bounded mutually recursive functions where LLVM proves 0/26 (339.46x caller DCE/LICM speedup) |
| **3. `mir-and-aliasing`** (3. MIR Operational Semantics, Aliasing Models, Allocation, Provenance, Floating-Point, and Layout) | `rustc_middle`, `rustc_abi`, `rustc_const_eval`, `rustc_mir_dataflow`, `rustc_ty_utils` | 15 (+ 15) | 15 / 0 | 0 | [L5_] Field-disjoint interior-pointer provenance splitting (PinFieldSplitCert) and unresumed child-future memcpy elision (UnresumedMoveIsRelocatable) reducing !Unpin coroutine frames from 80-104 B to 0 B (3.71x-9.34x speedup); [L6_] Tree Borrows unwind-landing-pad store sinking (SinkStoreToCleanupCert), loop &mut register promotion (PromoteProtectedMutInLoopCert), and caller-unobservable unwind DSE (1.18x-1.43x speedup under panic=unwind) |
| **4. `concurrency`** (4. Concurrency Theory, Relaxed Memory Models, Tier 1 Atomic Lowerings, and Hardware Litmus Validation) | `rustc_middle`, `rustc_codegen_ssa`, `rustc_codegen_llvm` | 3 (+ 4) | 3 / 0 | 0 | [S14] Exact instruction sequences emitted by rustc 1.99.1 and LLVM 23.1.1 for atomic loads, stores, RMWs, cmpxchg, and fences across all 8 Tier 1 targets (including i686 cmpxchg8b and AArch64 +lse/+rcpc/+outline-atomics); [S15] Empirical hardware weak-memory litmus execution (2.70e6 barrier-synchronized runs across 9 families on x86_64 plus AArch64 assembly verification) cross-checked against herd7 7.58 |
| **5. `platform-conventions`** (5. Tier 1 Platform Conventions: Calling Conventions, Unwinding, TLS, Stack Discipline, Startup, Object Formats, and Linking) | `rustc_target`, `rustc_abi`, `rustc_codegen_ssa`, `rustc_codegen_llvm`, `rustc_sanitizers` | 17 (+ 5) | 17 / 0 | 0 | [M5_] Concrete BitVec 64/128 sub-eightbyte shift/mask packing (unpack_pack_eightbyte_bitvec_id), AArch64/Win64 HFA lane extraction, C bitfields, and 4-ABI va_list state-machine refinement in Lean 4.34.1 (542 LOC, 0 sorryAx); [M8_] Bit-for-bit reproducible final executable linking across all 8 Tier 1 targets (0 diff bytes across dual directories/timestamps/threads) and deterministic Mach-O CS_CodeDirectory 4 KiB page SHA-256 Merkle signing covering ANNEAL_EVID_V1 |
| **6. `intrinsics-and-assembly`** (6. Compiler Intrinsics, Vendor SIMD Specifications, Target Features, and Inline Assembly) | `rustc_middle`, `rustc_codegen_ssa`, `rustc_target`, `rustc_builtin_macros` | 9 (+ 2) | 9 / 0 | 0 | [O4_] Complete legalization taxonomy and SplitVecCert proofs for all 81 rustc 1.99.1 simd_* intrinsics (512->256->128-bit splitting across AVX-512, AVX2, SSE2, NEON) and parameterized Intel Xeon / AMD Zen 4-5 / Arm Neoverse cost models; [M2_] Complete 333-site rustc 1.99.1 sysroot inline-asm census, Intel/AT&T/AArch64 template substitution parser, hidden-symbol extractor, and direct machine-code encoder achieving 100% (31/31) byte parity against llvm-mc without external assemblers |
| **7. `isa-models`** (7. Formal ISA Models (x86-64, i386, AArch64), Hardware Validation, Instruction Frequencies, and Verified Assemblers/Linkers) | `rustc_target` | 8 (+ 4) | 8 / 0 | 0 | [B10] Decidable linear-time machine-code byte validator (checkBinaryWF_sound, 78.67 MB/s across 2,494 Tier 1 sysroot .o files) checking canonical decoding, 16B stack alignment, stack probes, red zones, vzeroupper, errata, and CFI; [M7_] Post-link ELF/PE/Mach-O executable validator (checkLinkedBinaryWF) verifying resolved relocations, GOT-to-LEA relaxation, >128 MiB AArch64 veneers, Cortex-A53 page-end ADRP Erratum 843419 (0xFF8), and merged CET/BTI/PAC/GCS/CFGuard tables |
| **8. `verified-mode`** (8. Verified Mode at Function Granularity, Cross-Path LLVM Attributes, Binary Attribution, Attestation, and LLVM-Free Sysroot) | `rustc_codegen_ssa`, `rustc_monomorphize`, `rustc_symbol_mangling`, `rustc_metadata` | 11 (+ 4) | 11 / 0 | 0 | [O8_] Two-phase ThinLTO import budgeting, primary-owner COMDAT generic deduplication (ComdatEquivCert), 1-bit SurvivingExternalRefs intersection, and post-inlining LiveClosed pruning reducing verified functions by 84.52% (4.78x faster verification); [K5_] Per-trait/per-symbol ScopedExportCert slicing WPO edit invalidation from 100% down to 0.0000%-0.3376% (0.11-1.35 ms re-check) paired with libanneal_procmacro_det.so LD_PRELOAD sandbox achieving 100%MirItemKey determinism across 10 runs |
| **9. `normal-compilation`** (9. Normal Compilation Modes: Wild Profiles, PGO, LTO, Debuginfo, Security Hardening, and Size Optimization) | `rustc_session`, `rustc_codegen_ssa`, `rustc_codegen_llvm`, `rustc_sanitizers` | 14 (+ 0) | 14 / 0 | 0 | [O5_] Hardware LBR sample-profile ingester (anneal-profgen + .anneal_site_map), machine-branch polarity un-flipping (71.4% inverted branches), and L1 minimum-cost circulation smoothing reducing LBR skid error by 80.5% and retaining 99.5%-100% PGO gain; [M1_] Direct assembler-free emission of DWARF v5 (.debug_info, .debug_line, .debug_loclists) on ELF/Mach-O and CodeView C13 (.debug$S, .debug$T) on COFF with RegAllocCert location lists and non-interference proofs (llvm-dwarfdump --verify 100% pass) |
| **10. `rustc-internals`** (10. rustc Internal Architecture, MIR Artifact Export, MIR Optimization Passes, Monomorphization, and Lowering) | `rustc_middle`, `rustc_mir_transform`, `rustc_monomorphize`, `rustc_const_eval`, `rustc_codegen_ssa`, `rustc_codegen_llvm`, `rustc_symbol_mangling` | 7 (+ 6) | 12 / 0 | 0 | [N3] 100% byte-for-byte profile invariance of Runtime(PostCleanup) MIR across -O0..-O3/-Os/-Oz, audit of mandatory pre-PostCleanup passes, and retirement of all 42 inner_optimized_mir passes via the O(N) MiniSSA canonicalizer; [L7_] Cross-profile MIR subsumption checker (checkProfileSubsumption) and Lean 4.34.1 theorems (CheckedImpliesWrapping_sound, DebugAssertImpliesRelease_sound, UnwindImpliesAbort_sound) certifying release builds from debug proofs |
| **11. `ecosystem-demand`** (11. Standard-Library Demand, Download-Weighted Ecosystem Census, and Runtime Hot Code Patterns) | `rustc_middle` | 4 (+ 0) | 4 / 0 | 0 | [E3] Empirical profiling of where CPU time goes across 8 Rust kernel categories, instruction mix, slice panic_bounds_check survival (40 at -O0; [U4] 412-site census of real-world LLVM -O3 LoopVectorize and SLPVectorizer idioms across core, alloc, std, E3, and P2 crates on x86-64/v2/v3/v4 and aarch64 (+neon/+sve) establishing 100% coverage by 6 schemas |
| **12. `proof-system-and-irs`** (12. Witness Proof System, Intermediate Representations, LLVM 23.1.1 IR Semantics, E-Graphs, and Prototype Soundness/Completeness) |  | 17 (+ 8) | 17 / 0 | 0 | [K3_] Arbitrary k-premise, m-variable sparse Farkas certificates (checkFarkasCertN_sound), modular BitVec-to-Int no-wrap bridges, and graduated relational freeze-set refinement (checkAEGraphGraduated_sound) verifying 80/80 corpus obligations in 8.07 ms; [K4_] RuleSynthV2 metaprogramming framework synthesizing 25 Class C/D memory-frame & fuel-indexed loop rules and 30 width-polymorphic BitVec w (8..128-bit) rules at 20.43x direct LOC compression (reducing full 185-rule compiler proofs from 26.30 kLOC to 2.62 kLOC, 10.04x total compression) |
| **13. `optimizer`** (13. Proof-Producing -O3 Optimizer: LLVM 23.1.1 Pipeline, Pass Ablation, Proof Obligations, TableGen Reuse, and Backend Candidates) | `rustc_codegen_llvm`, `rustc_llvm` | 22 (+ 2) | 24 / 0 | 0 | [M3_] 1-to-k tail-duplication simulation via reverse functional block projection (tail_dup_clone_sim) and cross-section .text <-> .text.unlikely 32-bit branch-relaxation veneers (+6.48% serde_json and +3.41% bytecode-dispatch speedups); [M4_] Call-sequence and diverging panic/cleanup thunk outlining (OutlinerUnwindThunkCert) with synthesized DWARF .eh_frame/LSDA and Windows .pdata/.xdata descriptors achieving up to 53.03% .text reduction and verified LIFO catch_unwind drops |
| **14. `validated-llvm`** (14. Optional Validated LLVM Tier: Black-Box Translation Validation vs. Derivation-Emitting LLVM Instrumentation) | `rustc_codegen_llvm` | 2 (+ 0) | 2 / 0 | 0 | [L1] Empirical Alive2-style SMT validation across 18 Rust LLVM IR archetypes (94.4% single scalar/memory pass acceptance, 66.7% LoopVectorize, 44.4% whole -O3) and 100%-accepting Runtime(PostCleanup) MIR-to-LLVM-IR SMT validator prototype; [L2] Pass-by-pass C++ mutation site inventory across all 131 LLVM 23.1.1 pass modules (574,990 LOC, 4,655 mutation sites) and effort estimate for derivation-emitting LLVM vs remark-guided validation |
| **15. `checker-substrate`** (15. Implementation Substrate, Lean 4 Native & Kernel Scaling, Independent Checkers, and Toolchain TCB Inventory) |  | 10 (+ 5) | 10 / 0 | 0 | [K1_] CSR flat ByteArray graph arenas and 61-LOC audited C11 word-slice shim (ByteWordSlice.lean, CSRGraph.lean) closing all remaining Lean 4.34.1 vs Rust 1.99.1 -O3 compiler-kernel gaps to 0.31x-1.20x (dom_ssa 0.54x, regalloc 0.93x, egraph_uf 1.20x); [K2_] Resident dual-engine Lean.Environment C++ kernel + safe-Rust nanoda_lib daemon (anneal-audit-daemon) eliminating the 180 ms .olean startup floor and verifying 245-step leaf edits in 0.393 ms P50 (1,949x speedup) with 0 KB RSS leak over 10,000 requests |
| **16. `validation`** (16. Compiler Validation Infrastructure: compiletest, Test Classification, Fuzzers, Crater, Target Execution, and Parity Baselines) | `rustc_driver` | 7 (+ 0) | 7 / 0 | 0 | [Q6] Statistical benchmark methodology accounting for --shuffle-sections code-layout noise (sigma_layout up to 20.57%) and multi-target -O0/-O2/-O3/-Os/-Oz/LTO/PGO speed and size baselines; [Q7] Concurrency and SIMD compiler testing harnesses (Loom, Shuttle, GenMC, Miri weak-memory multi-seed exploration, stdarch intrinsic-test, and hardware vector probes) |
| **17. `program-planning`** (17. Program Planning: Baseline, Corpora, Effort Models, Licensing, Qualification, Future Horizons, Roadmap, and Designer Dry Run) | `rustc_driver`, `rustc_middle` | 15 (+ 0) | 15 / 0 | 0 | [K6_] Per-signature AbiCompatHash preserving 100% of cached .rlib proofs across 1.99.1->1.100.0 on x86_64/aarch64 and 97.81% on i686, with synthesized 26-byte AbiBridgeThunk trampolines (bridge_thunk_sound) bridging the remaining 2.08% i686 XMM float-passing shifts; [K7_] Typeclass-projected OpenCoreMIR (HasRegLens/HasMemLens/HasBorrowLens + open CoreStmt Ext) reducing Layer0 state/AsyncDrop .olean invalidation from 100% (68/68 modules) to 2.86% (2/70 modules, 0/52 rule families) plus anneal_proof_repair.py repairing 8/8 interface changes |
| **Total Across All 17 Areas** | **78 `compiler/` Crates** | **179 (+ 67 = 246)** | **186 / 0** | **0** | **100% of all 186 program questions answered; 0 unrecorded external facts.** |

---

### 4. Complete Catalog of All 179 `compilers/verified-rustc` Packages by Design Area

Basis: source + derived

Table 4 lists the exact package directory names under `reports/<package>/` for
all **179 `compilers/verified-rustc` report packages**, organized by the 17
design areas in `support/roadmap_ledger.json`.

| Area ID | Count | Published `compilers/verified-rustc` Report Packages (`reports/<package>/`) |
| :--- | :--- | :--- |
| **1. `contract`** | 8 | `rustc-external-cli-json-and-backend-interface-contract`, `rustc-build-system-and-consumer-invocation-contracts`, `rustc-backend-dependent-observable-behaviors`, `rust-normative-authority-map-and-rustc-deviations`, `rustc-and-llvm-soundness-holes-and-miscompilation-census`, `rust-language-and-library-codegen-feature-inventory`, `miri-rust-analyzer-proc-macro-and-doctest-toolchain-contracts`, `unified-cargo-anneal-and-verified-rustc-diagnostic-mapping-and-ux` |
| **2. `end-to-end-theorem`** | 10 | `compiler-correctness-theorem-shapes-and-end-to-end-chains`, `compositional-correctness-linking-and-whole-program-optimization`, `observable-behavior-property-transfer-and-anneal-statement-forms`, `cross-prover-guarantee-composition-and-native-checker-soundness`, `end-to-end-verified-mir-to-isa-refinement-chain-and-seams`, `bidirectional-mir-minissa-refinement-and-anneal-vc-transport`, `anneal-spec-minissa-normalization-and-proof-compression`, `loop-invariant-and-recursive-spec-minissa-vc-transport`, `cross-dso-dynamic-linking-vtable-uniqueness-and-open-world-lto-contracts`, `tarjan-scc-fixpoint-summary-certificates-for-mutually-recursive-thinlto` |
| **3. `mir-and-aliasing`** | 15 | `rustc-mir-construct-semantics-miri-minirust-and-codegen`, `rust-aliasing-models-stacked-tree-minirust-and-llvm-attributes`, `rust-aliasing-models-ub-prevalence-and-llvm-optimization-value`, `rust-floating-point-semantics-llvm-lowering-and-isa-behavior`, `rust-allocation-provenance-and-stack-lifetime-semantics`, `rustc-layout-computation-target-datalayouts-and-parametricity`, `rust-postcleanup-mir-type-validity-and-range-invariant-catalog`, `rustc-statetransform-coroutines-async-gen-and-pin-mir-semantics`, `tree-borrows-protectors-stack-coloring-and-dead-store-elimination`, `tree-borrows-unwinding-cleanup-pads-two-phase-borrows-and-unsafecell`, `rustc-ctfe-globalalloc-promoted-constants-and-runtime-mir-equivalence`, `partial-sroa-escaping-fields-and-unsafecell-hybrid-memory-lenses`, `smart-pointer-and-custom-type-validity-invariant-propagation`, `self-referential-unpin-coroutine-field-slicing-and-sroa`, `tree-borrows-unwinding-store-sinking-and-protected-dse` |
| **4. `concurrency`** | 3 | `weak-memory-concurrency-models-hardware-mappings-and-optimizations`, `tier1-atomics-and-fences-instruction-lowering`, `weak-memory-hardware-litmus-testing-x86-and-aarch64` |
| **5. `platform-conventions`** | 17 | `tier1-calling-conventions-fnabi-and-llvm-lowering`, `abi-cross-testing-matrix-rustc-llvm-cranelift-gcc-clang`, `unwinding-on-elf-and-macho-targets`, `unwinding-on-windows-targets-and-32bit-seh`, `rust-thread-local-storage-models-and-runtime-contracts`, `rust-stack-discipline-probes-red-zones-and-overflow`, `rust-program-startup-runtime-objects-and-entry-state`, `rustc-object-files-sections-symbols-comdats-and-relocations`, `rustc-static-linking-archive-formats-and-linker-driver`, `rustc-dynamic-linking-loader-contracts-and-code-signing`, `tier1-linux-hosted-cross-compilation-recipes-and-sysroots`, `tier1-default-codegen-settings-and-target-options`, `os-syscall-interfaces-asynchronous-signals-and-environment-models`, `tier1-exhaustive-procedural-abi-differential-campaign-and-fixes`, `lean-fnabi-marshaling-refinement-sysv64-win64-aapcs64-i686`, `bit-level-sub-eightbyte-packing-hfa-and-c-variadic-fnabi-refinement`, `cross-platform-bit-for-bit-reproducible-executable-linking-and-codesign` |
| **6. `intrinsics-and-assembly`** | 9 | `rustc-intrinsics-simd-and-arch-semantic-sources`, `vendor-intrinsic-specifications-stdarch-verification-and-lean-generation`, `llvm-instruction-selection-fallbacks-and-libcall-contracts`, `target-features-implications-detection-and-abi-effects`, `rustc-inline-assembly-specification-llvm-lowering-and-assembler-syntax`, `rust-ecosystem-inline-assembly-global-asm-and-naked-function-census`, `machine-code-verification-frameworks-and-assembly-contracts`, `portable-simd-repr-simd-legalization-and-cross-arch-cost-certificates`, `verified-builtin-inline-asm-template-parser-and-direct-encoder` |
| **7. `isa-models`** | 8 | `formal-isa-models-x86-64-i386-and-aarch64-coverage`, `isa-model-hardware-validation-divergences-errata-and-resources`, `llvm-compiled-rust-instruction-and-addressing-mode-frequencies`, `verified-assemblers-encoders-linkers-and-object-format-models`, `direct-verified-object-section-and-relocation-emitter-v0`, `hardware-errata-mitigations-linker-veneers-and-vzeroupper-verification`, `decidable-machine-code-well-formedness-and-errata-byte-validator`, `post-link-executable-validator-relocations-veneers-erratum-843419-and-gcs` |
| **8. `verified-mode`** | 11 | `rustc-codegen-backend-routing-and-mixed-backend-interoperability`, `rustc-llvm-ir-attributes-metadata-and-cross-path-obligations`, `rustc-binary-origin-attribution-gc-sections-and-icf-soundness`, `binary-evidence-packaging-provenance-attestations-and-rustc-reproducibility`, `rustc-llvm-free-sysroot-cranelift-gcc-and-host-tools-audit`, `verified-pre-proof-reachability-pruning-and-address-safe-icf`, `incremental-function-and-thinlto-summary-proof-cache-architecture`, `deterministic-distributed-verification-and-remote-build-cache-integration`, `ctfe-const-eval-select-and-reflection-intrinsic-verification-contracts`, `two-phase-thinlto-import-budgeting-generic-dedup-and-post-inline-pruning`, `scoped-exportlist-invalidation-slicing-and-proc-macro-determinism-sandbox` |
| **9. `normal-compilation`** | 14 | `cargo-profile-and-compiler-flag-census-in-the-wild`, `rustc-pgo-mechanics-heuristics-value-and-ir-portability`, `rustc-lto-mechanics-symbol-preservation-and-performance-value`, `rustc-dwarf-codeview-debuginfo-emission-and-debugger-contracts`, `rustc-tier1-security-hardening-and-mitigation-codegen`, `rustc-size-optimized-compilation-parity-and-transformations`, `mutation-resilient-polarity-safe-ir-portable-pgo`, `value-profile-specialization-and-hybridtrace-guard-certificates`, `cross-crate-thinlto-anneal-mir-summary-certificates-and-import-replay`, `whole-program-devirt-dae-and-globalopt-exportlist-certificates`, `unwind-preserving-pic-safe-machine-outliner-all-tier1-targets`, `verified-cfi-cet-bti-pac-cfguard-and-speculative-hardening`, `hardware-lbr-autofdo-sample-profile-ingestion-and-circulation-smoothing`, `direct-verified-dwarf-v5-and-codeview-debug-section-emitter` |
| **10. `rustc-internals`** | 7 | `rustc-baseline-repository-map-and-internal-interfaces`, `rustc-mir-artifact-export-settings-and-proof-binding`, `rustc-mir-optimization-passes-semantics-soundness-and-value`, `rustc-monomorphization-vtables-statics-symbols-and-cgu-partitioning`, `rustc-mir-to-llvm-lowering-and-runtime-visible-semantics`, `rustc-pre-postcleanup-lowerings-and-minissa-canonicalizer-replacement`, `mir-profile-subsumption-overflow-checks-debug-assertions-and-panic-modes` |
| **11. `ecosystem-demand`** | 4 | `rustc-standard-library-codegen-demand-per-target`, `crates-io-download-weighted-codegen-demand-census`, `where-time-goes-in-rust-programs-hot-patterns-and-instruction-mix`, `rust-llvm-o3-loop-and-slp-vectorization-idiom-census` |
| **12. `proof-system-and-irs`** | 17 | `proof-producing-compilation-and-certificate-formats-quantitative-survey`, `relational-logics-simulation-techniques-and-completeness-for-compiler-derivations`, `mechanized-compiler-ir-semantics-poison-provenance-and-machine-frames`, `llvm-ir-baseline-formal-semantics-and-ambiguities`, `llvm-o3-derivation-formats-expressiveness-and-checking-cost`, `lean-derivation-checker-soundness-and-completeness-prototype`, `rustc-build-ir-and-pass-transformation-volume-statistics`, `equality-saturation-with-proofs-egraphs-aegraphs-and-refinement-rewriting`, `verified-side-condition-decision-procedures-and-certificate-checkers`, `hybridtrace-vectorization-slp-and-loop-certificate-library`, `verified-regalloc2-spill-and-parallel-move-certificate-checker`, `unified-farkas-knownbits-and-aegraph-side-condition-certificates`, `lean-metaprogrammed-rule-soundness-and-completeness-synthesis`, `ordered-floating-point-simd-reductions-and-rfc3514-reassoc-certificates`, `sub-register-lane-aliasing-and-readonly-load-rematerialization-in-regalloccert`, `multi-premise-sparse-farkas-and-freeze-set-refinement-certificates`, `metaprogrammed-class-d-loop-memory-framing-and-width-polymorphic-bitvec-rules` |
| **13. `optimizer`** | 22 | `rustc-llvm-pass-pipelines-and-configuration`, `llvm-pass-ablation-speed-and-size-on-rust-code`, `llvm-scalar-memory-and-loop-optimization-proof-obligations`, `llvm-interprocedural-lto-and-codegen-optimization-obligations`, `verified-and-validated-compiler-optimization-precedents`, `candidate-optimizers-llvm-cranelift-and-gcc-backend-comparison`, `proven-baseline-compiler-candidates-and-reusable-verified-backends`, `llvm-tablegen-isa-extraction-and-verified-selector-reuse`, `performance-models-and-microarchitectural-tuning-data`, `type-validity-seeded-range-and-farkas-bounds-check-elimination`, `coroutine-state-machine-optimization-and-hybridtrace-scaling`, `untrusted-llvm-optimization-oracle-and-certificate-replay-architecture`, `llvm-oracle-guided-minissa-minimach-replay-prototype-and-parity`, `oracle-hint-drift-alignment-and-fallback-resilience`, `x86-avx512-short-loop-regression-and-vector-width-profitability`, `microarchitectural-code-layout-variance-dsb-jcc-and-btb-dissection`, `verified-minimach-ext-tsp-layout-and-loop-jcc-alignment`, `nonlinear-bitwise-mask-modulo-and-lookup-table-bounds-certificates`, `uninstrumented-instcombine-and-dagcombiner-egraph-chain-reconstruction`, `debuginfo-free-weisfeiler-leman-cfg-and-def-use-oracle-alignment`, `verified-tail-duplication-hot-cold-splitting-and-branch-relaxation`, `call-and-unwind-landing-pad-machine-outliner-with-lsda-synthesis` |
| **14. `validated-llvm`** | 2 | `black-box-translation-validation-alive2-and-mir-to-llvm-on-rust`, `llvm-derivation-emission-instrumentation-architecture-and-cost` |
| **15. `checker-substrate`** | 10 | `lean-native-compilation-pipeline-runtime-and-trust-surface`, `lean-kernel-derivation-scale-checking-and-reflection-throughput`, `independent-proof-checkers-and-smaller-trusted-computing-bases`, `compiler-substrate-benchmarks-lean-rust-and-ocaml`, `verified-rustc-delivered-toolchain-trusted-component-inventory`, `lean-large-isa-and-compiler-semantics-scaling`, `lean-unboxed-bytearray-bitset-and-soa-compiler-substrate-bridge`, `lean-kernel-natgmp-limb-tuning-and-nanoda-parallel-audit-throughput`, `csr-bytearray-arena-graphs-and-extern-primitives-for-1x-lean-rust-parity`, `persistent-mmap-lean-kernel-and-nanoda-audit-daemon-for-submillisecond-checks` |
| **16. `validation`** | 7 | `rustc-compiletest-bootstrap-and-alternate-backend-test-mechanics`, `rustc-test-suite-machine-readable-classification`, `compiler-differential-testing-fuzzing-reduction-and-bug-records`, `ecosystem-scale-testing-crater-self-hosting-and-flakiness`, `tier1-target-test-execution-emulators-and-combinatorial-coverage`, `rustc-benchmark-methodology-and-speed-size-baselines`, `concurrency-and-simd-compiler-testing-tools-and-harnesses` |
| **17. `program-planning`** | 15 | `rustc-baseline-toolchain-selection-and-manifest`, `rustc-experimental-corpora-and-harness-conventions`, `verified-rustc-research-map-and-open-question-ledger`, `verified-compiler-effort-precedents-and-agent-proof-productivity`, `compiler-isa-sdk-licensing-trademarks-and-upstream-governance`, `compiler-qualification-assurance-cases-and-deviation-policies`, `verified-rust-frontend-approaches-trait-solver-polonius-and-thir-lowering`, `safe-rust-ub-freedom-soundness-and-standard-library-verification`, `cross-language-lto-linker-plugin-bitcode-and-llvm-ir-semantics`, `verified-rustc-designer-dry-run-and-gap-analysis`, `rustc-multi-release-mir-abi-drift-and-version-isolated-adapter`, `automated-toolchain-table-regeneration-and-mir-minissa-upgrade-validator`, `compiler-upgrade-soundness-quarantine-and-proof-invalidation-bounds`, `cross-release-abi-compatibility-fingerprinting-and-automatic-thunk-bridge`, `typeclass-insulated-layer0-coremir-and-automated-lean-proof-repair` |

## Boundaries

- **Point-in-time baseline (`Rust 1.99.1`, `LLVM 23.1.1`, `Lean 4 v4.34.1`) with multi-release adapter and ABI thunk coverage:**
  All 186 answered questions and 179 `compilers/verified-rustc` packages are
  anchored to the pinned `1.99.1` / `23.1.1` / `v4.34.1` revisions in Table 2,
  with multi-release drift (`1.98.1` through `1.100.0` and `nightly-2026-11-12`)
  explicitly bridged by `CoreMIR`, `OpenCoreMIR`, `AbiCompatHash` +
  `AbiBridgeThunk`, and `regen_toolchain_tables.py` in Area 17
  (`program-planning`).

## Evidence

- **Compiler crate DAG:** Extracted directly from the 78 `compiler/*/Cargo.toml`
  manifests in `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`.
- **Normative specification revisions:** Verified via `git rev-parse HEAD` across
  the nine upstream repositories listed in Table 2.
- **Preserved support artifacts:**
  - `support/roadmap_ledger.json` — machine-readable 78-crate compiler DAG by
    depth and the 17-area mapping of governing crates, normative sources, topic
    queries, all 179 `compilers/verified-rustc` packages (plus 67 foundational
    packages), and all 186 answered program questions (`0` open questions).
  - `support/verify_roadmap_ledger.py` — automated verification script checking
    that all 17 areas, 186 questions, and 179 `compilers/verified-rustc`
    packages in `CATALOG.json` are completely indexed and answered.
  - `support/query_roadmap.py` — standalone CLI wrapper to query coverage by
    design area.

## Revalidation

To verify that all 17 design areas, 186 program questions, and 179
`compilers/verified-rustc` packages in `CATALOG.json` are indexed with zero
unanswered questions, run:

```console
python3 reports/verified-rustc-research-map-and-open-question-ledger/support/verify_roadmap_ledger.py
python3 reports/verified-rustc-research-map-and-open-question-ledger/support/query_roadmap.py
```
