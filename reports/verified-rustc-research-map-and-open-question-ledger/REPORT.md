# Verified Drop-In Rust Compiler Research Map, Crate Architecture, and Question Ledger

## Summary

Designing, verifying, and validating a drop-in replacement for **Rust 1.99.1**
(`rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67`, bundled **LLVM
23.1.1** at `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, **Anneal** at
`7abf0691c404393e3e4fc26eb3d4094e3170b5c7`, and **Lean 4 v4.34.1** at
`5045d0056413266e57c625dcd7c365b10e377c52`) spans **17 architectural design
areas** and **154 technical research questions**:

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
3. **Complete 17-area coverage map and closed 154-question ledger (`0` open questions):**
   `support/roadmap_ledger.json`, `support/verify_roadmap_ledger.py`, and
   `support/query_roadmap.py` index all **147 published
   `compilers/verified-rustc` report packages** (alongside **67 foundational
   Anneal, MiniRust, and Lean 4 packages**, totaling **214 mapped packages**)
   across all 17 design areas. All **154 program research questions** (`114`
   from Waves 0–4 plus `40` from Wave 5 across `N1`–`N10`, `U1`–`U10`,
   `B1`–`B10`, and `X1`–`X10`) are **answered in full (`154` answered fully, `0`
   answered partly, `0` open)**, and the end-to-end designer dry run
   (`verified-rustc-designer-dry-run-and-gap-analysis`) confirms that zero
   unrecorded external facts remain across the 13 architectural decision domains
   and 31 research goals.

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

### 3. Complete 17-Area Coverage Summary (`147` `compilers/verified-rustc` Packages, `154 / 154` Questions Answered)

Basis: source + execution + derived

Table 3 summarizes all **17 design areas** of the verified drop-in `rustc`
replacement, mapping each area to its governing `rustc 1.99.1` crates, count of
`compilers/verified-rustc` packages (plus foundational Anneal/MiniRust/Lean 4
packages), and closed question counts (`154` answered in full, `0` partly
answered, `0` open).

| Area ID & Title | Governing `rustc 1.99.1` Crates | `verified-rustc` Packages (+ Foundational) | Answered (Full / Part) | Open Questions | Representative Wave 0–5 Architectural and Quantitative Findings |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **1. `contract`** (1. Drop-In Compiler Contract, CLI/JSON Surfaces, Build Systems, Tooling, and Deviation Policy) | `rustc_driver`, `rustc_driver_impl`, `rustc_interface`, `rustc_session`, `rustc_errors`, `rustc_feature`, `rustc_lint` | 7 (+ 4) | 7 / 0 | 0 | [C6] Inventory of all 1,482 language, library, and rustc_* features in 1.99.1 and the 219 features with MIR, layout, ABI, or codegen impact (plus 469 sysroot #![feature] gates); [C7] Miri (20 rustc_private crates, -Zmiri-tree-borrows), rust-analyzer, proc-macro server ABI v2 (format version 10), and rustdoc --test-builder integration contracts |
| **2. `end-to-end-theorem`** (2. End-to-End Compiler Correctness Theorem, Compositional Linking, Cross-Prover Soundness, and Five-Link Prototype) | `rustc_middle`, `rustc_codegen_ssa` | 7 (+ 8) | 7 / 0 | 0 | [N1] Bidirectional Runtime(PostCleanup) MIR <-> MiniSSA refinement (BisimExact vs GuardedBisim vs RefinesOnly) and backward Anneal VC transport (verifyMirViaMiniSSA_sound, 0 sorryAx, 0 TCB expansion); [N2] Place-to-SSA #[anneal_spec] contract substitution lens (Sigma_spec) across Mem2Reg, SROA, and Inlining achieving 10.79x symbolic AST reduction, 6.19x proof LOC compression, and 10.68x kernel checking speedup |
| **3. `mir-and-aliasing`** (3. MIR Operational Semantics, Aliasing Models, Allocation, Provenance, Floating-Point, and Layout) | `rustc_middle`, `rustc_abi`, `rustc_const_eval`, `rustc_mir_dataflow`, `rustc_ty_utils` | 11 (+ 15) | 11 / 0 | 0 | [N9] Tree Borrows protector release on panic=unwind cleanup landing pads (store-sinking compensation vs sret dead_on_unwind), two-phase borrows (ReservedIM), and byte-precise UnsafeCell projections; [N10] CTFE InterpCx evaluation, 5 GlobalAlloc variants (cyclic static provenance graphs, uninitialized padding masks, GlobalAlloc::TypeId), promoted constants, and runtime PostCleanup MIR equivalence |
| **4. `concurrency`** (4. Concurrency Theory, Relaxed Memory Models, Tier 1 Atomic Lowerings, and Hardware Litmus Validation) | `rustc_middle`, `rustc_codegen_ssa`, `rustc_codegen_llvm` | 3 (+ 4) | 3 / 0 | 0 | [S14] Exact instruction sequences emitted by rustc 1.99.1 and LLVM 23.1.1 for atomic loads, stores, RMWs, cmpxchg, and fences across all 8 Tier 1 targets (including i686 cmpxchg8b and AArch64 +lse/+rcpc/+outline-atomics); [S15] Empirical hardware weak-memory litmus execution (2.70e6 barrier-synchronized runs across 9 families on x86_64 plus AArch64 assembly verification) cross-checked against herd7 7.58 |
| **5. `platform-conventions`** (5. Tier 1 Platform Conventions: Calling Conventions, Unwinding, TLS, Stack Discipline, Startup, Object Formats, and Linking) | `rustc_target`, `rustc_abi`, `rustc_codegen_ssa`, `rustc_codegen_llvm`, `rustc_sanitizers` | 15 (+ 5) | 15 / 0 | 0 | [B6] 256-archetype procedural ABI differential campaign across all 8 Tier 1 targets resolving 8 edge cases (MinGW f128 XMM0 vs sret, SysV 6th-GPR %r9 u128 straddle backfilling, AAPCS64 u128 alignment, i686 rust-cold SSE); [B7] Executable Lean 4.34.1 FnAbi classification (100% agreement across 2,048 Tier 1 target-signature pairs) and kernel-checked bidirectional caller/callee marshaling refinement across SysV64, Win64, AAPCS64, and i686 |
| **6. `intrinsics-and-assembly`** (6. Compiler Intrinsics, Vendor SIMD Specifications, Target Features, and Inline Assembly) | `rustc_middle`, `rustc_codegen_ssa`, `rustc_target`, `rustc_builtin_macros` | 7 (+ 2) | 7 / 0 | 0 | [M6] Empirical census of inline assembly, global_asm!, #[unsafe(naked)], and external C/assembly objects across sysroot, Linux kernel Rust, and crates.io; [M7] Machine-code verification frameworks (Islaris, s2n-bignum HOL Light, Jasmin, Bedrock2, CakeML) and frame-preserving vs system-state assembly contracts |
| **7. `isa-models`** (7. Formal ISA Models (x86-64, i386, AArch64), Hardware Validation, Instruction Frequencies, and Verified Assemblers/Linkers) | `rustc_target` | 7 (+ 4) | 7 / 0 | 0 | [B8] Mechanized silicon errata mitigations (Intel SKX102 32B JCC padding, Arm Cortex-A53 835769 MAC hazard and 843419 page-end ADRP linker veneers) and x86 AVX-to-SSE vzeroupper transition verification; [B10] Decidable linear-time machine-code byte validator (checkBinaryWF_sound, 78.67 MB/s across 2,494 Tier 1 sysroot .o files) checking canonical decoding, 16B stack alignment, stack probes, red zones, vzeroupper, errata, and CFI |
| **8. `verified-mode`** (8. Verified Mode at Function Granularity, Cross-Path LLVM Attributes, Binary Attribution, Attestation, and LLVM-Free Sysroot) | `rustc_codegen_ssa`, `rustc_monomorphize`, `rustc_symbol_mangling`, `rustc_metadata` | 8 (+ 4) | 8 / 0 | 0 | [X6] Three-tier SHA-256 Merkle proof cache (MirItemKey, CalleeSummaryKey import cone, CompiledArtifactKey) reducing ThinLTO re-verification to 0.00% on comment edits and 0.0042% on leaf function edits; [X7] 100% bit-for-bit deterministic .anneal-mir/.anneal-cert/.olean generation across paths and thread counts with zero-patch Cargo/sccache/Bazel/Buck2 caching and --Zanneal-check=defer REAPI v2 execution |
| **9. `normal-compilation`** (9. Normal Compilation Modes: Wild Profiles, PGO, LTO, Debuginfo, Security Hardening, and Size Optimization) | `rustc_session`, `rustc_codegen_ssa`, `rustc_codegen_llvm`, `rustc_sanitizers` | 12 (+ 0) | 12 / 0 | 0 | [B5] Diagnosis of LLVM 23.1.1 MachineOutliner bugs on Win64 SEH, Win32 FPO, i686 PIC, and WinARM64, and verification of unwind-preserving, PIC-safe VerifiedMachineOutliner across all 8 Tier 1 targets; [B9] Mechanized hardware control-flow integrity (Intel CET IBT/SHSTK, Arm64 BTI/PAC-RET/GCS, Windows CFGuard/EHCont) and Spectre v2 / SLS / stack-protector hardening across all 8 Tier 1 targets |
| **10. `rustc-internals`** (10. rustc Internal Architecture, MIR Artifact Export, MIR Optimization Passes, Monomorphization, and Lowering) | `rustc_middle`, `rustc_mir_transform`, `rustc_monomorphize`, `rustc_const_eval`, `rustc_codegen_ssa`, `rustc_codegen_llvm`, `rustc_symbol_mangling` | 6 (+ 6) | 11 / 0 | 0 | [R7] Runtime-visible lowering of panics (panic_fmt, nounwind cleanup pads, double-panic abort), allocator shims (__rust_alloc), and process entry points (lang_start); [N3] 100% byte-for-byte profile invariance of Runtime(PostCleanup) MIR across -O0..-O3/-Os/-Oz, audit of mandatory pre-PostCleanup passes, and retirement of all 42 inner_optimized_mir passes via the O(N) MiniSSA canonicalizer |
| **11. `ecosystem-demand`** (11. Standard-Library Demand, Download-Weighted Ecosystem Census, and Runtime Hot Code Patterns) | `rustc_middle` | 4 (+ 0) | 4 / 0 | 0 | [E3] Empirical profiling of where CPU time goes across 8 Rust kernel categories, instruction mix, slice panic_bounds_check survival (40 at -O0; [U4] 412-site census of real-world LLVM -O3 LoopVectorize and SLPVectorizer idioms across core, alloc, std, E3, and P2 crates on x86-64/v2/v3/v4 and aarch64 (+neon/+sve) establishing 100% coverage by 6 schemas |
| **12. `proof-system-and-irs`** (12. Witness Proof System, Intermediate Representations, LLVM 23.1.1 IR Semantics, E-Graphs, and Prototype Soundness/Completeness) |  | 13 (+ 8) | 13 / 0 | 0 | [X2] Unified PoisonOr side-condition certificate library in Lean 4.34.1 combining Farkas linear arithmetic, KnownBits/WrappingRange abstract domains, and freeze-guarded let-DAG AEGraphCert (1.71x kernel speedup); [X5] Four-class taxonomy of all 52 -O3 rule families (185 constructors) and Lean 4.34.1 metaprogrammed rule soundness/completeness synthesis (MetaRuleSynth, 12.42x direct / 5.48x compiler-wide proof KLOC reduction) |
| **13. `optimizer`** (13. Proof-Producing -O3 Optimizer: LLVM 23.1.1 Pipeline, Pass Ablation, Proof Obligations, TableGen Reuse, and Backend Candidates) | `rustc_codegen_llvm`, `rustc_llvm` | 17 (+ 2) | 19 / 0 | 0 | [B1] Microarchitectural dissection of Q6's 19.60% serde_json bimodal split, 69.97% regex-automata spread, and 7.88x .eh_frame_hdr slowdown to 32B JCC/DSB crossings, 4 KiB BTB aliasing, and missing -Zfunction-sections; [B2] Verified MiniMach Ext-TSP block placement, .text.unlikely splitting, and 32B loop/JCC NOP alignment (VerifiedLayoutPass.lean) collapsing 16-seed layout CV from 20.57% to <=1.42% and boosting speed by +6.8%/+14.9% |
| **14. `validated-llvm`** (14. Optional Validated LLVM Tier: Black-Box Translation Validation vs. Derivation-Emitting LLVM Instrumentation) | `rustc_codegen_llvm` | 2 (+ 0) | 2 / 0 | 0 | [L1] Empirical Alive2-style SMT validation across 18 Rust LLVM IR archetypes (94.4% single scalar/memory pass acceptance, 66.7% LoopVectorize, 44.4% whole -O3) and 100%-accepting Runtime(PostCleanup) MIR-to-LLVM-IR SMT validator prototype; [L2] Pass-by-pass C++ mutation site inventory across all 131 LLVM 23.1.1 pass modules (574,990 LOC, 4,655 mutation sites) and effort estimate for derivation-emitting LLVM vs remark-guided validation |
| **15. `checker-substrate`** (15. Implementation Substrate, Lean 4 Native & Kernel Scaling, Independent Checkers, and Toolchain TCB Inventory) |  | 8 (+ 5) | 8 / 0 | 0 | [X3] Diagnosis of 4 Lean 4.34.1 LCNF/C-runtime boxing bottlenecks and verified unboxed ByteArray BitSet64 + Struct-of-Arrays bridge shrinking the 28.34x regalloc liveness gap to 1.18x (1.24x 6-kernel geomean); [X4] Balanced binary-halving GMP limb unpacking (NatBinarySplit at B*=512 bits |
| **16. `validation`** (16. Compiler Validation Infrastructure: compiletest, Test Classification, Fuzzers, Crater, Target Execution, and Parity Baselines) | `rustc_driver` | 7 (+ 0) | 7 / 0 | 0 | [Q6] Statistical benchmark methodology accounting for --shuffle-sections code-layout noise (sigma_layout up to 20.57%) and multi-target -O0/-O2/-O3/-Os/-Oz/LTO/PGO speed and size baselines; [Q7] Concurrency and SIMD compiler testing harnesses (Loom, Shuttle, GenMC, Miri weak-memory multi-seed exploration, stdarch intrinsic-test, and hardware vector probes) |
| **17. `program-planning`** (17. Program Planning: Baseline, Corpora, Effort Models, Licensing, Qualification, Future Horizons, Roadmap, and Designer Dry Run) | `rustc_driver`, `rustc_middle` | 13 (+ 0) | 13 / 0 | 0 | [X9] Automated regeneration (regen_toolchain_tables.py) of Tier 1 TargetSpec, #[rustc_intrinsic], and TableGen tables with 100% cross-release (1.99.1 vs 1.100.0) CoreMIR digest and bv_decide equivalence validation; [X10] 5-layer opaque .olean firewall limiting upgrade invalidation to 11.8%-17.6% of modules and zero-sorryAx Soundness Quarantine protocol (applyWithQuarantine_sound) with automatic baseline fallback |
| **Total Across All 17 Areas** | **78 `compiler/` Crates** | **147 (+ 67 = 214)** | **154 / 0** | **0** | **100% of all 154 program questions answered; 0 unrecorded external facts.** |

---

### 4. Complete Catalog of All 147 `compilers/verified-rustc` Packages by Design Area

Basis: source + derived

Table 4 lists the exact package directory names under `reports/<package>/` for
all **147 `compilers/verified-rustc` report packages**, organized by the 17
design areas in `support/roadmap_ledger.json`.

| Area ID | Count | Published `compilers/verified-rustc` Report Packages (`reports/<package>/`) |
| :--- | :--- | :--- |
| **1. `contract`** | 7 | `rustc-external-cli-json-and-backend-interface-contract`, `rustc-build-system-and-consumer-invocation-contracts`, `rustc-backend-dependent-observable-behaviors`, `rust-normative-authority-map-and-rustc-deviations`, `rustc-and-llvm-soundness-holes-and-miscompilation-census`, `rust-language-and-library-codegen-feature-inventory`, `miri-rust-analyzer-proc-macro-and-doctest-toolchain-contracts` |
| **2. `end-to-end-theorem`** | 7 | `compiler-correctness-theorem-shapes-and-end-to-end-chains`, `compositional-correctness-linking-and-whole-program-optimization`, `observable-behavior-property-transfer-and-anneal-statement-forms`, `cross-prover-guarantee-composition-and-native-checker-soundness`, `end-to-end-verified-mir-to-isa-refinement-chain-and-seams`, `bidirectional-mir-minissa-refinement-and-anneal-vc-transport`, `anneal-spec-minissa-normalization-and-proof-compression` |
| **3. `mir-and-aliasing`** | 11 | `rustc-mir-construct-semantics-miri-minirust-and-codegen`, `rust-aliasing-models-stacked-tree-minirust-and-llvm-attributes`, `rust-aliasing-models-ub-prevalence-and-llvm-optimization-value`, `rust-floating-point-semantics-llvm-lowering-and-isa-behavior`, `rust-allocation-provenance-and-stack-lifetime-semantics`, `rustc-layout-computation-target-datalayouts-and-parametricity`, `rust-postcleanup-mir-type-validity-and-range-invariant-catalog`, `rustc-statetransform-coroutines-async-gen-and-pin-mir-semantics`, `tree-borrows-protectors-stack-coloring-and-dead-store-elimination`, `tree-borrows-unwinding-cleanup-pads-two-phase-borrows-and-unsafecell`, `rustc-ctfe-globalalloc-promoted-constants-and-runtime-mir-equivalence` |
| **4. `concurrency`** | 3 | `weak-memory-concurrency-models-hardware-mappings-and-optimizations`, `tier1-atomics-and-fences-instruction-lowering`, `weak-memory-hardware-litmus-testing-x86-and-aarch64` |
| **5. `platform-conventions`** | 15 | `tier1-calling-conventions-fnabi-and-llvm-lowering`, `abi-cross-testing-matrix-rustc-llvm-cranelift-gcc-clang`, `unwinding-on-elf-and-macho-targets`, `unwinding-on-windows-targets-and-32bit-seh`, `rust-thread-local-storage-models-and-runtime-contracts`, `rust-stack-discipline-probes-red-zones-and-overflow`, `rust-program-startup-runtime-objects-and-entry-state`, `rustc-object-files-sections-symbols-comdats-and-relocations`, `rustc-static-linking-archive-formats-and-linker-driver`, `rustc-dynamic-linking-loader-contracts-and-code-signing`, `tier1-linux-hosted-cross-compilation-recipes-and-sysroots`, `tier1-default-codegen-settings-and-target-options`, `os-syscall-interfaces-asynchronous-signals-and-environment-models`, `tier1-exhaustive-procedural-abi-differential-campaign-and-fixes`, `lean-fnabi-marshaling-refinement-sysv64-win64-aapcs64-i686` |
| **6. `intrinsics-and-assembly`** | 7 | `rustc-intrinsics-simd-and-arch-semantic-sources`, `vendor-intrinsic-specifications-stdarch-verification-and-lean-generation`, `llvm-instruction-selection-fallbacks-and-libcall-contracts`, `target-features-implications-detection-and-abi-effects`, `rustc-inline-assembly-specification-llvm-lowering-and-assembler-syntax`, `rust-ecosystem-inline-assembly-global-asm-and-naked-function-census`, `machine-code-verification-frameworks-and-assembly-contracts` |
| **7. `isa-models`** | 7 | `formal-isa-models-x86-64-i386-and-aarch64-coverage`, `isa-model-hardware-validation-divergences-errata-and-resources`, `llvm-compiled-rust-instruction-and-addressing-mode-frequencies`, `verified-assemblers-encoders-linkers-and-object-format-models`, `direct-verified-object-section-and-relocation-emitter-v0`, `hardware-errata-mitigations-linker-veneers-and-vzeroupper-verification`, `decidable-machine-code-well-formedness-and-errata-byte-validator` |
| **8. `verified-mode`** | 8 | `rustc-codegen-backend-routing-and-mixed-backend-interoperability`, `rustc-llvm-ir-attributes-metadata-and-cross-path-obligations`, `rustc-binary-origin-attribution-gc-sections-and-icf-soundness`, `binary-evidence-packaging-provenance-attestations-and-rustc-reproducibility`, `rustc-llvm-free-sysroot-cranelift-gcc-and-host-tools-audit`, `verified-pre-proof-reachability-pruning-and-address-safe-icf`, `incremental-function-and-thinlto-summary-proof-cache-architecture`, `deterministic-distributed-verification-and-remote-build-cache-integration` |
| **9. `normal-compilation`** | 12 | `cargo-profile-and-compiler-flag-census-in-the-wild`, `rustc-pgo-mechanics-heuristics-value-and-ir-portability`, `rustc-lto-mechanics-symbol-preservation-and-performance-value`, `rustc-dwarf-codeview-debuginfo-emission-and-debugger-contracts`, `rustc-tier1-security-hardening-and-mitigation-codegen`, `rustc-size-optimized-compilation-parity-and-transformations`, `mutation-resilient-polarity-safe-ir-portable-pgo`, `value-profile-specialization-and-hybridtrace-guard-certificates`, `cross-crate-thinlto-anneal-mir-summary-certificates-and-import-replay`, `whole-program-devirt-dae-and-globalopt-exportlist-certificates`, `unwind-preserving-pic-safe-machine-outliner-all-tier1-targets`, `verified-cfi-cet-bti-pac-cfguard-and-speculative-hardening` |
| **10. `rustc-internals`** | 6 | `rustc-baseline-repository-map-and-internal-interfaces`, `rustc-mir-artifact-export-settings-and-proof-binding`, `rustc-mir-optimization-passes-semantics-soundness-and-value`, `rustc-monomorphization-vtables-statics-symbols-and-cgu-partitioning`, `rustc-mir-to-llvm-lowering-and-runtime-visible-semantics`, `rustc-pre-postcleanup-lowerings-and-minissa-canonicalizer-replacement` |
| **11. `ecosystem-demand`** | 4 | `rustc-standard-library-codegen-demand-per-target`, `crates-io-download-weighted-codegen-demand-census`, `where-time-goes-in-rust-programs-hot-patterns-and-instruction-mix`, `rust-llvm-o3-loop-and-slp-vectorization-idiom-census` |
| **12. `proof-system-and-irs`** | 13 | `proof-producing-compilation-and-certificate-formats-quantitative-survey`, `relational-logics-simulation-techniques-and-completeness-for-compiler-derivations`, `mechanized-compiler-ir-semantics-poison-provenance-and-machine-frames`, `llvm-ir-baseline-formal-semantics-and-ambiguities`, `llvm-o3-derivation-formats-expressiveness-and-checking-cost`, `lean-derivation-checker-soundness-and-completeness-prototype`, `rustc-build-ir-and-pass-transformation-volume-statistics`, `equality-saturation-with-proofs-egraphs-aegraphs-and-refinement-rewriting`, `verified-side-condition-decision-procedures-and-certificate-checkers`, `hybridtrace-vectorization-slp-and-loop-certificate-library`, `verified-regalloc2-spill-and-parallel-move-certificate-checker`, `unified-farkas-knownbits-and-aegraph-side-condition-certificates`, `lean-metaprogrammed-rule-soundness-and-completeness-synthesis` |
| **13. `optimizer`** | 17 | `rustc-llvm-pass-pipelines-and-configuration`, `llvm-pass-ablation-speed-and-size-on-rust-code`, `llvm-scalar-memory-and-loop-optimization-proof-obligations`, `llvm-interprocedural-lto-and-codegen-optimization-obligations`, `verified-and-validated-compiler-optimization-precedents`, `candidate-optimizers-llvm-cranelift-and-gcc-backend-comparison`, `proven-baseline-compiler-candidates-and-reusable-verified-backends`, `llvm-tablegen-isa-extraction-and-verified-selector-reuse`, `performance-models-and-microarchitectural-tuning-data`, `type-validity-seeded-range-and-farkas-bounds-check-elimination`, `coroutine-state-machine-optimization-and-hybridtrace-scaling`, `untrusted-llvm-optimization-oracle-and-certificate-replay-architecture`, `llvm-oracle-guided-minissa-minimach-replay-prototype-and-parity`, `oracle-hint-drift-alignment-and-fallback-resilience`, `x86-avx512-short-loop-regression-and-vector-width-profitability`, `microarchitectural-code-layout-variance-dsb-jcc-and-btb-dissection`, `verified-minimach-ext-tsp-layout-and-loop-jcc-alignment` |
| **14. `validated-llvm`** | 2 | `black-box-translation-validation-alive2-and-mir-to-llvm-on-rust`, `llvm-derivation-emission-instrumentation-architecture-and-cost` |
| **15. `checker-substrate`** | 8 | `lean-native-compilation-pipeline-runtime-and-trust-surface`, `lean-kernel-derivation-scale-checking-and-reflection-throughput`, `independent-proof-checkers-and-smaller-trusted-computing-bases`, `compiler-substrate-benchmarks-lean-rust-and-ocaml`, `verified-rustc-delivered-toolchain-trusted-component-inventory`, `lean-large-isa-and-compiler-semantics-scaling`, `lean-unboxed-bytearray-bitset-and-soa-compiler-substrate-bridge`, `lean-kernel-natgmp-limb-tuning-and-nanoda-parallel-audit-throughput` |
| **16. `validation`** | 7 | `rustc-compiletest-bootstrap-and-alternate-backend-test-mechanics`, `rustc-test-suite-machine-readable-classification`, `compiler-differential-testing-fuzzing-reduction-and-bug-records`, `ecosystem-scale-testing-crater-self-hosting-and-flakiness`, `tier1-target-test-execution-emulators-and-combinatorial-coverage`, `rustc-benchmark-methodology-and-speed-size-baselines`, `concurrency-and-simd-compiler-testing-tools-and-harnesses` |
| **17. `program-planning`** | 13 | `rustc-baseline-toolchain-selection-and-manifest`, `rustc-experimental-corpora-and-harness-conventions`, `verified-rustc-research-map-and-open-question-ledger`, `verified-compiler-effort-precedents-and-agent-proof-productivity`, `compiler-isa-sdk-licensing-trademarks-and-upstream-governance`, `compiler-qualification-assurance-cases-and-deviation-policies`, `verified-rust-frontend-approaches-trait-solver-polonius-and-thir-lowering`, `safe-rust-ub-freedom-soundness-and-standard-library-verification`, `cross-language-lto-linker-plugin-bitcode-and-llvm-ir-semantics`, `verified-rustc-designer-dry-run-and-gap-analysis`, `rustc-multi-release-mir-abi-drift-and-version-isolated-adapter`, `automated-toolchain-table-regeneration-and-mir-minissa-upgrade-validator`, `compiler-upgrade-soundness-quarantine-and-proof-invalidation-bounds` |

## Boundaries

- **Point-in-time baseline (`Rust 1.99.1`, `LLVM 23.1.1`, `Lean 4 v4.34.1`) with multi-release adapter coverage:**
  All 154 answered questions and 147 `compilers/verified-rustc` packages are
  anchored to the pinned `1.99.1` / `23.1.1` / `v4.34.1` revisions in Table 2,
  with multi-release drift (`1.98.1` through `1.100.0` and `nightly-2026-11-12`)
  explicitly bridged by the version-isolated `CoreMIR` adapter and automated
  table-regeneration pipeline in Area 17 (`program-planning`).

## Evidence

- **Compiler crate DAG:** Extracted directly from the 78 `compiler/*/Cargo.toml`
  manifests in `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`.
- **Normative specification revisions:** Verified via `git rev-parse HEAD` across
  the nine upstream repositories listed in Table 2.
- **Preserved support artifacts:**
  - `support/roadmap_ledger.json` — machine-readable 78-crate compiler DAG by
    depth and the 17-area mapping of governing crates, normative sources, topic
    queries, all 147 `compilers/verified-rustc` packages (plus 67 foundational
    packages), and all 154 answered program questions (`0` open questions).
  - `support/verify_roadmap_ledger.py` — automated verification script checking
    that all 17 areas, 154 questions, and 147 `compilers/verified-rustc`
    packages in `CATALOG.json` are completely indexed and answered.
  - `support/query_roadmap.py` — standalone CLI wrapper to query coverage by
    design area.

## Revalidation

To verify that all 17 design areas, 154 program questions, and 147
`compilers/verified-rustc` packages in `CATALOG.json` are indexed with zero
unanswered questions, run:

```console
python3 reports/verified-rustc-research-map-and-open-question-ledger/support/verify_roadmap_ledger.py
python3 reports/verified-rustc-research-map-and-open-question-ledger/support/query_roadmap.py
```
