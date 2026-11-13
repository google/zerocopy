# Verified Drop-In Rust Compiler Research Map, Crate Architecture, and Open-Question Ledger

## Summary

Designing a verified drop-in replacement for **Rust 1.99.1**
(`rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67`, LLVM `23.1.1` at
`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, and **Lean 4 v4.34.1** at
`5045d0056413266e57c625dcd7c365b10e377c52`) spans 16 coupled architectural
areas:

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
   revisions of the nine external normative and semantic repositories (`rust-lang/fls`
   tag `1.99`, `rust-lang/reference`, `rust-lang/nomicon`,
   `rust-lang/unsafe-code-guidelines`, `minirust/minirust`,
   `rust-lang/opsem-team`, `rust-lang/rfcs`, `joshlf/anneal`, and
   `leanprover/lean4`) that govern source, MIR, and target semantics.
3. **16-area coverage map and open-question ledger:** `support/roadmap_ledger.json`
   and `support/query_roadmap.py` map each of the 16 design areas to its
   governing `rustc 1.99.1` crates, existing reference corpus reports (45
   directly mapped packages across the 184-report corpus), and the concrete
   questions that are answered **fully (20)**, **partly (16)**, or remain
   **open (45)** across the architecture, platform ABI, proof system, `-O3`
   optimizer, validated LLVM tier, checker substrate, and validation tracks.

## Applicability

This map and open-question ledger apply to the **Rust 1.99.1** compiler and
standard-library workspace (`58cf8f9c35b355199727627d07ae34a4e2846d67`), its
LLVM `23.1.1` backend (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), the
**Lean 4 v4.34.1** proof kernel (`5045d0056413266e57c625dcd7c365b10e377c52`),
the **Anneal** verification pipeline (`7abf0691c404393e3e4fc26eb3d4094e3170b5c7`),
and the eight Tier 1 targets (`x86_64-unknown-linux-gnu`,
`x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `aarch64-unknown-linux-gnu`,
`aarch64-apple-darwin`, `aarch64-pc-windows-msvc`, `i686-unknown-linux-gnu`, and
`i686-pc-windows-msvc`):

- **Durable subject discipline:** In accordance with `FORMAT.md`, `REPORT.json`
  pins only immutable external upstream repository revisions, never prior
  commits of the `reference` branch itself. Corpus package handles are listed in
  Section 3 and `support/roadmap_ledger.json` as navigation aids alongside
  their canonical topic queries.

## Findings

### 1. Rust 1.99.1 `compiler/` crate dependency DAG and backend seam

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

### 2. Pinned normative and semantic authority repositories

Basis: normative + source

Table 2 records the exact commits of the normative and formal specification
repositories inspected alongside `rust-lang/rust` `1.99.1`.

| Repository | Pinned Revision | Commit Date | Authority Scope |
| :--- | :--- | :--- | :--- |
| `rust-lang/fls` | `946eacae5a4a33a89af7832178504692439e7478` (tag `1.99`) | 2026-10-30 | Ferrocene Language Specification for Rust `1.99` (syntax, type system, attributes, ABI, inline assembly, and library contracts). |
| `rust-lang/reference` | `bcd62f35e8bf480ec5b0fa569b6d12ea5924030c` | 2026-11-10 | Upstream Rust Reference defining language constructs, memory model, type layout (`repr(C)`, `repr(Rust)`, `repr(simd)`), and list of behaviors considered undefined. |
| `rust-lang/nomicon` | `b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6` | 2026-10-17 | Unsafe Rust invariants, drop check, unwinding across FFI (`C-unwind`), and subtyping variance. |
| `rust-lang/unsafe-code-guidelines` | `d809f91e62968913d808e53397fbcf7cea762cce` | 2026-05-05 | Operational validity invariants (`Scalar`, padding, uninitialized memory), aliasing, and layout guarantees. |
| `minirust/minirust` | `063d784186d3252bee242217f218223205c0b568` | 2026-11-06 | Mechanized-style operational semantics for MiniRust (`BasicMemory`, `TreeBorrows`, `StackedBorrows`, pointer provenance, and value representation transfers). |
| `rust-lang/opsem-team` | `d462085814030cc5b21dfa0ce831dfc1619d69b1` | 2026-09-14 | Operational Semantics Team decisions and tracking issues on UB, provenance, and concurrency. |
| `rust-lang/rfcs` | `7677feddd580f356f780cb7123aeda6a3708275a` | 2026-11-10 | Design RFCs (`v0` symbol mangling RFC 2603, inline `asm!` RFC 2873, `c_unwind` RFC 2945, Strict Provenance RFC 3559). |
| `joshlf/anneal` | `7abf0691c404393e3e4fc26eb3d4094e3170b5c7` | 2026-11-12 | `trusted/lean` MIR semantics, `Trusted.CrateTheorem`, `trusted/audit` `.olean` verifier, and `trusted/rustc-capture`. |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | 2026-09-24 | Lean 4 kernel, `bv_decide`/`bv_omega` decision procedures, Lean-to-C compiler, and bundled LLVM `22.1.4` toolchain. |

### 3. Design-area coverage map and open-question ledger

Basis: source + derived

Table 3 summarizes the 16 design areas of the verified drop-in `rustc`
replacement, mapping each area to its governing `rustc 1.99.1` crates, existing
corpus packages, and open-question counts (full item-by-item ledger in
`support/roadmap_ledger.json`).

| Area ID & Title | Governing `rustc 1.99.1` Crates | Existing Corpus Packages Mapped | Answered (Full / Part) | Open Questions | Key Unresolved Questions and Empirical Discriminators |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **1. `contract`** (Drop-in CLI/JSON, build systems, deviations) | `rustc_driver`, `rustc_interface`, `rustc_session`, `rustc_errors`, `rustc_feature` | `rustc-baseline-toolchain-selection-and-manifest`, `cargo-unit-graphs-feature-resolution-and-rustc-invocations`, `cargo-rustc-wrapper-caching-and-extraction-coverage`, `rustc-conditional-compilation-source-spans-and-diagnostics`, `cross-tool-source-spans-utf8-columns-and-diagnostic-normalization` | 3 / 2 | 3 | Complete backend-dependent CLI flag inventory; how `bazel`, `buck2`, `gn`, Linux kernel, and `Soong` invoke `rustc`; observable implementation-defined behavior vs normative UB; ISO 26262 / DO-178C qualification assurance structure. |
| **2. `end-to-end-theorem`** (Theorem shape, horizontal/vertical composition, property transfer) | `rustc_middle`, `rustc_codegen_ssa` (+ Anneal `trusted/lean`) | `anneal-behavior-codec-and-partial-compile-refinement-algebra`, `anneal-forward-compatible-mir-semantics-and-reference-admissible-refinement`, `anneal-mir-to-x86-compiler-vcgen-and-variable-step-refinement`, `compcert-sel4-everest-pass-composition-and-proof-maintenance`, `compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026`, `cross-prover-interoperability-verified-checkers-and-tcb-accounting`, `semantic-models-lenses-hyperproperties-and-putnam-tcb-boundary`, `verified-rust-compiler-architecture-self-hosting-and-certifying-bootstrap` | 2 / 2 | 2 | Exact theorem signature transferring Anneal's `Compiler.Verified` obligations on `Runtime(PostCleanup)` MIR to Tier 1 ISA traces across separate compilation, unverified FFI shims, and LTO. |
| **3. `mir-and-aliasing`** (MIR semantics, aliasing, FP, provenance, layout) | `rustc_middle`, `rustc_abi`, `rustc_const_eval`, `rustc_mir_dataflow` | `minirust-*` (4 packages), `tree-borrows-two-stage-protector-release-and-reborrow-contracts`, `rustc-postcleanup-mir-*` (3 packages), `rustc-mir-phases-reachability-and-postcleanup-lowering`, `rust-validity-initialization-padding-and-transmute-semantics`, `rust-raw-pointer-validity-provenance-and-wide-metadata`, `rust-aggregate-dst-and-target-layout-guarantees`, `lean-ieee754-floatspec-cryptography-and-constant-time`, `lean-miri-interpreter-hooks-move-deinit-and-provenance-fragments`, `anneal-pme-mir-semantics-and-polar-ctfe-admission`, `anneal-scalar-mir-differential-execution-and-capture-alignment` | 2 / 2 | 2 | Construct-by-construct operational semantics for all `1.99.1` MIR forms (`BoxDerefTransmute`, `NullReferenceConstructed`); end-to-end FP NaN/FMA/`f16`/`f128` refinement; `StorageLive`/`StorageDead` stack lifetime and provenance across Rust, MIR, and LLVM; layout algorithm mechanization; empirical `noalias` value and UB rate. |
| **4. `concurrency`** (Weak memory models and Tier 1 atomic lowerings) | `rustc_middle`, `rustc_codegen_ssa`, `rustc_codegen_llvm` | `assembly-atomic-fence-mappings-and-aarch64-x86-weak-memory-models`, `rust-atomics-weak-memory-and-aliasing-operational-models`, `anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal`, `anneal-concurrency-weak-memory-kernels-and-storage-survey` | 1 / 1 | 2 | Exact atomic/fence sequences emitted by `rustc 1.99.1` across all 8 Tier 1 targets (including `i686` `cmpxchg8b` and `aarch64` `+outline-atomics`); hardware `litmus7` validation on x86-64 and AArch64. |
| **5. `platform-conventions`** (Calling conventions, unwinding, TLS, startup, objects, linking) | `rustc_target`, `rustc_abi`, `rustc_codegen_ssa`, `rustc_codegen_llvm`, `rustc_sanitizers` | `compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026`, `configured-rust-capture-fnabi-placement-and-formality-specr-boundaries`, `rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking`, `rustc-drop-elaboration-unwind-landing-pads-and-extensible-mir-semantics`, `anneal-subprocess-supervision-elf-runpath-and-archive-packaging`, `riscv64-elf64-relocations-lp64d-abi-and-linux-ecall-runtime-2026` | 1 / 1 | 4 | Complete Tier 1 `FnAbi` marshaling rules; ELF `.eh_frame`, Mach-O `__unwind_info`, Windows x64 `.pdata`/`.xdata`, and 32-bit `i686-pc-windows-msvc` `fs:[0]` SEH; ELF/Mach-O/PE TLS models; stack probes (`__rust_probestack`, `__chkstk`); CRT startup, relocations, linker driver, dynamic loading, and Linux-hosted cross-compilation for all 8 Tier 1 targets. |
| **6. `intrinsics-and-assembly`** (Intrinsics, `core::arch`, target features, inline `asm!`) | `rustc_middle`, `rustc_codegen_ssa`, `rustc_target`, `rustc_builtin_macros` | `rust-inline-assembly-contracts-relocations-and-simd-correspondence`, `rustc-codegen-backend-abi-intrinsics-and-rv64gc-cross-compilation` | 1 / 1 | 4 | Full semantic catalog of all 316 `#[rustc_intrinsic]` functions and 81 `simd_*` intrinsics in `1.99.1`; Intel XED / ARM ASL machine-readable vendor data extraction for 8,115 `core_arch` bindings; per-target instruction/libcall lowering tables; `target_features.rs` implication graphs and `asm!`/`global_asm!`/`#[unsafe(naked)]` census. |
| **7. `isa-models`** (Formal x86-64, i386, AArch64 models and verified assemblers/linkers) | `rustc_target` | `asl-l3-lnsym-and-isa-verification-frameworks-lean-adaptation`, `sail-isa-models-lean-backend-and-rv64d-decoding-framing`, `anneal-acceptance-frontier-isa-roadmap-and-verifier-bibliography`, `anneal-backend-codegen-binaries-lifters-and-sandboxes-survey` | 1 / 1 | 3 | Detailed evaluation of x86-64, i386, and AArch64 formal ISA models across GP, SIMD, FP, and flags; empirical instruction-usage census on LLVM-compiled Rust binaries; hardware ISA model validation and verified assemblers/linkers. |
| **8. `verified-mode`** (Per-function routing, LLVM attributes, binary origin, attestation, LLVM-free sysroot) | `rustc_codegen_ssa`, `rustc_monomorphize`, `rustc_symbol_mangling`, `rustc_metadata` | `anneal-public-mir-discovery-interprocedural-calls-and-obligation-inventory`, `anneal-trusted-boundary-audit-olean-stubbing-and-conservativity`, `open-rust-library-certificate-closure-and-consumer-acceptance-protocols`, `compiler-concurrent-source-modification-and-hermetic-input-binding` | 1 / 1 | 4 | Per-function routing between verified and fallback backends; complete catalog of LLVM attributes/metadata emitted by `rustc_codegen_llvm`; byte-by-byte binary origin attribution; building `core`/`alloc`/`std`/`compiler_builtins` and host tools without LLVM. |
| **9. `normal-compilation`** (Wild configs, PGO, LTO, debuginfo, hardening, size opt) | `rustc_session`, `rustc_codegen_ssa`, `rustc_codegen_llvm`, `rustc_sanitizers` | `cargo-unit-graphs-feature-resolution-and-rustc-invocations` | 0 / 1 | 4 | Wild crates.io profile/flag census; ThinLTO, Fat LTO, and PGO mechanics and empirical speed/size value; DWARF v4/v5 and PDB/CodeView debugger compatibility; hardening (`-Zstack-protector`, CET, PAC/BTI, CFG) and `opt-level=s`/`z` size parity. |
| **10. `rustc-internals`** (MIR artifact export, MIR passes, monomorphization, shims, vtables, statics, CGUs, lowering) | `rustc_middle`, `rustc_mir_transform`, `rustc_monomorphize`, `rustc_const_eval`, `rustc_codegen_ssa`, `rustc_codegen_llvm` | `rustc-mir-phases-reachability-and-postcleanup-lowering`, `rustc-mir-steal-lifetimes-and-dual-profile-capture`, `rustc-const-evaluation-monomorphization-and-pme-capture`, `rustc-cross-crate-rmeta-provenance-and-foreign-mir-inlining`, `rustc-name-resolution-local-item-identity-and-type-lowering`, `anssa-block-argument-ssa-mem2reg-and-mir-semantic-hazards-2026` | 2 / 1 | 4 | Deterministic external MIR artifact schema and cryptographic binding; complete inventory, bug history, and speed/size value of `rustc_mir_transform` passes; monomorphization collector, shims, vtable layouts, constants/statics, symbol visibility, CGU partitioning, `rustc_codegen_ssa::mir` lowering, and panic/entry lowering. |
| **11. `ecosystem-demand`** (Stdlib demand, download-weighted crate census, CPU time breakdown) | `rustc_middle` (+ `library/*`) | `rustc-experimental-corpora-and-harness-conventions` | 1 / 0 | 3 | Per-target codegen feature demand of `core`/`alloc`/`std`/`compiler_builtins`; download-weighted feature/intrinsic/assembly census across the crates.io sample; runtime hotspot profiling across the application and benchmark corpora. |
| **12. `proof-system-and-irs`** (Certificates, relational logics, IRs, LLVM 23 semantics, e-graphs, decision procedures) | Anneal `trusted/lean`, `theory/Anneal` | `translation-validation-certifying-compilation-and-pass-refinement-certificates`, `anllvm-clean-slate-ir-semantics-and-tree-borrows-lowering`, `anllvm-globalisel-backend-and-certificate-checkers`, `opencompl-riscv-lean-lean-mlir-and-ship-your-interpreter-2026`, `smt-sat-alethe-carcara-and-numerical-proof-certificate-reconstruction`, `anneal-solvers-decision-procedures-and-certificates-survey`, `lean-bitvec-proof-term-scaling-bv-omega-bv-decide-and-meta-fvar-caching`, `lean-tactic-extensions-simp-omega-and-grind` | 1 / 1 | 4 | Quantitative certificate size/speed numbers across certifying compilers; relational logic completeness for loop/CFG optimizations; IR representation trade-offs; LLVM 23.1.1 IR formal semantics; proof-producing e-graphs; derivation expressiveness and volume prototypes. |
| **13. `optimizer`** (LLVM NewPM pipeline, pass ablation, scalar/loop/IPO/codegen obligations, TableGen, backend candidates) | `rustc_codegen_llvm`, `rustc_llvm` | `anneal-mid-level-ir-optimizations-and-lowering-survey`, `regalloc2-symbolic-checker-stacking-and-quantitative-stack-bounds-2026` | 1 / 1 | 4 | Complete LLVM 23.1.1 pass pipeline in `rustc 1.99.1`; pass ablation speed/size measurements; formal obligations for scalar/memory, loop/vector, IPO/LTO, and codegen passes; TableGen reuse, tuning models, and GCC vs Cranelift vs LLVM vs CompCert/CakeML comparison. |
| **14. `validated-llvm`** (Black-box Alive2 validation vs derivation-emitting LLVM) | `rustc_codegen_llvm` | `translation-validation-certifying-compilation-and-pass-refinement-certificates`, `anllvm-clean-slate-ir-semantics-and-tree-borrows-lowering` | 0 / 1 | 2 | Empirical `alive-tv` coverage, timeout, and unsupported-feature breakdown on Rust `1.99.1` `-O3` LLVM IR; pass-by-pass C++ instrumentation cost to emit derivations from LLVM 23.1.1. |
| **15. `checker-substrate`** (Lean native compilation trust, kernel scaling, standalone checkers, TCB inventory) | Anneal `trusted/audit`, `trusted/cargo-anneal` | `untrusted-proof-dependencies-effect-isolation-and-guarantee-verification`, `cross-prover-interoperability-verified-checkers-and-tcb-accounting`, `lean-kernel-memory-ceilings-whnf-scaling-and-validator-architectures`, `lean-olean-ilean-format-and-compilation-determinism`, `lean-environment-identity-imports-and-trust-admissions`, `deductive-proof-object-and-refinement-certificate-kernels-2013-2026` | 2 / 1 | 3 | Audit of Lean `v4.34.1` C codegen, runtime reference counting, `libgmp`, and `@[extern]`; Lean kernel and standalone checker throughput at compiler-derivation and full ISA scale; delivered toolchain TCB inventory. |
| **16. `validation-and-planning`** (`compiletest`, fuzzers, Crater, target execution, effort, licensing, kill criteria) | `src/tools/compiletest` | `rustc-baseline-toolchain-selection-and-manifest`, `rustc-experimental-corpora-and-harness-conventions`, `compcert-sel4-everest-pass-composition-and-proof-maintenance` | 1 / 1 | 3 | `compiletest` mechanics and machine-readable test classification (~25,000+ tests); differential fuzzing (`rustlantis`, `abi-cafe`), Crater, and Tier 1 emulator/hardware test execution; person-year effort models, clean-room/SDK licensing, and kill criteria. |

## Boundaries

- **Wave 1–3 open questions (`not examined` in this initial roadmap baseline):**
  The 45 open questions cataloged in Table 3 and `support/roadmap_ledger.json`
  define the exact research targets for subsequent domain investigations and
  empirical benchmark runs; this report records their baseline status after
  establishing the `1.99.1` + Lean `v4.34.1` toolchain pin and shared corpora.

## Evidence

- **Compiler crate DAG:** Extracted directly from the 78 `compiler/*/Cargo.toml`
  manifests in `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`.
- **Normative specification revisions:** Verified via `git rev-parse HEAD` across
  the nine upstream repositories listed in Table 2.
- **Preserved support artifacts:**
  - `support/roadmap_ledger.json` — machine-readable 78-crate compiler DAG by
    depth and the 16-area mapping of governing crates, normative sources, topic
    queries, existing corpus packages, and answered/open questions.
  - `support/query_roadmap.py` — standalone script to query coverage and open
    questions by design area.

## Revalidation

After publishing new corpus reports under the `compilers/verified-rustc` topic,
update `support/roadmap_ledger.json` and run:

```console
python3 reports/verified-rustc-research-map-and-open-question-ledger/support/query_roadmap.py
```
