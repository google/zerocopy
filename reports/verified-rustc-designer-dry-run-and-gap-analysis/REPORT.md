# End-to-End Architectural Designer Dry Run and Gap Analysis for a Verified Drop-In Rust Compiler

## Summary

Executing a zero-external-access architectural design dry run for a verified
drop-in replacement for **Rust 1.99.1** (`rust-lang/rust`
`58cf8f9c35b355199727627d07ae34a4e2846d67`), its bundled **LLVM 23.1.1**
backend (`rust-lang/llvm-project` `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`),
the **Anneal** verification pipeline (`joshlf/anneal`
`7abf0691c404393e3e4fc26eb3d4094e3170b5c7`), and the **Lean 4 v4.34.1** theorem
prover (`leanprover/lean4` `5045d0056413266e57c625dcd7c365b10e377c52`) across
all **13 architectural decision domains** (`D1`–`D13`) and **27 program
research goals** (`G1`–`G27`) using only the **107 `compilers/verified-rustc`
corpus packages** (plus 67 foundational Anneal, MiniRust, and Lean 4 packages)
establishes four governing conclusions:

1. **Zero unrecorded external facts (`0` new research seeds required):** Every
   external specification, compiler interface, IR invariant, target calling
   convention, unwinding format, atomic mapping, intrinsic signature, ISA
   encoding, derivation format, kernel scaling cliff, and benchmark baseline
   required to specify the end-to-end system is recorded with primary-source
   citations and executable probes in `support/decision_coverage_matrix.json`.
   Every remaining design choice across `D1`–`D13` is classified as
   `REASONING_ONLY` (an engineering trade-off over quantified corpus facts
   rather than an unrecorded empirical unknown).
2. **Concrete end-to-end architecture selected by corpus evidence:**
   - **Frontend and MIR capture (`D1`, `D2`, `D5`):** Reuse the unmodified
     `rustc 1.99.1` frontend down to `Runtime(PostCleanup)` Mid-Level
     Intermediate Representation (`mir_drops_elaborated_and_const_checked`),
     bypassing the 42 unverified `inner_optimized_mir` pass invocations (`<0.8%`
     geomean runtime delta when `-O3` runs downstream) and emitting a
     deterministic, SHA-256-bound `.anneal-mir` section inside `.rlib`/`.rmeta`
     archives covering all 17 MIR-affecting compiler options, monomorphic
     `MonoItem` bodies, 12 `ShimKind` variants, `TyAndLayout` records, `FnAbi`
     tables, `VtblEntry` layouts, and `GlobalAlloc` byte/provenance tables.
   - **Semantics, aliasing, and concurrency (`D3`, `D4`):** Anchor the source
     semantics in `Runtime(PostCleanup)` MIR parameterized by `TargetDataLayout`
     invariants across all 8 Tier 1 targets, paired with **Tree Borrows** with
     two-stage protector release (eliminating `63.0%` (`4,969 / 7,887`) of
     ecosystem Miri UB failures caused by Stacked Borrows subobject shrinking
     and eager `Unique` retag invalidation while preserving `1.14x–1.38x`
     `noalias` speedup on memory-bound kernels), **RFC 3514** 4-choice NaN
     floating-point rules, and an **RC11 / IMM** axiomatic weak-memory model
     bridged to Promising-style thread-local simulation for atomic rewrites.
   - **IR stack, `HybridTrace` derivations, and kernel checking (`D6`, `D13`):**
     Lower through untrusted **MiniSSA** (block-argument SSA with explicit
     `freeze`/`undef`/`poison` and Tree Borrows ghost permissions) and
     **MiniMach** (register/frame-allocated machine IR) to Tier 1 assembly.
     Justify optimizations in **`HybridTrace`** (rewrite traces + acyclic
     e-graph congruence + decidable `BitVec`/`omega`/interval/FP side-condition
     checkers), which achieves **100% (`12 / 12`) `-O3` expressiveness** at
     **`24.77 B/step` raw (`12.04 B/step` zstd-compressed)**, is proven both
     sound (`checkDeriv_sound`) and checker-complete (`checkDeriv_complete`) in
     Lean `v4.34.1` (`2.95x` proof-to-spec ratio), and checks at **`2.13M`
     steps/s natively** or **`84,118` steps/s inside the Lean C++ kernel** via
     CPS-forced packed `NatGMP` reflection (`ReflPacked_NatGMP`).
   - **Optimizer, Validated LLVM tier, and Tier 1 targets (`D7`–`D12`):**
     Concentrate proof-producing optimization engineering on the **6 pass
     families** (`Inlining`, `SROA + Mem2Reg`, `InstCombine`, `SimplifyCFG`,
     `LoopOpt + LICM`, and `Loop + SLP Vectorization`) that capture **>99% of
     LLVM 23.1.1 `-O3` runtime speedup (`11.71x`)** and **65.8% of `.text` size
     reduction**, reusing LLVM 23.1.1's `684,912` lines of TableGen ISA data and
     family-stratified tag-record Lean 4 ISA models (`2,000+` opcodes elaborated
     in `2.66s–4.30s`). Pair the LLVM-free backend with an optional **Validated
     LLVM tier** combining a **100%-accepting `Runtime(PostCleanup)`
     MIR-to-LLVM-IR SMT validator** and **94.4%-accepting per-pass scalar/memory
     Alive2 validation**.
3. **Retirement of all six program kill criteria:** All six candidate failure
   modes from Goal 25 (proof-system expressiveness on vectorization/LTO,
   derivation size/checking speed, aliasing-model permissiveness vs. `noalias`
   power, Lean 4 full-ISA elaboration scaling, 32-bit Windows `fs:[0]` SEH
   verifiability, and IR-portable PGO effectiveness) are resolved with
   reproducible prototypes and hardware measurements.

## Applicability

This report applies to the end-to-end architectural design of a verified
drop-in replacement for **Rust 1.99.1**
(`58cf8f9c35b355199727627d07ae34a4e2846d67`), its **LLVM 23.1.1** backend
(`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), the **Lean 4 v4.34.1** theorem
prover (`5045d0056413266e57c625dcd7c365b10e377c52`), the **Anneal**
verification framework (`7abf0691c404393e3e4fc26eb3d4094e3170b5c7`), the
**Ferrocene Language Specification (FLS) tag `1.99`**
(`946eacae5a4a33a89af7832178504692439e7478`), and the eight Tier 1 targets
(`x86_64-unknown-linux-gnu`, `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`,
`aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`,
`aarch64-pc-windows-msvc`, `i686-unknown-linux-gnu`, and
`i686-pc-windows-msvc`).

In accordance with `FORMAT.md`, `REPORT.json` pins only immutable upstream
repository revisions and never prior commits of the `reference` branch. Corpus
report package names are cited in `## Findings` and
`support/decision_coverage_matrix.json` as deterministic navigation handles.

## Findings

### 1. Summary of the 13 Architectural Decision Domains (`D1`–`D13`)

Basis: normative + source + execution + derived

Table 1 synthesizes the architectural decisions, governing quantitative
parameters, primary-source corpus reports, and gap classifications across all
13 decision domains (`D1`–`D13`). Full machine-readable records appear in
`support/decision_coverage_matrix.json`.

| Domain | Goals | Selected Architectural Decision | Key Quantitative Parameters from the Corpus | Primary Supplying Reports (Count / Representative Handles) | Unrecorded Facts / Gap Class |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`D1` The Pin** | 5, 27 | Pin `rustc 1.99.1` (`58cf8f9c35b3`), LLVM `23.1.1` (`1b9c0d5ff9bb`), FLS `1.99` (`946eacae5a4a`), Anneal (`7abf0691c404`), and Lean `v4.34.1` (`5045d0056413`) across all 8 Tier 1 targets. | 78 `compiler/` crates (depth 23 DAG); 469 `#![feature]` gates in sysroot; 1,482 total features (219 codegen-relevant); fixes `#163911` FFI `bool` bug while avoiding `1.100.0` `PhantomDeref` (`#159103`). | 4 (`rustc-baseline-toolchain-selection-and-manifest`, `rustc-baseline-repository-map-and-internal-interfaces`, `rust-language-and-library-codegen-feature-inventory`, `verified-rustc-research-map-and-open-question-ledger`) | `0` / `REASONING_ONLY` |
| **`D2` Drop-In Contract** | 1, 2, 3, 4 | Reuse `rustc 1.99.1` frontend/driver; implement 27-method `CodegenBackend`; fail-closed on unsupported LLVM flags in strict mode; preserve JSON diagnostics, Miri (`-Zmiri-tree-borrows`), and `rust-analyzer` proc-macro v2 ABI; govern deviations by 5-tier normative map. | 38 top-level flags, 54 `-C` flags, 238 `-Z` flags, 21 `--print` kinds, 11 `--emit` kinds, 8 `--crate-type` kinds; 9 build systems; 14 backend-dependent observable categories; 292 `known-bug` UI tests; 18 spec disagreements resolved. | 6 (`rustc-external-cli-json-and-backend-interface-contract`, `rustc-build-system-and-consumer-invocation-contracts`, `rustc-backend-dependent-observable-behaviors`, `rust-normative-authority-map-and-rustc-deviations`, `rustc-and-llvm-soundness-holes-and-miscompilation-census`, `miri-rust-analyzer-proc-macro-and-doctest-toolchain-contracts`) | `0` / `REASONING_ONLY` |
| **`D3` End-to-End Theorem & Ledger** | 6 | 5-link `ProductiveCompiles` + `ResourceBSim` refinement chain from Anneal `Runtime(PostCleanup)` MIR `VerificationResult` through `.anneal-mir` hashes, `HybridTrace` checking, and CompCertO/DimSum open simulation to Tier 1 ISA traces, backed by a 5-stratum Assumption Ledger. | 10 Anneal claim forms classified; 5-link Lean `v4.34.1` prototype (`642` LOC, `4.27s` build, `0` `sorryAx`, `0` `native_decide`) down to 29-byte x86-64 `-O3` machine code; 5 definitional seams bridged (`wordRepresentsNat`, `FramePreserving`, `abiRegMap`, `ByteMem_to_WordMem`, `decode_encode_roundtrip`). | 14 (`compiler-correctness-theorem-shapes-and-end-to-end-chains`, `compositional-correctness-linking-and-whole-program-optimization`, `observable-behavior-property-transfer-and-anneal-statement-forms`, `cross-prover-guarantee-composition-and-native-checker-soundness`, `end-to-end-verified-mir-to-isa-refinement-chain-and-seams`, `verified-rustc-delivered-toolchain-trusted-component-inventory`) | `0` / `REASONING_ONLY` |
| **`D4` MIR, Aliasing & Concurrency** | 7, 9 | `Runtime(PostCleanup)` MIR semantics parameterized by `TargetDataLayout`; **Tree Borrows** (two-stage protector release) as default aliasing model; PNVI-ae-udi + Strict Provenance; RFC 3514 4-choice NaN lattice; RC11/IMM axiomatic concurrency + thread-local Promising views. | 12 `StatementKind`, 14 `TerminatorKind`, 13 `Rvalue`, 12 `CastKind` variants; Tree Borrows eliminates `63.0%` (`4,969 / 7,887`) of ecosystem Miri UB failures while retaining `1.14x–1.38x` `noalias` speedup on memory-bound kernels; `2.70e6` native x86-64 litmus runs (`495 / 300k` `SB_Relaxed` weak outcomes, `0 / 300k` `SeqCst`). | 28 (`rustc-mir-construct-semantics-miri-minirust-and-codegen`, `rust-aliasing-models-stacked-tree-minirust-and-llvm-attributes`, `rust-aliasing-models-ub-prevalence-and-llvm-optimization-value`, `rust-allocation-provenance-and-stack-lifetime-semantics`, `rustc-layout-computation-target-datalayouts-and-parametricity`, `rust-floating-point-semantics-llvm-lowering-and-isa-behavior`, `weak-memory-concurrency-models-hardware-mappings-and-optimizations`, `tier1-atomics-and-fences-instruction-lowering`, `weak-memory-hardware-litmus-testing-x86-and-aarch64`) | `0` / `REASONING_ONLY` |
| **`D5` MIR Artifact & Middle-End** | 8, 15 | Capture `Runtime(PostCleanup)` MIR (`-Zmir-opt-level=0`) into a deterministic `.anneal-mir` section inside `.rlib`/`.rmeta` archives bound by SHA-256 over the 17 MIR-affecting options, monomorphic `MonoItem`s, 12 `ShimKind`s, `TyAndLayout`, `FnAbi`, `VtblEntry`, and `GlobalAlloc`. | 67 `MirPass`es (42 in `inner_optimized_mir`; ablating all 42 shifts `-O3` speed by `<0.8%` geomean while removing MIR pass soundness hazards); 5 `InstanceKind` + 12 `ShimKind` variants; 3-word vtable headers; `139` `BuilderMethods` in `rustc_codegen_ssa::mir` (`9.6K` LOC). | 10 (`rustc-mir-artifact-export-settings-and-proof-binding`, `rustc-mir-optimization-passes-semantics-soundness-and-value`, `rustc-monomorphization-vtables-statics-symbols-and-cgu-partitioning`, `rustc-mir-to-llvm-lowering-and-runtime-visible-semantics`) | `0` / `REASONING_ONLY` |
| **`D6` IR Stack & Proof System** | 17 | Lower `Runtime(PostCleanup)` MIR $\rightarrow$ `MiniSSA` $\rightarrow$ `MiniMach` $\rightarrow$ ISA assembly; emit `HybridTrace` derivations (rewrite traces + acyclic e-graphs + decidable side-condition checkers) proven sound (`checkDeriv_sound`) and complete (`checkDeriv_complete`) in Lean `v4.34.1`, checked via CPS-forced `ReflPacked_NatGMP`. | `HybridTrace` expresses `12 / 12` (`100%`) `-O3` classes at `24.77 B/step` raw (`12.04 B/step` zstd); Lean `v4.34.1` soundness + completeness prototype (`691` lines, `2.95x` ratio, `2.66s` build); `ReflPacked_NatGMP` checks $10^6$ steps in `11.89s` (`84.1k` steps/s, `524 MB` RSS) vs. stack overflow at $N=10^3$ (right-nested terms) or $2.5 \times 10^5$ (naïve reflection); full sysroot certificates ~`3.6 MB` compressed. | 18 (`llvm-o3-derivation-formats-expressiveness-and-checking-cost`, `lean-derivation-checker-soundness-and-completeness-prototype`, `rustc-build-ir-and-pass-transformation-volume-statistics`, `lean-kernel-derivation-scale-checking-and-reflection-throughput`, `proof-producing-compilation-and-certificate-formats-quantitative-survey`, `relational-logics-simulation-techniques-and-completeness-for-compiler-derivations`, `mechanized-compiler-ir-semantics-poison-provenance-and-machine-frames`, `equality-saturation-with-proofs-egraphs-aegraphs-and-refinement-rewriting`, `verified-side-condition-decision-procedures-and-certificate-checkers`) | `0` / `REASONING_ONLY` |
| **`D7` Optimizer & Parity Plan** | 14, 18, 24 | Clean-slate derivation-emitting `MiniSSA`/`MiniMach` optimizer paired with a universally proven single-pass baseline lowerer; prioritize the 6 pass groups delivering >99% of `-O3` speedup; reuse LLVM 23.1.1 TableGen data; support ThinLTO/FatLTO over `.anneal-mir` and IR-portable CFG PGO profiles. | 6 LLVM pass groups (`Inlining`, `SROA`, `InstCombine`, `SimplifyCFG`, `LoopOpt/LICM`, `Vectorization`) drive >99% of the `11.71x` `-O3` speedup (`4,590 us` $\rightarrow$ `391.9 us`) and `65.8%` `.text` reduction; Cranelift `-O3` is `11.95x` slower and lacks `i686`/SEH; `-Os`/`-Oz` map to `O2` + `optsize`/`minsize` in LLVM 23.1.1; `684,912` TableGen lines (`18,412` x86, `9,846` AArch64 records). | 15 (`llvm-pass-ablation-speed-and-size-on-rust-code`, `rustc-llvm-pass-pipelines-and-configuration`, `llvm-scalar-memory-and-loop-optimization-proof-obligations`, `llvm-interprocedural-lto-and-codegen-optimization-obligations`, `candidate-optimizers-llvm-cranelift-and-gcc-backend-comparison`, `proven-baseline-compiler-candidates-and-reusable-verified-backends`, `llvm-tablegen-isa-extraction-and-verified-selector-reuse`, `rustc-pgo-mechanics-heuristics-value-and-ir-portability`, `rustc-lto-mechanics-symbol-preservation-and-performance-value`, `rustc-size-optimized-compilation-parity-and-transformations`, `rustc-benchmark-methodology-and-speed-size-baselines`) | `0` / `REASONING_ONLY` |
| **`D8` Tier 1 Platform Conventions** | 10 | Mechanize `FnAbi` rules across all 8 Tier 1 targets; verify DWARF `.eh_frame`/LSDA (ELF), `__unwind_info` (Mach-O), `.pdata`/`.xdata` `__CxxFrameHandler3` funclets (Windows x64/ARM64/gnu), and `fs:[0]` SEH (`i686-pc-windows-msvc`); implement all 4 TLS models, stack probes, CRT startup, and Linux-hosted `rust-lld` cross-compilation. | 16-pair live caller $\times$ callee ABI matrix achieves `100%` execution parity on standard types; all 4 unwinding table formats decoded and verified; all 8 Tier 1 targets cross-compiled and linked from a single `x86_64` Linux host via `lld` (`ld.lld`, `ld64.lld`, `lld-link`) using EULA-free headers/import stubs. | 18 (`tier1-calling-conventions-fnabi-and-llvm-lowering`, `abi-cross-testing-matrix-rustc-llvm-cranelift-gcc-clang`, `unwinding-on-elf-and-macho-targets`, `unwinding-on-windows-targets-and-32bit-seh`, `rust-thread-local-storage-models-and-runtime-contracts`, `rust-stack-discipline-probes-red-zones-and-overflow`, `rust-program-startup-runtime-objects-and-entry-state`, `rustc-object-files-sections-symbols-comdats-and-relocations`, `rustc-static-linking-archive-formats-and-linker-driver`, `rustc-dynamic-linking-loader-contracts-and-code-signing`, `tier1-linux-hosted-cross-compilation-recipes-and-sysroots`, `tier1-default-codegen-settings-and-target-options`, `os-syscall-interfaces-asynchronous-signals-and-environment-models`) | `0` / `REASONING_ONLY` |
| **`D9` Intrinsics, Assembly & ISA Models** | 11, 12 | Lower 316 `#[rustc_intrinsic]` and 81 `simd_*` operations via two-layer semantics; generate `core::arch` SIMD specs from vendored Intel XML (`6.7 MB`) and Arm JSON (`5.1 MB`); enforce frame-preserving contracts on `asm!` and ISA-level contracts on privileged/naked asm; encode full ISA models in Lean 4 via family-stratified tag-record dispatch. | 316 compiler intrinsics, 81 `simd_*`, 8,115 `core_arch` LLVM bindings across 74 x86 and 90 AArch64 features; 32-intrinsic Lean 4 + hardware co-execution pilot (`100%` match over `32,000` vectors); top 65 x86-64 and 55 AArch64 mnemonics cover `>99.2%` of `-O3` instructions; family-stratified tag-record Lean 4 ISA models elaborate $K=2,000$ opcodes in `2.66s–4.30s` (`524–672 MB` RSS) vs. $O(K^2)$ cliff at $K=500$ (`21.02s`) for monolithic inductives. | 18 (`rustc-intrinsics-simd-and-arch-semantic-sources`, `vendor-intrinsic-specifications-stdarch-verification-and-lean-generation`, `llvm-instruction-selection-fallbacks-and-libcall-contracts`, `target-features-implications-detection-and-abi-effects`, `rustc-inline-assembly-specification-llvm-lowering-and-assembler-syntax`, `rust-ecosystem-inline-assembly-global-asm-and-naked-function-census`, `machine-code-verification-frameworks-and-assembly-contracts`, `formal-isa-models-x86-64-i386-and-aarch64-coverage`, `isa-model-hardware-validation-divergences-errata-and-resources`, `llvm-compiled-rust-instruction-and-addressing-mode-frequencies`, `verified-assemblers-encoders-linkers-and-object-format-models`, `lean-large-isa-and-compiler-semantics-scaling`) | `0` / `REASONING_ONLY` |
| **`D10` Composite Routing & Attestation** | 13 | Composite `CodegenBackend` routing `MonoItem`s per function/CGU across the LLVM-free backend, Validated LLVM, and explicit fallback; enforce 42 cross-path LLVM attribute obligations; require `--icf=safe`; emit non-allocatable `.note.anneal.manifest` and detached `.anneal-bundle.tar.zst` attestations. | `98.4%` of linked executable `.text` bytes come from Rust CGUs (`1.6%` CRT stubs); `--gc-sections` prunes `74%–89%` of unused stdlib symbols before proof checking; `--icf=all` is unsound for address-compared Rust `fn` pointers; entire sysroot compiles without LLVM when 42 `compiler_builtins` asm/naked sites use ISA contracts. | 11 (`rustc-codegen-backend-routing-and-mixed-backend-interoperability`, `rustc-llvm-ir-attributes-metadata-and-cross-path-obligations`, `rustc-binary-origin-attribution-gc-sections-and-icf-soundness`, `binary-evidence-packaging-provenance-attestations-and-rustc-reproducibility`, `rustc-llvm-free-sysroot-cranelift-gcc-and-host-tools-audit`, `rustc-dwarf-codeview-debuginfo-emission-and-debugger-contracts`, `rustc-tier1-security-hardening-and-mitigation-codegen`) | `0` / `REASONING_ONLY` |
| **`D11` Normal Compilation & Demand** | 14, 16 | Support all 4 standard Cargo profiles (`dev`, `release`, `test`, `bench`), `opt-level=0..3/s/z`, Thin/Fat LTO, PGO, `panic=unwind/abort`, and DWARF/CodeView debuginfo; tune loop/scalar rules around the 8 hot Rust kernel families and slice bounds-check elimination idioms. | Across top-100 crates.io download-weighted census (`1,129`-crate closure), `94.2%` of crates use zero inline `asm!`; `-O0` emits 40 `panic_bounds_check` calls across the 8 kernel domains, and LLVM `-O3` eliminates `100%` (`13 / 13`) of slice-iterator/length-guarded bounds checks; `-C target-cpu=x86-64-v3` yields `1.18x–2.41x` SIMD speedups. | 8 (`cargo-profile-and-compiler-flag-census-in-the-wild`, `rustc-standard-library-codegen-demand-per-target`, `crates-io-download-weighted-codegen-demand-census`, `where-time-goes-in-rust-programs-hot-patterns-and-instruction-mix`) | `0` / `REASONING_ONLY` |
| **`D12` Validation & Validated LLVM** | 19, 21, 22, 23, 24 | 5-stage validation pipeline: 28,412 classified `compiletest` tests across native/QEMU/Wine/`remote-test-server`, `rustlantis`/`RustSmith`/`abi-cafe` fuzzing against Miri + LLVM, Crater + `stage0->stage2` self-hosting, multi-seed `--shuffle-sections` parity gates, and optional Validated LLVM tier (MIR-to-LLVM SMT validator + per-pass scalar/memory Alive2). | 28,412 `rustc 1.99.1` tests classified; `Runtime(PostCleanup)` MIR-to-LLVM-IR SMT prototype validates `100%` (`10 / 10`) of tested archetypes; Alive2 validates `94.4%` (`17 / 18`) of single scalar/memory/CFG pass groups (`66.7%` on LoopVectorize, `44.4%` whole `-O3`); instrumenting all 131 LLVM 23.1.1 pass modules (`574,990` LOC, `4,655` mutation sites) would require ~`115k–165k` C++ LOC; layout noise $\sigma_{\text{layout}}$ reaches `20.57%` (`69.97%` max/min spread). | 10 (`rustc-experimental-corpora-and-harness-conventions`, `rustc-compiletest-bootstrap-and-alternate-backend-test-mechanics`, `rustc-test-suite-machine-readable-classification`, `compiler-differential-testing-fuzzing-reduction-and-bug-records`, `ecosystem-scale-testing-crater-self-hosting-and-flakiness`, `tier1-target-test-execution-emulators-and-combinatorial-coverage`, `concurrency-and-simd-compiler-testing-tools-and-harnesses`, `black-box-translation-validation-alive2-and-mir-to-llvm-on-rust`, `llvm-derivation-emission-instrumentation-architecture-and-cost`, `llvm-ir-baseline-formal-semantics-and-ambiguities`) | `0` / `REASONING_ONLY` |
| **`D13` Substrate, Milestones & Horizons** | 20, 25, 26, 27 | Hybrid substrate: Lean `v4.34.1` (`leanc -O3` with `IO.Ref Array` FBIP mutation) for specifications, `HybridTrace` checker, and soundness/completeness proofs + Rust `1.99.1` for untrusted bit-packed optimizer passes + dual audit checking (`nanoda_lib`, `lean4lean`); Apache-2.0 OR MIT licensing; ISO 26262 TCL3 / DO-178C TQL-1 qualification; 11 milestones. | Compiled Lean `4.34.1` is within `1.10x` of Rust `1.99.1` on `IO.Ref Array` CFG dominator trees (`0.284 ms` vs. `0.259 ms`) and `2.94x–8.53x` on persistent trees/hash-consing, while Rust is `28.34x` faster on packed `u64` bitset liveness (`0.289 ms` vs. `8.191 ms`); all 6 kill criteria retired; future horizons (verified frontend, safe Rust UB-freedom over `14,812` stdlib `unsafe` blocks, cross-language LTO) interface cleanly at `.anneal-mir` / `MiniSSA`. | 15 (`lean-native-compilation-pipeline-runtime-and-trust-surface`, `independent-proof-checkers-and-smaller-trusted-computing-bases`, `compiler-substrate-benchmarks-lean-rust-and-ocaml`, `verified-compiler-effort-precedents-and-agent-proof-productivity`, `compiler-isa-sdk-licensing-trademarks-and-upstream-governance`, `compiler-qualification-assurance-cases-and-deviation-policies`, `verified-rust-frontend-approaches-trait-solver-polonius-and-thir-lowering`, `safe-rust-ub-freedom-soundness-and-standard-library-verification`, `cross-language-lto-linker-plugin-bitcode-and-llvm-ir-semantics`, `verified-rustc-designer-dry-run-and-gap-analysis`) | `0` / `REASONING_ONLY` |

---

### 2. Resolution of the Eight Core Cross-Cutting Architectural Tensions

Basis: source + execution + derived

Every cross-cutting tension identified in the research goals is resolved by
empirical corpus measurements without requiring additional external
investigation:

1. **`TENSION-1` (`-O3` Parity vs. Proof-System Expressiveness):**
   - *Corpus facts:* `llvm-pass-ablation-speed-and-size-on-rust-code` proves
     that 6 pass groups (`G1_Inlining`, `G2_SROA_Mem2Reg`, `G3_InstCombine`,
     `G4_SimplifyCFG`, `G6_LoopOpt_LICM`, `G7_Vectorization`) deliver `>99%` of
     LLVM 23.1.1's `11.71x` `-O3` speedup.
     `llvm-o3-derivation-formats-expressiveness-and-checking-cost` demonstrates
     that pure cut-point simulation (`SimCert`) covers only `8 / 12` (`66.7%`)
     of representative `-O3` transformations, whereas `HybridTrace` (combining
     rewrite traces, acyclic e-graph congruence explanations, and decidable
     side-condition checkers) covers `12 / 12` (`100%`), including
     `LoopVectorize` with runtime SCEV alias checks, `GVN + LICM` under scoped
     `noalias`, inlining across `cleanup` unwind edges, and C11/LLVM atomic
     access coalescing.
   - *Design decision:* Standardize on `HybridTrace` over `MiniSSA` and
     `MiniMach`, backed by `lean-derivation-checker-soundness-and-completeness-prototype`'s
     verified soundness (`checkDeriv_sound`) and completeness
     (`checkDeriv_complete`) architecture.
2. **`TENSION-2` (Full Derivations vs. Compile Time, Certificate Size, and Kernel Checking Speed):**
   - *Corpus facts:* `HybridTrace` encodes derivations at `24.77 B/step` raw and
     `12.04 B/step` zstd-compressed (`2.50x` smaller than `RelJudg`).
     `rustc-build-ir-and-pass-transformation-volume-statistics` shows that
     pre-compiling and caching `HybridTrace` certificates for the Tier 1 sysroot
     (`core` + `alloc` + `std`, ~`249k` machine instructions) requires only
     ~`3.6 MB` compressed per target.
     `lean-kernel-derivation-scale-checking-and-reflection-throughput` proves
     that CPS-forced reflection with 12-steps/limb packed `NatGMP` literals
     (`ReflPacked_NatGMP`) avoids Lean `v4.34.1`'s call-by-name WHNF stack cliff
     and checks $10^6$ derivation steps in `11.89s` (`84,118` steps/sec, `524 MB`
     RSS) inside the Lean C++ kernel and at `2.13M` steps/sec in natively
     compiled Lean.
   - *Design decision:* Run the natively compiled Lean `HybridTrace` checker by
     default during normal builds (`~1.5s` for a full sysroot-scale workload),
     cache per-function derivations in `.rlib` archives keyed by `.anneal-mir`
     SHA-256 digests, and invoke `ReflPacked_NatGMP` kernel replay (plus
     `nanoda_lib`) in offline audit mode.
3. **`TENSION-3` (Reusing Existing Optimizers vs. Clean-Slate Derivation Generation):**
   - *Corpus facts:* `candidate-optimizers-llvm-cranelift-and-gcc-backend-comparison`
     shows Cranelift `0.121` is `11.95x` slower than LLVM `-O3` on vectorizable
     compute kernels and lacks `i686` and Windows 32-bit SEH, while GCC `14.2`
     lacks MSVC targets and is GPLv3+. Meanwhile,
     `llvm-derivation-emission-instrumentation-architecture-and-cost` shows that
     instrumenting all 131 LLVM 23.1.1 pass modules (`574,990` C++ LOC, `4,655`
     mutation sites) requires `~115k–165k` LOC of invasive C++ hooks, whereas
     `black-box-translation-validation-alive2-and-mir-to-llvm-on-rust` achieves
     `100%` SMT validation on `Runtime(PostCleanup)` MIR-to-LLVM-IR lowering and
     `94.4%` (`17 / 18`) on single scalar/memory/CFG LLVM pass groups.
   - *Design decision:* Build the primary LLVM-free backend as a clean-slate
     derivation-emitting `MiniSSA`/`MiniMach` pipeline (seeded by a verified
     single-pass baseline lowerer and imported LLVM 23.1.1 TableGen descriptions
     from `llvm-tablegen-isa-extraction-and-verified-selector-reuse`), and offer
     the optional **Validated LLVM tier** using the MIR-to-LLVM SMT validator
     plus per-pass Alive2 + remark-assisted loop/LTO certificates on the 28
     parity-critical LLVM pass modules.
4. **`TENSION-4` (Whole-Program LTO vs. Compositional Per-Function Guarantees):**
   - *Corpus facts:* `compositional-correctness-linking-and-whole-program-optimization`
     and `rustc-lto-mechanics-symbol-preservation-and-performance-value` show
     that `rustc 1.99.1`'s `Lto::ThinLocal`, `Lto::Thin`, and `Lto::Fat` modes
     rely on explicit export lists (`exported_symbols::collect`) to govern
     `internalize`, cross-module inlining, dead-global elimination, and
     closed-world devirtualization.
   - *Design decision:* Parameterize per-function open simulation theorems by an
     explicit `ModuleSummary` / `ExportList` contract (mechanized in
     `CompositionalLinkingAndThinLtoWpoProbe.lean`), discharging closed-world
     internalization assumptions at the link-Step composition boundary.
5. **`TENSION-5` (Aliasing Model Optimization Power vs. Ecosystem UB Rate and Anneal Proof Burden):**
   - *Corpus facts:* `rust-aliasing-models-ub-prevalence-and-llvm-optimization-value`
     shows that `63.0%` (`4,969 / 7,887`) of ecosystem Miri UB failures come
     from Stacked Borrows subobject provenance shrinking (`37.4%`) and eager
     `Unique` retag invalidation (`25.6%`), both of which Tree Borrows permits
     by keeping unactivated `Reserved` mutable references readable/writable
     through parent pointers until the first child write, while preserving the
     `1.14x–1.38x` `noalias` speedup on memory-bound kernels.
   - *Design decision:* Adopt **Tree Borrows** with two-stage function-entry
     protector release (`tree-borrows-two-stage-protector-release-and-reborrow-contracts`)
     as the shared aliasing model for both Anneal and `MiniSSA`, with a
     `-Zverified-aliasing=none` fallback mode that strips `noalias` attributes
     for legacy unsafe crates that intentionally violate reference aliasing.
6. **`TENSION-6` (Privileged and Inline Assembly vs. Abstract MIR Memory Model):**
   - *Corpus facts:* `rust-ecosystem-inline-assembly-global-asm-and-naked-function-census`
     shows `94.2%` of download-weighted crates.io packages contain zero inline
     assembly, while `std` (11 files) and `compiler_builtins` (42 sites across
     13 files) use `asm!`, `global_asm!`, and `#[unsafe(naked)]`.
   - *Design decision:* Govern user-mode `asm!` blocks by the frame-preserving
     operand/clobber/options interface (`nomem`, `readonly`, `preserves_flags`,
     `nostack`, `noreturn`, `may_unwind`) mechanized in `SEAM-2` of
     `end-to-end-verified-mir-to-isa-refinement-chain-and-seams`, and verify
     privileged, `global_asm!`, and `#[unsafe(naked)]` blocks directly against
     the target ISA model via Islaris/`s2n-bignum`-style machine-code contracts
     (`machine-code-verification-frameworks-and-assembly-contracts`).
7. **`TENSION-7` (Broad Tier 1 ISA Coverage vs. Lean 4 Kernel Scaling and Hardware Validation):**
   - *Corpus facts:* `lean-large-isa-and-compiler-semantics-scaling` proves that
     monolithic `inductive Inst` + `match` encodings hit a quadratic $O(K^2)$
     elaboration cliff in Lean `v4.34.1` at $K = 500$ opcodes (`21.02s`,
     `1.51 GB` RSS) and fail at $K = 1,000$, whereas **family-stratified
     dispatch** (`20` families $\times$ `100` opcodes) elaborates $K = 2,000$
     opcodes in `4.30s` (`672 MB` RSS) and **tag-record table lookup**
     elaborates $K = 2,000$ in `2.66s` (`524 MB` RSS) while executing at
     `31.1M` steps/sec.
   - *Design decision:* Represent the x86-64, i386, and AArch64 ISA semantics in
     Lean `v4.34.1` using family-stratified tag-record dispatch, prioritizing
     the top 65 x86-64 and 55 AArch64 mnemonics (`>99.2%` of `-O3` instructions)
     for foundational manual audit and generating the remaining SIMD/vector
     extensions from vendored Intel XML (`x86-intel.xml`) and Arm ASL
     (`arm_intrinsics.json`) validated by hardware co-execution.
8. **`TENSION-8` (Shared Verifier-Compiler MIR Identity vs. Production Build Pipelines):**
   - *Corpus facts:* `rustc-mir-artifact-export-settings-and-proof-binding`
     demonstrates that standard `.rmeta` files omit non-generic bodies and store
     post-optimization MIR, whereas capturing `Runtime(PostCleanup)` MIR before
     `optimized_mir` steals the `Steal<Body>` query preserves the exact MIR
     checked by Anneal.
   - *Design decision:* Embed a content-addressed `.anneal-mir` section in every
     `.rlib`/`.rmeta` produced in verified mode and verify its SHA-256 digest
      inside both the per-function derivation checker and the final binary
     attestation bundler (`binary-evidence-packaging-provenance-attestations-and-rustc-reproducibility`).

---

### 3. Phased 11-Milestone Implementation Roadmap and Retired Kill Criteria

Basis: derived

Combining the effort ratios from
`verified-compiler-effort-precedents-and-agent-proof-productivity`, the
substrate benchmarks from `compiler-substrate-benchmarks-lean-rust-and-ocaml`,
and the pass priorities from `llvm-pass-ablation-speed-and-size-on-rust-code`
yields an 11-milestone sequence where every milestone delivers standalone
verification value:

1. **Milestone 1 — `.anneal-mir` Exporter & 5-Link End-to-End Fixture Chain:** Ship the
   deterministic `Runtime(PostCleanup)` `.anneal-mir` exporter in
   `rustc 1.99.1` and generalize the 5-link `end-to-end-verified-mir-to-isa-refinement-chain-and-seams`
   Lean `v4.34.1` theorem across scalar, reference, and call fixtures.
2. **Milestone 2 — Proven Single-Pass Baseline Backend (`x86_64-unknown-linux-gnu`):**
   Complete the universally verified `Runtime(PostCleanup)` MIR $\rightarrow$
   `MiniMach` $\rightarrow$ `x86-64` baseline lowerer (the zero-bug fallback
   safety net for all subsequent optimizer passes).
3. **Milestone 3 — `HybridTrace` Checker Soundness, Completeness & `ReflPacked_NatGMP` Kernel Audit:**
   Scale `lean-derivation-checker-soundness-and-completeness-prototype` to full
   `MiniSSA` and `MiniMach` with `ReflPacked_NatGMP` kernel reflection and
   `nanoda_lib` dual checking.
4. **Milestone 4 — Top-Ranked Scalar & Memory Optimizations (`SROA`, `Mem2Reg`, `InstCombine`, `SimplifyCFG`, `EarlyCSE/GVN`):**
   Implement derivation-emitting scalar/memory passes and acyclic e-graph
   rewrites, plus the optional Validated LLVM tier's MIR-to-LLVM-IR and
   scalar/memory Alive2 validators.
5. **Milestone 5 — Interprocedural Inlining, `TreeBorrows` `noalias`, and `panic_bounds_check` Elimination:**
   Implement derivation-emitting call-site inlining (`79.3%` call-site reduction
   at `-O3`), Tree Borrows two-stage protector `noalias` propagation, and
   `IndVarSimplify` slice bounds-check elimination.
6. **Milestone 6 — Loops, `LICM`, `LoopUnroll`, and `LoopVectorize` / `SLPVectorizer`:**
   Implement derivation-emitting loop optimizations and vectorization with
   runtime SCEV alias checks, closing the remaining gap to `-O3` compute speed.
7. **Milestone 7 — Concurrency, Atomics, Intrinsics, and Vendor SIMD (`x86_64` & `AArch64`):**
   Integrate RC11/IMM + Promising thread-local atomic simulation, the 316
   `#[rustc_intrinsic]` / 81 `simd_*` lowerings, and generated Intel XML / Arm
   JSON SIMD semantics.
8. **Milestone 8 — Platform Unwinding, TLS, Stack Probes, and All 8 Tier 1 Targets:**
   Extend `FnAbi`, DWARF `.eh_frame`, Mach-O `__unwind_info`, Windows
   `.pdata`/`.xdata` (`__CxxFrameHandler3`), 32-bit `i686-pc-windows-msvc`
   `fs:[0]` SEH, TLS models, and `rust-lld` cross-compilation across all 8 Tier
   1 targets.
9. **Milestone 9 — LLVM-Free Sysroot (`core`, `alloc`, `std`, `compiler_builtins`) & Composite Backend Routing:**
   Compile the complete Tier 1 sysroot without LLVM, activate per-function
   composite routing (`-Zverified-functions`), and emit `.note.anneal.manifest`
   attestations.
10. **Milestone 10 — Whole-Program `ThinLTO` / `FatLTO`, IR-Portable `PGO`, and `-Os`/`-Oz` Size Parity:**
    Enable cross-crate `.anneal-mir` summary importing, `ExportList`-parameterized
    internalization/devirtualization, and IR-portable CFG profile consumption.
11. **Milestone 11 — Full `compiletest`, Differential Fuzzing, Crater, Self-Hosting, and Multi-Seed Parity Qualification:**
    Pass the classified `compiletest` suite across all 8 Tier 1 targets,
    `rustlantis`/`abi-cafe` fuzzing campaigns, `stage0` $\rightarrow$ `stage2`
    self-hosting, and multi-seed `--shuffle-sections` `-O3`/`-Os`/`-Oz` parity
    gates.

## Boundaries

- **Stopping boundary (`brainstorm / plan only` for new seed generation):**
  Because the dry-run synthesis verified that all 13 decision domains and all
  27 research goals are backed by primary-source evidence and executable probes
  in the 107 `compilers/verified-rustc` corpus packages (`0` unrecorded external
  facts), zero follow-up research seeds are generated.
- **Proprietary target hardware and click-through EULAs (`not examined` by direct execution on proprietary hosts):**
  As documented in the platform and ISA validation reports
  (`tier1-linux-hosted-cross-compilation-recipes-and-sysroots`,
  `tier1-target-test-execution-emulators-and-combinatorial-coverage`, and
  `isa-model-hardware-validation-divergences-errata-and-resources`), cross-compilation,
  binary table verification, and user-mode emulation (`qemu-aarch64`,
  `qemu-i386`) were executed on the `x86_64` Linux host without accepting
  proprietary Apple Xcode SDK or Microsoft Windows SDK/MSVC click-through EULAs;
  native Apple Silicon M-series and Windows ARM64 hardware execution remain part
  of target deployment infrastructure rather than unrecorded specification gaps.

## Evidence

- **Machine-readable decision and goal coverage matrix:**
  `support/decision_coverage_matrix.json` maps all 13 decision domains
  (`D1`–`D13`), all 27 research goals (`G1`–`G27`), and all 8 cross-cutting
  design tensions (`TENSION-1`–`TENSION-8`) to the exact 107
  `compilers/verified-rustc` packages (and 67 foundational Anneal, MiniRust, and
  Lean 4 packages) in `CATALOG.json`.
- **Automated dry-run verification script:**
  `support/verify_dry_run_coverage.py` programmatically audits
  `support/decision_coverage_matrix.json` against `CATALOG.json`, confirming
  that all 13 decision domains, 27 goals, and 107 `compilers/verified-rustc`
  packages are mapped with `unrecorded_external_facts = 0` and
  `new_seeds_required = 0`.

## Revalidation

To re-verify that all 13 architectural decision domains, 27 research goals, and
107 `compilers/verified-rustc` corpus packages remain completely mapped with
zero unrecorded external facts, run:

```console
python3 reports/verified-rustc-designer-dry-run-and-gap-analysis/support/verify_dry_run_coverage.py
```
