# Empirical Ground-Truth Measurements of `rustc` Cross-Release ABI Drift, Full-Byte Binary Validation, Debuginfo-Free CFG Alignment, and Post-`-O3` Surviving Bounds Checks

## Summary

Four foundational architectural assumptions for a drop-in verified `rustc` backend—(1) `x86_64` cross-release ABI invariance across adjacent `rustc` releases, (2) high-speed linear-scan machine-code validation across sysroot `.rlib` archives and linked executables, (3) debuginfo-free (`-C debuginfo=0`) structural Weisfeiler–Leman (1-WL) CFG alignment between pre- and post-`-O3` LLVM IR, and (4) intra-procedural linear-Farkas bounds-check elimination (BCE) yield on post-`-O3` Rust code—were tested directly on real `rustc 1.99.1`, `rustc 1.100.0`, and `rustc 1.102.0-nightly` compiler outputs (`x86_64-unknown-linux-gnu`, plus `i686-unknown-linux-gnu` and `aarch64-unknown-linux-gnu` cross-target lowering). All four prior optimistic assumptions fail under direct compiler measurement:

1. **Cross-Release `x86_64` ABI Drift Is Real Even Between Adjacent Stable Releases (`1.99.1 -> 1.100.0`):** Compiling all `256` procedural Rust ABI archetypes live under `rustc 1.99.1` (`58cf8f9c35b3`), `rustc 1.100.0` (`0ef1bc386059`), and `rustc 1.102.0-nightly` (`3ef0c22cdb86`) reveals `255 / 256` (`99.61%`) preservation from `1.99.1` to `1.100.0` with **one silent breaking `x86_64` `extern "Rust"` ABI change**: `#[repr(simd)]` (`f4_simd_f32x4_rust`) switched from indirect `void (ptr sret([16 x i8]) align 16, ptr align 16)` in `1.99.1` to register-passed `<4 x float> (<4 x float>)` (LLVM-aliased to `extern "C"`) in `1.100.0`. Between `1.100.0` and `1.102.0-nightly`, `252 / 256` (`98.44%`) match, with **`4` breaking `extern "vectorcall"` / `"vectorcall-unwind"` symbol-mangling changes** adding MSVC `@@40`/`@@48` suffixes even on `x86_64-unknown-linux-gnu`.
2. **Full-Byte Machine-Code Validation Disproves Archive-Denominator Throughput and Exposes Three Linear-Scan Failure Modes:** Decoding `100%` of executable `.text` across all `30` `rustc 1.99.1` `x86_64-unknown-linux-gnu` sysroot `.rlib`s (`51.84 MB` total archive size, of which only `1.64 MB` = `3.16%` is actual `.text`: `427,075` instructions across `5,079` functions) plus real multi-MB linked executables (`anneal-audit` `2.17 MB`, `cargo-anneal` `3.65 MB`) achieves **`0.217 MB/s`** on unpacked `.rlib`s (`7.57s`) and **`0.770–0.793 MB/s`** on linked binaries via `llvm-objdump` + Python (`4/4` planted-fault negative controls caught; `0` invalid decodes across `1,323,621` instructions). Real binaries prove three mandatory validator requirements: (a) checking only `call __rust_probestack` yields `60` false positives on LLVM inline stack probes (`sub $0x1000, %rsp` in `driftsort_main`, `gimli`, `tar`) while genuinely flagging real unprobed C-FFI stack frames (`zstd-sys` `HUF_decompress`: `25,496 B`; `ZSTDv01_decompress`: `10,336 B`); (b) linear-scan `vzeroupper` checks false-positive on `memchr::find_avx2`'s early non-AVX2 `retq` (`0x12f924`, versus actual `vzeroupper; retq` at `0x12fcb6`), requiring CFG-aware dataflow; and (c) ELF executable validators must whitelist glibc `_start`'s post-`__libc_start_main` trap `hlt` (`0xf4`).
3. **Debuginfo-Free (`-C debuginfo=0`) 1-WL Structural CFG Alignment Collapses Across `-O0 -> -O3` (`10.37%` BB Recall):** Compiling real `library/core` at `-O0`, `-O1`, `-O2`, and `-O3` with `-C debuginfo=0` reduces `2,954` `-O0` functions to `543` surviving `-O3` functions (`81.6%` inlined/eliminated). Across all `530` surviving non-trivial (`>= 2` BBs) functions (`4,665` pre-BBs → `5,740` post-BBs), 1-WL basic-block micro-recall is **`10.37%`** (`11.13%` exact CFG match, **`2.50%` blind Top-1 function retrieval**). Even `-O0 -> -O1` collapses to `13.34%` BB micro-recall (`2.50%` Top-1); only `-O2 -> -O3` (post-SROA/Mem2Reg/Inlining) reaches `68.98%` BB recall (`66.67%` Top-1). Post-hoc debuginfo-free alignment cannot bridge unoptimized MIR to post-`-O3` LLVM IR.
4. **Post-`-O3` Surviving Bounds Checks Are Sparse (`0.044`/fn) and Predominantly Memory-Load-Dependent (`60.8%`):** Scanning `127` real compiled `.ll` files (`41,408` post-`-O3` LLVM 23.1.1 functions across `libcore`, `rustls`, `ring`, `miniz_oxide`, `memchr`, `base64`, `ureq`, `clap_builder`, `toml_parser`, `serde_json`, `syn`, `anneal-audit`, `cargo-anneal`, etc., strictly excluding LLVM `; call` comment lines) finds **`1,807` surviving bounds checks** (`926` `panic_bounds_check` + `881` `slice_index_fail`). Exactly **`60.8%` (`1,098`)** are dominated by heap/struct memory loads (beyond intra-procedural linear Farkas without memory/container invariants), `14.6%` (`263`) by loop-`phi` induction, `14.2%` (`256`) by bitwise masks/shifts (spiking to `31.0%` in `libcore`, `55.5%` in `miniz_oxide`, `73.3%` in `base64`), `9.0%` (`163`) by direct argument comparisons, `1.3%` (`24`) by cold paths, and **`0.17%` (`3`)** by modulo/remainder.

---

## Applicability

All measurements were executed natively on `x86_64-unknown-linux-gnu` (`2026-11-20`) using stock installed `rustup` toolchains and system `llvm-objdump` / `ar` / `as`:

- **`rustc 1.99.1`** (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, bundled `LLVM 23.1.1`) — primary baseline for all four experiments (`sysroot` `.rlib` validation, `libcore` `-O0/-O1/-O2/-O3` alignment, `41,408`-function BCE census, and `256`-signature ABI lowering on `x86_64`, `i686`, and `aarch64`).
- **`rustc 1.100.0`** (`rust-lang/rust@0ef1bc386059596dada8fb65b50425aab2ea637a`, bundled `LLVM 23.1.5`) and **`rustc 1.102.0-nightly`** (`rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, bundled `LLVM 23.1.5`) — cross-release `x86_64` ABI differential comparisons.
- **`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`** — source workspace compiled at `--release` (`anneal-audit`, `cargo-anneal`, and all transitive `crates.io` dependencies) for the real-world linked-binary validation and post-`-O3` surviving bounds-check censuses.

These measurements supersede earlier synthetic projections on these four surfaces; complementary primary-source MIR/LLVM IR structural statistics appear in `rustc-postcleanup-mir-and-llvm-poison-freeze-ground-truth-census`.

---

## Findings

### 1. Cross-Release `rustc` ABI Stability (`256/256` Procedural Archetypes)

`Basis: execution (rustc +1.99.1, +1.100.0, +nightly --emit=llvm-ir -C opt-level=2 on all 256 B6 procedural ABI archetypes in support/e1_5_cross_release_abi_diff.json)`

Parsing **both** LLVM `define` declarations and LLVM `unnamed_addr alias` entries (essential because LLVM's `MergeFunctions` pass collapses identical lowered functions into aliases, hiding ABI shifts if only `define` lines are inspected) accounts for `256 / 256` symbols on every tested toolchain and target:

| Toolchain & Target | Parsed Symbols (`define` + `alias`) | `sret(...)` (`define`s) | `byval(...)` (`define`s) | `inreg` (`define`s) | Cross-Release Drift vs. `1.99.1` (`x86_64`) |
| :--- | ---: | ---: | ---: | ---: | :--- |
| **`rustc 1.99.1` (`x86_64-unknown-linux-gnu`)** | `256` (`117` `define` + `139` `alias`) | `19` | `8` | `0` | Baseline |
| **`rustc 1.100.0` (`x86_64-unknown-linux-gnu`)** | `256` (`116` `define` + `140` `alias`) | `18` | `8` | `0` | **`1` breaking ABI change** (`255/256` = `99.61%` match) |
| **`rustc 1.102.0-nightly` (`x86_64-unknown-linux-gnu`)** | `256` (`116` `define` + `140` `alias`) | `18` | `8` | `0` | **`5` breaking ABI/mangling changes** (`251/256` = `98.05%` match) |
| **`rustc 1.99.1` (`i686-unknown-linux-gnu`)** | `256` (`128` `define` + `128` `alias`) | **`61`** (`47.7%` of `define`s) | `27` | `2` | Cross-target `i686` baseline (`3.2x` more `sret` than `x86_64`) |
| **`rustc 1.99.1` (`aarch64-unknown-linux-gnu`)** | `256` (`127` `define` + `129` `alias`) | `15` | `0` | `0` | Cross-target `aarch64` baseline |

Exact observed breaking changes on `x86_64-unknown-linux-gnu`:

1. **`1.99.1 -> 1.100.0` (`f4_simd_f32x4_rust`, `extern "Rust"` `#[repr(simd)]`):**
   - `rustc 1.99.1`: `define void @f4_simd_f32x4_rust(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([16 x i8]) align 16 ... %_0, ptr ... align 16 %v)` (passed via memory pointer, returned via hidden `sret` pointer).
   - `rustc 1.100.0` & `1.102.0-nightly`: `@f4_simd_f32x4_rust = unnamed_addr alias <4 x float> (<4 x float>), ptr @f4_simd_f32x4_c` (passed and returned directly in `%xmm0`).
   - **Implication:** Any cross-release `.rlib` compatibility claim asserting `100.0%` `x86_64` ABI preservation across adjacent `rustc` releases is empirically false. Automated ABI fingerprinting **must** hash the full resolved lowered signature across both `define` and `alias` targets and cannot exempt `x86_64` `extern "Rust"` SIMD functions.
2. **`1.100.0 -> 1.102.0-nightly` (`4` `extern "vectorcall"` / `"vectorcall-unwind"` symbols):**
   - `f6_x64_vectorcall_big`, `f6_x64_vectorcall_hfa`, `f6_x64_vectorcall_unwind_big`, and `f6_x64_vectorcall_unwind_hfa` changed ELF symbol names to MSVC-decorated `\01f6_x64_vectorcall_big@@48`, `\01f6_x64_vectorcall_hfa@@40`, `\01f6_x64_vectorcall_unwind_big@@48`, and `\01f6_x64_vectorcall_unwind_hfa@@40` on `x86_64-unknown-linux-gnu`.

### 2. Full-Byte Machine-Code & Post-Link Binary Validation (`100%` of Sysroot `.rlib`s + Linked Executables)

`Basis: execution (llvm-objdump -d full-section decoding of all 30 rustc 1.99.1 x86_64 sysroot .rlibs, anneal-audit, cargo-anneal, and 4 planted-fault .o negative controls in support/e1_3_real_binary_validator.json)`

Before scanning real artifacts, four synthetic x86-64 ELF `.o` negative controls (`0x06` invalid opcode in 64-bit mode, privileged `hlt`, unprobed `subq $0x4000, %rsp`, and `vxorps %ymm0, %ymm0, %ymm0; ret` without `vzeroupper`) were assembled and validated: **`4 / 4` planted faults were caught**.

Scanning `100%` of executable `.text` bytes across real Rust artifacts yields:

| Artifact Set | Total File Size | Actual Decoded `.text` | Decoded Insts | Functions | Elapsed | True `.text` MB/s | `bad_decode` | `priv_inst` | `large_frame_no_probe` | `ymm_ret_no_vzeroupper` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **All `30` `rustc 1.99.1` sysroot `.rlib`s** | `51.84 MB` | **`1.64 MB` (`3.16%`)** | `427,075` | `5,079` | `7.57s` | **`0.217 MB/s`** | `0` | `0` | `14` | `0` |
| **`anneal-audit` (`--release` ELF)** | `2.17 MB` | `1.41 MB` | `339,885` | `2,089` | `1.83s` | **`0.770 MB/s`** | `0` | `1` (`_start`) | `10` | `1` (`find_avx2`) |
| **`cargo-anneal` (`--release` ELF)** | `3.65 MB` | `2.18 MB` | `556,661` | `3,834` | `2.75s` | **`0.793 MB/s`** | `0` | `1` (`_start`) | `36` | `0` |

Inspecting every single flagged instruction in the real binaries yields four concrete engineering requirements for a verified post-link validator:

1. **Archive Size ≠ Executable Code Size:** Only `3.16%` (`1.64 MB` of `51.84 MB`) of `rustc 1.99.1`'s sysroot `.rlib` files is executable `.text`; the rest is `.rmeta` metadata, bitcode, and relocations. Dividing total archive megabytes by wall time inflates apparent decoding throughput by `>30x`. True `llvm-objdump` + Python `.text` validation throughput is `0.22–0.79 MB/s`; achieving `>50 MB/s` requires a compiled native byte decoder (Rust/C/compiled total Lean `ByteArray`), not spawning `llvm-objdump`.
2. **Inline Stack Probes vs. Real Unprobed C-FFI Stack Frames:** Every Rust-compiled `sub $0x1000, %rsp` (`4,096 B`) flagged in sysroot (`14` hits, including `___rust_probestack`, `driftsort_main`, `gimli::elf::Object::section`, `rustc_public_bridge::Body::fold_with`) and `anneal-audit` (`10` hits) uses LLVM's modern inline stack-probing (`probe-stack=inline-asm`), NOT `call __rust_probestack`. By contrast, in `cargo-anneal` the validator caught **genuinely unprobed large C stack frames** linked in via `zstd-sys`: **`HUF_decompress` (`25,496 B`)** and **`ZSTDv01_decompress` (`10,336 B`)**. A sound stack-probe validator must therefore perform abstract `rsp`/guard-page-touch tracking rather than grepping for `call __rust_probestack`, and must distinguish verified Rust `.text` sections from linked C FFI objects.
3. **Linear-Scan `vzeroupper` Fails on Real Multi-Exit AVX2 Functions:** The sole `ymm_ret_no_vzeroupper` hit (`memchr::arch::x86_64::memchr::count_raw::find_avx2` at `0x12f924: retq`) was manually disassembled (`0x12f910–0x12f92c` and `0x12fca0–0x12fcc0`): `0x12f924` is an **early return before entering any AVX2 `ymm` block**, whereas all AVX2 paths jump to `0x12fcb2` (`addq %r8, %rax; popq %rbx; vzeroupper; retq`). A sound `vzeroupper` checker MUST run **CFG-aware forward dataflow** (`ymm_dirty` lattice over basic blocks), never a linear disassembly scan.
4. **CRT Entry-Point `hlt` Whitelist:** Both linked executables contain exactly one `hlt` (`0xf4`) in glibc `_start` immediately following `call __libc_start_main`. A whole-binary validator must scope privileged-instruction bans to non-CRT code or permit unreachable post-`__libc_start_main` traps.

### 3. Debuginfo-Free (`-C debuginfo=0`) 1-WL Structural CFG Alignment Across Optimization Levels

`Basis: execution (rustc +1.99.1 -C debuginfo=0 --emit=llvm-ir on library/core at -O0, -O1, -O2, -O3 and anneal-audit at -O0/-O3 in support/e1_4_real_wl_cfg_alignment.json)`

We implemented genuine 3-round 1-Weisfeiler–Leman (1-WL) CFG vertex-color refinement (initial vertex label = `(in_deg, out_deg, terminator_opcode, sorted_unique_non_noise_opcodes)` excluding `alloca`/`bitcast`/`getelementptr`/`phi`/`llvm` noise; iterative neighborhood-hash refinement over predecessor and successor colors) and evaluated both unique 1-to-1 basic-block anchor recall and blind function retrieval (matching a stripped post-opt CFG against all `N` pre-opt CFGs by 1-WL color Jaccard similarity):

| Real `rustc 1.99.1` Comparison (`-C debuginfo=0`) | Pre Fns → Post Fns | Common Non-Trivial (`≥2` BBs) | Pre BBs → Post BBs | **1-WL 1:1 BB Micro-Recall** | **Exact Whole-CFG 1-WL Match** | Mean Opcode Jaccard | **Blind Fn Retrieval Top-1 / Top-5** (`n=120`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **`libcore` `-O0` vs. `-O1`** | `2,954 → 853` | `830` | `7,467 → 6,972` | **`13.34%`** | `9.88%` | `33.00%` | **`2.50%` / `4.17%`** |
| **`libcore` `-O0` vs. `-O2`** | `2,954 → 543` | `532` | `4,669 → 5,628` | **`10.61%`** | `11.09%` | `32.34%` | **`2.50%` / `7.50%`** |
| **`libcore` `-O0` vs. `-O3`** | `2,954 → 543` | `530` | `4,665 → 5,740` | **`10.37%`** | `11.13%` | `33.01%` | **`2.50%` / `6.67%`** |
| **`libcore` `-O2` vs. `-O3`** | `543 → 543` | `540` | `5,708 → 5,847` | **`68.98%`** | `79.07%` | `91.48%` | **`66.67%` / `83.33%`** |

**Architectural Conclusion:**
- `-O0 -> -O1` alone (`SROA` + `Mem2Reg` + `SimplifyCFG` + `InstCombine` + `EarlyCSE` + `Inline`) destroys `~87%` of 1-WL structural vertex invariants (`13.34%` BB micro-recall, `2.50%` blind Top-1 function retrieval), and `-O0 -> -O3` drops further to **`10.37%`** BB micro-recall while eliminating `81.6%` of functions via inlining and growing surviving function CFGs by `+23.0%` (`4,665 → 5,740` BBs).
- By contrast, `-O2 -> -O3` (where both sides are already post-SROA/Mem2Reg/Inlining) preserves `68.98%` BB recall (`79.07%` exact CFG match).
- **Consequence for untrusted LLVM oracles:** A verified compiler **cannot** rely on post-hoc `-C debuginfo=0` structural CFG alignment to recover MIR-to-`-O3` correspondences. Either (a) the compiler injects private synthetic origin metadata during its internal untrusted oracle run and strips it before emitting final user `.o` files (preserving `-C debuginfo=0` output bit-for-bit), or (b) oracle hints are extracted per single-pass / superblock boundary (`CompCert BTL` style) rather than across the full `-O0 -> -O3` chasm.

### 4. Real Post-`-O3` Surviving Bounds-Check Census (`41,408` Compiled Rust Functions)

`Basis: execution (rustc +1.99.1 -C opt-level=3 --emit=llvm-ir across libcore + anneal workspace + all transitive crates.io dependencies in support/e1_2a_real_bce_census.json)`

Filtering strictly to actual LLVM `call`/`tail call`/`musttail call`/`invoke` instructions (explicitly excluding `rustc`'s `; call ...` IR comment lines, which otherwise double-count every call!) across **`127` `.ll` files (`41,408` defined functions)** yields:

| Metric / Dominating Guard Class (25-Instruction Window) | Count | Share of Surviving Bounds Checks | Representative Crates & Patterns |
| :--- | ---: | ---: | :--- |
| **Total compiled post-`-O3` LLVM 23.1.1 functions** | `41,408` | — | `109` runtime crate `.ll` files (`38,455` fns) + `18` build scripts (`2,953` fns) |
| **Total surviving bounds checks** (`panic_bounds_check` `926` + `slice_index_fail` `881`) | **`1,807`** | `100.0%` (`0.044` / fn) | Also `1,256` `unwrap/expect_failed`, `41` `panic_const_div/rem_by_zero` |
| **`memory_load_dependent_in_window`** | **`1,098`** | **`60.76%`** | `rustls` (`240/294` = `81.6%`), `anneal_audit` (`43/58`), `syn` (`43/52`), `toml_parser` (`30/31`) |
| **`loop_phi_induction_in_window`** | **`263`** | **`14.55%`** | `clap_builder` (`62/93` = `66.7%`), `memchr` (`22/34` = `64.7%`), `core.ll` (`49/158` = `31.0%`) |
| **`bitwise_mask_or_shift_in_window`** | **`256`** | **`14.17%`** | `base64` (`11/15` = `73.3%`), `miniz_oxide` (`60/110` = `54.5%`), `core.ll` (`49/158` = `31.0%`) |
| **`direct_icmp_arg_or_expr`** | **`163`** | **`9.02%`** | Public API bounds checks on unvalidated caller arguments (`core::net::parser::read_ipv6_addr`) |
| **`other_or_unconditional_cold_path`** | **`24`** | **`1.33%`** | Outlined panic helpers / cold fallback paths |
| **`modulo_rem_in_window`** | **`3`** | **`0.17%`** | Exclusively `3` sites in `core.ll` (`0` across all `126` other crate `.ll` files) |

**Architectural Conclusion:**
- LLVM 23.1.1 `-O3` already eliminates the vast majority of trivial slice bounds checks (`0.044` surviving checks/fn across `41,408` functions; `crc32fast`, `zstd`, `adler2`, `zeroize` have `0` surviving checks).
- Among checks that **do** survive `-O3`, **`60.8%` depend on values loaded from heap/struct memory**—meaning purely intra-procedural linear Farkas certificates (`FarkasCertN`) CANNOT discharge the majority of real surviving checks unless coupled with container/struct validity invariants (e.g., `Vec` `len <= cap`, parser cursor invariants) or user-supplied preconditions.
- Conversely, in hot byte-processing crates (`miniz_oxide` `54.5%`, `base64` `73.3%`, `libcore` `31.0%`), **bitwise mask/shift checks** (`14.2%` overall) and **loop-induction checks** (`14.6%` overall; `memchr` `64.7%`, `clap_builder` `66.7%`) represent the genuine high-ROI targets for verified `BitDomain` + `FarkasCertN` discharge, whereas modulo/remainder checks are negligible (`0.17%`).

### 5. Performance, Comprehensibility, and Validation Summary (`L1`–`L6`, `C1`–`C2`, `V1`–`V4`)

- **`L2` / `L3` / `L5` / `L6`:** `Basis: execution` — Compiling `anneal` + all transitive `crates.io` deps with `RUSTFLAGS="--emit=llvm-ir"` (`rustc 1.99.1 --release`) completed in `23.69s`; full-byte `llvm-objdump` validation of all `30` sysroot `.rlib`s took `7.57s` (`0.217 MB/s` `.text`) and `1.83s`/`2.75s` for `anneal-audit`/`cargo-anneal` (`0.77–0.79 MB/s`). `L1`/`L4` (proof authoring effort / generated-binary runtime delta): `not measured`.
- **`C1` / `C2`:** All four experiments execute directly on stock `rustc`/`llvm-objdump` outputs with zero proxy layers or synthetic multipliers; every negative finding directly eliminates an unsound or unviable abstraction (`O2_` WL alignment, linear-scan `vzeroupper`/probestack, `x86_64` ABI-invariance assumption).
- **`V1`–`V4`:** `V2` validated `4/4` planted-fault negative controls for the binary validator and caught the `; call` comment double-count and LLVM `unnamed_addr alias` hiding bugs via raw-output spot-checks. `V4` ran across `41,408` real `crates.io`/`libcore` functions and `1.32M` real machine instructions. `V3` (weak-memory hardware execution): `known not to apply`.

---

## Boundaries

1. **Cross-Release Target Coverage (`not examined`):** `rustc 1.100.0` and `1.102.0-nightly` cross-release ABI diffs were executed on `x86_64-unknown-linux-gnu` only (their `i686` and `aarch64` cross-compilation targets were not installed in `rustup`, whereas `rustc 1.99.1` had all `8` Tier 1 targets installed). `i686` cross-release `1.99.1 -> 1.100.0` drift therefore remains `not examined`.
2. **Guard Classification Granularity (`approximate`):** The `E1-2a` BCE guard classifier inspects a 25-instruction textual predecessor window in LLVM IR rather than building a full SSA def-use backwards slice; it establishes upper-bound category prevalence (especially the `60.8%` memory-load dominance) rather than exact provability per site.
3. **Binary Validator Engine (`tool-bound`):** Measured `0.22–0.79 MB/s` reflects `llvm-objdump` subprocess + Python regex parsing, not the speed ceiling of a compiled native x86-64 decoder. Additionally, `fn_missing_endbr64_info` reports informational CET absence (`5,079 / 5,079` sysroot functions lack `endbr64` under stock non-CET Linux builds), not a bug.
4. **1-WL Alignment Variants (`not examined`):** Evaluated 3-round 1-WL over CFG + non-noise opcode multisets. Higher-order 2-WL, def-use dataflow-graph matching, or pass-by-pass incremental alignment (`-O0 -> SROA -> Mem2Reg -> ...`) were not measured here.

---

## Evidence

| Artifact / Source | Pin / Scope | Role |
| :--- | :--- | :--- |
| `support/e1_5_cross_release_abi_diff.json` | `256/256` B6 archetypes × `1.99.1`, `1.100.0`, `1.102.0-nightly` + `i686`/`aarch64` | Raw LLVM `define` + `alias` cross-release ABI diff (`f4_simd_f32x4_rust`, `4` `vectorcall` changes). |
| `support/e1_3_real_binary_validator.json` | `30` sysroot `.rlib`s + `anneal-audit` + `cargo-anneal` + `4/4` negative controls | Full-byte `.text` decode counts, throughput, inline stack probes, `zstd-sys` `25.5 KB` frames, `memchr::find_avx2`. |
| `support/e1_4_real_wl_cfg_alignment.json` | `libcore` (`-O0/-O1/-O2/-O3`) + `anneal-audit` (`-C debuginfo=0`) | Real 1-WL BB micro-recall (`10.37%` `-O0->-O3`, `68.98%` `-O2->-O3`) and blind function retrieval (`2.50%` Top-1). |
| `support/e1_2a_real_bce_census.json` | `127` `.ll` files / `41,408` post-`-O3` functions / `1,807` checks | Comment-filtered surviving `panic_bounds_check` + `slice_index_fail` census and guard breakdown. |
| `rust-lang/rust` (`1.99.1`, `1.100.0`, `1.102.0-nightly`) | `58cf8f9c35b355199727627d07ae34a4e2846d67`, `0ef1bc386059596dada8fb65b50425aab2ea637a`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | Real compilers executed for all four measurements. |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Real Rust binary workspace (`anneal-audit`, `cargo-anneal`, and transitive `crates.io` dependency graph). |

---

## Revalidation

1. **Cross-release ABI diff:** Compile the `256`-function procedural ABI suite from `tier1-exhaustive-procedural-abi-differential-campaign-and-fixes` with `rustc +1.99.1`, `rustc +1.100.0`, and `rustc +nightly` using `--crate-type=lib -C opt-level=2 --emit=llvm-ir` and parse both `define` and `alias` lines.
2. **Full-byte binary validation:** Unpack every `.rlib` under `$(rustc +1.99.1 --print sysroot)/lib/rustlib/x86_64-unknown-linux-gnu/lib/`, run `llvm-objdump -d` on `100%` of `.o` members and on `--release` linked `anneal-audit` and `cargo-anneal`, verifying `4/4` planted-fault `.o` controls first.
3. **Debuginfo-free 1-WL alignment:** Compile `library/core/src/lib.rs` with `RUSTC_BOOTSTRAP=1 rustc +1.99.1 --edition=2024 --crate-name core --crate-type=rlib -C opt-level={0,1,2,3} -C debuginfo=0 --emit=llvm-ir` and compute 3-round 1-WL CFG color recall across surviving common functions.
4. **Surviving bounds-check census:** Build with `RUSTFLAGS="--emit=llvm-ir" cargo +1.99.1 build --release`, ignore lines starting with `;`, and count `call`/`invoke` instructions matching `panic_bounds_check` or `slice_*index*fail`.
