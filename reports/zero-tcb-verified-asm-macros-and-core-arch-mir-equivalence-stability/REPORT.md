# Zero-TCB Structured Assembly Macros and `core::arch` MIR Equivalence Stability

## Summary

Verifying hyper-optimized Rust hot loops against clean Rust reference specifications at `.o` machine-code granularity for every function conflates two distinct verification regimes and exposes proofs to continuous LLVM register-allocation and instruction-scheduling churn. Empirical measurements across four `rustc` toolchains (`1.98.0-nightly` through `1.102.0-nightly`), 13 production Rust crates, a working Rust `#[proc_macro]` (`asm_verified!`), and 12 kernel-replayed Lean `v4.34.1` modules (`Init.*`-only, zero `sorryAx`) establish a two-regime architecture that cuts per-kernel proof authoring and maintenance by an order of magnitude while adding **zero lines to the trusted computing base (TCB)** when `.o` ISA semantics are already trusted (or replacing universal `.o` lifting for `core::arch` kernels with a tiny curated MIR intrinsic table):

1. **First-Class `core::arch` SIMD Equivalence at `Runtime(PostCleanup)` MIR Eliminates `100%` of `.o` Churn (`Basis: source + execution + derived`):**
   - **Production SIMD crate Pareto (`1,227` call sites, `0` `x86_64` `asm!` sites):** Across 12 pure-Rust performance and cryptographic crates (`zlib-rs`, `memchr`, `simdutf8`, `crc32fast`, `simd-adler32`, `blake3`, `aho-corasick`, `bytecount`, `hashbrown`, `sha2`, `chacha20`, `aes`), there are **`1,227` `core::arch::x86_64` call sites** (`167` unique `_mm*` functions) and **`0` `x86_64` `asm!` / `naked_asm!` sites** (`14` non-x86 `asm!` sites total; by contrast, C-port video decoder `rav1d` retains `94` external `.asm`/`.S` files). Unfolding `stdarch` (`6,064` `x86` functions in `rustc 1.99.1`) shows that **`293 / 1,227` (`23.88%`)** lower to pure Rust MIR (`Transmute`, `read_unaligned`, `write_unaligned`, `mem::zeroed`, `Simd` aggregate construction) and **`786 / 1,227` (`64.06%`)** lower to **just `16` portable `#[rustc_intrinsic]` `simd_*` operations**—covering **`87.94%` (`1,079 / 1,227`) with zero `llvm.x86.*` intrinsics**. Adding **`3` `llvm.x86.*` families** (`pclmulqdq`, `aesni`, `pshufb`) reaches **`95.19%` (`1,168 / 1,227`)**, and adding **`5` more** (`psadbw`, `vperm`, `pternlog`, `pmaddwd`, `pmaddubsw` — **`24` curated primitives total**) covers **`98.94%` (`1,214 / 1,227`)** ([`support/probe_core_arch_mir_vs_obj_stability.py`](support/probe_core_arch_mir_vs_obj_stability.py)).
   - **Why `Runtime(PostCleanup)` MIR preserves `core::arch` calls—and `0%` MIR drift vs. up to `8 / 16` `.o` drift:** Even at `-C opt-level=3 -Z mir-opt-level=4 -C target-feature=+avx2`, `rustc`'s MIR `Inline` pass leaves `core::arch::x86_64::_mm256_*` calls un-inlined because prebuilt `libcore.rlib` is compiled at baseline `SSE2`: internal bitcast helpers (`__m256i::as_i8x32`) lack `#[target_feature(enable = "avx2")]`, blocking intra-`libcore` MIR inlining across the 256-bit SIMD ABI boundary and inflating stored `optimized_mir` bodies past `inline-mir-hint-threshold=100`. Across **`80` compilations** (`5` AVX2 hot loops $\times$ `4` `rustc` versions $\times$ `4` optimization/caller perturbations), **both** `Runtime(PostCleanup)` MIR and unfolded-`stdarch` MIR produce **`1 / 16` distinct normalized hashes (`0%` churn)** on every kernel, whereas ELF64 `.o` machine bytes churn into **`2 / 16` to `8 / 16` distinct hashes** (`2–5` distinct register allocations, `+35.6%` instruction-count swings in `clmul_fold_avx2`, and `+36.5%` code-size swings in `adler32_avx2`). Validating the `24` curated `stdarch` lowering primitives once per toolchain in Pass 2 lets Pass 1 `SafeTwin` equivalence proofs run purely at MIR (`28` authored Lean LOC and `22.15 ms` private kernel replay vs. `312` LOC and `422.67 ms` for raw `.o` on `dot_maddubs` — an **`11.14x` LOC** and **`19.08x` replay speedup**).
2. **Zero-TCB Structured Assembly Macro (`asm_verified!`) Cuts Per-Kernel `.o` Proof LOC by `9.72x` Where `core::arch` Falls Short (`Basis: normative + source + execution + derived`):**
   - **Three empirical regimes where `core::arch` / Rust fails (`rustc 1.99.1 -O`):** (i) On 256-bit multi-precision multiplication (`_mulx_u64` + `_addcarryx_u64` under `#[target_feature(enable = "bmi2,adx")]`), LLVM emits **`0` `adcx` and `0` `adox` instructions**, serializing into two `adc` passes and spilling callee-saved `rbx`; (ii) on 2x-unrolled `vpmaddubsw` dot products, `core::arch` emits `14` RIP-relative `.rodata` constant relocations (`981–1,124` B) vs. `0` relocations (`125` B) when `ymm2 = 0x0001` is synthesized via `vpcmpeqd` + `vpsrlw`; and (iii) on a branch-free-looking 8-entry Rust constant-time scan, LLVM synthesizes **`cmp rsi, 7; ja 0x3d` plus a `.rodata` indirect jump table `jmp rcx`** (`9` `ret` blocks), leaking the secret index via control-flow and memory-address side channels (mechanized as a formal counterexample to MIR-only equivalence in `MirTwin_CtLookup8.llvm_jump_table_functional_but_leaks`).
   - **Zero-TCB macro + untrusted `HintCert` reflection over exact `.o` bytes:** Unlike `Vale` or `Jasmin`, whose compilers/printers either reside in the TCB or require non-standard toolchains, `asm_verified!` ([`support/probe_asm_verified_macro_and_obj.py`](support/probe_asm_verified_macro_and_obj.py)) is an **untrusted standard Rust `#[proc_macro]`** that: (a) expands to a private `#[unsafe(naked)] extern "sysv64" fn` (`naked_asm!`) wrapped in a public `#[inline] #[target_feature(enable = "...")] pub unsafe fn` gate (cleanly bypassing stable Rust `1.99.1`/`1.100.0` error `E0658` on `#[target_feature]` naked functions); (b) statically rejects five classes of raw `asm!` footguns (`F1..F5`, including closing `rustc`'s `out("ymm0") _` clobber target-feature blind spot and missing `vzeroupper` before `ret`); and (c) emits untrusted Lean 4 `HintCert` instruction-offset and loop-cutpoint witnesses (`namespace UntrustedHints`) checked by `rfl` against the **exact compiled ELF64 `.o` symbol bytes**.
   - **End-to-end Lean `v4.34.1` benchmark and `(level := .private)` kernel replay ([`support/bench_three_regimes_lean4.py`](support/bench_three_regimes_lean4.py)):** Across all three assembly archetypes (`mulx_adcx_adox_mac4` [`100` B], `dot_maddubs_unroll2` [`125` B], `ct_lookup8_cmov` [`98` B]), `HintCert`-assisted `.o` verification proves **character-for-character identical theorem types** (`type_hints == 0`, zero TCB growth, axioms strictly within `{propext, Classical.choice, Quot.sound}`) while cutting per-kernel authored Lean proof code from **`768` LOC** (`269 + 312 + 187`) to **`79` LOC** (`30 + 22 + 27` — **`9.72x` reduction**: `8.97x`, `14.18x`, and `6.93x` respectively), `.olean` artifact size by **`10.0x–26.7x`**, and per-module elaboration wall-clock time by **`1.16x–6.92x`**.

## Applicability

This report governs verification architecture selection, `stdarch` MIR primitive curation, structured assembly macro design, and Lean 4 certificate-reflection engineering for verifying SIMD and assembly hot-loop optimizations in Rust crates.

### Examined Subjects and Their Relationships

- **Rust toolchains (`rust-lang/rust`):** Four `x86_64-unknown-linux-gnu` compilers spanning six months and an LLVM major-version boundary (`LLVM 22` $\to$ `LLVM 23`):
  - `1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `2026-05-31`, `LLVM 22.1.6`);
  - `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, `2026-10-13`, `LLVM 23.1.1`);
  - `1.100.0` (`0ef1bc386059596dada8fb65b50425aab2ea637a`, `2026-11-09`, `LLVM 23.1.5`);
  - `1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `2026-11-11`, `LLVM 23.1.5`).
  All 80 MIR-vs-`.o` stability cells were compiled across all four toolchains; `stdarch` source decomposition, `asm_verified!` proc-macro compilation, and `.o` byte extraction for the Lean 4 benchmark used `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`).
- **Lean 4 kernel and replay harness (`leanprover/lean4`):** `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), invoked single-threaded with `-DElab.async=false -Ddebug.skipKernelTC=false -j1 -M2048` and audited via `importModules ... (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)` followed by `base.toKernelEnv.replay`.
- **Verification boundary (`joshlf/anneal`):** Evaluated against Anneal's MIR capture stage (`Runtime(PostCleanup)`), Statement-Origin Separation invariant (`type_hints == 0` on locked obligation types), tactic-free foundation rule, and three-axiom ceiling (`{propext, Classical.choice, Quot.sound}`) at `c131b320eeeb26ef692e5afd5ec8db49ee518613`.
- **Production Rust crate corpus (`13` upstream repositories):** Twelve pure-Rust SIMD/crypto crates (`zlib-rs 0.6.8`, `memchr 2.8.3`, `simdutf8 0.1.5`, `crc32fast 1.5.5`, `simd-adler32 0.3.10`, `blake3 1.8.7`, `aho-corasick 1.1.5`, `bytecount 0.6.9`, `hashbrown 0.17.1`, `sha2 0.11.1`, `chacha20 0.10.2`, `aes 0.9.4`) and C-to-Rust codec port `memorysafety/rav1d` (`2e7216c20ac2a75de204d6c8d7268b75a45959b4`), examined at the exact Git commits listed in `REPORT.json` to quantify real-world `core::arch` vs. `asm!` incidence and leaf-intrinsic Pareto concentration.

### Scope and Version Qualifications

- **Shared across all four `rustc` versions (`1.98.0-nightly`..`1.102.0-nightly`):** Exact `Runtime(PostCleanup)` MIR body invariance (`1 / 16` hashes per kernel), default MIR `Inline` preservation of `core::arch::x86_64::_mm256_*` calls, and `InlineAsmCtxt::check_asm`'s `out("ymm0") _` clobber target-feature blind spot hold identically across all four toolchains.
- **Version-specific behavior (`E0658` on `#[unsafe(naked)]` + `#[target_feature]`):** On stable `rustc 1.99.1` and `1.100.0`, attaching `#[target_feature(enable = "...")]` directly to a `#[unsafe(naked)]` function fails with `error[E0658]: #[target_feature(..)] cannot be applied to naked functions` (`#![feature(naked_functions_target_feature)]`, `rust-lang/rust#138568`). `asm_verified!`'s two-function split (private `#[unsafe(naked)] extern "sysv64" fn` + public `#[inline] #[target_feature(enable = "...")] pub unsafe fn`) compiles cleanly on both stable and nightly Rust.
- **Target ABI and ISA scope:** Machine-code decoding, register clobber checking, and `vzeroupper` enforcement in the prototype target `x86_64` System V AMD64 ABI (`extern "sysv64"` / Linux ELF64 `.o` relocatable objects). Extending the same zero-TCB `#[proc_macro]` + `HintCert` architecture to `aarch64` AAPCS64 or Windows `x64` requires substituting the target ABI clobber set and `.o` decoder without changing the trust-boundary architecture.

## Findings

### 1. Production Rust SIMD Crate Census and the 24-Primitive `stdarch` Pareto Curve

`Basis: source + derived`

Direct AST/token inspection of 12 widely deployed pure-Rust hot-loop crates alongside C-port `memorysafety/rav1d`, cross-referenced against the complete `core_arch/src/x86` (`stdarch`) source tree shipped in `rustc 1.99.1` (`6,064` `pub unsafe fn` / `pub fn` definitions and `1,052` `#[link_name = "llvm.x86.*"]` declarations), establishes that idiomatic Rust performance engineering overwhelmingly targets `core::arch` intrinsics rather than inline assembly:

| Crate (`version @ git_rev`) | `x86_64` `core::arch` call sites | Unique `_mm*` fns | `x86_64` `asm!` sites | Non-`x86` `asm!` sites |
| :--- | ---: | ---: | ---: | ---: |
| `chacha20 0.10.2 @ 6b236b75` | `232` | `44` | `0` | `0` |
| `zlib-rs 0.6.8 @ 0254e072` | `228` | `51` | `0` | `8` (4 AArch64 `crc32*`, 4 LoongArch) |
| `blake3 1.8.7 @ f3149ec5` | `218` | `38` | `0` | `0` |
| `simd-adler32 0.3.10 @ d93164f9` | `104` | `37` | `0` | `0` |
| `aes 0.9.4 @ 9a84f2f8` | `99` | `29` | `0` | `0` |
| `aho-corasick 1.1.5 @ 5178060c` | `88` | `26` | `0` | `0` |
| `crc32fast 1.5.5 @ 8a93d2a7` | `84` | `27` | `0` | `0` |
| `bytecount 0.6.9 @ f06647f9` | `63` | `19` | `0` | `0` |
| `sha2 0.11.1 @ 138dc5a0` | `48` | `22` | `0` | `6` (LoongArch / RISC-V `zknh`) |
| `simdutf8 0.1.5 @ 87ee8d9d` | `38` | `30` | `0` | `0` |
| `memchr 2.8.3 @ 5fdb40c0` | `14` | `14` | `0` | `0` |
| `hashbrown 0.17.1 @ c62a63a6` | `11` | `9` | `0` | `0` |
| **Total (`12` pure-Rust crates)** | **`1,227`** | **`167` (union)** | **`0`** | **`14`** |
| *Comparison:* `rav1d @ 2e7216c2` | — | — | `94` external `.asm`/`.S` files (`87` `.rs` files) | — |

Tracing each of the `167` unique `core::arch::x86_64` functions called across the `1,227` sites to its leaf body in `rustc 1.99.1`'s `library/stdarch/crates/core_arch/src/x86/` reveals a dramatic concentration of semantic surface:

1. **Tier 0 — Pure Rust MIR (`293 / 1,227` sites = `23.88%`, `0` new primitives):** Unaligned loads/stores (`_mm256_loadu_si256` $\to$ `ptr::read_unaligned`, `_mm256_storeu_si256` $\to$ `ptr::write_unaligned`), lane splats/constructors (`_mm256_set1_epi8`, `_mm256_setr_epi8`), casts (`_mm256_castsi256_si128` $\to$ `Transmute` / `simd_shuffle`), and zero initializers (`_mm256_setzero_si256` $\to$ `mem::zeroed`) lower entirely to existing MIR statements and `Rvalue`s.
2. **Tier 1 — `16` Portable `#[rustc_intrinsic]` `simd_*` Operations (`+786` sites = `64.06%`; cumulative `1,079 / 1,227` = `87.94%`):** Since `stdarch`'s migration away from vendor-specific LLVM intrinsics for lane-wise operations, nearly two-thirds of all `core::arch::x86_64` calls lower to just **16 architecture-independent `simd_*` intrinsics** shared across `x86_64`, `aarch64` NEON, and `wasm32` SIMD128:
   `simd_add`, `simd_and`, `simd_bitmask` (`_mm256_movemask_epi8`), `simd_eq` (`_mm256_cmpeq_epi8`), `simd_extract`, `simd_funnel_shl`, `simd_gt`, `simd_lt`, `simd_or`, `simd_reduce_or`, `simd_saturating_sub` (`_mm256_subs_epu8`), `simd_shl`, `simd_shr`, `simd_shuffle` (`_mm256_unpacklo_epi8`, `_mm_shuffle_epi32`, `_mm256_permute2x128_si256`), `simd_sub`, and `simd_xor`.
3. **Tier 2 — Top `3` `llvm.x86.*` Families (`+89` sites = `7.25%`; cumulative `1,168 / 1,227` = `95.19%` at `19` primitives):**
   - `pclmulqdq` (`_mm_clmulepi64_si128` / `_mm256_clmulepi64_epi128`, `38` sites in `crc32fast`, `zlib-rs`);
   - `aesni` (`_mm_aesenc_si128`, `_mm_aesenclast_si128`, `_mm_aeskeygenassist_si128`, `_mm_aesimc_si128`, `30` sites in `aes`);
   - `pshufb` (`_mm_shuffle_epi8`, `_mm256_shuffle_epi8`, `_mm512_shuffle_epi8`, `21` sites in `zlib-rs`, `simdutf8`, `aho-corasick`, `bytecount`, `simd-adler32`).
4. **Tier 3 — Next `5` `llvm.x86.*` Families (`+46` sites = `3.75%`; cumulative `1,214 / 1,227` = `98.94%` at `24` primitives):**
   - `psadbw` (`_mm256_sad_epu8`, `15` sites), `vperm` (`_mm256_permutevar8x32_epi32` / `perm2x128`, `9` sites), `pternlog` (`_mm512_ternarylogic_epi32`, `8` sites), `pmaddwd` (`_mm256_madd_epi16`, `8` sites), and `pmaddubsw` (`_mm256_maddubs_epi16`, `6` sites). The remaining `13 / 1,227` sites (`1.06%`) consist of `5` cache-hint `_mm_prefetch` calls (semantic no-op), `4` SHA-NI rounds (`sha256rnds2`, `sha256msg1`, `sha256msg2`), `3` AVX-VNNI `vpdpbusd` calls, and `1` `avx512.permvar.si.512` call.

### 2. Why Default `rustc` MIR `Inline` Preserves `core::arch` Calls, and Exact `Runtime(PostCleanup)` MIR Stability vs. `.o` Churn (`80` Compilations)

`Basis: source + execution + derived`

#### 2.1 The `libcore` SSE2-vs-AVX2 MIR Inlining Gate

Inspecting `-Z dump-mir` across `rustc 1.98.0-nightly` through `1.102.0-nightly` uncovers a non-obvious compiler invariant: even when compiling a crate with `-C opt-level=3 -Z mir-opt-level=4 -C target-feature=+avx2,+pclmul`, **`Runtime(PostCleanup)` MIR retains direct `Call` terminators to `core::arch::x86_64::_mm256_*` functions** rather than inlining them to `simd_*` / `llvm.x86.*` primitives.

Controlled MIR probes in [`support/probe_core_arch_mir_vs_obj_stability.py`](support/probe_core_arch_mir_vs_obj_stability.py) establish the exact mechanism:
- Precompiled `libcore.rlib` / `libcore.rmeta` is built for `x86_64-unknown-linux-gnu` with baseline `+sse2` only (no `+avx2`).
- Inside `library/stdarch/crates/core_arch/src/x86/avx2.rs`, `_mm256_cmpeq_epi8` carries `#[inline] #[target_feature(enable = "avx2")]`, **but** its internal representation-conversion helpers (`__m256i::as_i8x32`, `i8x32::as_m256i`) are plain `#[inline]` functions *without* `#[target_feature(enable = "avx2")]` that pass 256-bit SIMD vectors by value.
- When `libcore` itself is compiled, `rustc`'s MIR `Inline` pass refuses to inline `as_i8x32` into `_mm256_cmpeq_epi8` because caller and callee disagree on `+avx2` target features across a 256-bit vector ABI argument. As a result, `_mm256_cmpeq_epi8`'s serialized `optimized_mir` in `libcore.rmeta` retains three nested calls (`as_i8x32` $\to$ `simd_eq` $\to$ `as_m256i`), pushing its MIR inline cost above default `-Z inline-mir-hint-threshold=100` (deferring actual inlining to LLVM IR `alwaysinline` / `inlinehint` passes).
- Passing `-Z mir-opt-level=4 -Z inline-mir-hint-threshold=2000 --emit=llvm-ir` unfolds every `stdarch` wrapper cleanly at MIR into the 24 leaf primitives above. Crucially, **both** representations—un-inlined `core::arch::x86_64::_mm*` calls at standard `Runtime(PostCleanup)` MIR and unfolded `simd_*`/`llvm.x86.*` MIR—exhibit `100%` cross-toolchain and cross-flag stability.

#### 2.2 `80`-Cell Stability Matrix (`5` AVX2 Hot Loops $\times$ `4` Toolchains $\times$ `4` Perturbations)

Five representative `core::arch::x86_64` AVX2 hot loops (`adler32_avx2` [`zlib-rs`/`simd-adler32`], `memchr_avx2` [`memchr`], `utf8_range_avx2` [`simdutf8`], `dot_maddubs_avx2` [`rav1d`], and `clmul_fold_avx2` [`crc32fast`], all differentially tested against scalar Rust twins) were compiled across all four `rustc` versions under four compilation/caller perturbations:
1. `opt2`: `-C opt-level=2`;
2. `opt3`: `-C opt-level=3`;
3. `opt3_no_vec`: `-C opt-level=3 -C llvm-args=-vectorize-loops=false`;
4. `opt3_caller_perturb`: `-C opt-level=3` with an added `#[inline(always)]` live-register-pressure caller wrapper in the same compilation unit.

| AVX2 Kernel (`16` cells each) | `Runtime(PostCleanup)` MIR distinct hashes | Unfolded-`stdarch` MIR distinct hashes | ELF64 `.o` distinct byte hashes | Distinct regalloc sequences | Distinct mnemonic schedules | `.o` insn count `[min, max]` | `.o` `.text` bytes `[min, max]` | `.o` relocs `[min, max]` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `adler32_avx2` | **`1 / 16`** (`0%` drift) | **`1 / 16`** | **`5 / 16`** | `5` | `5` | `[110, 139]` (`+26.4%`) | `[425, 580]` (`+36.5%`) | `[2, 2]` |
| `memchr_avx2` | **`1 / 16`** (`0%` drift) | **`1 / 16`** | **`8 / 16`** | `5` | `5` | `[90, 95]` (`+5.6%`) | `[322, 337]` (`+4.7%`) | `[0, 0]` |
| `utf8_range_avx2` | **`1 / 16`** (`0%` drift) | **`1 / 16`** | **`4 / 16`** | `2` | `4` | `[51, 54]` (`+5.9%`) | `[177, 191]` (`+7.9%`) | `[3, 3]` |
| `dot_maddubs_avx2` | **`1 / 16`** (`0%` drift) | **`1 / 16`** | **`4 / 16`** | `4` | `4` | `[241, 270]` (`+12.0%`) | `[981, 1124]` (`+14.6%`) | `[14, 14]` |
| `clmul_fold_avx2` | **`1 / 16`** (`0%` drift) | **`1 / 16`** | **`2 / 16`** | `2` | `2` | `[45, 61]` (`+35.6%`) | `[191, 255]` (`+33.5%`) | `[0, 0]` |

Every kernel exhibits **within-toolchain `.o` drift** (`opt2` vs. `opt3` changes instruction counts and `.text` offsets on all 5 kernels across all 4 compilers) and **cross-LLVM `.o` drift** (`LLVM 22.1.6` $\to$ `23.1.1` $\to$ `23.1.5` re-allocates `ymm`/`gpr` registers and reschedules loads, producing `8 / 16` distinct `.o` binaries on `memchr_avx2`), plus `2`–`14` RIP-relative `.rodata` constant-pool relocations (`R_X86_64_PC32`) in `adler32_avx2`, `utf8_range_avx2`, and `dot_maddubs_avx2` that any `.o` lifter must resolve against `.rodata` sections. By contrast, `Runtime(PostCleanup)` MIR has **`0` drift across all `80` compilations**.

### 3. Three Concrete Regimes Where `core::arch` / Rust Codegen Falls Short (`rustc 1.99.1 -O`)

`Basis: execution + source + derived`

Compiling matched `core::arch` / pure-Rust implementations against structured assembly in [`support/probe_asm_verified_macro_and_obj.py`](support/probe_asm_verified_macro_and_obj.py) (`rustc 1.99.1 -C opt-level=3`) isolates the exact `1–2%` of hot-loop kernels where MIR-level `core::arch` is insufficient:

1. **Archetype 1 — Multi-Precision Dual Carry Chains (`mulx` + `adcx` + `adox`):**
   - *Goal:* Compute $t[0..4] + a[0..4] \times b \to (\text{out}[0..4], \text{carry}) \in [0, 2^{320})$ in a single pass by running `adcx` on `CF` in parallel with `adox` on `OF` while `mulx` leaves both flags untouched.
   - *Observed `core::arch` lowering (`mulx_adcx_adox_mac4_core_arch`, `58` B, `16` insns, SHA-256 `88448b13...`):* Even with `#[target_feature(enable = "bmi2,adx")]`, `_mulx_u64`, and `_addcarryx_u64` (`llvm.x86.addcarry.64`), LLVM `23.1.1`'s DAG legalizer collapses flag state to `EFLAGS` and emits **`0` `adcx` and `0` `adox` instructions**: it hoists four `mulx` loads (`spilling callee-saved rbx` via `push rbx ... pop rbx`), runs a serialized `add` + three `adc` + `adc rax, 0` chain for products, and then runs a second serialized `add` + two `adc` + `adc rax, 0` chain into `[rdi]`.
   - *`asm_verified!` lowering (`mulx_adcx_adox_mac4_asm_raw_naked`, `100` B, `20` insns, SHA-256 `69eb8ffe8219a54e880efe7b75befce2a63e525d66d00068f40c1e3da61668e3`):* Interleaves `mulx` + `adcx` (`CF`) + `adox` (`OF`) in a single pipeline pass with `0` stack spills and `0` callee-saved saves.
2. **Archetype 2 — Register-Pinned Unrolled `vpmaddubsw` + `vpmaddwd` Accumulation (`dot_maddubs_unroll2`):**
   - *Observed `core::arch` lowering (`dot_maddubs_avx2`, `981–1,124` B, `241–270` insns):* Spills vector constants into `.rodata` (`14` ELF relocations) and shifts across `4` distinct register allocations (`12` `ymm` registers) across compiler versions.
   - *`asm_verified!` lowering (`dot_maddubs_unroll2_asm_raw_naked`, `125` B, `31` insns, SHA-256 `687c2b8c82cf7753114db508518dfd3be2cc599d3e593050155a5ce10b0742e6`):* Pins dual accumulators (`ymm0`, `ymm1`) to break `vpaddd` loop-carried latency, synthesizes `ymm2 = [0x0001u16; 16]` in-register via `vpcmpeqd ymm2, ymm2, ymm2; vpsrlw ymm2, ymm2, 0xf` (`0` `.rodata` relocations), and executes `vzeroupper` immediately before `ret`.
3. **Archetype 3 — Constant-Time Table Lookup Under LLVM Jump-Table Optimization (`ct_lookup8_cmov`):**
   - *Observed Rust lowering (`ct_lookup8_naive_rust`, `64` B, `24` insns, SHA-256 `879518ba...`):* Given an arithmetic branchless-looking 8-element Rust loop (`let mask = ((i == secret_idx) as u64).wrapping_neg(); acc |= table[i] & mask`), LLVM `23.1.1` `-O` pattern-matches the loop into **`cmp rsi, 0x7; ja 0x3d` + `lea rax, [rip+0x0]; movsxd rcx, dword ptr [rax+rsi*4]; add rcx, rax; jmp rcx`** followed by **9 separate `mov rax, [rdi + 8*k]; ret` basic blocks**! This leaks `secret_idx` across four microarchitectural channels: conditional branch outcome (`ja`), `.rodata` jump-table cache line (`[rax+rsi*4]`), indirect branch target (`jmp rcx`), and secret-indexed table load (`[rdi + 8*k]`).
   - *`asm_verified!` lowering (`ct_lookup8_cmov_asm_raw_naked`, `98` B, `26` insns, SHA-256 `878fff952e7a1f34d3d46f4fd60c750112f3fbb18f5ea9977b43469645a36dcf`):* Emits 8 unconditional `mov r8, [rdi + 8*k]; cmp rsi, k; cmove rax, r8` triples with a secret-independent `LeakTrace`.

### 4. Zero-TCB Structured Assembly Macro (`asm_verified!`): Architecture and Footgun Elimination

`Basis: normative + source + execution`

Standalone verified assembly DSLs either place a custom parser/code-generator inside the TCB (`Vale`'s F\*/Dafny printer) or require an external compiler toolchain (`Jasmin`'s OCaml `jasminc`). By contrast, `asm_verified!` ([`support/probe_asm_verified_macro_and_obj.py`](support/probe_asm_verified_macro_and_obj.py)) is an **ordinary, untrusted, dependency-free Rust `#[proc_macro]`** (`proc_macro::TokenStream` only) with **zero TCB footprint**:

```text
  asm_verified! { ... }  (Untrusted Rust #[proc_macro], 0 TCB LOC)
         │
         ├──► (1) Static Compile-Time Footgun Gate (F1..F5 -> compile_error!)
         │
         ├──► (2) Standard Rust Expansion:
         │        #[unsafe(naked)] unsafe extern "sysv64" fn __raw(...) { naked_asm!(...) }
         │        #[inline] #[target_feature(enable = "...")] pub unsafe fn entry(...) { __raw(...) }
         │                 │
         │                 ▼  rustc -O --emit=obj (Standard Toolchain)
         │        ELF64 `.o` Symbol Bytes  ◄──────────┐
         │                                            │  rfl (Lean 4 Kernel WHNF)
         └──► (3) Untrusted Lean 4 Witness Emission:  │
                  `namespace UntrustedHints`          │
                  `HintCert` (PC offsets, cutpoints) ─┘
```

1. **Stable-Rust `E0658` Resolution via Two-Function Split:** Because stable `rustc 1.99.1` and `1.100.0` forbid `#[target_feature]` on `#[unsafe(naked)]` functions (`E0658`), `asm_verified!` emits a module-private `#[unsafe(naked)] unsafe extern "sysv64" fn <name>_raw_naked` containing `core::arch::naked_asm!(...)` and a public `#[inline] #[target_feature(enable = "...")] pub unsafe fn <name>` wrapper that tail-calls `<name>_raw_naked`. Callers lacking the required `#[target_feature]` cannot invoke `<name>` without discharging the target-feature safety contract, while callers *with* matching `#[target_feature]` inline the wrapper to a direct `call`.
2. **Five Verified Compile-Time Footgun Gates (`5 / 5` `rustc 1.99.1` negative compile tests passing with `rc = 1`):**
   - **`F1` — Closing `rustc`'s `out("ymm0") _` Target-Feature Blind Spot:** `rustc`'s `InlineAsmCtxt::check_asm` (`compiler/rustc_hir_typeck/src/inline_asm.rs:435-463`) skips target-feature validation on clobber operands (`if !op.is_clobber()`). `asm_verified!` inspects every declared clobber register (`ymm*`/`zmm*`) *and* every instruction mnemonic (`vpmaddubsw`, `mulx`, `adcx`, `adox`, `vpclmulqdq`) against the macro's `target_feature` list, rejecting mismatches at compile time (`error: [asm_verified!] Footgun F1`).
   - **`F2` — Mandatory `vzeroupper` Before `ret` on Dirty Upper `ymm`/`zmm` State:** Whenever any `ymm*`/`zmm*` register or VEX-256/EVEX-512 instruction appears, `asm_verified!` enforces that every `ret` instruction is immediately preceded by `vzeroupper` (`error: [asm_verified!] Footgun F2`), preventing AVX-SSE transition stalls and matching the operational `ymmDirty` fault guard in `AsmMirBase.execInsn`.
   - **`F3` — Intel-Syntax MASM Binary-Literal / Backward-Label Ambiguity Ban:** In LLVM's x86 Intel-syntax parser, `0b` / `1b` / `0b1010` tokens risk silent misparsing as MASM binary literals or directional local-label references; `asm_verified!` rejects `0b...` literals and bare `[0-9]+[bf]` labels in favor of explicit named labels (`.Lloop:`) and `0x...` hex constants (`Footgun F3`).
   - **`F4` — Raw Directive Containment:** Rejects `.byte`, `.word`, `.long`, `.quad`, `.inst`, `.section`, `.pushsection`, `.popsection`, `.global`, `.globl`, and `.att_syntax` directives that could smuggle unparsed opcodes or switch sections (`Footgun F4`).
   - **`F5` — System V ABI Callee-Saved & Live-Input Clobber Disjointness:** Rejects clobbers that alias live parameter registers (`rdi`, `rsi`, `rdx`, `rcx`, `r8`, `r9`) or undeclared System V callee-saved registers (`rbx`, `rbp`, `r12`–`r15`, `rsp`) (`Footgun F5`).
3. **Why TCB Growth Over `.o` Verification Is Strictly Zero:** Even if a buggy or adversarial `asm_verified!` macro emitted a bogus `HintCert` (wrong byte offsets, wrong instruction sequence, or wrong loop cutpoint), `LockedObligations.verify_<kernel>_obj` states its theorem **solely** over `AsmMirBase.run <elfObjBytes> <fuel> s` (`type_hints == 0`). In Lean 4's kernel, `check<Class>Cert <elfObjBytes> <cert> = true` is discharged by `rfl`: if the actual `.o` machine bytes emitted by `rustc`/LLVM deviate by a single bit from the certificate's instruction schedule or relative branch targets, kernel `isDefEq` fails closed.

### 5. End-to-End Lean `v4.34.1` Benchmark Across Three Regimes and Private-Level Kernel Replay

`Basis: execution + source + derived`

To measure authoring cost, certificate size, elaboration latency, and fresh kernel replay latency without mocks or axioms, [`support/bench_three_regimes_lean4.py`](support/bench_three_regimes_lean4.py) compiles 12 self-contained `prelude` + `Init.*`-only Lean `v4.34.1` modules (`support/lean/*.lean`, `0` `sorryAx`) over the **exact 323 bytes (`77` instructions)** of ELF64 `.text` machine code extracted from `rustc 1.99.1 -O --emit=obj`:

- **Shared Trusted Foundation (`AsmMirBase.lean`, `599` non-comment LOC, `100%` tactic-free):** Byte-level x86-64 REX / VEX2 / VEX3 / ModRM / SIB / `rel8` decoder (`decodeX86At`), operational semantics (`X86State`, `execInsn`, `step`, `run`) modeling independent `CF`/`OF`/`ZF` flags, `ymmDirty` `ret`-faulting without `vzeroupper`, `mem64`/`mem8`, and 2-safety `LeakEvent` traces (`load64`, `store64`, `load256`, `branch`), plus `Runtime(PostCleanup)` MIR twins and pure functional specifications.
- **Shared ISA Lemma Library (`IsaLemmas.lean`, `347` LOC) & Reusable Untrusted Certificate Checkers (`UntrustedHints.lean`, `969` LOC, `0` TCB LOC):** Proves `mac4_combine_conservation` ($\sum_{i=0}^4 \text{out}_i 2^{64i} = \sum_{i=0}^3 t_i 2^{64i} + b \sum_{i=0}^3 a_i 2^{64i} < 2^{320}$ with `cf5 = 0 ∧ of5 = 0`), `horizontal_reduce_256`, abstract `exec_*` instruction-stepping lemmas, and three reusable boolean certificate checkers (`checkDualCarryMac4Cert_sound`, `checkSimdDotUnroll2Cert_sound`, `checkCtLinearScan8Cert_exec` / `_2safety`).

#### 5.1 Per-Kernel Authored LOC, `.olean` Size, Compile Time, and `(level := .private)` Kernel Replay

All replay latencies below were measured in [`support/bench_three_regimes_lean4.py`](support/bench_three_regimes_lean4.py) via `importModules ... (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)` followed by `base.toKernelEnv.replay`. For Regime (b) (`HintObj_*`), **both** warm per-kernel delta replay (against `UntrustedHints`, measuring per-function CI incremental replay) and cold replay (against `IsaLemmas`, replaying all `197–198` constants of `UntrustedHints` + `HintObj_*` from scratch) are reported:

| Archetype & Regime (`Lean v4.34.1`) | Authored LOC (excl. cert) | Auto `HintCert` LOC (`bytes`) | Compile wall (`ms`) | `.olean` size (`B`) | Private replay warm / per-kernel (`ms`, `#consts`) | Private replay cold incl. `UntrustedHints` (`ms`, `#consts`) | `type_hints` / `val_hints` | Transitive axioms |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | :---: | :--- |
| **`MulxMac4` (`100` B, `20` insns)** | | | | | | | | |
| (a) `RawObj_MulxMac4` (raw `.o`) | `269` | `0` (`0` B) | `3,795.4` | `878,432` | `1,008.97` (`40`) | `1,008.97` (`40`) | `0 / 0` | `choice, Quot.sound, propext` |
| (b) `HintObj_MulxMac4` (`asm_verified!`) | **`30`** (**`8.97x` $\downarrow$**) | `7` (`259` B) | **`548.5`** (**`6.92x` $\downarrow$**) | **`32,896`** (**`26.7x` $\downarrow$**) | **`177.48`** (`2`) (**`5.68x` $\downarrow$**) | `1,444.77` (`197`) | `0 / 3` | `choice, Quot.sound, propext` |
| (c) `MirTwin_MulxMac4` (`core::arch` MIR)\* | `74` | `0` (`0` B) | `760.2` | `419,056` | `232.19` (`9`) | `232.19` (`9`) | `0 / 0` | `choice, Quot.sound, propext` |
| **`DotMaddubs` (`125` B, `31` insns, loop)** | | | | | | | | |
| (a) `RawObj_DotMaddubs` (raw `.o`) | `312` | `0` (`0` B) | `2,077.2` | `649,768` | `422.67` (`17`) | `422.67` (`17`) | `0 / 0` | `Quot.sound, propext` |
| (b) `HintObj_DotMaddubs` (`asm_verified!`) | **`22`** (**`14.18x` $\downarrow$**) | `8` (`378` B) | **`811.3`** (**`2.56x` $\downarrow$**) | **`36,760`** (**`17.7x` $\downarrow$**) | **`386.50`** (`2`) | `1,715.27` (`197`) | `0 / 3` | `Quot.sound, propext` |
| (c) `MirTwin_DotMaddubs` (`core::arch` MIR) | **`28`** (**`11.14x` $\downarrow$**) | `0` (`0` B) | **`173.3`** (**`11.99x` $\downarrow$**) | `77,256` | **`22.15`** (`7`) (**`19.08x` $\downarrow$**) | **`22.15`** (`7`) | `0 / 0` | `Quot.sound, propext` |
| **`CtLookup8` (`98` B, `26` insns, + 2-safety)** | | | | | | | | |
| (a) `RawObj_CtLookup8` (raw `.o`) | `187` | `0` (`0` B) | `1,074.3` | `460,560` | `211.56` (`5`) / `187.25` (2-safety) | `211.56` (`5`) | `0 / 0` | `Quot.sound, propext` |
| (b) `HintObj_CtLookup8` (`asm_verified!`) | **`27`** (**`6.93x` $\downarrow$**) | `7` (`322` B) | **`926.4`** | **`45,984`** (**`10.0x` $\downarrow$**) | `409.97` (`3`) / `454.20` (2-safety) | `1,595.05` (`198`) | `0 / 3` | `Quot.sound, propext` |
| (c) `MirTwin_CtLookup8` (MIR + leak refutation)\*\* | `64` | `0` (`0` B) | `324.6` | `391,968` | **`49.07`** (`7`) | `49.07` (`7`) | `0 / 0` | `Quot.sound, propext` |
| **3-Archetype Sum: (a) Raw `.o` vs. (b) `HintObj`** | **`768` $\to$ `79` (`9.72x` $\downarrow$)** | `0` $\to$ `22` (`959` B) | **`6,946.9` $\to$ `2,286.2` (`3.04x` $\downarrow$)** | **`1.99 MB` $\to$ `115.6 KB` (`17.2x` $\downarrow$)** | **`1,643.2` $\to$ `974.0` (`1.69x` $\downarrow$)** | — | `0 / 0` vs `0 / 3` | $\subseteq$ 3 standard axioms |

\* *In `MirTwin_MulxMac4`, the MIR proof verifies the `core::arch` code cleanly, but `rustc 1.99.1 -O` fails to emit `adcx`/`adox` hardware instructions (`0` `adcx`/`adox`, serialized `adc` + `push rbx`).*
\*\* *`MirTwin_CtLookup8` includes `llvm_jump_table_functional_but_leaks`, formally proving that `rustc 1.99.1 -O`'s jump-table lowering of `ct_lookup8_naive_rust` is functionally equal to `lookup8Spec` yet violates 2-safety leakage equivalence.*

#### 5.2 Three Concrete Lean `v4.34.1` Kernel-Engineering Insights from the Benchmark

1. **Why `HintObj_CtLookup8` per-kernel replay is `409.97 ms` vs. `211.56 ms` for `RawObj_CtLookup8`:** In `HintObj_CtLookup8`, a single `rfl` proof term forces Lean's kernel `isDefEq` reducer to evaluate `checkCtLinearScan8Cert ctObjBytes ctLookup8Cert = true` across all 26 variable-length x86-64 instructions over a 98-byte `List UInt8` (`O(N^2)` list indexing in `byteAt`). In `RawObj_CtLookup8`, those 26 decodes were split across separate `have hk_i` declarations; furthermore, `HintObj_CtLookup8` invokes `checkCtLinearScan8Cert_exec` in `verify_ct_lookup8_obj` and `checkCtLinearScan8Cert_2safety` (which internally calls `checkCtLinearScan8Cert_exec` twice), running kernel `rfl` over the certificate check in both theorems. Indexing code bytes via a balanced binary tree (`BinTree UInt8`, $O(\log N)$ lookup) or hoisting `private theorem ctCert_ok : checkCtLinearScan8Cert ctObjBytes ctLookup8Cert = true := rfl` once per module eliminates redundant kernel WHNF reduction.
2. **Eliminating $O(3^N)$ Symbolic State WHNF Blowup and `Decidable` Motive Errors:** Chaining `let s_{k+1} := execInsn ... s_k` across 20 instructions causes exponential WHNF blowup (`>200,000` heartbeats) whenever a branch or flag (`if hi = lo`, `decide (sum ≥ W64)`) duplicates `s_k`. Defining flat $O(1)$ record updates (`let k_{i+1} : X86State := { k_i with rip := ..., gpr := ... }`) paired with abstract `exec_*` instruction lemmas in [`support/lean/IsaLemmas.lean`](support/lean/IsaLemmas.lean) (proved over a variable `s : X86State` rather than a `{ ... }` literal so `simp only` never hits an implicit-vs-explicit `Decidable` transparency mismatch) reduced `UntrustedHints.lean`'s 969-LOC build to `7.62 s` and `<320 MB` RSS.
3. **Hidden Cost of Unassisted Raw `.o` Proofs (`decodeGpr4` / `decodeYmm3` AST Leakage):** Without `UntrustedHints.checkAt`, rewriting `step code s` via `step_of_decode ... rfl` unifies the instruction parameter with raw unreduced decoder expressions (`decodeYmm3 2`, `decodeGpr4 (UInt8.toNat 15 % 8)`), breaking downstream `rw` patterns unless the proof author manually supplies explicit `(ins := .vpmaddwd .ymm3 .ymm3 .ymm2) (len := 4)` annotations at every PC offset. `HintCert` reflection discharges all instruction-identity and PC-offset arithmetic inside boolean `checkAt` once.

### 6. Unified Zero-TCB Routing Architecture for Verified Hot-Loop Optimization

`Basis: derived`

Combining the MIR stability matrix (Section 2), the compiler lowering probe (Section 3), and the three-regime Lean 4 benchmark (Section 5) yields a deterministic two-path architecture:

| Optimization Workload | Share of Rust Hot Loops | Verification Seam | Per-Kernel Proof Cost & Churn | TCB Requirement |
| :--- | :--- | :--- | :--- | :--- |
| **Path A — `core::arch` SIMD Intrinsics** (`memchr`, `zlib-rs`, `simdutf8`, `crc32fast`, `blake3`, `aes`, `chacha20`) | **`~98.9%`** of pure-Rust SIMD sites (`24` primitives) | `Runtime(PostCleanup)` MIR `SafeTwin` equivalence | **`28–74` LOC**, **`22–232 ms`** replay, **`0%` churn** across `-O2`/`-O3`, caller changes, and `rustc`/`LLVM` upgrades | Curated 24-primitive `StdarchSemantics` table validated once per toolchain archive in Pass 2 (`0` per-function `.o` lifters) |
| **Path B — `asm_verified!` Naked/Inline Assembly** (`mulx`/`adcx`/`adox` bignum, register-pinned unrolled loops, constant-time `cmov`) | **`~1.1%`** + C-port `.asm` migrations + 2-safety CT kernels | Compiled ELF64 `.o` symbol bytes + untrusted `HintCert` reflection | **`22–30` authored LOC** (**`9.7x` $\downarrow$** vs. raw `.o`), **`177–454 ms`** warm replay, `F1..F5` footguns rejected at `rustc` compile time | **`0` added TCB lines** beyond `.o` ISA operational semantics (`asm_verified!` and `UntrustedHints.*` are 100% untrusted; `type_hints == 0`) |

## Boundaries

- **Known not to apply — MIR-level `SafeTwin` equivalence for constant-time / side-channel resistance:** As proved in [`support/lean/MirTwin_CtLookup8.lean`](support/lean/MirTwin_CtLookup8.lean) (`llvm_jump_table_functional_but_leaks`) and observed on `rustc 1.99.1 -O` (`ct_lookup8_naive_rust`), two functions that are 100% equivalent at `Runtime(PostCleanup)` MIR can differ catastrophically in secret-dependent branches and memory accesses after LLVM `SimplifyCFG` / `SwitchToLookupTable` lowering. Any constant-time `2-safety` (`LeakTrace`) claim **must** be verified at `.o` machine-code level (Path B), never purely at MIR.
- **Known not to apply — `core::arch` `_addcarryx_u64` guaranteeing hardware `adcx`/`adox` dual carry chains:** On `rustc 1.99.1 -O` (`LLVM 23.1.1`), `_mulx_u64` + `_addcarryx_u64` under `#[target_feature(enable = "bmi2,adx")]` emits `0` `adcx`/`adox` instructions. Throughput-critical multi-precision arithmetic requiring dual carry chains must use `asm_verified!` (Path B).
- **Unsupported in stable `rustc 1.99.1` and `1.100.0` — Direct `#[target_feature]` on `#[unsafe(naked)]` functions:** Rejected with `E0658` (`rust-lang/rust#138568`); `asm_verified!`'s private-naked + public-`#[inline] #[target_feature]` shim is required on stable toolchains.
- **Not examined — `aarch64` NEON/SVE, `riscv64` RVV, and `x86_64` AVX-512 mask-register `.o` decoding:** The production crate census recorded `14` non-x86 `asm!` sites (`zlib-rs` AArch64/LoongArch, `sha2` LoongArch/RISC-V) and `12` AVX-512 `pternlog`/`vpdpbusd`/`permvar` sites, but the `80`-cell MIR-vs-`.o` stability matrix and `AsmMirBase.lean` byte decoder were executed only for `x86_64` System V + SSE2/AVX2/PCLMULQDQ/BMI2/ADX.
- **Not examined — Cross-crate LTO (`-C lto=fat`) and PGO perturbations on `.o` vs. post-link ELF:** `.o` churn was measured on relocatable object files (`--emit=obj`); link-time optimization and BOLT/PGO post-link layout will increase machine-code churn further while leaving `Runtime(PostCleanup)` MIR unchanged.
- **Unknown — Asymptotic `rfl` certificate-checking crossover on `>500`-instruction straight-line kernels with `List UInt8` code representation:** On 20–31-instruction kernels (`98–125` B), `List UInt8` `byteAt` lookup inside kernel `rfl` takes `177–454 ms`. Exact scaling past `500` instructions (`>2.5 KB`, e.g., fully unrolled SHA-256 or Kyber NTT) without switching `code` from `List UInt8` to a radix/binary tree was not measured.
- **Attractive stronger conclusions not established by the evidence:**
  - *"`24` MIR primitives verify `98.9%` of Rust crates end-to-end without Pass 2 work":* False. Covering `98.94%` of `core::arch::x86_64` call sites at MIR eliminates *per-function* `.o` lifting, but Pass 2 still owes a one-time-per-toolchain correspondence check that `rustc`+LLVM lowers those `24` primitives (`16` `simd_*` + `8` `llvm.x86.*` families) faithfully on the pinned toolchain archive.
  - *"`asm_verified!` makes `.o` proofs completely immune to `rustc` upgrades":* False for inline `asm!` surrounded by Rust code, and qualified even for `naked_asm!`. Because `asm_verified!` emits `#[unsafe(naked)]` `naked_asm!`, `rustc`/LLVM register allocation is bypassed, **but** LLVM's integrated MC assembler can still change instruction-length encodings (e.g., `rel8` vs. `rel32` jumps if target labels move). However, because `HintCert` byte offsets are regenerated automatically from the compiled `.o` symbol bytes, only structural changes to the assembly template itself require updating `UntrustedHints` checkers.

## Evidence

### Primary Upstream Sources and Specifications

- **`rustc` inline-assembly type/target-feature checking (`normative` + `source`):** `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `compiler/rustc_hir_typeck/src/inline_asm.rs` (`InlineAsmCtxt::check_asm`, clobber skip `if !op.is_clobber()`) and `E0658` gate on `#[unsafe(naked)]` + `#[target_feature]`.
- **`stdarch` `core::arch::x86_64` implementation (`source`):** Shipped `rust-src` component in `rustc 1.99.1` (`library/stdarch/crates/core_arch/src/x86/*.rs`, `6,064` functions, `1,052` `llvm.x86.*` external links).
- **Lean 4 kernel replay interface (`normative` + `source`):** `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), `Lean.Environment.Replay` (`base.toKernelEnv.replay`) and `importModules` (`trustLevel := 0`, `plugins := #[]`, `loadExts := false`, `level := .private`).
- **Anneal trust model and Statement-Origin Separation (`normative`):** `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), `THREAT_MODEL.md` and `trusted/audit/`.

### Preserved Support Artifacts (`support/`)

All probes and Lean 4 modules were executed on `2026-11-21` on `x86_64-unknown-linux-gnu` inside clean temporary directories:

| Path | Size (`B`) | SHA-256 | Role |
| :--- | ---: | :--- | :--- |
| [`support/probe_core_arch_mir_vs_obj_stability.py`](support/probe_core_arch_mir_vs_obj_stability.py) | `35,007` | `f94007abdda45aa6d5d08894c0d2fa655b11c20fe85c298263953a4ae7d5b66a` | 12-crate + `rav1d` SIMD census, `stdarch` leaf tracer, `libcore` inlining probe, and 80-cell MIR-vs-`.o` stability harness |
| [`support/probe_core_arch_mir_vs_obj_stability_results.json`](support/probe_core_arch_mir_vs_obj_stability_results.json) | `71,401` | `03bd77adf732190a5b20f8e190ed79f2cac8d56ed1cf0540ba3b568a647c389f` | Complete JSON measurements for all 80 compilation cells and `167` `core::arch` intrinsics |
| [`support/probe_asm_verified_macro_and_obj.py`](support/probe_asm_verified_macro_and_obj.py) | `34,721` | `b80f3da74e49e8f1b6120d751d7875b36444e0d9b715bbda5a024113b8821cc7` | Working Rust `#[proc_macro]` (`asm_verified!`), `F1..F5` negative compile-error tests, differential execution, and ELF64 `.o` extractor |
| [`support/probe_asm_verified_macro_and_obj_results.json`](support/probe_asm_verified_macro_and_obj_results.json) | `24,287` | `5b12a6c7dbe0cc727380365e2c0a5f151349ad945a7023fdaa0346f05886f8f1` | Extracted `.o` byte arrays, SHA-256s, disassemblies, and `F1..F5` compiler diagnostics |
| [`support/bench_three_regimes_lean4.py`](support/bench_three_regimes_lean4.py) | `15,435` | `3bc0f5962e68a87bfc812f22c0c7ed092b0de1b92826f4f3d233e134caf7fe62` | Lean `v4.34.1` 12-module build benchmark and standalone `ReplayAudit.lean` `(level := .private)` kernel replay harness |
| [`support/bench_three_regimes_lean4_results.json`](support/bench_three_regimes_lean4_results.json) | `9,121` | `5bcfc0120913dc40dac01547eca253c3dfd672b686c085ba7c661df654fa0dc9` | Exact LOC, `.olean` bytes, compile wall-clock, and 14 private-replay audit records |
| [`support/lean/AsmMirBase.lean`](support/lean/AsmMirBase.lean) | `28,675` | `254981af668ad18ba1ec360431b3e5eb467b5ce9f25a2c3e8a08cd0257b0440f` | Tactic-free x86-64 byte decoder (`decodeX86At`), operational state machine, `.o` byte constants, and MIR/reference specs |
| [`support/lean/IsaLemmas.lean`](support/lean/IsaLemmas.lean) | `18,387` | `bfdbf08564959e9d0b76f06225e5bbee332483bd1243f79ea51ccc6074535c3a` | 320-bit dual-carry conservation (`mac4_combine_conservation`), 256-bit SIMD reduction, and abstract `exec_*` lemmas |
| [`support/lean/UntrustedHints.lean`](support/lean/UntrustedHints.lean) | `56,952` | `cc23f8d3f9de525fc0f2795c8b86866c2d70b4f534ed7f6a386b2482c3186316` | Untrusted `DualCarryMac4Cert`, `SimdDotUnroll2Cert`, and `CtLinearScan8Cert` boolean checkers + soundness theorems |
| [`support/lean/RawObj_MulxMac4.lean`](support/lean/RawObj_MulxMac4.lean) | `15,629` | `d42313411441f842f351beafb08f9bc80811887efc97cc56878eea03d6371647` | Regime (a) unassisted `.o` proof for `mulx_adcx_adox_mac4` (`269` authored LOC) |
| [`support/lean/HintObj_MulxMac4.lean`](support/lean/HintObj_MulxMac4.lean) | `2,047` | `9fab9ae562c7a293c2b949bd7412a711e2bf73ca43c45b4ad632adf8c3d2aa64` | Regime (b) `HintCert`-assisted `.o` proof for `mulx_adcx_adox_mac4` (`30` authored LOC + `7` cert LOC) |
| [`support/lean/MirTwin_MulxMac4.lean`](support/lean/MirTwin_MulxMac4.lean) | `4,273` | `6d6ee9711191ac0625ba879256de6fb6cf5fb95ec0abe92b9af9cd8f335558b4` | Regime (c) MIR `SafeTwin` proof for `mulx_adcx_adox_mac4` (`74` authored LOC) |
| [`support/lean/RawObj_DotMaddubs.lean`](support/lean/RawObj_DotMaddubs.lean) | `19,143` | `ee4e808409c0c12a5e3f9325b8bd362495fc378a3d463747dbb617fce144324f` | Regime (a) unassisted `.o` loop proof for `dot_maddubs_unroll2` (`312` authored LOC) |
| [`support/lean/HintObj_DotMaddubs.lean`](support/lean/HintObj_DotMaddubs.lean) | `1,685` | `d922f3f69e849ecc315f7d4f04e546b6ec9a039b8c53101de72df3d8944ff398` | Regime (b) `HintCert`-assisted `.o` loop proof for `dot_maddubs_unroll2` (`22` authored LOC + `8` cert LOC) |
| [`support/lean/MirTwin_DotMaddubs.lean`](support/lean/MirTwin_DotMaddubs.lean) | `1,503` | `84118c6822f6a9ffcd7d8887cf7b4ad537f4f88bb470fb97b1758c078b6c6321` | Regime (c) MIR `SafeTwin` proof for `dot_maddubs_avx2` (`28` authored LOC) |
| [`support/lean/RawObj_CtLookup8.lean`](support/lean/RawObj_CtLookup8.lean) | `11,930` | `36d695b00b6d5c32c314512cb3f4cd3f972c260fab40eca75c5be46d0a81a3e9` | Regime (a) unassisted `.o` functional + 2-safety proof for `ct_lookup8_cmov` (`187` authored LOC) |
| [`support/lean/HintObj_CtLookup8.lean`](support/lean/HintObj_CtLookup8.lean) | `2,136` | `c7faa34250083a9d40c135970e98967b72ceeb73d382ef84fcd7b8f36b37054a` | Regime (b) `HintCert`-assisted `.o` functional + 2-safety proof for `ct_lookup8_cmov` (`27` authored LOC + `7` cert LOC) |
| [`support/lean/MirTwin_CtLookup8.lean`](support/lean/MirTwin_CtLookup8.lean) | `3,142` | `cd8574027edefe241e29aa1e155c1b665a7331367e235a79918f77c8064317ab` | Regime (c) MIR proof + `llvm_jump_table_functional_but_leaks` refutation (`64` authored LOC) |

## Revalidation

Re-run this investigation whenever:
1. `rustc` changes MIR `Inline` target-feature gating on `stdarch` SIMD conversion helpers or stabilizes `#![feature(naked_functions_target_feature)]` (`rust-lang/rust#138568`);
2. `stdarch` migrates additional `llvm.x86.*` links to portable `#[rustc_intrinsic]` `simd_*` operations;
3. Lean 4 updates kernel WHNF reduction or `Lean.Environment.Replay` (`(level := .private)`) semantics.

### Self-Contained Reproduction Commands

From the package directory (`reports/zero-tcb-verified-asm-macros-and-core-arch-mir-equivalence-stability/`), with `rustup` toolchains (`nightly-2026-06-01`, `1.99.1`, `1.100.0`, `nightly-2026-11-12`), `objdump`, and Lean `v4.34.1` installed:

```bash
# 1. Re-run 12-crate SIMD Pareto census + 80-cell MIR-vs-.o stability matrix
PYTHONDONTWRITEBYTECODE=1 python3 -B support/probe_core_arch_mir_vs_obj_stability.py

# 2. Re-run `asm_verified!` #[proc_macro] F1..F5 footgun gates, differential tests, and .o byte extraction
PYTHONDONTWRITEBYTECODE=1 python3 -B support/probe_asm_verified_macro_and_obj.py

# 3. Compile all 12 Lean v4.34.1 modules (-DElab.async=false -Ddebug.skipKernelTC=false -j1)
#    and run standalone (trustLevel := 0, level := .private) kernel replay audit
PYTHONDONTWRITEBYTECODE=1 python3 -B support/bench_three_regimes_lean4.py
```

Verify that:
- `probe_core_arch_mir_vs_obj_stability.py` exits `0` with `distinct_postcleanup_mir_hashes == 1` across all 5 kernels and `distinct_obj_byte_hashes >= 2`;
- `probe_asm_verified_macro_and_obj.py` exits `0` with all 5 negative footgun gates (`F1..F5`) failing compilation (`rc == 1`), `ASM_VERIFIED_DIFF_OK`, and identical `.text` SHA-256 digests (`69eb8ffe...`, `687c2b8c...`, `878fff95...`);
- `bench_three_regimes_lean4.py` exits `0` with all 12 `.lean` modules compiling cleanly, all 14 `ReplayAudit.lean` checks reporting `type_hints == 0`, matching `type_hash` between `RawObj_<k>` and `HintObj_<k>`, and transitive axioms strictly within `{"Classical.choice", "Quot.sound", "propext"}`.
