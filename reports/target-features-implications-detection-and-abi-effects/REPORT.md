# Rust Target Features: Semantics, Implication Graphs, Runtime Detection, and ABI Effects in `rustc` 1.99.1 and LLVM 23.1.1

## Summary

A drop-in verified replacement for `rustc` that does not link LLVM must independently reproduce
every behavior of `rustc` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) that currently
queries `llvm::LLVMRustHasFeature` or LLVM's subtarget tables (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):

1. **Feature catalogs, stability tiers, and Rust-vs.-LLVM name mappings (`compiler/rustc_target/src/target_features.rs` & `compiler/rustc_codegen_llvm/src/llvm_util.rs:239-336`):**
   - At the `1.99.1` baseline, `rustc` declares **80** `X86_FEATURES` (`54` `Stable`, `22`
     `Unstable`, `4` `InternalOnly`) and **94** `AARCH64_FEATURES` (`39` `Stable`, `53`
     `Unstable`, `2` `InternalOnly`), plus `1` global `RUSTC_SPECIFIC_FEATURES` entry
     (`"crt-static"`).
   - Seven x86 features (`sse4.2` $\to$ `sse4.2` + EnableOnly `crc32`, `pclmulqdq` $\to$ `pclmul`,
     `rdrand` $\to$ `rdrnd`, `bmi1` $\to$ `bmi`, `cmpxchg16b` $\to$ `cx16`, `lahfsahf` $\to$ `sahf`,
     `apxf` $\to$ `egpr` + 7 subfeatures) and 14 AArch64 features (`rcpc2` $\to$ `rcpc-immo`,
     `dpb` $\to$ `ccpp`, `dpb2` $\to$ `ccdp`, `frintts` $\to$ `fptoint`, `fcma` $\to$ `complxnum`,
     `pmuv3` $\to$ `perfmon`, `paca`/`pacg` $\to$ tied `pauth`, `flagm2` $\to$ `altnzcv`,
     `neon` $\to$ `neon` + Both `fp-armv8`, `fhm` $\to$ `fp16fml`, `fp16` $\to$ `fullfp16`,
     and filtered `fpmr`/`tme` $\to$ `None`) have non-identity `to_llvm_features` translations.
2. **Two-stage `cfg(target_feature)` and `sess.target_features` computation (`compiler/rustc_codegen_ssa/src/target_features.rs:273-545`):**
   - **Stage A (CPU baseline via LLVM subtarget):** Queries the target CPU's LLVM feature bits
     (`X86.td` / `AArch64Processors.td` + target-spec `features`), retaining only features `f`
     for which *all* mapped `to_llvm_features(f)` bits are set in LLVM **and** all features in
     Rust's transitive `implied_target_features(f)` closure are also set.
   - **Stage B (`-Ctarget-feature` delta via Rust's implication graph only):** Applies `+feat`
     (adding transitive forward implications in `rust_target_features_map`) and `-feat`
     (removing transitive reverse implications in `rust_target_features_map`), **without**
     re-running LLVM's implication graph.
   - **Divergence between Rust and LLVM implication graphs:** On AArch64, Rust's `sve` implies
     `["neon", "fp16"]`, whereas LLVM's `FeatureSVE` (`AArch64Features.td`) implies `fullfp16`
     (`fp16`) but **not** `neon` (or `v8.2a` implies `ras`/`ccpp` in LLVM, while `sve` is
     orthogonal to `neon` in Arm's architecture manual). Conversely, LLVM's `apple-m1` CPU
     enables `FeatureLSE2` (`lse2`) and `FeatureAltNZCV` (`flagm2`) via `ArchV8_4aOps`, whereas
     Rust's `v8.4a` implies `["v8.3a", "dotprod", "dit", "flagm"]` **without** `lse2` or
     `flagm2`!
3. **`#[target_feature]` safety (RFC 2396 `target_feature 1.1`), MIR/LLVM inlining, and `-Ctarget-cpu`:**
   - Safe functions may carry `#[target_feature(enable = "...")]`: calling them from a function
     with identical or superset `#[target_feature]`s is safe, whereas calling them from a
     context lacking any enabled feature requires `unsafe`.
   - The MIR inliner (`compiler/rustc_mir_transform/src/inline.rs`) and LLVM's
     `TTI::areInlineCompatible` (`X86TargetTransformInfo.cpp`, `AArch64TargetTransformInfo.cpp`)
     forbid inlining a callee into a caller unless `caller_features ⊇ callee_features`, even
     when the callee is marked `#[inline(always)]` (`from_target_feature_attr` in
     `compiler/rustc_codegen_ssa/src/target_features.rs:140-195` rejects combining
     `#[inline(always)]` with `#[target_feature]` via a hard error!).
4. **Runtime detection in `std_detect` (`library/std_detect/src/detect/**`):**
   - Uses a lock-free 3-word atomic bitset cache (`static CACHE: [Cache; 3]`, storing up to
     `3 × 31 = 93` feature bits in `AtomicU32` with bit 31 as the initialized tag) populated on
     first query by OS/ISA-specific probes: `cpuid` + `_xgetbv(0)` on x86/x86_64 (`os/x86.rs`),
     `getauxval(AT_HWCAP)` / `AT_HWCAP2` with `/proc/self/auxv` fallback on Linux AArch64
     (`os/linux/aarch64.rs`), `sysctlbyname("hw.optional.arm.FEAT_*")` on macOS AArch64
     (`os/darwin/aarch64.rs`), and `IsProcessorFeaturePresent(PF_ARM_*)` on Windows AArch64
     (`os/windows/aarch64.rs`).
5. **ABI-relevant features (`abi_required_features` & `features_for_correct_fixed_length_vector_abi`):**
   - `x86` requires `x87` and forbids `soft-float` (`x86-sse2` additionally requires `sse2`);
     `x86_64` requires `x87` and `sse2` and forbids `soft-float`; `aarch64` requires `neon`
     (which is tied to `fp-armv8`).
   - Passing 128-bit, 256-bit, or 512-bit SIMD vectors by value across non-Rust FFI ABIs
     (`extern "C"`, `"sysv64"`, `"win64"`, `"vectorcall"`) checks
     `X86_FEATURES_FOR_CORRECT_FIXED_LENGTH_VECTOR_ABI` (`128b -> sse`, `256b -> avx`,
     `512b -> avx512f`) and `AARCH64_FEATURES_FOR_CORRECT_FIXED_LENGTH_VECTOR_ABI` (`128b -> neon`,
     scalable -> `sve`), emitting a hard error or lint if the required vector feature is not
     enabled at the call site or definition.

The complete machine-readable feature database (`80` x86 features, `94` AArch64 features,
`36` Arm features, `105` RISC-V features, `14` Wasm features, `136` x86 CPUs, `84` AArch64 CPUs)
and `--print cfg` goldens across 38 target-CPU combinations are preserved in
`support/target_feature_database.json` and `support/cpu_cfg_goldens.json`.

## Applicability

- **Primary subjects:** `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`)
  and `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`).
- **Scope:** Covers x86/x86_64 and AArch64 target-feature tables, implication graphs, CPU models,
  `#[target_feature]` checking and inlining rules, `std_detect` runtime detection across Linux,
  macOS, and Windows, and ABI feature constraints across all 8 Tier 1 targets.

## Findings

### 1. Baseline Target-Feature Catalogs, Stability Tiers, and LLVM Mapping (`rustc` 1.99.1)

Basis: source (`compiler/rustc_target/src/target_features.rs:216-560`, `compiler/rustc_codegen_llvm/src/llvm_util.rs:239-336`) + execution (`support/target_feature_database.json`)

#### 1.1 Summary Counts by Architecture and Stability Tier

| Architecture | Total Rust Features | `Stable` | `Unstable(sym::...)` | `InternalOnly` | Vector ABI Gates (`FEATURES_FOR_CORRECT_FIXED_LENGTH_VECTOR_ABI`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`x86` / `x86_64`** (`X86_FEATURES`) | **80** | **54** | **22** (`amx-*` (8), `apxf`, `avx10.1`, `avx10.2`, `clflushopt`, `ermsb`, `fma4`, `lahfsahf`, `movrs`, `prfchw`, `rtm`, `x87`, `xop`, plus 2 `avx512*`/misc) | **4** (`retpoline-external-thunk`, `retpoline-indirect-branches`, `retpoline-indirect-calls`, `soft-float`) | `(128, "sse")`, `(256, "avx")`, `(512, "avx512f")` |
| **`aarch64`** (`AARCH64_FEATURES`) | **94** | **39** | **53** (`cssc`, `ecv`, `faminmax`, `flagm2`, `fp8*` (4), `hbc`, `lse2`, `lse128`, `lut`, `mops`, `outline-atomics`, `pauth-lr`, `rcpc3`, `sme*` (11), `ssve-fp8*` (3), `sve-b16b16`, `sve2p1`, `v8.1a`..`v8.9a` (9), `v9a`..`v9.5a` (6), `wfxt`) | **2** (`fp-armv8`, `reserve-x18`) | `(128, "neon")`; scalable: `Some("sve")` |
| **`arm`** (`ARM_FEATURES`) | **36** | `0` | `35` | `1` (`atomics-32`) | `(128, "neon")`, `(128, "mve")` |
| **`riscv32` / `riscv64`** (`RISCV_FEATURES`) | **105** | `52` | `52` | `1` (`forced-atomics`) | `zvl32b`..`zvl65536b` (12 steps) |
| **`wasm32` / `wasm64`** (`WASM_FEATURES`) | **14** | `11` | `3` | `0` | `(128, "simd128")` |

#### 1.2 Complete Non-Identity `to_llvm_features` Translations (`llvm_util.rs:239-336`)

Every Rust feature name maps 1-to-1 to an identical LLVM `SubtargetFeature` name **except** for
the following 21 entries on `x86`/`x86_64` and `aarch64`:

| Architecture | Rust Feature | LLVM Feature(s) (`LLVMFeature`) | Fold Strength / Tie Rule |
| :--- | :--- | :--- | :--- |
| `x86` / `x86_64` | `sse4.2` | `"sse4.2"` + `"crc32"` | `EnableOnly("crc32")`: `+sse4.2` enables `+crc32`, but `-sse4.2` does not disable `crc32` |
| `x86` / `x86_64` | `pclmulqdq` | `"pclmul"` | 1-to-1 rename |
| `x86` / `x86_64` | `rdrand` | `"rdrnd"` | 1-to-1 rename |
| `x86` / `x86_64` | `bmi1` | `"bmi"` | 1-to-1 rename |
| `x86` / `x86_64` | `cmpxchg16b` | `"cx16"` | 1-to-1 rename |
| `x86` / `x86_64` | `lahfsahf` | `"sahf"` | 1-to-1 rename |
| `x86` / `x86_64` | `apxf` | `"egpr"`, `"push2pop2"`, `"ppx"`, `"ndd"`, `"ccmp"`, `"cf"`, `"nf"`, `"zu"` | `Both(...)`: all 8 LLVM subfeatures are toggled together |
| `aarch64` | `neon` | `"neon"` + `"fp-armv8"` | `Both("fp-armv8")`: Rust ties `neon` and `fp-armv8` together |
| `aarch64` | `fp16` | `"fullfp16"` | 1-to-1 rename |
| `aarch64` | `fhm` | `"fp16fml"` | 1-to-1 rename |
| `aarch64` | `rcpc2` | `"rcpc-immo"` | 1-to-1 rename |
| `aarch64` | `dpb` | `"ccpp"` | 1-to-1 rename |
| `aarch64` | `dpb2` | `"ccdp"` | 1-to-1 rename |
| `aarch64` | `frintts` | `"fptoint"` | 1-to-1 rename |
| `aarch64` | `fcma` | `"complxnum"` | 1-to-1 rename |
| `aarch64` | `pmuv3` | `"perfmon"` | 1-to-1 rename |
| `aarch64` | `flagm2` | `"altnzcv"` | 1-to-1 rename |
| `aarch64` | `paca`, `pacg` | `"pauth"` | Tied in `AARCH64_TIED_FEATURES`: `#[target_feature]` must enable both `paca` and `pacg` together or LLVM's single `pauth` feature cannot represent them |
| `aarch64` | `tme`, `fpmr` | `None` (filtered out on LLVM $\ge 22$) | `tme` was withdrawn by Arm and removed in LLVM 22; `fpmr` only existed in LLVM 18 |

#### 1.3 Divergences Between Rust's and LLVM 23.1.1's Implication Graphs

A standalone compiler reproducing `rustc` without LLVM must implement **both** LLVM's CPU
feature sets (for `-Ctarget-cpu`) and Rust's `ImpliedFeatures` DAG (for `-Ctarget-feature`,
`#[target_feature]`, and `cfg(target_feature)` filtering):
1. **AArch64 architecture version implications (`v8.1a`..`v9.5a`):**
   - In `llvm/lib/Target/AArch64/AArch64Features.td:600-760`, `HasV8_4aOps` implies
     `FeatureLSE2` (`lse2`), `FeatureAltNZCV` (`flagm2`), `FeatureFRInt3264` (`frintts`), and
     `FeatureTLB_RMI`, whereas in `rustc` (`target_features.rs:402`), `v8.4a` implies only
     `["v8.3a", "dotprod", "dit", "flagm"]`! Consequently, `-Ctarget-cpu=apple-m1` (which
     has `HasV8_4aOps` in `AArch64Processors.td`) enables `lse2`, `flagm2`, and `frintts`,
     whereas `-Ctarget-feature=+v8.4a` on `aarch64-unknown-linux-gnu` does **not** enable
     `lse2`, `flagm2`, or `frintts`!
2. **AArch64 `sve`, `fp16`, `jsconv`, `fcma`, `aes`, `sha2`, `rdm`, `dotprod`, `sm4`:**
   - In `rustc`, all of these explicitly imply `"neon"` (`sve -> ["neon", "fp16"]`). In LLVM's
     `AArch64Features.td`, `FeatureSVE` implies `FeatureFullFP16` (`fullfp16`), which implies
     `FeatureFPARMv8` (`fp-armv8`), **without** implying `FeatureNEON` (`neon`). Because
     `internal_target_features` (`compiler/rustc_codegen_ssa/src/target_features.rs:425-445`)
     filters out any CPU feature whose Rust-implied features are not also enabled in LLVM,
     if a target disables `neon`, `rustc` automatically strips `fp16` and `sve` from
     `cfg(target_feature)`.
3. **x86 `avx512f` and `sse4.2`:**
   - In `rustc`, `avx512f` implies `["avx2", "fma", "f16c"]`; in LLVM's `X86.td`, `FeatureAVX512`
     matches this (`FeatureAVX2`, `FeatureFMA`, `FeatureF16C`).
   - In `rustc`, `sse4.2` does not list `popcnt` in `ImpliedFeatures` (and `avx` implies
     `sse4.2` without `popcnt`), whereas in LLVM `X86.td`, `FeatureSSE42` implies `FeatureSSE41`
     (and `crc32` is added by `to_llvm_features`), keeping `popcnt` independent.

### 2. Rules for `#[target_feature]`, Safe Target-Feature Calls, Inlining, and `-Ctarget-cpu`

Basis: source (`compiler/rustc_codegen_ssa/src/target_features.rs:22-545`, `compiler/rustc_mir_transform/src/inline.rs`, `llvm/lib/Analysis/InlineCost.cpp`, `llvm/lib/TargetParser/Host.cpp`) + execution (`support/cpu_cfg_goldens.json`)

1. **Safe `#[target_feature]` (`target_feature 1.1`, RFC 2396, stabilized in Rust 1.86):**
   - Both safe `fn` and `unsafe fn` may carry `#[target_feature(enable = "...")]` (provided the
     function is not a trait implementation method, `main`, `#[no_mangle]`/`export_name` with
     wrong ABI, etc.).
   - Calling a safe `#[target_feature(enable = "F")]` function `callee` from `caller` is safe
     without an `unsafe` block **if and only if** every feature in `callee.target_features` is
     statically enabled in `caller` (either via `caller`'s own `#[target_feature]` transitive
     closure or via global `sess.target_features`). Otherwise `rustc` requires an `unsafe` block.
2. **Interaction with `#[inline]` and `#[inline(always)]`:**
   - **Hard error on `#[inline(always)]` + `#[target_feature]` (`compiler/rustc_codegen_ssa/src/target_features.rs:159-165`):**
     `rustc` emits a hard compile error (`cannot use #[inline(always)] with #[target_feature]`)
     when both attributes appear on the same function, because LLVM's `AlwaysInline` pass or
     MIR inlining across mismatched target features could hoist target-specific SIMD instructions
     into a caller lacking those features.
   - **MIR inliner check (`compiler/rustc_mir_transform/src/inline.rs`):** A callee with
     `tcx.codegen_fn_attrs(callee).target_features` is inlined into a caller only if
     `callee_features.iter().all(|f| caller_features.contains(f))` (i.e. `caller ⊇ callee`).
   - **LLVM `TTI::areInlineCompatible` (`X86TargetTransformInfo.cpp` & `AArch64TargetTransformInfo.cpp`):**
     Enforces that the caller's `FeatureBitset` is a superset of the callee's `FeatureBitset` on
     relevant ISA/ABI features (and on AArch64, forbids inlining across mismatched SME
     `streaming-compatible` / `pstate_sm` attributes).
3. **Accepted `-Ctarget-cpu` Names and `-Ctarget-cpu=native` Host Detection:**
   - On `rustc` `1.99.1` (LLVM 23.1.1), `--print target-cpus` accepts **136** CPU names on
     `x86_64`/`i686` (`llvm/include/llvm/TargetParser/X86TargetParser.def`, from `i386` and
     `pentium4` through `x86-64`, `x86-64-v2`, `x86-64-v3`, `x86-64-v4`, `sapphirerapids`,
     `graniterapids`, `arrowlake`, `pantherlake`, `diamondrapids`, `znver1`..`znver5`) and **84**
     CPU names on `aarch64` (`llvm/include/llvm/TargetParser/AArch64TargetParser.h` and
     `AArch64Processors.td`, from `generic` and `cortex-a35`..`cortex-x925` through
     `neoverse-n1`/`n2`/`n3`/`v1`/`v2`/`v3`, `apple-m1`..`apple-m4`, `ampere1`/`1a`/`1b`,
     `oryon-1`).
   - **`-Ctarget-cpu=native` (`llvm/lib/TargetParser/Host.cpp:getHostCPUName` & `getHostCPUFeatures`):**
     On x86/x86_64, executes `cpuid` leaf `0`, `1` (family/model/stepping), `7`, and `0x80000001`
     plus `xgetbv(0)` (checking OS `XCR0` support for XMM/YMM/ZMM/AMX states before enabling
     `avx`/`avx512f`/`amx-tile`). On Linux AArch64, parses `/proc/cpuinfo` (`CPU implementer`
     and `CPU part` MIDR fields). On macOS AArch64, queries `sysctlbyname("hw.cpufamily")`.
4. **How `cfg(target_feature)` is Computed (`compiler/rustc_codegen_ssa/src/target_features.rs:480-545`):**
   - After computing the active feature set (`Stage A` CPU features $\cup$ `Stage B`
     `-Ctarget-feature` additions $\setminus$ `-Ctarget-feature` removals), `rustc` emits
     `target_feature="<name>"` in `sess.psess.unstable_target_features` for every active feature
     with `gate.in_cfg() == true` (`Stable`, `CfgStableToggleUnstable`, or `Unstable`), and in
     `sess.psess.target_features` (visible to stable `#[cfg(target_feature = "...")]`) only for
     `Stable` and `CfgStableToggleUnstable` features.
   - For example, on `x86_64-unknown-linux-gnu`:
     - Default (`-Ctarget-cpu=x86-64`): stable `cfg(target_feature)` is `["fxsr", "sse", "sse2"]`
       (plus unstable `["x87"]` on nightly).
     - `-Ctarget-cpu=x86-64-v2`: adds `["cmpxchg16b", "popcnt", "sse3", "sse4.1", "sse4.2", "ssse3"]`
       (plus unstable `["lahfsahf"]`).
     - `-Ctarget-cpu=x86-64-v3`: adds `["avx", "avx2", "bmi1", "bmi2", "f16c", "fma", "lzcnt", "movbe", "xsave"]`.
     - `-Ctarget-cpu=x86-64-v4`: adds `["avx512bw", "avx512cd", "avx512dq", "avx512f", "avx512vl"]`.

### 3. Runtime Feature Detection and Caching in `std_detect` (`is_x86_feature_detected!`, `is_aarch64_feature_detected!`)

Basis: source (`library/std_detect/src/detect/cache.rs:1-203`, `os/x86.rs:1-335`, `os/linux/aarch64.rs:1-409`, `os/darwin/aarch64.rs:1-168`, `os/windows/aarch64.rs:1-173`)

1. **Lock-Free 3-Word Atomic Cache (`library/std_detect/src/detect/cache.rs:27-190`):**
   - `std_detect` stores up to **`CACHE_CAPACITY = 93`** feature bits across three `AtomicUsize`
     words (`static CACHE: [Cache; 3]`, where each `Cache(AtomicUsize)` uses the lower `31` bits
     for features and bit `31` (`INITIALIZED_BIT = 1 << 31`) as the initialization flag, so it
     fits in 32-bit `AtomicUsize` on `i686` as well as 64-bit targets).
   - If a feature is already statically enabled in `cfg(target_feature = "...")` at compile time,
     `is_x86_feature_detected!("...")` / `is_aarch64_feature_detected!("...")` constant-folds
     directly to **`true`** with zero runtime instructions!
   - Otherwise, `cache::test(bit)` performs one `Ordering::Relaxed` atomic load from
     `CACHE[bit / 31]`; on cold miss (when bit `31` is `0`), it calls `os::detect_features()`
     and stores all three bitmasks with `Ordering::Relaxed` (idempotent across racing threads).
2. **Per-OS Runtime Detection Mechanisms:**
   - **x86 / x86_64 (all OSes — Linux, macOS, Windows: `library/std_detect/src/detect/os/x86.rs:27-335`):**
     Executes `__cpuid(0)`, `__cpuid(1)`, `__cpuid_count(7, 0)`, `__cpuid_count(7, 1)`,
     `__cpuid_count(0xD, 1)` (`xsaveopt`/`xsavec`/`xsaves`), `__cpuid(0x80000000)`, and
     `__cpuid(0x80000001)` (`lzcnt`/`sse4a`/`tbm`/`prfchw`/`lahfsahf`). Crucially, before enabling
     any AVX, AVX-512, or AMX feature, it checks that `proc_info_ecx` has `osxsave` (bit 27) and
     executes **`_xgetbv(0)`** (`L197-245`):
     - `XCR0 & 0b110 == 0b110` (XMM + YMM state enabled by OS) is required for `avx`, `avx2`,
       `fma`, `f16c`, `vaes`, `vpclmulqdq`, `avxvnni*`, `sha512`, `sm3`, `sm4`.
     - `XCR0 & 0b1110_0110 == 0b1110_0110` (`opmask` `k0..k7` + `ZMM_Hi256` + `Hi16_ZMM`) is
       additionally required for all `avx512*` and `avx10.*` features (with Darwin's on-demand
       AVX-512 allocation handled when `XCR0` bits are not yet set).
     - `XCR0 & (0b11 << 17) == (0b11 << 17)` (`XTILECFG` + `XTILEDATA`) is required for `amx-*`.
   - **AArch64 Linux (`library/std_detect/src/detect/os/linux/aarch64.rs:7-409` & `auxvec.rs:47-221`):**
     Calls `libc::getauxval(AT_HWCAP)` (`16`) and `libc::getauxval(AT_HWCAP2)` (`26`), falling
     back to reading `/proc/self/auxv` if `getauxval` returns `0` (`auxvec::auxv()`), and maps
     the 64-bit `hwcap` and `hwcap2` bitmasks (`HWCAP_FP`, `HWCAP_ASIMD`, `HWCAP_ATOMICS` for
     `lse`, `HWCAP_LRCPC` for `rcpc`, `HWCAP_ILRCPC` for `rcpc2`, `HWCAP_SVE`, `HWCAP2_SVE2`,
     `HWCAP2_MTE`, `HWCAP2_BTI`, `HWCAP2_SME`, etc.) to `Feature` bits, applying implication
     guards (e.g., enabling `asimd`/`neon` only if `fp` is also set).
   - **AArch64 macOS / Darwin (`library/std_detect/src/detect/os/darwin/aarch64.rs:10-168`):**
     Queries `libc::sysctlbyname` for `hw.optional.floatingpoint`, `hw.optional.AdvSIMD`, and
     `hw.optional.arm.FEAT_*` (`FEAT_LSE`, `FEAT_LRCPC`, `FEAT_LRCPC2`, `FEAT_DotProd`,
     `FEAT_FP16`, `FEAT_FHM`, `FEAT_AES`, `FEAT_PMULL`, `FEAT_SHA256`, `FEAT_SHA512`,
     `FEAT_SHA3`, `FEAT_BTI`, `FEAT_BF16`, `FEAT_I8MM`, `FEAT_FCMA`, `FEAT_JSCVT`, `FEAT_PAuth`,
     `FEAT_FlagM`, `FEAT_FlagM2`, `FEAT_FRINTTS`, `FEAT_SB`, `FEAT_SPECRES`, `FEAT_SSBS`, etc.).
   - **AArch64 Windows (`library/std_detect/src/detect/os/windows/aarch64.rs:6-173`):**
     Calls `kernel32!IsProcessorFeaturePresent(DWORD)` with Win32 constants:
     - `PF_ARM_VFP_32_REGISTERS_AVAILABLE` (`18`) & `PF_ARM_NEON_INSTRUCTIONS_AVAILABLE` (`19`) $\to$ `neon`
     - `PF_ARM_V8_CRC32_INSTRUCTIONS_AVAILABLE` (`31`) $\to$ `crc`
     - `PF_ARM_V81_ATOMIC_INSTRUCTIONS_AVAILABLE` (`34`) $\to$ `lse`
     - `PF_ARM_V82_DP_INSTRUCTIONS_AVAILABLE` (`43`) $\to$ `dotprod`
     - `PF_ARM_V83_JSCVT_INSTRUCTIONS_AVAILABLE` (`44`) $\to$ `jsconv`
     - `PF_ARM_V83_LRCPC_INSTRUCTIONS_AVAILABLE` (`45`) $\to$ `rcpc`
     - `PF_ARM_V8_CRYPTO_INSTRUCTIONS_AVAILABLE` (`30`) $\to$ `aes`, `sha2`
     - Plus `PF_ARM_SVE_*` (`46..58`) and `PF_ARM_SME_*` constants on newer Windows 11 builds.

### 4. ABI and Semantic Effects of Target Features

Basis: source (`compiler/rustc_target/src/target_features.rs:1101-1471`, `compiler/rustc_ty_utils/src/abi.rs:420-530`)

1. **Vector Argument Passing Diagnostics (`X86_FEATURES_FOR_CORRECT_FIXED_LENGTH_VECTOR_ABI` & `AARCH64_FEATURES_FOR_CORRECT_FIXED_LENGTH_VECTOR_ABI`):**
   - When a function uses a non-Rust ABI (`extern "C"`, `"sysv64"`, `"win64"`, `"vectorcall"`)
     and passes or returns a SIMD vector of bit-width $W$ (either directly or wrapped inside a
     transparent/HVA aggregate), `rustc` looks up the minimum `bits >= W` entry in
     `features_for_correct_fixed_length_vector_abi()`:
     - On `x86` / `x86_64`: $W \le 128 \implies \text{requires }\texttt{sse}$;
       $128 < W \le 256 \implies \text{requires }\texttt{avx}$;
       $256 < W \le 512 \implies \text{requires }\texttt{avx512f}$.
     - On `aarch64`: $W \le 128 \implies \text{requires }\texttt{neon}$; scalable SVE vectors
       require `sve`.
   - If the required feature is not enabled on the function (via `-Ctarget-feature`,
     `-Ctarget-cpu`, or `#[target_feature]`), `rustc` emits an ABI soundness error (`this function
     definition/call uses a vector type that requires the <feat> target feature, which is not
     enabled`), because LLVM lowers `<8 x float>` (`__m256`) to a single `ymm0` register when
     `+avx` is enabled, but splits it into `xmm0, xmm1` (or stack) when `-avx`!
2. **Target-Level ABI-Pinned Features (`Target::abi_required_features`):**
   - Disabling `sse2` on `x86_64` or `i686` (`RustcAbi::X86Sse2`), disabling `x87` on `x86`/`x86_64`,
     enabling `soft-float`, or disabling `neon` (`fp-armv8`) on `aarch64` changes how scalar
     floats are passed and returned. `rustc` marks `soft-float` and `fp-armv8` as `InternalOnly`
     (forbidding them in `#[target_feature]`) and emits a target-ABI warning if `-Ctarget-cpu`
     or `-Ctarget-feature` violates `Target::abi_required_features()` (for example,
     `-Ctarget-cpu=i586` on `i686-unknown-linux-gnu` warns:
     `warning: target feature sse2 must be enabled to ensure that the ABI of the current target can be implemented correctly`).
3. **Behavioral / State-Modifying Features (`reserve-x18`, `bti`/`paca`/`pacg`, `sme`):**
   - `reserve-x18` (`InternalOnly` on `aarch64`, controlled via `-Zfixed-x18`): Removes `x18`
     from the general-purpose register allocator so `x18` is never clobbered across function bodies.
   - `bti` and `paca`/`pacg` (controlled per-Target/Crate via `-Zbranch-protection=bti,pac-ret`):
     Insert `bti c` / `paciasp` + `autiasp` (`hint #25`/`#29`/`#34`) at function prologues and
     epilogues, which execute as architectural NOPs on pre-v8.3/v8.5 hardware.
   - `sme` (`FEAT_SME` on Armv9-A / `apple-m4`): Introduces Streaming SVE mode (`PSTATE.SM`) and
     the `ZA` matrix array storage (`PSTATE.ZA`); entering or leaving streaming mode (`smstart` /
     `smstop`) zeros `v0..v31`/`z0..z31`, requiring AAPCS64 SME state-preservation wrappers at
     call boundaries between normal and streaming functions.

## Boundaries

- **Unlisted LLVM internal tuning features:** LLVM defines microarchitectural tuning flags
  (such as `fast-15bytenop`, `macrofusion`, `slow-3ops-lea`) in `X86.td` and `AArch64Features.td`
  that are not exposed in `X86_FEATURES` or `AARCH64_FEATURES`; those affect instruction
  scheduling only and never affect `cfg(target_feature)`, `#[target_feature]`, or calling-convention
  ABIs.
- **Live execution of `std_detect` on macOS and Windows hosts:** Verified from `library/std_detect`
  source in `rust-lang/rust` `1.99.1`; host execution was performed on Linux `x86_64`.

## Evidence

- **Primary upstream sources (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `compiler/rustc_target/src/target_features.rs:1-1472` — `Stability`, `AARCH64_FEATURES` (`94`),
    `X86_FEATURES` (`80`), `ARM_FEATURES` (`36`), `RISCV_FEATURES` (`105`), `WASM_FEATURES` (`14`),
    `X86_FEATURES_FOR_CORRECT_FIXED_LENGTH_VECTOR_ABI`, `AARCH64_FEATURES_FOR_CORRECT_FIXED_LENGTH_VECTOR_ABI`,
    `implied_target_features`, and `abi_required_features`.
  - `compiler/rustc_codegen_llvm/src/llvm_util.rs:178-385,479-600` — `to_llvm_features`,
    `target_config`, `print_target_cpus`, and `print_target_features`.
  - `compiler/rustc_codegen_ssa/src/target_features.rs:1-584` — `from_target_feature_attr`
    (`#[inline(always)]` prohibition) and `internal_target_features`.
  - `library/std_detect/src/detect/cache.rs:1-203`, `os/x86.rs:1-335`,
    `os/linux/aarch64.rs:1-409`, `os/linux/auxvec.rs:1-221`, `os/darwin/aarch64.rs:1-168`,
    `os/windows/aarch64.rs:1-173`.
- **Primary upstream sources (`rust-lang/llvm-project` @ `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):**
  - `llvm/lib/Target/X86/X86.td`, `llvm/include/llvm/TargetParser/X86TargetParser.def`, and
    `llvm/lib/Target/X86/X86TargetTransformInfo.cpp`.
  - `llvm/lib/Target/AArch64/AArch64Features.td`, `AArch64Processors.td`, and
    `AArch64TargetTransformInfo.cpp`.
  - `llvm/lib/TargetParser/Host.cpp` — `getHostCPUName` and `getHostCPUFeatures` (`-Ctarget-cpu=native`).
- **Preserved support artifacts:**
  - `support/target_feature_database.json` — complete machine-readable feature tables (`x86`,
    `aarch64`, `arm`, `riscv`, `wasm`), stability classification, `implies` edges, `llvm_mapping`,
    vector ABI gates, `abi_required_features`, and the 136 x86 / 84 AArch64 CPU names.
  - `support/cpu_cfg_goldens.json` — exact stable and unstable (`RUSTC_BOOTSTRAP=1`)
    `--print cfg` outputs and ABI warnings across 38 target-CPU combinations on `x86_64`, `i686`,
    and `aarch64` (`Linux`, `macOS`, `Windows`).

## Revalidation

To revalidate the feature database and `--print cfg` goldens against a newer `rustc` revision:

```bash
for cpu in generic x86-64 x86-64-v2 x86-64-v3 x86-64-v4 haswell skylake icelake-server sapphirerapids znver4; do
  rustc +1.99.1 --target x86_64-unknown-linux-gnu -Ctarget-cpu="$cpu" --print cfg
done
for cpu in generic cortex-a53 cortex-a76 neoverse-n1 neoverse-v1 neoverse-v2 apple-m1 apple-m4; do
  rustc +1.99.1 --target aarch64-unknown-linux-gnu -Ctarget-cpu="$cpu" --print cfg
done
```

Compare the emitted `target_feature="..."` sets against `support/cpu_cfg_goldens.json` and diff
`compiler/rustc_target/src/target_features.rs` against `support/target_feature_database.json`.
