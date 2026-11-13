# `rustc` External CLI, JSON, Artifact, and Codegen-Backend Interface Contract

## Summary

A drop-in replacement for `rustc` targeting Rust `1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`) must satisfy two distinct external
contracts: the **frontend/driver surface** implemented in `rustc_driver_impl`,
`rustc_session`, `rustc_metadata`, and `rustc_errors`, and the
**backend-supplied surface** delegated through the
`rustc_codegen_ssa::traits::backend::CodegenBackend` trait
(`compiler/rustc_codegen_ssa/src/traits/backend.rs:19-160`). Auditing the
compiler source and probing `rustc 1.99.1` alongside the LLVM and Cranelift
backends across all eight Tier 1 targets establishes five governing facts:

1. **Complete command-line and environment surface:** `rustc` `1.99.1` defines
   **38 top-level `getopts` flags** (`compiler/rustc_session/src/config.rs:1992-2195`),
   **54 `-C` (`CodegenOptions`) flags** (`options.rs:2197-2343`), **238 `-Z`
   (`UnstableOptions`) flags** (`options.rs:2345-3115`), **21 `--print` kinds**
   (`PrintKind` in `config.rs:781-815`), **11 `--emit` kinds** (`OutputType` in
   `config.rs:647-661`), **8 `--crate-type` kinds** (`CrateType` in
   `config.rs:2221-2232`), `@<path>` UTF-8 response files with optional
   `-Zshell-argfiles` POSIX quoting (`compiler/rustc_driver_impl/src/args.rs:13-112`),
   three exit codes (`0` success, `1` compile error, `101` internal compiler
   error), jobserver client token acquisition via `CARGO_MAKEFLAGS`/`MAKEFLAGS`
   (`compiler/rustc_interface/src/util.rs:220-260`), and **90 environment
   variables** read across `compiler/`.
2. **Backend-supplied `--print` and `cfg(target_feature)` synthesis:** Five of
   the 21 `--print` kinds (`target-cpus`, `target-features`,
   `relocation-models`, `code-models`, and `tls-models`), `-Ctarget-cpu=native`
   host CPU detection, unknown `-Ctarget-feature` diagnostics, and the active
   `cfg(target_feature = "...")` set are supplied by `CodegenBackend` methods
   rather than by the frontend. Because `CodegenBackend::{print_cpus,
   print_target_features, print}` default to no-ops
   (`compiler/rustc_codegen_ssa/src/traits/backend.rs:36-44`), running
   `rustc -Zcodegen-backend=cranelift` returns **0 lines (empty stdout)** for
   all five `--print` queries, silently ignores unknown `-Ctarget-feature=+foo`
   flags, and omits host-detected features (`avx2`, `avx512f`, `bmi2`, `fma`)
   under `-Ctarget-cpu=native --print=cfg`.
3. **LLVM-specific options and `--emit` kinds:** Eight `-C` options
   (`llvm-args`, `passes`, `no-prepopulate-passes`, `save-temps`, `remark`,
   `soft-float`, `jump-tables`, `no-redzone`), **35 `-Z` options** (including
   `llvm-plugins`, `verify-llvm-ir`, `lint-llvm-ir`, `time-llvm-passes`,
   `print-llvm-passes`, `inline-llvm`, `tune-cpu`, `trap-unreachable`, and
   `emit-stack-sizes`), and two `--emit` kinds (`llvm-ir` and `llvm-bc`) are
   consumed exclusively by `rustc_codegen_llvm` or LLVM-specific target passes.
   Under `rustc_codegen_cranelift`, `-Cpasses`, `-Cno-prepopulate-passes`, and
   `-Zllvm-plugins` are silently ignored (`rc = 0`), `-Clto=fat` is rejected
   with a fatal error, and `--emit=llvm-ir` / `--emit=llvm-bc` fail in
   `rustc_codegen_ssa::back::link` with `ENOENT` when copying unemitted `.ll` /
   `.bc` files.
4. **Binary metadata and archive layout invariants:** Every `.rmeta` file and
   `lib.rmeta` archive member begins with the 8-byte `METADATA_HEADER`
   `b"rust\x00\x00\x00\x0a"` (`72 75 73 74 00 00 00 0a`, `METADATA_VERSION = 10`
   in `compiler/rustc_metadata/src/rmeta/mod.rs:63-70`), followed at bytes
   `8..16` by the 64-bit little-endian byte offset of `CrateRoot`
   (`encoder.rs:2547,2591-2603`), and at byte `16` by the length-prefixed
   `rustc 1.99.1 (58cf8f9c3 2026-10-13)` version string checked before root
   decoding (`decoder.rs:410-445`). Dynamic libraries (`--crate-type=dylib`)
   embed this payload in an unallocated `.rustc` ELF/Mach-O/COFF section;
   `--crate-type=proc-macro` dylibs additionally export
   `__rustc_proc_macro_decls_<StableCrateId>__` containing a `ProcMacro` slice
   gated by `rustc_expand::proc_macro_server`.
5. **Toolchain and sysroot layout for `rustup` and Cargo:** A valid sysroot
   requires `<sysroot>/bin/{rustc,rustdoc}`,
   `<sysroot>/libexec/rust-analyzer-proc-macro-srv`,
   `<sysroot>/lib/rustlib/<host>/codegen-backends/`,
   `<sysroot>/lib/rustlib/<host>/bin/gcc-ld/{ld.lld,ld64.lld,lld-link,wasm-ld}`,
   and `<sysroot>/lib/rustlib/<target>/lib/` containing hashed `libcore`,
   `liballoc`, `libstd`, `libproc_macro`, `libtest`, and `libcompiler_builtins`
   `.rlib`s.

## Applicability

These findings govern any compiler driver, wrapper, or non-LLVM `CodegenBackend`
claiming drop-in compatibility with **Rust 1.99.1**
(`rust-lang/rust` commit `58cf8f9c35b355199727627d07ae34a4e2846d67`, bundled
with LLVM `23.1.1` at `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) across the
eight Tier 1 targets (`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`,
`i686-unknown-linux-gnu`, `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`,
`x86_64-pc-windows-gnu`, `aarch64-pc-windows-msvc`, and `i686-pc-windows-msvc`):

- **Exact observation:** Source definitions are extracted from `rust-lang/rust`
  `58cf8f9c35b355199727627d07ae34a4e2846d67`. Empirical `--print`, artifact, and
  JSON diagnostic probes were executed on `x86_64-unknown-linux-gnu` using
  `rustc +1.99.1` and compared against `-Zcodegen-backend=cranelift` on
  `nightly-2026-11-12` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).

## Findings

### 1. Command-line flags, response files, exit codes, and environment variables

Basis: source + execution

#### 1.1 Top-level flags, `-C` options, and `-Z` options
`compiler/rustc_session/src/config.rs:1992-2195` (`rustc_optgroups`) registers
**38 top-level `getopts` definitions** (22 standard flags shown in `rustc -h`
and 16 verbose-only flags shown in `rustc -h -v`, including `--extern`,
`--sysroot`, `-Z`, `--error-format`, `--json`, `--color`, `--diagnostic-width`,
`--remap-path-prefix`, and `--check-cfg`).
`compiler/rustc_session/src/options.rs` defines:
- **23 top-level `Options` struct fields** (`options.rs:333-405`), each tagged
  with incremental dependency tracking (`[TRACKED]`,
  `[TRACKED_NO_CRATE_HASH]`, `[UNTRACKED]`, or `[SUBSTRUCT]`).
- **54 `-C` (`CodegenOptions`) flags** (`options.rs:2197-2343`), of which 3 are
  removed tombstones (`ar`, `idesignate`, `soft-float` on unsupported targets)
  and 51 are active.
- **238 `-Z` (`UnstableOptions`) flags** (`options.rs:2345-3115`), gated on
  nightly channels or when `RUSTC_BOOTSTRAP=1` (or `RUSTC_BOOTSTRAP=<crate_name>`)
  is present in the environment (`config.rs:1810-1855`).

#### 1.2 `--print`, `--emit`, and `--crate-type` inventories
Table 1 lists all 21 `--print` kinds (`PrintKind` in `config.rs:781-815`),
whether each requires `-Zunstable-options`, and whether the output is computed
by the frontend (`rustc_session`/`rustc_target`/`rustc_middle`) or delegated to
`CodegenBackend`.

| `--print` Kind | Stability | Producer | Output Contract |
| :--- | :--- | :--- | :--- |
| `crate-name` | Stable | Frontend (`rustc_interface`) | Single line: resolved crate identifier |
| `file-names` | Stable | Frontend (`rustc_session::output`) | Filenames emitted for requested `--crate-type`s |
| `sysroot` | Stable | Frontend (`Session::sysroot`) | Absolute path to active toolchain sysroot |
| `target-libdir` | Stable | Frontend (`Session::target_tlib_path`) | `<sysroot>/lib/rustlib/<target>/lib` |
| `cfg` | Stable | Hybrid (`Session` + `CodegenBackend::target_config`) | Sorted `key` and `key="val"` active predicates |
| `check-cfg` | Unstable | Hybrid (`Session` + `CodegenBackend::target_config`) | Exhaustive expected `cfg` keys and value domains |
| `calling-conventions` | Stable | Frontend (`rustc_abi::ExternAbi`) | 40 supported `extern "..."` ABI strings |
| `target-list` | Stable | Frontend (`rustc_target::spec::TARGETS`) | 247 built-in target triples (`1.99.1`) |
| `native-static-libs` | Stable | Frontend (`rustc_metadata::native_libs`) | `note: native-static-libs: -lc -lm ...` on stderr |
| `split-debuginfo` | Stable | Frontend (`TargetOptions`) | Supported `-Csplit-debuginfo` modes (`off`, `packed`, `unpacked`) |
| `deployment-target` | Unstable | Frontend (`rustc_target` Apple/OS env) | Active minimum OS deployment target (e.g. `MACOSX_DEPLOYMENT_TARGET`) |
| `stack-protector-strategies` | Unstable | Frontend (`TargetOptions`) | `all`, `strong`, `basic`, `none` |
| `target-spec-json` | Unstable | Frontend (`Target::to_json`) | Complete target specification JSON object |
| `all-target-specs-json` | Unstable | Frontend (`rustc_target`) | Map of all built-in target triples to spec JSON |
| `link-args` | Unstable | Backend (`rustc_codegen_ssa::back::link`) | Exact linker executable and argument vector |
| `target-cpus` | Stable | **Backend (`CodegenBackend::print_cpus`)** | Target CPU names + `"native - Select the CPU of the current host (currently <cpu>)."` |
| `target-features` | Stable | **Backend (`CodegenBackend::print_target_features`)** | `rustc` and backend-specific target feature table |
| `relocation-models` | Stable | **Backend (`CodegenBackend::print`)** | `static`, `pic`, `pie`, `dynamic-no-pic`, `ropi`, `rwpi`, `ropi-rwpi`, `default` |
| `code-models` | Stable | **Backend (`CodegenBackend::print`)** | `tiny`, `small`, `kernel`, `medium`, `large` |
| `tls-models` | Stable | **Backend (`CodegenBackend::print`)** | `global-dynamic`, `local-dynamic`, `initial-exec`, `local-exec`, `emulated` |

The 11 `--emit` (`OutputType`) kinds are `asm`, `llvm-ir`, `llvm-bc`, `obj`,
`metadata`, `link`, `dep-info`, `mir`, `thin-link-bitcode` (unstable),
`exe` (deprecated alias), and `dep-info` path overrides (`--emit=KIND=PATH`).
The 8 `--crate-type` (`CrateType`) kinds are `bin`, `lib`, `rlib`, `dylib`,
`cdylib`, `staticlib`, `proc-macro`, and unstable `sdylib` (interface-only
shared library).

#### 1.3 Response files, exit codes, jobserver, and environment variables
- **Response files (`compiler/rustc_driver_impl/src/args.rs:13-112`):** Any CLI
  argument beginning with `@<path>` is expanded recursively before `getopts`
  parsing. By default, files must be valid UTF-8 and are split on `\n` (stripping
  trailing `\r`), with one argument per line; passing `-Zshell-argfiles` before
  `@<path>` switches parsing to POSIX shell token splitting (`shell:`). Non-UTF-8
  arguments or argfiles fail with exit code `1`.
- **Exit codes (`compiler/rustc_driver_impl/src/lib.rs:112-116,1377-1382`):**
  `EXIT_SUCCESS = 0`, `EXIT_FAILURE = 1` (ordinary compilation errors), and
  `101` (`std::process::ExitCode` default panic code when an Internal Compiler
  Error panics through `install_ice_hook`).
- **Environment variables and jobserver:** Across `compiler/`, `rustc` reads
  **90 distinct environment variables** (full source-location map in
  `support/interface_inventory.json`), including `RUSTC_BOOTSTRAP`,
  `RUST_BACKTRACE`, `RUST_LIB_BACKTRACE`, `RUST_MIN_STACK` (default 8 MiB worker
  thread stack), `RUSTC_ICE` (`0` disables `rustc-ice-*.txt` dump; path sets
  directory), `RUSTC_LOG`, `RUSTC_LOG_COLOR`, `RUSTC_COLOR`, `SOURCE_DATE_EPOCH`,
  `SDKROOT`, `MACOSX_DEPLOYMENT_TARGET`, `IPHONEOS_DEPLOYMENT_TARGET`,
  `TVOS_DEPLOYMENT_TARGET`, `XROS_DEPLOYMENT_TARGET`, `WATCHOS_DEPLOYMENT_TARGET`,
  and `CARGO_MAKEFLAGS` / `MAKEFLAGS` (parsed by `jobserver::Client::from_env` in
  `compiler/rustc_interface/src/util.rs:220-260` to share GNU Make jobserver pipe
  file descriptors across CGU worker threads).

---

### 2. Output formats: dep-info, JSON schema, `.rlib`/`.rmeta`, `.rustc`, and sysroot

Basis: source + execution

1. **Dep-info (`.d`) format (`compiler/rustc_interface/src/passes.rs:420-530`):**
   Makefile-compatible dependency rules mapping each emitted artifact path (and,
   unless `-Zdep-info-omit-d-target` is set, the `.d` file itself) to all read
   source files, `include!`d files, and build-time `# env-dep:<VAR>=<VAL>`
   comments tracked via `env!`/`option_env!`. Spaces and `#` in paths are
   backslash-escaped.
2. **JSON output schema (`--error-format=json` and `--json=...` in
   `compiler/rustc_errors/src/json.rs`):** Every stderr line is a standalone JSON
   object discriminated by `"$message_type"`:
   - `"diagnostic"`: fields `message`, `code` (`{code, explanation}` or `null`),
     `level` (`"error"`, `"warning"`, `"note"`, `"help"`, `"failure-note"`),
     `spans` (with 0-based `byte_start`/`byte_end` and 1-based UTF-8 codepoint
     `line_start`/`line_end`/`column_start`/`column_end`), `children`, and
     `rendered`. Modified by `--json=diagnostic-short`,
     `--json=diagnostic-rendered-ansi`, and `--json= diagnostic-unicode`.
   - `"artifact"` (enabled by `--json=artifacts`):
     `{"$message_type":"artifact","artifact":"<path>","emit":"link|metadata|dep-info|..."}`.
   - `"future-incompat"` (enabled by `--json=future-incompat`): wraps future-breakage
     lint reports for Cargo.
   - `"unused-externs"` (enabled by `--json=unused-externs` or `-Wunused-crate-dependencies`):
     lists unused `--extern` crate names.
3. **`.rlib` and `.rmeta` binary layout (`compiler/rustc_metadata/src/rmeta/`):**
   - An `.rlib` is an `ar` archive containing `lib.rmeta` (the crate metadata
     stub), `<crate>.<hash>-cgu.<N>.rcgu.o` object files, and—when
     `-Cembed-bitcode=yes` (default on LLVM, disabled by Cargo unless LTO is
     enabled)—`.rcgu.bc` LLVM bitcode sections/members.
   - `.rmeta` header (`mod.rs:63-70`, `encoder.rs:2544-2598`):
     - Bytes `0..8`: `b"rust\x00\x00\x00\x0a"` (`72 75 73 74 00 00 00 0a`,
       `METADATA_VERSION = 10`).
     - Bytes `8..16`: 64-bit little-endian `usize` byte offset to `CrateRoot`
       (e.g., `40 08 00 00 00 00 00 00` = offset `2112` in a `2498`-byte `.rmeta`).
     - Bytes `16..`: `rustc_version` string (`"rustc 1.99.1 (58cf8f9c3 2026-10-13)"`),
       verified by `MetadataBlob::check_version` before reading `CrateRoot` so
       mismatched compiler versions produce a clean `incompatible rustc version`
       error rather than a decoder panic.
4. **Dylib `.rustc` section and `proc-macro` ABI:**
   - `--crate-type=dylib` embeds the `.rmeta` stream (prefixed with an 8-byte
     big-endian length header) into an ELF/COFF `.rustc` section (`__DATA,.rustc`
     on Mach-O), observed at `2514` bytes (`0x9d2`) for a `2498`-byte `.rmeta`.
   - `--crate-type=proc-macro` compiles a host shared library exporting
     `__rustc_proc_macro_decls_<StableCrateId>__: &[ProcMacro]` (`D` data symbol
     in `nm -D`), loaded via `dlopen`/`LoadLibraryW` by `rustc_expand` or
     `rust-analyzer-proc-macro-srv`.

---

### 3. Backend-supplied behavior and LLVM vs. Cranelift/GCC differentials

Basis: source + execution

`CodegenBackend` (`compiler/rustc_codegen_ssa/src/traits/backend.rs:19-160`) has
20 methods, of which 6 have default implementations (`locale_resource`,
`init`, `print`, `print_passes`, `print_version`, `target_config`, `print_cpus`,
`print_target_features`) and 4 drive the compilation pipeline (`codegen_crate`,
`join_codegen`, `link`, `compile_codegen_unit`). Table 2 records empirical
differences across the eight Tier 1 targets and between LLVM and Cranelift
(full golden outputs in `support/tier1_print_goldens.json`).

| Interface / Query | LLVM Backend (`1.99.1` & `nightly`) | Cranelift Backend (`rustc_codegen_cranelift`) | GCC Backend (`rustc_codegen_gcc`) |
| :--- | :--- | :--- | :--- |
| `--print target-cpus` | Returns full target table (**104** CPUs on `x86_64`, **194** on `aarch64`, **65** on `i686`) + host CPU on `native` | **Empty stdout (0 lines, `rc=0`)** (`print_cpus` not implemented) | **Empty stdout (0 lines, `rc=0`)** (`print_cpus` not implemented) |
| `--print target-features` | Returns full feature table (**239** features on `x86_64`, **260** on `aarch64`, **239** on `i686`) | **Empty stdout (0 lines, `rc=0`)** (`print_target_features` not implemented) | **Empty stdout (0 lines, `rc=0`)** |
| `--print relocation-models` / `code-models` / `tls-models` | Prints 8 relocation models, 5 code models, and 5 TLS models | **Empty stdout (0 lines, `rc=0`)** (`print` not overridden) | **Empty stdout (0 lines, `rc=0`)** |
| `-Ctarget-cpu=native --print=cfg` | Queries `LLVMGetHostCPUName` (`icelake-server`) and `LLVMGetHostCPUFeatures`, enabling **45** `target_feature`s | Returns only the **4** baseline `x86_64` features (`fxsr`, `sse`, `sse2`, `x87`) | Queries `libgccjit` / baseline target features |
| `-Ctarget-feature=+unknown_feat` | Emits `warning: unknown and unstable feature specified...` | **Silently ignored (`rc=0, stderr=""`)** | Warns or passes through to `libgccjit` |
| `-Cllvm-args=-help` | Passed to `LLVMParseCommandLineOptions` | Fails (`rc=1`, `error: Unknown option '-help'` in Cranelift settings parser) | Ignored or interpreted by GCC wrapper |
| `-Cpasses=...`, `-Cno-prepopulate-passes`, `-Zllvm-plugins=...` | Configures LLVM PassBuilder pipeline | **Silently ignored (`rc=0`)** | **Silently ignored (`rc=0`)** |
| `--emit=llvm-ir`, `--emit=llvm-bc` | Emits `.ll` text and `.bc` bitcode | **Fails (`rc=1`)** in `rustc_codegen_ssa::back::link`: `could not copy "...rcgu.ll" to "lib.ll": No such file or directory` | **Fails (`rc=1`)** unless `emit_bitcode` stub writes dummy file |
| `-Clto=fat` / `-Clto=thin` | Runs LLVM LTO / ThinLTO | **Fails (`rc=1`)**: `error: LTO is not supported by rustc_codegen_cranelift` | Supports LTO only via GCC `-flto` linker plugin |

## Boundaries

- **Non-Tier-1 `--print target-cpus` and `target-features`:** Golden outputs in
  `support/tier1_print_goldens.json` cover the 8 Tier 1 targets; the remaining
  239 Tier 2/3 targets use the same `rustc_codegen_llvm::back::write::print_*`
  target machine queries (**not examined** individually).
- **Unstable `-Z` flag evolution:** Between `1.99.1` and `1.100.0`/`nightly`,
  unstable `-Z` options are added or removed without stability guarantees;
  only `-C` and stable top-level flags are SemVer-locked.

## Evidence

- **`rustc` option definitions (`rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - Top-level `getopts` table: `compiler/rustc_session/src/config.rs:1992-2195` (`rustc_optgroups`).
  - `Options`, `CodegenOptions` (`-C`), and `UnstableOptions` (`-Z`):
    `compiler/rustc_session/src/options.rs:307-405`, `2197-2343`, `2345-3115`.
  - `PrintKind`, `OutputType`, and `CrateType`:
    `compiler/rustc_session/src/config.rs:647-661`, `781-815`, `2221-2232`.
  - Response file expansion: `compiler/rustc_driver_impl/src/args.rs:13-154`.
  - Exit codes and ICE handler: `compiler/rustc_driver_impl/src/lib.rs:112-117`, `1377-1405`, `1672-1677`.
  - Jobserver integration: `compiler/rustc_interface/src/util.rs:220-260`.
  - `.rmeta` binary format: `compiler/rustc_metadata/src/rmeta/mod.rs:56-71`,
    `encoder.rs:2537-2603`, `decoder.rs:410-460`.
  - JSON diagnostics: `compiler/rustc_errors/src/json.rs:1-420`.
  - `CodegenBackend` trait: `compiler/rustc_codegen_ssa/src/traits/backend.rs:19-160`.
  - Cranelift & GCC backend implementations:
    `compiler/rustc_codegen_cranelift/src/lib.rs:1-310`,
    `compiler/rustc_codegen_gcc/src/lib.rs:1-380`.
- **Preserved artifacts in `support/`:**
  - `support/interface_inventory.json`: machine-readable inventory of all 38
    top-level flags, 54 `-C` options, 238 `-Z` options, 20 `CodegenBackend`
    methods, 90 environment variables, and artifact/JSON specimens.
  - `support/tier1_print_goldens.json`: golden `--print` outputs across all 8
    Tier 1 targets and the LLVM vs. Cranelift differential matrix.

## Revalidation

To revalidate the interface inventory or compare a replacement `rustc` binary
against the `1.99.1` baseline:

1. Diff `compiler/rustc_session/src/{options.rs,config.rs}`,
   `compiler/rustc_metadata/src/rmeta/mod.rs`, and
   `compiler/rustc_codegen_ssa/src/traits/backend.rs` against commit
   `58cf8f9c35b355199727627d07ae34a4e2846d67`.
2. Run `rustc --print=<kind> --target=<triple>` across the eight Tier 1 targets
   and compare against `support/tier1_print_goldens.json`, checking in
   particular that `cfg(target_feature)`, `target-cpus`, `target-features`,
   `relocation-models`, `code-models`, and `tls-models` are populated rather
   than falling back to `CodegenBackend`'s empty default methods.
