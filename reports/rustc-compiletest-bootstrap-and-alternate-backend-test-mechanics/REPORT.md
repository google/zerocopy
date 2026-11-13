# Rustc `compiletest`, `bootstrap`, and Alternate Codegen Backend Test Mechanics

## Summary

Driving `rustc`'s compiler and standard-library test suites against an external drop-in compiler binary or an alternate codegen backend in `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) is governed by two orchestration layers: the `bootstrap` (`./x.py test`) build graph in `src/bootstrap/src/core/build_steps/test.rs` and the standalone `compiletest` harness in `src/tools/compiletest/`.

1. **Direct Standalone `compiletest` Invocation vs. Stage-0 `bootstrap`**:
   - Via `bootstrap`, testing a prebuilt external compiler without rebuilding stage 1 requires `--stage 0 --set build.compiletest-allow-stage0=true` (`src/bootstrap/src/core/build_steps/test.rs:2229-2236`), plus either `build.rustc = "/path/to/compiler"` in `bootstrap.toml` (`local-rebuild = true`), `--test-codegen-backend <name>` (which passes `--override-codegen-backend <name>` and `--default-codegen-backend <name>` to `compiletest`, `test.rs:2434-2470`), or `--compiletest-rustc-args "<flags>"`.
   - Invoking the `compiletest` binary directly (`src/tools/compiletest/src/cli.rs:36-108`) requires **24 mandatory CLI flags** (`--compile-lib-path`, `--run-lib-path`, `--rustc-path`, `--python`, `--src-root`, `--src-test-suite-root`, `--build-root`, `--build-test-suite-root`, `--sysroot-base`, `--stage`, `--stage-id`, `--mode`, `--suite`, `--cc`, `--cxx`, `--cflags`, `--cxxflags`, `--llvm-components`, `--channel`, `--nightly-branch`, `--git-merge-commit-email`, `--minicore-path`, `--jobs`, `--host`, `--target`) plus four non-obvious environment/flag invariants:
     1. **Default Edition Is Rust 2015**: Do not pass `--edition 2021` globally; tests without `//@ edition:` assume Rust 2015 (4 tests in `tests/codegen-units/` fail on bare trait objects `&Trait` if `--edition 2021` is passed).
     2. **Native C Test Helpers (`librust_test_helpers.a`)**: For `ui` and `incremental` suites, `tests/auxiliary/rust_test_helpers.c` must be compiled into `librust_test_helpers.a` for both host and target and supplied via `--host-rustcflags -Lnative=<dir>` and `--target-rustcflags -Lnative=<dir>` (`test.rs:2568-2590`, `4195-4268`).
     3. **Deterministic Symbol-Hash Version (`RUSTC_FORCE_RUSTC_VERSION=compiletest`)**: `bootstrap` exports `RUSTC_FORCE_RUSTC_VERSION=compiletest` and `RUSTC_BOOTSTRAP=1` (`test.rs:2862-2865`) so `.stderr` and `.mir` output normalization matches committed expectations.
     4. **Each `--target-rustcflags` Entry Is a Single `rustc` Argument**: Passing space-separated flags in one `--target-rustcflags "-Cpanic=abort -Zpanic-abort-tests"` invocation passes the entire string as a single `argv` element to `rustc` (`common.rs:1219`), causing `error: incorrect value 'abort -Zpanic-abort-tests' for codegen option 'panic'`. Repeat `--target-rustcflags` once per token.
2. **All 18 `TestMode` Variants and 21 `TestSuite` Directories**:
   - `src/tools/compiletest/src/common.rs:95-190` defines 18 execution modes (`ui`, `pretty`, `codegen`, `codegen-units`, `mir-opt`, `assembly`, `incremental`, `debuginfo`, `crashes`, `run-make`, `js-doc-test`, `rustdoc-html`, `rustdoc-json`, `rustdoc-gui`, `coverage-map`, `coverage-run`, `coverage-run-rustdoc`) mapped across 21 test directories under `tests/`.
   - Directives (`//@ ...`) are validated against `KNOWN_DIRECTIVE_NAMES_SET` (308 directive names in `src/tools/compiletest/src/directives/directive_names.rs:6-354`) and dispatched by `DIRECTIVE_HANDLERS_MAP` (`src/tools/compiletest/src/directives/handlers.rs:14-375`). Unknown `//@` directives trigger a hard test failure.
3. **How `rustc_codegen_cranelift` and `rustc_codegen_gcc` Run and Exclude `rustc` Tests**:
   - **Cranelift (`compiler/rustc_codegen_cranelift/scripts/test_rustc_tests.sh:1-208`)**: Runs 5 `compiletest` suites (`codegen-units`, `run-make`, `run-make-cargo`, `ui`, `incremental`) at `--stage 0`, plus `library/{core,alloc,std}` tests via `./y.sh test` (`compiler/rustc_codegen_cranelift/build_system/tests.rs:58-481`, applying 4 stdlib/sysroot patches). It deletes all `//@ should-fail`, `//~ ERROR`, `//@ error-pattern:`, `//@ build-fail`, `//@ run-fail`, `-Cllvm-args`, and `lto` tests via `rg`, plus **121 explicit `rm` commands** across 11 documented categories, and patches `src/tools/compiletest/src/runtest/run_make.rs:109` to remove `.env("RUSTC_BOOTSTRAP", "-1")` so `rmake.rs` recipes can run with `-Zcodegen-backend`. Additionally, `rustc_codegen_cranelift/Cargo.toml:55` leaves `feature = "unwinding"` disabled by default, which forces `UnwindAction::Unreachable` in `src/abi/mod.rs:851-853` and lowers `sym::catch_unwind` in `src/intrinsics/mod.rs:1397-1407` without landing pads.
   - **GCC (`compiler/rustc_codegen_gcc/build_system/src/test.rs:882-1344`)**: Runs `ui`, `run-make`, and `run-make-cargo` via `./x.py test --run always --stage 0 --set build.compiletest-allow-stage0=true tests/<suite> --compiletest-rustc-args "-Zcodegen-backend=... --sysroot ..." --bypass-ignore-backends`, splitting `tests/ui` into passing tests (excluding 4 entire subdirectories `abi`, `extern`, `proc-macro`, `threads-sendsync`, non-thin LTO tests, and **113 files** in `tests/failing-ui-tests.txt` plus **47 files** in `tests/failing-ui-tests12.txt` for `libgccjit` 12) and error-pattern tests (excluding **40 files** in `tests/failing-ice-tests.txt`), plus **14 `run-make` exclusions** (`tests/failing-run-make-tests.txt`) and **6 LTO exclusions** (`tests/failing-lto-tests.txt`).

## Applicability

- **Primary baseline**: `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, LLVM `23.1.1`).
- **Alternate backend comparison**: `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `rustc-codegen-cranelift-preview`) and in-tree `compiler/rustc_codegen_cranelift` / `compiler/rustc_codegen_gcc` at `58cf8f9c35b355199727627d07ae34a4e2846d67`.
- **Scope**: Test modes, directive semantics, `rustc` process invocation, revisions, target/LLVM/backend conditions, remote testing (`remote-test-client` / `remote-test-server`), `run-make` (`rmake.rs` + `run_make_support`), standard-library test suites, and alternate backend exclusion rationales.

## Findings

### 1. Test Modes, Suites, and What Each Mode Executes

Basis: source (`src/tools/compiletest/src/common.rs:95-248`, `src/tools/compiletest/src/runtest.rs`, `src/bootstrap/src/core/build_steps/test.rs:960-1760`) + execution (`support/compiletest_probe_results.json`)

| Suite (`tests/<suite>`) | `compiletest --mode` | Default Pass/Fail Semantics | How `compiletest` Invokes `rustc` & Validates Output |
| :--- | :--- | :--- | :--- |
| `ui`, `ui-fulldeps`, `rustdoc-ui` | `ui` | Fails if `//~` error annotations, `//@ error-pattern`, `//@ check-fail`, `//@ build-fail`, or `//@ run-fail` are present; otherwise defaults to `build-pass` (`check-pass` or `run-pass` when directed or overridden by `--pass`) | Invokes `rustc --error-format=json` (`runtest/ui.rs`); compares structured diagnostic spans against `//~` annotations and normalized stderr/stdout against `.stderr`/`.stdout`; if `run-pass`/`run-fail`/`run-crash`, links and executes the binary. |
| `codegen-llvm` | `codegen` | Compiles with `--emit=llvm-ir -Cno-prepopulate-passes` | Runs LLVM `FileCheck` (`--llvm-filecheck`) over the emitted `.ll` file (`runtest/codegen.rs:1-21`). |
| `assembly-llvm` | `assembly` | Compiles with `--emit=asm` (or `--emit=obj` when `//@ assembly-output: ptx-linker`) | Runs LLVM `FileCheck` over the emitted `.s` file (`runtest/assembly.rs:1-51`). Verified 422/422 passing in 1.45s on `1.99.1`. |
| `mir-opt` | `mir-opt` | Compiles with `-Zdump-mir=<pass> -Zmir-include-spans=false` | Compares dumped `.mir` files or unified `.diff` before/after pass files (`runtest/mir_opt.rs:1-133`). Requires `std` built with `is_for_mir_opt_tests(true)` (`-Zalways-encode-mir`) for cross-crate inlining tests. |
| `codegen-units` | `codegen-units` | Compiles with `-Zprint-mono-items=<mode>` | Compares `MONO_ITEM` / `CGU` partitioning output lines against `//~ MONO_ITEM` annotations (`runtest/codegen_units.rs:1-195`). Verified 46/46 passing in 0.20s on `1.99.1`. |
| `incremental` | `incremental` | Multi-revision compilation with `-C incremental=<dir>` | Compiles each revision in sequence (`rpass*`, `cfail*`, `bfail*`, `rfail*`) sharing an incremental cache directory and checks `#[rustc_clean]` / `#[rustc_dirty]` queries (`runtest/incremental.rs:1-111`). |
| `debuginfo` | `debuginfo` | Compiles with `-g` (`-C debuginfo=2`) and runs `gdb`, `lldb`, or `cdb` | Feeds `//@ gdb-command:` / `lldb-command:` / `cdb-command:` scripts to the debugger and matches output against `//@ gdb-check:` / `lldb-check:` / `cdb-check:` (`runtest/debuginfo.rs:1-540`). |
| `coverage`, `coverage-run-rustdoc` | `coverage-map`, `coverage-run`, `coverage-run-rustdoc` | Compiles with `-C instrument-coverage` | `coverage-map` runs `coverage-dump` on `.ll` covmap metadata; `coverage-run` executes the binary, runs `llvm-profdata merge` and `llvm-cov show`, and diffs `.coverage` (`runtest/coverage.rs:1-384`). |
| `run-make`, `run-make-cargo`, `build-std` | `run-make` | Compiles `rmake.rs` with `--stage0-rustc-path` and `RUSTC_BOOTSTRAP=-1` against `librun_make_support.rlib`, then executes the compiled recipe binary | The recipe binary invokes the under-test `rustc` (`RUSTC` env var), `rustdoc`, `cargo` (for `run-make-cargo`/`build-std`), C/C++ compilers, and LLVM binutils (`runtest/run_make.rs:1-360`). |
| `crashes` | `crashes` | Expects `rustc` to exit with a non-zero ICE (`exit status 101`) | Fails the test if `rustc` succeeds or exits cleanly without crashing, so fixed ICEs are immediately flagged for promotion to `tests/ui/` (`runtest/crashes.rs:1-25`). |
| `pretty` | `pretty` | Runs `rustc -Zunpretty=<mode>` | Verifies idempotence and type-checking of pretty-printed AST/HIR/expanded output (`runtest/pretty.rs:1-87`). |
| `rustdoc-html`, `rustdoc-json`, `rustdoc-js`, `rustdoc-js-std`, `rustdoc-gui` | `rustdoc-html`, `rustdoc-json`, `js-doc-test`, `rustdoc-gui` | Invokes `rustdoc` and validates generated documentation | Uses `htmldocck.py`, `jsondocck` + `jsondoclint`, `nodejs`, or `browser-ui-test` (`runtest/rustdoc*.rs`). |

### 2. Directive Grammar, Revisions, and Condition Evaluation (`only-*`, `ignore-*`, `needs-*`)

Basis: source (`src/tools/compiletest/src/directives.rs:1-1482`, `src/tools/compiletest/src/directives/line.rs:1-132`, `src/tools/compiletest/src/directives/cfg.rs:1-351`, `src/tools/compiletest/src/directives/needs.rs:1-461`)

1. **Line Syntax and Revision Scoping (`line.rs:12-132`)**:
   - Directives must begin with `//@` (with optional `//@[rev1,rev2]` revision filter immediately after `//@`). In `Makefile`s, `#@` is used; in `.goml` GUI tests, `//` is used.
   - `//@ revisions: r1 r2 ...` expands a single test file into $N$ independent `CollectedTestDesc` instances (`TestVariant { revision: Some(rev), debugger }`, `directives.rs:165-235`), passing `--cfg <rev>` to `rustc` and looking up `<stem>.<rev>.stderr` / `.stdout` / `.fixed`.
   - In `incremental` tests, revision prefixes carry semantic pass/fail meaning (`directives.rs:1060-1085`): `rpass*` (`run-pass`), `rfail*` (`run-fail`), `cfail*` (`compile-fail` / `build-fail`), and `bfail*` (`build-fail`).
2. **Target, Architecture, OS, Environment, ABI, and Backend Conditions (`directives/cfg.rs:1-351`)**:
   - Before scanning test files, `DirectivesCache::load` invokes `--query-rustc-path` (or `--rustc-path`) with `--print=all-target-specs-json -Zunstable-options` and `--print=cfg --target=<target>` (`common.rs:1160-1280`).
   - Every `only-<cond>` and `ignore-<cond>` is checked against:
     - Exact target triple (`x86_64-unknown-linux-gnu`, etc.), OS (`linux`, `windows`, `macos`, `android`, `freebsd`, ...), OS family (`unix`, `windows`, `wasm`), environment (`gnu`, `msvc`, `musl`, `sgx`, `ohos`), ABI (`eabihf`, `abi64`, `sim`), architecture (`x86_64`, `aarch64`, `x86` / `i686`, `arm`, `riscv64`, `wasm32`, ...), pointer width (`32bit`, `64bit`, `16bit`), endianness (`endian-big`), and object format (`elf`, `macho`, `coff`, `wasm`).
     - Stage (`stage1`, `stage2`), channel (`stable`, `beta`, `nightly`), cross-compilation (`cross-compile` when `host != target`), remote execution (`remote`), debuggers (`cdb`, `gdb`, `lldb`, plus `gdb-version`, `lldb-version`), and compare modes (`compare-mode-next-solver`, `compare-mode-polonius`).
     - **LLVM Version (`ignore-llvm-version` / `min-llvm-version` / `max-llvm-version` / `exact-llvm-major-version`)**: Parses `--llvm-version` (e.g. `23.1.1`) into a 3-component `semver::Version` (`directives.rs:1320-1395`). When `--system-llvm` is set, `ignore-system-llvm` triggers.
     - **Codegen Backend (`ignore-backends: <backend>...` / `only-backends: <backend>...`)**: Evaluated against `config.default_codegen_backend` (`CodegenBackend` enum in `common.rs:250-292`: `Llvm`, `Cranelift`, `Gcc`), **unless** `--bypass-ignore-backends` is passed on the `compiletest` CLI (`directives.rs:945-975`). In `rustc 1.99.1`, `ignore-backends` appears **754 times** across `tests/` (predominantly `//@ ignore-backends: gcc`).
3. **Capability Conditions (`directives/needs.rs:1-461`)**:
   - `PreparedNeedsConditions` precomputes host/target capabilities once per suite:
     - `needs-llvm-components: <comp>...` (1,437 occurrences in `1.99.1`): requires every listed component (e.g. `x86`, `aarch64`, `arm`, `riscv`, `webassembly`, `nvptx`) to be present in `--llvm-components`.
     - `needs-unwind` (209 occurrences): requires `target_cfg.panic == PanicStrategy::Unwind`.
     - `needs-subprocess` (179), `needs-threads` (105): requires non-Wasm/non-bare-metal OS target supporting processes/threads.
     - `needs-target-std` (120): requires `std` available for `--target`.
     - `needs-asm-support` (95): requires target architecture in `[x86, x86_64, arm, aarch64, riscv32, riscv64, loongarch32, loongarch64, s390x, powerpc, powerpc64]`.
     - `needs-sanitizer-support` (21) and `needs-sanitizer-{address,cfi,kcfi,leak,memory,thread,hwaddress,dataflow,safestack,shadow-call-stack}`: requires `RUSTC_SANITIZER_SUPPORT=1` and target membership in the sanitizer's supported target list.
     - `needs-enzyme` (57, `--has-enzyme`), `needs-offload` (10, `--has-offload`), `needs-profiler-runtime` (12, `--profiler-runtime`), `needs-rustc-debug-assertions` (26, `--with-rustc-debug-assertions`), `needs-std-debug-assertions` (`--with-std-debug-assertions`), `needs-deterministic-layouts` (15, negated by `--rust-randomized-layout`), `needs-dynamic-linking` (23, `target_cfg.dynamic_linking`), `needs-rust-lld` (18), `needs-dlltool` (5).

### 3. Alternate Codegen Backend Modes and Exclusion Taxonomies (`Cranelift` vs. `GCC`)

Basis: source (`compiler/rustc_codegen_cranelift/scripts/test_rustc_tests.sh:1-208`, `compiler/rustc_codegen_cranelift/scripts/setup_rust_fork.sh:1-85`, `compiler/rustc_codegen_cranelift/Cargo.toml:50-56`, `compiler/rustc_codegen_gcc/build_system/src/test.rs:882-1344`, `compiler/rustc_codegen_gcc/tests/failing-*.txt`) + execution (`support/compiletest_probe_results.json`)

1. **Three Ways to Drive `compiletest` Against an Alternate Compiler or Backend**:
   - **Mechanism A — `bootstrap` `--test-codegen-backend <name>` (`src/bootstrap/src/core/build_steps/test.rs:2434-2470`)**:
     Passes `--override-codegen-backend <name>` and `--default-codegen-backend <name>` to `compiletest`. Inside `src/tools/compiletest/src/runtest.rs:1955-1965`, `--override-codegen-backend` appends `-Zcodegen-backend=<name>` to every target `rustc` invocation while respecting `//@ ignore-backends: <name>`.
   - **Mechanism B — Wrapper Binary (`rustc-clif` / Drop-In Replacement Binary)**:
     Used by `rustc_codegen_cranelift/scripts/setup_rust_fork.sh:24-45`: sets `build.rustc = ".../dist/bin/rustc-clif"`, `build.local-rebuild = true`, `build.compiletest-allow-stage0 = true`, `rust.llvm-tools = false`, and runs `./x.py test --stage 0 tests/{codegen-units,run-make,run-make-cargo,ui,incremental}`. Because `run_make.rs:109` sets `RUSTC_BOOTSTRAP=-1` when compiling `rmake.rs` with `--stage0-rustc-path` (which rejects `-Zcodegen-backend` inside the `rustc-clif` wrapper), `test_rustc_tests.sh:188-202` patches out `.env("RUSTC_BOOTSTRAP", "-1")`. (If `--stage0-rustc-path` points to an unmodified host `rustc` while `--rustc-path` points to the custom compiler under test, `rmake.rs` compiles cleanly with `RUSTC_BOOTSTRAP=-1`.)
   - **Mechanism C — `--compiletest-rustc-args` + `--bypass-ignore-backends`**:
     Used by `rustc_codegen_gcc/build_system/src/test.rs:1089-1121`: invokes `./x.py test --run always --stage 0 --set build.compiletest-allow-stage0=true tests/<suite> --compiletest-rustc-args "-Zcodegen-backend=<so> --sysroot <sysroot> -Csymbol-mangling-version=v0" --bypass-ignore-backends`, using its own explicit exclusion files (`tests/failing-*.txt`) instead of `//@ ignore-backends: gcc`.

2. **Taxonomy of Cranelift (`cg_clif`) and GCC (`cg_gcc`) Test Exclusions**:

| Exclusion Category | Cranelift (`test_rustc_tests.sh`) | GCC (`build_system/src/test.rs` + `failing-*.txt`) | Underlying Technical Cause |
| :--- | :--- | :--- | :--- |
| Frontend error / diagnostic tests (`//~ ERROR`, `build-fail`) | Bulk removed by `rg` (`~12,700` UI files) | Separated into `test_failing_ui_pattern_tests` (`40` excluded in `failing-ice-tests.txt`) | `cg_clif` skips frontend-only diagnostic tests in CI to save compile time and because `panic=abort` sysroots alter `run-fail` exit behavior. |
| `should-fail` and `run-fail` / `catch_unwind` tests | Bulk removed (`//@ should-fail`, `//@ run-fail`); `Cargo.toml:55` disables `feature = "unwinding"` by default | `run-fail` removed in normal pass (`test.rs:907`); `libstd` built with `-Cpanic=abort` in `bootstrap` (`test.rs:4452`) | Without DWARF LSDA landing pads (`UnwindAction::Cleanup`), panics either abort immediately or unwind past `catch_unwind` frames (confirmed empirically on `next-power-of-two-overflow-debug.rs`, `int-abs-overflow.rs`, `issue-8460.rs`). |
| LLVM-specific flags, IR, & intrinsics (`-Cllvm-args`, `llvm.*`) | Bulk removed (`-Cllvm-args`) + 14 `run-make` / `ui` files (`llvm-ident`, `llvm-outputs`, `volatile-intrinsics`, `dont-invalid-bitcast-x86_64.rs`) | Filtered by `-Cllvm-args` (`test.rs:909`) + `failing-ui-tests.txt` (`simd-intrinsic-*`, `llvm-*`) | Tests pass LLVM CLI flags (`-Cllvm-args=...`), call `llvm.*` intrinsics, or inspect `.ll`/`.bc` bitcode artifacts. |
| Link-Time Optimization (LTO / ThinLTO / Cross-Lang LTO) | Bulk removed (`rg "lto"`) + 11 `run-make` dirs (`lto-*`, `cross-lang-lto`, `fat-then-thin-lto`, `cdylib`) | Filtered by `-Clto` / `-Clinker-plugin-lto` (`test.rs:919-926`) + 6 entries in `failing-lto-tests.txt` | Neither Cranelift nor `libgccjit` emits LLVM bitcode sections (`.llvmbc`) required by `rust-lld` linker-plugin LTO or ThinLTO. |
| C-variadic definitions & non-C variadic ABIs | 12 `ui` + 1 `run-make` files (`c-link-to-rust-va-list-fn`, `variadic-ffi.rs`, `c-variadic/*`) | 9 entries in `failing-ui-tests.txt` (`c-variadic/*`, `variadic-ffi.rs`) | Callee-side `VaList` (`va_start`/`va_arg`) and float/non-C variadics are unimplemented in `cg_clif` and partially unsupported in `libgccjit`. |
| Inline assembly (`asm!` `goto`/labels, `may_unwind`, `sym`) | 7 `ui` files (`asm/x86_64/goto.rs`, `label-operand.rs`, `may_unwind.rs`, `global-asm-mono-sym-fn.rs`) | `asm/may_unwind.rs` and inline-asm constraint edge cases in `failing-ui-tests.txt` | Cranelift delegates `asm!` to an external assembler stub without `asm goto` label targets or `may_unwind` landing pads. |
| Coverage & sanitizer instrumentation | `tests/ui/instrument-coverage/` + `precise-drop-with-coverage.rs` + `kcfi-c-variadic.rs` | `instrument-coverage/*` and sanitizer tests in `failing-ui-tests.txt` | `-Cinstrument-coverage` (`__llvm_covmap`) and LLVM sanitizer passes (`-Zsanitizer=cfi/kcfi/address`) are LLVM-specific. |
| Entire `tests/ui` subdirectories (`abi`, `extern`, `proc-macro`, `threads-sendsync`) | Kept (except specific `rm` entries) | Removed wholesale in `test.rs:992` (`["abi", "extern", "proc-macro", "threads-sendsync"]`) | `cg_gcc` removes these 4 directories during `test_successful_rustc` due to ABI attribute, TLS/unwinding, and dlopen proc-macro gaps. |
| Optimization-dependent & implementation-limit tests | 12 `ui` + `incremental` files (`issue-28950.rs`, `init-large-type.rs`, `StackColoring`, `huge-stacks.rs`, `large-byval-align.rs`, `issue-49153.rs`) | `issue-28950.rs`, `init-large-type.rs`, `huge-stacks.rs` in `failing-ui-tests.txt` | Tests rely on LLVM stack coloring, dead-reference elimination before linking, or stack frames $>4\text{ GiB}$. |

### 4. Standard Library Test Suites (`library/`)

Basis: source (`src/bootstrap/src/core/build_steps/test.rs:3426-3575`, `compiler/rustc_codegen_cranelift/build_system/tests.rs:108-195`, `compiler/rustc_codegen_cranelift/patches/0001-*.patch`..`0028-*.patch`)

- Unlike `tests/*` (which use `compiletest`), standard library unit and integration tests in `library/` are driven via `cargo test` (`Step for Crate` in `src/bootstrap/src/core/build_steps/test.rs:3426`).
- In `rustc 1.99.1`, `core` and `alloc` unit tests are split into standalone test crates `library/coretests` (**1,645 `#[test]` functions** across 176 files) and `library/alloctests` (**1,228 `#[test]` functions** across 63 files), alongside `library/std` (**965 `#[test]` functions** across 696 files), `library/compiler-builtins` (345), `library/alloc` (315), `library/stdarch` (170), `library/test` (64), `library/portable-simd` (44), and `library/std_detect` (38).
- To run `library/` tests with `rustc_codegen_cranelift` (`build_system/tests.rs:108-135`), `cg_clif` applies 4 patches in `compiler/rustc_codegen_cranelift/patches/`:
  1. `0001-portable-simd-Disable-f16-usage-in-portable-simd.patch` (disables `f16` SIMD conversions).
  2. `0027-stdlib-128bit-atomic-operations.patch` and `0027-sysroot_tests-128bit-atomic-operations.patch` (adjusts 128-bit atomic expectations).
  3. `0028-sysroot_tests-Disable-long-running-tests.patch` (skips slow unoptimized BTree/sort/hash stress tests when testing with an unoptimized or Cranelift-compiled sysroot).

## Boundaries

- **Full 24,545-test execution under alternate backends**: We executed representative slices of `ui`, `codegen-llvm`, `assembly-llvm`, `mir-opt`, and `codegen-units` directly through `compiletest` (`support/compiletest_probe_results.json`), while cataloging the full 24,545-test corpus statically in `rustc-test-suite-machine-readable-classification`. Running the entire `tests/ui` suite end-to-end requires ~25–45 minutes of CPU time and is recorded as a deferred batch validation step.
- **Unwinding in prebuilt `rustc-codegen-cranelift-preview`**: Because `rustup`'s `rustc-codegen-cranelift-preview` component is built with default Cargo features (`unwinding` disabled), `catch_unwind` and thread-panic recovery require rebuilding `rustc_codegen_cranelift` with `--features unwinding`.

## Evidence

- **Standalone `compiletest` execution probe and results**:
  - `support/run_compiletest_standalone_probe.py` and `support/compiletest_probe_results.json`: Demonstrates direct CLI invocation of `compiletest` against `rustc 1.99.1` (`71/71` passing in `tests/ui/numbers-arithmetic/`, `46/46` passing in `tests/codegen-units/`, `422/422` passing in `tests/assembly-llvm/`), loopback `remote-test-client` + `remote-test-server` (`71/71` passing once sysroot `.so` libraries are pushed), and `rustc 1.102.0-nightly` with `--override-codegen-backend cranelift` (`65/69` passing; all 3 `run-pass` failures caused by disabled `feature = "unwinding"` in `rustc-codegen-cranelift-preview`).
- **Primary upstream source citations (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`)**:
  - `src/tools/compiletest/src/cli.rs:36-260` (required and optional CLI flags)
  - `src/tools/compiletest/src/common.rs:95-295, 1160-1280` (`TestMode`, `PassMode`, `FailMode`, `CodegenBackend`, target cfg discovery)
  - `src/tools/compiletest/src/directives.rs:1-1482`, `directives/directive_names.rs:1-354`, `directives/handlers.rs:1-375`, `directives/cfg.rs:1-351`, `directives/needs.rs:1-461`
  - `src/tools/compiletest/src/runtest/` (`ui.rs`, `codegen.rs`, `assembly.rs`, `mir_opt.rs`, `codegen_units.rs`, `incremental.rs`, `debuginfo.rs`, `coverage.rs`, `crashes.rs`, `run_make.rs`)
  - `src/bootstrap/src/core/build_steps/test.rs:2210-2900, 3426-3575, 4195-4500` (`Compiletest`, `Crate`, `TestHelpers`, `CodegenCranelift`, `CodegenGCC`)
  - `compiler/rustc_codegen_cranelift/scripts/test_rustc_tests.sh:1-208`, `scripts/setup_rust_fork.sh:1-85`, `Cargo.toml:50-56`, `src/abi/mod.rs:851-853`, `src/intrinsics/mod.rs:1383-1407`
  - `compiler/rustc_codegen_gcc/build_system/src/test.rs:882-1344` and `compiler/rustc_codegen_gcc/tests/failing-*.txt`

## Revalidation

Run `python3 support/run_compiletest_standalone_probe.py` against a `rust-lang/rust` checkout and `compiletest` binary to re-verify standalone `compiletest` execution, `librust_test_helpers.a` linkage, `remote-test-server` loopback execution, and `--override-codegen-backend` dispatch.
