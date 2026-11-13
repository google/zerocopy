# Miri, `rust-analyzer`, Proc-Macro, and Doctest Toolchain Integration Contracts at Rust `1.99.1`

## Summary

A drop-in replacement for `rustc` at Rust `1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`) interacts with four distinct
classes of developer and verification tools—**Miri**, **`rust-analyzer`**,
**procedural macros (`proc_macro` bridge)**, and **`rustdoc --test`
doctests**—each coupling to a different boundary of the compiler. Source
analysis of `src/tools/miri`, `src/tools/rust-analyzer`,
`library/proc_macro/src/bridge/`, `compiler/rustc_expand`,
`compiler/rustc_metadata`, and `src/librustdoc/doctest.rs`, combined with
empirical CLI probes (`support/tooling_integration_contracts.json`), establishes
four governing contracts:

1. **Miri couples to `rustc_private` in-process queries and `-Zalways-encode-mir`
   `.rmeta` artifacts, never to the codegen backend:** Miri links directly
   against **19 internal `rustc_*` crates** (`rustc_abi`, `rustc_apfloat`,
   `rustc_ast`, `rustc_codegen_ssa`, `rustc_const_eval`, `rustc_data_structures`,
   `rustc_driver`, `rustc_errors`, `rustc_hir`, `rustc_hir_analysis`,
   `rustc_index`, `rustc_interface`, `rustc_log`, `rustc_metadata`,
   `rustc_middle`, `rustc_session`, `rustc_span`, `rustc_symbol_mangling`, and
   `rustc_target`) and interprets `optimized_mir` via `rustc_const_eval::interpret`.
   `cargo miri setup` uses `rustc-build-sysroot` (`src/tools/miri/cargo-miri/src/setup.rs:8-192`)
   to compile a dedicated sysroot with `--cfg miri` and `-Zalways-encode-mir`.
   At `1.99.1`, Miri exposes **31 `-Zmiri-*` flags**, defaults to **Stacked
   Borrows** while supporting **Tree Borrows** via `-Zmiri-tree-borrows` (plus
   `-Zmiri-tree-borrows-implicit-writes`, `-Zmiri-tree-borrows-no-precise-interior-mut`,
   and `-Zmiri-tree-borrows-relax-custom-allocator-uniqueness`), vector-clock
   data-race detection, C11 weak-memory load buffering, and experimental
   **GenMC stateless model checking** (`-Zmiri-genmc`, with **67 dedicated test
   files** in `src/tools/miri/tests/genmc/` out of **1,189 total test files**).
2. **`rust-analyzer` is decoupled from the codegen backend except for host
   proc-macro dylibs and `rustc-Hash` ABI:** `rust-analyzer` never loads `.rlib`
   or `.rmeta` binaries for IDE semantic analysis; instead, it requires the
   **`rust-src` sysroot source tree** (`lib/rustlib/src/rust/library`,
   `crates/project-model/src/sysroot.rs:1-85`), queries `rustc --print sysroot`,
   `rustc -vV`, `rustc --print cfg`, and target data-layout via
   `rustc -Zunstable-options --print target-spec-json` (with `RUSTC_BOOTSTRAP=1`),
   consumes `cargo check --message-format=json-diagnostic-rendered-ansi` on
   save, and spawns **`rust-analyzer-proc-macro-srv`** (`libexec/rust-analyzer-proc-macro-srv`,
   gated by `RUST_ANALYZER_INTERNALS_DO_NOT_USE`, exit code `122` if unset,
   `crates/proc-macro-srv-cli/src/main.rs:18-56`) speaking protocol version
   **`CURRENT_API_VERSION = 6` (`HASHED_AST_ID`)** over `json-legacy` or
   `bidirectional-postcard-prototype` (`crates/proc-macro-api/src/lib.rs:28-55`).
3. **Procedural-macro `.so`/`.dylib`/`.dll` crates require a narrow C-ABI entry
   table (`__rustc_proc_macro_decls_<hash>__`) and `rustc_driver` version cookie:**
   A compiled proc-macro crate is a native host dynamic library exporting a
   single symbol `__rustc_proc_macro_decls_<stable_crate_id>__` of type
   `&[ bridge::client::ProcMacro ]`, flanked by a `.rustc` metadata section and a
   `RUSTC_VERSION_STRING` check (`library/proc_macro/src/bridge/client.rs:215-299`).
   All cross-dylib calls cross a single C-ABI function pointer
   `extern "C" fn(BridgeConfig<'_>) -> Buffer` using byte-serialized RPC packets
   (`ApiTags`, `ExpnGlobals`, `TokenStream` handles) with `catch_unwind` on the
   client side, isolating the compiler host from unwinding or Rust-ABI mismatches
   inside the proc-macro dylib—provided the host backend compiles `crate-type =
   proc-macro` as a native host shared library with `extern "C"` ABI fidelity.
4. **`rustdoc --test` natively supports drop-in replacement compilers via
   `--test-builder`:** `rustdoc` compiles every documentation test by invoking the
   binary passed to `--test-builder <path>` (or wrapping it with
   `--test-builder-wrapper <path>`, `src/librustdoc/config.rs:134-137, 877-954`,
   `src/librustdoc/doctest.rs:657-718`), passing `@<tmp>/rustdoc-cfgs --edition
   <E> --target <T> --color never --crate-type=bin -o <tmp>/rust_out -` with the
   synthesized test harness streamed on `stdin`.

## Applicability

This report applies to **Rust 1.99.1** (`rust-lang/rust`
`58cf8f9c35b355199727627d07ae34a4e2846d67`), compared against
**`nightly-2026-11-12`** (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`). All
source paths refer to the `rust-lang/rust` monorepo (which vendors `src/tools/miri`
and `src/tools/rust-analyzer`).

## Findings

### 1. Miri architecture, `rustc_private` surface, aliasing models, and test suite

Basis: source + empirical

#### 1.1 `rustc_private` crate and query dependencies

Miri is implemented as a custom `rustc_driver::Callbacks` driver that replaces
the codegen phase with MIR interpretation (`src/tools/miri/src/lib.rs` and
`bin/miri.rs`). Scanning all `extern crate rustc_*` declarations across
`src/tools/miri` (`support/tooling_integration_contracts.json`) shows that Miri
depends on **19 compiler crates**:

- **Core type, layout, and MIR crates:** `rustc_abi`, `rustc_apfloat`,
  `rustc_const_eval` (providing `interpret::InterpCx`, `MPlaceTy`, `OpTy`,
  `ImmTy`, and `Machine<'tcx>`), `rustc_middle` (`TyCtxt`, `mir::Body`,
  `Instance`), `rustc_target`, and `rustc_symbol_mangling`.
- **Frontend and driver crates:** `rustc_ast`, `rustc_driver`, `rustc_errors`,
  `rustc_hir`, `rustc_hir_analysis`, `rustc_interface`, `rustc_log`,
  `rustc_metadata`, `rustc_session`, `rustc_span`, `rustc_data_structures`, and
  `rustc_index`.
- **`rustc_codegen_ssa`:** Used only for target feature / inline-assembly and
  intrinsic fallback metadata, never to invoke LLVM or emit object files.

When a replacement compiler shares the `rustc` frontend and swaps only
`CodegenBackend` (via `-Zcodegen-backend=...` or linking a verified backend into
`rustc_driver`), Miri runs unmodified because Miri halts compilation after
`tcx.optimized_mir(def_id)` before `CodegenBackend::codegen_crate` is ever
called.

#### 1.2 How `cargo miri setup` builds its sysroot

Because Miri interprets every called function down to `core`, `alloc`, and `std`
(stopping only at `#[rustc_intrinsic]` operations and shimmed OS syscalls), every
crate in the sysroot must contain serialized MIR bodies in its `.rmeta` payload.
In `src/tools/miri/cargo-miri/src/setup.rs:8-192` and `phases.rs:268-678`:

- `cargo-miri` invokes the `rustc_build_sysroot` crate (`SysrootBuilder::new(&sysroot_dir, target)`),
  setting `RUSTC` back to the `cargo-miri` binary with `MIRI_CALLED_FROM_SETUP=1`.
- During `RustcPhase::Setup`, `cargo-miri` forwards each sysroot crate build to
  `miri` (`--sysroot` omitted during bootstrap, `--cfg miri`,
  `-Zalways-encode-mir`), producing `.rlib`/`.rmeta` files cached under the host's
  Miri cache directory (printed by `cargo miri setup --print-sysroot`).
- For subsequent `cargo miri test` / `cargo miri run` invocations, `cargo-miri`
  passes `--sysroot <MIRI_SYSROOT>` and `--cfg miri` to all target crates and
  `rustdoc` invocations (`phases.rs:468, 603, 676-678`).

#### 1.3 Aliasing models, concurrency checkers, and GenMC at `1.99.1`

Across `src/tools/miri/src/`, Miri accepts **31 `-Zmiri-*` flags**
(`support/tooling_integration_contracts.json`), grouped into four semantic
subsystems:

| Subsystem | Default at `1.99.1` | Controlling `-Zmiri-*` Flags | Stability & Replacement-Compiler Alignment |
| :--- | :--- | :--- | :--- |
| **Pointer aliasing & provenance** | **Stacked Borrows** (`-Zmiri-strict-provenance` optional) | `-Zmiri-tree-borrows`, `-Zmiri-tree-borrows-implicit-writes`, `-Zmiri-tree-borrows-no-precise-interior-mut`, `-Zmiri-tree-borrows-relax-custom-allocator-uniqueness`, `-Zmiri-disable-stacked-borrows`, `-Zmiri-permissive-provenance`, `-Zmiri-retag-fields` | Both Stacked Borrows (`borrow_tracker/stacked_borrows/`) and Tree Borrows (`borrow_tracker/tree_borrows/`) hook the same 4 `Machine` callbacks: `retag_place_contents`, `memory_read`, `memory_written`, and `dealloc`. Adapting Miri to a custom aliasing variant requires only implementing or parameterizing a module under `src/tools/miri/src/borrow_tracker/`. |
| **Type & invariant validation** | Enabled on every typed copy/retag | `-Zmiri-disable-validation`, `-Zmiri-recursive-validation`, `-Zmiri-disable-alignment-check`, `-Zmiri-symbolic-alignment-check` | Enforces `Scalar` valid ranges, `bool`/`char`/enum discriminant validity, and reference alignment/dereferenceability at `StatementKind::Assign` and `Retag`. |
| **Data-race & weak-memory emulation** | Vector-clock race detector + C11 weak-memory store buffers enabled | `-Zmiri-disable-data-race-detector`, `-Zmiri-disable-weak-memory-emulation`, `-Zmiri-track-weak-memory-loads`, `-Zmiri-deterministic-concurrency`, `-Zmiri-fixed-schedule`, `-Zmiri-many-seeds` | Implements C++20/C11 release/acquire/seqcst synchronization clocks (`concurrency/data_race.rs`) and per-location store buffers (`concurrency/weak_memory.rs`). |
| **GenMC stateless model checking** | Opt-in via `-Zmiri-genmc` | `-Zmiri-genmc` | Newly integrated at `1.99.1` (`concurrency/genmc/`), replacing randomized scheduler exploration (`-Zmiri-many-seeds`) with systematic DPOR execution graph exploration over atomic operations and mutexes, backed by **67 test files** in `src/tools/miri/tests/genmc/`. |

#### 1.4 Miri test suite size and structure at `1.99.1`

`src/tools/miri/tests/` contains **1,189 `.rs` test files** across 10
subdirectories:

- `fail/`: **547** tests (UB detection: aliasing, uninit, data races, alignment,
  invalid values, dangling pointers, unwinding).
- `pass/`: **375** tests (valid unsafe patterns, atomics, coroutines, SIMD,
  allocators, inline-asm shims).
- `fail-dep/` (**91**) and `pass-dep/` (**68**): tests requiring external crates
  (`libc`, `getrandom`, `num-traits`, `tokio`).
- `genmc/`: **67** stateless model-checking concurrency tests.
- `native-lib/` (**15**), `panic/` (**13**), `utils/` (**8**), `many-seeds/`
  (**3**), and `deps/` (**2**).

---

### 2. `rust-analyzer` toolchain discovery, sysroot source loading, and `proc-macro-srv` ABI

Basis: source

Inspecting `src/tools/rust-analyzer/crates/{project-model,proc-macro-api,proc-macro-srv,proc-macro-srv-cli}`
(`support/tooling_integration_contracts.json`) establishes the exact external
contract `rust-analyzer` requires from a toolchain:

1. **Toolchain binary and version probing (`crates/project-model/src/workspace.rs`,
   `toolchain_info/`):**
   - `rustc -vV`: parsed for `host:`, `release:`, and `commit-hash:` to populate
     `ProjectWorkspace::toolchain: Option<Version>`.
   - `rustc --print sysroot`: locates the toolchain root directory (`bin/`,
     `lib/`, `libexec/`).
   - `rustc --print cfg` (with optional `--target <triple>`): populates
     `ProjectWorkspace::rustc_cfg: Vec<CfgAtom>`.
   - `RUSTC_BOOTSTRAP=1 rustc -Zunstable-options --print target-spec-json`:
     extracts `data-layout`, `target-pointer-width`, `target-endian`, and
     `arch` into `TargetLoadResult`.
2. **Sysroot source loading (`crates/project-model/src/sysroot.rs:1-85`):**
   - Unlike `rustc`, `rust-analyzer` **cannot read `.rlib` or `.rmeta` binary
     metadata**. It resolves `$SYSROOT/lib/rustlib/src/rust/library` (installed
     by the `rust-src` rustup component or `RUST_SRC_PATH`) and loads `core`,
     `alloc`, `std`, `proc_macro`, and `test` as a `CargoWorkspace` (running
     `cargo metadata` on `library/Cargo.lock` / `library/sysroot/Cargo.toml`) or
     falls back to `RustLibSrcWorkspace::Stitched` source files.
   - If `rust-src` is missing, `Sysroot::is_rust_lib_src_empty()` returns `true`
     and `rust-analyzer` degrades gracefully: workspace crates still parse,
     highlight, and resolve local symbols, but prelude types (`Option`, `Result`,
     `Vec`, `String`, `Iterator`) and standard-library traits remain unresolved.
3. **Flycheck and build-script discovery (`cargo check` JSON):**
   - To run `build.rs` scripts and collect proc-macro dylib paths,
     `rust-analyzer` invokes `cargo check --workspace --message-format=json`
     (with `--keep-going` and `--all-targets`) during workspace loading, parsing
     `"reason": "build-script-executed"` (`out_dir`, `cfgs`, `env`) and
     `"reason": "compiler-artifact"` (where `"crate_types"` contains
     `"proc-macro"`, yielding `ProcMacroDylibPath`).
4. **Out-of-process proc-macro expansion (`rust-analyzer-proc-macro-srv`):**
   - `rust-analyzer` does not `dlopen` proc-macro `.so` files in its own LSP
     process. Instead, it spawns `$SYSROOT/libexec/rust-analyzer-proc-macro-srv`
     (or `rust-analyzer proc-macro` fallback) with
     `RUST_ANALYZER_INTERNALS_DO_NOT_USE=1` (`crates/proc-macro-srv-cli/src/main.rs:18-26`).
   - Client and server negotiate `version::CURRENT_API_VERSION = 6`
     (`HASHED_AST_ID`, `crates/proc-macro-api/src/lib.rs:28-39`) over stdin/stdout
     using either newline-delimited JSON (`--format json-legacy`) or
     `--format bidirectional-postcard-prototype`.
   - Inside `crates/proc-macro-srv/src/dylib.rs`, `proc-macro-srv` loads the
     compiled proc-macro dynamic library, verifies that the embedded
     `RUSTC_VERSION_STRING` matches its own `env!("RUSTC_VERSION")` (or reports a
     `ProcMacroLoadingError::AbiMismatch` diagnostic if the dylib was compiled by
     a different `rustc` commit/version), and invokes `rustc_proc_macro` bridge
     server routines using `rust-analyzer`'s own `SpanId` token-tree table.

---

### 3. Procedural-macro dylib ABI, `proc_macro::bridge`, and non-LLVM backend support

Basis: source

When `rustc` (or `rust-analyzer-proc-macro-srv`) compiles and loads a
`crate-type = "proc-macro"` crate (`library/proc_macro/src/bridge/{mod.rs,client.rs,server.rs}`,
`compiler/rustc_expand/src/proc_macro_server.rs`, and
`compiler/rustc_metadata/src/creader.rs`):

1. **What the backend must emit for a `proc-macro` crate:**
   - The compiler synthesizes a static declaration table symbol named
     `__rustc_proc_macro_decls_<stable_crate_id>__` containing a slice of
     `proc_macro::bridge::client::ProcMacro` descriptors (`CustomDerive`, `Attr`,
     `Bang`), alongside a `.rustc` ELF/Mach-O/PE metadata section so `creader`
     can read the crate's `rmeta` directly from the host `.so`/`.dylib`/`.dll`.
   - Every exported proc-macro entry point in `ProcMacro` holds an **`extern "C"`
     function pointer**:
     ```rust
     pub(super) run: extern "C" fn(BridgeConfig<'_>) -> Buffer
     ```
     (`library/proc_macro/src/bridge/client.rs:222`).
2. **How the `proc_macro::bridge` isolates the Rust ABI across the dylib boundary:**
   - `BridgeConfig<'a>` (`library/proc_macro/src/bridge/mod.rs:121-133`) is a
     `#[repr(C)]`-compatible bundle containing `input: Buffer` (a raw pointer +
     length + capacity byte buffer), `dispatch: Dispatcher` (an `extern "C"`
     callback function pointer back into the compiler server), and
     `force_show_panics: bool`.
   - Neither `TokenStream` nor `Span` crosses the FFI boundary as a direct Rust
     struct reference; instead, they cross as opaque integer handle counters
     (`Handle`) serialized into `Buffer` via `Encode`/`Decode`, while token
     operations (`TokenStream::from_str`, `Span::call_site`, diagnostic emission)
     dispatch back into `compiler/rustc_expand/src/proc_macro_server.rs` through
     `BridgeConfig::dispatch`.
   - On the client (dylib) side, `run_client` (`client.rs:245-295`) wraps the
     user's macro function in `std::panic::catch_unwind`, converts any panic
     payload into a serialized `PanicMessage` inside the returned `Buffer`, and
     returns normally over `extern "C"` without unwinding across the dylib
     boundary.
3. **Cranelift and GCC backend support for proc macros:**
   - Because proc-macro expansion crosses an `extern "C"` boundary and handles
     panics inside the dylib via `catch_unwind`, **any backend that supports
     building host dynamic libraries (`--crate-type proc-macro` / `dylib`), C-ABI
     struct passing for `BridgeConfig`/`Buffer`, and `.rustc` metadata section
     emission can compile and run procedural macros**.
   - Both `rustc_codegen_cranelift` and `rustc_codegen_gcc` compile and execute
     procedural macros on `x86_64-unknown-linux-gnu`; their only limitation is
     when a proc-macro panics if the sysroot was built with `-Cpanic=abort` (in
     which case `catch_unwind` cannot catch the panic and the compiler process
     aborts unless proc-macro expansion is run out-of-process).

---

### 4. Doctest execution and `rustdoc --test-builder` compatibility

Basis: source + empirical

Inspecting `src/librustdoc/doctest.rs:650-730` and `src/librustdoc/config.rs:134-137, 877-954`
and probing `rustdoc +1.99.1` empirically (`support/probe_tooling_contracts.py`,
`support/tooling_integration_contracts.json`) confirms how `rustdoc --test`
drives the compiler:

- By default, `rustdoc --test` locates a sibling `rustc` binary next to `rustdoc`
  (or via `RUSTC`). However, `rustdoc` provides two flags specifically designed
  for custom compiler drivers and wrappers:
  - `--test-builder <PATH>`: replaces the `rustc` binary invoked to compile each
    doctest crate (`config.rs:877`).
  - `-Zunstable-options --test-builder-wrapper <PATH>`: prepends one or more
    wrapper executables (analogous to `RUSTC_WRAPPER`) in front of the
    `--test-builder` binary (`doctest.rs:660, 717`).
- Running our empirical probe (`rustdoc +1.99.1 -Zunstable-options --test
  --test-builder=<wrapper> lib.rs`, `support/tooling_integration_contracts.json:229-250`)
  exits `0` (`1 passed; 0 failed`) and captures the exact invocation contract a
  replacement compiler must accept for doctests:
  ```json
  {
    "args": [
      "@/tmp/doctest_probe/rustdoc-cfgs",
      "--edition", "2015",
      "--target", "x86_64-unknown-linux-gnu",
      "--color", "never",
      "--crate-type=bin",
      "-o", "/tmp/doctest_probe/rust_out",
      "-"
    ]
  }
  ```
- Specifically, a replacement compiler used as `--test-builder` must support:
  1. **Response files (`@<path>/rustdoc-cfgs`)** containing newline-separated
     `--cfg` flags.
  2. **Reading crate source code from `stdin` (`-` as the input filename)**.
  3. **Merged doctest harnesses (`--edition 2024` / doctest merging):** when
     `rustdoc` merges multiple doctests into a single binary crate to amortize
     compilation overhead, it passes `--crate-type=bin -o <out> -` and falls back
     to per-doctest invocations if the merged compilation fails.

## Boundaries

- **Out-of-tree `rustc` forks with diverged `TyCtxt` vs. backend plugins:**
  Miri and `rust-analyzer-proc-macro-srv` compile in-tree against internal
  `rustc_*` crates (`#![feature(rustc_private)]`). A replacement compiler that
  preserves `rustc`'s frontend and swaps only `CodegenBackend` gets Miri and
  `rust-analyzer` compatibility for free; a clean-room compiler written in
  another language would have to either delegate Miri/`rust-analyzer` to the
  upstream `rustc` frontend or re-implement the `proc-macro-srv` postcard/JSON
  wire protocol (`CURRENT_API_VERSION = 6`).
- **GenMC platform and feature scope:** At `1.99.1`, Miri's `-Zmiri-genmc` mode
  supports core atomic operations, locks, and thread spawning across 67 test
  files, but does not yet support inline assembly, weak-memory store-buffer mixed
  size accesses, or arbitrary OS syscalls.

## Evidence

- **Miri (`rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `extern crate rustc_*` dependencies (`19` crates) and `-Zmiri-*` CLI flags
    (`31` flags): `src/tools/miri/src/lib.rs:1-120`, `src/tools/miri/src/bin/miri.rs:1-450`.
  - Sysroot builder (`rustc-build-sysroot`, `MIRI_SYSROOT`, `--cfg miri`,
    `-Zalways-encode-mir`): `src/tools/miri/cargo-miri/src/setup.rs:8-192`,
    `src/tools/miri/cargo-miri/src/phases.rs:36-678`.
  - Aliasing models & GenMC: `src/tools/miri/src/borrow_tracker/{stacked_borrows,tree_borrows}/`,
    `src/tools/miri/src/concurrency/{data_race.rs,weak_memory.rs,genmc/}`.
- **`rust-analyzer` (`rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - Sysroot source loading (`rust-src` vs `.rlib`):
    `src/tools/rust-analyzer/crates/project-model/src/sysroot.rs:1-85`.
  - Toolchain probing (`rustc --print sysroot`, `rustc --print cfg`, `target-spec-json`):
    `src/tools/rust-analyzer/crates/project-model/src/workspace.rs:1-95`.
  - Proc-macro protocol (`CURRENT_API_VERSION = 6`, `JsonLegacy`,
    `BidirectionalPostcardPrototype`):
    `src/tools/rust-analyzer/crates/proc-macro-api/src/lib.rs:28-75`,
    `src/tools/rust-analyzer/crates/proc-macro-srv/src/lib.rs:1-85`,
    `src/tools/rust-analyzer/crates/proc-macro-srv-cli/src/main.rs:18-60`.
- **Proc-macro bridge & doctests (`rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `BridgeConfig<'a>` and `extern "C" fn(BridgeConfig<'_>) -> Buffer`:
    `library/proc_macro/src/bridge/mod.rs:121-133`,
    `library/proc_macro/src/bridge/client.rs:220-295`,
    `library/proc_macro/src/bridge/server.rs:140-275`.
  - `rustdoc --test` and `--test-builder`:
    `src/librustdoc/config.rs:134-137, 722-724, 877, 951-954`,
    `src/librustdoc/doctest.rs:657-718`.
- **Preserved artifacts in `support/`:**
  - `support/probe_tooling_contracts.py`: source extractor and empirical
    `rustdoc --test --test-builder` probe script.
  - `support/tooling_integration_contracts.json`: extracted crate dependencies,
    `-Zmiri-*` flag table, Miri test suite counts, `rust-analyzer` protocol
    headers, and captured `rustdoc --test-builder` invocation trace.

## Revalidation

Run `python3 support/probe_tooling_contracts.py` against a checkout of
`rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67` (with
`rustup toolchain 1.99.1` installed) and compare `/tmp/reval/c7_extracted.json`
against `support/tooling_integration_contracts.json`.
