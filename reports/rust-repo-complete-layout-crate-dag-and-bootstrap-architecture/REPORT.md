# Rust Repository Complete Layout, Compiler Crate DAG, Query-Provider Map, and Multi-Stage Bootstrap Architecture

## Summary

At `rust-lang/rust` commit `412be32a6a189d9a28922beee178bc0abee9d492` (`1.102.0-nightly`, `2026-11-18`), the superproject tracks **64,687 files** (`~231.9 MB` of in-tree blobs) and **13 Git submodules** (`160000` gitlinks) organized into **32 root files** and **6 root directories** (`.github/`, `LICENSES/`, `compiler/`, `library/`, `src/`, `tests/`). Across the tree, **391 `Cargo.toml` manifests** and **63 `Cargo.lock` lockfiles** partition compilation into strictly isolated Cargo dependency graphs: the root compiler/tools workspace (`Cargo.toml`, `45` members, `Cargo.lock` with `644` packages), the standard-library workspace (`library/Cargo.toml`, `4` root members expanding to `51` `Cargo.toml`s under `library/`, `Cargo.lock` with `50` packages), the standalone build orchestrator (`src/bootstrap/Cargo.toml`, `121` locked packages), and excluded `#![feature(rustc_private)]` consumers (`compiler/rustc_codegen_cranelift`, `compiler/rustc_codegen_gcc`, and subtree workspaces such as `src/tools/rust-analyzer` and `src/tools/miri`).

The compiler and documentation core consists of **79 direct `compiler/*` crates** (`85` `compiler/**/Cargo.toml` manifests including `6` nested build-system/test packages) plus `src/librustdoc` (`80` crates total, **942,429 raw lines** / **715,601 approximate SLOC**, including `4,056` raw lines of C++ in `compiler/rustc_llvm/llvm-wrapper/`). Relative to `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, `78` direct `compiler/*` crates and `83` manifests), two crates were added (`rustc_expand_queries` and `rustc_structures`), one crate was removed (`rustc_baked_icu_data`), one nested GCC assembly-test harness (`compiler/rustc_codegen_gcc/build_system/asm-tester`) was added, a 13th submodule (`src/tpde`) was introduced, and a 22nd `compiletest` suite (`tests/assembly-gcc`) was added. Partitioning all `80` compiler and `rustdoc` crates along verification boundaries yields:
1. **32 frontend-only crates** (`449,495` raw lines / **343,596 SLOC**, `48.0%` of compiler+rustdoc SLOC) — lexing, parsing, macro expansion, name resolution, HIR lowering, trait solving, lints, THIR construction, and borrow checking, none of which execute after `MirPhase::Runtime(RuntimePhase::PostCleanup)` capture in a certifying backend;
2. **29 semantic-middle and shared-substrate crates** (`318,099` raw lines / **232,748 SLOC**, `32.5%`) — target/ABI layout (`rustc_abi`, `rustc_target`), interned `TyCtxt`/MIR (`rustc_type_ir`, `rustc_middle`, `rustc_ty_utils`), CTFE (`rustc_const_eval`), MIR passes (`rustc_mir_transform`), monomorphization/mangling (`rustc_monomorphize`, `rustc_symbol_mangling`), `.rmeta` serialization and query caching (`rustc_metadata`, `rustc_incremental`, `rustc_query_impl`), backend-agnostic SSA lowering (`rustc_codegen_ssa`), `rustc_public` (`stable_mir`), and foundational arena/index/span substrates;
3. **19 diagnostic, driver, and concrete-backend crates** (`174,835` raw lines / **139,257 SLOC**, `19.5%`) — CLI/driver orchestration (`rustc-main`, `rustc_driver`, `rustc_driver_impl`, `rustc_interface`), structured diagnostics, pretty-printers, `librustdoc`, and the LLVM, Cranelift, and GCC backends.

Inter-crate decoupling rests on two mechanisms: (a) the **`TyCtxt` query engine** (`compiler/rustc_middle/src/queries.rs`, **330 queries** and **8 `non_query` `DepKind`s**, `+4` queries over `1.99.1`), whose function-pointer tables (`Providers` and `ExternProviders`) are populated at startup across **24 crates** (`300` locally provided queries, `23` extern-only `separate_provide_extern` queries backed solely by `rustc_metadata`, and `7` `TyCtxtFeed`-only queries); and (b) **`src/bootstrap` (`x.py`)**, a memoized, cycle-checked `Step` DAG (`88` Rust/Python source files, `49,490` raw lines / `37,561` SLOC) that interposes `build/bootstrap/debug/rustc` as both `RUSTC` and `RUSTC_WRAPPER` to switch compilers, sysroots, stability enforcement (`RUSTC_FORCE_UNSTABLE=1` -> `-Zforce-unstable-if-unmarked`), and symbol-hash metadata (`__CARGO_DEFAULT_LIB_METADATA`) across `stage 0` through `stage 2` (and `stage 3` uplift or `full-bootstrap` verification).

## Applicability

- **Primary examined snapshot:** `rust-lang/rust` commit `412be32a6a189d9a28922beee178bc0abee9d492` (`in_tree_version = 1.102.0`, committed `2026-11-18T12:20:09Z`), together with all **13** Git submodule revisions pinned in its `.gitmodules` and tree gitlinks (`src/llvm-project` at `08ec928a5bd1866f4008c8ad216166ca685fd380`, `src/tools/cargo` at `f93c676e3e7ab1aee08dc95d869700f6b99a1a20`, `src/tools/rustc-perf` at `15d95905429e577d5a710b17c49e04b4451c263b`, `src/tools/enzyme` at `9cff5a8afebc22748bb36c135dfe5a09dd1047f3`, `src/gcc` at `e1c6e07b095d091177376a163da44039475e05e3`, `src/tpde` at `050927ee81dc11a9e599fa2524ff0eef16daf51a`, `library/backtrace` at `d902726a1dcdc1e1c66f73d1162181b5423c645b`, and the `6` documentation book submodules recorded in `REPORT.json`).
- **Baseline release comparison:** `rust-lang/rust` release `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, paired with `rust-lang/llvm-project` `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, LLVM `23.1.1`). All structural differences between `1.99.1` and `412be32a6a189d9a28922beee178bc0abee9d492` in `compiler/`, `queries.rs`, submodules, and `tests/` are explicitly isolated below.
- **Relationship to companion corpus reports:** Core AST/HIR/THIR/MIR/`TyKind` enum variant tables, the `20` `rustc_codegen_ssa::traits` (`281` methods), and the `381` `rustc_codegen_llvm` LLVM FFI declarations at `1.99.1` are documented in `rustc-baseline-repository-map-and-internal-interfaces`. Detailed `compiletest` CLI flags, `//@` directive evaluation, and per-file test-tier classifications are covered in `rustc-compiletest-bootstrap-and-alternate-backend-test-mechanics` and `rustc-test-suite-machine-readable-classification`. This report supplies the complete file/workspace/crate/query/library/tool/submodule/`bootstrap` architectural map not expanded in those packages.

## Findings

### 1. Complete Top-Level Repository Census and Cargo Workspace Isolation

`Basis: source + execution (support/extract_repo_architecture.py -> support/rust_repo_inventory.json)`

#### 1.1 Root Directories, `src/*` Subtrees, and Root Files

At `412be32a6a189d9a28922beee178bc0abee9d492`, the repository root contains exactly **38 entries**: **6 directories** and **32 files**.

| Root Directory | Tracked Blobs | Git Submodules | Blob Bytes | Code/Script Files | Raw Lines | Approx. SLOC | Architectural Role |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| `.github/` | 18 | 0 | 47,029 | 0 | 0 | 0 | GitHub Actions workflows (`ci.yml`), issue templates, and workflow scripts |
| `LICENSES/` | 12 | 0 | 97,855 | 0 | 0 | 0 | Full SPDX license texts referenced by `REUSE.toml` |
| `compiler/` | 2,995 | 0 | 36,101,016 | 2,273 | 899,826 | 681,153 | `79` direct compiler crates (`85` `Cargo.toml`s) + `rustc_llvm` C++ shim |
| `library/` | 2,399 | 1 | 57,637,344 | 2,118 | 1,153,390 | 812,646 | Standard library workspace (`22` crate trees + `backtrace` submodule + `rtstartup`) |
| `src/` | 13,687 | 12 | 78,129,568 | 8,085 | 1,333,249 | 1,038,708 | `bootstrap`, `librustdoc`, `47` `tools/` entries, `ci/`, `doc/`, `etc/`, and `3` submodules |
| `tests/` | 45,544 | 0 | 58,803,803 | 27,837 | 856,987 | 532,175 | `22` `compiletest` test suites + `tests/auxiliary` + `COMPILER_TESTS.md` |

Inside `src/` (`13,687` blobs + `12` submodules), `16` immediate child entries separate build orchestration (`src/bootstrap/`), documentation generation (`src/librustdoc/`, `src/rustdoc-json-types/`, `src/doc/`), CI infrastructure (`src/ci/`), `47` tools (`src/tools/`), and three compiler-backend submodules (`src/llvm-project`, `src/gcc`, `src/tpde`):

| `src/` Entry | Tracked Blobs | Submodules | Code Raw Lines | Approx. SLOC | Architectural Role |
| :--- | ---: | ---: | ---: | ---: | :--- |
| `src/README.md` | 1 | 0 | 0 | 0 | Brief pointer explaining `src/` layout |
| `src/bootstrap/` | 169 | 0 | 49,490 | 37,323 | Multi-stage Rust build system (`x.py` / `bootstrap` binary + `rustc`/`rustdoc` shims) |
| `src/build_helper/` | 14 | 0 | 1,276 | 895 | Zero-external-dep helper crate shared by `bootstrap`, `compiletest`, and CI tools |
| `src/ci/` | 200 | 0 | 8,264 | 6,001 | Dockerfiles, Linux/macOS/Windows CI job scripts, and `citool` (`src/ci/citool`) |
| `src/doc/` | 756 | 6 | 1,308 | 1,105 | `rustc-dev-guide` subtree, `unstable-book`, manpages, and `6` book submodules |
| `src/etc/` | 65 | 0 | 17,868 | 15,684 | GDB/LLDB/CDB pretty-printers, bash/zsh completions, natvis, and helper scripts |
| `src/gcc/` | 0 | 1 | 0 | 0 | Git submodule (`rust-lang/gcc`) providing the forked `libgccjit` backend library |
| `src/librustdoc/` | 165 | 0 | 64,373 | 51,257 | Core `rustdoc` library (`pkg = rustdoc`, `30` `rustc_private` crate imports) |
| `src/llvm-project/` | 0 | 1 | 0 | 0 | Git submodule (`rust-lang/llvm-project`) providing LLVM, Clang, LLD, and compiler-rt |
| `src/rustc-std-workspace/` | 7 | 0 | 7 | 7 | Published crates.io empty stub sources (`v1.0.1`) for `{core,alloc,std}` shims |
| `src/rustdoc-json-types/` | 4 | 0 | 2,033 | 890 | Stable public schema crate defining `rustdoc` JSON output format types |
| `src/shim_utils/` | 5 | 0 | 270 | 188 | Shared argument-file and environment helpers linked into `bootstrap` shims |
| `src/stage0` | 1 | 0 | 0 | 0 | Pinned stage-0 `beta` compiler (`2026-11-10`), `rustfmt`, and SHA-256 tarball manifest |
| `src/tools/` | 12,299 | 3 | 1,188,360 | 925,358 | `47` build, test, lint, doc, release, and linker tools (`3` submodules + `44` in-tree) |
| `src/tpde/` | 0 | 1 | 0 | 0 | Git submodule (`rust-lang/tpde`) for experimental fast single-pass TPDE codegen |
| `src/version` | 1 | 0 | 0 | 0 | Single-line release version string (`1.102.0`) |

Every one of the **32 root files** serves a specific build, workspace, governance, CI/merge-queue, or SPDX compliance contract:

| Root File | Git Mode | Bytes | Raw Lines | Operational Role |
| :--- | :---: | ---: | ---: | :--- |
| `.clang-format` | `100644` | 20 | 1 | C/C++ formatting style for `compiler/rustc_llvm/llvm-wrapper/` |
| `.editorconfig` | `100644` | 983 | 44 | Cross-editor indentation and newline rules |
| `.git-blame-ignore-revs` | `100644` | 1,332 | 38 | Bulk formatting commits hidden from `git blame` |
| `.gitattributes` | `100644` | 449 | 18 | Line-ending normalization and linguistic/diff attributes |
| `.gitignore` | `100644` | 1,657 | 107 | Untracked build (`build/`, `target/`), editor, and stamp exclusions |
| `.gitmodules` | `100644` | 1,609 | 53 | URL, path, shallow, and branch declarations for all 13 Git submodules |
| `.ignore` | `100644` | 132 | 3 | Ripgrep/ag ignore overrides (excludes `tests/` golden noise by default) |
| `.mailmap` | `100644` | 40,702 | 754 | Canonical contributor author/email deduplication map |
| `AGENTS.md` | `100644` | 13,848 | 265 | Repository-level instructions and `./x` workflow guidance for coding agents |
| `CODE_OF_CONDUCT.md` | `100644` | 131 | 3 | Pointer to the Rust Code of Conduct |
| `CONTRIBUTING.md` | `100644` | 3,114 | 59 | Contributor routing to `rustc-dev-guide` and `std-dev-guide` |
| `COPYRIGHT` | `100644` | 1,571 | 34 | Top-level dual MIT/Apache-2.0 and third-party copyright notice summary |
| `Cargo.lock` | `100644` | 155,534 | 6,989 | Unified lockfile (`644` packages) for the root compiler + in-tree tools workspace |
| `Cargo.toml` | `100644` | 2,831 | 89 | Root Cargo workspace (`resolver = "2"`, `45` members, `6` excluded trees) |
| `INSTALL.md` | `100644` | 11,367 | 310 | Source build prerequisites, `./configure`, and `./x.py install` reference |
| `LICENSE-APACHE` | `100644` | 9,723 | 176 | Apache License 2.0 full text |
| `LICENSE-MIT` | `100644` | 1,068 | 25 | MIT License full text |
| `README.md` | `100644` | 3,304 | 79 | Project overview, quick-start build instructions, and license summary |
| `RELEASES.md` | `100644` | 944,545 | 16,566 | Historical release notes across stable Rust releases |
| `REUSE.toml` | `100644` | 6,610 | 219 | SPDX/REUSE per-path license annotations checked by `collect-license-metadata` |
| `bootstrap.example.toml` | `100644` | 55,543 | 1,237 | Documented template (`1,237` lines) for `bootstrap.toml` build configuration |
| `configure` | `100755` | 296 | 18 | POSIX shell wrapper invoking `src/bootstrap/configure.py` to emit `bootstrap.toml` |
| `license-metadata.json` | `100644` | 9,334 | 290 | Machine-readable license tree generated by `collect-license-metadata` |
| `package.json` | `100644` | 140 | 8 | Node.js dev-dependency manifest (`eslint`, `puppeteer`) for rustdoc JS/GUI checks |
| `rust-bors.toml` | `100644` | 2,708 | 107 | Merge-queue (`bors`) timeout and label configuration |
| `rustfmt.toml` | `100644` | 2,347 | 58 | Repository-wide Rust style configuration (`version = "Two"`) |
| `triagebot.toml` | `100644` | 63,492 | 2,094 | PR autolabeling, reviewer routing, `@rustbot`, and subtree mention rules |
| `typos.toml` | `100644` | 4,263 | 109 | Spell-checker exclusions and identifier allowlists |
| `x` | `100755` | 1,696 | 55 | POSIX `/bin/sh` launcher locating `python3`/`python`/`py`/`uv` to exec `x.py` |
| `x.ps1` | `100755` | 1,391 | 45 | PowerShell launcher locating Python on Windows/pwsh hosts to exec `x.py` |
| `x.py` | `100755` | 2,007 | 53 | Python bootstrap entrypoint delegating `main()` to `src/bootstrap/bootstrap.py` |
| `yarn.lock` | `100644` | 38,355 | 939 | Pinned JS dependency lockfile for `rustdoc-js` and `rustdoc-gui` tooling |

#### 1.2 Multi-Workspace Cargo Partitioning and Lockfile Isolation

`Basis: source (Cargo.toml:1-89, library/Cargo.toml:1-90, src/bootstrap/Cargo.toml:1-97, src/tools/tidy/src/deps.rs)`

A single Cargo workspace cannot span `rust-lang/rust` because (1) `src/bootstrap` must compile with the downloaded `stage 0` compiler before any in-tree crate exists, (2) `library/` defines `core`, `alloc`, and `std` themselves (requiring `#![no_core]`, `-Zforce-unstable-if-unmarked`, and `[patch.crates-io]` shims that would break host compiler crates), and (3) `#![feature(rustc_private)]` plugins (`rustc_codegen_cranelift`, `rustc_codegen_gcc`, `rust-analyzer`, `miri`, `rustfmt`) link against sysroot-installed `librustc_driver-*.so` / `.rmeta` artifacts built in an earlier `bootstrap` step. Consequently, the repository's **391 `Cargo.toml` files** and **63 `Cargo.lock` files** split into six distinct workspace tiers:

| Workspace / Package Root | Resolver | Direct `members` | Explicit `exclude` | Lockfile (`[[package]]` Count) | Isolation Rationale & Special Mechanics |
| :--- | :---: | ---: | :--- | :--- | :--- |
| `Cargo.toml` (root) | `"2"` | `45` (`compiler/rustc` + `6` `src/*` helpers + `38` `src/tools/*` crates) | `build`, `compiler/rustc_codegen_cranelift`, `compiler/rustc_codegen_gcc`, `src/bootstrap`, `tests/rustdoc-gui`, `obj` | `Cargo.lock` (`644`) | Unifies all `77` in-graph `compiler/*` crates (reachable transitively from `compiler/rustc`), `src/librustdoc` (via `src/tools/rustdoc`), `clippy`, `miri`, `rustfmt`, `compiletest`, and `tidy` under one lockfile. Commented `#[patch.crates-io]` slot (`Cargo.toml:89`) is audited by `tidy/src/extdeps.rs`. |
| `library/Cargo.toml` | `"1"` | `4` (`std`, `sysroot`, `coretests`, `alloctests`) | `stdarch`, `windows_link` | `library/Cargo.lock` (`50`) | Uses `cargo-features = ["profile-rustflags"]` (`library/Cargo.toml:1`); sets `compiler_builtins` `codegen-units = 10000` (`lines 19-30`) so linkers can dead-strip per-intrinsic `.o` members without clashing with `libgcc`; forces `panic_abort` `-Cpanic=abort` (`lines 49-58`); embeds LLVM bitcode and frame pointers in `[profile.dist]` (`lines 60-81`); and patches `rustc-std-workspace-{core,alloc,std}` and `windows-sys` via `[patch.crates-io]` (`lines 83-90`). |
| `library/{compiler-builtins,portable-simd,stdarch}/Cargo.toml` | `"2"`, `"1"`, `"3"` | `12`, `3`, `2` | `builtins-test-intrinsics`, `compiler-builtins`, `wasm-assert-instr-tests`, `rust_programs` | `170`, `64`, `131` packages | Standalone workspaces for subtree-synced library repositories when tested or developed independently; when built inside `sysroot`, `library/Cargo.toml` pulls their inner library crates (`compiler-builtins/compiler-builtins`, `portable-simd/crates/core_simd`, `stdarch/crates/core_arch`) directly via path/module edges. |
| `src/bootstrap/Cargo.toml` | *(single pkg, ed. 2024)* | `1` lib + `3` bins (`bootstrap`, `rustc`, `rustdoc`) | *(excluded by root `Cargo.toml:55`)* | `src/bootstrap/Cargo.lock` (`121`) | Compiled by `src/bootstrap/bootstrap.py` using `stage 0` `cargo` into `build/bootstrap/`; pins `cc = "=1.2.62"` and `cmake = "=0.1.54"` (`lines 29-30`) and sets `[profile.dev] debug = 0` (`bootstrap.debug = 1`) to minimize cold bootstrap latency. |
| `compiler/rustc_codegen_{cranelift,gcc}/Cargo.toml` | *(standalone pkgs)* | `1` `dylib` each (+ nested `build_system` / `asm-tester` packages) | *(excluded by root `Cargo.toml:53-54`)* | `68` (`cg_clif`), `39` (`cg_gcc`), `59` (`asm-tester`) | Compiled via `Mode::Codegen` after `Rustc` finishes, linking `rustc_*` crates from the sysroot via `#![feature(rustc_private)]` (`extern crate rustc_*;`) rather than Cargo path dependencies. |
| Standalone tool & CI workspaces (`src/tools/rust-analyzer`, `src/tools/miri/*`, `src/tools/rustbook`, `src/ci/citool`) | `"2"` / pkg | `4` (`rust-analyzer`), `1` (`rustbook`, `citool`) | `proc-macro-test/imp`, `no-std-smoke` | `369` (`r-a`), `224` (`miri`), `221` (`rustbook`), `154` (`citool`) | Allow subtree tools and CI orchestrators to evolve heavier third-party dependency graphs without bloating the compiler's `Cargo.lock` (`src/tools/tidy/src/deps.rs` enforces strict third-party crate allowlists on `rustc` and `sysroot`). |

---

### 2. Complete Census of All 80 Compiler and Rustdoc Crates, Dependency DAG, and 3-Way Verification Split

`Basis: source + execution (compiler/**/Cargo.toml, src/librustdoc/Cargo.toml, support/rust_repo_inventory.json)`

#### 2.1 Exact Structural Delta Between `1.99.1` (`58cf8f9c35b3`) and `1.102.0-nightly` (`412be32a6a18`)

Between `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and `412be32a6a189d9a28922beee178bc0abee9d492`, the direct `compiler/*` crate count increased from **78 to 79** (`+2` added, `-1` removed), and total `compiler/**/Cargo.toml` manifests increased from **83 to 85** (`+3` added, `-1` removed):

1. **Added — `compiler/rustc_expand_queries` (`2` `.rs` files, `95` raw lines / `65` SLOC, depth `15`):** Keeps `rustc_expand` (depth `14`) decoupled from `rustc_middle` (`TyCtxt`) so pre-`TyCtxt` macro expansion remains independent of middle-end query arenas while still caching built-in/proc-macro `#[derive]` expansions in the incremental query graph. `rustc_expand_queries` depends on `{rustc_ast, rustc_expand, rustc_middle, rustc_proc_macro, rustc_span}`, registers the `derive_macro_expansion` query (`compiler/rustc_expand_queries/src/lib.rs:9-11`), and installs `derive::expand_derive_macro_cached` into `rustc_expand::proc_macro::EXPAND_DERIVE_MACRO_CACHED` via an `AtomicPtr` callback (`src/lib.rs:5-7`).
2. **Added — `compiler/rustc_structures` (`8` `.rs` files, `606` raw lines / `485` SLOC, depth `6`, `22` direct dependents / `46` transitive dependents):** Extracted with `#![deny(unstable_features, reason = "ends up in dependencies of rust-analyzer")]` (`compiler/rustc_structures/src/lib.rs:3`) and an optional `nightly` Cargo feature gating `{rustc_data_structures, rustc_error_messages, rustc_macros, rustc_serialize, rustc_span}` (`Cargo.toml:19-28`). It houses six shared configuration/attribute types—`CollapseMacroDebuginfo`, `CrateType`, `Limit`, `LintName`, `NativeLibKind`, and `SanitizerSet`—so `rust-analyzer` can share `rustc`'s attribute data structures when compiled on a stable toolchain (`default-features = false`).
3. **Removed — `compiler/rustc_baked_icu_data`:** Eliminated after `rustc` dropped its vendored pre-baked ICU4X locale data crate.
4. **Nested `compiler/**/Cargo.toml` packages (`6` total, up from `5` in `1.99.1`):**
   - `compiler/rustc_codegen_cranelift/build_system/Cargo.toml` (`pkg = build_system`, `12` files, `2,243` raw / `1,859` SLOC — `./y.rs` builder/test harness for `cg_clif`);
   - `compiler/rustc_codegen_gcc/build_system/Cargo.toml` (`pkg = build_system`, `15` files, `3,489` raw / `2,869` SLOC — `./y.sh` builder/test harness for `cg_gcc`);
   - `compiler/rustc_codegen_gcc/build_system/asm-tester/Cargo.toml` (`pkg = asm-tester`, `1` file, `100` raw / `81` SLOC — **added after `1.99.1`** to cross-check inline-assembly lowering);
   - `compiler/rustc_codegen_gcc/tests/cross_lang_lto/Cargo.toml` (`pkg = cross_lang_lto`, `1` file, `9` raw / `8` SLOC);
   - `compiler/rustc_codegen_gcc/tests/hello-world/Cargo.toml` (`pkg = hello-world`, `1` file, `52` raw / `42` SLOC);
   - `compiler/rustc_codegen_gcc/tests/hello-world/mylib/Cargo.toml` (`pkg = mylib`, `1` file, `61` raw / `49` SLOC).

#### 2.2 Dependency Graph Topology, `rustc_proc_macro`, and `rustc_private` Edges

Across all **80** compiler and `rustdoc` crates (`79` `compiler/*` + `src/librustdoc`):
- **77 crates** form the static Cargo dependency closure of `compiler/rustc` (`pkg = rustc-main`, topological depth `21`, `out_degree = 6`, `transitive_deps_count = 76`). The graph is strictly acyclic with a **longest directed chain of 22 crates** (`21` edges):
  ```text
  rustc (d=21) -> rustc_driver (20) -> rustc_driver_impl (19) -> rustc_interface (18) ->
  rustc_codegen_llvm (17) -> rustc_codegen_ssa (16) -> rustc_metadata (15) ->
  rustc_expand (14) -> rustc_attr_parsing (13) -> rustc_parse (12) -> rustc_session (11) ->
  rustc_target (10) -> rustc_abi (9) -> rustc_errors (8) -> rustc_lint_defs (7) ->
  rustc_ast (6) -> rustc_ast_ir (5) -> rustc_span (4) -> rustc_data_structures (3) ->
  rustc_index (2) -> rustc_serialize (1) -> rustc_hashes (0)
  ```
- **3 crates** sit outside `rustc-main`'s Cargo graph (`Cargo.toml` `out_degree = 0`) and instead consume compiled compiler crates from the sysroot via `#![feature(rustc_private)]` (`extern crate rustc_*;`):
  - `compiler/rustc_codegen_cranelift` (`dylib`, `17` `rustc_private` crate imports including `rustc_abi`, `rustc_codegen_ssa`, `rustc_const_eval`, `rustc_driver`, `rustc_middle`, `rustc_session`, `rustc_symbol_mangling`, `rustc_target`);
  - `compiler/rustc_codegen_gcc` (`dylib`, `18` `rustc_private` crate imports including `rustc_abi`, `rustc_codegen_ssa`, `rustc_driver`, `rustc_interface`, `rustc_middle`, `rustc_session`, `rustc_symbol_mangling`, `rustc_target`, `rustc_type_ir`);
  - `src/librustdoc` (`rlib` linked by `src/tools/rustdoc`, `30` `rustc_private` crate imports spanning `rustc_ast` through `rustc_hir_analysis`, `rustc_interface`, `rustc_middle`, `rustc_passes`, `rustc_resolve`, and `rustc_trait_selection`).
- **Dual-compiled `compiler/rustc_proc_macro` (`0` local `.rs` files):** `compiler/rustc_proc_macro/Cargo.toml:12` sets `[lib] path = "../../library/proc_macro/src/lib.rs"`. Compiling `library/proc_macro`'s source under the distinct crate name `rustc_proc_macro` gives `rustc_expand`, `rustc_expand_queries`, `rustc_builtin_macros`, and `rustc_metadata` exact host `proc_macro::bridge::server` types without adding `library/proc_macro` as a Cargo path dependency (which would inject duplicate `libproc_macro.rlib` artifacts into the sysroot).
- **Highest in-degree hub crates (within the 77-crate Cargo graph):** `rustc_span` (`55` direct dependents / `58` transitive), `rustc_data_structures` (`51` / `59`), `rustc_macros` (`50` / `61`), `rustc_errors` (`33` / `49`), `rustc_abi` (`33` / `48`), `rustc_middle` (`32` / `34`), `rustc_index` (`32` / `60`), `rustc_attr_ir` (`32` / `42`), `rustc_ast` (`31` / `52`), and `rustc_hir` (`31` / `38`).

#### 2.3 Three-Way Verification Split Across the 80 Compiler + Rustdoc Crates

For a verified Rust compilation or translation-validation architecture, the 80 crates partition cleanly into three disjoint classes:

| Verification Class | Crate Count | Raw Lines | Approx. SLOC | Share of SLOC | Role in Verified Compilation / Backend Architecture |
| :--- | ---: | ---: | ---: | ---: | :--- |
| **(a) Frontend-only** | 32 | 449,495 | 343,596 | 48.0% | Lexing, parsing, macro/proc-macro expansion, name resolution, AST->HIR->THIR->`MirPhase::Built` lowering, type/trait inference (`rustc_infer`, `rustc_trait_selection`, `rustc_next_trait_solver`), exhaustiveness, lints, privacy, and borrow checking (`rustc_borrowck`, `rustc_mir_dataflow`). **Zero runtime execution after `Runtime(PostCleanup)` MIR capture** in a backend; in a standalone verified compiler, these establish well-typedness and borrow safety prior to MIR semantics. (Note: `rustc_mir_transform` calls `rustc_mir_dataflow` utilities during MIR elaboration/optimization before codegen, after which codegen never touches `rustc_mir_dataflow`.) |
| **(b) Semantic middle & shared substrates** | 29 | 318,099 | 232,748 | 32.5% | Defines the operational meaning of post-borrowck programs: `rustc_abi` & `rustc_target` (`TyAndLayout`, `FnAbi`, `331+` target specs), `rustc_type_ir` & `rustc_middle` (`TyCtxt`, `mir::Body`), `rustc_ty_utils` (`layout_of`, `fn_abi_of_*`, `instance`), `rustc_const_eval` (CTFE/Miri `AllocId` & `ConstValue`), `rustc_mir_transform` (`Runtime(PostCleanup)` & `Optimized` passes), `rustc_monomorphize` & `rustc_symbol_mangling` (`MonoItem` collector, v0/legacy mangling), `rustc_metadata` / `rustc_crate_store` / `rustc_incremental` / `rustc_query_impl` (`.rmeta` cross-crate generics/MIR), `rustc_codegen_ssa` & `rustc_sanitizers` (backend-agnostic SSA/ABI orchestration), `rustc_public` / `rustc_public_bridge` (`stable_mir` extraction), plus arena/index/span/serialization substrates. |
| **(c) Diagnostics, driver & concrete backends** | 19 | 174,835 | 139,257 | 19.5% | Non-semantic error emission (`rustc_errors`, `rustc_error_codes`, `rustc_error_messages`), AST/HIR/DOT pretty-printers, OS/thread-pool utilities, CLI orchestration (`rustc-main`, `rustc_driver`, `rustc_driver_impl`, `rustc_interface`), `src/librustdoc`, and the three unverified target codegen backends (`rustc_codegen_llvm` + `rustc_llvm`, `rustc_codegen_cranelift`, `rustc_codegen_gcc`). Replaced or bypassed by a verified backend or translation validator. |
| **Total (`79` `compiler/*` + `librustdoc`)** | **80** | **942,429** | **715,601** | **100.0%** | (`compiler/*` alone: `79` crates, `891,726` raw lines / `674,439` SLOC; `src/librustdoc`: `50,703` raw / `41,162` SLOC.) |

#### 2.4 Complete 80-Crate Topological Catalog (`412be32a6a189d9a28922beee178bc0abee9d492`)

Columns `In (Trans)` and `Out (Trans)` report direct (and transitive) internal edges within the 80-crate set; for the three `rustc_private` crates (`librustdoc`, `rustc_codegen_cranelift`, `rustc_codegen_gcc`), sysroot `extern crate` edges are listed explicitly in the rightmost column.

| Depth | Crate Path (`package` if different) | Crate Type | Files | Raw Lines | Approx. SLOC | In (Trans) | Out (Trans) | Verification Split | Direct Internal `rustc_*` Dependencies |
| ---: | :--- | :--- | ---: | ---: | ---: | :---: | :---: | :--- | :--- |
| 0 | `src/librustdoc` (`rustdoc`) | `rlib` | 105 | 50,703 | 41,162 | 0 (0) | 0 (0) | Diag / driver / backend | `rustc_private` (30): `rustc_abi`, `rustc_ast`, `rustc_ast_pretty`, `rustc_attr_ir`, `rustc_attr_parsing`, `rustc_data_structures`, ... |
| 0 | `compiler/rustc_arena` | `rlib` | 2 | 984 | 651 | 10 (60) | 0 (0) | Semantic middle / shared | *(leaf)* |
| 0 | `compiler/rustc_codegen_cranelift` | `dylib` | 63 | 20,411 | 16,835 | 0 (0) | 0 (0) | Diag / driver / backend | `rustc_private` (17): `rustc_abi`, `rustc_ast`, `rustc_attr_ir`, `rustc_codegen_ssa`, `rustc_const_eval`, `rustc_data_structures`, ... |
| 0 | `compiler/rustc_codegen_gcc` | `dylib` | 120 | 33,220 | 28,163 | 0 (0) | 0 (0) | Diag / driver / backend | `rustc_private` (18): `rustc_abi`, `rustc_ast`, `rustc_attr_ir`, `rustc_codegen_ssa`, `rustc_data_structures`, `rustc_driver`, ... |
| 0 | `compiler/rustc_error_codes` | `rlib` | 1 | 691 | 527 | 1 (50) | 0 (0) | Diag / driver / backend | *(leaf)* |
| 0 | `compiler/rustc_fs_util` | `rlib` | 1 | 142 | 99 | 7 (44) | 0 (0) | Diag / driver / backend | *(leaf)* |
| 0 | `compiler/rustc_graphviz` | `rlib` | 2 | 1,079 | 579 | 5 (60) | 0 (0) | Diag / driver / backend | *(leaf)* |
| 0 | `compiler/rustc_hashes` | `rlib` | 1 | 131 | 89 | 15 (62) | 0 (0) | Semantic middle / shared | *(leaf)* |
| 0 | `compiler/rustc_index_macros` | `proc-macro` | 2 | 450 | 329 | 1 (61) | 0 (0) | Semantic middle / shared | *(leaf)* |
| 0 | `compiler/rustc_lexer` | `rlib` | 2 | 1,666 | 1,143 | 9 (60) | 0 (0) | Frontend-only | *(leaf)* |
| 0 | `compiler/rustc_llvm` | `rlib` | 10 | 5,120 | 3,977 | 1 (5) | 0 (0) | Diag / driver / backend | *(leaf)* |
| 0 | `compiler/rustc_log` | `rlib` | 1 | 377 | 279 | 1 (3) | 0 (0) | Diag / driver / backend | *(leaf)* |
| 0 | `compiler/rustc_macros` | `proc-macro` | 22 | 4,659 | 3,627 | 50 (61) | 0 (0) | Semantic middle / shared | *(leaf)* |
| 0 | `compiler/rustc_proc_macro` | `rlib` | 0 | 0 | 0 | 4 (11) | 0 (0) | Frontend-only | *(leaf)* |
| 0 | `compiler/rustc_thread_pool` | `rlib` | 34 | 7,745 | 4,668 | 4 (60) | 0 (0) | Diag / driver / backend | *(leaf)* |
| 0 | `compiler/rustc_type_ir_macros` | `proc-macro` | 1 | 483 | 358 | 2 (37) | 0 (0) | Semantic middle / shared | *(leaf)* |
| 0 | `compiler/rustc_windows_rc` | `rlib` | 1 | 137 | 91 | 2 (2) | 0 (0) | Diag / driver / backend | *(leaf)* |
| 1 | `compiler/rustc_parse_format` | `rlib` | 2 | 1,649 | 1,382 | 3 (17) | 1 (1) | Frontend-only | `rustc_lexer` |
| 1 | `compiler/rustc_serialize` | `rlib` | 8 | 2,123 | 1,628 | 24 (61) | 1 (1) | Semantic middle / shared | `rustc_hashes` |
| 2 | `compiler/rustc_index` | `rlib` | 9 | 4,152 | 3,122 | 32 (60) | 3 (4) | Semantic middle / shared | `rustc_index_macros`, `rustc_macros`, `rustc_serialize` |
| 3 | `compiler/rustc_data_structures` | `rlib` | 75 | 15,116 | 10,120 | 51 (59) | 7 (8) | Semantic middle / shared | `rustc_arena`, `rustc_graphviz`, `rustc_hashes`, `rustc_index`, `rustc_macros`, `rustc_serialize`, `rustc_thread_pool` |
| 4 | `compiler/rustc_span` | `rlib` | 18 | 12,585 | 9,366 | 55 (58) | 7 (10) | Semantic middle / shared | `rustc_arena`, `rustc_data_structures`, `rustc_hashes`, `rustc_index`, `rustc_lexer`, `rustc_macros`, `rustc_serialize` |
| 5 | `compiler/rustc_ast_ir` | `rlib` | 2 | 417 | 347 | 3 (53) | 4 (11) | Frontend-only | `rustc_data_structures`, `rustc_macros`, `rustc_serialize`, `rustc_span` |
| 5 | `compiler/rustc_error_messages` | `rlib` | 2 | 459 | 331 | 8 (52) | 4 (11) | Diag / driver / backend | `rustc_data_structures`, `rustc_macros`, `rustc_serialize`, `rustc_span` |
| 5 | `compiler/rustc_feature` | `rlib` | 6 | 2,266 | 1,326 | 15 (41) | 3 (11) | Semantic middle / shared | `rustc_data_structures`, `rustc_macros`, `rustc_span` |
| 5 | `compiler/rustc_hir_id` | `rlib` | 4 | 871 | 589 | 3 (51) | 6 (11) | Frontend-only | `rustc_data_structures`, `rustc_hashes`, `rustc_index`, `rustc_macros`, `rustc_serialize`, `rustc_span` |
| 6 | `compiler/rustc_ast` | `rlib` | 25 | 11,982 | 8,460 | 31 (52) | 6 (12) | Frontend-only | `rustc_ast_ir`, `rustc_data_structures`, `rustc_index`, `rustc_macros`, `rustc_serialize`, `rustc_span` |
| 6 | `compiler/rustc_structures` | `rlib` | 8 | 606 | 485 | 22 (46) | 5 (12) | Semantic middle / shared | `rustc_data_structures`, `rustc_error_messages`, `rustc_macros`, `rustc_serialize`, `rustc_span` |
| 7 | `compiler/rustc_ast_pretty` | `rlib` | 9 | 5,626 | 4,509 | 11 (44) | 3 (13) | Diag / driver / backend | `rustc_ast`, `rustc_lexer`, `rustc_span` |
| 7 | `compiler/rustc_lint_defs` | `rlib` | 2 | 6,883 | 1,659 | 28 (50) | 7 (15) | Frontend-only | `rustc_ast`, `rustc_data_structures`, `rustc_error_messages`, `rustc_hir_id`, `rustc_macros`, `rustc_serialize`, `rustc_span` |
| 8 | `compiler/rustc_errors` | `rlib` | 18 | 7,259 | 5,376 | 33 (49) | 10 (17) | Diag / driver / backend | `rustc_ast`, `rustc_data_structures`, `rustc_error_codes`, `rustc_error_messages`, `rustc_hashes`, `rustc_index`, `rustc_lint_defs`, `rustc_macros`, `rustc_serialize`, `rustc_span` |
| 9 | `compiler/rustc_abi` | `rlib` | 13 | 6,602 | 4,644 | 33 (48) | 8 (18) | Semantic middle / shared | `rustc_data_structures`, `rustc_error_messages`, `rustc_errors`, `rustc_hashes`, `rustc_index`, `rustc_macros`, `rustc_serialize`, `rustc_span` |
| 10 | `compiler/rustc_attr_ir` | `rlib` | 14 | 4,917 | 3,196 | 32 (42) | 10 (21) | Frontend-only | `rustc_abi`, `rustc_ast`, `rustc_ast_pretty`, `rustc_data_structures`, `rustc_error_messages`, `rustc_lint_defs`, `rustc_macros`, `rustc_serialize`, `rustc_span`, `rustc_structures` |
| 10 | `compiler/rustc_target` | `rlib` | 446 | 31,604 | 25,535 | 23 (43) | 8 (21) | Semantic middle / shared | `rustc_abi`, `rustc_data_structures`, `rustc_error_messages`, `rustc_fs_util`, `rustc_macros`, `rustc_serialize`, `rustc_span`, `rustc_structures` |
| 10 | `compiler/rustc_type_ir` | `rlib` | 52 | 20,562 | 14,238 | 3 (36) | 9 (20) | Semantic middle / shared | `rustc_abi`, `rustc_ast_ir`, `rustc_data_structures`, `rustc_error_messages`, `rustc_index`, `rustc_macros`, `rustc_serialize`, `rustc_span`, `rustc_type_ir_macros` |
| 11 | `compiler/rustc_crate_store` | `rlib` | 2 | 275 | 183 | 9 (35) | 8 (22) | Semantic middle / shared | `rustc_abi`, `rustc_attr_ir`, `rustc_data_structures`, `rustc_hir_id`, `rustc_macros`, `rustc_serialize`, `rustc_span`, `rustc_structures` |
| 11 | `compiler/rustc_hir` | `rlib` | 10 | 8,441 | 5,941 | 31 (38) | 14 (24) | Frontend-only | `rustc_abi`, `rustc_arena`, `rustc_ast`, `rustc_attr_ir`, `rustc_data_structures`, `rustc_error_messages`, `rustc_errors`, `rustc_hir_id`, `rustc_index`, `rustc_lint_defs`, `rustc_macros`, `rustc_serialize`, `rustc_span`, `rustc_target` |
| 11 | `compiler/rustc_next_trait_solver` | `rlib` | 25 | 12,856 | 9,561 | 1 (18) | 5 (21) | Frontend-only | `rustc_data_structures`, `rustc_index`, `rustc_macros`, `rustc_type_ir`, `rustc_type_ir_macros` |
| 11 | `compiler/rustc_session` | `rlib` | 20 | 12,530 | 9,652 | 25 (40) | 13 (23) | Semantic middle / shared | `rustc_abi`, `rustc_ast`, `rustc_data_structures`, `rustc_errors`, `rustc_feature`, `rustc_fs_util`, `rustc_hashes`, `rustc_lint_defs`, `rustc_macros`, `rustc_serialize`, `rustc_span`, `rustc_structures`, `rustc_target` |
| 12 | `compiler/rustc_hir_pretty` | `rlib` | 1 | 2,759 | 2,467 | 5 (13) | 6 (25) | Diag / driver / backend | `rustc_abi`, `rustc_ast`, `rustc_ast_pretty`, `rustc_attr_ir`, `rustc_hir`, `rustc_span` |
| 12 | `compiler/rustc_middle` | `rlib` | 139 | 66,574 | 46,012 | 32 (34) | 22 (30) | Semantic middle / shared | `rustc_abi`, `rustc_arena`, `rustc_ast`, `rustc_ast_ir`, `rustc_attr_ir`, `rustc_crate_store`, `rustc_data_structures`, `rustc_errors`, `rustc_feature`, `rustc_graphviz`, `rustc_hashes`, `rustc_hir`, `rustc_index`, `rustc_lint_defs`, `rustc_macros`, `rustc_serialize`, `rustc_session`, `rustc_span`, `rustc_structures`, `rustc_target`, `rustc_thread_pool`, `rustc_type_ir` |
| 12 | `compiler/rustc_parse` | `rlib` | 26 | 33,105 | 26,882 | 5 (17) | 11 (25) | Frontend-only | `rustc_ast`, `rustc_ast_pretty`, `rustc_data_structures`, `rustc_errors`, `rustc_feature`, `rustc_index`, `rustc_lexer`, `rustc_lint_defs`, `rustc_macros`, `rustc_session`, `rustc_span` |
| 13 | `compiler/rustc_attr_parsing` | `rlib` | 66 | 17,292 | 14,398 | 10 (16) | 16 (28) | Frontend-only | `rustc_abi`, `rustc_ast`, `rustc_ast_pretty`, `rustc_attr_ir`, `rustc_data_structures`, `rustc_errors`, `rustc_feature`, `rustc_lexer`, `rustc_lint_defs`, `rustc_macros`, `rustc_parse`, `rustc_parse_format`, `rustc_session`, `rustc_span`, `rustc_structures`, `rustc_target` |
| 13 | `compiler/rustc_incremental` | `rlib` | 12 | 2,671 | 1,854 | 2 (6) | 12 (31) | Semantic middle / shared | `rustc_attr_ir`, `rustc_data_structures`, `rustc_errors`, `rustc_fs_util`, `rustc_graphviz`, `rustc_hashes`, `rustc_hir`, `rustc_macros`, `rustc_middle`, `rustc_serialize`, `rustc_session`, `rustc_span` |
| 13 | `compiler/rustc_infer` | `rlib` | 39 | 13,543 | 9,371 | 10 (18) | 8 (31) | Frontend-only | `rustc_data_structures`, `rustc_errors`, `rustc_hir`, `rustc_index`, `rustc_macros`, `rustc_middle`, `rustc_span`, `rustc_type_ir` |
| 13 | `compiler/rustc_mir_dataflow` | `rlib` | 26 | 7,849 | 5,666 | 4 (7) | 9 (31) | Frontend-only | `rustc_abi`, `rustc_attr_ir`, `rustc_data_structures`, `rustc_errors`, `rustc_graphviz`, `rustc_index`, `rustc_macros`, `rustc_middle`, `rustc_span` |
| 13 | `compiler/rustc_pattern_analysis` | `rlib` | 14 | 6,001 | 3,720 | 1 (5) | 9 (31) | Frontend-only | `rustc_abi`, `rustc_arena`, `rustc_errors`, `rustc_hir`, `rustc_index`, `rustc_lint_defs`, `rustc_macros`, `rustc_middle`, `rustc_span` |
| 13 | `compiler/rustc_public_bridge` | `rlib` | 7 | 1,419 | 1,050 | 2 (4) | 9 (32) | Semantic middle / shared | `rustc_abi`, `rustc_attr_ir`, `rustc_crate_store`, `rustc_data_structures`, `rustc_hir`, `rustc_hir_pretty`, `rustc_middle`, `rustc_span`, `rustc_target` |
| 13 | `compiler/rustc_query_impl` | `rlib` | 9 | 2,689 | 2,027 | 1 (4) | 9 (31) | Semantic middle / shared | `rustc_data_structures`, `rustc_errors`, `rustc_hir`, `rustc_macros`, `rustc_middle`, `rustc_serialize`, `rustc_span`, `rustc_structures`, `rustc_thread_pool` |
| 13 | `compiler/rustc_symbol_mangling` | `rlib` | 6 | 2,356 | 1,650 | 5 (9) | 9 (31) | Semantic middle / shared | `rustc_abi`, `rustc_attr_ir`, `rustc_data_structures`, `rustc_hashes`, `rustc_hir`, `rustc_macros`, `rustc_middle`, `rustc_session`, `rustc_span` |
| 13 | `compiler/rustc_transmute` | `rlib` | 9 | 2,655 | 2,055 | 1 (18) | 5 (31) | Frontend-only | `rustc_abi`, `rustc_attr_ir`, `rustc_data_structures`, `rustc_middle`, `rustc_span` |
| 13 | `compiler/rustc_ty_walk` | `rlib` | 1 | 159 | 136 | 2 (7) | 3 (31) | Frontend-only | `rustc_hir`, `rustc_middle`, `rustc_span` |
| 14 | `compiler/rustc_ast_lowering` | `rlib` | 17 | 14,523 | 11,838 | 2 (5) | 14 (34) | Frontend-only | `rustc_abi`, `rustc_ast`, `rustc_attr_ir`, `rustc_attr_parsing`, `rustc_data_structures`, `rustc_errors`, `rustc_feature`, `rustc_hir`, `rustc_index`, `rustc_macros`, `rustc_middle`, `rustc_session`, `rustc_span`, `rustc_target` |
| 14 | `compiler/rustc_ast_passes` | `rlib` | 5 | 4,512 | 3,846 | 1 (4) | 13 (29) | Frontend-only | `rustc_abi`, `rustc_ast`, `rustc_ast_pretty`, `rustc_attr_ir`, `rustc_attr_parsing`, `rustc_data_structures`, `rustc_errors`, `rustc_feature`, `rustc_lint_defs`, `rustc_macros`, `rustc_session`, `rustc_span`, `rustc_target` |
| 14 | `compiler/rustc_expand` | `rlib` | 19 | 13,654 | 10,674 | 6 (10) | 17 (31) | Frontend-only | `rustc_ast`, `rustc_ast_pretty`, `rustc_attr_ir`, `rustc_attr_parsing`, `rustc_data_structures`, `rustc_errors`, `rustc_feature`, `rustc_hir`, `rustc_lexer`, `rustc_lint_defs`, `rustc_macros`, `rustc_parse`, `rustc_proc_macro`, `rustc_serialize`, `rustc_session`, `rustc_span`, `rustc_structures` |
| 14 | `compiler/rustc_monomorphize` | `rlib` | 12 | 4,914 | 3,507 | 1 (4) | 16 (32) | Semantic middle / shared | `rustc_abi`, `rustc_ast`, `rustc_attr_ir`, `rustc_data_structures`, `rustc_errors`, `rustc_hir`, `rustc_index`, `rustc_lint_defs`, `rustc_macros`, `rustc_middle`, `rustc_serialize`, `rustc_session`, `rustc_span`, `rustc_structures`, `rustc_symbol_mangling`, `rustc_target` |
| 14 | `compiler/rustc_privacy` | `rlib` | 2 | 2,016 | 1,625 | 2 (5) | 10 (32) | Frontend-only | `rustc_ast`, `rustc_attr_ir`, `rustc_data_structures`, `rustc_errors`, `rustc_hir`, `rustc_lint_defs`, `rustc_macros`, `rustc_middle`, `rustc_span`, `rustc_ty_walk` |
| 14 | `compiler/rustc_public` | `rlib` | 29 | 11,531 | 8,935 | 2 (3) | 7 (33) | Semantic middle / shared | `rustc_abi`, `rustc_crate_store`, `rustc_hir`, `rustc_middle`, `rustc_public_bridge`, `rustc_span`, `rustc_target` |
| 14 | `compiler/rustc_trait_selection` | `rlib` | 72 | 51,827 | 40,952 | 13 (17) | 17 (34) | Frontend-only | `rustc_abi`, `rustc_ast`, `rustc_attr_ir`, `rustc_crate_store`, `rustc_data_structures`, `rustc_errors`, `rustc_hir`, `rustc_index`, `rustc_infer`, `rustc_lint_defs`, `rustc_macros`, `rustc_middle`, `rustc_next_trait_solver`, `rustc_session`, `rustc_span`, `rustc_structures`, `rustc_transmute` |
| 15 | `compiler/rustc_borrowck` | `rlib` | 62 | 36,847 | 27,757 | 1 (4) | 16 (36) | Frontend-only | `rustc_abi`, `rustc_attr_ir`, `rustc_data_structures`, `rustc_errors`, `rustc_graphviz`, `rustc_hir`, `rustc_index`, `rustc_infer`, `rustc_lexer`, `rustc_lint_defs`, `rustc_macros`, `rustc_middle`, `rustc_mir_dataflow`, `rustc_session`, `rustc_span`, `rustc_trait_selection` |
| 15 | `compiler/rustc_builtin_macros` | `rlib` | 56 | 14,315 | 11,394 | 1 (4) | 18 (32) | Frontend-only | `rustc_ast`, `rustc_ast_pretty`, `rustc_attr_ir`, `rustc_attr_parsing`, `rustc_data_structures`, `rustc_errors`, `rustc_expand`, `rustc_feature`, `rustc_index`, `rustc_lexer`, `rustc_lint_defs`, `rustc_macros`, `rustc_parse`, `rustc_parse_format`, `rustc_proc_macro`, `rustc_session`, `rustc_span`, `rustc_target` |
| 15 | `compiler/rustc_const_eval` | `rlib` | 45 | 22,729 | 16,863 | 3 (5) | 18 (37) | Semantic middle / shared | `rustc_abi`, `rustc_ast`, `rustc_attr_ir`, `rustc_data_structures`, `rustc_errors`, `rustc_hir`, `rustc_hir_pretty`, `rustc_index`, `rustc_infer`, `rustc_lint_defs`, `rustc_macros`, `rustc_middle`, `rustc_mir_dataflow`, `rustc_session`, `rustc_span`, `rustc_structures`, `rustc_target`, `rustc_trait_selection` |
| 15 | `compiler/rustc_expand_queries` | `rlib` | 2 | 95 | 65 | 1 (4) | 5 (36) | Frontend-only | `rustc_ast`, `rustc_expand`, `rustc_middle`, `rustc_proc_macro`, `rustc_span` |
| 15 | `compiler/rustc_hir_analysis` | `rlib` | 53 | 41,020 | 32,116 | 3 (5) | 18 (35) | Frontend-only | `rustc_abi`, `rustc_arena`, `rustc_ast`, `rustc_attr_ir`, `rustc_data_structures`, `rustc_errors`, `rustc_feature`, `rustc_hir`, `rustc_index`, `rustc_infer`, `rustc_lint_defs`, `rustc_macros`, `rustc_middle`, `rustc_session`, `rustc_span`, `rustc_structures`, `rustc_target`, `rustc_trait_selection` |
| 15 | `compiler/rustc_lint` | `rlib` | 62 | 26,146 | 18,867 | 3 (5) | 22 (39) | Frontend-only | `rustc_abi`, `rustc_ast`, `rustc_ast_pretty`, `rustc_attr_ir`, `rustc_attr_parsing`, `rustc_data_structures`, `rustc_errors`, `rustc_feature`, `rustc_hashes`, `rustc_hir`, `rustc_index`, `rustc_infer`, `rustc_lint_defs`, `rustc_macros`, `rustc_middle`, `rustc_parse_format`, `rustc_session`, `rustc_span`, `rustc_structures`, `rustc_symbol_mangling`, `rustc_target`, `rustc_trait_selection` |
| 15 | `compiler/rustc_metadata` | `rlib` | 17 | 12,578 | 9,604 | 5 (7) | 23 (37) | Semantic middle / shared | `rustc_abi`, `rustc_ast`, `rustc_attr_ir`, `rustc_attr_parsing`, `rustc_crate_store`, `rustc_data_structures`, `rustc_errors`, `rustc_expand`, `rustc_feature`, `rustc_fs_util`, `rustc_hashes`, `rustc_hir`, `rustc_hir_pretty`, `rustc_index`, `rustc_lint_defs`, `rustc_macros`, `rustc_middle`, `rustc_proc_macro`, `rustc_serialize`, `rustc_session`, `rustc_span`, `rustc_structures`, `rustc_target` |
| 15 | `compiler/rustc_mir_build` | `rlib` | 39 | 23,282 | 17,553 | 2 (4) | 15 (36) | Frontend-only | `rustc_abi`, `rustc_arena`, `rustc_ast`, `rustc_attr_ir`, `rustc_data_structures`, `rustc_errors`, `rustc_hir`, `rustc_index`, `rustc_infer`, `rustc_lint_defs`, `rustc_macros`, `rustc_middle`, `rustc_pattern_analysis`, `rustc_span`, `rustc_trait_selection` |
| 15 | `compiler/rustc_passes` | `rlib` | 20 | 8,745 | 7,101 | 1 (4) | 19 (41) | Frontend-only | `rustc_abi`, `rustc_ast`, `rustc_ast_lowering`, `rustc_attr_ir`, `rustc_attr_parsing`, `rustc_data_structures`, `rustc_errors`, `rustc_feature`, `rustc_hir`, `rustc_index`, `rustc_lint_defs`, `rustc_macros`, `rustc_middle`, `rustc_privacy`, `rustc_session`, `rustc_span`, `rustc_structures`, `rustc_target`, `rustc_trait_selection` |
| 15 | `compiler/rustc_sanitizers` | `rlib` | 10 | 2,246 | 1,467 | 1 (5) | 8 (35) | Semantic middle / shared | `rustc_abi`, `rustc_attr_ir`, `rustc_data_structures`, `rustc_hir`, `rustc_middle`, `rustc_span`, `rustc_target`, `rustc_trait_selection` |
| 15 | `compiler/rustc_traits` | `rlib` | 9 | 703 | 562 | 1 (4) | 5 (35) | Frontend-only | `rustc_data_structures`, `rustc_infer`, `rustc_middle`, `rustc_span`, `rustc_trait_selection` |
| 15 | `compiler/rustc_ty_utils` | `rlib` | 16 | 5,460 | 4,304 | 1 (4) | 16 (36) | Semantic middle / shared | `rustc_abi`, `rustc_attr_ir`, `rustc_data_structures`, `rustc_errors`, `rustc_hashes`, `rustc_hir`, `rustc_index`, `rustc_infer`, `rustc_macros`, `rustc_middle`, `rustc_session`, `rustc_span`, `rustc_structures`, `rustc_target`, `rustc_trait_selection`, `rustc_ty_walk` |
| 16 | `compiler/rustc_codegen_ssa` | `rlib` | 57 | 30,971 | 23,078 | 4 (5) | 24 (44) | Semantic middle / shared | `rustc_abi`, `rustc_arena`, `rustc_ast`, `rustc_attr_ir`, `rustc_attr_parsing`, `rustc_crate_store`, `rustc_data_structures`, `rustc_errors`, `rustc_fs_util`, `rustc_hashes`, `rustc_hir`, `rustc_incremental`, `rustc_index`, `rustc_lint_defs`, `rustc_macros`, `rustc_metadata`, `rustc_middle`, `rustc_serialize`, `rustc_session`, `rustc_span`, `rustc_structures`, `rustc_symbol_mangling`, `rustc_target`, `rustc_trait_selection` |
| 16 | `compiler/rustc_hir_typeck` | `rlib` | 40 | 50,633 | 39,563 | 1 (4) | 18 (42) | Frontend-only | `rustc_abi`, `rustc_ast`, `rustc_attr_ir`, `rustc_data_structures`, `rustc_errors`, `rustc_hir`, `rustc_hir_analysis`, `rustc_hir_pretty`, `rustc_index`, `rustc_infer`, `rustc_lint`, `rustc_lint_defs`, `rustc_macros`, `rustc_middle`, `rustc_session`, `rustc_span`, `rustc_target`, `rustc_trait_selection` |
| 16 | `compiler/rustc_mir_transform` | `rlib` | 97 | 36,833 | 27,044 | 1 (4) | 19 (38) | Semantic middle / shared | `rustc_abi`, `rustc_arena`, `rustc_ast`, `rustc_attr_ir`, `rustc_const_eval`, `rustc_data_structures`, `rustc_errors`, `rustc_hir`, `rustc_index`, `rustc_infer`, `rustc_lint_defs`, `rustc_macros`, `rustc_middle`, `rustc_mir_dataflow`, `rustc_session`, `rustc_span`, `rustc_structures`, `rustc_target`, `rustc_trait_selection` |
| 16 | `compiler/rustc_resolve` | `rlib` | 16 | 30,891 | 25,177 | 2 (4) | 19 (38) | Frontend-only | `rustc_arena`, `rustc_ast`, `rustc_ast_pretty`, `rustc_attr_ir`, `rustc_attr_parsing`, `rustc_crate_store`, `rustc_data_structures`, `rustc_errors`, `rustc_expand`, `rustc_feature`, `rustc_hir`, `rustc_index`, `rustc_lint_defs`, `rustc_macros`, `rustc_metadata`, `rustc_middle`, `rustc_session`, `rustc_span`, `rustc_structures` |
| 17 | `compiler/rustc_codegen_llvm` | `rlib` | 59 | 31,929 | 24,627 | 1 (4) | 22 (47) | Diag / driver / backend | `rustc_abi`, `rustc_ast`, `rustc_attr_ir`, `rustc_codegen_ssa`, `rustc_crate_store`, `rustc_data_structures`, `rustc_errors`, `rustc_fs_util`, `rustc_hashes`, `rustc_hir`, `rustc_index`, `rustc_lint_defs`, `rustc_llvm`, `rustc_macros`, `rustc_metadata`, `rustc_middle`, `rustc_sanitizers`, `rustc_session`, `rustc_span`, `rustc_structures`, `rustc_symbol_mangling`, `rustc_target` |
| 18 | `compiler/rustc_interface` | `rlib` | 9 | 4,346 | 3,440 | 1 (3) | 45 (69) | Diag / driver / backend | `rustc_ast`, `rustc_ast_lowering`, `rustc_ast_passes`, `rustc_ast_pretty`, `rustc_attr_ir`, `rustc_attr_parsing`, `rustc_borrowck`, `rustc_builtin_macros`, `rustc_codegen_llvm`, `rustc_codegen_ssa`, `rustc_const_eval`, `rustc_crate_store`, `rustc_data_structures`, `rustc_errors`, `rustc_expand`, `rustc_expand_queries`, `rustc_feature`, `rustc_fs_util`, `rustc_hir`, `rustc_hir_analysis`, `rustc_hir_typeck`, `rustc_incremental`, `rustc_lint`, `rustc_lint_defs`, `rustc_macros`, `rustc_metadata`, `rustc_middle`, `rustc_mir_build`, `rustc_mir_dataflow`, `rustc_mir_transform`, `rustc_monomorphize`, `rustc_parse`, `rustc_passes`, `rustc_privacy`, `rustc_query_impl`, `rustc_resolve`, `rustc_session`, `rustc_span`, `rustc_structures`, `rustc_symbol_mangling`, `rustc_target`, `rustc_thread_pool`, `rustc_trait_selection`, `rustc_traits`, `rustc_ty_utils` |
| 19 | `compiler/rustc_driver_impl` | `rlib` | 8 | 2,727 | 2,072 | 2 (2) | 29 (73) | Diag / driver / backend | `rustc_abi`, `rustc_ast`, `rustc_ast_pretty`, `rustc_codegen_ssa`, `rustc_const_eval`, `rustc_data_structures`, `rustc_errors`, `rustc_expand`, `rustc_feature`, `rustc_hir`, `rustc_hir_analysis`, `rustc_hir_pretty`, `rustc_index`, `rustc_interface`, `rustc_lexer`, `rustc_lint`, `rustc_lint_defs`, `rustc_log`, `rustc_macros`, `rustc_metadata`, `rustc_middle`, `rustc_mir_build`, `rustc_parse`, `rustc_public`, `rustc_resolve`, `rustc_session`, `rustc_span`, `rustc_structures`, `rustc_target` |
| 20 | `compiler/rustc_driver` | `dylib` | 2 | 26 | 19 | 1 (1) | 2 (75) | Diag / driver / backend | `rustc_driver_impl`, `rustc_windows_rc` |
| 21 | `compiler/rustc` (`rustc-main`) | `rlib` | 2 | 79 | 36 | 0 (0) | 6 (76) | Diag / driver / backend | `rustc_codegen_ssa`, `rustc_driver`, `rustc_driver_impl`, `rustc_public`, `rustc_public_bridge`, `rustc_windows_rc` |

---

### 3. `TyCtxt` Query System Modifiers and Complete Crate Provider Map

`Basis: source + execution (compiler/rustc_middle/src/queries.rs:1-2918, compiler/rustc_macros/src/query.rs:1-490, compiler/rustc_middle/src/query/modifiers.rs:1-108, compiler/rustc_interface/src/passes.rs:920-1075)`

#### 3.1 Query Macro Architecture, Modifier Inventory, and `DepKind` Evolution

`compiler/rustc_middle/src/queries.rs` invokes the procedural macro `rustc_macros::rustc_queries!`, which expands into the higher-order macro `rustc_with_all_queries!` (`compiler/rustc_macros/src/query.rs:470-480`) and `define_query_api!` (`queries.rs:2918`). At `412be32a6a189d9a28922beee178bc0abee9d492`, `queries.rs` declares **330 queries** (`+4` over the `326` queries in `1.99.1`) and **8 `non_query` `DepKind`s** (`queries.rs:2868-2916`):
- **Sentinel and control `non_query` nodes (`3`):** `Null` (dense dep-node array decode slot), `Red` (`DepNodeIndex::FOREVER_RED_NODE` singleton always-dirty node), and `SideEffect` (replayable diagnostic/feature-gate side effects).
- **Anonymous task `non_query` nodes (`2`):** `AnonZeroDeps` (`SINGLETON_ZERO_DEPS_ANON_NODE`) and `TraitSelect` (anonymous trait-solving tasks keyed by the hash of their runtime dep-graph reads rather than a query key).
- **Special compilation task `non_query` nodes (`3`):** `CompileCodegenUnit`, `CompileMonoItem` (used by `rustc_codegen_cranelift`), and `Metadata`.

In `compiler/rustc_macros/src/query.rs:138-306` (`QMODLIST`) and `compiler/rustc_middle/src/query/modifiers.rs:11-106`, `rustc_queries!` supports **10 explicit syntax modifiers** plus **1 return-type-inferred modifier** (older `rustc` modifiers `dep_node`, `anon`, and `return_result_from_ensure_ok` were eliminated: every `query` now automatically generates a 1-to-1 `DepKind` variant, anonymous tasks use `non_query`, and `ensure_ok` behavior is inferred directly from `Result<_, ErrorGuaranteed>`):

| Modifier | Count (`/ 330`) | Semantics in `TyCtxt` Caching, Incremental Dep-Graph, and Provider Signatures |
| :--- | ---: | :--- |
| `desc { ... }` | 330 | Mandatory human-readable `format!`-style diagnostic/profiler description closure (`|tcx, key| format!(...)`). |
| `separate_provide_extern` | 119 | Splits dispatch on `CrateNum`: `LOCAL_CRATE` calls `Providers::queries.<name>`, whereas upstream `CrateNum != LOCAL_CRATE` calls `Providers::extern_queries.<name>` (typically decoded on demand from `.rmeta` in `rustc_metadata`). Suppresses disk caching for extern keys. |
| `cache_on_disk` | 58 | Serializes query return values into the incremental compilation on-disk cache (`QueryResultOnDiskCache`) so green dep-nodes reload results across sessions without re-executing providers. |
| `arena_cache` | 53 | Provider returns owned `T` (or `Option<T>` / `Result<T, ErrorGuaranteed>`), which query plumbing allocates into `tcx.arena` so `tcx.<query>(key)` returns `Copy` `&'tcx T`. |
| `eval_always` | 38 | Skips fine-grained dependency tracking and treats the node as unconditionally dirty (`Red`) across incremental sessions while still memoizing the result in memory for the current session. Cannot be combined with `feedable` (`query.rs:454-460`). |
| `feedable` | 27 | Generates `TyCtxtFeed::<'tcx, Key>::<query>(value)` so an earlier pass or enclosing query can eagerly populate the memoization table (inheriting the feeder's dep-node dependencies) without waiting for on-demand provider execution. |
| `returns_error_guaranteed` *(inferred)* | 23 | Automatically set by `returns_error_guaranteed(&query.return_ty)` (`query.rs:226-243`) whenever the return type matches `Result<_, ErrorGuaranteed>`; makes `tcx.ensure_ok().<query>(key)` return `Result<(), ErrorGuaranteed>` instead of `()`. |
| `no_hash` | 10 | Skips `StableHasher` fingerprinting of the query return value during incremental verification; recomputing the query unconditionally marks dependents dirty. |
| `handle_cycle_error` | 5 | Routes query-cycle recovery through a custom handler `rustc_query_impl::handle_cycle_error::<name>` instead of halting compilation with a fatal cycle diagnostic. |
| `depth_limit` | 2 | Enforces `sess.recursion_limit()` on nested query stack frames to prevent host stack overflow. |
| `no_force` | 2 | Prevents incremental green-marking from forcing the dep-node via fingerprint recovery, preserving full call stacks for custom cycle handlers. |

#### 3.2 Four-Way Dispatch Partition of All 330 Queries

Cross-referencing `queries.rs` against every `Providers`, `ExternProviders`, and `TyCtxtFeed` assignment across `compiler/` and `src/librustdoc` partitions all **330 queries** with zero unaccounted entries:
1. **207 local-only provided queries:** Registered in `Providers::queries` across the crates below (invoked either on `LOCAL_CRATE` items, crate-unit `()`, or crate-agnostic interned keys such as `Ty<'tcx>` / `PseudoCanonicalInput<'tcx, ...>`).
2. **93 dual local + extern provided queries:** Carry `separate_provide_extern` and register both a local `Providers::queries.<q>` implementation (computing from HIR/THIR/MIR for `LOCAL_CRATE`) and an `ExternProviders::<q>` implementation (`91` in `rustc_metadata` and `2` in `rustc_codegen_ssa`).
3. **23 extern-only `separate_provide_extern` queries:** Carry `separate_provide_extern` and register **only** an `ExternProviders` implementation in `rustc_metadata/src/rmeta/decoder/cstore_impl.rs`, leaving `Providers::queries.<q>` as the default panic stub (`default_query`) because local callers either assert `cnum != LOCAL_CRATE` or use a distinct local mechanism (for example, `tcx.module_children_local(local_id)` vs `tcx.module_children(extern_did)`, or HIR attribute maps vs `tcx.attrs_for_def(extern_did)`). The 23 extern-only queries are: `attrs_for_def`, `crate_dep_kind`, `crate_extern_paths`, `crate_host_hash`, `default_field`, `defined_lang_items`, `dylib_dependency_formats`, `extern_crate`, `extra_filename`, `impl_parent`, `implementations_of_trait`, `is_no_builtins`, `is_profiler_runtime`, `missing_extern_crate_item`, `missing_lang_items`, `module_children`, `num_extern_def_ids`, `panic_in_drop_strategy`, `rendered_const`, `symbol_mangling_version`, `upstream_monomorphizations_for`, `used_crate_source`, and `used_crate_source_flags`.
4. **7 `TyCtxtFeed`-only local queries:** Have no local `Providers` function because they are eagerly fed during session/HIR setup before any consumer runs: `crate_for_resolver`, `crate_name`, `features_query`, `limits`, and `output_filenames` (fed in `rustc_interface::passes::create_and_enter_global_ctxt`, `passes.rs:1066-1071`), plus `def_kind` and `visibility` (fed during name resolution and HIR construction in `rustc_resolve` and `rustc_middle`). Three of the seven (`crate_name`, `def_kind`, `visibility`) also carry `separate_provide_extern` (`93 + 23 + 3 = 119` total `separate_provide_extern` queries), with `rustc_metadata` supplying their `ExternProviders`.

#### 3.3 Complete Crate-to-Provider Registration Map (`DEFAULT_QUERY_PROVIDERS` and Overrides)

`compiler/rustc_interface/src/passes.rs:920-956` constructs `DEFAULT_QUERY_PROVIDERS` by combining inline `rustc_interface` closures with `provide(...)` functions across compiler crates (`rustc_driver_impl`, `rustc_parse_format`, and `librustdoc` register additional/override providers when active). Note that `6` queries have conditional or multi-crate override assignments (for instance, `librustdoc` overrides doc-specific queries via `Config::override_queries`), bringing the sum of per-crate local assignments across the **24 provider crates** to `306` over the `300` distinct locally provided queries:

| Provider Crate | Local Queries Provided | Extern Queries Provided | Representative Queries Registered |
| :--- | ---: | ---: | :--- |
| `rustc_metadata` | 18 | 117 | `alloc_error_handler_kind`, `allocator_kind`, `crate_name_with_rename`, `crates`, `dependency_formats`, `doc_link_resolutions` |
| `rustc_hir_analysis` | 64 | 0 | `adt_async_destructor`, `adt_def`, `adt_destructor`, `anon_const_kind`, `check_coroutine_obligations`, `check_potentially_region_dependent_goals` |
| `rustc_ty_utils` | 40 | 0 | `adt_async_drop_tys`, `adt_drop_tys`, `adt_significant_drop_tys`, `adt_sizedness_constraint`, `associated_item`, `associated_item_def_ids` |
| `rustc_middle` | 33 | 0 | `all_local_trait_impls`, `closure_typeinfo`, `crate_hash`, `def_ident_span`, `def_span`, `doc_notable_trait` |
| `rustc_mir_transform` | 23 | 0 | `check_liveness`, `coroutine_by_move_body_def_id`, `coverage_attr_on`, `coverage_codegen_info`, `cross_crate_inlinable`, `deduced_param_attrs` |
| `rustc_passes` | 23 | 0 | `all_canonical_symbols`, `all_diagnostic_items`, `all_fake_doc_items`, `canonical_symbols`, `check_externally_implementable_items`, `check_mod_attrs` |
| `rustc_codegen_ssa` | 16 | 2 | `all_rust_target_features`, `asm_target_features`, `codegen_fn_attrs`, `exported_generic_symbols`, `exported_non_generic_symbols`, `implied_target_features` |
| `rustc_trait_selection` | 16 | 0 | `args_known_to_outlive_alias_params`, `dyn_compatibility_violations`, `evaluate_root_goal_for_proof_tree_raw`, `first_method_vtable_slot`, `generics_require_sized_self`, `hir_owner` |
| `rustc_traits` | 16 | 0 | `adt_dtorck_constraint`, `codegen_select_candidate`, `coroutine_hidden_types`, `dropck_outlives`, `evaluate_obligation`, `implied_outlives_bounds` |
| `rustc_const_eval` | 9 | 0 | `check_validity_requirement`, `constness`, `eval_static_initializer`, `eval_to_allocation_raw`, `eval_to_const_value_raw`, `eval_to_valtree` |
| `rustc_interface` | 8 | 0 | `analysis`, `early_lint_checks`, `env_var_os`, `get_lang_items`, `proc_macro_decls_static`, `resolutions` |
| `rustc_lint` | 6 | 0 | `check_expectations`, `clashing_extern_declarations`, `lint_expectations`, `lint_mod`, `shallow_lint_levels_on`, `skippable_lints` |
| `rustc_mir_build` | 6 | 0 | `check_match`, `check_tail_calls`, `check_unsafety`, `closure_saved_names_of_captured_variables`, `lit_to_const`, `thir_body` |
| `rustc_monomorphize` | 6 | 0 | `check_mono_item`, `codegen_unit`, `collect_and_partition_mono_items`, `is_codegened_item`, `items_of_instance`, `size_estimate` |
| `rustc_hir_typeck` | 5 | 0 | `check_offloads`, `check_transmutes`, `method_autoderef_steps`, `typeck_root`, `used_trait_imports` |
| `librustdoc` | 3 | 0 | `lint_mod`, `typeck_root`, `used_trait_imports` |
| `rustc_ast_lowering` | 3 | 0 | `index_ast`, `lower_to_hir`, `resolve_type_relative_delegations` |
| `rustc_privacy` | 3 | 0 | `check_mod_privacy`, `check_private_in_public`, `effective_visibilities` |
| `rustc_borrowck` | 2 | 0 | `mir_borrowck`, `mir_borrowck_implied_outlives_bounds` |
| `rustc_resolve` | 2 | 0 | `registered_attr_tools`, `registered_lint_tools` |
| `rustc_driver_impl` | 1 | 0 | `trimmed_def_paths` |
| `rustc_expand_queries` | 1 | 0 | `derive_macro_expansion` |
| `rustc_parse_format` | 1 | 0 | `ty_span` |
| `rustc_symbol_mangling` | 1 | 0 | `symbol_name` |

---

### 4. Complete Census of All 24 `library/` Entries, Façade Shims, and Unstable Coupling

`Basis: source + execution (library/Cargo.toml, library/*/Cargo.toml, library/rustc-std-workspace-core/README.md:1-38, support/rust_repo_inventory.json)`

#### 4.1 All 24 Non-File Entries Under `library/` (`51` `Cargo.toml` Manifests)

Alongside `library/Cargo.toml` and `library/Cargo.lock`, `library/` contains **24 non-file entries** (`1,125,313` raw source lines / **794,386 SLOC** across `.rs`/`.c`/`.S` files): **22 Cargo crate trees** (`50` inner `Cargo.toml` files + `library/Cargo.toml` = `51` `Cargo.toml`s), **1 Git submodule** (`library/backtrace`), and **1 non-Cargo source directory** (`library/rtstartup`, containing `rbegin.rs` and `rend.rs` compiled directly via `rustc --emit=obj` by `compile::StartupObjects` in `src/bootstrap/src/core/build_steps/compile.rs:887-969` for `*-pc-windows-gnu` targets).

| `library/` Path | Entry Kind | `Cargo.toml`s | Source Files | Raw Lines | Approx. SLOC | `#![feature]` Count | In-Tree `path` Dependencies | `rustc-dep-of-std` Crates.io Deps | Role in Standard Library & Sysroot |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | :--- | :--- | :--- |
| `library/alloc` | `crate_tree` | 1 | 97 | 70,010 | 34,359 | 181 | `compiler_builtins`, `core` | — | Heap allocation, smart pointers (`Box`, `Rc`, `Arc`), and collections (`Vec`, `String`, `BTreeMap`) |
| `library/alloctests` | `crate_tree` | 1 | 63 | 24,902 | 19,764 | 92 | — | — | Standalone unit/integration test crate for `alloc` (decoupled to avoid dev-dep cycles) |
| `library/backtrace` | `submodule` | 0 | 0 | 0 | 0 | 0 | — | — | Git submodule (`rust-lang/backtrace-rs`) included into `std::backtrace` via `#[path]` |
| `library/compiler-builtins` | `crate_tree` | 15 | 328 | 56,510 | 42,123 | 17 | `compiler_builtins`, `core`, `panic-handler` | — | Software float/int intrinsics (`__muloti4`, `__aeabi_*`) and pure-Rust `libm` (`15` `Cargo.toml`s) |
| `library/core` | `crate_tree` | 1 | 295 | 178,134 | 75,621 | 271 | — | — | Dependency-free language primitives, traits, slices, iterators, atomics, and `316` `#[rustc_intrinsic]`s |
| `library/coretests` | `crate_tree` | 1 | 181 | 43,269 | 36,340 | 135 | — | — | Standalone unit/integration test crate for `core` (`181` files) |
| `library/hashbrown` | `crate_tree` | 1 | 39 | 25,285 | 12,515 | 0 | — | — | In-tree SwissTable implementation backing `std::collections::{HashMap, HashSet}` |
| `library/panic_abort` | `crate_tree` | 1 | 3 | 124 | 90 | 4 | `alloc`, `core` | — | `__rust_start_panic` implementation that traps/aborts immediately (`-Cpanic=abort`) |
| `library/panic_unwind` | `crate_tree` | 1 | 5 | 549 | 273 | 6 | `alloc`, `core`, `unwind` | — | Stack-unwinding panic runtime supporting Itanium DWARF, SEH, Win64, and Emscripten |
| `library/portable-simd` | `crate_tree` | 4 | 80 | 10,697 | 7,291 | 12 | `core_simd`, `std_float`, `test_helpers` | — | Experimental `core::simd` (`core_simd`) and `std::simd` (`std_float`) workspace (`4` `Cargo.toml`s) |
| `library/proc_macro` | `crate_tree` | 1 | 17 | 5,083 | 3,630 | 11 | `core`, `std` | `rustc-literal-escaper` | Host-side procedural macro token-stream API and client/server RPC bridge |
| `library/profiler_builtins` | `crate_tree` | 1 | 2 | 130 | 100 | 3 | — | — | Compiles LLVM `InstrProfiling` C runtime into `libprofiler_builtins.rlib` for `-Cinstrument-coverage` |
| `library/rtstartup` | `non_cargo_dir` | 0 | 2 | 155 | 90 | 3 | — | — | Non-Cargo Windows GNU CRT startup objects (`rbegin.rs`, `rend.rs`) built by `StartupObjects` |
| `library/rustc-std-workspace-alloc` | `crate_tree` | 1 | 1 | 9 | 4 | 1 | `alloc` | — | `[patch.crates-io]` façade re-exporting in-tree `alloc` for `rustc-dep-of-std` crates |
| `library/rustc-std-workspace-core` | `crate_tree` | 1 | 1 | 8 | 4 | 1 | `compiler_builtins`, `core` | — | `[patch.crates-io]` façade (`#![no_core]`) re-exporting `core` and pulling in `compiler_builtins` |
| `library/rustc-std-workspace-std` | `crate_tree` | 1 | 1 | 2 | 2 | 1 | `std` | — | `[patch.crates-io]` façade re-exporting in-tree `std` for `rustc-dep-of-std` crates |
| `library/std` | `crate_tree` | 1 | 706 | 167,154 | 100,590 | 210 | `alloc`, `core`, `panic_abort`, `panic_unwind`, `std_detect`, `unwind`, `windows-link` | `cfg-if`, `dlmalloc`, `fortanix-sgx-abi`, `hashbrown`, `hermit-abi` (+9) | OS abstractions, threads, I/O, networking, process, sync, and platform PAL modules |
| `library/std_detect` | `crate_tree` | 1 | 44 | 5,291 | 3,501 | 10 | — | — | Runtime CPU feature detection (`is_x86_feature_detected!`, `is_aarch64_feature_detected!`) |
| `library/stdarch` | `crate_tree` | 12 | 215 | 529,901 | 451,525 | 43 | `assert-instr-macro`, `core_arch`, `simd-test-macro`, `stdarch-gen-common`, `stdarch-test` | — | Architecture-specific SIMD intrinsics (`core::arch`, `8,387+` `llvm.*` bindings, `12` `Cargo.toml`s) |
| `library/sysroot` | `crate_tree` | 1 | 1 | 1 | 0 | 0 | `proc_macro`, `profiler_builtins`, `std`, `test` | — | Dummy Cargo root aggregator pulling `{std, test, proc_macro, profiler_builtins}` into one build |
| `library/test` | `crate_tree` | 1 | 31 | 7,427 | 6,047 | 8 | `core`, `std` | `getopts` | Built-in `#[test]` / `#[bench]` runner harness linked by `rustc --test` |
| `library/unwind` | `crate_tree` | 1 | 4 | 618 | 476 | 2 | `core` | `libc`, `unwinding` | Platform libunwind / `libgcc_s` / `unwinding` FFI bindings consumed by `panic_unwind` |
| `library/windows-sys` | `crate_tree` | 1 | 1 | 1 | 1 | 0 | — | — | In-tree trimmed `windows-sys` bindings overriding crates.io via `[patch.crates-io]` |
| `library/windows_link` | `crate_tree` | 1 | 1 | 53 | 40 | 2 | — | — | `#[link(.., kind = "raw-dylib")]` macro avoiding import-library requirements on Windows |

#### 4.2 How `rustc-std-workspace-{core,alloc,std}` Breaks Circular Crates.io Dependencies

External crates published on crates.io (`libc`, `hashbrown`, `cfg-if`, `dlmalloc`, `rustc-demangle`, `unwinding`, `getopts`, `wasip1`, `wasip2`, `hermit-abi`, `fortanix-sgx-abi`, `moto-rt`, `r-efi`) are ordinary Rust libraries that implicitly depend on `core` (and sometimes `alloc` or `std`), yet `library/std`, `library/unwind`, `library/proc_macro`, and `library/test` depend on those crates.io packages *while building the standard library itself*. `rust-lang/rust` resolves this cycle through a **two-directory shim pair** (`library/rustc-std-workspace-core/README.md:1-38`):

1. **Published crates.io stubs (`src/rustc-std-workspace/rustc-std-workspace-{core,alloc,std}`, `v1.0.1`, root `Cargo.toml:6-8`):** Empty 0-line crates published to crates.io. Upstream crates like `libc` and `hashbrown` define an optional feature:
   ```toml
   [dependencies]
   core = { version = "1.0.0", optional = true, package = "rustc-std-workspace-core" }
   compiler_builtins = { version = "0.1", optional = true }
   [features]
   rustc-dep-of-std = ["dep:core", "dep:compiler_builtins", ...]
   ```
   When Cargo compiles `libc` with `--features rustc-dep-of-std` (and `#![no_core]` or `#![no_std]`), Cargo passes `--extern core=.../librustc_std_workspace_core-XXXX.rlib`, satisfying `rustc`'s injected `extern crate core;`.
2. **In-tree `[patch.crates-io]` overrides (`library/Cargo.toml:83-90` -> `library/rustc-std-workspace-{core,alloc,std}`, `v1.99.0`):** `library/Cargo.toml` patches all three crates.io names to the local `library/rustc-std-workspace-*` crates. `library/rustc-std-workspace-core/lib.rs` is `#![feature(no_core)] #![no_core] pub use core::*; use compiler_builtins as _;`, using `cargo-features = ["public-dependency"]` (`public = true`) to re-export the in-tree `library/core` and unconditionally splice `compiler_builtins` into every downstream crate's dependency graph.
3. **`library/sysroot` single-invocation aggregation (`library/sysroot/Cargo.toml:1-39`):** Rather than invoking `cargo build` separately for `core`, `alloc`, `std`, `test`, and `proc_macro` (which would risk duplicate transitive dependency hashes), `bootstrap`'s `compile::Std` step builds `-p sysroot`, whose dummy `Cargo.toml` depends on `{std, test, proc_macro, profiler_builtins (optional)}` in one unified Cargo unit graph.
4. **Unstable feature & `#![staged_api]` coupling:** Standard-library crates activate hundreds of internal `#![feature(...)]` gates (`271` distinct features in `core`, `210` in `std`, `181` in `alloc`, including `rustc_attrs`, `intrinsics`, `no_core`, `staged_api`, `allow_internal_unstable`, and `lang_items`). To compile them on the `stage 0` `beta` compiler—and to ensure third-party crates linked into the sysroot cannot be imported by end users as stable public dependencies—`bootstrap` sets both `RUSTC_BOOTSTRAP=1` (`cargo.rs:1214`) and `RUSTC_FORCE_UNSTABLE=1` (`cargo.rs:1150`), causing the `bootstrap` `rustc` shim (`src/bootstrap/src/bin/rustc.rs:180-182`) to append `-Zforce-unstable-if-unmarked` to every `Mode::Std`, `Mode::Rustc`, and `Mode::Codegen` compilation.

---

### 5. Complete Census of All 47 `src/tools/` Entries, 13 Git Submodules, and Subtree-Synced Components

`Basis: source + execution (.gitmodules, triagebot.toml, src/tools/*, src/bootstrap/src/core/build_steps/tool.rs, support/rust_repo_inventory.json)`

#### 5.1 Complete 47-Entry `src/tools/` Catalog

`src/tools/` contains **47 immediate entries** (`12,299` tracked blobs, `1,188,360` raw code lines / **925,358 SLOC**): **42 in-tree directories**, **3 Git submodules** (`cargo`, `enzyme`, `rustc-perf`), and **2 standalone executable scripts** (`cherry-pick.sh`, `publish_toolstate.py`). Across `src/bootstrap/src/core/builder/mod.rs` and `tool.rs`, in-tree Rust tools compile under one of four `Mode`s:
- `Mode::ToolBootstrap`: Built with the `stage 0` snapshot compiler against the `stage 0` sysroot (`-Zallow-features=binary-dep-depinfo,proc_macro_span,...`, `cargo.rs:935-953`) so host orchestration tools (`compiletest`, `tidy`, `rustbook`, `opt-dist`, `build-manifest`) never wait for `stage 1` `rustc` or `std`.
- `Mode::ToolTarget`: Built for a target sysroot (`lld-wrapper`, `llvm-bitcode-linker`, `wasm-component-ld`, `remote-test-server`).
- `Mode::ToolStd`: Built with the newly assembled stage-N compiler using only stable/allowed `std` (`test-float-parse`).
- `Mode::ToolRustcPrivate`: Built with stage-N `rustc` and `-L` pointing to stage-N `rustc_libdir` + `llvm_libdir` (`cargo.rs:1256-1270`), enabling `#![feature(rustc_private)]` (`rustdoc`, `clippy`, `miri`, `rustfmt`, `rust-analyzer`, `error_index_generator`, `unstable-book-gen`).

| `src/tools/` Entry | Kind | Role Category | `Cargo.toml`s | Code Files | Raw Lines | Approx. SLOC | `bootstrap` `Mode` & Functional Summary |
| :--- | :--- | :--- | ---: | ---: | ---: | ---: | :--- |
| `src/tools/build-manifest` | `directory` | `release_and_dist` | 1 | 5 | 1,186 | 979 | `Mode::ToolBootstrap`; emits channel release manifests (`channel-rust-*.toml`) with SHA-256 digests |
| `src/tools/bump-stage0` | `directory` | `build_and_bootstrap` | 1 | 1 | 311 | 252 | `Mode::ToolBootstrap`; updates `src/stage0` compiler/rustfmt pins and tarball checksums |
| `src/tools/cargo` | `submodule` | `submodule` | 0 | 0 | 0 | 0 | Git submodule (`rust-lang/cargo`); built via `tool::Cargo` (`Mode::ToolRustcPrivate` / `ToolStd`) |
| `src/tools/cargotest` | `directory` | `test_harness` | 1 | 1 | 226 | 188 | `Mode::ToolBootstrap`; drives integration smoke tests over external Cargo repositories |
| `src/tools/cherry-pick.sh` | `script` | `standalone_script` | 0 | 1 | 34 | 29 | Standalone helper script for backporting commits cleanly |
| `src/tools/clippy` | `directory` | `linter_formatter_ide_subtree` | 71 | 2,392 | 301,806 | 213,999 | Subtree (`rust-lang/rust-clippy`); `Mode::ToolRustcPrivate` linter (`clippy-driver` + `cargo-clippy`) |
| `src/tools/collect-license-metadata` | `directory` | `tidy_and_compliance` | 1 | 6 | 769 | 585 | `Mode::ToolBootstrap`; scans `REUSE.toml` to verify/regenerate `license-metadata.json` |
| `src/tools/compiletest` | `directory` | `test_harness` | 1 | 54 | 15,949 | 11,823 | `Mode::ToolBootstrap`; orchestrates all 22 `tests/*` compiler and rustdoc test suites |
| `src/tools/coverage-dump` | `directory` | `test_harness` | 1 | 8 | 803 | 604 | `Mode::ToolBootstrap`; decodes `__llvm_covmap` sections in `coverage-map` tests |
| `src/tools/enzyme` | `submodule` | `submodule` | 0 | 0 | 0 | 0 | Git submodule (`rust-lang/enzyme`); LLVM automatic-differentiation plugin built by `llvm::Enzyme` |
| `src/tools/error_index_generator` | `directory` | `documentation` | 1 | 3 | 222 | 183 | `Mode::ToolRustcPrivate`; renders HTML compiler error-code index (`E0001`..) |
| `src/tools/features-status-dump` | `directory` | `documentation` | 1 | 1 | 54 | 44 | `Mode::ToolBootstrap`; exports structured JSON of all language/library feature gates |
| `src/tools/generate-copyright` | `directory` | `tidy_and_compliance` | 1 | 2 | 392 | 303 | `Mode::ToolBootstrap`; builds distribution copyright notices from license metadata |
| `src/tools/generate-windows-sys` | `directory` | `build_and_bootstrap` | 1 | 1 | 68 | 58 | `Mode::ToolBootstrap`; regenerates minimal `library/windows-sys` bindings |
| `src/tools/html-checker` | `directory` | `test_harness` | 1 | 1 | 128 | 103 | `Mode::ToolBootstrap`; validates HTML output structure for `rustdoc` tests |
| `src/tools/jsondocck` | `directory` | `test_harness` | 1 | 5 | 615 | 479 | `Mode::ToolBootstrap`; verifies `//@ has` / `//@ is` queries over `rustdoc-json` output |
| `src/tools/jsondoclint` | `directory` | `test_harness` | 1 | 6 | 1,387 | 1,217 | `Mode::ToolBootstrap`; checks `rustdoc` JSON output referential integrity |
| `src/tools/libcxx-version` | `directory` | `build_and_bootstrap` | 0 | 1 | 26 | 12 | C++ probe compiled by `tool::LibcxxVersionTool` to detect host `libc++` / `libstdc++` version |
| `src/tools/linkchecker` | `directory` | `documentation` | 1 | 3 | 989 | 770 | `Mode::ToolBootstrap`; validates internal hyperlinks across generated HTML docs |
| `src/tools/lint-docs` | `directory` | `documentation` | 1 | 3 | 971 | 834 | `Mode::ToolBootstrap`; extracts lint documentation into the `rustc` book |
| `src/tools/lld-wrapper` | `directory` | `linker_and_binary_wrapper` | 1 | 1 | 111 | 76 | `Mode::ToolTarget`; thin binary (`rust-lld` flavor selector) copied into target sysroot `bin/gcc-ld/` |
| `src/tools/llvm-bitcode-linker` | `directory` | `linker_and_binary_wrapper` | 1 | 5 | 348 | 257 | `Mode::ToolTarget`; PTX/GPU bitcode linker shipped in `lib/rustlib/<host>/bin/self-contained/` |
| `src/tools/miri` | `directory` | `linter_formatter_ide_subtree` | 28 | 1,497 | 135,340 | 96,344 | Subtree (`rust-lang/miri`); `Mode::ToolRustcPrivate` undefined-behavior interpreter (`miri` + `cargo-miri`) |
| `src/tools/miropt-test-tools` | `directory` | `test_harness` | 1 | 1 | 135 | 113 | `Mode::ToolBootstrap`; shared parser for `tests/mir-opt` pass dump specifications |
| `src/tools/nix-dev-shell` | `directory` | `build_and_bootstrap` | 0 | 1 | 50 | 33 | Nix flake/shell configuration for contributor dev environments |
| `src/tools/opt-dist` | `directory` | `release_and_dist` | 1 | 11 | 2,202 | 1,681 | `Mode::ToolBootstrap`; PGO + BOLT instrumented training orchestrator for Linux/Windows CI releases |
| `src/tools/publish_toolstate.py` | `script` | `standalone_script` | 0 | 1 | 325 | 260 | Standalone Python CI script updating external `rust-toolstate` repository records |
| `src/tools/remote-test-client` | `directory` | `test_harness` | 1 | 2 | 475 | 389 | `Mode::ToolBootstrap`; host client shipping test binaries to QEMU/Android/remote targets |
| `src/tools/remote-test-server` | `directory` | `test_harness` | 1 | 1 | 413 | 303 | `Mode::ToolTarget`; target daemon executing `compiletest` binaries over TCP |
| `src/tools/replace-version-placeholder` | `directory` | `release_and_dist` | 1 | 1 | 36 | 31 | `Mode::ToolBootstrap`; substitutes `CURRENT_RUSTC_VERSION` in stability attributes for releases |
| `src/tools/run-make-support` | `directory` | `test_harness` | 1 | 33 | 4,203 | 2,921 | Library (`librun_make_support.rlib`) linked by `rmake.rs` recipes in `run-make` suites |
| `src/tools/rust-analyzer` | `directory` | `linter_formatter_ide_subtree` | 50 | 1,513 | 596,238 | 497,213 | Subtree (`rust-lang/rust-analyzer`); `Mode::ToolRustcPrivate` LSP server + `rust-analyzer-proc-macro-srv` |
| `src/tools/rust-installer` | `directory` | `release_and_dist` | 1 | 14 | 3,409 | 2,717 | `Mode::ToolBootstrap`; packages `dist` tarballs with `install.sh` manifests |
| `src/tools/rustbook` | `directory` | `documentation` | 1 | 1 | 186 | 144 | `Mode::ToolBootstrap`; `mdbook` wrapper rendering The Book, Reference, Nomicon, and `rustc` books |
| `src/tools/rustc-perf` | `submodule` | `submodule` | 0 | 0 | 0 | 0 | Git submodule (`rust-lang/rustc-perf`); compiler benchmark suite used by `opt-dist` PGO and `./x perf` |
| `src/tools/rustdoc-gui-test` | `directory` | `test_harness` | 1 | 2 | 190 | 161 | `Mode::ToolBootstrap`; Puppeteer/browser-ui-test runner for `tests/rustdoc-gui` |
| `src/tools/rustdoc-js` | `directory` | `test_harness` | 0 | 2 | 760 | 691 | Node.js search-engine tester scripts for `tests/rustdoc-js` and `tests/rustdoc-js-std` |
| `src/tools/rustdoc-themes` | `directory` | `documentation` | 1 | 1 | 62 | 56 | `Mode::ToolRustcPrivate`; validates CSS theme parity for `rustdoc` |
| `src/tools/rustdoc` | `directory` | `documentation` | 1 | 1 | 13 | 7 | `Mode::ToolRustcPrivate`; binary wrapper (`src/tools/rustdoc/main.rs`) calling `rustdoc::main` in `src/librustdoc` |
| `src/tools/rustfmt` | `directory` | `linter_formatter_ide_subtree` | 20 | 2,072 | 104,013 | 78,825 | Subtree (`rust-lang/rustfmt`); `Mode::ToolRustcPrivate` code formatter (`rustfmt` + `cargo-fmt`) |
| `src/tools/test-float-parse` | `directory` | `test_harness` | 1 | 16 | 2,316 | 1,682 | `Mode::ToolStd`; exhaustive/randomized float-parsing verifier for `core::str::dec2flt` |
| `src/tools/tidy` | `directory` | `tidy_and_compliance` | 1 | 46 | 9,270 | 7,277 | `Mode::ToolBootstrap`; enforces style, license, dependency allowlist (`deps.rs`), and alphabetical gates |
| `src/tools/tier-check` | `directory` | `tidy_and_compliance` | 1 | 1 | 70 | 59 | `Mode::ToolBootstrap`; verifies target-tier documentation matches `rustc_target::spec` |
| `src/tools/unicode-table-generator` | `directory` | `build_and_bootstrap` | 1 | 8 | 1,911 | 1,372 | `Mode::ToolBootstrap`; generates compact UTF-8 property lookup tables for `library/core/src/unicode` |
| `src/tools/unstable-book-gen` | `directory` | `documentation` | 1 | 1 | 203 | 177 | `Mode::ToolRustcPrivate`; generates the Unstable Book from compiler/library feature gates |
| `src/tools/wasm-component-ld` | `directory` | `linker_and_binary_wrapper` | 1 | 1 | 9 | 1 | `Mode::ToolTarget`; WebAssembly Component Model linker wrapper for `wasm32-wasip2` |
| `src/tools/x` | `directory` | `build_and_bootstrap` | 1 | 1 | 136 | 106 | `Mode::ToolBootstrap`; optional `cargo install --path src/tools/x` wrapper locating repo root `./x` |

#### 5.2 All 13 Git Submodules (`160000` Gitlinks) and Subtree-Synced Repositories

At `412be32a6a189d9a28922beee178bc0abee9d492`, `.gitmodules` and the Git tree contain **13 submodules** (all marked `shallow = true` in `.gitmodules`), up from `12` in `1.99.1` due to the addition of `src/tpde`:

| Submodule Path | Upstream GitHub Repository | Pinned Commit at `412be32a6a18` | `.gitmodules` Branch | Delta vs. `1.99.1` (`58cf8f9c35b3`) |
| :--- | :--- | :--- | :--- | :--- |
| `library/backtrace` | `rust-lang/backtrace-rs` | `d902726a1dcdc1e1c66f73d1162181b5423c645b` | — | d902726a1dcdc1e1c66f73d1162181b5423c645b (unchanged) |
| `src/doc/book` | `rust-lang/book` | `2771df165f092a4fbb9f46b5b2e7450f19010adb` | — | advanced since `1.99.1` |
| `src/doc/edition-guide` | `rust-lang/edition-guide` | `ab8544aeed7b792984366aa122ac19bd47ad9a2f` | — | advanced since `1.99.1` |
| `src/doc/embedded-book` | `rust-embedded/book` | `637b4a0244e16ec391a60184ae0c86b550ffc24b` | — | advanced since `1.99.1` |
| `src/doc/nomicon` | `rust-lang/nomicon` | `b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6` | — | advanced since `1.99.1` |
| `src/doc/reference` | `rust-lang/reference` | `bcd62f35e8bf480ec5b0fa569b6d12ea5924030c` | — | advanced since `1.99.1` |
| `src/doc/rust-by-example` | `rust-lang/rust-by-example` | `dcc14f912bf8790792a2df082eddc82ab2539229` | — | advanced since `1.99.1` |
| `src/gcc` | `rust-lang/gcc` | `e1c6e07b095d091177376a163da44039475e05e3` | — | advanced since `1.99.1` |
| `src/llvm-project` | `rust-lang/llvm-project` | `08ec928a5bd1866f4008c8ad216166ca685fd380` | `rustc/23.1-2026-07-22` | `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` (`23.1.1`) in `1.99.1` |
| `src/tools/cargo` | `rust-lang/cargo` | `f93c676e3e7ab1aee08dc95d869700f6b99a1a20` | — | advanced since `1.99.1` |
| `src/tools/enzyme` | `rust-lang/enzyme` | `9cff5a8afebc22748bb36c135dfe5a09dd1047f3` | — | advanced since `1.99.1` |
| `src/tools/rustc-perf` | `rust-lang/rustc-perf` | `15d95905429e577d5a710b17c49e04b4451c263b` | — | advanced since `1.99.1` |
| `src/tpde` | `rust-lang/tpde` | `050927ee81dc11a9e599fa2524ff0eef16daf51a` | — | **Added after `1.99.1`** (not present in `1.99.1`) |

In addition to the 13 Git submodules, **11 directories** carry `josh-sync.toml` manifests for bidirectional synchronization with external `rust-lang/*` GitHub repositories via **Josh (`rustc-josh-sync`)** (`triagebot.toml`, `src/bootstrap/src/core/build_steps/check.rs:851`; full sync mechanics in `rust-repo-submodule-subtree-rolls-stage0-bumps-and-release-nightly-pipeline`):
1. `src/tools/rust-analyzer` <-> `rust-lang/rust-analyzer` (`596,238` raw lines / `497,213` SLOC);
2. `src/tools/clippy` <-> `rust-lang/rust-clippy` (`301,806` raw lines / `213,999` SLOC);
3. `src/tools/miri` <-> `rust-lang/miri` (`135,340` raw lines / `96,344` SLOC);
4. `src/tools/rustfmt` <-> `rust-lang/rustfmt` (`104,013` raw lines / `78,825` SLOC);
5. `compiler/rustc_codegen_gcc` <-> `rust-lang/rustc_codegen_gcc` (`33,220` raw lines + `build_system`);
6. `compiler/rustc_codegen_cranelift` <-> `rust-lang/rustc_codegen_cranelift` (`20,411` raw lines + `build_system`);
7. `library/stdarch` <-> `rust-lang/stdarch` (`529,901` raw lines / `451,525` SLOC);
8. `library/compiler-builtins` <-> `rust-lang/compiler-builtins` (`56,510` raw lines / `42,123` SLOC);
9. `library/portable-simd` <-> `rust-lang/portable-simd` (`22,605` raw lines / `10,141` SLOC);
10. `library/hashbrown` <-> `rust-lang/hashbrown` (`27,481` raw lines / `17,841` SLOC; synced in-tree via `library/hashbrown/josh-sync.toml`, while `library/std/Cargo.toml:23` still resolves `hashbrown 0.17.1` from `library/Cargo.lock` pending cutover);
11. `src/doc/rustc-dev-guide` <-> `rust-lang/rustc-dev-guide` (`756` blobs under `src/doc/`).

Keeping these eleven components as in-tree subtrees rather than `160000` gitlinks ensures that breaking internal `rustc_*` or `library/` refactorings atomically update `clippy`, `miri`, `rust-analyzer`, `rustfmt`, `cg_clif`, and `cg_gcc` in the same Bors rollup commit.

---

### 6. Complete `src/bootstrap` (`x.py`) Multi-Stage `Step` Execution Architecture

`Basis: source (x, x.py, x.ps1, src/stage0, src/bootstrap/bootstrap.py:1-1487, src/bootstrap/src/bin/rustc.rs:1-215, src/bootstrap/src/core/compiler.rs:1-51, src/bootstrap/src/core/builder/{mod.rs,cargo.rs,step_stack.rs}, src/bootstrap/src/core/build_steps/{compile,llvm,gcc,tool,test,check,dist,doc}.rs)`

#### 6.1 Phase 0 Bootstrap: `x` / `x.py` -> `bootstrap.py` -> `build/bootstrap/debug/bootstrap`

Invoking `./x`, `./x.py`, or `./x.ps1` executes a two-phase bootstrap before a single `Step` runs:
1. **Python Stage-0 Acquisition (`src/bootstrap/bootstrap.py:498-755, 1342-1426`):** `x.py` imports `bootstrap.py`, which parses `bootstrap.toml` (if present) and `src/stage0`. At `412be32a6a189d9a28922beee178bc0abee9d492`, `src/stage0` pins `compiler_date=2026-11-10` (`compiler_version=beta`) and `rustfmt_date=2026-11-10` (`rustfmt_version=nightly`) along with per-triple `.tar.xz`/`.tar.gz` SHA-256 checksums. Unless overridden by `build.rustc` / `build.cargo` in `bootstrap.toml` (`local_rebuild`), `RustBuild.download_toolchain()` downloads and verifies `rust-std`, `rustc`, and `cargo` tarballs from `https://static.rust-lang.org/dist/2026-11-10/`, unpacks them into `build/<host_triple>/stage0/`, and patches ELF interpreter/rpath headers on NixOS (`fix_bin_or_dylib`, `bootstrap.py:756-885`).
2. **Compiling the `bootstrap` Crate (`bootstrap.py:1062-1222`):** `RustBuild.build_bootstrap()` invokes `build/<host>/stage0/bin/cargo build --manifest-path src/bootstrap/Cargo.toml` with `CARGO_TARGET_DIR=build/bootstrap`, `RUSTC=build/<host>/stage0/bin/rustc`, `RUSTC_BOOTSTRAP=1` (`bootstrap.py:1141`), `-Zallow-features=` (`bootstrap.py:1148`, preventing `src/bootstrap` itself from accidentally relying on nightly Rust syntax), and `RUSTFLAGS` + `RUSTFLAGS_BOOTSTRAP` (`bootstrap.py:1194-1200`). This produces three binaries in `build/bootstrap/debug/`: `bootstrap` (the orchestrator), `rustc` (the compiler wrapper shim), and `rustdoc` (the doc wrapper shim). `bootstrap.py` then `exec`s (or spawns) `build/bootstrap/debug/bootstrap` with the user's CLI arguments.

#### 6.2 `Builder::ensure<S: Step>` Memoization, Cycle Detection, and Step Modules

Inside the Rust `bootstrap` binary (`88` `.rs`/`.py` files, `49,490` raw lines / `37,561` SLOC), build orchestration is driven on-demand rather than by a pre-materialized static graph (`src/bootstrap/src/core/builder/mod.rs:113-190, 1574-1665`):
- **`Step` and `CommandLineStep` traits (`mod.rs:113-190`):** Every build node is a typed key struct `S: 'static + Clone + Debug + PartialEq + Eq + Hash` implementing `Step` (`type Output: Clone; fn run(self, builder: &Builder<'_>) -> Self::Output`). User-invocable steps implement `CommandLineStep` (`should_run`, `is_default_step`, `make_run`, `IS_HOST`), which receives a blanket `impl<S: CommandLineStep> Step for S` (`mod.rs:130-140`).
- **Memoization and dynamic cycle panics (`Builder::ensure`, `mod.rs:1574-1665`):** Calling `builder.ensure(step)` first scans `self.stack: RefCell<Vec<Box<dyn AnyDebug>>>` (`lines 1576-1588`); if an equal `S` value is already active on the call stack, `bootstrap` panics immediately with `"Cycle in build detected when adding {step:?}"` and prints the active `StepStack`. Next, it probes `self.cache: Cache` (a type-indexed `HashMap<TypeId, Box<dyn Any>>` mapping `S -> S::Output`, `lines 1589-1598`), returning the cloned `S::Output` on hit. On miss, it pushes `step` onto `self.stack` and thread-local `STEP_STACK` (`step_stack.rs:1-48`), executes `step.clone().run(self)` while subtracting child dependency durations from self-timing (`lines 1623-1647`), pops `self.stack`, inserts `(step, out)` into `self.cache`, and returns `out`.

Across `src/bootstrap/src/core/build_steps/`, `18` implementation modules define all internal `Step`s, `CommandLineStep`s, and macro-generated `test!` suites:

| `build_steps/` Module | Raw Lines | Approx. SLOC | Internal `Step` Impls | `CommandLineStep` Impls | Macro-Generated Suite Steps |
| :--- | ---: | ---: | :--- | :--- | :--- |
| `check.rs` | 932 | 673 | `PrepareRustcRmetaSysroot`, `PrepareStdRmetaSysroot` | **4**: `CraneliftCodegenBackend`, `GccCodegenBackend`, `Rustc`, `Std` | — |
| `clean.rs` | 262 | 193 | — | **1**: `CleanAll` | — |
| `clippy.rs` | 678 | 550 | — | **4**: `CI`, `CodegenGcc`, `Rustc`, `Std` | — |
| `compile.rs` | 2,979 | 1,976 | `RustcLink`, `StdLink`, `Sysroot` | **6**: `Assemble`, `CraneliftCodegenBackend`, `GccCodegenBackend`, `Rustc`, `StartupObjects`, `Std` | — |
| `dist.rs` | 3,289 | 2,446 | `DebuggerScripts` | **29**: `Analysis`, `Bootstrap`, `BuildManifest`, `Cargo`, `Clippy`, `CraneliftCodegenBackend`, `Docs`, `Enzyme`, ... | — |
| `doc.rs` | 1,789 | 1,333 | `RustbookSrc`, `SharedAssets` | **11**: `CompilerWithTools`, `ErrorIndex`, `Reference`, `Releases`, `Rustc`, `RustcBook`, `Standalone`, `Std`, ... | — |
| `format.rs` | 377 | 280 | `InternalRustfmt` | — | — |
| `gcc.rs` | 384 | 275 | — | **1**: `Gcc` | — |
| `install.rs` | 343 | 284 | — | **1**: `Src` | — |
| `llvm.rs` | 2,491 | 1,770 | `FileCheck`, `LlvmFromCi` | **9**: `CrtBeginEnd`, `Enzyme`, `Libunwind`, `Lld`, `Llvm`, `OmpOffload`, `RustOffload`, `Sanitizers`, ... | — |
| `perf.rs` | 282 | 227 | — | — | — |
| `run.rs` | 556 | 404 | — | **14**: `BuildManifest`, `BumpStage0`, `CollectLicenseMetadata`, `CoverageDump`, `CyclicStep`, `FeaturesStatusDump`, `GenerateCompletions`, `GenerateCopyright`, ... | — |
| `setup.rs` | 768 | 631 | — | **4**: `Editor`, `Hook`, `Link`, `Profile` | — |
| `synthetic_targets.rs` | 71 | 45 | `MirOptPanicAbortSyntheticTarget` | — | — |
| `test.rs` | 5,112 | 3,749 | `BookTest`, `Compiletest`, `RemoteCopyLibs` | **44**: `Bootstrap`, `BootstrapPy`, `Cargo`, `CargoMiri`, `Cargotest`, `Clippy`, `CodegenCranelift`, `CodegenGCC`, ... | **17**: `AssemblyGcc`, `AssemblyLlvm`, `BuildStd`, `CodegenLlvm`, `CodegenUnits`, `CoverageRunRustdoc`, `Crashes`, `Debuginfo`, ... |
| `test/failed_tests.rs` | 106 | 81 | `SetupFailedTestsFile` | — | — |
| `tool.rs` | 1,683 | 1,259 | `LibcxxVersionTool`, `ToolBuild` | **11**: `BuildManifest`, `Cargo`, `ErrorIndex`, `LldWrapper`, `LlvmBitcodeLinker`, `RemoteTestServer`, `RustAnalyzer`, `RustAnalyzerProcMacroSrv`, ... | — |
| `toolstate.rs` | 460 | 296 | — | **1**: `ToolStateCheck` | — |
| `vendor.rs` | 184 | 120 | — | **1**: `Vendor` | — |

#### 6.3 `Compiler { stage, host }` Semantics and the Multi-Stage (`stage 0`..`stage 3`) DAG

A compiler instance is identified by `Compiler { stage: u32, host: TargetSelection, forced_compiler: bool }` (`src/bootstrap/src/core/compiler.rs:11-31`, where `Hash` and `PartialEq` ignore `forced_compiler`). Obtaining a usable compiler for `(stage, host)` runs `builder.compiler(stage, host)` -> `builder.ensure(Assemble { target_compiler })` (`compile.rs:2100-2455`):

1. **`stage 0` (`Compiler { stage: 0, host: build_triple }`):** Base case of `Assemble::run` (`compile.rs:2125-2133`). Always resolves directly to the prebuilt `stage 0` snapshot unpacked by `bootstrap.py` (or `build.rustc` when `local_rebuild = true`), asserting `target_compiler.host == builder.config.host_target`. `Std::run` for `build_compiler.stage == 0` is a no-op (`StdLink` copies prebuilt `stage 0` target libs unless cross-compiling under `local_rebuild`, `compile.rs:164-171`).
2. **Building `stage 1` (`Assemble { target_compiler: Compiler { stage: 1, host } }`):**
   - Requests `build_compiler = builder.compiler(0, host_target)` (`compile.rs:2297-2298`).
   - Ensures host `llvm::Llvm` (`compile.rs:2141-2146` -> either `LlvmFromCi` downloading prebuilt CI LLVM matching `src/bootstrap/download-ci-llvm-stamp` in `llvm.rs:257-420`, or full CMake/Ninja C++ compilation of `src/llvm-project/llvm`), plus optional `llvm::Enzyme` (`compile.rs:2301`), `llvm::RustOffload` / `OmpOffload` (`compile.rs:2310`), and `tool::LlvmBitcodeLinker` (`compile.rs:2232`).
   - Invokes `builder.ensure(Rustc::new(stage0, host))` (`compile.rs:2343`):
     - `Rustc::run` first calls `builder.std(stage0, host)` (`compile.rs:1064`), which is a no-op on `stage 0` (so **the `stage 1` compiler binary links against the `stage 0` beta standard library**!).
     - Compiles `compiler/rustc` (`Mode::Rustc`, root `Cargo.toml`) using `stage 0` `rustc` with `--cfg=bootstrap` (`cargo.rs:96, 882`) and `RUSTFLAGS_BOOTSTRAP`.
   - `Assemble` copies `librustc_driver-*.so` and non-proc-macro dynamic deps (excluding `libstd-*` because `rustc_driver` links `std` statically; see §6.4) into `build/host/stage1/lib/`, builds enabled alternate backends (`CraneliftCodegenBackend`, `GccCodegenBackend` + `gcc::Gcc` `libgccjit`, `compile.rs:2399-2450`), copies the `rustc` binary into `build/host/stage1/bin/rustc`, and links `rust-lld` (`tool::LldWrapper` + `llvm::Lld`) into `lib/rustlib/<host>/bin/gcc-ld/`.
   - **Target `stage 1` sysroot (`Std { build_compiler: stage1, target }`):** When `stage 1` `rustc` is subsequently asked to compile user code, tests, or `stage 2` `rustc`, `Std::run` (`compile.rs:157-360`) ensures `StartupObjects` and builds `library/sysroot` (`Mode::Std`) *using `stage 1` `rustc`* (without `--cfg=bootstrap`, using `RUSTFLAGS_NOT_BOOTSTRAP`), linking the newly compiled `libcore`, `liballoc`, `libstd`, `libtest`, and `libproc_macro` into `build/host/stage1/lib/rustlib/<target>/lib/` via `StdLink`.
3. **Building `stage 2` (`Assemble { target_compiler: Compiler { stage: 2, host } }`):**
   - Requests `build_compiler = builder.compiler(1, host_target)`.
   - `Rustc::run(build_compiler = stage1, target = host)` calls `builder.std(stage1, host)` (`compile.rs:1064`), ensuring in-tree `library/sysroot` is compiled by `stage 1`, and then compiles `compiler/rustc` *using `stage 1` `rustc`* against that in-tree `libstd`.
   - Thus `stage 2` is the first compiler binary **both compiled by the in-tree compiler logic and linked against the in-tree standard library and proc-macro ABI**, which is why shipped toolchains (`./x.py dist`), `rustc_private` end-user tools, and full ABI parity tests target `stage 2`.
4. **`stage 3` Uplift vs. `build.full-bootstrap = true` (`compile.rs:1079-1110`):**
   - When a step requests `stage >= 3` (`build_compiler.stage >= 2`) on the native host and `build.full-bootstrap` is `false` (default), `Rustc::run` **does not recompile `rustc`**; instead it uplifts the `stage 2` `rustc` artifacts (`uplift_build_compiler = builder.compiler(1, host)`) via `RustcLink::from_build_compiler_and_sysroot` (`compile.rs:1083-1109`). `compile.rs:1087-1089` explicitly notes that `stage 1` can never be uplifted because `stage 1` has the `stage 0` ABI whereas `stage 2+` share the in-tree ABI.
   - Setting `build.full-bootstrap = true` disables uplifting, forcing `stage 2` `rustc` to compile a fresh `stage 3` `rustc` so CI (`ReproducibleArtifacts` / self-hosting verification) can check fixed-point convergence between `stage 2` and `stage 3`.
5. **Developer Fast-Path Shortcuts:**
   - `rust.download-rustc = true` (`compile.rs:132-196, 1049-1060, 2258-2277`): Downloads a prebuilt CI `stage 2` compiler from `https://ci-artifacts.rust-lang.org/rustc-builds` (`ci-rustc-sysroot`) and reuses it for all `stage > 0` `Assemble` and `Rustc` steps; if `has_changes_from_upstream(&["library"])` detects local edits under `library/`, `force_recompile` automatically falls back to recompiling `Std` with the downloaded compiler (`compile.rs:132-135, 173-180`).
   - `build.local-rebuild = true` (`cargo.rs:767-772`, `compile.rs:165, 807, 934`): Treats a custom `build.rustc` at `stage 0` as already possessing `stage 1` unstable features (`build_compiler_stage = 1`, omitting `--cfg=bootstrap` and `RUSTFLAGS_BOOTSTRAP`).
   - `--keep-stage <N>` and `--keep-stage-std <N>` (`compile.rs:198-212, 1066-1074`, `cargo.rs:1039-1043`): Skips Cargo invocation and re-links previously built `stage <N>` `librustc` and/or `libstd` artifacts while suppressing `build_stamp::clear_if_dirty`.

#### 6.4 The `build/bootstrap/debug/rustc` Wrapper Shim and Environment Protocol

`Builder::cargo` (`src/bootstrap/src/core/builder/cargo.rs:750-1275`) never points Cargo directly at a raw `rustc` binary. Instead, it sets both `RUSTC` and `RUSTC_WRAPPER` to `build/bootstrap/debug/rustc` (`cargo.rs:1076-1078`, chaining any user `sccache` wrapper via `RUSTC_WRAPPER_REAL`, `lines 1082-1084`) and communicates per-mode build policy through environment variables interpreted by `src/bootstrap/src/bin/rustc.rs`:

| Environment Variable | Producer (`cargo.rs` / `bootstrap.py`) | Consumer (`bin/rustc.rs` / `rustc`) | Exact Bootstrap Role |
| :--- | :--- | :--- | :--- |
| `RUSTC_REAL` & `RUSTC_LIBDIR` | `cargo.rs:1060, 1063` | `bin/rustc.rs:52, 58-62` | Path and `LD_LIBRARY_PATH`/`PATH` prepend directory of the active stage compiler used when `--target` (or `-vV`) **is** passed (i.e. target crates and proc-macros under `-Zdual-proc-macros`). |
| `RUSTC_SNAPSHOT` & `RUSTC_SNAPSHOT_LIBDIR` | `cargo.rs:1242-1250` | `bin/rustc.rs:48-51` | Used when `target.is_none() && version.is_none()` (`is_build_script == true`): compiles `build.rs` scripts of `library/` (`Mode::Std`) using `initial_rustc` (`stage 0`), breaking the chicken-and-egg cycle where `std`'s `build.rs` needs an already-built `libstd`! |
| `RUSTC_SYSROOT` | `cargo.rs:781-785, 1062` | `bin/rustc.rs:55, 165` | Injects `--sysroot <path>` (`stage0` snapshot sysroot for `ToolBootstrap`, or `build/<host>/stage<N>` otherwise). |
| `RUSTC_STAGE` | `cargo.rs:767-772, 1061` | Build scripts & `bin/rustc.rs` | `"0"`, `"1"`, `"2"` (promoted from `"0"` to `"1"` when `local_rebuild = true`). |
| `RUSTFLAGS_BOOTSTRAP` vs. `RUSTFLAGS_NOT_BOOTSTRAP` | `cargo.rs:90-98` (`propagate_rustflag_envs`) | Encoded into `RUSTFLAGS` / `CARGO_ENCODED_RUSTFLAGS` (`cargo.rs:108-118`) | Appends `RUSTFLAGS_BOOTSTRAP` + `--cfg=bootstrap` **only** when `build_compiler_stage == 0`, and `RUSTFLAGS_NOT_BOOTSTRAP` **only** when `build_compiler_stage != 0`. |
| `RUSTC_BOOTSTRAP` | `bootstrap.py:1141`, `cargo.rs:1214` | `rustc` feature-gate checker | Set to `"1"` across Cargo invocations (`-Zallow-features=...` narrows allowed features for `ToolBootstrap` / `ToolStd` / `ToolTarget`, `cargo.rs:934-956`; `compiletest` sets `"-1"` when compiling `rmake.rs`). |
| `RUSTC_FORCE_UNSTABLE` | `cargo.rs:1145-1155` | `bin/rustc.rs:180-182` | Set to `"1"` for `Mode::{Std, Codegen, Rustc}`, causing `bin/rustc.rs` to pass `-Zforce-unstable-if-unmarked` so unmarked sysroot dependencies cannot leak into stable user namespaces. |
| `__CARGO_DEFAULT_LIB_METADATA` | `cargo.rs:971-1013` | `cargo` `-Cmetadata` hash seed | Concatenates `{"bootstrap" | channel} + {"std" | "tool-rustc" | "codegen" | ""} + version` so `libc`/`bitflags` compiled in `Std`, `Rustc`, `Codegen`, and `ToolRustcPrivate` receive distinct symbol hashes and never collide during dynamic linking. |
| *(Static `std` in `rustc_driver`)* | `bin/rustc.rs:95-106` | `rustc` linker args | When `--crate-name rustc_driver` is detected, `bin/rustc.rs` strips `-C prefer-dynamic` / `-Cprefer-dynamic` so `librustc_driver.so` statically embeds `libstd`, allowing `Assemble` (`compile.rs:2385-2388`) to omit `libstd-*.so` from `rustc_libdir`. |

---

### 7. Complete Census of All 23 `tests/` Directories and Suite Evolution

`Basis: source + execution (tests/*, src/bootstrap/src/core/build_steps/test.rs:2115-2165, src/tools/compiletest/src/common.rs:63, support/rust_repo_inventory.json)`

At `412be32a6a189d9a28922beee178bc0abee9d492`, `tests/` contains `tests/COMPILER_TESTS.md` plus **23 immediate directories** (`45,544` tracked files total): **22 `compiletest` suite directories** and **1 shared helper directory** (`tests/auxiliary/`). Relative to `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), top-level `tests/explain.rs` was removed and **`tests/assembly-gcc/`** was added as the 22nd `compiletest` suite (`test!(AssemblyGcc { path: "tests/assembly-gcc", mode: CompiletestMode::Assembly, suite: "assembly-gcc", default: true })` in `src/bootstrap/src/core/build_steps/test.rs:2128-2133`, `AssemblyGcc => "assembly-gcc"` in `src/tools/compiletest/src/common.rs:63`), initially seeded with `tests/assembly-gcc/stack-protector/stack-protector-heuristics-effect.rs` (`4` revisions `all`, `strong`, `none`, `missing` checking `__stack_chk_fail` emission under `-Zstack-protector`).

| `tests/` Directory | Total Tracked Files | `.rs` Files | `.stderr` Goldens | `compiletest` Mode, `bootstrap` Step & Suite Role |
| :--- | ---: | ---: | ---: | :--- |
| `tests/assembly-gcc` | 1 | 1 | 0 | `assembly` (`AssemblyGcc`, **added after `1.99.1`**); FileCheck over `rustc_codegen_gcc` emitted assembly |
| `tests/assembly-llvm` | 185 | 185 | 0 | `assembly` (`AssemblyLlvm`); FileCheck over LLVM emitted `.s` / PTX assembly |
| `tests/auxiliary` | 3 | 2 | 0 | Shared helper directory (`rust_test_helpers.c` -> `librust_test_helpers.a` + `minicore.rs`) |
| `tests/build-std` | 1 | 1 | 0 | `run-make` (`BuildStd`, `default: false`); exercises Cargo `-Zbuild-std` against in-tree `library/` |
| `tests/codegen-llvm` | 905 | 889 | 0 | `codegen` (`CodegenLlvm`); LLVM `FileCheck` over `--emit=llvm-ir -Cno-prepopulate-passes` |
| `tests/codegen-units` | 54 | 53 | 0 | `codegen-units` (`CodegenUnits`); checks `MONO_ITEM` collection and CGU partitioning |
| `tests/coverage-run-rustdoc` | 3 | 2 | 0 | `coverage-run-rustdoc`; doctest instrumentation coverage under `rustdoc` |
| `tests/coverage` | 347 | 117 | 0 | `coverage-map` & `coverage-run` (`Coverage`); checks `__llvm_covmap` and `llvm-cov` execution |
| `tests/crashes` | 148 | 147 | 0 | `crashes` (`Crashes`); tracked ICE reproducers expected to exit with status `101` |
| `tests/debuginfo` | 203 | 177 | 0 | `debuginfo` (`Debuginfo`); interactive `gdb`, `lldb`, and `cdb` variable/type inspection |
| `tests/incremental` | 218 | 218 | 0 | `incremental` (`Incremental`); multi-revision cache invalidation (`rpass`/`cfail`/`bfail`/`rfail`) |
| `tests/mir-opt` | 1,819 | 424 | 0 | `mir-opt` (`MirOpt`); diffs `-Zdump-mir` pass outputs (requires `std` with `-Zalways-encode-mir`) |
| `tests/pretty` | 166 | 118 | 0 | `pretty` (`Pretty`); idempotence and re-parse checks for `-Zunpretty` modes |
| `tests/run-make-cargo` | 108 | 48 | 0 | `run-make` (`RunMakeCargo`); `rmake.rs` recipes invoking Stage-N `cargo` + `rustc` |
| `tests/run-make` | 1,674 | 1,404 | 24 | `run-make` (`RunMake`); arbitrary `rmake.rs` Rust build/link/binutils recipes |
| `tests/rustdoc-gui` | 217 | 29 | 0 | `rustdoc-gui` (`RustdocGUI`); headless browser `.goml` UI tests |
| `tests/rustdoc-html` | 1,089 | 1,020 | 0 | `rustdoc-html` (`RustdocHtml`); `@has` / `@matches` HTML output checks |
| `tests/rustdoc-js-std` | 69 | 0 | 0 | `js-doc-test` (`RustdocJSStd`); standard-library search-index JS query tests |
| `tests/rustdoc-js` | 172 | 91 | 0 | `js-doc-test` (`RustdocJSNotStd`); custom crate search-index JS query tests |
| `tests/rustdoc-json` | 210 | 209 | 0 | `rustdoc-json` (`RustdocJson`); `jsondocck` + `jsondoclint` over `-Zunstable-options --output-format json` |
| `tests/rustdoc-ui` | 870 | 480 | 245 | `ui` (`RustdocUi`); diagnostic stderr tests for `rustdoc` lints and intra-doc links |
| `tests/ui-fulldeps` | 125 | 89 | 28 | `ui` (`UiFullDeps`); UI tests linking `#![feature(rustc_private)]` compiler crates or host plugins |
| `tests/ui` | 36,956 | 21,862 | 14,049 | `ui` (`Ui`); primary frontend diagnostic, `check-pass`, `build-pass`, and `run-pass` suite |

For `compiletest`'s `24` mandatory CLI flags, `308` `//@` directive names, `Cranelift`/`GCC` exclusion lists, and the 5-tier per-file test classification (`frontend-only`, `backend-codegen`, `mir-only`, `llvm-specific`, `rustdoc/ice`), see `rustc-compiletest-bootstrap-and-alternate-backend-test-mechanics` and `rustc-test-suite-machine-readable-classification`.

## Boundaries

- **Submodule internal file trees (`not examined` by `extract_repo_architecture.py`):** In Git's object model, `160000` gitlink entries in `rust-lang/rust` store only the 40-hex commit SHA of each submodule (`src/llvm-project`, `src/gcc`, `src/tpde`, `src/tools/{cargo,enzyme,rustc-perf}`, `library/backtrace`, and the `6` `src/doc/*` books), not their constituent blobs. `support/extract_repo_architecture.py` intentionally reads only blobs in the `rust-lang/rust` superproject so it executes deterministically on uninitialized or shallow clones; `src/llvm-project` internal SLOC (`2,443,836` SLOC in `llvm/lib` + `llvm/include` and `679,541` raw lines of `.td` at `1.99.1`) is recorded in `rustc-baseline-repository-map-and-internal-interfaces`.
- **Target-conditional third-party Cargo edges (`known not to apply` to internal `rustc_*` DAG):** All internal `rustc_*` dependencies across the `77` in-graph `compiler/*` crates are unconditional, whereas third-party crates (`windows`, `libc`, `object`, `unwinding`, `wasip1`, `wasip2`) activate conditionally per host/target `cfg(...)` predicate.
- **Line-counting heuristic (`approx_sloc`):** `support/extract_repo_architecture.py` computes `approx_sloc` by excluding blank lines and lines whose trimmed text starts with `//`, `/*`, `*`, or `#` (`# ` / bare `#` for Python/shell/TOML). Multiline block-comment bodies without leading `*` and raw string literals containing comment-like prefixes are not lexically stripped.
- **Runtime `Config::override_queries` hooks (`known not to apply` to default `rustc`):** Custom `rustc_driver::Callbacks` drivers (such as Miri, Kani, or external MIR extractors) can mutate `interface::Config::override_queries` at runtime after `DEFAULT_QUERY_PROVIDERS` initialization; the provider map in §3 reflects static in-tree `compiler/` and `src/librustdoc` registrations.

## Evidence

- **Preserved executable extractor and generated dataset (in this package):**
  - `support/extract_repo_architecture.py` — standalone, zero-working-tree-touch Python 3.11+ Git-object inventory extractor (`git ls-tree -r -l` + `git cat-file --batch`, `~9.3s` wall time across all `64,687` blobs).
  - `support/rust_repo_inventory.json` — complete machine-readable output for `rust-lang/rust` @ `412be32a6a189d9a28922beee178bc0abee9d492`.
- **Primary upstream source coordinates (`rust-lang/rust` @ `412be32a6a189d9a28922beee178bc0abee9d492`):**
  - Root workspace & governance: `Cargo.toml:1-89`, `Cargo.lock`, `.gitmodules:1-53`, `bootstrap.example.toml:1-1237`, `triagebot.toml:1-2094`, `rust-bors.toml:1-107`, `REUSE.toml:1-219`, `x:1-55`, `x.py:1-53`, `x.ps1:1-45`, `src/stage0`, `src/version`.
  - Compiler crates & `1.99.1 -> 1.102.0-nightly` additions: `compiler/*/Cargo.toml` (`79` direct crates, `85` manifests), `compiler/rustc_expand_queries/{Cargo.toml,src/lib.rs:1-12}`, `compiler/rustc_structures/{Cargo.toml,src/lib.rs:1-23}`, `compiler/rustc_proc_macro/Cargo.toml:1-24`, `compiler/rustc_codegen_cranelift/src/lib.rs`, `compiler/rustc_codegen_gcc/src/lib.rs`, `src/librustdoc/Cargo.toml`.
  - Query declarations, modifiers & providers: `compiler/rustc_middle/src/queries.rs:1-2918`, `compiler/rustc_macros/src/query.rs:1-490`, `compiler/rustc_middle/src/query/modifiers.rs:1-108`, `compiler/rustc_interface/src/passes.rs:920-1075`, `compiler/rustc_metadata/src/rmeta/decoder/cstore_impl.rs`.
  - Standard library & façade shims: `library/Cargo.toml:1-90`, `library/sysroot/Cargo.toml:1-39`, `library/std/Cargo.toml:1-125`, `library/rustc-std-workspace-core/{Cargo.toml,lib.rs,README.md:1-38}`, `src/rustc-std-workspace/rustc-std-workspace-{core,alloc,std}/Cargo.toml`, `library/rtstartup/{rbegin.rs,rend.rs}`.
  - Bootstrap orchestrator & wrapper shims: `src/bootstrap/Cargo.toml:1-97`, `src/bootstrap/bootstrap.py:498-1426`, `src/bootstrap/src/bin/rustc.rs:1-215`, `src/bootstrap/src/core/compiler.rs:1-51`, `src/bootstrap/src/core/builder/mod.rs:113-190,1574-1665`, `src/bootstrap/src/core/builder/step_stack.rs:1-48`, `src/bootstrap/src/core/builder/cargo.rs:70-130,755-1275`, `src/bootstrap/src/core/build_steps/compile.rs:115-225,887-1110,1678-1800,1928-2455`, `src/bootstrap/src/core/build_steps/llvm.rs:257-430,1670-2400`, `src/bootstrap/src/core/build_steps/tool.rs:43-1380`.
  - Test suite registry: `src/bootstrap/src/core/build_steps/test.rs:2115-2165`, `src/tools/compiletest/src/common.rs:63`, `tests/assembly-gcc/stack-protector/stack-protector-heuristics-effect.rs:1-80`.
- **Baseline comparison coordinates (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `compiler/*` (`78` direct crates including `compiler/rustc_baked_icu_data`; `83` `Cargo.toml` manifests), `compiler/rustc_middle/src/queries.rs` (`326` queries), `.gitmodules` (`12` submodules; `src/llvm-project` at `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), and `tests/*` (`21` `compiletest` suites + `tests/auxiliary` + `tests/explain.rs`).

## Revalidation

To revalidate all repository counts, Cargo workspace boundaries, compiler DAG edges, topological depths, 3-way verification splits, query modifiers/providers, `library/` shims, submodules, `bootstrap` steps, and `tests/` suites against any newer `rust-lang/rust` commit `<NEW_SHA>` without checking out or modifying a working tree:

```bash
python3 reports/rust-repo-complete-layout-crate-dag-and-bootstrap-architecture/support/extract_repo_architecture.py \
  --rust-repo /path/to/rust \
  --rev <NEW_SHA> \
  --out /tmp/rust_repo_inventory_new.json
```

Then run a focused structural diff against the preserved inventory:

```bash
python3 -c '
import json, sys
old = json.load(open("reports/rust-repo-complete-layout-crate-dag-and-bootstrap-architecture/support/rust_repo_inventory.json"))
new = json.load(open("/tmp/rust_repo_inventory_new.json"))
oc = {c["key"] for c in old["compiler"]["crates"]}
nc = {c["key"] for c in new["compiler"]["crates"]}
print("Compiler crates added:", sorted(nc - oc), "removed:", sorted(oc - nc))
print("Queries:", old["queries"]["query_count"], "->", new["queries"]["query_count"])
print("Modifier counts:", new["queries"]["modifier_counts"])
ot = {t["name"] for t in old["tests"]["directories"]}
nt = {t["name"] for t in new["tests"]["directories"]}
print("Test dirs added:", sorted(nt - ot), "removed:", sorted(ot - nt))
'
```

If `extract_repo_architecture.py` raises `KeyError` in `COMPILER_CRATE_TAXONOMY` or `TOOL_CLASSIFICATION`, a new `compiler/*` crate or `src/tools/*` entry was added upstream and should be classified explicitly before updating `REPORT.md`.
