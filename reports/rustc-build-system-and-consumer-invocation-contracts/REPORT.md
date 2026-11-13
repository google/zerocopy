# `rustc` Build-System Driver Patterns and Consumer Invocation Contracts

## Summary

A drop-in replacement for `rustc` at Rust `1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`, bundled with Cargo `0.100.0` at
`5f94df4789f005f9a352888e8355ffc645b7ed0e`) is almost never invoked directly
by humans; instead, it is driven by nine major build-system families (Cargo,
Bazel `rules_rust`, GN in Chromium and Fuchsia, Buck2, Linux Kernel Kbuild,
Android Soong, Meson, CMake Corrosion, and Nix/distro builders) and caching
wrappers (`sccache`). Tracing `execve` invocations across Cargo modes (`check`,
`build`, `build --release`, `test --no-run`, `bench --no-run`, `fix`, and
`-Zbuild-std=core`) and auditing non-Cargo build rules establishes five
governing requirements:

1. **Two-phase toolchain discovery handshake:** Before scheduling any crate
   compilation, Cargo and non-Cargo build systems execute two mandatory probe
   invocations:
   - `rustc -vV`, whose stdout must contain exact key-value lines (`binary:`,
     `commit-hash:`, `commit-date:`, `host:`, `release:`, `LLVM version:`).
   - A batched stdin discovery query (`rustc - --crate-name ___
     --print=file-names --crate-type bin --crate-type rlib --crate-type dylib
     --crate-type cdylib --crate-type staticlib --crate-type proc-macro
     --print=sysroot --print=split-debuginfo --print=crate-name --print=cfg
     -Wwarnings`), whose stdout is parsed positionally by line count.
2. **Core flag reliance hierarchy (`P0` vs. `P1`):** Across all 50 traced Cargo
   invocations (`support/cargo_invocation_logs.json`) and 8 non-Cargo build
   systems (`support/build_system_and_consumer_matrix.json`), 100% of unit
   compilations rely on `--crate-name`, `--edition`, `--crate-type`, `--emit`,
   `--out-dir`, `-L`, `--extern`, `-Cmetadata`, `-Cextra-filename`,
   `--error-format=json`, and `--json=diagnostic-rendered-ansi,artifacts`.
   Cargo `1.99.1` additionally passes `--check-cfg=cfg(docsrs,test)` and
   `--check-cfg=cfg(feature, values(...))` on every unit (including
   `-Zbuild-std` `core` builds).
3. **Non-Cargo build-system specifics (`@rspfile` and `-Zdep-info-omit-d-target`):**
   Bazel `rules_rust`, GN (Chromium/Fuchsia), Buck2, and Linux Kbuild pass
   arguments via `@<response_file>` and rely on `--emit=dep-info=<path>,link=<path>`
   paired with `-Zdep-info-omit-d-target` (with `RUSTC_BOOTSTRAP=1`) so Ninja
   and Bazel action graphs do not see circular self-targets in `.d` files.
4. **Consumer-specific kernel and OS flags:** Linux Kernel Kbuild (`rust/Makefile`)
   and Android Soong (`build/soong/rust`) require `-Cpanic=abort`,
   `-Cembed-bitcode=no`, `-Cforce-unwind-tables=n`,
   `-Csymbol-mangling-version=v0`, and architecture mitigation flags
   (`-Zbranch-protection`, `-Zfunction-return=thunk-extern`,
   `-Zcf-protection=branch`, `-Zno-jump-tables`,
   `-Zsanitize=hwaddress|cfi|shadow-call-stack`).
5. **Wrapper caching and jobserver invariants:** `sccache` caches only pure
   library compilations (`rlib`, `staticlib`, `proc-macro`) when
   `-Cincremental` is absent (`CARGO_INCREMENTAL=0`), keying its hash on
   `rustc -vV` output, full CLI arguments, env vars, and `--emit=dep-info`
   source hashes. Cargo shares concurrency tokens with `rustc` via
   `CARGO_MAKEFLAGS="-j --jobserver-fds=R,W --jobserver-auth=R,W"`.

## Applicability

These findings apply to any replacement compiler binary invoked as `rustc` (or
via `RUSTC` / `RUSTC_WRAPPER`) under **Rust 1.99.1** (`rust-lang/rust`
`58cf8f9c35b355199727627d07ae34a4e2846d67`) and **Cargo 0.100.0**
(`rust-lang/cargo` `5f94df4789f005f9a352888e8355ffc645b7ed0e`):

- **Exact observation:** All seven Cargo workflow modes (`cargo check`,
  `cargo build`, `cargo build --release`, `cargo test --no-run`,
  `cargo bench --no-run`, `cargo fix --allow-no-vcs`, and
  `cargo build -Zbuild-std=core --target x86_64-unknown-linux-gnu`) were traced
  end-to-end on `x86_64-unknown-linux-gnu` via a `RUSTC_WRAPPER` interceptor
  (`support/cargo_invocation_logs.json`).
- **Broader build-system coverage:** Invocation patterns for Bazel `rules_rust`,
  GN (Chromium and Fuchsia), Buck2, Linux Kbuild, Android Soong, Meson, CMake
  Corrosion, Nix (`buildRustPackage`/`crane`), and `sccache` are synthesized
  from their upstream driver templates and recorded in
  `support/build_system_and_consumer_matrix.json`.

## Findings

### 1. Cargo's `rustc` invocation protocol across workflow modes

Basis: source + execution

Tracing Cargo `0.100.0` (`rustc 1.99.1`) on a workspace containing a `build.rs`
script, a library target (`src/lib.rs`), and a binary target (`src/main.rs`)
yields the exact invocation sequences in `support/cargo_invocation_logs.json`:

1. **Compiler probing (`2` invocations per Cargo session):**
   - `rustc -vV`: parsed by Cargo (`src/cargo/util/rustc.rs`) to extract `host`,
     `release`, and `commit-hash` (used to salt the `.cargo/TargetInfo` cache
     and `-Cmetadata` hashes).
   - `rustc - --crate-name ___ --print=file-names --crate-type bin --crate-type rlib --crate-type dylib --crate-type cdylib --crate-type staticlib --crate-type proc-macro --print=sysroot --print=split-debuginfo --print=crate-name --print=cfg -Wwarnings`:
     reads an empty crate from stdin (`-`) and emits in a single process the six
     naming templates (`___`, `lib___.rlib`, `lib___.so`, `lib___.so`,
     `lib___.a`, `lib___.so`), the sysroot path, supported split-debuginfo
     modes (`off`, `packed`, `unpacked`), `___`, and all active `cfg` lines.
2. **Build-script compilation and execution (`build_script_build`):**
   - Compiled as `--crate-type bin --emit=dep-info,link -Cembed-bitcode=no`
     without `-Cdebuginfo=2` even in `dev` profile, with `-Cmetadata` and
     `-Cextra-filename` hashes.
   - Executed by Cargo; stdout lines beginning with `cargo:rustc-cfg=...` (or
     `cargo::rustc-cfg=...`) append `--cfg <pred>` to downstream unit
     invocations.
3. **Mode-specific unit compilation differences:**
   Table 1 compares the unit flags passed across the seven traced Cargo modes.

| Cargo Mode | Total `rustc` Calls | Library Unit `--emit` | Binary/Test Unit Flags | Profile / Special Flags |
| :--- | :--- | :--- | :--- | :--- |
| `cargo check` | 6 | `--emit=dep-info,metadata` | `--emit=dep-info,metadata` | `-Cembed-bitcode=no -Cdebuginfo=2 -Cincremental=...` |
| `cargo build` (dev) | 6 | `--emit=dep-info,metadata,link` | `--emit=dep-info,link` | `-Cembed-bitcode=no -Cdebuginfo=2 -Cincremental=...` |
| `cargo build --release` | 6 | `--emit=dep-info,metadata,link` | `--emit=dep-info,link` | `-Copt-level=3 -Cembed-bitcode=no` (no `-Cincremental`, no `-Cdebuginfo`) |
| `cargo test --no-run` | 7 | `--emit=dep-info,metadata,link` | `--test` (replaces `--crate-type bin`, adds `lib.rs` unit test binary) | Links `libtest` from sysroot; passes `--check-cfg=cfg(test)` |
| `cargo bench --no-run` | 7 | `--emit=dep-info,metadata,link` | `--test` | Same harness flags as `cargo test --no-run` |
| `cargo fix` | 6 | `--emit=dep-info,metadata` | `--emit=dep-info,metadata` | Intercepts via `RUSTC_WORKSPACE_WRAPPER` to apply JSON diagnostic suggestions with `"suggestion_applicability":"MachineApplicable"` |
| `cargo build -Zbuild-std=core` | 12 | `--emit=dep-info,metadata,link` | Compiles `compiler_builtins` (`build.rs` + `lib`) and `core` from `<sysroot>/lib/rustlib/src/rust/library` | Sets `RUSTC_BOOTSTRAP=1`, `-Zforce-unstable-if-unmarked` |

4. **Mandatory environment variables passed by Cargo to `rustc`:**
   Every crate compilation receives `CARGO`, `CARGO_CRATE_NAME`,
   `CARGO_MANIFEST_DIR`, `CARGO_MANIFEST_PATH`, `CARGO_PKG_AUTHORS`,
   `CARGO_PKG_DESCRIPTION`, `CARGO_PKG_HOMEPAGE`, `CARGO_PKG_LICENSE`,
   `CARGO_PKG_LICENSE_FILE`, `CARGO_PKG_NAME`, `CARGO_PKG_README`,
   `CARGO_PKG_REPOSITORY`, `CARGO_PKG_RUST_VERSION`, `CARGO_PKG_VERSION`,
   `CARGO_PKG_VERSION_MAJOR`, `CARGO_PKG_VERSION_MINOR`,
   `CARGO_PKG_VERSION_PATCH`, `CARGO_PKG_VERSION_PRE`, `CARGO_PRIMARY_PACKAGE`
   (for workspace members), `OUT_DIR` (if `build.rs` ran), and
   `CARGO_MAKEFLAGS="-j --jobserver-fds=3,5 --jobserver-auth=3,5"`. Because
   user crates read these via `env!("CARGO_PKG_VERSION")` or `env!("OUT_DIR")`
   at macro expansion time, `rustc` must record every read variable as an
   `# env-dep:<KEY>=<VALUE>` line in the emitted `.d` dep-info file.

---

### 2. Non-Cargo build systems and wrapper contracts

Basis: documentation + source + derived

Table 2 summarizes how the eight non-Cargo build systems and `sccache` invoke
`rustc` (`support/build_system_and_consumer_matrix.json`).

| Build System | Discovery Probes | Key `rustc` Flags & Argfile Usage | Special Env / Wrapper Contract |
| :--- | :--- | :--- | :--- |
| **Bazel (`rules_rust`)** | `rustc -vV` | `@<param_file>`, `--emit=dep-info,link,metadata`, `--error-format=json`, `--json=artifacts,diagnostic-rendered-ansi`, `--remap-path-prefix=${pwd}=.`, `-Ccodegen-units=1`, `--extern <name>=<rmeta>` (pipelined) | `process_wrapper` substitutes `${pwd}` and parses `"$message_type":"artifact"` JSON lines |
| **GN (Chromium & Fuchsia)** | `rustc -vV` | `@<rspfile>`, `--emit=dep-info=<dfile>,link=<outfile>`, `-Zdep-info-omit-d-target`, `-Cembed-bitcode=no`, `-Clinker=<clang++>`, `-Clink-arg=-fuse-ld=lld` | Sets `RUSTC_BOOTSTRAP=1`; Ninja consumes `<dfile>` directly and requires omitting the `.d` self-target |
| **Buck2 (`prelude//rust`)** | `rustc -vV` | `@<argfile>`, `--emit=dep-info,metadata,link`, `--error-format=json`, `--json=diagnostic-rendered-ansi,artifacts`, `-Zdep-info-omit-d-target`, `--remap-path-prefix` | Supports pipelined `.rmeta`-only compilation (`--emit=dep-info,metadata`) in action graphs |
| **Linux Kernel (`Kbuild`)** | `rustc --version`, `scripts/min-tool-version.sh` | `@<cfg_argfile>`, `--target=<json_or_builtin>`, `--emit=dep-info,obj,metadata`, `-Cpanic=abort`, `-Cembed-bitcode=no`, `-Clto=n`, `-Cforce-unwind-tables=n`, `-Ccodegen-units=1`, `-Csymbol-mangling-version=v0`, `-Zbranch-protection=...`, `-Zfunction-return=thunk-extern`, `-Zcf-protection=branch`, `-Zno-jump-tables` | Sets `RUSTC_BOOTSTRAP=1`; links `.o` directly with kernel `ld.lld` / `ld.bfd` without `rustc` linker driver |
| **Android (`Soong`)** | `rustc --version` | `--emit=link,dep-info`, `-Zdep-info-omit-d-target`, `-Cpanic=abort`, `-Copt-level=z\|s\|3`, `-Crelocation-model=pic`, `-Cforce-frame-pointers=yes`, `-Zsanitize=hwaddress\|cfi\|shadow-call-stack`, `--sysroot=/dev/null` | Compiles custom sysroot `libstd`/`libcore` as Soong modules (`--sysroot=/dev/null` + explicit `--extern`) |
| **Meson & CMake (`Corrosion`)** | `rustc --version`, `rustc -vV`, `--print sysroot`, `--print target-libdir`, `--print native-static-libs` | Meson passes `-Cdefault-linker-libraries=yes`, `--emit=dep-info,link`, `--out-dir`; Corrosion delegates to `cargo metadata` + `cargo build` and links `staticlib` via `--print native-static-libs` | CMake targets consume the `note: native-static-libs:` stderr line to populate `INTERFACE_link_libraries` |
| **Nix & Distro Builders (`crane`, `dh-cargo`, `rust2rpm`)** | `cargo -vV`, `rustc -vV` | `--offline`, `--frozen`, `--remap-path-prefix=/build/=<pkg>`, `-Clink-arg=-Wl,-z,relro,-z,now` | Sets `SOURCE_DATE_EPOCH` for reproducible archive timestamps and debuginfo |
| **`sccache` (`RUSTC_WRAPPER`)** | `rustc -vV`, `--emit=dep-info` | Intercepts `rustc` CLI; runs `--emit=dep-info` first to hash all transitive source files | Rejects caching if `-Cincremental` is present or if `--crate-type=bin` without supported link outputs |

---

### 3. Major consumer profiles and reliance ranking

Basis: source + derived

1. **Major consumer requirements:**
   - **Firefox ( Gecko / `moz.build` ):** Uses Cargo with `RUSTC_BOOTSTRAP=1`
     on release builds (for `simd`, `oom` hooks, and `profiler_builtins`),
     cross-language ThinLTO (`-Clinker-plugin-lto`, matching `rustc`'s bundled
     LLVM major version to `clang`), and PGO (`-Cprofile-generate` /
     `-Cprofile-use`).
   - **Chromium (`//build/rust`):** Drives `rustc` directly from GN without
     Cargo in production builds; builds `std` from source in-tree; uses `cxx`
     and `crubit` FFI bridges; links via `clang++ -fuse-ld=lld` with
     cross-language ThinLTO and `-Zsanitize=cfi`.
   - **Fuchsia (`//build/rust`):** Drives `rustc` from GN across
     `x86_64-unknown-fuchsia`, `aarch64-unknown-fuchsia`, and
     `riscv64gc-unknown-fuchsia` plus host Linux/macOS tools; uses
     `-Zdep-info-omit-d-target`, `@rspfile`, and `-Cpanic=abort` for Zircon/kernel
     components.
   - **Linux Kernel (`rust/`):** Invokes `rustc` via Kbuild with
     `--emit=dep-info,obj,metadata` (never invoking `rustc`'s linker driver),
     requires `-Csymbol-mangling-version=v0`, `-Cpanic=abort`, and x86_64/aarch64
     mitigation `-Z` flags (`-Zfunction-return=thunk-extern` for retpoline/ITS,
     `-Zcf-protection=branch` for IBT, `-Zbranch-protection=bti,pac-ret`, and
     `-Zno-jump-tables`).
   - **AWS (`firecracker`, `s2n-quic`, `aws-lc-rs`) & Cloudflare (`pingora`,
     `quiche`):** Standard Cargo workspaces on stable `x86_64-unknown-linux-gnu`,
     `x86_64-unknown-linux-musl`, and `aarch64-unknown-linux-gnu`; rely on
     `--crate-type=staticlib` / `cdylib` (`quiche`), `build.rs` CMake/cc
     compilation (`aws-lc-rs`), and `--print=native-static-libs`.
2. **Interface reliance ranking for a replacement compiler:**
   - **Tier P0 (Mandatory for any Cargo or GN/Bazel build):** `-vV`, stdin `-`
     with `--print={file-names,sysroot,split-debuginfo,crate-name,cfg}`,
     `--crate-name`, `--edition`, `--crate-type`, `--emit={dep-info,metadata,link,obj}`,
     `--out-dir`, `-o`, `-L`, `--extern`, `--cfg`, `--check-cfg`,
     `--error-format=json`, `--json={diagnostic-rendered-ansi,artifacts,future-incompat}`,
     `@<argfile>`, `-C{opt-level,debuginfo,embed-bitcode,metadata,extra-filename,panic,linker,link-arg,codegen-units,relocation-model,symbol-mangling-version,force-frame-pointers,force-unwind-tables,incremental}`,
     and `-Z{dep-info-omit-d-target,force-unstable-if-unmarked}`.
   - **Tier P1 (Required for kernel/systems consumers):**
     `-Z{function-return,cf-protection,branch-protection,no-jump-tables,sanitize,build-std}`
     and `--sysroot=/dev/null`.
   - **Tier P2 (LLVM-coupled cross-language optimization):**
     `-Clinker-plugin-lto`, `-Cprofile-generate`, `-Cprofile-use`, and
     `-Cembed-bitcode=yes`. A non-LLVM verified backend cannot emit LLVM ThinLTO
     bitcode for `clang` and must either reject `-Clinker-plugin-lto` or run in
     object-file mode (`-Cembed-bitcode=no`).

## Boundaries

- **Proprietary Windows and Apple consumer build trees:** Windows internal OS
  components (using MSBuild / Cargo wrappers) and Apple internal Xcode builds
  were **not examined** via live `execve` tracing; only open-source build-system
  drivers (Cargo, Bazel, GN, Buck2, Kbuild, Soong, Meson, CMake Corrosion, Nix)
  were audited.
- **Cross-language ThinLTO (`-Clinker-plugin-lto`):** Bitcode compatibility
  between `rustc` and `clang` requires exact LLVM bitcode format parity and is
  **unsupported** by any non-LLVM code generator.

## Evidence

- **Cargo `rustc` driver construction (`rust-lang/cargo` `5f94df4789f005f9a352888e8355ffc645b7ed0e`):**
  - Toolchain probing (`-vV` and `--print` batch query):
    `src/cargo/util/rustc.rs` and `src/cargo/core/compiler/build_context/target_info.rs`.
  - Unit command assembly (`--error-format=json`, `--check-cfg`, `-Cmetadata`,
    `CARGO_MAKEFLAGS`): `src/cargo/core/compiler/mod.rs` and
    `src/cargo/core/compiler/check_cfg.rs`.
  - `-Zbuild-std` sysroot compilation: `src/cargo/core/compiler/standard_lib.rs`.
- **Preserved artifacts in `support/`:**
  - `support/cargo_invocation_logs.json`: complete redacted `execve` argument
    vectors and environment maps for all 50 `rustc` invocations across 7 Cargo
    modes (`check`, `build`, `build --release`, `test --no-run`,
    `bench --no-run`, `fix`, and `-Zbuild-std=core`).
  - `support/build_system_and_consumer_matrix.json`: structured matrix of
    discovery probes, core flags, environment variables, and reliance tiers
    across 9 build-system families.

## Revalidation

To revalidate Cargo's invocation contract on a newer toolchain or test a
replacement `rustc` binary:

1. Run Cargo with a logging wrapper (`RUSTC_WRAPPER`) on a minimal package
   containing `build.rs`, `src/lib.rs`, and `src/main.rs` across `cargo check`,
   `cargo build --release`, `cargo test --no-run`, and
   `cargo build -Zbuild-std=core --target x86_64-unknown-linux-gnu`.
2. Diff the captured `args` and `env` keys against
   `support/cargo_invocation_logs.json`.
