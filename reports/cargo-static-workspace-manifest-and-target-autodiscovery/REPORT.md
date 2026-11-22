# Static Cargo Workspace, Target Auto-Discovery, Path Dependency, and Config Closure Specification

## Summary

- **Zero-execution parity with `cargo metadata --no-deps`:** A static TOML + filesystem implementation (`support/probe_cargo_static.py`) derived directly from `rust-lang/cargo@930a674da900a73c1dfbe16be62c42e75bdfdfc0` matched `cargo metadata --no-deps --format-version 1` (`cargo 1.102.0-nightly (c07ac2c4d 2026-11-06)`) with **0 discrepancies** across all 4 workspaces of `google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0` (10 member packages, 172 build targets, 7 path dependencies) and 25 synthetic edge-case fixtures.
- **Pre-sandbox `cargo fetch --locked` executes untrusted `.cargo/config(.toml)` code AND defaults to CLI `git` for git dependencies:** Direct source inspection and live offline execution (`Probes 17–18`) prove that `cargo fetch --locked` invokes `rustc` twice (`rustc -vV` and `rustc - --print=file-names ...`) honoring `.cargo/config(.toml)` `[build] rustc`, `rustc-wrapper`, `rustc-workspace-wrapper`, and injecting `[env]` (including `LD_PRELOAD`) directly into `rustc` even when wrappers are cleared. Legacy `.cargo/config` silently shadows `.cargo/config.toml` in the same directory, and `include = [...]` pulls arbitrary `.toml` files recursively. Furthermore, `net.git-fetch-with-cli` now defaults to `true` whenever `git` is installed (`src/sources/git/utils.rs:1120-1126`), and Cargo recursively fetches `.gitmodules` submodules (`update_submodules`, `L407-528`). Safe pre-sandbox fetching therefore requires: (1) classifying `.cargo/config`, `.cargo/config.toml`, included config files, and `rust-toolchain(.toml)` as executable TCB, (2) running `cargo fetch --locked --manifest-path ...` from an **isolated empty `cwd` outside the repository** (proven in `Probe 18b` to bypass all repo `.cargo/config(.toml)` and `rust-toolchain(.toml)` files because both Cargo and rustup walk ancestors of `cwd`, not `--manifest-path`), populating 0-byte stub files at statically discovered target paths when omitting crate sources (`rc = 101` without stubs, `rc = 0` with), and (3) statically allowlisting external `source` entries in `Cargo.lock` (e.g., `crates.io` only) before invoking `cargo fetch --locked`—omitting `--config` for built-in `crates-io` and translating custom `registry+https://...` lockfile URLs to `https://...` (or keeping `sparse+https://...` verbatim) in `--config registries.<name>.index=...`.
- **Implicit path-dependency membership is mandatory, while `[patch]`/`[replace]`/external path deps are compiled non-members:** `google/zerocopy`'s primary `zerocopy/Cargo.toml` declares an empty `[workspace]` (`members` omitted); `zerocopy-derive` and `testutil` become workspace members *only* through `Workspace::find_path_deps` traversing `[dependencies]`, `[dev-dependencies]`, `[build-dependencies]`, and `[target.<cfg>.dependencies]` (unconditionally, even for `cfg(any())`). Conversely, `[patch.*]` (both root manifest and `.cargo/config(.toml)`), `[replace]`, and external path dependencies outside `workspace_root` (without `package.workspace` pointing back) are excluded from `workspace_members` yet still compiled and must be crawled transitively into the source closure.
- **`package.include` and `package.exclude` MUST NOT prune CI source closures:** `PathSource::list_files` models crates.io packaging, not CI build/test inputs: `zerocopy/zerocopy-derive/Cargo.toml:259` puts an active CI integration test (`tests/enum_from_bytes.rs`) in `package.exclude`, and `zerocopy/Cargo.toml:30` sets `exclude = [".*"]` (excluding `zerocopy/.cargo/config.toml`). Real crates also read files outside `src/` and outside `package_root` via `include_str!`, `#[path = ...]`, `build.rs`, `readme = "../../README.md"`, vendored source directories, and `CARGO_MANIFEST_DIR/..`.
- **Key counterintuitive Cargo rules verified in source and execution:** `workspace.exclude` does **not** expand globs (`Path::starts_with` literal prefix match only); literal `workspace.members` entries override a parent `workspace.exclude` while glob `members` yield to `exclude`; `workspace.members` uses `glob = "0.3.3"` defaults (`*` matches hidden dot-directories, `**` recurses, unexcluded matched directories lacking `Cargo.toml` hard-error); a path dep into a nested `[workspace]` beneath `workspace_root` hard-errors unless listed in `workspace.exclude`; and target auto-discovery (`infer_any`) uses `DirEntry::file_type().is_dir()` (does not follow symlinks), ignoring symlinked subdirectories under `tests/`/`benches/`/`examples/`/`src/bin/` while discovering symlinked `.rs` files and symlinked `main.rs` inside real subdirectories.

## Applicability

This report specifies static workspace, target, dependency, lockfile, and configuration discovery for `rust-lang/cargo@930a674da900a73c1dfbe16be62c42e75bdfdfc0`, cross-checked by live execution against `cargo 1.102.0-nightly (c07ac2c4d 2026-11-06)` on Linux `x86_64`, `rust-lang/rustup@2faded0d9e7fb7b597ee948bac6aa04778dddcce`, and all four Cargo workspaces of `google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0` (`zerocopy`, `anneal`, `exocrate`, `tools`).

- **Source layout note:** Compared to older Cargo revisions, `930a674da` relocated `src/cargo/core/workspace.rs` → `src/workspace/workspace.rs`, `src/cargo/util/toml/{mod,targets}.rs` → `src/workspace/parser/{mod,targets}.rs`, `src/cargo/util/context/` → `src/context/mod.rs` + `crates/cargo-util-config/src/`, and `src/doc/` → `doc/book/src/`.
- **Edition & MSRV scope:** Behavior differences across Editions 2015, 2018, 2021, and 2024 are separated explicitly. `autobins`/`autoexamples`/`autotests`/`autobenches` apply since Cargo 1.27; `autolib` applies since Cargo 1.83 (`rust-lang/cargo#14591`). Execution probes assume Linux POSIX case-sensitive path semantics.

## Findings

### 1. `[workspace]` Root Resolution, Members, Exclusions, and Implicit Path-Dep Membership

Basis: source (`rust-lang/cargo@930a674da`: `src/workspace/workspace.rs`, `src/workspace/parser/mod.rs`, `Cargo.toml`) + documentation (`doc/book/src/reference/workspaces.md`) + execution (`Probes 1–8b, 16, 19`)

#### 1.1 Workspace Root Resolution (`Workspace::find_root`)

Given an absolute `manifest_path` (`workspace.rs:178-197, 820-838, 2191-2262`):
1. Specifying both `[workspace]` and `package.workspace` in one manifest is a hard error (`parser/mod.rs:282-285`).
2. If `manifest_path` defines `[workspace]` (and does not exclude itself), `root_manifest = Some(manifest_path)`.
3. Else if `package.workspace = "<rel>"`, `root_manifest = Some(normalize_path(manifest_path.parent() / rel / "Cargo.toml"))` (`read_root_pointer`, `workspace.rs:2232-2240`).
4. Else walk ancestor directories starting at `manifest_path.parent().parent()` (`paths::ancestors(manifest_path, None).skip(2)`, `find_root_iter`, `workspace.rs:2242-2262`), stopping before crossing a directory ending in `target/package` (`L2247`) or `$CARGO_HOME` (`L2253-2259`). At each ancestor with `Cargo.toml`, if it has `[workspace]` and `!is_excluded(manifest_path)`, return that ancestor; if excluded, continue walking upward; if it has `package.workspace`, follow that pointer.
5. If no ancestor matches, `root_manifest = None` (standalone single-package workspace).

#### 1.2 `workspace.members` Globs and `workspace.exclude` Precedence

- **`workspace.members` (`workspace.rs:10, 2036-2079`):** Expands patterns with `glob = "0.3.3"` default `MatchOptions::new()` (`require_literal_leading_dot = false`, `case_sensitive = true`). Consequently:
  - `*` **matches hidden dot-directories** (`crates/.hidden_crate`, `Probe 5a`), and `**` matches recursively (`deep/**/pkg`, `Probe 5a`).
  - Non-directory matches are silently skipped (`expanded_path.is_dir()`, `L2052`, `Probe 4a`).
  - If a glob matches nothing, Cargo pushes the literal pattern path (`L2046-2047`), which hard-errors in `find_path_deps` unless excluded (`Probe 19`).
  - Because `is_excluded` runs at `workspace.rs:953` *before* manifest loading at `L962`, an excluded non-crate directory matched by a glob is silently skipped (`Probe 4a`), whereas an unexcluded matched directory lacking `Cargo.toml` is a **hard error** (`Probe 5b`).
- **`workspace.exclude` (`WorkspaceRootConfig::is_excluded`, `workspace.rs:1973-1987`):**
  ```rust
  fn is_excluded(&self, manifest_path: &Path) -> bool {
      let excluded = self.exclude.iter()
          .any(|ex| manifest_path.starts_with(self.root_dir.join(ex)));
      let explicit_member = match self.members {
          Some(ref members) => members.iter()
              .any(|mem| manifest_path.starts_with(self.root_dir.join(mem))),
          None => false,
      };
      !explicit_member && excluded
  }
  ```
  1. **`workspace.exclude` never expands globs:** `exclude = ["crates/*"]` does not exclude `crates/still_included` (`Probe 4c`).
  2. **Literal `members` override parent `exclude`:** `members = ["crates/keep_me"]` + `exclude = ["crates"]` sets `explicit_member = true` and includes `keep_me` (`Probe 4b`).
  3. **Glob `members` yield to `exclude`:** `members = ["crates/*"]` + `exclude = ["crates/skip_me"]` has `explicit_member = false`, so `exclude` wins (`Probe 4a`).

#### 1.3 Implicit Path-Dep Membership, Nested Workspaces, `default-members`, and `workspace.dependencies`

- **Implicit path-dependency traversal (`find_members` L848-925, `find_path_deps` L927-981):** Cargo invokes `find_path_deps` on every expanded `workspace.members` entry *and unconditionally* on `root_manifest` (`L888`). Inside `find_path_deps`:
  1. A `path` dep **outside** `workspace_root` is skipped unless its `find_root` points back to `self.root_manifest` via `package.workspace = "<rel>"` (`L941-948`, `Probes 2–3`).
  2. Excluded paths are skipped (`L950-956`).
  3. Otherwise the manifest is added to `self.members` (`L959`) and Cargo recurses over **all** `path` deps across `[dependencies]`, `[dev-dependencies]`, `[build-dependencies]`, and `[target.<cfg>.(dev-|build-)dependencies]` unconditionally—even for `cfg(any())` (`Probe 1`).
  4. **Nested `[workspace]` trap (`Probes 6a–6b`):** Because `find_path_deps` inserts the manifest into `self.members` before checking for nested `[workspace]`, a `path` dep into a nested `[workspace]` under `workspace_root` **hard-errors** in `validate_workspace_roots` (`L1048-1079`, `multiple workspace roots found in the same workspace`) unless that directory is also listed in the outer `workspace.exclude`.
  5. Non-root member `[profile.*]`, `[replace]`, and `[patch]` tables are ignored with warnings (`validate_manifest`, `L1177-1240`).
- **`workspace.default-members` (`L865-922`, `Probe 16`):** When explicitly set at `root_manifest`, globs expand via `members_paths` (skipping entries matched by glob and excluded by `workspace.exclude`). Otherwise, virtual workspaces default to all members and non-virtual workspaces default strictly to `[current_manifest]`.
- **`workspace.dependencies` (`parser/mod.rs:1100-1127, 1195-1284`, `Probe 7`):** When a member writes `foo = { workspace = true }`, `detailed.path` resolves relative to **`workspace_root`** (not the member directory), and any `path` key on the member entry is discarded into `_unused_keys`. Uninherited `workspace.dependencies` path entries are **not** added as workspace members.

---

### 2. Target Auto-Discovery, `build`, `readme`, `license-file`, and Package Closure

Basis: source (`src/workspace/parser/targets.rs`, `src/workspace/parser/mod.rs`, `src/sources/path.rs`) + documentation (`doc/book/src/reference/cargo-targets.md`) + execution (`Probes 9–14, 20`)

#### 2.1 Conventional Paths, Depth, Dotfiles, and Symlink Asymmetry

From `targets.rs:725-798` (`Probe 12`):

| Target Kind | Conventional Paths | Auto Flag (MSRV) | Existence / Type Check |
| :--- | :--- | :--- | :--- |
| `lib` | `src/lib.rs` (name: `pkg_name.replace('-', '_')`) | `autolib` (1.83) | `Path::exists()` (follows symlinks) |
| `bin` | `src/main.rs` (name: `pkg_name`), `src/bin/*.rs`, `src/bin/*/main.rs` | `autobins` (1.27) | `src/main.rs`: `exists()`; `src/bin`: `infer_from_directory` |
| `example` | `examples/*.rs`, `examples/*/main.rs` | `autoexamples` (1.27) | `infer_from_directory` |
| `test` | `tests/*.rs`, `tests/*/main.rs` | `autotests` (1.27) | `infer_from_directory` |
| `bench` | `benches/*.rs`, `benches/*/main.rs` | `autobenches` (1.27) | `infer_from_directory` |
| `custom-build` | `build.rs` (name: `build-script-<stem>`) | `package.build` | `Path::is_file()` (follows symlinks, rejects dirs) |

- **Depth = 1, no dotfiles, `.rs` only:** `infer_from_directory` reads only immediate children (`fs::read_dir`), skips names starting with `.` (`is_not_dotfile`, `L796-798`), ignores non-`.rs` files, and ignores deeper nesting (`tests/a/b/main.rs`) or `mod.rs` (`tests/a/mod.rs`).
- **Symlink asymmetry (`infer_any`, `targets.rs:761-769`):** Because `DirEntry::file_type().is_dir()` does **not** follow symlinks, a **symlinked subdirectory** (`tests/sym_dir -> ...`) is ignored (`is_dir() == false`), whereas a **symlinked `.rs` file** (`tests/sym_file.rs -> ...`) and a **symlinked `main.rs` inside a real subdirectory** (`main.exists()` follows symlinks, `L785`) are both discovered (`Probe 12`).

#### 2.2 Edition Defaults, `auto<kind> = false`, and Explicit Target Path Inference

From `targets.rs:147-217, 292-367, 612-623, 800-894, 1056-1110` (`Probes 9–11, 20`):
- **Omitted `package.edition` defaults to `2015`** (`parser/mod.rs:1381, 1398`, `Probe 20`).
- **For `bin`/`example`/`test`/`bench` (`toml_targets_and_inferred`, `L800-894`):** When no explicit `[[kind]]` table exists, auto-discovery defaults to `true` on all editions (including 2015) unless `auto<kind> = false`. When at least one explicit `[[kind]]` exists, omitted `auto<kind>` defaults to **`false` on Edition 2015** and **`true` on Editions 2018/2021/2024** (`Probes 9, 20`).
- **Explicit target omitting `path` still runs inference even when `auto<kind> = false` (`are_normalized_`, `L612-623`):** If `autobins = false` and `[[bin]] name = "foo"` omits `path`, `are_normalized_` returns `false` so Cargo computes `inferred`, suppresses unmentioned targets, and resolves `"foo"` via `target_path` (`L1056-1110`, requiring a unique match in `inferred`, plus Edition 2015 legacy fallbacks `src/<name>.rs`/`src/main.rs`/`src/bin/main.rs` for `bin` and `src/bench.rs` for `bench`, `Probes 9, 11`).
- **`[lib]` & `autolib` (`normalize_lib`, `L147-217`, `Probe 10`):** `autolib = false` with no `[lib]` suppresses `src/lib.rs`; with `[lib]` present (even if `autolib = false`), omitted `name` defaults to `pkg_name.replace('-', '_')` and omitted `path` defaults to `src/lib.rs` (or `src/<name>.rs` on Edition 2015). `proc-macro = true` (or deprecated `proc_macro = true`, rejected in Edition 2024) sets `crate_types = ["proc-macro"]`.
- **`package.build` (`targets.rs:1114-1150`, `Probe 13`):** Omitted auto-detects `build.rs` via `.is_file()` (directory named `build.rs` ignored); `false` disables; `true` sets `build.rs` unconditionally even if absent; `"custom.rs"` normalizes relative to `package_root`. (`build = [...]` and `metabuild` are nightly-only.)
- **`package.readme` & `package.license-file` (`parser/mod.rs:774-890, 1138-1155`, `Probe 14`):** Omitted `readme` checks `["README.md", "README.txt", "README"]` in order via `.is_file()`; `readme = false` disables; `readme = true` sets literally `"README.md"` (no fallback to `README.txt`); `readme.workspace = true` runs auto-detection in `ws_root` even if `workspace.package.readme` is omitted, then rewrites relative to `package_root` via `pathdiff::diff_paths`. `license-file` has no auto-detection and supports `workspace = true` via `diff_paths`.

#### 2.3 Why `package.include` / `package.exclude` Must Not Prune CI Source Closures

Basis: source (`src/sources/path.rs:583-971`, `google/zerocopy@907b9175`) + derived

`PathSource::_list_files` uses `ignore = "0.4.25"` and `gix = "0.90.0"` (`include` overrides both `exclude` and `.gitignore`; non-Git trees prepend implicit `".*"` to `exclude`), stripping `target/` and nested `Cargo.toml` subdirectories. In real workspaces this diverges sharply from CI build/test inputs:
1. `zerocopy/zerocopy-derive/Cargo.toml:259` excludes active CI test `tests/enum_from_bytes.rs` in `package.exclude` to shrink crates.io tarballs.
2. `zerocopy/Cargo.toml:30` sets `exclude = [".*"]`, excluding `zerocopy/.cargo/config.toml`.
3. Crates routinely read non-`src/` and out-of-package files at compile/test time: `zerocopy/src/util/macros.rs:918` (`include_str!("../benches/formats/...")`), `zerocopy/benches/*.rs` (`#[path = "formats/..."]`), `zerocopy/tests/codegen.rs:116` (`CARGO_MANIFEST_DIR` bench fixtures), `zerocopy/build.rs` (parsing `Cargo.toml`), `anneal/trusted/cargo-anneal/Cargo.toml` (`readme = "../../README.md"`), and `anneal/trusted/audit` tests reading `CARGO_MANIFEST_DIR/../../vendor/lean-miri`.

Sound static closure expansion therefore includes: (a) whole discovered package directories (members + transitive external path deps + `[patch]`/`[replace]` crates) minus `target/` and nested non-closure `Cargo.toml` subtrees, (b) out-of-package manifest-referenced paths (`readme`, `license-file`, explicit target/build paths escaping via `..`), (c) workspace `Cargo.lock`, discovered `.cargo/config(.toml)` + `include`s + `[source.*]` (`directory`/`local-registry`) trees + `rust-toolchain(.toml)`, and (d) explicit consumer-declared extra paths for runtime `CARGO_MANIFEST_DIR/..` reads and non-standard manifests (`zerocopy/Cargo.toml.std`).

---

### 3. Complete Inventory of Local `path` Dependency Tables

Basis: source (`crates/cargo-util-schemas/src/manifest/mod.rs:35-68, 860-1050, 1638-1660`, `src/workspace/parser/mod.rs:466-641, 904-998, 1100-1127, 2153-2281, 2590-2613`) + execution (`Probes 1–3, 7–8b, 15`)

| Location | TOML Table(s) | Legacy Alias (`< Ed. 2024`) | `path` Resolution Base | Workspace Member? |
| :--- | :--- | :--- | :--- | :--- |
| Member / root `Cargo.toml` | `[dependencies]`, `[dev-dependencies]`, `[build-dependencies]` | `[dev_dependencies]`, `[build_dependencies]` | Package dir | Yes (if inside `ws_root` or `package.workspace` back-pointer, and not excluded) |
| Member / root `Cargo.toml` | `[target.<cfg_or_triple>.(dev-\|build-)dependencies]` | `...dev_dependencies`, `...build_dependencies` | Package dir | Yes (evaluated unconditionally, including `cfg(any())`) |
| Member / root `Cargo.toml` | Any above with `{ workspace = true }` | — | **`ws_root`** (member `path` ignored) | Yes when inherited by a member |
| Root `Cargo.toml` only | `[workspace.dependencies]` | — | `ws_root` | Only if inherited by a member |
| Root `Cargo.toml` only | `[patch.<registry_or_url>]` | — | `ws_root` | **No** (compiled; crawl transitively) |
| Root `Cargo.toml` only | `[replace]` (deprecated; exclusive with `[patch]`) | — | `ws_root` | **No** (compiled; crawl transitively) |
| `.cargo/config(.toml)` / `include` | `[patch.<registry_or_url>]` | — | `Definition::root` (`p.parent().parent()`, overrides manifest `[patch]`) | **No** (compiled; crawl transitively) |
| Nightly `-Zpath-bases` | Detailed dep with `base = "workspace" \| "<name>"` | — | `ws_root` or config `[path-bases.<name>]` | Same as containing table |

*(Note: `[project]` is accepted as an alias for `[package]` in Editions `< 2024` and rejected in Edition 2024, `parser/mod.rs:1412-1420`, `Probe 15`.)*

---

### 4. `Cargo.lock`, `.cargo/config(.toml)`, `rust-toolchain(.toml)`, and `cargo fetch --locked` Execution Hazards

Basis: source (`rust-lang/cargo@930a674da`: `src/workspace/workspace.rs:357-392, 711-745`, `crates/cargo-util-config/src/{loader,definition,schema}.rs`, `src/context/mod.rs:461-487`, `src/ops/cargo_fetch.rs:35-37`, `src/compiler/build_context/target_info.rs:176-216, 1004-1011`, `src/sources/git/utils.rs:407-528, 1120-1141`, `src/util/rustc.rs:353-372`; `rust-lang/rustup@2faded0d9e`: `src/config.rs:208-229, 661-740`) + execution (`Probes 17–18`)

- **`Cargo.lock` location (`workspace.rs:357-392, 724-738`):** Defaults to `<workspace_root>/Cargo.lock` (or `<package_root>/Cargo.lock` for standalone packages). Precedence of overrides: `--lockfile-path` > `CARGO_RESOLVER_LOCKFILE_PATH` > `.cargo/config(.toml)` `[resolver] lockfile-path` (resolved via `ConfigRootRelativePath`, must end in `Cargo.lock`).
- **`.cargo/config` vs. `.cargo/config.toml` and `include` (`loader.rs:53-271`, `definition.rs:58-90`):**
  - Cargo walks ancestors starting from **`cwd`** (NOT `--manifest-path`) up to `/`, then `$CARGO_HOME`.
  - In any `.cargo/` directory, **`.cargo/config` silently shadows `.cargo/config.toml`** (`get_file_path`, `L195-240`, `Probe 17`).
  - Stabilized `include = ["a.toml", { path = "b.toml", optional = true }]` (`L95-158`) resolves relative to the containing config file's directory (requiring `.toml` extension, forbidding globs), detects cycles, and has lower precedence than the including file.
  - Precedence: `--config` > `CARGO_*` env > closer-to-`cwd` config > its `include`s > ancestor configs > `$CARGO_HOME/config(.toml)`.
  - `ConfigRootRelativePath` (`[source.*] directory`/`local-registry`, `[patch.*] path`, `[resolver] lockfile-path`, `[path-bases]`) resolves relative to `p.parent().parent()` (two levels up from the config file).
- **`rust-toolchain(.toml)` (`rustup` only):** Cargo never reads `rust-toolchain(.toml)` (`src/util/rustc.rs:353-372`); `rustup` walks upward from `cwd`, where `rust-toolchain` shadows `rust-toolchain.toml`, and `toolchain.path` executes arbitrary binaries (`rustup@2faded0d9e`, `src/config.rs:661-740`).
- **Pre-sandbox `cargo fetch --locked` RCE & network-abuse vectors (`source` + `execution`):**
  1. **`.cargo/config(.toml)` code execution (`Probes 17 & 18`):** `cargo_fetch.rs:35-37` builds `RustcTargetData`, spawning `rustc` twice (`rustc -vV` and `rustc - --print=file-names ...`). Live offline execution proved `[build] rustc`, `[build] rustc-wrapper`, `[build] rustc-workspace-wrapper`, AND **`[env] LD_PRELOAD`** (with zero wrappers set!) all execute during `cargo fetch --locked`.
  2. **Mitigation proven by execution (`Probe 18b` + target-stub & registry-index probes):** Running `cargo fetch --locked --manifest-path <repo>/<ws>/Cargo.toml` with **`cwd` set to an empty temporary directory outside the repository** (and isolated `CARGO_HOME`) succeeded (`rc = 0`) while 100% bypassing repository `.cargo/config(.toml)` (`[build] rustc-wrapper` and `[env] LD_PRELOAD`) and `rust-toolchain(.toml)`. Two additional live execution constraints govern minimal containerized fetch trees (`cargo 1.102.0-nightly (c07ac2c4d 2026-11-06)`):
     - **Target stubs are required, while `readme` / `license-file` need not be materialized; `RUSTUP_HOME` must survive `HOME` isolation:** Invoking `cargo fetch --locked --manifest-path <ws>/Cargo.toml` over a manifest-only directory containing `Cargo.toml` + `Cargo.lock` without any discovered target source file **fails** (`rc = 101`: `no targets specified in the manifest`); adding a 0-byte empty stub at each statically discovered target path (e.g., `src/lib.rs`) succeeds (`rc = 0`) without exposing real crate source files, **even when `Cargo.toml` declares unmaterialized parent-relative `package.readme = "../../README.md"` and `package.license-file = "../../LICENSE"`** (`2026-11-22` live execution probe). However, when `cargo` on `PATH` is the `rustup` proxy shim and `HOME` is overridden to an empty temporary directory (`HOME=/empty-cwd`) while `cwd = /empty-cwd` has no `rust-toolchain(.toml)`, omitting `RUSTUP_HOME` causes `rustup` to look up `$HOME/.rustup/settings.toml` and **fail** (`rc = 1`: `rustup could not choose a version of cargo to run`); preserving `RUSTUP_HOME` (e.g., `/usr/local/rustup` from OCI `Config.Env` or the host's `~/.rustup` in native fallback) restores `rc = 0` without exposing repository config files.
     - **Custom registry `--config registries.<name>.index` URL syntax:** Built-in `crates-io` requires no `registries.crates-io.index` override. For custom registries (`registry = "<name>"`), passing the raw `Cargo.lock` `SourceId` string `registry+https://...` to `--config registries.<name>.index=...` **fails** URL/fetch parsing (`failed to fetch 'registry+https://...'`), whereas stripping `registry+` to `https://...` (git index) or keeping `sparse+https://...` verbatim (sparse HTTPS index, zero git) parses validly (verified against loopback `127.0.0.1:1` with `--config net.retry=0`).
  3. **Git dependency CLI & submodule fetch vector (`src/sources/git/utils.rs:407-528, 1120-1141`):** Even with isolated `cwd`, Cargo's `net.git-fetch-with-cli` **defaults to `true` whenever `git` is installed** (`unwrap_or_else(|| git_version().is_some())`, `L1123`), invoking external `git fetch` on untrusted `git = "..."` URLs (including `https://`, `ssh://`, `file://`) and recursively fetching arbitrary `.gitmodules` submodules (`update_submodules`, `L407-528`). Pre-sandbox `cargo fetch --locked` must therefore statically verify that every external `source` in `Cargo.lock` belongs to an allowlist (default: `registry+https://github.com/rust-lang/crates.io-index` only), or skip online fetch entirely when sources are vendored offline (e.g., `zerocopy/vendor/`).

---

### 5. Differential Verification Against `google/zerocopy@907b9175` and Synthetic Suite

Basis: execution (`support/probe_cargo_static.py` → `support/probe_results.json`, `cargo 1.102.0-nightly (c07ac2c4d 2026-11-06)`, Python `3.13.15`)

| Workspace (`google/zerocopy@907b9175`) | Virtual? | Members Matched | Default Members | Targets Matched | Path Deps Matched | Config & Notable Quirks | Diffs vs. `cargo metadata` |
| :--- | :--- | :--- | :--- | ---: | ---: | :--- | :--- |
| `zerocopy` | No | `3` (`zerocopy`, `zerocopy-derive`, `testutil`) | `zerocopy` | `151` | `6` (incl. `cfg(any())`, cyclic `zerocopy-renamed -> ../`) | Empty `[workspace]`; `zerocopy/.cargo/config.toml` (`vendor/`); `zerocopy-derive` `exclude` drops active test; secondary `Cargo.toml.std` | **0** |
| `anneal` | Yes | `3` (`anneal-audit`, `cargo-anneal`, `anneal-rustc-capture`) | All `3` | `17` | `1` (`anneal-audit -> cargo-anneal`) | `cargo-anneal` `readme = "../../README.md"`, pathless `[[bin]]`/`[[example]]`; tests read `CARGO_MANIFEST_DIR/../..` | **0** |
| `exocrate` | No | `1` (`exocrate`) | `exocrate` | `1` | `0` | Auto-detected `README.md`; binary fixture `tests/my-tool-deps.tar.zst` | **0** |
| `tools` | Yes | `3` (`cargo-zerocopy`, `generate-readme`, `ui-runner`) | All `3` | `3` | `0` | CRLF manifests; `[workspace.package]` & `[workspace.dependencies]` inheritance | **0** |

All **25/25 synthetic probes** in `support/probe_results.json` passed, confirming every rule in Sections 1–4 (implicit path-dep membership, external path deps with/without `package.workspace`, `exclude` vs. glob/literal `members` and non-expanding globs, hidden dirs & `**`, missing-manifest error cases, nested `[workspace]` error vs. `exclude`, `workspace.dependencies`, `[patch]`/`[replace]`, Edition 2015 vs. 2024 `autotests`, `autolib`, `autobins = false` explicit path inference, depth/dotfile/symlink asymmetry, `package.build` modes, `readme`/`license-file` inheritance, legacy `[project]`/`*_dependencies`, `default-members` with excluded member, omitted-edition 2015 default, and live `cargo fetch` RCE + isolated-`cwd` mitigation).

## Boundaries

- **`known not to apply`:** `package.include`/`package.exclude` do not define CI build/test source closures; Cargo does not read `rust-toolchain(.toml)`; `workspace.exclude` does not expand globs; non-root member `[patch]`/`[replace]`/`[profile.*]` tables are ignored.
- **`unsupported` / unstable Cargo features (`not examined` in execution):** Unstable `-Zpath-bases` custom config bases (`[path-bases.<name>]`), embedded single-file Cargo scripts (RFC 3424), `package.metabuild`, `build = [...]` (`multiple-build-scripts`), and `-Zbindeps` / custom JSON target specs (`package.default-target` / `forced-target`) were inspected in source only (fail-closed handling recommended for static parsers).
- **`not examined`:** Windows/macOS case-insensitive filesystems and Windows path prefixes; live execution of malicious `git = "..."` / `.gitmodules` payloads during `cargo fetch --locked` (established via `source` inspection of `src/sources/git/utils.rs`).

## Evidence

All evidence was gathered or executed on `2026-11-21`:

- **`rust-lang/cargo@930a674da900a73c1dfbe16be62c42e75bdfdfc0`:** `Cargo.toml` (`glob 0.3.3`, `ignore 0.4.25`, `pathdiff 0.2.3`, `toml 1.1.5`, `gix 0.90.0`), `src/workspace/workspace.rs` (L178-197, L321-395, L517-620, L711-745, L820-981, L1048-1079, L1177-1240, L1973-1987, L2036-2111, L2191-2262), `src/workspace/parser/targets.rs` (L48-367, L405-577, L612-623, L725-894, L1056-1150), `src/workspace/parser/mod.rs` (L236-288, L314-998, L1100-1284, L1305-1926, L2153-2281, L2413-2613, L2984-3008), `crates/cargo-util-schemas/src/manifest/mod.rs` (L35-222, L860-1050, L1463-1510, L1638-1660), `crates/cargo-util-config/src/{loader.rs,config_store.rs,definition.rs,schema.rs}`, `src/context/mod.rs`, `src/sources/{config.rs,path.rs,git/utils.rs,git/source.rs}`, `src/ops/{cargo_fetch.rs,lockfile.rs}`, `src/compiler/build_context/target_info.rs`, `src/util/rustc.rs`, `doc/book/src/reference/{cargo-targets.md,workspaces.md}`.
- **`rust-lang/rustup@2faded0d9e7fb7b597ee948bac6aa04778dddcce`:** `src/config.rs` (L208-229, L661-740).
- **`google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0`:** All 14 primary workspace manifests, `zerocopy/Cargo.toml.std`, `zerocopy/.cargo/config.toml`, `zerocopy/build.rs`, and source scan for `include_*!`/`#[path`/`CARGO_MANIFEST_DIR`.
- **Preserved executable probe & results:** `support/probe_cargo_static.py` (Python 3.13 stdlib `tomllib`, zero `cargo` calls in parser) and `support/probe_results.json` (run against `cargo 1.102.0-nightly (c07ac2c4d 2026-11-06)` on Linux `x86_64`, exit `0`, 4/4 `zerocopy` workspaces and 25/25 synthetic probes passing).
- **Additional live `cargo fetch --locked` CLI execution probes (`2026-11-21` and `2026-11-22`, same `cargo 1.102.0-nightly` binary on Linux `x86_64`):** (1) Manifest-only dir without `src/lib.rs` (`rc = 101`, `no targets specified in the manifest`) vs. adding 0-byte `src/lib.rs` (`rc = 0`, including when `Cargo.toml` declares unmaterialized `readme = "../../README.md"` and `license-file = "../../LICENSE"`), isolated empty `cwd` vs. workspace `cwd` with malicious `.cargo/config.toml` `[build] rustc-wrapper` + `[env] LD_PRELOAD` (`rc = 0` vs. `rc = 101`), and `HOME=/empty-cwd` without vs. with `RUSTUP_HOME` preserved (`rc = 1` `rustup could not choose a version of cargo to run` vs. `rc = 0`); (2) Custom registry loopback probes (`127.0.0.1:1`, `--config net.retry=0`) verifying `--config registries.corp.index="registry+https://..."` fails URL handling while `"https://..."` and `"sparse+https://..."` parse validly, and built-in `crates-io` omits `--config`.

## Revalidation

1. **Run the preserved differential probe:**
   ```console
   python3 support/probe_cargo_static.py
   ```
   (Pass `--repo-path /path/to/zerocopy --rev 907b9175fee081872ec883ca4709e6ad922f8ed0` to include the 4-workspace `google/zerocopy` differential suite alongside the 25 self-contained synthetic probes.) Confirm exit `0` and zero diffs in the output.
2. **Re-check minimal stub and custom-registry index URL rules:** Run `cargo fetch --locked --manifest-path <tmp_ws>/Cargo.toml` from an empty external `cwd` with vs. without a 0-byte `src/lib.rs`, and pass `--config net.retry=0 --config registries.corp.index="<url>"` for `registry+https://127.0.0.1:1/...`, `https://127.0.0.1:1/...`, and `sparse+https://127.0.0.1:1/...`.
3. **Audit upstream Cargo changes:** Diff `rust-lang/cargo` from `930a674da900a73c1dfbe16be62c42e75bdfdfc0` across `src/workspace/workspace.rs`, `src/workspace/parser/{targets.rs,mod.rs}`, `crates/cargo-util-config/src/loader.rs`, `src/ops/cargo_fetch.rs`, and `src/sources/git/utils.rs`.
