<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal Testing and Verification Architecture Specification

> **Status: Target Architecture (Policy Confirmed: `D1-A`–`D4-A`).**
>
> **Document Structure:** This specification is organized into three strictly
> separated partitions:
> - **Partition 1 (§1–§6) — Normative Architecture Specification:** Timeless
>   structural, API, corpus, regression-gate, and CI specification spanning
>   the landed Wave 0–2A baseline and remaining target Waves 2B–4 (relocating
>   alongside sibling `anneal/docs/` specs if `#4125` merges).
> - **Partition 2 (§7) — Decision Rationale and Eliminated Alternatives:**
>   Comparative architectural justification and falsified or dominated
>   alternatives grounded in repository measurements.
> - **Partition 3 (§8–§9) — Confirmed Policy Decisions (`D1-A`–`D4-A`), Outcome
>   Contract, and Epistemic Calibration:** Maintainer-approved policy
>   selections, the complete `(C+, C-)` contract ledger, and verification
>   calibration.

---

## Partition 1 — Normative Architecture Specification

### 1. Purpose, Scope, Guarantees, and Non-Goals

Anneal verifies Rust source code by extracting post-cleanup MIR
(`anneal-rustc-capture`), staging model, specification, and proof modules under
sandboxed Lean 4 compilation (`cargo-anneal`), and auditing the resulting proof
obligations and repository trust boundaries (`anneal-audit`,
`TrustedBoundary.lean`, `SpecPreflight.lean`, and external NDJSON proof
checkers). Because positive end-to-end proofs succeed silently if a soundness
check is weakened, omitted, or bypassed, Anneal's test architecture treats
**soundness rejection, semantic correspondence, TCB containment, hermetic
packaging, and elaboration scaling** as co-equal verification invariants rather
than line-coverage targets.

#### 1.1 Architectural Guarantees

1. **Zero Test Contamination of the Human-Audited TCB:** Production verification
   crates reside exclusively under `anneal/trusted/`. Integration test
   harnesses, shared testkits, synthetic `.olean` forge scripts, and test
   corpora reside under `anneal/tests/`, excluded from `crates.io` publication
   (`publish = false`) and forbidden from being imported by `anneal/trusted/`.
2. **Compile-Time Lifecycle Safety and Subprocess Containment:** Shared test
   scaffolding (`anneal-testkit`) encodes fixture staging, read-only directory
   permissions (`0o555`), process-group + process-wide subreaper supervision
   (paired with kernel `PR_SET_PDEATHSIG(SIGKILL)` on `ExecSeal` grandchildren
   and `cargo-nextest` process-per-test isolation), and diagnostic retention in
   Rust typestates so malformed test setups fail to compile and timed-out
   `lean`/`rustc` descendants cannot outlive a test run.
3. **Hermetic Split-Store and Dynamic-Linker Fidelity:** Linux ELF `PT_INTERP`,
   `DT_RUNPATH` vs. `DT_RPATH`, `/proc/self/maps` `(st_dev, st_ino)` DSO
   residency, and split-output Nix/content-addressed symlink forests
   (`symlinkJoin`) are exercised deterministically inside unprivileged
   user/mount namespaces (`bubblewrap`) without requiring host-global Nix
   installations.
4. **Polarity-Locked Soundness and Public-Entrypoint Guard Sensitivity:**
   Declarative `adversarial/` fixtures lock failure stage, diagnostic scope,
   and pass/fail polarity (`ANNEAL_BLESS=1` cannot flip `pass` $\leftrightarrow$
   `fail`), and link directly to single-guard ablation entries verifying a
   `100%` kill rate through public CLI/library entrypoints across both Lean and
   Rust TCB guards.
5. **Dual-Layer Differential Equivalence:** Semantic drift between
   `rustc`/`Miri` and `Trusted.MirSemantics` is gated by directional-refinement
   differential execution, while proof-kernel trust on Lean `v4.35.0+` is gated
   by disjoint `leanexport` NDJSON streams, a safe-Rust alpha-equivalence DAG
   comparator, and multi-kernel replay inside `ExecSeal`.
6. **First-Customer Verbatim Realism and Bounded Resource Scaling:** Real-crate
   suites anchor on unmodified `zerocopy/src/` items (paired with
   `zerocopy/proofs/`, excluded from `zerocopy/Cargo.toml` crate packaging)
   alongside SHA-256-pinned external crates, while cold `lean -j1` elaboration
   time, child peak RSS (`ru_maxrss`), 3-part Lean `module` `.olean*` sizes, and
   constructive axiom footprints are enforced by dedicated regression budgets.

#### 1.2 Explicit Non-Goals

- **No Ad-Hoc Line-Coverage Padding Before Monolith & Corpus Scaffolding:**
  Writing bespoke per-file unit/integration patches to inflate line coverage
  while remaining monolithic test files (`target_audit.rs`, `typed_capture.rs`,
  `cli.rs`, `itree_differential.rs`) and Wave-3 declarative corpora are
  still converging is prohibited; targeted line- and branch-coverage expansion
  is deferred to Wave 4.
- **No Test-Only Specification Languages:** The test suite tests Anneal's real
  specification and request surfaces; it does not grow or maintain an
  independent Rust doc-comment specification compiler outside `trusted/`.
- **No Ambient Host or Network Reliance in PR Gates:** Workspace, boundary, and
  corpus suites execute offline (`--locked`, `--offline`, `--network=none` /
  `ExecSeal`) with zero reliance on ambient `$HOME/.cargo`, `$HOME/.elan`, or
  live registry fetches.
- **No Binary `.olean` Mutation Stubbing:** Under Lean 4 `module` encapsulation
  (`.olean`, `.olean.server`, `.olean.private`) and NDJSON external-kernel
  verification, mutating binary `.olean` files on disk is excluded; any
  proof-body pruning operates strictly over exported NDJSON declarations.

---

### 2. TCB-Isolated Two-Zone Workspace Architecture

#### 2.1 Directory Layout and Crate Topology

`anneal/Cargo.toml` partitions all Rust workspace members into two disjoint
trust zones—production TCB crates under `anneal/trusted/` (`Zone::Trusted`) and
non-publishing verification/test crates under `anneal/tests/` (`Zone::Tests`):

```text
anneal/
├── Cargo.toml                         # Virtual [workspace] only (resolver = "2")
├── Cargo.lock                         # Version 4; crates.io SHA-256 + workspace members only
├── .config/
│   └── nextest.toml                   # Process-per-test profiles, slow-timeouts, heavy-lean slots
├── ci/
│   ├── check_guard_mutation.py        # Lean TCB + auditor single-guard mutation runner (205 guards)
│   ├── check_minirust_pin.py          # MiniRust pin, Lean hygiene & SpecAnchor CI check (+ manual --check-axioms)
│   ├── perf_tracking.py               # Telemetry collector, validator, & Tier A/B regression gate
│   ├── perf_budgets.json              # Tier A time, RSS, 3-part .olean*, binary, & unit budgets
│   ├── render_perf_dashboard.py       # Zero-CDN static HTML/JSON dashboard generator
│   └── verify_{zerocopy,starnix_e2e}.py
├── trusted/                           # Zone::Trusted ( rank = 0 ) — Human-Audited TCB
│   ├── root-manifest.sha256           # Pins Cargo.toml, Cargo.lock, flake.nix, flake.lock
│   ├── audit/                         # package = "anneal-audit"
│   │   ├── Cargo.toml
│   │   ├── TrustedBoundary.lean       # Offline Pass-1/Pass-2 audit & v4.34.1 fallback
│   │   ├── SpecPreflight.lean         # Target (#4109): runtime preflight + module index (v4.35.0+)
│   │   ├── library-lock.json
│   │   └── src/{lib,main,cli,cargo_boundary,miri_pin,repo_audit}.rs
│   ├── cargo-anneal/                  # package = "cargo-anneal" (published CLI/lib)
│   │   ├── Cargo.toml                 # Zero tests/ exclusion list; zero wait-timeout dev-dep
│   │   ├── build.rs                   # Generates $OUT_DIR/{bundled_resources.rs,bundled_theory.json}
│   │   ├── assets/scalar/             # Runtime assets for `cargo-anneal skill --example` (97L)
│   │   ├── skills/cargo-anneal/
│   │   └── src/{lib,main,bundle,cli,diagnostics,init,olean_cache,sandbox,setup,stage,target,theory_bundle,toolchain,trusted_bundle,verify}.rs
│   │       # (target #4016 adds ndjson_comparator.rs)
│   ├── rustc-capture/                 # package = "anneal-rustc-capture" (#![feature(rustc_private)])
│   │   ├── Cargo.toml
│   │   └── src/{lib,main,capture,driver,extract,identity,ir,lean,mono,publication}.rs
│   ├── lean/                              # Trusted.lean + Trusted/ MIR AST, model, & semantics (19 files)
│   └── correspondence/                    # Trusted/Correspondence* Pass-2 simulation adapter (7 files)
├── theory/                            # Pass-1 untrusted proof libraries (Anneal.*, bundle-manifest.json)
├── correspondence/                    # Pass-2 untrusted simulation proofs (MirCorrespondence.*, MiniRust.*)
└── tests/                             # Zone::Tests ( rank = 1 ) — Fenced Non-TCB Verification Suites
    ├── testkit/                       # package = "anneal-testkit" (publish = false, lib-only)
    │   ├── Cargo.toml
    │   └── src/{lib,toolchain,workspace,process,store_sim,corpora,assertions,digest,case_runner,audit_fixture,mir_wp_fixture}.rs
    ├── audit/                         # package = "anneal-audit-tests" (publish = false)
    │   ├── Cargo.toml
    │   ├── src/bin/anneal-audit-test-bin.rs
    │   └── tests/{boundary_audit.rs, boundary_audit/, target_audit.rs, cli_environment.rs, common/, fixtures/}
    │       # (`boundary_audit/` holds the `boundary_audit` target's domain submodules;
    │       #  Wave 2B target: decompose `target_audit.rs` likewise)
    ├── cargo-anneal/                  # package = "cargo-anneal-tests" (publish = false)
    │   ├── Cargo.toml                 # Mirrors `setup = ["cargo-anneal/setup", "dep:exocrate"]`
    │   ├── src/bin/cargo-anneal-test-bin.rs
    │   └── tests/
    │       ├── cli/{artifacts_and_overwrite,capture_request_binding,cargo_shortcut,help_and_bundled_resources,init_and_receipt_output,policy_taint_and_unstable_features,receipt_out,rustc_mode_and_env,setup_and_tool_discovery,sharding_and_limits}.rs
    │       ├── suite/{main,anti_vacuity_and_e2e,capture_and_cargo_isolation,corpora_runner,helpers,host_and_stage_security,receipt_and_bindings,split_store_bwrap}.rs
    │       └── {cli.rs, harness.rs, installed_smoke.rs, profile_v2_e2e.rs, sandbox_escape.rs, support_paths.rs, support_regressions.rs, support_signals.rs, fixtures/}
    ├── itree_diff/                    # package = "anneal-itree-diff" (publish = false)
    │   ├── Cargo.toml
    │   ├── src/{lib,trace_observer,outcome,spec,rustc_runner,miri_runner,lean_trace_runner,mir_eval_adapter,corpus,fuzzer,shrink}.rs
    │   ├── src/bin/itree_diff.rs
    │   └── tests/itree_differential.rs
    ├── rustc-capture/                 # package = "anneal-rustc-capture-tests" (publish = false)
    │   ├── Cargo.toml
    │   ├── src/bin/anneal-rustc-capture-test-bin.rs
    │   └── tests/{typed_capture.rs, stdlib_capture.rs, compiler_session.rs, pass_order_sentinel.rs}
    │       # (Wave 2B target: decompose typed_capture.rs into suite/main.rs)
    ├── differential/                  # package = "anneal-differential-tests" (publish = false)
    │   ├── Cargo.toml
    │   ├── src/bin/{anneal-diff.rs, anneal-diff-capture-test-bin.rs}
    │   ├── src/{lib.rs, corpus.rs, miri_runner.rs, lean_runner.rs, mir_eval_runner.rs, mutants.rs, verdict.rs}
    │   └── tests/differential_oracle.rs
    └── corpora/                       # Declarative data-driven corpora consumed by test crates
        ├── adversarial/               # Landed: capture/; Target Wave 3: + guards.toml, spec_and_preflight/, mir_ub_refutations/, audit_and_ndjson/
        ├── scalar/                    # Landed (#4187): dependency.rs, unsupported.rs
        ├── scalar_specs/              # Landed (#4187): 19 declarative (lib.rs, Spec.lean, Proof.lean) suites
        ├── spin/                      # Landed (#4187): loop verification corpus fixture
        ├── unsafe_identity/           # Landed (#4187): unsafe contract corpus fixture
        ├── differential/              # Landed Stage 1: profile_v1/manifest.toml (39 Miri <-> StepCore/MirWp cases); Target Wave 3: + multi-kernel NDJSON cases
        └── real_crates/               # Target Wave 3: declarative runner over zerocopy/proofs/ & external crates
```

Moving the integration suites out of `anneal/trusted/*/tests/` (`#4154`,
`348147c22d`, corresponding to `50` files / `30,302` lines at `c351dd381a`)
reduced `anneal/trusted/` by `31,016` lines at merge (`94,445` $\to$ `63,429`
lines; `114` $\to$ `71` files, retaining the `97`-line `assets/scalar/` runtime
example), eliminated `wait-timeout` and the `tests/` exclusion list from
`trusted/cargo-anneal/Cargo.toml`, and isolated integration-test archive
builders outside `trusted/` (leaving `tar` and `zstd` in
`trusted/cargo-anneal/Cargo.toml` `[dev-dependencies]` solely for `setup.rs`
`#[cfg(test)]` unit tests).

#### 2.2 Two-Zone Monotonic Lattice in `check_cargo_boundary`

`anneal-audit`'s `check_cargo_boundary` (`trusted/audit/src/cargo_boundary.rs`)
mechanically enforces workspace containment on every repository audit and
static CI run. To admit shared `anneal-testkit` dependencies across `tests/*`
while keeping `trusted/* -> tests/*` impossible, `cargo_boundary.rs` enforces a
**two-zone monotonic lattice**:

```rust
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum WorkspaceZone {
    /// Production TCB crates under `trusted/` (rank 0).
    Trusted = 0,
    /// Non-shipping test and harness crates under `tests/` (rank 1).
    Tests = 1,
}

fn classify_member_zone(rel_path: &str) -> Result<WorkspaceZone, Failure> {
    if !is_clean_relative_path(rel_path)
        || rel_path.ends_with('/')
        || rel_path.contains('\\')
    {
        return Err(Failure::new(
            1,
            "cargo-boundary",
            format!("unclean member path: {rel_path}"),
        ));
    }
    if rel_path.starts_with("trusted/") {
        Ok(WorkspaceZone::Trusted)
    } else if rel_path.starts_with("tests/") {
        Ok(WorkspaceZone::Tests)
    } else {
        Err(Failure::new(
            1,
            "cargo-boundary",
            format!("workspace member outside trusted/ or tests/: {rel_path}"),
        ))
    }
}
```

In `trusted/audit/src/cargo_boundary.rs` (`#4159`, `aa8d82c9bb`),
`check_cargo_boundary` forms `member_set = workspace.members ∪
workspace.exclude`, verifies that `trusted/rustc-capture/Cargo.toml` is a
regular file and `member_set.contains("trusted/rustc-capture")`, and validates
every registered path `M` across `workspace.members` and `workspace.exclude`
under five invariants (with optional target hardening to require all three
`trusted/{rustc-capture,cargo-anneal,audit}` crates in active
`workspace.members` rather than `member_set` so moving a TCB crate into
`workspace.exclude` cannot cause `--workspace` builds or tests to skip it):

1. **Zone Admission & TCB Presence:** `zone(M)` must resolve to
   `WorkspaceZone::Trusted` or `WorkspaceZone::Tests`, and `member_set` must
   contain `trusted/rustc-capture` (target hardening: check active
   `workspace.members` membership for `trusted/rustc-capture`,
   `trusted/cargo-anneal`, and `trusted/audit`).
2. **Publication Fence (`publish = false`):** If `zone(M) ==
   WorkspaceZone::Tests`, `M/Cargo.toml` must declare literal `package.publish =
   false` (`Some(toml::Value::Boolean(false))`); `publish = ["..."]`, `publish =
   true`, and omitted `publish` all fail closed.
3. **Build-Script, Proc-Macro, and Override Prohibition:**
   `trusted/cargo-anneal/build.rs` is required as a regular file to emit
   `$OUT_DIR/bundled_resources.rs` and `$OUT_DIR/bundled_theory.json`
   deterministically; neither zone may set `package.build` or
   `package.workspace`, and no other crate in either zone may contain
   `build.rs`. Across `[lib]`,
   `[[bin]]`, `[[example]]`, `[[test]]`, and `[[bench]]`,
   `validate_member_target` mechanically rejects `proc-macro = true` /
   `proc_macro = true` and `crate-type = ["proc-macro"]` / `crate_type =
   ["proc-macro"]` across `tests/*` (and every workspace crate), preventing
   compile-time proc-macro execution in non-TCB crates; target paths may not be
   absolute or contain `..`; and root `.cargo*`, `rust-toolchain*`, and
   `.gitmodules` remain forbidden.
4. **Monotonic Path-Dependency Rule (`zone(dst) <= zone(src)`):** Across
   `[dependencies]`, `[dev-dependencies]`, `[build-dependencies]` (hyphen and
   underscore spellings), and `[target.<cfg>.*]`:
   - `git` and custom `registry` keys are rejected unconditionally.
   - Every local `path` dependency from `src` to canonicalized `dst` must stay
     within `checkout`, belong to `member_set`, and satisfy
     `classify_member_zone(dst)? <= classify_member_zone(src)?`.
   - Consequently:
     - `trusted/* -> trusted/*` (`0 <= 0`): **permitted**.
     - `tests/* -> trusted/*` (`0 <= 1`): **permitted**.
     - `tests/* -> tests/*` (`1 <= 1`, e.g., `tests/audit -> tests/testkit`):
       **permitted** (acyclic by Cargo's crate graph).
     - `trusted/* -> tests/*` (`1 <= 0`, in `[dependencies]` or
       `[dev-dependencies]`): **rejected** (`exit 1`, `phase =
       "cargo-boundary"`).
5. **Lockfile Provenance:** `verify_cargo_lock` continues to require
   `Cargo.lock` `version = 4`, `crates.io-index` + 64-hex SHA-256 on every
   external package, and membership in `member_pkg_names` for every source-less
   local package.

#### 2.3 Feature-Synchronized CLI Binary Shims (`*-test-bin`)

Because Cargo populates `CARGO_BIN_EXE_<name>` only for `[[bin]]` targets
declared in the *same* Cargo package as the integration test, each fenced test
crate defines a 4-line binary shim delegating to its `trusted/` library's CLI
entrypoint (`#[doc(hidden)]` on `anneal_audit::cli` and `cargo_anneal::cli`;
`pub fn cli_main` on `publish = false`, `doctest = false`
`anneal_rustc_capture`):

| Fenced Test Crate | Binary Shim Target (`CARGO_BIN_EXE_*`) | Delegated `trusted/` Entrypoint | Required Shim Invariant |
| :--- | :--- | :--- | :--- |
| `anneal-audit-tests` | `anneal-audit-test-bin` | `anneal_audit::cli::main() -> ExitCode` | Non-colliding binary name in `target/<profile>/` |
| `cargo-anneal-tests` | `cargo-anneal-test-bin` | `cargo_anneal::cli::main() -> ExitCode` | Mirrors `setup = ["cargo-anneal/setup", "dep:exocrate"]` so `--no-default-features --test cli` compiles and tests the exact offline binary |
| `anneal-rustc-capture-tests` | `anneal-rustc-capture-test-bin` | `anneal_rustc_capture::cli_main() -> ExitCode` | Declares `#![feature(rustc_private)] extern crate rustc_driver;` so `rustc` links against `librustc_driver`'s dynamic `libstd` |

---

### 3. Shared `anneal-testkit` API, Typestates, and Monolith Decomposition

#### 3.1 `anneal-testkit` Module Structure and Core Typestates

`anneal/tests/testkit` (`anneal-testkit`, landed in `#4159` / `aa8d82c9bb` and
expanded with `digest`, `case_runner`, `audit_fixture`, and `mir_wp_fixture`)
consolidates tool discovery, temporary workspace staging, process supervision,
split-store simulation, directive parsing, receipt assertions, multi-case smoke
runners, persistent `OleanCache` reuse, and synthetic `MirWp` fixtures across
all three fenced test crates (`cargo-anneal-tests`,
`anneal-rustc-capture-tests`, and `anneal-audit-tests`; legacy
`cargo-anneal/tests/support/mod.rs` and `rustc-capture/tests/common/mod.rs`
shims are retired). It contains zero `rustc_private`
dependencies so it compiles once on both stable and pinned nightly Rust
toolchains and links into all three fenced test crates.

```rust
// anneal/tests/testkit/src/toolchain.rs

/// Explicit execution mode governing tool binary and library resolution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ToolchainMode {
    /// Resolve workspace-built `*-test-bin` shims (or explicit
    /// `ANNEAL_CLI`/`ANNEAL_CAPTURE`/`ANNEAL_AUDITOR` overrides, plus legacy
    /// `ANNEAL_MVP_CLI`/`ANNEAL_MVP_CAPTURE` and fallback
    /// `ANNEAL_TEST_INSTALL_ROOT`) paired with pinned Lean and Rust sysroot
    /// directories. Never reads `ANNEAL_TEST_CARGO_ANNEAL`.
    WorkspaceBuild {
        cli_bin: Option<PathBuf>,
        capture_bin: Option<PathBuf>,
        auditor_bin: Option<PathBuf>,
    },
    /// Exercise an installed `exocrate` bundle strictly outside the source
    /// checkout using an explicit `install_root` and optional explicit
    /// installed tool binaries (`cli_bin` / `ANNEAL_TEST_CARGO_ANNEAL` and
    /// `auditor_bin` / `ANNEAL_TEST_AUDITOR`). Requires `install_root`
    /// directly and never reads `ANNEAL_TEST_ARCHIVE` (falling back to
    /// `ANNEAL_TEST_INSTALL_ROOT` only inside Lean/sysroot lookup if
    /// `install_root/{lean/bin/lean,rust}` is absent).
    InstalledBundle {
        install_root: PathBuf,
        cli_bin: Option<PathBuf>,
        auditor_bin: Option<PathBuf>,
    },
}

/// Immutable, canonicalized tool coordinates shared across test cases.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ToolchainEnv {
    pub cli: Option<PathBuf>,
    pub capture: Option<PathBuf>,
    pub auditor: Option<PathBuf>,
    pub lean: PathBuf,
    pub lean_bin_dir: PathBuf,
    pub sysroot: PathBuf,
    pub has_ndjson_quorum_tools: bool, // true when lean_bin_dir bundles leanexport + nanoda_bin + con-ron
}
```

Workspace construction and execution follow a linear three-state typestate
pipeline (`WorkspaceBuilder<Building> -> StagedWorkspace -> ExecutedRun<Out>`):

```rust
// anneal/tests/testkit/src/workspace.rs

pub struct Building;

/// Allocates a `0o700` canonicalized temporary root partitioned into disjoint
/// sibling subdirectories:
///   `<root>/work/`   — mutable or staged project working directory (`cwd`)
///   `<root>/store/`  — simulated read-only Nix/CAS store packages (`DT_RUNPATH` / `PT_INTERP`)
///   `<root>/logs/`   — `commands/<NNNN>/{invocation.json,outcome.json,stdout,stderr,reproduce.py}`
pub struct WorkspaceBuilder<State = Building> {
    ro_guards: Vec<ReadOnlyTreeGuard>,
    root: tempfile::TempDir,
    work_dir: PathBuf,
    store_dir: PathBuf,
    logs_dir: PathBuf,
    timeout: Duration,
    _state: PhantomData<State>,
}

impl WorkspaceBuilder<Building> {
    pub fn new(prefix: &str, timeout: Duration) -> TestResult<Self>;

    /// Symlink-safe atomic file write under `<root>/work/<rel>` (`owned_rel_path` +
    /// `reject_symlink_components` + fresh-inode `NamedTempFile::persist`).
    pub fn write_work_file(&mut self, rel: impl AsRef<Path>, bytes: &[u8]) -> TestResult<&mut Self>;

    /// Copy minimal `trusted/lean` + `trusted/audit` lockfiles from the repository
    /// checkout for repository/target audit tests without copying `vendor/` or `target/`.
    pub fn seed_minimal_audit_locks(&mut self, checkout: &Path) -> TestResult<&mut Self>;

    /// Materialize a simulated store package under `<root>/store/<pkg_name>` and
    /// optionally freeze its permissions (`0o555` dirs / `0o444` files) behind a
    /// `ReadOnlyTreeGuard` that restores `u+rwx` top-down on drop.
    pub fn add_store_package(
        &mut self,
        pkg_name: &str,
        freeze_read_only: bool,
        populate: impl FnOnce(&Path) -> TestResult,
    ) -> TestResult<PathBuf>;

    /// Seal inputs, record `run.json`, and transition to `StagedWorkspace`.
    pub fn stage(self) -> TestResult<StagedWorkspace>;
}

pub struct StagedWorkspace { /* owns TempDir, ReadOnlyTreeGuards, command counter */ }

impl StagedWorkspace {
    pub fn work_dir(&self) -> &Path;
    pub fn store_dir(&self) -> &Path;

    /// Spawn an isolated process group (`process_group(0)` + process-wide subreaper),
    /// enforce `self.timeout` (`kill(-pgid, SIGKILL)` + `waitpid(-pgid)` for same-PGID
    /// descendants, paired with kernel `PR_SET_PDEATHSIG` on `ExecSeal` grandchildren),
    /// and record a self-contained `commands/<NNNN>/reproduce.py` bundle.
    pub fn exec(&self, inv: &Invocation) -> TestResult<ExecutedRun<RawOutput>>;

    /// Typed convenience runners parsing structured JSON receipts (`#[serde(deny_unknown_fields)]`).
    pub fn run_verify(&self, tools: &ToolchainEnv, args: &[&OsStr]) -> TestResult<ExecutedRun<VerifyReceipt>>;
    pub fn run_capture(&self, tools: &ToolchainEnv, args: &[&OsStr]) -> TestResult<ExecutedRun<CaptureStatus>>;
    pub fn run_audit(&self, tools: &ToolchainEnv, args: &[&OsStr]) -> TestResult<ExecutedRun<AuditReport>>;

    /// Retain `<root>` and export to `ANNEAL_TEST_DIAGNOSTICS` (excluding multi-GiB
    /// `installation/` copies) if `result.is_err()` or `ANNEAL_KEEP_SANDBOX == "1"`;
    /// otherwise run `ReadOnlyTreeGuard` top-down `chmod u+rwx` and clean `<root>`.
    pub fn finish<T>(self, result: TestResult<T>) -> TestResult<T>;
}
```

#### 3.2 Subprocess-Tree Supervision and Signal-Forwarding `reproduce.py`

`anneal-testkit::process` (and `anneal-testkit::case_runner` in
`anneal/tests/testkit/src/{process,case_runner}.rs`) replaces direct-child
`wait_timeout` supervision with synchronous group supervision:

1. **Test Process Initialization:** On Linux, `ensure_child_subreaper()` sets
   the **process-wide** `libc::prctl(libc::PR_SET_CHILD_SUBREAPER, 1)` attribute
   once per test process via `OnceLock`, keeping reparented descendants (`lean`,
   `rustc`, `ld`, `bwrap`) attached to the test runner rather than escaping to
   PID 1.
2. **Per-Invocation Group Isolation:** Every `Invocation` spawns with
   `CommandExt::process_group(0)` (`setpgid(0, 0)`), `env_clear()`, explicit
   `environment` bindings, `Stdio::null()` stdin, and file-backed
   `stdout`/`stderr` (preventing 64 KiB pipe-buffer deadlocks when a
   grandchild inherits stdio descriptors after the direct child exits).
3. **Deadline and Post-Exit Teardown (Same-PGID vs. `ExecSeal` Grandchildren):**
   - *Same-PGID children* (`cargo-anneal`, `anneal-rustc-capture` / `rustc`,
     `ld`, and direct helpers inheriting `pgid`): Before reaping `child` (so
     `pgid` stays pinned against PID reuse), the supervisor sends
     `libc::kill(-pgid, libc::SIGKILL)`, reaps the direct child, and loops on
     `libc::waitpid(-pgid, &mut status, 0)` until `ECHILD` (and after normal
     exit sweeps `waitpid(-pgid, WNOHANG)` + `kill(-pgid, SIGKILL)` so no
     orphaned `pgid` member outlives `run()`).
   - *Session- and PGID-detached `ExecSeal` grandchildren* (`bwrap` and
     Landlock-confined `lean`, plus unsandboxed Linux `lean` spawns): In
     `trusted/cargo-anneal/src/sandbox.rs`, `apply_process_hygiene` places
     sandboxed children into distinct sessions or process groups via `setsid()`
     / `setpgid(0, 0)` (`PGID != pgid`) and registers kernel
     `prctl(PR_SET_PDEATHSIG, SIGKILL)` (alongside `bwrap --die-with-parent` and
     a `getppid() != parent_pid` fork-race guard). When `cargo-anneal` exits or
     is killed via `kill(-pgid, SIGKILL)`, the kernel delivers `SIGKILL` to
     those grandchildren on parent exit even though `waitpid(-pgid)` immediately
     returns `ECHILD` for their distinct PGIDs.
   - *Process-Per-Test Isolation and `finish()` Cleanup:* Under `cargo-nextest`
     (`D3-A`), process-per-test execution isolates the process-wide subreaper
     to a single `#[test]`, eliminating cross-test subreaper zombie and
     teardown races (and reclaiming any reparented zombies at test-process
     exit). Under multi-threaded `cargo test` (`libtest`), where `waitpid(-1)`
     cannot be called without stealing sibling threads' children, `finish()`
     restores `ReadOnlyTreeGuard` permissions top-down before `TempDir` drop
     while kernel `PR_SET_PDEATHSIG(SIGKILL)` closes detached grandchild
     descriptors and locks (with bounded retry/backoff on transient
     `EBUSY`/`ENOTEMPTY` directory removal available as an incremental
     hardening if ever observed under heavy `libtest` contention).
4. **Replay Script Fidelity:** Every `commands/<NNNN>/reproduce.py` spawns with
   `process_group=0`, installs `SIGINT`/`SIGTERM` handlers forwarding
   `os.killpg(proc.pid, signum)`, and kills `-proc.pid` on `TimeoutExpired` so
   interactive `Ctrl-C` during local debugging never orphans background `lean`
   workers.

#### 3.3 Hermetic Nix-Style Split-Output Symlink and ELF `DT_RUNPATH` Simulation

Testing `anneal-rustc-capture` (`identity.rs`) and `cargo-anneal` (`sandbox.rs`)
against split Nix/CAS store topologies without requiring `/nix/store` on the
host relies on four invariants enforced by `anneal-testkit::store_sim`:

1. **Top-Down `ReadOnlyTreeGuard` Teardown:** Simulating `exocrate` (`chmod -R
   a-w`) or Nix store (`0o555` directories, `0o444` files) permissions inside a
   standard `TempDir` causes `TempDir::drop` (`unlinkat`) to fail with `EACCES`
   (`PermissionError`), leaking `/tmp` directories. `ReadOnlyTreeGuard::drop`
   walks registered store roots **top-down** (`follow_symlinks = false`) and
   applies `chmod(mode | 0o700)` to directories before `TempDir::drop` executes.
2. **Disjoint `<root>/store/` vs. `<root>/work/` Layout:** `identity.rs:350-389`
   (`is_allowed_pt_interp_dir`) rejects any `PT_INTERP` directory `D` for which
   `canon_home.starts_with(D)` or `canon_cwd.starts_with(D)`, and
   `sandbox.rs:467-532` (`validate_toolchain_mount_dir`) rejects any
   toolchain/mount directory `D` overlapping `canon_stage` or enclosing
   `canon_home` or `canon_cwd`. Because `WorkspaceBuilder` places all simulated
   packages under `<root>/store/<pkg>/lib` (`normal_count >= 2`) and sets child
   `current_dir` to `<root>/work/`, `canon_cwd` and `D` are guaranteed disjoint
   siblings.
3. **Five-Cell ELF `DT_RUNPATH` / `DT_RPATH` / `PT_INTERP` Fixture Builder
   (`ElfStoreBuilder`):**
   - Materializes split C/toolchain runtime layouts under `<root>/store/`—for
     example, `0001-glibc/lib/ld-linux-*.so.*`,
     `0002-gcc-lib/lib/libgcc_s.so.1` symlinking to
     `../../0003-gcc-libgcc/lib/libgcc_s.so.1`,
     `0004-zlib/lib/libz.so.1`, and `0005-rust-sysroot` (`bin/rustc`,
     `lib/librustc_driver-*.so`, `lib/libLLVM*.so*`)—covering:
     - **Cell 1:** Non-transitive `DT_RUNPATH` failure when leaf `libLLVM.so`
       lacks co-located `libz.so.1`;
     - **Cell 2:** Ancestor `DT_RPATH` suppression when an intermediate DSO
       carries `DT_RUNPATH != NULL` (`glibc` `elf/dl-load.c:_dl_map_object`);
     - **Cell 3:** Ancestor `DT_RPATH` resolution when leaf DSOs carry no
       `DT_RUNPATH`;
     - **Cell 4:** Consumer `DT_NEEDED` preloading (`patchelf --add-needed
       libz.so.1` inside immutable FOD split stores);
     - **Cell 5:** Co-located `$ORIGIN/../lib` `DT_RUNPATH` resolution
       (`omnibus-archive` layout) plus relative `../../../libLLVM*.so*`
       deduplication symlinks under `lib/rustlib/<triple>/lib/`;
     - **Explicit Loader Wrappers:** Launching
       `<store>/0001-glibc/lib/ld-linux-*.so.* --library-path ... <capture-bin>`
       where `/proc/self/exe` is the loader (`has_pt_interp == false`) while
       `self_addr` maps the capture binary VMA (`identity.rs:635-681`).
   - Negative splice probes replace `librustc_driver-*.so` or `libLLVM*.so*`
     inodes (`st_dev, st_ino`) in either `lib/` or `lib/rustlib/<triple>/lib/`
     and assert `status == "tool_failed"` with zero emitted capture artifacts.
4. **Namespace-Mounted `/nix/store` Harness for Cross-Package Lean `symlinkJoin`
   Trees:**
   - In `cargo-anneal/src/sandbox.rs:588-600`,
     `symlink_stays_within_dedicated_root` rejects cross-directory symlinks
     inside `<prefix>/lib/lean` unless **both** `canon_root` and `canon_target`
     start with `/nix/store`.
   - To test Nix `symlinkJoin` Lean wrappers (`0002-lean-joined/lib/lean/`
     symlinking `Init.olean` to
     `../../../0001-lean-unwrapped/lib/lean/Init.olean`, plus
     `.olean.server`/`.olean.private` companions) deterministically on any
     Linux runner without host Nix, `store_sim::run_in_simulated_nix_store`
     launches the test target inside an unprivileged `bwrap` mount namespace
     (`--unshare-all --die-with-parent --ro-bind <root>/store /nix/store`),
     binding the synthetic split store at `/nix/store` read-only. Inside
     `ci-core` (`NestedBwrap`), this composes directly with the outer
     container's capability-dropped inner `bwrap` contract.

#### 3.4 Concrete Monolith Decomposition Plan and Single-Binary Cargo Discipline

In Cargo, every top-level `tests/<name>.rs` file compiles and links a separate
executable. Splitting `boundary_audit.rs` (`9,824`L) and `typed_capture.rs`
(`2,840`L) into `25` top-level `tests/*.rs` files would force `25` separate
links of `anneal-audit` and `librustc_driver`, adding gigabytes of
`target/debug/deps/` bloat and tens of seconds of link latency. Instead, each
fenced test crate groups domain submodules (<800 lines per file) under **one
primary `tests/suite/main.rs` binary**, retaining separate binaries strictly
where Cargo feature flags (`--no-default-features`) or `#[ignore]` smoke
isolation require a distinct compilation unit:

| Suite & Pre-Split Monolith | Status on `main` | Crate & Binary Target | Domain Submodules (`<800`L target) | Shared `anneal-testkit` Primitives Used |
| :--- | :--- | :--- | :--- | :--- |
| `audit/tests/boundary_audit.rs` (`12,996`L before the split; `9,824`L at `c351dd381a`) | **Split (Wave 2B)** (`LeanAuditFixture`/`SharedOleanCache` & `MirWpFixtureSpec` wired; the target keeps its `boundary_audit` binary name, which `.config/nextest.toml` filters on; submodules span `505`–`1,397`L, and `forged_olean_replay.rs` holds a single `1,378`L test) | `anneal-audit-tests` `tests/boundary_audit.rs` root with `#[path]` submodules in `tests/boundary_audit/` | `cargo_boundary.rs`, `foundation_and_sysroot.rs`, `forged_olean_replay.rs`, `pass1_preflight.rs`, `pass1_tiers_and_theory.rs`, `pass1_universes_and_framework.rs`, `pass1_mir_wp_gates.rs`, `pass2_miri_pin.rs`, `pass2_miri_cache_and_sandbox.rs`, `pass2_correspondence_audit.rs`, `pass2_correspondence_non_backsliding.rs`, `pass2_module_isolation.rs`, `pass2_import_graph.rs`, `pass2_syntax_preflight.rs`, `bundle_parity_and_dag.rs`, `compiler_overrides.rs` | `LeanAuditFixture`, `SharedOleanCache`, `MirWpFixtureSpec`, `ReadOnlyTreeGuard`, forged-`.olean` script helper |
| `audit/tests/target_audit.rs` (`3,035`L on `main`; `2,332`L at `c351dd381a`) | **In Progress (Wave 2B)** (`LeanAuditFixture`/`SharedOleanCache` wired; submodule split remaining) | `anneal-audit-tests` `tests/target/main.rs` (or `suite/target_*.rs`) | `role_and_origin_gates.rs` (`Model`/`Capture`/`Spec`/`Expected`/`Proof` edges), `axiom_and_opaque_gates.rs` (`sorryAx`, `opaque`, `ofReduceBool`, native eval), `module_and_universe_gates.rs` (universe-polymorphic rejection, 3-part bundled `module` vs. 1-part user `.olean` enforcement) | `LeanAuditFixture`, `SharedOleanCache` |
| `cargo-anneal/tests/integration.rs` + `mvp_e2e.rs` (`4,315`L + `1,566`L at `c351dd381a`; deleted in `#4187`) | **Landed (Wave 2A, `#4187`)** (+ Wave-3 `ndjson_quorum_e2e.rs` once `#4016` lands) | `cargo-anneal-tests` `tests/suite/main.rs` | Landed submodules: `corpora_runner.rs` (`//@` engine driving `tests/corpora/{adversarial/capture,scalar,scalar_specs,spin,unsafe_identity}`), `receipt_and_bindings.rs`, `host_and_stage_security.rs`, `capture_and_cargo_isolation.rs`, `anti_vacuity_and_e2e.rs`, `split_store_bwrap.rs`, `helpers.rs`; Wave-3 addition: `ndjson_quorum_e2e.rs` (`5-init`/`5a`/`5b`/`5c` + 2-/4-kernel `ExecSeal` + 3-part `module` `expected_lib` linking) | `ToolchainEnv` (`WorkspaceBuild`), `StagedWorkspace::run_verify`, `corpora::DirectiveParser` (`1,388`L doc-comment synthesizer retired in `#4187` per `D2-A`), `store_sim::run_in_simulated_nix_store` |
| `cargo-anneal/tests/{cli,harness,installed_smoke,profile_v2_e2e,sandbox_escape}.rs` + `support_{paths,regressions,signals}.rs` | **Migrated onto `anneal-testkit`** (`support/mod.rs` retired; `cli.rs` split into `cli/` domain submodules; `support_{paths,regressions,signals}` kept for runner regression coverage) | `cargo-anneal-tests` (`cli.rs`, `harness.rs`, `installed_smoke.rs`, `profile_v2_e2e.rs`, `sandbox_escape.rs`, `support_*.rs`) | `cli.rs` remains a separate binary so `--no-default-features --test cli` compiles with zero `exocrate` deps, with tests organized under `cli/{artifacts_and_overwrite,capture_request_binding,cargo_shortcut,help_and_bundled_resources,init_and_receipt_output,policy_taint_and_unstable_features,receipt_out,rustc_mode_and_env,setup_and_tool_discovery,sharding_and_limits}.rs`; `sandbox_escape.rs` runs on both `x86_64` and `sandbox-aarch64`; `profile_v2_e2e.rs` splits into `10` parallel `#[test]` cases sharing `SharedOleanCache`; `installed_smoke.rs` consumes `RunDirectory`/`CaseDirectory`/`MirWpFixtureSpec` directly | `ToolchainEnv`, `RunDirectory`/`CaseDirectory`, `ProcessSupervisor`, `SharedOleanCache`, `VerifyReceipt`, `MirWpFixtureSpec`, `ReadOnlyTreeGuard` |
| `rustc-capture/tests/{typed_capture,stdlib_capture,compiler_session}.rs` (`typed_capture.rs`: `3,122`L on `main`) | **In Progress (Wave 2B)** (`common/mod.rs` retired; all 3 suites directly on `anneal-testkit`; `typed_capture` submodule split remaining) | `anneal-rustc-capture-tests` `tests/suite/main.rs` (`compiler_session.rs` & `stdlib_capture.rs` separate) | `cli_and_publication.rs` (mode flags, response-file refusal, atomic non-UTF8/symlink output guards), `namespace_and_env.rs` (`--source-file` allowlists, `include_str!`, `--env KEY=VALUE` `env_depinfo` binding), `mir_extraction.rs` (scalars, shifts, fieldless enums, `enum_id` `const _` scoping, `PlaceMention`, `required_consts` CTFE), `linux_residency.rs` (5-cell `DT_RUNPATH`/`DT_RPATH`, symlinked CAS sysroots, `libLLVM` splice rejection, `FORBIDDEN_LOADER_ENV_VARS`) | `ToolchainEnv`, `default_rust_sysroot`/`default_lean_path`, `StagedWorkspace::run_capture`, `ElfStoreBuilder` in `anneal-testkit` |

Process-level concurrency, per-test timeouts, and heavy-Lean slot throttling
are configured in `anneal/.config/nextest.toml` (landed in `#4159`):

```toml
# anneal/.config/nextest.toml
[profile.default]
retries = 0
slow-timeout = { period = "30s", terminate-after = 4 }
fail-fast = false

[[profile.default.overrides]]
filter = 'binary(differential_oracle)'
threads-required = 2
slow-timeout = { period = "90s", terminate-after = 4 }

[[profile.default.overrides]]
filter = 'binary(boundary_audit) | binary(target_audit) | binary(profile_v2_e2e) | test(/verifies_scalar_spec_corpus|selected_unit_normalization_and_boundary_rejections/)'
threads-required = 2
slow-timeout = { period = "60s", terminate-after = 4 }

[[profile.default.overrides]]
filter = 'test(/ndjson_quorum|correspondence|scale_|real_crates/)'
threads-required = 2
slow-timeout = { period = "45s", terminate-after = 4 }

[profile.ci]
retries = 0
slow-timeout = { period = "30s", terminate-after = 4 }
status-level = "pass"
final-status-level = "slow"
```

---

### 4. Declarative Data-Driven Corpora

Declarative test corpora live under `anneal/tests/corpora/` as pure data and
minimal Rust/Lean source packages, parsed and executed by
`anneal-testkit::corpora` and `tests/cargo-anneal/tests/suite/corpora_runner.rs`
so adding a test case requires **zero** harness code edits
(`adversarial/capture/`, `scalar/`, `scalar_specs/`, `spin/`, and
`unsafe_identity/` landed in `#4187`; Wave 3 adds the remaining `adversarial/`
subtrees, `differential/`, and `real_crates/`).

#### 4.1 `adversarial/`: `must-reject` Directives and Guard Ablation

`anneal/tests/corpora/adversarial/` (`capture/` landed in `#4187`; remaining
subtrees target Wave 3) unifies surface/pipeline negative fixtures
(`//@ fail(...)`) with TCB single-guard mutation testing
(`ci/check_guard_mutation.py`):

```text
anneal/tests/corpora/adversarial/
├── guards.toml                        # Unified guard-ablation catalog (Lean TCB + Rust TCB)
├── capture/                           # Capture-stage rejections (*.rs with //@ fail(capture))
├── spec_and_preflight/                # SpecPreflight / header / syntax / role rejections
├── mir_ub_refutations/                # UB refutation theorems & unprovable UB Rust programs
└── audit_and_ndjson/                  # Forged NDJSON, opaque/axiom/quotient/primitive attacks
```

1. **Stage-Typed, Polarity-Locked Directives:**
   Every `.rs` or `.lean` fixture declares exactly one primary expectation per
   `// === case: <id> ===` section:
   - `//@ pass`
   - `//@ fail(capture): "<diagnostic_substring>"`
   - `//@ fail(preflight): "<diagnostic_substring>"`
   - `//@ fail(spec): "<diagnostic_substring>"`
   - `//@ fail(proof, <fn_or_crate>): "<diagnostic_substring>"`
   - `//@ fail(audit): "<diagnostic_substring>"`
   - `//@ known_bug(#<issue>, <stage>): "<diagnostic_substring>"`
   - Optional metadata: `//@ kills-guard: <guard_id>`, `//@ mir-contains:
     "<substr>"`, `//@ mir-not-contains: "<substr>"`.

   **Polarity Lock Invariant:** Running with `ANNEAL_BLESS=1` may update
   `<diagnostic_substring>` within a matching `fail(...)` stage or promote a
   newly passing `known_bug(#N, ...)` to `//@ pass`, **never** flipping
   `//@ pass` $\to$ `fail` or `//@ fail(...)` $\to$ `pass`.
2. **Unified Guard-Ablation Schema (`guards.toml`, Target Wave 3):**
   Extends Anneal's `205` cataloged Lean guards (`185` `Trusted/MirSemantics/*`
   + `8` header + `12` boundary guards in `ci/check_guard_mutation.py`, up from
   `46` at `c351dd381a`) to cover **Rust TCB guards** across
   `trusted/rustc-capture`, `trusted/audit`, and `trusted/cargo-anneal`:

   ```toml
   [[guard]]
   id = "capture_required_consts_post_mono_ctfe"
   zone = "rust_tcb"
   target_file = "trusted/rustc-capture/src/extract.rs"
   anchor = "for const_op in required_consts {"
   replacement = "for const_op in required_consts.iter().take(0) {"
   positive_sanity = "scalar_specs::annotated_id"
   negative_witness = "adversarial/capture/dead_branch_pme.rs::instantiate_pme_unit"
   expected_unmutated = { status = "compiler_failed", detail_contains = "rustc rejected the compilation" }
   ```

   (Here `instantiate_pme_unit` invokes `--instantiate '{"path":"pme","args":
   ["()"]}'` on generic `pub fn pme<T>()` containing a dead-branch `const {
   assert!(size_of::<T>() > 0) }`; because `--emit=metadata,obj` skips
   unreferenced generic items, `eval_required_consts` is the sole guard
   triggering CTFE failure on `pme<()>`.)

   **Public-Entrypoint Kill Rule ($K_{\text{entry}} = 100\%$):** For every
   `[[guard]]`, the runner verifies that (a) against unmodified `trusted/`,
   `negative_witness` fails at the declared stage/category while
   `positive_sanity` passes; and (b) with *only* `anchor -> replacement` applied
   in an isolated `TempDir` copy, `positive_sanity` still compiles and passes
   (ruling out compiler/syntax errors masquerading as kills via
   `NON_KILL_ERROR_MARKERS`) while `negative_witness` flips to acceptance (or
   refutation type failure) **through the public CLI/library entrypoint**, never
   solely via a private unit helper.

#### 4.2 `differential/`: Semantic Execution and Multi-Kernel NDJSON Quorums

`anneal/tests/corpora/differential/` enforces agreement across two independent
semantic seams:

1. **Seam A — Miri $\leftrightarrow$ `Trusted.MirSemantics` Multi-Leg
   Differential Oracle (`profile_v1/`):**
   `anneal-differential-tests` (`tests/differential/`) loads
   `tests/corpora/differential/profile_v1/manifest.toml` (`39` Profile v1 cases)
   and compares legs under matching flags (`-C opt-level=0 -C
   debug-assertions=no -C overflow-checks=no`, `--target
   x86_64-unknown-linux-gnu`):
   - **Miri (`-Zmiri-tree-borrows`)** against an offline vendored sysroot,
   - **`anneal-rustc-capture` + Lean `Anneal.MirTotal.StepCore`** executable
     evaluator on `Captured.lean`,
   - **Lean kernel `Anneal.MirWp` adequacy theorems** (term-mode `rfl`
     witnesses under `-Ddebug.skipKernelTC=false`) on budget-fitting
     single-block `pass` cases and single-block or two-block `sysroot_call`
     `ub` cases, and
   - **Optional `anneal-mir-eval`** (`--body <body_id>`), plus native `rustc`
     and generative fuzzing extensions in Stage 2.

   | Miri Outcome | Lean `StepCore` Outcome | Differential Verdict | CI Gate Disposition |
   | :--- | :--- | :--- | :--- |
   | `Returned(v)` | `Returned(v')` with `v == v'` | `AgreeValue` | **PASS** (must also match `expected_return` and any active `mir_eval` leg) |
   | `Returned(v)` | `Returned(v')` with `v != v'` | **`ValueMismatch`** | **HARD FAIL** (semantic bug in capture or `MirSemantics`) |
   | `UndefinedBehavior` / `AbnormalAbort` / `Panic` | `Returned(_)` | **`UnsoundMissedFault`** | **HARD FAIL** (missing UB or fault guard in `MirSemantics` or capture) |
   | `UndefinedBehavior` | `UndefinedBehavior` | `AgreeUndefinedBehavior` | **PASS** (must also match `miri_ub_contains`) |
   | Any non-error outcome | Step-time `Unsupported` | `SoundConservativeAbstraction` / `ConservativeRejection` | **PASS only on `expected = "unsupported_control"`** with matching `expected_miri` pin (init-time `InitUnsupported` and undeclared `ConservativeRejection` **FAIL**) |

2. **Seam B — Multi-Kernel NDJSON Proof Quorum (`kernel_quorum/`, Lean
   `v4.35.0+`):**
   Exercises the three-stage zero-`.olean`-deserialization boundary (`5-init` 39
   `Init` primitives, `5a` disjoint `expected_lib/` mounting **all 3 `.olean` /
   `.olean.server` / `.olean.private` parts** of bundled `Model` modules and
   1-part `Capture`/`Spec`/`Expected` modules with zero `Proof.*`/`Anneal.*`
   files visible, `5b` bounded `proof_full.ndjson` export, and `5c`
   `#[forbid(unsafe_code)]` `CanonicalArena` DAG verification) across
   independent `ExecSeal`-sandboxed kernels:
   - **Default 2-Kernel Gate:** `nanoda_bin` (`"unpermitted_axiom_hard_error":
     true`, `nat_extension: true`, `string_extension: true`) + `con-ron
     --verified` (recording `con-ron` in `kernelsSkipped` strictly when
     `--allow-sorry-in-proof` is active and `sorryAx` is present).
   - **Paranoid 4-Kernel Quorum (`--paranoid-quorum`):** Adds `con-leche` and
     `lean4lean --import` over `proof_full.ndjson` inside `ExecSeal` (`< 3.0 s`
     total on `scalar`).
   - **Refinement of `auditing-and-comparator.md` (`lake comparator` Exclusion &
     `leanchecker --from-export` Quarantine):** Empirical Lean `v4.35.0`
     verification refines the earlier paranoid-CI sketch in
     [`auditing-and-comparator.md`][paranoid-ci] ("Optional paranoid
     multi-kernel CI mode") in three ways: (1) the `lake comparator` CLI wrapper
     is excluded from the authoritative verdict path because it hardcodes
     `"unpermitted_axiom_hard_error": false` when configuring `nanoda_bin`; (2)
     external kernels (`nanoda_bin` with `"unpermitted_axiom_hard_error": true`,
     `con-ron --verified`, `con-leche`, and `lean4lean --import`) are invoked
     directly under strict Rust configuration checks inside `ExecSeal`; and (3)
     `leanchecker --from-export` is deferred from gating verdicts until upstream
     `Lean.Kernel.Environment.replay` (`src/lean/Lean/Replay.lean:77, 186`)
     fixes its `Name.quickCmp` hash-order `NameSet` traversal on implicit
     string-literal reduction constants (`String.ofList`, `Char.ofNat`), which
     fails on valid `Captured.program` function-identity strings on `v4.35.0`.
     `kernel_quorum/` retains a non-gating canary probe
     (`string_literal_replay_probe`) tracking upstream `leanchecker
     --from-export` status.

3. **Seam C — Multi-Call Observable-Trace `ITree` Differential & Fuzz Suite
   (`tests/itree_diff/`, `anneal-itree-diff`):**
   Exercises multi-step and multi-call interaction-tree (`ITree`) observable
   spines (`CallEnter`, `CallReturn`, `CallUnwind`, `CallerFrameCheck`, and
   `BranchTag`), SHA-256 entry-argument and post-execution terminal boundary
   `mem_digest` parity, `core::mem::offset_of!` padding-safe byte capture,
   live caller-frame and watched-allocation preservation across calls and
   cleanup unwinds, deterministic `EnvSchedule` actions (`ReturnBytes`,
   `Unwind`, and real `std::process::abort()` `Abort`), and source-inlined
   single-body metamorphic twins:
   - **Miri-First UB Guard, `DegradedNoMiri`, & `DegradedNoLean`:** Miri
     (`-Zmiri-tree-borrows`) runs first whenever provisioned so Undefined
     Behavior inputs are never executed natively under host `rustc` (`-O0` /
     `-O2`). When Miri is absent from the trimmed omnibus archive
     (`workspace-tests`) or when Lean is disabled (`--no-lean`), `Agree` is
     never emitted: non-expected-UB cases run natively under `rustc` and
     classify as `DegradedNoMiri` or `DegradedNoLean` while `--require-miri`
     (`ANNEAL_ITREE_REQUIRE_MIRI=1`) fails closed, and default `.olean`,
     capture, and Miri caches write outside the checkout (external
     `CARGO_TARGET_*`, `XDG_CACHE_HOME` / `~/.cache`, or `TMPDIR`).
   - **Lean Trace Modes (`mirTyBeqAt 64`):** Instantiates `Anneal.MirTotal` at
     `mirTyBeqAt 64` (matching `Trusted.MirSemantics.evalStep` for `MirTy`
     trees of nesting depth `< 64`) in both `StrictVerbatim` mode (running
     single bodies, `.sysrootCall`, and safe intra-crate `.call`s directly under
     `evalMirStepBy` while refusing external callees, `.cleanup` unwinds, and
     unmodeled boundaries) and `CompositionalITree` multi-call stack mode
     outside `trusted/lean/`
     (where `ITreeDriver` steps individual bodies via `evalMirStepBy` and
     stitches call/unwind frames and caller-frame checks in the test driver,
     validating per-body `MirSemantics` plus harness composition), separating
     conservative twin skips (`SkippedConservative`) from verified metamorphic
     passes and pinning `ShrinkFailureSignature` across combined fixed-point
     `ddmin` + non-monotonic scalar candidate reduction.

#### 4.3 `real_crates/`: Verbatim `zerocopy` Suite and External Smoke Pins

`anneal/tests/corpora/real_crates/` prevents synthetic-fixture overfitting by
testing unmodified production crates:

1. **First-Customer Verbatim `zerocopy` (`zerocopy/proofs/` & Target
   `real_crates/zerocopy/`):**
   - Operates directly against the live repository's `zerocopy/src/` tree (`20`
     files, `33,939` LOC) and `zerocopy/proofs/` specifications (`4` proof
     units landed in `#4148` / `d3362d9a65`, excluded from
     `zerocopy/Cargo.toml`'s published crate tarball and verified in CI by
     `anneal/ci/verify_zerocopy.py`) using explicit `--env
     CARGO_PKG_VERSION=<ver>` bindings (`#4131`)—never copying snippets into
     standalone toy files.
   - Alongside `perf_budgets.json`'s active
     `zerocopy_proofs.suite.verified_units_count >= 4` floor, Wave 3 adds a
     checked-in **Monotone Non-Backsliding Ratchet
     (`real_crates/zerocopy/ratchet.json`)** partitioned into disjoint item
     classes so `2,203` trivial `only_derive_is_allowed_to_implement_this_trait`
     sealing stubs cannot mask substantive or `unsafe` regressions:

     ```json
     {
       "schema_version": 1,
       "profiles": ["no_std", "alloc_std_simd"],
       "floors": {
         "sealing_stubs_captured": 327,
         "safe_substantive_captured": 4,
         "unsafe_items_captured": 1,
         "end_to_end_verified_items": 5,
         "kani_contract_paired_items": 0
       },
       "verified_targets": [
         "<() as PointerMetadata>::from_elem_count",
         "<() as PointerMetadata>::to_elem_count",
         "<usize as PointerMetadata>::from_elem_count",
         "<usize as PointerMetadata>::to_elem_count",
         "util::macros::__unsafe"
       ]
     }
     ```

   - Every Anneal capability PR unlocking new MIR constructs updates `floors`
     upward (`actual >= floor` enforced in CI) and prioritizes
     `zerocopy/src/{layout.rs,byteorder.rs,util/mod.rs,byte_slice.rs}` items
     carrying existing `#[kani::proof*]` contracts (`63` contracts total: `55`
     in `layout.rs`, `5` in `byteorder.rs`, `2` in `util/mod.rs`, `1` in
     `byte_slice.rs`).
2. **Pinned External Multi-File Smoke Crates (`real_crates/external/`, Target
   Wave 3):**
   - Subsumes Fuchsia Starnix `ebpf_core` (`10` external `.rs` files
     SHA-256-pinned in `tests/cargo-anneal/tests/fixtures/starnix/source.json`
     and fetched at test time alongside checked-in `request.json` and
     `proof/*.lean`, currently driven by `anneal/ci/verify_starnix_e2e.py` for
     positive verification and implementation-mutation rejection) under the
     declarative `anneal-testkit` runner (`real_crates/external/starnix/`).

---

### 5. Performance, Memory, Artifact-Size, and Axiom-Footprint Gates

At `c351dd381a`, `theory/bundle-manifest.json` registered `18` bundled
`theory/` modules (`16,799` lines; `19` modules after `#4093` added
`Anneal.Firewall`), whereas `theory/Anneal.lean` transitively imported `73`
Lean modules (`66,307` lines across `19` `trusted/lean` + `54` `theory/` files,
including `36` unbundled `theory/` modules totaling `43,393` lines and a
`28`-module `19,704`-line critical path) that `installed_smoke.rs:lean_case`
compiles cold under `lean -j1 -DElab.async=false -Ddebug.skipKernelTC=false`
with a `120 s` per-child hard timeout. Furthermore, under Lean 4 `module`
encapsulation (`#4139`, `6a0932de51`), bundled Pass-1 modules emit **three**
artifact parts (`.olean` public interface, `.olean.server`, and
`.olean.private` proof bodies—where `94.8%` of `Anneal.MirWp.*` and `60%–71%`
of `Anneal.PureLift.*` reside in `.olean.private`), while `5b` (`leanexport`)
loads `.olean.private` during full-cone proof export.

To prevent late `installed_smoke` timeouts, runner OOM kills on 16 GiB CI
hosts, `.olean*` proof-term bloat, and silent constructive-purity regressions,
Anneal pairs the landed performance-tracking pipeline specified in
[`perf-tracking.md`](perf-tracking.md) (`anneal/ci/perf_tracking.py`,
`anneal/ci/perf_budgets.json`, `anneal/ci/render_perf_dashboard.py`, and
`.github/workflows/anneal-perf.yml`, landed in `#4171`–`#4173` and `#4212`)
with targeted Wave-3 quorum and axiom-footprint extensions across four
orthogonal axes:

#### 5.1 Four-Axis Regression Budget Matrix

| Gate Axis | Measured Quantity & Tooling | Landed `perf_budgets.json` Ceiling / Floor & Target Extensions | Failure Diagnostic & Remediation |
| :--- | :--- | :--- | :--- |
| **1. Cold `lean -j1` Per-Module Time & Heartbeats** | **Landed (`perf_tracking.py`):** Wall-clock `theory_elab.<mod>.cold_j1_ms` under `lean -j1 -M2048 -t0 -DElab.async=false -Ddebug.skipKernelTC=false` (`+ -DwarningAsError=true` for `Anneal.*`), plus `TrustedBoundary` ban on `set_option` (`maxHeartbeats`) | **Landed Tier A Hard Ceiling:** `<= 75,000 ms` (`75 s`, leaving `45 s` safety headroom below `installed_smoke`'s `120 s` child timeout)<br>**Landed Tier B (`main`):** Rolling 25-commit `Median / MAD` step-shift detector (`z > 3.5` sustained or `z > 6.0` severe) | Names exact slow module + critical-path contribution (`theory_elab.summary.*`); split `4,000+`L modules or eliminate `Meta.whnf` `_sunfold` / nested `simp` blowups |
| **2. Per-Process Peak RSS (`ru_maxrss`)** | **Landed (`perf_tracking.py`):** Isolated child `maxrss_kib` via fresh-`exec` `/usr/bin/time` wrapper (avoiding Linux `exec_mm_put_old` parent `mm_struct` high-water contamination) across cold `lean -j1`, `TrustedBoundary.lean`, and `cargo-anneal verify` | **Landed Tier A Ceilings:** `<= 2,621,440 KiB` (`2,560 MiB` / `2.5 GiB`) for `memory_rss.theory_*.cold_j1_maxrss_kib`, `memory_rss.theory_elab.max_module_maxrss_kib`, and `memory_rss.verify_scalar.*_maxrss_kib` (`4` workers $\times$ `2.5 GiB` = `10 GiB` on `16 GiB` runners)<br>**Target Wave 3 (`#4016`/`#4109`):** Add standalone `SpecPreflight` / `leanexport <= 1,048,576 KiB` (`1 GiB`) and `nanoda_bin` / `con-ron <= 524,288 KiB` (`512 MiB`) | Reports exact metric ID + peak RSS (`KiB`); catches exponential `Expr` tree/unsharing blowups before kernel OOM-killer `SIGKILL` (`exit 137`) |
| **3. 3-Part Lean `module` `.olean*`, Binary, & Archive Artifact Budgets** | **Landed (`perf_tracking.py`):** Deterministic (`CV = 0%`) byte counts across all 3 `module` parts (`.olean`, `.olean.server`, `.olean.private`), release Rust binaries, and the packaged `.tar.zst` archive | **Landed Tier A Ceilings (`perf_budgets.json`):**<br>• `Trusted` / `Trusted.*` / `Anneal.*` public `.olean`: `<= 3,145,728 B` (`3 MiB`)<br>• `TrustedBoundary.olean`: `<= 25,165,824 B` (`24 MiB`)<br>• Per-module `.olean.private`: `<= 12,582,912 B` (`12 MiB`)<br>• Total bundled `.olean*` (`artifact_size.bundled_olean.total_bytes`): `<= 67,108,864 B` (`64 MiB`)<br>• Release binaries (`cargo-anneal`, `anneal-rustc-capture`, `anneal-audit`): `<= 33,554,432 B` (`32 MiB`) each; omnibus `.tar.zst`: `<= 943,718,400 B` (`900 MiB`)<br>**Landed Tier B (`main`):** `+5.0%` (`>= 4,096 B`) deterministic growth notice | Flags exact module/artifact + `.olean` vs. `.olean.private` split; catches accidental `@[expose]` leaking theorem proof bodies into public `.olean` and keeps `*Canaries.lean` out of user runtime cones (`D1-A`) |
| **4. End-to-End Pipeline, First-Customer Floor, & Quorum Stage Telemetry** | **Landed (`perf_tracking.py`):** Receipt v3 `timing_ms.{total,capture,proof_and_audit}` (recorded as `verify.scalar.{cold_no_cache,cold_prebuilt,warm_disk}_{total,capture,proof_audit}_ms` and `zerocopy_proofs.<unit>.*`), plus `verified_units_count` | **Landed Tier A Floor:** `zerocopy_proofs.suite.verified_units_count >= 4`<br>**Landed Tier B (`main`):** Rolling 25-commit `Median / MAD` latency regression detection (avoiding noisy wall-clock micro-shift PR blocks per [`perf-tracking.md`](perf-tracking.md#12-explicit-non-goals))<br>**Target Wave 3 (`#4016`):** Add per-substage `5-init`/`5a`/`5b`/`5c` and 2-/4-kernel `--paranoid-quorum` timing series (`scalar`, `starnix`) | Pinpoints phase or unit regression (`capture` vs. `proof_and_audit` today; `spec-preflight`, `5-init`, `5a`, `5b`, `5c`, `nanoda_bin`, `con-ron` once `#4016` lands) |

#### 5.2 Two-Level Axiom-Footprint and Constructive-Purity Gate

Because `leanexport` over `Init` definitions can include transitive library
declarations referencing `Classical.choice` even when a target or `theory/`
theorem's own `#print axioms` cone uses only `[propext]`, Anneal separates
**soundness admission** from **constructive hygiene**:

1. **Level 1 — Hard Soundness Ceiling (All Cones, Fail-Closed in
   `TrustedBoundary.lean` and `ndjson_comparator.rs`):**
   - Permitted foundation axioms: closed allowlist `{"propext", "Quot.sound",
     "Classical.choice"}` (with `"sorryAx"` admitted strictly on proof-only
     edges under explicit `--allow-sorry-in-proof`, tainting the receipt).
   - Unconditionally forbidden across `expected_cone` and `proof_full`:
     `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`,
     `Lean.reduceBool`, `Lean.reduceNat`, custom `axiom` declarations,
     `.opaqueInfo` (`opaque`), `partial`/`unsafe` definitions (`._unsafe_rec`),
     and foreign `.quotInfo` primitives.
2. **Level 2 — Constructive-Purity Ratchet (`theory/axiom-footprint.json`,
   Target Wave 3):**
   - Checked-in manifest mapping each exported `Trusted.*` and `Anneal.*` root
     declaration prefix to its exact maximal direct-cone axiom subset:
     - **`["propext"]` or `[]` (strictly constructive / kernel-computable):**
       `Anneal.PureLift.*`, `Anneal.CnfOrd.*`, `Anneal.LinearArith.*`,
       `Anneal.BitTrieLrat.*`, `Anneal.PTree.*`, `Anneal.SpineForce.*`, and
       `zerocopy` scalar/layout proofs.
     - **`["propext", "Quot.sound"]`:** Modules using quotient constructions
       without classical choice.
     - **`["propext", "Quot.sound", "Classical.choice"]`:** Explicitly opted-in
       classical helper modules (`Anneal.ClassicalEm` and consumers).
   - Verified automatically during Pass-1 repository audit (`anneal-audit`) so
     no constructive `theory/` module can silently acquire a `Classical.choice`
     dependency without an explicit manifest diff.

#### 5.3 Multi-Version Lean Compatibility Matrix (`v4.33.1` – `v4.35.0+`)

Test suites validate two distinct runtime audit paths without silent fallback:

- **Pinned `v4.34.1` (`foundation-lock.json`) & `v4.33.1` compat (`#4139`):**
  Exercises `SpecPreflight.lean` + `TrustedBoundary.lean` (`"target-audit"` with
  `#[serde(deny_unknown_fields)]` `LegacyTargetAuditVerdict`) and verifies
  `-DwarningAsError=true` compilation across `v4.33.1`, `v4.34.1`, and
  `v4.35.0`.
- **`v4.35.0+` (bundled `<sysroot>/bin/{leanexport,nanoda_bin,con-ron}`):**
  Automatically activates `SpecPreflight.lean` + `5-init`/`5a`/`5b`/`5c` +
  `ExecSeal` 2-kernel default (`NdjsonAuditVerdict`), with `--paranoid-quorum`
  exercising the 4-kernel quorum (`nanoda_bin`, `con-ron`, `con-leche`,
  `lean4lean --import`).

---

### 6. CI Tiering and Sequenced Rollout Roadmap

#### 6.1 Four-Tier CI Execution Matrix (`ci-core` & `anneal-perf.yml`)

Anneal's target check graph aligns `anneal-perf.yml` with `ci-core`'s offline
container/sandbox onboarding (`#4077`, `#4079`, `#4140`–`#4141`, which retires
`anneal.yml`, `anneal-current.yml`, and `#3993`'s `detect_changes` path filters,
using the `6.73 GiB` single-user Nix `anneal-tc` OCI image
under `NestedBwrap` with `--network=none` and read-only `/nix` `overlayfs`):

| CI Tier | Trigger & Isolation | Executed Suites & Gates | Wall-Clock Target | Caching Policy |
| :--- | :--- | :--- | ---: | :--- |
| **Tier 0: Static & Boundary Preflight** | Every PR, `merge_group`, & `push` (`Container --network=none`) | `root-manifest.sha256`, zero-symlink `trusted/`/`tests/` scan, `check_cargo_boundary` (2-zone lattice), `regenerate_bundle --check`, `check_todo.sh`, `check_pr_hygiene.py` (required, soft-blocking `PR hygiene` check in `anneal-pr-hygiene.yml`, outside `ci-core`), `check_skills.py`, Python `ci/test_*.py`, `--no-default-features` `cargo clippy` + `cli` offline tests | `< 90 s` | Content-addressed `cargo_locked` + `anneal-tc` image |
| **Tier 1: PR Verification & Regression Gate** | PRs touching `anneal/**`, CI TCB, or `zerocopy/proofs/**` (`ci-core`: `NestedBwrap` + `ubuntu-24.04-arm` `sandbox-aarch64`) | Workspace unit + single-binary integration suites (`anneal-testkit`, `anneal-audit-tests`, `cargo-anneal-tests`, `anneal-itree-diff` in `DegradedNoMiri` parity mode when `bin/miri` is trimmed from the omnibus archive, `anneal-rustc-capture-tests`) run via `cargo nextest run --profile ci --workspace --locked` (`D3-A`, keeping `cargo test --workspace --locked` supported), `adversarial/` `must-reject` corpus, Lean TCB `check_guard_mutation.py` (`104` `MirSemantics` + `8` header + `12` boundary: `124` guards), path-filtered Rust TCB guard ablation on PR-modified `trusted/**/*.rs` files (`D4-A`), `anneal-audit --require-correspondence` (with verified `lean-miri` `.olean` cache), `perf_tracking.py check-budgets` against `anneal/ci/perf_budgets.json` (plus target Wave-3 `theory/axiom-footprint.json`), `installed_smoke` + `verify_zerocopy.py` (`zerocopy/proofs/` + target `ratchet.json`) + `starnix` | `< 12 min` critical path | `ci-core` attested `Claim::Cache` (`lean-miri` `.olean` + Cargo target) |
| **Tier 2: Merge-Queue Assurance Gate** | `merge_group` (`NestedBwrap`) | **Pass-1 & Pass-2 `anneal-audit --require-correspondence`** (`miri-v1` restored only from an attested entry, rebuilt cold on key changes, verified against `UPSTREAM_PIN.json`, and kernel-replayed on every run), full Rust + Lean TCB guard-ablation matrix (`D4-A`), **4-kernel `--paranoid-quorum`** (`nanoda_bin` + `con-ron` + `con-leche` + `lean4lean --import` once `v4.35.0` lands), full `zerocopy/proofs/` (`real_crates/zerocopy`) verification | `< 18 min` | Cold on pin edits; attested `miri-v1`, SHA-256-verified against `UPSTREAM_PIN.json` (zero unverified `.olean` cache hits) |
| **Tier 3: Continuous `main` Telemetry & Scheduled Deep Sweep** | `push` to `main` (`.github/workflows/anneal-perf.yml`), nightly cron, & pre-release qualification (`0.2.0-alpha.11+`) | Continuous `perf_tracking.py collect`/`analyze`/`check-budgets` + static dashboard publication on `benchmark-data` (`anneal-perf.yml`), full **all-guards Rust + Lean TCB ablation matrix** (recompiling all `rustc-capture`/`audit`/`cargo-anneal` single-guard mutants per `D4-A`), full 4-way **`differential/` Miri $\leftrightarrow$ `MirSemantics` boundary/fuzz sweep**, multi-version Lean (`v4.33.1`/`v4.34.1`/`v4.35.0`) matrix, and extended external crate smoke suite | `< 45 min` | Isolated ephemeral runners |

The `ci-core` cutover changes where some former pre-merge Anneal checks run.
Before merge, `anneal/ci/run_anneal_check.sh` packs the omnibus archive with
`.#omnibus-archive`'s excludes, deterministic tar flags, leak bans, required
entries, and in-archive `library-lock.json` sysroot-tree verification
(`anneal/ci/test_run_anneal_check.py` fails if it drifts from `flake.nix`),
but from the `anneal-tc` image rather than through `nix build`.
`nix build .#omnibus-archive` itself, and the omnibus budget in
`anneal/ci/perf_budgets.json`, now run only after merge, on every `main` push
in `anneal-perf.yml`, and during release in `release.yml`. Cold `main`-branch
`lean-miri` builds are no longer exercised. `run_anneal_check.sh` restores the
legacy job deadlines with `timeout`: 90 minutes for `ws-test`, `audit`,
`installed-smoke`, and `guard-mutation`, and 30 minutes for `clippy`,
`flake-eval`, `ci-tests`, and `sandbox`; the `ci/scripts/run_*.sh` entrypoints
are capped the same way. `ci-core` checks cannot read Git history, so
`check_pr_hygiene.py` runs in `.github/workflows/anneal-pr-hygiene.yml` as the
`PR hygiene` check, which the `main` ruleset requires alongside
`ci-core / gate`. Its findings can be waived only by a `Skip-pr-hygiene:`
trailer on the PR's `HEAD` commit, as
[`docs/scaffolding.md`](scaffolding.md) describes.

#### 6.2 Phased Rollout Roadmap (Landed Baseline vs. Remaining Stages)

Waves 0 (core foundation and `D1-A`), 1, and 2A have landed on `main`. Ad-hoc
per-file line-coverage padding remains **frozen** until Wave 2B finishes
decomposing the remaining `audit` and `rustc-capture` monoliths and Wave 3
completes the declarative corpora.

| Wave | Status on `main` | Scope & Concrete Deliverables | Sequencing & Acceptance Invariants |
| :--- | :--- | :--- | :--- |
| **Wave 0 (Foundation, Perf Pipeline, & `D1-A`)** | **Core & `D1-A` Landed; `#4016`/`#4109` & `ci-core` In Progress** | **Landed on `main`:** `#4078` (balanced Lean list literals), `#4131` (`enum_id` scoping & `--env`), `#4137` (`ci/check_skills.py`), `#4138` (`ANNEAL_RELEASE_LOCK`, superseded by commit-bound dispatch), `#4139` (`6a0932de51`, Lean 4 `module` 3-part `.olean*` + `4.33`–`4.35` compat), `#4142` (`7c7f821539`, cross-family Gate 2), `#4148` (`d3362d9a65`, `zerocopy/proofs/` + `verify_zerocopy.py`), `#4171`–`#4173`/`#4212` (`perf_tracking.py`, `perf_budgets.json`, static dashboard, and `anneal-perf.yml`), and **`D1-A`** (`*Canaries*.lean` decoupled from runtime umbrellas; monolithic `theory/Anneal.lean` retired in favor of demand-driven domain umbrellas `Anneal.Scalar`, `Anneal.Wp`, `Anneal.Simd`, and `Anneal.PureLift`, keeping `share/anneal/theory` matched 1-for-1 to `bundle-manifest.json`'s `20` modules).<br>**Remaining queue:** Land `#4016`/`#4109` (`SpecPreflight.lean` + `ndjson_comparator` `5a`/`5b`/`5c` + multi-kernel `ExecSeal`), and cutover cleanup (`#4125` relocates `docs/` if merged). | Zero `module` $\times$ `ndjson_comparator` regressions; `*Canaries*.lean` excluded from domain umbrellas and user bundles (`0` `*Canaries*` in `20` bundled modules) while `scan_lean_tree` discovers and audits every `.lean` module under `theory/` in repository Pass-1 `anneal-audit`. |
| **Wave 1 (`#4015` Two-Zone Split & `anneal-testkit`)** | **Landed (`#4154`, `#4159`); Optional Active-Member & CI `nextest` Follow-Up** | **Landed on `main`:** `#4154` (`348147c22d`, closing `#4015`) moved `trusted/{audit,cargo-anneal,rustc-capture}/tests/` into fenced `tests/{audit,cargo-anneal,rustc-capture}/` crates (`publish = false`, `*-test-bin` shims, `trusted/cargo-anneal/assets/scalar/`, lockstep policy updates keeping `anneal/AGENTS.md` at `30,654 B` below `check_skills.py`'s `31,744 B` cap); `#4159` (`aa8d82c9bb`) added the `WorkspaceZone::Trusted(0) < WorkspaceZone::Tests(1)` monotonic lattice and `proc-macro` ban in `cargo_boundary.rs`, `tests/testkit` (`anneal-testkit`: `toolchain`, `workspace`, `process`, `store_sim`, `corpora`, `assertions`), and `anneal/.config/nextest.toml`.<br>**Remaining follow-up:** Optionally tighten `cargo_boundary.rs` active-member checks for all three `trusted/*` crates in `workspace.members` (rejecting `workspace.exclude`), and switch CI test steps to `cargo nextest run --profile ci` (`D3-A`) once `anneal-tc` / `flake.nix` bundles `cargo-nextest`. | `anneal/trusted/` reduced by `31,016` LOC at `#4154`; 2-zone boundary + `proc-macro` negative/positive tests active; `cargo test --workspace --locked` preserved alongside `nextest`. |
| **Wave 2A (`cargo-anneal` Split & `D2-A`)** | **Landed (`#4187`, `a508ef1ba6`)** | Executed **`D2-A`**: retired and deleted `integration.rs`, `mvp_e2e.rs`, and the `1,388`-line `/// anneal:*` doc-comment synthesizer; migrated `19` scalar spec/proof suites into `tests/corpora/scalar_specs/`, `27` capture-refusal cases into `tests/corpora/adversarial/capture/`, and `scalar`/`spin`/`unsafe_identity` into `tests/corpora/`; split `cargo-anneal-tests` into `<800`L submodules under `tests/cargo-anneal/tests/suite/` (`main.rs` + 7 submodules, including `split_store_bwrap.rs` exercising `run_in_simulated_nix_store` alongside `#4159`'s 5-cell `ElfStoreBuilder`). | Doc-comment synthesizer deleted; `cargo-anneal` `suite/*` submodules modularized atop `anneal-testkit`; simulated `/nix/store` `symlinkJoin` tests passing without host Nix. |
| **Wave 2B (Testkit Consolidation & Remaining Monolith Decomposition)** | **In Progress (Testkit Migration & Shim Retirement Landed; Submodule Split Remaining)** | **Landed:** expanded `anneal-testkit` (`digest`, `case_runner`, `audit_fixture`, `mir_wp_fixture`); migrated `harness.rs`, `sandbox_escape.rs`, `installed_smoke.rs`, `profile_v2_e2e.rs` (split into `10` parallel tests), `support_{paths,regressions,signals}.rs`, `compiler_session.rs`, `stdlib_capture.rs`, `typed_capture.rs`, `audit/tests/common/{mod,correspondence_dsl}.rs`, `boundary_audit.rs`, and `target_audit.rs` directly onto `anneal-testkit`; deleted `tests/cargo-anneal/tests/support/mod.rs` and `tests/rustc-capture/tests/common/mod.rs` shims.<br>Split `tests/audit/tests/boundary_audit.rs` into domain submodules under `tests/audit/tests/boundary_audit/`.<br>**Remaining:** break up `boundary_audit` tests longer than `800`L, and decompose `tests/audit/tests/target_audit.rs`, `tests/rustc-capture/tests/typed_capture.rs`, `tests/cargo-anneal/tests/cli.rs`, and `tests/itree_diff/tests/itree_differential.rs` into `<800`L domain submodules under single-binary `tests/suite/main.rs` targets. | Pure `anneal/tests/` refactoring (`0` `anneal/trusted/` edits); zero test files `> 1,000` lines; zero duplicated `Tools::discover`, `MirWpSyntheticSpec`, or `TempFixture` helpers. |
| **Wave 3 (Expanded Corpora, Rust Guard Ablation, & Quorum/Axiom Gates)** | **Target** | Expand `tests/corpora/adversarial/` (`guards.toml` adding Rust TCB guards for `rustc-capture`, `cargo_boundary`, and `ndjson_comparator` with path-filtered Tier 1 + full Tier 2/3 ablation per `D4-A`, plus `spec_and_preflight/`, `mir_ub_refutations/`, `audit_and_ndjson/`), add `tests/corpora/differential/` (`Miri <-> MirSemantics` directional refinement + `v4.35.0+` 2-/4-kernel NDJSON quorum suites once `#4016` lands), add `tests/corpora/real_crates/` (`zerocopy/ratchet.json` item-class floors + `external/starnix/`), extend `perf_tracking.py` with quorum stage/RSS metrics, and enable `theory/axiom-footprint.json`. | `100%` Lean + Rust cataloged guard kill rate ($K_{\text{entry}} = 100\%$); monotone `zerocopy` item-class ratchet active; NDJSON quorum and `axiom-footprint.json` gates active. |
| **Wave 4 (Targeted Coverage & Fuzz Expansion)** | **Target** | *Only after Waves 2B–3 are merged:* measure branch/guard coverage gaps in `trusted/` (`cargo-llvm-cov`, disabling `--remap-path-prefix` strictly inside isolated coverage runs so line tables resolve cleanly without affecting release or hermetic builds) and add declarative corpus entries or property tests solely for uncovered high-risk state transitions. | High-signal branch & guard coverage across `trusted/` with minimal declarative corpus additions (`10–30` lines per entry). |

---

## Partition 2 — Decision Rationale and Eliminated Alternatives

### 7. Comparative Evaluation and Falsified or Dominated Alternatives

Every structural choice in Partition 1 was evaluated against the live
`google/zerocopy@74d509c852` / `c351dd381a` codebase and eliminated alternatives
on explicit contract violations, empirical falsifications, or strict comparative
dominance:

| Area | Eliminated Alternative | Elimination Basis (Contract Violation, Falsification, or Dominance) |
| :--- | :--- | :--- |
| **Workspace Containment** | **A1. Retain integration suites under `anneal/trusted/*/tests/`** (brownfield incumbent at `c351dd381a`). | **Violates `C+1` (TCB Isolation):** Leaves `50` non-TCB files (`30,302` lines, `33.96%` of `anneal/trusted/`) inside the human-audited TCB directory, forces fragile `exclude` lists in `trusted/cargo-anneal/Cargo.toml`, and retains `tests/`-only dependencies (`wait-timeout`, fixture archive builders) in the production TCB manifest. |
| **Workspace Containment** | **A2. Strict target-only dependency check `rel_str.starts_with("trusted/")`** across all workspace members. | **Comparatively Dominated by Two-Zone Monotonic Lattice (`zone(dst) <= zone(src)`):** While `rel_str.starts_with("trusted/")` blocks `trusted/ -> tests/`, it also rejects `tests/{audit,cargo-anneal,rustc-capture} -> tests/testkit`, forcing 4x harness duplication across test crates or pushing `testkit` back into `trusted/`. The 2-zone lattice (`0 <= 0`, `0 <= 1`, `1 <= 1`, forbidding `1 <= 0`) preserves identical `trusted/` isolation while admitting `anneal-testkit`. |
| **CLI Binary Resolution** | **A3. Invoke `target/debug/cargo-anneal` by relative path from `tests/*` instead of `*-test-bin` shims.** | **Empirically Falsified (under feature flags):** Cargo does not rebuild sibling-crate binaries when running `cargo test -p cargo-anneal-tests --no-default-features --test cli`, allowing a stale default-feature binary in `target/debug/` to satisfy an offline test falsely. `#[doc(hidden)]` library CLI delegation + `*-test-bin` shims preserve exact active Cargo features via `CARGO_BIN_EXE_*` with zero binary name collisions. |
| **Monolith Decomposition** | **A4. Split monoliths into `20–30` separate top-level `tests/*.rs` Cargo test targets.** | **Comparatively Dominated by Single-Binary Domain Submodules (`tests/suite/main.rs`) + `cargo-nextest`:** Cargo links a separate executable per top-level `tests/*.rs` file; linking `anneal-audit` and `rustc_private` drivers `25` times inflates compile/link latency and adds multi-GiB `target/` disk pressure on standard 14–32 GB CI runners. Submodules under `tests/suite/main.rs` achieve `<800`L file modularity with **one** link per crate, while `cargo-nextest` isolates every `#[test]` in its own OS process. |
| **Hermetic Split-Store Testing** | **A5. Test split-output Nix `symlinkJoin` Lean trees (`0002-lean-joined -> 0001-lean-unwrapped`) and `0o555` stores directly in raw `/tmp` `TempDir`s.** | **Empirically Falsified (on Linux):** (1) `sandbox.rs:588-600` (`symlink_stays_within_dedicated_root`) rejects cross-package symlinks inside `lib/lean` unless both canonical paths start with `/nix/store`; (2) `identity.rs:381-387` rejects `PT_INTERP`/`DT_RUNPATH` dirs if `cwd` shares their ancestor root; (3) `TempDir::drop` fails with `EACCES` on `0o555` directories. `ReadOnlyTreeGuard` + sibling `store/`/`work/` + `bwrap --ro-bind <store> /nix/store` resolves all three deterministically without host Nix. |
| **Declarative Directives** | **A6. Adopt `dtolnay/trybuild` whole-`.stderr` byte snapshots or expand `integration.rs`'s `1,388`L `/// anneal:*` Rust doc-comment synthesizer.** | **Comparatively Dominated:** `trybuild` `.stderr` snapshots break on harmless nightly `rustc` diagnostic formatting shifts and lack `Capture`/`Preflight`/`Proof`/`Audit` stage typing; conversely, growing a bespoke `1,388`L Rust parser inside `integration.rs` tests test-only code rather than Anneal's real specification/request pipeline. Stage-typed `//@ fail(<stage>)` directives over native requests + real specs preserve polarity-locked precision with zero shadow compiler. |
| **Multi-Kernel Proof Replay** | **A7. Wrap `lake comparator --paranoid` or `leanchecker --from-export` as the Lean `v4.35.0+` verdict gate** (earlier target sketch in [auditing-and-comparator.md](auditing-and-comparator.md#optional-paranoid-multi-kernel-ci-mode)). | **Empirically Falsified (on `leanprover/lean4` `v4.35.0`):** `Lean.Kernel.Environment.replay` (`src/lean/Lean/Replay.lean:77, 186`) iterates `NameSet` in `Name.quickCmp` hash order without recursing on implicit string-literal reduction constants (`String.ofList`), failing on every real Anneal `Captured.program` string literal; additionally, `lake comparator` hardcodes `"unpermitted_axiom_hard_error": false` in `nanoda_bin`. Running `nanoda_bin` (`"unpermitted_axiom_hard_error": true`), `con-ron --verified`, `con-leche`, and `lean4lean --import` directly under strict Rust config checks inside `ExecSeal` is faster (`<3.0 s`), stricter, and immune to `Replay.lean` ordering bugs while `leanchecker --from-export` remains deferred behind a non-gating probe. |

---

## Partition 3 — Policy Decisions, Outcome Contract, and Calibration

### 8. Confirmed Policy Decisions (`D1-A`–`D4-A`)

The four policy trade-offs below were resolved with maintainer confirmation of
**`D1-A`**, **`D2-A`**, **`D3-A`**, and **`D4-A`** (`anneal-testkit`,
`corpora/`, and `ci/perf_tracking.py` + `ci/perf_budgets.json` execute these
choices declaratively via configuration and manifests). Rejected options and
blast radii remain documented below for durable architectural rationale.

#### Decision D1: `Anneal.lean` & Canaries vs. `bundle-manifest.json` (`D1-A`)

- **Context (Measured at `74d509c852` / `c351dd381a`):**
  `theory/bundle-manifest.json` embeds `18` `theory/` modules (`16,799`L) into
  `cargo-anneal` (`bundled_theory.json`), whereas `theory/Anneal.lean`
  re-exports all `54` `theory/` modules (`60,192`L—including `36` unbundled
  modules totaling `43,393`L AND internal `*Canaries.lean` test suites totaling
  `~56 s` of single-core Lean elaboration CPU). Because `flake.nix` copies all
  of `theory/` into `share/anneal/theory` and `installed_smoke.rs:lean_case`
  compiles the transitive closure of `Anneal.lean` cold with `lean -j1`,
  `installed_smoke` pays for `3.58x` the bundled `theory/` LOC (`60,192 /
  16,799` lines; `3.95x` or `66,307 / 16,799` lines across the combined
  `trusted/lean/` + `theory/` closure) and drags `*Canaries.lean` into
  user-imported runtime umbrellas (`Anneal.MirWp`, `Anneal.PureLift`).
- **Options Considered:**
  - **Option D1-A (Confirmed & Landed):** Decouple `*Canaries*.lean` from
    runtime umbrella modules (`Anneal.MirWp`, `Anneal.PureLift`, `Anneal.Core`,
    `Anneal`, and sibling subsystem umbrellas) and from
    `theory/bundle-manifest.json` so `*Canaries*.lean` are compiled and audited
    strictly in Pass-1 repository `anneal-audit` (`test-and-verify`), AND
    require `theory/Anneal.lean` (subsequently retired in favor of domain
    umbrellas) + `share/anneal/theory` to match `theory/bundle-manifest.json`
    1-for-1 (promoting mature modules like `PureLift` into
    `bundle-manifest.json` explicitly when shipped to users).
  - **Option D1-B:** Keep `theory/Anneal.lean` as a repository-wide superset
    umbrella (divergent from `bundle-manifest.json`), decouple `*Canaries.lean`
    only, and scope `installed_smoke` `lean-file` strictly to
    `bundle-manifest.json` roots while `test-and-verify` compiles the rest of
    `theory/`.
  - **Option D1-C (Status Quo):** Keep all `54` `theory/` modules (including
    `*Canaries.lean`) reachable from `Anneal.lean` and compiled cold in
    `installed_smoke`.
- **Confirmed Decision (`D1-A`):** Eliminates the silent divergence between
  `cargo-anneal`'s embedded `bundled_theory.json` and the `exocrate` archive's
  `share/anneal/theory`, removes `~56 s` of dead canary elaboration + `5b`
  NDJSON export bloat from user builds, and keeps `installed_smoke` well below
  its `120 s` ceiling. To keep repository non-backsliding and packaged smoke
  audits mutually consistent:
  1. `TrustedBoundary.lean` (`verifyMirWpCoreTheorems`) unconditionally requires
     both `Anneal.MirWp` (`WpSoundnessClaim`, `WpFaultSoundnessClaim`,
     `ExecSoundnessClaimV2`, and public
     `Trusted.{Crate,CrateTheorem,UnitTheorem}` and
     `Trusted.{CrateV2,CrateTheoremV2,UnitTheoremV2}` aliases) and
     `Anneal.MirWp.Canaries` (all 26 `MirWp` canary `*Claim` proofs with
     `expectedProofMod = Anneal.MirWp.Canaries`) whenever `requireMirWp` is
     `true` or any MIR/`PureLift`/`MirWp` module is loaded (no conditional
     bypass when `Anneal.MirWp.Canaries` is absent);
  2. Repository Pass-1 `anneal-audit` (`repo_audit.rs`) dynamically discovers
     all `.lean` files under `anneal/theory/` via `scan_lean_tree`, auditing
     and kernel-replaying the real `Trusted` + `Anneal.MirWp` +
     `Anneal.MirWp.Canaries` closure alongside every decoupled
     `*Canaries*.lean` suite present on disk (`TrustedBoundary.lean` requires
     only `Anneal.MirWp.Canaries` among canary modules, while the repository
     `boundary_audit` test
     `theory_umbrella_and_manifest_exclude_canaries_and_match`, asserting named
     canary suites and `canary_modules.len() >= 16`, guards against deleting
     the other decoupled `*Canaries*.lean` modules); and
  3. Because `share/anneal/theory` omits `*Canaries*.lean` and
     `TrustedBoundary.lean` unconditionally requires `Anneal.MirWp.Canaries`,
     `installed_smoke.rs` splits installed smoke coverage cleanly: `lean-file`
     parses `share/anneal/theory/bundle-manifest.json`, walks all of
     `share/anneal/theory` recursively (allowing only `bundle-manifest.json`,
     root `Anneal.lean`, and `Anneal.*` modules with `0` `*Canaries*`), checks
     1-for-1 `Anneal.*` parity across the installed tree,
     `bundle-manifest.json`, and the transitive `Anneal` import closure, and
     compiles the shipped `share/anneal/{trusted,theory}` closure with the
     packaged `lean` binary, while `audit-accepted` exercises the standalone
     `anneal-audit` binary's packaged locks, preflight, compilation, Phase-2
     kernel replay, and `verifyMirWpCoreTheorems` enforcement on a
     self-contained synthetic `Trusted.*` + `Anneal.MirWp` +
     `Anneal.MirWp.Canaries` fixture (installed `audit-accepted` no longer
     audits shipped `Trusted`/`MirWp` Lean sources directly).

  Subsequently, monolithic `theory/Anneal.lean` is retired in favor of
  demand-driven domain umbrellas (`Anneal.Scalar`, `Anneal.Wp`, `Anneal.Simd`,
  and `Anneal.PureLift`), keeping `share/anneal/theory` (verified by
  `lean-file` to exclude `Anneal.lean` and `*Canaries*`) matched 1-for-1 to
  `theory/bundle-manifest.json` (`20` bundled modules) while `scan_lean_tree`
  (`require_umbrella = false` for `"Anneal"`) continues to discover and audit
  every `.lean` module under `theory/`.
- **Blast Radius:** Touches `anneal/theory/**/Canaries*.lean` import/re-export
  edges across `Anneal.{MirWp,PureLift,Core,ByteRun,ByteSubLens}` and
  `Anneal.{CallStackUnwind,CnfOrd,F2Simd,MirTotal,OverflowCastJoin,RefFrame}`,
  `anneal/theory/Anneal/MirWp/Canaries.lean`,
  `anneal/correspondence/Anneal/MirCorrespondence/Canaries.lean`,
  `anneal/theory/Anneal.lean`, `anneal/theory/bundle-manifest.json` (removing
  `theory/Anneal/MirWp/Canaries.lean`; `bundled_theory.json` is now generated
  into `$OUT_DIR/bundled_theory.json` at build time rather than checked in),
  `anneal/flake.nix` (`share/anneal/theory` + `trusted/root-manifest.sha256`),
  `anneal/trusted/lean/Trusted/MirSemantics.lean`,
  `anneal/trusted/cargo-anneal/src/target.rs`,
  `anneal/trusted/audit/src/repo_audit.rs` +
  `anneal/trusted/audit/TrustedBoundary.lean`,
  `anneal/tests/audit/tests/boundary_audit.rs`,
  `anneal/tests/cargo-anneal/tests/installed_smoke.rs`, and
  `anneal/docs/{architecture,mir-correspondence-design}.md`,
  `anneal/docs/{scaffolding,testing-architecture,trust-model}.md`.

#### Decision D2: Retiring Doc-Comment Synthesis (`D2-A`, `#4187`)

- **Context (Source inspection at `c351dd381a`):**
  `integration.rs:907-2294` (`1,388` lines) implemented a test-only Rust lexer
  and Lean `Spec.lean`/`Proof.lean` synthesizer for `/// anneal:ensures(...)`
  doc comments across `6` fixture files (`42` initial scalar cases—`11` `pass`,
  `2` `fail(proof, ...)`, `2` `fail(spec)`, and `27` `fail(capture)` across
  `id.rs`, `items.rs`, `nonzero.rs`, `refs.rs`, `scale_50_fns.rs`, and
  `transmute.rs`, growing to `19` scalar spec/proof cases plus `27`
  `fail(capture)` cases before `#4187`). `cargo-anneal` itself never parses
  Rust doc comments.
- **Options Considered:**
  - **Option D2-A (Confirmed & Landed in `#4187`):** Convert the scalar
    spec/proof cases (including `safe_fn_requires_cannot_guard_ub` and native
    `Spec.lean` rejections `spec_preflight_rejected` and
    `spec_unknown_ident_rejected`) into explicit declarative
    `(lib.rs, Spec.lean, Proof.lean)` fixture directories under
    `tests/corpora/scalar_specs/` (`19` suites), move the `27` `fail(capture)`
    cases to `tests/corpora/adversarial/capture/` (which need zero Lean proof
    compilation), and **delete the `1,388`-line test-only synthesizer** (further
    expanding `adversarial/spec_and_preflight/` in Wave 3).
  - **Option D2-B:** Retain the `1,388`-line synthesizer quarantined inside a
    frozen `legacy_doc_spec_synth.rs` module solely for the existing scalar
    cases (forbidding new `/// anneal:*` fixtures), and delete it once Anneal's
    production surface-spec macro/annotation lands.
- **Confirmed Decision (`D2-A`, Landed at `a508ef1ba6`):** The `27`
  capture-refusal cases run without Lean proof compilation, while converting
  all `19` passing, proof-failing, and spec-failing scalar suites into native
  `(lib.rs, Spec.lean, Proof.lean)` fixtures preserves full rejection coverage
  and removes `1,388` lines of bespoke parser/synthesizer maintenance while
  testing the exact production `request.json` + `Spec.lean` pipeline.
- **Blast Radius:** Confined strictly to `anneal/tests/cargo-anneal/` and
  `anneal/tests/corpora/` (`0` production `trusted/` impact).

#### Decision D3: `cargo-nextest` as Workspace Test Runner (`D3-A`)

- **Context:** `ci-core`'s `zc-nightly` and `zc-stable-msrv` images already
  bundle `cargo-nextest` (`0.9.152`), as does `anneal-tc`, whose
  `anneal-ws-test` check (`anneal/ci/run_anneal_check.sh`) runs
  `cargo nextest run --workspace --locked --offline` without `--profile ci`
  and keeps `cargo test` only for doctests and the `cargo-anneal` lib/CLI
  suites (`anneal/.config/nextest.toml` landed in `#4159`).
- **Options Considered:**
  - **Option D3-A (Confirmed):** Pre-install pinned `cargo-nextest` inside
    `anneal-tc` (and `anneal/flake.nix` devShell) and run `cargo nextest run
    --profile ci --workspace --locked` in CI while keeping `cargo test
    --workspace --locked` 100% supported for local contributors without
    `nextest` (`anneal-testkit` enforces `-pgid` reaping + kernel
    `PR_SET_PDEATHSIG` + `ReadOnlyTreeGuard` restoration internally, while
    `nextest` isolates the process-wide Linux subreaper per `#[test]`).
  - **Option D3-B:** Keep `cargo test` everywhere in CI and rely solely on
    `anneal-testkit`'s internal subprocess supervisor and `Condvar` concurrency
    cap.
- **Confirmed Decision (`D3-A`):** Provides process-per-test crash/env
  isolation, built-in JUnit/JSON slow-test telemetry, and declarative
  `threads-required` slot scheduling for heavy Lean tests while preserving
  `cargo test` compatibility (`anneal/.config/nextest.toml` landed in `#4159`;
  `anneal-ws-test` runs `nextest` from `anneal-tc`, while `--profile ci` and
  `flake.nix` bundling remain).
- **Blast Radius:** `anneal/.config/nextest.toml` (landed), plus one pinned
  binary in `anneal-tc` / `flake.nix` and the test step command in
  `ci/checks.toml` / `anneal/ci/run_anneal_check.sh`.

#### Decision D4: CI Tiering for Rust TCB Guard Ablation (`D4-A`)

- **Context:** Lean TCB guard mutation (`205` guards in
  `check_guard_mutation.py`: `185` `MirSemantics` + `8` header + `12` boundary
  guards) reuses precompiled `BASE_TRUSTED_MODULES` and `TrustedBoundary` /
  `SpecPreflight` `.olean`s inside `NestedBwrap` (already running in Tier 1 PR
  CI). By contrast, mutating `N` Rust TCB guards in
  `trusted/{rustc-capture,audit,cargo-anneal}` requires incremental
  `cargo build` recompilation of the mutated Rust crate (`~2–6 s` per guard
  for `audit`/`cargo-anneal`; `~8–15 s` per guard for `rustc_private`-linked
  `rustc-capture`, or `~4–6 min` for `30` Rust guards across `4` cores).
- **Options Considered:**
  - **Option D4-A (Confirmed):** **Path-filtered hybrid tiering** — run Lean TCB
    guard mutation on every Anneal PR (Tier 1); run **per-file
    targeted Rust TCB guard ablation** in Tier 1 *only* for `.rs` files under
    `anneal/trusted/` actually modified by the PR diff (`~15–60 s` incremental
    when `trusted/*.rs` changes, **`0 s`** on `theory/`, `docs/`, or `zerocopy`
    proof PRs), and run the **full all-guards Rust + Lean ablation matrix** on
    `merge_group` (Tier 2) or nightly (Tier 3).
  - **Option D4-B:** Run the full Rust + Lean guard-ablation matrix
    unconditionally in Tier 2 (`merge_group`) and Tier 3 (nightly) only, keeping
    Tier 1 PRs strictly to Lean guard mutation + unmodified `adversarial/`
    `must-reject` execution.
  - **Option D4-C:** Run the full Rust + Lean guard-ablation matrix
    unconditionally on every Tier 1 PR (`+4–6 min` per PR).
- **Confirmed Decision (`D4-A`):** Catches weakened Rust TCB guards pre-review
  on the exact PRs that edit `trusted/**/*.rs` at `<60 s` incremental cost
  while imposing zero latency tax on `theory/` or `zerocopy/proofs/` PRs.
- **Blast Radius:** Configures `ci-core` (`ci/checks.toml`) check filter
  flags (`--changed-files` on PRs vs. `--all` on `merge_group`/nightly);
  identical `guards.toml` manifest across all options.

---

### 9. Outcome Contract Ledger and Epistemic Calibration

#### 9.1 Sealed Outcome Contract `(C+, C-)`

- **Confirmed Positive Obligations (`C+`):**
  - `C+1` (TCB Isolation): Move non-production test suites out of
    `anneal/trusted/` into `publish = false`, build-script- and proc-macro-free
    workspace crates under `anneal/tests/`, enforcing one-way `tests/ ->
    trusted/` boundary containment and active TCB membership in
    `check_cargo_boundary` while permitting shared `tests/ -> tests/testkit`
    dependencies.
  - `C+2` (Shared Scaffolding & Monolith Decomposition): Consolidate duplicated
    harness logic into typestate-safe `anneal-testkit` (including process-group
    + subreaper supervision and hermetic split-store / symlink / ELF
    `DT_RUNPATH` simulation) and decompose `boundary_audit.rs`,
    `integration.rs`, `typed_capture.rs`, `target_audit.rs`, and `mvp_e2e.rs`
    before line-coverage expansion.
  - `C+3` (Declarative Soundness, Differential, & Real-Crate Corpora): Establish
    data-driven `adversarial/` (`must-reject` + guard-ablation),
    `differential/` (`rustc`/`Miri` $\leftrightarrow$ `MirSemantics` +
    `v4.35.0+` multi-kernel NDJSON replay), and `real_crates/` (verbatim
    `zerocopy` + pinned external crates) suites.
  - `C+4` (Performance, Memory, Artifact, & Axiom Gates): Enforce cold
    `lean -j1` time, child peak RSS, 3-part `module` / 1-part `.olean*` size,
    stage-latency, and constructive axiom-footprint regression gates, alongside
    confirmed policy decisions `D1-A`–`D4-A`.
  - `C+5` (CI Sequencing & Public Hygiene): Sequence cleanly across the landed
    foundation and test-boundary PRs (`#4015`/`#4154`, `#4078`, `#4131`,
    `#4137`–`#4139`, `#4142`, `#4148`, `#4159`, `#4171`–`#4173`, `#4187`) and
    open `ndjson_comparator` / `ci-core` streams (`#4016`/`#4109`, `#4077`,
    `#4079`, `#4140`–`#4141`), maintaining 100% OSS-clean documentation.
- **Confirmed Exclusions & Retired Foil Assumptions (`C-`):**
  - `C-1`: Zero ad-hoc per-file patch tests or line-coverage padding ahead of
    Wave 1–3 scaffolding.
  - `C-2` *(completed during specification phase)*: Kept architectural
    specification authoring strictly read-only with zero production code edits
    prior to policy sign-off on `D1-A`–`D4-A`.
  - `C-3` *(retired foil)*: Retire `installed_smoke` test-binary
    self-re-execution (`install_archive_worker`) once `setup::install_at` /
    `--install-dir` is called directly via `cargo-anneal`.
  - `C-4` *(retired foil)*: Exclude binary `.olean` mutation stubbing and
    1-part-only `.olean` assumptions for Pass-1 `module` libraries (`#4139`).

#### 9.2 Verification Basis & Epistemic Calibration

- **Specification Status:** **Confirmed Target Architecture (`D1-A`–`D4-A`
  Approved)** — Normative architecture in Partition 1 and policy decisions
  `D1-A`–`D4-A` in §8 are locked in; Waves 0 (core foundation and `D1-A`), 1,
  and 2A are merged on `main`, and implementation continues across Waves 2B–4.
- **Primary Evidence Basis:**
  - *Direct source inspection & measured repository invariants (verified against
    initial design baseline `google/zerocopy@74d509c852` / `c351dd381a` and
    post-Wave-2A `main` through `eb65abdaca71`):* Pre-move baseline counts
    (`113` `trusted/` files / `89,220`L and `50` `trusted/*/tests/` files /
    `30,302`L at `c351dd381a`; `31,016`L removed from `trusted/` in
    `348147c22d`); landed `anneal-testkit` + 2-zone lattice (`aa8d82c9bb`),
    `perf_tracking.py` + `perf_budgets.json` (`62ac035eed`), `zerocopy/proofs/`
    (`d3362d9a65`), and `cargo-anneal` suite decomposition (`a508ef1ba6`); `48`
    cataloged Lean guards in `ci/check_guard_mutation.py`; `73`-module
    `66,307`L `Anneal` umbrella vs. `18`-module `16,799`L
    `bundle-manifest.json` at `c351dd381a` (`19` bundled modules after
    `#4093`); `20`-file `33,939`L `zerocopy/src/` tree; standalone execution
    verifying the 12-case 2-zone boundary lattice, `0o555` `EACCES` vs.
    top-down `chmod` teardown, `cwd`/`DT_RUNPATH` sibling disjointness, and
    unprivileged `bwrap --ro-bind <store> /nix/store` cross-package symlink
    resolution; and Lean `v4.34.1` / `v4.35.0` `module` 3-part `.olean*` +
    `ndjson_comparator` (`nanoda_bin`, `con-ron`, `con-leche`,
    `lean4lean --import`) measurements.
  - *Empirically falsified premises:* `leanchecker --from-export` on `String`
    literal exports (`Lean/Replay.lean` `String.ofList` `Name.quickCmp` ordering
    bug on `v4.35.0`); 1-part-only `.olean` linking in `5a` `expected_lib/`
    under Lean `module` mode; host `/tmp` cross-package `lib/lean` symlinks
    outside `/nix/store`; naive `TempDir::drop` on `0o555` directories.
  - *Calibrated scope limits:* Tier A ceilings in `anneal/ci/perf_budgets.json`
    (`75,000 ms` per-module cold `lean -j1`, `2,621,440 KiB` [`2.5 GiB`] RSS,
    `3 MiB` / `12 MiB` / `64 MiB` `.olean*` caps) are calibrated with wide
    headroom for `ubuntu-24.04` 4-vCPU / 16 GiB GitHub-hosted runners while
    Tier B rolling 25-commit `Median / MAD` analysis (`perf_tracking.py
    analyze`) tracks finer step regressions on `benchmark-data`; macOS Mach-O
    split-store simulation is out of scope because `anneal-rustc-capture`
    restricts typed MIR residency verification to Linux
    (`identity.rs:1438-1443`).

[paranoid-ci]: auditing-and-comparator.md#optional-paranoid-multi-kernel-ci-mode
