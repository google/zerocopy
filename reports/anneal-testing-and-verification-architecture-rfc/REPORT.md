# Anneal Testing, TCB Isolation, Corpus Design, and Regression-Budget Architecture

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

At `google/zerocopy@74d509c8529b05e0e4839cc739d6da2fe0841e41`, `50` integration-test and harness files (`29,965` lines, or `33.92%` of `anneal/trusted/`) live inside `anneal/trusted/*/tests/`, coupling test-only dev-dependencies (`wait-timeout`, `tar`, `zstd`) to human-audited TCB manifests and duplicating tool discovery, temporary workspace staging, process supervision, and receipt parsing across six monolithic test files (`boundary_audit.rs` `9,824`L, `integration.rs` `4,315`L, `typed_capture.rs` `2,643`L, `target_audit.rs` `2,332`L, `mvp_e2e.rs` `1,566`L, `support*.rs` `4,851`L). Meanwhile, `theory/Anneal.lean` transitively imports `73` Lean modules (`66,307` lines, including `~56 s` of `*Canaries.lean`) versus `18` bundled modules (`16,799` lines) in `theory/bundle-manifest.json`.

This architecture establishes a TCB-isolated, data-driven testing and regression-gating framework across four pillars:
1. **Two-Zone Workspace Lattice (`Zone::Trusted = 0 < Zone::Tests = 1`):** Moves the `50` test files (`29,965` LOC) out of `anneal/trusted/` into `publish = false`, build-script-free crates under `anneal/tests/` (`anneal-testkit`, `anneal-audit-tests`, `cargo-anneal-tests`, `anneal-rustc-capture-tests`) using `*-test-bin` shims for exact Cargo feature propagation (`CARGO_BIN_EXE_*`), enforced by `check_cargo_boundary` (`zone(dst) <= zone(src)`).
2. **Typestate `anneal-testkit` & Monolith Decomposition:** Consolidates scaffolding behind `WorkspaceBuilder<Building> -> StagedWorkspace -> ExecutedRun<Out>`, Linux `PR_SET_CHILD_SUBREAPER` + `process_group(0)` deadline reaping, `ReadOnlyTreeGuard` top-down `0o555` teardown, 5-cell ELF `DT_RUNPATH`/`DT_RPATH`/`PT_INTERP` store simulation (`ElfStoreBuilder`), and `bwrap --ro-bind <store> /nix/store` `symlinkJoin` testing, while decomposing monoliths into `<800`L domain submodules under single-binary `tests/suite/main.rs` targets with `.config/nextest.toml`.
3. **Declarative Corpora (`anneal/tests/corpora/`):** Unifies polarity-locked `//@ fail(<stage>)` negative fixtures with `guards.toml` single-guard ablation (`100%` public-entrypoint kill rate across `46` Lean + Rust TCB guards), adds directional-refinement `Miri <-> MirSemantics` + `v4.35.0+` 2-/4-kernel NDJSON quorums (`differential/`), and anchors verbatim `zerocopy/src/` ratchets alongside SHA-256-pinned external smoke crates (`anneal/tests/fixtures/starnix/` `ebpf_core`, `10` files, `12,309` LOC).
4. **Four-Axis Perf/Memory/Artifact/Axiom Budgets & 4-Tier CI Roadmap:** Enforces per-module cold `lean -j1` time (`<= 45s` warn / `75s` fail), isolated `ru_maxrss` (`<= 2,560 MiB`), 3-part Lean `module` `.olean`/`.olean.server`/`.olean.private` size caps (`<= 2.5 MiB` public / `<= 6.0 MiB` private per module), end-to-end stage latency targets, and a constructive-purity ratchet (`theory/axiom-footprint.json`) across `ci-core` `NestedBwrap` Tiers `0`–`3` and Waves `0`–`4`.

## Applicability

Findings apply to the Anneal workspace in `google/zerocopy` at `74d509c8529b05e0e4839cc739d6da2fe0841e41`, spanning Lean `v4.33.1` (`#4139` compat), pinned `v4.34.1` (`foundation-lock.json`, `TrustedBoundary.lean`), and `v4.35.0+` (`SpecPreflight.lean`, `leanexport`, `nanoda_bin`, `con-ron`, `con-leche`, `lean4lean --import`). MacOS Mach-O split-store simulation is excluded because `anneal-rustc-capture` restricts typed MIR residency verification to Linux (`identity.rs:1497-1502`).

## Findings

### 1. Two-Zone Monotonic Workspace Lattice (`trusted/` vs. `tests/`)

Basis: source + execution (`google/zerocopy@74d509c852` + verified 12-case lattice probe).

- **Directory Partition:** `anneal/Cargo.toml` separates `Zone::Trusted` (`rank = 0`: `trusted/audit`, `trusted/cargo-anneal`, `trusted/rustc-capture`, `trusted/lean`, `trusted/correspondence`) from `Zone::Tests` (`rank = 1`: `tests/testkit`, `tests/audit`, `tests/cargo-anneal`, `tests/rustc-capture`, `tests/corpora`). Moving `50` files (`29,965`L) shrinks `anneal/trusted/` by `33.9%` (`88,328` → `58,460`L including the `97`-line `trusted/cargo-anneal/assets/scalar/` runtime example) and removes `wait-timeout`/archive dev-deps from `trusted/cargo-anneal/Cargo.toml`.
- **`check_cargo_boundary` Enforcement (`trusted/audit/src/cargo_boundary.rs`):**
  1. Every workspace member/exclude must classify cleanly under `trusted/` (`Trusted = 0`) or `tests/` (`Tests = 1`).
  2. Every `Zone::Tests` crate must declare literal `package.publish = false`.
  3. `package.build`, `package.workspace`, `build.rs`, `git`/`registry` deps, `..` target paths, `.cargo*`, `rust-toolchain*`, and `.gitmodules` are rejected in both zones.
  4. Across all dependency sections, local `path` dependencies must stay inside `member_set` and satisfy `zone(dst) <= zone(src)` (`trusted -> trusted`, `tests -> trusted`, and `tests -> tests` allowed; `trusted -> tests` rejected with `exit 1`, `phase = "cargo-boundary"`).
- **Feature-Synchronized `*-test-bin` Shims:** Because Cargo sets `CARGO_BIN_EXE_<name>` only for `[[bin]]` targets in the test crate itself, each test crate wraps a `#[doc(hidden)]` entrypoint (`anneal-audit-test-bin` → `anneal_audit::cli::main()`, `cargo-anneal-test-bin` → `cargo_anneal::cli::main()` mirroring `setup = ["cargo-anneal/setup", "dep:exocrate"]`, `anneal-rustc-capture-test-bin` → `anneal_rustc_capture::cli_main()` with `#![feature(rustc_private)] extern crate rustc_driver;`).

### 2. `anneal-testkit` Typestates, Subprocess Supervision, Split-Store Simulation, and Monolith Decomposition

Basis: source + execution (`identity.rs:440-446,713-740`, `sandbox.rs:520-532,588-600`, `support/mod.rs:263-276`).

- **Typestate Lifecycle (`anneal/tests/testkit/src/{toolchain,workspace}.rs`):**
  - `ToolchainMode` distinguishes `WorkspaceBuild` (`CARGO_BIN_EXE_*-test-bin`) from `InstalledBundle` (`ANNEAL_TEST_ARCHIVE` / `ANNEAL_TEST_INSTALL_ROOT`) so installed-smoke env vars never shadow local workspace binaries.
  - `WorkspaceBuilder<Building> -> StagedWorkspace -> ExecutedRun<Out>` allocates a `0o700` temp root split into disjoint `<root>/work/` (`cwd`), `<root>/store/` (simulated CAS/Nix packages), and `<root>/logs/commands/<NNNN>/{invocation.json,outcome.json,stdout,stderr,reproduce.py}`. `write_work_file` rejects symlinks and uses fresh-inode atomic `NamedTempFile::persist`.
- **Process-Group & Subreaper Supervision (`process.rs`):** Calls `prctl(PR_SET_CHILD_SUBREAPER, 1)`, spawns every command with `process_group(0)`, `env_clear()`, `Stdio::null()`, and file-backed `stdout`/`stderr`, and on timeout sends `kill(-pgid, SIGKILL)` and reaps `waitpid(-pgid, ...)` until `ECHILD` so timed-out `lean`/`rustc` grandchildren never leak `flock` handles. `reproduce.py` mirrors `process_group=0` and `SIGINT`/`SIGTERM` group forwarding.
- **Hermetic Split-Store & ELF `DT_RUNPATH` Simulation (`store_sim.rs`):**
  - `ReadOnlyTreeGuard::drop` restores `mode | 0o700` top-down on `0o555`/`0o444` simulated stores before `TempDir::drop` (`unlinkat` otherwise fails with `EACCES`).
  - Disjoint `<root>/store/<pkg>/lib` vs. `<root>/work/` satisfies `is_allowed_pt_interp_dir` (`identity.rs:440-446`) and `validate_toolchain_mount_dir` (`sandbox.rs:520-532`).
  - `ElfStoreBuilder` exercises 5 ELF cases: (1) non-transitive `DT_RUNPATH` failure on `libLLVM.so` missing co-located `libz.so.1`; (2) ancestor `DT_RPATH` suppression when intermediate DSO sets `DT_RUNPATH`; (3) ancestor `DT_RPATH` resolution without `DT_RUNPATH`; (4) consumer `DT_NEEDED` preloading; (5) `$ORIGIN/../lib` + relative `../../../libLLVM*.so*` symlinks and explicit `ld-linux` loader invocation, plus negative `st_dev`/`st_ino` splice probes (`status == "tool_failed"`).
  - `run_in_simulated_nix_store` launches `bwrap --unshare-all --die-with-parent --ro-bind <root>/store /nix/store` to test Nix `symlinkJoin` Lean trees (`symlink_stays_within_dedicated_root` at `sandbox.rs:588-600`) without host Nix.
- **Single-Binary Monolith Decomposition (`<800`L submodules + `.config/nextest.toml`):** Grouping domain submodules under one `tests/suite/main.rs` per crate avoids `25x` redundant `rustc_private`/`anneal-audit` link steps while `cargo-nextest` (`retries = 0`, `slow-timeout = 30s..45s`, `threads-required = 2` for `ndjson_quorum|correspondence|scale_|real_crates`) isolates every test in its own OS process:

| Legacy Monolith (`74d509c852`) | Target Crate & Binary | Decomposed `<800`L Submodules |
| :--- | :--- | :--- |
| `audit/tests/boundary_audit.rs` (`9,824`L, `53` tests) | `anneal-audit-tests` `tests/suite/main.rs` | `cargo_boundary`, `foundation_and_sysroot`, `pass1_preflight_and_tiers`, `pass1_mir_wp_gates`, `pass2_correspondence`, `bundle_parity_and_dag` |
| `audit/tests/target_audit.rs` (`2,332`L, `32` tests) | `anneal-audit-tests` `tests/target/main.rs` | `role_and_origin_gates`, `axiom_and_opaque_gates`, `module_and_universe_gates` |
| `cargo-anneal/tests/{integration.rs,mvp_e2e.rs}` (`5,881`L, `22` tests) | `cargo-anneal-tests` `tests/suite/main.rs` | `corpora_runner`, `receipt_and_bindings`, `host_and_stage_security`, `ndjson_quorum_e2e` |
| `cargo-anneal/tests/{cli,sandbox_escape,installed_smoke}.rs` + `support*.rs` (`4,851`L) | `cargo-anneal-tests` (`cli.rs`, `sandbox_escape.rs`, `installed_smoke.rs`) | Preserves `--no-default-features --test cli`, `sandbox-aarch64` coverage, and `InstalledBundle` testing |
| `rustc-capture/tests/typed_capture.rs` (`2,643`L, `48` tests) | `anneal-rustc-capture-tests` `tests/suite/main.rs` | `cli_and_publication`, `namespace_and_env`, `mir_extraction`, `linux_residency` |

### 3. Declarative Data-Driven Corpora (`adversarial/`, `differential/`, `real_crates/`)

Basis: source + execution (`Lean.Replay.lean:77,186`, `zerocopy/src/`).

1. **`adversarial/` (`must-reject` + `guards.toml`):** Stage-typed directives (`//@ pass`, `//@ fail(capture|preflight|proof|audit): "..."`, `//@ known_bug(#N, stage): "..."`, `//@ kills-guard: <id>`) with strict **polarity lock** (`ANNEAL_BLESS=1` cannot flip `pass <-> fail`). `guards.toml` extends the `46` cataloged Lean guards (`44` `Trusted/MirSemantics/*` + `2` header) to Rust TCB guards across `rustc-capture`, `audit`, and `cargo-anneal`, enforcing a `100%` public-entrypoint kill rate ($K_{\text{entry}} = 100\%$) with `NON_KILL_ERROR_MARKERS` filtering syntax-error false kills.
2. **`differential/` (2 Semantic Seams):**
   - *Seam A (`mir_oracle/`):* Compares native `rustc`, `cargo miri` (Tree Borrows), executable Lean `MirTotal`/`MirSemantics`, and `cargo-anneal verify` under `-C opt-level=0 -C debug-assertions=off -C overflow-checks=no`. Rejects `UnsoundValueMismatch` and `UnsoundMissedUb`; admits `ConservativeFault` only when explicitly annotated (`//@ differential: conservative_fault("<reason>")`).
   - *Seam B (`kernel_quorum/`, Lean `v4.35.0+`):* Exercises `5-init` (`39` `Init` primitives), `5a` (`expected_lib/` with 3-part bundled `Model` `.olean*`s and zero `Proof.*`/`Anneal.*`), `5b` `proof_full.ndjson`, and `5c` `CanonicalArena` + `nanoda_bin` (`unpermitted_axiom_hard_error: true`, `nat_extension: true`, `string_extension: true`) + `con-ron --verified`, plus `--paranoid-quorum` (`+ con-leche + lean4lean --import`, `< 3.0 s` on `scalar`). Tracks `leanchecker --from-export` in a non-gating canary because `Lean.Kernel.Environment.replay` (`Replay.lean:77,186`) fails on implicit `String.ofList` constants in `Captured.program` string literals and `lake comparator` disables `unpermitted_axiom_hard_error`.
3. **`real_crates/`:** Tests unmodified `zerocopy/src/` (`20` files, `33,939` LOC) + `zerocopy/proofs/` (`--env CARGO_PKG_VERSION=...`) under a 3-class non-backsliding `ratchet.json` (`sealing_stubs_captured: 327`, `safe_substantive_captured: 4`, `unsafe_items_captured: 1`, `end_to_end_verified_items: 5` so `2,203` trivial sealing stubs cannot hide substantive regressions), plus SHA-256-pinned external smoke fixtures including `anneal/tests/fixtures/starnix/` `ebpf_core` (`10` files, `12,309` LOC).

### 4. Four-Axis Regression Budgets, Axiom-Footprint Ratchet, and 4-Tier CI Rollout

Basis: source + execution (`74d509c852`, `#4139` `module` artifact measurements).

- **Four-Axis Budget Matrix (`anneal/ci/perf_and_hygiene_budgets.json`):**
  1. *Cold `lean -j1` (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`):* Warn `> 45,000 ms`, hard fail `> 75,000 ms` (leaving `>= 45s` below `installed_smoke`'s `120s` timeout; bans `set_option maxHeartbeats 0`).
  2. *Per-process peak `ru_maxrss`:* `<= 2,560 MiB` per `lean -j1` (`4 x 2.5 GiB = 10 GiB` on 16 GiB runners), `<= 1,024 MiB` for `SpecPreflight`/`leanexport`, `<= 512 MiB` for `nanoda_bin`/`con-ron`.
  3. *3-part `module` `.olean*` sizes:* Public `.olean <= 2.5 MiB`/module (catches accidental `@[expose]` proof leaks; today `94.8%` of `Anneal.MirWp.*` and `60%–71%` of `Anneal.PureLift.*` stay in `.olean.private`), `.olean.private <= 6.0 MiB`/module, total bundled public `.olean <= 20 MiB`.
  4. *End-to-end stage latency (`ANNEAL_PROFILE_JSON`):* `scalar <= 8.0s` (capture `<= 1.5s`, `5a+5b+5c+2-kernel <= 3.5s`), `zerocopy` `5` fns `<= 20.0s`, 4-kernel `--paranoid-quorum` `<= 4.5s`.
- **Two-Level Axiom Gate:** Level 1 enforces `{"propext", "Quot.sound", "Classical.choice"}` (banning `ofReduceBool`, `ofReduceNat`, `trustCompiler`, `reduceBool`, `reduceNat`, custom `axiom`s, `opaque`, `._unsafe_rec`). Level 2 (`theory/axiom-footprint.json`) pins per-module constructive subsets (`["propext"]` for `Anneal.{PureLift,CnfOrd,LinearArith,BitTrieLrat,PTree,SpineForce}.*` vs. explicit opt-in `["propext", "Quot.sound", "Classical.choice"]` for `Anneal.ClassicalEm`).
- **4-Tier CI & 5-Wave Sequencing:**
  - *Tiers:* Tier 0 static/boundary preflight (`< 90s`, `--network=none`); Tier 1 PR gate (`< 12 min` in `NestedBwrap` + `sandbox-aarch64`: workspace suites, `adversarial/`, `46`-guard Lean mutation `~35s`, `perf_and_hygiene`, `installed_smoke`, `zerocopy` ratchet); Tier 2 `merge_group` cold gate (`< 18 min`, gated by `ANNEAL_RELEASE_LOCK`: 100% cold Pass-1/Pass-2 `anneal-audit`, 4-kernel `--paranoid-quorum`); Tier 3 nightly (`< 45 min`: Rust TCB guard ablation, 4-way `differential/`, `v4.33.1`–`v4.35.0` Lean matrix).
  - *Waves 0–4:* Wave 0 drains `#4139`, `#4142`, `#4137`, `#4016`/`#4109`, `#4140`; Wave 1 lands `#4015` + 2-zone lattice (`+~15 LOC` in `cargo_boundary.rs`) + `anneal-testkit` (zero `AGENTS.md` size growth within `31,744 B`); Wave 2 decomposes monoliths (`0` `trusted/` edits); Wave 3 enables corpora + perf/axiom gates; Wave 4 performs targeted `cargo-llvm-cov` gap filling.
- **Eliminated Alternatives (`A1`–`A7`) & Open Maintainer Decisions (`D1`–`D4`):** Eliminated keeping tests in `trusted/*/tests/` (`A1`), naive `starts_with("trusted/")` blocking `tests -> testkit` (`A2`), relative `target/debug/cargo-anneal` paths bypassing feature flags (`A3`), `25` separate top-level `tests/*.rs` binaries (`A4`), raw `/tmp` store symlinks (`A5`), `trybuild` / expanding the `1,390`L `/// anneal:*` doc-comment synthesizer (`A6`), and `lake comparator` / `leanchecker --from-export` gating (`A7`). Open policy decisions: (`D1`) align `theory/Anneal.lean` and `share/anneal/theory` 1-for-1 with `bundle-manifest.json` and decouple `*Canaries.lean` (`~56 s` saved); (`D2`) convert `11` scalar + `31` capture cases to declarative corpora and delete the `1,390`L synthesizer; (`D3`) adopt `cargo-nextest` in CI while preserving `cargo test`; (`D4`) run path-filtered Rust TCB guard ablation on Tier 1 PRs (`0s` when `trusted/*.rs` untouched) and full matrix on Tier 2/3.

## Boundaries

- **not examined (live post-migration `nextest` timing across all `73` `Anneal` modules):** Initial numeric thresholds in §5.1 (`45s` / `75s` cold `lean -j1`, `2,560 MiB` RSS) are calibrated to 4-vCPU / 16 GiB `ubuntu-24.04` runners and require baseline tuning once Tier 1 `perf_and_hygiene` collects live measurements across all `73` modules.
- **known not to apply (`leanchecker --from-export` on Anneal `Captured.program` exports):** Probed and falsified on Lean `v4.35.0` (`Lean/Replay.lean:77,186` omits implicit `String.ofList` deps under `Name.quickCmp` ordering).
- **unsupported (macOS Mach-O split-store residency simulation):** `anneal-rustc-capture` limits typed MIR residency verification to Linux (`identity.rs:1497-1502`).

## Evidence

- **Inspected repository baseline:** `google/zerocopy@74d509c8529b05e0e4839cc739d6da2fe0841e41` (`anneal/trusted/{audit,cargo-anneal,rustc-capture}`, `anneal/theory/bundle-manifest.json`, `anneal/theory/Anneal.lean`, `zerocopy/src/`).
- **Live execution probes confirmed:** 12-case 2-zone `cargo_boundary` lattice, `0o555` `EACCES` vs. top-down `chmod` teardown, `cwd`/`DT_RUNPATH` sibling disjointness, unprivileged `bwrap --ro-bind <store> /nix/store` `symlinkJoin` resolution, and Lean `v4.34.1` / `v4.35.0` 3-part `.olean*` + 4-kernel NDJSON execution (`nanoda_bin`, `con-ron`, `con-leche`, `lean4lean --import`).

## Revalidation

1. Run `cargo test --workspace --locked` (and `cargo test -p cargo-anneal-tests --no-default-features --test cli`) plus `anneal-audit` `check_cargo_boundary` after landing Wave 1–2 to verify all `413+` migrated tests pass and zero files `> 1,000` lines remain in `anneal/tests/`.
2. Run `ci/check_guard_mutation.py` against `tests/corpora/adversarial/guards.toml` to confirm $K_{\text{entry}} = 100\%$ across Lean and Rust TCB guards.
3. Re-run `string_literal_replay_probe` whenever upgrading the pinned Lean toolchain beyond `v4.35.0` to check whether upstream `Lean.Kernel.Environment.replay` resolves `String.ofList` ordering.
