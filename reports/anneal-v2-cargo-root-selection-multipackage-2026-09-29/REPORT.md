# Anneal V2 Cargo root selection in a two-package workspace

## Summary

The checked-in Anneal V2 resolver returned two roots that Cargo did not select in this fixture: a package outside the virtual workspace's `default-members`, and a binary whose `required-features` was disabled. Its no-flag result matched its explicit `--workspace` result, while Cargo's no-flag check built only the default member. Its `--bins` result included the gated binary both with and without the feature, while Cargo checked that binary only with the feature enabled. These are selection differences in the current resolver, not observed extraction or verification failures.

The same execution also resolved both crate types of one library as separate Anneal roots, selected an integration-test target with `--tests`, and kept package identity in roots for two packages that each name a binary `always`. This is bounded evidence for #3731 I020's compilation-subject selection concern. It does not complete I020's downstream extraction, proof-context selection, or mismatch-reporting work.

## Applicability

The resolver bytes are an exact copy of `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988:anneal/src/resolve.rs`, SHA-256 `6b36c1c5647d4bff5955799c02c6c764ee1b7e29455fd55a8c5d01f0462d23b4`. The checked-in V2 CLI currently exposes setup, so `support/harness/` compiles that unmodified module with a small shim for Anneal's tool paths and lock type. The shim points the resolver at the pinned local Cargo and rustc binaries. It does not change package or target selection code. This exercises `resolve_roots`, `resolve_packages`, and `resolve_targets` as checked in, but not Anneal's full CLI, Charon, Aeneas, or Lean.

The fixture is a dependency-free Cargo workspace on macOS 26.6.2, arm64. Its virtual manifest has members `alpha` and `beta` but sets `default-members = ["alpha"]`. `alpha` has one library with `rlib` and `cdylib` crate types, an ordinary binary, a `gated` binary with `required-features = ["gated"]`, and an integration-test target. `beta` has a library and another binary named `always`. The fixture tree hash is in `REPORT.json`; every input file and both Cargo lockfiles are retained.

The harness was built with the pinned local `nightly-2026-05-31-aarch64-apple-darwin` toolchain, Cargo 1.98.0-nightly and rustc 1.98.0-nightly, using the project's local Cargo cache. All commands ran with `CARGO_NET_OFFLINE=true`; the harness build and Cargo controls used `--offline --locked`. The resolver's internal `cargo metadata` call has no explicit `--locked` flag, but the fixture lockfile was present. No dependency fetch or install occurred. Tool hashes and versions are retained in `support/environment.json`.

## Findings

### Virtual-root default selection expands past Cargo's default members

With no selector at the virtual workspace root, the resolver returned six roots: `alpha`'s `RLib`, `CDyLib`, `always`, and `gated`, plus `beta`'s `RLib` and `always`. Its explicit `--workspace` call returned the same six. Cargo metadata named only `alpha` in `workspace_default_members`; Cargo's no-flag `check` emitted artifacts only for `alpha`, while `cargo check --workspace` emitted artifacts for both packages. The resolver's virtual-root fallback uses `workspace_members`, not `workspace_default_members` (`resolve.rs`, `resolve_packages`).

Basis: **execution** in `support/raw/root_default.stdout`, `workspace.stdout`, `cargo_default.stdout`, `cargo_workspace.stdout`, and `cargo_metadata.stdout`; **source** in the retained resolver.

### Required features do not gate a returned binary root

Cargo metadata lists target `gated` with `required-features = ["gated"]`. The resolver returned both `always` and `gated` for `-p alpha --bins` with the feature disabled, and returned the same two roots with `--features gated`. Cargo's `check -p alpha --bins` emitted no `gated` artifact without the feature; adding `--features gated` emitted it. The resolver filters target kinds and names but does not inspect `required_features` (`resolve.rs`, `resolve_targets`). Its forwarded feature flags affect Cargo metadata resolution but do not change this target filter.

Basis: **execution** in `support/raw/alpha_bins.stdout`, `alpha_bins_feature.stdout`, `cargo_alpha_bins.stdout`, `cargo_alpha_bins_feature.stdout`, and `cargo_metadata.stdout`; **source** in the retained resolver.

### Target-kind expansion and direct selectors worked in this fixture

`-p alpha --lib` returned separate `RLib` and `CDyLib` roots for its one library target. `-p alpha --tests` returned its explicit `alpha_integration` test root. Running with the current directory inside `alpha` selected `alpha`, and `-p beta` selected `beta`. The two `always` binaries remained distinguishable in the resolver output by package name and manifest path. The experiment did not generate LLBC paths or check output collision behavior.

Basis: **execution** in the corresponding `support/raw/*.stdout` files; **source** in `resolve.rs` target flattening and package selection.

## Boundaries

- The fixture has two packages and no external dependencies, build scripts, proc macros, target triples, or profile variations. It does not establish the resolver's behavior for every Cargo workspace shape.
- Cargo `check` artifact messages show which units Cargo selected in these controls. They do not establish what Charon would extract or how Anneal would associate a proof with one unit.
- The harness replaces only tool-path and lock plumbing around the exact resolver source. A full V2 CLI path could add policy before or after this module.
- `RLib` and `CDyLib` were distinct returned roots; no Charon invocation, LLBC file, generated model, or verification result was produced for either.
- #3731 I020 also asks how an interactive proof query chooses a subject, how mismatches surface, and whether annotation identity can remain separate from subject-specific proof context. None of those behaviors was exercised here. This report is not completion evidence for I020 or for the broader #3731 agenda.

## Evidence

- `support/harness/src/resolve.rs` — exact retained bytes of `anneal/src/resolve.rs` at the main revision above. Relevant source regions: `resolve_roots` (lines 210–268), `resolve_packages` (301–380), `resolve_targets` (393–436).
- `support/harness/` — minimal executable wrapper and offline-generated `Cargo.lock`; its `setup` and `util` stubs provide local tool paths and a lock type, while root selection runs the checked-in source.
- `support/fixture/` — two-package source, virtual manifest, and offline-generated lockfile.
- `support/run.py`, `support/commands.json`, `support/build-commands.json`, and `support/raw/` — replay procedure, argument/cwd/exit records, and full stdout/stderr for the offline harness lock/build, eight resolver calls, Cargo metadata, and five Cargo check controls. Local absolute prefixes were replaced with `$PROBE_ROOT`, `$CARGO_TARGET_DIR`, `$CARGO_HOME`, and `$RUSTUP_HOME`; the JSON and target identities remain parseable.
- `support/environment.json` — source revision, toolchain identity, host, command environment, and hashes.
- `support/check.py` and `support/artifacts.sha256.json` — offline, read-only checks of retained inputs, command outcomes, metadata, root sets, and Cargo artifact controls.

The retained harness build output is a successful warm offline replay after the first compilation; the initial build also succeeded, but its compiler progress text was not saved. The harness lockfile hash was unchanged by that replay. This execution was on 2026-09-29. The relevant issue wording is #3731 I020, “One source file, several compilation subjects.” The probe covers resolver enumeration and selection only.

## Revalidation

Run `python3 support/check.py` from this package root to validate the retained evidence without launching Cargo. To repeat the execution, copy `support/` to a disposable directory, set `CARGO_HOME` to a cache containing the harness's locked crates, `RUSTUP_HOME` and `RUSTUP_TOOLCHAIN` to the intended local toolchain, and `CARGO_TARGET_DIR` outside the source tree. Build `harness/` with `cargo build --offline --locked`; set `PROBE_BINARY` to that binary and `PROBE_CARGO`, `PROBE_RUSTC`, and `PROBE_RUST_LIB` to the selected toolchain's paths, then run `python3 run.py` from the copied support directory. It rewrites `commands.json` and `raw/` in that copy. Compare the parsed root sets and compiler-artifact target sets, preserving the `default-members` and `required-features` controls. Re-run with real extraction and proof-context selection before drawing an end-to-end I020 conclusion.
