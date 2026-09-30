# Anneal V2 LLBC slug collision across profile and cfg subjects

## Summary

One dependency-free Rust library at one unchanged source path produced different Charon function bodies under debug, release, and a separate debug `--cfg probe_alt` compilation. The checked-in Anneal V2 `AnnealArtifact::artifact_slug()` helper assigned all three the same `.llbc` filename because its fields were identical: package, target name, `RLib` kind, and manifest path. The debug/release `profile_value` literals were 7/11; the debug/cfg `config_value` literals were 23/29. This extends the earlier feature-only locator collision to two additional compilation inputs for #3731 I020/I076 and #3730 D07. It is a locator contrast from a copied source helper and explicit Charon commands, not an observed Anneal overwrite or proof mismatch.

## Applicability and procedure

The harness contains a byte-for-byte copy of `anneal/src/scanner.rs` from `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`, SHA-256 `6a347ef9b6b0afd624ace8794eec19fa2af9c5c6ceecd533b12bf52992f20567`. Its minimal `resolve` stubs use package and target name `unit_key_probe`, `AnnealTargetKind::RLib` discriminant 1, and the single fixture manifest path. The same scanner copy and stub approach were established by [the feature-slug report](../anneal-v2-feature-subject-slug-collision-2026-09-29/REPORT.md). The V2 CLI did not invoke this helper or Charon in this experiment.

The fixture source SHA-256 `990beab58abb9a04f48c119fdcea2918865232730e278de3def35e15831b123d` was unchanged for all three Charon requests. It has two public functions with exclusive `#[cfg(debug_assertions)]` and `#[cfg(probe_alt)]` branches. The debug baseline used neither `--release` nor custom `RUSTFLAGS`; release added only `--release`; the separate cfg case kept the debug profile and set `RUSTFLAGS=--cfg probe_alt`. Explicit `CARGO_PROFILE_DEV_DEBUG_ASSERTIONS=true` and `CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS=false` kept those branches defined. Every Charon request selected `--lib`, used `--offline --locked -v`, one Cargo job, `CARGO_INCREMENTAL=0`, one Rayon thread, a private target and a distinct retained destination. The local pinned Charon, Cargo and rustc SHA-256 values are in `REPORT.json` and `support/results.json`; there was no download or installation.

The harness Cargo build, slug call and three Charon requests ran sequentially. Before each call and during it, the probe estimated reclaimable memory from `vm_stat` free + inactive + speculative pages and required at least 20% of 8 GiB physical memory. It also required 10 GiB free disk, capped sampled process-group RSS at 1 GiB, and capped each command at 60 seconds. The execution used an owned work tree under `/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/i076-profile-cfg-slug/work/`, then removed it. The exact command arrays, selected environment, resource samples and full short stdout/stderr are retained.

## Findings

| Charon subject | Selected `profile_value` U32 literal | Selected `config_value` U32 literal | LLBC SHA-256 prefix | Checked-in helper filename |
| --- | ---: | ---: | --- | --- |
| Debug | 7 | 23 | `51a0aafb437b` | `UnitKeyProbeUnitKeyProbe420dc0784be82942.llbc` |
| Release | 11 | 23 | `375cb601ffbe` | Same |
| Debug + `--cfg probe_alt` | 7 | 29 | `f9375847bc60` | Same |

All three Charon calls exited 0, emitted parseable `unit_key_probe` LLBC with `has_errors: false`, and embedded the same source-file contents hash. The verbose stderr shows one `charon-driver rustc --crate-name unit_key_probe` invocation per case. Release's driver line contains `-C opt-level=3`; the cfg case's line contains `--cfg probe_alt`. The selected local body hashes change only for `profile_value` in the release contrast and only for `config_value` in the cfg contrast. The `U32` literal changes give a concrete model difference, beyond raw file-hash inequality. **Basis: execution.**

`support/llbc-diffs.json` retains every changed parsed-JSON leaf: 25 for debug versus release and 19 for debug versus cfg. The differences include the selected scalar, source spans/source text for selected branches, serialized short-name order, and the requested destination path. Therefore the table asserts the selected body/literal contrasts and source equality, not that each whole LLBC differs only in one scalar. The helper's equal filename follows from identical fields passed to the exact copied source; profile and `RUSTFLAGS` are absent from those fields. **Basis: execution plus source-level derivation.**

The harness-build preflight observed 22.828% estimated reclaimable memory and 44.26 GB free disk. The minimum sampled values across all five local commands were 22.324% and 44.24 GB; the largest sampled process-group RSS sum was 178,336 KiB, during the harness build (the Charon maximum was 117,104 KiB). No guard or timeout fired. The work tree was absent after cleanup. These sampled host measurements can miss peaks and are not throughput or production resource estimates. **Basis: execution.**

## Exact issue alignment and limits

| Item | New bounded evidence | Remaining scope |
| --- | --- | --- |
| #3731 I020 | One source file and library target produced three profile/cfg-specific Charon models under one V2 slug. | The checked-in root selector and slug are not connected to an Anneal Charon request or interactive proof-context selector; visible mismatch and cross-stage proof rejection remain untested. |
| #3731 I076 | Profile and cfg now have direct model-difference/locator-alias witnesses, supplementing the earlier feature collision and sibling-name observations. | A complete compilation-unit key, host/target/tool/build-output dimensions, output ownership, concurrent arbitration and collision-rejecting Anneal publication remain untested. |
| #3730 D07 | Two previously source-only omitted dimensions were exercised with the selected Charon pin. | Full subject invalidation and concurrent producer/consumer controls require an implemented Anneal owner. |

The prior [subject/output phase matrix](../anneal-3730-charon-subject-output-phase-matrix-2026-09-29/REPORT.md) varied `RUSTFLAGS=-C opt-level=1` but its selected local body projection did not change; it also found multi-unit destination collisions. This package deliberately selects cfg branches so profile and custom cfg produce different modeled literals while holding the source bytes and helper fields fixed. All three requests used separate target directories and destinations, so this report does not claim an actual filename overwrite. It does not run Aeneas, Lean, an annotation parser, proof queries, or the V2 CLI. The copied `scanner.rs` is exact, but the surrounding stub does not reproduce runtime target selection or publication. The equality of its 64-bit slug here is deterministic input aliasing, not a hash collision between different helper inputs. The three cell timings are not a performance comparison.

## Evidence and revalidation

- `support/probe.py` (SHA-256 `d3f5c0efcf646c2c288a3b2ed5d3b5540cfbafd51357d8804fc04375f3a0a99a`) is the executed, guarded script. `support/harness/` preserves the scanner copy, stubs and locked manifest; `support/fixture/` preserves the exact one-path Rust source and lockfile.
- `support/results.json` (SHA-256 `ed27ba3bf4b30791bb162acdf0732d195ec7a4f5105e087249ef6f36c779eadb`) retains source/tool/harness-binary hashes, slug rows, all commands, selected environment, guard samples, output projections and cleanup. `support/command-hashes.json` hashes each recorded argv/cwd/selected-environment tuple. `support/raw/` retains each command's complete stdout/stderr, including the exact driver lines; `support/artifacts/` retains all three raw LLBCs. `support/llbc-diffs.json` is the exact parsed-JSON leaf diff for debug/release and debug/cfg.
- `support/check.py` verifies the retained evidence without launching Cargo or Charon. From the package root, run `python3 -B support/check.py`. For replay, copy the package to a disposable path with the pinned local tools, set `I076_PROFILE_WORK_ROOT` to a fresh owned path, and run `python3 -B support/probe.py` there. The replay overwrites that copy's results/raw outputs/LLBCs and may yield different raw hashes, short-name order, paths and resource samples; compare the same-source/same-slug and selected-literal relationships first.
