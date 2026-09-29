# Anneal V2 LLBC slug collision across feature-selected compilation subjects

## Summary

The checked-in Anneal V2 `AnnealArtifact::artifact_slug()` returns the **same** LLBC filename for two library compilations of one unchanged source path even though cached Charon produced different model bodies under default and `selected` features. The default model returns `7`; the selected-feature model returns `11`. The result is a concrete locator collision for a pair of distinct compilation subjects, not a witnessed Anneal overwrite: the current V2 CLI does not call this helper or invoke Charon for verification.

## Applicability

The examined helper is the exact `anneal/src/scanner.rs` bytes at `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988` (SHA-256 `6a347ef9b6b0afd624ace8794eec19fa2af9c5c6ceecd533b12bf52992f20567`). The local harness compiles that copied file unchanged with minimal stubs for its `resolve` types; the relevant `AnnealTargetKind::RLib` discriminant matches the checked-in enum's value `1`. The V2 crate itself could not be built offline in the earlier source audit because its pinned Charon git dependency was unavailable in the local Cargo cache. This harness uses only cached `sha2` and does not claim to exercise the V2 CLI.

The fixture is a dependency-free library with one `src/lib.rs` and one `Cargo.toml`. Both Charon commands use the same manifest, target kind (`--lib`), source bytes, Cargo lockfile, host triple, and cached toolchain. The compilation selector differs only by `--features selected`; the commands use separate output paths and temporary Cargo target directories to retain both results. Charon `0.1.210` at executable SHA-256 `51bb6d23...` and nightly-2026-05-31 Cargo/rustc were already cached on macOS arm64. All execution happened in the conversation-specific Meta data directory; no dependency was fetched or installed.

## Findings

### Same slug, different translated body

The harness constructs the `AnnealArtifact` fields that `resolve.rs` would provide: package `unit_key_probe`, target `unit_key_probe`, kind `RLib`, and the fixture's absolute manifest path. It calls the unchanged scanner helper for the two feature selections. Both rows in [`support/raw/slug.stdout`](support/raw/slug.stdout) report `UnitKeyProbeUnitKeyProbe2ddd03393e67b637.llbc`. The hexadecimal suffix depends on the absolute fixture path and will change if the package is copied elsewhere; equality between the two rows is the invariant.

The two exact offline Charon commands in [`support/results.json`](support/results.json) emitted separate retained LLBC files. Both report `has_errors: false`, one local function named `unit_key_probe::model_value`, and the **same file-table source contents**. Their function bodies contain distinct serialized `U32` scalar literals: default `7`, selected `11`. The respective LLBC SHA-256 values are `a7866222ec870d56a3a252bbd8e4e922f3029429691d5ccff7f62acf97ab619f` and `f28f4e3815f4e67f010ef4d7fcabb80e23eb8de0c87f121bec1e06d0f43f2e22`. The literal/body projection is the material model difference; the raw hash inequality alone would not establish it.

`scanner.rs` hashes only manifest path, target name, and target kind for the slug. Its input structure contains no feature set, target triple, profile, Cargo configuration, build outputs, or compiler flags. Thus the observed feature collision follows directly from the helper's inputs. The other omitted dimensions are source-level residuals here; this experiment did not vary them. A shared slug cannot identify which of these two Charon-produced models a later proof query means. It also cannot itself reject a proof/model mismatch. The current helper is an output locator, not a complete compilation-unit key or acceptance token.

### Exact issue-item mapping

| Public agenda item | Evidence added | Remaining work |
| --- | --- | --- |
| [#3731 I020](https://github.com/google/zerocopy/issues/3731) — one source file, several compilation subjects | Executed same-path, same-target feature contrast; checked-in helper gives one LLBC filename to two different Charon models. | Select and label a complete compilation subject in an actual Anneal request; expose ambiguity/mismatch to a proof query; test stable annotation identity separately from proof context. |
| #3731 I076 and [#3730 D07](https://github.com/google/zerocopy/issues/3730) — compilation-subject invalidation matrix | The feature dimension concretely aliases at the current V2 LLBC locator. | Implement and test a complete unit key, invalidation, and collision-safe per-unit destination across target kind, triple, profile, features, host role, cfg/build output, and tool settings. |

This adds one distinct V2 source-specific finding to the prior `anneal-v2-cargo-root-selection-multipackage-2026-09-29` resolver experiment. That report showed selected-root differences for `default-members` and `required-features`; this one tests the scanner's actual filename helper against two different extracted models. The older `anneal-3730-charon-subject-identity-2026-09-29` package already established several different Charon subjects at one source path; this report supplies the missing checked-in V2 locator comparison.

## Boundaries

- The two Charon invocations were explicit harness commands, not commands selected or launched by Anneal. No V2 runtime extraction, file overwrite, Aeneas model, Lean proof, annotation attachment, or proof acceptance was observed.
- The harness uses minimal type stubs around the exact scanner source because the V2 crate's pinned git dependency was not cached. The stub does not reproduce Cargo target selection, locking, or stage orchestration.
- The fixture varies only one feature on one host and one target kind. It establishes a **feature alias** in the current slug; it does not empirically test triples, profiles, `RUSTFLAGS`, build scripts, or target-kind collisions.
- The slug's 64-bit hash truncation also admits theoretical hash collisions among different field tuples, but no such collision was sought or observed here. The demonstrated collision is deterministic because the helper receives identical fields for two different compilations.

## Evidence

- [`support/harness/src/scanner.rs`](support/harness/src/scanner.rs) is byte-for-byte copied from checked-in V2 source. [`support/harness/src/main.rs`](support/harness/src/main.rs) supplies only the required types and calls `artifact_slug()`/`llbc_file_name()`.
- [`support/fixture/`](support/fixture/) retains the source, manifest, and lockfile. [`support/artifacts/`](support/artifacts/) retains both raw LLBC files. [`support/raw/`](support/raw/) retains every command's stdout/stderr, including build and Charon logs.
- [`support/results.json`](support/results.json) records exact argv, directories, exit codes, tool hashes, source hashes, slug rows, LLBC hashes, and parsed body literals. [`support/artifacts.sha256.json`](support/artifacts.sha256.json) binds the retained evidence files; [`support/check.py`](support/check.py) checks them without external tools.
- The public #3731 I020 wording was read on 2026-09-29. The preserved v23 crosswalk maps #3730 D07 to I009/I020/I076; this report claims only the I020/I076 feature-locator slice.

## Revalidation

Run `python3 support/check.py` from this package to verify retained evidence without Cargo or Charon. To replay with cached tools, copy the package to a writable directory, set `PROBE_TOOLS` or the individual tool path environment variables in [`support/run.py`](support/run.py), then run `python3 support/run.py` and `python3 support/check.py`. Replay refreshes `results.json` and `artifacts.sha256.json`. It uses `cargo generate-lockfile --offline`, `cargo build --offline --locked`, and `charon cargo ... --offline --locked`, with temporary target directories deleted afterward. The absolute fixture path changes the slug suffix on relocation; compare equality across the two rows and the distinct `7`/`11` translated bodies. To close I020 in Anneal, connect selection to a Charon invocation and carry a complete compilation-unit identity through LLBC, generated model, proof query, and rejection of wrong-subject results.
