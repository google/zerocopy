# Charon and Aeneas generation boundaries under A→B→A and failure

## Summary

At the installed June 3 Charon/Aeneas pair, a small source A→comment-only C→body-changed B→A sequence produced the expected changed and restored generated Lean source. Three A extractions did not always have identical raw LLBC bytes: the observed differences were ordering of entries in serialized keyed `short_names`; sorting only keyed `short_names` and `item_names` maps made the A LLBC values equal, and their three-file Lean inventories were byte-identical. Comment-only C changed source provenance in LLBC while leaving generated Lean bytes identical; B changed `Funs.lean`.

The failure controls show a sharper publication rule. Charon exited 2 on malformed Rust while the old successful `.llbc` stayed at the destination path. Aeneas exited 1 on an unsupported raw-pointer operation but wrote three Lean files, including a partial `Funs.lean` with `sorry`. A path's existence or a generated-file inventory is therefore insufficient evidence that the *latest* request succeeded. The adapter must bind outputs to the request's exit/error status, input identity, and complete-generation publication decision.

## Applicability

The executed binaries were Charon 0.1.210 SHA-256 `51bb6d23...`, Aeneas June 3 SHA-256 `f476001e...`, and rustc nightly-2026-05-31 at `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, on macOS 26.6.2 arm64. Local source checkouts used for context are `AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` and `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`; the executable hashes identify what actually ran. `aeneas -version` returned `unknown`, so it does not independently attest the source revision.

Each Charon invocation was a fresh process using `charon rustc --preset aeneas --dest-file <same current.llbc> -- <same source.rs> --crate-type lib --crate-name snapshot_probe --edition 2021`, with `CHARON_TOOLCHAIN_IS_IN_PATH=1` and the selected Rust nightly first in `PATH`. Each successful LLBC was copied before the next request. Aeneas was also a fresh process per input, invoked with `-backend lean -split-files -gen-lib-entry -sequential -no-progress-bar` into a new, empty output directory. The fixture is a dependency-free library with two safe functions; C changes only a doc marker, B changes that marker and `wrapping_add(1)` to `wrapping_add(2)`. The negative cases are malformed Rust and a raw-pointer dereference.

This report adds changed-input/failure and coarse handoff-manifest evidence to existing same-input and same-release reports. It partially informs [#3731](https://github.com/google/zerocopy/issues/3731) I078/I079/I082/I084/I085/I087/I088 and extensions I148/I149/I156. It does not execute the much broader I073–I077/I080/I081/I083/I086 or I158 matrices.

## Findings

### Raw LLBC ordering varies while this Aeneas output stays byte-identical

In the retained run, A1/A2/A3 raw `.llbc` SHA-256 values were `0784839f...`, `5389fa29...`, and `0784839f...`. A structural JSON comparison found the A1/A2 difference only under `translated.short_names` keyed-entry order; the A1/A3 raw files matched in this particular replay. The harness verifies unique keys and sorts the entries of *only* `short_names` and `item_names` plus ordinary JSON object keys. The resulting A canonical LLBC SHA-256 was `5eaaaea233c5...` in all three runs. It does not sort `ordered_decls`, function bodies, statements, branches, or source files.

All three A Aeneas runs emitted the same three files: `Funs.lean` SHA-256 `f7f03a06...`, `Types.lean` `a06e07ba...`, and `Snapshot.lean` `f655d06e...`. This is a bounded fresh-process, sequential-flag byte comparison; it does not prove Charon or Aeneas determinism for other inputs, schedules, configurations, or semantic equivalence. The selected Aeneas source report says the importer discards Charon `short_names` before translation, which is consistent with the observed output equality; this run itself does not isolate all internal reasons.

Basis: **execution**, `support/raw-results.json` `runs`/`comparisons`, retained raw LLBC and Lean files under `support/artifacts/A1`, `A2`, `A3`; **source** context from `aeneas-generated-source-determinism-nightly-2026-06-03`.

### Content identity and provenance identity can diverge

Changing only the doc marker from A to C changed the source SHA-256 and canonical LLBC digest; Charon's local `step` declaration retained the changed doc attribute and file content hash. The C generated Lean inventory was byte-identical to A. Changing the function body in B changed `Funs.lean` to SHA-256 `f0f5ca27...` while `Types.lean` and `Snapshot.lean` stayed byte-identical in this fixture. Restoring A restored the A Lean inventory and canonical LLBC value.

This separates three observable identities: raw serialized LLBC bytes, structured LLBC after one justified keyed-map ordering normalization, and generated Lean bytes. A byte-identical Lean model in C does not make C's source provenance current for navigation or diagnostics. Conversely, this fixture does not prove the C and A Rust programs semantically equivalent merely because their generated Lean text matches; no theorem or Rust/Lean correspondence was checked. A cross-layer result should retain exact source provenance independently of model-content reuse.

Basis: **execution**, `support/fixture/source-{A,B,C-comment-only}.rs`, `support/raw-results.json` comparisons, and retained outputs; freshness implication is **derived**. This partially informs I079/I082/I087/I148.

### Stage success is a property of the request, not of an output pathname

After successful A3 extraction, the script replaced the same `source.rs` with malformed `pub fn broken(` and called Charon with the same `--dest-file`. Charon exited 2, reported an unclosed delimiter, and left `current.llbc` byte-identical to A3's successful output. A consumer checking only that the path exists, parses, and has `has_errors: false` would misattribute old A3 to the failed request. The negative control directly falsifies that path/existence rule for this invocation. An adapter can stage into a request-unique destination and publish only after checking process status and the new artifact's identity/completeness.

For the raw-pointer source, Charon exited 0 and produced an LLBC containing local `snapshot_probe::read_raw` with a source span. Aeneas then reported that it does not yet support dereferencing raw pointers, exited 1, and nevertheless generated `Types.lean`, `Funs.lean`, and `Snapshot.lean`. `Funs.lean` contains a `def read_raw ... := do` body with `sorry`; stdout explicitly calls the files partial. Accepting a generated-file inventory or Lean parse alone would be unsafe for this case. This report does not test whether Lean typechecks the partial files or whether any subsequent theorem could be accepted; the stage failure and `sorry` are already sufficient to reject this generation as verified output.

Basis: **execution**, `support/raw-results.json` `invalid-rust`/`unsupported-rust` run records and preserved `support/artifacts/unsupported-rust/lean/Funs.lean`. The publication requirement is **derived** from these two observed failure modes. This partially informs I078/I085/I088/I156.

### A coarse cross-layer manifest is recoverable; edit provenance is not

`support/handoff-manifest.json` records each run's source/LLBC digests, generated-file inventory and imports, local Charon declaration IDs and spans, and candidate Lean declarations. The baseline LLBC had local `snapshot_probe::step` at lines 4:0–6:1 and `snapshot_probe::select` at 8:0–10:1. Split `Funs.lean` contains `def step` and `def select` with Aeneas source comments referring to those Rust items/spans. The raw-pointer failure similarly retains `read_raw` origin while the emitted body is partial. The handoff's item-to-Lean relation is explicitly a printed-name/source-comment match, not a compiler-verified bijection or an editable proof-range map.

This establishes what the selected tool outputs made directly inspectable for this tiny fixture. It leaves unresolved how to relate one Rust item to multiple generated helpers, missing/deleted declarations, external models, annotation obligations, or exact authored proof bytes. No newer `translation.json` capability is assumed at the selected Aeneas pin.

Basis: **execution** plus a **derived** lexical inventory in `support/handoff-manifest.json`; raw evidence is the retained LLBC/Lean files. This partially informs I087/I149.

## Boundaries

- All tool invocations were separate processes and sequential. Same-process Charon driver reuse, Aeneas library calls, parallel Aeneas mode, concurrent generation, cancellation, worker cleanup, and process-global residual state were not tested. Existing reports cover source-level process boundaries and a separate same-input Aeneas concurrency cell.
- The source path, destination path, crate name, host target, preset, and Aeneas flags were fixed within the run. There was no Cargo subject, shadow workspace, path dependency, build script, proc macro, external model, different target, or toolchain-upgrade matrix.
- The normalization is deliberately limited to two keyed name-map arrays and JSON object order. It is an equality aid for this schema and input, not a validated semantic hash or permission to erase provenance. A new schema must be reviewed before reusing it.
- The A/C Lean equality does not establish Rust semantic equivalence; the B Lean difference does not quantify downstream Lake rebuild cost. Generated Lean was not compiled or used in a proof.
- The error probes do not establish atomic publication behavior under interruption, disk-full, kill signals, crashes during a write, or shared destinations. They show stale prior LLBC and partial Lean under completed error paths.
- The handoff manifest supplies coarse declaration/source anchors only. It has no exact projected proof edit ranges, one-to-many obligation accounting, or independently checked origin relation.

## Evidence

- `support/probe.py`: complete replay harness, SHA-256 `ca098f663933e0d0993f9a0691ab50a24bec6d31f100e59d6ed3dabc94af82df`; it uses a fixed disposable source path to preserve source-path identity across runs and retains copies before the next invocation.
- `support/fixture/`: A, C-comment-only, B, malformed, and unsupported Rust inputs.
- `support/artifacts/`: every successful raw `.llbc` and emitted `.lean` file, including partial output from the failed Aeneas run. `support/raw-results.json`: exact command/flags, tool/binary hashes, source/LLBC/canonical/Lean hashes, statuses, stdout/stderr, source spans, declarations, inventories, and structural raw-difference paths. `support/handoff-manifest.json`: compact candidate cross-layer inventory.
- `support/host.txt`: Python, macOS, rustc revision, Charon/Aeneas versions, binary/harness hashes, and parent reference checkout `37a0ecd080d333f93bfe900d9c7dab193608e478`. `support/command.stdout`: final run summary. The local source checkouts were inspected at `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` (Charon) and `ac9f1bc5262a5e4ff1e24ca78617121382202727` (Aeneas).
- Relevant prior reports: `charon-llbc-output-goldens-and-revision-diffs-2026-09-27` documents an earlier keyed `item_names` order difference; `aeneas-concurrent-generation-determinism-nightly-2026-06-03` tests fixed-input concurrent Aeneas processes; `aeneas-incremental-translation-feasibility-nightly-2026-06-03` and `aeneas-library-process-architecture-nightly-2026-06-03` inspect process/library boundaries. This package does not revalidate their broader claims.

Reproduce from this package directory with `python3 support/probe.py` using the installed paths at the top of that script. It replaces only its own `support/artifacts/`, `support/work/`, `support/raw-results.json`, and `support/handoff-manifest.json`. Compare the assertions and manifest first; raw LLBC SHA values can vary with keyed name-map order across replays, as observed.

## Revalidation

At a new compatible tool pair, replay A1/A2/C/B/A3 and both error cases with exact executable/configuration identities. Compare raw LLBC, review schema-aware keyed maps, local declarations/spans and file contents, and then compare generated file inventory/bytes separately. Keep the failed Charon destination populated from a prior success and require the new request's failure to invalidate it; require Aeneas nonzero/partial output to be rejected even if files exist. To assess persistent-process reuse or fine-grained invalidation, build a separate library/daemon adapter and compare its A/B/A results with fresh-process oracles after errors and cancellation.
