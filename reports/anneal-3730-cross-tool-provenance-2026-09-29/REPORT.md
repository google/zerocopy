# First failing stage and provenance across rustc, Charon, Aeneas, and Lean

## Summary

On five tiny, pinned Rust inputs and one authored Lean proof, the first failing stage could be identified from stage-local process results: invalid Rust failed rustc; rustc-valid `async fn` reached a Charon unsupported-coroutine panic under strict error policy; valid raw-pointer Rust reached Aeneas, which exited 1 while emitting partial Lean containing `sorry`; a supported A model compiled in Lean before a separate proof failed in Lean batch and server modes. A fresh source revision deleting `select` removed its LLBC item and generated Lean definition.

The pipeline preserves several useful but different provenance forms: rustc JSON byte offsets and source spans; Charon LLBC file contents, item IDs, and item spans; Aeneas text errors and generated source comments; Lean batch JSON and LSP ranges. The specimen manifest labels Rust-item→Lean declaration edges as **lexical candidates**, because the observed outputs did not supply a compiler-authenticated item-to-declaration map. One Unicode line distinguishes Lean batch scalar columns from LSP UTF-16 character positions in this fixture.

## Applicability

The executed tools were local macOS arm64 binaries with SHA-256 values recorded in `REPORT.json` and `support/raw-results.json`: rustc nightly commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, Charon executable `51bb6d23...`, Aeneas executable `f476001e...`, and Lean `v4.30.0-rc2` commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. Charon `--version` was rejected by this binary and Aeneas `-version` printed `unknown`; the binary hashes are their tested identities. Local Charon and Aeneas source checkouts at `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` and `ac9f1bc5262a5e4ff1e24ca78617121382202727` supplied context, but were not assumed to be independently attested by the executables.

Each Rust input was checked directly with `rustc --error-format=json --emit metadata`, then passed to `charon rustc --preset aeneas --abort-on-error --dest-file <private path> -- <source> --crate-type lib --crate-name snapshot_probe --edition 2021`. Successful LLBC was passed to `aeneas -backend lean -no-progress-bar -sequential -split-files -gen-lib-entry -dest <private directory> <llbc>`. The supported A output's `Types.lean` and `Funs.lean` were compiled in a private `Snapshot/` module tree against the existing prebuilt Aeneas Lean library; the authored `Proof.lean` was then checked by `lean --json` and `lean --server`. Exact command arrays, environment paths, outputs, and hashes are retained.

This is a connected, executable specimen for [google/zerocopy#3731](https://github.com/google/zerocopy/issues/3731) I019/I027/I031/I055/I087/I149. Existing reference reports survey broader diagnostic categories, path policies, and Lean protocol behavior; this package contributes a joined first-failure and deletion trace through the selected tools. It does not execute Anneal V2, whose current pipeline remains a separate implementation question.

## Findings

### Stage identity prevents a downstream error from hiding its cause

| Case | rustc | Charon | Aeneas | First failing stage |
| --- | ---: | ---: | ---: | --- |
| Supported A | 0 | 0 | 0 | None; generated Lean modules compiled |
| A with `select` deleted | 0 | 0 | 0 | None |
| Wrong Rust return type after `🧪` | 1 | 2 | Not run | rustc |
| `async fn` coroutine | 0 | 101 | Not run | Charon |
| Raw-pointer dereference | 0 | 0 | 1 | Aeneas |
| Bad proof using supported A | Prior A succeeded | Prior A succeeded | Prior A succeeded | Lean (`--json` exit 1; server diagnostic) |

The rustc-error case returned structured JSON `mismatched types`, with primary source span line 2 column 44 and absolute byte span 67–73. Charon's wrapper then exited 2 without producing LLBC. The coroutine compiled under direct rustc, but Charon printed “Coroutine types are not supported yet” with the `async fn` source range and exited 101 after `--abort-on-error` converted the registered translation error into a panic. This 101 observation is tied to **that strict flag and input**; it is neither a rustc rejection nor a generic classification of all Charon panics.

For the raw pointer, Charon produced `has_errors: false` LLBC with `snapshot_probe::read_raw` and a serialized span at source lines 3–6. Aeneas then reported its unsupported dereference at `source-unsupported.rs`, lines 5:4–5:8, exited 1, and still generated `Types.lean`, `Funs.lean`, and `Unsupported.lean`; `Funs.lean` contains `sorry`. The stage failed regardless of the existence or parseability of generated files. The exact Aeneas output uses its own displayed range syntax; this run does not establish that syntax's coordinate-unit contract.

For the Lean error, both A generated modules compiled first. The authored proof with `/- 🧪 -/ rfl` on its fourth line then failed: batch JSON reported `Tactic rfl failed` at line 4, columns 10–13 and exit 1. A version-1 server `publishDiagnostics` reported the same message at zero-based line 3, UTF-16 characters 11–14; `waitForDiagnostics` returned for the requested version 1. The prefix before `rfl` is 10 Unicode scalars, 11 UTF-16 code units, and 13 UTF-8 bytes. These exact positions demonstrate a required coordinate conversion for this specimen. The server also emitted empty intermediate diagnostic notifications; consumers must await the settled version rather than treat the first empty notification as success.

Basis: **execution**. `support/raw-results.json` contains every status and raw stream; `support/mapping-manifest.json` retains extracted diagnostics, first-failure labels, and the unit checks. The proof and generated artifacts are preserved under `support/artifacts/`.

### Serialized source anchors survive, while source-to-Lean edges remain lexical

The A LLBC serialized the original source bytes (hashed in the manifest's file table), `snapshot_probe::step` with `def_id: 0` and source lines 4–6, and `snapshot_probe::select` with `def_id: 1` and source lines 8–10. Its generated `Funs.lean` contains `def step` on line 21 and `def select` on line 27, each preceded by an Aeneas comment naming the Rust item and source span. Those name/comment matches allow a candidate mapping. They do **not** authenticate an exact one-to-one source-to-generated-declaration edge, an editable proof range, or whether helper declarations and transformations share an origin. The manifest's `candidate_edges` records that evidence level per entry.

The fresh deleted-source run had no `snapshot_probe::select` local LLBC function and no `def select` in its generated `Funs.lean`; its `Funs.lean` hash changed from `807263e4...` to `fcff9343...`. This is a deletion/provenance control for a fresh destination. It does not establish how an incremental Anneal cache removes stale declarations after an edit or how proofs attached to the deleted item are handled.

Basis: **execution** for serialized LLBC and generated files; **derived lexical matching** for Rust-to-Lean candidate edges. See `support/mapping-manifest.json` `A_to_deleted` and `candidate_edges` and preserved raw `.llbc`/`.lean` files.

## Boundaries

- Five Rust files and one Lean proof do not cover macro expansion, multiple source files, path remapping, generated helpers, trait specialization, cross-crate definitions, Unicode in Charon/Aeneas source locations, or all diagnostic severities. The coordinate assertions are observed for the exact Unicode lines retained here, not a complete protocol proof.
- The coroutine Charon case uses `--abort-on-error` and exits 101 from its strict failure path. Without that flag, registered errors may have different status/artifact behavior; this report makes no claim about that mode.
- `rustc` and Charon were invoked independently, so rustc's structured JSON is the direct precheck output, not a structured payload returned by Charon. Source content identity and stage result identity must be joined by the harness's exact input hash.
- The supported generated Lean files compiled, but no Rust/Lean semantic correspondence or theorem about `step`/`select` was checked. The failing theorem is an authored diagnostic probe; its error is not automatically a diagnostic for the Rust function.
- The LSP run used one disk-backed document version. Open-buffer divergence, later edits, stale version races, cancellation, and navigation against a deleted declaration were not tested.
- No compiler-provided cross-layer mapping table was observed. The manifest does not upgrade printed names or source comments into authenticated provenance.

## Evidence

- `support/probe.py` SHA-256 `53980c7ec8d3e3dc14cdc3b91404cfb63f41c62ab34e80e0a2c4fb5cb3122114`: replay harness, including assertions for all stage exits, deleted declaration, partial output, and Unicode coordinates. `support/raw-results.json`: exact commands, working directories, environment-derived Lean path, full stdout/stderr, LSP transcript, tool/fixture/artifact hashes. `support/mapping-manifest.json`: compact first-failure, range, LLBC function/file, and candidate-edge inventory.
- `support/fixture/`: all five Rust inputs and the authored Lean proof. `support/artifacts/`: raw LLBC, metadata, generated Lean, compiled local `.olean`, and proof file. `support/tool-versions.txt` SHA-256 `9ba56c65332680a5ffdba1cf150d1f93a0d8c1ae3dbbf4e5ec00d4612e8d62c6`: raw version attempts.
- The prebuilt `Aeneas.olean` used for Lean compilation had SHA-256 `67701a9e8bf68cf0d51a01a4cb5648e2981c08d09402c4c4ac7bb8452d6263cb`; `lake env printenv LEAN_PATH` from the existing `aeneas-release/backends/lean` project supplied its prebuilt dependency paths. The package records that full path string and no dependencies were installed.

Run `python3 support/probe.py` from this package directory with the installed paths configured at the top of the script. It replaces only its own `support/artifacts/`, `support/raw-results.json`, and `support/mapping-manifest.json`. Compare stage statuses, the final server version-1 diagnostic, and source/LLBC/Lean hashes; raw Charon LLBC order can vary across runs, so inspect the serialized item/file structure before inferring a semantic change from a raw digest.

## Revalidation

For another toolchain, replay the five stage cases and the Lean batch/server proof with fresh exact binary/library hashes. Check the first failing stage before mapping messages, retain each raw coordinate form, and verify the final LSP diagnostic for the requested document version. Rebuild the lexical candidate map from Charon item IDs/spans and Aeneas emitted comments, and inspect any new authenticated provenance format before promoting an edge's evidence level. For an Anneal integration, add open-buffer edits, stale result suppression, and deleted-obligation UI behavior as separate tests.
