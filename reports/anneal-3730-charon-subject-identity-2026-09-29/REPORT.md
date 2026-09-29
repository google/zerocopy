# Charon item identity under feature, target, macro, and structural changes

## Summary

A dependency-free Cargo fixture was extracted six times with pinned Charon while reusing one `src/lib.rs` pathname. The same A source bytes yielded different local LLBC function sets for default-feature library, `selected`-feature library, and test target. Charon serialized distinct structured paths and in-crate IDs for same-named module functions; it also carried a macro-generated function whose item span pointed into the macro definition. A doc marker on a trait default appeared on both the trait method and an impl method. Moving an otherwise unchanged annotated function changed its LLBC ID and source span; duplicating it made its marker ambiguous.

These results show why a source-level annotation locator needs an explicit compilation subject and an ambiguity/missing-subject outcome before proposing an attachment. Charon's IDs, structured names, attributes, file table, and spans are serialized compiler-derived facts **within one LLBC**. Matching a doc marker or display path across separate extractions is a lexical candidate comparison, not an authenticated persistent annotation identity. No Anneal attachment mechanism was executed.

## Applicability

The fixture used Cargo/rustc nightly-2026-05-31 on macOS arm64 with no external dependencies. The Charon executable SHA-256 was `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`; Cargo and rustc executable hashes and exact command arrays are in `support/raw-results.json`. Charon `--version` was rejected, so the binary hash identifies what ran. A local Charon source checkout at `AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` was inspected for context, but this report's behavior claims come from the executable and preserved LLBC.

Each run invoked `charon cargo --preset aeneas --dest-file <private>.llbc -- --manifest-path <fixture/Cargo.toml> <subject flags> --offline --locked` with a fresh `CARGO_TARGET_DIR`. The six subjects were A default library, A library with `--features selected`, A `--tests`, moved B default library, duplicated C default library, and restored A default library. The script copied each version into the **same** `support/fixture/src/lib.rs` path before extraction and restored A at the end. Target build caches were removed after each run; raw LLBC and full commands/logs were retained. The literal `proof-id:` doc comments are invented fixture markers, not Anneal's annotation syntax.

This report addresses a bounded execution slice of [google/zerocopy#3731](https://github.com/google/zerocopy/issues/3731) I019/I020/I021. The earlier `charon-item-identity-spans-comments-nightly-2026-06-03` report defines the selected Charon source model, while `cargo-rust-charon-anneal-coverage-matrix-2026-09-28` surveys broader Cargo/Charon coverage. This package adds an executable ambiguity and cross-run identity matrix rather than repeating those surveys.

## Findings

### Identical source bytes select different compiler subjects

The A source and LLBC file-table content hash were the same under all three A subjects: `2ff9c22c8e7256331b538113fc4a7f856313142dad50bf4ac053a0968dc20a28`. The default library extraction had local `default_only` and lacked `selected_only`; with `--features selected`, those presences reversed and the `#[cfg_attr(feature = "selected", doc = "proof-id: conditional")]` marker appeared on `selected_only`. The default library lacked `tests::test_subject`; the `--tests` extraction contained it and the test harness added local functions. The local function counts were 10, 10, and 19 respectively.

The missing outcomes are explicit in `support/mapping-manifest.json`: the default-library subject has zero candidates for `selected_only` and `tests::test_subject`, and the selected-feature subject has zero for `default_only`. A path plus source hash would collide across these compilation subjects even though their emitted item sets differ. The exact Cargo target/features and tool input identity must accompany an attachment query. This fixture does not establish the minimum complete subject key for all Cargo environments.

Basis: **execution** of the three A Cargo/Charon commands and serialized LLBC; the attachment-key consequence is **derived**.

### Short names and marker text can be ambiguous inside one LLBC

The default-library LLBC had two local `duplicate` functions with the same short name and distinct structured paths: `subject_identity_probe::left::duplicate` (`def_id` 4) and `subject_identity_probe::right::duplicate` (`def_id` 5). A short-name-only locator therefore has two candidates. A fully scoped Charon path and its in-crate ID distinguish these entries in this LLBC; their authored doc markers `left-duplicate` and `right-duplicate` also differ in this fixture.

The one authored `proof-id: trait-default` doc comment appeared in two local function records: trait `Rule::defaulted` (`def_id` 6, source line 22) and an impl-associated `defaulted` (`def_id` 8, span on the impl block at lines 27–30). Charon's structured name for the latter contains an `Impl` element referring to its trait. This is an observed one-marker/two-record outcome, not evidence of two authored annotations or two independently owed proofs. An attachment rule based on marker text alone must recognize the multiplicity instead of silently choosing one.

Basis: **execution**, `support/mapping-manifest.json` `ambiguous_locator_controls` and the preserved default-library LLBC. The source file shows the single trait-default marker.

### A macro-generated item is represented, but its item span is not its invocation

`macro_rules! emit_generated` emitted local `generated` with `def_id` 1 and serialized `proof-id: macro-generated` doc attribute. Its item span was file ID 0, line 35 columns 8–40, inside the macro's definition; the invocation was at line 38. For this item, `source_text` was null and item `generated_from_span` was null. Charon's item record therefore identifies a generated function and an authored macro-definition location in this case, but it does not by itself identify the invocation as a safe edit target. A user-facing attachment or edit policy would need expansion/call-site provenance beyond this observed item record, or must keep the generated item read-only/ambiguous until that provenance is established.

Basis: **execution** of the macro expansion and serialized LLBC/item metadata. The edit-policy implication is **derived** and applies only to this fixture; statement-level spans may carry other provenance not analyzed here.

### A stable path and restored bytes do not make an ID persistent across edits

Version A put `/// proof-id: movable` on `movable` at line 41, with Charon function ID 2. Version B moved that unchanged doc/function block to line 4 in the same `src/lib.rs`; its function ID became 0, while `default_only` moved from ID 0 to 1 and `generated` from 1 to 2. The structured `subject_identity_probe::movable` path and marker text still matched, but relating B to A is a **lexical cross-run comparison**; Charon did not serialize a persistent cross-run identity edge.

Version C retained B's moved function and added `copy::movable` with the same `proof-id: movable` marker. The marker then matched two distinct local items, IDs 0 and 10. On restoring A source bytes, the marker again matched one item at line 41 with ID 2. The A and restored-A function/file/ordered-declaration projections were equal, while their raw LLBC SHA-256 values differed in this replay. That raw difference is not interpreted as a semantic change here; the earlier Charon report separately documents keyed serialized-name ordering variation.

This A→B→C→A control shows both a transient ID change for the same authored function and explicit duplication of the marker. An attachment to A's `def_id: 2` cannot simply be replayed against B's ID 2; a completed proof tied to A must be revalidated against the selected subject and chosen correspondence after the edit. This is a design consequence, not observed Anneal behavior.

Basis: **execution** for IDs, spans, markers, bytes, and projections; **derived** for cross-run attachment policy. `support/mapping-manifest.json` records the candidate comparisons and evidence level.

## Boundaries

- The `proof-id:` doc strings are fixture text, not a verified Anneal annotation grammar or parser. Charon serialized them as doc attributes; this report did not test whether Anneal would discover or attach them.
- Function IDs are only shown to identify entries within each LLBC. Their values across runs are compared as observations and are **not** asserted to be stable identities. The manifest labels cross-run structured-path/doc-marker comparisons as lexical candidates.
- The macro control is a local `macro_rules!` item. Attribute macros, procedural macros, `include!`, generated files, aliases, local nested items, target triples, file/module renames, and expanded source-map chains remain open I019/I021 cases.
- The `--tests` subject is Cargo's test target selection at this host, with harness-generated items. It is not a separate binary target matrix, and the selected-feature/test interaction was not swept.
- Moving the function changes source bytes and offsets. The fixture does not compare syntax-tree node identities, explicit persistent UUIDs, in-flight query completion, proof usability, or annotation ownership after deletion.
- Charon extraction success and `has_errors: false` establish only this translation stage. No Aeneas model, Lean theorem, Rust/Lean correspondence, or Anneal result was checked for this package.

## Evidence

- `support/probe.py` SHA-256 `4561c1da3a588c91d35c1c534a101170e43a9a5a3c9a4bab78c456e5f7f16814`: complete offline replay, source-path mutation, fresh target dirs, assertions, projection, and cleanup. `support/versions/` retains A/B/C Rust bytes; `support/fixture/` retains the manifest, lockfile, and restored A source.
- `support/artifacts/*.llbc`: all six raw serialized outputs. `support/raw-results.json`: exact commands, environment values, all statuses/stdout/stderr, source/manifest/lock hashes, LLBC hashes, file tables, local function records, structured names, attributes, source text, and spans. `support/mapping-manifest.json`: explicit missing/ambiguous controls and evidence-level labels.
- `support/tool-versions.txt` SHA-256 `28822e0797f54b39411537a2b206434dbabfab9d335db51e67f22f7bd69986fe`: raw rustc/Cargo version strings and Charon version-command rejection. `support/raw-results.json` records tested executable hashes: rustc `2ab7af1e...`, Cargo `71d7b3f8...`, Charon `51bb6d23...`.

Run `python3 support/probe.py` from this package directory with the selected installed paths near the top of the script. The script replaces its own `support/artifacts/`, `support/raw-results.json`, and `support/mapping-manifest.json`, mutates only its fixture's `src/lib.rs`, restores A even on failure, and removes each Cargo target directory after extraction. Raw LLBC SHA values may vary; compare serialized item/file projections and the explicit missing/ambiguity assertions first.

## Revalidation

At a new Charon/Cargo pin, rerun the six subjects with clean target dirs and inspect exact features, target, source bytes, LLBC `has_errors`, local typed IDs, structured paths, attributes, spans, and file-table content. Test any proposed annotation encoding separately, especially when macro expansion or `cfg_attr` can transform it. For a real attachment implementation, add an explicit subject selector and require zero-candidate and multiple-candidate outcomes to be visible; then test move, duplicate, rename, and deletion with in-flight proof results against the chosen identity scheme.
