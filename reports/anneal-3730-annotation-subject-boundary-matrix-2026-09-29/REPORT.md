# Annotation discovery and compiler-subject boundary matrix

## Summary

A tiny Rust crate with five invented `//%` comment annotations, a shared Lean helper, namespaced claims, a build script, and an `include_str!` macro was run through actual rustc, Cargo, pinned Charon, and Lean. A deliberately small line-marker locator continued to discover complete annotation text when Rust parsing failed, but Charon could not produce a compiler-backed subject for that malformed source. An unfinished comment marker compiled as Rust yet remained incomplete in the locator and contributed no projected Lean text.

The same baseline `src/lib.rs` bytes yielded different Charon function sets under default library, selected-feature library, and test subjects. Moving the annotated item to another namespace and line changed its serialized name, span, and in-crate ID. Duplicating its marker made a marker-only lookup return two compiler-derived candidates. A comment-only proof edit changed both the `include_str!` result and a build-script-derived environment value, despite both projected Lean texts compiling. These are direct tool observations plus an **illustrative locator model**, not evidence that Anneal currently discovers, attaches, or regenerates annotations this way.

## Applicability

The host was macOS 26.6.2 arm64. The executed tuple was local nightly-2026-05-31 rustc 1.98.0-nightly and Cargo 1.98.0-nightly, Charon binary SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`, and Lean 4.30.0-rc2 commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. Exact executable SHA-256 values, argv, cwd, exit codes, stdout/stderr, and source hashes are in [`support/summary.json`](support/summary.json) and [`support/raw-results.json`](support/raw-results.json). `charon --version` rejects that flag; its binary hash identifies the acquired executable. All commands ran offline in isolated targets with no external package dependency. Charon target dirs were removed after each subject, and no global toolchain or cache was modified.

The fixture syntax `//% begin <id> scope=...`, payload `//% ...`, and `//% end` is invented here. The locator uses line scanning and a seven-line next-function heuristic. Separate `/// proof-id: ...` doc markers are consumed by Charon as a compiler-derived **surrogate** for matching: Charon did not parse the `//%` blocks, and the proximity between a block and a doc marker is fixture construction, not compiler-authenticated attachment of the block. An explicit `missing`, `unique`, or `ambiguous` verdict over those serialized doc-marker candidates is in [`support/attachment-manifest.json`](support/attachment-manifest.json).

## Executed boundary cases

| Case | Minimal locator | Rust/Lean result | Compiler-backed consequence |
|---|---|---|---|
| Baseline | Five complete blocks: module helper; two namespaced claims; selected and test claims | rustc and projected Lean exit 0 | Charon default library has `claim-a` and `claim-b`; selected/test items absent. |
| Malformed Rust signature | Same five complete text blocks | rustc exits 1 with unclosed delimiter | Charon Cargo extraction exits 101 with no LLBC. Text discovery grants no valid compiled attachment. |
| Unfinished trailing marker | Five complete blocks plus `orphan` marked incomplete; orphan excluded from projection | rustc exits 0 | No Charon run for this variant; it tests scanner recovery only. |
| Moved item | `claim-a` block and `alpha` moved from `left` to `relocated`, line 17 to 49, with matching Lean namespace update | rustc and projected Lean exit 0 | Charon name changes from `left::alpha` to `relocated::alpha`, ID 4 to 5. |
| Duplicated marker | Two `claim-a` blocks, with distinct Rust items and Lean namespaces | rustc and projected Lean exit 0 | Charon default library has two `proof-id: claim-a` candidates (IDs 4 and 5); marker-only binding is ambiguous. |
| Proof-comment edit | One `//% theorem` line changes `by rfl` to `by exact rfl`; Rust declarations otherwise unchanged | rustc and both Lean projections exit 0 | `include_str!("lib.rs")` changes source length 1141→1147; `build.rs` annotation-line stamp changes 43240→43805; emitted rustc metadata hashes differ. |

The baseline model projects all five complete blocks into one Lean text. That text compiles, including selected/test claim blocks even when the default Rust library subject lacks those functions. This illustrates why a text-only projection cannot itself certify which compiled Rust item owes a proof. The shared `helper` precedes `Left::checked` and `Right::checked`, and the moved/duplicated versions keep those namespaced declarations compiling. This is a small order/visibility control, not an Anneal document-layout test.

The Cargo observation program is an example target. Its first and second runs reuse one Cargo target directory after the proof-comment edit. The build script declares `rerun-if-changed=src/lib.rs` and computes a stamp from annotation lines; `include_str!` reads the same source file at compile time. These are two concrete routes by which a nominally proof-only comment edit changes compilation inputs. No external proc macro, include-generated file, or production Anneal proof-only classifier was executed.

## Exact subject and attachment observations

Five Charon extractions succeeded with `has_errors: false`: baseline `--lib` had 5 local functions, baseline `--lib --features selected` had 6, baseline `--tests` had 14, moved `--lib` had 5, and duplicated `--lib` had 6. The first three used byte-identical baseline source. Their LLBC files and per-item structured names, doc markers, spans, file-table hashes, and local IDs are preserved under [`support/artifacts`](support/artifacts) and in the raw results. The test subject includes harness-generated functions, so its count is a subject observation, not a claim about annotation count.

`selected` has zero Charon marker candidates in default `--lib` and one in selected-feature `--lib`; `test-only` has zero in default `--lib` and one in `--tests`. `claim-a` has one candidate before duplication and two afterward. Cross-extraction comparison by doc marker or path is a lexical candidate comparison; Charon's local ID is not a persistent identity through moves. The malformed Rust case retained complete locator text but Charon exited 101 without a usable LLBC. Exact outcomes and ambiguity verdicts are asserted by [`support/check.py`](support/check.py).

## Issue and #3730 B-row crosswalk

| Agenda | New bounded evidence | Remaining condition |
|---|---|---|
| I017 / B06 | Complete text discovery during malformed Rust and an unfinished marker withheld from projection | Real Anneal annotation grammar, parser recovery across delimiters/attributes/Unicode/unfinished Lean, and editor behavior. |
| I018 / B09 | Comment-only proof edit changed actual `include_str!` and build-script inputs | Full dependency classifier across proc macros, `include!`, generated files, feature selection, and production extraction. |
| I019–I021 / B14 | Charon subject candidates, absent feature/test item, moved span/name/ID, duplicated marker ambiguity | Real annotation-to-compiler attachment, macro-expanded/trait/local items, stable cross-run correspondence, and explicit ambiguity handling in Anneal. |
| I022 / B07–B08 | Five blocks, shared helper, order and namespaces in compiled Lean projection | Actual generated wrapper/import semantics, multiple files, recursive helpers, scope/options/instances, and failure isolation. |
| I023 | Invalid Rust prevents Charon model acquisition while text remains visible | Actual broken-model Lean proof interaction and diagnostic lifetime. |
| I024 | Authored proof text remains in Rust source across two Cargo runs | Unsaved editor buffer, save/overwrite authority, and external proof ownership. B15 remains outside this fixture. |
| I028 | One model projector is run against several source variants | No actual Anneal batch/live generator or equality comparison. |
| I035 / B07 | One combined Lean projection demonstrates helper visibility and namespace separation | Per-annotation/per-file/per-artifact cost and isolation are a separate earlier Lean/Lake report; actual Rust annotation layout remains untested. |

B10's generated/authored edit authority and B09's import-header ownership are not exercised by this fixture. The table maps the directly relevant B rows; it does not convert their broader suggestions into completed outcomes.

## Limits and replay

The locator is intentionally not a Rust parser. Its seven-line next-function association is tentative and can be wrong under attributes, nested items, macros, reordering, or malformed syntax. The Charon `proof-id` markers are separate Rust doc comments rather than the Lean-bearing `//%` payloads. A one-to-one relationship was manufactured for the unique cases; the duplicate and absent controls show why that relationship cannot simply be assumed. Lean compiled only the model's projected text, with no Aeneas-generated model, no Rust-to-Lean correspondence check, no Anneal implementation, and no MCP/editor integration. The proof edit's observable Cargo effects show an unsafe assumption for this fixture, not that every comment change affects every toolchain.

[`support/probe.py`](support/probe.py), SHA-256 `d600c58b12e0f2b95aeb1194780e396725024de16d7ee58d1066f30de6b3de71`, writes the six Rust variants, tiny Cargo project, six projected Lean files (four compiled), commands and five successful plus one failing Charon acquisition. [`support/raw-results.json`](support/raw-results.json) has 35 ordered events and SHA-256 `c9d05f4aa650c6f5a8caa105eedcc63c6b49b6692ba455d6f55975b594029888`. The [attachment manifest](support/attachment-manifest.json) SHA-256 is `82626015b38978eaa5f23043908b67807c1719b02592525191b4ce009d285a90`. The included self-check passed. Generated support material is about 0.5 MB, and this local run completed in under eight seconds; that is no scale claim.

Replay from this package with `python3 support/probe.py` then `python3 support/check.py`. The probe replaces only its own `support/work`, `support/versions`, `support/artifacts`, and `support/raw-results.json`; the check writes summary and attachment manifest. It requires the pinned tools at the paths declared near the top of the script. Compare source, tool, and LLBC hashes with care: an exact artifact hash may vary after a different build path or toolchain pin. Preserve the missing/unique/ambiguous candidate outcomes and raw compiler diagnostics before inferring a new attachment rule.
