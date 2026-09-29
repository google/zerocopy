# Piecewise projection, coordinate, and stale-patch properties in an illustrative harness

## Summary

A deterministic property harness checked 2,982 invertible source boundaries across 106 Unicode/line-ending specimens and 800 edit steps against full projection regeneration. Its restricted incremental path matched regenerated text and segment maps in all 393 fast-path steps; 407 edits used full regeneration. Negative controls rejected edits into synthetic text, across distinct authored segments, at ambiguous insertion borders, and after the host/projection/version changed. The harness also preserved a concrete counterexample: inserting a scalar between CR and LF makes a naive projected-byte splice disagree with full regeneration, so that edit must leave the fast path in this fixture.

The projector is a deliberately small illustrative model. It is not Anneal's current or historical annotation parser, and passing these properties is not evidence that Anneal's real source projection is correct.

## Applicability

The harness ran with CPython 3.14.7 on macOS 26.6.2 arm64. It recognizes only source lines beginning with the invented marker `//| `, strips that prefix, copies the rest of each marked line byte-for-byte (including its line ending), and wraps the assembled text in synthetic `namespace Generated` and `end Generated` lines. Its map records one exact authored source-byte interval for each copied line. Prefixes and wrapper text have no editable source interval. This syntax and wrapper are test devices; current Anneal has not selected them.

The coordinate model distinguishes UTF-8 byte offsets, Unicode scalar columns, and zero-based LSP UTF-16 code-unit columns. It accepts only scalar boundaries in line content. Interior UTF-8 bytes, UTF-16 surrogate interiors, and positions inside line terminators are outside the inverse domain. It does not model display-width coordinates, which the existing `cross-tool-utf8-span-columns-2026-09-27` report separately identifies as lossy in pinned Charon spans.

The experiment directly informs the shape of [#3731](https://github.com/google/zerocopy/issues/3731) I025/I026/I029/I032. It gives only illustrative partial evidence for I017/I027. I021/I028/I030/I031 and compiler-backed attachment remain open. The companion `anneal-interactive-model-probes-2026-09-29` report previously checked a hand-authored coordinate/source-map fixture; this package adds randomized edit-stream comparison, strict patch application, and a preserved fast-path counterexample.

## Findings

### Coordinate conversion needs an explicit unit and inverse domain

Across six fixed cases and 100 seeded random specimens, the harness enumerated all 2,982 valid scalar boundaries within line content. Converting each UTF-8 byte boundary to `(line, scalar column, UTF-16 column)` and back through `(line, UTF-16 column)` returned the original byte. Numeric units differed at 2,478 boundaries. For `é🙂á\t界`, the boundary after `é🙂` was scalar column 2 and UTF-16 column 3, while its UTF-8 byte offset was 6. A UTF-16 position inside the emoji's surrogate pair and a byte inside `é`'s UTF-8 encoding were rejected.

These results confirm the fixture's conversion arithmetic for the enumerated strings; they falsify the naive rule that one numeric column can be copied between byte, scalar, and UTF-16 positions. This does not run the pinned Lean LSP or rustc coordinate converters. The design implication is to retain exact source bytes and coordinate-unit tags at a projection boundary.

Basis: **execution**, `support/probe.py` `coordinate_probe`, `support/raw-results.json` `coordinates`; the cross-tool interpretation is **derived** in conjunction with the existing pinned-source coordinate report.

### Authored provenance and edit authority are narrower than diagnostic attribution

The illustrative projection records exact byte intervals only for copied line payloads. `authored_range` maps a projected edit back only when the entire nonempty range lies inside one authored segment. It rejects a wrapper edit, an edit spanning two segments, and a zero-width insertion at a segment border. This is deliberately conservative: two projected segments may touch in generated text while a stripped Rust prefix separates their source intervals. An anchor that explains a synthetic diagnostic would not by itself justify a source replacement.

A patch for the word `trivial` applied to the unmodified host and regenerated to the expected projected replacement. Inserting an unrelated line before the proof left an old byte offset plausible but changed the host hash; the guarded application returned `stale-snapshot`, while an unguarded old-offset replacement corrupted different text. Changing only the projection object or document version likewise returned `stale-snapshot`. The guard compares the expected host hash, projected hash, version, exact mapping, and expected source bytes before applying.

This confirms the fixture's exact-origin and compare-and-swap rule and illustrates why source location alone does not authorize editing. It does not implement an LSP WorkspaceEdit transaction, concurrent multi-file CAS, snippets, imports, or code actions.

Basis: **execution**, `support/probe.py` `patch_probe`, `support/raw-results.json` `patches`; broader edit-policy consequence is **derived**.

### An edit stream can be checked against regenerated ground truth after every edit

With seed `0x3730029 + 1`, the harness made 800 deterministic source edits containing ASCII, `é`, emoji, combining marks, tabs, CJK text, empty replacements, line breaks, and marker text. The incremental path was permitted only for an edit strictly inside one copied segment and away from line-ending boundaries; otherwise it regenerated the entire projection. After every edit, it compared projected text and every source/projected segment endpoint with a fresh full projection. All 393 incremental and 407 full-path steps matched; an intentionally corrupted segment endpoint was detected by the equality comparator.

During construction, an earlier fast-path predicate allowed insertion between `\r` and `\n`. Python's line split then treated the resulting bare CR as one line break and the later LF as another, so the inserted scalar was no longer part of the marked source line. A simple byte splice still copied it. `newline_boundary_probe` preserves the minimal `//| a\r\n` → `//| a\ré\n` counterexample and verifies that the tightened predicate selects full regeneration. This is a fixture-level bug and repair, not an observed Anneal bug.

The run establishes equivalence to this harness's full-regeneration implementation over the recorded edits, not general correctness of its parser or a performance advantage. The cost/latency part of I032 remains unmeasured.

Basis: **execution**, `support/probe.py` `random_edit_probe` and `newline_boundary_probe`, `support/raw-results.json` `edit_stream`/`newline_boundary`; the fast-path restriction is **derived** from the demonstrated counterexample.

## Boundaries

- **Not examined:** real Anneal annotation syntax, Rust lexer/parser recovery, macro-expanded attachment, conditional compilation, Charon source spans, actual Lean projection, diagnostics, completion edits, formatter behavior, or human usability. I017–I024 remain largely unanswered.
- **Not examined:** one-to-many obligations or many-to-one declaration attribution. This fixture's one-line exact intervals only show why diagnostic ownership and edit authority should be separate; it does not resolve I027's real navigation problem.
- **Not examined:** LSP position-encoding negotiation other than UTF-16, invalid surrogate text, display-width inversion, or normalization by an external editor. The property domain is Unicode scalar text with exact retained UTF-8 bytes.
- **Not examined:** byte-level random mutation creating invalid UTF-8. Edits are generated as Python Unicode strings. No throughput, memory, or incremental-update latency measurement is claimed.
- **Unknown:** whether the current or future Anneal generator can share one batch/live projection path, including imports, scaffold text, and unfinished proofs (I028). This fixture has one projector but no actual batch or live Anneal sink.
- Full regeneration is the oracle for the incremental path, so a shared defect in the illustrative parser could pass the comparison. The injected endpoint corruption checks comparator sensitivity only.

## Evidence

- `support/probe.py`: complete harness, SHA-256 `78e4b04b5f1278a3c24f6b4d38360bf3ec8eb3cd69fa6dc37ac41d87bbee6e83`.
- `support/raw-results.json`: environment, coordinate counts, patch outcomes, newline counterexample, initial/final source, and all 800 edit decisions with per-step host/projection digests, segment maps, and oracle comparison. Seed and step count are in this file.
- `support/command.stdout`: successful invocation output: `{"corruption_detected": true, "mode_counts": {"full": 407, "incremental": 393}, "steps": 800, "valid_boundaries": 2982}`.
- `support/host.txt`: observed Python/macOS/kernel identity, script digest, and corpus checkout parent commit `37a0ecd080d333f93bfe900d9c7dab193608e478`.
- Existing context: `cross-tool-utf8-span-columns-2026-09-27` for pinned rustc/Charon/Aeneas/Lean coordinate units; `anneal-synthesized-scaffolding-diagnostic-provenance-main-41f5b37` for historical V1 `Source` versus synthetic anchors; `anneal-interactive-model-probes-2026-09-29` for earlier finite identity/projection cases. None of their implementation claims is revalidated here.

Run `python3 support/probe.py` from this package directory. The script overwrites its own `support/raw-results.json` with the replay result; no external service or repository mutation is required.

## Revalidation

At a new Python pin, rerun the included script and inspect both assertion outcomes and the per-step trace. For an Anneal implementation, substitute its actual annotation parser and generator as the full-regeneration oracle, instrument exact byte-source segments and synthetic provenance, feed the same Unicode and edit cases through both batch and live paths, and require a real patch application to reject stale host/projection generations. Add independent compiler-backed attachment, diagnostic and code-action probes before generalizing beyond projection mechanics.
