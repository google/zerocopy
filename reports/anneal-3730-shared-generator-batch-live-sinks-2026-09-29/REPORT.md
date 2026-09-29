# I028: shared generator plan with file and live sinks

## Result

This is a **synthetic generator**, not Anneal source. A typed `Input` carries an import choice and a proof annotation. One `construct` function creates the header, annotation and footer as a deterministic `Plan`, including an exhaustive codepoint-boundary map from annotation UTF-8 offsets to generated UTF-8 offsets and corresponding UTF-16 positions. Two independent sinks consume the same segments: a file sink writes `Generated.lean` incrementally; a live sink sends `didOpen` for the header and two full-text `didChange` notifications to a fresh Lean 4.30.0-rc2 server. The live final document reached version 3 while its generated pathname was still absent on disk. Only after the live query did the harness persist the streamed bytes for a separate batch check.

Across four controls, the file and live sinks produced **byte-identical generated Lean** and used the same plan source map, referenced the same compiled import bytes in their separate private roots, and produced identical `lean --json` return codes and diagnostic records when independently batch-checked. The live server's final diagnostics matched batch messages and severities; batch uses one-based lines and LSP zero-based lines, so raw range objects are not claimed equal. `#check Generated.checked` exposed the same elaborated theorem type, and `#print axioms Generated.checked` exposed the same no-axiom or `sorryAx` result. Each live server returned from `waitForDiagnostics` for document version 3 and exited 0 after shutdown.

| Case | Import OLean | Generated SHA-256 | Both batch exits | Final batch/live declaration, error, axiom result |
| --- | --- | --- | ---: | --- |
| Complete proof | `Base`, value 7 | `85a39246572e2afdf59db30674f3272516b82b10fe4a3532ce66a244909aecaa` | 0 | `Generated.checked : depValue = 7`; no error; no axioms |
| Incomplete `skip` proof | `Base`, value 7 | `0ff077cc11fa4da10f3cd5be6965e6a75604711c126cb4d737160817114fca3e` | 1 | Same declared type; `unsolved goals`; `sorryAx` |
| Import edit | `Alt`, value 9 | `f8088463eb04e121684b6e178c4db4a531c2fece73026f4a0189d43d4b31f73b` | 1 | Same declared type; `decide` finds proposition false; `sorryAx` |
| Unicode and CRLF annotation | `Base`, value 7 | `562a988a9b4d68353699a998ca05e703f4088f5a046fbcdfae32a11147918e5a` | 0 | Same declared type; no error; no axioms |

The `Base.olean` hash was `0d7cc92073e6cb5f6c8c99668439e31b22b58013b97968aa1fcc784bd5bc5e80` in three cases; `Alt.olean` was `f524eb221ac2fcf12ecb0605e4f3df996e022487a179bfa85db4a82aee5eadb8`. The Unicode control preserved CRLF bytes, `λ` and `😀` in both outputs. Its map advances the emoji position by two UTF-16 code units and preserves the fixed header-byte offset for every annotation codepoint boundary. It does not test LSP edits placed inside a CRLF delimiter.

## Evidence and procedure

`support/probe.py` is the typed generator, sink implementation and bounded harness. It writes only its private scratch root under `/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731/i028-work` plus this package's retained `support/results.json` and `support/artifacts/`. The four archived artifact directories contain the original annotation, imported module source, file output, streamed output and map JSON. `support/results.json` retains the exact Lean binary identity, import OLean hashes, generated hashes, file and stream batch commands/status/JSON diagnostics, final LSP diagnostic publications, and the full client/server protocol transcript for each case. It records that the streamed URI was virtual until the live query completed. No download or installation occurred; the cases ran serially with one Lean thread and 20-second CLI bounds.

Run `python3 support/check.py` for offline byte, map, context, batch and LSP assertions. To regenerate on the pinned host, run `python3 support/probe.py` from any directory, then the checker. The probe replaces its own retained results/artifacts and named scratch root; copy the package first if the original observation must remain frozen. The checker confirms all four outcomes, exact import identity per module, three live document versions, matching batch/LSP messages and severities, and the Unicode UTF-16 increment.

## I028 coverage and residual

This executed a **small generator architecture slice**: a single typed plan served a materialized file and a live stream, including incomplete proof, changed import, newline and Unicode controls. It demonstrates that two sinks can share exact text and map construction under one pin, and that batch/live Lean elaborate these selected outputs consistently. It also shows why comparing only exit 0 is insufficient: Lean creates a declaration with `sorryAx` in both negative controls while the batch exit is nonzero.

I028 remains **partial**. No real Anneal batch/live generator or Aeneas output path was modified; no Rust-hosted annotation parser, generated workspace, synchronized model generation, partial import availability, multiple annotations, incremental segment replacement, or long-lived server reuse was tested. A production test must route the same actual Anneal generator through independently materialized and streaming sinks, then compare exact generated bytes, provenance map, imports/options/artifacts, declarations, diagnostics, obligations and acceptance across edits and failures. This report makes no claim that Anneal already has such a shared generator.
