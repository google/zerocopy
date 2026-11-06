# Cross-Tool Source Spans, UTF-8 Columns, and Diagnostic Normalization

## Summary

Across the Rust, Charon, Aeneas, Lean batch, Lake, and Lean LSP toolchain layers selected by Anneal, diagnostic file paths, line/column coordinates, width/format controls, and item/range source correspondence are governed by distinct producer-local conventions rather than a single shared interchange protocol:

1. **Diagnostic path normalization and relocation (`path-policy-matrix.json`):** `rustc`, Charon, Aeneas, direct `lean --json`, `lake build`, and Lean LSP each normalize or preserve file paths differently. `rustc` stores both an optional `local` path and a `maybe_remapped` path in `RealFileName`, using `RemapPathScopeComponents::DIAGNOSTICS` for JSON diagnostics (`filename_for_diagnostics`). Charon `0.1.210` (`translate_filename`) intentionally prefers `name.local_path()` over `rustc`'s diagnostic remap when a local path exists—normalizing `\` separators and rewriting sysroot/Cargo prefixes to `/rustc/...`, `/toolchain/...`, and `/cargo/...` while leaving local workspace paths un-remapped—and falls back to `rustc`'s `MACRO` scope (stripping `/rustc/<40-hex-hash>/`) only when `local_path()` is `None`. Aeneas (`src/Errors.ml`) prints the Charon file string unchanged. Direct `lean --json` preserves the CLI `fileName` passed to `Elab.runFrontend`, `lake build` (`src/lake/Lake/Build/Actions.lean`) rewrites `SerialMessage.fileName` to the package-relative path `mkRelPathString relLeanFile`, and Lean LSP keys `PublishDiagnostics` notifications by `DocumentUri` (`documentUriFromModule?` resolves symlinks).
2. **Multibyte UTF-8 span and column units (`coordinate-matrix.json`):** At least five coordinate conventions coexist across the pipeline: (a) `rustc` JSON diagnostics use 1-based lines, 1-based Unicode scalar ("character") columns (`lookup_char_pos`, `start.col.0 + 1`), and 0-based UTF-8 byte offsets (`byte_start`/`byte_end`); (b) Charon serialized `Meta::Loc` uses 1-based lines and 0-based `rustc` terminal **display width** (`col = rustc_loc.col_display`, where tabs count as 4 columns, combining marks as 0, and East Asian wide/emoji scalars as 2 via `unicode_width`); (c) Aeneas prints Charon `line:col` unchanged; (d) Lean batch `--json` (`Position`) uses 1-based lines and 0-based Unicode scalar columns (`FileMap.toPosition`); and (e) Lean LSP (`Lean.Data.Lsp.Utf16`) uses 0-based lines and 0-based UTF-16 code-unit columns. Critically, Charon `meta_utils.rs` defines `Loc::to_byte(source)` as `line_start_byte + col` and uses `SpanData::to_byte_range` in `charon/src/errors.rs` to slice source text for `annotate_snippets`: after multibyte UTF-8 scalars (`é`, `界`, `😀`), combining marks (`a` + `U+0301`), or tabs, adding display width to a UTF-8 byte offset produces wrong or mid-codepoint byte indices.
3. **Diagnostic width and format controls (`diagnostic-format-matrix.json`):** `rustc` human diagnostics and the `rendered` field inside `--error-format=json` are not width-stable by default: `Session::diagnostic_width()` uses `--diagnostic-width <WIDTH>` if given, `140` under `-Zui-testing`, or terminal dimensions (`termize::dimensions()`) with fallback `140`, and type/trait error reporting consults `diagnostic_width()` to decide whether to truncate or abbreviate type descriptions. Charon `0.1.210` forwards `--rustc-arg` flags to selected `rustc` calls, stabilizing `rustc` output, but Charon's own `ErrorCtx` renders via `annotate_snippets::Renderer::styled()` to `stderr` with no Charon-native width or JSON flag in `CliOpts`. In Lean `v4.30.0-rc2`, `Message.toJson → Message.serialize → MessageData.toString` renders `Format` through the global `ToString Format` instance (`Format.pretty` with fixed `Std.Format.defWidth = 120`), bypassing `-Dformat.width=...` (which is only read by `Format.pretty'`), while `format.inputWidth = 100` (`Lean.Meta.TryThis`) governs code-action suggestion text rather than batch diagnostic bodies.
4. **End-to-end source correspondence across Charon, Aeneas, Lean, and historical Anneal V1:** Charon preserves item-level `ItemMeta` (`Name`, definition `Span`, and optional single-hop `generated_from_span` macro origin, without full `rustc` expansion hygiene). Aeneas preserves `item_meta` on pure declarations (`Pure.ml`, `Translate.ml`) and emits Lean doc comments (`extract_fun_comment`, `extract_comment_with_span`) linking each generated Lean definition to its Rust item name and Charon span (e.g., `[no_nested_borrows::choose]` at `tests/src/no_nested_borrows.rs`, lines `200:0-206:1` in `tests/lean/NoNestedBorrows.lean`). However, Aeneas emits declaration-level spans rather than a subexpression/token byte-range map, so synthesized backward borrow functions, loop helpers (`loop_id`), and termination templates have no 1-to-1 Rust token span. Lean diagnostics and tactic goals (`Widget.msgToInteractiveDiagnostic`, `FileWorker.publishDiagnostics`) address the generated Lean document only; historical Anneal V1 (`anneal/v1/src/generate.rs`, `anneal/v1/src/aeneas.rs`) bridged this gap via an explicit `SourceMapping` byte-range sidecar (`Source`, `Synthetic`, `Keyword`).

## Applicability

The source-level findings in this package apply to the exact toolchain revisions selected by Anneal (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`):

- **Rust compiler (`nightly`, selected by Charon's `rust-toolchain`):**
  - `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` and `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (sharing identical `compiler/rustc_session/src/config.rs` blob `e82f67eac5e9f7d0b089727e6317d77242ba3b1c` and `compiler/rustc_errors/src/json.rs` blob `04ac140f332618d6fa81254e9a16bc27c729eef5`).
- **Charon (`0.1.210`, pinned by Aeneas `nightly-2026.06.03`):**
  - `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.
- **Aeneas (`nightly-2026.06.03`, selected by Anneal):**
  - `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.
- **Lean and Lake (`v4.30.0-rc2`, selected by Aeneas and Anneal):**
  - `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.
- **Anneal design and historical V1 implementation:**
  - `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/DESIGN.md`, `anneal/PRINCIPLES.md`, `anneal/src/main.rs`, and historical `anneal/v1/src/{generate.rs,aeneas.rs,diagnostics.rs}`).

All findings in this package are established from pinned implementation source and checked-in upstream artifacts (`tests/lean/NoNestedBorrows.lean`), without fresh process execution.

## Findings

### Diagnostic Path Normalization and Relocation Across the Anneal Toolchain

#### `rustc` scope-sensitive path remapping vs Charon `local_path()` preference

Basis: **source** + **derived** (`path-policy-matrix.json`, `support/cross-tool-diagnostic-path-normalization/path-policy-matrix.json`).

In `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`:

- `rustc_span::RealFileName` (`compiler/rustc_span/src/lib.rs`, blob `2371bf15756dac74f5488d5d0b069ed6673014a5`) stores an optional `local` host path, a `maybe_remapped` path, and `RemapPathScopeComponents` (`MACRO`, `DIAGNOSTICS`, `DEBUGINFO`, `COVERAGE`, `DOCUMENTATION`, defaulting to all scopes in `compiler/rustc_session/src/config.rs`, blob `e82f67eac5e9f7d0b089727e6317d77242ba3b1c`).
- `rustc_errors::json::DiagnosticSpan::from_span_full` (`compiler/rustc_errors/src/json.rs`, blob `04ac140f332618d6fa81254e9a16bc27c729eef5`) formats `file_name` via `SourceMap::filename_for_diagnostics` (`compiler/rustc_span/src/source_map.rs`, blob `47c933e245d4942a81f48dc8bcd6b15ba9c39ea7`), which requests `RemapPathScopeComponents::DIAGNOSTICS`. Even when remapping is active, `FilePathMapping::to_real_filename` retains `local` so tools can read the file from disk.
- In Charon `0.1.210` (`charon/src/bin/charon-driver/translate/translate_meta.rs`, blob `187a703dff83687f369f1903c6646aabdff259d3`), `translate_filename` branches on `name.local_path()` **first**:
  1. When `local_path()` is `Some(path)`, Charon ignores `rustc`'s `DIAGNOSTICS` remap, splits on `\` to normalize Windows separators, rewrites paths under `lib/rustlib/src/rust` to `/rustc/<remainder>`, rewrites other sysroot paths to `/toolchain/<remainder>`, and rewrites `$CARGO_HOME` (or `$HOME/.cargo`) paths to `/cargo/<remainder>`, while leaving local workspace paths as raw host paths.
  2. When `local_path()` is `None` (e.g., imported crate metadata without a resolved local file), Charon queries `name.path(RemapPathScopeComponents::MACRO)`—not `DIAGNOSTICS`—and strips a leading `/rustc/<40-hex-hash>/` prefix to `/rustc/...`.
- Once serialized into Charon's `meta::FileName` (`Local`, `Virtual`, or `NotReal` in `charon/src/ast/meta.rs`, blob `7a80a92ea1b3f3eaff1758554001e32019473237`), `rustc`'s original `RealFileName` and scope set are discarded. Aeneas (`src/Errors.ml`, blob `c135674b8601786616c6c20ad81ec388bb8cbfea`) formats `Meta.span_data` by printing the Charon file string verbatim.

#### Lean batch CLI, Lake build rewrite, and Lean LSP URI policies

Basis: **source** + **derived**.

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`:

- **Direct `lean` CLI (`src/Lean/Shell.lean` blob `2ff5c4b0c82f876ddd4384c9c20dcaefb1b90e`, `src/Lean/Message.lean` blob `a7f76198c582d1d2032bb24d13ad4cb7a272fa57`):** Passes the CLI input filename string directly to `Elab.runFrontend`, which stores it in `BaseMessage.fileName` and `SerialMessage.fileName`. Invoking `lean --json` on `/scratch/run-A/Generated.lean` vs `/scratch/run-B/Generated.lean` therefore changes `fileName` even when file bytes are identical.
- **Lake build action (`src/lake/Lake/Build/Actions.lean` blob `5b3ab3cc3e9f45b8c695e31680342acc795004c7`):** Runs Lean with `--json`, parses each `SerialMessage`, and rewrites `msg.fileName` to `mkRelPathString relLeanFile` before logging. By contrast, invoking `lake env lean --json <path>` directly runs the Lean CLI in Lake's environment without passing through `Build/Actions.lean`'s relative-path rewrite.
- **Lean LSP (`src/Lean/Server/Utils.lean` blob `46a0826d3941b9f749ee4770273eac97d0501103`, `src/Lean/Data/Lsp/Diagnostics.lean` blob `d15c1ce80d3699be7a5d92ebf6cea6725c3a4b34`):** `DocumentMeta.mkInputContext` converts the client's `DocumentUri` to a filesystem path for the frontend, `mkPublishDiagnosticsNotification` publishes diagnostics back under the original `m.uri`, and `documentUriFromModule?` resolves symlinks via realpath before constructing server-originated module URIs.

| Toolchain Surface | Emitted Path / Locator Representation |
| --- | --- |
| `rustc` JSON diagnostic | `RealFileName::path(RemapPathScopeComponents::DIAGNOSTICS)` via `SourceMap::filename_for_diagnostics`. |
| Charon local/workspace source | `RealFileName::local_path()`, then `\` separator normalization and `/rustc`, `/toolchain`, `/cargo` prefix canonicalization. |
| Charon imported source without `local_path()` | `RealFileName::path(RemapPathScopeComponents::MACRO)` with `/rustc/<40-hex-hash>/` stripped to `/rustc/`. |
| Aeneas source diagnostic / doc comment | Stored Charon `FileName` string (`Local`, `Virtual`, or `NotReal`) printed verbatim. |
| Direct `lean --json` batch CLI | Frontend `fileName` string verbatim from the CLI argument. |
| `lake build` subprocess log | `SerialMessage.fileName` rewritten to Lake package-relative `mkRelPathString relLeanFile`. |
| Lean LSP `publishDiagnostics` | Client/server `DocumentUri` (`m.uri`), with symlinks resolved on server-constructed module URIs. |

---

### Multibyte UTF-8 Span and Column Behavior Across the Toolchain

#### Five incompatible line/column coordinate systems and Charon's `to_byte` unit bug

Basis: **source** + **documentation** + **derived** (`coordinate-matrix.json`, `support/cross-tool-utf8-span-columns/coordinate-matrix.json`).

| Toolchain Surface | Line Base | Column Base | Column Unit | Internal / Auxiliary Offset |
| --- | ---: | ---: | --- | --- |
| `rustc` JSON diagnostics (`DiagnosticSpan`) | `1` | `1` | Unicode scalar values (`CharPos`, `start.col.0 + 1`) | 0-based UTF-8 byte offsets (`byte_start`, `byte_end`) |
| Charon serialized `Meta::Loc` | `1` | `0` | `rustc` terminal **display width** (`col_display`) | None (`BytePos` and `CharPos` discarded) |
| Aeneas source locations (`Errors.loc_to_string`) | `1` | `0` | Charon display width, printed unchanged | None |
| Lean batch `--json` (`Position`) | `1` | `0` | Unicode scalar values (`FileMap.toPosition`) | Internal UTF-8 byte index (`String.Pos.Raw`) |
| Lean LSP (`Lsp.Position`) | `0` | `0` | UTF-16 code units (`leanPosToLspPos`) | Converted from Lean `Position` + `FileMap` |

- **`rustc` byte vs scalar vs display columns:** In `compiler/rustc_span/src/lib.rs` (`2371bf15756dac74f5488d5d0b069ed6673014a5`), `SourceFile::lookup_file_pos` converts a `BytePos` into a 0-based Unicode scalar count `CharPos` (`Loc.col`), while `lookup_file_pos_with_col_display` sums `char_width` (tab = `4`, control = `1`, others = `unicode_width`) to compute `Loc.col_display`. `rustc` JSON (`compiler/rustc_errors/src/json.rs` and `src/doc/rustc/src/json.md` blob `7421dd6210806f8e3a9b310f8f72578830309abe`) serializes `byte_start`/`byte_end` and 1-based scalar `column_start`/`column_end` (`start.col.0 + 1`), never `col_display`.
- **Charon `col_display` lossiness and `Loc::to_byte` mismatch:** In Charon `translate_meta.rs` (`187a703dff83687f369f1903c6646aabdff259d3`), `translate_span_data` calls `lookup_char_pos` and stores `col = rustc_loc.col_display` into `meta::Loc { line, col }` (`charon/src/ast/meta.rs` blob `7a80a92ea1b3f3eaff1758554001e32019473237`). Display width is non-injective: after `a` + `U+0301` (COMBINING ACUTE ACCENT), the boundary after `a` and the boundary after `U+0301` both have display column `1`. Worse, `charon/src/ast/meta_utils.rs` (blob `795723c998cf03c930d7c88200577786297f79e6`) defines `Loc::to_byte(source)` as `line_to_start_byte(source, line) + col`, and `charon/src/errors.rs` (blob `e4107c6deb5741d523d2220820d1ee0355adb3c0`) passes `span.to_byte_range(source)` to `annotate_snippets`:
  - After narrow 2-byte UTF-8 `é` (`éx`), the boundary after `é` is at byte offset `2`, but `col_display = 1`, so `to_byte` returns byte `1` (splitting the 2-byte UTF-8 sequence of `é`).
  - After wide 3-byte UTF-8 `界` (`界x`), the boundary after `界` is at byte offset `3`, but `col_display = 2`, so `to_byte` returns byte `2` (splitting `界`).
  - After a single tab `\t`, the boundary is at byte offset `1` (scalar column `1`), but `col_display = 4`, so `to_byte` returns byte `4`.
- **Lean scalar vs UTF-16 columns:** In `src/Lean/Data/Position.lean` (blob `f5eae212ed37f753a495437dc7b0c7f6cfeaa945`), `FileMap.toPosition` advances UTF-8 string positions via `String.Pos.next` (1 column per Unicode scalar), serialized directly by `Message.toJson` (`src/Lean/Language/Basic.lean` blob `08f9b688fc869224c316175220403c2aeb5eb415`). In `src/Lean/Data/Lsp/Utf16.lean` (blob `a779f34edfaf80f50c389599b5cd3c67ffcc38b0`), `leanPosToLspPos` converts 1-based lines to 0-based lines and counts UTF-16 code units (so supplementary emoji `U+1F600` `😀` advances Lean batch `column` by `1` and Lean LSP `character` by `2`).

---

### Stable Diagnostic Width and Format Controls in the Anneal Toolchain

#### `rustc`, Charon, and Lean width/format control matrix

Basis: **source** + **derived** (`diagnostic-format-matrix.json`, `support/diagnostic-format-controls-v4-30-0-rc2/diagnostic-format-matrix.json`).

| Diagnostic Surface | Default Width Behavior | Explicit Width Control | Machine-Readable Format & Coupling |
| --- | --- | --- | --- |
| `rustc` human diagnostics (`AnnotateSnippetEmitterWriter`) | Terminal width via `termize::dimensions()`, else `140`; fixed `140` under `-Zui-testing` (`Session::diagnostic_width()`) | `--diagnostic-width <N>` | None (human text; width also changes type/trait abbreviation thresholds) |
| `rustc` JSON `rendered` field (`--error-format=json`) | Same `Session::diagnostic_width()` passed into `AnnotateSnippetEmitter` | `--diagnostic-width <N>` | JSON object (`message`, `code`, `level`, `spans`, `children`, `rendered`); `--color` forbidden with `--json` (use `--json=diagnostic-rendered-ansi`, `diagnostic-short`, `diagnostic-unicode`) |
| Charon-native errors (`ErrorCtx` in `charon/src/errors.rs`) | `annotate-snippets` `0.12.12` `Renderer::styled()` to `stderr` via `anstream` `0.6.20` | None in `CliOpts` (`--rustc-arg` only affects `rustc`) | None (no Charon-native JSON diagnostic mode) |
| Lean batch `Message` text & `lean --json` `SerialMessage.data` | Fixed `Std.Format.defWidth = 120` via global `ToString Format` (`f.pretty`) | None in `Message.serialize` (`-Dformat.width` is only read by `Format.pretty'`, not `MessageData.toString`) | `lean --json` emits 1-line JSON `SerialMessage`, but `data` is pre-rendered 120-column text |
| Lean code-action / `TryThis` suggestions (`Lean.Meta.TryThis`) | `format.inputWidth` default `100` (`SuggestionText.prettyExtra`) | `-Dformat.inputWidth=<N>` or explicit `Suggestion.pretty` width | Embedded in higher-level suggestion/code-action structures |

- **`rustc` content sensitivity to width:** In `compiler/rustc_session/src/session.rs` (blob `c83bb62324e76a068651578223290961d655dd3d`) and `compiler/rustc_errors/src/annotate_snippet_emitter_writer.rs` (blob `c3c9f26c31571596875822ae7227d51dfb34f16b`), `Session::diagnostic_width()` is queried not only for line wrapping but also by type-error and trait-error formatters to decide when to elide or externalize long types.
- **Charon `--rustc-arg` forwarding:** In `charon/src/options.rs` (blob `f08f8bae08d7fb5f38773c0be038d925fe80cb4c`) and `charon/src/bin/charon-driver/driver.rs` (blob `3f90a7a31857aed462694066e5ffaa6e28b9dcfa`), repeatable `--rustc-arg` entries are serialized through `CHARON_ARGS` and appended to selected compiler invocations, whereas `charon/Cargo.lock` (blob `b623c6c4c3558f441ec2bc5281cec61080126c0c`) locks `annotate-snippets 0.12.12` for Charon's own `stderr` rendering.
- **Lean `Format` serialization path:** In `src/Init/Data/Format/Basic.lean` (blob `e0dbb5fa8be5578f8904e0e5a36decbcdf3fbec4`), `Std.Format.defWidth = 120`. `src/Init/Data/ToString/Basic.lean` (blob `505aa15ca363d66f70f850134b008d98c93df184`) defines `ToString Format` as `f.pretty` (using `defWidth = 120`), whereas `Format.pretty'` in `src/Lean/Data/Format.lean` (blob `9bcb44e2ce7c6848dd1f1d7a3f2801ccc54b4f42`) reads `format.width`. Because `Message.serialize` (`src/Lean/Message.lean` blob `a7f76198c582d1d2032bb24d13ad4cb7a272fa57`) calls `msg.data.toString`, which formats `MessageData` to `Format` and invokes `toString`, `-Dformat.width=...` does not change final line wrapping of batch `lean --json` messages. Separately, `src/Lean/Meta/TryThis.lean` (blob `b54e1160df2aa69c282941fbc673d99e5eef708d`) registers `format.inputWidth = 100`.
- **Current Anneal V2 surface (`anneal/src/main.rs` blob `b947700606677ea89c7a205f3ffcc75493508f63`):** The archive-reuse integration test invokes `lake --keep-toolchain env lean --json generated/Generated.lean`, while historical V1 (`anneal/v1/src/diagnostics.rs` blob `cd27b771e2f22bdb104c5335a70cfde3207e8fdb`) re-rendered structured diagnostics through `miette`.

---

### End-to-End Source Correspondence Across Charon, Aeneas, Lean, and Historical Anneal V1

#### Four-tier correspondence taxonomy and historical V1 byte-range sidecar

Basis: **source** + **derived** (`source-map.json`).

| Correspondence Tier | Upstream / Anneal Mechanism | Pinned Source / Artifact Evidence | Granularity & Boundary |
| --- | --- | --- | --- |
| **1. Semantic item identity** | Charon typed item IDs and crate maps | `charon/src/ast/krate.rs` (`fabd29106ded9cc2116ce508cbae7ccfbaef4070`) | Intra-crate reference graph; numeric IDs are not guaranteed stable across independent runs. |
| **2. Human-recognizable Rust source identity** | Structured `Name` paths and `ItemMeta` (`Span` + optional `generated_from_span`) | `charon/src/ast/names.rs` (`30441a758993d4f8f280702d175a2a6c7dc574b9`), `meta.rs` (`7a80a92ea1b3f3eaff1758554001e32019473237`) | Item-level Rust path and span; `generated_from_span` records single-hop macro origin, not full hygiene trees. |
| **3. Generated-declaration provenance** | Aeneas carries `item_meta` into `Pure.ml` (`Translate.ml`) and emits Lean doc comments (`extract_fun_comment`, `extract_comment_with_span`) | `Pure.ml` (`acde8579d6861a08efae086c72f3156283110342`), `Translate.ml` (`8376e580b542bf3ee28cc9e3d4c170a17b23d379`), `ExtractBase.ml` (`4fc8a3f35643ba66555f0889790d50993feef1b9`), `ExtractTypes.ml` (`371717638f4298cc9c488b31a597608f9bf5089c`), `Extract.ml` (`52754e4fdb25b50fce63abe2d2184751d69632e8`), `tests/lean/NoNestedBorrows.lean` (`e2a706b744e2e9a105e305cf8a2b353354209dae`) | Links generated Lean `def choose` to `[no_nested_borrows::choose]` at `tests/src/no_nested_borrows.rs`, lines `200:0-206:1`; also annotates loop helpers (`loop_id`) and termination templates with the parent function's span. |
| **4. Generated-range to Rust-range provenance** | Lean diagnostics (`Message.lean`, `InteractiveDiagnostic.lean` blob `5fc9e0b22a3195c7843f7a45b7c0bdab870fce08`, `FileWorker.lean` blob `c803034ed8810f13a5ef38a603a21e610efca2bc`, `ProtocolOverview.lean` blob `4f493fc900319113e00a0a9c0f5eac4c3e5bb8e5`) point into Lean only; historical Anneal V1 built an explicit `SourceMapping` byte-range sidecar | `anneal/v1/src/generate.rs` (`f087023d08011a90d56bcbdc759e6cbc90c344b5`), `anneal/v1/src/aeneas.rs` (`9b4618a20938315afc290744bbdfa498848620f4`), `anneal/DESIGN.md` (`0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`), `anneal/PRINCIPLES.md` (`d5339a95254eae14ac201139d07d9d36d48a19fb`) | Upstream Aeneas does not emit a token/expression byte map; V1 recorded `(lean_start..lean_end, rust_file, rust_start..rust_end, MappingKind::{Source, Synthetic, Keyword})` and intersected diagnostic ranges in `resolve_mapping`. |

Furthermore, pre-Lean failures in Charon or Aeneas (`Translate.translate_function_to_pure` catching `CFailure` and logging the Rust/LLBC span before returning `None`) never reach the generated Lean document, and build-script-generated `include!` files (which have real filesystem spans) differ in provenance from procedural-macro tokens (whose spans reflect macro-assigned call-site or definition-site hygiene).

## Boundaries

- **Source-grounded analysis without fresh tool execution:** No fresh `rustc`, Charon, Aeneas, Lean, Lake, or LSP process was executed in this investigation; `tests/lean/NoNestedBorrows.lean` is inspected as a checked-in upstream artifact at `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.
- **Downstream `annotate-snippets` behavior on malformed Charon byte ranges:** While source inspection of `Loc::to_byte` and `SpanData::to_byte_range` proves that Charon computes wrong or mid-character byte offsets after multibyte UTF-8 characters, combining marks, or tabs, the exact runtime behavior of `annotate-snippets 0.12.12` (panic, clipping, or shifted underline) on each malformed range requires an execution probe.
- **Unstable JSON schemas:** `rustc`'s `--error-format=json` and Lean's `lean --json` (`SerialMessage`) have no cross-version stability guarantee; consumers must pin exact tool revisions and parse structured fields rather than `rendered` or `data` prose.
- **Undecided Anneal V2 source-mapping architecture:** Historical Anneal V1's `SourceMapping` sidecar demonstrates feasibility for Anneal-generated Lean, but current `anneal/DESIGN.md` leaves V2's source/model correspondence and obligation-coverage mechanism open.

## Evidence

- **Path normalization and relocation (`support/cross-tool-diagnostic-path-normalization/`):**
  - `path-policy-matrix.json`, `support/cross-tool-diagnostic-path-normalization/path-policy-matrix.json`, and `support/cross-tool-diagnostic-path-normalization/source-map.json`.
- **Multibyte UTF-8 span and column units (`support/cross-tool-utf8-span-columns/`):**
  - `coordinate-matrix.json`, `support/cross-tool-utf8-span-columns/coordinate-matrix.json`, and `support/cross-tool-utf8-span-columns/source-map.json`.
- **Diagnostic width and format controls (`support/diagnostic-format-controls-v4-30-0-rc2/`):**
  - `diagnostic-format-matrix.json`, `support/diagnostic-format-controls-v4-30-0-rc2/diagnostic-format-matrix.json`, and `support/diagnostic-format-controls-v4-30-0-rc2/source-map.json`.
- **Top-level merged source map:**
  - `source-map.json`.

## Revalidation

1. **Path normalization and relocation matrix:** Compile one local crate file, one `$CARGO_HOME` dependency, and one Rust sysroot file under two distinct workspace roots (`root-A` and `root-B`) with no remap, with `--remap-path-prefix=<root>=/src`, and with scope-restricted `--remap-path-scope=diagnostics` vs `macro`. Verify that `rustc` JSON `file_name` follows `DIAGNOSTICS` while Charon `translate_filename` prefers `local_path()` when present and `MACRO` when absent. On the Lean side, run `lean --json`, `lake build`, and Lean LSP `publishDiagnostics` across two roots and verify direct CLI path preservation, Lake package-relative rewriting (`mkRelPathString relLeanFile`), and LSP `DocumentUri` symlink resolution.
2. **Multibyte UTF-8 coordinate and `Loc::to_byte` regression suite:** Place a diagnostic target after six prefixes on otherwise identical lines—ASCII `abc`, 2-byte BMP `é`, 3-byte wide BMP `界`, 4-byte supplementary emoji `😀` (`U+1F600`), combining sequence `a` + `U+0301`, and `\t`—and compare `rustc` JSON `byte_start`/`byte_end` and 1-based scalar columns, Charon serialized `Loc.col` and `Loc::to_byte`, Aeneas `line:col`, Lean batch `--json` `Position`, and Lean LSP UTF-16 `Position`. Assert that any byte-slicing offset lands on a valid UTF-8 scalar boundary matching `rustc`'s `byte_start`/`byte_end`.
3. **Diagnostic width and format controls:** Run `rustc` on a long-type error under two terminal widths without `--diagnostic-width` and with `--diagnostic-width=100` / `--diagnostic-width=140`, comparing structured JSON fields separately from `rendered`. Run `lean --json` on a wrapping diagnostic with default options and with `-Dformat.width=60` / `-Dformat.inputWidth=60` to confirm whether `Message.serialize` still uses fixed `Std.Format.defWidth = 120`.
4. **End-to-end source correspondence:** Diff `ast/meta.rs` and `translate_meta.rs` in Charon, `Pure.ml`, `Translate.ml`, `ExtractTypes.ml`, `Extract.ml`, and `Errors.ml` in Aeneas, and `Message.lean`, `InteractiveDiagnostic.lean`, and `FileWorker.lean` in Lean when upgrading pins, and verify that `tests/lean/NoNestedBorrows.lean` (or its successor golden) retains item-level Rust name and span comments.
