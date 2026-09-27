# Stable diagnostic width and format controls in the Anneal toolchain

## Summary

The Anneal-selected Rust and Lean toolchains expose very different notions of “stable diagnostic formatting.”

For `rustc` at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`nightly-2026-05-31`), human-readable diagnostics are **not width-stable by default**. `Session::diagnostic_width()` uses an explicit `--diagnostic-width` when supplied, otherwise fixes the width to 140 in rustc UI-testing mode, and otherwise asks the terminal for its dimensions with 140 as a fallback. The width is not merely cosmetic: compiler error-reporting code also consults it when deciding whether to abbreviate or externalize long type descriptions. A reproducible human-diagnostic specimen must therefore pin `--diagnostic-width`, not just capture output in a nominally similar terminal.

Rustc also has a substantially stronger machine-facing surface: `--error-format=json`. At this pin, each JSON diagnostic carries structured message, code, level, spans, children, suggestions, and a `rendered` human-readable string. The structured fields avoid terminal wrapping, but `rendered` is produced by the normal diagnostic renderer with the configured diagnostic width. The rustc source explicitly calls the JSON format unstable. For correctness-sensitive automation, treat the exact rustc revision and structured fields as the compatibility boundary; do not parse `rendered` prose. If exact rendered bytes matter, additionally pin width and the JSON rendering options.

Charon 0.1.210 can forward arbitrary extra rustc arguments through repeatable `--rustc-arg` values. Those flags are appended to selected rustc invocations by `charon-driver`, so an Anneal invocation can in principle force rustc's width and output format. That does **not** stabilize Charon-native diagnostics. Charon's own `ErrorCtx` renders errors separately through `annotate-snippets`' styled renderer and writes them to stderr; the inspected Charon option model contains rustc pass-through plus warning/error policy, but no Charon-native diagnostic-width or machine-JSON switch. Rustc formatting controls and Charon formatting controls are therefore separate surfaces.

Lean `v4.30.0-rc2` is different again. The batch `lean --json` interface supplies a machine-readable JSON-lines envelope, but the `data` field is already rendered human-facing text. At this exact revision, the normal `Message.serialize` path converts `MessageData` to `Format`, then uses the ordinary `ToString Format` instance, whose renderer uses `Std.Format.defWidth = 120`. That final conversion does not consult the registered `format.width` option. Lean does expose `format.width` for callers that explicitly render with options, and `format.inputWidth` for suggestion/edit text, but neither source path establishes `-Dformat.width=...` as a control over ordinary batch diagnostic serialization. In other words, the batch JSON diagnostic body is source-defined around a 120-column default at this revision, not terminal-width auto-detection and not a documented CLI diagnostic-width knob.

The practical rule for Anneal is to separate **semantic diagnostic data** from **rendered presentation**. Use structured rustc JSON fields and Lean JSON fields for machine decisions; pin exact tool revisions; treat human text as revision-coupled presentation; and, where golden rendered output is still useful, explicitly pin every available width/color mode and record the surfaces that cannot be pinned. Current Anneal V2 already executes `lean --json` in its archive-consumption integration test, which aligns with that model. It should not infer a cross-tool “one width setting” that does not exist.

No fresh rustc, Charon, or Lean executable was run for this report. The conclusions below are exact-source results. Runtime specimens remain valuable for byte-level golden tests, especially for Charon-native rendering and for confirming rustc JSON bytes under chosen flags.

## Applicability

This report covers the diagnostic width and format controls relevant to the currently selected Anneal toolchain:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler revision behind the Charon toolchain used by the pinned Aeneas release;
- `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, version `0.1.210`;
- `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, version `v4.30.0-rc2`; and
- current Anneal authority `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` only where needed to establish how these surfaces are presently consumed.

The report answers four questions:

1. what makes rendered diagnostics change width or format;
2. what explicit controls exist at the exact selected revisions;
3. which machine-readable outputs remain coupled to rendered prose; and
4. which settings are actually shared across the Charon/rustc and Lean layers.

It does not attempt to define a stable prose grammar for any compiler message. It also does not replace the existing reports on Lean's JSON schema, diagnostic object model, source correspondence, Charon source spans, or Lean pretty-printing round trips. Those reports establish the structured data being rendered. This report focuses on layout/format controls and their limits.

A “stable” control here means an explicit source-defined input that removes one environmental source of output variation at the pinned revision. It does not mean an upstream compatibility promise across tool versions.

## Findings

### Rustc human diagnostics inherit terminal width unless `--diagnostic-width` is explicit

Rustc exposes a stable command-line option:

```text
--diagnostic-width <WIDTH>
```

The pinned option table describes it as informing rustc of the output width so diagnostics can be truncated to fit.

The operative behavior is in `Session::diagnostic_width()`:

1. if `opts.diagnostic_width` is present, return that value;
2. otherwise, if `-Zui-testing` is active, return 140;
3. otherwise, ask `termize::dimensions()` for the terminal width;
4. if dimensions are unavailable, return 140.

Thus redirecting output, changing the pseudo-terminal, or running under a different automation host can change human output when the explicit option is absent. The 140-column fallback should not be mistaken for the universal default: it is used only when no explicit width exists and terminal dimensions are unavailable, or in rustc's own UI-testing mode.

Basis: **source** in pinned `compiler/rustc_session/src/config.rs` and `compiler/rustc_session/src/session.rs`.

### Rustc diagnostic width can change message content, not only wrapping

The width accessor is consumed outside the final renderer. At the pinned compiler revision, type-error reporting uses `Session::diagnostic_width()` to choose length limits for displayed type material, and trait error reporting similarly compares explanation lengths against the diagnostic width.

That means two runs with different widths can differ in more than line breaks or caret placement. A long type or explanation can cross a threshold that changes which representation is printed.

For golden diagnostics, “same source + same compiler revision” is therefore insufficient if the width remains environment-derived. Pinning `--diagnostic-width` removes a semantic presentation input as well as a layout input.

Basis: **source** in the pinned rustc session interface and error-reporting callers. The recommendation to pin width is **derived**.

### Rustc JSON separates structured diagnostic data from a width-sensitive rendered copy

`--error-format=json` selects rustc's `JsonEmitter`. The emitter serializes one JSON value and appends a newline. At this revision a diagnostic object contains, among other fields:

- `message`;
- optional `code`;
- `level`;
- structured `spans`;
- nested `children`; and
- optional `rendered`.

The `rendered` field is not an independent stable representation. `Diagnostic::from_errors_diagnostic` constructs an `AnnotateSnippetEmitter` and passes through `je.diagnostic_width`, along with short/unicode/color configuration, then stores the resulting buffer in `rendered`.

The structured span fields are produced separately from this rendering step. Width changes therefore do not require a consumer to re-parse different line wrapping if it relies on `spans`, `message`, `children`, and other structural fields. Width still matters if a test snapshots the `rendered` field.

The source header explicitly says the JSON format should be considered unstable and points readers to the implementation structs as the current specification. Exact rustc revision is therefore part of any durable machine contract.

Basis: **source** in pinned `compiler/rustc_errors/src/json.rs`.

### Rustc's JSON and color controls have distinct interactions

The pinned CLI exposes `--error-format`, `--json`, `--color`, and `--diagnostic-width` independently, but their accepted combinations are constrained.

`--error-format=json` selects compact JSON. `--error-format=pretty-json` selects indented JSON and is gated as unstable. `--json` suboptions configure material embedded in JSON; relevant diagnostic suboptions include `diagnostic-short`, `diagnostic-unicode`, and `diagnostic-rendered-ansi`.

The parser rejects combining ordinary `--color` with `--json`. ANSI rendering inside the JSON `rendered` field is instead requested through `--json=diagnostic-rendered-ansi`. Without that suboption, the JSON-rendered human string uses the non-ANSI configuration.

A stable machine consumer should therefore distinguish:

- the JSON serialization whitespace (`json` versus `pretty-json`);
- the structured diagnostic fields;
- the human-readable `rendered` field;
- whether that rendered field uses short/unicode mode;
- whether ANSI escapes are explicitly embedded; and
- the diagnostic width used by the embedded renderer.

Basis: **source** in pinned `compiler/rustc_session/src/config.rs` and `compiler/rustc_errors/src/json.rs`.

### Charon can forward rustc formatting controls to selected compiler invocations

Charon 0.1.210's `CliOpts` contains repeatable `rustc_args`, exposed as `--rustc-arg`. In a selected translation invocation, `charon-driver` deserializes Charon options from `CHARON_ARGS` and appends each `rustc_args` entry to the compiler argument vector before invoking rustc.

Therefore rustc controls such as `--diagnostic-width=<N>` can be transported through Charon without a Charon-specific implementation of that flag. In direct `charon rustc` mode, trailing rustc arguments are another compiler-argument channel; in `charon cargo` mode, Charon's `--rustc-arg` remains the direct selected-rustc channel while trailing arguments configure Cargo.

This statement is about routing, not compatibility of every possible rustc flag with Charon. In particular, switching rustc to JSON output can change the bytes Charon and its caller observe and should be tested before it becomes part of an Anneal protocol.

Basis: **source** in pinned `charon/src/options.rs` and `charon/src/bin/charon-driver/driver.rs`, plus the current corpus's exact-pin Charon CLI routing report.

### Rustc controls do not stabilize Charon-native errors

Charon also generates errors that are not rustc diagnostics. Its `ErrorCtx` and `Error` rendering path builds `annotate-snippets` groups, renders them through `Renderer::styled()`, and writes the resulting message through `anstream::eprintln!`. Unspanned errors use the same styled renderer.

The inspected `CliOpts` exposes rustc pass-through arguments, `abort_on_error`, and `error_on_warnings`, but no Charon-native diagnostic width or structured diagnostic format setting. Consequently, forwarding `--diagnostic-width` changes rustc's diagnostic behavior but does not establish a width contract for Charon's own rendered messages.

This distinction is important for cross-tool golden specimens. A fixture that contains both a rustc type error and a Charon translation error can still have two independent presentation surfaces even when the rustc side is fully pinned.

Basis: **source** in pinned `charon/src/errors.rs`, `charon/src/options.rs`, and `charon/src/bin/charon-driver/driver.rs`.

### Lean's generic `Format` renderer has a fixed default width of 120

At Lean `v4.30.0-rc2`, `Std.Format.defWidth` is 120. `Format.pretty` accepts an explicit width but defaults to `defWidth`. The global `ToString Format` instance renders a format simply by calling `f.pretty`, which therefore uses 120 unless the caller explicitly invokes another rendering function with a width.

Lean also registers `format.width` as an option and provides `Std.Format.pretty'`, which renders using `format.width` from an `Options` value. The existence of that option does **not** imply every format-to-string conversion consults it.

Basis: **source** in pinned `src/Init/Data/Format/Basic.lean`, `src/Init/Data/ToString/Basic.lean`, and `src/Lean/Data/Format.lean`.

### Ordinary Lean batch diagnostic serialization does not use `format.width`

The batch diagnostic path is especially relevant to Anneal because current V2 tests already execute:

```text
lake ... env lean --json generated/Generated.lean
```

For each message, Lean's batch reporter eventually calls `Message.toJson`. `Message.toJson` calls `Message.serialize`; `Message.serialize` replaces structured `MessageData` with `msg.data.toString`; and `MessageData.toString` formats the `MessageData` to a `Format` and then applies ordinary `toString` to that `Format`.

The final step therefore goes through the global `ToString Format` instance described above: `f.pretty` with its default 120-column width. The source path does not pass `MessageDataContext.opts` to `Format.pretty'`, nor does it read `format.width` at that final layout step.

This establishes a precise negative result for the selected revision: although `lean -Dformat.width=...` can set the registered option for code that chooses to read it, the ordinary `Message.serialize` / `lean --json` diagnostic body is **not source-defined to use that option as its final rendering width**.

The message's structured context still matters before final layout. `MessageData` can carry an environment, metavariable context, local context, and options that affect delaboration and pretty-printer choices. The negative result is specifically about final `Format` line width.

Basis: **source** in pinned `src/Lean/Message.lean`, `src/Init/Data/ToString/Basic.lean`, `src/Init/Data/Format/Basic.lean`, and `src/Lean/Data/Format.lean`.

### Lean `--json` stabilizes framing, not diagnostic prose

Lean's `--json` batch mode emits each non-silent diagnostic as compact JSON on one stdout line. The on-wire `SerialMessage` preserves machine fields such as file name, positions, severity, caption, and message kind, but its `data` field is the eager string produced by `Message.serialize`.

Thus the JSON framing removes ambiguity about line-oriented message objects, but it does not make the diagnostic body a semantic protocol. The rendered `data` text remains subject to the exact Lean revision, message producers, pretty-printer choices, and the 120-column final `Format` renderer described above.

The existing `lean-json-cli-protocol-v4-30-0-rc2` report establishes the full schema and the fact that the stream has no protocol-version field. This report adds the width consequence: parsing the `data` prose is both revision-sensitive and presentation-sensitive; machine decisions should use the structural JSON fields where possible.

Basis: **source** in pinned `src/Lean/Language/Basic.lean` and `src/Lean/Message.lean`; schema details are also covered by the existing native report.

### `format.inputWidth` controls generated suggestion/edit text, not batch message width

Lean separately registers `format.inputWidth`, default 100, in `Lean.Meta.TryThis`. It exists for output intended to be copied back into a Lean source file. `SuggestionText.prettyExtra` uses that width when no explicit width is supplied, together with the edit's indentation and source column.

This is a separate formatting surface from diagnostic serialization. A code action or “try this” suggestion can therefore have width behavior controlled by `format.inputWidth` even while the containing batch diagnostic message is ultimately serialized with the default `Format` width.

Tests that compare Lean diagnostics containing edits or suggestions should record both concerns rather than treating one option as a universal formatting width.

Basis: **source** in pinned `src/Lean/Meta/TryThis.lean`.

### Lean batch diagnostics do not depend on terminal-width detection in this path

Unlike rustc's `Session::diagnostic_width()`, the inspected Lean `Message.serialize` path does not query terminal dimensions. Its final generic `Format` conversion has the fixed default width of 120.

This means changing TTY geometry alone is not expected, from this source path, to reflow ordinary serialized `MessageData`. That is a narrower claim than “all Lean output is width-stable.” Raw process output, custom plugins, `IO.print`, preformatted strings, Lake progress output, language-server clients, and code that explicitly renders `Format` with another width remain separate surfaces.

Basis: **source** in the pinned Lean formatting and message serialization implementations; the exclusion list is a **scope boundary**.

### There is no cross-tool width knob

The exact selected tools expose three materially different mechanisms:

| Surface | Default width behavior | Explicit width control | Machine format |
| --- | --- | --- | --- |
| rustc human diagnostic | terminal width, else 140; 140 in UI-testing mode | `--diagnostic-width <N>` | no |
| rustc JSON `rendered` field | same rustc diagnostic width | `--diagnostic-width <N>` | surrounding diagnostic is JSON |
| Charon-native error renderer | Charon calls its own styled renderer | no Charon-native width control found in inspected `CliOpts` | no Charon-native JSON diagnostic mode found |
| Lean batch `Message` text / JSON `data` | generic `Format.pretty` default 120 at this pin | no final-layout diagnostic-width control established; `format.width` is not used by this path | `lean --json` wraps the rendered data in `SerialMessage` JSON |
| Lean suggestion/edit text | `format.inputWidth` default 100 | `format.inputWidth` / explicit `Suggestion.pretty` width | carried inside higher-level diagnostic/editor structures |

The values 140, 120, and 100 are not intended to match. They arise from different libraries and purposes. Choosing the same numeric value where a tool permits it does not create a shared formatting protocol.

### Stable goldens should separate structured evidence from presentation evidence

The source above supports a two-layer testing model.

For **semantic/machine evidence**:

- preserve exact rustc JSON objects and consume structured fields rather than `rendered`;
- preserve exact Lean `SerialMessage` objects and consume file/position/severity/kind fields rather than parsing `data`;
- preserve Charon's structured LLBC/span data separately from Charon-native stderr prose;
- pin the exact tool revisions and the invocation flags that select the serialization path.

For **presentation/golden evidence**:

- pin rustc `--diagnostic-width`;
- pin rustc JSON rendering suboptions if `rendered` is included;
- pin color/ANSI policy;
- record that Charon-native layout lacks an equivalent source-defined width knob at this revision;
- record Lean's fixed default diagnostic layout behavior rather than pretending `format.width` is a supported batch-diagnostic knob; and
- keep suggestion/edit width tests distinct from message-body width tests.

This design makes an expected textual diff useful without allowing wrapping changes to masquerade as semantic diagnostic changes.

The recommendation is **derived** from the exact source controls above.

### Current Anneal V2 already exercises Lean's machine-oriented batch surface

At current Anneal authority `41f5b37afe7060fd9fe08c00b200672cd76d77b9`, the archive reuse integration test runs Lean as:

```text
lake --keep-toolchain env lean --json generated/Generated.lean
```

That invocation is currently a build/archive consumption test rather than an implemented end-user diagnostic pipeline. Still, it confirms that the V2 environment already treats `lean --json` as a relevant supported execution surface.

Current V2 has not yet reproduced V1's full diagnostic-mapping/rendering pipeline, so this report should be read as input to that future implementation rather than as documentation of an already-finalized V2 user interface.

Basis: **source** in current `anneal/src/main.rs`; the implementation-status statement follows the current V2 source tree and design state.

## Boundaries

**No fresh execution.** This report did not run rustc, Charon, Lean, Cargo, Lake, or Anneal. It establishes exact source-defined controls and identifies the runtime specimens still worth capturing.

**Rustc JSON is revision-coupled.** The rustc source itself says the JSON format is unstable. The report does not promote it into a cross-version protocol.

**Charon-native rendering is not exhaustively characterized below `annotate-snippets`.** The report establishes that Charon uses `Renderer::styled()` without a Charon-native width option in the inspected option surface. It does not derive undocumented renderer behavior from a different `annotate-snippets` revision. A byte-level Charon golden still needs an exact execution probe.

**Cargo presentation is not a separate subject here.** Charon Cargo mode can interpose Cargo around rustc and Cargo has its own progress/message surfaces. This report focuses on compiler diagnostics and Charon-native diagnostics, not every Cargo terminal line. If Anneal needs Cargo's `--message-format` or terminal-width semantics as a public protocol, that deserves its own exact-pin report.

**Aeneas-native OCaml diagnostics are not claimed stable.** Aeneas extraction warnings/errors are outside the specific width-control source paths established here. Their machine/prose contract should not be inferred from rustc, Charon, or Lean.

**Lean's fixed 120-column result is path-specific.** It applies to ordinary `MessageData.toString` serialization at this revision. Plugins or message producers can embed preformatted strings/newlines, and other Lean APIs can call `Format.pretty` with explicit widths or `Format.pretty'` with `format.width`.

**`format.width` is not declared useless.** It is a real Lean option used by callers that choose it. The negative result is only that ordinary batch `Message.serialize` does not use it for final layout.

**The report does not claim byte-level reproducibility.** File paths, source text, message ordering, hash-generated names, Unicode choices, compiler behavior, and other inputs can still change diagnostic bytes even after width and color are pinned.

**Miette/Anneal-owned final rendering is separate.** Historical Anneal V1 converted some external structured diagnostics into its own `miette` presentation. Stabilizing that final UI requires Anneal-owned rendering controls in addition to the upstream controls documented here.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

### Rust compiler

Subject: `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `compiler/rustc_session/src/config.rs`, blob `e82f67eac5e9f7d0b089727e6317d77242ba3b1c`
  - stable `--diagnostic-width`, `--error-format`, `--json`, and `--color` option declarations;
  - diagnostic-width parsing;
  - `parse_json`;
  - `parse_error_format`;
  - JSON/color compatibility checks.
- `compiler/rustc_session/src/session.rs`, blob `c83bb62324e76a0686515782d3290961d655dd3d`
  - `Session::diagnostic_width()` terminal/UI-testing/explicit-width behavior.
- `compiler/rustc_errors/src/json.rs`, blob `04ac140f332618d6fa81254e9a16bc27c729eef5`
  - exact JSON diagnostic structs;
  - explicit instability notice;
  - newline-delimited JSON emission;
  - construction of `rendered` using `AnnotateSnippetEmitter` with `diagnostic_width`.
- `compiler/rustc_errors/src/annotate_snippet_emitter_writer.rs`, blob `c3c9f26c31571596875822ae7227d51dfb34f16b`
  - human diagnostic emitter's width field and renderer integration.

The additional conclusion that width can affect message content rather than only final line wrapping was revalidated against exact-pin error-reporting callers of `Session::diagnostic_width()`.

### Charon

Subject: `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`).

- `charon/src/options.rs`, blob `f08f8bae08d7fb5f38773c0be038d925fe80cb4c`
  - repeatable `--rustc-arg`;
  - Charon warning/error policy;
  - absence of a Charon-native width/JSON diagnostic option in the inspected CLI option model.
- `charon/src/bin/charon-driver/driver.rs`, blob `3f90a7a31857aed462694066e5ffaa6e28b9dcfa`
  - appending `rustc_args` to selected compiler invocations.
- `charon/src/errors.rs`, blob `e4107c6deb5741d523d2220820d1ee0355adb3c0`
  - Charon-native `annotate-snippets` rendering and stderr output.
- `charon/Cargo.lock`, blob `b623c6c4c3558f441ec2bc5281cec61080126c0c`
  - Charon resolves `annotate-snippets` 0.12.12 and `anstream` 0.6.20.

The current native report `charon-cli-invocation-modes-0-1-210` was used to preserve the already-established distinction between Charon's forwarded underlying-tool arguments and `--rustc-arg`.

### Lean

Subject: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

- `src/Init/Data/Format/Basic.lean`, blob `e0dbb5fa8be5578f8904e0e5a36decbcdf3fbec4`
  - `Std.Format.defWidth = 120`;
  - `Format.pretty` explicit/default width.
- `src/Init/Data/ToString/Basic.lean`, blob `505aa15ca363d66f70f850134b008d98c93df184`
  - `ToString Format` delegates to `f.pretty`.
- `src/Lean/Data/Format.lean`, blob `9bcb44e2ce7c6848dd1f1d7a3f2801ccc54b4f42`
  - registered `format.width`;
  - `Format.pretty'` as the option-reading renderer.
- `src/Lean/Message.lean`, blob `a7f76198c582d1d2032bb24d13ad4cb7a272fa57`
  - `MessageData.format` / `MessageData.toString`;
  - `Message.serialize`;
  - `Message.toJson`;
  - `SerialMessage`.
- `src/Lean/Language/Basic.lean`, blob `08f9b688fc869224c316175220403c2aeb5eb415`
  - batch message reporting;
  - compact JSON-lines emission.
- `src/Lean/Shell.lean`, blob `2ff5c4b0c82f876ddd4384c9c20dcaefebc1b90e`
  - `--json`;
  - `-D` option handling and frontend invocation.
- `src/Lean/Meta/TryThis.lean`, blob `b54e1160df2aa69c282941fbc673d99e5eef708d`
  - `format.inputWidth = 100`;
  - suggestion/edit width handling.

Current native reports `lean-json-cli-protocol-v4-30-0-rc2`, `lean-diagnostic-objects-severity-v4-30-0-rc2`, and `lean-pretty-printing-roundtrip-v4-30-0-rc2` were used to maintain scope boundaries.

### Anneal applicability

Subject: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

- `anneal/src/main.rs`, blob `b947700606677ea89c7a205f3ffcc75493508f63`
  - current V2 archive-reuse integration path invokes `lake ... env lean --json`.
- `anneal/v1/src/diagnostics.rs`, blob `cd27b771e2f22bdb104c5335a70cfde3207e8fdb`
  - historical evidence that V1 re-rendered external structured diagnostics with Anneal-owned `miette` presentation; used only as a boundary, not as current V2 authority.

Evidence roles are **source** and **derived synthesis**. There is no fresh **execution** evidence.

## Revalidation

When any selected tool revision changes, revalidate the controls independently rather than assuming they evolved together.

For **rustc**:

1. inspect the CLI option declarations and parsers for `--diagnostic-width`, `--error-format`, `--json`, and `--color`;
2. inspect `Session::diagnostic_width()` for terminal/default/UI-testing behavior;
3. search every caller of `diagnostic_width()` to see whether width still changes content-selection decisions;
4. inspect the JSON diagnostic structs and the code that builds `rendered`;
5. confirm whether the source still labels JSON as unstable; and
6. run one fixture under at least two terminal widths, then repeat with a fixed `--diagnostic-width`.

The runtime fixture should preserve structured JSON and compare it separately from `rendered`. Include a deliberately long type/error so the probe can distinguish pure reflow from width-dependent content changes.

For **Charon**:

1. re-read `CliOpts` for newly added diagnostic/width/color/JSON controls;
2. confirm that `rustc_args` still reaches selected compiler invocations;
3. inspect `errors.rs` for the Charon-native renderer and output destination;
4. capture one rustc-originated error and one Charon-native translation error under the same invocation; and
5. vary terminal width and explicit rustc width independently.

This will establish whether future Charon versions acquire their own width control and whether its native renderer is byte-stable under non-TTY execution.

For **Lean**:

1. re-read `Std.Format.defWidth`, `ToString Format`, and `Lean.Data.Format`;
2. trace `Message.toJson` → `Message.serialize` → `MessageData.toString` all the way to the final string renderer;
3. check whether that path begins reading `format.width`, a terminal width, or another option;
4. re-read `format.inputWidth` for suggestion/edit behavior; and
5. execute a diagnostic containing grouped `Format.line` opportunities long enough to wrap.

Run that Lean fixture with the default options and with widely different `-Dformat.width=...` values. If source remains as described here, ordinary batch diagnostic `data` should retain the final default-width layout while APIs that explicitly read `format.width` may change. Preserve stdout JSON lines, stderr, and process status.

For **Anneal**, keep semantic and rendered specimens separate. A useful cross-tool golden suite should include:

- one rustc error emitted as structured JSON at a fixed width;
- the same rustc error at a second width to expose width-sensitive fields;
- one Charon-native translation error;
- one Lean batch JSON error with enough grouped content to wrap;
- one Lean suggestion/edit whose `format.inputWidth` is varied; and
- exact source/tool revisions and invocation environments for every specimen.

A passing suite should compare structured machine fields with structural assertions and presentation bytes with explicitly declared formatting inputs. It should not require unrelated tools to share the same width number merely for visual uniformity.
