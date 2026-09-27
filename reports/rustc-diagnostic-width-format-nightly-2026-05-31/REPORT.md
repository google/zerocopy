# rustc diagnostic width and output-format controls at nightly-2026-05-31

## Summary

At `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`nightly-2026-05-31`), rustc provides a stable command-line control, `--diagnostic-width=<N>`, that directly fixes the width used by its diagnostic renderer. The explicit value takes precedence over terminal-size discovery. The same value is passed into the renderer that populates the `rendered` field of JSON diagnostics, so it is the right control when a test needs stable wrapping in either human output or JSON's embedded human rendering.

Width is not merely presentation state at this revision. Compiler error-reporting code also calls `Session::diagnostic_width()` when deciding how aggressively to shorten long type names and, in at least one trait-error path, whether explanatory text belongs in a span label or a separate `help` child. A golden-diagnostic harness that wants reproducible structure as well as reproducible wrapping should therefore set `--diagnostic-width` even if it ignores JSON's `rendered` string.

For stable human-oriented output, the useful control set is `--diagnostic-width=<N>`, an explicit `--error-format=human` or `short`, and `--color=never`. For machine-oriented output, use ordinary `--error-format=json`; `--json=diagnostic-short` changes the embedded human rendering, while `--json=diagnostic-rendered-ansi` explicitly opts that rendering into ANSI color. `--json` requires JSON error format and cannot be combined with `--color`.

These controls stabilize selected dimensions of output, not the diagnostic protocol across compiler releases. rustc's own JSON emitter states that the JSON format is unstable, and the rustc book tells consumers to parse forwards-compatibly because fields and enumerated values may be added. The current structured fields are a better machine interface than rendered text, but their schema is still revision-sensitive.

The current zerocopy UI harness independently encodes the same operational lesson: it pins `--diagnostic-width=100` because `TERM` and `COLUMNS` are not reliable enough to control rustc's wrapping by themselves. This is downstream corroboration of how the explicit width flag is used, not an upstream compatibility promise.

No fresh rustc execution was performed for this report. The evidence is exact-revision rustc documentation/source, checked-in rustc UI fixtures, and current zerocopy harness source.

## Applicability

The rustc findings apply to:

- repository: `rust-lang/rust`;
- revision: `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`;
- selected toolchain date: `nightly-2026-05-31`;
- compiler diagnostic modes: human, short, and ordinary JSON output;
- diagnostic rendering through the current `AnnotateSnippetEmitter` and `JsonEmitter` paths.

The zerocopy observation applies to `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, specifically `tools/ui-runner/src/main.rs`.

This report uses **stable control** to mean a command-line option that rustc marks stable at the exact pin. It does not mean that the bytes emitted under that option are a stable cross-version interface. `--error-format=json`, `--json`, `--color`, and `--diagnostic-width` are registered as stable command-line options, while particular JSON fields and diagnostic wording remain revision-sensitive.

The report is about rustc. It does not infer that Lean, Charon, Aeneas, Cargo, or another diagnostic producer accepts the same controls or has the same stability contract. Cargo can transport rustc JSON, but Cargo's message protocol is a separate subject.

## Findings

### `--diagnostic-width` bypasses terminal-width discovery

rustc registers `--diagnostic-width` as a stable option. The rustc book describes it as the terminal width, in characters, that diagnostic formatting should take into account.

The implementation stores the parsed value in `Options.diagnostic_width`. When compiler error-reporting code asks `Session::diagnostic_width()`, rustc returns that explicit value first. Without it, UI-testing mode uses a fixed width of 140; otherwise rustc asks `termize` for terminal dimensions and falls back to 140 when dimensions are unavailable.

The human renderer has the same precedence. `AnnotateSnippetEmitter::renderer` uses its explicit `diagnostic_width` when present; only otherwise does it use UI-testing/default behavior or terminal-dimension discovery. It then passes the chosen width to `annotate_snippets::Renderer::term_width`.

An explicit flag therefore removes terminal discovery from both the compiler's width-dependent diagnostic decisions and its human renderer.

Basis: **documentation + source** in `src/doc/rustc/src/command-line-arguments.md`, `compiler/rustc_session/src/config.rs`, `compiler/rustc_session/src/session.rs`, and `compiler/rustc_errors/src/annotate_snippet_emitter_writer.rs`.

### Width can change diagnostic structure, not only line wrapping

At this revision, `Session::diagnostic_width()` participates in error construction before final rendering.

`TyCtxt::short_string` and related type-description paths derive length limits from the diagnostic width. Long expected/found types can therefore be shortened according to the configured width, and with `-Zwrite-long-types-to-disk=yes` rustc may move the full spelling into a `long-type-<hash>.txt` file.

A trait-fulfillment diagnostic has a more structural example. It compares an explanation's length to `diagnostic_width()`. If the explanation is long, rustc emits a generic `unsatisfied trait bound` span label and moves the explanation into a `help` diagnostic; otherwise the explanation itself remains the span label. The source comment explicitly notes the JSON position consequence.

A consumer that compares structured JSON should therefore fix width even if it discards the `rendered` field. Otherwise terminal width can affect message text, label placement, child diagnostics, and long-type handling in addition to visual wrapping.

Basis: **source** in `compiler/rustc_middle/src/ty/error.rs`, `compiler/rustc_trait_selection/src/error_reporting/infer/mod.rs`, and `compiler/rustc_trait_selection/src/error_reporting/traits/fulfillment_errors.rs`.

### JSON's `rendered` field uses the same explicit width

`--error-format=json` selects `JsonEmitter`. That emitter builds a structured `Diagnostic` containing `message`, `code`, `level`, `spans`, `children`, and an optional `rendered` string.

When rustc constructs `rendered`, `JsonEmitter` creates an `AnnotateSnippetEmitter` and passes through its `diagnostic_width`. Thus `--diagnostic-width=<N>` controls the human rendering embedded in JSON as well as direct human output.

The checked-in `tests/ui/diagnostic-width/flag-json.rs` fixture pins `--diagnostic-width=20 --error-format=json` specifically to exercise width-sensitive JSON diagnostic output. Its checked-in stderr preserves the resulting narrow rendered diagnostic.

Basis: **source** in `compiler/rustc_errors/src/json.rs` + **checked-in test specimen** `tests/ui/diagnostic-width/flag-json.rs` and `.stderr`.

### Human output has explicit format, width, and color controls

At the exact pin, the stable public choices advertised by `--error-format` are:

- `human`, the default multi-line human rendering;
- `short`, a one-line human rendering; and
- `json`, the structured emitter.

`--color=auto|always|never` controls ANSI coloring for human output. A reproducible text fixture should set `--color=never` rather than inherit TTY-dependent `auto` behavior.

The parser also recognizes `pretty-json` and `human-unicode`. `check_error_format_stability` rejects those variants on a non-nightly compiler unless unstable options are enabled. They should not be treated as part of the stable format surface merely because this pinned nightly accepts them.

For a human-readable golden test at this pin, a conservative baseline is therefore:

```text
--error-format=human --diagnostic-width=<fixed> --color=never
```

Use `--error-format=short` only when the one-line form is the intended contract.

Basis: **documentation + source** in `src/doc/rustc/src/command-line-arguments.md` and `compiler/rustc_session/src/config.rs`.

### Ordinary JSON is line-delimited; its structured schema is revision-sensitive

The rustc book states that ordinary JSON messages are emitted one per line to stderr. The implementation's non-pretty `JsonEmitter` serializes one JSON value, writes a newline, and flushes.

That makes ordinary `--error-format=json` appropriate for a streaming machine consumer. `pretty-json`, by contrast, uses pretty serialization and is gated as unstable; it should not be substituted when a consumer relies on one JSON value per physical line.

The command-line mode is stable, but the schema is not a frozen compatibility contract. The JSON emitter source says the format should be considered unstable. The rustc book separately instructs parsers to be forwards-compatible: optional values may be null, new fields may appear, and enumerated fields may gain values.

A durable consumer should therefore:

1. select ordinary `--error-format=json`;
2. identify records through `$message_type` rather than byte layout;
3. accept unknown fields and future enum values where possible;
4. consume structured `message`, `code`, `level`, spans, children, and suggestions according to the pinned revision it supports; and
5. treat `rendered` as presentation text, not the canonical machine identity of a diagnostic.

Basis: **documentation + source** in `src/doc/rustc/src/json.md` and `compiler/rustc_errors/src/json.rs`.

### `--json` controls the embedded rendering and additional record classes

`--json` is a stable multi-value option, but the parser requires it to accompany JSON error format. At this revision the source recognizes:

- `diagnostic-short`;
- `diagnostic-unicode`;
- `diagnostic-rendered-ansi`;
- `artifacts`;
- `timings`;
- `unused-externs`;
- `unused-externs-silent`; and
- `future-incompat`.

The public rustc book documents the main stable-facing subset and states two important constraints: `--json` requires `--error-format=json`, and `--json` cannot be combined with `--color`.

By default, JSON's `rendered` field is plain text. `diagnostic-rendered-ansi` is the explicit opt-in to ANSI coloring inside that string. `diagnostic-short` selects short human rendering for that field. A machine consumer that ignores `rendered` should still avoid assuming that these switches cannot affect any other diagnostic state without checking the exact revision; the source-level width examples above already show that formatting-related inputs can affect structured error construction.

`--json=timings` is additionally gated behind `-Zunstable-options` at this pin.

Basis: **documentation + source** in `src/doc/rustc/src/command-line-arguments.md` and `compiler/rustc_session/src/config.rs`.

### Width and error format are untracked compiler options

`compiler/rustc_session/src/options.rs` classifies both `error_format` and `diagnostic_width` as `UNTRACKED` options rather than compilation-tracked inputs.

At this revision, changing them is therefore intended to change diagnostic presentation/reporting without changing the compilation dependency fingerprint used by tracked compiler options. This does not make diagnostics invariant: as shown above, width can alter which diagnostic text or child form rustc chooses.

Basis: **source** in `compiler/rustc_session/src/options.rs`.

### `TERM` and `COLUMNS` are weaker controls than the explicit width flag for zerocopy's UI tests

Current zerocopy's UI harness makes the reproducibility choice explicit. For non-MSRV toolchains it passes `--diagnostic-width=100`, with a comment that this is the most reliable way to keep rustc diagnostic wrapping fixed. It also sets `TERM=dumb` and `COLUMNS=100`, but the adjacent comment says rustc can still discover the real terminal width and that the command-line width is more reliable.

The harness additionally filters some known volatile diagnostic content, such as generated long-type filenames and counts of omitted implementation candidates. This is a useful boundary: fixed width removes one environmental source of drift, but a robust golden suite may still need narrowly justified normalizations for other revision/configuration-dependent text.

Basis: **source** in `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `tools/ui-runner/src/main.rs`.

### A practical stability profile separates structured identity from rendered text

For a test that needs to preserve machine-meaningful diagnostics while remaining insensitive to terminal state, the exact-pin evidence supports this profile:

```text
rustc ... \
  --error-format=json \
  --diagnostic-width=100
```

Do not pass `--json=diagnostic-rendered-ansi` unless ANSI bytes are intentionally part of the specimen. Parse JSON records structurally. Compare only the fields that matter to the test, and normalize source paths through an explicit path-remapping policy rather than by deleting location information wholesale.

If the test instead intends to lock the user-facing rendering, include `rendered` in the specimen and fix every presentation control that the test cares about, especially width and color/ANSI policy. The compiler revision, target/configuration, and input source remain part of the fixture identity.

This is a **derived testing recommendation** from the pinned implementation and the current zerocopy UI harness. It is not an upstream guarantee that diagnostic wording or JSON shape stays stable between compiler releases.

## Boundaries

**No fresh execution.** The report did not invoke the pinned rustc. Checked-in rustc UI fixtures provide preserved specimens, but they are source-tree evidence rather than a newly run probe.

**No cross-version byte-stability claim.** Stable command-line options do not make diagnostic text, ordering, spans, suggestions, or JSON schema stable across compiler revisions.

**JSON is not a versioned frozen protocol here.** The source explicitly calls the JSON format unstable. The rustc book documents how to consume it defensively; it does not promise exact field or enum closure.

**Width is not the only source of nondeterminism or drift.** Compiler revision, target, cfg/features, source paths, enabled lints, macro expansion, long-type handling, and other inputs can all affect output. The report establishes width/format controls, not a complete golden-test normalization policy.

**The explicit width is not semantically inert with respect to diagnostics.** It is untracked for compilation, but it can alter shortening and diagnostic child/label choices. Code that wants stable diagnostic structure should not vary it casually.

**No claim about other tools.** Lean, Cargo, Charon, Aeneas, rustdoc, Clippy wrappers, and LSP transports can add their own formats or controls. rustdoc shares parts of rustc's diagnostic stack, but its complete CLI behavior is not examined here.

**Environment-variable semantics are not specified here.** The report does not claim exactly how the `termize` dependency interprets every terminal/environment configuration. The relevant implementation fact is that explicit `diagnostic_width` is consulted before terminal-dimension discovery.

## Evidence

Primary rustc subject:

- `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`nightly-2026-05-31`).
- `src/doc/rustc/src/command-line-arguments.md`, blob `b6ee6c3f5fa79a2a98e43951658bd958e96dabd3`: public `--error-format`, `--color`, `--diagnostic-width`, and `--json` behavior.
- `src/doc/rustc/src/json.md`, blob `7421dd6210806f8e3a9b310f8f72578830309abe`: line-delimited JSON documentation, diagnostic shape, and forwards-compatibility guidance.
- `compiler/rustc_session/src/config.rs`, blob `e82f67eac5e9f7d0b089727e6317d77242ba3b1c`: option stability registration, JSON sub-option parsing, format gating, and width parsing.
- `compiler/rustc_session/src/session.rs`, blob `c83bb62324e76a0686515782d3290961d655dd3d`: `Session::diagnostic_width` precedence and fallback.
- `compiler/rustc_session/src/options.rs`, blob `de606458d048e93b4bb97b0b5cdc6d70f9cee6a4`: `error_format` and `diagnostic_width` marked `UNTRACKED`.
- `compiler/rustc_errors/src/annotate_snippet_emitter_writer.rs`, blob `c3c9f26c31571596875822ae7227d51dfb34f16b`: explicit-width renderer path and terminal fallback.
- `compiler/rustc_errors/src/json.rs`, blob `04ac140f332618d6fa81254e9a16bc27c729eef5`: JSON serialization, unstable-schema warning, structured fields, and width passthrough into `rendered`.
- `compiler/rustc_middle/src/ty/error.rs`, blob `81cd3efffc9d4fb110bbc736f21024b3dc1a607f`: width-dependent type shortening and long-type file decisions.
- `compiler/rustc_trait_selection/src/error_reporting/infer/mod.rs`, blob `c9e2312895820e0cd480eace6b4a32c12aeea3c3`: width-dependent expected/found type shortening.
- `compiler/rustc_trait_selection/src/error_reporting/traits/fulfillment_errors.rs`, blob `4d051a370c06570d2511a0b49b6137b6b99baab9`: width-dependent span-label versus help structure.
- `tests/ui/diagnostic-width/flag-json.rs`, blob `edc7d2e2a4255429405ee2a0a45fac414424ccd6`, and `flag-json.stderr`, blob `cfc0364be76dee749b2baab13d4ee4f6d4e58ede`: checked-in narrow-width JSON specimen.
- `tests/ui/diagnostic-width/flag-human.rs`, blob `8e656293b41025febe2236c13bb5e4d6e39670c4`: checked-in narrow-width human-rendering fixture.

Downstream corroboration:

- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `tools/ui-runner/src/main.rs`, blob `933bef1b3a41fb11978247ef2a185c3e289257f4`: fixed `--diagnostic-width=100`, `TERM=dumb`, `COLUMNS=100`, and comments explaining why the explicit rustc flag is the reliable control for UI snapshots.

Observation date: 2026-09-27.

## Revalidation

For a new rustc revision, the cheapest source revalidation is:

1. inspect `compiler/rustc_session/src/config.rs` and confirm the stability/accepted values for `error-format`, `json`, `color`, and `diagnostic-width`;
2. inspect `Session::diagnostic_width` and `AnnotateSnippetEmitter::renderer` to confirm explicit width still precedes terminal discovery;
3. search the compiler for every call to `diagnostic_width()` and determine whether width still changes diagnostic construction beyond wrapping;
4. inspect `compiler/rustc_errors/src/json.rs` and `src/doc/rustc/src/json.md` for schema/stability and `rendered` construction changes; and
5. rerun the narrow `tests/ui/diagnostic-width/flag-human.rs` and `flag-json.rs` fixtures, or equivalent minimal specimens, with two materially different fixed widths.

A compact external probe can use one source file that triggers both a long type mismatch and a long trait-bound explanation. Run it under:

```text
--error-format=human --color=never --diagnostic-width=40
--error-format=human --color=never --diagnostic-width=100
--error-format=json  --diagnostic-width=40
--error-format=json  --diagnostic-width=100
```

For JSON, preserve both the structured object and `rendered`. The expected discriminator is not merely different wrapping: at least one long diagnostic should exercise a width-dependent shortening or label/help decision. If the structured object no longer changes with width, update this report rather than carrying forward the current implementation inference.

For the downstream zerocopy harness, recheck `tools/ui-runner/src/main.rs` whenever its compiler invocation or UI-test normalization changes. Its use of `--diagnostic-width=100` is evidence about that harness revision, not a contract for future zerocopy tests.
