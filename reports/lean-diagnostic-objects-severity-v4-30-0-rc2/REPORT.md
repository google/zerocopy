# Lean diagnostic objects and severity at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Lean's elaborator diagnostic model is centered on `Message`, not directly on LSP `Diagnostic`. A `Message` carries a Lean file name, start and optional end positions, a three-valued severity (`information`, `warning`, or `error`), a silent-display flag, a caption, and structured `MessageData`. Its top-level message-data tag can also carry a machine-recognizable message kind or named-error identity.

Messages accumulate in `MessageLog`, which separately retains already-reported and not-yet-reported messages. Batch reporting serializes `MessageData` to text and can emit the resulting `SerialMessage` as JSON. The language server instead converts each `Message` to a richer `InteractiveDiagnostic`, maps Lean positions into the open document's LSP coordinates, preserves the full semantic range separately from a display range, maps the three Lean severities into LSP severities, attaches named-error codes and selected tags, and only then flattens the interactive message to the ordinary string-valued LSP diagnostic sent to clients.

Two distinctions are especially important for downstream tooling. First, Lean's core `MessageSeverity` has no `hint` case even though LSP's `DiagnosticSeverity` does; the pinned `Message`-to-LSP conversion only produces error, warning, or information. Second, severity can change before or during reporting. `warningAsError` promotes warnings when they are logged, changing the stored `Message`. Separately, batch `runAndReport` accepts per-message-kind severity overrides that rewrite the message used for output without changing the preceding error count computed from the stored severity. Consumers should therefore distinguish a diagnostic's stored severity, its rendered severity on a particular output path, and process/build success.

No fresh Lean execution was performed. These findings come from exact pinned source and describe the implementation contract at this revision, not adjacent-version behavior.

## Applicability

This report applies to Lean 4 at `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, tagged `v4.30.0-rc2`, which is the Lean revision selected by current Anneal toolchain research.

The report covers Lean's in-process message representation, message-log lifecycle, severity assignment and promotion, batch-report conversion, and language-server diagnostic conversion. It does not define the complete `lean --json` command protocol, warning-command-line syntax, editor behavior, or every diagnostic-producing API. Those are separate surfaces built on the object model documented here.

The LSP structures follow Lean's implementation of the LSP 3.17 diagnostic shape, but claims here are about the pinned Lean source. The external LSP specification is not needed to establish the Lean-specific extensions or conversion behavior described below.

## Findings

### `Message` is the elaborator diagnostic object

`MessageSeverity` has exactly three constructors: `information`, `warning`, and `error`. `BaseMessage α` carries `fileName`, `pos`, optional `endPos`, `keepFullRange`, `severity`, `isSilent`, `caption`, and `data`. `Message` is `BaseMessage MessageData`; its payload is therefore structured and may require an elaboration/pretty-printing context to render.

`MessageData` is not merely a string. Its constructors include formatted text with info annotations, goals, widgets, saved pretty-printing contexts, composition/grouping, tags, traces, and lazy content. `MessageData.kind` returns the top-level tag through context wrappers. That tag is used as a machine-facing message kind independently of the rendered prose.

Basis: **source**.

### Named errors reuse the message-kind channel

Lean encodes a user-facing named error by tagging the message with a name ending in `_namedError`. `kindOfErrorName` constructs that tag; `errorNameOfKind?` reverses it; `Message.errorName?` exposes the result. A message can have a non-anonymous kind without being a named error, so `kind` and named-error identity are related but not interchangeable.

`ErrorExplanation.Metadata` separately records an explanation summary, the Lean version that introduced the named error, a `MessageSeverity` (defaulting to `error`), and an optional removal version. This metadata is stored in an environment extension. The explanation metadata is not the same object as an emitted `Message`, and its severity field does not by itself override an already-created message.

Basis: **source**.

### Logging assigns source range, context, severity, and silence before the message enters the log

`MonadLog.logMessage` is the primitive sink. `logAt` builds the `Message` around a `MessageData` value: it chooses a source reference, converts raw offsets through the current `FileMap` to Lean line/column positions, adds the current message-printing context, fills `fileName`, `pos`, `endPos`, `severity`, and `isSilent`, then calls `logMessage`.

The convenience functions `logErrorAt`/`logError`, `logWarningAt`/`logWarning`, and `logInfoAt`/`logInfo` select the three corresponding severities. Named-error and named-warning helpers first add the named-error tag and then use the same logging path.

`warningAsError` is applied in `logAt`: when the requested severity is `warning` and the option is true, Lean stores the new `Message` with severity `error`. This is an early promotion, before the message reaches `MessageLog` or either reporting path.

Basis: **source**.

### `MessageLog` distinguishes diagnostic history from pending report output

`MessageLog` contains two persistent arrays plus a set of logged kinds:

- `reported` contains messages already saved/reported for the current command;
- `unreported` contains newly added messages in insertion order;
- `loggedKinds` records message kinds for duplicate-suppression mechanisms.

`add`, `toList`, `toArray`, and the normal iteration helpers operate on `unreported`. `markAllReported` appends `unreported` to `reported` and empties `unreported`. By contrast, `hasErrors` checks both arrays, so code can remember that the current command has errored even after its diagnostics have been moved out of the pending-report set.

This is a lifecycle distinction, not a severity distinction: reporting a message does not demote or delete it from the command's lookback history.

Basis: **source**.

### Serialization freezes structured message data into text and preserves the message kind

`Message.serialize` evaluates the structured `MessageData` to a string and constructs a `SerialMessage` that otherwise extends the same `BaseMessage` fields while adding the saved `kind`. `Message.toJson` serializes through this representation rather than directly encoding the effectful `MessageData` tree.

`SerialMessage.toString` treats information specially: it prints the message text without the file-position severity prefix used for warnings and errors. Warning and error text output includes the file/position label and, for a named error, the recovered error name.

This establishes the object-level basis for batch JSON/text output. The command-line protocol framing and exact `lean --json` consumer contract are outside this report.

Basis: **source**.

### Snapshot diagnostics keep the ordinary log and optionally cache the interactive conversion

The incremental language layer wraps a `MessageLog` in `Language.Snapshot.Diagnostics`. Alongside `msgLog`, this object has an optional mutable slot used by the language server to memoize interactive diagnostics. A `Snapshot` carries one such diagnostic set, and the union of finished snapshot message logs is what the server eventually reports.

`Snapshot.Diagnostics.ofMessageLog` allocates the cache slot. The file worker reuses a cached interactive conversion when present; otherwise it converts the snapshot's unreported messages and stores the resulting interactive diagnostics in that slot.

Basis: **source**.

### Lean's LSP diagnostic shape is richer than the core message shape

`Lsp.DiagnosticSeverity` has four values with the standard numeric encodings: error `1`, warning `2`, information `3`, and hint `4`. `Lsp.DiagnosticWith α` contains:

- a display `range` and Lean extension `fullRange?`;
- optional LSP severity;
- Lean extension `isSilent?`;
- optional diagnostic `code?` and `source?`;
- payload `message : α`;
- standard diagnostic tags plus Lean-specific tags;
- related information; and
- an opaque `data?` field.

Ordinary LSP diagnostics specialize the message payload to `String`. Lean's `InteractiveDiagnostic` specializes the same structure to widget-enriched `InteractiveMessage`, so the server can retain rich message content internally without changing the surrounding diagnostic metadata model.

Basis: **source**.

### Core messages never map to LSP `hint` at this revision

`Widget.msgToInteractiveDiagnostic` converts `MessageSeverity.information` to LSP `information`, `warning` to `warning`, and `error` to `error`. There is no fourth core message severity to map to LSP `hint`.

The LSP datatype still accepts and can encode/decode `hint`; this report does not claim that no other Lean server subsystem can ever construct a hint-valued `DiagnosticWith` directly. The narrower established fact is that the ordinary `Message` conversion cannot produce one.

Basis: **source** + **derived**.

### Server conversion preserves a full range separately from its editor display range

The converter maps `Message.pos` and `Message.endPos` through the current document's `FileMap` to LSP positions. The resulting `fullRange` spans the complete message range. Unless `keepFullRange` is true, a multi-line message's ordinary display `range` is truncated to the end of the first line so editors do not underline a large block of source. `fullRange?` still receives the untruncated range.

A missing `endPos` yields a zero-width range at the start position. This range conversion is local to the Lean document; it does not recover Rust or Charon source coordinates.

Basis: **source**.

### Server conversion also derives codes, tags, source, and silence metadata

For ordinary messages, `msgToInteractiveDiagnostic` sets `source?` to `"Lean 4"`. If the message kind encodes a named error, it becomes a string-valued diagnostic code. Deprecation-warning and unused-variable tags become standard LSP `deprecated` and `unnecessary` tags. Lean-specific message tags can become `unsolvedGoals` or `goalsAccomplished` diagnostic tags.

A silent message becomes `isSilent? := some true`. If the connected client does not advertise Lean's silent-diagnostic capability, `FileWorker` filters silent messages before conversion. Otherwise the silent metadata is retained. The server's public `publishDiagnostics` path then flattens each interactive message to string form via `InteractiveDiagnostic.toDiagnostic` while preserving the other diagnostic fields.

Basis: **source**.

### Batch output has a second, later severity-override layer

`Language.SnapshotTree.runAndReport` accepts a `NameMap MessageSeverity` of severity overrides. `reportMessages` first increments its error counter from the stored `msg.severity`; only after that does it replace `msg.severity` for a matching message kind before formatting or JSON serialization. The same function suppresses `isSilent` messages and enforces `maxErrors` from the stored-error counter.

`Elab.runFrontend` builds this map from its `errorOnKinds` argument by mapping those kinds to `error` and passes it to `runAndReport`.

Therefore, at this exact revision, an output-time kind override is not equivalent to changing the stored message severity. In particular, the rendered/serialized copy can have severity `error` even though the error counter and `runAndReport` result were computed from a stored warning or information message. Conversely, an override of a stored error would not retroactively remove it from the error count.

This is separate from `warningAsError`, which promotes the message inside `logAt` and thus changes the stored severity before counting.

Basis: **source** + **derived** from the ordering in `reportMessages`.

### Severity, fatality, and success are separate dimensions

`MessageSeverity.error` is the severity that `MessageLog.hasErrors` recognizes and that batch reporting counts. A language `Snapshot` separately carries `isFatal`, meaning processing cannot continue for the remainder of the file. A nonfatal error message and a fatal snapshot are therefore distinct states.

Likewise, visual severity does not by itself specify the whole batch process result: stored severity, output-time severity overrides, `maxErrors`, frontend control flow, and fatal processing state participate at different layers. A consumer that needs a verification success predicate should derive it from the relevant Lean entry point rather than infer it only from the color or severity of one emitted LSP diagnostic.

Basis: **source** + **derived**.

## Boundaries

- No Lean executable, language server, editor client, or `lean --json` command was run for this report.
- This report does not inventory every producer of `Message` or every direct producer of `Lsp.DiagnosticWith`.
- It does not define the complete `lean --json` wire protocol, line framing, process-exit behavior, or stability guarantees. It only establishes that `Message.toJson` serializes through `SerialMessage` and that batch reporting may emit it.
- It does not fully characterize command-line warning controls. It establishes the source-level `warningAsError` promotion and `runAndReport` kind-override mechanisms because they directly affect diagnostic severity.
- It does not claim LSP `hint` is unused everywhere. It establishes only that `MessageSeverity` lacks a hint case and `msgToInteractiveDiagnostic` never maps an ordinary `Message` to hint.
- It does not claim that `isSilent` means semantically irrelevant. Silent messages remain messages; the language-server display behavior depends on client capability, while batch reporting suppresses them.
- It does not claim that `MessageData.kind` is always a named error. Only the `_namedError` encoding recognized by `errorNameOfKind?` produces the named-error identity used as the LSP diagnostic code.
- It does not establish a Rust-source mapping. Message and LSP ranges are coordinates in the Lean source/document; the existing source-correspondence report covers the separate cross-language problem.
- The report is pinned to Lean `v4.30.0-rc2`. Adjacent Lean releases may change fields, tags, caching, severity handling, or reporting order.

## Evidence

All implementation evidence is **source** from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`). The conclusions explicitly labeled derived above are **derived** from those source paths. There is no fresh **execution** evidence.

- `src/Lean/Message.lean`, blob `a7f76198c582d1d2032bb24d13ad4cb7a272fa57`: `MessageSeverity`; structured `MessageData`; `BaseMessage`; `Message`; named-error kind encoding; `Message.serialize`; `SerialMessage`; `MessageLog` and its reported/unreported lifecycle.
- `src/Lean/Log.lean`, blob `3d40ada008ff57e9c82568661f3c4ecf928f9280`: `MonadLog`; `warningAsError`; `logAt`; error/warning/information and named-error logging helpers.
- `src/Lean/Language/Basic.lean`, blob `08f9b688fc869224c316175220403c2aeb5eb415`: `Snapshot.Diagnostics`; `Snapshot`; `reportMessages`; `SnapshotTree.runAndReport`; interactive-diagnostic cache allocation.
- `src/Lean/Data/Lsp/Diagnostics.lean`, blob `d15c1ce80d3699be7a5d92ebf6cea6725c3a4b34`: `DiagnosticSeverity`; `DiagnosticCode`; standard and Lean-specific tags; `DiagnosticWith`; `PublishDiagnosticsParams`.
- `src/Lean/Widget/InteractiveDiagnostic.lean`, blob `5fc9e0b22a3195c7843f7a45b7c0bdab870fce08`: `InteractiveDiagnostic`; `toDiagnostic`; `msgToInteractiveDiagnostic`; severity, range, code, source, tag, and silent-field conversion.
- `src/Lean/Server/FileWorker.lean`, blob `c803034ed8810f13a5ef38a603a21e610efca2bc`: memoization of interactive diagnostics, client-dependent silent-message filtering, and `textDocument/publishDiagnostics` publication.
- `src/Lean/Elab/Frontend.lean`, blob `fd3760667db96a351b4f654720193c89bbee356e`: `runFrontend`, construction of `errorOnKinds` severity overrides, batch reporting, and the subsequent frontend error gate.
- `src/Lean/ErrorExplanation.lean`, blob `9c16eef5064048796e18f171c34206f6d788eba5`: named-error explanation metadata and its persistent environment extension.

The existing corpus report `end-to-end-source-correspondence-nightly-2026-06-03-v4-30-0-rc2` independently documents the Lean-document coordinate boundary and Rust-to-Lean source-correspondence problem. This report narrows in on the diagnostic object and severity model rather than repeating that cross-language analysis.

## Revalidation

For another Lean revision, first diff the small set of definitions that determines the model:

1. `MessageSeverity`, `BaseMessage`, `Message.serialize`, named-error helpers, and `MessageLog` in `src/Lean/Message.lean`;
2. `warningAsError` and `logAt` in `src/Lean/Log.lean`;
3. `Snapshot.Diagnostics`, `reportMessages`, and `SnapshotTree.runAndReport` in `src/Lean/Language/Basic.lean`;
4. `DiagnosticSeverity` and `DiagnosticWith` in `src/Lean/Data/Lsp/Diagnostics.lean`;
5. `msgToInteractiveDiagnostic` and `InteractiveDiagnostic.toDiagnostic` in `src/Lean/Widget/InteractiveDiagnostic.lean`; and
6. the diagnostic conversion/cache/publication block in `src/Lean/Server/FileWorker.lean`.

Also inspect `Elab.runFrontend` if output-time severity overrides or batch success behavior matter. If any of these definitions changed, do not infer compatibility from the version number alone.

On a capable execution surface, a compact discriminating probe should emit one information message, one warning, one named warning, one error, and one silent message at known single- and multi-line ranges. Run it with and without `warningAsError`, collect ordinary text output, batch JSON output, and language-server `publishDiagnostics`, and preserve exact bytes/transcripts. Add a message kind passed through the frontend's severity-override mechanism so the probe distinguishes stored severity from rendered severity and process success. If LSP `hint` behavior matters, separately test whether any direct server producer emits a hint; the ordinary `Message` conversion cannot answer that broader question by itself.