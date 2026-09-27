# Lean `--json` CLI protocol at v4.30.0-rc2

## Summary

At Lean `v4.30.0-rc2`, `lean --json` is primarily a **JSON-lines encoding of Lean diagnostic messages**, not a versioned protocol that frames every byte written by the process. The command-line frontend passes a Boolean `jsonOutput` flag into elaboration; each non-silent, unreported `Message` is converted to a `SerialMessage`, encoded as compact JSON, and printed as one line on standard output. The same frontend still has ordinary text error paths, and Lake's own `lean --json` consumer deliberately accepts non-JSON stdout and plain stderr alongside serialized messages.

The on-wire message shape is mechanically derived from Lean's `SerialMessage` data type. At this revision it carries the file name, start and optional end positions, range-control and silent flags, severity, caption, rendered message text, and message kind. The rich `MessageData` payload is **not** preserved structurally: `Message.serialize` renders it to a `String` and saves only its top-level `kind` separately.

There is no schema-version field, handshake, or content-type envelope in this path. Anneal should therefore treat the exact `SerialMessage` definition and Lean revision as the compatibility boundary. A robust consumer should pin the Lean revision, decode the documented fields permissively, and preserve a fallback path for non-JSON process output instead of treating `--json` as a whole-process transport contract.

## Applicability

This report describes [`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`](https://github.com/leanprover/lean4/tree/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc), the Lean revision selected by Anneal's `v4.30.0-rc2` toolchain.

It covers the `lean` frontend's `--json` diagnostic output: its framing, `SerialMessage` schema, source positions, warning/error treatment, ordinary process exit behavior, and compatibility boundary. It does not cover Lean server JSON-RPC, InfoView RPC encoding, Lake's unrelated `lake --json` modes, or the full semantics of every warning-promotion mechanism. Those are distinct interfaces.

The findings are source-based. No fresh Lean executable was available or bootstrapped for this report. Where source code does not promise a compatibility property, this report states the implementation boundary rather than inferring a stronger guarantee.

## Findings

### `--json` selects JSON-lines diagnostic reporting

The shell exposes `--json` as "report Lean output (e.g., messages) as JSON (one per line)" and records the option as `ShellOptions.jsonOutput`. The frontend receives that Boolean as the `jsonOutput` argument to `Elab.runFrontend`. [`Shell.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L154-L176) [`Shell.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L227-L247) [`Shell.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L382-L385) [`Shell.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L530-L535)

The actual framing is implemented by `Language.reportMessages`. It walks `MessageLog.unreported`; for each non-silent message, JSON mode calls `msg.toJson` and then `IO.println j.compress`. Thus each reported diagnostic is one compact JSON value followed by a newline on **stdout**. `SnapshotTree.runAndReport` traverses the snapshot tree in preorder and feeds every snapshot's diagnostic log through this function. [`Language/Basic.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Language/Basic.lean#L302-L345)

The `MessageLog` distinction between `reported` and `unreported` is part of the incremental implementation: diagnostic reporting consumes the messages still in the `unreported` portion of each snapshot rather than serializing an aggregate environment-wide log. [`Message.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Message.lean#L568-L590)

### Each JSON line is a derived `SerialMessage`

`Message.toJson` first invokes `Message.serialize`, which renders the effectful `MessageData` to a string and saves `msg.kind`, then applies the ordinary `ToJson` instance for `SerialMessage`. [`Message.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Message.lean#L542-L566)

`SerialMessage` extends `BaseMessage String`. At this revision its logical JSON fields are:

| Field | JSON value | Meaning |
| --- | --- | --- |
| `fileName` | string | Diagnostic source file name. |
| `pos` | object `{ "line": Nat, "column": Nat }` | Start position. |
| `endPos` | `null` or the same position object | Optional end position. |
| `keepFullRange` | boolean | Whether clients should preserve the full supplied diagnostic range. |
| `severity` | string `"information"`, `"warning"`, or `"error"` | Reported message severity. |
| `isSilent` | boolean | Message's silent flag. The CLI skips silent messages before serialization, so emitted lines normally have this false. |
| `caption` | string | Optional caption kept separately from the body. |
| `data` | string | Eagerly rendered `MessageData` body. |
| `kind` | string | The top-level `MessageData.kind` name. |

The field set follows directly from `BaseMessage` and `SerialMessage`. Both structures derive JSON encoding; `MessageSeverity` is a nullary inductive with derived JSON encoding; `Position` is a `{line, column}` structure with derived JSON encoding; and `Name` encodes as its string form. [`Message.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Message.lean#L43-L53) [`Message.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Message.lean#L427-L451) [`Data/Position.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Position.lean#L11-L16) [`FromToJson/Basic.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Json/FromToJson/Basic.lean#L82-L94)

The deriving implementation encodes structures as JSON objects using their field names. A field is omitted only when its Lean field name itself ends in `?`; otherwise an `Option` value is encoded normally, with `none` becoming JSON `null`. `BaseMessage.endPos` is named `endPos`, not `endPos?`, so it remains a field whose absent value is `null`. Nullary inductive constructors are encoded as their constructor-name strings. [`FromToJson.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Elab/Deriving/FromToJson.lean#L29-L56) [`FromToJson/Basic.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Json/FromToJson/Basic.lean#L82-L94)

The important semantic loss is deliberate: the JSON `data` field contains `MessageData.toString` output, not the structured `MessageData` tree used inside Lean. Consumers retain the top-level `kind`, positions, severity, caption, and flags, but they cannot reconstruct arbitrary formatting tags, embedded expressions, widgets, or other structured message content from this wire representation. [`Message.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Message.lean#L542-L566)

### Positions use Lean diagnostic coordinates, not LSP coordinates

`SerialMessage.pos` and `endPos` are `Lean.Position`, not `Lean.Lsp.Position`. `Lean.Position` contains `line` and `column`. `FileMap.toPosition` produces one-based line numbers through `getLine`, while columns begin at zero and are counted by iterating the Lean `String` from the start of the line to the raw source position. [`Data/Position.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Position.lean#L11-L16) [`Data/Position.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Position.lean#L60-L98)

This distinction matters for an Anneal consumer that also speaks LSP: it should not reuse LSP's zero-based line/UTF-16 coordinate assumptions for `lean --json` messages.

`printMessageEndPos` does not control the JSON schema. `reportMessages` reads that option, but passes it only to the text `msg.toString includeEndPos` path. JSON mode calls `msg.toJson` directly, so `endPos` follows the `SerialMessage` value regardless of the text-formatting option. [`Language/Basic.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Language/Basic.lean#L291-L333)

### Severity and exit status are related but not identical interfaces

`runFrontend` constructs a map from every `-E/--error=kind` argument to `.error`, reports the entire snapshot tree, and returns `none` when `runAndReport` says an error was reported. The shell then exits successfully only when an environment was returned. Ordinary elaboration errors therefore produce an error-severity JSON diagnostic and a nonzero process status. [`Shell.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L418-L423) [`Elab/Frontend.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Elab/Frontend.lean#L136-L194) [`Shell.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L530-L557)

There is a pin-specific subtlety around `-E`: `reportMessages` increments its error counter from the message's **original** severity before consulting `severityOverrides`; only afterward does it replace the message severity for output. Consequently, this code path establishes that `-E kind` changes the serialized severity, but it does not establish that such a promotion contributes to `runAndReport`'s `numErrors`/Boolean in the same way as an originally-error message. Anneal should not infer process failure merely from seeing a serialized `severity: "error"`; process exit status remains authoritative. [`Language/Basic.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Language/Basic.lean#L311-L345)

`maxErrors` is another explicit exit path. Once the count of originally-error messages exceeds the configured limit, the current message is replaced with a `maximum number of errors ... reached` error and `reportMessages` calls `IO.Process.exit 1` immediately. [`Language/Basic.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Language/Basic.lean#L311-L335)

### `--json` is not a whole-process framing guarantee

JSON mode changes the frontend message-reporting branch. Other shell paths still write ordinary text. For example, malformed command-line usage and an unknown `#lang` are reported with `IO.eprintln` and a nonzero return, independent of `jsonOutput`. [`Shell.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L420-L447) [`Shell.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L450-L517)

Lean's own Lake code confirms the intended defensive consumption pattern. `Lake.compileLeanModule` invokes Lean with `--json`, splits stdout into lines, attempts to parse each line as a `SerialMessage`, logs recognized messages structurally, and accumulates unrecognized lines as ordinary stdout. It handles stderr separately as ordinary text and independently checks the process exit code. [`Lake/Build/Actions.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Actions.lean#L28-L84)

For Anneal, this makes a line-oriented opportunistic decoder the safest direct-CLI design: parse complete stdout lines as `SerialMessage` when possible, retain non-JSON lines as process output, retain stderr separately, and use the actual process exit code rather than deriving success solely from diagnostics.

### The JSON shape is revision-coupled, not negotiated

The `--json` path serializes the implementation type `SerialMessage` directly through a derived `ToJson` instance. The stream contains no protocol-version field or envelope, and `ShellOptions` exposes only a Boolean `jsonOutput`, not a requested wire version. [`Message.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Message.lean#L427-L451) [`Message.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Message.lean#L542-L566) [`Shell.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L227-L247)

That does not prove Lean maintainers will change the schema frequently. It does establish that the source provides no wire-level negotiation mechanism that could let an unpinned consumer distinguish incompatible shapes. A durable Anneal adapter should therefore bind its parser to the exact Lean toolchain identity, tolerate unknown object fields where doing so is safe, reject missing or malformed fields needed for correctness, and revalidate the shape when the Lean pin changes.

## Boundaries

This report does not claim that every output-producing Lean feature obeys JSON-lines framing. The cited implementation proves the diagnostic-message path and shows ordinary shell and Lake fallback paths outside it. Code executed during elaboration or execution may have its own I/O behavior; consumers should preserve that possibility rather than infer a stronger guarantee from the `--json` option name.

This report does not specify the full warning policy. The exact `-E` ordering above is included because it affects how an observer should interpret serialized severity versus exit status. The broader warning-as-error mechanisms, warning kinds, and options belong in their dedicated corpus report.

This report also does not treat `SerialMessage.data` as a stable grammar. It is rendered human-facing text. Semantic automation should prefer machine fields such as `kind`, `severity`, and positions when those fields answer the question, and should not build correctness-critical parsers over message prose unless a separate exact-revision contract is established.

No runtime probe was performed. In particular, this report does not provide sample output captured from an executed `lean --json` process. The exact field inventory instead follows the pinned source types and the pinned derived-JSON implementation.

## Evidence

- Lean `v4.30.0-rc2` exact revision: [`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`](https://github.com/leanprover/lean4/tree/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc).
- `--json` help text, option storage, parsing, and forwarding: [`src/Lean/Shell.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L154-L176), [`ShellOptions`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L227-L247), [`--json` parse arm](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L382-L385), and [`runFrontend` invocation](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L530-L535).
- JSON-lines reporting, silent filtering, severity overrides, error counting, maximum-error exit, and preorder snapshot traversal: [`src/Lean/Language/Basic.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Language/Basic.lean#L291-L345).
- `BaseMessage`, `SerialMessage`, serialization, and JSON conversion: [`src/Lean/Message.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Message.lean#L427-L566).
- JSON derivation rules for structure fields and nullary inductives: [`src/Lean/Elab/Deriving/FromToJson.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Elab/Deriving/FromToJson.lean#L29-L63).
- `Option` JSON behavior: [`src/Lean/Data/Json/FromToJson/Basic.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Json/FromToJson/Basic.lean#L82-L94).
- `Lean.Position` shape and conversion: [`src/Lean/Data/Position.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Position.lean#L11-L16) and [`FileMap.toPosition`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Position.lean#L60-L98).
- Frontend error result and artifact suppression after reported errors: [`src/Lean/Elab/Frontend.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Elab/Frontend.lean#L136-L220).
- Shell-level plain-text paths and exit status: [`src/Lean/Shell.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L420-L447) and [`shellMain`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L450-L557).
- Lake's same-revision `lean --json` consumer and non-JSON fallback: [`src/lake/Lake/Build/Actions.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Actions.lean#L28-L84).

## Revalidation

When Anneal changes its Lean pin, revalidate this report from the new revision rather than assuming wire compatibility.

1. Re-read `src/Lean/Shell.lean` for the `--json` option, frontend invocation, ordinary stderr paths, and final exit behavior.
2. Re-read `src/Lean/Language/Basic.lean` for `reportMessages` and `SnapshotTree.runAndReport`; check output stream, framing, silent filtering, traversal order, severity-override ordering, and error counting.
3. Re-read `src/Lean/Message.lean` for `BaseMessage`, `SerialMessage`, `Message.serialize`, and `Message.toJson`. Diff every field and its type.
4. Re-read the active `ToJson` derivation implementation and the `ToJson` instances for `Option`, `Name`, `Position`, and `MessageSeverity`. Do not assume unchanged encoding merely because the Lean structures have similar names.
5. Re-read Lake's `compileLeanModule` consumer. A change in how Lean's own build tool distinguishes serialized diagnostics from ordinary stdout is strong evidence that Anneal's process adapter should change as well.
6. If an executable is available without bootstrapping a new toolchain, add a bounded probe containing one information message, warning, ordinary error, end-position-bearing error, silent message if constructible, and plain process output. Capture stdout, stderr, and exit code separately; confirm every source-derived claim above.
7. Keep the runtime probe subordinate to the source contract. A handful of sample messages cannot prove schema completeness; the exact data types and deriving implementation remain the exhaustive source for the field set at a pinned revision.