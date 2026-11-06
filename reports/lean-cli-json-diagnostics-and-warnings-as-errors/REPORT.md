# Lean CLI Entry Points, JSON Diagnostics, Formatting Controls, and Warnings-as-Errors

## Summary

Across `leanprover/lean4` at `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) and `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), the `lean` executable is a single command-line dispatcher (`Lean.Shell`) that selects between batch frontend elaboration (`.frontend`), the language-server watchdog (`--server` / `.watchdog`), and per-file server workers (`--worker` / `.worker`). Ordinary batch file checking and artifact generation share `Lean.Elab.runFrontend`; `--json` and `-E kind` modify snapshot reporting on that same frontend path rather than invoking a separate checker. Because module identity (`moduleNameOfFileName` relative to `--root`), pre-resolved `--setup` (`ModuleSetup` JSON), and compiled-module search paths (`LEAN_PATH`, `LEAN_SRC_PATH`, `LEAN_SYSROOT`) feed directly into `runFrontend`, a caller cannot treat `lean file.lean` as a pure function of source bytes and binary version alone.

In batch JSON mode (`lean --json`), `Language.reportMessages` iterates over `MessageLog.unreported` across the preorder snapshot tree, skips messages with `isSilent = true`, converts each `Message` (`BaseMessage MessageData`) into a `SerialMessage` (`BaseMessage String` plus `kind`) by eagerly rendering `MessageData.toString`, and prints one compact JSON object per line on standard output with fields `caption`, `data`, `endPos`, `fileName`, `isSilent`, `keepFullRange`, `kind`, `pos`, and `severity`. Source coordinates in `SerialMessage` use `Lean.Position` (one-based `line`, zero-based Unicode-character `column` via `FileMap.toPosition`), whereas language-server `InteractiveDiagnostic` / LSP `Diagnostic` conversion uses zero-based UTF-16 positions, maps the three core `MessageSeverity` values (`information`, `warning`, `error`—never LSP `hint`) to LSP severities, truncates multi-line display `range` to the first line unless `keepFullRange` is set while preserving `fullRange?`, and attaches `"Lean 4"` source labels, `_namedError` diagnostic codes, and diagnostic tags.

Diagnostic formatting and severity promotion have sharp source-level and runtime boundaries that remain unchanged between `v4.30.0-rc2` and `v4.34.1`:

1. **Width and formatting options**: `MessageData.toString` formats structured message data into a `Std.Format` and invokes `ToString.toString`, which calls `Std.Format.pretty` with its default width (`Std.Format.defWidth = 120`) without passing the active `Options`. Setting `-Dformat.width=N` therefore has no effect on ordinary multi-line batch diagnostic wrapping (`pp.oneline=false`), though it directly controls truncation (`[...]`) when `pp.oneline=true` because `PrettyPrinter.Formatter.format` explicitly calls `OneLine.pretty f (Std.Format.format.width.get options)`.
2. **Three distinct warning-promotion mechanisms**:
   - `set_option warningAsError true` / `-DwarningAsError=true` rewrites `.warning` to `.error` inside `Lean.logAt` before the message enters `MessageLog`, affecting `MessageLog.hasErrors`, batch exit status, artifact suppression, and (via `forwardedArgs`) language-server workers.
   - `lean -E kind` / `--error=kind` supplies a reporting-time `severityOverrides` map to `SnapshotTree.runAndReport`, where `reportMessages` increments its error counter from the stored `msg.severity` *before* overriding `msg.severity` for output. A warning promoted solely by `-E` is serialized with `"severity": "error"` on stdout without incrementing the frontend error count or causing `lean` to exit nonzero.
   - `lake --wfail` (`--fail-level=warning`) leaves Lean message severities unchanged as warnings, parses `lean --json` lines via `LogEntry.ofSerialMessage`, and fails the outer Lake `LogIO` action after completion when `log.maxLv >= .warning`.
3. **Batch diagnostic normalization versus semantic equivalence**: In a 5-case compilation and import-query fixture (`a` through `e`) plus a 20-cell formatting option matrix (62 recorded batch invocations across `v4.30.0-rc2` and `v4.34.1`), all 31 stdout transcripts per version are byte-identical between `v4.30.0-rc2` and `v4.34.1`. Relocating identical source (`a` vs. `b`) changes raw `fileName` and `.olean` bytes (`cfad98ad...` vs. `f5d53027...` on `v4.30.0-rc2`) while filename-normalized JSON diagnostics and consumer `#check`/`#print axioms` queries agree. However, changing a true theorem statement from `1 + 1 = 2` (`a`) to `2 + 2 = 4` (`e`) produces **identical filename-normalized compilation diagnostics** and exit code `0` while producing a different theorem in the compiled `.olean`. Normalized compilation diagnostics plus exit status are therefore insufficient as a verification or cache-equivalence oracle without an independent check of the exported environment.

## Applicability

The findings in this report apply to the following subjects recorded in `REPORT.json`:

- **Lean 4 / Lake `v4.30.0-rc2`**: `leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (local release binary SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997` on `arm64-apple-darwin24.6.0`), selected by `google/zerocopy` revision `41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/flake.nix`, `leanVersion = "v4.30.0-rc2"`).
- **Lean 4 / Lake `v4.34.1`**: `leanprover/lean4` revision `5045d0056413266e57c625dcd7c365b10e377c52` (`Lake version 5.0.0-src+5045d00`, local release binary SHA-256 `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554` on `arm64-apple-darwin24.6.0`).
- **Adjacent baseline reference (`v4.29.0`)**: `leanprover/lean4` revision `98dc76e3c0a9b856c9b98726b713fb04fab16740` (referenced for cross-version context where corpus comparisons bridge `v4.29.0`, `v4.30.0-rc2`, and `v4.34.1`; not directly executed in the 62-run batch normalization and formatting matrix below).

### Shared Behavior vs. Version-Specific Behavior (`v4.30.0-rc2` vs. `v4.34.1`)

- **Shared across `v4.30.0-rc2` and `v4.34.1`**:
  - `Lean.Shell` dispatch architecture (`.frontend`, `.watchdog`, `.worker`), `Elab.runFrontend` invocation, `--setup` (`ModuleSetup`), `--root` module-name derivation, and `LEAN_PATH` / `LEAN_SRC_PATH` / `LEAN_SYSROOT` lookup.
  - `MessageSeverity` (`information`, `warning`, `error`), `BaseMessage`, `Message`, `SerialMessage` 9-field JSON schema (`caption`, `data`, `endPos`, `fileName`, `isSilent`, `keepFullRange`, `kind`, `pos`, `severity`), `MessageLog` (`reported`, `unreported`, `loggedKinds`), and `Language.reportMessages` preorder JSON-lines emission on stdout.
  - The 120-column default width boundary in `MessageData.toString` (`ToString Format` -> `Format.pretty`), `OneLine.pretty` consulting `format.width` when `pp.oneline=true`, `format.indent`, `pp.unicode`, `pp.unicode.fun`, `pp.mvars.anonymous`, `pp.fvars.anonymous`, and `printMessageEndPos` (affecting text output only, not JSON).
  - The three-way distinction between `warningAsError` (log-time promotion in `Lean.logAt`), `lean -E kind` (post-count reporting override in `Language.reportMessages`), and `lake --wfail` (Lake `LogIO` threshold failure).
  - Byte-identical stdout across all 11 batch normalization-oracle invocations and all 20 formatting-control invocations on the preserved fixtures.
- **Version-specific differences in `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`)**:
  - Compiled `.olean` binary outputs for the normalization fixture (`a`, `b`, `c`, `e`) have different SHA-256 digests under `v4.34.1` than under `v4.30.0-rc2`, even though same-version repeated and relocated-output compilations remain deterministic within each version.
  - In `v4.34.1`, `src/Lean/Message.lean` grows to 901 lines (SHA-256 `09277320b843288e...`, with `MessageSeverity` at line 44 and `MessageLog` at line 658), and module compilation with the module system enabled can additionally emit `.olean.server`, `.olean.private`, and `.ir.sig` alongside `.olean` and `.ilean`.

## Findings

### 1. CLI Entry Points, `runFrontend`, and Outer Environment Boundaries

Basis: **source + derived** (`src/Lean/Shell.lean`, `src/Lean/Elab/Frontend.lean`, `src/Lean/Util/Path.lean`, `src/lake/Lake/Config/InstallPath.lean`, `src/lake/Lake/Config/Env.lean`, `src/lake/Lake/CLI/Help.lean`).

#### Single-Executable Dispatch (`Lean.Shell`)

`src/Lean/Shell.lean` defines the command-line state (`ShellOptions`), per-option updates (`ShellOptions.process`), and `shellMain`. Dispatch occurs before ordinary file elaboration:

- Default `.frontend` mode expects one input file (unless `--run` passes trailing arguments to `main`) or reads `<stdin>` under `--stdin`, decodes lossy UTF-8, and invokes `Elab.runFrontend`.
- `--server` switches the component to `.watchdog` and returns from `Server.Watchdog.watchdogMain`, forwarding accumulated `-D` options in `forwardedArgs`.
- `--worker` switches the component to `.worker` and returns from `Server.FileWorker.workerMain`.
- `--server` and `--worker` are exposed in CLI help only when Lean is built with multithreading support.
- Dependency-only flags (`--deps`, `--src-deps`, and internal dependency-JSON mode) parse only the module header to print import or source paths and return before `runFrontend`. Their success does not establish that the module elaborates.

#### Shared Batch Frontend (`Lean.Elab.runFrontend`)

In `.frontend` mode, `shellMain` resolves the target module name and calls:

```lean
Elab.runFrontend contents opts.leanOpts fileName mainModuleName ...
```

`runFrontend` enables command-line snapshots, defaults asynchronous elaboration on, parses and elaborates the file, runs `Language.SnapshotTree.runAndReport` to emit diagnostics, waits for the final command state, and returns `none` if no final state was produced or if any counted error occurred. Upon success (`some env`), `runFrontend` and `shellMain` can write `.olean` (`writeModule`), `.ilean` (extracted from snapshot `InfoTree`s), C source (`-c`), or LLVM bitcode (`-bc`), or execute `main` (`--run`). Passing `--json` sets `ShellOptions.jsonOutput := true`, and passing `-E kind` populates `ShellOptions.errorOnKinds`; both are passed into the same `runFrontend` call rather than selecting an alternate parser or elaborator.

#### Module Identity, `--root`, `--setup`, and Search Paths

A batch `lean` invocation depends on external path and environment state:

- **Path-derived module name**: Absent `--setup`, `moduleNameOfFileName` (`src/Lean/Util/Path.lean`) resolves both the input file and `--root` (defaulting to the current working directory) to real paths, requires the file to reside under the root, strips the root prefix and `.lean` extension, and converts path components to a `Lean.Name`. Moving identical bytes to another path or changing `--root=dir` changes the module's identity (falling back to `_stdin` only for plain checks that do not emit compiled module outputs).
- **`--setup=file` (`ModuleSetup`)**: Loads `ModuleSetup` JSON prior to frontend execution, supplying explicit module name, package identity, `isModule` status, imports, pre-resolved `importArts` (`ImportArtifacts`), dynamic libraries, plugins, and `options` (which override command-line options during the setup merge).
- **Compiled and source search paths**: `Lean.Util.Path` derives the installation root from the running executable (`--print-prefix`), sets the built-in library path to `<prefix>/lib/lean`, and prepends `LEAN_PATH` entries so `findOLean` checks `LEAN_PATH` before built-in libraries. `LEAN_SRC_PATH` governs source lookup.
- **Outer launcher vs. `LEAN_SYSROOT`**: `Lean.Shell` does not parse `lean-toolchain` or run Elan proxy resolution; `findSysroot` consults `LEAN_SYSROOT` or runs `lean --print-prefix` (explicitly noting that `lean` in `PATH` may be an Elan proxy). Lake (`Lake.findLeanInstall?` in `src/lake/Lake/Config/InstallPath.lean` and `src/lake/Lake/Config/Env.lean`) detects the installation from `LEAN_SYSROOT`, `LEAN`, or `PATH`, records `ELAN_TOOLCHAIN` (or `Lean.toolchain`), and populates `LEAN_SYSROOT`, `LEAN_PATH`, `LEAN_SRC_PATH`, `PATH`, and shared-library paths for `lake env`, `lake lean <file>`, and `lake serve`.

### 2. Diagnostic Object Model, Severity Lifecycle, and `lean --json` Wire Protocol

Basis: **source + execution + derived** (`src/Lean/Message.lean`, `src/Lean/Log.lean`, `src/Lean/Language/Basic.lean`, `src/Lean/Data/Position.lean`, `src/Lean/Data/Json/FromToJson/Basic.lean`, `src/Lean/Elab/Deriving/FromToJson.lean`, `src/Lean/Data/Lsp/Diagnostics.lean`, `src/Lean/Widget/InteractiveDiagnostic.lean`, `src/Lean/Server/FileWorker.lean`, `src/Lean/ErrorExplanation.lean`, `src/lake/Lake/Build/Actions.lean`).

#### In-Memory `Message`, `MessageData`, Named Errors, and `MessageLog`

In `src/Lean/Message.lean` (at both `v4.30.0-rc2` blob `a7f76198c582d1d2032bb24d13ad4cb7a272fa57` and `v4.34.1` line 44 / line 658, SHA-256 `09277320b843288e...`), `MessageSeverity` is a three-constructor inductive type:

```lean
inductive MessageSeverity where
  | information
  | warning
  | error
```

`BaseMessage α` carries `fileName : String`, `pos : Position`, `endPos : Option Position := none`, `keepFullRange : Bool := false`, `severity : MessageSeverity := .error`, `isSilent : Bool := false`, `caption : String := ""`, and `data : α`. An elaborator `Message` is `BaseMessage MessageData`, where `MessageData` is a rich tree containing formatted text with `Info` annotations, tactic goals, widgets, saved `PPContext` environments, tags, traces, and lazy closures. `MessageData.kind` extracts the outer tag name through context wrappers.

User-facing named errors encode their identifier into `MessageData.kind` by appending the `_namedError` suffix (`kindOfErrorName` / `errorNameOfKind?` / `Message.errorName?`). Separate `ErrorExplanation.Metadata` entries in an environment extension (`src/Lean/ErrorExplanation.lean`) record the summary, introducing version, default severity, and optional removal version.

Messages accumulate per command in `MessageLog`, which maintains:

- `reported : PersistentArray Message` — messages already flushed by incremental reporting;
- `unreported : PersistentArray Message` — newly logged messages awaiting emission; and
- `loggedKinds : NameSet` — kinds recorded for duplicate suppression.

`MessageLog.add` and standard iterators (`toList`, `toArray`) operate on `unreported`, `markAllReported` moves `unreported` into `reported`, and `MessageLog.hasErrors` checks both `reported` and `unreported` for any message with `severity == .error`.

#### `lean --json` Framing and `SerialMessage` Schema

When `jsonOutput = true`, `SnapshotTree.runAndReport` traverses the snapshot tree in preorder and calls `Language.reportMessages` (`src/Lean/Language/Basic.lean`, lines 291–345). For each message in `msgLog.unreported` where `isSilent == false`, `msg.toJson` invokes `Message.serialize` (which renders `msg.data.toString` and copies `msg.kind`) and encodes the resulting `SerialMessage` via its derived `ToJson` instance (`IO.println j.compress`) as one compact JSON object line on **stdout**. Executed on both `v4.30.0-rc2` and `v4.34.1`, every JSON diagnostic line has the exact 9-field schema below:

| Field | JSON Type | Semantics and Derivation Rules |
| --- | --- | --- |
| `fileName` | `string` | Source file name passed to the frontend (relative or absolute as invoked). |
| `pos` | `{"line": Nat, "column": Nat}` | Start `Lean.Position`: **1-based** `line` and **0-based** Unicode character `column` (`FileMap.toPosition`). |
| `endPos` | `null` or `{"line": Nat, "column": Nat}` | Optional end `Lean.Position`. Because the field is named `endPos` (not ending in `?`), Lean's `ToJson` deriving always emits the key, encoding `none` as `null`. |
| `keepFullRange` | `boolean` | Whether clients should preserve the full multi-line range rather than truncating display to the first line. |
| `severity` | `"information"` \| `"warning"` \| `"error"` | Derived `ToJson` string of `MessageSeverity` (after `warningAsError` or `-E` override). |
| `isSilent` | `boolean` | Silent flag (`Language.reportMessages` filters out `isSilent = true` before printing, so emitted CLI JSON lines have `false`). |
| `caption` | `string` | Optional message caption separate from the body. |
| `data` | `string` | Eagerly rendered `MessageData.toString` human-readable body (all structured widgets, tags, and `Expr` trees are flattened). |
| `kind` | `string` | String form of `MessageData.kind` (e.g., `""` for `[anonymous]`, `"Elab.synthPlaceholder"`, or `"..._namedError"`). |

Key protocol boundaries for `lean --json` consumers:

- **Coordinate mismatch with LSP**: `SerialMessage` uses `Lean.Position` (1-based line, 0-based Unicode scalar character offset), whereas LSP uses 0-based line and 0-based UTF-16 code units.
- **`printMessageEndPos` independence**: `reportMessages` passes `printMessageEndPos.get opts` only to the plain-text `msg.toString includeEndPos` branch; JSON mode calls `msg.toJson` directly and always includes `endPos`.
- **Non-JSON process output**: `--json` only changes `Language.reportMessages`. Bad CLI flags, unknown `#lang` headers (`src/Lean/Shell.lean`, lines 420–517), or user `IO` during elaboration still write plain text to stdout or stderr. Lake's own consumer (`Lake.compileLeanModule` in `src/lake/Lake/Build/Actions.lean`, lines 28–84) splits stdout by line, parses valid `SerialMessage` JSON lines structurally, retains non-JSON stdout lines and stderr as plain text, and checks the process exit code independently.

#### Language-Server `InteractiveDiagnostic` and LSP Conversion

Inside `lean --server`, `Language.Snapshot.Diagnostics` (`src/Lean/Language/Basic.lean`) pairs `msgLog` with a mutable cache slot for `InteractiveDiagnostic` (`Lsp.DiagnosticWith InteractiveMessage`, defined in `src/Lean/Widget/InteractiveDiagnostic.lean` and `src/Lean/Data/Lsp/Diagnostics.lean`). `Widget.msgToInteractiveDiagnostic` differs from batch `SerialMessage` in four ways:

1. **Severities**: LSP `DiagnosticSeverity` has 4 values (`error = 1`, `warning = 2`, `information = 3`, `hint = 4`), but `msgToInteractiveDiagnostic` maps `MessageSeverity` only to `error`, `warning`, or `information` (never `hint`).
2. **Display range truncation**: `Message.pos` and `Message.endPos` map to LSP `fullRange`. Unless `keepFullRange` is `true`, multi-line messages have their primary LSP `range` truncated to the end of the first line while `fullRange?` preserves the full span; a missing `endPos` becomes a zero-width range at `pos`.
3. **Codes and tags**: `source?` is set to `"Lean 4"`, named errors (`errorNameOfKind?`) populate `code?`, deprecation and unused-variable kinds map to LSP `deprecated` and `unnecessary` tags, and Lean-specific kinds map to `unsolvedGoals` or `goalsAccomplished` tags.
4. **Silent messages**: `isSilent` becomes `isSilent? := some true`; `FileWorker` filters silent messages unless the client advertises Lean's silent-diagnostic capability, and flattens `InteractiveMessage` to `String` via `InteractiveDiagnostic.toDiagnostic` when emitting `textDocument/publishDiagnostics`.

### 3. Warnings-as-Errors Mechanisms (`warningAsError`, `lean -E`, and `lake --wfail`)

Basis: **source + checked-in tests + derived** (`src/Lean/Log.lean`, `src/Lean/Message.lean`, `src/Lean/Shell.lean`, `src/Lean/Language/Basic.lean`, `src/Lean/Elab/Frontend.lean`, `src/lake/Lake/CLI/Main.lean`, `src/lake/Lake/Util/Log.lean`, `src/lake/Lake/Build/Actions.lean`, `tests/elab_fail/warningAsError.lean`, `tests/lake/tests/logLevel/test.sh`).

Lean and Lake expose three non-equivalent warning-enforcement mechanisms:

| Mechanism | Layer Where Applied | Modifies Stored `Message.severity`? | Affects `MessageLog.hasErrors` During Elaboration? | Causes Batch / Build Nonzero Exit on Warning? | Propagated to `lean --server` Workers? |
| --- | --- | --- | --- | --- | --- |
| `set_option warningAsError true` / `-DwarningAsError=true` | `Lean.logAt` (`src/Lean/Log.lean`, lines 104–123) | **Yes** (`.warning` becomes `.error` at construction) | **Yes** (`hasErrors` inspects stored `.error` severity) | **Yes** (`runFrontend` returns `none`; `shellMain` exits nonzero; `.olean` suppressed) | **Yes** (`-D` is appended to `forwardedArgs` in `Shell.lean`, lines 392–396, 463–468) |
| `lean -E kind` / `--error=kind` | `Language.reportMessages` (`src/Lean/Language/Basic.lean`, lines 305–345) | **No** (stored message remains `.warning`) | **No** (runs after snapshot elaboration completes) | **No** (`numErrors` is incremented *before* `severityOverrides` rewrites output severity) | **No** (`ShellOptions.errorOnKinds` is passed only to batch `runFrontend`) |
| `lake --wfail` / `--fail-level=warning` | `LogIO.toBaseIO` (`src/lake/Lake/Util/Log.lean`, lines 596–638; `Lake/CLI/Main.lean`, lines 241–287) | **No** (Lean and Lake both log `.warning`) | **No** | **Yes** (Lake build fails after action when `cfg.failLv <= log.maxLv`) | **No** (Lake build-log policy; note `LoggerIO` does not enforce `failLv`) |

The ordering inside `Language.reportMessages` (`src/Lean/Language/Basic.lean`, lines 311–335) is critical for tool authors:

1. `reportMessages` checks the original `msg.severity` to increment `numErrors` (and triggers `IO.Process.exit 1` if `numErrors > maxErrors`).
2. Only after updating `numErrors` does `reportMessages` look up `severityOverrides.find? msg.kind` (populated from `-E kind` in `Elab.runFrontend`, `src/Lean/Elab/Frontend.lean`, lines 176–183) and replace `msg := { msg with severity := sev }` prior to calling `msg.toJson` or `msg.toString`.
3. Consequently, a warning promoted only by `-E kind` is printed on stdout with `"severity": "error"`, yet `runAndReport` returns `hasErrors = false` if no originally-error messages were logged, and `lean` exits `0`. An automated verifier must therefore use `-DwarningAsError=true` (or check process exit status plus warning counts) rather than relying on `-E` or serialized `"severity": "error"` alone.

### 4. Diagnostic Width and Formatting Controls (`v4.30.0-rc2` and `v4.34.1` 20-Cell Matrix)

Basis: **source + execution + checked-in tests** (`src/Lean/Message.lean`, `src/Init/Data/Format/Basic.lean`, `src/Init/Data/ToString/Basic.lean`, `src/Lean/Data/Format.lean`, `src/Lean/PrettyPrinter/Formatter.lean`, `src/Lean/PrettyPrinter/Delaborator/Options.lean`, `support/lean-diagnostic-format-controls/source-map.json`, `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/results.json`, `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/source-map.json`, `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/source-diff.patch`).

#### Source Mechanism: Why `-Dformat.width` Does Not Wrap Ordinary Batch Diagnostics

In `src/Lean/Message.lean`, `MessageData.toString` renders structured message data via:

```lean
protected def toString (msgData : MessageData) : BaseIO String := do
  return toString (← msgData.format)
```

`ToString Format` (`src/Init/Data/ToString/Basic.lean`) delegates to `Std.Format.pretty f` using its default parameter `width : Nat := defWidth` (`120` in `src/Init/Data/Format/Basic.lean`). Although `src/Lean/Data/Format.lean` registers the option `format.width : Nat` (default `120`) and provides `Format.pretty' f o`, `MessageData.toString` does not call `Format.pretty'` and does not thread `Options` into the final string conversion.

By contrast, when `pp.oneline` (default `false`) is set to `true`, `PrettyPrinter.Formatter.format` (`src/Lean/PrettyPrinter/Formatter.lean`) runs `OneLine.pretty f (Std.Format.format.width.get options)`, which truncates at the first newline and appends ` [...]`. Thus `format.width` acts as a truncation threshold under `pp.oneline=true` while leaving ordinary (`pp.oneline=false`) 120-column final rendering unchanged.

#### Cross-Version 20-Cell Option Execution Matrix (`v4.30.0-rc2` vs. `v4.34.1`)

The fixture `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/r448/Format.lean` combines expressions from `tests/elab/ppOneline.lean` and `tests/elab/ppUnicode.lean`, a nested `let`, and a deliberate trailing unknown identifier (exiting `1` in all 20 cells). Executed serially across both `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) and `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), all 20 stdout outputs in `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/raw/r448/` are **byte-identical between `v4.30.0-rc2` and `v4.34.1`**:

| Formatting Control Tested on `Format.lean` | Observed Behavior Under Both `v4.30.0-rc2` and `v4.34.1` |
| --- | --- |
| `format.width=10` vs. `120` with `pp.oneline=false` | Batch JSON output is byte-identical; final `Format.pretty` still wraps at the hardcoded 120-column default. |
| `format.width=10` vs. `120` with `pp.oneline=true` | Batch JSON changes: width `10` truncates the list and lambda expressions with `[...]`. |
| `format.indent=2` vs. `8` | Construction-time syntax indentation changes nested `let` continuation lines between 2 and 8 spaces. |
| `pp.unicode=false` vs. `true` | `→` and `∧` render as `->` and `/\` when `pp.unicode=false` (note: `format.unicode` in `Lean/Data/Format.lean` does not govern syntax token spelling). |
| `pp.unicode.fun=false` vs. `true` | With `pp.unicode=true`, lambda `=>` renders as `↦`; with `pp.unicode=false`, ASCII `=>` is forced regardless of `pp.unicode.fun`. |
| `pp.mvars.anonymous=false` vs. `true` | Generated metavariable `?m.1` renders anonymously as `?_` when `false` and with its numeric suffix when `true`. |
| `pp.fvars.anonymous=false` vs. `true` | No output change on this fixture because no loose generated free variable (`_fvar.*`) is exposed in the diagnostic (used in `#guard_msgs` to suppress loose fvar numbering). |
| `printMessageEndPos=false` vs. `true` | Plain-text error header changes from `10:7` to `10:7-10:35`; `--json` output is byte-identical (`endPos` is always serialized). |

### 5. Batch Diagnostic Normalization Oracle vs. Semantic Equivalence (`v4.30.0-rc2` and `v4.34.1`)

Basis: **execution + derived** (`support/lean-batch-diagnostic-normalization-oracle/run-probe.py`, `support/lean-batch-diagnostic-normalization-oracle/results/observations.json`, `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/results.json`, `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/raw/r444/`).

To test whether normalizing `fileName` in `lean --json` output suffices as a relocation or verification oracle, five single-file modules (`support/lean-batch-diagnostic-normalization-oracle/{a,b,c,d,e}/Probe.lean`, duplicated under `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/r444/`) were compiled with `lean --json -o .../Probe.olean .../Probe.lean` and queried with a fixed consumer (`support/lean-batch-diagnostic-normalization-oracle/query/Query.lean`: `import Probe`, `#check arithmetic`, `#print axioms arithmetic`) under both `v4.30.0-rc2` and `v4.34.1`:

| Case | Input Difference Relative to `a` (`#check Nat.zero` + `theorem arithmetic : 1 + 1 = 2 := by decide`) | Compilation Exit Code | Filename-Normalized `--json` Diagnostics vs. `a` | `.olean` Bytes Within Same Version vs. `a` | `.olean` Bytes Across `v4.30.0-rc2` vs. `v4.34.1` | Fixed Consumer Query (`#check arithmetic` / `#print axioms`) vs. `a` |
| --- | --- | --- | --- | --- | --- | --- |
| `a` (baseline) | Baseline (`a/Probe.lean`) | `0` | baseline | baseline (`cfad98ad...` on `v4.30.0-rc2`) | differs across versions | `arithmetic : 1 + 1 = 2`, no axioms |
| `a-repeat` / `a-output-only` | Same `a/Probe.lean` compiled a second time or to a different `-o` path | `0` | equal | **equal** (`cfad98ad...` on `v4.30.0-rc2`) | differs across versions | equal |
| `b` | Byte-identical source at `b/Probe.lean` | `0` | **equal** (raw JSON differs only in `fileName`) | **different** (`f5d53027...` on `v4.30.0-rc2`) | differs across versions | **equal** (byte-identical consumer JSONL) |
| `c` | `#check Nat.succ` replaces `#check Nat.zero`; same theorem | `0` | different `information` message; equal warning/error set | **different** | differs across versions | **equal** (`arithmetic : 1 + 1 = 2`, no axioms) |
| `d` | False proposition `theorem arithmetic : 1 + 1 = 3 := by decide` | `1` | extra `decide` error diagnostic | absent (no `.olean` written) | absent | unavailable |
| `e` | Different true proposition `theorem arithmetic : 2 + 2 = 4 := by decide` with `#check Nat.zero` | `0` | **equal** (identical normalized JSONL to `a`) | **different** | differs across versions | **different** (`arithmetic : 2 + 2 = 4` vs. `1 + 1 = 2`) |

Two architectural invariants follow from this execution matrix:

1. **Input-path sensitivity of `.olean` vs. output-path invariance**: Compiling the exact same input path `a/Probe.lean` twice (`a-repeat`) or to a different output path (`a-output-only`) produced identical `.olean` bytes within each compiler version, whereas compiling byte-identical source from `b/Probe.lean` changed both raw `SerialMessage.fileName` and the emitted `.olean` bytes.
2. **Unsoundness of normalized compilation diagnostics as a standalone theorem oracle**: Case `e` (`2 + 2 = 4`) exits `0` and emits the exact same filename-normalized `--json` compilation stream as case `a` (`1 + 1 = 2`), because successful theorem declarations emit no diagnostic and both files share `#check Nat.zero`. All 11 stdout streams in this suite are also byte-identical between `v4.30.0-rc2` and `v4.34.1`. A sound verification or cache oracle must therefore pair process exit status and warning/error checks with an explicit check of the target theorem/environment (such as the consumer query), rather than trusting compilation diagnostic equality alone.

## Boundaries

- **Elan proxy precedence (`not examined`)**: `Lean.Shell` and Lake consume an already-selected toolchain or `ELAN_TOOLCHAIN`/`LEAN_SYSROOT` environment; Elan's own proxy binary resolution, directory overrides, and download rules belong to the independent Elan repository and were **not examined**.
- **Internal `.olean` byte-offset attribution (`not examined`)**: The normalization probe proves that relocating `a/Probe.lean` to `b/Probe.lean` changes `.olean` bytes while changing only `-o` does not, and that `v4.30.0-rc2` and `v4.34.1` emit different `.olean` hashes, but the exact serialized field offsets inside `.olean` were **not examined** in this package.
- **LSP hint severity from non-`Message` producers (`not examined`)**: `MessageSeverity` has no `hint` constructor and `Widget.msgToInteractiveDiagnostic` never produces LSP severity `4` (`hint`) (**known not to apply** to standard `Message` conversion), though whether custom server widgets ever construct `Lsp.DiagnosticSeverity.hint` directly was **not examined**.
- **Whole-process JSON framing (`known not to apply`)**: `lean --json` is **known not to apply** to CLI usage errors, `#lang` failures, or arbitrary elaboration `IO` writes on stdout/stderr; consumers must tolerate non-JSON lines and inspect process exit status.
- **Canonical version-independent diagnostic prose (`unsupported`)**: Lean explicitly leaves human-rendered `SerialMessage.data` sensitive to `pp.*` options, `format.indent`, `pp.oneline` + `format.width`, and compiler version changes; using `SerialMessage.data` as a canonical version-independent serialization is **unsupported**.
- **`LoggerIO` warning failure in Lake (`known not to apply`)**: Lake's `LogConfig.failLv` (`--wfail`) is documented in `src/lake/Lake/Util/Log.lean` as **known not to apply** to `LoggerIO` streaming contexts.

## Evidence

### Primary Upstream Source (`leanprover/lean4`)

- **CLI entry points, `--json`, `-D`, `-E`, and `runFrontend`**:
  - `src/Lean/Shell.lean` (`v4.30.0-rc2` blob `2ff5c4b0c82f876ddd4384c9c20dcaefebc1b90e`; `v4.34.1` recorded in `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/source-map.json`): `ShellOptions` (lines 227–247), `-D` / `setConfigOption` and `forwardedArgs` (lines 272–284, 392–396), `--json` (lines 382–385), `-E` / `--error` (lines 418–424), `--server` / `--worker` dispatch (lines 463–468), and `runFrontend` invocation and exit status (lines 530–557).
  - `src/Lean/Elab/Frontend.lean` (`v4.30.0-rc2` blob `fd3760667db96a351b4f654720193c89bbee356e`): `runFrontend`, `errorOnKinds` -> `severityOverrides` construction, snapshot reporting, `.olean`/`.ilean` output gating (lines 136–220).
  - `src/Lean/Util/Path.lean` (`v4.30.0-rc2` blob `b2af1878ec01bcf790f31401c0d46efd6b94c840`): `findOLean`, `LEAN_PATH`, `LEAN_SRC_PATH`, `moduleNameOfFileName`, `findSysroot`.
- **Diagnostic objects, `SerialMessage`, `Language.reportMessages`, and LSP conversion**:
  - `src/Lean/Message.lean` (`v4.30.0-rc2` blob `a7f76198c582d1d2032bb24d13ad4cb7a272fa57`; `v4.34.1` 901 lines, SHA-256 `09277320b843288e...`): `MessageSeverity` (line 44 in `v4.34.1`), `BaseMessage` and `SerialMessage` (lines 427–451 in `v4.30.0-rc2`), `MessageData.toString` and `Message.serialize` / `Message.toJson` (lines 542–566 in `v4.30.0-rc2`), `MessageLog` and `hasErrors` (lines 568–623 in `v4.30.0-rc2`, line 658 in `v4.34.1`).
  - `src/Lean/Log.lean` (`v4.30.0-rc2` blob `3d40ada008ff57e9c82568661f3c4ecf928f9280`): `warningAsError` registration (lines 52–60) and `logAt` severity promotion (lines 104–123).
  - `src/Lean/Language/Basic.lean` (`v4.30.0-rc2` blob `08f9b688fc869224c316175220403c2aeb5eb415`): `Snapshot.Diagnostics`, `reportMessages` (`printMessageEndPos`, `numErrors` counting before `severityOverrides`, `maxErrors` exit), `SnapshotTree.runAndReport` (lines 291–345).
  - `src/Lean/Data/Position.lean` (`v4.30.0-rc2` blob `f5eae212ed37f753a495437dc7b0c7f6cfeaa945`): `Position` (lines 11–16) and `FileMap.toPosition` (lines 60–98).
  - `src/Lean/Data/Lsp/Diagnostics.lean` (`v4.30.0-rc2` blob `d15c1ce80d3699be7a5d92ebf6cea6725c3a4b34`) and `src/Lean/Widget/InteractiveDiagnostic.lean` (`v4.30.0-rc2` blob `5fc9e0b22a3195c7843f7a45b7c0bdab870fce08`): `DiagnosticSeverity`, `DiagnosticWith`, `InteractiveDiagnostic`, `msgToInteractiveDiagnostic`.
- **Formatting and Lake build/log controls**:
  - `src/Init/Data/Format/Basic.lean` (blob `e0dbb5fa8be5578f8904e0e5a36decbcdf3fbec4`), `src/Init/Data/ToString/Basic.lean` (blob `505aa15ca363d66f70f850134b008d98c93df184`), `src/Lean/Data/Format.lean` (blob `9bcb44e2ce7c6848dd1f1d7a3f2801ccc54b4f42`), `src/Lean/PrettyPrinter/Formatter.lean` (blob `2067634ee568e8e1480cece32b51eb197d04468c`), `src/Lean/PrettyPrinter/Delaborator/Options.lean` (blob `4475cbe095664e277abe916a551a472f7177a2fb`).
  - `src/lake/Lake/CLI/Main.lean` (`--wfail`, `--fail-level`, lines 241–287), `src/lake/Lake/Util/Log.lean` (`LogEntry.ofSerialMessage`, `LogConfig.failLv`, `LogIO.toBaseIO`, lines 115–167, 596–638), `src/lake/Lake/Build/Actions.lean` (`compileLeanModule` at line 28 in `v4.30.0-rc2` and line 29 in `v4.34.1`, SHA-256 `9c7d7101f89eb1d0...`).

### Preserved Package Support Artifacts and Execution Records

- **Formatting controls source map (`v4.30.0-rc2`)**: `support/lean-diagnostic-format-controls/source-map.json` (observed 2026-09-27).
- **Batch diagnostic normalization oracle (`v4.30.0-rc2`, observed 2026-09-28)**:
  - Probe runner and inputs: `support/lean-batch-diagnostic-normalization-oracle/run-probe.py`, `support/lean-batch-diagnostic-normalization-oracle/a/Probe.lean`, `support/lean-batch-diagnostic-normalization-oracle/b/Probe.lean`, `support/lean-batch-diagnostic-normalization-oracle/c/Probe.lean`, `support/lean-batch-diagnostic-normalization-oracle/d/Probe.lean`, `support/lean-batch-diagnostic-normalization-oracle/e/Probe.lean`, `support/lean-batch-diagnostic-normalization-oracle/query/Query.lean`.
  - Recorded JSONL outputs, `.olean` specimens, and digest summary: `support/lean-batch-diagnostic-normalization-oracle/results/observations.json`, `support/lean-batch-diagnostic-normalization-oracle/results/a.jsonl`, `support/lean-batch-diagnostic-normalization-oracle/results/a-repeat.jsonl`, `support/lean-batch-diagnostic-normalization-oracle/results/a-output-only.jsonl`, `support/lean-batch-diagnostic-normalization-oracle/results/b.jsonl`, `support/lean-batch-diagnostic-normalization-oracle/results/c.jsonl`, `support/lean-batch-diagnostic-normalization-oracle/results/d.jsonl`, `support/lean-batch-diagnostic-normalization-oracle/results/e.jsonl`, `support/lean-batch-diagnostic-normalization-oracle/results/a-consumer.jsonl`, `support/lean-batch-diagnostic-normalization-oracle/results/b-consumer.jsonl`, `support/lean-batch-diagnostic-normalization-oracle/results/c-consumer.jsonl`, `support/lean-batch-diagnostic-normalization-oracle/results/e-consumer.jsonl`, and `.olean` files under `support/lean-batch-diagnostic-normalization-oracle/results/{a,a-output-only,b,c,e}/Probe.olean`.
- **Cross-version `v4.30.0-rc2` to `v4.34.1` 62-run batch normalization and option-matrix execution (observed 2026-10-01)**:
  - Master results, source diff, and offline/online scripts: `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/results.json`, `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/source-map.json`, `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/source-diff.patch`, `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/probe.py`, `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/check.py`.
  - Fixtures and raw per-version outputs: `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/r444/`, `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/r448/Format.lean`, `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/raw/r444/`, and `support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/raw/r448/`.
  - Resource telemetry across all 62 recorded child processes: minimum reclaimable memory `22.0371%`, minimum free disk `2,276,118,528` bytes, maximum owned package bytes `260,572`, maximum sampled child RSS `402,256 KiB`, maximum child duration `1.61 s` (with a preliminary `import Lean` attempt terminated by the harness guard at `1,051,648 KiB` RSS and excluded from the 62 core runs).

## Revalidation

1. **Offline verification of retained `v4.30.0-rc2` and `v4.34.1` evidence (no Lean binary required)**:
   ```bash
   python3 -B support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/check.py
   ```
   This verifies all fixture and source-blob SHA-256 digests, all 62 recorded command outputs and exit codes, resource-admission bounds, the 5-case normalization/consumer equivalence matrix, the 20-cell formatting option matrix, and cross-version stdout byte identity between `v4.30.0-rc2` and `v4.34.1`.

2. **Live batch re-execution against a new Lean toolchain**:
   - Wrap CLI Lean invocations in `anneal-lean-run` (or run the guarded probe scripts in a disposable copy of the package):
     ```bash
     LEAN_BIN=/path/to/lean python3 -B support/lean-batch-diagnostic-normalization-oracle/run-probe.py
     python3 -B support/lean-batch-diagnostics-r444-r448-430rc2-to-4341/probe.py
     ```
   - Check whether `a` and `b` still produce equal filename-normalized JSON diagnostics and consumer query outputs while `a` and `e` still collide on compilation diagnostics and diverge on the consumer query.
   - Check whether `format.width=10` vs. `120` still leaves `pp.oneline=false` JSON output unchanged while truncating `pp.oneline=true` with `[...]`.

3. **Targeted source diff for new Lean revisions**:
   - Diff `src/Lean/Message.lean` (`MessageSeverity`, `BaseMessage`, `SerialMessage`, `MessageData.toString`, `Message.serialize`), `src/Lean/Log.lean` (`warningAsError` in `logAt`), `src/Lean/Language/Basic.lean` (`reportMessages` error-counting order relative to `severityOverrides`), `src/Lean/PrettyPrinter/Formatter.lean` (`OneLine.pretty`), and `src/lake/Lake/Build/Actions.lean` (`compileLeanModule`).
