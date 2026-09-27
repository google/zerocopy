# Lean warnings-as-errors mechanisms at v4.30.0-rc2

## Summary

Lean v4.30.0-rc2 has three distinct mechanisms that are easy to conflate.

`warningAsError` changes a warning into an error when Lean logs the message. That change enters the message log itself, so it affects `MessageLog.hasErrors`, error-sensitive elaborator behavior, command-line success, artifact emission, and the severity later exposed by the language server.

`lean -E kind` / `--error=kind` is narrower and later. It changes the severity used when the command-line frontend reports messages of a selected internal kind, but the frontend counts errors before applying that reporting override. A warning promoted only by `-E` is therefore printed or serialized as an error without, by itself, making the Lean invocation fail.

Lake's `--wfail` is different again. It sets Lake's build-log failure threshold to `warning`. Lake explicitly documents that this does not convert warnings to errors and does not necessarily abort at the point the warning is logged. During Lean builds, Lake invokes Lean with `--json`, converts each serialized Lean message severity to the corresponding Lake log level, and can therefore fail a build because an ordinary Lean warning reached the Lake log.

For Anneal, the important distinction is **severity conversion inside Lean** versus **command-line reporting override** versus **outer build-policy failure**. They have different effects on proofs, incremental/server behavior, process status, and diagnostics.

## Applicability

The Lean and Lake findings apply to `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, the source revision corresponding to Lean `v4.30.0-rc2`. Current Anneal `main` at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` selects `leanVersion = "v4.30.0-rc2"` in `anneal/flake.nix`, so this is the Lean release relevant to the current Anneal toolchain selection.

This report describes mechanisms available in the pinned Lean/Lake toolchain. It does **not** claim that current Anneal enables any particular warnings-as-errors policy. The redesign deliberately leaves many build and verification policy choices open.

The investigation used source inspection and checked-in upstream tests. No fresh Lean or Lake execution was performed in this environment.

## Findings

### `warningAsError` changes the stored Lean diagnostic severity

Lean registers `warningAsError : Bool` with default `false`. `Lean.logAt` checks the current options and rewrites `.warning` to `.error` before constructing and logging the `Message`. The standard `logWarningAt`, `logNamedWarningAt`, `logWarning`, and `logNamedWarning` helpers flow through this path.

Basis: source.

[`Lean/Log.lean` registers the option](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Log.lean#L52-L60) and [`logAt` performs the severity conversion](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Log.lean#L104-L123).

This timing matters. `MessageLog.hasErrors` checks the severities already stored in the log. Once `warningAsError` has rewritten a warning to `.error`, later code sees an actual error rather than a warning that only looks like one when printed.

Basis: source + derived.

[`MessageLog.hasErrors` tests stored message severity](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Message.lean#L618-L623).

The batch frontend waits for the snapshot tree, reports it, and returns no environment when errors were reported. The shell then exits nonzero when the frontend returned no environment. Thus a warning converted by `warningAsError` participates in ordinary batch failure and prevents later output-module generation through the same path as other errors.

Basis: source + derived.

[`runFrontend` uses the snapshot error result as a success gate](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Elab/Frontend.lean#L176-L199); [`shellMain` maps frontend success to process status](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L533-L557).

The checked-in `tests/elab_fail/warningAsError.lean` fixture exercises both a deprecation warning and an unused-variable linter warning. Before `set_option warningAsError true`, the deprecated use is expected as a warning; afterward the same class of diagnostic and the linter diagnostic are expected as errors.

Basis: source + preserved upstream test expectation.

[Fixture](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/tests/elab_fail/warningAsError.lean#L1-L15) and [expected output](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/tests/elab_fail/warningAsError.lean.out.expected#L1-L6).

The implementation point is `logAt`, so the strongest source-grounded statement is about warnings emitted through that logging path. Code that constructs or transports `Message` values without passing through `logAt` needs separate inspection before assuming the option rewrites it.

### `-DwarningAsError=true` is the command-line form of the same Lean option

The Lean shell's `-D name=value` path parses a configuration option into `leanOpts`. It also appends the same `-D...` argument to `forwardedArgs`. When the shell starts server/watchdog mode, it passes `forwardedArgs` to the watchdog. Consequently, a command-line `-DwarningAsError=true` is not merely a batch-output policy: it supplies the actual Lean option and is propagated into the server-worker launch path.

Basis: source + derived.

[`-D` parses configuration values](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L272-L284), [the `-D` handler adds the option to `forwardedArgs`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L392-L396), and [the server path receives forwarded arguments](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L463-L468).

Because the option changes severity at logging time, server snapshots created under that option retain the promoted `.error` severity. The language server does not acquire a separate "build failed" state from this fact; it continues to operate as a server while reporting error diagnostics. The important effect is that downstream consumers of the message log see error severity and error-sensitive elaborator code can observe `hasErrors`.

Basis: source + derived.

### `-E kind` is a reporting override, not the same failure mechanism

Lean's shell also exposes `-E, --error=kind`, described as "report Lean messages of kind as errors." It records the requested internal message kinds in `ShellOptions.errorOnKinds` and passes them only to the batch `runFrontend` call.

Basis: source.

[CLI help and option state](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L164-L181); [`-E` handling](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L419-L424); [batch frontend call](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Shell.lean#L533-L535).

The frontend turns these names into `severityOverrides`. However, `reportMessages` increments its error counter from the message's original severity **before** replacing the severity used for output. `SnapshotTree.runAndReport` returns whether that original-severity counter is nonzero.

Basis: source + derived.

[Frontend constructs the overrides](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Elab/Frontend.lean#L176-L183); [`reportMessages` counts before applying the override](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Language/Basic.lean#L305-L334); [`runAndReport` returns from that counter](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Language/Basic.lean#L336-L345).

Therefore, if a message was a warning in the stored message log and is changed to `.error` only by `-E`, that override changes text/JSON reporting but does not add to the frontend's error count and does not by itself make the shell exit nonzero. It also happens after elaboration has produced the snapshot diagnostics, so it cannot retroactively affect `MessageLog.hasErrors` decisions made during elaboration.

`-E` is also not added to `forwardedArgs`, whereas `-D` is. The server/watchdog branch receives only `forwardedArgs`. On this source revision, `-E` is therefore a command-line frontend reporting feature rather than a server-worker configuration mechanism.

Basis: source + derived.

This distinction is especially important for an agent that wants "warnings must make verification fail": `-E` can make output *look* error-like without establishing that property.

### Lake `--wfail` fails on warning-level log entries without rewriting them

Lake has its own ordered log levels: trace, info, warning, error. Its `failLv` defaults to `error`. `--wfail` sets `failLv := .warning`; the more general `--fail-level=lv` sets the threshold explicitly. Lake's help describes `--wfail` as equivalent to `--fail-level=warning`.

Basis: source.

[Lake option state and CLI parsing](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/CLI/Main.lean#L52-L83) and [`--wfail` / `--fail-level`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/CLI/Main.lean#L241-L287).

Lake's logging contract explicitly says the threshold does **not** convert such entries to errors and does not necessarily abort execution when warnings are logged. For `LogIO`, failure is computed after the action as `a?.isNone ∨ cfg.failLv ≤ log.maxLv`.

Basis: source.

[`LogConfig.failLv` contract and `LogIO.toBaseIO`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Util/Log.lean#L596-L638).

This makes `--wfail` an outer build-policy mechanism. It can fail because of Lake's own warnings as well as warnings originating in Lean, and the warning remains a warning in the Lake log.

The bundled Lean build action runs Lean with `--json`. Each serialized Lean message is parsed and sent through `logSerialMessage`; `LogEntry.ofSerialMessage` maps Lean's `MessageSeverity.warning` directly to Lake's `LogLevel.warning`. Thus an ordinary Lean warning that reaches this path is sufficient to reach Lake's warning failure threshold under `--wfail`.

Basis: source + derived.

[Lake invokes Lean with `--json` and logs serialized messages](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Actions.lean#L53-L78); [serialized severity maps directly to a Lake log level](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Util/Log.lean#L115-L123) and [`LogEntry.ofSerialMessage`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Util/Log.lean#L151-L167).

The upstream Lake test suite also has a log-level fixture that expects warning-producing targets to fail under `--wfail`.

Basis: preserved upstream test source.

[Lake log-level test](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/tests/lake/tests/logLevel/test.sh#L16-L27).

One boundary is explicit in Lake's source: not every logging monad supports `LogConfig.failLv`; `LoggerIO` is called out as an exception. Do not generalize `--wfail` into a theorem that every warning from every Lake code path necessarily fails every command.

### The mechanisms answer different questions

For Anneal, these mechanisms compose but are not interchangeable:

| Mechanism | Where it acts | Changes stored Lean severity? | Can affect Lean elaboration's `hasErrors`? | Can make batch/build fail on a warning? |
| --- | --- | --- | --- | --- |
| `set_option warningAsError true` / `-DwarningAsError=true` | Lean logging | Yes | Yes | Yes, through ordinary Lean error handling |
| `lean -E kind` | Batch frontend reporting | No | No | No, not by itself |
| `lake --wfail` / `--fail-level=warning` | Lake log/build policy | No | No | Yes, at the Lake layer |

Basis: derived from the source paths above.

The table does not imply that every possible warning producer flows through each mechanism. It identifies the semantics of the mechanisms themselves.

## Boundaries

- **No fresh execution.** This run did not execute Lean or Lake. Checked-in tests provide preserved upstream behavioral evidence, but the report does not claim a newly reproduced runtime result.
- **Not a warning inventory.** This report does not enumerate every Lean warning kind, linter, diagnostic option, or warning-suppression control.
- **`warningAsError` implementation boundary.** The source rewrite occurs in `Lean.logAt`; a diagnostic introduced through another low-level path may require separate analysis.
- **`-E` kinds are internal message kinds.** This report establishes how the override is stored and applied, but it does not inventory which user-facing warnings map to which internal `Message.kind` names.
- **Server process status is out of scope.** The report establishes option forwarding and stored diagnostic severity. It does not claim that a server should terminate or that an editor client treats an error diagnostic as a failed build.
- **Lake coverage is not universal.** `LogConfig.failLv` applies where the relevant Lake action/logging path honors it. Lake itself documents that `LoggerIO` does not support this setting.
- **No current Anneal policy claim.** The current Anneal pin establishes applicability of the toolchain facts; it does not establish that Anneal currently enables `warningAsError`, `-E`, or `--wfail`.

## Evidence

Observation date: 2026-09-26.

Primary source identities:

- `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`):
  - `src/Lean/Log.lean`: `warningAsError`, `logAt`, warning logging helpers.
  - `src/Lean/Message.lean`: `MessageLog`, `MessageLog.hasErrors`, message kinds.
  - `src/Lean/Shell.lean`: `-D`, `-E/--error`, server forwarding, frontend invocation, exit status.
  - `src/Lean/Language/Basic.lean`: command-line diagnostic reporting, severity overrides, error counting.
  - `src/Lean/Elab/Frontend.lean`: snapshot reporting and success gate.
  - `src/lake/Lake/CLI/Main.lean`: `failLv`, `--wfail`, `--fail-level`.
  - `src/lake/Lake/Util/Log.lean`: log-level mapping and failure-threshold semantics.
  - `src/lake/Lake/Build/Actions.lean`: Lean `--json` invocation and serialized-message logging.
  - `tests/elab_fail/warningAsError.lean` and `.out.expected`: checked-in `warningAsError` fixture and expected output.
  - `tests/lake/tests/logLevel/test.sh`: checked-in Lake warning-failure fixture.
- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`:
  - [`anneal/flake.nix` selects `leanVersion = "v4.30.0-rc2"`](https://github.com/google/zerocopy/blob/41f5b37afe7060fd9fe08c00b200672cd76d77b9/anneal/flake.nix#L38-L46).

Evidence roles used here are **source** and **derived**. The checked-in fixtures and expected-output files are preserved source evidence about upstream's intended/tested behavior, not fresh **execution** evidence from this run. There is no normative external specification in this report.

## Revalidation

For another Lean revision, the cheapest source check is:

1. inspect `Lean.logAt` and confirm where `warningAsError` rewrites severity;
2. inspect `MessageLog.hasErrors`;
3. inspect `Language.reportMessages` / `SnapshotTree.runAndReport` and check whether error counting still occurs before or after any `-E` severity override;
4. inspect the shell's `-D` and `-E` handling plus server argument forwarding;
5. inspect Lake's `failLv`, `--wfail`, `LogIO.toBaseIO`, serialized-message severity mapping, and Lean build action.

A minimal capable-surface behavioral probe should then use one deterministic warning-producing file and compare:

- `lean file.lean`;
- `lean -DwarningAsError=true file.lean`;
- `lean -E <that-message-kind> file.lean`;
- a Lake build with and without `--wfail`.

Record both diagnostic severity and process/build status. A separate server probe should start Lean with `-DwarningAsError=true` and confirm that the same source warning is published as an error diagnostic while the server remains operational.

If `reportMessages` changes the order of error counting and severity override, re-evaluate the `-E` conclusion first; that ordering is the narrowest discriminator for the most surprising behavior in this report.