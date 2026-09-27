# Stable diagnostic width and formatting controls at Lean v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Lean exposes many options that change how expressions and syntax appear inside diagnostics, but it does not expose one option that makes the complete batch diagnostic string a canonical, version-independent format.

The most important width boundary is easy to miss. Lean registers `format.width` with the same default value as `Std.Format.defWidth`, 120 columns. However, the ordinary `MessageData.toString` path does not pass the current `Options` value to the final renderer. It formats the structured message to a `Format`, then converts that `Format` with its ordinary `ToString` instance. That instance calls `Format.pretty` with its default width, which is 120. Therefore `-Dformat.width=N` is not a general final-width control for ordinary batch diagnostic strings at this revision.

`format.width` still matters in narrower paths. Most notably, when `pp.oneline` is enabled, the syntax formatter runs its first-line elision algorithm using `format.width`; output beyond the first rendered line becomes ` [...]`. The checked-in `ppOneline.lean` tests deliberately vary `format.width` and observe different truncation points. The default `pp.oneline=false` avoids that lossy presentation mode.

Other options affect the contents of the message before final rendering. `format.indent` changes nesting inserted by the syntax formatter. `pp.unicode` and `pp.unicode.fun` change token spellings. Options such as `pp.fullNames`, `pp.explicit`, `pp.universes`, `pp.proofs`, `pp.deepTerms`, and `pp.maxSteps` can change what semantic material is shown at all. Lean also exposes narrow stabilization knobs: the descriptions of `pp.mvars.anonymous` and `pp.fvars.anonymous` explicitly support hiding generated numeric names, with the latter calling this useful for stabilizing `#guard_msgs` output. These knobs reduce particular sources of textual churn; they do not turn human-readable diagnostics into a canonical serialization.

For Anneal, use structured diagnostic fields for machine decisions whenever possible. `lean --json` preserves fields such as positions, severity, caption, and kind, but its `data` field is still `MessageData.toString` output. Pin the Lean revision and any presentation options that matter, avoid `pp.oneline` when complete diagnostic text is required, and do not make correctness depend on raw diagnostic-body byte equality unless Anneal deliberately defines and tests its own normalization protocol.

Basis: exact pinned source plus checked-in Lean regression tests. No fresh Lean process was executed.

## Applicability

This report covers the batch/frontend diagnostic rendering path and the pretty-printer options that materially affect diagnostic text at Lean `v4.30.0-rc2`, revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

It is complementary to three existing corpus reports:

- `lean-diagnostic-objects-severity-v4-30-0-rc2` describes the diagnostic object model and severity lifecycle;
- `lean-json-cli-protocol-v4-30-0-rc2` describes JSON-lines framing and the `SerialMessage` wire shape; and
- `lean-pretty-printing-roundtrip-v4-30-0-rc2` explains why pretty-printed Lean text is regenerated, option-sensitive source rather than a stable serialization.

This report narrows in on **which width and formatting controls affect the rendered diagnostic body, where they apply, and which apparent controls do not provide the stronger stability property an automated consumer might assume**.

The findings apply to the exact pin. Lean's pretty-printer options and message-rendering internals are implementation details that can change across revisions. No adjacent-version continuity is assumed.

## Findings

### Final batch message rendering uses `Format.pretty`'s 120-column default

`MessageData` is structured. `MessageData.format` first reduces that structure to a `Format`, retaining the pretty-printer choices made while formatting expressions, goals, traces, and nested message data.

The final conversion to text is separate. At this pin, `MessageData.toString` is:

```lean
protected def toString (msgData : MessageData) : BaseIO String := do
  return toString (← msgData.format)
```

The `ToString Format` instance calls `f.pretty`. `Std.Format.pretty` has a default width argument of `defWidth`, and `defWidth` is 120.

Therefore the ordinary batch diagnostic body has a final layout width of 120 unless the caller bypasses this conversion and explicitly renders the `Format` another way. The current `Options` object carried while constructing message data is not passed into this last `Format.pretty` call.

This distinction is the core answer to the checklist item. `format.width` exists, but it is not a universal final diagnostic-width setting.

Basis: **source** in `src/Lean/Message.lean`, `src/Init/Data/ToString/Basic.lean`, and `src/Init/Data/Format/Basic.lean`.

### `format.width` is a real option, but its effect is path-dependent

`src/Lean/Data/Format.lean` registers:

```lean
register_builtin_option format.width : Nat := {
  defValue := defWidth
  ...
}
```

and `defWidth` is 120. The same file provides `Format.pretty'`, which renders with `format.width.get o` when a caller explicitly supplies `Options`.

That mechanism is not used by `MessageData.toString`. Thus changing `format.width` does not, by itself, replace the final 120-column rendering step used by ordinary `Message` serialization.

The option can still change a diagnostic indirectly when an earlier pretty-printing stage consults it. The clearest pinned example is `pp.oneline`.

Basis: **source**.

### `pp.oneline` makes `format.width` a truncation control

`pp.oneline` defaults to `false` and is documented as eliding all but the first line of pretty-printer output.

When it is enabled, `PrettyPrinter.Formatter.format` calls:

```lean
OneLine.pretty f (Std.Format.format.width.get options)
```

`OneLine.pretty` stops at the first rendered newline and appends ` [...]`. Its result is then carried forward as a single-line `Format`.

The pinned `tests/elab/ppOneline.lean` fixtures vary `format.width` and expect different truncation points. For example, list and lambda output changes as the width moves across small thresholds.

For Anneal this yields a simple rule: **leave `pp.oneline` disabled when the complete diagnostic expression or proof state matters**. If one-line output is deliberately desired, `format.width` becomes part of the protocol because it changes where information is discarded.

Basis: **source + checked-in test**.

### `format.indent` affects the `Format` structure before final rendering

The syntax formatter reads `Std.Format.getIndent options` while constructing nested formats. It uses the value for category formatting and comment alignment. Unlike `format.width` in the ordinary final message path, this is a construction-time input: changing the indentation option can change the `Format` that is later rendered at 120 columns.

A deterministic diagnostic snapshot therefore needs to pin `format.indent` if it contains syntax or expressions whose formatter consults that option.

Basis: **source** in `src/Lean/PrettyPrinter/Formatter.lean` and `src/Lean/Data/Format.lean`.

### Unicode spelling is controlled by `pp.unicode`, not by width

`pp.unicode` defaults to `true`. `pp.unicode.fun` defaults to `false`. The syntax formatter's Unicode-token path reads `pp.unicode` when choosing between a Unicode symbol and its ASCII alternative.

The checked-in `tests/elab/ppUnicode.lean` file makes the effect concrete. The same logical expression can render as, for example, `→` versus `->`, `∧` versus `/\\`, and `≤` versus `<=`. Enabling `pp.unicode.fun` can render lambda syntax with `↦`; disabling `pp.unicode` forces the ASCII form even when the function-arrow preference is enabled.

Lean also registers a separate `format.unicode` option in `src/Lean/Data/Format.lean`. The diagnostic/syntax paths inspected here use `pp.unicode` for token spelling. Do not treat the similarly named `format.unicode` registration as evidence that setting it controls expression notation in diagnostics.

For stable snapshots, pin `pp.unicode` and any specialized spelling options Anneal relies on. Choosing ASCII may reduce display-environment concerns, but ASCII is not semantically more canonical than Unicode; the important property is that the choice is explicit.

Basis: **source + checked-in test**.

### Pretty-printer options can change semantic detail, not only whitespace

The pinned delaborator registers many `pp.*` options. Several alter which details appear in output:

- `pp.fullNames` changes name qualification;
- `pp.universes` changes universe display;
- `pp.explicit` changes implicit-argument display;
- `pp.proofs` and `pp.proofs.threshold` change whether proof terms are shown or replaced;
- `pp.deepTerms` and its threshold can replace nested terms;
- `pp.maxSteps` can stop delaboration and render omitted terms;
- `pp.notation`, `pp.match`, `pp.fieldNotation`, and related controls change presentation syntax;
- `pp.instantiateMVars` changes whether metavariables are instantiated before delaboration.

These options mean that two diagnostic bodies produced from the same underlying elaboration state can differ substantially without any change in the underlying error or proof obligation.

If Anneal compares human-facing message strings, the comparison protocol must treat the relevant option set as part of the observation environment. Relying on Lean defaults alone couples the comparison to the exact Lean revision.

Basis: **source** in `src/Lean/PrettyPrinter/Delaborator/Options.lean`; the automation consequence is **derived**.

### Lean provides narrow knobs for suppressing generated-name churn

Two option descriptions are explicitly relevant to stable snapshots.

`pp.mvars.anonymous` controls whether auto-generated expression metavariable names such as `?m.22` are displayed; when disabled, generated metavariable names can be rendered anonymously. `pp.fvars.anonymous` similarly suppresses numeric identities for loose free variables and is described in the source as useful for stabilizing output in `#guard_msgs`.

`pp.mvars.levels` separately controls generated universe metavariable names. The interaction matters because hiding one class of generated identifier does not hide every other source of unstable-looking names.

These options are useful when exact names are not part of the claim being tested. They are not universally safe normalization rules. If a test needs to distinguish two metavariables or free variables by identity, hiding their generated names can discard evidence the test cares about.

Basis: **source**; the caution is **derived** from what the options intentionally erase.

### `lean --json` makes metadata more stable, not the message body canonical

The batch reporter has two output branches. Text mode calls `msg.toString`; JSON mode calls `msg.toJson`.

Both paths serialize the structured `MessageData` first. `Message.serialize` stores `data := ← msg.data.toString`, and `Message.toJson` encodes that `SerialMessage`. Thus the JSON `data` field contains the same eagerly rendered diagnostic body boundary discussed above; JSON mode does not transport the original `MessageData` tree or an option-independent expression representation.

JSON remains preferable for machine processing because file positions, severity, caption, message kind, and other fields are separate from the human text. But a consumer that compares the `data` string byte-for-byte still inherits Lean's presentation choices and revision sensitivity.

Basis: **source** in `src/Lean/Message.lean` and `src/Lean/Language/Basic.lean`. The complete JSON schema is covered by the dedicated corpus report.

### `printMessageEndPos` changes the text envelope, not JSON diagnostic data

`printMessageEndPos` defaults to `false`. In batch reporting, Lean reads the option and passes it to the text `msg.toString includeEndPos` path. The JSON branch does not use that boolean; it serializes the message object directly, including its optional `endPos` field according to the JSON schema.

This is another reason not to treat text and JSON output as interchangeable snapshots. A command-line `-DprintMessageEndPos=true` intentionally changes text diagnostics while leaving the JSON field model intact.

Basis: **source**. Exact JSON field semantics remain owned by `lean-json-cli-protocol-v4-30-0-rc2`.

### Command-line `-D` is the batch control surface for these options

The Lean shell documents `-D name=value` as setting a configuration option. Its `setConfigOption` path updates `ShellOptions.leanOpts`, and the frontend receives those options in `Elab.runFrontend`.

Anneal can therefore pin relevant presentation choices at process invocation rather than relying only on local `set_option` commands inside generated Lean source.

Local source options can still override or scope behavior inside the file. A reproducibility protocol must therefore distinguish **initial command-line options** from **source-level option changes** encountered during elaboration.

Basis: **source** in `src/Lean/Shell.lean`; the scope distinction is **derived**.

### There is no source-grounded canonical diagnostic-text profile at this pin

The inspected sources provide controls over presentation, but no declaration or protocol that says a particular combination produces canonical diagnostic bytes across environments, projects, or Lean releases.

A practical Anneal policy should separate three needs:

1. **Machine classification.** Prefer structured fields: message kind, severity, positions, process status, and other protocol data.
2. **Human explanation.** Preserve the rendered body as useful evidence, but treat it as presentation text.
3. **Snapshot regression tests.** Pin the exact Lean revision and all relevant options, suppress only nondeterminism that the test does not care about, and validate the normalization against purpose-built fixtures.

If stable byte identity becomes a requirement, Anneal should define its own versioned normalization/serialization contract rather than infer one from Lean's default pretty printer.

Basis: **derived** from the pinned rendering paths and the neighboring corpus report on pretty-printing round trips.

## Boundaries

**No fresh execution.** This report did not run Lean, `lake`, the language server, or the checked-in pretty-printer tests. It relies on exact pinned source and test fixtures.

**This is not an exhaustive inventory of every `pp.*` option.** The report identifies controls that materially affect diagnostic stability and width. The full option file contains additional presentation switches.

**`format.width` may affect specialized callers not discussed here.** The established claim is narrower: ordinary `MessageData.toString` reaches `Format.pretty` through `ToString Format` without passing the current `Options`, while `pp.oneline` explicitly reads `format.width`. Callers that render `Format` directly can choose any width.

**No claim that ASCII is inherently stable.** `pp.unicode=false` makes one spelling choice explicit. It does not protect against changes in delaboration, names, omission thresholds, message prose, or the Lean version.

**No claim that anonymous metavariable/free-variable printing is always appropriate.** It removes generated identities. Use it only when those identities are outside the assertion being tested.

**No general LSP-rendering claim.** The Lean language server retains richer interactive diagnostic structures before conversion to ordinary LSP diagnostics. This report focuses on batch/frontend text and JSON diagnostic rendering. Interactive tactic-state and LSP/MCP behavior belong to separate subjects.

**No canonicalization claim for message prose.** Error wording can change when implementation code changes even if formatting options are held fixed.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27 against `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

Primary pinned sources:

- `src/Lean/Message.lean`, blob `a7f76198c582d1d2032bb24d13ad4cb7a272fa57`
  - `MessageData.format`, `MessageData.toString`, `Message.serialize`, `Message.toJson`, and `SerialMessage.toString`.
  - Establishes the structured-message to rendered-string boundary.
- `src/Init/Data/Format/Basic.lean`, blob `e0dbb5fa8be5578f8904e0e5a36decbcdf3fbec4`
  - `Format.defWidth = 120` and `Format.pretty`'s default-width argument.
- `src/Init/Data/ToString/Basic.lean`, blob `505aa15ca363d66f70f850134b008d98c93df184`
  - `ToString Format` delegates to `f.pretty`.
- `src/Lean/Data/Format.lean`, blob `9bcb44e2ce7c6848dd1f1d7a3f2801ccc54b4f42`
  - registration of `format.width`, `format.indent`, and `format.unicode`; `Format.pretty'`.
- `src/Lean/PrettyPrinter/Formatter.lean`, blob `2067634ee568e8e1480cece32b51eb197d04468c`
  - construction-time indentation; Unicode token formatting; `pp.oneline`; `OneLine.pretty`; explicit use of `format.width` in one-line mode.
- `src/Lean/PrettyPrinter/Delaborator/Options.lean`, blob `4475cbe095664e277abe916a551a472f7177a2fb`
  - presentation options including `pp.unicode`, `pp.unicode.fun`, name/detail controls, omission thresholds, and generated-name controls.
- `src/Lean/Language/Basic.lean`, blob `08f9b688fc869224c316175220403c2aeb5eb415`
  - `printMessageEndPos` and the text-versus-JSON batch-reporting branches.
- `src/Lean/Shell.lean`, blob `2ff5c4b0c82f876ddd4384c9c20dcaefebc1b90e`
  - `-D name=value`, `setConfigOption`, and propagation of `leanOpts` into `Elab.runFrontend`.

Pinned checked-in tests:

- `tests/elab/ppOneline.lean`, blob `9430dfef1427cce3a76f4c707f6a0babc44b950e`
  - demonstrates `pp.oneline` output changing as `format.width` changes.
- `tests/elab/ppUnicode.lean`, blob `0fa450fe5dfa6ad5d4e405c9e1681f13d07fbd86`
  - demonstrates Unicode/ASCII and function-arrow spelling changes under `pp.unicode` and `pp.unicode.fun`.

Relevant current corpus reports used to maintain scope boundaries:

- `reports/lean-diagnostic-objects-severity-v4-30-0-rc2`
- `reports/lean-json-cli-protocol-v4-30-0-rc2`
- `reports/lean-pretty-printing-roundtrip-v4-30-0-rc2`

Evidence roles are **source**, **checked-in test**, and **derived synthesis**. There is no fresh **execution** evidence.

## Revalidation

For a new Lean revision, revalidate the rendering chain before carrying forward any stability assumption:

1. inspect `MessageData.format`, `MessageData.toString`, `Message.serialize`, and `Message.toJson`;
2. inspect the `ToString Format` instance and `Format.pretty` default width;
3. inspect registration and uses of `format.width` and `format.indent`;
4. inspect `PrettyPrinter.Formatter.format`, `pp.oneline`, and the Unicode token formatter;
5. diff the relevant `pp.*` option definitions, especially generated-name and omission controls;
6. inspect the batch reporting branch and `printMessageEndPos` behavior; and
7. inspect the shell's `-D` option path if Anneal depends on process-level configuration.

On an execution-capable surface, add a compact pinned fixture that emits the same diagnostic under a matrix of options. At minimum preserve stdout, JSON output, and exit status for:

- default options;
- two widely separated `format.width` values with `pp.oneline=false`;
- the same widths with `pp.oneline=true`;
- two `format.indent` values;
- `pp.unicode=true` and `false`;
- `pp.unicode.fun=true` and `false`;
- generated metavariable/free-variable names with anonymous-name controls both enabled and disabled; and
- `printMessageEndPos=true` and `false` in text and JSON modes.

The discriminating expectation is that ordinary final message wrapping remains tied to the default `Format.pretty` width unless an earlier stage changes the `Format`, while one-line mode reacts directly to `format.width`. Preserve the exact fixture and output bytes if Anneal later adopts a normalized diagnostic snapshot protocol.

Do not use such a fixture as evidence of cross-version stability. The source-level rendering path remains the authority for each pinned Lean revision.
