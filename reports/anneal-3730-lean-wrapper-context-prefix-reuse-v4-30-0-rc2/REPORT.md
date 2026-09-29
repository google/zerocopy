# Lean wrapper context and command-prefix reuse at v4.30.0-rc2

## Scope and result

This direct Lean experiment fills two previously unexecuted component cells in #3731: **I037/B08** compares elaborated theorem outputs under local instances, macros, and `autoImplicit`; **I036** records which commands actually re-elaborated after separate late tactic, definition, option, namespace, and import edits. It uses the cached Lean `v4.30.0-rc2` binary, seven fresh `lean --json` batch files, and one sequential `lean --server` process with eleven document versions. There is no Anneal parser, generator, projected Rust document, or cancellation result here. Neither row is fully closed for product use.

The local instance pair retained the exact same theorem source line. With the local `Marker` instance, batch exited 0 and `#print axioms` reported none. Omitting that instance made `decide` report the proposition false, batch exited 1, and the retained declaration printed with `sorryAx`. The two macro files also retained the same theorem line and both exited 0 without axioms, yet `#print N.proof` showed propositions `0 = 0` and `1 = 1` respectively. A missing macro exited 1; `autoImplicit false` rejected a forward name, while `autoImplicit true` accepted it as an implicit binder and printed `∀ {later : Nat}, later = 1`. This demonstrates that accepting the same authored theorem text is not enough to attest an intended proposition or dependency environment. The local-instance `#print` displays the same surface proposition in both variants; the proof outcome and axiom output expose the difference in resolved instance. These are Lean elaboration observations, not a proposed complete Anneal wrapper.

## Prefix experiment

The LSP fixture put a `run_cmd` append marker before and after the mutable commands. Each `textDocument/didChange` used the same URI and a strictly increasing version; `textDocument/waitForDiagnostics` completed for that version before the next edit. The marker file records elaboration execution rather than inferred cache state. Each mutation was followed by a reset to the base text, so suffix boundaries can be compared in both directions.

| Change from base | Newly executed marker commands | Wait latency on this tiny file |
| --- | --- | ---: |
| initial open | A B C D E | 726 ms |
| late proof tactic, then reset | E; E | 213; 213 ms |
| generated definition, then reset | D E; D E | 213; 213 ms |
| option, then reset | C D E; C D E | 213; 213 ms |
| namespace, then reset | B C D E; B C D E | 213; 213 ms |
| import, then reset | A B C D E; A B C D E | 891; 912 ms |

The definition mutation changed `generated` from `1` to `2`; version 4 emitted a Lean error saying `decide` had proved `generated = 1` false. Restoring the definition cleared it. Thus the suffix markers are coupled to a semantic failure control, not just to timing. The timings are one-run observations; they do not estimate product or large-module latency. `run_cmd` performs a file side effect and is itself part of the synthetic fixture, so these markers establish the tested command execution boundary only. The report does not assert Lean's internal cache representation or that every wrapper shape has the same reuse behavior.

## Evidence and reproduction

- [`support/probe.py`](support/probe.py) creates every source, drives one direct LSP server, captures complete JSON-RPC events and fresh batch output, then normalizes private work and binary paths in [`support/raw.json`](support/raw.json). The raw record retains source text, SHA-256 identities, exact versions, responses, diagnostics, marker deltas, elapsed times, and clean server exit. The final generated source files and marker ledger are retained under [`support/work`](support/work).
- [`support/check.py`](support/check.py) validates all seven batch outcomes and key elaborated prints, the eleven versioned marker deltas, source digests, the semantic error control, and server shutdown. Run `python3 support/check.py` without starting Lean. To repeat the experiment, run `python3 support/probe.py` from the package; it recreates only its own `support/work` directory and rewrites its raw transcript, then run the checker. No package fetch or install is performed.
- The recorded executable SHA-256 is `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`; batch `#eval Lean.versionString` returned `4.30.0-rc2`. `LEAN_NUM_THREADS=1`; only one server/compiler operation ran at a time. See the prior [direct document-context report](../anneal-3730-document-context-v4-30-0-rc2/REPORT.md) for the earlier namespace/section/notation and unsaved-import controls that this experiment extends.

## Residuals

- **I036:** Cancellation during re-elaboration, generated Rust-to-Lean scaffolding, larger imported modules, and repeated performance distributions remain unmeasured. Stable filename alone does not guarantee prefix reuse when an early generated command changes in this fixture.
- **I037/B08:** The actual Anneal annotation parser, wrapper transform, source map, and claim manifest must compare the elaborated proposition and dependencies to the intended Rust subject. These local Lean files cannot prove that mapping or its preservation across regeneration.
- The direct `lean --server` path was tested; this does not attest `lake serve`, an editor host, MCP responses, or a production worker lifecycle.
