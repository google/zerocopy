# One agent repair comparison: exact Lean goal versus batch diagnostics

## Summary

One Codex agent, identified for this task as GPT-6 Sol with high reasoning, repaired the same disposable Lean theorem twice: once after a versioned `lean --server` goal/context query, and once from fresh `lean --json` diagnostics. Both arms preserved the intended theorem, rejected one injected stale edit, and ended with the fixed consumer passing and `#print axioms claim` reporting no axioms. The first candidate in **both** arms compiled and satisfied the consumer but depended on `propext`; the agent corrected each after inspecting the axiom output. Under this small fixture, the batch diagnostic already exposed the hypothesis and target needed for the proof, so the exact goal path did not show a correctness advantage. This is a single sequential agent trial, not a statistically meaningful comparison or a human-user study.

## Applicability

The executed subject was Lean 4 `v4.30.0-rc2`, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, arm64 macOS, with `LEAN_NUM_THREADS=1`; the binary SHA-256 is in `REPORT.json`. Python 3.14.7 and the standard library implemented the tiny control shell. Only one Lean compiler or server ran at a time on the 8-GiB host. No network, Mathlib, Lake, Charon, Aeneas, or actual Anneal code participated.

The fixture has an old model (`modelValue = 4`, claim `n + 2 = 6`) and two isolated copies of the current model (`modelValue = 5`, claim `n + 2 = 7`). Both current arms began with `exact ?_` and the same compiled `Generated.olean` hash `48944da596a4ec3cb1adede2c4832b4cf1473ecdea2b9ded8f4a02c7ddae73d8`. The allowed proof context was the displayed hypothesis `h : n = modelValue`, standard definitions, and the imported module; no admissions, new axioms, or changed statement/model were allowed. The local fixed consumer checked the Lean proposition, not any Rust obligation.

The agent operated both arms sequentially, exact first. The matched budget was initially eight investigator actions per arm and, after the first oracle exposed an axiom dependency in both, amended to ten for each. The two arms shared one model context, so the batch arm had carryover from the exact arm. The 180-second per-arm wall limit in the prompt was not measured as active agent time and cannot be certified: the exact arm paused while the batch arm and report analysis proceeded. Tool wall time was measured; model deliberation and experimenter overhead were not isolated.

## Findings

### The complete agent path

The exact path inspected the current proof hash `4f75bbe1…c8974f9`, saw an old goal envelope with target `n + 2 = 6` and different proof/import hashes, then queried the current server and saw `h : n = modelValue ⊢ n + 2 = 7` under the current hashes. It did not use the old result to edit the current file. The batch path's fresh `lean --json` output independently showed the same current hypothesis and target in its placeholder and unsolved-goal diagnostics. The full prompt card, Lean protocol messages, compiler JSON, hashes, and decisions are preserved in [`support/prompts.json`](support/prompts.json) and [`support/transcript.jsonl`](support/transcript.jsonl). Basis: **execution** and recorded agent choice.

A deterministic concurrent writer appended a harmless comment to each proof after the first read. Each arm's first guarded edit used the old proof hash and was rejected. The agent inspected the new bytes, retained the concurrent note, and retried under the updated hash. There were no lost updates. This is a prototype compare-and-swap guard in `experiment.py`, not an Anneal edit API or a real simultaneous editing race. Basis: **execution** for the attempted and accepted edits; **prototype execution** for the conflict decision.

The first tactic chosen in both arms was `simp [h, modelValue]`. Lean compiled it and the fixed consumer accepted the intended type, but `#print axioms claim` reported `[propext]`. The scorer treated that as outside the stated allowed assumptions, even though no axiom declaration was added to the source. The agent then replaced the tactic under the hash guard with `rw [h]; rfl`. Both final consumers exited 0, both axiom queries said the theorem does not depend on any axioms, and both final proof texts had SHA-256 `9bfeeba3d4eaad1581c2c2c9646f9b0185a3a1bf75db354f13c78279cedb08c1`. This is a concrete case where accepted Lean plus a matching proposition missed a trust-policy violation; the explicit axiom check changed the repair. Basis: **execution** and the stipulated fixture policy.

### Matched scorecard

| Measure | Exact goal/context | Batch diagnostics |
| --- | ---: | ---: |
| Investigator actions through final oracle | 9 of 10 | 8 of 10 |
| Guarded edit attempts / rejected conflicts | 3 / 1 | 3 / 1 |
| Stale goal used as current authority | No; old and current hashes differed | No old goal shown |
| Intended proposition preserved | Yes; fixed consumer exit 0 | Yes; fixed consumer exit 0 |
| First proof's axiom report | `[propext]` | `[propext]` |
| Final proof's axiom report | None | None |
| Admissions or new axiom declarations | None | None |
| Measured tool wall time, including two final oracles | 1,312.5 ms | 973.4 ms |
| Final per-arm fixture bytes on disk | 13,278 | 13,278 |

The exact path's tool time includes 270.2 ms for the intentionally obsolete goal and 272.1 ms for the current goal. Batch diagnostics took 238.9 ms. Each arm also used two fresh proof compilations and two fixed-consumer runs because the first axiom report required a correction. These small, single-shot timings do not estimate interactive latency, model deliberation, throughput, or production memory. The transcript's macOS `ru_maxrss` values are cumulative raw bytes across child processes and cannot be interpreted as a per-arm peak. At no point did this runner start more than one Lean process concurrently. The detailed rubric and first/final scores are in [`support/score.json`](support/score.json). Basis: **execution** for recorded timings and sizes; **derived** for the comparison.

### Bounded I141 freshness check

A second Codex agent, given only two shuffled goal cards and the current proposition/proof/import hashes, selected the current card and explained why the other was stale. [`support/blind-check.json`](support/blind-check.json) preserves the exact card text, answer, and rubric. This tests one agent's interpretation of explicit freshness identities. It does not test a human reader, interface presentation quality, pending imports, cancellation, unsupported translation, approximate locations, or expired goal handles. **Real human participants are needed for I141's human-understanding claim**, with varied states and sound-repair choices rather than these two obvious cards. Basis: **agent judgment** on a constrained prompt.

## Boundaries

- **Not established:** that exact goal access improves proof quality or reduces interventions. In this fixture batch JSON already contained the whole local context, and the same agent solved exact first, creating transfer to batch.
- **Not established:** model-to-Rust meaning, obligation coverage, imported artifact integrity beyond its captured hash, independent kernel checking, or an Anneal-level acceptance contract. The fixed consumer checks one Lean theorem type and its visible axiom report.
- **Not established:** reproducible human work time or resource superiority. The action budgets were matched and documented, while per-arm cognitive wall time and peak RSS were not measured. The budget extension was an evaluator intervention applied equally to both arms.
- **Known not to apply:** the obsolete goal's target and import artifact did not match the current subject; using it as current guidance would have been a stale-query error.
- **Not examined:** real editors, MCP transport, concurrent writers, pending imports, cancelled work, unsupported translation, approximate locations, expired goal handles, multiple operators, larger proofs, or other Lean versions.

## Evidence

- Scope: [google/zerocopy issue #3731](https://github.com/google/zerocopy/issues/3731), exact I140/I141 lines captured in [`support/issue-scope.md`](support/issue-scope.md). The prior scripted vertical slice is [`../anneal-3730-vertical-acceptance-v4-30-0-rc2/REPORT.md`](../anneal-3730-vertical-acceptance-v4-30-0-rc2/REPORT.md); this package adds a model-chosen repair, matched arms, stale interpretation, conflict, and explicit intervention/resource scoring.
- Executable fixture: [`support/experiment.py`](support/experiment.py), SHA-256 `6b12b9c25d512c68e1cf16dd97032c2942e418f9f42cda594bc4d6a04c0d94bc`. It uses only Python's standard library and direct Lean. The final script includes a generic second guarded tactic replacement and corrects the resource field name; the original first-action events remain in the transcript.
- Exact prompt card: [`support/prompts.json`](support/prompts.json), SHA-256 `9b6f1b9b12cf85f97fd6b66f312c8db79c6144f88bc8d0a14ea4efa2166ab55c`; the amendment appears after the first oracles and is preserved rather than silently changing the initial budget.
- Full chronological execution and LSP protocol: [`support/transcript.jsonl`](support/transcript.jsonl), SHA-256 `bb3b647a1d59329f77d7fffdecaa4b238b2f49356ba5e3c3ff5331212d4e9cce`. Local absolute paths are substituted with `$WORK`, `$WORK_URI`, `$LEAN_BIN`, and `$LEAN_HOME`; all protocol fields, compiler messages, timestamps, and hashes remain. One initially named `child_maxrss_kib_cumulative` field was normalized to `child_maxrss_raw_cumulative` because macOS reports raw bytes.
- Fixture files: [`support/work/`](support/work/) contains old, exact, and batch sources, compiled artifacts, and the final fixed consumers. Initial source and first-candidate proof bytes are also present verbatim in the transcript.

## Revalidation

Copy this package to a fresh disposable directory, set `LEAN_BIN` to the pinned Lean executable, and run `python3 support/experiment.py setup`. Follow `support/prompts.json` with `query --arm old`, `query --arm exact`, or `diagnose` on separate arm copies; call `conflict`, `apply --expected <read hash> --tactic <choice>`, and `oracle` in each arm. Compare the old/current artifact and proof hashes, confirm that a stale edit is rejected, and inspect both the fixed consumer result and full axiom text. Use a new copy for each run because `setup` overwrites fixture files and appends to `events.jsonl`. To make a broader I140 claim, repeat with independently assigned agents, counterbalanced arm order, varied proof tasks, and measured model/user time. For I141, recruit human participants and test the other failure/freshness states named in the issue.
