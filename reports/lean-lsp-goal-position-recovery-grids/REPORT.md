# Lean LSP Tactic and Term Goal Selection Across Nested Proofs, Macros, Partial Elaboration, and Unsaved Edits

## Summary

Across direct `lean --server` and `lake --no-cache serve` sessions on Lean `v4.30.0-rc2`, `$/lean/plainGoal` and `Lean.Widget.getInteractiveGoals` agree on goal availability, goal count, and rendered hypothesis/target contexts across valid nested proofs (`have`, `constructor` bullets, `first` combinators), tactic macros, and unsaved buffers containing syntax errors or unknown tactics. Similarly, `$/lean/plainTermGoal` and `Lean.Widget.getInteractiveTermGoal` agree on term target types and UTF-16 source ranges inside nested term proofs (`Eq.refl`, `Eq.trans`) at cursor positions where tactic-goal endpoints return empty goal lists (`goals: []`).

However, cursor-level goal responses are strictly local elaboration selections rather than whole-module verification verdicts:
1. Within a single line, moving the cursor a few UTF-16 columns (such as from the start of an inner `simpa` at column 4 to inside `simpa` at column 8, or from before a tactic macro to inside its body) switches the selected goal between the outer target, the inner subgoal, and `no goals`.
2. In files containing middle-declaration errors (`exact ?_`, unknown tactic, deterministic `maxHeartbeats 1` timeout, or unexpected `)` syntax error), declarations before and after the failure remain queryable and `#print axioms` on a valid later theorem still reports no axioms, while fresh batch `lean --json` exits `1`.
3. Under an unsaved syntax error (`solve_macro )`), `$/lean/plainGoal` and `Lean.Widget.getInteractiveGoals` can return `no goals` (empty list) at a cursor position even though the buffer fails compilation.
4. In a controlled single-agent proof-repair comparison between versioned `lean --server` goal queries and fresh batch `lean --json` diagnostics, both arms rejected a stale goal card (`n + 2 = 6` vs. `n + 2 = 7`), handled a compare-and-swap edit conflict, and discovered via `#print axioms` that an initial compiling candidate (`simp [h, modelValue]`) introduced an disallowed `[propext]` dependency before repairing the proof to `rw [h]; rfl` (zero axioms).

## Applicability

- **Evaluated Toolchain Subject**: Lean 4 and Lake `v4.30.0-rc2` (`leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`) on arm64 macOS with `LEAN_NUM_THREADS=1` and network access disabled (`LAKE_NO_NET=1` and/or `/usr/bin/sandbox-exec` network denial).
- **Subprobe Coverage**:
  1. **Single-agent workflow repair evaluation** (`support/agent-workflow-evaluation-v4-30-0-rc2/`): Sequential comparison of exact `lean --server` goal/context queries vs. fresh `lean --json` batch diagnostics, plus a blind freshness-card discrimination check.
  2. **Direct Lean macro tactic position recovery** (`support/macro-tactic-position-recovery-v4-30-0-rc2/`): Eight cursor positions across versions 1 (`solve_macro ?_`), 2 (`solve_macro h`), and 3 (`solve_macro ?_`).
  3. **Direct Lean nested tactic and term position grid** (`support/nested-tactic-position-grid-v4-30-0-rc2/`): Twenty `$/lean/plainGoal` and three `$/lean/plainTermGoal` queries across `have ... := by simpa`, `first` combinator with emoji trace `"🧪"` (verifying UTF-16 surrogate offsets), `constructor` bullets, and `exact Eq.refl n`.
  4. **Direct Lean nested unsaved error and recovery grid (`plainGoal`)** (`support/nested-unsaved-recovery-grid-v4-30-0-rc2/`): Seven cursor positions across four unsaved `didChange` versions (valid v1, syntax error `)` v2, unknown tactic v3, recovered v4).
  5. **Direct Lean partial and failed elaboration queries** (`support/partial-elaboration-queries-v4-30-0-rc2/`): Four middle-declaration failure classes (`exact ?_`, `tactic_that_does_not_exist`, `set_option maxHeartbeats 1` with `omega`, and unexpected `)`) flanked by valid `before` and `after` theorems, plus an immediate post-`didChange` query race.
  6. **Direct Lean plain and rich goals across unsaved nested errors** (`support/rich-goal-unsaved-recovery-v4-30-0-rc2/`): 24 paired `$/lean/plainGoal` and `Lean.Widget.getInteractiveGoals` queries (6 positions × 4 document versions) in one persistent RPC session.
  7. **Lake-launched nested position context with prepared import** (`support/lake-launched-position-context-v4-30-0-rc2/`): Seven paired plain/rich goal queries under `lake --no-cache serve` importing `depValue : Nat := 7` from a local `probe_dep` package.
  8. **Lake-launched nested `constructor` and `have` goal positions** (`support/lake-nested-constructor-goal-positions-v4-30-0-rc2/`): 13 paired plain/rich goal queries across outer `constructor`, two case bullets (`case left`, `case right`), and an inner `have hz : depValue = 7 := by exact h` (sampled peak RSS 808,208 KiB).
  9. **Lake-launched reflexive term-goal positions** (`support/lake-reflexive-term-goal-positions-v4-30-0-rc2/`): Nine sequential triples (`plainGoal`, `getInteractiveGoals`, `plainTermGoal`) on `by exact Eq.refl depValue` (sampled peak RSS 1,023,920 KiB).
  10. **Lake-launched rich term-goal nested positions** (`support/lake-rich-term-goal-nested/`): 11 sequential quadruples (`plainGoal`, `getInteractiveGoals`, `plainTermGoal`, `Lean.Widget.getInteractiveTermGoal`) on `exact Eq.trans (Eq.refl depValue) (Eq.refl depValue)` (sampled peak RSS 758,560 KiB).
  11. **Lake-launched unsaved macro and error goal positions** (`support/lake-unsaved-macro-error-positions-v4-30-0-rc2/`): 20 paired plain/rich queries (5 positions × 4 unsaved versions: solved `solve_macro h`, unresolved `solve_macro ?_`, syntax error `solve_macro )`, restored `solve_macro h`; sampled peak RSS 830,720 KiB).

## Findings

### 1. Nested Tactic, Combinator, Constructor, and Macro Selection Grids

- **Direct Lean nested tactic and UTF-16 emoji grid** (`support/nested-tactic-position-grid-v4-30-0-rc2/transcript.json`, `support/nested-tactic-position-grid-v4-30-0-rc2/Nested.lean`):

| Position in the fixture | `plainGoal` result |
| --- | --- |
| Outer `by`, start of `have`, start of inner `simpa` | One goal with `n : Nat`, `h : n = 0`, target `n + 0 = 0` |
| Five UTF-16 units after the start of `simpa` | One goal with target `n = 0` and the same `n`, `h` context |
| `first`, `trace`, emoji string, before outer `exact` | One goal with added `hz : n + 0 = 0` |
| End of outer `exact hz` and start of unselected branch | No goals |
| Before `constructor` | One `True ∧ n = n` goal |
| First bullet marker | Two goals, `case left ⊢ True` and `case right ⊢ n = n` |
| Start/end of `trivial` | Left goal / no goals |
| Second bullet marker and start of `rfl` | Right goal |
| Before `exact Eq.refl n` / within `Eq.refl n` | One tactic goal / no tactic goals |

  On the `trace "🧪"; exact hz` line, the emoji occupies UTF-16 columns 11–13 (a surrogate pair), shifting `exact` from Unicode code-point column 15 to UTF-16 column 16. `$/lean/plainTermGoal` at `Eq.refl` returned `n : Nat ⊢ n = n` with range line 15, columns 8–17, and returned JSON `null` at the earlier `exact` tactic and inside the emoji string (**Basis: execution**).

- **Lake-launched imported position context** (`support/lake-launched-position-context-v4-30-0-rc2/results.json`, `Dep.lean` SHA-256 `15bbf60d162408dade43c6e618dd0d09b28c8fdeb7528c80e40329908f12b7a2`, `Proof.lean` SHA-256 `357891c27b46563b35d8f5f314ba4c742e205b6f1a90261b204b456a33d9e699`):

| Position in `Proof.lean` | Zero-based `(line, character)` | Plain and rich result |
| --- | ---: | --- |
| Outer `have` | `(3, 2)` | `n : Nat`, `h : n = depValue` ⊢ `n + 0 = depValue` |
| Inner `simpa` start | `(4, 4)` | Same incoming target and hypotheses |
| Inside `simpa` | `(4, 8)` | Same hypotheses ⊢ `n = depValue` |
| End of inner tactic line | `(4, 17)` | Empty goal list |
| Outer `exact` start | `(5, 2)` | Adds `hz : n + 0 = depValue`; target returns to `n + 0 = depValue` |
| End of `exact hz` | `(5, 10)` | Empty goal list |
| File end after `#eval` | `(8, 0)` | JSON `null` |

- **Lake-launched nested `constructor` and inner `have` grid** (`support/lake-nested-constructor-goal-positions-v4-30-0-rc2/results.json`, SHA-256 `821402691c13066d19146d766eae67666c2ce3c018e208aa5e640d80bbefa881`):

| Position in `Proof.lean` | Zero-based `(line, character)` | Plain and rich result |
| --- | ---: | --- |
| Before `constructor` | `(3,2)` | One outer goal, `h : depValue = 7 ⊢ depValue = 7 ∧ True` |
| End of `constructor` and first bullet marker | `(3,13)`, `(4,2)` | Two goals: `case left ⊢ depValue = 7` and `case right ⊢ True` |
| Start of outer `have` | `(4,4)` | Left goal only |
| Inner `by` and start of `exact h` | `(4,30)`, `(5,6)` | Inner equality goal, without a case label |
| End of inner `exact h` | `(5,13)` | Empty goal list |
| Outer `exact hz` start | `(6,4)` | Left goal with `h hz : depValue = 7` |
| End of outer `exact hz` | `(6,12)` | Empty goal list |
| Second bullet and `trivial` start | `(7,2)`, `(7,4)` | Right goal, `h : depValue = 7 ⊢ True` |
| End of `trivial` | `(7,11)` | Empty goal list |
| EOF after `#eval` | `(10,0)` | JSON null |

- **Direct Lean tactic macro recovery** (`support/macro-tactic-position-recovery-v4-30-0-rc2/results.json`, SHA-256 `66be28d077c110dc3a57b9a2e2077eb18a2fdc8f961f0d2698d35514af557c69`):

| Version | Fresh `lean --json` | Live diagnostics | `plainGoal` at tactic line 3, column 8 | Incoming goal at line 3, column 0 |
| --- | --- | --- | --- | --- |
| 1, `solve_macro ?_` | Exit 1; placeholder synthesis and unsolved-goal errors. | Same two error classes at version 1. | `h : True ⊢ True`. | `h : True ⊢ True`. |
| 2, `solve_macro h` | Exit 0. | Empty at version 2. | `no goals`. | `h : True ⊢ True`. |
| 3, `solve_macro ?_` | Exit 1; placeholder synthesis and unsolved-goal errors. | Same two error classes at version 3. | `h : True ⊢ True`. | `h : True ⊢ True`. |

  In versions 1 and 3, columns 0, 2, 8, 14, 16 on line 3 and column 0 on line 4 returned `h : True ⊢ True`, while line 3 column 20 and line 4 column 2 returned `null`. In solved version 2, columns 0–2 returned `h : True ⊢ True` while columns 8–16 and line 4 column 0 returned `no goals` (**Basis: execution**).

### 2. Plain and Rich Term-Goal Selection Inside Reflexive and Nested Term Proofs

- **Reflexive `Eq.refl depValue` term positions** (`support/lake-reflexive-term-goal-positions-v4-30-0-rc2/results.json`, SHA-256 `71c94390d16bbfaa1f0e5e5c5260de689fcdd68febf40028a7f622b0149d0455`):

| Position in `Proof.lean` | Zero-based `(line, character)` | Plain/rich tactic goals | `plainTermGoal` |
| --- | ---: | --- | --- |
| Start of `exact` | `(3,2)` | One goal, `⊢ depValue = depValue` | Null |
| Inside `exact` | `(3,5)` | Empty lists | Null |
| Start/inside `Eq.refl` | `(3,8)`, `(3,11)` | Empty lists | `⊢ depValue = depValue`, range `(3,8)`–`(3,24)` |
| Start/inside argument `depValue` | `(3,16)`, `(3,20)` | Empty lists | `⊢ Nat`, range `(3,16)`–`(3,24)` |
| End of tactic line | `(3,24)` | Empty lists | `⊢ Nat`, same argument range |
| Next line and EOF | `(4,0)`, `(6,0)` | JSON null | Null |

- **Nested `Eq.trans (Eq.refl depValue) (Eq.refl depValue)` plain vs. rich term goals** (`support/lake-rich-term-goal-nested/results.json`):

| Cursor on proof line 3 | Character | Plain and rich term target | Returned range on line 3 | Tactic goals |
| --- | ---: | --- | --- | --- |
| `exact` start | 2 | null | — | one input goal |
| `Eq.trans` start | 8 | `depValue = depValue` | 8–54 | empty |
| inside `Eq.trans` | 11 | `depValue = depValue` | 8–54 | empty |
| first `Eq.refl` | 18 | `depValue = depValue` | 18–34 | empty |
| first `depValue` | 26 | `Nat` | 26–34 | empty |
| between arguments | 35 | `depValue = depValue` | 17–35 | empty |
| second `Eq.refl` | 37 | `depValue = depValue` | 37–53 | empty |
| second `depValue` | 45 | `Nat` | 45–53 | empty |
| end of term | 54 | `depValue = depValue` | 36–54 | empty |
| next line 4, character 0 | 0 | null | — | null |
| EOF line 6, character 0 | 0 | null | — | null |

  At all 8 non-null term positions, `Lean.Widget.getInteractiveTermGoal` and `$/lean/plainTermGoal` returned identical target types and UTF-16 ranges, with the rich response additionally carrying tagged target subexpressions and session-scoped `ctx: {p: ...}` and `term: {p: ...}` references (**Basis: execution**).

### 3. Partial Elaboration, Unsaved Error Recovery, and False-Empty Goal States

- **Four middle-declaration failure classes with valid surrounding theorems** (`support/partial-elaboration-queries-v4-30-0-rc2/transcript.json`, SHA-256 `af3249d8ddf9da06628b00fba72d13eb0b08827766c98606c9f65b69f899ba10`; batch timings 1848.5, 584.7, 584.5, and 582.7 ms):

| Middle declaration | Batch result | Goal at failing tactic/token (col 4) | Goal at start of `before` and `after` (col 2) |
| --- | --- | --- | --- |
| `exact ?_` | Placeholder and unsolved-goal errors (exit 1) | `⊢ True` | `⊢ True` each (col 4/EOL: `[]`) |
| `tactic_that_does_not_exist` | Unknown tactic and unsolved-goal errors (exit 1) | `⊢ True` | `⊢ True` each (col 4/EOL: `[]`) |
| `set_option maxHeartbeats 1` with `omega` | Deterministic timeout at elaborator (exit 1) | JSON `null` | `⊢ True` each (col 4/EOL: `[]`) |
| Unexpected `)` in tactic block | Parse error and unsolved-goal errors (exit 1) | JSON `null` | `⊢ True` each (col 4/EOL: `[]`) |

  In all four files, `#print axioms before` and `#print axioms after` reported no axioms, while batch compilation exited `1`. In a same-URI edit test (`broken : True` at v1 edited to `broken : False` at v2), a `plainGoal` request sent immediately after `didChange` (before `waitForDiagnostics(version=2)`) and subsequent `plainGoal` requests carrying extra `textDocument.version` values `1` or `2` all returned `⊢ False`, demonstrating that `plainGoal` ignores extra `version` fields and serves latest worker state (**Basis: execution**).

- **Direct Lean unsaved nested error and recovery grids (`plainGoal` and `getInteractiveGoals`)** (`support/nested-unsaved-recovery-grid-v4-30-0-rc2/transcript.json`, SHA-256 `9af1f3c455aa04d7c04e66de39b3dad209ff003533e3c1c222532056f3d2f77a`, and `support/rich-goal-unsaved-recovery-v4-30-0-rc2/results.json`, SHA-256 `561c2246041961e086e66f67f5776d83659a4a4a96579be032e147a5153383d9`):

| Cursor position | Valid v1 and recovered v4 | Syntax error v2 (`)`) | Unknown tactic v3 |
| --- | --- | --- | --- |
| Outer `have` start, line 3 column 2 (rich probe) | `n, h ⊢ n + 0 = 0` | `n, h ⊢ n + 0 = 0` | `n, h ⊢ n + 0 = 0` |
| Nested token start, line 4 column 4 | `n, h ⊢ n + 0 = 0` | JSON `null` | `n, h ⊢ n + 0 = 0` |
| Inside nested tactic, line 4 column 6 / col 8 | `n, h ⊢ n = 0` | JSON `null` | `n, h ⊢ n + 0 = 0` |
| Nested tactic end, line 4 column 17/5/24 | Empty goals (`[]`) | JSON `null` | `n, h ⊢ n + 0 = 0` |
| Outer `exact hz` start, line 5 column 2 | `n, h, hz ⊢ n + 0 = 0` | JSON `null` | JSON `null` |
| Later `trivial` start, line 8 column 2 | `⊢ True` | `⊢ True` | `⊢ True` |
| Later `trivial` end, line 8 column 9 / EOF `(9,0)` | Empty goals (`[]`) | Empty goals (`[]`) | Empty goals (`[]`) |

  Across all 24 paired cells in `support/rich-goal-unsaved-recovery-v4-30-0-rc2/results.json` (17 goal pairs, 2 empty-list pairs, 5 `null` pairs; diagnostic counts `{"1": 0, "2": 3, "3": 3, "4": 0}`), `$/lean/plainGoal` and `Lean.Widget.getInteractiveGoals` returned identical categories and target strings. While one RPC session survived all three `didChange` edits, `ctx.p` handles changed across versions and `mvarId` strings sometimes repeated (**Basis: execution**).

- **Lake-launched unsaved macro and syntax-error grid** (`support/lake-unsaved-macro-error-positions-v4-30-0-rc2/results.json`):

| Open-buffer version | Fresh batch for these bytes | Incoming `(4,2)` | Macro body `(4,8)` | Later `(4,16)` / `(5,0)` | EOF `(5,2)` | Final live errors |
| --- | --- | --- | --- | --- | --- | --- |
| 1 solved, `solve_macro h` | Exit 0 | One `h : depValue = 7 ⊢ depValue = 7` goal | No goals | No goals / no goals | Null | 0 |
| 2 unresolved, `solve_macro ?_` | Exit 1 | Same goal | Same goal | Same goal / same goal | Null | 2 |
| 3 syntax error, `solve_macro )` | Exit 1 | Same goal | No goals | Null / null | Null | 1 |
| 4 restored, `solve_macro h` | Same bytes as version 1 | Same goal | No goals | No goals / no goals | Null | 0 |

  Crucially, in version 3 (`solve_macro )`), cursor position `(4,8)` returned **no goals** (`[]`) on both plain and rich APIs despite the `unexpected token ')'` error diagnostic and batch exit `1` (**Basis: execution**).

### 4. Single-Agent Proof Repair Comparison: Exact Goal vs. Batch Diagnostics

In `support/agent-workflow-evaluation-v4-30-0-rc2/score.json` and `support/agent-workflow-evaluation-v4-30-0-rc2/transcript.jsonl` (SHA-256 `bb3b647a1d59329f77d7fffdecaa4b238b2f49356ba5e3c3ff5331212d4e9cce`), one agent repaired a theorem under `Generated.olean` (`modelValue = 5`, SHA-256 `48944da596a4ec3cb1adede2c4832b4cf1473ecdea2b9ded8f4a02c7ddae73d8`, target `h : n = modelValue ⊢ n + 2 = 7`) in two matched arms:

| Measure | Exact goal/context | Batch diagnostics |
| --- | ---: | ---: |
| Investigator actions through final oracle | 9 of 10 | 8 of 10 |
| Guarded edit attempts / rejected conflicts | 3 / 1 | 3 / 1 |
| Stale goal used as current authority | No; old (`n + 2 = 6`) and current hashes differed | No old goal shown |
| Intended proposition preserved | Yes; fixed consumer exit 0 | Yes; fixed consumer exit 0 |
| First proof's axiom report (`simp [h, modelValue]`) | `[propext]` | `[propext]` |
| Final proof's axiom report (`rw [h]; rfl`) | None | None |
| Admissions or new axiom declarations | None | None |
| Measured tool wall time, including two final oracles | 1,312.5 ms (old goal 270.2 ms, current goal 272.1 ms) | 973.4 ms (batch JSON 238.9 ms) |
| Final per-arm fixture bytes on disk | 13,278 (final proof SHA-256 `9bfeeba3d4eaad1581c2c2c9646f9b0185a3a1bf75db354f13c78279cedb08c1`) | 13,278 |

A separate blind freshness check (`support/agent-workflow-evaluation-v4-30-0-rc2/blind-check.json`) confirmed that an unprimed agent given two shuffled goal cards and current proof/import digests selected the current card and rejected the stale card (**Basis: execution and recorded agent judgment**).

## Boundaries

- **Not examined**: Multi-agent statistical trials, counterbalanced arm ordering, or human-participant usability studies for stale-model/rebuilding UI banners.
- **Not examined**: Dereferencing or expiring opaque `ctx`, `info`, or `term` RPC handles across edits inside the position-grid probes, or mapping positions across real Anneal-generated Rust-to-Lean source projections.
- **Unknown**: General parser-recovery spans across arbitrary delimiter errors or deeply nested macro expansions beyond the tested single-token `)` and `solve_macro` fixtures.
- **Known not to apply**: Neither `$/lean/plainGoal` returning `goals: []` nor `textDocument/waitForDiagnostics` returning `{}` certifies whole-module compilation or axiom-free verification (as shown by `(4,8)` returning `no goals` on `solve_macro )`, `after` elaborating cleanly after a broken declaration, and `simp` introducing `propext`).

## Evidence

- **Agent workflow evaluation**: [`support/agent-workflow-evaluation-v4-30-0-rc2/experiment.py`](support/agent-workflow-evaluation-v4-30-0-rc2/experiment.py) (SHA-256 `6b12b9c25d512c68e1cf16dd97032c2942e418f9f42cda594bc4d6a04c0d94bc`), [`support/agent-workflow-evaluation-v4-30-0-rc2/prompts.json`](support/agent-workflow-evaluation-v4-30-0-rc2/prompts.json) (SHA-256 `9b6f1b9b12cf85f97fd6b66f312c8db79c6144f88bc8d0a14ea4efa2166ab55c`), [`support/agent-workflow-evaluation-v4-30-0-rc2/transcript.jsonl`](support/agent-workflow-evaluation-v4-30-0-rc2/transcript.jsonl), [`support/agent-workflow-evaluation-v4-30-0-rc2/score.json`](support/agent-workflow-evaluation-v4-30-0-rc2/score.json), [`support/agent-workflow-evaluation-v4-30-0-rc2/blind-check.json`](support/agent-workflow-evaluation-v4-30-0-rc2/blind-check.json), [`support/agent-workflow-evaluation-v4-30-0-rc2/issue-scope.md`](support/agent-workflow-evaluation-v4-30-0-rc2/issue-scope.md), and [`support/agent-workflow-evaluation-v4-30-0-rc2/work`](support/agent-workflow-evaluation-v4-30-0-rc2/work).
- **Direct macro tactic recovery**: [`support/macro-tactic-position-recovery-v4-30-0-rc2/probe.py`](support/macro-tactic-position-recovery-v4-30-0-rc2/probe.py) (SHA-256 `5036644080d121bcfb674a94dd865144ca286b178db88b65ed31103c2274b8c9`), [`support/macro-tactic-position-recovery-v4-30-0-rc2/results.json`](support/macro-tactic-position-recovery-v4-30-0-rc2/results.json), [`support/macro-tactic-position-recovery-v4-30-0-rc2/check.py`](support/macro-tactic-position-recovery-v4-30-0-rc2/check.py), and [`support/macro-tactic-position-recovery-v4-30-0-rc2/work`](support/macro-tactic-position-recovery-v4-30-0-rc2/work).
- **Direct nested tactic/term grid**: [`support/nested-tactic-position-grid-v4-30-0-rc2/Nested.lean`](support/nested-tactic-position-grid-v4-30-0-rc2/Nested.lean), [`support/nested-tactic-position-grid-v4-30-0-rc2/probe.py`](support/nested-tactic-position-grid-v4-30-0-rc2/probe.py), [`support/nested-tactic-position-grid-v4-30-0-rc2/transcript.json`](support/nested-tactic-position-grid-v4-30-0-rc2/transcript.json), and [`support/nested-tactic-position-grid-v4-30-0-rc2/check.py`](support/nested-tactic-position-grid-v4-30-0-rc2/check.py).
- **Direct nested unsaved recovery (`plainGoal` and rich)**: [`support/nested-unsaved-recovery-grid-v4-30-0-rc2/Nested.lean`](support/nested-unsaved-recovery-grid-v4-30-0-rc2/Nested.lean) (SHA-256 `0f262ebe59eeef631b313d59110c403d36256634200b0a16c4a621da40a3ab28`), [`support/nested-unsaved-recovery-grid-v4-30-0-rc2/probe.py`](support/nested-unsaved-recovery-grid-v4-30-0-rc2/probe.py), [`support/nested-unsaved-recovery-grid-v4-30-0-rc2/transcript.json`](support/nested-unsaved-recovery-grid-v4-30-0-rc2/transcript.json), [`support/nested-unsaved-recovery-grid-v4-30-0-rc2/check.py`](support/nested-unsaved-recovery-grid-v4-30-0-rc2/check.py), [`support/nested-unsaved-recovery-grid-v4-30-0-rc2/variants`](support/nested-unsaved-recovery-grid-v4-30-0-rc2/variants), [`support/rich-goal-unsaved-recovery-v4-30-0-rc2/probe.py`](support/rich-goal-unsaved-recovery-v4-30-0-rc2/probe.py) (SHA-256 `f5fcc6eadabe08bf54463bf3b98d15840dc2f77dc5688e0dcf00f76235839671`), [`support/rich-goal-unsaved-recovery-v4-30-0-rc2/transcript.json`](support/rich-goal-unsaved-recovery-v4-30-0-rc2/transcript.json) (SHA-256 `608458932c47f5a054b4a6157def570b2f238e1364580596f5ea5445ae468e97`), [`support/rich-goal-unsaved-recovery-v4-30-0-rc2/results.json`](support/rich-goal-unsaved-recovery-v4-30-0-rc2/results.json), [`support/rich-goal-unsaved-recovery-v4-30-0-rc2/check.py`](support/rich-goal-unsaved-recovery-v4-30-0-rc2/check.py) (SHA-256 `5b80334f937edf8013eb9c7505800b08ecce0b1feb04dd58d0e21675005e3174`), [`support/rich-goal-unsaved-recovery-v4-30-0-rc2/Nested.lean`](support/rich-goal-unsaved-recovery-v4-30-0-rc2/Nested.lean), [`support/rich-goal-unsaved-recovery-v4-30-0-rc2/Batch-valid.lean`](support/rich-goal-unsaved-recovery-v4-30-0-rc2/Batch-valid.lean), [`support/rich-goal-unsaved-recovery-v4-30-0-rc2/Batch-syntax.lean`](support/rich-goal-unsaved-recovery-v4-30-0-rc2/Batch-syntax.lean), and [`support/rich-goal-unsaved-recovery-v4-30-0-rc2/Batch-unknown.lean`](support/rich-goal-unsaved-recovery-v4-30-0-rc2/Batch-unknown.lean).
- **Partial elaboration queries**: [`support/partial-elaboration-queries-v4-30-0-rc2/probe.py`](support/partial-elaboration-queries-v4-30-0-rc2/probe.py) (SHA-256 `1a52598fa127dbdc06ca021a8b954e03c320419c3c8575a98f66116913a5f6a9`), [`support/partial-elaboration-queries-v4-30-0-rc2/transcript.json`](support/partial-elaboration-queries-v4-30-0-rc2/transcript.json) (344 events), [`support/partial-elaboration-queries-v4-30-0-rc2/summarize.py`](support/partial-elaboration-queries-v4-30-0-rc2/summarize.py), [`support/partial-elaboration-queries-v4-30-0-rc2/summary.json`](support/partial-elaboration-queries-v4-30-0-rc2/summary.json), and [`support/partial-elaboration-queries-v4-30-0-rc2/work`](support/partial-elaboration-queries-v4-30-0-rc2/work).
- **Lake-launched position and term-goal suites**:
  - [`support/lake-launched-position-context-v4-30-0-rc2/probe.py`](support/lake-launched-position-context-v4-30-0-rc2/probe.py), [`support/lake-launched-position-context-v4-30-0-rc2/results.json`](support/lake-launched-position-context-v4-30-0-rc2/results.json), [`support/lake-launched-position-context-v4-30-0-rc2/check.py`](support/lake-launched-position-context-v4-30-0-rc2/check.py), and [`support/lake-launched-position-context-v4-30-0-rc2/fixture`](support/lake-launched-position-context-v4-30-0-rc2/fixture).
  - [`support/lake-nested-constructor-goal-positions-v4-30-0-rc2/probe.py`](support/lake-nested-constructor-goal-positions-v4-30-0-rc2/probe.py) (SHA-256 `1ef7547483edd5cf5830a62f1275c7fd356ad8fd50e76d5484a7f235a3f9dc43`), [`support/lake-nested-constructor-goal-positions-v4-30-0-rc2/results.json`](support/lake-nested-constructor-goal-positions-v4-30-0-rc2/results.json), [`support/lake-nested-constructor-goal-positions-v4-30-0-rc2/check.py`](support/lake-nested-constructor-goal-positions-v4-30-0-rc2/check.py), and [`support/lake-nested-constructor-goal-positions-v4-30-0-rc2/fixture`](support/lake-nested-constructor-goal-positions-v4-30-0-rc2/fixture).
  - [`support/lake-reflexive-term-goal-positions-v4-30-0-rc2/probe.py`](support/lake-reflexive-term-goal-positions-v4-30-0-rc2/probe.py) (SHA-256 `9f17d45428378c76bd5995e3c7ea20b31223562b0a594dd75cba52f78576fb16`), [`support/lake-reflexive-term-goal-positions-v4-30-0-rc2/results.json`](support/lake-reflexive-term-goal-positions-v4-30-0-rc2/results.json), [`support/lake-reflexive-term-goal-positions-v4-30-0-rc2/check.py`](support/lake-reflexive-term-goal-positions-v4-30-0-rc2/check.py), and [`support/lake-reflexive-term-goal-positions-v4-30-0-rc2/fixture`](support/lake-reflexive-term-goal-positions-v4-30-0-rc2/fixture).
  - [`support/lake-rich-term-goal-nested/probe.py`](support/lake-rich-term-goal-nested/probe.py), [`support/lake-rich-term-goal-nested/results.json`](support/lake-rich-term-goal-nested/results.json), [`support/lake-rich-term-goal-nested/check.py`](support/lake-rich-term-goal-nested/check.py), and [`support/lake-rich-term-goal-nested/fixture`](support/lake-rich-term-goal-nested/fixture).
  - [`support/lake-unsaved-macro-error-positions-v4-30-0-rc2/probe.py`](support/lake-unsaved-macro-error-positions-v4-30-0-rc2/probe.py), [`support/lake-unsaved-macro-error-positions-v4-30-0-rc2/results.json`](support/lake-unsaved-macro-error-positions-v4-30-0-rc2/results.json), [`support/lake-unsaved-macro-error-positions-v4-30-0-rc2/check.py`](support/lake-unsaved-macro-error-positions-v4-30-0-rc2/check.py), and [`support/lake-unsaved-macro-error-positions-v4-30-0-rc2/fixture`](support/lake-unsaved-macro-error-positions-v4-30-0-rc2/fixture).

## Revalidation

Run all offline verification scripts without starting Lean or Lake:

```sh
python3 support/macro-tactic-position-recovery-v4-30-0-rc2/check.py
python3 support/nested-tactic-position-grid-v4-30-0-rc2/check.py
python3 support/nested-unsaved-recovery-grid-v4-30-0-rc2/check.py
python3 support/partial-elaboration-queries-v4-30-0-rc2/summarize.py
python3 support/rich-goal-unsaved-recovery-v4-30-0-rc2/check.py
python3 -B support/lake-launched-position-context-v4-30-0-rc2/check.py
python3 -B support/lake-nested-constructor-goal-positions-v4-30-0-rc2/check.py
python3 -B support/lake-reflexive-term-goal-positions-v4-30-0-rc2/check.py
python3 -B support/lake-rich-term-goal-nested/check.py
python3 -B support/lake-unsaved-macro-error-positions-v4-30-0-rc2/check.py
```

To re-run any live probe, invoke the corresponding `probe.py` (passing `--work <absent-private-dir> --output <new-results-json>` for the Lake suites, or setting `LEAN_BIN` to the pinned `v4.30.0-rc2` binary) and re-verify with `check.py` / `summarize.py`.
