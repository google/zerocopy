# Abstraction-Design V1 Result

## Result

The added abstraction-design workflow produced a large, repeatable improvement
on its central purpose, but this revision **does not pass the preregistered
gates**.

Most importantly, no treatment report certified an unimplemented proposal as
`PROVED`, while 16 of 27 core-ablation reports did. The treatment also equaled
or exceeded the ablation's adjudicated atom recovery in every mode. However,
two treatment reports incorrectly proved an actually unsound Rust-1.70 pointer
loop, and treatment agents repeatedly mislabeled behavioral postconditions in
executions containing UB. The zero-hard-error gate and the per-atom recovery
gate therefore fail.

This is an exploratory result about the exact frozen skill, comparator,
fixtures, prompts, hosted agents, and environment recorded in
[`manifest.md`](manifest.md). It is not a universal claim about the skill or
unsafe-Rust review.

## Frozen experiment

- 9 capability modes, 2 conditions, and 3 fresh replicates per cell: 54 valid
  reports.
- Treatment: the complete frozen `unsafe-rust` package.
- Comparator: the same package with only the abstraction-design workflow and
  its routing/report cross-references removed. It is a **core ablation**, not a
  no-skill or previous-release baseline.
- Source-only review; targets were neither modified nor executed.
- All reports remained below the frozen 1,400-word cap.
- Treatment tree digest:
  `d97b9ace50109216614fbb7c975ac9c97508bfa928381d247869699593a2bcdd`.
- Comparator tree digest:
  `7ae4d42abd086720ed97bf1ef8b22f66b1d0ed33a0a5834b17eebfdc245c4d52`.
- Report-tree digest:
  `5e4adb0ccddb368282c95116278b980b0b1fc859f50116310e440f79a18fb649`.
- Blind-score/adjudication-tree digest:
  `a0772c8375ff573c6e571676b63411d2370b735c9a0a17cb431d94852b325240`.

The raw reports are in [`reports/`](reports/), raw anonymous scores and
adjudications are in [`blind-scores/`](blind-scores/), and condition identities
are disclosed only in the manifest after report collection.

## Raw blind scores

These are the scorers' original atom totals before condition unblinding and
semantic/rubric adjudication. H's hard-error flags were explicitly conditional
on disputed pointer semantics, so raw hard-error counts for H are not reduced
to a number.

| Mode | Treatment atoms | Core-ablation atoms | Treatment hard-error reports | Ablation hard-error reports |
|---|---:|---:|---:|---:|
| A — immutable acceptance | 11/12 | 10/12 | 0/3 | 0/3 |
| R — projection redesign | 15/21 | 8/21 | 0/3 | 1/3 |
| T — ticket obligation | 15/15 | 12/15 | 0/3 | 3/3 |
| P — published contract | 13/15 | 13/15 | 0/3 | 0/3 |
| C — configuration domain | 15/15 | 12/15 | 0/3 | 3/3 |
| S — sealed boundary | 12/15 | 10/15 | 0/3 | 3/3 |
| G — greenfield design | 15/15 | 12/15 | 0/3 | 3/3 |
| H — proof/performance tradeoff | 10/15 | 10/15 | conditional | conditional |
| N — new implemented snapshot | 14/15 | 15/15 | 0/3 | 0/3 |

The protocol intentionally does not pool these heterogeneous modes into one
headline accuracy theorem.

## Adjudicated scores

The adjudication applies equivalent-reasoning and exact-version semantic
corrections symmetrically to both conditions. Raw score files remain unchanged.

| Mode | Treatment atoms | Core-ablation atoms | Treatment hard-error reports | Ablation hard-error reports |
|---|---:|---:|---:|---:|
| A — immutable acceptance | 12/12 | 12/12 | 0/3 | 0/3 |
| R — projection redesign | 21/21 | 14/21 | 0/3 | 1/3 |
| T — ticket obligation | 13/15 | 11/15 | 0/3 | 3/3 |
| P — published contract | 15/15 | 15/15 | 0/3 | 0/3 |
| C — configuration domain | 13/15 | 12/15 | 0/3 | 3/3 |
| S — sealed boundary | 15/15 | 12/15 | 0/3 | 3/3 |
| G — greenfield design | 15/15 | 12/15 | 0/3 | 3/3 |
| H — proof/performance tradeoff | 11/15 | 9/15 | 2/3 | 3/3 |
| N — new implemented snapshot | 15/15 | 15/15 | 0/3 | 0/3 |

The treatment has no adjudicated per-mode atom regression. A, P, and N are
ties; R, T, C, S, G, and H favor treatment. This is descriptive evidence, not
a causal theorem: the platform does not expose a fixed seed or precise hosted
model identity, and physical filesystem isolation was procedural.

## Gate disposition

| Preregistered gate | Result | Evidence |
|---|---|---|
| Zero treatment hard errors | **FAIL** | `r043` and `r044` incorrectly give the current H loop `PROVED`; the exact supported Rust-1.70 artifact is unsound. |
| Every atom passes in at least 2/3 treatment replicates | **FAIL** | T1, C1, H1, and H4 each pass only 1/3 after adjudication. |
| A1–A3, R1, P2–P4, C3–C4, and N1–N4 pass 3/3 treatment | **PASS** | All listed firewall, support-preservation, and fresh-snapshot atoms pass under equivalent-reasoning calibration. |
| No treatment run launders T's obligation or calls G's sketch proved | **PASS** | All six relevant treatment reports keep enforcement local and proposals uncertified. |

The overall preregistered result is therefore **FAIL**. The failure should not
be softened merely because treatment substantially outperformed the ablation.

## Confirmed improvement: proposal/snapshot firewall

The strongest result is direct and consistent. Across the 27 treatment reports,
no agent called an unimplemented candidate `PROVED`. Across the 27 ablation
reports, 16 did:

- R: 1/3 ablation reports;
- T, C, S, G, and H: 3/3 ablation reports in each mode.

The treatment agents instead separated the current artifact, design
requirements, conditional candidate proof, compatibility consequences, and
fresh exact-source audit. This confirms the hypothesized benefit of making
abstraction design an explicit workflow rather than leaving agents to compose
ordinary audit guidance unaided.

Treatment also recovered the desired parsimonious designs: direct safe
specialization for the one-off projection, checked `NonZeroUsize` construction,
checked character conversion across configurations, a private sealed leaf
boundary, safe `split_at_mut`, and receiver-bound lifetimes for both `View`
accessors. It preserved immutable-review scope and published 1.x contracts.

## Genuine treatment failures

### UB does not prove a behavioral counterexample

In T, treatment reports `r013` and `r014` correctly found UB but also labeled
the mandatory panic postcondition `CONTRACT-BROKEN`. In C, `r025` and `r027`
made the same mistake for the surrogate-panic promise. An execution containing
UB has no defined observation from which to prove “did not panic”; the
behavioral theorem is `UNPROVED` or not guaranteed unless a separate defined
counterexample exists.

The skill's formal verdict definition already says `CONTRACT-BROKEN` requires a
false postcondition even though UB need not occur. The 2/3 repeated treatment
failure shows that this implication is not operationally salient enough. A
future revision should state the decision rule directly at the proof workflow
and reporting sites, with the same-execution UB case as an explicit forbidden
classification.

### Exact-version pointer proof

The initial H oracle expected the current pointer loop to be provable. That
oracle was wrong. Rust 1.70's
[`pointer::add`](https://doc.rust-lang.org/1.70.0/std/primitive.pointer.html#method.add)
requires both pointers to be in or one-past the same allocated object and has
no zero-offset exception. Rust 1.70's
[`slice::from_raw_parts`](https://doc.rust-lang.org/1.70.0/std/slice/fn.from_raw_parts.html#safety)
allows an aligned dangling pointer for a zero-length slice. Consequently,
`total(&[])` can execute `ptr.add(0)` on a dangling pointer and reach UB before
the loop condition.

Treatment `r045` found this exact valid-use witness. Treatment `r043` and
`r044` instead generalized constructor/slice facts too far and gave the loop
`PROVED`; both are hard errors. All three ablation reports also missed the
strongest verdict. The detailed independent analysis is
[`blind-scores/adjudication-H.md`](blind-scores/adjudication-H.md).

This is simultaneously a skill/agent failure and a successful open-world test:
the treatment helped one agent falsify the evaluator's own oracle, but only one
of three treatment replicates followed the exact-version contract rigorously
enough. The next revision should make the final `PROVED` checkpoint demand an
operation-clause ledger for the earliest supported Rust version and explicit
empty, dangling, zero-offset, one-past, ZST, and arithmetic-boundary cases when
applicable. Constructor safety requirements must not be promoted to universal
type invariants without an authoritative type-level premise.

## Evaluator corrections, not skill defects

Several raw atoms rewarded extra prose rather than stronger reasoning. The
independent rubric adjudication corrected these symmetrically:

- a report need not list every unused intent-evidence channel;
- specialization need not mention a future generic projection abstraction;
- an agent need not reject cosmetic, fabricated, unsafe-trait, or plain-sum
  alternatives it never proposed;
- a compatible 1.x simplification need not use one particular private-helper
  syntax; and
- one complete safe UB witness is enough when the shared lifetime defect, both
  accessors, and the two-method repair are explicitly covered.

These corrections follow the frozen plan's equivalent-reasoning rule and the
skill's instruction not to pad reports with dominated alternatives. See
[`blind-scores/adjudication-rubric.md`](blind-scores/adjudication-rubric.md).
Future fixture atoms should encode necessary propositions, not preferred
candidate inventories or redundant counterexamples. Version-sensitive oracles
should also receive an independent exact-documentation review before freezing.

## Relationship to the legacy suite

The unchanged legacy suite was rerun before this experiment. It found no hard
regression: both conditions recovered all 78 synthetic vulnerable-case points,
the historical defect/fix pair was recovered, and treatment better surfaced
proof debt in fixed controls and the current challenge. The current challenge
still exposed a missed indirect `Copy`/`UnsafeCell` proof, so the legacy result
is not a universal pass. See
[`../2026-07-31-legacy-regression/result.md`](../2026-07-31-legacy-regression/result.md).

## Disposition

Keep the evaluated skill snapshot frozen as the result's treatment artifact.
Do not patch it in place after observing these reports. The abstraction-design
addition is supported as a material improvement, especially for parsimony and
proposal/snapshot separation, but the revision is not yet release-gate clean.
A subsequent revision should address the two genuine failure classes above and
rerun at least T, C, H, the legacy challenge, and unchanged acceptance/public-
contract controls under a new digest.
