# V3 Targeted Confirmation: Qualitative Findings

## Status

The preregistered V3 gate failed. This run is preserved as evidence about the
frozen V3 package, not rewritten into a passing result.

The run collected all 80 planned reports, obtained all 16 blind scores, used
blind adjudication for the four modes with scorer disagreement, and produced
the frozen aggregate in [results/aggregate.json](results/aggregate.json). Three
first report attempts were lost to orchestration interruption and were
preserved as `ORCHESTRATOR_TOOL_FAILURE`; their second attempts completed. No
canonical report had an operational scope deviation, semantic noncompletion,
or word-budget defect.

The candidate passed 272 of 300 atom decisions. That aggregate number is only
descriptive: modes are heterogeneous, and the preregistered rule required every
V3 atom to pass in all five replicates. The exact result is in
[results/summary.md](results/summary.md):

- every atom passed 5/5 in `S`, `Q`, `W`, `M`, `R`, and `K`;
- `C1` passed 1/5 and `C3`–`C5` passed 3/5;
- `X4`, `X6`, and `X7` passed 0/5, while `X11` passed 2/5;
- two `C` reports contained hard errors and TCB/authority defects; and
- one `K` report had a TCB/authority-accounting defect without a hard error.

The frozen V3 package is byte-identical to the current `skills/unsafe-rust`
package at the time of this analysis. V2 is a coherent diagnostic comparator,
not a causal ablation. Exact hosted model-build and sampling-seed metadata were
unavailable, and host isolation was procedural.

## What V3 Demonstrated Reliably

The six modes outside `C` and `X` produced 205/205 V3 atom passes across 30
reports. Twenty-nine of those reports had no scored defect. This is strong
fixture-specific evidence that the model-plus-skill can perform:

- symbolic support-domain and multi-release coverage;
- correct separation of incomplete universal proofs from complete existential
  UB certificates;
- whole-execution reasoning for postconditions in the presence of UB;
- exact-version and admitted compatibility-premise reasoning;
- current-artifact verdicts separated from abstraction redesign; and
- continued review after finding one unsound surface, including reconstructed
  local proofs and literal unsafe-trait contracts.

V2 also reached the ceiling on those atoms, so this is replication rather than
evidence that V3 caused an improvement. Five reports per cell are an engineering
screen, not a population estimate or release-readiness claim.

## Failure Analysis

### C1: predicate relationships need an explicit proof

All five V3 reports reproduced both nonlinear policy predicates and passed the
conservative-domain atom. Only one explicitly pinned a Scarlet-only case and
an Indigo-only case, so `C1` passed 1/5.

The code and domain reasoning were not generally lost. The missed proposition
was the asserted relationship between the two predicates. Reproducing both
formulas and correctly normalizing their union does not itself expose a proof
that neither predicate contains the other. For proof-grade reporting, a claim
of incomparability needs a separating witness for each failed containment
direction, just as equality needs both containments.

There is also an evaluation-alignment issue. The user request asked for the
strongest conclusion without choosing a policy but did not expressly request
separating witnesses. The hidden rubric used “identifies a region” as a strict
reporting requirement. Future tasks should either request the relationship
certificate explicitly or define when a symbolic derivation is sufficient.

### C3–C5: one omitted proof edge cascaded into several failures

V3 reports `r046` and `r010` correctly derived the conservative union and
correctly proved the local `unwrap_or` and guarded `unwrap_unchecked` bodies.
They cited the `cfg` attribute's include/remove behavior and `compile_error!`,
but did not state and narrowly cite the applicable Rust semantics of `all` and
`not`. `BUILD-MAP-C` expressly supplied only Cargo feature/target leaf mappings
and no Rust semantics.

Both reports nevertheless asserted exact body selection, effective rejection,
`Required ⊆ Covered`, and full `PROVED` verdicts. Strict adjudication therefore
failed `C3`–`C5`, applied `G11`, `CH2`, and `CH6`, and marked a TCB/authority
defect. This is one missing semantic bridge per report, not three independent
unsafe-code reasoning defects.

The current skill already requires every material premise and inference to be
explicit, applicable, and authoritative. Three V3 reports and all five V2
reports supplied the missing semantics. The result is best classified as a
stochastic adherence failure that exposes insufficient reliability of the
final closure check, not absence of the underlying rule and not evidence that
V3 caused a regression.

One additional V3 `C` report twice attributed `unwrap_unchecked` to source line
22 when it was on line 20. That factual error was preserved as a novel finding
but did not enter the preregistered defective-report count.

### X4, X6, and X7: the build pipeline was compressed into a mapping

Every report recovered the external selector partition, accepted selector to
allocator-cfg mapping, simultaneous target/feature/allocator UB cell, genuine
wasm/arena exclusion, and final source reachability. None of the five V3
reports proved the complete ordered and fallible build-script relation required
by `X4`, `X6`, and `X7`.

The source first attempts the rerun directive, then the check-cfg directive,
then reads and classifies the environment input, and finally emits a selected
cfg. Either earlier output write can fail before selector handling. A complete
proof therefore distinguishes at least:

1. failure of the first write;
2. first-write success followed by failure of the second;
3. both writes succeeding followed by selector rejection; and
4. all prerequisite writes and selector handling succeeding, with exactly the
   resulting directives and Cargo effects.

Reports generally summarized this as “invalid selectors panic; stdout failure
produces no compilation; BUILD-MAP-X supplies rerun/check-cfg/cfg behavior.”
That proves important endpoints but not the staged relation, exact ordering,
or the proposition that an earlier failure preempts later handling.

This exposes a runtime architecture gap. The configuration reference tells the
agent to audit build scripts and every path producing different output, but it
does not operationalize a build as an ordered, fallible transducer from inputs
through effects and exits to compiler-selected source. The correction should
be that general model, not Cargo- or fixture-specific directive trivia.

The evaluation also overbundled some requirements. `X4` combined selector
policy rejection with an infrastructure prefix path and produced five scorer
disagreements. `X6` and `X7` made exact directive bookkeeping primary atoms even
though the task did not separately name those theorems. Such details are valid
audit obligations when they affect configuration freshness or reachability,
but future fixtures should make that semantic dependency explicit.

### X11: a useful regional theorem, but not required to close `UNSOUND`

Two V3 reports proved the exact positive region:

```text
(Required \ Q_X) × every u8
  ∪ Q_X × {1..=255}.
```

The other three proved every input outside `Q_X` and supplied the zero-input UB
witness inside `Q_X`, but did not separately prove the nonzero inputs there.

This result reveals a wording inconsistency worth fixing: the core skill defines
`case` across configurations, inputs, states, and executions, while the
configuration reference sometimes speaks only of `Covered(configuration)`.
Coverage must retain every dimension relevant to the claim.

It does not follow that every audit which closes `UNSOUND` must compute a
maximal positive remainder. One valid existential certificate refutes the
universal soundness claim, while comprehensive review still requires a
disposition for every independent surface and obligation. `X11` demanded an
additional regional theorem that was useful but not explicitly requested.
Future scoring should require maximal or exact regional classification only
when the task asks for it; any regional theorem actually asserted must of
course retain the full case tuple and be proved exactly.

The V2/V3 comparison for `X11` is additionally unreliable. Both scorers passed
V2 report `F` by claiming it affirmatively proved nonzero inputs in `Q_X`, but
the report only identified zero as the failing case—the same proof shape that
adjudication rejected in comparable reports. Because both scorers made the
same error, the cell never reached adjudication. The reported V2 4/5 therefore
is not calibrated consistently with V3 2/5.

### K: correct proof, incomplete citation inventory

V3 report `r016` passed all eight `K` atoms and had no hard error. It correctly
derived false `is_empty` ⇒ `len > 0` ⇒ representable `len - 1 < len`, but
cited only the arithmetic-operator rules while asserting that its listed
authorities were complete. It omitted the available version-matched authority
for the unsigned `usize` domain.

Adjudication correctly kept the implementation proof and all atoms: the report
had invoked the right proposition, and the permitted authority verified it.
It nevertheless retained the TCB/authority-accounting defect because the
report itself did not cite or inventory that consumed proposition. This is a
narrow provenance failure, not bad unsafe-Rust reasoning. Like the `C` cascade,
it supports a final premise-to-citation reconciliation pass rather than a new
integer-specific rule.

### V2 R: the recorded scope defect is a scorer false positive

Both scorers marked V2 report `r011` for prohibited package inspection because
it disclosed the evaluated skill digest. The report prompt expressly required
the agent to read the supplied package, and the V2 report template required the
skill revision. The disclosed digest matched that permitted package. This was
not sibling or condition-map inspection.

Agreement prevented adjudication, so the aggregate preserves the flag. It
should be treated as an evaluation defect and does not affect the V3 gate.
Future rubrics must define scope flags precisely, state that permitted package
identity may be reported, and independently review every positive global
defect flag even when two scorers agree.

## Holistic V4 Direction

The runtime package should not accumulate `cfg(all)`, `println!`, `usize`, or
fixture-specific checklist bullets. It should make the existing proof model
harder to compress incorrectly.

The coherent revision should have one reusable certificate discipline:

1. Preserve one full `Case` domain through policy, build/configuration, API
   input/state, and execution reasoning. References may project it for local
   discussion but must not redefine claim coverage at a coarser granularity.
2. For every claimed relationship or proof edge, state the exact proposition,
   applicability, derivation or witness, premise source, and consumer. This may
   live in ordinary proof prose or the existing obligation ledger; no explicit
   dependency graph or second record schema is required.
3. Prove predicate relationships according to the relation asserted: both
   containments for equality, containment plus a separating witness for strict
   containment, and a witness in each set difference for incomparability.
4. Model build and generation machinery as a staged relation from inputs,
   through ordered and fallible local operations and emitted effects, through
   build-tool interpretation, to compiler-selected artifacts and source. Cover
   alternative exits and partial progress before consuming later-stage facts.
5. Before any affirmative certificate, reverse-trace every conclusion to
   explicit local facts, mathematical steps, authoritative Rust propositions,
   tool theorems, or accepted TCB entries. Reconcile every material Rust leaf
   with the exact quotation/link and applicability recorded in the report.
6. Preserve the existing quantifier-sensitive verdict rules. `UNSOUND` closes
   existentially; it neither excuses auditing other surfaces nor creates an
   unnecessary requirement to maximize every positive remainder.

This is a refinement and consolidation of the obligation/domain workflow, not
a new ontology. Existing duplicated uses of `Covered(configuration)` and broad
“cfg/build mapping” shorthand should be replaced where the full-case and staged
relation make them unnecessary.

The report template should instantiate the same model with an optional staged
configuration table and a stronger final proof-edge/premise attestation. The
maintainer rationale should record why these requirements are load-bearing and
why no explicit proof graph or fixture taxonomy is imposed.

## Evaluation Corrections and Next Sequence

Before the next run:

- fix adjudication packet identity so read-only hardening cannot conflict with
  permission-sensitive target identity checks;
- define global defect flags precisely and adjudicate every positive flag;
- add a cross-report consistency review for atoms with heterogeneous decisions
  or other reason to suspect equivalent proof shapes were treated differently;
- split unrelated atom clauses or expressly request the combined theorem;
- require separating witnesses when predicate incomparability is scored; and
- require an exact regional map only when the task asks for one.

Then:

1. revise the runtime skill and maintainer rationale coherently and preserve it
   as V4;
2. run focused confirmation on predicate relationships, proof-edge authority,
   staged build/configuration behavior, and full-case applicability, with
   unchanged verdict and redesign controls;
3. if that passes, run the broader fresh-agent release suite; and
4. only after all skill/meta revisions and evaluation rounds are complete,
   write the deferred terse process report, split between design/brainstorming
   and empirical evaluation/iteration.

The separately requested audit of zerocopy's uses of `#[doc(hidden)]` also
remains deferred until the skill is final.

## Evidence Index

The principal preserved evidence for the conclusions above is:

- aggregate counts, defects, and failed cells:
  [results/aggregate.json](results/aggregate.json) and
  [results/summary.md](results/summary.md);
- condition and report identity:
  [sealed/condition-map.tsv](sealed/condition-map.tsv),
  [sealed/blind-map.tsv](sealed/blind-map.tsv), and
  [sealed/launch-schedule.tsv](sealed/launch-schedule.tsv);
- `C` requirements and final decisions:
  [freeze/rubrics/C.md](freeze/rubrics/C.md),
  [scoring/final/C.json](scoring/final/C.json), and
  [scoring/adjudications/C.json](scoring/adjudications/C.json);
- the two defective `C` reports:
  [r046](collection/attempts/r046/1/report.md) and
  [r010](collection/attempts/r010/1/report.md), compared with the passing V3
  reports [r077](collection/attempts/r077/1/report.md),
  [r023](collection/attempts/r023/1/report.md), and
  [r062](collection/attempts/r062/1/report.md);
- `X` requirements and final decisions:
  [freeze/rubrics/X.md](freeze/rubrics/X.md),
  [scoring/final/X.json](scoring/final/X.json), and
  [scoring/adjudications/X.json](scoring/adjudications/X.json);
- the V3 `X` reports:
  [r066](collection/attempts/r066/1/report.md),
  [r018](collection/attempts/r018/1/report.md),
  [r015](collection/attempts/r015/1/report.md),
  [r034](collection/attempts/r034/2/report.md), and
  [r064](collection/attempts/r064/1/report.md);
- the build pipeline being scored:
  [build.rs](../../fixtures/v3-targeted/x_cross/build.rs),
  [TCB.md](../../fixtures/v3-targeted/x_cross/TCB.md), and
  [src/lib.rs](../../fixtures/v3-targeted/x_cross/src/lib.rs);
- the `K` authority-accounting decision:
  [r016](collection/attempts/r016/1/report.md),
  [scoring/final/K.json](scoring/final/K.json), and
  [scoring/adjudications/K.json](scoring/adjudications/K.json); and
- the V2 `R` scope false positive:
  [r011](collection/attempts/r011/1/report.md),
  [scoring/final/R.json](scoring/final/R.json), the permitted-package wording
  in [freeze/prompts/report.md](freeze/prompts/report.md), and the V2 report
  template under the frozen package identified by
  [sealed/condition-map.tsv](sealed/condition-map.tsv).
