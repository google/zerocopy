# V4 Focused Evaluation: Qualitative Findings

## Status

The preregistered V4 gate failed. The frozen reports, blind scores,
adjudications, and aggregate remain the result of record; this post-unblinding
analysis does not amend them.

The run collected all 50 planned reports across five modes and two conditions.
Every canonical report was valid UTF-8, within its word budget, and free of a
known operational-scope deviation or semantic noncompletion. Ten blind
scorers, five consistency reviewers, and blind adjudicators produced the final
scores. The static manifests, byte-tree identities, packets, attempt
preservation, event chain, reveal, and aggregate validate.

The exact official result is in [results/summary.md](results/summary.md):

- `P`: V4 passed 135/135 atom instances; V3 passed 124/135;
- `B`: V4 passed 25/75; V3 passed 8/75;
- `L`: V4 passed 40/55; V3 passed 46/55;
- `Q`: both conditions passed 25/25; and
- `R`: V4 passed 27/35; V3 passed 23/35.

These totals are descriptive, not interchangeable measurements. A single
missing premise can block several dependent atoms, reports within a condition
share one package, and the modes test different capabilities. The frozen gate
required every V4 atom to pass 5/5, no hard error or TCB/authority defect, and
the other preregistered integrity and control conditions. V4 therefore cannot
be a release candidate or the terminal `VN`.

## What V4 Demonstrated

Mode `P` gives strong fixture-specific evidence for exact bounded predicates,
directional set witnesses, full case domains, conservative containment,
composite-`cfg` authority, rejection regions, branch proofs, closure ledgers,
and TCB-qualified conclusions. Its apparent V3-to-V4 gain is correlated: one
V3 report accounts for all eleven missed instances. The prompt also requested
most of the scored artifacts expressly, so this is a targeted regression
success rather than broad evidence of spontaneous transfer.

Mode `Q` preserved the intended distinction among caller-validity domains,
implementation-safety domains, complete UB witnesses, and missing dependency
theorems. It also preserved the distinction between `UNSOUND` and `UNPROVED`
without inventing a witness. The exact fixture is now saturated across recent
runs. It remains useful as a regression control but cannot serve as a fresh
confirmatory holdout again.

All ten `B` reports found the same real configuration-dependent defect, the
same witness, the same maximal positive region, and the intended staged build
relation. All ten `R` reports found the valid safe-use counterexample,
correctly rejected the existing abstraction, and proposed the intended safe
nongeneric design while requiring a fresh audit. The failures in these modes
were therefore not failures to understand the unsafe code's central hazard or
the abstraction's intent.

Mode `L` continued to distinguish an implementation proof from the adequacy of
its existing safety comment. Its failures likewise arose mostly at the
boundary between a correct argument in the model's head and a complete,
reviewable evidence certificate.

## Dominant Root Cause: Visible Syntax Is Not Its Semantics

The recurring V4 defect was an incomplete transition from inspected source to
an authoritative semantic proposition. Reports often treated a token,
declaration, expression, or control-flow shape as if inspection alone proved
what compiling or executing it means.

A rigorous proof needs three distinct kinds of proposition:

1. **Artifact facts** describe literal properties of the audited material:
   tokens, declarations, ordering, attributes, type annotations, generated
   text, or other directly inspected structure.
2. **Rust axioms** state the applicable meaning assigned to those facts by the
   version-matched Rust Reference or standard-library contract.
3. **Derived lemmas** follow from artifact facts, Rust axioms, accepted TCB
   entries, and explicit logical or mathematical steps.

Inspection can establish that an `if`, call expression, subtraction, `cfg`,
match arm, or omitted return expression is present. It does not by itself
establish branch selection, callee execution, arithmetic behavior, source
inclusion, exhaustiveness, or the value returned. Those are semantic edges.
Every semantic edge consumed by a soundness or behavior conclusion needs an
applicable axiom and an exact excerpt that entails the proposition used.

This distinction is more useful than a growing list of Rust constructs. The
Reference and standard-library documentation remain the ground truth, and any
example list in the skill would be advisory and liable to omission or
bit-rot.

## Mode B: The Build Model Was Learned; Its Proof Was Not Closed

V4 materially improved the substantive build/configuration reasoning. Every
report recovered the correct target/feature/allocator domain, the relevant
ordered and fallible build behavior, the reachable bad cell, and the positive
remainder. Yet four of five reports were officially defective.

The cleanest diagnostic example is report `D` (`r027`). It omitted authority
for the semantic effect of returning from `main` by reaching the end of its
body. That single missing leaf blocked the later build outcome and closure,
causing nine dependent atom failures plus global and mode-specific defects.
Other reports omitted or compressed related semantic edges, including the
effect of successful output, match selection or exhaustiveness, tuple and
literal matching, composite `cfg` behavior, comparison, and branch execution.

This is not evidence that the skill needs a checklist containing those exact
constructs. It is evidence that its existing reverse-trace instruction was
not operational or salient enough to prevent a verdict before every semantic
edge had evidence. A report which names the right source construct and cites a
page about the general topic has not necessarily stated or proved the exact
proposition it consumes.

The official aggregate contains one nominally fully passing V4 `B` report,
`E` (`r045`). Independent post-unblinding review found that this is a scorer
false pass. Its authority says that calls execute their function bodies, but
never extracts the propositions that an omitted return type is unit or that a
function implicitly returns its body value. Its block excerpt covers component
statements, while the source `match` is the block's optional final operand.
The report then asserts that `main` returns normally after successful writes.
The rubric expressly requires that leaf for `B3` and `B4`; later source
selection, reachability, and closure claims consume it. Both raw scorers
accepted the same omission, so it never reached adjudication. This strengthens
the diagnosis but does not alter the frozen official score.

## Mode L: Exact Entailment and Numeric Semantics

V4 reports `E` (`r019`) and `F` (`r007`) reasoned from non-emptiness to a valid
last index but did not close the Rust premises for `len`'s return type, the
`usize` value domain, built-in subtraction, and overflow/profile behavior.
Both nonetheless claimed that no such semantic facts were silently consumed.
That contradiction is precisely what final evidence reconciliation should
catch.

Report `J` (`r041`) had an otherwise complete proof, but its quoted `if`
material did not entail the exact direction it consumed: that taking the true
branch skips the `else` branch. Across both conditions, seven of ten `L`
reports cited the right page and stated the right conclusion while extracting
prose that supported only a different direction or an incomplete implication.

The V4 numeric regression is real in this sample, but five coherent-package
replicates cannot establish that the V4 edit caused it. V4 already contained a
general reverse-trace rule, and two reports simply failed to follow it. The
appropriate response is to make exact evidence closure a compact mandatory
step, not to add integer- or `if`-specific doctrine.

## Mode R: One Missing Valid-Use Leaf

The five defective `R` reports—two V4 and three V3—share one root omission.
Every one constructed the downstream safe call, reached the out-of-bounds
unchecked access, cited its UB contract, returned `UNSOUND`, and proposed a
conditional safe redesign. None cited the exact Rust authority needed to show
that calling the ordinary `fn` imposed no caller-side unsafe obligation. The
five clean reports all supplied that authority.

The frozen dependency graph then propagated that missing leaf through four
atoms. This application is consistent with the frozen rubric, but the
aggregate obscures the diagnosis: it appears to record four conceptual
failures even though the reachability, UB consequence, verdict, and redesign
were directly present. Future evaluators should preserve dependency semantics
while reporting both each atom's direct decision and any `blocked_by` cause,
then aggregate root failures separately.

No change to the abstraction-design doctrine is supported by this mode.
Abstraction recovery, proposal generation, parsimony, conditionality, and
fresh-audit requirements were all directly reliable. The missing capability
is a reusable valid-use certificate that separately closes accessibility,
well-typedness/coherence, documented contracts, ordinary versus unsafe caller
or implementer obligations, and any additional TCB premise.

## Holistic V5 Direction

V5 should consolidate the runtime material around one short, mandatory proof
kernel at the point where a conclusion is issued:

```text
artifact fact
  + exact applicable Rust/stdlib axiom
  + explicit logic or mathematics
  -> derived proposition
  -> consumer or verdict
```

For every edge, the report must state the exact proposition, provide an excerpt
that entails it, establish version and case applicability, and identify how it
is consumed. A final direction check should translate the excerpt and claimed
proposition into implication form and reject an unjustified converse,
contrapositive, strengthening, or domain change.

This kernel should replace scattered and partly duplicative evidence-closure
instructions. It should not create a second proof graph or mandatory global
schema. Ordinary prose or the existing obligation ledger is sufficient if a
reviewer can reverse-trace every conclusion without reconstructing a missing
edge. Reusable, checked axiom identifiers may avoid repetition, but every use
must remain applicable and auditable.

The same kernel should contain a compact valid-use subroutine for
counterexamples and API theorems. It must close the actual safe reachability
and typing path—including the absence or satisfaction of relevant unsafe
obligations—before using that path to refute soundness. The existing full-case,
staged-build, verdict, robustness, module-boundary, TCB, and abstraction-design
material remains load-bearing. Conditional configuration references should be
routed only when those transformations are present.

When an auditor must reconstruct a missing proof in order to accept code, the
audit report should present that reconstructed proof. Silent reconstruction
would deprive the author of the evidence needed to repair the safety comment.

## Evaluation and Protocol Corrections

The next evaluation should make these corrections before collection:

- score root decisions separately from dependency-propagated failures;
- resolve the observed `P` rubric ambiguities about overlapping authority
  defects and whether a TCB qualification may be inherited implicitly;
- replace the saturated `Q` target with an unseen metamorphic holdout that
  varies names, control flow, unsafe operation, dependency shape, and tempting
  false witnesses while preserving its core distinctions;
- test isolated semantic-edge certificates for implicit return, match or
  branch selection, configuration selection, numeric operations, and ordinary
  safe calls, followed by naturalistic full `B`, `L`, and `R` audits;
- machine-materialize every preregistered gate clause, including disposition of
  flagged cells, adjudication/challenge completion, integrity validation, and
  independent controls;
- define objectively whether verified report bytes are scored when a later
  orchestration failure occurs. In `r022`, attempt 1 wrote a complete-looking
  report before a coordinator failure and was retried, creating avoidable
  selection ambiguity;
- preserve reviewer packets and reasoning, not only terse signoffs;
- prefer immutable offline authority snapshots or a content-gated proxy over
  procedural isolation from live documentation;
- diversify evaluator implementations where practical; and
- record each package identity algorithm explicitly, including both legacy and
  byte-tree hashes when both are relevant.

## Terminal `VN` Rule

The project must not stop when a version merely appears good after repeated
inspection. Before the final confirmatory sequence, freeze:

1. a finite maximum number of candidate versions `N_max`;
2. mutually disjoint, opaque holdout cohorts `H1 ... HN_max`;
3. replicate counts, retry and invalidation rules, all atom, hard-error,
   authority, integrity, control, and robustness gates; and
4. the exact conjunctive stopping predicate.

Candidate `Vn` receives exactly one confirmatory look at `Hn`. The complete
cohort must finish; a favorable subset cannot produce success. A
preregistered fail-fast rule may terminate a candidate after an irreversible
gate failure, but only as a recorded failure. Once any part of `Hn` is
revealed, it may become a regression fixture but can never confirm `Vn` or a
later candidate. Any modified package is `V(n+1)` and receives untouched
`H(n+1)`.

Declare `VN` done at the first `n` for which every frozen gate passes on the
entire fresh cohort and no evidence-backed, in-scope material defect remains
after the preregistered adversarial review. The package must also be internally
coherent: its runtime instructions, routed references, templates, and
maintainer rationale must express the same model without stale duplication or
contradiction. Known limitations and explicit TCB admissions are recorded;
they are not silently converted into proof.

If no candidate passes by `N_max`, the sequence terminates without a successful
`VN`; a new evaluation design must be frozen before more testing. If the claim
is statistical rather than an exact engineering gate, the protocol must also
predeclare an across-version error-control method, because fresh cohorts alone
do not eliminate optional-stopping inflation.

Thus “done” means the first full pass of a finite, preregistered, fail-closed
procedure—not perfection, and not an assertion that no future counterexample
can exist. The defensible claim is that no known material defect remains after
saturated adversarial testing and one untouched confirmatory evaluation under
the frozen rule.

## Integrity Limitations

The run was well preserved and internally auditable, but interpretation must
retain these limits:

- report generation, scoring, consistency review, and adjudication used the
  same model family in fresh contexts;
- blinding hid condition labels but could not eliminate stylistic package
  fingerprinting;
- V4 was a coherent multi-file package change, not a causal ablation of one
  instruction;
- the two non-author freeze signoffs do not preserve their underlying review
  packets or reasoning;
- authority isolation was procedural and depended on live retrieval;
- `P` was unusually explicit and `Q` was saturated; and
- five replicates per cell are an engineering screen, not a population
  estimate.

## Evidence Index

The principal preserved evidence is:

- aggregate and gate result:
  [results/aggregate.json](results/aggregate.json) and
  [results/summary.md](results/summary.md);
- blinded identities and schedule:
  [sealed/condition-map.tsv](sealed/condition-map.tsv),
  [sealed/blind-map.tsv](sealed/blind-map.tsv), and
  [sealed/launch-schedule.tsv](sealed/launch-schedule.tsv);
- frozen rubrics: [freeze/rubrics](freeze/rubrics);
- canonical reports and preserved attempts:
  [collection/attempts](collection/attempts);
- raw, consistency, adjudicated, and final scoring:
  [scoring](scoring); and
- the chained protocol record: [events.jsonl](events.jsonl).

The requested final process retrospective remains deferred until all skill and
meta-document revisions and evaluation rounds are complete. The separate
zerocopy-wide review of `#[doc(hidden)]` use likewise remains deferred until
the skill is final.
