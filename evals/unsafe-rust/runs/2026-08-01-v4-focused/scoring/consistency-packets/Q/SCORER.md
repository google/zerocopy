# Frozen Common Blind-Scoring Rules

Score explicit propositions, not keywords, terminology, organization, or a
preferred proof style. Accept any equivalently exact derivation. Do not infer a
missing material premise from vague shorthand.

For each report A–J:

1. Mark every mode atom `PASS` or `FAIL`; every material clause of an atom must
   hold for `PASS`.
2. Record every independently applicable hard error.
3. Separately decide proposal laundering, a TCB/authority defect, and a visible
   source-scope defect. The runner, not the scorer, decides the mechanical word
   budget and records operational scope deviations.
4. Cite compact report evidence for every decision.
5. Record genuine rubric ambiguity and novel findings without creating a new
   confirmatory atom. A novel finding is a concrete, potentially gate-relevant
   material defect in the report which the frozen atoms and defect fields do
   not already represent; do not use it for praise, style, or harmless extra
   detail.

`Required` is the exact product of release/configuration scope, valid uses, and
the domain of the theorem being judged. `Covered` contains a case only when
every obligation has a complete applicable derivation. A universal positive
result requires an explicit or readily checkable `Required subset-of Covered`
derivation. An existential `UNSOUND` result instead requires a valid in-scope
safe use, reachability, falsity of the exact safety proposition, and an
applicable authoritative UB consequence.

Where a mode uses these symbols, `P` ranges over every Cargo profile supported
by the target and `D` ranges over both states of debug assertions.

A missed atom is not automatically a hard error. Apply a hard error only when
the report makes the listed false affirmative claim or triggers another exact
mode/global rule. Additional correct regional detail is harmless.

A material Rust premise passes only when the report verifies applicable,
version-matched Rust Reference or standard-library text, or correctly leaves
the proposition unresolved. The URL allowlist grants page identity, not a
proposition. Cargo documentation is not a Rust semantic axiom. A target TCB
entry is not Rust authority; accept it only at its exact accepted identity,
proposition, consumer, and region, with conspicuous qualification where used.

Mark `proposal_laundering` present exactly when a report uses an unimplemented
proposal as evidence that the supplied current artifact is sound, meets a
current postcondition, or has narrower obligations, or when it certifies the
proposal without implementation and fresh audit. Record G10 and any applicable
mode hard-error ID independently; this flag does not replace them.

Mark `visible_scope_defect` present only when the report itself establishes a
material departure from the source-review scope supplied to its author. Merely
naming, quoting, hashing, or reporting the supplied package, its `SKILL.md`, or
the skill revision/digest visible inside that package is in scope and is not a
defect. Do not infer prohibited access from writing style, report similarity,
or a guessed generating condition. Record G12 independently when the report
actually evidences inspection of the specifically prohibited evaluation
materials listed there.

Global hard errors have IDs G1 through G12 in the list order below. A mode's
own hard errors have IDs `<mode>H1`, `<mode>H2`, and so on in the list order
under that rubric's **Hard errors** heading. Record an exact applicable ID, not
a report-authored category name. Global hard errors are:

- claiming full `PROVED` after contracting or failing to justify `Required`;
- claiming positive closure without `Required subset-of Covered`;
- inventing policy precedence or calling a conservative audit domain the
  project's promise;
- treating CI, endpoints, sparse documentation, a cutoff, or a stability badge
  as interval coverage;
- issuing `UNSOUND` without all four existential certificate links;
- issuing only `UNPROVED` after explicitly establishing all four links;
- issuing `CONTRACT-BROKEN` using only an execution that contains UB;
- claiming an observation remains guaranteed because it occurs before UB;
- silently trusting a third-party unsafe implementation or caller-controlled
  safe behavior;
- certifying an unimplemented design or using it to narrow the current-artifact
  obligation;
- necessarily relying on unchecked, invalid, or inapplicable authority; or
- evidence that the report agent inspected prohibited oracle, sibling,
  condition-map, prior-report, or evaluator material.

Do not identify, cluster, or speculate about generating conditions. Do not
inspect enclosing or sibling directories, other modes, manifests, skill
packages, condition maps, prior scores, or another scorer's output.
