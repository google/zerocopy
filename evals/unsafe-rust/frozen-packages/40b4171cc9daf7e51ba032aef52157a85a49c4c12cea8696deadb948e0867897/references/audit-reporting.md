# Audit Execution and Reporting

## Contents

- [Freeze the audit claim](#freeze-the-audit-claim)
- [Maintain an obligation ledger](#maintain-an-obligation-ledger)
- [Aggregate verdicts](#aggregate-verdicts)
- [Write actionable findings](#write-actionable-findings)
- [Deliver a complete report](#deliver-a-complete-report)
- [Preserve and update the audit](#preserve-and-update-the-audit)

## Freeze the Audit Claim

Before reviewing proofs, record:

- exact repository, source revision/digest, workspace packages, generated
  artifacts, and relevant uncommitted changes;
- supported toolchain/configuration predicate, its controlling policy sources,
  conflicts or gaps, audit cutoff, authorized resolution or conservative audit
  domain, and enforced exclusions;
- dependency resolution and relevant source identities;
- API, module, binary, or whole-project scope;
- soundness theorem and documented postconditions in scope;
- TCB log identity/revision;
- prior audit results being reused;
- known inaccessible, unsupported, or intentionally excluded regions.

Do not issue a whole-crate verdict for a diff, one feature, one target, or one
unsafe block. State the narrow result actually established.

If the task is review-only, report findings and proposed remedies without
silently changing code. If the task includes authoring or fixing, update the
proof artifacts and contracts together with the implementation.

## Maintain an Obligation Ledger

Track every in-scope obligation sufficiently to detect omissions. The ledger may
be a table, issue list, annotated source, or another reviewable form. Ensure it
provides complete location-by-location coverage of producers, transitions,
consumers, and proof sites.

For each obligation, record:

- stable identifier and source location/API;
- exact proposition to prove;
- operation, contract, invariant, or postcondition that requires it;
- required applicability domain;
- supporting local facts, invariant clauses, axioms, and TCB entries, with the
  applicability of each premise;
- domain actually covered by the derivation and any case partition;
- proof location;
- reviewer verification;
- status and finding link.

Include obligations created by:

- unsafe operations and unsafe API calls;
- unsafe functions, traits, impls, fields, attributes, declarations, macros, and
  generated code as applicable;
- construction, mutation, suspension, consumption, and destruction of
  invariant-bearing state;
- safe APIs backed by unsafe code;
- every documented postcondition of each in-scope unsafe API, and every
  documented guarantee consumed by later unsafe code;
- FFI, assembly, allocators, concurrency, target/configuration selection, and
  external contracts;
- generated public APIs and code shipped downstream.

This is a discovery aid, not an exhaustive semantic taxonomy. Add whatever the
actual code and authoritative contracts require.

The ledger complements rather than replaces the proof workflow in
[proof-obligations.md](proof-obligations.md). Review surrounding safe code and
follow changed propositions to every consumer; compiler-marked unsafe locations
and textual diffs are only discovery starting points.

## Aggregate Verdicts

Use the verdict definitions in `SKILL.md` for individual obligations and the
final in-scope claim.

Report multiple statuses when applicable. For example, soundness can be
`PROVED` while documented postconditions are `CONTRACT-BROKEN`, or one path can
be `UNSOUND` while a different configuration remains `UNPROVED`. Issue `PROVED`
for the combined default claim only when every in-scope soundness and
documented-postcondition obligation is proved.

Classify a witness using the execution as a whole. A valid execution that ever
exhibits UB can establish `UNSOUND` but cannot itself establish the UB-free
existence claim required for `CONTRACT-BROKEN`. If it is the only behavioral
evidence, report that postcondition as `UNPROVED`. An independent UB-free
witness or equivalent existence proof may establish `CONTRACT-BROKEN`;
separate proofs may establish both verdicts.

Place qualifications in the theorem, not in vague prose. Use:

> PROVED for `<scope>` under `<supported-set predicate>`, relative to TCB
> `<revision>`.

For a deployment, external, or cryptographic premise, name the exact entry and
state whether the result is a conditional source, binary, or application claim.

Never use “looks sound,” “no issues found,” “probably safe,” “Miri-clean,”
“battle-tested,” or “tests pass” as a verdict.

## Write Actionable Findings

Each finding should contain:

- severity/status and affected theorem;
- exact source/API/configuration;
- required proposition;
- existing claimed proof;
- any material derivation the reviewer had to reconstruct, with citations and
  applicability, or the smallest portion still missing;
- proposed replacement proof text when the reviewed artifact omits that
  derivation;
- smallest missing, false, circular, or unsupported implication;
- authoritative contract or TCB entry involved;
- whether a valid UB witness or a separate UB-free postcondition refutation or
  equivalent existence proof is known;
- affected callers, producers, consumers, generated output, and configurations;
- minimal acceptable resolution;
- compatibility and re-audit consequences.

Distinguish:

- an implementation defect;
- insufficient or ambiguous safety documentation;
- a correct implementation with an invalid local comment;
- an undocumented TCB assumption;
- an authoritative Reference/std documentation gap;
- a skill-guidance gap;
- a compatibility/robustness defect without established UB.

A successfully reconstructed implementation proof does not erase deficient
safety documentation. Report the implementation obligation and the proof
artifact separately, and offer corrected proof text. Reconstruction may not add
a hidden caller or implementer obligation or create a provider guarantee absent
from the controlling contract.

Keep every verdict for the current artifact independent of design alternatives.
If redesign was requested, report proposals and their conditional proof plans
separately; audit an implemented redesign as a new snapshot.

If authoritative documentation is insufficient, quote the exact missing
proposition and suggest a narrowly scoped upstream report. If this skill failed
to route the reviewer to a necessary check, identify a proposed skill issue
without treating the proposed rule as current authority.

## Deliver a Complete Report

A complete audit report contains:

1. **Claim and verdict:** Exact theorem, status, scope, supported configuration
   predicate, and TCB identity.
2. **Snapshot:** Source, generated artifacts, Rust/toolchain, dependency
   resolution, and relevant build inputs.
3. **Boundary and API coverage:** Safe and unsafe surfaces crossing the owning
   module or external API boundary, including restricted-visible fields,
   constructors, safe methods, safe trait methods, macro-generated APIs, and
   language-reachable hidden items.
4. **Invariant inventory:** Index of named local contracts, owners, permitted
   transitions, and consumers—not an informal global proof.
5. **Obligation coverage:** Proof sites and status summary; link to detailed
   proofs/findings rather than duplicating them. Include material reconstructed
   proofs missing from the reviewed proof artifacts.
6. **Configuration closure:** Supported-set definition, controlling policy
   sources and conflicts, audit cutoff, authorized resolution or conservative
   superset, axes, abstract or enumerative coverage proof, generated artifacts,
   and enforced exclusions.
7. **TCB audit log:** Every authoritative or admitted proposition and reviewer
   disposition.
8. **Tool-derived evidence:** Exact theorem, artifact/model scope, bounds,
   result, non-vacuity check, and residual TCB.
9. **Postcondition/robustness scope:** Documented guarantees proved and any
   separately requested properties.
10. **Findings:** `UNPROVED`, `UNSOUND`, `CONTRACT-BROKEN`, documentation gaps,
   compatibility defects, and maintenance risks.
11. **Residual scope:** Anything not audited, inaccessible, unsupported, or
    conditional.
12. **Review triggers:** Changes that invalidate or require revisiting the
    result.

Use the bundled report and TCB templates for persistent artifacts. For an inline
review, provide the same information compactly.

## Preserve and Update the Audit

When a canonical audit or TCB log exists:

- reuse its identifiers and format;
- verify rather than blindly inherit prior `PROVED` entries;
- update changed source, contracts, configurations, dependencies, and trust;
- retain historical identity through version control rather than duplicating a
  stale snapshot;
- record the skill revision used for the audit;
- link proofs and findings to exact source revisions.

Trigger review when code or documentation changes any consumed proposition,
when supported compilation options expand, when generators or generated output
change, when dependencies or contract channels change, when authoritative Rust
documentation changes materially, or when a new incident reveals an omitted
class of obligation.

A prior successful audit is evidence about its exact snapshot and theorem, not a
permanent certification of later code.
