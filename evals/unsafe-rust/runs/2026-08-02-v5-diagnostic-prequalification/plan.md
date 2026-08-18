# V5 Diagnostic Prequalification Harness Plan

> **Status: DRAFT / UNSEALED.** This directory is harness source, not a frozen
> evaluation. It intentionally contains no lock, file manifest, random seeds,
> generated maps, event ledger, target/package identities, completed report,
> score, or result. Any DRAFT atom/oracle/authority/allowlist/rule material
> under `freeze/` is unapproved integration input, not a frozen artifact.

## Claim boundary

This harness supports a rigorous diagnostic rehearsal of reusable V5
prequalification. It cannot establish candidate admission, release readiness,
terminal confirmation, or `VN` because collaboration agents share the checkout
and their final response is captured by a coordinator rather than a trusted
runner. The executable gate manifest therefore fixes `G-ISOLATION` and
`G-OUTPUT-FINALIZATION` to direct `FAIL`, and the typed inventory fixes
`release_eligibility=false` / `INELIGIBLE`. Release admission is not evaluated.
The other checks use `D-*` names so diagnostic completion cannot be mistaken
for a partial default release-root inventory.

No opaque terminal holdout is allocated or consumed. All eventual fixtures are
development/regression material and may be reused by later prequalification.

## Design

- Modes: `E`, `V`, `F`, `P`, `B`, `L`, `R`, `Q`.
- Conditions: V5 candidate, frozen V4 predecessor, and no mounted skill.
- Replicates: five fresh agents per mode/condition cell.
- Reports: 15 per mode and 120 total.
- Prompt regime: controlled for `E`, `V`, `F`, `P`, and `Q`; naturalistic for
  `B`, `L`, and `R`.
- Scoring: two blind mode-level direct-decision scorers each see all A–O in an
  independent order (16 scorer agents total), one condition-blind consistency
  review per mode, and at most one adjudicator per mode. The deterministic
  adjudication packet unions disagreements, agreed-positive hard/global flags,
  consistency challenges, and every novel potentially material finding.

`fixture_id`, `task_mode`, `prompt_regime`, `condition`, and `replicate` remain
separate typed fields. The no-skill condition has no package mount; an empty or
dummy package is forbidden. Because the checkout remains discoverable, it is
described only as a procedural no-mounted-skill comparison.

## Atom and gate semantics

Each integration-supplied atom manifest freezes a direct criterion and an
acyclic list of immediate atom prerequisites. Scorers decide only the direct
criterion. After adjudication the harness computes:

```text
blocked_by(a) = immediate prerequisites whose certificate_decision is not PASS
certificate_decision(a) = PASS
  iff direct_decision(a) is PASS and blocked_by(a) is empty
root_failures(a) = directly failed atoms in the transitive failed closure
```

An atom that fails directly and is also blocked preserves both facts. Root
failures and dependency fan-out are reported separately.

A separate machine-readable inventory freezes every common and mode-specific
hard-error rule and every global-defect rule with an exact stable ID. Each
scorer attests every closed rule for every A–O report; unknown IDs are rejected.
Novel findings remain open-ended but use scorer-scoped stable IDs and
are always routed to adjudication. Consistency must attest every atom and defect
family across all 15 labels exactly once.

The diagnostic inventory and gate manifest are executable DRAFT design inputs.
Their ID sets must be exactly equal, their dependency graph must be complete
and acyclic, every input is typed, and missing/error inputs fail closed. Gate
results preserve direct outcome, `blocked_by`, certificate outcome, and
transitive root failures. `D-DIAGNOSTIC-COMPLETION` covers all other `D-*`
gates but does not depend on or waive the two failed release blockers.

This source tree does not yet have the deterministic aggregate/context builder
needed to derive gate inputs from canonical envelopes, final mode scores,
review packets, and their content digests. Caller-supplied context values are
therefore only provisional direct diagnostics. `D-STATIC-INTEGRITY` is a
constant direct `FAIL` and is upstream of every data-dependent D-* certificate,
so favorable JSON cannot make diagnostic completion pass. The validated
`integration-hooks.json` enumerates every missing blocking implementation step.

`comparison-predicate.json` machine-freezes the descriptive comparison: every
V5 mode/atom certificate must pass in all five replicates, and for every
mode/atom the V5 five-replicate pass count must be at least the V4 and no-skill
counts. Missing/malformed data is `ERROR`; no inferential or release claim is
permitted. Its content-bound aggregate implementation is one of the blocking
hooks.

## Attempt and envelope protocol

The coordinator acquires one exclusive lease for a slot before launch. Each
started attempt uses a fresh directory. After the collaboration result returns,
the coordinator supplies the final-response bytes, complete declared output
tree, process disposition, and metadata to `protocol.py seal-attempt`.

The finalizer first captures and fsyncs a complete immutable envelope, then
uses exclusive creation of one canonical pointer as a first-terminal
compare-and-swap. Format defects are recorded inside the canonical envelope
and evaluated after sealing. A later completion cannot replace the first seal.
The DRAFT protocol permits no retry after a started lease; only a failure before
lease acquisition is outside the attempt count.

This is the strongest coordinator-side mechanism available here, but it does
not make the coordinator a trusted runner. `G-OUTPUT-FINALIZATION` remains
`FAIL` by construction.

## Deliberately absent integration material

Integration must later supply, review, and content-address:

- `packages.json` with V5 and V4 package identities and `no_skill: null`;
- `targets.json` with all target paths/digests, task modes, regimes, and caps;
- review/promotion of DRAFT `atoms/{mode}.json`, `oracle/{mode}.md`,
  `allowlists/{mode}.txt`, authority propositions, and defect rules;
- fresh evaluator-custodied `seeds.json`;
- complete offline authority snapshots and provenance bindings;
- envelope specifications, reviewer packets, and coherence review;
- generated condition/target/schedule/blind/presentation maps; and
- the final input manifest and lock.

Integration must implement every blocking hook—package/target tree and SKILL
byte recomputation, READY and cross-reference validation, oracle/allowlist and
signoff validation, treatment-render byte-delta review, READY envelope specs,
randomization verification, whole-file manifest, lock-last, and content-bound
aggregate derivation—in a new reviewed freeze. Merely changing a hook status or
supplying favorable gate-context booleans is invalid.

Do not add stand-in hashes or empty oracle files. Until all integration inputs
exist, only `verify-draft` and synthetic self-tests are valid.

## Freeze boundary

Before any semantic agent is launched, a later integration change must validate
all inputs, preserve two independent oracle-review packets with reasoning,
generate fresh sealed maps, build the full input manifest, and create a lock as
the last mutation. Discovery of a frozen defect invalidates that run; it must
not be patched in place.
