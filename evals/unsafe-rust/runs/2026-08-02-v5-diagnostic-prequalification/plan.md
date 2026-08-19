# V5 Diagnostic Prequalification Harness Plan

> **Status: DRAFT / UNSEALED.** This directory is harness source, not a frozen
> evaluation. It intentionally contains no static lock, static file manifest,
> random seeds, generated maps, event ledger, target/package identities, completed report,
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
  independent order (16 scorer agents total), two independent condition-blind
  consistency reviews per mode (16 consistency agents total), and at most one
  adjudicator per mode. The deterministic
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

The diagnostic inventory and gate manifest are executable source design inputs.
Their ID sets must be exactly equal, their dependency graph must be complete
and acyclic, every input is typed, and missing/error inputs fail closed. Gate
results preserve direct outcome, `blocked_by`, certificate outcome, and
transitive root failures. `D-DIAGNOSTIC-COMPLETION` covers all other `D-*`
gates but does not depend on or waive the two failed release blockers.

Static integration and semantic execution are separate. Before
`SNAPSHOT_BUILD`, `prepare-source-review` publishes an immutable theorem-input
and semantic candidate. Two independent oracle reviewers and one coherence
reviewer work from verified private copies and surface complete itemized work
products. Only their exact, independently authenticated receipts permit
`finalize-reviewed-inputs`. Production integration then proceeds through
`SNAPSHOT_BUILD`, `SNAPSHOT_REVIEW`, and `FINALIZE_STATIC`; execution uses
`RUNTIME_COLLECTION` and `POSTRUN_AGGREGATE`. `prepare-snapshot` derives every static payload byte,
including the complete 120 report prompts/launches and all 43 possible
evaluator prompts/runtime-instantiation contracts, then emits an immutable
framed commitment with an exactly empty `runtime/state/`. Independent reviews
use locked hook-specific artifact/procedure contracts and verified private
copies, disjoint from their source candidates, to bind that exact candidate.
Production receipts must be canonical read-only regular files. Finalization
opens each through one no-follow, nonblocking descriptor, checks its inode and
mode before and after reading, and preserves those exact captured bytes without
reopening the pathname. `finalize` copies and rechecks
the candidate without changing its payload, adds only the bound receipts and
mechanical finalization records, and writes the whole-tree manifest and lock.
It derives and rechecks the external commitment on the private stage before
publication, then fully verifies the published path and requires it to derive
that identical commitment before the commitment file can be published.
There is no one-shot production path and no receipt over merely proposed input
values. The three source and eight snapshot reviewers use one canonical actor
identity grammar, are pairwise distinct, and are permanently excluded from all
runtime semantic roles. One trusted static-verification operation authenticates
the descriptor-captured receipt bytes against the static manifest and returns
the exclusion set derived from those exact captures; runtime operations carry
that set without reopening receipt paths. Contracts and receipts bind the exact reviewer tool
set, observed Python/SSL/platform runtime, and item-by-item work product; actor
authentication and reviewer honesty remain explicit coordinator TCB premises.
Production source/package/target identities come from the separately
trusted source declaration and source trees, never candidate self-description.
The trusted verifier deterministically regenerates and byte-compares every
report prompt, input plan, and launch record. This closes the relational joins
from each scheduled target label and condition label to the exact trusted
target and selected V5/V4/no-skill package; internally consistent launch or
mount digests cannot substitute a different target or treatment. The trusted
runtime repeats this check before leasing reports and while reconstructing the
aggregate.
`evaluate-gates` accepts caller-supplied JSON only on an explicitly
unbound DRAFT path and therefore fixes `D-STATIC-INTEGRITY` to direct `FAIL`.
Only `evaluate-bound-gates` can pass it: that path authenticates a
`PRODUCTION` static lock with the trusted in-process verifier, deterministically
rederives the complete aggregate from canonical envelopes, scorer/reviewer
packets and outputs, final scores, word counts, projection audits, controls,
materiality decisions, and oracle/coherence review, then validates the exact
runtime-receipt set and its terminal content binding before evaluating the
READY gate contract.

`comparison-predicate.json` machine-freezes the descriptive comparison: every
V5 mode/atom certificate must pass in all five replicates, and for every
mode/atom the V5 five-replicate pass count must be at least the V4 and no-skill
counts. Missing/malformed data is `ERROR`; no inferential or release claim is
permitted. The deterministic aggregate builder computes this exact predicate
from all 120 joined report outcomes; no caller-provided aggregate boolean is
accepted on the bound path.

## Attempt and envelope protocol

The coordinator acquires one exclusive lease for a slot before launch. Each
started attempt uses a fresh directory. After the collaboration result returns,
the coordinator supplies the final-response bytes, complete declared output
tree, process disposition, and metadata to `protocol.py seal-attempt`.
Every production acquire and seal validates all authoritative persisted peer
leases under the operation lock: each actor must use the canonical production
identity grammar and must not be one of the eleven locked source/snapshot
reviewers. Acquire also performs this check before materializing launch inputs.

The finalizer first captures and fsyncs a complete immutable envelope, then
uses exclusive creation of one canonical pointer as a first-terminal
compare-and-swap. Format defects are recorded inside the canonical envelope
and evaluated after sealing. A later completion cannot replace the first seal.
The protocol permits no retry after a started lease; only a failure before
lease acquisition is outside the attempt count.

This is the strongest coordinator-side mechanism available here, but it does
not make the coordinator a trusted runner. `G-OUTPUT-FINALIZATION` remains
`FAIL` by construction.

## Reviewed integration material absent from the source tree

An integrated copy is valid only if integration has supplied, reviewed, and
content-addressed:

- reviewed target task modes/caps and V5/V4 invocation blocks; `integrate.py`
  recomputes `packages.json` and `targets.json` from the fixed source selection,
  including the unchanged V4 `p_predicates` source for mode P;
- review/promotion of DRAFT `atoms/{mode}.json`, `oracle/{mode}.md`,
  `allowlists/{mode}.txt`, authority propositions, and defect rules;
- fresh evaluator-custodied `seeds.json`;
- complete offline authority snapshots and provenance bindings;
- envelope specifications, reviewer packets, and coherence review;
- generated condition/target/schedule/blind/presentation maps;
- every deterministic evaluator template rendering, assignment ID, input/output
  packet schema, role execution manifest, envelope spec, and conditional-launch
  rule; and
- the final root `STATIC-MANIFEST.sha256` and `STATIC-LOCK.json`.

Hooks marked `DIRECTLY_REVALIDATED` are rerun by the trusted integration
mechanism. Hooks marked `INDEPENDENT_RECEIPT_REQUIRED` run only after the full
derived review snapshot exists; each receipt names a reviewer and review
implementation/version, binds the exact snapshot descriptor, framed payload
manifest, locked hook contract, and artifact-set digest, and records the exact
required checks and evidence bindings. The unsigned receipt still depends on
out-of-band authentication and the named reviewer's honesty; it is not a
cryptographic proof that the actor performed the work. Runtime and post-run
receipts cannot exist at prelaunch lock time and are confined to the post-lock
state tree. Evaluator
identity qualification is necessarily a runtime check over actual assignments,
not a static promise.

Do not add stand-in hashes or empty oracle files. A real run uses, in order,
`prepare-source-review`; three `review-source-subject` private copies with
`reviewer-runtime-attestation`, exact quotation/oracle/coherence procedures,
reviewer-authored itemized work products/results, and
`build-source-review-receipt` plus `validate-source-review-receipts` custody
and binding checks;
`finalize-reviewed-inputs`; `prepare-snapshot`; eight `review-subject` private
copies with reviewer-authored itemized work products/results followed by
`build-snapshot-review-receipt` and `validate-snapshot-review-receipts`; `finalize
--external-commitment-output`; and finally `verify-static
--expected-external-commitment` (which expects `PRODUCTION` by default). Both
the public Python verifier and this CLI reject uncommitted `PRODUCTION`
verification, and public review finalizers reject integration-self-test
independent-review receipts carrying `SYNTHETIC-TEST-ONLY` even if their actor
field is renamed. The synthetic test
writes only beneath an automatically removed temporary directory and can mint
only `SYNTHETIC-TEST-ONLY` static/review status. Protocol self-test runtime
validation fixtures may use the runtime receipt schema's `PASS` outcome only
inside an automatically removed temporary state tree; they are not independent
review receipts and cannot authorize either production review boundary.

## Static freeze boundary

Before any semantic agent is launched, integration validates all reviewed
inputs, preserves two independent oracle-review packets plus an independent
coherence review, generates the exact 120 READY report prompt/launch records
and 43 deterministic evaluator prompt/launch contracts, obtains
reviews of those exact bytes, and creates an injective domain-separated framed
file-and-directory manifest. `STATIC-LOCK.json` is exclusively created as the
final static byte mutation. It authenticates `bundle_kind`, snapshot and receipt
digests, path domain, file/directory modes, and the whole static tree. Only the
manifest, lock, and descendants of the exact post-lock `runtime/state/`
subtree are excluded; the `runtime/` and `runtime/state/` directory records are
themselves inventoried. No sibling child of `runtime/` is allowed, and state is
exactly empty until the lock exists. A separately custodied external commitment
is required to detect replacement of an entire internally coherent bundle.
The commitment is first derived and re-derived identically from the verified
private finalization stage. After no-replace bundle publication, full
verification and an identical commitment derivation are required before the
external file can gain authority. The commitment file itself is completely
written, fsynced, changed to `0444`, and fsynced again at a
same-directory staging path before no-replace rename and parent fsync, so the
final commitment path is either absent or complete and read-only. Recovery from
the narrow bundle-published/commitment-missing crash window requires the
explicit `recover-external-commitment` operation, a fresh external output, exact
trusted provenance revalidation, and a non-mechanical coordinator attestation
that this exact bundle has remained under uninterrupted trusted custody since
finalization. Recovery never overwrites; uncertain custody requires discarding
and recreating the bundle.

Agent workspaces are fresh external opaque directories. Rendered prompts refer
only to the fixed workspace-relative aliases `input/` and `output/`; absolute
workspace, input, and output paths occur only in coordinator launch records.
Discovery of a frozen defect invalidates that bundle; it must not be patched in
place. Runtime and post-run receipts are appended only beneath
`runtime/state/` and cannot retroactively change the static lock.
