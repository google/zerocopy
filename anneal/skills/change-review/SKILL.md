---
name: change-review
description: >-
  Review the complete intended change in joshlf/anneal, either before an
  author publishes it or as a hosted reviewer. Use for code, documentation,
  configuration, and agent-instruction changes, including review fixes.
  Coordinate coverage, separate trust and general passes, verify findings,
  and re-review the final candidate. Not permission to edit, publish, or merge.
---

# Complete-change review

Find actionable defects before the next handoff, not merely enough comments
for a useful first round. Complete coverage is a review obligation, not a
claim that an agent can prove the absence of defects.

Apply [`AGENTS.md`](../../AGENTS.md), the governing project documents, and the
skills relevant to the changed artifacts. This skill owns review coordination;
[`trust-review`](../trust-review/SKILL.md) owns the adversarial trust checks,
and [`robust-code`](../robust-code/SKILL.md) owns code-comprehension checks.
Do not duplicate or weaken those contracts to obtain a clean result.

## Establish the candidate and coverage

Identify the target branch, its resolved base commit, the merge base used for
the comparison, and the candidate head or snapshot. For unpublished work,
include the intended staged, unstaged, and untracked contents. A head SHA alone
does not identify a dirty working tree. Exclude unrelated work explicitly;
do not discard it or accidentally include it in publication.

Freeze the candidate while reviewers inspect it, using an immutable commit,
separate worktree, or another stable snapshot available on the host. Inspect
the actual diff and full change inventory, not just selected hunks or a PR
summary. Include renames, deletions, modes, symlinks, hidden files, and
non-text artifacts. Read surrounding definitions, affected callers and
callees, contracts, tests, and expected companion changes where needed.

Keep a compact coverage record in working notes or the review result. For
every changed path and applicable concern, record inspected, inapplicable
with a reason, or blocked. Group paths when they share the same assessment,
but do not let grouping hide an uninspected path. This is not a requirement
for another checked-in tracking file.

## Run separate reviews

Authors must run both general review and the dedicated adversarial trust
review before publication. Use fresh-context subagents or separate reviewer
sessions when supported by the available, authorized tools. Give reviewers
the requirements, acceptance criteria, exact candidate and base, repository
instructions, and source access. Do not prime their first pass with the
author's defense, expected verdict, or another reviewer's findings. Relevant
design decisions and specifications remain necessary input.

Assign one reviewer the general pass and another the trust pass when possible.
A reviewer may run the passes sequentially when separate reviewers are not
available; the trust pass must remain a distinct activity. Reviewers inspect
without editing the candidate or publishing. Use host-enforced read-only
controls where available; prose alone does not restrict tool permissions.
Run tests only within the task's execution authority and appropriate isolation.
Do not expose private context to a new service or acquire paid capabilities
merely to satisfy this workflow.

Inspect actual capabilities rather than assuming subagents exist. When no
fresh-context reviewer is available, the author must perform the same passes
as a dedicated self-review and disclose the limitation. Do not label it
independent review or fabricate separate agents. Independence of context also
does not establish independent errors, especially with the same model.

A hosted reviewer uses these coverage and findings rules within its host's
constraints. When delegation is unavailable, run the trust pass first and
the general pass second in the same review. Review-only tasks report findings;
they do not enter the author's editing loop. Delegated reviewers return their
assigned assessment to the coordinator rather than recursively launching a
review of their own review.

## Investigate before concluding

In the general pass, trace required behavior, boundary and error cases,
cross-file contracts, state transitions, tests, and maintainability. Review
prose and instruction changes for contradictory duties, missing activation,
impossible prerequisites, authority expansion, and unsupported claims. A
documentation-only change is not automatically exempt from trust review.

In the trust pass, apply the full `trust-review` inventory and both goals
when triggered. Do not let naming or style findings displace adversarial
analysis. Preserve its distinction between a confirmed violation and an open
verification question that still blocks trust acceptance.

Continue across the remaining inventory after finding defects. For each
suspected issue, establish the affected location, violated requirement,
triggering conditions, and concrete failure mechanism. Use a focused test,
counterexample, source check, or explicit argument appropriate to the claim.
Do not demand a runnable reproducer for every sound semantic argument, and
do not turn a hypothesis into a fact when the needed check is unavailable.

Before reporting, challenge each finding against the actual candidate and
requirements. Combine duplicates of the same root cause without discarding
independent defects at the same location. Make a final omissions sweep over
the full diff, interfaces, and coverage record. Return every supported,
actionable finding permitted by the host, not an arbitrary top few. A clean
change may correctly produce no findings.

Keep findings concise enough to act on: location, violated invariant,
conditions, consequence, and evidence or remaining uncertainty. Respect the
host's severity threshold and output schema. Do not raise severity just to
bypass a reporting threshold.

## Report within the host's constraints

Always perform the required assessments. Use permitted prose, summary or
status fields, or another already authorized reporting channel for trust
assessments, coverage gaps, and unavailable checks. If none exists, omit this
narrative from the response and return only schema-supported findings. A
completed clean review may return an empty findings collection. This is a
presentation exception, not permission to skip assessment or manufacture
findings, locations, fields, or severity. It grants no additional authority
to publish comments or use another service.

If review is incomplete or a blocking trust question remains, use a supported
failure or abstention path when available. If the host provides no such path,
keep the response schema-valid, retain the incomplete assessment in working
notes, and report the limitation at the next authorized handoff. Do not call
that result approval. A findings-only response does not attest to completion;
accepting it as approval requires completion evidence tied to the reviewed
comparison, such as a supported host completion signal or an authorized
reviewer handoff. Lack of a narrative field alone does not make a completed
review incomplete.

## Authors: resolve, recheck, and repeat

Evaluate every finding; do not blindly apply a suggested fix. Repair confirmed
in-scope defects and add appropriate regression coverage. Record the evidence
for rejecting a finding, and keep unresolved disagreements or trust questions
visible. Do not weaken specifications, tests, audit checks, or merge gates to
make a review pass. An out-of-scope defect needs an explicit disposition, not
an unsupported declaration that the candidate is clean.

After fixes, run applicable deterministic checks and review the resulting
candidate again. Check for newly introduced defects, not just whether the
original comments were addressed. Reuse unaffected evidence only while its
candidate and assumptions remain valid. The final candidate must receive a
complete general and trust review after the last substantive edit, using a
fresh-context reviewer when available. An edit that changes only publication
metadata still requires checking that metadata and the unchanged tree identity.

Finish local preflight only when coverage is complete, all actionable
correctness defects in scope (including P2-equivalent defects) are resolved,
no blocking trust question remains, and required checks have passed on the
candidate they validate. Record justified inapplicability; unavailable or
failed required checks are not passes. The hosted service's narrower reporting
threshold does not narrow the author's responsibility to fix known defects.

If tools, context, or resources prevent completion, stop with an incomplete
assessment naming the remaining work. Do not loop indefinitely or change the
stopping rule to get approval. An explicitly authorized incomplete handoff may
preserve the patch or publish a draft with its gaps stated; it must not claim
readiness or waive any merge requirement.

## Bind the result to publication

Before an authorized push or PR update, verify that the candidate, comparison
base, and relevant instructions still match the reviewed state. A changed
base, conflict resolution, or further edit requires reassessing the affected
comparison and completing review for the new candidate. Never reuse an old
clean verdict solely because the branch name is unchanged.

Prepare a compact review receipt before publication: reviewed base and
candidate identity, pass coverage, reviewer capability and any self-review
fallback, findings and their disposition, checks actually run, and remaining
limits. Keep the prepared receipt in task notes until its publication
destination exists; an initial branch push does not require an existing PR.

After a push, verify that the remote head matches the reviewed candidate.
Include the prepared receipt in the initial PR description when creating the
PR, or update the existing PR's description or discussion as part of the
publication handoff. For an authorized branch-only push, include the receipt
in the task handoff instead; do not create a PR without authorization. If the
push succeeds but the PR create or update fails, report partial publication
and retain the receipt for the next authorized retry. Revalidate the candidate
and base before reusing it.

Do not publish private reasoning traces or unnecessary raw transcripts.
Distinguish completed checks, author review, independent review, and untested
expectations about effectiveness.

Local preflight never substitutes for the actual current-change Codex
approval, human approval, CI, and stack requirements in
[`docs/codex-review.md`](../../docs/codex-review.md). Preserve review history.
This procedure grants no editing, publication, spending, or merge authority.
