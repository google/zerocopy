<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Complete-change review: maintainer contract

## Goal and preservation boundary

The review policy aims to find valid defects before publication and reduce
avoidable author-reviewer rounds. It requires local author preflight and asks
hosted reviewers to exhaust the relevant change inventory before concluding,
not to produce a particular number of comments. It applies to source,
documentation, configuration, and agent-facing instructions.

Preserve the governing project principles, the dedicated adversarial trust
review, evidence-based findings, and the existing Codex, human, CI, and stack
merge requirements. Neither a review receipt nor a passing local check is a
security guarantee or proof that no defect remains. Do not turn this process
into a substitute for the bounded human review and uncompromised execution
environment required by `THREAT_MODEL.md`.

## Responsibilities and representation

`AGENTS.md` carries a concise entry contract, including `Code Review Rules`
for hosted review. `change-review` owns candidate identity, coverage, reviewer
coordination, finding validation, and the author-side fix loop. `trust-review`
retains the domain-specific adversarial checks. `source-control` applies the
publication boundary, while `.gemini/styleguide.md` routes that integration
to the same rules. `CLAUDE.md` already imports `AGENTS.md`; the skill registry
already points at `skills/`. Vendored general-purpose skills stay unchanged.

Keep three questions distinct: what was inspected, what defects the evidence
supports, and whether publication or merge is authorized. A zero-finding
result may still be incomplete. A completed local review may still lack
independent corroboration or hosted approval. A fix changes the candidate and
can invalidate a prior result. Recording these distinctions avoids both stale
approval and an endless demand for a guarantee the review cannot establish.

Fresh-context reviewers are required when the authorized tools support them.
They receive the task contract and source, not a desired verdict. A separate
trust pass protects attention for cross-cutting failures. Where delegation is
unavailable, a disclosed self-review fallback preserves the local obligation
without pretending to provide independent evidence. Findings are checked
against the candidate rather than counted as votes.

A compact coverage record is sufficient; no new machine-readable attestation,
external service, CI permission, or committed per-review ledger is required.
These instructions are behavioral requirements, not tamper-proof enforcement.
An unreviewed change to them cannot authorize bypassing existing trust or merge
requirements. Review policy changes themselves need review under the existing
governing contract.

Review and receipt preparation precede a push; receipt posting follows once
the destination exists. This preserves the initial stacked-PR sequence of
push, create with a prepared body, and link. Branch-only publication uses the
task handoff rather than requiring an unauthorized PR. A failed PR write does
not undo a successful push: report the partial result, retain the receipt,
and revalidate its candidate and base before retrying.

## Host limits and evidence

The [official Codex GitHub integration documentation][codex-github] describes
repository `AGENTS.md` review rules and directory-specific scope. Keep the
load-bearing hosted instructions in the root file rather than assuming every
host follows links or supports skill loading, subagents, hooks, or arbitrary
output sections. Recheck host behavior before adding provider-specific
controls. Repository instructions do not override the service's severity,
output, or resource limits.

A required assessment and its rendered narrative are separate obligations.
When no schema field or already authorized channel can carry the narrative,
the reviewer may omit it, but must still perform the assessment. A completed
clean review may return an empty findings collection. Incomplete review stays
non-approving: use a supported failure path when available, otherwise preserve
its limits for the next authorized handoff. A findings-only response is not
completion evidence; the maintainer needs that evidence separately before
accepting it as approval. This fallback does not authorize invented findings,
extra output fields, or new publication channels.

The local preflight deliberately covers actionable correctness defects beyond
a hosted review's reporting threshold. Do not inflate severity, weaken checks,
or optimize for an approval reaction. False positives, correlated misses, and
bad fixes remain possible. The procedure's effectiveness is a hypothesis to
evaluate, not an observed consequence of committing these files.

## Maintenance checks and behavioral evaluation

For a policy revision, inspect routing, relative links, preserved trust and
merge rules, and the final diff. Check the following boundary cases against
the instructions; these are design checks, not behavioral evidence:

- Early findings must not hide a later changed or hidden file, an untracked
  addition, or a missing companion update. A genuinely clean change may
  correctly yield no findings.
- A fix, changed base, dirty edit, or conflict resolution must invalidate
  affected review evidence. The final candidate needs complete review.
- A plausible but unverified issue must not become a confirmed defect by
  repetition. A blocked trust question must not disappear during deduplication.
- An unavailable reviewer must lead to an honest capability disclosure, not
  invented independence. Missing required checks or coverage remain incomplete.
- Hosted output restrictions must not cause fabricated code locations,
  inflated severity, or false approval. Review-only helpers must not edit,
  publish, or recursively impose another author-preflight loop on themselves.
- A completed clean trust-sensitive review on a findings-only host with no
  summary, status field, or authorized side channel must permit empty findings
  without a narrative assessment. The same empty output from an incomplete
  review must not establish completion or approval. Check both cases without
  inventing fields or findings, and preserve the reporting limits.
- Initial single-branch and stacked-PR publication must allow a prepared
  receipt before push and include it in the PR body at creation. Branch-only
  publication must deliver it in the task handoff. A failed PR create or
  update must preserve the receipt and report the already-published branch
  without claiming the PR write succeeded.
- A clean local review must not authorize publication or bypass Codex approval,
  human approval, CI, stack ordering, or the governing trust model.

To test effectiveness, compare the prior policy, a competent short exhaustive
review instruction, and the delegated preflight on the same frozen changes.
Use changes with independently adjudicated defects and clean controls; keep
confirmation cases separate from development examples. Preserve all assigned
attempts, including failed and incomplete ones. Measure valid defects and
misses by severity, precision, new defects introduced by fixes, hosted-review
rounds, latency, and actual resource usage where observable. Fewer hosted
comments alone can reflect misses or suppressed findings rather than better
code. Report model, host, instructions, candidate identities, and coverage
limits needed to interpret the results. Do not claim token or cost savings
from response length alone.

Simplify or replace this procedure when evidence supports an equally effective
less burdensome method, but retain its coverage, correctness, trust, honesty,
and authority obligations. New integrations need actual routing checks;
passing Markdown checks does not establish that a hosted reviewer used them.

[codex-github]: https://developers.openai.com/codex/integrations/github/
