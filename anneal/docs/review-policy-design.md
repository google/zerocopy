<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Review Policy Design

This document records the maintainer contract for Anneal's review,
trust-boundary, and source-control instruction architecture so future revisions
preserve security boundaries, avoid cross-file drift, and test behavioral
effectiveness empirically.

## Governing constraints

Every policy file serves [`META_PRINCIPLES.md`](../META_PRINCIPLES.md),
[`PRINCIPLES.md`](../PRINCIPLES.md), and
[`THREAT_MODEL.md`](../THREAT_MODEL.md). Pre-merge review narrows defects and
prepares bounded human review of stated specifications and the TCB audit log;
it never proves defect absence or substitutes for CI or the merge gates in
[`docs/codex-review.md`](codex-review.md#merge-gates).

## Policy ownership

Every operational procedure has **one canonical owner**; except for the
self-contained `Code Review Rules` mirror shared verbatim between `AGENTS.md`
and `.gemini/styleguide.md` (governed by the parity rules and drift checks
below), peer files link to the canonical owner in at most one sentence without
repeating CLI flags, path blocklists, or multi-step checklists. This table is
the single repository-wide ownership map:

| File | Sole canonical ownership |
|---|---|
| [`AGENTS.md`](../AGENTS.md) | Repository conventions, deterministic preflight checklist, privacy rule, author routing table, and shared [Code Review Rules](../AGENTS.md#code-review-rules) |
| [`.gemini/styleguide.md`](../.gemini/styleguide.md) | Role-pure single-turn reviewer mirror of the shared Code Review Rules (zero links, zero author workflow) |
| [`skills/change-review/SKILL.md`](../skills/change-review/SKILL.md) | Reviewer coverage, isolated probes, and host-constrained reporting (Part I); evidence reuse, risk/structure sizing, delegation, holdouts, pipelining, adjudication, and receipts (Part II) |
| [`skills/trust-review/SKILL.md`](../skills/trust-review/SKILL.md) | Path-to-surface map, repo-wide filesystem/Unicode hygiene, Pass 1 untrusted/seam/spec audit, Pass 2 TCB/CI checklists, and pre-existing hazard reporting |
| [`skills/source-control/SKILL.md`](../skills/source-control/SKILL.md) | Commit sizing, bottom-up stack self-containment, commit messages, delegated-worker quarantine, PR/stack publication and readiness, and stack locking/rebasing |
| [`docs/codex-review.md`](codex-review.md) | Merge gates, live ruleset state, read-only `ci/codex_review.py` diagnostics, and re-enablement criteria |
| [`docs/review-policy-design.md`](review-policy-design.md) | Maintainer architecture contract, drift checks, non-bootstrap self-modification rule, and empirical evaluation methodology |
| [`skills/README.md`](../skills/README.md) | Provenance and short index for all vendored and repo-owned skills |

### Parity between Code Review Rules and skill hubs

Single-turn hosted reviewers cannot follow links, so `AGENTS.md` and
`.gemini/styleguide.md` carry a verbatim marker-delimited `Code Review Rules`
block. Codex's `project_doc_max_bytes` (32 KiB) is a **shared cumulative
budget** across global user instructions, root `AGENTS.md`, and nested
`AGENTS.md` files (truncating silently when exceeded); keep the repository's
cumulative `AGENTS.md` footprint under 31 KiB (enforced below by reserving at
least 1 KiB—or `GLOBAL_AGENTS_BYTES` when set—for global instructions within
the 32 KiB limit). Maintain parity using two rules:

1. Every bullet in `Code Review Rules` maps to one canonical section in
   `change-review` or `trust-review`; the skill hubs add multi-turn procedures,
   symbol lists, and rationale without widening or narrowing any trigger,
   scope, or severity. Update both in the same commit.
2. The `theory/` example list in `Code Review Rules` and `trust-review` is a
   non-exhaustive static summary anchored to
   `trusted/audit/TrustedBoundary.lean`'s allowlists (the live allowlist in
   `TrustedBoundary.lean` governs); keep those summaries synchronized with
   `TrustedBoundary.lean` and `docs/trust-model.md` whenever the allowlists
   change.

## Drift checks

Run these fail-closed checks whenever editing any file in the ownership table
(and run `python3 -B -m unittest discover -s ci -p 'test_codex_review.py'`
whenever `ci/codex_review.py`, `.github/workflows/codex-review.yml`, or
`.github/codex-review-ruleset.json` changes):

```bash
set -euo pipefail
git rev-parse --git-dir >/dev/null
k() {
  sed -n '/<!-- code-review-rules:begin -->/,/<!-- code-review-rules:end -->/p' \
    "$1"
}
fail() { echo "drift check failed: $*" >&2; exit 1; }
for f in AGENTS.md .gemini/styleguide.md; do
  c="$(k "$f" | grep -c 'code-review-rules:' || true)"
  if [ "$c" -ne 2 ]; then fail "markers: $f"; fi
done
rules="$(k AGENTS.md)"
for req in \
  '^- \*\*Untrusted input and policy stability:\*\*' \
  '^- \*\*Comparison, diff integrity, and coverage:\*\*' \
  '^- \*\*Pass order and surface scope:\*\*' \
  '^- \*\*Pass 1, filesystem hygiene, untrusted contents, and specifications:\*\*' \
  '^- \*\*Pass 2, TCB and CI \(only when triggered\):\*\*' \
  '^- \*\*General pass:\*\*' \
  '^- \*\*Execution, isolation, and probes:\*\*' \
  '^- \*\*Findings, severity, hazards, and host output:\*\*'; do
  if ! grep -Eq -- "$req" <<< "$rules"; then
    fail "missing section: $req"
  fi
done
if ! diff -u <(k AGENTS.md) <(k .gemini/styleguide.md); then
  fail 'copies differ'
fi
for tok in \
  allowedCommandKinds allowedDeclarationKinds allowedAttributeNames \
  allowedTrustedSyntaxKinds allowedTheoryTacticKinds SourceRole \
  inspectNodeKind inspectSyntax validateLocalConstant checkTierReferences \
  validateGraph validCandidateFeatures Lean.ofReduceBool Lean.trustCompiler \
  .cursorrules .windsurfrules .clinerules AGENTS.override.md \
  'lakefile.*' lean-toolchain '#[anneal::trusted]' '-- anneal-trust-tier:' \
  .cargo 'rust-toolchain*' Trusted.CrateTheorem Trusted.Crate \
  Trusted.VerificationResult foundation-lock.json root-manifest.sha256 \
  all-jobs-succeed 'persist-credentials: false' ACTIONS_RUNTIME_TOKEN; do
  if ! grep -Fq -- "$tok" <<< "$rules"; then
    fail "token missing in rules: $tok"
  fi
  if ! grep -Fq -- "$tok" skills/trust-review/SKILL.md; then
    fail "token missing in trust-review: $tok"
  fi
done
sg_body="$(tail -n +8 .gemini/styleguide.md)"
if grep -En '\]\(|\[[^]]+\]\[[^]]*\]|^\[[^]]+\]:|https?://' <<< "$sg_body"; then
  fail 'link or URL in styleguide'
fi
if grep -En '\bgh (pr|stack)\b|\bdiff[-]tree\b' <<< "$sg_body"; then
  fail 'author workflow token in styleguide'
fi
if [ "$(grep -c '^#' .gemini/styleguide.md)" -ne 1 ]; then
  fail 'unexpected heading in styleguide'
fi
global_reserve="${GLOBAL_AGENTS_BYTES:-1024}"
case "$global_reserve" in
  ''|*[!0-9]*) fail "invalid GLOBAL_AGENTS_BYTES: $global_reserve" ;;
esac
agents_bytes="$(git ls-files -z 'AGENTS.md' '*/AGENTS.md' \
  'AGENTS.override.md' '*/AGENTS.override.md' | \
  xargs -0 wc -c | tail -n 1 | awk '{print $1}')"
if [ "$((agents_bytes + global_reserve))" -ge 32768 ]; then
  fail "AGENTS.md ($agents_bytes B) + global reserve ($global_reserve B) >= 32 KiB"
fi
set +e
git grep --untracked -n 'diff[-]tree' -- '*.md' ':!skills/source-control/SKILL.md'
rc=$?
set -e
if [ "$rc" -eq 0 ]; then fail 'quarantine copy outside source-control'; fi
if [ "$rc" -ne 1 ]; then fail "git grep error: $rc"; fi
echo 'drift checks passed'
```

Also run the preflight checklist in
[`AGENTS.md`](../AGENTS.md#standing-rules) (including `./ci/check_todo.sh`,
headers, 80-column wrapping, and relative links and anchors).

## Host-constrained rendering rationale

Separating mandatory assessment from schema-constrained rendering ensures
findings-only hosts still run the full audit and emit code-anchored defects and
open trust questions inline without fabricating findings, inflating severity,
or losing Gate 1 (local review) coverage of lower-severity questions (for
example under the [Codex GitHub integration][codex-github] default P0/P1
focus; see
[`change-review`](../skills/change-review/SKILL.md#report-within-the-hosts-constraints)
and
[`docs/codex-review.md`](codex-review.md#merge-gates)).

## Non-bootstrap self-modification rule

Review every PR that modifies governing docs, review rules, agent instructions,
or security checks under the **existing base contract**, never under its own
weakened rules:

- Flag any undisclosed or unsound weakening of governing docs, review rules,
  agent instructions, or security checks (including trust-boundary checks,
  severity discipline, or merge gates) as blocking. Even a justified relaxation
  must be explained in the commit body, surfaced in the PR description's `Human
  review surface` block, judged sound by reviewers, and confirmed at Gate 5
  (human approval).
- Keep CI and human branch protections live while automated Codex ruleset
  enforcement remains disabled under
  [`docs/codex-review.md`](codex-review.md).
- Treat structural and drift checks as **design checks**, never as proof of
  reviewer behavioral effectiveness.

## Boundary design checks

When revising policy files, verify every scenario affected by the revision
against its canonical owner and required outcome:

1. **Multi-commit worker quarantine evasion (add-then-delete, shared `.git`,
   dir-prefix collision, fail-open ancestry, unlisted edits to governing docs,
   skills, or review policies):**
   [`source-control`](../skills/source-control/SKILL.md#integrate-delegated-worker-commits)
   — requires host-enforced filesystem/write isolation for untrusted workers
   (and separate clones rather than shared `.git` worktrees), fail-closed
   ancestry and SHA checks, per-commit null-delimited inspection covering
   policy, governing, and dot-prefixed paths, `EXIT`-trap cleanup, and full-tree
   prefix collision rejection.
2. **Point-in-time artifact drift (absent generators vs. deleted locks):**
   [`trust-review`](../skills/trust-review/SKILL.md#pass-2-tcb-and-ci-surfaces)
   — flags deleted or stale tracked manifests without flagging absent future
   generators.
3. **Holdout isolation and reserve partition:**
   [`change-review`](../skills/change-review/SKILL.md#delegate-review-and-holdouts)
   — separates `Sealed` vs. `Behavioral` vs. `exposed design witness`, withholds
   reserves before first repair, and blocks leaking passing premises.
4. **Repair-induced TCB violation and style oscillation:**
   [`change-review`](../skills/change-review/SKILL.md#adjudicate-findings-and-repairs)
   — rejects TCB-violating repairs and repeated style oscillation without new
   evidence; escalates refuted Codex findings without agent waiver.
5. **Stated-specification, seam, and helper-predicate tampering outside
   `trusted/`:**
   [`trust-review`](../skills/trust-review/SKILL.md#pass-1-untrusted-inputs-seams-and-specification-integrity)
   — catches weakened specs, vacuous `theory/` seams, helper predicates, and
   waivers in Pass 1 without falsely triggering Pass 2.
6. **Findings-only hosted bot (clean `[]`, anchored question, incomplete):**
   [`change-review`](../skills/change-review/SKILL.md#report-within-the-hosts-constraints)
   and
   [`docs/codex-review.md`](codex-review.md#merge-gates) — permits clean `[]`
   on completed reviews, emits anchored questions inline without severity
   inflation, forbids clean `[]` on incomplete runs, and keeps Gate 1 owning
   lower-severity questions.
7. **Single-file reviewer self-containment and role purity:**
   [`AGENTS.md`](../AGENTS.md#code-review-rules) and
   [`.gemini/styleguide.md`](../.gemini/styleguide.md) — byte-identical,
   link-free, parity-aligned with skill hubs, and read-only.
8. **Multi-PR stack pipelining, cumulative CI-push gating, coalesced repair
   batches, and locking/rebase:**
   [`change-review`](../skills/change-review/SKILL.md#schedule-by-data-dependency)
   and
   [`source-control`](../skills/source-control/SKILL.md#lock-and-rebase-a-stack)
   — evaluates the CI-executed-surface gate across cumulative `main..<head>`
   before push, overlaps non-CI draft-PR CI/hosted review with local review,
   coalesces repairs into focused commits, locks converged prefixes, and checks
   `range-diff`.
9. **Trivial edit zero-ceremony path and scoped evidence reuse:**
   [`change-review`](../skills/change-review/SKILL.md#key-every-result-to-its-inputs)
   and
   [`change-review`](../skills/change-review/SKILL.md#size-review-effort-to-risk)
   — skips Pass 2 and refinement passes on verified trivial non-policy edits
   (preserving Pass 1 hygiene) and produces a 3–5 bullet receipt.
10. **Large multi-subsystem TCB slice-sharding and pre-existing CI hazard:**
    [`change-review`](../skills/change-review/SKILL.md#delegate-review-and-holdouts)
    and
    [`trust-review`](../skills/trust-review/SKILL.md#report-findings-and-pre-existing-hazards)
    — allows one level of coordinator-owned disjoint slices with a cross-slice
    lead verifier, and requires explicit maintainer disposition for
    pre-existing hazards without public exploit payloads.
11. **Bottom-up stack self-containment and stale-base false positives:**
    [`source-control`](../skills/source-control/SKILL.md#structure-and-size-commits-for-review)
    and
    [`change-review`](../skills/change-review/SKILL.md#identify-and-cover-the-comparison)
    — keeps lower commits free of unsettled upper counts and prevents false
    positives on valid roadmap prose.
12. **Receipt verification, probe isolation, and output-validity checks:**
    [`change-review`](../skills/change-review/SKILL.md#use-executed-checks-and-isolated-probes)
    and
    [`change-review`](../skills/change-review/SKILL.md#delegate-review-and-holdouts)
    — verifies SHA-bound receipts instead of repeating cold builds, isolates
    untrusted probes in OS sandboxes after static checks, and rejects
    coverage-free or truncated outputs.

## Empirical evaluation methodology

Evaluate material policy revisions on real or synthetic PRs before trusting
them in production:

- **Controlled comparisons:** Compare the prior policy, a competent short
  exhaustive review instruction, and the revised policy on the same frozen
  changes, holding diff, host, and model family constant.
- **Independent adjudication and separation:** Use changes with independently
  adjudicated defects and embedded clean controls; **keep confirmation cases
  separate from development examples** and **preserve all assigned attempts,
  including failed and incomplete ones** (see
  [`skill-authorship`](../skills/skill-authorship/SKILL.md)).
- **Metrics and interpretation guards:** Measure true-positive catch rate and
  misses by severity on seeded Pass 1/Pass 2 and specification defects,
  precision and false-positive rate on clean controls, new defects introduced
  by fixes, coverage completeness, escalation accuracy on open trust questions,
  hosted-review rounds, end-to-end wall-clock review latency, and actual
  resource usage where observable. Fewer hosted comments alone can reflect
  misses or suppressed findings rather than better code. Do not claim token or
  cost savings from response length alone. Report model, host, instructions,
  candidate identities, and coverage limits needed to interpret the results.
- **Routing verification and graduation:** New integrations need actual routing
  checks; passing Markdown checks does not establish that a hosted reviewer
  used them. Simplify or replace this procedure when evidence supports an
  equally effective less burdensome method while retaining its coverage,
  correctness, trust, honesty, and authority obligations. Whenever a recurring
  defect class can be caught mechanically without false positives, move the
  check into CI or `anneal-audit` and retire the redundant prose.

[codex-github]: https://developers.openai.com/codex/integrations/github/
