#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Two-tier GitHub issue metadata hygiene tool for google/zerocopy.

Tier 1 (`--fix-deterministic`) applies only sound, deterministic closure rules
derived from structured GitHub metadata:
  - Sub-crate -> primary-scope label closure (`zerocopy-derive` -> `zerocopy`,
    `exocrate` -> `anneal`).
  - Unscoped child -> single-project ancestor primary-scope propagation.
  - Legacy kind-label migration (`bug` -> Type `Bug`, `enhancement` -> Type
    `Feature`) only when unambiguous and non-conflicting.
  - Stripping PR/bot-only labels accidentally applied to Issues.
  - Clearing closed milestones lingering on open Issues.

Tier 2 (default read-only report mode, `--json` supported) surfaces diagnostics
that require human or agent judgment without mutating GitHub state.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict
import json
from pathlib import Path
import sys
from typing import Sequence

# Keep direct runs and test imports from writing `__pycache__` into the
# source tree, and make `issue_hygiene_lib` importable when this script runs
# from another directory.
sys.dont_write_bytecode = True
if str(Path(__file__).resolve().parent) not in sys.path:
    sys.path.insert(0, str(Path(__file__).resolve().parent))

# Every module-level name of the library is re-exported here, so callers and
# tests keep using `issue_hygiene.<name>`.
from issue_hygiene_lib.model import (
    Action,
    AddLabels,
    Blocker,
    COMPAT_LABELS,
    ClearMilestone,
    DEFAULT_ADVISORY_TRACKER,
    DEFAULT_GRAPHQL_TIMEOUT_SECONDS,
    DEFAULT_PTR_TRACKER,
    DEFAULT_UPSTREAM_TRACKERS,
    Diagnostic,
    ExternalIssueRef,
    HygieneReport,
    Issue,
    LEGACY_TYPE_LABELS,
    Milestone,
    PRIMARY_SCOPES,
    PR_ONLY_LABELS,
    RETRY_BACKOFF_SECONDS,
    RefState,
    RemoveLabels,
    RepoSnapshot,
    SUBCRATE_IMPLIES,
    SetIssueType,
    TITLE_TAG_IMPLIES_LABEL,
    _ADVISORY_TITLE_RE,
    _EXTERNAL_MARKER_RE,
    _FENCE_OPEN_RE,
    _GITHUB_ISSUE_URL_RE,
    _INLINE_CODE_RE,
    _ISSUE_REF_RE,
    _LEADING_TAGS_RE,
    _MAX_GRAPHQL_INT,
    _SAFE_SLUG_RE,
    _TASK_MARKER_ALT,
    _TRANSIENT_ERR_PATTERNS,
    _TRANSIENT_GQL_TYPES,
    _UNCHECKED_ITEM_RE,
    _action_kind_and_values,
    _action_to_dict,
    _extract_body_refs,
    _format_action,
    _strip_code,
)
from issue_hygiene_lib.analysis import (
    _diagnose_external_refs,
    _diagnose_issues,
    _extract_leading_tags,
    _find_single_project_ancestor,
    _has_ancestor,
    _plan_issue_actions,
    analyze_repo,
    extract_issue_external_refs,
    scan_repo_external_markers,
)
from issue_hygiene_lib.github import GitHubCli, _is_transient_graphql_failure


def format_report(report: HygieneReport, as_json: bool) -> str:
    if as_json:
        return json.dumps(
            {
                "actions": [_action_to_dict(a) for a in report.actions],
                "diagnostics": [asdict(d) for d in report.diagnostics],
            },
            indent=2,
        )
    lines = [f"=== Tier 1 Deterministic Actions ({len(report.actions)}) ==="]
    if report.actions:
        lines.extend(f"  {_format_action(a)}" for a in report.actions)
    else:
        lines.append("  (none)")

    lines.append(f"\n=== Tier 2 Diagnostics ({len(report.diagnostics)}) ===")
    if not report.diagnostics:
        lines.append("  (none)")
    by_code: dict[str, list[Diagnostic]] = {}
    for d in report.diagnostics:
        by_code.setdefault(d.code, []).append(d)
    for code in sorted(by_code):
        items = by_code[code]
        lines.append(f"  -- {code} ({len(items)}) --")
        lines.extend(f"     {d.target}: {d.message}" for d in items)
    return "\n".join(lines)


def _optional_issue_number(raw: str) -> int | None:
    value = int(raw)
    return value if value > 0 else None


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Audit and deterministically reconcile GitHub issue metadata for "
            "google/zerocopy."
        )
    )
    parser.add_argument(
        "--repo",
        default="google/zerocopy",
        help="GitHub repository in OWNER/REPO form (default: google/zerocopy).",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Local git checkout root used for source marker scans.",
    )
    parser.add_argument(
        "--check-upstream",
        action="store_true",
        help=(
            "Query upstream GitHub repos for closed external blockers in "
            "`blocked-on-rust` issues, #208, and source comments."
        ),
    )
    parser.add_argument(
        "--advisory-tracker",
        type=_optional_issue_number,
        default=DEFAULT_ADVISORY_TRACKER,
        help="Security/soundness advisory tracker issue (0 to disable).",
    )
    parser.add_argument(
        "--ptr-tracker",
        type=_optional_issue_number,
        default=DEFAULT_PTR_TRACKER,
        help="`Ptr` architecture tracker issue (0 to disable).",
    )
    parser.add_argument(
        "--fix-deterministic",
        action="store_true",
        help="Apply Tier 1 deterministic actions; never mutates Tier 2 items.",
    )
    parser.add_argument(
        "--json", action="store_true", help="Emit machine-readable JSON output."
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    if "/" not in args.repo:
        raise SystemExit(
            f"Invalid --repo value (expected OWNER/REPO): {args.repo}"
        )
    owner, repo = args.repo.split("/", 1)
    gh = GitHubCli(owner, repo)

    issues = gh.fetch_open_issues()
    issues_by_num = {i.number: i for i in issues}

    ref_nums: set[int] = set()
    for iss in issues:
        body_refs, _ = _extract_body_refs(iss.body, iss.number)
        ref_nums.update(body_refs)
    # Open issues are already known OPEN; only resolve closed/PR/other refs.
    refs = gh.fetch_refs(ref_nums - set(issues_by_num))

    ext_refs: tuple[ExternalIssueRef, ...] = ()
    ext_states: dict[tuple[str, str, int], str] = {}
    if args.check_upstream:
        ext_refs = extract_issue_external_refs(
            issues, repo_owner=owner, repo_name=repo
        ) + scan_repo_external_markers(
            args.repo_root, repo_owner=owner, repo_name=repo
        )
        ext_states = gh.fetch_external_states(ext_refs)

    snapshot = RepoSnapshot(
        issues=issues,
        refs=refs,
        external_refs=ext_refs,
        external_states=ext_states,
        advisory_tracker=args.advisory_tracker,
        ptr_tracker=args.ptr_tracker,
    )
    report = analyze_repo(snapshot)

    if args.fix_deterministic and report.actions:
        gh.apply_actions(report.actions, issues_by_num)

    print(format_report(report, as_json=args.json))
    return 0


if __name__ == "__main__":
    sys.exit(main())
