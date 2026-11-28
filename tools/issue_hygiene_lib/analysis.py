# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Tier 1 action planning, Tier 2 diagnostics, and external-reference
extraction for `issue_hygiene`."""

from __future__ import annotations

from pathlib import Path
import re
import subprocess
from typing import Iterable, Mapping, Sequence

from .model import (
    Action,
    AddLabels,
    COMPAT_LABELS,
    ClearMilestone,
    DEFAULT_UPSTREAM_TRACKERS,
    Diagnostic,
    ExternalIssueRef,
    HygieneReport,
    Issue,
    LEGACY_TYPE_LABELS,
    PRIMARY_SCOPES,
    PR_ONLY_LABELS,
    RefState,
    RemoveLabels,
    RepoSnapshot,
    SUBCRATE_IMPLIES,
    SetIssueType,
    TITLE_TAG_IMPLIES_LABEL,
    _ADVISORY_TITLE_RE,
    _EXTERNAL_MARKER_RE,
    _GITHUB_ISSUE_URL_RE,
    _LEADING_TAGS_RE,
    _TASK_MARKER_ALT,
    _extract_body_refs,
    _strip_code,
)


def _extract_leading_tags(title: str) -> tuple[str, ...]:
    match = _LEADING_TAGS_RE.match(title)
    if not match:
        return ()
    return tuple(
        t.strip().lower() for t in re.findall(r"\[([^\]]+)\]", match.group(1))
    )


def _find_single_project_ancestor(
    issue_num: int,
    issues_by_num: Mapping[int, Issue],
    effective_labels: Mapping[int, set[str]],
) -> tuple[int, str] | None:
    """Return `(ancestor_num, primary_scope)` if nearest scoped ancestor has 1.

    Multi-project ancestors (e.g. `[zerocopy, anneal]`) return `None`, and
    sub-crate labels are never auto-inherited.
    """
    visited = {issue_num}
    cur = issues_by_num[issue_num].parent_number
    while cur is not None and cur not in visited:
        visited.add(cur)
        if cur not in issues_by_num:
            return None
        primaries = effective_labels[cur] & PRIMARY_SCOPES
        if primaries:
            return (cur, next(iter(primaries))) if len(primaries) == 1 else None
        cur = issues_by_num[cur].parent_number
    return None


def _has_ancestor(
    issue_num: int, target: int, issues_by_num: Mapping[int, Issue]
) -> bool:
    """Return True if `target` appears in `issue_num`'s parent chain."""
    visited = {issue_num}
    cur = issues_by_num[issue_num].parent_number
    while cur is not None and cur not in visited:
        if cur == target:
            return True
        visited.add(cur)
        if cur not in issues_by_num:
            return False
        cur = issues_by_num[cur].parent_number
    return False


def _plan_issue_actions(
    sorted_issues: Sequence[Issue], issues_by_num: Mapping[int, Issue]
) -> tuple[
    list[Action],
    list[Diagnostic],
    dict[int, set[str]],
    dict[int, str | None],
]:
    actions: list[Action] = []
    diagnostics: list[Diagnostic] = []
    eff_labels = {i.number: set(i.labels) for i in sorted_issues}
    eff_type = {i.number: i.issue_type for i in sorted_issues}

    # Tier 1a: per-issue local deterministic rules.
    for iss in sorted_issues:
        cur = eff_labels[iss.number]
        implied = sorted(
            {
                umbrella
                for sub, umbrella in SUBCRATE_IMPLIES.items()
                if sub in cur and umbrella not in cur
            }
        )
        if implied:
            cur.update(implied)
            actions.append(
                AddLabels(
                    iss.number,
                    tuple(implied),
                    "sub-crate implies primary scope umbrella",
                )
            )

        pr_only = sorted(cur & PR_ONLY_LABELS)
        if pr_only:
            cur.difference_update(pr_only)
            actions.append(
                RemoveLabels(
                    iss.number,
                    tuple(pr_only),
                    "PR/bot-only label is forbidden on Issues",
                )
            )

        legacy = sorted(lbl for lbl in LEGACY_TYPE_LABELS if lbl in cur)
        if len(legacy) == 1:
            lbl = legacy[0]
            target_type = LEGACY_TYPE_LABELS[lbl]
            current_type = eff_type[iss.number]
            if current_type is None:
                eff_type[iss.number] = target_type
                cur.discard(lbl)
                # Set native Type before removing legacy label so a mid-run
                # failure cannot lose classification.
                actions.append(
                    SetIssueType(
                        iss.number,
                        target_type,
                        f"migrate legacy `{lbl}` label to Issue Type",
                    )
                )
                actions.append(
                    RemoveLabels(
                        iss.number,
                        (lbl,),
                        f"migrated to Issue Type `{target_type}`",
                    )
                )
            elif current_type == target_type:
                cur.discard(lbl)
                actions.append(
                    RemoveLabels(
                        iss.number,
                        (lbl,),
                        f"superseded by matching Issue Type `{target_type}`",
                    )
                )
            else:
                diagnostics.append(
                    Diagnostic(
                        "conflicting-legacy-type",
                        "Issue",
                        f"#{iss.number}",
                        f"legacy label `{lbl}` conflicts with Issue Type "
                        f"`{current_type}`",
                    )
                )
        elif len(legacy) > 1:
            diagnostics.append(
                Diagnostic(
                    "conflicting-legacy-type",
                    "Issue",
                    f"#{iss.number}",
                    f"carries conflicting legacy type labels {legacy}",
                )
            )

        if iss.milestone is not None and iss.milestone.state == "CLOSED":
            actions.append(
                ClearMilestone(
                    iss.number,
                    iss.milestone.title,
                    "open issue references a closed milestone",
                )
            )

    # Tier 1b: single-pass ancestor primary-scope propagation. Walking to the
    # nearest scoped ancestor already reaches fixed point in one pass.
    snapshot_labels = {n: set(ls) for n, ls in eff_labels.items()}
    for iss in sorted_issues:
        cur = eff_labels[iss.number]
        if cur & PRIMARY_SCOPES:
            continue
        anc = _find_single_project_ancestor(
            iss.number, issues_by_num, snapshot_labels
        )
        if anc is not None:
            anc_num, scope = anc
            cur.add(scope)
            actions.append(
                AddLabels(
                    iss.number,
                    (scope,),
                    f"inherits single-project scope from #{anc_num}",
                )
            )

    return actions, diagnostics, eff_labels, eff_type


def _diagnose_issues(
    sorted_issues: Sequence[Issue],
    issues_by_num: Mapping[int, Issue],
    eff_labels: Mapping[int, set[str]],
    eff_type: Mapping[int, str | None],
    ref_lookup: Mapping[int, RefState],
    advisory_tracker: int | None,
    ptr_tracker: int | None,
) -> list[Diagnostic]:
    diagnostics: list[Diagnostic] = []

    def add(code: str, target: str, message: str) -> None:
        diagnostics.append(Diagnostic(code, "Issue", target, message))

    tracker = (
        issues_by_num.get(advisory_tracker)
        if advisory_tracker is not None
        else None
    )
    tracker_links: frozenset[int] = (
        tracker.sub_issues
        | tracker.relates_to
        | frozenset(
            b.local_number
            for b in tracker.blocked_by
            if b.local_number is not None
        )
        if tracker is not None
        else frozenset()
    )

    for iss in sorted_issues:
        cur = eff_labels[iss.number]
        target = f"#{iss.number}"

        if eff_type[iss.number] is None:
            add(
                "missing-type",
                target,
                f"missing native Issue Type: {iss.title}",
            )
        if not (cur & PRIMARY_SCOPES):
            add(
                "missing-primary-scope",
                target,
                f"missing Primary Scope label: {iss.title}",
            )

        if (
            not iss.has_sub_issues
            and not iss.sub_issues
            and COMPAT_LABELS[0] in cur
            and COMPAT_LABELS[1] in cur
        ):
            add(
                "conflicting-compatibility",
                target,
                "leaf issue carries both `compatibility-breaking` and "
                "`compatibility-nonbreaking`",
            )

        tags = _extract_leading_tags(iss.title)
        for tag, req_label in TITLE_TAG_IMPLIES_LABEL.items():
            if tag in tags and req_label not in cur:
                add(
                    "title-label-mismatch",
                    target,
                    f"title carries `[{tag}]` without `{req_label}` label",
                )
        if (
            ("ptr" in tags or "pointer" in tags)
            and ptr_tracker is not None
            and iss.number != ptr_tracker
            and not _has_ancestor(iss.number, ptr_tracker, issues_by_num)
        ):
            add(
                "title-label-mismatch",
                target,
                f"title carries `[ptr]`/`[pointer]` but is not under "
                f"#{ptr_tracker}",
            )

        body_refs, unchecked_refs = _extract_body_refs(iss.body, iss.number)
        for ref_num in sorted(unchecked_refs):
            rs = ref_lookup.get(ref_num)
            if rs and rs.state in ("CLOSED", "MERGED"):
                add(
                    "stale-checklist-ref",
                    target,
                    f"unchecked checklist item references {rs.state} "
                    f"{rs.kind} #{ref_num}",
                )

        for ref_num in sorted(body_refs):
            rs = ref_lookup.get(ref_num)
            if rs and rs.kind == "PullRequest" and rs.state == "CLOSED":
                add(
                    "closed-unmerged-pr-ref",
                    target,
                    f"body references closed unmerged PR #{ref_num}",
                )

        local_blockers = frozenset(
            b.local_number
            for b in iss.blocked_by
            if b.local_number is not None
        )
        if iss.has_sub_issues or iss.sub_issues or len(unchecked_refs) >= 2:
            linked = iss.sub_issues | local_blockers | iss.relates_to
            for ref_num in sorted(unchecked_refs - linked):
                rs = ref_lookup.get(ref_num)
                if rs and rs.kind == "Issue" and rs.state == "OPEN":
                    add(
                        "unlinked-tasklist-ref",
                        target,
                        f"unchecked checklist item #{ref_num} is OPEN but not "
                        "linked via subIssues/blockedBy/relatesTo",
                    )

        if iss.blocked_by and all(b.state == "CLOSED" for b in iss.blocked_by):
            refs_str = ", ".join(sorted(b.ref for b in iss.blocked_by))
            add(
                "resolved-blockers",
                target,
                f"all blockedBy targets ({refs_str}) are CLOSED",
            )

        if (
            advisory_tracker is not None
            and iss.number != advisory_tracker
            and _ADVISORY_TITLE_RE.match(iss.title)
        ):
            linked_to_tracker = (
                iss.number in tracker_links
                or iss.parent_number == advisory_tracker
                or advisory_tracker in iss.relates_to
                or advisory_tracker in local_blockers
            )
            if not linked_to_tracker:
                add(
                    "unlinked-advisory",
                    target,
                    f"advisory is not linked to tracker #{advisory_tracker} "
                    "via subIssues/blockedBy/relatesTo",
                )

    return diagnostics


def _diagnose_external_refs(
    external_refs: Sequence[ExternalIssueRef],
    external_states: Mapping[tuple[str, str, int], str],
) -> list[Diagnostic]:
    diagnostics: list[Diagnostic] = []
    seen: set[tuple[str, str, tuple[str, str, int]]] = set()
    for ext in external_refs:
        dedup_key = (ext.target_kind, ext.target, ext.key)
        if external_states.get(ext.key) == "CLOSED" and dedup_key not in seen:
            seen.add(dedup_key)
            diagnostics.append(
                Diagnostic(
                    "closed-upstream-blocker",
                    ext.target_kind,
                    ext.target,
                    f"upstream issue {ext.url} is CLOSED",
                )
            )
    return diagnostics


def analyze_repo(snapshot: RepoSnapshot) -> HygieneReport:
    """Compute Tier 1 deterministic actions and Tier 2 diagnostics."""
    sorted_issues = tuple(sorted(snapshot.issues, key=lambda i: i.number))
    issues_by_num = {i.number: i for i in sorted_issues}
    ref_lookup = {
        i.number: RefState("Issue", "OPEN") for i in sorted_issues
    } | dict(snapshot.refs)

    actions, diagnostics, eff_labels, eff_type = _plan_issue_actions(
        sorted_issues, issues_by_num
    )
    diagnostics.extend(
        _diagnose_issues(
            sorted_issues,
            issues_by_num,
            eff_labels,
            eff_type,
            ref_lookup,
            snapshot.advisory_tracker,
            snapshot.ptr_tracker,
        )
    )
    diagnostics.extend(
        _diagnose_external_refs(
            snapshot.external_refs, snapshot.external_states
        )
    )
    return HygieneReport(tuple(actions), tuple(diagnostics))


def scan_repo_external_markers(
    repo_root: Path, *, repo_owner: str = "google", repo_name: str = "zerocopy"
) -> tuple[ExternalIssueRef, ...]:
    """Scan tracked text files outside `vendor/` for external issue URLs."""
    proc = subprocess.run(
        [
            "git",
            "-C",
            str(repo_root),
            "grep",
            "-I",
            "-n",
            "-E",
            rf"(FIXME|{_TASK_MARKER_ALT})\(https://github\.com/",
            "--",
            ":(glob,exclude)**/vendor/**",
        ],
        text=True,
        capture_output=True,
        check=False,
    )
    if proc.returncode not in (0, 1):
        raise RuntimeError(f"git grep failed: {proc.stderr.strip()}")
    self_slug = (repo_owner.lower(), repo_name.lower())
    refs: list[ExternalIssueRef] = []
    for line in proc.stdout.splitlines():
        parts = line.split(":", 2)
        if len(parts) < 3:
            continue
        path, lineno, content = parts
        for match in _EXTERNAL_MARKER_RE.finditer(content):
            owner, repo = match.group(2), match.group(3)
            if (owner.lower(), repo.lower()) == self_slug:
                continue
            refs.append(
                ExternalIssueRef(
                    owner,
                    repo,
                    int(match.group(4)),
                    "Source",
                    f"{path}:{lineno}",
                )
            )
    return tuple(refs)


def extract_issue_external_refs(
    issues: Iterable[Issue],
    *,
    repo_owner: str = "google",
    repo_name: str = "zerocopy",
    tracker_issues: frozenset[int] = DEFAULT_UPSTREAM_TRACKERS,
) -> tuple[ExternalIssueRef, ...]:
    """Collect upstream issue URLs from `blocked-on-rust` & tracker issues."""
    self_slug = (repo_owner.lower(), repo_name.lower())
    refs: list[ExternalIssueRef] = []
    for iss in issues:
        if (
            "blocked-on-rust" not in iss.labels
            and iss.number not in tracker_issues
        ):
            continue
        for match in _GITHUB_ISSUE_URL_RE.finditer(_strip_code(iss.body)):
            owner, repo = match.group(1), match.group(2)
            if (owner.lower(), repo.lower()) == self_slug:
                continue
            refs.append(
                ExternalIssueRef(
                    owner, repo, int(match.group(3)), "Issue", f"#{iss.number}"
                )
            )
    return tuple(refs)
