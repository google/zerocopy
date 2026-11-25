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
from collections.abc import Callable
from dataclasses import asdict, dataclass, field
import json
from pathlib import Path
import re
import subprocess
import sys
import time
from typing import Iterable, Mapping, Sequence, Union

PRIMARY_SCOPES = frozenset({"zerocopy", "anneal", "reference", "repo"})
SUBCRATE_IMPLIES: Mapping[str, str] = {
    "zerocopy-derive": "zerocopy",
    "exocrate": "anneal",
}
TITLE_TAG_IMPLIES_LABEL: Mapping[str, str] = {
    "anneal": "anneal",
    "exocrate": "exocrate",
    "derive": "zerocopy-derive",
    "ci": "ci",
    "reference": "reference",
}
PR_ONLY_LABELS = frozenset({
    "hide-from-release-notes",
    "dependencies",
    "github_actions",
    "rust",
    "codex",
    "needs-backport",
})
LEGACY_TYPE_LABELS: Mapping[str, str] = {"bug": "Bug", "enhancement": "Feature"}
COMPAT_LABELS = ("compatibility-breaking", "compatibility-nonbreaking")

DEFAULT_ADVISORY_TRACKER = 3642
DEFAULT_PTR_TRACKER = 859
DEFAULT_UPSTREAM_TRACKERS = frozenset({208})
DEFAULT_GRAPHQL_TIMEOUT_SECONDS = 60.0
RETRY_BACKOFF_SECONDS = (2.0, 5.0)

_TRANSIENT_ERR_PATTERNS = (
    "http 500",
    "http 502",
    "http 503",
    "http 504",
    "http 429",
    "bad gateway",
    "service unavailable",
    "gateway timeout",
    "something went wrong",
    "rate limit",
    "secondary rate limit",
    "abuse detection",
    "timed out",
    "timeout",
    "connection reset",
    "connection refused",
    "temporary failure",
    "unexpected eof",
    "tls handshake",
)
_TRANSIENT_GQL_TYPES = frozenset(
    {"RATE_LIMITED", "INTERNAL", "SERVICE_UNAVAILABLE"}
)

# Constructed dynamically so `./ci/check_todo.sh` does not flag this scanner.
_TASK_MARKER_ALT = "TO" + "DO"
_EXTERNAL_MARKER_RE = re.compile(
    rf"(?:FIXME|{_TASK_MARKER_ALT})\((https://github\.com/"
    r"([A-Za-z0-9_.-]+)/([A-Za-z0-9_.-]+)/issues/(\d+))\)"
)
_GITHUB_ISSUE_URL_RE = re.compile(
    r"https://github\.com/([A-Za-z0-9_.-]+)/([A-Za-z0-9_.-]+)/issues/(\d+)"
)
_LEADING_TAGS_RE = re.compile(r"^((?:\[[^\]]+\]\s*)+)")
_UNCHECKED_ITEM_RE = re.compile(
    r"^[ \t]*[-*+][ \t]+\[ \][ \t]*(.*)$", re.MULTILINE
)
_ISSUE_REF_RE = re.compile(r"(?<![A-Za-z0-9_/&-])#(\d+)\b")
_ADVISORY_TITLE_RE = re.compile(
    r"^(?:Security|Soundness)\s+Advisory:", re.IGNORECASE
)
_FENCE_OPEN_RE = re.compile(r"^ {0,3}(`{3,}|~{3,})")
_INLINE_CODE_RE = re.compile(r"(`+)(?!`).*?(?<!`)\1(?!`)")
_SAFE_SLUG_RE = re.compile(r"\A[A-Za-z0-9_.-]+\Z")
_MAX_GRAPHQL_INT = (1 << 31) - 1


def _strip_code(text: str) -> str:
    """Strip Markdown fenced code blocks and inline code spans."""
    out: list[str] = []
    fence_char: str | None = None
    fence_len = 0
    for line in text.splitlines():
        if fence_char is None:
            match = _FENCE_OPEN_RE.match(line)
            # CommonMark section 4.5: backtick fence info strings cannot
            # contain '`', so line-leading inline triple-backtick spans stay
            # inline.
            if match and not (
                match.group(1)[0] == "`" and "`" in line[match.end() :]
            ):
                token = match.group(1)
                fence_char, fence_len = token[0], len(token)
                continue
            out.append(_INLINE_CODE_RE.sub("", line))
        else:
            stripped = line.lstrip(" ")
            indent = len(line) - len(stripped)
            trimmed = stripped.rstrip()
            if (
                indent <= 3
                and trimmed
                and set(trimmed) == {fence_char}
                and len(trimmed) >= fence_len
            ):
                fence_char, fence_len = None, 0
    return "\n".join(out)


def _extract_body_refs(
    body: str, self_num: int
) -> tuple[frozenset[int], frozenset[int]]:
    """Return `(all_body_refs, unchecked_task_refs)` excluding `self_num`."""
    prose = _strip_code(body)
    body_refs = frozenset(
        int(m.group(1))
        for m in _ISSUE_REF_RE.finditer(prose)
        if int(m.group(1)) != self_num
    )
    unchecked = frozenset(
        int(ref_m.group(1))
        for match in _UNCHECKED_ITEM_RE.finditer(prose)
        for ref_m in _ISSUE_REF_RE.finditer(match.group(1))
        if int(ref_m.group(1)) != self_num
    )
    return body_refs, unchecked


@dataclass(frozen=True)
class Milestone:
    title: str
    state: str  # "OPEN" or "CLOSED"


@dataclass(frozen=True)
class Blocker:
    ref: str
    state: str  # "OPEN" or "CLOSED"
    local_number: int | None = None


@dataclass(frozen=True)
class Issue:
    node_id: str
    number: int
    title: str
    body: str
    labels: frozenset[str]
    issue_type: str | None
    milestone: Milestone | None = None
    parent_number: int | None = None
    sub_issues: frozenset[int] = field(default_factory=frozenset)
    has_sub_issues: bool = False
    blocked_by: tuple[Blocker, ...] = ()
    relates_to: frozenset[int] = field(default_factory=frozenset)


@dataclass(frozen=True)
class RefState:
    kind: str  # "Issue" or "PullRequest"
    state: str  # "OPEN", "CLOSED", or "MERGED"


@dataclass(frozen=True)
class ExternalIssueRef:
    owner: str
    repo: str
    number: int
    target_kind: str  # "Issue" or "Source"
    target: str  # e.g. "#208" or "zerocopy/src/wrappers.rs:310"

    @property
    def key(self) -> tuple[str, str, int]:
        return (self.owner.lower(), self.repo.lower(), self.number)

    @property
    def url(self) -> str:
        return (
            f"https://github.com/{self.owner}/{self.repo}/issues/{self.number}"
        )


@dataclass(frozen=True)
class RepoSnapshot:
    issues: tuple[Issue, ...]
    refs: Mapping[int, RefState] = field(default_factory=dict)
    external_refs: tuple[ExternalIssueRef, ...] = ()
    external_states: Mapping[tuple[str, str, int], str] = field(
        default_factory=dict
    )
    advisory_tracker: int | None = DEFAULT_ADVISORY_TRACKER
    ptr_tracker: int | None = DEFAULT_PTR_TRACKER


@dataclass(frozen=True)
class AddLabels:
    number: int
    labels: tuple[str, ...]
    reason: str


@dataclass(frozen=True)
class RemoveLabels:
    number: int
    labels: tuple[str, ...]
    reason: str


@dataclass(frozen=True)
class SetIssueType:
    number: int
    issue_type: str
    reason: str


@dataclass(frozen=True)
class ClearMilestone:
    number: int
    milestone: str
    reason: str


Action = Union[AddLabels, RemoveLabels, SetIssueType, ClearMilestone]


@dataclass(frozen=True)
class Diagnostic:
    code: str
    target_kind: str  # "Issue" or "Source"
    target: str
    message: str


@dataclass(frozen=True)
class HygieneReport:
    actions: tuple[Action, ...]
    diagnostics: tuple[Diagnostic, ...]


def _action_kind_and_values(act: Action) -> tuple[str, tuple[str, ...]]:
    if isinstance(act, AddLabels):
        return ("add_labels", act.labels)
    if isinstance(act, RemoveLabels):
        return ("remove_labels", act.labels)
    if isinstance(act, SetIssueType):
        return ("set_type", (act.issue_type,))
    if isinstance(act, ClearMilestone):
        return ("clear_milestone", (act.milestone,))
    raise TypeError(f"Unsupported action type: {type(act)!r}")


def _action_to_dict(act: Action) -> dict[str, object]:
    kind, values = _action_kind_and_values(act)
    return {
        "kind": kind,
        "number": act.number,
        "values": list(values),
        "reason": act.reason,
    }


def _format_action(act: Action) -> str:
    kind, values = _action_kind_and_values(act)
    vals = ", ".join(values)
    return f"[{kind}] Issue #{act.number}: {vals} ({act.reason})"


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


def _is_transient_graphql_failure(
    stderr: str, errors: Sequence[Mapping[str, object]]
) -> bool:
    lower_err = stderr.lower()
    if any(pat in lower_err for pat in _TRANSIENT_ERR_PATTERNS):
        return True
    for err in errors:
        err_type = err.get("type")
        if isinstance(err_type, str) and err_type in _TRANSIENT_GQL_TYPES:
            return True
        msg = err.get("message")
        if isinstance(msg, str) and any(
            pat in msg.lower() for pat in _TRANSIENT_ERR_PATTERNS
        ):
            return True
    return False


class GitHubCli:
    """Thin GraphQL adapter over `gh` for read and Tier 1 write operations."""

    def __init__(
        self,
        owner: str,
        repo: str,
        *,
        timeout: float = DEFAULT_GRAPHQL_TIMEOUT_SECONDS,
        sleep_fn: Callable[[float], None] | None = None,
    ) -> None:
        if timeout <= 0:
            raise ValueError(f"timeout must be positive: {timeout}")
        self.owner = owner
        self.repo = repo
        self.timeout = timeout
        self._sleep = sleep_fn
        self._slug_lower = f"{owner}/{repo}".lower()

    def _do_sleep(self, delay: float) -> None:
        if self._sleep is not None:
            self._sleep(delay)
        else:
            time.sleep(delay)

    def graphql(
        self,
        query: str,
        variables: Mapping[str, object] | None = None,
        *,
        allow_not_found: bool = False,
    ) -> dict[str, object]:
        """Execute a GraphQL operation with timeout and transient retries.

        Retries assume idempotent operations (true for all current read
        queries and label/type/milestone mutations). Any future
        non-idempotent mutation (e.g. `addComment`) must explicitly opt out
        of retries on unknown/timed-out outcomes.
        """
        payload = json.dumps(
            {"query": query, "variables": dict(variables or {})}
        )
        attempts = len(RETRY_BACKOFF_SECONDS) + 1
        last_error: RuntimeError | None = None
        for attempt in range(attempts):
            try:
                proc = subprocess.run(
                    ["gh", "api", "graphql", "--input", "-"],
                    input=payload,
                    text=True,
                    capture_output=True,
                    check=False,
                    timeout=self.timeout,
                )
            except subprocess.TimeoutExpired as exc:
                raw_err = exc.stderr
                if isinstance(raw_err, bytes):
                    stderr = raw_err.decode("utf-8", errors="replace").strip()
                else:
                    stderr = (raw_err or "").strip()
                detail = f": {stderr}" if stderr else ""
                last_error = RuntimeError(
                    f"gh api graphql timed out after {self.timeout}s{detail}"
                )
                if attempt < len(RETRY_BACKOFF_SECONDS):
                    self._do_sleep(RETRY_BACKOFF_SECONDS[attempt])
                    continue
                raise last_error from exc

            data, retryable, err = self._parse_graphql_response(
                proc, allow_not_found=allow_not_found
            )
            if data is not None:
                return data
            last_error = err
            if retryable and attempt < len(RETRY_BACKOFF_SECONDS):
                self._do_sleep(RETRY_BACKOFF_SECONDS[attempt])
                continue
            raise last_error
        raise last_error or RuntimeError("GraphQL request failed")

    def _parse_graphql_response(
        self,
        proc: subprocess.CompletedProcess[str],
        *,
        allow_not_found: bool,
    ) -> tuple[dict[str, object] | None, bool, RuntimeError]:
        raw_out = proc.stdout.strip()
        stderr = proc.stderr.strip()
        if not raw_out:
            err = RuntimeError(
                f"gh api graphql returned empty output (exit {proc.returncode})"
                f": {stderr or 'no stderr'}"
            )
            return None, _is_transient_graphql_failure(stderr, ()), err

        try:
            parsed = json.loads(raw_out)
        except json.JSONDecodeError as exc:
            snippet = raw_out[:200] + ("..." if len(raw_out) > 200 else "")
            err = RuntimeError(
                f"gh api graphql returned invalid JSON (exit {proc.returncode})"
                f": {exc}; stderr={stderr or 'none'}; stdout={snippet!r}"
            )
            retryable = _is_transient_graphql_failure(
                f"{stderr}\n{raw_out[:500]}", ()
            )
            return None, retryable, err

        if not isinstance(parsed, dict):
            return (
                None,
                False,
                RuntimeError("gh api graphql returned non-object JSON"),
            )

        raw_errors = parsed.get("errors")
        errors: list[Mapping[str, object]] = []
        if raw_errors is not None:
            if not isinstance(raw_errors, list) or not all(
                isinstance(e, Mapping) for e in raw_errors
            ):
                return (
                    None,
                    False,
                    RuntimeError(
                        f"Malformed GraphQL `errors` field: {raw_errors!r}"
                    ),
                )
            errors = list(raw_errors)

        only_allowed_not_found = (
            allow_not_found
            and bool(errors)
            and all(e.get("type") == "NOT_FOUND" for e in errors)
        )
        top_msg = parsed.get("message")
        err_context = (
            f"{stderr}\n{top_msg}" if isinstance(top_msg, str) else stderr
        )

        if errors and not only_allowed_not_found:
            err = RuntimeError(f"GraphQL errors: {errors}")
            return (
                None,
                _is_transient_graphql_failure(err_context, errors),
                err,
            )

        data = parsed.get("data")
        if proc.returncode != 0 and not (
            allow_not_found and data is not None
        ):
            err = RuntimeError(
                f"gh api graphql exited {proc.returncode}: "
                f"{stderr or raw_out}"
            )
            return (
                None,
                _is_transient_graphql_failure(err_context, errors),
                err,
            )

        if not isinstance(data, dict):
            if allow_not_found:
                return {}, False, RuntimeError("unreachable")
            err = RuntimeError("GraphQL response missing `data` object")
            return (
                None,
                _is_transient_graphql_failure(err_context, errors),
                err,
            )

        return data, False, RuntimeError("unreachable")

    def _require_repo(self, data: Mapping[str, object]) -> dict[str, object]:
        repo_obj = data.get("repository")
        if not isinstance(repo_obj, dict):
            raise RuntimeError(f"Repository {self.owner}/{self.repo} not found")
        return repo_obj

    def _is_same_repo(self, node: Mapping[str, object]) -> bool:
        repo_obj = node.get("repository")
        if not isinstance(repo_obj, Mapping):
            return False
        nwo = repo_obj.get("nameWithOwner")
        return isinstance(nwo, str) and nwo.lower() == self._slug_lower

    def _paginate_repo_conn(
        self, field_name: str, args_str: str, node_selection: str
    ) -> list[dict[str, object]]:
        nodes: list[dict[str, object]] = []
        cursor: str | None = None
        query = (
            "query($owner: String!, $repo: String!, $after: String) {"
            "  repository(owner: $owner, name: $repo) {"
            f"    {field_name}({args_str}, after: $after) {{"
            "      pageInfo { hasNextPage endCursor }"
            f"      nodes {{ {node_selection} }}"
            "    }"
            "  }"
            "}"
        )
        while True:
            repo_obj = self._require_repo(
                self.graphql(
                    query,
                    {"owner": self.owner, "repo": self.repo, "after": cursor},
                )
            )
            conn = repo_obj.get(field_name)
            if conn is None:
                return nodes
            if not isinstance(conn, Mapping):
                raise RuntimeError(
                    f"Unexpected `{field_name}` connection payload"
                )
            raw_nodes = conn.get("nodes") or ()
            nodes.extend(n for n in raw_nodes if isinstance(n, dict))
            pi = conn.get("pageInfo")
            if not isinstance(pi, Mapping) or not pi.get("hasNextPage"):
                break
            if not pi.get("endCursor"):
                raise RuntimeError(
                    f"Missing `endCursor` while paginating `{field_name}`"
                )
            cursor = str(pi["endCursor"])
        return nodes

    def _paginate_issue_conn(
        self,
        issue_id: str,
        field_name: str,
        node_selection: str,
        initial_conn: object,
    ) -> list[dict[str, object] | None]:
        if initial_conn is None:
            return []
        if not isinstance(initial_conn, Mapping):
            raise RuntimeError(
                f"Unexpected `{field_name}` connection on {issue_id}"
            )
        raw_nodes = initial_conn.get("nodes") or ()
        nodes: list[dict[str, object] | None] = [
            n if isinstance(n, dict) else None for n in raw_nodes
        ]
        pi = initial_conn.get("pageInfo")
        if isinstance(pi, Mapping) and pi.get("hasNextPage"):
            if not pi.get("endCursor"):
                raise RuntimeError(
                    f"Missing `endCursor` on {issue_id} `{field_name}`"
                )
            cursor: str | None = str(pi["endCursor"])
        else:
            cursor = None
        while cursor is not None:
            data = self.graphql(
                "query($id: ID!, $after: String) { node(id: $id) { ... on Issue"
                f" {{ {field_name}(first: 100, after: $after) {{"
                " pageInfo { hasNextPage endCursor }"
                f" nodes {{ {node_selection} }} }} }} }} }}",
                {"id": issue_id, "after": cursor},
            )
            node_obj = data.get("node")
            if not isinstance(node_obj, Mapping):
                raise RuntimeError(
                    f"Missing node {issue_id} while paginating {field_name}"
                )
            conn = node_obj.get(field_name)
            if conn is None:
                break
            if not isinstance(conn, Mapping):
                raise RuntimeError(
                    f"Unexpected `{field_name}` page on {issue_id}"
                )
            page_nodes = conn.get("nodes") or ()
            nodes.extend(n if isinstance(n, dict) else None for n in page_nodes)
            pi = conn.get("pageInfo")
            if isinstance(pi, Mapping) and pi.get("hasNextPage"):
                if not pi.get("endCursor"):
                    raise RuntimeError(
                        f"Missing `endCursor` on {issue_id} `{field_name}`"
                    )
                cursor = str(pi["endCursor"])
            else:
                cursor = None
        return nodes

    def fetch_metadata(self) -> tuple[dict[str, str], dict[str, str]]:
        """Return paginated `(label_name -> id, issue_type_name -> id)`."""
        label_nodes = self._paginate_repo_conn(
            "labels", "first: 100", "id name"
        )
        type_nodes = self._paginate_repo_conn(
            "issueTypes", "first: 50", "id name isEnabled"
        )
        labels = {str(n["name"]): str(n["id"]) for n in label_nodes}
        types = {
            str(n["name"]): str(n["id"])
            for n in type_nodes
            if n.get("isEnabled")
        }
        return labels, types

    def fetch_open_issues(self) -> tuple[Issue, ...]:
        issue_nodes = self._paginate_repo_conn(
            "issues",
            "states: [OPEN], first: 100, "
            "orderBy: {field: CREATED_AT, direction: ASC}",
            """id number title body
            issueType { name }
            milestone { title state }
            labels(first: 30) {
              pageInfo { hasNextPage endCursor }
              nodes { name }
            }
            parent { number repository { nameWithOwner } }
            subIssues(first: 50) {
              pageInfo { hasNextPage endCursor }
              nodes { number repository { nameWithOwner } }
            }
            subIssuesSummary { total }
            blockedBy(first: 30) {
              pageInfo { hasNextPage endCursor }
              nodes { number state repository { nameWithOwner } }
            }
            relatesTo(first: 30) {
              pageInfo { hasNextPage endCursor }
              nodes { number repository { nameWithOwner } }
            }""",
        )
        issues: list[Issue] = []
        for n in issue_nodes:
            iid = str(n["id"])
            label_nodes = self._paginate_issue_conn(
                iid, "labels", "name", n.get("labels")
            )
            sub_nodes = self._paginate_issue_conn(
                iid,
                "subIssues",
                "number repository { nameWithOwner }",
                n.get("subIssues"),
            )
            blocker_nodes = self._paginate_issue_conn(
                iid,
                "blockedBy",
                "number state repository { nameWithOwner }",
                n.get("blockedBy"),
            )
            rel_nodes = self._paginate_issue_conn(
                iid,
                "relatesTo",
                "number repository { nameWithOwner }",
                n.get("relatesTo"),
            )
            parent = n.get("parent")
            parent_num = (
                int(str(parent["number"]))
                if isinstance(parent, Mapping) and self._is_same_repo(parent)
                else None
            )
            ms = n.get("milestone")
            milestone = (
                Milestone(str(ms["title"]), str(ms["state"]))
                if isinstance(ms, Mapping)
                else None
            )
            blockers: list[Blocker] = []
            for b in blocker_nodes:
                if b is None:
                    # Preserve inaccessible/private blockers as UNKNOWN so
                    # `resolved-blockers` never falsely fires.
                    blockers.append(Blocker("<inaccessible>", "UNKNOWN", None))
                    continue
                state = str(b["state"])
                if self._is_same_repo(b):
                    num = int(str(b["number"]))
                    blockers.append(Blocker(f"#{num}", state, num))
                else:
                    r = b.get("repository")
                    nwo = r["nameWithOwner"] if isinstance(r, Mapping) else "?"
                    ref = f"{nwo}#{b['number']}"
                    blockers.append(Blocker(ref, state, None))
            it = n.get("issueType")
            issue_type = str(it["name"]) if isinstance(it, Mapping) else None
            summary = n.get("subIssuesSummary")
            sub_total = (
                int(str(summary["total"]))
                if isinstance(summary, Mapping)
                else 0
            )
            if any(x is None for x in label_nodes):
                raise RuntimeError(
                    f"Unexpected null label node on issue #{n['number']}"
                )
            issues.append(
                Issue(
                    node_id=iid,
                    number=int(str(n["number"])),
                    title=str(n["title"]),
                    body=str(n.get("body") or ""),
                    labels=frozenset(
                        str(x["name"]) for x in label_nodes if x is not None
                    ),
                    issue_type=issue_type,
                    milestone=milestone,
                    parent_number=parent_num,
                    sub_issues=frozenset(
                        int(str(x["number"]))
                        for x in sub_nodes
                        if x is not None and self._is_same_repo(x)
                    ),
                    has_sub_issues=sub_total > 0,
                    blocked_by=tuple(blockers),
                    relates_to=frozenset(
                        int(str(x["number"]))
                        for x in rel_nodes
                        if x is not None and self._is_same_repo(x)
                    ),
                )
            )
        return tuple(issues)

    def fetch_refs(self, numbers: Iterable[int]) -> dict[int, RefState]:
        nums = sorted({n for n in numbers if 0 < n <= _MAX_GRAPHQL_INT})
        result: dict[int, RefState] = {}
        for idx in range(0, len(nums), 50):
            chunk = nums[idx : idx + 50]
            fields = "\n".join(
                f"r{n}: issueOrPullRequest(number: {n}) {{ __typename "
                "... on Issue { state } ... on PullRequest { state } }"
                for n in chunk
            )
            query = (
                "query($owner: String!, $repo: String!) { "
                f"repository(owner: $owner, name: $repo) {{\n{fields}\n}} }}"
            )
            data = self.graphql(
                query,
                {"owner": self.owner, "repo": self.repo},
                allow_not_found=True,
            )
            repo_data = data.get("repository")
            if not isinstance(repo_data, Mapping):
                continue
            for n in chunk:
                item = repo_data.get(f"r{n}")
                if isinstance(item, Mapping) and item.get("__typename") in (
                    "Issue",
                    "PullRequest",
                ):
                    result[n] = RefState(
                        str(item["__typename"]), str(item["state"])
                    )
        return result

    def fetch_external_states(
        self, refs: Iterable[ExternalIssueRef]
    ) -> dict[tuple[str, str, int], str]:
        unique_by_key: dict[tuple[str, str, int], tuple[str, str, int]] = {}
        for r in refs:
            if (
                _SAFE_SLUG_RE.match(r.owner)
                and _SAFE_SLUG_RE.match(r.repo)
                and 0 < r.number <= _MAX_GRAPHQL_INT
            ):
                unique_by_key.setdefault(r.key, (r.owner, r.repo, r.number))
        items = sorted(unique_by_key.items())
        states: dict[tuple[str, str, int], str] = {}
        for idx in range(0, len(items), 25):
            chunk = items[idx : idx + 25]
            var_decls: list[str] = []
            blocks: list[str] = []
            variables: dict[str, object] = {}
            for i, (_, (ow, rp, num)) in enumerate(chunk):
                var_decls.append(
                    f"$ow{i}: String!, $rp{i}: String!, $num{i}: Int!"
                )
                blocks.append(
                    f"e{i}: repository(owner: $ow{i}, name: $rp{i}) "
                    f"{{ issue(number: $num{i}) {{ state }} }}"
                )
                variables[f"ow{i}"] = ow
                variables[f"rp{i}"] = rp
                variables[f"num{i}"] = num
            query = (
                f"query({', '.join(var_decls)}) {{\n"
                + "\n".join(blocks)
                + "\n}"
            )
            data = self.graphql(query, variables, allow_not_found=True)
            for i, (key, _) in enumerate(chunk):
                repo_obj = data.get(f"e{i}")
                if isinstance(repo_obj, Mapping):
                    issue_obj = repo_obj.get("issue")
                    if isinstance(issue_obj, Mapping) and issue_obj.get(
                        "state"
                    ):
                        states[key] = str(issue_obj["state"])
        return states

    def apply_actions(
        self, actions: Sequence[Action], issues_by_num: Mapping[int, Issue]
    ) -> None:
        """Pre-validate all IDs, then apply Tier 1 mutations."""
        if not actions:
            return
        label_ids, type_ids = self.fetch_metadata()

        # Fail closed before any mutation if an issue, label, or type is absent.
        missing_issues = sorted(
            {a.number for a in actions if a.number not in issues_by_num}
        )
        missing_labels = sorted(
            {
                lbl
                for a in actions
                if isinstance(a, (AddLabels, RemoveLabels))
                for lbl in a.labels
                if lbl not in label_ids
            }
        )
        missing_types = sorted(
            {
                a.issue_type
                for a in actions
                if isinstance(a, SetIssueType) and a.issue_type not in type_ids
            }
        )
        problems: list[str] = []
        if missing_issues:
            problems.append(f"unknown issues: {missing_issues}")
        if missing_labels:
            problems.append(f"unknown labels on repo: {missing_labels}")
        if missing_types:
            problems.append(f"unknown issue types on repo: {missing_types}")
        if problems:
            raise RuntimeError(
                "Aborting before any mutation (" + "; ".join(problems) + ")"
            )

        total = len(actions)
        for idx, act in enumerate(actions, start=1):
            iss = issues_by_num[act.number]
            try:
                if isinstance(act, (AddLabels, RemoveLabels)):
                    mut = (
                        "addLabelsToLabelable"
                        if isinstance(act, AddLabels)
                        else "removeLabelsFromLabelable"
                    )
                    self.graphql(
                        f"mutation($id: ID!, $lids: [ID!]!) {{ {mut}"
                        "(input: {labelableId: $id, labelIds: $lids})"
                        " { clientMutationId } }",
                        {
                            "id": iss.node_id,
                            "lids": [label_ids[l] for l in act.labels],
                        },
                    )
                elif isinstance(act, SetIssueType):
                    self.graphql(
                        "mutation($id: ID!, $tid: ID!) { updateIssueIssueType"
                        "(input: {issueId: $id, issueTypeId: $tid})"
                        " { issue { number } } }",
                        {"id": iss.node_id, "tid": type_ids[act.issue_type]},
                    )
                elif isinstance(act, ClearMilestone):
                    self.graphql(
                        "mutation($id: ID!) { updateIssue"
                        "(input: {id: $id, milestoneId: null})"
                        " { issue { number } } }",
                        {"id": iss.node_id},
                    )
                else:
                    raise TypeError(f"Unsupported action: {type(act)!r}")
            except Exception as exc:
                raise RuntimeError(
                    f"Applied {idx - 1}/{total} actions before failure on "
                    f"{_format_action(act)}: {exc}"
                ) from exc
            print(
                f"[applied {idx}/{total}] {_format_action(act)}",
                file=sys.stderr,
            )


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
