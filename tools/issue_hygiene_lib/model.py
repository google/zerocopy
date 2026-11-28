# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Constants, issue and action records, and their formatting for
`issue_hygiene`."""

from __future__ import annotations

from dataclasses import dataclass, field
import re
from typing import Mapping, Union


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
