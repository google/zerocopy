# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Evaluate Gate 2 cross-family reviews, legacy Codex summaries, and propose commit statuses.

The deployed workflow runs this standard-library adapter only as manually
dispatched, read-only diagnostics. The former publisher and deletion recorder
remain available for the research tracked in issue #4013. Neither write mode
runs in that workflow. PR code and comment contents are never executed.
The default mode reads live inputs and prints proposed statuses. Explicit
--publish and --record-deletion retain the former gate's two write effects.
"""

import argparse
from collections import defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
import io
import os
import re
import sys
from urllib.error import HTTPError
from urllib.request import Request, urlopen


CONTEXT = "Codex review"
# The gate uses the standard Actions token. Repository writers and ordinary
# review of workflow changes are trusted; no separate publisher is provisioned.
PUBLISHER_LOGIN = "github-actions[bot]"
# Pin the account ID as well as its display name. A copied marker or a similarly
# named account must not acquire authority to approve a revision.
BOT_ID = 199175422
BOT_LOGIN = "chatgpt-codex-connector[bot]"
SUMMARY = "<!-- codex-pull-request-review-summary"
STATE = "<!-- codex-review-state:"
GATE2_MARKER = "<!-- anneal-gate2-review:"
GATE2_AUTHORIZED_ASSOCIATIONS = frozenset({"OWNER", "MEMBER", "COLLABORATOR"})
SHA1_RE = re.compile(r"[0-9a-f]{40}")
SHA256_RE = re.compile(r"[0-9a-f]{64}")
ONE_IDENTITY_RE = re.compile(r"^one:([0-9a-f]{40}):([0-9a-f]{40}):([0-9a-f]{64})$")
MULTI_IDENTITY_RE = re.compile(r"^multi:([0-9a-f]{40}):([0-9a-f]{40})$")
FAMILY_RE = re.compile(r"[a-z0-9][a-z0-9._-]{0,63}")
DISALLOWED_FAMILIES = frozenset({
    "unknown", "none", "null", "n/a", "na", "unspecified", "self", "same", "auto",
})
CANONICAL_FAMILY_PREFIXES = (
    ("claude", ("claude", "anthropic")),
    ("gemini", ("gemini", "google-gemini")),
    ("openai", ("openai", "gpt", "codex", "chatgpt", "o1", "o3", "o4")),
)
GATE2_VERDICTS = frozenset({"clean", "findings", "incomplete"})
GATE2_SEVERITIES = frozenset({"P0", "P1", "P2", "P3"})
GATE2_REQUIRED_KEYS = frozenset({
    "base_sha", "head_sha", "tree_sha",
    "reviewer_family", "author_family",
    "verdict", "findings",
})
GATE2_OPTIONAL_KEYS = frozenset({
    "parent_tree", "commit_msg_sha256", "reviewed_at",
    "round", "risk_tier", "merge_base", "identity_key",
    "panel_seats", "prior_findings_status", "coverage",
    "advisories",
})
GATE2_FINDING_KEYS = frozenset({
    "severity", "summary", "path", "line", "id",
    "fingerprint", "surface", "consensus_count", "raised_by", "repro_status",
})
GATE2_PANEL_SEAT_KEYS = frozenset({
    "seat", "family", "model_label", "role",
    "status", "verdict", "findings_count", "latency_sec",
})
# Deletions remove evidence from the comments API. Record each deletion as an
# immutable, uniquely named commit status on Anneal's initial commit. This
# stable anchor survives branch moves without needing a database, a new ref,
# contents-write permission, or a stored copy of the deleted prose.
STATE_ANCHOR = "8950b5afa6444859c21fb4d100e21dd283afb6d6"
DELETION_CONTEXT = "Codex summary deletion/"


@dataclass(frozen=True)
class Result:
    """A native commit-status state and the reason shown beside it."""

    state: str
    reason: str


def unique_object(pairs):
    """Reject ambiguous JSON rather than accepting the last duplicate key."""
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def authentic_summary(comment):
    """Authenticate the comment author, independently of the event sender."""
    user = comment.get("user") or {}
    return (user.get("id") == BOT_ID and user.get("login") == BOT_LOGIN
            and user.get("type") == "Bot"
            and SUMMARY in (comment.get("body") or ""))


def authentic_gate2_item(item, authorized_reviewers=None):
    """Authenticate a structured Gate 2 review or comment."""
    user = item.get("user") or {}
    login = user.get("login")
    user_id = user.get("id")
    if (not isinstance(login, str) or not login
            or not isinstance(user_id, int) or isinstance(user_id, bool)
            or GATE2_MARKER not in (item.get("body") or "")):
        return False
    if authorized_reviewers is not None:
        allowed = {entry.casefold() if isinstance(entry, str) else entry
                   for entry in authorized_reviewers}
        return login.casefold() in allowed or (user_id, login) in allowed
    return item.get("author_association") in GATE2_AUTHORIZED_ASSOCIATIONS


def latest_summary(comments):
    """Use the same authoritative comment for policy and freshness checks."""
    return max((c for c in comments if authentic_summary(c)),
               key=lambda c: c["id"], default=None)


def summary_snapshot(comments):
    """Compare legacy Codex summary inputs, ignoring unrelated comments."""
    latest = latest_summary(comments)
    return ((latest["id"], latest.get("created_at"), latest["body"])
            if latest is not None else None)


def codex_findings_snapshot(comments):
    """Snapshot all authentic Codex summaries carrying completed findings."""
    items = []
    for comment in comments:
        if not authentic_summary(comment):
            continue
        try:
            review = _parse_codex_summary(comment.get("body") or "")
        except ValueError:
            continue
        if _codex_summary_has_completed_findings(review):
            items.append((comment.get("id"), comment.get("created_at"), comment["body"]))
    items.sort(key=lambda row: (
        0 if isinstance(row[0], int) and not isinstance(row[0], bool) else 1,
        row[0] if isinstance(row[0], int) and not isinstance(row[0], bool) else str(row[0]),
    ))
    return tuple(items)


def review_snapshot(comments, reviews=(), authorized_reviewers=None):
    """Compare Gate 2 and legacy Codex decision inputs during reconciliation."""
    gate2_items = []
    for source, entries in (("comment", comments), ("review", reviews)):
        for item in entries:
            if authentic_gate2_item(item, authorized_reviewers):
                ts_key = "submitted_at" if source == "review" else "created_at"
                gate2_items.append((
                    source, item.get("id"), item.get(ts_key),
                    item.get("state"), item.get("commit_id"), item.get("body"),
                ))
    gate2_items.sort(key=lambda row: (row[0], str(row[1])))
    return (
        summary_snapshot(comments),
        codex_findings_snapshot(comments),
        tuple(gate2_items),
    )


def timestamp(value):
    """Reject missing or naive times instead of guessing a comparison zone."""
    if not isinstance(value, str):
        raise ValueError("Expected an aware timestamp")
    parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    if parsed.utcoffset() is None:
        raise ValueError("Expected a timezone")
    return parsed.astimezone(timezone.utc)


def canonical_family(value, *, allow_human):
    """Normalize and validate a model-family token fail-closed."""
    if not isinstance(value, str) or value != value.strip():
        raise ValueError("Model family must be a trimmed string")
    token = value.casefold()
    if not FAMILY_RE.fullmatch(token) or token in DISALLOWED_FAMILIES:
        raise ValueError(f"Invalid model family: {value!r}")
    if not allow_human and token == "human":
        raise ValueError("Gate 2 reviewer_family cannot be human")
    for canonical, prefixes in CANONICAL_FAMILY_PREFIXES:
        for prefix in prefixes:
            if token == prefix or token.startswith((f"{prefix}-", f"{prefix}_", f"{prefix}.")):
                return canonical
    return token


def _is_non_empty_str(value):
    return isinstance(value, str) and bool(value.strip())


def _is_int_ge(value, minimum):
    return isinstance(value, int) and not isinstance(value, bool) and value >= minimum


def _validate_finding(entry):
    if not isinstance(entry, dict):
        raise ValueError("Gate 2 finding must be an object")
    if not {"severity", "summary"} <= set(entry) or not set(entry) <= GATE2_FINDING_KEYS:
        raise ValueError("Invalid Gate 2 finding keys")
    severity = entry["severity"]
    if not isinstance(severity, str) or severity not in GATE2_SEVERITIES:
        raise ValueError("Invalid Gate 2 finding severity")
    if not _is_non_empty_str(entry["summary"]):
        raise ValueError("Gate 2 finding summary must be non-empty")
    for str_key in ("path", "id", "fingerprint", "surface", "repro_status"):
        if str_key in entry and entry[str_key] is not None:
            if not _is_non_empty_str(entry[str_key]):
                raise ValueError(f"Gate 2 finding {str_key} must be a non-empty string or null")
    for int_key in ("line", "consensus_count"):
        if int_key in entry and entry[int_key] is not None:
            if not _is_int_ge(entry[int_key], 1):
                raise ValueError(f"Gate 2 finding {int_key} must be a positive integer or null")
    if "raised_by" in entry and entry["raised_by"] is not None:
        raised_by = entry["raised_by"]
        if not isinstance(raised_by, list) or not all(_is_non_empty_str(s) for s in raised_by):
            raise ValueError("Gate 2 finding raised_by must be a list of non-empty strings")


def _validate_panel_seats(seats):
    if not isinstance(seats, list):
        raise ValueError("Gate 2 panel_seats must be a list")
    completed_families = []
    for seat in seats:
        if not isinstance(seat, dict):
            raise ValueError("Gate 2 panel seat must be an object")
        keys = set(seat)
        if not {"seat", "family", "status", "verdict"} <= keys or not keys <= GATE2_PANEL_SEAT_KEYS:
            raise ValueError("Invalid Gate 2 panel seat keys")
        if not _is_non_empty_str(seat["seat"]) or not _is_non_empty_str(seat["status"]):
            raise ValueError("Gate 2 panel seat and status must be non-empty")
        fam = canonical_family(seat["family"], allow_human=False)
        if fam == "multi":
            raise ValueError("Gate 2 panel seat family cannot be multi")
        if not _is_non_empty_str(seat["verdict"]):
            raise ValueError("Gate 2 panel seat verdict must be non-empty")
        if seat["status"] == "completed":
            if seat["verdict"] not in GATE2_VERDICTS:
                raise ValueError("Invalid completed Gate 2 panel seat verdict")
            completed_families.append(fam)
        for opt_str in ("model_label", "role"):
            if opt_str in seat and seat[opt_str] is not None and not _is_non_empty_str(seat[opt_str]):
                raise ValueError(f"Gate 2 panel seat {opt_str} must be non-empty")
        if "findings_count" in seat and seat["findings_count"] is not None:
            if not _is_int_ge(seat["findings_count"], 0):
                raise ValueError("Gate 2 panel seat findings_count must be a non-negative integer")
        if "latency_sec" in seat and seat["latency_sec"] is not None:
            lat = seat["latency_sec"]
            if not isinstance(lat, (int, float)) or isinstance(lat, bool) or lat < 0:
                raise ValueError("Gate 2 panel seat latency_sec must be a non-negative number")
    return completed_families


def _validate_prior_findings_status(items, verdict):
    if not isinstance(items, list):
        raise ValueError("Gate 2 prior_findings_status must be a list")
    for item in items:
        if isinstance(item, dict):
            if not _is_non_empty_str(item.get("id")) or not _is_non_empty_str(item.get("status")):
                raise ValueError("Gate 2 prior_findings_status entry requires id and status")
            if verdict == "clean" and item["status"] == "still_open":
                raise ValueError("Clean Gate 2 verdict cannot retain still_open prior findings")
        elif not _is_non_empty_str(item):
            raise ValueError("Invalid Gate 2 prior_findings_status entry")


def _validate_coverage(coverage, verdict):
    if not isinstance(coverage, dict):
        raise ValueError("Gate 2 coverage must be an object")
    for key, val in coverage.items():
        if not _is_non_empty_str(key) or not _is_int_ge(val, 0):
            raise ValueError("Gate 2 coverage entries must be non-negative integers")
    if verdict == "clean" and coverage.get("blocked", 0) > 0:
        raise ValueError("Clean Gate 2 verdict cannot have blocked coverage")


def parse_gate2_payload(body, *, strict_identity_key=True):
    """Parse and validate an anneal-gate2-review:v1 structured payload."""
    markers = re.findall(r"<!-- anneal-gate2-review:.*?-->", body, re.DOTALL)
    if body.count(GATE2_MARKER) != 1 or len(markers) != 1:
        raise ValueError("Ambiguous Gate 2 review marker")
    match = re.fullmatch(r"<!-- anneal-gate2-review:v1 (.*?) -->", markers[0],
                         re.DOTALL)
    if match is None:
        raise ValueError("Unsupported Gate 2 review version")
    payload = json.loads(match[1], object_pairs_hook=unique_object)
    if not isinstance(payload, dict):
        raise ValueError("Gate 2 review payload must be an object")
    keys = set(payload)
    if not GATE2_REQUIRED_KEYS <= keys or not keys <= (GATE2_REQUIRED_KEYS | GATE2_OPTIONAL_KEYS):
        raise ValueError("Invalid Gate 2 review payload keys")
    for sha_key in ("base_sha", "head_sha", "tree_sha"):
        val = payload[sha_key]
        if not isinstance(val, str) or not SHA1_RE.fullmatch(val):
            raise ValueError(f"Invalid Gate 2 {sha_key}")
    if "parent_tree" in payload and payload["parent_tree"] is not None and (
            not isinstance(payload["parent_tree"], str)
            or not SHA1_RE.fullmatch(payload["parent_tree"])):
        raise ValueError("Invalid Gate 2 parent_tree")
    if "commit_msg_sha256" in payload and payload["commit_msg_sha256"] is not None and (
            not isinstance(payload["commit_msg_sha256"], str)
            or not SHA256_RE.fullmatch(payload["commit_msg_sha256"])):
        raise ValueError("Invalid Gate 2 commit_msg_sha256")
    if "merge_base" in payload and (
            not isinstance(payload["merge_base"], str)
            or not SHA1_RE.fullmatch(payload["merge_base"])):
        raise ValueError("Invalid Gate 2 merge_base")
    if "round" in payload and not _is_int_ge(payload["round"], 1):
        raise ValueError("Invalid Gate 2 round")
    if "risk_tier" in payload and not _is_non_empty_str(payload["risk_tier"]):
        raise ValueError("Invalid Gate 2 risk_tier")
    if "identity_key" in payload and strict_identity_key:
        ik = payload["identity_key"]
        if not _is_non_empty_str(ik):
            raise ValueError("Invalid Gate 2 identity_key")
        one_m = ONE_IDENTITY_RE.fullmatch(ik)
        multi_m = MULTI_IDENTITY_RE.fullmatch(ik)
        if one_m is not None:
            ik_parent_tree, ik_tree, ik_msg_hash = one_m.groups()
            if ik_tree != payload["tree_sha"]:
                raise ValueError("Gate 2 identity_key tree_sha mismatch")
            if payload.get("parent_tree") is not None and ik_parent_tree != payload["parent_tree"]:
                raise ValueError("Gate 2 identity_key parent_tree mismatch")
            if payload.get("commit_msg_sha256") is not None and ik_msg_hash != payload["commit_msg_sha256"]:
                raise ValueError("Gate 2 identity_key commit_msg_sha256 mismatch")
        elif multi_m is not None:
            ik_base, ik_head = multi_m.groups()
            if ik_base != payload["base_sha"] or ik_head != payload["head_sha"]:
                raise ValueError("Gate 2 identity_key base/head mismatch")
        elif ik.strip().casefold().startswith(("one:", "multi:")):
            raise ValueError("Invalid Gate 2 identity_key format")
    if "reviewed_at" in payload:
        timestamp(payload["reviewed_at"])
    reviewer_norm = canonical_family(payload["reviewer_family"], allow_human=False)
    author_norm = canonical_family(payload["author_family"], allow_human=True)
    verdict = payload["verdict"]
    if verdict not in GATE2_VERDICTS:
        raise ValueError("Invalid Gate 2 verdict")
    findings = payload["findings"]
    if not isinstance(findings, list):
        raise ValueError("Gate 2 findings must be a list")
    for entry in findings:
        _validate_finding(entry)
    if verdict == "clean" and findings:
        raise ValueError("Clean Gate 2 verdict cannot include findings")
    if verdict == "findings" and not findings:
        raise ValueError("Findings Gate 2 verdict requires non-empty findings")
    if "advisories" in payload:
        advisories = payload["advisories"]
        if not isinstance(advisories, list):
            raise ValueError("Gate 2 advisories must be a list")
        for entry in advisories:
            _validate_finding(entry)
            if entry["severity"] != "P3":
                raise ValueError("Gate 2 advisories must have severity P3")
    if "prior_findings_status" in payload:
        _validate_prior_findings_status(payload["prior_findings_status"], verdict)
    if "coverage" in payload:
        _validate_coverage(payload["coverage"], verdict)
    completed_seat_families = None
    if "panel_seats" in payload:
        completed_seat_families = _validate_panel_seats(payload["panel_seats"])
    if reviewer_norm == "multi" and (
            completed_seat_families is None or not payload["panel_seats"]):
        raise ValueError("Multi reviewer_family requires non-empty panel_seats")
    return payload, reviewer_norm, author_norm, completed_seat_families


def _gate2_item_timestamp(source, item):
    raw = item.get("submitted_at") if source == "review" else item.get("created_at")
    return timestamp(raw)


def _is_structured_identity_key(value):
    return isinstance(value, str) and (
        ONE_IDENTITY_RE.fullmatch(value) is not None
        or MULTI_IDENTITY_RE.fullmatch(value) is not None
    )


def _is_one_commit_identity_match(payload, head, base_sha, tree_sha,
                                  identity_key, historical_identities=None):
    if not (
        isinstance(identity_key, str)
        and ONE_IDENTITY_RE.fullmatch(identity_key) is not None
        and payload.get("identity_key") == identity_key
        and tree_sha is not None
        and payload["tree_sha"] == tree_sha
        and base_sha is not None
        and (payload.get("merge_base") is None
             or payload["merge_base"] == payload["base_sha"])
    ):
        return False
    p_head = payload["head_sha"]
    p_base = payload["base_sha"]
    if p_head == head and p_base == base_sha:
        return True
    if not isinstance(historical_identities, dict):
        return False
    return historical_identities.get((p_head, p_base)) == (tree_sha, identity_key)


def _has_verified_historical_one_commit_identity(payload, head, base_sha,
                                                 tree_sha, identity_key,
                                                 historical_identities):
    if not (
        isinstance(identity_key, str)
        and ONE_IDENTITY_RE.fullmatch(identity_key) is not None
        and tree_sha is not None
        and payload["tree_sha"] == tree_sha
        and base_sha is not None
        and isinstance(historical_identities, dict)
    ):
        return False
    p_head = payload["head_sha"]
    p_base = payload["base_sha"]
    if (p_head, p_base) == (head, base_sha):
        return False
    return historical_identities.get((p_head, p_base)) == (tree_sha, identity_key)


def _has_verified_historical_same_tree(payload, head, base_sha, tree_sha,
                                       historical_identities,
                                       historical_trees=None):
    if (
        tree_sha is None
        or payload["tree_sha"] != tree_sha
        or base_sha is None
    ):
        return False
    p_head = payload["head_sha"]
    p_base = payload["base_sha"]
    if (p_head, p_base) == (head, base_sha):
        return False
    # Caller-supplied tree_sha is head's verified tree, so p_head == head
    # confirms the tree across base_sha retargets without historical_trees.
    if p_head == head:
        return True
    if isinstance(historical_trees, dict) and historical_trees.get(p_head) == tree_sha:
        return True
    if isinstance(historical_identities, dict):
        hist = historical_identities.get((p_head, p_base))
        return hist is not None and hist[0] == tree_sha
    return False


def _matches_historical_codex_commit(commit_sha, tree_sha,
                                     historical_identities,
                                     historical_trees=None):
    if not (
        isinstance(commit_sha, str)
        and SHA1_RE.fullmatch(commit_sha) is not None
        and tree_sha is not None
    ):
        return False
    if isinstance(historical_trees, dict) and historical_trees.get(commit_sha) == tree_sha:
        return True
    if not isinstance(historical_identities, dict):
        return False
    # Block active completed legacy Codex findings whenever GitHub confirms
    # the historical commit's tree matches the current PR tree.
    return any(
        p_head == commit_sha and val is not None and val[0] == tree_sha
        for (p_head, _p_base), val in historical_identities.items()
    )


def _matches_gate2_identity(payload, head, base_sha, tree_sha,
                            identity_key=None, historical_identities=None):
    if _is_one_commit_identity_match(
        payload, head, base_sha, tree_sha, identity_key,
        historical_identities=historical_identities,
    ):
        return True
    return (
        payload["head_sha"] == head
        and (base_sha is None or payload["base_sha"] == base_sha)
        and (tree_sha is None or payload["tree_sha"] == tree_sha)
    )


# Rebase-only carry-forward. A base change may touch this PR file only when
# the PR's own added and removed lines in it are unchanged: each line names
# its file and digest, so a line's meaning does not depend on its context.
CARRY_FORWARD_OVERLAP_PATHS = frozenset({"anneal/trusted/root-manifest.sha256"})
# Base changes to the rules that govern reviews (or to this evaluator)
# always need a new review: CI cannot tell whether they got stricter.
CARRY_FORWARD_POLICY_PATHS = frozenset({
    ".gemini/styleguide.md", "anneal/.gemini/styleguide.md",
    "anneal/docs/codex-review.md", "anneal/docs/review-policy-design.md",
    "anneal/docs/trust-model.md", "anneal/ci/codex_review.py",
    "anneal/META_PRINCIPLES.md", "anneal/PRINCIPLES.md",
    "anneal/THREAT_MODEL.md",
})
# Agent instruction files anywhere in the tree.
CARRY_FORWARD_POLICY_BASENAMES = frozenset({
    "AGENTS.md", "AGENTS.override.md", "CLAUDE.md", "GEMINI.md",
})
CARRY_FORWARD_POLICY_PREFIXES = (
    ".github/", "anneal/.github/", "skills/", "anneal/skills/",
)
# GitHub truncates a commit's or comparison's file list at 300 entries.
MAX_API_FILES = 300
_DIFF_HEADER_RE = re.compile(r"^diff --git a/(.*) b/(.*)$")
_DIFF_MODE_RE = re.compile(
    r"^(?:old mode|new mode|new file mode|deleted file mode) ([0-7]{6})$"
)
_DIFF_INDEX_MODE_RE = re.compile(r"^index [0-9a-f]+\.\.[0-9a-f]+ ([0-7]{6})$")


def _patch_change_lines(patch):
    """A unified diff's added, removed, and no-newline lines, in order."""
    return [line for line in patch.split("\n")
            if line.startswith(("+", "-", "\\"))]


def _file_change_key(entry, relaxed_paths):
    if not isinstance(entry, dict):
        raise ValueError("Invalid commit file entry")
    name = entry.get("filename")
    status = entry.get("status")
    patch = entry.get("patch")
    previous = entry.get("previous_filename")
    blob = entry.get("sha")
    if (not _is_non_empty_str(name) or not _is_non_empty_str(status)
            or not isinstance(patch, str)
            or (previous is not None and not _is_non_empty_str(previous))):
        # A missing patch (binary or oversized file) cannot be compared.
        raise ValueError("Uncomparable commit file entry")
    if name in relaxed_paths and status == "modified":
        # The base changed this allowlisted file, so its blob differs.
        content = None
    elif isinstance(blob, str) and SHA1_RE.fullmatch(blob) is not None:
        # The base did not touch the file, so the result must be identical.
        content = blob
    else:
        raise ValueError("Commit file entry has no blob SHA")
    return name, (status, previous, content, tuple(_patch_change_lines(patch)))


def rebase_only_patch_equivalent(old_files, new_files, relaxed_paths=frozenset()):
    """Whether two one-commit patches make exactly the same changes.

    Context lines and hunk positions may differ. The file set, statuses,
    rename sources, added and removed lines, and resulting blobs may not,
    except that `relaxed_paths` (allowlisted files the base changed) skip
    the blob comparison.
    """
    if (not isinstance(old_files, list) or not isinstance(new_files, list)
            or not old_files or len(old_files) >= MAX_API_FILES
            or len(new_files) >= MAX_API_FILES):
        return False
    try:
        old = dict(_file_change_key(f, relaxed_paths) for f in old_files)
        new = dict(_file_change_key(f, relaxed_paths) for f in new_files)
    except ValueError:
        return False
    return len(old) == len(old_files) and len(new) == len(new_files) and old == new


def _change_set(files):
    """A commit's file names and added and removed lines, base-independent.

    Returns None when a file has no comparable patch.
    """
    if not isinstance(files, list) or len(files) >= MAX_API_FILES:
        return None
    changes = set()
    for entry in files:
        if (not isinstance(entry, dict) or not _is_non_empty_str(entry.get("filename"))
                or not isinstance(entry.get("patch"), str)):
            return None
        changes.add((entry["filename"], tuple(_patch_change_lines(entry["patch"]))))
    return frozenset(changes)


def diff_file_modes(diff_text):
    """Maps each file in a `git diff` to its mode header lines.

    GitHub's JSON file list omits modes, so they come from the raw diff.
    Returns None when the diff cannot be parsed.
    """
    if not isinstance(diff_text, str):
        return None
    modes, current = {}, None
    for line in diff_text.split("\n"):
        if line.startswith("diff --git "):
            header = _DIFF_HEADER_RE.match(line)
            if header is None or header.group(2) in modes:
                return None
            current = header.group(2)
            modes[current] = []
        elif current is None:
            continue
        elif line.startswith(("@@", "--- ", "+++ ", "Binary ")):
            current = None
        elif _DIFF_MODE_RE.match(line):
            modes[current].append(line)
        else:
            index = _DIFF_INDEX_MODE_RE.match(line)
            if index:
                modes[current].append(f"index {index.group(1)}")
    # `git diff` names a mode for every file; a section without one means
    # an unexpected or truncated format.
    if any(not lines for lines in modes.values()):
        return None
    return modes


def pr_paths(files):
    paths = set()
    for entry in files:
        if not isinstance(entry, dict) or not _is_non_empty_str(entry.get("filename")):
            raise ValueError("Invalid commit file entry")
        paths.add(entry["filename"])
        previous = entry.get("previous_filename")
        if previous is not None:
            if not _is_non_empty_str(previous):
                raise ValueError("Invalid commit file entry")
            paths.add(previous)
    return paths


def base_drift_allows_carry_forward(compare_status, base_files, paths):
    """Returns the allowlisted PR files the base touched, or None.

    The base must have moved strictly forward without touching any PR file
    outside the allowlist or any review-governing file; the caller still
    requires the PR's own lines in the returned files to be unchanged.
    """
    if (compare_status != "ahead" or not isinstance(base_files, list)
            or not base_files or len(base_files) >= MAX_API_FILES):
        return None
    relaxed = set()
    for entry in base_files:
        if not isinstance(entry, dict) or not _is_non_empty_str(entry.get("filename")):
            return None
        previous = entry.get("previous_filename")
        if previous is not None and not _is_non_empty_str(previous):
            return None
        touched = {entry["filename"]} | ({previous} if previous else set())
        if any(path in CARRY_FORWARD_POLICY_PATHS
               or path.startswith(CARRY_FORWARD_POLICY_PREFIXES)
               or path.rsplit("/", 1)[-1] in CARRY_FORWARD_POLICY_BASENAMES
               for path in touched):
            return None
        for path in touched & paths:
            if path not in CARRY_FORWARD_OVERLAP_PATHS:
                return None
            relaxed.add(path)
    return frozenset(relaxed)


def _carry_forward_blocked_by_history(comments, reviews, authorized_reviewers,
                                      anchor_head, anchor_tree,
                                      deleted_through=0):
    """Whether any Gate 2 or Codex evidence on the anchor could still block.

    Conservative: any legacy Codex summary that is not a completed clean
    review stops the carry-forward, as does any Gate 2 item recorded on the
    anchor's head or tree (every commit with the anchor's one-commit
    identity has that tree) that has findings or fails on its own recorded
    identity, mirroring which failures the normal rules keep blocking.
    """
    for source, entries in (("comment", comments), ("review", reviews)):
        for item in entries:
            if not authentic_gate2_item(item, authorized_reviewers):
                continue
            try:
                payload, _, _, _ = parse_gate2_payload(
                    item.get("body") or "", strict_identity_key=False,
                )
            except ValueError:
                continue
            if (payload["head_sha"] != anchor_head
                    and payload["tree_sha"] != anchor_tree):
                continue
            if payload["findings"] or payload["verdict"] == "findings":
                return True
            if source == "comment" and item["id"] <= deleted_through:
                continue
            if _is_blocking_non_finding_failure(
                    source, item, payload["head_sha"], payload["base_sha"],
                    payload["tree_sha"]):
                return True
    for comment in comments:
        if not authentic_summary(comment):
            continue
        try:
            review = _parse_codex_summary(comment.get("body") or "")
        except ValueError:
            return True
        if (review.get("status") != "completed"
                or review.get("has_any_findings") is not False
                or review.get("has_unresolved_findings") is not False):
            return True
    return False


def _gate2_failure_heads(comments, reviews, authorized_reviewers):
    """Heads named by authentic Gate 2 items that have findings or fail."""
    heads = set()
    for source, entries in (("comment", comments), ("review", reviews)):
        for item in entries:
            if not authentic_gate2_item(item, authorized_reviewers):
                continue
            try:
                payload, _, _, _ = parse_gate2_payload(
                    item.get("body") or "", strict_identity_key=False,
                )
            except ValueError:
                continue
            if (payload["findings"] or payload["verdict"] == "findings"
                    or _is_blocking_non_finding_failure(
                        source, item, payload["head_sha"], payload["base_sha"],
                        payload["tree_sha"])):
                heads.add(payload["head_sha"])
    return heads


def _carry_forward_result(head, comments, reviews, deleted_through, base_sha,
                          tree_sha, authorized_reviewers, identity_key,
                          verifier):
    """Carry the latest clean Gate 2 review forward across a rebase.

    The latest eligible Gate 2 item must be a clean review of an earlier
    head on a different base. `verifier` must confirm with GitHub data
    that the PR was only rebased and return that head's verified one-commit
    identity key (see `GitHub.verify_rebase_carry_forward`); the review must
    then pass on that verified identity with no blocking evidence left.
    """
    if not (isinstance(identity_key, str)
            and ONE_IDENTITY_RE.fullmatch(identity_key) is not None
            and base_sha is not None and tree_sha is not None):
        return None
    items = [
        ("review", r) for r in reviews if authentic_gate2_item(r, authorized_reviewers)
    ] + [
        ("comment", c) for c in comments if authentic_gate2_item(c, authorized_reviewers)
    ]
    if not items:
        return None
    # The anchor must be the latest Gate 2 item of all, so a deletion can
    # never hide a newer, still-present item behind it.
    source, item = sorted(items, key=_gate2_item_sort_key)[-1]
    if source == "comment" and item["id"] <= deleted_through:
        return None
    try:
        payload, _, _, _ = parse_gate2_payload(item.get("body") or "")
    except ValueError:
        return None
    a_head, a_base, a_tree = payload["head_sha"], payload["base_sha"], payload["tree_sha"]
    if (payload["verdict"] != "clean" or payload["findings"]
            or a_head == head or a_base == base_sha
            or _carry_forward_blocked_by_history(
                comments, reviews, authorized_reviewers, a_head, a_tree,
                deleted_through)):
        return None
    # Findings or failures recorded on any other head may concern this
    # same patch (for example on an earlier rebase), so the verifier must
    # show that each such head's patch differs from the anchor's.
    other_heads = sorted(_gate2_failure_heads(comments, reviews,
                                              authorized_reviewers) - {a_head})
    try:
        anchor_ik = verifier(a_head, a_base, a_tree, head, base_sha, other_heads)
    except (RuntimeError, ValueError, OSError):
        return None
    if not (isinstance(anchor_ik, str)
            and ONE_IDENTITY_RE.fullmatch(anchor_ik) is not None):
        return None
    # The whole PR history, judged as of the anchor's verified identity,
    # must pass; this also re-checks a structured identity_key.
    anchor_res = review_result(
        a_head, comments, deleted_through, None, reviews=reviews,
        base_sha=a_base, tree_sha=a_tree,
        authorized_reviewers=authorized_reviewers, identity_key=anchor_ik,
    )
    if anchor_res.state != "success":
        return None
    return Result(
        "success",
        f"Gate 2 review of {a_head[:12]} carried forward "
        f"(rebase only, verified; {payload['reviewer_family']})",
    )

def _evaluate_gate2_item(source, item, head, base_sha, tree_sha, base_changed_at,
                         identity_key=None, historical_identities=None,
                         historical_trees=None,
                         *, strict_identity_key=True,
                         allow_historical_findings=False,
                         allow_historical_failures=False):
    body = item.get("body") or ""
    # allow_historical_failures evaluates items on a GitHub-verified historical
    # commit with this one-commit identity even without a payload
    # identity_key, so callers can carry that commit's failures forward.
    try:
        payload, reviewer_norm, author_norm, completed_seat_families = parse_gate2_payload(
            body, strict_identity_key=strict_identity_key,
        )
    except ValueError as err:
        msg = str(err)
        if "Ambiguous" in msg:
            return Result("failure", "Ambiguous Gate 2 review marker"), None
        if "Unsupported" in msg:
            return Result("failure", "Unsupported Gate 2 review version"), None
        if "verdict" in msg.lower() or "findings" in msg.lower():
            return Result("failure", "Malformed or contradictory Gate 2 verdict or findings"), None
        return Result("failure", "Malformed Gate 2 review payload"), None
    try:
        entry_ts = _gate2_item_timestamp(source, item)
    except ValueError:
        return Result("failure", "Missing or invalid Gate 2 review timestamp"), None

    if source == "review" or "state" in item:
        review_state = item.get("state")
        if review_state == "APPROVED":
            return Result("failure", "Gate 2 review must use COMMENT, never APPROVE"), payload
    if (source == "review" or "commit_id" in item) and item.get("commit_id") != payload["head_sha"]:
        return Result("failure", "Gate 2 review commit_id does not match payload head_sha"), payload
    identity_matched = _is_one_commit_identity_match(
        payload, head, base_sha, tree_sha, identity_key,
        historical_identities=historical_identities,
    )
    has_findings = bool(payload["findings"] or payload["verdict"] == "findings")
    exact_finding_matched = (
        allow_historical_findings
        and has_findings
        and payload["head_sha"] == head
        and base_sha is not None
        and payload["base_sha"] == base_sha
        and tree_sha is not None
        and payload["tree_sha"] == tree_sha
    )
    historical_finding_matched = (
        allow_historical_findings
        and has_findings
        and (
            _has_verified_historical_one_commit_identity(
                payload, head, base_sha, tree_sha, identity_key,
                historical_identities,
            )
            or _has_verified_historical_same_tree(
                payload, head, base_sha, tree_sha,
                historical_identities, historical_trees,
            )
        )
    )
    historical_failure_matched = (
        allow_historical_failures
        and _has_verified_historical_one_commit_identity(
            payload, head, base_sha, tree_sha, identity_key,
            historical_identities,
        )
    )
    effective_identity_matched = (
        identity_matched or exact_finding_matched or historical_finding_matched
        or historical_failure_matched
    )
    if not effective_identity_matched and payload["head_sha"] != head:
        return Result("pending", "Gate 2 has not reviewed this head commit"), payload
    if reviewer_norm == author_norm:
        return Result("failure", "Gate 2 reviewer_family must differ from author_family"), payload
    if (completed_seat_families is not None
            and payload["verdict"] in ("clean", "findings")
            and not any(fam != author_norm for fam in completed_seat_families)):
        return Result("failure", "Gate 2 panel_seats requires a completed cross-family seat"), payload
    if tree_sha is None:
        return Result("failure", "Cannot verify PR head tree SHA for Gate 2 review"), payload
    if payload["tree_sha"] != tree_sha:
        return Result("failure", "Gate 2 review tree_sha does not match head commit tree"), payload
    if base_sha is None:
        return Result("failure", "Cannot verify PR base SHA for Gate 2 review"), payload
    if not effective_identity_matched:
        if payload["base_sha"] != base_sha:
            return Result("pending", "Base changed; request a new Gate 2 review"), payload
        payload_ik = payload.get("identity_key")
        if (strict_identity_key
                and isinstance(identity_key, str)
                and _is_structured_identity_key(payload_ik)
                and payload_ik != identity_key):
            return Result("failure", "Gate 2 review identity_key does not match commit identity"), payload
        if (payload.get("merge_base") is not None
                and payload["merge_base"] != payload["base_sha"]):
            return Result("failure", "Gate 2 review merge_base does not match base_sha"), payload

    if source == "review" or "state" in item:
        review_state = item.get("state")
        if review_state in ("PENDING", "DISMISSED"):
            if payload["findings"]:
                return Result("failure", f"Gate 2 review reported {len(payload['findings'])} finding(s)"), payload
            return Result("pending", f"Gate 2 review is {review_state.lower()}"), payload
        if review_state == "CHANGES_REQUESTED":
            if payload["findings"]:
                return Result("failure", f"Gate 2 review reported {len(payload['findings'])} finding(s)"), payload
            return Result("failure", "Gate 2 review must use COMMENT, not CHANGES_REQUESTED"), payload
        if review_state != "COMMENTED":
            return Result("failure", "Unsupported Gate 2 review state"), payload

    if payload["findings"] or payload["verdict"] == "findings":
        return Result("failure", f"Gate 2 review reported {len(payload['findings'])} finding(s)"), payload
    # A stable pull.base.sha does not prove which base was reviewed, so a
    # review recorded against the current base_sha must postdate the last
    # base change, with or without a matching one-commit identity. Only
    # transfers from a different, GitHub-verified base_sha skip this check.
    # It runs after every failure above, so a base change can turn a would-be
    # pass into pending but never makes a failing review stop blocking.
    if payload["base_sha"] == base_sha and base_changed_at is not None:
        try:
            changed = timestamp(base_changed_at)
        except ValueError:
            return Result("failure", "Cannot establish Gate 2 freshness after base change"), payload
        if entry_ts <= changed:
            return Result("pending", "Base changed; request a new Gate 2 review"), payload
    if payload["verdict"] == "incomplete":
        return Result("pending", "Waiting for a completed Gate 2 review"), payload
    return Result("success", f"Independent cross-family Gate 2 review passed ({payload['reviewer_family']})"), payload


def _gate2_item_sort_key(entry):
    min_utc = datetime.min.replace(tzinfo=timezone.utc)
    source, item = entry
    try:
        ts = _gate2_item_timestamp(source, item)
        invalid = False
    except ValueError:
        ts = min_utc
        invalid = True
    return (invalid, ts, 0 if source == "comment" else 1, item["id"])


def _is_blocking_non_finding_failure(source, item, p_head, p_base, p_tree):
    """Whether an item fails on its own recorded (head, base, tree).

    Mirrors _find_active_gate2_failure: malformed non-finding items and items
    with a stale merge_base never block, so they need no verification.
    """
    res, payload = _evaluate_gate2_item(
        source, item, p_head, p_base, p_tree, None,
    )
    if payload is None or res.state != "failure":
        return False
    return (payload.get("merge_base") is None
            or payload["merge_base"] == payload["base_sha"])


def _find_active_gate2_failure(entries, head, base_sha, tree_sha,
                               base_changed_at, identity_key,
                               historical_identities, historical_trees,
                               *, deleted_through=0, include_non_findings=True):
    for source, item in entries:
        prior_res, prior_payload = _evaluate_gate2_item(
            source, item, head, base_sha, tree_sha, base_changed_at,
            identity_key=identity_key,
            historical_identities=historical_identities,
            historical_trees=historical_trees,
            allow_historical_findings=True,
            allow_historical_failures=True,
        )
        strict_failed = prior_payload is None
        if strict_failed:
            prior_res, prior_payload = _evaluate_gate2_item(
                source, item, head, base_sha, tree_sha, base_changed_at,
                identity_key=identity_key,
                historical_identities=historical_identities,
                historical_trees=historical_trees,
                strict_identity_key=False,
                allow_historical_findings=True,
                allow_historical_failures=True,
            )
        if prior_payload is None or prior_res.state != "failure":
            continue
        has_findings = bool(
            prior_payload["findings"] or prior_payload["verdict"] == "findings"
        )
        if strict_failed and not has_findings:
            continue
        exact_match = (
            prior_payload["head_sha"] == head
            and (base_sha is None or prior_payload["base_sha"] == base_sha)
            and (tree_sha is None or prior_payload["tree_sha"] == tree_sha)
        )
        if has_findings:
            if (exact_match
                    or _is_one_commit_identity_match(
                        prior_payload, head, base_sha, tree_sha, identity_key,
                        historical_identities=historical_identities,
                    )
                    or _has_verified_historical_one_commit_identity(
                        prior_payload, head, base_sha, tree_sha, identity_key,
                        historical_identities,
                    )
                    or _has_verified_historical_same_tree(
                        prior_payload, head, base_sha, tree_sha,
                        historical_identities, historical_trees,
                    )):
                return prior_res, prior_payload
            continue
        if not include_non_findings or (source == "comment" and item["id"] <= deleted_through):
            continue
        # Non-findings failures (CHANGES_REQUESTED, APPROVED, same-family,
        # mismatched commit_id) remain blocking on the exact identity and on
        # any GitHub-verified historical commit with this one-commit identity
        # (the commits a clean verdict could transfer from), unless invalidated
        # by a mismatched structured identity_key or merge_base.
        identity_applicable = (
            exact_match
            or _is_one_commit_identity_match(
                prior_payload, head, base_sha, tree_sha, identity_key,
                historical_identities=historical_identities,
            )
            or _has_verified_historical_one_commit_identity(
                prior_payload, head, base_sha, tree_sha, identity_key,
                historical_identities,
            )
        )
        payload_ik = prior_payload.get("identity_key")
        ik_applicable = not (
            isinstance(identity_key, str)
            and _is_structured_identity_key(payload_ik)
            and payload_ik != identity_key
        )
        merge_base_applicable = (
            prior_payload.get("merge_base") is None
            or prior_payload["merge_base"] == prior_payload["base_sha"]
        )
        if identity_applicable and ik_applicable and merge_base_applicable:
            return prior_res, prior_payload
    return None


def review_gate2_result(head, comments, reviews=(), deleted_through=0,
                        base_changed_at=None, base_sha=None, tree_sha=None,
                        authorized_reviewers=None, identity_key=None,
                        historical_identities=None, historical_trees=None):
    """Evaluate structured anneal-gate2-review:v1 reviews and comments."""
    comment_candidates = [c for c in comments if authentic_gate2_item(c, authorized_reviewers)]
    review_candidates = [r for r in reviews if authentic_gate2_item(r, authorized_reviewers)]
    if not comment_candidates and not review_candidates:
        return None, None
    all_items = sorted(
        [("review", r) for r in review_candidates]
        + [("comment", c) for c in comment_candidates],
        key=_gate2_item_sort_key,
    )
    eligible = [
        ("review", r) for r in review_candidates
    ] + [
        ("comment", c) for c in comment_candidates if c["id"] > deleted_through
    ]
    if not eligible:
        # deleted_through only prevents older comments from approving; it must
        # never waive still-present finding comments on the active identity.
        prior_finding = _find_active_gate2_failure(
            all_items, head, base_sha, tree_sha, base_changed_at,
            identity_key, historical_identities, historical_trees,
            deleted_through=deleted_through, include_non_findings=False,
        )
        if prior_finding is not None:
            return prior_finding
        return Result("pending", "A newer Gate 2 comment was deleted; request a new review"), None

    ordered = sorted(eligible, key=_gate2_item_sort_key)
    latest_source, latest_item = ordered[-1]
    latest_res, latest_payload = _evaluate_gate2_item(
        latest_source, latest_item, head, base_sha, tree_sha, base_changed_at,
        identity_key=identity_key,
        historical_identities=historical_identities,
        historical_trees=historical_trees,
        allow_historical_findings=True,
    )
    if latest_res.state != "failure":
        # A later clean or incomplete Gate 2 review on the same identity or tree
        # cannot silently erase still-present failures (including finding
        # comments with id <= deleted_through). The latest item is included
        # too: as a failure on a verified historical commit with this identity
        # it evaluates as pending above, yet it must still block.
        # _find_active_gate2_failure returns only failures, so a clean latest
        # item never passes through it.
        active_failure = _find_active_gate2_failure(
            all_items, head, base_sha, tree_sha, base_changed_at,
            identity_key, historical_identities, historical_trees,
            deleted_through=deleted_through, include_non_findings=True,
        )
        if active_failure is not None:
            return active_failure
    return latest_res, latest_payload


def _parse_codex_summary(body):
    markers = re.findall(r"<!-- codex-review-state:.*?-->", body, re.DOTALL)
    if (body.count(SUMMARY) != 1
            or "<!-- codex-pull-request-review-summary -->" not in body
            or body.count(STATE) != 1 or len(markers) != 1):
        raise ValueError("Unrecognized or ambiguous Codex summary")
    match = re.fullmatch(r"<!-- codex-review-state:v1 (.*?) -->", markers[0],
                         re.DOTALL)
    if match is None:
        raise ValueError("Unsupported Codex review-state version")
    try:
        payload = json.loads(match[1], object_pairs_hook=unique_object)
        review = payload["code_review"]
        if not isinstance(review, dict):
            raise ValueError("Code Review state is not an object")
    except (ValueError, TypeError, KeyError) as err:
        raise ValueError("Malformed Codex Code Review state") from err
    return review


def _codex_summary_has_completed_findings(review):
    return (
        review.get("status") == "completed"
        and (review.get("has_any_findings") is not False
             or review.get("has_unresolved_findings") is not False)
    )


def _any_active_codex_findings_for_tree(comments, head, tree_sha,
                                        historical_identities,
                                        historical_trees=None):
    # Legacy Codex summaries record only a commit, so they match the current
    # head by SHA or a historical commit by its GitHub-verified tree.
    for comment in comments:
        if not authentic_summary(comment):
            continue
        try:
            review = _parse_codex_summary(comment["body"])
        except ValueError:
            continue
        if not _codex_summary_has_completed_findings(review):
            continue
        c_sha = review.get("commit_sha")
        if c_sha == head or _matches_historical_codex_commit(
            c_sha, tree_sha, historical_identities,
            historical_trees=historical_trees,
        ):
            return Result("failure", "Codex findings remain or the verdict is unknown")
    return None


def review_codex_result(head, comments, deleted_through=0, base_changed_at=None, *,
                        tree_sha=None,
                        historical_identities=None, historical_trees=None):
    """Read the latest authentic Codex summary; never fall back to an older success.

    The hidden v1 state is an observed integration format, not a documented
    OpenAI API contract. Recognize summary and state prefixes broadly enough to
    notice a replacement version, then require exactly the version understood
    here. A format change should stop merging and call for an adapter update.
    """
    latest = latest_summary(comments)
    if latest is None:
        return None
    historical_finding = _any_active_codex_findings_for_tree(
        comments, head, tree_sha,
        historical_identities, historical_trees=historical_trees,
    )
    # Comment IDs order creation. An edit to an older summary must not make it
    # supersede a newer, possibly incomplete review summary, while
    # still-present completed findings on the active identity remain blocking.
    if latest["id"] <= deleted_through:
        if historical_finding is not None:
            return historical_finding
        return Result("pending", "A newer summary was deleted; request a new summary")
    body = latest["body"]
    try:
        review = _parse_codex_summary(body)
    except ValueError as err:
        return Result("failure", str(err))

    # Security Review has an independent verdict. A clean security result,
    # emoji, or prose receipt cannot fill in a missing Code Review verdict.
    if review.get("commit_sha") != head:
        if historical_finding is not None:
            return historical_finding
        return Result("pending", "Codex has not reviewed this head commit")
    if review.get("status") != "completed":
        if historical_finding is not None:
            return historical_finding
        return Result("pending", "Waiting for a completed Codex Code Review")
    # Identity checks distinguish JSON false from null, zero, and empty strings.
    # Resolving threads by hand is insufficient: has_any_findings must also be
    # false, so Codex must publish a clean result for this revision.
    if (review.get("has_any_findings") is not False
            or review.get("has_unresolved_findings") is not False):
        return Result("failure", "Codex findings remain or the verdict is unknown")
    if historical_finding is not None:
        return historical_finding
    if base_changed_at is not None:
        # The JSON identifies only the head. After a retarget or force-push of
        # the base, require a newly created summary and a Code Review result
        # newer than that event. Merely editing an old summary, or recreating
        # it for a security-only review, must not revive an old Code Review.
        # This deliberately requires a fresh comment after a base change;
        # updated_at is not evidence that Code Review itself ran again.
        rows = [line for line in body.splitlines()
                if re.match(r"^\|[^|]*\*\*Code Review\*\*\s*\|", line)]
        completed = re.findall(r'<relative-time datetime="([^"]+)">', rows[0]) \
            if len(rows) == 1 and "**Completed**" in rows[0] else []
        try:
            changed = timestamp(base_changed_at)
            created = timestamp(latest.get("created_at"))
            if (created <= changed or len(completed) != 1
                    or timestamp(completed[0]) < created):
                return Result("pending", "Base changed; request a new Code Review summary")
        except ValueError:
            return Result("failure", "Cannot establish review freshness after base change")
    return Result("success", "Codex completed Code Review with no findings")


def review_result(head, comments, deleted_through=0, base_changed_at=None, *,
                  reviews=None, base_sha=None, tree_sha=None,
                  authorized_reviewers=None, identity_key=None,
                  historical_identities=None, historical_trees=None,
                  carry_forward_verifier=None):
    """Evaluate Gate 2 cross-family reviews and legacy Codex summaries."""
    codex_res = review_codex_result(
        head, comments, deleted_through=deleted_through,
        base_changed_at=base_changed_at,
        tree_sha=tree_sha,
        historical_identities=historical_identities,
        historical_trees=historical_trees,
    )
    gate2_res, gate2_payload = review_gate2_result(
        head, comments, reviews=reviews or (),
        deleted_through=deleted_through,
        base_changed_at=base_changed_at,
        base_sha=base_sha,
        tree_sha=tree_sha,
        authorized_reviewers=authorized_reviewers,
        identity_key=identity_key,
        historical_identities=historical_identities,
        historical_trees=historical_trees,
    )
    if (gate2_res is not None and gate2_res.state == "pending"
            and carry_forward_verifier is not None
            and (codex_res is None or codex_res.state != "failure")):
        carried = _carry_forward_result(
            head, comments, reviews or (), deleted_through, base_sha,
            tree_sha, authorized_reviewers, identity_key,
            carry_forward_verifier,
        )
        if carried is not None:
            return carried
    if gate2_res is None and codex_res is None:
        return Result("pending", "Waiting for a Gate 2 or Codex review")
    if gate2_res is None:
        return codex_res
    if codex_res is None:
        return gate2_res
    if gate2_res.state == "failure":
        return gate2_res
    if codex_res.state == "failure":
        return codex_res
    if gate2_res.state == "success":
        return gate2_res
    if codex_res.state == "success":
        if (gate2_payload is not None
                and _matches_gate2_identity(
                    gate2_payload, head, base_sha, tree_sha, identity_key,
                    historical_identities=historical_identities,
                )):
            return gate2_res
        return codex_res
    return gate2_res


def pull_snapshot(pulls):
    """Keep the PR identities that affect a commit's shared status."""
    return sorted((pull["number"], pull["head"]["sha"], pull["base"]["ref"],
                   pull["base"]["sha"]) for pull in pulls)


@dataclass(frozen=True)
class ReviewContext:
    """Comparable API observations, not an atomic GitHub transaction.

    Keep decision-relevant metadata together so adding another dependency also
    adds it to the final equality check. Summary bodies are rechecked separately
    so a comment read failure can block its PR without losing other verdicts.
    """

    pulls: tuple
    deleted: dict
    queues: dict
    bases: dict


def read_context(github, pulls=None):
    pulls = github.pulls() if pulls is None else pulls
    deleted = github.deleted_summaries()
    queues = github.queue_groups()
    bases = github.base_changes()
    numbers = {pull["number"] for pull in pulls}
    if set(bases) != numbers:
        raise RuntimeError("PR list and base history differ; recheck required")
    return ReviewContext(tuple(pull_snapshot(pulls)),
                         {n: deleted.get(n, 0) for n in numbers}, queues, bases)


def require_clean(results, success_reason):
    """Apply one all-members rule to shared heads and generated queue heads.

    Empty membership is unknown, never vacuous approval. Findings take
    precedence over waiting; any non-success result prevents success.
    """
    results = list(results)
    if not results:
        return Result("pending", "Unknown review membership")
    blockers = [result for result in results if result.state != "success"]
    if blockers:
        return next((r for r in blockers if r.state == "failure"), blockers[0])
    return Result("success", success_reason)


def combine_results(pulls, results):
    """Require each open PR sharing a commit to have its own clean result.

    A status belongs to a commit, not to a PR. Publishing independent answers
    under the same context lets the last PR overwrite the others. Group all
    open PRs, including drafts and stacks targeting other branches, so a clean
    review of one diff cannot supply a missing review of another diff.
    """
    groups = defaultdict(list)
    for pull in pulls:
        groups[pull["head"]["sha"]].append(pull["number"])
    combined = {}
    for head, numbers in groups.items():
        combined[head] = require_clean(
            (Result(results[n].state, f"PR #{n}: {results[n].reason}")
             for n in numbers),
            f"Clean Gate 2 review for all {len(numbers)} PR(s)")
    return combined


class GitHub:
    """The effect boundary: fixed-host API reads and commit-status writes."""

    def __init__(self, repository, token, authorized_reviewers=None):
        if (not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]*/[A-Za-z0-9_.-]+", repository)
                or repository.split("/")[-1] in {".", ".."}):
            raise ValueError("Expected an owner/repository name")
        self.repository = repository
        self.root = f"https://api.github.com/repos/{repository}/"
        self.token = token
        self.authorized_reviewers = (
            tuple(authorized_reviewers) if authorized_reviewers is not None else None
        )

    def request(self, path, data=None):
        return self.request_url(self.root + path, data)

    def request_url(self, url, data=None):
        request = Request(url,
                          data=None if data is None else json.dumps(data).encode(),
                          headers={"Authorization": f"Bearer {self.token}",
                                   "Accept": "application/vnd.github+json",
                                   "Content-Type": "application/json",
                                   "X-GitHub-Api-Version": "2022-11-28"})
        try:
            with urlopen(request, timeout=30) as response:
                return json.load(response)
        except HTTPError as error:
            # Do not log request headers or retry an ambiguous status write.
            # A manual recheck recomputes the result instead of replaying it.
            raise RuntimeError(
                f"GitHub {request.get_method()}: HTTP {error.code}") from None

    def graphql(self, query, variables):
        # GraphQL can return errors with HTTP 200. Both metadata readers must
        # reject that response rather than interpret missing data as no work.
        response = self.request_url("https://api.github.com/graphql", {
            "query": query, "variables": variables,
        })
        data = response.get("data")
        if (response.get("errors") or not isinstance(data, dict)
                or not isinstance(data.get("repository"), dict)):
            raise RuntimeError("GitHub could not read review context")
        return data["repository"]

    def pages(self, path):
        separator = "&" if "?" in path else "?"
        page = 1
        while True:
            batch = self.request(f"{path}{separator}per_page=100&page={page}")
            if not isinstance(batch, list):
                raise ValueError("Expected a paginated GitHub array")
            yield from batch
            if len(batch) < 100:
                return
            page += 1

    def pulls(self):
        return list(self.pages("pulls?state=open&sort=created&direction=asc"))

    def comments(self, number):
        return list(self.pages(f"issues/{number}/comments"))

    def reviews(self, number):
        return list(self.pages(f"pulls/{number}/reviews"))

    def _read_commit(self, sha):
        if not isinstance(sha, str) or not SHA1_RE.fullmatch(sha):
            raise ValueError(f"Invalid commit SHA: {sha!r}")
        commit = self.request(f"commits/{sha}")
        if not isinstance(commit, dict) or commit.get("sha") != sha:
            raise RuntimeError("GitHub returned unexpected commit metadata")
        commit_obj = commit.get("commit")
        if not isinstance(commit_obj, dict):
            raise RuntimeError("GitHub returned invalid commit metadata")
        tree_obj = commit_obj.get("tree")
        tree_sha = tree_obj.get("sha") if isinstance(tree_obj, dict) else None
        if not isinstance(tree_sha, str) or not SHA1_RE.fullmatch(tree_sha):
            raise RuntimeError("GitHub returned invalid commit tree SHA")
        return commit, commit_obj, tree_sha

    def commit_tree(self, sha):
        _, _, tree_sha = self._read_commit(sha)
        return tree_sha

    def commit_info(self, sha):
        commit, commit_obj, tree_sha = self._read_commit(sha)
        raw_parents = commit.get("parents")
        if not isinstance(raw_parents, list):
            raise RuntimeError("GitHub returned invalid commit parents")
        parents = []
        for parent in raw_parents:
            psha = parent.get("sha") if isinstance(parent, dict) else None
            if not isinstance(psha, str) or not SHA1_RE.fullmatch(psha):
                raise RuntimeError("GitHub returned invalid parent commit SHA")
            parents.append(psha)
        message = commit_obj.get("message")
        if not isinstance(message, str):
            raise RuntimeError("GitHub returned invalid commit message")
        return {
            "sha": sha,
            "tree_sha": tree_sha,
            "parents": parents,
            "message": message,
        }

    def request_text(self, path, accept):
        request = Request(self.root + path,
                          headers={"Authorization": f"Bearer {self.token}",
                                   "Accept": accept,
                                   "X-GitHub-Api-Version": "2022-11-28"})
        try:
            with urlopen(request, timeout=30) as response:
                return response.read().decode("utf-8")
        except HTTPError as error:
            raise RuntimeError(
                f"GitHub {request.get_method()}: HTTP {error.code}") from None

    def commit_files(self, sha):
        commit, _, _ = self._read_commit(sha)
        files = commit.get("files")
        if not isinstance(files, list):
            raise RuntimeError("GitHub returned invalid commit files")
        return files

    def commit_diff(self, sha):
        if not isinstance(sha, str) or not SHA1_RE.fullmatch(sha):
            raise ValueError(f"Invalid commit SHA: {sha!r}")
        return self.request_text(f"commits/{sha}", "application/vnd.github.diff")

    def compare(self, base, head):
        for sha in (base, head):
            if not isinstance(sha, str) or not SHA1_RE.fullmatch(sha):
                raise ValueError(f"Invalid commit SHA: {sha!r}")
        data = self.request(f"compare/{base}...{head}")
        if not isinstance(data, dict) or not isinstance(data.get("status"), str):
            raise RuntimeError("GitHub returned invalid comparison")
        files = data.get("files", [])
        if not isinstance(files, list):
            raise RuntimeError("GitHub returned invalid comparison files")
        return data["status"], files

    def verify_rebase_carry_forward(self, old_head, old_base, old_tree,
                                    new_head, new_base, other_heads=()):
        """Returns `old_head`'s one-commit identity key if `new_head` only
        rebases it onto a later base, else None.

        Both must be single commits on their (different) bases with the same
        message and the same file changes and modes, `old_head` must have
        the reviewed `old_tree`, and the base must have moved forward
        without touching the PR's files (the allowlisted manifest excepted)
        or the review rules. Each of `other_heads` (heads with findings or
        failures) must make different changes than `old_head`, so that no
        finding about this patch is skipped.
        """
        if old_base == new_base:
            return None
        commits = {}
        for sha in (old_head, new_head):
            commit, commit_obj, tree_sha = self._read_commit(sha)
            parents = commit.get("parents")
            files = commit.get("files")
            message = commit_obj.get("message")
            if (not isinstance(parents, list) or not isinstance(files, list)
                    or not isinstance(message, str)):
                return None
            commits[sha] = (
                [p.get("sha") if isinstance(p, dict) else None for p in parents],
                tree_sha, message, files,
            )
        old_parents, old_tree_actual, old_message, old_files = commits[old_head]
        new_parents, _, new_message, new_files = commits[new_head]
        if (old_parents != [old_base] or new_parents != [new_base]
                or old_tree_actual != old_tree or old_message != new_message):
            return None
        status, base_files = self.compare(old_base, new_base)
        relaxed = base_drift_allows_carry_forward(
            status, base_files, pr_paths(old_files) | pr_paths(new_files),
        )
        if relaxed is None or not rebase_only_patch_equivalent(
                old_files, new_files, relaxed):
            return None
        names = {entry["filename"] for entry in new_files}
        old_modes = diff_file_modes(self.commit_diff(old_head))
        new_modes = diff_file_modes(self.commit_diff(new_head))
        if (old_modes is None or new_modes is None or set(old_modes) != names
                or old_modes != new_modes):
            return None
        old_changes = _change_set(old_files)
        for sha in other_heads:
            try:
                other_files = self.commit_files(sha)
            except (RuntimeError, ValueError):
                return None
            other_changes = _change_set(other_files)
            if other_changes is None or other_changes == old_changes:
                return None
        parent_tree = self.commit_tree(old_base)
        msg_sha256 = hashlib.sha256(old_message.encode("utf-8")).hexdigest()
        return f"one:{parent_tree}:{old_tree}:{msg_sha256}"

    def commit_identity(self, head, base_sha):
        if not isinstance(base_sha, str) or not SHA1_RE.fullmatch(base_sha):
            raise ValueError(f"Invalid base commit SHA: {base_sha!r}")
        info = self.commit_info(head)
        tree_sha = info["tree_sha"]
        if len(info["parents"]) == 1 and info["parents"][0] == base_sha:
            parent_tree = self.commit_tree(base_sha)
            msg_sha256 = hashlib.sha256(
                info["message"].encode("utf-8")
            ).hexdigest()
            return tree_sha, f"one:{parent_tree}:{tree_sha}:{msg_sha256}"
        return tree_sha, f"multi:{base_sha}:{head}"

    def deleted_summaries(self):
        deleted = {}
        for status in self.pages(f"commits/{STATE_ANCHOR}/statuses"):
            match = re.fullmatch(r"Codex summary deletion/([1-9][0-9]*)/([1-9][0-9]*)",
                                 status["context"])
            if (match and status["state"] == "success"
                    and status.get("creator", {}).get("login") == PUBLISHER_LOGIN):
                number, comment = map(int, match.groups())
                deleted[number] = max(deleted.get(number, 0), comment)
        return deleted

    def record_deletion(self, event):
        """Record deletion events before they enter a coalescing job queue.

        A user may delete a bot comment, so authenticate the deleted comment's
        author, not the user who performed the deletion. Each event has a unique
        context: concurrent recorders cannot overwrite another deletion.
        """
        comment = event.get("comment") or {}
        issue = event.get("issue") or {}
        if (event.get("action") != "deleted" or not issue.get("pull_request")
                or not (authentic_summary(comment)
                        or authentic_gate2_item(comment, self.authorized_reviewers))):
            return
        number, comment_id = issue["number"], comment["id"]
        self.publish_status(STATE_ANCHOR, {
            "context": f"{DELETION_CONTEXT}{number}/{comment_id}",
            "state": "success", "description": "Deleted Codex summary; older results cannot approve",
            "target_url": f"https://github.com/{self.repository}/pull/{number}",
        })

    def queue_groups(self):
        """Read the main queue's generated heads and their required PR prefix.

        GitHub's MergeQueueEntry exposes the generated headCommit for an entry,
        its queue position, and its pullRequest. A group may incorporate earlier
        entries, so require the entire prefix through that position, including
        entries which do not yet have a generated commit. Never infer membership
        from a branch name or assume squash commits retain PR ancestry.
        """
        owner, name = self.repository.split("/")
        query = """query($owner: String!, $name: String!, $after: String) {
          repository(owner: $owner, name: $name) {
            mergeQueue(branch: "main") { entries(first: 100, after: $after) {
              nodes { position headCommit { oid }
                pullRequest { number headRefOid } }
              pageInfo { hasNextPage endCursor }
            } }
          }
        }"""
        entries, after = [], None
        while True:
            queue = self.graphql(query, {
                "owner": owner, "name": name, "after": after,
            })["mergeQueue"]
            if queue is None:
                return {}
            page = queue["entries"]
            entries.extend(page["nodes"])
            if not page["pageInfo"]["hasNextPage"]:
                break
            after = page["pageInfo"]["endCursor"]
        prefix, groups = {}, {}
        for entry in sorted(entries, key=lambda entry: entry["position"]):
            pull = entry["pullRequest"]
            prefix[pull["number"]] = pull["headRefOid"]
            if entry["headCommit"] is not None:
                head = entry["headCommit"]["oid"]
                groups.setdefault(head, {}).update(prefix)
        return groups

    def base_changes(self):
        """Read immutable base-change events, including changes before startup.

        A stable base in two consecutive API reads does not prove that an old
        review used that base. GitHub's PR timeline supplies the last retarget
        or base force-push even when no gate was deployed when it happened.
        """
        owner, name = self.repository.split("/")
        query = """query($owner: String!, $name: String!, $after: String) {
          repository(owner: $owner, name: $name) {
            pullRequests(states: OPEN, first: 100, after: $after) {
              nodes { number timelineItems(last: 1,
                itemTypes: [BASE_REF_CHANGED_EVENT, BASE_REF_FORCE_PUSHED_EVENT]) {
                nodes { ... on BaseRefChangedEvent { createdAt }
                        ... on BaseRefForcePushedEvent { createdAt } }
              } }
              pageInfo { hasNextPage endCursor }
            }
          }
        }"""
        changes, after = {}, None
        while True:
            page = self.graphql(query, {
                "owner": owner, "name": name, "after": after,
            })["pullRequests"]
            for pull in page["nodes"]:
                events = pull["timelineItems"]["nodes"]
                changes[pull["number"]] = events[-1]["createdAt"] if events else None
            if not page["pageInfo"]["hasNextPage"]:
                return changes
            after = page["pageInfo"]["endCursor"]

    def publish(self, head, result):
        # Use the SHA evaluated, never a branch name that could have advanced.
        # The Actions job's own check belongs to its default-branch checkout;
        # this explicit status is what branch protection requires on the PR.
        desired = {
            "context": CONTEXT, "state": result.state,
            "description": result.reason[:140],
            "target_url": f"https://github.com/{self.repository}/actions/workflows/codex-review.yml",
        }
        self.publish_status(head, desired)

    def publish_status(self, head, desired):
        # GitHub limits the number of statuses per commit and context. An
        # unrelated PR's event must not consume another entry for an unchanged
        # verdict. The API returns statuses newest first; stop at this context.
        current = next((status for status in self.pages(f"commits/{head}/statuses")
                        if status["context"].casefold() == desired["context"].casefold()), {})
        if (current.get("creator", {}).get("login") == PUBLISHER_LOGIN
                and all(current.get(key) == value
                        for key, value in desired.items())):
            return
        self.request(f"statuses/{head}", desired)


def publish_results(github, results, publish):
    """Use the same reporting path for normal verdicts and failed reads."""
    for head, result in sorted(results.items()):
        print(f"{head}: {result.state}: {result.reason}")
        if publish:
            github.publish(head, result)


def _parse_gate2_payload_for_reconcile(body):
    try:
        payload, _, _, _ = parse_gate2_payload(body)
        has_findings = (
            payload["verdict"] == "findings" or bool(payload.get("findings"))
        )
        return payload, has_findings
    except ValueError:
        try:
            payload, _, _, _ = parse_gate2_payload(
                body, strict_identity_key=False
            )
        except ValueError:
            return None, False
        has_findings = (
            payload["verdict"] == "findings" or bool(payload.get("findings"))
        )
        if not has_findings:
            return None, False
        return payload, True


def reconcile(github, publish=False, requested_group=None):
    """Recompute every open PR, because serialized event runs can be coalesced.

    GitHub may replace a pending concurrency-group run with a newer one. Since
    every run reads all open PRs, the retained run also covers the discarded
    event. Deletion tombstones are recorded separately before coalescing, since
    the comments API alone cannot recover a deleted summary's existence.
    """
    pulls = github.pulls()
    try:
        context = read_context(github, pulls)
    except (RuntimeError, ValueError, OSError) as error:
        # A partial API outage must not preserve success merely because the
        # metadata failed before comment evaluation. Revoke known heads when
        # the status API remains available, then expose the operational error.
        blocked = {pull["head"]["sha"]: Result("pending", "Review context unavailable")
                   for pull in pulls}
        if requested_group:
            blocked[requested_group] = Result("pending", "Review context unavailable")
        publish_results(github, blocked, publish)
        raise RuntimeError(str(error)) from None
    snapshots = {}
    identities = {}
    tree_cache = {}
    missing_historical = set()
    missing_codex_commits = set()
    results = {}
    read_errors = []
    authorized = getattr(github, "authorized_reviewers", None)
    for pull in pulls:
        number = pull["number"]
        head = pull["head"]["sha"]
        base_sha = pull["base"]["sha"]
        try:
            pr_comments = github.comments(number)
            pr_reviews = github.reviews(number)
            deleted_through = context.deleted.get(number, 0)
            active_gate2_items = []
            for source, entries in (("comment", pr_comments), ("review", pr_reviews)):
                for item in entries:
                    if not authentic_gate2_item(item, authorized):
                        continue
                    parsed, has_findings = _parse_gate2_payload_for_reconcile(
                        item.get("body") or ""
                    )
                    if (source == "comment"
                            and item["id"] <= deleted_through
                            and not has_findings):
                        continue
                    active_gate2_items.append((source, item, parsed, has_findings))
            active_codex_finding_shas = []
            for comment in pr_comments:
                if not authentic_summary(comment):
                    continue
                try:
                    codex_review = _parse_codex_summary(comment.get("body") or "")
                except ValueError:
                    continue
                c_sha = codex_review.get("commit_sha")
                if (_codex_summary_has_completed_findings(codex_review)
                        and isinstance(c_sha, str)
                        and SHA1_RE.fullmatch(c_sha) is not None
                        and c_sha != head):
                    active_codex_finding_shas.append(c_sha)

            tree_sha = None
            identity_key = None
            historical_identities = {}
            historical_trees = {}
            if active_gate2_items or active_codex_finding_shas:
                cache_key = (head, base_sha)
                if cache_key not in identities:
                    identities[cache_key] = github.commit_identity(head, base_sha)
                tree_sha, identity_key = identities[cache_key]
                tree_cache[head] = tree_sha
                is_one_identity = (
                    isinstance(identity_key, str)
                    and ONE_IDENTITY_RE.fullmatch(identity_key) is not None
                )
                for source, item, item_payload, has_findings in active_gate2_items:
                    if item_payload is None:
                        continue
                    p_head = item_payload["head_sha"]
                    p_base = item_payload["base_sha"]
                    if (p_head, p_base) == (head, base_sha):
                        continue
                    same_tree_finding = (
                        has_findings and item_payload["tree_sha"] == tree_sha
                    )
                    # Verify every same-tree non-finding item whose
                    # identity_key does not contradict ours: clean ones may
                    # transfer, and failing ones must keep blocking.
                    item_ik = item_payload.get("identity_key")
                    matching_one_candidate = (
                        not has_findings
                        and is_one_identity
                        and item_payload["tree_sha"] == tree_sha
                        and not (_is_structured_identity_key(item_ik)
                                 and item_ik != identity_key)
                    )
                    if not (same_tree_finding or matching_one_candidate):
                        continue
                    if same_tree_finding:
                        if p_head not in tree_cache:
                            tree_cache[p_head] = github.commit_tree(p_head)
                        historical_trees[p_head] = tree_cache[p_head]
                    elif matching_one_candidate:
                        hist_key = (p_head, p_base)
                        if (hist_key not in identities
                                and hist_key not in missing_historical):
                            try:
                                identities[hist_key] = github.commit_identity(
                                    p_head, p_base
                                )
                            except RuntimeError as err:
                                err_str = str(err)
                                if ("HTTP 404" in err_str
                                        or "HTTP 422" in err_str):
                                    missing_historical.add(hist_key)
                                else:
                                    raise
                        if hist_key in missing_historical:
                            # An unverifiable commit only denies clean reuse;
                            # a failure recorded on it must fail closed.
                            if _is_blocking_non_finding_failure(
                                source, item, p_head, p_base,
                                item_payload["tree_sha"],
                            ):
                                raise RuntimeError(
                                    "Cannot verify historical commit for a "
                                    "blocking Gate 2 review"
                                )
                            continue
                        historical_identities[hist_key] = identities[hist_key]

                for c_sha in dict.fromkeys(active_codex_finding_shas):
                    if c_sha in missing_codex_commits:
                        continue
                    if c_sha not in tree_cache:
                        try:
                            tree_cache[c_sha] = github.commit_tree(c_sha)
                        except RuntimeError as err:
                            err_str = str(err)
                            # A legacy Codex summary records no tree, so an
                            # unresolvable commit cannot be shown to share
                            # the current tree; like any other-tree finding,
                            # it does not block.
                            if ("HTTP 404" in err_str
                                    or "HTTP 422" in err_str):
                                missing_codex_commits.add(c_sha)
                                continue
                            raise
                    historical_trees[c_sha] = tree_cache[c_sha]
            verify = getattr(github, "verify_rebase_carry_forward", None)
            results[number] = review_result(
                head, pr_comments,
                deleted_through, context.bases[number],
                reviews=pr_reviews,
                base_sha=base_sha,
                tree_sha=tree_sha,
                authorized_reviewers=authorized,
                identity_key=identity_key,
                historical_identities=historical_identities,
                historical_trees=historical_trees,
                carry_forward_verifier=verify,
            )
            snapshots[number] = review_snapshot(pr_comments, pr_reviews, authorized)
        except (RuntimeError, ValueError, OSError) as error:
            # A failed read replaces old success with a blocking verdict where
            # the status API remains available. Other PRs are still evaluated.
            results[number] = Result("failure", "Cannot read Gate 2 reviews or summary")
            read_errors.append(f"PR #{number}: {error}")
    # A push, retarget, newly opened PR, or closure can change grouping while
    # comments are read. Leave statuses pending and let the queued event (or a
    # manual recheck) read a new snapshot rather than publish a mixed snapshot.
    try:
        if context != read_context(github):
            raise RuntimeError("Review context changed during evaluation")
        for number, original in snapshots.items():
            # PR metadata does not change when a review or summary is edited.
            # Include that evidence in the final read, rather than revalidating
            # only the commit graph and accepting a superseded verdict.
            if original != review_snapshot(
                github.comments(number), github.reviews(number), authorized
            ):
                results[number] = Result("pending", "Gate 2 review or summary changed; recheck required")
    except (RuntimeError, ValueError, OSError) as error:
        results = {pull["number"]: Result("pending", "PR snapshot changed or is unavailable")
                   for pull in pulls}
        read_errors.append(str(error))
    pr_verdicts = combine_results(pulls, results)
    combined = dict(pr_verdicts)
    by_number = {pull["number"]: pull for pull in pulls}
    for head, members in context.queues.items():
        queue_results = []
        for number, expected_head in members.items():
            pull = by_number.get(number)
            if pull is None or pull["head"]["sha"] != expected_head:
                queue_results.append(Result("pending", "Merge queue PR head changed"))
            else:
                queue_results.append(pr_verdicts[expected_head])
        # Use shared-head verdicts so queueing one PR cannot bypass a blocked
        # duplicate. An empty or unknown queue membership never passes.
        combined[head] = require_clean(
            queue_results, "Clean Gate 2 reviews for the merge queue group")
    if requested_group and requested_group not in context.queues:
        combined[requested_group] = Result("pending", "Merge queue membership is not available; recheck")
    publish_results(github, combined, publish)
    if read_errors:
        raise RuntimeError("; ".join(read_errors))
    return combined


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", default=os.environ.get("GITHUB_REPOSITORY"))
    parser.add_argument(
        "--reviewer-login",
        action="append",
        dest="reviewer_logins",
        default=None,
        help="Authorized Gate 2 reviewer GitHub login (repeatable; defaults to OWNER/MEMBER/COLLABORATOR).",
    )
    effects = parser.add_mutually_exclusive_group()
    effects.add_argument("--publish", action="store_true")
    effects.add_argument("--record-deletion", action="store_true")
    args = parser.parse_args()
    token = os.environ.get("GH_TOKEN")
    if not args.repository or not token:
        parser.error("Supply --repository and GH_TOKEN")
    github = GitHub(args.repository, token, authorized_reviewers=args.reviewer_logins)
    event_path = os.environ.get("GITHUB_EVENT_PATH")
    with open(event_path, encoding="utf-8") if event_path else io.StringIO("{}") as source:
        event = json.load(source)
    if args.record_deletion:
        github.record_deletion(event)
    else:
        group = (event.get("merge_group") or {}).get("head_sha")
        reconcile(github, args.publish, group)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, OSError) as error:
        sys.exit(str(error))
