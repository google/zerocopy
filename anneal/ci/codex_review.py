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
    return (summary_snapshot(comments), tuple(gate2_items))


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
    if entry["severity"] not in GATE2_SEVERITIES:
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


def parse_gate2_payload(body):
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
    for str_opt in ("risk_tier", "identity_key"):
        if str_opt in payload and not _is_non_empty_str(payload[str_opt]):
            raise ValueError(f"Invalid Gate 2 {str_opt}")
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


def _evaluate_gate2_item(source, item, head, base_sha, tree_sha, base_changed_at):
    body = item.get("body") or ""
    try:
        payload, reviewer_norm, author_norm, completed_seat_families = parse_gate2_payload(body)
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
    if payload["head_sha"] != head:
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
    if payload["base_sha"] != base_sha:
        return Result("pending", "Base changed; request a new Gate 2 review"), payload
    if base_changed_at is not None:
        try:
            changed = timestamp(base_changed_at)
        except ValueError:
            return Result("failure", "Cannot establish Gate 2 freshness after base change"), payload
        if entry_ts <= changed:
            return Result("pending", "Base changed; request a new Gate 2 review"), payload

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
    if payload["verdict"] == "incomplete":
        return Result("pending", "Waiting for a completed Gate 2 review"), payload
    return Result("success", f"Independent cross-family Gate 2 review passed ({payload['reviewer_family']})"), payload


def review_gate2_result(head, comments, reviews=(), deleted_through=0,
                        base_changed_at=None, base_sha=None, tree_sha=None,
                        authorized_reviewers=None):
    """Evaluate structured anneal-gate2-review:v1 reviews and comments."""
    comment_candidates = [c for c in comments if authentic_gate2_item(c, authorized_reviewers)]
    review_candidates = [r for r in reviews if authentic_gate2_item(r, authorized_reviewers)]
    if not comment_candidates and not review_candidates:
        return None, None
    active = [("review", r) for r in review_candidates]
    active.extend(("comment", c) for c in comment_candidates if c["id"] > deleted_through)
    if not active:
        return Result("pending", "A newer Gate 2 comment was deleted; request a new review"), None

    min_utc = datetime.min.replace(tzinfo=timezone.utc)

    def sort_key(entry):
        source, item = entry
        try:
            ts = _gate2_item_timestamp(source, item)
            invalid = False
        except ValueError:
            ts = min_utc
            invalid = True
        return (invalid, ts, 0 if source == "comment" else 1, item["id"])

    ordered = sorted(active, key=sort_key)
    latest_source, latest_item = ordered[-1]
    latest_res, latest_payload = _evaluate_gate2_item(
        latest_source, latest_item, head, base_sha, tree_sha, base_changed_at,
    )
    if latest_res.state != "failure":
        # A later clean or incomplete Gate 2 review on the same identity cannot
        # silently erase or mask findings raised on that same identity.
        for source, item in ordered[:-1]:
            prior_res, prior_payload = _evaluate_gate2_item(
                source, item, head, base_sha, tree_sha, base_changed_at,
            )
            if (prior_payload is not None
                    and prior_payload["head_sha"] == head
                    and prior_payload["base_sha"] == base_sha
                    and prior_payload["tree_sha"] == tree_sha
                    and prior_res.state == "failure"):
                return prior_res, prior_payload
    return latest_res, latest_payload


def review_codex_result(head, comments, deleted_through=0, base_changed_at=None):
    """Read the latest authentic Codex summary; never fall back to an older success.

    The hidden v1 state is an observed integration format, not a documented
    OpenAI API contract. Recognize summary and state prefixes broadly enough to
    notice a replacement version, then require exactly the version understood
    here. A format change should stop merging and call for an adapter update.
    """
    latest = latest_summary(comments)
    if latest is None:
        return None
    # Comment IDs order creation. An edit to an older summary must not make it
    # supersede a newer, possibly incomplete review summary.
    if latest["id"] <= deleted_through:
        return Result("pending", "A newer summary was deleted; request a new summary")
    body = latest["body"]
    markers = re.findall(r"<!-- codex-review-state:.*?-->", body, re.DOTALL)
    if (body.count(SUMMARY) != 1
            or "<!-- codex-pull-request-review-summary -->" not in body
            or body.count(STATE) != 1 or len(markers) != 1):
        return Result("failure", "Unrecognized or ambiguous Codex summary")
    match = re.fullmatch(r"<!-- codex-review-state:v1 (.*?) -->", markers[0],
                         re.DOTALL)
    if match is None:
        return Result("failure", "Unsupported Codex review-state version")
    try:
        payload = json.loads(match[1], object_pairs_hook=unique_object)
        review = payload["code_review"]
        if not isinstance(review, dict):
            raise ValueError("Code Review state is not an object")
    except (ValueError, TypeError, KeyError):
        return Result("failure", "Malformed Codex Code Review state")

    # Security Review has an independent verdict. A clean security result,
    # emoji, or prose receipt cannot fill in a missing Code Review verdict.
    if review.get("commit_sha") != head:
        return Result("pending", "Codex has not reviewed this head commit")
    if review.get("status") != "completed":
        return Result("pending", "Waiting for a completed Codex Code Review")
    # Identity checks distinguish JSON false from null, zero, and empty strings.
    # Resolving threads by hand is insufficient: has_any_findings must also be
    # false, so Codex must publish a clean result for this revision.
    if (review.get("has_any_findings") is not False
            or review.get("has_unresolved_findings") is not False):
        return Result("failure", "Codex findings remain or the verdict is unknown")
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
                  authorized_reviewers=None):
    """Evaluate Gate 2 cross-family reviews and legacy Codex summaries."""
    codex_res = review_codex_result(
        head, comments, deleted_through=deleted_through,
        base_changed_at=base_changed_at,
    )
    gate2_res, gate2_payload = review_gate2_result(
        head, comments, reviews=reviews or (),
        deleted_through=deleted_through,
        base_changed_at=base_changed_at,
        base_sha=base_sha,
        tree_sha=tree_sha,
        authorized_reviewers=authorized_reviewers,
    )
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
                and gate2_payload["head_sha"] == head
                and (base_sha is None or gate2_payload["base_sha"] == base_sha)):
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

    def commit_tree(self, sha):
        if not isinstance(sha, str) or not SHA1_RE.fullmatch(sha):
            raise ValueError(f"Invalid commit SHA: {sha!r}")
        commit = self.request(f"commits/{sha}")
        if not isinstance(commit, dict) or commit.get("sha") != sha:
            raise RuntimeError("GitHub returned unexpected commit metadata")
        tree_sha = ((commit.get("commit") or {}).get("tree") or {}).get("sha")
        if not isinstance(tree_sha, str) or not SHA1_RE.fullmatch(tree_sha):
            raise RuntimeError("GitHub returned invalid commit tree SHA")
        return tree_sha

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
    trees = {}
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
            has_gate2 = any(
                authentic_gate2_item(item, authorized)
                for item in (*pr_comments, *pr_reviews)
            )
            tree_sha = None
            if has_gate2:
                if head not in trees:
                    trees[head] = github.commit_tree(head)
                tree_sha = trees[head]
            results[number] = review_result(
                head, pr_comments,
                context.deleted.get(number, 0), context.bases[number],
                reviews=pr_reviews,
                base_sha=base_sha,
                tree_sha=tree_sha,
                authorized_reviewers=authorized,
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
