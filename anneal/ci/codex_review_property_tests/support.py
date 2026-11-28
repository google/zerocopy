# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Shared imports, commit constants, mutants, and helpers for the
`codex_review` property tests."""

from __future__ import annotations

import hashlib
from pathlib import Path
import random
import sys
import types
from unittest.mock import patch

import codex_review
from codex_review import Result, reconcile, review_result
from test_codex_review import (
    BASE,
    HEAD,
    OTHER_BASE,
    OTHER_HEAD,
    OTHER_TREE,
    TREE,
    FakeGitHub,
    gate2_comment,
    gate2_review,
    pull,
    summary,
)


ANCHOR_HEAD = OTHER_HEAD
NEW_HEAD = HEAD
OLD_BASE = BASE
NEW_BASE = OTHER_BASE
PARENT_TREE = "1" * 40
MSG = "Subject\n\nBody text."
MSG_HASH = hashlib.sha256(MSG.encode("utf-8")).hexdigest()
ANCHOR_IK = f"one:{PARENT_TREE}:{TREE}:{MSG_HASH}"
AUTH_REVIEWERS = {"reviewer"}

# Exact 49 single-guard mutants protecting carry-forward evaluation, GitHub
# verification, Gate 2 vs. legacy Codex precedence, and history/tombstone
# ordering.
CF_MUTANTS: dict[str, tuple[str, str]] = {
    "context_lines_compared": (
        '            if line.startswith(("+", "-", "\\\\"))]',
        "            if line]",
    ),
    "no_eol_ignored": (
        '            if line.startswith(("+", "-", "\\\\"))]',
        '            if line.startswith(("+", "-"))]',
    ),
    "status_ignored": (
        "    return name, (status, previous, content, "
        "tuple(_patch_change_lines(patch)))",
        "    return name, (None, previous, content, "
        "tuple(_patch_change_lines(patch)))",
    ),
    "previous_ignored": (
        "    return name, (status, previous, content, "
        "tuple(_patch_change_lines(patch)))",
        "    return name, (status, None, content, "
        "tuple(_patch_change_lines(patch)))",
    ),
    "relaxed_any_status": (
        '    if name in relaxed_paths and status == "modified":',
        "    if name in relaxed_paths:",
    ),
    "blob_ignored": ("        content = blob\n", "        content = None\n"),
    "missing_blob_ok": (
        '        raise ValueError("Commit file entry has no blob SHA")',
        "        content = None",
    ),
    "dup_new_ok": (
        "    return len(old) == len(old_files) and len(new) == len(new_files) "
        "and old == new",
        "    return len(old) == len(old_files) and old == new",
    ),
    "file_cap_off": (
        "            or not old_files or len(old_files) >= MAX_API_FILES\n"
        "            or len(new_files) >= MAX_API_FILES):",
        "            or not old_files):",
    ),
    "overlap_any": (
        "            if path not in CARRY_FORWARD_OVERLAP_PATHS:\n"
        "                return None",
        "            if False:\n                return None",
    ),
    "base_rename_source_ignored": (
        '        touched = {entry["filename"]} | '
        "({previous} if previous else set())",
        '        touched = {entry["filename"]}',
    ),
    "base_prev_validation_off": (
        "        if previous is not None "
        "and not _is_non_empty_str(previous):\n"
        "            return None\n        touched",
        "        touched",
    ),
    "identical_ok": (
        '    if (compare_status != "ahead" or not isinstance(base_files, list)',
        '    if (compare_status not in ("ahead", "identical") '
        "or not isinstance(base_files, list)",
    ),
    "base_cap_off": (
        "            or not base_files or len(base_files) >= MAX_API_FILES):\n"
        "        return None",
        "            or not base_files):\n        return None",
    ),
    "diff_dup_ok": (
        "            if header is None or header.group(2) in modes:",
        "            if header is None:",
    ),
    "message_ignored": (
        "                or old_tree_actual != old_tree "
        "or old_message != new_message):",
        "                or old_tree_actual != old_tree):",
    ),
    "old_tree_unchecked": (
        "                or old_tree_actual != old_tree "
        "or old_message != new_message):",
        "                or old_message != new_message):",
    ),
    "parents_ignored": (
        "        if (old_parents != [old_base] or new_parents != [new_base]",
        "        if (False",
    ),
    "same_base_verify_ok": (
        "        if old_base == new_base:\n            return None\n"
        "        commits = {}",
        "        commits = {}",
    ),
    "modes_ignored": (
        "                or old_modes != new_modes):",
        "                ):",
    ),
    "mode_names_unchecked": (
        "        if (old_modes is None or new_modes is None "
        "or set(old_modes) != names",
        "        if (old_modes is None or new_modes is None",
    ),
    "anchor_eval_off": (
        '    if anchor_res.state != "success":\n        return None',
        "    pass",
    ),
    "anchor_eval_no_ik": (
        "        authorized_reviewers=authorized_reviewers, "
        "identity_key=anchor_ik,\n    )",
        "        authorized_reviewers=authorized_reviewers,\n    )",
    ),
    "history_findings_off": (
        '            if payload["findings"] '
        'or payload["verdict"] == "findings":\n'
        "                return True",
        "            if False:\n                return True",
    ),
    "history_tree_off": (
        '            if (payload["head_sha"] != anchor_head\n'
        '                    and payload["tree_sha"] != anchor_tree):',
        '            if (payload["head_sha"] != anchor_head):',
    ),
    "history_nonfinding_off": (
        "            if _is_blocking_non_finding_failure(\n"
        "                    source, item,",
        "            if False and _is_blocking_non_finding_failure(\n"
        "                    source, item,",
    ),
    "history_tomb_skip_off": (
        '            if source == "comment" '
        'and item["id"] <= deleted_through:\n'
        "                continue\n            if _is_blocking",
        "            if _is_blocking",
    ),
    "latest_tomb_check_off": (
        '    if source == "comment" and item["id"] <= deleted_through:\n'
        "        return None\n    try:",
        "    try:",
    ),
    "latest_excludes_tombstoned": (
        '        ("comment", c) for c in comments '
        "if authentic_gate2_item(c, authorized_reviewers)\n    ]",
        '        ("comment", c) for c in comments '
        "if authentic_gate2_item(c, authorized_reviewers) "
        'and c["id"] > deleted_through\n    ]',
    ),
    "history_codex_off": (
        "    for comment in comments:\n"
        "        if not authentic_summary(comment):\n"
        "            continue\n        try:\n"
        '            review = _parse_codex_summary(comment.get("body") or "")\n'
        "        except ValueError:\n            return True",
        "    for comment in ():\n"
        "        if not authentic_summary(comment):\n"
        "            continue\n        try:\n"
        '            review = _parse_codex_summary(comment.get("body") or "")\n'
        "        except ValueError:\n            return True",
    ),
    "same_base_anchor_ok": (
        "            or a_head == head or a_base == base_sha\n",
        "            or a_head == head\n",
    ),
    "same_head_anchor_ok": (
        "            or a_head == head or a_base == base_sha\n",
        "            or a_base == base_sha\n",
    ),
    "multi_identity_ok": (
        "            and ONE_IDENTITY_RE.fullmatch(identity_key) is not None\n"
        "            and base_sha is not None and tree_sha is not None):",
        "            and base_sha is not None and tree_sha is not None):",
    ),
    "verifier_ik_unchecked": (
        "    if not (isinstance(anchor_ik, str)\n"
        "            and ONE_IDENTITY_RE.fullmatch(anchor_ik) is not None):\n"
        "        return None",
        "    if not anchor_ik:\n        return None",
    ),
    "earliest_anchor": (
        "    source, item = sorted(items, key=_gate2_item_sort_key)[-1]",
        "    source, item = sorted(items, key=_gate2_item_sort_key)[0]",
    ),
    "reconcile_unwired": (
        "                carry_forward_verifier=verify,\n",
        "",
    ),
    "history_gate2_decouple_off": (
        "    if has_authentic_gate2:\n        return False",
        "    if False:\n        return False",
    ),
    "history_gate2_auth_off": (
        "            if _is_valid_cross_family_gate2_item(\n"
        "                    source, item, authorized_reviewers, deleted_through):",
        "            if True or _is_valid_cross_family_gate2_item(\n"
        "                    source, item, authorized_reviewers, deleted_through):",
    ),
    "helper_state_check_off": (
        '    if ((source == "review" or "state" in item)\n'
        '            and item.get("state") != "COMMENTED"):\n'
        "        return False",
        "    if False:\n        return False",
    ),
    "helper_seat_family_off": (
        "    if (completed_seat_families is not None\n"
        "            and not any(fam != author_norm for fam in completed_seat_families)):\n"
        "        return False",
        "    if False:\n        return False",
    ),
    "helper_tombstone_off": (
        '    if source == "comment" and item["id"] <= deleted_through and not has_findings:\n'
        "        return False",
        "    if False:\n        return False",
    ),
    "gate2_precedence_off": (
        '    if gate2_res.state in ("failure", "success"):\n'
        "        return gate2_res",
        '    if gate2_res.state == "failure":\n'
        "        return gate2_res\n"
        '    if codex_res.state == "failure":\n'
        "        return codex_res",
    ),
    "gate2_failure_precedence_off": (
        '    if gate2_res.state in ("failure", "success"):\n'
        "        return gate2_res",
        '    if gate2_res.state == "success":\n'
        "        return gate2_res",
    ),
    "pending_gate2_masks_codex_failure": (
        '    if codex_res.state == "failure":\n        return codex_res',
        "    if False:\n        return codex_res",
    ),
    "policy_path_ignored": (
        "        if any(path in CARRY_FORWARD_POLICY_PATHS\n"
        "               or path.startswith(CARRY_FORWARD_POLICY_PREFIXES)",
        "        if any(path.startswith(CARRY_FORWARD_POLICY_PREFIXES)",
    ),
    "policy_prefix_ignored": (
        "        if any(path in CARRY_FORWARD_POLICY_PATHS\n"
        "               or path.startswith(CARRY_FORWARD_POLICY_PREFIXES)",
        "        if any(path in CARRY_FORWARD_POLICY_PATHS",
    ),
    "policy_basename_ignored": (
        '               or path.rsplit("/", 1)[-1] '
        "in CARRY_FORWARD_POLICY_BASENAMES\n",
        "\n",
    ),
    "other_heads_unchecked": (
        "        for sha in other_heads:\n",
        "        for sha in ():\n",
    ),
    "changeset_eq_ignored": (
        "            if other_changes is None "
        "or other_changes == old_changes:\n",
        "            if other_changes is None:\n",
    ),
}


def _compile_mutant(source: str, tag: str) -> tuple[str, types.ModuleType]:
    name = f"_codex_review_mutant_{tag}"
    mod = types.ModuleType(name)
    mod.__file__ = codex_review.__file__
    sys.modules[name] = mod
    try:
        exec(compile(source, codex_review.__file__, "exec"), mod.__dict__)
    except Exception:
        sys.modules.pop(name, None)
        raise
    return name, mod


def _commit_obj(
    sha: str,
    parent: str,
    tree: str,
    path: str = "anneal/ci/x.py",
    blob: str = "9" * 40,
    patch_text: str = "@@ -1 +1 @@\n-a\n+b\n",
    message: str = MSG,
) -> dict:
    return {
        "sha": sha,
        "parents": [{"sha": parent}],
        "commit": {"tree": {"sha": tree}, "message": message},
        "files": [
            {
                "filename": path,
                "status": "modified",
                "sha": blob,
                "patch": patch_text,
            }
        ],
    }


def _diff_text(path: str = "anneal/ci/x.py", mode: str = "100644") -> str:
    return (
        f"diff --git a/{path} b/{path}\n"
        f"index 1111111..2222222 {mode}\n"
        f"--- a/{path}\n"
        f"+++ b/{path}\n"
        "@@ -1 +1 @@\n-a\n+b\n"
    )


def _oracle_has_active_blocker_for_head(
    gen_items: list[dict],
    head: str,
    base: str,
    tree: str,
    target_ik: str,
    deleted_through: int,
    *,
    is_carry_forward: bool = False,
) -> bool:
    """Independent oracle checking generated fixtures."""
    eligible_g2 = [
        g
        for g in gen_items
        if g["kind"] == "g2_rev"
        or (g["kind"] == "g2_cmt" and g["id"] > deleted_through)
    ]
    latest_g2 = eligible_g2[-1] if eligible_g2 else None
    latest_ik = latest_g2["ik"] if latest_g2 is not None else None
    gate2_authoritative = is_carry_forward or (
        latest_g2 is not None
        and latest_g2["head"] == head
        and latest_g2["base"] == base
        and latest_g2["tree"] == tree
        and latest_g2["verdict"] == "clean"
        and not latest_g2["findings"]
        and latest_g2["reviewer_fam"] == "gemini"
        and latest_g2["state"] in (None, "COMMENTED")
        and latest_g2["cid"] == latest_g2["head"]
        and not (
            latest_ik is not None
            and (latest_ik.startswith("one:") or latest_ik.startswith("multi:"))
            and latest_ik != target_ik
        )
    )
    for item in gen_items:
        if item["malformed"]:
            continue
        if item["kind"] == "codex":
            if (
                not gate2_authoritative
                and item["head"] == head
                and item["status"] == "completed"
                and (
                    item["any_findings"] is not False
                    or item["unres"] is not False
                )
            ):
                return True
            continue
        has_findings = item["verdict"] == "findings" or item["findings"]
        if has_findings:
            if is_carry_forward and (
                item["head"] == ANCHOR_HEAD or item["tree"] == tree
            ):
                return True
            if (
                item["head"] == head
                and item["base"] == base
                and item["tree"] == tree
            ):
                return True
            continue
        exact = (
            item["head"] == head
            and item["base"] == base
            and item["tree"] == tree
        )
        if not exact:
            continue
        ik = item["ik"]
        if ik is not None and (
            ik.startswith("one:") or ik.startswith("multi:")
        ) and ik != target_ik:
            continue
        if item["kind"] == "g2_cmt":
            if (
                item["id"] > deleted_through
                and item["reviewer_fam"] == "claude"
            ):
                return True
            continue
        if (
            item["state"] == "APPROVED"
            or item["reviewer_fam"] == "claude"
            or item["state"] == "CHANGES_REQUESTED"
            or item["cid"] != item["head"]
        ):
            return True
    return False
