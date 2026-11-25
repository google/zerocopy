# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Property fuzzers, concurrency interleavings, and mutation guards."""

from __future__ import annotations

import hashlib
from pathlib import Path
import random
import sys
import types
import unittest
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

# Exact 42 single-guard mutants protecting carry-forward evaluation, GitHub
# verification, and history/tombstone ordering.
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
    "codex_gate_off": (
        '            and (codex_res is None or codex_res.state != "failure")):',
        "            ):",
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
    for item in gen_items:
        if item["malformed"]:
            continue
        if item["kind"] == "codex":
            if (
                item["head"] == head
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


class CodexReviewPropertyTests(unittest.TestCase):
    def test_carry_forward_safety_and_deletion_monotonicity_fuzzer(
        self,
    ) -> None:
        rng = random.Random(20261125)
        unrelated_head = "9" * 40
        alt_ik = f"one:{'2' * 40}:{TREE}:{MSG_HASH}"

        def verifier(o_head, o_base, o_tree, n_head, n_base, other_heads=()):
            if (o_head, o_base, o_tree, n_head, n_base) == (
                ANCHOR_HEAD,
                OLD_BASE,
                TREE,
                NEW_HEAD,
                NEW_BASE,
            ):
                return ANCHOR_IK
            return None

        carry_forward_hits = 0
        direct_failure_checked = 0
        cf_non_success_checked = 0
        direct_unblock_hits = 0
        cf_carry_unblock_hits = 0
        cf_direct_unblock_hits = 0

        for trial in range(1500):
            skew_window = trial >= 1000
            comments = []
            reviews = []
            gen_items = []
            n_items = rng.randint(2, 4) if skew_window else rng.randint(1, 5)
            next_id = 100
            for idx in range(n_items):
                next_id += rng.randint(1, 5)
                ts = f"2026-11-23T0{idx // 6}:{(idx * 7) % 60:02d}:00Z"
                if skew_window and idx == 0:
                    kind = rng.choice(["g2_cmt", "g2_cmt", "codex"])
                elif skew_window and idx == n_items - 1:
                    kind = "g2_rev"
                else:
                    kind = rng.choice(["g2_rev", "g2_rev", "g2_cmt", "codex"])
                if kind == "codex":
                    c_head = rng.choice(
                        [ANCHOR_HEAD, NEW_HEAD, unrelated_head]
                    )
                    c_status = rng.choice(
                        ["completed", "completed", "in_progress"]
                    )
                    c_any = rng.choice([False, False, True, None])
                    c_unres = rng.choice([False, False, True, None])
                    item = summary(
                        head=c_head,
                        created_at=ts,
                        completed_at=ts,
                        status=c_status,
                        has_any_findings=c_any,
                        has_unresolved_findings=c_unres,
                    )
                    item["id"] = next_id
                    malformed = rng.random() < (0.2 if skew_window else 0.08)
                    if malformed:
                        item["body"] = (
                            "<!-- codex-pull-request-review-summary -->\n"
                            "<!-- codex-review-state:v99 {} -->"
                        )
                    comments.append(item)
                    gen_items.append(
                        {
                            "kind": "codex",
                            "id": next_id,
                            "head": c_head,
                            "status": c_status,
                            "any_findings": c_any,
                            "unres": c_unres,
                            "malformed": malformed,
                        }
                    )
                    continue

                verdict = (
                    rng.choice(["clean", "clean", "findings"])
                    if skew_window
                    else rng.choice(
                        ["clean", "clean", "clean", "findings", "incomplete"]
                    )
                )
                findings = (
                    [
                        {
                            "severity": "P1",
                            "path": "a.rs",
                            "line": 1,
                            "summary": "bug",
                        }
                    ]
                    if verdict == "findings"
                    else []
                )
                if skew_window:
                    r_head = rng.choice([ANCHOR_HEAD, NEW_HEAD])
                    r_base = OLD_BASE if r_head == ANCHOR_HEAD else NEW_BASE
                    r_tree = TREE
                    ik_choice = ANCHOR_IK
                    r_fam = (
                        "gemini"
                        if idx == n_items - 1
                        else rng.choice(["gemini", "claude", "claude"])
                    )
                    if idx == n_items - 1:
                        verdict = "clean"
                        findings = []
                else:
                    r_head = rng.choice(
                        [
                            ANCHOR_HEAD,
                            ANCHOR_HEAD,
                            ANCHOR_HEAD,
                            NEW_HEAD,
                            unrelated_head,
                        ]
                    )
                    r_base = (
                        OLD_BASE
                        if r_head == ANCHOR_HEAD
                        else rng.choice([OLD_BASE, NEW_BASE])
                    )
                    r_tree = rng.choice([TREE, TREE, OTHER_TREE])
                    r_fam = rng.choice(["gemini", "gemini", "claude"])
                    ik_choice = rng.choice(
                        [ANCHOR_IK, ANCHOR_IK, alt_ik, "custom:legacy", None]
                    )
                extra = {}
                if ik_choice is not None:
                    extra["identity_key"] = ik_choice
                if kind == "g2_rev":
                    state = (
                        "COMMENTED"
                        if skew_window
                        else rng.choice(
                            [
                                "COMMENTED",
                                "COMMENTED",
                                "COMMENTED",
                                "CHANGES_REQUESTED",
                                "APPROVED",
                                "PENDING",
                            ]
                        )
                    )
                    cid = (
                        r_head
                        if skew_window or rng.random() < 0.85
                        else unrelated_head
                    )
                    reviews.append(
                        gate2_review(
                            review_id=next_id,
                            head_sha=r_head,
                            base_sha=r_base,
                            tree_sha=r_tree,
                            reviewer_family=r_fam,
                            author_family="claude",
                            verdict=verdict,
                            findings=findings,
                            state=state,
                            commit_id=cid,
                            submitted_at=ts,
                            **extra,
                        )
                    )
                    gen_items.append(
                        {
                            "kind": "g2_rev",
                            "id": next_id,
                            "head": r_head,
                            "base": r_base,
                            "tree": r_tree,
                            "reviewer_fam": r_fam,
                            "verdict": verdict,
                            "findings": bool(findings),
                            "state": state,
                            "cid": cid,
                            "ik": ik_choice,
                            "malformed": False,
                        }
                    )
                else:
                    comments.append(
                        gate2_comment(
                            comment_id=next_id,
                            head_sha=r_head,
                            base_sha=r_base,
                            tree_sha=r_tree,
                            reviewer_family=r_fam,
                            author_family="claude",
                            verdict=verdict,
                            findings=findings,
                            created_at=ts,
                            **extra,
                        )
                    )
                    gen_items.append(
                        {
                            "kind": "g2_cmt",
                            "id": next_id,
                            "head": r_head,
                            "base": r_base,
                            "tree": r_tree,
                            "reviewer_fam": r_fam,
                            "verdict": verdict,
                            "findings": bool(findings),
                            "state": None,
                            "cid": r_head,
                            "ik": ik_choice,
                            "malformed": False,
                        }
                    )

            comment_ids = sorted(c["id"] for c in comments)
            tail = [comment_ids[-1] + 10] if comment_ids else [10]
            watermarks = [0] + comment_ids + tail
            if skew_window:
                d1, d2 = 0, tail[0]
            else:
                d1 = rng.choice(watermarks)
                d2 = rng.choice([w for w in watermarks if w >= d1])

            direct_d1 = review_result(
                ANCHOR_HEAD,
                comments,
                deleted_through=d1,
                reviews=reviews,
                base_sha=OLD_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
            )
            direct_d2 = review_result(
                ANCHOR_HEAD,
                comments,
                deleted_through=d2,
                reviews=reviews,
                base_sha=OLD_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
            )
            # Omit `historical_identities` so carry-forward actually runs
            # whenever ANCHOR_HEAD clears and NEW_HEAD lacks a direct pass.
            cf_d1 = review_result(
                NEW_HEAD,
                comments,
                deleted_through=d1,
                reviews=reviews,
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            )
            cf_d2 = review_result(
                NEW_HEAD,
                comments,
                deleted_through=d2,
                reviews=reviews,
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            )

            # CI-01: Carried-forward success requires anchor success at that
            # same deletion watermark.
            for watermark, anchor_r, cf_r in (
                (d1, direct_d1, cf_d1),
                (d2, direct_d2, cf_d2),
            ):
                if "carried forward" in cf_r.reason:
                    carry_forward_hits += 1
                    self.assertEqual(
                        anchor_r.state,
                        "success",
                        f"trial={trial} d={watermark}: "
                        f"direct={anchor_r} cf={cf_r}",
                    )

            # CI-02a: For direct `review_gate2_result`, increasing
            # `deleted_through` (`d1 <= d2`) never waives an active finding or
            # failing PR review on `(ANCHOR_HEAD, OLD_BASE, TREE)`; any unblock
            # requires a tombstoned comment or Codex summary in `(d1, d2]`.
            if direct_d1.state == "failure":
                direct_failure_checked += 1
                if direct_d2.state == "success":
                    direct_unblock_hits += 1
                    self.assertFalse(
                        _oracle_has_active_blocker_for_head(
                            gen_items,
                            ANCHOR_HEAD,
                            OLD_BASE,
                            TREE,
                            ANCHOR_IK,
                            d2,
                        ),
                        f"trial={trial} direct: tombstoning waived finding "
                        f"or failing review on {d1}->{d2}: "
                        f"{direct_d1} -> {direct_d2}",
                    )
                    self.assertTrue(
                        any(d1 < c["id"] <= d2 for c in comments),
                        f"trial={trial} direct: no comment in ({d1}, {d2}]",
                    )

            # CI-02b: On NEW_HEAD (`cf_d1 -> cf_d2`), branch by whether `cf_d2`
            # passed via rebase carry-forward or direct review on NEW_HEAD.
            # Raising `deleted_through` can unblock a tombstoned non-finding
            # comment or Codex summary in `(d1, d2]`, but never waive an active
            # finding or failing PR review on the winning path.
            if cf_d1.state != "success":
                cf_non_success_checked += 1
                if cf_d2.state == "success":
                    if "carried forward" in cf_d2.reason:
                        cf_carry_unblock_hits += 1
                        self.assertFalse(
                            _oracle_has_active_blocker_for_head(
                                gen_items,
                                ANCHOR_HEAD,
                                OLD_BASE,
                                TREE,
                                ANCHOR_IK,
                                d2,
                                is_carry_forward=True,
                            ),
                            f"trial={trial} cf: tombstoning waived anchor "
                            f"blocker on {d1}->{d2}: {cf_d1} -> {cf_d2}",
                        )
                    else:
                        cf_direct_unblock_hits += 1
                        self.assertFalse(
                            _oracle_has_active_blocker_for_head(
                                gen_items,
                                NEW_HEAD,
                                NEW_BASE,
                                TREE,
                                ANCHOR_IK,
                                d2,
                            ),
                            f"trial={trial} cf direct: tombstoning waived "
                            f"NEW_HEAD blocker on {d1}->{d2}: "
                            f"{cf_d1} -> {cf_d2}",
                        )
                    self.assertTrue(
                        any(d1 < c["id"] <= d2 for c in comments),
                        f"trial={trial} cf: no comment in ({d1}, {d2}]",
                    )

        # Thresholds set comfortably below the multi-seed observed minima.
        self.assertGreaterEqual(carry_forward_hits, 20)
        self.assertGreaterEqual(direct_failure_checked, 40)
        self.assertGreaterEqual(cf_non_success_checked, 80)
        self.assertGreaterEqual(direct_unblock_hits, 5)
        self.assertGreaterEqual(cf_carry_unblock_hits, 5)
        self.assertGreaterEqual(cf_direct_unblock_hits, 5)

    def test_tombstoned_non_finding_comment_unblocks_only_comment_failures(
        self,
    ) -> None:
        # Positive + negative control for docs/codex-review.md:313-327:
        # tombstoning a non-finding issue comment unblocks a later clean review,
        # while a finding comment or failing PR review stays blocking.
        clean_anchor = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            identity_key=ANCHOR_IK,
            submitted_at="2026-11-23T02:00:00Z",
        )
        non_finding_cmt = gate2_comment(
            comment_id=15,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            reviewer_family="claude",
            author_family="claude",
            created_at="2026-11-23T01:00:00Z",
        )
        finding_cmt = gate2_comment(
            comment_id=15,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            verdict="findings",
            findings=[
                {
                    "severity": "P1",
                    "path": "a.rs",
                    "line": 1,
                    "summary": "bug",
                }
            ],
            created_at="2026-11-23T01:00:00Z",
        )
        blocking_rev = gate2_review(
            review_id=15,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            state="CHANGES_REQUESTED",
            submitted_at="2026-11-23T01:00:00Z",
        )

        self.assertEqual(
            review_result(
                ANCHOR_HEAD,
                [non_finding_cmt],
                deleted_through=0,
                reviews=[clean_anchor],
                base_sha=OLD_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
            ).state,
            "failure",
        )
        self.assertEqual(
            review_result(
                ANCHOR_HEAD,
                [non_finding_cmt],
                deleted_through=15,
                reviews=[clean_anchor],
                base_sha=OLD_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
            ).state,
            "success",
        )
        self.assertEqual(
            review_result(
                ANCHOR_HEAD,
                [finding_cmt],
                deleted_through=15,
                reviews=[clean_anchor],
                base_sha=OLD_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
            ).state,
            "failure",
        )
        self.assertEqual(
            review_result(
                ANCHOR_HEAD,
                [non_finding_cmt],
                deleted_through=15,
                reviews=[blocking_rev, clean_anchor],
                base_sha=OLD_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
            ).state,
            "failure",
        )
        verifier = lambda oh, ob, ot, nh, nb, other_heads=(): ANCHOR_IK
        self.assertEqual(
            review_result(
                NEW_HEAD,
                [non_finding_cmt],
                deleted_through=0,
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "pending",
        )
        self.assertEqual(
            review_result(
                NEW_HEAD,
                [non_finding_cmt],
                deleted_through=15,
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        self.assertEqual(
            review_result(
                NEW_HEAD,
                [finding_cmt],
                deleted_through=15,
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "pending",
        )

    def test_concurrent_context_mutation_fuzzing_never_publishes_success(
        self,
    ) -> None:
        rng = random.Random(20261125 + 4)
        mut_kinds = [
            "head_changed",
            "base_changed",
            "pr_closed",
            "deleted_jumped",
            "queue_changed",
            "base_ts_changed",
            "comment_findings_added",
            "review_findings_added",
        ]

        # Cover all 8 classes multiple times with randomized PR numbers,
        # timestamps, comment/review IDs, and benign noise items, plus an
        # unmutated control trial proving the baseline publishes `success`.
        for trial in range(160):
            pr_num = rng.randint(1, 50)
            mut_kind = mut_kinds[trial % len(mut_kinds)]
            base_pull = pull(pr_num, HEAD, "main")
            rev_id = rng.randint(10, 80)
            later_id = rev_id + rng.randint(5, 40)
            ts1 = f"2026-11-23T0{rng.randint(0, 9)}:10:00Z"
            ts2 = f"2026-11-24T0{rng.randint(0, 9)}:20:00Z"
            clean_rev = gate2_review(
                review_id=rev_id,
                head_sha=HEAD,
                base_sha=BASE,
                tree_sha=TREE,
                identity_key=ANCHOR_IK,
                submitted_at=ts1,
            )
            noise_comments = (
                [
                    summary(
                        head=HEAD,
                        created_at=ts1,
                        completed_at=ts1,
                        status="completed",
                        has_any_findings=False,
                        has_unresolved_findings=False,
                    )
                ]
                if rng.random() < 0.5
                else []
            )
            initial = [base_pull]
            final = [base_pull]
            deleted = {pr_num: 0}
            queues = {}
            bases = {pr_num: None}
            comments = {pr_num: list(noise_comments)}
            changed_comments = {}
            reviews = {pr_num: [clean_rev]}
            changed_reviews = {}

            # Periodically verify unmutated baseline on this PR topology.
            if trial % len(mut_kinds) == 0:
                ctrl_gh = FakeGitHub(
                    initial,
                    comments,
                    final=final,
                    deleted=deleted,
                    queues=queues,
                    bases=bases,
                    reviews=reviews,
                    authorized_reviewers=AUTH_REVIEWERS,
                    trees={HEAD: TREE, BASE: PARENT_TREE},
                    parents={HEAD: [BASE]},
                    messages={HEAD: MSG},
                )
                with patch("sys.stdout"):
                    ctrl_res = reconcile(ctrl_gh, publish=True)
                self.assertEqual(ctrl_res[HEAD].state, "success")
                self.assertTrue(
                    any(res.state == "success" for _, res in ctrl_gh.writes)
                )

            if mut_kind == "head_changed":
                final = [pull(pr_num, OTHER_HEAD, "main")]
            elif mut_kind == "base_changed":
                final = [
                    {
                        "number": pr_num,
                        "head": {"sha": HEAD},
                        "base": {"ref": "main", "sha": OTHER_BASE},
                        "draft": False,
                    }
                ]
            elif mut_kind == "pr_closed":
                final = []
            elif mut_kind == "deleted_jumped":
                deleted_calls = [0]
                jump_to = rng.randint(25, 200)

                class MutFakeGitHub(FakeGitHub):
                    def deleted_summaries(self):
                        val = 0 if deleted_calls[0] == 0 else jump_to
                        deleted_calls[0] += 1
                        return {pr_num: val}

                gh = MutFakeGitHub(
                    initial,
                    comments,
                    reviews=reviews,
                    authorized_reviewers=AUTH_REVIEWERS,
                    trees={HEAD: TREE, BASE: PARENT_TREE},
                    parents={HEAD: [BASE]},
                    messages={HEAD: MSG},
                )
            elif mut_kind == "queue_changed":
                q_calls = [0]

                class MutQueueGitHub(FakeGitHub):
                    def queue_groups(self):
                        val = (
                            {}
                            if q_calls[0] == 0
                            else {"9" * 40: {pr_num: HEAD}}
                        )
                        q_calls[0] += 1
                        return val

                gh = MutQueueGitHub(
                    initial,
                    comments,
                    reviews=reviews,
                    authorized_reviewers=AUTH_REVIEWERS,
                    trees={HEAD: TREE, BASE: PARENT_TREE},
                    parents={HEAD: [BASE]},
                    messages={HEAD: MSG},
                )
            elif mut_kind == "base_ts_changed":
                b_calls = [0]

                class MutBaseGitHub(FakeGitHub):
                    def base_changes(self):
                        val = (
                            {pr_num: None} if b_calls[0] == 0 else {pr_num: ts2}
                        )
                        b_calls[0] += 1
                        return val

                gh = MutBaseGitHub(
                    initial,
                    comments,
                    reviews=reviews,
                    authorized_reviewers=AUTH_REVIEWERS,
                    trees={HEAD: TREE, BASE: PARENT_TREE},
                    parents={HEAD: [BASE]},
                    messages={HEAD: MSG},
                )
            elif mut_kind == "comment_findings_added":
                changed_comments = {
                    pr_num: noise_comments
                    + [
                        gate2_comment(
                            comment_id=later_id,
                            head_sha=HEAD,
                            base_sha=BASE,
                            tree_sha=TREE,
                            verdict="findings",
                            findings=[
                                {
                                    "severity": "P1",
                                    "path": "x.rs",
                                    "line": 1,
                                    "summary": "bad",
                                }
                            ],
                            created_at=ts2,
                        )
                    ]
                }
            elif mut_kind == "review_findings_added":
                changed_reviews = {
                    pr_num: [
                        clean_rev,
                        gate2_review(
                            review_id=later_id,
                            head_sha=HEAD,
                            base_sha=BASE,
                            tree_sha=TREE,
                            verdict="findings",
                            findings=[
                                {
                                    "severity": "P1",
                                    "path": "x.rs",
                                    "line": 1,
                                    "summary": "bad",
                                }
                            ],
                            submitted_at=ts2,
                        ),
                    ]
                }

            if mut_kind not in (
                "deleted_jumped",
                "queue_changed",
                "base_ts_changed",
            ):
                gh = FakeGitHub(
                    initial,
                    comments,
                    final=final,
                    changed_comments=changed_comments,
                    deleted=deleted,
                    queues=queues,
                    bases=bases,
                    reviews=reviews,
                    changed_reviews=changed_reviews,
                    authorized_reviewers=AUTH_REVIEWERS,
                    trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: PARENT_TREE},
                    parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
                    messages={HEAD: MSG, OTHER_HEAD: MSG},
                )

            with patch("sys.stdout"):
                try:
                    reconcile(gh, publish=True)
                except RuntimeError:
                    pass
            self.assertFalse(
                any(res.state == "success" for _, res in gh.writes),
                f"trial={trial} mut_kind={mut_kind} published: {gh.writes}",
            )

    def test_keyless_legacy_and_structured_anchor_pin(self) -> None:
        # Per docs/codex-review.md:102-103 and 114-149:
        # - Non-structured legacy keys never transfer via historical_identities.
        # - Under GitHub-verified rebase carry-forward, a clean keyless or
        #   exact-anchor legacy review carries forward only with `verifier`,
        #   never without it.
        # - A contradicting structured key (`multi:` or wrong `one:`) never
        #   carries forward, even with `verifier`.
        keyless_anchor = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            submitted_at="2026-11-23T01:00:00Z",
        )
        legacy_keyed = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            identity_key="custom:legacy-v1-key",
            submitted_at="2026-11-23T01:00:00Z",
        )
        multi_keyed = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            identity_key=f"multi:{OLD_BASE}:{ANCHOR_HEAD}",
            submitted_at="2026-11-23T01:00:00Z",
        )
        wrong_one_keyed = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            identity_key=f"one:{'2' * 40}:{TREE}:{MSG_HASH}",
            submitted_at="2026-11-23T01:00:00Z",
        )
        verifier = lambda oh, ob, ot, nh, nb, other_heads=(): ANCHOR_IK

        hist = {(ANCHOR_HEAD, OLD_BASE): (TREE, ANCHOR_IK)}
        no_hist_transfer = review_result(
            NEW_HEAD,
            [],
            reviews=[legacy_keyed],
            base_sha=NEW_BASE,
            tree_sha=TREE,
            authorized_reviewers=AUTH_REVIEWERS,
            identity_key=ANCHOR_IK,
            historical_identities=hist,
        )
        self.assertEqual(no_hist_transfer.state, "pending", no_hist_transfer)

        for label, rev in (
            ("keyless", keyless_anchor),
            ("legacy", legacy_keyed),
        ):
            with self.subTest(carry_allowed=label):
                carried = review_result(
                    NEW_HEAD,
                    [],
                    reviews=[rev],
                    base_sha=NEW_BASE,
                    tree_sha=TREE,
                    authorized_reviewers=AUTH_REVIEWERS,
                    identity_key=ANCHOR_IK,
                    carry_forward_verifier=verifier,
                )
                self.assertEqual(carried.state, "success", carried)
                self.assertIn("carried forward", carried.reason)
                unverified = review_result(
                    NEW_HEAD,
                    [],
                    reviews=[rev],
                    base_sha=NEW_BASE,
                    tree_sha=TREE,
                    authorized_reviewers=AUTH_REVIEWERS,
                    identity_key=ANCHOR_IK,
                )
                self.assertEqual(unverified.state, "pending", unverified)

        for label, rev in (
            ("multi", multi_keyed),
            ("wrong_one", wrong_one_keyed),
        ):
            with self.subTest(carry_blocked=label):
                blocked = review_result(
                    NEW_HEAD,
                    [],
                    reviews=[rev],
                    base_sha=NEW_BASE,
                    tree_sha=TREE,
                    authorized_reviewers=AUTH_REVIEWERS,
                    identity_key=ANCHOR_IK,
                    carry_forward_verifier=verifier,
                )
                self.assertNotEqual(blocked.state, "success", blocked)

    def _run_carry_forward_probe_suite(self, mod: types.ModuleType) -> None:
        """Exercise all 42 carry-forward guards in-memory (no disk writes)."""
        clean_anchor = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            identity_key=ANCHOR_IK,
            submitted_at="2026-11-23T01:00:00Z",
        )
        verifier = lambda oh, ob, ot, nh, nb, other_heads=(): ANCHOR_IK

        # 1. `patch` / `rebase_only_patch_equivalent` checks:
        patch_old = (
            "@@ -1,3 +1,3 @@\n ctx1\n-old\n+new\n"
            "\\ No newline at end of file\n"
        )
        patch_ctx = (
            "@@ -10,3 +10,3 @@\n ctx2\n-old\n+new\n"
            "\\ No newline at end of file\n"
        )
        f_old = [
            {
                "filename": "anneal/ci/x.py",
                "status": "modified",
                "sha": "9" * 40,
                "patch": patch_old,
            }
        ]
        f_ctx = [
            {
                "filename": "anneal/ci/x.py",
                "status": "modified",
                "sha": "9" * 40,
                "patch": patch_ctx,
            }
        ]
        self.assertTrue(mod.rebase_only_patch_equivalent(f_old, f_ctx))
        f_noeols = [
            {
                "filename": "anneal/ci/x.py",
                "status": "modified",
                "sha": "9" * 40,
                "patch": "@@ -10,3 +10,3 @@\n ctx2\n-old\n+new\n",
            }
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(f_old, f_noeols))
        f_ren = [
            {
                "filename": "anneal/ci/x.py",
                "status": "renamed",
                "previous_filename": "a",
                "sha": "9" * 40,
                "patch": patch_old,
            }
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(f_old, f_ren))
        f_ren2 = [
            {
                "filename": "anneal/ci/x.py",
                "status": "renamed",
                "previous_filename": "b",
                "sha": "9" * 40,
                "patch": patch_old,
            }
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(f_ren, f_ren2))
        f_blob = [
            {
                "filename": "anneal/ci/x.py",
                "status": "modified",
                "sha": "8" * 40,
                "patch": patch_old,
            }
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(f_old, f_blob))
        f_add = [
            {
                "filename": "anneal/ci/x.py",
                "status": "added",
                "sha": "9" * 40,
                "patch": patch_old,
            }
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(f_old, f_add))
        f_no_blob = [
            {
                "filename": "anneal/ci/x.py",
                "status": "modified",
                "patch": patch_old,
            }
        ]
        self.assertFalse(
            mod.rebase_only_patch_equivalent(f_no_blob, f_no_blob)
        )
        try:
            mod._file_change_key(f_no_blob[0], frozenset())
            self.fail("expected ValueError on missing blob sha")
        except ValueError:
            pass
        self.assertFalse(mod.rebase_only_patch_equivalent(f_old, f_old + f_old))
        many_300 = [
            {
                "filename": f"f{i}.py",
                "status": "modified",
                "sha": "9" * 40,
                "patch": patch_old,
            }
            for i in range(300)
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(many_300, many_300))
        self.assertFalse(mod.rebase_only_patch_equivalent([], []))
        rm_path = "anneal/trusted/root-manifest.sha256"
        rm_patch = "@@ -1 +1 @@\n-a\n+b\n"
        rm_old = [
            {
                "filename": rm_path,
                "status": "modified",
                "sha": "1" * 40,
                "patch": rm_patch,
            }
        ]
        rm_new = [
            {
                "filename": rm_path,
                "status": "modified",
                "sha": "2" * 40,
                "patch": rm_patch,
            }
        ]
        self.assertTrue(
            mod.rebase_only_patch_equivalent(
                rm_old, rm_new, frozenset({rm_path})
            )
        )
        rm_add = [
            {
                "filename": rm_path,
                "status": "added",
                "sha": "2" * 40,
                "patch": rm_patch,
            }
        ]
        rm_add_other = [
            {
                "filename": rm_path,
                "status": "added",
                "sha": "1" * 40,
                "patch": rm_patch,
            }
        ]
        self.assertFalse(
            mod.rebase_only_patch_equivalent(
                rm_add, rm_new, frozenset({rm_path})
            )
        )
        self.assertFalse(
            mod.rebase_only_patch_equivalent(
                rm_add_other, rm_add, frozenset({rm_path})
            )
        )

        # 2. `base_drift_allows_carry_forward`:
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "identical",
                [{"filename": "other.py", "status": "modified"}],
                {"anneal/ci/x.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward("ahead", [], {"anneal/ci/x.py"})
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [{"filename": "other.py", "status": "modified"}] * 300,
                {"anneal/ci/x.py"},
            )
        )
        self.assertEqual(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [{"filename": "other.py", "status": "modified"}],
                {"anneal/ci/x.py"},
            ),
            frozenset(),
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [{"filename": "anneal/ci/x.py", "status": "modified"}],
                {"anneal/ci/x.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [
                    {
                        "filename": "y.py",
                        "status": "renamed",
                        "previous_filename": "anneal/ci/x.py",
                    }
                ],
                {"anneal/ci/x.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [
                    {
                        "filename": "unrelated.py",
                        "status": "modified",
                        "previous_filename": "",
                    }
                ],
                {"y.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [
                    {
                        "filename": "anneal/docs/codex-review.md",
                        "status": "modified",
                    }
                ],
                {"anneal/ci/x.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [{"filename": "AGENTS.md", "status": "modified"}],
                {"anneal/ci/x.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [{"filename": "skills/foo.md", "status": "modified"}],
                {"anneal/ci/x.py"},
            )
        )

        # 3. `diff_file_modes` & `GitHub.verify_rebase_carry_forward`:
        self.assertIsNone(mod.diff_file_modes(_diff_text() + _diff_text()))

        class StubGH(mod.GitHub):
            def __init__(
                self,
                *,
                same_base_compare=False,
                bad_msg=False,
                bad_tree=False,
                bad_parents=False,
                bad_modes=False,
                extra_mode=False,
                extra_both=False,
                diff_other=False,
            ):
                super().__init__("google/zerocopy", "tok", AUTH_REVIEWERS)
                self.same_base_compare = same_base_compare
                self.bad_msg = bad_msg
                self.bad_tree = bad_tree
                self.bad_parents = bad_parents
                self.bad_modes = bad_modes
                self.extra_mode = extra_mode
                self.extra_both = extra_both
                self.diff_other = diff_other

            def request(self, path, data=None):
                if path == f"commits/{ANCHOR_HEAD}":
                    return _commit_obj(
                        ANCHOR_HEAD,
                        "9" * 40 if self.bad_parents else OLD_BASE,
                        OTHER_TREE if self.bad_tree else TREE,
                    )
                if path == f"commits/{NEW_HEAD}":
                    return _commit_obj(
                        NEW_HEAD,
                        OLD_BASE if self.same_base_compare else NEW_BASE,
                        TREE,
                        message="changed" if self.bad_msg else MSG,
                    )
                if path == f"commits/{'9' * 40}":
                    patch_s = (
                        "@@ -1 +1 @@\n-a\n+c\n"
                        if self.diff_other
                        else "@@ -1 +1 @@\n-a\n+b\n"
                    )
                    return _commit_obj(
                        "9" * 40, OLD_BASE, TREE, patch_text=patch_s
                    )
                if path == f"commits/{OLD_BASE}":
                    return {
                        "sha": OLD_BASE,
                        "commit": {
                            "tree": {"sha": PARENT_TREE},
                            "message": "base",
                        },
                    }
                if path.startswith("compare/"):
                    return {
                        "status": "ahead",
                        "files": [
                            {"filename": "unrelated.txt", "status": "modified"}
                        ],
                    }
                raise AssertionError(path)

            def request_text(self, path, accept):
                if path == f"commits/{ANCHOR_HEAD}":
                    if self.extra_both:
                        return _diff_text() + _diff_text("anneal/ci/extra.py")
                    return _diff_text()
                if path == f"commits/{NEW_HEAD}":
                    if self.bad_modes:
                        return _diff_text(mode="100755")
                    if self.extra_mode or self.extra_both:
                        return _diff_text() + _diff_text("anneal/ci/extra.py")
                    return _diff_text()
                raise AssertionError(path)

        self.assertEqual(
            StubGH().verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            ),
            ANCHOR_IK,
        )
        self.assertEqual(
            StubGH(diff_other=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE, ["9" * 40]
            ),
            ANCHOR_IK,
        )
        self.assertIsNone(
            StubGH(diff_other=False).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE, ["9" * 40]
            )
        )
        self.assertIsNone(
            StubGH(same_base_compare=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, OLD_BASE
            )
        )
        self.assertIsNone(
            StubGH(bad_msg=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )
        self.assertIsNone(
            StubGH(bad_tree=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )
        self.assertIsNone(
            StubGH(bad_parents=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )
        self.assertIsNone(
            StubGH(bad_modes=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )
        self.assertIsNone(
            StubGH(extra_mode=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )
        self.assertIsNone(
            StubGH(extra_both=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )

        # 4. `_carry_forward_result`, `_carry_forward_blocked_by_history`,
        # and `review_result`:
        # Same head/base rejected:
        self.assertNotEqual(
            mod.review_result(
                ANCHOR_HEAD,
                [],
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [],
                reviews=[clean_anchor],
                base_sha=OLD_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # Multi / invalid identity_key rejected:
        keyless_anchor = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            submitted_at="2026-11-23T01:00:00Z",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [],
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=f"multi:{NEW_BASE}:{NEW_HEAD}",
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [],
                reviews=[keyless_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=lambda *_: "custom:bad",
            ).state,
            "success",
        )
        # Anchor eval must check anchor_ik (contradictory anchor_ik fails):
        wrong_ik_rev = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            identity_key=f"one:{'2' * 40}:{TREE}:{MSG_HASH}",
            submitted_at="2026-11-23T01:00:00Z",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [],
                reviews=[wrong_ik_rev],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # Anchor eval failure (`CHANGES_REQUESTED` on anchor) fails:
        cr_anchor = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            state="CHANGES_REQUESTED",
            identity_key=ANCHOR_IK,
            submitted_at="2026-11-23T01:00:00Z",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [],
                reviews=[cr_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # History findings on another head with the anchor's tree block:
        other_head_same_tree_finding = gate2_comment(
            comment_id=10,
            head_sha="9" * 40,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            verdict="findings",
            findings=[
                {
                    "severity": "P1",
                    "path": "a",
                    "line": 1,
                    "summary": "f",
                }
            ],
            created_at="2026-11-23T00:10:00Z",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [other_head_same_tree_finding],
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # Deleted `OTHER_TREE` findings on anchor head still block
        # (`history_findings_off`):
        anchor_diff_tree_finding = gate2_comment(
            comment_id=11,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=OTHER_TREE,
            verdict="findings",
            findings=[
                {
                    "severity": "P1",
                    "path": "a",
                    "line": 1,
                    "summary": "f",
                }
            ],
            created_at="2026-11-23T00:11:00Z",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [anchor_diff_tree_finding],
                deleted_through=11,
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # History non-finding failure on anchor head (`OTHER_BASE`) blocks:
        cr_earlier = gate2_review(
            review_id=15,
            head_sha=ANCHOR_HEAD,
            base_sha=OTHER_BASE,
            tree_sha=TREE,
            state="CHANGES_REQUESTED",
            submitted_at="2026-11-23T00:30:00Z",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [],
                reviews=[cr_earlier, clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # Deleted earlier non-finding comment does NOT block carry-forward
        # (`deleted_through=15`):
        cmt_cr_earlier = gate2_comment(
            comment_id=15,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            reviewer_family="claude",
            author_family="claude",
            created_at="2026-11-23T00:30:00Z",
        )
        self.assertEqual(
            mod.review_result(
                NEW_HEAD,
                [cmt_cr_earlier],
                deleted_through=15,
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # Deleted latest clean comment (`id=30 <= deleted_through=30`) MUST NOT
        # carry forward or fall back to older clean `id=20`
        # (`latest_excludes_tombstoned` & `earliest_anchor` &
        # `latest_tomb_check_off`):
        cmt_clean_latest = gate2_comment(
            comment_id=30,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            identity_key=ANCHOR_IK,
            created_at="2026-11-23T02:00:00Z",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [cmt_clean_latest],
                deleted_through=30,
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # Earliest clean + later findings (`earliest_anchor`):
        finding_latest = gate2_comment(
            comment_id=30,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            verdict="findings",
            findings=[
                {
                    "severity": "P1",
                    "path": "a",
                    "line": 1,
                    "summary": "f",
                }
            ],
            created_at="2026-11-23T02:00:00Z",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [finding_latest],
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # Legacy Codex blocking summary on unrelated head blocks carry-forward
        # (`history_codex_off`):
        bad_codex = summary(
            head="9" * 40,
            status="completed",
            has_any_findings=True,
            has_unresolved_findings=True,
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [bad_codex],
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )

        # 5. Isolated direct unit mock for `codex_gate_off`:
        with (
            patch.object(
                mod,
                "review_codex_result",
                side_effect=[
                    mod.Result("failure", "mock codex failure"),
                    mod.Result("pending", "anchor codex clear"),
                ],
            ),
            patch.object(
                mod, "_carry_forward_blocked_by_history", return_value=False
            ),
        ):
            res_codex_off = mod.review_result(
                NEW_HEAD,
                [],
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            )
            self.assertNotEqual(res_codex_off.state, "success")

        # 6. `reconcile` wiring (`reconcile_unwired`):
        class ReconcileCarryGH(FakeGitHub):
            def verify_rebase_carry_forward(
                self, o_head, o_base, o_tree, n_head, n_base, other_heads=()
            ):
                return ANCHOR_IK

        gh_rec = ReconcileCarryGH(
            [
                {
                    "number": 1,
                    "head": {"sha": NEW_HEAD},
                    "base": {"ref": "main", "sha": NEW_BASE},
                    "draft": False,
                }
            ],
            {1: []},
            reviews={1: [clean_anchor]},
            authorized_reviewers=AUTH_REVIEWERS,
            trees={NEW_HEAD: TREE, OLD_BASE: PARENT_TREE, NEW_BASE: "2" * 40},
            parents={NEW_HEAD: [NEW_BASE]},
            messages={NEW_HEAD: MSG},
        )
        with patch("sys.stdout"):
            res_rec = mod.reconcile(gh_rec, publish=False)
        self.assertEqual(res_rec[NEW_HEAD].state, "success")

    def test_carry_forward_single_guard_mutations_100_percent_killed(
        self,
    ) -> None:
        source = Path(codex_review.__file__).read_text(encoding="utf-8")
        # Baseline unmutated source must pass the entire probe suite cleanly.
        base_name, base_mod = _compile_mutant(source, "baseline")
        try:
            self._run_carry_forward_probe_suite(base_mod)
        finally:
            sys.modules.pop(base_name, None)

        survivors = []
        for idx, (name, (needle, replacement)) in enumerate(
            CF_MUTANTS.items()
        ):
            count = source.count(needle)
            self.assertEqual(
                count, 1, f"{name}: expected unique anchor, got {count}"
            )
            mutated = source.replace(needle, replacement, 1)
            mod_name, mod = _compile_mutant(mutated, f"{idx}_{name}")
            killed = False
            try:
                self._run_carry_forward_probe_suite(mod)
            except AssertionError:
                killed = True
            finally:
                sys.modules.pop(mod_name, None)
            if not killed:
                survivors.append(name)

        self.assertEqual(survivors, [], f"surviving mutants: {survivors}")


if __name__ == "__main__":
    unittest.main()
