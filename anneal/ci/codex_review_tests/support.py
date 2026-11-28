# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Shared constants, payload builders, and the in-memory `FakeGitHub`
for the `codex_review` tests."""

import copy
import hashlib
import io
import json
from pathlib import Path
import unittest
from unittest.mock import patch
from urllib.error import HTTPError

from codex_review import (
    BOT_ID, BOT_LOGIN, CONTEXT, PUBLISHER_LOGIN, GitHub, Result, combine_results,
    STATE_ANCHOR, base_drift_allows_carry_forward, diff_file_modes,
    parse_gate2_payload, rebase_only_patch_equivalent, reconcile,
    review_result,
)


HEAD = "a" * 40
OTHER_HEAD = "b" * 40
BASE = "c" * 40
OTHER_BASE = "d" * 40
TREE = "e" * 40
OTHER_TREE = "f" * 40


def gate2_payload(base_sha=BASE, head_sha=HEAD, tree_sha=TREE,
                  reviewer_family="gemini", author_family="claude",
                  verdict="clean", findings=None, **extra):
    payload = {
        "base_sha": base_sha,
        "head_sha": head_sha,
        "tree_sha": tree_sha,
        "reviewer_family": reviewer_family,
        "author_family": author_family,
        "verdict": verdict,
        "findings": [] if findings is None else findings,
    }
    payload.update(extra)
    return payload


def gate2_review(review_id=20, head_sha=HEAD, submitted_at="2026-11-23T01:00:00Z",
                 state="COMMENTED", author_association="MEMBER",
                 login="reviewer", user_id=42, commit_id=...,
                 prefix="Automated Gate 2 review completed.\n", **payload_overrides):
    payload = gate2_payload(head_sha=head_sha, **payload_overrides)
    return {
        "id": review_id,
        "state": state,
        "commit_id": payload["head_sha"] if commit_id is ... else commit_id,
        "submitted_at": submitted_at,
        "author_association": author_association,
        "user": {"id": user_id, "login": login, "type": "User"},
        "body": f"{prefix}<!-- anneal-gate2-review:v1 {json.dumps(payload)} -->",
    }


def gate2_comment(comment_id=30, head_sha=HEAD, created_at="2026-11-23T01:00:00Z",
                  updated_at=None, author_association="MEMBER",
                  login="reviewer", user_id=42, **payload_overrides):
    payload = gate2_payload(head_sha=head_sha, **payload_overrides)
    comment = {
        "id": comment_id,
        "created_at": created_at,
        "author_association": author_association,
        "user": {"id": user_id, "login": login, "type": "User"},
        "body": f"Gate 2 review.\n<!-- anneal-gate2-review:v1 {json.dumps(payload)} -->",
    }
    if updated_at is not None:
        comment["updated_at"] = updated_at
    return comment


def summary(head=HEAD, created_at="2026-11-08T10:00:00Z",
            completed_at="2026-11-08T10:01:00Z", **changes):
    # The wire shape comes from actual managed-review summaries, including the
    # independent security verdict that must not substitute for Code Review.
    review = {"commit_sha": head, "status": "completed",
              "has_any_findings": False, "has_unresolved_findings": False}
    review.update(changes)
    return {
        "id": 10,
        "created_at": created_at,
        "user": {"id": BOT_ID, "login": BOT_LOGIN, "type": "Bot"},
        "body": "<!-- codex-pull-request-review-summary -->\n"
                "<!-- codex-review-state:v1 " + json.dumps({
                    "code_review": review,
                    "security_review": {"status": "completed",
                                        "has_any_findings": False},
                }) + " -->\nCodex Review Summary: Completed\n"
                '| 📝 **Code Review** | ✅ **Completed** <relative-time datetime="'
                + completed_at + '">completed</relative-time> | head | PR opened |',
    }


def pull(number=1, head=HEAD, base="main"):
    return {"number": number, "head": {"sha": head},
            "base": {"ref": base, "sha": BASE}, "draft": False}


class FakeGitHub:
    def __init__(self, initial, comments, final=None, changed_comments=None,
                 deleted=None, queues=None, bases=None,
                 reviews=None, changed_reviews=None, trees=None,
                 authorized_reviewers=None, parents=None, messages=None):
        self.snapshots = [initial, initial if final is None else final]
        self.bodies = comments
        self.review_bodies = (
            {p["number"]: [] for p in initial} if reviews is None else reviews
        )
        self.writes = []
        self.comment_reads = set()
        self.review_reads = set()
        self.changed_comments = changed_comments or {}
        self.changed_reviews = changed_reviews or {}
        self.deleted = deleted or {}
        self.queues = queues or {}
        self.bases = {p["number"]: None for p in initial} if bases is None else bases
        self.trees = {HEAD: TREE, OTHER_HEAD: OTHER_TREE} if trees is None else trees
        self.authorized_reviewers = authorized_reviewers
        self.parents = {} if parents is None else parents
        self.messages = {} if messages is None else messages

    def pulls(self):
        return copy.deepcopy(self.snapshots.pop(0))

    def comments(self, number):
        body = (self.changed_comments.get(number, self.bodies[number])
                if number in self.comment_reads else self.bodies[number])
        self.comment_reads.add(number)
        if isinstance(body, Exception):
            raise body
        return body

    def reviews(self, number):
        body = (self.changed_reviews.get(number, self.review_bodies.get(number, []))
                if number in self.review_reads else self.review_bodies.get(number, []))
        self.review_reads.add(number)
        if isinstance(body, Exception):
            raise body
        return body

    def commit_tree(self, sha):
        val = self.trees[sha]
        if isinstance(val, Exception):
            raise val
        return val

    def commit_info(self, sha):
        tree_sha = self.commit_tree(sha)
        return {
            "sha": sha,
            "tree_sha": tree_sha,
            "parents": list(self.parents.get(sha, [])),
            "message": self.messages.get(sha, ""),
        }

    def commit_identity(self, head, base_sha):
        tree_sha = self.commit_tree(head)
        if head in self.parents and head in self.messages and base_sha in self.trees:
            if len(self.parents[head]) == 1 and self.parents[head][0] == base_sha:
                parent_tree = self.commit_tree(base_sha)
                msg_sha256 = hashlib.sha256(
                    self.messages[head].encode("utf-8")
                ).hexdigest()
                return tree_sha, f"one:{parent_tree}:{tree_sha}:{msg_sha256}"
        return tree_sha, f"multi:{base_sha}:{head}"

    def deleted_summaries(self):
        return self.deleted

    def queue_groups(self):
        return self.queues

    def base_changes(self):
        return self.bases

    def publish(self, head, result):
        self.writes.append((head, result))
