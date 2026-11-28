# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Gate 2 cross-family tests for reviewer families, exact commit binding,
freshness, review states, payload consistency, authorization, and
anti-downgrade retries."""

from .support import (
    BASE,
    gate2_comment,
    gate2_review,
    HEAD,
    OTHER_BASE,
    OTHER_HEAD,
    OTHER_TREE,
    review_result,
    TREE,
)


class Gate2BindingTests:
    """Part of `Gate2CrossFamilyTests`."""

    def test_clean_cross_family_comment_review_and_comment_pass(self):
        for reviewer, author in [
            ("gemini", "claude"),
            ("claude", "gemini"),
            ("openai", "claude"),
            ("claude", "human"),
            ("deepseek", "qwen"),
        ]:
            with self.subTest(reviewer=reviewer, author=author):
                rev = gate2_review(reviewer_family=reviewer, author_family=author)
                res = review_result(
                    HEAD, [], reviews=[rev], base_sha=BASE, tree_sha=TREE,
                )
                self.assertEqual(res.state, "success")
        # Issue comment with valid authorization and optional identity fields
        # also passes cleanly.
        cmt = gate2_comment(
            parent_tree="1" * 40,
            commit_msg_sha256="2" * 64,
            reviewed_at="2026-11-23T01:00:00Z",
        )
        res = review_result(HEAD, [cmt], base_sha=BASE, tree_sha=TREE)
        self.assertEqual(res.state, "success")

    def test_same_family_and_invalid_family_tokens_fail_closed(self):
        same_family_pairs = [
            ("claude", "claude"),
            ("Claude", "claude"),
            ("claude-opus", "claude"),
            ("anthropic", "claude-sonnet"),
            ("gemini-pro", "gemini"),
            ("google-gemini", "gemini-flash"),
            ("openai", "gpt-4o"),
            ("codex", "openai"),
            ("o3-pro", "chatgpt"),
        ]
        for reviewer, author in same_family_pairs:
            with self.subTest(reviewer=reviewer, author=author):
                rev = gate2_review(reviewer_family=reviewer, author_family=author)
                res = review_result(
                    HEAD, [], reviews=[rev], base_sha=BASE, tree_sha=TREE,
                )
                self.assertEqual(res.state, "failure")

        for bad_reviewer in ["", " ", "unknown", "none", "null", "n/a", "self", "human"]:
            with self.subTest(bad_reviewer=bad_reviewer):
                rev = gate2_review(reviewer_family=bad_reviewer, author_family="claude")
                res = review_result(
                    HEAD, [], reviews=[rev], base_sha=BASE, tree_sha=TREE,
                )
                self.assertEqual(res.state, "failure")

        for bad_author in ["", " ", "unknown", "none", "null", "n/a"]:
            with self.subTest(bad_author=bad_author):
                rev = gate2_review(reviewer_family="gemini", author_family=bad_author)
                res = review_result(
                    HEAD, [], reviews=[rev], base_sha=BASE, tree_sha=TREE,
                )
                self.assertEqual(res.state, "failure")

    def test_exact_base_head_tree_and_commit_id_binding(self):
        # Wrong head waits; wrong tree fails; wrong base waits.
        wrong_head = gate2_review(head_sha=OTHER_HEAD)
        self.assertEqual(
            review_result(HEAD, [], reviews=[wrong_head], base_sha=BASE, tree_sha=TREE).state,
            "pending",
        )
        wrong_tree = gate2_review(tree_sha=OTHER_TREE)
        self.assertEqual(
            review_result(HEAD, [], reviews=[wrong_tree], base_sha=BASE, tree_sha=TREE).state,
            "failure",
        )
        wrong_base = gate2_review(base_sha=OTHER_BASE)
        self.assertEqual(
            review_result(HEAD, [], reviews=[wrong_base], base_sha=BASE, tree_sha=TREE).state,
            "pending",
        )
        mismatched_commit_id = gate2_review(commit_id=OTHER_HEAD)
        self.assertEqual(
            review_result(HEAD, [], reviews=[mismatched_commit_id], base_sha=BASE, tree_sha=TREE).state,
            "failure",
        )
        # Missing base_sha or tree_sha in caller fails closed.
        clean_rev = gate2_review()
        self.assertEqual(
            review_result(HEAD, [], reviews=[clean_rev], base_sha=None, tree_sha=TREE).state,
            "failure",
        )
        self.assertEqual(
            review_result(HEAD, [], reviews=[clean_rev], base_sha=BASE, tree_sha=None).state,
            "failure",
        )

    def test_base_change_freshness_ignores_comment_updated_at(self):
        changed = "2026-11-23T02:00:00Z"
        stale_cmt = gate2_comment(
            created_at="2026-11-23T01:00:00Z",
            updated_at="2026-11-23T03:00:00Z",
        )
        self.assertEqual(
            review_result(
                HEAD, [stale_cmt], base_changed_at=changed, base_sha=BASE, tree_sha=TREE,
            ).state,
            "pending",
        )
        stale_rev = gate2_review(submitted_at="2026-11-23T02:00:00Z")
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[stale_rev], base_changed_at=changed,
                base_sha=BASE, tree_sha=TREE,
            ).state,
            "pending",
        )
        fresh_rev = gate2_review(submitted_at="2026-11-23T02:00:01Z")
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[fresh_rev], base_changed_at=changed,
                base_sha=BASE, tree_sha=TREE,
            ).state,
            "success",
        )

    def test_gate5_approve_separation_and_review_states(self):
        # Gate 2 marker attached to an APPROVED review must fail closed.
        approved_gate2 = gate2_review(state="APPROVED")
        self.assertEqual(
            review_result(HEAD, [], reviews=[approved_gate2], base_sha=BASE, tree_sha=TREE).state,
            "failure",
        )
        # Ordinary human APPROVE without Gate 2 marker does not satisfy or break
        # Gate 2.
        human_approve = {
            "id": 99,
            "state": "APPROVED",
            "commit_id": HEAD,
            "submitted_at": "2026-11-23T01:05:00Z",
            "author_association": "OWNER",
            "user": {"id": 7, "login": "maintainer", "type": "User"},
            "body": "LGTM, Gate 5 approved.",
        }
        self.assertEqual(
            review_result(HEAD, [], reviews=[human_approve], base_sha=BASE, tree_sha=TREE).state,
            "pending",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[gate2_review(), human_approve],
                base_sha=BASE, tree_sha=TREE,
            ).state,
            "success",
        )
        for pending_state in ("PENDING", "DISMISSED"):
            rev = gate2_review(state=pending_state)
            self.assertEqual(
                review_result(HEAD, [], reviews=[rev], base_sha=BASE, tree_sha=TREE).state,
                "pending",
            )
        changes_req = gate2_review(state="CHANGES_REQUESTED")
        self.assertEqual(
            review_result(HEAD, [], reviews=[changes_req], base_sha=BASE, tree_sha=TREE).state,
            "failure",
        )

    def test_verdict_findings_consistency_and_malformed_payloads(self):
        finding = {"severity": "P1", "path": "anneal/ci/codex_review.py", "line": 10, "summary": "Bug"}
        self.assertEqual(
            review_result(
                HEAD, [],
                reviews=[gate2_review(verdict="findings", findings=[finding])],
                base_sha=BASE, tree_sha=TREE,
            ).state,
            "failure",
        )
        self.assertEqual(
            review_result(
                HEAD, [],
                reviews=[gate2_review(verdict="incomplete", findings=[])],
                base_sha=BASE, tree_sha=TREE,
            ).state,
            "pending",
        )
        # Contradictions and malformed payloads fail closed.
        bad_reviews = [
            gate2_review(verdict="clean", findings=[finding]),
            gate2_review(verdict="findings", findings=[]),
            gate2_review(verdict="incomplete", findings=[finding]),
            gate2_review(verdict="approve", findings=[]),
            gate2_review(findings=[{"severity": "HIGH", "summary": "Bad severity"}]),
            gate2_review(findings=[{"severity": "P1", "summary": ""}]),
            gate2_review(findings=[{"severity": "P1", "summary": "Bad line", "line": True}]),
            gate2_review(findings=[{"severity": "P1", "summary": "Bad line", "line": 0}]),
            gate2_review(unexpected_field=True),
            gate2_review(parent_tree="not-a-sha"),
            gate2_review(commit_msg_sha256="short"),
            gate2_review(submitted_at=None),
        ]
        for rev in bad_reviews:
            with self.subTest(rev=rev["body"]):
                self.assertEqual(
                    review_result(HEAD, [], reviews=[rev], base_sha=BASE, tree_sha=TREE).state,
                    "failure",
                )
        # Duplicate JSON keys, duplicate markers, and unsupported versions fail
        # closed.
        clean_body = gate2_review()["body"]
        for bad_body in [
            clean_body.replace("review:v1", "review:v2"),
            clean_body.replace('"verdict": "clean"', '"verdict": "clean", "verdict": "findings"'),
            clean_body + "\n" + clean_body,
            "<!-- anneal-gate2-review:v1 [] -->",
        ]:
            rev = gate2_review()
            rev["body"] = bad_body
            with self.subTest(bad_body=bad_body):
                self.assertEqual(
                    review_result(HEAD, [], reviews=[rev], base_sha=BASE, tree_sha=TREE).state,
                    "failure",
                )

    def test_authorization_and_explicit_allowlist(self):
        for assoc in ("NONE", "CONTRIBUTOR", "FIRST_TIME_CONTRIBUTOR", None):
            rev = gate2_review(author_association=assoc, login="outsider", user_id=999)
            self.assertEqual(
                review_result(HEAD, [], reviews=[rev], base_sha=BASE, tree_sha=TREE).state,
                "pending",
            )
        bot_rev = gate2_review(author_association="NONE", login="anneal-gate2[bot]", user_id=555)
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[bot_rev], base_sha=BASE, tree_sha=TREE,
                authorized_reviewers={"anneal-gate2[bot]"},
            ).state,
            "success",
        )
        member_rev = gate2_review(author_association="MEMBER", login="someone", user_id=123)
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[member_rev], base_sha=BASE, tree_sha=TREE,
                authorized_reviewers={"anneal-gate2[bot]"},
            ).state,
            "pending",
        )

    def test_anti_downgrade_retry_and_separate_id_spaces(self):
        finding = {"severity": "P1", "summary": "Soundness gap"}
        earlier_findings = gate2_review(
            review_id=10, submitted_at="2026-11-23T01:00:00Z",
            verdict="findings", findings=[finding],
        )
        later_clean = gate2_review(
            review_id=11, submitted_at="2026-11-23T01:05:00Z",
            verdict="clean", findings=[],
        )
        # Later silent clean review on the exact same identity does not clear
        # prior findings.
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[earlier_findings, later_clean],
                base_sha=BASE, tree_sha=TREE,
            ).state,
            "failure",
        )
        # Prior incomplete (0 findings) followed by clean retry passes.
        earlier_incomplete = gate2_review(
            review_id=10, submitted_at="2026-11-23T01:00:00Z",
            verdict="incomplete", findings=[],
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[earlier_incomplete, later_clean],
                base_sha=BASE, tree_sha=TREE,
            ).state,
            "success",
        )
        # Prior findings on an older head followed by clean review on new head
        # passes.
        old_head_findings = gate2_review(
            review_id=10, head_sha=OTHER_HEAD, tree_sha=OTHER_TREE,
            submitted_at="2026-11-23T01:00:00Z",
            verdict="findings", findings=[finding],
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[old_head_findings, later_clean],
                base_sha=BASE, tree_sha=TREE,
            ).state,
            "success",
        )
        # Issue comment deleted_through never blocks a PR review ID from the
        # separate GitHub review ID sequence, while blocking older issue
        # comments.
        small_id_review = gate2_review(review_id=5)
        self.assertEqual(
            review_result(
                HEAD, [], deleted_through=9999999999,
                reviews=[small_id_review], base_sha=BASE, tree_sha=TREE,
            ).state,
            "success",
        )
        deleted_cmt = gate2_comment(comment_id=50)
        self.assertEqual(
            review_result(
                HEAD, [deleted_cmt], deleted_through=50,
                base_sha=BASE, tree_sha=TREE,
            ).state,
            "pending",
        )
        # An incomplete retry after a finding on the same identity keeps
        # failure.
        later_incomplete = gate2_review(
            review_id=12, submitted_at="2026-11-23T01:06:00Z",
            verdict="incomplete", findings=[],
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[earlier_findings, later_incomplete],
                base_sha=BASE, tree_sha=TREE,
            ).state,
            "failure",
        )
