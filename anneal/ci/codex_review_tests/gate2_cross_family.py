# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`codex_review` tests for cross-family Gate 2 review results."""

from .support import (
    BASE,
    FakeGitHub,
    gate2_comment,
    gate2_review,
    GitHub,
    hashlib,
    HEAD,
    io,
    OTHER_BASE,
    OTHER_HEAD,
    OTHER_TREE,
    parse_gate2_payload,
    patch,
    pull,
    reconcile,
    Result,
    review_result,
    summary,
    TREE,
    unittest,
)


class Gate2CrossFamilyTests(unittest.TestCase):
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

    def test_coexistence_with_legacy_codex_summaries(self):
        clean_gate2 = gate2_review()
        connector_error = {
            "id": 10,
            "created_at": "2026-11-08T10:00:00Z",
            "user": dict(summary()["user"]),
            "body": (
                "<!-- codex-pull-request-review-summary -->\n"
                "To use Codex here, create a Codex account and connect to github."
            ),
        }
        malformed_codex = {
            "id": 10,
            "created_at": "2026-11-08T10:00:00Z",
            "user": dict(summary()["user"]),
            "body": (
                "<!-- codex-pull-request-review-summary -->\n"
                "<!-- codex-review-state:v1 [] -->"
            ),
        }
        # (a) Authentic cross-family Gate 2 success on current identity is
        # authoritative over legacy Codex failures, findings, and errors.
        for label, codex_cmt in (
            ("silent_fail", summary(
                status="failed", has_any_findings=True, has_unresolved_findings=True,
            )),
            ("completed_findings", summary(
                status="completed", has_any_findings=True, has_unresolved_findings=True,
            )),
            ("connector_error", connector_error),
            ("malformed_state", malformed_codex),
            ("in_progress", summary(status="running")),
        ):
            with self.subTest(gate2_wins_over_codex=label):
                self.assertEqual(
                    review_result(
                        HEAD, [codex_cmt], reviews=[clean_gate2],
                        base_sha=BASE, tree_sha=TREE,
                    ),
                    Result(
                        "success",
                        "Independent cross-family Gate 2 review passed (gemini)",
                    ),
                )

        # (b) Authentic Gate 2 failure on current identity wins over legacy
        # Codex success.
        finding = {"severity": "P1", "summary": "Soundness defect"}
        for label, failing_gate2 in (
            ("findings", gate2_review(verdict="findings", findings=[finding])),
            ("changes_requested", gate2_review(state="CHANGES_REQUESTED")),
            ("approved", gate2_review(state="APPROVED")),
            ("same_family", gate2_review(
                reviewer_family="claude", author_family="claude",
            )),
            ("wrong_tree", gate2_review(tree_sha=OTHER_TREE)),
            ("wrong_commit_id", gate2_review(commit_id=OTHER_HEAD)),
        ):
            with self.subTest(gate2_failure_wins=label):
                self.assertEqual(
                    review_result(
                        HEAD, [summary()], reviews=[failing_gate2],
                        base_sha=BASE, tree_sha=TREE,
                    ).state,
                    "failure",
                )

        # (d) Without an authentic Gate 2 review covering the current identity,
        # legacy Codex fallback behavior is preserved.
        old_gate2 = gate2_review(head_sha=OTHER_HEAD, tree_sha=OTHER_TREE)
        for g2_list in ([], [old_gate2]):
            self.assertEqual(
                review_result(
                    HEAD, [summary()], reviews=g2_list,
                    base_sha=BASE, tree_sha=TREE,
                ).state,
                "success",
            )
            self.assertEqual(
                review_result(
                    HEAD, [summary(has_any_findings=True, has_unresolved_findings=True)],
                    reviews=g2_list, base_sha=BASE, tree_sha=TREE,
                ).state,
                "failure",
            )
            self.assertEqual(
                review_result(
                    HEAD, [connector_error], reviews=g2_list,
                    base_sha=BASE, tree_sha=TREE,
                ).state,
                "failure",
            )
            self.assertEqual(
                review_result(
                    HEAD, [summary(status="running")], reviews=g2_list,
                    base_sha=BASE, tree_sha=TREE,
                ).state,
                "pending",
            )

        # (e) Unauthenticated or malformed Gate 2 markers fail closed and never
        # override legacy Codex failures (or pass via legacy Codex success).
        codex_finding = summary(has_any_findings=True, has_unresolved_findings=True)
        for assoc in ("NONE", "CONTRIBUTOR", "FIRST_TIME_CONTRIBUTOR", None):
            unauth_rev = gate2_review(
                author_association=assoc, login="outsider", user_id=999,
            )
            unauth_cmt = gate2_comment(
                comment_id=30, author_association=assoc,
                login="outsider", user_id=999,
            )
            with self.subTest(unauthenticated_assoc=assoc):
                self.assertEqual(
                    review_result(
                        HEAD, [codex_finding], reviews=[unauth_rev],
                        base_sha=BASE, tree_sha=TREE,
                    ),
                    Result("failure", "Codex findings remain or the verdict is unknown"),
                )
                self.assertEqual(
                    review_result(
                        HEAD, [codex_finding, unauth_cmt],
                        base_sha=BASE, tree_sha=TREE,
                    ),
                    Result("failure", "Codex findings remain or the verdict is unknown"),
                )
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[unauth_rev],
                        base_sha=BASE, tree_sha=TREE,
                    ).state,
                    "pending",
                )
        for bad_label, bad_body in (
            ("unsupported_v2", clean_gate2["body"].replace("review:v1", "review:v2")),
            ("duplicate_key", clean_gate2["body"].replace(
                '"verdict": "clean"', '"verdict": "clean", "verdict": "clean"',
            )),
            ("non_object", "<!-- anneal-gate2-review:v1 [] -->"),
            ("contradictory_clean", gate2_review(
                verdict="clean", findings=[finding],
            )["body"]),
            ("bad_identity_key", gate2_review(identity_key="one:bad")["body"]),
        ):
            bad_rev = {**clean_gate2, "body": bad_body}
            with self.subTest(malformed_gate2=bad_label):
                self.assertEqual(
                    review_result(
                        HEAD, [summary()], reviews=[bad_rev],
                        base_sha=BASE, tree_sha=TREE,
                    ).state,
                    "failure",
                )
                self.assertEqual(
                    review_result(
                        HEAD, [codex_finding], reviews=[bad_rev],
                        base_sha=BASE, tree_sha=TREE,
                    ).state,
                    "failure",
                )
        # Tombstoned clean Gate 2 comment cannot override a live Codex failure.
        tombstoned_g2 = gate2_comment(comment_id=10)
        later_codex_fail = summary(has_any_findings=True, has_unresolved_findings=True)
        later_codex_fail["id"] = 25
        self.assertEqual(
            review_result(
                HEAD, [tombstoned_g2, later_codex_fail],
                deleted_through=15, base_sha=BASE, tree_sha=TREE,
            ).state,
            "failure",
        )

        # Non-passing Gate 2 entries on HEAD (incomplete, dismissed, pending,
        # or base-stale) hold a clean Codex summary pending, without
        # downgrading a legacy Codex failure from failure to pending.
        incomplete_gate2 = gate2_review(verdict="incomplete", findings=[])
        self.assertEqual(
            review_result(
                HEAD, [summary()], reviews=[incomplete_gate2],
                base_sha=BASE, tree_sha=TREE,
            ).state,
            "pending",
        )
        stale_clean_gate2 = gate2_review(submitted_at="2026-11-23T01:00:00Z")
        fresh_codex_fail = summary(
            created_at="2026-11-23T03:00:00Z",
            completed_at="2026-11-23T03:01:00Z",
            has_any_findings=True,
            has_unresolved_findings=True,
        )
        for pending_label, pending_g2, changed_at in (
            ("incomplete", incomplete_gate2, None),
            ("dismissed", gate2_review(state="DISMISSED"), None),
            ("pending_state", gate2_review(state="PENDING"), None),
            ("base_stale", stale_clean_gate2, "2026-11-23T02:00:00Z"),
        ):
            with self.subTest(pending_gate2_preserves_codex_failure=pending_label):
                self.assertEqual(
                    review_result(
                        HEAD, [fresh_codex_fail], reviews=[pending_g2],
                        base_changed_at=changed_at,
                        base_sha=BASE, tree_sha=TREE,
                    ),
                    Result(
                        "failure",
                        "Codex findings remain or the verdict is unknown",
                    ),
                )

    def test_reconcile_and_transport_for_reviews_and_commit_tree(self):
        with patch("sys.stdout", new=io.StringIO()):
            # Reconcile passes via Gate 2 PR review even when Codex summary
            # failed.
            github = FakeGitHub(
                [pull()],
                {1: [summary(status="failed", has_any_findings=True)]},
                reviews={1: [gate2_review()]},
            )
            verdicts = reconcile(github, publish=True)
            self.assertEqual(verdicts[HEAD].state, "success")
            self.assertEqual(github.writes, [(HEAD, Result("success", "Clean Gate 2 review for all 1 PR(s)"))])

            # Review edits/dismissals during reconcile force pending recheck.
            github = FakeGitHub(
                [pull()],
                {1: []},
                reviews={1: [gate2_review()]},
                changed_reviews={1: [gate2_review(state="DISMISSED")]},
            )
            reconcile(github, publish=True)
            self.assertEqual(github.writes[0][1].state, "pending")

            # Tree lookup failure blocks that PR without dropping other PRs.
            github = FakeGitHub(
                [pull(1, HEAD), pull(2, OTHER_HEAD)],
                {1: [], 2: [summary(OTHER_HEAD)]},
                reviews={1: [gate2_review()], 2: []},
                trees={HEAD: OSError("commits API failed"), OTHER_HEAD: OTHER_TREE},
            )
            with self.assertRaisesRegex(RuntimeError, "commits API failed"):
                reconcile(github, publish=True)
            self.assertEqual(
                {head: result.state for head, result in github.writes},
                {HEAD: "failure", OTHER_HEAD: "success"},
            )

        # Transport: reviews(), commit_tree(), and Gate 2 deletion tombstones.
        gh = GitHub("google/zerocopy", "not-a-real-token", authorized_reviewers=["anneal-bot"])
        with patch.object(gh, "request", return_value=[{"id": 1}]) as req:
            self.assertEqual(gh.reviews(42), [{"id": 1}])
            self.assertEqual(req.call_args.args[0], "pulls/42/reviews?per_page=100&page=1")
        with patch.object(gh, "request", return_value={"sha": HEAD, "commit": {"tree": {"sha": TREE}}}):
            self.assertEqual(gh.commit_tree(HEAD), TREE)
        with patch.object(gh, "request", return_value={"sha": OTHER_HEAD, "commit": {"tree": {"sha": TREE}}}):
            with self.assertRaises(RuntimeError):
                gh.commit_tree(HEAD)
        event = {
            "action": "deleted",
            "issue": {"number": 42, "pull_request": True},
            "comment": gate2_comment(comment_id=77, login="anneal-bot", author_association="NONE"),
        }
        with patch.object(gh, "publish_status") as publish:
            gh.record_deletion(event)
            self.assertEqual(publish.call_args.args[1]["context"], "Codex summary deletion/42/77")

    def test_multi_seat_and_round_optional_fields(self):
        seats = [
            {
                "seat": "seat1",
                "family": "claude",
                "model_label": "claude-frontier-thinking",
                "role": "tcb_and_api_critic",
                "status": "completed",
                "verdict": "clean",
                "findings_count": 0,
                "latency_sec": 120,
            },
            {
                "seat": "seat2",
                "family": "gemini",
                "model_label": "gemini-frontier-thinking",
                "role": "tcb_and_spec_critic",
                "status": "completed",
                "verdict": "clean",
                "findings_count": 0,
                "latency_sec": 95,
            },
        ]
        # Full multi-seat clean payload (including nullable
        # parent_tree/commit_msg_sha256).
        rev = gate2_review(
            reviewer_family="gemini",
            author_family="claude",
            parent_tree=None,
            commit_msg_sha256=None,
            round=2,
            risk_tier="tier2_tcb",
            merge_base=BASE,
            identity_key=f"multi:{BASE}:{HEAD}",
            panel_seats=seats,
            prior_findings_status=[{"id": "G2-R1-01", "status": "fixed"}],
            coverage={"total_files": 3, "inspected": 3, "inapplicable": 0, "blocked": 0},
        )
        self.assertEqual(
            review_result(HEAD, [], reviews=[rev], base_sha=BASE, tree_sha=TREE).state,
            "success",
        )
        # Multi reviewer_family works with human author when panel_seats has
        # completed seat.
        multi_human = gate2_review(
            reviewer_family="multi",
            author_family="human",
            panel_seats=seats,
        )
        self.assertEqual(
            review_result(HEAD, [], reviews=[multi_human], base_sha=BASE, tree_sha=TREE).state,
            "success",
        )
        # Findings with multi-seat metadata validate cleanly and block.
        rich_finding = {
            "id": "G2-R1-01",
            "severity": "P1",
            "path": "anneal/ci/codex_review.py",
            "line": 10,
            "summary": "Missing guard",
            "fingerprint": "sha256:abcd",
            "surface": "Pass 2 ci/",
            "consensus_count": 2,
            "raised_by": ["seat1", "seat2"],
            "repro_status": "probe_confirmed",
        }
        findings_rev = gate2_review(
            verdict="findings",
            findings=[rich_finding],
            panel_seats=seats,
            round=1,
            risk_tier="tier2_tcb",
        )
        self.assertEqual(
            review_result(HEAD, [], reviews=[findings_rev], base_sha=BASE, tree_sha=TREE).state,
            "failure",
        )
        # Fail-closed rejections: multi without panel_seats, panel with no
        # completed cross-family seat, clean with still_open prior finding,
        # clean with blocked coverage, bad round/merge_base/finding metadata.
        same_only_seats = [
            {"seat": "seat1", "family": "claude", "status": "completed", "verdict": "clean"},
            {"seat": "seat2", "family": "gemini", "status": "failed", "verdict": "incomplete"},
        ]
        bad_cases = [
            gate2_review(reviewer_family="multi", author_family="claude"),
            gate2_review(reviewer_family="multi", author_family="claude", panel_seats=[]),
            gate2_review(reviewer_family="multi", author_family="claude", panel_seats=same_only_seats),
            gate2_review(reviewer_family="gemini", author_family="claude", panel_seats=same_only_seats),
            gate2_review(prior_findings_status=[{"id": "G2-R1-01", "status": "still_open"}]),
            gate2_review(coverage={"total_files": 2, "inspected": 1, "blocked": 1}),
            gate2_review(round=0),
            gate2_review(round=True),
            gate2_review(merge_base="bad-sha"),
            gate2_review(risk_tier=" "),
            gate2_review(verdict="findings", findings=[{**rich_finding, "consensus_count": 0}]),
            gate2_review(verdict="findings", findings=[{**rich_finding, "raised_by": [""]}]),
        ]
        for bad_rev in bad_cases:
            with self.subTest(body=bad_rev["body"]):
                self.assertEqual(
                    review_result(HEAD, [], reviews=[bad_rev], base_sha=BASE, tree_sha=TREE).state,
                    "failure",
                )

    def test_one_commit_identity_key_reuse_and_fail_closed_invalidation(self):
        parent_tree = "1" * 40
        other_parent_tree = "2" * 40
        msg = "Subject\n\nBody text."
        msg_hash = hashlib.sha256(msg.encode("utf-8")).hexdigest()
        other_msg_hash = hashlib.sha256(b"Changed subject").hexdigest()
        ik = f"one:{parent_tree}:{TREE}:{msg_hash}"
        verified_hist = {(OTHER_HEAD, BASE): (TREE, ik)}

        # Clean review on OLD_HEAD/BASE transfers to rebased HEAD/OTHER_BASE
        # when historical head/base identity is verified to match current ik.
        old_clean_rev = gate2_review(
            head_sha=OTHER_HEAD,
            base_sha=BASE,
            tree_sha=TREE,
            parent_tree=parent_tree,
            commit_msg_sha256=msg_hash,
            identity_key=ik,
            submitted_at="2026-11-23T01:00:00Z",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[old_clean_rev],
                base_sha=OTHER_BASE, tree_sha=TREE,
                base_changed_at="2026-11-23T02:00:00Z",
                identity_key=ik,
                historical_identities=verified_hist,
            ).state,
            "success",
        )
        old_clean_cmt = gate2_comment(
            head_sha=OTHER_HEAD,
            base_sha=BASE,
            tree_sha=TREE,
            parent_tree=parent_tree,
            commit_msg_sha256=msg_hash,
            identity_key=ik,
        )
        self.assertEqual(
            review_result(
                HEAD, [old_clean_cmt],
                base_sha=OTHER_BASE, tree_sha=TREE,
                identity_key=ik,
                historical_identities=verified_hist,
            ).state,
            "success",
        )

        # Cross-head reuse fails closed without verified historical head/base
        # identity, or if historical commit actually had a different identity.
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[old_clean_rev],
                base_sha=OTHER_BASE, tree_sha=TREE,
                identity_key=ik,
            ).state,
            "pending",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[old_clean_rev],
                base_sha=OTHER_BASE, tree_sha=TREE,
                identity_key=ik,
                historical_identities={
                    (OTHER_HEAD, BASE): (TREE, f"one:{parent_tree}:{TREE}:{other_msg_hash}"),
                },
            ).state,
            "pending",
        )

        # Any change to tree, commit message, parent_tree, or multi-commit
        # shape fails closed to pending (never reuses prior review).
        for changed_ik in (
            f"one:{parent_tree}:{OTHER_TREE}:{msg_hash}",
            f"one:{parent_tree}:{TREE}:{other_msg_hash}",
            f"one:{other_parent_tree}:{TREE}:{msg_hash}",
            f"multi:{OTHER_BASE}:{HEAD}",
            None,
        ):
            target_tree = OTHER_TREE if changed_ik == f"one:{parent_tree}:{OTHER_TREE}:{msg_hash}" else TREE
            with self.subTest(changed_ik=changed_ik):
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[old_clean_rev],
                        base_sha=OTHER_BASE, tree_sha=target_tree,
                        identity_key=changed_ik,
                        historical_identities=verified_hist,
                    ).state,
                    "pending",
                )

        # Legacy or custom v1 identity_key values remain valid on exact
        # head/base/tree, but never transfer across heads.
        legacy_rev = gate2_review(identity_key="custom:legacy-v1-key")
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[legacy_rev],
                base_sha=BASE, tree_sha=TREE, identity_key=ik,
            ).state,
            "success",
        )
        legacy_old = gate2_review(
            head_sha=OTHER_HEAD, base_sha=BASE,
            identity_key="custom:legacy-v1-key",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[legacy_old],
                base_sha=BASE, tree_sha=TREE, identity_key=ik,
                historical_identities={(OTHER_HEAD, BASE): (TREE, ik)},
            ).state,
            "pending",
        )

        # Malformed structured or self-contradictory identity_key fields fail
        # closed.
        bad_ik_reviews = [
            gate2_review(identity_key=" "),
            gate2_review(identity_key="one:not-a-valid-key"),
            gate2_review(identity_key=" one:bad"),
            gate2_review(identity_key="multi:bad"),
            gate2_review(identity_key=f"one:{parent_tree}:{OTHER_TREE}:{msg_hash}"),
            gate2_review(
                parent_tree=other_parent_tree,
                identity_key=ik,
            ),
            gate2_review(
                commit_msg_sha256=other_msg_hash,
                identity_key=ik,
            ),
            gate2_review(identity_key=f"multi:{OTHER_BASE}:{HEAD}"),
            gate2_review(identity_key=f"multi:{BASE}:{OTHER_HEAD}"),
        ]
        for bad_rev in bad_ik_reviews:
            for caller_ik in (ik, None):
                with self.subTest(bad_ik=bad_rev["body"], caller_ik=caller_ik):
                    self.assertEqual(
                        review_result(
                            HEAD, [], reviews=[bad_rev],
                            base_sha=BASE, tree_sha=TREE, identity_key=caller_ik,
                        ).state,
                        "failure",
                    )
        # parse_gate2_payload's own consistency checks reject these, with no
        # caller identity_key to mask a disabled check.
        for bad_rev, expected_msg in (
            (bad_ik_reviews[4], "identity_key tree_sha mismatch"),
            (bad_ik_reviews[5], "identity_key parent_tree mismatch"),
            (bad_ik_reviews[6], "identity_key commit_msg_sha256 mismatch"),
            (bad_ik_reviews[7], "identity_key base/head mismatch"),
            (bad_ik_reviews[8], "identity_key base/head mismatch"),
        ):
            with self.subTest(parser_only=bad_rev["body"]):
                with self.assertRaisesRegex(ValueError, expected_msg):
                    parse_gate2_payload(bad_rev["body"])
        # Contradictory identity_key on exact head/base fails closed.
        self.assertEqual(
            review_result(
                HEAD, [],
                reviews=[gate2_review(identity_key=ik)],
                base_sha=BASE, tree_sha=TREE,
                identity_key=f"one:{other_parent_tree}:{TREE}:{msg_hash}",
            ).state,
            "failure",
        )
        # Base retarget without rebase (unchanged head, changed base_sha) stays
        # pending rather than failing on identity_key mismatch.
        self.assertEqual(
            review_result(
                HEAD, [],
                reviews=[gate2_review(identity_key=f"multi:{BASE}:{HEAD}")],
                base_sha=OTHER_BASE, tree_sha=TREE,
                identity_key=f"multi:{OTHER_BASE}:{HEAD}",
            ).state,
            "pending",
        )
        # Payload claiming one: identity_key with stale merge_base != base_sha
        # cannot match across rebases.
        self.assertEqual(
            review_result(
                HEAD, [],
                reviews=[gate2_review(
                    head_sha=OTHER_HEAD,
                    base_sha=BASE,
                    merge_base=OTHER_BASE,
                    identity_key=ik,
                )],
                base_sha=OTHER_BASE, tree_sha=TREE,
                identity_key=ik,
                historical_identities=verified_hist,
            ).state,
            "pending",
        )

        # Anti-downgrade: findings on OLD_HEAD block NEW_HEAD with the same
        # identity_key, even if a clean review is posted on NEW_HEAD.
        finding = {"severity": "P1", "summary": "Soundness defect"}
        old_findings = gate2_review(
            review_id=10,
            head_sha=OTHER_HEAD,
            base_sha=BASE,
            tree_sha=TREE,
            identity_key=ik,
            submitted_at="2026-11-23T01:00:00Z",
            verdict="findings",
            findings=[finding],
        )
        new_clean = gate2_review(
            review_id=11,
            head_sha=HEAD,
            base_sha=OTHER_BASE,
            tree_sha=TREE,
            identity_key=ik,
            submitted_at="2026-11-23T02:00:00Z",
            verdict="clean",
            findings=[],
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[old_findings],
                base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                historical_identities=verified_hist,
            ).state,
            "failure",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[old_findings, new_clean],
                base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                historical_identities=verified_hist,
            ).state,
            "failure",
        )
        # Once the tree changes (new identity_key), a clean review passes.
        new_ik = f"one:{parent_tree}:{OTHER_TREE}:{msg_hash}"
        fixed_clean = gate2_review(
            review_id=12,
            head_sha=HEAD,
            base_sha=OTHER_BASE,
            tree_sha=OTHER_TREE,
            identity_key=new_ik,
            submitted_at="2026-11-23T03:00:00Z",
            verdict="clean",
            findings=[],
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[old_findings, fixed_clean],
                base_sha=OTHER_BASE, tree_sha=OTHER_TREE, identity_key=new_ik,
                historical_identities=verified_hist,
            ).state,
            "success",
        )
        # Incomplete review on NEW_HEAD supersedes clean review on OLD_HEAD.
        new_incomplete = gate2_review(
            review_id=13,
            head_sha=HEAD,
            base_sha=OTHER_BASE,
            tree_sha=TREE,
            identity_key=ik,
            submitted_at="2026-11-23T02:30:00Z",
            verdict="incomplete",
            findings=[],
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[old_clean_rev, new_incomplete],
                base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                historical_identities=verified_hist,
            ).state,
            "pending",
        )

    def test_reconcile_and_transport_identity_key(self):
        parent_tree = "1" * 40
        other_parent_tree = "2" * 40
        msg = "[anneal] Clean single commit"
        msg_trailing_nl = "[anneal] Clean single commit\n"
        msg_hash = hashlib.sha256(msg.encode("utf-8")).hexdigest()
        msg_nl_hash = hashlib.sha256(msg_trailing_nl.encode("utf-8")).hexdigest()
        ik = f"one:{parent_tree}:{TREE}:{msg_hash}"

        with patch("sys.stdout", new=io.StringIO()):
            # End-to-end reconcile reuses a clean review on OTHER_HEAD after a
            # squash-rebase onto OTHER_BASE only when OTHER_HEAD/BASE also
            # resolves to the same 1-commit identity on GitHub.
            pr1 = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": OTHER_BASE}, "draft": False}
            old_clean = gate2_review(
                head_sha=OTHER_HEAD,
                base_sha=BASE,
                tree_sha=TREE,
                parent_tree=parent_tree,
                commit_msg_sha256=msg_hash,
                identity_key=ik,
                submitted_at="2026-11-23T01:00:00Z",
            )
            github = FakeGitHub(
                [pr1],
                {1: []},
                reviews={1: [old_clean]},
                bases={1: "2026-11-23T02:00:00Z"},
                trees={HEAD: TREE, OTHER_HEAD: TREE, OTHER_BASE: parent_tree, BASE: parent_tree},
                parents={HEAD: [OTHER_BASE], OTHER_HEAD: [BASE]},
                messages={HEAD: msg, OTHER_HEAD: msg},
            )
            verdicts = reconcile(github, publish=True)
            self.assertEqual(verdicts[HEAD].state, "success")

            # Spoofed/miscomputed identity_key on historical OTHER_HEAD must not
            # transfer when GitHub shows OTHER_HEAD actually had a different
            # message or parent.
            github_mismatch = FakeGitHub(
                [pr1],
                {1: []},
                reviews={1: [old_clean]},
                bases={1: "2026-11-23T02:00:00Z"},
                trees={HEAD: TREE, OTHER_HEAD: TREE, OTHER_BASE: parent_tree, BASE: parent_tree},
                parents={HEAD: [OTHER_BASE], OTHER_HEAD: [BASE]},
                messages={HEAD: msg, OTHER_HEAD: msg_trailing_nl},
            )
            verdicts_mismatch = reconcile(github_mismatch, publish=True)
            self.assertEqual(verdicts_mismatch[HEAD].state, "pending")

            # Missing (404) historical commit denies cross-head reuse on clean
            # review without hiding a fresher review on HEAD, while failing
            # closed if an unverified 404/500 blocks a historical findings item.
            github_404 = FakeGitHub(
                [pr1],
                {1: []},
                reviews={1: [old_clean]},
                trees={
                    HEAD: TREE,
                    OTHER_HEAD: RuntimeError("GitHub GET: HTTP 404"),
                    OTHER_BASE: parent_tree,
                },
                parents={HEAD: [OTHER_BASE]},
                messages={HEAD: msg},
            )
            verdicts_404 = reconcile(github_404, publish=True)
            self.assertEqual(verdicts_404[HEAD].state, "pending")

            # A 404 on PR #1's historical item must not poison PR #2 when PR #2
            # uses that same (head, base) as its live head (no TypeError).
            pr2_same_missing = {
                "number": 2, "head": {"sha": OTHER_HEAD},
                "base": {"ref": "main", "sha": BASE}, "draft": False,
            }
            pr2_rev = gate2_review(
                review_id=19, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            )
            github_shared_404 = FakeGitHub(
                [pr1, pr2_same_missing],
                {1: [], 2: []},
                reviews={1: [old_clean], 2: [pr2_rev]},
                trees={
                    HEAD: TREE,
                    OTHER_HEAD: RuntimeError("GitHub GET: HTTP 404"),
                    OTHER_BASE: parent_tree,
                },
                parents={HEAD: [OTHER_BASE]},
                messages={HEAD: msg},
            )
            with self.assertRaises(RuntimeError):
                reconcile(github_shared_404, publish=True)
            written_shared = dict(github_shared_404.writes)
            self.assertEqual(written_shared[HEAD].state, "pending")
            self.assertEqual(written_shared[OTHER_HEAD].state, "failure")

            old_findings_404 = gate2_review(
                review_id=20,
                head_sha=OTHER_HEAD,
                base_sha=BASE,
                tree_sha=TREE,
                parent_tree=parent_tree,
                commit_msg_sha256=msg_hash,
                identity_key=ik,
                verdict="findings",
                findings=[{"severity": "P1", "summary": "Bug"}],
            )
            github_findings_404 = FakeGitHub(
                [pr1],
                {1: []},
                reviews={1: [old_findings_404]},
                trees={
                    HEAD: TREE,
                    OTHER_HEAD: RuntimeError("GitHub GET: HTTP 404"),
                    OTHER_BASE: parent_tree,
                },
                parents={HEAD: [OTHER_BASE]},
                messages={HEAD: msg},
            )
            with self.assertRaises(RuntimeError):
                reconcile(github_findings_404, publish=True)
            self.assertEqual(github_findings_404.writes[-1][1].state, "failure")

            # Legacy v1 identity_key remains accepted on exact head/base/tree.
            pr_legacy = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": BASE}, "draft": False}
            legacy_clean = gate2_review(
                head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                identity_key="legacy-v1-key",
            )
            github_legacy = FakeGitHub(
                [pr_legacy],
                {1: []},
                reviews={1: [legacy_clean]},
                trees={HEAD: TREE, BASE: parent_tree},
                parents={HEAD: [BASE]},
                messages={HEAD: msg},
            )
            self.assertEqual(reconcile(github_legacy, publish=True)[HEAD].state, "success")

            # Rebase onto a base commit with a different parent tree waits.
            github_changed_base = FakeGitHub(
                [pr1],
                {1: []},
                reviews={1: [old_clean]},
                trees={HEAD: TREE, OTHER_HEAD: TREE, OTHER_BASE: other_parent_tree, BASE: parent_tree},
                parents={HEAD: [OTHER_BASE], OTHER_HEAD: [BASE]},
                messages={HEAD: msg, OTHER_HEAD: msg},
            )
            verdicts_changed = reconcile(github_changed_base, publish=True)
            self.assertEqual(verdicts_changed[HEAD].state, "pending")

            # Multi-commit PR (parent != base) stays pending with same tree.
            github_multi = FakeGitHub(
                [pr1],
                {1: []},
                reviews={1: [old_clean]},
                trees={HEAD: TREE, OTHER_HEAD: TREE, OTHER_BASE: parent_tree, BASE: parent_tree},
                parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
                messages={HEAD: msg, OTHER_HEAD: msg},
            )
            verdicts_multi = reconcile(github_multi, publish=True)
            self.assertEqual(verdicts_multi[HEAD].state, "pending")

        # Transport: GitHub.commit_info and GitHub.commit_identity hash the
        # UTF-8 bytes of GitHub REST's `commit.message` verbatim (GitHub's
        # commits API omits the raw commit object's trailing newlines, so
        # local producers must hash that same canonical message).
        gh = GitHub("google/zerocopy", "not-a-real-token")
        head_resp = {
            "sha": HEAD,
            "commit": {"tree": {"sha": TREE}, "message": msg},
            "parents": [{"sha": BASE}],
        }
        head_nl_resp = {
            "sha": HEAD,
            "commit": {"tree": {"sha": TREE}, "message": msg_trailing_nl},
            "parents": [{"sha": BASE}],
        }
        base_resp = {"sha": BASE, "commit": {"tree": {"sha": parent_tree}}}
        with patch.object(gh, "request", side_effect=[head_resp, base_resp]):
            self.assertEqual(gh.commit_identity(HEAD, BASE), (TREE, ik))
        with patch.object(gh, "request", side_effect=[head_nl_resp, base_resp]):
            self.assertEqual(
                gh.commit_identity(HEAD, BASE),
                (TREE, f"one:{parent_tree}:{TREE}:{msg_nl_hash}"),
            )
        self.assertNotEqual(msg_hash, msg_nl_hash)
        merge_resp = {
            "sha": HEAD,
            "commit": {"tree": {"sha": TREE}, "message": msg},
            "parents": [{"sha": BASE}, {"sha": OTHER_HEAD}],
        }
        with patch.object(gh, "request", return_value=merge_resp):
            self.assertEqual(gh.commit_identity(HEAD, BASE), (TREE, f"multi:{BASE}:{HEAD}"))
        # A single parent other than base_sha (a multi-commit PR) is never a
        # one-commit identity, and GitHub is not asked for that parent's tree.
        other_parent_resp = {
            "sha": HEAD,
            "commit": {"tree": {"sha": TREE}, "message": msg},
            "parents": [{"sha": OTHER_BASE}],
        }
        with patch.object(gh, "request", side_effect=[other_parent_resp]) as req:
            self.assertEqual(gh.commit_identity(HEAD, BASE), (TREE, f"multi:{BASE}:{HEAD}"))
            self.assertEqual(req.call_count, 1)
        # Malformed parent SHAs and non-string messages fail closed.
        for bad_commit_payload in (
            {"sha": HEAD, "commit": {"tree": {"sha": TREE}, "message": msg},
             "parents": [{"sha": "not-a-sha"}]},
            {"sha": HEAD, "commit": {"tree": {"sha": TREE}, "message": msg},
             "parents": ["bad"]},
            {"sha": HEAD, "commit": {"tree": {"sha": TREE}, "message": None},
             "parents": [{"sha": BASE}]},
        ):
            with self.subTest(bad_commit_payload=bad_commit_payload):
                with patch.object(gh, "request", return_value=bad_commit_payload):
                    with self.assertRaises(RuntimeError):
                        gh.commit_info(HEAD)
        with self.assertRaises(ValueError):
            gh.commit_identity(HEAD, "bad-base")
        bad_commit = {"sha": HEAD, "commit": {"tree": {"sha": TREE}, "message": msg}, "parents": "bad"}
        with patch.object(gh, "request", return_value=bad_commit):
            with self.assertRaises(RuntimeError):
                gh.commit_info(HEAD)
        for bad_payload in (
            {"sha": HEAD, "commit": "bad"},
            {"sha": HEAD, "commit": {"tree": "bad"}},
        ):
            with self.subTest(bad_payload=bad_payload):
                with patch.object(gh, "request", return_value=bad_payload):
                    with self.assertRaises(RuntimeError):
                        gh.commit_info(HEAD)

    def test_gate2_antidowngrade_preserves_mismatched_malformed_and_legacy_findings(self):
        msg = "feat: add identity check\n\nBody"
        other_msg = "feat: fix wording\n\nBody"
        msg_hash = hashlib.sha256(msg.encode("utf-8")).hexdigest()
        parent_tree = "4" * 40
        other_parent_tree = "5" * 40
        ik = f"one:{parent_tree}:{TREE}:{msg_hash}"
        finding = {"severity": "P1", "summary": "Soundness gap"}

        later_clean_exact = gate2_review(
            review_id=20, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T02:00:00Z",
        )
        # Exact-head findings with mismatched structured key,
        # malformed one:/multi: key, or contradictory key still block a later
        # clean review on the exact commit.
        prior_exact_cases = [
            ("mismatched_structured", {"identity_key": f"one:{other_parent_tree}:{TREE}:{msg_hash}"}),
            ("malformed_one", {"identity_key": "one:not-a-valid-key"}),
            ("malformed_multi", {"identity_key": "multi:bad"}),
            ("whitespace_ik", {"identity_key": " "}),
            ("contradictory_parent_tree", {"parent_tree": other_parent_tree, "identity_key": ik}),
        ]
        for label, extra in prior_exact_cases:
            with self.subTest(case=label):
                prior_bad = gate2_review(
                    review_id=10, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                    verdict="findings", findings=[finding], **extra,
                )
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[prior_bad, later_clean_exact],
                        base_sha=BASE, tree_sha=TREE, identity_key=ik,
                    ).state,
                    "failure",
                )
        # A malformed prior clean review does not poison a newer clean one.
        prior_bad_clean = gate2_review(
            review_id=11, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key="one:not-a-valid-key",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[prior_bad_clean, later_clean_exact],
                base_sha=BASE, tree_sha=TREE, identity_key=ik,
            ).state,
            "success",
        )

        # Legacy (no identity_key or custom legacy key) findings on
        # OTHER_HEAD still block HEAD after squash-rebase onto OTHER_BASE or
        # no-op amend on BASE when historical commit identity matches.
        pr_rebased = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": OTHER_BASE}, "draft": False}
        pr_amended = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": BASE}, "draft": False}
        for label, extra in (("keyless", {}), ("legacy_key", {"identity_key": "legacy-v1"})):
            old_findings = gate2_review(
                review_id=30, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
                verdict="findings", findings=[finding], **extra,
            )
            clean_rebased = gate2_review(
                review_id=31, head_sha=HEAD, base_sha=OTHER_BASE, tree_sha=TREE,
                identity_key=ik, submitted_at="2026-11-23T02:00:00Z",
            )
            with self.subTest(mode="squash_rebase", label=label):
                gh_rebase = FakeGitHub(
                    [pr_rebased], {1: []},
                    reviews={1: [old_findings, clean_rebased]},
                    trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree, OTHER_BASE: parent_tree},
                    parents={HEAD: [OTHER_BASE], OTHER_HEAD: [BASE]},
                    messages={HEAD: msg, OTHER_HEAD: msg},
                )
                self.assertEqual(reconcile(gh_rebase, publish=True)[HEAD].state, "failure")

            clean_amended = gate2_review(
                review_id=32, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                submitted_at="2026-11-23T02:00:00Z",
            )
            with self.subTest(mode="noop_amend", label=label):
                gh_amend = FakeGitHub(
                    [pr_amended], {1: []},
                    reviews={1: [old_findings, clean_amended]},
                    trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree},
                    parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
                    messages={HEAD: msg, OTHER_HEAD: msg},
                )
                self.assertEqual(reconcile(gh_amend, publish=True)[HEAD].state, "failure")

        # Changing only the commit message while preserving the tree
        # keeps prior same-tree Gate 2 findings blocking (keyless and one:).
        for label, extra in (
            ("keyless", {}),
            ("one_key", {"identity_key": f"one:{parent_tree}:{TREE}:{hashlib.sha256(other_msg.encode('utf-8')).hexdigest()}"}),
        ):
            old_same_tree_findings = gate2_review(
                review_id=40, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
                verdict="findings", findings=[finding], **extra,
            )
            new_msg_clean = gate2_review(
                review_id=41, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                identity_key=ik, submitted_at="2026-11-23T02:00:00Z",
            )
            with self.subTest(msg_changed=label):
                gh_msg_changed = FakeGitHub(
                    [pr_amended], {1: []},
                    reviews={1: [old_same_tree_findings, new_msg_clean]},
                    trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree},
                    parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
                    messages={HEAD: msg, OTHER_HEAD: other_msg},
                )
                self.assertEqual(reconcile(gh_msg_changed, publish=True)[HEAD].state, "failure")

        # Spoofed same tree_sha in a prior OTHER_HEAD payload does not block
        # when GitHub confirms OTHER_HEAD actually had a different tree.
        spoofed_tree_findings = gate2_review(
            review_id=42, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            verdict="findings", findings=[finding],
        )
        new_msg_clean = gate2_review(
            review_id=41, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T02:00:00Z",
        )
        gh_spoofed_tree = FakeGitHub(
            [pr_amended], {1: []},
            reviews={1: [spoofed_tree_findings, new_msg_clean]},
            trees={HEAD: TREE, OTHER_HEAD: OTHER_TREE, BASE: parent_tree},
            parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
            messages={HEAD: msg, OTHER_HEAD: other_msg},
        )
        self.assertEqual(reconcile(gh_spoofed_tree, publish=True)[HEAD].state, "success")

        # Needed by gh_same_tree_404 below.
        old_keyless_findings = gate2_review(
            review_id=40, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            verdict="findings", findings=[finding],
        )

        # Changing the tree after a keyless finding also passes without needing
        # the superseded OTHER_HEAD commit to still exist in GitHub.
        old_tree_findings = gate2_review(
            review_id=50, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=OTHER_TREE,
            verdict="findings", findings=[finding],
        )
        gh_tree_changed_404 = FakeGitHub(
            [pr_amended], {1: []},
            reviews={1: [old_tree_findings, new_msg_clean]},
            trees={HEAD: TREE, OTHER_HEAD: RuntimeError("GitHub GET: HTTP 404"), BASE: parent_tree},
            parents={HEAD: [BASE]},
            messages={HEAD: msg},
        )
        self.assertEqual(reconcile(gh_tree_changed_404, publish=True)[HEAD].state, "success")

        # Missing (404) same-tree historical keyless findings fail closed.
        gh_same_tree_404 = FakeGitHub(
            [pr_amended], {1: []},
            reviews={1: [old_keyless_findings, new_msg_clean]},
            trees={HEAD: TREE, OTHER_HEAD: RuntimeError("GitHub GET: HTTP 404"), BASE: parent_tree},
            parents={HEAD: [BASE]},
            messages={HEAD: msg},
        )
        with self.assertRaises(RuntimeError):
            reconcile(gh_same_tree_404, publish=True)
        self.assertEqual(gh_same_tree_404.writes[-1][1].state, "failure")

        # Sole/latest keyless findings on OTHER_HEAD still block HEAD after
        # squash-rebase or no-op amend, even with a clean Codex summary on HEAD.
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[old_keyless_findings],
                base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                historical_identities={(OTHER_HEAD, BASE): (TREE, ik)},
            ).state,
            "failure",
        )
        self.assertEqual(
            review_result(
                HEAD, [summary()], reviews=[old_keyless_findings],
                base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                historical_identities={(OTHER_HEAD, BASE): (TREE, ik)},
            ).state,
            "failure",
        )
        gh_sole_finding_with_codex = FakeGitHub(
            [pr_rebased], {1: [summary()]},
            reviews={1: [old_keyless_findings]},
            trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree, OTHER_BASE: parent_tree},
            parents={HEAD: [OTHER_BASE], OTHER_HEAD: [BASE]},
            messages={HEAD: msg, OTHER_HEAD: msg},
        )
        self.assertEqual(
            reconcile(gh_sole_finding_with_codex, publish=True)[HEAD].state,
            "failure",
        )

    def test_gate2_antidowngrade_codex_merge_base_clean_poison_and_tombstone(self):
        msg = "feat: add identity check\n\nBody"
        other_msg = "feat: edit message\n\nBody"
        msg_hash = hashlib.sha256(msg.encode("utf-8")).hexdigest()
        parent_tree = "4" * 40
        other_parent_tree = "5" * 40
        ik = f"one:{parent_tree}:{TREE}:{msg_hash}"
        finding = {"severity": "P1", "summary": "Soundness defect"}

        # Exact-(HEAD, BASE, TREE) findings without matching one:
        # identity_key still block after a base_changed_at event on exact BASE.
        for label, extra in (
            ("keyless", {}),
            ("legacy_key", {"identity_key": "legacy-v1"}),
            ("malformed_one", {"identity_key": "one:bad"}),
            ("mismatched_one", {"identity_key": f"one:{other_parent_tree}:{TREE}:{msg_hash}"}),
        ):
            r_findings = gate2_review(
                review_id=10, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                submitted_at="2026-11-23T01:00:00Z",
                verdict="findings", findings=[finding], **extra,
            )
            r_clean_after = gate2_review(
                review_id=11, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
            )
            with self.subTest(exact_finding_without_key=label):
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[r_findings],
                        base_changed_at="2026-11-23T02:00:00Z",
                        base_sha=BASE, tree_sha=TREE, identity_key=ik,
                    ).state,
                    "failure",
                )
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[r_findings, r_clean_after],
                        base_changed_at="2026-11-23T02:00:00Z",
                        base_sha=BASE, tree_sha=TREE, identity_key=ik,
                    ).state,
                    "failure",
                )

        # Clean keyless exact-head review still turns pending after base change.
        stale_clean = gate2_review(
            review_id=12, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            submitted_at="2026-11-23T01:00:00Z",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[stale_clean],
                base_changed_at="2026-11-23T02:00:00Z",
                base_sha=BASE, tree_sha=TREE, identity_key=ik,
            ).state,
            "pending",
        )

        # Authentic cross-family Gate 2 clean verdicts covering HEAD's current
        # identity are authoritative over prior or running legacy Codex
        # summaries, while legacy Codex fallback still blocks same-tree
        # findings when no authentic Gate 2 review covers HEAD.
        codex_old_findings = summary(
            OTHER_HEAD, status="completed",
            has_any_findings=True, has_unresolved_findings=True,
        )
        clean_rebased_g2 = gate2_review(
            review_id=20, head_sha=HEAD, base_sha=OTHER_BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
        )
        clean_old_g2 = gate2_review(
            review_id=21, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T02:00:00Z",
        )
        pr_rebased = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": OTHER_BASE}, "draft": False}
        pr_amended = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": BASE}, "draft": False}
        for label, pr_obj, g2_rev in (
            ("squash_rebase_new_g2", pr_rebased, clean_rebased_g2),
            ("squash_rebase_reused_g2", pr_rebased, clean_old_g2),
            ("noop_amend", pr_amended, gate2_review(
                review_id=22, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
            )),
        ):
            with self.subTest(historical_codex_findings=label):
                gh = FakeGitHub(
                    [pr_obj], {1: [codex_old_findings]},
                    reviews={1: [g2_rev]},
                    trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree, OTHER_BASE: parent_tree},
                    parents={HEAD: [pr_obj["base"]["sha"]], OTHER_HEAD: [BASE]},
                    messages={HEAD: msg, OTHER_HEAD: msg},
                )
                self.assertEqual(reconcile(gh, publish=True)[HEAD].state, "success")

        codex_running_new = summary(HEAD, status="running")
        codex_running_new["id"] = 11
        gh_codex_running = FakeGitHub(
            [pr_rebased], {1: [codex_old_findings, codex_running_new]},
            reviews={1: [clean_rebased_g2]},
            trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree, OTHER_BASE: parent_tree},
            parents={HEAD: [OTHER_BASE], OTHER_HEAD: [BASE]},
            messages={HEAD: msg, OTHER_HEAD: msg},
        )
        self.assertEqual(reconcile(gh_codex_running, publish=True)[HEAD].state, "success")

        # Without an authentic Gate 2 review, a newer clean or running Codex
        # summary on HEAD does not mask an older completed-findings Codex
        # summary on HEAD or on a same-tree historical commit.
        codex_old_findings_head = summary(
            HEAD, has_any_findings=True, has_unresolved_findings=True,
        )
        codex_old_findings_head["id"] = 10
        codex_old_findings_hist = summary(
            OTHER_HEAD, has_any_findings=True, has_unresolved_findings=True,
        )
        codex_old_findings_hist["id"] = 10
        codex_clean_new = summary(
            HEAD, created_at="2026-11-08T11:00:00Z",
            completed_at="2026-11-08T11:01:00Z",
        )
        codex_clean_new["id"] = 11
        for label, cmts, hist_trees, expected in (
            ("clean_only", [codex_clean_new], None, "success"),
            ("older_findings_on_head",
             [codex_old_findings_head, codex_clean_new], None, "failure"),
            ("older_findings_same_tree",
             [codex_old_findings_hist, codex_clean_new],
             {OTHER_HEAD: TREE}, "failure"),
            ("older_findings_other_tree",
             [codex_old_findings_hist, codex_clean_new],
             {OTHER_HEAD: OTHER_TREE}, "success"),
        ):
            with self.subTest(codex_clean_after_findings=label):
                self.assertEqual(
                    review_result(
                        HEAD, cmts, tree_sha=TREE, historical_trees=hist_trees,
                    ).state,
                    expected,
                )

        # In legacy Codex fallback mode (no Gate 2 review), changing only the
        # commit message keeps historical same-tree Codex findings blocking,
        # while changing the tree or adding an authentic clean Gate 2 review
        # on HEAD passes.
        gh_codex_fallback_same_tree_msg = FakeGitHub(
            [pr_amended], {1: [codex_old_findings, codex_clean_new]},
            reviews={1: []},
            trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree},
            parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
            messages={HEAD: msg, OTHER_HEAD: other_msg},
        )
        self.assertEqual(
            reconcile(gh_codex_fallback_same_tree_msg, publish=True)[HEAD].state,
            "failure",
        )
        gh_codex_same_tree_msg = FakeGitHub(
            [pr_amended], {1: [codex_old_findings]},
            reviews={1: [gate2_review(
                review_id=23, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
            )]},
            trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree},
            parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
            messages={HEAD: msg, OTHER_HEAD: other_msg},
        )
        self.assertEqual(reconcile(gh_codex_same_tree_msg, publish=True)[HEAD].state, "success")
        gh_codex_changed_tree = FakeGitHub(
            [pr_amended], {1: [codex_old_findings, codex_clean_new]},
            reviews={1: []},
            trees={HEAD: TREE, OTHER_HEAD: OTHER_TREE, BASE: parent_tree},
            parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
            messages={HEAD: msg, OTHER_HEAD: msg},
        )
        self.assertEqual(reconcile(gh_codex_changed_tree, publish=True)[HEAD].state, "success")

        # A historical completed Codex commit that GitHub cannot resolve
        # (404/422) carries no tree claim, so like any other-tree finding it
        # does not block a clean Gate 2 review of the current identity; other
        # read errors (HTTP 500) still fail closed.
        for label, err, expected in (
            ("http_404", "GitHub GET: HTTP 404", "success"),
            ("http_422", "GitHub GET: HTTP 422", "success"),
            ("http_500", "GitHub GET: HTTP 500", "failure"),
        ):
            with self.subTest(codex_unresolvable=label):
                gh_codex_missing = FakeGitHub(
                    [pr_amended], {1: [codex_old_findings]},
                    reviews={1: [gate2_review(
                        review_id=24, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                        identity_key=ik,
                    )]},
                    trees={HEAD: TREE, OTHER_HEAD: RuntimeError(err), BASE: parent_tree},
                    parents={HEAD: [BASE]},
                    messages={HEAD: msg},
                )
                if expected == "failure":
                    with self.assertRaises(RuntimeError):
                        reconcile(gh_codex_missing, publish=True)
                    self.assertEqual(gh_codex_missing.writes[-1][1].state, "failure")
                else:
                    self.assertEqual(
                        reconcile(gh_codex_missing, publish=True)[HEAD].state,
                        expected,
                    )

        # Exact-head review with merge_base != base_sha fails closed
        # even when base_changed_at is None and identity_key matches.
        self.assertEqual(
            review_result(
                HEAD, [],
                reviews=[gate2_review(
                    head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                    merge_base=OTHER_BASE, identity_key=ik,
                )],
                base_sha=BASE, tree_sha=TREE, identity_key=ik,
            ).state,
            "failure",
        )

        # Prior clean review with valid-syntax mismatched structured
        # identity_key (or bad merge_base) does not poison a valid clean retry.
        for label, bad_clean_kwargs in (
            ("mismatched_one", {"identity_key": f"one:{other_parent_tree}:{TREE}:{msg_hash}"}),
            ("mismatched_multi", {"identity_key": f"multi:{BASE}:{HEAD}"}),
            ("bad_merge_base", {"identity_key": ik, "merge_base": OTHER_BASE}),
        ):
            bad_clean = gate2_review(
                review_id=30, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                submitted_at="2026-11-23T01:00:00Z", **bad_clean_kwargs,
            )
            good_clean = gate2_review(
                review_id=31, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                identity_key=ik, submitted_at="2026-11-23T02:00:00Z",
            )
            with self.subTest(bad_clean_no_poison=label):
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[bad_clean, good_clean],
                        base_sha=BASE, tree_sha=TREE, identity_key=ik,
                    ).state,
                    "success",
                )

        # deleted_through stops older comments (<= deleted_through)
        # from approving, skips historical lookups for still-present clean
        # comments <= deleted_through, and keeps live finding comments blocking.
        # The tombstoned comment carries the matching identity_key and its
        # commit raises an unswallowed HTTP 500, so any historical lookup for
        # it fails the PR instead of passing.
        tombstoned_clean_g2 = gate2_comment(
            comment_id=10, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, created_at="2026-11-23T01:00:00Z",
        )
        fresh_clean_cmt = gate2_comment(
            comment_id=30, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, created_at="2026-11-23T03:00:00Z",
        )
        gh_tombstoned_clean = FakeGitHub(
            [pr_amended],
            {1: [tombstoned_clean_g2, fresh_clean_cmt]},
            deleted={1: 20},
            trees={HEAD: TREE, OTHER_HEAD: RuntimeError("GitHub GET: HTTP 500"), BASE: parent_tree},
            parents={HEAD: [BASE]},
            messages={HEAD: msg},
        )
        with patch.object(
            gh_tombstoned_clean, "commit_identity",
            wraps=gh_tombstoned_clean.commit_identity,
        ) as identity_spy:
            self.assertEqual(reconcile(gh_tombstoned_clean, publish=True)[HEAD].state, "success")
            self.assertEqual(
                [call.args for call in identity_spy.call_args_list],
                [(HEAD, BASE)],
            )
        # Control: the same comment above deleted_through is looked up, so the
        # HTTP 500 surfaces and fails closed.
        gh_untombstoned_clean = FakeGitHub(
            [pr_amended],
            {1: [tombstoned_clean_g2, fresh_clean_cmt]},
            deleted={1: 5},
            trees={HEAD: TREE, OTHER_HEAD: RuntimeError("GitHub GET: HTTP 500"), BASE: parent_tree},
            parents={HEAD: [BASE]},
            messages={HEAD: msg},
        )
        with self.assertRaises(RuntimeError):
            reconcile(gh_untombstoned_clean, publish=True)
        self.assertEqual(gh_untombstoned_clean.writes[-1][1].state, "failure")

    def test_gate2_deleted_through_snapshot_and_same_tree_findings(self):
        msg = "feat: add identity check\n\nBody"
        other_msg = "feat: edit commit message\n\nBody"
        msg_hash = hashlib.sha256(msg.encode("utf-8")).hexdigest()
        parent_tree = "4" * 40
        ik = f"one:{parent_tree}:{TREE}:{msg_hash}"
        finding = {"severity": "P1", "path": "anneal/ci/codex_review.py", "line": 657, "summary": "Live finding"}
        pr_amended = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": BASE}, "draft": False}
        pr_multi = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": OTHER_BASE}, "draft": False}

        # Live undeleted Gate 2 finding comments <= deleted_through still block
        # clean Gate 2 comment #30 and clean review #5; live Codex finding
        # comments <= deleted_through still block fallback Codex clean #30
        # while authentic Gate 2 clean verdicts remain authoritative.
        live_g2_finding_head = gate2_comment(
            comment_id=12, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            created_at="2026-11-23T01:00:00Z",
            verdict="findings", findings=[finding],
        )
        live_g2_finding_hist = gate2_comment(
            comment_id=12, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            created_at="2026-11-23T01:00:00Z",
            verdict="findings", findings=[finding],
        )
        live_codex_finding_head = summary(
            HEAD, status="completed",
            has_any_findings=True, has_unresolved_findings=True,
        )
        live_codex_finding_head["id"] = 10
        live_codex_finding_hist = summary(
            OTHER_HEAD, status="completed",
            has_any_findings=True, has_unresolved_findings=True,
        )
        live_codex_finding_hist["id"] = 10
        clean_codex_30 = summary(HEAD)
        clean_codex_30["id"] = 30
        clean_cmt_30 = gate2_comment(
            comment_id=30, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, created_at="2026-11-23T03:00:00Z",
        )
        clean_rev_5 = gate2_review(
            review_id=5, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
        )
        for label, cmts, revs, expected in (
            ("g2_head_cmt_vs_clean_cmt", [live_g2_finding_head, clean_cmt_30], [], "failure"),
            ("g2_head_cmt_vs_clean_rev", [live_g2_finding_head], [clean_rev_5], "failure"),
            ("g2_head_cmt_sole_tombstoned", [live_g2_finding_head], [], "failure"),
            ("g2_hist_cmt_vs_clean_cmt", [live_g2_finding_hist, clean_cmt_30], [], "failure"),
            ("g2_hist_cmt_vs_clean_rev", [live_g2_finding_hist], [clean_rev_5], "failure"),
            ("codex_head_vs_clean_codex", [live_codex_finding_head, clean_codex_30], [], "failure"),
            ("codex_hist_vs_clean_codex", [live_codex_finding_hist, clean_codex_30], [], "failure"),
            ("codex_head_vs_clean_cmt", [live_codex_finding_head, clean_cmt_30], [], "success"),
            ("codex_head_vs_clean_rev", [live_codex_finding_head], [clean_rev_5], "success"),
            ("codex_hist_vs_clean_cmt", [live_codex_finding_hist, clean_cmt_30], [], "success"),
            ("codex_hist_vs_clean_rev", [live_codex_finding_hist], [clean_rev_5], "success"),
        ):
            with self.subTest(live_finding_comment=label):
                gh = FakeGitHub(
                    [pr_amended],
                    {1: cmts},
                    reviews={1: revs},
                    deleted={1: 20},
                    trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree},
                    parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
                    messages={HEAD: msg, OTHER_HEAD: other_msg},
                )
                self.assertEqual(reconcile(gh, publish=True)[HEAD].state, expected)

        # Live tombstoned-era Gate 2 finding on 404 OTHER_HEAD fails closed.
        gh_live_g2_404 = FakeGitHub(
            [pr_amended],
            {1: [live_g2_finding_hist, clean_cmt_30]},
            deleted={1: 20},
            trees={HEAD: TREE, OTHER_HEAD: RuntimeError("GitHub GET: HTTP 404"), BASE: parent_tree},
            parents={HEAD: [BASE]},
            messages={HEAD: msg},
        )
        with self.assertRaises(RuntimeError):
            reconcile(gh_live_g2_404, publish=True)
        self.assertEqual(gh_live_g2_404.writes[-1][1].state, "failure")

        # Older clean comment <= deleted_through still cannot approve.
        old_clean_cmt_10 = gate2_comment(
            comment_id=10, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            created_at="2026-11-23T01:00:00Z",
        )
        old_clean_codex_10 = summary(HEAD)
        old_clean_codex_10["id"] = 10
        for label, cmts in (
            ("clean_g2_blocked_by_deletion", [old_clean_cmt_10]),
            ("clean_codex_blocked_by_deletion", [old_clean_codex_10]),
        ):
            with self.subTest(tombstoned_clean=label):
                gh_pend = FakeGitHub(
                    [pr_amended],
                    {1: cmts},
                    deleted={1: 20},
                    trees={HEAD: TREE, BASE: parent_tree},
                    parents={HEAD: [BASE]},
                    messages={HEAD: msg},
                )
                self.assertEqual(reconcile(gh_pend, publish=True)[HEAD].state, "pending")

        # Concurrent in-place edit of a non-latest Codex summary from
        # running to completed findings invalidates the snapshot -> pending.
        codex_10_running = summary(HEAD, status="running")
        codex_10_running["id"] = 10
        codex_10_findings = summary(
            HEAD, status="completed",
            has_any_findings=True, has_unresolved_findings=True,
        )
        codex_10_findings["id"] = 10
        codex_10_hist_findings = summary(
            OTHER_HEAD, status="completed",
            has_any_findings=True, has_unresolved_findings=True,
        )
        codex_10_hist_findings["id"] = 10
        codex_11_clean = summary(HEAD)
        codex_11_clean["id"] = 11
        codex_11_running = summary(HEAD, status="running")
        codex_11_running["id"] = 11
        for label, init_cmts, changed_cmts, revs in (
            (
                "head_codex_vs_clean_codex",
                [codex_10_running, codex_11_clean],
                [codex_10_findings, codex_11_clean],
                [],
            ),
            (
                "hist_codex_vs_clean_gate2",
                [codex_10_running, codex_11_running],
                [codex_10_hist_findings, codex_11_running],
                [clean_rev_5],
            ),
        ):
            with self.subTest(codex_summary_edit=label):
                gh_toctou = FakeGitHub(
                    [pr_amended],
                    {1: init_cmts},
                    changed_comments={1: changed_cmts},
                    reviews={1: revs},
                    trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree},
                    parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
                    messages={HEAD: msg, OTHER_HEAD: other_msg},
                )
                self.assertEqual(reconcile(gh_toctou, publish=True)[HEAD].state, "pending")

        # Multi-commit HEAD preserving TREE still blocks on prior same-tree
        # Gate 2 findings (or fallback Codex findings without Gate 2), while an
        # authentic clean Gate 2 review on HEAD is authoritative over Codex.
        live_g2_rev_hist = gate2_review(
            review_id=59, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            submitted_at="2026-11-23T01:00:00Z",
            verdict="findings", findings=[finding],
        )
        multi_clean = gate2_review(
            review_id=60, head_sha=HEAD, base_sha=OTHER_BASE, tree_sha=TREE,
            identity_key=f"multi:{OTHER_BASE}:{HEAD}",
            submitted_at="2026-11-23T03:00:00Z",
        )
        for label, cmts, revs, expected_state, expected_substr in (
            ("multi_same_tree_g2", [], [live_g2_rev_hist, multi_clean], "failure", "finding"),
            ("multi_same_tree_codex_fallback", [live_codex_finding_hist, clean_codex_30], [], "failure", "Codex findings"),
            ("multi_same_tree_codex_with_gate2", [live_codex_finding_hist], [multi_clean], "success", "Clean Gate 2"),
        ):
            with self.subTest(same_tree_rewrite=label):
                gh_multi_same_tree = FakeGitHub(
                    [pr_multi],
                    {1: cmts},
                    reviews={1: revs},
                    trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree, OTHER_BASE: "9" * 40},
                    parents={HEAD: [BASE, OTHER_BASE], OTHER_HEAD: [BASE]},
                    messages={HEAD: msg, OTHER_HEAD: other_msg},
                )
                verdict = reconcile(gh_multi_same_tree, publish=True)[HEAD]
                self.assertEqual(verdict.state, expected_state)
                self.assertIn(expected_substr, verdict.reason)

        # Direct review_result() keeps same-head, same-tree findings
        # blocking across base_sha retargets without historical_trees[head],
        # and reconcile() reuses tree_sha without a second commit_tree(head).
        retarget_finding = gate2_review(
            review_id=70, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            submitted_at="2026-11-23T01:00:00Z",
            verdict="findings", findings=[finding],
        )
        retarget_clean = gate2_review(
            review_id=71, head_sha=HEAD, base_sha=OTHER_BASE, tree_sha=TREE,
            submitted_at="2026-11-23T03:00:00Z",
        )
        for label, revs in (
            ("sole_after_retarget", [retarget_finding]),
            ("followed_by_clean", [retarget_finding, retarget_clean]),
        ):
            with self.subTest(same_head_retarget=label):
                verdict = review_result(
                    HEAD, [], reviews=revs, base_sha=OTHER_BASE, tree_sha=TREE,
                )
                self.assertEqual(verdict.state, "failure")
                self.assertIn("finding", verdict.reason)

        gh_retarget = FakeGitHub(
            [pr_multi], {1: []},
            reviews={1: [retarget_finding, retarget_clean]},
            trees={HEAD: TREE, BASE: parent_tree, OTHER_BASE: "9" * 40},
            parents={HEAD: [OTHER_BASE]},
            messages={HEAD: msg},
        )
        with patch.object(
            gh_retarget, "commit_tree", wraps=gh_retarget.commit_tree
        ) as tree_spy:
            self.assertEqual(reconcile(gh_retarget, publish=True)[HEAD].state, "failure")
            self.assertEqual(
                [call.args for call in tree_spy.call_args_list].count((HEAD,)),
                1,
            )

        # Earlier non-finding failures (CHANGES_REQUESTED, APPROVED,
        # same-family, wrong commit_id) on exact (HEAD, BASE, TREE) block.
        valid_clean_after = gate2_review(
            review_id=81, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
        )
        for label, bad_rev, expected_substr in (
            (
                "changes_requested",
                gate2_review(
                    review_id=80, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                    state="CHANGES_REQUESTED", submitted_at="2026-11-23T01:00:00Z",
                ),
                "CHANGES_REQUESTED",
            ),
            (
                "approved",
                gate2_review(
                    review_id=80, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                    state="APPROVED", submitted_at="2026-11-23T01:00:00Z",
                ),
                "APPROVE",
            ),
            (
                "same_family",
                gate2_review(
                    review_id=80, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                    reviewer_family="claude", author_family="claude",
                    submitted_at="2026-11-23T01:00:00Z",
                ),
                "differ",
            ),
            (
                "wrong_commit_id",
                gate2_review(
                    review_id=80, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                    commit_id=OTHER_HEAD, submitted_at="2026-11-23T01:00:00Z",
                ),
                "commit_id",
            ),
        ):
            with self.subTest(exact_non_finding_failure=label):
                verdict = review_result(
                    HEAD, [], reviews=[bad_rev, valid_clean_after],
                    base_sha=BASE, tree_sha=TREE, identity_key=ik,
                )
                self.assertEqual(verdict.state, "failure")
                self.assertIn(expected_substr, verdict.reason)

        # A keyed clean review recorded against the current base_sha
        # (exact head, or a verified historical head on the same base) must
        # postdate base_changed_at; a verified cross-base transfer still works.
        changed = "2026-11-23T02:00:00Z"
        same_base_hist = {(OTHER_HEAD, BASE): (TREE, ik)}
        cross_base_hist = {(OTHER_HEAD, OTHER_BASE): (TREE, ik)}
        for label, rev_head, rev_base, submitted, hist, expected in (
            ("exact_stale", HEAD, BASE, "2026-11-23T01:00:00Z", None, "pending"),
            ("exact_fresh", HEAD, BASE, "2026-11-23T03:00:00Z", None, "success"),
            ("same_base_hist_stale", OTHER_HEAD, BASE, "2026-11-23T01:00:00Z",
             same_base_hist, "pending"),
            ("same_base_hist_fresh", OTHER_HEAD, BASE, "2026-11-23T03:00:00Z",
             same_base_hist, "success"),
            ("cross_base_hist_stale", OTHER_HEAD, OTHER_BASE,
             "2026-11-23T01:00:00Z", cross_base_hist, "success"),
        ):
            keyed_clean = gate2_review(
                review_id=90, head_sha=rev_head, base_sha=rev_base,
                tree_sha=TREE, identity_key=ik, submitted_at=submitted,
            )
            with self.subTest(keyed_freshness=label):
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[keyed_clean],
                        base_sha=BASE, tree_sha=TREE, identity_key=ik,
                        base_changed_at=changed,
                        historical_identities=hist,
                    ).state,
                    expected,
                )
        stale_keyed_comment = gate2_comment(
            comment_id=91, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, created_at="2026-11-23T01:00:00Z",
        )
        self.assertEqual(
            review_result(
                HEAD, [stale_keyed_comment], base_sha=BASE, tree_sha=TREE,
                identity_key=ik, base_changed_at=changed,
            ).state,
            "pending",
        )
        pr_same_base = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": BASE}, "draft": False}
        gh_stale_keyed = FakeGitHub(
            [pr_same_base], {1: []},
            reviews={1: [gate2_review(
                review_id=92, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                identity_key=ik, submitted_at="2026-11-23T01:00:00Z",
            )]},
            bases={1: changed},
            trees={HEAD: TREE, BASE: parent_tree},
            parents={HEAD: [BASE]},
            messages={HEAD: msg},
        )
        self.assertEqual(reconcile(gh_stale_keyed, publish=True)[HEAD].state, "pending")

        # Non-finding failures on a verified historical commit with
        # the current one-commit identity keep blocking a clean verdict that
        # transfers from that identity, with or without a payload identity_key.
        hist_clean = gate2_review(
            review_id=101, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
        )
        hist_failures = []
        for keyed in (True, False):
            key_kwargs = {"identity_key": ik} if keyed else {}
            suffix = "keyed" if keyed else "keyless"
            hist_failures.extend((
                (f"changes_requested_{suffix}", gate2_review(
                    review_id=100, head_sha=OTHER_HEAD, base_sha=BASE,
                    tree_sha=TREE, state="CHANGES_REQUESTED",
                    submitted_at="2026-11-23T01:00:00Z", **key_kwargs,
                ), "CHANGES_REQUESTED"),
                (f"approved_{suffix}", gate2_review(
                    review_id=100, head_sha=OTHER_HEAD, base_sha=BASE,
                    tree_sha=TREE, state="APPROVED",
                    submitted_at="2026-11-23T01:00:00Z", **key_kwargs,
                ), "APPROVE"),
                (f"same_family_{suffix}", gate2_review(
                    review_id=100, head_sha=OTHER_HEAD, base_sha=BASE,
                    tree_sha=TREE, reviewer_family="claude",
                    author_family="claude",
                    submitted_at="2026-11-23T01:00:00Z", **key_kwargs,
                ), "differ"),
                (f"wrong_commit_id_{suffix}", gate2_review(
                    review_id=100, head_sha=OTHER_HEAD, base_sha=BASE,
                    tree_sha=TREE, commit_id=HEAD,
                    submitted_at="2026-11-23T01:00:00Z", **key_kwargs,
                ), "commit_id"),
            ))
        for label, bad_rev, expected_substr in hist_failures:
            with self.subTest(historical_non_finding_failure=label):
                verdict = review_result(
                    HEAD, [], reviews=[bad_rev, hist_clean],
                    base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                    historical_identities=same_base_hist,
                )
                self.assertEqual(verdict.state, "failure")
                self.assertIn(expected_substr, verdict.reason)
                # Without the historical failure, the clean verdict transfers.
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[hist_clean],
                        base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                        historical_identities=same_base_hist,
                    ).state,
                    "success",
                )

        # A keyless historical failure that is the sole or latest Gate 2 item
        # still blocks (it evaluates as pending when treated as the latest
        # item) and is not masked by a clean legacy Codex summary on HEAD; a
        # sole keyless historical clean review stays pending.
        clean_codex_head = summary(HEAD)
        for label, failing_kwargs, expected_substr in (
            ("changes_requested", {"state": "CHANGES_REQUESTED"},
             "CHANGES_REQUESTED"),
            ("same_family", {"reviewer_family": "claude",
                             "author_family": "claude"}, "differ"),
        ):
            latest_keyless = gate2_review(
                review_id=102, head_sha=OTHER_HEAD, base_sha=BASE,
                tree_sha=TREE, submitted_at="2026-11-23T04:00:00Z",
                **failing_kwargs,
            )
            for order_label, revs in (
                ("sole", [latest_keyless]),
                ("latest_after_clean", [hist_clean, latest_keyless]),
            ):
                for codex_label, cmts in (
                    ("no_codex", []),
                    ("clean_codex_head", [clean_codex_head]),
                ):
                    with self.subTest(latest_historical_failure=(
                            label, order_label, codex_label)):
                        verdict = review_result(
                            HEAD, cmts, reviews=revs,
                            base_sha=OTHER_BASE, tree_sha=TREE,
                            identity_key=ik,
                            historical_identities=same_base_hist,
                        )
                        self.assertEqual(verdict.state, "failure")
                        self.assertIn(expected_substr, verdict.reason)
        sole_keyless_clean = gate2_review(
            review_id=103, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            submitted_at="2026-11-23T04:00:00Z",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[sole_keyless_clean],
                base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                historical_identities=same_base_hist,
            ).state,
            "pending",
        )

        # Failures on unverified or different identities do not block.
        third_head = "7" * 40
        for label, bad_rev in (
            ("unverified_commit", gate2_review(
                review_id=100, head_sha=third_head, base_sha=BASE,
                tree_sha=TREE, state="CHANGES_REQUESTED",
                submitted_at="2026-11-23T01:00:00Z",
            )),
            ("mismatched_structured_key", gate2_review(
                review_id=100, head_sha=OTHER_HEAD, base_sha=BASE,
                tree_sha=TREE, state="CHANGES_REQUESTED",
                identity_key=f"multi:{BASE}:{OTHER_HEAD}",
                submitted_at="2026-11-23T01:00:00Z",
            )),
            ("stale_merge_base", gate2_review(
                review_id=100, head_sha=OTHER_HEAD, base_sha=BASE,
                tree_sha=TREE, state="CHANGES_REQUESTED", identity_key=ik,
                merge_base=OTHER_BASE, submitted_at="2026-11-23T01:00:00Z",
            )),
        ):
            with self.subTest(unverified_or_mismatched_failure=label):
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[bad_rev, hist_clean],
                        base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                        historical_identities=same_base_hist,
                    ).state,
                    "success",
                )

        # reconcile() verifies a keyless same-tree failure's commit identity
        # even when it sits on a different historical commit than the clean
        # review that transfers.
        third_base = "8" * 40
        keyless_cr_third = gate2_review(
            review_id=100, head_sha=third_head, base_sha=third_base,
            tree_sha=TREE, state="CHANGES_REQUESTED",
            submitted_at="2026-11-23T01:00:00Z",
        )
        recon_trees = {
            HEAD: TREE, OTHER_HEAD: TREE, third_head: TREE,
            BASE: parent_tree, OTHER_BASE: parent_tree, third_base: parent_tree,
        }
        recon_parents = {
            HEAD: [OTHER_BASE], OTHER_HEAD: [BASE], third_head: [third_base],
        }
        recon_messages = {HEAD: msg, OTHER_HEAD: msg, third_head: msg}
        for label, revs, expected in (
            ("clean_only", [hist_clean], "success"),
            ("keyless_failure_elsewhere", [keyless_cr_third, hist_clean], "failure"),
        ):
            with self.subTest(reconcile_historical_failure=label):
                gh_hist_failure = FakeGitHub(
                    [pr_multi], {1: []},
                    reviews={1: revs},
                    trees=recon_trees,
                    parents=recon_parents,
                    messages=recon_messages,
                )
                self.assertEqual(
                    reconcile(gh_hist_failure, publish=True)[HEAD].state,
                    expected,
                )

        # A base change never makes a failing review on the exact
        # identity stop blocking, keyed or keyless; it only stops a stale
        # review from passing.
        fresh_keyed_clean = gate2_review(
            review_id=111, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
        )
        for label, stale_kwargs, expected_substr in (
            ("changes_requested", {"state": "CHANGES_REQUESTED"},
             "CHANGES_REQUESTED"),
            ("approved", {"state": "APPROVED"}, "APPROVE"),
            ("same_family", {"reviewer_family": "claude",
                             "author_family": "claude"}, "differ"),
            ("wrong_commit_id", {"commit_id": OTHER_HEAD}, "commit_id"),
        ):
            for keyed in (False, True):
                key_kwargs = {"identity_key": ik} if keyed else {}
                stale_failure = gate2_review(
                    review_id=110, head_sha=HEAD, base_sha=BASE,
                    tree_sha=TREE, submitted_at="2026-11-23T01:00:00Z",
                    **stale_kwargs, **key_kwargs,
                )
                with self.subTest(failure_predating_base_change=(label, keyed)):
                    verdict = review_result(
                        HEAD, [], reviews=[stale_failure, fresh_keyed_clean],
                        base_sha=BASE, tree_sha=TREE, identity_key=ik,
                        base_changed_at=changed,
                    )
                    self.assertEqual(verdict.state, "failure")
                    self.assertIn(expected_substr, verdict.reason)
        stale_keyless_clean = gate2_review(
            review_id=112, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            submitted_at="2026-11-23T01:00:00Z",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[stale_keyless_clean],
                base_sha=BASE, tree_sha=TREE, identity_key=ik,
                base_changed_at=changed,
            ).state,
            "pending",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[stale_keyless_clean, fresh_keyed_clean],
                base_sha=BASE, tree_sha=TREE, identity_key=ik,
                base_changed_at=changed,
            ).state,
            "success",
        )

        # reconcile() fails closed when a blocking same-tree
        # non-finding failure sits on a historical commit GitHub cannot
        # resolve (404/422), even next to a clean review on HEAD, while an
        # unresolvable clean review or a stale-merge_base failure only
        # loses reuse.
        pr_head_base = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": BASE}, "draft": False}
        clean_on_head = gate2_review(
            review_id=121, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
        )
        for label, hist_rev, err, expected in (
            ("keyless_cr_404", gate2_review(
                review_id=120, head_sha=OTHER_HEAD, base_sha=BASE,
                tree_sha=TREE, state="CHANGES_REQUESTED",
                submitted_at="2026-11-23T01:00:00Z",
            ), "GitHub GET: HTTP 404", "failure"),
            ("keyed_same_family_422", gate2_review(
                review_id=120, head_sha=OTHER_HEAD, base_sha=BASE,
                tree_sha=TREE, identity_key=ik, reviewer_family="claude",
                author_family="claude", submitted_at="2026-11-23T01:00:00Z",
            ), "GitHub GET: HTTP 422", "failure"),
            ("keyed_clean_404", gate2_review(
                review_id=120, head_sha=OTHER_HEAD, base_sha=BASE,
                tree_sha=TREE, identity_key=ik,
                submitted_at="2026-11-23T01:00:00Z",
            ), "GitHub GET: HTTP 404", "success"),
            ("stale_merge_base_cr_404", gate2_review(
                review_id=120, head_sha=OTHER_HEAD, base_sha=BASE,
                tree_sha=TREE, state="CHANGES_REQUESTED", identity_key=ik,
                merge_base=OTHER_BASE, submitted_at="2026-11-23T01:00:00Z",
            ), "GitHub GET: HTTP 404", "success"),
        ):
            with self.subTest(unresolvable_historical_failure=label):
                gh_unverifiable = FakeGitHub(
                    [pr_head_base], {1: []},
                    reviews={1: [hist_rev, clean_on_head]},
                    trees={HEAD: TREE, OTHER_HEAD: RuntimeError(err), BASE: parent_tree},
                    parents={HEAD: [BASE]},
                    messages={HEAD: msg},
                )
                if expected == "failure":
                    with self.assertRaises(RuntimeError):
                        reconcile(gh_unverifiable, publish=True)
                    self.assertEqual(gh_unverifiable.writes[-1][1].state, "failure")
                else:
                    self.assertEqual(
                        reconcile(gh_unverifiable, publish=True)[HEAD].state,
                        expected,
                    )

        # A non-finding failure in an issue comment with id <= deleted_through
        # no longer blocks a later clean review above the tombstone, while the
        # same comment above deleted_through still blocks.
        same_family_cmt = gate2_comment(
            comment_id=130, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            reviewer_family="claude", author_family="claude",
            created_at="2026-11-23T01:00:00Z",
        )
        clean_cmt_above = gate2_comment(
            comment_id=140, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, created_at="2026-11-23T03:00:00Z",
        )
        for label, deleted, expected in (
            ("tombstoned", 135, "success"),
            ("live", 0, "failure"),
        ):
            with self.subTest(non_finding_comment=label):
                self.assertEqual(
                    review_result(
                        HEAD, [same_family_cmt, clean_cmt_above],
                        deleted_through=deleted, base_sha=BASE, tree_sha=TREE,
                        identity_key=ik,
                    ).state,
                    expected,
                )

    def test_gate2_advisories(self):
        advisory = {"severity": "P3", "summary": "Wording nit"}
        blocking = {"severity": "P2", "summary": "Real defect"}
        p3_finding = {"severity": "P3", "summary": "Blocking P3"}

        # Advisories are P3-only and never block a clean review; a P3 in
        # findings[] keeps blocking.
        for label, rev, expected in (
            ("clean_with_advisory",
             gate2_review(advisories=[advisory]), "success"),
            ("clean_with_empty_advisories", gate2_review(advisories=[]),
             "success"),
            ("p3_finding_blocks", gate2_review(
                verdict="findings", findings=[p3_finding]), "failure"),
            ("findings_with_advisory", gate2_review(
                verdict="findings", findings=[blocking],
                advisories=[advisory]), "failure"),
        ):
            with self.subTest(valid=label):
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[rev], base_sha=BASE, tree_sha=TREE,
                    ).state,
                    expected,
                )
        for label, extra in (
            ("p2_advisory", {"advisories": [blocking]}),
            ("malformed_advisory", {"advisories": [{"severity": "P3"}]}),
            ("advisories_not_list", {"advisories": 5}),
            ("advisories_null", {"advisories": None}),
            ("unhashable_advisory_severity", {
                "advisories": [{"severity": [], "summary": "note"}]}),
            ("unhashable_finding_severity", {
                "verdict": "findings",
                "findings": [{"severity": {}, "summary": "note"}]}),
            # The only review modes are "full" and "delta", and delta_from
            # needs delta mode (see Gate2DeltaReviewTests).
            ("unknown_review_mode", {"review_mode": "partial"}),
            ("delta_from_without_mode", {"delta_from": OTHER_HEAD}),
            ("delta_from_with_full_mode",
             {"review_mode": "full", "delta_from": OTHER_HEAD}),
        ):
            with self.subTest(malformed=label):
                with self.assertRaises(ValueError):
                    parse_gate2_payload(gate2_review(**extra)["body"])
                # A malformed payload fails closed instead of crashing.
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[gate2_review(**extra)],
                        base_sha=BASE, tree_sha=TREE,
                    ).state,
                    "failure",
                )
