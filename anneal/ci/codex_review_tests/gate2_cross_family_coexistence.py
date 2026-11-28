# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Gate 2 cross-family tests for coexistence with legacy Codex summaries,
`reconcile` and transport of reviews, and multi-seat payloads."""

from .support import (
    BASE,
    FakeGitHub,
    gate2_comment,
    gate2_review,
    GitHub,
    HEAD,
    io,
    OTHER_HEAD,
    OTHER_TREE,
    patch,
    pull,
    reconcile,
    Result,
    review_result,
    summary,
    TREE,
)


class Gate2CoexistenceTests:
    """Part of `Gate2CrossFamilyTests`."""

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
