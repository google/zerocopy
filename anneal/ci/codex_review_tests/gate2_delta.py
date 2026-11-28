# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`codex_review` tests for conditional delta Gate 2 reviews."""

from .support import (
    BASE,
    FakeGitHub,
    gate2_comment,
    gate2_review,
    HEAD,
    io,
    OTHER_BASE,
    OTHER_HEAD,
    OTHER_TREE,
    parse_gate2_payload,
    patch,
    pull,
    reconcile,
    review_result,
    summary,
    TREE,
    unittest,
)


class Gate2DeltaReviewTests(unittest.TestCase):
    """Conditional delta reviews (`review_mode: "delta"`) fail closed."""

    SEATS = [
        {"seat": "seat1", "family": "claude", "status": "completed",
         "verdict": "clean"},
        {"seat": "seat2", "family": "gemini", "status": "completed",
         "verdict": "clean"},
    ]
    P2 = {"id": "G2-R1-01", "severity": "P2", "summary": "Off-by-one"}
    # Marks a default payload field to leave out of the review.
    OMIT = object()

    @classmethod
    def _review(cls, defaults, overrides):
        fields = {**defaults, **overrides}
        return gate2_review(
            **{k: v for k, v in fields.items() if v is not cls.OMIT})

    def _anchor(self, **overrides):
        fields = {
            "review_id": 20, "head_sha": OTHER_HEAD, "tree_sha": OTHER_TREE,
            "submitted_at": "2026-11-23T01:00:00Z",
            "reviewer_family": "multi", "author_family": "agent",
            "panel_seats": self.SEATS, "risk_tier": "tier1_code", "round": 1,
            "verdict": "findings", "findings": [self.P2],
        }
        return self._review(fields, overrides)

    def _delta(self, **overrides):
        fields = {
            "review_id": 21, "head_sha": HEAD, "tree_sha": TREE,
            "submitted_at": "2026-11-23T02:00:00Z",
            "reviewer_family": "multi", "author_family": "agent",
            "panel_seats": self.SEATS, "risk_tier": "tier1_code", "round": 2,
            "review_mode": "delta", "delta_from": OTHER_HEAD,
            "prior_findings_status": [{"id": "G2-R1-01", "status": "closed"}],
        }
        return self._review(fields, overrides)

    def _state(self, reviews, comments=(), **kwargs):
        # The evaluator verifies the anchor head's tree through GitHub.
        kwargs.setdefault("historical_trees", {OTHER_HEAD: OTHER_TREE})
        return review_result(
            HEAD, list(comments), reviews=reviews, base_sha=BASE, tree_sha=TREE,
            **kwargs,
        )

    def test_delta_after_full_panel_passes(self):
        res = self._state([self._anchor(), self._delta()])
        self.assertEqual(res.state, "success", res.reason)
        for label, anchor, delta in (
            ("explicit_full_anchor", self._anchor(review_mode="full"),
             self._delta()),
            ("clean_anchor", self._anchor(verdict="clean", findings=[]),
             self._delta(prior_findings_status=[])),
            ("p3_anchor", self._anchor(findings=[dict(self.P2, severity="P3")]),
             self._delta()),
            ("docs_tier", self._anchor(risk_tier="tier0_docs"),
             self._delta(risk_tier="tier0_docs")),
            ("unclear_prior", self._anchor(),
             self._delta(prior_findings_status=[
                 {"id": "G2-R1-01", "status": "unclear"}])),
        ):
            with self.subTest(label):
                self.assertEqual(self._state([anchor, delta]).state, "success")
        # Explicit full mode is valid without any delta fields.
        parse_gate2_payload(gate2_review(review_mode="full")["body"])
        # A delta review with findings fails like any other review.
        self.assertEqual(self._state([self._anchor(), self._delta(
            verdict="findings", findings=[dict(self.P2, id="G2-R2-01")],
            prior_findings_status=[{"id": "G2-R1-01", "status": "still_open"}],
        )]).state, "failure")

    def test_malformed_delta_shapes_fail(self):
        # Only the shape of `review_mode` and `delta_from` is schema.
        for label, overrides in (
            ("unknown_mode", {"review_mode": "partial"}),
            ("unknown_mode_alone",
             {"review_mode": "partial", "delta_from": self.OMIT}),
            ("null_mode", {"review_mode": None}),
            ("list_mode", {"review_mode": ["delta"]}),
            ("escalated_mode", {"review_mode": "delta_escalated"}),
            ("delta_from_with_full", {"review_mode": "full"}),
            ("delta_from_without_mode", {"review_mode": self.OMIT}),
            ("short_delta_from", {"delta_from": "b" * 39}),
            ("upper_delta_from", {"delta_from": "B" * 40}),
            ("null_delta_from", {"delta_from": None}),
            ("bool_round", {"round": True}),
            ("missing_seats", {"panel_seats": self.OMIT}),
            ("empty_seats", {"panel_seats": []}),
        ):
            with self.subTest(label):
                delta = self._delta(**overrides)
                with self.assertRaises(ValueError):
                    parse_gate2_payload(delta["body"])
                self.assertEqual(
                    self._state([self._anchor(), delta]).state, "failure")

    INELIGIBLE = {
        "missing_delta_from": {"delta_from": OMIT},
        "self_delta_from": {"delta_from": HEAD},
        "missing_round": {"round": OMIT},
        "first_round": {"round": 1},
        "tcb_tier": {"risk_tier": "tier2a_core_tcb"},
        "policy_tier": {"risk_tier": "tier2b_cli_policy"},
        "legacy_tcb_tier": {"risk_tier": "tier2_tcb"},
        "missing_tier": {"risk_tier": OMIT},
        "failed_seat": {"panel_seats": SEATS + [
            dict(SEATS[1], status="failed", verdict="error")]},
        # A seat that did not complete fails even with a clean verdict.
        "failed_clean_seat": {"panel_seats": SEATS + [
            dict(SEATS[1], status="failed")]},
        "claude_only": {"panel_seats": [SEATS[0]]},
        "unfinished_seat": {"panel_seats": [
            SEATS[0], dict(SEATS[1], verdict="incomplete")]},
        "gemini_only": {"panel_seats": [SEATS[1]]},
        "missing_prior_status": {"prior_findings_status": OMIT},
        "bare_prior_status": {"prior_findings_status": ["G2-R1-01"]},
        "unknown_prior_status": {"prior_findings_status": [
            {"id": "G2-R1-01", "status": "fixed"}]},
        "extra_prior_status_key": {"prior_findings_status": [
            {"id": "G2-R1-01", "status": "closed", "note": "fixed"}]},
        "duplicate_prior_status": {"prior_findings_status": [
            {"id": "G2-R1-01", "status": "closed"},
            {"id": "G2-R1-01", "status": "unclear"}]},
    }

    def test_ineligible_delta_reviews_stay_pending(self):
        # A delta review that misses an eligibility condition is a
        # well-formed review that does not pass, not a malformed one.
        for label, overrides in self.INELIGIBLE.items():
            with self.subTest(label):
                delta = self._delta(**overrides)
                parse_gate2_payload(delta["body"])
                res = self._state([self._anchor(), delta])
                self.assertEqual(res.state, "pending", res.reason)
                self.assertIn("request a full Gate 2 review", res.reason)

    def test_delta_from_must_differ_from_head(self):
        # With an anchor on this head, only the delta review's own check
        # rejects `delta_from == head_sha`.
        anchor = self._anchor(head_sha=HEAD, tree_sha=TREE, verdict="clean",
                              findings=[])
        trees = {HEAD: TREE}
        self.assertEqual(self._state(
            [anchor, self._delta(delta_from=OTHER_HEAD,
                                 prior_findings_status=[])],
            historical_trees=trees).state, "pending")
        res = self._state(
            [anchor, self._delta(delta_from=HEAD, prior_findings_status=[])],
            historical_trees=trees)
        self.assertEqual(res.state, "pending", res.reason)
        self.assertIn("must differ from head_sha", res.reason)

    def test_ineligible_delta_findings_still_block(self):
        # Findings in an ineligible delta review of this head keep blocking a
        # later clean full review of the same head.
        p1 = dict(self.P2, id="G2-R2-01", severity="P1")
        clean_full = gate2_review(
            review_id=22, submitted_at="2026-11-23T03:00:00Z",
            reviewer_family="multi", author_family="agent",
            panel_seats=self.SEATS, risk_tier="tier1_code", round=3)
        self.assertEqual(
            self._state([self._anchor(), clean_full]).state, "success")
        for label, overrides in self.INELIGIBLE.items():
            with self.subTest(label):
                delta = self._delta(
                    **{**overrides, "verdict": "findings", "findings": [p1]})
                res = self._state([self._anchor(), delta, clean_full])
                self.assertEqual(res.state, "failure", res.reason)

    def test_delta_fails_closed_on_deleted_history(self):
        # The deletion journal cannot say what was deleted, so any recorded
        # deletion rules out a delta round.
        res = self._state([self._anchor(), self._delta()], deleted_through=5)
        self.assertEqual(res.state, "pending")
        self.assertIn("deleted", res.reason)
        # A still-present comment covered by the journal and sorted after the
        # delta review cannot hide a P1 finding on the anchor.
        p1_comment = gate2_comment(
            comment_id=31, head_sha=OTHER_HEAD, tree_sha=OTHER_TREE,
            created_at="2026-11-23T03:00:00Z",
            verdict="findings", findings=[dict(self.P2, severity="P1")])
        for created_at in ("2026-11-23T03:00:00Z", "not a timestamp"):
            with self.subTest(created_at=created_at):
                res = self._state(
                    [self._anchor(), self._delta()],
                    comments=[dict(p1_comment, created_at=created_at)],
                    deleted_through=31)
                self.assertNotEqual(res.state, "success", res.reason)

    def test_delta_requires_verified_anchor_tree(self):
        for label, trees in (
            ("unverified", {}),
            ("absent", None),
            ("mismatched", {OTHER_HEAD: "9" * 40}),
        ):
            with self.subTest(label):
                res = self._state([self._anchor(), self._delta()],
                                  historical_trees=trees)
                self.assertEqual(res.state, "pending")
                self.assertIn("Cannot verify the tree", res.reason)
        # An anchor that misstates its tree cannot hide a P1 finding on
        # another head with the anchor's actual tree.
        earlier = self._anchor(
            review_id=19, submitted_at="2026-11-23T00:30:00Z",
            head_sha="9" * 40, tree_sha=OTHER_TREE,
            findings=[dict(self.P2, id="G2-R0-01", severity="P1")])
        audited = self._delta(prior_findings_status=[
            {"id": "G2-R0-01", "status": "closed"},
            {"id": "G2-R1-01", "status": "closed"}])
        res = self._state(
            [earlier, self._anchor(tree_sha="8" * 40), audited])
        self.assertEqual(res.state, "pending", res.reason)

    def test_reconcile_rechecks_when_any_codex_summary_changes(self):
        # Any non-clean legacy Codex summary rules out a delta round, so an
        # edit to an older summary during reconciliation forces a recheck.
        reviews = {1: [self._anchor(), self._delta()]}
        old, latest = summary(head=OTHER_HEAD), summary(head=OTHER_HEAD)
        latest["id"] = 20
        edited = summary(head=OTHER_HEAD, status="running")
        with patch("sys.stdout", new=io.StringIO()):
            github = FakeGitHub([pull()], {1: [old, latest]}, reviews=reviews)
            self.assertEqual(reconcile(github)[HEAD].state, "success")
            github = FakeGitHub([pull()], {1: [old, latest]}, reviews=reviews,
                                changed_comments={1: [edited, latest]})
            res = reconcile(github)[HEAD]
            self.assertEqual(res.state, "pending", res.reason)

    def test_reconcile_verifies_anchor_tree(self):
        reviews = {1: [self._anchor(), self._delta()]}
        with patch("sys.stdout", new=io.StringIO()):
            github = FakeGitHub([pull()], {1: []}, reviews=reviews)
            self.assertEqual(reconcile(github)[HEAD].state, "success")
            for label, tree in (
                ("missing", RuntimeError("HTTP 404")),
                ("mismatched", "9" * 40),
            ):
                with self.subTest(label):
                    github = FakeGitHub(
                        [pull()], {1: []}, reviews=reviews,
                        trees={HEAD: TREE, OTHER_HEAD: tree})
                    self.assertEqual(
                        reconcile(github)[HEAD].state, "pending")

    def test_delta_requires_valid_preceding_full_review(self):
        p1 = dict(self.P2, severity="P1")
        intervening = gate2_review(
            review_id=25, head_sha=OTHER_HEAD, tree_sha=OTHER_TREE,
            submitted_at="2026-11-23T01:30:00Z", verdict="incomplete")
        cases = {
            "no_anchor": [self._delta()],
            "delta_anchor": [self._anchor(), self._anchor(
                review_id=22, submitted_at="2026-11-23T01:30:00Z", round=2,
                review_mode="delta", delta_from="9" * 40, verdict="clean",
                findings=[], prior_findings_status=[
                    {"id": "G2-R1-01", "status": "closed"}]), self._delta()],
            "wrong_delta_from": [self._anchor(),
                                 self._delta(delta_from="9" * 40)],
            "p1_anchor": [self._anchor(findings=[p1]), self._delta()],
            "p0_anchor": [self._anchor(findings=[dict(p1, severity="P0")]),
                          self._delta()],
            "tcb_anchor": [self._anchor(risk_tier="tier2a_core_tcb"),
                           self._delta()],
            "untiered_anchor": [self._anchor(risk_tier=self.OMIT),
                                self._delta()],
            "incomplete_anchor": [self._anchor(verdict="incomplete",
                                               findings=[]), self._delta()],
            "failed_seat_anchor": [self._anchor(panel_seats=self.SEATS + [
                dict(self.SEATS[1], status="failed", verdict="error")]),
                self._delta()],
            "seatless_anchor": [self._anchor(panel_seats=self.OMIT,
                                             reviewer_family="gemini",
                                             author_family="claude"),
                                self._delta()],
            "blocked_anchor": [self._anchor(coverage={"blocked": 1}),
                               self._delta()],
            "unnamed_finding": [self._anchor(findings=[
                {k: v for k, v in self.P2.items() if k != "id"}]),
                self._delta()],
            "unaudited_finding": [self._anchor(), self._delta(
                prior_findings_status=[])],
            "other_id_audited": [self._anchor(), self._delta(
                prior_findings_status=[
                    {"id": "G2-R1-02", "status": "closed"}])],
            "intervening_review": [self._anchor(), intervening, self._delta()],
            # Cross-family seats do not excuse a same-family reviewer.
            "same_family_anchor": [self._anchor(reviewer_family="agent"),
                                   self._delta()],
            # A multi-family anchor needs a seat outside the author's family.
            "same_family_seats_anchor": [self._anchor(
                author_family="claude",
                panel_seats=[self.SEATS[0], dict(self.SEATS[0], seat="seat2")]),
                self._delta()],
            "changes_requested_anchor": [self._anchor(
                state="CHANGES_REQUESTED"), self._delta()],
            "wrong_commit_anchor": [self._anchor(commit_id="9" * 40),
                                    self._delta()],
            "unfinished_seat_anchor": [self._anchor(panel_seats=[
                self.SEATS[0], dict(self.SEATS[1], verdict="incomplete")]),
                self._delta()],
            "rebased": [self._anchor(base_sha=OTHER_BASE), self._delta()],
            # Two earlier findings that share an id need two audits.
            "duplicate_finding_id": [
                self._anchor(review_id=19, submitted_at="2026-11-23T00:30:00Z",
                             head_sha="9" * 40, tree_sha="8" * 40),
                self._anchor(), self._delta()],
            "stale_merge_base_anchor": [self._anchor(merge_base=OTHER_BASE),
                                        self._delta()],
            # A second review of the anchor head can hide behind the anchor.
            "earlier_p1_on_anchor_head": [
                self._anchor(review_id=19, submitted_at="2026-11-23T00:30:00Z",
                             tree_sha="8" * 40,
                             findings=[dict(p1, id="G2-R1-02")]),
                self._anchor(), self._delta(prior_findings_status=[
                    {"id": "G2-R1-01", "status": "closed"},
                    {"id": "G2-R1-02", "status": "closed"}])],
            # A P1 on another head with the anchor's tree is on the anchor.
            "earlier_p1_on_anchor_tree": [
                self._anchor(review_id=19, submitted_at="2026-11-23T00:30:00Z",
                             head_sha="9" * 40,
                             findings=[dict(p1, id="G2-R0-01")]),
                self._anchor(), self._delta(prior_findings_status=[
                    {"id": "G2-R0-01", "status": "closed"},
                    {"id": "G2-R1-01", "status": "closed"}])],
            "earlier_round_unaudited": [
                self._anchor(review_id=19, submitted_at="2026-11-23T00:30:00Z",
                             head_sha="9" * 40, tree_sha="8" * 40,
                             findings=[dict(self.P2, id="G2-R0-01")]),
                self._anchor(), self._delta()],
            # Earlier items are parsed strictly, identity_key included.
            "earlier_bad_identity_key": [
                self._anchor(review_id=19, submitted_at="2026-11-23T00:30:00Z",
                             head_sha="9" * 40, tree_sha="8" * 40,
                             verdict="clean", findings=[],
                             identity_key="one:not-an-identity"),
                self._anchor(), self._delta()],
            "earlier_contradictory_identity_key": [
                self._anchor(review_id=19, submitted_at="2026-11-23T00:30:00Z",
                             head_sha="9" * 40, tree_sha="8" * 40,
                             verdict="clean", findings=[],
                             identity_key=f"multi:{BASE}:{'7' * 40}"),
                self._anchor(), self._delta()],
            "earlier_malformed": [
                dict(self._anchor(review_id=19,
                                  submitted_at="2026-11-23T00:30:00Z"),
                     body="<!-- anneal-gate2-review:v1 {} -->"),
                self._anchor(), self._delta()],
            "malformed_anchor": [dict(self._anchor(), body=(
                "<!-- anneal-gate2-review:v1 {} -->")), self._delta()],
        }
        for label, reviews in cases.items():
            with self.subTest(label):
                res = self._state(reviews)
                self.assertNotEqual(res.state, "success", res.reason)
        self.assertIn("no preceding full review",
                      self._state(cases["no_anchor"]).reason)
        # The anchor must postdate a base change on the current base.
        res = self._state([self._anchor(), self._delta()],
                          base_changed_at="2026-11-23T01:30:00Z")
        self.assertEqual(res.state, "pending", res.reason)
        self.assertIn("spans a base change", res.reason)
        # A pair recorded on an earlier base, whose delta review transfers by
        # one-commit identity, is not judged by the current base's change.
        ik = f"one:{'6' * 40}:{TREE}:{'7' * 64}"
        for changed_at in (None, "2026-11-23T01:30:00Z"):
            with self.subTest(transferred_base_changed_at=changed_at):
                res = review_result(
                    "1" * 40, [], base_changed_at=changed_at, reviews=[
                        self._anchor(base_sha=OTHER_BASE),
                        self._delta(base_sha=OTHER_BASE, identity_key=ik)],
                    base_sha=BASE, tree_sha=TREE, identity_key=ik,
                    historical_identities={(HEAD, OTHER_BASE): (TREE, ik)},
                    historical_trees={OTHER_HEAD: OTHER_TREE})
                self.assertEqual(res.state, "success", res.reason)
        self.assertEqual(self._state(
            [self._anchor(), self._delta()],
            base_changed_at="2026-11-23T00:30:00Z").state, "success")
        # An issue comment binds no commit, so it never anchors a delta review.
        anchor_comment = gate2_comment(
            comment_id=30, head_sha=OTHER_HEAD, tree_sha=OTHER_TREE,
            created_at="2026-11-23T01:00:00Z", reviewer_family="multi",
            author_family="agent", panel_seats=self.SEATS,
            risk_tier="tier1_code", round=1, verdict="findings",
            findings=[self.P2])
        res = self._state([self._delta()], comments=[anchor_comment])
        self.assertEqual(res.state, "pending")
        self.assertIn("full PR review", res.reason)
        # Earlier findings on other heads pass once audited, and a non-clean
        # legacy Codex summary anywhere on the PR rules out a delta round.
        earlier = self._anchor(
            review_id=19, submitted_at="2026-11-23T00:30:00Z",
            head_sha="9" * 40, tree_sha="8" * 40,
            findings=[dict(p1, id="G2-R0-01")])
        audited = self._delta(prior_findings_status=[
            {"id": "G2-R0-01", "status": "closed"},
            {"id": "G2-R1-01", "status": "closed"}])
        self.assertEqual(
            self._state([earlier, self._anchor(), audited]).state, "success")
        self.assertEqual(self._state(
            [self._anchor(), self._delta()],
            comments=[summary(head=OTHER_HEAD)]).state, "success")
        self.assertEqual(self._state(
            [self._anchor(), self._delta()],
            comments=[summary(head=OTHER_HEAD, has_any_findings=True,
                              has_unresolved_findings=False)]).state,
            "pending")
        # A contradictory summary (unresolved but no findings) is not clean.
        self.assertEqual(self._state(
            [self._anchor(), self._delta()],
            comments=[summary(head=OTHER_HEAD,
                              has_unresolved_findings=True)]).state,
            "pending")

    def test_delta_review_never_carries_forward(self):
        new_head, new_base, new_tree = "1" * 40, "2" * 40, "3" * 40
        identity = f"one:{'4' * 40}:{new_tree}:{'5' * 64}"
        anchor_ik = f"one:{'6' * 40}:{TREE}:{'7' * 64}"

        def state(latest):
            calls = []

            def verifier(*args):
                calls.append(args)
                return anchor_ik

            res = review_result(
                new_head, [], reviews=[self._anchor(), latest],
                base_sha=new_base, tree_sha=new_tree, identity_key=identity,
                historical_trees={OTHER_HEAD: OTHER_TREE},
                carry_forward_verifier=verifier,
            )
            return res.state, len(calls)

        full = self._delta(review_mode="full", delta_from=self.OMIT)
        self.assertEqual(state(full), ("success", 1))
        # A delta review never reaches the rebase verifier.
        self.assertEqual(state(self._delta()), ("pending", 0))
