# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`codex_review` tests for review policy boundaries."""

from .support import (
    BOT_ID,
    combine_results,
    HEAD,
    json,
    OTHER_HEAD,
    pull,
    Result,
    review_result,
    summary,
    unittest,
)


class PolicyTests(unittest.TestCase):
    def test_clean_exact_head_needs_no_formal_review_or_reaction(self):
        self.assertEqual(review_result(HEAD, [summary()]).state, "success")

    def test_retargeting_unchanged_head_requires_a_fresh_code_review(self):
        changed = "2026-11-08T11:00:00Z"
        old = summary()
        old["updated_at"] = "2026-11-08T13:00:00Z"
        self.assertEqual(review_result(HEAD, [old], base_changed_at=changed).state,
                         "pending")
        fresh = summary(created_at="2026-11-08T12:00:00Z",
                        completed_at="2026-11-08T12:01:00Z")
        self.assertEqual(review_result(HEAD, [fresh], base_changed_at=changed).state,
                         "success")
        # Recreating the summary for Security Review cannot republish the old
        # Code Review's completion time as a fresh review of the new base.
        copied = summary(created_at="2026-11-08T12:00:00Z")
        self.assertEqual(review_result(HEAD, [copied], base_changed_at=changed).state,
                         "pending")

    def test_base_freshness_needs_unambiguous_aware_code_review_times(self):
        changed = "2026-11-08T11:00:00Z"
        for created, completed in [(None, "2026-11-08T12:01:00Z"),
                                   ("2026-11-08T12:00:00", "2026-11-08T12:01:00Z"),
                                   ("2026-11-08T12:00:00Z", "invalid"),
                                   ("2026-11-08T12:00:00+02:00", "2026-11-08T12:01:00+02:00")]:
            candidate = summary(created_at=created, completed_at=completed)
            with self.subTest(created=created, completed=completed):
                self.assertNotEqual(review_result(
                    HEAD, [candidate], base_changed_at=changed).state, "success")
        for suffix in ["", "\n" + summary()["body"].splitlines()[-1]]:
            candidate = summary(created_at="2026-11-08T12:00:00Z",
                                completed_at="2026-11-08T12:01:00Z")
            if not suffix:
                candidate["body"] = candidate["body"].rsplit("\n", 1)[0]
            else:
                candidate["body"] += suffix
            self.assertNotEqual(review_result(
                HEAD, [candidate], base_changed_at=changed).state, "success")

    def test_missing_deleted_or_wrong_head_summary_waits(self):
        for comments in [[], [summary(OTHER_HEAD)]]:
            with self.subTest(comments=comments):
                self.assertEqual(review_result(HEAD, comments).state, "pending")

    def test_only_the_exact_bot_identity_is_authoritative(self):
        for key, value in [("id", BOT_ID + 1), ("login", "codex[bot]"),
                           ("type", "User")]:
            comment = summary()
            comment["user"][key] = value
            with self.subTest(key=key):
                self.assertEqual(review_result(HEAD, [comment]).state, "pending")

    def test_running_and_failed_review_states_do_not_pass(self):
        for status in ["running", "queued", "failed", None, True]:
            with self.subTest(status=status):
                self.assertNotEqual(review_result(
                    HEAD, [summary(status=status)]).state, "success")

    def test_completed_is_not_a_verdict_and_resolution_is_not_a_clean_review(self):
        for key in ["has_any_findings", "has_unresolved_findings"]:
            for value in [True, None, 0, "false", [], {}]:
                with self.subTest(key=key, value=value):
                    self.assertEqual(review_result(
                        HEAD, [summary(**{key: value})]).state, "failure")
            comment = summary()
            payload = json.loads(comment["body"].split("v1 ")[1].split(" -->")[0])
            del payload["code_review"][key]
            comment["body"] = ("<!-- codex-pull-request-review-summary -->\n"
                               "<!-- codex-review-state:v1 "
                               + json.dumps(payload) + " -->")
            self.assertEqual(review_result(HEAD, [comment]).state, "failure")

    def test_no_fallback_to_an_older_clean_summary(self):
        older = summary()
        newer = summary(status="running")
        newer["id"] += 1
        # Updated timestamps and input ordering do not change creation order.
        older["updated_at"] = "2099-01-01T00:00:00Z"
        for comments in [[older, newer], [newer, older]]:
            self.assertEqual(review_result(HEAD, comments).state, "pending")
        newer["body"] = "<!-- codex-pull-request-review-summary:v2 -->"
        self.assertEqual(review_result(HEAD, [older, newer]).state, "failure")

    def test_deletion_tombstone_prevents_resurrecting_an_older_clean_summary(self):
        old_clean = summary()
        self.assertEqual(review_result(HEAD, [old_clean], 11).state, "pending")
        # Rewinding to this head does not erase the PR's deletion record.
        self.assertEqual(review_result(HEAD, [old_clean], 10).state, "pending")
        new_clean = summary()
        new_clean["id"] = 12
        self.assertEqual(review_result(HEAD, [old_clean, new_clean], 11).state,
                         "success")
        self.assertEqual(review_result(HEAD, [new_clean], 9).state, "success")

    def test_unsupported_ambiguous_and_malformed_state_blocks(self):
        clean = summary()["body"]
        variants = [
            clean.replace("state:v1", "state:v2"),
            clean.replace('"code_review": {', '"code_review": null, "extra": {'),
            clean.replace('"status": "completed"', '"status": "completed", "status": "running"'),
            clean.replace('"has_any_findings": false', '"has_any_findings": true, "has_any_findings": false'),
            clean + clean,
            clean + "<!-- codex-review-state:v2 {} -->",
            clean.replace(" -->\nCodex", "\nCodex"),
            "<!-- codex-pull-request-review-summary -->\n<!-- codex-review-state:v1 [] -->",
        ]
        for body in variants:
            comment = summary()
            comment["body"] = body
            with self.subTest(body=body):
                self.assertEqual(review_result(HEAD, [comment]).state, "failure")

    def test_security_receipt_and_emoji_do_not_fill_in_code_review(self):
        comment = summary()
        comment["body"] = comment["body"].replace('"code_review":', '"other":')
        self.assertEqual(review_result(HEAD, [comment]).state, "failure")
        for body in ["👍", "No major issues found", "<!-- codex-review-receipt:v1 -->"]:
            comment["body"] = body
            self.assertEqual(review_result(HEAD, [comment]).state, "pending")

    def test_shared_head_requires_each_pr_even_with_a_different_base_or_draft(self):
        pulls = [pull(1), pull(2, base="stack-parent")]
        pulls[1]["draft"] = True
        results = {1: review_result(HEAD, [summary()]),
                   2: review_result(HEAD, [])}
        self.assertEqual(combine_results(pulls, results)[HEAD].state, "pending")
        results[2] = Result("failure", "Findings")
        self.assertEqual(combine_results(pulls, results)[HEAD].state, "failure")
        results[2] = review_result(HEAD, [summary()])
        self.assertEqual(combine_results(pulls, results)[HEAD].state, "success")

    def test_findings_are_reported_even_if_another_pr_is_still_waiting(self):
        results = {1: Result("pending", "Waiting"),
                   2: Result("failure", "Findings")}
        combined = combine_results([pull(1), pull(2)], results)
        self.assertEqual(combined[HEAD], Result("failure", "PR #2: Findings"))

    def test_unrelated_commits_have_independent_verdicts(self):
        results = {1: Result("success", "Clean"), 2: Result("failure", "Findings")}
        combined = combine_results([pull(1), pull(2, OTHER_HEAD)], results)
        self.assertEqual(combined[HEAD].state, "success")
        self.assertEqual(combined[OTHER_HEAD].state, "failure")
