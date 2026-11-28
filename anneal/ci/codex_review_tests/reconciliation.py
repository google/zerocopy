# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`codex_review` tests for status reconciliation."""

from .support import (
    FakeGitHub,
    HEAD,
    io,
    OTHER_HEAD,
    patch,
    pull,
    reconcile,
    Result,
    summary,
    unittest,
)


class ReconciliationTests(unittest.TestCase):
    def run_gate(self, github, publish=False, requested_group=None):
        with patch("sys.stdout", new=io.StringIO()):
            return reconcile(github, publish, requested_group)

    def test_summary_changes_without_pr_metadata_changes_block_publication(self):
        newer = summary()
        newer["id"] = 11
        for changed in [[], [summary(status="running")],
                        [summary(has_any_findings=True)], [newer]]:
            github = FakeGitHub([pull()], {1: [summary()]},
                                changed_comments={1: changed})
            with self.subTest(changed=changed):
                self.run_gate(github, True)
                self.assertEqual(github.writes[0][1].state, "pending")

    def test_old_comment_activity_cannot_invalidate_an_unchanged_latest_verdict(self):
        latest = summary()
        latest["id"] = 11
        old = summary(status="running")
        github = FakeGitHub([pull()], {1: [old, latest]},
                            changed_comments={1: [latest]})
        self.assertEqual(self.run_gate(github, True)[HEAD].state, "success")
        # A deletion record for a closed PR is not an input to any open PR's
        # decision and must not force a spurious context-change failure.
        github = FakeGitHub([pull()], {1: [latest]})
        with patch.object(github, "deleted_summaries", side_effect=[{}, {2: 99}]):
            self.assertEqual(self.run_gate(github, True)[HEAD].state, "success")

    def test_initial_context_failure_revokes_known_successes(self):
        for method in ["deleted_summaries", "queue_groups", "base_changes"]:
            github = FakeGitHub([pull()], {1: [summary()]})
            with self.subTest(method=method), patch.object(
                    github, method, side_effect=RuntimeError("API unavailable")):
                with self.assertRaisesRegex(RuntimeError, "API unavailable"):
                    self.run_gate(github, True)
            self.assertEqual(github.writes[0][1].state, "pending")

    def test_missing_base_history_is_not_an_initial_base_with_no_changes(self):
        github = FakeGitHub([pull()], {1: [summary()]}, bases={})
        with self.assertRaisesRegex(RuntimeError, "PR list and base history differ"):
            self.run_gate(github, True)
        self.assertEqual(github.writes[0][1].state, "pending")

    def test_deletion_or_queue_changes_during_evaluation_revoke_success(self):
        for method, reads in [("deleted_summaries", [{}, {1: 11}]),
                              ("queue_groups", [{}, {"d" * 40: {1: HEAD}}])]:
            github = FakeGitHub([pull()], {1: [summary()]})
            with patch.object(github, method, side_effect=reads):
                with self.assertRaises(RuntimeError):
                    self.run_gate(github, True)
            self.assertEqual(github.writes[0][1].state, "pending")

    def test_deleting_a_newer_comment_during_read_cannot_expose_old_success(self):
        newer = summary()
        newer["id"] = 11
        github = FakeGitHub([pull()], {1: [summary(), newer]},
                            changed_comments={1: [summary()]})
        self.run_gate(github, True)
        self.assertEqual(github.writes[0][1].state, "pending")
        # A later run still blocks after the comment has disappeared entirely.
        github = FakeGitHub([pull()], {1: [summary()]}, deleted={1: 11})
        self.run_gate(github, True)
        self.assertEqual(github.writes[0][1].state, "pending")

    def test_queue_heads_inherit_all_member_pr_verdicts(self):
        group = "d" * 40
        queues = {group: {1: HEAD, 2: OTHER_HEAD}}
        for second, expected in [([summary(OTHER_HEAD)], "success"),
                                 ([], "pending"),
                                 ([summary(OTHER_HEAD, has_any_findings=True)], "failure")]:
            github = FakeGitHub([pull(1), pull(2, OTHER_HEAD)],
                                {1: [summary()], 2: second}, queues=queues)
            with self.subTest(expected=expected):
                verdicts = self.run_gate(github, True, group)
                self.assertEqual(verdicts[group].state, expected)

    def test_unknown_queue_membership_and_moving_heads_do_not_pass(self):
        group = "d" * 40
        for queues in [{}, {group: {}}, {group: {2: HEAD}},
                       {group: {1: OTHER_HEAD}}]:
            github = FakeGitHub([pull()], {1: [summary()]}, queues=queues)
            with self.subTest(queues=queues):
                self.assertEqual(self.run_gate(github, True, group)[group].state,
                                 "pending")

    def test_a_nonqueued_duplicate_still_blocks_the_queue_group(self):
        group = "d" * 40
        github = FakeGitHub([pull(1), pull(2)], {1: [summary()], 2: []},
                            queues={group: {1: HEAD}})
        self.assertEqual(self.run_gate(github, True, group)[group].state, "pending")

    def test_dry_run_reads_live_inputs_without_writes(self):
        github = FakeGitHub([pull()], {1: [summary()]})
        self.assertEqual(self.run_gate(github)[HEAD].state, "success")
        self.assertEqual(github.writes, [])

    def test_event_coalescing_does_not_omit_unrelated_prs(self):
        github = FakeGitHub([pull(1), pull(2, OTHER_HEAD)],
                            {1: [summary()], 2: []})
        self.run_gate(github, True)
        self.assertEqual({head: result.state for head, result in github.writes},
                         {HEAD: "success", OTHER_HEAD: "pending"})

    def test_push_open_close_and_retarget_during_reads_cannot_publish_success(self):
        initial = [pull()]
        changed_base = pull()
        changed_base["base"]["sha"] = OTHER_HEAD
        for final in [[], [pull(1, OTHER_HEAD)], [pull(1), pull(2)],
                      [pull(base="another-branch")], [changed_base]]:
            github = FakeGitHub(initial, {1: [summary()]}, final)
            with self.subTest(final=final), self.assertRaises(RuntimeError):
                self.run_gate(github, True)
            self.assertEqual(github.writes, [(
                HEAD, Result("pending", "PR #1: PR snapshot changed or is unavailable"))])

    def test_api_failure_blocks_that_commit_and_preserves_other_evaluations(self):
        github = FakeGitHub([pull(1), pull(2, OTHER_HEAD)],
                            {1: OSError("API unavailable"), 2: [summary(OTHER_HEAD)]})
        with self.assertRaisesRegex(RuntimeError, "API unavailable"):
            self.run_gate(github, True)
        self.assertEqual({head: result.state for head, result in github.writes},
                         {HEAD: "failure", OTHER_HEAD: "success"})

    def test_new_head_can_never_receive_an_old_heads_success(self):
        github = FakeGitHub([pull(head=OTHER_HEAD)], {1: [summary()]})
        self.run_gate(github, True)
        self.assertEqual([(head, result.state) for head, result in github.writes],
                         [(OTHER_HEAD, "pending")])

    def test_stable_retarget_history_blocks_old_review_after_restart(self):
        github = FakeGitHub([pull()], {1: [summary()]},
                            bases={1: "2026-11-08T11:00:00Z"})
        self.assertEqual(self.run_gate(github, True)[HEAD].state, "pending")
        github = FakeGitHub([pull()], {1: [summary()]})
        with patch.object(github, "base_changes", side_effect=[
                {1: None}, {1: "2026-11-08T11:00:00Z"}]):
            with self.assertRaises(RuntimeError):
                self.run_gate(github, True)
        self.assertEqual(github.writes[0][1].state, "pending")
