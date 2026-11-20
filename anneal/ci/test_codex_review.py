# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exercise policy boundaries and publication using in-memory GitHub data."""

import copy
import io
import json
from pathlib import Path
import unittest
from unittest.mock import patch
from urllib.error import HTTPError

from codex_review import (
    BOT_ID, BOT_LOGIN, CONTEXT, PUBLISHER_LOGIN, GitHub, Result, combine_results,
    STATE_ANCHOR, reconcile, review_result,
)


HEAD = "a" * 40
OTHER_HEAD = "b" * 40
BASE = "c" * 40


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


class FakeGitHub:
    def __init__(self, initial, comments, final=None, changed_comments=None,
                 deleted=None, queues=None, bases=None):
        self.snapshots = [initial, initial if final is None else final]
        self.bodies = comments
        self.writes = []
        self.comment_reads = set()
        self.changed_comments = changed_comments or {}
        self.deleted = deleted or {}
        self.queues = queues or {}
        self.bases = {p["number"]: None for p in initial} if bases is None else bases

    def pulls(self):
        return copy.deepcopy(self.snapshots.pop(0))

    def comments(self, number):
        body = (self.changed_comments.get(number, self.bodies[number])
                if number in self.comment_reads else self.bodies[number])
        self.comment_reads.add(number)
        if isinstance(body, Exception):
            raise body
        return body

    def deleted_summaries(self):
        return self.deleted

    def queue_groups(self):
        return self.queues

    def base_changes(self):
        return self.bases

    def publish(self, head, result):
        self.writes.append((head, result))


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


class TransportTests(unittest.TestCase):
    def test_base_history_reads_retargets_and_force_pushes_before_gate_startup(self):
        github = GitHub("joshlf/anneal", "not-a-real-token")
        def page(nodes, more):
            return {"data": {"repository": {"pullRequests": {
                "nodes": nodes, "pageInfo": {"hasNextPage": more, "endCursor": "next"},
            }}}}
        responses = [page([{"number": 1, "timelineItems": {"nodes": []}}], True),
                     page([{"number": 2, "timelineItems": {"nodes": [
                         {"createdAt": "2026-11-08T11:00:00Z"}]}}], False)]
        with patch.object(github, "request_url", side_effect=responses) as query:
            self.assertEqual(github.base_changes(),
                             {1: None, 2: "2026-11-08T11:00:00Z"})
            self.assertIn("BASE_REF_FORCE_PUSHED_EVENT", query.call_args.args[1]["query"])
    def test_each_deletion_has_a_durable_independent_status_context(self):
        github = GitHub("joshlf/anneal", "not-a-real-token")
        event = {"action": "deleted", "issue": {"number": 1, "pull_request": True},
                 "comment": summary()}
        with patch.object(github, "publish_status") as publish:
            github.record_deletion(event)
            head, status = publish.call_args.args
            self.assertEqual(head, STATE_ANCHOR)
            self.assertEqual(status["context"], "Codex summary deletion/1/10")
            event["comment"]["id"] = 11
            github.record_deletion(event)
            self.assertEqual(publish.call_args.args[1]["context"],
                             "Codex summary deletion/1/11")
            event["comment"]["user"]["id"] += 1
            github.record_deletion(event)
            self.assertEqual(publish.call_count, 2)

    def test_deletion_journal_preserves_the_maximum_id_for_each_pr(self):
        github = GitHub("joshlf/anneal", "not-a-real-token")
        rows = [{"context": context, "state": "success", "creator": {"login": writer}}
                for context, writer in [
                    ("Codex summary deletion/1/12", PUBLISHER_LOGIN),
                    ("Codex summary deletion/1/10", PUBLISHER_LOGIN),
                    ("Codex summary deletion/2/9", PUBLISHER_LOGIN),
                    ("Codex summary deletion/1/99", "another-writer"),
                ]]
        with patch.object(github, "request", return_value=rows):
            self.assertEqual(github.deleted_summaries(), {1: 12, 2: 9})

    def test_queue_pagination_retains_the_full_prefix_for_generated_heads(self):
        github = GitHub("joshlf/anneal", "not-a-real-token")
        def entry(position, number, generated):
            return {"position": position,
                    "headCommit": {"oid": generated} if generated else None,
                    "pullRequest": {"number": number, "headRefOid": HEAD}}
        def page(entries, more):
            return {"data": {"repository": {"mergeQueue": {"entries": {
                "nodes": entries, "pageInfo": {"hasNextPage": more, "endCursor": "next"},
            }}}}}
        group = "d" * 40
        responses = [page([entry(1, 1, None)], True),
                     page([entry(3, 3, group), entry(2, 2, group)], False)]
        with patch.object(github, "request_url", side_effect=responses) as query:
            self.assertEqual(github.queue_groups(), {group: {1: HEAD, 2: HEAD, 3: HEAD}})
            self.assertEqual(query.call_args.args[1]["variables"]["after"], "next")
        with patch.object(github, "request_url", return_value={"errors": [{}]}):
            with self.assertRaises(RuntimeError):
                github.queue_groups()

    def test_retained_ruleset_is_disabled_and_keeps_actions_context(self):
        root = Path(__file__).resolve().parent.parent
        ruleset = json.loads((root / ".github/codex-review-ruleset.json").read_text())
        self.assertEqual(ruleset["enforcement"], "disabled")
        self.assertEqual(ruleset["conditions"]["ref_name"]["include"],
                         ["refs/heads/main"])
        required = ruleset["rules"][0]["parameters"]["required_status_checks"]
        self.assertEqual(required, [{"context": CONTEXT, "integration_id": 15368}])
        self.assertEqual(PUBLISHER_LOGIN, "github-actions[bot]")
        self.assertEqual(ruleset["bypass_actors"], [])

    def test_pagination_continues_past_a_full_page(self):
        github = GitHub("joshlf/anneal", "not-a-real-token")
        with patch.object(github, "request", side_effect=[list(range(100)), [100]]) as request:
            self.assertEqual(list(github.pages("pulls?state=open")), list(range(101)))
        self.assertEqual(request.call_args_list[1].args,
                         ("pulls?state=open&per_page=100&page=2",))

    def test_malformed_page_is_not_an_empty_result(self):
        github = GitHub("joshlf/anneal", "not-a-real-token")
        with patch.object(github, "request", return_value={"message": "Error"}):
            with self.assertRaises(ValueError):
                github.pulls()

    def test_status_is_written_to_the_evaluated_sha_and_repeated_results_are_noops(self):
        github = GitHub("joshlf/anneal", "not-a-real-token")
        with patch.object(github, "request", side_effect=[[], {}]) as request:
            github.publish(HEAD, Result("success", "Clean"))
        path, desired = request.call_args.args
        self.assertEqual(path, f"statuses/{HEAD}")
        self.assertEqual(desired["context"], CONTEXT)
        existing = dict(desired, creator={"login": PUBLISHER_LOGIN})
        with patch.object(github, "request", return_value=[existing]) as request:
            github.publish(HEAD, Result("success", "Clean"))
            self.assertEqual(request.call_count, 1)
        # A previous success must not suppress publication when the summary is
        # removed or a new review is running on the same commit.
        with patch.object(github, "request", side_effect=[[existing], {}]) as request:
            github.publish(HEAD, Result("pending", "Waiting"))
            self.assertEqual(request.call_args.args[1]["state"], "pending")
        existing["creator"]["login"] = "another-writer"
        with patch.object(github, "request", side_effect=[[existing], {}]) as request:
            github.publish(HEAD, Result("success", "Clean"))
            self.assertEqual(request.call_count, 2)

    def test_repository_text_cannot_change_the_api_host_or_path(self):
        for repository in ["../anneal", "joshlf/anneal/../x", "https://evil.invalid/x"]:
            with self.subTest(repository=repository), self.assertRaises(ValueError):
                GitHub(repository, "not-a-real-token")

    def test_transport_encodes_data_without_executing_or_logging_it(self):
        github = GitHub("joshlf/anneal", "not-a-real-token")
        with patch("codex_review.urlopen") as open_url:
            open_url.return_value.__enter__.return_value = io.BytesIO(b"{}")
            github.request(f"statuses/{HEAD}", {"description": "$(exit 99)"})
        request = open_url.call_args.args[0]
        self.assertEqual(request.full_url,
                         f"https://api.github.com/repos/joshlf/anneal/statuses/{HEAD}")
        self.assertEqual(json.loads(request.data), {"description": "$(exit 99)"})
        with patch("codex_review.urlopen", side_effect=HTTPError(
                request.full_url, 403, "Forbidden", {}, None)):
            with self.assertRaisesRegex(RuntimeError, "POST.*HTTP 403") as error:
                github.request(f"statuses/{HEAD}", {})
        self.assertNotIn("not-a-real-token", str(error.exception))


if __name__ == "__main__":
    unittest.main()
