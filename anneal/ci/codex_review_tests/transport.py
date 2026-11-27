# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`codex_review` tests for the GitHub transport."""

from .support import (
    CONTEXT,
    GitHub,
    HEAD,
    HTTPError,
    io,
    json,
    patch,
    Path,
    PUBLISHER_LOGIN,
    Result,
    STATE_ANCHOR,
    summary,
    unittest,
)


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
        root = Path(__file__).resolve().parent.parent.parent
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
