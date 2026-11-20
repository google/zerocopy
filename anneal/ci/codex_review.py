# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Evaluate managed Codex summaries and propose commit statuses.

The deployed workflow runs this standard-library adapter only as manually
dispatched, read-only diagnostics. The former publisher and deletion recorder
remain available for the research tracked in issue #236. Neither write mode
runs in that workflow. PR code and comment contents are never executed.
The default mode reads live inputs and prints proposed statuses. Explicit
--publish and --record-deletion retain the former gate's two write effects.
"""

import argparse
from collections import defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
import json
import io
import os
import re
import sys
from urllib.error import HTTPError
from urllib.request import Request, urlopen


CONTEXT = "Codex review"
# The gate uses the standard Actions token. Repository writers and ordinary
# review of workflow changes are trusted; no separate publisher is provisioned.
PUBLISHER_LOGIN = "github-actions[bot]"
# Pin the account ID as well as its display name. A copied marker or a similarly
# named account must not acquire authority to approve a revision.
BOT_ID = 199175422
BOT_LOGIN = "chatgpt-codex-connector[bot]"
SUMMARY = "<!-- codex-pull-request-review-summary"
STATE = "<!-- codex-review-state:"
# Deletions remove evidence from the comments API. Record each deletion as an
# immutable, uniquely named commit status on Anneal's initial commit. This
# stable anchor survives branch moves without needing a database, a new ref,
# contents-write permission, or a stored copy of the deleted prose.
STATE_ANCHOR = "8950b5afa6444859c21fb4d100e21dd283afb6d6"
DELETION_CONTEXT = "Codex summary deletion/"


@dataclass(frozen=True)
class Result:
    """A native commit-status state and the reason shown beside it."""

    state: str
    reason: str


def unique_object(pairs):
    """Reject ambiguous JSON rather than accepting the last duplicate key."""
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def authentic_summary(comment):
    """Authenticate the comment author, independently of the event sender."""
    user = comment.get("user") or {}
    return (user.get("id") == BOT_ID and user.get("login") == BOT_LOGIN
            and user.get("type") == "Bot"
            and SUMMARY in (comment.get("body") or ""))


def latest_summary(comments):
    """Use the same authoritative comment for policy and freshness checks."""
    return max((c for c in comments if authentic_summary(c)),
               key=lambda c: c["id"], default=None)


def summary_snapshot(comments):
    """Compare the decision's inputs, not unrelated old-comment activity.

    ID, creation time, and body determine policy. updated_at does not: a
    security-only update is not a new Code Review. Deleting or editing an older
    summary cannot change the verdict while the authoritative one survives.
    """
    latest = latest_summary(comments)
    return ((latest["id"], latest.get("created_at"), latest["body"])
            if latest is not None else None)


def timestamp(value):
    """Reject missing or naive times instead of guessing a comparison zone."""
    if not isinstance(value, str):
        raise ValueError("Expected an aware timestamp")
    parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    if parsed.utcoffset() is None:
        raise ValueError("Expected a timezone")
    return parsed.astimezone(timezone.utc)


def review_result(head, comments, deleted_through=0, base_changed_at=None):
    """Read the latest authentic summary; never fall back to an older success.

    The hidden v1 state is an observed integration format, not a documented
    OpenAI API contract. Recognize summary and state prefixes broadly enough to
    notice a replacement version, then require exactly the version understood
    here. A format change should stop merging and call for an adapter update.
    """
    latest = latest_summary(comments)
    if latest is None:
        return Result("pending", "Waiting for a Codex Review Summary")
    # Comment IDs order creation. An edit to an older summary must not make it
    # supersede a newer, possibly incomplete review summary.
    if latest["id"] <= deleted_through:
        return Result("pending", "A newer summary was deleted; request a new summary")
    body = latest["body"]
    markers = re.findall(r"<!-- codex-review-state:.*?-->", body, re.DOTALL)
    if (body.count(SUMMARY) != 1
            or "<!-- codex-pull-request-review-summary -->" not in body
            or body.count(STATE) != 1 or len(markers) != 1):
        return Result("failure", "Unrecognized or ambiguous Codex summary")
    match = re.fullmatch(r"<!-- codex-review-state:v1 (.*?) -->", markers[0],
                         re.DOTALL)
    if match is None:
        return Result("failure", "Unsupported Codex review-state version")
    try:
        payload = json.loads(match[1], object_pairs_hook=unique_object)
        review = payload["code_review"]
        if not isinstance(review, dict):
            raise ValueError("Code Review state is not an object")
    except (ValueError, TypeError, KeyError):
        return Result("failure", "Malformed Codex Code Review state")

    # Security Review has an independent verdict. A clean security result,
    # emoji, or prose receipt cannot fill in a missing Code Review verdict.
    if review.get("commit_sha") != head:
        return Result("pending", "Codex has not reviewed this head commit")
    if review.get("status") != "completed":
        return Result("pending", "Waiting for a completed Codex Code Review")
    # Identity checks distinguish JSON false from null, zero, and empty strings.
    # Resolving threads by hand is insufficient: has_any_findings must also be
    # false, so Codex must publish a clean result for this revision.
    if (review.get("has_any_findings") is not False
            or review.get("has_unresolved_findings") is not False):
        return Result("failure", "Codex findings remain or the verdict is unknown")
    if base_changed_at is not None:
        # The JSON identifies only the head. After a retarget or force-push of
        # the base, require a newly created summary and a Code Review result
        # newer than that event. Merely editing an old summary, or recreating
        # it for a security-only review, must not revive an old Code Review.
        # This deliberately requires a fresh comment after a base change;
        # updated_at is not evidence that Code Review itself ran again.
        rows = [line for line in body.splitlines()
                if re.match(r"^\|[^|]*\*\*Code Review\*\*\s*\|", line)]
        completed = re.findall(r'<relative-time datetime="([^"]+)">', rows[0]) \
            if len(rows) == 1 and "**Completed**" in rows[0] else []
        try:
            changed = timestamp(base_changed_at)
            created = timestamp(latest.get("created_at"))
            if (created <= changed or len(completed) != 1
                    or timestamp(completed[0]) < created):
                return Result("pending", "Base changed; request a new Code Review summary")
        except ValueError:
            return Result("failure", "Cannot establish review freshness after base change")
    return Result("success", "Codex completed Code Review with no findings")


def pull_snapshot(pulls):
    """Keep the PR identities that affect a commit's shared status."""
    return sorted((pull["number"], pull["head"]["sha"], pull["base"]["ref"],
                   pull["base"]["sha"]) for pull in pulls)


@dataclass(frozen=True)
class ReviewContext:
    """Comparable API observations, not an atomic GitHub transaction.

    Keep decision-relevant metadata together so adding another dependency also
    adds it to the final equality check. Summary bodies are rechecked separately
    so a comment read failure can block its PR without losing other verdicts.
    """

    pulls: tuple
    deleted: dict
    queues: dict
    bases: dict


def read_context(github, pulls=None):
    pulls = github.pulls() if pulls is None else pulls
    deleted = github.deleted_summaries()
    queues = github.queue_groups()
    bases = github.base_changes()
    numbers = {pull["number"] for pull in pulls}
    if set(bases) != numbers:
        raise RuntimeError("PR list and base history differ; recheck required")
    return ReviewContext(tuple(pull_snapshot(pulls)),
                         {n: deleted.get(n, 0) for n in numbers}, queues, bases)


def require_clean(results, success_reason):
    """Apply one all-members rule to shared heads and generated queue heads.

    Empty membership is unknown, never vacuous approval. Findings take
    precedence over waiting; any non-success result prevents success.
    """
    results = list(results)
    if not results:
        return Result("pending", "Unknown review membership")
    blockers = [result for result in results if result.state != "success"]
    if blockers:
        return next((r for r in blockers if r.state == "failure"), blockers[0])
    return Result("success", success_reason)


def combine_results(pulls, results):
    """Require each open PR sharing a commit to have its own clean result.

    A status belongs to a commit, not to a PR. Publishing independent answers
    under the same context lets the last PR overwrite the others. Group all
    open PRs, including drafts and stacks targeting other branches, so a clean
    review of one diff cannot supply a missing review of another diff.
    """
    groups = defaultdict(list)
    for pull in pulls:
        groups[pull["head"]["sha"]].append(pull["number"])
    combined = {}
    for head, numbers in groups.items():
        combined[head] = require_clean(
            (Result(results[n].state, f"PR #{n}: {results[n].reason}")
             for n in numbers),
            f"Clean Codex Code Review for all {len(numbers)} PR(s)")
    return combined


class GitHub:
    """The effect boundary: fixed-host API reads and commit-status writes."""

    def __init__(self, repository, token):
        if (not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]*/[A-Za-z0-9_.-]+", repository)
                or repository.split("/")[-1] in {".", ".."}):
            raise ValueError("Expected an owner/repository name")
        self.repository = repository
        self.root = f"https://api.github.com/repos/{repository}/"
        self.token = token

    def request(self, path, data=None):
        return self.request_url(self.root + path, data)

    def request_url(self, url, data=None):
        request = Request(url,
                          data=None if data is None else json.dumps(data).encode(),
                          headers={"Authorization": f"Bearer {self.token}",
                                   "Accept": "application/vnd.github+json",
                                   "Content-Type": "application/json",
                                   "X-GitHub-Api-Version": "2022-11-28"})
        try:
            with urlopen(request, timeout=30) as response:
                return json.load(response)
        except HTTPError as error:
            # Do not log request headers or retry an ambiguous status write.
            # A manual recheck recomputes the result instead of replaying it.
            raise RuntimeError(
                f"GitHub {request.get_method()}: HTTP {error.code}") from None

    def graphql(self, query, variables):
        # GraphQL can return errors with HTTP 200. Both metadata readers must
        # reject that response rather than interpret missing data as no work.
        response = self.request_url("https://api.github.com/graphql", {
            "query": query, "variables": variables,
        })
        data = response.get("data")
        if (response.get("errors") or not isinstance(data, dict)
                or not isinstance(data.get("repository"), dict)):
            raise RuntimeError("GitHub could not read review context")
        return data["repository"]

    def pages(self, path):
        separator = "&" if "?" in path else "?"
        page = 1
        while True:
            batch = self.request(f"{path}{separator}per_page=100&page={page}")
            if not isinstance(batch, list):
                raise ValueError("Expected a paginated GitHub array")
            yield from batch
            if len(batch) < 100:
                return
            page += 1

    def pulls(self):
        return list(self.pages("pulls?state=open&sort=created&direction=asc"))

    def comments(self, number):
        return list(self.pages(f"issues/{number}/comments"))

    def deleted_summaries(self):
        deleted = {}
        for status in self.pages(f"commits/{STATE_ANCHOR}/statuses"):
            match = re.fullmatch(r"Codex summary deletion/([1-9][0-9]*)/([1-9][0-9]*)",
                                 status["context"])
            if (match and status["state"] == "success"
                    and status.get("creator", {}).get("login") == PUBLISHER_LOGIN):
                number, comment = map(int, match.groups())
                deleted[number] = max(deleted.get(number, 0), comment)
        return deleted

    def record_deletion(self, event):
        """Record deletion events before they enter a coalescing job queue.

        A user may delete a bot comment, so authenticate the deleted comment's
        author, not the user who performed the deletion. Each event has a unique
        context: concurrent recorders cannot overwrite another deletion.
        """
        comment = event.get("comment") or {}
        issue = event.get("issue") or {}
        if (event.get("action") != "deleted" or not issue.get("pull_request")
                or not authentic_summary(comment)):
            return
        number, comment_id = issue["number"], comment["id"]
        self.publish_status(STATE_ANCHOR, {
            "context": f"{DELETION_CONTEXT}{number}/{comment_id}",
            "state": "success", "description": "Deleted Codex summary; older results cannot approve",
            "target_url": f"https://github.com/{self.repository}/pull/{number}",
        })

    def queue_groups(self):
        """Read the main queue's generated heads and their required PR prefix.

        GitHub's MergeQueueEntry exposes the generated headCommit for an entry,
        its queue position, and its pullRequest. A group may incorporate earlier
        entries, so require the entire prefix through that position, including
        entries which do not yet have a generated commit. Never infer membership
        from a branch name or assume squash commits retain PR ancestry.
        """
        owner, name = self.repository.split("/")
        query = """query($owner: String!, $name: String!, $after: String) {
          repository(owner: $owner, name: $name) {
            mergeQueue(branch: "main") { entries(first: 100, after: $after) {
              nodes { position headCommit { oid }
                pullRequest { number headRefOid } }
              pageInfo { hasNextPage endCursor }
            } }
          }
        }"""
        entries, after = [], None
        while True:
            queue = self.graphql(query, {
                "owner": owner, "name": name, "after": after,
            })["mergeQueue"]
            if queue is None:
                return {}
            page = queue["entries"]
            entries.extend(page["nodes"])
            if not page["pageInfo"]["hasNextPage"]:
                break
            after = page["pageInfo"]["endCursor"]
        prefix, groups = {}, {}
        for entry in sorted(entries, key=lambda entry: entry["position"]):
            pull = entry["pullRequest"]
            prefix[pull["number"]] = pull["headRefOid"]
            if entry["headCommit"] is not None:
                head = entry["headCommit"]["oid"]
                groups.setdefault(head, {}).update(prefix)
        return groups

    def base_changes(self):
        """Read immutable base-change events, including changes before startup.

        A stable base in two consecutive API reads does not prove that an old
        review used that base. GitHub's PR timeline supplies the last retarget
        or base force-push even when no gate was deployed when it happened.
        """
        owner, name = self.repository.split("/")
        query = """query($owner: String!, $name: String!, $after: String) {
          repository(owner: $owner, name: $name) {
            pullRequests(states: OPEN, first: 100, after: $after) {
              nodes { number timelineItems(last: 1,
                itemTypes: [BASE_REF_CHANGED_EVENT, BASE_REF_FORCE_PUSHED_EVENT]) {
                nodes { ... on BaseRefChangedEvent { createdAt }
                        ... on BaseRefForcePushedEvent { createdAt } }
              } }
              pageInfo { hasNextPage endCursor }
            }
          }
        }"""
        changes, after = {}, None
        while True:
            page = self.graphql(query, {
                "owner": owner, "name": name, "after": after,
            })["pullRequests"]
            for pull in page["nodes"]:
                events = pull["timelineItems"]["nodes"]
                changes[pull["number"]] = events[-1]["createdAt"] if events else None
            if not page["pageInfo"]["hasNextPage"]:
                return changes
            after = page["pageInfo"]["endCursor"]

    def publish(self, head, result):
        # Use the SHA evaluated, never a branch name that could have advanced.
        # The Actions job's own check belongs to its default-branch checkout;
        # this explicit status is what branch protection requires on the PR.
        desired = {
            "context": CONTEXT, "state": result.state,
            "description": result.reason[:140],
            "target_url": f"https://github.com/{self.repository}/actions/workflows/codex-review.yml",
        }
        self.publish_status(head, desired)

    def publish_status(self, head, desired):
        # GitHub limits the number of statuses per commit and context. An
        # unrelated PR's event must not consume another entry for an unchanged
        # verdict. The API returns statuses newest first; stop at this context.
        current = next((status for status in self.pages(f"commits/{head}/statuses")
                        if status["context"].casefold() == desired["context"].casefold()), {})
        if (current.get("creator", {}).get("login") == PUBLISHER_LOGIN
                and all(current.get(key) == value
                        for key, value in desired.items())):
            return
        self.request(f"statuses/{head}", desired)


def publish_results(github, results, publish):
    """Use the same reporting path for normal verdicts and failed reads."""
    for head, result in sorted(results.items()):
        print(f"{head}: {result.state}: {result.reason}")
        if publish:
            github.publish(head, result)


def reconcile(github, publish=False, requested_group=None):
    """Recompute every open PR, because serialized event runs can be coalesced.

    GitHub may replace a pending concurrency-group run with a newer one. Since
    every run reads all open PRs, the retained run also covers the discarded
    event. Deletion tombstones are recorded separately before coalescing, since
    the comments API alone cannot recover a deleted summary's existence.
    """
    pulls = github.pulls()
    try:
        context = read_context(github, pulls)
    except (RuntimeError, ValueError, OSError) as error:
        # A partial API outage must not preserve success merely because the
        # metadata failed before comment evaluation. Revoke known heads when
        # the status API remains available, then expose the operational error.
        blocked = {pull["head"]["sha"]: Result("pending", "Review context unavailable")
                   for pull in pulls}
        if requested_group:
            blocked[requested_group] = Result("pending", "Review context unavailable")
        publish_results(github, blocked, publish)
        raise RuntimeError(str(error)) from None
    comments = {}
    results = {}
    read_errors = []
    for pull in pulls:
        number = pull["number"]
        try:
            comments[number] = github.comments(number)
            results[number] = review_result(
                pull["head"]["sha"], comments[number],
                context.deleted.get(number, 0), context.bases[number])
        except (RuntimeError, ValueError, OSError) as error:
            # A failed read replaces old success with a blocking verdict where
            # the status API remains available. Other PRs are still evaluated.
            results[number] = Result("failure", "Cannot read Codex summary")
            read_errors.append(f"PR #{number}: {error}")
    # A push, retarget, newly opened PR, or closure can change grouping while
    # comments are read. Leave statuses pending and let the queued event (or a
    # manual recheck) read a new snapshot rather than publish a mixed snapshot.
    try:
        if context != read_context(github):
            raise RuntimeError("Review context changed during evaluation")
        for number, original in comments.items():
            # PR metadata does not change when Codex edits its summary. Include
            # that evidence in the final read, rather than revalidating only the
            # commit graph and accidentally accepting a superseded verdict.
            if summary_snapshot(original) != summary_snapshot(github.comments(number)):
                results[number] = Result("pending", "Codex summary changed; recheck required")
    except (RuntimeError, ValueError, OSError) as error:
        results = {pull["number"]: Result("pending", "PR snapshot changed or is unavailable")
                   for pull in pulls}
        read_errors.append(str(error))
    pr_verdicts = combine_results(pulls, results)
    combined = dict(pr_verdicts)
    by_number = {pull["number"]: pull for pull in pulls}
    for head, members in context.queues.items():
        queue_results = []
        for number, expected_head in members.items():
            pull = by_number.get(number)
            if pull is None or pull["head"]["sha"] != expected_head:
                queue_results.append(Result("pending", "Merge queue PR head changed"))
            else:
                queue_results.append(pr_verdicts[expected_head])
        # Use shared-head verdicts so queueing one PR cannot bypass a blocked
        # duplicate. An empty or unknown queue membership never passes.
        combined[head] = require_clean(
            queue_results, "Clean Codex reviews for the merge queue group")
    if requested_group and requested_group not in context.queues:
        combined[requested_group] = Result("pending", "Merge queue membership is not available; recheck")
    publish_results(github, combined, publish)
    if read_errors:
        raise RuntimeError("; ".join(read_errors))
    return combined


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", default=os.environ.get("GITHUB_REPOSITORY"))
    effects = parser.add_mutually_exclusive_group()
    effects.add_argument("--publish", action="store_true")
    effects.add_argument("--record-deletion", action="store_true")
    args = parser.parse_args()
    token = os.environ.get("GH_TOKEN")
    if not args.repository or not token:
        parser.error("Supply --repository and GH_TOKEN")
    github = GitHub(args.repository, token)
    event_path = os.environ.get("GITHUB_EVENT_PATH")
    with open(event_path, encoding="utf-8") if event_path else io.StringIO("{}") as source:
        event = json.load(source)
    if args.record_deletion:
        github.record_deletion(event)
    else:
        group = (event.get("merge_group") or {}).get("head_sha")
        reconcile(github, args.publish, group)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, OSError) as error:
        sys.exit(str(error))
