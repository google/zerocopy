# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""The `gh` GraphQL adapter (`GitHubCli`) for `issue_hygiene`."""

from __future__ import annotations

from collections.abc import Callable
import json
import subprocess
import sys
import time
from typing import Iterable, Mapping, Sequence

from .model import (
    Action,
    AddLabels,
    Blocker,
    ClearMilestone,
    DEFAULT_GRAPHQL_TIMEOUT_SECONDS,
    ExternalIssueRef,
    Issue,
    Milestone,
    RETRY_BACKOFF_SECONDS,
    RefState,
    RemoveLabels,
    SetIssueType,
    _MAX_GRAPHQL_INT,
    _SAFE_SLUG_RE,
    _TRANSIENT_ERR_PATTERNS,
    _TRANSIENT_GQL_TYPES,
    _format_action,
)


def _is_transient_graphql_failure(
    stderr: str, errors: Sequence[Mapping[str, object]]
) -> bool:
    lower_err = stderr.lower()
    if any(pat in lower_err for pat in _TRANSIENT_ERR_PATTERNS):
        return True
    for err in errors:
        err_type = err.get("type")
        if isinstance(err_type, str) and err_type in _TRANSIENT_GQL_TYPES:
            return True
        msg = err.get("message")
        if isinstance(msg, str) and any(
            pat in msg.lower() for pat in _TRANSIENT_ERR_PATTERNS
        ):
            return True
    return False


class GitHubCli:
    """Thin GraphQL adapter over `gh` for read and Tier 1 write operations."""

    def __init__(
        self,
        owner: str,
        repo: str,
        *,
        timeout: float = DEFAULT_GRAPHQL_TIMEOUT_SECONDS,
        sleep_fn: Callable[[float], None] | None = None,
    ) -> None:
        if timeout <= 0:
            raise ValueError(f"timeout must be positive: {timeout}")
        self.owner = owner
        self.repo = repo
        self.timeout = timeout
        self._sleep = sleep_fn
        self._slug_lower = f"{owner}/{repo}".lower()

    def _do_sleep(self, delay: float) -> None:
        if self._sleep is not None:
            self._sleep(delay)
        else:
            time.sleep(delay)

    def graphql(
        self,
        query: str,
        variables: Mapping[str, object] | None = None,
        *,
        allow_not_found: bool = False,
    ) -> dict[str, object]:
        """Execute a GraphQL operation with timeout and transient retries.

        Retries assume idempotent operations (true for all current read
        queries and label/type/milestone mutations). Any future
        non-idempotent mutation (e.g. `addComment`) must explicitly opt out
        of retries on unknown/timed-out outcomes.
        """
        payload = json.dumps(
            {"query": query, "variables": dict(variables or {})}
        )
        attempts = len(RETRY_BACKOFF_SECONDS) + 1
        last_error: RuntimeError | None = None
        for attempt in range(attempts):
            try:
                proc = subprocess.run(
                    ["gh", "api", "graphql", "--input", "-"],
                    input=payload,
                    text=True,
                    capture_output=True,
                    check=False,
                    timeout=self.timeout,
                )
            except subprocess.TimeoutExpired as exc:
                raw_err = exc.stderr
                if isinstance(raw_err, bytes):
                    stderr = raw_err.decode("utf-8", errors="replace").strip()
                else:
                    stderr = (raw_err or "").strip()
                detail = f": {stderr}" if stderr else ""
                last_error = RuntimeError(
                    f"gh api graphql timed out after {self.timeout}s{detail}"
                )
                if attempt < len(RETRY_BACKOFF_SECONDS):
                    self._do_sleep(RETRY_BACKOFF_SECONDS[attempt])
                    continue
                raise last_error from exc

            data, retryable, err = self._parse_graphql_response(
                proc, allow_not_found=allow_not_found
            )
            if data is not None:
                return data
            last_error = err
            if retryable and attempt < len(RETRY_BACKOFF_SECONDS):
                self._do_sleep(RETRY_BACKOFF_SECONDS[attempt])
                continue
            raise last_error
        raise last_error or RuntimeError("GraphQL request failed")

    def _parse_graphql_response(
        self,
        proc: subprocess.CompletedProcess[str],
        *,
        allow_not_found: bool,
    ) -> tuple[dict[str, object] | None, bool, RuntimeError]:
        raw_out = proc.stdout.strip()
        stderr = proc.stderr.strip()
        if not raw_out:
            err = RuntimeError(
                f"gh api graphql returned empty output (exit {proc.returncode})"
                f": {stderr or 'no stderr'}"
            )
            return None, _is_transient_graphql_failure(stderr, ()), err

        try:
            parsed = json.loads(raw_out)
        except json.JSONDecodeError as exc:
            snippet = raw_out[:200] + ("..." if len(raw_out) > 200 else "")
            err = RuntimeError(
                f"gh api graphql returned invalid JSON (exit {proc.returncode})"
                f": {exc}; stderr={stderr or 'none'}; stdout={snippet!r}"
            )
            retryable = _is_transient_graphql_failure(
                f"{stderr}\n{raw_out[:500]}", ()
            )
            return None, retryable, err

        if not isinstance(parsed, dict):
            return (
                None,
                False,
                RuntimeError("gh api graphql returned non-object JSON"),
            )

        raw_errors = parsed.get("errors")
        errors: list[Mapping[str, object]] = []
        if raw_errors is not None:
            if not isinstance(raw_errors, list) or not all(
                isinstance(e, Mapping) for e in raw_errors
            ):
                return (
                    None,
                    False,
                    RuntimeError(
                        f"Malformed GraphQL `errors` field: {raw_errors!r}"
                    ),
                )
            errors = list(raw_errors)

        only_allowed_not_found = (
            allow_not_found
            and bool(errors)
            and all(e.get("type") == "NOT_FOUND" for e in errors)
        )
        top_msg = parsed.get("message")
        err_context = (
            f"{stderr}\n{top_msg}" if isinstance(top_msg, str) else stderr
        )

        if errors and not only_allowed_not_found:
            err = RuntimeError(f"GraphQL errors: {errors}")
            return (
                None,
                _is_transient_graphql_failure(err_context, errors),
                err,
            )

        data = parsed.get("data")
        if proc.returncode != 0 and not (
            allow_not_found and data is not None
        ):
            err = RuntimeError(
                f"gh api graphql exited {proc.returncode}: "
                f"{stderr or raw_out}"
            )
            return (
                None,
                _is_transient_graphql_failure(err_context, errors),
                err,
            )

        if not isinstance(data, dict):
            if allow_not_found:
                return {}, False, RuntimeError("unreachable")
            err = RuntimeError("GraphQL response missing `data` object")
            return (
                None,
                _is_transient_graphql_failure(err_context, errors),
                err,
            )

        return data, False, RuntimeError("unreachable")

    def _require_repo(self, data: Mapping[str, object]) -> dict[str, object]:
        repo_obj = data.get("repository")
        if not isinstance(repo_obj, dict):
            raise RuntimeError(f"Repository {self.owner}/{self.repo} not found")
        return repo_obj

    def _is_same_repo(self, node: Mapping[str, object]) -> bool:
        repo_obj = node.get("repository")
        if not isinstance(repo_obj, Mapping):
            return False
        nwo = repo_obj.get("nameWithOwner")
        return isinstance(nwo, str) and nwo.lower() == self._slug_lower

    def _paginate_repo_conn(
        self, field_name: str, args_str: str, node_selection: str
    ) -> list[dict[str, object]]:
        nodes: list[dict[str, object]] = []
        cursor: str | None = None
        query = (
            "query($owner: String!, $repo: String!, $after: String) {"
            "  repository(owner: $owner, name: $repo) {"
            f"    {field_name}({args_str}, after: $after) {{"
            "      pageInfo { hasNextPage endCursor }"
            f"      nodes {{ {node_selection} }}"
            "    }"
            "  }"
            "}"
        )
        while True:
            repo_obj = self._require_repo(
                self.graphql(
                    query,
                    {"owner": self.owner, "repo": self.repo, "after": cursor},
                )
            )
            conn = repo_obj.get(field_name)
            if conn is None:
                return nodes
            if not isinstance(conn, Mapping):
                raise RuntimeError(
                    f"Unexpected `{field_name}` connection payload"
                )
            raw_nodes = conn.get("nodes") or ()
            nodes.extend(n for n in raw_nodes if isinstance(n, dict))
            pi = conn.get("pageInfo")
            if not isinstance(pi, Mapping) or not pi.get("hasNextPage"):
                break
            if not pi.get("endCursor"):
                raise RuntimeError(
                    f"Missing `endCursor` while paginating `{field_name}`"
                )
            cursor = str(pi["endCursor"])
        return nodes

    def _paginate_issue_conn(
        self,
        issue_id: str,
        field_name: str,
        node_selection: str,
        initial_conn: object,
    ) -> list[dict[str, object] | None]:
        if initial_conn is None:
            return []
        if not isinstance(initial_conn, Mapping):
            raise RuntimeError(
                f"Unexpected `{field_name}` connection on {issue_id}"
            )
        raw_nodes = initial_conn.get("nodes") or ()
        nodes: list[dict[str, object] | None] = [
            n if isinstance(n, dict) else None for n in raw_nodes
        ]
        pi = initial_conn.get("pageInfo")
        if isinstance(pi, Mapping) and pi.get("hasNextPage"):
            if not pi.get("endCursor"):
                raise RuntimeError(
                    f"Missing `endCursor` on {issue_id} `{field_name}`"
                )
            cursor: str | None = str(pi["endCursor"])
        else:
            cursor = None
        while cursor is not None:
            data = self.graphql(
                "query($id: ID!, $after: String) { node(id: $id) { ... on Issue"
                f" {{ {field_name}(first: 100, after: $after) {{"
                " pageInfo { hasNextPage endCursor }"
                f" nodes {{ {node_selection} }} }} }} }} }}",
                {"id": issue_id, "after": cursor},
            )
            node_obj = data.get("node")
            if not isinstance(node_obj, Mapping):
                raise RuntimeError(
                    f"Missing node {issue_id} while paginating {field_name}"
                )
            conn = node_obj.get(field_name)
            if conn is None:
                break
            if not isinstance(conn, Mapping):
                raise RuntimeError(
                    f"Unexpected `{field_name}` page on {issue_id}"
                )
            page_nodes = conn.get("nodes") or ()
            nodes.extend(n if isinstance(n, dict) else None for n in page_nodes)
            pi = conn.get("pageInfo")
            if isinstance(pi, Mapping) and pi.get("hasNextPage"):
                if not pi.get("endCursor"):
                    raise RuntimeError(
                        f"Missing `endCursor` on {issue_id} `{field_name}`"
                    )
                cursor = str(pi["endCursor"])
            else:
                cursor = None
        return nodes

    def fetch_metadata(self) -> tuple[dict[str, str], dict[str, str]]:
        """Return paginated `(label_name -> id, issue_type_name -> id)`."""
        label_nodes = self._paginate_repo_conn(
            "labels", "first: 100", "id name"
        )
        type_nodes = self._paginate_repo_conn(
            "issueTypes", "first: 50", "id name isEnabled"
        )
        labels = {str(n["name"]): str(n["id"]) for n in label_nodes}
        types = {
            str(n["name"]): str(n["id"])
            for n in type_nodes
            if n.get("isEnabled")
        }
        return labels, types

    def fetch_open_issues(self) -> tuple[Issue, ...]:
        issue_nodes = self._paginate_repo_conn(
            "issues",
            "states: [OPEN], first: 100, "
            "orderBy: {field: CREATED_AT, direction: ASC}",
            """id number title body
            issueType { name }
            milestone { title state }
            labels(first: 30) {
              pageInfo { hasNextPage endCursor }
              nodes { name }
            }
            parent { number repository { nameWithOwner } }
            subIssues(first: 50) {
              pageInfo { hasNextPage endCursor }
              nodes { number repository { nameWithOwner } }
            }
            subIssuesSummary { total }
            blockedBy(first: 30) {
              pageInfo { hasNextPage endCursor }
              nodes { number state repository { nameWithOwner } }
            }
            relatesTo(first: 30) {
              pageInfo { hasNextPage endCursor }
              nodes { number repository { nameWithOwner } }
            }""",
        )
        issues: list[Issue] = []
        for n in issue_nodes:
            iid = str(n["id"])
            label_nodes = self._paginate_issue_conn(
                iid, "labels", "name", n.get("labels")
            )
            sub_nodes = self._paginate_issue_conn(
                iid,
                "subIssues",
                "number repository { nameWithOwner }",
                n.get("subIssues"),
            )
            blocker_nodes = self._paginate_issue_conn(
                iid,
                "blockedBy",
                "number state repository { nameWithOwner }",
                n.get("blockedBy"),
            )
            rel_nodes = self._paginate_issue_conn(
                iid,
                "relatesTo",
                "number repository { nameWithOwner }",
                n.get("relatesTo"),
            )
            parent = n.get("parent")
            parent_num = (
                int(str(parent["number"]))
                if isinstance(parent, Mapping) and self._is_same_repo(parent)
                else None
            )
            ms = n.get("milestone")
            milestone = (
                Milestone(str(ms["title"]), str(ms["state"]))
                if isinstance(ms, Mapping)
                else None
            )
            blockers: list[Blocker] = []
            for b in blocker_nodes:
                if b is None:
                    # Preserve inaccessible/private blockers as UNKNOWN so
                    # `resolved-blockers` never falsely fires.
                    blockers.append(Blocker("<inaccessible>", "UNKNOWN", None))
                    continue
                state = str(b["state"])
                if self._is_same_repo(b):
                    num = int(str(b["number"]))
                    blockers.append(Blocker(f"#{num}", state, num))
                else:
                    r = b.get("repository")
                    nwo = r["nameWithOwner"] if isinstance(r, Mapping) else "?"
                    ref = f"{nwo}#{b['number']}"
                    blockers.append(Blocker(ref, state, None))
            it = n.get("issueType")
            issue_type = str(it["name"]) if isinstance(it, Mapping) else None
            summary = n.get("subIssuesSummary")
            sub_total = (
                int(str(summary["total"]))
                if isinstance(summary, Mapping)
                else 0
            )
            if any(x is None for x in label_nodes):
                raise RuntimeError(
                    f"Unexpected null label node on issue #{n['number']}"
                )
            issues.append(
                Issue(
                    node_id=iid,
                    number=int(str(n["number"])),
                    title=str(n["title"]),
                    body=str(n.get("body") or ""),
                    labels=frozenset(
                        str(x["name"]) for x in label_nodes if x is not None
                    ),
                    issue_type=issue_type,
                    milestone=milestone,
                    parent_number=parent_num,
                    sub_issues=frozenset(
                        int(str(x["number"]))
                        for x in sub_nodes
                        if x is not None and self._is_same_repo(x)
                    ),
                    has_sub_issues=sub_total > 0,
                    blocked_by=tuple(blockers),
                    relates_to=frozenset(
                        int(str(x["number"]))
                        for x in rel_nodes
                        if x is not None and self._is_same_repo(x)
                    ),
                )
            )
        return tuple(issues)

    def fetch_refs(self, numbers: Iterable[int]) -> dict[int, RefState]:
        nums = sorted({n for n in numbers if 0 < n <= _MAX_GRAPHQL_INT})
        result: dict[int, RefState] = {}
        for idx in range(0, len(nums), 50):
            chunk = nums[idx : idx + 50]
            fields = "\n".join(
                f"r{n}: issueOrPullRequest(number: {n}) {{ __typename "
                "... on Issue { state } ... on PullRequest { state } }"
                for n in chunk
            )
            query = (
                "query($owner: String!, $repo: String!) { "
                f"repository(owner: $owner, name: $repo) {{\n{fields}\n}} }}"
            )
            data = self.graphql(
                query,
                {"owner": self.owner, "repo": self.repo},
                allow_not_found=True,
            )
            repo_data = data.get("repository")
            if not isinstance(repo_data, Mapping):
                continue
            for n in chunk:
                item = repo_data.get(f"r{n}")
                if isinstance(item, Mapping) and item.get("__typename") in (
                    "Issue",
                    "PullRequest",
                ):
                    result[n] = RefState(
                        str(item["__typename"]), str(item["state"])
                    )
        return result

    def fetch_external_states(
        self, refs: Iterable[ExternalIssueRef]
    ) -> dict[tuple[str, str, int], str]:
        unique_by_key: dict[tuple[str, str, int], tuple[str, str, int]] = {}
        for r in refs:
            if (
                _SAFE_SLUG_RE.match(r.owner)
                and _SAFE_SLUG_RE.match(r.repo)
                and 0 < r.number <= _MAX_GRAPHQL_INT
            ):
                unique_by_key.setdefault(r.key, (r.owner, r.repo, r.number))
        items = sorted(unique_by_key.items())
        states: dict[tuple[str, str, int], str] = {}
        for idx in range(0, len(items), 25):
            chunk = items[idx : idx + 25]
            var_decls: list[str] = []
            blocks: list[str] = []
            variables: dict[str, object] = {}
            for i, (_, (ow, rp, num)) in enumerate(chunk):
                var_decls.append(
                    f"$ow{i}: String!, $rp{i}: String!, $num{i}: Int!"
                )
                blocks.append(
                    f"e{i}: repository(owner: $ow{i}, name: $rp{i}) "
                    f"{{ issue(number: $num{i}) {{ state }} }}"
                )
                variables[f"ow{i}"] = ow
                variables[f"rp{i}"] = rp
                variables[f"num{i}"] = num
            query = (
                f"query({', '.join(var_decls)}) {{\n"
                + "\n".join(blocks)
                + "\n}"
            )
            data = self.graphql(query, variables, allow_not_found=True)
            for i, (key, _) in enumerate(chunk):
                repo_obj = data.get(f"e{i}")
                if isinstance(repo_obj, Mapping):
                    issue_obj = repo_obj.get("issue")
                    if isinstance(issue_obj, Mapping) and issue_obj.get(
                        "state"
                    ):
                        states[key] = str(issue_obj["state"])
        return states

    def apply_actions(
        self, actions: Sequence[Action], issues_by_num: Mapping[int, Issue]
    ) -> None:
        """Pre-validate all IDs, then apply Tier 1 mutations."""
        if not actions:
            return
        label_ids, type_ids = self.fetch_metadata()

        # Fail closed before any mutation if an issue, label, or type is absent.
        missing_issues = sorted(
            {a.number for a in actions if a.number not in issues_by_num}
        )
        missing_labels = sorted(
            {
                lbl
                for a in actions
                if isinstance(a, (AddLabels, RemoveLabels))
                for lbl in a.labels
                if lbl not in label_ids
            }
        )
        missing_types = sorted(
            {
                a.issue_type
                for a in actions
                if isinstance(a, SetIssueType) and a.issue_type not in type_ids
            }
        )
        problems: list[str] = []
        if missing_issues:
            problems.append(f"unknown issues: {missing_issues}")
        if missing_labels:
            problems.append(f"unknown labels on repo: {missing_labels}")
        if missing_types:
            problems.append(f"unknown issue types on repo: {missing_types}")
        if problems:
            raise RuntimeError(
                "Aborting before any mutation (" + "; ".join(problems) + ")"
            )

        total = len(actions)
        for idx, act in enumerate(actions, start=1):
            iss = issues_by_num[act.number]
            try:
                if isinstance(act, (AddLabels, RemoveLabels)):
                    mut = (
                        "addLabelsToLabelable"
                        if isinstance(act, AddLabels)
                        else "removeLabelsFromLabelable"
                    )
                    self.graphql(
                        f"mutation($id: ID!, $lids: [ID!]!) {{ {mut}"
                        "(input: {labelableId: $id, labelIds: $lids})"
                        " { clientMutationId } }",
                        {
                            "id": iss.node_id,
                            "lids": [label_ids[l] for l in act.labels],
                        },
                    )
                elif isinstance(act, SetIssueType):
                    self.graphql(
                        "mutation($id: ID!, $tid: ID!) { updateIssueIssueType"
                        "(input: {issueId: $id, issueTypeId: $tid})"
                        " { issue { number } } }",
                        {"id": iss.node_id, "tid": type_ids[act.issue_type]},
                    )
                elif isinstance(act, ClearMilestone):
                    self.graphql(
                        "mutation($id: ID!) { updateIssue"
                        "(input: {id: $id, milestoneId: null})"
                        " { issue { number } } }",
                        {"id": iss.node_id},
                    )
                else:
                    raise TypeError(f"Unsupported action: {type(act)!r}")
            except Exception as exc:
                raise RuntimeError(
                    f"Applied {idx - 1}/{total} actions before failure on "
                    f"{_format_action(act)}: {exc}"
                ) from exc
            print(
                f"[applied {idx}/{total}] {_format_action(act)}",
                file=sys.stderr,
            )
