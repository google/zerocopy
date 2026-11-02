#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Deterministic simulation probe for GHerrit batched GraphQL PR creation.

Models the interaction between:
1. `joshlf/gherrit`'s `BatchPlan` and `classify_response`
   (`src/pre_push/batching.rs:5-93` and `src/pre_push/mod.rs:397-786` at
   commits `2dbcbb6174ac3cf75dd7fcd0ab15cb27027b405d` and
   `86179afb27feabd50ddd7d2dc2493892885db8ba`), and
2. GitHub's GraphQL `createPullRequest` serial mutation execution when a
   49-commit stack exceeds per-request GraphQL resource limits after committing
   the first K = 16 pull requests on the server.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import json
import sys
from typing import Any

INITIAL_GRAPHQL_BATCH_LEN = 64
PATCHED_CREATE_PR_BATCH_LEN = 12


@dataclass
class PullRequestRecord:
    number: int
    node_id: str
    head_branch: str
    base_branch: str
    title: str
    body: str
    state: str = "OPEN"

    @property
    def url(self) -> str:
        return f"https://github.com/owner/repo/pull/{self.number}"


@dataclass
class SimulatedGitHubServer:
    """Stateful GraphQL server executing mutations serially in document order."""

    create_limit_per_request: int = 16
    small_batch_bonus_threshold: int | None = None
    partial_data_on_limit: bool = False
    prs_by_head: dict[str, PullRequestRecord] = field(default_factory=dict)
    next_pr_number: int = 1
    request_log: list[dict[str, Any]] = field(default_factory=list)

    def _effective_create_limit(self, batch_size: int) -> int:
        if (
            self.small_batch_bonus_threshold is not None
            and batch_size <= self.small_batch_bonus_threshold
        ):
            return self.create_limit_per_request + 1
        return self.create_limit_per_request

    def execute_find_prs(self, head_branches: list[str]) -> dict[str, Any]:
        data: dict[str, Any] = {}
        for idx, head in enumerate(head_branches):
            pr = self.prs_by_head.get(head)
            nodes = (
                [
                    {
                        "number": pr.number,
                        "id": pr.node_id,
                        "title": pr.title,
                        "body": pr.body,
                        "baseRefName": pr.base_branch,
                        "state": pr.state,
                        "isCrossRepository": False,
                    }
                ]
                if pr is not None
                else []
            )
            data[f"op{idx}"] = {
                "open": {"nodes": nodes, "pageInfo": {"hasNextPage": False}},
                "historical": {"nodes": [], "pageInfo": {"hasNextPage": False}},
            }
        self.request_log.append(
            {
                "kind": "FindPullRequest",
                "batch_size": len(head_branches),
                "heads": [head_branches[0], head_branches[-1]],
                "result": "SUCCESS",
            }
        )
        return {"data": data}

    def execute_create_prs(
        self, creations: list[dict[str, str]]
    ) -> dict[str, Any]:
        limit = self._effective_create_limit(len(creations))
        data: dict[str, Any] = {}
        errors: list[dict[str, Any]] = []
        created_in_request: list[str] = []

        for idx, item in enumerate(creations):
            alias = f"op{idx}"
            head = item["head_branch"]

            if idx >= limit:
                errors.append(
                    {
                        "type": "RESOURCE_LIMITS_EXCEEDED",
                        "path": [alias],
                        "message": (
                            "Wait a few minutes before you try again; "
                            "Exceeded GraphQL resource limits"
                        ),
                    }
                )
                for rem_idx in range(idx, len(creations)):
                    data[f"op{rem_idx}"] = None
                break

            if head in self.prs_by_head:
                data[alias] = None
                errors.append(
                    {
                        "type": "UNPROCESSABLE",
                        "path": [alias],
                        "message": (
                            f"A pull request already exists for owner:{head}."
                        ),
                    }
                )
                for rem_idx in range(idx + 1, len(creations)):
                    data[f"op{rem_idx}"] = None
                break

            number = self.next_pr_number
            self.next_pr_number += 1
            pr = PullRequestRecord(
                number=number,
                node_id=f"PR_{number}",
                head_branch=head,
                base_branch=item["base_branch"],
                title=item["title"],
                body=item["body"],
            )
            self.prs_by_head[head] = pr
            created_in_request.append(head)
            data[alias] = {
                "pullRequest": {
                    "number": pr.number,
                    "url": pr.url,
                    "id": pr.node_id,
                }
            }

        has_resource_error = any(
            e.get("type") == "RESOURCE_LIMITS_EXCEEDED" for e in errors
        )
        if has_resource_error and not self.partial_data_on_limit:
            response: dict[str, Any] = {"data": None, "errors": errors}
        elif errors:
            response = {"data": data, "errors": errors}
        else:
            response = {"data": data}

        self.request_log.append(
            {
                "kind": "CreatePullRequest",
                "batch_size": len(creations),
                "range_heads": [
                    creations[0]["head_branch"],
                    creations[-1]["head_branch"],
                ],
                "committed_count": len(created_in_request),
                "committed_heads": (
                    [created_in_request[0], created_in_request[-1]]
                    if created_in_request
                    else []
                ),
                "total_prs_on_server": len(self.prs_by_head),
                "errors": [
                    {"type": e.get("type"), "message": e.get("message")}
                    for e in errors
                ],
                "data_is_null": response.get("data") is None,
            }
        )
        return response

    def execute_update_prs(
        self, updates: list[dict[str, str]]
    ) -> dict[str, Any]:
        data: dict[str, Any] = {}
        for idx, upd in enumerate(updates):
            node_id = upd["node_id"]
            matched = next(
                (
                    pr
                    for pr in self.prs_by_head.values()
                    if pr.node_id == node_id
                ),
                None,
            )
            assert matched is not None, f"Missing PR for {node_id}"
            matched.title = upd["title"]
            matched.body = upd["body"]
            matched.base_branch = upd["base_branch"]
            data[f"op{idx}"] = {"clientMutationId": None}

        self.request_log.append(
            {
                "kind": "UpdatePullRequest",
                "batch_size": len(updates),
                "result": "SUCCESS",
            }
        )
        return {"data": data}


@dataclass
class BatchPlan:
    """Exact mirror of `BatchPlan` in `src/pre_push/batching.rs:8-51`."""

    item_count: int
    cursor: int = 0
    batch_len: int = INITIAL_GRAPHQL_BATCH_LEN

    def current(self) -> tuple[int, int] | None:
        if self.cursor < self.item_count:
            return (
                self.cursor,
                min(self.item_count, self.cursor + self.batch_len),
            )
        return None

    def accept(self) -> None:
        cur = self.current()
        assert cur is not None
        self.cursor = cur[1]

    def reject(self) -> tuple[int, int]:
        cur = self.current()
        assert cur is not None
        attempted = cur[1] - cur[0]
        if attempted == 1:
            raise RuntimeError(
                f"GraphQL operation at item {cur[0]} exceeds GitHub resource limits."
            )
        retry = attempted // 2
        self.batch_len = retry
        return (attempted, retry)


def is_resource_limit_error(error: dict[str, Any]) -> bool:
    """Exact mirror of `is_resource_limit_error` in `src/pre_push/batching.rs:80-93`."""
    return error.get("type") in (
        "RESOURCE_LIMITS_EXCEEDED",
        "MAX_NODE_LIMIT_EXCEEDED",
    ) or (
        error.get("message")
        == "A query attribute must be specified and must be a string."
    )


def classify_response_unpatched(response: dict[str, Any]) -> str:
    """Exact mirror of `classify_response` in `src/pre_push/batching.rs:64-78`."""
    errors = response.get("errors")
    if errors is None:
        return "Success"
    has_no_data = response.get("data") is None
    has_only_resource_errors = isinstance(errors, list) and (
        len(errors) > 0 and all(is_resource_limit_error(e) for e in errors)
    )
    if has_no_data and has_only_resource_errors:
        return "RetryLimit"
    return "Fatal"


def make_stack(num_commits: int = 49) -> list[dict[str, str]]:
    stack: list[dict[str, str]] = []
    for i in range(1, num_commits + 1):
        gherrit_id = f"G{i:02d}"
        base_branch = "main" if i == 1 else f"G{i - 1:02d}"
        stack.append(
            {
                "gherrit_id": gherrit_id,
                "head_branch": gherrit_id,
                "base_branch": base_branch,
                "title": f"Commit {i} of {num_commits}",
                "body": f"Body for commit {i}",
            }
        )
    return stack


def run_unpatched_sync_prs(
    server: SimulatedGitHubServer, stack: list[dict[str, str]]
) -> dict[str, Any]:
    """Mirrors unpatched `sync_prs` + `run_batched_graphql`."""
    heads = [c["head_branch"] for c in stack]
    find_resp = server.execute_find_prs(heads)
    existing: dict[str, dict[str, Any]] = {}
    for idx, head in enumerate(heads):
        nodes = find_resp["data"][f"op{idx}"]["open"]["nodes"]
        if nodes:
            existing[head] = nodes[0]

    creations = [c for c in stack if c["head_branch"] not in existing]
    backoff_trace: list[dict[str, int]] = []

    if creations:
        plan = BatchPlan(
            item_count=len(creations), batch_len=INITIAL_GRAPHQL_BATCH_LEN
        )
        while (rng := plan.current()) is not None:
            start, end = rng
            chunk = creations[start:end]
            resp = server.execute_create_prs(chunk)
            disposition = classify_response_unpatched(resp)
            if disposition == "Success":
                for idx, c in enumerate(chunk):
                    pr_data = resp["data"][f"op{idx}"]["pullRequest"]
                    existing[c["head_branch"]] = {
                        "number": pr_data["number"],
                        "id": pr_data["id"],
                        "title": c["title"],
                        "body": c["body"],
                        "baseRefName": c["base_branch"],
                    }
                plan.accept()
            elif disposition == "RetryLimit":
                attempted, retry = plan.reject()
                backoff_trace.append(
                    {
                        "cursor": plan.cursor,
                        "attempted": attempted,
                        "retry": retry,
                    }
                )
            else:
                return {
                    "status": "fatal_error",
                    "failed_at_range": [start, end],
                    "backoff_trace": backoff_trace,
                    "errors": resp.get("errors"),
                    "server_pr_count": len(server.prs_by_head),
                }

    updates = [
        {
            "node_id": existing[c["head_branch"]]["id"],
            "title": c["title"],
            "body": f"{c['body']}\n\n---\nStack linked ({len(stack)} PRs)",
            "base_branch": c["base_branch"],
        }
        for c in stack
    ]
    server.execute_update_prs(updates)
    return {
        "status": "ok",
        "backoff_trace": backoff_trace,
        "server_pr_count": len(server.prs_by_head),
    }


def compute_full_halving_sequence(initial_items: int) -> list[tuple[int, int]]:
    """Computes the exact slice sequence of `BatchPlan::reject`."""
    plan = BatchPlan(
        item_count=initial_items, batch_len=INITIAL_GRAPHQL_BATCH_LEN
    )
    slices: list[tuple[int, int]] = []
    while True:
        cur = plan.current()
        assert cur is not None
        slices.append(cur)
        try:
            plan.reject()
        except RuntimeError:
            break
    return slices


def run_patched_sync_prs(
    server: SimulatedGitHubServer,
    stack: list[dict[str, str]],
    *,
    initial_create_batch_len: int,
) -> dict[str, Any]:
    """Patched `sync_prs` with partial-data harvesting and state re-query."""
    heads = [c["head_branch"] for c in stack]
    find_resp = server.execute_find_prs(heads)
    existing: dict[str, dict[str, Any]] = {}
    for idx, head in enumerate(heads):
        nodes = find_resp["data"][f"op{idx}"]["open"]["nodes"]
        if nodes:
            existing[head] = nodes[0]

    creations = [c for c in stack if c["head_branch"] not in existing]
    backoff_trace: list[dict[str, Any]] = []

    if creations:
        plan = BatchPlan(
            item_count=len(creations), batch_len=initial_create_batch_len
        )
        while (rng := plan.current()) is not None:
            start, end = rng
            chunk = creations[start:end]
            resp = server.execute_create_prs(chunk)
            errors = resp.get("errors")
            data = resp.get("data")

            if errors is None:
                assert isinstance(data, dict)
                for idx, c in enumerate(chunk):
                    pr_data = data[f"op{idx}"]["pullRequest"]
                    existing[c["head_branch"]] = {
                        "number": pr_data["number"],
                        "id": pr_data["id"],
                        "title": c["title"],
                        "body": c["body"],
                        "baseRefName": c["base_branch"],
                    }
                plan.accept()
                continue

            has_only_resource_errors = isinstance(errors, list) and (
                len(errors) > 0 and all(is_resource_limit_error(e) for e in errors)
            )
            if not has_only_resource_errors:
                return {
                    "status": "fatal_error",
                    "failed_at_range": [start, end],
                    "errors": errors,
                }

            # Layer 3A: If partial `data` object is present, harvest contiguous
            # leading non-null creations before backing off.
            harvested_from_data = 0
            if isinstance(data, dict):
                for idx, c in enumerate(chunk):
                    op_val = data.get(f"op{idx}")
                    if isinstance(op_val, dict) and isinstance(
                        op_val.get("pullRequest"), dict
                    ):
                        pr_data = op_val["pullRequest"]
                        existing[c["head_branch"]] = {
                            "number": pr_data["number"],
                            "id": pr_data["id"],
                            "title": c["title"],
                            "body": c["body"],
                            "baseRefName": c["base_branch"],
                        }
                        harvested_from_data += 1
                    else:
                        break

            # Layer 3B: If `data` was null (or truncated), re-query the
            # attempted chunk via `FindPullRequest` so any server-side partial
            # creations are reconciled before retrying `CreatePullRequest`.
            harvested_from_requery = 0
            if harvested_from_data == 0:
                recheck_heads = [c["head_branch"] for c in chunk]
                recheck_resp = server.execute_find_prs(recheck_heads)
                for idx, c in enumerate(chunk):
                    nodes = recheck_resp["data"][f"op{idx}"]["open"]["nodes"]
                    if nodes:
                        existing[c["head_branch"]] = nodes[0]
                        harvested_from_requery += 1
                    else:
                        break

            harvested = harvested_from_data + harvested_from_requery
            attempted = end - start
            if attempted == 1 and harvested == 0:
                raise RuntimeError(
                    f"Single operation at {start} exceeded resource limits"
                )
            retry = max(1, attempted // 2)
            plan.cursor += harvested
            plan.batch_len = retry
            backoff_trace.append(
                {
                    "attempted_range": [start, end],
                    "harvested_from_data": harvested_from_data,
                    "harvested_from_requery": harvested_from_requery,
                    "new_cursor": plan.cursor,
                    "new_batch_len": plan.batch_len,
                }
            )

    updates = [
        {
            "node_id": existing[c["head_branch"]]["id"],
            "title": c["title"],
            "body": f"{c['body']}\n\n---\nStack linked ({len(stack)} PRs)",
            "base_branch": c["base_branch"],
        }
        for c in stack
    ]
    server.execute_update_prs(updates)
    return {
        "status": "ok",
        "backoff_trace": backoff_trace,
        "server_pr_count": len(server.prs_by_head),
    }


def run_all_simulations() -> dict[str, Any]:
    stack = make_stack(49)
    halving_slices = compute_full_halving_sequence(49)
    assert halving_slices == [
        (0, 49),
        (0, 24),
        (0, 12),
        (0, 6),
        (0, 3),
        (0, 1),
    ]

    # 1. Unpatched single invocation when server returns `data: null` on limit.
    srv_unpatched_null = SimulatedGitHubServer(
        create_limit_per_request=16, partial_data_on_limit=False
    )
    res_unpatched_null = run_unpatched_sync_prs(srv_unpatched_null, stack)
    assert res_unpatched_null["status"] == "fatal_error"
    assert res_unpatched_null["failed_at_range"] == [0, 24]
    assert res_unpatched_null["server_pr_count"] == 16
    assert (
        "already exists for owner:G01"
        in res_unpatched_null["errors"][0]["message"]
    )

    # 2. Unpatched single invocation when server returns partial `data` on limit.
    srv_unpatched_partial = SimulatedGitHubServer(
        create_limit_per_request=16, partial_data_on_limit=True
    )
    res_unpatched_partial = run_unpatched_sync_prs(srv_unpatched_partial, stack)
    assert res_unpatched_partial["status"] == "fatal_error"
    assert res_unpatched_partial["failed_at_range"] == [0, 49]
    assert res_unpatched_partial["server_pr_count"] == 16

    # 3A. Unpatched external `git push` retry loop (empirical 3-pass progression
    # 0 -> 16 -> 32 -> 49 when the 17-item tail succeeds).
    srv_external_3pass = SimulatedGitHubServer(
        create_limit_per_request=16,
        small_batch_bonus_threshold=17,
        partial_data_on_limit=False,
    )
    passes_3pass: list[dict[str, Any]] = []
    for pass_num in range(1, 10):
        before_count = len(srv_external_3pass.prs_by_head)
        outcome = run_unpatched_sync_prs(srv_external_3pass, stack)
        after_count = len(srv_external_3pass.prs_by_head)
        passes_3pass.append(
            {
                "pass": pass_num,
                "prs_before": before_count,
                "prs_after": after_count,
                "status": outcome["status"],
            }
        )
        if outcome["status"] == "ok":
            break
    assert [
        (p["prs_before"], p["prs_after"], p["status"]) for p in passes_3pass
    ] == [
        (0, 16, "fatal_error"),
        (16, 32, "fatal_error"),
        (32, 49, "ok"),
    ]

    # 3B. Unpatched external `git push` retry loop with strict fixed K = 16
    # (0 -> 16 -> 32 -> 48 -> 49).
    srv_external_strict16 = SimulatedGitHubServer(
        create_limit_per_request=16,
        small_batch_bonus_threshold=None,
        partial_data_on_limit=False,
    )
    passes_strict16: list[dict[str, Any]] = []
    for pass_num in range(1, 10):
        before_count = len(srv_external_strict16.prs_by_head)
        outcome = run_unpatched_sync_prs(srv_external_strict16, stack)
        after_count = len(srv_external_strict16.prs_by_head)
        passes_strict16.append(
            {
                "pass": pass_num,
                "prs_before": before_count,
                "prs_after": after_count,
                "status": outcome["status"],
            }
        )
        if outcome["status"] == "ok":
            break
    assert [
        (p["prs_before"], p["prs_after"], p["status"]) for p in passes_strict16
    ] == [
        (0, 16, "fatal_error"),
        (16, 32, "fatal_error"),
        (32, 48, "fatal_error"),
        (48, 49, "ok"),
    ]

    # 4A. Patched stateful/idempotent retry starting from 64 with `data: null`.
    srv_patched_null = SimulatedGitHubServer(
        create_limit_per_request=16, partial_data_on_limit=False
    )
    res_patched_null = run_patched_sync_prs(
        srv_patched_null,
        stack,
        initial_create_batch_len=INITIAL_GRAPHQL_BATCH_LEN,
    )
    assert res_patched_null["status"] == "ok"
    assert res_patched_null["server_pr_count"] == 49

    # 4B. Patched stateful/idempotent retry starting from 64 with partial `data`.
    srv_patched_partial = SimulatedGitHubServer(
        create_limit_per_request=16, partial_data_on_limit=True
    )
    res_patched_partial = run_patched_sync_prs(
        srv_patched_partial,
        stack,
        initial_create_batch_len=INITIAL_GRAPHQL_BATCH_LEN,
    )
    assert res_patched_partial["status"] == "ok"
    assert res_patched_partial["server_pr_count"] == 49

    # 5. Patched with INITIAL_CREATE_PR_BATCH_LEN = 12.
    srv_patched_12 = SimulatedGitHubServer(
        create_limit_per_request=16, partial_data_on_limit=False
    )
    res_patched_12 = run_patched_sync_prs(
        srv_patched_12,
        stack,
        initial_create_batch_len=PATCHED_CREATE_PR_BATCH_LEN,
    )
    assert res_patched_12["status"] == "ok"
    assert res_patched_12["server_pr_count"] == 49
    assert res_patched_12["backoff_trace"] == []

    return {
        "stack_size": len(stack),
        "server_create_limit_per_request": 16,
        "unpatched_batch_plan_halving_slices": [
            list(s) for s in halving_slices
        ],
        "experiment_1_unpatched_single_push_null_data_on_limit": {
            "outcome": res_unpatched_null,
            "server_requests": srv_unpatched_null.request_log,
        },
        "experiment_2_unpatched_single_push_partial_data_on_limit": {
            "outcome": res_unpatched_partial,
            "server_requests": srv_unpatched_partial.request_log,
        },
        "experiment_3_unpatched_external_push_retry_loop": {
            "empirical_3_pass_progression_0_16_32_49": passes_3pass,
            "strict_k16_4_pass_progression_0_16_32_48_49": passes_strict16,
        },
        "experiment_4a_patched_idempotent_retry_from_64_null_data": {
            "outcome": res_patched_null,
            "server_requests": srv_patched_null.request_log,
        },
        "experiment_4b_patched_idempotent_retry_from_64_partial_data": {
            "outcome": res_patched_partial,
            "server_requests": srv_patched_partial.request_log,
        },
        "experiment_5_patched_initial_create_batch_len_12": {
            "outcome": res_patched_12,
            "server_requests": srv_patched_12.request_log,
        },
    }


def main() -> int:
    results = run_all_simulations()
    json.dump(results, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
