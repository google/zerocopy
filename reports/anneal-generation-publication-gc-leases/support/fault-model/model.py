#!/usr/bin/env python3
"""Finite orchestration model with single-fence mutants; not Anneal code."""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass, replace
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PARTS = ("source", "model", "proof")
FULL = (1 << len(PARTS)) - 1
MUTANTS = ("none", "no_revision", "no_digest", "no_generation", "no_worker",
           "no_rpc", "no_owner", "no_status", "no_completeness", "no_echo",
           "no_reconcile", "cancel_any")


@dataclass(frozen=True)
class Job:
    number: int
    revision: int
    digest: str
    generation: int
    worker: int
    rpc: int
    owners: frozenset[str]
    parts: int = 0
    status: str = "active"


@dataclass(frozen=True)
class State:
    actual_revision: int = 0
    actual_digest: str = "A"
    observed_revision: int = 0
    observed_digest: str = "A"
    generation: int = 0
    worker: int = 0
    rpc: int = 0
    jobs: tuple[Job, ...] = ()
    published: int | None = None


def job_by_number(state: State, number: int) -> Job:
    return state.jobs[number]


def change_job(state: State, job: Job) -> State:
    jobs = list(state.jobs)
    jobs[job.number] = job
    return replace(state, jobs=tuple(jobs))


def actions(state: State) -> list[str]:
    # This is a deliberately finite event graph: two jobs, two values/epochs,
    # and three completion pieces. All enabled transitions are enumerated.
    out = []
    if not state.jobs or (len(state.jobs) == 1 and
                          (state.observed_revision, state.observed_digest, state.generation,
                           state.worker, state.rpc) !=
                          (state.jobs[0].revision, state.jobs[0].digest,
                           state.jobs[0].generation, state.jobs[0].worker, state.jobs[0].rpc)):
        out.append("start")
    if state.actual_revision == 0 and state.observed_revision == 0:
        out += ["bump_revision", "external_edit"]
    if state.actual_digest == "A" and state.observed_digest == "A":
        out.append("replace_digest_same_revision")
    if state.generation == 0:
        out.append("regenerate_same_source")
    if state.worker == 0:
        out.append("restart_worker")
    if state.rpc == 0:
        out.append("reconnect_rpc")
    if (state.observed_revision, state.observed_digest) != (state.actual_revision, state.actual_digest):
        out.append("reconcile")
    for j in state.jobs:
        prefix = f"j{j.number}:"
        if j.status == "active" and "agent" not in j.owners:
            out.append(prefix + "join_agent")
        for owner in ("editor", "agent"):
            if owner in j.owners:
                out.append(prefix + "cancel_" + owner)
        for i, part in enumerate(PARTS):
            if not (j.parts & (1 << i)):
                out.append(prefix + "complete_" + part)
        if j.status == "active":
            out += [prefix + "fail", prefix + "timeout"]
        out += [prefix + "deliver_valid", prefix + "deliver_wrong_echo"]
    return out


def required(state: State, job: Job, echo_valid: bool) -> dict[str, bool]:
    """Reference obligations at the instant of publication, independent of mutation."""
    return {
        "revision": job.revision == state.actual_revision,
        "digest": job.digest == state.actual_digest,
        "generation": job.generation == state.generation,
        "worker": job.worker == state.worker,
        "rpc": job.rpc == state.rpc,
        "owner": bool(job.owners),
        "status": job.status == "active",
        "completeness": job.parts == FULL,
        "echo": echo_valid,
        "reconcile": ((state.actual_revision, state.actual_digest) ==
                      (state.observed_revision, state.observed_digest)),
    }


def authorizes(obligations: dict[str, bool], mutant: str) -> bool:
    dropped = {"no_revision": "revision", "no_digest": "digest",
               "no_generation": "generation", "no_worker": "worker",
               "no_rpc": "rpc", "no_owner": "owner", "no_status": "status",
               "no_completeness": "completeness", "no_echo": "echo"}
    omit = dropped.get(mutant)
    return all(v for k, v in obligations.items() if k != omit)


def step(state: State, action: str, mutant: str) -> tuple[State, dict | None]:
    if action == "start":
        j = Job(len(state.jobs), state.observed_revision, state.observed_digest,
                state.generation, state.worker, state.rpc, frozenset({"editor"}))
        return replace(state, jobs=state.jobs + (j,)), None
    if action == "bump_revision":
        return replace(state, actual_revision=1, observed_revision=1), None
    if action == "replace_digest_same_revision":
        return replace(state, actual_digest="B", observed_digest="B"), None
    if action == "external_edit":
        return replace(state, actual_revision=1, actual_digest="B"), None
    if action == "reconcile":
        return replace(state, observed_revision=state.actual_revision,
                       observed_digest=state.actual_digest, generation=1), None
    if action == "regenerate_same_source":
        return replace(state, generation=1), None
    if action == "restart_worker":
        return replace(state, worker=1), None
    if action == "reconnect_rpc":
        return replace(state, rpc=1), None
    number, op = action.split(":", 1)
    job = job_by_number(state, int(number[1:]))
    if op == "join_agent":
        return change_job(state, replace(job, owners=job.owners | {"agent"})), None
    if op.startswith("cancel_"):
        owner = op.removeprefix("cancel_")
        remaining = job.owners - {owner}
        status = "cancelled" if mutant == "cancel_any" else job.status
        next_state = change_job(state, replace(job, owners=remaining, status=status))
        wrong_kill = mutant == "cancel_any" and bool(remaining) and status == "cancelled"
        return next_state, ({"violation": "shared_owner_killed", "remaining": sorted(remaining)}
                            if wrong_kill else None)
    if op.startswith("complete_"):
        part = op.removeprefix("complete_")
        return change_job(state, replace(job, parts=job.parts | (1 << PARTS.index(part)))), None
    if op in ("fail", "timeout"):
        return change_job(state, replace(job, status=op)), None
    if op.startswith("deliver_"):
        echo_valid = op == "deliver_valid"
        obligations = required(state, job, echo_valid)
        if mutant == "no_reconcile":
            # Trust watcher-maintained observations in place of a fresh read of
            # the authoritative source, including its revision and digest.
            obligations = dict(obligations, revision=job.revision == state.observed_revision,
                               digest=job.digest == state.observed_digest, reconcile=True)
        accepted = authorizes(obligations, mutant)
        if not accepted:
            return state, None
        next_state = replace(state, published=job.number)
        required_now = required(state, job, echo_valid)
        if not all(required_now.values()):
            return next_state, {"violation": "invalid_publication", "failed":
                                sorted(k for k, v in required_now.items() if not v),
                                "job": job.number, "published": next_state.published}
        return next_state, None
    raise ValueError(action)


def explore(mutant: str, depth: int = 7) -> dict:
    initial = State()
    queue = deque([(initial, ())])
    seen = {initial}
    checked_edges = 0
    terminal_depth = 0
    shortest = None
    while queue:
        state, path = queue.popleft()
        terminal_depth = max(terminal_depth, len(path))
        if len(path) == depth:
            continue
        for action in actions(state):
            checked_edges += 1
            successor, violation = step(state, action, mutant)
            if violation and shortest is None:
                shortest = {"schedule": list(path + (action,)), "detail": violation,
                            "prestate": serialize(state), "poststate": serialize(successor)}
            if successor not in seen:
                seen.add(successor)
                queue.append((successor, path + (action,)))
    return {"mutant": mutant, "bound": depth, "states": len(seen),
            "edges": checked_edges, "max_reached_depth": terminal_depth,
            "shortest_counterexample": shortest}


def serialize(value):
    if isinstance(value, State):
        return {field: serialize(getattr(value, field)) for field in value.__dataclass_fields__}
    if isinstance(value, Job):
        return {field: serialize(getattr(value, field)) for field in value.__dataclass_fields__}
    if isinstance(value, (tuple, frozenset)):
        return [serialize(x) for x in value]
    return value


CONTROLS = {
    "valid_complete": ["start", "j0:complete_source", "j0:complete_model",
                       "j0:complete_proof", "j0:deliver_valid"],
    "shared_survivor": ["start", "j0:join_agent", "j0:cancel_editor",
                        "j0:complete_source", "j0:complete_model", "j0:complete_proof",
                        "j0:deliver_valid"],
    "late_after_edit": ["start", "bump_revision", "j0:complete_source",
                        "j0:complete_model", "j0:complete_proof", "j0:deliver_valid"],
    "partial": ["start", "j0:deliver_valid"],
    "wrong_echo": ["start", "j0:complete_source", "j0:complete_model",
                   "j0:complete_proof", "j0:deliver_wrong_echo"],
    "timed_out": ["start", "j0:complete_source", "j0:complete_model",
                  "j0:complete_proof", "j0:timeout", "j0:deliver_valid"],
    "lost_watcher": ["start", "external_edit", "j0:complete_source",
                     "j0:complete_model", "j0:complete_proof", "j0:deliver_valid"],
}


def control(name: str, schedule: list[str]) -> dict:
    state = State()
    events = []
    for action in schedule:
        assert action in actions(state), (name, action, serialize(state))
        next_state, violation = step(state, action, "none")
        assert violation is None, (name, action, violation)
        events.append({"action": action, "published_before": state.published,
                       "published_after": next_state.published})
        state = next_state
    expected = name in ("valid_complete", "shared_survivor")
    assert (state.published is not None) == expected, (name, serialize(state))
    return {"name": name, "schedule": schedule, "published": state.published,
            "expected_publication": expected, "events": events}


def main():
    searches = {m: explore(m) for m in MUTANTS}
    assert searches["none"]["shortest_counterexample"] is None
    assert all(searches[m]["shortest_counterexample"] is not None for m in MUTANTS if m != "none")
    controls = {n: control(n, s) for n, s in CONTROLS.items()}
    output = {"model_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "python": sys.version, "bounds": {"depth": 7, "max_jobs": 2,
              "revisions": [0, 1], "digests": ["A", "B"], "stage_parts": list(PARTS),
              "worker_epochs": [0, 1], "rpc_epochs": [0, 1]},
              "searches": searches, "controls": controls}
    (ROOT / "results.json").write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    print(json.dumps({m: {"states": v["states"], "edges": v["edges"],
                          "counterexample": v["shortest_counterexample"]["schedule"]
                          if v["shortest_counterexample"] else None}
                      for m, v in searches.items()}, indent=2))


if __name__ == "__main__":
    main()
