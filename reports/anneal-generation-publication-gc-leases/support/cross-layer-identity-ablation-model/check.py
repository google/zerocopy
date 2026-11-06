#!/usr/bin/env python3
"""Bounded, symbolic I145 identity ablation; Python standard library only.

Run `python3 check.py --write` to regenerate results.json, then `python3 check.py`
to check that the retained result is exactly reproducible. No Anneal tool runs.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


FIELDS = (
    "source_subject", "source_bytes", "source_revision", "charon_config",
    "llbc_bytes", "aeneas_config", "generated_tree", "generated_generation",
    "lake_environment", "import_artifact", "document_bytes",
    "document_generation", "worker_epoch", "file_worker_epoch",
    "rpc_session", "rpc_request",
)
LOCATORS = {
    "source_path": "src/lib.rs", "llbc_path": "out/Probe.llbc",
    "generated_path": "generated/Probe/", "module": "Probe.Funs",
    "proof_uri": "file:///work/Proof.lean",
}
CONTENT = ("lake_environment", "import_artifact", "document_bytes")
LINEAGE = FIELDS[:12]
ADMISSION = FIELDS
POLICIES = {
    "elaboration_content": CONTENT,
    "strict_cross_stage_lineage": LINEAGE,
    "current_request_admission": ADMISSION,
}
BASE = tuple(0 for _ in FIELDS)
INDEX = {name: i for i, name in enumerate(FIELDS)}


def project(state: tuple[int, ...], names: tuple[str, ...]) -> tuple[int, ...]:
    return tuple(state[INDEX[name]] for name in names)


def mutate(state: tuple[int, ...], **updates: int) -> tuple[int, ...]:
    result = list(state)
    for name, value in updates.items():
        result[INDEX[name]] = value
    return tuple(result)


def changed(left: tuple[int, ...], right: tuple[int, ...]) -> dict[str, list[int]]:
    return {name: [left[i], right[i]] for i, name in enumerate(FIELDS)
            if left[i] != right[i]}


def witness(left: tuple[int, ...], right: tuple[int, ...], names: tuple[str, ...]) -> dict:
    return {
        "constant_locators": LOCATORS,
        "changed_fields": changed(left, right),
        "key_equal": project(left, names) == project(right, names),
    }


def analyze_policy(name: str, required: tuple[str, ...], states: list[tuple[int, ...]]) -> dict:
    # The oracle is an explicit observational policy over independent binary axes.
    # For each projected key, exhaustive grouping checks label consistency.
    analyses = {}
    for removed in (None, *FIELDS):
        remaining = tuple(x for x in required if x != removed)
        seen: dict[tuple[int, ...], tuple[int, ...]] = {}
        counterexample = None
        for state in states:
            key = project(state, remaining)
            oracle_label = project(state, required)
            old = seen.get(key)
            if old is None:
                seen[key] = state
            elif counterexample is None and project(old, required) != oracle_label:
                counterexample = witness(old, state, remaining)
        label = "full" if removed is None else removed
        analyses[label] = {
            "distinct_keys": len(seen),
            "sound_for_policy": counterexample is None,
            "counterexample": counterexample,
        }
        if removed is None:
            assert counterexample is None
        elif removed in required:
            assert counterexample is not None
            assert set(counterexample["changed_fields"]) == {removed}
        else:
            assert counterexample is None
    return {"oracle_fields": required, "ablations": analyses}


def controls() -> dict:
    b = BASE
    cases = {
        "same_locator_source_payload": [b, mutate(b, source_bytes=1)],
        "same_locator_source_revision": [b, mutate(b, source_revision=1)],
        "source_A_B_A": [b, mutate(b, source_bytes=1, source_revision=1),
                         mutate(b, source_revision=2)],
        "equal_outputs_distinct_histories": [b, mutate(b, source_revision=1,
                                                         charon_config=1,
                                                         generated_generation=1)],
        "unchanged_proof_changed_import": [b, mutate(b, import_artifact=1)],
        "unchanged_proof_changed_lake_environment": [b, mutate(b, lake_environment=1)],
        "same_bytes_new_document_generation": [b, mutate(b, document_generation=1)],
        "worker_restart_reused_rpc_id": [b, mutate(b, worker_epoch=1)],
        "file_worker_restart_reused_rpc_id": [b, mutate(b, file_worker_epoch=1)],
        "rpc_session_reused_request_number": [b, mutate(b, rpc_session=1)],
    }
    out = {}
    for case, trace in cases.items():
        start, end = trace[0], trace[-1]
        out[case] = {
            "trace_deltas": [changed(a, c) for a, c in zip(trace, trace[1:])],
            "start_to_end": changed(start, end),
            "same_elaboration_content": project(start, CONTENT) == project(end, CONTENT),
            "same_strict_lineage": project(start, LINEAGE) == project(end, LINEAGE),
            "same_request_admission": project(start, ADMISSION) == project(end, ADMISSION),
            "constant_locators": LOCATORS,
        }
    assert out["source_A_B_A"]["start_to_end"] == {"source_revision": [0, 2]}
    assert out["equal_outputs_distinct_histories"]["same_elaboration_content"]
    assert not out["unchanged_proof_changed_import"]["same_elaboration_content"]
    return out


def build() -> dict:
    states = list(itertools.product((0, 1), repeat=len(FIELDS)))
    assert len(states) == 65536
    policies = {name: analyze_policy(name, required, states)
                for name, required in POLICIES.items()}
    return {
        "model": "I145 independent binary cross-stage axes v1",
        "state_count": len(states),
        "state_domain": "Cartesian product of 16 independent {0,1} fields; locators fixed",
        "fields": FIELDS,
        "constant_locators": LOCATORS,
        "policies": policies,
        "named_controls": controls(),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true", help="regenerate results.json")
    args = parser.parse_args()
    target = Path(__file__).with_name("results.json")
    encoded = json.dumps(build(), indent=2, sort_keys=True) + "\n"
    if args.write:
        target.write_text(encoded, encoding="utf-8")
        print(f"wrote {target}")
    else:
        assert target.read_text(encoding="utf-8") == encoded, "results.json differs; run --write"
        print("PASS: 65,536 states; 3 full policies; 31 field removals; 17 absent-field controls; named controls; retained JSON")


if __name__ == "__main__":
    main()
