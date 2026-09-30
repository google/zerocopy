#!/usr/bin/env python3
"""Validate retained results from the guarded sequential destination probe."""

import json
from pathlib import Path
import probe

HERE = Path(__file__).resolve().parent
EXPECTED = {
    "release": {"unit_key_probe::profile_value": ["11"],
                "unit_key_probe::config_value": ["23"]},
    "cfg_alt": {"unit_key_probe::profile_value": ["7"],
                "unit_key_probe::config_value": ["29"]},
}
ORDERS = {"release_then_cfg": ["release", "cfg_alt"],
          "cfg_then_release": ["cfg_alt", "release"]}


def projection(decoded):
    return {k: v["u32_literals"] for k, v in decoded["local_bodies"].items()}


def destination(command):
    argv = command["argv"]
    index = argv.index("--dest-file")
    return argv[index + 1]


def source_is_fixed(decoded):
    assert len(decoded["files"]) == 1
    assert decoded["files"][0]["contents_sha256"] == probe.PINS["fixture_source"]


def check():
    path = HERE / "results.json"
    if not path.exists():
        raise SystemExit("not run: support/results.json is absent")
    metadata = json.loads((HERE.parent / "REPORT.json").read_text())
    probe_subject = next(subject for subject in metadata["subjects"]
                         if "acquisition_probe_sha256" in subject["identity"])
    identity = probe_subject["identity"]
    assert probe.sha(HERE / "acquisition-probe.py.txt") == identity["acquisition_probe_sha256"]
    assert probe.sha(HERE / "probe.py") == identity["replay_probe_sha256"]
    assert probe.sha(path) == identity["results_sha256"]
    result = json.loads(path.read_text())
    assert result["schema"] == 1
    assert result["status"] == "completed", result["status"]
    assert result["input_sha256"] == probe.PINS
    assert probe.sha(HERE / "fixture/src/lib.rs") == probe.PINS["fixture_source"]
    assert not result["cleanup"]["work_exists"]
    assert result["initial_destinations_absent"] == {key: True for key in ORDERS}
    limits = result["limits"]
    for run in result["runs"].values():
        assert run["samples"] and run["guard_reason"] is None
        assert run["elapsed_seconds"] <= limits["command_timeout_seconds"]
        for sample in run["samples"]:
            assert sample["host"]["estimated_reclaimable_percent"] >= limits["minimum_reclaimable_percent"]
            assert sample["host"]["free_disk_bytes"] >= limits["minimum_free_disk_bytes"]
            assert sample["combined_rss_kib"] <= limits["maximum_combined_process_group_rss_kib"]
            assert sample["scratch_kib"] <= limits["maximum_scratch_kib"]
        for command in run["commands"]:
            for suffix in ("stdout", "stderr"):
                raw = HERE / "raw" / f"{command['label']}.{suffix}"
                assert raw.exists() and probe.sha(raw) == command[f"{suffix}_sha256"]
    for label in EXPECTED:
        run = result["runs"][f"control_{label}"]
        assert run["guard_reason"] is None
        assert len(run["commands"]) == 1 and run["commands"][0]["exit"] == 0
        artifact = HERE / "artifacts" / f"control-{label}.llbc"
        decoded = probe.decode(artifact)
        assert decoded == result["artifacts"][f"control_{label}"]
        assert not decoded["has_errors"]
        assert decoded["dest_file"] == destination(run["commands"][0])
        source_is_fixed(decoded)
        assert projection(decoded) == EXPECTED[label]
    for order_name, cases in ORDERS.items():
        steps = result["orders"][order_name]
        assert len(steps) == 2
        commands = [result["runs"][f"{order_name}-step{i}-{label}"]["commands"][0]
                    for i, label in enumerate(cases, 1)]
        assert destination(commands[0]) == destination(commands[1])
        assert commands[0]["end_monotonic_ns"] <= commands[1]["start_monotonic_ns"]
        for index, label in enumerate(cases, 1):
            step = steps[index - 1]
            run_label = f"{order_name}-step{index}-{label}"
            run = result["runs"][run_label]
            assert run["guard_reason"] is None
            command = run["commands"][0]
            assert len(run["commands"]) == 1
            assert command["exit"] == step["exit"] == 0
            assert command["environment"]["CARGO_NET_OFFLINE"] == "true"
            assert command["environment"]["CARGO_BUILD_JOBS"] == "1"
            if label == "cfg_alt":
                assert command["environment"]["RUSTFLAGS"] == "--cfg probe_alt"
            else:
                assert "--release" in command["argv"]
                assert command["environment"]["RUSTFLAGS"] is None
            name = f"{order_name}-step{index}"
            assert step["step"] == index and step["case"] == label
            assert step["artifact"] == name
            artifact = HERE / "artifacts" / f"{name}.llbc"
            decoded = probe.decode(artifact)
            assert decoded == result["artifacts"][name]
            assert decoded["dest_file"] == destination(command)
            source_is_fixed(decoded)
            assert projection(decoded) == step["selected_literals"]
            assert not decoded["has_errors"]
            assert projection(decoded) == EXPECTED[label]
    print("PASS: two controls and four sequential destination snapshots/absences")


if __name__ == "__main__":
    check()
