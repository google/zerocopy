#!/usr/bin/env python3
"""Offline checker for one retained concurrent Charon shared-destination cell."""

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


def projection(decoded):
    return {name: body["u32_literals"] for name, body in decoded["local_bodies"].items()}


def destination(command):
    argv = command["argv"]
    return argv[argv.index("--dest-file") + 1]


def main():
    path = HERE / "results.json"
    if not path.exists():
        raise SystemExit("not run: support/results.json is absent")
    result = json.loads(path.read_text())
    assert result["schema"] == 1 and result["status"] == "completed"
    assert result["input_sha256"] == probe.PINS
    for key, local in (("fixture_source", HERE / "fixture/src/lib.rs"),
                       ("control_release", HERE / "controls/release.llbc"),
                       ("control_cfg_alt", HERE / "controls/cfg_alt.llbc")):
        assert probe.sha(local) == probe.PINS[key]
    assert result["controls_source_package"] == "anneal-3731-i076-sequential-shared-destination-2026-09-30"
    assert result["initial_destination_absent"] is True
    assert result["control_models"] == {
        key: {"sha256": probe.PINS[f"control_{key}"], "selected_literals": EXPECTED[key]}
        for key in EXPECTED}
    assert result["preflight"]["host"]["estimated_reclaimable_percent"] > 33.0
    assert result["preflight"]["host"]["free_disk_bytes"] > 10 * 1024**3
    limits = result["limits"]
    assert limits == {
        "minimum_admission_reclaimable_percent": 33.0,
        "minimum_live_reclaimable_percent": 20.0,
        "minimum_free_disk_bytes": 10 * 1024**3,
        "maximum_combined_process_group_rss_kib": 512 * 1024,
        "maximum_scratch_kib": 100 * 1024,
        "command_timeout_seconds": 15.0,
    }
    run = result["run"]
    assert run["guard_reason"] is None and run["elapsed_seconds"] < 15.0
    assert run["preflight"]["host"]["estimated_reclaimable_percent"] > 33.0
    assert len(run["commands"]) == 2
    commands = {row["label"]: row for row in run["commands"]}
    assert set(commands) == set(EXPECTED)
    assert all(row["exit"] == 0 for row in commands.values())
    assert len({row["pid"] for row in commands.values()}) == 2
    assert destination(commands["release"]) == destination(commands["cfg_alt"])
    assert commands["release"]["environment"]["CARGO_TARGET_DIR"] != commands["cfg_alt"]["environment"]["CARGO_TARGET_DIR"]
    for label, row in commands.items():
        env = row["environment"]
        assert env["CARGO_NET_OFFLINE"] == "true" and env["CARGO_BUILD_JOBS"] == "1"
        assert env["CARGO_INCREMENTAL"] == "0" and env["RAYON_NUM_THREADS"] == "1"
        assert "--lib" in row["argv"] and "--offline" in row["argv"]
        assert len(row["driver_lines"]) == 1
        for suffix in ("stdout", "stderr"):
            raw = HERE / "raw" / f"{label}.{suffix}"
            assert raw.exists() and probe.sha(raw) == row[f"{suffix}_sha256"]
    assert "--release" in commands["release"]["argv"]
    assert commands["release"]["environment"]["RUSTFLAGS"] is None
    assert "-C opt-level=3" in commands["release"]["driver_lines"][0]
    assert "--release" not in commands["cfg_alt"]["argv"]
    assert commands["cfg_alt"]["environment"]["RUSTFLAGS"] == "--cfg probe_alt"
    assert "--cfg probe_alt" in commands["cfg_alt"]["driver_lines"][0]
    assert run["samples"]
    simultaneous = []
    for sample in run["samples"]:
        assert sample["host"]["estimated_reclaimable_percent"] >= 20.0
        assert sample["host"]["free_disk_bytes"] >= 10 * 1024**3
        assert sample["combined_rss_kib"] <= 512 * 1024
        assert sample["scratch_kib"] <= 100 * 1024
        groups = sample["process_group_rss_kib"]
        if all(groups[str(row["pid"])] > 0 for row in commands.values()):
            simultaneous.append(sample)
    assert simultaneous, "no sampled simultaneous process-group residency"
    assert result["intervals_overlap"] is True
    assert all(value == 0 for value in result["postrun_process_group_rss_kib"].values())
    assert result["cleanup"]["work_exists"] is False

    final = result["final_destination"]
    assert final and final["parseable"] is True
    artifact = HERE / "artifacts/shared-final.llbc"
    assert probe.sha(artifact) == final["sha256"]
    assert artifact.stat().st_size == final["bytes"]
    decoded = probe.decode(artifact)
    assert decoded == final["decoded"]
    assert decoded["dest_file"] == destination(commands["release"])
    assert decoded["crate_name"] == "unit_key_probe" and decoded["has_errors"] is False
    assert len(decoded["files"]) == 1
    assert decoded["files"][0]["contents_sha256"] == probe.PINS["fixture_source"]
    assert projection(decoded) == EXPECTED["release"]

    metadata = json.loads((HERE.parent / "REPORT.json").read_text())
    assert metadata["observed_at"] == "2026-09-30"
    report_subject = next(s for s in metadata["subjects"] if "probe_sha256" in s["identity"])
    assert report_subject["identity"]["probe_sha256"] == probe.sha(HERE / "probe.py")
    assert report_subject["identity"]["results_sha256"] == probe.sha(path)
    print("PASS: one overlapping release/cfg pair, release-model final output, guards and cleanup")


if __name__ == "__main__":
    main()
