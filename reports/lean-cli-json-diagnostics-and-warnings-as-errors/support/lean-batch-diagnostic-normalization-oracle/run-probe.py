#!/usr/bin/env python3
"""Run the retained Lean relocation and negative-control fixture.

Use LEAN_BIN to select the pinned Lean binary. All compiler inputs and outputs
are package-relative, so the recorded JSON does not contain local host paths.
"""

import hashlib
import json
import os
from pathlib import Path
import subprocess


SUPPORT = Path(__file__).resolve().parent
PACKAGE = SUPPORT.parent
RESULTS = SUPPORT / "results"
LEAN = os.environ.get("LEAN_BIN", "lean")
CASES = ("a", "b", "c", "d", "e")


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def canonical_messages(messages, case):
    expected = f"support/{case}/Probe.lean"
    normalized = []
    for message in messages:
        assert message["fileName"] == expected, message
        item = dict(message)
        item["fileName"] = "<same-source-file>/Probe.lean"
        normalized.append(item)
    return normalized


def main():
    RESULTS.mkdir(exist_ok=True)
    binary = subprocess.run([LEAN, "--version"], text=True, capture_output=True, check=True)
    binary_path = Path(LEAN) if "/" in LEAN else Path(subprocess.check_output(["which", LEAN], text=True).strip())
    observations = {
        "tool": {
            "version": binary.stdout.strip(),
            "binary_sha256": sha256(binary_path.read_bytes()),
            "command_pattern": "lean --json -o support/results/<case>/Probe.olean support/<case>/Probe.lean",
            "consumer_command_pattern": "LEAN_PATH=support/results/<case> lean --json support/query/Query.lean",
        },
        "cases": {},
    }
    raw_messages = {}
    normalized_messages = {}
    actionable_messages = {}

    for case in CASES:
        source = SUPPORT / case / "Probe.lean"
        case_results = RESULTS / case
        case_results.mkdir(exist_ok=True)
        output = case_results / "Probe.olean"
        output.unlink(missing_ok=True)
        command = [LEAN, "--json", "-o", f"support/results/{case}/Probe.olean", f"support/{case}/Probe.lean"]
        run = subprocess.run(command, cwd=PACKAGE, capture_output=True, text=True)
        assert not run.stderr, (case, run.stderr)
        (RESULTS / f"{case}.jsonl").write_text(run.stdout, encoding="utf-8")
        messages = [json.loads(line) for line in run.stdout.splitlines() if line]
        raw_messages[case] = messages
        normalized_messages[case] = canonical_messages(messages, case)
        actionable_messages[case] = [
            message for message in normalized_messages[case]
            if message["severity"] in ("warning", "error")
        ]
        observations["cases"][case] = {
            "source_sha256": sha256(source.read_bytes()),
            "exit_code": run.returncode,
            "severity": [message["severity"] for message in messages],
            "olean_sha256": sha256(output.read_bytes()) if output.exists() else None,
            "olean_bytes": output.stat().st_size if output.exists() else None,
        }
        if output.exists():
            environment = os.environ.copy()
            environment["LEAN_PATH"] = str(case_results)
            consumer = subprocess.run(
                [LEAN, "--json", "support/query/Query.lean"],
                cwd=PACKAGE, capture_output=True, text=True, env=environment,
            )
            assert not consumer.stderr, (case, consumer.stderr)
            (RESULTS / f"{case}-consumer.jsonl").write_text(consumer.stdout, encoding="utf-8")
            observations["cases"][case]["consumer_exit_code"] = consumer.returncode
            observations["cases"][case]["consumer_json_sha256"] = sha256(consumer.stdout.encode())

    for label, output_name in (("a-repeat", "a/Probe.olean"), ("a-output-only", "a-output-only/Probe.olean")):
        output = RESULTS / output_name
        output.parent.mkdir(exist_ok=True)
        run = subprocess.run(
            [LEAN, "--json", "-o", f"support/results/{output_name}", "support/a/Probe.lean"],
            cwd=PACKAGE, capture_output=True, text=True,
        )
        assert run.returncode == 0 and not run.stderr, (label, run.returncode, run.stderr)
        (RESULTS / f"{label}.jsonl").write_text(run.stdout, encoding="utf-8")
        observations["cases"][label] = {
            "exit_code": run.returncode,
            "olean_sha256": sha256(output.read_bytes()),
            "olean_bytes": output.stat().st_size,
        }

    observations["comparisons"] = {
        "a_b_same_source": observations["cases"]["a"]["source_sha256"] == observations["cases"]["b"]["source_sha256"],
        "a_repeat_olean_equal": observations["cases"]["a"]["olean_sha256"] == observations["cases"]["a-repeat"]["olean_sha256"],
        "a_output_only_olean_equal": observations["cases"]["a"]["olean_sha256"] == observations["cases"]["a-output-only"]["olean_sha256"],
        "a_b_raw_diagnostics_equal": raw_messages["a"] == raw_messages["b"],
        "a_b_normalized_diagnostics_equal": normalized_messages["a"] == normalized_messages["b"],
        "a_b_olean_equal": observations["cases"]["a"]["olean_sha256"] == observations["cases"]["b"]["olean_sha256"],
        "a_b_consumer_equal": observations["cases"]["a"]["consumer_json_sha256"] == observations["cases"]["b"]["consumer_json_sha256"],
        "a_c_normalized_diagnostics_equal": normalized_messages["a"] == normalized_messages["c"],
        "a_c_actionable_diagnostics_equal": actionable_messages["a"] == actionable_messages["c"],
        "a_c_olean_equal": observations["cases"]["a"]["olean_sha256"] == observations["cases"]["c"]["olean_sha256"],
        "a_c_consumer_equal": observations["cases"]["a"]["consumer_json_sha256"] == observations["cases"]["c"]["consumer_json_sha256"],
        "d_rejected": observations["cases"]["d"]["exit_code"] != 0,
        "d_olean_absent": observations["cases"]["d"]["olean_sha256"] is None,
        "a_e_normalized_diagnostics_equal": normalized_messages["a"] == normalized_messages["e"],
        "a_e_olean_equal": observations["cases"]["a"]["olean_sha256"] == observations["cases"]["e"]["olean_sha256"],
        "a_e_consumer_equal": observations["cases"]["a"]["consumer_json_sha256"] == observations["cases"]["e"]["consumer_json_sha256"],
    }
    verification_oracle = {
        case: {
            "exit_code": observations["cases"][case]["exit_code"],
            "actionable_messages": actionable_messages[case],
            "consumer_json_sha256": observations["cases"][case].get("consumer_json_sha256"),
        }
        for case in CASES
    }
    observations["verification_oracle"] = verification_oracle
    observations["comparisons"].update({
        "a_b_verification_oracle_equal": verification_oracle["a"] == verification_oracle["b"],
        "a_c_verification_oracle_equal": verification_oracle["a"] == verification_oracle["c"],
        "a_d_verification_oracle_equal": verification_oracle["a"] == verification_oracle["d"],
        "a_e_verification_oracle_equal": verification_oracle["a"] == verification_oracle["e"],
    })
    (RESULTS / "observations.json").write_text(json.dumps(observations, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(observations, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
