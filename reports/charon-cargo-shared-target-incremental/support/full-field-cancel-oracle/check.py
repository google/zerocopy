#!/usr/bin/env python3
"""Revalidate the retained full-field LLBC comparison without tool execution."""

import hashlib
import json
from pathlib import Path
import resource
import time

from compare import EXPECTED, PAIRS, SOURCE_RESULTS_SHA256, deep_diff

HERE = Path(__file__).resolve().parent
start = time.monotonic()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def short_name_map(data):
    rows = data["translated"]["short_names"]
    result = {json.dumps(row["key"], sort_keys=True, separators=(",", ":")):
              row["value"] for row in rows}
    assert len(result) == len(rows)
    return result


def main():
    record = json.loads((HERE / "comparison.json").read_text())
    assert record["status"] == "completed"
    assert record["source_results_sha256"] == SOURCE_RESULTS_SHA256
    assert sha(HERE / "source-results.json") == SOURCE_RESULTS_SHA256
    source = json.loads((HERE / "source-results.json").read_text())
    source_outputs = {
        phase["run"]["label"] + ".llbc": phase["run"]["output"]
        for name, phase in source["phases"].items() if name != "cancel_pair"
    }
    source_outputs["companion-B.llbc"] = source["phases"]["cancel_pair"]["runs"]["B"]["output"]
    assert source["phases"]["cancel_pair"]["runs"]["A"]["output"] is None
    assert set(source_outputs) == set(EXPECTED)
    assert {name: output["sha256"] for name, output in source_outputs.items()} == EXPECTED
    assert record["input_sha256"] == EXPECTED
    assert set(p.name for p in (HERE / "artifacts").glob("*.llbc")) == set(EXPECTED)
    assert record["elapsed_seconds"] <= 5
    assert record["self_peak_rss_bytes"] <= 64 * 1024**2
    assert record["samples"][0]["stage"] == "preflight"
    assert len(record["samples"]) == 12
    assert all(s["host"]["estimated_reclaimable_percent"] >= 20 and
               s["self_peak_rss_bytes"] <= 64 * 1024**2 and
               s["elapsed_seconds"] <= 5 for s in record["samples"])
    data = {}
    for name, expected in EXPECTED.items():
        path = HERE / "artifacts" / name
        assert sha(path) == expected
        assert record["artifacts"][name]["sha256"] == expected
        assert record["artifacts"][name]["bytes"] == path.stat().st_size
        assert source_outputs[name]["bytes"] == path.stat().st_size
        data[name] = json.loads(path.read_text())
        assert data[name]["has_errors"] is False
        assert data[name]["translated"]["crate_name"] == "warm_probe"
    assert sum((HERE / "artifacts" / n).stat().st_size for n in EXPECTED) == 145317
    counts = {"prewarm_A_to_baseline_oracle": 14,
              "prewarm_B_to_baseline_oracle": 12,
              "companion_B_to_baseline_oracle": 17,
              "recovery_A_to_edited_oracle": 19,
              "edited_to_baseline_negative_control": 23}
    same_subject = set(counts) - {"edited_to_baseline_negative_control"}
    for label, left, right in PAIRS:
        pair = record["pairs"][label]
        assert pair["left"] == left and pair["right"] == right
        diff = deep_diff(data[left], data[right])
        assert pair["differences"] == diff
        assert pair["difference_count"] == len(diff) == counts[label]
        assert pair["full_json_equal"] is False
        if label in same_subject:
            allowed = {"/translated/options/dest_file",
                       "/translated/files/1/name/Local"}
            assert all(row["path"] in allowed or
                       row["path"].startswith("/translated/short_names/")
                       for row in diff)
            assert short_name_map(data[left]) == short_name_map(data[right])
            assert sum(row["path"].startswith("/translated/short_names/")
                       for row in diff) == counts[label] - 2
    negative = record["pairs"]["edited_to_baseline_negative_control"]["differences"]
    neg_paths = {row["path"] for row in negative}
    assert "/translated/files/0/contents" in neg_paths
    assert "/translated/fun_decls/0/item_meta/source_text" in neg_paths
    literal = "/translated/fun_decls/0/body/Structured/body/statements/2/kind/Call/args/1/Const/kind/Literal/Scalar/Unsigned/1"
    assert literal in neg_paths
    row = next(row for row in negative if row["path"] == literal)
    assert row["left"] == "2" and row["right"] == "1"
    assert time.monotonic() - start < 5
    assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < 64 * 1024**2
    print("PASS: six retained LLBC hashes, all field differences, keyed short names, negative control and resource guards")


if __name__ == "__main__":
    main()
