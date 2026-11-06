#!/usr/bin/env python3
"""Compare Charon generated-file item spans to independently retained bytes."""

import hashlib
import json
from pathlib import Path
import sys
import unicodedata

HERE = Path(__file__).resolve().parent
TEMPLATE = HERE / "fixture/generated_template.rs"
GENERATED = HERE / "generated.rs"
HOST = HERE / "fixture/src/lib.rs"
LLBC = HERE / "generated.llbc"
RESULT = HERE / "results.json"
COMPARISON = HERE / "comparison.json"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def columns(text):
    return {
        "utf8_bytes": len(text.encode("utf-8")),
        "unicode_scalars": len(text),
        "utf16_code_units": len(text.encode("utf-16-le")) // 2,
        "fixture_display_cells": sum(0 if unicodedata.combining(ch)
            else 2 if unicodedata.east_asian_width(ch) in ("W", "F") else 1
            for ch in text),
    }


def main():
    template, generated = TEMPLATE.read_bytes(), GENERATED.read_bytes()
    host, artifact = HOST.read_bytes(), LLBC.read_bytes()
    result, llbc = json.loads(RESULT.read_text()), json.loads(artifact)
    metadata = json.loads((HERE / "REPORT.json").read_text())
    assert metadata["observed_at"] == "2026-09-30"
    tool_subject = next(s for s in metadata["subjects"] if "charon_sha256" in s["identity"])
    fixture_subject = next(s for s in metadata["subjects"] if "template_sha256" in s["identity"])
    assert tool_subject["identity"]["charon_sha256"] == result["tool_sha256"]["charon"]
    assert tool_subject["identity"]["cargo_sha256"] == result["tool_sha256"]["cargo"]
    assert tool_subject["identity"]["rustc_sha256"] == result["tool_sha256"]["rustc"]
    assert fixture_subject["identity"]["template_sha256"] == sha(template)
    assert fixture_subject["identity"]["generated_source_sha256"] == sha(generated)
    assert fixture_subject["identity"]["build_rs_sha256"] == sha((HERE / "fixture/build.rs").read_bytes())
    assert fixture_subject["identity"]["probe_sha256"] == sha((HERE / "probe.py").read_bytes())
    assert fixture_subject["identity"]["results_sha256"] == sha(RESULT.read_bytes())
    assert template == generated
    assert result["fixture_sha256"]["generated_template.rs"] == sha(template)
    assert result["generated_source"] == {
        "sha256": sha(generated), "bytes": len(generated),
        "original_path": result["generated_source"]["original_path"]}
    assert len(result["generated_candidates"]) == 1
    assert result["generated_candidates"][0] == result["generated_source"]["original_path"]
    assert result["status"] == "completed" and result["stop_reason"] is None
    assert result["command"]["exit"] == 0
    assert len(result["command"]["driver_lines"]) == 2
    assert "--crate-name build_script_build" in result["command"]["driver_lines"][0]
    assert "--crate-name generated_span_probe" in result["command"]["driver_lines"][1]
    assert "--lib" in result["command"]["argv"]
    assert "--offline" in result["command"]["argv"]
    assert result["command"]["environment"]["CARGO_NET_OFFLINE"] == "true"
    assert result["command"]["environment"]["CARGO_BUILD_JOBS"] == "1"
    assert result["preflight"]["host"]["estimated_reclaimable_percent"] > 30
    assert result["command_preflight"]["host"]["estimated_reclaimable_percent"] > 30
    assert result["preflight"]["host"]["free_disk_bytes"] > 10 * 1024**3
    assert result["samples"] and result["cleanup"]["work_exists"] is False
    assert result["postrun_process_group_rss_kib"] == 0
    limits = result["limits"]
    for sample in result["samples"]:
        assert sample["host"]["estimated_reclaimable_percent"] >= limits["minimum_live_reclaimable_percent"]
        assert sample["host"]["free_disk_bytes"] >= limits["minimum_free_disk_bytes"]
        assert sample["process_group_rss_kib"] <= limits["maximum_process_group_rss_kib"]
        assert sample["scratch_bytes"] <= limits["maximum_scratch_bytes"]
    assert max(sample["elapsed_seconds"] for sample in result["samples"]) <= limits["timeout_seconds"]
    for suffix in ("stdout", "stderr"):
        raw = (HERE / "raw" / f"charon.{suffix}").read_bytes()
        assert sha(raw) == result["command"][f"{suffix}_sha256"]
    assert result["output"] == {"sha256": sha(artifact), "bytes": len(artifact)}
    assert llbc["has_errors"] is False
    files = {entry["id"]: entry for entry in llbc["translated"]["files"]}
    assert files[0]["name"] == {"Local": "src/lib.rs"}
    assert files[0]["contents"].encode("utf-8") == host
    assert files[1]["name"] == {"Local": result["generated_source"]["original_path"]}
    assert files[1]["contents"].encode("utf-8") == template == generated

    expected = {"generated_span_probe::EMOJI", "generated_span_probe::COMBINING",
                "generated_span_probe::after_emoji",
                "generated_span_probe::after_combining",
                "generated_span_probe::generated_body"}
    lines = generated.decode("utf-8").splitlines()
    observations, excluded = [], []
    for category in ("fun_decls", "global_decls"):
        for item in llbc["translated"][category]:
            meta = item["item_meta"]
            span = meta["span"]["data"]
            name = "::".join(part["Ident"][0] for part in meta["name"] if "Ident" in part)
            if span["file_id"] != 1:
                excluded.append({"category": category, "name": name, "file_id": span["file_id"]})
                continue
            assert name in expected
            source_text = meta["source_text"]
            assert source_text and generated.decode("utf-8").count(source_text) == 1
            assert span["beg"]["line"] == span["end"]["line"]
            line_number = span["beg"]["line"]
            assert 1 <= line_number <= len(lines)
            line = lines[line_number - 1]
            assert line.count(source_text) == 1
            start = line.index(source_text)
            end = start + len(source_text)
            beginning, ending = columns(line[:start]), columns(line[:end])
            observed = {"beg": span["beg"]["col"], "end": span["end"]["col"]}
            matched = {mode: observed == {"beg": beginning[mode], "end": ending[mode]}
                       for mode in beginning}
            assert matched["fixture_display_cells"]
            observations.append({"category": category, "name": name,
                "line": line_number, "source_text": source_text,
                "observed": observed, "predicted_begin": beginning,
                "predicted_end": ending, "matched": matched})
    assert len(observations) == 7 and {row["name"] for row in observations} == expected
    assert len(excluded) == 1 and excluded[0]["name"] == "core::str::len"
    mismatch_counts = {mode: sum(not row["matched"][mode] for row in observations)
                       for mode in observations[0]["matched"]}
    assert mismatch_counts["fixture_display_cells"] == 0
    assert all(mismatch_counts[mode] > 0 for mode in
               ("utf8_bytes", "unicode_scalars", "utf16_code_units"))
    assert b"x + 1" in template
    changed_template = template.replace(b"x + 1", b"x + 9", 1)
    assert changed_template != files[1]["contents"].encode("utf-8")
    assert all(row["observed"]["beg"] + 1 != row["predicted_begin"]["fixture_display_cells"]
               for row in observations)
    assert all(row["observed"]["end"] + 1 != row["predicted_end"]["fixture_display_cells"]
               for row in observations)
    comparison = {"template_sha256": sha(template), "generated_sha256": sha(generated),
        "llbc_sha256": sha(artifact), "generated_file_id": 1,
        "observations": observations, "excluded_nonlocal": excluded,
        "mismatch_counts": mismatch_counts,
        "controls": {"wrong_file_id_zero_rejected": all(
            row["source_text"] not in host.decode("utf-8") for row in observations),
            "begin_plus_one_rejected": True, "inclusive_end_rejected": True,
            "changed_template_bytes_rejected": True}}
    assert comparison["controls"]["wrong_file_id_zero_rejected"]
    serialized = json.dumps(comparison, indent=2, ensure_ascii=False) + "\n"
    if sys.argv[1:] == ["--write"]:
        COMPARISON.write_text(serialized)
    else:
        assert COMPARISON.read_text() == serialized
    print(json.dumps({"generated_records": len(observations),
        "excluded_nonlocal": len(excluded), "mismatch_counts": mismatch_counts,
        "generated_sha256": sha(generated), "llbc_sha256": sha(artifact)},
        ensure_ascii=False))


if __name__ == "__main__":
    main()
