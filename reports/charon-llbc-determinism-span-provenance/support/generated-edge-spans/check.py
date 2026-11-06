#!/usr/bin/env python3
"""Offline byte/source/span/resource audit for the one generated edge fixture."""

import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    raw = (HERE / "fixture/generated_template.rs").read_bytes()
    generated = (HERE / "generated.rs").read_bytes()
    llbc_raw = (HERE / "generated.llbc").read_bytes()
    host = (HERE / "fixture/src/lib.rs").read_bytes()
    declaration = json.loads((HERE / "predeclared.json").read_text())
    result = json.loads((HERE / "results.json").read_text())
    llbc = json.loads(llbc_raw)
    metadata = json.loads((HERE / "REPORT.json").read_text())
    assert metadata["observed_at"] == "2026-09-30"
    tool_subject = next(s for s in metadata["subjects"] if "charon_sha256" in s["identity"])
    assert all(tool_subject["identity"][f"{name}_sha256"] == result["tool_sha256"][name]
               for name in ("charon", "cargo", "rustc"))
    source_subject = next(s for s in metadata["subjects"] if "results_sha256" in s["identity"])
    identity = source_subject["identity"]
    assert identity["raw_generated_sha256"] == sha(generated)
    assert identity["llbc_sha256"] == sha(llbc_raw)
    assert identity["predeclared_sha256"] == sha((HERE / "predeclared.json").read_bytes())
    assert identity["results_sha256"] == sha((HERE / "results.json").read_bytes())
    assert raw == generated and len(raw) == 201
    assert declaration["source_sha256"] == sha(raw)
    assert declaration["source_bytes"] == len(raw)
    assert declaration["source_line_ending"] == "CRLF"
    assert raw.count(b"\r\n") == 6 and raw.count(b"\n") == 6
    normalized = raw.replace(b"\r\n", b"\n")
    assert normalized != raw and len(raw) - len(normalized) == 6
    assert identity["llbc_embedded_normalized_sha256"] == sha(normalized)
    assert result["fixture_sha256"]["generated_template.rs"] == sha(raw)
    assert result["generated_source"]["sha256"] == sha(generated)
    assert result["generated_source"]["bytes"] == len(generated)
    assert len(result["generated_candidates"]) == 1
    assert result["generated_candidates"][0] == result["generated_source"]["original_path"]
    assert result["status"] == "completed" and result["stop_reason"] is None
    assert result["command"]["exit"] == 0
    assert result["command"]["argv"][1:4] == ["cargo", "--preset", "aeneas"]
    assert "--offline" in result["command"]["argv"]
    assert result["command"]["environment"]["CARGO_NET_OFFLINE"] == "true"
    assert result["command"]["environment"]["CARGO_BUILD_JOBS"] == "1"
    assert len(result["command"]["driver_lines"]) == 2
    assert "--crate-name build_script_build" in result["command"]["driver_lines"][0]
    assert "--crate-name generated_span_probe" in result["command"]["driver_lines"][1]
    assert result["preflight"]["host"]["estimated_reclaimable_percent"] > 30
    assert result["command_preflight"]["host"]["estimated_reclaimable_percent"] > 30
    assert result["preflight"]["host"]["free_disk_bytes"] > 10 * 1024**3
    assert result["command_preflight"]["host"]["free_disk_bytes"] > 10 * 1024**3
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
        output = (HERE / "raw" / f"charon.{suffix}").read_bytes()
        assert sha(output) == result["command"][f"{suffix}_sha256"]
        assert len(output) == result["command"][f"{suffix}_bytes"]
    assert result["output"] == {"sha256": sha(llbc_raw), "bytes": len(llbc_raw)}
    assert llbc["has_errors"] is False
    files = {entry["id"]: entry for entry in llbc["translated"]["files"]}
    assert files[0]["name"] == {"Local": "src/lib.rs"}
    assert files[0]["contents"].encode("utf-8") == host
    assert files[1]["name"] == {"Local": result["generated_source"]["original_path"]}
    assert files[1]["contents"].encode("utf-8") == normalized
    assert b"\r" not in files[1]["contents"].encode("utf-8")
    assert files[2]["contents"] is None and files[3]["contents"] is None

    expected = {item["name"]: item for item in declaration["items"]}
    assert len(expected) == 4
    source = raw.decode("utf-8")
    observations, excluded = [], []
    for category in ("fun_decls", "global_decls"):
        for item in llbc["translated"][category]:
            meta = item["item_meta"]
            span = meta["span"]["data"]
            name = "::".join(part["Ident"][0] for part in meta["name"] if "Ident" in part)
            if span["file_id"] != 1:
                excluded.append({"category": category, "name": name,
                                 "file_id": span["file_id"]})
                continue
            assert name in expected
            oracle = expected[name]
            begin, end = oracle["scalar_range"]
            assert source[begin:end] == oracle["source_text"]
            assert sha(source[begin:end].encode("utf-8")) == oracle["source_utf8_sha256"]
            assert [len(source[:begin].encode("utf-8")),
                    len(source[:end].encode("utf-8"))] == oracle["byte_range"]
            expected_text = oracle["source_text"].replace("\r\n", "\n")
            assert meta["source_text"] == expected_text
            assert source.count(oracle["source_text"]) == 1
            observed = {"begin": span["beg"], "end": span["end"]}
            matched = {}
            for mode in oracle["begin"]["columns"]:
                matched[mode] = (
                    observed["begin"] == {"line": oracle["begin"]["line"],
                                          "col": oracle["begin"]["columns"][mode]} and
                    observed["end"] == {"line": oracle["end"]["line"],
                                        "col": oracle["end"]["columns"][mode]})
            assert matched["tab_fixed_four"]
            observations.append({"category": category, "name": name,
                                 "observed": observed, "hypothesis_matches": matched,
                                 "source_text_crlf_normalized":
                                     oracle["source_text"] != expected_text,
                                 "source_text": meta["source_text"]})
    assert len(observations) == 6
    assert {item["name"] for item in observations} == set(expected)
    assert len(excluded) == 1 and excluded[0]["name"] == "core::str::len"
    assert next(item for item in observations if item["name"].endswith("tabbed_multiline"))["observed"] == {
        "begin": {"line": 2, "col": 4}, "end": {"line": 5, "col": 5}}
    assert next(item for item in observations if item["name"].endswith("after_prefix"))["observed"] == {
        "begin": {"line": 1, "col": 35}, "end": {"line": 1, "col": 71}}
    mismatch = {mode: sum(not item["hypothesis_matches"][mode] for item in observations)
                for mode in observations[0]["hypothesis_matches"]}
    assert mismatch["tab_fixed_four"] == 0
    assert mismatch["tab_one"] > 0 and mismatch["tab_fixed_eight"] > 0
    assert mismatch["tab_stop_four"] > 0 and mismatch["tab_stop_eight"] > 0
    assert sum(item["source_text_crlf_normalized"] for item in observations) == 1
    assert all(item["source_text"] not in host.decode("utf-8") for item in observations)
    assert all(item["observed"]["begin"]["col"] + 1 !=
               expected[item["name"]]["begin"]["columns"]["tab_fixed_four"]
               for item in observations)
    assert all(item["observed"]["end"]["col"] + 1 !=
               expected[item["name"]]["end"]["columns"]["tab_fixed_four"]
               for item in observations)
    changed = raw.replace(b"{ 1 }", b"{ 2 }", 1)
    assert changed != raw and changed.replace(b"\r\n", b"\n") != files[1]["contents"].encode("utf-8")
    comparison = {
        "schema": 1,
        "template_sha256": sha(raw), "generated_sha256": sha(generated),
        "embedded_normalized_sha256": sha(normalized), "llbc_sha256": sha(llbc_raw),
        "raw_source_bytes": len(raw), "normalized_embedded_bytes": len(normalized),
        "generated_file_id": 1, "observations": observations,
        "excluded_nonlocal": excluded, "mismatch_counts": mismatch,
        "controls": {"wrong_file_id_zero_rejected": True,
                     "begin_plus_one_rejected": True,
                     "inclusive_end_rejected": True,
                     "changed_template_bytes_rejected": True,
                     "raw_crlf_equals_embedded_rejected": True},
    }
    comparison_path = HERE / "comparison.json"
    serialized = json.dumps(comparison, indent=2, ensure_ascii=False) + "\n"
    if "--write" in sys.argv[1:]:
        comparison_path.write_text(serialized)
    else:
        assert comparison_path.read_text() == serialized
    print(json.dumps({"generated_records": len(observations),
                      "multiline_normalized_records": sum(item["source_text_crlf_normalized"]
                                                          for item in observations),
                      "mismatch_counts": mismatch,
                      "raw_sha256": sha(raw), "normalized_sha256": sha(normalized)},
                     ensure_ascii=False))


if __name__ == "__main__":
    main()
