#!/usr/bin/env python3
"""Check the bounded Charon control outcomes and record run-specific witnesses."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RAW = ROOT / "results.json"


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    raw = json.loads(RAW.read_text())
    for key in ("direct_distinct", "cargo_distinct"):
        cell = raw[key]
        assert [r["rc"] for r in cell["processes"]] == [0, 0]
        assert set(cell["files"]) == {"alpha.llbc", "beta.llbc"}
        assert {x["crate"] for x in cell["files"].values()} == {"alpha", "beta"}
        assert all(x["parseable"] and not x["has_errors"] for x in cell["files"].values())
    assert all(x["command"]["rc"] == 0 and x["llbc"]["crate"] == "alpha" for x in raw["restart"])
    assert raw["restart"][0]["llbc"]["local_names"] == raw["restart"][1]["llbc"]["local_names"]
    assert raw["restart"][0]["llbc"]["local_body_sha256"] == raw["restart"][1]["llbc"]["local_body_sha256"]
    variants = {x["case"]: x for x in raw["variants"]}
    assert variants["reordered"]["llbc"]["local_names"] == ["alpha::common", "alpha::marker_alpha"]
    assert variants["flag-off"]["llbc"]["local_names"] == ["alpha::marker_alpha", "alpha::common"]
    assert variants["flag-on"]["llbc"]["local_names"] == ["alpha::marker_alpha", "alpha::common", "alpha::flagged"]
    collisions = {}
    for key in ("direct_collisions", "cargo_collisions"):
        rows = raw[key]
        assert all([p["rc"] for p in x["processes"]] == [0, 0] for x in rows)
        assert all(x["file"]["exists"] for x in rows)
        collisions[key] = {"rounds": len(rows),
            "parseable": sum(x["file"]["parseable"] for x in rows),
            "malformed": sum(not x["file"]["parseable"] for x in rows),
            "round_details": [{"round": x["round"], "parseable": x["file"]["parseable"],
                              "crate": x["file"].get("crate"), "sha256": x["file"]["sha256"],
                              "parse_error": x["file"].get("parse_error")} for x in rows]}
    multi = raw["multi_collisions"]
    assert all([p["rc"] for p in x["processes"]] == [0, 0] for x in multi)
    assert all(x["postcard"]["exists"] for x in multi)
    collisions["multi_collisions"] = {"rounds": len(multi),
        "json_malformed": sum(not x["json"]["parseable"] for x in multi),
        "postcard_unreadable": sum(x["postcard"]["pretty_print_rc"] != 0 for x in multi),
        "json_postcard_subject_mismatch_when_both_readable": sum(
            x["json"].get("crate") != x["postcard"]["pretty_subject"] for x in multi
            if x["json"]["parseable"] and x["postcard"]["pretty_print_rc"] == 0),
        "round_details": [{"round": x["round"], "json_parseable": x["json"]["parseable"],
                           "json_crate": x["json"].get("crate"),
                           "postcard_readable": x["postcard"]["pretty_print_rc"] == 0,
                           "postcard_subject": x["postcard"]["pretty_subject"],
                           "json_sha256": x["json"]["sha256"],
                           "postcard_sha256": x["postcard"]["sha256"]} for x in multi]}
    assert collisions["direct_collisions"]["malformed"] + collisions["cargo_collisions"]["malformed"] > 0
    warm = raw["warm"]
    assert [x["stage"] for x in warm] == ["first", "unchanged", "source-touched"]
    assert all(x["command"]["rc"] == 0 and x["output"]["parseable"] for x in warm)
    stale = raw["failed_over_stale"]
    assert stale["seed"]["rc"] == 0 and stale["failed"]["rc"] != 0
    assert stale["before"]["sha256"] == stale["after"]["sha256"]
    before = raw["kill_before_reader"]
    first = raw["kill_after_first_bytes"]
    between = raw["kill_between_formats"]
    assert before["alive_before_kill"] and before["rc"] == -9 and before["fifo_is_fifo"]
    assert first["alive_at_first_bytes"] and first["rc"] == -9
    assert first["captured_prefix_bytes"] > 0 and first["prefix_json_parseable"] is False
    assert between["alive_with_complete_json"] and between["rc"] == -9
    assert between["json_before_kill"]["parseable"] and between["json_after_kill"]["parseable"]
    assert between["postcard_is_fifo"] and not between["postcard_is_regular"]
    retry = raw["retry_after_kill"]
    assert retry["command"]["rc"] == 0 and retry["output"]["parseable"] and retry["output"]["crate"] == "large"
    retry_multi = raw["retry_multi_after_kill"]
    assert retry_multi["command"]["rc"] == 0 and retry_multi["json"]["parseable"]
    assert retry_multi["postcard"]["exists"] and retry_multi["postcard"]["pretty_print_rc"] == 0
    artifacts = {p.name: {"bytes": p.stat().st_size, "sha256": sha(p)}
                 for p in sorted((ROOT/"artifacts").iterdir()) if p.is_file()}
    summary = {"raw_sha256": sha(RAW), "tool_hashes": {k: raw["tools"][k] for k in
               ("charon_sha256", "cargo_sha256", "rustc_sha256")},
               "source_hashes": raw["source_hashes"],
               "distinct_outputs": {k: {name: {"crate": info["crate"], "sha256": info["sha256"]}
                                    for name, info in raw[k]["files"].items()}
                                    for k in ("direct_distinct", "cargo_distinct")},
               "restart_hashes": [x["llbc"]["sha256"] for x in raw["restart"]],
               "variants": {k: {"source_sha256": x["source_sha256"], "flags": x["flags"],
                              "llbc_sha256": x["llbc"]["sha256"], "local_names": x["llbc"]["local_names"]}
                            for k, x in variants.items()},
               "collisions": collisions,
               "warm": [{"stage": x["stage"], "rc": x["command"]["rc"],
                         "output_sha256": x["output"]["sha256"],
                         "cargo_compiled": "Compiling alpha" in x["command"]["stderr"]} for x in warm],
               "failed_over_stale": {"failed_rc": stale["failed"]["rc"],
                                      "old_hash_retained": stale["before"]["sha256"] == stale["after"]["sha256"],
                                      "sha256": stale["after"]["sha256"], "crate": stale["after"]["crate"]},
               "interruptions": {"before_reader": {"rc": before["rc"], "fifo_is_fifo": before["fifo_is_fifo"]},
                   "after_first_bytes": {"rc": first["rc"], "prefix_bytes": first["captured_prefix_bytes"],
                                         "prefix_sha256": first["captured_prefix_sha256"],
                                         "prefix_parseable": first["prefix_json_parseable"]},
                   "between_formats": {"rc": between["rc"], "first_json_sha256": between["json_after_kill"]["sha256"],
                                       "first_json_parseable": between["json_after_kill"]["parseable"],
                                       "postcard_is_fifo": between["postcard_is_fifo"]},
                   "retry_single": {"rc": retry["command"]["rc"], "sha256": retry["output"]["sha256"],
                                    "crate": retry["output"]["crate"]},
                   "retry_pair": {"rc": retry_multi["command"]["rc"],
                                  "json_sha256": retry_multi["json"]["sha256"],
                                  "postcard_sha256": retry_multi["postcard"]["sha256"]}},
               "artifacts": artifacts}
    (ROOT/"summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"collision_malformed": {k:v.get("malformed",v.get("json_malformed")) for k,v in collisions.items()},
                      "artifact_count": len(artifacts), "assertions": "passed"}, indent=2))


if __name__ == "__main__": main()
