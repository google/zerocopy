#!/usr/bin/env python3
"""Check retained report evidence offline; never invoke Lean or Lake."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).absolute().parent
EVIDENCE = ROOT / "evidence"


def read(name):
    return json.loads((EVIDENCE / name).read_text())


def text(name):
    return (EVIDENCE / name).read_text()


def main():
    index = read("INDEX.json")
    seen = set()
    for item in index["files"]:
        rel = Path(item["output"])
        assert not rel.is_absolute() and ".." not in rel.parts, rel
        assert item["output"] not in seen, rel
        seen.add(item["output"])
        data = (EVIDENCE / rel).read_bytes()
        assert len(data) == item["bytes"], rel
        assert hashlib.sha256(data).hexdigest() == item["output_sha256"], rel
        assert b"/Users/josh" not in data, rel
    actual = {p.relative_to(EVIDENCE).as_posix() for p in EVIDENCE.rglob("*")
              if p.is_file() and p.name != "INDEX.json"}
    assert seen == actual, (seen - actual, actual - seen)

    identity = read("subject-identity.json")
    assert identity["archive"]["sha256"] == (
        "b4e0a5b420eb441e37564c365f06c215f61a3b825fc3df37293da7c3010d2b81")
    assert identity["bundled_lean"]["commit"] == (
        "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc")
    assert len(identity["upstream_package_revisions"]) == 9
    assert len(identity["sample_source_byte_matches"]) == 2

    outcomes = read("selected-outcomes.json")
    passes, failures = outcomes["expected_successes"], outcomes["expected_failures"]
    assert len(passes) == 19 and len(failures) == 7
    assert all(r["exit"] == 0 and r["abort"] is None for r in passes)
    assert all(r["exit"] == 1 and r["abort"] is None for r in failures)
    rows = {r["label"]: r for r in passes + failures}
    assert len(rows) == 26
    for row in rows.values():
        # null means this summary did not attach tracer data; not zero.
        assert row["blocked_shared_attempts"] in (None, 0)
        assert row["network_attempts"] in (None, 0)
    module_prefix = "native-lake-v1-build-"
    modules = ["SdkIdentity", "Config", "Anneal", "Generated",
               "ExpandOutputExpandOutput1d49e11e5683007f.Types",
               "ExpandOutputExpandOutput1d49e11e5683007f.Funs"]
    assert all(rows[module_prefix + module]["exit"] == 0 for module in modules)
    assert "does not depend on any axioms" in text("logs/native-lake-v1-audit.stdout")
    assert "Insufficient number of fields" in text("logs/native-lake-v1-false.stdout")
    assert "'sorry' tactic is forbidden" in text("logs/native-lake-v1-sorry.stdout")
    assert "slice is not valid mach-o file" in text("logs/native-lake-followup-bad-plugin.stdout")
    assert "incompatible header" in text("logs/final-rc2-mismatch.stdout")
    setup = json.loads(text("logs/native-lake-smoke-setup.stdout"))
    assert any(p.endswith("libaeneas_AeneasMeta.dylib") for p in setup["plugins"])
    assert "dyld[" in text("logs/native-plugin-load.selected.txt")
    assert "libaeneas_AeneasMeta.dylib" in text("logs/native-plugin-load.selected.txt")
    coherent = [json.loads(line) for line in text("coherent-sdk-results.jsonl").splitlines()]
    assert len(coherent) == 4
    for row in coherent[:3]:
        assert row["exit"] == 0 and row["abort"] is None
        assert row["blocked_mutations"] == [] and row["network_attempts"] == []
    assert coherent[0]["stdout_tail"].strip() == coherent[3]["view"]
    assert "dyld[" in coherent[1]["stdout_tail"]
    assert "libaeneas_AeneasMeta.dylib" in coherent[1]["stdout_tail"]
    coherent_setup = json.loads(coherent[2]["stdout_tail"])
    assert any(p.endswith("libaeneas_AeneasMeta.dylib") for p in coherent_setup["plugins"])
    for key in ("archive_tree_metadata_unchanged", "selected_shared_artifact_hashes_unchanged",
                "view_and_sdk_content_metadata_unchanged"):
        assert coherent[3][key] is True
    sizes = read("size-and-launcher-identity.json")
    assert sizes["directories"]["primary_sdk_view"]["du_kib"] == 88
    assert sizes["directories"]["v1_workspace"]["du_kib"] == 3284
    assert sizes["launchers"]["coherent_lean"]["bytes"] == 49968
    assert sizes["launchers"]["coherent_lake"]["bytes"] == 51840
    actions = read("followup-local-output-actions.json")["cells"]
    assert "Replayed Smoke" in "\n".join(actions[1]["actions"])
    assert all("Built Smoke" in "\n".join(row["actions"]) for row in (actions[0], actions[2], actions[3]))

    lsp = read("lsp-selected.json")
    assert len(lsp) == 2
    for row in lsp:
        assert row["result"] == "pass" and row["exit"] == 0 and row["abort"] is None
        assert row["goal"]["goals"] == ["⊢ True"]
        assert row["trace"]["blocked_shared_mutations"] == 0
        assert row["trace"]["network_attempts"] == 0
    assert lsp[0]["last_diagnostics_by_version"]["1"] == []
    nav = lsp[1]
    assert nav["false_edit_error_count"] > 0
    assert nav["last_diagnostics_by_version"]["3"] == []
    assert nav["restored_goal"]["goals"] == ["⊢ True"]
    assert nav["definitions"]["aeneas"]["path"].endswith("AeneasMeta/Saturate/Tactic.lean")
    assert nav["definitions"]["aeneas"]["range"]["start"]["line"] == 740
    assert nav["definitions"]["mathlib"]["path"].endswith("Mathlib/Data/Nat/Basic.lean")
    assert nav["definitions"]["mathlib"]["range"]["start"]["line"] == 55

    snapshots = read("snapshot-equality.json")
    assert [s["entry_count_before"] for s in snapshots] == [28893, 217]
    for row in snapshots:
        assert row["byte_equal"] and row["parsed_equal"]
        assert row["entry_count_before"] == row["entry_count_after"]
        assert row["raw_sha256_before"] == row["raw_sha256_after"]
    gap = read("producer-gap.json")
    assert gap["aeneas_dependency_config_olean_present"] is False
    assert any("[anonymous]/lakefile.olean" in r["path"] for r in gap["bundled_backend_config_entries"])
    final = read("final-check.json")
    assert final["completed_expected_command_checks"] == 26
    assert final["archive_unchanged"] and final["sdk_view_unchanged"]
    assert len(final["guard_stops"]) == 5
    assert final["selected_min_memory_free_pct"] >= 27
    assert final["selected_peak_rss_mib"] < 1634
    print(f"PASS: {len(seen)} retained evidence files; 26 command outcomes; coherent SDK; 2 LSP sessions; scoped snapshot digests")


if __name__ == "__main__":
    main()
