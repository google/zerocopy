#!/usr/bin/env python3
"""Extract asserted semantic outcomes from raw probe results."""
import csv
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RAW = ROOT / "results.json"


def diagnostics(command):
    found = []
    for line in command["stdout"].splitlines():
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue
        found.append({k: obj.get(k) for k in ("severity", "data", "pos")})
    return found


def goal(reply):
    return reply.get("result", {}).get("goals")


def batch_semantics(command):
    ds = diagnostics(command)
    return {"rc": command["rc"], "diagnostics": ds,
            "axiom_free": any(x["data"] == "'generatedEq' does not depend on any axioms" for x in ds),
            "sorry_ax": any("sorryAx" in str(x["data"]) for x in ds),
            "value": next((x["data"] for x in ds if x["data"] in ("7", "9")), None),
            "false_proposition": any("is false" in str(x["data"]) for x in ds)}


def main():
    raw = json.loads(RAW.read_text())
    report = {"raw_sha256": hashlib.sha256(RAW.read_bytes()).hexdigest(),
              "toolchains": {}, "assertions": []}
    rows = []
    for version, v in raw["versions"].items():
        baseline = v["baseline"]
        clean_inv, prepared_inv = v["clean_inventory"], v["prepared_inventory_before"]
        assert clean_inv == prepared_inv
        assert prepared_inv == v["prepared_inventory_after"]
        lib = ".lake/build/lib/lean/Dep.olean"
        library_sha = clean_inv[lib]["sha256"]
        assert v["source_only"]["inventory"][lib]["sha256"] == library_sha
        artifact_sha = v["artifact_only"]["inventory"][lib]["sha256"]
        assert artifact_sha != library_sha
        cell = {"lean_sha256": v["lean_sha256"], "lake_sha256": v["lake_sha256"],
                "version_output": [x["stdout"].strip() for x in v["versions"]],
                "proof_source_sha256": v["source_hashes"]["Generated.lean"],
                "dependency_source_sha256": v["source_hashes"]["Dep.lean"],
                "baseline_dep_olean_sha256": library_sha,
                "replacement_dep_olean_sha256": artifact_sha,
                "baseline": {}, "source_only": {}, "artifact_only": {}, "refresh": {}}
        semantic_references = []
        for kind, item in baseline.items():
            assert item["setup"]["rc"] == 0
            cell["baseline"][kind] = {"setup_rc": 0, "batch": {}, "live": {}}
            for command in item["batch"]:
                mode = "direct" if "direct-batch" in command["label"] else "lake-env"
                sem = batch_semantics(command)
                assert sem["rc"] == 0 and sem["axiom_free"] and sem["value"] == "7"
                cell["baseline"][kind]["batch"][mode] = sem
                semantic_references.append(sem)
                rows.append({"version": version, "generation": kind, "interface": mode+" batch",
                             "rc": sem["rc"], "value": sem["value"], "axiom_free": sem["axiom_free"],
                             "goal_count": "", "olean_sha256": library_sha})
            for mode, run in item["live"].items():
                assert run["wait"].get("result") == {}
                assert goal(run["goal"]) == []
                texts = [x.get("message") for p in run["diagnostics"] for x in p.get("diagnostics", [])]
                assert "'generatedEq' does not depend on any axioms" in texts
                assert "7" in texts
                cell["baseline"][kind]["live"][mode] = {
                    "goal_count": 0, "diagnostic_messages": texts, "wait_succeeded": True}
                rows.append({"version": version, "generation": kind, "interface": mode+" live",
                             "rc": 0, "value": "7", "axiom_free": True,
                             "goal_count": 0, "olean_sha256": library_sha})
        assert all(x == semantic_references[0] for x in semantic_references)
        for generation, expected_value, expected_rc, expected_axiom in (
                ("source_only", "7", 0, True), ("artifact_only", "9", 1, False)):
            entry = v[generation]
            sems = {}
            for mode in ("direct_batch", "lake_batch"):
                sem = batch_semantics(entry[mode])
                assert sem["rc"] == expected_rc and sem["value"] == expected_value
                assert sem["axiom_free"] == expected_axiom
                assert sem["false_proposition"] == (generation == "artifact_only")
                sems[mode] = sem
                rows.append({"version": version, "generation": generation,
                             "interface": mode.replace("_", " "), "rc": sem["rc"],
                             "value": sem["value"], "axiom_free": sem["axiom_free"],
                             "goal_count": "", "olean_sha256": library_sha if generation == "source_only" else artifact_sha})
            assert sems["direct_batch"] == sems["lake_batch"]
            no_build_rc = entry["no_build"]["rc"]
            assert no_build_rc == (3 if generation == "source_only" else 0)
            cell[generation] = {"batch": sems, "no_build_rc": no_build_rc,
                                "dependency_source_sha256": entry["inventory"]["Dep.lean"]["sha256"]}
            if generation == "source_only":
                cell[generation]["live"] = {}
                for mode, observed in entry["live"].items():
                    run = observed["result"]
                    assert observed["before_inventory"][lib]["sha256"] == library_sha
                    after_olean = observed["after_inventory"][lib]["sha256"]
                    assert after_olean != library_sha
                    assert run["wait"].get("result") == {}
                    assert goal(run["goal"]) == ["⊢ depValue + 1 = 8"]
                    texts = [x.get("message") for p in run["diagnostics"]
                             for x in p.get("diagnostics", [])]
                    assert any("is false" in str(x) for x in texts)
                    assert "'generatedEq' depends on axioms: [sorryAx]" in texts
                    assert "9" in texts
                    cell[generation]["live"][mode] = {
                        "goal_count": 1, "diagnostic_messages": texts, "wait_succeeded": True,
                        "before_olean_sha256": library_sha, "after_olean_sha256": after_olean}
                    rows.append({"version": version, "generation": generation,
                                 "interface": mode+" live", "rc": 0,
                                 "value": "9", "axiom_free": False,
                                 "goal_count": 1, "olean_sha256": after_olean})
        for mode, entry in v["artifact_only_refresh"].items():
            assert entry["old_olean_sha256"] == library_sha
            assert entry["new_olean_sha256"] == artifact_sha
            assert goal(entry["old_goal_before"]) == []
            assert goal(entry["old_goal_after"]) == []
            assert goal(entry["reopened_goal"]) == ["⊢ depValue + 1 = 8"]
            fresh = batch_semantics(entry["fresh_batch"])
            assert fresh["rc"] == 1 and fresh["value"] == "9" and fresh["false_proposition"]
            label = version+"-artifact-"+mode
            published = [e["message"].get("params", {}) for e in raw["events"]
                         if e.get("kind") == "server" and e.get("label") == label and
                         e["message"].get("method") == "textDocument/publishDiagnostics"]
            reopened_messages = [d.get("message") for p in published if p.get("version") == 2
                                 for d in p.get("diagnostics", [])]
            assert any("is false" in str(m) for m in reopened_messages)
            assert "'generatedEq' depends on axioms: [sorryAx]" in reopened_messages
            assert "9" in reopened_messages
            cell["refresh"][mode] = {"old_before_goal_count": 0,
                                    "old_after_watcher_goal_count": 0,
                                    "reopened_goal_count": 1,
                                    "reopened_goal": goal(entry["reopened_goal"])[0],
                                    "reopened_diagnostic_messages": list(dict.fromkeys(reopened_messages)),
                                    "fresh_batch": fresh}
        report["toolchains"][version] = cell
        report["assertions"].append(f"{version}: clean/prepared, direct/Lake and refresh checks passed")
    for version, cell in report["toolchains"].items():
        assert cell["proof_source_sha256"] == raw["fixture_proof_sha256"]
    assert report["toolchains"]["v4.29.0"]["baseline_dep_olean_sha256"] != report["toolchains"]["v4.30.0-rc2"]["baseline_dep_olean_sha256"]
    with (ROOT / "matrix.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)
    (ROOT / "summary.json").write_text(json.dumps(report, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"versions": list(report["toolchains"]),
                      "matrix_rows": len(rows), "assertions": report["assertions"]}, indent=2))


if __name__ == "__main__":
    main()
