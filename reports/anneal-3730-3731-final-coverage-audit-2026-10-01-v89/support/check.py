#!/usr/bin/env python3
"""Read-only v89 published-object and inherited-ledger audit."""
import argparse
import csv
from collections import Counter
import hashlib
import io
import json
import os
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
M = json.loads((HERE / "delta.json").read_text())

def sha(data): return hashlib.sha256(data).hexdigest()
def git(root, *args):
    env = dict(os.environ, GIT_NO_LAZY_FETCH="1")
    return subprocess.check_output(["git", *args], cwd=root, env=env)
def committed(root, revision, path): return git(root, "show", f"{revision}:{path}")
def rows(data): return list(csv.DictReader(io.StringIO(data.decode())))
def ancestor(root, old, new):
    env = dict(os.environ, GIT_NO_LAZY_FETCH="1")
    return subprocess.run(["git", "merge-base", "--is-ancestor", old, new], cwd=root, env=env,
                          capture_output=True).returncode == 0
def validate_package(root, package):
    c, n = package["publication_revision"], package["package"]
    assert ancestor(root, c, M["reference_head"]), (n, c)
    path = f"reports/{n}"
    assert git(root, "rev-parse", f"{c}:{path}").decode().strip() == package["tree"]
    assert sha(committed(root, c, f"{path}/REPORT.md")) == package["report_sha256"]
    assert sha(committed(root, c, f"{path}/REPORT.json")) == package["metadata_sha256"]
    assert json.loads(committed(root, c, f"{path}/REPORT.json"))["subjects"]

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--reference-root", type=Path,
                   default=Path(os.environ["REFERENCE_ROOT"]) if os.environ.get("REFERENCE_ROOT") else None)
    a = p.parse_args()
    if a.reference_root is None: p.error("pass --reference-root or set REFERENCE_ROOT")
    root = a.reference_root
    assert git(root, "cat-file", "-t", M["reference_head"]).strip() == b"commit"
    assert ancestor(root, M["reference_head"], git(root, "rev-parse", "HEAD").decode().strip())
    assert ancestor(root, M["baseline_v87_head"], M["reference_head"])
    assert ancestor(root, M["baseline_v88_head"], M["reference_head"])
    assert M["baseline_v88_head"] == M["v88"]["publication_revision"]
    assert git(root, "rev-parse", f'{M["reference_head"]}^{{tree}}').decode().strip() == M["reference_tree"]
    catalog_bytes = committed(root, M["reference_head"], "CATALOG.json")
    assert sha(catalog_bytes) == M["catalog_sha256"]
    assert git(root, "rev-parse", f'{M["reference_head"]}:CATALOG.json').decode().strip() == M["catalog_blob"]
    catalog = json.loads(catalog_bytes)["reports"]
    assert M["schema"] == 1 and M["observed_at"] == "2026-10-01"
    for k in ("v84", "v85", "v86", "v88", "lean_source_delta"):
        validate_package(root, M[k])
    for package in M["supplements"]: validate_package(root, package)
    validate_package(root, M["pre_v86_runtime"])
    validate_package(root, M["r428_canary"])
    v88_delta = committed(root, M["v88"]["publication_revision"], f'reports/{M["v88"]["package"]}/support/delta.json')
    assert sha(v88_delta) == M["v88_delta_sha256"]
    assert json.loads(v88_delta)["reference_head"] == M["supplements"][-1]["publication_revision"]
    assert len(M["supplements"]) == 13
    ids = [rid for package in M["supplements"] for rid in package["inventory_ids"]]
    assert len(ids) == len(set(ids)) == 17
    assert all(x["evidence_kind"] == "runtime_fixture" for x in M["supplements"])
    expected_new = {
        "rustc-local-identity-r534-r565-may-to-september-2026-10-01": (["R534"], ["R565"]),
        "lean-batch-diagnostics-r444-r448-430rc2-to-4341-2026-10-01": (["R444", "R448"], []),
        "rust-cfg-hir-mir-r522-may-september-2026-10-01": (["R522"], []),
        "rustc-mir-version-followup-r563-r564-2026-10-01": (["R563", "R564"], []),
        "rust-layout-runtime-may-september-2026-10-01": (["R530"], []),
        "lean-omega-runtime-may-september-2026-10-01": (["R470"], []),
        "lean-unused-simp-hints-runtime-may-september-2026-10-01": (["R488"], []),
    }
    assert {x["package"]:(x["inventory_ids"],x.get("contextual_ids",[])) for x in M["supplements"][6:]} == expected_new
    assert M["pre_v86_runtime"]["inventory_ids"] == ["R121"]
    assert M["pre_v86_runtime"]["contextual_ids"] == []
    assert all(x["package"] in catalog for x in [M["pre_v86_runtime"],M["v88"],M["r428_canary"]] + M["supplements"])
    for package in [M["pre_v86_runtime"],M["v88"],M["r428_canary"]] + M["supplements"]:
        metadata = json.loads(committed(root,package["publication_revision"],f'reports/{package["package"]}/REPORT.json'))
        assert catalog[package["package"]] == metadata

    v84, v85, v86 = M["v84"], M["v85"], M["v86"]
    v85_path = f"reports/{v85['package']}/support/validation-v85.json"
    manifest = committed(root, v85["publication_revision"], v85_path)
    assert sha(manifest) == M["inherited_manifest_sha256"]
    old = json.loads(manifest)
    assert {k:old["counts"][k] for k in M["inherited_counts"]} == M["inherited_counts"]
    assert M["inherited_counts"] == {"investigations":159,"suggestions":174,"suggestion_links":345,
                                      "challenge_rows":333,"version_inventory":581}
    parts = M["inherited_version_partitions"]
    assert parts == {"newer_version_rows":361,"exact_claim_source_review":356,
                     "contextual_or_paired_component_only":5,"source_revision_rows":72,
                     "prior_comparison_rows":11,"source_changed":21,"source_unchanged":55,"source_unavailable":7}
    assert old["counts"]["newer_version_rows"] == parts["newer_version_rows"]
    assert old["counts"]["newer_version_source_status"] == {
        "exact_claim_source_review":356,"contextual_or_paired_component_only":5}
    assert old["counts"]["source_revision_rows"] == 72 and old["counts"]["prior_comparison_rows"] == 11
    assert old["counts"]["source_83_relations"] == {"changed":21,"unchanged":55,"unavailable":7}

    base = f"reports/{v84['package']}/support/"
    filemap = {"investigation-final-v80.csv":"investigations",
               "3730-crosswalk-final-v80.csv":"suggestions",
               "row-challenge-v80.json":"challenge_rows",
               "version-inventory-ebcdcad-581.csv":"version_inventory"}
    frozen = {}
    for name in filemap:
        data = committed(root, v84["publication_revision"], base + name)
        assert sha(data) == old["preserved_file_sha256"][name], name
        frozen[name] = data
    investigations = rows(frozen["investigation-final-v80.csv"])
    suggestions = rows(frozen["3730-crosswalk-final-v80.csv"])
    challenges = json.loads(frozen["row-challenge-v80.json"])
    inventory = rows(frozen["version-inventory-ebcdcad-581.csv"])
    assert len(investigations) == 159 and len(suggestions) == 174 and len(challenges) == 333 and len(inventory) == 581
    assert Counter(r["v80_status"] for r in investigations) == M["inherited_investigation_statuses"] == {
        "partial":151,"complete":4,"conditional":3,"not-run":1}
    links = [dest for row in suggestions for dest in row["3731_destinations"].split(";")]
    assert len(links) == 345 and all(re.fullmatch(r"I\d{3}", x) for x in links)
    by_id = {r["inventory_id"]: r for r in inventory}
    assert len(by_id) == 581
    classification = Counter(r["classification"] for r in inventory)
    assert classification == {"newer_version_recheck":361,"source_revision_recheck":72,
                              "prior_comparison":11,"incidental_or_citation":136,"no_newer_release":1}
    for package in M["supplements"]:
        for rid in package["inventory_ids"]:
            assert rid in by_id
            assert by_id[rid]["report_md_at_commit"].startswith("reports/")
    assert "R121" in by_id and "R565" in by_id

    matrix_info = M["version_matrix"]
    matrix_bytes = (HERE.parent / matrix_info["path"]).read_bytes()
    assert sha(matrix_bytes) == matrix_info["sha256"]
    matrix = rows(matrix_bytes)
    assert len(matrix) == matrix_info["rows"] == 648
    assert matrix_info["frozen_inventory_rows"] == 581
    assert matrix_info["post_frozen_report_rows"] == 67
    assert Counter(r["inventory_id"] for r in matrix)["post581"] == 67
    assert len({r["report_path"] for r in matrix}) == 648
    report_names = git(root, "ls-tree", "-d", "--name-only", f'{M["reference_head"]}:reports').decode().splitlines()
    assert len(report_names) == 648
    assert {r["report_path"] for r in matrix} == {f"reports/{n}/REPORT.md" for n in report_names}
    matrix_by_id = {r["inventory_id"]:r for r in matrix if r["inventory_id"] != "post581"}
    assert set(matrix_by_id) == set(by_id)
    for rid, original in by_id.items():
        assert matrix_by_id[rid]["report_path"] == original["report_md_at_commit"]
        assert matrix_by_id[rid]["classification"] == original["classification"]
    direct_ids = set(ids + M["pre_v86_runtime"]["inventory_ids"])
    assert len(direct_ids) == matrix_info["direct_runtime_original_ids"] == 18
    contextual_ids = {rid for p in M["supplements"] for rid in p.get("contextual_ids",[])}
    assert contextual_ids == set(matrix_info["contextual_only_original_ids"]) == {"R565"}
    assert "R565" not in direct_ids
    r565 = matrix_by_id["R565"]
    assert r565["runtime_coverage"].startswith("contextual only: reports/")
    assert "rustc-local-identity-r534-r565-may-to-september-2026-10-01/REPORT.md" in r565["runtime_coverage"]
    assert "no direct R565 runtime comparison" in r565["runtime_coverage"]
    assert "stable-item-identity claim" in r565["runtime_coverage"]
    assert "remains source-only" in r565["local_feasibility_or_blocker"]
    assert "does not establish stable DefPath identity" in r565["local_feasibility_or_blocker"]
    assert len(direct_ids | contextual_ids) == matrix_info["mapped_original_ids"] == 19
    assert len(M["supplements"]) + 1 == matrix_info["runtime_packages_including_pre_v86"] == 14
    for package in [M["pre_v86_runtime"]] + M["supplements"]:
        for rid in package["inventory_ids"] + package.get("contextual_ids",[]):
            assert f"reports/{package['package']}/REPORT.md" in matrix_by_id[rid]["runtime_coverage"]
    canary = M["r428_canary"]
    assert canary["inventory_id"] == "R428" and canary["evidence_kind"] == "partial_canary_resource_stop"
    assert canary["invalidation_matrix_cases_executed"] == 0
    assert (canary["old_exit_code"],canary["new_exit_code"]) == (0,-9)
    assert canary["old_peak_group_rss_kib"] == 1046032 < canary["rss_cap_kib"] == 1048576 < canary["new_peak_group_rss_kib"] == 1096880
    r428 = matrix_by_id["R428"]
    assert f"reports/{canary['package']}/REPORT.md" in r428["runtime_coverage"]
    assert "canary only" in r428["runtime_coverage"] and "zero invalidation matrix cases tested" in r428["runtime_coverage"]
    assert "not disk" in r428["local_feasibility_or_blocker"] and "RSS >1 GiB" in r428["local_feasibility_or_blocker"]
    canary_analysis = json.loads(committed(root, canary["publication_revision"], f"reports/{canary['package']}/analysis.json"))
    assert canary_analysis["invalidation_matrix_cases_executed"] == 0
    assert canary_analysis["corrected_old_build_succeeded"] and canary_analysis["corrected_new_build_killed_at_rss_cap"]

    resource = M["resource_observation"]
    assert set(resource["pages"]) == {"free","inactive","speculative"}
    assert abs(resource["reclaimable_percent"] - 100*resource["page_bytes"]*sum(resource["pages"].values())/resource["memory_bytes"]) < 1e-9
    assert resource["lean_server_min_reclaimable_percent_exclusive"] == 30
    assert resource["lake_build_min_disk_bytes_exclusive"] == 10*1024**3
    assert resource["batch_min_reclaimable_percent_exclusive"] == 20
    assert resource["batch_min_disk_bytes_exclusive"] == 1024**3
    assert 20 < resource["reclaimable_percent"] < 30
    assert resource["disk_free_bytes"] > 10*1024**3

    v86_path = f"reports/{v86['package']}/support/"
    v86_delta = committed(root, v86["publication_revision"], v86_path + "delta.json")
    assert sha(v86_delta) == M["v86_delta_sha256"]
    prior = json.loads(v86_delta)
    assert prior["reference_head"] == M["lean_source_delta"]["publication_revision"]
    assert prior["inherited_counts"] == M["inherited_counts"]
    issue = committed(root, v86["publication_revision"], v86_path + "issue-observation-2026-10-01.json")
    assert sha(issue) == M["v86_issue_observation_sha256"]
    assert M["issue_state_source"] == "inherited_v86_read_only_observation_no_new_issue_read_or_mutation"
    assert [(x["number"],x["status"]) for x in json.loads(issue)["issues"]] == [
        (3731,"Open"),(3730,"Closed as not planned")]
    assert prior["admission"]["lean_server_launched"] is False

    report = (HERE.parent / "REPORT.md").read_text()
    for package in [M[k] for k in ("v84","v85","v86","v88","lean_source_delta","pre_v86_runtime","r428_canary")] + M["supplements"]:
        link = f"../{package['package']}/REPORT.md"
        assert link in report, link
        assert (root / "reports" / package["package"] / "REPORT.md").is_file()
    assert "support/delta.json" in report and "support/check.py" in report
    assert "support/version-coverage-matrix-20261001-v89.csv" in report
    assert "R565 is linked as context only" in report
    assert "zero R428 invalidation matrix cases" in report
    assert "**19,239,747,584** free disk bytes" in report
    print(f"PASS: {len(M['supplements'])} post-v86 supplements plus R121, {len(direct_ids)} direct / "
          f"{len(contextual_ids)} contextual original IDs, R428 zero-case RSS stop, 648 report matrix, "
          "159/174/345/333/581 inherited, 356/5 and 21/55/7 source partitions, ancestry and hashes")

if __name__ == "__main__": main()
