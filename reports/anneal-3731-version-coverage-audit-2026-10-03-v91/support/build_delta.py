#!/usr/bin/env python3
"""Build the integrated v91 index from the pinned v90 Git object and frozen inputs."""
import argparse
import csv
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess

BASE = "ba4556c30835b56d108b0a6854a760bccf8438c5"
PACKAGE = Path(__file__).resolve().parents[1]
SUPPORT = PACKAGE / "support"
INPUT = SUPPORT / "source-inputs"
NAME = PACKAGE.name
MATRIX = "reports/anneal-3730-3731-final-coverage-audit-2026-10-01-v90/support/version-coverage-matrix-20261001-v90.csv"
V90 = "reports/anneal-3730-3731-final-coverage-audit-2026-10-01-v90"
LEAN = "reports/lean-lake-4350rc3-output-reference-routing-source-followup-2026-10-03"
RUST = "reports/rust-199-cargo-source-followup-2026-10-03"
INVENTORY = "reports/anneal-3730-3731-residual-38-source-audit-2026-09-30-v85/support/version-inventory-ebcdcad-581.csv"
REVIEW = "reports/sel4-compcert-everest-current-source-review"
OBS = f"{REVIEW}/support/official-source-observation.json"
R578 = "reports/verified-compiler-pass-composition-compcert-3-18-popl-2008/REPORT.md"
R414 = "reports/lake-artifact-cache-publication-restoration-v4-30-0-rc2/REPORT.md"
R578_SOURCE = "no newer official release as of 2026-09-30; published development-master source review: four commits ahead, three R578-mapped blobs unchanged; no proof/runtime execution"
R578_EVIDENCE = f"{REVIEW}/REPORT.md;{OBS}"
R414_SOURCE = "v85 crosswalk: exact_claim_source_review; source_only_no_new_runtime_or_package_execution; Lean/Lake v4.35.0-rc3 output-reference routing predicate changed in mapped Build.Common source; direct Cache.writeOutputs remains; runtime unexecuted"
R414_EVIDENCE = f"reports/lean-lake-430rc2-to-4341-source-review-2026-09-30/support/frozen-cohort.csv;{LEAN}/REPORT.md"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], stderr=subprocess.DEVNULL,
                                   env=dict(os.environ, GIT_NO_LAZY_FETCH="1"))


def obj(root, path):
    return git(root, "show", f"{BASE}:{path}")


def rows(data):
    return list(csv.DictReader(io.StringIO(data.decode("utf-8"))))


def csv_line(fields, row):
    out = io.StringIO(newline="")
    csv.DictWriter(out, fieldnames=fields, lineterminator="\n").writerow(row)
    return out.getvalue().encode()


def load_input(name):
    return (INPUT / name).read_bytes()


def source_metadata():
    expected_lean = {"topics": ["lean", "lean/lake", "anneal/version-review"],
            "subjects": [
                {"name": "Lean/Lake stable v4.34.1", "identity": {"repository": "leanprover/lean4", "revision": "5045d0056413266e57c625dcd7c365b10e377c52", "version": "v4.34.1"}},
                {"name": "Lean/Lake prerelease v4.35.0-rc3", "identity": {"repository": "leanprover/lean4", "revision": "470d5ce1400764999581fd26d5d72b00d990b0f4", "version": "v4.35.0-rc3"}}],
            "observed_at": "2026-10-03"}
    expected_rust = {"topics": ["rust", "cargo", "cargo/feature-resolution", "cargo/incremental-compilation"],
            "subjects": [
                {"name": "Cargo integrated with Rust 1.98.1", "identity": {"repository": "rust-lang/cargo", "revision": "797e8a9bca276c1c9f9f738d2a20f484fa4eea9d", "version": "1.98.1"}},
                {"name": "Rust 1.99.0 release", "identity": {"repository": "rust-lang/rust", "revision": "b940084d7eb6a299eb4bfeb8e34901bc051e7ac4", "version": "1.99.0"}},
                {"name": "Cargo integrated with Rust 1.99.0", "identity": {"repository": "rust-lang/cargo", "revision": "5f94df4789f005f9a352888e8355ffc645b7ed0e", "version": "1.99.0"}},
                {"name": "Persisted version coverage matrix", "identity": {"repository": "google/zerocopy", "revision": BASE, "path": MATRIX}}],
            "observed_at": "2026-10-03"}
    lean = json.loads(load_input("lean-REPORT.json"))
    rust = json.loads(load_input("rust-REPORT.json"))
    assert lean == expected_lean and rust == expected_rust
    assert all(set(x) == {"topics", "subjects", "observed_at"} for x in (lean, rust))
    return {LEAN.split("/")[1]: lean, RUST.split("/")[1]: rust,
            NAME: json.loads((PACKAGE / "REPORT.json").read_text())}


def build(root):
    assert git(root, "rev-parse", BASE).decode().strip() == BASE
    base = obj(root, MATRIX)
    assert digest(base) == "0e308f4cb43bee371c29f7dd4e83b9a2e8af0ebb0c2c8af26178907c515dbeb3"
    original = rows(base)
    assert len(original) == 651 and len({r["report_path"] for r in original}) == 651
    fields = list(original[0])
    assert base.count(b"\n") == 652 and b"\r" not in base
    by_id = {r["inventory_id"]: r for r in original if r["inventory_id"].startswith("R")}
    assert len(by_id) == 581
    assert by_id["R578"]["report_path"] == R578 and by_id["R414"]["report_path"] == R414
    assert by_id["R578"]["classification"] == "no_newer_release"
    frozen = [r for r in rows(obj(root, INVENTORY)) if r["inventory_id"] == "R578"]
    assert len(frozen) == 1 and frozen[0]["classification"] == "no_newer_release"
    assert frozen[0]["report_md_at_commit"] == R578
    assert frozen[0]["exact_pinned_subject_identities_json"] == by_id["R578"]["pinned_subjects_json"]
    cc = [r for r in json.loads(obj(root, OBS))["repositories"] if r["repository"] == "AbsInt/CompCert"]
    assert len(cc) == 1
    cc = cc[0]
    assert cc["pinned_commit"] == "74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6"
    assert cc["selected_current_commit"] == "66a9fd06ef88619cc94765ca995a1018f7259b5c"
    assert cc["compare"]["ahead_by"] == 4 and cc["compare"]["behind_by"] == 0
    assert cc["release"]["tag_name"] == "v3.18"
    assert {r["path"] for r in cc["mapped_files"]} == {"VERSION", "common/Smallstep.v", "driver/Compiler.v"}
    assert all(r["pinned_blob_sha1"] == r["current_blob_sha1"] for r in cc["mapped_files"])

    lean_report = load_input("lean-REPORT.md")
    lean_manifest = json.loads(load_input("lean-verification-manifest.json"))
    assert digest(lean_report) == lean_manifest["sha256"]["REPORT.md"]
    assert digest(load_input("lean-REPORT.json")) == lean_manifest["sha256"]["REPORT.json"]
    assert lean_manifest["reference_commit"] == BASE and lean_manifest["matrix_rows"] == ["R414"]
    assert lean_manifest["source_result"] == "narrow_source_delta" and lean_manifest["runtime_result"] == "unexecuted"
    assert "pkg.wsIdx = ctx.outputsIdx" in lean_report.decode() and "Cache.writeOutputs" in lean_report.decode()

    rust_report = load_input("rust-REPORT.md")
    rust_manifest = json.loads(load_input("rust-provenance.json"))
    rust_bytes = load_input("rust-matrix-delta.json")
    rust_delta = json.loads(rust_bytes)
    assert digest(load_input("rust-REPORT.json")) == rust_manifest["evidence_sha256"]["REPORT.json"]
    assert digest(rust_report) == rust_manifest["evidence_sha256"]["REPORT.md"]
    assert digest(rust_bytes) == rust_manifest["evidence_sha256"]["matrix-delta.json"]
    assert rust_delta["base_reference"] == BASE and rust_delta["base_matrix_path"] == MATRIX
    assert rust_delta["base_matrix_sha256"] == digest(base)
    assert rust_delta["integrated_report_path"] == f"{RUST}/REPORT.md"
    assert rust_delta["integration"]["status"] == "applied_by_integrated_v91_coverage_matrix"
    assert rust_delta["release_evidence"]["source_commit"] == "b940084d7eb6a299eb4bfeb8e34901bc051e7ac4"
    assert rust_delta["release_evidence"]["cargo_gitlink"] == "5f94df4789f005f9a352888e8355ffc645b7ed0e"
    assert rust_manifest["runtime_result"] == "unexecuted"

    modified = {}
    def update(index, values):
        old = original[index]
        new = dict(modified.get(index, old))
        for key, value in values.items():
            assert key in fields and key not in ("report_path", "inventory_id", "classification", "pinned_subjects_json", "runtime_coverage", "local_feasibility_or_blocker")
            new[key] = value
        modified[index] = new

    index_by_id = {r["inventory_id"]: i for i, r in enumerate(original) if r["inventory_id"].startswith("R")}
    update(index_by_id["R578"], {"source_coverage": R578_SOURCE, "source_evidence_path": R578_EVIDENCE})
    update(index_by_id["R414"], {"source_coverage": R414_SOURCE, "source_evidence_path": R414_EVIDENCE})
    first, r349, r351 = rust_delta["changes"]
    assert first["selector"] == "newer_target_exact" and first["expected_row_count"] == 55
    selected = [(i, r) for i, r in enumerate(original) if r["newer_target"] == first["old_value"]]
    assert len(selected) == 55
    assert {r["inventory_id"] for _, r in selected} == set(first["inventory_ids"])
    assert len(first["inventory_ids"]) == 55
    for i, _ in selected:
        update(i, first["set"])
    assert r349["selector"] == r351["selector"] == "inventory_id_and_report_path"
    for change in (r349, r351):
        i = index_by_id[change["inventory_id"]]
        old = original[i]
        assert old["report_path"] == change["report_path"]
        for key, value in change.items():
            if key.startswith("old_"):
                assert old[key[4:]] == value
        update(i, change["set"])
    assert len(modified) == 58
    assert set(rust_delta["unchanged_fields"]) == {"classification", "pinned_subjects_json", "runtime_coverage", "local_feasibility_or_blocker"}

    meta = source_metadata()
    package_hash_bytes = (SUPPORT / "source-package-hashes.json").read_bytes()
    package_hashes = json.loads(package_hash_bytes)
    assert set(package_hashes) == {LEAN.split("/")[1], RUST.split("/")[1]}
    for package_name, prefix, manifest_path in (
        (LEAN.split("/")[1], "lean", "support/verification-manifest.json"),
        (RUST.split("/")[1], "rust", "support/provenance.json"),
    ):
        files = package_hashes[package_name]
        for package_path, input_name in (("REPORT.md", f"{prefix}-REPORT.md"),
                                         ("REPORT.json", f"{prefix}-REPORT.json"),
                                         (manifest_path, f"{prefix}-verification-manifest.json" if prefix == "lean" else "rust-provenance.json")):
            assert files[package_path]["sha256"] == digest(load_input(input_name))
            assert files[package_path]["bytes"] == len(load_input(input_name))
    assert package_hashes[RUST.split("/")[1]]["matrix-delta.json"]["sha256"] == digest(rust_bytes)
    v90_meta = json.loads(obj(root, f"{V90}/REPORT.json"))
    additions = {
        V90.split("/")[1]: v90_meta,
        LEAN.split("/")[1]: meta[LEAN.split("/")[1]],
        RUST.split("/")[1]: meta[RUST.split("/")[1]],
    }
    def post(path, subject, target, source, evidence):
        return {"report_path": f"{path}/REPORT.md", "inventory_id": "post581",
                "classification": "published coverage audit" if path == V90 else "source-only version supplement",
                "pinned_subjects_json": json.dumps(subject["subjects"], ensure_ascii=False),
                "newer_target": target, "source_coverage": source,
                "source_evidence_path": evidence,
                "runtime_coverage": "audit only; no new runtime" if path == V90 else "source-only; no new runtime execution",
                "local_feasibility_or_blocker": "inherited counts and residuals stay frozen" if path == V90 else "runtime behavior remains untested"}
    appended = [
        post(V90, v90_meta, "as stated in report; no new frozen inventory ID", "v90 inherited audit", ""),
        post(LEAN, meta[LEAN.split("/")[1]], "Lean/Lake v4.35.0-rc3 prerelease at 470d5ce1400764999581fd26d5d72b00d990b0f4", "R414 mapped output-reference condition changed; direct cache mapping write retained", f"{LEAN}/REPORT.md"),
        post(RUST, meta[RUST.split("/")[1]], "Rust stable 1.99.0 at b940084d7eb6a299eb4bfeb8e34901bc051e7ac4", "R349 inherited default-features and R351 CI incremental-default source deltas", f"{RUST}/REPORT.md"),
    ]
    assert all(set(r) == set(fields) for r in appended)
    lines = base.splitlines(keepends=True)
    for i, row in modified.items():
        assert next(csv.reader([lines[i + 1].decode()]))[0] == row["report_path"]
        lines[i + 1] = csv_line(fields, row)
    lines.extend(csv_line(fields, r) for r in appended)
    matrix = b"".join(lines)
    final = rows(matrix)
    assert len(final) == 654 and len({r["report_path"] for r in final}) == 654
    assert final[-3:] == appended
    assert all(final[i] == modified.get(i, old) for i, old in enumerate(original))

    catalog = json.loads(obj(root, "CATALOG.json"))["reports"]
    assert len(catalog) == 652 and V90.split("/")[1] in catalog
    assert all(n not in catalog for n in meta)
    assert catalog[V90.split("/")[1]] == v90_meta
    addition = {"base_catalog_entries": 652, "next_catalog_entries": 655,
                "additions": {LEAN.split("/")[1]: meta[LEAN.split("/")[1]],
                              RUST.split("/")[1]: meta[RUST.split("/")[1]], NAME: meta[NAME]}}
    delta = {
        "schema": 2, "base_commit": BASE, "base_tree": git(root, "rev-parse", f"{BASE}^{{tree}}").decode().strip(),
        "base_matrix_path": MATRIX, "base_matrix_sha256": digest(base), "base_matrix_rows": 651,
        "next_matrix_sha256": digest(matrix), "next_matrix_rows": 654,
        "changed_existing_rows": [{"inventory_id": original[i]["inventory_id"], "report_path": original[i]["report_path"],
                                  "changed_fields": {k: {"old": original[i][k], "new": row[k]} for k in fields if original[i][k] != row[k]}}
                                 for i, row in sorted(modified.items())],
        "newly_indexed_reports": [r["report_path"] for r in appended],
        "v90_report_sha256": digest(obj(root, f"{V90}/REPORT.md")),
        "source_inputs_sha256": {p.name: digest(p.read_bytes()) for p in sorted(INPUT.iterdir()) if p.is_file()},
        "source_package_hashes_sha256": digest(package_hash_bytes),
        "frozen_inventory_path": INVENTORY, "frozen_inventory_sha256": digest(obj(root, INVENTORY)),
        "compcert_review_sha256": digest(obj(root, f"{REVIEW}/REPORT.md")),
        "compcert_observation_sha256": digest(obj(root, OBS)),
        "catalog_sha256": digest(obj(root, "CATALOG.json")),
        "base_catalog_entries": 652, "next_catalog_entries": 655,
        "catalog_additions": list(addition["additions"]),
        "catalog_addition_sha256": digest((json.dumps(addition, indent=2, ensure_ascii=False) + "\n").encode()),
        "report_md_sha256": digest((PACKAGE / "REPORT.md").read_bytes()),
        "report_json_sha256": digest((PACKAGE / "REPORT.json").read_bytes()),
    }
    return matrix, addition, delta


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--reference-root", required=True, type=Path)
    a = p.parse_args()
    matrix, addition, delta = build(a.reference_root)
    (SUPPORT / "version-coverage-matrix-20261003-v91.csv").write_bytes(matrix)
    (SUPPORT / "catalog-addition.json").write_text(json.dumps(addition, indent=2, ensure_ascii=False) + "\n")
    (SUPPORT / "delta.json").write_text(json.dumps(delta, indent=2, ensure_ascii=False) + "\n")
    print("Built 654-row integrated v91 matrix and three catalog additions")

if __name__ == "__main__":
    main()
