#!/usr/bin/env python3
"""Offline Cargo/Charon source-subject identity matrix with stable source path."""

import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
FIX = HERE / "fixture"
VERSIONS = HERE / "versions"
ART = HERE / "artifacts"
RAW = HERE / "raw-results.json"
MAPPING = HERE / "mapping-manifest.json"
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
RUST_BIN = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"
CHARON = TOOLS / "bin/charon"
CARGO = RUST_BIN / "cargo"
RUSTC = RUST_BIN / "rustc"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def item_name(parts):
    result = []
    for part in parts:
        if "Ident" in part:
            result.append(part["Ident"][0])
        elif "Impl" in part:
            result.append("<impl>" + json.dumps(part["Impl"], sort_keys=True))
        else:
            result.append("<" + next(iter(part)) + ">")
    return "::".join(result)


def projection(path):
    data = json.loads(path.read_text())
    crate = data["translated"]
    files = [{"id": f["id"], "name": f["name"], "crate_name": f["crate_name"],
              "contents_sha256": hashlib.sha256(f["contents"].encode()).hexdigest() if f.get("contents") is not None else None}
             for f in crate["files"]]
    functions = []
    for entry in crate["fun_decls"]:
        if entry is None:
            continue
        meta = entry.get("item_meta") or {}
        if not meta.get("is_local"):
            continue
        attrs = meta.get("attr_info", {}).get("attributes", [])
        markers = [a["DocComment"].strip() for a in attrs
                   if isinstance(a, dict) and "DocComment" in a and "proof-id:" in a["DocComment"]]
        functions.append({"id": entry["def_id"], "name": item_name(meta["name"]),
                          "short_name": next((x["Ident"][0] for x in reversed(meta["name"]) if "Ident" in x), None),
                          "structured_name": meta["name"], "span": meta.get("span"),
                          "source_text": meta.get("source_text"), "markers": markers,
                          "all_attributes": attrs, "local": meta.get("is_local")})
    return {"llbc_sha256": sha(path), "has_errors": data["has_errors"],
            "crate_name": crate["crate_name"], "files": files, "functions": functions,
            "ordered_decls": crate.get("ordered_decls")}


def by_name(proj, name):
    return [f for f in proj["functions"] if f["name"] == name]


def by_marker(proj, marker):
    return [f for f in proj["functions"] if marker in f["markers"]]


def ids(items):
    return [{"id": f["id"], "name": f["name"], "span": f["span"]} for f in items]


def main():
    if ART.exists():
        shutil.rmtree(ART)
    ART.mkdir()
    source_path = FIX / "src/lib.rs"
    env = dict(os.environ)
    env.update({"RUSTUP_HOME": str(TOOLS / "rustup"), "CARGO_HOME": str(TOOLS / "cargo"),
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1",
                "PATH": os.pathsep.join([str(RUST_BIN), str(TOOLS / "bin"), env.get("PATH", "")])})
    cases = [("A-default-lib", "A.rs", ["--lib"]),
             ("A-selected-lib", "A.rs", ["--lib", "--features", "selected"]),
             ("A-default-tests", "A.rs", ["--tests"]),
             ("B-moved-default-lib", "B-moved.rs", ["--lib"]),
             ("C-duplicated-default-lib", "C-duplicated.rs", ["--lib"]),
             ("A-restored-default-lib", "A.rs", ["--lib"])]
    records = []
    try:
        for label, variant, cargo_flags in cases:
            source_path.write_bytes((VERSIONS / variant).read_bytes())
            target = ART / ("target-" + label)
            output = ART / (label + ".llbc")
            command = [str(CHARON), "cargo", "--preset", "aeneas", "--dest-file", str(output),
                       "--", "--manifest-path", str(FIX / "Cargo.toml"), *cargo_flags,
                       "--offline", "--locked"]
            run_env = dict(env, CARGO_TARGET_DIR=str(target))
            result = subprocess.run(command, cwd=FIX, env=run_env, capture_output=True,
                                    text=True, timeout=45)
            proj = projection(output) if output.exists() else None
            records.append({"label": label, "variant": variant, "source_path": str(source_path),
                            "source_sha256": sha(source_path), "manifest_sha256": sha(FIX / "Cargo.toml"),
                            "lock_sha256": sha(FIX / "Cargo.lock"), "cargo_flags": cargo_flags,
                            "command": command, "cwd": str(FIX), "env": {
                                "RUSTUP_HOME": run_env["RUSTUP_HOME"], "CARGO_HOME": run_env["CARGO_HOME"],
                                "CARGO_TARGET_DIR": run_env["CARGO_TARGET_DIR"],
                                "CHARON_TOOLCHAIN_IS_IN_PATH": "1", "PATH_prefix": [str(RUST_BIN), str(TOOLS / "bin")]},
                            "exit_code": result.returncode, "stdout": result.stdout,
                            "stderr": result.stderr, "output_exists": output.exists(),
                            "projection": proj})
            if target.exists():
                shutil.rmtree(target)
    finally:
        source_path.write_bytes((VERSIONS / "A.rs").read_bytes())

    assert all(r["exit_code"] == 0 and r["projection"] and not r["projection"]["has_errors"]
               for r in records), records
    d = {r["label"]: r["projection"] for r in records}
    a, selected, tests, moved, duplicated, restored = (d[x] for x in
        ("A-default-lib", "A-selected-lib", "A-default-tests", "B-moved-default-lib",
         "C-duplicated-default-lib", "A-restored-default-lib"))
    crate = "subject_identity_probe::"
    assert len(by_name(a, crate + "default_only")) == 1
    assert not by_name(a, crate + "selected_only")
    assert len(by_name(selected, crate + "selected_only")) == 1
    assert not by_name(selected, crate + "default_only")
    assert len(by_marker(selected, "proof-id: conditional")) == 1
    assert not by_marker(a, "proof-id: conditional")
    assert not by_name(a, crate + "tests::test_subject")
    assert len(by_name(tests, crate + "tests::test_subject")) == 1
    assert len([f for f in a["functions"] if f["short_name"] == "duplicate"]) == 2
    assert len(by_marker(a, "proof-id: trait-default")) == 2
    assert len(by_marker(a, "proof-id: movable")) == 1
    assert len(by_marker(moved, "proof-id: movable")) == 1
    assert len(by_marker(duplicated, "proof-id: movable")) == 2
    assert len(by_marker(restored, "proof-id: movable")) == 1
    assert records[0]["source_sha256"] == records[-1]["source_sha256"]
    assert {k: v for k, v in a.items() if k != "llbc_sha256"} == {
        k: v for k, v in restored.items() if k != "llbc_sha256"}

    named = {label: {f["name"]: f for f in proj["functions"]} for label, proj in d.items()}
    mapping = {"evidence_levels": {
        "serialized_compiler_derived": "Within one LLBC, Charon's typed ID, structured name, attribute, file table, and source span are serialized results of the selected rustc subject; IDs are not proven stable across runs.",
        "lexical_candidate": "Matching authored proof-id doc-comment text or display names across LLBCs is a comparison heuristic, not an authenticated cross-run attachment."},
        "subjects": [{"label": r["label"], "variant": r["variant"], "cargo_flags": r["cargo_flags"],
                      "source_sha256": r["source_sha256"], "llbc_sha256": r["projection"]["llbc_sha256"],
                      "local_function_count": len(r["projection"]["functions"])} for r in records],
        "missing_subject_controls": {
            "default_lib_selected_only": ids(by_name(a, crate + "selected_only")),
            "selected_lib_default_only": ids(by_name(selected, crate + "default_only")),
            "default_lib_test_subject": ids(by_name(a, crate + "tests::test_subject")),
            "selected_lib_conditional_marker": ids(by_marker(selected, "proof-id: conditional"))},
        "ambiguous_locator_controls": {
            "short_name_duplicate_in_distinct_modules": ids([f for f in a["functions"] if f["short_name"] == "duplicate"]),
            "trait_default_marker_on_trait_and_impl_items": ids(by_marker(a, "proof-id: trait-default")),
            "duplicated_movable_marker": ids(by_marker(duplicated, "proof-id: movable"))},
        "macro_generated": ids(by_marker(a, "proof-id: macro-generated")),
        "structural_revisions": {
            "A": ids(by_marker(a, "proof-id: movable")),
            "B_moved": ids(by_marker(moved, "proof-id: movable")),
            "C_duplicated": ids(by_marker(duplicated, "proof-id: movable")),
            "A_restored": ids(by_marker(restored, "proof-id: movable")),
            "A_restored_source_bytes_equal": records[0]["source_sha256"] == records[-1]["source_sha256"],
            "A_restored_projection_equal_excluding_raw_sha": True,
            "A_restored_movable_id_equal": by_marker(a, "proof-id: movable")[0]["id"] == by_marker(restored, "proof-id: movable")[0]["id"]},
        "cross_run_candidate_comparison": [
            {"path": name, "A_id": named["A-default-lib"].get(name, {}).get("id"),
             "B_moved_id": named["B-moved-default-lib"].get(name, {}).get("id"),
             "A_span": named["A-default-lib"].get(name, {}).get("span"),
             "B_moved_span": named["B-moved-default-lib"].get(name, {}).get("span"),
             "edge_kind": "lexical structured-path comparison across separate LLBCs"}
            for name in sorted(set(named["A-default-lib"]) & set(named["B-moved-default-lib"]))]}

    result = {"environment": {"platform": platform.platform(), "python": sys.version,
                              "charon_sha256": sha(CHARON), "cargo_sha256": sha(CARGO),
                              "rustc_sha256": sha(RUSTC), "script_sha256": sha(__file__),
                              "variant_hashes": {p.name: sha(p) for p in sorted(VERSIONS.glob("*.rs"))}},
              "runs": records}
    RAW.write_text(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    MAPPING.write_text(json.dumps(mapping, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"runs": [(r["label"], r["exit_code"], len(r["projection"]["functions"])) for r in records],
                      "missing": {k: len(v) for k, v in mapping["missing_subject_controls"].items()},
                      "ambiguous": {k: len(v) for k, v in mapping["ambiguous_locator_controls"].items()},
                      "movable_ids": [by_marker(p, "proof-id: movable")[0]["id"] for p in (a,moved,restored)]},
                     sort_keys=True))


if __name__ == "__main__":
    main()
