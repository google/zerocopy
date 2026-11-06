#!/usr/bin/env python3
"""Check retained I020 slug/Charon evidence without executing external tools."""

import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def u32_scalars(node):
    if isinstance(node, dict):
        if "Unsigned" in node and node["Unsigned"][0] == "U32":
            yield node["Unsigned"][1]
        for value in node.values():
            yield from u32_scalars(value)
    elif isinstance(node, list):
        for value in node:
            yield from u32_scalars(value)


def main():
    hashes = json.loads((HERE / "artifacts.sha256.json").read_text())
    for relative, expected in hashes.items():
        path = HERE / relative
        assert path.is_file(), relative
        assert sha(path) == expected, relative
    data = json.loads((HERE / "results.json").read_text())
    assert data["source_scanner_sha256"] == sha(HERE / "harness/src/scanner.rs")
    assert data["fixture_source_sha256"] == sha(HERE / "fixture/src/lib.rs")
    assert data["fixture_manifest_sha256"] == sha(HERE / "fixture/Cargo.toml")
    assert data["fixture_lock_sha256"] == sha(HERE / "fixture/Cargo.lock")
    assert data["harness_lock_sha256"] == sha(HERE / "harness/Cargo.lock")
    rows = data["slug_rows"]
    assert [row[0] for row in rows] == ["default", "selected"]
    assert rows[0][1:] == rows[1][1:]
    assert rows[0][2] == rows[0][1] + ".llbc"
    for key in ("harness_lock", "fixture_lock", "harness_build", "slug", "charon_default", "charon_selected"):
        assert data["commands"][key]["exit_code"] == 0, key
    default = data["commands"]["charon_default"]["argv"]
    selected = data["commands"]["charon_selected"]["argv"]
    assert "--lib" in default and "--lib" in selected
    assert "--features" not in default
    assert selected[selected.index("--features") + 1] == "selected"
    assert data["llbc_sha256"]["default"] == sha(HERE / "artifacts/default.llbc")
    assert data["llbc_sha256"]["selected"] == sha(HERE / "artifacts/selected.llbc")
    assert data["llbc_sha256"]["default"] != data["llbc_sha256"]["selected"]
    fixture_source = (HERE / "fixture/src/lib.rs").read_text()
    for label, expected in (("default", "7"), ("selected", "11")):
        source = json.loads((HERE / "artifacts" / f"{label}.llbc").read_text())
        assert source["has_errors"] is False
        assert source["translated"]["files"][0]["contents"] == fixture_source
        assert data["projections"][label]["local_bodies"][0]["u32_scalar_literals"] == [expected]
        assert list(u32_scalars(source["translated"]["fun_decls"][0]["body"])) == [expected]
    assert data["projections"]["default"]["local_function_names"] == data["projections"]["selected"]["local_function_names"]
    print(f"checked {len(hashes)} evidence files; one slug, distinct 7/11 LLBC bodies")


if __name__ == "__main__":
    main()
