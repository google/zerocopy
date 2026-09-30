#!/usr/bin/env python3
"""Offline integrity and scope check for the 41-package source synthesis."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REPORTS = ROOT / "reports"
EXPECTED_NONE = {"I057", "I059", "I061", "I062"}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    census = json.loads((HERE / "source-census.json").read_text())
    mapping = json.loads((HERE / "id-map.json").read_text())
    meta = json.loads((HERE.parent / "REPORT.json").read_text())
    assert len(census) == 41 and len({x["package"] for x in census}) == 41
    assert len(mapping) == 23 and {x for x,y in mapping.items() if not y} == EXPECTED_NONE
    assert set(mapping) <= {f"I{i:03d}" for i in range(1,160)}
    assert meta["subjects"][0]["identity"]["source_census_sha256"] == sha(HERE / "source-census.json")
    assert meta["subjects"][1]["identity"]["id_map_sha256"] == sha(HERE / "id-map.json")
    assert meta["subjects"][1]["identity"]["reference_parent"] == "ebcdcadb63fefd1e6c0f46cb2030270ae3232837"
    names = {x["package"] for x in census}
    for item, packages in mapping.items():
        assert len(packages) == len(set(packages)) and set(packages) <= names, item
    for record in census:
        folder = REPORTS / record["package"]
        assert sha(folder / "REPORT.md") == record["report_sha256"]
        assert record["mapped_ids"] == sorted(item for item, packages in mapping.items() if record["package"] in packages)
        found = sorted(path.relative_to(ROOT).as_posix() for path in folder.rglob("*") if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc")
        assert found == [x["path"] for x in record["files"]], record["package"]
        for entry in record["files"]:
            p = ROOT / entry["path"]
            assert sha(p) == entry["sha256"] and p.stat().st_size == entry["size"], entry["path"]
    body = (HERE.parent / "REPORT.md").read_text()
    for item in mapping:
        assert f"| {item} |" in body
    assert "0c504d98f5abafcbbd1460738e6d753378a6460e" in body
    assert "result: null" in body and "missing quiescence" in body
    print("PASS: 41 source packages, 23 bounded IDs and published-parent clarification")

if __name__ == "__main__":
    main()
