#!/usr/bin/env python3
"""Read-only checks for the retained I080 incremental target-layout matrix."""
import hashlib
import json
from pathlib import Path

here = Path(__file__).resolve().parent
root = here.parent
meta = json.loads((root / "REPORT.json").read_text())
data = json.loads((here / "results.json").read_text())

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

assert sha(here / "probe.py") == meta["subjects"][2]["identity"]["matrix_probe_sha256"]
pre = data["preflight"]
assert pre["charon_sha256"] == meta["subjects"][0]["identity"]["sha256"]
assert pre["cargo_sha256"] == meta["subjects"][1]["identity"]["cargo_sha256"]
assert pre["rustc_sha256"] == meta["subjects"][1]["identity"]["rustc_sha256"]
assert pre["free_disk_bytes"] > 10 * 1024**3
assert pre["free_memory_percent"] >= 30
assert pre["minimum_free_disk_bytes"] == 10 * 1024**3
assert pre["minimum_free_memory_percent"] == 30
assert pre["cell_timeout_seconds"] == 35
files = {str(p.relative_to(here / "fixture-origin")): sha(p)
         for p in (here / "fixture-origin").rglob("*") if p.is_file()}
assert files == pre["fixture_files"]

assert [(c["layout"], c["incremental"]) for c in data["cells"]] == [
    ("private", 0), ("private", 1), ("shared", 0), ("shared", 1)]
all_body_maps = []
all_raw_hashes = []
expected_artifacts = set()
root_lengths = set()
for cell in data["cells"]:
    layout, inc = cell["layout"], cell["incremental"]
    cell_name = f"{layout.ljust(7, '_')}-inc{inc}"
    roots = cell["source_root_paths"]
    assert set(roots) == {"A", "B"}
    assert all(Path(p).name in {"A", "B"} and Path(p).parent.name == cell_name
               for p in roots.values())
    assert len(roots["A"]) == len(roots["B"])
    root_lengths.add(len(roots["A"]))
    assert [p["phase"] for p in cell["phases"]] == ["cold", "warm"]
    for phase in cell["phases"]:
        assert phase["reason"] is None and phase["samples"]
        assert any(s["groups"]["A"] and s["groups"]["B"] for s in phase["samples"])
        assert min(s["headroom"]["free_memory_percent"] for s in phase["samples"]) >= 30
        assert min(s["headroom"]["free_disk_bytes"] for s in phase["samples"]) >= 10 * 1024**3
        assert phase["samples"][-1]["elapsed_seconds"] < 35
        assert set(phase["results"]) == {"A", "B"}
        lock = []
        for name, r in phase["results"].items():
            assert r["exit"] == 0
            assert r["pid"] > 0
            assert r["command"][0].endswith("/.anneal-local-tools/bin/charon")
            assert "--offline" in r["command"] and "--locked" in r["command"]
            assert r["target"].endswith("shared-target" if layout == "shared" else name + "-target")
            out = r["output"]
            assert out["crate_name"] == "warm_probe" and out["has_errors"] is False
            assert set(out["local_body_sha256"]) == {
                "warm_probe::step", "warm_probe::use_step", "warm_probe::payload_len",
                "warm_probe::generated_value", "warm_probe::SNAPSHOT_VALUE"}
            artifact = here / "artifacts" / cell_name / f"{phase['phase']}-{name}.llbc"
            expected_artifacts.add(artifact)
            assert sha(artifact) == out["sha256"]
            assert artifact.stat().st_size == out["bytes"]
            llbc = json.loads(artifact.read_text())
            assert llbc["translated"]["crate_name"] == "warm_probe"
            assert llbc["has_errors"] is False
            bodies = {}
            for decl in llbc["translated"]["fun_decls"]:
                if decl["item_meta"]["is_local"]:
                    item = "::".join(part["Ident"][0] for part in decl["item_meta"]["name"] if "Ident" in part)
                    body = json.dumps(decl["body"], sort_keys=True, separators=(",", ":")).encode()
                    bodies[item] = hashlib.sha256(body).hexdigest()
            assert bodies == out["local_body_sha256"]
            all_body_maps.append(bodies)
            all_raw_hashes.append(out["sha256"])
            lock.append("Blocking waiting for file lock on build directory" in r["stderr"])
            assert phase["targets"][name]["incremental_files"] == 0 if inc == 0 else phase["targets"][name]["incremental_files"] > 0
        assert any(lock) if layout == "shared" else not any(lock)
    assert cell["final_targets"] == cell["phases"][-1]["targets"]
    if layout == "shared":
        assert cell["final_targets"]["A"] == cell["final_targets"]["B"]

assert len(expected_artifacts) == 16
assert len(root_lengths) == 1
assert set((here / "artifacts").rglob("*.llbc")) == expected_artifacts
assert len({tuple(sorted(x.items())) for x in all_body_maps}) == 1
assert len(set(all_raw_hashes)) == 16
assert data["cleanup"]["work_exists_after_removal"] is False
assert len(data["cleanup"]["process_groups"]) == 16
assert all(not group["members"] for group in data["cleanup"]["process_groups"].values())
assert data["cleanup"]["headroom_after"]["free_memory_percent"] >= 30
assert data["cleanup"]["headroom_after"]["free_disk_bytes"] >= 10 * 1024**3
print("PASS: four cold/warm cells, 16 LLBCs, selected bodies, locks, target state, guards and cleanup")
