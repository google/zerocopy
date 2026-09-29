#!/usr/bin/env python3
"""Read-only validation of the retained I080 edit/revert observation."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
META = json.loads((HERE.parent / "REPORT.json").read_text())
DATA = json.loads((HERE / "results.json").read_text())

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

assert sha(HERE / "probe.py") == META["subjects"][2]["identity"]["probe_sha256"]
pre = DATA["preflight"]
assert pre["charon_sha256"] == META["subjects"][0]["identity"]["sha256"]
assert pre["cargo_sha256"] == META["subjects"][1]["identity"]["cargo_sha256"]
assert pre["rustc_sha256"] == META["subjects"][1]["identity"]["rustc_sha256"]
assert pre["min_free_disk_bytes"] == 10 * 1024**3
assert pre["min_free_memory_percent"] == 30
assert pre["command_timeout_seconds"] == 30
assert pre["free_disk_bytes"] >= pre["min_free_disk_bytes"]
assert pre["free_memory_percent"] >= pre["min_free_memory_percent"]
fixture = {str(p.relative_to(HERE / "fixture-origin")): sha(p)
           for p in (HERE / "fixture-origin").rglob("*") if p.is_file()}
assert fixture == pre["fixture_files"]
source = (HERE / "fixture-origin/app/src/lib.rs").read_bytes()
assert source.count(b"x.wrapping_add(1)") == 1
baseline_sha = hashlib.sha256(source).hexdigest()
edited_sha = hashlib.sha256(source.replace(b"x.wrapping_add(1)",
                                            b"x.wrapping_add(2)")).hexdigest()
assert baseline_sha != edited_sha

expected_files = set()
assert [c["incremental"] for c in DATA["cells"]] == [0, 1]

def verify_run(run, label, root, target, inc, source_sha):
    assert run["label"] == label
    assert run["root"] == root and run["target"] == target
    assert run["source_sha256"] == source_sha
    assert run["exit"] == 0 and run["reason"] is None
    assert 0 < run["elapsed_seconds"] < 30
    assert run["headroom_samples"]
    assert all(s["free_disk_bytes"] >= 10 * 1024**3 and
               s["free_memory_percent"] >= 30 for s in run["headroom_samples"])
    assert run["command"][0].endswith("/.anneal-local-tools/bin/charon")
    assert run["command"][1:4] == ["cargo", "--preset", "aeneas"]
    assert run["command"][-3:] == ["--lib", "--offline", "--locked"]
    assert "--manifest-path" in run["command"]
    assert run["command"][run["command"].index("--manifest-path") + 1] == root + "/Cargo.toml"
    assert run["environment"]["CARGO_INCREMENTAL"] == str(inc)
    assert run["environment"]["CARGO_TARGET_DIR"] == target
    assert run["environment"]["CARGO_BUILD_JOBS"] == "1"
    assert run["environment"]["RAYON_NUM_THREADS"] == "1"
    assert run["environment"]["CARGO_NET_OFFLINE"] == "true"
    assert run["environment"]["BUILD_VALUE"] == "7"
    assert "Compiling warm_probe" in run["stderr"]
    stats = run["target_stats"]
    assert stats["files"] > 0 and stats["allocated_kib"] > 0
    assert stats["incremental_files"] > 0 if inc else stats["incremental_files"] == 0
    assert stats["incremental_bytes"] > 0 if inc else stats["incremental_bytes"] == 0
    dest = HERE / "artifacts" / f"{label}.llbc"
    expected_files.add(dest)
    recorded_dest = Path(run["command"][run["command"].index("--dest-file") + 1])
    suffix = Path("reports") / HERE.parent.name / "support" / "artifacts" / f"{label}.llbc"
    assert recorded_dest.is_absolute()
    assert recorded_dest.parts[-len(suffix.parts):] == suffix.parts
    assert dest.stat().st_size == run["output"]["bytes"]
    assert sha(dest) == run["output"]["sha256"]
    d = json.loads(dest.read_text())
    assert d["translated"]["crate_name"] == run["output"]["crate_name"] == "warm_probe"
    assert d["has_errors"] is run["output"]["has_errors"] is False
    bodies = {}
    for decl in d["translated"]["fun_decls"]:
        meta = decl["item_meta"]
        if meta["is_local"]:
            name = "::".join(part["Ident"][0] for part in meta["name"] if "Ident" in part)
            body = json.dumps(decl["body"], sort_keys=True, separators=(",", ":")).encode()
            bodies[name] = hashlib.sha256(body).hexdigest()
    assert bodies == run["output"]["local_body_sha256"]
    assert set(bodies) == {"warm_probe::step", "warm_probe::use_step",
                           "warm_probe::payload_len", "warm_probe::generated_value",
                           "warm_probe::SNAPSHOT_VALUE"}
    return bodies, stats

for cell in DATA["cells"]:
    inc = cell["incremental"]
    roots = cell["roots"]
    assert set(roots) == {"A", "B"}
    assert roots["A"].endswith(f"/inc{inc}/A")
    assert roots["B"].endswith(f"/inc{inc}/B")
    assert len(roots["A"]) == len(roots["B"])
    assert cell["baseline_sha256"] == baseline_sha
    assert cell["edited_sha256"] == edited_sha
    assert cell["shared_target"].endswith(f"/inc{inc}/shared-target")
    oracle_maps = {}
    for state, source_sha in (("baseline", baseline_sha), ("edited", edited_sha)):
        label = f"inc{inc}-oracle-{state}"
        oracle_maps[state], _ = verify_run(cell["oracle"][state], label, roots["A"],
            str(Path(roots["A"]).parent / "oracle-target"), inc, source_sha)
    assert [k for k in oracle_maps["baseline"]
            if oracle_maps["baseline"][k] != oracle_maps["edited"][k]] == ["warm_probe::step"]
    assert [p["name"] for p in cell["phases"]] == ["baseline", "edited", "reverted"]
    incremental_counts = []
    for phase in cell["phases"]:
        state = phase["name"]
        assert phase["source_hashes"] == {
            "A": edited_sha if state == "edited" else baseline_sha,
            "B": baseline_sha}
        assert set(phase["runs"]) == {"A", "B"}
        for name, run in phase["runs"].items():
            label = f"inc{inc}-{state}-{name}"
            bodies, stats = verify_run(run, label, roots[name], cell["shared_target"], inc,
                phase["source_hashes"][name])
            expected = oracle_maps["edited" if name == "A" and state == "edited" else "baseline"]
            assert bodies == expected
            incremental_counts.append(stats["incremental_files"])
    if inc:
        assert incremental_counts == sorted(incremental_counts)
        assert incremental_counts[-1] > incremental_counts[0]
    else:
        assert set(incremental_counts) == {0}

assert len(expected_files) == 16
assert set((HERE / "artifacts").glob("*.llbc")) == expected_files
assert DATA["cleanup"]["work_exists_after_removal"] is False
assert DATA["cleanup"]["headroom_after"]["free_disk_bytes"] >= 10 * 1024**3
assert DATA["cleanup"]["headroom_after"]["free_memory_percent"] >= 30
print("PASS: 16 pinned LLBCs, source A/B/A identity, cold oracles, incremental state, guards and cleanup")
