#!/usr/bin/env python3
"""Validate the retained R37 component observations without rerunning tools."""
import hashlib
import json
from pathlib import Path

here = Path(__file__).resolve().parent
work = here / "work"
r = json.loads((here / "results.json").read_text())
assert r["schema"] == 1 and r["skipped"] == []
expected = {f"o{o}-i{i}" for o in (1, 2, 4) for i in (1, 2)}
assert set(r["results"]["cargo"]) == expected
assert set(r["results"]["lean"]) == expected
assert r["host"]["mem_bytes"] == 8 * 1024**3
assert r["limits"] == {
    "rss_cap_kib": 4_000_000,
    "process_cap": 32,
    "cell_seconds": 40,
    "free_floor_percent": 25,
}
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
for path, digest in r["tools"].items():
    assert sha(path) == digest

admissions = [e for e in r["events"] if e["event_type"] == "admission"]
assert len(admissions) == 12 and all(e["allowed"] for e in admissions)
assert all(e["pressure"]["free_percent"] >= 25 for e in admissions)

for key, cell in r["results"]["cargo"].items():
    outer, inner = int(key[1]), int(key[4])
    assert (cell["outer"], cell["inner"]) == (outer, inner)
    assert len(cell["root_paths"]) == outer
    assert cell["noop_unchanged_output"] == [False] * outer
    assert cell["incremental_changed_output"] == [True] * outer
    for phase in ("cold", "warm_noop", "warm_incremental"):
        group = cell[phase]
        assert not group["aborted"] and group["elapsed_ms"] > 0
        assert group["elapsed_ms"] < 40_000
        assert group["max_process_count"] <= 32
        assert group["peak_rss_tree"]["rss_kib"] <= 4_000_000
        assert group["cleanup_tree"]["count"] == 0
        assert len(group["results"]) == outer
        for item in group["results"]:
            assert item["rc"] == 0 and item["llbc_exists"]
            assert len(item["llbc_sha256"]) == 64
            assert "Finished `dev` profile" in item["stderr"]
    for i, root in enumerate(cell["root_paths"]):
        folder = Path(root)
        assert folder.is_relative_to(work)
        assert (folder / "Cargo.toml").is_file()
        assert (folder / "src/lib.rs").is_file()
        assert (folder / "build.rs").is_file()
        for phase in ("cold", "warm-noop", "warm-incremental"):
            assert (folder / f"{phase}.stderr").is_file()
        digest = cell["warm_incremental"]["results"][i]["llbc_sha256"]
        assert sha(folder / "probe.llbc") == digest
    assert all(a["llbc_sha256"] != b["llbc_sha256"]
               for a, b in zip(cell["cold"]["results"], cell["warm_noop"]["results"]))

cleanups = [e for e in r["events"] if e["event_type"] == "lean_cleanup"]
assert len(cleanups) == 6
assert all(e["tree"]["count"] == 0 for e in cleanups)
for key, cell in r["results"]["lean"].items():
    outer, inner = int(key[1]), int(key[4])
    assert (cell["outer"], cell["inner"], cell["configured_LEAN_NUM_THREADS"]) == (outer, inner, inner)
    assert len(cell["startup"]) == len(cell["cold"]) == len(cell["warm"]) == outer
    assert cell["stable_tree"]["count"] == 2 * outer
    assert cell["stable_tree"]["rss_kib"] < 4_000_000
    assert len(cell["resource_sample"]["thread_counts"]) == 2 * outer
    assert all(x["phys_footprint_bytes"] is not None
               for x in cell["resource_sample"]["footprints"])
    for row in cell["cold"] + cell["warm"]:
        assert row["wait_ms"] > 0 and row["goal_ms"] > 0
        assert row["goal"]["result"]["goals"] == ["n : Nat\n⊢ n = n"]
    for pid in cell["server_pids"]:
        assert any(p["pid"] == pid for p in cell["stable_tree"]["processes"])
        assert any(p["ppid"] == pid for p in cell["stable_tree"]["processes"])
    assert cell["memory_pressure"]["free_percent"] >= 25

print("R37 retained-result checks passed: 12 cells; no skips; all process trees cleaned")
