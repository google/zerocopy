#!/usr/bin/env python3
"""Read-only validation of the retained incremental-on cancellation observation."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PACKAGE = "anneal-3731-i080-incremental-on-shared-target-cancel-recovery-2026-09-29"
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
assert pre["max_group_rss_kib"] == 1024 * 1024
assert pre["max_private_work_kib"] == 100 * 1024
assert pre["serial_timeout_seconds"] == 15 and pre["pair_timeout_seconds"] == 20
assert pre["free_disk_bytes"] >= pre["min_free_disk_bytes"]
assert pre["free_memory_percent"] >= pre["min_free_memory_percent"]
fixture = {str(p.relative_to(HERE / "fixture-origin")): sha(p)
           for p in (HERE / "fixture-origin").rglob("*") if p.is_file()}
assert fixture == pre["fixture_files"]
source = (HERE / "fixture-origin/app/src/lib.rs").read_bytes()
build = (HERE / "fixture-origin/app/build.rs").read_text()
assert source.count(b"x.wrapping_add(1)") == 1
assert build.count("fn main() {") == 1
assert DATA["edit"]["baseline_sha256"] == hashlib.sha256(source).hexdigest()
assert DATA["edit"]["edited_sha256"] == hashlib.sha256(source.replace(
    b"x.wrapping_add(1)", b"x.wrapping_add(2)")).hexdigest()
assert DATA["edit"]["original_build_sha256"] == hashlib.sha256(build.encode()).hexdigest()
instrumented = build.replace("fn main() {", (
    'fn main() {\n  std::fs::write('
    'std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(".build-entered"), '
    'b"entered").unwrap();\n  '
    'std::thread::sleep(std::time::Duration::from_secs(3));'))
assert DATA["edit"]["instrumented_build_sha256"] == hashlib.sha256(instrumented.encode()).hexdigest()

roots = DATA["roots"]
assert set(roots) == {"A", "B"}
assert roots["A"].endswith("/work/A") and roots["B"].endswith("/work/B")
assert len(roots["A"]) == len(roots["B"])
assert DATA["shared_target"] == str(Path(roots["A"]).parent / "shared-target")
assert DATA["edit"]["marker"] == roots["A"] + "/app/.build-entered"
phases = DATA["phases"]
assert set(phases) == {"prewarm_A", "prewarm_B", "cancel_pair", "recovery_A",
                       "oracle_edited_A", "oracle_baseline_B"}
expected_artifacts = set()

def verify_run(run, label, root, target, source_sha, build_sha, expected_exit):
    assert run["label"] == label and run["pid"] > 0
    assert run["root"] == root and run["target"] == target
    assert run["source_sha256"] == source_sha
    assert run["build_script_sha256"] == build_sha
    assert run["exit"] == expected_exit
    cmd = run["command"]
    assert cmd[0].endswith("/.anneal-local-tools/bin/charon")
    assert cmd[1:4] == ["cargo", "--preset", "aeneas"]
    assert cmd[-3:] == ["--lib", "--offline", "--locked"]
    assert cmd[cmd.index("--manifest-path") + 1] == root + "/Cargo.toml"
    recorded_dest = Path(cmd[cmd.index("--dest-file") + 1])
    suffix = Path("reports") / PACKAGE / "support" / "artifacts" / f"{label}.llbc"
    assert recorded_dest.is_absolute()
    assert recorded_dest.parts[-len(suffix.parts):] == suffix.parts
    dest = HERE / "artifacts" / f"{label}.llbc"
    if expected_exit != 0:
        assert run["output"] is None and not dest.exists()
        return None
    expected_artifacts.add(dest)
    out = run["output"]
    assert out and dest.stat().st_size == out["bytes"] and sha(dest) == out["sha256"]
    d = json.loads(dest.read_text())
    assert d["translated"]["crate_name"] == out["crate_name"] == "warm_probe"
    assert d["has_errors"] is out["has_errors"] is False
    bodies = {}
    for decl in d["translated"]["fun_decls"]:
        if decl["item_meta"]["is_local"]:
            name = "::".join(part["Ident"][0] for part in decl["item_meta"]["name"]
                             if "Ident" in part)
            body = json.dumps(decl["body"], sort_keys=True, separators=(",", ":")).encode()
            bodies[name] = hashlib.sha256(body).hexdigest()
    assert bodies == out["local_body_sha256"]
    assert set(bodies) == {"warm_probe::step", "warm_probe::use_step",
                           "warm_probe::payload_len", "warm_probe::generated_value",
                           "warm_probe::SNAPSHOT_VALUE"}
    return bodies

def verify_samples(phase, timeout):
    assert phase["reason"] is None and phase["samples"]
    assert phase["samples"][-1]["elapsed_seconds"] < timeout
    for s in phase["samples"]:
        assert s["free_disk_bytes"] >= 10 * 1024**3
        assert s["free_memory_percent"] >= 30
        assert s["work_allocated_kib"] <= 100 * 1024
        assert all(v <= 1024 * 1024 for v in s["group_rss_sum_kib"].values())
    assert phase["target_after"]["incremental_files"] > 0
    assert phase["target_after"]["incremental_bytes"] > 0

shared = DATA["shared_target"]
baseline = DATA["edit"]["baseline_sha256"]
edited = DATA["edit"]["edited_sha256"]
original_build = DATA["edit"]["original_build_sha256"]
new_build = DATA["edit"]["instrumented_build_sha256"]
mapping = {
    "prewarm_A": ("prewarm-A", roots["A"], shared, baseline, original_build),
    "prewarm_B": ("prewarm-B", roots["B"], shared, baseline, original_build),
    "recovery_A": ("recovery-A", roots["A"], shared, edited, new_build),
    "oracle_edited_A": ("oracle-edited-A", roots["A"],
                        str(Path(shared).parent / "oracle-edited-target"), edited, new_build),
    "oracle_baseline_B": ("oracle-baseline-B", roots["B"],
                          str(Path(shared).parent / "oracle-baseline-target"), baseline, original_build),
}
maps = {}
for phase_name, (label, root, target, source_sha, build_sha) in mapping.items():
    phase = phases[phase_name]
    verify_samples(phase, 15)
    maps[phase_name] = verify_run(phase["run"], label, root, target,
                                  source_sha, build_sha, 0)
    assert "Compiling warm_probe" in phase["run"]["stderr"]
pair = phases["cancel_pair"]
verify_samples(pair, 20)
ev = pair["events"]
assert 0 < ev["marker_seen_seconds"] <= ev["companion_started_seconds"]
assert ev["companion_started_seconds"] < ev["signal_seconds"]
assert ev["signal_seconds"] <= ev["owner_exit_seconds"] < ev["companion_exit_seconds"] < 20
assert ev["both_live_before_cancel"] is True
assert ev["companion_live_after_owner_exit"] is True
assert any(s["groups"].get("A") and s["groups"].get("B") for s in pair["samples"])
assert set(pair["runs"]) == {"A", "B"}
verify_run(pair["runs"]["A"], "cancel-A", roots["A"], shared, edited, new_build, -15)
maps["companion_B"] = verify_run(pair["runs"]["B"], "companion-B", roots["B"],
                                  shared, baseline, original_build, 0)
assert "Blocking waiting for file lock on build directory" in pair["runs"]["B"]["stderr"]
assert maps["prewarm_A"] == maps["prewarm_B"] == maps["oracle_baseline_B"]
assert maps["companion_B"] == maps["oracle_baseline_B"]
assert maps["recovery_A"] == maps["oracle_edited_A"]
assert [n for n in maps["oracle_edited_A"]
        if maps["oracle_edited_A"][n] != maps["oracle_baseline_B"][n]] == ["warm_probe::step"]
assert phases["prewarm_A"]["target_after"]["incremental_files"] > 0
assert phases["prewarm_B"]["target_after"]["incremental_files"] > 0
assert pair["target_after"]["incremental_files"] > 0
assert phases["recovery_A"]["target_after"] == DATA["final_shared_target"]
assert set((HERE / "artifacts").glob("*.llbc")) == expected_artifacts
assert len(expected_artifacts) == 6
assert set(DATA["postrun_groups"]) == {"prewarm-A", "prewarm-B", "cancel-A",
                                        "companion-B", "recovery-A", "oracle-edited-A",
                                        "oracle-baseline-B"}
assert all(not members for members in DATA["postrun_groups"].values())
assert DATA["cleanup"]["work_exists_after_removal"] is False
assert DATA["cleanup"]["free_disk_bytes"] >= 10 * 1024**3
assert DATA["cleanup"]["free_memory_percent"] >= 30
print("PASS: warm incremental target, marked cancellation, live companion, cold-oracle retry, guards and cleanup")
