#!/usr/bin/env python3
"""Read-only offline checker for the retained I148 same-path Lake replay."""
import gzip
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PRIOR = REPO / "reports/anneal-3731-i148-multifunction-translation-repeat-2026-09-29"
RESULT = json.loads((HERE / "results.json").read_text())
MODULES = ("Probe.Types", "Probe.Funs", "Probe", "Consumer")
SOURCES = {"Types.lean": "Probe/Types.lean", "Funs.lean": "Probe/Funs.lean", "Probe.lean": "Probe.lean"}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def file_sha(path):
    return sha(Path(path).read_bytes())

def log_bytes(label, stream):
    raw = HERE / "logs" / f"{label}.{stream}"
    compressed = HERE / "logs" / f"{label}.{stream}.gz"
    assert raw.is_file() != compressed.is_file(), (raw, compressed)
    return raw.read_bytes() if raw.is_file() else gzip.decompress(compressed.read_bytes())

def artifact(state, module, ext):
    return state[f".lake/build/lib/lean/{module.replace('.', '/')}.{ext}"]

def status_lines(build, expected):
    lines = build["own_job_lines"]
    assert len(lines) == 4, (build["label"], lines)
    for module, action in expected.items():
        assert sum(bool(re.search(rf"\b{action} {re.escape(module)}(?:\s|$)", line)) for line in lines) == 1, (build["label"], module, lines)

def main():
    d = RESULT
    assert d["schema"] == 1 and d["status"] == "complete"
    assert d["identity"]["parent_commit"] == "3b549cb1eddebc54896a106c5c94ede6c2c134e5"
    assert d["identity"]["prior_report_sha256"] == file_sha(PRIOR / "REPORT.md")
    assert d["identity"]["prior_results_sha256"] == file_sha(PRIOR / "support/results.json")
    for n in range(1, 6):
        for name in SOURCES:
            assert d["identity"]["prior_generated"][f"gen-{n}"][name] == file_sha(PRIOR / "support/artifacts" / f"gen-{n}" / name)
    assert all(len({d["identity"]["prior_generated"][f"gen-{n}"][name] for n in range(1, 6)}) == 1 for name in SOURCES)
    for n in range(1, 4):
        assert d["identity"]["prior_llbc"][f"seq-{n}"] == file_sha(PRIOR / "support/artifacts" / f"seq-{n}.llbc")
    assert len({d["identity"]["prior_llbc"][f"seq-{n}"] for n in range(1, 4)}) == 3
    limits = d["limits"]
    assert limits == {"free_memory_percent_min": 30, "disk_bytes_min": 10 * 1024**3,
                      "process_tree_rss_bytes_max": int(2.5 * 1024**3), "build_seconds_max": 60}
    assert len(d["preflights"]) == 11
    assert all(p["free_memory_percent"] >= 30 and p["free_disk_bytes"] >= 10 * 1024**3 for p in d["preflights"])
    commands = d["commands"]
    labels = ["fresh-baseline", "warm-no-write"] + [f"identical-replace-{n}" for n in range(2, 6)] + ["charon-mutant", "aeneas-mutant", "function-change", "changed-no-write"]
    assert [c["label"] for c in commands] == labels
    # Commands retain execution-time absolute paths. Bind them to the recorded
    # package layout; inspect artifact bytes through HERE so copied packages work.
    recorded_here = Path(commands[0]["cwd"]).parents[1]
    assert recorded_here.is_absolute() and recorded_here.name == "support"
    assert recorded_here.parent.name == HERE.parent.name
    for c in commands:
        assert c["exit"] == 0 and c["guard_failure"] is None and c["peak_tree_rss_bytes"] <= int(2.5 * 1024**3)
        assert c["elapsed_seconds"] <= 60
        for stream in ("stdout", "stderr"):
            assert c[f"{stream}_sha256"] == sha(log_bytes(c["label"], stream))
        assert c["argv"] and c["cwd"]
    tools = d["identity"]["tools"]
    assert any(k.endswith("/bin/lake") for k in tools)
    lake_path = next(k for k in tools if k.endswith("/bin/lake"))
    charon_path = next(k for k in tools if k.endswith("/bin/charon"))
    aeneas_path = next(k for k in tools if k.endswith("/bin/aeneas"))
    for c in commands:
        if c["label"] in labels[:6] + labels[-2:]:
            assert c["argv"] == [lake_path, "build", "-v"]
            assert c["cwd"] == str(recorded_here / "work/consumer")
    assert commands[6]["argv"][0:4] == [charon_path, "cargo", "--preset", "aeneas"]
    assert commands[6]["cwd"] == str(recorded_here / "work/mutant")
    assert commands[6]["argv"][4:9] == ["--dest-file", str(recorded_here / "work/mutant.llbc"),
                                        "--", "--manifest-path", str(recorded_here / "work/mutant/Cargo.toml")]
    assert commands[6]["env_overrides"]["CARGO_TARGET_DIR"] == str(recorded_here / "work/target-mutant")
    assert commands[6]["argv"][-5:] == ["--lib", "--offline", "--locked", "-j", "1"]
    assert commands[7]["argv"][0:7] == [aeneas_path, "-backend", "lean", "-no-progress-bar", "-sequential", "-split-files", "-gen-lib-entry"]
    assert commands[7]["cwd"] == str(recorded_here / "work")
    assert commands[7]["argv"][7:] == ["-dest", str(recorded_here / "work/mutant-generated"),
                                        str(recorded_here / "work/mutant-input/probe.llbc")]
    assert all(c["env_overrides"].get("LAKE_NO_NET") == "1" and c["env_overrides"].get("LEAN_NUM_THREADS") == "1" and c["env_overrides"].get("LAKE_JOBS") == "1" for c in commands if c["label"] in labels[:6] + labels[-2:])
    builds = d["builds"]
    assert [b["label"] for b in builds] == labels[:6] + labels[-2:]
    for build in builds:
        stdout = log_bytes(build["label"], "stdout").decode()
        assert "Build completed successfully (1686 jobs)." in stdout
        assert build["own_job_lines"] == [line for line in stdout.splitlines()
            if re.search(r"\b(?:Built|Replayed) (?:Probe(?:\.|\s|$)|Consumer(?:\s|$))", line)]
        assert all("/1686]" in line for line in build["own_job_lines"])
    baseline = builds[0]["state"]
    status_lines(builds[0], dict.fromkeys(MODULES, "Built"))
    for build in builds[1:6]:
        status_lines(build, dict.fromkeys(MODULES, "Replayed"))
        for key, value in baseline.items():
            assert build["state"][key]["sha256"] == value["sha256"]
            if key.endswith((".trace", ".olean")):
                assert build["state"][key]["mtime_ns"] == value["mtime_ns"]
    changed = builds[6]["state"]
    status_lines(builds[6], {"Probe.Types": "Replayed", "Probe.Funs": "Built", "Probe": "Built", "Consumer": "Built"})
    status_lines(builds[7], dict.fromkeys(MODULES, "Replayed"))
    assert builds[7]["state"] == changed
    for mod in MODULES:
        assert artifact(changed, mod, "trace")["sha256"] == artifact(baseline, mod, "trace")["sha256"] if mod == "Probe.Types" else artifact(changed, mod, "trace")["sha256"] != artifact(baseline, mod, "trace")["sha256"]
    assert artifact(changed, "Probe.Funs", "olean")["sha256"] != artifact(baseline, "Probe.Funs", "olean")["sha256"]
    assert artifact(changed, "Probe.Types", "olean")["sha256"] == artifact(baseline, "Probe.Types", "olean")["sha256"]
    mutation = d["mutation"]
    original = (PRIOR / "support/fixture/src/lib.rs").read_text()
    mutant = (HERE / "work/mutant/src/lib.rs").read_text()
    assert original.count("x + 1") == 1 and mutant == original.replace("x + 1", "x + 2")
    assert mutation["original_sha256"] == sha(original.encode()) and mutation["changed_sha256"] == sha(mutant.encode())
    assert mutation["llbc_sha256"] == file_sha(HERE / "work/mutant.llbc")
    assert json.loads((HERE / "work/mutant.llbc").read_text())["has_errors"] is False
    for name, dest in SOURCES.items():
        assert mutation["generated"][name] == file_sha(HERE / "work/mutant-generated" / name)
        assert changed[dest]["sha256"] == mutation["generated"][name]
        assert baseline[dest]["sha256"] == d["identity"]["prior_generated"]["gen-1"][name]
    assert mutation["generated"]["Types.lean"] == baseline["Probe/Types.lean"]["sha256"]
    assert mutation["generated"]["Probe.lean"] == baseline["Probe.lean"]["sha256"]
    old_funs = (PRIOR / "support/artifacts/gen-1/Funs.lean").read_text()
    new_funs = (HERE / "work/mutant-generated/Funs.lean").read_text()
    assert old_funs.count("  x + 1#u32") == 1 and new_funs == old_funs.replace("  x + 1#u32", "  x + 2#u32")
    assert (HERE / "work/consumer/Consumer.lean").read_text().count("theorem ") == 5
    for label in ("fresh-baseline", "function-change"):
        stdout = log_bytes(label, "stdout").decode()
        assert "'combine_self' depends on axioms: [propext, Classical.choice, Quot.sound]" in stdout
        assert "sorryAx" not in stdout
    extracted = []
    for label in ("fresh-baseline", "function-change"):
        lines = [s for s in log_bytes(label, "stdout").decode().splitlines() if "'combine_self' depends on axioms" in s]
        assert len(lines) == 1
        extracted.extend([f"{label}:", lines[0], ""])
    assert (HERE / "theorem-output.txt").read_text() == "\n".join(extracted)
    summary = json.loads((HERE / "summary.json").read_text())
    assert summary["parent_commit"] == d["identity"]["parent_commit"]
    assert summary["mapping"] == {"I148": "partial", "E06": "context_only_partial", "E07": "context_only_partial", "F20": "context_only_partial"}
    assert [x["label"] for x in summary["builds"]] == [x["label"] for x in builds]
    assert summary["guards"]["max_sampled_tree_rss_bytes"] == max(c["peak_tree_rss_bytes"] for c in commands)
    metadata = json.loads((HERE.parent / "REPORT.json").read_text())
    assert metadata["observed_at"] == "2026-09-29" and len(metadata["subjects"]) == 3
    corpus, tools_subject, replay_subject = (subject["identity"] for subject in metadata["subjects"])
    assert corpus["prior_report_sha256"] == d["identity"]["prior_report_sha256"]
    assert corpus["prior_results_sha256"] == d["identity"]["prior_results_sha256"]
    assert corpus["original_rust_source_sha256"] == mutation["original_sha256"]
    assert tools_subject["charon_sha256"] == d["identity"]["tools"][charon_path]
    assert tools_subject["aeneas_sha256"] == d["identity"]["tools"][aeneas_path]
    assert tools_subject["lake_sha256"] == d["identity"]["tools"][lake_path]
    assert replay_subject["probe_sha256"] == file_sha(HERE / "probe.py")
    assert replay_subject["results_sha256"] == file_sha(HERE / "results.json")
    assert replay_subject["mutant_rust_source_sha256"] == mutation["changed_sha256"]
    assert replay_subject["mutant_funs_sha256"] == mutation["generated"]["Funs.lean"]
    for key, info in changed.items():
        p = HERE / "work/consumer" / key
        assert p.is_file() and file_sha(p) == info["sha256"] and p.stat().st_size == info["size"]
    print("PASS: 8 bounded Lake builds, four identical same-path replays, one function-change invalidation, retained artifacts and theorem output")

if __name__ == "__main__":
    main()
