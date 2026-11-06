#!/usr/bin/env python3
"""Offline raw-evidence checker for the Lake version-only ablation."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
o = json.loads((ROOT / "oracle.json").read_text())
r = json.loads((ROOT / "results.json").read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def assertion(condition, message):
    if not condition:
        raise AssertionError(message)


assertion(r["status"] == "completed" and len(r["runs"]) == 15 and len(r["cells"]) == 5, "run completion")
assertion(r["oracle_sha256"] == digest(ROOT / "oracle.json"), "oracle hash")
assertion(r["lake_sha256"] == o["lake_sha256"] and r["lean_sha256"] == o["lean_sha256"], "binary hashes")
assertion(r["preflight"]["memory"]["reclaimable_fraction"] > .30 and r["preflight"]["disk"]["free"] > 10 * 1024 ** 3, "admission")

expected_cells = [("main", "v1", "producer_v1_lakefile", "producer_dep7", "7"),
                  ("main", "v2", "producer_v2_lakefile", "producer_dep7", "7"),
                  ("main", "v1return", "producer_v1_lakefile", "producer_dep7", "7"),
                  ("control", "value7", "producer_v1_lakefile", "producer_dep7", "7"),
                  ("control", "value9", "producer_v1_lakefile", "producer_dep9", "9")]
assertion([(x["case"], x["variant"], x["config_key"], x["source_key"]) for x in r["cells"]] == [e[:4] for e in expected_cells], "cell order")
run_by_label = {x["label"]: x for x in r["runs"]}
assertion(len(run_by_label) == 15, "duplicate run labels")

for c, (_, _, config, source, value) in zip(r["cells"], expected_cells):
    prefix = f'{c["case"]}-{c["variant"]}'
    assertion(c["run_labels"] == [f"{prefix}-{a}" for a in ("build", "setup", "eval")], "action order")
    after = c["after"]
    for rel, key in (("producer/lakefile.lean", config), ("producer/Dep.lean", source),
                     ("consumer/lakefile.lean", "consumer_lakefile"),
                     ("consumer/Generated.lean", "consumer_generated")):
        assertion(after[rel]["sha256"] == o["files"][key]["sha256"], f"fixture: {prefix}/{rel}")
    for rel, expected_hash in c["snapshot_files"].items():
        path = ROOT / "snapshots" / prefix / rel
        assertion(path.is_file() and digest(path) == expected_hash == after[rel]["sha256"], f"snapshot: {prefix}/{rel}")
    assertion(set(c["snapshot_files"]) == set(after), "snapshot completeness")
    producer_manifest = json.loads((ROOT / "snapshots" / prefix / "producer/lake-manifest.json").read_text())
    consumer_manifest = json.loads((ROOT / "snapshots" / prefix / "consumer/lake-manifest.json").read_text())
    assertion(producer_manifest["name"] == "probe_dep" and producer_manifest["packages"] == [], "producer manifest")
    assertion(consumer_manifest["name"] == "consumer" and len(consumer_manifest["packages"]) == 1, "consumer manifest")
    assertion(consumer_manifest["packages"][0]["dir"] == "../producer", "fixed dep path")
    trace = json.loads((ROOT / "snapshots" / prefix / "producer/.lake/config/probe_dep/lakefile.olean.trace").read_text())
    assertion(trace["name"] == "probe_dep" and trace["idx"] == 1 and trace["options"] == {}, "config trace identity")
    expected_config_hash = "b74db869a8cb920f" if prefix == "main-v2" else "a5b4b476a0591aca"
    assertion(trace["configHash"] == expected_config_hash, f"configHash: {prefix}")
    for action in ("build", "setup", "eval"):
        label = f"{prefix}-{action}"
        x = run_by_label[label]
        assertion(x["exit"] == 0 and x["aborted"] is None and x["elapsed"] < 30, f"exit: {label}")
        assertion(x["cwd"].endswith(f"/work/{c['case']}/consumer"), f"fixed cwd: {label}")
        assertion(x["env_overrides"]["LAKE_NO_NET"] == "1" and x["env_overrides"]["LAKE_ARTIFACT_CACHE"] == "false", "offline env")
        assertion(x["argv"][:5] == [x["argv"][0], "--keep-toolchain", "--no-cache", "--no-ansi", "-v"], "base argv")
        assertion(x["argv"][0].endswith("/bin/lake"), "lake argv")
        assertion(x["before"] and x["after"] and x["samples"], f"capture: {label}")
        rawout = ROOT / "raw" / f"{label}.stdout"
        rawerr = ROOT / "raw" / f"{label}.stderr"
        assertion(digest(rawout) == x["stdout_sha256"] and digest(rawerr) == x["stderr_sha256"], f"raw hashes: {label}")
        for sample in x["samples"]:
            assertion(sample["memory"]["reclaimable_fraction"] >= .20 and sample["disk_free"] >= 10 * 1024 ** 3, f"resource: {label}")
            assertion(sample["scratch_bytes"] <= 100 * 1024 ** 2 and sample["group_rss_kib"] <= 1200 * 1024, f"resource: {label}")
        text = rawout.read_text() + rawerr.read_text()
        if action == "build":
            assertion("Dep" in text and "Generated" in text, f"build actions: {label}")
        if action == "setup":
            setup = json.loads(rawout.read_text().strip())
            path = setup["importArts"]["Dep"][0]
            assertion(path == str(Path(x["cwd"]).parent / "producer/.lake/build/lib/lean/Dep.olean"), f"setup import: {label}")
            assertion(setup["package"] == "consumer" and setup["name"] == "Generated", f"setup identity: {label}")
        if action == "eval":
            messages = [json.loads(line) for line in rawout.read_text().splitlines()]
            assertion(len(messages) == 1 and messages[0]["data"] == value and messages[0]["severity"] == "information", f"eval: {label}")
    assertion(all(run_by_label[f"{prefix}-eval"]["after"][k]["sha256"] == v["sha256"] for k, v in after.items()), "final inventory agrees")
    build, setup, evaluate = (run_by_label[f"{prefix}-{a}"] for a in ("build", "setup", "eval"))
    assertion(build["after"] == setup["before"] and setup["after"] == evaluate["before"], f"adjacent action continuity: {prefix}")
    assertion(setup["before"] == setup["after"] and evaluate["before"] == evaluate["after"], f"setup/eval write inventory: {prefix}")

def delta(run):
    before, after = run["before"], run["after"]
    return ({k for k in before.keys() & after.keys() if before[k]["sha256"] != after[k]["sha256"]},
            set(after) - set(before), set(before) - set(after))

config_files = {"producer/.lake/config/probe_dep/lakefile.olean",
                "producer/.lake/config/probe_dep/lakefile.olean.trace"}
lock_file = {"producer/.lake/config/probe_dep/lakefile.olean.lock"}
assertion(delta(run_by_label["main-v2-build"]) == (config_files, lock_file, set()), "version B write inventory")
assertion(delta(run_by_label["main-v1return-build"]) == (config_files, set(), set()), "version A return write inventory")
source_changes = {"producer/.lake/build/ir/Dep.c", "producer/.lake/build/ir/Dep.c.hash",
                  "producer/.lake/build/lib/lean/Dep.olean", "producer/.lake/build/lib/lean/Dep.olean.hash",
                  "producer/.lake/build/lib/lean/Dep.trace", "consumer/.lake/build/lib/lean/Generated.trace"}
assertion(delta(run_by_label["control-value9-build"]) == (source_changes, set(), set()), "source control write inventory")

for first, second, edited in (("main-v1", "main-v2", "producer/lakefile.lean"),
                              ("main-v2", "main-v1return", "producer/lakefile.lean"),
                              ("control-value7", "control-value9", "producer/Dep.lean")):
    after = run_by_label[f"{first}-eval"]["after"]
    before = run_by_label[f"{second}-build"]["before"]
    assertion(after.keys() == before.keys(), f"inter-cell key continuity: {first} to {second}")
    assertion({k for k in after if after[k]["sha256"] != before[k]["sha256"]} == {edited},
              f"only predeclared edit: {first} to {second}")
    assertion(all(after[k] == before[k] for k in after if k != edited), f"unmodified cell inputs: {first} to {second}")

for case, last in (("main", "main-v1return"), ("control", "control-value9")):
    recorded = run_by_label[f"{last}-eval"]["after"]
    actual = {}
    case_root = ROOT / "work" / case
    for path in case_root.rglob("*"):
        if path.is_file() and not path.is_symlink():
            stat = path.stat()
            actual[str(path.relative_to(case_root))] = {"sha256": digest(path), "bytes": stat.st_size,
                                                       "mtime_ns": stat.st_mtime_ns}
    assertion(actual == recorded, f"final work inventory: {case}")

def h(c, path):
    return c["after"][path]["sha256"]

m1, m2, m3, n7, n9 = r["cells"]
config_olean = "producer/.lake/config/probe_dep/lakefile.olean"
config_trace = config_olean + ".trace"
dep_olean = "producer/.lake/build/lib/lean/Dep.olean"
gen_olean = "consumer/.lake/build/lib/lean/Generated.olean"
assertion(h(m1, config_olean) != h(m2, config_olean) and h(m1, config_olean) == h(m3, config_olean), "version config OLean reversible")
assertion(h(m1, config_trace) != h(m2, config_trace) and h(m1, config_trace) == h(m3, config_trace), "version config trace reversible")
assertion(len({h(c, dep_olean) for c in (m1, m2, m3)}) == 1, "version Dep OLean stable")
assertion(len({h(c, gen_olean) for c in (m1, m2, m3)}) == 1, "version Generated OLean stable")
assertion(len({h(c, "producer/Dep.lean") for c in (m1, m2, m3)}) == 1, "version source stable")
assertion(len({h(c, "producer/lake-manifest.json") for c in (m1, m2, m3)}) == 1, "version manifest stable")
assertion(len({h(c, "consumer/lake-manifest.json") for c in (m1, m2, m3)}) == 1, "version consumer manifest stable")
assertion(h(n7, config_olean) == h(n9, config_olean) and h(n7, config_trace) == h(n9, config_trace), "source config stable")
assertion(h(n7, dep_olean) != h(n9, dep_olean), "source Dep OLean changed")
assertion(h(n7, "producer/lakefile.lean") == h(n9, "producer/lakefile.lean"), "source version fixed")
for label in ("main-v2-build", "main-v1return-build"):
    assertion(re.search(r"Replayed Dep", (ROOT / "raw" / f"{label}.stdout").read_text()), f"replay: {label}")
assertion("Built Dep" in (ROOT / "raw/control-value9-build.stdout").read_text(), "source build")
assertion((ROOT / "preliminary/first/results.json").exists() and
          (ROOT / "preliminary/second/results.json").exists(), "excluded acquisitions preserved")
print("PASS: 5 cells, 15 raw-backed calls, reversible version config hashes, stable version-only module OLeans, distinct source-value control")
