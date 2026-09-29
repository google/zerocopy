#!/usr/bin/env python3
"""Read-only checks for the preserved two-consumer Lake cache experiment."""

import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULT = json.loads((HERE / "results.json").read_text())
REJECTED = json.loads((HERE / "rejected-wrapper-results.json").read_text())


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def digest(data):
    return hashlib.sha256(data.encode()).hexdigest()


def file_hash(inventory, path):
    return inventory[path]["sha256"]


source = (
    "import Dep\ntheorem generatedEq : depValue + 1 = 8 := by\n"
    "  trace_state\n  decide\n#print axioms generatedEq\n"
    "#eval depValue + 1\n"
)
require(RESULT["source"] == source, "fixture source differs")
require(RESULT["tools"] == {
    "lake_sha256": "9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb",
    "lean_sha256": "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997",
}, "tool identities differ")
limits = RESULT["limits"]
pre = RESULT["preflight"]
guard = RESULT["guard"]
require(pre["disk_free_bytes"] >= limits["disk_bytes"], "disk admission failed")
require(pre["memory_free_percent"] >= limits["start_free_percent"], "memory admission failed")
require(limits["start_free_percent"] == 23 and limits["runtime_free_percent"] == 12, "memory policy differs")
require(limits["rss_kib"] == 4500000 and limits["cell_seconds"] == 75 and limits["call_seconds"] == 30, "run caps differ")
require(guard["abort"] is None and guard["samples"] > 0, "guard aborted or did not sample")
require(0 < guard["peak_rss_kib"] < limits["rss_kib"], "sampled RSS cap")
require(guard["min_free_percent"] >= limits["runtime_free_percent"], "runtime memory floor")
require(guard["max_processes"] <= 8, "unexpected process count")

seed = RESULT["seed_build"]
require(seed["args"] == ["-v", "build", "Generated"] and seed["exit"] == 0, "seed build")
require("Built Dep" in seed["stdout"] and "Built Generated" in seed["stdout"], "seed build provenance")
require("⊢ depValue + 1 = 8" in seed["stdout"] and "does not depend on any axioms" in seed["stdout"], "seed theorem output")
require(RESULT["seed_before"] == RESULT["seed_after"], "seed tree changed")
require(RESULT["cache_before"] == RESULT["cache_after"], "shared cache changed")
require(len(RESULT["cache_before"]) == 8, "seeded cache file count")

expected = {
    "Dep.olean": "cebebbbc892381bd3920a0b12ab5e4d65f1804574357994ccb20f95f87f98f9b",
    "Generated.olean": "e807370f82380c588dad12a60d8e2475ac82fc5232cffbbf68a8b1a7dbef9401",
}
require(RESULT["seed_product"] == expected, "seed product hashes")
require(file_hash(RESULT["seed_before"], "producer/Dep.lean") == digest("def depValue : Nat := 7\n"), "seed dependency source")
require(file_hash(RESULT["seed_before"], "consumer/Generated.lean") == digest(source), "seed generated source")
for module, rel in (("Dep.olean", "producer/.lake/build/lib/lean/Dep.olean"),
                    ("Generated.olean", "consumer/.lake/build/lib/lean/Generated.olean")):
    require(file_hash(RESULT["seed_before"], rel) == expected[module], "seed product inventory " + module)
    require(any(path.endswith(".olean") and data["sha256"] == expected[module]
                for path, data in RESULT["cache_before"].items()), "cache product " + module)

require(set(RESULT["consumers"]) == {"a", "b"}, "not exactly two consumers")
require(set(RESULT["private_before"]) == {"a", "b"}, "private roots")
source_paths = {
    "producer/Dep.lean", "producer/lakefile.lean", "producer/lean-toolchain",
    "consumer/Generated.lean", "consumer/lakefile.lean",
    "consumer/lean-toolchain", "consumer/lake-manifest.json",
}
expected_data = ["⊢ depValue + 1 = 8", "'generatedEq' does not depend on any axioms", "8"]
builds = []
goals = []
batch_streams = []
for label in ("a", "b"):
    initial = RESULT["private_before"][label]
    consumer = RESULT["consumers"][label]
    require(set(initial) == source_paths, label + " was not source-only")
    for path in source_paths:
        require(file_hash(initial, path) == file_hash(RESULT["seed_before"], path), label + " source/config mismatch " + path)
    dep_after = consumer["producer_after"]
    generated_after = consumer["consumer_after"]
    for path in source_paths:
        half, rel = path.split("/", 1)
        after = dep_after if half == "producer" else generated_after
        require(file_hash(initial, path) == file_hash(after, rel), label + " source/config changed " + path)
    require(file_hash(dep_after, ".lake/build/lib/lean/Dep.olean") == expected["Dep.olean"], label + " fetched Dep hash")
    require(file_hash(generated_after, ".lake/build/lib/lean/Generated.olean") == expected["Generated.olean"], label + " fetched Generated hash")
    for inv, stem in ((dep_after, "Dep"), (generated_after, "Generated")):
        for suffix in (".olean", ".ilean", ".trace"):
            require(any(path.endswith("/" + stem + suffix) for path in inv), label + " missing artifact " + stem + suffix)
    build = consumer["build"]
    require(build["args"] == ["-v", "--no-build", "build", "Generated"], label + " no-build command")
    require(build["exit"] == 0 and not build["stderr"], label + " no-build exit")
    actions = [line for line in build["stdout"].splitlines() if "Fetched " in line or "Built " in line or "Replayed " in line]
    require(len(actions) == 2 and "Fetched Dep" in actions[0] and "Fetched Generated" in actions[1], label + " cache fetch provenance")
    builds.append(build)
    batch = consumer["batch"]
    require(batch["args"] == ["--no-cache", "env", "lean", "--json", "Generated.lean"], label + " batch command")
    require(batch["exit"] == 0 and not batch["stderr"], label + " batch exit")
    messages = [json.loads(line) for line in batch["stdout"].splitlines()]
    require([message["data"] for message in messages] == expected_data, label + " batch theorem/value")
    batch_streams.append(batch["stdout"])
    goal = consumer["goal"]
    require(goal["error"] is None and goal["wait"] == {"id": 2, "jsonrpc": "2.0", "result": {}}, label + " diagnostic wait")
    require(goal["goal"]["result"]["goals"] == [expected_data[0]], label + " live first goal")
    require(goal["goal"]["result"]["rendered"] == "```lean\n⊢ depValue + 1 = 8\n```", label + " rendered goal")
    require(goal["stop"] == {"exit": 0, "stderr": ""}, label + " server exit")
    require(goal["diagnostics"] and all(d["params"]["uri"] == "$WORK_URI/" + label + "/consumer/Generated.lean" for d in goal["diagnostics"]), label + " diagnostic source")
    require(all(m.get("severity") == 3 for d in goal["diagnostics"] for m in d["params"]["diagnostics"]), label + " error diagnostic")
    goals.append(goal)
require(batch_streams[0] == batch_streams[1], "batch oracle diverged")
require(max(x["start"] for x in builds) < min(x["end"] for x in builds), "no-build fetches did not overlap")
require(max(x["start"] for x in goals) < min(x["end"] for x in goals), "server sessions did not overlap")

for label in ("a", "b"):
    rejected = REJECTED["consumers"][label]
    require(rejected["build"]["exit"] == 65 and "sandbox-exec: illegal argument" in rejected["build"]["stderr"], "initial wrapper failure class")
    require("BrokenPipeError" in rejected["goal"]["error"], "initial wrapper server failure class")

print("Two concurrent fresh Lake cache consumers: preserved evidence passed")
