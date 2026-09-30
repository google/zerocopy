#!/usr/bin/env python3
"""Offline checker for the retained package-local Lake interruption."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
r = json.loads((ROOT / "results.json").read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(ok, label):
    if not ok:
        raise AssertionError(label)


expected = ["old-build", "rlimit-control", "limited-update", "post-limit-no-build",
            "post-limit-direct", "uncapped-repair", "post-repair-no-build", "post-repair-direct"]
check(r["status"] == "completed" and [x["label"] for x in r["runs"]] == expected, "run order/completion")
check((r["lake_sha256"], r["lean_sha256"]) == (
    "9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb",
    "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"), "binary identity")
for key in ("admission", "continuation_admission"):
    a = r[key]
    check(a["memory"]["fraction"] > .30 and a["disk_free"] > 10 * 1024 ** 3, key)
check(r["old_olean_bytes"] == 4616 and r["chosen_limit_bytes"] == 2308 and r["rlimit_control_size"] == 2308, "size limit")
check(r["fixture_sha256"]["old"] == hashlib.sha256(b"def depValue : Nat := 7\n").hexdigest(), "old source")
check(r["fixture_sha256"]["new"] == r["source_after_edit_sha256"] == hashlib.sha256(b"def depValue : Nat := 9\n").hexdigest(), "new source")
check(r["fixture_sha256"]["lakefile"] == hashlib.sha256(b"import Lake\nopen Lake DSL\npackage probe_dep\n@[default_target]\nlean_lib Dep\n").hexdigest(), "lakefile fixture")
check(r["fixture_sha256"]["check"] == hashlib.sha256(b"import Dep\n#eval depValue\n").hexdigest(), "Check.lean fixture")

run = {x["label"]: x for x in r["runs"]}
for x in r["runs"]:
    label = x["label"]
    check(x["aborted"] is None and x["elapsed"] < 30 and x["resource_samples"], f"guard/exit: {label}")
    check(x["env_overrides"]["LAKE_NO_NET"] == "1" and x["env_overrides"]["LAKE_ARTIFACT_CACHE"] == "false", f"offline: {label}")
    for s in x["resource_samples"]:
        check(s["reclaimable"] >= .20 and s["disk_free"] >= 10 * 1024 ** 3,
              f"memory/disk guard: {label}")
        check(s["group_rss_kib"] <= 1200 * 1024 and s["scratch_bytes"] <= 100 * 1024 ** 2,
              f"RSS/scratch guard: {label}")
    for stream in ("stdout", "stderr"):
        check(sha(ROOT / "raw" / f"{label}.{stream}") == x[f"{stream}_sha256"], f"raw: {label}/{stream}")
    if label not in ("old-build", "rlimit-control"):
        check(x["before"]["producer/Dep.lean"]["sha256"] == r["fixture_sha256"]["new"], f"new input: {label}")
    if label not in ("rlimit-control",):
        check(x["cwd"].endswith("/work/producer"), f"producer cwd: {label}")
    check(x["before"]["producer/Check.lean"]["sha256"] == r["fixture_sha256"]["check"] and
          x["before"]["producer/lakefile.lean"]["sha256"] == r["fixture_sha256"]["lakefile"],
          f"fixed fixtures: {label}")
check([run[x]["exit"] for x in expected] == [0, 1, 1, 3, 1, 0, 0, 0], "exit matrix")
for before, after in zip(r["runs"], r["runs"][1:]):
    left, right = before["after"], after["before"]
    check(left.keys() == right.keys(), f"adjacent paths: {before['label']}→{after['label']}")
    changed = {k for k in left if left[k] != right[k]}
    allowed = {"producer/Dep.lean"} if (before["label"], after["label"]) == ("rlimit-control", "limited-update") else set()
    check(changed == allowed, f"adjacent inventory: {before['label']}→{after['label']}")
for label in ("post-limit-no-build", "post-repair-no-build"):
    x = run[label]
    check(x["argv"][-3:] == ["--no-build", "build", "Dep"] and x["argv"][0].endswith("/bin/lake"), f"no-build argv: {label}")
for label in ("post-limit-direct", "post-repair-direct"):
    x = run[label]
    check(x["argv"][-2:] == ["--json", "Check.lean"] and x["argv"][0].endswith("/bin/lean"), f"direct argv: {label}")
check(run["rlimit-control"]["rlimit_fsize_bytes"] == run["limited-update"]["rlimit_fsize_bytes"] == 2308,
      "child limits")
check(all(run[x]["rlimit_fsize_bytes"] is None for x in expected if x not in ("rlimit-control", "limited-update")),
      "other calls uncapped")
check((ROOT / "work/fsize-control.bin").stat().st_size == 2308, "child write control bytes")
check("File too large" in (ROOT / "raw/rlimit-control.stderr").read_text(), "child limit error")
limited_stdout = (ROOT / "raw/limited-update.stdout").read_text()
check("Lean exited with code 153" in limited_stdout and " -o " in limited_stdout and "Dep.olean" in limited_stdout,
      "limited child invocation and exit")
check("out-of-date and needs to be rebuilt" in (ROOT / "raw/post-limit-no-build.stdout").read_text(), "no-build rejected")
check("unknown module prefix 'Dep'" in (ROOT / "raw/post-limit-direct.stdout").read_text(), "fresh direct rejected")
check("Built Dep" in (ROOT / "raw/uncapped-repair.stdout").read_text(), "repair build")
check("Replayed Dep" in (ROOT / "raw/post-repair-no-build.stdout").read_text(), "repaired no-build")
msgs = [json.loads(line) for line in (ROOT / "raw/post-repair-direct.stdout").read_text().splitlines()]
check(len(msgs) == 1 and msgs[0]["data"] == "9" and msgs[0]["severity"] == "information", "repaired direct value")

for name, files in r["snapshots"].items():
    root = ROOT / "snapshots" / name
    check({str(p.relative_to(root)) for p in root.rglob("*") if p.is_file()} == set(files), f"snapshot paths: {name}")
    for rel, meta in files.items():
        path = root / rel
        check(path.stat().st_size == meta["size"] and sha(path) == meta["sha256"], f"snapshot hash: {name}/{rel}")
    source_run = {"old-valid": "old-build", "after-limited": "limited-update",
                  "after-repair": "uncapped-repair"}[name]
    recorded = {k.removeprefix("producer/"): v for k, v in run[source_run]["after"].items()
                if k.startswith("producer/")}
    check(files == recorded, f"snapshot tied to run: {name}")

old = r["snapshots"]["old-valid"]
partial = r["snapshots"]["after-limited"]
repaired = r["snapshots"]["after-repair"]
olean = ".lake/build/lib/lean/Dep.olean"
trace = ".lake/build/lib/lean/Dep.trace"
sidecar = ".lake/build/lib/lean/Dep.olean.hash"
temps = [p for p in partial if p.startswith(olean + ".tmp.")]
check(old[olean]["size"] == 4616 and old[olean]["sha256"] == r["old_olean_sha256"], "old OLean preimage")
check(len(temps) == 1 and partial[temps[0]]["size"] == 2308 and olean not in partial,
      "partial temp and absent final")
check(partial[sidecar]["sha256"] == old[sidecar]["sha256"] and partial[trace]["sha256"] == old[trace]["sha256"],
      "old sidecar and trace retained")
check(partial["Dep.lean"]["sha256"] == r["fixture_sha256"]["new"], "partial source 9")
check(repaired[olean]["size"] == 4520 and repaired[olean]["sha256"] != old[olean]["sha256"], "repaired OLean")
check(repaired[trace]["sha256"] != old[trace]["sha256"] and repaired[sidecar]["sha256"] != old[sidecar]["sha256"], "repair trace/sidecar")
check(repaired[temps[0]]["sha256"] == partial[temps[0]]["sha256"], "orphan temp survives repair")
check(run["post-repair-direct"]["after"]["producer/" + olean]["sha256"] == repaired[olean]["sha256"], "final OLean")

events = run["limited-update"]["observed_file_events"]
removed = [e["elapsed"] for e in events if olean in e["removed"]]
created = [e["elapsed"] for e in events if temps[0] in e["changed"]]
check(len(removed) == len(created) == 1 and removed[0] < created[0], "observed file-event order")
print("PASS: limited child output, package-local partial temp, fail-closed no-build/direct, uncapped repair and orphan temp")
