#!/usr/bin/env python3
"""One-shot, guarded offline Lake package-version ablation."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import threading
import time

ROOT = Path(__file__).resolve().parent
ORACLE = json.loads((ROOT / "oracle.json").read_text())
WORK = ROOT / "work"
LAKE = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lake")
LEAN = LAKE.with_name("lean")
RSS_LIMIT_KIB = 1200 * 1024
SCRATCH_LIMIT = 100 * 1024 * 1024
DISK_LIMIT = 10 * 1024 ** 3


def sha(data):
    return hashlib.sha256(data).hexdigest()


def memory():
    total = int(subprocess.check_output(["sysctl", "-n", "hw.memsize"]).strip())
    raw = subprocess.check_output(["vm_stat"], text=True)
    page = int(re.search(r"page size of (\d+) bytes", raw).group(1))
    vals = {k: int(v.replace(".", "")) for k, v in re.findall(r"Pages ([\w ]+):\s+(\d+\.)", raw)}
    fraction = page * sum(vals[k] for k in ("free", "inactive", "speculative")) / total
    return {"total_bytes": total, "page_bytes": page, "pages": vals,
            "reclaimable_fraction": fraction}


def disk():
    du = shutil.disk_usage(ROOT)
    return {"total": du.total, "used": du.used, "free": du.free}


def size(path):
    return sum(p.stat().st_size for p in path.rglob("*") if p.is_file() and not p.is_symlink())


def inventory(path):
    return {str(p.relative_to(path)): {"sha256": sha(p.read_bytes()), "bytes": p.stat().st_size,
                                        "mtime_ns": p.stat().st_mtime_ns}
            for p in sorted(path.rglob("*")) if p.is_file() and not p.is_symlink()}


def selected(inv):
    return {k: v for k, v in inv.items() if k.endswith(("lakefile.olean", "lakefile.olean.trace",
            "Dep.olean", "Dep.olean.trace", "Generated.olean", "Generated.olean.trace",
            "lake-manifest.json", "lakefile.lean", "Dep.lean", "Generated.lean", "lean-toolchain"))}


def fixture_text(key):
    x = ORACLE["files"][key]
    data = x["text"].encode()
    assert sha(data) == x["sha256"], key
    return data


def write_if_changed(path, data):
    if not path.exists() or path.read_bytes() != data:
        path.write_bytes(data)


def manifest(name, deps):
    return {"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [
        {"type": "path", "scope": "", "name": "probe_dep", "manifestFile": "lake-manifest.json",
         "inherited": False, "dir": "../producer", "configFile": "lakefile.lean"} for _ in deps],
        "name": name, "lakeDir": ".lake", "fixedToolchain": False}


def initialize_case(case):
    producer, consumer = case / "producer", case / "consumer"
    producer.mkdir(parents=True)
    consumer.mkdir(parents=True)
    (producer / "lakefile.lean").write_bytes(fixture_text("producer_v1_lakefile"))
    (producer / "Dep.lean").write_bytes(fixture_text("producer_dep7"))
    (consumer / "lakefile.lean").write_bytes(fixture_text("consumer_lakefile"))
    (consumer / "Generated.lean").write_bytes(fixture_text("consumer_generated"))
    for path, name, deps in ((producer, "probe_dep", []), (consumer, "consumer", [1])):
        (path / "lean-toolchain").write_text(ORACLE["toolchain"] + "\n")
        (path / "lake-manifest.json").write_text(json.dumps(manifest(name, deps), indent=2) + "\n")
    return producer, consumer


def rss_group(pgid):
    proc = subprocess.run(["ps", "-axo", "pgid=,rss="], capture_output=True, text=True, timeout=3)
    total = 0
    for line in proc.stdout.splitlines():
        fields = line.split()
        if len(fields) == 2 and fields[0].isdigit() and fields[1].isdigit() and int(fields[0]) == pgid:
            total += int(fields[1])
    return total


def run(label, case, args, deadline, env, result):
    before = inventory(case)
    argv = [str(LAKE), "--keep-toolchain", "--no-cache", "--no-ansi", "-v", *args]
    start = time.monotonic()
    p = subprocess.Popen(argv, cwd=case / "consumer", env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, start_new_session=True)
    out = [None]

    def drain():
        out[0] = p.communicate()

    t = threading.Thread(target=drain, daemon=True)
    t.start()
    samples = []
    aborted = None
    while t.is_alive():
        mem = memory()
        ds = disk()
        scratch = size(WORK)
        rss = rss_group(p.pid)
        samples.append({"elapsed": round(time.monotonic() - start, 4), "memory": mem,
                        "disk_free": ds["free"], "scratch_bytes": scratch, "group_rss_kib": rss})
        if mem["reclaimable_fraction"] < 0.20:
            aborted = "reclaimable_below_20_percent"
        elif ds["free"] < DISK_LIMIT:
            aborted = "disk_below_10_gib"
        elif scratch > SCRATCH_LIMIT:
            aborted = "scratch_over_100_mib"
        elif rss > RSS_LIMIT_KIB:
            aborted = "group_rss_over_1200_mib"
        elif time.monotonic() > deadline:
            aborted = "cell_over_30_seconds"
        if aborted:
            os.killpg(p.pid, signal.SIGKILL)
            break
        t.join(0.1)
    t.join(3)
    if out[0] is None:
        out[0] = (b"", b"")
    stdout, stderr = out[0]
    raw = ROOT / "raw"
    raw.mkdir(exist_ok=True)
    (raw / f"{label}.stdout").write_bytes(stdout)
    (raw / f"{label}.stderr").write_bytes(stderr)
    after = inventory(case)
    rec = {"label": label, "argv": argv, "cwd": str(case / "consumer"),
           "env_overrides": {k: env[k] for k in ("ELAN_TOOLCHAIN", "LEAN_NUM_THREADS", "LAKE_ARTIFACT_CACHE", "LAKE_NO_CACHE", "LAKE_NO_NET", "HOME", "XDG_CACHE_HOME", "PATH")},
           "pid": p.pid, "exit": p.returncode, "aborted": aborted,
           "elapsed": round(time.monotonic() - start, 4), "samples": samples,
           "stdout_sha256": sha(stdout), "stderr_sha256": sha(stderr),
           "before": before, "after": after}
    result["runs"].append(rec)
    (ROOT / "results.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    if aborted or p.returncode:
        raise RuntimeError(f"{label}: {aborted or p.returncode}")
    return rec


def main():
    assert not WORK.exists(), "one-shot work directory already exists"
    assert sha(LAKE.read_bytes()) == ORACLE["lake_sha256"]
    assert sha(LEAN.read_bytes()) == ORACLE["lean_sha256"]
    assert ORACLE["main_versions"] == ["1.0.0", "2.0.0", "1.0.0"]
    assert ORACLE["control_values"] == [7, 9]
    preflight = {"memory": memory(), "disk": disk()}
    result = {"schema": 1, "oracle_sha256": sha((ROOT / "oracle.json").read_bytes()),
              "preflight": preflight, "lake_sha256": sha(LAKE.read_bytes()),
              "lean_sha256": sha(LEAN.read_bytes()), "runs": [], "cells": [], "status": "prepared"}
    (ROOT / "results.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    if preflight["memory"]["reclaimable_fraction"] <= 0.30 or preflight["disk"]["free"] <= DISK_LIMIT:
        result["status"] = "admission_denied"
        (ROOT / "results.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
        return
    WORK.mkdir()
    for label in ("main", "control"):
        initialize_case(WORK / label)
    env = dict(os.environ)
    env.update({"ELAN_TOOLCHAIN": ORACLE["toolchain"], "LEAN_NUM_THREADS": "1",
                "LAKE_ARTIFACT_CACHE": "false", "LAKE_NO_CACHE": "1", "LAKE_NO_NET": "1",
                "HOME": str(WORK / "home"), "XDG_CACHE_HOME": str(WORK / "cache"),
                "PATH": str(LAKE.parent) + os.pathsep + env.get("PATH", "")})
    Path(env["HOME"]).mkdir()
    Path(env["XDG_CACHE_HOME"]).mkdir()
    try:
        for case_name, variants in (("main", [("v1", "producer_v1_lakefile", "producer_dep7"),
                                              ("v2", "producer_v2_lakefile", "producer_dep7"),
                                              ("v1return", "producer_v1_lakefile", "producer_dep7")]),
                                    ("control", [("value7", "producer_v1_lakefile", "producer_dep7"),
                                                 ("value9", "producer_v1_lakefile", "producer_dep9")])):
            case = WORK / case_name
            for variant, config_key, source_key in variants:
                write_if_changed(case / "producer/lakefile.lean", fixture_text(config_key))
                write_if_changed(case / "producer/Dep.lean", fixture_text(source_key))
                cell = {"case": case_name, "variant": variant, "config_key": config_key,
                        "source_key": source_key, "before": selected(inventory(case)), "run_labels": []}
                result["cells"].append(cell)
                deadline = time.monotonic() + ORACLE["maximum_cell_seconds"]
                for action, opts in (("build", ["build", "Generated"]),
                                     ("setup", ["setup-file", str(case / "consumer/Generated.lean")]),
                                     ("eval", ["env", "lean", "--json", "Generated.lean"])):
                    label = f"{case_name}-{variant}-{action}"
                    run(label, case, opts, deadline, env, result)
                    cell["run_labels"].append(label)
                cell["after"] = selected(inventory(case))
                snapshot = ROOT / "snapshots" / f"{case_name}-{variant}"
                snapshot.mkdir(parents=True)
                cell["snapshot_files"] = {}
                for rel in cell["after"]:
                    source = case / rel
                    target = snapshot / rel
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(source, target)
                    cell["snapshot_files"][rel] = sha(target.read_bytes())
                result["status"] = "in_progress"
                (ROOT / "results.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
        result["status"] = "completed"
    except Exception as exc:
        result["status"] = "stopped"
        result["error"] = str(exc)
    finally:
        result["final_disk"] = disk()
        result["final_memory"] = memory()
        result["final_scratch_bytes"] = size(WORK)
        (ROOT / "results.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
