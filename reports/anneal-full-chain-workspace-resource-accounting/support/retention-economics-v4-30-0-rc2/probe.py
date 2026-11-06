#!/usr/bin/env python3
"""Sequential tiny Lake generation retention and owned cleanup probe."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

TOOLCHAIN = "leanprover/lean4:v4.30.0-rc2"


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def inventory(root):
    files = {}
    if not root.exists():
        return files
    for p in sorted(root.rglob("*")):
        if p.is_file():
            st = p.stat()
            files[str(p.relative_to(root))] = {
                "sha256": sha(p), "bytes": st.st_size,
                "blocks_bytes": st.st_blocks * 512,
            }
    return files


def bill(root):
    files = inventory(root)
    return {"files": len(files), "logical_bytes": sum(x["bytes"] for x in files.values()),
            "blocks_bytes": sum(x["blocks_bytes"] for x in files.values())}


def make(base, value):
    base.mkdir(parents=True, exist_ok=False)
    (base / "source.json").write_text(json.dumps({"value": value}) + "\n")
    prod = base / "producer"
    cons = base / "consumer"
    prod.mkdir()
    cons.mkdir()
    (prod / "lakefile.lean").write_text(
        "import Lake\nopen Lake DSL\npackage retained_dep\n@[default_target]\nlean_lib Dep\n")
    (prod / "Dep.lean").write_text(f"def depValue : Nat := {value}\n")
    (prod / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    (cons / "lakefile.lean").write_text(
        'import Lake\nopen Lake DSL\nrequire retained_dep from "../producer"\n'
        "package retained_consumer\n@[default_target]\nlean_lib Generated\n")
    (cons / "Generated.lean").write_text(
        f"import Dep\ntheorem generationEq : depValue = {value} := by decide\n"
        "#eval depValue\n")
    (cons / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    manifest = {"version": "1.2.0", "packagesDir": ".lake/packages",
                "packages": [{"type": "path", "scope": "", "name": "retained_dep",
                              "manifestFile": "lake-manifest.json", "inherited": False,
                              "dir": "../producer", "configFile": "lakefile.lean"}],
                "name": "retained_consumer", "lakeDir": ".lake",
                "fixedToolchain": False}
    (cons / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return prod, cons


def copy_source_control(src, dst):
    dst.mkdir(parents=True, exist_ok=False)
    shutil.copy2(src / "source.json", dst / "source.json")
    for name in ("producer", "consumer"):
        shutil.copytree(src / name, dst / name,
                        ignore=shutil.ignore_patterns(".lake"))


def pid_alive(pid):
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lake", type=Path, required=True)
    ap.add_argument("--lean", type=Path, required=True)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    a.work = a.work.resolve()
    a.out = a.out.resolve()
    a.work.mkdir(parents=True, exist_ok=False)
    a.out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN, LEAN_NUM_THREADS="1",
               LAKE_CACHE_DIR="", LAKE_ARTIFACT_CACHE="false",
               MATHLIB_NO_CACHE_ON_UPDATE="1")
    env["PATH"] = str(a.lake.parent) + os.pathsep + env.get("PATH", "")
    results = {"lake_sha256": sha(a.lake), "lean_sha256": sha(a.lean),
               "toolchain": TOOLCHAIN, "runs": [], "observations": {}}

    def lake(label, cwd, args):
        argv = [str(a.lake), "--keep-toolchain", "--no-cache", *args]
        t = time.monotonic()
        p = subprocess.run(argv, cwd=cwd, env=env, capture_output=True,
                           text=True, timeout=15)
        r = {"label": label, "cwd": str(cwd.relative_to(a.work)),
             "args": argv[1:], "exit": p.returncode,
             "seconds": round(time.monotonic() - t, 3),
             "stdout": p.stdout, "stderr": p.stderr}
        results["runs"].append(r)
        return r

    # Build 16 generations serially. Their source/control and compiled states
    # are retained under separate roots for a 1/2/4/8/16 logical sweep.
    baseline = a.work / "baseline"
    baseline.mkdir()
    for value in range(1, 17):
        prod, cons = make(baseline / str(value), value)
        lake(f"generation-{value}-build", cons, ["build", "Generated"])
        results["observations"][f"generation-{value}"] = {
            "source_sha256": sha(prod / "Dep.lean"),
            "olean_sha256": sha(prod / ".lake/build/lib/lean/Dep.olean"),
            "baseline_bill": bill(baseline / str(value)),
        }

    retained = a.work / "retained"
    for tier in ("source-only", "generated", "compiled"):
        (retained / tier).mkdir(parents=True)
        for value in range(1, 17):
            src = baseline / str(value)
            dst = retained / tier / str(value)
            if tier == "source-only":
                dst.mkdir()
                shutil.copy2(src / "source.json", dst / "source.json")
            elif tier == "generated":
                copy_source_control(src, dst)
            else:
                shutil.copytree(src, dst)
    sweep = {}
    for tier in ("source-only", "generated", "compiled"):
        sweep[tier] = {}
        for count in (1, 2, 4, 8, 16):
            files = {}
            for value in range(17 - count, 17):
                for name, obj in inventory(retained / tier / str(value)).items():
                    files[f"{value}/{name}"] = obj
            sweep[tier][str(count)] = {
                "files": len(files),
                "logical_bytes": sum(x["bytes"] for x in files.values()),
                "blocks_bytes": sum(x["blocks_bytes"] for x in files.values()),
            }
    results["observations"]["retention_sweep"] = sweep

    # Reconstruct an old historical generation and the current one from each
    # tier in fresh directories. Build results include actual theorem checking.
    reconstruction = {}
    for value in (1, 16):
        reconstruction[str(value)] = {}
        for tier in ("source-only", "generated", "compiled"):
            src = retained / tier / str(value)
            dst = a.work / "reconstructed" / tier / str(value)
            dst.parent.mkdir(parents=True, exist_ok=True)
            started = time.monotonic()
            if tier == "source-only":
                v = json.loads((src / "source.json").read_text())["value"]
                make(dst, v)
            else:
                shutil.copytree(src, dst)
            materialize_sec = time.monotonic() - started
            cons = dst / "consumer"
            if tier == "compiled":
                pre = lake(f"reconstruct-{value}-{tier}-no-build", cons,
                           ["--no-build", "build", "Dep"])
            else:
                pre = lake(f"reconstruct-{value}-{tier}-build", cons,
                           ["build", "Generated"])
            query = lake(f"reconstruct-{value}-{tier}-query", cons,
                         ["env", "lean", "--json", "Generated.lean"])
            reconstruction[str(value)][tier] = {
                "materialize_seconds": round(materialize_sec, 4),
                "prepare_exit": pre["exit"], "prepare_seconds": pre["seconds"],
                "query_exit": query["exit"], "query_seconds": query["seconds"],
                "disk_after": bill(dst),
                "import_olean_sha256": sha(dst / "producer/.lake/build/lib/lean/Dep.olean"),
            }
    results["observations"]["reconstruction"] = reconstruction

    # One live reader imports a retained OLean, pauses after import, then the
    # owned generation is deleted. A new process with the same LEAN_PATH is the
    # negative control. An unrelated active generation has a sentinel.
    live = a.work / "live"
    live.mkdir()
    shutil.copytree(retained / "compiled" / "1", live / "retiring-1")
    shutil.copytree(retained / "compiled" / "16", live / "active-16")
    sentinel = live / "active-16" / "ACTIVE-SENTINEL"
    sentinel.write_text("keep generation 16\n")
    marker = live / "reader-entered"
    query_file = live / "Historical.lean"
    query_file.write_text(
        "import Lean\nimport Dep\nrun_cmd do\n"
        f'  let _ ← IO.FS.writeFile "{marker}" "entered"\n'
        "  let _ ← IO.sleep 1500\n#eval depValue\n")
    read_env = dict(env, LEAN_PATH=str(live / "retiring-1/producer/.lake/build/lib/lean"))
    t = time.monotonic()
    reader = subprocess.Popen([str(a.lean), "--json", str(query_file)],
                              cwd=live, env=read_env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    while not marker.exists() and reader.poll() is None and time.monotonic() - t < 5:
        time.sleep(0.02)
    marker_seen = marker.exists()
    rss_kib = None
    if marker_seen:
        try:
            rss_text = subprocess.run(["ps", "-o", "rss=", "-p", str(reader.pid)],
                                      text=True, capture_output=True,
                                      timeout=2).stdout.strip()
            rss_kib = int(rss_text)
        except (ValueError, OSError, subprocess.TimeoutExpired):
            pass
        shutil.rmtree(live / "retiring-1")
    out, err = reader.communicate(timeout=5)
    results["runs"].append({"label": "live-reader-after-retire",
                            "args": ["--json", "Historical.lean"],
                            "exit": reader.returncode, "stdout": out, "stderr": err,
                            "seconds": round(time.monotonic() - t, 3)})
    fresh = subprocess.run([str(a.lean), "--json", str(query_file)],
                           cwd=live, env=read_env, text=True,
                           capture_output=True, timeout=5)
    results["runs"].append({"label": "fresh-reader-after-retire",
                            "args": ["--json", "Historical.lean"],
                            "exit": fresh.returncode, "stdout": fresh.stdout,
                            "stderr": fresh.stderr})
    results["observations"]["live_reader"] = {
        "marker_seen": marker_seen, "sampled_rss_kib": rss_kib,
        "retired_generation_absent": not (live / "retiring-1").exists(),
        "active_sentinel_unchanged": sentinel.read_text() == "keep generation 16\n",
    }

    # Owned staging cleanup with a dead process, a live process, and an
    # incomplete stage lacking an owner. This is a policy model, not Lake GC.
    stages = a.work / "stages"
    stages.mkdir()
    live_owner = subprocess.Popen(["sleep", "10"])
    dead_owner = subprocess.Popen(["sleep", "10"])
    dead_owner.kill()
    dead_owner.wait(timeout=2)
    for name, owner in (("active", live_owner.pid), ("orphan", dead_owner.pid),
                        ("incomplete", None)):
        d = stages / name
        d.mkdir()
        (d / "partial.olean").write_text("incomplete\n")
        (d / "owner.json").write_text(json.dumps({"pid": owner}) + "\n")
    removed = []
    preserved = []
    for d in sorted(stages.iterdir()):
        owner = json.loads((d / "owner.json").read_text())["pid"]
        if owner is None or not pid_alive(owner):
            shutil.rmtree(d)
            removed.append(d.name)
        else:
            preserved.append(d.name)
    live_owner.terminate()
    live_owner.wait(timeout=2)
    results["observations"]["staging_cleanup"] = {
        "removed": removed, "preserved": preserved,
        "active_sentinel_unchanged": sentinel.read_text() == "keep generation 16\n",
        "stage_bill_after": bill(stages),
    }

    # Explicit bounded-handle policy model: retain last four, refuse older
    # handle 1 even though source bytes exist in a separate full archive.
    retained_handles = set(range(13, 17))
    results["observations"]["handle_policy_model"] = {
        str(value): "served" if value in retained_handles else "refused-expired"
        for value in (1, 13, 16)}
    (a.out / "results.json").write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
