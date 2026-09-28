#!/usr/bin/env python3
"""Bounded synthetic Lake cache and concurrency probe; no downloads."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT.parents[2]
BIN = PROJECT / ".anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin"
LAKE = BIN / "lake"
TOOLCHAIN = "leanprover/lean4:v4.30.0-rc2"
RUNS = []
ENV = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN, LEAN_NUM_THREADS="1", LAKE_CACHE_DIR="", MATHLIB_NO_CACHE_ON_UPDATE="1")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(path):
    return {str(p.relative_to(path)): {"sha256": sha(p), "bytes": p.stat().st_size, "mtime_ns": p.stat().st_mtime_ns}
            for p in sorted(path.rglob("*")) if p.is_file()}


def run(label, cwd, args):
    started = time.monotonic()
    p = subprocess.run([str(LAKE), *args], cwd=cwd, env=ENV, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
    result = {"label": label, "cwd": str(cwd), "argv": [str(LAKE), *args],
              "exit": p.returncode, "seconds": round(time.monotonic() - started, 3),
              "stdout": p.stdout, "stderr": p.stderr}
    RUNS.append(result)
    return result


def start(label, cwd, args):
    p = subprocess.Popen([str(LAKE), *args], cwd=cwd, env=ENV, text=True,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return label, cwd, args, p, time.monotonic()


def finish(item):
    label, cwd, args, p, started = item
    try:
        out, err = p.communicate(timeout=30)
    except subprocess.TimeoutExpired:
        p.kill()
        out, err = p.communicate()
        err += "\nTIMEOUT: killed after 30 seconds"
    result = {"label": label, "cwd": str(cwd), "argv": [str(LAKE), *args],
              "exit": p.returncode, "seconds": round(time.monotonic() - started, 3),
              "stdout": out, "stderr": err}
    RUNS.append(result)
    return result


def make_workspace(base, name, dep_source=True, dep_build=None):
    base.mkdir(parents=True, exist_ok=True)
    producer = base / "producer"
    consumer = base / name
    if dep_source:
        producer.mkdir(exist_ok=True)
        (producer / "lakefile.lean").write_text("import Lake\nopen Lake DSL\npackage probe_dep\n@[default_target]\nlean_lib Dep\n")
        (producer / "Dep.lean").write_text("def depValue : Nat := 7\n")
        (producer / "lean-toolchain").write_text(TOOLCHAIN + "\n")
        if dep_build is not None:
            shutil.copytree(dep_build, producer / ".lake", dirs_exist_ok=True)
    consumer.mkdir(exist_ok=True)
    (consumer / "lakefile.lean").write_text("import Lake\nopen Lake DSL\nrequire probe_dep from \"../producer\"\npackage probe_consumer\n@[default_target]\nlean_lib Generated\n")
    (consumer / "Generated.lean").write_text("import Dep\ntheorem generatedEq : depValue + 1 = 8 := by decide\n#eval depValue + 1\n")
    (consumer / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    manifest = {"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [
        {"type": "path", "scope": "", "name": "probe_dep", "manifestFile": "lake-manifest.json",
         "inherited": False, "dir": "../producer", "configFile": "lakefile.lean"}],
        "name": "probe_consumer", "lakeDir": ".lake", "fixedToolchain": False}
    (consumer / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return producer, consumer


def make_consumer(base, name):
    _, consumer = make_workspace(base, name, dep_source=False)
    return consumer


def freeze(path):
    for p in sorted(path.rglob("*"), reverse=True):
        if p.is_file():
            p.chmod(0o444)
        elif p.is_dir():
            p.chmod(0o555)
    path.chmod(0o555)


def main():
    clean_prod, clean = make_workspace(ROOT / "clean", "consumer")
    clean_manifest_hash = sha(clean / "lake-manifest.json")
    run("clean-build", clean, ["--keep-toolchain", "--no-cache", "--old", "build", "Generated"])
    (ROOT / "clean-inventory.json").write_text(json.dumps({"producer": inventory(clean_prod), "consumer": inventory(clean)}, indent=2))
    run("clean-setup", clean, ["--keep-toolchain", "--no-cache", "setup-file", "Generated.lean"])
    run("clean-lean-json", clean, ["--keep-toolchain", "--no-cache", "env", "lean", "--json", "Generated.lean"])

    seed_base = ROOT / "seeded"
    seed_prod, c1 = make_workspace(seed_base, "consumer-a", dep_build=clean_prod / ".lake")
    c2 = make_consumer(seed_base, "consumer-b")
    before = inventory(seed_prod)
    freeze(seed_prod)
    pair = [start("seeded-a-build", c1, ["--keep-toolchain", "--no-cache", "--old", "build", "Generated"]),
            start("seeded-b-build", c2, ["--keep-toolchain", "--no-cache", "--old", "build", "Generated"])]
    for item in pair:
        finish(item)
    after = inventory(seed_prod)
    run("seeded-a-setup", c1, ["--keep-toolchain", "--no-cache", "setup-file", "Generated.lean"])
    run("seeded-b-setup", c2, ["--keep-toolchain", "--no-cache", "setup-file", "Generated.lean"])
    (ROOT / "seeded-inventory.json").write_text(json.dumps({"producer_before": before, "producer_after": after,
        "consumer_a": inventory(c1), "consumer_b": inventory(c2)}, indent=2))

    race_prod, r1 = make_workspace(ROOT / "shared-writable", "consumer-a")
    r2 = make_consumer(ROOT / "shared-writable", "consumer-b")
    pair = [start("shared-writable-a", r1, ["--keep-toolchain", "--no-cache", "--old", "build", "Generated"]),
            start("shared-writable-b", r2, ["--keep-toolchain", "--no-cache", "--old", "build", "Generated"])]
    for item in pair:
        finish(item)
    (ROOT / "shared-writable-inventory.json").write_text(json.dumps({"producer": inventory(race_prod),
        "consumer_a": inventory(r1), "consumer_b": inventory(r2)}, indent=2))
    (ROOT / "runs.json").write_text(json.dumps({"env": {k: ENV[k] for k in ["ELAN_TOOLCHAIN", "LEAN_NUM_THREADS", "LAKE_CACHE_DIR", "MATHLIB_NO_CACHE_ON_UPDATE"]},
        "clean_manifest_sha256": clean_manifest_hash, "runs": RUNS}, indent=2))


if __name__ == "__main__":
    main()
