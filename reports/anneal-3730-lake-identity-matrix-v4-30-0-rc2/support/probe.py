#!/usr/bin/env python3
"""Small Lake cache ownership, package identity, and artifact-family matrix."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

TOOLCHAIN = "leanprover/lean4:v4.30.0-rc2"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inv(root):
    return {str(p.relative_to(root)): {"sha256": sha(p), "bytes": p.stat().st_size,
                                       "mtime_ns": p.stat().st_mtime_ns}
            for p in sorted(root.rglob("*")) if p.is_file()}


def make(base, name="consumer", package="probe_consumer", dep_dir="../producer",
         producer=True):
    prod = base / "producer"
    if producer:
        prod.mkdir(parents=True)
        (prod / "lakefile.lean").write_text(
            "import Lake\nopen Lake DSL\npackage probe_dep\n@[default_target]\nlean_lib Dep\n")
        (prod / "Dep.lean").write_text("def depValue : Nat := 7\n")
        (prod / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    c = base / name
    c.mkdir(parents=True)
    (c / "lakefile.lean").write_text(
        f'import Lake\nopen Lake DSL\nrequire probe_dep from "{dep_dir}"\n'
        f"package {package}\n@[default_target]\nlean_lib Generated\n")
    (c / "Generated.lean").write_text(
        "import Dep\ntheorem valueEq : depValue = 7 := by decide\n#eval depValue\n")
    (c / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    manifest = {"version": "1.2.0", "packagesDir": ".lake/packages",
                "packages": [{"type": "path", "scope": "", "name": "probe_dep",
                              "manifestFile": "lake-manifest.json", "inherited": False,
                              "dir": dep_dir, "configFile": "lakefile.lean"}],
                "name": package, "lakeDir": ".lake", "fixedToolchain": False}
    (c / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return prod, c


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
    results = {"toolchain": TOOLCHAIN, "lake_sha256": sha(a.lake),
               "lean_sha256": sha(a.lean), "runs": [], "observations": {}}
    base_env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN, LEAN_NUM_THREADS="1",
                    MATHLIB_NO_CACHE_ON_UPDATE="1")
    base_env["PATH"] = str(a.lake.parent) + os.pathsep + base_env.get("PATH", "")

    def run(label, cwd, args, cache_dir="", artifact_cache="false"):
        env = dict(base_env, LAKE_CACHE_DIR=str(cache_dir),
                   LAKE_ARTIFACT_CACHE=artifact_cache)
        argv = [str(a.lake), "--keep-toolchain", *args]
        t = time.monotonic()
        p = subprocess.run(argv, cwd=cwd, env=env, text=True,
                           capture_output=True, timeout=15)
        r = {"label": label, "cwd": str(cwd.relative_to(a.work)),
             "args": argv[1:], "cache_dir": str(cache_dir),
             "artifact_cache": artifact_cache, "exit": p.returncode,
             "seconds": round(time.monotonic() - t, 3),
             "stdout": p.stdout, "stderr": p.stderr}
        results["runs"].append(r)
        return r

    # A 2x2 cache location/policy matrix on separately constructed fixtures.
    for loc in ("local", "explicit"):
        for policy in ("false", "true"):
            label = f"cache-{loc}-{policy}"
            base = a.work / label
            dep, c = make(base)
            cache = "" if loc == "local" else (base / "explicit-cache")
            run(label + "-build", c, ["build", "Generated"], cache, policy)
            resolved = base / "consumer/.lake/cache" if loc == "local" else cache
            results["observations"][label] = {
                "resolved_cache": str(resolved.relative_to(a.work)),
                "cache_inventory": inv(resolved),
                "producer_inventory": inv(dep),
                "consumer_inventory": inv(c)}
            run(label + "-env", c, ["env", "printenv", "LAKE_CACHE_DIR"],
                cache, policy)

    # Source bytes change at the same path and mtime. Use the explicit-cache
    # true cell to observe a new producer input mapping after a real rebuild.
    source_base = a.work / "cache-explicit-true"
    source = source_base / "producer/Dep.lean"
    stat = source.stat()
    before_hash = sha(source)
    source.write_text("def depValue : Nat := 9\n")
    os.utime(source, ns=(stat.st_atime_ns, stat.st_mtime_ns))
    cache = source_base / "explicit-cache"
    results["observations"]["source_change"] = {
        "before_sha256": before_hash, "after_sha256": sha(source),
        "same_mtime_ns": source.stat().st_mtime_ns == stat.st_mtime_ns,
        "cache_before": inv(cache)}
    c = source_base / "consumer"
    run("source-change-no-build", c, ["--no-build", "build", "Dep"], cache, "true")
    run("source-change-rebuild-dep", c, ["build", "Dep"], cache, "true")
    results["observations"]["source_change"]["cache_after"] = inv(cache)

    # Same consumer pathname, changed root-package declaration and manifest.
    identity = a.work / "identity"
    dep, c = make(identity)
    run("identity-initial-build", c, ["build", "Generated"])
    initial_cfg = inv(c / ".lake/config")
    run("identity-initial-setup", c, ["setup-file", "Generated.lean"])
    lakefile = c / "lakefile.lean"
    manifest_path = c / "lake-manifest.json"
    old_lakefile_hash = sha(lakefile)
    lakefile.write_text(lakefile.read_text().replace("package probe_consumer",
                                                  "package probe_consumer_alt"))
    manifest = json.loads(manifest_path.read_text())
    manifest["name"] = "probe_consumer_alt"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    run("identity-changed-no-build", c, ["--no-build", "build", "Dep"])
    run("identity-changed-setup", c, ["setup-file", "Generated.lean"])
    results["observations"]["identity"] = {
        "same_consumer_path": str(c.relative_to(a.work)),
        "old_lakefile_sha256": old_lakefile_hash,
        "new_lakefile_sha256": sha(lakefile),
        "old_config_inventory": initial_cfg,
        "new_config_inventory": inv(c / ".lake/config"),
        "producer_inventory": inv(dep)}

    # Missing-artifact family controls. Each operation receives its own copy
    # of an intact built fixture, avoiding one operation repairing the next.
    family = a.work / "family-intact"
    dep, c = make(family)
    run("family-intact-build", c, ["build", "Generated"])
    operations = {
        "no-build": ["--no-build", "build", "Dep"],
        "setup": ["--no-build", "setup-file", "Generated.lean"],
        "json": ["env", "lean", "--json", "Generated.lean"],
    }
    run("family-intact-no-build", c, operations["no-build"])
    run("family-intact-setup", c, operations["setup"])
    run("family-intact-json", c, operations["json"])
    rels = {"olean": ".lake/build/lib/lean/Dep.olean",
            "ilean": ".lake/build/lib/lean/Dep.ilean",
            "trace": ".lake/build/lib/lean/Dep.trace",
            "c": ".lake/build/ir/Dep.c",
            "setup-json": ".lake/build/ir/Dep.setup.json"}
    for kind, rel in rels.items():
        for opname, args in operations.items():
            base = a.work / f"missing-{kind}-{opname}"
            shutil.copytree(family, base)
            target = base / "producer" / rel
            assert target.exists(), target
            target.unlink()
            run(f"missing-{kind}-{opname}", base / "consumer", args)
            results["observations"][f"missing-{kind}-{opname}"] = {
                "removed": rel, "producer_inventory_after": inv(base / "producer")}

    # Path alias: one physical producer reached by two consumer manifest paths.
    alias_base = a.work / "alias"
    alias_prod, original = make(alias_base, "consumer-direct")
    run("alias-prime", original, ["build", "Generated"])
    alias = alias_base / "producer-alias"
    alias.symlink_to(alias_prod, target_is_directory=True)
    _, via_alias = make(alias_base, "consumer-alias", producer=False,
                        dep_dir="../producer-alias")
    run("alias-direct-setup", original,
        ["--no-build", "setup-file", "Generated.lean"])
    run("alias-link-setup", via_alias,
        ["--no-build", "setup-file", "Generated.lean"])
    results["observations"]["alias"] = {
        "alias_target": str(alias.readlink()),
        "same_inode": alias.stat().st_ino == alias_prod.stat().st_ino,
        "producer_inventory": inv(alias_prod)}

    (a.out / "results.json").write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
