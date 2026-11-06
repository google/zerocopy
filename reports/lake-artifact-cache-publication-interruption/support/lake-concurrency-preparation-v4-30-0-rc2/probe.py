#!/usr/bin/env python3
"""Small bounded Lake preparation, relocation, cache, and consumer probe."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor

TOOLCHAIN = "leanprover/lean4:v4.30.0-rc2"


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def inventory(root):
    out = {}
    for p in sorted(root.rglob("*")):
        if p.is_file():
            st = p.stat()
            out[str(p.relative_to(root))] = {
                "sha256": digest(p), "bytes": st.st_size,
                "mtime_ns": st.st_mtime_ns, "mode": oct(st.st_mode & 0o777),
            }
    return out


def make(base, name="consumer", producer=True):
    dep = base / "producer"
    if producer:
        dep.mkdir(parents=True)
        (dep / "lakefile.lean").write_text(
            "import Lake\nopen Lake DSL\npackage probe_dep\n@[default_target]\nlean_lib Dep\n")
        (dep / "Dep.lean").write_text("def depValue : Nat := 7\n")
        (dep / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    c = base / name
    c.mkdir(parents=True)
    (c / "lakefile.lean").write_text(
        'import Lake\nopen Lake DSL\nrequire probe_dep from "../producer"\n'
        "package probe_consumer\n@[default_target]\nlean_lib Generated\n")
    (c / "Generated.lean").write_text(
        "import Dep\ntheorem generatedEq : depValue + 1 = 8 := by decide\n"
        "#eval depValue + 1\n")
    (c / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    manifest = {
        "version": "1.2.0", "packagesDir": ".lake/packages",
        "packages": [{"type": "path", "scope": "", "name": "probe_dep",
                      "manifestFile": "lake-manifest.json", "inherited": False,
                      "dir": "../producer", "configFile": "lakefile.lean"}],
        "name": "probe_consumer", "lakeDir": ".lake", "fixedToolchain": False,
    }
    (c / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return dep, c


def freeze(root):
    for p in sorted(root.rglob("*"), reverse=True):
        if p.is_file():
            p.chmod(0o444)
        elif p.is_dir():
            p.chmod(0o555)
    root.chmod(0o555)


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
    results = {"toolchain": TOOLCHAIN, "lake_sha256": digest(a.lake),
               "lean_sha256": digest(a.lean), "runs": [], "observations": {}}
    base_env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN, LEAN_NUM_THREADS="1",
                    MATHLIB_NO_CACHE_ON_UPDATE="1")
    base_env["PATH"] = str(a.lake.parent) + os.pathsep + base_env.get("PATH", "")

    def run(label, cwd, args, cache=None):
        env = base_env.copy()
        if cache is None:
            env["LAKE_CACHE_DIR"] = ""
            env["LAKE_ARTIFACT_CACHE"] = "false"
        else:
            env["LAKE_CACHE_DIR"] = str(cache)
            env["LAKE_ARTIFACT_CACHE"] = "true"
        argv = [str(a.lake), "--keep-toolchain", *args]
        t = time.monotonic()
        try:
            p = subprocess.run(argv, cwd=cwd, env=env, text=True,
                               capture_output=True, timeout=25)
            code, out, err = p.returncode, p.stdout, p.stderr
        except subprocess.TimeoutExpired as e:
            code = "timeout"
            out = (e.stdout or b"").decode(errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
            err = (e.stderr or b"").decode(errors="replace") if isinstance(e.stderr, bytes) else (e.stderr or "")
        r = {"label": label, "cwd": str(cwd.relative_to(a.work)),
             "args": argv[1:], "cache": str(cache.relative_to(a.work)) if cache else None,
             "exit": code, "seconds": round(time.monotonic() - t, 3),
             "stdout": out, "stderr": err}
        results["runs"].append(r)
        return r

    # Final-path preparation control. The old root is removed by rename before
    # the relocated commands, then the copy is frozen.
    original = a.work / "original"
    dep, c = make(original)
    run("original-build", c, ["--no-cache", "build", "Generated"])
    relocated = a.work / "other" / "depth" / "relocated"
    relocated.parent.mkdir(parents=True)
    shutil.copytree(original, relocated)
    original.rename(a.work / "original-inaccessible")
    relocated_dep = relocated / "producer"
    relocated_c = relocated / "consumer"
    freeze(relocated_dep)
    before = inventory(relocated_dep)
    run("relocated-no-build-hash", relocated_c,
        ["--no-cache", "--no-build", "build", "Dep"])
    run("relocated-no-build-old", relocated_c,
        ["--no-cache", "--old", "--no-build", "build", "Dep"])
    run("relocated-setup-no-build", relocated_c,
        ["--no-cache", "--no-build", "setup-file", "Generated.lean"])
    run("relocated-json", relocated_c,
        ["--no-cache", "env", "lean", "--json", "Generated.lean"])
    results["observations"]["relocated_producer_unchanged"] = before == inventory(relocated_dep)
    results["observations"]["relocated_producer_inventory"] = before

    # Minimum source/control plus an isolated artifact-cache candidate. The
    # clean cache build is deliberately distinct from the no-cache relocation.
    cache_root = a.work / "artifact-cache"
    cached = a.work / "cache-producer"
    dep_cache, c_cache = make(cached)
    run("cache-producer-build", c_cache, ["build", "Generated"], cache_root)
    cache_inventory_before = inventory(cache_root)
    reconstructed = a.work / "cache-reconstruction"
    dep_recon, c_recon = make(reconstructed)
    run("cache-reconstruction-no-build", c_recon,
        ["--no-build", "build", "Dep"], cache_root)
    run("cache-reconstruction-build", c_recon, ["build", "Generated"], cache_root)
    run("cache-reconstruction-setup", c_recon,
        ["--no-build", "setup-file", "Generated.lean"], cache_root)
    run("cache-reconstruction-json", c_recon,
        ["env", "lean", "--json", "Generated.lean"], cache_root)
    results["observations"]["cache_inventory_before"] = cache_inventory_before
    results["observations"]["cache_inventory_after"] = inventory(cache_root)
    results["observations"]["cache_reconstructed_producer"] = inventory(dep_recon)

    # Isolate damage to copied caches. A missing object tests ordinary recovery;
    # a present-but-bad object tests whether local resolution checks the bytes.
    dep_map = next((cache_root / "outputs" / "probe_dep").glob("*.json"))
    dep_olean_name = json.loads(dep_map.read_text())["data"]["o"][0]
    for damage in ("missing", "corrupt"):
        damaged_cache = a.work / f"cache-{damage}"
        shutil.copytree(cache_root, damaged_cache)
        artifact = damaged_cache / "artifacts" / dep_olean_name
        if damage == "missing":
            artifact.unlink()
        else:
            artifact.chmod(0o644)
            artifact.write_bytes(b"not an olean\n")
        _, damaged_consumer = make(a.work / f"reconstruct-{damage}")
        run(f"cache-{damage}-no-build", damaged_consumer,
            ["--no-build", "build", "Dep"], damaged_cache)
        run(f"cache-{damage}-setup", damaged_consumer,
            ["--no-build", "setup-file", "Generated.lean"], damaged_cache)
        run(f"cache-{damage}-json", damaged_consumer,
            ["env", "lean", "--json", "Generated.lean"], damaged_cache)
        results["observations"][f"cache-{damage}-artifact"] = dep_olean_name

    # Loader control: a symlink supplies the conventional module filename so
    # the actual Lean loader sees each cache object's bytes, unlike `lake env`
    # in this cache-writable fixture (which omits that conventional placement).
    for mode, cache_dir in (("clean", cache_root),
                            ("missing", a.work / "cache-missing"),
                            ("corrupt", a.work / "cache-corrupt")):
        shim = a.work / f"loader-{mode}"
        shim.mkdir()
        (shim / "Dep.olean").symlink_to(cache_dir / "artifacts" / dep_olean_name)
        env = base_env.copy()
        env["LEAN_PATH"] = str(shim)
        t = time.monotonic()
        p = subprocess.run([str(a.lean), "--json", "Generated.lean"],
                           cwd=c_recon, env=env, text=True, capture_output=True,
                           timeout=10)
        results["runs"].append({
            "label": f"loader-{mode}-json", "cwd": str(c_recon.relative_to(a.work)),
            "args": ["--json", "Generated.lean"],
            "lean_path": str(shim.relative_to(a.work)), "exit": p.returncode,
            "seconds": round(time.monotonic() - t, 3),
            "stdout": p.stdout, "stderr": p.stderr,
        })

    # Frozen producer with genuinely separate writable consumer trees. Sizes
    # 1, 2, 4 are bounded by the 8 GiB host; no general scaling claim follows.
    for n in (1, 2, 4):
        base = a.work / f"parallel-{n}"
        dep_n, primer = make(base, "primer")
        run(f"parallel-{n}-prepare-producer", primer,
            ["--no-cache", "build", "Generated"])
        shutil.rmtree(primer)
        _, c0 = make(base, "consumer-0", producer=False)
        consumers = [c0]
        for i in range(1, n):
            _, ci = make(base, f"consumer-{i}", producer=False)
            consumers.append(ci)
        freeze(dep_n)
        inv0 = inventory(dep_n)
        t = time.monotonic()
        with ThreadPoolExecutor(max_workers=n) as pool:
            futures = [pool.submit(run, f"parallel-{n}-consumer-{i}", ci,
                                   ["--no-cache", "build", "Generated"])
                       for i, ci in enumerate(consumers)]
            concurrent = [f.result() for f in futures]
        results["observations"][f"parallel-{n}"] = {
            "wall_seconds": round(time.monotonic() - t, 3),
            "all_success": all(r["exit"] == 0 for r in concurrent),
            "producer_unchanged": inv0 == inventory(dep_n),
            "consumer_bytes": [sum(x["bytes"] for x in inventory(ci).values())
                               for ci in consumers],
            "producer_bytes": sum(x["bytes"] for x in inv0.values()),
        }
    (a.out / "results.json").write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
