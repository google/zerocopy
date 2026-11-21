#!/usr/bin/env python3
"""Execution probe for Lake v4.35.0 LAKE_CACHE_DIR read-only vs read-write behavior under bwrap."""
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

_default_lake = shutil.which("lake")
TOOLCHAIN_BIN = Path(
    os.environ.get(
        "LEAN_TOOLCHAIN_BIN",
        str(Path(_default_lake).resolve().parent)
        if _default_lake
        else str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0/bin"),
    )
)
LAKE = str(TOOLCHAIN_BIN / "lake")
LEAN = str(TOOLCHAIN_BIN / "lean")
OUT_JSON = Path(os.environ.get("PROBE_OUT_JSON", str(Path(__file__).resolve().parent / "probe_results.json")))


def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def tree_inventory(root: Path) -> dict:
    inv = {}
    if not root.exists():
        return inv
    for p in sorted(root.rglob("*")):
        rel = str(p.relative_to(root))
        if p.is_file():
            st = p.stat()
            inv[rel] = {"size": st.st_size, "sha256": sha256_file(p), "ino": st.st_ino, "nlink": st.st_nlink}
    return inv


def create_project(dest: Path, leaf_val: int = 42):
    dest.mkdir(parents=True, exist_ok=True)
    (dest / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
    (dest / "lakefile.toml").write_text(
        'name = "cacheprobe"\n'
        'defaultTargets = ["CacheProbe"]\n\n'
        '[[lean_lib]]\n'
        'name = "CacheProbe"\n'
    )
    (dest / "CacheProbe").mkdir(exist_ok=True)
    (dest / "CacheProbe" / "Base.lean").write_text(
        "namespace CacheProbe\ndef baseVal : Nat := 100\nend CacheProbe\n"
    )
    (dest / "CacheProbe" / "Leaf.lean").write_text(
        f"import CacheProbe.Base\nnamespace CacheProbe\ndef leafVal : Nat := baseVal + {leaf_val}\nend CacheProbe\n"
    )
    (dest / "CacheProbe.lean").write_text(
        "import CacheProbe.Base\nimport CacheProbe.Leaf\n"
    )


def run_lake_bwrap(proj: Path, cache_host: Path, cache_ro: bool, env_extra: dict):
    cache_mount = "/tmp/ro-cache" if cache_ro else "/tmp/rw-cache"
    cmd = [
        "bwrap",
        "--ro-bind", "/", "/",
        "--dev", "/dev",
        "--proc", "/proc",
        "--tmpfs", "/tmp",
        "--bind", str(proj), "/tmp/work",
        "--ro-bind" if cache_ro else "--bind", str(cache_host), cache_mount,
        "--chdir", "/tmp/work",
        "--",
        LAKE, "build", "-v", "--no-ansi",
    ]
    env = {
        "PATH": f"{TOOLCHAIN_BIN}:/usr/bin:/bin",
        "HOME": "/tmp/home",
        "LAKE_CACHE_DIR": cache_mount,
        "LEAN_NUM_THREADS": "1",
    }
    env.update(env_extra)
    t0 = time.monotonic()
    r = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=60)
    dt = round(time.monotonic() - t0, 3)
    return {
        "returncode": r.returncode,
        "elapsed_s": dt,
        "stdout": r.stdout,
        "stderr": r.stderr,
    }


def main():
    ver_lean = subprocess.run([LEAN, "--version"], capture_output=True, text=True, check=True).stdout.strip()
    ver_lake = subprocess.run([LAKE, "--version"], capture_output=True, text=True, check=True).stdout.strip()
    results = {
        "lean_version": ver_lean,
        "lake_version": ver_lake,
        "cases": {},
    }

    with tempfile.TemporaryDirectory(prefix="lake-ro-probe-") as td:
        tmp = Path(td)
        cache_dir = tmp / "cache"
        cache_dir.mkdir()

        # Case 1: Producer build (RW cache, LAKE_ARTIFACT_CACHE=true)
        p1 = tmp / "p1_producer"
        create_project(p1, leaf_val=42)
        res1 = run_lake_bwrap(p1, cache_dir, cache_ro=False, env_extra={"LAKE_ARTIFACT_CACHE": "true", "LAKE_NO_CACHE": "true"})
        cache_inv_after_1 = tree_inventory(cache_dir)
        results["cases"]["1_producer_rw_writable"] = {
            "returncode": res1["returncode"],
            "elapsed_s": res1["elapsed_s"],
            "cache_file_count": len(cache_inv_after_1),
            "cache_outputs": sorted(k for k in cache_inv_after_1 if k.startswith("outputs/")),
            "stdout_lines": res1["stdout"].splitlines(),
            "stderr_lines": res1["stderr"].splitlines(),
        }

        # Case 2: RO cache, LAKE_ARTIFACT_CACHE unset (default readable=true, writable=false), LAKE_NO_CACHE=true, 100% hit
        p2 = tmp / "p2_ro_default_hit"
        create_project(p2, leaf_val=42)
        res2 = run_lake_bwrap(p2, cache_dir, cache_ro=True, env_extra={"LAKE_NO_CACHE": "true"})
        p2_oleans = sorted(str(x.relative_to(p2)) for x in (p2 / ".lake/build").rglob("*.olean")) if (p2 / ".lake/build").exists() else []
        results["cases"]["2_ro_default_full_hit"] = {
            "returncode": res2["returncode"],
            "elapsed_s": res2["elapsed_s"],
            "cache_unchanged": tree_inventory(cache_dir) == cache_inv_after_1,
            "restored_oleans_in_build": p2_oleans,
            "hardlink_fallback_seen": "could not hard link artifact, copying from cache instead" in (res2["stdout"] + res2["stderr"]),
            "stdout_lines": res2["stdout"].splitlines(),
            "stderr_lines": res2["stderr"].splitlines(),
        }

        # Case 3: RO cache, LAKE_ARTIFACT_CACHE unset (default), PARTIAL HIT (Leaf.lean modified!)
        p3 = tmp / "p3_ro_default_leaf_miss"
        create_project(p3, leaf_val=99)
        res3 = run_lake_bwrap(p3, cache_dir, cache_ro=True, env_extra={"LAKE_NO_CACHE": "true"})
        results["cases"]["3_ro_default_leaf_miss"] = {
            "returncode": res3["returncode"],
            "elapsed_s": res3["elapsed_s"],
            "cache_unchanged": tree_inventory(cache_dir) == cache_inv_after_1,
            "stdout_lines": res3["stdout"].splitlines(),
            "stderr_lines": res3["stderr"].splitlines(),
        }

        # Case 4: RO cache, LAKE_ARTIFACT_CACHE=true (writable=true), PARTIAL HIT (Leaf.lean modified!) -> expect crash!
        p4 = tmp / "p4_ro_writable_leaf_miss"
        create_project(p4, leaf_val=99)
        res4 = run_lake_bwrap(p4, cache_dir, cache_ro=True, env_extra={"LAKE_ARTIFACT_CACHE": "true", "LAKE_NO_CACHE": "true"})
        results["cases"]["4_ro_writable_leaf_miss"] = {
            "returncode": res4["returncode"],
            "elapsed_s": res4["elapsed_s"],
            "cache_unchanged": tree_inventory(cache_dir) == cache_inv_after_1,
            "stdout_lines": res4["stdout"].splitlines(),
            "stderr_lines": res4["stderr"].splitlines(),
        }

        # Case 5: RO cache, LAKE_ARTIFACT_CACHE=true (writable=true), 100% hit
        p5 = tmp / "p5_ro_writable_full_hit"
        create_project(p5, leaf_val=42)
        res5 = run_lake_bwrap(p5, cache_dir, cache_ro=True, env_extra={"LAKE_ARTIFACT_CACHE": "true", "LAKE_NO_CACHE": "true"})
        p5_oleans = sorted(str(x.relative_to(p5)) for x in (p5 / ".lake/build").rglob("*.olean")) if (p5 / ".lake/build").exists() else []
        p5_ileans = sorted(str(x.relative_to(p5)) for x in (p5 / ".lake/build").rglob("*.ilean")) if (p5 / ".lake/build").exists() else []
        results["cases"]["5_ro_writable_full_hit"] = {
            "returncode": res5["returncode"],
            "elapsed_s": res5["elapsed_s"],
            "cache_unchanged": tree_inventory(cache_dir) == cache_inv_after_1,
            "restored_oleans_in_build": p5_oleans,
            "restored_ileans_in_build": p5_ileans,
            "stdout_lines": res5["stdout"].splitlines(),
            "stderr_lines": res5["stderr"].splitlines(),
        }

        # Case 6: RW cache, LAKE_ARTIFACT_CACHE=true, PARTIAL HIT (Leaf.lean modified!) -> Base hit, Leaf built & published
        p6 = tmp / "p6_rw_writable_leaf_miss"
        create_project(p6, leaf_val=99)
        res6 = run_lake_bwrap(p6, cache_dir, cache_ro=False, env_extra={"LAKE_ARTIFACT_CACHE": "true", "LAKE_NO_CACHE": "true"})
        cache_inv_after_6 = tree_inventory(cache_dir)
        results["cases"]["6_rw_writable_leaf_miss"] = {
            "returncode": res6["returncode"],
            "elapsed_s": res6["elapsed_s"],
            "cache_files_before": len(cache_inv_after_1),
            "cache_files_after": len(cache_inv_after_6),
            "new_cache_outputs": sorted(set(k for k in cache_inv_after_6 if k.startswith("outputs/")) - set(k for k in cache_inv_after_1 if k.startswith("outputs/"))),
            "stdout_lines": res6["stdout"].splitlines(),
            "stderr_lines": res6["stderr"].splitlines(),
        }

    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.write_text(json.dumps(results, indent=2))
    print(f"Wrote {OUT_JSON}")
    for k, v in results["cases"].items():
        print(f"  {k}: rc={v['returncode']} dt={v['elapsed_s']}s")


if __name__ == "__main__":
    main()
