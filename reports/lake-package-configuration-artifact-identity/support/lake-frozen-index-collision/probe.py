#!/usr/bin/env python3
"""Tiny frozen producer with matching and shifted consumer graph identities."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

TOOLCHAIN = "leanprover/lean4:v4.30.0-rc2"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(path):
    return {str(p.relative_to(path)): [sha(p), p.stat().st_size, p.stat().st_mode & 0o777]
            for p in sorted(path.rglob("*")) if p.is_file()}


def manifest(name, deps):
    return {"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [
        {"type": "path", "scope": "", "name": n, "manifestFile": "lake-manifest.json",
         "inherited": False, "dir": rel, "configFile": "lakefile.lean"}
        for n, rel in deps], "name": name, "lakeDir": ".lake", "fixedToolchain": False}


def put(path, content):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)


def package(path, name, module, source):
    put(path / "lakefile.lean", f"import Lake\nopen Lake DSL\npackage {name}\n@[default_target]\nlean_lib {module}\n")
    put(path / f"{module}.lean", source)
    put(path / "lean-toolchain", TOOLCHAIN + "\n")
    put(path / "lake-manifest.json", json.dumps(manifest(name, []), indent=2) + "\n")


def consumer(path, deps):
    put(path / "lakefile.lean", "import Lake\nopen Lake DSL\n" +
        "".join(f'require {name} from "{rel}"\n' for name, rel in deps) +
        "package consumer\n@[default_target]\nlean_lib Generated\n")
    put(path / "Generated.lean", "import Dep\ntheorem checked : depValue = 7 := by decide\n#eval depValue\n")
    put(path / "lean-toolchain", TOOLCHAIN + "\n")
    put(path / "lake-manifest.json", json.dumps(manifest("consumer", deps), indent=2) + "\n")


def run(lake, home, cwd, label):
    env = dict(os.environ)
    env.update(ELAN_TOOLCHAIN=TOOLCHAIN, LEAN_NUM_THREADS="1", LAKE_ARTIFACT_CACHE="false",
               LAKE_NO_CACHE="1", HOME=str(home), XDG_CACHE_HOME=str(home / "cache"),
               PATH=str(lake.parent) + os.pathsep + env.get("PATH", ""))
    argv = [str(lake), "--keep-toolchain", "--no-cache", "--no-ansi", "-v", "build", "Generated"]
    p = subprocess.run(argv, cwd=cwd, env=env, capture_output=True, text=True, timeout=30)
    root = home.parent
    clean = lambda s: s.replace(str(root), "$WORK").replace(str(lake.parent), "$TOOLCHAIN_BIN")
    return {"label": label, "argv": argv[1:], "exit": p.returncode,
            "stdout": clean(p.stdout), "stderr": clean(p.stderr)}


def main():
    root, lake, output = map(Path, sys.argv[1:4])
    assert not root.exists() and lake.is_file()
    root.mkdir(parents=True)
    home = root / "home"
    home.mkdir()
    (home / "cache").mkdir()
    producer = root / "producer"
    dummy = root / "dummy"
    package(producer, "probe_dep", "Dep", "def depValue : Nat := 7\n")
    package(dummy, "dummy", "Extra", "def extraValue : Nat := 1\n")
    base = root / "base"
    match = root / "matching"
    shifted = root / "shifted"
    consumer(base, [("probe_dep", "../producer")])
    consumer(match, [("probe_dep", "../producer")])
    consumer(shifted, [("probe_dep", "../producer"), ("dummy", "../dummy")])
    records = [run(lake, home, base, "prime-index-1")]
    prime_trace = json.loads((producer / ".lake/config/probe_dep/lakefile.olean.trace").read_text())
    for p in sorted(producer.rglob("*"), reverse=True):
        if not p.is_symlink():
            p.chmod(0o555 if p.is_dir() else 0o444)
    producer.chmod(0o555)
    before = inventory(producer)
    records.append(run(lake, home, match, "frozen-matching-index-1"))
    after_match = inventory(producer)
    records.append(run(lake, home, shifted, "frozen-shifted-index-2"))
    after_shift = inventory(producer)
    shift_trace = json.loads((producer / ".lake/config/probe_dep/lakefile.olean.trace").read_text())
    for p in sorted(producer.rglob("*"), reverse=True):
        if not p.is_symlink():
            p.chmod(0o755 if p.is_dir() else 0o644)
    producer.chmod(0o755)
    records.append(run(lake, home, shifted, "writable-shifted-index-2"))
    writable_trace = json.loads((producer / ".lake/config/probe_dep/lakefile.olean.trace").read_text())
    data = {"lake_sha256": sha(lake), "lean_sha256": sha(lake.with_name("lean")),
            "producer_prime_trace": prime_trace,
            "producer_shift_trace": shift_trace, "producer_before": before,
            "producer_after_match": after_match, "producer_after_shift": after_shift,
            "producer_writable_trace": writable_trace,
            "producer_after_writable_shift": inventory(producer),
            "runs": records}
    output.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
