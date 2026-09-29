#!/usr/bin/env python3
"""Bounded Lean/Lake prepared-workspace and artifact-family contract probe."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
TOOLCHAIN = "leanprover/lean4:v4.30.0-rc2"
BASE = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin")
LAKE = BASE / "lake"
LEAN = BASE / "lean"
SANDBOX = Path("/usr/bin/sandbox-exec")
PROFILE = "(version 1) (allow default) (deny network*)"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(root):
    return {str(p.relative_to(root)): {"sha256": sha(p), "bytes": p.stat().st_size, "mode": oct(p.stat().st_mode & 0o777)}
            for p in sorted(root.rglob("*")) if p.is_file()}


def make(root, value=7, config="lean"):
    dep = root / "producer"
    consumer = root / "consumer"
    dep.mkdir(parents=True)
    consumer.mkdir(parents=True)
    if config == "lean":
        (dep / "lakefile.lean").write_text("import Lake\nopen Lake DSL\npackage probe_dep\n@[default_target]\nlean_lib Dep\n")
    else:
        (dep / "lakefile.toml").write_text('name = "probe_dep"\ndefaultTargets = ["Dep"]\n[[lean_lib]]\nname = "Dep"\n')
    (dep / "Dep.lean").write_text(f"def depValue : Nat := {value}\n")
    (dep / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    (consumer / "lakefile.lean").write_text('import Lake\nopen Lake DSL\nrequire probe_dep from "../producer"\npackage probe_consumer\n@[default_target]\nlean_lib Generated\n')
    (consumer / "Generated.lean").write_text(f"import Dep\ntheorem generatedEq : depValue + 1 = {value + 1} := by decide\n#print axioms generatedEq\n#eval depValue + 1\n")
    (consumer / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    (consumer / "lake-manifest.json").write_text(json.dumps({"version": "1.2.0", "packagesDir": ".lake/packages",
         "packages": [{"type": "path", "scope": "", "name": "probe_dep", "manifestFile": "lake-manifest.json",
                       "inherited": False, "dir": "../producer", "configFile": f"lakefile.{config}"}],
         "name": "probe_consumer", "lakeDir": ".lake", "fixedToolchain": False}, indent=2) + "\n")
    return dep, consumer


def freeze(root):
    for p in sorted(root.rglob("*"), reverse=True):
        if p.is_file():
            p.chmod(0o444)
        elif p.is_dir():
            p.chmod(0o555)
    root.chmod(0o555)


def thaw(root):
    for p in sorted(root.rglob("*")):
        if p.is_dir():
            p.chmod(0o755)
        elif p.is_file():
            p.chmod(0o644)
    root.chmod(0o755)


def run(records, label, cwd, argv, work, env, timeout=25):
    start = time.monotonic()
    try:
        p = subprocess.run([str(x) for x in argv], cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
        code, stdout, stderr = p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired as e:
        code = "timeout"
        stdout = e.stdout.decode(errors="replace") if isinstance(e.stdout, bytes) else e.stdout or ""
        stderr = e.stderr.decode(errors="replace") if isinstance(e.stderr, bytes) else e.stderr or ""
    canon = lambda s: s.replace(str(work), "$WORK").replace(str(BASE.parent), "$TOOLCHAIN")
    record = {"label": label, "cwd": canon(str(cwd)), "argv": [canon(str(x)) for x in argv],
              "exit": code, "seconds": round(time.monotonic() - start, 4),
              "stdout": canon(stdout), "stderr": canon(stderr)}
    records.append(record)
    return record


def env_for(work, cache=None):
    env = dict(os.environ)
    env.update({"ELAN_TOOLCHAIN": TOOLCHAIN, "LEAN_NUM_THREADS": "1", "MATHLIB_NO_CACHE_ON_UPDATE": "1",
                "HOME": str(work / "empty-home"), "LAKE_CACHE_DIR": "" if cache is None else str(cache),
                "LAKE_ARTIFACT_CACHE": "false" if cache is None else "true",
                "PATH": str(BASE) + os.pathsep + env.get("PATH", "")})
    return env


def lake(records, label, cwd, args, work, cache=None, offline=False):
    argv = [LAKE, "--keep-toolchain", *args]
    if offline:
        argv = [SANDBOX, "-p", PROFILE, *argv]
    return run(records, label, cwd, argv, work, env_for(work, cache))


def lean(records, label, cwd, args, work, cache=None):
    return lake(records, label, cwd, ["--no-cache", "env", "lean", *args], work, cache)


def cache_object(cache, pkg="probe_dep"):
    mapping = next((cache / "outputs" / pkg).glob("*.json"))
    document = json.loads(mapping.read_text())
    return mapping, cache / "artifacts" / document["data"]["o"][0]


def direct_loader(records, label, root, artifact, work):
    root.mkdir(parents=True)
    (root / "Dep.olean").symlink_to(artifact)
    env = env_for(work)
    env["LEAN_PATH"] = str(root)
    source = work / "Loader.lean"
    source.write_text("import Dep\n#eval depValue\n")
    return run(records, label, root, [LEAN, "--json", source], work, env)


def direct_proof_loader(records, label, root, source, work):
    env = env_for(work)
    env["LEAN_PATH"] = str(root)
    return run(records, label, source.parent, [LEAN, "--json", source], work, env)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--work", type=Path, required=True)
    args = ap.parse_args()
    work = args.work.resolve()
    if work.exists():
        raise SystemExit("choose a new absent --work path")
    if shutil.disk_usage(work.parent).free < 15 * (1 << 30):
        raise SystemExit("disk guard: less than 15 GiB free")
    work.mkdir(parents=True)
    (work / "empty-home").mkdir()
    records = []
    observations = {}
    try:
        # Executable Lean config and TOML config with the same declared package graph.
        clean_l_dep, clean_l_cons = make(work / "clean-lean", config="lean")
        clean_t_dep, clean_t_cons = make(work / "clean-toml", config="toml")
        for label, dep, cons in (("lean", clean_l_dep, clean_l_cons), ("toml", clean_t_dep, clean_t_cons)):
            lake(records, f"clean-{label}-build", cons, ["--no-cache", "build", "Generated"], work)
            lake(records, f"clean-{label}-setup", cons, ["--no-cache", "--no-build", "setup-file", "Generated.lean"], work)
            lean(records, f"clean-{label}-batch", cons, ["--json", "Generated.lean"], work)
            observations[f"clean-{label}-producer"] = inventory(dep)
            observations[f"clean-{label}-consumer"] = inventory(cons)

        # Native facet is a distinct target; the ordinary OLean consumer omits it.
        lake(records, "dynlib-build", clean_t_dep, ["--no-cache", "build", "+Dep:dynlib"], work)
        dylibs = sorted((clean_t_dep / ".lake/build").rglob("*.dylib"))
        observations["dynlibs"] = {str(p.relative_to(clean_t_dep)): {"sha256": sha(p), "bytes": p.stat().st_size} for p in dylibs}
        if dylibs:
            lean(records, "batch-with-dynlib", clean_t_cons, ["--load-dynlib", dylibs[0], "--json", "Generated.lean"], work)
            damaged = work / "bad-native.dylib"
            damaged.write_bytes(b"not a dynamic library\n")
            lean(records, "batch-with-bad-dynlib", clean_t_cons, ["--load-dynlib", damaged, "--json", "Generated.lean"], work)
            native_copy = work / "native-removed"
            shutil.copytree(work / "clean-toml", native_copy)
            copied_lib = native_copy / "producer" / dylibs[0].relative_to(clean_t_dep)
            copied_lib.unlink()
            lake(records, "native-missing-no-build", native_copy / "producer", ["--no-cache", "--no-build", "build", "+Dep:dynlib"], work)
            lean(records, "native-missing-batch-ordinary", native_copy / "consumer", ["--json", "Generated.lean"], work)

        # Move the prepared tree to a new depth and make the original unavailable.
        prepared = work / "different" / "depth" / "prepared"
        prepared.parent.mkdir(parents=True)
        shutil.copytree(work / "clean-lean", prepared)
        (work / "clean-lean").rename(work / "clean-lean-hidden")
        prod = prepared / "producer"
        cons = prepared / "consumer"
        freeze(prod)
        before = inventory(prod)
        consumer_before = inventory(cons)
        lake(records, "relocated-offline-no-build", cons, ["--no-cache", "--no-build", "build", "Dep"], work, offline=True)
        lake(records, "relocated-offline-setup", cons, ["--no-cache", "--no-build", "setup-file", "Generated.lean"], work, offline=True)
        lake(records, "relocated-offline-batch", cons, ["--no-cache", "env", "lean", "--json", "Generated.lean"], work, offline=True)
        observations["relocated_producer_unchanged"] = before == inventory(prod)
        observations["relocated_consumer_changed_paths"] = sorted(set(consumer_before) ^ set(inventory(cons)) |
            {k for k in consumer_before.keys() & inventory(cons).keys() if consumer_before[k] != inventory(cons)[k]})
        # The network-denial control must fail with EPERM rather than connection-refused.
        run(records, "network-denial-control", cons,
            [SANDBOX, "-p", PROFILE, "/usr/bin/python3", "-c", 'import socket; socket.socket().connect(("127.0.0.1", 1))'],
            work, env_for(work))

        # A source-only consumer cannot be built in a non-writable tree.
        readonly_root = work / "readonly-consumer"
        shutil.copytree(prepared, readonly_root)
        read_cons = readonly_root / "consumer"
        shutil.rmtree(read_cons / ".lake")
        freeze(read_cons)
        lake(records, "readonly-consumer-build", read_cons, ["--no-cache", "build", "Generated"], work)
        thaw(read_cons)

        # Two valid artifact caches for the same module but different definitions.
        cache7 = work / "cache7"
        cache9 = work / "cache9"
        _, c7 = make(work / "cache-seed7", value=7)
        _, c9 = make(work / "cache-seed9", value=9)
        lake(records, "cache7-build", c7, ["build", "Generated"], work, cache7)
        lake(records, "cache9-build", c9, ["build", "Generated"], work, cache9)
        mapping7, object7 = cache_object(cache7)
        mapping9, object9 = cache_object(cache9)
        observations["cache7_olean"] = {"mapping": str(mapping7.relative_to(work)), "artifact": str(object7.relative_to(work)), "sha256": sha(object7)}
        observations["cache9_olean"] = {"mapping": str(mapping9.relative_to(work)), "artifact": str(object9.relative_to(work)), "sha256": sha(object9)}
        direct_loader(records, "cache7-direct-loader", work / "loader7", object7, work)
        direct_loader(records, "cache9-direct-loader", work / "loader9", object9, work)
        wrong = work / "cache-wrong-valid"
        shutil.copytree(cache7, wrong)
        wrong_map, wrong_object = cache_object(wrong)
        wrong_object.chmod(0o644)
        wrong_object.write_bytes(object9.read_bytes())
        observations["wrong_valid_object"] = {"mapping": str(wrong_map.relative_to(work)), "artifact": str(wrong_object.relative_to(work)), "sha256": sha(wrong_object)}
        _, wrong_cons = make(work / "wrong-reconstruct", value=7)
        lake(records, "wrong-valid-cache-no-build", wrong_cons, ["--no-build", "build", "Dep"], work, wrong)
        lake(records, "wrong-valid-cache-setup", wrong_cons, ["--no-build", "setup-file", "Generated.lean"], work, wrong)
        direct_loader(records, "wrong-valid-direct-loader", work / "loader-wrong", wrong_object, work)
        direct_proof_loader(records, "wrong-valid-proof-against-7", work / "loader-wrong", wrong_cons / "Generated.lean", work)

        truncated = work / "cache-truncated-map"
        shutil.copytree(cache7, truncated)
        broken_map, _ = cache_object(truncated)
        broken_map.write_text('{"data":')
        _, bad_cons = make(work / "truncated-reconstruct", value=7)
        lake(records, "truncated-map-no-build", bad_cons, ["--no-build", "build", "Dep"], work, truncated)
        lake(records, "truncated-map-setup", bad_cons, ["--no-build", "setup-file", "Generated.lean"], work, truncated)

        by = {r["label"]: r for r in records}
        assert all(by[f"clean-{c}-{op}"]["exit"] == 0 for c in ("lean", "toml") for op in ("build", "setup", "batch"))
        assert all("does not depend on any axioms" in by[f"clean-{c}-batch"]["stdout"] for c in ("lean", "toml"))
        assert by["dynlib-build"]["exit"] == 0 and dylibs
        assert by["batch-with-dynlib"]["exit"] == 0 and by["batch-with-bad-dynlib"]["exit"] != 0
        assert by["native-missing-no-build"]["exit"] != 0 and by["native-missing-batch-ordinary"]["exit"] == 0
        assert all(by[k]["exit"] == 0 for k in ("relocated-offline-no-build", "relocated-offline-setup", "relocated-offline-batch"))
        assert observations["relocated_producer_unchanged"]
        assert by["network-denial-control"]["exit"] != 0 and "Operation not permitted" in by["network-denial-control"]["stderr"]
        assert by["readonly-consumer-build"]["exit"] != 0
        assert by["wrong-valid-cache-no-build"]["exit"] == 0 and by["wrong-valid-cache-setup"]["exit"] == 0
        assert by["wrong-valid-proof-against-7"]["exit"] != 0 and '"data":"10"' in by["wrong-valid-proof-against-7"]["stdout"]
        assert by["truncated-map-no-build"]["exit"] != 0 and by["truncated-map-setup"]["exit"] != 0
        evidence = HERE / "artifacts"
        if evidence.exists():
            shutil.rmtree(evidence)
        evidence.mkdir()
        specimens = {
            "cache7-Dep.olean": object7, "cache9-Dep.olean": object9,
            "cache7-output.json": mapping7, "cache9-output.json": mapping9,
            "toml-Dep.olean": clean_t_dep / ".lake/build/lib/lean/Dep.olean",
            "toml-Dep.ilean": clean_t_dep / ".lake/build/lib/lean/Dep.ilean",
            "toml-Dep.trace": clean_t_dep / ".lake/build/lib/lean/Dep.trace",
            "toml-Dep.c": clean_t_dep / ".lake/build/ir/Dep.c",
            "lean-config.olean": work / "clean-lean-hidden/producer/.lake/config/probe_dep/lakefile.olean",
            "Dep.dylib": dylibs[0],
        }
        for name, path in specimens.items():
            shutil.copy2(path, evidence / name)
        observations["preserved_artifacts"] = {name: {"sha256": sha(evidence / name), "bytes": (evidence / name).stat().st_size} for name in specimens}
        output = {"environment": {"platform": platform.platform(), "lake_sha256": sha(LAKE), "lean_sha256": sha(LEAN), "toolchain": TOOLCHAIN},
                  "runs": records, "observations": observations}
        (HERE / "results.json").write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
        print(json.dumps({"commands": len(records), "dynlibs": len(dylibs), "wrong_cache_sha256": sha(wrong_object),
                          "relocated_producer_unchanged": observations["relocated_producer_unchanged"]}, sort_keys=True))
    finally:
        for parent in (work / "different", work / "readonly-consumer"):
            if parent.exists():
                for p in parent.rglob("*"):
                    if p.is_dir():
                        p.chmod(0o755)


if __name__ == "__main__":
    main()
