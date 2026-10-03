#!/usr/bin/env python3
"""Optional tiny runtime replay of the RC2 external-SDK canary.

Requires a matching installed Lean/Lake v4.30.0-rc2 sysroot and a fresh scratch
directory on a POSIX filesystem with symlinks. No network or archive download.
The script writes only inside --scratch, except for reads of --lean-root.
This can launch about twenty small Lean/Lake processes; it is never run by
support/check.py and needs explicit --run. See REPORT.md for interpretation.
"""

import argparse
import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIXTURES = HERE / "fixtures"
REVISION = "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc"


def write(path, content):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)


def fixture(name):
    return (FIXTURES / name).read_text()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def setup_sdk(root, version):
    write(root / "lean-toolchain", "leanprover/lean4:v4.30.0-rc2\n")
    write(root / "lakefile.lean", fixture("sdk-lakefile.lean"))
    write(root / "Sdk.lean", fixture(f"Sdk-{version}.lean"))


def setup_consumer(root, identity=False):
    write(root / "lean-toolchain", "leanprover/lean4:v4.30.0-rc2\n")
    write(root / "lakefile.lean", fixture(
        "consumer-identity-lakefile.lean" if identity else "consumer-lakefile.lean"))
    write(root / "Client.lean", fixture(
        "Client-identity.lean" if identity else "Client.lean"))
    write(root / "Inspect.lean", fixture("Inspect.lean"))
    if identity:
        write(root / "SdkIdentity.lean", fixture("SdkIdentity-v1.lean"))


def freeze(root):
    for base, dirs, files in os.walk(root):
        for name in dirs + files:
            path = Path(base) / name
            if not path.is_symlink():
                path.chmod(stat.S_IMODE(path.stat().st_mode) & ~0o222)
    root.chmod(stat.S_IMODE(root.stat().st_mode) & ~0o222)


def overlay(view, toolchain, sdk, copy_lean, copy_lake):
    (view / "bin").mkdir(parents=True)
    (view / "lib/lean").mkdir(parents=True)
    for part in toolchain.iterdir():
        if part.name not in ("bin", "lib"):
            (view / part.name).symlink_to(part, target_is_directory=part.is_dir())
    for part in (toolchain / "bin").iterdir():
        target = view / "bin" / part.name
        if part.name in ("lean", "lake") and (
                (part.name == "lean" and copy_lean) or
                (part.name == "lake" and copy_lake)):
            shutil.copy2(part, target)
        else:
            target.symlink_to(part, target_is_directory=part.is_dir())
    for part in (toolchain / "lib").iterdir():
        if part.name != "lean":
            (view / "lib" / part.name).symlink_to(part,
                target_is_directory=part.is_dir())
    for part in (toolchain / "lib/lean").iterdir():
        (view / "lib/lean" / part.name).symlink_to(part,
            target_is_directory=part.is_dir())
    for part in (sdk / ".lake/build/lib/lean").glob("Sdk.*"):
        target = view / "lib/lean" / part.name
        if target.exists() or target.is_symlink():
            raise RuntimeError(f"SDK module name collides with toolchain: {part.name}")
        target.symlink_to(part)
    freeze(view)


def env_for(root, scratch, external_lean_path=None):
    env = os.environ.copy()
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "CI", "ELAN_TOOLCHAIN"):
        env.pop(key, None)
    env.update({
        "LEAN_SYSROOT": str(root),
        "LAKE_OVERRIDE_LEAN": "true",
        "PATH": str(root / "bin") + os.pathsep + env.get("PATH", ""),
        "DYLD_LIBRARY_PATH": str(root / "lib") + os.pathsep + str(root / "lib/lean"),
        "LAKE_CACHE_DIR": "",
        "LAKE_ARTIFACT_CACHE": "false",
        "LAKE_RESTORE_ARTIFACTS": "false",
        "LEAN_NUM_THREADS": "1",
        "HOME": str(scratch / "home"),
    })
    if external_lean_path:
        env["LEAN_PATH"] = str(external_lean_path)
    (scratch / "home").mkdir(exist_ok=True)
    return env


def command(label, binary, args, cwd, env, scratch):
    proc = subprocess.run([str(binary), *args], cwd=cwd, env=env,
                          text=True, capture_output=True, timeout=90)
    record = {"label": label, "exit": proc.returncode,
              "cmd": [str(binary), *args],
              "stdout": proc.stdout, "stderr": proc.stderr}
    (scratch / f"{label}.json").write_text(json.dumps(record, indent=2) + "\n")
    print(label, "exit", proc.returncode, flush=True)
    return record


def lake(label, view, args, work, scratch, external_lean_path=None):
    return command(label, view / "bin/lake",
                   ["--keep-toolchain", "--no-cache", *args], work,
                   env_for(view, scratch, external_lean_path), scratch)


def expect(result, exit_code, fragment=None):
    assert result["exit"] == exit_code, (result["label"], result["exit"])
    if fragment is not None:
        assert fragment in result["stdout"] + result["stderr"], result["label"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-root", type=Path, required=True)
    parser.add_argument("--scratch", type=Path, required=True)
    parser.add_argument("--run", action="store_true",
                        help="actually launch the small compiler matrix")
    ns = parser.parse_args()
    toolchain, scratch = ns.lean_root.resolve(), ns.scratch.absolute()
    if not ns.run:
        print("Dry run only. Add --run after checking free resources and scratch path.")
        return
    if scratch.exists():
        parser.error("--scratch must not exist; refusing to overwrite")
    if not (toolchain / "bin/lean").is_file() or not (toolchain / "bin/lake").is_file():
        parser.error("--lean-root must contain bin/lean and bin/lake")
    githash = subprocess.run([str(toolchain / "bin/lean"), "--githash"],
                            text=True, capture_output=True, check=True).stdout.strip()
    if githash != REVISION:
        parser.error(f"requires exact RC2 commit {REVISION}; got {githash}")
    scratch.mkdir(parents=True)
    sdk = {}
    for version in ("v1", "v2"):
        root = scratch / f"sdk-{version}"
        setup_sdk(root, version)
        result = lake(f"prepare-{version}", toolchain, ["build", "Sdk"], root, scratch)
        expect(result, 0)
        freeze(root)
        sdk[version] = root

    # LEAN_PATH works for `lake env`, but stock Lake's own module build drops it.
    external = sdk["v1"] / ".lake/build/lib/lean"
    plain = scratch / "plain-consumer"
    setup_consumer(plain)
    path = lake("external-path-env", toolchain,
                ["env", sys.executable, "-c", "import os; print(os.environ['LEAN_PATH'])"],
                plain, scratch, external)
    expect(path, 0, str(external))
    build = lake("external-path-build", toolchain,
                 ["--verbose", "build", "Client"], plain, scratch, external)
    expect(build, 1, "unknown module prefix 'Sdk'")

    views = {}
    for name, copy_lean, copy_lake in (("both-symlink", False, False),
                                       ("lean-only", True, False),
                                       ("coherent-v1", True, True)):
        view = scratch / name
        overlay(view, toolchain, sdk["v1"], copy_lean, copy_lake)
        views[name] = view
    view2 = scratch / "coherent-v2"
    overlay(view2, toolchain, sdk["v2"], True, True)

    for name in ("both-symlink", "lean-only", "coherent-v1"):
        work = scratch / (name + "-consumer")
        setup_consumer(work)
        prefix = lake(name + "-prefix", views[name],
                      ["env", "lean", "--print-prefix"], work, scratch)
        expect(prefix, 0)
        build = lake(name + "-build", views[name],
                     ["--verbose", "build", "Client"], work, scratch)
        expect(build, 1 if name == "both-symlink" else 0,
               "unknown module prefix 'Sdk'" if name == "both-symlink" else None)
        if name == "lean-only":
            assert prefix["stdout"].strip() == str(toolchain), prefix["stdout"]
            inspect = lake(name + "-inspect", views[name],
                           ["env", "lean", "Inspect.lean"], work, scratch)
            expect(inspect, 1, "unknown module prefix 'Sdk'")
        if name == "coherent-v1":
            assert prefix["stdout"].strip() == str(views[name]), prefix["stdout"]

    baseline = scratch / "coherent-v1-consumer"
    first = lake("baseline-v1-inspect", views["coherent-v1"],
                 ["env", "lean", "Inspect.lean"], baseline, scratch)
    expect(first, 0, "10\n10\ntrue\nclientProof")
    artifact = baseline / ".lake/build/lib/lean/Client.olean"
    before = (sha(artifact), artifact.stat().st_mtime_ns)
    second = lake("baseline-v2-build", view2,
                  ["--verbose", "build", "Client"], baseline, scratch)
    expect(second, 0)
    assert before == (sha(artifact), artifact.stat().st_mtime_ns), "Client changed on SDK switch"
    inspect = lake("baseline-v2-inspect", view2,
                   ["env", "lean", "Inspect.lean"], baseline, scratch)
    expect(inspect, 0, "10\n20\nfalse\nclientProof")

    root_name = scratch / "root-name-consumer"
    setup_consumer(root_name)
    expect(lake("root-name-v1", views["coherent-v1"],
                ["build", "Client"], root_name, scratch), 0)
    old = (root_name / "lakefile.lean").read_text()
    write(root_name / "lakefile.lean",
          old.replace("package probe_consumer", "package probe_consumer_renamed"))
    expect(lake("root-name-v2", view2,
                ["build", "Client"], root_name, scratch), 1, "is false")

    identity = scratch / "identity-consumer"
    setup_consumer(identity, identity=True)
    expect(lake("identity-v1", views["coherent-v1"],
                ["build", "Client"], identity, scratch), 0)
    write(identity / "SdkIdentity.lean", fixture("SdkIdentity-v2.lean"))
    expect(lake("identity-v2", view2,
                ["build", "Client"], identity, scratch), 1, "is false")

    expect(lake("baseline-clean", view2, ["clean"], baseline, scratch), 0)
    expect(lake("baseline-v2-after-clean", view2,
                ["build", "Client"], baseline, scratch), 1, "is false")
    print("replay matched the tiny external-SDK and invalidation observations")


if __name__ == "__main__":
    main()
