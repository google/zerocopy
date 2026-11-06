#!/usr/bin/env python3
"""Bounded, offline Lake consumer identity and action-observation matrix."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import threading
import time

TOOLCHAIN = "leanprover/lean4:v4.30.0-rc2"
REVISION = "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(root):
    if not root.exists():
        return {}
    return {str(p.relative_to(root)): [digest(p), p.stat().st_size, p.stat().st_mtime_ns]
            for p in sorted(root.rglob("*")) if p.is_file() and not p.is_symlink()}


def changes(before, after):
    return {"added": sorted(after.keys() - before.keys()),
            "removed": sorted(before.keys() - after.keys()),
            "content_changed": sorted(k for k in before.keys() & after.keys()
                                      if before[k][:2] != after[k][:2]),
            "mtime_only": sorted(k for k in before.keys() & after.keys()
                                 if before[k][:2] == after[k][:2] and before[k][2] != after[k][2])}


def config_traces(producer):
    return {str(p.relative_to(producer)): json.loads(p.read_text())
            for p in sorted((producer / ".lake/config").rglob("*.trace"))}


def manifest(name, dependencies):
    return {"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [
        {"type": "path", "scope": "", "name": depname,
         "manifestFile": "lake-manifest.json", "inherited": False,
         "dir": rel, "configFile": "lakefile.lean"}
        for depname, rel in dependencies], "name": name,
        "lakeDir": ".lake", "fixedToolchain": False}


def make_package(path, name, source):
    path.mkdir(parents=True)
    (path / "lakefile.lean").write_text(
        f"import Lake\nopen Lake DSL\npackage {name}\n@[default_target]\nlean_lib {source}\n")
    (path / f"{source}.lean").write_text(
        "def depValue : Nat := 7\n" if source == "Dep" else "def extraValue : Nat := 1\n")
    (path / "lean-toolchain").write_text(TOOLCHAIN + "\n")


def make_consumer(path, deps, *, server_option=False):
    path.mkdir(parents=True)
    reqs = "".join(f'require {name} from "{rel}"\n' for name, rel in deps)
    extra = " where\n  moreServerOptions := #[⟨`pp.universes, true⟩]" if server_option else ""
    (path / "lakefile.lean").write_text(
        f"import Lake\nopen Lake DSL\n{reqs}package consumer{extra}\n"
        "@[default_target]\nlean_lib Generated\n")
    (path / "Generated.lean").write_text(
        "import Dep\ntheorem depCheck : depValue = 7 := by decide\n")
    (path / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    (path / "lake-manifest.json").write_text(json.dumps(manifest("consumer", deps), indent=2) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lake", type=Path, required=True)
    ap.add_argument("--lean", type=Path, required=True)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    lake, lean, work = args.lake.resolve(), args.lean.resolve(), args.work.resolve()
    assert lake.is_file() and lean.is_file()
    assert not work.exists(), work
    work.mkdir(parents=True)
    out = {"toolchain": TOOLCHAIN, "revision": REVISION,
           "lake_sha256": digest(lake), "lean_sha256": digest(lean),
           "runs": [], "snapshots": {}}
    env = dict(os.environ)
    env.update(ELAN_TOOLCHAIN=TOOLCHAIN, LEAN_NUM_THREADS="1", LAKE_ARTIFACT_CACHE="false",
               LAKE_NO_CACHE="1", HOME=str(work / "home"),
               XDG_CACHE_HOME=str(work / "cache"))
    (work / "home").mkdir()
    (work / "cache").mkdir()
    env["PATH"] = str(lake.parent) + os.pathsep + env.get("PATH", "")

    def clean(text):
        return text.replace(str(work), "$WORK").replace(str(lake.parent), "$TOOLCHAIN_BIN")

    producer = work / "producer"
    dummy = work / "dummy"
    make_package(producer, "probe_dep", "Dep")
    make_package(dummy, "dummy", "Extra")
    (producer / "lake-manifest.json").write_text(json.dumps(manifest("probe_dep", []), indent=2) + "\n")
    (dummy / "lake-manifest.json").write_text(json.dumps(manifest("dummy", []), indent=2) + "\n")

    def run(label, cwd, opts, *, full_inventory=False):
        before = inventory(work)
        command = [str(lake), "--keep-toolchain", "--no-cache", "--no-ansi", "-v", *opts]
        t = time.monotonic()
        p = subprocess.Popen(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, text=True)
        sampled = []
        stop = threading.Event()
        trace_processes = label in {"base-build", "base-replay",
                                    "changed-source-build-rehash",
                                    "changed-source-post-build-replay"}

        def sample_descendants():
            while not stop.is_set():
                ps = subprocess.run(["ps", "-axo", "pid=,ppid=,comm="],
                                    capture_output=True, text=True, timeout=3)
                rows = []
                for line in ps.stdout.splitlines():
                    fields = line.strip().split(None, 2)
                    if len(fields) == 3 and fields[0].isdigit() and fields[1].isdigit():
                        rows.append((int(fields[0]), int(fields[1]), fields[2]))
                known = {p.pid}
                for _ in range(3):
                    known.update(pid for pid, ppid, _ in rows if ppid in known)
                sampled.extend((pid, clean(comm)) for pid, _, comm in rows
                               if pid in known and pid != p.pid)
                stop.wait(0.02)

        monitor = None
        if trace_processes:
            monitor = threading.Thread(target=sample_descendants, daemon=True)
            monitor.start()
        try:
            stdout, stderr = p.communicate(timeout=30)
        finally:
            stop.set()
            if monitor is not None:
                monitor.join(timeout=4)
        after = inventory(work)
        record = {"label": label, "cwd": str(cwd.relative_to(work)),
                  "argv": [clean(a) for a in command[1:]], "exit": p.returncode,
                  "seconds": round(time.monotonic() - t, 3),
                  "stdout": clean(stdout),
                  "stderr": clean(stderr),
                  "delta": changes(before, after)}
        if trace_processes:
            record["observed_descendants"] = sorted(set(comm for _, comm in sampled))
        if full_inventory:
            record["inventory"] = {k: v[:2] for k, v in after.items()}
        out["runs"].append(record)
        return record

    base = work / "base"
    make_consumer(base, [("probe_dep", "../producer")])
    run("base-build", base, ["build", "Generated"])
    run("base-replay", base, ["build", "Generated"])
    run("base-no-build", base, ["--no-build", "build", "Generated"])
    run("base-setup", base, ["setup-file", str(base / "Generated.lean")])
    out["snapshots"]["after_base"] = {k: v[:2] for k, v in inventory(producer).items()}
    out["snapshots"]["base_config_traces"] = config_traces(producer)

    alias = work / "alias"
    make_consumer(alias, [("dep_alias", "../producer")])
    run("assigned-name-alias-build", alias, ["build", "Generated"])
    run("assigned-name-alias-setup", alias, ["setup-file", str(alias / "Generated.lean")])
    out["snapshots"]["after_alias"] = {k: v[:2] for k, v in inventory(producer).items()}
    out["snapshots"]["alias_config_traces"] = config_traces(producer)

    shifted = work / "shifted"
    make_consumer(shifted, [("probe_dep", "../producer"), ("dummy", "../dummy")])
    run("dependency-index-shift-build", shifted, ["build", "Generated"])
    run("dependency-index-shift-setup", shifted, ["setup-file", str(shifted / "Generated.lean")])
    out["snapshots"]["after_shift"] = {k: v[:2] for k, v in inventory(producer).items()}
    out["snapshots"]["shift_config_traces"] = config_traces(producer)

    nested = work / "nested" / "consumer"
    make_consumer(nested, [("probe_dep", "../../producer")])
    run("relative-root-build", nested, ["build", "Generated"])
    run("relative-root-setup", nested, ["setup-file", str(nested / "Generated.lean")])
    out["snapshots"]["relative_root_config_traces"] = config_traces(producer)

    run("K-first", base, ["-Kprobe=one", "setup-file", str(base / "Generated.lean")])
    run("K-second", base, ["-Kprobe=two", "setup-file", str(base / "Generated.lean")])
    make_consumer_after = base / "lakefile.lean"
    make_consumer_after.write_text(make_consumer_after.read_text().replace(
        "package consumer\n", "package consumer where\n  moreServerOptions := #[⟨`pp.universes, true⟩]\n"))
    run("server-option-changed-setup", base, ["setup-file", str(base / "Generated.lean")])

    # A same-mtime source edit separates a normal replay from the rehash gate.
    source = producer / "Dep.lean"
    stat = source.stat()
    source.write_text("def depValue : Nat := 8\n")
    os.utime(source, ns=(stat.st_atime_ns, stat.st_mtime_ns))
    out["snapshots"]["same_mtime_source_mutation"] = {
        "source_sha256": digest(source), "mtime_ns": source.stat().st_mtime_ns}
    run("changed-source-no-build-rehash", base,
        ["--rehash", "--no-build", "build", "Dep"])
    run("changed-source-build-rehash", base, ["--rehash", "build", "Dep"])
    run("changed-source-post-build-replay", base, ["build", "Dep"])

    # Same assigned/declared name, distinct physical packages, source and version.
    duplicate = work / "duplicate"
    for suffix, value, version in (("a", 7, "1.0.0"), ("b", 9, "2.0.0")):
        package = duplicate / f"producer_{suffix}"
        make_package(package, "probe_dep", "Dep")
        (package / "lakefile.lean").write_text(
            f'import Lake\nopen Lake DSL\npackage probe_dep where\n'
            f'  version := v!"{version}"\n@[default_target]\nlean_lib Dep\n')
        (package / "Dep.lean").write_text(f"def depValue : Nat := {value}\n")
        (package / "lake-manifest.json").write_text(
            json.dumps(manifest("probe_dep", []), indent=2) + "\n")
    for order in ("ab", "ba"):
        consumer = duplicate / f"consumer_{order}"
        dependencies = [("probe_dep", f"../producer_{suffix}") for suffix in order]
        make_consumer(consumer, dependencies)
        (consumer / "Generated.lean").write_text("import Dep\n#eval depValue\n")
        run(f"duplicate-name-{order}-build", consumer, ["build", "Generated"])
        out["snapshots"][f"duplicate-{order}-config-traces"] = {
            suffix: config_traces(duplicate / f"producer_{suffix}") for suffix in ("a", "b")}

    # Route the same name collision through two distinct transitive packages,
    # avoiding the direct duplicate-require syntax error above.
    for suffix in ("a", "b"):
        wrapper = duplicate / f"wrapper_{suffix}"
        make_package(wrapper, f"wrapper_{suffix}", f"Wrap{suffix.upper()}")
        (wrapper / "lakefile.lean").write_text(
            f'import Lake\nopen Lake DSL\nrequire probe_dep from "../producer_{suffix}"\n'
            f'package wrapper_{suffix}\n@[default_target]\nlean_lib Wrap{suffix.upper()}\n')
        (wrapper / "lake-manifest.json").write_text(json.dumps(
            manifest(f"wrapper_{suffix}", [("probe_dep", f"../producer_{suffix}")]),
            indent=2) + "\n")
    for order, selected in (("ab", "a"), ("ba", "a"), ("ab", "b")):
        label = f"{order}-manifest-{selected}"
        consumer = duplicate / f"transitive_{label}"
        deps = [(f"wrapper_{suffix}", f"../wrapper_{suffix}") for suffix in order]
        make_consumer(consumer, deps)
        (consumer / "Generated.lean").write_text("import Dep\n#eval depValue\n")
        # Lake's root manifest must list transitive packages too. Vary its
        # single probe_dep entry separately from wrapper graph order.
        (consumer / "lake-manifest.json").write_text(json.dumps(
            manifest("consumer", deps + [("probe_dep", f"../producer_{selected}")]),
            indent=2) + "\n")
        run(f"transitive-name-{label}-build", consumer, ["build", "Generated"])
        out["snapshots"][f"transitive-{label}-config-traces"] = {
            suffix: config_traces(duplicate / f"producer_{suffix}") for suffix in ("a", "b")}

    text = json.dumps(out, indent=2, sort_keys=True) + "\n"
    args.output.write_text(text)


if __name__ == "__main__":
    main()
