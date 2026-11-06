#!/usr/bin/env python3
"""Replay the checked-in Anneal scanner slug against two Charon subjects."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
TOOLS = Path(os.environ.get("PROBE_TOOLS", "/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools"))
RUST_BIN = Path(os.environ.get("PROBE_RUST_BIN", str(TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin")))
CARGO = Path(os.environ.get("PROBE_CARGO", str(RUST_BIN / "cargo")))
RUSTC = Path(os.environ.get("PROBE_RUSTC", str(RUST_BIN / "rustc")))
CHARON = Path(os.environ.get("PROBE_CHARON", str(TOOLS / "bin/charon")))
HARNESS = HERE / "harness"
FIXTURE = HERE / "fixture"
RAW = HERE / "raw"
ARTIFACTS = HERE / "artifacts"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(label, args, cwd, env):
    result = subprocess.run(args, cwd=cwd, env=env, capture_output=True, text=True, timeout=120)
    (RAW / f"{label}.stdout").write_text(result.stdout)
    (RAW / f"{label}.stderr").write_text(result.stderr)
    return {"argv": [str(a) for a in args], "cwd": str(cwd), "exit_code": result.returncode,
            "stdout": f"raw/{label}.stdout", "stderr": f"raw/{label}.stderr"}


def project(path):
    data = json.loads(path.read_text())
    names = []
    bodies = []
    def scalars(node):
        if isinstance(node, dict):
            if "Unsigned" in node and node["Unsigned"][0] == "U32":
                yield node["Unsigned"][1]
            for value in node.values():
                yield from scalars(value)
        elif isinstance(node, list):
            for value in node:
                yield from scalars(value)
    for item in data["translated"]["fun_decls"]:
        if item is None or not (item.get("item_meta") or {}).get("is_local"):
            continue
        names.append([part["Ident"][0] for part in item["item_meta"]["name"] if "Ident" in part])
        bodies.append({"source_text": item["item_meta"]["source_text"],
                       "u32_scalar_literals": list(scalars(item["body"]))})
    return {"has_errors": data["has_errors"], "local_function_names": names,
            "local_function_count": len(names), "local_bodies": bodies}


def main():
    RAW.mkdir(exist_ok=True)
    ARTIFACTS.mkdir(exist_ok=True)
    env = dict(os.environ)
    env.update({"RUSTUP_HOME": str(TOOLS / "rustup"), "CARGO_HOME": str(TOOLS / "cargo"),
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1",
                "PATH": os.pathsep.join([str(RUST_BIN), str(TOOLS / "bin"), env.get("PATH", "")])})
    commands = {}
    with tempfile.TemporaryDirectory(prefix="i020-work-", dir=HERE) as tmp:
        work = Path(tmp)
        env["CARGO_TARGET_DIR"] = str(work / "harness-target")
        commands["harness_lock"] = run("harness_lock", [CARGO, "generate-lockfile", "--offline"], HARNESS, env)
        commands["fixture_lock"] = run("fixture_lock", [CARGO, "generate-lockfile", "--offline"], FIXTURE, env)
        commands["harness_build"] = run("harness_build", [CARGO, "build", "--offline", "--locked"], HARNESS, env)
        binary = work / "harness-target/debug/anneal-scanner-slug-probe"
        commands["slug"] = run("slug", [binary, FIXTURE / "Cargo.toml"], HARNESS, env)
        for label, flags in (("default", []), ("selected", ["--features", "selected"])):
            env["CARGO_TARGET_DIR"] = str(work / f"target-{label}")
            output = ARTIFACTS / f"{label}.llbc"
            commands[f"charon_{label}"] = run(
                f"charon_{label}",
                [CHARON, "cargo", "--preset", "aeneas", "--dest-file", output, "--",
                 "--manifest-path", FIXTURE / "Cargo.toml", "--lib", *flags, "--offline", "--locked"],
                FIXTURE, env)
    for name, command in commands.items():
        if command["exit_code"] != 0:
            raise RuntimeError(f"{name}: exit {command['exit_code']}; see {command['stderr']}")
    slug_rows = [line.split("\t") for line in (RAW / "slug.stdout").read_text().splitlines()]
    assert [row[0] for row in slug_rows] == ["default", "selected"]
    assert slug_rows[0][1:] == slug_rows[1][1:], slug_rows
    projections = {name: project(ARTIFACTS / f"{name}.llbc") for name in ("default", "selected")}
    assert all(not row["has_errors"] for row in projections.values())
    assert sha(ARTIFACTS / "default.llbc") != sha(ARTIFACTS / "selected.llbc")
    assert projections["default"]["local_function_names"] == projections["selected"]["local_function_names"]
    assert projections["default"]["local_bodies"][0]["u32_scalar_literals"] == ["7"]
    assert projections["selected"]["local_bodies"][0]["u32_scalar_literals"] == ["11"]
    result = {
        "source_commit": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "source_scanner_sha256": sha(HARNESS / "src/scanner.rs"),
        "tool_sha256": {"cargo": sha(CARGO), "rustc": sha(RUSTC), "charon": sha(CHARON)},
        "fixture_source_sha256": sha(FIXTURE / "src/lib.rs"),
        "fixture_manifest_sha256": sha(FIXTURE / "Cargo.toml"),
        "fixture_lock_sha256": sha(FIXTURE / "Cargo.lock"),
        "harness_lock_sha256": sha(HARNESS / "Cargo.lock"),
        "slug_rows": slug_rows,
        "llbc_sha256": {name: sha(ARTIFACTS / f"{name}.llbc") for name in projections},
        "projections": projections,
        "commands": commands,
        "environment": {"RUSTUP_HOME": env["RUSTUP_HOME"], "CARGO_HOME": env["CARGO_HOME"],
                        "RUST_BIN": str(RUST_BIN), "CHARON": str(CHARON),
                        "CHARON_TOOLCHAIN_IS_IN_PATH": "1", "targets": "fresh per Charon case"},
    }
    (HERE / "results.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    manifest = HERE / "artifacts.sha256.json"
    evidence_paths = json.loads(manifest.read_text())
    manifest.write_text(json.dumps({path: sha(HERE / path) for path in evidence_paths},
                                   indent=2, sort_keys=True) + "\n")
    print(json.dumps({"slug": slug_rows[0][1], "llbc_sha256": result["llbc_sha256"]}, indent=2))


if __name__ == "__main__":
    main()
