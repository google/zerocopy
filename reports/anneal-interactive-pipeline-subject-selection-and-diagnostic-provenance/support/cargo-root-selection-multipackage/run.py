#!/usr/bin/env python3
"""Replay the checked-in Anneal resolver against a local Cargo workspace."""
import json
import os
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parent
fixture = root / "fixture"
raw = root / "raw"
raw.mkdir(exist_ok=True)
binary = Path(os.environ["PROBE_BINARY"])
cargo = Path(os.environ["PROBE_CARGO"])
env = os.environ.copy()
env["CARGO_NET_OFFLINE"] = "true"
replacements = [
    (str(root), "$PROBE_ROOT"),
    (str(Path(env["CARGO_TARGET_DIR"])), "$CARGO_TARGET_DIR"),
    (str(Path(env["CARGO_HOME"])), "$CARGO_HOME"),
    (str(Path(env["RUSTUP_HOME"])), "$RUSTUP_HOME"),
]
replacements.sort(key=lambda pair: len(pair[0]), reverse=True)

def sanitize(text):
    for original, replacement in replacements:
        text = text.replace(original, replacement)
    return text
cases = {
    "root_default": (fixture, []),
    "workspace": (fixture, ["--workspace"]),
    "alpha_lib": (fixture, ["-p", "alpha", "--lib"]),
    "alpha_bins": (fixture, ["-p", "alpha", "--bins"]),
    "alpha_bins_feature": (fixture, ["-p", "alpha", "--bins", "--features", "gated"]),
    "alpha_tests": (fixture, ["-p", "alpha", "--tests"]),
    "alpha_dir_default": (fixture / "alpha", []),
    "beta_default": (fixture, ["-p", "beta"]),
}

def run(name, command, cwd):
    result = subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True)
    (raw / f"{name}.stdout").write_text(sanitize(result.stdout))
    (raw / f"{name}.stderr").write_text(sanitize(result.stderr))
    return {
        "argv": [sanitize(str(part)) for part in command],
        "cwd": sanitize(str(cwd)),
        "exit_code": result.returncode,
        "stdout_file": f"raw/{name}.stdout",
        "stderr_file": f"raw/{name}.stderr",
    }

records = {}
for name, (cwd, args) in cases.items():
    records[name] = run(name, [binary, *args], cwd)

metadata_cmd = [cargo, "metadata", "--offline", "--locked", "--format-version", "1"]
records["cargo_metadata"] = run("cargo_metadata", metadata_cmd, fixture)
for name, extra in {
    "cargo_default": [],
    "cargo_workspace": ["--workspace"],
    "cargo_alpha_bins": ["-p", "alpha", "--bins"],
    "cargo_alpha_bins_feature": ["-p", "alpha", "--bins", "--features", "gated"],
    "cargo_alpha_tests": ["-p", "alpha", "--tests"],
}.items():
    records[name] = run(
        name,
        [cargo, "check", "--offline", "--locked", "--message-format", "json", *extra],
        fixture,
    )

(root / "commands.json").write_text(json.dumps(records, indent=2) + "\n")
for name, record in records.items():
    print(name, record["exit_code"], record["stdout_file"], record["stderr_file"])
