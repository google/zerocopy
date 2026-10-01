# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Read Anneal's archive identity and validate the local CLI patch installation.

The flake lock identifies the upstream sources; the archive supplies their runtime
versions. This module stores no independent upstream pin and never edits metadata.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess

PATCH_SHA256 = "a61422f5483f4f753164e0e9e209cc0c872f8072c3318728746665f878bf6b19"
PATCH_SUFFIX = "+nominal-tuple-structs.1"


def digest(path):
    result = hashlib.sha256()
    with path.open('rb') as file:
        for block in iter(lambda: file.read(1024 * 1024), b''):
            result.update(block)
    return result.hexdigest()


def load_metadata(repo, tools):
    lock = json.loads((repo / "anneal/flake.lock").read_text())
    nodes = lock["nodes"]
    aeneas = nodes[nodes[lock["root"]]["inputs"]["aeneas"]]
    charon = nodes[aeneas["inputs"]["charon"]]
    data = json.loads((tools / "bundle/aeneas/metadata.json").read_text())
    fields = {"aeneas-release", "aeneas-revision", "aeneas-source-nar-hash",
              "charon-revision", "lean-toolchain", "rust-toolchain-date",
              "rust-toolchain-version"}
    if not isinstance(data, dict) or set(data) != fields or not all(isinstance(v, str) for v in data.values()):
        raise ValueError("Invalid Anneal archive metadata")
    expected = {"aeneas-revision": aeneas["locked"]["rev"],
                "aeneas-source-nar-hash": aeneas["locked"]["narHash"],
                "charon-revision": charon["locked"]["rev"]}
    for key, value in expected.items():
        if data.get(key) != value:
            raise ValueError(f"Anneal archive identity mismatch: {key}")
    if not re.fullmatch(r"nightly-\d{4}\.\d{2}\.\d{2}-" + expected["aeneas-revision"][:7], data["aeneas-release"]):
        raise ValueError("Anneal archive release/source mismatch")
    if not re.fullmatch(r"\d+\.\d+\.\d+", data["lean-toolchain"]):
        raise ValueError("Invalid archive Lean version")
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", data["rust-toolchain-date"]):
        raise ValueError("Invalid archive Rust date")
    if data["rust-toolchain-version"] != "nightly-" + data["rust-toolchain-date"]:
        raise ValueError("Anneal archive Rust date/version mismatch")
    if digest(repo / "verification/aeneas/patches/use-tuple-structs.patch") != PATCH_SHA256:
        raise ValueError("Checked-in CLI patch digest mismatch")
    return data


def runtime_env(tools):
    env = dict(os.environ)
    env["PATH"] = os.pathsep.join([str(tools / "rust/bin"), str(tools / "lean/bin"), str(tools), env.get("PATH", "")])
    libs = os.pathsep.join(str(tools / p) for p in ["rust/lib", "lean/lib", "lean/lib/lean"])
    for key in ["LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH"]:
        env[key] = libs + (os.pathsep + env[key] if env.get(key) else "")
    env["LEAN_SYSROOT"] = str(tools / "lean")
    env["CHARON_TOOLCHAIN_IS_IN_PATH"] = "1"
    return env


def output(tools, binary, *args):
    return subprocess.check_output([str(tools / binary), *args], env=runtime_env(tools), text=True).strip()


def probe(tools, data, patched):
    version = data["aeneas-release"] + (PATCH_SUFFIX if patched else "")
    actual = output(tools, "aeneas", "-version")
    allowed = {"aeneas " + version}
    if not patched:
        allowed.add("aeneas " + data["aeneas-revision"][:7])
    if actual not in allowed:
        raise ValueError(f"Aeneas version mismatch: {actual}")
    charon = output(tools, "charon", "version")
    if not charon.endswith(" (" + data["charon-revision"] + ")"):
        raise ValueError("Charon revision mismatch")
    if output(tools, "charon", "toolchain-version") != data["rust-toolchain-version"]:
        raise ValueError("Charon Rust toolchain mismatch")
    rust = output(tools, "rust/bin/rustc", "--version")
    if not rust.startswith("rustc ") or "-nightly (" not in rust:
        raise ValueError("Invalid bundled nightly Rust compiler")
    lean = output(tools, "lean/bin/lean", "--version")
    if not lean.startswith("Lean (version " + data["lean-toolchain"] + ","):
        raise ValueError("Bundled Lean version mismatch")
    if (tools / "backends/lean/lean-toolchain").read_text().strip() != "leanprover/lean4:v" + data["lean-toolchain"]:
        raise ValueError("Backend Lean version mismatch")
    return charon.split(" (", 1)[0]


def provenance(tools, data):
    return {"metadata": data, "source_rev": data["aeneas-revision"],
            "source_nar_hash": data["aeneas-source-nar-hash"],
            "patch_sha256": PATCH_SHA256, "version": data["aeneas-release"] + PATCH_SUFFIX,
            "binary_sha256": digest(tools / "aeneas"),
            "upstream_binary_sha256": digest(tools / "aeneas-upstream"),
            "runtime_binary_sha256": {name: digest(tools / name) for name in
                                      ["charon", "charon-driver", "rust/bin/rustc",
                                       "rust/bin/cargo", "lean/bin/lean", "lean/bin/lake"]},
            "libraries": {p.name: digest(p) for p in sorted((tools / "libs").glob("*.dylib"))}}


def validate(repo, tools, patched=True):
    data = load_metadata(repo, tools)
    if patched:
        record = json.loads((tools / "aeneas-build.json").read_text())
        if record != provenance(tools, data):
            raise ValueError("Patched CLI provenance mismatch; rebuild in a fresh installation")
        upstream = output(tools, "aeneas-upstream", "-version")
        if upstream not in {"aeneas " + data["aeneas-release"], "aeneas " + data["aeneas-revision"][:7]}:
            raise ValueError("Upstream comparison binary version mismatch")
    charon_version = probe(tools, data, patched)
    return data, charon_version


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["check", "shell", "record"])
    parser.add_argument("tools", type=Path)
    parser.add_argument("--upstream", action="store_true")
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[2]
    tools = args.tools.resolve()
    if args.command == "record":
        data = load_metadata(repo, tools)
        probe(tools, data, True)
        record = tools / "aeneas-build.json"
        if record.exists():
            raise ValueError("Refusing to overwrite CLI provenance")
        record.write_text(json.dumps(provenance(tools, data), indent=2) + "\n")
        return
    data, charon = validate(repo, tools, patched=not args.upstream)
    if args.command == "shell":
        values = {"AENEAS_RELEASE": data["aeneas-release"], "AENEAS_REV": data["aeneas-revision"],
                  "AENEAS_SOURCE_NAR_HASH": data["aeneas-source-nar-hash"],
                  "AENEAS_VERSION": data["aeneas-release"] + PATCH_SUFFIX,
                  "AENEAS_PATCH_SHA256": PATCH_SHA256, "CHARON_VERSION": charon,
                  "CHARON_REV": data["charon-revision"],
                  "AENEAS_RUST_TOOLCHAIN": data["rust-toolchain-version"],
                  "AENEAS_LEAN_TOOLCHAIN": "leanprover/lean4:v" + data["lean-toolchain"],
                  "AENEAS_LEAN_VERSION": data["lean-toolchain"]}
        for key, value in values.items():
            print(key + "=" + shlex.quote(value))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        raise SystemExit("Invalid Anneal toolchain: " + str(error))
