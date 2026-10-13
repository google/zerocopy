#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Real Kani regressions for compiled, acyclic verified contract dependencies."""

import json
import os
import re
from pathlib import Path
import subprocess
import sys
import tempfile
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "kani"))
import check_generated

BASE = {"leaf", "pre_leaf", "post_leaf", "gate", "left", "right", "join_post", "top"}
REJECTIONS = {
    "missing_provider": "contract has no discovered generated proof",
    "wrong_instance": "verified dependency has no generated full-domain proof",
    "mutual_cycle": "cyclic verified contract dependencies are forbidden",
    "generator_reentry": "argument generation or cleanup reaches contract checking",
}
FAILURES = {
    "stub_requires": "violates_requires",
    "false_callee": "false_leaf",
    "full_output": "output_caller",
}
ADDITIONS = {
    "stub_requires": {"violates_requires"},
    "false_callee": {"false_leaf", "false_leaf_caller"},
    "narrow_output": {"output_leaf", "output_caller"},
    "full_output": {"output_leaf", "output_caller"},
}


def proof(function):
    return f"__kani_contract_{function}_all"


def checked_inventory(metadata):
    models = []
    original = check_generated.validate_dependencies

    def capture(values):
        models.extend(values)
        return original(values)

    with patch.object(check_generated, "validate_dependencies", side_effect=capture):
        names = check_generated.validate_generated_models(metadata)
    providers = {symbol: harness["pretty_name"] for harness, symbol, _ in models}
    edges = {harness["pretty_name"]: {providers[symbol] for symbol in used}
             for harness, _, used in models}
    if proof("top") not in edges:
        return names
    # These include dependencies reached from requires/ensures of replacements,
    # rather than only calls in the selected implementation body.
    expected = {proof(name) for name in
                {"left", "right", "gate", "join_post", "pre_leaf", "post_leaf"}}
    if edges[proof("top")] != expected:
        raise ValueError("compiled hidden-condition dependency edges were lost")
    for function in ("left", "right"):
        if edges[proof(function)] != {proof("leaf")}:
            raise ValueError("compiled diamond dependency edges were lost")
    return names


def run(args, env):
    result = subprocess.run(args, env=env, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    print(result.stdout, flush=True)
    return result


def statuses(result):
    blocks = re.findall(r"Checking harness ([^\n]+)\.\.\.\n(.*?)(?=\nChecking harness |"
                        r"\nManual Harness Summary:|\Z)", result.stdout, re.S)
    values = {}
    for name, block in blocks:
        matches = re.findall(r"VERIFICATION:- (SUCCESSFUL|FAILED)", block)
        if name in values or len(matches) != 1:
            raise ValueError("unexpected harness verification result")
        values[name] = matches[0]
    return values


def main():
    if subprocess.check_output(["cargo", "kani", "--version"], text=True).strip() != "cargo-kani 0.60.0":
        raise ValueError("review dependency fixture semantics before changing Kani")
    fixture = Path(__file__).resolve().parent / "dependencies"
    command = ["cargo", "kani", "--manifest-path", str(fixture / "Cargo.toml"),
               "-Zfunction-contracts", "-Zunstable-options", "--output-format=terse",
               "--memory-safety-checks", "--overflow-checks", "--undefined-function-checks",
               "--unwinding-checks", "--harness-timeout", "30s"]
    (fixture / "target").mkdir(exist_ok=True)
    for feature in (None, *REJECTIONS, *FAILURES, "narrow_output"):
        print(f"Dependency fixture: {feature or 'positive'}", flush=True)
        with tempfile.TemporaryDirectory(prefix="kani-dependencies-", dir=fixture / "target") as target:
            env = dict(os.environ, CARGO_TARGET_DIR=target, RUSTFLAGS="-Copt-level=0")
            args = command + (["--no-default-features", "--features", feature] if feature else [])
            run(args + ["--only-codegen"], env).check_returncode()
            inventories = [json.loads(p.read_text()) for p in
                           Path(target).glob("kani/**/deps/*.kani-metadata.json")]
            inventories = [m for m in inventories if m["crate_name"] == "kani_contract_dependency_fixture"]
            if len(inventories) != 1 or inventories[0]["unsupported_features"]:
                raise ValueError("expected exactly one supported fresh dependency inventory")
            metadata = inventories[0]
            if feature in REJECTIONS:
                try:
                    check_generated.validate_generated_models(metadata)
                except ValueError as error:
                    if REJECTIONS[feature] not in str(error):
                        raise
                    print(f"Expected rejection: {error}", flush=True)
                else:
                    raise ValueError(f"{feature} escaped the compiled dependency check")
                continue
            names = checked_inventory(metadata)
            base = BASE if feature is None else {"leaf"}
            expected = {proof(name) for name in base | ADDITIONS.get(feature, set())}
            if set(names) != expected or len(metadata["proof_harnesses"]) != len(expected):
                raise ValueError("missing or extra dependency fixture proofs")
            if feature == "false_callee":
                # Diagnostic control only: a substituted caller can succeed
                # before its dependency is proved. The mandatory run is below.
                isolated = run(args + ["--exact", "--harness", proof("false_leaf_caller")], env)
                isolated.check_returncode()
                if statuses(isolated) != {proof("false_leaf_caller"): "SUCCESSFUL"}:
                    raise ValueError("false-callee isolation control did not verify exactly its caller")
            result = run(args, env)
            expected_statuses = {name: "SUCCESSFUL" for name in expected}
            if feature in FAILURES:
                expected_statuses[proof(FAILURES[feature])] = "FAILED"
                if result.returncode == 0:
                    raise ValueError(f"{feature} was not refuted by the complete suite")
            else:
                result.check_returncode()
            if statuses(result) != expected_statuses:
                raise ValueError("complete suite did not produce the expected per-harness results")
            if feature not in FAILURES:
                if feature == "narrow_output":
                    print("Expected success outside the full-output Arbitrary obligation; "
                          "full_output refutes the same caller.", flush=True)
    print("Verified contract dependency fixtures passed", flush=True)


if __name__ == "__main__":
    main()
