#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Real compiled ignore metadata, selection and failed-provider controls."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "kani"))
from check_generated import ignored_proofs, select_harnesses, validate_generated_models
from verify_dependencies import statuses


def verify_selected(args, env, selected, failure=None):
    filters = ["--exact"]
    for name in selected:
        filters += ["--harness", name]
    result = subprocess.run(args + filters, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, flush=True)
    expected = {name: "FAILED" if name == failure else "SUCCESSFUL" for name in selected}
    assert statuses(result) == expected, (statuses(result), expected)
    assert (result.returncode == 0) == (failure not in selected)


def main():
    if subprocess.check_output(["cargo", "kani", "--version"], text=True).strip() != "cargo-kani 0.60.0":
        raise ValueError("review ignore fixture semantics before changing Kani")
    fixture = Path(__file__).resolve().parent / "ignored"
    command = ["cargo", "kani", "--manifest-path", str(fixture / "Cargo.toml"),
               "-Zfunction-contracts", "-Zunstable-options", "--output-format=terse",
               "--memory-safety-checks", "--overflow-checks", "--undefined-function-checks",
               "--unwinding-checks", "--harness-timeout", "30s"]
    (fixture / "target").mkdir(exist_ok=True)
    for feature in (None, "enabled_depends_ignored", "handwritten_depends_ignored",
                    "generic_handwritten", "original_body"):
        with tempfile.TemporaryDirectory(prefix="kani-ignored-", dir=fixture / "target") as target:
            env = dict(os.environ, CARGO_TARGET_DIR=target, RUSTFLAGS="-Copt-level=0")
            args = command + (["--features", feature] if feature else [])
            subprocess.check_call(args + ["--only-codegen"], env=env)
            inventories = [json.loads(p.read_text()) for p in
                           Path(target).glob("kani/**/deps/*.kani-metadata.json")]
            metadata, = [m for m in inventories if m["crate_name"] == "kani_contract_ignore_fixture"]
            proofs, dependencies = validate_generated_models(metadata, return_dependencies=True)
            ignored = ignored_proofs(metadata)
            assert set(ignored.values()) == {"Manual λ", "Known failure", "Requires broken provider", "Generic λ"}
            if feature == "original_body":
                selected, _ = select_harnesses(metadata, dependencies)
                target = "__kani_contract_original_body_all"
                assert not dependencies[target]
                verify_selected(args, env, selected, target)
                continue
            if feature:
                try:
                    select_harnesses(metadata, dependencies)
                except ValueError as error:
                    assert "ignored" in str(error), error
                else:
                    raise AssertionError("enabled caller relied on ignored provider")
                if feature == "generic_handwritten":
                    word, = [name for name in ignored if
                             name.startswith("__kani_contract_Generic_get_word_all")]
                    assert dependencies["generic_handwritten"] == {word}
                    selected, _ = select_harnesses(metadata, dependencies,
                        harnesses=["generic_handwritten"], include_ignored=True)
                    assert set(selected) == {word, "generic_handwritten"}
                    verify_selected(args, env, selected)
                continue
            assert len(proofs) == 7
            broken, = [name for name, reason in ignored.items() if reason == "Known failure"]
            caller, = [name for name, reason in ignored.items() if reason == "Requires broken provider"]
            for options in ({}, {"only_ignored": True}, {"include_ignored": True},
                            {"harnesses": [broken]}, {"harnesses": [caller]}):
                selected, _ = select_harnesses(metadata, dependencies, **options)
                if not options:
                    assert len(selected) == 3 and "handwritten_enabled" in selected
                if options == {"only_ignored": True}:
                    assert len(selected) == 6 and "__kani_contract_enabled_all" in selected
                if options == {"harnesses": [caller]}:
                    assert set(selected) == {caller, broken, "__kani_contract_enabled_all"}
                verify_selected(args, env, selected, broken)
    print("Ignored contract fixtures passed", flush=True)


if __name__ == "__main__":
    main()
