#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Real Kani checks: discovery, no duplicates, full-domain failure and rejection."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "kani"))
from check_generated import validate_generated

EXPECTED = {
    "__kani_contract_increment_all",
    "Example::__kani_contract_get_all",
    "Example::__kani_contract_width_unit",
    "Example::__kani_contract_width_word",
    "__kani_contract_Generic_width_byte_all",
    "__kani_contract_Generic_width_word_all",
    "__kani_contract_Generic_pair_byte_byte",
    "__kani_contract_Generic_pair_byte_word",
    "__kani_contract_Generic_pair_word_byte",
    "__kani_contract_Generic_pair_word_word",
}

REJECTIONS = {
    "unsupported_slice": "unbounded or opaque input domains are unsupported",
    "wrong_owner": "mismatched types",
    "wrong_generic_owner": "generic parameters from outer item",
    "local_homonym": "was not found",
    "free_method": "module is not supported",
    "generic_local_homonym": "was not found",
    "contracted_local_homonym": "was not found",
}

FAILURES = {
    "false_contract": "__kani_contract_broken_all",
    "false_generic_pair": "__kani_contract_Generic_pair_word_byte",
}


def main():
    version = subprocess.check_output(["cargo", "kani", "--version"], text=True).strip()
    if version != "cargo-kani 0.60.0":
        raise ValueError("review the fixture/checker schema before changing Kani")
    fixture = Path(__file__).resolve().parent / "fixture"
    command = ["cargo", "kani", "--manifest-path", str(fixture / "Cargo.toml"),
               "-Zfunction-contracts", "-Zunstable-options", "--output-format=terse",
               "--memory-safety-checks", "--overflow-checks", "--undefined-function-checks",
               "--unwinding-checks", "--harness-timeout", "30s"]
    (fixture / "target").mkdir(exist_ok=True)
    for feature in (None, *FAILURES, *REJECTIONS):
        with tempfile.TemporaryDirectory(prefix="kani-macro-", dir=fixture / "target") as target:
            env = dict(os.environ, CARGO_TARGET_DIR=target)
            args = command + (["--features", feature] if feature else [])
            codegen = subprocess.run(args + ["--only-codegen"], env=env,
                                     text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            print(codegen.stdout, flush=True)
            if feature in REJECTIONS:
                message = REJECTIONS[feature]
                if codegen.returncode == 0 or message not in codegen.stdout:
                    raise ValueError(f"{feature} did not produce the expected compile error")
                continue
            codegen.check_returncode()
            inventories = [json.loads(p.read_text()) for p in
                           Path(target).glob("kani/**/deps/*.kani-metadata.json")]
            inventories = [m for m in inventories if m["crate_name"] == "kani_contract_macro_fixture"]
            if len(inventories) != 1:
                raise ValueError("expected exactly one fresh fixture inventory")
            metadata = inventories[0]
            actual = set(validate_generated(metadata))
            expected = EXPECTED | ({"__kani_contract_broken_all"}
                                   if feature == "false_contract" else set())
            if actual != expected or len(metadata["proof_harnesses"]) != len(expected):
                raise ValueError(f"missing/extra generated proofs: {actual ^ expected}")
            selection = (["--exact", "--harness", FAILURES[feature]]
                         if feature in FAILURES else [])
            result = subprocess.run(args + selection, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            print(result.stdout, flush=True)
            if feature in FAILURES:
                if (result.returncode == 0 or "VERIFICATION:- FAILED" not in result.stdout
                        or FAILURES[feature] not in result.stdout):
                    raise ValueError("the boundary-only false contract was not refuted")
                if (feature == "false_generic_pair"
                        and "Generic::<u16>::pair::<u8>" not in result.stdout):
                    raise ValueError("the intended concrete generic pair was not refuted")
            else:
                result.check_returncode()
    print("Generated contract proof fixtures passed", flush=True)


if __name__ == "__main__":
    main()
