#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check every compiled proof, then verify the selected crate suite."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile
import tomllib
from check_generated import select_harnesses, validate_generated_models
from injected import injected_crate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-no-features-build", action="store_true",
                        help="compile and inspect the dependency configuration; do not verify")
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--include-ignored", action="store_true",
                           help="allow ignored proofs; verify all unless --harness selects roots")
    selection.add_argument("--ignored", action="store_true",
                           help="verify ignored contracts and their dependency providers")
    parser.add_argument("--harness", action="append", default=[], metavar="EXACT_NAME",
                        help="select an exact harness and its dependency providers; repeatable")
    args = parser.parse_args()
    if subprocess.check_output(["cargo", "kani", "--version"], text=True).strip() != "cargo-kani 0.60.0":
        raise ValueError("review the proof metadata schema before changing Kani")
    crate = Path(__file__).resolve().parents[2] / "zerocopy"
    manifest = tomllib.loads((crate / "Cargo.toml").read_text())
    if (manifest.get("kani") or manifest.get("package", {}).get("metadata", {}).get("kani")
            or manifest.get("workspace", {}).get("metadata", {}).get("kani")):
        raise ValueError("Kani manifest overrides could disable proof checks")
    with injected_crate(crate.parent) as crate:
        os.chdir(crate)
        (crate / "target").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="kani-generated-", dir=crate / "target") as target:
            os.environ["CARGO_TARGET_DIR"] = target
            command = ["./cargo.sh", "+stable", "kani", "--package", "zerocopy",
                       "-Zfunction-contracts", "--output-format=terse", "--randomize-layout",
                       "--memory-safety-checks", "--overflow-checks", "--undefined-function-checks",
                       "--unwinding-checks"]
            command += (["--no-default-features"] if args.check_no_features_build else
                        ["--features", "__internal_use_only_features_that_work_on_stable"])
            subprocess.check_call(command + ["--only-codegen"])
            metadata = [json.loads(p.read_text()) for p in Path(target).glob("kani/**/deps/*.kani-metadata.json")]
            metadata = [m for m in metadata if m["crate_name"] == "zerocopy"]
            if len(metadata) != 1 or metadata[0]["unsupported_features"]:
                raise ValueError("unexpected fresh crate inventory")
            proofs, dependencies = validate_generated_models(
                metadata[0], return_dependencies=True)
            if not proofs:
                raise ValueError("no generated contract proofs discovered")
            selected, ignored = select_harnesses(
                metadata[0], dependencies, include_ignored=args.include_ignored,
                only_ignored=args.ignored, harnesses=args.harness)
            for name, reason in ignored.items():
                status = ("CHECK ignored" if args.check_no_features_build else
                          "RUN ignored") if name in selected else "SKIP ignored"
                print(f"{status}: {name}: {reason}", flush=True)
            if not args.check_no_features_build:
                # Kani applies --exact to the whole repeated --harness inventory.
                # Keep all compilation/checking unfiltered; filter verification only.
                filters = ["--exact"]
                for name in selected:
                    filters += ["--harness", name]
                subprocess.check_call(command + filters)


if __name__ == "__main__":
    main()
