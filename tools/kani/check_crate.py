#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check generated proof attributes, then verify the complete crate suite."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import tomllib
from check_generated import validate_generated
from injected import injected_crate


def main():
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
                       "--features", "__internal_use_only_features_that_work_on_stable",
                       "-Zfunction-contracts", "--output-format=terse", "--randomize-layout",
                       "--memory-safety-checks", "--overflow-checks", "--undefined-function-checks",
                       "--unwinding-checks"]
            subprocess.check_call(command + ["--only-codegen"])
            metadata = [json.loads(p.read_text()) for p in Path(target).glob("kani/**/deps/*.kani-metadata.json")]
            metadata = [m for m in metadata if m["crate_name"] == "zerocopy"]
            if len(metadata) != 1 or metadata[0]["unsupported_features"]:
                raise ValueError("unexpected fresh crate inventory")
            proofs = validate_generated(metadata[0])
            if not proofs:
                raise ValueError("no generated contract proofs discovered")
            subprocess.check_call(command)


if __name__ == "__main__":
    main()
