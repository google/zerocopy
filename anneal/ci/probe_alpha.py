# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check the alpha CLI with its installed toolchain and the scalar fixture."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import tempfile


FIXTURE = (
    Path(__file__).resolve().parent.parent
    / "trusted/cargo-anneal/tests/fixtures/scalar"
)


def check(cli, directory, code, status):
    result = subprocess.run(
        [str(cli), "verify", "--request", "request.json"],
        cwd=directory,
        capture_output=True,
        text=True,
        timeout=240,
    )
    if result.returncode != code:
        raise RuntimeError(
            f"expected exit {code}, got {result.returncode}\n"
            f"{result.stdout}\n{result.stderr}"
        )
    receipt = json.loads(result.stdout)
    if receipt["status"] != status:
        raise RuntimeError(f"expected {status}, got {receipt}")
    print(f"{status} (exit {code})", flush=True)
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cli", required=True, type=Path)
    cli = parser.parse_args().cli.resolve(strict=True)
    with tempfile.TemporaryDirectory(prefix="anneal-alpha-") as tmp:
        directory = Path(tmp)
        for name in ("lib.rs", "Spec.lean", "Proof.lean", "request.json"):
            shutil.copyfile(FIXTURE / name, directory / name)

        accepted = check(cli, directory, 0, "selected_unit_verified")
        if accepted["scope"] != {"kind": "selected_unit", "roots": ["zero"]}:
            raise RuntimeError(f"wrong verification scope: {accepted['scope']}")

        source = directory / "lib.rs"
        original = source.read_text()
        changed = original.replace("    0\n", "    1\n")
        if changed == original:
            raise RuntimeError("scalar fixture no longer returns zero")
        source.write_text(changed)
        check(cli, directory, 1, "proof_failed")

        source.write_text(original)
        request_path = directory / "request.json"
        request = json.loads(request_path.read_text())
        request["compilation"]["target"] = "aarch64-unknown-linux-gnu"
        request_path.write_text(json.dumps(request))
        refused = check(cli, directory, 1, "unsupported")
        if refused["phase"] != "capture":
            raise RuntimeError(f"unexpected refusal phase: {refused}")


if __name__ == "__main__":
    main()
