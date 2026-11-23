# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check the alpha CLI with its installed toolchain and the scalar fixture."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import shutil
import subprocess
import tempfile


FIXTURE = (
    Path(__file__).resolve().parent.parent
    / "trusted/cargo-anneal/assets/scalar"
)
FIXTURE_FILES = ("lib.rs", "Spec.lean", "Proof.lean", "request.json")


def check(cli, directory, code, status, stderr_contains=None):
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
    if stderr_contains is not None and stderr_contains not in result.stderr:
        raise RuntimeError(f"missing compiler diagnostic: {result.stderr}")
    return receipt, f"{status} (exit {code})"


def stage_fixture(directory):
    for name in FIXTURE_FILES:
        shutil.copyfile(FIXTURE / name, directory / name)


def run_accepted(cli):
    with tempfile.TemporaryDirectory(prefix="anneal-alpha-accepted-") as tmp:
        directory = Path(tmp)
        stage_fixture(directory)
        accepted, line = check(cli, directory, 0, "selected_unit_verified")
        if accepted["scope"] != {"kind": "selected_unit", "roots": ["zero"]}:
            raise RuntimeError(f"wrong verification scope: {accepted['scope']}")
        return line


def run_proof_failed(cli):
    with tempfile.TemporaryDirectory(prefix="anneal-alpha-proof-failed-") as tmp:
        directory = Path(tmp)
        stage_fixture(directory)
        source = directory / "lib.rs"
        original = source.read_text()
        changed = original.replace("    0\n", "    1\n")
        if changed == original:
            raise RuntimeError("scalar fixture no longer returns zero")
        source.write_text(changed)
        _, line = check(cli, directory, 1, "proof_failed")
        return line


def run_compiler_failed(cli):
    with tempfile.TemporaryDirectory(prefix="anneal-alpha-compiler-failed-") as tmp:
        directory = Path(tmp)
        stage_fixture(directory)
        (directory / "lib.rs").write_text(
            'compile_error!("alpha compiler diagnostic");\n'
        )
        _, line = check(
            cli, directory, 2, "compiler_failed", "alpha compiler diagnostic"
        )
        return line


def run_unsupported(cli):
    with tempfile.TemporaryDirectory(prefix="anneal-alpha-unsupported-") as tmp:
        directory = Path(tmp)
        stage_fixture(directory)
        request_path = directory / "request.json"
        request = json.loads(request_path.read_text())
        request["compilation"]["target"] = "aarch64-unknown-linux-gnu"
        request_path.write_text(json.dumps(request))
        refused, line = check(cli, directory, 1, "unsupported")
        if refused["phase"] != "capture":
            raise RuntimeError(f"unexpected refusal phase: {refused}")
        return line


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cli", required=True, type=Path)
    cli = parser.parse_args().cli.resolve(strict=True)
    cases = (run_accepted, run_proof_failed, run_compiler_failed, run_unsupported)
    with ThreadPoolExecutor(max_workers=len(cases)) as pool:
        futures = [pool.submit(case, cli) for case in cases]
        lines = [future.result() for future in futures]
    for line in lines:
        print(line, flush=True)


if __name__ == "__main__":
    main()
