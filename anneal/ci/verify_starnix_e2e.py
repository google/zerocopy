#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check the production Starnix proof and fresh implementation mutations.

Source hashes bind this test to the original ten-file Fuchsia compilation.
Kernel-evaluated symbolic paths must first prove actual source executions of
each capture. A separate check then applies the fixed byte-reversal endpoints.
"""

import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time
import urllib.request


# Retain raw streams before interpreting a receipt. A compiler crash or
# timeout must not count as proof rejection.
def checked_command(command, directory, log_prefix):
    with log_prefix.with_suffix(".stdout").open("wb") as stdout:
        with log_prefix.with_suffix(".stderr").open("wb") as stderr:
            result = subprocess.run(command, cwd=directory, stdout=stdout,
                                    stderr=stderr, timeout=600, check=False)
    return result.returncode


def verification(arguments, request, artifacts, log_prefix, expected):
    command = [str(arguments.cli), "verify", "--request", str(request),
               "--capture", str(arguments.capture), "--sysroot", str(arguments.sysroot),
               "--lean", str(arguments.lean), "--artifacts", str(artifacts)]
    code = checked_command(command, request.parent, log_prefix)
    output = json.loads(log_prefix.with_suffix(".stdout").read_text())
    valid_sandboxes = ("linux_bwrap", "linux_landlock_seccomp")
    is_pass = expected.endswith("verified")
    if (output.get("schema_version") != 3
            or output.get("taint_reasons") != []
            or "tainted" in output
            or output.get("elaboration_sandbox") not in valid_sandboxes
            or "sorry_declarations" in output
            or (is_pass and "hostile Lean elaborator effects" in output.get("deferred", []))
            or output.get("status") != expected
            or code != (0 if is_pass else 1)):
        raise RuntimeError(f"unexpected {log_prefix.name}: exit {code}, "
                           f"{json.dumps(output)[:2500]}")
    return output


def sources(arguments, fixture, destination):
    pin = json.loads((fixture / "source.json").read_text())
    destination.mkdir()
    # Both downloads and local caches must supply the same original bytes.
    # A cache is a transport choice, not authority to change the workload.
    for name, expected in pin["files"].items():
        if arguments.source_dir:
            data = (arguments.source_dir / name).read_bytes()
        else:
            url = ("https://fuchsia.googlesource.com/fuchsia/+/"
                   f"{pin['revision']}/{pin['source_path']}/{name}?format=TEXT")
            for attempt in range(3):
                try:
                    with urllib.request.urlopen(url, timeout=60) as response:
                        data = base64.b64decode(response.read(), validate=False)
                    break
                except Exception:
                    if attempt == 2:
                        raise
                    time.sleep(1 << attempt)
        actual = hashlib.sha256(data).hexdigest()
        if actual != expected:
            raise RuntimeError(f"pinned source mismatch: {name}: {actual}")
        (destination / name).write_bytes(data)
    return pin


def mutate(path, kind):
    text = path.read_text()
    signature = "pub fn apply_endianness(to_be: bool, width: DataWidth, value: u64) -> u64"
    if text.count(signature) != 1:
        raise RuntimeError("production function signature changed")
    start = text.index("{", text.index(signature))
    # The hash-pinned function is a top-level item. Its inner closing braces
    # are indented; the first column-zero closing brace is its exact end.
    end = text.index("\n}", start) + 2
    if kind == "zero":
        replacement = "{\n    0\n}"
    else:
        replacement = """{
    match width {
        DataWidth::U8 => value & 0xff,
        DataWidth::U16 => value & 0xffff,
        DataWidth::U32 => value & 0xffff_ffff,
        DataWidth::U64 => value,
    }
}"""
    path.write_text(text[:start] + replacement + text[end:])


def execution_request(request_path):
    """Check every symbolic path without assuming byte-reversal results."""
    request = json.loads(request_path.read_text())
    proof = request["proof"]
    fixed_claim_modules = {
        "ProductionClaims", "ProductionEndpoints", "Proof", "Spec",
    }
    proof["sources"] = [source for source in proof["sources"]
                        if source["module"] not in fixed_claim_modules]
    proof["sources"] += [
        {"module": "ExecutionSpec", "path": "ExecutionSpec.lean",
         "role": "specification"},
        {"module": "ExecutionProof", "path": "ExecutionProof.lean", "role": "proof"},
    ]
    proof["specification"] = "ExecutionSpec.specs"
    proof["theorem"] = "ExecutionProof.verify"
    destination = request_path.with_name("execution-request.json")
    destination.write_text(json.dumps(request, indent=2) + "\n")
    return destination


def run(arguments, work):
    repository = Path(__file__).resolve().parents[1]
    fixture = repository / "trusted/cargo-anneal/tests/fixtures/starnix"
    project = work / "production"
    project.mkdir()
    pin = sources(arguments, fixture, project / "source")
    shutil.copytree(fixture / "proof", project / "proof")
    shutil.copyfile(fixture / "request.json", project / "request.json")
    # No proof source depends on a particular capture, so every mutation
    # reuses the exact bytes that the baseline verifies.
    fixed_sources = {path.name: path.read_bytes()
                     for path in (project / "proof").glob("*.lean")}
    proof_sha256 = hashlib.sha256(b"".join(
        name.encode() + b"\0" + contents
        for name, contents in sorted(fixed_sources.items()))).hexdigest()
    start = time.monotonic()
    baseline = verification(arguments, project / "request.json", work / "baseline-artifacts",
                            work / "baseline", "selected_unit_verified")
    if len(baseline["sources"]) != 10 or len(baseline["selected"]) != 1:
        raise RuntimeError("production source/selection inventory changed")
    results = {"baseline": {"status": baseline["status"],
                             "proof_sha256": proof_sha256,
                             "request_sha256": baseline["request_sha256"],
                             "capture_sha256": baseline["capture_sha256"],
                             "timing_ms": baseline["timing_ms"]}}
    # Zero challenges a nontrivial output; masked identity challenges byte
    # reversal while preserving the requested width. Reusing the complete
    # source tree keeps each mutation in its production compilation context.
    for kind in ["zero", "masked-identity"]:
        candidate = work / kind
        shutil.copytree(project, candidate)
        mutate(candidate / "source/api.rs", kind)
        # The unchanged proof sources first prove that every control path of
        # the changed capture actually returns. Syntax, import, or transition
        # failures must stop the test before it can credit the rejection.
        checked_execution = verification(
            arguments, execution_request(candidate / "request.json"),
            work / f"{kind}-checked-execution", work / f"{kind}-execution",
            "selected_unit_verified")
        rejected = verification(arguments, candidate / "request.json",
                                work / f"{kind}-artifacts",
                                work / f"{kind}-rejected", "proof_failed")
        if any((candidate / "proof" / name).read_bytes() != contents
               for name, contents in fixed_sources.items()):
            raise RuntimeError(f"fixed proof sources changed for {kind}")
        if rejected.get("phase") != "audit":
            raise RuntimeError(f"fixed property did not reach proof checking for {kind}")
        results[kind] = {"status": rejected["status"],
                         "phase": rejected["phase"],
                         "execution_status": checked_execution["status"],
                         "capture_sha256": checked_execution["capture_sha256"]}
    # Completion requires both positive execution checks and rejection of the
    # unchanged fixed property. Earlier logs alone establish neither outcome.
    summary = {"source_revision": pin["revision"], "results": results,
               "elapsed_seconds": round(time.monotonic() - start, 3)}
    (work / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


def env_tool(names, bundle_suffix=None):
    for name in names:
        raw = os.environ.get(name, "")
        if raw:
            return Path(raw)
    bundle = os.environ.get("ANNEAL_TEST_INSTALL_ROOT", "")
    if bundle and bundle_suffix:
        return Path(bundle) / bundle_suffix
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    defaults = {
        "cli": env_tool(["ANNEAL_CLI", "ANNEAL_TEST_CARGO_ANNEAL"]),
        "capture": env_tool(["ANNEAL_CAPTURE"], "bin/anneal-rustc-capture"),
        "sysroot": env_tool(
            ["ANNEAL_SYSROOT", "ANNEAL_TEST_RUST_SYSROOT"],
            "rust",
        ),
        "lean": env_tool(["ANNEAL_LEAN"], "lean/bin/lean"),
    }
    for name, default in defaults.items():
        parser.add_argument(
            f"--{name}", type=Path, default=default, required=(default is None)
        )
    parser.add_argument("--source-dir", type=Path,
                        help="Existing pinned core/src; otherwise fetch hash-pinned files")
    parser.add_argument("--artifacts-dir", type=Path,
                        help="New directory retaining complete test evidence")
    arguments = parser.parse_args()
    for name in ["cli", "capture", "sysroot", "lean", "source_dir"]:
        path = getattr(arguments, name)
        if path is not None:
            setattr(arguments, name, path.resolve(strict=True))
    # Own a fresh private evidence directory so an old successful receipt
    # cannot satisfy this run and exported source/log bytes stay private.
    if arguments.artifacts_dir:
        arguments.artifacts_dir.mkdir(mode=0o700)
        run(arguments, arguments.artifacts_dir.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="anneal-starnix-") as directory:
            run(arguments, Path(directory))


if __name__ == "__main__":
    main()
