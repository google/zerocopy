#!/usr/bin/env python3
"""R121: compare three installed rustc binaries against the frozen scanner.

This script writes only under its own directory. It imports the published
scanner without changing that source or the shared reference checkout.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish")
SCANNER = REPO / "reports/anneal-3730-annotation-gap-probes-2026-09-29/support/probe.py"
RUSTC = {
    "nightly_2026_05_31": Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin/rustc"),
    "stable_1_98_1": Path("/opt/homebrew/bin/rustc"),
    "nightly_2026_09_17": Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/rustup/toolchains/nightly-2026-09-17-aarch64-apple-darwin/bin/rustc"),
}


def sha(path_or_bytes):
    data = path_or_bytes.read_bytes() if isinstance(path_or_bytes, Path) else path_or_bytes
    return hashlib.sha256(data).hexdigest()


def command(args):
    process = subprocess.run([str(a) for a in args], cwd=HERE, text=True,
                             capture_output=True, timeout=30)
    return {"argv": [str(a) for a in args], "exit": process.returncode,
            "stdout": process.stdout, "stderr": process.stderr}


def main():
    assert SCANNER.is_file()
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location("frozen_r121_scanner", SCANNER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    original = json.loads((SCANNER.parent / "raw-results.json").read_text())
    fixtures = {}
    (HERE / "fixtures").mkdir(exist_ok=True)
    for name in ("baseline", "rust_incomplete"):
        source = original["fixtures"][name]["source"]
        path = HERE / "fixtures" / f"{name}.rs"
        path.write_bytes(source.encode("utf-8"))
        assert sha(path) == original["fixtures"][name]["source_sha256"]
        projection, mapping = module.render(source)
        blocks = module.scan(source)
        assert blocks == original["fixtures"][name]["blocks"]
        assert mapping == original["fixtures"][name]["map"]
        assert projection == original["fixtures"][name]["projection"]
        fixtures[name] = {
            "path": str(path), "source_sha256": sha(path),
            "scanner_blocks": blocks, "projection_sha256": sha(projection.encode()),
        }

    compilers = {}
    for name, binary in RUSTC.items():
        assert binary.is_file(), binary
        entry = {"path": str(binary), "binary_sha256": sha(binary),
                 "version": command([binary, "-Vv"]), "runs": {}}
        for fixture_name in fixtures:
            source_path = HERE / "fixtures" / f"{fixture_name}.rs"
            metadata_path = HERE / "fixtures" / f"{name}-{fixture_name}.rmeta"
            metadata_path.unlink(missing_ok=True)
            run = command([binary, "--crate-type", "lib", "--emit", "metadata",
                           "-o", metadata_path, source_path])
            run["metadata_exists"] = metadata_path.exists()
            run["metadata_sha256"] = sha(metadata_path) if metadata_path.exists() else None
            entry["runs"][fixture_name] = run
        compilers[name] = entry

    assert all(c["runs"]["baseline"]["exit"] == 0 for c in compilers.values())
    assert all(c["runs"]["rust_incomplete"]["exit"] != 0 for c in compilers.values())
    assert all(c["runs"]["baseline"]["metadata_exists"] for c in compilers.values())
    assert all(not c["runs"]["rust_incomplete"]["metadata_exists"] for c in compilers.values())
    assert len({c["runs"]["rust_incomplete"]["stderr"] for c in compilers.values()}) == 1
    assert fixtures["baseline"]["projection_sha256"] == fixtures["rust_incomplete"]["projection_sha256"]

    result = {"scanner": {"path": str(SCANNER), "sha256": sha(SCANNER)},
              "original_raw_results_sha256": sha(SCANNER.parent / "raw-results.json"),
              "fixtures": fixtures, "compilers": compilers}
    output = HERE / "evidence.json"
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"evidence_sha256": sha(output),
                      "malformed_exit": {n: c["runs"]["rust_incomplete"]["exit"]
                                         for n, c in compilers.items()},
                      "scanner_projection_equal": fixtures["baseline"]["projection_sha256"] == fixtures["rust_incomplete"]["projection_sha256"]},
                     sort_keys=True))


if __name__ == "__main__":
    main()
