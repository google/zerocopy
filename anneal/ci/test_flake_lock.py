# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Verify flake.nix platform triples and jq filter match foundation-lock."""

import json
from pathlib import Path
import re
import shutil
import subprocess
import textwrap
import unittest


ANNEAL_ROOT = Path(__file__).resolve().parents[1]
FLAKE_PATH = ANNEAL_ROOT / "flake.nix"
LOCK_PATH = ANNEAL_ROOT / "trusted/lean/foundation-lock.json"
TOOLCHAIN_PATH = ANNEAL_ROOT / "trusted/lean/lean-toolchain"

EXPECTED_PLATFORMS = {
    "x86_64-linux": "x86_64-unknown-linux-gnu",
    "aarch64-linux": "aarch64-unknown-linux-gnu",
    "x86_64-darwin": "x86_64-apple-darwin",
    "aarch64-darwin": "arm64-apple-darwin",
}


def _extract_braced_block(text: str, open_brace_idx: int) -> str:
    """Return contents inside `{ ... }` starting at `open_brace_idx`."""
    depth = 0
    in_string = False
    escape = False
    for idx in range(open_brace_idx, len(text)):
        ch = text[idx]
        if escape:
            escape = False
            continue
        if in_string:
            if ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            continue
        if ch == '"':
            in_string = True
        elif ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return text[open_brace_idx + 1 : idx]
    raise AssertionError("unterminated Nix attribute set")


def parse_flake_lock_triples(flake_text: str) -> dict[str, str]:
    """Extract `platforms.<system>.leanLockTriple` entries from flake.nix."""
    header = re.search(r"(?m)^\s*platforms\s*=\s*\{", flake_text)
    if header is None:
        raise AssertionError("could not locate platforms block in flake.nix")
    body = _extract_braced_block(flake_text, header.end() - 1)
    triples: dict[str, str] = {}
    pos = 0
    while True:
        sys_match = re.search(r"(?m)^\s*([A-Za-z0-9_-]+)\s*=\s*\{", body[pos:])
        if sys_match is None:
            break
        system = sys_match.group(1)
        brace_idx = pos + sys_match.end() - 1
        block = _extract_braced_block(body, brace_idx)
        pos = brace_idx + len(block) + 2
        triple_match = re.search(
            r'^\s*leanLockTriple\s*=\s*"([^"]+)";',
            block,
            flags=re.MULTILINE,
        )
        if triple_match is None:
            raise AssertionError(
                f"platform {system!r} in flake.nix is missing leanLockTriple"
            )
        triples[system] = triple_match.group(1)
    if not triples:
        raise AssertionError("found zero platforms inside flake.nix")
    return triples


def extract_flake_jq_filter(flake_text: str) -> str:
    """Extract the `lean-toolchain` `jq` distribution filter from flake.nix."""
    match = re.search(
        r'expected_lean_sha="\$\(jq -er --arg prefix '
        r'"Lean \(version \$\{leanVersion\}, \$\{platform\.leanLockTriple\}" '
        r"'\n(.*?)\n\s*' "
        r'"\$lockFile"\)"',
        flake_text,
        flags=re.DOTALL,
    )
    if match is None:
        raise AssertionError(
            "could not locate expected_lean_sha jq filter in flake.nix"
        )
    return textwrap.dedent(match.group(1)).strip()


def run_flake_jq_filter(
    jq_bin: str,
    jq_filter: str,
    distributions: dict[str, str],
    lean_version: str,
    triple: str,
) -> subprocess.CompletedProcess[str]:
    """Execute flake.nix's real `jq -er` filter on `distributions`."""
    prefix = f"Lean (version {lean_version}, {triple}"
    payload = json.dumps({"distributions": distributions})
    return subprocess.run(
        [jq_bin, "-er", "--arg", "prefix", prefix, jq_filter],
        input=payload,
        text=True,
        capture_output=True,
        check=False,
    )


class FlakeFoundationLockTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        jq_bin = shutil.which("jq")
        if jq_bin is None:
            raise RuntimeError("jq executable is required to verify flake.nix")
        cls.jq_bin = jq_bin
        cls.flake_text = FLAKE_PATH.read_text()
        cls.jq_filter = extract_flake_jq_filter(cls.flake_text)
        toolchain = TOOLCHAIN_PATH.read_text().strip()
        prefix = "leanprover/lean4:v"
        if not toolchain.startswith(prefix):
            raise AssertionError(f"unexpected lean-toolchain: {toolchain!r}")
        cls.lean_version = toolchain[len(prefix) :]
        cls.distributions = json.loads(LOCK_PATH.read_text())["distributions"]

    def test_every_flake_platform_uniquely_matches_foundation_lock(self):
        triples = parse_flake_lock_triples(self.flake_text)
        self.assertEqual(triples, EXPECTED_PLATFORMS)
        self.assertIn("${platform.leanLockTriple}", self.flake_text)
        self.assertIn("expected unique distribution match", self.flake_text)
        self.assertNotIn("pkgs.stdenv.hostPlatform.config", self.flake_text)

        matched_keys: set[str] = set()
        for system, triple in triples.items():
            with self.subTest(system=system, triple=triple):
                proc = run_flake_jq_filter(
                    self.jq_bin,
                    self.jq_filter,
                    self.distributions,
                    self.lean_version,
                    triple,
                )
                self.assertEqual(
                    proc.returncode,
                    0,
                    f"jq failed ({proc.returncode}): {proc.stderr}",
                )
                sha = proc.stdout.strip()
                self.assertEqual(len(sha), 64)
                matches = [k for k, v in self.distributions.items() if v == sha]
                self.assertEqual(len(matches), 1, matches)
                matched_keys.add(matches[0])
        self.assertEqual(matched_keys, set(self.distributions.keys()))

    def test_missing_partial_and_ambiguous_distribution_matches_fail(self):
        # Nix's `aarch64-apple-darwin` must fail against `arm64-apple-darwin*`.
        for missing_triple in (
            "aarch64-apple-darwin",
            "x86_64-apple-darwinfoo",
        ):
            with self.subTest(triple=missing_triple):
                proc = run_flake_jq_filter(
                    self.jq_bin,
                    self.jq_filter,
                    self.distributions,
                    self.lean_version,
                    missing_triple,
                )
                self.assertNotEqual(proc.returncode, 0)
                self.assertIn("found 0", proc.stderr)

        # Suffix decoys (even if real entries were absent or relaxed to `>= 1`)
        # must never satisfy `test("^([0-9]+(\\.[0-9]+)*)?, ")`.
        for decoy_triple, decoy_key in (
            (
                "x86_64-apple-darwin",
                f"Lean (version {self.lean_version}, x86_64-apple-darwinfoo, "
                "commit deadbeef, Release)",
            ),
            (
                "arm64-apple-darwin",
                f"Lean (version {self.lean_version}, "
                "arm64-apple-darwin24.6.0x, commit deadbeef, Release)",
            ),
        ):
            with self.subTest(decoy_key=decoy_key):
                decoy_only = {decoy_key: "f" * 64}
                proc = run_flake_jq_filter(
                    self.jq_bin,
                    self.jq_filter,
                    decoy_only,
                    self.lean_version,
                    decoy_triple,
                )
                self.assertNotEqual(proc.returncode, 0)
                self.assertIn("found 0", proc.stderr)

                with_decoy = dict(self.distributions)
                with_decoy[decoy_key] = "f" * 64
                real_proc = run_flake_jq_filter(
                    self.jq_bin,
                    self.jq_filter,
                    with_decoy,
                    self.lean_version,
                    decoy_triple,
                )
                self.assertEqual(real_proc.returncode, 0, real_proc.stderr)
                self.assertNotEqual(real_proc.stdout.strip(), "f" * 64)

        # Ambiguous matches (`> 1`) must fail closed with `found 2`.
        duplicate = dict(self.distributions)
        duplicate[
            f"Lean (version {self.lean_version}, arm64-apple-darwin25.0.0, "
            "commit deadbeef, Release)"
        ] = "0" * 64
        dup_proc = run_flake_jq_filter(
            self.jq_bin,
            self.jq_filter,
            duplicate,
            self.lean_version,
            "arm64-apple-darwin",
        )
        self.assertNotEqual(dup_proc.returncode, 0)
        self.assertIn("found 2", dup_proc.stderr)


if __name__ == "__main__":
    unittest.main()
