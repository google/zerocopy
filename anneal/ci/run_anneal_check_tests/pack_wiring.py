# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Tests that the flake, `run_anneal_check.sh`, `checks.toml`, and the
toolchain Dockerfile wire `pack_omnibus_archive.sh` in."""

import os
from pathlib import Path
import stat
import subprocess
import tempfile
import tomllib

from run_anneal_check_tests.support import (
    SCRIPT,
    PACK_SCRIPT,
    FLAKE,
    CHECKS_TOML,
    ANNEAL_TC_DOCKERFILE,
    case_branch,
)


class OmnibusPackWiringCases:
    def setUp(self) -> None:
        self.flake_text = FLAKE.read_text(encoding="utf-8")
        self.script_text = SCRIPT.read_text(encoding="utf-8")
        self.pack_text = PACK_SCRIPT.read_text(encoding="utf-8")

    def test_pack_script_is_executable_and_single_pass_verified(self) -> None:
        mode = PACK_SCRIPT.stat().st_mode
        self.assertTrue(mode & stat.S_IXUSR, "pack_omnibus_archive.sh must be executable")
        self.assertEqual(
            self.pack_text.count("zstd -dc "),
            1,
            "archive verification must decompress the .tar.zst in a single pass",
        )
        self.assertIn("-12 --long=27", self.pack_text)

    def test_flake_and_run_script_both_invoke_canonical_pack_script(self) -> None:
        start = self.flake_text.index("omnibus-archive = pkgs.stdenv.mkDerivation {")
        end = self.flake_text.index("release-check-python =", start)
        omnibus_section = self.flake_text[start:end]

        self.assertIn("packOmnibusScript = ./ci/pack_omnibus_archive.sh;", omnibus_section)
        self.assertIn("minirustUpstreamPin = ./vendor/minirust/UPSTREAM_PIN.json;", omnibus_section)
        self.assertIn('--minirust-upstream-pin "$minirustUpstreamPin"', omnibus_section)
        self.assertIn("targetSpecPreflight = ./trusted/audit/SpecPreflight.lean;", omnibus_section)
        self.assertIn('--target-spec-preflight "$targetSpecPreflight"', omnibus_section)
        self.assertIn('bash "$packOmnibusScript"', omnibus_section)
        self.assertIn("darwin.cctools", omnibus_section)
        self.assertIn("darwin.sigtool", omnibus_section)
        self.assertNotIn("--exclude=", omnibus_section)
        self.assertNotIn("excluded_patterns", omnibus_section)
        self.assertNotIn("zstd -dc", omnibus_section)

        self.assertIn("./ci/pack_omnibus_archive.sh", self.script_text)
        self.assertIn('--minirust-upstream-pin "$minirust_upstream_pin"', self.pack_text)
        self.assertNotIn("--exclude=", self.script_text)
        self.assertNotIn("excluded_patterns", self.script_text)
        self.assertNotIn("zstd -dc", self.script_text)

    def test_ws_test_stages_directly_while_installed_smoke_packs_archive(self) -> None:
        ci_tests_mode = case_branch(self.script_text, "ci-tests")
        clippy_mode = case_branch(self.script_text, "clippy")
        ws_test = case_branch(self.script_text, "ws-test")
        ws_meta = case_branch(self.script_text, "ws-meta")
        installed_smoke = case_branch(self.script_text, "installed-smoke")

        self.assertIn("export ANNEAL_CI_STRICT=1", ci_tests_mode)
        self.assertIn("--test cli --test inspect", clippy_mode)
        self.assertIn("--lib --target wasm32-unknown-unknown", clippy_mode)

        self.assertIn('stage_ws_toolchain_root "$INSTALL_ROOT"', ws_test)
        self.assertNotIn("build_omnibus_archive", ws_test)
        self.assertNotIn("--zstd", ws_test)
        # Shard 1 of `ws-test` still runs `check_mir_differential.py`, while
        # metadata/doc checks live exclusively in `ws-meta`.
        self.assertIn('SHARD_SPEC" == 1/*', ws_test)
        self.assertIn("ci/check_mir_differential.py", ws_test)

        for cmd_fragment in (
            "--example regenerate_bundle",
            "-p cargo-anneal --no-default-features",
            "-p cargo-anneal-tests --no-default-features",
            "--test cli --test inspect",
            "cargo test --workspace --locked --offline",
            "--doc",
        ):
            self.assertIn(cmd_fragment, ws_meta)
            self.assertNotIn(cmd_fragment, ws_test)

        self.assertIn('build_omnibus_archive "$ARCHIVE_PATH"', installed_smoke)
        self.assertIn('setup --local-archive "$ARCHIVE_PATH"', installed_smoke)
        self.assertIn("./bundled_resources.rs", installed_smoke)
        self.assertIn("./bundled_theory.json", installed_smoke)

    def test_ws_meta_preserves_internal_lean_symlinks(self) -> None:
        ws_meta = case_branch(self.script_text, "ws-meta")
        self.assertNotIn("cp -rL", ws_meta)
        self.assertIn('LEAN_TC="$(readlink -f /opt/anneal-nix/lean-toolchain)"', ws_meta)
        self.assertIn('cp -r "$LEAN_TC" "$INSTALL_ROOT/lean"', ws_meta)
        self.assertIn('chmod -R u+w "$INSTALL_ROOT/lean"', ws_meta)

        start = ws_meta.index('    INSTALL_CACHE="')
        end = ws_meta.index('    apply_bundle_env ')
        stage_snippet = ws_meta[start:end]

        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            lean_store = tmp_path / "nix-store-lean"
            (lean_store / "bin").mkdir(parents=True)
            (lean_store / "lib").mkdir(parents=True)
            (lean_store / "bin" / "lean").write_text("#!/bin/sh\n")
            (lean_store / "lib" / "libLLVM.so.22.1").write_bytes(b"elf")
            (lean_store / "lib" / "libLLVM.so").symlink_to("libLLVM.so.22.1")
            top_link = tmp_path / "lean-toolchain-link"
            top_link.symlink_to(lean_store)
            scratch_root = tmp_path / "scratch"
            scratch_root.mkdir()

            for root_dir, _, files in os.walk(lean_store):
                for name in files:
                    p = Path(root_dir) / name
                    if not p.is_symlink():
                        p.chmod(0o444)
                Path(root_dir).chmod(0o555)
            try:
                adapted = stage_snippet.replace(
                    "/opt/anneal-nix/lean-toolchain", str(top_link)
                )
                subprocess.run(
                    [
                        "bash",
                        "-euo",
                        "pipefail",
                        "-c",
                        f'export SCRATCH_ROOT="{scratch_root}"\n{adapted}',
                    ],
                    check=True,
                    capture_output=True,
                    text=True,
                )
            finally:
                for root_dir, _, files in os.walk(lean_store, topdown=False):
                    Path(root_dir).chmod(0o755)
                    for name in files:
                        p = Path(root_dir) / name
                        if not p.is_symlink():
                            p.chmod(0o644)

            staged = scratch_root / "anneal-ws-meta-toolchain/anneal/toolchain/extracted/lean"
            self.assertFalse(staged.is_symlink())
            self.assertTrue(staged.is_dir())
            llvm_real = staged / "lib" / "libLLVM.so.22.1"
            llvm_link = staged / "lib" / "libLLVM.so"
            self.assertFalse(llvm_real.is_symlink())
            self.assertTrue(llvm_real.is_file())
            self.assertTrue(stat.S_IMODE(llvm_real.stat().st_mode) & stat.S_IWUSR)
            self.assertTrue(llvm_link.is_symlink())
            self.assertEqual(os.readlink(llvm_link), "libLLVM.so.22.1")

    def test_checks_toml_and_dockerfile_wire_pack_script_and_ws_meta(self) -> None:
        data = tomllib.loads(CHECKS_TOML.read_text(encoding="utf-8"))
        checks = {c["id"]: c for c in data["checks"]}

        flake_eval = checks["anneal-flake-eval"]
        flake_globs = [
            pat
            for inp in flake_eval["inputs"]
            if inp.get("kind") == "glob"
            for pat in inp.get("include", [])
        ]
        self.assertIn("anneal/ci/pack_omnibus_archive.sh", flake_globs)

        ci_tests = checks["anneal-ci-tests"]
        ci_tests_globs = [
            pat
            for inp in ci_tests["inputs"]
            if inp.get("kind") == "glob"
            for pat in inp.get("include", [])
        ]
        self.assertIn("ci/checks.toml", ci_tests_globs)
        self.assertIn("ci/docker/anneal-tc.Dockerfile", ci_tests_globs)

        self.assertIn("anneal-ws-meta", checks)
        ws_meta = checks["anneal-ws-meta"]
        ws_test = checks["anneal-ws-test"]
        self.assertEqual(ws_meta["image"], ws_test["image"])
        self.assertEqual(ws_meta["sandbox"], ws_test["sandbox"])
        self.assertEqual(ws_meta["runner"], ws_test["runner"])
        self.assertEqual(ws_meta["workdir"], ws_test["workdir"])
        self.assertEqual(
            ws_test["inputs"],
            ws_meta["inputs"] + [{"kind": "glob", "include": ["zerocopy/src/**"]}],
        )
        self.assertEqual(ws_meta["command"], ["./ci/run_anneal_check.sh", "ws-meta"])

        dockerfile_text = ANNEAL_TC_DOCKERFILE.read_text(encoding="utf-8")
        self.assertIn("/tmp/anneal-seed/anneal/ci/pack_omnibus_archive.sh", dockerfile_text)
