# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for ci/scripts/check_toolchains_sync.py and merge_vendor.py."""

import importlib.util
from pathlib import Path
import tempfile
import unittest


REPO_ROOT = Path(__file__).resolve().parent.parent


def load_module(name: str, rel_path: str):
    spec = importlib.util.spec_from_file_location(name, REPO_ROOT / rel_path)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


MOD = load_module("check_toolchains_sync", "ci/scripts/check_toolchains_sync.py")
MERGE = load_module("merge_vendor", "ci/scripts/merge_vendor.py")


class CheckToolchainsSyncTests(unittest.TestCase):
    def _seed_valid_repo(self, root: Path) -> None:
        (root / "ci/pins").mkdir(parents=True)
        (root / "ci/docker").mkdir(parents=True)
        (root / "zerocopy").mkdir(parents=True)
        (root / "zerocopy/Cargo.toml").write_text(
            '[package]\nname = "zerocopy"\nrust-version = "1.56.0"\n'
            '[package.metadata.ci]\npinned-stable = "1.100.0"\n'
            'pinned-nightly = "nightly-2026-09-30"\n'
            '[package.metadata.build-rs]\n'
            'no-zerocopy-core-error-1-81-0 = "1.81.0"\n',
            encoding="utf-8",
        )
        (root / "ci/pins/rust-toolchains.toml").write_text(
            'msrv = "1.56.0"\nstable = "1.100.0"\n'
            'nightly = "nightly-2026-09-30"\n'
            'no-zerocopy-core-error-1-81-0 = "1.81.0"\n',
            encoding="utf-8",
        )
        (root / "ci/pins/kani-pin.toml").write_text(
            'version = "0.60.0"\nbundle-sha256 = "' + ("b" * 64) + '"\n',
            encoding="utf-8",
        )
        (root / "ci/pins/semver-baseline.toml").write_text(
            'version = "0.8.64"\ncrate-sha256 = "' + ("c" * 64) + '"\n'
            'skip = "false"\ntool-version = "0.51.0"\n'
            'tool-sha256 = "' + ("a" * 64) + '"\n',
            encoding="utf-8",
        )
        (root / "ci/pins/layout-seed.toml").write_text(
            'seed = "20261122"\n', encoding="utf-8"
        )
        (root / "ci/docker/zc-stable-msrv.Dockerfile").write_text(
            "ARG PIN_RUST_TOOLCHAINS__MSRV\n"
            "ARG PIN_RUST_TOOLCHAINS__STABLE\n",
            encoding="utf-8",
        )
        (root / "ci/docker/zc-build-rs.Dockerfile").write_text(
            "ARG PIN_RUST_TOOLCHAINS__STABLE\n"
            "ARG PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_CORE_ERROR_1_81_0\n",
            encoding="utf-8",
        )

    def test_live_repository_is_in_sync(self) -> None:
        expected = MOD.verify_rust_toolchains(REPO_ROOT)
        self.assertGreaterEqual(len(expected), 13)
        MOD.verify_other_pins(REPO_ROOT)
        MOD.verify_dockerfile_coverage(REPO_ROOT, expected)
        MOD.verify_checks_toml_coverage(REPO_ROOT, expected)

    def test_detects_version_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._seed_valid_repo(root)
            (root / "ci/pins/rust-toolchains.toml").write_text(
                'msrv = "1.56.0"\nstable = "1.99.0"\n'
                'nightly = "nightly-2026-09-30"\n'
                'no-zerocopy-core-error-1-81-0 = "1.81.0"\n',
                encoding="utf-8",
            )
            with self.assertRaises(SystemExit) as ctx:
                MOD.verify_rust_toolchains(root)
            self.assertIn("stable", str(ctx.exception))

    def test_rejects_integer_layout_seed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._seed_valid_repo(root)
            (root / "ci/pins/layout-seed.toml").write_text(
                "seed = 20261122\n", encoding="utf-8"
            )
            with self.assertRaises(SystemExit) as ctx:
                MOD.verify_other_pins(root)
            self.assertIn("seed", str(ctx.exception))

    def test_detects_missing_dockerfile_arg(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._seed_valid_repo(root)
            expected = MOD.verify_rust_toolchains(root)
            (root / "ci/docker/zc-build-rs.Dockerfile").write_text(
                "ARG PIN_RUST_TOOLCHAINS__STABLE\n",
                encoding="utf-8",
            )
            with self.assertRaises(SystemExit) as ctx:
                MOD.verify_dockerfile_coverage(root, expected)
            self.assertIn("NO_ZEROCOPY_CORE_ERROR_1_81_0", str(ctx.exception))

    def test_detects_missing_checks_toml_toolchain(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._seed_valid_repo(root)
            expected = MOD.verify_rust_toolchains(root)
            (root / "ci/checks.toml").write_text(
                '[[checks]]\nid = "zc"\n'
                'matrix = { toolchain = ["msrv", "stable"] }\n',
                encoding="utf-8",
            )
            with self.assertRaises(SystemExit) as ctx:
                MOD.verify_checks_toml_coverage(root, expected)
            self.assertIn("nightly", str(ctx.exception))


class MergeVendorTests(unittest.TestCase):
    def test_preserves_distinct_versions_and_deduplicates_exact_pairs(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            v1 = root / "rust-src-vendor"
            v2 = root / "zc-vendor"
            out = root / "merged"
            (v1 / "libc").mkdir(parents=True)
            (v1 / "libc/Cargo.toml").write_text(
                '[package]\nname = "libc"\nversion = "0.2.191"\n',
                encoding="utf-8",
            )
            (v1 / "cfg-if").mkdir(parents=True)
            (v1 / "cfg-if/Cargo.toml").write_text(
                '[package]\nname = "cfg-if"\nversion = "1.0.4"\n',
                encoding="utf-8",
            )
            (v2 / "libc").mkdir(parents=True)
            (v2 / "libc/Cargo.toml").write_text(
                '[package]\nname = "libc"\nversion = "0.2.163"\n',
                encoding="utf-8",
            )
            (v2 / "cfg-if").mkdir(parents=True)
            (v2 / "cfg-if/Cargo.toml").write_text(
                '[package]\nname = "cfg-if"\nversion = "1.0.4"\n',
                encoding="utf-8",
            )

            rc = MERGE.main(["merge_vendor.py", str(v1), str(v2), str(out)])
            self.assertEqual(rc, 0)
            entries = sorted(p.name for p in out.iterdir())
            self.assertEqual(entries, ["cfg-if-1.0.4", "libc-0.2.163", "libc-0.2.191"])
            self.assertEqual((out / "libc-0.2.191").resolve(), (v1 / "libc").resolve())
            self.assertEqual((out / "libc-0.2.163").resolve(), (v2 / "libc").resolve())


if __name__ == "__main__":
    unittest.main()
