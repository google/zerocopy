# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`check_minirust_pin.py` tests for the vendored MiniRust pin checks and
`run_cli`."""

from __future__ import annotations

from .support import (
    ANNEAL_ROOT,
    check_minirust_pin,
    json,
    _make_tree_writable,
    os,
    Path,
    populate_valid_repo,
    SCRIPT,
    _sha256_bytes,
    shutil,
    subprocess,
    sys,
    tempfile,
)


class VendorPinCases:
    """`CheckMiniRustPinTests` methods for the vendored MiniRust pin checks and
    `run_cli`."""

    def run_cli(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), *args],
            capture_output=True,
            text=True,
        )

    # ------------------------------------------------------------------
    # Vendor pin tests
    # ------------------------------------------------------------------

    def test_real_vendored_minirust_pin_passes(self) -> None:
        res = self.run_cli(
            "--repo-root",
            str(ANNEAL_ROOT),
            "--check-lean",
            "--check-anchors",
        )
        self.assertEqual(res.returncode, 0, res.stderr)
        self.assertIn("vendor-pin: OK (30 files at d821c6e3a3d3)", res.stdout)
        self.assertIn("lean-hygiene: OK (10 modules)", res.stdout)
        self.assertIn("spec-anchors: OK (58 anchors)", res.stdout)

    def test_valid_copied_pin_passes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            res = self.run_cli("--repo-root", str(root))
            self.assertEqual(res.returncode, 0, res.stderr)
            self.assertIn(
                "vendor-pin: OK (30 files at d821c6e3a3d3)", res.stdout
            )

    def test_populate_valid_repo_from_readonly_source_tree(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            ro_src = tmp_path / "readonly_anneal"
            shutil.copytree(
                ANNEAL_ROOT / "vendor/minirust", ro_src / "vendor/minirust"
            )
            try:
                for dirpath, _, filenames in os.walk(
                    ro_src, topdown=False, followlinks=False
                ):
                    dp = Path(dirpath)
                    for name in filenames:
                        fp = dp / name
                        if not fp.is_symlink():
                            fp.chmod(0o444)
                    dp.chmod(0o555)

                dst_repo = tmp_path / "dst_anneal"
                populate_valid_repo(dst_repo, source_root=ro_src)
                vendor_dir = dst_repo / "vendor/minirust"
                (vendor_dir / "UPSTREAM_PIN.json").write_text(
                    "{}\n", encoding="utf-8"
                )
                (vendor_dir / "spec/lang/well-formed.md").write_text(
                    "mutated\n", encoding="utf-8"
                )
                (vendor_dir / "spec/lang/extra.md").write_text(
                    "added\n", encoding="utf-8"
                )
            finally:
                if ro_src.exists():
                    _make_tree_writable(ro_src)

    def test_rejects_altered_locked_commit_and_manifest_sha256(self) -> None:
        # 1. Valid 40-hex commit different from LOCKED_MINIRUST_COMMIT fails.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            pin_path = root / "vendor/minirust/UPSTREAM_PIN.json"
            pin = json.loads(pin_path.read_text(encoding="utf-8"))
            pin["commit"] = "a" * 40
            pin_path.write_text(
                json.dumps(pin, indent=2) + "\n", encoding="utf-8"
            )
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("LOCKED_MINIRUST_COMMIT", res.stderr)

        # 2. Lockstep re-pin (file modified + files map + manifest_sha256
        # recomputed consistently) still fails against LOCKED_MINIRUST_MANIFEST.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            readme = root / "vendor/minirust/README.md"
            new_bytes = b"# Replaced upstream spec\n"
            readme.write_bytes(new_bytes)
            pin_path = root / "vendor/minirust/UPSTREAM_PIN.json"
            pin = json.loads(pin_path.read_text(encoding="utf-8"))
            pin["files"]["README.md"] = _sha256_bytes(new_bytes)
            pin["manifest_sha256"] = (
                check_minirust_pin._compute_manifest_sha256(pin["files"])
            )
            pin_path.write_text(
                json.dumps(pin, indent=2) + "\n", encoding="utf-8"
            )
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("LOCKED_MINIRUST_MANIFEST_SHA256", res.stderr)

        # 3. Valid 64-hex tarball_sha256 different from
        # LOCKED_MINIRUST_TARBALL_SHA256 fails, as do malformed digests, bad
        # schema_version, and duplicate JSON keys.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            pin_path = root / "vendor/minirust/UPSTREAM_PIN.json"
            orig_pin = json.loads(pin_path.read_text(encoding="utf-8"))

            for mutate, expected in (
                (
                    lambda p: p.update(tarball_sha256="b" * 64),
                    "LOCKED_MINIRUST_TARBALL_SHA256",
                ),
                (
                    lambda p: p.update(tarball_sha256="not-hex"),
                    "tarball_sha256 must be a 64-char lowercase hex SHA",
                ),
                (lambda p: p.update(schema_version=2), "schema_version"),
                (lambda p: p.update(schema_version=True), "schema_version"),
            ):
                bad = json.loads(json.dumps(orig_pin))
                mutate(bad)
                pin_path.write_text(
                    json.dumps(bad, indent=2) + "\n", encoding="utf-8"
                )
                res = self.run_cli("--repo-root", str(root))
                self.assertNotEqual(res.returncode, 0)
                self.assertIn(expected, res.stderr)

            pin_path.write_text(
                '{"schema_version": 1, "schema_version": 1}\n',
                encoding="utf-8",
            )
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("duplicate JSON key", res.stderr)

    def test_rejects_tampered_sha(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            target = root / "vendor/minirust/spec/lang/machine.md"
            target.write_text(
                target.read_text(encoding="utf-8") + "\ntampered\n",
                encoding="utf-8",
            )
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("SHA-256 mismatch", res.stderr)

    def test_rejects_extra_unpinned_file_and_stray_dir(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            (root / "vendor/minirust/EXTRA.txt").write_text(
                "stray\n", encoding="utf-8"
            )
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("extra unpinned file", res.stderr)

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            (root / "vendor/minirust/tooling").mkdir()
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("unpinned directory", res.stderr)

    def test_rejects_missing_pinned_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            (root / "vendor/minirust/spec/mem/basic.md").unlink()
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("missing pinned file", res.stderr)

    def test_rejects_forbidden_vendor_names_pinned_or_on_disk(self) -> None:
        forbidden_paths = (
            "Cargo.toml",
            "spec/Cargo.lock",
            "rust-toolchain.toml",
            "rust-toolchain",
            ".cargo/config.toml",
            "lean-toolchain",
            "lakefile",
            "lakefile.lean",
            "lakefile.toml",
            ".gitattributes",
            "build.rs",
            ".envrc",
        )
        for forbidden in forbidden_paths:
            with (
                self.subTest(pinned=forbidden),
                tempfile.TemporaryDirectory() as tmp,
            ):
                root = Path(tmp) / "anneal"
                populate_valid_repo(
                    root,
                    spec_files={
                        "README.md": "ok\n",
                        forbidden: "forbidden\n",
                    },
                )
                res = self.run_cli("--repo-root", str(root))
                self.assertNotEqual(res.returncode, 0)
                self.assertIn("forbidden ambient/build/toolchain", res.stderr)

            with (
                self.subTest(on_disk=forbidden),
                tempfile.TemporaryDirectory() as tmp,
            ):
                root = Path(tmp) / "anneal"
                populate_valid_repo(root)
                target = root / "vendor/minirust" / forbidden
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text("forbidden\n", encoding="utf-8")
                res = self.run_cli("--repo-root", str(root))
                self.assertNotEqual(res.returncode, 0)
                self.assertIn("forbidden ambient/build/toolchain", res.stderr)

    def test_rejects_symlinks_in_vendor_tree(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            (root / "vendor/minirust/link.md").symlink_to("README.md")
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("symlink forbidden", res.stderr)

        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            real_root = tmp_path / "real"
            populate_valid_repo(real_root)
            fake_root = tmp_path / "fake"
            (fake_root / "vendor").mkdir(parents=True)
            (fake_root / "vendor/minirust").symlink_to(
                real_root / "vendor/minirust"
            )
            res = self.run_cli("--repo-root", str(fake_root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("expected regular directory", res.stderr)

    def test_rejects_unreadable_dir_and_bad_manifest_digest(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            pin_path = root / "vendor/minirust/UPSTREAM_PIN.json"
            pin = json.loads(pin_path.read_text(encoding="utf-8"))
            pin["manifest_sha256"] = "0" * 64
            pin_path.write_text(
                json.dumps(pin, indent=2) + "\n", encoding="utf-8"
            )
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("manifest_sha256 mismatch", res.stderr)

        if os.geteuid() != 0:
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp) / "anneal"
                populate_valid_repo(root)
                hidden = root / "vendor/minirust/spec/hidden"
                hidden.mkdir()
                (hidden / "escape.md").symlink_to("/etc/passwd")
                hidden.chmod(0o000)
                try:
                    res = self.run_cli("--repo-root", str(root))
                    self.assertNotEqual(res.returncode, 0)
                    self.assertIn("cannot traverse", res.stderr)
                finally:
                    hidden.chmod(0o755)
