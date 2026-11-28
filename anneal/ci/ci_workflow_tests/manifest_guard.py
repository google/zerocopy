# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""The root TCB manifest guard and bundle environment parsing in
`run_anneal_check.sh`."""

from .support import (
    hashlib,
    Path,
    subprocess,
    tempfile,
)


class ManifestGuardCases:
    """Manifest guard tests of `CiWorkflowManifestGuardTests`."""

    def run_manifest_guard(self, mutate=None, *, parent_override=False):
        with tempfile.TemporaryDirectory(prefix="anneal-ci-guard-") as tmp:
            root = Path(tmp) / "repo"
            project = root / "anneal"
            (project / "trusted").mkdir(parents=True)
            cargo_toml = project / "Cargo.toml"
            cargo_toml.write_bytes(b"[workspace]\n")
            digest = hashlib.sha256(cargo_toml.read_bytes()).hexdigest()
            (project / "trusted/root-manifest.sha256").write_text(
                f"{digest}  Cargo.toml\n"
            )

            if mutate is not None:
                mutate(root if parent_override else project)

            snippet = (
                "set -euo pipefail\n"
                f"{self.manifest_fn}\n"
                "verify_root_tcb_manifest\n"
            )
            return subprocess.run(
                ["bash", "--noprofile", "--norc", "-c", snippet],
                cwd=project,
                capture_output=True,
                text=True,
            )

    def test_manifest_guard_runs_unconditionally_before_mode_dispatch(self):
        call_idx = self.runner_script.index("\nverify_root_tcb_manifest\n")
        case_idx = self.runner_script.index('\ncase "$MODE" in\n')
        self.assertLess(call_idx, case_idx)

    def test_clean_tree_passes_manifest_guard(self):
        res = self.run_manifest_guard()
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

    def test_root_override_paths_and_symlinks_fail_closed(self):
        cases = [
            ("cargo_dir", lambda r: (r / ".cargo").mkdir()),
            ("cargo_file", lambda r: (r / ".cargo").write_text("")),
            ("rust_toolchain", lambda r: (r / "rust-toolchain").write_text("nightly\n")),
            ("rust_toolchain_toml", lambda r: (r / "rust-toolchain.toml").write_text("")),
            ("gitmodules", lambda r: (r / ".gitmodules").write_text("")),
            ("valid_symlink_cargo", lambda r: (r / ".cargo").symlink_to("Cargo.toml")),
            (
                "valid_symlink_toolchain",
                lambda r: (r / "rust-toolchain.toml").symlink_to("Cargo.toml"),
            ),
            ("dangling_symlink_cargo", lambda r: (r / ".cargo").symlink_to("missing")),
            (
                "dangling_symlink_toolchain",
                lambda r: (r / "rust-toolchain").symlink_to("missing"),
            ),
            (
                "dangling_symlink_gitmodules",
                lambda r: (r / ".gitmodules").symlink_to("missing"),
            ),
        ]
        for parent_override in (False, True):
            for label, mutate in cases:
                with self.subTest(case=label, parent=parent_override):
                    res = self.run_manifest_guard(
                        mutate=mutate, parent_override=parent_override
                    )
                    self.assertNotEqual(res.returncode, 0)
                    self.assertIn(
                        "forbidden root config override:",
                        res.stdout + res.stderr,
                    )

    def test_trusted_tree_symlink_and_manifest_tamper_fail_closed(self):
        res_link = self.run_manifest_guard(
            mutate=lambda p: (p / "trusted/evil_link").symlink_to("../Cargo.toml")
        )
        self.assertNotEqual(res_link.returncode, 0)
        self.assertIn(
            "symlink in Anneal trusted tree:",
            res_link.stdout + res_link.stderr,
        )

        res_tamper = self.run_manifest_guard(
            mutate=lambda p: (p / "Cargo.toml").write_bytes(b"[workspace]\n# x\n")
        )
        self.assertNotEqual(res_tamper.returncode, 0)

    def test_apply_bundle_env_rejects_malformed_lines_and_preserves_spaces(self):
        with tempfile.TemporaryDirectory(prefix="anneal-bundle-env-") as tmp:
            root = Path(tmp)
            (root / "ci").mkdir()
            script = root / "ci/check_bundle_tree.py"

            def run_case(py_body: str):
                script.write_text(py_body)
                snippet = (
                    "set -euo pipefail\n"
                    f"{self.bundle_env_fn}\n"
                    "apply_bundle_env --demo\n"
                    'printf "%s" "${RUSTFLAGS:-}"\n'
                )
                return subprocess.run(
                    ["bash", "--noprofile", "--norc", "-c", snippet],
                    cwd=root,
                    capture_output=True,
                    text=True,
                )

            ok = run_case(
                'print("ANNEAL_SYSROOT=/opt/sysroot")\n'
                'print("RUSTFLAGS=-Lnative=/opt/path with spaces/lib")\n'
            )
            self.assertEqual(ok.returncode, 0, ok.stderr)
            self.assertEqual(ok.stdout, "-Lnative=/opt/path with spaces/lib")

            no_eq = run_case('print("MALFORMED_LINE")\n')
            self.assertNotEqual(no_eq.returncode, 0)
            self.assertIn("malformed check_bundle_tree.py line", no_eq.stderr)

            bad_key = run_case('print("bad-key=1")\n')
            self.assertNotEqual(bad_key.returncode, 0)
            self.assertIn("invalid check_bundle_tree.py env key", bad_key.stderr)

            exit_fail = run_case("import sys\nsys.exit(3)\n")
            self.assertNotEqual(exit_fail.returncode, 0)
