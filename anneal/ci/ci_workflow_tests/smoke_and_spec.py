# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Static check, installed smoke, and `tools/anneal-spec` check modes."""

from .support import (
    Path,
    REPO_ROOT,
    subprocess,
    tempfile,
)


class SmokeAndSpecCases:
    """Check-mode tests of `CiWorkflowManifestGuardTests`."""

    def _runner_mode(self, mode):
        idx = self.runner_script.index(f"  {mode})\n")
        end = self.runner_script.index("\n    ;;", idx)
        return self.runner_script[idx:end]

    def test_static_checks_enforce_wasm32_core_and_offline_inspect(self):
        # `#4220`: the pure `cargo_anneal::core` must keep building for
        # `wasm32-unknown-unknown` with `-D warnings`, and the offline
        # `inspect` CLI must be linted and tested without default features.
        clippy = self._runner_mode("clippy")
        self.assertIn(
            'RUSTFLAGS="-D warnings" cargo check --locked --offline', clippy
        )
        self.assertIn("--lib --target wasm32-unknown-unknown", clippy)
        self.assertIn("--test cli --test inspect", clippy)
        ws_meta = self._runner_mode("ws-meta")
        self.assertIn("--test cli --test inspect", ws_meta)

    def test_installed_smoke_package_stages_generated_bundle_in_scratch(self):
        # `#4244` and `#4341` generate `bundled_resources.rs` and
        # `bundled_theory.json` in `build.rs`, so `cargo package` needs both
        # staged under `packaged/`. The read-only checkout must stay
        # untouched: staging happens only in a scratch copy, must stage
        # exactly those two files, and must use the same optimization flags
        # as the other Cargo invocations.
        idx = self.runner_script.index("  installed-smoke)\n")
        end = self.runner_script.index("\n    ;;", idx)
        window = self.runner_script[idx:end]
        stage_start = window.index('PKG_SRC="${SCRATCH_ROOT}/package-src"')
        stage_end = window.index('rm -rf "$PKG_SRC"\n    PREPARED_MANIFEST=')
        stage = window[stage_start:stage_end]
        self.assertIn('cp -a . "$PKG_SRC/anneal"', stage)
        self.assertIn('cd "$PKG_SRC/anneal"', stage)
        self.assertIn("test ! -e trusted/cargo-anneal/packaged", stage)
        self.assertIn("-- --root . --stage-package", stage)
        self.assertIn(
            'staged="$(cd trusted/cargo-anneal/packaged && '
            'find . -mindepth 1 | LC_ALL=C sort)"',
            stage,
        )
        self.assertIn(
            "expected_staged=\"$(printf './bundled_resources.rs\\n"
            "./bundled_theory.json')\"",
            stage,
        )
        self.assertIn('test "$staged" = "$expected_staged"', stage)
        self.assertLess(
            stage.index("--stage-package"),
            stage.index("cargo package --allow-dirty"),
        )
        self.assertEqual(stage.count('"${FULL_OPT_ARGS[@]}"'), 2)
        # The checked-in generated file is gone; provenance comes from the
        # shared renderer invoked via `pack_omnibus_archive.sh` instead of
        # scraping Rust source.
        self.assertIn("build_omnibus_archive", window)
        self.assertIn("ci/pack_omnibus_archive.sh", self.runner_script)
        self.assertNotIn("src/bundled_resources.rs", self.runner_script)
        self.assertNotIn("src/bundled_resources.rs", self.pack_script)
        self.assertIn("ci/render_correspondence_provenance.py", self.pack_script)


    def test_installed_smoke_verifies_anneal_spec_units_in_bwrap(self):
        # The untrusted `tools/anneal-spec` lowering is built from its own
        # locked workspace and run against the installed toolchain inside a
        # fresh sandbox that sees the checkout read-only.
        smoke = self._runner_mode("installed-smoke")
        start = smoke.index('SPEC_TARGET="${SCRATCH_ROOT}/anneal-spec-target"')
        end = smoke.index('rm -rf "$SPEC_TARGET" "$SPEC_CARGO_HOME"\n', start)
        window = smoke[start:end]
        self.assertLess(smoke.index("ci/verify_zerocopy.py"), start)
        # The build itself runs in its own sandbox, before the verifier's,
        # with no access to the installed tools or the rest of the scratch
        # root.
        build_end = window.index(
            '"$SPEC_CARGO" build --locked --offline -p anneal-spec-lower'
        )
        build = window[window.index("bwrap --unshare-all"):build_end]
        self.assertIn("--clearenv --cap-drop ALL", build)
        # `apply_bundle_env` points `RUSTC` into the unmounted installed
        # bundle, so the build must name the image's toolchain explicitly.
        self.assertIn("SPEC_RUSTC=/opt/anneal-nix/build-rustc\n", window)
        self.assertIn(
            "SPEC_CARGO=/opt/anneal-nix/rust-toolchain/bin/cargo\n", window
        )
        self.assertIn('--setenv RUSTC "$SPEC_RUSTC"', build)
        self.assertIn("--ro-bind /opt/anneal-nix /opt/anneal-nix", build)
        self.assertNotIn("${RUSTC", build)
        self.assertNotIn("command -v", window)
        self.assertIn('--chdir "$PWD/tools/anneal-spec"', build)
        self.assertIn('--bind "$SPEC_TARGET" /target', build)
        self.assertIn("--ro-bind /opt/anneal-cargo-vendor", build)
        self.assertNotIn("ANNEAL_TEST_", build)
        self.assertNotIn("SCRATCH_ROOT", build)
        self.assertLess(
            build_end, window.index("ci/verify_anneal_spec_zerocopy.py")
        )
        self.assertIn("bwrap --unshare-all --die-with-parent", window)
        self.assertIn("--clearenv --cap-drop ALL", window)
        self.assertIn('--ro-bind "$REPO_ROOT" "$REPO_ROOT"', window)
        self.assertIn('--ro-bind "$SPEC_TARGET" "$SPEC_TARGET"', window)
        self.assertIn("ci/verify_anneal_spec_zerocopy.py", window)
        self.assertIn('--lower "$SPEC_TARGET/debug/anneal-spec-lower"', window)
        self.assertIn('--jobs "$ANNEAL_TEST_JOBS"', window)

    def test_tools_anneal_spec_check_is_scoped_and_offline(self):
        checks = {c["id"]: c for c in self.checks_cfg["checks"]}
        check = checks["tools-anneal-spec"]
        self.assertEqual(
            check["command"], ["./ci/scripts/run_anneal_spec_check.sh"]
        )
        self.assertEqual(check["caches"], ["anneal-spec-cargo-v1"])
        self.assertEqual(
            self.checks_cfg["caches"]["anneal-spec-cargo-v1"]["cargo_locked"],
            {"workspace": "anneal/tools/anneal-spec/Cargo.toml"},
        )
        self.assertIn(
            {
                "kind": "cargo_workspace",
                "manifest_path": "anneal/tools/anneal-spec/Cargo.toml",
            },
            check["inputs"],
        )
        ci_test_globs = [
            glob
            for entry in checks["anneal-ci-tests"]["inputs"]
            for glob in entry.get("include", [])
        ]
        self.assertIn("ci/scripts/run_anneal_spec_check.sh", ci_test_globs)
        script = (REPO_ROOT / "ci/scripts/run_anneal_spec_check.sh").read_text()
        self.assertIn("export CARGO_NET_OFFLINE=true", script)
        for needle in (
            "clippy --locked --offline --workspace --all-targets",
            "test --locked --offline --workspace",
            '--src-root . --check "$unit" "$unit/spec.rs"',
        ):
            self.assertIn(needle, script)
        # Inline specifications live in `zerocopy/src`. The verifier checks
        # `spec_sources.json` units in installed-smoke, and this check's
        # golden tests lower them too, so both must rerun when it changes.
        for check_id in ("anneal-installed-smoke", "tools-anneal-spec"):
            globs = [
                glob
                for entry in checks[check_id]["inputs"]
                for glob in entry.get("include", [])
            ]
            self.assertIn("zerocopy/src/**", globs, check_id)
            # Both lower inline specifications against the generated modules
            # checked in under `zerocopy/proofs`.
            self.assertIn("zerocopy/proofs/**", globs, check_id)

    def test_tools_anneal_scaffold_check_is_scoped_and_offline(self):
        checks = {c["id"]: c for c in self.checks_cfg["checks"]}
        check = checks["tools-anneal-scaffold"]
        self.assertEqual(
            check["command"], ["./ci/scripts/run_anneal_scaffold_check.sh"]
        )
        self.assertEqual(check["caches"], ["anneal-scaffold-cargo-v1"])
        self.assertEqual(
            self.checks_cfg["caches"]["anneal-scaffold-cargo-v1"]["cargo_locked"],
            {"workspace": "anneal/tools/anneal-scaffold/Cargo.toml"},
        )
        self.assertIn(
            {
                "kind": "cargo_workspace",
                "manifest_path": "anneal/tools/anneal-scaffold/Cargo.toml",
            },
            check["inputs"],
        )
        globs = [
            glob for entry in check["inputs"] for glob in entry.get("include", [])
        ]
        # The unit tests read these trusted sources to catch drift.
        for path in (
            "anneal/trusted/rustc-capture/src/ir.rs",
            "anneal/trusted/rustc-capture/src/lean.rs",
            "anneal/trusted/cargo-anneal/src/verify.rs",
        ):
            self.assertIn(path, globs)
        ci_test_globs = [
            glob
            for entry in checks["anneal-ci-tests"]["inputs"]
            for glob in entry.get("include", [])
        ]
        self.assertIn("ci/scripts/run_anneal_scaffold_check.sh", ci_test_globs)
        script = (REPO_ROOT / "ci/scripts/run_anneal_scaffold_check.sh").read_text()
        self.assertIn("export CARGO_NET_OFFLINE=true", script)
        for needle in (
            "clippy --locked --offline --workspace --all-targets",
            "test --locked --offline --workspace",
        ):
            self.assertIn(needle, script)

    def test_tools_anneal_cpp_check_is_scoped_and_offline(self):
        checks = {c["id"]: c for c in self.checks_cfg["checks"]}
        check = checks["tools-anneal-cpp"]
        self.assertEqual(
            check["command"], ["./ci/scripts/run_anneal_cpp_check.sh"]
        )
        self.assertEqual(check["caches"], ["anneal-cpp-cargo-v1"])
        self.assertEqual(
            self.checks_cfg["caches"]["anneal-cpp-cargo-v1"]["cargo_locked"],
            {"workspace": "anneal/tools/anneal-cpp/Cargo.toml"},
        )
        self.assertIn(
            {
                "kind": "cargo_workspace",
                "manifest_path": "anneal/tools/anneal-cpp/Cargo.toml",
            },
            check["inputs"],
        )
        globs = [
            glob for entry in check["inputs"] for glob in entry.get("include", [])
        ]
        self.assertIn("anneal/tools/anneal-cpp/lower-cpp/tests/**", globs)
        ci_test_globs = [
            glob
            for entry in checks["anneal-ci-tests"]["inputs"]
            for glob in entry.get("include", [])
        ]
        self.assertIn("ci/scripts/run_anneal_cpp_check.sh", ci_test_globs)
        script = (REPO_ROOT / "ci/scripts/run_anneal_cpp_check.sh").read_text()
        self.assertIn("export CARGO_NET_OFFLINE=true", script)
        for needle in (
            "clippy --locked --offline --workspace --all-targets",
            "test --locked --offline --workspace",
        ):
            self.assertIn(needle, script)

    def test_tools_anneal_spec_freshness_skips_spec_sources_units(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            units = root / "anneal/tools/anneal-spec/tests/zerocopy"
            for name in ("01_companion", "02_inline", "03_inline_link"):
                (units / name).mkdir(parents=True)
            (units / "01_companion/spec.rs").write_text("")
            (units / "02_inline/spec_sources.json").write_text(
                '{"files": ["--help"]}'
            )
            (units / "03_inline_link/spec_sources.json").symlink_to(
                root / "missing.json"
            )
            log = root / "cargo.log"
            stub = root / "bin/cargo"
            stub.parent.mkdir()
            stub.write_text(
                '#!/usr/bin/env bash\nprintf \'%s\\n\' "$*" >> "$CARGO_LOG"\n'
            )
            stub.chmod(0o755)
            script = REPO_ROOT / "ci/scripts/run_anneal_spec_check.sh"
            res = subprocess.run(
                ["/bin/bash", str(script)],
                cwd=root,
                env={
                    "PATH": f"{stub.parent}:/usr/bin:/bin",
                    "HOME": str(root),
                    "CARGO_LOG": str(log),
                    "PIN_RUST_TOOLCHAINS__STABLE": "1.0.0",
                },
                capture_output=True,
                text=True,
                timeout=60,
                check=False,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            runs = [
                line
                for line in log.read_text().splitlines()
                if line.startswith("+1.0.0 run ")
            ]
            self.assertEqual(
                runs,
                [
                    "+1.0.0 run --locked --offline -q -p anneal-spec-lower -- "
                    "--src-root . --check tests/zerocopy/01_companion "
                    "tests/zerocopy/01_companion/spec.rs"
                ],
            )


    def test_tools_anneal_spec_freshness_allows_no_companion_units(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "anneal/tools/anneal-spec").mkdir(parents=True)
            log = root / "cargo.log"
            stub = root / "bin/cargo"
            stub.parent.mkdir()
            stub.write_text(
                '#!/usr/bin/env bash\nprintf \'%s\\n\' "$*" >> "$CARGO_LOG"\n'
            )
            stub.chmod(0o755)
            script = REPO_ROOT / "ci/scripts/run_anneal_spec_check.sh"
            res = subprocess.run(
                ["/bin/bash", str(script)],
                cwd=root,
                env={
                    "PATH": f"{stub.parent}:/usr/bin:/bin",
                    "HOME": str(root),
                    "CARGO_LOG": str(log),
                    "PIN_RUST_TOOLCHAINS__STABLE": "1.0.0",
                },
                capture_output=True,
                text=True,
                timeout=60,
                check=False,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertFalse(
                [l for l in log.read_text().splitlines() if l.startswith("+1.0.0 run ")]
            )
