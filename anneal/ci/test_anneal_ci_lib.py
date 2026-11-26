#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `anneal/ci/anneal_ci_lib.py`."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

_CI_DIR = Path(__file__).resolve().parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))

import anneal_ci_lib  # noqa: E402


class AnnealCiLibTests(unittest.TestCase):
    def test_sha256_helpers_and_symlink_rejection(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            target = root / "sample.bin"
            payload = b"anneal-shared-lib-test\n"
            target.write_bytes(payload)
            expected = hashlib.sha256(payload).hexdigest()

            self.assertEqual(anneal_ci_lib.sha256_bytes(payload), expected)
            self.assertEqual(anneal_ci_lib.sha256_file(target), expected)
            self.assertEqual(
                anneal_ci_lib.sha256_file(target, reject_symlink=True),
                expected,
            )

            link = root / "sample.link"
            link.symlink_to(target)
            with self.assertRaises(RuntimeError):
                anneal_ci_lib.sha256_file(
                    link,
                    reject_symlink=True,
                    missing_label="fixture",
                    exc_type=RuntimeError,
                )

    def test_atomic_write_text_mode_symlink_guard_and_cleanup(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            out = root / "nested" / "config.json"
            anneal_ci_lib.atomic_write_text(out, '{"ok": true}\n', mode=0o600)
            self.assertEqual(out.read_text(encoding="utf-8"), '{"ok": true}\n')
            self.assertEqual(out.stat().st_mode & 0o777, 0o600)
            # Atomic write leaves no temporary staging files behind.
            self.assertEqual([p.name for p in out.parent.iterdir()], ["config.json"])

            sym = root / "nested" / "sym.json"
            sym.symlink_to(out)
            with self.assertRaises(ValueError):
                anneal_ci_lib.atomic_write_text(sym, "nope\n", exc_type=ValueError)

    def test_discover_tools_and_resolve_cli_tools(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            anneal_root = root / "anneal"
            install_root = root / "install"
            target_dir = anneal_root / "target"
            (target_dir / "release").mkdir(parents=True)
            (install_root / "bin").mkdir(parents=True)
            (install_root / "rust").mkdir(parents=True)
            (install_root / "lean" / "bin").mkdir(parents=True)

            cli_rel = target_dir / "release" / "cargo-anneal"
            cli_rel.write_text("cli", encoding="utf-8")
            cap_inst = install_root / "bin" / "anneal-rustc-capture"
            cap_inst.write_text("cap", encoding="utf-8")
            lean_inst = install_root / "lean" / "bin" / "lean"
            lean_inst.write_text("lean", encoding="utf-8")
            aud_dbg = target_dir / "debug" / "anneal-audit"
            aud_dbg.parent.mkdir(parents=True)
            aud_dbg.write_text("aud", encoding="utf-8")

            env_keys = (
                "CARGO_TARGET_DIR",
                "ANNEAL_CLI",
                "ANNEAL_TEST_CARGO_ANNEAL",
                "ANNEAL_CAPTURE",
                "ANNEAL_SYSROOT",
                "ANNEAL_TEST_RUST_SYSROOT",
                "ANNEAL_LEAN",
                "ANNEAL_TEST_INSTALL_ROOT",
            )
            with mock.patch.dict(os.environ, {}, clear=False):
                for key in env_keys:
                    os.environ.pop(key, None)

                discovered = anneal_ci_lib.discover_tools(
                    anneal_root,
                    install_root=install_root,
                    defaults_fn=lambda _root: {
                        "cli": None,
                        "capture": None,
                        "sysroot": None,
                        "lean": None,
                    },
                )
                self.assertEqual(discovered["cli"], cli_rel.resolve())
                self.assertEqual(discovered["capture"], cap_inst.resolve())
                self.assertEqual(
                    discovered["sysroot"], (install_root / "rust").resolve()
                )
                self.assertEqual(discovered["lean"], lean_inst.resolve())
                self.assertEqual(discovered["auditor"], aud_dbg.resolve())

                # Exporting CARGO_TARGET_DIR redirects default target lookup,
                # while explicit target_dir takes precedence over the env var.
                override_target = root / "override-target"
                override_cli = override_target / "debug" / "cargo-anneal"
                override_cli.parent.mkdir(parents=True)
                override_cli.write_text("override-cli", encoding="utf-8")
                os.environ["CARGO_TARGET_DIR"] = str(override_target)
                overridden = anneal_ci_lib.discover_tools(
                    anneal_root,
                    install_root=install_root,
                    defaults_fn=lambda _root: {
                        "cli": None,
                        "capture": None,
                        "sysroot": None,
                        "lean": None,
                    },
                )
                self.assertEqual(overridden["cli"], override_cli.resolve())
                explicit_target = anneal_ci_lib.discover_tools(
                    anneal_root,
                    install_root=install_root,
                    target_dir=target_dir,
                    defaults_fn=lambda _root: {
                        "cli": None,
                        "capture": None,
                        "sysroot": None,
                        "lean": None,
                    },
                )
                self.assertEqual(explicit_target["cli"], cli_rel.resolve())
                os.environ.pop("CARGO_TARGET_DIR", None)

                calls = {"count": 0}

                def counting_defaults(_root: Path) -> dict[str, Path | None]:
                    calls["count"] += 1
                    return {
                        "cli": cli_rel,
                        "capture": cap_inst,
                        "sysroot": install_root / "rust",
                        "lean": lean_inst,
                    }

                args_full = argparse.Namespace(
                    cli=cli_rel,
                    capture=cap_inst,
                    sysroot=install_root / "rust",
                    lean=lean_inst,
                )
                anneal_ci_lib.resolve_cli_tools(
                    anneal_root,
                    args_full,
                    defaults_fn=counting_defaults,
                )
                self.assertEqual(calls["count"], 0)

                args_partial = argparse.Namespace(
                    cli=None,
                    capture=None,
                    sysroot=None,
                    lean=None,
                )
                os.environ["ANNEAL_TEST_INSTALL_ROOT"] = str(install_root)
                os.environ["ANNEAL_CLI"] = str(cli_rel)
                resolved = anneal_ci_lib.resolve_cli_tools(
                    anneal_root,
                    args_partial,
                    defaults_fn=counting_defaults,
                )
                self.assertEqual(calls["count"], 0)
                self.assertEqual(resolved["cli"], cli_rel)
                self.assertEqual(resolved["capture"], cap_inst)
                self.assertEqual(resolved["sysroot"], install_root / "rust")
                self.assertEqual(resolved["lean"], lean_inst)

    def test_run_cargo_anneal_verify_preserves_dot_log_prefix_and_validates(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            logs_dir = root / "logs"
            log_prefix = logs_dir / "01.unit"
            receipt_payload = {
                "schema_version": 3,
                "status": "selected_unit_verified",
                "taint_reasons": [],
                "elaboration_sandbox": "linux_bwrap",
                "deferred": [],
            }
            captured: dict[str, object] = {}

            def fake_runner(
                cmd: list[str],
                *,
                cwd: Path,
                env: dict[str, str] | None,
                timeout: float,
            ) -> subprocess.CompletedProcess[str]:
                captured["cmd"] = cmd
                captured["cwd"] = cwd
                captured["env"] = env
                captured["timeout"] = timeout
                return subprocess.CompletedProcess(
                    cmd,
                    0,
                    stdout=json.dumps(receipt_payload),
                    stderr="diag stderr\n",
                )

            proc, parsed = anneal_ci_lib.run_cargo_anneal_verify(
                cli=root / "cargo-anneal",
                request_path=root / "req.json",
                cwd=root,
                capture=root / "cap",
                sysroot=root / "rust",
                lean=root / "lean",
                artifacts_dir=root / "art",
                extra_flags=["--json"],
                env={
                    "KEEP": "1",
                    "ACTIONS_RUNTIME_TOKEN": "secret-runtime",
                    "ACTIONS_ID_TOKEN_REQUEST_TOKEN": "secret-oidc",
                },
                timeout=42.0,
                runner=fake_runner,
                log_prefix=log_prefix,
                label="dot.unit",
            )
            self.assertEqual(proc.returncode, 0)
            self.assertEqual(parsed, receipt_payload)
            self.assertEqual(
                captured["cmd"][:4],
                [str(root / "cargo-anneal"), "verify", "--format", "json"],
            )
            self.assertEqual(captured["env"], {"KEEP": "1"})
            self.assertEqual(
                (logs_dir / "01.unit.stdout").read_text(encoding="utf-8"),
                json.dumps(receipt_payload),
            )
            self.assertEqual(
                (logs_dir / "01.unit.stderr").read_text(encoding="utf-8"),
                "diag stderr\n",
            )
            self.assertFalse((logs_dir / "01.stdout").exists())
            self.assertEqual(
                anneal_ci_lib.validate_receipt_v3_envelope(parsed, returncode=0),
                [],
            )

            bad = dict(receipt_payload)
            bad["tainted"] = False
            bad["taint_reasons"] = ["unsound"]
            bad["elaboration_sandbox"] = "none"
            bad["deferred"] = ["hostile Lean elaborator effects"]
            reasons = anneal_ci_lib.validate_receipt_v3_envelope(bad, returncode=1)
            self.assertTrue(any("exit=1" in r for r in reasons))
            self.assertTrue(any("tainted" in r for r in reasons))
            self.assertTrue(any("taint_reasons" in r for r in reasons))
            self.assertTrue(any("elaboration_sandbox" in r for r in reasons))
            self.assertTrue(any("hostile" in r for r in reasons))

            def bad_json_runner(
                cmd: list[str],
                *,
                cwd: Path,
                env: dict[str, str] | None,
                timeout: float,
            ) -> subprocess.CompletedProcess[str]:
                return subprocess.CompletedProcess(cmd, 2, stdout="not-json", stderr="boom")

            with self.assertRaises(RuntimeError):
                anneal_ci_lib.run_cargo_anneal_verify(
                    cli=root / "cargo-anneal",
                    request_path=root / "req.json",
                    cwd=root,
                    runner=bad_json_runner,
                    log_prefix=logs_dir / "02.unit",
                )
            self.assertEqual(
                (logs_dir / "02.unit.stderr").read_text(encoding="utf-8"),
                "boom",
            )

    def test_workflow_repo_fixture_git_bash_and_cleanup(self) -> None:
        fixture_root: Path
        with anneal_ci_lib.WorkflowRepoFixture(prefix="anneal-lib-test-") as fx:
            fixture_root = fx.root
            self.assertTrue(fixture_root.is_dir())
            remote = fx.init_repo("remote.git", bare=True)
            work = fx.init_repo("work", initial_branch="main")
            fx.write_file("work/hello.txt", "world\n")
            sha = fx.commit_all(work, "initial commit")
            fx.git(work, "remote", "add", "origin", remote.as_uri())
            fx.git(work, "push", "-q", "origin", "main")

            clone = fx.clone_repo(remote, "clone", branch="main", depth=1)
            self.assertEqual((clone / "hello.txt").read_text(encoding="utf-8"), "world\n")
            self.assertEqual(fx.git(clone, "rev-parse", "HEAD").stdout.strip(), sha)

            kv = fx.write_file("out.env", "KEY=val=ue\n")
            self.assertEqual(fx.parse_kv_file(kv), {"KEY": "val=ue"})
            bad_kv = fx.write_file("bad.env", "KEY=ok\nMALFORMED\n")
            with self.assertRaises(ValueError):
                fx.parse_kv_file(bad_kv)
            self.assertEqual(fx.parse_kv_file(bad_kv, strict=False), {"KEY": "ok"})
            res = fx.run_bash("printf '%s' ok")
            self.assertEqual(res.returncode, 0)
            self.assertEqual(res.stdout, "ok")

        self.assertFalse(fixture_root.exists())

    def test_run_cargo_anneal_verify_streams_raw_logs_on_timeout(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            slow_cli = root / "slow-cli"
            slow_cli.write_text(
                "#!/usr/bin/env python3\n"
                "import sys, time\n"
                "sys.stdout.write('partial-out\\n'); sys.stdout.flush()\n"
                "sys.stderr.write('partial-err\\n'); sys.stderr.flush()\n"
                "time.sleep(5)\n",
                encoding="utf-8",
            )
            slow_cli.chmod(0o755)
            log_prefix = root / "logs/timeout.unit"
            with self.assertRaises(subprocess.TimeoutExpired):
                anneal_ci_lib.run_cargo_anneal_verify(
                    cli=slow_cli,
                    request_path=root / "req.json",
                    cwd=root,
                    timeout=0.3,
                    log_prefix=log_prefix,
                )
            self.assertEqual(
                (root / "logs/timeout.unit.stdout").read_text(encoding="utf-8"),
                "partial-out\n",
            )
            self.assertEqual(
                (root / "logs/timeout.unit.stderr").read_text(encoding="utf-8"),
                "partial-err\n",
            )

    def test_run_cargo_anneal_verify_rejects_invalid_utf8_stdout(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            bad_cli = root / "bad-utf8-cli"
            raw_payload = b'{"status":"selected_unit_verified","note":"\xff"}\n'
            bad_cli.write_text(
                "#!/usr/bin/env python3\n"
                "import sys\n"
                f"sys.stdout.buffer.write({raw_payload!r})\n"
                "sys.stdout.buffer.flush()\n"
                "sys.stderr.buffer.write(b'diag \\xfe err\\n')\n"
                "sys.stderr.buffer.flush()\n",
                encoding="utf-8",
            )
            bad_cli.chmod(0o755)
            log_prefix = root / "logs/badutf8.unit"
            with self.assertRaisesRegex(
                RuntimeError, "invalid UTF-8 receipt stdout"
            ):
                anneal_ci_lib.run_cargo_anneal_verify(
                    cli=bad_cli,
                    request_path=root / "req.json",
                    cwd=root,
                    log_prefix=log_prefix,
                    label="badutf8.unit",
                )
            # Raw stdout and stderr bytes remain persisted for diagnostics.
            self.assertEqual(
                (root / "logs/badutf8.unit.stdout").read_bytes(), raw_payload
            )
            self.assertEqual(
                (root / "logs/badutf8.unit.stderr").read_bytes(),
                b"diag \xfe err\n",
            )

            with self.assertRaisesRegex(
                RuntimeError, "invalid UTF-8 receipt stdout"
            ):
                anneal_ci_lib.run_cargo_anneal_verify(
                    cli=bad_cli,
                    request_path=root / "req.json",
                    cwd=root,
                    log_prefix=None,
                    label="badutf8.inline",
                )

    def test_verify_starnix_e2e_standalone_fetch_only_without_ci_lib(self) -> None:
        source_script = _CI_DIR / "verify_starnix_e2e.py"
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            ci_dir = root / "anneal/ci"
            ci_dir.mkdir(parents=True)
            standalone = ci_dir / "verify_starnix_e2e.py"
            standalone.write_text(
                source_script.read_text(encoding="utf-8"), encoding="utf-8"
            )
            help_proc = subprocess.run(
                [sys.executable, "-I", "-B", str(standalone), "--help"],
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(help_proc.returncode, 0, msg=help_proc.stderr)

            fixture_dir = (
                root / "anneal/tests/cargo-anneal/tests/fixtures/starnix"
            )
            fixture_dir.mkdir(parents=True)
            src_dir = root / "cached_src"
            src_dir.mkdir()
            sample = b"fn sample() {}\n"
            (src_dir / "api.rs").write_bytes(sample)
            (fixture_dir / "source.json").write_text(
                json.dumps(
                    {
                        "revision": "deadbeef",
                        "source_path": "src/starnix",
                        "files": {
                            "api.rs": hashlib.sha256(sample).hexdigest(),
                        },
                    }
                ),
                encoding="utf-8",
            )
            dest = root / "fetched"
            fetch_proc = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(standalone),
                    "--fetch-only",
                    str(dest),
                    "--source-dir",
                    str(src_dir),
                ],
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(fetch_proc.returncode, 0, msg=fetch_proc.stderr)
            self.assertEqual((dest / "api.rs").read_bytes(), sample)

    def test_strip_actions_env_runtime_and_oidc(self) -> None:
        source = {
            "PATH": "/usr/bin",
            "ACTIONS_CACHE_URL": "https://cache.example",
            "ACTIONS_RESULTS_URL": "https://results.example",
            "ACTIONS_RUNTIME_TOKEN": "secret-runtime",
            "ACTIONS_RUNTIME_URL": "https://runtime.example",
            "ACTIONS_ID_TOKEN_REQUEST_URL": "https://oidc.example",
            "ACTIONS_ID_TOKEN_REQUEST_TOKEN": "secret-oidc",
            "KEEP_ME": "1",
        }
        snapshot = dict(source)
        stripped = anneal_ci_lib.strip_actions_env(source)
        self.assertEqual(source, snapshot)
        for key in anneal_ci_lib.ACTIONS_ENV_TOKENS:
            self.assertNotIn(key, stripped)
        for key in anneal_ci_lib.ACTIONS_OIDC_TOKENS:
            self.assertIn(key, stripped)
        self.assertEqual(stripped["KEEP_ME"], "1")

        stripped_all = anneal_ci_lib.strip_actions_env(source, include_oidc=True)
        for key in anneal_ci_lib.ACTIONS_ENV_TOKENS + anneal_ci_lib.ACTIONS_OIDC_TOKENS:
            self.assertNotIn(key, stripped_all)
        self.assertEqual(stripped_all["KEEP_ME"], "1")

    def test_discover_local_defaults_prefers_newest_cached_lean_by_mtime(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            home = root / "home"
            xdg = root / "xdg"
            anneal_root = root / "anneal"
            home.mkdir()
            anneal_root.mkdir()

            tc_root = xdg / "anneal/toolchain"
            tc_old = tc_root / "tc_old"
            tc_new = tc_root / "tc_new"
            old_lean = tc_old / "lean/bin/lean"
            new_lean = tc_new / "lean/bin/lean"
            for lean_bin in (old_lean, new_lean):
                lean_bin.parent.mkdir(parents=True)
                lean_bin.write_text("#!/bin/sh\n", encoding="utf-8")

            # Set directory mtimes after creating children so `tc_new` is newer.
            os.utime(tc_old, (1000.0, 1000.0))
            os.utime(tc_new, (2000.0, 2000.0))

            elan_lean = (
                home / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
            )
            elan_lean.parent.mkdir(parents=True)
            elan_lean.write_text("#!/bin/sh\n", encoding="utf-8")

            with (
                mock.patch.dict(
                    os.environ, {"XDG_CACHE_HOME": str(xdg)}, clear=False
                ),
                mock.patch.object(Path, "home", return_value=home),
                mock.patch("subprocess.check_output", side_effect=OSError),
            ):
                os.environ.pop("CARGO_TARGET_DIR", None)
                defaults = anneal_ci_lib.discover_local_defaults(anneal_root)
                self.assertEqual(defaults["lean"], new_lean)

    def test_validate_receipt_v3_envelope_rejects_wrong_schema_version(self) -> None:
        base = {
            "schema_version": 3,
            "status": "selected_unit_verified",
            "taint_reasons": [],
            "elaboration_sandbox": "linux_bwrap",
            "deferred": [],
        }
        self.assertEqual(
            anneal_ci_lib.validate_receipt_v3_envelope(base, returncode=0), []
        )
        for bad_version in (2, 4, "3", None, True, 3.0):
            with self.subTest(schema_version=bad_version):
                bad = dict(base, schema_version=bad_version)
                reasons = anneal_ci_lib.validate_receipt_v3_envelope(
                    bad, returncode=0
                )
                self.assertTrue(
                    any("schema_version=" in r for r in reasons), reasons
                )
        bad_def = dict(base, deferred=[{}])
        def_reasons = anneal_ci_lib.validate_receipt_v3_envelope(
            bad_def, returncode=0
        )
        self.assertTrue(any("deferred=" in r for r in def_reasons), def_reasons)

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            dup_file = root / "dup.json"
            dup_file.write_text('{"a": 1, "a": 2}\n', encoding="utf-8")
            with self.assertRaisesRegex(RuntimeError, "duplicate JSON key"):
                anneal_ci_lib.load_strict_json_object(dup_file, "dup test")
            sym_file = root / "sym.json"
            good_file = root / "good.json"
            good_file.write_text('{"ok": 1}\n', encoding="utf-8")
            sym_file.symlink_to(good_file)
            with self.assertRaisesRegex(RuntimeError, "regular non-symlink"):
                anneal_ci_lib.load_strict_json_object(sym_file, "sym test")
            self.assertEqual(
                anneal_ci_lib.load_strict_json_object(good_file, "good test"),
                {"ok": 1},
            )

    def test_negative_consumers_refuse_resource_limit_proof_failed(self) -> None:
        import probe_alpha
        import verify_starnix_e2e

        ordinary = {
            "schema_version": 3,
            "status": "proof_failed",
            "phase": "audit",
            "taint_reasons": [],
            "elaboration_sandbox": "linux_bwrap",
            "detail": "type mismatch",
            "artifacts": None,
        }
        self.assertEqual(
            anneal_ci_lib.validate_receipt_v3_envelope(
                ordinary,
                returncode=1,
                expected_status="proof_failed",
                expected_returncode=1,
                check_deferred=False,
            ),
            [],
        )
        verify_starnix_e2e.validate_mutation_rejection(ordinary, "zero")
        probe_alpha.validate_proof_failed_receipt(ordinary)

        for reason in ("heartbeat_limit_exceeded", "recursion_depth_exceeded"):
            with self.subTest(reason=reason):
                limited = dict(ordinary, reason=reason)
                failures = anneal_ci_lib.validate_receipt_v3_envelope(
                    limited,
                    returncode=1,
                    expected_status="proof_failed",
                    expected_returncode=1,
                    check_deferred=False,
                )
                self.assertTrue(
                    any("resource-limit proof_failed" in f for f in failures),
                    failures,
                )
                with self.assertRaisesRegex(RuntimeError, "resource-limit proof_failed"):
                    verify_starnix_e2e.validate_mutation_rejection(limited, "zero")
                with self.assertRaisesRegex(RuntimeError, "resource-limit proof_failed"):
                    probe_alpha.validate_proof_failed_receipt(limited)

    def test_find_workflow_step_unique_missing_and_duplicate(self) -> None:
        wf = {
            "jobs": {
                "build": {
                    "steps": [
                        {"id": "checkout", "name": "Checkout"},
                        {"id": "dup_a", "name": "Repeated"},
                        {"id": "dup_b", "name": "Repeated"},
                        {"id": "shared_id", "name": "First"},
                        {"id": "shared_id", "name": "Second"},
                    ]
                }
            }
        }
        self.assertEqual(
            anneal_ci_lib.find_workflow_step(wf, "build", step_id="checkout"),
            {"id": "checkout", "name": "Checkout"},
        )
        self.assertEqual(
            anneal_ci_lib.find_workflow_step(wf, "build", step_name="First"),
            {"id": "shared_id", "name": "First"},
        )
        self.assertEqual(
            anneal_ci_lib.find_workflow_step(
                wf, "build", step_id="dup_b", step_name="Repeated"
            ),
            {"id": "dup_b", "name": "Repeated"},
        )
        with self.assertRaises(KeyError):
            anneal_ci_lib.find_workflow_step(wf, "build", step_id="missing")
        with self.assertRaises(KeyError):
            anneal_ci_lib.find_workflow_step(wf, "build", step_name="Repeated")
        with self.assertRaises(KeyError):
            anneal_ci_lib.find_workflow_step(wf, "build", step_id="shared_id")


if __name__ == "__main__":
    unittest.main()
