# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Miri UB oracle tests for bounded child runs, sysroot pin hardening, and the
Tier B gate."""

from __future__ import annotations

from .support import (
    io,
    json,
    oracle,
    oracle_archive,
    oracle_bounded,
    oracle_corpus,
    oracle_pins,
    os,
    Path,
    sys,
    tarfile,
    tempfile,
)


class BoundedRunAndTierBCases:
    """`ClassificationAndGateTests` methods for bounded child runs, sysroot pin
    hardening, and the Tier B gate."""

    def test_run_bounded_caps_child_output_and_kills_process_group(self):
        cap = 4096
        for stream_name in ("stdout", "stderr"):
            with self.subTest(stream=stream_name):
                code = (
                    f"import sys; w = sys.{stream_name}.buffer.write\n"
                    "chunk = b'X' * 16384\n"
                    "while True:\n"
                    "    w(chunk)\n"
                )
                rc, out, err, elapsed = oracle.run_bounded(
                    [sys.executable, "-c", code],
                    env=oracle.sanitized_child_env(),
                    timeout_secs=10,
                    max_memory_mb=oracle.DEFAULT_MAX_MEMORY_MB,
                    max_output_bytes=cap,
                )
                self.assertEqual(rc, "output_limit")
                self.assertLessEqual(len(out.encode("utf-8")), cap)
                self.assertLessEqual(len(err.encode("utf-8")), cap)
                self.assertLess(elapsed, 5.0)
                bucket, sub_bucket, _ = oracle.classify_eval_result(
                    rc, out, err, expect_valid=False
                )
                self.assertEqual((bucket, sub_bucket), ("tool_error", "output_limit"))

    def test_run_bounded_kills_before_reap_and_pin_sysroot_hardening(self):
        from unittest import mock

        # Every _kill_process_group call must precede proc.wait() reaping the
        # PID (pinned via waitid WNOWAIT), preventing PID-recycling kill races.
        events: list[str] = []
        orig_kill = oracle._kill_process_group
        orig_popen = oracle.subprocess.Popen

        def tracked_kill(proc):
            events.append("killpg")
            return orig_kill(proc)

        class TrackedPopen(orig_popen):
            def wait(self, *args, **kwargs):
                events.append("wait")
                return super().wait(*args, **kwargs)

        with (
            mock.patch.object(oracle_bounded, "_kill_process_group", side_effect=tracked_kill),
            mock.patch.object(oracle.subprocess, "Popen", TrackedPopen),
        ):
            rc, _, _, _ = oracle.run_bounded(
                [sys.executable, "-I", "-B", "-c", "print('ok')"],
                env=oracle.sanitized_child_env(),
                timeout_secs=10,
                max_memory_mb=256,
            )
        self.assertEqual(rc, 0)
        self.assertIn("killpg", events)
        self.assertIn("wait", events)
        last_kill = max(i for i, ev in enumerate(events) if ev == "killpg")
        first_wait = min(i for i, ev in enumerate(events) if ev == "wait")
        self.assertLess(last_kill, first_wait, events)

        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            real_pin = json.loads(oracle.DEFAULT_PIN_PATH.read_text(encoding="utf-8"))
            pin_file = td_path / "pin.json"
            pin_file.write_text(json.dumps(real_pin), encoding="utf-8")

            # Symlinked, FIFO, and oversized --pin files must fail closed
            # atomically without blocking or unbounded reads.
            sym_pin = td_path / "pin_link.json"
            sym_pin.symlink_to(pin_file)
            with self.assertRaisesRegex(oracle.OracleError, "non-symlink"):
                oracle.load_pin(sym_pin)

            fifo_pin = td_path / "pin_fifo.json"
            os.mkfifo(fifo_pin)
            with self.assertRaisesRegex(oracle.OracleError, "regular file"):
                oracle.load_pin(fifo_pin)

            with mock.patch.object(oracle_pins, "MAX_PIN_BYTES", 64):
                with self.assertRaisesRegex(oracle.OracleError, "max size"):
                    oracle.load_pin(pin_file)

            # Streaming tar extraction must stop at MAX_TAR_MEMBERS without
            # materializing the full archive via getmembers().
            many_tar = td_path / "many.tar.gz"
            with tarfile.open(many_tar, "w:gz") as tf:
                for i in range(10):
                    data = b"fn main() {}\n"
                    ti = tarfile.TarInfo(f"miri-test/tests/fail/f{i}.rs")
                    ti.size = len(data)
                    tf.addfile(ti, io.BytesIO(data))
            with (
                mock.patch.object(oracle_archive, "MAX_TAR_MEMBERS", 3),
                mock.patch.object(
                    tarfile.TarFile,
                    "getmembers",
                    side_effect=AssertionError("must stream with next()"),
                ),
            ):
                with self.assertRaisesRegex(oracle.OracleError, "exceeds 3 members"):
                    oracle.safe_extract_miri_corpus(
                        many_tar,
                        td_path / "many_out",
                        expected_top_dir="miri-test",
                        extract_subdirs=["tests/fail"],
                    )

            # Invalid upstream_repo and overlapping extract_subdirs fail closed.
            bad_repo = dict(real_pin, upstream_repo="evil/miri")
            bad_repo_path = td_path / "bad_repo.json"
            bad_repo_path.write_text(json.dumps(bad_repo), encoding="utf-8")
            with self.assertRaisesRegex(oracle.OracleError, "upstream_repo"):
                oracle.load_pin(bad_repo_path)

            overlap = dict(real_pin, extract_subdirs=["tests/fail", "tests/fail/sub"])
            overlap_path = td_path / "overlap.json"
            overlap_path.write_text(json.dumps(overlap), encoding="utf-8")
            with self.assertRaisesRegex(oracle.OracleError, "overlapping"):
                oracle.load_pin(overlap_path)

            # Missing ANNEAL_TEST_INSTALL_ROOT/rust must fail closed, not fall
            # through to rustup; and rustup fallback strips CI credentials.
            missing_root = td_path / "no_rust_here"
            missing_root.mkdir()
            with mock.patch.dict(
                os.environ,
                {"ANNEAL_TEST_INSTALL_ROOT": str(missing_root)},
                clear=False,
            ):
                os.environ.pop("ANNEAL_SYSROOT", None)
                with self.assertRaisesRegex(
                    oracle.OracleError, "ANNEAL_TEST_INSTALL_ROOT"
                ):
                    oracle.resolve_sysroot(None, "nightly-2026-05-31")

            fake_sysroot = td_path / "fake_sysroot"
            fake_sysroot.mkdir()
            captured_env: dict[str, str] = {}

            def fake_check_output(cmd, **kwargs):
                captured_env.update(kwargs.get("env") or {})
                return str(fake_sysroot) + "\n"

            env_override = {
                "GITHUB_TOKEN": "secret-tok",
                "ACTIONS_RUNTIME_TOKEN": "secret-rt",
            }
            with (
                mock.patch.dict(os.environ, env_override, clear=False),
                mock.patch.object(
                    oracle.subprocess, "check_output", side_effect=fake_check_output
                ),
            ):
                os.environ.pop("ANNEAL_SYSROOT", None)
                os.environ.pop("ANNEAL_TEST_INSTALL_ROOT", None)
                resolved = oracle.resolve_sysroot(None, "nightly-2026-05-31")
            self.assertEqual(resolved, fake_sysroot.resolve())
            self.assertNotIn("GITHUB_TOKEN", captured_env)
            self.assertNotIn("ACTIONS_RUNTIME_TOKEN", captured_env)

            # Pre-extracted --corpus-dir must reject FIFOs without blocking and
            # enforce per-file and aggregate extracted-byte limits.
            fifo_root = td_path / "fifo_corpus"
            (fifo_root / "fail").mkdir(parents=True)
            os.mkfifo(fifo_root / "fail" / "hang.rs")
            with self.assertRaisesRegex(oracle.OracleError, "non-regular file"):
                oracle.compute_corpus_manifest_sha256(fifo_root, ["tests/fail"])

            big_root = td_path / "big_corpus"
            (big_root / "fail").mkdir(parents=True)
            (big_root / "fail" / "a.rs").write_bytes(b"a" * 64)
            (big_root / "fail" / "b.rs").write_bytes(b"b" * 64)
            with mock.patch.object(oracle_corpus, "MAX_SINGLE_FILE_BYTES", 32):
                with self.assertRaisesRegex(
                    oracle.OracleError, "exceeds size limit"
                ):
                    oracle.compute_corpus_manifest_sha256(big_root, ["tests/fail"])
            with (
                mock.patch.object(oracle_corpus, "MAX_SINGLE_FILE_BYTES", 100),
                mock.patch.object(oracle_corpus, "MAX_TOTAL_EXTRACTED_BYTES", 100),
            ):
                with self.assertRaisesRegex(
                    oracle.OracleError, "exceeds total size limit"
                ):
                    oracle.compute_corpus_manifest_sha256(big_root, ["tests/fail"])

            # Streaming directory traversal must bound total entries (even empty
            # non-.rs files) and excess .rs files fail-closed while walking.
            many_root = td_path / "many_corpus"
            (many_root / "fail").mkdir(parents=True)
            for idx in range(12):
                (many_root / "fail" / f"empty_{idx}.txt").write_bytes(b"")
            with self.assertRaisesRegex(oracle.OracleError, "max entry limit"):
                oracle.compute_corpus_manifest_sha256(
                    many_root, ["tests/fail"], max_entries=10
                )
            with self.assertRaisesRegex(oracle.OracleError, "file count mismatch"):
                oracle.compute_corpus_manifest_sha256(
                    big_root, ["tests/fail"], max_rs_files=1
                )

            # Snapshotting during verification captures verified bytes once so
            # mutating `--corpus-dir` afterward cannot alter the snapshot.
            snap_dir = td_path / "corpus_snapshot"
            snap_sha, snap_files = oracle.compute_corpus_manifest_sha256(
                big_root, ["tests/fail"], snapshot_dir=snap_dir
            )
            self.assertEqual(snap_files, ["fail/a.rs", "fail/b.rs"])
            (big_root / "fail" / "a.rs").write_bytes(b"TAMPERED" * 100)
            self.assertEqual((snap_dir / "fail" / "a.rs").read_bytes(), b"a" * 64)
            snap_sha_recheck, _ = oracle.compute_corpus_manifest_sha256(
                snap_dir, ["tests/fail"]
            )
            self.assertEqual(snap_sha_recheck, snap_sha)

    def test_tier_b_gate_enforces_ub_detection_and_valid_controls(self):
        passing = [
            {
                "id": "ub1",
                "kind": "rust_ub_caught",
                "bucket": "caught_ub",
                "detail": "signed integer division or remainder by zero",
                "expected_fault_substring": "division or remainder by zero",
            },
            {
                "id": "fc1",
                "kind": "rust_ub_fail_closed",
                "bucket": "capture_refused",
                "detail": "unsupported type",
            },
            {
                "id": "ok1",
                "kind": "rust_valid_control",
                "bucket": "accepted_valid",
            },
        ]
        passed, failures, _ = oracle.evaluate_tier_b_gate(passing)
        self.assertTrue(passed, failures)

        # Rejecting a valid control MUST fail (prevents trivially-reject-all).
        bad_control = [
            passing[0],
            {"id": "ok1", "kind": "rust_valid_control", "bucket": "capture_refused", "detail": "nope"},
        ]
        passed, failures, _ = oracle.evaluate_tier_b_gate(bad_control)
        self.assertFalse(passed)
        self.assertTrue(any("valid control MUST be accepted_valid" in f for f in failures))

        # Fail-closed UB fixture accepted unsoundly MUST fail.
        bad_fc = [
            passing[0],
            {"id": "fc1", "kind": "rust_ub_fail_closed", "bucket": "unsound_accept", "detail": ""},
            passing[2],
        ]
        passed, failures, _ = oracle.evaluate_tier_b_gate(bad_fc)
        self.assertFalse(passed)
        self.assertTrue(any("fc1" in f for f in failures))

        # Fail-closed UB fixture hitting compiler_failed MUST fail.
        bad_fc_compile = [
            passing[0],
            {"id": "fc1", "kind": "rust_ub_fail_closed", "bucket": "rustc_or_harness_rejected", "detail": "err"},
            passing[2],
        ]
        passed, failures, _ = oracle.evaluate_tier_b_gate(bad_fc_compile)
        self.assertFalse(passed)

        # Missing expected fault substring MUST fail.
        bad_sub = [
            {
                "id": "ub1",
                "kind": "rust_ub_caught",
                "bucket": "caught_ub",
                "detail": "wrong fault reason",
                "expected_fault_substring": "MIN / -1",
            },
            passing[2],
        ]
        passed, failures, _ = oracle.evaluate_tier_b_gate(bad_sub)
        self.assertFalse(passed)
        self.assertTrue(any("missing expected substring" in f for f in failures))
