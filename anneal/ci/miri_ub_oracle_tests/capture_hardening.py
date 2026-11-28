# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Miri UB oracle tests for corpus walking, capture confinement, and compiler
pinning."""

from __future__ import annotations

from .support import (
    hashlib,
    json,
    oracle,
    oracle_corpus,
    oracle_tiers,
    os,
    Path,
    _sample_pin,
    sys,
    tempfile,
    unittest,
    _write_executable,
)


class CaptureHardeningCases:
    """`RealTierBCorpusHygieneTests` methods for corpus walking, capture
    confinement, and compiler pinning."""

    def test_walk_corpus_tree_anchors_file_opens_to_dir_fd(self):
        with tempfile.TemporaryDirectory(prefix="miri-dirfd-") as tmp:
            tmp_path = Path(tmp)
            corpus = tmp_path / "corpus"
            sub = corpus / "fail" / "nested"
            sub.mkdir(parents=True)
            orig_bytes = b"fn main() { /* original */ }\n"
            (sub / "case.rs").write_bytes(orig_bytes)

            # Verify `_walk_corpus_tree` opens every matched file relative to
            # an open directory descriptor (`dir_fd`) using only the entry's
            # basename (never a multi-component pathname reopen).
            observed_calls: list[tuple[str | Path, int | None]] = []
            orig_stream = oracle._stream_regular_file_sha256

            def _spy_stream(path, **kwargs):
                observed_calls.append((path, kwargs.get("dir_fd")))
                return orig_stream(path, **kwargs)

            from unittest import mock

            snap = tmp_path / "snap"
            with mock.patch.object(
                oracle_corpus, "_stream_regular_file_sha256", side_effect=_spy_stream
            ):
                sha, rels = oracle._walk_corpus_tree(
                    corpus,
                    ["tests/fail"],
                    suffixes=(".rs",),
                    snapshot_dir=snap,
                )
            self.assertEqual(rels, ["fail/nested/case.rs"])
            self.assertEqual(len(observed_calls), 1)
            opened_name, opened_dir_fd = observed_calls[0]
            self.assertEqual(opened_name, "case.rs")
            self.assertIsInstance(opened_dir_fd, int)
            self.assertEqual(
                (snap / "fail/nested/case.rs").read_bytes(), orig_bytes
            )

            # Simulate an ancestor rename race after obtaining `dir_fd`:
            # opening relative to `dir_fd` must still read the original inode
            # rather than a swapped decoy directory at the old pathname.
            dfd = os.open(sub, os.O_RDONLY | os.O_DIRECTORY)
            try:
                moved = corpus / "fail" / "moved_nested"
                sub.rename(moved)
                sub.mkdir()
                (sub / "case.rs").write_bytes(b"fn main() { /* decoy */ }\n")
                got_sha, got_size = oracle._stream_regular_file_sha256(
                    "case.rs",
                    max_bytes=1024,
                    dir_fd=dfd,
                    display_path=sub / "case.rs",
                )
            finally:
                os.close(dfd)
            self.assertEqual(got_size, len(orig_bytes))
            self.assertEqual(got_sha, hashlib.sha256(orig_bytes).hexdigest())
            self.assertTrue(sha)

    def test_tier_a_rejects_mismatched_capture_compiler_commit(self):
        with tempfile.TemporaryDirectory(prefix="miri-commit-mismatch-") as tmp:
            tmp_path = Path(tmp)
            corpus = tmp_path / "corpus"
            (corpus / "fail").mkdir(parents=True)
            (corpus / "fail" / "ub1.rs").write_text(
                "fn main() { /* TRIGGER_UB */ }\n", encoding="utf-8"
            )
            manifest_sha, _ = oracle.compute_corpus_manifest_sha256(
                corpus, ["tests/fail"]
            )
            pin = _sample_pin(
                manifest_sha=manifest_sha,
                expected_file_count=1,
                min_caught_ub=1,
            )
            pin["extract_subdirs"] = ["tests/fail"]
            pin["expected_caught_ub_units"] = ["fail/ub1.rs"]
            pin_path = tmp_path / "pin.json"
            pin_path.write_text(json.dumps(pin), encoding="utf-8")

            sysroot = tmp_path / "sysroot"
            (sysroot / "lib").mkdir(parents=True)
            stale_cap = tmp_path / "stale-capture"
            eval_bin = tmp_path / "fake-eval"
            _write_executable(
                stale_cap,
                f"#!{sys.executable}\n"
                "import json, pathlib, sys\n"
                "args = sys.argv[1:]\n"
                "out = pathlib.Path(args[args.index('--out-dir') + 1])\n"
                "out.mkdir(parents=True, exist_ok=True)\n"
                "(out / 'capture.json').write_text(\n"
                "    json.dumps({'compiler': {'commit': '0' * 40}})\n"
                ")\n"
                "print(json.dumps({'status': 'captured'}))\n",
            )
            _write_executable(
                eval_bin,
                f"#!{sys.executable}\n"
                "import json, sys\n"
                "print(json.dumps({'outcome': {'kind': 'fault', "
                "'value': {'kind': 'undefined', 'reason': 'stub ub'}}}))\n"
                "sys.exit(2)\n",
            )
            report_path = tmp_path / "report.json"
            rc = oracle.main([
                "--tier-a",
                "--pin", str(pin_path),
                "--corpus-dir", str(corpus),
                "--no-network",
                "--capture-bin", str(stale_cap),
                "--eval-bin", str(eval_bin),
                "--sysroot", str(sysroot),
                "--output", str(report_path),
            ])
            self.assertEqual(rc, 1)
            report = json.loads(report_path.read_text(encoding="utf-8"))
            self.assertFalse(report["passed"])
            self.assertEqual(report["counts"]["tool_error"], 1)
            self.assertEqual(report["counts"]["caught_ub"], 0)
            self.assertEqual(
                report["units"][0]["sub_bucket"], "compiler_commit_mismatch"
            )

    def test_capture_confinement_refuses_root_uid(self):
        from unittest import mock

        with mock.patch.object(oracle.os, "getuid", return_value=0):
            with self.assertRaisesRegex(oracle.OracleError, "UID 0"):
                oracle._require_confinement_support(256)
            with self.assertRaisesRegex(oracle.OracleError, "UID 0"):
                oracle._enter_capture_namespaces(None)
            # Both run_tier_a and run_tier_b must fail closed at preflight
            # before loading pins, snapshotting corpora, or running fixtures.
            with (
                mock.patch.object(
                    oracle_tiers,
                    "load_pin",
                    side_effect=AssertionError("load_pin called as UID 0"),
                ),
                mock.patch.object(
                    oracle_tiers,
                    "load_tier_b_manifest",
                    side_effect=AssertionError("manifest loaded as UID 0"),
                ),
            ):
                with self.assertRaisesRegex(oracle.OracleError, "UID 0"):
                    oracle.run_tier_a(
                        pin_path=Path("/nonexistent/pin.json"),
                        capture_bin=Path("/nonexistent/cap"),
                        eval_bin=Path("/nonexistent/eval"),
                        sysroot=Path("/nonexistent/sysroot"),
                        archive_path=None,
                        corpus_dir=None,
                        no_network=True,
                        profile_override=None,
                        workers=1,
                        timeout_secs=10,
                        max_memory_mb=256,
                        fuel_override=None,
                    )
                with self.assertRaisesRegex(oracle.OracleError, "UID 0"):
                    oracle.run_tier_b(
                        tier_b_dir=Path("/nonexistent/tier_b"),
                        capture_bin=Path("/nonexistent/cap"),
                        eval_bin=Path("/nonexistent/eval"),
                        sysroot=Path("/nonexistent/sysroot"),
                        target="x86_64-unknown-linux-gnu",
                        fuel=1000,
                        profile="auto",
                        workers=1,
                        timeout_secs=10,
                        max_memory_mb=256,
                    )
        with mock.patch.object(oracle.os, "geteuid", return_value=0):
            with self.assertRaisesRegex(oracle.OracleError, "RLIMIT_NPROC"):
                oracle._assert_capture_non_root_uid()

    def test_drop_all_capabilities_verifies_bounding_set_on_eperm(self):
        import ctypes
        import errno
        from unittest import mock

        class _FakeLibc:
            def __init__(self, read_result: int):
                self._read_result = read_result
                self.capset_calls = 0

            def prctl(self, option, arg2, _arg3, _arg4, _arg5):
                if option == 24:  # PR_CAPBSET_DROP
                    ctypes.set_errno(errno.EPERM)
                    return -1
                if option == 23:  # PR_CAPBSET_READ
                    if arg2 > 2:
                        ctypes.set_errno(errno.EINVAL)
                        return -1
                    return self._read_result
                if option == 47:  # PR_CAP_AMBIENT
                    return 0
                return 0

            def syscall(self, _nr, _hdr, _data):
                self.capset_calls += 1
                return 0

        # Non-empty bounding set with EPERM on PR_CAPBSET_DROP must fail closed.
        with mock.patch.object(oracle.ctypes, "get_errno", return_value=errno.EPERM):
            with self.assertRaisesRegex(oracle.OracleError, "bounding set"):
                oracle._drop_all_capabilities(_FakeLibc(read_result=1), drop_bounding=True)

        # Already-empty bounding set (PR_CAPBSET_READ == 0) is accepted.
        def _fake_get_errno_seq():
            return ctypes.get_errno()

        fake_empty = _FakeLibc(read_result=0)
        oracle._drop_all_capabilities(fake_empty, drop_bounding=True)
        self.assertEqual(fake_empty.capset_calls, 1)

        # eval mode (`drop_bounding=False`) skips PR_CAPBSET_DROP and still
        # invokes capset to clear active capability sets.
        fake_eval = _FakeLibc(read_result=1)
        oracle._drop_all_capabilities(fake_eval, drop_bounding=False)
        self.assertEqual(fake_eval.capset_calls, 1)

    def test_compile_flags_accept_capture_fixed_and_reject_unforwarded(self):
        # Flags unconditionally enforced by `anneal-rustc-capture` are accepted
        # without being reported as unforwarded.
        ed, pan, unfwd = oracle.parse_compile_flags([
            "--edition=2024",
            "-C",
            "debug-assertions=no",
            "-Copt-level=0",
            "-Coverflow-checks=no",
            "-Z",
            "mir-opt-level=0",
            "-Zmiri-strict-provenance",
            "-Cpanic=abort",
        ])
        self.assertEqual(ed, "2024")
        self.assertEqual(pan, "abort")
        self.assertEqual(unfwd, [])

        # Non-default build-affecting flags are flagged as unforwarded and
        # rejected fail-closed BEFORE spawning capture_bin.
        _, _, unfwd2 = oracle.parse_compile_flags([
            "-Ctarget-feature=-sse4.1",
            "-Z",
            "mir-opt-level=3",
        ])
        self.assertEqual(
            unfwd2, ["-Ctarget-feature=-sse4.1", "-Zmir-opt-level=3"]
        )
        with tempfile.TemporaryDirectory(prefix="miri-unfwd-") as tmp:
            tmp_path = Path(tmp)
            src = tmp_path / "u.rs"
            src.write_text("fn main() {}\n", encoding="utf-8")
            rec = oracle.evaluate_rust_unit(
                src,
                "fail/u.rs",
                revision=None,
                flags=["-Ctarget-feature=-sse4.1"],
                capture_bin=tmp_path / "missing-capture",
                eval_bin=tmp_path / "missing-eval",
                sysroot=tmp_path / "missing-sysroot",
                target="x86_64-unknown-linux-gnu",
                fuel=1000,
                profile="auto",
                timeout_secs=10,
                max_memory_mb=256,
                expect_valid=False,
            )
            self.assertEqual(rec["bucket"], "rustc_or_harness_rejected")
            self.assertEqual(rec["sub_bucket"], "harness_unforwarded_flags")
            self.assertEqual(
                rec["unforwarded_rustc_flags"], ["-Ctarget-feature=-sse4.1"]
            )
            self.assertIsNone(rec["capture_rc"])
        # Gate counts `harness_unforwarded_flags` against `max_harness_skips`.
        pin = _sample_pin(expected_file_count=1, min_caught_ub=0)
        pin["expected_unit_count"] = 1
        pin["max_harness_skips"] = 0
        passed, failures, _ = oracle.evaluate_tier_a_gate(
            [rec], total_files=1, pin=pin
        )
        self.assertFalse(passed)
        self.assertTrue(any("max_harness_skips" in f for f in failures))

    def test_tier_b_repo_corpus_forwards_pinned_rustc_commit(self) -> None:
        """Repository Tier B runs must bind captures to the pinned rustc_commit."""
        real_pin = oracle.load_pin(oracle.DEFAULT_PIN_PATH)
        seen_commits: list[str | None] = []

        def fake_eval_rust(*_args: object, **kwargs: object) -> dict[str, object]:
            seen_commits.append(kwargs.get("expected_rustc_commit"))  # type: ignore[arg-type]
            return {
                "file": "stub.rs",
                "revision": None,
                "profile": "auto",
                "bucket": "tool_error",
                "sub_bucket": "compiler_commit_mismatch",
                "detail": "stale capture compiler commit",
            }

        def fake_eval_mir(*_args: object, **_kwargs: object) -> dict[str, object]:
            return {
                "file": "stub.json",
                "revision": None,
                "profile": "auto",
                "bucket": "caught_ub",
                "sub_bucket": "undefined",
                "detail": "stub ub",
            }

        with (
            unittest.mock.patch.object(oracle_tiers, "_require_confinement_support"),
            unittest.mock.patch.object(
                oracle_tiers, "evaluate_rust_unit", side_effect=fake_eval_rust
            ),
            unittest.mock.patch.object(
                oracle_tiers, "evaluate_mir_json_unit", side_effect=fake_eval_mir
            ),
        ):
            report = oracle.run_tier_b(
                tier_b_dir=oracle.DEFAULT_TIER_B_DIR,
                capture_bin=Path("/bin/true"),
                eval_bin=Path("/bin/true"),
                sysroot=Path("/tmp"),
                target="x86_64-unknown-linux-gnu",
                fuel=2_000_000,
                profile="auto",
                workers=1,
                timeout_secs=10,
                max_memory_mb=256,
                pin=real_pin,
            )
        self.assertFalse(report["passed"])
        self.assertGreater(len(seen_commits), 0)
        self.assertEqual(set(seen_commits), {str(real_pin["rustc_commit"])})
        # Verify Landlock UAPI bit positions match <linux/landlock.h>.
        self.assertEqual(oracle._LANDLOCK_ACCESS_FS_MAKE_DIR, 1 << 7)
        self.assertEqual(oracle._LANDLOCK_ACCESS_FS_MAKE_REG, 1 << 8)
