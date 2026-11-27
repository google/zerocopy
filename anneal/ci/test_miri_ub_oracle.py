# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for the 2-tier Miri UB oracle harness."""

from __future__ import annotations

import hashlib
import io
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import tarfile
import tempfile
import unittest

import run_miri_ub_oracle as oracle


CI_DIR = Path(__file__).resolve().parent
ANNEAL_DIR = CI_DIR.parent


def _make_tar_gz(dest: Path, entries: list[tuple[str, bytes | str, bytes]]) -> str:
    """Build a .tar.gz with explicit TarInfo types; return its SHA-256."""
    with tarfile.open(dest, "w:gz") as tf:
        for name, payload, mtype in entries:
            info = tarfile.TarInfo(name=name)
            info.type = mtype
            if mtype == tarfile.REGTYPE:
                raw = payload.encode("utf-8") if isinstance(payload, str) else payload
                info.size = len(raw)
                tf.addfile(info, io.BytesIO(raw))
            elif mtype in (tarfile.SYMTYPE, tarfile.LNKTYPE):
                info.linkname = payload if isinstance(payload, str) else payload.decode("utf-8")
                tf.addfile(info)
            else:
                tf.addfile(info)
    return hashlib.sha256(dest.read_bytes()).hexdigest()


def _write_executable(path: Path, content: str) -> None:
    path.write_text(content, encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IXUSR)


def _sample_pin(
    *,
    miri_commit: str = "a" * 40,
    archive_sha: str = "b" * 64,
    manifest_sha: str = "c" * 64,
    expected_file_count: int = 2,
    min_caught_ub: int = 1,
) -> dict[str, object]:
    return {
        "schema_version": 1,
        "upstream_repo": "rust-lang/miri",
        "miri_commit": miri_commit,
        "rustc_toolchain_channel": "nightly-2026-05-31",
        "rustc_commit": "f" * 40,
        "miri_tree_sha": "3" * 40,
        "fail_tree_sha": "1" * 40,
        "fail_dep_tree_sha": "2" * 40,
        "archive_url": f"https://github.com/rust-lang/miri/archive/{miri_commit}.tar.gz",
        "archive_sha256": archive_sha,
        "expected_top_dir": f"miri-{miri_commit}",
        "extract_subdirs": ["tests/fail", "tests/fail-dep"],
        "expected_file_count": expected_file_count,
        "corpus_manifest_sha256": manifest_sha,
        "target": "x86_64-unknown-linux-gnu",
        "capture_scope": "crate",
        "fuel": 2000000,
        "profile": "auto",
        "max_unsound_accepts": 0,
        "max_tool_errors": 0,
        "min_caught_ub": min_caught_ub,
    }


class PinAndSupplyChainTests(unittest.TestCase):
    def test_real_pin_manifest_is_valid_and_matches_repo_toolchain(self):
        pin = oracle.load_pin(oracle.DEFAULT_PIN_PATH)
        self.assertEqual(pin["max_unsound_accepts"], 0)
        self.assertEqual(pin["max_tool_errors"], 0)
        self.assertEqual(pin["capture_scope"], "crate")
        self.assertGreaterEqual(pin["min_caught_ub"], 1)
        self.assertEqual(pin["extract_subdirs"], ["tests/fail"])
        self.assertEqual(pin["expected_file_count"], 512)
        self.assertEqual(pin["expected_unit_count"], 571)
        self.assertEqual(pin["max_harness_skips"], 5)
        self.assertEqual(pin["max_rustc_or_harness_rejected"], 14)
        self.assertEqual(
            len(pin["expected_caught_ub_units"]), pin["min_caught_ub"]
        )

        flake_text = (ANNEAL_DIR / "flake.nix").read_text(encoding="utf-8")
        date_match = re.search(r'rustDate\s*=\s*"([0-9-]+)"', flake_text)
        self.assertIsNotNone(date_match, "rustDate missing in anneal/flake.nix")
        self.assertEqual(
            pin["rustc_toolchain_channel"],
            f"nightly-{date_match.group(1)}",
        )

        ir_text = (
            ANNEAL_DIR / "trusted" / "rustc-capture" / "src" / "ir.rs"
        ).read_text(encoding="utf-8")
        commit_match = re.search(
            r'pub const COMPILER_COMMIT:\s*&str\s*=\s*"([0-9a-f]{40})"',
            ir_text,
        )
        self.assertIsNotNone(commit_match, "COMPILER_COMMIT missing in ir.rs")
        self.assertEqual(pin["rustc_commit"], commit_match.group(1))
        self.assertRegex(str(pin["miri_tree_sha"]), r"^[0-9a-f]{40}$")
        self.assertRegex(str(pin["fail_tree_sha"]), r"^[0-9a-f]{40}$")
        self.assertNotIn("fail_dep_tree_sha", pin)
        self.assertRegex(str(pin["tier_b_corpus_sha256"]), r"^[0-9a-f]{64}$")

    def test_pin_rejects_weakened_gates_and_bad_urls(self):
        mutations = [
            ("nonzero_unsound", {"max_unsound_accepts": 1}),
            ("nonzero_tool_err", {"max_tool_errors": 1}),
            ("select_scope", {"capture_scope": "select"}),
            ("zero_ratchet", {"min_caught_ub": 0}),
            ("bad_url", {"archive_url": "http://example.com/miri.tar.gz"}),
            ("bad_top_dir", {"expected_top_dir": "miri-other"}),
            ("bad_sha", {"archive_sha256": "not-hex"}),
            ("bad_schema", {"schema_version": 99}),
            ("subdir_dotdot", {"extract_subdirs": ["tests/../.."]}),
            ("subdir_dup", {"extract_subdirs": ["tests/fail", "tests/fail"]}),
            ("subdir_outside", {"extract_subdirs": ["src/fail"]}),
            ("too_many_expected_units", {"expected_caught_ub_units": ["a", "b"], "min_caught_ub": 1}),
            ("neg_max_rejected", {"max_rustc_or_harness_rejected": -1}),
            ("bool_max_rejected", {"max_rustc_or_harness_rejected": True}),
        ]
        with tempfile.TemporaryDirectory(prefix="miri-pin-test-") as tmp:
            for label, patch in mutations:
                with self.subTest(case=label):
                    pin = _sample_pin()
                    pin.update(patch)
                    p = Path(tmp) / f"{label}.json"
                    p.write_text(json.dumps(pin), encoding="utf-8")
                    with self.assertRaises(oracle.OracleError):
                        oracle.load_pin(p)

    def test_sha256_mismatch_fails_closed(self):
        with tempfile.TemporaryDirectory(prefix="miri-sha-test-") as tmp:
            archive = Path(tmp) / "archive.tar.gz"
            real_sha = _make_tar_gz(
                archive,
                [("miri-" + "a" * 40 + "/tests/fail/a.rs", "fn main() {}\n", tarfile.REGTYPE)],
            )
            bad_sha = ("0" if real_sha[0] != "0" else "1") + real_sha[1:]

            # TOCTOU-free copy-and-verify succeeds on match and deletes temp
            # output on mismatch, symlink, or size overflow.
            copy_ok = Path(tmp) / "copy_ok.tar.gz"
            self.assertEqual(
                oracle.copy_and_verify_archive_sha256(archive, copy_ok, real_sha),
                real_sha,
            )
            self.assertTrue(copy_ok.is_file())

            copy_bad = Path(tmp) / "copy_bad.tar.gz"
            with self.assertRaisesRegex(oracle.OracleError, "SHA-256 mismatch"):
                oracle.copy_and_verify_archive_sha256(archive, copy_bad, bad_sha)
            self.assertFalse(copy_bad.exists())

            link = Path(tmp) / "link.tar.gz"
            link.symlink_to(archive)
            copy_link = Path(tmp) / "copy_link.tar.gz"
            with self.assertRaisesRegex(oracle.OracleError, "non-symlink"):
                oracle.copy_and_verify_archive_sha256(link, copy_link, real_sha)
            self.assertFalse(copy_link.exists())

            copy_big = Path(tmp) / "copy_big.tar.gz"
            with self.assertRaisesRegex(oracle.OracleError, "exceeds max"):
                oracle.copy_and_verify_archive_sha256(
                    archive, copy_big, real_sha, max_bytes=8
                )
            self.assertFalse(copy_big.exists())

            fifo = Path(tmp) / "hang.tar.gz"
            os.mkfifo(fifo)
            copy_fifo = Path(tmp) / "copy_fifo.tar.gz"
            with self.assertRaisesRegex(oracle.OracleError, "non-symlink"):
                oracle.copy_and_verify_archive_sha256(fifo, copy_fifo, real_sha)
            self.assertFalse(copy_fifo.exists())
            self.assertFalse(copy_bad.exists())

    def test_https_host_validation_rejects_non_github(self):
        oracle._validate_https_host("https://github.com/rust-lang/miri/archive/x.tar.gz")
        oracle._validate_https_host("https://codeload.github.com/rust-lang/miri/tar.gz/x")
        for bad in (
            "http://github.com/rust-lang/miri/archive/x.tar.gz",
            "file:///etc/passwd",
            "https://evil.example.com/archive.tar.gz",
        ):
            with self.subTest(url=bad):
                with self.assertRaises(oracle.OracleError):
                    oracle._validate_https_host(bad)


class SafeTarExtractionTests(unittest.TestCase):
    def test_safe_extract_accepts_clean_archive_and_skips_non_rs(self):
        top = "miri-" + "a" * 40
        with tempfile.TemporaryDirectory(prefix="miri-tar-ok-") as tmp:
            tmp_path = Path(tmp)
            archive = tmp_path / "clean.tar.gz"
            _make_tar_gz(
                archive,
                [
                    (f"{top}/", b"", tarfile.DIRTYPE),
                    (f"{top}/README.md", "ignored\n", tarfile.REGTYPE),
                    (f"{top}/tests/fail/a.rs", "fn main() {}\n", tarfile.REGTYPE),
                    (f"{top}/tests/fail/a.stderr", "ignored\n", tarfile.REGTYPE),
                    (f"{top}/tests/fail-dep/b.rs", "fn main() {}\n", tarfile.REGTYPE),
                ],
            )
            dest = tmp_path / "out"
            extracted = oracle.safe_extract_miri_corpus(
                archive,
                dest,
                expected_top_dir=top,
                extract_subdirs=["tests/fail", "tests/fail-dep"],
            )
            self.assertEqual(extracted, ["fail-dep/b.rs", "fail/a.rs"])
            self.assertFalse((dest / "fail" / "a.stderr").exists())
            sha, files = oracle.compute_corpus_manifest_sha256(
                dest, ["tests/fail", "tests/fail-dep"]
            )
            self.assertEqual(files, ["fail-dep/b.rs", "fail/a.rs"])
            self.assertRegex(sha, r"^[0-9a-f]{64}$")

            # Oversized compressed PAX extended header must fail closed via
            # `_BoundedReadStream` inside `tf.next()` before materialization.
            from unittest import mock

            pax_bomb = tmp_path / "pax_bomb.tar.gz"
            with tarfile.open(pax_bomb, mode="w:gz", format=tarfile.PAX_FORMAT) as tf:
                ti = tarfile.TarInfo(f"{top}/tests/fail/a.rs")
                ti.pax_headers = {"comment": "A" * 65536}
                body = b"fn main() {}\n"
                ti.size = len(body)
                tf.addfile(ti, io.BytesIO(body))
            with mock.patch.object(oracle, "MAX_DECOMPRESSED_TAR_BYTES", 8192):
                with self.assertRaisesRegex(
                    oracle.OracleError, "decompressed tar stream exceeds"
                ):
                    oracle.safe_extract_miri_corpus(
                        pax_bomb,
                        tmp_path / "pax_out",
                        expected_top_dir=top,
                        extract_subdirs=["tests/fail"],
                    )

    def test_safe_extract_rejects_traversal_symlinks_hardlinks_and_specials(self):
        top = "miri-" + "a" * 40
        malicious_cases = [
            ("dotdot", [(f"{top}/tests/fail/../../evil.rs", "x", tarfile.REGTYPE)]),
            ("abs_path", [("/etc/passwd", "x", tarfile.REGTYPE)]),
            ("wrong_root", [("other/tests/fail/a.rs", "x", tarfile.REGTYPE)]),
            ("backslash", [(f"{top}/tests\\fail\\a.rs", "x", tarfile.REGTYPE)]),
            ("symlink", [(f"{top}/tests/fail/s.rs", "/etc/passwd", tarfile.SYMTYPE)]),
            ("hardlink", [(f"{top}/tests/fail/h.rs", f"{top}/tests/fail/a.rs", tarfile.LNKTYPE)]),
            ("fifo", [(f"{top}/tests/fail/pipe", b"", tarfile.FIFOTYPE)]),
            (
                "duplicate",
                [
                    (f"{top}/tests/fail/a.rs", "fn main() {}\n", tarfile.REGTYPE),
                    (f"{top}/tests/fail/a.rs", "fn main() {}\n", tarfile.REGTYPE),
                ],
            ),
        ]
        with tempfile.TemporaryDirectory(prefix="miri-tar-bad-") as tmp:
            for label, entries in malicious_cases:
                with self.subTest(case=label):
                    archive = Path(tmp) / f"{label}.tar.gz"
                    _make_tar_gz(archive, entries)
                    dest = Path(tmp) / f"dest-{label}"
                    with self.assertRaises(oracle.OracleError):
                        oracle.safe_extract_miri_corpus(
                            archive,
                            dest,
                            expected_top_dir=top,
                            extract_subdirs=["tests/fail", "tests/fail-dep"],
                        )


class ClassificationAndGateTests(unittest.TestCase):
    def test_classify_eval_result_cross_checks_rc_and_json(self):
        returned_json = json.dumps({"outcome": {"kind": "returned", "value": {"kind": "returned"}}})
        unwound_json = json.dumps({"outcome": {"kind": "returned", "value": {"kind": "unwound"}}})
        ub_json = json.dumps({
            "outcome": {"kind": "fault", "value": {"kind": "undefined", "reason": "div zero"}}
        })
        unsup_json = json.dumps({
            "outcome": {"kind": "fault", "value": {"kind": "unsupported", "reason": "op"}}
        })
        oof_json = json.dumps({"outcome": {"kind": "out_of_fuel"}})
        abort_json = json.dumps({"outcome": {"kind": "aborted", "value": {}}})

        self.assertEqual(
            oracle.classify_eval_result(0, returned_json, "", expect_valid=False)[0],
            "unsound_accept",
        )
        self.assertEqual(
            oracle.classify_eval_result(0, returned_json, "", expect_valid=True)[0],
            "accepted_valid",
        )
        self.assertEqual(
            oracle.classify_eval_result(0, unwound_json, "", expect_valid=False)[0],
            "unsound_accept",
        )
        self.assertEqual(
            oracle.classify_eval_result(0, unwound_json, "", expect_valid=True)[0],
            "eval_fail_closed",
        )
        self.assertEqual(
            oracle.classify_eval_result(2, ub_json, "", expect_valid=False),
            ("caught_ub", None, "div zero"),
        )
        self.assertEqual(
            oracle.classify_eval_result(3, unsup_json, "", expect_valid=False)[0],
            "eval_fail_closed",
        )
        self.assertEqual(
            oracle.classify_eval_result(3, oof_json, "", expect_valid=False)[:2],
            ("eval_fail_closed", "out_of_fuel"),
        )
        self.assertEqual(
            oracle.classify_eval_result(4, abort_json, "", expect_valid=False)[:2],
            ("unsound_accept", "aborted"),
        )
        self.assertEqual(
            oracle.classify_eval_result(4, abort_json, "", expect_valid=True)[:2],
            ("eval_fail_closed", "unexpected_abort"),
        )
        # Exit code / JSON mismatches must fail closed as tool_error.
        self.assertEqual(
            oracle.classify_eval_result(2, unsup_json, "", expect_valid=False)[0],
            "tool_error",
        )
        self.assertEqual(
            oracle.classify_eval_result(0, ub_json, "", expect_valid=False)[0],
            "tool_error",
        )
        self.assertEqual(
            oracle.classify_eval_result(2, "not-json", "", expect_valid=False)[0],
            "tool_error",
        )
        self.assertEqual(
            oracle.classify_eval_result("timeout", "", "", expect_valid=False)[0],
            "tool_error",
        )
        self.assertEqual(
            oracle.classify_eval_result("output_limit", "", "", expect_valid=False)[:2],
            ("tool_error", "output_limit"),
        )

    def test_classify_eval_result_pre_eval_unsupported_rc3(self):
        reason = (
            "Profile v2 only supports little-endian targets "
            "(Trusted.MirSemantics.profileV2TargetEndian)"
        )
        stderr = f"unsupported program: {reason}\n"
        self.assertEqual(
            oracle.classify_eval_result(3, "", stderr, expect_valid=False),
            ("eval_fail_closed", "pre_eval_unsupported", reason),
        )
        self.assertEqual(
            oracle.classify_eval_result(3, "   \n", stderr, expect_valid=True),
            ("eval_fail_closed", "pre_eval_unsupported", reason),
        )
        # Non-rc3, non-empty stdout, empty reason, extra stderr lines, or
        # unrelated stderr must all remain fail-closed `tool_error`.
        for rc, out, err in (
            (2, "", stderr),
            (1, "", stderr),
            (3, "not-json", stderr),
            (3, "", "unsupported program:   \n"),
            (3, "", f"extra noise\n{stderr}"),
            (3, "", "error: failed to parse MIR\n"),
            (3, "", ""),
        ):
            self.assertEqual(
                oracle.classify_eval_result(rc, out, err, expect_valid=False)[:2],
                ("tool_error", "invalid_eval_json"),
                f"expected tool_error for rc={rc!r}, out={out!r}, err={err!r}",
            )

    def test_tier_a_gate_enforces_unsound_ratchet_and_tool_error(self):
        pin = _sample_pin(expected_file_count=3, min_caught_ub=2)
        ok_units = [
            {"file": "fail/a.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/b.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/c.rs", "revision": None, "bucket": "capture_refused"},
        ]
        passed, failures, counts = oracle.evaluate_tier_a_gate(
            ok_units, total_files=3, pin=pin
        )
        self.assertTrue(passed, failures)
        self.assertEqual(counts["caught_ub"], 2)

        # Unsound accept fails hard.
        bad_unsound = [
            {"file": "fail/a.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/b.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/c.rs", "revision": None, "bucket": "unsound_accept"},
        ]
        passed, failures, _ = oracle.evaluate_tier_a_gate(
            bad_unsound, total_files=3, pin=pin
        )
        self.assertFalse(passed)
        self.assertTrue(any("unsound_accept=1" in f for f in failures))

        # Ratchet drop (caught_ub < min_caught_ub) fails hard.
        bad_ratchet = [
            {"file": "fail/a.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/b.rs", "revision": None, "bucket": "capture_refused"},
            {"file": "fail/c.rs", "revision": None, "bucket": "capture_refused"},
        ]
        passed, failures, _ = oracle.evaluate_tier_a_gate(
            bad_ratchet, total_files=3, pin=pin
        )
        self.assertFalse(passed)
        self.assertTrue(any("regressed below pinned ratchet" in f for f in failures))

        # Tool error fails hard.
        bad_tool = [
            {"file": "fail/a.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/b.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/c.rs", "revision": None, "bucket": "tool_error"},
        ]
        passed, failures, _ = oracle.evaluate_tier_a_gate(
            bad_tool, total_files=3, pin=pin
        )
        self.assertFalse(passed)
        self.assertTrue(any("tool_error=1" in f for f in failures))

        # Set ratchet catches swapping one caught unit for another.
        set_pin = dict(pin)
        set_pin["expected_caught_ub_units"] = ["fail/a.rs", "fail/b.rs"]
        set_pin["expected_unit_count"] = 3
        set_pin["max_harness_skips"] = 0
        swapped = [
            {"file": "fail/a.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/b.rs", "revision": None, "bucket": "capture_refused"},
            {"file": "fail/c.rs", "revision": None, "bucket": "caught_ub"},
        ]
        passed, failures, _ = oracle.evaluate_tier_a_gate(
            swapped, total_files=3, pin=set_pin
        )
        self.assertFalse(passed)
        self.assertTrue(any("pinned caught_ub units regressed: fail/b.rs" in f for f in failures))

        # Exceeding max_harness_skips or changing unit count fails closed.
        skipped = [
            {"file": "fail/a.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/b.rs", "revision": None, "bucket": "caught_ub"},
            {
                "file": "fail/c.rs",
                "revision": None,
                "bucket": "rustc_or_harness_rejected",
                "sub_bucket": "harness_target",
            },
        ]
        passed, failures, _ = oracle.evaluate_tier_a_gate(
            skipped, total_files=3, pin=set_pin
        )
        self.assertFalse(passed)
        self.assertTrue(any("max_harness_skips" in f for f in failures))

        # Exceeding max_rustc_or_harness_rejected fails closed even for
        # non-harness-target rustc rejections.
        rej_pin = dict(set_pin)
        rej_pin["max_harness_skips"] = 1
        rej_pin["max_rustc_or_harness_rejected"] = 0
        rustc_rejected = [
            {"file": "fail/a.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/b.rs", "revision": None, "bucket": "caught_ub"},
            {
                "file": "fail/c.rs",
                "revision": None,
                "bucket": "rustc_or_harness_rejected",
                "sub_bucket": "rustc_error",
            },
        ]
        passed, failures, _ = oracle.evaluate_tier_a_gate(
            rustc_rejected, total_files=3, pin=rej_pin
        )
        self.assertFalse(passed)
        self.assertTrue(
            any("max_rustc_or_harness_rejected" in f for f in failures)
        )

        # File-count and unit-count drift must fail closed explicitly.
        passed, failures, _ = oracle.evaluate_tier_a_gate(
            ok_units, total_files=2, pin=set_pin
        )
        self.assertFalse(passed)
        self.assertTrue(any("file count mismatch" in f for f in failures))

        passed, failures, _ = oracle.evaluate_tier_a_gate(
            ok_units[:2], total_files=3, pin=set_pin
        )
        self.assertFalse(passed)
        self.assertTrue(any("unit count mismatch" in f for f in failures))

    def test_no_preexec_fn_in_threaded_runner_and_confinement_wrapping(self):
        from unittest import mock

        src = (CI_DIR / "run_miri_ub_oracle.py").read_text(encoding="utf-8")
        self.assertNotIn("preexec_fn=", src)
        args = oracle.build_arg_parser().parse_args(
            ["--tier-b", "--capture-bin", "/bin/true", "--eval-bin", "/bin/true"]
        )
        self.assertEqual(args.max_memory_mb, oracle.DEFAULT_MAX_MEMORY_MB)
        self.assertEqual(args.max_total_memory_mb, oracle.DEFAULT_MAX_TOTAL_MEMORY_MB)
        self.assertIsNone(args.workers)
        self.assertGreater(args.max_memory_mb, 0)
        eff_workers, eff_mem = oracle._resolve_worker_memory_budget(
            workers=args.workers,
            max_memory_mb=args.max_memory_mb,
            max_total_memory_mb=args.max_total_memory_mb,
        )
        self.assertGreaterEqual(eff_workers, 1)
        self.assertLessEqual(
            eff_workers * (oracle.CAPTURE_MAX_TASKS * eff_mem + oracle.CAPTURE_MAX_DISK_MB),
            oracle.DEFAULT_MAX_TOTAL_MEMORY_MB,
        )

        # Explicit workers exceeding aggregate capture-task + tmpfs budget fail.
        with self.assertRaises(oracle.OracleError):
            oracle._resolve_worker_memory_budget(
                workers=2, max_memory_mb=1024, max_total_memory_mb=16384
            )
        with self.assertRaises(oracle.OracleError):
            oracle._resolve_worker_memory_budget(
                workers=None, max_memory_mb=2045, max_total_memory_mb=16384
            )
        with self.assertRaises(oracle.OracleError):
            oracle._resolve_worker_memory_budget(
                workers=0, max_memory_mb=1024, max_total_memory_mb=4096
            )
        with self.assertRaises(oracle.OracleError):
            oracle._resolve_worker_memory_budget(
                workers=1, max_memory_mb=1024, max_total_memory_mb=0
            )
        # Capture mode requires Landlock ABI >= 3 for truncate mediation.
        with mock.patch.object(oracle, "_probe_landlock_abi", return_value=2):
            with self.assertRaises(oracle.OracleError):
                oracle._wrap_with_confinement(
                    ["/bin/true"],
                    timeout_secs=10,
                    max_memory_mb=256,
                    confinement="capture",
                )
            with self.assertRaises(oracle.OracleError):
                oracle._install_landlock(
                    Path("/bin/true"), [], require_truncate_mediation=True
                )

        wrapped = oracle._wrap_with_confinement(
            ["/bin/true"], timeout_secs=10, max_memory_mb=256
        )
        self.assertEqual(wrapped[-1], "/bin/true")
        self.assertIn("--", wrapped)
        self.assertIn(oracle._CONFINED_EXEC_FLAG, wrapped)
        self.assertIn(str(256 * 1024 * 1024), wrapped)

        # Non-positive limits and unsupported OS/arch must fail closed.
        for bad in (0, -1):
            with self.assertRaises(oracle.OracleError):
                oracle._wrap_with_confinement(
                    ["/bin/true"], timeout_secs=10, max_memory_mb=bad
                )
        with mock.patch.object(oracle.sys, "platform", "darwin"):
            with self.assertRaises(oracle.OracleError):
                oracle._wrap_with_confinement(
                    ["/bin/true"], timeout_secs=10, max_memory_mb=256
                )
        with mock.patch.object(oracle.platform, "machine", return_value="sparc64"):
            with self.assertRaises(oracle.OracleError):
                oracle._wrap_with_confinement(
                    ["/bin/true"], timeout_secs=10, max_memory_mb=256
                )

        # BPF assembly must succeed on both supported Linux architectures and
        # confinement modes.
        for arch in ("x86_64", "aarch64"):
            for mode in ("eval", "capture"):
                bpf = oracle._build_confinement_seccomp_bpf(arch, confinement=mode)
                self.assertEqual(len(bpf) % 8, 0)

        # Strict `eval` confinement must enforce Landlock (no `/proc`, no
        # unlisted paths, no writes anywhere), default-deny seccomp allowlist
        # (blocking fork, threads, setsid, setpgid, pipe, socket, socketpair,
        # eventfd, SysV IPC, memfd_create, and FS mutations), RLIMIT_NOFILE,
        # and a non-dumpable parent, while still allowing read-only access to
        # explicit `read_only_paths` and stdout pipes.
        with (
            tempfile.TemporaryDirectory(prefix="miri-eval-ro-") as ro_dir,
            tempfile.TemporaryDirectory(prefix="miri-eval-secret-") as secret_dir,
        ):
            ro_path = Path(ro_dir)
            existing = ro_path / "existing.txt"
            existing.write_text("hello", encoding="utf-8")
            unlisted = Path(secret_dir) / "secret.txt"
            unlisted.write_text("top-secret", encoding="utf-8")
            grandparent_pid = os.getppid()
            probe = (
                "import array, ctypes, errno, fcntl, os, resource, socket, threading\n"
                f"ro_dir = {str(ro_path)!r}\n"
                f"existing = {str(existing)!r}\n"
                f"unlisted = {str(unlisted)!r}\n"
                f"parent_pid = {os.getpid()}\n"
                f"parent_env = f'/proc/{{{os.getpid()}}}/environ'\n"
                f"grandparent_env = f'/proc/{{{grandparent_pid}}}/environ'\n"
                "def expect_blocked(name, fn):\n"
                "    try:\n"
                "        fn()\n"
                "    except (PermissionError, RuntimeError):\n"
                "        return\n"
                "    except OSError as exc:\n"
                "        if exc.errno in (errno.EPERM, errno.EACCES, errno.EFBIG, errno.EMFILE):\n"
                "            return\n"
                "        raise\n"
                "    raise SystemExit(f'{name} was not blocked')\n"
                "expect_blocked('fork', os.fork)\n"
                "expect_blocked('thread', lambda: threading.Thread(target=lambda: None).start())\n"
                "expect_blocked('pipe', os.pipe)\n"
                "expect_blocked('socket', lambda: socket.socket(socket.AF_UNIX, socket.SOCK_STREAM))\n"
                "expect_blocked('socketpair', lambda: socket.socketpair())\n"
                "if hasattr(os, 'eventfd'):\n"
                "    expect_blocked('eventfd', lambda: os.eventfd(0))\n"
                "libc = ctypes.CDLL(None, use_errno=True)\n"
                "assert libc.shmget(0, 4096, 0o600 | 0o1000) == -1 and ctypes.get_errno() == errno.EPERM\n"
                "# Filesystem/device/TTY ioctls must be denied even on O_RDONLY fds;\n"
                "# only FIOCLEX (0x5451, process-private FD_CLOEXEC) is allowed.\n"
                "ro_fd = os.open(existing, os.O_RDONLY)\n"
                "try:\n"
                "    expect_blocked('ioctl_getflags', lambda: fcntl.ioctl(ro_fd, 0x80086601, array.array('l', [0])))\n"
                "    expect_blocked('ioctl_setflags', lambda: fcntl.ioctl(ro_fd, 0x40086602, array.array('l', [0])))\n"
                "    expect_blocked('ioctl_tiocsti', lambda: fcntl.ioctl(ro_fd, 0x5412, b'x'))\n"
                "    fcntl.ioctl(ro_fd, 0x5451)\n"
                "    # fcntl must deny F_SETOWN, F_SETSIG, F_SETFL|O_ASYNC, F_SETPIPE_SZ,\n"
                "    # and non-zero upper-32-bit cmd values, while allowing safe FD/FL queries\n"
                "    # and non-O_ASYNC F_SETFL/F_DUPFD_CLOEXEC.\n"
                "    expect_blocked('fcntl_setown', lambda: fcntl.fcntl(1, fcntl.F_SETOWN, parent_pid))\n"
                "    expect_blocked('fcntl_setsig', lambda: fcntl.fcntl(1, 10, 9))\n"
                "    expect_blocked('fcntl_setfl_o_async_stdout', lambda: fcntl.fcntl(1, fcntl.F_SETFL, fcntl.fcntl(1, fcntl.F_GETFL) | 0x2000))\n"
                "    expect_blocked('fcntl_setfl_o_async_ro', lambda: fcntl.fcntl(ro_fd, fcntl.F_SETFL, 0x2000))\n"
                "    expect_blocked('fcntl_setpipe_sz', lambda: fcntl.fcntl(1, 1031, 4096))\n"
                "    # Non-zero upper 32 bits in fcntl cmd or F_SETFL flags must be denied.\n"
                "    import platform as _plat\n"
                "    _fcntl_nr = 72 if _plat.machine().lower() in ('x86_64', 'amd64') else 25\n"
                "    libc.syscall.argtypes = [ctypes.c_long, ctypes.c_long, ctypes.c_uint64, ctypes.c_uint64]\n"
                "    libc.syscall.restype = ctypes.c_long\n"
                "    assert libc.syscall(_fcntl_nr, ro_fd, (1 << 32) | 1, 0) == -1 and ctypes.get_errno() == errno.EPERM\n"
                "    assert libc.syscall(_fcntl_nr, ro_fd, 4, (1 << 32)) == -1 and ctypes.get_errno() == errno.EPERM\n"
                "    cur_fd = fcntl.fcntl(ro_fd, fcntl.F_GETFD)\n"
                "    fcntl.fcntl(ro_fd, fcntl.F_SETFD, cur_fd | fcntl.FD_CLOEXEC)\n"
                "    cur_fl = fcntl.fcntl(ro_fd, fcntl.F_GETFL)\n"
                "    fcntl.fcntl(ro_fd, fcntl.F_SETFL, cur_fl | os.O_NONBLOCK)\n"
                "    dup_fd = fcntl.fcntl(ro_fd, fcntl.F_DUPFD_CLOEXEC, 0)\n"
                "    os.close(dup_fd)\n"
                "finally:\n"
                "    os.close(ro_fd)\n"
                "# prlimit64 is permitted only for pid==0 (self), never for other PIDs.\n"
                "assert resource.prlimit(0, resource.RLIMIT_NOFILE)[1] <= 32\n"
                "expect_blocked('prlimit_parent', lambda: resource.prlimit(parent_pid, resource.RLIMIT_NOFILE))\n"
                "expect_blocked('prlimit_self_pid', lambda: resource.prlimit(os.getpid(), resource.RLIMIT_NOFILE))\n"
                "expect_blocked('open_write', lambda: open(os.path.join(ro_dir, 'new.txt'), 'w'))\n"
                "expect_blocked('open_rw', lambda: open(existing, 'r+'))\n"
                "expect_blocked('mkdir', lambda: os.mkdir(os.path.join(ro_dir, 'sub')))\n"
                "expect_blocked('truncate', lambda: os.truncate(existing, 0))\n"
                "expect_blocked('unlink', lambda: os.unlink(existing))\n"
                "expect_blocked('proc_list', lambda: os.listdir('/proc'))\n"
                "expect_blocked('parent_environ', lambda: open(parent_env, 'rb').read())\n"
                "expect_blocked('grandparent_environ', lambda: open(grandparent_env, 'rb').read())\n"
                "expect_blocked('unlisted_file', lambda: open(unlisted, 'rb').read())\n"
                "if hasattr(os, 'memfd_create'):\n"
                "    expect_blocked('memfd_create', lambda: os.memfd_create('x'))\n"
                "# RLIMIT_NOFILE must bound simultaneous open descriptors.\n"
                "fds = []\n"
                "hit_emfile = False\n"
                "try:\n"
                "    for _ in range(64):\n"
                "        fds.append(os.open(existing, os.O_RDONLY))\n"
                "except OSError as exc:\n"
                "    hit_emfile = exc.errno == errno.EMFILE\n"
                "finally:\n"
                "    for fd in fds:\n"
                "        os.close(fd)\n"
                "assert hit_emfile, 'RLIMIT_NOFILE did not cap open FDs'\n"
                "assert open(existing, 'rb').read() == b'hello'\n"
                "assert 'existing.txt' in os.listdir(ro_dir)\n"
            )
            rc_sec, out_sec, err_sec, _ = oracle.run_bounded(
                [sys.executable, "-I", "-B", "-c", probe],
                env=oracle.sanitized_child_env(),
                timeout_secs=10,
                max_memory_mb=256,
                read_only_paths=(ro_path,),
            )
            self.assertEqual(rc_sec, 0, f"stdout={out_sec!r} stderr={err_sec!r}")
            self.assertFalse((ro_path / "new.txt").exists())
            self.assertEqual(existing.read_text(encoding="utf-8"), "hello")
            self.assertGreater(len(oracle._build_confinement_seccomp_bpf("aarch64")), 0)

            # Non-vacuous _harden_parent_process() (PR_SET_DUMPABLE=0) test:
            # verify PR_GET_DUMPABLE == 0 directly AND verify from an
            # unconfined child (where `/proc` IS listable) that
            # `/proc/<parent_pid>/environ` is still denied with EACCES.
            import ctypes

            oracle._harden_parent_process()
            libc_p = ctypes.CDLL(None, use_errno=True)
            self.assertEqual(
                libc_p.prctl(oracle._PR_GET_DUMPABLE, 0, 0, 0, 0), 0
            )
            dumpable_probe = (
                "import os\n"
                f"parent_env = '/proc/{os.getpid()}/environ'\n"
                "assert len(os.listdir('/proc')) > 0\n"
                "try:\n"
                "    open(parent_env, 'rb').read()\n"
                "except PermissionError:\n"
                "    pass\n"
                "else:\n"
                "    raise SystemExit('unconfined child read parent /proc/<pid>/environ')\n"
            )
            r_dump = subprocess.run(
                [sys.executable, "-I", "-B", "-c", dumpable_probe],
                env=oracle.sanitized_child_env(),
                capture_output=True,
                text=True,
                timeout=10,
                check=False,
            )
            self.assertEqual(
                r_dump.returncode, 0, f"stdout={r_dump.stdout!r} stderr={r_dump.stderr!r}"
            )

            # Capture confinement must isolate inside private user/PID/mount/
            # network namespaces, enforce Landlock ABI >= 3 (writes/truncates
            # allowed strictly inside the bounded `tmpfs` work dir, denied on
            # `read_only_paths` and unlisted paths, `/proc` enumeration denied),
            # enforce default-deny seccomp (blocking nested userns via
            # `unshare`/`clone`/`clone3`, `kill`, `ptrace`, `prlimit64` on peer
            # PIDs, sockets, eventfd, memfd_create, SysV IPC), cap
            # `RLIMIT_NOFILE` and `RLIMIT_NPROC`, enforce aggregate disk quota
            # via `tmpfs`, and export bounded regular output files after
            # PID-namespace teardown.
            with (
                tempfile.TemporaryDirectory(prefix="miri-cap-rw-") as rw_dir,
                tempfile.TemporaryDirectory(prefix="miri-cap-exp-") as exp_dir,
            ):
                rw_path = Path(rw_dir)
                exp_path = Path(exp_dir)
                capture_iso_probe = (
                    "import ctypes, errno, os, pathlib, platform, resource, socket\n"
                    f"ro_dir = pathlib.Path({str(ro_path)!r})\n"
                    f"existing = pathlib.Path({str(existing)!r})\n"
                    f"rw_dir = pathlib.Path({str(rw_path)!r})\n"
                    f"unlisted = pathlib.Path({str(unlisted)!r})\n"
                    f"parent_pid = {os.getpid()}\n"
                    f"parent_env = '/proc/{os.getpid()}/environ'\n"
                    "# Capture child runs as PID 1 inside its isolated PID namespace,\n"
                    "# as a non-root UID with all Linux capability sets cleared.\n"
                    "assert os.getpid() == 1, f'expected PID 1 in CLONE_NEWPID, got {os.getpid()}'\n"
                    "assert os.getuid() != 0 and os.geteuid() != 0, f'unexpected root UID: {os.getuid()}/{os.geteuid()}'\n"
                    "status_fields = dict(\n"
                    "    ln.split(':', 1)\n"
                    "    for ln in pathlib.Path('/proc/self/status').read_text(encoding='utf-8').splitlines()\n"
                    "    if ':' in ln\n"
                    ")\n"
                    "for cap_key in ('CapInh', 'CapPrm', 'CapEff', 'CapBnd', 'CapAmb'):\n"
                    "    if cap_key in status_fields:\n"
                    "        assert int(status_fields[cap_key].strip(), 16) == 0, f'{cap_key} not cleared: {status_fields[cap_key]}'\n"
                    "# Private mount propagation: rw_dir tmpfs must not be shared with host.\n"
                    "rw_mount_lines = [\n"
                    "    ln for ln in pathlib.Path('/proc/self/mountinfo').read_text(encoding='utf-8').splitlines()\n"
                    "    if f' {rw_dir} ' in ln\n"
                    "]\n"
                    "assert rw_mount_lines, 'rw_dir tmpfs mount missing from /proc/self/mountinfo'\n"
                    "for ln in rw_mount_lines:\n"
                    "    opt_fields = ln.split(' - ', 1)[0].split()[6:]\n"
                    "    assert not any(tok.startswith('shared:') for tok in opt_fields), f'shared mount propagation leaked: {ln}'\n"
                    "# Writes + intra-dir rename inside bounded tmpfs work_dir/out succeed,\n"
                    "# including sharded sibling `Captured/` directory alongside `capture.json`.\n"
                    "out_d = rw_dir / 'out'\n"
                    "out_d.mkdir()\n"
                    "(out_d / 'Captured').mkdir()\n"
                    "(out_d / 'Captured' / 'Shard0.lean').write_text('-- shard', encoding='utf-8')\n"
                    "tmp_f = rw_dir / 'tmp' / 'a.tmp'\n"
                    "tmp_f.write_text('ok', encoding='utf-8')\n"
                    "os.replace(tmp_f, out_d / 'capture.json')\n"
                    "assert existing.read_text(encoding='utf-8') == 'hello'\n"
                    "# Writes/truncates/fchmod outside rw_dir (including system paths\n"
                    "# such as /dev/null, /etc/ld.so.cache, and /usr) and unlisted reads fail.\n"
                    "for label, fn in (\n"
                    "    ('write_ro', lambda: (ro_dir / 'evil.txt').write_text('x')),\n"
                    "    ('truncate_ro', lambda: os.truncate(existing, 0)),\n"
                    "    ('fchmod_ro', lambda: (lambda fd: (os.fchmod(fd, 0), os.close(fd)))(os.open(existing, os.O_RDONLY))),\n"
                    "    ('fchmod_dev_null', lambda: (lambda fd: (os.fchmod(fd, 0o666), os.close(fd)))(os.open('/dev/null', os.O_RDONLY))),\n"
                    "    ('fchmod_ld_cache', lambda: (lambda fd: (os.fchmod(fd, 0o644), os.close(fd)))(os.open('/etc/ld.so.cache', os.O_RDONLY))),\n"
                    "    ('fchmod_usr', lambda: (lambda fd: (os.fchmod(fd, 0o755), os.close(fd)))(os.open('/usr', os.O_RDONLY))),\n"
                    "    ('read_unlisted', lambda: unlisted.read_bytes()),\n"
                    "    ('write_unlisted', lambda: (unlisted.parent / 'evil.txt').write_text('x')),\n"
                    "    ('proc_list', lambda: os.listdir('/proc')),\n"
                    "    ('parent_environ', lambda: open(parent_env, 'rb').read()),\n"
                    "):\n"
                    "    try:\n"
                    "        fn()\n"
                    "    except PermissionError:\n"
                    "        if label.startswith('fchmod_'):\n"
                    "            raise SystemExit(f'{label} must fail with EROFS, not EPERM')\n"
                    "        continue\n"
                    "    except OSError as exc:\n"
                    "        if label.startswith('fchmod_'):\n"
                    "            if exc.errno == errno.EROFS:\n"
                    "                continue\n"
                    "            raise SystemExit(f'{label} expected EROFS, got errno={exc.errno}')\n"
                    "        if exc.errno in (errno.EROFS, errno.EACCES, errno.EPERM):\n"
                    "            continue\n"
                    "        raise\n"
                    "    raise SystemExit(f'capture isolation did not block {label}')\n"
                    "# Default-deny capture seccomp must block nested userns (unshare,\n"
                    "# clone(CLONE_NEWUSER), clone3), peer control (kill, ptrace,\n"
                    "# prlimit64(other)), and unnecessary kernel-object syscalls.\n"
                    "libc = ctypes.CDLL(None, use_errno=True)\n"
                    "assert libc.unshare(0x10000000) == -1 and ctypes.get_errno() == errno.EPERM\n"
                    "is_x86 = platform.machine().lower() in ('x86_64', 'amd64')\n"
                    "clone_nr = 56 if is_x86 else 220\n"
                    "ptrace_nr = 101 if is_x86 else 117\n"
                    "libc.syscall.restype = ctypes.c_long\n"
                    "# clone with CLONE_NEWUSER | SIGCHLD must return EPERM.\n"
                    "assert libc.syscall(ctypes.c_long(clone_nr), ctypes.c_uint64(0x10000011), ctypes.c_void_p(0), ctypes.c_void_p(0), ctypes.c_void_p(0), ctypes.c_uint64(0)) == -1 and ctypes.get_errno() == errno.EPERM\n"
                    "# clone3 must return ENOSYS so glibc falls back to filtered clone.\n"
                    "assert libc.syscall(ctypes.c_long(435), ctypes.c_void_p(0), ctypes.c_size_t(0)) == -1 and ctypes.get_errno() == errno.ENOSYS\n"
                    "# kill, ptrace, and prlimit64 on peer PIDs must return EPERM.\n"
                    "assert libc.kill(parent_pid, 0) == -1 and ctypes.get_errno() == errno.EPERM\n"
                    "assert libc.syscall(ctypes.c_long(ptrace_nr), ctypes.c_long(16), ctypes.c_long(parent_pid), ctypes.c_void_p(0), ctypes.c_void_p(0)) == -1 and ctypes.get_errno() == errno.EPERM\n"
                    "for label, fn in (\n"
                    "    ('prlimit_parent', lambda: resource.prlimit(parent_pid, resource.RLIMIT_NOFILE)),\n"
                    "    ('socket', lambda: socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)),\n"
                    "    ('socketpair', lambda: socket.socketpair()),\n"
                    "):\n"
                    "    try:\n"
                    "        fn()\n"
                    "    except PermissionError:\n"
                    "        continue\n"
                    "    raise SystemExit(f'capture seccomp did not block {label}')\n"
                    "if hasattr(os, 'eventfd'):\n"
                    "    try:\n"
                    "        os.eventfd(0)\n"
                    "        raise SystemExit('capture seccomp did not block eventfd')\n"
                    "    except PermissionError:\n"
                    "        pass\n"
                    "if hasattr(os, 'memfd_create'):\n"
                    "    try:\n"
                    "        os.memfd_create('x')\n"
                    "        raise SystemExit('capture seccomp did not block memfd_create')\n"
                    "    except PermissionError:\n"
                    "        pass\n"
                    "assert libc.shmget(0, 4096, 0o600 | 0o1000) == -1 and ctypes.get_errno() == errno.EPERM\n"
                    "# RLIMIT_NOFILE must bound simultaneous open descriptors in capture mode.\n"
                    f"assert resource.prlimit(0, resource.RLIMIT_NOFILE)[1] <= {oracle.CAPTURE_MAX_NOFILE}\n"
                    "fds = []\n"
                    "hit_emfile = False\n"
                    "try:\n"
                    f"    for _ in range({oracle.CAPTURE_MAX_NOFILE + 32}):\n"
                    "        fds.append(os.open(existing, os.O_RDONLY))\n"
                    "except OSError as exc:\n"
                    "    hit_emfile = exc.errno == errno.EMFILE\n"
                    "finally:\n"
                    "    for fd in fds:\n"
                    "        os.close(fd)\n"
                    "assert hit_emfile, 'capture RLIMIT_NOFILE did not cap open FDs'\n"
                    "# Bounded tmpfs must enforce aggregate disk quota across multiple files.\n"
                    "hit_enospc = False\n"
                    "created = []\n"
                    "chunk = b'A' * (2 * 1024 * 1024)\n"
                    "try:\n"
                    "    for i in range(24):\n"
                    "        p = rw_dir / 'tmp' / f'fill_{i}.bin'\n"
                    "        created.append(p)\n"
                    "        with open(p, 'wb') as fh:\n"
                    "            fh.write(chunk)\n"
                    "except OSError as exc:\n"
                    "    hit_enospc = exc.errno == errno.ENOSPC\n"
                    "finally:\n"
                    "    for p in created:\n"
                    "        try:\n"
                    "            p.unlink()\n"
                    "        except OSError:\n"
                    "            pass\n"
                    "assert hit_enospc, 'capture tmpfs did not enforce aggregate disk quota'\n"
                    "# Kernel task cap (max_tasks=4) must synchronously reject tight fork loops.\n"
                    "r_fd, w_fd = os.pipe()\n"
                    "pids = []\n"
                    "hit_eagain = False\n"
                    "try:\n"
                    "    for _ in range(16):\n"
                    "        pid = os.fork()\n"
                    "        if pid == 0:\n"
                    "            os.close(w_fd)\n"
                    "            os.read(r_fd, 1)\n"
                    "            os._exit(0)\n"
                    "        pids.append(pid)\n"
                    "except OSError as exc:\n"
                    "    hit_eagain = exc.errno in (errno.EAGAIN, errno.ENOMEM)\n"
                    "finally:\n"
                    "    os.close(w_fd)\n"
                    "    os.close(r_fd)\n"
                    "    for pid in pids:\n"
                    "        try:\n"
                    "            os.waitpid(pid, 0)\n"
                    "        except OSError:\n"
                    "            pass\n"
                    "assert hit_eagain, f'kernel task cap did not trigger (spawned {len(pids)})'\n"
                    "assert len(pids) <= 3, f'kernel task cap exceeded: {len(pids)}'\n"
                )
                rc_cap, out_cap, err_cap, _ = oracle.run_bounded(
                    [sys.executable, "-I", "-B", "-c", capture_iso_probe],
                    env=oracle.sanitized_child_env(),
                    timeout_secs=10,
                    max_memory_mb=256,
                    confinement="capture",
                    max_procs=None,
                    max_tasks=4,
                    read_only_paths=(ro_path,),
                    read_write_paths=(rw_path,),
                    export_src=rw_path / "out" / "capture.json",
                    export_dst=exp_path / "capture.json",
                )
                self.assertEqual(
                    rc_cap, 0, f"stdout={out_cap!r} stderr={err_cap!r}"
                )
                self.assertEqual(
                    (exp_path / "capture.json").read_text(encoding="utf-8"), "ok"
                )
                self.assertFalse((exp_path / "Captured").exists())
                self.assertEqual(existing.read_text(encoding="utf-8"), "hello")
                self.assertFalse((ro_path / "evil.txt").exists())
                self.assertFalse((Path(secret_dir) / "evil.txt").exists())

                # Export helper must reject symlinks and non-regular entries.
                bad_src = Path(secret_dir) / "bad_out"
                bad_src.mkdir()
                (bad_src / "link.json").symlink_to(existing)
                with self.assertRaises(OSError):
                    oracle._export_capture_file(
                        bad_src / "link.json", exp_path / "sym.json"
                    )
                (bad_src / "link.json").unlink()
                (bad_src / "subdir").mkdir()
                with self.assertRaises(oracle.OracleError):
                    oracle._export_capture_file(
                        bad_src / "subdir", exp_path / "dir.json"
                    )

            # Non-vacuous `setsid`/`setpgid` confinement test:
            # inside a `start_new_session=True` leader, `setsid()` and
            # `setpgid(0, 0)` return `EPERM` even without seccomp. Verify
            # first via an unconfined control that forked non-leader children
            # succeed at both `os.setsid()` and `os.setpgid(0, 0)`, then
            # verify that both are blocked with `EPERM` in a forked non-leader
            # child under `confinement="capture"` (exercising `session_nrs`)
            # and in a non-leader child under `confinement="eval"`.
            non_leader_probe = (
                "import errno, os, sys\n"
                "expect_eperm = sys.argv[1] == 'blocked'\n"
                "for label, op in (('setsid', 'setsid'), ('setpgid', 'setpgid')):\n"
                "    pid = os.fork()\n"
                "    if pid == 0:\n"
                "        try:\n"
                "            if op == 'setsid':\n"
                "                os.setsid()\n"
                "            else:\n"
                "                os.setpgid(0, 0)\n"
                "            os._exit(10 if expect_eperm else 0)\n"
                "        except PermissionError:\n"
                "            os._exit(0 if expect_eperm else 20)\n"
                "        except OSError as exc:\n"
                "            os._exit(0 if (expect_eperm and exc.errno == errno.EPERM) else 30)\n"
                "    _, status = os.waitpid(pid, 0)\n"
                "    if not os.WIFEXITED(status) or os.WEXITSTATUS(status) != 0:\n"
                "        raise SystemExit(f'{label} unexpected status={status}')\n"
            )
            ctrl_proc = subprocess.run(
                [sys.executable, "-I", "-B", "-c", non_leader_probe, "allowed"],
                start_new_session=True,
                capture_output=True,
                text=True,
                timeout=10,
                check=False,
            )
            self.assertEqual(
                ctrl_proc.returncode,
                0,
                f"unconfined non-leader control failed: {ctrl_proc.stderr!r}",
            )
            rc_cap_sess, out_cs, err_cs, _ = oracle.run_bounded(
                [sys.executable, "-I", "-B", "-c", non_leader_probe, "blocked"],
                env=oracle.sanitized_child_env(),
                timeout_secs=10,
                max_memory_mb=256,
                confinement="capture",
                max_procs=2,
            )
            self.assertEqual(
                rc_cap_sess, 0, f"capture setsid/setpgid failed: out={out_cs!r} err={err_cs!r}"
            )

            eval_sess_cmd = oracle._wrap_with_confinement(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    "-c",
                    (
                        "import errno, os\n"
                        "for name, fn in (('setsid', os.setsid), ('setpgid', lambda: os.setpgid(0, 0))):\n"
                        "    try:\n"
                        "        fn()\n"
                        "    except PermissionError:\n"
                        "        continue\n"
                        "    except OSError as exc:\n"
                        "        if exc.errno == errno.EPERM:\n"
                        "            continue\n"
                        "        raise\n"
                        "    raise SystemExit(f'{name} was not blocked')\n"
                    ),
                ],
                timeout_secs=10,
                max_memory_mb=256,
                confinement="eval",
            )
            # Launch from a forked non-leader helper without `start_new_session`
            # and verify `getsid(0) != getpid()` before exec so the eval child
            # is guaranteed NOT to be a session leader.
            non_leader_eval_launcher = (
                "import os, subprocess, sys\n"
                f"cmd = {eval_sess_cmd!r}\n"
                "pid = os.fork()\n"
                "if pid == 0:\n"
                "    assert os.getsid(0) != os.getpid(), 'must not be session leader'\n"
                "    os.execv(cmd[0], cmd)\n"
                "_, status = os.waitpid(pid, 0)\n"
                "raise SystemExit(os.WEXITSTATUS(status) if os.WIFEXITED(status) else 99)\n"
            )
            eval_sess_proc = subprocess.run(
                [sys.executable, "-I", "-B", "-c", non_leader_eval_launcher],
                env=oracle.sanitized_child_env(),
                start_new_session=True,
                capture_output=True,
                text=True,
                timeout=10,
                check=False,
            )
            self.assertEqual(
                eval_sess_proc.returncode,
                0,
                f"non-leader eval setsid/setpgid failed: {eval_sess_proc.stderr!r}",
            )

            # Interruption & parent-death cleanup:
            # 1. `KeyboardInterrupt` inside `run_bounded` must immediately kill
            #    the confined sleeping child process group.
            # 2. `SIGKILL` of a parent harness must terminate a sleeping
            #    confined child via Linux `PR_SET_PDEATHSIG`.
            import signal as _sig
            import time as _time

            def _pid_alive(pid: int) -> bool:
                try:
                    os.kill(pid, 0)
                    return True
                except ProcessLookupError:
                    return False

            pid_file = Path(tmp_path := ro_path) / "sleep_pid.txt"
            captured_child_pid: list[int] = []
            orig_popen = oracle.subprocess.Popen

            def _spy_popen(*args, **kwargs):
                p = orig_popen(*args, **kwargs)
                captured_child_pid.append(p.pid)
                return p

            wait_calls = 0
            orig_event_wait = oracle.threading.Event.wait

            def _interrupting_wait(self_ev, timeout=None):
                nonlocal wait_calls
                wait_calls += 1
                if wait_calls == 2:
                    raise KeyboardInterrupt("simulated Ctrl-C")
                return orig_event_wait(self_ev, timeout=timeout)

            with (
                mock.patch.object(oracle.subprocess, "Popen", side_effect=_spy_popen),
                mock.patch.object(oracle.threading.Event, "wait", _interrupting_wait),
            ):
                with self.assertRaises(KeyboardInterrupt):
                    oracle.run_bounded(
                        [sys.executable, "-I", "-B", "-c", "import time; time.sleep(30)"],
                        env=oracle.sanitized_child_env(),
                        timeout_secs=30,
                        max_memory_mb=256,
                        confinement="eval",
                    )
            self.assertEqual(len(captured_child_pid), 1)
            self.assertFalse(
                _pid_alive(captured_child_pid[0]),
                "sleeping confined child survived KeyboardInterrupt",
            )

            pdeath_launcher = (
                "import os, subprocess, sys, time\n"
                f"sys.path.insert(0, {str(CI_DIR)!r})\n"
                "import run_miri_ub_oracle as oracle\n"
                "cmd = oracle._wrap_with_confinement(\n"
                "    [sys.executable, '-I', '-B', '-c', 'import time; time.sleep(30)'],\n"
                "    timeout_secs=30, max_memory_mb=256, confinement='eval',\n"
                "    parent_pid=os.getpid(),\n"
                ")\n"
                "p = subprocess.Popen(cmd, env=oracle.sanitized_child_env(), start_new_session=True)\n"
                "print(p.pid, flush=True)\n"
                "time.sleep(30)\n"
            )
            mid = subprocess.Popen(
                [sys.executable, "-I", "-B", "-c", pdeath_launcher],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            try:
                assert mid.stdout is not None
                child_pid = int(mid.stdout.readline().strip())
                # Wait briefly so `--_confined-exec` installs PR_SET_PDEATHSIG.
                _time.sleep(0.3)
                os.kill(mid.pid, _sig.SIGKILL)
                mid.wait(timeout=5)
                deadline_pd = _time.monotonic() + 3.0
                while _pid_alive(child_pid) and _time.monotonic() < deadline_pd:
                    _time.sleep(0.05)
                self.assertFalse(
                    _pid_alive(child_pid),
                    f"confined child {child_pid} survived parent SIGKILL",
                )
            finally:
                if mid.poll() is None:
                    mid.kill()
                    mid.wait(timeout=5)
                if mid.stdout is not None:
                    mid.stdout.close()
                if mid.stderr is not None:
                    mid.stderr.close()
            del pid_file

        # A child exceeding RLIMIT_AS must fail rather than exhaust host RAM.
        rc, _, _, _ = oracle.run_bounded(
            [sys.executable, "-c", "buf = bytearray(400 * 1024 * 1024)"],
            env=oracle.sanitized_child_env(),
            timeout_secs=10,
            max_memory_mb=256,
        )
        self.assertNotEqual(rc, 0)

        # Even in capture confinement mode, exceeding max_procs kills the PGID.
        fork_probe = (
            "import os, time\n"
            "for _ in range(2):\n"
            "    pid = os.fork()\n"
            "    if pid == 0:\n"
            "        time.sleep(5)\n"
            "        os._exit(0)\n"
            "time.sleep(5)\n"
        )
        rc_p, _, _, elapsed_p = oracle.run_bounded(
            [sys.executable, "-I", "-B", "-c", fork_probe],
            env=oracle.sanitized_child_env(),
            timeout_secs=10,
            max_memory_mb=256,
            confinement="capture",
            max_procs=2,
        )
        self.assertEqual(rc_p, "process_limit")
        self.assertLess(elapsed_p, 3.0)

        # If /proc enumeration fails, max_procs enforcement must fail closed.
        from unittest import mock

        with mock.patch.object(
            oracle, "_count_pgid_processes", return_value=None
        ):
            rc_fc, _, _, _ = oracle.run_bounded(
                [sys.executable, "-I", "-B", "-c", "import time; time.sleep(5)"],
                env=oracle.sanitized_child_env(),
                timeout_secs=10,
                max_memory_mb=256,
                confinement="capture",
                max_procs=2,
            )
        self.assertEqual(rc_fc, "process_limit")

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
            mock.patch.object(oracle, "_kill_process_group", side_effect=tracked_kill),
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

            with mock.patch.object(oracle, "MAX_PIN_BYTES", 64):
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
                mock.patch.object(oracle, "MAX_TAR_MEMBERS", 3),
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
            with mock.patch.object(oracle, "MAX_SINGLE_FILE_BYTES", 32):
                with self.assertRaisesRegex(
                    oracle.OracleError, "exceeds size limit"
                ):
                    oracle.compute_corpus_manifest_sha256(big_root, ["tests/fail"])
            with (
                mock.patch.object(oracle, "MAX_SINGLE_FILE_BYTES", 100),
                mock.patch.object(oracle, "MAX_TOTAL_EXTRACTED_BYTES", 100),
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


class StubbedEndToEndTests(unittest.TestCase):
    def _build_stubs(self, root: Path, *, eval_mode: str = "normal") -> tuple[Path, Path, Path]:
        sysroot = root / "sysroot"
        (sysroot / "lib").mkdir(parents=True)
        cap_bin = root / "fake-capture"
        eval_bin = root / "fake-eval"

        _write_executable(
            cap_bin,
            f"""#!{sys.executable}
import json, pathlib, sys
args = sys.argv[1:]
src = pathlib.Path(args[args.index("--crate-root") + 1]).read_text()
out = pathlib.Path(args[args.index("--out-dir") + 1])
out.mkdir(parents=True, exist_ok=True)
if "CAPTURE_REFUSE" in src:
    print(json.dumps({{"status": "unsupported", "unsupported": [{{"reason": "stub refused"}}]}}))
    sys.exit(1)
(out / "capture.json").write_text(
    json.dumps({{"marker": src.strip(), "compiler": {{"commit": "{ 'f' * 40 }"}}}})
)
print(json.dumps({{"status": "captured"}}))
""",
        )

        _write_executable(
            eval_bin,
            f"""#!{sys.executable}
import json, pathlib, sys
mode = {eval_mode!r}
args = sys.argv[1:]
cap = pathlib.Path(args[1]).read_text()
if mode == "accept_all":
    print(json.dumps({{"outcome": {{"kind": "returned", "value": {{"kind": "returned"}}}}}}))
    sys.exit(0)
if mode == "reject_all":
    print(json.dumps({{"outcome": {{"kind": "fault", "value": {{"kind": "undefined", "reason": "always ub"}}}}}}))
    sys.exit(2)
if "TRIGGER_UB" in cap:
    print(json.dumps({{"outcome": {{"kind": "fault", "value": {{"kind": "undefined", "reason": "stub ub"}}}}}}))
    sys.exit(2)
print(json.dumps({{"outcome": {{"kind": "returned", "value": {{"kind": "returned"}}}}}}))
sys.exit(0)
""",
        )
        return cap_bin, eval_bin, sysroot

    def test_stubbed_tier_a_passes_and_validates_json_schema(self):
        top = "miri-" + "a" * 40
        with tempfile.TemporaryDirectory(prefix="miri-e2e-a-") as tmp:
            tmp_path = Path(tmp)
            archive = tmp_path / "miri.tar.gz"
            ub1_bytes = b"// TRIGGER_UB\nfn main() {}\n"
            refused_bytes = b"// CAPTURE_REFUSE\nfn main() {}\n"
            archive_sha = _make_tar_gz(
                archive,
                [
                    (f"{top}/tests/fail/ub1.rs", ub1_bytes, tarfile.REGTYPE),
                    (f"{top}/tests/fail-dep/refused.rs", refused_bytes, tarfile.REGTYPE),
                ],
            )
            extract_tmp = tmp_path / "hash_check"
            oracle.safe_extract_miri_corpus(
                archive,
                extract_tmp,
                expected_top_dir=top,
                extract_subdirs=["tests/fail", "tests/fail-dep"],
            )
            manifest_sha, _ = oracle.compute_corpus_manifest_sha256(
                extract_tmp, ["tests/fail", "tests/fail-dep"]
            )
            fail_node = {
                "ub1.rs": (
                    b"100644",
                    hashlib.sha1(
                        f"blob {len(ub1_bytes)}\x00".encode("ascii") + ub1_bytes
                    ).digest(),
                )
            }
            fail_dep_node = {
                "refused.rs": (
                    b"100644",
                    hashlib.sha1(
                        f"blob {len(refused_bytes)}\x00".encode("ascii") + refused_bytes
                    ).digest(),
                )
            }
            pin_obj = _sample_pin(
                archive_sha=archive_sha,
                manifest_sha=manifest_sha,
                expected_file_count=2,
                min_caught_ub=1,
            )
            pin_obj["miri_tree_sha"] = oracle._compute_git_tree_sha1(
                {"tests": {"fail": fail_node, "fail-dep": fail_dep_node}}
            ).hex()
            pin_obj["fail_tree_sha"] = oracle._compute_git_tree_sha1(fail_node).hex()
            pin_obj["fail_dep_tree_sha"] = oracle._compute_git_tree_sha1(
                fail_dep_node
            ).hex()
            pin_path = tmp_path / "pin.json"
            pin_path.write_text(json.dumps(pin_obj), encoding="utf-8")
            cap_bin, eval_bin, sysroot = self._build_stubs(tmp_path)
            out_json = tmp_path / "report.json"
            out_md = tmp_path / "summary.md"

            rc = oracle.main([
                "--tier-a",
                "--pin", str(pin_path),
                "--archive", str(archive),
                "--no-network",
                "--capture-bin", str(cap_bin),
                "--eval-bin", str(eval_bin),
                "--sysroot", str(sysroot),
                "--workers", "2",
                "--max-memory-mb", "512",
                "--output", str(out_json),
                "--summary-markdown", str(out_md),
            ])
            self.assertEqual(rc, 0)
            report = json.loads(out_json.read_text(encoding="utf-8"))
            self.assertEqual(report["schema_version"], oracle.REPORT_SCHEMA_VERSION)
            self.assertEqual(report["tier"], "tier_a")
            self.assertTrue(report["passed"])
            self.assertNotIn("elapsed_secs", report)
            for unit in report["units"]:
                self.assertNotIn("capture_secs", unit)
                self.assertNotIn("eval_secs", unit)
            self.assertEqual(report["counts"]["caught_ub"], 1)
            self.assertEqual(report["counts"]["capture_refused"], 1)
            self.assertEqual(report["counts"]["unsound_accept"], 0)
            self.assertIn("PASS", out_md.read_text(encoding="utf-8"))

            # Re-running must produce byte-for-byte identical JSON output.
            out_json2 = tmp_path / "report2.json"
            rc2 = oracle.main([
                "--tier-a",
                "--pin", str(pin_path),
                "--archive", str(archive),
                "--no-network",
                "--capture-bin", str(cap_bin),
                "--eval-bin", str(eval_bin),
                "--sysroot", str(sysroot),
                "--workers", "2",
                "--max-memory-mb", "512",
                "--output", str(out_json2),
            ])
            self.assertEqual(rc2, 0)
            self.assertEqual(
                out_json.read_bytes(), out_json2.read_bytes()
            )

            # Unsound accept with accept_all eval must exit 1.
            cap_bin2, eval_bin2, sysroot2 = self._build_stubs(
                tmp_path / "bad", eval_mode="accept_all"
            )
            rc_bad = oracle.main([
                "--tier-a",
                "--pin", str(pin_path),
                "--archive", str(archive),
                "--no-network",
                "--capture-bin", str(cap_bin2),
                "--eval-bin", str(eval_bin2),
                "--sysroot", str(sysroot2),
                "--workers", "1",
            ])
            self.assertEqual(rc_bad, 1)

    def test_stubbed_tier_b_rejects_orphan_and_reject_all_evaluator(self):
        with tempfile.TemporaryDirectory(prefix="miri-e2e-b-") as tmp:
            tmp_path = Path(tmp)
            corpus = tmp_path / "corpus"
            corpus.mkdir()
            (corpus / "ub.rs").write_text("// TRIGGER_UB\nfn main() {}\n", encoding="utf-8")
            (corpus / "ok.rs").write_text("fn main() {}\n", encoding="utf-8")
            (corpus / "manifest.json").write_text(
                json.dumps({
                    "schema_version": 1,
                    "fixtures": [
                        {
                            "id": "ub1",
                            "path": "ub.rs",
                            "kind": "rust_ub_caught",
                            "category": "arith",
                            "expected_fault_substring": "stub ub",
                        },
                        {"id": "ok1", "path": "ok.rs", "kind": "rust_valid_control", "category": "valid"},
                    ],
                }),
                encoding="utf-8",
            )
            cap_bin, eval_bin, sysroot = self._build_stubs(tmp_path)
            rc = oracle.main([
                "--tier-b",
                "--tier-b-dir", str(corpus),
                "--capture-bin", str(cap_bin),
                "--eval-bin", str(eval_bin),
                "--sysroot", str(sysroot),
                "--workers", "2",
                "--max-memory-mb", "512",
            ])
            self.assertEqual(rc, 0)

            # A reject-all evaluator must fail Tier B on the valid control.
            cap_r, eval_r, sys_r = self._build_stubs(tmp_path / "rej", eval_mode="reject_all")
            rc_rej = oracle.main([
                "--tier-b",
                "--tier-b-dir", str(corpus),
                "--capture-bin", str(cap_r),
                "--eval-bin", str(eval_r),
                "--sysroot", str(sys_r),
                "--workers", "1",
            ])
            self.assertEqual(rc_rej, 1)

            # Adding an unlisted orphan fixture MUST fail closed (exit 2).
            (corpus / "orphan.rs").write_text("fn main() {}\n", encoding="utf-8")
            rc_orphan = oracle.main([
                "--tier-b",
                "--tier-b-dir", str(corpus),
                "--capture-bin", str(cap_bin),
                "--eval-bin", str(eval_bin),
                "--sysroot", str(sysroot),
            ])
            self.assertEqual(rc_orphan, 2)

    def test_capture_rc_status_mismatch_and_bad_tier_b_fields_fail_closed(self):
        with tempfile.TemporaryDirectory(prefix="miri-cap-rc-") as tmp:
            tmp_path = Path(tmp)
            sysroot = tmp_path / "sysroot"
            (sysroot / "lib").mkdir(parents=True)
            cap_bad = tmp_path / "cap-bad"
            eval_ok = tmp_path / "eval-ok"
            _write_executable(
                cap_bad,
                f"""#!{sys.executable}
import json, sys
print(json.dumps({{"status": "unsupported"}}))
sys.exit(0)
""",
            )
            _write_executable(eval_ok, f"#!{sys.executable}\nimport sys; sys.exit(0)\n")
            src = tmp_path / "a.rs"
            src.write_text("fn main() {}\n", encoding="utf-8")
            rec = oracle.evaluate_rust_unit(
                src,
                "fail/a.rs",
                revision=None,
                flags=[],
                capture_bin=cap_bad,
                eval_bin=eval_ok,
                sysroot=sysroot,
                target="x86_64-unknown-linux-gnu",
                fuel=1000,
                profile="v1",
                timeout_secs=10,
                max_memory_mb=oracle.DEFAULT_MAX_MEMORY_MB,
                expect_valid=False,
            )
            self.assertEqual(rec["bucket"], "tool_error")
            self.assertIn("capture_rc_status_mismatch", str(rec["sub_bucket"]))

            # Invalid Tier B optional fields must fail closed at manifest load.
            for label, patch in (
                ("bad_profile", {"profile": "v3"}),
                ("bad_args", {"args": "ab"}),
                ("bad_fuel", {"fuel": 0}),
                ("bad_edition", {"edition": "1999"}),
                ("bad_panic", {"panic": "trap"}),
                ("missing_sub", {"expected_fault_substring": ""}),
            ):
                with self.subTest(case=label):
                    cdir = tmp_path / f"tb-{label}"
                    cdir.mkdir()
                    (cdir / "ub.rs").write_text("fn main() {}\n", encoding="utf-8")
                    (cdir / "ok.rs").write_text("fn main() {}\n", encoding="utf-8")
                    ub_entry = {
                        "id": "ub1",
                        "path": "ub.rs",
                        "kind": "rust_ub_caught",
                        "category": "arith",
                        "expected_fault_substring": "ub",
                    }
                    ub_entry.update(patch)
                    (cdir / "manifest.json").write_text(
                        json.dumps({
                            "schema_version": 1,
                            "fixtures": [
                                ub_entry,
                                {"id": "ok1", "path": "ok.rs", "kind": "rust_valid_control", "category": "valid"},
                            ],
                        }),
                        encoding="utf-8",
                    )
                    with self.assertRaises(oracle.OracleError):
                        oracle.load_tier_b_manifest(cdir)


class RealTierBCorpusHygieneTests(unittest.TestCase):
    def test_real_tier_b_manifest_and_fixtures_are_original_and_clean(self):
        from unittest import mock

        real_pin = oracle.load_pin(oracle.DEFAULT_PIN_PATH)
        manifest = oracle.load_tier_b_manifest(
            oracle.DEFAULT_TIER_B_DIR,
            expected_corpus_sha256=str(real_pin["tier_b_corpus_sha256"]),
            min_kind_counts=dict(real_pin["tier_b_min_counts"]),
        )
        fixtures = manifest["fixtures"]
        self.assertEqual(len(fixtures), 47)
        for entry in fixtures:
            path = oracle.DEFAULT_TIER_B_DIR / entry["path"]
            text = path.read_text(encoding="utf-8")
            if path.suffix == ".rs":
                self.assertNotIn("//@", text, f"upstream directive in {entry['path']}")
                self.assertNotIn("//~", text, f"upstream error annotation in {entry['path']}")
                self.assertIn("Licensed under a BSD-style license", text, entry["path"])
                self.assertNotIn(
                    "let _ = unsafe { *",
                    text,
                    f"wildcard pattern avoids deref load in {entry['path']}",
                )

        # Atomic bounded Tier B manifest loading (FIFO / oversized), pinned
        # inventory ratchets (SHA-256 + kind floors), download wall-clock
        # deadline, and single-snapshot `--pin` loading in main().
        with tempfile.TemporaryDirectory(prefix="miri-r14-") as td:
            td_path = Path(td)
            fifo_dir = td_path / "fifo_tb"
            fifo_dir.mkdir()
            os.mkfifo(fifo_dir / "manifest.json")
            with self.assertRaisesRegex(oracle.OracleError, "regular file"):
                oracle.load_tier_b_manifest(fifo_dir)

            big_dir = td_path / "big_tb"
            big_dir.mkdir()
            (big_dir / "manifest.json").write_text("{" + " " * 128 + "}", encoding="utf-8")
            with mock.patch.object(oracle, "MAX_PIN_BYTES", 64):
                with self.assertRaisesRegex(oracle.OracleError, "max size"):
                    oracle.load_tier_b_manifest(big_dir)

            # Weakening a `rust_ub_caught` fixture to `rust_ub_fail_closed` or
            # deleting an entry must fail the pinned Tier B ratchets.
            tamper_dir = td_path / "tamper_tb"
            tamper_dir.mkdir()
            (tamper_dir / "ub.rs").write_text("fn main() {}\n", encoding="utf-8")
            (tamper_dir / "ok.rs").write_text("fn main() {}\n", encoding="utf-8")
            tamper_manifest = {
                "schema_version": 1,
                "fixtures": [
                    {
                        "id": "ub1",
                        "path": "ub.rs",
                        "kind": "rust_ub_caught",
                        "category": "arith",
                        "expected_fault_substring": "ub",
                    },
                    {
                        "id": "ok1",
                        "path": "ok.rs",
                        "kind": "rust_valid_control",
                        "category": "valid",
                    },
                ],
            }
            (tamper_dir / "manifest.json").write_text(
                json.dumps(tamper_manifest), encoding="utf-8"
            )
            good_tb_sha, _ = oracle._walk_corpus_tree(
                tamper_dir, [""], suffixes=(".rs", ".json"), label="Tier B corpus"
            )
            tb_snap = td_path / "tamper_tb_snap"
            with mock.patch.object(
                oracle.os,
                "walk",
                side_effect=AssertionError("Tier B must use bounded os.scandir"),
            ):
                oracle.load_tier_b_manifest(
                    tamper_dir,
                    expected_corpus_sha256=good_tb_sha,
                    snapshot_dir=tb_snap,
                )
            self.assertEqual(
                (tb_snap / "ub.rs").read_text(encoding="utf-8"), "fn main() {}\n"
            )
            # Editing a Tier B fixture without touching manifest.json must
            # invalidate `tier_b_corpus_sha256` (while snapshot stays intact).
            (tamper_dir / "ub.rs").write_text(
                "fn main() { let _ = 1 + 2; }\n", encoding="utf-8"
            )
            self.assertEqual(
                (tb_snap / "ub.rs").read_text(encoding="utf-8"), "fn main() {}\n"
            )
            with self.assertRaisesRegex(oracle.OracleError, "SHA-256 mismatch"):
                oracle.load_tier_b_manifest(
                    tamper_dir,
                    expected_corpus_sha256=good_tb_sha,
                )
            with self.assertRaisesRegex(oracle.OracleError, "regressed"):
                oracle.load_tier_b_manifest(
                    tamper_dir,
                    min_kind_counts={"rust_ub_caught": 2},
                )

            # Bounded Tier B traversal must cap irrelevant empty files and
            # directory depth.
            flood_tb = td_path / "flood_tb"
            flood_tb.mkdir()
            (flood_tb / "manifest.json").write_text(
                json.dumps(tamper_manifest), encoding="utf-8"
            )
            (flood_tb / "ub.rs").write_text("fn main() {}\n", encoding="utf-8")
            (flood_tb / "ok.rs").write_text("fn main() {}\n", encoding="utf-8")
            for idx in range(12):
                (flood_tb / f"noise_{idx}.txt").write_bytes(b"")
            with self.assertRaisesRegex(oracle.OracleError, "max entry limit"):
                oracle.load_tier_b_manifest(flood_tb, max_entries=10)

            deep_tb = td_path / "deep_tb"
            cur_deep = deep_tb
            for idx in range(5):
                cur_deep = cur_deep / f"d{idx}"
                cur_deep.mkdir(parents=True)
            (deep_tb / "manifest.json").write_text(
                json.dumps(tamper_manifest), encoding="utf-8"
            )
            (deep_tb / "ub.rs").write_text("fn main() {}\n", encoding="utf-8")
            (deep_tb / "ok.rs").write_text("fn main() {}\n", encoding="utf-8")
            with self.assertRaisesRegex(oracle.OracleError, "max depth"):
                oracle.load_tier_b_manifest(deep_tb, max_depth=3)

            # Archive extraction recomputes and enforces exact Git tree SHA-1s
            # for root (`miri_tree_sha`), `tests/fail`, and `tests/fail-dep`.
            top = "miri-" + "a" * 40
            tree_tar = td_path / "tree_check.tar.gz"
            _make_tar_gz(
                tree_tar,
                [
                    (f"{top}/README.md", "hi\n", tarfile.REGTYPE),
                    (f"{top}/tests/fail/a.rs", "fn main() {}\n", tarfile.REGTYPE),
                    (f"{top}/tests/fail/a.stderr", "err\n", tarfile.REGTYPE),
                    (f"{top}/tests/fail-dep/b.rs", "fn main() {}\n", tarfile.REGTYPE),
                ],
            )
            def _blob(data: bytes) -> tuple[bytes, bytes]:
                return (
                    b"100644",
                    hashlib.sha1(f"blob {len(data)}\x00".encode("ascii") + data).digest(),
                )
            fail_node = {
                "a.rs": _blob(b"fn main() {}\n"),
                "a.stderr": _blob(b"err\n"),
            }
            fail_dep_node = {"b.rs": _blob(b"fn main() {}\n")}
            root_node = {
                "README.md": _blob(b"hi\n"),
                "tests": {"fail": fail_node, "fail-dep": fail_dep_node},
            }
            exp_trees = {
                "": oracle._compute_git_tree_sha1(root_node).hex(),
                "tests/fail": oracle._compute_git_tree_sha1(fail_node).hex(),
                "tests/fail-dep": oracle._compute_git_tree_sha1(fail_dep_node).hex(),
            }
            oracle.safe_extract_miri_corpus(
                tree_tar,
                td_path / "tree_ok",
                expected_top_dir=top,
                extract_subdirs=["tests/fail", "tests/fail-dep"],
                expected_tree_shas=exp_trees,
            )
            for bad_key in ("", "tests/fail", "tests/fail-dep"):
                bad_trees = dict(exp_trees)
                bad_trees[bad_key] = "0" * 40
                with self.assertRaisesRegex(
                    oracle.OracleError, "Git tree SHA-1 mismatch"
                ):
                    oracle.safe_extract_miri_corpus(
                        tree_tar,
                        td_path / f"tree_bad_{bad_key.replace('/', '_') or 'root'}",
                        expected_top_dir=top,
                        extract_subdirs=["tests/fail", "tests/fail-dep"],
                        expected_tree_shas=bad_trees,
                    )

            # `verify_rustc_miri_linkage` walks documented 40-char Git object
            # SHAs via /git/commits/{sha} and /git/trees/{sha} (never
            # `<commit>:path` path-specs) to verify rust-lang/rust@rustc_commit
            # matches miri_commit and the pinned tests/fail subtree.
            link_pin = dict(real_pin)
            rc_sha = str(link_pin["rustc_commit"])
            mc_sha = str(link_pin["miri_commit"])
            mt_sha = str(link_pin["miri_tree_sha"])
            ft_sha = str(link_pin["fail_tree_sha"])
            root_tree_sha = "1" * 40
            src_tree_sha = "2" * 40
            tools_tree_sha = "3" * 40
            tests_tree_sha = "9" * 40

            api_responses = {
                f"https://api.github.com/repos/rust-lang/rust/git/commits/{rc_sha}": {
                    "sha": rc_sha,
                    "tree": {"sha": root_tree_sha},
                },
                f"https://api.github.com/repos/rust-lang/rust/git/trees/{root_tree_sha}": {
                    "sha": root_tree_sha,
                    "tree": [{"path": "src", "type": "tree", "sha": src_tree_sha}],
                },
                f"https://api.github.com/repos/rust-lang/rust/git/trees/{src_tree_sha}": {
                    "sha": src_tree_sha,
                    "tree": [{"path": "tools", "type": "tree", "sha": tools_tree_sha}],
                },
                f"https://api.github.com/repos/rust-lang/rust/git/trees/{tools_tree_sha}": {
                    "sha": tools_tree_sha,
                    "tree": [{"path": "miri", "type": "tree", "sha": mt_sha}],
                },
                f"https://api.github.com/repos/rust-lang/rust/git/trees/{mt_sha}": {
                    "sha": mt_sha,
                    "tree": [{"path": "tests", "type": "tree", "sha": tests_tree_sha}],
                },
                f"https://api.github.com/repos/rust-lang/rust/git/trees/{tests_tree_sha}": {
                    "sha": tests_tree_sha,
                    "tree": [{"path": "fail", "type": "tree", "sha": ft_sha}],
                },
                f"https://api.github.com/repos/rust-lang/miri/git/commits/{mc_sha}": {
                    "sha": mc_sha,
                    "tree": {"sha": mt_sha},
                },
            }

            class _JsonResp:
                def __init__(self, url: str, body: bytes):
                    self._url = url
                    self._buf = io.BytesIO(body)

                def __enter__(self):
                    return self

                def __exit__(self, *args):
                    return False

                def geturl(self):
                    return self._url

                def read(self, n=-1):
                    return self._buf.read(n)

            class _LinkOpener:
                def __init__(self, table: dict[str, dict[str, object]]):
                    self._table = table

                def open(self, req, timeout=None):
                    assert ":" not in req.full_url.split("://", 1)[1], (
                        f"unexpected path-spec URL: {req.full_url}"
                    )
                    return _JsonResp(
                        req.full_url,
                        json.dumps(self._table[req.full_url]).encode("utf-8"),
                    )

            with mock.patch.object(
                oracle.urllib.request,
                "build_opener",
                return_value=_LinkOpener(api_responses),
            ):
                oracle.verify_rustc_miri_linkage(link_pin)

            # Drifting miri_commit's tree SHA away from rustc_commit fails.
            drifted = dict(api_responses)
            drifted[
                f"https://api.github.com/repos/rust-lang/miri/git/commits/{mc_sha}"
            ] = {"sha": mc_sha, "tree": {"sha": "0" * 40}}
            with mock.patch.object(
                oracle.urllib.request,
                "build_opener",
                return_value=_LinkOpener(drifted),
            ):
                with self.assertRaisesRegex(
                    oracle.OracleError, "root tree SHA mismatch"
                ):
                    oracle.verify_rustc_miri_linkage(link_pin)

            # Drifting fail_tree_sha against rust-lang/rust fails closed.
            drifted_fail = dict(api_responses)
            drifted_fail[
                f"https://api.github.com/repos/rust-lang/rust/git/trees/{tests_tree_sha}"
            ] = {
                "sha": tests_tree_sha,
                "tree": [{"path": "fail", "type": "tree", "sha": "0" * 40}],
            }
            with mock.patch.object(
                oracle.urllib.request,
                "build_opener",
                return_value=_LinkOpener(drifted_fail),
            ):
                with self.assertRaisesRegex(
                    oracle.OracleError, "tests/fail tree SHA mismatch"
                ):
                    oracle.verify_rustc_miri_linkage(link_pin)

            # Archive download must enforce a total wall-clock deadline even
            # when each small chunk arrives before the per-read socket timeout.
            class _SlowResp:
                def __init__(self):
                    self.calls = 0

                def __enter__(self):
                    return self

                def __exit__(self, *args):
                    return False

                def geturl(self):
                    return "https://codeload.github.com/rust-lang/miri/tar.gz/x"

                def read(self, _n):
                    self.calls += 1
                    return b"chunk"

            class _SlowOpener:
                def open(self, _req, timeout=None):
                    return _SlowResp()

            ticks = iter([0.0, 1.0, 2.0, 5.0, 10.0])
            dest_dl = td_path / "dl.tar.gz"
            with (
                mock.patch.object(
                    oracle.urllib.request, "build_opener", return_value=_SlowOpener()
                ),
                mock.patch.object(
                    oracle.time, "monotonic", side_effect=lambda: next(ticks)
                ),
            ):
                with self.assertRaisesRegex(oracle.OracleError, "wall-clock deadline"):
                    oracle.download_verified_archive(
                        "https://github.com/rust-lang/miri/archive/a.tar.gz",
                        "0" * 64,
                        dest_dl,
                        timeout_secs=3.0,
                    )
            self.assertFalse(dest_dl.exists())

            # `main(["--tier-a", ...])` must load `--pin` strictly once and
            # pass that immutable snapshot through sysroot resolution and
            # `run_tier_a` even if the file changes on disk mid-run.
            pin_swap = td_path / "swap_pin.json"
            pin_swap.write_text(json.dumps(real_pin), encoding="utf-8")
            fake_bin = td_path / "bin"
            fake_bin.write_text("#!/bin/sh\n", encoding="utf-8")
            fake_sysroot = td_path / "sysroot"
            fake_sysroot.mkdir()
            load_calls = 0
            orig_load_pin = oracle.load_pin
            seen_pins: list[dict[str, object]] = []

            def counting_load_pin(path):
                nonlocal load_calls
                load_calls += 1
                return orig_load_pin(path)

            def swapping_resolve(explicit, channel):
                pin_swap.write_text("not-json-anymore", encoding="utf-8")
                return fake_sysroot

            def capturing_tier_a(**kwargs):
                seen_pins.append(kwargs["pin"])
                return {
                    "schema_version": 1,
                    "tier": "tier_a",
                    "passed": True,
                    "failures": [],
                    "counts": {},
                    "units": [],
                }

            with (
                mock.patch.object(oracle, "load_pin", side_effect=counting_load_pin),
                mock.patch.object(oracle, "resolve_sysroot", side_effect=swapping_resolve),
                mock.patch.object(oracle, "run_tier_a", side_effect=capturing_tier_a),
            ):
                rc_once = oracle.main([
                    "--tier-a",
                    "--pin", str(pin_swap),
                    "--capture-bin", str(fake_bin),
                    "--eval-bin", str(fake_bin),
                    "--sysroot", str(fake_sysroot),
                ])
            self.assertEqual(rc_once, 0)
            self.assertEqual(load_calls, 1)
            self.assertEqual(len(seen_pins), 1)
            self.assertEqual(seen_pins[0]["miri_commit"], real_pin["miri_commit"])

    def test_child_env_strips_actions_credentials_and_profile_flags_are_explicit(self):
        secret_vars = {
            "ACTIONS_CACHE_URL": "https://cache.invalid/",
            "ACTIONS_RESULTS_URL": "https://results.invalid/",
            "ACTIONS_RUNTIME_TOKEN": "secret-runtime-token",
            "ACTIONS_ID_TOKEN_REQUEST_URL": "https://oidc.invalid/",
            "ACTIONS_ID_TOKEN_REQUEST_TOKEN": "secret-oidc-token",
            "GITHUB_TOKEN": "secret-gh-token",
            "GITHUB_ENV": "/tmp/fake-github-env",
            "GITHUB_PATH": "/tmp/fake-github-path",
            "GITHUB_OUTPUT": "/tmp/fake-github-output",
            "GITHUB_STEP_SUMMARY": "/tmp/fake-github-summary",
            "RUNNER_TEMP": "/tmp/fake-runner-temp",
            "GH_TOKEN": "secret-gh-cli-token",
        }
        saved = {k: os.environ.get(k) for k in secret_vars}
        os.environ.update(secret_vars)
        try:
            with tempfile.TemporaryDirectory(prefix="miri-env-prof-") as tmp:
                tmp_path = Path(tmp)
                sysroot = tmp_path / "sysroot"
                (sysroot / "lib").mkdir(parents=True)
                cap_bin = tmp_path / "cap"
                eval_bin = tmp_path / "eval"
                arg_log = tmp_path / "eval_args.jsonl"

                _write_executable(
                    cap_bin,
                    f"""#!{sys.executable}
import json, os, pathlib, sys
leaked = [k for k in {sorted(secret_vars)!r} if k in os.environ]
if leaked:
    sys.stderr.write(f"capture env leaked: {{leaked}}\\n")
    sys.exit(99)
ld_parts = os.environ.get("LD_LIBRARY_PATH", "").split(os.pathsep)
if not ld_parts or ld_parts[0] != {str(sysroot / "lib")!r}:
    sys.stderr.write(f"missing confined sysroot LD_LIBRARY_PATH: {{ld_parts!r}}\\n")
    sys.exit(96)
args = sys.argv[1:]
out = pathlib.Path(args[args.index("--out-dir") + 1])
out.mkdir(parents=True, exist_ok=True)
(out / "capture.json").write_text(json.dumps({{"ok": True}}))
print(json.dumps({{"status": "captured"}}))
""",
                )
                _write_executable(
                    eval_bin,
                    f"""#!{sys.executable}
import json, os, sys
leaked = [k for k in {sorted(secret_vars)!r} if k in os.environ]
if leaked:
    sys.stderr.write(f"eval env leaked: {{leaked}}\\n")
    sys.exit(99)
try:
    open(f"/proc/{{{os.getpid()}}}/environ", "rb").read()
    sys.stderr.write("parent /proc/$PPID/environ leaked\\n")
    sys.exit(98)
except PermissionError:
    pass
try:
    open({str(arg_log)!r}, "a", encoding="utf-8")
    sys.stderr.write("eval disk write was not blocked\\n")
    sys.exit(97)
except PermissionError:
    pass
print(json.dumps({{"outcome": {{"kind": "fault", "value": {{"kind": "undefined", "reason": json.dumps(sys.argv[1:])}}}}}}))
sys.exit(2)
""",
                )
                src = tmp_path / "a.rs"
                src.write_text("fn main() {}\n", encoding="utf-8")
                mir = tmp_path / "m.json"
                mir.write_text(json.dumps({"ok": True}), encoding="utf-8")

                invocations: list[list[str]] = []
                trampoline_ld_checks: list[tuple[str, Path | None]] = []
                orig_run_bounded = oracle.run_bounded

                def _spy_run_bounded(*rb_args, **rb_kwargs):
                    if rb_kwargs.get("confinement") == "capture":
                        trampoline_ld_checks.append(
                            (
                                rb_kwargs["env"].get("LD_LIBRARY_PATH", ""),
                                rb_kwargs.get("prepend_ld_library_path"),
                            )
                        )
                    return orig_run_bounded(*rb_args, **rb_kwargs)

                from unittest import mock

                with mock.patch.object(
                    oracle, "run_bounded", side_effect=_spy_run_bounded
                ):
                    for mode, expected_flag in (
                        ("auto", None),
                        ("v1", "--strict-v1"),
                        ("v2", "--profile-v2"),
                    ):
                        r_rust = oracle.evaluate_rust_unit(
                            src,
                            "fail/a.rs",
                            revision=None,
                            flags=[],
                            capture_bin=cap_bin,
                            eval_bin=eval_bin,
                            sysroot=sysroot,
                            target="x86_64-unknown-linux-gnu",
                            fuel=1000,
                            profile=mode,
                            timeout_secs=10,
                            max_memory_mb=oracle.DEFAULT_MAX_MEMORY_MB,
                            expect_valid=False,
                        )
                        self.assertEqual(r_rust["bucket"], "caught_ub", r_rust)
                        invocations.append(json.loads(str(r_rust["detail"])))
                        r_mir = oracle.evaluate_mir_json_unit(
                            mir,
                            "mir/m.json",
                            eval_bin=eval_bin,
                            fuel=1000,
                            profile=mode,
                            timeout_secs=10,
                            max_memory_mb=oracle.DEFAULT_MAX_MEMORY_MB,
                            expect_valid=False,
                        )
                        self.assertEqual(r_mir["bucket"], "caught_ub", r_mir)
                        invocations.append(json.loads(str(r_mir["detail"])))
                self.assertEqual(len(trampoline_ld_checks), 3)
                for tramp_ld, deferred_ld in trampoline_ld_checks:
                    self.assertNotIn(str(sysroot / "lib"), tramp_ld)
                    self.assertEqual(deferred_ld, sysroot / "lib")

                self.assertEqual(len(invocations), 6)
                # auto: neither override flag
                for argv in invocations[0:2]:
                    self.assertNotIn("--strict-v1", argv)
                    self.assertNotIn("--profile-v2", argv)
                # v1: --strict-v1 only
                for argv in invocations[2:4]:
                    self.assertIn("--strict-v1", argv)
                    self.assertNotIn("--profile-v2", argv)
                # v2: --profile-v2 only
                for argv in invocations[4:6]:
                    self.assertIn("--profile-v2", argv)
                    self.assertNotIn("--strict-v1", argv)
        finally:
            for k, prev in saved.items():
                if prev is None:
                    os.environ.pop(k, None)
                else:
                    os.environ[k] = prev

    def test_miri_headers_scope_target_directives_by_revision_and_extend_revisions(self):
        src = (
            "//@revisions: linux_rev\n"
            "//@revisions: win_rev alt_rev\n"
            "//@[linux_rev]only-target: linux\n"
            "//@[win_rev]only-target: windows\n"
            "//@[alt_rev]ignore-target: linux\n"
            "fn main() {}\n"
        )
        hdr = oracle.parse_miri_headers(src)
        self.assertEqual(hdr["revisions"], ["linux_rev", "win_rev", "alt_rev"])
        self.assertIsNone(
            oracle.harness_skip_reason(hdr, "x86_64-unknown-linux-gnu", "linux_rev")
        )
        self.assertIn(
            "only-target windows",
            oracle.harness_skip_reason(hdr, "x86_64-unknown-linux-gnu", "win_rev") or "",
        )
        self.assertIn(
            "ignore-target linux",
            oracle.harness_skip_reason(hdr, "x86_64-unknown-linux-gnu", "alt_rev") or "",
        )

    def test_tier_b_and_cli_reject_symlinks_before_resolve(self):
        with tempfile.TemporaryDirectory(prefix="miri-symlink-test-") as tmp:
            tmp_path = Path(tmp)
            corpus = tmp_path / "corpus"
            corpus.mkdir()
            (corpus / "ub.rs").write_text("fn main() {}\n", encoding="utf-8")
            (corpus / "ok.rs").write_text("fn main() {}\n", encoding="utf-8")
            manifest_data = {
                "schema_version": 1,
                "fixtures": [
                    {
                        "id": "ub1",
                        "path": "ub.rs",
                        "kind": "rust_ub_caught",
                        "category": "arith",
                        "expected_fault_substring": "ub",
                    },
                    {
                        "id": "ok1",
                        "path": "ok.rs",
                        "kind": "rust_valid_control",
                        "category": "valid",
                    },
                ],
            }
            (corpus / "manifest.json").write_text(
                json.dumps(manifest_data), encoding="utf-8"
            )

            # 1. Symlinked fixture file listed in manifest must be rejected
            #    (would pass if .resolve() ran before is_symlink()).
            real_target = corpus / "ok.rs"
            (corpus / "link_ok.rs").symlink_to(real_target)
            bad_manifest = dict(manifest_data)
            bad_manifest["fixtures"] = [
                manifest_data["fixtures"][0],
                {
                    "id": "ok_link",
                    "path": "link_ok.rs",
                    "kind": "rust_valid_control",
                    "category": "valid",
                },
            ]
            (corpus / "manifest.json").write_text(
                json.dumps(bad_manifest), encoding="utf-8"
            )
            with self.assertRaisesRegex(oracle.OracleError, "symlink"):
                oracle.load_tier_b_manifest(corpus)
            (corpus / "link_ok.rs").unlink()
            (corpus / "manifest.json").write_text(
                json.dumps(manifest_data), encoding="utf-8"
            )

            # 2. Symlinked subdirectory inside tier_b_dir must be rejected by
            #    the orphan/symlink walk.
            other_dir = tmp_path / "other"
            other_dir.mkdir()
            (corpus / "alias_dir").symlink_to(other_dir)
            with self.assertRaisesRegex(oracle.OracleError, "symlink"):
                oracle.load_tier_b_manifest(corpus)
            (corpus / "alias_dir").unlink()

            # 3. Symlinked tier_b_dir itself must be rejected.
            corpus_link = tmp_path / "corpus_link"
            corpus_link.symlink_to(corpus)
            with self.assertRaisesRegex(oracle.OracleError, "symlink"):
                oracle.load_tier_b_manifest(corpus_link)

            # 3b. Unnormalized '.' or empty segments must be rejected so
            #     'ub.rs' and './ub.rs' cannot bypass duplicate-path checks.
            dot_manifest = dict(manifest_data)
            dot_manifest["fixtures"] = [
                manifest_data["fixtures"][0],
                {
                    "id": "ub_dup",
                    "path": "./ub.rs",
                    "kind": "rust_ub_caught",
                    "category": "arith",
                    "expected_fault_substring": "ub",
                },
                manifest_data["fixtures"][1],
            ]
            (corpus / "manifest.json").write_text(
                json.dumps(dot_manifest), encoding="utf-8"
            )
            with self.assertRaisesRegex(oracle.OracleError, "invalid Tier B fixture path"):
                oracle.load_tier_b_manifest(corpus)
            (corpus / "manifest.json").write_text(
                json.dumps(manifest_data), encoding="utf-8"
            )

            # 3c. ignore-bitwidth respects target pointer width (32 vs 64).
            hdr32 = oracle.parse_miri_headers("//@ignore-bitwidth: 32\n")
            self.assertIsNone(oracle.harness_skip_reason(hdr32, "x86_64-unknown-linux-gnu"))
            self.assertEqual(
                oracle.harness_skip_reason(hdr32, "i686-unknown-linux-gnu"),
                "ignore-bitwidth 32",
            )

            # 4. CLI --archive pointing to a symlink must fail closed (exit 2)
            #    with a non-symlink diagnostic (using a pin with the real
            #    manifest digest so removing the symlink guard would not fail
            #    on manifest mismatch instead).
            import contextlib
            import io

            top = "miri-" + "a" * 40
            archive = tmp_path / "real.tar.gz"
            archive_sha = _make_tar_gz(
                archive,
                [(f"{top}/tests/fail/a.rs", "fn main() {}\n", tarfile.REGTYPE)],
            )
            extracted = tmp_path / "extracted"
            oracle.safe_extract_miri_corpus(
                archive,
                extracted,
                expected_top_dir=top,
                extract_subdirs=["tests/fail"],
            )
            real_manifest_sha, _ = oracle.compute_corpus_manifest_sha256(
                extracted, ["tests/fail"]
            )
            archive_link = tmp_path / "link.tar.gz"
            archive_link.symlink_to(archive)
            pin_path = tmp_path / "pin.json"
            pin_data = _sample_pin(
                archive_sha=archive_sha,
                manifest_sha=real_manifest_sha,
                expected_file_count=1,
                min_caught_ub=1,
            )
            pin_data["extract_subdirs"] = ["tests/fail"]
            pin_path.write_text(json.dumps(pin_data), encoding="utf-8")
            sysroot = tmp_path / "sysroot"
            (sysroot / "lib").mkdir(parents=True)
            cap_bin = tmp_path / "cap"
            eval_bin = tmp_path / "eval"
            _write_executable(
                cap_bin,
                f"#!{sys.executable}\n"
                "import json, pathlib, sys\n"
                "out = pathlib.Path(sys.argv[sys.argv.index('--out-dir') + 1])\n"
                "out.mkdir(parents=True, exist_ok=True)\n"
                "(out / 'capture.json').write_text(json.dumps({'compiler': {'commit': 'f' * 40}}), encoding='utf-8')\n"
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
            stderr_buf = io.StringIO()
            with contextlib.redirect_stderr(stderr_buf):
                rc = oracle.main([
                    "--tier-a",
                    "--pin", str(pin_path),
                    "--archive", str(archive_link),
                    "--no-network",
                    "--capture-bin", str(cap_bin),
                    "--eval-bin", str(eval_bin),
                    "--sysroot", str(sysroot),
                ])
            self.assertEqual(rc, 2)
            self.assertIn("non-symlink", stderr_buf.getvalue())

            # 5. CLI --corpus-dir positive path + manifest-digest mismatch +
            #    file-count mismatch + symlink rejection (root and subdir).
            rc_ok = oracle.main([
                "--tier-a",
                "--pin", str(pin_path),
                "--corpus-dir", str(extracted),
                "--no-network",
                "--capture-bin", str(cap_bin),
                "--eval-bin", str(eval_bin),
                "--sysroot", str(sysroot),
            ])
            self.assertEqual(rc_ok, 0)

            bad_sha_pin = tmp_path / "pin_bad_manifest.json"
            bad_pin_data = dict(pin_data)
            bad_pin_data["corpus_manifest_sha256"] = (
                ("0" if real_manifest_sha[0] != "0" else "1")
                + real_manifest_sha[1:]
            )
            bad_sha_pin.write_text(json.dumps(bad_pin_data), encoding="utf-8")
            stderr_sha = io.StringIO()
            with contextlib.redirect_stderr(stderr_sha):
                rc_sha = oracle.main([
                    "--tier-a",
                    "--pin", str(bad_sha_pin),
                    "--corpus-dir", str(extracted),
                    "--no-network",
                    "--capture-bin", str(cap_bin),
                    "--eval-bin", str(eval_bin),
                    "--sysroot", str(sysroot),
                ])
            self.assertEqual(rc_sha, 2)
            self.assertIn("manifest SHA-256 mismatch", stderr_sha.getvalue())

            bad_cnt_pin = tmp_path / "pin_bad_count.json"
            bad_cnt_data = dict(pin_data)
            bad_cnt_data["expected_file_count"] = 2
            bad_cnt_pin.write_text(json.dumps(bad_cnt_data), encoding="utf-8")
            stderr_cnt = io.StringIO()
            with contextlib.redirect_stderr(stderr_cnt):
                rc_cnt = oracle.main([
                    "--tier-a",
                    "--pin", str(bad_cnt_pin),
                    "--corpus-dir", str(extracted),
                    "--no-network",
                    "--capture-bin", str(cap_bin),
                    "--eval-bin", str(eval_bin),
                    "--sysroot", str(sysroot),
                ])
            self.assertEqual(rc_cnt, 2)
            self.assertIn("file count mismatch", stderr_cnt.getvalue())

            extracted_link = tmp_path / "extracted_link"
            extracted_link.symlink_to(extracted)
            stderr_clink = io.StringIO()
            with contextlib.redirect_stderr(stderr_clink):
                rc_clink = oracle.main([
                    "--tier-a",
                    "--pin", str(pin_path),
                    "--corpus-dir", str(extracted_link),
                    "--no-network",
                    "--capture-bin", str(cap_bin),
                    "--eval-bin", str(eval_bin),
                    "--sysroot", str(sysroot),
                ])
            self.assertEqual(rc_clink, 2)
            self.assertIn("symlink", stderr_clink.getvalue())

            (extracted / "fail" / "sym_sub").symlink_to(other_dir)
            stderr_sub = io.StringIO()
            with contextlib.redirect_stderr(stderr_sub):
                rc_sub = oracle.main([
                    "--tier-a",
                    "--pin", str(pin_path),
                    "--corpus-dir", str(extracted),
                    "--no-network",
                    "--capture-bin", str(cap_bin),
                    "--eval-bin", str(eval_bin),
                    "--sysroot", str(sysroot),
                ])
            self.assertEqual(rc_sub, 2)
            self.assertIn("symlink", stderr_sub.getvalue())
            (extracted / "fail" / "sym_sub").unlink()

    def test_capture_grandchild_pdeathsig_pool_cancel_and_tmp_sanitization(self):
        import signal as _sig
        import threading
        import time as _time
        from unittest import mock

        def _pid_alive(pid: int) -> bool:
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                return False
            except PermissionError:
                return True
            stat_path = Path(f"/proc/{pid}/stat")
            if stat_path.exists():
                try:
                    stat_txt = stat_path.read_text(encoding="utf-8", errors="ignore")
                    rp = stat_txt.rfind(")")
                    if rp != -1 and stat_txt[rp + 2 : rp + 3] == "Z":
                        return False
                except OSError:
                    return False
            return True

        def _child_pids(pid: int) -> list[int]:
            out: list[int] = []
            task_dir = Path(f"/proc/{pid}/task")
            if not task_dir.is_dir():
                return out
            try:
                for tid_dir in task_dir.iterdir():
                    try:
                        txt = (tid_dir / "children").read_text(encoding="ascii")
                    except OSError:
                        continue
                    for tok in txt.split():
                        if tok.isdigit():
                            out.append(int(tok))
            except OSError:
                return out
            return out

        # 1a. In capture confinement mode, a forked grandchild inside the
        #     isolated PID namespace must die promptly when the parent harness
        #     dies via SIGKILL, AND must die atomically before the supervisor
        #     exits when the capture child exits normally.
        with tempfile.TemporaryDirectory(prefix="anneal-miri-pdeath-") as tmp:
            tmp_path = Path(tmp)
            capture_inner = (
                "import os, time\n"
                "pid = os.fork()\n"
                "if pid == 0:\n"
                "    time.sleep(30)\n"
                "    os._exit(0)\n"
                "time.sleep(30)\n"
            )
            launcher = (
                "import os, subprocess, sys, time\n"
                f"sys.path.insert(0, {str(CI_DIR)!r})\n"
                "import run_miri_ub_oracle as oracle\n"
                f"cmd = oracle._wrap_with_confinement(\n"
                f"    [sys.executable, '-I', '-B', '-c', {capture_inner!r}],\n"
                "    timeout_secs=30, max_memory_mb=256, confinement='capture',\n"
                "    parent_pid=os.getpid(),\n"
                ")\n"
                "p = subprocess.Popen(cmd, env=oracle.sanitized_child_env(), start_new_session=True)\n"
                "print(p.pid, flush=True)\n"
                "time.sleep(30)\n"
            )
            mid = subprocess.Popen(
                [sys.executable, "-I", "-B", "-c", launcher],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            grand_pid: int | None = None
            child_host_pid: int | None = None
            sup_pid: int | None = None
            try:
                assert mid.stdout is not None
                sup_pid = int(mid.stdout.readline().strip())
                deadline_g = _time.monotonic() + 5.0
                while _time.monotonic() < deadline_g:
                    sup_kids = _child_pids(sup_pid)
                    if sup_kids:
                        child_host_pid = sup_kids[0]
                        grand_kids = _child_pids(child_host_pid)
                        if grand_kids:
                            grand_pid = grand_kids[0]
                            break
                    _time.sleep(0.05)
                self.assertIsNotNone(
                    grand_pid,
                    f"capture grandchild failed to spawn under sup={sup_pid} child={child_host_pid}",
                )
                assert grand_pid is not None and child_host_pid is not None
                os.kill(mid.pid, _sig.SIGKILL)
                mid.wait(timeout=5)
                deadline_dead = _time.monotonic() + 5.0
                while (
                    _pid_alive(grand_pid)
                    or _pid_alive(child_host_pid)
                    or _pid_alive(sup_pid)
                ) and _time.monotonic() < deadline_dead:
                    _time.sleep(0.05)
                self.assertFalse(
                    _pid_alive(grand_pid),
                    f"capture grandchild {grand_pid} survived parent SIGKILL",
                )
                self.assertFalse(
                    _pid_alive(child_host_pid),
                    f"capture child {child_host_pid} survived parent SIGKILL",
                )
                self.assertFalse(
                    _pid_alive(sup_pid),
                    f"capture supervisor {sup_pid} survived parent SIGKILL",
                )
            finally:
                if mid.poll() is None:
                    mid.kill()
                    mid.wait(timeout=5)
                for pid in (grand_pid, child_host_pid, sup_pid):
                    if pid is not None and _pid_alive(pid):
                        try:
                            os.kill(pid, _sig.SIGKILL)
                        except OSError:
                            pass
                if mid.stdout is not None:
                    mid.stdout.close()
                if mid.stderr is not None:
                    mid.stderr.close()

            # 1b. Normal child exit with a long-lived forked descendant must
            #     tear down the descendant before the supervisor exits (PID 1
            #     exit inside CLONE_NEWPID atomically kills all descendants).
            exit_early_inner = (
                "import os, time\n"
                "pid = os.fork()\n"
                "if pid == 0:\n"
                "    time.sleep(30)\n"
                "    os._exit(0)\n"
                "time.sleep(0.4)\n"
                "os._exit(0)\n"
            )
            early_cmd = oracle._wrap_with_confinement(
                [sys.executable, "-I", "-B", "-c", exit_early_inner],
                timeout_secs=30,
                max_memory_mb=256,
                confinement="capture",
                parent_pid=os.getpid(),
            )
            sup_early = subprocess.Popen(
                early_cmd,
                env=oracle.sanitized_child_env(),
                start_new_session=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            early_grand: int | None = None
            try:
                deadline_eg = _time.monotonic() + 3.0
                while sup_early.poll() is None and _time.monotonic() < deadline_eg:
                    kids = _child_pids(sup_early.pid)
                    if kids:
                        gkids = _child_pids(kids[0])
                        if gkids:
                            early_grand = gkids[0]
                            break
                    _time.sleep(0.02)
                self.assertIsNotNone(early_grand, "early-exit grandchild never spawned")
                rc_early = sup_early.wait(timeout=5)
                self.assertEqual(rc_early, 0)
                assert early_grand is not None
                self.assertFalse(
                    _pid_alive(early_grand),
                    f"capture grandchild {early_grand} survived normal child exit",
                )
            finally:
                if sup_early.poll() is None:
                    sup_early.kill()
                    sup_early.wait(timeout=5)
                if early_grand is not None and _pid_alive(early_grand):
                    try:
                        os.kill(early_grand, _sig.SIGKILL)
                    except OSError:
                        pass
                if sup_early.stdout is not None:
                    sup_early.stdout.close()
                if sup_early.stderr is not None:
                    sup_early.stderr.close()

            # 2. tool_error stderr containing tmp_path is sanitized to <tmp>.
            fake_cap = tmp_path / "fake_cap.py"
            fake_cap.write_text(
                "#!/usr/bin/env python3\n"
                "import sys\n"
                "out_idx = sys.argv.index('--out-dir') + 1\n"
                "sys.stderr.write('boom at ' + sys.argv[out_idx] + '/capture.json\\n')\n"
                "sys.exit(9)\n",
                encoding="utf-8",
            )
            fake_cap.chmod(0o755)
            fake_eval = tmp_path / "fake_eval.py"
            fake_eval.write_text(
                "#!/usr/bin/env python3\n"
                "import json, sys\n"
                "print(json.dumps({'outcome': {'kind': 'unexpected'}}))\n"
                "sys.stderr.write('eval fail at ' + sys.argv[2] + '\\n')\n"
                "sys.exit(7)\n",
                encoding="utf-8",
            )
            fake_eval.chmod(0o755)
            src_rs = tmp_path / "ub.rs"
            src_rs.write_text("fn main() {}\n", encoding="utf-8")
            rec_rs = oracle.evaluate_rust_unit(
                src_rs,
                "ub.rs",
                revision=None,
                flags=[],
                capture_bin=fake_cap,
                eval_bin=fake_eval,
                sysroot=tmp_path,
                target="x86_64-unknown-linux-gnu",
                fuel=10,
                profile="v1",
                timeout_secs=10,
                max_memory_mb=256,
                expect_valid=False,
            )
            self.assertEqual(rec_rs["bucket"], "tool_error")
            self.assertIn("<tmp>", str(rec_rs.get("detail", "")))
            self.assertNotIn("anneal-miri-unit-", str(rec_rs.get("detail", "")))

            mir_dir = tmp_path / "anneal-miri-tier-b-sample"
            mir_dir.mkdir()
            mir_json = mir_dir / "ub.json"
            mir_json.write_text("{}\n", encoding="utf-8")
            rec_mir = oracle.evaluate_mir_json_unit(
                mir_json,
                "mir/ub.json",
                eval_bin=fake_eval,
                fuel=10,
                profile="v1",
                timeout_secs=10,
                max_memory_mb=256,
                expect_valid=False,
            )
            self.assertEqual(rec_mir["bucket"], "tool_error")
            self.assertIn("<tmp>", str(rec_mir.get("detail", "")))
            self.assertNotIn(str(mir_dir), str(rec_mir.get("detail", "")))

            # 3. KeyboardInterrupt in run_tier_b must cancel pending futures
            #    and kill active children promptly rather than draining all.
            tier_b_dir = tmp_path / "tier_b"
            (tier_b_dir / "mir").mkdir(parents=True)
            entries = []
            for idx in range(4):
                rel = f"mir/f{idx}.json"
                (tier_b_dir / rel).write_text("{}\n", encoding="utf-8")
                if idx < 3:
                    entries.append({
                        "id": f"f{idx}",
                        "path": rel,
                        "kind": "mir_ub_caught",
                        "category": "test",
                        "expected_fault_substring": "stub",
                    })
                else:
                    entries.append({
                        "id": f"f{idx}",
                        "path": rel,
                        "kind": "mir_valid_control",
                        "category": "valid_control",
                    })
            (tier_b_dir / "manifest.json").write_text(
                json.dumps({"schema_version": 1, "fixtures": entries}),
                encoding="utf-8",
            )
            started_ev = threading.Event()
            slow_eval = tmp_path / "slow_eval.py"
            slow_eval.write_text(
                "#!/usr/bin/env python3\n"
                "import time\n"
                "time.sleep(30)\n",
                encoding="utf-8",
            )
            slow_eval.chmod(0o755)
            orig_eval_mir = oracle.evaluate_mir_json_unit
            call_count = 0

            def _wrapped_eval_mir(*args, **kwargs):
                nonlocal call_count
                call_count += 1
                started_ev.set()
                return orig_eval_mir(*args, **kwargs)

            def _send_sigint():
                started_ev.wait(timeout=5.0)
                _time.sleep(0.25)
                os.kill(os.getpid(), _sig.SIGINT)

            t0 = _time.monotonic()
            interrupter = threading.Thread(target=_send_sigint, daemon=True)
            interrupter.start()
            with mock.patch.object(
                oracle, "evaluate_mir_json_unit", side_effect=_wrapped_eval_mir
            ):
                with self.assertRaises(KeyboardInterrupt):
                    oracle.run_tier_b(
                        tier_b_dir=tier_b_dir,
                        capture_bin=fake_cap,
                        eval_bin=slow_eval,
                        sysroot=tmp_path,
                        target="x86_64-unknown-linux-gnu",
                        profile="v1",
                        workers=1,
                        timeout_secs=30,
                        max_memory_mb=256,
                        fuel=10,
                        pin=None,
                    )
            elapsed_int = _time.monotonic() - t0
            interrupter.join(timeout=2.0)
            self.assertLess(elapsed_int, 5.0)
            self.assertEqual(call_count, 1)

            # 4. Atomic cancellation race: if cancellation triggers between
            #    Popen() and killer registration, run_bounded must kill the
            #    newly spawned child PGID immediately and raise
            #    KeyboardInterrupt without waiting for timeout_secs.
            race_token = oracle._CancelToken()
            orig_popen = oracle.subprocess.Popen
            spawned_pids: list[int] = []

            def _racy_popen(*p_args, **p_kwargs):
                proc = orig_popen(*p_args, **p_kwargs)
                spawned_pids.append(proc.pid)
                race_token.cancel_and_kill_all()
                return proc

            t_race = _time.monotonic()
            with mock.patch.object(
                oracle.subprocess, "Popen", side_effect=_racy_popen
            ):
                with self.assertRaises(KeyboardInterrupt):
                    oracle.run_bounded(
                        [sys.executable, "-I", "-B", "-c", "import time; time.sleep(30)"],
                        env=oracle.sanitized_child_env(),
                        timeout_secs=30,
                        max_memory_mb=256,
                        cancel_token=race_token,
                    )
            self.assertLess(_time.monotonic() - t_race, 5.0)
            self.assertEqual(len(spawned_pids), 1)
            self.assertFalse(_pid_alive(spawned_pids[0]))

            # Already-cancelled token must abort before calling Popen.
            with mock.patch.object(
                oracle.subprocess,
                "Popen",
                side_effect=AssertionError("Popen must not be called"),
            ):
                with self.assertRaises(KeyboardInterrupt):
                    oracle.run_bounded(
                        [sys.executable, "-I", "-B", "-c", "pass"],
                        env=oracle.sanitized_child_env(),
                        timeout_secs=10,
                        max_memory_mb=256,
                        cancel_token=race_token,
                    )

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
                oracle, "_stream_regular_file_sha256", side_effect=_spy_stream
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
                    oracle,
                    "load_pin",
                    side_effect=AssertionError("load_pin called as UID 0"),
                ),
                mock.patch.object(
                    oracle,
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
            unittest.mock.patch.object(oracle, "_require_confinement_support"),
            unittest.mock.patch.object(
                oracle, "evaluate_rust_unit", side_effect=fake_eval_rust
            ),
            unittest.mock.patch.object(
                oracle, "evaluate_mir_json_unit", side_effect=fake_eval_mir
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


if __name__ == "__main__":
    unittest.main()
