# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Miri UB oracle tests for the pin manifest, supply-chain checks, and safe tar
extraction."""

from __future__ import annotations

from .support import (
    ANNEAL_DIR,
    io,
    json,
    _make_tar_gz,
    oracle,
    os,
    Path,
    re,
    _sample_pin,
    tarfile,
    tempfile,
)


class PinAndSupplyChainCases:
    """`PinAndSupplyChainTests` methods for the pin manifest and supply-chain
    checks."""

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


class SafeTarExtractionCases:
    """`SafeTarExtractionTests` methods for safe tar extraction."""

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
