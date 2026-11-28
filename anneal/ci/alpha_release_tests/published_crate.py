# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`alpha_release.py` tests for published-crate download verification."""

from __future__ import annotations

from .support import (
    build_parser,
    contextlib,
    CRATES_API_URL,
    hashlib,
    inspect_crate_archive,
    io,
    json,
    _make_crate_bytes,
    STATIC_CRATES_PREFIX,
    verify_published_crate,
)


class PublishedCrateCases:
    """`AlphaReleaseTests` methods for published-crate download verification."""

    def test_verify_published_crate_downloads_and_verifies_checksum_and_parity(
        self,
    ) -> None:
        version = "0.2.0-alpha.12"
        commit = "a" * 40
        digest = "2" * 64
        crate_bytes = _make_crate_bytes(
            version=version, commit=commit, sha256=digest
        )
        crate_sha256 = hashlib.sha256(crate_bytes).hexdigest()
        expected_source = inspect_crate_archive(
            crate_bytes,
            version=version,
            expected_commit=commit,
            expected_sha256=digest,
        ).crate_source_sha256
        crate_url = f"{STATIC_CRATES_PREFIX}/cargo-anneal-{version}.crate"

        # Invalid inputs must fail closed before contacting crates.io.
        def forbid_http(_url: str) -> tuple[int, bytes]:
            raise AssertionError("unexpected crates.io request")

        for label, kwargs, pattern in (
            (
                "bad_version",
                {
                    "version": "0.2.0",
                    "commit": commit,
                    "sha256": digest,
                    "expected_source_sha256": expected_source,
                },
                "stable Anneal version",
            ),
            (
                "bad_commit",
                {
                    "version": version,
                    "commit": "not-a-sha",
                    "sha256": digest,
                    "expected_source_sha256": expected_source,
                },
                "invalid 40-hex commit",
            ),
            (
                "zero_sha256",
                {
                    "version": version,
                    "commit": commit,
                    "sha256": "0" * 64,
                    "expected_source_sha256": expected_source,
                },
                "invalid nonzero 64-hex sha256",
            ),
            (
                "zero_source_sha256",
                {
                    "version": version,
                    "commit": commit,
                    "sha256": digest,
                    "expected_source_sha256": "0" * 64,
                },
                "invalid nonzero 64-hex expected_source_sha256",
            ),
            (
                "negative_wait",
                {
                    "version": version,
                    "commit": commit,
                    "sha256": digest,
                    "expected_source_sha256": expected_source,
                    "wait_seconds": -1,
                },
                "non-negative",
            ),
        ):
            with self.subTest(case=label):
                with self.assertRaisesRegex(ValueError, pattern):
                    verify_published_crate(**kwargs, http_get=forbid_http)

        # Bounded polling handles both API visibility lag and static.crates.io
        # 404 propagation lag, then downloads and verifies the published crate.
        api_ready = (
            200,
            json.dumps({
                "versions": [{
                    "num": version,
                    "yanked": False,
                    "checksum": crate_sha256,
                }]
            }).encode("utf-8"),
        )
        api_responses = iter([
            (404, b""),
            (200, json.dumps({"versions": []}).encode("utf-8")),
            api_ready,
            api_ready,
        ])
        dl_responses = iter([
            (404, b""),
            (200, crate_bytes),
        ])

        def sequenced_get(url: str) -> tuple[int, bytes]:
            if url == CRATES_API_URL:
                return next(api_responses)
            if url == crate_url:
                return next(dl_responses)
            raise AssertionError(f"unexpected URL: {url}")

        now = [0.0]

        def advance_clock() -> float:
            return now[0]

        def advance_sleep(dt: float) -> None:
            now[0] += dt

        verified = verify_published_crate(
            version=version,
            commit=commit,
            sha256=digest,
            expected_source_sha256=expected_source,
            wait_seconds=20,
            http_get=sequenced_get,
            clock=advance_clock,
            sleep_fn=advance_sleep,
        )
        self.assertEqual(verified, expected_source)

        # CLI parser accepts verify-published-crate without `--crate` and
        # rejects the removed `--crate` option.
        parsed = build_parser().parse_args([
            "verify-published-crate",
            "--version",
            version,
            "--commit",
            commit,
            "--sha256",
            digest,
            "--expected-source-sha256",
            expected_source,
        ])
        self.assertEqual(parsed.subcommand, "verify-published-crate")
        with (
            contextlib.redirect_stderr(io.StringIO()),
            self.assertRaises(SystemExit),
        ):
            build_parser().parse_args([
                "verify-published-crate",
                "--crate",
                "/tmp/nonexistent.crate",
                "--version",
                version,
                "--commit",
                commit,
                "--sha256",
                digest,
                "--expected-source-sha256",
                expected_source,
            ])

        def fixed_get(
            *,
            api_resp: tuple[int, bytes] = api_ready,
            dl_resp: tuple[int, bytes] = (200, crate_bytes),
        ):
            def _get(url: str) -> tuple[int, bytes]:
                if url == CRATES_API_URL:
                    return api_resp
                if url == crate_url:
                    return dl_resp
                raise AssertionError(f"unexpected URL: {url}")

            return _get

        # Mismatched downloaded checksum must fail closed immediately.
        with self.assertRaisesRegex(ValueError, "crates.io checksum"):
            verify_published_crate(
                version=version,
                commit=commit,
                sha256=digest,
                expected_source_sha256=expected_source,
                wait_seconds=20,
                http_get=fixed_get(
                    api_resp=(
                        200,
                        json.dumps({
                            "versions": [{
                                "num": version,
                                "yanked": False,
                                "checksum": "f" * 64,
                            }]
                        }).encode("utf-8"),
                    ),
                ),
            )

        # Source-parity mismatch on the downloaded crate must fail closed.
        with self.assertRaisesRegex(ValueError, "published crate_source_sha256"):
            verify_published_crate(
                version=version,
                commit=commit,
                sha256=digest,
                expected_source_sha256="9" * 64,
                wait_seconds=0,
                http_get=fixed_get(),
            )

        # Non-404 download error must fail closed immediately.
        with self.assertRaisesRegex(ValueError, "HTTP 500 downloading"):
            verify_published_crate(
                version=version,
                commit=commit,
                sha256=digest,
                expected_source_sha256=expected_source,
                wait_seconds=20,
                http_get=fixed_get(dl_resp=(500, b"")),
            )

        # Yanked release must fail closed immediately.
        with self.assertRaisesRegex(ValueError, "yanked"):
            verify_published_crate(
                version=version,
                commit=commit,
                sha256=digest,
                expected_source_sha256=expected_source,
                wait_seconds=0,
                http_get=fixed_get(
                    api_resp=(
                        200,
                        json.dumps({
                            "versions": [{
                                "num": version,
                                "yanked": True,
                                "checksum": crate_sha256,
                            }]
                        }).encode("utf-8"),
                    ),
                ),
            )

        # Permanently invisible API release must time out and fail closed.
        now[0] = 0.0
        with self.assertRaisesRegex(ValueError, "not visible on crates.io"):
            verify_published_crate(
                version=version,
                commit=commit,
                sha256=digest,
                expected_source_sha256=expected_source,
                wait_seconds=5,
                http_get=fixed_get(
                    api_resp=(
                        200,
                        json.dumps({"versions": []}).encode("utf-8"),
                    ),
                ),
                clock=advance_clock,
                sleep_fn=advance_sleep,
            )

        # Permanently 404 static.crates.io download must time out and fail.
        now[0] = 0.0
        with self.assertRaisesRegex(ValueError, "not downloadable within"):
            verify_published_crate(
                version=version,
                commit=commit,
                sha256=digest,
                expected_source_sha256=expected_source,
                wait_seconds=5,
                http_get=fixed_get(dl_resp=(404, b"")),
                clock=advance_clock,
                sleep_fn=advance_sleep,
            )
