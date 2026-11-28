# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`alpha_release.py` tests for release resolution, prior-release
coordination, and post-crate recovery."""

from __future__ import annotations

from .support import (
    CRATES_API_URL,
    DEV_VERSION,
    hashlib,
    inspect_crate_archive,
    json,
    LOCK_REL,
    _make_crate_bytes,
    MANIFEST_REL,
    Path,
    RepoFixture,
    resolve_and_validate,
    STATIC_CRATES_PREFIX,
    subprocess,
    tempfile,
    UNPINNED,
)


class ResolveAndRecoveryCases:
    """`AlphaReleaseTests` methods for release resolution, prior-release
    coordination, and post-crate recovery."""

    def test_resolve_fresh_monotonicity_first_parent_and_shallow_guards(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-resolve-") as tmp:
            fx = RepoFixture(Path(tmp))
            c1 = fx.initial_commit
            fx.tag_annotated("anneal-v0.2.0-alpha.5", c1)
            c2 = fx.commit_all("add scalar feature", touch_file="anneal/a.txt")
            # Merge a side branch via `--no-ff` so `side_sha` is an ancestor of
            # `origin/main` but NOT on `origin/main`'s first-parent history.
            fx.git("checkout", "-q", "-b", "feature", c1)
            side_sha = fx.commit_all("side commit", touch_file="anneal/side.txt")
            fx.git("checkout", "-q", "main")
            fx.git("merge", "--quiet", "--no-ff", "feature", "-m", "merge feature")
            c3 = fx.git("rev-parse", "HEAD")
            fx.push_main()

            def crates_api_with(versions: list[dict]) -> tuple[int, bytes]:
                return 200, json.dumps({"versions": versions}).encode("utf-8")

            # A colliding branch name (`refs/heads/anneal-v0.2.0-alpha.5`) must
            # not break `refs/tags/anneal-v*` enumeration (`refname:lstrip=2`).
            fx.git("branch", "anneal-v0.2.0-alpha.5", c1)

            # Historical untagged crates (`0.2.0-alpha.1` below
            # `anneal-v0.2.0-alpha.5`) do not block fresh releases.
            http_map = {
                CRATES_API_URL: crates_api_with(
                    [
                        {"num": "0.2.0-alpha.5", "yanked": False},
                        {"num": "0.2.0-alpha.1", "yanked": False},
                    ]
                )
            }
            res = resolve_and_validate(
                fx.repo,
                version="0.2.0-alpha.7",
                default_sha=c3,
                http_get=lambda url: http_map[url],
            )
            self.assertFalse(res.already_published)
            self.assertEqual(res.commit, c3)

            # Explicit first-parent historical commit `c2` is also valid.
            res_c2 = resolve_and_validate(
                fx.repo,
                version="0.2.0-alpha.7",
                commit=c2,
                default_sha=c3,
                http_get=lambda url: http_map[url],
            )
            self.assertEqual(res_c2.commit, c2)

            # Side-branch commit `side_sha` is rejected.
            with self.assertRaisesRegex(ValueError, "first-parent"):
                resolve_and_validate(
                    fx.repo,
                    version="0.2.0-alpha.7",
                    commit=side_sha,
                    default_sha=c3,
                    http_get=lambda url: http_map[url],
                )

            # Re-releasing at an already tagged commit `c1` is rejected.
            with self.assertRaisesRegex(ValueError, "already tagged"):
                resolve_and_validate(
                    fx.repo,
                    version="0.2.0-alpha.7",
                    commit=c1,
                    default_sha=c3,
                    http_get=lambda url: http_map[url],
                )

            # Older version (`0.2.0-alpha.4` < `0.2.0-alpha.5`) is rejected by
            # SemVer monotonicity; non-`0.2.0-alpha.<N>` pre-releases (including
            # `+build` suffixes) fail the version gate.
            with self.assertRaisesRegex(ValueError, "strictly exceed"):
                resolve_and_validate(
                    fx.repo,
                    version="0.2.0-alpha.4",
                    default_sha=c3,
                    http_get=lambda url: http_map[url],
                )
            for bad_ver in ("0.2.0-alpha.5+b1", "1.0.0-rc.1"):
                with self.subTest(bad_ver=bad_ver), self.assertRaisesRegex(
                    ValueError, r"0\.2\.0-alpha\.<N>"
                ):
                    resolve_and_validate(
                        fx.repo,
                        version=bad_ver,
                        default_sha=c3,
                        http_get=lambda url: http_map[url],
                    )
            for empty_kw in (
                {"expected_sha256": ""},
                {"expected_source_sha256": ""},
            ):
                with self.subTest(empty_kw=empty_kw), self.assertRaisesRegex(
                    ValueError, "invalid nonzero 64-hex"
                ):
                    resolve_and_validate(
                        fx.repo,
                        version="0.2.0-alpha.7",
                        default_sha=c3,
                        http_get=lambda url: http_map[url],
                        **empty_kw,
                    )

            # An already-existing `anneal-v<V>` Git tag without a crates.io
            # release fails closed immediately.
            fx.tag_annotated("anneal-v0.2.0-alpha.6", c2)
            with self.assertRaisesRegex(ValueError, "already exists"):
                resolve_and_validate(
                    fx.repo,
                    version="0.2.0-alpha.6",
                    default_sha=c3,
                    http_get=lambda url: http_map[url],
                )

            # Shallow clone fails closed via `ensure_not_shallow`.
            shallow_dir = Path(tmp) / "shallow"
            subprocess.run(
                [
                    "git",
                    "clone",
                    "--quiet",
                    "--depth=1",
                    f"file://{fx.origin}",
                    str(shallow_dir),
                ],
                check=True,
            )
            with self.assertRaisesRegex(ValueError, "shallow"):
                resolve_and_validate(
                    shallow_dir,
                    version="0.2.0-alpha.7",
                    default_sha=c3,
                    http_get=lambda url: http_map[url],
                )

    def test_untagged_prior_release_coordination_polling_and_yanked_exemption(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-poll-") as tmp:
            fx = RepoFixture(Path(tmp))
            c1 = fx.initial_commit
            c2 = fx.commit_all("second commit", touch_file="anneal/b.txt")
            fx.push_main()

            # Initial repository (`max_git_tag_semver is None`): un-yanked
            # `0.2.0-alpha.1` on crates.io without its Git tag blocks
            # immediately when `wait_for_prior_tags_seconds=0`.
            untagged_v1 = {
                CRATES_API_URL: (
                    200,
                    json.dumps(
                        {"versions": [{"num": "0.2.0-alpha.1", "yanked": False}]}
                    ).encode("utf-8"),
                )
            }
            with self.assertRaisesRegex(ValueError, "lack corresponding anneal-v"):
                resolve_and_validate(
                    fx.repo,
                    version="0.2.0-alpha.2",
                    commit=c2,
                    default_sha=c2,
                    wait_for_prior_tags_seconds=0,
                    http_get=lambda url: untagged_v1[url],
                )

            # Yanked `0.2.0-alpha.1` does NOT block `0.2.0-alpha.2`.
            yanked_v1 = {
                CRATES_API_URL: (
                    200,
                    json.dumps(
                        {"versions": [{"num": "0.2.0-alpha.1", "yanked": True}]}
                    ).encode("utf-8"),
                )
            }
            res_yanked = resolve_and_validate(
                fx.repo,
                version="0.2.0-alpha.2",
                commit=c2,
                default_sha=c2,
                http_get=lambda url: yanked_v1[url],
            )
            self.assertEqual(res_yanked.commit, c2)

            # Back-to-back sequential approval simulation: `0.2.0-alpha.1`'s
            # Job 5 pushes `anneal-v0.2.0-alpha.1` at `c1` on `origin` before
            # the poll deadline expires; `resolve_and_validate` fetches it,
            # verifies `c1 < c2`, and resolves `c2`.
            now = [0.0]
            sleeps: list[float] = []

            def fake_clock() -> float:
                return now[0]

            def fake_sleep(dt: float) -> None:
                sleeps.append(dt)
                now[0] += dt

            fx.tag_annotated("anneal-v0.2.0-alpha.1", c1, local=False)
            polled = resolve_and_validate(
                fx.repo,
                version="0.2.0-alpha.2",
                commit=c2,
                default_sha=c2,
                wait_for_prior_tags_seconds=15,
                http_get=lambda url: untagged_v1[url],
                clock=fake_clock,
                sleep_fn=fake_sleep,
            )
            self.assertEqual(polled.commit, c2)
            self.assertEqual(sleeps, [5.0])

    def test_post_crate_recovery_cross_authenticates_tag_and_rejects_mismatches(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-recover-") as tmp:
            fx = RepoFixture(Path(tmp))
            c1 = fx.initial_commit
            fx.tag_annotated("anneal-v0.2.0-alpha.5", c1)
            c_pub = fx.commit_all("release target", touch_file="anneal/rel.txt")
            c_head = fx.commit_all("later main commit", touch_file="anneal/later.txt")
            fx.push_main()

            version = "0.2.0-alpha.7"
            digest = "4" * 64
            crate_bytes = _make_crate_bytes(
                version=version, commit=c_pub, sha256=digest
            )
            checksum = hashlib.sha256(crate_bytes).hexdigest()
            expected_info = inspect_crate_archive(
                crate_bytes,
                version=version,
                expected_commit=c_pub,
                expected_sha256=digest,
            )

            crate_url = f"{STATIC_CRATES_PREFIX}/cargo-anneal-{version}.crate"
            http_map = {
                CRATES_API_URL: (
                    200,
                    json.dumps(
                        {
                            "versions": [
                                {"num": "0.2.0-alpha.5", "yanked": False},
                                {
                                    "num": version,
                                    "yanked": False,
                                    "checksum": checksum,
                                },
                            ]
                        }
                    ).encode("utf-8"),
                ),
                crate_url: (200, crate_bytes),
            }

            # Without the local `anneal-toolchain-<C12>-<D16>` Git tag,
            # recovery fails closed instead of trusting external metadata alone.
            with self.assertRaisesRegex(ValueError, "missing local Git tag"):
                resolve_and_validate(
                    fx.repo,
                    version=version,
                    commit="",
                    default_sha=c_head,
                    http_get=lambda url: http_map[url],
                )

            # Once the toolchain tag points to `c_pub`, blank-`commit` recovery
            # resolves `c_pub` even though `origin/main` advanced to `c_head`.
            fx.tag_annotated(expected_info.toolchain_tag, c_pub)
            recovered = resolve_and_validate(
                fx.repo,
                version=version,
                commit="",
                default_sha=c_head,
                http_get=lambda url: http_map[url],
            )
            self.assertTrue(recovered.already_published)
            self.assertEqual(recovered.commit, c_pub)
            self.assertEqual(recovered.archive_sha256, digest)
            self.assertEqual(
                recovered.toolchain_tag, expected_info.toolchain_tag
            )
            self.assertEqual(
                recovered.published_crate_source_sha256,
                expected_info.crate_source_sha256,
            )

            # Mismatched `--commit`, `--expected-sha256`, or
            # `--expected-source-sha256` fails closed (catching duplicate
            # cold-build races `D_A != D_B`).
            with self.assertRaisesRegex(ValueError, "does not match expected"):
                resolve_and_validate(
                    fx.repo,
                    version=version,
                    commit=c_head,
                    default_sha=c_head,
                    http_get=lambda url: http_map[url],
                )
            with self.assertRaisesRegex(ValueError, "sha256"):
                resolve_and_validate(
                    fx.repo,
                    version=version,
                    commit=c_pub,
                    default_sha=c_head,
                    expected_sha256="5" * 64,
                    http_get=lambda url: http_map[url],
                )
            with self.assertRaisesRegex(ValueError, "crate_source_sha256"):
                resolve_and_validate(
                    fx.repo,
                    version=version,
                    commit=c_pub,
                    default_sha=c_head,
                    expected_sha256=digest,
                    expected_source_sha256="6" * 64,
                    http_get=lambda url: http_map[url],
                )

    def test_resolve_rejects_missing_or_non_sentinel_target_commits(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-sentinel-") as tmp:
            fx = RepoFixture(Path(tmp))
            c_dev = fx.initial_commit
            http_map = {
                CRATES_API_URL: (
                    200,
                    json.dumps({"versions": []}).encode("utf-8"),
                )
            }

            orig_manifest = (fx.repo / MANIFEST_REL).read_text(encoding="utf-8")
            orig_lock = (fx.repo / LOCK_REL).read_text(encoding="utf-8")

            # Already-pinned/pre-cutover `Cargo.toml` fails closed before build.
            pinned_url = (
                "https://github.com/google/zerocopy/releases/download/"
                "anneal-toolchain-deadbeef/anneal-toolchain-linux-x86_64.tar.zst"
            )
            pinned_manifest = orig_manifest.replace(
                f'version = "{DEV_VERSION}"', 'version = "0.2.0-alpha.6"', 1
            ).replace(
                f'sha256 = "{UNPINNED}"', f'sha256 = "{"7" * 64}"', 1
            ).replace(
                'url = ""',
                f'url = "{pinned_url}"',
                1,
            )
            (fx.repo / MANIFEST_REL).write_text(pinned_manifest, encoding="utf-8")
            c_pinned = fx.commit_all("pinned manifest commit")

            # Restore `Cargo.toml` sentinel but leave `Cargo.lock` drifted.
            (fx.repo / MANIFEST_REL).write_text(orig_manifest, encoding="utf-8")
            (fx.repo / LOCK_REL).write_text(
                orig_lock.replace(
                    f'version = "{DEV_VERSION}"', 'version = "0.2.0-alpha.6"', 1
                ),
                encoding="utf-8",
            )
            c_bad_lock = fx.commit_all("drifted lockfile commit")

            # Missing `Cargo.toml` commit.
            (fx.repo / LOCK_REL).write_text(orig_lock, encoding="utf-8")
            (fx.repo / MANIFEST_REL).unlink()
            c_missing = fx.commit_all("missing manifest commit")

            # Symlinked `Cargo.lock` commit.
            (fx.repo / MANIFEST_REL).write_text(orig_manifest, encoding="utf-8")
            (fx.repo / LOCK_REL).unlink()
            (fx.repo / LOCK_REL).symlink_to("trusted/cargo-anneal/Cargo.toml")
            c_symlink = fx.commit_all("symlink lockfile commit")

            # Restore clean `0.0.0-dev` HEAD so `origin/main` tip itself is
            # valid.
            (fx.repo / LOCK_REL).unlink()
            (fx.repo / LOCK_REL).write_text(orig_lock, encoding="utf-8")
            c_clean_head = fx.commit_all("restored dev head")
            fx.push_main()

            res_ok = resolve_and_validate(
                fx.repo,
                version="0.2.0-alpha.7",
                commit=c_dev,
                default_sha=c_clean_head,
                http_get=lambda url: http_map[url],
            )
            self.assertEqual(res_ok.commit, c_dev)

            for bad_commit, pattern in (
                (c_pinned, "unpinned sentinel metadata"),
                (c_bad_lock, "does not hold version"),
                (c_missing, "does not contain regular file"),
                (c_symlink, "must be a regular file"),
            ):
                with self.subTest(bad_commit=bad_commit, pattern=pattern):
                    with self.assertRaisesRegex(ValueError, pattern):
                        resolve_and_validate(
                            fx.repo,
                            version="0.2.0-alpha.7",
                            commit=bad_commit,
                            default_sha=c_clean_head,
                            http_get=lambda url: http_map[url],
                        )
