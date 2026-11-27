# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Miri UB oracle tests for the real Tier B manifest and fixtures."""

from __future__ import annotations

from .support import (
    hashlib,
    io,
    json,
    _make_tar_gz,
    oracle,
    os,
    Path,
    tarfile,
    tempfile,
)


class CorpusManifestCases:
    """`RealTierBCorpusHygieneTests` methods for the real Tier B manifest and
    fixtures."""

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
