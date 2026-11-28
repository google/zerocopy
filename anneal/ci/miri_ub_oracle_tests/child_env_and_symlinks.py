# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Miri UB oracle tests for child environments, Miri headers, and symlink
refusal."""

from __future__ import annotations

from .support import (
    json,
    _make_tar_gz,
    oracle,
    oracle_evaluate,
    os,
    Path,
    _sample_pin,
    sys,
    tarfile,
    tempfile,
    _write_executable,
)


class ChildEnvAndSymlinkCases:
    """`RealTierBCorpusHygieneTests` methods for child environments, Miri
    headers, and symlink refusal."""

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
                    oracle_evaluate, "run_bounded", side_effect=_spy_run_bounded
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
