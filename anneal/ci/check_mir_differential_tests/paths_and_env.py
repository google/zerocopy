# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Path anchoring, child environment, and artifact manifest tests for
`check_mir_differential.py`."""

from __future__ import annotations

import json
import os
from pathlib import Path
import tempfile
from unittest import mock

import check_mir_differential as cmd
from check_mir_differential_tests.support import _sample_diff_report


class PathsAndEnvCases:
    def test_outside_cwd_anchors_relative_cli_and_env_paths_and_rejects_symlinks(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            repo_root = Path(tmpd).resolve()
            anneal_dir = repo_root / "anneal"
            (anneal_dir / "target" / "debug").mkdir(parents=True)
            (anneal_dir / "corpora").mkdir(parents=True)
            (repo_root / "tools" / "eval").mkdir(parents=True)

            diff_bin = anneal_dir / "target" / "debug" / "anneal-diff"
            diff_bin.write_text("", encoding="utf-8")
            capture_bin = anneal_dir / "target" / "debug" / "anneal-rustc-capture"
            capture_bin.write_text("", encoding="utf-8")
            manifest_file = anneal_dir / "corpora" / "manifest.toml"
            manifest_file.write_text("schema_version = 1\n", encoding="utf-8")
            mir_eval_bin = repo_root / "tools" / "eval" / "anneal-mir-eval"
            mir_eval_bin.write_text("", encoding="utf-8")
            mir_eval_manifest = repo_root / "tools" / "eval" / "Cargo.toml"
            mir_eval_manifest.write_text(
                "[package]\nname = 'anneal-mir-eval'\n", encoding="utf-8"
            )
            (repo_root / "tools" / "eval" / "target" / "debug").mkdir(parents=True)
            (
                repo_root / "tools" / "eval" / "target" / "debug" / "anneal-mir-eval"
            ).write_text("", encoding="utf-8")

            sample = _sample_diff_report()
            recorded_calls: list[tuple[list[str], Path, dict[str, str]]] = []

            def fake_subprocess_run(
                args: list[str],
                *,
                cwd: Path | None = None,
                env: dict[str, str] | None = None,
                **kwargs: object,
            ) -> mock.Mock:
                if args and (
                    Path(args[0]).name in ("git", "rustc", "lean")
                    or "--version" in args
                ):
                    return mock.Mock(returncode=1, stdout="", stderr="")
                if len(args) >= 2 and args[1] == "test":
                    return mock.Mock(returncode=0, stdout="", stderr="")
                if len(args) >= 2 and args[1] == "build":
                    built_exe = (
                        repo_root
                        / "tools"
                        / "eval"
                        / "target"
                        / "debug"
                        / "anneal-mir-eval"
                    )
                    return mock.Mock(
                        returncode=0,
                        stdout=json.dumps(
                            {
                                "reason": "compiler-artifact",
                                "manifest_path": str(mir_eval_manifest.resolve()),
                                "target": {
                                    "kind": ["bin"],
                                    "name": "anneal-mir-eval",
                                },
                                "profile": {"test": False},
                                "executable": str(built_exe),
                            }
                        )
                        + "\n",
                        stderr="",
                    )
                recorded_calls.append(
                    (list(args), Path(cwd) if cwd else Path.cwd(), dict(env or {}))
                )
                return mock.Mock(
                    returncode=0, stdout=json.dumps(sample), stderr=""
                )

            prev_cwd = Path.cwd()
            try:
                os.chdir(repo_root)
                with (
                    mock.patch.dict(
                        os.environ,
                        {
                            "ANNEAL_CAPTURE": "anneal/target/debug/anneal-rustc-capture",
                            "ANNEAL_MIRI_SYSROOT": "rel-miri-sysroot",
                            "ANNEAL_DIFF_CACHE_DIR": "rel-diff-cache",
                            "CARGO_TARGET_DIR": "rel-cargo-target",
                            "CARGO": "./scripts/cargo-wrap",
                        },
                        clear=False,
                    ),
                    mock.patch(
                        "subprocess.run", side_effect=fake_subprocess_run
                    ),
                ):
                    rc = cmd.main(
                        [
                            "--anneal-root",
                            "anneal",
                            "--anneal-diff-bin",
                            "anneal/target/debug/anneal-diff",
                            "--manifest",
                            "anneal/corpora/manifest.toml",
                            "--capture-bin",
                            "anneal/target/debug/anneal-rustc-capture",
                            "--mir-eval-bin",
                            "tools/eval/anneal-mir-eval",
                            "--cache-root",
                            "rel-cache/diff",
                            "--output",
                            "rel-out/detail.json",
                            "--perf-metrics-out",
                            "rel-out/perf.json",
                            "--perf-record-out",
                            "rel-out/perf-record.json",
                            "--branch",
                            "rel-branch",
                            "--allow-unknown-git",
                        ]
                    )
                self.assertEqual(rc, 0)
                self.assertEqual(len(recorded_calls), 1)
                diff_args, diff_cwd, diff_env = recorded_calls[0]
                self.assertEqual(diff_cwd, anneal_dir)
                self.assertEqual(diff_args[0], str(diff_bin))
                self.assertEqual(
                    diff_args[diff_args.index("--manifest") + 1],
                    str(manifest_file),
                )
                self.assertEqual(
                    diff_args[diff_args.index("--capture-bin") + 1],
                    str(capture_bin),
                )
                self.assertEqual(
                    diff_args[diff_args.index("--mir-eval-bin") + 1],
                    str(mir_eval_bin),
                )
                self.assertEqual(
                    diff_args[diff_args.index("--cache-root") + 1],
                    str(repo_root / "rel-cache" / "diff"),
                )
                self.assertEqual(
                    diff_env["ANNEAL_CAPTURE"], str(capture_bin)
                )
                self.assertEqual(
                    diff_env["ANNEAL_MIRI_SYSROOT"],
                    str(repo_root / "rel-miri-sysroot"),
                )
                self.assertEqual(
                    diff_env["ANNEAL_DIFF_CACHE_DIR"],
                    str(repo_root / "rel-diff-cache"),
                )
                self.assertEqual(
                    diff_env["CARGO_TARGET_DIR"],
                    str(repo_root / "rel-cargo-target"),
                )
                self.assertEqual(
                    diff_env["CARGO"], str(repo_root / "scripts" / "cargo-wrap")
                )
                self.assertTrue((repo_root / "rel-out" / "detail.json").is_file())
                self.assertTrue((repo_root / "rel-out" / "perf.json").is_file())
                self.assertTrue(
                    (repo_root / "rel-out" / "perf-record.json").is_file()
                )

                # Direct `run_anneal_diff` call with relative `Path` objects
                # also anchors against the caller's working directory.
                recorded_calls.clear()
                with (
                    mock.patch.dict(os.environ, {"CARGO": "cargo"}, clear=False),
                    mock.patch(
                        "subprocess.run", side_effect=fake_subprocess_run
                    ),
                ):
                    rc_direct, _ = cmd.run_anneal_diff(
                        anneal_root=Path("anneal"),
                        manifest=Path("anneal/corpora/manifest.toml"),
                        capture_bin=Path("anneal/target/debug/anneal-rustc-capture"),
                        mir_eval_bin=Path("tools/eval/anneal-mir-eval"),
                        cache_root=Path("rel-cache/direct"),
                        self_check_oracle=False,
                        anneal_diff_bin=None,
                    )
                self.assertEqual(rc_direct, 0)
                direct_args, direct_cwd, direct_env = recorded_calls[0]
                self.assertEqual(direct_cwd, anneal_dir)
                self.assertEqual(direct_args[0], "cargo")
                self.assertEqual(direct_env["CARGO"], "cargo")
                self.assertEqual(
                    direct_args[direct_args.index("--manifest") + 1],
                    str(manifest_file),
                )
                self.assertEqual(
                    direct_args[direct_args.index("--cache-root") + 1],
                    str(repo_root / "rel-cache" / "direct"),
                )

                # Relative `--mir-eval-manifest` resolves against `repo_root`,
                # and missing relative manifests return `rc == 1` cleanly.
                recorded_calls.clear()
                with (
                    mock.patch.dict(os.environ, {}, clear=False),
                    mock.patch(
                        "subprocess.run", side_effect=fake_subprocess_run
                    ),
                ):
                    os.environ.pop("CARGO_TARGET_DIR", None)
                    rc_eval = cmd.main(
                        [
                            "--anneal-root",
                            "anneal",
                            "--anneal-diff-bin",
                            "anneal/target/debug/anneal-diff",
                            "--mir-eval-manifest",
                            "tools/eval/Cargo.toml",
                            "--branch",
                            "rel-branch",
                            "--allow-unknown-git",
                        ]
                    )
                    rc_missing_eval = cmd.main(
                        [
                            "--anneal-root",
                            "anneal",
                            "--anneal-diff-bin",
                            "anneal/target/debug/anneal-diff",
                            "--mir-eval-manifest",
                            "tools/eval/missing-Cargo.toml",
                            "--allow-unknown-git",
                        ]
                    )
                self.assertEqual(rc_eval, 0)
                self.assertEqual(rc_missing_eval, 1)
                eval_args, _, _ = recorded_calls[0]
                self.assertEqual(
                    eval_args[eval_args.index("--mir-eval-bin") + 1],
                    str(
                        repo_root
                        / "tools"
                        / "eval"
                        / "target"
                        / "debug"
                        / "anneal-mir-eval"
                    ),
                )

                # Reject symlinks on relative CLI paths (including lexical
                # `nonexistent/../sym` paths) before running child commands.
                sym_file = repo_root / "sym-target"
                os.symlink(diff_bin, sym_file)
                for flag in (
                    "--anneal-diff-bin",
                    "--manifest",
                    "--capture-bin",
                    "--mir-eval-bin",
                    "--mir-eval-manifest",
                    "--cache-root",
                    "--output",
                    "--perf-metrics-out",
                    "--perf-record-out",
                ):
                    for rel_sym in ("sym-target", "missing-parent/../sym-target"):
                        with self.subTest(flag=flag, rel_sym=rel_sym):
                            with self.assertRaises(ValueError):
                                cmd.main(
                                    [
                                        "--anneal-root",
                                        "anneal",
                                        flag,
                                        rel_sym,
                                        "--allow-unknown-git",
                                    ]
                                )
            finally:
                os.chdir(prev_cwd)

    def test_child_subprocesses_strip_actions_and_github_credentials(
        self,
    ) -> None:
        secret_env = {
            "ACTIONS_CACHE_URL": "https://results-receiver.actions.example/cache/",
            "ACTIONS_ID_TOKEN_REQUEST_TOKEN": "oidc-secret-token",
            "ACTIONS_ID_TOKEN_REQUEST_URL": "https://vstoken.actions.example/",
            "ACTIONS_RESULTS_URL": "https://results-receiver.actions.example/",
            "ACTIONS_RUNTIME_TOKEN": "runtime-secret-token",
            "ACTIONS_RUNTIME_URL": "https://pipelines.actions.example/",
            "GH_TOKEN": "ghs_secret_cli_token",
            "GITHUB_TOKEN": "ghs_secret_actions_token",
            "ANNEAL_BENIGN_TEST_VAR": "kept-value",
        }
        self.assertEqual(
            frozenset(cmd._STRIPPED_CHILD_ENV_VARS),
            frozenset(secret_env.keys()) - {"ANNEAL_BENIGN_TEST_VAR"},
        )

        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            (anneal_dir / "target" / "debug").mkdir(parents=True)
            diff_bin = anneal_dir / "target" / "debug" / "anneal-diff"
            diff_bin.write_text("", encoding="utf-8")

            eval_dir = root / "tools" / "eval"
            (eval_dir / "target" / "debug").mkdir(parents=True)
            eval_manifest = eval_dir / "Cargo.toml"
            eval_manifest.write_text(
                "[package]\nname = 'anneal-mir-eval'\n", encoding="utf-8"
            )
            (eval_dir / "target" / "debug" / "anneal-mir-eval").write_text(
                "", encoding="utf-8"
            )

            sample = _sample_diff_report()
            seen_envs: list[tuple[list[str], dict[str, str] | None]] = []

            def spy_subprocess_run(
                args: list[str],
                *,
                env: dict[str, str] | None = None,
                **kwargs: object,
            ) -> mock.Mock:
                seen_envs.append((list(args), None if env is None else dict(env)))
                if args and args[0] == "git":
                    if "rev-parse" in args and "--abbrev-ref" in args:
                        return mock.Mock(returncode=0, stdout="main\n", stderr="")
                    if "rev-parse" in args:
                        return mock.Mock(
                            returncode=0, stdout=("a" * 40) + "\n", stderr=""
                        )
                    return mock.Mock(
                        returncode=0, stdout="1780000000\n", stderr=""
                    )
                if args and "--version" in args:
                    return mock.Mock(
                        returncode=0, stdout="tool 1.0.0\n", stderr=""
                    )
                if len(args) >= 2 and args[1] == "test":
                    return mock.Mock(returncode=0, stdout="", stderr="")
                if len(args) >= 2 and args[1] == "build":
                    built_exe = eval_dir / "target" / "debug" / "anneal-mir-eval"
                    return mock.Mock(
                        returncode=0,
                        stdout=json.dumps(
                            {
                                "reason": "compiler-artifact",
                                "manifest_path": str(eval_manifest.resolve()),
                                "target": {
                                    "kind": ["bin"],
                                    "name": "anneal-mir-eval",
                                },
                                "profile": {"test": False},
                                "executable": str(built_exe),
                            }
                        )
                        + "\n",
                        stderr="",
                    )
                return mock.Mock(
                    returncode=0, stdout=json.dumps(sample), stderr=""
                )

            with (
                mock.patch.dict(os.environ, secret_env, clear=False),
                mock.patch("subprocess.run", side_effect=spy_subprocess_run),
            ):
                os.environ.pop("CARGO_TARGET_DIR", None)
                rc = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--anneal-diff-bin",
                        str(diff_bin),
                        "--mir-eval-manifest",
                        str(eval_manifest),
                    ]
                )
            self.assertEqual(rc, 0)
            # Covers git (3), cargo test/build (2), anneal-diff run (1),
            # and rustc/lean version probes (2).
            self.assertGreaterEqual(len(seen_envs), 8)
            for sub_args, sub_env in seen_envs:
                self.assertIsNotNone(
                    sub_env,
                    f"subprocess {sub_args!r} inherited raw os.environ",
                )
                assert sub_env is not None
                self.assertEqual(
                    sub_env.get("ANNEAL_BENIGN_TEST_VAR"), "kept-value"
                )
                for secret_key in cmd._STRIPPED_CHILD_ENV_VARS:
                    self.assertFalse(
                        secret_key in sub_env,
                        f"subprocess {sub_args!r} leaked {secret_key}",
                    )

    def test_artifact_manifest_and_missing_mir_eval_and_hex_provenance(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            manifest = Path(tmpd) / "Cargo.toml"
            manifest.write_text("[package]\nname='x'\n", encoding="utf-8")
            exe = Path(tmpd) / "anneal-mir-eval"
            exe.write_text("", encoding="utf-8")
            no_manifest_line = json.dumps(
                {
                    "reason": "compiler-artifact",
                    "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                    "profile": {"test": False},
                    "executable": str(exe),
                }
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    no_manifest_line, "anneal-mir-eval", manifest.resolve()
                )
            )

        detail_missing_eval = cmd.build_semantic_detail_report(
            diff_report=_sample_diff_report(),
            mir_eval_status={"executed": False, "passed": False},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
        )
        self.assertFalse(cmd.report_passes(detail_missing_eval))
