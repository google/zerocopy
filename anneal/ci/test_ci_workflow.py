# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exercise Anneal ci-core workflow, manifest, sandbox, and cache invariants."""

import hashlib
import os
from pathlib import Path
import re
import subprocess
import tempfile
import tomllib
import unittest

from anneal_ci_lib import WorkflowRepoFixture, find_workflow_step, load_workflow
from workflow_yaml import load_workflow_yaml


SOURCE = Path(__file__).resolve().parent
ANNEAL_ROOT = SOURCE.parent
REPO_ROOT = ANNEAL_ROOT.parent


def extract_bash_function(script_text: str, func_name: str) -> str:
    """Extract a top-level `func_name() { ... }` definition from bash text."""
    pattern = re.compile(
        rf"(?m)^{re.escape(func_name)}\(\)\s*\{{\n.*?\n\}}$",
        flags=re.DOTALL,
    )
    match = pattern.search(script_text)
    if match is None:
        raise AssertionError(f"missing bash function {func_name}()")
    return match.group(0)


class CiWorkflowManifestGuardTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.runner_script = (SOURCE / "run_anneal_check.sh").read_text()
        cls.pack_script = (SOURCE / "pack_omnibus_archive.sh").read_text()
        cls.manifest_fn = extract_bash_function(
            cls.runner_script, "verify_root_tcb_manifest"
        )
        cls.bundle_env_fn = extract_bash_function(
            cls.runner_script, "apply_bundle_env"
        )
        cls.checks_cfg = tomllib.loads(
            (REPO_ROOT / "ci/checks.toml").read_text()
        )
        cls.pr_wf = load_workflow_yaml(
            (REPO_ROOT / ".github/workflows/ci-core-pr.yml").read_text()
        )
        cls.trusted_wf = load_workflow_yaml(
            (REPO_ROOT / ".github/workflows/ci-core-trusted.yml").read_text()
        )
        cls.codeowners = (REPO_ROOT / ".github/CODEOWNERS").read_text()

    def run_manifest_guard(self, mutate=None, *, parent_override=False):
        with tempfile.TemporaryDirectory(prefix="anneal-ci-guard-") as tmp:
            root = Path(tmp) / "repo"
            project = root / "anneal"
            (project / "trusted").mkdir(parents=True)
            cargo_toml = project / "Cargo.toml"
            cargo_toml.write_bytes(b"[workspace]\n")
            digest = hashlib.sha256(cargo_toml.read_bytes()).hexdigest()
            (project / "trusted/root-manifest.sha256").write_text(
                f"{digest}  Cargo.toml\n"
            )

            if mutate is not None:
                mutate(root if parent_override else project)

            snippet = (
                "set -euo pipefail\n"
                f"{self.manifest_fn}\n"
                "verify_root_tcb_manifest\n"
            )
            return subprocess.run(
                ["bash", "--noprofile", "--norc", "-c", snippet],
                cwd=project,
                capture_output=True,
                text=True,
            )

    def test_manifest_guard_runs_unconditionally_before_mode_dispatch(self):
        call_idx = self.runner_script.index("\nverify_root_tcb_manifest\n")
        case_idx = self.runner_script.index('\ncase "$MODE" in\n')
        self.assertLess(call_idx, case_idx)

    def test_clean_tree_passes_manifest_guard(self):
        res = self.run_manifest_guard()
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

    def test_root_override_paths_and_symlinks_fail_closed(self):
        cases = [
            ("cargo_dir", lambda r: (r / ".cargo").mkdir()),
            ("cargo_file", lambda r: (r / ".cargo").write_text("")),
            ("rust_toolchain", lambda r: (r / "rust-toolchain").write_text("nightly\n")),
            ("rust_toolchain_toml", lambda r: (r / "rust-toolchain.toml").write_text("")),
            ("gitmodules", lambda r: (r / ".gitmodules").write_text("")),
            ("valid_symlink_cargo", lambda r: (r / ".cargo").symlink_to("Cargo.toml")),
            (
                "valid_symlink_toolchain",
                lambda r: (r / "rust-toolchain.toml").symlink_to("Cargo.toml"),
            ),
            ("dangling_symlink_cargo", lambda r: (r / ".cargo").symlink_to("missing")),
            (
                "dangling_symlink_toolchain",
                lambda r: (r / "rust-toolchain").symlink_to("missing"),
            ),
            (
                "dangling_symlink_gitmodules",
                lambda r: (r / ".gitmodules").symlink_to("missing"),
            ),
        ]
        for parent_override in (False, True):
            for label, mutate in cases:
                with self.subTest(case=label, parent=parent_override):
                    res = self.run_manifest_guard(
                        mutate=mutate, parent_override=parent_override
                    )
                    self.assertNotEqual(res.returncode, 0)
                    self.assertIn(
                        "forbidden root config override:",
                        res.stdout + res.stderr,
                    )

    def test_trusted_tree_symlink_and_manifest_tamper_fail_closed(self):
        res_link = self.run_manifest_guard(
            mutate=lambda p: (p / "trusted/evil_link").symlink_to("../Cargo.toml")
        )
        self.assertNotEqual(res_link.returncode, 0)
        self.assertIn(
            "symlink in Anneal trusted tree:",
            res_link.stdout + res_link.stderr,
        )

        res_tamper = self.run_manifest_guard(
            mutate=lambda p: (p / "Cargo.toml").write_bytes(b"[workspace]\n# x\n")
        )
        self.assertNotEqual(res_tamper.returncode, 0)

    def test_apply_bundle_env_rejects_malformed_lines_and_preserves_spaces(self):
        with tempfile.TemporaryDirectory(prefix="anneal-bundle-env-") as tmp:
            root = Path(tmp)
            (root / "ci").mkdir()
            script = root / "ci/check_bundle_tree.py"

            def run_case(py_body: str):
                script.write_text(py_body)
                snippet = (
                    "set -euo pipefail\n"
                    f"{self.bundle_env_fn}\n"
                    "apply_bundle_env --demo\n"
                    'printf "%s" "${RUSTFLAGS:-}"\n'
                )
                return subprocess.run(
                    ["bash", "--noprofile", "--norc", "-c", snippet],
                    cwd=root,
                    capture_output=True,
                    text=True,
                )

            ok = run_case(
                'print("ANNEAL_SYSROOT=/opt/sysroot")\n'
                'print("RUSTFLAGS=-Lnative=/opt/path with spaces/lib")\n'
            )
            self.assertEqual(ok.returncode, 0, ok.stderr)
            self.assertEqual(ok.stdout, "-Lnative=/opt/path with spaces/lib")

            no_eq = run_case('print("MALFORMED_LINE")\n')
            self.assertNotEqual(no_eq.returncode, 0)
            self.assertIn("malformed check_bundle_tree.py line", no_eq.stderr)

            bad_key = run_case('print("bad-key=1")\n')
            self.assertNotEqual(bad_key.returncode, 0)
            self.assertIn("invalid check_bundle_tree.py env key", bad_key.stderr)

            exit_fail = run_case("import sys\nsys.exit(3)\n")
            self.assertNotEqual(exit_fail.returncode, 0)

    def test_active_ci_core_workflows_and_tcb_dominance(self):
        for retired in ("anneal.yml", "anneal-current.yml", "ci.yml"):
            self.assertFalse(
                (REPO_ROOT / ".github/workflows" / retired).exists(),
                f"legacy workflow {retired} must be retired after cutover",
            )

        repo_cfg = self.checks_cfg["repo"]
        trusted_shas = set(repo_cfg["trusted_engine_shas"])
        self.assertTrue(trusted_shas)
        for sha in trusted_shas:
            self.assertRegex(sha, r"^[0-9a-f]{40}$")

        trusted_engine_wf = repo_cfg["trusted_engine_workflow"]
        self.assertTrue(trusted_engine_wf.endswith("/.github/workflows/ci.yml"))
        pr_engine_wf = trusted_engine_wf[: -len("ci.yml")] + "ci-pr.yml"

        for wf, expected_workflow in (
            (self.pr_wf, pr_engine_wf),
            (self.trusted_wf, trusted_engine_wf),
        ):
            self.assertEqual(wf.get("permissions"), {})
            job = wf["jobs"]["ci-core"]
            self.assertEqual(job["with"]["config_path"], "ci/checks.toml")
            uses_wf, sep, uses_sha = job["uses"].partition("@")
            self.assertEqual(sep, "@")
            self.assertEqual(uses_wf, expected_workflow)
            self.assertIn(uses_sha, trusted_shas)

        self.assertEqual(
            self.pr_wf["jobs"]["ci-core"]["with"].get("shadow_mode", "false"),
            "false",
        )
        self.assertNotIn("shadow_mode", self.trusted_wf["jobs"]["ci-core"]["with"])

        self.assertEqual(
            self.pr_wf["jobs"]["ci-core"]["permissions"],
            {
                "actions": "read",
                "contents": "read",
                "packages": "read",
                "pull-requests": "read",
            },
        )
        self.assertEqual(
            self.trusted_wf["jobs"]["ci-core"]["permissions"],
            {
                "actions": "read",
                "contents": "read",
                "id-token": "write",
                "packages": "write",
                "pull-requests": "read",
            },
        )

        tcb_cfg = self.checks_cfg["tcb"]
        self.assertIs(tcb_cfg["allow_owner_self_approval"], True)
        # Every root workflow stays in the TCB: the engine's non-TCB
        # permission scan cannot see `secrets.*` use or job names that spoof
        # required checks.
        self.assertEqual(tcb_cfg.get("non_tcb_workflows", []), [])
        for exec_glob in (
            "anneal/ci/**",
            "ci/scripts/**",
            "zerocopy/cargo.sh",
            "zerocopy/ci/**",
        ):
            self.assertIn(exec_glob, tcb_cfg["extra_executable_paths"])
        self.assertEqual(
            tcb_cfg["caller"]["caller_workflows"],
            [
                ".github/workflows/ci-core-pr.yml",
                ".github/workflows/ci-core-trusted.yml",
            ],
        )
        self.assertEqual(tcb_cfg["caller"]["gate_check_name"], "ci-core / gate")

        for owner_rule in (
            "/.github/**",
            "/ci/**",
            "/zerocopy/cargo.sh",
            "/tools/**",
            "/anneal/ci/**",
            "/anneal/flake.nix",
            "/anneal/flake.lock",
            "/anneal/Cargo.toml",
            "/anneal/Cargo.lock",
            "/anneal/trusted/**",
            "/anneal/vendor/lean-miri/UPSTREAM_PIN.json",
        ):
            self.assertIn(owner_rule, self.codeowners)

    def test_anneal_checks_nested_bwrap_and_miri_cache_isolation(self):
        checks_by_id = {c["id"]: c for c in self.checks_cfg["checks"]}
        self.assertEqual(
            checks_by_id["meta-githooks"]["command"],
            ["./ci/scripts/check_shell_and_hooks.sh", "--require-shellcheck"],
        )

        expected_anneal = (
            "anneal-flake-eval",
            "anneal-ci-tests",
            "anneal-clippy",
            "anneal-sandbox-aarch64",
            "anneal-audit",
            "anneal-guard-mutation",
            "anneal-ws-meta",
            "anneal-ws-test",
            "anneal-installed-smoke",
        )
        for cid in expected_anneal:
            self.assertIn(cid, checks_by_id)
            self.assertNotIn(
                "events",
                checks_by_id[cid],
                f"{cid} must run across PR, merge_group, and push",
            )

        for bwrap_cid in (
            "anneal-flake-eval",
            "anneal-ci-tests",
            "anneal-audit",
            "anneal-guard-mutation",
            "anneal-ws-meta",
            "anneal-ws-test",
            "anneal-installed-smoke",
        ):
            chk = checks_by_id[bwrap_cid]
            self.assertEqual(chk.get("sandbox"), "nested_bwrap", bwrap_cid)
            self.assertEqual(chk.get("image"), "anneal-tc", bwrap_cid)

        arm_chk = checks_by_id["anneal-sandbox-aarch64"]
        self.assertEqual(arm_chk.get("sandbox"), "nested_bwrap")
        self.assertEqual(arm_chk.get("runner"), "ubuntu-24.04-arm")
        self.assertEqual(arm_chk.get("image"), "anneal-arm64")
        self.assertEqual(arm_chk.get("command"), ["./ci/run_anneal_check.sh", "sandbox"])
        self.assertEqual(
            self.checks_cfg["images"]["anneal-arm64"].get("platform"),
            "linux/arm64",
        )

        miri_cache = self.checks_cfg["caches"]["miri-v1"]
        self.assertEqual(miri_cache["tier"], "public_cas")
        self.assertEqual(miri_cache["mount"], "/ci-cache/miri")
        self.assertFalse(miri_cache["mount"].startswith("/work"))
        miri_inputs = set()
        for entry in miri_cache["inputs"]:
            miri_inputs.update(entry.get("include", ()))
        for key_file in (
            "anneal/flake.nix",
            "anneal/flake.lock",
            "anneal/trusted/lean/lean-toolchain",
            "anneal/trusted/lean/foundation-lock.json",
            "anneal/vendor/lean-miri/UPSTREAM_PIN.json",
        ):
            self.assertIn(key_file, miri_inputs)

        audit_match = re.search(
            r"(?ms)^\s*audit\)\n(.*?)\n\s*;;$", self.runner_script
        )
        self.assertIsNotNone(audit_match)
        audit_body = audit_match.group(1)

        with tempfile.TemporaryDirectory(prefix="anneal-miri-cache-") as tmp:
            tmp_path = Path(tmp)
            bin_dir = tmp_path / "bin"
            bin_dir.mkdir()
            recorded = tmp_path / "cargo_args.txt"
            seen_env = tmp_path / "ambient_env.txt"
            stub_cargo = bin_dir / "cargo"
            stub_cargo.write_text(
                "#!/usr/bin/env bash\n"
                f"printf '%s\\n' \"$@\" > '{recorded}'\n"
                f"printf '%s' \"${{ANNEAL_MIRI_CACHE_DIR-UNSET}}\" > '{seen_env}'\n"
            )
            stub_cargo.chmod(0o755)
            scratch_root = tmp_path / "scratch"
            scratch_miri = scratch_root / "miri-cache"

            # Execute the real `audit)` cache-selection logic with
            # `SCRATCH_ROOT` bound directly and stubbed
            # `verify_bwrap_sandbox`/`apply_bundle_env`.
            adapted_body = audit_body.replace(
                "cp -rL /opt/anneal-nix/lean-toolchain",
                "mkdir -p",
            )
            harness = (
                "set -euo pipefail\n"
                "unset ANNEAL_MIRI_CACHE_DIR ANNEAL_TEST_ARCHIVE ANNEAL_TEST_CASE\n"
                f"export SCRATCH_ROOT='{scratch_root}'\n"
                "HASH_OPT_ARGS=(--config 'profile.dev.package.sha2.opt-level=3')\n"
                "verify_bwrap_sandbox() { :; }\n"
                "apply_bundle_env() { export ANNEAL_TEST_INSTALL_ROOT=/fake/install; }\n"
                f"{adapted_body}\n"
            )

            def run_audit_probe(cache_path: Path):
                recorded.unlink(missing_ok=True)
                seen_env.unlink(missing_ok=True)
                env = os.environ.copy()
                env["PATH"] = f"{bin_dir}:{env.get('PATH', '')}"
                env["ANNEAL_MIRI_CACHE_DIR"] = "/ambient/poison"
                env["ANNEAL_CI_MIRI_CACHE_DIR"] = str(cache_path)
                res = subprocess.run(
                    ["bash", "--noprofile", "--norc", "-c", harness],
                    cwd=tmp_path,
                    env=env,
                    capture_output=True,
                    text=True,
                )
                self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
                self.assertEqual(seen_env.read_text(), "UNSET")
                return recorded.read_text().splitlines()

            # 1. Absent cache -> cold build without --miri-cache-dir.
            cold_args = run_audit_probe(tmp_path / "missing-cache")
            self.assertNotIn("--miri-cache-dir", cold_args)

            # 2. Writable cache -> passes --miri-cache-dir directly.
            rw_cache = tmp_path / "rw-cache"
            rw_cache.mkdir()
            rw_args = run_audit_probe(rw_cache)
            self.assertIn("--miri-cache-dir", rw_args)
            self.assertIn(str(rw_cache), rw_args)

            # 3. Read-only cache -> copies to scratch and passes scratch dir.
            ro_cache = tmp_path / "ro-cache"
            ro_cache.mkdir()
            (ro_cache / "marker.olean").write_text("olean")
            ro_cache.chmod(0o555)
            try:
                ro_args = run_audit_probe(ro_cache)
            finally:
                ro_cache.chmod(0o755)
            if os.geteuid() != 0:
                self.assertIn("--miri-cache-dir", ro_args)
                self.assertIn(str(scratch_miri), ro_args)
                self.assertTrue((scratch_miri / "marker.olean").is_file())

    def test_runner_optimization_sandbox_and_python_isolation_invariants(self):
        self.assertIn('CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-4}"', self.runner_script)
        self.assertIn('RUST_TEST_THREADS="${RUST_TEST_THREADS:-4}"', self.runner_script)
        self.assertIn("CARGO_NET_OFFLINE=true", self.runner_script)
        self.assertIn('ANNEAL_TEST_JOBS="4"', self.runner_script)

        for pkg in ("cpufeatures", "digest", "sha2", "zstd-sys"):
            self.assertIn(
                f"--config 'profile.dev.package.{pkg}.opt-level=3'",
                self.runner_script,
            )

        for mode_header in ("sandbox)", "audit)", "ws-meta)", "ws-test)", "installed-smoke)"):
            idx = self.runner_script.index(f"  {mode_header}\n")
            end = self.runner_script.index("\n    ;;", idx)
            window = self.runner_script[idx:end]
            self.assertIn("verify_bwrap_sandbox", window, mode_header)

        for sandbox_test in (
            "sandbox_escape_vectors_blocked_in_tier1_and_tier2",
            "wall_clock_timeout_kills_process_group_in_tier1_and_tier2",
            "tier1_as_pid1_prevents_post_exit_out_writes",
        ):
            self.assertIn(sandbox_test, self.runner_script)

        self.assertIn(
            "cargo package --allow-dirty --no-verify --offline --registry crates-io",
            self.runner_script,
        )
        self.assertIn(
            'cargo build --locked --offline --manifest-path "$PREPARED_MANIFEST"',
            self.runner_script,
        )
        self.assertIn(
            'cargo test --locked --offline --manifest-path "$PREPARED_MANIFEST" --no-run',
            self.runner_script,
        )
        self.assertIn("ci/probe_alpha.py --cli /cargo-anneal", self.runner_script)
        self.assertIn("ci/verify_starnix_e2e.py", self.runner_script)
        self.assertIn("ci/verify_zerocopy.py", self.runner_script)

        # Every inline python3 heredoc in run_anneal_check.sh must run with
        # `-I -B` so repository files cannot shadow stdlib modules.
        heredocs = list(re.finditer(r"python3\b[^;\n]*<<", self.runner_script))
        self.assertGreaterEqual(len(heredocs), 1)
        for match in heredocs:
            self.assertIn("python3 -I -B -", match.group(0))

    def _runner_mode(self, mode):
        idx = self.runner_script.index(f"  {mode})\n")
        end = self.runner_script.index("\n    ;;", idx)
        return self.runner_script[idx:end]

    def test_static_checks_enforce_wasm32_core_and_offline_inspect(self):
        # `#4220`: the pure `cargo_anneal::core` must keep building for
        # `wasm32-unknown-unknown` with `-D warnings`, and the offline
        # `inspect` CLI must be linted and tested without default features.
        clippy = self._runner_mode("clippy")
        self.assertIn(
            'RUSTFLAGS="-D warnings" cargo check --locked --offline', clippy
        )
        self.assertIn("--lib --target wasm32-unknown-unknown", clippy)
        self.assertIn("--test cli --test inspect", clippy)
        ws_meta = self._runner_mode("ws-meta")
        self.assertIn("--test cli --test inspect", ws_meta)

    def test_installed_smoke_package_stages_generated_bundle_in_scratch(self):
        # `#4244` and `#4341` generate `bundled_resources.rs` and
        # `bundled_theory.json` in `build.rs`, so `cargo package` needs both
        # staged under `packaged/`. The read-only checkout must stay
        # untouched: staging happens only in a scratch copy, must stage
        # exactly those two files, and must use the same optimization flags
        # as the other Cargo invocations.
        idx = self.runner_script.index("  installed-smoke)\n")
        end = self.runner_script.index("\n    ;;", idx)
        window = self.runner_script[idx:end]
        stage_start = window.index('PKG_SRC="${SCRATCH_ROOT}/package-src"')
        stage_end = window.index('rm -rf "$PKG_SRC"\n    PREPARED_MANIFEST=')
        stage = window[stage_start:stage_end]
        self.assertIn('cp -a . "$PKG_SRC/anneal"', stage)
        self.assertIn('cd "$PKG_SRC/anneal"', stage)
        self.assertIn("test ! -e trusted/cargo-anneal/packaged", stage)
        self.assertIn("-- --root . --stage-package", stage)
        self.assertIn(
            'staged="$(cd trusted/cargo-anneal/packaged && '
            'find . -mindepth 1 | LC_ALL=C sort)"',
            stage,
        )
        self.assertIn(
            "expected_staged=\"$(printf './bundled_resources.rs\\n"
            "./bundled_theory.json')\"",
            stage,
        )
        self.assertIn('test "$staged" = "$expected_staged"', stage)
        self.assertLess(
            stage.index("--stage-package"),
            stage.index("cargo package --allow-dirty"),
        )
        self.assertEqual(stage.count('"${FULL_OPT_ARGS[@]}"'), 2)
        # The checked-in generated file is gone; provenance comes from the
        # shared renderer invoked via `pack_omnibus_archive.sh` instead of
        # scraping Rust source.
        self.assertIn("build_omnibus_archive", window)
        self.assertIn("ci/pack_omnibus_archive.sh", self.runner_script)
        self.assertNotIn("src/bundled_resources.rs", self.runner_script)
        self.assertNotIn("src/bundled_resources.rs", self.pack_script)
        self.assertIn("ci/render_correspondence_provenance.py", self.pack_script)


class PrHygieneWorkflowTests(unittest.TestCase):
    """`check_pr_hygiene.py` reads Git history and PR event metadata, which
    `ci-core` sandboxes do not provide, so it runs in its own workflow. The
    job is required, but its diff and commit-message checks are waivable
    with a `Skip-pr-hygiene:` trailer on the PR's tip commit."""

    PATH = REPO_ROOT / ".github/workflows/anneal-pr-hygiene.yml"
    ON_PR = "github.event_name == 'pull_request'"
    ON_MERGE_GROUP = "github.event_name == 'merge_group'"

    def setUp(self):
        self.workflow = load_workflow(self.PATH)
        self.job = self.workflow["jobs"]["pr-hygiene"]
        self.step = find_workflow_step(
            self.workflow, "pr-hygiene", step_name="Run PR hygiene check"
        )

    def test_pr_hygiene_workflow_is_read_only(self):
        wf = self.workflow
        self.assertEqual(wf["name"], "Anneal PR Hygiene")
        self.assertEqual(wf["permissions"], {})
        # Merge group runs have no checkout, so no `anneal/` directory
        # exists for a workflow-level default to enter.
        self.assertNotIn("defaults", wf)
        self.assertEqual(list(wf["jobs"]), ["pr-hygiene"])
        job = self.job
        self.assertEqual(job["name"], "PR hygiene")
        self.assertEqual(job["runs-on"], "ubuntu-latest")
        self.assertEqual(job["permissions"], {"contents": "read"})
        self.assertNotIn("defaults", job)
        self.assertEqual(job["env"], {
            "ACTIONS_CACHE_URL": "",
            "ACTIONS_RESULTS_URL": "",
            "ACTIONS_RUNTIME_TOKEN": "",
            "ACTIONS_RUNTIME_URL": "",
        })

    def test_triggers_and_concurrency(self):
        wf = self.workflow
        self.assertEqual(set(wf["on"]), {"pull_request", "merge_group"})
        # `edited` re-checks retitled and retargeted PRs.
        self.assertEqual(
            wf["on"]["pull_request"],
            {"types": ["opened", "synchronize", "reopened", "edited"]},
        )
        self.assertIn(wf["on"]["merge_group"], (None, "", {}))
        # A merge group run must report for its exact commit.
        self.assertEqual(wf["concurrency"], {
            "group": "${{ github.workflow }}-${{ github.ref }}",
            "cancel-in-progress": "${{ " + self.ON_PR + " }}",
        })

    def test_every_pull_request_event_runs_the_full_check(self):
        # A fast path for description-only edits would let an edit replace
        # a failing result for the same head with a passing one.
        self.assertNotIn("github.event.changes", self.PATH.read_text())
        steps = self.job["steps"]
        self.assertEqual(
            [s.get("if") for s in steps],
            [self.ON_PR, self.ON_PR, self.ON_MERGE_GROUP],
        )
        checkout = steps[0]
        self.assertEqual(
            checkout["uses"],
            "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1",
        )
        # `merge_base(base, head)` needs history; no token may persist.
        self.assertEqual(
            checkout["with"],
            {"fetch-depth": "0", "persist-credentials": "false"},
        )
        self.assertIs(steps[1], self.step)
        self.assertEqual(self.step["working-directory"], "anneal")

    def test_merge_group_step_needs_no_checkout(self):
        step = self.job["steps"][2]
        self.assertEqual(step["name"], "Skip PR hygiene on merge groups")
        self.assertNotIn("uses", step)
        self.assertNotIn("working-directory", step)
        self.assertNotIn("${{", step["run"])
        with WorkflowRepoFixture(prefix="anneal-pr-hygiene-mq-") as fx:
            empty = fx.mkdir("workspace")
            res = fx.run_bash(step["run"], cwd=empty)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertIn("::notice::", res.stdout)

    def test_title_regex_matches_commit_policy(self):
        checks_cfg = tomllib.loads((REPO_ROOT / "ci/checks.toml").read_text())
        policy = checks_cfg["commit_policy"]["forbid_message_regex"]
        self.assertEqual(policy, r"\b[T]ODO\b")
        flags = re.findall(r"--forbid-pr-title-regex '([^']*)'",
                           self.step["run"])
        self.assertEqual(flags, [policy])
        # Title equality applies only to single-commit PRs and is checked
        # by publishing tooling, not here.
        self.assertNotIn("--pr-title ", self.step["run"])

    def test_pr_hygiene_step_reads_event_data_from_env(self):
        step = self.step
        # Event data reaches the script only through `env`, never by
        # template expansion inside `run`.
        self.assertNotIn("${{", step["run"])
        self.assertEqual(step["env"], {
            "PR_BASE_SHA": "${{ github.event.pull_request.base.sha }}",
            "PR_HEAD_SHA": "${{ github.event.pull_request.head.sha }}",
            "PR_AUTHOR_TYPE": "${{ github.event.pull_request.user.type }}",
            "PR_TITLE": "${{ github.event.pull_request.title }}",
        })
        self.assertIn("set -euo pipefail", step["run"])

    def test_pr_hygiene_step_behavior(self):
        step = self.step
        marker = "TO" + "DO"
        trailer = "Agent-authored-by: AI agent acting on joshlf's behalf"
        with WorkflowRepoFixture(prefix="anneal-pr-hygiene-step-") as fx:
            root = fx.init_repo("repo")
            project = fx.mkdir("repo/anneal")
            fx.write_bytes(
                "repo/anneal/ci/check_pr_hygiene.py",
                (SOURCE / "check_pr_hygiene.py").read_bytes(),
            )
            rules = (
                "<!-- code-review-rules:begin -->\nR\n"
                "<!-- code-review-rules:end -->\n"
            )
            fx.write_file("repo/anneal/AGENTS.md", rules)
            fx.write_file("repo/anneal/.gemini/styleguide.md", rules)
            base = fx.commit_all(root, "init")
            fx.write_file("repo/anneal/ci/new.py", "X = 1\n")
            head = fx.commit_all(root, "[ci] Add a file without a header")
            summary = fx.root / "summary.md"

            def run(author_type="User", title="[ci] Add a file", sha=None):
                env = os.environ.copy()
                env.pop("GITHUB_STEP_SUMMARY", None)
                env.update(
                    PR_BASE_SHA=base,
                    PR_HEAD_SHA=sha or head,
                    PR_AUTHOR_TYPE=author_type,
                    PR_TITLE=title,
                    GITHUB_STEP_SUMMARY=str(summary),
                )
                return fx.run_bash(step["run"], cwd=project, env=env)

            res = run()
            self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
            self.assertIn("[header] anneal/ci/new.py", res.stderr)
            self.assertNotIn("--skip-commit-messages", res.stderr)
            res = run(author_type="Bot")
            self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
            self.assertIn("skipped: --skip-commit-messages", res.stderr)
            res = run(title=f"[ci] Add a file ({marker})")
            self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
            self.assertIn("[pr-title-policy]", res.stderr)
            self.assertFalse(summary.exists())

            # The tip commit waives the header finding loudly.
            fx.git(root, "commit", "-q", "--amend", "-m",
                   "[ci] Add a file without a header\n\n"
                   "Skip-pr-hygiene: header -- Fixture without a header.\n"
                   f"{trailer}\n")
            waived = fx.git(root, "rev-parse", "HEAD").stdout.strip()
            res = run(sha=waived)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertIn("::warning file=anneal/ci/new.py,line=1,",
                          res.stdout)
            self.assertIn("Fixture without a header.", summary.read_text())
            # A waiver cannot cover the title policy.
            res = run(sha=waived, title=f"{marker}: header")
            self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
            self.assertIn("[pr-title-policy]", res.stderr)


if __name__ == "__main__":
    unittest.main()
