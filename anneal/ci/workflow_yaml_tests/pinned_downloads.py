# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Workflow YAML tests for pinned `curl` and `wget` download steps."""

from .support import (
    _find_unpinned_download_steps,
    load_workflow_yaml,
    mock,
    Path,
    PINNED_DOWNLOAD_STEPS,
    REPO_ROOT,
    tempfile,
    WORKFLOWS_DIR,
    YQ_ACTION_FIXTURE,
    YQ_ACTION_FIXTURE_PIN,
    YQ_ACTION_FIXTURE_REL,
)


class PinnedDownloadCases:
    """`WorkflowPolicyLintTests` methods for pinned `curl` and `wget` download
    steps."""

    def test_workflows_pin_curl_and_wget_steps(self):
        violations = []
        matched = set()
        docs_by_rel = {}
        for path in self._mounted_yaml_targets():
            doc = load_workflow_yaml(path.read_text(encoding="utf-8"))
            rel = path.relative_to(REPO_ROOT).as_posix()
            docs_by_rel[rel] = doc
            violations.extend(_find_unpinned_download_steps(doc, rel, matched))
        self.assertEqual(violations, [])
        # Fail closed if any pinned workflow/action file is omitted from the
        # mounted tree or CI closure (`anneal-ci-tests` mounts all of them).
        self.assertEqual(matched, set(PINNED_DOWNLOAD_STEPS))

        with tempfile.TemporaryDirectory(prefix="anneal-wf-yaml-") as tmp:
            tmp_root = Path(tmp)
            wf_dir = tmp_root / ".github" / "workflows"
            act_dir = tmp_root / ".github" / "actions"
            wf_dir.mkdir(parents=True)
            (act_dir / "pub").mkdir(parents=True)
            (wf_dir / "alt.yaml").write_text("on: push\n", encoding="utf-8")
            (act_dir / "pub" / "action.yaml").write_text(
                "name: p\n", encoding="utf-8"
            )
            self.assertEqual(
                self._mounted_yaml_targets(wf_dir, act_dir),
                [wf_dir / "alt.yaml", act_dir / "pub" / "action.yaml"],
            )

        # Spot-check safety invariants on every pinned live step.
        rel_doc = docs_by_rel[".github/workflows/release.yml"]
        rel_exists_run = rel_doc["jobs"]["anneal-build-archive"]["steps"][2][
            "run"
        ]
        self.assertIn("$RUNNER_TEMP/rel-check.json", rel_exists_run)
        host_check_run = rel_doc["jobs"]["anneal-host-archive"]["steps"][2][
            "run"
        ]
        self.assertIn("$RUNNER_TEMP/host-check.json", host_check_run)
        self.assertIn("jq -e", host_check_run)
        upload_run = rel_doc["jobs"]["anneal-host-archive"]["steps"][4]["run"]
        self.assertIn("sha256sum", upload_run)
        self.assertIn('--upload-file "$archive_file"', upload_run)
        env_run = rel_doc["jobs"]["anneal-qualify-package"]["steps"][0]["run"]
        self.assertIn('"$environment_api"', env_run)
        self.assertIn("| jq -e", env_run)

        roller_doc = docs_by_rel[
            ".github/workflows/roll-pinned-toolchain-versions.yml"
        ]
        semver_run = roller_doc["jobs"]["roll_semver_baseline"]["steps"][1][
            "run"
        ]
        self.assertIn("https://index.crates.io/ze/ro/zerocopy", semver_run)
        self.assertIn("jq -rs", semver_run)
        kani_run = roller_doc["jobs"]["roll_kani"]["steps"][1]["run"]
        self.assertIn(
            'KANI_BUNDLE_SHA="$(sha256sum "$KANI_BUNDLE_TMP"', kani_run
        )
        self.assertIn('rm -f "$KANI_BUNDLE_TMP"', kani_run)
        self.assertNotIn("tar ", kani_run)

        # The cases below pin the retired `install-yq` action as a fixture.
        self.enterContext(
            mock.patch.dict(PINNED_DOWNLOAD_STEPS, YQ_ACTION_FIXTURE_PIN)
        )
        yq_text = YQ_ACTION_FIXTURE
        yq_doc = load_workflow_yaml(yq_text)
        self.assertEqual(
            _find_unpinned_download_steps(yq_doc, YQ_ACTION_FIXTURE_REL), []
        )
        yq_run = yq_doc["runs"]["steps"][0]["run"]
        self.assertIn("--proto '=https' --tlsv1.2", yq_run)
        self.assertIn("sha256sum --check --strict", yq_run)
        dup_yq_text = (
            yq_text
            + "\n    - name: Install pinned yq binary\n"
            + "      run: curl -fsSL https://example.com/dup\n"
        )
        # Any unpinned curl/wget step fails closed (case-insensitive, incl.
        # subshells, env smuggling, mapping keys, and duplicate step keys).
        unpinned_cases = (
            (
                "unpinned_curl_step",
                ".github/workflows/new.yml",
                "jobs:\n  install:\n    steps:\n      - name: Fetch\n"
                "        run: |\n"
                "          curl -fsSL https://example.com/install.sh | bash\n",
                "unpinned curl/wget step",
            ),
            (
                "unpinned_wget_mixed_case",
                ".github/actions/new/action.yaml",
                "runs:\n  steps:\n    - id: dl\n"
                "      run: Wget -qO- https://example.com/s.tgz | tar xz\n",
                "unpinned curl/wget step",
            ),
            (
                "env_smuggled_curl",
                ".github/workflows/new.yml",
                "jobs:\n  j:\n    env:\n      DL: curl\n    steps:\n"
                "      - run: \"$DL https://example.com/x\"\n",
                "outside step.run",
            ),
            (
                "with_script_smuggled_wget",
                ".github/workflows/new.yml",
                "jobs:\n  j:\n    steps:\n"
                "      - uses: actions/github-script@abc\n"
                "        with:\n"
                "          script: exec('wget -qO- https://example.com')\n",
                "outside step.run",
            ),
            (
                "mapping_key_curl",
                ".github/workflows/new.yml",
                "jobs:\n  j:\n    env:\n      curl: enabled\n",
                "mapping key",
            ),
            (
                "duplicate_pinned_step_key",
                YQ_ACTION_FIXTURE_REL,
                dup_yq_text,
                "duplicate curl/wget step key",
            ),
        )
        for label, rel_path, yaml_text, msg_sub in unpinned_cases:
            with self.subTest(case=label):
                hits = _find_unpinned_download_steps(
                    load_workflow_yaml(yaml_text), rel_path
                )
                self.assertEqual(len(hits), 1, yaml_text)
                self.assertIn(msg_sub, hits[0])

        # Any modification to a pinned step's `run:`, `env:`, `shell:`,
        # `working-directory:`, `if:`, job `env:`, top `env:`, or action
        # `inputs:` fails closed.
        roller_text = (
            WORKFLOWS_DIR / "roll-pinned-toolchain-versions.yml"
        ).read_text(encoding="utf-8")
        rel_text = (WORKFLOWS_DIR / "release.yml").read_text(encoding="utf-8")
        yq_mutations = (
            (
                "yq_run_removed_sha",
                yq_text,
                yq_text.replace(
                    'printf \'%s  %s\\n\' "${YQ_SHA256}" "${tmp_bin}" '
                    "| sha256sum --check --strict",
                    "# sha256 check removed",
                ),
                YQ_ACTION_FIXTURE_REL,
            ),
            (
                "yq_env_swapped",
                yq_text,
                yq_text.replace("YQ_VERSION: v4.44.1", "YQ_VERSION: v9.9.9"),
                YQ_ACTION_FIXTURE_REL,
            ),
            (
                "yq_shell_changed",
                yq_text,
                yq_text.replace("shell: bash", "shell: sh"),
                YQ_ACTION_FIXTURE_REL,
            ),
            (
                "yq_step_working_dir_added",
                yq_text,
                yq_text.replace(
                    "shell: bash", "shell: bash\n      working-directory: /tmp"
                ),
                YQ_ACTION_FIXTURE_REL,
            ),
            (
                "yq_action_inputs_added",
                yq_text,
                yq_text.replace(
                    "runs:", "inputs:\n  ver:\n    default: bad\nruns:"
                ),
                YQ_ACTION_FIXTURE_REL,
            ),
            (
                "roller_kani_unpack",
                roller_text,
                roller_text.replace(
                    'rm -f "$KANI_BUNDLE_TMP"',
                    'tar -xzf "$KANI_BUNDLE_TMP"\n'
                    '            rm -f "$KANI_BUNDLE_TMP"',
                ),
                ".github/workflows/roll-pinned-toolchain-versions.yml",
            ),
            (
                "release_job_env_changed",
                rel_text,
                rel_text.replace(
                    "  anneal-build-archive:\n",
                    "  anneal-build-archive:\n    env:\n      OVERRIDE: 1\n",
                ),
                ".github/workflows/release.yml",
            ),
            (
                "roller_top_env_changed",
                roller_text,
                roller_text.replace(
                    "CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN: 1",
                    "CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN: 0",
                ),
                ".github/workflows/roll-pinned-toolchain-versions.yml",
            ),
            (
                "release_job_defaults_added",
                rel_text,
                rel_text.replace(
                    "  anneal-build-archive:\n",
                    "  anneal-build-archive:\n"
                    "    defaults:\n      run:\n        shell: sh\n",
                ),
                ".github/workflows/release.yml",
            ),
            (
                "release_top_defaults_added",
                rel_text,
                rel_text.replace(
                    "jobs:\n",
                    "defaults:\n  run:\n    working-directory: /tmp\njobs:\n",
                ),
                ".github/workflows/release.yml",
            ),
            (
                "roller_job_container_added",
                roller_text,
                roller_text.replace(
                    "  roll_kani:\n",
                    "  roll_kani:\n    container: ubuntu:latest\n",
                ),
                ".github/workflows/roll-pinned-toolchain-versions.yml",
            ),
        )
        for m_label, orig_text, m_text, m_rel in yq_mutations:
            with self.subTest(mutation=m_label):
                self.assertNotEqual(m_text, orig_text)
                m_hits = _find_unpinned_download_steps(
                    load_workflow_yaml(m_text), m_rel
                )
                self.assertGreaterEqual(len(m_hits), 1)
                self.assertTrue(
                    any("pinned curl/wget step modified" in h for h in m_hits),
                    m_hits,
                )

        # Unrelated substrings (`curling`) do not trigger the curl/wget gate.
        benign_wf = load_workflow_yaml(
            "jobs:\n  b:\n    steps:\n      - name: Check\n"
            "        run: echo 'curling check'\n"
        )
        self.assertEqual(
            _find_unpinned_download_steps(benign_wf, "benign.yml"), []
        )
