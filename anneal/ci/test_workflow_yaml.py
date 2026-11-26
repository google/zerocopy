# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exercise workflow YAML decoding and supply-chain/policy checks."""

import hashlib
import json
from pathlib import Path
import re
import tempfile
import tomllib
import unittest
from unittest import mock

import yaml

from workflow_yaml import load_workflow_yaml


REPO_ROOT = Path(__file__).resolve().parents[2]
WORKFLOWS_DIR = REPO_ROOT / ".github" / "workflows"
ACTIONS_DIR = REPO_ROOT / ".github" / "actions"
PUBLISH_ACTION = ACTIONS_DIR / "publish-github-release" / "action.yml"
CHECKS_TOML = REPO_ROOT / "ci" / "checks.toml"
STATUS_FN_RE = re.compile(
    r"\b(?:cancelled|failure|success|always)\s*\(", re.IGNORECASE
)
EXTGLOB_RE = re.compile(r"[?!+*@]\(")
DOWNLOAD_TOOL_RE = re.compile(r"\b(?:curl|wget)\b", re.IGNORECASE)

# Fail-closed inventory of every workflow/action `run:` step whose YAML
# text literally names `curl` or `wget`, keyed by
# `(relpath, yaml_steps_path, step_key)` and pinned to the SHA-256 of its
# canonical JSON payload (`step` mapping plus enclosing `job_env`,
# `job_defaults`, `job_container`, `top_env`, `top_defaults`, and
# `action_inputs`). Any new or modified step/context fails CI until
# audited and re-pinned here (other fetch tools, external actions, and
# Dockerfiles are outside this lint).
PINNED_DOWNLOAD_STEPS = {
    (
        ".github/workflows/release.yml",
        "root.jobs.anneal-build-archive.steps",
        "name:Check whether GitHub Release already exists",
    ): (
        "35190397ea5f44f37761fe067978abd886c18dd3eca7aad3dbf89663e368d379",
        "GitHub Releases API metadata check: writes JSON to $RUNNER_TEMP "
        "and branches solely on HTTP status code.",
    ),
    (
        ".github/workflows/release.yml",
        "root.jobs.anneal-host-archive.steps",
        "id:check_hosted",
    ): (
        "674d00092be2fac63a420fe4846b558efa752776ea0f9b589cfc0cca384063f4",
        "GitHub Releases API metadata check: writes JSON to $RUNNER_TEMP "
        "and checks digest via jq.",
    ),
    (
        ".github/workflows/release.yml",
        "root.jobs.anneal-host-archive.steps",
        "name:Stage draft prerelease, verify server SHA-256, and "
        "publish atomically",
    ): (
        "67af27ffc20d29f0816ffd67883cf1a878c22259ed891b2cddcb5ed6f28a96ea",
        "Upload only (--upload-file): publishes local sha256sum-verified "
        "archive to draft release and verifies server digest.",
    ),
    (
        ".github/workflows/release.yml",
        "root.jobs.anneal-qualify-package.steps",
        "name:Check Anneal publishing environment protections",
    ): (
        "d25c93beecbe469c99c0fff9b5b234cb3a23501525226a0d78de5c782900307a",
        "GitHub Environments API metadata query: pipes JSON solely to jq -e.",
    ),
    (
        ".github/workflows/roll-pinned-toolchain-versions.yml",
        "root.jobs.roll_semver_baseline.steps",
        "id:advance",
    ): (
        "5c890feccac8eec866a2f2ab74e5eae2b80bfb5595136efdcea1aad1cbd6ab73",
        "crates.io sparse index JSON query: parses semver and cksum via jq.",
    ),
    (
        ".github/workflows/roll-pinned-toolchain-versions.yml",
        "root.jobs.roll_kani.steps",
        "index:1",
    ): (
        "1d987fe451dfa0e995fcd4eed4755f83aced2cb933012cea156865ae99199899",
        "Pin-hash computation: hashes $KANI_BUNDLE_TMP via sha256sum to "
        "write ci/pins/kani-pin.toml and removes it without unpacking.",
    ),
}

# The ci-core cutover retired `.github/actions/install-yq`. Its last audited
# text stays here, pinned to its audited digest, so the action-level mutation
# cases below (`env:`, `shell:`, `working-directory:`, and action `inputs:`)
# keep exercising the pin lint.
YQ_ACTION_FIXTURE_REL = ".github/actions/install-yq/action.yml"
YQ_ACTION_FIXTURE_PIN = {
    (
        YQ_ACTION_FIXTURE_REL,
        "root.runs.steps",
        "name:Install pinned yq binary",
    ): (
        "5279508731dd6b02640802e3920a27bfe9015a1a346b9f320201ef9d5bae484b",
        "Binary download: curl -o ${tmp_bin} verified by "
        "sha256sum --check --strict against ${YQ_SHA256} before install.",
    ),
}
YQ_ACTION_FIXTURE = r'''# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

name: Install yq
description: Install a pinned, SHA-256-verified mikefarah/yq binary without Go module/sumdb network calls

runs:
  using: composite
  steps:
    - name: Install pinned yq binary
      shell: bash
      env:
        YQ_VERSION: v4.44.1
        YQ_SHA256: 6dc2d0cd4e0caca5aeffd0d784a48263591080e4a0895abe69f3a76eb50d1ba3
      run: |
        set -euo pipefail

        if [ "$(uname -s)" != "Linux" ] || [ "$(uname -m)" != "x86_64" ]; then
          echo "Unsupported platform for pinned yq binary: $(uname -s)/$(uname -m)" >&2
          exit 1
        fi

        # Reuse an already-installed binary only if its SHA-256 matches the
        # pinned release digest verbatim.
        if existing_yq="$(command -v yq 2>/dev/null || true)" && [ -n "${existing_yq}" ]; then
          if printf '%s  %s\n' "${YQ_SHA256}" "${existing_yq}" | sha256sum --check --status; then
            "${existing_yq}" --version
            exit 0
          fi
        fi

        url="https://github.com/mikefarah/yq/releases/download/${YQ_VERSION}/yq_linux_amd64"
        tmp_bin="$(mktemp "${RUNNER_TEMP}/yq.download.XXXXXX")"
        trap 'rm -f -- "${tmp_bin}"' EXIT

        curl --proto '=https' --tlsv1.2 -fsSL \
          --retry 5 --retry-all-errors --retry-delay 2 \
          -o "${tmp_bin}" "${url}"
        printf '%s  %s\n' "${YQ_SHA256}" "${tmp_bin}" | sha256sum --check --strict

        if [ -w /usr/local/bin ]; then
          install -m 0755 "${tmp_bin}" /usr/local/bin/yq
        else
          sudo install -m 0755 "${tmp_bin}" /usr/local/bin/yq
        fi
        /usr/local/bin/yq --version
'''


class WorkflowYamlTests(unittest.TestCase):
    def test_scalars_keep_their_lexical_values(self):
        self.assertEqual(
            load_workflow_yaml("on: off\nyes: no\nnull: ~\nnumber: 42\nflag: true\n"),
            {"on": "off", "yes": "no", "null": "~", "number": "42", "flag": "true"},
        )

    def test_decoding_leaves_workflow_shape_validation_to_consumers(self):
        self.assertEqual(load_workflow_yaml("[1, 2]\n"), ["1", "2"])
        self.assertEqual(load_workflow_yaml("uses: 42\n"), {"uses": "42"})
        self.assertIsNone(load_workflow_yaml(""))

    def test_anchors_share_decoded_values_without_cycles(self):
        decoded = load_workflow_yaml(
            "events: &events [push, pull_request]\n"
            "on: *events\n"
            "first: &step {uses: owner/action@abc}\n"
            "second: *step\n"
        )
        self.assertEqual(decoded["on"], ["push", "pull_request"])
        self.assertIs(decoded["on"], decoded["events"])
        self.assertIs(decoded["first"], decoded["second"])

    def test_duplicate_keys_fail_at_every_mapping_depth(self):
        for text in (
            "on: push\non: pull_request\n",
            "jobs: {build: {}, build: {}}\n",
            "step: {uses: owner/action@v1, uses: owner/action@v2}\n",
            "x: &key jobs\n*key: one\njobs: two\n",
        ):
            with self.subTest(text=text):
                with self.assertRaisesRegex(yaml.YAMLError, "duplicate workflow key"):
                    load_workflow_yaml(text)

    def test_sequence_and_mapping_keys_fail_with_focused_errors(self):
        for text in ("? [a, b]\n: value\n", "? {a: b}\n: value\n"):
            with self.subTest(text=text):
                with self.assertRaisesRegex(yaml.YAMLError, "keys must be scalars"):
                    load_workflow_yaml(text)

    def test_merge_keys_are_rejected_even_when_quoted(self):
        for text in (
            "base: &base {uses: owner/action@v1}\nstep: {<<: *base}\n",
            "step: {'<<': {uses: owner/action@v1}}\n",
            "step: {\"<<\": {uses: owner/action@v1}}\n",
        ):
            with self.subTest(text=text):
                with self.assertRaisesRegex(yaml.YAMLError, "merge keys"):
                    load_workflow_yaml(text)

    def test_yaml_parser_rejects_direct_and_indirect_cycles(self):
        for text in (
            "value: &cycle [*cycle]\n",
            "value: &cycle {back: *cycle}\n",
            "value: &cycle [{back: *cycle}]\n",
        ):
            with self.subTest(text=text):
                with self.assertRaisesRegex(yaml.YAMLError, "recursive node"):
                    load_workflow_yaml(text)

    def test_python_tags_cannot_construct_objects_or_execute_payloads(self):
        with tempfile.TemporaryDirectory(prefix="anneal-yaml-tags-") as directory:
            sentinel = Path(directory) / "executed"
            payload = f"__import__('pathlib').Path({str(sentinel)!r}).touch()"
            text = (
                "value: !!python/object/apply:builtins.eval\n"
                f"  - {json.dumps(payload)}\n"
            )
            self.assertEqual(load_workflow_yaml(text), {"value": [payload]})
            self.assertFalse(sentinel.exists())
        self.assertEqual(
            load_workflow_yaml("value: !!python/name:os.system ''\n"),
            {"value": ""},
        )

    def test_malformed_yaml_and_multiple_documents_are_rejected(self):
        for text in ("on: [\n", "on: push\n---\non: pull_request\n"):
            with self.subTest(text=text):
                with self.assertRaises(yaml.YAMLError):
                    load_workflow_yaml(text)


def _iter_gha_expressions(text):
    """Yield `(start, end, body)` for `${{ ... }}` expressions."""
    i = 0
    n = len(text)
    while True:
        start = text.find("${{", i)
        if start < 0:
            return
        j = start + 3
        in_sq = False
        while j < n:
            ch = text[j]
            if ch == "'":
                if in_sq and j + 1 < n and text[j + 1] == "'":
                    j += 2
                    continue
                in_sq = not in_sq
            elif not in_sq and text[j : j + 2] == "}}":
                yield start, j + 2, text[start + 3 : j]
                i = j + 2
                break
            j += 1
        else:
            yield start, n, text[start + 3 :]
            return


def _iter_env_mappings(node, path="root"):
    """Yield `(path, env_dict)` pairs from a decoded workflow/action YAML."""
    if isinstance(node, dict):
        env_val = node.get("env")
        if isinstance(env_val, dict):
            yield f"{path}.env", env_val
        for key, value in node.items():
            yield from _iter_env_mappings(value, f"{path}.{key}")
    elif isinstance(node, list):
        for idx, item in enumerate(node):
            yield from _iter_env_mappings(item, f"{path}[{idx}]")


def _strip_gha_string_literals(expr):
    """Replace single-quoted string literals in a GHA expression with ''."""
    out = []
    i = 0
    n = len(expr)
    in_sq = False
    while i < n:
        ch = expr[i]
        if ch == "'":
            if in_sq and i + 1 < n and expr[i + 1] == "'":
                i += 2
                continue
            in_sq = not in_sq
            out.append("'")
        elif not in_sq:
            out.append(ch)
        i += 1
    return "".join(out)


def _find_env_status_violations(doc, label):
    violations = []
    for loc, env_map in _iter_env_mappings(doc):
        for key, value in env_map.items():
            if not isinstance(value, str):
                continue
            if any(
                STATUS_FN_RE.search(_strip_gha_string_literals(expr))
                for _s, _e, expr in _iter_gha_expressions(value)
            ):
                violations.append(f"{label} {loc}.{key}: {value!r}")
    return violations


def _is_minimatch_glob_pattern(pattern):
    """Return True if `pattern` uses Minimatch magic or extended globs."""
    return (
        pattern.startswith("!")
        or any(ch in pattern for ch in ("*", "?", "[", "{"))
        or EXTGLOB_RE.search(pattern) is not None
    )


def _find_download_artifact_pattern_violations(doc, label):
    violations = []

    def walk(node, loc):
        if isinstance(node, dict):
            uses = node.get("uses")
            if (
                isinstance(uses, str)
                and uses.split("@", 1)[0].lower() == "actions/download-artifact"
            ):
                with_map = node.get("with")
                if isinstance(with_map, dict):
                    with_lower = {
                        str(k).lower(): v for k, v in with_map.items()
                    }
                    if "pattern" in with_lower:
                        merge_mult = str(
                            with_lower.get("merge-multiple", "false")
                        ).lower()
                        pattern = str(with_lower["pattern"])
                        if merge_mult != "true" and _is_minimatch_glob_pattern(
                            pattern
                        ):
                            violations.append(
                                f"{label} {loc}: download-artifact uses "
                                f"pattern={pattern!r} with merge-multiple!=true"
                            )
            for key, value in node.items():
                walk(value, f"{loc}.{key}")
        elif isinstance(node, list):
            for idx, item in enumerate(node):
                walk(item, f"{loc}[{idx}]")

    walk(doc, "root")
    return violations


def _step_pin_key(step, idx):
    step_id = step.get("id")
    if isinstance(step_id, str) and step_id:
        return f"id:{step_id}"
    step_name = step.get("name")
    if isinstance(step_name, str) and step_name:
        return f"name:{step_name}"
    return f"index:{idx}"


def _step_pin_digest(
    step,
    job_ctx,
    top_env,
    top_defaults,
    action_inputs,
):
    """Return canonical SHA-256 over a pinned step and enclosing context."""
    job_env, job_defaults, job_container = job_ctx
    payload = {
        "action_inputs": action_inputs,
        "job_container": job_container,
        "job_defaults": job_defaults,
        "job_env": job_env,
        "step": step,
        "top_defaults": top_defaults,
        "top_env": top_env,
    }
    canon = json.dumps(
        payload, sort_keys=True, ensure_ascii=True, separators=(",", ":")
    )
    return hashlib.sha256(canon.encode("utf-8")).hexdigest()


def _find_unpinned_download_steps(doc, label, matched_keys=None):
    """Fail closed on any unpinned or modified `curl`/`wget` usage."""
    violations = []
    seen_in_doc = set()
    top_env = doc.get("env") if isinstance(doc, dict) else None
    top_defaults = doc.get("defaults") if isinstance(doc, dict) else None
    action_inputs = doc.get("inputs") if isinstance(doc, dict) else None

    def walk(node, loc, job_ctx):
        if isinstance(node, dict):
            for key, value in node.items():
                child_loc = f"{loc}.{key}"
                if key == "steps" and isinstance(value, list):
                    for idx, step in enumerate(value):
                        step_loc = f"{child_loc}[{idx}]"
                        if isinstance(step, dict):
                            run_script = step.get("run")
                            if (
                                isinstance(run_script, str)
                                and DOWNLOAD_TOOL_RE.search(run_script)
                            ):
                                step_key = _step_pin_key(step, idx)
                                pin_id = (label, child_loc, step_key)
                                if pin_id in seen_in_doc:
                                    violations.append(
                                        f"{label} {step_loc}: duplicate "
                                        f"curl/wget step key {step_key!r}"
                                    )
                                else:
                                    seen_in_doc.add(pin_id)
                                    expected = PINNED_DOWNLOAD_STEPS.get(
                                        pin_id
                                    )
                                    actual_sha = _step_pin_digest(
                                        step,
                                        job_ctx,
                                        top_env,
                                        top_defaults,
                                        action_inputs,
                                    )
                                    if expected is None:
                                        violations.append(
                                            f"{label} {step_loc}: unpinned "
                                            f"curl/wget step ({step_key})"
                                        )
                                    elif actual_sha != expected[0]:
                                        violations.append(
                                            f"{label} {step_loc}: pinned "
                                            "curl/wget step modified "
                                            f"(expected sha256 {expected[0]}, "
                                            f"got {actual_sha})"
                                        )
                                    elif matched_keys is not None:
                                        matched_keys.add(pin_id)
                            for s_k, s_v in step.items():
                                if s_k != "run":
                                    walk(s_v, f"{step_loc}.{s_k}", job_ctx)
                        else:
                            walk(step, step_loc, job_ctx)
                else:
                    if isinstance(key, str) and DOWNLOAD_TOOL_RE.search(key):
                        violations.append(
                            f"{label} {loc}: unpinned curl/wget reference in "
                            f"mapping key {key!r}"
                        )
                    next_job_ctx = (
                        (
                            value.get("env"),
                            value.get("defaults"),
                            value.get("container"),
                        )
                        if loc == "root.jobs" and isinstance(value, dict)
                        else job_ctx
                    )
                    walk(value, child_loc, next_job_ctx)
        elif isinstance(node, list):
            for idx, item in enumerate(node):
                walk(item, f"{loc}[{idx}]", job_ctx)
        elif isinstance(node, str) and DOWNLOAD_TOOL_RE.search(node):
            violations.append(
                f"{label} {loc}: unpinned curl/wget reference outside "
                f"step.run: {node!r}"
            )

    walk(doc, "root", (None, None, None))
    return violations


def _find_unmounted_local_uses(
    doc, label, repo_root: Path, mounted_resolved: set[Path]
):
    violations = []

    def walk(node, loc):
        if isinstance(node, dict):
            uses = node.get("uses")
            if isinstance(uses, str) and uses.startswith("./"):
                target = repo_root / uses[2:].rstrip("/")
                if target.suffix in (".yml", ".yaml"):
                    candidates = (target,)
                else:
                    candidates = (
                        target / "action.yml",
                        target / "action.yaml",
                    )
                if not any(
                    c.resolve() in mounted_resolved for c in candidates
                ):
                    violations.append(
                        f"{label} {loc}: local uses {uses!r} does not "
                        "resolve to an audited YAML target"
                    )
            for key, value in node.items():
                walk(value, f"{loc}.{key}")
        elif isinstance(node, list):
            for idx, item in enumerate(node):
                walk(item, f"{loc}[{idx}]")

    walk(doc, "root")
    return violations


class WorkflowPolicyLintTests(unittest.TestCase):
    def _mounted_yaml_targets(
        self, workflows_dir=WORKFLOWS_DIR, actions_dir=ACTIONS_DIR
    ):
        workflows = sorted(
            [
                *workflows_dir.glob("*.yml"),
                *workflows_dir.glob("*.yaml"),
            ]
        )
        self.assertTrue(
            workflows, f"expected workflow YAML files under {workflows_dir}"
        )
        actions = sorted(
            {
                *actions_dir.rglob("action.yml"),
                *actions_dir.rglob("action.yaml"),
            }
        )
        if actions_dir == ACTIONS_DIR:
            self.assertIn(
                PUBLISH_ACTION,
                actions,
                f"missing composite action {PUBLISH_ACTION}",
            )
        return [*workflows, *actions]

    def test_workflows_forbid_status_functions_in_env(self):
        violations = []
        for path in self._mounted_yaml_targets():
            doc = load_workflow_yaml(path.read_text(encoding="utf-8"))
            rel = path.relative_to(REPO_ROOT).as_posix()
            violations.extend(_find_env_status_violations(doc, rel))
        self.assertEqual(violations, [])

        for bad_expr in (
            "cancelled()",
            "Cancelled()",
            "failure()",
            "FAILURE()",
            "success()",
            "always()",
            "ALWAYS()",
            "format('{0}', success())",
            "format('failure() ok {0}', cancelled())",
        ):
            for scope, yaml_text in (
                ("workflow", f"env:\n  BAD: ${{{{ {bad_expr} }}}}\n"),
                (
                    "job",
                    "jobs:\n  b:\n    env:\n"
                    f"      BAD: ${{{{ {bad_expr} }}}}\n",
                ),
                (
                    "step",
                    "jobs:\n  b:\n    steps:\n      - name: s\n"
                    f"        env:\n          BAD: ${{{{ {bad_expr} }}}}\n",
                ),
            ):
                with self.subTest(expr=bad_expr, scope=scope):
                    hits = _find_env_status_violations(
                        load_workflow_yaml(yaml_text), "synthetic.yml"
                    )
                    self.assertEqual(len(hits), 1, yaml_text)

        safe_wf = load_workflow_yaml(
            "env:\n"
            '  OK: "${{ format(\'failure() was reported: {0}\', '
            'github.ref) }}"\n'
        )
        self.assertEqual(_find_env_status_violations(safe_wf, "safe.yml"), [])

    def test_workflows_forbid_wildcard_download_artifact_pattern(self):
        violations = []
        for path in self._mounted_yaml_targets():
            doc = load_workflow_yaml(path.read_text(encoding="utf-8"))
            rel = path.relative_to(REPO_ROOT).as_posix()
            violations.extend(
                _find_download_artifact_pattern_violations(doc, rel)
            )
        self.assertEqual(violations, [])

        for bad_pat in (
            "'{plan-a1,img-meta-*}'",
            "'img-meta-?'",
            "'shard-[01]'",
            "'+(plan-a|plan-b)'",
            "'@(a|b)'",
            "'!exclude-me'",
        ):
            bad_wf = load_workflow_yaml(
                "jobs:\n  gate:\n    steps:\n"
                "      - uses: Actions/Download-Artifact@abc\n"
                f"        with:\n          pattern: {bad_pat}\n"
                "          merge-multiple: false\n          path: meta-in\n"
            )
            self.assertEqual(
                len(_find_download_artifact_pattern_violations(bad_wf, "b")),
                1,
                bad_pat,
            )

        for good_yaml in (
            "jobs:\n  gate:\n    steps:\n"
            "      - uses: actions/download-artifact@abc\n"
            "        with:\n          name: plan-a1\n          path: meta-in\n",
            "jobs:\n  gate:\n    steps:\n"
            "      - uses: actions/download-artifact@abc\n"
            "        with:\n          pattern: 'img-meta-*'\n"
            "          Merge-Multiple: 'True'\n          path: meta-in\n",
        ):
            self.assertEqual(
                _find_download_artifact_pattern_violations(
                    load_workflow_yaml(good_yaml), "good.yml"
                ),
                [],
            )

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

    def test_checks_toml_mounts_audited_github_yaml_trees(self):
        data = tomllib.loads(CHECKS_TOML.read_text(encoding="utf-8"))
        checks = {c["id"]: c for c in data.get("checks", [])}
        self.assertIn("anneal-ci-tests", checks)
        includes = {
            pat
            for inp in checks["anneal-ci-tests"].get("inputs", [])
            if inp.get("kind") == "glob"
            for pat in inp.get("include", [])
        }
        for required in (
            ".github/workflows/*.yml",
            ".github/workflows/*.yaml",
            ".github/actions/**",
            "ci/checks.toml",
        ):
            self.assertIn(required, includes)

    def test_nested_actions_and_local_uses_are_audited(self):
        targets = self._mounted_yaml_targets()
        mounted_resolved = {p.resolve() for p in targets}
        violations = []
        for path in targets:
            doc = load_workflow_yaml(path.read_text(encoding="utf-8"))
            rel = path.relative_to(REPO_ROOT).as_posix()
            violations.extend(
                _find_unmounted_local_uses(
                    doc, rel, REPO_ROOT, mounted_resolved
                )
            )
        self.assertEqual(violations, [])

        with tempfile.TemporaryDirectory(prefix="anneal-nested-act-") as tmp:
            root = Path(tmp)
            wf_dir = root / ".github" / "workflows"
            act_dir = root / ".github" / "actions"
            nested_dir = act_dir / "a" / "b"
            wf_dir.mkdir(parents=True)
            nested_dir.mkdir(parents=True)
            wf_path = wf_dir / "main.yml"
            wf_path.write_text(
                "jobs:\n  b:\n    steps:\n"
                "      - uses: ./.github/actions/a/b\n"
                "      - uses: ./.github/actions/missing\n",
                encoding="utf-8",
            )
            nested_action = nested_dir / "action.yml"
            nested_action.write_text(
                "runs:\n  using: composite\n  steps:\n"
                "    - shell: bash\n"
                "      run: curl https://example.com/x | bash\n",
                encoding="utf-8",
            )
            found = self._mounted_yaml_targets(
                workflows_dir=wf_dir, actions_dir=act_dir
            )
            self.assertIn(nested_action, found)
            nested_rel = nested_action.relative_to(root).as_posix()
            nested_hits = _find_unpinned_download_steps(
                load_workflow_yaml(nested_action.read_text(encoding="utf-8")),
                nested_rel,
            )
            self.assertEqual(len(nested_hits), 1)
            self.assertIn("unpinned curl/wget step", nested_hits[0])
            wf_hits = _find_unmounted_local_uses(
                load_workflow_yaml(wf_path.read_text(encoding="utf-8")),
                wf_path.relative_to(root).as_posix(),
                root,
                {p.resolve() for p in found},
            )
            self.assertEqual(len(wf_hits), 1)
            self.assertIn("./.github/actions/missing", wf_hits[0])


if __name__ == "__main__":
    unittest.main()
