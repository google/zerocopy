# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Shared imports, workflow paths, pinned-download fixtures, and policy
scanners for the workflow YAML tests."""

import hashlib
import json
from pathlib import Path
import re
import tempfile
import tomllib
from unittest import mock

import yaml

from workflow_yaml import load_workflow_yaml


REPO_ROOT = Path(__file__).resolve().parents[3]
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
