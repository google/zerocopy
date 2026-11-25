#!/usr/bin/env bash
#
# Copyright 2025 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -eo pipefail

script_name="ci/check_actions.sh"

links_only=0
if [[ "${CHECK_ACTIONS_LINKS_ONLY:-0}" == "1" ]]; then
    links_only=1
fi
for arg in "$@"; do
    case "$arg" in
        --links-only)
            links_only=1
            ;;
        *)
            echo "$script_name: unknown argument: $arg" >&2
            exit 2
            ;;
    esac
done

if [[ -n "${CHECK_ACTIONS_REPO_ROOT:-}" ]]; then
    cd "$CHECK_ACTIONS_REPO_ROOT"
else
    cd "$(dirname "$0")/.."
fi

if [[ $links_only -eq 0 ]]; then
    # Ensure action-validator is installed (reusing a preinstalled binary on
    # PATH in offline sandboxes).
    export PATH="$HOME/.cargo/bin:$PATH"
    if ! command -v action-validator >/dev/null 2>&1; then
        echo "$script_name: action-validator not found, installing..." >&2
        # Install specific version to ensure reproducibility
        cargo install -q action-validator --version 0.8.0 --locked
    fi
fi

# Files to exclude from validation (e.g., because they are not Actions/Workflows)
# Use relative paths matching `find .github` output
EXCLUDE_FILES=(
    "./.github/ISSUE_TEMPLATE/anneal.yml"
    "./.github/ISSUE_TEMPLATE/customer-request.yml"
    "./.github/ISSUE_TEMPLATE/zerocopy-bug.yml"
    "./.github/ISSUE_TEMPLATE/zerocopy-feature.yml"
    "./.github/dependabot.yml"
)

failed=0

if [[ -L ./.github ]]; then
    echo "$script_name: ❌ Disallowed symlink at ./.github (expected non-symlink directory)" >&2
    exit 1
fi

if [[ ! -d ./.github ]]; then
    echo "$script_name: ❌ Missing .github directory under $(pwd)" >&2
    exit 1
fi

# Reject any non-excluded symlink anywhere under ./.github (including symlinked
# directories such as ./.github/workflows or ./.github/actions, which `find`
# does not traverse, as well as symlinked workflow/action files).
while IFS= read -r -d '' sym; do
    for exclude in "${EXCLUDE_FILES[@]}"; do
        if [[ "$sym" == "$exclude" ]]; then
            continue 2
        fi
    done
    echo "$script_name: ❌ Disallowed symlink under .github (expected non-symlink regular file or directory): $sym" >&2
    failed=1
done < <(find ./.github -type l -print0 | sort -z)

files_to_check=()

# Use process substitution and while loop to handle filenames with spaces robustly
while IFS= read -r -d '' file; do
    # Check if file is in exclusion list
    for exclude in "${EXCLUDE_FILES[@]}"; do
        if [[ "$file" == "$exclude" ]]; then
            continue 2
        fi
    done

    if [[ $links_only -eq 0 ]]; then
        if ! output=$(action-validator "$file" 2>&1); then
            echo "$script_name: ❌ Validation failed for $file" >&2
            echo "$output" | sed "s|^|$script_name:   |" >&2
            failed=1
        fi
    fi

    files_to_check+=("$file")
done < <(find ./.github -type f \( -iname '*.yml' -o -iname '*.yaml' \) -print0 | sort -z)

if [[ ${#files_to_check[@]} -gt 0 ]]; then
    if ! python3 -I -B - "$script_name" "${files_to_check[@]}" <<'PY_EOF'; then
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

SCRIPT_NAME = sys.argv[1]
FILES = sys.argv[2:]
REPO_ROOT = Path.cwd()
REPO_ROOT_RESOLVED = REPO_ROOT.resolve()
FORCE_YQ = os.environ.get("CHECK_ACTIONS_FORCE_YQ") == "1"

_PY_YAML = None
if not FORCE_YQ:
    try:
        import yaml as _yaml_mod  # type: ignore[import-not-found]
        _PY_YAML = _yaml_mod
    except ImportError:
        _PY_YAML = None

_YQ_INFO: str | None = None


def _get_yq_info() -> str:
    """Return `yq` binary path for `mikefarah/yq v4` or raise ValueError."""
    global _YQ_INFO
    if _YQ_INFO is not None:
        return _YQ_INFO
    yq_bin = shutil.which("yq")
    if not yq_bin:
        raise ValueError(
            "neither PyYAML nor `yq` is available to parse workflow YAML"
        )
    try:
        proc = subprocess.run(
            [yq_bin, "--version"],
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        raise ValueError("yq --version timed out") from exc
    combined = f"{proc.stdout}\n{proc.stderr}".lower()
    if "mikefarah" not in combined:
        raise ValueError(
            "unsupported yq binary (does not preserve duplicate keys); "
            "install PyYAML or mikefarah/yq v4"
        )
    _YQ_INFO = yq_bin
    return _YQ_INFO


def _no_dup_json_pairs(pairs: list[tuple[str, object]]) -> dict[str, object]:
    out: dict[str, object] = {}
    for k, v in pairs:
        if k in out:
            raise ValueError(f"duplicate YAML mapping key {k!r}")
        out[k] = v
    return out


def _reject_unexpanded_merge_keys(obj: object, display: str) -> None:
    if isinstance(obj, dict):
        if "<<" in obj:
            raise ValueError(
                f"unexpanded YAML merge key '<<' in {display}"
            )
        for val in obj.values():
            _reject_unexpanded_merge_keys(val, display)
    elif isinstance(obj, list):
        for item in obj:
            _reject_unexpanded_merge_keys(item, display)


def _load_via_pyyaml(text: str, display: str) -> object:
    assert _PY_YAML is not None

    class StrictSafeLoader(_PY_YAML.SafeLoader):
        def __init__(self, stream: object) -> None:
            super().__init__(stream)
            self._active_construct: set[int] = set()

        def construct_object(
            self, node: object, deep: bool = False
        ) -> object:
            nid = id(node)
            if nid in self._active_construct:
                raise _PY_YAML.constructor.ConstructorError(
                    None,
                    None,
                    f"cyclic YAML alias in {display}",
                    getattr(node, "start_mark", None),
                )
            self._active_construct.add(nid)
            try:
                return super().construct_object(node, deep=True)
            finally:
                self._active_construct.discard(nid)

    # Disable YAML 1.1 boolean implicit coercion (`on`, `yes`, `true`, ...)
    # so `on:` stays `"on"` and `true:`/`yes:` never masquerade as `on:`.
    StrictSafeLoader.yaml_implicit_resolvers = {
        first_char: [
            (tag, regex)
            for tag, regex in resolvers
            if tag != "tag:yaml.org,2002:bool"
        ]
        for first_char, resolvers in (
            _PY_YAML.SafeLoader.yaml_implicit_resolvers.items()
        )
    }

    # Track validated MappingNodes on their unflattened `node.value` so chained
    # merges (`&base` -> `&derived` -> step) do not re-scan nodes already
    # mutated in place by `loader.flatten_mapping`.
    validated_nodes: dict[int, object] = {}

    def _check_explicit_dups(
        loader: StrictSafeLoader,
        node: object,
        deep: bool,
        active_nodes: set[int],
    ) -> None:
        node_id = id(node)
        if node_id in active_nodes:
            raise ValueError(f"cyclic YAML merge key in {display}")
        if node_id in validated_nodes:
            return
        active_nodes.add(node_id)
        try:
            seen_raw: set[tuple[object, object]] = set()
            for key_node, val_node in node.value:
                if key_node.tag == "tag:yaml.org,2002:merge":
                    marker: tuple[object, object] = ("merge", "<<")
                    if marker in seen_raw:
                        raise ValueError("duplicate YAML mapping key '<<'")
                    seen_raw.add(marker)
                    if isinstance(val_node, _PY_YAML.MappingNode):
                        _check_explicit_dups(
                            loader, val_node, deep, active_nodes
                        )
                    elif isinstance(val_node, _PY_YAML.SequenceNode):
                        for subnode in val_node.value:
                            if isinstance(subnode, _PY_YAML.MappingNode):
                                _check_explicit_dups(
                                    loader, subnode, deep, active_nodes
                                )
                    continue
                if key_node.tag == "tag:yaml.org,2002:value":
                    marker = (str, "=")
                    if marker in seen_raw:
                        raise ValueError("duplicate YAML mapping key '='")
                    seen_raw.add(marker)
                    continue
                key = loader.construct_object(key_node, deep=deep)
                try:
                    marker = (type(key), key)
                    is_dup = marker in seen_raw
                except TypeError as exc:
                    raise ValueError(
                        f"unhashable YAML key in {display}"
                    ) from exc
                if is_dup:
                    raise ValueError(
                        f"duplicate YAML mapping key {key!r}"
                    )
                seen_raw.add(marker)
            validated_nodes[node_id] = node
        finally:
            active_nodes.discard(node_id)

    def _construct_mapping(
        loader: StrictSafeLoader, node: object, deep: bool = False
    ) -> dict[object, object]:
        # Check explicit mapping keys BEFORE flatten_mapping so valid merge-key
        # overrides (`<<: *d` + explicit `uses:`) succeed while duplicate
        # explicit keys (`uses:` + `uses:`, `<<:` + `<<:`) still fail closed.
        _check_explicit_dups(loader, node, deep, set())
        loader.flatten_mapping(node)
        mapping: dict[object, object] = {}
        for key_node, val_node in node.value:
            key = loader.construct_object(key_node, deep=deep)
            mapping[key] = loader.construct_object(val_node, deep=deep)
        return mapping

    StrictSafeLoader.add_constructor(
        _PY_YAML.resolver.BaseResolver.DEFAULT_MAPPING_TAG,
        _construct_mapping,
    )
    try:
        docs = list(_PY_YAML.load_all(text, Loader=StrictSafeLoader))
    except (_PY_YAML.YAMLError, RecursionError) as exc:
        raise ValueError(f"YAML parse error: {exc}") from exc
    if len(docs) != 1:
        raise ValueError(
            f"expected exactly 1 YAML document, found {len(docs)}"
        )
    return docs[0]


def _yq_eval_int(yq_bin: str, expr: str, path: Path, desc: str) -> int:
    try:
        proc = subprocess.run(
            [yq_bin, "eval", expr, str(path)],
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        raise ValueError(f"yq timed out {desc}") from exc
    if proc.returncode != 0:
        detail = (
            proc.stderr.strip() or proc.stdout.strip() or f"rc={proc.returncode}"
        )
        raise ValueError(f"yq failed while {desc}: {detail}")
    lines = proc.stdout.strip().splitlines()
    if len(lines) != 1:
        raise ValueError(
            f"expected exactly 1 YAML document, found {len(lines)}"
        )
    try:
        return int(lines[0].strip())
    except ValueError as exc:
        raise ValueError(
            f"unexpected yq output while {desc}: {lines[0]!r}"
        ) from exc


def _load_via_yq(path: Path, display: str) -> object:
    yq_bin = _get_yq_info()
    # `mikefarah/yq` collapses duplicate keys with last-key-wins semantics
    # whenever a mapping contains a `<<` merge key (both for duplicate `<<`
    # entries and for duplicate explicit keys alongside `<<`); reject any
    # mapping with repeated keys first so behavior matches `StrictSafeLoader`.
    dup_key_expr = (
        '[.. | select(tag == "!!map") | keys | group_by(.) | map(length) '
        "| max // 0] | max // 0"
    )
    if _yq_eval_int(yq_bin, dup_key_expr, path, "inspecting mapping keys") > 1:
        raise ValueError(f"duplicate YAML mapping key in {display}")
    # `mikefarah/yq` silently truncates recursive aliases instead of failing
    # closed; reject any anchor whose subtree contains an alias to itself
    # before running `explode(.)`.
    cyclic_alias_expr = (
        '[.. | select(anchor != "") | anchor as $a '
        '| .. | select(kind == "alias" and alias == $a)] | length'
    )
    if _yq_eval_int(yq_bin, cyclic_alias_expr, path, "inspecting aliases") > 0:
        raise ValueError(f"cyclic YAML alias in {display}")
    cmd = [yq_bin, "eval", "explode(.)", "-o=json", str(path)]
    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        raise ValueError("yq timed out parsing YAML") from exc
    if proc.returncode != 0:
        detail = proc.stderr.strip() or proc.stdout.strip() or f"rc={proc.returncode}"
        raise ValueError(f"yq failed to parse YAML: {detail}")
    raw = proc.stdout.strip()
    if not raw:
        raise ValueError("empty YAML document")
    try:
        doc = json.loads(raw, object_pairs_hook=_no_dup_json_pairs)
    except json.JSONDecodeError as exc:
        raise ValueError(f"invalid JSON from yq: {exc}") from exc
    _reject_unexpanded_merge_keys(doc, display)
    return doc


_DOC_CACHE: dict[Path, dict[object, object]] = {}


def load_yaml_mapping(path: Path, display: str) -> dict[object, object]:
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"expected non-symlink regular file at {display}")
    resolved = path.resolve()
    if resolved in _DOC_CACHE:
        return _DOC_CACHE[resolved]
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise ValueError(f"cannot read {display}: {exc}") from exc
    doc = (
        _load_via_pyyaml(text, display)
        if _PY_YAML is not None
        else _load_via_yq(path, display)
    )
    if not isinstance(doc, dict):
        raise ValueError(
            f"expected top-level YAML mapping in {display}, got {type(doc).__name__}"
        )
    _DOC_CACHE[resolved] = doc
    return doc


def _extract_workflow_on(doc: dict[object, object], display: str) -> object:
    """Extract top-level `on` trigger as literal string key `'on'`."""
    return doc.get("on")


def _has_workflow_call_trigger(doc: dict[object, object], display: str) -> bool:
    on_val = _extract_workflow_on(doc, display)
    if isinstance(on_val, str):
        return on_val == "workflow_call"
    if isinstance(on_val, list):
        return all(isinstance(item, str) for item in on_val) and (
            "workflow_call" in on_val
        )
    if isinstance(on_val, dict):
        return "workflow_call" in on_val
    return False


def _has_symlink_component(rel_parts: tuple[str, ...]) -> bool:
    cur = REPO_ROOT
    for part in rel_parts:
        cur = cur / part
        if cur.is_symlink():
            return True
    return False


_VALIDATED_ACTIONS: set[Path] = set()
_ACTIVE_ACTIONS: set[Path] = set()
errors: list[str] = []


def err(msg: str) -> None:
    errors.append(msg)


def validate_uses_target(
    raw_target: str,
    *,
    caller: str,
    context: str,
    kind: str,
) -> None:
    stripped = raw_target.strip()
    if stripped != raw_target and stripped.startswith("."):
        err(
            f"Local uses target has leading/trailing whitespace in "
            f"{caller} ({context}): {raw_target!r}"
        )
        return
    if not raw_target.startswith("."):
        return

    # Fail closed on empty segments (`//`) BEFORE stripping any trailing `/`,
    # and require `./...` (or `.`) without `.` or `..` traversal components.
    if "//" in raw_target or not (
        raw_target == "." or raw_target.startswith("./")
    ):
        err(
            f"Local uses target contains invalid path in "
            f"{caller} ({context}): {raw_target}"
        )
        return

    if kind == "job" and raw_target.endswith("/"):
        err(
            f"Local reusable workflow must not end with '/' in "
            f"{caller} ({context}): {raw_target}"
        )
        return

    norm = (
        "."
        if raw_target in (".", "./")
        else (
            raw_target[:-1]
            if (kind == "step" and raw_target.endswith("/"))
            else raw_target
        )
    )
    rel = "" if norm == "." else norm[2:]
    rel_parts = tuple(rel.split("/")) if rel else ()
    if any(part in ("", ".", "..") for part in rel_parts):
        err(
            f"Local uses target contains invalid path in "
            f"{caller} ({context}): {raw_target}"
        )
        return

    if _has_symlink_component(rel_parts):
        err(
            f"Local uses target traverses a symlink in "
            f"{caller} ({context}): {norm}"
        )
        return

    target_path = REPO_ROOT.joinpath(*rel_parts) if rel_parts else REPO_ROOT
    try:
        if not target_path.resolve().is_relative_to(REPO_ROOT_RESOLVED):
            err(
                f"Local uses target escapes repository root in "
                f"{caller} ({context}): {norm}"
            )
            return
    except OSError as exc:
        err(f"Cannot resolve local uses target in {caller} ({context}): {exc}")
        return

    if kind == "job":
        if not norm.startswith("./.github/workflows/"):
            err(
                f"Job-level local uses must target ./.github/workflows/ in "
                f"{caller} ({context}): {norm}"
            )
            return
        wf_rel = norm[len("./.github/workflows/") :]
        if "/" in wf_rel:
            err(
                f"Local reusable workflow must live directly under "
                f"./.github/workflows/ in {caller} ({context}): {norm}"
            )
            return
        if not wf_rel.lower().endswith((".yml", ".yaml")):
            err(
                f"Local reusable workflow must end in .yml or .yaml in "
                f"{caller} ({context}): {norm}"
            )
            return
        if not target_path.is_file() or target_path.is_symlink():
            err(
                f"Missing local reusable workflow in "
                f"{caller} ({context}): {norm}"
            )
            return
        try:
            wf_doc = load_yaml_mapping(target_path, norm)
            has_call = _has_workflow_call_trigger(wf_doc, norm)
        except ValueError as exc:
            err(
                f"Invalid local reusable workflow {norm} referenced in "
                f"{caller} ({context}): {exc}"
            )
            return
        if not has_call:
            err(
                f"Local reusable workflow does not declare 'on: workflow_call' "
                f"in {caller} ({context}): {norm}"
            )
        return

    # `kind == "step"`
    if norm == "./.github/workflows" or norm.startswith(
        "./.github/workflows/"
    ):
        err(
            f"Step-level uses cannot target a reusable workflow in "
            f"{caller} ({context}): {norm}"
        )
        return

    if not target_path.is_dir() or target_path.is_symlink():
        err(
            f"Missing local action target in {caller} ({context}): {norm} "
            "(expected real directory with non-symlink action.yml or "
            "action.yaml)"
        )
        return

    manifest_path: Path | None = None
    for cand_name in ("action.yml", "action.yaml"):
        cand = target_path / cand_name
        if cand.is_symlink():
            err(
                f"Local action manifest is a symlink in "
                f"{caller} ({context}): {norm}/{cand_name}"
            )
            return
        if cand.is_file() and manifest_path is None:
            manifest_path = cand

    if manifest_path is None:
        err(
            f"Missing local action target in {caller} ({context}): {norm} "
            "(expected real directory with non-symlink action.yml or "
            "action.yaml)"
        )
        return

    validate_action_file(manifest_path, f"{norm}/{manifest_path.name}")


def validate_steps_list(
    steps: object, *, caller: str, prefix: str
) -> None:
    if not isinstance(steps, list):
        err(f"Expected '{prefix}' to be a list in {caller}")
        return
    for idx, step in enumerate(steps):
        step_ctx = f"{prefix}[{idx}]"
        if not isinstance(step, dict):
            err(f"Expected {step_ctx} to be a mapping in {caller}")
            continue
        if "uses" in step:
            uses_val = step["uses"]
            if not isinstance(uses_val, str) or not uses_val.strip():
                err(
                    f"Expected {step_ctx}.uses to be a non-empty string in "
                    f"{caller}"
                )
                continue
            validate_uses_target(
                uses_val,
                caller=caller,
                context=f"{step_ctx}.uses",
                kind="step",
            )


def validate_action_file(path: Path, display: str) -> None:
    if path.is_symlink() or not path.is_file():
        err(
            f"Invalid action metadata {display}: "
            f"expected non-symlink regular file at {display}"
        )
        return
    resolved = path.resolve()
    if resolved in _VALIDATED_ACTIONS:
        return
    if resolved in _ACTIVE_ACTIONS:
        err(f"Cyclic composite action reference involving {display}")
        return
    _ACTIVE_ACTIONS.add(resolved)
    try:
        try:
            doc = load_yaml_mapping(path, display)
        except ValueError as exc:
            err(f"Invalid action metadata {display}: {exc}")
            return
        runs = doc.get("runs")
        if not isinstance(runs, dict):
            err(f"Expected 'runs' mapping in action {display}")
            return
        if runs.get("using") == "composite" or "steps" in runs:
            if "steps" not in runs:
                err(f"Composite action {display} is missing 'runs.steps'")
                return
            validate_steps_list(runs["steps"], caller=display, prefix="runs.steps")
    finally:
        _ACTIVE_ACTIONS.discard(resolved)
        _VALIDATED_ACTIONS.add(resolved)


def validate_workflow_file(path: Path, display: str) -> None:
    try:
        doc = load_yaml_mapping(path, display)
        _extract_workflow_on(doc, display)
    except ValueError as exc:
        err(f"Invalid workflow file {display}: {exc}")
        return

    jobs = doc.get("jobs")
    if not isinstance(jobs, dict):
        err(f"Expected 'jobs' mapping in workflow {display}")
        return

    for job_id, job_spec in jobs.items():
        if not isinstance(job_spec, dict):
            err(f"Expected jobs.{job_id} to be a mapping in {display}")
            continue
        if "uses" in job_spec:
            uses_val = job_spec["uses"]
            if not isinstance(uses_val, str) or not uses_val.strip():
                err(
                    f"Expected jobs.{job_id}.uses to be a non-empty string in "
                    f"{display}"
                )
            else:
                validate_uses_target(
                    uses_val,
                    caller=display,
                    context=f"jobs.{job_id}.uses",
                    kind="job",
                )
        if "steps" in job_spec:
            validate_steps_list(
                job_spec["steps"],
                caller=display,
                prefix=f"jobs.{job_id}.steps",
            )


for raw_file in FILES:
    file_path = Path(raw_file)
    norm_rel = (
        raw_file[2:] if raw_file.startswith("./") else raw_file
    )
    parts = Path(norm_rel).parts
    if len(parts) >= 2 and parts[0] == ".github" and parts[1] == "workflows":
        if len(parts) != 3:
            err(
                f"Workflow file must live directly under "
                f"./.github/workflows/: {raw_file}"
            )
        validate_workflow_file(file_path, raw_file)
    elif file_path.name.lower() in ("action.yml", "action.yaml"):
        validate_action_file(file_path, raw_file)
    else:
        try:
            other_doc = load_yaml_mapping(file_path, raw_file)
        except ValueError as exc:
            err(f"Invalid YAML file {raw_file}: {exc}")
            continue
        if "jobs" in other_doc:
            validate_workflow_file(file_path, raw_file)
        elif "runs" in other_doc:
            validate_action_file(file_path, raw_file)
        else:
            err(
                f"Unrecognized non-excluded YAML file under .github "
                f"(expected workflow or action): {raw_file}"
            )

if errors:
    for message in errors:
        print(f"{SCRIPT_NAME}: ❌ {message}", file=sys.stderr)
    sys.exit(1)
PY_EOF
        failed=1
    fi
fi

if [[ $failed -ne 0 ]]; then
    echo "$script_name: One or more files failed validation." >&2
    exit 1
fi
