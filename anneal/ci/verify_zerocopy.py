#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Verify every Anneal proof unit under `zerocopy/proofs/` against `zerocopy/src/`."""

import argparse
import collections
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time


VALID_SANDBOXES = ("linux_bwrap", "linux_landlock_seccomp")
ALLOWED_AXIOMS = frozenset({"propext"})
BINDING_DIGEST_FIELDS = (
    ("requestSha256", "request_sha256"),
    ("captureSha256", "capture_sha256"),
    ("specificationManifestSha256", "specification_manifest_sha256"),
    ("modelManifestSha256", "model_manifest_sha256"),
)


def is_safe_relative_filename(raw):
    """Return True if `raw` is a single relative filename with no traversal."""
    if not isinstance(raw, str) or not raw:
        return False
    path = Path(raw)
    return (
        not path.is_absolute()
        and len(path.parts) == 1
        and path.parts[0] not in (".", "..")
    )


def _normalize_instantiations(raw_insts, context):
    """Validate `scope.instantiations` and return unique `(path, args)` keys.

    Empty `args` lists are permitted because `rustc-capture/src/mono.rs` allows
    omitting region-only parameters, while each provided arg must be non-empty.
    """
    if not isinstance(raw_insts, list):
        raise ValueError(f"{context}: scope.instantiations must be a list")
    seen = set()
    normalized = []
    for entry in raw_insts:
        if not isinstance(entry, dict) or set(entry) != {"path", "args"}:
            raise ValueError(
                f"{context}: scope.instantiations entries must have keys "
                f"'path' and 'args': {entry!r}"
            )
        path = entry["path"]
        args = entry["args"]
        if not isinstance(path, str) or not path:
            raise ValueError(
                f"{context}: scope.instantiations path must be a non-empty string"
            )
        if not isinstance(args, list) or not all(
            isinstance(a, str) and a for a in args
        ):
            raise ValueError(
                f"{context}: scope.instantiations args must be a list of "
                "non-empty strings"
            )
        key = (path, tuple(args))
        if key in seen:
            raise ValueError(
                f"{context}: duplicate entry in scope.instantiations: {key!r}"
            )
        seen.add(key)
        normalized.append(key)
    return normalized


def _normalize_selected_unit_scope(scope, context):
    """Validate a `selected_unit` scope dict and return `(roots, inst_keys)`."""
    if not isinstance(scope, dict) or scope.get("kind") != "selected_unit":
        raise ValueError(f"{context}: expected scope.kind == 'selected_unit'")
    extra_keys = set(scope) - {"kind", "roots", "instantiations"}
    if extra_keys:
        raise ValueError(
            f"{context}: unexpected scope keys {sorted(extra_keys)!r}"
        )
    if "roots" not in scope or not isinstance(scope["roots"], list):
        raise ValueError(
            f"{context}: scope.roots must be a list of non-empty strings"
        )
    roots = scope["roots"]
    if not all(isinstance(r, str) and r for r in roots):
        raise ValueError(
            f"{context}: scope.roots entries must be non-empty strings"
        )
    if len(roots) != len(set(roots)):
        raise ValueError(f"{context}: duplicate entry in scope.roots")

    if "instantiations" in scope:
        raw_insts = scope["instantiations"]
    else:
        raw_insts = []
    inst_keys = _normalize_instantiations(raw_insts, context)

    if not roots and not inst_keys:
        raise ValueError(
            f"{context}: scope must contain at least one root or instantiation"
        )
    return list(roots), inst_keys


_MAX_SYMLINK_HOPS = 40


def _reject_symlink_ancestors_in_repo(
    path, label, repo_root=None, *, check_outside_repo=False
):
    """Reject symlinks at `path` or along traversed in-scope prefixes."""
    if path.is_symlink():
        raise RuntimeError(f"symlink disallowed in {label} path: {path}")

    resolved_repo = (
        repo_root.resolve(strict=True) if repo_root is not None else None
    )

    if path.is_absolute():
        resolved_cur = Path(path.anchor).resolve()
        queue = collections.deque(path.parts[1:])
    else:
        resolved_cur = Path.cwd().resolve(strict=True)
        queue = collections.deque(path.parts)

    def parent_in_scope(cur_dir):
        if resolved_repo is None:
            return check_outside_repo
        return cur_dir == resolved_repo or cur_dir.is_relative_to(
            resolved_repo
        )

    # Step component-by-component over a symlink-free `resolved_cur`:
    # reject symlinks at the final target or inside `resolved_repo`, and
    # expand permitted outside-repository symlinks one `readlink` hop at a
    # time so paths entering `resolved_repo` via an external symlink still
    # check every in-repository component while relative and absolute
    # external `--artifacts-dir` paths behave identically.
    hops = 0
    while queue:
        part = queue.popleft()
        if part in ("", "."):
            continue
        if part == "..":
            resolved_cur = resolved_cur.parent
            continue
        candidate = resolved_cur / part
        is_final = not any(p not in ("", ".") for p in queue)
        if candidate.is_symlink():
            if is_final or parent_in_scope(resolved_cur):
                raise RuntimeError(
                    f"symlink disallowed in {label} path: {candidate}"
                )
            hops += 1
            if hops > _MAX_SYMLINK_HOPS:
                raise RuntimeError(
                    f"too many symlink levels in {label} path: {path}"
                )
            target = Path(os.readlink(candidate))
            if target.is_absolute():
                resolved_cur = Path(target.anchor).resolve()
                for p in reversed(target.parts[1:]):
                    queue.appendleft(p)
            else:
                for p in reversed(target.parts):
                    queue.appendleft(p)
            continue
        resolved_cur = candidate


def _validate_real_directory(path, label, repo_root=None):
    """Verify `path` is a real directory without symlink traversal."""
    _reject_symlink_ancestors_in_repo(
        path, label, repo_root=repo_root, check_outside_repo=(repo_root is None)
    )
    if not path.is_dir():
        raise RuntimeError(f"invalid {label} directory: {path}")
    return path.resolve(strict=True)


def discover_units(proofs_dir, src_dir, selected_units=None, *, repo_root=None):
    """Validate `proofs_dir` hygiene and return ordered unit pairs."""
    proofs_dir = _validate_real_directory(
        proofs_dir, "proofs", repo_root=repo_root
    )
    resolved_src = _validate_real_directory(
        src_dir, "src", repo_root=repo_root
    )
    lib_rs = resolved_src / "lib.rs"
    if lib_rs.is_symlink() or not lib_rs.is_file():
        raise RuntimeError(f"zerocopy crate root missing: {lib_rs}")

    discovered = {}
    for entry in sorted(proofs_dir.iterdir(), key=lambda p: p.name):
        if entry.is_symlink():
            raise RuntimeError(f"symlink disallowed in proofs tree: {entry}")
        if entry.is_file():
            if entry.name != "README.md":
                raise RuntimeError(f"unexpected top-level proofs file: {entry}")
            continue
        if not entry.is_dir():
            raise RuntimeError(f"unexpected entry in proofs tree: {entry}")

        unit_files = []
        for child in sorted(entry.iterdir(), key=lambda p: p.name):
            if child.is_symlink():
                raise RuntimeError(f"symlink disallowed in proof unit: {child}")
            if not child.is_file():
                raise RuntimeError(f"unexpected non-file entry in proof unit: {child}")
            unit_files.append(child.name)

        req_path = entry / "request.json"
        if not req_path.is_file():
            raise RuntimeError(f"missing request.json in proof unit: {entry}")
        request = json.loads(req_path.read_text(encoding="utf-8"))

        compilation = request.get("compilation")
        if not isinstance(compilation, dict):
            raise RuntimeError(f"{entry.name}: missing compilation table")
        source_root = compilation.get("source_root")
        if not isinstance(source_root, str) or not source_root or Path(source_root).is_absolute():
            raise RuntimeError(
                f"{entry.name}: compilation.source_root must be a relative path: {source_root!r}"
            )
        try:
            unit_src = (entry / source_root).resolve(strict=True)
        except OSError as exc:
            raise RuntimeError(
                f"{entry.name}: source_root {source_root!r} cannot resolve: {exc}"
            ) from exc
        if unit_src != resolved_src:
            raise RuntimeError(
                f"{entry.name}: source_root {source_root!r} does not resolve to {resolved_src}"
            )

        try:
            _normalize_selected_unit_scope(request.get("scope"), entry.name)
        except ValueError as exc:
            raise RuntimeError(str(exc)) from exc

        proof = request.get("proof")
        if not isinstance(proof, dict) or proof.get("source_root") != ".":
            raise RuntimeError(f"{entry.name}: proof.source_root must be '.'")
        sources = proof.get("sources")
        if not isinstance(sources, list) or not sources:
            raise RuntimeError(f"{entry.name}: proof.sources must be non-empty")

        declared_files = {"request.json"}
        for source in sources:
            filename = source.get("path") if isinstance(source, dict) else None
            if not is_safe_relative_filename(filename) or not filename.endswith(".lean"):
                raise RuntimeError(f"{entry.name}: invalid Lean source path {filename!r}")
            if not (entry / filename).is_file():
                raise RuntimeError(f"{entry.name}: missing declared source {filename}")
            declared_files.add(filename)

        unexpected = set(unit_files) - declared_files
        if unexpected:
            raise RuntimeError(
                f"{entry.name}: undeclared files in proof unit: {sorted(unexpected)}"
            )
        discovered[entry.name] = (entry, request)

    if not discovered:
        raise RuntimeError(f"no proof units discovered under {proofs_dir}")
    if selected_units:
        unique_units = list(dict.fromkeys(selected_units))
        missing = [name for name in unique_units if name not in discovered]
        if missing:
            raise RuntimeError(f"requested proof unit(s) not found: {missing}")
        return [discovered[name] for name in unique_units]
    return [discovered[name] for name in sorted(discovered)]


_SELECTED_BODY_KEYS = frozenset(("def_id", "path", "body_index"))


def _is_nonneg_int(val):
    return not isinstance(val, bool) and isinstance(val, int) and val >= 0


def _is_valid_selected_bodies(selected):
    """Return True iff `selected` is a non-empty list of SelectedBody dicts."""
    if not isinstance(selected, list) or not selected:
        return False
    for entry in selected:
        if not isinstance(entry, dict):
            return False
        if set(entry.keys()) != _SELECTED_BODY_KEYS:
            return False
        if not _is_nonneg_int(entry["def_id"]):
            return False
        if not isinstance(entry["path"], str) or not entry["path"]:
            return False
        if not _is_nonneg_int(entry["body_index"]):
            return False
    return True


def validate_receipt(
    unit_name,
    returncode,
    stdout_text,
    stderr_text,
    expected_roots,
    expected_instantiations=None,
):
    """Fail closed unless `cargo-anneal verify` emitted an untainted passing receipt."""
    try:
        exp_roots, exp_inst_keys = _normalize_selected_unit_scope(
            {
                "kind": "selected_unit",
                "roots": expected_roots,
                "instantiations": (
                    expected_instantiations
                    if expected_instantiations is not None
                    else []
                ),
            },
            f"{unit_name} expected",
        )
    except ValueError as exc:
        raise RuntimeError(str(exc)) from exc

    try:
        receipt = json.loads(stdout_text)
    except json.JSONDecodeError as exc:
        raise RuntimeError(
            f"{unit_name}: invalid JSON receipt (exit {returncode}): {exc}\n"
            f"stdout={stdout_text[:800]}\nstderr={stderr_text[:800]}"
        ) from exc
    if not isinstance(receipt, dict):
        raise RuntimeError(f"{unit_name}: receipt JSON must be an object")

    failures = []
    if returncode != 0:
        failures.append(f"exit={returncode}")
    if receipt.get("schema_version") != 3:
        failures.append(f"schema_version={receipt.get('schema_version')!r}")
    if receipt.get("status") != "selected_unit_verified":
        failures.append(f"status={receipt.get('status')!r}")
    if receipt.get("taint_reasons") != []:
        failures.append(f"taint_reasons={receipt.get('taint_reasons')!r}")
    if "tainted" in receipt:
        failures.append("unexpected legacy tainted key")
    if "sorry_declarations" in receipt:
        failures.append(f"sorry_declarations={receipt.get('sorry_declarations')!r}")
    if receipt.get("elaboration_sandbox") not in VALID_SANDBOXES:
        failures.append(f"elaboration_sandbox={receipt.get('elaboration_sandbox')!r}")
    deferred = receipt.get("deferred", [])
    if not isinstance(deferred, list):
        failures.append(f"deferred={deferred!r}")
    elif "hostile Lean elaborator effects" in deferred:
        failures.append("hostile Lean elaborator effects deferred")

    scope = receipt.get("scope")
    try:
        actual_roots, actual_inst_keys = _normalize_selected_unit_scope(
            scope, f"{unit_name} receipt"
        )
    except ValueError as exc:
        failures.append(f"scope mismatch ({exc}): {scope!r}")
    else:
        if set(actual_roots) != set(exp_roots) or set(actual_inst_keys) != set(
            exp_inst_keys
        ):
            failures.append(f"scope mismatch: {scope!r}")

    selected = receipt.get("selected")
    if not _is_valid_selected_bodies(selected):
        failures.append(f"selected={selected!r}")

    audit = receipt.get("audit")
    if not isinstance(audit, dict):
        failures.append("missing audit object")
    else:
        if audit.get("exactType") is not True:
            failures.append(f"audit.exactType={audit.get('exactType')!r}")
        if audit.get("checkedAlternateProofs") != 0:
            failures.append(
                f"audit.checkedAlternateProofs={audit.get('checkedAlternateProofs')!r}"
            )
        axioms = audit.get("axioms")
        if not isinstance(axioms, list) or not set(axioms).issubset(ALLOWED_AXIOMS):
            failures.append(f"disallowed audit.axioms={axioms!r}")
        if audit.get("canonicalRoot") != "Trusted.MirSemantics.UnitTheorem":
            failures.append(f"canonicalRoot={audit.get('canonicalRoot')!r}")
        bindings = audit.get("bindings")
        if not isinstance(bindings, dict):
            failures.append("missing audit.bindings")
        else:
            for bind_key, top_key in BINDING_DIGEST_FIELDS:
                top_val = receipt.get(top_key)
                if (
                    not isinstance(top_val, str)
                    or not top_val
                    or bindings.get(bind_key) != top_val
                ):
                    failures.append(f"binding digest mismatch on {bind_key}")

    if failures:
        detail = "; ".join(failures)
        raise RuntimeError(
            f"{unit_name}: verification failed ({detail}): {json.dumps(receipt)[:2500]}"
        )
    return receipt


def env_tool(names, bundle_suffix=None):
    for name in names:
        raw = os.environ.get(name, "")
        if raw:
            return Path(raw)
    bundle = os.environ.get("ANNEAL_TEST_INSTALL_ROOT", "")
    if bundle and bundle_suffix:
        return Path(bundle) / bundle_suffix
    return None


def discover_local_defaults(anneal_root):
    raw_target = os.environ.get("CARGO_TARGET_DIR", "")
    target_dir = Path(raw_target) if raw_target.strip() else anneal_root / "target"
    cli = target_dir / "debug/cargo-anneal"
    capture_candidates = [
        target_dir / "debug/anneal-rustc-capture",
        anneal_root / "trusted/rustc-capture/target/debug/anneal-rustc-capture",
    ]
    capture = next((p for p in capture_candidates if p.is_file()), None)
    home = Path.home()
    lean_candidates = [
        home / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean",
    ]
    raw_xdg_cache = os.environ.get("XDG_CACHE_HOME", "")
    cache_home = Path(raw_xdg_cache) if raw_xdg_cache.strip() else home / ".cache"
    tc_root = cache_home / "anneal/toolchain"
    if tc_root.is_dir():
        entries = []
        try:
            tc_entries = list(tc_root.iterdir())
        except OSError:
            tc_entries = []
        for entry in tc_entries:
            try:
                mtime = entry.stat().st_mtime
            except OSError:
                continue
            entries.append((mtime, entry))
        for _, entry in sorted(entries, key=lambda item: item[0], reverse=True):
            cand = entry / "lean/bin/lean"
            if cand.is_file():
                lean_candidates.insert(0, cand)
    lean = next((p for p in lean_candidates if p.is_file()), None)
    sysroot = None
    try:
        out = subprocess.check_output(
            ["rustup", "run", "nightly-2026-05-31", "rustc", "--print", "sysroot"],
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
        if out and Path(out).is_dir():
            sysroot = Path(out)
    except Exception:
        pass
    return {
        "cli": cli if cli.is_file() else None,
        "capture": capture,
        "sysroot": sysroot,
        "lean": lean,
    }


def verify_unit(arguments, unit_dir, request, artifacts_root):
    cmd = [
        str(arguments.cli),
        "verify",
        "--request",
        str(unit_dir / "request.json"),
        "--capture",
        str(arguments.capture),
        "--sysroot",
        str(arguments.sysroot),
        "--lean",
        str(arguments.lean),
        "--artifacts",
        str(artifacts_root / unit_dir.name),
    ]
    started = time.monotonic()
    proc = subprocess.run(
        cmd,
        cwd=unit_dir,
        capture_output=True,
        text=True,
        timeout=arguments.timeout,
        check=False,
    )
    elapsed = round(time.monotonic() - started, 3)
    (artifacts_root / f"{unit_dir.name}.stdout").write_text(proc.stdout, encoding="utf-8")
    (artifacts_root / f"{unit_dir.name}.stderr").write_text(proc.stderr, encoding="utf-8")
    receipt = validate_receipt(
        unit_dir.name,
        proc.returncode,
        proc.stdout,
        proc.stderr,
        request["scope"]["roots"],
        expected_instantiations=request["scope"].get("instantiations"),
    )
    return unit_dir.name, {
        "status": receipt["status"],
        "scope": receipt["scope"],
        "axioms": receipt["audit"]["axioms"],
        "elaboration_sandbox": receipt["elaboration_sandbox"],
        "selected": receipt["selected"],
        "request_sha256": receipt["request_sha256"],
        "capture_sha256": receipt["capture_sha256"],
        "specification_manifest_sha256": receipt["specification_manifest_sha256"],
        "timing_ms": receipt.get("timing_ms", {}),
        "wall_seconds": elapsed,
    }


def run_suite(arguments, work_dir, *, repo_root=None):
    units = discover_units(
        arguments.proofs_dir,
        arguments.src_dir,
        selected_units=arguments.unit or None,
        repo_root=repo_root,
    )
    workers = max(1, min(arguments.jobs, len(units)))
    started = time.monotonic()
    results = {}
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [
            pool.submit(verify_unit, arguments, unit_dir, request, work_dir)
            for unit_dir, request in units
        ]
        for future in futures:
            name, record = future.result()
            results[name] = record
    summary = {
        "units": results,
        "unit_count": len(results),
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    (work_dir / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, indent=2))
    return summary


def main(argv=None):
    anneal_root = Path(__file__).resolve().parents[1]
    repo_root = anneal_root.parent

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--proofs-dir",
        type=Path,
        default=repo_root / "zerocopy/proofs",
        help="Path to zerocopy/proofs directory",
    )
    parser.add_argument(
        "--src-dir",
        type=Path,
        default=repo_root / "zerocopy/src",
        help="Path to zerocopy/src directory",
    )
    parser.add_argument(
        "--unit",
        action="append",
        default=[],
        help="Verify only the named proof unit subdirectory (repeatable)",
    )
    parser.add_argument(
        "--artifacts-dir",
        type=Path,
        help="New directory retaining complete verification artifacts and summary",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=min(4, max(1, os.cpu_count() or 1)),
        help="Maximum concurrent `cargo-anneal verify` workers",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=600,
        help="Per-unit `cargo-anneal verify` timeout in seconds",
    )
    for name in ("cli", "capture", "sysroot", "lean"):
        parser.add_argument(f"--{name}", type=Path)

    arguments = parser.parse_args(argv)
    env_fallbacks = {
        "cli": env_tool(["ANNEAL_CLI", "ANNEAL_TEST_CARGO_ANNEAL"]),
        "capture": env_tool(["ANNEAL_CAPTURE"], "bin/anneal-rustc-capture"),
        "sysroot": env_tool(["ANNEAL_SYSROOT", "ANNEAL_TEST_RUST_SYSROOT"], "rust"),
        "lean": env_tool(["ANNEAL_LEAN"], "lean/bin/lean"),
    }
    for name, fallback in env_fallbacks.items():
        if getattr(arguments, name) is None:
            setattr(arguments, name, fallback)
    if any(getattr(arguments, name) is None for name in env_fallbacks):
        local = discover_local_defaults(anneal_root)
        for name in env_fallbacks:
            if getattr(arguments, name) is None:
                setattr(arguments, name, local[name])
    for required in ("cli", "capture", "sysroot", "lean"):
        value = getattr(arguments, required)
        if value is None:
            parser.error(f"the following arguments are required: --{required}")
        setattr(arguments, required, value.resolve(strict=True))

    arguments.proofs_dir = _validate_real_directory(
        arguments.proofs_dir, "proofs", repo_root=repo_root
    )
    arguments.src_dir = _validate_real_directory(
        arguments.src_dir, "src", repo_root=repo_root
    )

    if arguments.artifacts_dir is not None:
        _reject_symlink_ancestors_in_repo(
            arguments.artifacts_dir, "artifacts", repo_root=repo_root
        )
        arguments.artifacts_dir.mkdir(mode=0o700)
        run_suite(
            arguments,
            arguments.artifacts_dir.resolve(),
            repo_root=repo_root,
        )
    else:
        with tempfile.TemporaryDirectory(
            prefix="anneal-zerocopy-proofs-"
        ) as tmp:
            run_suite(arguments, Path(tmp), repo_root=repo_root)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
