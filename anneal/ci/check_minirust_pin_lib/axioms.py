# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""The constructive axiom check (`--check-axioms`)."""

from __future__ import annotations

import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from .common import (
    ALLOWED_CONSTRUCTIVE_AXIOMS, VerificationError, _require_regular_file,
    _resolve_regular_dir, _walk_non_symlink_dirs,
)
from .lean_hygiene import extract_exported_theorems


_NO_AXIOMS_RE = re.compile(
    r"^'([^']+)'\s+does not depend on any axioms\s*$"
)
_DEPENDS_ON_AXIOMS_RE = re.compile(
    r"^'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]\s*$"
)
_DEPENDS_ON_AXIOMS_START_RE = re.compile(
    r"^'([^']+)'\s+depends on axioms:\s*\[(.*)$"
)


def parse_print_axioms_output(output: str) -> dict[str, list[str]]:
    """Parse Lean 4 `#print axioms` output (including multi-line lists)."""
    result: dict[str, list[str]] = {}
    lines = output.splitlines()
    idx = 0
    while idx < len(lines):
        line = lines[idx].strip()
        m_none = _NO_AXIOMS_RE.match(line)
        if m_none:
            result[m_none.group(1)] = []
            idx += 1
            continue
        m_one = _DEPENDS_ON_AXIOMS_RE.match(line)
        if m_one:
            name = m_one.group(1)
            body = m_one.group(2)
            result[name] = [a.strip() for a in body.split(",") if a.strip()]
            idx += 1
            continue
        m_start = _DEPENDS_ON_AXIOMS_START_RE.match(line)
        if m_start:
            name = m_start.group(1)
            acc = [m_start.group(2)]
            idx += 1
            closed = False
            while idx < len(lines):
                part = lines[idx].strip()
                idx += 1
                if "]" in part:
                    before, _ = part.split("]", 1)
                    acc.append(before)
                    closed = True
                    break
                acc.append(part)
            if not closed:
                raise VerificationError(
                    f"malformed `#print axioms` output for {name!r}: "
                    "missing `]`"
                )
            body = " ".join(acc)
            result[name] = [a.strip() for a in body.split(",") if a.strip()]
            continue
        idx += 1
    return result


def _has_path_separator(spec: str) -> bool:
    if "/" in spec or os.sep in spec:
        return True
    return os.altsep is not None and os.altsep in spec


def _resolve_lean_spec(
    raw: Path | str, label: str, path_env: str | None
) -> list[str]:
    spec = os.fspath(raw)
    if not spec:
        raise VerificationError(
            f"{label} executable does not exist or is not executable: {raw}"
        )
    if not _has_path_separator(spec):
        which_hit = shutil.which(spec, path=path_env)
        if which_hit is None:
            raise VerificationError(
                f"{label} executable does not exist or is not executable: {raw}"
            )
        cand = Path(os.path.abspath(which_hit))
    else:
        cand = Path(os.path.abspath(spec))
    try:
        cand.lstat()
    except OSError as exc:
        raise VerificationError(
            f"{label} executable does not exist or is not executable: {raw}"
        ) from exc
    if not cand.is_file() or not os.access(cand, os.X_OK):
        raise VerificationError(
            f"{label} executable does not exist or is not executable: {raw}"
        )
    return [str(cand)]


def _resolve_lean_command(
    lean_arg: Path | str | None, *, path_env: str | None = None
) -> list[str]:
    """Resolve the Lean executable from `--lean`, `ANNEAL_LEAN`, or `PATH`."""
    effective_path = (
        os.environ.get("PATH") if path_env is None else path_env
    )
    if lean_arg is not None:
        return _resolve_lean_spec(lean_arg, "--lean", effective_path)

    env_lean = os.environ.get("ANNEAL_LEAN")
    if env_lean:
        return _resolve_lean_spec(env_lean, "ANNEAL_LEAN", effective_path)

    which_lean = shutil.which("lean", path=effective_path)
    if which_lean:
        return _resolve_lean_spec(which_lean, "PATH lean", effective_path)

    raise VerificationError(
        "cannot locate a Lean executable; pass --lean <path> or set ANNEAL_LEAN"
    )


def verify_axioms(
    repo_root: Path,
    *,
    lean: Path | str | None = None,
    stage_dir: Path | None = None,
) -> dict[str, list[str]]:
    """Verify exported theorems in `Anneal.MiniRustProof` are constructive."""
    real_root = _resolve_regular_dir(repo_root, "repo root")
    anneal_dir = _walk_non_symlink_dirs(real_root, ("correspondence", "Anneal"))
    proof_file = _require_regular_file(
        anneal_dir / "MiniRustProof.lean",
        "correspondence/Anneal/MiniRustProof.lean",
    )

    theorems = extract_exported_theorems(
        proof_file.read_text(encoding="utf-8"), proof_file
    )
    if not theorems:
        raise VerificationError(
            f"{proof_file}: no exported top-level theorems found for axiom "
            "check"
        )

    env = os.environ.copy()
    for secret_var in (
        "ACTIONS_CACHE_URL",
        "ACTIONS_RESULTS_URL",
        "ACTIONS_RUNTIME_TOKEN",
        "ACTIONS_RUNTIME_URL",
        "ACTIONS_ID_TOKEN_REQUEST_URL",
        "ACTIONS_ID_TOKEN_REQUEST_TOKEN",
        "GITHUB_TOKEN",
        "GH_TOKEN",
    ):
        env.pop(secret_var, None)
    if stage_dir is not None:
        real_stage = _resolve_regular_dir(stage_dir, "stage dir")
        existing = env.get("LEAN_PATH", "")
        env["LEAN_PATH"] = (
            f"{real_stage}{os.pathsep}{existing}"
            if existing
            else str(real_stage)
        )

    cmd_prefix = _resolve_lean_command(lean, path_env=env.get("PATH"))

    with tempfile.TemporaryDirectory(
        prefix="anneal-minirust-axioms-"
    ) as tmp_dir:
        probe_path = Path(tmp_dir) / "CheckMiniRustAxioms.lean"
        probe_lines = ["import Anneal.MiniRustProof"]
        probe_lines.extend(f"#print axioms {thm}" for thm in theorems)
        probe_path.write_text("\n".join(probe_lines) + "\n", encoding="utf-8")

        cmd = [
            *cmd_prefix,
            "-j1",
            "-DElab.async=false",
            "-Ddebug.skipKernelTC=false",
            str(probe_path),
        ]
        try:
            proc = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                env=env,
                timeout=120,
            )
        except subprocess.TimeoutExpired as exc:
            raise VerificationError(
                f"Lean axiom probe timed out after 120s: {cmd}"
            ) from exc

    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout).strip()
        raise VerificationError(
            f"Lean axiom probe failed (exit {proc.returncode}):\n{detail}"
        )

    combined = "\n".join(part for part in (proc.stdout, proc.stderr) if part)
    axioms_map = parse_print_axioms_output(combined)

    failures: list[str] = []
    for thm in theorems:
        if thm not in axioms_map:
            failures.append(
                f"theorem {thm!r} missing from `#print axioms` output"
            )
            continue
        disallowed = sorted(set(axioms_map[thm]) - ALLOWED_CONSTRUCTIVE_AXIOMS)
        if disallowed:
            failures.append(
                f"theorem {thm!r} uses disallowed axiom(s): "
                + ", ".join(disallowed)
            )

    if failures:
        raise VerificationError(
            "Constructive axiom check failed:\n  " + "\n  ".join(failures)
        )

    return {thm: axioms_map[thm] for thm in theorems}
