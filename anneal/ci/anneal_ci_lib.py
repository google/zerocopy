# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Shared stdlib-only helpers and test fixtures for Anneal CI scripts."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import tempfile
from typing import Any, Callable, Sequence


VALID_SANDBOXES: tuple[str, ...] = ("linux_bwrap", "linux_landlock_seccomp")
SAFE_GIT_FLAGS: tuple[str, ...] = (
    "-c",
    "core.hooksPath=/dev/null",
    "-c",
    "core.fsmonitor=false",
)
ACTIONS_ENV_TOKENS: tuple[str, ...] = (
    "ACTIONS_CACHE_URL",
    "ACTIONS_RESULTS_URL",
    "ACTIONS_RUNTIME_TOKEN",
    "ACTIONS_RUNTIME_URL",
)
ACTIONS_OIDC_TOKENS: tuple[str, ...] = (
    "ACTIONS_ID_TOKEN_REQUEST_URL",
    "ACTIONS_ID_TOKEN_REQUEST_TOKEN",
)
DEFAULT_TOOL_ENV_SPECS: dict[str, tuple[tuple[str, ...], str | None]] = {
    "cli": (("ANNEAL_CLI", "ANNEAL_TEST_CARGO_ANNEAL"), None),
    "capture": (("ANNEAL_CAPTURE",), "bin/anneal-rustc-capture"),
    "sysroot": (("ANNEAL_SYSROOT", "ANNEAL_TEST_RUST_SYSROOT"), "rust"),
    "lean": (("ANNEAL_LEAN",), "lean/bin/lean"),
}


def strip_actions_env(
    env: dict[str, str] | None = None,
    *,
    include_oidc: bool = False,
) -> dict[str, str]:
    """Return a copy of `env` (or `os.environ`) with Actions creds removed."""
    out = dict(os.environ if env is None else env)
    tokens = ACTIONS_ENV_TOKENS + (ACTIONS_OIDC_TOKENS if include_oidc else ())
    for key in tokens:
        out.pop(key, None)
    return out


def default_anneal_root(script_file: str | Path | None = None) -> Path:
    """Return the `anneal/` root inferred from `script_file` (or this module)."""
    anchor = Path(script_file) if script_file is not None else Path(__file__)
    return anchor.resolve().parent.parent


def ensure_not_symlink(
    path: Path,
    label: str = "path",
    *,
    exc_type: type[Exception] = ValueError,
) -> None:
    """Reject symlink inputs/outputs fail-closed."""
    if path.is_symlink():
        raise exc_type(f"{label} must not be a symlink: {path}")


def is_nonneg_int(val: Any) -> bool:
    """Return True iff `val` is a non-boolean integer `>= 0`."""
    return type(val) is int and val >= 0


def is_exact_int(val: Any, expected: int) -> bool:
    """Return True iff `val` is a non-boolean integer equal to `expected`."""
    return type(val) is int and val == expected


def reject_duplicate_json_keys(
    pairs: list[tuple[str, Any]],
) -> dict[str, Any]:
    """JSON `object_pairs_hook` that rejects duplicate object keys."""
    seen: dict[str, Any] = {}
    for key, val in pairs:
        if key in seen:
            raise ValueError(f"duplicate JSON key {key!r}")
        seen[key] = val
    return seen


def load_strict_json_object(
    path: Path,
    label: str = "JSON file",
) -> dict[str, Any]:
    """Read regular non-symlink `path` as a duplicate-key-free JSON object."""
    if path.is_symlink() or not path.is_file():
        raise RuntimeError(
            f"{label} must be a regular non-symlink file: {path}"
        )
    try:
        text = path.read_text(encoding="utf-8")
        data = json.loads(text, object_pairs_hook=reject_duplicate_json_keys)
    except (OSError, UnicodeDecodeError, ValueError) as exc:
        raise RuntimeError(f"invalid JSON in {label} ({path}): {exc}") from exc
    if not isinstance(data, dict):
        raise RuntimeError(f"{label} must be a JSON object: {path}")
    return data


def sha256_bytes(data: bytes) -> str:
    """Return the lowercase SHA-256 hex digest of `data`."""
    return hashlib.sha256(data).hexdigest()


def sha256_raw_file(
    path: Path,
    *,
    chunk_size: int = 1024 * 1024,
    reject_symlink: bool = False,
    missing_label: str = "file",
    exc_type: type[Exception] = RuntimeError,
) -> bytes:
    """Return the 32-byte SHA-256 digest of `path`, optionally rejecting symlinks."""
    if reject_symlink and (path.is_symlink() or not path.is_file()):
        raise exc_type(f"expected regular file in {missing_label}: {path}")
    h = hashlib.sha256()
    with path.open("rb") as f:
        while chunk := f.read(chunk_size):
            h.update(chunk)
    return h.digest()


def sha256_file(
    path: Path,
    *,
    chunk_size: int = 1024 * 1024,
    reject_symlink: bool = False,
    missing_label: str = "file",
    exc_type: type[Exception] = RuntimeError,
) -> str:
    """Return the lowercase SHA-256 hex digest of `path`."""
    return sha256_raw_file(
        path,
        chunk_size=chunk_size,
        reject_symlink=reject_symlink,
        missing_label=missing_label,
        exc_type=exc_type,
    ).hex()


def atomic_write_bytes(
    path: Path,
    data: bytes,
    *,
    mode: int | None = None,
    exc_type: type[Exception] = ValueError,
) -> None:
    """Atomically write `data` to `path` via fsynced temp file + `os.replace`."""
    ensure_not_symlink(path, "output file", exc_type=exc_type)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp_name = tempfile.mkstemp(
        prefix=f".{path.name}.",
        suffix=".tmp",
        dir=str(path.parent),
    )
    tmp_path = Path(tmp_name)
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(data)
            f.flush()
            if mode is not None:
                os.fchmod(f.fileno(), mode)
            os.fsync(f.fileno())
        os.replace(tmp_path, path)
    except BaseException:
        tmp_path.unlink(missing_ok=True)
        raise


def atomic_write_text(
    path: Path,
    text: str,
    *,
    mode: int | None = None,
    exc_type: type[Exception] = ValueError,
) -> None:
    """Atomically write UTF-8 `text` to `path` via fsynced temp file."""
    atomic_write_bytes(path, text.encode("utf-8"), mode=mode, exc_type=exc_type)


def env_tool(
    names: Sequence[str],
    bundle_suffix: str | None = None,
) -> Path | None:
    """Resolve a tool path from environment variables or `ANNEAL_TEST_INSTALL_ROOT`."""
    for name in names:
        raw = os.environ.get(name, "")
        if raw:
            return Path(raw)
    bundle = os.environ.get("ANNEAL_TEST_INSTALL_ROOT", "")
    if bundle and bundle_suffix:
        return Path(bundle) / bundle_suffix
    return None


def discover_local_defaults(anneal_root: Path) -> dict[str, Path | None]:
    """Discover local Anneal binaries, pinned Lean toolchain, and rustc sysroot."""
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
        entries: list[tuple[float, Path]] = []
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
        cached_lean_candidates = [
            cand
            for _, entry in sorted(entries, key=lambda item: item[0], reverse=True)
            if (cand := entry / "lean/bin/lean").is_file()
        ]
        lean_candidates = cached_lean_candidates + lean_candidates
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


def _pick_existing_file(
    explicit: Path | None,
    candidates: Sequence[Path | None],
) -> Path | None:
    if explicit is not None:
        return explicit.resolve(strict=True)
    for cand in candidates:
        if cand is not None and cand.is_file():
            return cand.resolve(strict=True)
    return None


def _pick_existing_dir(
    explicit: Path | None,
    candidates: Sequence[Path | None],
) -> Path | None:
    if explicit is not None:
        return explicit.resolve(strict=True)
    for cand in candidates:
        if cand is not None and cand.is_dir():
            return cand.resolve(strict=True)
    return None


def discover_tools(
    anneal_root: Path,
    *,
    cli: Path | None = None,
    capture: Path | None = None,
    sysroot: Path | None = None,
    lean: Path | None = None,
    auditor: Path | None = None,
    install_root: Path | None = None,
    target_dir: Path | None = None,
    defaults_fn: Callable[[Path], dict[str, Path | None]] | None = None,
) -> dict[str, Path | None]:
    """Resolve `cli`, `capture`, `sysroot`, `lean`, and `auditor` paths."""
    raw_target = os.environ.get("CARGO_TARGET_DIR", "")
    resolved_target = target_dir or (
        Path(raw_target) if raw_target.strip() else anneal_root / "target"
    )
    defaults = (defaults_fn or discover_local_defaults)(anneal_root)
    inst = install_root.resolve(strict=True) if install_root else None

    return {
        "cli": _pick_existing_file(
            cli,
            [
                resolved_target / "release/cargo-anneal",
                resolved_target / "debug/cargo-anneal",
                defaults.get("cli"),
            ],
        ),
        "capture": _pick_existing_file(
            capture,
            [
                (inst / "bin/anneal-rustc-capture") if inst else None,
                resolved_target / "release/anneal-rustc-capture",
                resolved_target / "debug/anneal-rustc-capture",
                defaults.get("capture"),
            ],
        ),
        "sysroot": _pick_existing_dir(
            sysroot,
            [
                (inst / "rust") if inst else None,
                defaults.get("sysroot"),
            ],
        ),
        "lean": _pick_existing_file(
            lean,
            [
                (inst / "lean/bin/lean") if inst else None,
                defaults.get("lean"),
            ],
        ),
        "auditor": _pick_existing_file(
            auditor,
            [
                resolved_target / "release/anneal-audit",
                resolved_target / "debug/anneal-audit",
            ],
        ),
    }


def resolve_cli_tools(
    anneal_root: Path,
    arguments: Any,
    *,
    names: Sequence[str] = ("cli", "capture", "sysroot", "lean"),
    env_specs: dict[str, tuple[tuple[str, ...], str | None]] | None = None,
    defaults_fn: Callable[[Path], dict[str, Path | None]] | None = None,
) -> dict[str, Path | None]:
    """Populate missing CLI tool attributes via env fallbacks then lazy local defaults."""
    specs = env_specs if env_specs is not None else DEFAULT_TOOL_ENV_SPECS
    resolved: dict[str, Path | None] = {}
    for name in names:
        val = getattr(arguments, name, None)
        if val is None and name in specs:
            env_names, bundle_suffix = specs[name]
            val = env_tool(env_names, bundle_suffix)
        resolved[name] = val

    if any(resolved[name] is None for name in names):
        local = (defaults_fn or discover_local_defaults)(anneal_root)
        for name in names:
            if resolved[name] is None:
                resolved[name] = local.get(name)

    for name in names:
        setattr(arguments, name, resolved[name])
    return resolved


def build_cargo_anneal_verify_cmd(
    *,
    cli: Path,
    request_path: Path,
    capture: Path | None = None,
    sysroot: Path | None = None,
    lean: Path | None = None,
    artifacts_dir: Path | None = None,
    extra_flags: Sequence[str] = (),
) -> list[str]:
    """Construct the canonical `cargo-anneal verify` command line."""
    cmd = [str(cli), "verify", "--request", str(request_path), *extra_flags]
    if capture is not None:
        cmd.extend(["--capture", str(capture)])
    if sysroot is not None:
        cmd.extend(["--sysroot", str(sysroot)])
    if lean is not None:
        cmd.extend(["--lean", str(lean)])
    if artifacts_dir is not None:
        cmd.extend(["--artifacts", str(artifacts_dir)])
    return cmd


def run_cargo_anneal_verify(
    *,
    cli: Path,
    request_path: Path,
    cwd: Path,
    capture: Path | None = None,
    sysroot: Path | None = None,
    lean: Path | None = None,
    artifacts_dir: Path | None = None,
    extra_flags: Sequence[str] = (),
    env: dict[str, str] | None = None,
    strip_actions_creds: bool = True,
    timeout: float = 600.0,
    runner: Callable[..., Any] | None = None,
    log_prefix: Path | None = None,
    label: str = "verify",
) -> tuple[Any, dict[str, Any]]:
    """Run `cargo-anneal verify`, persist optional logs, and decode JSON.

    When `runner` is omitted and `log_prefix` is set, child stdout and stderr
    stream straight to `<log_prefix>.stdout` and `<log_prefix>.stderr` so raw
    diagnostics survive timeouts and UTF-8 decode failures.
    """
    cmd = build_cargo_anneal_verify_cmd(
        cli=cli,
        request_path=request_path,
        capture=capture,
        sysroot=sysroot,
        lean=lean,
        artifacts_dir=artifacts_dir,
        extra_flags=extra_flags,
    )
    child_env = (
        strip_actions_env(env, include_oidc=True)
        if strip_actions_creds
        else env
    )
    if runner is not None:
        proc = runner(cmd, cwd=cwd, env=child_env, timeout=timeout)
        if log_prefix is not None:
            log_prefix.parent.mkdir(parents=True, exist_ok=True)
            Path(f"{log_prefix}.stdout").write_text(proc.stdout, encoding="utf-8")
            Path(f"{log_prefix}.stderr").write_text(proc.stderr, encoding="utf-8")
    elif log_prefix is not None:
        log_prefix.parent.mkdir(parents=True, exist_ok=True)
        stdout_path = Path(f"{log_prefix}.stdout")
        stderr_path = Path(f"{log_prefix}.stderr")
        with stdout_path.open("wb") as out_f, stderr_path.open("wb") as err_f:
            raw_proc = subprocess.run(
                cmd,
                cwd=cwd,
                env=child_env,
                stdout=out_f,
                stderr=err_f,
                timeout=timeout,
                check=False,
            )
        raw_stdout = stdout_path.read_bytes()
        stderr_text = stderr_path.read_text(encoding="utf-8", errors="replace")
        try:
            stdout_text = raw_stdout.decode("utf-8")
        except UnicodeDecodeError as exc:
            stdout_preview = raw_stdout.decode("utf-8", errors="replace")[:800]
            raise RuntimeError(
                f"{label}: invalid UTF-8 receipt stdout "
                f"(exit {raw_proc.returncode}): {exc}\n"
                f"stdout={stdout_preview}\nstderr={stderr_text[:800]}"
            ) from exc
        proc = subprocess.CompletedProcess(
            cmd,
            raw_proc.returncode,
            stdout=stdout_text,
            stderr=stderr_text,
        )
    else:
        raw_proc = subprocess.run(
            cmd,
            cwd=cwd,
            env=child_env,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
        raw_stdout = raw_proc.stdout
        stderr_text = raw_proc.stderr.decode("utf-8", errors="replace")
        try:
            stdout_text = raw_stdout.decode("utf-8")
        except UnicodeDecodeError as exc:
            stdout_preview = raw_stdout.decode("utf-8", errors="replace")[:800]
            raise RuntimeError(
                f"{label}: invalid UTF-8 receipt stdout "
                f"(exit {raw_proc.returncode}): {exc}\n"
                f"stdout={stdout_preview}\nstderr={stderr_text[:800]}"
            ) from exc
        proc = subprocess.CompletedProcess(
            cmd,
            raw_proc.returncode,
            stdout=stdout_text,
            stderr=stderr_text,
        )
    try:
        receipt = json.loads(
            proc.stdout, object_pairs_hook=reject_duplicate_json_keys
        )
    except (ValueError, json.JSONDecodeError) as exc:
        raise RuntimeError(
            f"{label}: invalid JSON receipt (exit {proc.returncode}): {exc}\n"
            f"stdout={proc.stdout[:800]}\nstderr={proc.stderr[:800]}"
        ) from exc
    if not isinstance(receipt, dict):
        raise RuntimeError(f"{label}: receipt JSON must be an object")
    return proc, receipt


def validate_receipt_v3_envelope(
    receipt: dict[str, Any],
    *,
    returncode: int,
    expected_status: str = "selected_unit_verified",
    expected_returncode: int = 0,
    check_deferred: bool = True,
) -> list[str]:
    """Validate common Receipt v3 envelope invariants and return failures."""
    failures: list[str] = []
    if returncode != expected_returncode:
        failures.append(f"exit={returncode}")
    if not is_exact_int(receipt.get("schema_version"), 3):
        failures.append(f"schema_version={receipt.get('schema_version')!r}")
    if receipt.get("status") != expected_status:
        failures.append(f"status={receipt.get('status')!r}")
    if receipt.get("taint_reasons") != []:
        failures.append(f"taint_reasons={receipt.get('taint_reasons')!r}")
    if "tainted" in receipt:
        failures.append("unexpected legacy tainted key")
    if "sorry_declarations" in receipt:
        failures.append(f"sorry_declarations={receipt.get('sorry_declarations')!r}")
    if receipt.get("elaboration_sandbox") not in VALID_SANDBOXES:
        failures.append(f"elaboration_sandbox={receipt.get('elaboration_sandbox')!r}")
    if check_deferred:
        deferred = receipt.get("deferred", [])
        if not isinstance(deferred, list) or not all(
            isinstance(d, str) for d in deferred
        ):
            failures.append(f"deferred={deferred!r}")
        elif "hostile Lean elaborator effects" in deferred:
            failures.append("hostile Lean elaborator effects deferred")
    return failures


def find_workflow_step(
    workflow: dict[str, Any],
    job_id: str,
    *,
    step_id: str | None = None,
    step_name: str | None = None,
) -> dict[str, Any]:
    """Return the unique step in `workflow['jobs'][job_id]['steps']` matching id/name."""
    steps = workflow["jobs"][job_id]["steps"]
    matches = [
        s
        for s in steps
        if (step_id is None or s.get("id") == step_id)
        and (step_name is None or s.get("name") == step_name)
    ]
    if len(matches) != 1:
        raise KeyError(
            f"Expected 1 step in {job_id!r} (id={step_id!r}, name={step_name!r}), "
            f"found {len(matches)}"
        )
    return matches[0]


def load_workflow(path: Path) -> dict[str, Any]:
    """Decode a workflow YAML file via `workflow_yaml.load_workflow_yaml`."""
    from workflow_yaml import load_workflow_yaml

    return load_workflow_yaml(path.read_text(encoding="utf-8"))


class WorkflowRepoFixture:
    """Managed temporary Git / workflow workspace for `anneal/ci` unit tests."""

    def __init__(self, *, prefix: str = "anneal-ci-wf-") -> None:
        self._prefix = prefix
        self._tmp: tempfile.TemporaryDirectory[str] | None = None
        self.root: Path = Path()

    def __enter__(self) -> WorkflowRepoFixture:
        self._tmp = tempfile.TemporaryDirectory(prefix=self._prefix)
        self.root = Path(self._tmp.name)
        return self

    def __exit__(self, exc_type: Any, exc: Any, tb: Any) -> None:
        if self._tmp is not None:
            self._tmp.cleanup()
            self._tmp = None

    def path(self, rel: str | Path) -> Path:
        p = Path(rel)
        return p if p.is_absolute() else self.root / p

    def mkdir(self, rel: str | Path) -> Path:
        p = self.path(rel)
        p.mkdir(parents=True, exist_ok=True)
        return p

    def write_file(self, rel: str | Path, content: str) -> Path:
        p = self.path(rel)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
        return p

    def write_bytes(self, rel: str | Path, data: bytes) -> Path:
        p = self.path(rel)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(data)
        return p

    def write_executable(self, rel: str | Path, content: str) -> Path:
        p = self.write_file(rel, content)
        p.chmod(p.stat().st_mode | stat.S_IRWXU)
        return p

    def git(
        self,
        cwd: Path,
        *args: str,
        check: bool = True,
        env: dict[str, str] | None = None,
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["git", *SAFE_GIT_FLAGS, *args],
            cwd=cwd,
            env=env,
            capture_output=True,
            text=True,
            check=check,
        )

    def init_repo(
        self,
        rel: str | Path = "repo",
        *,
        initial_branch: str | None = None,
        bare: bool = False,
        user_name: str = "Test",
        user_email: str = "test@example.com",
    ) -> Path:
        repo = self.path(rel)
        if bare:
            repo.parent.mkdir(parents=True, exist_ok=True)
            self.git(self.root, "init", "--bare", "-q", str(repo))
            return repo
        repo.mkdir(parents=True, exist_ok=True)
        init_args = ["init", "-q"]
        if initial_branch is not None:
            init_args.extend(["-b", initial_branch])
        self.git(repo, *init_args)
        self.git(repo, "config", "user.name", user_name)
        self.git(repo, "config", "user.email", user_email)
        return repo

    def clone_repo(
        self,
        remote: Path | str,
        dest: str | Path,
        *,
        branch: str | None = None,
        depth: int | None = None,
        quiet: bool = True,
    ) -> Path:
        dest_path = self.path(dest)
        dest_path.parent.mkdir(parents=True, exist_ok=True)
        cmd = ["clone"]
        if quiet:
            cmd.append("--quiet")
        if depth is not None:
            cmd.append(f"--depth={depth}")
        if branch is not None:
            cmd.extend(["--branch", branch])
        remote_arg = remote.as_uri() if isinstance(remote, Path) else str(remote)
        cmd.extend([remote_arg, str(dest_path)])
        self.git(self.root, *cmd)
        return dest_path

    def commit_all(
        self,
        repo: Path,
        message: str = "init",
        *,
        paths: Sequence[str] = (".",),
    ) -> str:
        self.git(repo, "add", "--", *paths)
        self.git(repo, "commit", "-qm", message)
        return self.git(repo, "rev-parse", "HEAD").stdout.strip()

    def run_bash(
        self,
        script: str,
        *,
        cwd: Path | None = None,
        env: dict[str, str] | None = None,
        shell: str = "bash",
        strict: bool = True,
    ) -> subprocess.CompletedProcess[str]:
        if shell == "bash":
            cmd = ["bash", "--noprofile", "--norc"]
            if strict:
                cmd.extend(["-eo", "pipefail"])
            cmd.extend(["-c", script])
        else:
            cmd = [shell, "-c", script]
        return subprocess.run(
            cmd,
            cwd=cwd or self.root,
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )

    @staticmethod
    def parse_kv_file(path: Path, *, strict: bool = True) -> dict[str, str]:
        out: dict[str, str] = {}
        for line in path.read_text(encoding="utf-8").splitlines():
            if "=" not in line:
                if strict:
                    raise ValueError(
                        f"malformed key=value line in {path}: {line!r}"
                    )
                continue
            k, v = line.split("=", 1)
            out[k] = v
        return out
