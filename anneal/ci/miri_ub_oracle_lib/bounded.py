# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Bounded subprocess execution with process-group cleanup, and result
classification."""

from __future__ import annotations

from collections.abc import Callable
import json
import os
from pathlib import Path
import re
import signal
import stat
import subprocess
import threading
import time

from .common import (
    CHILD_READ_CHUNK_BYTES, DEFAULT_MAX_MEMORY_MB, MAX_CHILD_OUTPUT_BYTES, STRIPPED_CI_ENV_PREFIXES,
    STRIPPED_CI_ENV_VARS,
)
from .confined_exec import _wrap_with_confinement


def _kill_process_group(proc: subprocess.Popen[bytes]) -> None:
    """Force-terminate a child process and its POSIX process group."""
    if os.name == "posix":
        try:
            os.killpg(proc.pid, signal.SIGKILL)
            return
        except ProcessLookupError:
            return
        except OSError:
            pass
    try:
        proc.kill()
    except OSError:
        pass


def _count_pgid_processes(pgid: int) -> int | None:
    """Count live non-zombie Linux processes in process group `pgid`.

    Returns `None` if `/proc` cannot be enumerated so callers fail closed.
    """
    count = 0
    try:
        entries = os.listdir("/proc")
    except OSError:
        return None
    for name in entries:
        if not name.isdigit():
            continue
        try:
            stat = Path(f"/proc/{name}/stat").read_text(encoding="ascii", errors="ignore")
        except OSError:
            continue
        rparen = stat.rfind(")")
        if rparen < 0:
            continue
        fields = stat[rparen + 2 :].split()
        if len(fields) < 3:
            continue
        state = fields[0]
        if state == "Z":
            continue
        try:
            if int(fields[2]) == pgid:
                count += 1
        except ValueError:
            continue
    return count


class _CancelToken:
    """Thread-safe atomic cancellation state and active-child killer registry.

    Serializing cancellation and child registration under one lock closes the
    race where Ctrl-C/SIGTERM arrives after a worker starts `Popen` and before
    it registers its PGID killer: a late `register()` observes `_cancelled`
    atomically, kills the child immediately, and raises `KeyboardInterrupt`.
    """

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._cancelled = False
        self._killers: dict[int, Callable[[], None]] = {}
        self._next_id = 0

    def check_cancelled(self) -> None:
        with self._lock:
            if self._cancelled:
                raise KeyboardInterrupt("oracle run cancelled")

    def register(self, kill_fn: Callable[[], None]) -> int:
        with self._lock:
            if self._cancelled:
                cancelled_now = True
                tok = -1
            else:
                cancelled_now = False
                self._next_id += 1
                tok = self._next_id
                self._killers[tok] = kill_fn
        if cancelled_now:
            kill_fn()
            raise KeyboardInterrupt("oracle run cancelled")
        return tok

    def unregister(self, tok: int) -> None:
        if tok < 0:
            return
        with self._lock:
            self._killers.pop(tok, None)

    def cancel_and_kill_all(self) -> None:
        with self._lock:
            self._cancelled = True
            killers = list(self._killers.values())
        for killer in killers:
            try:
                killer()
            except Exception:  # noqa: BLE001
                pass


def _sanitize_detail(
    text: str, *tmp_paths: Path | None, max_len: int = 240
) -> str:
    """Normalize temporary paths out of diagnostic strings for determinism."""
    out = text
    for p in tmp_paths:
        if p is not None:
            out = out.replace(str(p), "<tmp>")
    out = re.sub(r"/[^\s:'\"]*anneal-miri-[^\s:'\"/]+", "<tmp>", out)
    return out[:max_len]


def run_bounded(
    cmd: list[str],
    *,
    env: dict[str, str],
    timeout_secs: int,
    max_memory_mb: int = DEFAULT_MAX_MEMORY_MB,
    max_output_bytes: int = MAX_CHILD_OUTPUT_BYTES,
    confinement: str = "eval",
    max_procs: int | None = None,
    max_tasks: int | None = None,
    read_only_paths: tuple[Path, ...] = (),
    read_only_exec_paths: tuple[Path, ...] = (),
    read_write_paths: tuple[Path, ...] = (),
    prepend_ld_library_path: Path | None = None,
    export_src: Path | None = None,
    export_dst: Path | None = None,
    cancel_token: _CancelToken | None = None,
) -> tuple[int | str, str, str, float]:
    """Run a child process with timeout, Landlock/seccomp/rlimit confinement, and bounded pipes.

    `RLIMIT_FSIZE` does not cap pipe writes, so stdout and stderr are drained
    incrementally into fixed-size buffers. Exceeding `max_output_bytes` on
    either stream kills the child process group immediately and returns
    `("output_limit", ...)` so callers classify overflow as `tool_error`.
    """
    if cancel_token is not None:
        cancel_token.check_cancelled()
    t0 = time.monotonic()
    bounded_cmd = _wrap_with_confinement(
        cmd,
        timeout_secs=timeout_secs,
        max_memory_mb=max_memory_mb,
        confinement=confinement,
        read_only_paths=read_only_paths,
        read_only_exec_paths=read_only_exec_paths,
        read_write_paths=read_write_paths,
        prepend_ld_library_path=prepend_ld_library_path,
        export_src=export_src,
        export_dst=export_dst,
        max_tasks=max_tasks,
        parent_pid=os.getpid(),
    )
    if cancel_token is not None:
        cancel_token.check_cancelled()
    try:
        proc = subprocess.Popen(
            bounded_cmd,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env,
            start_new_session=(os.name == "posix"),
        )
    except OSError as exc:
        return "os_error", "", str(exc), time.monotonic() - t0

    out_buf = bytearray()
    err_buf = bytearray()
    overflowed = threading.Event()
    done = threading.Event()
    kill_lock = threading.Lock()
    reaped = False

    def _kill_if_unreaped() -> None:
        with kill_lock:
            if not reaped:
                _kill_process_group(proc)

    cancel_reg: int | None = None
    if cancel_token is not None:
        try:
            cancel_reg = cancel_token.register(_kill_if_unreaped)
        except BaseException:
            with kill_lock:
                reaped = True
            try:
                proc.wait(timeout=5.0)
            except subprocess.TimeoutExpired:
                pass
            if proc.stdout is not None:
                proc.stdout.close()
            if proc.stderr is not None:
                proc.stderr.close()
            raise

    def _drain(stream, buf: bytearray) -> None:
        try:
            while True:
                chunk = stream.read(CHILD_READ_CHUNK_BYTES)
                if not chunk:
                    break
                remaining = max_output_bytes - len(buf)
                if len(chunk) > remaining:
                    if remaining > 0:
                        buf.extend(chunk[:remaining])
                    overflowed.set()
                    _kill_if_unreaped()
                    break
                buf.extend(chunk)
        except OSError:
            pass
        finally:
            try:
                stream.close()
            except OSError:
                pass

    def _wait_child() -> None:
        try:
            # Wait without reaping (`WNOWAIT`) so `proc.pid` stays pinned in the
            # kernel PID table until all synchronized `os.killpg` calls finish.
            if (
                os.name == "posix"
                and hasattr(os, "waitid")
                and hasattr(os, "P_PID")
                and hasattr(os, "WEXITED")
                and hasattr(os, "WNOWAIT")
            ):
                try:
                    os.waitid(os.P_PID, proc.pid, os.WEXITED | os.WNOWAIT)
                except ChildProcessError:
                    pass
            else:
                proc.wait()
        finally:
            done.set()

    assert proc.stdout is not None and proc.stderr is not None
    t_out = threading.Thread(target=_drain, args=(proc.stdout, out_buf), daemon=True)
    t_err = threading.Thread(target=_drain, args=(proc.stderr, err_buf), daemon=True)
    t_wait = threading.Thread(target=_wait_child, daemon=True)
    timed_out = False
    proc_limit_exceeded = False
    # In `capture` mode, `--_confined-exec` stays in the PGID as a lightweight
    # `PR_SET_PDEATHSIG` supervisor alongside up to `max_procs` capture tasks.
    pgid_cap = (
        max_procs + (1 if confinement == "capture" else 0)
        if max_procs is not None
        else None
    )
    try:
        t_out.start()
        t_err.start()
        t_wait.start()

        deadline = t0 + timeout_secs
        poll_secs = 0.02 if pgid_cap is not None else 0.05
        while not done.is_set():
            if overflowed.is_set():
                _kill_if_unreaped()
                break
            if pgid_cap is not None:
                proc_count = _count_pgid_processes(proc.pid)
                if proc_count is None or proc_count > pgid_cap:
                    proc_limit_exceeded = True
                    _kill_if_unreaped()
                    break
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                timed_out = True
                _kill_if_unreaped()
                break
            done.wait(timeout=min(poll_secs, remaining))
    finally:
        # Always terminate any lingering descendants (including on
        # KeyboardInterrupt or SIGTERM) while `proc.pid` is still pinned
        # (unreaped), then mark `reaped = True` under `kill_lock` before
        # calling `proc.wait()` so no `killpg` can race with PID recycling.
        _kill_if_unreaped()
        if t_wait.is_alive():
            t_wait.join(timeout=5.0)
        _kill_if_unreaped()
        with kill_lock:
            reaped = True
        if cancel_token is not None and cancel_reg is not None:
            cancel_token.unregister(cancel_reg)
        try:
            proc.wait(timeout=5.0)
        except subprocess.TimeoutExpired:
            pass
        if t_out.is_alive():
            t_out.join(timeout=5.0)
        if t_err.is_alive():
            t_err.join(timeout=5.0)

    out = bytes(out_buf).decode("utf-8", errors="replace")
    err = bytes(err_buf).decode("utf-8", errors="replace")
    elapsed = time.monotonic() - t0
    if proc_limit_exceeded:
        return "process_limit", out, err, elapsed
    if overflowed.is_set():
        return "output_limit", out, err, elapsed
    if timed_out:
        return "timeout", out, err, elapsed
    return proc.returncode, out, err, elapsed


def classify_eval_result(
    rc: int | str,
    stdout: str,
    stderr: str,
    *,
    expect_valid: bool,
) -> tuple[str, str | None, str | None]:
    """Cross-check `anneal-mir-eval --json` exit code and structured outcome.

    Recognizes the documented pre-evaluation refusal path where `cmd_eval`
    rejects a program during configuration (e.g., Profile v2 with a big-endian
    target) by exiting with status 3, empty stdout, and a single
    `unsupported program: <reason>` stderr line. Any other non-JSON output or
    exit-code/JSON mismatch fails closed as `tool_error`.
    """
    if not isinstance(rc, int):
        return "tool_error", str(rc), (stderr or stdout)[-300:] or None

    if rc == 3 and not stdout.strip():
        err_lines = [line.strip() for line in stderr.splitlines() if line.strip()]
        if (
            len(err_lines) == 1
            and err_lines[0].startswith("unsupported program:")
        ):
            reason = err_lines[0].removeprefix("unsupported program:").strip()
            if reason:
                return "eval_fail_closed", "pre_eval_unsupported", reason

    try:
        payload = json.loads(stdout)
    except json.JSONDecodeError as exc:
        return "tool_error", "invalid_eval_json", f"rc={rc}: {exc}"

    if not isinstance(payload, dict) or not isinstance(payload.get("outcome"), dict):
        return "tool_error", "missing_outcome", f"rc={rc}"

    outcome = payload["outcome"]
    kind = outcome.get("kind")
    val = outcome.get("value")

    if rc == 0 and kind == "returned" and isinstance(val, dict):
        term_kind = val.get("kind")
        if term_kind == "returned":
            if expect_valid:
                return "accepted_valid", None, None
            return "unsound_accept", "returned", None
        if term_kind == "unwound":
            if expect_valid:
                return "eval_fail_closed", "unexpected_unwind", "unwound (panic)"
            return "unsound_accept", "unwound", "unwound (panic)"
        return "tool_error", "unknown_terminal_kind", repr(term_kind)

    if rc == 2 and kind == "fault" and isinstance(val, dict):
        if val.get("kind") == "undefined":
            reason = str(val.get("reason", ""))
            return "caught_ub", None, reason
        return "tool_error", "rc2_non_undefined", repr(val)

    if rc == 3 and kind == "fault" and isinstance(val, dict):
        if val.get("kind") == "unsupported":
            reason = str(val.get("reason", ""))
            return "eval_fail_closed", "eval_unsupported", reason
        return "tool_error", "rc3_non_unsupported", repr(val)

    if rc == 3 and kind == "out_of_fuel":
        return "eval_fail_closed", "out_of_fuel", "out of fuel"

    if rc == 4 and kind == "aborted":
        if expect_valid:
            return (
                "eval_fail_closed",
                "unexpected_abort",
                "aborted (UnwindAction::Terminate)",
            )
        return (
            "unsound_accept",
            "aborted",
            "aborted (UnwindAction::Terminate)",
        )

    return (
        "tool_error",
        "eval_rc_outcome_mismatch",
        f"rc={rc}, outcome.kind={kind!r}, stderr={stderr[-200:]!r}",
    )


def sanitized_child_env() -> dict[str, str]:
    """Return a child environment with GitHub Actions credentials stripped.

    `anneal-mir-eval` lives under `tools/` (outside `trusted/`), so CI policy
    requires scrubbing Actions cache/runtime tokens before executing it.
    Applying the same scrubber to capture keeps both child paths uniform and
    leaves the `--_confined-exec` trampoline's loader environment clean (any
    caller-controlled sysroot library path is injected only inside confinement
    immediately before the final target `execve`).
    """
    return {
        key: value
        for key, value in os.environ.items()
        if key not in STRIPPED_CI_ENV_VARS
        and not key.startswith(STRIPPED_CI_ENV_PREFIXES)
    }
