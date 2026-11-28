# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""The confined child entry point and the wrapper command that launches it."""

from __future__ import annotations

import ctypes
import os
from pathlib import Path
import resource
import signal
import sys
import time

from .common import (
    CAPTURE_MAX_NOFILE, CAPTURE_MAX_TASKS, CI_DIR, DEFAULT_MAX_MEMORY_MB, EVAL_MAX_NOFILE,
    MAX_SUBPROCESS_FSIZE_BYTES, OracleError,
)
from .linux_abi import CONFINEMENT_MODES, _CONFINED_EXEC_FLAG, _MNT_DETACH
from .seccomp import _install_confinement_seccomp
from .capture import _drop_all_capabilities, _enter_capture_namespaces, _export_capture_file
from .landlock import (
    _collect_landlock_read_paths, _install_eval_landlock, _install_landlock,
    _require_confinement_support,
)


def _apply_rlimit(limit_kind: int, requested: int) -> None:
    """Apply a hard+soft rlimit without attempting to raise an existing tighter cap."""
    _, cur_hard = resource.getrlimit(limit_kind)
    if cur_hard != resource.RLIM_INFINITY and cur_hard < requested:
        effective = cur_hard
    else:
        effective = requested
    resource.setrlimit(limit_kind, (effective, effective))


def _run_confined_exec(argv: list[str]) -> int:
    """Single-threaded exec trampoline: install Landlock + seccomp + rlimits, then `execv`."""
    try:
        if len(argv) < 7:
            raise OracleError("malformed --_confined-exec invocation")
        cpu_limit = int(argv[0])
        fsize_limit = int(argv[1])
        as_limit = int(argv[2])
        nofile_limit = int(argv[3])
        mode = argv[4]
        if mode not in CONFINEMENT_MODES:
            raise OracleError(f"invalid --_confined-exec mode: {mode!r}")
        idx = 5
        ro_paths: list[Path] = []
        ro_exec_paths: list[Path] = []
        rw_paths: list[Path] = []
        prepend_ld_paths: list[str] = []
        export_src: Path | None = None
        export_dst: Path | None = None
        max_tasks = CAPTURE_MAX_TASKS
        expected_parent_pid: int | None = None
        while idx < len(argv) and argv[idx] in (
            "--ro",
            "--ro-exec",
            "--rw",
            "--prepend-ld-library-path",
            "--export-src",
            "--export-dst",
            "--max-tasks",
            "--parent-pid",
        ):
            if idx + 1 >= len(argv):
                raise OracleError(f"malformed {argv[idx]} in --_confined-exec")
            if argv[idx] == "--ro":
                ro_paths.append(Path(argv[idx + 1]))
            elif argv[idx] == "--ro-exec":
                ro_exec_paths.append(Path(argv[idx + 1]))
            elif argv[idx] == "--rw":
                rw_paths.append(Path(argv[idx + 1]))
            elif argv[idx] == "--prepend-ld-library-path":
                if not argv[idx + 1]:
                    raise OracleError(
                        "empty --prepend-ld-library-path in --_confined-exec"
                    )
                prepend_ld_paths.append(argv[idx + 1])
            elif argv[idx] == "--export-src":
                export_src = Path(argv[idx + 1])
            elif argv[idx] == "--export-dst":
                export_dst = Path(argv[idx + 1])
            elif argv[idx] == "--max-tasks":
                max_tasks = int(argv[idx + 1])
                if max_tasks <= 0:
                    raise OracleError("invalid --max-tasks in --_confined-exec")
            else:
                expected_parent_pid = int(argv[idx + 1])
                if expected_parent_pid <= 0:
                    raise OracleError("invalid --parent-pid in --_confined-exec")
            idx += 2
        if idx >= len(argv) or argv[idx] != "--":
            raise OracleError("malformed --_confined-exec invocation")
        target_cmd = argv[idx + 1 :]
        if (
            cpu_limit <= 0
            or fsize_limit < 0
            or as_limit <= 0
            or nofile_limit <= 0
            or not target_cmd
        ):
            raise OracleError("invalid --_confined-exec limits or command")
        if mode == "capture" and fsize_limit == 0:
            raise OracleError("capture mode requires positive RLIMIT_FSIZE")
        if mode == "capture" and len(rw_paths) > 1:
            raise OracleError("capture mode supports at most one bounded work directory")
        if (export_src is None) != (export_dst is None):
            raise OracleError("--export-src and --export-dst must be paired")

        libc = ctypes.CDLL(None, use_errno=True)
        libc.prctl.argtypes = [
            ctypes.c_int,
            ctypes.c_ulong,
            ctypes.c_ulong,
            ctypes.c_ulong,
            ctypes.c_ulong,
        ]
        libc.prctl.restype = ctypes.c_int

        if mode == "capture":
            # Always supervise `capture` inside private user/PID/mount/network
            # namespaces. The forked capture child becomes PID 1 of the private
            # PID namespace (so it cannot see or signal peer runner processes,
            # and the Linux kernel atomically SIGKILLs + reaps all descendants
            # before `waitpid` returns on ANY child exit). Any writable work
            # directory is overlaid with a size- and inode-bounded `tmpfs` so
            # sequential file creation cannot fill the host disk, and regular
            # output files are exported only after PID-namespace teardown.
            child_pid_box: list[int] = []

            def _kill_capture_and_exit(
                _signum: int = 0, _frame: object = None
            ) -> None:
                if child_pid_box:
                    try:
                        os.kill(child_pid_box[0], signal.SIGKILL)
                    except OSError:
                        pass
                    try:
                        os.waitpid(child_pid_box[0], 0)
                    except OSError:
                        pass
                try:
                    os.killpg(0, signal.SIGKILL)
                except OSError:
                    pass
                os._exit(128 + int(signal.SIGKILL))

            if expected_parent_pid is not None:
                signal.signal(signal.SIGTERM, _kill_capture_and_exit)
                if libc.prctl(1, int(signal.SIGTERM), 0, 0, 0) != 0:
                    err = ctypes.get_errno()
                    raise OracleError(f"prctl(PR_SET_PDEATHSIG) failed: errno={err}")
                if os.getppid() != expected_parent_pid:
                    os._exit(128 + int(signal.SIGKILL))

            work_dir = rw_paths[0] if rw_paths else None
            cap_ro_exec, cap_ro = _collect_landlock_read_paths(
                Path(target_cmd[0]), ro_paths, ro_exec_paths
            )
            _enter_capture_namespaces(
                work_dir,
                read_only_bind_paths=[p for p, _ in (*cap_ro_exec, *cap_ro)],
            )
            if expected_parent_pid is not None:
                # Writing uid_map/gid_map can clear PR_SET_PDEATHSIG; re-arm.
                if libc.prctl(1, int(signal.SIGTERM), 0, 0, 0) != 0:
                    err = ctypes.get_errno()
                    raise OracleError(
                        f"post-userns prctl(PR_SET_PDEATHSIG) failed: errno={err}"
                    )
                if os.getppid() != expected_parent_pid:
                    os._exit(128 + int(signal.SIGKILL))

            sync_r, sync_w = os.pipe()
            child_pid = os.fork()
            if child_pid == 0:
                try:
                    os.close(sync_w)
                    signal.signal(signal.SIGTERM, signal.SIG_DFL)
                    if libc.prctl(1, int(signal.SIGKILL), 0, 0, 0) != 0:
                        err = ctypes.get_errno()
                        raise OracleError(
                            f"child prctl(PR_SET_PDEATHSIG) failed: errno={err}"
                        )
                    os.set_blocking(sync_r, False)
                    try:
                        if os.read(sync_r, 1) == b"":
                            os._exit(128 + int(signal.SIGKILL))
                    except BlockingIOError:
                        pass
                    os.close(sync_r)
                    _install_landlock(
                        Path(target_cmd[0]),
                        ro_paths,
                        read_only_exec_paths=ro_exec_paths,
                        read_write_paths=rw_paths,
                        allow_proc_self=True,
                        require_truncate_mediation=True,
                    )
                    # Supervisor occupies 1 task slot in shared userns ucounts.
                    _apply_rlimit(resource.RLIMIT_NPROC, max_tasks + 1)
                    _apply_rlimit(resource.RLIMIT_CPU, cpu_limit)
                    _apply_rlimit(resource.RLIMIT_FSIZE, fsize_limit)
                    _apply_rlimit(resource.RLIMIT_AS, as_limit)
                    _apply_rlimit(resource.RLIMIT_NOFILE, nofile_limit)
                    _drop_all_capabilities(libc, drop_bounding=True)
                    exec_env = dict(os.environ)
                    if prepend_ld_paths:
                        prefix = os.pathsep.join(prepend_ld_paths)
                        prev_ld = exec_env.get("LD_LIBRARY_PATH", "")
                        exec_env["LD_LIBRARY_PATH"] = (
                            f"{prefix}{os.pathsep}{prev_ld}"
                            if prev_ld
                            else prefix
                        )
                    _install_confinement_seccomp(confinement=mode)
                    os.execve(target_cmd[0], target_cmd, exec_env)
                except BaseException as exc:  # noqa: BLE001
                    sys.stderr.write(f"confined-exec failed closed: {exc}\n")
                    sys.stderr.flush()
                    os._exit(125)

            os.close(sync_r)
            child_pid_box.append(child_pid)
            try:
                while True:
                    if (
                        expected_parent_pid is not None
                        and os.getppid() != expected_parent_pid
                    ):
                        _kill_capture_and_exit()
                    try:
                        waited_pid, status = os.waitpid(child_pid, os.WNOHANG)
                    except ChildProcessError:
                        os._exit(1)
                    if waited_pid == child_pid:
                        # PID 1 of the private PID namespace has exited, so the
                        # kernel has atomically terminated and reaped every
                        # descendant inside that namespace.
                        if export_src is not None and export_dst is not None:
                            _export_capture_file(export_src, export_dst)
                        if work_dir is not None:
                            try:
                                libc.umount2(os.fsencode(work_dir), _MNT_DETACH)
                            except OSError:
                                pass
                        if os.WIFEXITED(status):
                            os._exit(os.WEXITSTATUS(status))
                        if os.WIFSIGNALED(status):
                            os._exit(128 + os.WTERMSIG(status))
                        os._exit(1)
                    time.sleep(0.02)
            finally:
                try:
                    os.close(sync_w)
                except OSError:
                    pass

        if expected_parent_pid is not None:
            # In `eval` mode, seccomp denies `fork`/`clone`, so direct
            # `PR_SET_PDEATHSIG(SIGKILL)` binds the sole process in the tree.
            if libc.prctl(1, int(signal.SIGKILL), 0, 0, 0) != 0:
                err = ctypes.get_errno()
                raise OracleError(f"prctl(PR_SET_PDEATHSIG) failed: errno={err}")
            if os.getppid() != expected_parent_pid:
                os._exit(128 + int(signal.SIGKILL))
        _install_eval_landlock(Path(target_cmd[0]), ro_paths)
        _apply_rlimit(resource.RLIMIT_CPU, cpu_limit)
        _apply_rlimit(resource.RLIMIT_FSIZE, fsize_limit)
        _apply_rlimit(resource.RLIMIT_AS, as_limit)
        _apply_rlimit(resource.RLIMIT_NOFILE, nofile_limit)
        _drop_all_capabilities(libc, drop_bounding=False)
        exec_env = dict(os.environ)
        if prepend_ld_paths:
            prefix = os.pathsep.join(prepend_ld_paths)
            prev_ld = exec_env.get("LD_LIBRARY_PATH", "")
            exec_env["LD_LIBRARY_PATH"] = (
                f"{prefix}{os.pathsep}{prev_ld}" if prev_ld else prefix
            )
        _install_confinement_seccomp(confinement=mode)
        os.execve(target_cmd[0], target_cmd, exec_env)
    except BaseException as exc:  # noqa: BLE001
        sys.stderr.write(f"confined-exec failed closed: {exc}\n")
        sys.stderr.flush()
        os._exit(125)
    return 125


def _wrap_with_confinement(
    cmd: list[str],
    *,
    timeout_secs: int,
    max_memory_mb: int = DEFAULT_MAX_MEMORY_MB,
    confinement: str = "eval",
    read_only_paths: tuple[Path, ...] = (),
    read_only_exec_paths: tuple[Path, ...] = (),
    read_write_paths: tuple[Path, ...] = (),
    prepend_ld_library_path: Path | None = None,
    export_src: Path | None = None,
    export_dst: Path | None = None,
    max_tasks: int | None = None,
    parent_pid: int | None = None,
) -> list[str]:
    """Wrap child command in our single-threaded Landlock + seccomp + rlimit trampoline.

    Avoids unsafe `preexec_fn` in multi-threaded callers, isolates `capture`
    inside private user/PID/mount/network namespaces with a size- and
    inode-bounded `tmpfs` work dir, enforces Landlock filesystem isolation in
    both `eval` (strictly read-only, no `/proc`) and `capture` (ABI >= 3 with
    truncate mediation, read-only source/sysroot + bounded `tmpfs` work dir),
    enforces default-deny seccomp in both modes, and enforces `RLIMIT_CPU`,
    `RLIMIT_FSIZE`, `RLIMIT_AS`, and `RLIMIT_NOFILE`. Fails closed via
    `OracleError` if confinement is unavailable.
    """
    if confinement not in CONFINEMENT_MODES:
        raise OracleError(f"unsupported confinement mode: {confinement!r}")
    _require_confinement_support(
        max_memory_mb, require_truncate_mediation=(confinement == "capture")
    )
    cpu_limit = max(timeout_secs + 5, 10)
    fsize_limit = 0 if confinement == "eval" else MAX_SUBPROCESS_FSIZE_BYTES
    nofile_limit = EVAL_MAX_NOFILE if confinement == "eval" else CAPTURE_MAX_NOFILE
    extra_args: list[str] = []
    for p in read_only_paths:
        extra_args.extend(["--ro", str(p)])
    for p in read_only_exec_paths:
        extra_args.extend(["--ro-exec", str(p)])
    for p in read_write_paths:
        extra_args.extend(["--rw", str(p)])
    if prepend_ld_library_path is not None:
        extra_args.extend(
            ["--prepend-ld-library-path", str(prepend_ld_library_path)]
        )
    if export_src is not None or export_dst is not None:
        if export_src is None or export_dst is None:
            raise OracleError("export_src and export_dst must both be set")
        extra_args.extend(["--export-src", str(export_src), "--export-dst", str(export_dst)])
    if confinement == "capture":
        eff_tasks = CAPTURE_MAX_TASKS if max_tasks is None else max_tasks
        if isinstance(eff_tasks, bool) or not isinstance(eff_tasks, int) or eff_tasks <= 0:
            raise OracleError(f"invalid max_tasks: {eff_tasks!r}")
        extra_args.extend(["--max-tasks", str(eff_tasks)])
    if parent_pid is not None:
        extra_args.extend(["--parent-pid", str(parent_pid)])
    return [
        sys.executable,
        "-I",
        "-B",
        str(CI_DIR / "run_miri_ub_oracle.py"),
        _CONFINED_EXEC_FLAG,
        str(cpu_limit),
        str(fsize_limit),
        str(max_memory_mb * 1024 * 1024),
        str(nofile_limit),
        confinement,
        *extra_args,
        "--",
        *cmd,
    ]
