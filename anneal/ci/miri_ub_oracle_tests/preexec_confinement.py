# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Miri UB oracle tests for the threaded runner's `preexec_fn` ban and
confinement wrapping."""

from __future__ import annotations

from .support import (
    CI_DIR,
    oracle,
    os,
    Path,
    subprocess,
    sys,
    tempfile,
)


class PreexecConfinementCases:
    """`ClassificationAndGateTests` methods for the threaded runner's
    `preexec_fn` ban and confinement wrapping."""

    def test_no_preexec_fn_in_threaded_runner_and_confinement_wrapping(self):
        from unittest import mock

        src = (CI_DIR / "run_miri_ub_oracle.py").read_text(encoding="utf-8")
        self.assertNotIn("preexec_fn=", src)
        args = oracle.build_arg_parser().parse_args(
            ["--tier-b", "--capture-bin", "/bin/true", "--eval-bin", "/bin/true"]
        )
        self.assertEqual(args.max_memory_mb, oracle.DEFAULT_MAX_MEMORY_MB)
        self.assertEqual(args.max_total_memory_mb, oracle.DEFAULT_MAX_TOTAL_MEMORY_MB)
        self.assertIsNone(args.workers)
        self.assertGreater(args.max_memory_mb, 0)
        eff_workers, eff_mem = oracle._resolve_worker_memory_budget(
            workers=args.workers,
            max_memory_mb=args.max_memory_mb,
            max_total_memory_mb=args.max_total_memory_mb,
        )
        self.assertGreaterEqual(eff_workers, 1)
        self.assertLessEqual(
            eff_workers * (oracle.CAPTURE_MAX_TASKS * eff_mem + oracle.CAPTURE_MAX_DISK_MB),
            oracle.DEFAULT_MAX_TOTAL_MEMORY_MB,
        )

        # Explicit workers exceeding aggregate capture-task + tmpfs budget fail.
        with self.assertRaises(oracle.OracleError):
            oracle._resolve_worker_memory_budget(
                workers=2, max_memory_mb=1024, max_total_memory_mb=16384
            )
        with self.assertRaises(oracle.OracleError):
            oracle._resolve_worker_memory_budget(
                workers=None, max_memory_mb=2045, max_total_memory_mb=16384
            )
        with self.assertRaises(oracle.OracleError):
            oracle._resolve_worker_memory_budget(
                workers=0, max_memory_mb=1024, max_total_memory_mb=4096
            )
        with self.assertRaises(oracle.OracleError):
            oracle._resolve_worker_memory_budget(
                workers=1, max_memory_mb=1024, max_total_memory_mb=0
            )
        # Capture mode requires Landlock ABI >= 3 for truncate mediation.
        with mock.patch.object(oracle, "_probe_landlock_abi", return_value=2):
            with self.assertRaises(oracle.OracleError):
                oracle._wrap_with_confinement(
                    ["/bin/true"],
                    timeout_secs=10,
                    max_memory_mb=256,
                    confinement="capture",
                )
            with self.assertRaises(oracle.OracleError):
                oracle._install_landlock(
                    Path("/bin/true"), [], require_truncate_mediation=True
                )

        wrapped = oracle._wrap_with_confinement(
            ["/bin/true"], timeout_secs=10, max_memory_mb=256
        )
        self.assertEqual(wrapped[-1], "/bin/true")
        self.assertIn("--", wrapped)
        self.assertIn(oracle._CONFINED_EXEC_FLAG, wrapped)
        self.assertIn(str(256 * 1024 * 1024), wrapped)

        # Non-positive limits and unsupported OS/arch must fail closed.
        for bad in (0, -1):
            with self.assertRaises(oracle.OracleError):
                oracle._wrap_with_confinement(
                    ["/bin/true"], timeout_secs=10, max_memory_mb=bad
                )
        with mock.patch.object(oracle.sys, "platform", "darwin"):
            with self.assertRaises(oracle.OracleError):
                oracle._wrap_with_confinement(
                    ["/bin/true"], timeout_secs=10, max_memory_mb=256
                )
        with mock.patch.object(oracle.platform, "machine", return_value="sparc64"):
            with self.assertRaises(oracle.OracleError):
                oracle._wrap_with_confinement(
                    ["/bin/true"], timeout_secs=10, max_memory_mb=256
                )

        # BPF assembly must succeed on both supported Linux architectures and
        # confinement modes.
        for arch in ("x86_64", "aarch64"):
            for mode in ("eval", "capture"):
                bpf = oracle._build_confinement_seccomp_bpf(arch, confinement=mode)
                self.assertEqual(len(bpf) % 8, 0)

        # Strict `eval` confinement must enforce Landlock (no `/proc`, no
        # unlisted paths, no writes anywhere), default-deny seccomp allowlist
        # (blocking fork, threads, setsid, setpgid, pipe, socket, socketpair,
        # eventfd, SysV IPC, memfd_create, and FS mutations), RLIMIT_NOFILE,
        # and a non-dumpable parent, while still allowing read-only access to
        # explicit `read_only_paths` and stdout pipes.
        with (
            tempfile.TemporaryDirectory(prefix="miri-eval-ro-") as ro_dir,
            tempfile.TemporaryDirectory(prefix="miri-eval-secret-") as secret_dir,
        ):
            ro_path = Path(ro_dir)
            existing = ro_path / "existing.txt"
            existing.write_text("hello", encoding="utf-8")
            unlisted = Path(secret_dir) / "secret.txt"
            unlisted.write_text("top-secret", encoding="utf-8")
            grandparent_pid = os.getppid()
            probe = (
                "import array, ctypes, errno, fcntl, os, resource, socket, threading\n"
                f"ro_dir = {str(ro_path)!r}\n"
                f"existing = {str(existing)!r}\n"
                f"unlisted = {str(unlisted)!r}\n"
                f"parent_pid = {os.getpid()}\n"
                f"parent_env = f'/proc/{{{os.getpid()}}}/environ'\n"
                f"grandparent_env = f'/proc/{{{grandparent_pid}}}/environ'\n"
                "def expect_blocked(name, fn):\n"
                "    try:\n"
                "        fn()\n"
                "    except (PermissionError, RuntimeError):\n"
                "        return\n"
                "    except OSError as exc:\n"
                "        if exc.errno in (errno.EPERM, errno.EACCES, errno.EFBIG, errno.EMFILE):\n"
                "            return\n"
                "        raise\n"
                "    raise SystemExit(f'{name} was not blocked')\n"
                "expect_blocked('fork', os.fork)\n"
                "expect_blocked('thread', lambda: threading.Thread(target=lambda: None).start())\n"
                "expect_blocked('pipe', os.pipe)\n"
                "expect_blocked('socket', lambda: socket.socket(socket.AF_UNIX, socket.SOCK_STREAM))\n"
                "expect_blocked('socketpair', lambda: socket.socketpair())\n"
                "if hasattr(os, 'eventfd'):\n"
                "    expect_blocked('eventfd', lambda: os.eventfd(0))\n"
                "libc = ctypes.CDLL(None, use_errno=True)\n"
                "assert libc.shmget(0, 4096, 0o600 | 0o1000) == -1 and ctypes.get_errno() == errno.EPERM\n"
                "# Filesystem/device/TTY ioctls must be denied even on O_RDONLY fds;\n"
                "# only FIOCLEX (0x5451, process-private FD_CLOEXEC) is allowed.\n"
                "ro_fd = os.open(existing, os.O_RDONLY)\n"
                "try:\n"
                "    expect_blocked('ioctl_getflags', lambda: fcntl.ioctl(ro_fd, 0x80086601, array.array('l', [0])))\n"
                "    expect_blocked('ioctl_setflags', lambda: fcntl.ioctl(ro_fd, 0x40086602, array.array('l', [0])))\n"
                "    expect_blocked('ioctl_tiocsti', lambda: fcntl.ioctl(ro_fd, 0x5412, b'x'))\n"
                "    fcntl.ioctl(ro_fd, 0x5451)\n"
                "    # fcntl must deny F_SETOWN, F_SETSIG, F_SETFL|O_ASYNC, F_SETPIPE_SZ,\n"
                "    # and non-zero upper-32-bit cmd values, while allowing safe FD/FL queries\n"
                "    # and non-O_ASYNC F_SETFL/F_DUPFD_CLOEXEC.\n"
                "    expect_blocked('fcntl_setown', lambda: fcntl.fcntl(1, fcntl.F_SETOWN, parent_pid))\n"
                "    expect_blocked('fcntl_setsig', lambda: fcntl.fcntl(1, 10, 9))\n"
                "    expect_blocked('fcntl_setfl_o_async_stdout', lambda: fcntl.fcntl(1, fcntl.F_SETFL, fcntl.fcntl(1, fcntl.F_GETFL) | 0x2000))\n"
                "    expect_blocked('fcntl_setfl_o_async_ro', lambda: fcntl.fcntl(ro_fd, fcntl.F_SETFL, 0x2000))\n"
                "    expect_blocked('fcntl_setpipe_sz', lambda: fcntl.fcntl(1, 1031, 4096))\n"
                "    # Non-zero upper 32 bits in fcntl cmd or F_SETFL flags must be denied.\n"
                "    import platform as _plat\n"
                "    _fcntl_nr = 72 if _plat.machine().lower() in ('x86_64', 'amd64') else 25\n"
                "    libc.syscall.argtypes = [ctypes.c_long, ctypes.c_long, ctypes.c_uint64, ctypes.c_uint64]\n"
                "    libc.syscall.restype = ctypes.c_long\n"
                "    assert libc.syscall(_fcntl_nr, ro_fd, (1 << 32) | 1, 0) == -1 and ctypes.get_errno() == errno.EPERM\n"
                "    assert libc.syscall(_fcntl_nr, ro_fd, 4, (1 << 32)) == -1 and ctypes.get_errno() == errno.EPERM\n"
                "    cur_fd = fcntl.fcntl(ro_fd, fcntl.F_GETFD)\n"
                "    fcntl.fcntl(ro_fd, fcntl.F_SETFD, cur_fd | fcntl.FD_CLOEXEC)\n"
                "    cur_fl = fcntl.fcntl(ro_fd, fcntl.F_GETFL)\n"
                "    fcntl.fcntl(ro_fd, fcntl.F_SETFL, cur_fl | os.O_NONBLOCK)\n"
                "    dup_fd = fcntl.fcntl(ro_fd, fcntl.F_DUPFD_CLOEXEC, 0)\n"
                "    os.close(dup_fd)\n"
                "finally:\n"
                "    os.close(ro_fd)\n"
                "# prlimit64 is permitted only for pid==0 (self), never for other PIDs.\n"
                "assert resource.prlimit(0, resource.RLIMIT_NOFILE)[1] <= 32\n"
                "expect_blocked('prlimit_parent', lambda: resource.prlimit(parent_pid, resource.RLIMIT_NOFILE))\n"
                "expect_blocked('prlimit_self_pid', lambda: resource.prlimit(os.getpid(), resource.RLIMIT_NOFILE))\n"
                "expect_blocked('open_write', lambda: open(os.path.join(ro_dir, 'new.txt'), 'w'))\n"
                "expect_blocked('open_rw', lambda: open(existing, 'r+'))\n"
                "expect_blocked('mkdir', lambda: os.mkdir(os.path.join(ro_dir, 'sub')))\n"
                "expect_blocked('truncate', lambda: os.truncate(existing, 0))\n"
                "expect_blocked('unlink', lambda: os.unlink(existing))\n"
                "expect_blocked('proc_list', lambda: os.listdir('/proc'))\n"
                "expect_blocked('parent_environ', lambda: open(parent_env, 'rb').read())\n"
                "expect_blocked('grandparent_environ', lambda: open(grandparent_env, 'rb').read())\n"
                "expect_blocked('unlisted_file', lambda: open(unlisted, 'rb').read())\n"
                "if hasattr(os, 'memfd_create'):\n"
                "    expect_blocked('memfd_create', lambda: os.memfd_create('x'))\n"
                "# RLIMIT_NOFILE must bound simultaneous open descriptors.\n"
                "fds = []\n"
                "hit_emfile = False\n"
                "try:\n"
                "    for _ in range(64):\n"
                "        fds.append(os.open(existing, os.O_RDONLY))\n"
                "except OSError as exc:\n"
                "    hit_emfile = exc.errno == errno.EMFILE\n"
                "finally:\n"
                "    for fd in fds:\n"
                "        os.close(fd)\n"
                "assert hit_emfile, 'RLIMIT_NOFILE did not cap open FDs'\n"
                "assert open(existing, 'rb').read() == b'hello'\n"
                "assert 'existing.txt' in os.listdir(ro_dir)\n"
            )
            rc_sec, out_sec, err_sec, _ = oracle.run_bounded(
                [sys.executable, "-I", "-B", "-c", probe],
                env=oracle.sanitized_child_env(),
                timeout_secs=10,
                max_memory_mb=256,
                read_only_paths=(ro_path,),
            )
            self.assertEqual(rc_sec, 0, f"stdout={out_sec!r} stderr={err_sec!r}")
            self.assertFalse((ro_path / "new.txt").exists())
            self.assertEqual(existing.read_text(encoding="utf-8"), "hello")
            self.assertGreater(len(oracle._build_confinement_seccomp_bpf("aarch64")), 0)

            # Non-vacuous _harden_parent_process() (PR_SET_DUMPABLE=0) test:
            # verify PR_GET_DUMPABLE == 0 directly AND verify from an
            # unconfined child (where `/proc` IS listable) that
            # `/proc/<parent_pid>/environ` is still denied with EACCES.
            import ctypes

            oracle._harden_parent_process()
            libc_p = ctypes.CDLL(None, use_errno=True)
            self.assertEqual(
                libc_p.prctl(oracle._PR_GET_DUMPABLE, 0, 0, 0, 0), 0
            )
            dumpable_probe = (
                "import os\n"
                f"parent_env = '/proc/{os.getpid()}/environ'\n"
                "assert len(os.listdir('/proc')) > 0\n"
                "try:\n"
                "    open(parent_env, 'rb').read()\n"
                "except PermissionError:\n"
                "    pass\n"
                "else:\n"
                "    raise SystemExit('unconfined child read parent /proc/<pid>/environ')\n"
            )
            r_dump = subprocess.run(
                [sys.executable, "-I", "-B", "-c", dumpable_probe],
                env=oracle.sanitized_child_env(),
                capture_output=True,
                text=True,
                timeout=10,
                check=False,
            )
            self.assertEqual(
                r_dump.returncode, 0, f"stdout={r_dump.stdout!r} stderr={r_dump.stderr!r}"
            )

            # Capture confinement must isolate inside private user/PID/mount/
            # network namespaces, enforce Landlock ABI >= 3 (writes/truncates
            # allowed strictly inside the bounded `tmpfs` work dir, denied on
            # `read_only_paths` and unlisted paths, `/proc` enumeration denied),
            # enforce default-deny seccomp (blocking nested userns via
            # `unshare`/`clone`/`clone3`, `kill`, `ptrace`, `prlimit64` on peer
            # PIDs, sockets, eventfd, memfd_create, SysV IPC), cap
            # `RLIMIT_NOFILE` and `RLIMIT_NPROC`, enforce aggregate disk quota
            # via `tmpfs`, and export bounded regular output files after
            # PID-namespace teardown.
            with (
                tempfile.TemporaryDirectory(prefix="miri-cap-rw-") as rw_dir,
                tempfile.TemporaryDirectory(prefix="miri-cap-exp-") as exp_dir,
            ):
                rw_path = Path(rw_dir)
                exp_path = Path(exp_dir)
                capture_iso_probe = (
                    "import ctypes, errno, os, pathlib, platform, resource, socket\n"
                    f"ro_dir = pathlib.Path({str(ro_path)!r})\n"
                    f"existing = pathlib.Path({str(existing)!r})\n"
                    f"rw_dir = pathlib.Path({str(rw_path)!r})\n"
                    f"unlisted = pathlib.Path({str(unlisted)!r})\n"
                    f"parent_pid = {os.getpid()}\n"
                    f"parent_env = '/proc/{os.getpid()}/environ'\n"
                    "# Capture child runs as PID 1 inside its isolated PID namespace,\n"
                    "# as a non-root UID with all Linux capability sets cleared.\n"
                    "assert os.getpid() == 1, f'expected PID 1 in CLONE_NEWPID, got {os.getpid()}'\n"
                    "assert os.getuid() != 0 and os.geteuid() != 0, f'unexpected root UID: {os.getuid()}/{os.geteuid()}'\n"
                    "status_fields = dict(\n"
                    "    ln.split(':', 1)\n"
                    "    for ln in pathlib.Path('/proc/self/status').read_text(encoding='utf-8').splitlines()\n"
                    "    if ':' in ln\n"
                    ")\n"
                    "for cap_key in ('CapInh', 'CapPrm', 'CapEff', 'CapBnd', 'CapAmb'):\n"
                    "    if cap_key in status_fields:\n"
                    "        assert int(status_fields[cap_key].strip(), 16) == 0, f'{cap_key} not cleared: {status_fields[cap_key]}'\n"
                    "# Private mount propagation: rw_dir tmpfs must not be shared with host.\n"
                    "rw_mount_lines = [\n"
                    "    ln for ln in pathlib.Path('/proc/self/mountinfo').read_text(encoding='utf-8').splitlines()\n"
                    "    if f' {rw_dir} ' in ln\n"
                    "]\n"
                    "assert rw_mount_lines, 'rw_dir tmpfs mount missing from /proc/self/mountinfo'\n"
                    "for ln in rw_mount_lines:\n"
                    "    opt_fields = ln.split(' - ', 1)[0].split()[6:]\n"
                    "    assert not any(tok.startswith('shared:') for tok in opt_fields), f'shared mount propagation leaked: {ln}'\n"
                    "# Writes + intra-dir rename inside bounded tmpfs work_dir/out succeed,\n"
                    "# including sharded sibling `Captured/` directory alongside `capture.json`.\n"
                    "out_d = rw_dir / 'out'\n"
                    "out_d.mkdir()\n"
                    "(out_d / 'Captured').mkdir()\n"
                    "(out_d / 'Captured' / 'Shard0.lean').write_text('-- shard', encoding='utf-8')\n"
                    "tmp_f = rw_dir / 'tmp' / 'a.tmp'\n"
                    "tmp_f.write_text('ok', encoding='utf-8')\n"
                    "os.replace(tmp_f, out_d / 'capture.json')\n"
                    "assert existing.read_text(encoding='utf-8') == 'hello'\n"
                    "# Writes/truncates/fchmod outside rw_dir (including system paths\n"
                    "# such as /dev/null, /etc/ld.so.cache, and /usr) and unlisted reads fail.\n"
                    "for label, fn in (\n"
                    "    ('write_ro', lambda: (ro_dir / 'evil.txt').write_text('x')),\n"
                    "    ('truncate_ro', lambda: os.truncate(existing, 0)),\n"
                    "    ('fchmod_ro', lambda: (lambda fd: (os.fchmod(fd, 0), os.close(fd)))(os.open(existing, os.O_RDONLY))),\n"
                    "    ('fchmod_dev_null', lambda: (lambda fd: (os.fchmod(fd, 0o666), os.close(fd)))(os.open('/dev/null', os.O_RDONLY))),\n"
                    "    ('fchmod_ld_cache', lambda: (lambda fd: (os.fchmod(fd, 0o644), os.close(fd)))(os.open('/etc/ld.so.cache', os.O_RDONLY))),\n"
                    "    ('fchmod_usr', lambda: (lambda fd: (os.fchmod(fd, 0o755), os.close(fd)))(os.open('/usr', os.O_RDONLY))),\n"
                    "    ('read_unlisted', lambda: unlisted.read_bytes()),\n"
                    "    ('write_unlisted', lambda: (unlisted.parent / 'evil.txt').write_text('x')),\n"
                    "    ('proc_list', lambda: os.listdir('/proc')),\n"
                    "    ('parent_environ', lambda: open(parent_env, 'rb').read()),\n"
                    "):\n"
                    "    try:\n"
                    "        fn()\n"
                    "    except PermissionError:\n"
                    "        if label.startswith('fchmod_'):\n"
                    "            raise SystemExit(f'{label} must fail with EROFS, not EPERM')\n"
                    "        continue\n"
                    "    except OSError as exc:\n"
                    "        if label.startswith('fchmod_'):\n"
                    "            if exc.errno == errno.EROFS:\n"
                    "                continue\n"
                    "            raise SystemExit(f'{label} expected EROFS, got errno={exc.errno}')\n"
                    "        if exc.errno in (errno.EROFS, errno.EACCES, errno.EPERM):\n"
                    "            continue\n"
                    "        raise\n"
                    "    raise SystemExit(f'capture isolation did not block {label}')\n"
                    "# Default-deny capture seccomp must block nested userns (unshare,\n"
                    "# clone(CLONE_NEWUSER), clone3), peer control (kill, ptrace,\n"
                    "# prlimit64(other)), and unnecessary kernel-object syscalls.\n"
                    "libc = ctypes.CDLL(None, use_errno=True)\n"
                    "assert libc.unshare(0x10000000) == -1 and ctypes.get_errno() == errno.EPERM\n"
                    "is_x86 = platform.machine().lower() in ('x86_64', 'amd64')\n"
                    "clone_nr = 56 if is_x86 else 220\n"
                    "ptrace_nr = 101 if is_x86 else 117\n"
                    "libc.syscall.restype = ctypes.c_long\n"
                    "# clone with CLONE_NEWUSER | SIGCHLD must return EPERM.\n"
                    "assert libc.syscall(ctypes.c_long(clone_nr), ctypes.c_uint64(0x10000011), ctypes.c_void_p(0), ctypes.c_void_p(0), ctypes.c_void_p(0), ctypes.c_uint64(0)) == -1 and ctypes.get_errno() == errno.EPERM\n"
                    "# clone3 must return ENOSYS so glibc falls back to filtered clone.\n"
                    "assert libc.syscall(ctypes.c_long(435), ctypes.c_void_p(0), ctypes.c_size_t(0)) == -1 and ctypes.get_errno() == errno.ENOSYS\n"
                    "# kill, ptrace, and prlimit64 on peer PIDs must return EPERM.\n"
                    "assert libc.kill(parent_pid, 0) == -1 and ctypes.get_errno() == errno.EPERM\n"
                    "assert libc.syscall(ctypes.c_long(ptrace_nr), ctypes.c_long(16), ctypes.c_long(parent_pid), ctypes.c_void_p(0), ctypes.c_void_p(0)) == -1 and ctypes.get_errno() == errno.EPERM\n"
                    "for label, fn in (\n"
                    "    ('prlimit_parent', lambda: resource.prlimit(parent_pid, resource.RLIMIT_NOFILE)),\n"
                    "    ('socket', lambda: socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)),\n"
                    "    ('socketpair', lambda: socket.socketpair()),\n"
                    "):\n"
                    "    try:\n"
                    "        fn()\n"
                    "    except PermissionError:\n"
                    "        continue\n"
                    "    raise SystemExit(f'capture seccomp did not block {label}')\n"
                    "if hasattr(os, 'eventfd'):\n"
                    "    try:\n"
                    "        os.eventfd(0)\n"
                    "        raise SystemExit('capture seccomp did not block eventfd')\n"
                    "    except PermissionError:\n"
                    "        pass\n"
                    "if hasattr(os, 'memfd_create'):\n"
                    "    try:\n"
                    "        os.memfd_create('x')\n"
                    "        raise SystemExit('capture seccomp did not block memfd_create')\n"
                    "    except PermissionError:\n"
                    "        pass\n"
                    "assert libc.shmget(0, 4096, 0o600 | 0o1000) == -1 and ctypes.get_errno() == errno.EPERM\n"
                    "# RLIMIT_NOFILE must bound simultaneous open descriptors in capture mode.\n"
                    f"assert resource.prlimit(0, resource.RLIMIT_NOFILE)[1] <= {oracle.CAPTURE_MAX_NOFILE}\n"
                    "fds = []\n"
                    "hit_emfile = False\n"
                    "try:\n"
                    f"    for _ in range({oracle.CAPTURE_MAX_NOFILE + 32}):\n"
                    "        fds.append(os.open(existing, os.O_RDONLY))\n"
                    "except OSError as exc:\n"
                    "    hit_emfile = exc.errno == errno.EMFILE\n"
                    "finally:\n"
                    "    for fd in fds:\n"
                    "        os.close(fd)\n"
                    "assert hit_emfile, 'capture RLIMIT_NOFILE did not cap open FDs'\n"
                    "# Bounded tmpfs must enforce aggregate disk quota across multiple files.\n"
                    "hit_enospc = False\n"
                    "created = []\n"
                    "chunk = b'A' * (2 * 1024 * 1024)\n"
                    "try:\n"
                    "    for i in range(24):\n"
                    "        p = rw_dir / 'tmp' / f'fill_{i}.bin'\n"
                    "        created.append(p)\n"
                    "        with open(p, 'wb') as fh:\n"
                    "            fh.write(chunk)\n"
                    "except OSError as exc:\n"
                    "    hit_enospc = exc.errno == errno.ENOSPC\n"
                    "finally:\n"
                    "    for p in created:\n"
                    "        try:\n"
                    "            p.unlink()\n"
                    "        except OSError:\n"
                    "            pass\n"
                    "assert hit_enospc, 'capture tmpfs did not enforce aggregate disk quota'\n"
                    "# Kernel task cap (max_tasks=4) must synchronously reject tight fork loops.\n"
                    "r_fd, w_fd = os.pipe()\n"
                    "pids = []\n"
                    "hit_eagain = False\n"
                    "try:\n"
                    "    for _ in range(16):\n"
                    "        pid = os.fork()\n"
                    "        if pid == 0:\n"
                    "            os.close(w_fd)\n"
                    "            os.read(r_fd, 1)\n"
                    "            os._exit(0)\n"
                    "        pids.append(pid)\n"
                    "except OSError as exc:\n"
                    "    hit_eagain = exc.errno in (errno.EAGAIN, errno.ENOMEM)\n"
                    "finally:\n"
                    "    os.close(w_fd)\n"
                    "    os.close(r_fd)\n"
                    "    for pid in pids:\n"
                    "        try:\n"
                    "            os.waitpid(pid, 0)\n"
                    "        except OSError:\n"
                    "            pass\n"
                    "assert hit_eagain, f'kernel task cap did not trigger (spawned {len(pids)})'\n"
                    "assert len(pids) <= 3, f'kernel task cap exceeded: {len(pids)}'\n"
                )
                rc_cap, out_cap, err_cap, _ = oracle.run_bounded(
                    [sys.executable, "-I", "-B", "-c", capture_iso_probe],
                    env=oracle.sanitized_child_env(),
                    timeout_secs=10,
                    max_memory_mb=256,
                    confinement="capture",
                    max_procs=None,
                    max_tasks=4,
                    read_only_paths=(ro_path,),
                    read_write_paths=(rw_path,),
                    export_src=rw_path / "out" / "capture.json",
                    export_dst=exp_path / "capture.json",
                )
                self.assertEqual(
                    rc_cap, 0, f"stdout={out_cap!r} stderr={err_cap!r}"
                )
                self.assertEqual(
                    (exp_path / "capture.json").read_text(encoding="utf-8"), "ok"
                )
                self.assertFalse((exp_path / "Captured").exists())
                self.assertEqual(existing.read_text(encoding="utf-8"), "hello")
                self.assertFalse((ro_path / "evil.txt").exists())
                self.assertFalse((Path(secret_dir) / "evil.txt").exists())

                # Export helper must reject symlinks and non-regular entries.
                bad_src = Path(secret_dir) / "bad_out"
                bad_src.mkdir()
                (bad_src / "link.json").symlink_to(existing)
                with self.assertRaises(OSError):
                    oracle._export_capture_file(
                        bad_src / "link.json", exp_path / "sym.json"
                    )
                (bad_src / "link.json").unlink()
                (bad_src / "subdir").mkdir()
                with self.assertRaises(oracle.OracleError):
                    oracle._export_capture_file(
                        bad_src / "subdir", exp_path / "dir.json"
                    )

            # Non-vacuous `setsid`/`setpgid` confinement test:
            # inside a `start_new_session=True` leader, `setsid()` and
            # `setpgid(0, 0)` return `EPERM` even without seccomp. Verify
            # first via an unconfined control that forked non-leader children
            # succeed at both `os.setsid()` and `os.setpgid(0, 0)`, then
            # verify that both are blocked with `EPERM` in a forked non-leader
            # child under `confinement="capture"` (exercising `session_nrs`)
            # and in a non-leader child under `confinement="eval"`.
            non_leader_probe = (
                "import errno, os, sys\n"
                "expect_eperm = sys.argv[1] == 'blocked'\n"
                "for label, op in (('setsid', 'setsid'), ('setpgid', 'setpgid')):\n"
                "    pid = os.fork()\n"
                "    if pid == 0:\n"
                "        try:\n"
                "            if op == 'setsid':\n"
                "                os.setsid()\n"
                "            else:\n"
                "                os.setpgid(0, 0)\n"
                "            os._exit(10 if expect_eperm else 0)\n"
                "        except PermissionError:\n"
                "            os._exit(0 if expect_eperm else 20)\n"
                "        except OSError as exc:\n"
                "            os._exit(0 if (expect_eperm and exc.errno == errno.EPERM) else 30)\n"
                "    _, status = os.waitpid(pid, 0)\n"
                "    if not os.WIFEXITED(status) or os.WEXITSTATUS(status) != 0:\n"
                "        raise SystemExit(f'{label} unexpected status={status}')\n"
            )
            ctrl_proc = subprocess.run(
                [sys.executable, "-I", "-B", "-c", non_leader_probe, "allowed"],
                start_new_session=True,
                capture_output=True,
                text=True,
                timeout=10,
                check=False,
            )
            self.assertEqual(
                ctrl_proc.returncode,
                0,
                f"unconfined non-leader control failed: {ctrl_proc.stderr!r}",
            )
            rc_cap_sess, out_cs, err_cs, _ = oracle.run_bounded(
                [sys.executable, "-I", "-B", "-c", non_leader_probe, "blocked"],
                env=oracle.sanitized_child_env(),
                timeout_secs=10,
                max_memory_mb=256,
                confinement="capture",
                max_procs=2,
            )
            self.assertEqual(
                rc_cap_sess, 0, f"capture setsid/setpgid failed: out={out_cs!r} err={err_cs!r}"
            )

            eval_sess_cmd = oracle._wrap_with_confinement(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    "-c",
                    (
                        "import errno, os\n"
                        "for name, fn in (('setsid', os.setsid), ('setpgid', lambda: os.setpgid(0, 0))):\n"
                        "    try:\n"
                        "        fn()\n"
                        "    except PermissionError:\n"
                        "        continue\n"
                        "    except OSError as exc:\n"
                        "        if exc.errno == errno.EPERM:\n"
                        "            continue\n"
                        "        raise\n"
                        "    raise SystemExit(f'{name} was not blocked')\n"
                    ),
                ],
                timeout_secs=10,
                max_memory_mb=256,
                confinement="eval",
            )
            # Launch from a forked non-leader helper without `start_new_session`
            # and verify `getsid(0) != getpid()` before exec so the eval child
            # is guaranteed NOT to be a session leader.
            non_leader_eval_launcher = (
                "import os, subprocess, sys\n"
                f"cmd = {eval_sess_cmd!r}\n"
                "pid = os.fork()\n"
                "if pid == 0:\n"
                "    assert os.getsid(0) != os.getpid(), 'must not be session leader'\n"
                "    os.execv(cmd[0], cmd)\n"
                "_, status = os.waitpid(pid, 0)\n"
                "raise SystemExit(os.WEXITSTATUS(status) if os.WIFEXITED(status) else 99)\n"
            )
            eval_sess_proc = subprocess.run(
                [sys.executable, "-I", "-B", "-c", non_leader_eval_launcher],
                env=oracle.sanitized_child_env(),
                start_new_session=True,
                capture_output=True,
                text=True,
                timeout=10,
                check=False,
            )
            self.assertEqual(
                eval_sess_proc.returncode,
                0,
                f"non-leader eval setsid/setpgid failed: {eval_sess_proc.stderr!r}",
            )

            # Interruption & parent-death cleanup:
            # 1. `KeyboardInterrupt` inside `run_bounded` must immediately kill
            #    the confined sleeping child process group.
            # 2. `SIGKILL` of a parent harness must terminate a sleeping
            #    confined child via Linux `PR_SET_PDEATHSIG`.
            import signal as _sig
            import time as _time

            def _pid_alive(pid: int) -> bool:
                try:
                    os.kill(pid, 0)
                    return True
                except ProcessLookupError:
                    return False

            pid_file = Path(tmp_path := ro_path) / "sleep_pid.txt"
            captured_child_pid: list[int] = []
            orig_popen = oracle.subprocess.Popen

            def _spy_popen(*args, **kwargs):
                p = orig_popen(*args, **kwargs)
                captured_child_pid.append(p.pid)
                return p

            wait_calls = 0
            orig_event_wait = oracle.threading.Event.wait

            def _interrupting_wait(self_ev, timeout=None):
                nonlocal wait_calls
                wait_calls += 1
                if wait_calls == 2:
                    raise KeyboardInterrupt("simulated Ctrl-C")
                return orig_event_wait(self_ev, timeout=timeout)

            with (
                mock.patch.object(oracle.subprocess, "Popen", side_effect=_spy_popen),
                mock.patch.object(oracle.threading.Event, "wait", _interrupting_wait),
            ):
                with self.assertRaises(KeyboardInterrupt):
                    oracle.run_bounded(
                        [sys.executable, "-I", "-B", "-c", "import time; time.sleep(30)"],
                        env=oracle.sanitized_child_env(),
                        timeout_secs=30,
                        max_memory_mb=256,
                        confinement="eval",
                    )
            self.assertEqual(len(captured_child_pid), 1)
            self.assertFalse(
                _pid_alive(captured_child_pid[0]),
                "sleeping confined child survived KeyboardInterrupt",
            )

            pdeath_launcher = (
                "import os, subprocess, sys, time\n"
                f"sys.path.insert(0, {str(CI_DIR)!r})\n"
                "import run_miri_ub_oracle as oracle\n"
                "cmd = oracle._wrap_with_confinement(\n"
                "    [sys.executable, '-I', '-B', '-c', 'import time; time.sleep(30)'],\n"
                "    timeout_secs=30, max_memory_mb=256, confinement='eval',\n"
                "    parent_pid=os.getpid(),\n"
                ")\n"
                "p = subprocess.Popen(cmd, env=oracle.sanitized_child_env(), start_new_session=True)\n"
                "print(p.pid, flush=True)\n"
                "time.sleep(30)\n"
            )
            mid = subprocess.Popen(
                [sys.executable, "-I", "-B", "-c", pdeath_launcher],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            try:
                assert mid.stdout is not None
                child_pid = int(mid.stdout.readline().strip())
                # Wait briefly so `--_confined-exec` installs PR_SET_PDEATHSIG.
                _time.sleep(0.3)
                os.kill(mid.pid, _sig.SIGKILL)
                mid.wait(timeout=5)
                deadline_pd = _time.monotonic() + 3.0
                while _pid_alive(child_pid) and _time.monotonic() < deadline_pd:
                    _time.sleep(0.05)
                self.assertFalse(
                    _pid_alive(child_pid),
                    f"confined child {child_pid} survived parent SIGKILL",
                )
            finally:
                if mid.poll() is None:
                    mid.kill()
                    mid.wait(timeout=5)
                if mid.stdout is not None:
                    mid.stdout.close()
                if mid.stderr is not None:
                    mid.stderr.close()
            del pid_file

        # A child exceeding RLIMIT_AS must fail rather than exhaust host RAM.
        rc, _, _, _ = oracle.run_bounded(
            [sys.executable, "-c", "buf = bytearray(400 * 1024 * 1024)"],
            env=oracle.sanitized_child_env(),
            timeout_secs=10,
            max_memory_mb=256,
        )
        self.assertNotEqual(rc, 0)

        # Even in capture confinement mode, exceeding max_procs kills the PGID.
        fork_probe = (
            "import os, time\n"
            "for _ in range(2):\n"
            "    pid = os.fork()\n"
            "    if pid == 0:\n"
            "        time.sleep(5)\n"
            "        os._exit(0)\n"
            "time.sleep(5)\n"
        )
        rc_p, _, _, elapsed_p = oracle.run_bounded(
            [sys.executable, "-I", "-B", "-c", fork_probe],
            env=oracle.sanitized_child_env(),
            timeout_secs=10,
            max_memory_mb=256,
            confinement="capture",
            max_procs=2,
        )
        self.assertEqual(rc_p, "process_limit")
        self.assertLess(elapsed_p, 3.0)

        # If /proc enumeration fails, max_procs enforcement must fail closed.
        from unittest import mock

        with mock.patch.object(
            oracle, "_count_pgid_processes", return_value=None
        ):
            rc_fc, _, _, _ = oracle.run_bounded(
                [sys.executable, "-I", "-B", "-c", "import time; time.sleep(5)"],
                env=oracle.sanitized_child_env(),
                timeout_secs=10,
                max_memory_mb=256,
                confinement="capture",
                max_procs=2,
            )
        self.assertEqual(rc_fc, "process_limit")
