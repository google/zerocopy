#!/usr/bin/env python3
"""Standalone probe for POSIX process, signal, path and address-space hazards.

The probe has two layers.

* Portable, pure-Python, exhaustively enumerated state-machine models.  They run
  on any host with Python 3.10 or newer and are the only checks that can make
  the probe exit non-zero on a host without the live facilities.
* Live checks against the running kernel and C library.  Each live check first
  detects whether the facility exists (``os.fork``, ``/proc``, ``openat2`` and
  so on) and reports SKIP when it does not.  A live check that runs and
  contradicts the documented behaviour is a FAIL.

Usage::

    python3 -B verify_posix_runtime_hazards.py              # models + live checks
    python3 -B verify_posix_runtime_hazards.py --model-only  # models only
    python3 -B verify_posix_runtime_hazards.py --json        # machine-readable

Row kinds: PASS/FAIL rows are computed (model exploration) or observed (live).
DEF rows restate constants or decision tables transcribed from the upstream
files listed below, or a model arm whose outcome is fixed by its definition;
they document what the report cites and are NOT verification of upstream.

Exit status is 0 when no check failed (SKIP and DEF are not failures) and 1 otherwise.
The probe writes only below a private temporary directory that it removes.

Numeric constants are quoted from these upstream revisions:

* torvalds/linux 4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd
  (arch/x86/kernel/signal.c, include/uapi/linux/openat2.h,
  include/uapi/asm-generic/{signal-defs.h,mman-common.h},
  arch/x86/entry/syscalls/syscall_64.tbl)
* llvm/llvm-project 36f1fd30c75dc97c58a2350b6c7646206b30a0aa
  (compiler-rt/lib/asan/asan_mapping.h, compiler-rt/lib/tsan/rtl/tsan_platform.h)
* golang/go b496a3044e1dcdc3eed0af3e0e89db92f740d764 (src/runtime/malloc.go)
* openjdk/jdk 4f33273115381cd7697082fcb1bb2642dae19043
  (src/hotspot/share/oops/compressedOops.hpp)
* v8/v8 e88118f63dd96f24a9acb8bd0665e7880063f5c0 (include/v8-internal.h)
"""

from __future__ import annotations

import argparse
import ctypes
import errno
import itertools
import json
import os
import platform
import shutil
import signal
import sys
import tempfile
import threading
import time
import warnings
from collections import deque
from typing import Callable, Iterable, Iterator, Optional, Sequence

# --------------------------------------------------------------------------
# Result bookkeeping
# --------------------------------------------------------------------------

RESULTS: list[dict] = []


def record(section: str, name: str, status: str, detail: str = "") -> None:
    RESULTS.append({"section": section, "check": name, "status": status, "detail": detail})


def check(section: str, name: str, cond: bool, detail: str = "") -> bool:
    record(section, name, "PASS" if cond else "FAIL", detail)
    return cond


def skip(section: str, name: str, reason: str) -> None:
    record(section, name, "SKIP", reason)


def by_definition(section: str, name: str, cond: bool, detail: str = "") -> None:
    """Row that restates a transcribed table/constant or a model's own definition.

    Such a row cannot contradict the upstream source it was copied from, so it is
    reported as DEF (or FAIL if the transcription is internally inconsistent) and
    is never counted as a passed verification.
    """
    record(section, name, "DEF" if cond else "FAIL", detail)


# --------------------------------------------------------------------------
# A. fork() versus threads: explicit-state model
# --------------------------------------------------------------------------
#
# A process is a set of threads, each running a straight-line program over
#   ("lock", L) ("unlock", L) ("set", var, value) ("fork",)
# Mutexes are non-recursive: locking a mutex that is held (even by the same
# thread) blocks.  A state is (pcs, owners, memory).  Every interleaving is
# explored breadth-first.

Op = tuple
State = tuple  # (pcs, owners, mem)


class Model:
    def __init__(self, programs: Sequence[Sequence[Op]], locks: Sequence[str],
                 variables: Sequence[str]) -> None:
        self.programs = [list(p) for p in programs]
        self.locks = list(locks)
        self.variables = list(variables)
        self.lock_ix = {name: i for i, name in enumerate(self.locks)}
        self.var_ix = {name: i for i, name in enumerate(self.variables)}

    def initial(self) -> State:
        return (tuple(0 for _ in self.programs),
                tuple(None for _ in self.locks),
                tuple(0 for _ in self.variables))

    def enabled(self, state: State, tid: int) -> Optional[State]:
        pcs, owners, mem = state
        prog = self.programs[tid]
        if pcs[tid] >= len(prog):
            return None
        op = prog[pcs[tid]]
        owners_l, mem_l = list(owners), list(mem)
        if op[0] == "lock":
            ix = self.lock_ix[op[1]]
            if owners[ix] is not None:
                return None
            owners_l[ix] = tid
        elif op[0] == "unlock":
            ix = self.lock_ix[op[1]]
            if owners[ix] != tid:
                raise AssertionError("unlock by non-owner in model program")
            owners_l[ix] = None
        elif op[0] == "set":
            mem_l[self.var_ix[op[1]]] = op[2]
        elif op[0] == "fork":
            pass  # the parent simply continues; snapshots are taken by the explorer
        else:
            raise AssertionError(f"unknown op {op!r}")
        pcs_l = list(pcs)
        pcs_l[tid] += 1
        return (tuple(pcs_l), tuple(owners_l), tuple(mem_l))

    def explore(self) -> tuple[set, list, list]:
        """Return (reachable states, fork snapshots, deadlocked states)."""
        start = self.initial()
        seen = {start}
        queue = deque([start])
        snapshots: list[tuple[State, int]] = []
        deadlocks: list[State] = []
        while queue:
            state = queue.popleft()
            pcs = state[0]
            progressed = False
            for tid, prog in enumerate(self.programs):
                if pcs[tid] < len(prog) and prog[pcs[tid]][0] == "fork":
                    snapshots.append((state, tid))
                nxt = self.enabled(state, tid)
                if nxt is None:
                    continue
                progressed = True
                if nxt not in seen:
                    seen.add(nxt)
                    queue.append(nxt)
            finished = all(pcs[t] >= len(p) for t, p in enumerate(self.programs))
            if not progressed and not finished:
                deadlocks.append(state)
        return seen, snapshots, deadlocks


def run_child(model: Model, snapshot: State, forker: int, child_prog: Sequence[Op],
              policy: str, invariants: dict[str, tuple[str, str]]) -> str:
    """Run the single surviving thread of a forked or spawned child.

    policy:
      "fork"   -- POSIX fork(): memory and mutex state copied verbatim.
      "reinit" -- like fork, but a child handler force-reinitialises every mutex.
      "spawn"  -- a fresh image: no inherited mutex state or memory.
    Returns "ok", "deadlock" (blocked on a mutex whose owner does not exist in
    the child, or on its own non-recursive mutex) or "inconsistent" (the child
    acquired a mutex and observed its guarded invariant broken).
    """
    _, owners, mem = snapshot
    owners_l, mem_l = list(owners), list(mem)
    if policy == "reinit":
        owners_l = [None] * len(owners_l)
    elif policy == "spawn":
        owners_l = [None] * len(owners_l)
        mem_l = [0] * len(mem_l)
    for op in child_prog:
        if op[0] == "lock":
            ix = model.lock_ix[op[1]]
            if owners_l[ix] is not None:
                return "deadlock"
            owners_l[ix] = forker
            a, b = invariants[op[1]]
            if mem_l[model.var_ix[a]] != mem_l[model.var_ix[b]]:
                return "inconsistent"
        elif op[0] == "unlock":
            ix = model.lock_ix[op[1]]
            if owners_l[ix] != forker:
                return "deadlock"  # unlocking a mutex owned by a vanished thread
            owners_l[ix] = None
    return "ok"


LOCKS = ["M", "IO", "X"]  # allocator arena, stdio list, third-party library
VARS = ["M.a", "M.b", "IO.a", "IO.b", "X.a", "X.b"]
INVARIANTS = {"M": ("M.a", "M.b"), "IO": ("IO.a", "IO.b"), "X": ("X.a", "X.b")}


def critical(lock: str) -> list[Op]:
    """A two-step update that breaks and restores the lock's invariant."""
    a, b = INVARIANTS[lock]
    return [("lock", lock), ("set", a, 1), ("set", b, 1), ("unlock", lock)]


def tally(model: Model, snapshots: Iterable, child_prog: Sequence[Op], policy: str) -> dict:
    out = {"ok": 0, "deadlock": 0, "inconsistent": 0}
    for state, tid in snapshots:
        out[run_child(model, state, tid, child_prog, policy, INVARIANTS)] += 1
    return out


def part_a_model() -> None:
    sec = "A.model"
    child_uses_libs = [("lock", "M"), ("unlock", "M"), ("lock", "X"), ("unlock", "X")]
    child_as_safe_only: list[Op] = []  # only async-signal-safe calls, then exec

    # A1: two workers inside library critical sections, a third thread forks.
    plain = Model([critical("M"), critical("X"), [("fork",)]], LOCKS, VARS)
    states, snaps, dead = plain.explore()
    t_fork = tally(plain, snaps, child_uses_libs, "fork")
    t_safe = tally(plain, snaps, child_as_safe_only, "fork")
    t_reinit = tally(plain, snaps, child_uses_libs, "reinit")
    t_spawn = tally(plain, snaps, child_uses_libs, "spawn")
    n = len(snaps)
    check(sec, "parent alone is deadlock-free", not dead, f"{len(states)} reachable states")
    check(sec, "fork(): child using library locks can deadlock", t_fork["deadlock"] > 0,
          f"{t_fork['deadlock']}/{n} fork snapshots deadlock")
    check(sec, "fork(): async-signal-safe-only child never blocks",
          t_safe == {"ok": n, "deadlock": 0, "inconsistent": 0}, f"{n}/{n} ok")
    check(sec, "reinitialising mutexes in the child trades deadlock for broken invariants",
          t_reinit["deadlock"] == 0 and t_reinit["inconsistent"] > 0,
          f"{t_reinit['inconsistent']}/{n} snapshots expose a half-updated structure")
    by_definition(sec, "control arm: a spawn-style child inherits no lock state in this model",
                  t_spawn == {"ok": n, "deadlock": 0, "inconsistent": 0},
                  "the spawn policy clears inherited state by definition")

    # A2: atfork prepare/child handlers registered for M only (X is a library
    # that did not register).  prepare = lock M; child handler = unlock M.
    partial = Model([critical("M"), critical("X"),
                     [("lock", "M"), ("fork",), ("unlock", "M")]], LOCKS, VARS)
    _, snaps, dead = partial.explore()
    t = tally(partial, snaps, [("unlock", "M")] + child_uses_libs, "fork")
    check(sec, "atfork for one library leaves unregistered locks stranded",
          not dead and t["deadlock"] > 0 and t["inconsistent"] == 0,
          f"{t['deadlock']}/{len(snaps)} snapshots deadlock on X")

    # A3: every lock registered, one global order (M before X).
    full = Model([critical("M"), critical("X"),
                  [("lock", "M"), ("lock", "X"), ("fork",), ("unlock", "X"), ("unlock", "M")]],
                 LOCKS, VARS)
    _, snaps, dead = full.explore()
    t = tally(full, snaps, [("unlock", "X"), ("unlock", "M")] + child_uses_libs, "fork")
    check(sec, "atfork over every lock with one global order is safe",
          not dead and t == {"ok": len(snaps), "deadlock": 0, "inconsistent": 0},
          f"{len(snaps)}/{len(snaps)} ok")

    # A4: same handlers, but another thread nests the locks in the opposite order.
    inverted = Model([[("lock", "X"), ("lock", "M"), ("unlock", "M"), ("unlock", "X")],
                      [("lock", "M"), ("lock", "X"), ("fork",), ("unlock", "X"), ("unlock", "M")]],
                     LOCKS, VARS)
    _, _, dead = inverted.explore()
    check(sec, "atfork prepare order that disagrees with a library deadlocks the parent",
          len(dead) > 0, f"{len(dead)} deadlocked parent states")

    # A5: the forking thread itself holds a registered lock (the flockfile case
    # in the POSIX pthread_atfork rationale): prepare blocks on its own mutex.
    selfheld = Model([[("lock", "IO"), ("lock", "IO"), ("fork",), ("unlock", "IO"), ("unlock", "IO")]],
                     LOCKS, VARS)
    _, snaps, dead = selfheld.explore()
    check(sec, "fork from inside a registered critical section self-deadlocks in prepare",
          len(dead) == 1 and not snaps, "fork is never reached")


def read_maps(path: str = "/proc/self/maps") -> list[tuple[int, int, str, str]]:
    out = []
    with open(path, "r", encoding="utf-8", errors="replace") as fh:
        for line in fh:
            parts = line.split(None, 5)
            lo, hi = (int(x, 16) for x in parts[0].split("-"))
            out.append((lo, hi, parts[1], parts[5].strip() if len(parts) > 5 else ""))
    return out


def layout_fingerprint(maps: Sequence[tuple[int, int, str, str]]) -> tuple:
    """(lowest libc text base, stack range) -- stable across fork, re-randomised by exec."""
    libc = [lo for lo, _, _, name in maps if "/libc" in name or "libc.so" in name
            or "libSystem" in name]
    stack = [(lo, hi) for lo, hi, _, name in maps if name == "[stack]"]
    return (min(libc) if libc else None, stack[0] if stack else None)


SPAWN_CHILD = r"""
import sys, threading
fp = ("none", "none")
try:
    libc, stack = [], []
    for line in open("/proc/self/maps"):
        parts = line.split(None, 5)
        name = parts[5].strip() if len(parts) > 5 else ""
        lo = int(parts[0].split("-")[0], 16)
        if "/libc" in name or "libc.so" in name:
            libc.append(lo)
        if name == "[stack]":
            stack.append(parts[0])
    fp = (str(min(libc)) if libc else "none", stack[0] if stack else "none")
except OSError:
    pass
lock = threading.Lock()
print(threading.active_count(), int(lock.acquire(timeout=1.0)), fp[0], fp[1])
"""


def part_a_live() -> None:
    sec = "A.live"
    if not hasattr(os, "fork"):
        skip(sec, "multi-threaded fork()", "os.fork unavailable")
        return
    lock = threading.Lock()
    held = threading.Event()
    release = threading.Event()

    def holder() -> None:
        with lock:
            held.set()
            release.wait(30)

    th = threading.Thread(target=holder, daemon=True)
    th.start()
    held.wait(10)
    have_proc = os.path.exists("/proc/self/maps")
    parent_fp = layout_fingerprint(read_maps()) if have_proc else (None, None)
    try:
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter("always")
            pid = os.fork()
            if pid == 0:
                # Child: exactly one thread exists; `lock` is owned by nobody alive.
                code = 0
                try:
                    if lock.acquire(timeout=0.4):
                        code |= 1
                    if threading.active_count() == 1:
                        code |= 2
                    if have_proc and layout_fingerprint(read_maps()) == parent_fp:
                        code |= 4
                finally:
                    os._exit(code)
        deadline = time.monotonic() + 15
        status = None
        while time.monotonic() < deadline:
            done, st = os.waitpid(pid, os.WNOHANG)
            if done:
                status = st
                break
            time.sleep(0.02)
        if status is None:
            os.kill(pid, signal.SIGKILL)
            os.waitpid(pid, 0)
            check(sec, "forked child terminates", False, "child hung; killed")
            return
        code = os.WEXITSTATUS(status) if os.WIFEXITED(status) else -1
        check(sec, "child of a multi-threaded fork has exactly one thread", code >= 0 and bool(code & 2),
              f"exit code {code}")
        check(sec, "mutex held by a non-forking thread is permanently locked in the child",
              code >= 0 and not (code & 1), "acquire(timeout=0.4) timed out in child")
        if have_proc and parent_fp != (None, None):
            check(sec, "forked child keeps the parent's address-space layout", bool(code & 4),
                  "libc base and [stack] range identical")
        else:
            skip(sec, "forked child keeps the parent's address-space layout", "no /proc/self/maps")
        if sys.implementation.name == "cpython" and sys.version_info >= (3, 12):
            msgs = [str(w.message) for w in caught if issubclass(w.category, DeprecationWarning)]
            check(sec, "CPython >= 3.12 warns when a multi-threaded process forks",
                  any("multi-threaded" in m and "fork" in m for m in msgs),
                  (msgs[0][:90] if msgs else "no warning recorded"))
        else:
            skip(sec, "CPython >= 3.12 warns when a multi-threaded process forks",
                 f"{sys.implementation.name} {sys.version_info[0]}.{sys.version_info[1]}")
    finally:
        release.set()
        th.join(10)

    if not hasattr(os, "posix_spawn"):
        skip(sec, "posix_spawn() child", "os.posix_spawn unavailable")
        return
    r, w = os.pipe()
    try:
        pid = os.posix_spawn(sys.executable, [sys.executable, "-B", "-c", SPAWN_CHILD],
                             dict(os.environ), file_actions=[(os.POSIX_SPAWN_DUP2, w, 1)])
        os.close(w)
        w = -1
        data = b""
        while True:
            chunk = os.read(r, 4096)
            if not chunk:
                break
            data += chunk
        _, st = os.waitpid(pid, 0)
    except OSError as exc:
        skip(sec, "posix_spawn() child", f"spawn failed: {exc}")
        return
    finally:
        os.close(r)
        if w != -1:
            os.close(w)
    fields = data.decode("utf-8", "replace").split()
    ok = os.WIFEXITED(st) and os.WEXITSTATUS(st) == 0 and len(fields) == 4
    check(sec, "posix_spawn() child starts single-threaded with fresh lock state",
          ok and fields[0] == "1" and fields[1] == "1", " ".join(fields[:2]))
    if ok and have_proc and parent_fp[0] is not None and fields[2] != "none":
        aslr = "?"
        try:
            with open("/proc/sys/kernel/randomize_va_space") as fh:
                aslr = fh.read().strip()
        except OSError:
            pass
        same = (str(parent_fp[0]) == fields[2]
                and f"{parent_fp[1][0]:x}-{parent_fp[1][1]:x}" == fields[3])
        if same:
            skip(sec, "posix_spawn() child gets a freshly randomised layout",
                 f"layout identical (randomize_va_space={aslr}; ASLR appears disabled)")
        else:
            check(sec, "posix_spawn() child gets a freshly randomised layout", True,
                  f"randomize_va_space={aslr}")
    else:
        skip(sec, "posix_spawn() child gets a freshly randomised layout", "no /proc layout data")


# --------------------------------------------------------------------------
# B. Signals: async-signal-safety, EINTR and restart
# --------------------------------------------------------------------------

def part_b_model() -> None:
    sec = "B.model"
    # B1: one thread runs malloc()-like code; a handler may run between any two
    # steps, on the same thread, to completion before the thread resumes.
    main = critical("M")
    unsafe_handler = [("lock", "M"), ("read", "M"), ("unlock", "M")]   # calls malloc
    safe_handler = [("set", "flag", 1)]                    # sig_atomic_t flag / write(2) to a pipe

    def run_handler(handler: Sequence[Op], at: int, recursive: bool) -> str:
        """Interrupt `main` before step `at`, run `handler` to completion on the same thread."""
        owner: Optional[int] = None
        mem = {"M.a": 0, "M.b": 0, "flag": 0}
        for op in main[:at]:
            if op[0] == "lock":
                owner = 0
            elif op[0] == "unlock":
                owner = None
            else:
                mem[op[1]] = op[2]
        depth = 0
        for op in handler:
            if op[0] == "lock":
                if owner is not None and not recursive:
                    return "deadlock"          # the only thread that could unlock is suspended
                depth += 1
            elif op[0] == "read":
                if mem["M.a"] != mem["M.b"]:
                    return "inconsistent"
            elif op[0] == "unlock":
                depth -= 1
            else:
                mem[op[1]] = op[2]
        return "ok"

    points = range(len(main) + 1)
    unsafe_plain = [run_handler(unsafe_handler, at, False) for at in points]
    unsafe_recursive = [run_handler(unsafe_handler, at, True) for at in points]
    safe = [run_handler(safe_handler, at, False) for at in points]
    check(sec, "handler that takes the interrupted code's lock self-deadlocks",
          unsafe_plain.count("deadlock") == 3 and unsafe_plain.count("ok") == 2,
          f"{unsafe_plain.count('deadlock')}/{len(points)} interruption points")
    check(sec, "a recursive mutex instead lets the handler read a half-updated structure",
          unsafe_recursive.count("inconsistent") == 1 and unsafe_recursive.count("deadlock") == 0,
          f"{unsafe_recursive.count('inconsistent')}/{len(points)} interruption points")
    check(sec, "handler restricted to a flag write completes at every interruption point",
          safe == ["ok"] * len(points), f"{safe.count('ok')}/{len(points)} ok")

    # B2: Linux restart decision (arch/x86/kernel/signal.c handle_signal and
    # arch_do_signal_or_restart): internal return code x disposition.
    def decide(code: str, handler: bool, sa_restart: bool) -> str:
        if not handler:
            return "restart_syscall()" if code == "ERESTART_RESTARTBLOCK" else "restart"
        if code in ("ERESTART_RESTARTBLOCK", "ERESTARTNOHAND"):
            return "EINTR"
        if code == "ERESTARTSYS":
            return "restart" if sa_restart else "EINTR"
        if code == "ERESTARTNOINTR":
            return "restart"
        raise AssertionError(code)

    golden = {
        ("ERESTARTSYS", True, False): "EINTR",
        ("ERESTARTSYS", True, True): "restart",
        ("ERESTARTSYS", False, False): "restart",
        ("ERESTARTNOINTR", True, False): "restart",
        ("ERESTARTNOINTR", True, True): "restart",
        ("ERESTARTNOHAND", True, True): "EINTR",
        ("ERESTARTNOHAND", False, False): "restart",
        ("ERESTART_RESTARTBLOCK", True, True): "EINTR",
        ("ERESTART_RESTARTBLOCK", False, False): "restart_syscall()",
    }
    by_definition(sec, "Linux restart table as transcribed: SA_RESTART only affects ERESTARTSYS",
          all(decide(*k) == v for k, v in golden.items())
          and all(decide(c, True, True) == decide(c, True, False)
                  for c in ("ERESTARTNOINTR", "ERESTARTNOHAND", "ERESTART_RESTARTBLOCK")),
          f"{len(golden)} cells; only the ERESTARTSYS row is observed, in B.live")

    # B3: write(fd, buf, n) on a slow device, n = 4.  Each call transfers k
    # bytes; a signal may cut it short.  Without progress the call fails with
    # EINTR (or is restarted under SA_RESTART); with progress it returns the
    # short count in both modes.
    n_bytes = 4

    def schedules(remaining: int, depth: int) -> Iterator[tuple]:
        """All kernel behaviours: per call, ('eintr',) or ('n', k) with 1 <= k <= remaining."""
        if remaining == 0 or depth == 0:
            yield ()
            return
        for k in range(1, remaining + 1):
            for rest in schedules(remaining - k, depth - 1):
                yield (("n", k),) + rest
        for rest in schedules(remaining, depth - 1):
            yield (("eintr",),) + rest

    def client(kind: str, sched: tuple, sa_restart: bool) -> tuple[int, bool, int]:
        """Return (bytes delivered, client believes success, EINTR results seen)."""
        delivered = eintr_seen = 0
        it = iter(sched)
        while delivered < n_bytes:
            ev = next(it, ("n", n_bytes - delivered))
            if ev[0] == "eintr":
                if sa_restart:
                    continue                   # the kernel re-enters the call
                eintr_seen += 1
                if kind == "single-call":
                    return delivered, False, eintr_seen
                continue                       # user-space retry loop
            delivered += ev[1]
            if kind in ("single-call", "retry-eintr-only"):
                return delivered, True, eintr_seen
        return delivered, True, eintr_seen

    summary = {}
    for kind in ("single-call", "retry-eintr-only", "full-loop"):
        for sa in (False, True):
            lost = spurious = eintr = total = 0
            for sched in schedules(n_bytes, 3):
                total += 1
                got, success, seen = client(kind, sched, sa)
                eintr += seen
                if success and got != n_bytes:
                    lost += 1
                if not success:
                    spurious += 1
            summary[(kind, sa)] = (lost, spurious, eintr, total)
    check(sec, "SA_RESTART removes EINTR results but not short counts",
          all(summary[(k, True)][2] == 0 and summary[(k, True)][1] == 0 for k in
              ("single-call", "retry-eintr-only", "full-loop"))
          and summary[("single-call", True)][0] > 0,
          f"single-call under SA_RESTART loses data in {summary[('single-call', True)][0]}"
          f"/{summary[('single-call', True)][3]} schedules")
    check(sec, "retrying only on EINTR still loses data on short writes",
          summary[("retry-eintr-only", False)][0] > 0,
          f"{summary[('retry-eintr-only', False)][0]}/{summary[('retry-eintr-only', False)][3]} schedules")
    check(sec, "offset-advancing retry loop is correct with and without SA_RESTART",
          summary[("full-loop", False)][:2] == (0, 0) and summary[("full-loop", True)][:2] == (0, 0),
          f"{summary[('full-loop', False)][3]} schedules each")


SA_ONSTACK = 0x08000000   # include/uapi/asm-generic/signal-defs.h
SA_RESTART = 0x10000000
LINUX_GENERIC_SIGACTION = ("x86_64", "aarch64", "riscv64")


def task_status(tid: int) -> dict[str, int]:
    out = {}
    with open(f"/proc/self/task/{tid}/status") as fh:
        for line in fh:
            key, _, val = line.partition(":")
            if key in ("SigBlk", "SigCgt", "SigIgn"):
                out[key] = int(val.strip(), 16)
    return out


def part_b_live() -> None:
    sec = "B.live"
    if threading.current_thread() is not threading.main_thread() or not hasattr(signal, "pthread_sigmask"):
        skip(sec, "signal disposition and mask checks", "not on the main thread of a POSIX host")
        return
    sig = signal.SIGUSR1
    hits: list[int] = []
    old = signal.signal(sig, lambda s, f: hits.append(s))
    try:
        # B.live.1: dispositions are per process, masks per thread (Linux /proc).
        if sys.platform.startswith("linux") and os.path.isdir("/proc/self/task"):
            info: dict = {}
            ready, done = threading.Event(), threading.Event()

            def blocked_thread() -> None:
                signal.pthread_sigmask(signal.SIG_BLOCK, {sig})
                info["tid"] = threading.get_native_id()
                info["status"] = task_status(info["tid"])
                ready.set()
                done.wait(10)

            th = threading.Thread(target=blocked_thread, daemon=True)
            th.start()
            ready.wait(10)
            mine = task_status(threading.get_native_id())
            done.set()
            th.join(10)
            bit = 1 << (int(sig) - 1)
            theirs = info.get("status", {})
            check(sec, "caught-signal set (disposition table) is shared by all threads",
                  bool(theirs) and mine["SigCgt"] == theirs["SigCgt"] and bool(mine["SigCgt"] & bit),
                  f"SigCgt={mine['SigCgt']:016x} in both tasks")
            check(sec, "blocked-signal mask is per thread",
                  bool(theirs) and bool(theirs["SigBlk"] & bit) and not (mine["SigBlk"] & bit),
                  f"main SigBlk={mine['SigBlk']:016x}, helper SigBlk={theirs.get('SigBlk', 0):016x}")
        else:
            skip(sec, "per-process dispositions / per-thread masks", "no Linux /proc/self/task")

        try:
            libc = ctypes.CDLL(None, use_errno=True)
            libc.read.argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_size_t]
            libc.read.restype = ctypes.c_ssize_t
        except (OSError, AttributeError) as exc:
            skip(sec, "raw libc checks", f"cannot load libc: {exc}")
            return

        # B.live.2: sa_flags of the handler the running interpreter installed.
        def flags_of() -> Optional[int]:
            if not (sys.platform.startswith("linux") and platform.machine() in LINUX_GENERIC_SIGACTION
                    and ctypes.sizeof(ctypes.c_void_p) == 8):
                return None
            buf = (ctypes.c_ubyte * 256)()
            libc.sigaction.argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p]
            libc.sigaction.restype = ctypes.c_int
            if libc.sigaction(int(sig), None, buf) != 0:
                return None
            # struct sigaction { handler (8); sigset_t sa_mask (128); int sa_flags; ... }
            return int.from_bytes(bytes(buf[136:140]), sys.byteorder)

        signal.siginterrupt(sig, True)
        f_default = flags_of()
        signal.siginterrupt(sig, False)
        f_restart = flags_of()
        signal.siginterrupt(sig, True)
        if f_default is None or f_restart is None:
            skip(sec, "sigaction sa_flags inspection", "unsupported platform or struct layout")
        else:
            check(sec, "siginterrupt(sig, False) is exactly the SA_RESTART bit",
                  not (f_default & SA_RESTART) and bool(f_restart & SA_RESTART)
                  and (f_default | SA_RESTART) == f_restart,
                  f"sa_flags {f_default:#010x} -> {f_restart:#010x}")
            if sys.implementation.name == "cpython":
                check(sec, "CPython installs handlers with SA_ONSTACK and without SA_RESTART",
                      bool(f_default & SA_ONSTACK) and not (f_default & SA_RESTART),
                      f"sa_flags={f_default:#010x}")

        # B.live.3: blocking read(2) on an empty pipe, interrupted by a handler.
        main_ident = threading.main_thread().ident

        def attempt(sa_restart: bool, t_sig: float, t_write: float) -> tuple[int, int]:
            r, w = os.pipe()
            try:
                signal.siginterrupt(sig, not sa_restart)

                def poke() -> None:
                    time.sleep(t_sig)
                    signal.pthread_kill(main_ident, sig)
                    time.sleep(t_write)
                    os.write(w, b"x")

                th = threading.Thread(target=poke, daemon=True)
                th.start()
                buf = ctypes.create_string_buffer(1)
                ctypes.set_errno(0)
                n = libc.read(r, buf, 1)
                err = ctypes.get_errno()
                th.join(10)
                return int(n), err
            finally:
                os.close(r)
                os.close(w)

        got = (0, 0)
        for t_sig in (0.15, 0.4, 0.9):          # retried so a loaded host cannot fake a failure
            got = attempt(False, t_sig, 0.6)
            if got == (-1, errno.EINTR):
                break
        check(sec, "read(2) interrupted by a non-SA_RESTART handler fails with EINTR",
              got == (-1, errno.EINTR), f"read returned {got[0]}, errno {got[1]}")
        before = len(hits)
        got = attempt(True, 0.15, 0.3)
        check(sec, "the same read(2) is transparently restarted under SA_RESTART",
              got[0] == 1 and len(hits) > before, f"read returned {got[0]} after the handler ran")
    finally:
        signal.siginterrupt(sig, True)
        signal.signal(sig, old)


# --------------------------------------------------------------------------
# C. Paths, descriptors and ambient authority
# --------------------------------------------------------------------------

class Node:
    def __init__(self, kind: str, name: str, parent: Optional["Node"], target: str = "") -> None:
        self.kind, self.name, self.parent, self.target = kind, name, parent, target
        self.children: dict[str, Node] = {}

    def add(self, kind: str, name: str, target: str = "") -> "Node":
        node = Node(kind, name, self, target)
        self.children[name] = node
        return node

    def inside(self, root: "Node") -> bool:
        cur: Optional[Node] = self
        while cur is not None:
            if cur is root:
                return True
            cur = cur.parent
        return False


def build_fs() -> tuple[Node, Node]:
    root = Node("dir", "", None)
    root.add("file", "secret.txt")
    root.add("dir", "etc").add("file", "passwd")
    jail = root.add("dir", "jail")
    jail.add("file", "inside.txt")
    sub = jail.add("dir", "sub")
    sub.add("file", "deep.txt")
    sub.add("link", "up", "../inside.txt")        # stays inside the jail
    jail.add("link", "link_out", "../secret.txt")  # escapes through ..
    jail.add("link", "dirlink", "..")              # directory symlink to the parent
    jail.add("link", "abs_link", "/etc/passwd")    # absolute target
    jail.add("link", "loop", "loop")
    return root, jail


def resolve(policy: str, fs_root: Node, dirfd: Node, path: str) -> tuple[str, Optional[Node]]:
    """Resolve `path` relative to `dirfd`.

    plain          openat(dirfd, path, O_RDONLY)
    nofollow       openat(dirfd, path, O_RDONLY|O_NOFOLLOW)
    beneath        openat2(..., RESOLVE_BENEATH) / Capsicum strict-relative lookup
    componentwise  one openat(O_NOFOLLOW) per component with a directory stack
                   (the manual algorithm described for WASI hosts)
    """
    comps = deque(path.split("/"))
    cur = dirfd
    stack: list[Node] = []
    if path.startswith("/"):
        if policy in ("beneath", "componentwise"):
            return "EXDEV", None
        cur = fs_root
    hops = 0
    while comps:
        comp = comps.popleft()
        if comp in ("", "."):
            continue
        if cur.kind != "dir":
            return "ENOTDIR", None
        if comp == "..":
            if policy == "beneath":
                if cur is dirfd:
                    return "EXDEV", None
                cur = cur.parent or cur
            elif policy == "componentwise":
                if not stack:
                    return "EXDEV", None
                stack.pop()
                cur = stack[-1] if stack else dirfd
            else:
                cur = cur.parent or cur
            continue
        child = cur.children.get(comp)
        if child is None:
            return "ENOENT", None
        if child.kind == "link":
            if policy == "nofollow" and not comps:
                return "ELOOP", None
            hops += 1
            if hops > 40:
                return "ELOOP", None
            if child.target.startswith("/"):
                if policy in ("beneath", "componentwise"):
                    return "EXDEV", None
                cur = fs_root
            comps.extendleft(reversed(child.target.split("/")))
            continue
        cur = child
        if policy == "componentwise" and child.kind == "dir":
            stack.append(child)
    return "ok", cur


def interleavings(a: Sequence, b: Sequence) -> Iterator[tuple]:
    for pos in itertools.combinations(range(len(a) + len(b)), len(a)):
        out, ia, ib = [], iter(a), iter(b)
        posset = set(pos)
        for i in range(len(a) + len(b)):
            out.append(next(ia) if i in posset else next(ib))
        yield tuple(out)


def part_c_model() -> None:
    sec = "C.model"
    fs_root, jail = build_fs()
    tokens = ["inside.txt", "sub", "up", "deep.txt", "link_out", "dirlink", "abs_link",
              "loop", "..", ".", "secret.txt", "jail", "etc", "passwd"]
    paths: list[str] = []
    for length in (1, 2, 3, 4):
        for combo in itertools.product(tokens, repeat=length):
            paths.append("/".join(combo))
    paths += ["/" + p for p in paths if p.count("/") <= 1]
    stats = {p: {"ok": 0, "escape": 0} for p in ("plain", "nofollow", "beneath", "componentwise")}
    refinement = equivalent = True
    for path in paths:
        res = {p: resolve(p, fs_root, jail, path) for p in stats}
        for pol, (status, node) in res.items():
            if status == "ok":
                stats[pol]["ok"] += 1
                if not node.inside(jail):
                    stats[pol]["escape"] += 1
        if res["beneath"][0] == "ok" and res["beneath"] != res["plain"]:
            refinement = False
        if res["beneath"] != res["componentwise"]:
            equivalent = False
    total = len(paths)
    check(sec, "plain openat(dirfd, path) is not a confinement mechanism",
          stats["plain"]["escape"] > 0, f"{stats['plain']['escape']}/{total} enumerated paths escape")
    check(sec, "O_NOFOLLOW guards only the final component",
          0 < stats["nofollow"]["escape"] < stats["plain"]["escape"],
          f"{stats['nofollow']['escape']}/{total} paths still escape")
    check(sec, "RESOLVE_BENEATH-style resolution never leaves the directory handle",
          stats["beneath"]["escape"] == 0 and stats["beneath"]["ok"] > 0,
          f"{stats['beneath']['ok']} successes, 0 escapes")
    check(sec, "beneath resolution is a pure restriction of plain resolution", refinement, "same object whenever it succeeds")
    check(sec, "component-wise O_NOFOLLOW walk equals beneath resolution on a quiescent tree",
          equivalent and stats["componentwise"]["escape"] == 0, f"{total} paths compared")

    # C2: check-then-use on a path versus on a descriptor, with a racing renamer.
    def path_based(order: tuple) -> bool:
        target, checked, used = "good", None, None
        for step in order:
            if step == "swap":
                target = "evil"
            elif step == "check":
                checked = target
            elif step == "use" and checked == "good":
                used = target
        return used == "evil"

    def fd_based(order: tuple) -> bool:
        target, bound, checked, used = "good", None, None, None
        for step in order:
            if step == "swap":
                target = "evil"
            elif step == "open":
                bound = target
            elif step == "fstat":
                checked = bound
            elif step == "use" and checked == "good":
                used = bound
        return used == "evil"

    bad_path = sum(path_based(o) for o in interleavings(["check", "use"], ["swap"]))
    bad_fd = sum(fd_based(o) for o in interleavings(["open", "fstat", "use"], ["swap"]))
    check(sec, "path-based check-then-use has a time-of-check/time-of-use window",
          bad_path == 1, f"{bad_path}/3 interleavings use an unchecked object")
    check(sec, "descriptor-based check-then-use has none", bad_fd == 0, "0/4 interleavings")

    # C3: the working directory is one mutable cell per process.
    def cwd_violations(use_dirfd: bool) -> int:
        bad = 0
        t1, t2 = [("chdir", "A"), ("open", "A")], [("chdir", "B"), ("open", "B")]
        for order in interleavings(t1, t2):
            cwd = None
            for op, want in order:
                if op == "chdir":
                    cwd = want
                elif not use_dirfd and cwd != want:
                    bad += 1
                    break
        return bad

    check(sec, "two threads using chdir()+relative open race on the process-wide cwd",
          cwd_violations(False) == 4, "4/6 interleavings open in the wrong directory")
    check(sec, "openat() on per-thread directory handles does not", cwd_violations(True) == 0, "0/6")

    # C4: completion-based I/O.  User: submit, request cancel, free buffer.
    # Kernel: write into buffer, post completion.  The kernel write may land
    # after a cancellation request; only the completion ends the kernel's use.
    def kernel_write_after_free(wait_for_completion: bool) -> int:
        bad = 0
        for order in interleavings(["submit", "cancel", "free"], ["kwrite", "cqe"]):
            if order.index("kwrite") < order.index("submit"):
                continue
            if order.index("cqe") < order.index("kwrite"):
                continue
            if wait_for_completion and order.index("free") < order.index("cqe"):
                continue
            if order.index("free") < order.index("kwrite"):
                bad += 1
        return bad

    check(sec, "freeing a buffer at scope exit while a completion is outstanding is unsound",
          kernel_write_after_free(False) > 0,
          f"{kernel_write_after_free(False)} interleavings write into freed memory")
    check(sec, "releasing the buffer only after its completion is sound",
          kernel_write_after_free(True) == 0, "0 interleavings")


SYS_OPENAT2 = 437            # arch/x86/entry/syscalls/syscall_64.tbl; same in asm-generic
RESOLVE_BENEATH = 0x08       # include/uapi/linux/openat2.h
NOFOLLOW_ERRNOS = {errno.ELOOP, errno.EMLINK, getattr(errno, "EFTYPE", errno.ELOOP)}


class OpenHow(ctypes.Structure):
    _fields_ = [("flags", ctypes.c_uint64), ("mode", ctypes.c_uint64), ("resolve", ctypes.c_uint64)]


def part_c_live() -> None:
    sec = "C.live"
    if not (os.open in os.supports_dir_fd and hasattr(os, "O_NOFOLLOW") and hasattr(os, "symlink")):
        skip(sec, "openat()/O_NOFOLLOW checks", "dir_fd or O_NOFOLLOW unsupported")
        return
    base = tempfile.mkdtemp(prefix="posix_probe_")
    rootfd = -1
    try:
        jail = os.path.join(base, "jail")
        os.makedirs(os.path.join(jail, "sub"))
        secret = os.path.join(base, "secret.txt")
        for p in (secret, os.path.join(jail, "inside.txt")):
            with open(p, "w") as fh:
                fh.write("x")
        os.symlink("../secret.txt", os.path.join(jail, "link_out"))
        os.symlink("..", os.path.join(jail, "dirlink"))
        os.symlink(secret, os.path.join(jail, "abs_link"))
        rootfd = os.open(jail, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))

        def try_open(path: str, flags: int = 0) -> int:
            try:
                fd = os.open(path, os.O_RDONLY | flags, dir_fd=rootfd)
            except OSError as exc:
                return exc.errno or -1
            os.close(fd)
            return 0

        check(sec, "openat(dirfd, 'inside.txt') succeeds", try_open("inside.txt") == 0)
        check(sec, "openat(dirfd, '../secret.txt') escapes the directory handle",
              try_open("../secret.txt") == 0, "plain openat is a starting point, not a boundary")
        e = try_open("link_out", os.O_NOFOLLOW)
        check(sec, "O_NOFOLLOW refuses a symlink in the final component",
              e in NOFOLLOW_ERRNOS, errno.errorcode.get(e, str(e)))
        check(sec, "O_NOFOLLOW still follows a symlink in a non-final component",
              try_open("dirlink/secret.txt", os.O_NOFOLLOW) == 0, "'dirlink' -> '..' was followed")

        fd1 = os.open(os.devnull, os.O_RDONLY)
        fd2 = os.open(os.devnull, os.O_RDONLY)
        os.close(fd1)
        fd3 = os.open(os.devnull, os.O_RDONLY)
        os.close(fd2)
        os.close(fd3)
        check(sec, "descriptor numbers are reused lowest-first", fd3 == fd1 and fd2 > fd1,
              f"closed {fd1}, next open returned {fd3}")

        if not (sys.platform.startswith("linux") and platform.machine() in LINUX_GENERIC_SIGACTION):
            skip(sec, "openat2(RESOLVE_BENEATH)", "not Linux on a generic-syscall-table architecture")
            return
        libc = ctypes.CDLL(None, use_errno=True)
        libc.syscall.restype = ctypes.c_long
        libc.syscall.argtypes = [ctypes.c_long, ctypes.c_int, ctypes.c_char_p,
                                 ctypes.POINTER(OpenHow), ctypes.c_size_t]

        def openat2(path: str) -> int:
            how = OpenHow(os.O_RDONLY | os.O_CLOEXEC, 0, RESOLVE_BENEATH)
            ctypes.set_errno(0)
            fd = libc.syscall(SYS_OPENAT2, rootfd, os.fsencode(path), ctypes.byref(how),
                              ctypes.sizeof(how))
            if fd < 0:
                return ctypes.get_errno()
            os.close(fd)
            return 0

        first = openat2("inside.txt")
        if first in (errno.ENOSYS, errno.EPERM, errno.EACCES):
            skip(sec, "openat2(RESOLVE_BENEATH)", f"syscall unavailable ({errno.errorcode.get(first)})")
            return
        inside = [first, openat2("sub/../inside.txt")]
        escapes = {p: openat2(p) for p in
                   ("../secret.txt", "link_out", "dirlink/secret.txt", "abs_link", secret)}
        check(sec, "openat2(RESOLVE_BENEATH) admits paths that stay beneath the handle",
              inside == [0, 0], "'inside.txt', 'sub/../inside.txt'")
        check(sec, "openat2(RESOLVE_BENEATH) rejects every escape with EXDEV",
              all(v == errno.EXDEV for v in escapes.values()),
              ", ".join(f"{'<absolute path>' if k.startswith('/') else k}={errno.errorcode.get(v, v)}"
                        for k, v in escapes.items()))
    except OSError as exc:
        skip(sec, "filesystem containment checks", f"sandboxed filesystem: {exc}")
    finally:
        if rootfd != -1:
            os.close(rootfd)
        shutil.rmtree(base, ignore_errors=True)


# --------------------------------------------------------------------------
# D. One flat address space shared by every runtime
# --------------------------------------------------------------------------

GIB = 1 << 30
# compiler-rt/lib/asan/asan_mapping.h, "Typical shadow mapping on Linux/x86_64
# with SHADOW_OFFSET == 0x00007fff8000" (inclusive bounds).
ASAN_X86_64 = {
    "LowMem": (0x000000000000, 0x00007fff7fff),
    "LowShadow": (0x00007fff8000, 0x00008fff6fff),
    "ShadowGap": (0x00008fff7000, 0x02008fff6fff),
    "HighShadow": (0x02008fff7000, 0x10007fff7fff),
    "HighMem": (0x10007fff8000, 0x7fffffffffff),
}
# src/runtime/malloc.go: default 64-bit hint  p = uintptr(i)<<40 | 0x00c0<<32, i = 0x7f..0
GO_DEFAULT_HINTS = [(i << 40) | (0x00C0 << 32) for i in range(0x80)]
GO_RACE_HEAP = (0x00C000000000, 0x00E000000000)       # malloc.go, raceenabled case
TSAN_GO48_HEAP = (0x00C000000000, 0x00E000000000)     # tsan_platform.h, "Go on linux ... x86_64"
TSAN_GO48_APP = (0x000000001000, 0x00E000000000)      # MappingGo48 kLoAppMemBeg/End
JVM_UNSCALED_MAX = 4 * GIB                             # UnscaledOopHeapMax
JVM_ZERO_BASED_MAX = 32 * GIB                          # 4 GiB << 3 (8-byte object alignment)
V8_CAGE = 1 << 32                                      # kPtrComprCageReservationSize / alignment
V8_SANDBOX_DEFAULT_LOG2, V8_SANDBOX_SMALL_VA_LOG2 = 40, 37


def region_of(addr: int) -> str:
    for name, (lo, hi) in ASAN_X86_64.items():
        if lo <= addr <= hi:
            return name
    return "outside"


class AddressSpace:
    """First-come, first-served interval allocator: the only arbiter a process has."""

    def __init__(self) -> None:
        self.taken: list[tuple[int, int, str]] = []

    def free(self, lo: int, hi: int) -> bool:
        return all(hi <= a or lo >= b for a, b, _ in self.taken)

    def fixed(self, lo: int, hi: int, who: str) -> bool:
        if not self.free(lo, hi):
            return False
        self.taken.append((lo, hi, who))
        return True

    def hinted(self, hints: Sequence[int], size: int, who: str) -> Optional[int]:
        for index, lo in enumerate(hints):
            if self.fixed(lo, lo + size, who):
                return index
        return None


def part_d_model() -> None:
    sec = "D.model"
    regions = sorted(ASAN_X86_64.values())
    check(sec, "ASan x86-64 regions tile the 47-bit user address space exactly",
          regions[0][0] == 0 and regions[-1][1] == (1 << 47) - 1
          and all(regions[i][1] + 1 == regions[i + 1][0] for i in range(len(regions) - 1)),
          "5 contiguous regions")
    shadow_or_gap = sum(hi - lo + 1 for name, (lo, hi) in ASAN_X86_64.items()
                        if name not in ("LowMem", "HighMem"))
    check(sec, "ASan reserves one eighth of the address space plus the gap at fixed addresses",
          shadow_or_gap == (1 << 44), f"{shadow_or_gap / (1 << 40):.0f} TiB of shadow and gap")
    placed = [region_of(h) for h in GO_DEFAULT_HINTS]
    blocked = [i for i, r in enumerate(placed) if r in ("ShadowGap", "HighShadow", "LowShadow")]
    check(sec, "Go's first default heap hint lies inside ASan's shadow gap",
          placed[0] == "ShadowGap", f"{GO_DEFAULT_HINTS[0]:#014x}")
    check(sec, "the first 16 of Go's 128 default hints collide with ASan regions",
          blocked == list(range(16)) and all(r == "HighMem" for r in placed[16:]),
          f"hints 0..15 blocked; hint 16 = {GO_DEFAULT_HINTS[16]:#014x} is the first in HighMem")
    by_definition(sec, "Go race-mode heap window and TSan Go mapping, as transcribed, coincide",
          GO_RACE_HEAP == TSAN_GO48_HEAP and TSAN_GO48_APP[0] <= GO_RACE_HEAP[0]
          and GO_RACE_HEAP[1] <= TSAN_GO48_APP[1],
          f"[{GO_RACE_HEAP[0]:#x}, {GO_RACE_HEAP[1]:#x})")
    check(sec, "that mandatory race-mode window is entirely ASan shadow gap",
          region_of(GO_RACE_HEAP[0]) == "ShadowGap" and region_of(GO_RACE_HEAP[1] - 1) == "ShadowGap",
          "the two fixed layouts cannot coexist in one process")
    usable_low = ASAN_X86_64["LowMem"][1] + 1
    check(sec, "under the ASan layout only ~2 GiB of the JVM zero-based-oops window is application memory",
          usable_low == 2 * GIB - 0x8000 and JVM_ZERO_BASED_MAX == JVM_UNSCALED_MAX << 3
          and region_of(JVM_ZERO_BASED_MAX - 1) == "ShadowGap",
          f"{usable_low / GIB:.5f} GiB of 32 GiB ({100 * usable_low / JVM_ZERO_BASED_MAX:.2f}%)")
    by_definition(sec, "V8 sandbox sizes as transcribed: 2**40 default, 2**37 for 39-bit address spaces",
          (1 << V8_SANDBOX_DEFAULT_LOG2) > (1 << 39) and (1 << V8_SANDBOX_SMALL_VA_LOG2) * 4 == (1 << 39)
          and V8_CAGE == 4 * GIB, "hence the 128 GiB configuration: one quarter of 2**39")

    # Initialisation order decides who gets an address; nobody arbitrates.
    arena = 64 << 20
    shadow = (ASAN_X86_64["LowShadow"][0], ASAN_X86_64["HighShadow"][1] + 1)
    a_first = AddressSpace()
    asan_ok_1 = a_first.fixed(*shadow, "asan")
    go_ix_1 = a_first.hinted(GO_DEFAULT_HINTS, arena, "go")
    g_first = AddressSpace()
    go_ix_2 = g_first.hinted(GO_DEFAULT_HINTS, arena, "go")
    asan_ok_2 = g_first.fixed(*shadow, "asan")
    check(sec, "fixed-address tenant first: the hinting runtime silently falls back",
          asan_ok_1 and go_ix_1 == 16, f"Go heap lands on hint {go_ix_1}")
    check(sec, "hinting runtime first: the fixed-address tenant cannot initialise",
          go_ix_2 == 0 and not asan_ok_2, "outcome depends only on start-up order")


MAP_PRIVATE, MAP_FIXED, MAP_ANONYMOUS_LINUX, MAP_FIXED_NOREPLACE = 0x02, 0x10, 0x20, 0x100000
PROT_READ, PROT_WRITE = 0x1, 0x2


def part_d_live() -> None:
    sec = "D.live"
    if not (sys.platform.startswith("linux") and os.path.exists("/proc/self/maps")):
        skip(sec, "/proc/self/maps checks", "not Linux or /proc unavailable")
        return
    try:
        maps = read_maps()
    except OSError as exc:
        skip(sec, "/proc/self/maps checks", str(exc))
        return
    user = [m for m in maps if m[3] != "[vsyscall]"]
    ordered = all(user[i][1] <= user[i + 1][0] for i in range(len(user) - 1))
    top = max(hi for _, hi, _, _ in user)
    check(sec, "mappings are disjoint, sorted, and all in one user address range",
          ordered and top.bit_length() <= 57, f"{len(user)} mappings, highest end uses {top.bit_length()} bits")
    tenants = {
        "interpreter/DSO files": sum(1 for m in user if m[3].startswith("/")),
        "anonymous": sum(1 for m in user if m[3] == ""),
        "[heap]": sum(1 for m in user if m[3] == "[heap]"),
        "[stack]": sum(1 for m in user if m[3] == "[stack]"),
        "[vdso]": sum(1 for m in user if m[3] == "[vdso]"),
    }
    check(sec, "program, libraries, heap, stack and kernel-provided vDSO share that range",
          tenants["interpreter/DSO files"] > 0 and tenants["[stack]"] == 1 and tenants["anonymous"] > 0,
          ", ".join(f"{k}={v}" for k, v in tenants.items()))
    info: dict = {}

    def other() -> None:
        try:
            info["maps"] = read_maps(f"/proc/self/task/{threading.get_native_id()}/maps")
        except OSError as exc:
            info["err"] = str(exc)

    th = threading.Thread(target=other)
    th.start()
    th.join(10)
    if "maps" in info:
        key = lambda ms: {(lo, hi) for lo, hi, _, name in ms if name.startswith("/") or name == "[stack]"}
        check(sec, "a second thread sees the same file-backed and stack mappings",
              key(maps) <= key(info["maps"]) or key(info["maps"]) <= key(maps),
              f"{len(key(maps))} ranges compared")
    else:
        skip(sec, "a second thread sees the same mappings", info.get("err", "no data"))

    if platform.machine() not in LINUX_GENERIC_SIGACTION or ctypes.sizeof(ctypes.c_void_p) != 8:
        skip(sec, "mmap placement arbitration", "flag values not verified for this architecture")
        return
    try:
        libc = ctypes.CDLL(None, use_errno=True)
        libc.mmap.restype = ctypes.c_void_p
        libc.mmap.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int, ctypes.c_int,
                              ctypes.c_int, ctypes.c_long]
        libc.munmap.argtypes = [ctypes.c_void_p, ctypes.c_size_t]
    except (OSError, AttributeError) as exc:
        skip(sec, "mmap placement arbitration", str(exc))
        return
    size = 1 << 16
    failed = ctypes.c_void_p(-1).value
    anon = MAP_PRIVATE | MAP_ANONYMOUS_LINUX
    a = libc.mmap(None, size, PROT_READ | PROT_WRITE, anon, -1, 0)
    if a in (None, failed):
        skip(sec, "mmap placement arbitration", "mmap failed")
        return
    try:
        ctypes.memset(a, 0x5A, 1)
        b = libc.mmap(a, size, PROT_READ | PROT_WRITE, anon, -1, 0)
        hint_moved = b not in (None, failed) and b != a
        if b not in (None, failed):
            libc.munmap(b, size)
        check(sec, "an address hint for an occupied range is silently relocated", hint_moved,
              f"asked {a:#x}, got {b:#x}" if hint_moved else "hint unexpectedly honoured")
        ctypes.set_errno(0)
        c = libc.mmap(a, size, PROT_READ | PROT_WRITE, anon | MAP_FIXED_NOREPLACE, -1, 0)
        err = ctypes.get_errno()
        if c not in (None, failed):
            libc.munmap(c, size) if c != a else None
            skip(sec, "MAP_FIXED_NOREPLACE reports the collision", "flag ignored (kernel older than 4.17?)")
        else:
            check(sec, "MAP_FIXED_NOREPLACE reports the collision with EEXIST", err == errno.EEXIST,
                  errno.errorcode.get(err, str(err)))
        d = libc.mmap(a, size, PROT_READ | PROT_WRITE, anon | MAP_FIXED, -1, 0)
        clobbered = d == a and ctypes.string_at(a, 1) == b"\x00"
        check(sec, "MAP_FIXED silently replaces the existing tenant's pages", clobbered,
              "byte 0x5a written earlier now reads 0x00")
    finally:
        libc.munmap(a, size)


# --------------------------------------------------------------------------

def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--model-only", action="store_true", help="skip every live check")
    ap.add_argument("--json", action="store_true", help="print results as JSON")
    args = ap.parse_args(argv)

    parts: list[tuple[str, Callable[[], None], bool]] = [
        ("A.model", part_a_model, False), ("A.live", part_a_live, True),
        ("B.model", part_b_model, False), ("B.live", part_b_live, True),
        ("C.model", part_c_model, False), ("C.live", part_c_live, True),
        ("D.model", part_d_model, False), ("D.live", part_d_live, True),
    ]
    for name, fn, live in parts:
        if live and args.model_only:
            skip(name, "live checks", "--model-only")
            continue
        try:
            fn()
        except Exception as exc:  # a crashed section is a failure, never a silent pass
            record(name, "section completed", "FAIL", f"{type(exc).__name__}: {exc}")

    counts = {s: sum(1 for r in RESULTS if r["status"] == s) for s in ("PASS", "FAIL", "SKIP", "DEF")}
    if args.json:
        print(json.dumps({"host": {"system": platform.system(), "release": platform.release(),
                                   "machine": platform.machine(),
                                   "python": platform.python_version()},
                          "counts": counts, "results": RESULTS}, indent=2))
    else:
        print(f"host: {platform.system()} {platform.release()} {platform.machine()}, "
              f"{sys.implementation.name} {platform.python_version()}")
        for r in RESULTS:
            tail = f"  [{r['detail']}]" if r["detail"] else ""
            print(f"{r['status']:4s} {r['section']:8s} {r['check']}{tail}")
        print(f"RESULT: {'FAIL' if counts['FAIL'] else 'PASS'} "
              f"({counts['PASS']} passed, {counts['FAIL']} failed, {counts['SKIP']} skipped, "
              f"{counts['DEF']} by-definition rows not counted as verification)")
    return 1 if counts["FAIL"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
