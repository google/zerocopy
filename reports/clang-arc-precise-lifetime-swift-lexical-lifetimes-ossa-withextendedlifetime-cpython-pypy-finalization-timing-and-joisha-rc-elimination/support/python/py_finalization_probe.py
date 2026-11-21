"""Release-timing probe for a reference-counted Python implementation.

Each scenario prints an ordered event log; the question is where the
finalizer / weakref callback / resource close happens relative to the
marker lines. Run with:  python3 -X dev py_finalization_probe.py
Only the standard library is used.
"""
import gc
import os
import socket
import sys
import sysconfig
import tempfile
import time
import weakref

LOG = []


def ev(msg):
    LOG.append(msg)
    print("   ", msg)


class Res:
    def __init__(self, name):
        self.name = name

    def __del__(self):
        ev(f"__del__ {self.name}")


def scenario_local_last_use():
    x = Res("local")
    weakref.finalize(x, ev, "weakref.finalize callback local")
    ev(f"use {x.name}")
    ev("marker after last use (x still bound)")
    # no further use of x; the function returns next


def scenario_del_statement():
    x = Res("del")
    ev(f"use {x.name}")
    del x
    ev("marker after del")


def scenario_temporary():
    Res("temp").name
    ev("marker after expression statement")


def scenario_rebind():
    x = Res("first")
    x = Res("second")
    ev("marker after rebinding x")
    return x.name


def scenario_cycle():
    a = Res("cycle-a")
    b = Res("cycle-b")
    a.peer, b.peer = b, a
    del a, b
    ev("marker after dropping both names (cycle remains)")
    n = gc.collect()
    ev(f"gc.collect() returned {n}")


def scenario_exception_keeps_frame():
    def inner():
        y = Res("in-raising-frame")
        raise ValueError("boom")

    try:
        inner()
    except ValueError as e:
        ev("in except clause (traceback references inner frame)")
    ev("marker after except clause (name e is unbound at clause end)")


def scenario_generator_finally():
    def gen():
        try:
            yield 1
            yield 2
        finally:
            ev("generator finally block ran")

    g = gen()
    next(g)
    ev("generator suspended inside try")
    del g
    ev("marker after del of suspended generator")


def scenario_file_flush(path):
    f = open(path, "w")
    f.write("hello")  # stays in the userspace buffer until flush/close
    size_before = os.path.getsize(path)
    del f
    size_after = os.path.getsize(path)
    ev(f"file size before drop={size_before} after drop={size_after}")


def scenario_socket_fd():
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    fd = s.fileno()
    del s
    try:
        os.fstat(fd)
        state = "still open"
    except OSError:
        state = "closed"
    ev(f"socket fd {fd} after drop: {state}")


def timing():
    class Plain:
        __slots__ = ("v",)

    class WithDel:
        __slots__ = ("v",)

        def __del__(self):
            pass

    def loop(cls, n):
        t0 = time.perf_counter()
        for i in range(n):
            o = cls()
            o.v = i
        return time.perf_counter() - t0

    n = 1_000_000
    tp = min(loop(Plain, n) for _ in range(5))
    td = min(loop(WithDel, n) for _ in range(5))
    print(f"    create+drop 1e6 objects (best of 5): plain {tp*1e9/n:.1f} ns/obj, "
          f"with __del__ {td*1e9/n:.1f} ns/obj")

    class Node:
        pass

    gc.collect()
    gc.disable()
    k = 100_000
    for _ in range(k):
        a, b = Node(), Node()
        a.p, b.p = b, a
    del a, b
    t0 = time.perf_counter()
    freed = gc.collect()
    t1 = time.perf_counter()
    gc.enable()
    print(f"    gc.collect() over {k} two-object cycles: {freed} objects, {(t1-t0)*1e3:.1f} ms")


def main():
    print(f"implementation={sys.implementation.name} version={sys.version.split()[0]} "
          f"Py_GIL_DISABLED={sysconfig.get_config_var('Py_GIL_DISABLED')} "
          f"gc_thresholds={gc.get_threshold()}")
    for fn in (scenario_local_last_use, scenario_del_statement, scenario_temporary,
               scenario_rebind, scenario_cycle, scenario_exception_keeps_frame,
               scenario_generator_finally):
        print(fn.__name__)
        fn()
        ev(f"returned from {fn.__name__}")
    with tempfile.TemporaryDirectory() as d:
        print("scenario_file_flush")
        scenario_file_flush(os.path.join(d, "out.txt"))
    print("scenario_socket_fd")
    scenario_socket_fd()
    print("timing")
    timing()


if __name__ == "__main__":
    main()
