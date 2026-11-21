"""Probe: how many dropped top-level function objects stay allocated until a
cyclic-GC pass, in a free-threaded (no-GIL) CPython build versus a default
(GIL) build of the same source revision.

Run with each interpreter:  <python> deferred_rc_probe.py
Prints one JSON line.  Basis: execution of the real interpreter.

Mechanism under test (CPython source, pinned revision): PyFunction_NewWithQualName
marks functions whose code object lacks CO_NESTED (top-level functions) with
deferred reference counting; deferred objects carry a large bias in
ob_ref_shared, so ordinary decrefs never reach zero and only the cyclic GC
can free them.  In a GIL build the marking is a no-op.
"""
import gc, json, sys, types, weakref
import _tracemalloc as tracemalloc  # builtin; avoids importing extension modules

N = 200_000
code = compile("def f():\n    return 1\n", "<probe>", "exec")
fcode = next(c for c in code.co_consts if isinstance(c, types.CodeType))
# Control: a nested function's code object carries CO_NESTED, so the
# interpreter does not mark its function objects for deferred counting.
outer = compile("def outer():\n    def f():\n        return 1\n    return f\n", "<probe>", "exec")
ocode = next(c for c in outer.co_consts if isinstance(c, types.CodeType))
ncode = next(c for c in ocode.co_consts if isinstance(c, types.CodeType))
CO_NESTED = 0x10

def alive(refs):
    return sum(1 for r in refs if r() is not None)

def run(gc_enabled, codeobj=None):
    codeobj = codeobj or fcode
    gc.collect()
    if gc_enabled:
        gc.enable()
    else:
        gc.disable()
    tracemalloc.start()
    base = tracemalloc.get_traced_memory()[0]
    refs = []
    peak_alive = 0
    for i in range(N):
        fn = types.FunctionType(codeobj, {})
        refs.append(weakref.ref(fn))
        del fn
        if gc_enabled and (i & 1023) == 0:
            peak_alive = max(peak_alive, alive(refs[-4096:]))
    after_drop_alive = alive(refs)
    after_drop_bytes = tracemalloc.get_traced_memory()[0] - base
    gc.collect()
    after_gc_alive = alive(refs)
    del refs
    gc.collect()
    after_gc_bytes = tracemalloc.get_traced_memory()[0] - base
    tracemalloc.stop()
    gc.enable()
    return dict(gc_enabled=gc_enabled, code_is_nested=bool(codeobj.co_flags & CO_NESTED), created=N,
                alive_after_drop=after_drop_alive,
                traced_bytes_after_drop=after_drop_bytes,
                alive_after_gc_collect=after_gc_alive,
                traced_bytes_after_collect_and_refs_freed=after_gc_bytes,
                sampled_alive_in_last_4096_max=peak_alive if gc_enabled else None)

out = dict(version=sys.version.split()[0],
           free_threading_build=("free-threading" in sys.version),
           gil_enabled_at_runtime=(sys._is_gil_enabled() if hasattr(sys, "_is_gil_enabled") else True),
           gc_threshold=gc.get_threshold(),
           runs=[run(False), run(True), run(False, ncode)])
print(json.dumps(out))
