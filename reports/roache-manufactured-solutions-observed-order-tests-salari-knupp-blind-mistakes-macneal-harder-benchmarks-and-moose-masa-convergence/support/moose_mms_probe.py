#!/usr/bin/env python3
"""Probe the MOOSE `python/mms` package (pinned revision) without a MOOSE build.

Runs the real upstream files `runner.py`, `evaluate.py`, `fparser.py`,
`ConvergencePlot.py` and `test/test_mms.py`, replacing only the `mooseutils`
dependency with a stub whose `run_executable` writes a CSV the way a MOOSE app
with `Outputs/csv=true` would. Usage:

    python3 moose_mms_probe.py <dir containing the upstream mms/ package>

Checks:
  P1  run_spatial(..., csv=<name>) with an explicit csv argument.
  P2  run_temporal(...): the dt recorded in the returned DataFrame versus the
      dt passed to each run, and whether the fitted slope is affected.
  P3  the IOError message when the CSV is missing.
  P4  evaluate(): manufactured source term for a variable-coefficient
      advection-diffusion-reaction operator, compared with a hand derivation.
  P5  ConvergencePlot._fit on synthetic data with known slope.
  P6  test_mms.py::testExceptions against a mutant evaluate.py whose
      _check_reserved() is a no-op (is the test non-vacuous?).
"""
import importlib
import io
import os
import shutil
import sys
import tempfile
import types
import unittest
import contextlib

src = os.path.abspath(sys.argv[1])

# ---------------------------------------------------------------- stub mooseutils
calls = []
stub = types.ModuleType("mooseutils")


def run_executable(exe, *args, mpi=None, suppress_output=False):
    calls.append(list(args))
    # emulate an MMS run: error = C * h^2 (spatial) or C * dt^2 (temporal)
    refine = [a for a in args if a.startswith("Mesh/uniform_refine=")]
    dtarg = [a for a in args if a.startswith("Executioner/dt=")]
    base = [a for a in args if a.startswith("Outputs/file_base=")]
    inp = args[args.index("-i") + 1]
    out = base[0].split("=", 1)[1] + ".csv" if base else inp.replace(".i", "_out.csv")
    if refine:
        h = 0.125 / 2 ** int(refine[0].split("=")[1])
        err = 3.0 * h ** 2
    else:
        h = 0.125
        dt = float(dtarg[0].split("=")[1])
        err = 5.0 * dt ** 2
    with open(out, "w") as f:
        f.write("time,h,error\n0,%r,%r\n" % (h, err))
    with open("explicit_name.csv", "w") as f:
        f.write("time,h,error\n0,%r,%r\n" % (h, err))
    return 0


stub.run_executable = run_executable
stub.find_moose_executable_recursive = lambda d: "/bin/true"
stub.find_moose_executable = lambda d: "/bin/true"
sys.modules["mooseutils"] = stub

work = tempfile.mkdtemp(prefix="mms_probe_")
try:
    shutil.copytree(os.path.join(src, "mms"), os.path.join(work, "mms"))
    sys.path.insert(0, work)
    os.chdir(work)
    open("mms_spatial.i", "w").write("# dummy input\n")
    import mms  # noqa: E402

    print("== P1 run_spatial with explicit csv= argument")
    try:
        df = mms.run_spatial("mms_spatial.i", 2, console=False, executable="/bin/true", csv="explicit_name.csv")
        print("returned:\n", df)
    except Exception as e:  # report the exact exception type and message
        print("EXCEPTION:", type(e).__name__, "-", e)

    print("== P2 run_temporal: recorded dt versus dt passed to each run")
    calls.clear()
    df = mms.run_temporal("mms_spatial.i", 3, console=False, executable="/bin/true", dt=0.1)
    passed = [float([a for a in c if a.startswith("Executioner/dt=")][0].split("=")[1]) for c in calls]
    print("dt passed to runs :", passed)
    print("x column recorded :", list(df[df.columns[0]]), "(column name %r)" % df.columns[0])
    import numpy as np
    s_rec = np.polyfit(np.log10(df[df.columns[0]]), np.log10(df["error"]), 1)[0]
    s_true = np.polyfit(np.log10(passed), np.log10(df["error"]), 1)[0]
    print("slope vs recorded x = %.6f ; slope vs passed dt = %.6f" % (s_rec, s_true))

    print("== P3 missing-CSV error message")
    saved = stub.run_executable
    stub.run_executable = lambda *a, **k: 0
    for fn in ("mms_spatial_out.csv",):
        if os.path.exists(fn):
            os.remove(fn)
    try:
        mms.run_spatial("mms_spatial.i", 1, console=False, executable="/bin/true")
    except Exception as e:
        print("EXCEPTION:", type(e).__name__, "-", e)
    stub.run_executable = saved

    print("== P4 evaluate(): -div(k*grad(u)) + c*diff(u,x) + r*u with k = 1 + x/2")
    f, s = mms.evaluate("-div(k*grad(u)) + c*diff(u, x) + r*u", "sin(3*x)*exp(x)",
                        scalars=["c", "r"], k="1 + x/2")
    print("fparser(f) =", mms.fparser(f))
    import sympy as sp
    X, C, Rr = sp.symbols("X c r")
    U = sp.sin(3 * X) * sp.exp(X)
    K = 1 + X / 2
    hand = -sp.diff(K * sp.diff(U, X), X) + C * sp.diff(U, X) + Rr * U
    from sympy.vector import CoordSys3D  # noqa: F401
    fx = sp.simplify(f.subs({list(f.free_symbols - {sp.Symbol('c'), sp.Symbol('r')})[0]: X}) - hand) \
        if len(f.free_symbols - {sp.Symbol('c'), sp.Symbol('r')}) == 1 else None
    print("evaluate() minus hand derivation simplifies to:", fx)

    print("== P5 ConvergencePlot._fit on synthetic data (slope 2 by construction)")
    import pandas as pd
    hs = np.array([0.1, 0.05, 0.025, 0.0125])
    data = pd.DataFrame({"h": hs, "e": 7.0 * hs ** 2 * (1 + 0.3 * hs)})
    fig = mms.ConvergencePlot(xlabel="h", ylabel="e")
    fig.plot(data, label="toy", num_fitted_points=3)
    print("label_to_slope:", {k: round(v, 6) for k, v in fig.label_to_slope.items()})

    print("== P6 test_mms.py::testExceptions vs a no-op _check_reserved mutant")
    shutil.copy(os.path.join(src, "mms", "test", "test_mms.py"), os.path.join(work, "test_mms.py"))
    ev = os.path.join(work, "mms", "evaluate.py")
    text = open(ev).read()
    mutant = text.replace('def _check_reserved(var):\n    """Error checking for input variables."""\n',
                          'def _check_reserved(var):\n    """Error checking for input variables."""\n    return\n')
    assert mutant != text, "mutation anchor not found"
    tsrc = open(os.path.join(work, "test_mms.py")).read()
    # P6b: same test, but with 'k' declared so the inputs are otherwise valid
    tvariant = tsrc.replace('scalars=["R"], h=', 'scalars=["R", "k"], h=') \
                   .replace('scalars=["x"], h=', 'scalars=["x", "k"], h=') \
                   .replace('scalars=["t"], h=', 'scalars=["t", "k"], h=') \
                   .replace('scalars=["e_k"], h=', 'scalars=["e_k", "k"], h=')
    assert tvariant != tsrc
    for tlabel, tbody in (("upstream test", tsrc), ("test with k declared", tvariant)):
        open(os.path.join(work, "test_mms.py"), "w").write(tbody)
        for label, body in (("original", text), ("mutant", mutant)):
            open(ev, "w").write(body)
            for m in [k for k in list(sys.modules) if k == "mms" or k.startswith("mms.") or k == "test_mms"]:
                del sys.modules[m]
            import test_mms  # noqa: E402
            suite = unittest.TestSuite([test_mms.TestMMS("testExceptions")])
            buf = io.StringIO()
            res = unittest.TextTestRunner(stream=buf, verbosity=0).run(suite)
            print("%-21s %-8s evaluate.py -> testExceptions: run=%d failures=%d errors=%d" % (
                tlabel, label, res.testsRun, len(res.failures), len(res.errors)))
            for _, tb in res.errors + res.failures:
                print("   last line:", tb.strip().splitlines()[-1])
finally:
    os.chdir("/")
    shutil.rmtree(work, ignore_errors=True)
