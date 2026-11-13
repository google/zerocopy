#!/usr/bin/env python3
"""Revalidation probe for Lean 4.34.1 native compilation pipeline, runtime, and trust surface."""
import hashlib
import os
import subprocess
import tempfile

def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

def main() -> None:
    here = os.path.dirname(os.path.abspath(__file__))
    probe_lean = os.path.join(here, "LeanNativeCompilationAndTrustProbe.lean")
    lean_tc = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.34.1")
    lean_bin = os.path.join(lean_tc, "bin/lean")
    leanc_bin = os.path.join(lean_tc, "bin/leanc")

    with tempfile.TemporaryDirectory() as tmp:
        d1 = os.path.join(tmp, "d1")
        d2 = os.path.join(tmp, "d2")
        os.makedirs(d1)
        os.makedirs(d2)
        c1 = os.path.join(d1, "probe.c")
        c2 = os.path.join(d2, "probe.c")
        b1 = os.path.join(d1, "probe_bin")
        b2 = os.path.join(d2, "probe_bin")

        out1 = subprocess.check_output(
            [lean_bin, "-DElab.async=false", f"--root={here}", f"--c={c1}", probe_lean],
            stderr=subprocess.STDOUT,
            text=True,
        )
        out2 = subprocess.check_output(
            [lean_bin, "-DElab.async=false", f"--root={here}", f"--c={c2}", probe_lean],
            stderr=subprocess.STDOUT,
            text=True,
        )
        assert out1 == out2, "Lean elaboration output differed"
        assert "does not depend on any axioms" in out1
        assert "[Lean.ofReduceBool, Lean.trustCompiler]" in out1
        assert "_native.native_decide.ax_1" in out1
        assert "unsound_csimp_ax" not in out1, "csimp axiom unexpectedly tracked in kernel expr"

        c1_bytes = open(c1, "rb").read()
        c2_bytes = open(c2, "rb").read()
        assert sha256_bytes(c1_bytes) == sha256_bytes(c2_bytes), "Emitted C is non-deterministic"

        subprocess.check_call([leanc_bin, "-O3", "probe.c", "-o", "probe_bin"], cwd=d1)
        subprocess.check_call([leanc_bin, "-O3", "probe.c", "-o", "probe_bin"], cwd=d2)
        b1_bytes = open(b1, "rb").read()
        b2_bytes = open(b2, "rb").read()
        assert sha256_bytes(b1_bytes) == sha256_bytes(b2_bytes), "Compiled ELF binary is non-deterministic"

        run_out = subprocess.check_output([b1, "arg1"], text=True)
        assert "safeSpec0 (compiled): true" in run_out
        assert "callerOfCsimp0 (compiled): true" in run_out
        print("OK: C sha256 =", sha256_bytes(c1_bytes), "ELF sha256 =", sha256_bytes(b1_bytes))

if __name__ == "__main__":
    main()
