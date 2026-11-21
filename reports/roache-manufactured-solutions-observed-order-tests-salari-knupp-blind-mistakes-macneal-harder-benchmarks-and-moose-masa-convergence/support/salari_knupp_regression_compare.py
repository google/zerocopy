#!/usr/bin/env python3
"""Derived comparison on PUBLISHED data: would a fixed-tolerance comparison of
discretization-error norms against the verified code's values (a "gold file"
regression test on a single mesh) have flagged the same blind-test mistakes as
the observed-order test in Salari & Knupp, SAND2000-1444 (2000), Appendix E?

Inputs are the 11x9-mesh relative error norms (L2 and max, for density, u, v,
total energy) transcribed from an OCR text of the scanned report's Tables
E1-E21. Transcription notes:
  * E.10, E.13 (placebo), E.18, E.20 print identical 11x9 values; those values
    are the baseline ("verified code").
  * E.3 u max-norm is printed as 1.48811E-3 (smaller than its L2 value
    8.84338E-3); likely an OCR/print exponent error. It does not change any
    conclusion because E.3 deviates by >1000% in other norms.
  * E.4 and E.5 print identical total-energy L2 values (3.55018E-2 and
    2.44229E-2 on 11x9 and 21x17); reproduced as printed.
  * The OCR text lost the 11x9 total-energy row of Table E21; it is omitted.
MMS verdicts and classifications are the report's own (Section 7, App. E).
This script performs arithmetic only; it does not run any flow solver.
"""

BASE = [3.91885e-4, 8.33373e-4, 3.31435e-4, 5.98882e-4, 2.28458e-4, 3.83091e-4, 1.90889e-4, 3.51916e-4]
NAMES = ["rho L2", "rho max", "u L2", "u max", "v L2", "v max", "E L2", "E max"]

# case: (classification per report, detected by MMS order test per report, 11x9 values or None)
CASES = {
    "E.1 incorrect array index": ("OAM (consistency)", True,
        [9.23708e-4, 1.68128e-3, 6.00723e-4, 9.98966e-4, 9.13941e-3, 1.50775e-2, 2.59926e-4, 1.04577e-3]),
    "E.2 duplicate index": ("OAM (consistency)", True,
        [2.26266e-3, 3.93677e-3, 2.62133e-3, 5.01838e-3, 6.62900e-3, 2.02920e-2, 6.49276e-2, 1.81950e-1]),
    "E.3 incorrect constant": ("OAM (consistency)", True,
        [5.31931e-3, 9.79076e-3, 8.84338e-3, 1.48811e-3, 3.83176e-2, 6.85403e-2, 6.09470e-3, 1.02714e-2]),
    "E.4 incorrect do-loop range": ("OAM", True,
        [3.10730e-1, 9.00000e-1, 4.25453e-2, 1.30070e-1, 3.37892e-2, 1.12420e-1, 3.55018e-2, 1.10310e-1]),
    "E.5 uninitialized variable": ("static", True,
        [2.65560e-2, 5.38971e-2, 3.01007e-2, 5.83826e-2, 5.24298e-3, 1.50089e-2, 3.55018e-2, 1.48726e-2]),
    "E.6 swapped arrays in argument list": ("formal", False, list(BASE)),
    "E.7 swapped loop indices": ("divergence", True,
        [1.75040e-1, 6.80710e-1, 1.01780e-1, 3.01180e-1, 3.94940e-1, 1.77269e-1, 3.07015e-1, 1.04740e-1]),
    "E.8 incorrect sign": ("OAM", True,
        [5.24657e-4, 1.20947e-3, 4.49409e-4, 1.00287e-3, 2.27151e-3, 4.69045e-3, 4.75690e-1, 6.63490e-1]),
    "E.9 incorrect operator position": ("OAM (consistency)", True,
        [2.01690e-1, 3.20620e-1, 1.84100e-1, 2.71070e-1, 4.92486e-2, 9.41443e-2, 5.08252e-2, 1.18530e-1]),
    "E.10 parenthesis in unused corner stencil": ("formal", False, list(BASE)),
    "E.11 differencing-scheme mistake": ("OAM (consistency)", True,
        [5.59550e-1, 7.53550e-1, 3.42692e-2, 5.94497e-2, 3.62034e-2, 6.39796e-2, 2.53229e-2, 4.67058e-2]),
    "E.12 logical IF in convergence check": ("formal", False,
        [3.91885e-4, 8.33374e-4, 3.31435e-4, 5.98882e-4, 2.28458e-4, 3.83091e-4, 1.90889e-4, 3.51916e-4]),
    "E.13 no mistake (placebo)": ("none", False, list(BASE)),
    "E.14 incorrect relaxation factor": ("efficiency", False, list(BASE)),
    "E.15 incorrect differencing (dx for dy)": ("OAM", True,
        [4.65492e-4, 1.00034e-3, 3.43574e-4, 6.08897e-4, 6.33114e-4, 1.36905e-3, 2.57412e-3, 6.63811e-3]),
    "E.16 missing term": ("OAM (consistency)", True,
        [2.94477e-4, 7.68192e-4, 2.01106e-4, 3.32522e-4, 7.75258e-4, 1.53890e-3, 3.98107e-3, 8.56773e-3]),
    "E.17 one distorted grid point": ("OAM (max norm only)", True,
        [3.94756e-4, 8.34218e-4, 3.32636e-4, 6.04219e-4, 2.80813e-4, 1.26750e-3, 1.91004e-4, 3.51126e-4]),
    "E.18 operator in unused output routine": ("formal", False, list(BASE)),
    "E.19 grid size changed by one": ("formal (per report)", False,
        [3.21339e-4, 6.98219e-4, 2.66476e-4, 4.98390e-4, 1.77446e-4, 3.05520e-4, 1.51588e-4, 2.81122e-4]),
    "E.20 redundant do loop": ("efficiency or formal", False, list(BASE)),
    "E.21 time step x0.5 (steady problem)": ("formal", False,
        [3.91885e-4, 8.33373e-4, 3.31435e-4, 5.98882e-4, 2.28458e-4, 3.83091e-4, None, None]),
}

# 41x33-mesh density norms printed for cases that are identical at 11x9
FINE = {"base": (2.50657e-5, 4.93822e-5), "E.12": (2.50656e-5, 4.93819e-5),
        "E.14": (2.50638e-5, 4.93784e-5), "E.21": (2.50647e-5, 4.93798e-5)}

TAUS = [5.5e-6, 1e-3, 1e-2, 1e-1]

if __name__ == "__main__":
    print("%-42s %-22s %-5s %10s %-8s  %s" % ("case", "class (report)", "MMS", "max|rel|", "worst", " ".join("R(%g)" % t for t in TAUS)))
    agree = {t: 0 for t in TAUS}
    for name, (cls, mms, vals) in CASES.items():
        devs = [(abs(v - b) / b, n) for v, b, n in zip(vals, BASE, NAMES) if v is not None]
        d, worst = max(devs)
        flags = ["FLAG" if d > t else "pass" for t in TAUS]
        for t, f in zip(TAUS, flags):
            agree[t] += (f == "FLAG") == mms
        print("%-42s %-22s %-5s %10.3e %-8s  %s" % (name, cls, "det" if mms else "miss", d, worst, " ".join("%-8s" % f for f in flags)))
    print()
    print("cases where single-mesh regression verdict == MMS verdict (of %d):" % len(CASES),
          {("%g" % t): agree[t] for t in TAUS})
    print()
    print("41x33 density norms for cases identical on 11x9 (relative deviation from verified code):")
    for k in ("E.12", "E.14", "E.21"):
        l2, mx = FINE[k]
        print("  %-5s L2 %.2e   max %.2e" % (k, abs(l2 - FINE["base"][0]) / FINE["base"][0], abs(mx - FINE["base"][1]) / FINE["base"][1]))
