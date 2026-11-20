# Support material

Self-contained toy probes (Python 3 + NumPy) and their recorded outputs,
referenced by `REPORT.md`. They model mechanisms; they are not runs of PETSc,
Belos, Ginkgo, SciPy, LAPACK's DSGESV, CADNA or Verificarlo.

| File | Purpose |
| --- | --- |
| `probe_residual_gap.py` / `.out` | CG: recursively updated vs true residual in binary32 and binary64 |
| `probe_backward_error.py` / `.out` | Rigal-Gaches attainability; r0-relative vs b-relative tests; left-preconditioned norm; normwise vs componentwise backward error with LAPACK-style safe denominators; Hilbert forward error |
| `probe_mixed_ir.py` / `.out` | DSGESV-style mixed-precision refinement acceptance vs forward error |
| `probe_cestac_toy.py` / `.out` | CESTAC re-implementation (N = 3, exact random rounding) applied to CG, with digit estimates vs exact-arithmetic references and instability counters |

Run each with `python3 <file>.py`; all seeds are fixed.
