# Code verification by observed order of accuracy: manufactured solutions, blind-mistake evidence, finite-element benchmark problems, GCI reporting, and the MOOSE and MASA harnesses

## Summary

- **What an order test checks.** In the method of manufactured solutions (MMS), the tester chooses a smooth exact solution and derives the source terms and boundary data that make it exact. The code is then run on a systematically refined sequence of meshes or time steps, and the observed rate at which the discretization error falls is compared with the formal order of the scheme. The test is sensitive to any mistake that changes the order of accuracy, however small that mistake's error is on a given mesh. It is blind, by construction, to mistakes that leave the discrete solution unchanged: efficiency mistakes, dead code, solver-only defects, and options the manufactured solution does not exercise. Basis: documentation (Salari–Knupp 2000; Roy et al. 2004) + execution (toy model).
- **Blind-test evidence.** In the only controlled deliberate-mistake study examined here (Salari–Knupp, SAND2000-1444), one author inserted 21 blind changes into a verified 2-D compressible Navier–Stokes code (20 mistakes and 1 placebo). The order test detected all 10 order-of-accuracy mistakes, plus the static and the divergence mistake. It did not detect the efficiency mistake or the 7 formal mistakes, none of which changed the solution. Four of the 10 order mistakes would have escaped the weaker "consistency" criterion (error merely tends to zero). One order mistake, a single distorted grid point, was visible only in the max norm, not in the L2 norm. Basis: documentation.
- **Order tests and regression tests answer different questions.** The report's own published error tables (a derived reanalysis) show that a gold-value comparison of the same error norms on the coarsest mesh agrees with the order test's verdict in 20 of 21 cases, for any relative tolerance from 5.5e-6 to 0.1. It disagrees only on the grid-size change, which it flags. That agreement holds only because the gold values came from an already order-verified code. A regression test detects *change*; only the order test (or an exact solution) detects *incorrectness*. Tight tolerances on finer meshes also flag harmless iteration-level changes (4–8e-5 relative for the relaxation-factor and time-step mutants on the 41×33 mesh). Basis: derived.
- **Mesh range limits order tests.** In a toy model (not any production code), a 1e-4 relative error in a coefficient kept the observed order at 2.03 → 1.94 → 1.69 over the first three refinements. It became detectable only once the meshes were fine enough for the defect to dominate the discretization error. A 1e-7 coefficient error remained invisible over all seven levels (p = 1.99). A loose iterative-solver tolerance (1e-6) produced a false order failure (p = 0.91). Basis: execution (toy model).
- **MOOSE `python/mms`.** The package derives forcing functions symbolically with SymPy, runs `Mesh/uniform_refine` or halved-`dt` sequences, and fits the slope with `numpy.polyfit` on log10 data, usually over the last 3 levels. Acceptance is left to each test. At the pinned revision, 139 Python test files import `mms`, and the most common assertion is `fuzzyAbsoluteEqual(slope, 2.0, 0.1)` (56 occurrences). The package's *own* tests check the convergence CSVs by `CSVDiff` regression (default relative tolerance 5.5e-6), not by slope. Execution with a stubbed launcher found three defects. Passing `csv=` raises `UnboundLocalError`. The temporal runner records half of each run's `dt`, which does not change the slope. The missing-CSV error message prints `None`. Basis: source + execution.
- **MASA.** MASA is a C++ library of precomputed manufactured solutions and source terms; it does not itself check solver order. Its tests compare each library source term with an independent hand-coded copy at sample points, to 5 machine epsilons relative by default. At the pinned revision with GCC 15.2, `make check` fails to compile, because the C header lacks a declaration for `masa_eval_2d_grad_w`. With that diagnostic downgraded, 73 tests pass and 7 are skipped (the automatic-differentiation tests, which need MetaPhysicL). Basis: source + execution.
- **Benchmarks and GCI fill different gaps.** The MacNeal–Harder problems are fixed coarse-mesh accuracy tests of element formulations, examined here through secondary sources. They detect locking, sensitivity to distorted shapes, and warping/curvature defects, which smooth-solution order tests on regular meshes do not exercise. The Celik et al. (2008) GCI procedure reports discretization *uncertainty* for an application whose exact solution is unknown, which is solution verification rather than code verification. An implementation from the published equations reproduces all three worked columns of its Table 1. Basis: documentation + execution.

## Applicability

- **Subjects and how they relate.** Two production implementations are examined at pinned revisions: the MOOSE framework's `python/mms` package and test harness (`idaholab/moose@8bd2be95dfbe80e93b76ada74775630e9e6a040c`), and the MASA library (`manufactured-solutions/MASA@9c31838b49501d7925b60006b59b8a39c3ea4a73`, version string 0.51). They are complementary, not competitors. MASA supplies precomputed exact solutions and source terms for codes to consume. MOOSE generates source terms on demand and also runs and fits the refinement study. Neither was checked against the other.
- **Literature.** The literature examined in full text is Salari–Knupp SAND2000-1444, Roy et al. 2004, Celik et al. 2008, and a secondary survey of finite-element pathological tests (Mallikarjuna Rao–Shrinivasa 2001). For Roache 2002 and Roache 1994, only the Crossref abstracts were examined. The original MacNeal–Harder 1985 paper, Knupp–Salari 2002 (book), Oberkampf–Trucano 2002, Roy 2005, Oberkampf–Roy 2010, and the MASA paper (Malaya et al. 2013) were **not examined in full text**. Their DOIs and metadata were verified, and no claim below rests on their content.
- **Execution environment.** All executions ran on an x86_64 Linux workstation (Intel Xeon @ 2.60 GHz, 96 logical CPUs, 236 GiB RAM) with Python 3.13, SymPy 1.14.0, NumPy 2.5.4, pandas 3.1.1, matplotlib 3.11.2, and GCC/GFortran 15.2.0. MOOSE itself was **not built**: its Python helpers were executed with the `mooseutils` dependency stubbed. MASA was built from the pinned tarball.
- **Toy model.** "Toy model" below means a 1-D finite-difference advection–diffusion–reaction solver written for this report (`support/toy_mms_mutants.py`). Its numbers describe only that model problem and are never properties of MOOSE, MASA, or the Sandia code.
- **Scope.** Findings about MOOSE apply to the pinned `next`-branch revision; the harness files change frequently. Findings about the SAND report apply to that report's single code and 21 mistakes. They are not a detection rate for any population of real bugs.

## Findings

### 1. Code verification, solution verification and validation

| Activity | Question | Reference answer used | Typical evidence | Source |
|---|---|---|---|---|
| Code verification | Does the code solve its governing equations correctly (no coding mistakes in the exercised options)? | Exact or manufactured solution | Observed order equals formal order on a refinement sequence | Roy et al. 2004 §1, §3; Salari–Knupp §2.5.6 |
| Solution (calculation) verification | How large is the discretization (and iteration) error in *this* application calculation? | None (exact solution unknown) | Richardson extrapolation / GCI on ≥3 grids; iterative-residual drop | Celik et al. 2008; Roache 2002 abstract |
| Validation | Is the model an adequate representation of reality for the intended use? | Experimental data | Model-vs-experiment comparison with uncertainty | Roy et al. 2004 §1 (modelling errors are "validation related") |

Roache's abstract states the distinction compactly: "Verification of Calculations involves error estimation, whereas Verification of Codes involves error evaluation, from known benchmark solutions". Benchmarks "need not be realistic since Verification is a purely mathematical exercise." Roy et al. list four ways to verify a code: exact solutions, manufactured solutions, benchmark numerical solutions, and code-to-code comparison. They call the last two "confidence-building exercises" that "should not take the place of rigorous code verification." Basis: documentation.

### 2. The MMS procedure as specified

Salari–Knupp §5 specifies the procedure as a 12-step loop:

1. Determine the governing equations.
2. Design the coverage tests. A code with Dirichlet and Neumann conditions needs two tests, made by swapping boundary subdomains; a transient code needs an additional time-refinement test on a fine fixed grid.
3. Construct a general manufactured solution.
4. Perform the test: compute code inputs from the solution, run, compute the global error and the observed order.
5. Refine the grid, using "the most general grid the code is capable of using". For example, a stretched grid if the code supports one.
6. Compare the observed order with the theoretical order. The comparison is one-sided: an observed order "equal to or exceeds" the theoretical order passes.
7. Troubleshoot the test implementation: input deck, solution or source derivation, error-norm software, or failure to reach the asymptotic range.
8. Decide whether an implementation problem was found.
9. Search for the order-of-accuracy mistake, narrowing the search with less general tests.
10. Decide whether another coverage test is needed.
11. Decide whether a new manufactured solution is needed.
12. Declare the code verified.

Roy et al. §3 compress the same idea into six steps. Basis: documentation.

The manufactured solution and the PDE coefficients must satisfy the guidelines of Salari–Knupp §3.1–3.2:

- They are built from smooth analytic functions.
- The solution exercises every term (for example, do not make temperature time-independent).
- The solution has enough non-trivial derivatives. A function linear in space would converge at second order even with mistakes.
- Derivatives are bounded by a small constant, so the asymptotic range is reachable.
- The solution must not break the code's robustness assumptions, such as positivity.
- Coefficient functions are general: for example, a full conductivity tensor rather than a constant scalar.
- Physical realism is explicitly *not* required.

Roy et al. add "realizable" (no negative density or pressure). They generated source code for the source terms with Mathematica. Basis: documentation.

A concrete instance of the "exercise every term" rule appears in MOOSE (`test/tests/time_integrators/bdf2/test.py`, class `TestLinearFVVaryingFactor`, docstring at lines 25–28). It explains why the time-derivative multiplier must vary in time: "Held constant ... d(cu)/dt and c du/dt are the same operator and neither pairing can be distinguished from the other." Basis: source.

### 3. Observed order, norms and acceptance criteria

Two mesh levels give the pairwise observed order. For grid spacing h and refinement ratio r = h_coarse/h_fine,

```text
E(h) = C h^p + H.O.T.
p_obs = ln(E_coarse / E_fine) / ln(r)            (Salari–Knupp Eq. 25; Roy et al. Eq. 14)
p_fit = slope of least squares fit of log10 E against log10 h over the last n levels
                                                 (MOOSE ConvergencePlot._fit, n = num_fitted_points)
```

Salari–Knupp rank four acceptance criteria by increasing rigour: expert judgement, percent difference, consistency (p > 0), and order of accuracy. Roy et al. give the same ranking with "error quantification" in second place. The order criterion is recommended because it uses the same data as the consistency criterion at almost no extra cost. Salari–Knupp note that the theoretical order should not be expected "to more than two or three significant figures". Roy et al. report both discrete L2 and L∞ norms and note that L∞ is the hardest norm in which to attain the formal order. Basis: documentation.

**Acceptance as implemented in MOOSE.** `fuzzyAbsoluteEqual(test_value, true_value, tolerance)` is `abs(test_value - true_value) < tolerance` (`python/mooseutils/mooseutils.py:518–519`). The check is two-sided, so superconvergence beyond the tolerance also fails a MOOSE test. Salari–Knupp's Step 6 is one-sided. One MOOSE test file uses the one-sided `assertGreaterEqual(slope, minimum_slopes[label])`. Basis: source.

### 4. The 21 blind tests (Salari–Knupp §7 and Appendix E)

The verified code was the 2-D compressible Navier–Stokes code of §6.2, formally second order, run on 11×9, 21×17 and 41×33 grids. Mistakes are classified with the report's taxonomy:

- **static:** caught by compilers or checkers;
- **dynamic:** found by running the code, subdivided into
  - **OAM:** order-of-accuracy mistake;
  - **consistency mistake:** an OAM severe enough to drop the order to zero or below;
  - **divergence:** the code fails to converge;
  - **efficiency:** a mistake that only slows the code;
- **formal:** remains after static and dynamic tests, for example a computed-but-unused quantity.

| Case | Change | Class (report) | Order test | Report's explanation of a miss |
|---|---|---|---|---|
| E.1 | `v(i,i)` for `v(i,j)` in a derivative | OAM, consistency | detected (p→0) | — |
| E.2 | duplicate index in a flux | consistency | detected | — |
| E.3 | wrong constant in `R2Dy` | consistency | detected | — |
| E.4 | do-loop range `imax-2` | OAM | detected (p<1; 41×33 did not converge) | Would be missed if the solution were initialized to the exact answer |
| E.5 | uninitialized `f23` | static | detected (p≈0; 41×33 did not converge) | — |
| E.6 | two derivative arrays swapped in a call | formal | missed | The arrays are only summed in one shear-stress component |
| E.7 | inner/outer loop indices swapped | divergence | detected | — |
| E.8 | `gam+1` for `gam-1` | OAM | detected (all tabulated orders ≤ 0.4; the prose says L2 converges at first order, which the table does not show) | — |
| E.9 | operators repositioned in a flux | consistency | detected | — |
| E.10 | parenthesis moved in a corner-point gradient | formal | missed | The stencil never reaches the corner point |
| E.11 | extra term in a difference | consistency | detected | — |
| E.12 | `.ae.` in the convergence test | formal | missed | Coupling makes energy converge anyway |
| E.13 | none (placebo) | — | passes at p≈2 | — |
| E.14 | relaxation factor | efficiency | missed | Only the iteration rate changes |
| E.15 | `R2Dx` for `R2Dy` | OAM | detected (v and E drop to p≈1) | — |
| E.16 | missing term | consistency | detected | — |
| E.17 | one interior grid point moved by 0.25 Δx | OAM | detected **only in max norm** (v: p≈1.1, 1.0); L2 shows p≈2 | — |
| E.18 | operator moved in an unused output routine | formal | missed | Errors were computed in-code, not from output |
| E.19 | `imax+1`, `jmax+1` | formal (per report) | missed, even with an extra 81×65 level | Only visible if the output is examined |
| E.20 | redundant loop | efficiency (App. E) / formal (§7 count) | missed | — |
| E.21 | Δt × 0.5 in a steady run | formal | missed | Would be detected in an unsteady problem |

The report's §7 tally reads "one Static, one Divergence, one Efficiency, ten OAM, and seven Formal". The tally is reproduced only if E.20 is counted as formal; Appendix E calls E.20 "an efficiency mistake, although one could argue also that it is a formal error". The source is inconsistent on this point, and the inconsistency is preserved here. Section 7 also states that with the consistency criterion "six out of ten OAM's would have been detected": E.4, E.8, E.15 and E.17 would escape, with E.8 "inconclusive" without more resolution. The report recommends computing errors from the code's *output*, since E.18 and E.19 would then have been caught. It also recommends initializing away from the exact solution (E.4). Basis: documentation.

### 5. Order tests versus fixed-tolerance regression tests

The comparison below is derived from published data. It is `support/salari_knupp_regression_compare.py`, arithmetic on the report's 11×9 error norms transcribed from an OCR text of the scan. The "regression test" compares all eight error norms (L2 and max for ρ, u, v, E) on the coarsest mesh against the verified code's values, with a per-value relative tolerance τ.

| Outcome on the 11×9 mesh | Cases |
|---|---|
| Both flag (any τ ∈ {5.5e-6, 1e-3, 1e-2, 0.1}) | E.1, E.2, E.3, E.4, E.5, E.7, E.8, E.9, E.11, E.15, E.16, E.17 |
| Both pass | E.6, E.10, E.12 (max deviation 1.2e-6), E.13, E.14, E.18, E.20, E.21 |
| Regression flags, order test passes | E.19 (grid changed: −22% in v L2) |
| Order test flags, regression passes | none |

- **E.17 is a norm-choice effect, not a mesh effect.** Its largest single-mesh deviation is +231% in the v max norm. The deviation is 23% in v L2 and only 0.73% in ρ L2. A regression test that stored only L2 norms with τ = 1e-2 would still flag it (via v L2), but one monitoring only ρ L2 would not.
- **Tight tolerances fail harmless changes on finer meshes.** On the 41×33 mesh, the efficiency mistake E.14 and the formal mistake E.21 change ρ norms by 7.6e-5 and 4.0–4.9e-5 relative. E.12 changes ρ max by 6.1e-6. All three exceed a 5.5e-6 tolerance, although none is a correctness defect.
- **The decisive difference is the reference.** The regression baseline here is the *verified* code. A regression test whose gold file was generated after a mistake was introduced passes forever by construction. Only a comparison against an exact or manufactured solution, at the observed order, reveals that the stored answer is wrong. This is the mechanism by which an error is "absorbed into the reference". Basis: derived.

### 6. Toy-model mutant experiment (`support/toy_mms_mutants.py`)

Basis: execution (toy model of a 1-D advection–diffusion–reaction discretization, not any production code).

The toy solves −(k u′)′ + c u′ + r u = f on (0,1) with a Dirichlet condition at x = 0 and a Neumann (flux) condition at x = 1. The coefficients are k = 1 + 0.5 sin 2x, c = 2 and r = 3, and the manufactured solution is u = 1 + 0.4x + e^(−x) sin 2.5x. The scheme is second order: conservative face-centred k, central advection, and a ghost-node Neumann condition. It is solved on N = 8…512. Acceptance uses MOOSE's most common rule: |p_fit − 2| < 0.1 on the 3 finest levels, in both L2 and L∞. The regression test compares the N = 32 solution with the correct code's N = 32 solution, as per-node relative difference.

| Mutant | p_fit L2 | p_fit L∞ | Order test | Regression diff | R(5.5e-6) | R(1e-2) |
|---|---|---|---|---|---|---|
| M0 correct | 2.003 | 2.000 | pass | 0 | pass | pass |
| M1 k at node, not faces | −0.001 | −0.000 | FAIL | 3.6e-2 | FAIL | FAIL |
| M2 first-order upwind advection | 1.000 | 1.001 | FAIL | 7.7e-3 | FAIL | pass |
| M3 reaction on u[i−1] | 1.009 | 1.011 | FAIL | 3.8e-3 | FAIL | pass |
| M4 first-order Neumann row | 0.963 | 0.960 | FAIL | 1.3e-3 | FAIL | pass |
| M5 source at x + h/2 | 1.004 | 1.004 | FAIL | 2.0e-2 | FAIL | FAIL |
| M6 advection sign flipped, test with c = 2 | −0.001 | −0.000 | FAIL | 1.1e-1 | FAIL | FAIL |
| M6 same mistake, test with c = 0 | 2.004 | 2.000 | pass | 0 | pass | pass |
| M8 unused diagnostic wrong | 2.003 | 2.000 | pass | 0 | pass | pass |
| M9a k × (1 + 1e-4) | 0.255 | 0.309 | FAIL | 2.4e-5 | FAIL | pass |
| M9b k × (1 + 1e-7) | 1.989 | 1.993 | pass | 2.4e-8 | pass | pass |

- **Small-defect detectability depends on the mesh range.** M9a's pairwise orders are 2.03, 1.94, 1.69, 1.07, 0.40 and 0.11. The L2 error plateaus near 3.5e-5 while the correct code reaches 1.2e-6 at N = 512. A study stopping at N = 32 would have accepted it.
- **Coverage gaps defeat both kinds of test.** M6 is invisible when the test configuration sets c = 0, because the faulty term is multiplied by zero. This is Salari–Knupp's Step 2 coverage failure in miniature.
- **Solver settings: cost without error, error without a bug.** SOR replaced the direct solve up to N = 128. With ω = 1.9 and rtol 1e-12 the fit is p = 2.011, using 3,410 iterations at N = 128. With ω = 1.5 (an efficiency mistake), p = 2.011 again, but N = 128 takes 21,600 iterations and the regression difference is 1.5e-11. With ω = 1.9 and rtol 1e-6, the fit is **p = 0.908** (pairwise 2.05, 2.03, 1.79, 0.02), a false failure caused by iteration error rather than a coding mistake. Celik et al. likewise require at least three, preferably four, orders of residual reduction before estimating discretization error, and warn that this "does not always ensure adequate convergence".

### 7. Production practice: Roy et al. 2004

Roy et al. used MMS to verify two Sandia finite-volume codes. Premo is node-centred and unstructured; Wind is structured. Both use Roe upwinding with MUSCL extrapolation and central viscous differences, so both are formally second order. Tests covered 2-D supersonic Euler and subsonic Navier–Stokes, on meshes up to 129×129 nodes with r = 2. Mathematica generated Fortran for the source terms. Both codes showed second-order L2 and L∞ convergence.

Coding mistakes found by MMS included:

- a mistake that zeroed the MUSCL gradient term when the limiter was set to zero, which produced first-order behaviour;
- an inadvertently activated constant-angular-rotation option, which produced "non-ordered errors".

The authors explicitly list what was **not** verified: solver efficiency and stability ("not verifiable with the method"), non-uniform or curvilinear meshes, temporal accuracy, and variable transport properties. Over-specified Dirichlet inflow/outflow values for Navier–Stokes did not degrade the observed order. Basis: documentation.

### 8. MacNeal–Harder standard problems: what they test that order tests do not

Basis: documentation (secondary sources; the 1985 paper itself was not examined).

The problems are coarse-mesh accuracy tests with known reference answers. They target element pathologies rather than asymptotic rate:

- **Patch tests**, including a 3-D solid patch with irregular, warped interior elements. They test constant-strain representability, and hence convergence.
- **Straight cantilever beams.** Six elements in rectangular, trapezoidal and parallelogram shapes, under unit tension, in-plane shear, out-of-plane shear, and constant bending moment. They test sensitivity to distortion and trapezoidal locking.
- **Curved beam.** Tests curvature.
- **Twisted beam.** The beam twists 90° over 12 elements, 7.5° per element. It tests warping.
- **Plates, the Scordelis–Lo roof, and the pinched hemisphere.** These test shells.
- **Thick-walled cylinder** with ν → 0.4999. Tests near-incompressibility (volumetric locking).

The Sadhana survey summarizes MacNeal–Harder as defining element failure modes and "throwaway tests". An element that fails to reach 98% accuracy on the extension beam with distorted shapes "is to be thrown away".

The Abaqus 6.11 Benchmarks Manual (§2.3.7) shows how the twisted-beam test is reported in practice. Reference tip displacements for the thick case (b = 0.32 in) are 5.424e-3 in in-plane and 1.754e-3 in out-of-plane, under 1 lb loads. The manual tabulates per-element results at three meshes. A one-layer continuum-shell mesh (SC8R, 2×12×1) is off by 44.2% in-plane and 38.4% out-of-plane, while S4 shells are within 1.4%. A smooth manufactured solution on a regular mesh would not provoke these defects unless the test deliberately used distorted, thin, curved or nearly incompressible configurations. Conversely, a single-mesh benchmark against a reference value does not establish the order of convergence. Basis: documentation + derived.

### 9. Discretization-uncertainty reporting: the GCI (Celik et al. 2008)

**Procedure.**

1. Define a representative size h. For 3-D, h = [(1/N) Σ ΔV_i]^(1/3); for 2-D, the analogue with areas.
2. Run three significantly different grids, preferably with r = h_coarse/h_fine > 1.3; that threshold is "based on experience and not on formal derivation".
3. Solve p = |ln|ε32/ε21| + q(p)| / ln r21 by fixed-point iteration, with q(p) = ln((r21^p − s)/(r32^p − s)) and s = sign(ε32/ε21). A negative ratio indicates oscillatory convergence.
4. Compute the extrapolated value: φ_ext21 = (r21^p φ1 − φ2)/(r21^p − 1).
5. Report e_a21 = |(φ1 − φ2)/φ1|, e_ext21, and GCI_fine21 = 1.25 e_a21 / (r21^p − 1).

The procedure requires that the code be previously verified, with its formal order stated. It also requires at least three (preferably four) orders of iterative residual reduction. The GCI does not account for modelling error.

**Reproduction.** `support/gci_celik2008.py` implements these equations. With the grid ratios derived from the stated 2-D cell counts (r = √(N_coarse/N_fine)), it reproduces all three columns of the note's Table 1 to printed precision:

| Column | p | φ_ext21 | e_a21 | e_ext21 | GCI_fine21 |
|---|---|---|---|---|---|
| Reattachment length (monotonic) | 1.534 | 6.1685 | 1.50% | 1.71% | 2.17% |
| Axial velocity (p < 1) | 0.752 | 10.8801 | 0.58% | 0.85% | 1.07% |
| Axial velocity (oscillatory) | 1.508 | 6.0269 | 0.70% | 0.38% | 0.47% |

The published values are 1.53 / 6.1685 / 1.5 / 1.7 / 2.2, then 0.75 / 10.8801 / 0.6 / 0.9 / 1.1, then 1.51 / 6.0269 / 0.7 / 0.4 / 0.5. Using the rounded printed ratio r32 = 1.333 instead gives p = 1.54 and φ_ext21 = 6.1682 for the first column. The printed ratios are therefore rounded and should not be fed back verbatim. Basis: normative (journal policy) + execution.

### 10. MOOSE `python/mms` at `8bd2be95dfbe80e93b76ada74775630e9e6a040c`

**Source-term derivation** (`python/mms/evaluate.py`). `evaluate(pde, soln, variable="u", scalars, vectors, functions, vectorfunctions, negative=False, transformation="cartesian"|"cylindrical", ...)` builds a SymPy `CoordSys3D`. It `eval`s the solution string, rewrites the PDE string with `pde.replace("grad", "gradient")` and then `pde.replace("div", "divergence")` (lines 134–135), and `eval`s the result. It returns `(forcing, exact)`. `print_fparser`/`print_hit` emit MOOSE `ParsedFunction` input; `print_moose` emits C++.

The rewrite is plain substring replacement. A PDE string that already contains `divergence(` or `gradient(`, or any identifier containing `div` or `grad`, is corrupted; for example, `divergence` becomes `divergenceergence`. Basis: source + derived.

Executing `evaluate("-div(k*grad(u)) + c*diff(u, x) + r*u", "sin(3*x)*exp(x)", scalars=["c","r"], k="1 + x/2")` gives a forcing function whose difference from an independent SymPy hand derivation simplifies to 0. One call takes about 1–2 ms once SymPy is imported; importing the package takes 0.8–1.2 s. Basis: execution.

**Runner** (`python/mms/runner.py`). `run_spatial`/`run_temporal` call `_runner`. Each spatial level appends `Mesh/uniform_refine=<step>` (line 104); each temporal level appends `Executioner/dt=<dt>` and then halves `dt` (lines 106–107). The runner reads the last row of the app's CSV (`x_pp` default `h`, `y_pp` default `error`) into a pandas DataFrame. Execution with a stub launcher (`support/moose_mms_probe.py`) found the following.

- **The `csv=` argument is broken.** Lines 63–65 assign `fcsv` only `if csv is None`, and lines 112–113 also only `if csv is None`. Passing `csv="explicit_name.csv"` therefore raises `UnboundLocalError: cannot access local variable 'fcsv' where it is not associated with a value` at line 121. Basis: source + execution.

```python
    63	    # Assume output CSV file, if not specified
    64	    if csv is None:
    65	        fcsv = input_files[-1].replace(".i", "_out.csv")
   ...
   121	        if not os.path.isfile(fcsv):
   122	            raise IOError("The CSV output does not exist: {}".format(csv))
```

- **The missing-output message prints `None`.** Line 122 formats `csv` rather than `fcsv`, so the error reads "The CSV output does not exist: None". Basis: execution.
- **The temporal runner records half of each run's `dt`.** Line 132 (`x.append(dt)`) runs after line 107 has halved `dt`. Runs with dt = 0.1, 0.05, 0.025 are recorded as 0.05, 0.025, 0.0125, under a column named `h` (the `x_pp` default). Line 137 (`x_pp == "dt"`) is a comparison with no effect, placed in the spatial branch. A uniform factor shifts log10 x by a constant, so the fitted slope is unchanged; it came out 2.000000 both ways. Plotted time-step labels are off by a factor of 2. Basis: source + execution + derived.
- **The derived output name is fragile.** The default CSV name comes from `input_files[-1].replace(".i", "_out.csv")`, which replaces *every* occurrence of `.i` in the path. Basis: source.

**Fit and tolerance** (`python/mms/ConvergencePlot.py`). The fit is `np.polyfit(np.log10(x), np.log10(y), 1)` (line 126), optionally over the last `num_fitted_points` (lines 91–94). The slope is stored in `label_to_slope`. `ConvergencePlot` applies **no** acceptance criterion; each test asserts its own. On data 7h²(1+0.3h) at h = 0.05…0.0125, the 3-point fit returns 2.008. Basis: source + execution.

**Harness integration.**

- `MMSTest` (`python/TestHarness/testers/MMSTest.py`) subclasses `PythonUnitTest`. It adds `pandas` and `matplotlib` to the required packages, forces `capabilities ... method=opt` (lines 71–74), honours `--n-threads` (`max_threads = 16`), and pins `max_parallel` to `min_parallel`. Its docstring says MMS tests do not run under `--valgrind`, `--recover`, `--restep` or `--capture-perf-graph`.
- Failures surface as an ordinary `unittest` assertion failure, `assertTrue(fuzzyAbsoluteEqual(...))`. Unless the test prints it, as `TestLinearFVVaryingFactor` does, the message does not include the observed slope.
- The bdf2 spec comment records the cost of order tests: "Four refinement levels of a 32x32 transient run to about seven seconds, well past the couple of seconds a framework test wants"; the test is marked `heavy = true`. Basis: source.

**The package's own tests are regression tests, not order tests.** `python/mms/test/tests` checks only:

- that `mms_spatial.png` and `mms_temporal.png` exist (`CheckFiles`);
- that the error-versus-h CSVs match gold files (`CSVDiff`), with default `rel_err = 5.5e-6` and `abs_zero = 1e-10` (`python/TestHarness/testers/FileTester.py:26–31`);
- that `test_mms.py` string-compares derived forcing functions.

`test_mms.py::testExceptions` (lines 98–118) wraps each call in `try: ... except SyntaxError as e: self.assertIn(...)`, with no `self.fail()` when nothing is raised. Making `_check_reserved` a no-op still makes the upstream test error out. The cause is a `NameError` for the undeclared scalar `k` in every call's `h="k*x*x"`, not the reserved-name check. Once `k` is declared, so that the inputs are otherwise valid, the no-op mutant **passes** the test. The test's apparent strength against this mutant is therefore incidental. Basis: execution (mutation of the real upstream file).

**Census of the framework's test suite.** `support/moose_test_census.sh` performs a measured census at the pinned revision over all 48,408 blobs. It found 3,099 test-spec files, and counted tester `type =` declarations:

| Tester | Exodiff | CSVDiff | RunException | RunApp | PetscJacobianTester | JSONDiff | PythonUnitTest | MMSTest | CheckFiles | ImageDiff |
|---|---|---|---|---|---|---|---|---|---|---|
| Declarations | 5,212 | 4,133 | 2,771 | 1,040 | 1,028 | 353 | 293 | 217 | 148 | 117 |

Among the 638 `.py` files under `/tests/` paths:

- **Usage:** 139 import `mms`, and 57 use `label_to_slope`.
- **Assertion forms:** `fuzzyAbsoluteEqual(value, 2.0, 0.1)` × 56, `(value, 1.0, 0.1)` × 18, `(value, 2.0, 0.25)` × 14, `(value, 1.0, 0.25)` × 11, `(value, 3.0, 0.1)` × 7, `(value, 1.0, 0.05)` × 7, `(value, 2.0, 0.05)` × 6, and others.
- **Fit window:** `num_fitted_points=3` × 186, `=2` × 19.
- **Literal refinement counts:** 4 levels × 13, 5 × 12, 6 × 10, 7 × 17.

Declarations are counted, not executed test instances; a block can inherit a type. Some order tests run as `PythonUnitTest` rather than `MMSTest`, and some `CSVDiff` tests may compare convergence data, so the ratio is approximate. In this one framework, `MMSTest` declarations are outnumbered by gold-file regression testers by more than an order of magnitude: (5,212 + 4,133)/217 ≈ 43 (derived). Basis: execution (census) + derived.

### 11. MASA at `9c31838b49501d7925b60006b59b8a39c3ea4a73`

- **Model.** MASA provides named manufactured solutions: heat, Laplace, Euler with and without chemistry, Navier–Stokes, RANS/Spalart–Allmaras, radiation, Burgers, ablation, and others. Each solution has registered parameters and `masa_eval_source_*`, `masa_eval_exact_*` and `masa_eval_grad_*` evaluators, with C, Fortran 90 and SWIG-Python bindings. The README calls it an application-independent library "to enhance reusability and consistency". The consuming code still runs the refinement study and judges the order. Basis: documentation + source.
- **Two source-term paths.** Most solutions ship closed-form source code. Tests label the comparison copy "check against maple" (`tests/euler2d.cpp:360`). The `ad_*` solutions, such as `src/ad_cns_3d_crossterms.cpp:146–193`, instead evaluate the PDE residual at run time with nested MetaPhysicL `DualNumber` types. These compute first and second derivatives by forward-mode AD, so the source term is generated from the operator definition rather than transcribed. MetaPhysicL is optional (`configure.ac:91–98`); without it, the 7 AD tests are skipped. Basis: source + execution.
- **Test oracle.** Each test evaluates the library's source and exact terms at a few points and compares them with an independent duplicate formula. The default comparison is relative, `|a−b|/|b|`, against 5 × machine epsilon. `--enable-strict-tests` switches to absolute (`tests/euler2d.cpp:373–397`; `configure.ac:119–129`). Several C tests use absolute 1e-15 or 2e-15; `c_euler3d.c` notes a weakening "because of O(1000) FP operations failing on some macbooks". This is an implementation-consistency oracle (two transcriptions agree), not an order test. A mistake common to both copies, such as a wrong symbolic derivation fed to both, would not be caught. Basis: source + derived.
- **Weak checks in the tests.** `tests/heatsc.cpp` checks the return value of `masa_sanity_check` for the 1-D solution (line 102) but discards it for 2-D and 3-D (lines 147, 177). `src/masa_class.cpp:303` carries the upstream comment "check all vector values -- this has a subtle bug". Basis: source.
- **Build and test run** (`support/masa_build_check.txt`):
  - `./configure` failed ("Giving up, python development not available") even though Python interfaces were not requested; setting `PYTHON=/usr/bin/python3` fixed it.
  - `make check` failed to compile `tests/c_source.c:79` (`out = masa_eval_2d_grad_w(x,x,i);`). GCC 15.2 rejects implicit function declarations: `src/cmasa.cpp:229` defines `extern "C" double masa_eval_2d_grad_w(...)`, but `src/masa.h.in` declares only `masa_eval_2d_grad_u` (1157), `_v` (1175), `_p` (1212), `_rho` (1237) and `masa_eval_3d_grad_w` (1193). Under compilers that accept implicit declarations, the call is typed as returning `int`, while the function returns `double`. The only check on the value is `nancheck(out)` (line 80), so a garbage value would likely pass. That consequence is derived from the C calling convention and was not executed.
  - With `-Wno-error=implicit-function-declaration`: examples 23/23 pass; tests 50 pass, 7 skipped, 0 fail.

  Basis: execution + source.

### 12. Performance and resource footprint (L1–L6)

| Level | Order test (toy model) | MOOSE `python/mms` | MASA | GCI / MacNeal–Harder |
|---|---|---|---|---|
| L1 authoring/maintenance | not measured | Package: 812 lines in 6 files (25,698 bytes, sum of API sizes); a typical test file 36 lines (bdf2) | Library 20,281 lines vs tests 21,605 lines (`wc -l`; test:library ≈ 1.07, derived) | not measured |
| L2 toolchain build | n/a (pure Python) | MOOSE build not measured | bootstrap 3.92 s; configure 9.81 s; `make -j8` 11.52 s, peak RSS 165,676 KB (measured) | not applicable |
| L3 source-term generation | SymPy derivation, not timed separately | `evaluate()` ≈ 0.9–2 ms per call after a 0.8–1.2 s import (measured) | Precomputed (no runtime derivation) or AD at evaluation time; not timed | not applicable |
| L4 execution of the test | 7-level direct study 0.079 s vs one N = 32 solve 0.0045 s (≈ 17.6×, measured toy) | bdf2 MMS: "about seven seconds" for 4 levels of 32×32 (cited, upstream comment) | `make -j8 check` 6.77 s including test compilation (measured) | One application run per grid; ≥ 3 grids by definition |
| L5 checker | Slope fit `np.polyfit` on 3 points ≈ 28–39 µs (measured) | same fit | point comparisons; not timed | GCI arithmetic: negligible, not timed |
| L6 footprint | not measured | not measured | `libmasa-0.51.so` 2,497,848 bytes (text 2,164,666); source tarball 597,134 bytes (measured) | not applicable |

Derived scaling. With refinement ratio 2, d spatial dimensions and a solver whose cost is linear in the number of unknowns, an L-level study costs at most 1/(1 − 2^−d) times the finest run: 2× in 1-D, 1.33× in 2-D, 1.14× in 3-D. The dominant cost is the finest level, which must reach the asymptotic range. Superlinear solvers raise the cost further. Energy and power were not measured at any level.

### 13. Comprehensibility and conceptual simplicity (C1–C2)

- **C1: legible verdicts, opaque diagnoses.** The order test reduces to one human-checkable invariant: "error falls as h^p". Its failure diagnostic, a slope, says *that* something is wrong but not *where*. Salari–Knupp's Step 9 and Roy et al. both prescribe localising by switching solution terms off, or by inspecting local error fields. MOOSE's assertion messages do not even report the slope by default. A fixed-tolerance regression failure says *what changed* and where, but not whether it matters. The two diagnostics are complementary.
- **C1: hidden footguns.** A human auditing a manufactured-solution test must check three things that the harness does not:
  - that every term is non-zero (toy M6; the MOOSE bdf2 docstring);
  - which norm is monitored (SAND E.17);
  - that the error is computed from the code's output (SAND E.18, E.19).
- **C2: one acceptance mechanism, configured differently.** MOOSE leaves acceptance to each test, giving 25 distinct `fuzzyAbsoluteEqual` forms across test files, and checks its own harness by gold-file CSV regression. A minimal universal abstraction would be a single declared contract per test: formal order, one- or two-sided tolerance, number of fitted levels, and the norms covered. Salari–Knupp's one-sided rule and MOOSE's two-sided rule would then become explicit parameters instead of implicit conventions.
- **C2: separate source-term generation from transcription.** Symbolic generation (MOOSE `evaluate`) and AD evaluation (MASA `ad_*`) remove transcription as a failure point. Closed-form shipped source plus a duplicate-copy test (MASA's default) keeps two transcriptions in sync, but cannot catch a shared derivation error. Basis: derived.

### 14. Validation coverage of the methods themselves (V1–V4)

- **V1 (specification adequacy / mutation).** The SAND blind test is a 21-mutant study of the order test's kill rate on one code. The toy experiment (§6) is a 10-mutant study on a toy. The MOOSE test-file mutation in §10 is a single-mutant check of a test's non-vacuity. No examined source reports systematic mutation analysis of MOOSE's `MMSTest` suite or of MASA's source terms (not examined beyond this).
- **V2 (lowering/checker fuzzing).** The MASA build is a compiler-change probe. It showed that a newer C compiler turns a latent header omission into a build failure. Differential testing of source-term generators (SymPy vs Maple vs AD) was not performed; one hand-vs-`evaluate()` check agreed.
- **V3 (concurrency/crash/silicon).** Not applicable to order tests as such. MOOSE runs MMS tests in opt mode with threads but caps MPI ranks. Thread-count sensitivity of observed orders was not examined.
- **V4 (field/human validation).** Validation against experiment is by definition outside code verification. MacNeal–Harder-style benchmarks are the closest analogue for element behaviour. No examined source measures how engineers interpret slope failures.

## Boundaries

- **Not examined:**
  - the full texts of Knupp–Salari 2002, Oberkampf–Trucano 2002, Roy 2005, Oberkampf–Roy 2010, the MASA paper (Malaya et al. 2013), Roache 2002 (abstract only) and Roache 1994 (abstract only);
  - the original MacNeal–Harder 1985 paper, including its exact problem dimensions, its grading scale, and its results for the elements it examined. The MacNeal–Harder material above is secondary.
- **Not executed:**
  - MOOSE was not built, and no MOOSE `MMSTest` was run. Runtime claims for MOOSE are cited from upstream comments.
  - The MOOSE probes replace `mooseutils` with a stub, so behaviour of the real launcher, MPI, and CSV writers is not exercised.
  - MASA's AD solutions, its Fortran and Python interfaces, and `--enable-strict-tests` were not built or run.
- **Unknown:** whether the MASA `c_source.c` call actually returned a wrong value under older compilers (derived from the calling convention, not run). Also unknown is what "subtle bug" `src/masa_class.cpp:303` refers to.
- **Known not to apply.** Salari–Knupp's 10/10 OAM detection is a result for one code, one manufactured solution and 20 author-chosen mistakes. It is not a detection rate for real defects in other codes. The derived regression comparison (§5) uses OCR-transcribed numbers from a scanned report: one value, E.3 u max-norm, is probably mis-printed, and E.4 and E.5 print identical energy-L2 values. Neither changes any verdict.
- **Unsupported by the evidence here:**
  - that order tests detect all bugs (they are blind to efficiency, stability, robustness, dead code and unexercised options);
  - that regression tests are weaker in general (on the SAND data they were as sensitive as order tests to change, but only relative to a verified reference);
  - that a passing order test verifies non-uniform, adaptive or curvilinear mesh paths unless those were used in the test (Roy et al. explicitly did not verify them).
- **Not measured.** All L1 velocity and maintenance costs, token budgets, MOOSE build time and footprint, MOOSE MMS test runtimes, RSS of the toy and of MOOSE helpers, energy, and GCI/benchmark runtimes are not measured.
- **Census not performed.** No cross-code census was run. A census over a stated sample of open-source simulation codes (for example: MOOSE, deal.II, FEniCS/Firedrake, OpenFOAM, PETSc TS examples, SU2) would record per physics component whether the test suite has (a) order assertions, (b) gold-file regression only, or (c) both. Method for each code: list spec/test files at a pinned commit, classify assertions by pattern (slope fit plus tolerance vs file diff), then hand-audit a random 5% sample for misclassification.

## Evidence

All evidence was gathered on 2026-11-21 (UTC).

- **MOOSE** (`idaholab/moose@8bd2be95dfbe80e93b76ada74775630e9e6a040c`, resolved with `gh api repos/idaholab/moose/commits/HEAD`):
  - `python/mms/evaluate.py` lines 16–28 (signature), 129–136 (eval and string rewrite);
  - `python/mms/runner.py` lines 63–65, 101–113, 121–122, 127–137, 145;
  - `python/mms/ConvergencePlot.py` lines 91–99, 116–127;
  - `python/mms/test/tests` lines 1–53;
  - `python/mms/test/test_mms.py` lines 98–118;
  - `python/TestHarness/testers/MMSTest.py` lines 15–74;
  - `python/TestHarness/testers/FileTester.py` lines 26–31;
  - `python/mooseutils/mooseutils.py` lines 518–519;
  - `test/tests/time_integrators/bdf2/test.py` lines 1–36 and `tests` lines 25–54.

  Files were fetched from `raw.githubusercontent.com` at that SHA. The tree listing used `gh api repos/idaholab/moose/git/trees/<sha>?recursive=1`, descending into subtrees when truncated (`support/list_tree.py`).
- **MASA** (`manufactured-solutions/MASA@9c31838b49501d7925b60006b59b8a39c3ea4a73`; codeload tarball, 597,134 bytes):
  - `README.md`;
  - `src/masa.h.in` lines 1157, 1175, 1193, 1212, 1237;
  - `src/cmasa.cpp` lines 227–231, 257;
  - `src/masa_class.cpp` lines 278–326;
  - `src/ad_masa.h`;
  - `src/ad_cns_3d_crossterms.cpp` lines 146–193;
  - `tests/heatsc.cpp` lines 84–190;
  - `tests/euler2d.cpp` lines 232, 360–406;
  - `tests/tests.h` lines 42–170;
  - `tests/c_source.c` lines 75–84;
  - `configure.ac` lines 91–129.
- **Literature**, with DOIs verified against Crossref metadata (`api.crossref.org/works/<doi>`, via a read-only fetch tool):
  - **Salari & Knupp**, SAND2000-1444, June 2000, `10.2172/759450`. Full text was read from a public mirror of the OSTI scan. §2.4, §2.5.6, §3.1–3.2, §4.2, §5, §7, §8, §9 and Appendix E were used.
  - **Roy, Nelson, Smith & Ober**, Int. J. Numer. Meth. Fluids 44(6):599–620, 2004, `10.1002/fld.660`. Full text was read from a university mirror.
  - **Celik, Ghia, Roache, Freitas, Coleman & Raad**, J. Fluids Eng. 130(7):078001, 2008, `10.1115/1.2960953`. Full text was read from the publisher PDF. Crossref lists no authors; they were taken from the note's signature block.
  - **Roache**, J. Fluids Eng. 124(1):4–10, 2002, `10.1115/1.1436090`, abstract only.
  - **Roache**, J. Fluids Eng. 116(3):405–413, 1994, `10.1115/1.2910291`, abstract only.
  - **Mallikarjuna Rao & Shrinivasa**, Sādhanā 26(6):549–590, 2001, `10.1007/BF02703459`, full text.
  - **Metadata only (content not examined):**
    - MacNeal & Harder, Finite Elem. Anal. Des. 1(1):3–20, 1985, `10.1016/0168-874X(85)90003-4`;
    - Oberkampf & Trucano, Prog. Aerosp. Sci. 38(3):209–272, 2002, `10.1016/S0376-0421(02)00005-2`;
    - Roy, J. Comput. Phys. 205(1):131–156, 2005, `10.1016/j.jcp.2004.10.036`;
    - Oberkampf & Roy, Cambridge University Press 2010, `10.1017/CBO9780511760396`;
    - Knupp (Crossref lists only this author) & Salari, Chapman & Hall/CRC 2002, `10.1201/9781420035421`;
    - Malaya, Estacio-Hiroms, Stogner, Schulz, Bauman & Carey, Eng. Comput. 29(4):487–496, 2013, `10.1007/s00366-012-0267-9`.
- **Vendor documentation:**
  - Abaqus 6.11 Benchmarks Manual §2.3.7 (twisted beam; Tables 2.3.7–1 to 2.3.7–12);
  - OptiStruct 2026 verification problem OS-V: 0760 (MacNeal–Harder solid patch test) and its index of OS-V: 0700–0730 MacNeal–Harder problems.
- **Execution support** (`support/`):
  - `toy_mms_mutants.py` and `.out.txt` (§6; wall time about 6 s);
  - `moose_mms_probe.py` and `.out.txt` (§10, probes P1–P6);
  - `timings_probe.py` and `.out.txt`;
  - `gci_celik2008.py` and `.out.txt` (§9);
  - `salari_knupp_regression_compare.py` and `.out.txt` (§5, derived arithmetic on published tables);
  - `moose_test_census.sh`, `list_tree.py` and `moose_test_census.out.txt` (§10 census);
  - `masa_build_check.txt` (§11).

  Commands take the upstream directory as an argument. The Python probes need `numpy` and `sympy`; the MOOSE probes also need `pandas` and `matplotlib`.

## Revalidation

- **MOOSE runner defects.** Diff `python/mms/runner.py` lines 60–140 at a new revision. If `fcsv` is still assigned only under `if csv is None` and line 132 still follows the halving at line 107, the findings stand. To confirm by execution, run `python3 support/moose_mms_probe.py <dir containing mms/>`; P1, P2 and P3 print the exception, the recorded-vs-passed `dt`, and the message.
- **MOOSE acceptance conventions.** Rerun `sh support/moose_test_census.sh idaholab/moose <sha> <workdir>` (about 1 minute with an authenticated `gh`) and compare the counts.
- **MASA header gap.** Check `grep -n masa_eval_2d_grad_w src/masa.h.in` at a new revision. An empty result with a matching `src/cmasa.cpp` definition means `make check` still fails under GCC ≥ 14. To confirm, build with `PYTHON=python3 ./configure && make && make check`.
- **SAND numbers.** These are fixed historical data. Recheck `support/salari_knupp_regression_compare.py` only if a better scan or transcription becomes available.
- **GCI implementation.** `python3 support/gci_celik2008.py` must reproduce Table 1 to printed precision.
- **Toy conclusions.** `python3 support/toy_mms_mutants.py` is deterministic. It characterises only the toy and should be rerun after any change to it.
