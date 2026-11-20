# Convergence tests versus delivered accuracy: backward-error acceptance, recursively updated residual gaps, production solver defaults, and stochastic-arithmetic digit estimates

## Summary

"Converged" is a statement about a stopping test, not about the answer. A stopping test entails an accuracy statement only through a chain of four links, and every link can break independently:

1. **Monitored quantity → true residual of the original system.** Production Krylov codes monitor a *recursively updated* residual, a *preconditioned* residual, or a GMRES least-squares estimate, not `b − A x_k`. In finite precision the updated residual can keep falling after the true residual stagnates (Greenbaum 1997). In a NumPy CG toy model at `u ≈ 6e-8` (binary32), the updated residual passed `1e-8` at iteration 512 while the true relative residual was `6.4e-7`; in binary64 the updated residual reached `5e-21` while the true one stayed at `1.3e-15` (`Basis: execution (toy model)`).
2. **True residual → backward error.** Rigal–Gaches gives the normwise backward error `η_{E,f}(y) = ‖r‖ / (‖E‖‖y‖ + ‖f‖)`; Oettli–Prager gives the componentwise one `ω_{E,f}(y) = max_i |r_i| / (E|y| + f)_i`. A test `‖r‖ ≤ τ‖b‖` therefore implies `η_{A,b} ≤ τ`. A test relative to `‖r_0‖` with a nonzero initial guess implies nothing comparable, and a preconditioned-norm test bounds only the backward error of the *preconditioned* system. A normwise acceptance can coexist with a componentwise backward error of `1` on badly row-scaled sparse systems (toy probe: `η = 3.9e-11`, `ω = 1.0`, forward error `0.73`; one fixed-precision refinement step gave `ω = 1.05e-15`).
3. **Backward error → forward error** needs a condition number. Iteration does not supply one (Hilbert `n = 12`: `η = 6.7e-17`, forward error `0.18`).
4. **Floating-point realization → digits.** Stochastic arithmetic (CESTAC as implemented by CADNA; Monte Carlo arithmetic in Verificarlo) estimates how many digits survive *rounding*. It does not measure truncation or iteration error. In a toy CESTAC re-implementation applied to CG, the digit estimates tracked the true rounding error until the method's self-validation reported unstable operations. After that point the estimates were over-optimistic, and a naive "update is a computational zero" stop fired at an iterate with no correct digits.

Production defaults at the pinned revisions (`Basis: source`):

| Library | Default test |
| --- | --- |
| PETSc | `rnorm ≤ max(1e-5·rnorm_0, 1e-50)`, measured by default in the left-preconditioned norm for GMRES and CG. No true-residual confirmation except a GMRES restart consistency check. The `KSPCreate` documentation says modified Gram–Schmidt, but the code installs classical Gram–Schmidt without refinement. |
| Belos | Tolerance `1e-8`. `PseudoBlockGmres` confirms implicit convergence with an explicit residual. `StatusTestImpResNorm` returns `Passed` together with a loss-of-accuracy flag when the explicit residual cannot be driven below the tolerance. The `isLOADetected()` documentation describes the left-preconditioner case backwards relative to the code. Belos CG tests only the recursively updated residual. |
| Ginkgo | `ResidualNorm` is documented as the "explicit residual norm" `‖b − A x_k‖`, but it uses the solver-supplied residual vector, which in CG is the recursively updated one. |
| SciPy | `cg` tests only the updated residual against `max(atol, 1e-5‖b‖)`. `gmres` re-computes `b − A x` at each restart. |
| LAPACK | `xGERFS` stops refinement on the componentwise backward error. `DSGESV` stops mixed-precision refinement on a normwise backward-error test and falls back to binary64 after 30 iterations. |

## Applicability

The findings apply to the following subjects, each identified in `REPORT.json`:

- **Default convergence-test source paths**, by direct reading of:
  - PETSc `petsc/petsc` at `a78a7628566ecd590e0aaab6176b0f93422bab63`;
  - Trilinos Belos `trilinos/Trilinos` at `59703d7d03c88652d111c902535b0a4fb57f7cce`;
  - Ginkgo `ginkgo-project/ginkgo` at `796a388db0e8fb8c2a2d9918c658858bcab9c798`;
  - SciPy `scipy/scipy` at `5a63b65045f80b5a2198f0d7c00d9935efe9a676`;
  - Reference LAPACK `Reference-LAPACK/lapack` at `b458ca66c8f828f246bae508888b4b79a3244900`.
- **Significant-digit machinery of Verificarlo** `verificarlo/verificarlo` at `5142c8f7a86106bce1800e433a49ec22c594f175`.
- **The backward-error and stochastic-arithmetic literature** listed under Evidence. Where only a secondary source or an abstract was read, the Evidence section says so.

Relationship among subjects: the libraries are compared against the backward-error theory. Verificarlo and CADNA are compared as two estimators of rounding-induced digit loss that can audit a converged result.

None of the libraries was built or run. Every library claim is a source-reading claim about the pinned revision; runtime behaviour under particular builds, options files or preconditioners is out of scope.

The executable evidence consists of four self-written probes under `support/`. All are toy models:

| Probe | What it is |
| --- | --- |
| `probe_residual_gap.py` | Textbook CG in NumPy |
| `probe_backward_error.py` | Backward-error formulas, a small GMRES, and LAPACK-style componentwise refinement |
| `probe_mixed_ir.py` | Re-implementation of the `DSGESV` control flow on NumPy LU |
| `probe_cestac_toy.py` | Re-implementation of CESTAC with exact random rounding |

They demonstrate mechanisms, not properties of PETSc, Belos, Ginkgo, CADNA or Verificarlo. They ran on an x86-64 cloud VM (2 sockets × 24 cores × 2 threads, `Intel(R) Xeon(R) CPU @ 2.60GHz` per `lscpu`) with Python 3.13.15 and NumPy 2.3.5.

The backward-error results quoted assume real (or complex) dense or sparse linear systems `Ax = b` in IEEE binary floating point. Nonlinear solvers enter only through the inexact-Newton forcing-term analysis and PETSc's `SNES` defaults.

## Findings

### 1. What a stopping test must compute for acceptance to entail an accuracy statement

#### 1.1 The two backward-error characterizations

Basis: normative (published theorems, read through secondary statements where noted) + execution (toy check of attainability).

| Measure | Definition (`r = b − Ay`) | Perturbation class | Attaining perturbation | Source |
| --- | --- | --- | --- | --- |
| Normwise (Rigal–Gaches 1967) | `η_{E,f}(y) = ‖r‖ / (‖E‖‖y‖ + ‖f‖)` | `(A+ΔA)y = b+Δb`, `‖ΔA‖ ≤ η‖E‖`, `‖Δb‖ ≤ η‖f‖` | rank one: `ΔA = (‖E‖‖y‖/(‖E‖‖y‖+‖f‖)) r yᵀ/‖y‖²` (2-norm), `Δb = −(‖f‖/(‖E‖‖y‖+‖f‖)) r` | Rigal–Gaches 1967 as restated by Strakoš–Paige 2006 and D. J. & N. J. Higham 1992 |
| Componentwise (Oettli–Prager 1964) | `ω_{E,f}(y) = max_i |r_i| / (E|y| + f)_i`, with `0/0 := 0` and `ξ/0 := ∞` | `|ΔA| ≤ ω E`, `|Δb| ≤ ω f` entrywise | diagonal scaling of `r` | Oettli–Prager 1964 as restated in Arioli–Demmel–Duff 1989 §1 |

Common choices are `E = A, f = b` (normwise relative), `E = A, f = 0` (perturb the matrix only), `E = 0, f = b` (perturb the data only, `η = ‖r‖/‖b‖`), and `E = |A|, f = |b|` (componentwise relative; perturbations preserve sparsity and scaling).

`probe_backward_error.py` section A builds the Rigal–Gaches rank-one perturbation for a random 50×50 system and checks that `(A+ΔA)y = b+Δb` holds to `9.4e-15`, with `‖ΔA‖/‖A‖ = ‖Δb‖/‖b‖ = η = 3.825e-07`.

#### 1.2 Acceptance test → entailed statement

Basis: derived from §1.1. `τ` is the user tolerance, `y` the accepted iterate and `r = b − Ay` the *true* residual.

| Acceptance test actually evaluated | What acceptance entails | What it does not entail |
| --- | --- | --- |
| `‖r‖ ≤ τ(‖A‖‖y‖ + ‖b‖)` | `η_{A,b}(y) ≤ τ` exactly | Componentwise accuracy; forward error |
| `‖r‖ ≤ τ‖b‖` | `η_{0,b}(y) ≤ τ`, and since `‖A‖‖y‖ + ‖b‖ ≥ ‖b‖`, also `η_{A,b}(y) ≤ τ` | Same as above |
| `‖r‖ ≤ τ‖r_0‖`, `x_0 ≠ 0` | `η_{0,b}(y) ≤ τ‖r_0‖/‖b‖`, which is unbounded when `x_0` is poor | Any `τ`-level backward error |
| `‖M⁻¹r‖ ≤ τ‖M⁻¹b‖` (left-preconditioned norm) | `η` of the *preconditioned* system `M⁻¹A x = M⁻¹b` ≤ `τ`; for the original system `‖r‖/‖b‖ ≤ κ(M)·τ` | `‖r‖/‖b‖ ≤ τ` |
| Recursively updated `‖r_k‖ ≤ τ‖b‖` | Nothing about `b − A x_k` beyond `‖b − A x_k‖ ≤ τ‖b‖ + ‖b − A x_k − r_k‖` | A bound unless the gap term is bounded separately (§2.1) |
| `max_i |r_i|/(|A||y|+|b|)_i ≤ τ` (LAPACK `xGERFS` quantity) | Componentwise relative backward error `≤ τ`; `y` solves a nearby system with the same sparsity | Forward error, which needs `cond(A, x)` |
| Small update `‖x_k − x_{k−1}‖ ≤ τ‖x_k‖` (PETSc `SNES` `stol`) | Nothing about the residual | Any backward error |

A **forward-error** statement additionally needs a condition number. Higham's rule of thumb is "forward error ≲ condition number × backward error". For the componentwise case, fixed-precision refinement yields `‖x − x̂‖∞/‖x‖∞ ≲ cond(A,x)u` with `cond(A,x) = ‖|A⁻¹||A||x|‖∞/‖x‖∞` (Higham, "What Is Backward Error?" and "What Is Iterative Refinement?").

`probe_backward_error.py` section E solves the 12×12 Hilbert system with LAPACK `dgesv` through NumPy:

| Quantity | Value |
| --- | --- |
| `κ₂` | `1.78e16` |
| `η` | `6.7e-17` |
| `ω` | `1.0e-16` |
| Forward error | `0.18` |
| First-order bound `2κη` | `2.37` |

Basis: execution (toy model).

#### 1.3 Sparse backward error and the safe denominator

Basis: normative (Arioli–Demmel–Duff 1989, read) + source (LAPACK).

The componentwise formula breaks down when `(|A||y| + |b|)_i` is zero or tiny.

- **Arioli–Demmel–Duff (1989)** split the equations by a threshold. In their words: "τ_i = 1000 n ε (‖A_i·‖∞ ‖x̂‖∞ + |b_i|)", "about 1000 times larger than the maximum possible roundoff error committed in computing w". For rows below the threshold they replace `f_i` by a larger normwise surrogate (`f^(2) = |A^(2)| e ‖x̂‖∞` or `‖b‖∞ e`). This yields two backward errors `ω1`, `ω2`, combined with two condition numbers in their error bound. They conclude that "it is possible and inexpensive to guarantee solutions of sparse linear systems that are exact solutions of a nearby system whose matrix has the same sparsity structure", at a cost of "as little as two matrix-vector multiplications".
- **Reference LAPACK `dgerfs`** implements a production variant (`SRC/dgerfs.f`, lines 301–343). The comment describes `max(i) ( abs(R(i)) / ( abs(op(A))*abs(X) + abs(B) )(i) )`, and "If the i-th component of the denominator is less than SAFE2, then SAFE1 is added to the i-th components of the numerator and denominator before dividing". Here `SAFE1 = NZ*SAFMIN`, `SAFE2 = SAFE1 / EPS`, and `NZ = N + 1` for the dense routine (lines 278–284).
- **The `dgerfs` stopping rule** (lines 345–361) continues refinement only while `BERR( J ).GT.EPS .AND. TWO*BERR( J ).LE.LSTRES .AND. COUNT.LE.ITMAX`, with `ITMAX = 5` (lines 203–204). That is: componentwise backward error above machine epsilon, still halving, and at most five steps. `BERR` is documented as "the smallest relative change in any element of A or B that makes X(j) an exact solution" (lines 141–143).

Toy demonstration (`probe_backward_error.py` section D; Basis: execution, toy model). The system is a 400×400 tridiagonal `[−1, 4, −1]` whose odd rows are scaled by `1e-10`, solved by unpreconditioned GMRES stopped at `‖r‖/‖b‖ ≤ 1e-10`:

| State | `η` | `ω` | Forward error |
| --- | --- | --- | --- |
| After GMRES (1 iteration, `‖r‖/‖b‖ = 8.25e-11`) | `3.89e-11` | `1.00` | `0.73` |
| After one LU refinement step | `4.0e-17` | `1.05e-15` | `1.95e-16` |

The normwise test is blind to the down-scaled rows: they contribute `1e-10` of `‖b‖`.

#### 1.4 Baseline and norm choices in practice

Basis: execution (toy model, `probe_backward_error.py` sections B–C) + source (§3).

- **Initial-residual baseline.** CG on a 100×100 SPD system (κ = 1e3) with `x_0 = 1e6·randn`, tolerance `1e-8`:

  | Baseline | Stops at | `‖b−Ax‖/‖b‖` | `η` | Forward error |
  | --- | --- | --- | --- | --- |
  | `‖r_0‖` (Belos default scaling, "Norm of Initial Residual") | `k = 136` | `8.4e-3` | `1.5e-3` | `0.82` |
  | `‖b‖` (PETSc and Ginkgo default baseline) | `k = 230` | `9.3e-9` | `2.1e-9` | `2.5e-7` |

  Strakoš and Paige make the same point: "for an unwise choice of x_0 this may differ greatly from the frequently used relative residual norm ‖r_n‖₂/‖r_0‖₂".
- **Left-preconditioned norm.** Left-Jacobi GMRES on a 200×200 matrix with row scales spread over `1…1e6`, `b = 1`, stopped PETSc-style at `‖M⁻¹r‖/‖M⁻¹b‖ ≤ 1e-5`:

  | Iterations | Preconditioned ratio | Unpreconditioned `‖r‖/‖b‖` | `η_{A,b}` |
  | --- | --- | --- | --- |
  | 4 | `6.4e-6` | `0.24` | `1.2e-6` |

  The last two columns differ because `‖A‖‖x‖ ≫ ‖b‖` here: the iterate is a normwise-backward-stable answer that leaves 24% of `b` unexplained.

### 2. Mechanisms by which reported and true convergence diverge

| Mechanism | Published account | Detecting test | Production mitigation at pinned revisions |
| --- | --- | --- | --- |
| Recursively updated residual drifts from `b − A x_k` | Greenbaum 1997, abstract: the difference "depends on the machine precision ϵ and on the maximum norm of an iterate divided by the norm of the true solution"; when updated residuals become tiny, "the actual residual norm reaches the level ϵ‖A‖‖x‖ times the maximum ratio of the norm of an iterate to that of the true solution". Restated bound: `‖f_n‖ ≤ O(ε)‖A‖(‖x‖ + max_i ‖x̄_i‖)` for the gap `f_n = r̄_n − (b − Ax̄_n)` (Carson, Rozložník, Strakoš, Tichý, Tůma, preprint §3, eq. 3.7). Pipelined CG adds recurrences whose local rounding errors reduce attainable accuracy; Cools et al. 2018 (abstract) "estimate the gap between the true residual and the recursively computed residual" and propose automated residual replacement | Explicit `b − A x_k` at acceptance | Belos `StatusTestImpResNorm`; SciPy `gmres` outer check; PETSc `KSPPIPECGRR` automated residual replacement ("{cite}`cools2018analyzing`", `pipecgrr.c` line 238); PETSc GMRES restart check (§3.1) |
| Residual replacement | van der Vorst & Ye 2000, abstract: occasional replacement of computed by true residuals "improves the agreement of the computed residuals and the true residuals to the level of O(u) ||A|| ||x||", with replacement steps chosen by computable error bounds so that the recurrences "are perturbed within safe bounds" | n/a (repair) | PETSc `KSPPIPECGRR` |
| Loss of orthogonality in Gram–Schmidt Arnoldi | MGS-GMRES "is backward stable" (Paige–Rozložník–Strakoš 2006, abstract). The class of systems is restricted to `σ_min(A)` large relative to `n²ε‖A‖_F`; the inequality was read from extracted text with symbols partly lost, and the theorem's constants were not read. Giraud–Langou–Rozložník 2005: "the loss of orthogonality in CGS leads to a very poor limiting accuracy of the related GMRES method. In this case, the reorthogonalization is mandatory" | Explicit residual; orthogonality monitor | PETSc default is classical Gram–Schmidt *without* refinement (§3.1); Belos GMRES default `"ICGS"` (iterated classical Gram–Schmidt) |
| Preconditioned or wrongly scaled norm | §1.2–1.4 | Unpreconditioned explicit residual or backward error | Belos explicit test when a left preconditioner is present (§3.2); SciPy `gmres` outer check |
| Inexact Newton forcing terms | Dembo–Eisenstat–Steihaug 1982: inexact Newton steps satisfy `‖F(x_k) + F′(x_k)s_k‖ ≤ η_k‖F(x_k)‖`. Restated by Eisenstat–Walker §1: `0 ≤ η_k ≤ η_max < 1` gives local q-linear convergence in `‖F′(x*)·‖` with rate ≤ `η_max`, `η_k → 0` gives q-superlinear, and `η_k = O(‖F(x_k)‖)` gives q-quadratic convergence. Eisenstat–Walker 1996 Choice 1: `η_k = |‖F(x_k)‖ − ‖F(x_{k−1}) + F′(x_{k−1})s_{k−1}‖| / ‖F(x_{k−1})‖`. Choice 2: `η_k = γ(‖F(x_k)‖/‖F(x_{k−1})‖)^α`. Both safeguarded when the previous term exceeds `.1`; "choosing η_k too small may lead to oversolving" | Nonlinear residual `‖F(x_k)‖` | PETSc `SNES` default `rtol = 1e-8`, `abstol = 1e-50`, `stol = 1e-8` (`snes.c` 1837–1839). Eisenstat–Walker off by default (`ksp_ewconv = PETSC_FALSE`, line 1910). When on: version 2, `rtol_0 = 0.3` ("Eisenstat and Walker suggest rtol_0=.5, but this was too large for some test cases"), `rtol_max = 0.9`, `gamma = 1.0`, `alpha = (1+√5)/2`, `threshold = 0.1` (lines 1943–1951) |
| Step-length acceptance | — | Residual at acceptance | PETSc `SNESConvergedDefault` declares `SNES_CONVERGED_SNORM_RELATIVE` when `snorm < snes->stol * xnorm` (`snesut.c` 747–749): a small step, not a small residual |
| Mixed-precision refinement | Carson–Higham 2018 (Table 7.1, preprint): LU-based refinement with factorization precision `u_f` is guaranteed to converge for `κ∞(A)` up to `10^4` (`u_f` = half) or `10^8` (`u_f` = single), to a normwise backward error at the working precision ("η(x̂_i) ≲ pu") and forward error `≲ 4p u_r cond(A,x) + u`. GMRES-based refinement (Table 8.1) extends the bound up to `κ∞(A) ≤ 10^16`, "although in general there is no guarantee that GMRES will converge quickly" (abstract); Langou et al. 2006: of 147 LAPACK test matrices, 15 with κ near `1e15` did not converge, 18 overflowed in conversion, 18 failed single LU, and "for all those matrices DSGESV switches, as expected, to DGESV" | Normwise backward error in the working precision | LAPACK `DSGESV` (§3.5) |

Toy evidence (Basis: execution, toy model):

- **Residual gap** (`probe_residual_gap.py`; CG on a 200×200 SPD matrix with geometric spectrum, κ = 1e4):

  | Precision | Updated residual | True relative residual at the same point | Gap estimate `u‖A‖max_j‖x_j‖/‖b‖` |
  | --- | --- | --- | --- |
  | binary32 | passes `1e-8` at `k = 512` | `6.4e-7` | final measured gap `7.7e-7` vs estimate `2.3e-7` |
  | binary64 | `5.0e-21` at `k = 1100` | `1.32e-15` | gap stays within a factor ≈ 3.6 of the estimate |

  The estimate tracks the measured gap only to within a small constant. It is a heuristic `u‖A‖max‖x_j‖` scale, not Greenbaum's exact bound.
- **Mixed-precision refinement** (`probe_mixed_ir.py`; binary32 LU, binary64 residual, `DSGESV` acceptance test; 200×200 matrices with prescribed singular values):

  | `κ₂` | Iterations | Accepted | Forward error |
  | --- | --- | --- | --- |
  | `1e2` | 1 | yes | `1.2e-13` |
  | `1e5` | 2 | yes | `4.4e-12` |
  | `1e7` (`κ∞·u32 ≈ 6`) | 3 | yes | `2.6e-9` |
  | `1e9` | 30 | **not accepted** | `1.2e10` (diverged) |

  `DSGESV` would fall back to binary64 factorization in the last case. In every accepted case, acceptance certified `η_{A,0} ≤ 1.3e-15` (infinity norm, perturbing `A` only; the `DSGESV` threshold is `√n·ε ≈ 3.1e-15` for `n = 200`). The forward error scaled with κ.

### 3. Default convergence tests in production libraries (Basis: source)

#### 3.1 PETSc (`petsc/petsc` @ `a78a7628566ecd590e0aaab6176b0f93422bab63`)

- **Defaults** (`src/ksp/ksp/interface/itcreate.c`, lines 813–818): `ksp->default_rtol = ksp->rtol = 1.e-5;`, `ksp->default_abstol = ksp->abstol = PetscDefined(USE_REAL_SINGLE) ? 1.e-25 : 1.e-50;`, `ksp->default_divtol = ksp->divtol = 1.e4;`, `max_it = 10000`. `guess_zero = PETSC_TRUE` (line 823).
- **Test** (`src/ksp/ksp/interface/iterativ.c`, `KSPConvergedDefault`, lines 1492–1600).
  - At `n == 0`, `rnorm0` is the current `rnorm` (`‖r_0‖ = ‖b‖` in the active norm when `guess_zero`). With a nonzero guess it is recomputed as the norm of `b`, or of the preconditioned `b`, unless `KSPConvergedDefaultSetUIRNorm()` selects `‖b − A x_0‖` (lines 1512–1561).
  - Then `ksp->ttol = PetscMax(ksp->rtol * ksp->rnorm0, ksp->abstol)` (line 1562) and convergence is `if (rnorm <= ksp->ttol)` (line 1583).
  - The doc comment says "reaches convergence when rnorm < MAX (rtol * rnorm_0, abstol)" (line 1459). The code uses `≤`.
  - The input is documented as "residual norm (may be estimated, depending on the method may be the preconditioned residual norm)" (line 1439).
  - Divergence: `rnorm >= ksp->divtol * ksp->rnorm0` (line 1595); NaN/Inf gives `KSP_DIVERGED_NANORINF` (lines 1567–1578).
  - "By default, reaching the maximum number of iterations is considered divergence" (line 1461).
- **Default norm.** `KSPCreate_GMRES` ranks `KSP_NORM_PRECONDITIONED` with `PC_LEFT` highest (priority 4; `gmres.c` lines 787–791). `KSPCreate_CG` does the same with priority 3 (`cg.c` lines 844–847). With default options the test therefore measures the norm of the preconditioned residual against `‖B⁻¹ b‖`. In `KSPCG` that residual is updated recursively (`cg.c` line 419: `VecAXPY(R, -a, W); /*     r <- r - aw */`; preconditioned norm at lines 427–429).
- **Default preconditioner.** On one MPI process `PCGetDefaultType_Private` picks `PCICC` when an ICC factorization is available and symmetry is known, otherwise `PCILU`; on several processes it picks `PCBJACOBI` (`src/ksp/pc/interface/precon.c`, lines 13–58).
- **No explicit confirmation in `KSPConvergedDefault`.** The only true-residual cross-check found on the default path is at each GMRES restart, where `KSPInitialResidual` recomputes the (preconditioned) residual (`gmres.c` line 213) and the cycle compares it with the recursion's estimate (`gmres.c` lines 98–106): "the constant .1 is arbitrary, just some measure at how incorrect the residuals are". If `|res − ksp->rnorm| > gmres->breakdowntol * gmres->rnorm0` the solver logs "Residual norm computed by GMRES recursion formula %g is far from the computed residual norm %g at restart" and returns `KSP_DIVERGED_BREAKDOWN`. Here `breakdowntol = 0.1` and `haptol = 1.0e-30` (lines 810–811), and the default restart length is 30 (`gmresimpl.h` line 82).
- **Documentation/code disagreement on orthogonalization.** `KSPCreate`'s note says "The default `KSPType` is `KSPGMRES` with a restart of 30, using modified Gram-Schmidt orthogonalization" (`itcreate.c` line 798). The same function sets `ksp->orthog = KSPOrthogonalizationClassicalGramSchmidt;` and `ksp->cgstype = KSP_ORTHOGONALIZATION_CGS_REFINE_NEVER;` (lines 827–828). `KSPCreate_GMRES` does not override `orthog` (`gmres.c` 780–818), and `KSPView_GMRES` would print "classical (unmodified) Gram-Schmidt orthogonalization with no iterative refinement" (line 447). The MGS-GMRES backward-stability theorem (§2) therefore does not directly cover PETSc's default configuration.
- **`SNES`.**
  - Default tolerances: `rtol = 1e-8`, `abstol = 1e-50`, `stol = 1e-8` (double precision; `snes.c` lines 1837–1839).
  - Acceptance on `fnorm <= snes->ttol` (relative to the initial function norm) or on small step (`snesut.c` lines 744–749).
  - Eisenstat–Walker forcing terms are opt-in (`-snes_ksp_ew`).

#### 3.2 Trilinos Belos (`trilinos/Trilinos` @ `59703d7d03c88652d111c902535b0a4fb57f7cce`)

- **Default tolerance**: `DefaultSolverParameters::convTol = 1.0e-8` (`packages/belos/src/BelosTypes.cpp` line 201).
- **`StatusTestImpResNorm` semantics** (`BelosStatusTestImpResNorm.hpp`).
  - The class documentation (lines 47–66) explains: "Once the implicit residual norm reaches the convergence tolerance, this test then checks the explicit residual norm to make sure that it has reached the convergence tolerance as well"; on failure it makes the current tolerance smaller, and "If that doesn't work, this test declares a loss of accuracy".
  - Defaults set in the constructor (lines 389–406): 2-norm residual, scaling `NormOfInitRes` (2-norm of the initial residual).
  - **Loss of accuracy still counts as passed.** In `checkStatus` (lines 649–709), when the explicit scaled residual exceeds `tolerance_` and `diff = |implicit − explicit| > currTolerance_`, the code sets `lossDetected_ = true;` and executes `have2++; // Count this right-hand side as converged.` The closing comment: "report a loss of accuracy, but mark this right-hand side converged". Consequently `getStatus() == Passed` does **not** imply that the explicit residual met the tolerance. Callers must also read `getLOADetected()`.
  - Otherwise the current tolerance is reduced by `currTolerance_ = currTolerance_ - onePointFive * diff;` (with a `+= oneTenth * diff` loop to keep it positive; lines 701–707). The code carries the maintainer comment "mfh 23 Apr 2012: I have no idea why the currTolerance_ update formula is done the way it's done below. It doesn't make sense to me. It definitely makes the current tolerance smaller, though, which is what we want." (lines 691–694).
- **`PseudoBlockGmresSolMgr` composition** (`BelosPseudoBlockGmresSolMgr.hpp`).
  - With a left preconditioner, `expResTest_ = true` (lines 1059–1062) and the convergence test is `StatusTestCombo_t::SEQ` of two `StatusTestGenResNorm` objects: implicit, scaled by the default `"Norm of Preconditioned Initial Residual"`, then explicit, scaled by the default `"Norm of Initial Residual"` (lines 473–474, 1064–1089). `StatusTestGenResNorm::getLOADetected()` always returns `false` (`BelosStatusTestGenResNorm.hpp` line 209).
  - Without a left preconditioner, it uses `StatusTestImpResNorm` (lines 1091–1107).
  - When the combined test passes and `expConvTest_->getLOADetected()`, `solve()` sets `retType = LossOfAccuracyDetected` and prints "Warning! Solver has experienced a loss of accuracy!" (lines 1269–1286). It returns that code instead of `Converged` (lines 1587–1590; enum value 7, "Convergence was not reached because loss of accuracty was detected", `BelosTypes.hpp` line 141). At the solver-manager level the condition is therefore surfaced.
- **Documentation/code disagreement.** The `isLOADetected()` documentation (lines 301–326) says: "When using a left preconditioner, this solver tries to detect if the implicit residuals have converged but the explicit residuals have not ... it declares a 'loss of accuracy'". It also says "When *not* using a left preconditioner, this solver will iterate until both the implicit and explicit residuals converge ... does *not* report a 'loss of accuracy'". The code at lines 1059–1107 does the opposite. The loss-of-accuracy-capable `StatusTestImpResNorm` is installed only when there is **no** left preconditioner, and the left-preconditioned path uses the `SEQ` combination, which can never report loss of accuracy.
- **Cosmetic diagnostic bug.** `resFormStr()` prints the scaling norm with `oss << ((scalenormtype_==OneNorm) ? "1-Norm" : (resnormtype_==TwoNorm) ? "2-Norm" : "Inf-Norm");` (`BelosStatusTestImpResNorm.hpp` line 301; identical in `BelosStatusTestGenResNorm.hpp` line 264). The second condition tests the residual norm type, so the printed scaling norm is wrong whenever the two norm types differ. This affects only the description string.
- **CG solver managers.** `PseudoBlockCGSolMgr` uses `StatusTestGenResNorm` (`using StatusTestResNorm_t = Belos::StatusTestGenResNorm<...>`, line 537) with its default `Implicit` residual form. The comment reads "Implicit residual test, using the native residual to determine if convergence was achieved." (lines 625–629). No explicit check is configured on this path. The CG iteration's native residual is the recursively updated one: `getNativeResiduals` returns `R_` (`BelosPseudoBlockCGIter.hpp` line 198), and `R_` is updated by `// Compute the new residual R_ := R_ - alpha * AP_` (lines 475–477). `BlockCGSolMgr` explicitly calls `defineResForm(StatusTestResNorm_t::Implicit, normType)` (lines 644, 671–672).

#### 3.3 Ginkgo (`ginkgo-project/ginkgo` @ `796a388db0e8fb8c2a2d9918c658858bcab9c798`)

- **Modes** (`include/ginkgo/core/stop/residual_norm.hpp` line 37): `enum class mode { absolute, initial_resnorm, rhs_norm };`.
- **Defaults**: `reduction_factor{5 * std::numeric_limits<...>::epsilon()}` (lines 137–138; ≈ `1.1e-15` in binary64) and `baseline` `mode::rhs_norm` (line 150). Ginkgo solvers take user-supplied criteria. The paper (Anzt et al. 2022, §2.5) describes Time, Iteration and residual-norm criteria combined by logical OR, noting that "some stopping criteria may detain the iteration process before 'convergence' is reached".
- **What `ResidualNorm` measures.** It is documented as "Stopping criterion based on the explicit residual norm ‖r_k‖ = ‖b − A x_k‖" (lines 88–92). But "Per-iteration, the criterion prefers a pre-computed residual norm passed by the solver ... otherwise it falls back to computing the 2-norm of the residual vector itself" (lines 104–107).
  - `check_impl` (`core/stop/residual_norm.cpp` lines 165–195) computes `b − A x` only when neither a residual norm nor a residual vector is supplied.
  - `Cg::apply_dense_impl` supplies `.residual(r)` (`core/solver/cg.cpp` lines 162–167). Its `r` is updated recursively by the comment-documented step `// r = r - tmp * q` (lines 186–195).
  - For CG the "explicit" criterion therefore tests the recursively updated residual. Ginkgo's naming distinguishes "norm computed from a vector" from "solver-maintained squared estimate" (`ImplicitResidualNorm`, which uses `rho = r·z`, a preconditioned quantity). It does not distinguish true from updated residuals.
  - The `ImplicitResidualNorm` documentation itself warns that the estimate "can drift from the true residual norm on long runs in finite precision" (lines 185–188).

#### 3.4 SciPy (`scipy/scipy` @ `5a63b65045f80b5a2198f0d7c00d9935efe9a676`)

All in `scipy/sparse/linalg/_isolve/iterative.py`:

- `_get_atol_rtol` sets `atol = max(float(atol), float(rtol) * float(b_norm))` with default `rtol=1e-5`, `atol=0.` (lines 11–22).
- **`cg`** tests `if np.linalg.norm(r) < atol` on `r` updated by `r -= alpha*q` (lines 398–425). This is an implicit-only test.
- **`cgs`** recomputes the residual. The comment reads "Due to numerical error build-up the actual residual is computed instead of the following two lines that were in the original FORTRAN templates", followed by `r = b - matvec(x)` (lines 574–580).
- **`gmres`** runs its inner loop on the left-preconditioned residual estimate `presid <= ptol` (lines 726–735). After each restart cycle it computes `r = b - matvec(x)` and accepts only if `rnorm <= atol`. If the inner test passed but the outer did not, it tightens the inner tolerance (`ptol_max_factor = max(eps, 0.25 * ptol_max_factor)`; lines 827–849). This is the same implicit-then-explicit structure as Belos, with an adaptive inner tolerance.

#### 3.5 Reference LAPACK (`Reference-LAPACK/lapack` @ `b458ca66c8f828f246bae508888b4b79a3244900`)

- **`dgerfs`**: componentwise backward-error stopping (§1.3).
- **`DSGESV`** (`SRC/dsgesv.f`). Documented stopping rule (lines 56–66): "ITER > ITERMAX or RNRM < SQRT(N)*XNRM*ANRM*EPS*BWDMAX", infinity norms, "The value ITERMAX and BWDMAX are fixed to 30 and 1.0D+00".
  - Implemented as `CTE = ANRM*EPS*SQRT( DBLE( N ) )*BWDMAX` (line 281) and `IF( RNRM.GT.XNRM*CTE )` (lines 340, 393).
  - Acceptance therefore certifies a normwise backward error `η_{A,0} ≤ √n·ε_64` in the infinity norm, perturbing `A` only.
  - On failure, `ITER = -ITERMAX - 1` and the routine resorts to binary64 factorization (lines 409–418). Other negative codes cover narrowing overflow (`-2`) and `SGETRF` failure (`-3`).

#### 3.6 Cross-library matrix

| Library / solver | Default tolerance | Default baseline | Norm monitored | True residual confirmed? | Accuracy statement on success |
| --- | --- | --- | --- | --- | --- |
| PETSc GMRES / CG | `1e-5` relative, `1e-50` absolute | `‖b‖` (or `‖B⁻¹b‖`) | Left-preconditioned (default) | No; GMRES restart consistency check only | Preconditioned-system relative residual |
| Belos PseudoBlockGMRES, no left prec. | `1e-8` | `‖r_0‖` | Implicit, then explicit | Yes; loss of accuracy reported via return code | Explicit `‖r‖/‖r_0‖ ≤ 1e-8` unless `LossOfAccuracyDetected` |
| Belos PseudoBlockGMRES, left prec. | `1e-8` | Implicit: preconditioned `‖r_0‖`; explicit: `‖r_0‖` | Implicit, then explicit | Yes; iterates until both pass or limits hit | Explicit `‖r‖/‖r_0‖ ≤ 1e-8` |
| Belos CG | `1e-8` | `‖r_0‖` | Implicit only | No | None about the true residual |
| Ginkgo CG + `ResidualNorm` | User-supplied (factory default `5ε`) | `‖b‖` | Updated `r` | No | None about the true residual |
| SciPy `cg` | `1e-5` | `‖b‖` | Updated `r` | No | None about the true residual |
| SciPy `gmres` | `1e-5` | `‖b‖` | Preconditioned estimate, then true | Yes, per restart | `‖b−Ax‖/‖b‖ ≤ 1e-5` (implies `η_{A,b} ≤ 1e-5`) |
| LAPACK `dgerfs` | `EPS`, halving, ≤ 5 steps | componentwise | True residual | Yes | Componentwise backward error in `BERR` |
| LAPACK `DSGESV` | `√n·ε` normwise | `‖A‖∞‖x‖∞` | True residual | Yes | `η_{A,0} ≤ √n ε_64` or fallback to `DGESV` |

### 4. Stochastic-arithmetic estimates of significant digits

#### 4.1 CESTAC / discrete stochastic arithmetic (CADNA)

Basis: documentation + literature.

- **Mechanism.** In Denis et al.'s description (arXiv v4, §2): "DSA has made the choice to carry out a single program in which each FP operation is performed N times with a rounding mode towards plus or minus infinity. For each sample, the rounding mode is randomly chosen ... The number of significant digits is computed by using the Student distribution", and "The CADNA library is an implementation of Discrete Stochastic Arithmetic (DSA) with N = 3 samples." The CADNA group's own description (F. Jézéquel, lecture slides "Numerical validation using stochastic arithmetic", slides 19–33):
  - the number of correct decimal digits of the mean `R̄` of `N` samples is estimated as `C_R̄ ≈ log10(√N|R̄|/(στ_β))`, with `τ_β` from Student's distribution with `N−1` degrees of freedom;
  - "each operation executed N = 3 times with a random rounding mode", at confidence 95%;
  - "With β = 0.95 and N = 3, the probability of overestimating the number of correct digits of at least 1 is 0.054%" and of underestimating by at least 1 digit "29%";
  - "The CESTAC method is based on a 1st order model. A multiplication of two insignificant results or a division by an insignificant result may invalidate the 1st order approximation. Therefore the CESTAC method requires a dynamical control of multiplications and divisions";
  - a computational zero `@.0` is a result with "∀i, R_i = 0 or C_R̄ ≤ 0";
  - Vignes (2004, abstract) defines Discrete Stochastic Arithmetic as "the joint use of the synchronous implementation of the CESTAC method and the stochastic order relations". He adds that the library "is able to dynamically control the validity of the hypotheses which must hold so that results provided by CESTAC method are reliable. If the hypotheses do not hold then warnings are printed in a special file."
- **What CADNA reports.** The CADNA site states that CADNA "estimate[s] in any computed result which digits are affected by round-off errors", implements stochastic order and equality relations, "detect[s] numerical instabilities", and "When a result is numerical noise the symbol @.0 is printed". Its controls "lead to a self-validation of the library. CADNA is able to detect when the conditions for a right estimation of the round-off errors are not satisfied anymore". Jézéquel & Chesneaux (2008, abstract): "by detecting all the instabilities which may occur at run time, a numerical debugging of the user code can be performed". The instability categories, per the same slides (slides 34, 38), are:
  - "unstable division: the divisor is insignificant";
  - "unstable power function";
  - "unstable multiplication: both operands are insignificant";
  - "unstable branching";
  - cancellation (`cancel_level` default 4), mathematical functions and intrinsics.
- **Validity is debated.** Denis et al. cite Chesneaux–Vignes, who argue that CESTAC estimates digits correctly "with a probability of 95%", and Chatelin, for whom "CESTAC's confidence cannot be greater than 5% under various conditions which are shown to be often met in practice". They note that "DSA is based on a first order model: some operations such as unstable division or unstable multiplication may invalidate the model". In their case study 4, "CADNA ... overestimates the number of significant digits of the result."
- **Use as a stopping criterion.** The CADNA group's "optimal stopping criterion" replaces `while (fabs(X-Y) > EPSILON)` by the stochastic relation `while (X != Y)`: "It would be optimal to stop when X − Y is an insignificant value". An example contrasts "Stopping criterion IEEE: |S_n − S_{n−1}| < 10⁻¹⁵|S_n|; CADNA: S_n == S_{n−1}" (slides 28, 52–53). The supporting theorem is for approximation methods with `L(h) − L = Kh^p + O(h^q)`: "If the convergence zone is reached, the digits common to two successive iterates are also common to the exact result, up to one" (slide 55). The premise "convergence zone is reached" carries the weight; §4.3 shows the rule firing outside it.

#### 4.2 Monte Carlo arithmetic (Verificarlo)

Basis: source + literature.

- **Perturbation model** (Denis et al. 2016, §2.1): `inexact(x) = x + 2^{e_x − t} ξ` with `ξ` uniform in `(−1/2, 1/2)`.
  - Random rounding perturbs outputs, precision bounding perturbs inputs, and full MCA does both.
  - Significant digits are `s' = −log_β(σ/|μ|)` over the sample distribution (Parker's formula).
  - The quad backend implements the noise as `/* noise = rand * 2^(exp) */` with "random number in (-0.5, 0.5)" (`src/backends/interflop-backend-mcaquad/interflop_mca.c` lines 268–291).
- **Backend status at the pinned revision.** `doc/02-Backends.md` heads the MCA section "MCA Backends (legacy)" and says "These backends are deprecated and the more efficient PRISM backend is prefered. MCA backends are only recommended when you need the mca or ib modes" (lines 439–447). PRISM "implements Stochastic Rounding and Up & Down rounding", instruments "at the IR level during compilation", and selects its mode with `--prism-backend=MODE` (lines 177–186). Default virtual precision is 53 (binary64) and 24 (binary32).
- **Digit estimator in Verificarlo CI** (`src/tools/ci/test_data_processing.py` lines 25–98):
  - If a normality test's `pvalue < 0.05`, it calls `sd.significant_digits(..., error=sd.Error.Relative, method=sd.Method.General, probability=0.9, confidence=0.95)`. Otherwise it uses the Stott-Parker formula `min(-np.log2(np.absolute(x.sigma / x.mu)), 53)`.
  - The lower confidence bound uses `sd.Method.CNH` with `probability=0.9`, `confidence=0.95`.
  - `sd` is the `significantdigits` package imported at line 23. Its `CNH` and `General` methods correspond to the framework of Sohier et al. 2021, whose abstract (the only part read) says it "unifies all existing definitions of the number of significant digits (CESTAC and MCA)" and provides "Sound confidence intervals ... both in the case of normally distributed results, and in the general case". The estimators' exact definitions were not read.
- **Cost.** In Denis et al. (arXiv v4, Table 1; compensated sum, 10⁶ elements, `-O0`, 16-core 2-socket Xeon E5 @ 2.70 GHz):

  | Configuration | Samples | Total time |
  | --- | --- | --- |
  | Original program | 1 | 0.056 s |
  | CADNA | 3 | 2.93 s (0.097 s/sample) |
  | Verificarlo, single thread | 128 | 834.57 s (6.52 s/sample) |
  | Verificarlo, 16 threads | 128 | 54.39 s |

  Derived: CADNA ≈ 52× the original run; Verificarlo per sample ≈ 116×. These figures predate the PRISM backend; PRISM cost is not measured here.

#### 4.3 Toy CESTAC applied to CG stopping

`probe_cestac_toy.py`. Basis: execution (toy re-implementation; not CADNA).

**Setup.** Every operation is performed in `N = 3` samples. Each result is rounded toward −∞ or +∞ at random, using exact rational arithmetic to decide the rounding. The digit estimate is `C = log10(√N|mean|/(τσ))` with `τ = 4.303`. Unstable multiplications (both operands insignificant) and divisions (divisor insignificant) are counted. The system is a 12×12 SPD matrix with κ = 1e6. The reference is (a) exact-arithmetic CG iterates `x_k` (CESTAC's reference) and (b) the exact solution `x*`.

| `k` | Estimated min digits of `x_k` | Actual digits vs exact `x_k` | Actual digits vs `x*` | Instabilities so far (div, mul) | "Update is @.0"? |
| --- | --- | --- | --- | --- | --- |
| 4 | 11.25 | 12.12 | −0.84 | (0, 0) | no |
| 6 | 6.54 | 7.43 | −0.86 | (0, 0) | no |
| 7 | 2.37 | 2.99 | −0.79 | (0, 11) | no |
| 8 | 2.37 | **−0.87** | −0.79 | (2, 70) | **yes** |
| 22 | 5.52 | 5.99 | 5.99 | (20, 651) | yes |
| 32 | 8.62 | 10.29 | 10.29 | (40, 1203) | yes |

Readings:

- **Before the first instability (k ≤ 7)** the estimate was conservative against the true rounding error relative to exact `x_k`, by 0.6–1.2 digits.
- **After instabilities began (k = 8–18)** the samples agreed with one another to 1–4 digits while all being far from exact `x_k`. The estimate was optimistic by up to ≈ 4.6 digits (k = 14: estimate 3.81, actual −0.83).
- **The "update is a computational zero" stop fired at k = 8**, where the iterate had no correct digit. A residual-based test on the updated residual first passed `1e-8` at `k = 22`.
- **In the converged phase (k ≥ 22)** the estimate was again conservative by 0.5–1.7 digits.

**What "N significant digits" means.** The estimate concerns the computed value of a finite computation versus the same computation in exact arithmetic. For an iterative method this is *not* the distance to the solution of `Ax = b`; an unconverged iterate can have many "significant" digits. In this run the over-optimistic estimates occurred only after the first reported instability. Estimates in the converged phase were conservative even though the instability counters kept rising. The method therefore vouches for a digit count only when self-validation reports no instability; with instabilities, the count may or may not be right. This mirrors the "first order model" caveat in the literature.

### 5. Performance and resource footprint (L1–L6)

| Level | Backward-error tests | Explicit residual confirmation | Stochastic arithmetic | Source of number |
| --- | --- | --- | --- | --- |
| L1 authoring | not measured | not measured | CADNA: "essentially changes in the declarations of variables" (CADNA site; qualitative) | documentation |
| L2 toolchain build | not measured (no library built) | not measured | not measured | — |
| L3 per-iteration overhead | `ω`: "as little as two matrix-vector multiplications" (ADD 1989); `η`: one norm of `A` (once) + one residual | One extra mat-vec + reduction per confirmation; Belos does it only after the implicit test passes (`checkStatus`, lines 612–622) | CADNA 3 samples: 2.93 s vs 0.056 s original (≈ 52×); Verificarlo 128 samples single-thread 834.57 s (Denis et al. Table 1) | literature, derived |
| L4 solver throughput | LAPACK `DSGESV` vs `DGESV` speedup 1.57 (Pentium IV, `n = 4000`), 1.53 (Opteron), 1.38 (Cray X1), 0.91 (SGI Octane) (Langou et al. 2006 preprint, Table 2) | not measured | not measured | literature |
| L5 checker cost | Toy probes: `probe_backward_error.py` 0.43 s, `probe_residual_gap.py` 0.37 s, `probe_mixed_ir.py` 0.34 s, `probe_cestac_toy.py` 1.0 s wall | — | — | execution (this host) |
| L6 memory | Componentwise `ω` needs one extra `n`-vector (`|A||y|+|b|`); `dgerfs` workspace `3*N` (doc line 148) | One `n`-vector per right-hand side (Belos clones the solution multivector, line 618) | `N = 3` copies of every value (CADNA) or `≥ 3` full runs (MCA) | source, derived |

No library was built; every L2 cell and every throughput figure not quoted from a paper is `not measured`.

### 6. Comprehensibility and conceptual simplicity (C1, C2)

- **C1: one statement, many quantities.** A reader of "converged, rtol = 1e-5" must know four hidden facts to interpret it:
  - which norm (preconditioned or not; PETSc default: preconditioned);
  - which baseline (`‖b‖`, `‖r_0‖`, preconditioned `‖r_0‖`);
  - which residual (updated, estimated, or true);
  - whether loss of accuracy is folded into success (Belos `StatusTestImpResNorm`).

  Each library documents some of these, and two documentation/code disagreements were found (PETSc Gram–Schmidt variant; Belos left-preconditioner LOA description). Diagnostics are therefore not self-explaining. The Belos `resFormStr()` bug can even mislabel the scaling norm.
- **C1: what a human can audit.** `η_{E,f}` and `ω_{E,f}` are short formulas with an explicit perturbation class. They can be audited by hand and checked constructively (§1.1 probe A).
- **C2: one invariant, one quantity.** A minimal, universal acceptance object is the triple *(true residual, perturbation class `(E,f)`, tolerance)*, reporting `η` or `ω`. It subsumes the special cases:
  - `‖r‖/‖b‖` is `E = 0, f = b`;
  - LAPACK `BERR` is `E = |A|, f = |b|`;
  - `DSGESV` is `E = A, f = 0`;
  - preconditioned tests are the same object on a different system.

  Implicit/explicit residual handling then becomes one rule: compute the true residual at acceptance. Loss of accuracy becomes a failed acceptance rather than a passed status plus a flag. The hidden complexity this moves is the cost of one true-residual evaluation per acceptance, the same cost Belos and SciPy `gmres` already pay. Realization-medium quirks (binary32 vs binary64, CGS vs MGS, pipelining) then change only whether acceptance is reachable, not what it means.

### 7. How the implementations and proposed solutions are validated (V1–V4)

- **V1: specification adequacy.** The tests examined encode different specifications, and none states its perturbation class in its result object. The constructive check (probe A) and the toy counter-examples (probes B–E) act as specification mutants: each shows a test that accepts an iterate failing a stricter, plausible reading of "accurate". No library test suite was examined for such mutants (not examined).
- **V2: differential and implementation validation.** Possible differential oracles: explicit-vs-implicit residual comparison (Belos, SciPy `gmres`, PETSc GMRES restart check), exact-rational CG (probe), and binary64 fallback (`DSGESV`). CADNA's self-validation (instability detection) is the stochastic-arithmetic analogue of a checker's admission test. Verificarlo CI computes digit confidence intervals. Fuzzing of the libraries' status tests was not found or performed (not examined).
- **V3: concurrency and hardware.** Pipelined and communication-hiding Krylov variants change the rounding pattern and the gap (Cools et al. 2018; PETSc `KSPPIPECGRR`). Their behaviour across MPI process counts or GPUs was not examined.
- **V4: field and replay.** Not examined. No incident report tying a production failure to a specific default test was collected for this report.

## Boundaries

- **Not examined.**
  - No PETSc, Trilinos, Ginkgo, SciPy, CADNA or Verificarlo build was compiled or run. Every library claim is from source reading at the pinned revision. Options files, environment variables, or solver-specific overrides (for example a preconditioner that changes `KSPSetNormType`) can change the effective default.
  - Belos block solvers other than `PseudoBlockGmres`, `BlockGmres` and the two CG managers.
  - Ginkgo solvers other than CG.
  - PETSc Krylov types other than GMRES, CG and PIPECGRR.
  - SciPy solvers other than `cg`, `cgs`, `gmres`.
- **CADNA source not examined.** No official public repository was found; only the project website, which states its features, and published papers were used. CADNA's behaviour on the toy CG problem is therefore **unknown**. The toy probe re-implements the published CESTAC recipe and adds only two of CADNA's instability checks (multiplication and division). The other documented checks (branching, functions, cancellation) were not modelled.
- **Literature read through secondary sources or abstracts** (see Evidence): Rigal–Gaches 1967, Oettli–Prager 1964, Paige–Rozložník–Strakoš 2006 (main theorem not read; no constants are stated here). Also read only through abstracts or restatements:
  - Greenbaum 1997 (abstract; bound as restated by Carson et al.);
  - van der Vorst & Ye 2000 (abstract; replacement test not read);
  - Dembo–Eisenstat–Steihaug 1982 (abstract; theorem as restated by Eisenstat–Walker);
  - Cools et al. 2018 (abstract);
  - Vignes 2004 (abstract);
  - Jézéquel & Chesneaux 2008 (abstract; the instability list and costs come from later CADNA-group material);
  - Sohier et al. 2021 (abstract).

  Not read: Vignes 1993, Higham's monograph, and Parker–Pierce–Eggert 2000 (Parker's formula is quoted via Denis et al.).
- **Known not to apply.** The MGS-GMRES backward-stability result does not cover PETSc's default classical Gram–Schmidt without refinement. Whether PETSc's default GMRES is backward stable on a given class of matrices is **unknown** from this investigation.
- **Toy numbers are not library numbers.** The gap, baseline, preconditioned-norm, mixed-precision and CESTAC figures come from self-written NumPy and Python code with fixed seeds. They demonstrate mechanisms and must not be read as measured properties of any library.
- **Unsupported stronger conclusions.**
  - The PETSc and Belos documentation/code disagreements are established at the pinned revisions only; whether they were ever consistent is not examined.
  - Neither disagreement was shown to cause an incorrect result in an application.
  - The Belos `resFormStr()` defect affects only printed descriptions.

## Evidence

Observation date: 2026-11-20 (UTC) for all source reads, DOI resolutions and executions.

**Source, by repository and revision.**

- `petsc/petsc` @ `a78a7628566ecd590e0aaab6176b0f93422bab63`:
  - `src/ksp/ksp/interface/iterativ.c` 1431–1600 (`KSPConvergedDefault`)
  - `src/ksp/ksp/interface/itcreate.c` 790–830 (`KSPCreate` defaults; line 798 note vs lines 827–828)
  - `src/ksp/ksp/impls/gmres/gmres.c` 86–175 (`KSPGMRESCycle`, restart check 98–106), 213 (`KSPInitialResidual` at each restart), 444–461 (`KSPView_GMRES` strings), 778–818 (`KSPCreate_GMRES`, supported norms 787–791, `haptol`/`breakdowntol` 810–811)
  - `src/ksp/ksp/impls/gmres/gmresimpl.h` 82
  - `src/ksp/ksp/impls/cg/cg.c` 415–440, 844–847
  - `src/ksp/ksp/impls/cg/pipecgrr/pipecgrr.c` 18–22, 238–250
  - `src/ksp/pc/interface/precon.c` 13–58
  - `src/snes/interface/snes.c` 1837–1839, 1910, 1943–1951
  - `src/snes/interface/snesut.c` 720–757
- `trilinos/Trilinos` @ `59703d7d03c88652d111c902535b0a4fb57f7cce`, under `packages/belos/src/`:
  - `BelosStatusTestImpResNorm.hpp` 23–66, 283–313, 387–410, 459–720, 779–838
  - `BelosStatusTestGenResNorm.hpp` 62–64, 209, 249–264, 359–362, 459–492
  - `BelosPseudoBlockGmresSolMgr.hpp` 255–328, 464–476, 1050–1107, 1255–1300, 1575–1591
  - `BelosBlockGmresSolMgr.hpp` 289–304, 780–810
  - `BelosPseudoBlockCGSolMgr.hpp` 301–311, 537, 615–630
  - `BelosPseudoBlockCGIter.hpp` 198, 449–477
  - `BelosBlockCGSolMgr.hpp` 304–317, 592, 644, 671–672
  - `BelosTypes.hpp` 124–145
  - `BelosTypes.cpp` 195–205
- `ginkgo-project/ginkgo` @ `796a388db0e8fb8c2a2d9918c658858bcab9c798`:
  - `include/ginkgo/core/stop/residual_norm.hpp` 20–40, 86–165, 170–206
  - `core/stop/residual_norm.cpp` 160–231
  - `core/solver/cg.cpp` 120–197
- `scipy/scipy` @ `5a63b65045f80b5a2198f0d7c00d9935efe9a676`: `scipy/sparse/linalg/_isolve/iterative.py` 11–22, 311–425, 572–584, 593–852.
- `Reference-LAPACK/lapack` @ `b458ca66c8f828f246bae508888b4b79a3244900`: `SRC/dgerfs.f` 136–170, 203–204, 276–365; `SRC/dsgesv.f` 56–66, 156–163, 215–219, 279–281, 338–418.
- `verificarlo/verificarlo` @ `5142c8f7a86106bce1800e433a49ec22c594f175`: `doc/02-Backends.md` 176–200, 205–220, 439–520; `src/backends/interflop-backend-mcaquad/interflop_mca.c` 268–320; `src/tools/ci/test_data_processing.py` 21–160.

**Literature.** DOIs were resolved through the DOI handle API (`https://doi.org/api/handles/<doi>`, `responseCode` 1) on 2026-11-20. Content was read as stated.

- J. L. Rigal, J. Gaches, "On the compatibility of a given solution with the data of a linear system," *J. ACM* 14(3):543–548, 1967, DOI `10.1145/321406.321416`.
  - Primary text not read.
  - Formula from Z. Strakoš & C. C. Paige, "Stopping criteria in iterative methods – a miscellaneous issue?", GAMM 2006 slides 7, 9, 17, 18.
  - Also from D. J. Higham & N. J. Higham, *SIAM J. Matrix Anal. Appl.* 13(1):162–175, 1992, §1.
- W. Oettli, W. Prager, *Numer. Math.* 6:405–409, 1964, DOI `10.1007/BF01386090`. Primary not read; theorem as restated by Arioli–Demmel–Duff 1989 §1.
- M. Arioli, J. W. Demmel, I. S. Duff, "Solving sparse linear systems with sparse backward error," *SIAM J. Matrix Anal. Appl.* 10(2):165–190, 1989, DOI `10.1137/0610013`. Full text read (OCR): abstract, pp. 166–170, 181.
- A. Greenbaum, "Estimating the attainable accuracy of recursively computed residual methods," *SIAM J. Matrix Anal. Appl.* 18(3):535–551, 1997, DOI `10.1137/S0895479895284944`. Abstract read (SIAM landing page). Bound as restated in E. C. Carson, M. Rozložník, Z. Strakoš, P. Tichý, M. Tůma, "The numerical stability analysis of pipelined conjugate gradient methods: historical context and methodology", author preprint, §3 eqs. (3.4)–(3.7).
- H. A. van der Vorst, Q. Ye, *SIAM J. Sci. Comput.* 22(3), 2000, DOI `10.1137/S1064827599353865`. Abstract read.
- C. C. Paige, M. Rozložník, Z. Strakoš, *SIAM J. Matrix Anal. Appl.* 28(1):264–284, 2006, DOI `10.1137/050630416`. Abstract and pp. 264–265 read; §8.2 theorem not read.
- L. Giraud, J. Langou, M. Rozložník, *Comput. Math. Appl.* 50:1069–1075, 2005, DOI `10.1016/j.camwa.2005.08.009`. Full text read (OCR), pp. 1071–1075.
- R. S. Dembo, S. C. Eisenstat, T. Steihaug, "Inexact Newton methods," *SIAM J. Numer. Anal.* 19(2), 1982, DOI `10.1137/0719025`. Abstract read; theorem as restated by Eisenstat–Walker 1996 §1.
- S. C. Eisenstat, H. F. Walker, *SIAM J. Sci. Comput.* 17(1), 1996, DOI `10.1137/0917003`. Full text read (author-hosted scan, pp. 16–23, 26).
- E. Carson, N. J. Higham, *SIAM J. Sci. Comput.* 40(2):A817–A847, 2018, DOI `10.1137/17M1140819`. Abstract read; mid-2017 preprint read (Corollaries 3.3 and 4.2, Tables 7.1 and 8.1); section and table numbers may differ in the published version.
- S. Cools, E. F. Yetkin, E. Agullo, L. Giraud, W. Vanroose, *SIAM J. Matrix Anal. Appl.* 39(1):426–450, 2018, DOI `10.1137/17M1117872`. Abstract (arXiv:1601.07068) read.
- J. Langou, J. Langou, P. Luszczek, J. Kurzak, A. Buttari, J. Dongarra, SC'06, DOI `10.1109/SC.2006.30`. Preprint dated May 1, 2006 read; abstract, pp. 3–8, Table 2.
- J. Vignes, *Math. Comput. Simul.* 35(3):233–261, 1993, DOI `10.1016/0378-4754(93)90003-D`; J. Vignes, *Numer. Algorithms* 37, 2004, DOI `10.1023/B:NUMA.0000049483.75679.ce`. 1993 paper not read; 2004 abstract read. Formulas and probabilities from F. Jézéquel, "Numerical validation using stochastic arithmetic", lecture slides (99 slides), slides 19–38 and 52–55.
- F. Jézéquel, J.-M. Chesneaux, *Comput. Phys. Commun.* 178(12):933–955, 2008, DOI `10.1016/j.cpc.2008.02.003`. Abstract read (HAL record hal-01146486). Costs from P. Eberhart, J. Brajard, P. Fortin, F. Jézéquel, "High performance numerical validation using stochastic arithmetic", *Reliable Computing* 21:35–52, 2015 (HAL hal-01254446, read). CADNA project website (`cadna.lip6.fr`) home page read 2026-11-20.
- C. Denis, P. de Oliveira Castro, E. Petit, "Verificarlo: checking floating point accuracy through Monte Carlo Arithmetic," ARITH 2016, DOI `10.1109/ARITH.2016.31`; arXiv:1509.01347 v4 read in full (§2, Table 1, case study 4).
- D. Sohier et al., "Confidence intervals for stochastic arithmetic," *ACM TOMS* 47(2), 2021, DOI `10.1145/3432184`. Abstract read (arXiv:1807.09655 page and the TOMS abstract).
- H. Anzt et al., "Ginkgo: a modern linear operator algebra framework for high performance computing," *ACM TOMS*, 2022, DOI `10.1145/3480935`; arXiv:2006.16852 v2 §2.5 read.
- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM 2002, DOI `10.1137/1.9780898718027`: not read. Higham's statements above are from his essays "What Is Backward Error?" (25 Mar 2020) and "What Is Iterative Refinement?" (13 Mar 2023).

**Execution.** Host: x86-64 cloud VM, 2 sockets × 24 cores × 2 threads, `Intel(R) Xeon(R) CPU @ 2.60GHz` (`lscpu`), Linux; Python 3.13.15, NumPy 2.3.5. Commands, run from `support/`:

```text
python3 probe_residual_gap.py     > probe_residual_gap.out     # 0.37 s wall
python3 probe_backward_error.py   > probe_backward_error.out   # 0.43 s wall
python3 probe_mixed_ir.py         > probe_mixed_ir.out         # 0.34 s wall
python3 probe_cestac_toy.py       > probe_cestac_toy.out       # 1.0 s wall
```

All seeds are fixed. The `.out` files preserved in `support/` are the outputs quoted above.

## Revalidation

- **PETSc default test.** Diff `src/ksp/ksp/interface/iterativ.c` `KSPConvergedDefault`, the `KSPCreate` default block and note in `itcreate.c`, and `KSPCreate_GMRES` / `KSPCreate_CG` supported-norm tables.
  - Grep: `grep -n "orthog *=\|cgstype *=\|modified Gram-Schmidt" src/ksp/ksp/interface/itcreate.c`.
  - Run any example with `-ksp_view` and `-ksp_converged_reason`; the view prints the orthogonalization actually used.
- **Belos.** Diff `BelosStatusTestImpResNorm.hpp` `checkStatus` around the comment "Count this right-hand side as converged", and `BelosPseudoBlockGmresSolMgr.hpp` around `getLeftPrec()` in `setParameters`/status-test construction against the `isLOADetected()` documentation. A single run with a left-preconditioned problem whose explicit residual cannot converge shows which path reports `LossOfAccuracyDetected`.
- **Ginkgo.** Check whether `Cg::apply_dense_impl` still passes `.residual(r)` and whether `ResidualNormBase::check_impl` still prefers `residual_` over recomputing `b − A x`.
- **SciPy.** Check `cg` for `r -= alpha*q` with `np.linalg.norm(r) < atol`, and `gmres` for `r = b - matvec(x)` after the inner loop.
- **LAPACK.** Check `ITMAX`, the `BERR` loop condition in `dgerfs.f`, and `ITERMAX`/`BWDMAX`/`CTE` in `dsgesv.f`.
- **Verificarlo.** Check whether `doc/02-Backends.md` still marks MCA backends as legacy, and the constants `probability = 0.9`, `confidence = 0.95`, `min_pvalue = 0.05` in `src/tools/ci/test_data_processing.py`.
- **Mechanisms.** Rerun the four probes. Each prints the numbers quoted, in under 2 seconds on a commodity x86-64 host. A changed NumPy or BLAS may move toy numbers in the last digits but not the qualitative outcome. Re-check this by comparing pass/fail columns rather than exact values.
