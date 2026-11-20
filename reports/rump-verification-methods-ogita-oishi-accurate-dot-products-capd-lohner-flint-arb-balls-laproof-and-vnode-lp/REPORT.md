# Guaranteed numerical error bounds: verification methods, error-free transformations, ball and interval arithmetic, rigorous ODE enclosures, and mechanized accuracy proofs

## Summary

- **Two different products are sold as "guaranteed accuracy".** *A posteriori* methods (verification methods for linear systems, interval/ball arithmetic, rigorous ODE enclosures) compute an enclosure at run time and either return it or report failure; their guarantee is conditional on correct directed rounding (or an equivalent bound) and on a trusted implementation. *A priori* mechanized proofs (LAProof, VerifiedLeapfrog, the Coq/Frama-C wave-equation proof of Boldo et al.) prove a closed-form worst-case bound once, for a fixed program and evaluation order; nothing is checked at run time. A postcondition "true error ≤ ε" needs one of the two; stopping tests and stochastic digit estimates provide neither.
- **Verified linear solve = cheap theorem + expensive products.** The certificate used by FLINT's `arb_mat_solve_preapprox` (Rump 2010, Theorem 10.2): if ‖I − RA‖∞ < 1 then A is nonsingular and ‖x − x̃‖∞ ≤ ‖R(Ax̃ − b)‖∞ / (1 − ‖I − RA‖∞). It fails (and must report failure) once cond(A) approaches 1/u. Measured on this host with a toy numpy implementation: certification costs **5.2–13.9×** an uncertified LAPACK solve (typically ≈10–14× at n = 1000), consistent with the flop-count ratio ≈10 (derived); it **failed at cond = 1e14 (n = 1000) and 1e16 (n = 100, 300)**. Published reference points: INTLAB's `verifylss` ≈ 6× MATLAB's solver (Ogita–Rump–Oishi 2005, §6); FLINT documents "about three matrix multiplications and an approximate inversion, several times that of `arb_mat_solve_lu`".
- **Error-free transformations (EFTs) give accuracy "as if in doubled precision" with a proved bound, but are fragile under compiler transformations.** Dot2 (Ogita–Rump–Oishi 2005, Prop. 5.5): |res − xᵀy| ≤ u|xᵀy| + γₙ²|xᵀ||y| (no underflow). Measured: Dot2 kept relative error ≤ 1.9e-16 up to cond ≈ 1e15 where naive summation had error 0.55; **with GCC 15.2's GNU-mode default `-ffp-contract=fast` on an FMA target, Dekker-split Dot2 lost error-freeness (2.8e-8 at cond 1e8 instead of 8.2e-17); with `-ffast-math` all Dot2 variants degraded to naive accuracy.** Dot2 with explicit `fma()` cost **1.5–1.6×** a scalar naive loop.
- **Directed rounding is trusted mutable per-thread state.** CAPD writes MXCSR directly and its documentation warns that without `-frounding-math` "compiler can optimize code so that it is not rigorous anymore"; a pthread created before `fesetround` kept round-to-nearest in our probe; Julia removed `setrounding` for `Float64` in 1.0, and its docs say the function is not thread-safe; Julia interval libraries swap in an OpenBLAS build with consistent FP control state and self-test it at load.
- **Source-level soundness gap:** `IntervalLinearAlgebra.jl`'s `epsilon_inflation` for real (non-interval) matrices computes `C = I - R * A` in plain floating point (`src/linear_systems/verify.jl:84`), whereas the ε-inflation theorem needs an enclosure of I − RA. The returned `cert == true` is therefore not a proof as written for `Float64` inputs (derived from source; not executed).
- **A priori bounds are pessimistic but cheap to evaluate; a posteriori bounds are adaptive but cost run time.** For one left-to-right binary64 dot product, LAProof's proved bound exceeded the actual error by 21×–137,000× and a directed-rounding enclosure's width by 1.3×–56×; for the float32 leapfrog program verified by VerifiedLeapfrog, the proved total-error bound 0.0308 exceeded the measured error 1.29e-3 by 23.9×.
- **Wrapping effect:** propagating a box through 1000 exact leapfrog steps with naive interval arithmetic inflated the q-width by 1.2e13× relative to the exact (affine) image; CAPD's doubleton/Lohner sets and VNODE-LP's QR-based representation exist to prevent exactly this.

## Applicability

**Subjects and their relation.** The report compares independent methods for producing guaranteed numerical error bounds; the subjects are not combined into one system.

- *A posteriori libraries:* FLINT (ball arithmetic `arb`, `arb_mat` solvers; repository `flintlib/flint`), CAPD::DynSys (rigorous ODE integration; `CAPDGroup/CAPD`), `IntervalArithmetic.jl` and `IntervalLinearAlgebra.jl` (Julia interval arithmetic and verified linear algebra; `JuliaIntervals/*`). Julia's `base/rounding.jl` (`JuliaLang/julia`) is examined only as the platform API those Julia packages build on.
- *A priori mechanized proofs:* LAProof (`VeriNum/LAProof`, Coq/Rocq accuracy theorems for dot products, matrix–vector and matrix–matrix kernels) and VerifiedLeapfrog (`VeriNum/VerifiedLeapfrog`, the end-to-end proof for a float32 leapfrog C program that accompanies Kellison–Appel 2022).
- *Literature and standards:* Ogita–Rump–Oishi 2005 (full text examined), Johansson 2017 (Arb; arXiv text examined), Boldo et al. (JAR 2013 version, arXiv text examined; CAMWA 2014 abstract), Kellison et al. 2023 (LAProof paper text examined), IEEE Std 1788-2015 (examined only through implementations that claim compliance; standard text not examined). Rump 2010 (Acta Numerica) is used only through FLINT's restatement of its Theorem 10.2. CAPD 2021, Nedialkov 2011, Tucker 1999/2002: abstracts or secondary descriptions only.
- *Execution environment for every measured number in this report:* x86-64 cloud VM, Intel Xeon @ 2.60 GHz (2 sockets × 24 cores × 2 threads; probes are single-threaded), Debian GCC 15.2.0 (`gcc (Debian 15.2.0-14)`), glibc 2.43, CPython 3.13.15, numpy 2.3.5 (Debian build) linked to the single-threaded reference BLAS/LAPACK 3.12.1 (`/usr/lib/x86_64-linux-gnu/{blas,lapack}/lib*.so.3.12.1`, Debian 3.12.1-7). Upstream numpy, reference LAPACK and GCC are pinned to their release tags in `REPORT.json`; Debian patches were not examined.

**Scope limits.** Library results are statements about the pinned revisions. Toy implementations written for this report (verified solve, Dot2, leapfrog replay, interval wrapping demo) are labelled as such and characterize *methods*, not the named libraries. No FLINT, CAPD, VNODE-LP, INTLAB or Julia code was executed (MPFR headers, CMake, Julia and MATLAB were not available on the host).

## Findings

### 1. What each method's output means

| Method (subject) | Output | Guarantee when it succeeds | Hypotheses / trusted parts | Failure signal |
|---|---|---|---|---|
| Verified linear solve, Theorem 10.2 form (FLINT `arb_mat_solve_preapprox`; toy probe) | x̃ plus a normwise radius per column | A is nonsingular; exact solution of every matrix in the input balls lies in the returned balls | ‖I − RA‖ bounded **from above** rigorously; residual enclosed rigorously; R and x̃ need not be accurate | return value 0 (FLINT) / `None` (probe) |
| Ball Gaussian elimination (`arb_mat_solve_lu`) | ball matrix | same | every pivot ball excludes 0 | return 0; radii grow ~exponentially in n |
| Preconditioned ball solve (`arb_mat_solve_precond`) | ball matrix | same; radius ≈ κ(A)·2^-p | approximate R from midpoints; RA, RB in ball arithmetic | falls back to ball LU if ‖I−RA‖ ≥ 1; returns 0 if a pivot ball contains 0 |
| ε-inflation (`IntervalLinearAlgebra.jl` `epsilon_inflation`) | interval vector, `cert::Bool` | intended: A⁻¹b ∈ result when `cert` | needs an enclosure of I − RA (see §2.4 for a gap) | `cert == false` after `iter_max = 20` |
| EFT summation/dot product (Dot2, DotK) | one float | |res − xᵀy| ≤ u|xᵀy| + γₙ²|x|ᵀ|y| | round-to-nearest, no overflow, no underflow (else + 5n·η), **no re-association or contraction by the compiler** | none — accuracy silently degrades beyond cond ≈ u⁻² |
| Ball arithmetic (`arb`) | [m ± r] | true value in ball | radius ops rounded upward from upper bounds (FLINT `error-propagation.md:21`) | radius becomes large or infinite |
| Rigorous ODE step (CAPD `HighOrderEnclosure`) | enclosure of φ([0,h], x) + remainder | solution exists and stays in enclosure | a priori enclosure verified by inclusion test; rounding mode control; compiler flags | exception: "minimal time step reached", "loop limit exceeded" |
| Mechanized a priori bound (LAProof, VerifiedLeapfrog) | theorem | for every input meeting the hypotheses, computed − exact ≤ bound | finiteness of result (LAProof), fixed evaluation order of the modelled program, correspondence of compiled code to the model (VST/CompCert in VerifiedLeapfrog) | none at run time; violated hypotheses make the theorem inapplicable |

Basis: documentation + source (FLINT, CAPD, Julia packages, LAProof, VerifiedLeapfrog) + normative statements as quoted in Ogita–Rump–Oishi 2005.

### 2. Verified linear systems

**2.1 Theorem used.** FLINT's documentation (`doc/src/arb_mat/solve.md`, "Certifying a given approximation") restates Rump 2010 Theorem 10.2: if ‖I − RA‖∞ < 1 then A is invertible and each column satisfies ‖X_j − T_j‖∞ ≤ ‖R(AT_j − B_j)‖∞ / (1 − ‖I − RA‖∞). `src/arb_mat/solve_preapprox.c:63` cites it ("Use Theorem 10.2 of Rump in Acta Numerica 2010"); the code computes 1 − ‖I − RA‖ with `mag_sub_lower` (a *lower* bound of the denominator), requires it nonzero (`_mag_err_complement`, line 65), and adds `max_i |(R(AT − B))_ij| / d` to every entry of column j (line 91). R and T may come from any untrusted source. Basis: documentation + source.

**2.2 FLINT dispatch.** `arb_mat_solve` (`src/arb_mat/solve.c:19`): `if (n <= 4 || prec > 10.0 * n) return arb_mat_solve_lu(...) else return arb_mat_solve_precond(...)`. `arb_mat_solve_precond` (`solve_precond.c:140`) uses ball LU on (RA)X = RB when `m < 0.1 * n + 1` right-hand sides, otherwise the Neumann bound X = RB ± δ/(1−δ)·‖(RB)_j‖ when δ = ‖I − RA‖∞ < 1 (`mag_cmp_2exp_si(d, 0) < 0`, line 88), and falls back to ball LU if δ ≥ 1. The documented reason (`solve.md:27–31`): in ball LU "the radii typically grow exponentially with n even for well-conditioned matrices. At 64-bit precision, the enclosures of a random 40 × 40 system are already useless and larger systems fail entirely". FLINT's documented example output (64-bit precision, random entries in [−1,1]): LU radius 3.74e-15 (n = 10), 1.39e-9 (n = 20), 3.34e-1 (n = 40), no result (n = 80); preconditioned 2.24e-18 … 2.83e-16. The linear-systems design note states the preconditioned radius is "about κ(A)·2^-p relative to the solution" and success requires precision to exceed log₂κ(A) "by a few bits, independently of n" (`doc/src/algorithms/ball-arithmetic/linear-systems.md:96–98`). Basis: source + documentation (FLINT's example output was not re-executed here).

**2.3 Cost and failure, measured (toy).** `support/verified_solve.py` implements the Theorem 10.2 certification in numpy, obtaining lower/upper bounds of R·A and A·x̃ by running the same numpy/BLAS calls under `fesetround(FE_DOWNWARD)` and `fesetround(FE_UPWARD)` (glibc via ctypes). It first runs the rounding self-test used by `IntervalLinearAlgebra.jl` (in upward mode, (AAᵀ)ᵢᵢ = 1 + 2⁻¹⁰⁶ must round to nextafter(1)); the test passed with the single-threaded reference BLAS. Matrices: A = U·diag(logspace(0, −log₁₀κ))·Vᵀ with random orthogonal U, V; b = A·1.

Basis: execution (toy implementation of the Rump/FLINT certificate on numpy 2.3.5 + reference BLAS 3.12.1; not INTLAB, not FLINT).

| n | target κ | `np.linalg.solve` [ms] | certification incl. `inv` [ms] | total/solve | bound on ‖I−RA‖∞ | certified rel. radius |
|---|---|---|---|---|---|---|
| 100 | 1e2 | 0.28 | 3.02 | 11.7 | 6.9e-13 | 5.6e-13 |
| 100 | 1e10 | 0.37 | 2.53 | 7.9 | 2.4e-5 | 1.3e-5 |
| 100 | 1e14 | 0.26 | 2.10 | 9.2 | 0.28 | 0.17 |
| 100 | 1e16 | 0.25 | 1.95 | 8.8 | 25.8 | FAIL |
| 300 | 1e6 | 10.10 | 57.80 | 6.7 | 1.6e-8 | 9.8e-9 |
| 300 | 1e14 | 7.83 | 71.02 | 10.1 | 0.86 | 3.8 |
| 1000 | 1e2 | 191.9 | 1885.5 | 10.8 | 2.5e-11 | 1.3e-11 |
| 1000 | 1e10 | 187.1 | 2231.6 | 12.9 | 6.3e-4 | 2.8e-4 |
| 1000 | 1e14 | 185.8 | 2390.9 | 13.9 | 5.42 | FAIL |

(Full 18-row output in `support/verified_solve.out`.) Derived interpretation: LU costs ≈ ⅔n³ flops, `inv` ≈ 2n³, and two directed-rounding products R·A ≈ 4n³, so certification/solve ≈ (2 + 4)/(⅔) ≈ 9 plus the solve itself ≈ 10 — matching the measured ratios because the reference BLAS is unblocked and flop-bound. The certified radii (≈ κ·1e-15) are wider than the true error because the residual A·x̃ − b was enclosed in working precision; INTLAB-style implementations compute the residual in doubled precision (e.g. with Dot2) to obtain near-optimal radii — the toy omits this (see Boundaries). Failure occurs exactly when the rigorous upper bound on ‖I − RA‖∞ reaches 1, i.e. for κ within a factor ~n of u⁻¹ ≈ 9e15; the method then *reports* failure rather than returning a wrong enclosure.

**2.4 `IntervalLinearAlgebra.jl` `epsilon_inflation`: a certificate hypothesis not established for real inputs.** At the pinned revision `src/linear_systems/verify.jl` lines 78–96 read (excerpt):

```julia
function epsilon_inflation(A::AbstractMatrix{T}, b::AbstractArray{S, N};
                           r=0.1, ϵ=1e-20, iter_max=20) where {T<:Real, S<:Real, N}
    ...
    R = inv(mid.(A))
    C = I - R * A
    xs = R * mid.(b)
    z = R * (b - (A * Interval.(xs)))
    ...
        if all(isinterior.(x, y))
            return xs + x, true
```

The docstring cites "algorithm 10.7 of [RUM10]" and says that if `cert == true` the result "is *certified* to contain the true solution". The ε-inflation argument requires z ⊇ R(b − Ax̃) and **C ⊇ I − RA**. For `A::Matrix{Float64}`, `R * A` is an ordinary `Float64` BLAS product, so `C` is a rounded approximation of I − RA, not an enclosure; the error |C − (I − RA)| ≲ γₙ₊₁|R||A| is not covered by the inflation step. `z` *is* enclosed (the product `A * Interval.(xs)` is interval-valued). For interval-valued `A` the same method applies — `Interval{T} <: Real` in `IntervalArithmetic.jl` (`src/intervals/construction.jl:334`) — and then `R * A` dispatches to the package's rigorous interval product, so the gap is specific to plain floating-point inputs. Basis: source + derived. Not executed (no Julia on the host); magnitude: because y is inflated by 10 % relative and 1e-20 absolute, the omitted term is small compared with y whenever n·u·‖|R||A|‖ ≪ 0.1, so practical misses are expected to be rare — but the flag is not a proof. The package test (`test/test_solvers/test_epsilon_inflation.jl`) checks only membership of the known solution and the `cert` flag on 4×4 examples (Float64, interval and BigFloat inputs) plus one uncertifiable interval system; membership cannot reveal a missing enclosure of I − RA.

**2.5 How Julia packages obtain directed rounding.** `IntervalArithmetic.jl` (`src/intervals/rounding.jl:1–11`) offers rounding types `:correct` ("rounding via RoundingEmulator.jl and CRlibm.jl; fallback to MPFR" — error-free-transformation emulation of directed rounding, no mode switch), `:ulp` (round-to-nearest result widened by `prevfloat`/`nextfloat`, i.e. up to one extra ulp), and `:none` ("no rounding (non-rigorous numerics)"). Matrix products of interval matrices instead switch the hardware mode: `ext/IntervalArithmeticLinearAlgebraExt.jl` calls `fesetround` around `dgemm_64_` from `OpenBLASConsistentFPCSR_jll` (lines 884–900). `IntervalLinearAlgebra.jl`'s `:fast` midpoint–radius product (Rump 1999) wraps products in `setrounding(T, RoundUp)` / `setrounding(T, RoundDown)` (`src/multiplication.jl:78, 91`), and its `__init__` swaps in the ConsistentFPCSR OpenBLAS and runs `rounding_test` on all BLAS threads, reducing to one thread on failure (`src/IntervalLinearAlgebra.jl:56–80`). Julia's own docs (`base/rounding.jl:190–205` at the pinned revision) say `setrounding(T, mode)` "is currently only supported for `T == BigFloat`" and is "not thread-safe"; Julia 0.7 deprecated `setrounding` for `Float32`/`Float64` and 1.0 removed it (checked in `base/rounding.jl` at tags v0.6.0, v1.0.0, v1.6.0, v1.9.0, v1.10.0). The `Float64` method is supplied by the shim package `SetRounding.jl`, a dependency of `IntervalArithmetic.jl` 0.20.x but not of 1.0.14 (pinned `Project.toml`). Derived risk (not executed): under `IntervalArithmetic.jl` 1.x without `SetRounding.jl` loaded, `IntervalLinearAlgebra.jl`'s `setrounding(Float64, RoundUp)` calls have no method; whether a real environment resolves this through another dependency is **unknown**. Basis: source + documentation + derived.

### 3. Error-free transformations and Dot2

**3.1 Statements (Ogita–Rump–Oishi 2005, full text).** TwoSum and TwoProduct transform a+b and a·b into x + y exactly (Theorem 3.4 "also in the presence of underflow" for TwoSum; TwoProduct needs no underflow). Dot2 (Algorithm 5.3): `[p,s]=TwoProduct(x1,y1); for i=2:n [h,r]=TwoProduct(xi,yi); [p,q]=TwoSum(p,h); s=fl(s+(q+r)); end; res=fl(p+s)`. Proposition 5.5: with n·u < 1 and no underflow, |res − xᵀy| ≤ u|xᵀy| + γₙ²|xᵀ||y|; with underflow add 5n·η. Cost 25n − 7 flops, or 6n − 3 with ADD3 and FMA. The authors' Figure 6.1 shows maximal accuracy up to cond ≈ u⁻¹ ≈ 1e16, degrading to no correct digits by u⁻² ≈ 1e32, with the bound "pessimistic by 2 or 3 orders of magnitude" beyond u⁻¹. Measured timing in the paper (Table 6.6, n = 100…3000): Dot2 residual A·x − b took 3.8× (Pentium 3, ATLAS) and 4.8× (Pentium 4, MKL) the time of BLAS `DGEMV` (theoretical 12.5); Dot2 iterative refinement added at most 25 % to a linear solve. Basis: documentation (peer-reviewed paper).

**3.2 Accuracy, measured (toy).** `support/eft_dot.py` re-implements Dot2 with `math.fma` and the paper's GenDot generator (Algorithm 6.1); errors and condition numbers (cond = 2|x|ᵀ|y|/|xᵀy|) are computed exactly with `fractions.Fraction`. n = 100, 20 samples per decade, seed 1.

| target cond | median actual cond | max rel. err naive | max rel. err Dot2 | max err/bound naive | max err/bound Dot2 |
|---|---|---|---|---|---|
| 1e2 | 2e3 | 3.4e-12 | 8.8e-17 | 9.8e-3 | 0.79 |
| 1e10 | 1.3e11 | 3.3e-4 | 7.9e-17 | 2.2e-2 | 0.65 |
| 1e14 | 1e15 | 0.55 | 1.9e-16 | 2.2e-2 | 1.9e-2 |
| 1e18 | 1e19 | 3.8e3 | 3.5e-12 | 2.9e-2 | 1.2e-3 |
| 1e26 | 1.3e27 | 2.7e12 | 8.0e-4 | 1.8e-2 | 6.9e-4 |
| 1e30 | 1.3e31 | 4.9e15 | 3.1 | 1.3e-2 | 7.2e-4 |

No bound violations in 200 samples. Basis: execution (toy re-implementation; Python binary64 with correctly rounded FMA). Consistent with the paper: the a priori bound for naive summation (γₙ|x|ᵀ|y|) overestimates by ≈ 35–100× here; Dot2's bound by ≈ 1000× beyond cond 1e16.

**3.3 Compiler flags break EFTs, measured on the real compiler.** `support/dotprobe.c` (naive, Dot2 with `fma()`, Dot2 with Dekker split) built three ways and checked exactly by `support/check_dot.py` (n = 100, 10 GenDot samples per decade):

| cond | strict (`-std=c99 -ffp-contract=off`) naive / Dot2-fma / Dot2-Dekker | GNU default (`-std=gnu99`, contraction "fast") | `-ffast-math` |
|---|---|---|---|
| 1e8 | 1.7e-7 / 8.2e-17 / 8.2e-17 | 1.7e-7 / 8.2e-17 / **2.8e-8** | 1.8e-7 / **1.6e-7** / **1.7e-7** |
| 1e16 | 25 / 6.4e-15 / 6.4e-15 | 25 / 6.4e-15 / **4.4** | 22 / **16** / **15** |
| 1e24 | 2.7e9 / 8.2e-7 / 8.2e-7 | 2.7e9 / 8.2e-7 / **3.2e8** | 1.7e9 / **1.4e9** / **2.0e9** |

All builds use `-O2 -march=x86-64-v3` (FMA available). A fourth build in ISO mode without an explicit flag (`-std=c99`) emitted no FMA instruction in `dot2_dekker` and reproduced the strict column exactly (`support/check_dot.out`), so the hazard is the GNU-dialect default; note that `gcc -Q --help=optimizers` prints `fast` for both dialects and therefore does not reveal the effective ISO-mode setting. Disassembly of the GNU-mode `dot2_dekker` contains a `vfmadd231sd` that, on our reading, computes p + x·y in one rounding — TwoProduct's product fused into TwoSum's addition after inlining — so TwoSum receives inputs inconsistent with the separately rounded product it later subtracts. The same Dekker TwoProduct compiled *in isolation* (`support/eft_contract.c`; FMA instructions present in the binary) remained error-free on 2,000,000 random pairs, checked with `__float128`: testing an EFT outside its use context does not validate it. Basis: execution (real GCC 15.2.0 + exact checking).

**3.4 Cost, measured.** `dotprobe time` (best of 5, single thread):

| build | n | naive ns/elem | Dot2-fma ns/elem (×naive) | Dot2-Dekker ns/elem (×naive) |
|---|---|---|---|---|
| strict | 1,000 | 1.144 | 1.833 (1.60) | 3.813 (3.33) |
| strict | 4,000,000 | 1.398 | 2.146 (1.53) | 3.986 (2.85) |
| GNU default | 1,000 | 1.126 | 1.844 (1.64) | 2.915 (2.59) |
| `-ffast-math` | 1,000 | 0.265 | 0.302 (1.14) | 0.269 (1.01) |

The strict naive loop is latency-bound (one dependent add per element, ≈ 3 cycles at the nominal 2.6 GHz, derived; the actual clock during the run was not recorded). Against the vectorized `-ffast-math` naive loop, correct Dot2 costs 1.833/0.265 ≈ **6.9×** at n = 1000 and 2.146/1.099 ≈ 1.95× at n = 4e6 (memory-bound) — derived from the table. The `-ffast-math` "Dot2" is fast only because its error terms were optimized away (§3.3).

### 4. Directed rounding, compilers and threads as trusted components

- **CAPD** sets rounding by loading MXCSR directly: `asm volatile ("ldmxcsr %0" : : "m" (ROUND_UP_CW))` with `AMD64_DEFAULT_SSE_FLAGS 0x1fbf` (all exceptions masked, sticky flags pre-set; comment: loading MXCSR "is extermly slow if it clears any xE flag" on Pentium 4) (`capdAlg/src/capd/rounding/DoubleRounding.cpp:84–122`). The top-level `CMakeLists.txt:15` compiles with `-O2 -frounding-math`, and `capdMake/docs/src/user_programs.dox:40` warns: "without option -frounding-math compiler can optimize code so that it is not rigorous anymore." Basis: source + documentation.
- **Threads.** `support/round_threads.c`: after `fesetround(FE_UPWARD)` the main thread computes 1 + 2⁻⁶⁰ = `0x1.0000000000001p+0`, a thread created afterwards also does (POSIX: the FP environment is inherited at creation), but a pool thread created *before* the call returns `0x1p+0`. Threaded BLAS implementations dispatch to such pools; this is why the Julia packages above require `OpenBLASConsistentFPCSR_jll` and a load-time self-test. Basis: execution (glibc 2.43, Linux, x86-64).
- **numpy on this host** honoured `fesetround` in its matrix products only because the reference BLAS is single-threaded (self-test in §2.3); this is a property of the host's BLAS selection, not of numpy.

### 5. Ball arithmetic (FLINT `arb`)

FLINT's design note (`doc/src/algorithms/ball-arithmetic/error-propagation.md`) defines a ball function as "evaluates its result at the midpoint ... and adds to the radius a bound for the propagated error", e.g. |(x + a)(y + b) − xy| ≤ |x||b| + |y||a| + |a||b| for multiplication, with all bounds "evaluated with `mag_t` arithmetic, rounding upward, from upper bounds for the quantities that occur in numerators and lower bounds for those in denominators" (line 21). Radii are low-precision `mag_t` values, so the radius bookkeeping is cheap: Johansson 2017 (Table 2, Intel i5-4300U, MPFR 3.1.5, MPFI 1.5.1) reports time relative to an MPFR operation on the midpoints at 64-bit precision: Arb add 1.08, mul 1.03, div 1.72, sqrt 1.78; MPFI add 2.58, mul 2.06, div 2.96, sqrt 2.02; at 32768 bits Arb mul 1.02, MPFI 2.02. Basis: documentation (FLINT docs) + peer-reviewed measurement (not re-measured).

### 6. IEEE 1788-2015 concepts as exposed by a claimed-compliant implementation

`IntervalArithmetic.jl` states compliance with IEEE 1788-2015 (README). Its `Flavor` docstring (`src/intervals/flavor.jl`) describes the default `:set_based` flavor as "described and required in Part 2 of the IEEE Standard 1788-2015": intervals contain only reals, `[0,0]/[0,0] = ∅`, `x/[0,0] = ∅`, `x × [0,0] = [0,0]`; it notes "Currently only the flavor `:set_based` is supported". Decorations (`construction.jl:260–285`): `com` (non-empty, continuous, bounded), `dac`, `def`, `trv`, `ill` (NaI); `com`, `dac`, `def` are "safe". The implementation adds a non-standard `isguaranteed` flag (the "NG" flag) recording whether a value passed through non-interval code; linear-algebra routines propagate it (`_ensure_ng_flag!`). Its constructor docstring warns that "floating point literals are rounded to the nearest when parsed (e.g. `0.1`)" — an enclosure of a decimal datum must be built from the string. Basis: documentation + source of an implementation; **the standard's own text was not examined**, so these are not normative claims about IEEE 1788.

### 7. Rigorous ODE enclosures

- **CAPD one-step enclosure** (`capdDynSys/include/capd/dynsys/HighOrderEnclosure.h:336–414`, `computeEnclosureAndRemainder`): (1) enclose the range of the Taylor polynomial over [0, h]; (2) *predict* an enclosure from the previous step's remainder; (3) compute remainder coefficients on the predicted set and **check inclusion** in the prediction; (4) if inclusion fails and step changes are allowed, shrink h by factor^(1/(order+1)) (error "minimal time step reached. Cannot integrate." if below the minimum, line 391); otherwise enlarge the enclosure up to `maxAttempts = 30` times (line 399) and throw "cannot find enclosure guaranteeing bounds, loop limit exceeded" (line 413). Set representations control wrapping: `C0DoubletonSet` keeps x + C·r₀ + B·r with B chosen by a `QRPolicy` (`C0DoubletonSet.h:27`), i.e. Lohner-style coordinate changes. Basis: source.
- **Wrapping effect, measured (toy).** `support/leapfrog_probe.py` Part B propagates the box [1 ± 1e-6] × [0 ± 1e-6] through the exact linear leapfrog map (rational arithmetic, so no rounding at all): naive interval width of q after 100/250/500/1000 steps is 20× / 1.9e3× / 3.5e6× / **1.2e13×** the width of the exact affine image (which stays ≈ 2.1e-6). Basis: execution (toy model of the phenomenon, not CAPD/VNODE-LP).
- **VNODE-LP** (site text): "this solver tries to prove that a unique solution to a problem exists and then computes bounds that contain this solution", "developed entirely using Literate Programming ... the theory, documentation, and source code are produced from the same CWEB files" so that correctness "can be examined easier". Secondary descriptions attribute to it an interval Hermite–Obreschkoff method with Lohner-type QR wrapping control and a separate a priori enclosure phase; these were **not verified against VNODE-LP's CWEB source**. Basis: documentation (primary site) + secondary.
- **Tucker 1999/2002.** The existence proof of the Lorenz attractor combined normal-form analysis near the origin with rigorous interval-based integration elsewhere to establish properties of a return map (secondary description; the papers' text and run times were not examined).

### 8. Mechanized a priori accuracy proofs

- **LAProof** (`accuracy_proofs/dot_acc.v`): `dotprod_forward_error`: |fl(v₁·v₂) − v₁·v₂| ≤ g(n)·(|v₁|·|v₂|) + g₁(n, n−1), with g(n) = (1+u)ⁿ − 1 and g₁(n₁, n₂) = n₁·η·(1 + g(n₂)) (`common.v:436, 494`), u = `default_rel` = ½·2^(1−p), η = `default_abs` = ½·2^(3−emax−p) (`common.v:211–215`); hypotheses only `size v1 = size v2` and `Binary.is_finite (dotprodF v1 v2) = true`. `dotprodF` is the left-to-right fold (`dotprod_model.v:106–111`); the paper states the forward bound "holds ... for any permutation" of the summands. `gemv_acc.v:209` (`mat_vec_mul_forward_error`) and `gemm_acc.v:349` (`GEMM_error`) give analogous normwise and mixed bounds, the latter decomposing fl(s₁AB + s₂Y) into backward terms bounded by g(n) and u and absolute terms bounded by g₁(n,n). The paper: bounds "account for underflow, proved subject to no assumptions except a low-level formal model of IEEE-754 arithmetic", low-order terms concrete (not O(u²)); a VST proof connects the model to a C CSR matrix–vector routine that uses `fma`. Basis: source + documentation.
- **VerifiedLeapfrog** (Kellison–Appel 2022 artifact): `total_error.v:21` proves, for n ≤ 1000, ‖(p(tₙ), q(tₙ)) − computed‖ ≤ (h³ + local_round_off)/(σ_b − 1)·(σ_bⁿ − 1); corollary `yes_accurate_harmonic_oscillator` instantiates it to **0.0308** for N = 1000, h = 1/32, q₀ = 1, p₀ = 0 in binary32 (`float_model.v:24, 82–85`); `main.v` lifts this to a VST function specification of `integrate` in `lfharm.c` (README: tested with Rocq 9.0.1, VST 2.16, CompCert 3.17, VCFloat 2.4.1). Basis: source.
- **Boldo et al.** (wave-equation C program, JAR 2013 version): Frama-C/Jessie/Why obligations discharged by Alt-Ergo, CVC3, Z3, Gappa and Coq; Coq sizes and check times on a 3-GHz dual core: convergence part 991 spec lines / 5,275 lines / 42 s; round-off + runtime errors 7,737 spec lines (7,321 auto-generated) / 13,175 lines / **32 min**; remaining axioms include a fact about Jacobi polynomials and existence/regularity of the PDE solution; the effective total error was about 10⁶ times smaller than the proved upper bound in their test. Basis: documentation (paper).

### 9. A priori vs. a posteriori on the same computation

`support/apriori_vs_aposteriori.py` (binary64 left-to-right dot product; LAProof's formula evaluated exactly; interval = same loop rounded down/up; running bound = Higham-style, made rigorous):

| data | n | actual | LAProof bound | interval width | running bound | bound/actual | width/actual |
|---|---|---|---|---|---|---|---|
| positive | 100 | 4.8e-15 | 2.7e-13 | 1.9e-13 | 1.3e-13 | 55 | 40 |
| positive | 10,000 | 1.6e-11 | 2.8e-9 | 2.0e-9 | 1.4e-9 | 175 | 129 |
| mixed sign | 1,000 | 2.0e-16 | 2.8e-11 | 1.2e-12 | 8.3e-13 | 137,446 | 5,850 |
| mixed sign | 10,000 | 5.0e-14 | 2.8e-9 | 4.9e-11 | 3.5e-11 | 55,725 | 987 |

Leapfrog (`support/leapfrog_probe.py` Part A, re-implementation of `lfharm.c`'s expression order in numpy float32): total error **1.292e-3**, of which discretization 1.291e-3 and round-off 4.3e-7; proved bound 0.0308 = **23.9×** actual. Derived reading: a priori bounds pay ≈ n·u worst-case growth regardless of data; directed-rounding enclosures adapt to cancellation (mixed sign) but not to statistical error cancellation, and cost 2× the computation plus rounding-mode switches; neither approaches the √n-like actual error. Basis: execution (toy evaluation of the proved formulas on synthetic data; LAProof proves, it does not compute).

### 10. Cost and footprint at six levels

| Level | Quantity | Value | Source |
|---|---|---|---|
| L1 authoring | Coq lines, wave-equation proof | 5,275 + 13,175 lines (991 + 7,737 spec lines) | Boldo et al. (paper) |
| L1 | proof sizes and person-effort for LAProof / VerifiedLeapfrog | not measured | — |
| L2 toolchain build | FLINT, CAPD, LAProof, VerifiedLeapfrog builds | not measured (not built) | — |
| L3 proof/elaboration | Coq check, wave-equation round-off part | 32 min (3-GHz dual core) | Boldo et al. |
| L4 run time | verified solve / uncertified solve | 5.2–13.9× (toy, numpy + ref BLAS) | measured |
| L4 | INTLAB `verifylss` / MATLAB solve | ≈ 6× | Ogita–Rump–Oishi 2005 |
| L4 | Dot2 / naive (scalar) | 1.47–1.64×; Dekker 2.26–3.33× | measured |
| L4 | Dot2 residual / DGEMV | 3.8× and 4.8× | Ogita–Rump–Oishi 2005, Table 6.6 |
| L4 | Arb mul / MPFR mul at 64 bits | 1.03× (MPFI 2.06×) | Johansson 2017, Table 2 |
| L4 | FLINT precond. solve / ball LU | "several times" | FLINT docs |
| L5 certificate check | a posteriori: none separate (the run *is* the check); a priori: Coq kernel re-check | not measured | — |
| L6 memory | verified solve extra storage | R (n²) + two bound matrices (2n²) beyond LU (derived from the algorithm in `verified_solve.py`) | derived |
| L6 | `.vo` sizes, peak RSS of provers, binary sizes | not measured | — |

### 11. Comprehensibility and conceptual simplicity

- **C1.** The Theorem 10.2 certificate has one inequality and two computed quantities; its failure is a single boolean. A user must still understand that "success" covers every matrix in the input balls and that a failed certificate says nothing about the data. Dot2's guarantee is invisible at the call site: its accuracy degrades silently beyond cond ≈ u⁻², and correctness depends on build flags no reviewer of the source sees. A priori theorems (LAProof) are auditable statements but their hypothesis "the computed result is finite" and the modelled evaluation order must be matched to the deployed binary by a separate argument (VST/CompCert in VerifiedLeapfrog). CAPD's failure messages name the mechanism ("minimal time step reached") rather than a mathematical quantity.
- **C2.** One invariant — "the exact value lies in the representation" — is enforced by at least four mechanisms in the subjects: hardware rounding-mode switching (CAPD, Julia BLAS paths), EFT emulation of directed rounding (`:correct` via RoundingEmulator), one-ulp widening (`:ulp`), and upward-rounded radius arithmetic on a separate low-precision type (Arb `mag_t`). The last two are mode-free and thread-safe by construction; the first imposes global, per-thread, compiler-visible state (`-frounding-math`, pool threads, `setrounding` removal). A minimal portable abstraction is "an upper-bound oracle for each primitive" (as `mag_t` provides) rather than "a rounding mode".

### 12. Validation of the implementations (V1–V4)

- **V1 (specification adequacy).** LAProof's specifications are stated against Coq reals and Flocq binary floats; VerifiedLeapfrog's statement quantifies over *all* exact solutions satisfying the ODE system, so it is non-vacuous only if such solutions exist (they do for the linear oscillator; not checked in Coq here). The `IntervalLinearAlgebra.jl` test for `epsilon_inflation` checks membership of the known solution only, which cannot detect a missing enclosure of I − RA (§2.4).
- **V2 (compiler/lowering).** §3.3 shows the decisive role of `-ffp-contract`/`-ffast-math`; CAPD encodes `-frounding-math` in its build; VerifiedLeapfrog relies on CompCert semantics (no contraction). No differential or metamorphic fuzzing of these libraries' arithmetic was found or run (not examined).
- **V3 (concurrency/hardware).** Rounding mode is per-thread (§4); the Julia packages' load-time BLAS self-test is the only run-time validation of that assumption among the subjects examined.
- **V4 (plant/field).** Not applicable to these libraries; Boldo et al. and FLINT document comparison of bounds against observed errors (§8, §2.2).

## Boundaries

- **Not examined:** IEEE Std 1788-2015 and 1788.1-2017 normative text (DOIs verified only); INTLAB source and `verifylss` internals; Rump 2010 full text (Theorem 10.2 taken from FLINT's restatement); VNODE-LP's CWEB source and its exact method (Hermite–Obreschkoff/QR attribution is secondary; the claim that VNODE-LP uses *Taylor-model* integration is **not supported** by any source found); CAPD 2021 paper text, CAPD run times, and Tucker's computation times; Kellison–Appel 2022 paper text (the repository was examined instead); LAProof's FMA dot-product file (`fma_dot_acc.v`) and the C proofs in `C/`.
- **Not measured:** any FLINT, CAPD, VNODE-LP or Julia run; build times and footprints (L2, L6) of all subjects; Coq check times for LAProof and VerifiedLeapfrog; checker throughput (L5).
- **Unknown:** whether `IntervalLinearAlgebra.jl` with `IntervalArithmetic.jl` 1.x fails at load or obtains `setrounding(Float64, ·)` from another package; how often the §2.4 gap yields a false `cert == true` in practice (no counterexample constructed).
- **Toy-model caveats:** the verified-solve cost ratios are for the author's numpy implementation on an unblocked reference BLAS; with a tuned multithreaded BLAS the ratio would differ and rounding-mode control would additionally require a ConsistentFPCSR-style build. The probe encloses the residual in working precision, so its radii are wider than INTLAB/FLINT-quality enclosures. Dot2 timings are for scalar C loops on one host.
- **Stronger conclusions not established:** that FLINT's or CAPD's implementations are free of defects (only their algorithms and safety conditions were read); that `-ffp-contract=fast` breaks *every* EFT (it broke the Dekker variant in context, not FMA-based TwoProduct and not Dekker in isolation); that a priori bounds are always looser than a posteriori ones (true in every case measured here, but by data-dependent factors from 1.3× to 56×).

## Evidence

Observation date for all evidence: 2026-11-20 (UTC). All GitHub revisions resolved through the GitHub API on that date.

**Repositories (full revisions in `REPORT.json`):**

- `flintlib/flint` @ `66efe60ea72b922d2537fa1344c1c997bb7b5bf3`: `src/arb_mat/solve.c:19`; `src/arb_mat/solve_preapprox.c:63–109`; `src/arb_mat/solve_precond.c:32, 72, 88, 96, 140`; `doc/src/arb_mat/solve.md` (dispatch rationale lines 27–31, cost line 53, preapprox theorem, documented example outputs); `doc/src/algorithms/ball-arithmetic/linear-systems.md:96–98`; `doc/src/algorithms/ball-arithmetic/error-propagation.md:21`.
- `CAPDGroup/CAPD` @ `37057e5899bccaa6cd5701057b7e6ea5e232ef8b`: `capdDynSys/include/capd/dynsys/HighOrderEnclosure.h:336–414`; `capdDynSys/include/capd/dynset/C0DoubletonSet.h:27`; `capdAlg/src/capd/rounding/DoubleRounding.cpp:82–123`; `CMakeLists.txt:15`; `capdMake/docs/src/user_programs.dox:37–40`.
- `JuliaIntervals/IntervalLinearAlgebra.jl` @ `3940007c1ceb989099e626412bd8d5534da49c1f` (version 0.2.0): `src/linear_systems/verify.jl:78–96`; `src/multiplication.jl:64–98, 78, 91`; `src/IntervalLinearAlgebra.jl:44–80`; `src/numerical_test/multithread.jl` (`rounding_test`); `test/test_solvers/test_epsilon_inflation.jl`; `Project.toml` (compat `IntervalArithmetic = "0.20.5, 1.0"`).
- `JuliaIntervals/IntervalArithmetic.jl` @ `63cf591feb1bb775aea9ce10aa032c0ff19dc907` (version 1.0.14): `README.md`; `src/intervals/rounding.jl:1–16, 86–102`; `src/intervals/flavor.jl`; `src/intervals/construction.jl:186–195, 260–285, 315–340`; `ext/IntervalArithmeticLinearAlgebraExt.jl:863–928`; `Project.toml`. Older release examined for the dependency comparison: tag `v0.20.9` `Project.toml` (lists `SetRounding`).
- `JuliaLang/julia` @ `2aa7c9fd5bf14ef95960c44bf2fcf5370f7123a1`: `base/rounding.jl:188–256`; history checked at tags v0.6.0 (`setrounding(::Type{T}, r::RoundingMode) where {T<:Union{Float32,Float64}}`, line 145), v0.7.0 `base/deprecated.jl:1698–1700` (deprecation message), v1.0.0, v1.6.0, v1.9.0, v1.10.0 (no such method).
- `VeriNum/LAProof` @ `86a9a74a55bd1ac15f1dab41e430e7498543d016`: `README.md`; `accuracy_proofs/dot_acc.v:86–200`; `common.v:30–48, 205–215, 434–500`; `dotprod_model.v:106–111`; `gemv_acc.v:202–215`; `gemm_acc.v:338–375`.
- `VeriNum/VerifiedLeapfrog` @ `720f093e1aad26c21f1425e91dd52a8c3435983b`: `README.md`; `leapfrog_project/total_error.v:21–31, 72–92`; `main.v:9–58`; `float_model.v:24–85`; `lfharm.c`.
- `numpy/numpy` tag v2.3.5 @ `c3d60fc8393f3ca3306b8ce8b6453d43737e3d90`, `Reference-LAPACK/lapack` tag v3.12.1 @ `6ec7f2bc4ecf4c4a93496aa2fa519575bc0e39ca`, `gcc-mirror/gcc` tag releases/gcc-15.2.0 @ `5115c7e447fc07457443df874bf57840e8316d5f`: upstream identities of the host's Debian builds used for execution.

**Literature (DOIs verified through the doi.org handle API, `responseCode` 1, and OpenAlex metadata for title, authors, venue, year; Crossref's API was not reachable from the fetch tool):** Ogita, Rump, Oishi, "Accurate Sum and Dot Product", SIAM J. Sci. Comput. 26(6):1955–1988, 2005, DOI 10.1137/030601818 (full text read from the authors' copy). Rump, "Verification methods: Rigorous results using floating-point arithmetic", Acta Numerica 19:287–449, 2010, DOI 10.1017/S096249291000005X. Rump, "INTLAB — INTerval LABoratory", 1999, DOI 10.1007/978-94-017-1247-7_7. Rump, "Fast and Parallel Interval Arithmetic", BIT 39(3):534–554, 1999, DOI 10.1023/A:1022374804152. Hansen, Smith, "Interval Arithmetic in Matrix Computations, Part II", SIAM J. Numer. Anal. 4(1), 1967, DOI 10.1137/0704001. Dekker, "A floating-point technique for extending the available precision", Numer. Math. 18(3), 1971, DOI 10.1007/BF01397083. Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., SIAM 2002, DOI 10.1137/1.9780898718027. Rump, Ogita, Oishi, "Accurate Floating-Point Summation Part I: Faithful Rounding", SIAM J. Sci. Comput. 31(1), 2008, DOI 10.1137/050645671. IEEE Std 1788-2015, DOI 10.1109/IEEESTD.2015.7140721; IEEE Std 1788.1-2017, DOI 10.1109/IEEESTD.2018.8277144. Johansson, "Arb: Efficient Arbitrary-Precision Midpoint-Radius Interval Arithmetic", IEEE Trans. Comput. 66(8):1281–1292, 2017, DOI 10.1109/TC.2017.2690633 (arXiv:1611.02831 text read). Kapela, Mrozek, Wilczak, Zgliczyński, "CAPD::DynSys", Commun. Nonlinear Sci. Numer. Simul. 101:105578, 2021, DOI 10.1016/j.cnsns.2020.105578 (abstract only). Nedialkov, "Implementing a Rigorous ODE Solver Through Literate Programming", 2011, DOI 10.1007/978-3-642-15956-5_1 (metadata only); Nedialkov, Jackson, Corliss, "Validated solutions of initial value problems for ordinary differential equations", Appl. Math. Comput. 105(1), 1999, DOI 10.1016/S0096-3003(98)10083-8 (metadata only). Tucker, "The Lorenz attractor exists", C. R. Acad. Sci. Paris Sér. I 328(12):1197–1202, 1999, DOI 10.1016/S0764-4442(99)80439-X; Tucker, "A Rigorous ODE Solver and Smale's 14th Problem", Found. Comput. Math. 2(1):53–117, 2002, DOI 10.1007/s002080010018 (metadata only). Boldo, Clément, Filliâtre, Mayero, Melquiond, Weis, "Trusting computations: A mechanized proof from partial differential equations to actual program", Comput. Math. Appl. 68(3):325–352, 2014, DOI 10.1016/j.camwa.2014.06.004 (abstract), and the same authors' 2013 J. Autom. Reasoning 50(4):423–456 paper on the 1D acoustic wave equation C program, DOI 10.1007/s10817-012-9255-4 (arXiv:1112.1795 text read; proof sizes and times in its §4). Kellison, Appel, "Verified Numerical Methods for Ordinary Differential Equations", NSV 2022, LNCS, DOI 10.1007/978-3-031-21222-2_9 (metadata; content via the VerifiedLeapfrog repository). Kellison, Appel, Tekriwal, Bindel, "LAProof", ARITH 2023, pp. 36–43, DOI 10.1109/ARITH58626.2023.00021 (authors' copy read).

**Execution (host described under Applicability; outputs preserved in `support/*.out`):**

```text
python3 support/eft_dot.py 1 100 20                      > support/eft_dot.out
gcc -O2 -std=c99   -march=x86-64-v3 -ffp-contract=off support/dotprobe.c -lm -o dot_strict
gcc -O2 -std=gnu99 -march=x86-64-v3                    support/dotprobe.c -lm -o dot_gnu
gcc -O2 -std=c99   -march=x86-64-v3 -ffast-math        support/dotprobe.c -lm -o dot_fastmath
gcc -O2 -std=c99   -march=x86-64-v3                    support/dotprobe.c -lm -o dot_iso
python3 support/check_dot.py ./dot_strict ./dot_gnu ./dot_fastmath ./dot_iso   > support/check_dot.out
./dot_strict time 1000 20000; ./dot_strict time 4000000 10 (same for the other two) > support/dotprobe_time.out
gcc -O2 -march=x86-64-v3 support/eft_contract.c -o c_default && ./c_default      (also -ffp-contract=off, -std=c17)
gcc -O2 -frounding-math -pthread support/round_threads.c -lm -o rt && ./rt        > support/round_threads.out
python3 support/verified_solve.py 100 300 1000             > support/verified_solve.out
python3 support/apriori_vs_aposteriori.py                  > support/apriori_vs_aposteriori.out
python3 support/leapfrog_probe.py                          > support/leapfrog_probe.out
```

## Revalidation

- **Certificate and dispatch (FLINT):** diff `src/arb_mat/solve.c`, `solve_precond.c`, `solve_preapprox.c` against the pinned revision; the thresholds `n <= 4 || prec > 10.0 * n` and `m < 0.1 * n + 1` and the `mag_sub_lower` denominator determine behaviour. Re-running the two documented examples in `doc/src/arb_mat/solve.md` checks the radius claims.
- **ε-inflation gap:** inspect `src/linear_systems/verify.jl`; the finding is resolved if `C` is computed as an interval enclosure (e.g. `I - R * Interval.(A)`) for real inputs. A Julia session can probe it by comparing `C` with an interval enclosure of `I - R*A` on an ill-conditioned 50×50 matrix.
- **Julia rounding API:** `grep -n "setrounding" base/rounding.jl` in the Julia version in use, and check whether `SetRounding` appears in the resolved manifest of a project using `IntervalLinearAlgebra.jl`.
- **Compiler hazard:** rebuild `support/dotprobe.c` with the compiler and flags of interest and run `support/check_dot.py`; any Dot2 column above ~1e-15 at cond 1e8 indicates broken EFTs. `gcc -Q --help=optimizers | grep contract` shows the contraction default.
- **Rounding mode across threads:** run `support/round_threads.c`; for a BLAS, run the rounding self-test in `support/verified_solve.py` (`rounding_selftest`) with the BLAS's thread count set as deployed.
- **Cost ratios:** rerun `support/verified_solve.py` and `support/dotprobe.c time` on the target host; ratios depend on BLAS blocking and threading.
- **A priori bounds:** re-evaluate the bound formulas only if `dot_acc.v`'s `dotprod_forward_error` or VerifiedLeapfrog's `yes_accurate_harmonic_oscillator` statement changes (diff those lemmas); `support/apriori_vs_aposteriori.py` and `support/leapfrog_probe.py` then recompute the comparisons in about 3 s.
