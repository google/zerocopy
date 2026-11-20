# Correctness of statistical implementations used as acceptance gates: NIST StRD certified values, published package and spreadsheet accuracy studies, embedded reference tests, CAMIS cross-language divergences, and differential testing of probabilistic programming systems

## Summary

- **A certified value tests the whole pipeline, including decimal-to-binary input conversion.** The NIST Statistical Reference Datasets (StRD) give decimal data and certified results (univariate statistics, one-way ANOVA, linear and nonlinear least squares; graded lower/average/higher difficulty). Recomputing the certified values in exact rational arithmetic reproduced every univariate, ANOVA and linear-regression value examined to ≥ 14.3 significant digits. But the *exact* statistic of the binary64-parsed data already disagrees with the certificate: the best attainable log relative error (LRE) is **8.3** for NumAcc4's standard deviation, **4.2–4.4** for the ANOVA F of SmLs07–09, and **7.7** for the Filip regression coefficients. Any LRE report that does not separate this "representation limit" from algorithmic loss overstates or misattributes failures (derived + execution).
- **Measured on real code (numpy 2.3.5 + reference LAPACK 3.12.1; CPython 3.13.15):** `numpy.std` and `statistics.stdev` reached the representation limit on all nine univariate datasets; `numpy.linalg.lstsq` with its default `rcond = eps·max(M, N)` **silently truncated Filip to rank 10 of 11 (LRE 0.0)**, reporting the reduced rank only in its returned tuple; with `rcond=0` it reached LRE 5.6. Textbook one-pass formulas (toy re-implementations) failed exactly where the classic studies located failures: one-pass standard deviation LRE 0.0 on NumAcc4; one-pass ANOVA F LRE 0.0–0.3 on SmLs05–09.
- **Published studies (what could be verified):** McCullough's 1998 methodology tests estimation, random number generation and statistical distributions; his 1999 application found weaknesses in all RNGs of SAS, SPSS and S-Plus, the S-Plus correlation procedure, and the one-way ANOVA and nonlinear least squares of SAS and SPSS. Excel was assessed for the 97, 2000/XP, 2003, 2007 and 2010 releases; Almiron et al. (2010) found "no safe choice" among five spreadsheets, all failing nonlinear regression; Mélard (2014) found Excel 2010 "partially improved ... essentially the statistical functions and the random number generator". Per-procedure LRE tables of these papers were **not examined** (paywalled).
- **Open-source test suites embed only part of StRD, at loose or broken tolerances.** SciPy embeds the 11 ANOVA datasets (rtol 1e-7, relaxed to **1e-4 for SmLs07–09** — consistent with the 4.2–4.4-digit representation limit) and only Norris for regression. statsmodels checks Longley against NIST with an absolute 4-decimal tolerance on parameters, and its standard-error check passes `DECIMAL_4 = 4` **as `rtol`** (`assert_allclose(self.res1.bse, self.res2.bse, self.decimal_standarderrors)`), accepting up to 400 % relative error.
- **CAMIS (47 R/SAS/Python comparison documents):** 17 report agreement; 30 report at least one divergence. The dominant causes are documented defaults and legitimately different methods (continuity corrections, quantile definitions, exact-test p-value definitions, variance estimators, optimizer convergence), not defects; only 3 documents attribute a difference to a defect. `riskmetric`'s 19 metrics assess process and popularity signals; none checks numerical results against reference data. The FDA's 2015 statement requires software identification and "reliable" software, not a specific package.
- **Probabilistic programming systems:** ProbFuzz (Dutta et al. 2018) found 67 previously unknown bugs (51 fixes accepted) in Edward, Pyro and Stan using generated programs and output oracles; Storm (2019) reduced 47 failing programs by 49–58 % code, 67–96 % data and 96–99 % iterations. In the public ProbFuzz artifact the accuracy oracle `metrics/lr_smape.py` compares a float with the **string** threshold (`smape_thres=sys.argv[1]`), so it cannot work as written (Python 3 raises; under the Python 2.7 the installer selects, the outcome depends on mixed-type ordering — not executed).
- **Formalization reach:** a verified central limit theorem (Isabelle) and a verified PAC bound for decision stumps (Lean) are qualitative/probabilistic theorems; neither provides finite-sample error bounds, verified distribution-function evaluation, or floating-point correctness, all of which an executable hypothesis test needs.

## Applicability

**Subjects and their relation.** The report examines the correctness of statistical implementations from four independent angles; the subjects are compared, not combined:

1. *Reference data:* the NIST StRD collection as served on 2026-11-20 (9 univariate, 11 ANOVA and 11 linear least-squares datasets read and executed; nonlinear datasets described from NIST's pages only). The ANOVA files were taken from SciPy's test tree at the pinned revision; the others from NIST's site (SHA-256 of every input file in `support/strd_inputs.sha256`).
2. *Implementations executed:* numpy 2.3.5 (Debian build, linked to the single-threaded reference BLAS/LAPACK 3.12.1; `lstsq` uses LAPACK's SVD-based driver), CPython 3.13.15 `statistics`. Toy formulas (one-pass and two-pass variance/ANOVA, normal equations, Householder QR via `numpy.linalg.qr`) are labelled "toy"; they characterize textbook algorithms, not any named package.
3. *Test suites and assessment tools read (not executed):* SciPy and statsmodels at their pinned revisions; `pharmaR/riskmetric`; CAMIS (`PSIAIMS/CAMIS`, directory `Comp/`); ProbFuzz and Storm artifacts (`uiuc-arc/probfuzz`, `uiuc-arc/storm`).
4. *Literature:* abstracts or publisher/indexed summaries for the spreadsheet and package accuracy studies; full text for Storm (2019) and the CLT formalization (arXiv version); abstracts for ProbFuzz (2018) and the PAC formalization.

Execution host for every measured number: x86-64 cloud VM, Intel Xeon @ 2.60 GHz, Debian, CPython 3.13.15, numpy 2.3.5, reference LAPACK 3.12.1. LRE results for numpy depend on the LAPACK build and could differ with OpenBLAS/MKL (not examined). Statements about SAS, SPSS, S-Plus, Excel, R or Stan come from the cited documents only; none of these was executed.

## Findings

### 1. How the StRD reference values are built and graded

- **Graded difficulty, multiple categories.** NIST's linear least-squares background page: datasets are "ordered by level of difficulty (lower, average, and higher)", "Strictly speaking the level of difficulty of a dataset depends on the algorithm used"; two no-intercept datasets are "average" because "We have encountered codes that produce negative R-squared and incorrect F-statistics"; higher-difficulty datasets "are multicollinear" (Longley, Wampler). Certified values cover parameter estimates, their standard deviations, residual standard deviation, R², and the ANOVA table, "quoted to 16 significant digits and are accurate up to the last digit, due to possible truncation errors" (the data files print 15). Passing all datasets "does not imply that your software will do the same for your particular dataset". Basis: documentation (NIST `lls/lls_info.shtml`).
- **Nonlinear regression.** Certified values "are 'best-available' solutions, obtained using 128-bit precision and confirmed by at least two different algorithms and software packages using analytic derivatives"; three starting values per problem (far, near, and the certified solution), because some codes "given the certified values as starting values, return parameter estimates that produce a final residual sum of squares" worse than the certified one. Basis: documentation (NIST `nls/nls_info.shtml`).
- **Linear procedures.** NIST material indexed by a web search on the observation date states that certified values for univariate, ANOVA and linear regression were computed carrying 500 digits; the primary background page redirected and could not be read, so this is **documentation via secondary index, unverified**. Independent check here: exact rational recomputation (`support/strd_probe.py`) reproduced all 9 univariate datasets (mean, s, r(1)) to LRE ≥ 14.5, all 11 ANOVA F statistics to 14.7–15.0, and all 11 linear-regression coefficient vectors to 14.3–15.0 — i.e. to the printed digits. Basis: execution.
- **Construction of hard cases.** NumAcc4: "a constructed/fabricated data set ... 9-digit floating point values and differ only in the last decimal place", certified mean 10000000.2, s = 0.1, r(1) = −0.999, all exact. SmLs07–09 ("13 Constant Leading Digits", higher difficulty) come from Simon and Lesage (1989). Basis: documentation (dataset headers).

### 2. The representation limit: what an LRE can mean

For decimal data x_i, a binary64 program sees fl(x_i). Define the *representation limit* as the LRE of the exact statistic of {fl(x_i)} against the certified value — no binary64 algorithm that parses the decimal input can be expected to exceed it. Measured (`support/strd_probe.out`):

| dataset | statistic | representation limit (LRE) | numpy | CPython `statistics` | toy one-pass | toy two-pass |
|---|---|---|---|---|---|---|
| Mavro | s | 13.1 | 13.1 | 13.1 | 9.4 | — |
| Michelso | s | 13.8 | 13.8 | 13.8 | 8.3 | — |
| NumAcc2 | s | 15.0 | 15.0 | 15.0 | 11.6 | — |
| NumAcc3 | s | 9.5 | 9.5 | 9.5 | 1.1 | — |
| NumAcc4 | s | 8.3 | 8.3 | 8.3 | 0.0 | — |
| NumAcc4 | r(1) | — | — | — | — | 10.7 |
| AtmWtAg | F | 10.2 | — | — | 1.6 | 8.5 |
| SmLs04 / 05 / 06 | F | 10.4 / 10.2 / 10.2 | — | — | 2.4 / 0.3 / 0.0 | 8.7 / 9.3 / 9.3 |
| SmLs07 / 08 / 09 | F | 4.4 / 4.2 / 4.2 | — | — | 0.0 / 0.0 / 0.0 | 2.7 / 3.3 / 3.3 |
| Filip | min coeff. | 7.7 | lstsq 0.0 (rank 10); `rcond=0` 5.6 | — | normal eq. 0.0 | QR 7.5 |
| Pontius | min coeff. | 13.5 | lstsq 6.2 | — | normal eq. 11.2 | QR 12.4 |
| Longley | min coeff. | 14.6 | lstsq 10.9 | — | normal eq. 7.4 | QR 10.9 |
| Wampler4 / 5 | min coeff. | 15.0 / 15.0 | lstsq 7.8 / 5.8 | — | normal eq. 6.1 / 6.1 | QR 7.8 / 5.8 |

All means had LRE 15 with numpy and `statistics`. Basis: execution (real numpy and CPython for the named columns; toy formulas otherwise). Consequences (derived):
- NumAcc3/NumAcc4 and SmLs04–09 test *input conversion* as much as algorithms; an implementation reaching LRE 8.3 on NumAcc4's s has no algorithmic error at all.
- CPython's `statistics.stdev` is exact on its binary64 inputs by construction: `_ss` "Return[s] the exact mean and sum of square deviations" using `Fraction` accumulation (`Lib/statistics.py:212–214`) and `_float_sqrt_of_frac` is "Square root of n/m as a float, correctly rounded" (line 430); its result therefore equals the representation limit.
- SciPy's relaxation of its ANOVA test tolerance to rtol 1e-4 for SmLs07–09 (§4) is close to the best any binary64-parsing implementation can achieve (limit 4.2–4.4), not merely a concession to a weak algorithm.

### 3. Silent rank truncation in `numpy.linalg.lstsq`

`numpy/linalg/_linalg.py` at v2.3.5: the docstring (lines 2464–2470) says singular values "smaller than `rcond` times the largest singular value" are treated as zero and "The default uses the machine precision times ``max(M, N)``"; the code is `if rcond is None: rcond = finfo(t).eps * max(n, m)` (lines 2553–2554). For Filip (82 × 11, cond₂(X) = 1.8e15 > 1/(82·2.2e-16) ≈ 5.5e13) the default returns rank 10 and coefficients with LRE 0.0, without warning; passing `rcond=0` restores rank 11 and LRE 5.6. A gate that consumes only the coefficient vector cannot see the truncation. For Pontius (cond₂ 1.4e13, below the cutoff) `lstsq` lost 6–7 more digits than Householder QR (6.2 vs 12.4), consistent with an SVD of unscaled polynomial columns. Basis: source + execution.

### 4. How open-source suites embed reference data

| Suite (pinned) | StRD content | Tolerance | Notes |
|---|---|---|---|
| SciPy `scipy/stats/tests/test_stats.py` | 11 ANOVA files in `tests/data/nist_anova/` (`test_nist`, lines 7914–7942) | `rtol = 1e-7`; `rtol = 1e-4` for `('SmLs07', 'SmLs08', 'SmLs09')` ("With the hard test cases we relax the tolerance a bit") | only F is compared, not sums of squares |
| SciPy, same file | Norris as literals (`test_nist_norris`, line 2266) for `linregress` | default of `xp_assert_close` (delegated helper; value not examined) | `tests/data/nist_linregress/` holds only `Norris.dat` |
| SciPy | univariate, other linear (Longley, Filip, Wampler), nonlinear | — | **absent** from the repository tree (path search) |
| statsmodels `statsmodels/regression/tests/test_regression.py` | Longley (`datasets/longley/longley.csv`; certified values in `tests/results/results_regression.py`, class `Longley`, "obtained from NIST") | params: `assert_almost_equal(..., DECIMAL_4)` (absolute ±1.5e-4); bse: see below; CI: `rtol=10**-4` | `test_fit_chol_longley` notes "the normal equations lose about half of the digits" and compares Cholesky to pinv at rtol 1e-6 |

**statsmodels standard-error check defect.** Lines 48 and 74–77 at the pinned revision:

```python
DECIMAL_4 = 4
...
    decimal_standarderrors = DECIMAL_4

    def test_standarderrors(self):
        assert_allclose(self.res1.bse, self.res2.bse, self.decimal_standarderrors)
```

`assert_allclose` is `numpy.testing.assert_allclose(actual, desired, rtol=1e-07, ...)` (imported at line 15–17), so the third positional argument is `rtol = 4`: every `CheckRegressionResults` subclass that keeps the default accepts standard errors within a factor of 5 of the reference. The adjacent confidence-interval test uses `rtol=10**-self.decimal_confidenceintervals` (lines 79–95), showing the intended meaning. Executed demonstration (`support/defect_demos.out`, numpy 2.3.5): `assert_allclose([4.9], [1.0], 4)` passes; `[5.1]` fails; `rtol=1e-4` rejects `1.0002`. The CI test still constrains bse indirectly (bounds are params ± t·bse). Basis: source + execution. The absolute 4-decimal parameter tolerance is itself scale-dependent: on Longley it demands LRE ≈ 10 for the intercept (−3482258.63) but only ≈ 2.4 for the 0.0358 coefficient (derived).

### 5. Published accuracy studies

| Study | Subject | What could be verified | Basis |
|---|---|---|---|
| McCullough 1998, Am. Stat. 52(4) | methodology | "intermediate-level tests focusing on three areas: estimation, both linear and nonlinear; random number generation; and statistical distributions" | abstract (OpenAlex) |
| McCullough 1999, Am. Stat. 53(2) | SAS, SPSS, S-Plus | "Weaknesses are identified in all the random number generators, the S-Plus correlation procedure, and in the one-way ANOVA and nonlinear least squares routines of SAS and SPSS" | abstract |
| McCullough–Wilson 1999, CSDA 31(1) | Excel 97 | inadequate in estimation, RNG and distributions; advice not to use Excel for statistics | secondary summary only |
| McCullough–Wilson 2002, CSDA 40(4) | Excel 2000/XP | title, venue | metadata only |
| McCullough–Wilson 2005, CSDA 49(4) | Excel 2003 | title, venue | metadata only |
| McCullough–Heiser 2008, CSDA 52(10) | Excel 2007 | "fails a standard set of intermediate-level accuracy tests in three areas"; "Microsoft's continuing inability to correctly fix errors" | abstract as reproduced by a search index (publisher page not reachable) |
| Yalta 2008, CSDA 52(10) | Excel 2007 distributions | title, venue | metadata only |
| Keeling–Pavur 2007, CSDA 51(8) | nine packages | uses StRD univariate, ANOVA, linear and nonlinear datasets | secondary summary only |
| Almiron et al. 2010, JSS 34(4) | Calc, Excel, Gnumeric, NeoOffice, Oleo on i386/amd64 under Windows Vista, Ubuntu, Mac OS | "there is no safe choice among the spreadsheets here assessed: they all fail in nonlinear regression and they are not suited for Monte Carlo experiments" | abstract (journal page) |
| Mélard 2014, Comput. Stat. 29(5) | Excel 2010, OpenOffice.org Calc 3.3, Gnumeric 1.10.16 | "Microsoft has partially improved the statistical aspects of Excel, essentially the statistical functions and the random number generator" | abstract (publisher page) |

Fix history across versions (derived from the sequence of abstracts): failures reported for Excel 97 persisted in the authors' assessment through 2007 and were partly fixed by 2010; which individual procedures changed, and their LREs, is **not examined**. The one-pass failures in §2 reproduce the *mechanism* (Chan, Golub, LeVeque 1983 analyze the instability of the textbook one-pass variance; Welford 1962 gives a stable updating method), not any specific package's code.

### 6. CAMIS: cross-language divergences of named procedures

All 47 documents in `Comp/` were classified by reading each file (counts by primary outcome):

| Outcome | Files | Typical documented cause |
|---|---|---|
| Agreement only | 17 | e.g. ANCOVA "identical results for the datasets tried"; OLS in R, SAS, Python "equivalent results" |
| Divergence resolvable by an option | 4 | McNemar: "{stats} is using Edward's continuity correction by default ... there is no option to include Edward's continuity correction in SAS"; quantiles: SAS `PCTLDEF=5` vs R `type = 7`, aligned by `type=2` (25th/40th percentiles 30, 95 vs 32.5, 106) |
| Legitimate method difference | 1 | Wilcoxon signed-rank / Hodges–Lehmann estimator computation |
| Unresolved | 1 | Jonckheere–Terpstra: statistic equal, p 0.002655 vs 0.002649, "The reason for this gap may be either of the following" |
| Mixed (several of the above) | 24 | chi-square (R applies Yates' correction to 2×2 by default; Fisher odds ratio conditional MLE vs sample OR); exact binomial two-sided p (0.00168 vs 0.0019: "both R and SAS compute this test differently"); negative binomial SEs (expected vs observed information); MMRM/GLMM (non-convergence of some R optimizers) |

Across all files, 15 contain an option-alignable divergence, 19 a method divergence, 4 an unresolved part and 3 a defect-attributed part: a SAS macro error "fixed by updating rows 449 and 450 of the SAS macro from using 1E-15 ... to be 1E-9" (Poisson-rate CIs); SAS `round()` and `cards::round5()` "are incorrect in rare different cases" (rounding: SAS rounds half away from zero, base R to even — "Both are right based on what they say they do, but they produce different results"); an error from `vcdExtra::CMHtest` on sparse tables (CMH). The documents also contain self-contradictions a reviewer should not trust blindly (e.g. an RMST intercept printed as 380.8065 vs 308.8065 while the text says the results "match exactly"; a binomial-test summary claiming identity that contradicts its own p-value table). Basis: documentation (CAMIS documents; results shown only as images were not inspected).

**riskmetric.** 19 `assess_*` metrics (`R/`): code coverage (`covr`), dependencies, downloads, exported help/namespace, bug-report URL, examples, maintainer, NEWS (present/current), source control, vignettes, website, status of last 30 bugs, license, `R CMD check` notes/warnings/errors, remote checks, reverse dependencies, codebase size. The README describes metrics of "development best practices, code documentation, community engagement and development sustainability" and marks the package "Maintenance Only" in favour of `val.meter`. None of the metrics compares outputs with reference values; numerical correctness enters only indirectly through the package's own tests (coverage, `R CMD check`). Basis: source + documentation.

**Regulatory statement.** The R Foundation's "R: Regulatory Compliance and Validation Issues" (version dated March 12, 2026) quotes the FDA's May 2015 "Statistical Software Clarifying Statement": "FDA does not require use of any specific software for statistical analyses ... However, the software package(s) used for statistical analyses should be fully documented in the submission, including version and build identification", citing ICH E9: "The computer software used for data management and statistical analysis should be reliable, and documentation of appropriate software testing procedures should be available." The same document points users to R's `tests` sub-directory as "objective evidence as to the accuracy, reliability and consistency of their installation of R". Basis: documentation.

### 7. Differential testing of probabilistic programming systems

- **ProbFuzz** (Dutta, Legunsen, Huang, Misailovic, ESEC/FSE 2018; abstract): characterizes "118 previously reported bugs" in Edward, Pyro and Stan; generates programs from templates with holes, translates them per system, and checks outputs "against several oracles, including an accuracy checker"; found "67 previously unknown bugs", "51 bug fixes" accepted. The artifact (`uiuc-arc/probfuzz`): templates `simple`, `linearregression`, `mlr`, `cond` (`language/templates/`); back ends `stan.py`, `edward.py`, `pyro.py`; `summary.sh` reports per program and system Crash (no `se_mean`/`_mean` in output), Num (an `inf`/`nan` token) and Acc (metric script output does not contain "True", line 53). Metrics are SMAPE scripts (`metrics/*_smape.py`) comparing a model's posterior means applied to the generated data with the observed data. `install.sh` installs `python2.7`, `tensorflow==1.5.0`, `pyro-ppl==0.2.1`.
- **Oracle defect in the artifact.** `metrics/lr_smape.py` line 7 `smape_thres=sys.argv[1]` (a `str`), line 27 `if abs(smape) <= smape_thres:`; `metrics/lr_smape.sh` passes the literal `0.1`; `config.json` selects `"metric" : "lr_smape"`. Under Python 3 the comparison raises (`UFuncTypeError` for `numpy.float64`, `TypeError` for `float`; executed in `support/defect_demos.out`), so nothing is printed and `summary.sh` marks every program as an accuracy failure; under Python 2.7 mixed-type comparison falls back to an implementation-defined ordering, so the outcome is constant rather than data-dependent (derived, not executed). Also, when weight/bias extraction yields too few arguments, the `except` branch prints `True` (no failure). Whether the paper's reported accuracy bugs were found with this script or another version is **unknown**. Basis: source + execution (Python 3 part).
- **Storm** (Dutta, Zhang, Huang, Misailovic, ESEC/FSE 2019; full text): language-agnostic reduction through Storm-IR combining generic (C-Reduce-like) and probabilistic transformations (distributions, data size, inference arguments); preserved property: the reduced program "reproduces the same error status and message"; 47 programs (34 Stan, 13 Pyro); Stan reductions 49 % code, 67 % data, 96 % iterations; Pyro 58 %, 96 %, 99 %; run time of reduced vs original tests (Table 6) 1.02 s → 0.25 s (4.1×, Stan issues), 12.63 s → 0.10 s (126.3×, Stan examples), 106.36 s → 0.85 s (125.1×, Pyro); total reduction time per suite on a 12-core machine 41:24–55:58 (Stan issues), 42:15–52:28 (Stan examples), 1:46–7:14 (Pyro) min:s across six transformation orders (Table 7). Basis: documentation (paper).

### 8. How far formalized statistics reaches toward an executable test

- **CLT (Avigad, Hölzl, Serafin 2017, Isabelle).** Statement: for i.i.d. square-integrable X_n with variance σ² > 0 and common distribution μ, the law of (S_n − n·c)/√(nσ²) converges weakly (`weak_conv_m`, defined via CDFs) to `std_normal_distribution`. The final proof "is only about 120 lines long" on top of extended measure-theory and characteristic-function libraries. It is qualitative: no rate (Berry–Esseen-type results are mentioned as other work). Basis: documentation (paper, arXiv version).
- **PAC learnability of decision stumps (Tassarotti, Vajjha, Banerjee, Tristan, CPP 2021, Lean).** A probability bound on the error of a learned threshold classifier, structured to "separate reasoning about deterministic properties of a learning function from proofs of measurability and analysis of probabilities". Basis: documentation (abstract).
- **Gap to a verified gate (derived).** To certify "this implementation of test T rejects at level α exactly when it should" one additionally needs: (a) finite-sample distributional statements (exact null distributions or explicit approximation-error bounds — neither theorem supplies them); (b) verified evaluation of distribution functions/quantiles (e.g. regularized incomplete beta for t and F) with rigorous floating-point error bounds; (c) a verified computation of the statistic from binary data, including summation error; (d) a specification of input conversion — §2 shows that conversion alone can limit accuracy to 4 digits. None of the examined formalizations addresses (b)–(d).

### 9. Cost and footprint at six levels

| Level | Quantity | Value | Source |
|---|---|---|---|
| L1 authoring | CLT final proof | ≈ 120 lines atop libraries | Avigad et al. |
| L1 | size of CAMIS comparison corpus | 47 comparison documents in `Comp/` | measured (tree listing) |
| L2 build | SciPy/statsmodels/R/ProbFuzz builds | not measured | — |
| L3 | Storm reduction time per suite | 1:46 to 55:58 min:s (12 cores) | Storm Table 7 |
| L4 run time | Storm-reduced test speedup | 4.1×–126.3× | Storm Table 6 |
| L4 | `strd_probe.py` (all 31 datasets incl. exact recomputation) | 1.7 s wall | measured |
| L5 check | exact rational recomputation of all certified values used | included in the 1.7 s above | measured |
| L6 footprint | StRD inputs used | 31 files, largest SmLs09.dat 577,633 bytes | measured |
| L6 | memory/peak RSS of any package under test | not measured | — |

### 10. Comprehensibility and conceptual simplicity

- **C1.** An LRE is one number that silently mixes three error sources — input conversion, algorithm, and the reference's own rounding (15 printed digits). A reviewer of a gate should see the representation limit beside every LRE. CAMIS documents are human-readable explanations of *why* two implementations differ, which is the information a regulated user needs; their self-contradictions (§6) show they are not mechanically checked. `lstsq`'s rank truncation is reported only through a second return value, which a gate written as `beta = lstsq(X, y)[0]` discards.
- **C2.** "Same named procedure" is an underspecified identity: the CAMIS cases reduce to a small set of orthogonal parameters (continuity correction, tie handling, quantile definition, p-value definition for asymmetric discrete tests, variance estimator, rounding rule, optimizer and convergence criterion). Treating these as explicit, named arguments of the procedure, rather than package defaults, turns most "divergences" into ordinary parameter choices; the residual cases are genuine method differences or defects.

### 11. Validation of the validators (V1–V4)

- **V1 (specification adequacy).** StRD certified values were independently reproduced here in exact arithmetic (§1), so the references themselves are sound for the datasets examined. The test suites' adequacy is weaker: the statsmodels bse check is ineffective (§4); SciPy's ANOVA test compares only F. ProbFuzz's linear-regression accuracy oracle is non-functional as published (§7). A mutation-style check — perturb a reference value by 1 % and confirm the test fails — would have exposed the statsmodels defect.
- **V2 (differential testing).** CAMIS is manual differential testing across R/SAS/Python; ProbFuzz automates differential and oracle-based testing across PPS back ends; Storm minimizes failing inputs. No automatic differential run across statistical packages on StRD was found in the examined repositories (not examined beyond them).
- **V3 (platform).** Almiron et al. explicitly vary hardware (i386/amd64) and operating system; the numpy results here are for one LAPACK build.
- **V4 (human comprehension).** Not examined.

## Boundaries

- **Not examined:** the full text and per-procedure LRE tables of McCullough 1998/1999, McCullough–Wilson 1999/2002/2005, McCullough–Heiser 2008, Yalta 2008, Keeling–Pavur 2007, Almiron et al. 2010 and Mélard 2014; the ProbFuzz paper body (abstract only); Altman, Gill and McDonald's 2003 book; Knüsel's studies of Excel distributions; the StRD MCMC and nonlinear datasets (no nonlinear dataset was run); R and SAS behaviour (CAMIS text only); CAMIS results shown only as images; SciPy and statsmodels were not installed, so their tests were read, not run.
- **Unknown:** whether NIST's linear-procedure certification used 500-digit arithmetic (secondary only; the values are reproduced exactly here regardless); which Excel procedures were fixed in which release; whether ProbFuzz's published accuracy bugs relied on `lr_smape.py`; how `numpy.linalg.lstsq` behaves with OpenBLAS or MKL LAPACK on these datasets.
- **Known not to apply:** the representation limit does not bound implementations that parse decimal data exactly (decimal or rational input), e.g. a rational pipeline reaches the certified values (§1); conclusions about `statistics.stdev` exactness do not extend to `statistics.fmean`/`correlation` (not examined).
- **Toy-model caveats:** one-pass, two-pass, normal-equation and QR results are re-implementations of textbook formulas; they reproduce failure mechanisms reported for packages but are not measurements of any package other than numpy/CPython where named.
- **Stronger conclusions not established:** that statsmodels' regression standard errors are wrong (only that the test cannot detect errors below 400 %; the CI test constrains them indirectly); that CAMIS divergences are harmless (the documents classify causes, not consequences); that riskmetric scores correlate or fail to correlate with numerical accuracy (no data examined).

## Evidence

Observation date for all evidence: 2026-11-20 (UTC). GitHub revisions resolved through the GitHub API on that date; full revisions in `REPORT.json`.

**Repositories:**
- `scipy/scipy` @ `73d740ca203cd4ce087a1a818fb2db576646eacc`: `scipy/stats/tests/test_stats.py:56–64` (docstring citing NIST/McCullough), `2266–2294` (`test_nist_norris`), `7914–7942` (`test_nist`, tolerances); `scipy/stats/tests/data/nist_anova/*.dat` (11 files); `scipy/stats/tests/data/nist_linregress/Norris.dat`; `scipy/_lib/_array_api.py:279` (`xp_assert_close`, `rtol=None`).
- `statsmodels/statsmodels` @ `b96a618f835b5b0c306e9b8b93efdbb4b0f6e59c`: `statsmodels/regression/tests/test_regression.py:15–17, 48–53, 60–95, 222–240, 2620–2633`; `statsmodels/regression/tests/results/results_regression.py:10–40`; `statsmodels/datasets/longley/data.py:8–20`.
- `numpy/numpy` tag v2.3.5 @ `c3d60fc8393f3ca3306b8ce8b6453d43737e3d90`: `numpy/linalg/_linalg.py:2443–2588` (`lstsq`; docstring 2464–2470; default `rcond` 2553–2554).
- `python/cpython` tag v3.13.15 @ `4061bc4c35f7c26f25264666d4ba083b93d2f6f9`: `Lib/statistics.py:158–250` (`_sum`, `_ss`), `429–440` (`_float_sqrt_of_frac`), `1196–1216` (`stdev`).
- `Reference-LAPACK/lapack` tag v3.12.1 @ `6ec7f2bc4ecf4c4a93496aa2fa519575bc0e39ca`: upstream identity of the host LAPACK.
- `PSIAIMS/CAMIS` @ `a08825e2fa4d6db76714d4e43923a6d647bfcbec`: all 47 files `Comp/*.qmd` (e.g. `Comp/r-sas_mcnemar.qmd` line 63; `Comp/r-sas-summary-stats.qmd` lines 33, 52, 56, 58; `Comp/r-sas_rounding.qmd` lines 7, 9; `Comp/r-sas_ci_for_poissonrate.qmd` line 15; `Comp/r-sas_jonckheere.qmd` line 24; `Comp/r-sas_binomial_test.qmd` lines 89, 122; `Comp/r-sas_chi-sq.qmd` line 302).
- `pharmaR/riskmetric` @ `fd07e38635ddd2ba675c6afa4fa1ba4ff787fd19` (version 0.2.7): `R/assess_*.R` (19 files), `README.md:9–32`, `DESCRIPTION`.
- `uiuc-arc/probfuzz` @ `29144130466ec20debdf7bddbfd82300ca33c0db`: `README.md`, `config.json`, `install.sh`, `summary.sh:28–60`, `metrics/lr_smape.py:1–30`, `metrics/lr_smape.sh`, `backends/`, `language/templates/`.
- `uiuc-arc/storm` @ `57a0445227e74fcb4f6059c927f03e76b3fc52d2`: `README.md` (test sets `stan`, `stan_em`, `pyro`), `bugs/templates/`.

**Other primary sources:** NIST StRD pages `https://www.itl.nist.gov/div898/strd/lls/lls_info.shtml`, `.../nls/nls_info.shtml`, `.../lls/lls.shtml`, `.../nls/nls_main.shtml` and dataset files (hashes in `support/strd_inputs.sha256`; manifest file SHA-256 prefix `28091bea1072db93`). R Foundation, "R: Regulatory Compliance and Validation Issues", `https://www.r-project.org/doc/R-FDA.pdf`, version dated March 12, 2026. Storm paper text from the authors' copy (`misailo.cs.illinois.edu/papers/storm-fse19.pdf`); its abstract also verified on a conference listing page.

**Literature (DOIs verified through the doi.org handle API, `responseCode` 1, plus OpenAlex title/author/venue/year; Crossref's API was not reachable from the fetch tool):** McCullough, "Assessing the Reliability of Statistical Software: Part I", Am. Stat. 52(4), 1998, DOI 10.1080/00031305.1998.10480597; "Part II", Am. Stat. 53(2), 1999, DOI 10.1080/00031305.1999.10474450. McCullough, Wilson, Excel 97: CSDA 31(1):27–37, 1999, DOI 10.1016/S0167-9473(99)00004-3; Excel 2000 and XP: CSDA 40(4):713–721, 2002, DOI 10.1016/S0167-9473(02)00095-6; Excel 2003: CSDA 49(4):1244–1252, 2005 (OpenAlex lists 2004), DOI 10.1016/j.csda.2004.06.016. McCullough, Heiser, Excel 2007: CSDA 52(10):4570–4578, 2008, DOI 10.1016/j.csda.2008.03.004. Yalta, CSDA 52(10):4579–4586, 2008, DOI 10.1016/j.csda.2008.03.005. Keeling, Pavur, CSDA 51(8):3811–3831, 2007, DOI 10.1016/j.csda.2006.02.013. Almiron, Lopes, Oliveira, Medeiros, Frery, JSS 34(4), 2010, DOI 10.18637/jss.v034.i04. Mélard, Comput. Stat. 29(5):1095–1128, 2014, DOI 10.1007/s00180-014-0482-5. Altman, Gill, McDonald, Numerical Issues in Statistical Computing for the Social Scientist, Wiley 2003, DOI 10.1002/0471475769. Chan, Golub, LeVeque, Am. Stat. 37(3), 1983, DOI 10.1080/00031305.1983.10483115. Welford, Technometrics 4(3), 1962, DOI 10.1080/00401706.1962.10490022. Hyndman, Fan, "Sample Quantiles in Statistical Packages", Am. Stat. 50(4), 1996, DOI 10.1080/00031305.1996.10473566 (background for quantile definitions; not examined in full). Dutta, Legunsen, Huang, Misailovic, ESEC/FSE 2018, pp. 574–586, DOI 10.1145/3236024.3236057. Dutta, Zhang, Huang, Misailovic, ESEC/FSE 2019, pp. 729–739, DOI 10.1145/3338906.3338972. Avigad, Hölzl, Serafin, J. Autom. Reasoning 59(4):389–423, 2017, DOI 10.1007/s10817-017-9404-x (arXiv:1405.7012 text read). Tassarotti, Vajjha, Banerjee, Tristan, CPP 2021, pp. 5–17, DOI 10.1145/3437992.3439917 (arXiv:1911.00385 abstract). StRD documentation itself has no DOI.

**Execution (outputs preserved in `support/`):**

```text
python3 support/strd_probe.py <dir with the 31 StRD .dat files>   > support/strd_probe.out   (1.7 s)
python3 support/defect_demos.py                                    > support/defect_demos.out
```

## Revalidation

- **References:** `support/strd_probe.py` recomputes every certified value it uses in exact arithmetic ("exact" columns; `exact-recompute-matches=True`); a changed StRD file shows up as a hash mismatch against `support/strd_inputs.sha256`.
- **An implementation under test:** add it as a column in `strd_probe.py` and compare each LRE with the printed representation limit; anything below the limit is algorithmic loss.
- **numpy `lstsq`:** rerun the Filip row; the finding holds while `rank` < 11 with `rcond=None` (check `numpy/linalg/_linalg.py` for the default `rcond` expression).
- **statsmodels:** `grep -n "assert_allclose(self.res1.bse" statsmodels/regression/tests/test_regression.py`; the defect is fixed when `rtol=10**-self.decimal_standarderrors` (or equivalent) is passed.
- **SciPy:** check `test_nist` in `scipy/stats/tests/test_stats.py` for the tolerance pair and the dataset list, and the repository tree for any added StRD categories.
- **CAMIS:** list `Comp/` and diff changed files; re-classify only changed documents.
- **ProbFuzz:** inspect `metrics/lr_smape.py` lines 7 and 27; the oracle works only once the threshold is converted with `float(...)`.
- **Formalization reach:** search the current Isabelle AFP and Lean mathlib for Berry–Esseen or verified incomplete-beta evaluation; the gap analysis in §8 changes only if such results exist and connect to floating point.
