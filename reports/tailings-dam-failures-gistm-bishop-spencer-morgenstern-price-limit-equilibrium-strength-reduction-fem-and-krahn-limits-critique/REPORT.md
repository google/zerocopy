# Slope and tailings-embankment stability: limit-equilibrium methods of slices, strength-reduction FEM, reliability formulations, open codes, and failure-review evidence

## Summary

- **A reported factor of safety (FS) is the output of four separable choices, not of "the method".** These are the equilibrium formulation (Ordinary/Fellenius, Bishop simplified, Spencer, Morgenstern–Price/GLE), the critical-surface search, the convergence and admissibility policy, and the strength model. On one 2H:1V, 10 m homogeneous slope (γ = 20 kN/m³, c′ = 15 kPa, φ′ = 20°, dry):
  - **Method:** on one fixed circle the four methods give OMS 1.514, Bishop 1.595, Spencer 1.591 and Morgenstern–Price (half-sine) 1.591 (toy implementation).
  - **Search:** varying only the search density of an open Bishop code moves the minimum FS non-monotonically between 1.588 and 1.605. That is about 1%, larger than the Bishop–Spencer–Morgenstern–Price spread on the fixed circle (about 0.2%).
  - **Strength reduction:** a textbook viscoplastic strength-reduction program brackets failure between trial factors 1.53 and 1.58, depending on mesh and iteration ceiling.
  - Basis: execution (upstream PySlope and textbook program 6.4) + execution (toy model, labelled).
- **Strength-reduction FS is defined by a numerical failure criterion, and the classic relative-displacement test cannot detect steady plastic flow.** In the textbook program 6.4, a trial "converges" when max|Δu|/max|u| ≤ tol. Under steady plastic flow, u grows roughly linearly with iteration count n, so that ratio decays like 1/n. Any trial therefore "converges" at about n ≈ 1/tol, however unstable it is.
  - Measured: with tol = 10⁻⁴ and a 30 000-iteration ceiling, trial factors 1.7, 2.0 and 3.0 all "converged", at 9 936–9 978 iterations, with maximum displacements of 2.07, 11.3 and 40.9 m. Under the same model the elastic displacement is 0.017 m.
  - With tol = 10⁻³ and a 1 000-iteration ceiling, the first non-converging trial was 2.80.
  - xslope pairs its relative-displacement test with a per-node force-equilibrium test and a displacement cap of 0.1 × mesh height. It documents the cap as the guard against "false convergence at true failure" (Basis: execution + source).
- **Reliability is not a monotone function of FS.** Christian, Ladd & Baecher (1994) report for the James Bay dikes:
  - E[F] = 1.500 → β = 1.84; E[F] = 1.453 → β = 2.66; E[F] = 1.427 → β = 3.69. The ranking by β is the reverse of the ranking by FS.
  - These indices depend on separating spatial variability, which averages along the slip surface (variance reduction ratio 0.2 or 0.7 in their cases), from systematic error, which does not.
  - A Taylor-series implementation (xslope) uses a lognormal index without spatial averaging. Recomputed from the published variance components, the 12 m dike's index ranges over 1.77–3.15, depending on (normal vs lognormal) × (averaged vs not).
  - Basis: documentation + derived.
- **Expert panels found limit-equilibrium FS an unreliable guide for brittle, contractive tailings and foundations; the strength model and site characterization governed outcomes.**
  - Mount Polley (2015): pre-failure effective-stress FS values met or exceeded 1.3. At the section near the breach the critical surface never reached the weak glaciolacustrine layer (FS 1.77). The back-analysis needed an undrained strength ratio of 0.27 (2D Morgenstern–Price) and 0.29 (strength reduction).
  - Feijão Dam I (2019): limit-equilibrium analysis with s_u/σ′_vo = 0.26 gave FS close to 1.0, while peak undrained strengths gave FS close to 1.5. The panel calls limit equilibrium "misleading" when strength loss is possible.
  - Fundão (2016): liquefaction was triggered by lateral extrusion before a shear mechanism reached FS = 1.
  - Basis: documentation (panel reports).
- **The open codes differ sharply in what they refuse to report.**
  - PySlope silently returns the last Bishop iterate after 15 iterations and checks only m_α = 0 exactly.
  - xslope refuses non-converged, inadmissible (m_α < 0.05, more than 50% base tension) and no-root solutions with typed messages.
  - pyBIMstab's convergence flag is computed by `all((d1, d2)) <= tol`, which is true only when one successive difference is exactly 0.0. Its λ-point filter `np.where(tolM and tolF)` ignores the moment-equilibrium flags.
  - Basis: source + execution.

## Applicability

**Subjects and their relation.** The report compares three open-source slope-stability codes and one textbook strength-reduction program at pinned revisions. It interprets them through the primary method papers, one reliability paper, a published discussion of an LEM-versus-strength-reduction comparison, three expert failure-review reports and one industry standard:

| subject | revision / identity | role | how examined |
|---|---|---|---|
| PySlope | `JesseBonanno/PySlope@d6167796769743e069ec540588193216753b678f` | Bishop simplified + entry–exit circular search | source read; analysis core **executed** unmodified (import shims replace `plotly`, `tqdm` and `colour`, which are used only for plotting/progress) |
| xslope 1.0.9 | `njones61/xslope@28f16877a9c204ed421d3e2d6e353609ec8d0c8b` | OMS/Bishop/Janbu/Spencer/Morgenstern–Price/Corps/Lowe, circular and non-circular search, viscoplastic strength reduction, Taylor/Monte Carlo/response-surface reliability | source read only (**not executed**; requires pandas, scipy, shapely and other packages not installed in the probe environment) |
| pyBIMstab 0.1.4 | `eamontoyaa/pyBIMstab@ca13d23379c60453e1df53c6d3849902e3c600e0` | GLE (Fredlund–Krahn) for block-in-matrix slopes with A*-searched tortuous surfaces | source read; two Boolean expressions evaluated in CPython; the package itself was **not executed** (needs scipy, matplotlib, shapely) |
| Smith & Griffiths program 6.4 (community port) | `cunyizju/Programming-FEM-5th-Fortran@bf19e8a773c2a9f0a9a10f304540efdf586955f1` | viscoplastic strength reduction, 8-node quadrilaterals | built from the pinned archive with gfortran 15.2.0 and **executed**. The published example output is reproduced exactly. One probe patch initialises two locals (see Findings §5) |

The papers, panel reports and standard are identified in `REPORT.json`. **Coverage is uneven**:

- **Read in full:** Christian et al. 1994, the Bojorque et al. discussion, and the Mount Polley, Feijão Dam I and Fundão reports.
- **Abstract plus verified bibliographic metadata only:** Morgenstern–Price 1965, Spencer 1967, Fredlund–Krahn 1977, Griffiths–Lane 1999, Zhu et al. 2003 and Krahn 2003.
- **Bibliographic metadata only:** Bishop 1955, Dawson et al. 1999, Cheng et al. 2007 (its content enters only through the discussion) and Santamarina et al. 2019 (plus its one-sentence standfirst).
- **The GISTM primary PDF could not be retrieved.** Its requirement wording below comes from secondary reproductions.

**Scope of execution.** All execution was on one Linux x86-64 virtual machine (Intel Xeon @ 2.60 GHz, 96 vCPUs) with CPython 3.13.15, NumPy 2.3.5 and GNU Fortran 15.2.0, on 2026-11-21 (UTC).

- The benchmark slope is the published program-6.4 example: crest width 20 m, face 20 m horizontal over 10 m height (2H:1V), toe width 20 m, foundation depth 5 m to a rigid base, φ′ = 20°, c′ = 15 kPa, ψ = 0, γ = 20 kN/m³, E = 10⁵ kPa, ν = 0.3, dry.
- PySlope cannot represent the rigid base. Its critical circle bottoms out 0.42–0.77 m below toe level, well above the base, so the base does not constrain it.
- Results are for this one geometry and do not extend to layered, saturated or non-circular cases without re-running.

**What the toy model is.** `support/probes/toy_lem.py` is an independent implementation written for this report from the textbook equilibrium equations. It is not any product. Its Bishop solution agrees with PySlope's to within 2.0 × 10⁻¹⁴ relative on 13 circles (Findings §2), which validates it only on circular, dry, homogeneous cases.

## Findings

### 1. Equilibrium formulations and their unification

Basis: normative-strength sources are the method papers (abstracts) and the equations as implemented in the pinned sources. The per-slice algebra below is derived and executed in the toy model.

Consider slice *i* with weight W, base inclination α (positive where the base descends in the direction of motion), base length l = b/cos α, width b, pore force U = u·l, and Mohr–Coulomb strength (c′, φ′). Let E and X be the interslice normal and shear forces. The mobilized base shear is S = (c′l + N′ tan φ′)/F. The vertical and horizontal per-slice equilibrium equations give

```text
N' = [W + (X_R − X_L) − U cos α − c' l sin α / F] / m_α,     m_α = cos α + sin α tan φ' / F
E_R = E_L + (N' + U) sin α − S cos α
moment about a circle centre (interslice forces cancel):  F_m = Σ (c' l + N' tan φ') / Σ W sin α
force closure:                                            F_f is the F with E_{n+1} = 0 given E_0 = 0
GLE closure assumption:                                   X = λ · f(x) · E
```

| method | equilibrium enforced | interslice assumption | unknowns solved | source evidence |
|---|---|---|---|---|
| Ordinary (Fellenius) | moment about centre; no per-slice force balance | interslice resultant ignored (N′ = W cos α − U) | F only | PySlope `pyslope.py:1491-1504`; toy `oms` |
| Bishop simplified | moment about centre + per-slice vertical force | X_R − X_L = 0 (horizontal interslice forces) | F (fixed point in m_α) | PySlope `pyslope.py:1709-1731`; xslope `solve.py:753-935` |
| Spencer | moment + both force directions | X/E = tan θ constant (parallel resultants) | F, θ | Spencer 1967 abstract: "two equations of equilibrium, the first in respect of forces and the second in respect of moments"; xslope `solve.py:2116` ("Steve G. Wright's formulation from the UTEXAS v2 user manual") |
| Morgenstern–Price | moment + both force directions | X = λ f(x) E, f prescribed | F, λ | MP 1965 abstract: "all equilibrium and boundary conditions are satisfied"; xslope `solve.py:3398-3622`; pyBIMstab `slopestabl.py:575-680` |
| GLE (Fredlund–Krahn) | F_m(λ) and F_f(λ) solved independently; answer where they cross | as Morgenstern–Price | F, λ | Fredlund–Krahn 1977 abstract ("independent solution of the force and moment equilibrium factors of safety for various values of λ"); pyBIMstab README and `getFm`/`getFf` docstrings cite its Eqs. [16], [18], [20], [23] |
| Zhu et al. generalized framework | explicit F from both equations | assumed normal-stress distribution × modification function with two auxiliary unknowns | F + 2 auxiliaries | Zhu et al. 2003 abstract ("generally converges within a few iterations") |

The unification is concrete. Fredlund & Krahn state that "the normal force equation is of the same form for all methods with the exception of the ordinary method", and that the handling of interslice forces is what differentiates the methods. In xslope, `mprice` with `f_type='constant'` "reproduces `spencer()` to machine precision on both facings" (docstring, `solve.py:3421-3422`). In the toy model, λ = 0 in the GLE moment equation reproduces Bishop exactly. Basis: documentation + source + derived.

**Singularities are part of the formulation.** m_α vanishes at tan α = −F/tan φ′. Past that point N′ changes sign. The force recursion has an analogous per-slice determinant, cos(α − θ) + tan φ′/F · sin(α − θ). xslope's comments describe this determinant as producing "a dozen roots between 0.05 and 10, only one of which describes a body of soil" (`solve.py:130-139`). Its Spencer solver restricts θ to the pole-free band |α_i − θ − arctan(tan φ′_i/F)| < π/2 (`spencer_theta_bounds`, `solve.py:1592-1622`). Basis: source.

### 2. Method differences on a fixed surface, separated from search

Basis: execution of the toy model (labelled) + execution of upstream PySlope.

The toy grid search covered 43 495 admissible circles, with centres x ∈ [−5, 15] and y ∈ [10, 30] at 0.5 m spacing, radii R ∈ [5, 34.5] at 0.5 m, 50 slices, and circles rejected if they pass below the rigid base. It finished in 5.92 s. The critical Bishop circle has centre (15.0, 21.0) and R = 21.5. It enters the crest at x = −3.47 and exits at x = 19.88, with its lowest point 0.50 m below the toe. On that circle:

| method (toy) | FS | relative to Bishop | notes |
|---|---|---|---|
| Ordinary (OMS) | 1.5136 | −5.1% | no interslice forces |
| Bishop simplified | 1.5945 | — | 9 fixed-point iterations to 10⁻⁹; min m_α = 0.723 |
| Spencer (f = 1) | 1.5914 | −0.19% | λ = −0.335 (sign follows the toy's convention) |
| Morgenstern–Price (f = sin πs) | 1.5911 | −0.21% | λ = −0.411 |

**Cross-validation.** On six circles through this slope, five deep circles through it, and two circles through a second, frictional slope (1V:1.5H, c′ = 1 kPa, φ′ = 35°), the toy Bishop and PySlope's Bishop agree to within 2.0 × 10⁻¹⁴ relative, with PySlope run at max_iterations = 1000 and tolerance 10⁻⁹ (`support/outputs/pyslope_probe.txt`, P4 and P4b). The probe also reproduces PySlope's documented validation example (a), giving 1.2704, 2.1777, 3.9004 and 5.7184 for R = 2–5. These match the documentation's pySlope column and are within 0.11–0.31% of the Slide values quoted in its tests. Basis: execution.

These magnitudes are consistent with the claim summarised in Spencer's abstract that the paper "investigated" "the factors affecting the accuracy of Bishop's simplified method". For circular surfaces in this one homogeneous case, the rigorous methods differ from Bishop by about 0.2%. That number does not transfer to non-circular, layered or anisotropic cases (see Boundaries).

### 3. Critical-surface search is a separate, comparable source of FS variation

**PySlope entry–exit search** (`pyslope.py:1015-1081`, `1083-1169`). The search places `num_points_top` entry points on the crest and `num_points_bot` exit points on the face/toe, with `num_circles = max(5, int(iterations / 800))` radii per pair. The first radius is `1.1 ×` the vertical-tangent radius, a factor whose comment reads "increase to 1.1 to prevent ma denominator issues for bishops method" (line 1126). The others shrink the chord-to-edge distance linearly. Derived candidate counts are:

| `iterations` | num_circles | top × bottom points | candidates (derived) | evaluated (measured) | min FS, 25 slices | min FS, 50 slices | wall s (25 / 50) |
|---|---|---|---|---|---|---|---|
| 1 000 (code default) | 5 | 14 × 15 | 1 050 | 1 011 / 1 010 | 1.5882 | 1.5892 | 0.208 / 0.206 |
| 2 000 | 5 | 20 × 20 | 2 000 | 1 951 | 1.6044 | 1.6049 | 0.507 / 0.405 |
| 5 000 | 6 | 28 × 30 | 5 040 | 4 934 | 1.5948 | 1.5956 | 1.223 / 1.134 |
| 10 000 | 12 | 28 × 30 | 10 080 | 9 833 / 9 834 | 1.5891 | 1.5897 | 2.310 / 2.623 |

The minimum is **not monotone** in search effort (Basis: execution). The cause is derived from the code: each `iterations` value generates a different entry/exit lattice and a different set of radius fractions, not a refinement of the previous one, so a denser search can miss the region the sparser one hit. PySlope's own documentation spreadsheet shows the same pattern against Slide: pySlope 2.09/2.10/2.15 at 1 000/2 000/5 000 searches versus Slide 2.14 (`pyslope/examples/search.xlsx`). That spreadsheet was produced by an earlier version of the code, not the pinned revision. Its README also says "By default 2000 iterations are run with 50 slices per failure plane" (`README.md:141`), while the constructor sets `slices=25, iterations=1000` (`pyslope.py:287-293`). Basis: source + documentation.

**xslope circular search** (`search.py:660`, docstring lines 665-743). It is a "global 9-point circular search with adaptive grid refinement" whose stop is FS-driven: two successive refinement levels must each gain less than `fs_tol = 5e-4`, after the grid has refined below `min_grid_frac = 0.03` of domain height. A geometric backstop `tol = 1e-2` applies, and `max_iter = 50`. Optional `seed='grid'` seeds the refinement from competing tangent families "when a single starting circle risks trapping the search in a local minimum". Search-window constraints (`center_box`, `entry_range`, `exit_range`, `tangent_depth`, `min_slip_depth`) reject rather than clamp out-of-window trials. Surfaces are also rejected when |ΣW sin α| < 1% of total weight (`MIN_DRIVING_FRAC = 0.01`, line 39) or when more than 25% of slices are in base tension (`MAX_BASE_TENSION_FRAC = 0.25`, line 44). Basis: source.

**xslope non-circular search** (`search.py:1136`). It is coordinate descent: `movement_distance = 4.0`, `shrink_factor = 0.8`, `fs_tol = 0.001`, `move_tol = 0.1`, `max_iter = 100`, with two geometric guards, `max_base_angle = 65°` and `MAX_KINK_BACK = 10°`. The upstream comment reports, without independent reproduction here, the following: without the kink guard, free searches "took a false minimum in 5 of 20 models … F of 0.28 to 0.77 against circles of 0.99 to 1.50", while "the largest bend in a surface whose methods agree is 7.3 degrees" (James Bay weak-layer surface; Spencer 1.516, Janbu 1.58, Morgenstern–Price 1.53) (`search.py:46-71`). Basis: source (upstream-reported numbers).

**pyBIMstab** analyses user-specified circular surfaces (`CircularSurface(dist1, dist2, radius)`) or A*-optimal tortuous paths through a block-in-matrix grid (`TortuousSurface`). It has no automatic minimum-FS search over circles. Basis: source.

### 4. Convergence and admissibility policies in the open codes

Basis: source (line-cited) + execution where marked.

| code / routine | tolerance, ceiling | on non-convergence | base-normal / pole guard | other refusals |
|---|---|---|---|---|
| PySlope `_analyse_circular_failure_bishop` (`pyslope.py:1709-1731`) | \|F_k − F_{k−1}\| < 0.005, 15 iterations; seed = OMS | **returns the last iterate** (`return float(prev_FS)`, line 1731) with no flag | only `if np.any(denom == 0): return None` (lines 1714-1716) | `driving <= 0 or resisting < 0` → None (line 1723) |
| xslope `bishop` (`solve.py:753`) | 10⁻⁶, 100 iterations; seed 1.0 or Monte Carlo seed | returns `(False, "Bishop method did not converge …")` (line 935) | refuse if min m_α < `FE_MIN_BASE_FACTOR = 0.05` (lines 162, 1571-1579) | refuse if > 50% of base normals in tension (`MAX_BASE_TENSION_EXTENT = 0.5`, line 128) |
| xslope `spencer` (`solve.py:2116`) | 10⁻⁴ residual (scaled below `SPENCER_TOL_REF` for tiny masses), 100 iterations | typed messages: no admissible solution / not converged / inadmissible (lines 43-49) | θ restricted to the pole-free band (lines 1592-1622) | thrust line outside the slice on > 65% of boundaries triggers a band sweep (line 222) |
| xslope `mprice` (`solve.py:3398`) | hybr 2-D Newton on scaled residuals, then a 61-point λ grid with Brent's method on λ ∈ [−1.5, 1.5]; crossing nearest λ = 0 (lines 3470-3491) | `"Morgenstern-Price: no F_f/F_m crossing found in λ ∈ [-1.5, 1.5]."` | base tension by extent only | — |
| pyBIMstab `getFm`/`getFf` (`slopestabl.py:333-490`) | intended tol 10⁻³, 50 iterations, seed FS = 1; λ ∈ [−0.6, 0.6], 10 points + 0 | flag computed by the expression below | none | ratio > 1.5 between successive λ solutions sets flag False (lines 631-632, 648-649) |

**PySlope's silent non-convergence did not change results materially in these probes.** On 18 circles, the default policy (15 iterations, 0.005) differed from a converged solution (1 000 iterations, 10⁻⁹) by at most 3.0 × 10⁻⁴ (`pyslope_probe.txt`, P3 and P4b). None of the 21 circles whose minimum m_α was computed (the toy critical circle and the P4/P4b circles) had m_α < 0.2. m_α was not computed for every candidate in the PySlope searches. The absence of a guard is therefore a source-level fact whose consequence was not exercised here (Boundaries). Basis: execution + source.

**pyBIMstab convergence bookkeeping** (`eamontoyaa/pyBIMstab@ca13d23379c60453e1df53c6d3849902e3c600e0`). Lines 409 and 487 of `pybimstab/slopestabl.py`, verbatim:

```python
            if i > 5 and all((fs[-1] - fs[-2], fs[-2] - fs[-3])) <= self.tol:
```

In Python, `all(...)` returns a `bool`, and `True <= 1e-3` is `False` while `False <= 1e-3` is `True`. The flag is therefore set only when one of the last two successive differences is exactly `0.0`. A sequence converged to 10⁻⁹ is reported as not converged (`pybimstab_expr_probe.txt`). The loop runs the full `maxIter = 50` unless an exact floating-point fixed point occurs. The docstring example's `(2.0741545445738296, True)` is consistent with that, but it was not executed here.

Line 657, verbatim:

```python
            idx2interp = np.where(tolM and tolF)
```

Python's `and` on two non-empty lists returns the second list, so the λ points kept for the spline intersection are selected by the force-equilibrium flags alone, and the moment flags are discarded. The probe gives `[True, False, False, True] and [False, True, True, True]` → `[False, True, True, True]`; an element-wise AND would give `[False, False, False, True]`. Basis: source + execution (expression semantics in CPython, not pyBIMstab itself).

### 5. Strength reduction: definitions of failure and measured sensitivity

**Definition of the reduced strengths.** Program 6.4 (`subordinates/Material-Non-linearity/p64.f90`) sets `phif=ATAN(tnph/srf(iy))` (lines 101, 129), `psif=ATAN(tnps/srf(iy))` (line 132; the dilation angle is reduced too) and `cf=prop(2,etype(iel))/srf(iy)` (line 133). xslope's comment reads "Apply strength reduction (Griffiths & Lane 1999): c_r = c/F, phi_r = atan(tan(phi)/F)", and it reduces soil strength only, not reinforcement (`fem.py:7347-7370`). The FS is the SRF at which the numerical criterion first declares failure. Basis: source.

**Program 6.4's criterion.** A trial is converged when `MAXVAL(ABS(loads-oldlds))/MAXVAL(ABS(loads))<=tol` (`main/checon.f90:12`), with `loads` holding nodal displacements. It fails when `iters==limit` (`p64.f90:123, 174, 177`). The trial loop exits at the first failing SRF.

**Port defect.** In the port, `argv` (declared `CHARACTER(LEN=15)::argv,…`, `p64.f90:20`) and `nlen` (declared in the `INTEGER::` list, `p64.f90:14`) are never assigned before `CALL mesh(g_coord,g_num,argv,nlen,12)` (`p64.f90:61`). That routine executes `OPEN(ips,FILE=argv(1:nlen)//'.msh')` (`main/mesh.f90:15`), which reads undefined values. The probe build inserts `argv='p64'; nlen=3` before the first `OPEN`. With that change, the published input reproduces the repository's `p64.res` exactly: SRF 1.00/1.20/1.40/1.50/1.55/1.60 → 10/17/33/67/244/500 iterations. Basis: source + execution.

**Measured sensitivity** (`support/outputs/ssrm_p64_sweep.txt`). The SRF grid is 1.00, then 1.50–1.65 in steps of 0.01.

| mesh (elements) | tol | ceiling | last converged SRF | first failed SRF | iterations at last converged | wall s |
|---|---|---|---|---|---|---|
| 20/10/10/5 (2 120 eq.) | 10⁻⁴ | 250 | 1.55 | 1.56 | 244 | 1.57 |
| same | 10⁻⁴ | 500 | 1.56 | 1.57 | 327 | 2.05 |
| same | 10⁻⁴ | 1 000 / 2 000 / 5 000 | 1.57 | 1.58 | 935 | 3.78 / 4.75 / 8.36 |
| same | 10⁻³ | 250 | 1.59 | 1.60 | 129 | 1.01 |
| same | 10⁻³ | 500 | 1.60 | 1.61 | 307 | 1.96 |
| same | 10⁻³ | ≥ 1 000 | 1.65 | none ≤ 1.65 | 893 | 5.4–5.9 |
| 40/20/20/10 (8 440 eq.) | 10⁻⁴ | 250 | 1.53 | 1.54 | 165 | 5.11 |
| same | 10⁻⁴ | 500 / 1 000 | 1.55 | 1.56 | 493 | 11.56 / 16.78 |
| same | 10⁻⁴ | 2 000 | 1.56 | 1.57 | 1 015 | 28.07 |
| same | 10⁻⁴ | 5 000 | 1.57 | 1.58 | 3 393 | 73.74 |
| same | 10⁻³ | ≥ 1 000 | 1.65 | none ≤ 1.65 | 900 | 35–45 |

**False convergence under steady flow** (`ssrm_p64_false_convergence.txt`).

- With tol = 10⁻³ and ceiling 5 000, trials at SRF 1.7–4.0 all "converge" at 948–1 001 iterations, with max displacement rising from 0.209 m to 6.0 m.
- With ceiling 1 000, SRF 2.80 reaches the ceiling and becomes the reported failure.
- With tol = 10⁻⁴ and ceiling 30 000, SRF 1.7, 2.0 and 3.0 "converge" at 9 936, 9 948 and 9 978 iterations, with max displacement 2.07, 11.3 and 40.9 m (41.6 s wall).
- The iteration counts saturate at ≈ 1/tol, as the derived argument predicts: Δu ≈ const per pseudo-time step during flow, so max|Δu|/max|u| ≈ 1/n.
- The non-convergence criterion is valid only when the ceiling satisfies limit ≪ 1/tol. Inside that regime the reported FS still drifts with the ceiling, by 1.55 → 1.57 (coarse mesh) and 1.53 → 1.57 (fine mesh) over 250 → 5 000 iterations.

Basis: execution + derived.

**How xslope addresses it** (source; not executed). `solve_fem` requires both CHECON-style convergence (tolerance 10⁻³) and "the maximum over all nodes of the nodal out-of-balance force, each normalized by that node's own gravitational body force, is below `force_tol`" ("the criterion of Dawson, Roth & Drescher", `fem.py:6694-6704`). Its documentation of the tolerance states "so steady benign viscoplastic creep is accepted as converged; false convergence at true failure is guarded by max_disp_factor below" (lines 6794-6801; displacement cap 0.1 × mesh height). `solve_ssrm` bisects to `tolerance = 0.01` and reports the bracket midpoint (line 15643). Its default `failure_criterion="hybrid"` additionally requires "displacement evidence of failure: max|u| beyond the trial's own elastic scale AND still growing" before counting a non-converged trial as failed (lines 15728-15736). The upstream comment reports that over 103 FEM benchmarks the switch "moved 4 rows and NO row downward" (lines 15737-15742; not reproduced). Per-trial budgets are 12 000 iterations, extended while improving up to a 50 000 ceiling, beyond which a trial is "inconclusive" and the FS is reported as a lower bound (lines 15700-15710). xslope also documents that "the Mohr-Coulomb limit assumes ASSOCIATED flow, while XSLOPE runs psi = 0" (`fem.py:4154`).

**LEM versus strength reduction on the same slope** (Basis: execution + derived). Upstream PySlope gives a minimum Bishop FS of 1.588–1.605, depending on search, and the toy rigorous methods give 1.591 on the toy critical circle. Program 6.4's brackets are [1.53, 1.58] for tol = 10⁻⁴. The strength-reduction value is lower than Bishop by about 0.5–5% on this geometry, depending on mesh, ceiling and which search result is taken.

**Published comparisons disagree in sign** (Basis: documentation):

- Bojorque, De Roeck & Maertens (2008) summarise Cheng et al. (2007): "for most of the cases the FOS obtained by SRM are slightly larger than those obtained by LEM".
- Re-running the cases in PLAXIS, the discussers found "for all of the cases the FOS values are lower than those obtained by the authors' method, and for most of the cases slightly lower than LEM", with "differences range from 1% to 21.5%". They attribute these to "the type of nonlinear solution algorithm".
- The discussers also report that tension cut-off and flow rule move the FS, and that "for the cases where φ = 0°, SRM produced a very deep seated slip surface affected by the boundaries".
- The Mount Polley panel's PLAXIS strength reduction of the Upper GLU collapsed at s_u/σ′_v = 0.29, against 0.27 from 2D Morgenstern–Price limit equilibrium on the same section and boundary conditions (report §6.2.1–6.2.2).

### 6. The limits of limit equilibrium, as stated by the code developer and the panels

Krahn (2003) identifies "the fundamental shortcoming of limit equilibrium methods, which only satisfy equations of statics", as "that they do not consider strain and displacement compatibility". He proposes "finite element computed stresses inside a conventional limit equilibrium framework" (abstract). Griffiths & Lane (1999) argue that in strength-reduction FEM failure "occurs 'naturally' through the zones in which the shear strength of the soil is insufficient", with "fewer a priori assumptions, especially, regarding the failure mechanism" (abstract). Basis: documentation (abstracts only).

The three panel reports give the field form of this limitation:

| facility (failure date) | mechanism (panel) | material behaviour | analyses before failure | reconstruction |
|---|---|---|---|---|
| Mount Polley perimeter embankment (2014-08-04) | "undrained failure of the Upper GLU under the imposed load" (§6.4) | glaciolacustrine clay normally consolidated under embankment load; contractive; strain-weakening; sensitivity 1–3 | design criterion FS ≥ 1.3; ESA values 1.43, 1.67, 1.4, 1.31. At Section D near the breach "the critical failure surface did not reach the GLU … producing a much higher factor of safety of 1.77" (§5.4). "The design never incorporated an undrained strength analysis (USA), except in one instance" (Stage 6, FS 1.1, not pursued) | 2D Morgenstern–Price (SLOPE/W): ratio 0.27 (high water table) / 0.22 (low) at FS = 1. PLAXIS collapse at 0.29. 3D LEM (SVSlope 3D, Morgenstern–Price, entry–exit, aspect ratio 2.6): FS 1.288 at 0.27 and ≈ 1.1 at a strain-weakened 0.13. Progressive failure "embedded in the back-calculated average resistance" (§6.2–6.3) |
| Fundão (2015-11-05) | liquefaction flowslide triggered by lateral extrusion of slimes beneath the setback | loose saturated sands; mean undrained strength ratio 0.21 (yield) → 0.07 (critical) from CPT correlations (§4.2, Fig. 4-6) | right-abutment ESA (φ′ 35°/5 kPa compacted, 33°/0 hydraulic) and USA (ratio 0.25) presented in §5.3.2 | "liquefaction would be initiated by lateral extrusion prior to the development of shear failure"; the shear mechanism "does not take into account additional three dimensional resistance, which will be substantial" (§6.6, §6.1); earthquakes about 90 minutes earlier added "a small additional increment of loading" |
| Feijão Dam I (2019-01-25) | flow (static) liquefaction; failure complete in under 10 s; 9.7 Mm³ (≈ 75% of stored tailings) released in under 5 min | heavy, bonded (iron-oxide) tailings, stiff but brittle; strain to peak < 1% | "undrained conditions were considered in stability calculations for the Fifth Raising onwards" (§4.1.2). LEM "that used an undrained strength ratio of s_u/σ′_vo = 0.26 calculated an FS close to 1.0" (§8.2) | peak undrained re-analysis "resulted in a FS close to 1.5. However, this ignores possible regions of high shear stress where the local FS can be less than 1.0". "In conditions where a significant portion of the materials … have a potential for significant strength loss, the results of LEM can be misleading" (§8.2). Trigger: creep plus a suction-loss strength reduction of up to 15 kPa (3D deformation analyses) |

Basis: documentation.

**What the panel evidence does not say.** None of the three reports attributes a failure to a defect in limit-equilibrium software or to the choice among Bishop, Spencer and Morgenstern–Price. Every reconstruction turns on the strength model (drained vs undrained, peak vs post-peak) and on whether site characterization found the controlling layer. The FS spreads measured in §§2–5 (≈ 0.2–5%) are an order of magnitude smaller than the effect of choosing the drained or the undrained strength model, as at Mount Polley Stage 6: ESA 1.4 versus USA 1.1. Basis: derived.

**Cross-failure synthesis.** Santamarina, Torres-Cruz & Bachus (2019) summarise in their standfirst: "Knowledge gaps and management shortcomings contribute to catastrophic dam failures". Their body text was not retrievable here (Boundaries).

### 7. Reliability formulations for strength uncertainty

Christian, Ladd & Baecher (1994) use a first-order second-moment model F = g(x) + e, with V[F] ≈ Σ(∂g/∂x_i)² V[x_i] + V[e] for uncorrelated inputs, and β = (E[F] − 1)/σ[F] (their Eqs. 8, 10, 13). They split soil-property uncertainty into data scatter (spatial variability plus random testing error) and systematic error (statistical error in the mean plus measurement bias; Fig. 3). Spatial variance is reduced by averaging over the slip-surface length L: "V[τ_avg] = (2r₀/L) V[c_u]", giving reduction ratios of 0.2 (12 m dike) and 0.7 (6 m dike). Model error is added as E[F] × 1.05 with V[e] = (0.07 E[F])². Recomputed from their tabulated components (`support/probes/reliability_recompute.py`):

| case (Christian et al. Table 7) | E[F] | V[F] used | β published | β recomputed | p_f (normal) | lognormal index from the same E, V |
|---|---|---|---|---|---|---|
| single stage, H = 6 m | 1.500 | 0.074 | 1.84 | 1.84 | 3.3 × 10⁻² | 2.16 |
| single stage, H = 12 m | 1.453 | 0.029 | 2.66 | 2.66 | 3.9 × 10⁻³ | 3.15 |
| multistage, H = 23 m | 1.427 | 0.0134 | 3.69 | 3.69 | 1.1 × 10⁻⁴ | 4.35 |
| H = 12 m, spatial variance **not** averaged | 1.453 | 0.0658 | — | 1.77 | 3.9 × 10⁻² | 2.05 |

With model error, the recomputed indices are 1.96 / 2.62 / 3.19 against the published 1.96 / 2.60 / 3.19; the 0.02 gap is rounding of tabulated variances. The paper's conclusions include that "attempts to determine the absolute probability of failure are much less successful" and that reliability analysis is "especially useful in establishing design values of factors of safety representing consistent risks for different types of failure" (abstract). Basis: documentation + derived.

**xslope's Taylor Series Probability Method** (`reliability.py:183`, `629-660`) runs 1 + 2N searches (the most likely values, then each parameter at ±σ). It computes σ_F = √Σ(ΔF_i/2)², COV_F = σ_F/F_MLV, and β_ln = ln(F/√(1+COV²))/√ln(1+COV²) (line 637). It neither averages spatially nor carries a model-error term. A source comment warns that a perturbation that "jumps to a competing minimum contributes its FAMILY GAP to the variance and is read as sensitivity to the parameter" (lines 250-256), and it therefore applies one search window to all 1 + 2N searches. Other engines are Monte Carlo on a fixed surface (`MC_DEFAULT_SAMPLES = 10000`, seed 20240117, normal or lognormal inputs) and a quadratic response surface gated on held-out real solves (`reliability_rs`). To reproduce Christian et al. one must treat as random the field-vane strength profile (two clay layers), crust depth, depth to till and fill density and friction. Spatial and systematic parts must be separated, and the averaging ratio applied to the spatial part. PySlope and pyBIMstab have no reliability module. xslope's `reliability.py` contains no autocorrelation, correlation-length or random-field term (grep at the pinned revision), so none of the three codes can apply Christian et al.'s averaging step directly. Basis: source + derived.

### 8. The industry standard and what can be checked from analysis outputs

The GISTM primary text could not be retrieved. Wording here comes from secondary reproductions, and its accuracy is a Boundary. Requirement 4.6, as reproduced: "Identify and address brittle failure modes with conservative design criteria, independent of trigger mechanisms, to minimise their impact on the performance of the tailings facility." Secondary sources also describe a consequence classification (Annex 2) whose highest class carries external-loading criteria at an annual exceedance probability of 1/10 000, an Engineer of Record, and independent review. Basis: documentation (secondary).

| requirement theme | checkable from analysis outputs? | depends on site characterization? | evidence from this report |
|---|---|---|---|
| brittle failure modes addressed independent of trigger (4.6) | partly: whether undrained/post-peak strengths were analysed, and the minimum FS under them | yes: identifying contractive, bonded or sensitive layers | Mount Polley (layer missed; one USA ignored); Feijão (peak vs liquefied strengths: FS ≈ 1.5 vs ≈ 1.0) |
| critical-surface coverage | yes: search window, minima per surface family, refusals | yes: layer continuity | Mount Polley Section D surface never reached the GLU (FS 1.77); xslope reports unsolved trials per kind |
| numerical adequacy of FS | yes: method, convergence flags, m_α, base tension, SSR criterion, mesh/ceiling sensitivity | no | §§4–5 |
| probability/reliability statements | yes, if variance components and averaging are reported | yes: autocorrelation, bias | §7 |
| consequence classification and external loading | no (inundation and hazard analyses) | yes | not examined |

### 9. Performance and resource footprint (L1–L6)

Host for measured rows: the VM described in Applicability. Single runs.

| level | quantity | value | basis |
|---|---|---|---|
| L1 authoring | source size (lines) at the pinned revisions | PySlope `pyslope.py` 2 925. xslope `solve.py` 3 722, `search.py` 1 910, `slice.py` 3 007, `reliability.py` 2 017, `fem.py` 19 010. pyBIMstab `slopestabl.py` 924, `slipsurface.py` 709, `slices.py` 782. `p64.f90` 182 | measured (`wc -l`) |
| L1 | person-months, LLM-token budgets, repair cost per change | not measured | — |
| L2 build | program 6.4 + 98-file library, gfortran -O2, sequential | 14.29 s wall, 206 320 kB peak RSS | measured |
| L2 | Python package install/build times | not measured | — |
| L3 single-surface solve latency | PySlope Bishop, 25–50 slices, incl. geometry | 3 749–4 893 circles/s (0.20–0.27 ms per circle) | measured (P2) |
| L3 | toy Bishop in pure Python, 50 slices | 43 495 circles in 5.92 s (0.136 ms per circle) | measured (toy) |
| L3 | toy Spencer + Morgenstern–Price on one circle (scan-based root finding) | 8.25 s | measured (toy; not representative of production solvers) |
| L3 | xslope solver latency | not measured; upstream comment: band sweep "costs about a hundred times what the cascade does" (`solve.py:198-200`) | source |
| L4 analysis execution | program 6.4, published example (6 trials) | 1.03 s (2 120 eq.); 9.51 s (8 440 eq.) | measured |
| L4 | program 6.4, 17-trial sweep, fine mesh, ceiling 5 000 | 73.74 s | measured |
| L4 | PySlope full search, 10 000 candidates | 2.31–2.62 s | measured |
| L5 independent re-check | toy Bishop vs PySlope on identical circles | max relative difference 2.0 × 10⁻¹⁴ over 13 circles | measured |
| L5 | independent re-check of FEM strength-reduction results | not measured | — |
| L6 memory/disk | program 6.4 peak RSS | 3 892 kB (coarse), 11 840 kB (fine), 3 916 kB (30 000-iteration run) | measured |
| L6 | program 6.4 skyline matrix | 151 000 / 1 175 290 reals → 1.21 / 9.40 MB at 8 B per real | derived from program output |
| L6 | program 6.4 binary | 418 816 bytes | measured |
| L6 | PySlope probe process peak RSS (interpreter + NumPy) | 33 608 kB | measured |
| L6 | energy/power | not measured | — |

### 10. Human comprehensibility and model refinement (C1–C2)

**C1, working memory and legibility.**

- A slice-method FS asks a reviewer to hold 5–7 interacting choices: equilibrium set, interslice function, search family and window, convergence tolerance, admissibility guards, and strength model with its pore-pressure field. The output is a single scalar that records none of them.
- PySlope's silent last-iterate return and pyBIMstab's flag expression are invisible at the call site. A human reading "converged" or a bare FS cannot tell what was checked.
- xslope instead returns typed refusals ("no admissible solution", "not converged", "inadmissible") and keeps them distinct. Its comment explains that an earlier fallback "turned Morgenstern-Price's no-crossing condition … into a fabricated report of iterations running out" (`solve.py:92-96`). That design trades code size (about 29 700 lines in the five xslope files listed in §9) for legibility of failure reasons.
- In strength reduction, the reported FS hides tol, ceiling, mesh, flow rule and the definition of failure. §5 shows that each moves the answer.

**C2, simplicity and orthogonality.**

- The GLE closure X = λ f(x) E (plus the moment- and force-equilibrium residuals) makes Bishop (λ = 0, moment), Spencer (f = 1) and Morgenstern–Price (f general) ordinary cases of one model, not separate algorithms. xslope and the toy model both exploit this, and xslope regression-checks `mprice(f=1)` against `spencer`.
- The genuinely separate invariants are:
  1. statics, the equilibrium set;
  2. the interslice closure;
  3. the strength law, including its drained/undrained state and post-peak behaviour;
  4. surface admissibility, covering the m_α / pole band, base tension and geometry guards;
  5. search completeness.
- The panel evidence locates catastrophic error in invariant 3 and in the site model feeding it, not in 1 or 2.
- A refinement that keeps these orthogonal is to report FS as a tuple of (method, surface family and search certificate, strength state, admissibility margins) rather than a scalar. That would add no new mechanism; it would surface choices that already exist.
- Strength reduction is not a different invariant. It shares invariant 3 and replaces 1–2 with continuum equilibrium plus a numerical failure definition, which then needs its own admissibility rule: the force-balance and displacement-growth tests.

### 11. Validation of implementations and claims (V1–V4)

- **V1, specification adequacy and non-vacuity.**
  - PySlope's validation tests (`pyslope/tests/test_validation_examples.py`) assert < 1% difference from Slide on prescribed circles for examples a–e. They do not exercise the search.
  - Tests f and g only `assert s.get_min_FOS()`, which passes for any non-zero FS. That is a near-vacuous oracle.
  - The comment above example c reads "for c the results of 500 slices in slide used to be closer to the true value since the difference was too high to pass the test". The reference values were adjusted.
  - xslope's comments cite corpus A/B measurements (570 Bishop/Janbu solves; 103 FEM benchmarks; 5 251 Spencer/Morgenstern–Price search trials, 665 disagreeing by more than 1%). These were not reproduced. Spec-mutation or mutant-kill rates: not measured.
- **V2, differential testing.**
  - Toy vs PySlope Bishop: agreement to 10⁻¹⁴.
  - Method differential on a fixed circle: 0.2% between rigorous methods and Bishop, 5% for Bishop vs OMS.
  - LEM vs strength reduction: 0.5–5%.
  - Strength reduction vs strength reduction across implementations: 1–21.5% (Bojorque et al. vs Cheng et al.).
  - xslope uses Spencer vs Morgenstern–Price (f = 1) as an internal differential and notes that a lost pore-pressure field "moves every method together", so that cross-check could not catch it (`solve.py:3528-3548`).
- **V3, physical gaps outside the rigid-plastic model.**
  - Progressive failure (Mount Polley), creep rupture (Feijão), lateral extrusion of soft slimes (Fundão) and three-dimensional end restraint (Mount Polley 2D 1.0 vs 3D 1.29 at the same strength) are outside both 2D limit-equilibrium and the 2D strength-reduction codes examined.
  - The panels used deformation analyses (PLAXIS, 3D) and laboratory element tests to cross these gaps.
  - Software concurrency, crash consistency and side channels are not relevant to these codes.
- **V4, field telemetry and operator mental models.**
  - Feijão was monitored by survey monuments, inclinometers, ground radar and piezometers. "None of these methods detected any significant deformations or changes prior to failure". Post-failure satellite analysis found downward deformations of less than 36 mm/year.
  - Mount Polley collapsed "without any apparent warning" (§6.3.2).
  - Acceptance criteria are themselves interpretive: the regulator's 2012 letter, quoted in the Mount Polley report, debates whether 1.3 or 1.5 applies under the Dam Safety Guidelines and accepts 1.3 "only in conjunction with the Observational Method" (§5.4).
  - Real-incident replay of analyses against monitoring records was not examined.

## Boundaries

- **Not examined.** The full texts of Bishop 1955, Spencer 1967, Morgenstern–Price 1965, Fredlund–Krahn 1977, Zhu et al. 2003, Krahn 2003, Griffiths–Lane 1999, Dawson et al. 1999, Duncan 1996 (10.1061/(ASCE)0733-9410(1996)122:7(577)) and Cheng et al. 2007. Claims attributed to them are limited to abstracts or to statements in other examined documents. The specific benchmark slopes and numerical results inside Griffiths–Lane, Dawson et al., Cheng et al. and Duncan were not extracted.
- **Not examined.** Santamarina et al. 2019 beyond its standfirst. No common-cause statistics from that paper are reported here, and secondary quotations circulating online were not verified against it.
- **Unknown.** The exact GISTM wording. The primary PDF could not be retrieved through the available fetch services. Requirement 4.6 is quoted from a secondary reproduction; the 1/10 000 AEP criterion and the governance roles come from secondary summaries.
- **Not examined.** xslope was not executed. All xslope statements are source-level, and all numbers in its comments are upstream-reported and not reproduced. pyBIMstab was not executed. Its flag defects are established from source and Python semantics; their effect on FS values in real runs is **unknown**.
- **Not exercised.** PySlope's missing m_α guard. None of the 21 circles whose m_α was computed had m_α < 0.2, so the attractive conclusion that PySlope returns wrong FS values near the m_α singularity is **unsupported** by this evidence.
- **Toy model.** `toy_lem.py` results (OMS/Bishop/Spencer/Morgenstern–Price on one circle) characterise those equations on one dry, homogeneous, circular case. They are not properties of any product. The rigorous-vs-Bishop gap of about 0.2% is **known not to apply** to non-circular surfaces in general: xslope's comments report Spencer at 0.42–1.05 × Bishop on circles and 0.82–1.71 × Janbu off circles across its corpus.
- **Single geometry.** Strength-reduction sensitivities (§5) are for one slope, ψ = 0 and Mohr–Coulomb with no tension cut-off, in one textbook program with one patch. Other strength-reduction implementations (xslope, PLAXIS, FLAC, RS2) use different criteria and were not run. The ≈ 1/tol saturation is a property of the relative-displacement test, but its practical impact depends on each code's ceiling and on any additional criteria.
- **Not examined.** Three-dimensional analysis, seismic and dynamic loading, and unsaturated strength beyond what the panel reports state.
- **Not examined.** Liquefaction-triggering assessment, a separate topic with its own corpus coverage.
- **Unsupported.** "Strength reduction is always more conservative than limit equilibrium", in either direction. The measured case and the two published studies disagree in sign.
- **Unsupported.** "A higher FS means a safer facility": Christian et al.'s James Bay indices invert that ranking.

## Evidence

All observations were made on 2026-11-21 (UTC).

**Upstream source (path:line at the pinned revision).**

- `JesseBonanno/PySlope@d6167796769743e069ec540588193216753b678f`: `pyslope/pyslope.py:287-293` (constructor defaults), `1015-1081` (entry–exit lattice), `1083-1169` (radii), `1232-1259` (analyse), `1261-1504` (OMS), `1506-1731` (Bishop; silent return at 1731; `denom == 0` at 1714-1716); `README.md:141`; `pyslope/tests/test_validation_examples.py`; `pyslope/examples/{summary_results,search,slices}.xlsx`. The SHA-256 of `pyslope/pyslope.py` is `ce9599079428bfa20a07f385995d4d8ef561ac3e75cac08e44e9b8f46c76493a`.
- `njones61/xslope@28f16877a9c204ed421d3e2d6e353609ec8d0c8b`: `xslope/solve.py:28-242` (failure taxonomy and guard constants), `753-935` (`bishop`), `1538-1589` (`_base_normal_admissibility`), `1592-1622` (`spencer_theta_bounds`), `2116` (`spencer`), `3398-3622` (`mprice`); `xslope/search.py:39-72`, `660-743`, `1136-1190`; `xslope/fem.py:4050-4066`, `4150-4157`, `6664-6801`, `7347-7370`, `15591-15760`; `xslope/reliability.py:183-260`, `629-660`, `818`. SHA-256: `solve.py` `7788b63252b08cef9b4977f1449e949a91e253579acb0e9f6e8d7b8800a1144d`, `fem.py` `4a31b919f0540d2160a495528b082218ec38ef6a8d1c66829e587b19b89c687a`.
- `eamontoyaa/pyBIMstab@ca13d23379c60453e1df53c6d3849902e3c600e0`: `pybimstab/slopestabl.py:14-49` (defaults), `333-412` (`getFm`), `414-490` (`getFf`), `409`, `487`, `556`, `575-680` (`iterateGLE`; filter at 657); `setup.py` (version 0.1.4).
- `cunyizju/Programming-FEM-5th-Fortran@bf19e8a773c2a9f0a9a10f304540efdf586955f1` (archive SHA-256 `923a2c82bdd66c7a1004283221739aa581694b8085c5ee6ae0524d4fe3d4a901`): `subordinates/Material-Non-linearity/p64.f90:14, 20, 61, 92-133, 174-177`; `main/checon.f90:12`; `main/mesh.f90:15`; `subordinates/Material-Non-linearity/p64.dat`, `p64.res`.

**Literature (DOIs verified against Crossref metadata for title, authors, venue, volume, issue, pages and year).** 10.1680/geot.1955.5.1.7; 10.1680/geot.1965.15.1.79; 10.1680/geot.1967.17.1.11; 10.1139/t77-045; 10.1680/geot.2003.53.4.377; 10.1139/t03-024; 10.1680/geot.1999.49.3.387; 10.1680/geot.1999.49.6.835; 10.1016/j.compgeo.2006.10.011; 10.1016/j.compgeo.2007.04.005; 10.1061/(ASCE)0733-9410(1994)120:12(2180); 10.1061/(ASCE)0733-9410(1996)122:7(577); 10.1126/science.aax1927. Abstracts were read from Crossref where deposited. Christian et al. 1994 was read in full from an author-hosted copy, and the Bojorque et al. discussion from a university repository copy. Also verified but not used beyond citation: 10.1061/(ASCE)1090-0241(2000)126:4(307) (Duncan 2000), 10.1061/(ASCE)1090-0241(2004)130:5(507) (Griffiths & Fenton 2004) and 10.3208/sandf1972.32.59 (Matsui & San 1992).

**Panel reports.** Mount Polley (2015-01-30; Executive Summary, §§5.4, 6.2.1–6.2.3, 6.3.2–6.3.3, 6.4). Fundão (2016-08-25; Executive Summary, §§4.2, 5.3.2, 6.1, 6.6; read from a mirror, because the panel's own host was not retrievable). Feijão Dam I (2019-12-12; Executive Summary, §§4.1.2, 8.2–8.3). All three were text-extracted by a fetch service. Section numbers refer to the reports' own numbering, and no PDF hashes were recorded.

**Execution.** Scripts are in `support/probes/` and raw outputs in `support/outputs/` (see `support/README.md` for exact commands and host). Key outputs are `ssrm_p64_sweep.txt`, `ssrm_p64_false_convergence.txt`, `pyslope_probe.txt`, `toy_lem_grid_search.txt`, `reliability_recompute.txt` and `pybimstab_expr_probe.txt`.

## Revalidation

- **PySlope behaviour at a new revision.** Diff `_analyse_circular_failure_bishop` and `_set_entry_exit_planes`, then rerun `PYTHONPATH=. python3 pyslope_probe.py p1 p2 p3`. P1 must reproduce 1.2704/2.1777/3.9004/5.7184. Compare P2's minimum FS per `iterations` value with the table in §3, and check whether line 1731's `return float(prev_FS)` still exists.
- **pyBIMstab flags.** `grep -n "all((fs\[-1\]" pybimstab/slopestabl.py` and `grep -n "tolM and tolF"`. If either line is present unchanged, §4's conclusion holds. Run `pybimstab_expr_probe.py` to restate the semantics.
- **xslope policies.** Grep the constants `FE_MIN_BASE_FACTOR`, `MAX_BASE_TENSION_EXTENT`, `MIN_DRIVING_FRAC`, `MAX_BASE_TENSION_FRAC`, `MAX_KINK_BACK`, the `mprice` λ window `lo, hi = -1.5, 1.5`, and `failure_criterion="hybrid"` in `solve_ssrm`. Changes there change §4–5 directly. Running xslope on the program-6.4 slope (it ships Griffiths & Lane benchmark builders under `benchmarks/`) would convert its source-level claims into measurements.
- **Strength-reduction false convergence in any code.** Run trials at SRF ≫ FS (for example 2–3 × the expected FS) with the iteration ceiling raised above 1/tol. A code relying only on a relative-displacement test will report convergence at about 1/tol iterations while the displacement grows without bound. Reproduce with `big.dat` (in `ssrm_p64_false_convergence.txt`) in about 42 s.
- **Reliability arithmetic.** `python3 reliability_recompute.py` must print 1.84 / 2.66 / 3.69. Any change in the published variance components (errata) would show up there.
- **Panel and standard claims.** Re-read the cited sections. For GISTM, obtain the primary PDF and replace the secondary wording in §8. That is the one claim group in this report not yet grounded in a primary text.
