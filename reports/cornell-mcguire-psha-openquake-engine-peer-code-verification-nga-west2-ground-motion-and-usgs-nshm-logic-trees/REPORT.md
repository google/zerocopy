# Probabilistic seismic hazard codes: the Cornell–McGuire integral in OpenQuake, nshmp-haz and OpenSHA, the PEER code-verification exercises, NGA-West2 model verification, and logic-tree aggregation

## Summary

- **One algebra, three internal currencies.** All three open codes examined compute the Cornell (1968) / McGuire hazard integral under a Poisson occurrence model, `P(IM > x in T) = 1 − exp(−T · Σ_ruptures λ_r · P(IM > x | rupture r))`, but they carry different intermediate quantities. OpenQuake accumulates per-rupture probabilities of *no* exceedance `exp(−λ_r·T·poe)` (`tom.py`) and finally combines source groups through rate maps; OpenSHA multiplies `(1 − q_r)^{poe}` per rupture, where `q_r` is the rupture's probability over the time span; nshmp-haz sums annual-rate curves `λ_r · poe` and stays in rate units. These forms are algebraically identical for independent Poisson ruptures. They diverge only when quantities that are not additive (probabilities) are averaged or summed. *Basis: source (all three) + derived.*
- **What "mean hazard" means depends on a flag.** PEER 2018/03 Test 3.2 found that 7 of 9 codes averaged weighted *rates* across logic-tree branches and then converted to probability, and called this "not correct" when Poisson probabilities are requested. The maximum effect was about 9% at 0.001 g. OpenQuake's default (`use_rates = false`) averages per-branch probabilities, which is the PEER-recommended scheme. `use_rates = true` averages rates, and the engine logs `You should set use_rates=true` when only the mean is requested and the flag is off. nshmp-haz weights rate curves. On a synthetic three-branch tree, OpenQuake's two modes differed by +13.5% at a level where branch rates span 0.05–0.8/yr and by +0.15% near 3.5×10⁻³/yr. *Basis: documentation (PEER 2018/03 §4.3) + source + execution (OpenQuake functions on synthetic input).*
- **Fractiles use linear, not log, interpolation in OpenQuake.** `stats.quantile_curve` interpolates hazard *linearly* against cumulative branch weight. PEER 2018/03 states that interpolation "should be linear on the cumulative weights and log on the hazard". For a 3-branch example the OpenQuake median was 25% above the log-interpolated value. The report expects the difference to be negligible for trees with thousands of branches. *Basis: source + execution + documentation.*
- **Ground-motion truncation.** OpenQuake's truncated-normal survival function renormalizes over both tails (`(Φ(b) − Φ(x)) / (2Φ(b) − 1)`). This is the PEER 2018/03 group consensus ("truncation should be performed on both ends"), which only 4 of 15 codes initially followed. nshmp-haz exposes both `TRUNCATION_UPPER_ONLY` and `TRUNCATION_LOWER_UPPER`. At a 2σ truncation the upper-only form is 2.33% lower across the body of the distribution. *Basis: source + execution.*
- **PEER benchmarks and their encoding.** PEER 2010/106 had 8 participating codes, set a minimum standard of about 10% in probability, and reached consensus only on Set 1. PEER 2018/03 had 15 codes (OpenQuake, OpenSHA, CRISIS, HAZ45 and others) and defined benchmarks as the mean of the 5 best-agreeing independent "core" codes, with a ±5% acceptance band on hazard. Its Set 3 tests have no benchmark, only groups of codes that share an approach. The pinned OpenQuake acceptance suite encodes only 2010 Set 1 cases 2, 5, 10 and 11, plus a non-parametric variant of case 2. It uses σ = 0, a 10 km area discretization for cases 10/11 (the PEER instruction is a 1 km grid), `rtol = 0.1`, and `atol` between 2×10⁻⁵ and 3×10⁻³. Its case 10/11 magnitude–frequency distribution (`a = 3.1`) yields 0.0380 events/yr for M ≥ 5, against the specified 0.0395, which puts the lowest-level probability 3.6% low. The tolerance hides this. At the encoded 10 km spacing, benchmark PoEs near 2×10⁻⁵ are missed by up to 89% and still pass. At the PEER 1 km grid and at 0.5 km, the worst errors are 6.8% and 6.1%. The PEER-2018-derived QA cases (Test 2.5b, Test 3.1a) compare against outputs that the engine generated itself (`generated_by='OpenQuake engine 3.20.0-…'`). *Basis: documentation + source + execution.*
- **NGA-West2 verification in OpenQuake uses author-supplied tables.** The reference tables come from the model authors' own Matlab, Fortran or Excel tools, or from OpenSHA, at tolerances between 0.001% and 2%. The 34 tests for ASK14, BSSA14, CB14, CY14 and I14 pass at the pinned revision (86 s). Several of those reference artifacts had errors: an ASK14 RY0 error in the PEER NGA-West2 Excel file, CB14 spreadsheet formula errors noted in the test source, and an ASK14 Z1.0 unit typo. *Basis: source + execution + documentation.*
- **Testing against observations is unsettled.** Published work ranges from rejection of the New Zealand model until aftershocks are removed (Stirling–Gerstenberger 2010), to Japanese maps outperformed by uniform or random maps on a fractional-exceedance metric but not on squared misfit (Brooks et al. 2016), to the USGS 2023 model's statement that it is consistent with past ShakeMap intensities (Petersen et al. 2024). Stein et al. (2012) argue that maps fail and should be tested against null models. Hanks et al. (2012) and Frankel (2013) published critical responses to the Stein et al. papers, whose content was not examined beyond titles and abstract openings. *Basis: documentation (abstracts and indexed metadata).*

## Applicability

The repository subjects were read at the pinned revisions in `REPORT.json`. Line numbers below refer to those revisions.

- **OpenQuake engine** at `gem/oq-engine` `d6042c3ad58401d8eb9d8319d9fc0480b3f8f25d` (`openquake.baselib.__version__ = '3.27.0'`). This is the only code that was executed. The pinned source tarball was run under CPython 3.13.15 with numpy 2.5.4, scipy 1.18.1, numba 0.68.1, pandas 2.3.3, h5py 3.16.0, fiona 1.10.1, pyproj 3.8.0 and shapely 2.2.0, installed from PyPI. These versions are not the engine's pinned `requirements-py313-linux64.txt` wheels (`pyproject.toml` asks for `numba~=0.67`). The engine's geospatial import guard says "Only the GEM wheels are tested and guaranteed to work". Execution results therefore show behavior under this dependency set and are not a certification of the supported install.
- **nshmp-haz** at `usgs/nshmp-haz` `35e140b8eb665e35d373dbd4a96d2204ce7f2592` (last commit 2022-12-08). The GitHub repository is archived, and its README states it "has been moved to GitLab: https://code.usgs.gov/ghsc/nshmp/nshmp-haz". Findings apply to this archived snapshot only. The GitLab code used for the 2023 NSHM was **not examined**. No Java code was compiled or run. One function (`Maths.erf`/`normalCcdf`) was ported line for line to Python to measure its accuracy.
- **OpenSHA** at `opensha/opensha` `a0bba0d13f3dbd9ec3a3076a7ccea4491cc41393` was read only (`HazardCurveCalculator.java`).
- **PEER Report 2010/106** and **PEER Report 2018/03** were read as text extracted from the PDFs at the URLs in `REPORT.json`. No DOIs are assigned. The extracted text ends partway through the appendices, so the full benchmark tables and the Excel electronic supplement (Appendix D) were **not examined**.
- The literature subjects were checked through the doi.org handle API and OpenAlex metadata and abstracts, not full texts, except where stated.

The subjects relate as follows. The PEER reports specify tests. OpenQuake and OpenSHA took part in PEER 2018/03 (Table 1.1). OpenQuake's repository encodes a subset of the PEER 2010 tests as acceptance tests. nshmp-haz is the USGS production lineage, and its GitHub snapshot is compared at the source level for algebra and truncation only.

## Findings

### 1. The hazard integral and its discrete form

Cornell (1968) derived the distribution of maximum annual ground motion from point, line and areal sources with Poisson occurrence. McGuire (2008) traces the method's history and defines the PSHA product as an annual frequency of exceedance versus amplitude. Both PEER reports take this as the standard model. PEER 2010/106 §2.2 writes `p(Z > z) = 1 − e^{−ν(z)·t}`, with `ν(z)` the annual rate of events in which Z exceeds z. The discretized form used by every code examined is

```text
ν(x) = Σ_sources Σ_ruptures λ_r · P(ln IM > ln x | M_r, distances_r, site, ε-truncation)
P(x, T) = 1 − exp(−ν(x)·T)        (independent Poisson ruptures)
P(ln IM > ln x | r) = TSF((ln x − μ_r)/σ_r),  TSF = truncated-normal survival function
```

The PEER tests isolate the terms. Single magnitudes, σ = 0 and fixed hypocentres each turn one factor into a delta function. PEER 2018/03 §1.5 warns that this simplified modelling "should not be used outside of the verification test environment". *Basis: normative (test specification) + documentation.*

Two derived checks reproduce PEER Set 1 constants. Test 1.1 has a fault activity rate of 0.0028528/yr, and `1 − e^{−0.0028528} = 0.0028487`, which matches the report's Poisson probability. For the OpenQuake encoding of 2010 Set 1 Case 2, the comment in `_peer_test_data.py` lines 187–206 derives the rate from moment balance as `M0_rate = 3e10 · 25e3 · 12e3 · 2e-3 = 1.8e16 N·m/yr` and `a_inc = log10(M0_rate) − (1.5 + b)·M − 9.05` with `b = −0.9` and `M = 6.0`. That gives `10^(3.6053 − 5.4) = 0.016043/yr` (line 208 stores `0.0160425168864`), and `1 − e^{−0.0160425} = 0.01591`, the tabulated `1.59E-02`. *Basis: derived.*

### 2. How the three codes implement it

| Aspect | OpenQuake `d6042c3a` | OpenSHA `a0bba0d1` | nshmp-haz `35e140b8` (archived) |
|---|---|---|---|
| Per-rupture term | probability of no exceedance `exp(−rate·T·poes)` (`hazardlib/tom.py` `get_pnes`, lines 187–217; Poisson branch line 201). Non-Poisson ruptures use `Σ_k p(k;T)·(1−poe)^k` (p(k;T) = probability of k occurrences in T) (lines 202–217) | `hazFunction *= exp(log1p(−qkProb)·condProb)` (`HazardCurveCalculator.java` lines 379–401), i.e. `(1−q)^{poe}` with `q = 1 − e^{−λT}` | `utilCurve.multiply(rate); gmmCurve.add(utilCurve)` (`calc/Transforms.java` lines 194–215): annual-rate curves |
| Across sources or groups | `pmap = 1 − (1 − pmap)·exp(−rmap)` (`calc/hazard_curve.py` line 158; `rmap` is a rate map) | product of per-source non-exceedance, then `1 − Π` (lines 425–435). Non-Poisson sources first sum `q·poe` over mutually exclusive ruptures (lines 403–405) | weighted sums of rate curves (`HazardCurveSet.java` lines 169–170, 199–200) |
| Guard | — | throws if `log(1 − qkProb) < −30` (lines 387–389; "~infinite number of events") | — |
| Truncation | symmetric two-sided, `truncation_level` default 99 (`contexts.py` lines 846–853); job files map 0 to `1E-9` (`commonlib/oqvalidation.py` line 1395) | not examined (handled in IMR classes) | enum: `NONE`, `TRUNCATION_OFF`, `TRUNCATION_UPPER_ONLY`, `TRUNCATION_LOWER_UPPER`, `TRUNCATION_3SIGMA_UPPER`, PEER mixture models, `NSHM_CEUS_MAX_INTENSITY`, `NSHM_CEUS_3SIGMA_MAX_INTENSITY` (`calc/ExceedanceModel.java` lines 48–223) |
| Normal tail | `0.5·(1 + erf(x/√2))` via `math.erf`, subtracted from `Φ(b)` (`stats.py` lines 33–64) | not examined | Abramowitz–Stegun 7.1.26 rational approximation (`util/Maths.java` lines 53–79; `normalCcdf` lines 128–130) |

The three agree exactly for independent Poisson ruptures, because `(1−q)^{p} = e^{−λTp}` when `q = 1 − e^{−λT}`. PEER 2018/03 §3.2 (Test 2.1) records the error class this identity guards against: "a couple of codes were incorrectly converting the rate of exceedance to Poisson probability for each source and then summing the Poisson probabilities". *Basis: source + documentation + derived.*

### 3. Truncation of the ground-motion distribution

OpenQuake's scalar kernel (`stats.py` lines 41–64) is

```python
if x > tmax: return 0.
z = phi_b * 2. - 1.
p = (phi_b - .5 * (1. + math.erf(x * SQRT05))) / z
return min(max(p, 0.), 1.)
```

Here `phi_b = ndtr(truncation_level)`, and `tmax = ndtri(phi_b) + 1E-6`, or 9 when `phi_b == 1` (lines 77–88). This is two-sided truncation with renormalization. nshmp-haz computes `(p − pHi)/(pLo − pHi)` with `pLo = 1` for `TRUNCATION_UPPER_ONLY` and `pLo = 1 − pHi` for `TRUNCATION_LOWER_UPPER` (`ExceedanceModel.java` lines 85–114, 332–341). The archived snapshot leaves the choice to `config.hazard.exceedanceModel` (`Transforms.java` lines 167–168).

PEER 2018/03 §2.9 reports that 4 of 15 codes initially truncated both ends and 11 truncated only the upper end. The group consensus is that "the truncation should be performed on both ends". Results for Test 1.8b (2σ) were split into two benchmark groups because participants were not required to rerun. Two codes changed, bringing the both-ends group to six. Test 1.8c (3σ) showed no difference. Many participants "no longer truncate ground motions, or they apply a high truncation level, say, four standard deviations".

Measured with OpenQuake's `truncnorm_sf` at n = 2 (`support/oq_stats_truncation_probe.py`):

| ε | OpenQuake | two-sided formula | upper-only formula | untruncated | upper/two-sided − 1 |
|---|---|---|---|---|---|
| −1.0 | 0.857616 | 0.857616 | 0.837651 | 0.841345 | −2.328% |
| 0.0 | 0.500000 | 0.500000 | 0.488360 | 0.500000 | −2.328% |
| 1.0 | 0.142384 | 0.142384 | 0.139069 | 0.158655 | −2.328% |
| 1.9 | 0.006251 | 0.006251 | 0.006105 | 0.028717 | −2.328% |
| 2.0 | 0 | 0 | 0 | 0.022750 | — |

The largest absolute difference between OpenQuake and the two-sided formula is 1.2×10⁻¹⁶. Within the body, the two conventions differ by the constant factor `(2Φ(2) − 1)/Φ(2) = 0.97672`. *Basis: execution (OpenQuake function) + derived.*

**Edge case at `truncation_level = 0`.** The PEER σ = 0 acceptance tests call the hazardlib API with `truncation_level = 0` (`peer_test.py` lines 70, 112, 150, 194, 245). In that case `phi_b = 0.5` and `z = 0`. The engine compiles with `numba.njit(..., error_model='numpy')` (`baselib/performance.py` lines 518, 528), so division by zero does not raise. Executing `truncnorm_sf(0.5, [−1, −1e−9, 0, 5e−7, 1e−6, 2e−6, 1])` returned `[1, 1, nan, 0, 0, 0, 0]`: the survival function is a step, but exactly at `x = 0` (IML equal to the median) it is NaN. The job-file path cannot produce this because `truncation_level` is validated as `positivefloat(s) or 1E-9`. This was observed only through the direct API, and no hazard curve containing NaN was observed. *Basis: execution + source.*

### 4. Accuracy of the normal tail at the epsilons PEER tests

PEER 2018/03 Test 2.5a drives exceedance to ε ≈ 6 (7.0 g at 15 km). At the start of the project, "some codes used normal distribution functions that were accurate up to three or four standard deviations". Measured relative error against `scipy.special.ndtr` (`support/normal_tail_accuracy.py`):

| ε | exact P(Z>ε) | nshmp-haz A&S 7.1.26 (Python port) | OpenQuake `truncnorm_sf`, untruncated |
|---|---|---|---|
| 3 | 1.3499e-3 | +0.01% | +0.00% |
| 4 | 3.1671e-5 | +0.05% | +0.00% |
| 5 | 2.8665e-7 | +0.16% | −0.00% |
| 6 | 9.8659e-10 | +0.36% | +0.00% |
| 7 | 1.2798e-12 | +0.65% | +0.00% |
| 8 | 6.2210e-16 | −1.84% | +7.08% |
| 8.5 | 9.4795e-18 | −100% (returns 0) | −100% (returns 0) |

Both are well inside ±5% through ε = 7. Both lose all precision near ε ≈ 8.3, where the probability falls below double-precision resolution of `1 − Φ`. OpenQuake additionally cuts off at `tmax = 9` by design. The nshmp-haz column is a **port** of the quoted Java lines, not an execution of the Java code. *Basis: execution (port + OpenQuake function).*

### 5. The PEER code-verification exercises

| | PEER 2010/106 (Thomas, Wong, Abrahamson) | PEER 2018/03 (Hale, Abrahamson, Bozorgnia) |
|---|---|---|
| Codes | 8 participants published. Some Working Group members did not finish | 15 codes. 4 (HAZ45, HAZ45b, HAZ38-URS, THAZ) share a base and are not independent. The OpenSHA, OpenQuake and HAZ45 tests were run by the project coordinator "with support from the participant listed" (§1.4) |
| Process | blind feedback, then workshops (5 held) | blind first resubmittal, then open. 10 meetings over about 4 years; tests "often re-run several times" |
| Benchmark | analytical solution or "means over all results" | mean of the 5 best-agreeing codes, at most one from the HAZ family. Hand solutions agree "generally … less than half a percent" |
| Acceptance | "minimum standards … (e.g., 10% in probability level)" | ±5% on hazard (y-axis). Deaggregation ±2% (absolute percentage points for bin shares) |
| Sets | Set 1 (cases 1–11) consensus. Set 2 "consensus results were not reached" | Set 1 (1.1–1.11, no 1.9), Set 2 (multi-source + deaggregation, ASK14/BSSA14/CB14/CY14, hanging wall, hypocentre distributions, ε≈6 tails, mixture model), Set 3 (bending fault, logic tree + fractiles, intraslab, area zone with finite ruptures) with **no benchmarks** |

**Error classes and modelling differences found in PEER 2018/03**, with the section where each is reported:

- **Rate inputs.** Some codes need the rate above M0 or a moment rate rather than a slip rate. OpenQuake needs an a-value: Test 1.5 has 1347 events/yr above M 0 and `a = 3.129`, and Test 1.10 has 1308/yr and `a = 3.116`. Here "the test is more an indication of whether or not the individual running the code can calculate the required input correctly" (§2.2, §2.6, §2.10).
- **Rupture placement.** Floating ruptures are restricted to the fault, with area conserved and the magnitude *not* downgraded (§2.2). Codes either step a polygon or use a gridded fault. About 0.05 km steps were needed to meet ±5% without ground-motion variability (§2.3). Test 1.3 had internally inconsistent area, width and length scaling relations, and the instructions were rewritten (§2.4).
- **Distance precision.** Simplified distance functions in codes "not typically used for site-specific hazard" failed Test 1.4 and were fixed (§2.5).
- **Magnitude discretization.** Analytic bin integrals versus centre value times width (§2.6).
- **Area sources.** Degree-based grid spacing much larger than 1 km, distance grouping, and swinging-arc discretization (FRISK88) all appeared. A site at a zone edge was sensitive to grid origin. Point spacing was reduced to 0.5 km and σ was added (§2.10). Depth discretization should use increment centres, which changes the result by < 0.25% versus about 3% when the boundaries are included (§2.11).
- **Aggregation across sources.** Some codes summed Poisson probabilities across sources (§3.2).
- **NGA-West2 pitfalls (§3.3).** These include the ASK14 Z1.0 unit typo, the fact that CY14 needs Z1.0 in metres while ASK14 and BSSA14 need kilometres, BSSA14 coefficients truncated to three decimals by spreadsheet display, BSSA14's separate PGA coefficients, the CB14 rock-PGA `A1100` requiring Z2.5 from its own equation, and CY14's ΔZTOR needing `E[ZTOR]` for every rupture. One code computed ZHYPO as ZTOR (§1.5). An error was found and fixed in the PEER NGA-West2 Excel file for ASK14 RY0, and 7 versus 6 codes used the RY0 versus RJB form of the ASK14 T5 taper (§3.4).
- **Logic trees (Test 3.2: 36 branches).** Some codes did not restrict ruptures to the fault. 7 of 9 codes averaged rates instead of probabilities (§4.3). Fractile conventions split 5 (interpolation) versus 4 (first exceeding), a difference of up to 29% at the 10th percentile.
- **Bending faults (Test 3.1).** Projection along an average strike (the "Stirling" approach) versus orthogonal projection changes fault area by 9%. Closest-segment RX versus GC2 changes hazard by up to 17% off the fault end (§4.2).

*Basis: documentation.*

### 6. How OpenQuake encodes PEER tests, and how strict the encoding is

`openquake/hazardlib/tests/acceptance/peer_test.py` cites PEER 2010/106 and contains:

| Test | Source in test | σ / truncation | Discretization | Tolerance (`numpy.allclose`) |
|---|---|---|---|---|
| `test_case_2` | simple fault, M 6.0, rate 0.0160425 | `truncation_level = 0` | `rupture_mesh_spacing=1.0` | `atol` 3e-3 / 2e-5 / 1e-3 by site, `rtol=1e-5` |
| `test_case_5` | simple fault, truncated GR | 0 | 1.0 | `atol=1e-3, rtol=1e-5` |
| `test_case_10` | area source, depth 5 km | 0 | `area_discretization=10.0` (lines 62–63) | `atol=1e-4, rtol=1e-1` |
| `test_case_11` | area source, 6 hypocentre depths 5–10 km | 0 | 10.0 (lines 104–105) | `atol=1e-4, rtol=1e-1` |
| `test_non_parametric_source` | case 2 as explicit ruptures | 0 | — | as case 2 |

The 2010 instructions (§3.1) specify "uniformly distributed point sources … (1 km grid spacing)" and "number of events per year … (M ≥ 5) is 0.0395 … b-value = 0.9, and Mmax = 6½". The encoded `SET1_CASE10_MFD = TruncatedGRMFD(a_val=3.1, b_val=0.9, min_mag=5.0, max_mag=6.5, bin_width=0.1)` (`_peer_test_data.py` lines 135–136) gives 0.038032/yr (15 bins, centres 5.05–6.45), so `1 − e^{−0.038032} = 0.03732` against the tabulated `3.87E-02`, which is 3.6% low. `a = 3.116` (PEER 2018 §2.10) gives 0.039460. *Basis: execution + normative.*

Discretization sensitivity of the encoded case 10, measured with everything else as in the test (`support/oq_peer_case10_discretization.py`):

| area_discretization (km) | ruptures | seconds | lowest-IML PoE error, site 1 | max relative error, benchmark PoE ≥ 1e-4 | max relative error, benchmark PoE ≥ 1e-5 | passes encoded tolerance | all PoE ≥ 1e-5 within ±5% |
|---|---|---|---|---|---|---|---|
| 10 (as encoded) | 4,635 | 1.6 | −3.57% | 18.5% (site 2, 0.2 g) | 89.3% (site 3, 0.25 g) | yes | no |
| 5 | 18,720 | 7.3 | −3.59% | 15.4% (site 3, 0.15 g) | 31.8% (site 3, 0.25 g) | yes | no |
| 2 | 117,510 | 42.2 | −3.59% | 3.8% (site 4, 0.001 g) | 10.5% (site 3, 0.25 g) | yes | no |
| 1 (PEER instruction) | 470,565 | 172.0 | −3.52% | 3.9% (site 1, 0.05 g) | 6.8% (site 1, 0.3 g) | yes | no |
| 0.5 | 1,881,945 | 705.7 | −4.36% | 4.8% (site 4, 0.001 g) | 6.1% (site 1, 0.3 g) | yes | no |

The lowest-level error stays between −3.5% and −3.6% from 10 km down to 1 km (−4.4% at 0.5 km). The rate shortfall from the magnitude–frequency distribution dominates it, not the geometry. At the encoded 10 km spacing, errors up to 89% at PoE about 2×10⁻⁵ pass because `atol = 1e-4` exceeds those PoEs. *Basis: execution.*

**Coverage gaps (derived from the file list and the test bodies).** No 2010 Set 1 case 1, 3, 4, 6, 7, 8 or 9 is encoded, and no case with σ > 0 against PEER values. Nothing from PEER 2018/03 is encoded against PEER benchmark values. The QA suite has PEER-derived inputs: `qa_tests_data/classical/case_47` ("Mixture Model for Sigma using PEER (2018) Test Case 2.5b", `classical_test.py` lines 783–787) and `case_41` ("PEER 2015 Validation Project, Set 3, Test 3.1a as Characteristic Source w/SERA Site Amplification Models"). Their `expected/*.csv` headers read `generated_by='OpenQuake engine 3.20.0-git6a5db97d59'`, which makes them regression baselines, not external benchmarks. PEER 2018/03 Table 3.2 and Table 4.2 show that OpenQuake ran all Set 2 and Set 3 tests during the project. Those runs, and the electronic supplement comparing them, are outside the repository and were **not examined**.

### 7. NGA-West2 ground-motion models: implementation verification in OpenQuake

NGA-West2 (Bozorgnia et al. 2014) produced the ASK14, BSSA14, CB14, CY14 and I14 models for shallow crustal earthquakes, using a database covering M 3.0–7.9. Its research topics included directivity, damping scaling, NEHRP site-factor discrepancies and epistemic uncertainty. OpenQuake verifies each model against tables of median and standard deviation (`tests/gsim/utils.py` `BaseGSIMTestCase.check`, lines 215–262). The check computes `|got/expected·100 − 100|` per row and requires it to be ≤ `max_discrep_percentage`:

| Model | Reference table origin (quoted from the test file) | Tolerance |
|---|---|---|
| ASK14 | "generated from the Matlab implementation available as Annex 1 of Abrahamson et al. (2014)" (`abrahamson_2014_test.py` lines 26–27) | 0.1% (Taiwan regional mean 0.5%) |
| BSSA14 | "generated from the Fortran implementation provided by David M. Boore (Jul, 2014)" (`boore_2014_test.py` line 22) | `MEAN_DISCREP = 2.0`, `STDDEV_DISCREP = 1.0` (lines 29–30) |
| CB14 | "Excel file published as supplementary material with the V/H Earthquake Spectra paper", with two noted spreadsheet bugs (f_sed flag, A1100 Z2.5 cell) (`campbell_bozorgnia_2014_test.py` lines 21–29) | 0.1% |
| CY14 | "obtained from a tool given by the authors". Sigma tables "generated from opensha" (`chiou_youngs_2014_test.py` lines 51–79) | 0.05%. Extended backward-compatibility table 0.001% |
| I14 | "Matlab implementation created by Yue Hua, Stanford University" (`idriss_2014_test.py` line 22) | 0.1% |

Executed: the five test modules (34 tests) pass in 86.17 s (pytest), with 87.44 s wall time and 478 MB peak RSS. This checks transcription of coefficients and functional form against the authors' tools. It does not check distance-metric generation (RX, RY0, ZTOR, ZHYP per rupture), which PEER 2018/03 §1.3 identifies as the harder half of an NGA-West2 implementation ("not just a matter of programming the new equations but also automating the calculation of these new distance values"). PEER §3.3 says Test 2.2 "did not provide a complete validation of the NGA-West2 ground-motion models" and recommends validation tables from the PEER spreadsheet. *Basis: source + execution + documentation.*

### 8. Logic trees: aggregation, interpretation and scale

**Two quantities called "mean hazard".** Let a site have branch rates `ν_i(x)` with weights `w_i`. Then

```text
mean_poe(x)      = Σ w_i (1 − e^{−ν_i T})            # PEER 2018/03 §4.3 "correct" for Poisson probability
poe_of_mean(x)   = 1 − e^{−T Σ w_i ν_i}              # rate averaging, then conversion
poe_of_mean ≥ mean_poe   (Jensen: 1 − e^{−u} is concave)
```

OpenQuake computes the first by default. `calculators/getters.py` `build_stat_curve` (lines 49–75) applies `stat(poes, weights)` and switches to `to_probs(stat(to_rates(poes), weights))` only when `use_rates` is set (`oqvalidation.py` line 1401 default `False`; documented at lines 1038–1041). `preclassical.py` lines 386–398 log `You should set use_rates=true` when only the mean is requested (lines 415–416). nshmp-haz scales rate curves by GMM and source-set weights and sums them, which is the second quantity. Its `HazardCurveSet` comment notes distance-dependent GMM weights "may lead to the dropping of some curves". Measured with OpenQuake's functions on three equally weighted branches with rates {0.05, 0.2, 0.8}, {5e-3, 2e-2, 8e-2}, {5e-4, 2e-3, 8e-3} and {5e-5, 2e-4, 8e-4}/yr: the PoE of the mean rate exceeds the mean PoE by +13.48%, +1.49%, +0.15% and +0.015%. PEER's maximum of about 9% occurred at 0.001 g, where hazard is high. *Basis: source + execution (synthetic input) + documentation.*

**Fractiles.** `stats.quantile_curve` (lines 213–248) sorts branch values and returns `numpy.interp(q, cumsum(w), values)`. This is linear in hazard and places each value at its cumulative weight including itself (the docstring at line 212 notes `numpy.interp(q, [1/N, 2/N, ..., N/N], values)` for equal weights). For values {1e-4, 4e-4, 1.6e-3} with weights {0.2, 0.6, 0.2}:

| q | OpenQuake | linear-weight / log-hazard (PEER recommendation) | first value with cumulative weight ≥ q |
|---|---|---|---|
| 0.1 | 1.0e-4 | 1.0e-4 | 1.0e-4 |
| 0.5 | 2.5e-4 | 2.0e-4 | 4.0e-4 |
| 0.9 | 1.0e-3 | 8.0e-4 | 1.6e-3 |

*Basis: execution (synthetic input) + documentation.*

**Use and misuse.** Bommer and Scherbaum (2008) argue that branches must be mutually exclusive and collectively exhaustive, and that this "can actually be met" only questionably in practice. They suggest it "may be more rational to determine the mean ground motion at the selected design return period" than the ground motion at the mean return period. Abrahamson and Bommer (2005) argued against using the mean hazard curve for design. McGuire, Cornell and Toro (2005) argued that "it is always preferable to use the mean". Marzocchi, Taroni and Selva (2015) treat logic-tree outputs as a sample from an epistemic parent distribution ("ensemble modeling"), which allows validation. Atkinson, Bommer and Abrahamson (2014) discuss alternative ways to represent ground-motion epistemic uncertainty beyond a set of weighted published GMPEs. This is an editorial, and only its opening text was examined. Bommer et al. (2005) show that combining GMPEs requires conversions of component definitions and distance metrics before weighting.

**Scale in national models.** UCERF3-TI uses "1440 alternative logic-tree branches, necessitating access to supercomputers" (Field et al. 2014). UCERF3-TD produces "5760 different forecasts" (Field et al. 2015). The 2018 NSHM update added new CEUS GMMs with "modified assessments of the associated epistemic uncertainties", basin amplification in four western urban areas, and 22 periods × 8 VS30 maps, with hazard increases up to about 30% (CEUS) and about 50% (basins) (Petersen et al. 2020). The 2023 50-state model reports "hazard curves at hundreds of thousands of sites" for 21 periods, 2 peak parameters, MMI and 8 site classes (Petersen et al. 2024). *Basis: documentation.*

### 9. Testing hazard estimates against observed shaking

- **Stein, Geller and Liu (2012).** Maps understated shaking in Tohoku 2011, Wenchuan 2008 and Haiti 2010. The authors attribute this to short records and assumptions such as characteristic earthquakes and seismic gaps, and propose uncertainty communication and testing against null models (uniform or random). *Basis: documentation (secondary summary; full text not examined).*
- **Hanks, Beroza and Toda (2012) and Frankel (2013).** Hanks et al. respond to what they call the "remarkable indictment of the methods, models, and results" of PSHA in an earlier Stein et al. (2011) opinion piece. Frankel's paper is a formal Comment on Stein et al. (2012). Only titles and abstract openings were available, so their arguments were **not examined**.
- **Stirling and Gerstenberger (2010).** The New Zealand model is rejected as underpredicting PGA exceedances over 1–4 decades. It "is not inconsistent with the observations" once aftershock motions are removed.
- **Brooks, Stein and Spencer (2016).** Over a 510-year shaking record, uniform and randomized maps beat the Japanese national maps on the fractional-exceedance metric implicit in the maps. The national maps win on squared misfit.
- **Mak and Schorlemmer (2016), "A Comparison between the Forecast by the United States National Seismic Hazard Maps with Recent Ground-Motion Records", BSSA 106(4):1817–1831, DOI 10.1785/0120150323.** The DOI resolves (handle API) and the metadata matches OpenAlex. No abstract was available and the full text was **not examined**, so this report draws no conclusion from it.
- **Petersen et al. (2024).** "Tests show the new model is consistent with past ShakeMap intensity observations."
- **Gerstenberger et al. (2020).** They call for "a proper testing phase of the model to quantify its consistency and skill".

The disagreement is partly about metrics. A map defined by a 10%-in-50-years exceedance fraction is a statement about a fraction of sites, not about every site, and Brooks et al. show that metric choice reverses rankings. *Basis: documentation + derived.*

### 10. Performance and resource footprint (L1–L6)

Host for all measurements: Linux, 96-vCPU Intel Xeon @ 2.60 GHz, 236 GB RAM, CPython 3.13.15.

| Level | Quantity | Value | Basis |
|---|---|---|---|
| L1 authoring | person-months per hazard code or per PEER test | not measured. PEER 2018/03 reports about 4 years and 10 meetings for 15 codes | documentation |
| L2 toolchain build | build step, source size, JIT cache | none: pure Python + numba. Source tarball 146,771,236 B compressed (sha256 `c826e064…94bf`), 404 MB extracted. Numba cache in the tree: 52 `.nbi` + 72 `.nbc` files, 9.2 MB | measured |
| L3 JIT/compile | numba compile latency on first use | PEER suite with an empty `NUMBA_CACHE_DIR`: 72.09 s (pytest), 74.06 s wall, 840 MB peak RSS. Immediately rerun with the populated cache: 14.22 s, 521 MB. About 58 s of the cold run is attributable to JIT compilation (derived: 72.09 − 14.22). Cache size: 8.9 MB in 116 files | measured + derived |
| L4 execution | PEER acceptance suite (5 tests) | 21.6 s on the first successful run. 18.2 s, 16.9 s and 14.2 s on warm reruns (pytest time) | measured |
| L4 execution | NGA-West2 GMM suite (34 tests) | 86.2 s | measured |
| L4 execution | PEER case 10 at 10, 5, 2, 1 and 0.5 km discretization | 1.6, 7.3, 42.2, 172.0 and 705.7 s for 4,635 to 1,881,945 ruptures. Roughly linear in rupture count (see §6) | measured |
| L5 checking | cost of checking a hazard curve against a benchmark | trivial (`numpy.allclose`). PEER benchmark derivation needs ≥ 5 independent codes | derived |
| L6 memory | peak RSS, PEER suite / GMM suite | 515 MB / 478 MB (`/usr/bin/time -v`) | measured |
| L6 scale | UCERF3 branches | 1440 (TI), 5760 (TD) | documentation |
| L4/L6 for nshmp-haz, OpenSHA | any | not measured (not built) | — |

### 11. Comprehensibility and conceptual simplicity (C1–C2)

- **C1.** A reader needs about six concepts: Poisson rate, conditional exceedance, truncation convention, rate-versus-probability currency, branch weights, and fractile convention. The two silent switches, mean of probabilities versus probability of mean rate and linear versus log fractile interpolation, change answers by up to about 13% and 25% in the examples above, and neither appears in hazard-curve output names (`hazard_curve-mean-*.csv`). PEER 2018/03 §4.3 reports that the split appeared only in Test 3.2, when discussion revealed that 7 of 9 codes were computing the rate-averaged form.
- **C2.** The orthogonal core is a rate field `ν(x)` per branch. Probability is a terminal transform, and statistics should state their domain. nshmp-haz keeps rates throughout, OpenSHA keeps probabilities, and OpenQuake keeps both and exposes a flag. A minimal model would label every statistic with its domain (`mean(rate)` or `mean(poe)`) instead of a boolean. The truncation convention is a second hidden degree of freedom that the PEER group resolved by consensus, not by data. The physical upper bound some participants intended is "more closely tied to a limit on the amount of shaking that the earth can transmit, for instance 8.0g" (§2.9).

*Basis: derived.*

### 12. How implementations are validated (V1–V4)

- **V1, specification adequacy.** PEER tests turn individual terms into delta functions so that hand solutions exist. Their known weaknesses are inconsistent scaling relations (Test 1.3), under-specified seismogenic boundaries (Tests 3.3 and 3.4), and grid-origin sensitivity (Test 1.10). OpenQuake's encoded checks are weaker than the specification. The tolerance absorbs a 3.6% rate shortfall (§6), and `atol = 1e-4` dominates for PoEs below about 1e-3. Self-generated expected files are regression oracles only.
- **V2, differential testing across codes.** This is the main method: ≥ 5 independent codes agreeing within a few percent defines the answer. Code families that share ancestry (the HAZ family) are explicitly limited to one core vote. GMM tables are differential tests against the authors' own tools, so they share any error in those tools. Spreadsheet errors were found in ASK14 (RY0) and CB14.
- **V3, concurrency, crash and physical leakage.** Not applicable to these batch computations. Not examined.
- **V4, field falsification.** Hazard-versus-observation tests (§9) are the only check of model validity, as distinct from code correctness. They are limited by record length and by aftershock and declustering choices (Stirling–Gerstenberger), and they are sensitive to the metric (Brooks et al.).

## Boundaries

- **Not examined.** nshmp-haz on GitLab, which is the code used for the 2018 and 2023 NSHM. Any nshmp-haz or OpenSHA execution. OpenSHA's truncation implementation (in IMR classes). The PEER 2018/03 electronic supplement (Appendix D) and the full benchmark tables. PEER 2010/106 Appendix A tables beyond the values copied in `_peer_test_data.py`. Full texts of Stein et al. (2012), Hanks et al. (2012), Frankel (2013), Musson (2005), Mak–Schorlemmer (2016) and Bommer–Scherbaum (2008) beyond their abstracts. Engine runs through `oq engine` job files, as opposed to the hazardlib API. OpenQuake's disaggregation, event-based and non-Poisson (time-dependent) source paths.
- **Unknown.** Whether OpenQuake's 2018 PEER submissions met ±5% on every test. PEER Table 2.2/3.2 shows participation but not per-code pass/fail in the extracted text. Whether the archived nshmp-haz defaults to `TRUNCATION_UPPER_ONLY` or `TRUNCATION_LOWER_UPPER` in the NSHM configurations (the config files were not examined). How often the NaN-at-tie edge (§3) can arise in practice through the hazardlib API.
- **Known not to apply.** The execution measurements describe OpenQuake under the PyPI dependency set listed in Applicability, not GEM's supported wheel set. The nshmp-haz tail-accuracy figures describe a Python port, not the JVM build. Synthetic logic-tree and fractile inputs show the size of definitional differences, not differences in any national model's published hazard.
- **Unsupported stronger conclusions.** None of this establishes that any code is wrong. The rate-versus-probability mean and the fractile interpolation are definitional choices, and the PEER report itself accepted results in "annual frequency of exceedance" as a separate group. The 3.6% rate shortfall in the encoded Case 10 is a test-encoding issue, not a hazard-code defect. Agreement with author tables does not validate a GMM against data.

## Evidence

Evidence was acquired on 2026-11-20 (UTC). Revisions were resolved with `gh api repos/<owner>/<repo>/commits/HEAD`.

- **OpenQuake `gem/oq-engine@d6042c3ad58401d8eb9d8319d9fc0480b3f8f25d`.**
  - Core computation: `openquake/hazardlib/calc/hazard_curve.py` (lines 84–159; line 158 is the group combination) and `openquake/hazardlib/tom.py` (`PoissonTOM.get_probability_no_exceedance` lines 156–173; `get_pnes` lines 186–217).
  - Statistics and truncation: `openquake/hazardlib/stats.py` (`ndtr` 33–35, `_truncnorm_sf` 41–64, `get_tmax` 77–88, `mean_curve` 190–198, `quantile_curve` 211–248) and `openquake/hazardlib/contexts.py` (truncation fields 846–853, `_set_poes_` 696–707, std check 1762–1764).
  - Engine options: `openquake/calculators/getters.py` (`build_stat_curve` 49–75), `openquake/commonlib/oqvalidation.py` (1038–1041, 1395, 1401), `openquake/calculators/preclassical.py` (386–398, 415–416), `openquake/hazardlib/calc/mean_rates.py` (`to_rates` 26–39, `to_probs` 42–49) and `openquake/baselib/performance.py` (518, 528).
  - Tests: `openquake/hazardlib/tests/acceptance/peer_test.py` (47–266), `_peer_test_data.py` (135–136, 142–158, 187–208), `openquake/hazardlib/tests/gsim/{abrahamson_2014,boore_2014,campbell_bozorgnia_2014,chiou_youngs_2014,idriss_2014}_test.py`, `tests/gsim/utils.py` (215–262), `openquake/qa_tests_data/classical/case_41`, `case_47` and `openquake/calculators/tests/classical_test.py` (699–703, 783–787).
- **nshmp-haz `usgs/nshmp-haz@35e140b8eb665e35d373dbd4a96d2204ce7f2592`.** `src/gov/usgs/earthquake/nshmp/calc/ExceedanceModel.java` (48–223, 332–384), `calc/Transforms.java` (162–215), `calc/HazardCurveSet.java` (25–40, 160–200), `util/Maths.java` (53–79, 121–130) and `README.md`.
- **OpenSHA `opensha/opensha@a0bba0d13f3dbd9ec3a3076a7ccea4491cc41393`.** `src/main/java/org/opensha/sha/calc/HazardCurveCalculator.java` (349–440).
- **PEER 2010/106.** Abstract, §2.1–2.2 and §3.1 (instructions, Case 10/11 text, area-source rate). **PEER 2018/03.** §1.4–1.6, §2.2–2.11, §3.2–3.6, §4.2–4.5 and §5.
- **Literature.** All DOIs in `REPORT.json`, plus 10.1193/070913EQS198M, 10.1193/070113EQS184M, 10.1193/062913EQS175M, 10.1193/072813EQS219M, 10.1193/070613EQS195M, 10.1193/1.1899158, 10.1193/1.1985447, 10.1193/1.1985445, 10.1785/0120140131, 10.1785/0220140120, 10.1785/0120040073, 10.1785/0120140093, 10.1785/0220120043, 10.1016/j.tecto.2012.11.032, 10.1785/0220150100, 10.1785/0120090336, 10.1785/gssrl.83.1.130, 10.1785/BSSA0890020501, 10.1785/gssrl.68.1.180 and 10.1785/0120150323. Each was resolved through the doi.org handle API (`responseCode 1`) and matched for title, year, venue and pages against OpenAlex. Crossref was unreachable from the fetcher used.
- **Execution (support/).** `support/oq_stats_truncation_probe.py` with output `.out`, `support/normal_tail_accuracy.py` with `.out`, `support/oq_peer_case10_discretization.py` with `.out`, and `support/run_log.txt` (test commands, timings, environment). Commands are run from the extracted tarball root `oq-engine-d6042c3ad58401d8eb9d8319d9fc0480b3f8f25d/`:

```console
python -m pytest -q -p no:cacheprovider openquake/hazardlib/tests/acceptance/peer_test.py      # 5 passed
python -m pytest -q -p no:cacheprovider openquake/hazardlib/tests/gsim/{abrahamson_2014,boore_2014,campbell_bozorgnia_2014,chiou_youngs_2014,idriss_2014}_test.py   # 34 passed
python support/oq_stats_truncation_probe.py <tarball root>
python support/normal_tail_accuracy.py <tarball root>
python support/oq_peer_case10_discretization.py <tarball root>
```

## Revalidation

1. **Algebra and currency.** Diff `hazardlib/tom.py` `get_pnes` and `calc/hazard_curve.py` line 158 at a new revision. If `exp(−rate·T·poes)` and the rate-map combination remain, §2 holds.
2. **Mean and fractile conventions.** Check that `getters.build_stat_curve` still branches on `use_rates`, the `oqvalidation.py` default, and `stats.quantile_curve`'s `numpy.interp` on raw values. Rerun `support/oq_stats_truncation_probe.py` to confirm the 13.48% and 25% figures.
3. **Truncation.** Rerun the probe. `max |OQ − 2-sided|` should be about 1e-16.
4. **PEER encoding.** `grep -n "area_discretization\|a_val\|atol" openquake/hazardlib/tests/acceptance/*.py`, then rerun `support/oq_peer_case10_discretization.py`. If `a_val` becomes 3.116 or the tolerances tighten, revise §6. Inspect `expected/*.csv` headers of PEER-derived QA cases for `generated_by`.
5. **GMM verification.** Rerun the five gsim test modules and grep the tolerance constants.
6. **nshmp-haz.** For the production lineage, repeat the `ExceedanceModel`, `Transforms` and `Maths` reads on the GitLab repository. Whether its rate-curve weighting and A&S erf persist is not established by this snapshot.
