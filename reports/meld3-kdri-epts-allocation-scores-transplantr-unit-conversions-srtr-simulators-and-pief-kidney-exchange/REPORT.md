# Transplant allocation scores and kidney-exchange clearing: OPTN MELD/MELD-Na/MELD 3.0, KDRI/KDPI and EPTS versus the transplantr R package, SRTR simulated allocation models, and cycle and position-indexed formulations in open kidney-exchange solvers

## Summary

- **Allocation scores are defined by OPTN policy text, not by the papers that derived them. The text fixes rounding, floors, caps and unit conventions that change rank order.**
  - The pre-2023 OPTN MELD(i) was "rounded to the tenth decimal place and then multiplied by 10".
  - The OPTN MELD-Na adjustment is `MELD(i) + 1.32·(137−Na) − 0.033·MELD(i)·(137−Na)`, with sodium bounded to 125–137 and applied only when MELD(i) > 11.
  - MELD 3.0 (adults, effective July 13, 2023) adds sex and albumin. It caps creatinine at 3.0 mg/dL (previously 4.0), bounds albumin to 1.5–3.5 g/dL, and rounds to the nearest whole number within 6–40.
  - On October 31, 2024 the KDPI was refit without donor race and hepatitis C. It now uses 8 donor factors and new coefficients, scaled by the previous year's median KDRI (1.40436817065005 for 2024).
- **The open R implementation `transplantr` (v0.2.0) diverges from OPTN policy in ways that change scores and rank order.**
  - Code-level defects:
    - It rounds MELD to 10 decimal digits instead of one.
    - Its `meld_na` omits the creatinine cap at 4.0 and uses the 140-based research formula of Kim et al. (2008) without bounding sodium.
    - Its UKELD "US units" path divides by the conversion factors instead of multiplying. For the package's own test patient this lowers UKELD from 63.22 to 32.13.
    - Its `raw_epts` uses a non-vectorised `max` and its EPTS table has no 99th-percentile bin.
    - Its `soft()` converts units twice.
  - Version drift: the package predates MELD 3.0 and the 2024 KDPI refit.
  - The numbers above come from a line-by-line Python transliteration of the R code (R was not run). The transliteration reproduces all three of the package's own numeric MELD/UKELD test values.
- **Simulated allocation models predict direction better than magnitude.** The kidney model (KPSAM) projected small changes for the 2014 kidney allocation system. Observed changes were several times larger for black recipients (+6% vs +1% projected), for cPRA-100% candidates (+9% vs +2%) and for sharing (+10% vs +2%). The authors attribute the gap to unmodelled changes in acceptance behaviour. The liver model's acceptance sub-model discriminates worse for infants (AUC 0.783 non-status-1A; 0.618 status 1A) than for adults (0.922; 0.779).
- **Kidney-exchange clearing objectives differ by programme, and open solvers make solver settings part of the result.**
  - The UK programme optimises a five-level lexicographic hierarchy.
  - `kidney_solver` sets Gurobi's MIP gap to 0 but returns whatever incumbent exists at a time limit, signalling this only by a printed status code.
  - `KidneyExchange` leaves CPLEX's default 1e-4 relative gap in force unless a positive gap is requested, and its edge-formulation solver is an unimplemented stub returning `null`.
  - An exact toy enumerator found up to 56 distinct optimal cycle sets on induced sub-instances of a 64-pair benchmark instance. Who is matched can therefore depend on solver tie-breaking rather than on the stated objective.

## Applicability

| Subject (pinned in `REPORT.json`) | What was examined | Execution |
|---|---|---|
| `johnasher/transplantr` (DESCRIPTION `Version: 0.2.0`; last commit 2020-02-28) | `R/liver.R`, `R/liver_scores.R`, `R/uskdri.R`, `R/epts.R`, `R/unit_conversion.R`, `tests/testthat/*.R` | **Not run.** A Python transliteration was run (`support/transplantr_translit_probe.py`) |
| OPTN policy notice "Improving Liver Allocation: MELD, PELD, Status 1A, Status 1B" (Board approved June 27, 2022) | Policy 9.1.D/9.1.E text, old and new | Normative text only |
| OPTN KDPI guide (updated April 23, 2026) and EPTS guide (updated April 07, 2026) | Formulas, coefficients, worked example, c-statistics | Normative and documentary text only |
| `jamestrimble/kidney_solver` | `kidney_solver/kidney_ip.py`, `kidney_digraph.py`, `kidney_solver.py`, `kidney_utils.py`, `README.md`, `tests/test_ip.py`, test fixtures | **Not run** (requires Gurobi). An independent exact toy enumerator was run on its fixtures |
| `JohnDickerson/KidneyExchange` | `solver/CPLEXSolver.java`, `Solver.java`, `CycleFormulationCPLEXSolver.java`, `EdgeFormulationCPLEXSolver.java`, `fairness/solver/FairnessCPLEXSolver.java` | **Not run** (requires CPLEX) |
| Papers, abstracts and documents listed in `REPORT.json` | As noted per finding | Not applicable |

- **Relationship between the subjects.**
  - `transplantr` is compared against OPTN policy and against the derivation papers.
  - The simulated allocation models (SAMs) are described from the SRTR authors' own papers and from independent evaluations. The SAM software itself is not public and was not examined.
  - The two solvers are compared with the formulations they cite (cycle formulation; PICEF/HPIEF) and with programme objectives.
- **Coverage of OPTN versions.** Two OPTN liver-score versions are covered: pre-July 2023 MELD/MELD-Na, and MELD 3.0. Two KDPI versions are covered: the Rao et al. 10-factor donor KDRI, and the October 2024 8-factor refit. EPTS has one formula with annually updated mapping tables.
- **Host for all executions.** Linux x86-64 VM, Intel Xeon @ 2.60 GHz, Python 3.13 (standard library only).

## Findings

### 1. Liver scores as specified by OPTN policy

Source: the OPTN policy notice, Policy 9.1.D text, before and after the change. Basis: normative.

**Pre-July 2023 MELD and MELD-Na.**

```text
MELD(i) = 0.957 × ln(creatinine mg/dL) + 0.378 × ln(bilirubin mg/dL) + 1.120 × ln(INR) + 0.643
Laboratory values less than 1.0 will be set to 1.0.
Creatinine 4.0 mg/dL if: creatinine > 4.0; ≥ 2 dialysis treatments in prior 7 days; 24 h CVVHD in prior 7 days.
The maximum MELD score is 40. The MELD score derived from this calculation will be rounded
to the tenth decimal place and then multiplied by 10.
For candidates with an initial MELD score greater than 11:
MELD = MELD(i) + 1.32*(137-Na) – [0.033*MELD(i)*(137-Na)]
Sodium values less than 125 mmol/L will be set to 125, and values greater than 137 mmol/L will be set to 137.
```

**MELD 3.0 (candidates at least 18 years old at registration).**

```text
MELD = 1.33 (if female) + [4.56 × ln(bilirubin)] + [0.82 × (137 − sodium)] − [0.24 × (137 − sodium) × ln(bilirubin)]
     + [9.09 × ln(INR)] + [11.14 × ln(creatinine)] + [1.85 × (3.5 − albumin)] − [1.83 × (3.5 − albumin) × ln(creatinine)] + 6
Bilirubin, INR, creatinine < 1.0 → 1.0; creatinine 3.0 if > 3.0 or the dialysis/CVVHD rule applies;
sodium bounded 125–137 mmol/L; albumin bounded 1.5–3.5 g/dL; minimum 6, maximum 40; rounded to the nearest whole number.
```

- Candidates who were 12–17 years old at registration and are now at least 12 receive the same expression without the female term, with constant 7.33 in place of 6.
- PELD Cr caps creatinine at 1.3 mg/dL, with minimum 6 and integer rounding.
- The HRSA MELD calculator page states that the MELD 3.0 changes took effect July 13, 2023 (Basis: documentation).

**Provenance of the coefficients** (Basis: documentation, abstracts):

- MELD descends from a model predicting survival after transjugular intrahepatic portosystemic shunts (Malinchoc et al., 2000).
- Kim et al. (NEJM 2008) derived MELD-Na on 2005 OPTN registrants and validated it on 2006 registrants. They report hazard ratios of 1.21 per MELD point and 1.05 per 1-mmol/L sodium decrease, for sodium between 125 and 140 mmol/L.
- MELD 3.0 is from Kim et al. (Gastroenterology 2021).
- The sodium range stated in the abstract (125–140) differs from the OPTN policy bounds (125–137). The two documents define different equations.

### 2. Kidney donor and candidate indices as specified by OPTN

Basis: normative and documentation (OPTN guides).

| Factor | Rao et al. donor KDRI coefficient (as implemented in transplantr) | OPTN refit coefficient (implemented Oct 31, 2024) |
|---|---|---|
| Age (all) | 0.0128 × (age − 40) | 0.0092 × (age − 40) |
| Age < 18 | −0.0194 × (age − 18) | +0.0113 × (age − 18) |
| Age > 50 | 0.0107 × (age − 50) | 0.0067 × (age − 50) |
| Height | −0.0464 × (cm − 170)/10 | −0.0557 × (cm − 170)/10 |
| Weight < 80 kg | −0.0199 × (kg − 80)/5 | −0.0333 × (kg − 80)/5 |
| Black race | 0.1790 | removed |
| Hypertension | 0.1260 | 0.1106 |
| Diabetes | 0.1300 | 0.2577 |
| Cause of death CVA | 0.0881 | 0.0743 |
| Creatinine | 0.2200 × (Cr − 1); −0.2090 × (Cr − 1.5) if Cr > 1.5 | 0.2128 × (Cr − 1); −0.2199 × (Cr − 1.5) if Cr > 1.5 |
| HCV positive | 0.2400 | removed |
| DCD | 0.1330 | 0.1966 |

- `KDRI_SCALED = exp(Xβ) / scaling`. The scaling factor is the median KDRI_RAO among the previous calendar year's donors, 1.40436817065005 for 2024. The KDPI is read from an annually updated mapping table.
- The guide's worked example is: age 52, 183 cm, 81 kg, hypertensive, non-diabetic, CVA, creatinine 1.7 mg/dL, DCD. It gives `Xβ = 0.53787`, KDRI_RAO = 1.71235565748184, KDRI_SCALED = 1.21930679808076, and KDPI = 72%. The probe reproduces the first three numbers exactly.
- The KDPI c-statistic is approximately 0.60.
- Rao et al. (2009) proposed a 14-factor KDRI that includes transplant factors (HLA-B/DR mismatch, cold ischaemia, en bloc). The KDPI uses the donor-only subset.
- **EPTS.**

  ```text
  raw = 0.047·max(age−25,0) − 0.015·DM·max(age−25,0) + 0.398·priorTx − 0.237·DM·priorTx
      + 0.315·ln(yearsDialysis+1) − 0.099·DM·ln(yearsDialysis+1) + 0.130·[yearsDialysis=0] − 0.348·DM·[yearsDialysis=0] + 1.262·DM
  ```

  - The raw value is converted through a mapping table updated annually.
  - The c-statistic is 0.69.
  - EPTS matters only for kidneys with KDPI ≤ 20%. For those, candidates with EPTS ≤ 20% receive priority, within the 250-nautical-mile geography.
  - The number of prior transplants does not matter, only whether there was one.

### 3. transplantr versus policy: discrepancies with quoted source lines

Each row quotes the pinned source. The "effect" column comes from `support/transplantr_translit_probe.py`, a Python transliteration, not transplantr. Its fidelity check: the transliteration reproduces the package's own test expectations `meld(INR=2.0, bili=54, creat=170) = 24.798`, `meld_na(…, Na=131, units="US") = 26.257` and `ukeld(1.0, 212, 54, 126) = 63.22`.

| # | Function and lines | Source | Policy or definition | Effect (transliteration) |
|---|---|---|---|---|
| D1 | `meld`, `R/liver.R` 100 | `meld = 10 * round(meldi, digits = 10)` | MELD(i) "rounded to the tenth decimal place and then multiplied by 10"; no cap at 40 in code | Test patient: 24.798 vs policy MELD(i) 25.0 |
| D2 | `meld_na`, `R/liver.R` 151–172 | No `creat = ifelse(creat > 4, 4, creat)` line; `meld` has it at line 92 | Creatinine set to 4.0 if > 4.0 | Cr 6.0 mg/dL, INR 1.5, bili 3.0, Na 137: `meld` 28.39, `meld_na` 32.85, policy 28.0 |
| D3 | `meld_na`, `R/liver.R` 171–172 | `meldna0 = meldscore - Na - (0.025 * meldscore * (140 - Na)) + 140`; `meldna = ifelse(meldscore > 11, meldna0, meldscore)`; sodium never bounded | OPTN: `MELD(i) + 1.32(137−Na) − 0.033·MELD(i)(137−Na)`, Na in [125,137] | INR 1.8, bili 2, Cr 2: Na 120 → +2.00 vs policy; 131 → +0.69; 137 → +1.60; 145 → −1.95 |
| D4 | — | No MELD 3.0 function at this revision | MELD 3.0 since July 13, 2023 | Rank inversion: candidate A (female, albumin 2.0, INR 1.6, bili 2.5, Cr 1.0) vs B (male, albumin 3.5, INR 1.7, bili 3.0, Cr 1.1), both Na 137. `meld_na`: A 17.02 < B 19.13. MELD 3.0: A 19 > B 17 |
| D5 | `ukeld`, `R/liver.R` 21–24; `ukeld_US`, 53–54 | `if (units == "US") { bili = bili / 17.1; creat = creat / 88.4 }`; `1.485 * log(creat / 88.4) + 3.13 * log(bili / 17.1)` | UKELD takes µmol/L, so mg/dL inputs must be multiplied. The package's own `bilirubin_to_SI` and `creatinine_to_SI` multiply (`R/unit_conversion.R`) | Same patient: SI 63.22; `units = "US"` and `ukeld_US` both 32.13 (−31.09 points, = 2·(1.485·ln 88.4 + 3.13·ln 17.1)) |
| D6 | `raw_epts`, `R/epts.R` 24 | `agebase = max(age - 25, 0)` | Elementwise `max(age−25,0)` per candidate | `raw_epts(age = c(30, 60), …)` gives [1.775, 1.775]; scalar calls give [0.365, 1.775] |
| D7 | `epts_lookup`, `R/epts.R` 189–190 | `raw <= 3.1633656423 ~ 98,` then `TRUE ~ 100)` | Scores range 0–100% | No raw value maps to 99. Every value above the 98th-percentile threshold maps to 100 |
| D8 | `uskdri`, `R/uskdri.R` 44–55 | Rao coefficients including `ethvar = ifelse(eth == "black", 0.1790, 0)` and `hcvvar = 0.2400 * hcv` | 2024 refit removed race and HCV | Guide example donor, scaled by the 2024 factor: transplantr KDRI 1.26414, which its table maps to 74 (87 with `eth = "black"`); OPTN 2024: 72 |
| D9 | `kdpi`, `R/uskdri.R` 132–135 | `kdri = uskdri(..., scaling, units); kdpi_lookup(kdri, scaling = 1)` with `scaling = 1` default | The KDPI table is indexed by scaled KDRI | Guide donor with the default `scaling = 1`: 95; with the documented 2018 factor 1.250609: 83 |
| D10 | `soft`, `R/liver_scores.R` 287–295 | Converts `Albumin / 10` and `DonorSCr / 88.4`, then calls `p_soft(...)` and `soft2(...)` without `Units`, whose defaults (`"SI"`) convert again (lines 126–128, 203–205) | One conversion | Albumin 30 g/L is seen as 0.30 g/dL, giving 2 points (intended 0). Donor creatinine 140 µmol/L is seen as 0.018 mg/dL, giving 0 points (intended 2) |
| D11 | `p_soft`, `R/liver_scores.R` 122–135 | `AbdoSurg` is a documented parameter but does not appear in the returned sum | — | Previous abdominal surgery never changes the score |
| D12 | `soft2`, `R/liver_scores.R` 201 | `ifelse(DonorAge >= 10 && DonorAge <= 20, -2, …)` | Vectorised use needs `&` | R 4.3.0 made `&&` with an operand of length > 1 an error (R NEWS). Not executed here |

- **Test coverage.** The upstream tests cover the SI paths of `ukeld`, `meld` and `meld_na` with sodium 131 and creatinine 2. They do not exercise D2, D5 to D7 or D9.
- **Consequence for rank order** (Basis: derived). D1 and D3 shift scores by fractions of a point to two points. Under MELD-based sorting, such shifts reorder candidates whose policy scores differ by less than that amount. D4 shows a full inversion. D5 moves a patient by about 31 UKELD points.

### 4. Simulated allocation models: structure and agreement with observed outcomes

- **Structure.** SRTR maintains a family of simulated allocation models: LSAM (liver), KPSAM (kidney–pancreas) and TSAM (thoracic) (Thompson et al., 2004; Basis: documentation, abstract). The KPSAM used for the 2014 kidney policy has the following structure (Israni et al., JASN 2014; Basis: documentation, full text):
  - It replays the actual 2010 donors and candidates over one year.
  - It checks compatibility at each organ arrival and builds ordered lists by points.
  - It simulates accept/decline with a logistic regression fitted to 2010 acceptance behaviour.
  - It counts transplants and discards, and projects survival with linear approximations to Cox models.
  - It repeats this 10 times per policy, permuting donor arrival order and drawing new acceptance random numbers.
  - Because the cohort is fixed, "this range reflects variability of the simulation modeling, not variability in actual organ allocations". The authors state "The KPSAM cannot account for changes in organ acceptance behaviors."
- **Projections for the 2014 kidney allocation system** (same paper):
  - transplants 11,531 → 11,599;
  - median post-transplant lifespan 11.82 → 12.65 years;
  - +7.0% median patient life-years per transplant;
  - +2.8% median allograft-years;
  - an estimated 9,130 patient life-years gained, assuming 11,000 transplants.
- **Projected versus observed** (Gustafson et al., ATC 2016 abstract C72, by the SRTR group). Basis: documentation. Simulated 2010 cohorts, first 9 months, compared with Dec 2013–Sep 2014 (pre) and Dec 2014–Sep 2015 (post).

| Quantity | Projected change | Observed change |
|---|---|---|
| Transplants to black candidates | +1% | nearly +6% |
| Transplants to Hispanic candidates | +0.8% | +1.5% |
| cPRA 99% | +0.3% | +2% |
| cPRA 100% | +2.0% | +9% |
| Sharing beyond local | +2% | nearly +10% |
| ABO B candidates | +5% | +0.5% |
| Age 18–34 | +5% | +4% |
| Waitlist deaths by age | — | "well predicted" |

  The authors' explanation: "SAM predictions tend to be conservative, likely due to inability to predict behavioral changes in listing and organ acceptance, and reliance on historic data."

- **Independent one-year evaluation** (Stewart et al., AJT 2016; Basis: documentation, abstract):
  - transplants with donor–recipient age difference above 30 years fell 23%;
  - bolus effects for cPRA 99–100% candidates and candidates with at least 10 years on dialysis;
  - more long-distance shipping and longer cold ischaemia;
  - higher delayed graft function;
  - unchanged 6-month graft survival.
- **Sub-model validity** (Wood et al., AJT 2021; Basis: documentation, full text). LSAM's acceptance models have 23 variables (status 1A) and 58 variables (non-1A). On 2013–2016 offers their AUCs were:
  - non-1A: adults 0.922, pediatric 0.815, teenagers 0.898, children 0.806, infants 0.783;
  - status 1A: adults 0.779, pediatric 0.711, infants 0.618.
  - Acceptance rates were 1:57 for non-1A adults and 1:34.7 for non-1A pediatric candidates.
- **Newer simulators.**
  - Pivo et al. (Transplant Direct 2025) re-implemented the existing OPTN simulation model. One simulated year fell from more than 6 h to about 15 s, enabling 50,000 policy simulations and multiobjective optimisation for kidney continuous distribution.
  - Rose et al. (JHLT 2024) describe COMET, an open-source agent-based simulator with synthetic populations. COMET-Lung against observed 2018–2019 outcomes:
    - waitlist deaths per waitlist-year: 0.162 [0.157, 0.167] simulated vs 0.170 observed;
    - transplants per waitlist-year: 1.25 vs 1.26;
    - post-transplant deaths per patient-year: 0.115 vs 0.113;
    - travel distance: 202 vs 165 nautical miles.
  - These are the authors' own validation numbers.

### 5. Kidney-exchange clearing formulations and programme objectives

- **Formulations.**
  - *Cycle formulation*: one binary per feasible cycle or chain up to the caps (Roth, Sönmez and Ünver; Abraham, Blum and Sandholm).
  - *Edge formulations*: extended edge formulation (Constantino et al., 2013).
  - *Position-indexed formulations*: PIEF/PICEF/HPIEF (Dickerson, Manlove, Plaut, Sandholm and Trimble, EC 2016).
  - Abraham et al. prove clearing with a cycle-length cap NP-hard. Their column-generation approach replaced CPLEX for the Alliance for Paired Donation.
  - Dickerson et al. introduce three formulations, two of them compact. One has an LP relaxation "exactly as tight as the previous tightest formulation (which was not compact)" for instances without non-directed donors. They report orders-of-magnitude speedups on UNOS and UK NLDKSS data.
  - Basis: documentation, abstracts.
- **UK objective hierarchy** (Manlove and O'Malley; quoted from the technical-report version TR-2012-330 of the JEA paper; Basis: documentation, full text):
  1. maximise the number of effective 2-cycles, that is 2-cycles plus 3-cycles with a back-arc;
  2. maximise size;
  3. minimise the number of 3-cycles;
  4. maximise the number of back-arcs in 3-cycles;
  5. maximise the total weight.

  - The hierarchy is solved as a sequence of IPs. Each stage's optimum becomes a constraint for the next.
  - Every optimal solution for 14 matching runs (July 2008–October 2011) was computed in under 2 s on a single-core Pentium 4 at 3 GHz.
  - The technical report says allowing 4-way exchanges would yield "a significant number of additional transplants". The JEA abstract says "a moderate number". The two versions disagree.
- **European diversity** (Biró et al., Transplantation; Basis: documentation, abstract): 17 countries reported, 10 programmes operating, more than 1,300 transplants through the end of 2016, about 8% of these countries' living donation in 2015. Objectives, cycle and chain limits, and legal constraints differ by country.

### 6. Open solvers: caps, chains, failure awareness, tolerances

Basis: source.

- **`kidney_solver`.**
  - Formulations: `uef`, `hpief_prime`, `hpief_prime_full_red`, `hpief_2prime`, `hpief_2prime_full_red`, `eef`, `eef_full_red`, `picef`, `cf`.
  - The chain cap counts edges "excluding the dummy arc to the NDD" (`README.md`).
  - `create_ip_model` (`kidney_ip.py` lines 149–157) sets `m.params.mipGap = 0` and, if given, `m.params.timelimit`.
  - `kidney_solver.py` line 104 prints `solver_status: {}` with the raw Gurobi status code. Otherwise a time-limited run's output has the same shape as an optimal run's.
  - Failure-aware matching uses a uniform edge-success probability `p`, only for `cf` and `picef`:
    - cycle value `= (Σ edge scores) · p^|c|` (`kidney_digraph.py` lines 22–32);
    - a chain edge at position `pos` is weighted `p^(pos+1)` (`kidney_ip.py` line 547).
  - Solution extraction thresholds are `var.x > 0.1` for edge variables and `> 0.5` for cycle variables.
  - Upstream oracle values (`tests/test_ip.py`):
    - fixture `MD-00001-00000100` with cycle cap 4 and chain cap 0: total score 39 for every formulation;
    - `two_2cycles`: 40;
    - failure-aware `3cycle_and_3chain` with p = 0.5: e.g. `3*.125 + .875` with caps (3, 3).
- **`KidneyExchange`.**
  - `CycleFormulationCPLEXSolver` maximises `scalProd(weights, x)` over cycle binaries.
  - `EdgeFormulationCPLEXSolver.solve()` at this revision logs "Solving cycle formulation IP." and then reaches `// TODO implement constraint generation`, `cplex.clearModel();`, `return null;` (lines 17–26).
  - `CPLEXSolver.initializeCPLEX` (lines 31–36) sets `TiLim` only `if(getMaxSolveSeconds() > 0)` and `EpGap` only `if(getRelativeMipGap() > 0)`. `Solver` defaults are `maxSolveSeconds = 0` and `relativeMipGap = 0.0` (lines 10–11). With defaults, CPLEX's own relative gap tolerance applies, whose documented default is 1e-04 (IBM CPLEX 22.1.1 parameter reference).
  - `solveCPLEX` accepts any `cplex.solve() == true` result. The CPLEX status is printed only when debug printing is enabled. In the CPLEX API, `solve()` returns true for a feasible, not necessarily optimal, solution (Basis: documentation, vendor API semantics; no pinned CPLEX version examined).
  - `FairnessCPLEXSolver` maximises total weight subject to `Σ altWeight_c·x_c ≥ α·|special|` (line 198), with failure-aware or plain per-cycle "special" weights.
- **Toy probe: ties in optimal matchings.**
  - `support/cycle_packing_toy.py` is an exact memoised enumerator, an independent re-implementation of the cycle-formulation objective without chains. It is not either solver.
  - On `two_2cycles` it reproduces the upstream oracle (40, unique optimum).
  - It could not finish the full 64-pair `MD-00001-00000100` within minutes, so the upstream value 39 was **not reproduced**.
  - On induced sub-instances (vertices 0..N−1, unit weights), measured:

| N | Cycle cap | Cycles | Optimum | Distinct optimal cycle sets | Vertices matched in some but not all optima |
|---|---|---|---|---|---|
| 32 | 3 | 20 | 11 | 5 | 3 |
| 40 | 3 | 34 | 15 | 2 | 2 |
| 48 | 3 | 93 | 22 | 28 | 9 |
| 24 | 4 | 19 | 7 | 4 | 0 |
| 32 | 4 | 43 | 12 | 18 | 3 |
| 40 | 4 | 82 | 15 | 56 | 5 |

  Interpretation (Basis: derived from the toy model):
  - With unit weights, which pairs receive a transplant is frequently not determined by the objective.
  - The solver's branching order, presolve or relabelling (`kidney_solver -r`) decides.
  - Programmes that care about who is matched need explicit tie-breaking criteria, as the UK hierarchy does.

### 7. Performance and resource footprint across levels

| Level | Allocation scores (OPTN / transplantr) | Simulated allocation models | Kidney-exchange solvers |
|---|---|---|---|
| L1 authoring / maintenance | transplantr: 12 defects or drifts above in v0.2.0; no commits since 2020-02-28 (version drift D4, D8); OPTN guides re-issued annually (mapping tables) | the policy development that KPSAM supported was "a 9-year effort" by the OPTN committee (Israni et al.) | not measured |
| L2 build | not applicable (interpreted R) | not measured (software not public) | not measured (Gurobi/CPLEX not available) |
| L3 model build / formulation size | not applicable | not measured | Cycle-variable counts on sub-instances 19–93 (toy, measured); PIEF compactness (paper) |
| L4 run time | transliteration probe < 1 s (measured; not transplantr) | One simulated year: > 6 h → ~15 s (Pivo et al.); KPSAM 10 iterations per policy | UK: every optimum < 2 s on 2012 hardware (paper); toy enumerator 0.01–0.10 s on N ≤ 48, did not finish on N = 64 within minutes (measured) |
| L5 verification of a result | Policy worked examples reproduced (KDPI guide) by transliteration | Projections compared with observation post hoc (ATC 2016) | `kidney_utils.check_validity` checks feasibility, not optimality |
| L6 memory | not measured | not measured | toy enumerator ≤ 33 MB max RSS (measured) |

### 8. Comprehensibility and conceptual simplicity

- **C1, human legibility.**
  - Policy text is legible but scattered. MELD's rounding rule ("rounded to the tenth decimal place and then multiplied by 10") is easy to misread, and the D1 misreading is exactly this. Sodium bounds appear in a separate sentence from the formula.
  - Units are implicit: OPTN uses mg/dL, while UK formulas use µmol/L. Unit errors (D5, D10) are silent because every intermediate value stays numerically plausible.
  - KPSAM's iteration range looks like a confidence interval but explicitly is not one.
  - Lexicographic objectives (UK) are legible to clinicians as priorities. A single weighted objective with tiny weights achieving the same order is not.
- **C2, one invariant, many mechanisms.**
  - Each score is "a fitted linear predictor with clamped inputs, mapped to a rank". The clamps, rounding and percentile maps are where implementations diverge.
  - A minimal shared abstraction is `score = round_policy(clamp_policy(units_policy(inputs)) · β)`, with the three policy maps versioned together with β.
  - transplantr keeps β in code but scatters the three maps: per-function `units` flags, inconsistent clamps between `meld` and `meld_na`, and no policy version.
  - For kidney exchange, the "solution" abstraction needs an explicit tie-break or a canonical order. Otherwise the objective under-determines the outcome (§6 toy).

### 9. How implementations and policy changes are validated

- **V1, specification adequacy and mutation.**
  - The upstream transplantr tests check one point per function. Only tests at clamp boundaries would detect D2 and D3, and only a test of the US-units path would detect D5.
  - The OPTN KDPI guide's worked example is a golden test that any implementation can reproduce. The transliteration reproduces `Xβ` and both KDRI values to all printed digits.
- **V2, differential testing.**
  - `kidney_solver`'s tests are differential: all formulations must agree on the optimum (`test_weighted_instance`), and relabelling must not change it (`test_relabelled_solve`).
  - No such differential suite exists in `KidneyExchange`, whose edge formulation is a stub.
  - The transliteration is a differential oracle against R only to the extent of the three upstream test values it reproduces.
- **V3, stochastic and time-limit behaviour.** Neither solver turns "time limit reached" into an error. Programme operators must check status codes. KPSAM's randomness covers only donor order and acceptance draws.
- **V4, field replay.**
  - The KAS evaluation compares simulated with observed cohorts after the fact (ATC 2016; Stewart et al. 2016). The LSAM pediatric study replays real offers against the acceptance model (AUC).
  - Behavioural response (listing, acceptance) is the dominant unmodelled factor named by the model's own authors.

## Boundaries

- **Not examined.**
  - transplantr executed in R. All transplantr effects are from a Python transliteration, verified only against the package's three numeric MELD/UKELD test values.
  - The SAM software (LSAM, KPSAM, TSAM). Its source is not public.
  - The full text of Kim et al. 2008 and 2021, Rao et al. 2009, Rana et al. 2008, Thompson et al. 2004, Abraham et al. 2007, Dickerson et al. 2016, Constantino et al. 2013 and Biró et al. Abstracts only.
  - OPTN's annual KDPI and EPTS mapping-table PDFs. The 2024 KDPI value 72 is the guide's stated result.
  - Gurobi or CPLEX runs of either solver.
  - PELD Cr in detail.
  - The UK 2019 deceased-donor kidney scheme, and the UK KDRI functions in transplantr.
- **Unknown.**
  - Which year's OPTN tables transplantr's `kdpi_lookup` and `epts_lookup` reproduce. The package documents a 2018 scaling factor of 1.250609 and, in a vignette, 1.250697 for 2019.
  - Whether Rana et al. assign 2 points to previous abdominal surgery. If so, D10 and D11 cancel exactly in the package's SOFT test case (7 points either way). This was not verified.
  - The exact MELD-Na equation printed in the body of Kim et al. 2008. transplantr's 140-based form is the commonly cited one. The abstract states only the 125–140 sodium range.
  - The upstream optimum 39 for the full `MD-00001-00000100` instance was not reproduced by the toy enumerator.
- **Known not to apply.**
  - transplantr's KDRI/KDPI is not the current OPTN KDPI (race and HCV removed October 31, 2024; coefficients changed).
  - transplantr's `meld_na` is not the OPTN MELD-Na equation.
  - Neither package computes MELD 3.0.
- **Unsupported.** `KidneyExchange`'s edge formulation (returns `null`). `kidney_solver`'s failure-aware mode for formulations other than `cf` and `picef`.
- **Stronger conclusions not established.**
  - That SAMs are systematically conservative for all policies. The direction-but-not-magnitude result is one abstract on one policy.
  - That any programme actually suffered a suboptimal match from a solver tolerance. The tolerance paths are shown in code. No incident was examined.
  - That ties change real outcomes. The toy uses unit weights and sub-instances; real programmes use weights and tie-breakers.

## Evidence

Evidence acquired 2026-11-20 (UTC).

- **Git sources** (full revisions in `REPORT.json`):
  - `johnasher/transplantr`:
    - `R/liver.R` lines 20–31 (UKELD), 51–57 (UKELD_US), 82–102 (MELD), 151–174 (MELD-Na), 230–242 (PELD);
    - `R/liver_scores.R` lines 122–135 (`p_soft`), 200–210 (`soft2`), 283–296 (`soft`);
    - `R/uskdri.R` lines 7–9 (scaling note), 38–57 (`uskdri`), 132–135 (`kdpi`), 195–304 (`kdpi_lookup`);
    - `R/epts.R` lines 23–33 (`raw_epts`), 85–192 (`epts_lookup`);
    - `R/unit_conversion.R`;
    - `tests/testthat/test_liver.R`, `test_units.R`;
    - `DESCRIPTION` (`Version: 0.2.0`).
  - `jamestrimble/kidney_solver`:
    - `README.md`;
    - `kidney_solver/kidney_ip.py` lines 149–157, 504–558, 566–614;
    - `kidney_solver/kidney_digraph.py` 22–32;
    - `kidney_solver/kidney_solver.py` 43–58, 104;
    - `kidney_solver/kidney_utils.py` 11–61;
    - `tests/test_ip.py`;
    - fixtures `test-fixtures/MD-00001-00000100.input` (sha256 `1d7f88636b9c2378f0827ab9289968697205f8b275f44c0f2323644127e1d3d3`) and `test-fixtures/two_2cycles.input`.
  - `JohnDickerson/KidneyExchange`:
    - `src/edu/cmu/cs/dickerson/kpd/solver/CPLEXSolver.java` 25–66;
    - `Solver.java` 9–38;
    - `CycleFormulationCPLEXSolver.java` 55;
    - `EdgeFormulationCPLEXSolver.java` 15–31;
    - `fairness/solver/FairnessCPLEXSolver.java` 26–200.
- **OPTN documents.**
  - Policy notice: https://www.hrsa.gov/sites/default/files/hrsa/optn/policy-guid-change_impr-liv-alloc-meld-peld-sta-1a-sta-1b_liv.pdf (Board approved June 27, 2022).
  - KDPI guide: https://www.hrsa.gov/sites/default/files/hrsa/optn/kdpi_guide.pdf ("Updated: April 23, 2026").
  - EPTS guide: https://www.hrsa.gov/sites/default/files/hrsa/optn/epts_guide.pdf ("Updated: April 07, 2026").
  - HRSA MELD and KDPI calculator pages (effective date July 13, 2023; refit date October 31, 2024).
- **Other documents.**
  - IBM CPLEX 22.1.1 "relative MIP gap tolerance" ("default: 1e-04").
  - Gustafson et al., "Projection versus Reality: KPSAM and KAS", Am J Transplant 2016;16(suppl 3), abstract C72 (https://atcmeetingabstracts.com/abstract/projection-versus-reality-kpsam-and-kas/).
  - Manlove and O'Malley, technical report TR-2012-330, University of Glasgow (https://www.dcs.gla.ac.uk/~davidm/pubs/9383.pdf).
  - R 4.3.0 NEWS (`&&`/`||` length rule; documentation only).
- **Literature.** DOIs and arXiv identifiers are in `REPORT.json`. Every DOI was confirmed as registered through the doi.org handle API, and bibliographic data was matched against OpenAlex records. Full text was read for:
  - Israni et al. 2014 (PMC);
  - Wood et al. 2021 (PMC);
  - Rose et al. 2024 and Pivo et al. 2025 (abstracts with numbers);
  - the Manlove and O'Malley technical report.
- **Execution** (scripts and raw outputs in `support/`):
  - `python3 transplantr_translit_probe.py` → `support/transplantr_translit_probe.out` (fetches R sources at the pinned revision);
  - `bash cycle_packing_toy.sh` → `support/cycle_packing_toy.out`.

## Revalidation

- **transplantr.** Diff `R/liver.R` lines 82–173 and `R/epts.R` lines 23–33 and 185–192 at the new revision. Then rerun `support/transplantr_translit_probe.py`.
  - The parse line must report `missing percentile values in 0..100: [99]` while D7 holds.
  - Better: run the package in R ≥ 4.3 on the same inputs to replace the transliteration with execution.
  - The cheapest single check for D5 is `ukeld_US(1.0, 212/17.1, 54/88.4, 126)`. A correct implementation returns 63.22.
- **OPTN policy.** Re-read Policy 9.1.D in the current OPTN policies PDF (rounding, bounds, constants) and the KDPI guide's Table 1 and worked example. If the guide's example still yields 72%, the refit coefficients in §2 still apply.
- **SAM agreement.** No cheap check exists. A new post-implementation evaluation is required for each policy change.
- **Solvers.** Re-grep `kidney_ip.py` for `mipGap` and `timelimit`, `CPLEXSolver.java` for `if(getRelativeMipGap() > 0)`, and `EdgeFormulationCPLEXSolver.java` for `return null;`.
- **Tie probe.** Run `support/cycle_packing_toy.sh`. The distinct-optima counts in §6 must match. This revalidates only the toy model.
