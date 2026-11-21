# Highway bridge load rating (LRFR) and its calibration, the I-35W gusset-plate and FIU pedestrian-bridge collapse investigations, the Morandi viaduct, and checking pycba influence lines against closed-form solutions

## Summary

- **Rating equation (AASHTO *Manual for Bridge Evaluation*, MBE, LRFR; read through public secondary documents):**

  `RF = (C − γDC·DC − γDW·DW ± γP·P) / (γLL·(LL + IM))`, with `C = φc·φs·φ·Rn` and `φc·φs ≥ 0.85`.

  - Design-load rating with HL-93 uses `γLL = 1.75` (inventory, target reliability β = 3.5) or `1.35` (operating, β = 2.5).
  - The legal-load factor was originally tied to truck traffic (ADTT): 1.80 above 5000 trucks per day, 1.65 at 1000, 1.40 below 100. A current state manual instead uses a single 1.45.
  - Condition factors are 1.00, 0.95 and 0.85 for good, fair and poor members; system factors run from 0.85 (non-redundant) to 1.00.
  - For legal-load posting: `Posting = (W/0.7)·(RF − 0.3)` when `0.3 < RF < 1.0`; close the bridge when RF < 0.3.
- **I-35W, Minneapolis, 2007 (NTSB/HAR-08/03).** 13 people died and 145 were injured.
  - Probable cause: a design error left the U10 gusset plates with inadequate capacity. They failed under (1) dead-load increases from earlier modifications (+13.4% in 1977, +6.1% in 1998) and (2) traffic plus 578,735 lb of construction material and equipment staged near pier 6.
  - Contributing: neither the design firm's quality control nor the Federal and State design review caught that the main-truss gusset calculations had not been performed.
  - Rating practice excluded gusset plates: the rating software (BARS, Virtis) could not model them, and the 1979 and 1995 ratings did not evaluate them. Bowing visible in 1999 and 2003 photographs was never recorded.
  - Afterwards FHWA issued gusset-plate rating guidance with explicit resistance checks (FHWA-IF-09-014).
- **FIU pedestrian bridge, Miami, 2018 (NTSB/HAR-19/02).** 6 people died.
  - Probable cause: load and capacity calculation errors at the member 11/12 nodal region. Demand was underestimated by 46% (the actual demand was nearly twice the calculated value), and capacity was overestimated by using a 1.25 rather than a lower-bound dead-load factor in the clamping force.
  - The independent peer review analysed the structure as a whole, not its nodes or construction stages, and the reviewing firm was not prequalified for the work type.
  - Cracks more than 40 times generally acceptable widths were judged "not a safety issue"; a member was re-tensioned with the road open.
- **Morandi/Polcevera viaduct, Genoa, 2018.** Read as abstract only: 43 deaths and about 243 m collapsed; a 1990s strengthening was carried out and a later strengthening project was never built.
- **Cross-case pattern (derived).** In each investigated case the decisive error sat in a connection or node that the global member-level analysis, the rating software or the independent review did not model. Independent checking that reuses the same structural idealisation cannot detect such errors.
- **pycba 1.0.2 (pinned) against closed forms.**
  - Moment and reaction influence lines are exact to about 1e-15 at sections on the result grid, for a simple span and for a two-span continuous beam.
  - A point of interest off the grid silently snaps to the nearest result section: on a 20 m span with 100 points per member, a POI at 7.33 m is evaluated at 7.40 m (peak error +0.81%).
  - Calling `create_ils` twice leaves `pos` twice as long as the ordinates.
  - Moving-load envelopes underestimate the true maximum unless the step hits the governing position: −0.24% at steps of 0.25–1.0 m and −0.007% at 0.1 m for the HL-93 truck on 20 m. Because RF ∝ 1/LL, this error is unconservative by the same relative amount.
  - The library's HL-93 truck uses SI-edition loads (35/145/145 kN), giving 1.4% higher truck moments than 8/32/32 kip.

## Applicability

- **Rating method.** The LRFR equation, factors and reliability targets come from two public documents: the Wisconsin DOT Bridge Manual, Chapter 45 (edition dated July 2026), which quotes MBE Eq. 6A.4.2.1-1 and also states WisDOT policy values; and FHWA/NHI Course 130092 "LRFR of Highway Bridges" slides (April 2008), which reflect the 2003 Guide Manual and the first-edition MBE. The MBE itself was **not examined**. Where the two sources differ (legal-load factors; the condition factor, which WisDOT policy sets to 1.0), both are reported and attributed. Factor values are therefore edition-specific.
- **Collapse findings.** These come from NTSB/HAR-08/03 (the text extraction reached printed p. ≈69), the NTSB recommendation letter H-08-20 through -25, NTSB/HAR-19/02 (reached printed p. ≈62) and its NTSB digest SPC-20/02 (full text), FHWA Technical Advisory T 5140.29 and FHWA-IF-09-014 (read from an unofficial mirror; see **Boundaries**). The FIU-related finite-element and "FHWA postcollapse check" numbers are as quoted by NTSB.
- **Journal papers.** Nowak 1995, Minervino et al. 2004, Hao 2010, Liao et al. 2011 and Calvi et al. 2019 were read as abstracts only.
- **Execution.** All execution results are for `ccaprani/pycba` at the pinned revision (package 1.0.2), with CPython 3.13.15, numpy 2.5.4 and scipy 1.18.1 on a Linux x86-64 workstation with 4 BLAS threads; each run took ≤ 60 s and < 200 MiB RSS. The closed-form references are independent Python implementations of Euler–Bernoulli statics and the three-moment equation, written for this report (support `pycba_*.py`). They check pycba; they are not themselves upstream artefacts.

## Findings

### 1. LRFR rating equation, levels and factors

Basis: documentation (WisDOT Bridge Manual Ch. 45, July 2026, §45.3.7 and Tables 45.3-1 to 45.3-4; FHWA/NHI 130092 LRFR slides, April 2008).

| Element | Value | Source and edition note |
|---|---|---|
| General equation | `RF = (C − γDC·DC − γDW·DW ± γP·P) / (γLL·(LL+IM))`, `γP = 1.0` | WisDOT §45.3.7, citing MBE Eq. 6A.4.2.1-1 |
| Capacity | `C = φc·φs·φ·Rn`, lower limit `φc·φs ≥ 0.85` (strength) | WisDOT; NHI marks φc, φs as "optional" |
| Dead-load factors (Strength I) | DC 1.25, DW 1.50 | WisDOT Table 45.3-1 |
| Design load (HL-93), inventory / operating | γLL 1.75 / 1.35; β 3.5 / 2.5 | NHI slides; WisDOT Table 45.3-1 |
| Legal loads | 1.80 (ADTT > 5000), 1.65 (ADTT = 1000), 1.40 (ADTT < 100), interpolated; β = 2.5 | NHI 2008 (early-MBE values) |
| Legal loads (current state manual) | 1.45 (AASHTO legal, state, lane-type, SU4–SU7); 1.30 for FAST Act emergency vehicles | WisDOT Table 45.3-2; the MBE revision behind 1.45 was not examined |
| Permit loads | routine/annual β = 2.5; special β = 3.5. WisDOT: annual 1.30, single-trip mixed 1.20, escorted 1.10 | NHI; WisDOT Table 45.3-3 |
| Condition factor φc | good/satisfactory 1.00, fair 0.95, poor 0.85 (or NBI superstructure rating 6+/5/4) | NHI; WisDOT policy uses 1.0 |
| System factor φs | redundant 1.00; non-redundant 0.85; riveted two-girder/truss 0.90; multiple-eyebar truss members 0.90; floorbeams spaced > 12 ft 0.85. Not for shear ("shear failures tend to be brittle") | NHI (basis NCHRP Report 406); WisDOT Table 45.3-4 adds girder-count cases |
| Posting | `Posting load = (W/0.7)·(RF − 0.3)` for `0.3 < RF < 1.0`; close when RF < 0.3 for all three AASHTO legal loads | NHI slide; MBE equation number not found |

Pre-LRFR heritage (Basis: documentation, HAR-08/03 p. 35): allowable-stress rating (AASHO 1970), with load-factor rating added in 1978; the *Manual for Condition Evaluation* general form `RF = (C − A1·DL)/(A2·LL)` and rating tonnage `RT = RF·W` (Minnesota used HS20 = 36 tons). The 2003 LRFR Guide Manual was combined with these into the MBE in 2008.

Derived consequences:
- RF is linear in capacity and inversely proportional to the live-load effect, so a relative error ε in `LL+IM` gives a relative error of about −ε in RF.
- Because `φc·φs ≥ 0.85` clamps the product, a poor member (0.85) in a non-redundant bridge (0.85) is rated with 0.85 rather than 0.7225.
- The condition factor was intended to raise reliability "from 2.5 to a target of 3.5" for deteriorated members (NHI slide).

### 2. Calibration

Basis: documentation (NHI slides; abstracts of Nowak 1995 and Minervino et al. 2004).

- Bridges designed to the older Standard Specifications had reliability indices "ranged from 1.5 to 4.5". LRFD selected β = 3.5 ("1 in 10,000 notional failure probability"), and evaluation uses β = 2.5 ("1 in 100").
- Nowak (1995, abstract) derives load and resistance factors so that the reliability of designed bridges reaches "the predefined target level". He proposes a new live-load model "which provides a consistent safety margin for a wide spectrum of spans", includes a dynamic load model, and summarises resistance statistics for four material and structure classes.
- Minervino et al. (2004, abstract): the LRFR Guide Manual, completed in March 2000 under NCHRP and adopted in 2002, extends LRFD "to the areas of inspection, load rating, posting and permit rules, fatigue evaluation, and load testing".
- The numerical target β = 3.5 is **not** stated in either abstract; it comes from the NHI slides.

### 3. I-35W (NTSB/HAR-08/03): findings classified

Basis: documentation (NTSB report Executive Summary and Factual sections; NTSB letter H-08-20 through -25; FHWA T 5140.29; investigation-team conference paper by Schultheisz, Kushner, Nakamura, Ocel, Wright and Li).

Probable cause, verbatim in part: "the inadequate load capacity, due to a design error by Sverdrup & Parcel and Associates, Inc., of the gusset plates at the U10 nodes, which failed under a combination of (1) substantial increases in the weight of the bridge, which resulted from previous bridge modifications, and (2) the traffic and concentrated construction loads on the bridge on the day of the collapse." Corrosion at L11, floor-truss fracture, preexisting cracking, temperature and pier movement were considered and excluded.

| Factor | Category | Evidence |
|---|---|---|
| No main-truss gusset calculations in the design records. FHWA's design check found shear demand/capacity ratios above 2 at U4, U10 and L11, plates "only half as thick as necessary" (allowable 15 ksi vs 30 ksi demand), and yielding under the original 1967 dead load. A University of Minnesota study (CTS 09-29) describes U10W as "a pair of 0.5-inch-thick gusset plates of ASTM A441 grade 50 steel" | design calculation | probable cause; team paper (FHWA check); CTS 09-29 §2 |
| The design firm's QC did not ensure the gusset calculations were done | checking/review | probable cause |
| Mn/DOT and FHWA predecessors reviewed the design in 1962–65; Mn/DOT's procedures for checking consultants' computations "were not applied to gusset plates". 10 of 14 surveyed States had approved designs later found deficient | checking/review | letter pp. 2–3 |
| Ratings excluded gusset plates. Superstructure rating 2002–2007: inventory 36.0 t (HS20) / operating 59.4 t (HS33). BARS and Virtis "had no provision for including gusset plates"; the MCE gave no connection method. No requirement existed to rate a new bridge before service | rating practice | report pp. 31–40; H-08-21 |
| Dead load +3 million lb (+13.4%) in 1977 (≈ 8.7 in. average deck); +1.13 million lb (+6.1%) in 1998; post-accident analysis used +19.5% | loading | report pp. 23, 31 |
| 383,200 lb of aggregates plus 195,535 lb of vehicles, equipment and people (578,735 lb) over the inner west side just north of pier 6; whole-bridge load 1,260,326 lb | loading | report p. 28, Table 2 |
| Bowing visible in all four U10 plates in 1999 (University of Minnesota) and 2003 (URS) photographs, never noted; an inspector believed "gusset plates are overdesigned". Calculated edge displacement up to 0.82–0.99 in. (U10′W) | inspection | report pp. 61–63 |

Recommendations, verbatim and abridged, from documents actually read:
- **H-08-1 (FHWA):** load capacity calculations including gusset plates for non-load-path-redundant steel truss bridges whenever modifications may significantly increase stresses.
- **H-08-17 (FHWA) / H-08-20 (AASHTO):** a design QA/QC program that verifies "that the appropriate design calculations have been performed, that the calculations are accurate".
- **H-08-21:** load ratings of new bridges before service.
- **H-08-22:** include gusset-plate capacity in MBE load ratings of non-load-path-redundant steel trusses.
- **H-08-23:** update the MBE with the joint FHWA–AASHTO gusset study.
- **H-08-24:** construction-load guidelines.
- **H-08-25:** make gusset plates a CoRe element.
- FHWA's 2011 QC/QA guidance answering H-08-17 says it "is not intended to be a mandated national standard".

Post-collapse analyses:
- **Liao et al. 2011 (abstract):** "substantial portions of the U10 gusset plates were yielded at the time of collapse"; the deck weight increase, the staged construction load and insufficient thickness were the main factors; compression–shear interaction "played an important role".
- **Hao 2010 (abstract):** plate thicknesses were "designed proportional to the bending moment solution of a one-dimensional influence line analysis", with insufficient consideration of diagonal forces. A 3-D nonlinear FE rating showed some gusset plates "had almost reached their yield limit" under the design load.
- **Investigation-team paper:** members were "at the most about 5 percent above their design loads" at collapse; the collapse was "triggered by a local bending instability in the U10W gusset plates".

### 4. Gusset-plate rating guidance after I-35W

Basis: documentation (FHWA T 5140.29, 2008-01-15; FHWA-IF-09-014, February 2009, unofficial mirror; equations partly garbled in extraction).

- **T 5140.29** "strongly encouraged" owners to check gusset capacity in initial ratings of new or replaced non-load-path-redundant trusses and in future recalculations, and to review past ratings. It is an advisory, not a requirement.
- **FHWA-IF-09-014** covers LRFR (Part A) and LFR (Part B); no allowable-stress part was found. Connection resistance is the lesser of the fasteners and the plate; plate resistance is the least of tension, block shear, shear and compression. LRFR checks the strength limit state only.

| Check (LRFR) | Equation | φ |
|---|---|---|
| Rivet shear | `R = φF·m·Ar`; φF = 18 / 21 / 27 / 32 ksi by rivet age and grade; ×0.80 for connections > 50 in. long | — |
| Gross-section yield (Whitmore width, 30°) | `Pr = φy·Fy·Ag` | 0.95 |
| Net-section fracture | `Pr = φu·Fu·An·U`, U = 1.0 | 0.80 |
| Block shear | `Atn ≥ 0.58·Avn`: `φbs(0.58·Fy·Avg + Fu·Atn)`; else `φbs(0.58·Fu·Avn + Fy·Atg)` | 0.80 |
| Shear yield (gross) | `φvy·0.58·Fy·Ag·Ω`, Ω = 1.00 (stiff enough) or 0.74 | 0.95 |
| Shear fracture (net) | `φvu·0.58·Fu·An` | 0.80 |
| Compression | idealised column on the Whitmore width; `Lc` = mean of three distances; K from 0.65 to 2.1 | 0.90 (example) |

Flexure–axial interaction is "questionable and not required". Worked examples: LRFR inventory RF 1.06 for HL-93 and LFR inventory RF 1.27 for HS20, both governed by block-shear rupture at the end of member 5. The LFR example reduces capacity by 10% because gusset failure in a non-redundant structure may collapse the bridge.

### 5. FIU pedestrian bridge (NTSB/HAR-19/02): findings classified

Basis: documentation (NTSB report Executive Summary and §§1.7–1.9; NTSB digest SPC-20/02).

Probable cause, verbatim in part: "the load and capacity calculation errors made by FIGG Bridge Engineers, Inc., … in its design of the main span truss member 11/12 nodal region and connection to the bridge deck. Contributing … was the inadequate peer review performed by Louis Berger … Further contributing … was the failure of the FIGG engineer of record to identify the significance of the structural cracking … and to obtain an independent peer review of the remedial plan". The 174-ft span fell about 18.5 ft onto SW 8th Street. One worker and five vehicle occupants died; one westbound lane and all five eastbound lanes were open.

| Factor | Category | Evidence |
|---|---|---|
| FHWA post-collapse check: interface-shear demand at node 11/12 underestimated by 46% ("nearly twice"; nearly 10× at node 10/11). Design used LUSAS model results, although LARSA results with larger nodal demands were available | design calculation | digest p. 7; report p. 44 |
| Clamping force `Pc` in `Vni = c·Acv + μ(Avf·fy + Pc)` used the maximum dead-load factor 1.25 and included non-permanent loads; FHWA recommends 0.90 (at most 1.0) | design calculation | report p. 46; digest p. 7 |
| Plans did not call for roughening deck–diagonal cold joints, though node 11/12 would have been under-designed even if roughened; no redundant load path | design calculation (detailing, system) | digest pp. 5, 10; report p. xvi |
| Peer review (ADINA) "analyzed the entire structure as one unit" but not nodes or construction stages ("not part of our scope"); no 90% certification letters; the firm was not FDOT-prequalified for work type 4.3.1 | checking/review | report pp. 50–52 |
| Member 11 post-tensioning rods re-tensioned to 280 kips on a cracked node without independent review | loading (construction) | report pp. 33, 39 |
| Cracks over 40× typical acceptable widths (the digest says 45×), worsening after detensioning on March 10; judged "not a safety issue" on March 13 and 15; work not stopped and road not closed | inspection / response to distress | report pp. 33–37; digest p. 4 |
| Load rating | rating practice | not applicable (bridge under construction); no rating finding in the text read |

Recommendations: H-19-24 (FHWA) and H-19-30 (AASHTO) call for reasonable estimates of interface-shear demand, cohesion, friction and clamping force. H-19-25 to H-19-29 (FDOT) require that peer review check "all nodal forces", require prequalification letters, require closure when cracks are detected, and add a redundancy discussion. H-19-31/32 add redundancy discussion to the AASHTO LRFD and pedestrian-bridge guides. H-19-33/34 (FIGG) cover training on `Pc` and prequalification checks.

### 6. Morandi (Polcevera) viaduct

Basis: documentation (Calvi et al. 2019, abstract only). The collapse occurred on 14 August 2018 at 11:35 AM. About 243 m fell and 43 people died. The bridge was designed in the early 1960s and opened in 1967. The collapsed part was a self-standing structure spanning 171 m plus two simply supported Gerber spans of 36 m. The paper covers the 1990s strengthening, subsequent monitoring, and a strengthening project "never brought to fruition". It is "based entirely on publicly available material" because the debris was classified. Its design assumptions, deterioration mechanisms and maintenance details beyond the abstract were **not examined**.

### 7. Cross-case synthesis: what independent checking could and could not see

Basis: derived from Findings 3 and 5.

| Check | I-35W | FIU |
|---|---|---|
| Global member analysis | members within design loads ("about 5 percent above" at collapse) | the whole-structure peer-review model passed |
| What failed | connection plate (U10) | node/connection interface (11/12) |
| Did the checking tool model the failed element? | no (BARS/Virtis could not; State review procedures "not applied to gusset plates") | no (peer-review scope excluded nodes and stages) |
| Observed distress | bowing photographed in 1999 and 2003, not recorded | cracks over 40× acceptable; judged safe |
| Load added at failure | +19.5% dead load plus 578,735 lb staged | re-tensioning of member 11 to 280 kips |

Both independent checks reused the global idealisation of the original design, so they could not detect a connection-level error by construction. NTSB's recommendations add requirements to model the failed element class (H-08-22; H-19-25 "all nodal forces"). The model-refinement point: "verify every load-path element at its own limit state" is one invariant. Member checks, gusset checks and node interface-shear checks are instances of it, not separate special cases.

### 8. pycba: method and checks against closed forms

Basis: source (`src/pycba/inf_lines.py`, `bridge.py`, `vehicle.py`, `beam.py`, `analysis.py`) + execution (support `pycba_il_check.py`, `pycba_continuous_check.py`, `pycba_state_probe.py`).

Method:
- `BeamAnalysis` uses the direct-stiffness method with prismatic or non-prismatic elements. `analyze(npts)` recovers M, V and deflection at `npts` (default 100) points per member and returns 0 or raises.
- `InfluenceLines.create_ils(step)` marches a unit point load in `step` increments (default L/100) and stores one full analysis per position. `get_il(poi, 'M'|'V'|'R'|'MR')` reads the effect at the result point nearest `poi`: `idx_in_span = np.abs(span_x[1:-1] - poi).argmin() + 1` (line 143).
- `BridgeAnalysis.run_vehicle(step)` places the front axle at `pos_start + i·step`, superimposes on-deck axle loads, and builds `Envelopes` (max/min per section) from all positions.
- `VehicleLibrary.US.get_hl93_truck(rear_spacing=4.3)` is `Vehicle([4.3, s], [35, 145, 145])` (kN, m); `get_hl93_tandem()` is two 110 kN axles at 1.2 m.

| Check | Closed form | pycba result |
|---|---|---|
| Simple span 20 m, M IL at a = 10 and a = 6 (step 0.1) | `x(L−a)/L` / `a(L−x)/L` | max error 1.5e-15 |
| Same, a = 7.33 (off the 0.2 m result grid) | peak 4.62455 | section 7.40 used; peak 4.662; max error 0.0441 (+0.81% of peak) |
| Left reaction IL | `1 − x/L` | 3.3e-16 |
| Two equal spans 2×20 m, M at interior support | `−x(L²−x²)/(4L²)`; min −L/(6√3) = −1.924501 at x = 11.547 | error 6.7e-16 on the grid; grid minimum −1.924453 at 11.5 |
| Two spans, M at 0.4L | simple-span IL + `M_B·a/L` | 1.3e-15 |
| HL-93 truck, 20 m simple span, absolute max M | resultant theorem 1246.605 kN·m | step 1.0 / 0.5: 1243.615 (−0.240%); 0.25: −0.236%; 0.1 / 0.05: 1246.520 (−0.007%, limited by the 0.2 m section grid) |
| HL-93 truck, 2×20 m: min M at support / max M at 0.4L | 200,001 + kink positions: −571.5525 / 963.7915 kN·m | step 0.5: +0.0294 / −1.2883; 0.1: +0.0081 / 0.0000; 0.02: +0.0002 / 0.0000 |
| POI 3.33 m on 10 m span, peak ordinate vs `npts` | 2.22111 | npts 10: 2.100 (x = 3.0); 20: 2.275 (3.5); 100: 2.211 (3.3); 1000: 2.22111 |

Defects and hazards at the pinned revision (quoted source):
- **IL state not reset:** `self.pos = []` is set only in `__init__` (line 44); `create_ils` resets only `self.vResults = []  # reset` (line 69) and then calls `self.pos.append(pos)` (line 79). Execution: after a second `create_ils(step=0.5)`, `get_il` returns `len(x) = 42` against `len(eta) = 21`. `BridgeAnalysis.run_vehicle` does reset `self.pos`.
- **Silent POI snapping:** no warning when `poi` is off-grid. The upstream regression test for off-grid POIs asserts only `np.linalg.norm(y) > 0`.
- **Dead-code diagnostic:** `bridge.py` line 434 is `raise ValueError("Bridge analysis did not succeed at {pos=}")`, without the `f` prefix, while line 585 in `run_load_model` has it. Because `analyze()` returns 0 or raises, this branch is unreachable in practice.
- **Docstring mismatch:** `get_local_span_coords` documents "The index (1-based)" (line 515), but the code returns 0-based indices that callers increment.
- **Envelope sampling:** sampling can only underestimate a maximum. The error vanishes only when a step hits the governing axle position and the section lies on the result grid.
- **Unit edition:** the SI-edition HL-93 truck gives 1.36–1.44% larger absolute truck moments than 8/32/32 kip at 14 ft for 10–40 m spans (Basis: derived; support `hl93_si_vs_customary.py`). Lane load (9.3 kN/m) and IM (33%) are left to the caller.

### 9. Performance and resource footprint (L1–L6)

| Level | Quantity | Value | Basis |
|---|---|---|---|
| L1 | pycba source size | 13,788 lines of Python (installed package) | measured (`wc -l`) |
| L1 | effort to rate a bridge, or for an LLM to do so | not measured | — |
| L2 | pycba install (pure Python; numpy/scipy/matplotlib prebuilt binary packages) | build time not measured; installed size 1,140 KiB | measured (`du -sk`) |
| L3 | `import pycba` (cold) | 1.22 s, 104.8 MiB RSS | measured |
| L4 | one static analysis inside an IL or moving-load loop | 0.34 ms per unit-load position (201 in 0.069 s, simple span); 0.59–0.67 ms per truck position on 2×20 m (2,431 in 1.531 s); 1.4–1.5 ms per position on the 20 m span, where `tracemalloc` was active | measured |
| L4 | upstream tests `test_inf_lines.py` + `test_bridge.py` | 18 passed in 26.25 s | measured |
| L5 | proof/certificate checking | not applicable | — |
| L6 | peak RSS of the probes | 128 MiB (IL check), 171 MiB (continuous), 183 MiB (state probe), 275 MiB (pytest) | measured |
| L6 | Python peak traced allocation in `run_vehicle` | 0.3 MB (30 positions) to 5.9 MB (573 positions), linear in positions | measured (`tracemalloc`) |
| — | Commercial rating software (BARS, Virtis) | not measured | — |

### 10. Comprehensibility and conceptual simplicity (C1–C2)

- **C1.** The RF equation has about 8 symbols and is locally auditable. The hidden complexity sits in what "C" covers. A rating is only as complete as the list of limit states and elements checked: gusset plates were outside that list until 2008–2010, and node interface shear was outside the FIU review's scope. Diagnostic legibility in pycba is good for the global analysis (exact ILs) but weak at the edges: silently snapping a POI, and a mismatched `x`/`eta` pair after reuse, are both quiet failures.
- **C2.** A single abstraction removes the special cases: every load-path element `e` gets `RF_e = (C_e − Σγ·D_e)/(γLL·L_e)`, where `L_e` comes from that element's own influence surface. The bridge rating is then `min_e RF_e`. Members, gussets, nodes and bearings are instances of `e`. In pycba, accepting an exact `poi` as an extra result station (as the `shear_points` mechanism already does for shear) would make off-grid POIs an ordinary case rather than a snapping exception.

### 11. Validation coverage (V1–V4)

- **V1 specification adequacy.** The closed-form oracles here kill the snapping and envelope-sampling deviations. The upstream IL tests are regression goldens plus norm-positivity checks, which would not detect a wrong section.
- **V2 independent checking.** NTSB's findings are V2 failures in practice: independent review that shares the designer's idealisation (FIU) or skips an element class (I-35W) cannot catch the defect. NTSB's remedies require element-class coverage ("all nodal forces"; gusset plates in ratings).
- **V3.** Not applicable (no concurrency); fatigue and crack growth were not examined.
- **V4 field evidence.** Photographs (I-35W bowing) and crack monitoring (FIU) were physical evidence that contradicted the model. Neither was turned into a model-validity trigger; NTSB recommendation H-19-27 makes crack detection a mandatory stop-and-close trigger.

## Boundaries

- **Not examined:**
  - the AASHTO MBE text itself (any edition), including its gusset-plate provisions added after 2008;
  - NCHRP Reports 368, 406 and 454;
  - the numbered Findings and Analysis chapters of both NTSB reports beyond the printed pages listed in **Applicability** (for I-35W, the 0.5-in. U10 plate thickness is quoted from CTS 09-29, not from the NTSB text read);
  - the full texts of Nowak 1995, Minervino et al. 2004, Hao 2010, Liao et al. 2011 and Calvi et al. 2019;
  - Morandi design and deterioration details (stay construction, tendon corrosion, pier-specific retrofits);
  - FHWA's 2019 post-collapse report as a standalone document;
  - the official FHWA-IF-09-014 PDF, which failed to download, so equations were read from an unofficial mirror with garbled symbols;
  - NTSB recommendations H-08-18 and H-08-19, whose text was available only through a search summary and is not quoted.
- **Unknown:** which legal-load factor set (ADTT-dependent or 1.45) a given agency applies today; whether pycba's maintainers consider POI snapping intended.
- **Known not to apply:** the closed-form checks here are linear-elastic, prismatic and statically loaded. They say nothing about pycba's non-prismatic, Timoshenko, spring-support, nonlinear or modal features.
- **Attractive but unsupported:**
  - a claim that "pycba is exact": it is exact only at grid sections and on hit positions;
  - a claim that the I-35W plates were exactly half the required thickness: this was reported by FHWA engineers in the team paper, not quoted from the NTSB text read;
  - inferring Morandi causes from the abstract.

## Evidence

Observation date for all evidence: 2026-11-21 (UTC).

- **pycba.** `ccaprani/pycba` @ `329aa6e8ce3474eae812501c31520025e9afdaa4` (package version 1.0.2; tarball from codeload.github.com, SHA-256 `7a9b664a2e0b17a4dbd97bfa7e20c09938863c912b01379038cee50436ccfbf2`):
  - `src/pycba/inf_lines.py` lines 15–194 (`InfluenceLines.__init__`, `create_ils`, `get_il`);
  - `src/pycba/bridge.py` lines 284–448 (`_axle_LM`, `_single_analysis`, `run_vehicle`), 434 and 585;
  - `src/pycba/vehicle.py` lines 10–55 (`Vehicle`) and 533–566 (`VehicleLibrary.US.get_hl93_truck`, `get_hl93_tandem`);
  - `src/pycba/beam.py` lines 502–528 (`get_local_span_coords`);
  - `src/pycba/analysis.py` lines 406–466 (`analyze`);
  - `tests/test_inf_lines.py` (`test_il_arbitrary_poi`, `test_discretization`).
- **NTSB.**
  - *Collapse of I-35W Highway Bridge, Minneapolis, Minnesota, August 1, 2007*, NTSB/HAR-08/03, adopted 2008-11-14 (ntsb.gov `HAR0803.pdf`): Executive Summary pp. xiii–xiv; pp. 23, 28, 31–40, 61–63.
  - Safety Recommendation letter H-08-20 through -25 (2008-11-21, `H08_20_25.pdf`).
  - *Pedestrian Bridge Collapse Over SW 8th Street, Miami, Florida, March 15, 2018*, NTSB/HAR-19/02 (`HAR1902.pdf`): Executive Summary pp. xiv–xvi; §§1.7–1.9, pp. 32–52.
  - Digest NTSB/SPC-20/02 (`SPC2002.pdf`): pp. 4–11.
  - No DOIs are assigned to these documents.
- **FHWA.** Technical Advisory T 5140.29 (2008-01-15; fhwa.dot.gov `t514029.cfm`). *Load Rating Guidance and Examples for Bolted and Riveted Gusset Plates in Truss Bridges*, FHWA-IF-09-014 (2009-02-01; ROSA P record dot/49981; text read from an unofficial mirror). *Guidance on QC/QA in Bridge Design in Response to NTSB Recommendation H-08-17* (Final Draft, August 2011; `h0817.pdf`).
- **Secondary rating sources.** Wisconsin DOT Bridge Manual, Chapter 45 "Bridge Rating", July 2026 edition (`ch45.pdf`). FHWA/NHI Course 130092 "Load & Resistance Factor Rating of Highway Bridges", April 2008 slides, with the FHWA memorandum of 2006-10-30 (hosted by WSDOT, `lrfrclassnotes.pdf`).
- **Investigation-team paper.** Schultheisz, Kushner, Nakamura, Ocel, Wright and Li, "Minneapolis I-35W Bridge Collapse – Engineering Evaluations and Finite Element Analyses" (SIMULIA conference paper).
- **University of Minnesota study.** Liao and Okazaki, *A Computational Study of the I-35W Bridge Collapse*, Center for Transportation Studies report CTS 09-29, October 2009 (§2, U10 plate description; no DOI).
- **Journal papers.** Every DOI was checked against the Crossref REST API on 2026-11-21 (title, authors, venue, volume, pages):
  - Nowak, *J. Struct. Eng.* 121(8):1245–1251, 1995, doi:10.1061/(ASCE)0733-9445(1995)121:8(1245);
  - Minervino, Sivakumar, Moses, Mertz, Edberg, *J. Bridge Eng.* 9(1):43–54, 2004, doi:10.1061/(ASCE)1084-0702(2004)9:1(43);
  - Hao, *J. Bridge Eng.* 15(5):608–614, 2010, doi:10.1061/(ASCE)BE.1943-5592.0000090;
  - Liao (Crossref given name "Minmao"), Okazaki, Ballarini, Schultz, Galambos, *J. Struct. Eng.* 137(1):59–68, 2011, doi:10.1061/(ASCE)ST.1943-541X.0000269;
  - Calvi, Moratti, O'Reilly, Scattarreggia, Monteiro, Malomo, Calvi, Pinho, *Struct. Eng. Int.* 29(2):198–217, 2019 (Crossref online date 2018-12-20), doi:10.1080/10168664.2018.1558033.
  - The abstracts were read through OpenAlex records mirroring the publisher abstracts.
- **Execution.** Scripts and raw outputs are in `support/` (see `support/README.md`); the host and toolchain are as in **Applicability**.

## Revalidation

- **pycba ILs:** install the tarball at a new revision and run `python3 pycba_il_check.py` and `python3 pycba_continuous_check.py`. Expect errors ≤ 1e-12 at grid POIs, the 7.33 → 7.40 snap with `npts = 100`, and the step-dependence table. Any change in `get_il` (line 143) or `analyze` defaults shifts these numbers.
- **State bug:** `python3 pycba_state_probe.py`. The bug is present while `(a)` prints `len(x)= 42 len(eta)= 21`. A one-line diff check: `grep -n "self.pos = \[\]" src/pycba/inf_lines.py` shows whether `create_ils` resets `pos`.
- **Dead-code message:** `grep -n 'did not succeed at {pos=}' src/pycba/bridge.py`.
- **Rating factors:** recheck the MBE edition in force (Eq. 6A.4.2.1-1, Tables 6A.4.2.2-1, 6A.4.2.3-1, 6A.4.2.4-1, and the legal and permit live-load factor tables) against Finding 1. Factor values change between editions and interims.
- **Investigations:** the NTSB probable-cause paragraphs and recommendation texts are fixed documents; recheck recommendation status in NTSB's recommendation database if status matters.
