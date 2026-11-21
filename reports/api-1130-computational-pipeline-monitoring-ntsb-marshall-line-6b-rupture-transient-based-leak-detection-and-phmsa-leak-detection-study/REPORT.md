# Computational pipeline monitoring for hazardous liquids: the Marshall Line 6B investigation, API RP 1130 and 49 CFR 195 obligations, the regulator's leak-detection study, and balance versus transient leak detection probed with TSNet's MOC kernels

## Summary

- **Software alarmed; the organisation did not act.** In the 25–26 July 2010 Enbridge Line 6B rupture at Marshall, Michigan, the US National Transportation Safety Board (NTSB) found that the leak detection and SCADA systems "generated alarms consistent with a ruptured pipeline". Control-centre staff attributed those alarms to column separation. They restarted the line twice, pumping about 1.5 hours of additional oil, which was 81 % of the 843,444-gallon release. The rupture was recognised only when an outside caller reported it more than 17 hours after it occurred. NTSB's probable-cause statement names inadequate training of control-centre personnel and does not name the detection algorithm. The facts it records show three further failures: the material balance system (MBS) was configured incorrectly for the restart, the MBS procedure itself declared the software "unreliable" when column separation was present, and the operator's own 10-minute shutdown rule was overridden. Basis: normative (investigation report).
- **What the regulations require.** 49 CFR 195.444(c) requires every computational pipeline monitoring (CPM) system to comply with API RP 1130 in "operating, maintaining, testing, record keeping, and dispatcher training". 195.134(c) requires new or replaced CPM components to follow RP 1130 section 4.2. The regulations set no detection-performance threshold. The 2019 final rule extended leak-detection duty to all single-phase hazardous liquid lines (deadline 1 October 2024 for pre-2019 lines) and deliberately declined to set performance criteria. The 2022 rupture rule (195.417) defines a default rupture indicator of more than a 10 % pressure loss within 15 minutes, and operators may document a different threshold. Basis: normative.
- **The regulator's own summary of its 2012 leak-detection study.** The study was commissioned under section 8 of the 2011 Act and performed by Kiefner and Associates. In the regulator's words, pressure/flow monitoring "will consistently and reliably catch large volume, uncontrolled release events such as ruptures". The same summary says that operator procedures "may have allowed ignoring alarms, restarting pumps, or opening valves during large releases", and that the same technology "can have very different results" on two different pipelines. The study's own detection statistics were **not retrievable** for this report (see Boundaries). Basis: normative (Federal Register).
- **Probe results on a toy line ([execution, toy model]).** The probe ran TSNet's own method-of-characteristics (MOC) kernels at revision `27e616a8e2048a431eed27b00a08322d49035a52`, with a harness written for this report, on a 40 km toy line:
  - A two-sided pressure rule and an uncompensated volume balance each produce false leak indications for a different operational transient: a pump-head drop trips the pressure rule, and a delivery-valve closure trips the balance.
  - The arrival-time difference of the negative pressure wave locates mid-size leaks to within about 1–3 km. It also locates operational transients at the station that caused them, which is a usable discriminator.
  - In this configuration a rupture drawing 24 % of the flow did **not** cross the 195.417 default of 10 % pressure loss within 15 minutes; one drawing 55 % did.
  - TSNet's `detect_cusum` alarms on the *undrifted* cumulative sum. At the same threshold and drift it raised 4.8 alarms per sensor-hour on pure noise, against 0.4 for the classical CUSUM.
- **Where TSNet does not transfer to crude oil.** TSNet is a water-network tool. It hard-codes water viscosity (`solver.py:33`), states pressure as metres of fluid at 1000 kg/m³, and contains **no vapour-cavity or column-separation model**: none of the 19 Python files at the pin contains "cavit", "vapor", "vapour" or "column sep". Column separation was the very condition that misled the Marshall controllers.

## Applicability

**Subjects and their relationship.** The report combines four kinds of subject:
1. A durable accident investigation: NTSB/PAR-12/01, adopted 10 July 2012, and the companion recommendation letter P-12-3 through -10.
2. US federal regulation text in 49 CFR Part 195 as rendered on the observation date, plus two Federal Register documents that state the regulator's reasoning (84 FR 52260 of 1 October 2019; 85 FR 7162 of 6 February 2020).
3. The API RP 1175 (first edition, December 2015) product sheet and table of contents, and API's 2022 publication notices for RP 1130 and RP 1175.
4. One open-source transient simulator (TSNet, `glorialulu/TSNet` at `27e616a8e2048a431eed27b00a08322d49035a52`, `setup.py` version 0.3.1), examined as source and partially executed.

The methods literature (Wang et al. 2002 and the TSNet paper) interprets the simulator and the detection principles. The NTSB findings concern one operator, one control room and one 2010 software configuration. Nothing here generalises them to other operators' CPM performance.

**Regulatory scope.** 195.444 applies to hazardous liquid pipelines carrying liquid "in single phase (without gas in the liquid)", except offshore gathering and regulated rural gathering lines. The text was observed on 2026-11-21 as amended by Amdt. 195-102 (84 FR 52296). 195.446 applies to operators whose controllers use SCADA. 195.417 and 195.418 come from Amdt. 195-105 (87 FR 20989, 8 April 2022), as amended in 2023, and exclude gathering lines. Later amendments are not covered.

**TSNet scope.** Only these TSNet functions were executed: `inner_node_steady`, `source_pump`, `add_leakage` and `dead_end` (from `tsnet/simulation/solver.py`), `burstsetting` (from `tsnet/network/control.py`) and `detect_cusum` (from `tsnet/postprocessing/detect_cusum.py`). The following were **not** executed: TSNet's WNTR-based network setup and steady-state solver (`tsnet/network/model.py`, `tsnet/simulation/initialize.py`), its main loop (`tsnet/simulation/main.py`), its quasi-steady and unsteady friction models, its surge tanks and its valves. The probe uses steady (constant Darcy *f*) friction, a flat line and a single leak node, so every probe number is a property of that configuration only.

**Host and environment for execution.** The probe ran on an x86-64 cloud VM (Intel Xeon @ 2.60 GHz, 96 vCPUs) with Python 3.13.15 and numpy 2.3.5, on 2026-11-21.

## Findings

### 1. Marshall Line 6B: sequence, interpretation, and what each failure concerned

Basis: normative (NTSB/PAR-12/01, sections 1.2 and 1.11; Executive Summary).

| Time (EDT) | Event recorded by NTSB | Concerns |
|---|---|---|
| 25 Jul 17:58 | Line 6B, 30-inch diameter, ruptures during the last stages of a planned shutdown | — |
| by 18:03 | Operator A1 receives rupture-related alarms, including a 5-minute MBS alarm ("a severe leak alarm"), low-suction-pressure alarms and six invalid-pressure alarms. NTSB: "All of the alarms were indications of the rupture." | detection worked |
| 18:05 | MBS analyst A concludes that column separation near Marshall pump station generated the MBS alarm. "Within minutes, the MBS alarm cleared on its own. (MBS alarms clear after a shutdown because the oil flow stops.)" | alarm semantics; interpretation |
| 20:00–20:30 | Handover: shift lead B1 "not informed about the previous shutdown … the MBS alarm"; no written record required | procedures |
| 21:25 on | First of several 911 odour calls; responders find nothing | public awareness |
| 26 Jul ~04:04 | First restart. By 04:12 a 5-minute MBS alarm appears. The analyst says column separation, then realises "the MBS software had not been set up correctly" because Niles pump station was out of service and its pressure transmitters sat behind closed valves. | software configuration |
| 04:24 | A 20-minute and another 5-minute MBS alarm. The line has run 10 minutes with pressure below 1 psig downstream of Marshall. Procedures required shutdown when column separation was not restored within 10 minutes. Staff instead apply a *draft* procedure that starts the 10-minute clock only after an estimated fill time. | procedures (override) |
| ~05:00–05:03 | About 396,000 gal/h pumped in versus 71,062 gal received since startup; shutdown | balance evidence ignored |
| 06:35 | The on-call supervisor frames "two choices: identify the alarms as a leak or identify the alarms as column separation". The analyst calls the alarm "false" because "the MBS software was unreliable when column separation was present". | interpretation; organisation |
| 07:20–07:52 | Second restart; many 5- and 20-minute MBS alarms; the operator says "Something about this feels wrong." | — |
| 10:16 | The regional manager declines to send line walkers: "if it's a rupture someone's going to notice". | organisation |
| 11:17 | An outside caller reports oil in the creek; remote valves close at 11:18 | — |

**Alarm design facts.** One MBS alarm indication, shown as a 5-minute, 20-minute or 2-hour alarm ("the shorter the time, the larger the leak indication"), plus a second alarm after 10 minutes' persistence. SCADA "used only one sound for all alarms, regardless of pipeline condition or urgency". The MBS was "a real-time pressure transient pipeline model" (a model-compensated, RTTM-style balance); one mainline meter at Marshall split Line 6B into two balance sections. Some controllers "were not trained to use the MBS software". Analysts handled 1.6–4.2 MBS alarm calls per shift in 2010, and "valid"/"false" were control-centre terms absent from the analysts' flowchart. Training simulators had no MBS alarms, so operators "recognize leaks by line pressure variations".

**Organisational precedent.** The 10-minute rule was adopted after Enbridge's March 1991 Line 3 rupture at Grand Rapids, Minnesota, a release of 1.7 million gallons. There too, controllers interpreted the alarms as column separation and instrument error and pumped for more than an hour. The rule was therefore a documented lesson that was not applied at Marshall.

**Probable cause and recommendations relevant to CPM.**
- *Probable cause.* "Inadequate training of control center personnel, which allowed the rupture to remain undetected for 17 hours and through two startups". Contributing factors were PHMSA's "ineffective oversight of … control center procedures".
- *P-12-7 (to PHMSA).* "Develop requirements for team training of control center staff involved in pipeline operations similar to those used in other transportation modes."
- *P-12-8 (to PHMSA).* Extend operator-qualification requirements "to all hazardous liquid and gas transmission control center staff involved in pipeline operational decisions".
- The regulation now contains such a team-training element: 195.446(h)(6) requires "Control room team training and exercises that include both controllers and other individuals … (control room personnel)", with compliance due by 23 January 2018 (Amdt. 195-101, 82 FR 7999). Basis: normative. That this element *responds to* P-12-7 is an inference from content and timing; the amendment text examined here does not say so.

**Contributing factors by class** (Basis: derived): software (mis-configured for the restart); alarm presentation (one type, one sound, self-clearing at shutdown); procedures (draft procedure overriding the 10-minute rule; undocumented handover); training (no team training; no MBS alarms in simulators); oversight (analyst outside the chain of command; supervisors chose restart).

### 2. What API RP 1130 and RP 1175 contribute, and what 49 CFR 195 binds

Basis: normative (49 CFR text as rendered by the Cornell LII mirror of the eCFR; NTSB quotations of RP 1130) + documentation (API product sheet and press notices).

| Obligation | Source text (observed 2026-11-21) | Marshall relevance |
|---|---|---|
| Leak detection required on all single-phase hazardous liquid lines; operator must evaluate capability considering "length and size of the pipeline, type of product carried, the swiftness of leak detection, location of nearest response personnel, and leak history" | 195.444(a)–(b) | in 2010 NTSB cited the HCA integrity-management clause 195.452(i)(3) as the governing leak-detection requirement |
| CPM must comply with API RP 1130 in operating, maintaining, testing, record keeping, dispatcher training | 195.444(c) | training finding |
| New or replaced CPM components designed per RP 1130 section 4.2 | 195.134(c); deadlines 1 Oct 2024 (pre-2019 lines) and 1 Oct 2020 (new lines) in 195.134(b) | — |
| RP 1130 edition incorporated | 195.3: "3rd edition, September 2007" (IBR for 195.134(c), 195.444(c)) | — |
| Alarm management plan: monthly review of points with inhibited or false alarms; annual set-point verification; monitor controller workload | 195.446(e)(1)–(6) | single-sound, high-volume alarms |
| Shift-handover procedures per RP 1168 section 5 | 195.446(c)(5) | undocumented handover |
| Simulator or tabletop training for abnormal conditions; team training | 195.446(h)(2), (h)(6) | simulator lacked MBS alarms; no team training |
| Rupture indicator: pressure loss >10 % within 15 min unless documented otherwise | 195.417(a)(1) | NTSB records Marshall pump station pressures at zero during the shutdown and never above 4 psig downstream during either restart |

**RP 1130 as quoted by NTSB.** Basis: normative, quoted at second hand; the RP text itself was not examined.
- It describes three CPM alarm categories, intended to "justify the CPM system credibility and sensitivity".
- Where a system "provide[s] just one type of alarm", it says the cause should be determined "by the person who evaluates the alarm … or by a separate piece of software (i.e. an expert system)"; "Automatic alarm cause evaluation would be a desirable CPM system feature."
- It warns that "an excessive number of alarms will detract from the system credibility and may create complacency".
- It calls a CPM alarm probably "the most complex alarm that a control center operator will experience".

**RP 1175.** The first edition (December 2015, 94 pages) "focuses on management of LDPs, not the design of leak detection systems". Its contents list performance targets, metrics and KPIs (§7), testing (§8), recognition and response including "Pipeline Restart" (§9.7), alarm threshold setting and tuning (§10), training (§11) and example metrics and targets (Annex D). API announced second editions of both RP 1130 and RP 1175 on 28 April 2022. API calls the new RP 1130 the "2nd edition", while 195.3 incorporates a "3rd edition, September 2007". This numbering disagreement is preserved, not resolved. RP 1175 does not appear in 195.3's incorporation list as observed (the entries found were RP 1130, 1165 and 1168).

**Performance-metric vocabulary.** CPM performance is commonly described with four terms attributed to RP 1130: *sensitivity* (smallest leak, and time to detect it), *reliability* (correct decisions about the presence or absence of a leak, that is, few false alarms), *accuracy* (estimates of leak rate and location) and *robustness* (continued function under degraded data or transients). Basis: documentation (secondary descriptions); the RP's exact definitions were not examined.

### 3. What the regulator says its 2012 leak-detection study found

Basis: normative (Federal Register text summarising the study; the study itself was not retrieved).

- The study is identified as Kiefner & Associates, *Leak Detection Study*, Final Report No. 12–173, contract DTPH56-11-D-000001, 10 December 2012 (84 FR 52284, footnote 45). It was submitted to Congress on 31 December 2012.
- Its five tasks (85 FR 7167) were: assess past incidents for whether additional leak detection would have reduced consequences; review installed and available technologies and their retrofit applicability; study operational practices; perform a cost-benefit analysis; and identify gaps in standards.
- The study "did not provide any specific conclusions or recommendations related to leak detection system standards" (85 FR 7167–7168).
- Findings as summarised by the regulator (85 FR 7168):
  - pressure/flow monitoring "will consistently and reliably catch large volume, uncontrolled release events such as ruptures";
  - "operator procedures may have allowed ignoring alarms, restarting pumps, or opening valves during large releases";
  - "it is typically more challenging to detect smaller leaks in an operationally, technically, and economically feasible manner";
  - "LDS with the same technology, when applied to two different operating pipeline systems, can have very different results. In short, one size does not fit all."
- As quoted in 84 FR 52270, the study found most technologies retrofittable. It also found that operators "fear investing in leak detection systems, with potentially little benefit to show from them and no way to truly measure success in a standardized way".
- The regulator's consequence in 2019: "Given the difficulties identified in the Kiefner study related to leak detection performance standards, PHMSA is not making any additional changes to the regulations concerning specific leak detection system performance criteria requirements at this time" (84 FR 52270).
- The 2020 proposal motivated a 10-minute rupture-confirmation standard with Enbridge's own 10-minute rule as recorded by NTSB (85 FR 7168).

### 4. Detection principles and their physical limits

| Method | Physical model and inputs | Detects by | Localises by | Characteristic failure |
|---|---|---|---|---|
| Uncompensated volume balance | Q_in − Q_out over a window; meters at the ends | sustained positive imbalance | no | linepack change during transients looks like a leak (probe S6); meter bias floors sensitivity |
| Compensated / real-time transient model (RTTM; Enbridge MBS) | MOC or equivalent model driven by measured pressures, flows, temperature and density | model-versus-measured imbalance | sometimes (pressure-gradient intersection) | model invalid outside its assumptions: column separation, wrong valve states, overridden transmitters (Marshall) |
| Negative-pressure-wave / pressure-point analysis | pressure at two or more points; wave speed *a* | step drop in pressure | x = (L + a·(t_up − t_dn))/2 | operational transients produce the same signature at one end; slow leaks give no sharp front |
| Transient damping (Wang et al. 2002) | linearised water-hammer equations solved as a Fourier series; injected transient | leak adds component-dependent damping on top of friction damping (uniform across components) | ratio of damping rates between harmonics | the authors say it is not generally applicable to complex networks; it needs a deliberate transient |
| Inverse transient analysis (Liggett–Chen 1994) | transient model fitted to measured transients | fitted leak parameters | from the fit | per Wang et al., needs the transient event and boundary conditions modelled |

Wang et al. report detecting, locating and quantifying "a 0.1 % size leak with respect to the cross-sectional area" in a 37.2 m copper laboratory pipe of 22 mm inner diameter at wave speed 1320 m/s, between pressurised tanks. Basis: documentation (accepted manuscript). That is laboratory evidence; it is not field-pipeline evidence.

**Wave-front amplitude (derived).** For an abrupt leak of flow Q_L at an interior point of a uniform line, each outgoing front carries a velocity change of about Q_L/(2A). The Joukowsky relation then gives a head drop of about (a/g)·Q_L/(2A). With the probe's parameters (Q_L = 0.0208 m³/s, A = π·0.762²/4 = 0.456 m², a = 1000 m/s): (1000/9.81)·0.0208/0.912 ≈ 2.3 m. The probe measured station drops of 1.6 m (pump end) and 2.4 m (orifice end). These differ because the boundaries reflect the front differently.

### 5. TSNet at the pin: how it implements the hydraulics, and what transfers

Basis: source, at `glorialulu/TSNet@27e616a8e2048a431eed27b00a08322d49035a52`.

- **Interior MOC.** `inner_node_steady` (`tsnet/simulation/solver.py:369–416`) forms the C⁺ and C⁻ constants `C[0,0] = V1 + ga*H1 - J1 + ga*dt*V1*theta` and `C[1,0] = -V2 + ga*H2 + J2 + ga*dt*V2*theta`, with steady friction `J = f*dt/2/D*V*|V|`, and solves `HP[i] = (C[0,0] + C[1,0]) / (C[0,1] + C[1,1])`, where both denominators equal g/a. This is the textbook fixed-grid MOC with dt = dx/a. The docs describe a wave-speed adjustment scheme that forces a common time step (`docs/transient.rst`, "Choice of Time Step").
- **Leak node.** `add_leakage` (`solver.py:924–1019`) combines the C⁺/C⁻ relations with continuity and the orifice law Q_l = k·√(H_P − z). Squaring gives `a1 = b**2`, `b1 = -2*a*b - emitter_coef**2.`, `c1 = a**2 + emitter_coef**2.*elev` (`solver.py:1001–1003`). The solver takes the root `HP = (-b1 - np.sqrt(delta))/(2*a1)` (`solver.py:1008`), which is the root consistent with a − b·H_P ≥ 0. The function has **no branch on the sign of H_P − z**. The documented behaviour ("if the pressure head is negative, the leak discharge will be set to zero, assuming a backflow preventer", `docs/transient.rst`, Leaks) is implemented when the *recorded* discharge is computed (`tsnet/simulation/main.py:209–216`: `if HN[pn][0] - pipe.start_node.elevation >0:` … `emitter_discharge[ts] = 0.`), not inside the solve. Under sub-atmospheric pressure at a leak node, the reported discharge and the hydraulics solved therefore follow different rules. This is an observation of where the rule lives; no wrong numerical result was demonstrated.
- **Leaks only at nodes** (`docs/limitations.rst:50`: "Pipe bursts and leaks occur only on the nodes"). A leak position therefore needs a junction there; the probe splits the line into two pipes.
- **Water-specific constants.** `solver.py:33`: `nu = 1.004e-6  # kinematic viscosity [m^2/s]` is used by `Reynold()`, and hence by the quasi-steady and unsteady friction models. The same constant appears in `tsnet/simulation/initialize.py:83`. `docs/limitations.rst:12–13` state that pressure is in metres "(this assumes a fluid density of 1000 kg/m^3)". In steady-friction mode (the probe's mode), *f* is user-set and `nu` is unused. For crude oils, whose viscosity differs from water's, the non-steady friction modes would be mis-parameterised without a code change. Basis: source + derived.
- **No column separation.** None of the 19 Python files under `tsnet/` contains "cavit", "vapor", "vapour" or "column sep". The NTSB notes that column separation "is a known limitation to pressure transient leak detection systems because the systems are built to estimate the flows and pressures of a homogenous liquid line". TSNet shares that limitation and cannot reproduce the Marshall confounder.
- **Open note in unsteady friction.** `solver.py:91` reads `" TO DO: check the sign of unsteady friction"`, inside `unsteady_friction()` (Brunone/Vardy form). The unsteady mode was not executed here.
- **Modified CUSUM.** `tsnet/postprocessing/detect_cusum.py:98` (`# add gp_real and gn_rel to track the actual amplitude of the transient`) introduces undrifted sums. Line 110 alarms on them: `if gp_real[i] > threshold or gn_real[i] > threshold:  # change detected!`. The drifted sums `gp`/`gn` only decide resets. The classical Page/Gustafsson test survives as a commented-out block (lines 82–95), yet line 115 still says `# THE CLASSICAL CUSUM ALGORITHM ENDS HERE`. The function returns `tai, taf, amp` (line 145): change-start indices, not alarm indices, so an online user cannot read detection latency from the return value. Its docstring (line 24) says `ending … (default = False)`, while the signature (line 11) defaults `ending=True`.
- **Version labels disagree.** `setup.py:53` has `version='0.3.1'` and `tsnet/__init__.py:12` has `__version__ = '0.2.2'`.

### 6. Probe: leaks and operational transients on a toy line using TSNet's kernels

Basis: execution (toy model driven by TSNet kernels; **not** any real pipeline or CPM product). The script and its full JSON output are in `support/`.

**Configuration (all invented):**
- Line: 40 km, D = 0.762 m, a = 1000 m/s, Darcy f = 0.015, flat, dx = 500 m (dt = 0.5 s).
- Upstream: sump at 10 m with a pump h = 200 − 147.4·Q² (`source_pump`). Downstream: a delivery orifice Q = 0.0594·√(H − 100) (`dead_end`). Steady flow Q₀ = 0.4199 m³/s; station heads 184.0 m and 150.0 m.
- Leak: `add_leakage` at x = 20 km or 10 km, opened at t = 300 s by `burstsetting`.
- SCADA: 2 s scan; pressure noise σ = 0.2 m; flow noise 0.25 % of Q₀ plus a per-meter bias with sd 0.1 % of Q₀; 20 noise seeds per scenario.
- Detectors:
  - (P) TSNet `detect_cusum` on each station pressure (threshold 1.0 m, drift 0.05 m). It "fires" when both ends raise a post-event alarm on a falling signal; alarm times are recovered by bisection on prefixes, because the function's forward pass is causal.
  - (B) windowed volume balance Q_in − Q_out with threshold 4·√(2σ_Q²/n + 2σ_bias²).
  - (L) location from the first change-start index at each end.

| Scenario (true leak at end) | Station Δp in 15 min, up / down | P fires (median delay) | B 60 s fires (median delay) | Location estimate, median [IQR] |
|---|---|---|---|---|
| S0 no event | 0 / 0 | 8/20 runs (false, median 670 s) | 0/20 | meaningless |
| S1 leak 5 % at 20 km (0.0208 m³/s) | −0.87 % / −1.57 % | 20/20 (22 s) | 20/20 (28 s) | 20.0 km [18–21] |
| S2 leak 1 % at 20 km | −0.18 % / −0.32 % | 9/20 (not distinguishable from S0) | 20/20 (56 s) | meaningless |
| S3 leak 0.5 % at 20 km, 60 s ramp | −0.09 % / −0.14 % | 9/20 | 13/20 (246 s) | meaningless |
| S4 rupture, 24 % of flow at 10 km | −4.9 % / −6.5 % | 20/20 (32 s) | 20/20 (14 s) | 10.5 km [9.75–13.25] |
| S7 rupture, 55 % of flow at 10 km | −11.6 % / −14.4 % | 20/20 (32 s) | 20/20 (12 s) | 10.5 km [9.75–13.25] |
| S5 pump head −10 % in 10 s (no leak) | −8.3 % / −6.3 % | 20/20 (**false**, 42 s) | 0/20 (imbalance negative: min −0.0576, max +0.0014 m³/s in 0–300 s) | 1.0 km [0–2]: at the pump |
| S6 delivery valve 20 % closed in 10 s (no leak) | +5.5 m / +14.2 m (rises) | 13/20 (noise-driven) | 20/20 (**false**, 8 s) | 38 km [37.75–40]: at the valve |

**What the probe shows (toy-scoped):**
1. *Each single-signal rule has an operational twin.* A pump-head drop lowers pressure at both ends, so a two-ended pressure rule fires. A downstream valve closure packs the line: Q_in − Q_out peaks at 0.048 m³/s (11.5 % of Q₀) within 300 s, so an uncompensated balance fires faster than for a real 5 % leak. The NTSB's statement that startups and shutdowns "could impact the MBS software's leak detection capabilities" is the operational form of this.
2. *Localisation discriminates.* The arrival-time difference placed the two operational transients at the stations that caused them (1 km and 38 km), and the leaks at 10.5 km and 20 km. A rule that requires an interior location separates S5 and S6 from S1, S4 and S7 in this toy.
3. *Balance sensitivity is floored by meter bias, not window length.* With per-meter bias sd 0.1 %, the steady-state sd of the imbalance is at least √2·0.1 % ≈ 0.14 % of Q₀. A 4-sd threshold is therefore about 0.57 % of Q₀ (derived). The 0.5 % leak (S3) was detected only in runs where the random biases happened to help (13/20 at 60 s, 8/20 at 300 s, 6/20 at 1200 s). Longer windows did not help, because they average out white noise but not bias.
4. *195.417 default versus this toy.* A rupture taking 24 % of the flow produced station pressure losses of 4.9 % and 6.5 % within 15 minutes, below the 10 % default. At 55 % of the flow the losses were 11.6 % and 14.4 %. A stiff pump curve and a mid-line break dampen the station pressure signal; the rule's documented-alternative clause exists for line-specific dynamics.
5. *CUSUM variant.* On pure noise (S0, 20 seeds × 2 sensors × 1800 s = 20 sensor-hours), alarms per sensor-hour at drift 0.05 m were:

| threshold (m) | TSNet `detect_cusum` | classical CUSUM (lines 82–95 reimplemented) |
|---|---|---|
| 0.6 | 163.15 | 64.0 |
| 0.8 | 35.2 | 8.0 |
| 1.0 | 4.8 | 0.4 |
| 1.5 | 0.0 | 0.0 |

At equal settings the TSNet variant alarms 2.5–12 times more often on noise. This follows from line 110: the undrifted sum is always at least the drifted one. Tuning guidance written for the classical form (the docstring cites Gustafsson) therefore does not carry over to this variant unchanged.

### 7. Performance and resource footprint (L1–L6)

| Level | Quantity | Value | Basis |
|---|---|---|---|
| L1 authoring | harness size; authoring effort | 254 lines (`wc -l`); effort not measured | measured / — |
| L2 toolchain build | TSNet install/build time | not measured (WNTR, scipy, pandas absent on host) | — |
| L3 simulation latency | 8 scenarios × 3600 MOC steps × 80 reaches (82 grid points), Python | 16.53 s wall for all simulations; 35.24 s for the whole probe including 8 × 20 noisy trials (CUSUM with prefix bisection and balance) | measured (`/usr/bin/time -v`, host above) |
| L4 runtime of a deployed CPM | scan-to-alarm latency, throughput | not measured; NTSB records the operator's alarm windows (5 min, 20 min, 2 h) and a 10-minute persistence alarm | normative |
| L5 verification | independent check of CPM correctness | not measured | — |
| L6 memory | peak RSS of probe | 37,756 KiB | measured (`/usr/bin/time -v`) |

### 8. Comprehensibility and model simplicity (C1–C2)

- **C1: the operator's mental model was the failure locus.** Staff held one hypothesis (column separation) that explained every alarm, including volume shortfalls of hundreds of thousands of gallons. Three features of the system supported that frame: a single undifferentiated alarm type and sound, alarm self-clearing on shutdown, and an analyst flowchart that said "software unreliable" whenever vapour was indicated. Diagnostics said *that* something was abnormal, not *which* hypothesis the data contradicted. In the probe, two-ended wave timing and the imbalance sign do contradict operational explanations; exposing such checks would make alarms human-auditable, but no examined subject implements that. Basis: derived.
- **C2: one invariant, several mechanisms.** The invariant is conservation of mass in a closed segment: inflow − outflow − d(linepack)/dt = leak flow. Balance, RTTM, pressure-wave and damping methods are all estimators of the terms of that one equation under different observability, not different invariants. The confusion at Marshall came from a realisation-medium quirk, column separation, that breaks the single-phase assumption every listed estimator shares (and that 195.444(a) builds into its scope: "single phase (without gas in the liquid)"). A minimal universal abstraction would carry an explicit *model-validity state* alongside every CPM output. When that state is false, the operating procedure must default to the conservative action (the 10-minute rule) rather than to "alarm is false". This is a design inference, not a tested mechanism.

### 9. Validation of implementations and proposals (V1–V4)

- **V1 specification adequacy.** RP 1130 and RP 1175 specify process and testing, and the regulation binds RP 1130 compliance but no detection threshold. The regulator itself states the absence of a standard way to "truly measure success". Non-vacuity of a CPM specification would require stating which leak sizes, at which locations and under which operating states must alarm within what time. No examined subject states such numbers except 195.417's rupture indicator.
- **V2 differential testing.** TSNet's CUSUM was tested differentially against the classical CUSUM on identical inputs (the false-alarm gap above). No MOC-versus-MOC differential test was run; TSNet's own comparison with commercial software (`docs/validation.rst`) was not examined.
- **V3 concurrency and crash.** Not applicable.
- **V4 plant falsification, incident replay, operator litmus.** The NTSB timeline (alarm 18:03; restarts ~04:04 and 07:20; recognition 11:17) is a falsification case for any proposed CPM-plus-procedure design. Simulators without MBS alarms could not test controllers' alarm models; 195.446(h)(2) and (h)(6) now require simulator/tabletop training and team exercises. Replaying Marshall SCADA data through TSNet is impossible without a column-separation model and was not attempted.

## Boundaries

- **Not examined: the 2012 leak-detection study's own text and statistics.** The PHMSA-hosted PDF (`.../16691/leak-detection-study.pdf`), the older URL given in 84 FR footnote 45 and an archived copy could not be retrieved through the tools available on 2026-11-21. All study content above is the regulator's summary in 84 FR and 85 FR. Secondary web summaries attribute specific first-identification percentages for CPM and SCADA to the study; they are **unverified** and deliberately not reported.
- **Not examined: API RP 1130 and RP 1175 text.** RP 1130 is cited only as NTSB quotes it (3rd edition) and as the CFR incorporates it. The four-metric vocabulary rests on secondary descriptions. RP 1175 rests on its product sheet and table of contents only.
- **Not examined: the NTSB report beyond its first ~77 PDF pages.** These include the Executive Summary, probable cause, the accident sequence and section 1.11 on the MBS, procedures and training. The analysis section 2, the numbered findings 3.1 and the full recommendation list in section 4 were not retrieved, except through the recommendation letter for P-12-3 through -10. Recommendation numbers to Enbridge, API and other recipients are not reported.
- **Not examined: methods papers beyond metadata.** Billmann–Isermann 1987, Liggett–Chen 1994, Colombo–Lee–Karney 2009 and Murvay–Silea 2012 were verified only as bibliographic records (Crossref). Liggett–Chen's method is characterised only through Wang et al.'s description. Adegboye–Fung–Karnik 2019 was examined at abstract level only.
- **Known not to apply: TSNet to two-phase or slack-line flow.** There is no vapour-cavity model (Finding 5). Probe results say nothing about column separation, batch interfaces, temperature or density effects, elevation profiles, or multiple pump stations.
- **Unknown: whether `add_leakage` produces wrong hydraulics under negative pressure.** The structural observation stands (no sign branch in the solve; clamp only in recording). A failing case was not constructed.
- **Toy-model scope.** Detection fractions, delays, location errors and the "24 % rupture stays below 10 %" result are properties of the invented line, noise model and thresholds. They are not CPM performance figures for any pipeline, are not a validation of RP 1130 metrics, and are not evidence about Enbridge's MBS.
- **Not established:** that any particular algorithm would have averted Marshall; that RTTM beats balance methods in general; that the 195.417 default is mis-set (it permits documented alternatives); that 195.446(h)(6) was adopted because of P-12-7.

## Evidence

All web material was observed on **2026-11-21 (UTC)**.

- **NTSB.** *Enbridge Incorporated Hazardous Liquid Pipeline Rupture and Release, Marshall, Michigan, July 25, 2010*, NTSB/PAR-12/01, PB2012-916501, Notation 8423, adopted 10 July 2012. https://www.ntsb.gov/investigations/AccidentReports/Reports/PAR1201.pdf. Sections used: Executive Summary (pp. xii–xiv); 1.2.2–1.2.5 (sequence); 1.11.4 (training); 1.11.5 (MBS leak detection, RP 1130 quotations, column separation); 1.11.6 (10-minute restriction, procedures, leak triggers). Text extraction covered roughly the first 77 PDF pages.
- **NTSB safety recommendation letter** to PHMSA, P-12-3 through -10 and P-11-8 (reiterated), 25 July 2012. https://www.ntsb.gov/safety/safety-recs/recletters/P-12-003-010.pdf
- **49 CFR Part 195** as rendered by Cornell LII (eCFR mirror): §§195.3 (items 7, 9, 10), 195.134, 195.417, 195.418, 195.444, 195.446. https://www.law.cornell.edu/cfr/text/49/195.444 (and sibling URLs). The eCFR.gov HTML pages presented an automated-access challenge and were not used.
- **84 FR 52260** (1 October 2019), *Pipeline Safety: Safety of Hazardous Liquid Pipelines*, Docket PHMSA-2010-0229, RIN 2137-AE66, FR Doc. 2019-20458. https://www.govinfo.gov/content/pkg/FR-2019-10-01/pdf/2019-20458.pdf. Used: pp. 52270 and 52284.
- **85 FR 7162** (6 February 2020), *Pipeline Safety: Valve Installation and Minimum Rupture Detection Standards* (NPRM), Docket PHMSA-2013-0255, RIN 2137-AF06, FR Doc. 2020-01459. https://www.govinfo.gov/content/pkg/FR-2020-02-06/html/2020-01459.htm. Used: pp. 7167–7168.
- **API.**
  - RP 1175, first edition (December 2015) product sheet: https://www.api.org/~/media/files/publications/whats%20new/1175_e1%20pa.pdf
  - 2022 notices: https://www.api.org/products-and-services/standards/important-standards-announcements/rp1130 and .../rp1175
- **PHMSA report to Congress** cover letters (December 2012; the study is "almost 300 pages"): https://www.phmsa.dot.gov/sites/phmsa.dot.gov/files/docs/Report%20to%20Congress%20on%20Leak%20Detection%20-%20December%202012.pdf
- **TSNet.** `glorialulu/TSNet` at `27e616a8e2048a431eed27b00a08322d49035a52` (HEAD on the observation date; commit dated 2023-09-21). Files read: `tsnet/simulation/{solver,main,single,initialize}.py`, `tsnet/network/{control,topology}.py`, `tsnet/postprocessing/detect_cusum.py`, `docs/{limitations,transient}.rst`, `setup.py`, `tsnet/__init__.py`. Full SHA-256 sums of the files read at the pin are in `support/tsnet_files_at_pin.sha256`.
- **Literature** (DOIs verified against Crossref metadata on 2026-11-21):
  - L. Billmann, R. Isermann, "Leak detection methods for pipelines", *Automatica* 23(3):381–385, 1987, doi:10.1016/0005-1098(87)90011-2 (metadata only).
  - J. A. Liggett, L.-C. Chen, "Inverse Transient Analysis in Pipe Networks", *J. Hydraul. Eng.* 120(8):934–955, 1994, doi:10.1061/(ASCE)0733-9429(1994)120:8(934) (metadata only).
  - X.-J. Wang, M. F. Lambert, A. R. Simpson, J. A. Liggett, J. P. Vítkovský, "Leak Detection in Pipelines using the Damping of Fluid Transients", *J. Hydraul. Eng.* 128(7):697–711, 2002, doi:10.1061/(ASCE)0733-9429(2002)128:7(697). Accepted manuscript read at http://hdl.handle.net/2440/994.
  - A. F. Colombo, P. Lee, B. W. Karney, *J. Hydro-environment Res.* 2(4):212–227, 2009, doi:10.1016/j.jher.2009.02.003 (metadata only).
  - P.-S. Murvay, I. Silea, *J. Loss Prev. Process Ind.* 25(6):966–973, 2012, doi:10.1016/j.jlp.2012.05.010 (metadata only).
  - M. A. Adegboye, W.-K. Fung, A. Karnik, *Sensors* 19(11):2548, 2019, doi:10.3390/s19112548 (abstract).
  - L. Xing, L. Sela, "Transient simulations in water distribution networks: TSNet python package", *Adv. Eng. Softw.* 149:102884, 2020, doi:10.1016/j.advengsoft.2020.102884 (abstract).
- **Execution.**
  - `support/tsnet_leak_probe.py` and `support/tsnet_probe_out.json`.
  - Command: `python3 tsnet_leak_probe.py --tsnet-root <TSNet checkout at the pin>`. Default 20 seeds; numpy only, with a stub injected for `matplotlib.dates`.
  - Recorded: wall time 35.24 s and maximum RSS 37,756 KiB (`/usr/bin/time -v`).

## Revalidation

1. **Regulatory text.** Re-read 195.3 (RP 1130 edition), 195.134(b)–(c), 195.417(a)(1), 195.444 and 195.446(e) and (h) on the eCFR or a mirror. If 195.3 adopts the 2022 RP 1130 or adds RP 1175, revise Finding 2.
2. **TSNet behaviour.** At any newer TSNet revision:
   - `grep -n "gp_real\[i\] > threshold" tsnet/postprocessing/detect_cusum.py` (the modified CUSUM);
   - `grep -n "nu = 1.004e-6" tsnet/simulation/*.py` (water viscosity);
   - `grep -rniE "cavit|vapou?r|column sep" tsnet/` (absence of a cavity model; an empty result supports Finding 5);
   - inspect `add_leakage` for a pressure-sign branch;
   - rerun `support/tsnet_leak_probe.py --seeds 5` (about 10 s on the host above). The S0 false-alarm table and the S5/S6 false-indication pattern are the discriminating outputs.
3. **NTSB facts.** Re-check quotations against PAR-12/01 sections 1.2 and 1.11 (stable PDF). Retrieve sections 3–4 to complete the recommendation list.
4. **Study statistics.** Retrieve the 2012 study PDF from PHMSA's technical-resources page and extract its incident-discovery tables before citing any percentage.

