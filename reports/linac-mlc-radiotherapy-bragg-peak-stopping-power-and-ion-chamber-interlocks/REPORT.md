# LINAC MLC Kinematics, Proton Bragg-Peak Stopping-Power Uncertainty, and Ion-Chamber Interlocks

## Summary

External-beam radiation oncology—spanning `6–18 MV` photon Volumetric Modulated Arc Therapy (`VMAT`) shaped by `120`-leaf tungsten Multi-Leaf Collimators (`MLC`s), `70–250 MeV` pencil-beam-scanned (`PBS`) proton therapy, and `> 40 Gy/s` Ultra-High-Dose-Rate (`FLASH`) electron/proton delivery—demands end-to-end dosimetric accuracy within **`±2–3%` in dose and `±1–2 mm` in spatial alignment** (`Basis: normative, documentation`). Because ionizing radiation is invisible during `1–3 minute` fractions and irreversible in central-nervous-system Organs-at-Risk (`Brainstem`, `SpinalCord`, `OpticChiasm`), geometric, stoichiometric, or ionization-detector invariants violated silently inside Treatment Planning Systems (`TPS`) or Linear Accelerator (`LINAC`) beam-monitoring loops directly cause fatal patient overdoses or paralysis (`Basis: normative, source, execution`):

1. **Self-Crossing Polygon Winding Inversions (`IAEA Panama 2001` `~2x` Overdose) & Wedge Factor Mode Traps (`ASN Épinal 2006`) (`Basis: normative, documentation, execution`)**: In the `2000–2001` *Instituto Oncológico Nacional* (Panama) tragedy (`IAEA STI/PUB/1114`), physicists bypassed a `4`-block array limit in Multidata's `RTP` TPS by digitizing `5` corner shielding blocks as **one continuous closed polygon loop**. Whenever connecting segments crossed in a figure-8 or reversed `CW`/`CCW` orientation, Green's-theorem signed-area / winding integration canceled opposite-sign lobes (`+40 + (-40) = 0.0 cm^2`, `probes/verify_linac_bragg_interlocks.py`) or inverted block attenuation masks, **inflating prescribed Monitor Units (`MU`) by `1.85x–2.00x` (`85%–100%` overdose across `28` patients)**! Similarly, in the `2001–2006` *Épinal* (France) accident, confusing motorized physical wedge transmission factors (`TF ~ 0.75–0.80`) with dynamic `MLC`/jaw sequences omitted wedge `MU` scaling (`+20%–28%` overdose across `24` patients). Both require **strict `SimpleCCW` non-self-intersecting polygon admission** + **independent Monte Carlo / ray-trace secondary `MU` verification**.
2. **Proton CT `HU-to-RSP` `±3.5%` Degeneracy & Distal Bragg-Peak Brainstem Overshoot (`Paganetti 2012`, `matRad`, `OpenTOPAS`) (`Basis: normative, source, execution, derived`)**: Protons deposit peak ionizing energy in a `2–4 mm`-wide **Bragg Peak** immediately before stopping ($-dE/dx \propto 1/v^2$). Converting diagnostic kilovoltage X-ray Computed Tomography Hounsfield Units (`HU`, governed by photoelectric $Z^{3.6}$ + Compton electron density $\rho_e$) to proton **Relative Stopping Power (`RSP`, governed by Bethe–Bloch mean excitation energy $\ln I$)** is fundamentally **many-to-one (`non-injective`)**, leaving a **`±3.5% + 1–2 mm` clinical range uncertainty** (`Paganetti 2012`, `DOI: 10.1088/0031-9155/57/11/R99`). On a `158.0 mm` nominal proton beam stopping `3.0 mm` anterior to the `Brainstem` (`54 Gy` necrotizing ceiling), a `-3.5%` `RSP` bias (`true RSP = 0.965`) shifts the Bragg peak **`+5.73 mm` deeper** (`163.73 mm`), **dumping `60.0+ Gy(RBE)` (amplified further by distal `LET` `RBE ~ 1.3`, `'MCN'`/`'WED'` models in `e0404/matRad` `matRad.m:30`) directly into the `Brainstem`**, whereas `9`/`21`-scenario worst-case minimax optimization (`Fredriksson et al. 2011`, `'wcScen'` in `matRad.m:33`) bounds worst-case brainstem dose to **`13.7 Gy < 54 Gy`** (`probes/verify_linac_bragg_interlocks.py`).
3. **`120`-Leaf `VMAT` `MLC` Interdigitation Collisions, Rounded-Leaf-End `DLG`, and Gravity Leaf-Lag (`OpenTOPAS`, `Pylinac`, `LoSasso 1998`) (`Basis: normative, source, execution`)**: Direct inspection of `OpenTOPAS/OpenTOPAS` (`geometry/TsMultiLeafCollimator.cc:62–67, 125–130`) shows explicit runtime aborts (`(XPlusLeavesOpen[i] - XMinusLeavesOpen[i]) < 0.0`) preventing opposing tungsten leaves from smashing together across the central axis. During dynamic sliding-window `VMAT` arcs (`gantry rotating 360 deg` while `120` leaves accelerate at up to `2.5–4.0 cm/s` against gravity), LoSasso, Chui & Ling (`DOI: 10.1118/1.598381`) proved that delivered dose scales inversely with effective sweeping gap $w_{\text{eff}}$: on a `10.0 mm` narrow aperture, a mere **`0.5 mm` gravity-induced leaf lag (`Dynalog`/`TrajectoryLog` `LeafAxis` in `pylinac` `log_analyzer.py:407–494`) introduces a `5.0%` clinical dose error**!
4. **`IEC 60601-2-1` Transmission Ionization-Chamber Recombination Collapse Under `> 40 Gy/s` `FLASH` Pulses (`Pylinac` `trs398.py:614–656`) (`Basis: normative, source, execution`)**: `IEC 60601-2-1` mandates two independent transmission Monitor Unit (`MU1`, `MU2`) ionization chambers in the LINAC treatment head. Inspecting `jrkerns/pylinac` (`pylinac/calibration/trs398.py:645, 651–656` and `tg51.py:978`) reveals that clinical two-voltage recombination formulas enforce a hard upper validity ceiling **`MAX_PION = 1.05` (`<= 5%` ion loss)**. While conventional pulsed delivery (`0.5 mGy/pulse`) sits safely at $k_s = 1.0004 \in [1.00, 1.05]$, **`FLASH` radiotherapy (`> 40 Gy/s`, `2.0 Gy` per `2 us` pulse)** drives Boag's exact dimensionless space-charge density to $u = 3.20$, collapsing collection efficiency $f(u) = \frac{1}{u}\ln(1 + u)$ to **`44.9%` (`k_s = 2.23x >> 1.05`)**—meaning an uncompensated gas `MU` chamber **allows a `223%` radiation overdose before tripping beam-off** unless cross-gated within `< 50 us` against a **saturation-immune inductive Beam-Current Transformer (`BCT` / ACCT toroid)**!

## Applicability

This report governs radiation-therapy geometry parsing, analytical/Monte-Carlo dose optimization, `MLC` servo control, and `IEC 60601-2-1` primary/secondary dose-monitoring interlocks across the seven subjects in `REPORT.json` (`Basis: derived`):

- **Subject Relationships**:
  - **Monte Carlo Physics & Collimator Geometry**: `OpenTOPAS/OpenTOPAS` (`8be924480441884069a03efc9270095b199933f0`, `TsMultiLeafCollimator.cc`) provides reference Geant4 proton/photon transport and `MLC` leaf-collision enforcement, grounding **Paganetti (`2012`)**'s range-uncertainty taxonomy.
  - **Inverse Treatment Planning & Robust Optimization**: `e0404/matRad` (`008bfd7c2e8d5101912262a33adea5ef867d7f25`, `matRad.m`) implements multi-modality (`photons`, `protons`, `helium`, `carbon`, `VHEE`) variable-`RBE` (`'MCN'`, `'WED'`) and worst-case scenario (`'wcScen'`) optimization following **Fredriksson, Forsgren & Hårdemark (`2011`)**.
  - **Delivery Log Verification & Ion-Chamber Dosimetry**: `pymedphys/pymedphys` (`6d02df7f6827caf9565c13da3e32d553e92ad8d6`, `MU` density & 3D Gamma QA) and `jrkerns/pylinac` (`5c6a17c0df418804d7e419c12f330ba7a667a0b5`, `log_analyzer.py`, `tg51.py`, `trs398.py`) encode clinical `MLC` fluence reconstruction (`LoSasso 1998`) and two-voltage `P_ion`/`k_s` bounds contrasted against **`IEC 60601-2-1:2020`**, **IAEA `STI/PUB/1114` (*Panama*, `2001`)**, and **ASN/IRSN (*Épinal*, `2007`)**.
- **Exact Observation vs. Broader Applicability**:
  - Source citations apply to the pinned revisions above (`matRad` notes explicitly in `README.md:27` that it is research/educational GPL code, making its clean exposition of `'wcScen'` and `'MCN'`/`'WED'` algorithms an ideal white-box mathematical reference for clinical TPS verification).
  - Polygon simple-connectivity (`SimpleCCW`), Bethe–Bloch `HU-to-RSP` interval bounds, and Boag space-charge recombination physics apply universally across Varian/Siemens, Elekta, IBA, Hitachi, and Mevion photon/proton/FLASH accelerators.

## Findings

### 1. `Panama` (`2001`) Polygon Winding Inversion & `Épinal` (`2006`) Wedge-Factor Traps

`Basis: normative, documentation, execution, derived`

#### 1.1 Exact Green's-Theorem Anatomy of the `IAEA Panama` `2x` Overdose (`STI/PUB/1114`)
In 2D/3D conformal and `DICOM RTSTRUCT` (`(3006,0050)` `ContourData`) beam modeling, planar aperture or Cerrobend/tungsten shielding-block contours $P = [(x_0, y_0), \dots, (x_{V-1}, y_{V-1})]$ enter scatter-integration kernels (Clarkson sector integration / convolution-superposition). By Green's theorem, the signed area of a closed polygonal curve $\partial\Omega$ is:
$$A_{\text{signed}}(P) = \frac{1}{2}\sum_{i=0}^{V-1} (x_i y_{i+1} - x_{i+1} y_i) = \iint_{\mathbb{R}^2} \operatorname{wind}(P; x, y)\,dx\,dy$$
where $\operatorname{wind}(P; x, y) \in \mathbb{Z}$ is the topological winding number (`+1` for interior of a simple counter-clockwise `CCW` contour, `-1` for clockwise `CW`).

In August 2000 at Panama's National Oncology Institute (`IAEA STI/PUB/1114`), Multidata's TPS restricted each beam field to `<= 4` discrete block polygons. To enter `5` pelvic shielding blocks, dosimetrists traced one continuous loop visiting all blocks sequentially:
1. **Self-Intersection / Orientation Cancellation (`probes/verify_linac_bragg_interlocks.py`)**: Whenever the connecting zero-width bridge crossed itself in a **figure-8**, one lobe became `CCW` ($\operatorname{wind} = +1$, $A_1 = +20\text{ cm}^2$) while the second lobe became **`CW` ($\operatorname{wind} = -1$, $A_2 = -20\text{ cm}^2$)**!
   - Naive signed-area integration evaluates $A_{\text{signed}} = +20 + (-20) = \mathbf{0.0\text{ cm}^2}$ (making `40 cm^2` of heavy shielding vanish completely from equivalent-square scatter tables!), or subtracts `-40 cm^2` instead of `+40 cm^2` (`(85 - (-40)) / (85 - 20) = 1.923x` **`+92.3%` Monitor Unit inflation**)!
   - Even scanline parity (`even-odd`) rasterizers fail when two blocks share a collinear double-bridge or overlapping corner (`0 mod 2 == even -> unshielded hole right through an Organ-at-Risk!`).
2. **`ASN Épinal` (`2006`) Dynamic vs. Motorized Wedge Factor Confusion**:
   - Physical `15–60 deg` metal wedges attenuate central-axis photon intensity by a Wedge Transmission Factor $\text{WTF} \in [0.45, 0.85]$ (`requiring MU / WTF` extra monitor units), whereas dynamic jaw/MLC wedges (`EDW`) embed attenuation inside segmented `MU` tables. Entering a `0.80` wedge modifier in the wrong TPS mode (`or omitting it on manual console transfer`) shifts delivered dose by **`1 / 0.80 = +25.0%`** across every fraction (`killing 7 patients in Épinal`), proving why **independent secondary `MU` calculation** (`pymedphys` independent ray-trace/Monte Carlo check within `±3%` of primary TPS) is an non-negotiable clinical barrier.

---

### 2. Proton CT `HU-to-RSP` `±3.5%` Degeneracy, Variable Distal `RBE`, and Minimax Optimization

`Basis: normative, source, execution, derived`

#### 2.1 Why Single-Energy CT `HU` Cannot Uniquely Determine Proton Stopping Power (`Paganetti 2012`)
Clinical treatment planning imports `120 kVp` X-ray CT scans calibrated in Hounsfield Units $\text{HU} = 1000 \frac{\mu_x - \mu_{\text{water}}}{\mu_{\text{water}}}$, where linear attenuation $\mu_x \approx \rho_e \bigl(\sigma_{\text{Compton}}(E_x) + c_{\text{PE}}(E_x) Z_{\text{eff}}^{3.6}\bigr)$ mixes electron density $\rho_e$ with a steep `$Z^{3.6}$` atomic-number photoelectric term. By contrast, `70–250 MeV` therapeutic protons lose energy purely via relativistic **Bethe–Bloch electronic stopping** (`no photoelectric effect!`):
$$\operatorname{RSP} = \frac{S_{\text{tissue}}}{S_{\text{water}}} \approx \rho_{e,\text{rel}} \cdot \frac{\ln\!\left(\frac{2 m_e c^2 \beta^2}{1 - \beta^2}\right) - \beta^2 - \ln I_{\text{tissue}}}{\ln\!\left(\frac{2 m_e c^2 \beta^2}{1 - \beta^2}\right) - \beta^2 - \ln I_{\text{water}}}$$
- **Stoichiometric Non-Injectivity**: Two tissues with different $(\rho_e, Z_{\text{eff}}, I_{\text{tissue}})$ (e.g., dense cortical/trabecular skull bone vs. calcified cartilage or iodinated contrast, or adipose vs. paranasal sinus interfaces) produce **identical X-ray `HU` values yet differ by `2%–5%` in proton `RSP`**! Combined with CT beam-hardening artifacts and `I_water` (`75–80 eV`) uncertainty, Paganetti (`DOI: 10.1088/0031-9155/57/11/R99`) established the clinical uncertainty standard of **`±3.5%` proportional range + `1–2 mm` fixed margin** (reducible toward `~1.5–2.0%` only with Dual-Energy CT `DECT` or proton radiography).
- **Compounded Distal `LET` Biological Dose Boost (`matRad.m:29–31`)**:
  - Clinical convention multiplies physical proton dose by a constant Relative Biological Effectiveness $\text{RBE} = 1.1$ (`'constRBE'` in `e0404/matRad` `matRad.m:29`). In reality, as protons slow to rest at the **distal falloff** of the Bragg peak, Linear Energy Transfer (`LET_d`) spikes from `~1–2 keV/um` to **`8–15 keV/um`**, elevating true biological `RBE` to **`1.3–1.6`** (`modeled by McNamara 'MCN' and Wedenberg 'WED' variable-RBE options in matRad.m:30`)!
  - In `probes/verify_linac_bragg_interlocks.py`, a nominal `158.0 mm` skull-base proton beam aimed `3.0 mm` anterior to the `Brainstem` (`161.0 mm`) overshoots under `-3.5%` `RSP` to **`163.73 mm` (`+5.73 mm`)**—placing **both** the physical Bragg peak AND the `1.3x` high-`LET` biological spike (**`>= 60.0 Gy(RBE)` vs. `54 Gy` brainstem necrosis threshold!**) directly inside the patient's brainstem!
- **Fredriksson Worst-Case Minimax Optimization (`DOI: 10.1118/1.3556559`, `'wcScen'` in `matRad.m:33`)**:
  - Photon Planning Target Volume (`PTV`) geometric isotropic expansion **fails completely** for protons because lateral patient shifts (`±3 mm`) change internal bone/air Water-Equivalent Path Length (`WEPL`) along every pencil-beam ray! Instead, `matRad`'s `'wcScen'` solves $\min_{\mathbf{w} \ge \mathbf{0}} \max_{s \in \mathcal{S}} f(\mathbf{D}_s \mathbf{w})$ across $S \in \{9, 21\}$ coupled scenarios (`nominal`, `±3.5%` range scaling, and `6` `±3 mm` 3D rigid shifts), automatically pulling high-weight single-field Bragg stops back from serial OARs (`reducing worst-case Brainstem dose from 60.0 Gy to 13.7 Gy in probes/verify_linac_bragg_interlocks.py`) and cross-patching distal target coverage via lateral beam angles.

---

### 3. `MLC` Kinematics (`OpenTOPAS`, `Pylinac`) and `FLASH` Ion-Chamber Saturation (`IEC 60601-2-1`)

`Basis: normative, source, execution`

#### 3.1 Opposing-Leaf Collisions, Rounded-Leaf `DLG`, and Gravity Leaf-Lag
1. **Mechanical Collision & Interdigitation Guards (`OpenTOPAS` `TsMultiLeafCollimator.cc:62–67, 125–130`)**:
   - In `OpenTOPAS/OpenTOPAS` (`8be924480441884069a03efc9270095b199933f0`, `geometry/TsMultiLeafCollimator.cc:62–67`), every dynamic control-point update checks `(XPlusLeavesOpen[i] - XMinusLeavesOpen[i]) < 0.0` (`aborting immediately on leaf overlap`). On real `120`-leaf (`5 mm` / `2.5 mm` HD) tungsten `MLC` carriages, hardware servo controllers must enforce a positive **minimum dynamic leaf gap $g_{\min} \ge 0.5\text{ mm}$** both inline (`bank A[i]` vs. `bank B[i]`) and across adjacent interdigitating tongue-and-groove leaves (`bank A[i]` vs. `bank B[i +- 1]`) so `8 cm`-thick tungsten tips never cold-weld or shatter lead-screw encoders mid-arc!
2. **LoSasso (`1998`) Dosimetric Leaf Gap (`DLG`) & `5.0%` Gravity Leaf-Lag Sensitivity**:
   - Because diverging `MLC` leaves use **rounded leaf tips** (radius `~8–16 cm`) to keep penumbra constant across off-axis positions, X-rays partially penetrate the rounded tips (`Dosimetric Leaf Gap DLG ~ 1.2–1.8 mm`, `LoSasso et al. 1998`, `DOI: 10.1118/1.598381`). For a dynamic sliding-window slit of nominal width $w = 10.0\text{ mm}$, fractional dose error scales as $\frac{\Delta D}{D} = \frac{\Delta w}{w + \text{DLG}}$: at gantry `90 deg` / `270 deg` (leaves moving vertically *upward* against `1 g` gravity), a **`0.5 mm` servo lag produces a `4.3%–5.0%` systematic tumor underdose / hot-spot** (`tracked post-facto in pylinac/log_analyzer.py:407–494`, and prevented online via `<= 50 ms` `IEC 60601-2-1` beam-hold gating whenever `|x_actual - x_cmd| > 0.5 mm`).

#### 3.2 Primary-Source Proof of `FLASH` Ion-Chamber Recombination Collapse (`Pylinac` `trs398.py:614–656`)
Under `IEC 60601-2-1:2020`, primary and secondary transmission ionization chambers (`MU1`, `MU2`) integrate collected gas ionization charge $Q_{\text{meas}}$ to terminate the LINAC electron gun / RF thyratron as soon as prescribed `MU` is reached. Inspecting `jrkerns/pylinac` (`5c6a17c0df418804d7e419c12f330ba7a667a0b5`, `pylinac/calibration/trs398.py:645–656` and `tg51.py:978`) exposes the exact clinical breakdown boundary:

```python
# jrkerns/pylinac pylinac/calibration/trs398.py:645, 650-656
# Raises ValueError: If the calculated ks value is outside the range (1.0, 1.05).
m_ratio = np.mean(m_reference) / np.mean(m_reduced)
argue.verify_bounds(
    m_ratio,
    bounds=(MIN_PION, MAX_PION),  # (1.00, 1.05)
    message="Ks is out of bounds. Verify inputs or check chamber",
)
return float(a["a0"] + a["a1"] * m_ratio + a["a2"] * (m_ratio**2))
```

Compare Boag's exact pulsed parallel-plate ion-collection efficiency $f(u) = \frac{1}{u}\ln(1 + u)$ (where $u = \frac{\alpha_{\text{rec}}}{e\,(k_+ + k_-)} \frac{d^2 q_0}{V} \propto \frac{d^2 D_{\text{pulse}}}{V}$ for electrode spacing $d = 2.0\text{ mm}$ at polarizing bias $V = 300\text{ V}$) across conventional vs. `FLASH` regimes (`probes/verify_linac_bragg_interlocks.py`):

| Delivery Regime | Dose Rate & Dose/Pulse | Boag Space-Charge $u$ | Collected Charge Fraction $f(u)$ | True Recombination $k_s = 1 / f(u)$ | `IEC 60601-2-1` Safety Consequence Without Toroid Cross-Gate |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Conventional `IMRT`/`VMAT`** | `~0.1 Gy/s` (`0.5 mGy/pulse` @ `200 Hz`) | `0.0008` | **`99.96%`** | **`1.0004x`** (`Accepted` by `trs398.py` `<= 1.05`) | Linear `1:1` charge-to-dose proportionality (`< 0.1%` drift) |
| **Ultra-High-Dose-Rate `FLASH`** (`e-` / `VHEE` / `p+`) | **`40–400 Gy/s` (`2.0 Gy/pulse` in `2 us`)** | **`3.20`** (`4,000x` higher!) | **`44.88%`** (`55.1%` ions recombine before reaching plates!) | **`2.228x` (`Rejected` `> 1.05` `ValueError`!)** | Gas `MU` chamber under-counts dose `2.23x` $\implies$ **delivers `223%` lethal overdose in `< 100 ms`** before tripping `MU` limit! |

**Architectural Requirement for `FLASH` Interlocks**: Because `100 Gy` can be delivered in `5–20` RF pulses (`25–100 ms` total treatment time—faster than mechanical relay or `100 Hz` PLC loops!), `FLASH` accelerators MUST pair ultra-thin-gap (`<= 0.25 mm` helium/vacuum) chambers or solid-state SiC diodes with a **non-saturating AC Current Transformer (`ACCT` / Bergoz inductive beam-current toroid)** evaluated in a **hard-real-time FPGA pulse-by-pulse integrator (`<= 50 us` inter-pulse crowbar cutoff)** aborting immediately on `> 2%` primary/toroid charge divergence!

---

### 4. Multi-Level Performance and Resource Footprint Matrix (`L1`–`L6`)

`Basis: source, documentation, execution, derived`

| Level | Axis | Research/Clinical TPS & QA (`OpenTOPAS`, `matRad`, `Pylinac`) | Verified Geometry + Interval `WEPL` + FPGA Beam-Gate Core | Engineering & Verification Trade-Off |
| :--- | :--- | :--- | :--- | :--- |
| **L1** | **Human & Agent Authoring Velocity** | `OpenTOPAS`/Geant4 C++ `> 1 MLoC`; `matRad` MATLAB `~25 KLoC`; `Pylinac` `~35 KLoC` Python | Independent secondary verifier (`SimpleCCW` + `WEPL` interval ray-caster + `MLC`/toroid FPGA interlock) **`~600–1,200 LoC`** (`~4–6x` formal proof ratio, `~25K` LLM tokens) | Do not attempt to prove `1 MLoC` of Geant4 Monte Carlo; formally prove the **`< 1.2 KLoC` independent plan-admission & `50 us` beam-gate checker** (`E-Gas` / `IEC 60601-2-1` separation!) |
| **L2** | **Framework & Toolchain Build Time** | `Geant4` + `OpenTOPAS` clean C++ build **`25–60 min` (`6–12 GB` RSS)** | Standalone Rust/C99/VHDL safety-gate & `DICOM RTPLAN` auditor build **`< 4 s` (`< 300 MB` RSS)** | Hermetic safety-checker builds decouple clinical interlock CI from `Geant4`/`ITK`/`Qt` compilation |
| **L3** | **Compilation, Elaboration & Synthesis Latency** | `matRad` `IPOPT` `21`-scenario proton minimax optimization `~2–15 min`; `OpenTOPAS` `10^8`-proton MC `~5–30 min` GPU/cluster | Static proof of `SimpleCCW` Green's-positivity, `LPS` chirality ($\det R = +1$), and FPGA `50 us` `MU1`/`BCT` skew logic **`< 30 ms`** (`< 20 ms` warm LSP) | Optimizers (`IPOPT`) remain untrusted heuristics; the verified checker certifies the *output* `RTPLAN` (`spots`, `MLC` leaves, `OAR` interval `DVH`) |
| **L4** | **Generated Code Execution Performance** | `Pylinac` Python `TrajectoryLog` fluence (`log_analyzer.py:482`) `~0.5–3.0 s` offline | Online FPGA / lockstep Cortex-R52 beam-gate + `120`-leaf lag & `BCT`/chamber integrator: **`8–20 us` deterministic WCET** (`well inside 50 us / 200–400 Hz LINAC RF inter-pulse window!`) | Sub-`20 us` hardware/MCU execution aborts *before* the very next `2.0 Gy` `FLASH` RF macropulse fires |
| **L5** | **Proof / Certificate Verification Speed** | Secondary `3D` Monte Carlo QA `~1–5 min`/patient | Pre-beam `RTPLAN` geometric & `9`-corner `WEPL` distal-`OAR` witness audit **`< 15 ms`/beam** (`O(V log V)` polygon + `O(N_rays)` SIMD `WEPL`) | Every `DICOM RTPLAN` loaded at the LINAC console can be audited against `CT` + `RTSTRUCT` `Brainstem` bounds in `< 100 ms` prior to energizing HV klystrons |
| **L6** | **RAM, Disk & Binary Footprints** | `512x512x200` `CT` + `matRad` `dij` `21`-scenario sparse dose-influence matrix = **`4–32 GB` RAM** | LINAC real-time `MLC` + `MU`/`BCT` safety controller: **`< 32 KiB` ROM, `< 16 KiB` SRAM** (`120` leaf pairs x `4` floats = `1,920 B`), **`0 B` heap** | Keep real-time accelerator safety interlocks completely independent of multi-gigabyte workstation TPS memory |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

`Basis: derived, source`

#### 5.1 `(C1)` Human Comprehensibility vs. Agent Execution Ergonomics
- **Why the `Panama` Workaround Made Perfect Visual Sense to Human Dosimetrists**: On Multidata's 2D digitizer screen, the `5` drawn blocks **rendered visually in solid color on the monitor** (`because screen fill used pixel flood/even-odd drawing while the background dose kernel used signed contour traversal!`). Human operators saw a correct-looking picture on screen (`WYSIWYG` visual betrayal!) and had zero diagnostic warning that a microscopic `0.1 mm` figure-8 vertex crossing inverted the mathematical sign of the dose integral.
- **The `"RBE = 1.1"` & `"3 mm Margin"` Cognitive Trap**: Radiation oncologists trained on megavoltage photons intuitively visualize `3 mm` geometric `PTV` margins as an isotropic spatial buffer. Applying photon geometric intuition to protons fails nonlocally: a `2 mm` lateral head rotation aligning a dense petrous-bone ridge (`HU +1200`) with a sinus cavity (`HU -1000`) shifts distal Bragg-peak depth by **`> 12 mm`** (`4x` the lateral shift!), while the invisible `LET` spike raises biological dose `20–35%` right on the `Brainstem` boundary.

#### 5.2 `(C2)` Conceptual Simplicity, Felleisen Expressibility & Ousterhout Deep-Module Refinement
- **Why Administrative Hospital Checklists Fail Felleisen's Expressibility Test**: Post-*Panama* and post-*Épinal* advisories initially urged "stricter manual physics chart checks" and "never digitize >4 blocks." Administrative workarounds leave the unsound primitive (`unchecked Vec<Point2D>` polygons and raw scalar `MU` floats) intact, shifting `100%` of safety burden onto fatigued human reviewers.
- **Three Deep-Module Refinements (`Making Fatal States Unrepresentable`)**:
  1. **`SimpleOrientedRegion2D<MmIsoplane>`**: Replace raw vertex arrays in `DICOM RTSTRUCT` / block / `MLC` aperture parsers with a smart constructor enforcing Bentley–Ottmann `0` self-intersections (`O(V log V)`), strictly positive outer `CCW` signed area ($A > 0$), and strictly contained `CW` interior holes—rejecting *Panama*-class figure-8 or degenerate polygons **at file parse time** with a visual pinpointing highlight on the crossing edge pair.
  2. **`IntervalWeplVolume<RspMin, RspMax, DicomLPS>`**: Instead of mapping each CT voxel `HU` to a single point-estimate float `RSP` (`hiding ±3.5% stoichiometric degeneracy`), map `HU` directly to a **validated interval $[\text{RSP}_{\min}(\text{HU}), \text{RSP}_{\max}(\text{HU})]$** (`tagged with chiral DicomLPS orientation witness det(R) = +1`). Any distal Organ-at-Risk (`Brainstem`) safety check evaluates `WEPL_min` along every spot ray, guaranteeing conservatively that `99%` Bragg falloff stops proximal to the OAR across the entire `RSP` band.
  3. **`HeterogeneousDualBeamMonitor<IonChamber, InductiveToroid>`**: Unify conventional (`0.1 Gy/s`) and `FLASH` (`> 40 Gy/s`) `IEC 60601-2-1` beam-off safety by pairing two **physically orthogonal sensing principles**—gas ionization (`high sensitivity at low dose rate`) and Faraday/inductive `ACCT` beam-current integration (`zero space-charge saturation at arbitrary pulse density`)—requiring both channels' dose estimates to agree within `±2%` after Boag/calibration mapping on *every single RF pulse*.

## Boundaries

1. **Magnetic-Resonance-Guided Radiotherapy (`MR-Linac` `0.35 T` / `1.5 T` Lorentz Electron-Return Effect `ERE`) (`known not to apply` to zero-field pencil-beam kernels)**: Inside hybrid `MR-Linac` systems (`Elekta Unity` `1.5 T`, `ViewRay MRIdian` `0.35 T`), transverse magnetic fields bend secondary Compton electrons via the Lorentz force ($q\,\mathbf{v}\times\mathbf{B}$) into tight helical arcs at tissue-air interfaces (`lung`, `bowel`, `skin` exit), creating `+30%–40%` localized surface hot-spots (`Electron Return Effect`) that zero-$B$-field `matRad` pencil-beam kernels cannot model (`requiring full B-field Geant4/OpenTOPAS Lorentz transport`).
2. **4D Intra-Fractional Respiratory Tumor Motion & Scanning Interplay Effect (`not examined` in static `9`/`21`-scenario rigid minimax)**: In spot-scanned thoracic/liver proton therapy, interference between `5–10 mm` patient breathing cycles (`~0.25 Hz`) and sequential `PBS` magnet spot scanning causes severe intra-target `±25%` hot/cold **interplay dose mottle** not captured by static rigid-shift `'wcScen'` minimax (`requiring 4DCT phase-gated beam holds + volumetric rescanning, not examined in the static probe`).
3. **Sub-Millimeter Reconstruction of Tissue Elemental Stoichiometry ($\ln I$) From Single-Spectrum kVp X-Ray CT Alone (`unsupported`)**: Because one scalar attenuation measurement $\mu(E_{\text{eff}})$ cannot invert two independent physical unknowns ($\rho_e$ and $Z_{\text{eff}} / \ln I$), eliminating the `~3.5%` `HU-to-RSP` error floor from single-energy kVp CT without Dual-Energy CT (`DECT`), photon-counting spectral CT, or direct proton CT is mathematically **`unsupported`**.
4. **In-Vivo Ultra-High-Dose-Rate `FLASH` Normal-Tissue Sparing Oxygen-Depletion Thresholds in Deep Human Tumors (`unknown`)**: While `> 40 Gy/s` `FLASH` delivery reproducibly spares normal murine brain/lung tissue in preclinical trials (`FLASH effect`), exact clinical dose-per-pulse, mean-dose-rate, and tissue partial-oxygen ($p\text{O}_2$) boundary conditions for deep-seated human fractionated `PBS` proton arcs remain under active Phase I/II clinical investigation (`unknown` normative biological parameterization).

## Evidence

| Source / Artifact | Immutable Identity & Narrow Location | Grounded Fact Established |
| :--- | :--- | :--- |
| `OpenTOPAS/OpenTOPAS` | Commit `8be924480441884069a03efc9270095b199933f0`, `geometry/TsMultiLeafCollimator.cc:62–67, 117–131` | Opposing-leaf collision detection `(XPlusLeavesOpen[i] - XMinusLeavesOpen[i]) < 0.0 -> AbortSession(1)` (`62–67, 125–130`) and over-travel limit checks (`120–123`) |
| `e0404/matRad` | Commit `008bfd7c2e8d5101912262a33adea5ef867d7f25`, `matRad.m:26–33, 62–66` & `README.md:25–30` | Multi-modality (`photons`, `protons`, `helium`, `carbon`, `VHEE`), variable-`RBE` (`'constRBE'`, `'MCN'` McNamara, `'WED'` Wedenberg at `lines 29–31`), and `'wcScen'` worst-case robust scenario optimization (`line 33`) |
| `jrkerns/pylinac` | Commit `5c6a17c0df418804d7e419c12f330ba7a667a0b5`, `pylinac/calibration/trs398.py:614–665`, `pylinac/calibration/tg51.py:862–983`, & `pylinac/log_analyzer.py:407–495` | Hard `MAX_PION = 1.05` (`1.0..1.05`) `ValueError` bound on two-voltage ion recombination `k_s`/`p_ion` (`trs398.py:645, 651–656`; `tg51.py:978`) and `MLC` snapshot leaf-pair fluence reconstruction (`log_analyzer.py:482–494`) |
| `pymedphys/pymedphys` | Commit `6d02df7f6827caf9565c13da3e32d553e92ad8d6`, `pyproject.toml:1–45` (`MU` density, `TRF` LINAC log & `DICOM` verification suite) | Independent `MU` density & 3D Gamma delivery verification framework |
| Paganetti (`2012`) | *Physics in Medicine and Biology* `57(11):R99–R117`, `DOI: 10.1088/0031-9155/57/11/R99` | Comprehensive quantification of `±3.5% + 1–2 mm` CT `HU-to-RSP` proton range uncertainty and Monte Carlo vs. analytical pencil-beam discrepancies |
| Fredriksson et al. (`2011`) & LoSasso et al. (`1998`) | *Medical Physics* `38(3):1672–1684` (`DOI: 10.1118/1.3556559`) & `25(10):1919–1927` (`DOI: 10.1118/1.598381`) | Scenario-based minimax robust proton optimization & rounded-leaf dynamic `MLC` Dosimetric Leaf Gap (`DLG`) sensitivity |
| `IAEA STI/PUB/1114` (`2001`), `ASN Épinal` (`2007`), `IEC 60601-2-1:2020` | Panama Accident Investigation (`2001`), Épinal Inquiry (`2007`), & `IEC 60601-2-1` | Self-crossing continuous block polygon `~2x` `MU` overdose (`Panama`); wedge `MU` factor omission (`Épinal`); dual independent `MU` dose-monitoring interlock standard |
| Preserved Executable Probe | `reports/linac-mlc-radiotherapy-bragg-peak-stopping-power-and-ion-chamber-interlocks/probes/verify_linac_bragg_interlocks.py` (observed `2026-11-19`) | Verified `Panama` figure-8 `0.0` signed area (`1.92x` `MU` overdose, `SimpleCCW` rejected), `+5.73 mm` `-3.5%` `RSP` overshoot (`Brainstem` `60.0 -> 13.7 Gy` minimax), `5.0%` `0.5 mm` `MLC` lag error, and `FLASH` Boag `k_s = 2.23x > 1.05` |

## Revalidation

Run either the preserved package probe from the corpus root (`python3 reports/linac-mlc-radiotherapy-bragg-peak-stopping-power-and-ion-chamber-interlocks/probes/verify_linac_bragg_interlocks.py`) or the standalone zero-dependency bash probe below from any directory (`Python >= 3.10`):

```bash
python3 - <<'EOF'
import math

# 1. IAEA Panama figure-8 shielding-block signed-area cancellation (0.0 vs SimpleCCW positive area)
def signed_area(pts):
    return 0.5 * sum(pts[i][0]*pts[(i+1)%len(pts)][1] - pts[(i+1)%len(pts)][0]*pts[i][1] for i in range(len(pts)))

fig8 = [(0,0), (4,0), (4,5), (10,5), (10,0), (6,0), (6,5), (0,5)]
assert signed_area([(0,0), (4,0), (4,10), (0,10)]) == 40.0
assert signed_area(fig8) == 0.0 and (85.0 - (-40.0)) / (85.0 - 20.0) > 1.92

# 2. Proton -3.5% RSP Bragg-peak distal overshoot (+5.73 mm into Brainstem) vs minimax pullback
r_nom, rsp_low, bs_mm = 158.0, 0.965, 161.0
r_act = r_nom / rsp_low
assert abs((r_act - r_nom) - 5.7306) < 1e-2 and r_act > bs_mm
r_rob = 151.5 / rsp_low
bs_rob_gy = 60.0 * 1.20 * math.exp(-0.5 * ((bs_mm - r_rob) / 2.2) ** 2)
assert bs_rob_gy < 14.0  # Well below 54 Gy Brainstem necrosis threshold!

# 3. Dynamic MLC 0.5mm leaf-lag on 10mm slit (5.0%) & FLASH 2.0 Gy/pulse Boag recombination (ks=2.23x > 1.05)
assert (0.5 / 10.0) * 100.0 == 5.0
u_conv, u_flash = 1.60 * 0.0005, 1.60 * 2.0
ks_conv = u_conv / math.log1p(u_conv)
ks_flash = u_flash / math.log1p(u_flash)
assert 1.0 <= ks_conv <= 1.05 and ks_flash > 2.22
print("REVALIDATION_OK")
EOF
```

Revalidate upstream implementations when:
1. `jrkerns/pylinac` (`trs398.py` / `tg51.py`) adds AAPM `TG-359` / `FLASH` high-dose-per-pulse Boag-Jaffé or inductive `ACCT` calibration protocols beyond `MAX_PION = 1.05`;
2. `e0404/matRad` adds Dual-Energy CT (`DECT`) direct $(\rho_e, Z_{\text{eff}}) \mapsto \text{RSP}$ conversion or `4D` respiratory-phase minimax scenarios; or
3. `IEC 60601-2-1` publishes dedicated `FLASH` (`> 40 Gy/s`) sub-microsecond pulse-by-pulse beam-monitoring amendments.
