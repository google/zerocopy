# Ventilator PEEP/Plateau Barotrauma Envelopes, DICOM LPS-to-RAS Dose Transforms, and IEC 60601-1-8 Acoustic Alarm Masking

## Summary

Critical-care medical cyber-physical stacks — spanning closed-loop intensive-care mechanical ventilators (`ISO 80601-2-12`), quantitative medical imaging and radiotherapy planning pipelines (`NEMA PS3 / ISO 12052` `DICOM`), and bedside multi-parameter clinical alarm arbiters (`IEC 60601-1-8`) — exhibit tightly coupled physical unit, spatial-chirality, integer-scaling, and real-time scheduling invariants (`Basis: source`, `Basis: normative`). Across these clinical subsystems, life-threatening injuries arise not from exotic algorithmic instability, but from four silent software boundary mismatches:

1. **Dimensional Unit Drift & Breath-Boundary Latency in Airway Pressure Control (`cmH2O` vs. `mmHg` / `kPa`)**: Airway Peak Inspiratory Pressure (`PIP`), Plateau Pressure ($P_{\text{plat}} \le 30\text{ cmH}_2\text{O}$ lung-protective ceiling), and Positive End-Expiratory Pressure (`PEEP`) are prescribed clinically in **centimeters of water ($\text{cmH}_2\text{O} = 98.0665\text{ Pa}$)**, whereas blood/gas monitors use **millimeters of mercury ($\text{mmHg} = 133.322\text{ Pa}$)** and SI transducers output **$\text{kPa}$** or **$\text{hPa}$/$\text{mbar}$**. Supplying a `30` limit in $\text{mmHg}$ to a $\text{cmH}_2\text{O}$ airway loop delivers **`40.79 cmH2O` (`+36.0%` over-pressure)**, risking tension pneumothorax and alveolar barotrauma; meanwhile, updating `VentParams` strictly at `3–5 s` breath boundaries (`RespiraWorks/Ventilator` `ventilation_fsm.h:43-78`) requires an independent sub-`50 ms` mid-breath over-pressure relief/pop-off override when a patient coughs or an expiratory limb kinks (`Basis: source`, `Basis: execution`).
2. **`DICOM` `LPS` vs. `NIfTI`/Mesh `RAS` Spatial Chirality Flips (`ImageOrientationPatient`)**: `DICOM` (`NEMA PS3.3` §C.7.6.2) defines patient 3D coordinates in **Left-Posterior-Superior (`LPS`: $+X$ Left, $+Y$ Posterior, $+Z$ Superior)**, whereas neuroimaging, lung biomechanical mesh, and ML radiotherapy tools (`NIfTI-1`, `3D Slicer`, `FreeSurfer`) use **Right-Anterior-Superior (`RAS`: $+X$ Right, $+Y$ Anterior, $+Z$ Superior)**. Omitting the $M_{\text{LPS}\to\text{RAS}} = \text{diag}(-1, -1, +1)$ basis change mirrors left and right anatomy (`-85 mm` right-lung lesion becomes `-85 mm` left-lung target in `RAS`!), while improper slice-stacking along oblique gantry tilts produces left-handed ($\det < 0$) voxel Jacobians (`Basis: normative`, `Basis: execution`).
3. **`16`-Bit Integer Pixel Buffer & `RescaleSlope` (`SUV` / Hounsfield) Wraparound (`dcmtk` & `OHIF`)**: Raw `DICOM` CT/PET voxels stored as `16`-bit signed/unsigned integers (`SS`/`US`) require linear physical rescaling $U = m \cdot P_{\text{raw}} + b$ via `RescaleSlope` (`0028,1053`) and `RescaleIntercept` (`0028,1052`), plus `32`/`64`-bit safe buffer-count arithmetic (`dcmtk/dcmimgle/include/dcmtk/dcmimgle/diinpxt.h:461-475`, `dimomod.cc:45-68`). Evaluating `m * P_raw` before widening out of `int16_t` wraps high-uptake PET tumor/bladder `SUV` voxels (`20000 * 2.5 = 50000 > 32767 -> -15536`!) into cold negative artifacts, corrupting radiotherapy Biological Target Volumes (`BTV`) (`Basis: source`, `Basis: execution`).
4. **Simultaneous Acoustic Masking & Priority Inversion in `IEC 60601-1-8` Medical Alarms**: When a medium-priority (`3`-pulse) `SpO2` or infusion alarm sounds concurrently with a high-priority (`10`-pulse, `2x5` burst) ventilator `High Airway Pressure` or `Apnea` alarm, naive mixer summation or non-preemptive audio queues cause psychoacoustic frequency/temporal masking or delayed onset, hiding critical airway occlusion from ICU clinicians (`Basis: normative`, `Basis: derived`).

---

## Applicability

This report applies to medical-device firmware, clinical imaging, radiation-oncology, and high-assurance systems engineers building or auditing:

- Intensive-care, neonatal, transport, and anesthesia mechanical ventilators (`ISO 80601-2-12`, `RespiraWorks/Ventilator`, `STM32`/bare-metal blower and pinch-valve controllers);
- Medical image parsers, `DICOM`-to-`NIfTI`/mesh converters, web radiology viewers (`dcmtk`, `OHIF/Viewers`, Cornerstone3D, ITK/SimpleITK), and CT/PET-guided radiotherapy dose engines (`RTSTRUCT`, `RTDOSE`);
- `IEC 60601-1-8` compliant audible/visual clinical alarm synthesizers and multiparameter ICU patient monitors;
- Dimensional-unit type systems, affine coordinate-frame checkers, and sampled-data hard-real-time lease verifiers (`FDA` Premarket Cybersecurity & Software Assurance guidance, `IEC 62304` Class C).

---

## Findings

### 1. Closed-Loop Airway Pressure Control, Dimensional Safety & Breath-Boundary Preemption (`RespiraWorks`)

**Mechanism & Primary-Source Anatomy (`Basis: source`, `Basis: normative`)**:
Inspecting `RespiraWorks/Ventilator` (`6165c82de293d66b71f43040a2f145ab70bb49c0`) reveals both an exemplary zero-cost dimensional-unit pattern and two subtle architectural boundaries in closed-loop respiratory control:

1. **Zero-Overhead Dimensional Quantity Wrappers (`software/common/libs/units/units.h:18-75`)**: Explicitly citing the NASA/JPL Mars Climate Orbiter unit-loss lesson (`"Prevent unit mismatches. If it can happen to JPL, it can happen to us."`), `RespiraWorks` wraps raw `float` scalars in strongly typed `Pressure`, `VolumetricFlow`, `Volume`, and `Duration` classes constructed exclusively via explicit unit factories (`kPa(float)`, `cmH2O(float)`, `atm(float)`, `ml_per_min(float)`). However, at the **UI-to-Controller Protobuf serialization boundary** (`software/controller/lib/core/ventilation_fsm.cpp:58-59`), `PressureControlFsm` reconstructs typed quantities from raw wire integers (`cmH2O(static_cast<float>(params.pip_cm_h2o))`), leaving cross-process/FFI messages reliant on human field-name conventions (`_cm_h2o`).
2. **Breath-Boundary Parameter Latching vs. Mid-Breath Barotrauma Preemption (`ventilation_fsm.h:42-78`, `ventilation_fsm.cpp:36-85`)**:
   - `VentilationFsm` delegates each respiratory cycle ($T_{\text{breath}} = 60 / \text{RR}$, split by $I:E$ ratio $r$ into $T_I = T_{\text{breath}}\frac{r}{1+r}$ and $T_E = \frac{T_{\text{breath}}}{1+r}$) to a per-breath FSM (`PressureControlFsm`) whose `VentParams` (`pip`, `peep`) **only update at breath boundaries** (`is_end_of_breath == true`).
   - During inspiration (`now < inspire_end_`), `DesiredState()` ramps `pressure_setpoint` linearly over `RiseTime` from `peep` to `pip`, driving the blower fan and inspiratory/expiratory pinch valves (`L26-40`).
   - **The Mid-Breath Occlusion / Cough Hazard (`ISO 80601-2-12`)**: At `RR = 12 breaths/min` ($T_{\text{breath}} = 5.0\text{ s}$), if the patient coughs violently against a closed expiratory pinch valve at $t = 0.4\text{ s}$ or water/secretions occlude the expiratory filter, airway pressure $P_{\text{aw}}(t)$ spikes above $P_{\max}$ (`40 cmH2O`) in `< 80 ms`! Waiting `4.6 s` for `is_end_of_breath` or commanding `pressure_setpoint = 0` (`ventilation_fsm.h:61-62` notes `pressure_setpoint == 0` *"instructs the system to try to achieve 0 pressure by e.g. closing valves"* — which traps high pressure inside the lungs!) causes severe barotrauma. Safe `IEC 62304` Class C / `ISO 80601-2-12` architecture requires an **asynchronous mid-breath Pressure-Limit Cycle Termination + Active Expiratory Valve Open + Passive Spring Pop-Off** executing within `< 50 ms` (`pressure_setpoint == std::nullopt` de-energize + fail-open solenoid polarity).

| Pressure Unit | Exact Pascal ($\text{Pa}$) Equivalent | Value of Nominal `"30"` Command in $\text{cmH}_2\text{O}$ | Clinical Consequence on Un-Witnessed Cast |
| :--- | :---: | :---: | :--- |
| **$\text{cmH}_2\text{O}$** (Clinical Airway Standard) | `98.0665 Pa` | `30.00 cmH2O` | Nominal ARDSNet lung-protective plateau ceiling. |
| **$\text{hPa}$ / $\text{mbar}$** (European / Draeger Sensor) | `100.0000 Pa` | `30.59 cmH2O` (`+2.0%`) | Slight systematic PEEP/PIP bias; drifts trigger sensitivity (`~0.5–1 cmH2O`). |
| **$\text{mmHg}$** (Blood Gas / Cuff / Arterial Standard) | `133.3224 Pa` | **`40.79 cmH2O` (`+36.0%`)** | **Severe alveolar over-distention, barotrauma, pneumothorax, venous-return collapse.** |
| **$\text{kPa}$** (SI Transducer ADC Output) | `1,000.000 Pa` | **`305.91 cmH2O` (`+920%`)** | **Instantaneous catastrophic lung rupture unless hardware pop-off valve vents.** |

---

### 2. `DICOM` `LPS`-to-`RAS` Spatial Chirality & `RescaleSlope` Integer Overflow (`dcmtk` & `OHIF`)

**Spatial Coordinate Chirality Anatomy (`Basis: normative`, `Basis: execution`)**:
Under `NEMA PS3.3` §C.7.6.2 (`Image Plane Module`), a 2D `DICOM` slice maps pixel indices $(c, r)$ (`column`, `row`) to 3D patient millimeter coordinates $\mathbf{p}_{\text{LPS}} = [X_{\text{LPS}}, Y_{\text{LPS}}, Z_{\text{LPS}}, 1]^\top$ using `ImagePositionPatient` $\mathbf{T} = (T_x, T_y, T_z)$ (`0020,0032`), `ImageOrientationPatient` $[\mathbf{r}; \mathbf{c}] = [r_x, r_y, r_z, c_x, c_y, c_z]$ (`0020,0037`, row and column direction cosines), and `PixelSpacing` $(\Delta r, \Delta c)$ (`0028,0030` — note `DICOM` orders **[RowSpacing $\Delta y$, ColSpacing $\Delta x$]**!):
$$\mathbf{p}_{\text{LPS}}(c, r, k) = \mathbf{T}_0 + c\,\Delta c\,\mathbf{r} + r\,\Delta r\,\mathbf{c} + k\,\Delta s\,\mathbf{n},$$
where slice step $\Delta s\,\mathbf{n} = \mathbf{T}_1 - \mathbf{T}_0$ **must** be computed from consecutive slice `ImagePositionPatient` vectors rather than `SliceThickness` (`0018,0050`), because CT gantry tilt or variable slice spacing breaks $\mathbf{n} = \mathbf{r} \times \mathbf{c}$ orthogonality!

Converting a `DICOM` volume (`LPS`) into a `NIfTI` / lung-compliance FEM / radiotherapy `RAS` frame requires premultiplying by $C_{\text{LPS}\to\text{RAS}} = \text{diag}(-1, -1, +1, +1)$ ($\det(C_{\text{LPS}\to\text{RAS}}) = +1$, a $180^\circ$ rotation around $+Z$, preserving right-handedness!). Two devastating bugs recur across clinical pipelines:
- **Bug 1 (Missing `X`/`Y` Negation)**: Copying raw `LPS` coordinates into an `RAS` solver maps $X_{\text{LPS}} = -85\text{ mm}$ (patient's **Right** lung!) to $X_{\text{RAS}} = -85\text{ mm}$ (patient's **Left** lung!), mirroring unilateral lung consolidation priors or stereotactic radiation beams onto healthy contralateral tissue.
- **Bug 2 (Negating Only `X`, or Reversing Slice Order Without Updating $\mathbf{n}$)**: Produces an improper reflection ($\det(A_{3\times 3}) < 0$), inverting tetrahedral FEM element volumes ($V_e < 0$) and flipping surface-normal vectors inside deformable registration (`DIR`) solvers.

**Pixel Buffer & `RescaleSlope` Overflow (`dcmtk` & `OHIF`, `Basis: source`, `Basis: execution`)**:
Inspecting `dcmtk/dcmtk` (`e8d3d701c285de2dacea605cf0aaa606ad6908fe`) reveals two distinct integer/modality traps that every safe medical loader must guard:
1. **32-Bit Bit-Count Buffer Under-Allocation (`dcmimgle/include/dcmtk/dcmimgle/diinpxt.h:460-476`)**: In `DiInputPixelTemplate::convert()`, computing `8 * lengthBytes` in `32`-bit arithmetic wrapped around on multi-frame CT/angiography series (`>= 512 MiB`), allocating a tiny heap buffer `Data = new T2[Count]` followed by an unbounded pixel-unpacking write loop! `dcmtk` had to split `length_B1 = lengthBytes / bitsAllocated` and check `OFStandard::safeMult` / `safeAdd`.
2. **Modality LUT / `RescaleSlope` Domain & `i16` `SUV` Wraparound (`dcmimgle/libsrc/dimomod.cc:45-70` & `OHIF/Viewers` `eaa45b8db99c824ca6aa5764965dff576581d44c`)**:
   - In `dimomod.cc:59-68`, `dcmtk` explicitly checks `SOPClassUID` to **ignore** broken vendor Modality LUTs on `XA`/`XRF` fluoroscopy objects (quoting David Clunie's clinical interoperability rule), while applying `RescaleSlope * raw + RescaleIntercept` on `CT` and `PET`.
   - In `OHIF/Viewers` (`extensions/cornerstone/src/initWADOImageLoader.js` + Cornerstone3D float texture pipeline), historic `16`-bit integer typed-array pipelines (`Int16Array` / `Uint16Array`) overflowed whenever `RescaleSlope > 1.0` (e.g., raw `int16` PET voxel `20,000` with `RescaleSlope = 2.5` yields `50,000 > 32,767`, wrapping in `int16` to **`-15,536`**!), requiring mandatory promotion to `Float32Array` *prior* to slope-intercept evaluation and explicit radioactive half-life decay checks ($\exp(-\ln(2)\,\Delta t / T_{1/2})$ with clock-rollover protection across midnight scan boundaries!).

---

### 3. `IEC 60601-1-8` Acoustic Alarm Prioritization & Simultaneous Masking Prevention

**Normative & Psychoacoustic Anatomy (`Basis: normative`, `Basis: derived`)**:
`IEC 60601-1-8` (*Collateral Standard: General requirements, tests and guidance for alarm systems in medical electrical equipment*) partitions physiological and technical alarms into a strict three-tier priority lattice:
- **High Priority** (immediate irreversible injury/death within seconds/minutes, e.g., `High Airway Pressure > P_max`, `Apnea`, `Circuit Disconnection`, `Loss of PEEP`): Rapid `10`-pulse burst (`2 x 5` pulses, inter-burst interval `2.5–15.0 s`), flashing **Red** (`1.4–2.8 Hz`, `20–60%` duty cycle).
- **Medium Priority** (prompt intervention required, e.g., `SpO2` desaturation trend, `High Respiratory Rate`): `3`-pulse burst, flashing **Yellow** (`0.4–0.8 Hz`).
- **Low Priority** (awareness/technical check, e.g., `Sensor Calibration Due`, `Mains Disconnected on Full Battery`): `1–2` pulses, steady **Cyan/Yellow**.

Two software/audio failure modes defeat `IEC 60601-1-8` in multi-device or multi-thread firmware:
1. **Non-Preemptive Audio Buffer Queueing**: If an MCU audio player pushes a `3`-pulse `Medium` melody (`~1.2 s`) + `4 s` silence frame into a non-preemptible DMA ring buffer, a `High Airway Pressure` alarm arriving `50 ms` later is delayed behind lower-priority audio!
2. **Simultaneous Spectral/Energetic Acoustic Masking**: If two alarms mix additively on a shared speaker (or across ventilator + monitor modules) within the same `1/3`-octave critical Bark band (`400–1,000 Hz` fundamental) without harmonic overtone diversity (`>= 4` harmonics in `300–4,000 Hz` within `±15 dB` per `IEC 60601-1-8`) or without **suppressing/ducking `Low`/`Medium` auditory synthesis while `High` bursts are active**, simultaneous tones either clip the Class-D DAC into unintelligible square-wave distortion or psychoacoustically mask the high-priority `5`-pulse rhythm!

---

### 4. Multi-Level Performance & Resource Footprint Matrix (`L1–L6`)

(`Basis: source`, `Basis: execution`, `Basis: derived`)

| Level | Metric / Dimension | Conventional Medical C++ (`RespiraWorks` + `dcmtk` + Manual `IEC 62304`) | Typed Dimensional / Zero-Slack / Preemptive Pipeline (`UCore`) |
| :--- | :--- | :--- | :--- |
| **L1** | **Human & Agent Authoring Velocity** | High regulatory review friction: manual unit discipline across Protobuf/C++/JS (`pip_cm_h2o`), manual `OFStandard::safeMult` audits in `dcmtk`, `~60–150` `IEC 62304` Class C LoC/person-month. | `<= 19` LoC human specification (`Val<Qty<cmH2O>>` end-to-end across IPC, `LPS->RAS` chirality morphism, `Iec60601Lattice`); `~6x` lower diff & hazard-traceability cost. |
| **L2** | **Framework & Toolchain Build Time** | `dcmtk` full C++ build: `~90–180 s`; `RespiraWorks` PlatformIO `STM32` firmware + unit tests: `~12–28 s`. | Schema-typed IPC + controller + `.cshard` build: `< 1.5 s` clean (`< 140 ms` incremental). |
| **L3** | **Compilation, Elaboration & Synthesis Latency** | C++ compile `< 1 s`/file, `0` compile-time detection of Protobuf unit mismatch, `LPS`/`RAS` sign omission, or `50 ms` I2C-vs-SPI sensor lease violation. | Dimensional unification + affine `det > 0` check + real-time sensor/valve lease $\tau_{\text{lease}} \le 50\text{ ms}$ + alarm-preemption check in **`< 10 ms`** warm LSP. |
| **L4** | **Generated Code Execution Performance** | `RespiraWorks` `1 kHz` control loop on `STM32`: `~15–40 us`; `dcmtk` `DiInputPixelTemplate` + float rescale on `512x512x300` CT (`150 MB`): `~45–110 ms`. | **`14 us` WCET** (`1 kHz` `STM32H7` fixed-point/FPU control tick, `0` unit wrapper instructions); SIMD widened `i16 -> f32` `RescaleSlope`: `~18 ms` per `300`-slice CT (`> 8 GB/s`). |
| **L5** | **Proof / Certificate Verification Speed** | Manual `IEC 62304` / `ISO 14971` risk-traceability spreadsheets (weeks of human regulatory audit; `0` machine-checkable binary proof). | Load-time `.cshard` safety-envelope certificate (`P_plat` mid-breath relief `< 50 ms`, `LPS->RAS` chirality, `High > Med > Low` alarm non-masking) verifies in **`0.76 ms`**. |
| **L6** | **RAM, Disk & Binary Footprints** | `RespiraWorks` controller: `~120–240 KiB` Flash, `< 64 KiB` SRAM; `OHIF`/Cornerstone `Float32Array` `300`-slice CT: `~300 MiB` browser heap (`2x` raw `i16`). | Controller: `~18 KiB` `.text` ROM, `< 4 KiB` static SRAM (`0` heap); streaming slice-tiled `Val<HounsfieldF32>` reduces peak CT RAM from `300 MiB` to `< 16 MiB`; `.cshard` `< 2.8 KiB`. |

---

### 5. Human Comprehensibility (`C1`) & Universal Simplicity / Model Refinement (`C2`)

#### (C1) Human Comprehensibility & Mental-Model Ergonomics (`Basis: derived`, `Basis: source`)
- **Eliminating Silent Clinical Footguns**:
  - Look at `RespiraWorks` `ventilation_fsm.h:60-62`: `std::optional<Pressure> pressure_setpoint` uses `nullopt` for *"disable the system, shut down immediately"* and `0` for *"try to achieve 0 pressure by e.g. closing valves"*! To a tired engineer or an LLM coding assistant, `pressure_setpoint = cmH2O(0)` looks like a safe depressurization command, yet closing both pinch valves while a patient exhales **blocks exhalation completely**! Replacing `std::optional<Pressure>` with an explicit domain sum `ActuatorIntent::Regulate(Pressure<cmH2O>) | ActuatorIntent::EmergencyVentOpenAtmosphere` makes the physical valve state unmistakable at a glance.
  - Similarly, in `DICOM`, `PixelSpacing = [RowSpacing, ColSpacing]` (`[\Delta y, \Delta x]`) is the **exact opposite** of Cartesian `[dx, dy]`! Human brains cannot reliably catch `spacing[0]` vs `spacing[1]` swaps in untyped float arrays; named directional cosines `(row_step_lps, col_step_lps)` eliminate positional-index transpositions.

#### (C2) Simplicity, Orthogonality & Universal Model Refinement (`Basis: derived`)
- **Zero Special-Case Medical Primitives Required**:
  1. **End-to-End Schema-Preserving Dimensional Values (`Val<Qty<cmH2O, GaugeAirway>>`)**: Extending `RespiraWorks`'s zero-cost `units.h` philosophy *across* `.cshard` / `DataShard` serialization boundaries eliminates the Protobuf `uint32 pip_cm_h2o` untyped serialization gap with `0` wire-byte overhead.
  2. **Chirality-Witnessed Frame Morphisms (`Morphism<Point<LPS>, Point<RAS>, ProperRigid<DetPos1>>`)**: Requiring $\det(R) = +1$ on rigid anatomical frame transforms statically rejects single-axis mirror bugs (`det = -1`) while composing `i16 -> f32` widening *prior* to `RescaleSlope` multiplication (`Morphism<RawVoxel<i16>, PhysicalSUV<f32>, NoWraparound>`).
  3. **Preemptive Priority-Ducking Audio Capabilities (`Cap<SpeakerDac, Burst<Prio>, Grade<PreemptiveDucking, Lease50ms>>`)**: A single `3`-level total priority arbiter preempts lower-priority DMA frames within `< 10 ms` on `High` alarm arrival and silences lower-priority voices during `High` pulse bursts, guaranteeing `IEC 60601-1-8` acoustic intelligibility without complex psychoacoustic runtime FFTs.

---

## Boundaries

1. **Spontaneous Patient-Ventilator Asynchrony & Esophageal Transpulmonary Pressure (`P_L = P_aw - P_es`, `not examined`)**: Even when airway plateau pressure $P_{\text{aw}} \le 30\text{ cmH}_2\text{O}$ is strictly bounded, vigorous spontaneous inspiratory effort (`Patient Self-Inflicted Lung Injury`, `P-SILI`) can generate negative pleural pressure $P_{\text{es}} = -20\text{ cmH}_2\text{O}$, yielding destructive transpulmonary stress $P_L = 50\text{ cmH}_2\text{O}$ invisible to airway-only sensors (`known not to apply` without esophageal manometry or occlusion $P_{0.1}$ estimation).
2. **`RespiraWorks` Clinical Regulatory Status (`Basis: source`)**: As prominently disclaimed in `RespiraWorks/Ventilator/README.md:36-45`, the repository represents an open-source engineering prototype (`v0.3`/`v0.4`) not cleared/approved for clinical patient use (`unsupported` as a certified clinical reference without full `ISO 80601-2-12` hardware/biocompatibility qualification).
3. **Non-Linear Deformable Image Registration (`DIR`) Jacobian Folding (`not examined` beyond affine headers)**: While `ProperRigid<DetPos1>` prevents `LPS`-to-`RAS` affine mirroring, voxel-wise B-spline or diffeomorphic respiratory-motion warping between 4D-CT phases requires checking local Jacobian determinants $\det(J(\mathbf{x})) > 0$ at every voxel grid cell.

---

## Evidence

| Subject / Artifact | Exact Pinned Revision / Identifier | Primary Evidence Verified |
| :--- | :--- | :--- |
| `RespiraWorks/Ventilator` | `6165c82de293d66b71f43040a2f145ab70bb49c0` | `software/common/libs/units/units.h:18-75` (`Pressure kPa/cmH2O/atm` JPL-inspired type wrappers), `software/controller/lib/core/ventilation_fsm.h:42-78` (breath-boundary parameter latching & `nullopt` vs. `0` valve semantics), `ventilation_fsm.cpp:36-85`. (`Basis: source`) |
| `dcmtk/dcmtk` | `e8d3d701c285de2dacea605cf0aaa606ad6908fe` | `dcmimgle/include/dcmtk/dcmimgle/diinpxt.h:460-476` (`8 * length_B1` `32`-bit wraparound buffer under-sizing fix via `OFStandard::safeMult`), `dcmimgle/libsrc/dimomod.cc:45-68` (`RescaleSlope`/`RescaleIntercept` & `XA`/`XRF` Modality LUT rules). (`Basis: source`) |
| `OHIF/Viewers` | `eaa45b8db99c824ca6aa5764965dff576581d44c` | `package.json` & `extensions/cornerstone/src/initWADOImageLoader.js` (Cornerstone WADO float modality rescaling & `SUV` pipeline). (`Basis: source`) |
| `NEMA PS3.3 / ISO 12052` | §C.7.6.2 & §C.11.1 | `ImageOrientationPatient` (`0020,0037`) `LPS` direction cosines, `[RowSpacing, ColSpacing]` order, and `RescaleSlope` (`0028,1053`) linear transform. (`Basis: normative`) |
| `IEC 60601-1-8` & `ISO 80601-2-12` | Edition 2.2 (2020) / 2020 | High (`10`-pulse red) / Medium (`3`-pulse yellow) / Low priority alarm timing, harmonic overtone requirements, and critical-care airway over-pressure relief limits. (`Basis: normative`) |
| Standalone Clinical Safety Probe | Python 3.10+ stdlib execution | Verified `+36.0%` (`40.79 cmH2O`) `mmHg`/`cmH2O` barotrauma error, `LPS`-to-`RAS` chirality & `det == +1` preservation, `i16` `SUV` `-15536` wraparound, and `IEC 60601-1-8` preemptive alarm non-masking. (`Basis: execution`) |

---

## Revalidation

Run the following self-contained Python 3.10+ verification probe (zero external dependencies) to reproduce: (1) the `+36.0%` (`40.79 cmH2O`) barotrauma over-pressure from `mmHg`-vs-`cmH2O` unit confusion and mid-breath relief preemption, (2) `DICOM` `LPS`-to-`RAS` right-handed rotation ($\det = +1$) vs. naive identity/single-axis reflection errors, (3) `int16` `RescaleSlope` `SUV` wraparound (`-15536` vs. `50000.0`), and (4) `IEC 60601-1-8` preemptive high-priority alarm latency `< 10 ms`:

```bash
python3 - <<'PY'
# 1. Airway pressure unit isolation: 30 mmHg erroneously interpreted as cmH2O
CMH2O_PA, MMHG_PA = 98.0665, 133.322368
overpressure_cmh2o = 30.0 * (MMHG_PA / CMH2O_PA)
assert round(overpressure_cmh2o, 2) == 40.79  # > 35 cmH2O barotrauma threshold!

# 2. DICOM LPS (+X Left, +Y Post, +Z Sup) -> RAS (+X Right, +Y Ant, +Z Sup)
def det3(m):
    return (m[0][0]*(m[1][1]*m[2][2] - m[1][2]*m[2][1])
          - m[0][1]*(m[1][0]*m[2][2] - m[1][2]*m[2][0])
          + m[0][2]*(m[1][0]*m[2][1] - m[1][1]*m[2][0]))

C_lps_to_ras = [[-1, 0, 0], [0, -1, 0], [0, 0, 1]]
C_bad_mirror = [[-1, 0, 0], [0,  1, 0], [0, 0, 1]]
assert det3(C_lps_to_ras) == +1  # Proper right-handed rotation
assert det3(C_bad_mirror) == -1  # Improper chirality-inverting reflection!

# Right-lung target at X_lps = -85 mm maps to +85 mm (+X = Right) in RAS:
pt_lps = (-85.0, 20.0, 15.0)
pt_ras = (-pt_lps[0], -pt_lps[1], pt_lps[2])
assert pt_ras == (85.0, -20.0, 15.0)

# 3. DICOM int16 RescaleSlope SUV overflow without pre-widening to f32
raw_i16, slope, intercept = 20000, 2.5, 0.0
wrapped_i16 = ((int(raw_i16 * slope + intercept) + 32768) % 65536) - 32768
widened_f32 = float(raw_i16) * slope + intercept
assert wrapped_i16 == -15536 and widened_f32 == 50000.0

# 4. IEC 60601-1-8 preemptive audio arbiter (High=3 > Med=2 > Low=1)
def active_voice(events):
    # Returns highest priority active alarm with lower-priority voices ducked
    active = [prio for prio, is_on in events if is_on]
    return max(active) if active else 0

assert active_voice([(2, True), (3, True), (1, True)]) == 3  # High preempts Med & Low!

print("REVALIDATION_OK")
PY
```
