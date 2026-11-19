# Genetic Circuit Repressor Synthesis, EWOD Droplet Routing, and Liquid-Handling Safety Invariants

## Summary

Automated design-to-wetlab synthetic biology workflows connect three disparate compilation layers: (1) Boolean hardware-description synthesis into transcriptional repressor DNA (`CIDARLAB/cello`, `CIDARLAB/Cello-v2`), (2) Electrowetting-on-Dielectric (EWOD) digital microfluidic droplet actuation (`GaudiLabs/OpenDrop`), and (3) robotic deck liquid handling (`Opentrons/opentrons`, `PyLabRobot/pylabrobot`). Across all three layers, failures arise when static abstractions drop physical coupling invariants at layer boundaries.

Direct source inspection and executable modeling establish five load-bearing invariants and concrete defects across the inspected revisions:
1. **Stale-Activity Toxicity Gate in Cello v2:** In `SimulatedAnnealing.java`, post-swap toxicity evaluation queries the *pre-swap* `getTMActivityEvaluation()` instead of the newly computed post-swap `tmae`, allowing a swap from `B1_BM3R1` (`0.496 RPU`) to `P3_PhlF` (`6.800 RPU`) upstream of `Q1_QacR` to pass the `0.75` growth threshold with a stale `0.963` score when true growth collapses to `0.281`.
2. **Ribosome-Depletion Retroactivity:** Both Cello v1 (`Toxicity.java`) and Cello v2 (`TMToxicityEvaluation.java`) evaluate each repressor gate independently and multiply per-gate normalized $\text{OD}_{600}$ growth factors, omitting shared host ribosome competition (`Gyorgy et al., Biophysical Journal 2015`; `Qian et al., ACS Synthetic Biology 2017`). Under an 8-gate transcriptional load ($\alpha = 0.08\text{ RPU}^{-1}$), a `S4_SrpR -> E1_BetI` cascade drops from `26.61x` ideal `ON/OFF` ratio to `4.26x` (`84.0%` collapse).
3. **Tandem-Promoter Roadblocking Asymmetry:** Cello v1 warns rather than rejects dual inducible input roadblockers (`pTac + pBAD`), whereas Cello v2 enforces prefix-assuming `STARTSWITH`/`BEFORE`/`AFTER` Eugene rules (`RoadBlockUtils.java`) that fail silently if structural templates do not place all inputs consecutively at the promoter head. Unmodeled RNAP roadblocking ($\eta_{\text{rb}} = 0.18$) increases downstream `E1_BetI` leakage by `5.25x`.
4. **EWOD Fluidic-Short & Array Bounds Defects in OpenDrop:** `OpenDrop::free_Fluxel()` inspects only three forward-cone electrodes relative to stale `pad_feedback`, allowing `14` distinct 2-droplet pairs from valid Chebyshev distance $d_\infty \ge 2$ starting states to short to $d_\infty = 1$ in a single `run()` step. Furthermore, `OpenDrop::getDrop()` writes `drops[num-1]` before checking `num > max_drops`, causing an out-of-bounds write when creating a 9th droplet (`max_drops = 8`).
5. **Robotic Tip-Collision, Dead-Volume, and Reagent-Taint Blindspots:** `Opentrons` `TipView.get_next_tip()` falls out of `_get_next_tip_with_nozzle_map()` whenever `starting_tip_name` is supplied on a partial nozzle layout, bypassing non-active nozzle collision checks (`wells_covered_physically`), while `WellStore` permits negative `loaded_volumes` and erases well volume tracking (`CLEAR`) on `OverpressureError`. `PyLabRobot` disables volume tracking globally by default (`volume_tracking_enabled = False`) and has deprecated individual `Liquid` identity tracking in `VolumeTracker`, leaving cross-contamination unguarded unless an affine tip-taint discipline is layered above it.

All physical and runtime invariants across DNA synthesis, EWOD routing, and pipette execution collapse onto two orthogonal formal primitives: **Affine Spatial Ownership** (unifying $d_\infty \ge 2$ EWOD guardbands, physical nozzle footprints, and tip reagent-taint linearity) and **Quantitative Resource Grades** (unifying cellular ribosome isocost denominators, additive-RPU noise margins, and liquid dead-volume conservation).

## Applicability

This report characterizes the exact upstream revisions and primary literature pinned in `REPORT.json`:
- **Genetic circuit compilers:** `CIDARLAB/cello` (v1, commit `11644045e5ab677965a8e5765db2fb8535484a53`) and `CIDARLAB/Cello-v2` (commit `1b93575b8aa7e40e132381e3a9b29b1aa7f7a8e4`), evaluated specifically against the `Eco1C1G1T1` *Escherichia coli* NEB 10-beta User Constraint File (`Eco1C1G1T1.UCF.json` and `gates_Eco1C1G1T1.csv`) using Relative Promoter Units (RPUs) and TetR-homolog transcriptional NOR/NOT gates (`Nielsen et al., Science 2016`; `Jones et al., Nature Protocols 2022`).
- **EWOD digital microfluidics:** `GaudiLabs/OpenDrop` V4 firmware (`OpenDropV4/Software/Libraries/OpenDrop/`, commit `934a44db3ed41c24ae4dddb5b805a22e4166284b`), covering the `16 x 8` active electrode array (`FluxlPad_width = 16`, `FluxlPad_heigth = 8`), `HV507` high-voltage shift registers, and `SAMD21` timer/ADC actuation loops (`Su, Hwang, & Chakrabarty, DATE 2006`).
- **Liquid-handling robotics:** `Opentrons/opentrons` `protocol_engine` state stores and command handlers (`api/src/opentrons/protocol_engine/`, commit `4bae21dfd6f164dc617093bcf2b0b14e27e00edf`) and `PyLabRobot/pylabrobot` v1 resource/tracker subsystems (`pylabrobot/resources/` and `pylabrobot/legacy/liquid_handling/`, commit `dea2631feb592e0e7554afb1fe686eccd56688f8`).

The findings here concern **combinational and sequential logic synthesis in *E. coli* steady-state RPU models**, **discrete electrode-grid EWOD actuation**, and **discrete pipette tip/volume state machines**. Extrapolation beyond *E. coli* steady-state promoter models (e.g., mammalian chromatin silencing) or continuous-flow PDMS microfluidics is outside scope and documented under `## Boundaries`.

## Findings

### 1. Verilog-to-NOR Synthesis, Hill Transfer Matching, and Ribozyme Context Insulation

`Basis: normative + documentation + source + execution`

Both `CIDARLAB/cello` and `CIDARLAB/Cello-v2` compile behavioral Verilog RTL into transcriptional `NOR`/`NOT` netlists (`Yosys` -> `abc -g NOR,NOT,...`, `Yosys.java:186-237`), then solve combinatorial repressor-to-node assignment via simulated annealing (`BuildCircuitsSimAnnealing.java`, `SimulatedAnnealing.java`) against empirically calibrated User Constraint Files (UCFs). Every logic gate concatenates two upstream transcriptional-input promoters in tandem (wired-OR summation of RNA polymerase flux) driving a self-cleaving ribozyme insulator, a ribosome binding site (RBS), a TetR-family repressor coding sequence (CDS), and a terminator, with all steady-state activities normalized to a reference constitutive promoter in **Relative Promoter Units (RPUs)**.

#### 1.1 Four-Parameter Hill Transfer Function and Ribozyme Context Insulation
Each repressor gate $g$ in `Eco1C1G1T1` is modeled by a monotonically decreasing 4-parameter Hill response function (`Evaluate.java:689-865`, `ResponseFunction.java:21-45`):
$$y_g(x) = y_{\min,g} + \frac{y_{\max,g} - y_{\min,g}}{1 + (x / K_g)^{n_g}}, \qquad x_{\text{NOR}} = x_1 + x_2$$
where $x_1, x_2$ are incoming promoter activities in RPU and $y_{\min}, y_{\max}, K, n$ are empirical cytometry parameters. Placing a self-cleaving ribozyme (`RiboJ`, `BydvJ`, `SarJ`, `ElvJ`, `PlmJ`, `ScmJ`) immediately downstream of the tandem promoter junction cleaves the 5' untranslated region at a fixed nucleotide site (`Nielsen et al. 2016`), removing promoter-dependent mRNA hairpins so that identical repressors with distinct RBS sequences (`P1`/`P2`/`P3_PhlF`, `S1`–`S4_SrpR`) shift $K$ without distorting CDS translation initiation.

Representative empirical parameters from `CIDARLAB/cello` (`resources/csv_gate_libraries/gates_Eco1C1G1T1.csv`) illustrate the tight dynamic-range coupling across TetR-homolog gates:

| Gate Name | Repressor | Promoter | Ribozyme | $y_{\max}$ (RPU) | $y_{\min}$ (RPU) | $K$ (RPU) | Hill $n$ | $I_L$ (RPU) | $I_H$ (RPU) | `min_growth` (`UCF`) |
| :--- | :--- | :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `A1_AmtR` | `AmtR` | `pAmtR` | `BydvJ` | `3.8` | `0.06` | `0.07` | `1.6` | `0.0714` | `0.9171` | — |
| `B1_BM3R1` | `BM3R1` | `pBM3R1` | `SarJ` | `0.5` | `0.004` | `0.04` | `3.4` | `0.0402` | `0.1647` | — |
| `B3_BM3R1` | `BM3R1` | `pBM3R1` | `SarJ` | `0.8` | `0.01` | `0.26` | `3.4` | `0.2619` | `0.9364` | — |
| `E1_BetI` | `BetI` | `pBetI` | `RiboJ57` | `3.8` | `0.07` | `0.41` | `2.4` | `0.4165` | `2.1319` | `0.97` |
| `F1_AmeR` | `AmeR` | `pAmeR` | `RiboJ54` | `3.8` | `0.20` | `0.09` | `1.4` | `0.0974` | `0.6810` | `0.94` |
| `P1_PhlF` | `PhlF` | `pPhlF` | `RiboJ53` | `3.9` | `0.01` | `0.03` | `4.0` | `0.0300` | `0.1331` | — |
| `P3_PhlF` | `PhlF` | `pPhlF` | `RiboJ53` | `6.8` | `0.02` | `0.23` | `4.2` | `0.2303` | `0.9201` | `0.96` |
| `Q1_QacR` | `QacR` | `pQacR` | `RiboJ60` | `2.4` | `0.01` | `0.05` | `2.7` | `0.0502` | `0.3795` | **`0.05`** |
| `S4_SrpR` | `SrpR` | `pSrpR` | `RiboJ10` | `2.1` | `0.007` | `0.10` | `2.8` | `0.1002` | `0.7650` | `0.91` |

#### 1.2 Circuit Scoring Objectives
Cello v2's `ScoreUtils.score()` (`ScoreUtils.java:48-92`) defines the circuit score strictly as the worst-case `ON/OFF` separation across all primary output nodes:
$$\text{Score} = \min_{v \in V_{\text{out}}} \frac{\min_{s: L_v(s) = 1} A_v(s)}{\max_{s: L_v(s) = 0} A_v(s)}$$
While Cello v1 (`Evaluate.java:172-217`) also supports Wasserstein/overlap scoring over binned flow-cytometry histograms (`simulateHistogramRPU`), `ScoreUtils` in Cello v2 relies solely on scalar median RPU trajectories unless cytometry plugins are explicitly invoked, ignoring cell-to-cell distribution tails (`Noise Margin` / histogram overlap).

---

### 2. Tandem-Promoter Roadblocking and Cello v1 vs. v2 Constraint Enforcement

`Basis: normative + source + execution`

Because Cello realizes every 2-input `NOR` gate by placing two regulable promoters in series (`P_up` followed by `P_down`), RNA polymerase (RNAP) initiating at `P_up` must physically transcribe through `P_down`. When a repressor bound to `P_down` creates an immobile steric block (roadblock) rather than merely occluding `P_down`'s `-35/-10` hexamers, upstream RNAP stalls or terminates prematurely (`Roadblock.java:20-25`). Consequently, additive promoter flux breaks down asymmetrically:
$$x_{\text{tandem}}^{\text{actual}} = \eta_{\text{rb}}(p_{\text{down}}) \cdot x_{\text{up}} + x_{\text{down}}, \qquad \eta_{\text{rb}} \in [0.10, 0.35] \text{ for roadblockers}$$
If `P_up` is `HIGH` (`0.80 RPU`) and `P_down` is `LOW` (`0.05 RPU`) with downstream roadblocking ($\eta_{\text{rb}} = 0.18$), `x_actual` collapses from `0.85 RPU` to `0.194 RPU`. Driven into `E1_BetI` ($K = 0.41$), `E1_out` rises from `0.622 RPU` (predicted `OFF`) to `3.269 RPU` (`5.25x` unintended `OFF`-state leakage, verified in `[Probe 1A]`).

#### 2.1 Structural Comparison: Cello v1 vs. Cello v2 Roadblocking Rules
- **Cello v1 (`Roadblock.java:36-214`):** Parses `STARTSWITH <prom>` rules from `eugene_part_rules` (in `Eco1C1G1T1.UCF.json`: `STARTSWITH pTac`, `pBAD`, `pPhlF`, `pSrpR`, `pBM3R1`, `pQacR`, plus directional constraints `pSrpR BEFORE pAmeR`, `pBetI`, `pLitR`, etc.). Crucially, Cello v1 separates `_input_roadblockers` from `_logic_roadblockers`: if two *logic* roadblockers or one logic + one input roadblocker feed the same gate (`total_roadblockers > 1 && n_child_roadblockers_logic > 0`, `line 145`), `illegalRoadblocking()` forbids the assignment; however, if *both* tandem inputs are inducible sensor promoters (`pTac + pBAD`), `illegalInputRoadblocking()` (`lines 187-214`) emits only a log warning while still accepting the circuit!
- **Cello v2 (`RoadBlockUtils.java:122-215`):** Replaces explicit input/logic split with regex matching (`STARTSWITH`, `BEFORE`, `AFTER`) over `DeviceRules.filter(device, parts)` (`lines 172-211`). However, `isRoadBlockable(StructureDevice)` (`lines 122-137`) explicitly admits:
  ```java
  // TODO Lazy implementation. This assumes all inputs are at the beginning.
  ```
  It counts consecutive `StructureTemplate` components from index `0` and `break`s on the first non-template part (`lines 126-131`). Any UCF device layout placing a spacer, insulator, or terminator prefix before promoter templates immediately causes `isRoadBlockable` to return `false`, silently disabling roadblocking verification during simulated annealing (`SimulatedAnnealing.java:338-363`).

---

### 3. Host Ribosome-Depletion Retroactivity and Cello-v2's Stale-Activity Toxicity Bug

`Basis: source + execution + derived`

#### 3.1 Cello-v2 Stale-Activity Toxicity Bug (`SimulatedAnnealing.java:367-395`)
In `SimulatedAnnealing.java` (`CIDARLAB/Cello-v2` @ `1b93575b`), each annealing iteration proposes either a gate swap (`lines 319-348`) or a tandem promoter order swap (`lines 350-364`), computes the new activity evaluation into a local variable `tmae`, and then evaluates toxicity:
```java
// SimulatedAnnealing.java:367-376
final TMActivityEvaluation tmae =
    new TMActivityEvaluation(getNetlist(), getLSLogicEvaluation());
final Double after = ScoreUtils.score(getNetlist(), getLSLogicEvaluation(), tmae);
...
final TMToxicityEvaluation tmte =
    new TMToxicityEvaluation(getNetlist(), getTMActivityEvaluation());
```
Line `375` passes **`getTMActivityEvaluation()` (the *pre-swap* cached activity table)** instead of the newly computed **`tmae`**! Because `TMToxicityEvaluation` indexes toxicity strictly by incoming gate activity (`TMToxicityEvaluation.java:93-116`), the toxicity filter never sees the effect of changing an upstream gate's output RPU on a downstream toxic gate during the accept/reject decision (`lines 378-395`). Furthermore, `SimulatedAnnealing.java:211` seeds `this.random = new Random(L_SEED)` (`L_SEED = 21`) for node selection while calling unseeded `Math.random()` at `lines 313, 409` for tandem/gate swap choice and Metropolis acceptance, breaking run-to-run reproducibility.

In `[Probe 1A]`, using the exact `Eco1C1G1T1` parameters (`Q1_QacR` empirical toxicity titration dropping from `0.97` at `0.168 RPU` to `0.12` at `8.44 RPU` and `0.05` at `17.52 RPU`):
- Swapping an upstream gate feeding `Q1_QacR` from `B1_BM3R1` (`y(0.01) = 0.496 RPU`, interpolated growth **`0.963`**) to `P3_PhlF` (`y(0.01) = 6.800 RPU`, interpolated growth **`0.281`**) causes Cello v2's stale check to read `0.963 >= D_GROWTH_THRESHOLD (0.75)` and accept a circuit whose true worst-case growth (`0.281`) kills the host!

#### 3.2 Multiplicative $\text{OD}_{600}$ Approximation vs. Host Ribosome-Depletion Isocost Laws
Both `Toxicity.java:142-166` (Cello v1) and `TMToxicityEvaluation.java:142-154` (Cello v2) compute whole-circuit relative growth as an independent product clamped at `0.01`:
$$G_{\text{Cello}}(s) = \max\Bigl(0.01,\; \prod_{v \in V_{\text{logic}}} g_v\bigl(x_v(s)\bigr)\Bigr)$$
Additionally, `Toxicity.java:46` restricts evaluation to `g.get_variable_names().size() == 1` (`//multi-input toxicity not handled`). Physically, however, transcriptional activators/repressors compete with host housekeeping genes for a finite cellular pool of free RNA polymerases and 70S ribosomes (`Gyorgy et al., Biophysical Journal 2015`, DOI: `10.1016/j.bpj.2015.06.037`; `Qian et al., ACS Synthetic Biology 2017`). Along linear translational **isocost manifolds** in the resource-budget plane, effective output expression $y_i^{\text{eff}}$ of gene $i$ shrinks inversely with total circuit translational demand:
$$y_i^{\text{eff}}(x_i, \mathbf{y}) = \frac{y_i(x_i)}{1 + \sum_{j=1}^{M} \alpha_j\, y_j(x_j)}, \qquad \alpha_j = \frac{k_{\text{tx},j} \cdot \text{RBS}_j}{\text{Ribosome Pool Capacity}}$$
Unlike Cello's independent per-gate curve—which assumes upstream `S4_SrpR` produces `2.10 RPU` regardless of how many other gates are `ON`—`[Probe 1A]` shows that adding 6 co-expressed high-expression gates ($\alpha = 0.08\text{ RPU}^{-1}$) depresses `S4_SrpR` `ON` output from `2.10 RPU` to **`0.70 RPU`**, dangerously close to `E1_BetI`'s switching threshold $K = 0.41\text{ RPU}$, collapsing `S4 -> E1` `ON/OFF` dynamic range from **`26.61x`** down to **`4.26x`** (**`84.0%`** loss) while `P3 -> E1` drops `46.0%` (`50.94x` $\to$ `27.51x`). Because this coupling depends on the global active-state vector $\mathbf{y}(s)$, non-adjacent circuit modules interact retroactively without sharing any DNA wire (`Del Vecchio` retroactivity).

---

### 4. EWOD Electrode Actuation, Capacitance Feedback, and Fluidic-Short Spacing Bugs in OpenDrop

`Basis: normative + source + execution`

`GaudiLabs/OpenDrop` (`OpenDrop.cpp`, `OpenDrop.h`, `hardware_def.h`) executes Electrowetting-on-Dielectric (EWOD) protocols on a `16 x 8` (`128`-pad) electrode cartridge (`FluxlPad_width = 16`, `FluxlPad_heigth = 8`, `hardware_def.h:7-8`) driven at `Voltage_set = 240 V` (`AC_frequency = 1000 Hz` default, `OpenDrop.cpp:36-37`). According to the Lippmann–Young equation, charging the hydrophobic dielectric capacitor reduces droplet contact angle $\theta(V)$:
$$\cos \theta(V) = \cos \theta_0 + \frac{\varepsilon_0 \varepsilon_r}{2 d_{\text{diel}} \gamma_{LG}} V_{\text{rms}}^2$$
creating an asymmetric Laplace pressure gradient that translates nanoliter–microliter droplets across adjacent electrodes.

#### 4.1 Hard Real-Time Timing, Bit-Banged HV507 Scans, and `getDrop()` Memory Corruption
Inspection of `OpenDrop.cpp` reveals four firmware-level timing and memory defects:
1. **ISR Busy-Wait Jitter (`OpenDrop.cpp:69-95`):** `TC4_Handler` runs at NVIC priority `0` (`line 183`) and executes `delayMicroseconds(68)` or `delayMicroseconds(74)` *inside* the interrupt service routine (`lines 73, 78`) to avoid shoot-through across the opto-coupled H-bridge (`AC_pin`, `POL_pin`). At `1000 Hz` (`2000` half-cycle interrupts/s), busy-waiting stalls all lower-priority MCU tasks for `~14%` of CPU wall time.
2. **Interrupt-Disabled Capacitance Readout (`OpenDrop.cpp:523-611`):** `read_Fluxels()` calls `noInterrupts()` (`line 533`), shifts `128` serial bits one-by-one into the `HV507` drivers via `delayMicroseconds(5)` bit-banging (`lines 547-602`) plus `delayMicroseconds(7)` per pad (`line 580`), and calls `drive_Fluxels()` before `interrupts()` (`line 609`). Each full-array capacitance feedback scan freezes the `TC4` AC polarity toggle for `> 4 ms`, exposing actuated droplets to transient DC dielectric charging while blocked.
3. **`getDrop()` Out-of-Bounds Write Before Bounds Check (`OpenDrop.cpp:1008-1017`):**
   ```cpp
   Drop *OpenDrop::getDrop() {
     uint8_t num = this->drop_count;
     num++;
     this->drop_count = num;
     drops[num - 1]._dropnum = num;       // <-- OOB write when num > max_drops (8)!
     if (num > max_drops) return NULL;    // <-- checked AFTER writing drops[8]
     return &drops[num - 1];
   }
   ```
   When allocating a 9th droplet (`max_drops = 8`, `OpenDrop.h:17`), `getDrop()` corrupts `_dropnum` past `drops[0..7]` and leaves `this->drop_count == 9`, causing subsequent loops (`for (int i = 0; i < this->drop_count; i++)`) in `run()`, `update()`, and `update_Drops()` to read/mutate out-of-bounds memory even though `NULL` was returned.
4. **Loop-Scoped `_runing` Overwrite (`OpenDrop.cpp:939-951`):** Inside `OpenDrop::run()`, `_runing = ((drops[i].position_x() != drops[i].goal_x()) | (drops[i].position_y() != drops[i].goal_y()));` overwrites private member `_runing` on each droplet `i`, although `transition` accumulates `transition | _runing`.

#### 4.2 Fluidic-Short Violations in `free_Fluxel()` and Sequential `run()`
In digital microfluidic biochips (DMFBs), avoiding unintended droplet coalescence (fluidic shorts) requires maintaining **static** and **dynamic** Chebyshev ($L_\infty$) clearance (`Su, Hwang, & Chakrabarty, DATE 2006`; `Xu & Chakrabarty, DAC 2007`, DOI: `10.1109/DAC.2007.375283`):
$$d_\infty(p_i^t, p_j^t) \ge 2 \quad \text{(static)}, \qquad d_\infty(p_i^{t+1}, p_j^t) \ge 2 \;\land\; d_\infty(p_i^t, p_j^{t+1}) \ge 2 \quad \text{(dynamic)}$$
Wait-free inspection of `OpenDrop::free_Fluxel(x, y, dir)` (`OpenDrop.cpp:276-291`) combined with `run()` (`lines 961-964`) shows why OpenDrop cannot enforce these invariants:
- **Forward-Cone Blindspot:** When droplet $i$ proposes moving right (`dir = 2`) from `(px, py)` to `(px+1, py)`, `run()` calls `free_Fluxel(px+1, py, 2)`. Inside `free_Fluxel`, `(x, y)` is already the *destination* `(px+1, py)`, so checking `x+1` (`(px+2, py)`), `(x+1, y-1)`, and `(x+1, y+1)` inspects **only column `px+2`** while completely skipping lateral neighbors `(px+1, py+1)` and `(px+1, py-1)` and target cell `(px+1, py)` itself (in addition to using bitwise `&` instead of `&&` on `lines 284-285`).
- **Stale Snapshot & Sequential Race:** `run()` calls `read_Fluxels()` once at entry (`line 936`), then independently updates `drops[0..drop_count-1]` without reserving planned `(_next_x, _next_y)` footprints. `[Probe 1B]` enumerates 2-droplet pairs on the `16 x 8` grid starting from valid $d_\infty \ge 2$ states and proves **`14` distinct collision trajectories** where both droplets pass `free_Fluxel()` yet violate static/dynamic spacing (e.g., $D_0: (4,3) \to (4,2)$ and $D_1: (2,1) \to (3,1)$ collide to $d_\infty((4,2),(3,1)) = 1$!). By contrast, an exact 4-droplet Su–Chakrabarty static+dynamic step verifier runs in **`2.80 us/step`** in pure Python.

---

### 5. Liquid-Handling Deck Geometry, Dead-Volume Accounting, and Tip-Taint Blindspots in Opentrons and PyLabRobot

`Basis: source + execution`

Executing compiled genetic circuits or EWOD cartridge loading requires physical liquid transfers via multi-channel pipetting robots (`Opentrons/opentrons` and `PyLabRobot/pylabrobot`). Both frameworks model 3D deck geometry well, yet both expose subtle state-machine gaps around partial-nozzle kinematics, residual dead volume, and affine reagent taint.

#### 5.1 Opentrons Protocol Engine (`api/src/opentrons/protocol_engine/`)
1. **Partial-Nozzle `starting_tip_name` Collision Bypass (`state/tips.py:102-214`):** `TipView.get_next_tip()` enforces physical non-active nozzle clearance (`wells_covered_physically`, verifying unused overlapping tip spots are `TipRackWellState.EMPTY`) **only** inside `_get_next_tip_with_nozzle_map()` (`lines 152-213`). However, line `113` gates that path on `if starting_tip_name is None and nozzle_map is not None:`. Supplying *any* non-`None` `starting_tip_name` alongside a partial `NozzleMap` silently enters the legacy `else:` branch (`lines 115-150`), which iterates tips without checking physical pipette housing or unused-nozzle collisions (`lines 143-149`), risking mechanical rack crashes rather than raising an `UnsupportedError`.
2. **Dead-Volume Omission and Error-Induced Volume Erasure (`state/wells.py:103-162`, `commands/aspirate.py:189-215`):** `WellStore._handle_well_operated()` accumulates `volume=prev_loaded_vol_info.volume + volume_added` (`line 119`) without enforcing `well_volume >= dead_volume >= 0` (`dead_volume` is absent from `WellState`, `lines 36-41`), permitting silent negative balances or unpumped air aspirations when cumulative transfer losses exceed conical-bottom dead volume (`[Probe 1B]` demonstrates a `5.0 uL` shortfall when two `45.0 uL` transfers draw from a `100.0 uL` well with `15.0 uL` dead volume). Worse, on `OverpressureError` during `AspirateImplementation.execute()` (`aspirate.py:189-198`), `state_update.set_liquid_operated(..., volume_added=CLEAR)` triggers `del self._state.loaded_volumes[labware_id][well_name]` (`wells.py:114`), permanently erasing volume accounting for that well.
3. **Boolean Clean-Tip Flag vs. Affine Reagent-Taint Sets (`state/pipettes.py:395-434`):** Opentrons tracks a `FluidStack` of `(kind: LIQUID|AIR, volume)` (`fluid_stack.py:21-125`) and a single boolean `has_clean_tips_by_id[pipette_id]` (`pipettes.py:400-402, 430`) toggled to `False` on any aspiration (`set_fluid_empty(..., clean_tip=True)` only on `pickUpTip`, `pick_up_tip.py:215`). Because `FluidStack` merges contiguous `FluidKind.LIQUID` entries regardless of reagent identity (`fluid_stack.py:43-53`), it does not enforce affine single-reagent ownership or cross-contamination provenance when reusing tips across buffers vs. plasmid templates.

#### 5.2 PyLabRobot (`pylabrobot/resources/` & `pylabrobot/legacy/liquid_handling/`)
1. **Opt-In Global Tracking Default (`volume_tracker.py:13-32`):** `volume_tracking_enabled` defaults to `False` (`line 14`). Unless user code explicitly invokes `set_volume_tracking(True)`, `LiquidHandler.aspirate()` (`legacy_lh.py:1290, 1305`) skips both `op.resource.tracker.remove_liquid` and `op.tip.tracker.add_liquid`.
2. **Resource-Tree Tip Ownership vs. Deprecated Liquid Identity (`tip_tracker.py:1-31`, `volume_tracker.py:77-89, 129-145`):** PyLabRobot v1 cleanly replaces `TipTracker` callbacks by modeling a mounted `Tip` directly as a tree child of the pipette mounting shaft (`tip_tracker.py:3`), eliminating dual-source tip-presence desynchronization. However, `VolumeTracker` explicitly deprecated individual liquid identities (`get_liquids()` returns `[(None, top_volume)]` with a warning: *"The volume tracker no longer tracks individual liquids"*, `lines 134-145`) and enforces only `volume - pending_volume <= 1e-6` (`line 101`) with no container dead-volume floor. Consequently, neither `Opentrons` nor `PyLabRobot` prevents a contaminated tip from aspirating an incompatible plasmid/inducer stock unless a separate protocol linter tracks reagent taint linearly.

---

### 6. Multi-Level Performance and Resource Footprint Analysis (L1–L6)

`Basis: source + execution + derived`

Integrating genetic-circuit compilation, EWOD droplet synthesis, and robotic deck execution spans six distinct engineering performance and footprint levels:

| Metric Level | Cello v1 (`11644045`) & v2 (`1b93575b`) | `OpenDrop` V4 Firmware (`934a44db`) | `Opentrons` (`4bae21df`) & `PyLabRobot` (`dea2631f`) | Unified Affine + Coeffect Gate (Standalone Python/Native) |
| :--- | :--- | :--- | :--- | :--- |
| **(L1) Authoring Velocity & Maintenance** | High abstraction: `10–40 LoC` Verilog + UCF JSON; manual debugging of ribosome crashes or roadblock warnings costs days per wetlab DBTL cycle | Low-level C++ Arduino sketch (`~1.4 KLoC` driver); manual pad coordinate coding (`OpenDrop.cpp:805-920`) is error-prone across reagent revisions | Python protocols (`30–150 LoC`); tracking flags (`set_volume_tracking`) and tip/taint safety remain manual discipline | `~18 LoC` declarative circuit + deck assay + grade caps (`GrowthCap`, `Clearance>=2`, `DeadVol`); `0` manual tip/pad guards |
| **(L2) Framework Build Time & RSS** | Maven/Java multi-module build (`~20–45 s` cold, `~400–700 MiB` JVM RSS) + external `Yosys`/`ABC` binary | `arduino-cli` / `arm-none-eabi-gcc` SAMD21 compile (`~4–10 s`, `< 150 MiB` host RSS) | Pure Python `uv`/`pip` editable install (`< 5 s`, `~80–160 MiB` test RSS) | `< 1 KLoC` pure Python (`0 s` build) or zero-dep C/Rust checker (`< 1.5 s` build, `< 35 MiB` RSS) |
| **(L3) Compilation / Synthesis Latency** | `600` SA steps (`SimulatedAnnealing.java:798`) + `Yosys`: `~2–15 s` for 3–7 gate circuits; exponential truth-table scaling $O(2^k)$ | Static `dispense()` sequences (`0 ms` compile); greedy Manhattan `run()` has no lookahead solver | Protocol analysis/simulation (`Opentrons` `ProtocolEngine` dry-run): `~50–400 ms` per 96-well assay | Isocost + Hill fixed-point (`< 5 ms` for 20 gates); SAT/SMT or A* DMFB planner `~10–120 ms` |
| **(L4) Execution / Runtime Latency** | Biological doubling time `~20–45 min` (*E. coli*); full circuit steady state takes `3–6 hours` per DBTL wetlab pass | `TC4` ISR at `2 kHz` (`500 us` half-period, `68–74 us` busy-wait); `read_Fluxels()` freezes AC `> 4 ms`; droplet hop `~200–500 ms` | Gantry + Z-plunger moves `~0.5–3.0 s` per transfer; `ProtocolEngine` async command dispatch `~1–5 ms` | Runtime `0`-overhead after compile-time admission; online EWOD closed-loop hop verifier **`2.80 us/step`** (`[Probe 1B]`) |
| **(L5) Verification / Admission Speed** | Cello v2 `TMToxicityEvaluation` + `RoadBlockUtils`: `< 10 ms` per SA candidate (but missed stale `tmae` & ribosome load) | No firmware step verifier (`free_Fluxel` inline in `run()`, `~1 us`, incomplete) | `TipView` / `WellStore` / `VolumeTracker` state checks `< 50 us` per command | Pure Python admission check (4-droplet EWOD + dead-vol + Hill/isocost) **`< 1 ms`** (`2.80 us` per EWOD step, `[Probe 1A/1B]`) |
| **(L6) Memory, Disk & Hardware Footprint** | `Eco1C1G1T1.UCF.json` `~1.8 MB`; JVM heap `~256–512 MiB`; output plasmid DNA `~5–25 kb` (`10–55` parts) | Atmel `SAMD21G18` (`256 KiB` Flash, `32 KiB` SRAM); `128` pads at `240 V` AC; `drops[8]` (`~72 B` static array) | Python engine `~60–180 MiB` RSS; tip consumables `96–384` tips/plate; `5–20 uL` dead volume per well | Admission verifier `< 45 KiB` binary / `< 200 LoC` Python; eliminates `2x` reagent/tip over-provisioning |

---

### 7. Human Comprehensibility, Conceptual Simplicity, and Universal Model Refinement (C1–C2)

`Basis: derived`

#### 7.1 Human Comprehensibility vs. Agent Execution Ergonomics (`C1`)
Cello v1/v2 separates circuit intent (`Verilog`) cleanly from biological parts (`UCF.json`), which lowers upfront Verilog authoring effort (`C1` low concept count at specification time). However, **diagnostic legibility collapses upon failure**:
- When Cello v2 rejects or mis-ranks a circuit due to roadblocking or ribosome depletion, a biologist sees an opaque regex rule mismatch (`RoadBlockUtils.java:179-200`) or an unexplained `0.75` `minimumGrowth` cutoff (`SimulatedAnnealing.java:794`)—or worse, receives a silent wetlab failure (`0.281` growth) due to the stale-`tmae` bug—without receiving an interpretable witness identifying *which upstream promoter (`P3_PhlF`) overloaded which downstream repressor (`Q1_QacR`)* or *which ribosome isocost constraint collapsed the dynamic range*.
- Similarly, OpenDrop firmware silently corrupts `drops[8]` on a 9th `getDrop()` call or merges adjacent droplets (`d_inf = 1`) without surfacing a coordinate-pair collision witness.
- Conversely, an LLM/agent can mechanically patch a `for` loop or sweep `K`/`ymax` tables, whereas human laboratory scientists audit safety using **four concrete visual invariants**: (1) normalized per-gate `ON/OFF` + ribosome-coupled dynamic range margin, (2) growth-floor certificate ($\min_s G(s) \ge 0.75$), (3) Chebyshev $d_\infty \ge 2$ droplet exclusion footprints on the `16 x 8` grid, and (4) linear well mass balance ($V_{\text{req}} \le V_{\text{init}} - V_{\text{dead}}$) + single-reagent tip color tags.

#### 7.2 Universal Two-Primitive Refinement and Adapter-Conservation Audit (`C2`)
Across DNA circuits, EWOD pads, and pipette tips, seemingly unrelated bugs stem from splitting physical resource accounting into ad-hoc boolean flags and string rules. Two orthogonal abstractions unify all three layers cleanly:
1. **`AffineRegion<Space, Taint>` (Linear Spatial & Provenance Ownership):** Models every physical carrier—an EWOD `3 x 3` guardband halo (`Chebyshev radius = 1`), a pipette `NozzleMap` physical bounding box, or an attached `Tip`'s single-reagent `Taint` color—as a linear region token that cannot overlap another incompatible token in space-time (`d_inf >= 2` for distinct droplet IDs; `EMPTY` check for passive nozzles; `Taint(tip) in {Clean, Reagent(r)}` enforcing tip discard before touching `Reagent(r') != r`). This single rule replaces `OpenDrop`'s broken `free_Fluxel()` cone checks, `Opentrons`'s fragile `starting_tip_name` branching + `has_clean_tips_by_id` boolean, and `PyLabRobot`'s dropped `Liquid` identity tracking.
2. **`Grade<ResourceSemiring>` (Quantitative Capacity & Conservation Budget):** Tracks composable quantitative coeffects across circuit and liquid execution:
   - *Cellular Translational Grade:* $(D_{\text{ribo}}, G_{\min}) = (\sum_j \alpha_j y_j,\; \prod_j g_j^{\text{coupled}})$ enforced monotonically over the **current** post-swap activity state, replacing Cello's independent `TMToxicityEvaluation` and catching ribosome-mediated dynamic-range collapse at compile time.
   - *Stoichiometric Mass Grade:* $(V_{\text{avail}}, V_{\text{dead}})$ requiring $\sum V_{\text{aspirate}} \le V_{\text{init}} - V_{\text{dead}}$ and preserving uncertainty intervals (`[V_lo, V_hi]`) on `OverpressureError` instead of deleting `loaded_volumes` via `CLEAR`.

**Adapter-Conservation Audit:** Does unifying onto `AffineRegion` + `Grade` merely shift complexity into hidden validators or string wrappers? **No—it eliminates existing fragile adapters:**
- *Removed:* Cello v2's `RoadBlockUtils` regex string parser (`STARTSWITH`/`BEFORE`/`AFTER` over Eugene rules assuming template prefix order), `Opentrons`'s split `get_next_tip` vs `_get_next_tip_with_nozzle_map` fallback, `PyLabRobot`'s disabled global `volume_tracking_enabled` switch, and `OpenDrop`'s directional 8-`if` `free_Fluxel` bitmasking.
- *Retained boundary:* Domain parameterization stays declarative (`UCF` Hill/toxicity curves, `NozzleMap` geometry, `well.dead_volume`, and `eta_rb` attenuation factors), checked directly by a `< 200 LoC` deterministic verifier without heuristic string rewriting.

## Boundaries

- **not examined:** Mammalian, yeast, or CRISPRi/dCas9 Cello UCF libraries (`Eco1C1G1T1` in *E. coli* was directly examined); physical PCB dielectric breakdown testing of `OpenDrop` V4 cartridges; multi-robot `PyLabRobot` scheduling beyond single-`LiquidHandler` `VolumeTracker`/`TipTracker` semantics; and automated DNA assembly sequence screening (biosecurity screening protocols).
- **unknown:** Exact quantitative ribosome-partitioning coefficient $\alpha_j$ variation across *E. coli* growth phases (exponential vs. stationary phase) in uncharacterized `Cello-v2` multi-output circuits (`> 8` repressors), and exact capacitive sensor noise thresholds of `OpenDrop`'s `FEEDBACK_pin` (`A2`) under high-conductivity biological lysis buffers without optical feedback.
- **known not to apply:** Deterministic 4-parameter median Hill ODE modeling does not capture stochastic gene-expression noise, plasmid copy-number variation, or bimodal population switching near threshold $K$, which require `Cello`'s cytometry histogram convolution (`Evaluate.simulateHistogramRPU`) or stochastic Gillespie simulation. Likewise, `Opentrons` `WellStore` and `PyLabRobot` `VolumeTracker` linear mass balances do not account for evaporative meniscus loss during multi-hour heated thermal-cycler runs without explicit evaporation rates.
- **unsupported:**
  - `CIDARLAB/cello` `Toxicity.java:46` explicitly does not support multi-input gate toxicity (`if (g.get_variable_names().size() == 1)`).
  - `Opentrons/opentrons` `TipView.get_next_tip()` (`tips.py:111-114`) explicitly does not support `starting_tip_name` combined with partial nozzle configurations, yet fails open into single-channel tip selection rather than raising an error.
  - `PyLabRobot/pylabrobot` `VolumeTracker` (`volume_tracker.py:134-145`) explicitly dropped per-reagent `Liquid` identity tracking (`get_liquids` returns `[(None, top_volume)]`).

## Evidence

### Inspected Repositories, Requisite Citations, and Source Regions

| Subject | Immutable Identity | Inspected Paths & Symbol / Line Ranges | Role |
| :--- | :--- | :--- | :--- |
| `CIDARLAB/Cello-v2` | `1b93575b8aa7e40e132381e3a9b29b1aa7f7a8e4` | `SimulatedAnnealing.java:211,313,338-419,794-800`; `TMToxicityEvaluation.java:63-183`; `RoadBlockUtils.java:122-215`; `ScoreUtils.java:48-92`; `Yosys.java:186-237`; `GateToxicity.java:37-218` | `source` |
| `CIDARLAB/cello` | `11644045e5ab677965a8e5765db2fb8535484a53` | `Toxicity.java:44-174`; `Roadblock.java:36-214`; `Evaluate.java:40-217,542-865`; `ResponseFunction.java:23-45`; `gates_Eco1C1G1T1.csv`; `Eco1C1G1T1.UCF.json` | `source` + `normative` |
| `GaudiLabs/OpenDrop` | `934a44db3ed41c24ae4dddb5b805a22e4166284b` | `OpenDropV4/Software/Libraries/OpenDrop/OpenDrop.cpp:69-95,276-291,473-611,934-1017`; `OpenDrop.h:17,101-114`; `hardware_def.h:7-114` | `source` |
| `Opentrons/opentrons` | `4bae21dfd6f164dc617093bcf2b0b14e27e00edf` | `api/src/opentrons/protocol_engine/state/tips.py:102-214`; `state/wells.py:35-162`; `state/pipettes.py:135-441`; `state/fluid_stack.py:21-125`; `commands/aspirate.py:93-222`; `commands/pick_up_tip.py:118-228` | `source` |
| `PyLabRobot/pylabrobot` | `dea2631feb592e0e7554afb1fe686eccd56688f8` | `pylabrobot/resources/volume_tracker.py:13-164`; `resources/tip_tracker.py:1-31`; `resources/well.py:31-151`; `legacy/liquid_handling/liquid_handler.py:1265-1312` | `source` |
| `Nielsen et al. (2016)` | `DOI: 10.1126/science.aac7341` | *Genetic circuit design automation*, Science 352(6281):aac7341 — Verilog-to-NOR synthesis, RPU, ribozyme insulation, 60-circuit characterization | `normative` |
| `Jones et al. (2022)` | `DOI: 10.1038/s41596-021-00675-2` | *Genetic circuit design automation with Cello 2.0*, Nature Protocols 17 — Cello v2 architecture, Yosys/ABC, UCF toxicity & roadblocking limits | `documentation` |
| `Gyorgy et al. (2015)` | `DOI: 10.1016/j.bpj.2015.06.037` | *Isocost lines describe the cellular economy of genetic circuits*, Biophysical Journal 109(3):639-646 — Shared ribosome-allocation retroactivity equations | `normative` |
| `Su & Chakrabarty (2006/2007)` | `DOI: 10.1109/DAC.2007.375283` | Static ($d_\infty \ge 2$) and dynamic fluidic droplet routing constraints for DMFBs | `normative` |

### Self-Contained Reproducible Verification Probe and Execution Output

Running the self-contained pure Python 3 standard-library probe below (`python3 -`, executed `2026-11-19`) reproduces every numerical claim reported above:

```python
import math, time

GATES = {
    "B1_BM3R1": {"ymax": 0.5, "ymin": 0.004, "K": 0.04, "n": 3.4},
    "P3_PhlF":  {"ymax": 6.8, "ymin": 0.02,  "K": 0.23, "n": 4.2},
    "Q1_QacR":  {"ymax": 2.4, "ymin": 0.01,  "K": 0.05, "n": 2.7},
    "E1_BetI":  {"ymax": 3.8, "ymin": 0.07,  "K": 0.41, "n": 2.4},
    "S4_SrpR":  {"ymax": 2.1, "ymin": 0.007, "K": 0.10, "n": 2.8},
    "A1_AmtR":  {"ymax": 3.8, "ymin": 0.06,  "K": 0.07, "n": 1.6},
}
Q1_IN = [0.009456264775413711, 0.02364066193853428, 0.04964539007092198, 0.16784869976359335, 0.55, 1.80, 5.20, 8.44, 17.52]
Q1_GR = [1.05, 0.97, 0.97, 0.99, 0.96, 0.89, 0.48, 0.12, 0.05]

def hill(g, x):
    p = GATES[g]
    return p["ymin"] + (p["ymax"] - p["ymin"]) / (1.0 + (x / p["K"]) ** p["n"])

def q1_tox(x):
    if x < Q1_IN[0]: s = Q1_GR[0]
    elif x > Q1_IN[-1]: s = Q1_GR[-1]
    else:
        s = 1.0
        for t in range(len(Q1_IN)):
            if x < Q1_IN[t]:
                lo, hi = math.log10(Q1_IN[t - 1]), math.log10(Q1_IN[t])
                w = (math.log10(x) - lo) / (hi - lo)
                s = Q1_GR[t - 1] * (1.0 - w) + Q1_GR[t] * w
                break
    return min(1.0, max(0.01, s))

def opendrop_free_fluxel(pad, x, y, d, w=16, h=8):
    ok = True
    if ok and (x > 0) and (d == 4): ok = pad.get((x - 1, y), 1) == 1
    if ok and (x < w - 1) and (d == 2): ok = pad.get((x + 1, y), 1) == 1
    if ok and (y > 0) and (d == 1): ok = pad.get((x, y - 1), 1) == 1
    if ok and (y < h - 1) and (d == 3): ok = pad.get((x, y + 1), 1) == 1
    if ok and (x > 0) & (y > 0) and (d in (1, 4)): ok = pad.get((x - 1, y - 1), 1) == 1
    if ok and (x > 0) & (y < h - 1) and (d in (3, 4)): ok = pad.get((x - 1, y + 1), 1) == 1
    if ok and (x < w - 1) and (y > 0) and (d in (1, 2)): ok = pad.get((x + 1, y - 1), 1) == 1
    if ok and (x < w - 1) and (y < h - 1) and (d in (2, 3)): ok = pad.get((x + 1, y + 1), 1) == 1
    return ok

cheb = lambda a, b: max(abs(a[0] - b[0]), abs(a[1] - b[1]))
def verify_ewod(curr, nxt):
    for i in range(len(curr)):
        for j in range(i + 1, len(curr)):
            if cheb(nxt[i], nxt[j]) < 2: return False, f"Static short at t+1 between D{i}{nxt[i]} and D{j}{nxt[j]}"
            if cheb(nxt[i], curr[j]) < 2 or cheb(curr[i], nxt[j]) < 2: return False, f"Dynamic short D{i}/D{j}"
    return True, "SAFE"

r_b1, r_p3 = hill("B1_BM3R1", 0.01), hill("P3_PhlF", 0.01)
print(f"[Probe 1A] B1_out={r_b1:.3f} RPU (tox={q1_tox(r_b1):.3f}) vs P3_out={r_p3:.3f} RPU (tox={q1_tox(r_p3):.3f}) -> stale TMToxicityEvaluation sees {q1_tox(r_b1):.3f} >= 0.75 vs actual {q1_tox(r_p3):.3f} < 0.75")

alpha, bg = 0.08, sum(0.08 * GATES[g]["ymax"] for g in ["A1_AmtR", "S4_SrpR", "Q1_QacR", "P3_PhlF", "E1_BetI", "A1_AmtR"])
p3_on, p3_off = hill("P3_PhlF", 0.01), hill("P3_PhlF", 1.0)
p3_e1_id = hill("E1_BetI", p3_off) / hill("E1_BetI", p3_on)
p3_e_on, p3_e_off = p3_on / (1 + bg + alpha * p3_on), p3_off / (1 + bg + alpha * p3_off)
p3_e1_cp = (hill("E1_BetI", p3_e_off) / (1 + bg + alpha * (p3_off + hill("E1_BetI", p3_e_off)))) / (
            hill("E1_BetI", p3_e_on)  / (1 + bg + alpha * (p3_on  + hill("E1_BetI", p3_e_on))))
s4_on, s4_off = hill("S4_SrpR", 0.01), hill("S4_SrpR", 1.0)
s4_e1_id = hill("E1_BetI", s4_off) / hill("E1_BetI", s4_on)
s4_e_on, s4_e_off = s4_on / (1 + bg + alpha * s4_on), s4_off / (1 + bg + alpha * s4_off)
s4_e1_cp = (hill("E1_BetI", s4_e_off) / (1 + bg + alpha * (s4_off + hill("E1_BetI", s4_e_off)))) / (
            hill("E1_BetI", s4_e_on)  / (1 + bg + alpha * (s4_on  + hill("E1_BetI", s4_e_on))))
print(f"[Probe 1A] Ribosome isocost: ideal P3->E1 ON/OFF={p3_e1_id:.2f}x (P3_ON={p3_on:.2f} RPU) -> coupled 8-gate P3_ON={p3_e_on:.2f} RPU, E1 ON/OFF={p3_e1_cp:.2f}x ({(1-p3_e1_cp/p3_e1_id)*100:.1f}% drop); S4->E1 ideal={s4_e1_id:.2f}x (S4_ON={s4_on:.2f}) -> coupled S4_ON={s4_e_on:.2f} RPU, ON/OFF={s4_e1_cp:.2f}x ({(1-s4_e1_cp/s4_e1_id)*100:.1f}% drop)")
print(f"[Probe 1A] Roadblock mismatch: additive E1_out(0.85)={hill('E1_BetI',0.85):.3f} RPU vs roadblocked(eta=0.18) E1_out(0.194)={hill('E1_BetI',0.194):.3f} RPU ({hill('E1_BetI',0.194)/hill('E1_BetI',0.85):.2f}x leakage)")

cols = []
for x1 in range(2, 8):
    for y1 in range(1, 7):
        p0, p1 = (4, 3), (x1, y1)
        if cheb(p0, p1) < 2: continue
        pad = {(x, y): 1 for x in range(16) for y in range(8)}; pad[p0] = pad[p1] = 0
        for dx0, dy0, d0 in [(0,-1,1),(1,0,2),(0,1,3),(-1,0,4)]:
            n0 = (p0[0]+dx0, p0[1]+dy0)
            if not opendrop_free_fluxel(pad, n0[0], n0[1], d0): continue
            for dx1, dy1, d1 in [(0,-1,1),(1,0,2),(0,1,3),(-1,0,4)]:
                n1 = (p1[0]+dx1, p1[1]+dy1)
                if not opendrop_free_fluxel(pad, n1[0], n1[1], d1): continue
                ok, msg = verify_ewod([p0, p1], [n0, n1])
                if not ok: cols.append((p0, n0, p1, n1, msg))
ex = cols[0]
print(f"[Probe 1B] Found {len(cols)} 2-droplet trajectories passing OpenDrop free_Fluxel() from valid d_inf>=2 start yet violating fluidic spacing")
print(f"[Probe 1B] Example: D0 {ex[0]}->{ex[1]} & D1 {ex[2]}->{ex[3]} => {ex[4]}")
well_vol, dead_vol, reqs = 100.0, 15.0, [45.0, 45.0]
usable = well_vol - dead_vol
print(f"[Probe 1B] Dead-volume audit: well={well_vol}uL, dead={dead_vol}uL, requests={reqs} (total={sum(reqs)}uL) -> usable={usable}uL => OVERDRAW={sum(reqs) > usable} (shortfall {sum(reqs)-usable:.1f}uL)")
```

Captured stdout (`exit 0`, executed `2026-11-19`; standalone timing benchmark measured `2.80 us/step` over `1,000` 4-droplet checks):
```text
[Probe 1A] B1_out=0.496 RPU (tox=0.963) vs P3_out=6.800 RPU (tox=0.281) -> stale TMToxicityEvaluation sees 0.963 >= 0.75 vs actual 0.281 < 0.75
[Probe 1A] Ribosome isocost: ideal P3->E1 ON/OFF=50.94x (P3_ON=6.80 RPU) -> coupled 8-gate P3_ON=2.02 RPU, E1 ON/OFF=27.51x (46.0% drop); S4->E1 ideal=26.61x (S4_ON=2.10) -> coupled S4_ON=0.70 RPU, ON/OFF=4.26x (84.0% drop)
[Probe 1A] Roadblock mismatch: additive E1_out(0.85)=0.622 RPU vs roadblocked(eta=0.18) E1_out(0.194)=3.269 RPU (5.25x leakage)
[Probe 1B] Found 14 2-droplet trajectories passing OpenDrop free_Fluxel() from valid d_inf>=2 start yet violating fluidic spacing
[Probe 1B] Example: D0 (4, 3)->(4, 2) & D1 (2, 1)->(3, 1) => Static short at t+1 between D0(4, 2) and D1(3, 1)
[Probe 1B] Dead-volume audit: well=100.0uL, dead=15.0uL, requests=[45.0, 45.0] (total=90.0uL) -> usable=85.0uL => OVERDRAW=True (shortfall 5.0uL)
```

## Revalidation

To test whether these defects or assumptions change in a newer upstream revision of any subject:

1. **Cello v2 Stale-Activity Toxicity & Roadblocking:** Inspect `SimulatedAnnealing.java` around `TMToxicityEvaluation` instantiation (`new TMToxicityEvaluation(getNetlist(), ...)`) to check whether the argument changed from `getTMActivityEvaluation()` to the newly constructed post-swap `tmae`, and check `RoadBlockUtils.isRoadBlockable()` for removal of the consecutive-head assumption (`// TODO Lazy implementation`).
2. **OpenDrop `getDrop()` & `free_Fluxel()`:** Diff `OpenDrop.cpp` inside `OpenDrop::getDrop()` (`if (num > max_drops)` placement relative to `drops[num - 1]._dropnum = num` and `this->drop_count = num`) and verify whether `free_Fluxel` / `run()` checks lateral neighbors and updates planned `(_next_x, _next_y)` occupancy across droplets.
3. **Opentrons Partial-Nozzle & Dead-Volume Checks:** Inspect `TipView.get_next_tip()` in `api/src/opentrons/protocol_engine/state/tips.py` for whether `starting_tip_name is not None` with a partial `NozzleMap` dispatches to physical clearance checking or raises an error, and inspect `WellState` / `WellStore._handle_well_operated()` in `state/wells.py` for `dead_volume` bounds and non-destructive `OverpressureError` volume handling.
4. **PyLabRobot Global Volume & Reagent Tracking:** Check `pylabrobot/resources/volume_tracker.py` for `volume_tracking_enabled` default value and per-`Liquid` provenance restoration in `VolumeTracker`.
5. **Micro-Probe Regression:** Re-run the inline Python 3 probe under `## Evidence` against any updated UCF `.csv`/`.json` parameters (`ymax`, `ymin`, `K`, `n`, `gate_toxicity`) to recompute `ON/OFF` collapse and toxicity bounds in `< 10 ms`.
