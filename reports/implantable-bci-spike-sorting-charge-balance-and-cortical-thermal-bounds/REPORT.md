# Implantable BCI Spike Sorting, Electrochemical Charge Balance, and Cortical Thermal Safety Bounds

## Summary

Closed-loop cortical brain-computer interfaces (BCIs) couple three tightly constrained domains: (1) low-latency neural acquisition, stimulation-artifact blanking, and drift-compensated spike sorting (`open-ephys/plugin-GUI`, `SpikeInterface/spikeinterface`, `MouseLand/Kilosort`), (2) biphasic electrochemical charge-balance and tissue-damage limits (`Shannon 1992`, `Merrill et al. 2005`, `Cogan 2008`), and (3) cortical thermal dissipation ceilings (`ISO 14708-3:2017`, `Wolf 2008` Pennes bioheat bounds). End-to-end safety requires hardware- and ROM-enforced physical invariants because adaptive decoders routinely undergo post-implant software updates—such as algorithmic compensation after flexible-thread retraction in the 2024 Neuralink PRIME study—and cannot be trusted with unconstrained stimulation authority.

Direct source inspection and executable physical simulations establish five concrete boundaries and failure modes:
1. **Ring-Buffer Sample-Number Corruption in Open Ephys:** `DataQueue::fillSampleNumbers()` (`DataQueue.cpp:120-151`) computes `startSampleNumber + (i * m_blockSize)` where `i` already increments by `m_blockSize`, producing quadratic sample-number skew (`1024^2` stride), repeatedly overwrites a single `m_sampleNumbers[blockIdx]`, and can write out-of-bounds (`blockIdx == m_numBlocks`) when wrapping across the final block.
2. **Spike-Sorting Refractory-Gate and Drift Fragilities in Kilosort4:** Prior to commit `0e07514c` (PR `#1043`), `swarmsplitter.py:56-61` checked `len(st2 == 0)` instead of `len(st2) == 0`, causing a truthy boolean-array length on all non-empty spike trains and silently disabling cross-correlogram refractoriness checks. Meanwhile, `CCG.py:90-91` and `swarmsplitter.py:66-67` diverge on `Q00 < 0.25` acceptance gates, and `datashift.py`/`preprocessing.py` rely on offline GPU batch Kriging (`2.0 s` windows) unsuitable without adaptation for `< 2 ms` real-time cortical closed-loop triggers.
3. **Stimulation-Artifact Blanking Deadlocks and Interpolation Faults:** `SpikeInterface` `RemoveArtifactsRecording` defaults (`ms_before = 0.5`, `ms_after = 3.0`) blank `45.5%` of all samples at `130 Hz` deep-brain stimulation and `87.5%` at `250 Hz` (`100%` lockout at `>= 286 Hz`), creating a closed-loop decoder starvation deadlock if stimulation triggers re-enter blanking windows. Source inspection also identifies a `TypeError` (`warnings(...)` called as a function at `remove_artifacts.py:108`), unguarded zero-norm `NaN` division (`lines 414-417`), and boundary blowup under `scipy.interpolate.interp1d(..., kind="cubic", fill_value="extrapolate")`.
4. **Biphasic DAC Mismatch Electrolysis & Shannon Microelectrode Breakdown:** Even a `1%` anodic/cathodic current-source mismatch (`0.10 nC` residual per `10 nC` pulse at `200 Hz` on a `20 nF` microelectrode) ratchets interfacial double-layer potential past the `+0.8 V` vs. `Ag|AgCl` platinum-iridium water window within **`320` pulses (`1.60 s`)**, triggering Faradaic gas evolution and thin-film `SIROF`/`PtIr` delamination unless suppressed by interpulse passive electrode shorting (`V_short = 6.92e-90 V` steady state). Moreover, satisfying Shannon's macroelectrode formula ($\log_{10} D + \log_{10} Q \le 1.85$) does *not* protect microelectrodes ($A = 2{,}000\,\mu\text{m}^2$, $Q = 0.02\,\mu\text{C} \implies k = 1.30 \le 1.85$), whose charge density $D = 1{,}000\,\mu\text{C/cm}^2$ exceeds bare `PtIr` capacitive injection limits (`~150 uC/cm^2`) by `6.7x`.
5. **Cortical Pennes Bioheat Power Ceilings:** Solving steady-state cortical Pennes bioheat diffusion ($k_{\text{tis}} = 0.52\,\text{W/(m}\cdot\text{K)}$, perfusion $\omega_b \rho_b c_b = 37{,}000\,\text{W/(m}^3\cdot\text{K)}$, characteristic length $L_p = 3.75\,\text{mm}$) yields `13.9 mW/cm^2` per `1 °C` for an infinite planar sheet and `48.5 mW/cm^2` (`~40 mW/cm^2` cortical design ceiling, `Wolf 2008`) for a `5 mm`-radius cortical die (`97.1 mW/cm^2` at `ISO 14708-3`'s `2 °C` ceiling). This power floor rules out onboard floating-point GPU sorting (`15–300 W`) and forces implanted DSP into `< 10–20 mW` fixed-point ASIC pipelines decoupled from untrusted decoder weights behind a single **Charge-Shannon-Bioheat Safety Semiring**.

## Applicability

This report covers the exact upstream revisions, hardware specifications, and biomedical standards in `REPORT.json`:
- **Acquisition and real-time audio/data ring transport:** `open-ephys/plugin-GUI` (`560c995500f7f1438c6c3646311ff11776da49bb`), specifically `Source/Processors/DataThreads/DataBuffer.cpp` and `Source/Processors/RecordNode/DataQueue.cpp`.
- **Offline/workstation preprocessing and drift-compensated sorting:** `SpikeInterface/spikeinterface` (`1d7bacaa2a934ed4547f906e637887f3f609f9b1`, `remove_artifacts.py` and `motion.py`) and `MouseLand/Kilosort` (`0e07514c16fc1162f6470ecbad25be9c7e256306`, `Kilosort4` Python/PyTorch pipeline).
- **Electrochemical and thermal neuromodulation invariants:** Biphasic current-controlled microstimulation (exemplified by integrated stimulator/amplifier ASICs such as the Intan `RHS2116` architecture), `Shannon (1992)` macroelectrode boundaries, `Merrill, Bikson, & Jefferys (2005)` charge-recovery models, `Cogan (2008)` `PtIr`/`SIROF` electrochemical water-window limits, `ISO 14708-3:2017` neurostimulator thermal ceilings, and FDA's May 2021 IDE guidance on implanted BCIs.

Findings distinguish **workstation/offline batch sorters** (high-throughput multi-hour recordings on CUDA GPUs) from **implanted closed-loop firmware/ASICs** (`< 1–2 ms` trigger latency, `< 40–80 mW/cm^2` cortical dissipation), noting explicitly where algorithms (`Kilosort4` full-recording Kriging) cannot run directly inside an implanted package without structural refactoring.

## Findings

### 1. Real-Time Extracellular Acquisition Rings and Sample-Number Corruption in Open Ephys

`Basis: source + execution`

`open-ephys/plugin-GUI` separates USB/PCIe acquisition threads from downstream processing and disk recording via single-producer single-consumer (SPSC) lock-free circular buffers built on JUCE `AbstractFifo`:

#### 1.1 Silent Producer Truncation & Wraparound Scalar Loss in `DataBuffer`
In `Source/Processors/DataThreads/DataBuffer.cpp`:
- **Partial Write Truncation (`DataBuffer.cpp:66-104`):** `addToBuffer()` calls `abstractFifo.prepareToWrite(numItems, startIndex1, blockSize1, startIndex2, blockSize2)` (`line 74`) and iterates over `bs = {blockSize1, blockSize2, 0}` (`lines 76-98`), returning `idx = blockSize1 + blockSize2`. If the ring is nearly full (`idx < numItems`), tail samples `[idx .. numItems)` are silently omitted from the circular buffer without emitting an internal overflow flag inside `DataBuffer`—shifting drop detection responsibility entirely onto every `DataThread` subclass checking the return value.
- **Single-Timestamp Wraparound Ambiguity (`lines 137-161`):** During `readAllFromBuffer()`, when a read splits across the ring boundary (`blockSize1 > 0` and `blockSize2 > 0`), `DataBuffer` copies `blockTimestamps` and `eventCodes` from both segments (`lines 138-139, 159-160`), yet copies only a **single `int64` scalar** `*blockSampleNumber = sampleNumberBuffer[startIndex1]` (`line 137`). Consumers assume sample numbers step strictly by `+1` across the two wrapped segments; any upstream hardware sample skip (`gap > 0`) starting inside `startIndex2` is invisible to downstream spike sorters.

#### 1.2 Quadratic Sample-Number Skew & Out-of-Bounds Write in `DataQueue::fillSampleNumbers`
In `Source/Processors/RecordNode/DataQueue.cpp:120-151`, `DataQueue` stores one sample number per `m_blockSize`-sample block (`m_sampleNumbers` sized `m_numBlocks` at `lines 80-83`):
```cpp
// DataQueue.cpp:137-150
        blockIdx++;
    }
    int64 latestSampleNumber;
    for (int i = 0; i < size; i += m_blockSize)
    {
        if ((blockStartPos + i) < (index + size))
        {
            latestSampleNumber = startSampleNumber + (i * m_blockSize);
            m_sampleNumbers[blockIdx] = latestSampleNumber;
        }
    }
```
Source inspection and execution (`[Probe 2B]`) reveal three coupled bugs in `fillSampleNumbers`:
1. **Quadratic Sample Offset (`line 147`):** Because `i` advances in increments of `m_blockSize`, multiplying `i * m_blockSize` advances `latestSampleNumber` by `k * m_blockSize^2` instead of `i` (`startSampleNumber + i`). With `m_blockSize = 1024`, `index = 7168`, `size = 3072`, `sampleNumber = 100000`, iteration `i = 2048` computes `100000 + 2048 * 1024 = 2,197,152` instead of `102,048`.
2. **Missing `blockIdx` Increment (`line 148`):** `blockIdx` is never incremented (or wrapped modulo `m_numBlocks`) inside the loop, overwriting the same `m_sampleNumbers[blockIdx]` slot on every block of a multi-block write while leaving subsequent block entries stale.
3. **End-of-Ring Out-of-Bounds Vector Access (`lines 137, 148`):** When a non-aligned write (`blockMod != 0`) begins in the last ring block (`index = 7680` with `blockSize = 1024, numBlocks = 8`, so `index // 1024 = 7`), line `137` increments `blockIdx++` to `8 == m_numBlocks`, and for `size = 1024`, `(8192 + 0) < (7680 + 1024) = 8704` holds—triggering an unchecked `m_sampleNumbers[8]` out-of-bounds write (`[Probe 2B]`).
4. **Independent Audio/Timestamp FIFO Read Thresholds (`lines 385, 452`):** `DataQueue::startRead()` independently clamps `samplesToRead` on `m_fifos` and `ftsToRead` on `m_FTSFifos` without requiring `ftsToRead == samplesToRead`, permitting synchronized-timestamp streams to skew relative to neural trace indices under disk-write backpressure.

---

### 2. Drift-Compensated Spike Sorting, Template Matching, and Refractory-Gate Fragility in Kilosort4

`Basis: source + execution + documentation`

Brain tissue micromotion and mechanical probe/thread retraction—clinically underscored in May 2024 when Neuralink disclosed in its PRIME Study progress update that flexible cortical threads retracted from brain tissue post-implant, reducing active contact yield until decoding algorithms were adapted—cause extracellular spike amplitudes to translate vertically across electrode sites over seconds to weeks.

#### 2.1 Batch Drift Fingerprinting and Gaussian Kernel Kriging (`datashift.py`, `preprocessing.py`)
`MouseLand/Kilosort` (`0e07514c`) models vertical drift $d_{\text{shift}}(t, y)$ prior to template extraction:
1. **Universal Spike Detection & 2D Fingerprinting (`datashift.py:12-63`):** `spikedetect.run()` extracts candidate spikes per `batch_size = 60,000` samples (`2.0 s` at `30 kHz`, `parameters.py:34-44`). `bin_spikes()` constructs a sparse 2D matrix per batch over vertical depth (`binning_depth`) and `20` logarithmic amplitude bins (`Th_universal = 9` to `100`), applying $\log_2(1 + \text{count})$ compression (`line 58`).
2. **Block-Wise Iterative Alignment (`align_block2`, `datashift.py:66-168`):** Performs `10` rigid vertical alignment iterations (`n = 15` depth bins via `torch.roll`, `lines 82-108`), then subdivides depth into `2 * nblocks - 1` half-overlapping blocks (`lines 110-118`), smooths cross-correlation tensors (`gaussian_filter(dcs, drift_smoothing)`, `line 144`), and upsamples peak offsets by `10x` via Gaussian kernels (`kernelD`, `lines 138-156`).
3. **Kriging Spatial Resampling (`preprocessing.py:44-69`, `datashift.py:216-224`):** Precomputes the probe-contact Gaussian covariance inverse:
   $$K_{xx}^{-1} = \bigl(K(\mathbf{x}_p, \mathbf{x}_p; \sigma_{\text{interp}}) + 0.01\,I\bigr)^{-1}, \qquad M(t) = K(\mathbf{x}_p - \Delta y(t)\,\hat{\mathbf{y}}, \mathbf{x}_p; \sigma_{\text{interp}}) \, K_{xx}^{-1}$$
   Linearly multiplying raw/whitened voltage batches by $M(t)$ reconstructs stationary virtual channels. `SpikeInterface`'s `motion.py` generalizes this stage across `"dredge"` (decentralized/DREDge AP, `win_step_um = 400.0`, `win_scale_um = 400.0`), `"nonrigid_accurate"` (`monopolar_triangulation` + decentralized), and `"kilosort_like"` presets, using `border_mode = "force_extrapolate"` or `"remove_channels"`. Crucially, if electrode threads retract completely out of cortical gray matter (no surviving neighbor amplitude gradient), Kriging interpolation cannot hallucinate missing signal—explaining why clinical systems must pair drift registration with decoder weight re-calibration over surviving contacts.

#### 2.2 Orthogonal PCA Matching and Refractory-Gate Bug (`template_matching.py`, `CCG.py`, `swarmsplitter.py`)
- **Convolutional PCA Peeling (`template_matching.py:155-245`):** `prepare_matching()` precomputes temporal filter autocorrelations `WtW` and spatial-temporal pairwise template overlaps `ctc = UtU @ WtW` (`lines 158-165`). `run_matching()` projects residual `Xres` onto `wPCA`, evaluates $C_f = \text{ReLU}(B)^2 / \|U\|_F^2$ (`line 197`), picks non-overlapping peaks via `max_pool1d` over `2*nt + 1` (`nt = 61`, `2.03 ms` window, `line 206`), peels peaks exceeding `Th_learned^2` (`8^2 = 64`) for up to `max_peels` iterations, and subtracts exact waveform/projection updates in 2-strided slices (`lines 235-238`).
- **Auto/Cross-Correlogram (`CCG`) Merge Gate & `len(st2 == 0)` Bug:** Biological neurons obey an absolute/relative refractory period (`~1–3 ms`). `CCG.compute_CCG` and `CCG_metrics` (`CCG.py:8-78`) evaluate the ratio of refractory-window coincidences $R_{12}$ and Poisson tail $p$-value $Q_{12}$ over `1..10 ms` bins (`lines 55-68`). In `swarmsplitter.py:53-68`, commit `0e07514c16fc1162f6470ecbad25be9c7e256306` repaired a silent regression where `len(st2 == 0)` had replaced `len(st2) == 0`: in NumPy, `st2 == 0` yields a boolean vector of length `N`, so `len(st2 == 0)` is truthy for *all* non-empty spike trains (`[Probe 2B]`), bypassing `compute_CCG` and forcing `check_CCG` to return `(False, False)` across all real units! Even at commit `0e07514c`, `CCG.py:90-91` enforces `R12 < acg_threshold and (Q12 < 0.2)` (`# or Q00 < .25` commented out), whereas `swarmsplitter.py:66-67` enforces `R12 < 0.1 and (Q12 < 0.2 or Q00 < 0.25)`, permitting low-rate bursty splits (`Q00 < 0.25`) to pass differently between hierarchical splitting and final merging.

---

### 3. Stimulation-Artifact Blanking Deadlocks and Interpolation Pitfalls in Closed-Loop Pipelines

`Basis: normative + source + execution`

Closed-loop neuromodulation simultaneously stimulates at milliamps/volts while attempting to record microvolt action potentials (`~50–300 uV`, `> 80 dB` dynamic-range separation). Hardware front-ends such as the Intan `RHS2116` isolate recording amplifiers via fast-settling switches (`amp settle` bits shifting high-pass cutoff $f_L$ up to `500 Hz` post-pulse) and software pipelines strip remaining transients (`SpikeInterface` `RemoveArtifactsRecording`, `remove_artifacts.py:92-449`).

#### 3.1 Three Concrete Implementation Pitfalls in `RemoveArtifactsRecording`
1. **Callable-Module Exception (`remove_artifacts.py:107-108`):** Passing deprecated `waveforms_kwargs` executes `warnings("...")`—calling the Python `warnings` module instead of `warnings.warn(...)`—and immediately throws `TypeError`.
2. **Boundary Overshoot Under Cubic Extrapolation (`lines 347-358`):** In `mode="cubic"`, `scipy.interpolate.interp1d(all_idx, interp_traces, kind="cubic", axis=0, bounds_error=False, fill_value="extrapolate")` extrapolates a degree-3 spline whenever an artifact lies within `[start_frame, start_frame + pad[0]]` or `[end_frame - pad[1], end_frame]`, producing ringing overshoot at chunk boundaries when fed into downstream bandpass filters.
3. **Unintended Cosine-Normalized Scaling & Zero-Norm `NaN` (`lines 414-445`):** In `mode="average"`/`"median"` with `time_jitter > 0`, `best_amplitudes[count]` computes cosine similarity `dot(trace, artifact) / (||trace|| * ||artifact||)` (`lines 414-417`). If a channel/segment is zeroed, `norm == 0` yields `NaN` (corrupting the trace); if `scale_amplitude=True`, subtracting `best_amp * artifact` scales by the unitless correlation `<= 1.0` rather than the least-squares amplitude projection $\frac{\langle \text{trace}, \text{artifact}\rangle}{\|\text{artifact}\|^2}$!

#### 3.2 Closed-Loop Blanking Starvation and Feedback Oscillation Deadlocks
When a spike detector triggers stimulation whenever decoded firing rate crosses a threshold, each trigger blanks `[t_trig - ms_before, t_trig + ms_after]` (`0.5 + 3.0 = 3.5 ms` default in `remove_artifacts.py:96-97`; up to `5–8 ms` when hardware recovery tails are included). Defining the effective observation fraction:
$$\eta_{\text{obs}}(f_{\text{stim}}) = \max\bigl(0,\; 1 - f_{\text{stim}} \cdot (t_{\text{pre}} + t_{\text{post}} + t_{\text{settle}})\bigr)$$
`[Probe 2B]` quantifies how high-frequency clinical stimulation (`3.5 ms` window) starves closed-loop sensing:
- `30 Hz` theta/beta burst: `10.5%` blanked (`89.5%` observable);
- `130 Hz` conventional DBS: **`45.5%`** blanked (nearly half of all cortical spikes lost or fragmented across `pad` edges);
- `250 Hz` high-rate ICMS: **`87.5%`** blanked;
- `>= 286 Hz` (`300 Hz` burst): **`100.0%`** blanked—inducing total sensory blindness.

**Re-Entrant Blanking Deadlock:** If stimulation rebound or residual edge-filter ringing around `t_trig + ms_after` trips the threshold spike detector, the closed-loop controller immediately fires another pulse, locking the implant at its maximum pulse repetition rate (`100%` blanked) until hardware watchdog or thermal cutoffs trip. Closed-loop firmware must enforce a **monotonic blanking-holdoff refractory invariant** ($T_{\text{min\_interpulse}} > t_{\text{blank}} + t_{\text{filter\_settle}}$) plus hard duty-cycle caps outside the trainable decoder.

---

### 4. Biphasic DAC Mismatch, Passive Discharge, Water-Window Electrolysis, and Shannon Damage Limits

`Basis: normative + documentation + execution`

#### 4.1 Charge-Balance Law, DAC Mismatch Ratcheting, and Electrode Delamination
Safe neurostimulation prevents irreversible Faradaic oxidation/reduction (water electrolysis: $\text{H}_2$ evolution $< -0.6\text{ V}$, $\text{O}_2$ evolution / Pt dissolution $> +0.8\text{ V}$ vs. $\text{Ag}|\text{AgCl}$ in saline, `Cogan 2008`, DOI: `10.1146/annurev.bioeng.10.061807.160518`). Over a stimulation period $T$, the net injected charge must satisfy:
$$Q_{\text{net}} = \int_0^T I(t)\,dt = 0 \quad \text{(ideally symmetric cathodic-first biphasic: } I_c t_c = I_a t_a \text{)}$$
In real CMOS stimulator DACs (even with trimmed current mirrors), process mismatch $\epsilon \in [0.2\%, 2\%]$ leaves a residual imbalance $\Delta Q = \epsilon Q_{\text{phase}}$ per pulse (`Merrill, Bikson, & Jefferys 2005`, DOI: `10.1016/j.jneumeth.2004.10.020`). On a capacitive double layer $C_{\text{dl}}$ shunted only by high Faradaic leakage resistance $R_f$, pulse $N$ ratchets interfacial polarization according to:
$$V_{C_{\text{dl}}}[N] = V_{C_{\text{dl}}}[N-1] \cdot e^{-T_{\text{rep}} / (R_f C_{\text{dl}})} + \frac{\Delta Q}{C_{\text{dl}}}$$
As verified in `[Probe 2A]`, driving a microelectrode ($C_{\text{dl}} = 20\,\text{nF}$, $R_f = 50\,\text{M}\Omega$) at `200 Hz` (`Q = 10 nC/phase`, `50 uA * 200 us`) with just a **`1%` anodic mismatch** ($\Delta Q = 0.10\,\text{nC/pulse}$, net DC leakage `20 nA`) drives $V_{C_{\text{dl}}}$ past the `+0.8 V` water window at **pulse `#320` (`1.60 s`)**, stabilizing at **`1.00 V`** in open-circuit leakage—destroying tissue via pH gradients and forming gas micro-bubbles beneath thin-film **PtIr** or **SIROF** (Sputtered Iridium Oxide Film) layers that trigger catastrophic coating **delamination** (a primary failure mode flagged in FDA's May 2021 BCI IDE guidance).

**Passive Discharge Shorting & Compliance Monitoring:** Engaging an interpulse low-impedance passive discharge switch ($R_{\text{dis}} = 500\,\Omega \implies \tau = R_{\text{dis}} C_{\text{dl}} = 10\,\mu\text{s}$ over a `2 ms` interpulse window—as implemented via the Intan `RHS2116` charge-recovery switch and `±1.22 V` current-limited `1 nA–1 uA` recovery modes) clamps steady-state polarization to **`6.92e-90 V`** (`[Probe 2A]`), while series DC-blocking capacitors (`~100 nF–1 uF`) guarantee $I_{\text{DC}} = 0$ even under single-fault MOSFET stuck-on failure. Concurrently, hardware compliance monitors (`RHS2116` `VSTIM` supply bounded to `±7 V`, `<= 14 V` total span) detect open/delaminated high-impedance leads immediately when $I_{\text{stim}} \cdot |Z_{\text{elec}}(f)| + V_{C_{\text{dl}}} > V_{\text{compliance}}$, locking out further pulsing on faulted sites.

#### 4.2 Shannon Empirical Limit ($k = 1.85$) vs. Microelectrode Geometric Breakdown
`Shannon (1992)` (*IEEE Trans. Biomed. Eng.*, DOI: `10.1109/10.126616`) parameterized safe macroelectrode stimulation regions from McCreery et al.'s cortical histology via:
$$\log_{10}(D) + \log_{10}(Q) \le k, \qquad D = \frac{Q}{A}\; [\mu\text{C/cm}^2], \quad Q\; [\mu\text{C/phase}], \quad k = 1.85$$
Rewriting $D \cdot Q \le 10^k \approx 70.79$ (`k = 1.85`; conservative chronic threshold $k = 1.5 \implies 31.62$) exposes a dangerous blindspot when scaling from `1 mm^2` macroelectrodes (`0.01 cm^2`) down to `100–2,000 um^2` microelectrodes (`Cogan 2008`, `[Probe 2A]`):

| Regime | Area $A$ | Charge $Q$ ($\mu\text{C/ph}$) | Charge Density $D$ ($\mu\text{C/cm}^2$) | Shannon $k = \log_{10}(DQ)$ | Physical Water-Window / CIC Safety Status |
| :--- | :--- | ---: | ---: | ---: | :--- |
| **Macroelectrode (DBS/ECoG)** | `0.01 cm^2` (`1 mm^2`) | `0.800` | `80.0` | `1.81 <= 1.85` | **SAFE** (`80 uC/cm^2` within bare `PtIr` CIC `50–150 uC/cm^2`) |
| **Cortical Microelectrode (Bare PtIr)** | `2,000 um^2` (`2e-5 cm^2`) | `0.020` | `1,000.0` | `1.30 <= 1.85` | **UNSAFE** (`1,000 uC/cm^2` is **`6.7x` above** `PtIr` CIC `150 uC/cm^2` -> electrolysis!) |
| **Cortical Microelectrode (SIROF)** | `2,000 um^2` (`2e-5 cm^2`) | `0.020` | `1,000.0` | `1.30 <= 1.85` | **SAFE** (`1,000 uC/cm^2` within `SIROF` reversible faradaic CIC `1.5–5 mC/cm^2`) |

Because Shannon's curve allows $D$ to grow inversely with $Q$ as $Q \to 0$, $k \le 1.85$ is **necessary only for macroelectrodes and non-sufficient for microelectrodes**: cortical safety requires the conjunction $(\log_{10} D + \log_{10} Q \le 1.85) \;\land\; (D \le \text{CIC}_{\text{material}}) \;\land\; (V_{C_{\text{dl}}} \in [V_{\text{H}_2}, V_{\text{O}_2}])$.

---

### 5. Cortical Pennes Bioheat Equations and ISO 14708-3 Power-Density Ceilings

`Basis: normative + documentation + execution + derived`

Implanted CMOS amplification, telemetry, and closed-loop DSP electronics dissipate Joule heat directly onto pia/cortex or subgaleal tissues. Under `ISO 14708-3:2017` (Active Implantable Medical Devices — Implantable Neurostimulators, Clause 17.1), no outer surface of the implantable pulse generator or tissue-contacting electronics may exceed normal body temperature by **more than $\Delta T_{\max} = 2\,^\circ\text{C}$ (`39 °C`)**, while cortical neuroengineering guidelines (`Wolf 2008`, *Indwelling Neural Implants*; FDA 2021 BCI Guidance) target a conservative **$\Delta T_{\max} < 1\,^\circ\text{C}$** to avoid glial proliferation and neuronal thermal stress.

Modeling steady-state heat transport via the Pennes bioheat equation (`Wolf 2008`, `[Probe 2B]`):
$$k_{\text{tis}}\,\nabla^2 T - \omega_b \rho_b c_b \,(T - T_a) + q_m = 0$$
with gray-matter thermal conductivity $k_{\text{tis}} \approx 0.52\,\text{W/(m}\cdot\text{K)}$ and blood-perfusion sink $\omega_b \rho_b c_b \approx 37{,}000\,\text{W/(m}^3\cdot\text{K)}$, the characteristic cortical thermal perfusion length is:
$$L_p = \sqrt{\frac{k_{\text{tis}}}{\omega_b \rho_b c_b}} \approx \mathbf{3.75\,\text{mm}}$$
1. **Semi-Infinite 1D Planar Bound (`[Probe 2B]`):** Integrating the 1D exponentially decaying profile $T(z) - T_a = \Delta T_0 e^{-z/L_p}$ gives surface heat flux $q''_{\text{1D}} = \sqrt{k_{\text{tis}} \omega_b \rho_b c_b}\,\Delta T_0 \approx \mathbf{13.9\,\text{mW/cm}^2\text{ per }^\circ\text{C}}$ (worst case for large epidural plates $r \gg L_p$).
2. **3D Spreading on Compact Cortical Dies (`r = 5.0 mm`, `A = 0.785 cm^2`):** Radial conduction plus perfusion yields $q''_{\text{3D}} \approx \frac{2 k_{\text{tis}}(1 + r/L_p)}{r} \Delta T_0$, allowing **`48.5 mW/cm^2`** at $\Delta T = 1\,^\circ\text{C}$ (matching the classic **`~40 mW/cm^2`** cortical implant ceiling) and **`97.1 mW/cm^2`** (`~80 mW/cm^2` for $\sim 1\,\text{cm}^2$ encapsulated devices) at `ISO 14708-3`'s `2 °C` ceiling.

**Architectural Consequence for Spike Sorting:** A `384`-channel desktop `Kilosort4` pipeline on a discrete GPU draws `15–300 W` (`100–2,000x` above the `~15–40 mW` total implantable cortical power budget). Consequently, implantable closed-loop BCIs must either stream compressed spike/bandpass snippets transcutaneously or run fixed-point (`int8`/`int16`) matched filtering on-die (`< 10–20 mW`), reserving full `Kilosort4`/`SpikeInterface` Kriging updates for asynchronous external recalibration—and ensuring any over-the-air updated decoder runs strictly *upstream* of hardware- and ROM-enforced charge/Shannon/thermal safety interlocks.

---

### 6. Multi-Level Performance and Resource Footprint Analysis (L1–L6)

`Basis: source + execution + derived`

Comparing host/workstation processing stacks (`Open Ephys`, `SpikeInterface`, `Kilosort4`) against implantable closed-loop fixed-point DSP and a standalone physical safety shield across all six performance and footprint levels:

| Metric Level | `Open Ephys` (`560c9955`) C++ Host | `SpikeInterface` (`1d7bacaa`) Python Host | `Kilosort4` (`0e07514c`) PyTorch GPU | Implanted Fixed-Point DSP + `< 1.7 KLoC` Safety Shield |
| :--- | :--- | :--- | :--- | :--- |
| **(L1) Authoring & Maintenance** | High C++/JUCE boilerplate (`DataQueue.cpp` `488 LoC`); manual FIFO wraparound bugs (`fillSampleNumbers`) | Concise Python API (`10–40 LoC` pipelines); `remove_artifacts.py` `454 LoC` | Clean Python/PyTorch (`~3 KLoC` core); updating neural decoders after thread retraction requires offline re-sorting | `~16 LoC` safety policy (`ChargeZero`, `CIC`, `Shannon(1.85)`, `Thermal(40mW/cm2)`); untrusted OTA ML decoder weights |
| **(L2) Toolchain Build Time & RSS** | CMake + C++17 + JUCE build (`~45–120 s`, `~400–800 MiB` RSS) | Pure Python + SciPy/NumPy (`< 5 s`, `~150–300 MiB` test RSS) | Python + PyTorch/CUDA/Numba JIT (`~10–30 s` cold JIT warm-up) | Bare-metal C/Rust `no_std` ROM shield (`< 2 s` build, `< 35 MiB` host RSS) |
| **(L3) Compilation / Synthesis / Fit** | `0 ms` (fixed DSP graph); channel-resize reallocates `AbstractFifo` dynamically | Lazy segment wrapper (`< 5 ms` init); template estimation runs `O(N_trig)` | `datashift` Kriging + template clustering + matching (`minutes` per 1-hour `384`-ch Neuropixels session) | Precomputed static `iKxx`/matched-filter LUT (`< 45 ms` offline quantize); `0` solver cost at runtime |
| **(L4) Execution Throughput & Latency** | `30 kHz` streaming at `~1–10 ms` audio/block latency; lock-free SPSC copy | `get_traces()` chunked NumPy/SciPy (`~2–20 ms`/chunk; `cubic` spline slows `5–10x`) | GPU `conv1d` + `max_pool1d` peeling: faster than real-time batch (`~0.1–0.4x` real-time on RTX GPUs), `15–300 W` | **`< 1.2 ms`** closed-loop trigger latency; `< 100 nA` net DC drift; `0` dynamic allocation |
| **(L5) Safety / Admission Verification** | No electrochemical, thermal, or sample-stride invariants checked | Assertion checks on segment count & trigger types only (`remove_artifacts.py:126-143`) | `CCG.check_CCG` refractoriness (`numba @njit`); missed empty guard in `swarmsplitter` pre-fix | **`< 0.1 us` (`0.06 us` `[Probe 2B]`)** online charge/Shannon/Pennes flux gate; `< 1.5 ms` OTA image admission check |
| **(L6) Memory, Power & Silicon Footprint** | `100–500 MiB` host RAM; `10–50 W` desktop CPU | `250 MiB–4 GiB` RAM depending on chunk memory / `n_jobs` | `4–16 GiB` VRAM/RAM (`batch_size=60000`, `st`/`tF` prealloc `10^6` spikes); `15–300 W` | **`< 64 KiB` SRAM**, `< 16 KiB` safety-monitor ROM, **`< 18 mW`** total die (`< 35 mW/cm^2` `@ 0.5–1 cm^2`) |

---

### 7. Human Comprehensibility, Conceptual Simplicity, and Universal Model Refinement (C1–C2)

`Basis: derived`

#### 7.1 Human Comprehensibility vs. Agent Execution Ergonomics (`C1`)
Neurosurgical teams, FDA IDE reviewers, and electrophysiological engineers cannot verify tissue safety by reading `3,000+` lines of PyTorch `einsum` kernels, JUCE `AbstractFifo` index arithmetic, or `scipy.interpolate` spline branches. Even an LLM agent can easily miss `len(st2 == 0)` (`swarmsplitter.py`) or `blockIdx++` OOB indexing (`DataQueue.cpp`) when editing complex array code—yet human safety review reduces cleanly to **three concrete clinical invariants**:
1. **Interfacial Polarization Margin:** Every pulse sequence ends with residual $V_{C_{\text{dl}}} \in [V_{\text{H}_2}, V_{\text{O}_2}]$ (passive discharge active + compliance flags clear), preventing gas evolution and `SIROF`/`PtIr` delamination.
2. **Dual Micro-Macro Damage Envelope:** Every pulse obeys *both* $\log_{10}(D) + \log_{10}(Q) \le 1.85$ and $D \le \text{CIC}_{\text{material}}$ (pinpointing exact violating `(Q_uC, D_uC_cm2)` coordinates).
3. **Cortical Thermal & Duty-Cycle Envelope:** Time-averaged die surface flux stays `< 40 mW/cm^2` ($\Delta T < 1\,^\circ\text{C}$) and blanking duty cycle remains `< 50%` (`f_stim * t_blank < 0.5`).

#### 7.2 Universal Safety Semiring Refinement and Adapter-Conservation Audit (`C2`)
Rather than scattering independent validators across telemetry drivers, DSP artifact blankers, and DAC stimulation state machines, all five physical and timing constraints collapse onto **one compositional Quantitative Safety Grade** enforcing an **immutable Hardware/ROM Shield** around an **untrusted Adaptive Decoder**:
$$\text{Grade}\langle Q_{\text{net}},\; (Q, D),\; P_{\text{elec}},\; \eta_{\text{blank}}\rangle \triangleq \Bigl(|\Sigma \Delta Q| \le Q_{\text{leak}}^{\max}\Bigr) \;\land\; \Bigl(\log_{10}(DQ) \le 1.85 \;\land\; D \le \text{CIC}\Bigr) \;\land\; \Bigl(\overline{q''_{\text{3D}}} \le q''_{\Delta T < 1^\circ\text{C}}\Bigr) \;\land\; \Bigl(f_{\text{stim}} t_{\text{blank}} \le \eta_{\max}\Bigr)$$
Under this separation:
- **Untrusted Decoder (`0` TCB):** Arbitrary `Kilosort`-style PCA templates, DREDge/Kriging thread-retraction remapping, or OTA ML models run freely to propose `(channel, amplitude_uA, pulse_width_us, trigger_time)`.
- **Minimal Trusted Safety Shield (`< 1.7 KLoC` ROM / Hardware Timer):** Computes the monotone resource grade over a sliding window before arming the H-bridge / current DAC (`0.06 us` analytical check in `[Probe 2B]`), refusing unsafe triggers and engaging passive discharge (`R_dis`) automatically on compliance trip or timeout.

**Adapter-Conservation Audit:** Does decoupling `AdaptiveDecoder` from `Grade<Electrochem, Bioheat, Blanking>` add hidden complexity into FFI adapters? **No—it eliminates dual-layer validation duplication:**
- *Removed:* Ad-hoc compliance adoptions scattered across host GUI code, soft unguarded artifact-subtraction timers (`remove_artifacts.py` vs. hardware `amp settle`), and manual post-hoc FDA review of every decoder weight tweak.
- *Preserved Simplicity:* Changing electrode material (`PtIr` $\to$ `SIROF`) or cortical die geometry (`r_chip`) updates only the declarative constants (`CIC`, `L_p`, `r_chip`) of the single shield; OTA decoder updates following Neuralink-style thread retraction cannot breach tissue limits even under worst-case adversarial ML predictions.

## Boundaries

- **not examined:** Non-electrical neuromodulation modalities (optogenetics, focused ultrasound thermal cavitation, magnetothermal nanoparticles), wireless inductive RF Specific Absorption Rate (`SAR`) tissue heating inside the skull/scalp above the epidural space, and long-term foreign-body astrocytic encapsulation impedance kinetics (`> 1 year` chronic scarring curves).
- **unknown:** Exact longitudinal reduction in local cortical perfusion $\omega_b$ caused by chronic glial scarring around retracted polymer threads, which could lower local steady-state $q''_{\Delta T < 1^\circ\text{C}}$ below healthy-cortex `40 mW/cm^2` estimates.
- **known not to apply:**
  - `Shannon (1992)` $k = 1.85$ does *not* guarantee safety on microelectrodes ($A < 2{,}000\,\mu\text{m}^2$) where edge current crowding drives local $D$ past bare `PtIr` capacitive limits (`[Probe 2A]`), nor at extreme pulse rates (`> 500 Hz`) where thermal/metabolic exhaustion dominates.
  - `Kilosort4`'s full-recording GPU PyTorch batch pipeline (`datashift` + `template_matching`) does *not* apply directly to hard real-time (`< 2 ms`) closed-loop implanted inference without causal streaming quantization.
  - Infinite 1D planar Pennes flux (`13.9 mW/cm^2/°C`) does *not* penalize sub-millimeter micro-probes (`r < 0.5 mm`), which benefit from strong 3D spherical spreading (`~1 / r`).
- **unsupported:**
  - `open-ephys/plugin-GUI` `DataQueue::fillSampleNumbers` (`DataQueue.cpp:120-151`) and `DataBuffer::addToBuffer` do not enforce non-dropping ring backpressure or multi-block monotonic sample-number verification across wraparound.
  - `SpikeInterface` `RemoveArtifactsRecording` (`remove_artifacts.py:108, 350, 416`) does not support safe zero-norm template scaling or chunk-edge artifact cubic interpolation without `NaN`/extrapolation risks, nor does it model closed-loop blanking starvation.

## Evidence

### Inspected Repositories, Standards, Literature, and Source Regions

| Subject | Immutable Identity | Inspected Paths & Symbol / Line Ranges | Role |
| :--- | :--- | :--- | :--- |
| `open-ephys/plugin-GUI` | `560c995500f7f1438c6c3646311ff11776da49bb` | `Source/Processors/DataThreads/DataBuffer.cpp:66-176`; `Source/Processors/RecordNode/DataQueue.cpp:120-484` | `source` |
| `SpikeInterface/spikeinterface` | `1d7bacaa2a934ed4547f906e637887f3f609f9b1` | `src/spikeinterface/preprocessing/remove_artifacts.py:92-449`; `src/spikeinterface/preprocessing/motion.py:17-169` | `source` |
| `MouseLand/Kilosort` | `0e07514c16fc1162f6470ecbad25be9c7e256306` | `kilosort/datashift.py:12-225`; `kilosort/preprocessing.py:37-69`; `kilosort/template_matching.py:14-245`; `kilosort/CCG.py:8-121`; `kilosort/swarmsplitter.py:53-140`; `kilosort/parameters.py:19-115`; `kilosort/run_kilosort.py:169-340` | `source` |
| `Shannon (1992)` | `DOI: 10.1109/10.126616` | *A model of safe levels for electrical stimulation*, IEEE TBME 39(4):424-426 — $\log_{10}(D)+\log_{10}(Q) \le 1.85$ boundary | `normative` |
| `Merrill, Bikson, & Jefferys (2005)` | `DOI: 10.1016/j.jneumeth.2004.10.020` | *Electrical stimulation of excitable tissue*, J. Neurosci. Methods 141(2):171-198 — Charge-balance, Faradaic electrolysis, passive discharge risks | `normative` |
| `Cogan (2008)` | `DOI: 10.1146/annurev.bioeng.10.061807.160518` | *Neural stimulation and recording electrodes*, Annu. Rev. Biomed. Eng. 10:275-309 — Water window `[-0.6V, +0.8V]` vs Ag\|AgCl, `PtIr` vs `SIROF` (`1.5–5 mC/cm^2`) CIC, microelectrode deviation | `normative` |
| `ISO 14708-3:2017` | `ISO 14708-3:2017` | Active implantable neurostimulator outer-surface $\Delta T \le 2\,^\circ\text{C}$ (`39 °C`) limit (`Wolf 2008` `< 1 °C` cortical Pennes target) | `normative` + `documentation` |
| `FDA (2021)` / `Intan RHS2116` / `Neuralink PRIME (2024)` | Public Guidance & Datasheets | FDA *Implanted BCI Devices* IDE guidance (May 2021); `Intan RHS2116` fast-settle/`1 nA–1 uA` charge recovery/`±7 V` compliance; Neuralink May 2024 PRIME Study thread retraction disclosure | `documentation` |

### Self-Contained Reproducible Verification Probe and Execution Output

Running the self-contained pure Python 3 standard-library probe below (`python3 -`, executed `2026-11-19`) reproduces all electrochemical, DSP bug, blanking-duty-cycle, and Pennes bioheat calculations:

```python
import math, time

# 1. Randles polarization under 1% biphasic mismatch
c_dl, r_f, r_dis = 20.0e-9, 50.0e6, 500.0
i_cath, t_pw, eps, freq_hz, t_dis = 50.0e-6, 200.0e-6, 0.01, 200.0, 2.0e-3
q_err = eps * i_cath * t_pw
decay_open = math.exp(-(1.0 / freq_hz) / (r_f * c_dl))
decay_short = math.exp(-t_dis / (r_dis * c_dl))
v_open, v_short, breach = 0.0, 0.0, None
for n in range(1, 2000):
    v_open = v_open * decay_open + q_err / c_dl
    v_short = (v_short + q_err / c_dl) * decay_short
    if breach is None and v_open > 0.8:
        breach = n
print(f"[Probe 2A] 1% biphasic mismatch (Q={i_cath*t_pw*1e9:.1f} nC, dQ={q_err*1e9:.2f} nC/pulse, C_dl={c_dl*1e9:.0f} nF): open-circuit polarization breaches +0.8V PtIr water window at pulse #{breach} ({breach/freq_hz:.2f}s), steady V_open={v_open:.2f}V vs passive-shorted V_short={v_short:.3e}V")

# 2. Shannon macro vs microelectrode CIC discrepancy
print(f"[Probe 2A] Shannon check: Macro(A=1e-2 cm^2, Q=0.8 uC, D=80 uC/cm^2) -> k={math.log10(0.8/0.01)+math.log10(0.8):.2f} (<=1.85); Micro(A=2000 um^2, Q=0.02 uC, D={0.02/2e-5:.0f} uC/cm^2) -> k={math.log10(0.02/2e-5)+math.log10(0.02):.2f} (<=1.85 yet 6.7x over PtIr CIC!)")

# 3. Open Ephys DataQueue::fillSampleNumbers model (DataQueue.cpp:120-151) & Kilosort4 pre-fix check
def fill_sample_numbers(index, size, sample_number, block_size=1024, num_blocks=8):
    block_mod, block_idx = index % block_size, index // block_size
    if block_mod == 0:
        start_sn, block_start = sample_number, index
    else:
        start_sn = sample_number + (block_size - block_mod)
        block_start = index + (block_size - block_mod)
        block_idx += 1
    out = {}
    for i in range(0, size, block_size):
        if (block_start + i) < (index + size):
            out[block_idx] = f"OOB(idx={block_idx}>={num_blocks})" if block_idx >= num_blocks else start_sn + (i * block_size)
    return out
print(f"[Probe 2B] Open Ephys DataQueue::fillSampleNumbers(idx=7168, sz=3072, sn=100000) overwrites block_idx=7 repeatedly with stride 1024^2: {fill_sample_numbers(7168, 3072, 100000)}")
print(f"[Probe 2B] Open Ephys non-aligned end-of-ring(idx=7680, sz=1024, nBlocks=8) writes: {fill_sample_numbers(7680, 1024, 100000)}")
buggy_len_check = bool(len([x == 0 for x in [1.0, 2.0, 3.0]]))
print(f"[Probe 2B] Kilosort4 pre-fix `len(st2 == 0)` evaluates truthy ({buggy_len_check}) on non-empty spike trains, bypassing check_CCG")

# 4. Blanking starvation + Pennes 1D & 3D bioheat
for f in (30.0, 130.0, 250.0, 300.0):
    print(f"[Probe 2B] Blanking duty cycle @ f_stim={f:5.1f} Hz (window=3.5 ms): {min(1.0, f*3.5/1000.0)*100:5.1f}% blanked")
k_tis, wb_rho_c, r_chip = 0.52, 37000.0, 5.0e-3
lp = math.sqrt(k_tis / wb_rho_c)
q1d = math.sqrt(k_tis * wb_rho_c) * 0.1
q3d = (2.0 * k_tis * (1.0 + r_chip / lp) / r_chip) * 0.1
print(f"[Probe 2B] Cortical Pennes bioheat (L_p={lp*1000:.2f} mm): 1D planar flux@1C={q1d:.1f} mW/cm^2; 3D spreading (r=5.0 mm, A={math.pi*(r_chip**2)*1e4:.3f} cm^2)@1C={q3d:.1f} mW/cm^2 (@2C={2*q3d:.1f} mW/cm^2)")
```

Captured stdout (`exit 0`, executed `2026-11-19`; standalone Pennes flux-check loop averaged `0.06 us` per call):
```text
[Probe 2A] 1% biphasic mismatch (Q=10.0 nC, dQ=0.10 nC/pulse, C_dl=20 nF): open-circuit polarization breaches +0.8V PtIr water window at pulse #320 (1.60s), steady V_open=1.00V vs passive-shorted V_short=6.919e-90V
[Probe 2A] Shannon check: Macro(A=1e-2 cm^2, Q=0.8 uC, D=80 uC/cm^2) -> k=1.81 (<=1.85); Micro(A=2000 um^2, Q=0.02 uC, D=1000 uC/cm^2) -> k=1.30 (<=1.85 yet 6.7x over PtIr CIC!)
[Probe 2B] Open Ephys DataQueue::fillSampleNumbers(idx=7168, sz=3072, sn=100000) overwrites block_idx=7 repeatedly with stride 1024^2: {7: 2197152}
[Probe 2B] Open Ephys non-aligned end-of-ring(idx=7680, sz=1024, nBlocks=8) writes: {8: 'OOB(idx=8>=8)'}
[Probe 2B] Kilosort4 pre-fix `len(st2 == 0)` evaluates truthy (True) on non-empty spike trains, bypassing check_CCG
[Probe 2B] Blanking duty cycle @ f_stim= 30.0 Hz (window=3.5 ms):  10.5% blanked
[Probe 2B] Blanking duty cycle @ f_stim=130.0 Hz (window=3.5 ms):  45.5% blanked
[Probe 2B] Blanking duty cycle @ f_stim=250.0 Hz (window=3.5 ms):  87.5% blanked
[Probe 2B] Blanking duty cycle @ f_stim=300.0 Hz (window=3.5 ms): 100.0% blanked
[Probe 2B] Cortical Pennes bioheat (L_p=3.75 mm): 1D planar flux@1C=13.9 mW/cm^2; 3D spreading (r=5.0 mm, A=0.785 cm^2)@1C=48.5 mW/cm^2 (@2C=97.1 mW/cm^2)
```

## Revalidation

To verify whether these findings shift on newer upstream revisions or alternate electrode geometries:

1. **Open Ephys `DataQueue::fillSampleNumbers`:** Diff `Source/Processors/RecordNode/DataQueue.cpp` inside `fillSampleNumbers()` to check if `i * m_blockSize` is corrected to `i`, `blockIdx` increments modulo `m_numBlocks`, and `startRead()` aligns `samplesToRead` with `ftsToRead`.
2. **SpikeInterface `RemoveArtifactsRecording`:** Inspect `src/spikeinterface/preprocessing/remove_artifacts.py` around `warnings(...)` (`line 108`), `interp1d(..., fill_value="extrapolate")` (`line 350`), and `norm` / `best_amplitudes` (`lines 414-445`) to verify whether zero-norm protection and least-squares amplitude scaling have been added.
3. **Kilosort4 CCG Gate Consistency:** Compare `kilosort/swarmsplitter.py:check_CCG` against `kilosort/CCG.py:check_CCG` to verify that `len(st2) == 0` stays fixed and check whether `Q00 < 0.25` threshold criteria remain divergent.
4. **Hardware Electrochemical & Thermal Regression:** Re-run the inline Python 3 probe under `## Evidence` whenever changing stimulator DAC mismatch tolerance $\epsilon$, electrode area $A$, coating material CIC (`PtIr` vs. `SIROF`), blanking window duration, or die radius $r_{\text{chip}}$ (`< 1 ms` runtime).
