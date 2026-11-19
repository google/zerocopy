# Physical Power, Electromagnetic, Remote DVFS/RAPL, and SIFA Leakage Models

## Summary

Instruction-set constant-time (`CT`) guarantees—requiring only that control flow and memory addresses be independent of secrets—do not hold across physical execution substrates where data-dependent CMOS switching activity couples into observable electrical, electromagnetic, thermal, or fault-survival channels. Five foundational invariants govern the boundary between software security proofs and silicon physics:

1. **CMOS Switching & Transition Dominance**: Dynamic switching power $P_{\text{dyn}} = \alpha C_L V_{DD}^2 f$ depends primarily on bit transitions (Hamming distance $\mathrm{HD}(v_{\text{prev}}, v_{\text{curr}}) = \mathrm{HW}(v_{\text{prev}} \oplus v_{\text{curr}})$) and secondarily on state weight ($\mathrm{HW}(v)$) and static leakage ($P_{\text{stat}} = V_{DD} I_{\text{leak}}(T)$). In sequential pipelines and shared buses (as captured in `sca-research/ELMO`), consecutive register/bus transitions cancel first-order Boolean masking identically: $\mathrm{HD}(x \oplus r, r) = \mathrm{HW}(x)$.
2. **Statistical & Profiled Distinguishers**: Non-profiled distinguishers (DPA, CPA) project traces onto hypothesized $\mathrm{HW}$/$\mathrm{HD}$ models; profiled distinguishers (multivariate Gaussian Templates and deep-learning classifiers benchmarked in `ANSSI-FR/ASCAD`) learn joint distributions over points of interest without explicit leakage-function assumptions and can absorb trace desynchronization or combine shares for higher-order leakage.
3. **Physical Proximity Is No Longer Required**: Mixed-signal RF coupling (`eurecom-s3/screaming_channels`) modulates digital switching noise onto on-die radio carriers at meter-scale distances; software energy telemetry (`PLATYPUS` via x86 RAPL) exposes power without probes; multi-tenant FPGA power-distribution-network (`PDN`) voltage drops are sensed remotely via Ring Oscillators (`RO`) and Time-to-Digital Converters (`TDC`); and dynamic voltage-frequency scaling (`FPSG-UIUC/hertzbleed`) converts constant-time power differences into **remote wall-clock timing differences**.
4. **Nonlinear DVFS Knees Leak Variance Under First-Order Masking**: Even when first-order Boolean masking equalizes the expected Hamming activity within a DVFS integration window ($\mathbb{E}[\tfrac{1}{2}(\mathrm{HW}(s \oplus r) + \mathrm{HW}(r))] = w/2$), its variance $(w - \mathrm{HW}(s))/4$ remains secret-dependent; a piecewise-clipped power-throttling curve rectifies that variance via Jensen's inequality into a systematic frequency and wall-clock shift.
5. **SIFA Defeats Classical Redundancy and Naive Masking Simultaneously**: Statistical Ineffective Fault Analysis (`SIFA`) conditions on **uncorrupted** executions where an injected biased fault had no effect on the ciphertext. Because no fault manifests at the output, classical error-detection redundancy passes silently while surviving intermediate states exhibit a secret-dependent non-uniform distribution; closing SIFA requires fault-tolerant error correction or SIFA-resistant invertible/duplicated masked gate structures.

## Applicability

This report synthesizes primary cryptographic literature and pinned upstream verification/measurement artifacts to establish the physical threat models and hardware-software contract boundaries relevant to verified cryptographic and systems software:

- **Embedded microcontrollers (ARM Cortex-M0/M3, AVR ATmega, nRF52 BLE SoCs)**: Directly characterized by `sca-research/ELMO` (3-stage Cortex-M0 instruction-triplet power regression), `ANSSI-FR/ASCAD` (ATmega8515 first-order Boolean-masked AES and STM32 affine-masked AES), and `eurecom-s3/screaming_channels` (mixed-signal Bluetooth LE SoCs).
- **General-purpose x86 CPUs with power telemetry and closed-loop DVFS**: Directly characterized by `0xhilbert/Platypus` (Linux `powercap`/RAPL energy interfaces on Intel x86) and `FPSG-UIUC/hertzbleed` (bare-metal Intel i7-9700 P-state frequency scaling under Turbo Boost / power limits). Hardware parameters (TDP caps, DVFS integration windows, microarchitectural capacitance weights) are silicon-specific; the structural contract failure—that cycle-constant-time code is not wall-clock-constant-time under active power-capped DVFS—generalizes to any processor whose closed-loop frequency controller depends on dynamic power.
- **Multi-tenant cloud FPGAs and heterogeneous SoCs**: Characterized via Zhao & Suh (IEEE S&P 2018) PDN impedance sharing; applicability requires a shared power delivery rail across logically isolated regions and permission to instantiate delay-sensitive combinational/sequential sensor fabrics.
- **Fault-protected symmetric primitives**: Characterized via Dobraunig et al. (TCHES 2018; ASIACRYPT 2018) on block ciphers with redundancy checks and masking.

Relationship among subjects: `ELMO` and `ASCAD` establish microarchitectural leakage models and profiling baselines; `Screaming Channels`, `PLATYPUS`, `Hertzbleed`, and Zhao & Suh generalize the observation channel from local probes to RF, software counters, remote wall-clock timing, and shared-PDN silicon; `SIFA` defines the orthogonal combined fault-and-statistical boundary where detection-only fault countermeasures fail.

## Findings

### 1. CMOS Power Physics and Microarchitectural Leakage Models

Basis: normative (physical circuit model) + source (`sca-research/ELMO`) + execution (Probe 1A).

Total instantaneous CMOS power consumption decomposes into three physical components:

$$P_{\text{tot}}(t) = \underbrace{\alpha(t)\, C_L\, V_{DD}^2\, f}_{\text{dynamic switching}} + \underbrace{I_{\text{sc}}(t)\, V_{DD}}_{\text{short-circuit}} + \underbrace{I_{\text{leak}}(T, \text{state})\, V_{DD}}_{\text{static leakage}}$$

where $\alpha(t)$ is the data-dependent bit-transition activity factor, $C_L$ is the switched node/bus capacitance, $V_{DD}$ is supply voltage, and $f$ is clock frequency. Three progressively richer leakage abstractions map architectural state to $P_{\text{tot}}$:

| Leakage Model | Functional Form | Physical Origin | Effect on 1st-Order Masking $(x \oplus r, r)$ |
| :--- | :--- | :--- | :--- |
| **Hamming Weight (`HW`)** | $L(v) = a \cdot \mathrm{HW}(v) + b + \varepsilon$ | Precharged buses, state-dependent static leakage | Individually uniform ($\mathbb{E}[\mathrm{HW}(x \oplus r)] = w/2$); leaks at 2nd order via centered product |
| **Hamming Distance (`HD`)** | $L(v_0, v_1) = a \cdot \mathrm{HW}(v_0 \oplus v_1) + b + \varepsilon$ | Flip-flop/register overwrites, unprecharged data buses | **Collapses order $1 \to 0$** whenever two shares transition consecutively: $\mathrm{HD}(x \oplus r, r) = \mathrm{HW}(x)$ |
| **Instruction-Triplet Regression (`ELMO`)** | Linear + pairwise bit-interaction model over $(I_{t-1}, I_t, I_{t+1})$ | 3-stage pipeline overlap, asymmetric bit-line capacitances, memory bus | Reveals hidden microarchitectural share recombinations across adjacent instructions |

Direct source inspection of `sca-research/ELMO` (`include/powermodel.h`, lines 227–319) confirms that `elmopowermodel()` models differential voltage over a sliding 3-instruction window (`previous`, `current`, `subsequent`) as a weighted sum of:
- per-bit operand weights (`Operand1[i][instructiontype]`, `Operand2[i][instructiontype]`),
- per-bit transitions (`BitFlip1[i][instructiontype]`, `BitFlip2[i][instructiontype]` comparing `previous->op{1,2}_binary[i]` with `current->op{1,2}_binary[i]`),
- instruction-type context interactions (`PrvInstr`, `SubInstr`, `HWOp{1,2}PrvInstr`, `HDOp{1,2}PrvInstr`, `HWOp{1,2}SubInstr`, `HDOp{1,2}SubInstr`),
- pairwise bit-interaction terms (`Operand{1,2}_bitinteractions_data`, `BitFlip{1,2}_bitinteractions_data`), and
- an optional memory-bus transition extension (`#ifdef MEMORY_EXTENSION`, line 309):
  `Memory_data = HDOp1PrvInstr[0][instructiontype] * hdistance(previous->readbus, current->readbus) + HDOp1PrvInstr[0][instructiontype] * hdistance(previous->writebus, current->writebus)`.

Exact enumeration over all 8-bit values and masks (Probe 1A) verifies the algebraic separation between `HW`, `HD`, and second-order moments:
- $\mathbb{E}[\mathrm{HW}(x \oplus r) \mid x] = 4.0000$ identically for all $x \in [0, 255]$.
- $\mathbb{E}[\mathrm{HD}(x \oplus r, r) \mid x] = \mathrm{HW}(x)$ (`0.0000` for `0x00`, `8.0000` for `0xFF`).
- $\mathbb{E}[(\mathrm{HW}(x \oplus r) - 4)(\mathrm{HW}(r) - 4) \mid x] = 2 - \tfrac{1}{2}\mathrm{HW}(x)$ (`+2.0000` at `0x00`, `0.0000` at `0x0F`, `-2.0000` at `0xFF`), showing why independent first-order `HW` traces still leak at second order.

### 2. Taxonomy of Physical & Statistical Side-Channel Distinguishers

Basis: normative (published mathematical definitions) + source (`ANSSI-FR/ASCAD`).

| Analysis Class | Profiling Required? | Mathematical Core | Primary Strength & Defensive Implication |
| :--- | :--- | :--- | :--- |
| **SPA** (Kocher et al., CRYPTO 1999) | No | Visual / single-trace structural differentiation | Exploits secret-dependent control flow or distinct opcodes; eliminated by ISA constant-time execution |
| **DPA** (Kocher et al., CRYPTO 1999) | No | Difference-of-means partition on target intermediate bit(s) | Recovers secret key material under additive Gaussian noise without profiling; requires masking/hiding |
| **CPA** (Brier et al., CHES 2004) | No | Sample Pearson correlation $\hat{\rho}(T_t, H_k)$ between traces $T_t$ and modeled leakage $H_k = \mathrm{HW}/\mathrm{HD}(f(p, k))$ | Maximizes signal-to-noise ratio when leakage is approximately linear in the chosen model; generalizes to higher-order centered-product combining |
| **Template Analysis** (Chari et al., CHES 2002) | Yes (open clone device) | Multivariate Gaussian likelihood $\mathcal{N}(\mathbf{t}; \boldsymbol{\mu}_v, \boldsymbol{\Sigma}_v)$ over selected Points of Interest (`POIs`) | Information-theoretically optimal under Gaussian noise; naturally captures multivariate covariance across multiple mask shares |
| **Profiled DL-SCA** (Benadjila et al., JCEN 2020; `ANSSI-FR/ASCAD`) | Yes | Supervised neural networks (MLP/CNN) approximating posterior $P(v \mid \mathbf{t})$ evaluated by guessing entropy / key rank | Convolutional layers provide shift invariance against jitter/random-delay hiding and automatically learn nonlinear multi-share recombinations without manual POI alignment |

In `ANSSI-FR/ASCAD` (`Readme.md`, lines 7–38), the community benchmark separates fixed-key (`ATMEGA_AES_v1`, first-order Boolean-masked AES on ATmega8515) from variable-key profiling and affine-masked 32-bit targets (`STM32_AES_v2`), demonstrating that profiling-to-target portability and desynchronization resistance must be evaluated on distinct keys and higher-dimensional traces.

### 3. Electromagnetic Analysis and Mixed-Signal RF Screaming Channels

Basis: normative (`doi:10.1145/3243734.3243802`) + documentation (`eurecom-s3/screaming_channels`).

Near-field Electromagnetic Analysis (`EMA`) measures localized magnetic/electric fields induced by transient on-chip current loops, yielding higher spatial selectivity than aggregate supply-rail power measurements (isolating individual buses, register files, or cryptographic co-processors).

**Screaming Channels** (Camurati et al., ACM CCS 2018; extended CHES 2020; `eurecom-s3/screaming_channels`) demonstrate that mixed-signal System-on-Chip (`SoC`) designs integrating digital CPU cores and analog RF transceivers (e.g., Bluetooth LE / Wi-Fi on Nordic nRF52 / Qualcomm-class dies) bypass the physical-proximity assumption of near-field EMA:
- **Coupling Mechanism**: Digital logic switching couples through the shared silicon substrate and common power-distribution network into the analog RF front-end (local oscillator, mixer, power amplifier), amplitude- or phase-modulating digital leakage onto the transmitted RF carrier and its clock-harmonic sidebands ($f_{\text{carrier}} \pm k \cdot f_{\text{clk}}$).
- **Architectural Implication**: The radio transmitter acts as an unintended on-chip amplifier and antenna, extending physical leakage observability from millimeters to multi-meter distances. Software-only constant-time execution is ineffective; mitigation requires hardware substrate isolation (guard rings, separate power domains/LDOs), avoiding concurrent cryptographic execution during active RF transmission, and verified higher-order masking.

### 4. Software-Readable, Shared-PDN, and Remote DVFS Power Side Channels

Basis: normative (`doi:10.1109/SP40001.2021.00031`, `doi:10.1109/SP.2018.00049`, USENIX Security 2022) + source (`FPSG-UIUC/hertzbleed`, `0xhilbert/Platypus`) + execution (Probe 1B).

Three classes of modern hardware mechanisms expose CMOS switching power to purely remote or unprivileged software observers:

| Channel | Physical Sensor / Coupling | Software / Hardware Contract Violated | Primary Defensive Mitigation |
| :--- | :--- | :--- | :--- |
| **PLATYPUS** (Lipp et al., IEEE S&P 2021) | On-chip Intel RAPL energy telemetry (`MSR_PKG_ENERGY_STATUS`, Linux `powercap` `energy_uj`) | Unprivileged OS telemetry must not reflect privileged/enclave operand weights or instruction mixes | Restrict RAPL/powercap read permissions to privileged roles (Linux kernel CVE mitigations) and coarsen/noise enclave energy accounting |
| **Cloud Multi-Tenant FPGA Power Sensors** (Zhao & Suh, IEEE S&P 2018) | Shared FPGA PDN voltage droop sensed via Ring Oscillator (`RO`) frequency drift or `TDC` carry-chain delay | Spatial logical partitioning of FPGA fabric implies electrical isolation between tenants | Bitstream DRC prohibiting combinational loops (`RO`) and unclocked delay-line sensors (`TDC`); dedicated PDN domains or active power-balancing/masking |
| **Hertzbleed** (Wang et al., USENIX Security 2022; `FPSG-UIUC/hertzbleed`) | Closed-loop CPU DVFS throttling converting $\mathrm{HW}$/$\mathrm{HD}$ power differences into P-state frequency shifts | **Cycle-count constant-time (`CT`) implies wall-clock constant-time** | Lock CPU frequency strictly below power/thermal throttling limits (disable Turbo / pin P-state), or design algorithms whose power distribution is secret-independent |

Direct inspection of `FPSG-UIUC/hertzbleed` (`README.md`, lines 18–33; `05-leakage-model-hd_hw/README.md`, lines 1–25) confirms that x86 P-state frequency scales additively with both Hamming-distance (`03-leakage-model-hd`) and Hamming-weight (`04-leakage-model-hw`) switching activity whenever the processor operates under an active power or thermal cap (`Turbo Boost` active or TDP-saturated workloads). Because wall-clock latency is $T_{\text{wall}}(s) = \int_0^N \frac{dc}{f(c; s)}$, identical architectural traces and identical cycle counts $N$ still diverge in network-observable response time whenever $\mathbb{E}[f(c; s_1)] \neq \mathbb{E}[f(c; s_2)]$.

**Second-Order DVFS-Knee Leakage Under First-Order Masking (Derived + Execution, Probe 1B)**:
First-order Boolean masking $s \mapsto (s \oplus r, r)$ makes the expected intra-window activity constant:

$$A(s, r) = \frac{1}{2}\big(\mathrm{HW}(s \oplus r) + \mathrm{HW}(r)\big) = \frac{1}{2}\mathrm{HW}(s) + \mathrm{HW}((\neg s) \land r) \implies \mathbb{E}[A(s, r)] = \frac{w}{2}.$$

However, letting $k = w - \mathrm{HW}(s)$ be the number of zero bits in $s$, $\mathrm{HW}((\neg s) \land r) \sim \mathrm{Binomial}(k, \tfrac{1}{2})$, so the variance depends linearly on the secret weight:

$$\mathrm{Var}[A(s, r)] = \frac{w - \mathrm{HW}(s)}{4}.$$

Whenever both shares execute inside the same millisecond-scale DVFS integration window near a concave/piecewise-clipped power cap $f(A) = f_{\max} - \gamma \max(0, A - P_{\text{cap}})$, Jensen's inequality guarantees $\mathbb{E}[f(A)] < f(\mathbb{E}[A])$ strictly proportionally to the upper-tail spread. Probe 1B evaluates this exact distribution for $w = 16$, $f_{\max} = 4.0\text{ GHz}$, $P_{\text{cap}} = 8.0$, $\gamma = 0.20\text{ GHz/bit}$:
- At $\mathrm{HW}(s) = 0$: $\mathrm{Var}[A] = 4.0000$, $\mathbb{E}[f] = 3.842896\text{ GHz}$, $\mathbb{E}[1/f] = 0.261311\text{ ns/cyc}$.
- At $\mathrm{HW}(s) = 8$: $\mathrm{Var}[A] = 2.0000$, $\mathbb{E}[f] = 3.890625\text{ GHz}$, $\mathbb{E}[1/f] = 0.257539\text{ ns/cyc}$.
- At $\mathrm{HW}(s) = 16$: $\mathrm{Var}[A] = 0.0000$, $\mathbb{E}[f] = 4.000000\text{ GHz}$, $\mathbb{E}[1/f] = 0.250000\text{ ns/cyc}$.

Thus, first-order software masking alone does **not** close DVFS power-to-timing channels operating at a nonlinear throttling knee; closing the boundary requires either operating in an unthrottled frequency regime (frequency pinned strictly below $P_{\text{cap}}$) or bounding higher-order intra-window switching variance (higher-order masking / dual-rail constant-power hardware).

### 5. SIFA: Statistical Ineffective Fault Analysis

Basis: normative (`doi:10.13154/tches.v2018.i3.547-572`, `ePrint 2018/357`) + execution (Probe 1C).

Classical Differential Fault Analysis (`DFA`) relies on **effective** faults that corrupt outputs; standard countermeasures duplicate computation in time/space and suppress output whenever replicas disagree. **SIFA** (Dobraunig et al., TCHES 2018; extended to masked ciphers in ASIACRYPT 2018) breaks this defense architecture through two observations:

1. **Conditioning on Ineffective Faults**: Under realistic physical fault mechanisms (voltage/clock glitching, laser/EM pulses), fault induction is biased (e.g., stuck-at-0/reset or setup-time violation favoring specific bit transitions). When an injected fault happens to leave the target intermediate value unchanged ($X' = X$), the fault is *ineffective*: the ciphertext is valid and **all fault-detection/redundancy checks pass**.
2. **Surviving-State Bias Breaks Both Redundancy and Naive Masking**: Filtering for valid (uncorrupted) ciphertexts induces a non-uniform conditional distribution $P(X = x \mid \text{ineffective})$. For a uniform 8-bit state subjected to a bit-0 reset fault with probability $p_f = 0.5$ (Probe 1C), $P(\text{ineffective}) = 0.7500$, $P(\text{bit}_0 = 0 \mid \text{ineffective}) = 2/3$, $P(\text{bit}_0 = 1 \mid \text{ineffective}) = 1/3$, yielding exact Squared Euclidean Imbalance $\mathrm{SEI} = \sum_x (P(X=x \mid \text{ineff}) - 2^{-8})^2 = 1/2304 \approx 4.34 \times 10^{-4}$ (vs. $0$ for uniform). In masked implementations (ASIACRYPT 2018), faulting a single nonlinear gate input or share still biases the joint survival probability of the unmasked state whenever fault propagation depends on the value of the other share (e.g., in an `AND` gate, faulting an operand to `0` is ineffective whenever the *other* operand is `0`).
3. **Required Countermeasure Boundary**: Error *detection* (dual-modular redundancy, parity, infective computation that suppresses faulty outputs) is structurally insufficient against SIFA because SIFA discards detected faulty executions anyway. Defending against SIFA requires **fault-tolerant error correction** (e.g., triple-modular redundancy with majority voting so single faults are corrected unconditionally regardless of data values) combined with SIFA-resistant masked gate constructions (invertible/Toffoli-style encodings where a single-share fault cannot have data-dependent ineffectiveness).

## Boundaries

- **known not to apply**: Software constant-time verification (proving secret-independence of control flow and memory addresses) does not prevent DPA/CPA, EMA/Screaming Channels, RAPL/PDN sensors, Hertzbleed DVFS timing leakage, or SIFA. Classical error-detection-only DFA countermeasures do not mitigate SIFA. First-order Boolean masking does not eliminate Hamming-distance transitions on reused storage or second-order variance rectification at nonlinear DVFS throttling knees.
- **unsupported**: `sca-research/ELMO` models the 3-stage ARM Cortex-M0 pipeline (with an optional Cortex-M3 coefficient set and basic read/write memory-bus extension) and explicitly marks unprofiled instructions (`instructiontype == 5`, `include/powermodel.h:218`); it does not model out-of-order superscalar pipelines, x86 DVFS loops, RF substrate coupling, or analog glitch propagation.
- **not examined**: Concrete analog PCB/package EM simulation, silicon-level laser fault injection physics, post-2022 non-x86 (ARM/Apple Silicon/GPU) DVFS frequency-scaling microbenchmarks, and physical oscilloscope trace acquisition on real hardware were not executed in this study.
- **unknown**: Whether hardware-level vendor power-averaging mitigations on newer x86 generations completely eliminate sub-millisecond DVFS variance rectification under worst-case multi-core TDP saturation without explicit frequency pinning remains silicon-stepping dependent and unresolved from source inspection alone.

## Evidence

### Upstream Repositories and Source Anchors
- `sca-research/ELMO` @ `7c4e2930714a498d08a1b4469acc262f58952fb8`:
  - `README.md` (3-stage Cortex-M0 Thumbulator pipeline emulator, statistical triplet model building, memory extension).
  - `include/powermodel.h`: `hwpowermodel()` (lines 76–171), `elmopowermodel()` (lines 177–365), unprofiled instruction fallback `instructiontype == 5` (lines 218–225), `HW`/`HD`/bitflip/triplet terms (lines 228–285), `MEMORY_EXTENSION` `readbus`/`writebus` `hdistance` terms (lines 308–319).
- `eurecom-s3/screaming_channels` @ `5b04f0a89c332a2307e90ce25a85946e5ff78953`:
  - `README.md` (mixed-signal radio transceiver side-channel scope, CCS 2018 & CHES 2020 artifacts).
- `FPSG-UIUC/hertzbleed` @ `9cfdf955245e8e1673bb5c6cbee31f4424586ca4`:
  - `README.md` (lines 1–58: Intel i7-9700 setup, Turbo Boost vs base-frequency P-state cap, experiment suite `01`–`09`).
  - `05-leakage-model-hd_hw/README.md` (lines 1–30: HD/HW additivity verification for CPU frequency and energy).
- `ANSSI-FR/ASCAD` @ `5d0086353269fe03ebf447e8a7ae85a80d071c56`:
  - `Readme.md` (lines 1–55: ATmega8515 first-order Boolean-masked AES fixed/variable-key and STM32 affine-masked AES benchmarks for TensorFlow 2 DL-SCA).
- `0xhilbert/Platypus` @ `f7326a85f27937d5a97a125ecc7b5818586c579f`:
  - `README.md` (Linux `powercap` `/sys/class/powercap/intel-rapl:0/energy_uj` interface).

### Peer-Reviewed Literature
- Kocher, Jaffe, Jun, *Differential Power Analysis*, CRYPTO 1999, `doi:10.1007/3-540-48405-1_25`.
- Chari, Rao, Rohatgi, *Template Attacks*, CHES 2002, `doi:10.1007/3-540-36400-5_3`.
- Brier, Clavier, Olivier, *Correlation Power Analysis with a Leakage Model*, CHES 2004, `doi:10.1007/978-3-540-28632-5_2`.
- McCann, Oswald, Whitnall, *Towards Practical Tools for Side Channel Aware Software Engineering: 'Grey Box' Modelling for Instruction Leakages*, USENIX Security 2017.
- Zhao, Suh, *FPGA-Based Remote Power Side-Channel Attacks*, IEEE S&P 2018, `doi:10.1109/SP.2018.00049`.
- Camurati, Poeplau, Muench, Hayes, Francillon, *Screaming Channels: When Electromagnetic Side Channels Meet Radio Transceivers*, ACM CCS 2018, `doi:10.1145/3243734.3243802`.
- Dobraunig, Eichlseder, Korak, Mangard, Mendel, Primas, *SIFA: Exploiting Ineffective Fault Inductions on Symmetric Cryptography*, TCHES 2018(3):547–572, `doi:10.13154/tches.v2018.i3.547-572`.
- Dobraunig, Eichlseder, Groß, Mangard, Mendel, Primas, *Statistical Ineffective Fault Attacks on Masked AES with Fault Countermeasures*, ASIACRYPT 2018, `ePrint 2018/357`.
- Benadjila, Prouff, Strullu, Cagli, Dumas, *Deep Learning for Side-Channel Analysis and Introduction to ASCAD Database*, JCEN 2020, `doi:10.1007/s13389-019-00220-8`.
- Lipp, Kogler, Oswald, Schwarz, Easdon, Canella, Gruss, *PLATYPUS: Software-based Power Side-Channel Attacks on x86*, IEEE S&P 2021, `doi:10.1109/SP40001.2021.00031`.
- Wang, Paccagnella, He, Shacham, Fletcher, Kohlbrenner, *Hertzbleed: Turning Power Side-Channel Attacks Into Remote Timing Attacks on x86*, USENIX Security 2022.

### Analytical Micro-Probe Execution (2026-11-19, Python 3)
Executed standalone analytical probe verifying exact `HW`/`HD`/2nd-order moments (Probe 1A), exact 16-bit DVFS-knee Jensen shift under 1st-order Boolean masking (Probe 1B), and exact SIFA bit-reset conditional state bias and SEI (Probe 1C):
```text
=== Probe 1A: 1st-Order Boolean Masking HW vs HD Moments (8-bit, exact) ===
E[HW(x^r)|x=0x00] = 4.0000, E[HW(x^r)|x=0xFF] = 4.0000
E[HD(x^r, r)|x=0x00] = 0.0000, E[HD(x^r, r)|x=0xFF] = 8.0000
E[(HW(x0)-4)(HW(x1)-4)|x=0x00] = +2.0000 (expected +2.0)
E[(HW(x0)-4)(HW(x1)-4)|x=0x0F] = +0.0000 (expected  0.0)
E[(HW(x0)-4)(HW(x1)-4)|x=0xFF] = -2.0000 (expected -2.0)

=== Probe 1B: Exact DVFS Knee Frequency Shift Under 1st-Order Masking (w=16) ===
HW(s)= 0: E[A]=8.0000, Var[A]=4.0000 (exact k/4=4.0000), E[f]=3.842896 GHz, E[1/f]=0.261311 ns/cyc
HW(s)= 8: E[A]=8.0000, Var[A]=2.0000 (exact k/4=2.0000), E[f]=3.890625 GHz, E[1/f]=0.257539 ns/cyc
HW(s)=16: E[A]=8.0000, Var[A]=0.0000 (exact k/4=0.0000), E[f]=4.000000 GHz, E[1/f]=0.250000 ns/cyc

=== Probe 1C: Exact SIFA Ineffective-Fault Conditional Bias (8-bit, bit-0 reset p_f=0.5) ===
P(ineffective) = 0.7500
P(bit0=0 | ineffective) = 0.6667, P(bit0=1 | ineffective) = 0.3333
Exact SEI = 0.00043403 (uniform = 0.0; ratio vs 1/256^2 = 28.4444)
```

## Revalidation

1. **Pin & Diff Upstream Artifacts**: Run `git ls-remote https://github.com/<owner>/<repo>.git HEAD` on `sca-research/ELMO`, `eurecom-s3/screaming_channels`, `FPSG-UIUC/hertzbleed`, `ANSSI-FR/ASCAD`, and `0xhilbert/Platypus`; diff `ELMO/include/powermodel.h` (`elmopowermodel` and `MEMORY_EXTENSION`) if checking newer Cortex-M leakage model revisions.
2. **Re-run Exact Mathematical Invariant Checks**: Re-execute the deterministic Python 3 standard-library probe below (`python3 - <<'EOF' ... EOF`) to verify `HW`/`HD` cancellation, DVFS-knee variance rectification, and SIFA conditional SEI:
```python
import math
hw = lambda x: x.bit_count()
assert all(sum(hw(x ^ r) for r in range(256)) / 256 == 4.0 for x in range(256))
assert all(sum(hw((x ^ r) ^ r) for r in range(256)) / 256 == hw(x) for x in range(256))
# DVFS knee (w=16, f_max=4.0, P_cap=8.0, slope=0.2)
ef0 = sum((math.comb(16, j) / 2**16) * (4.0 - 0.2 * max(0.0, j - 8.0)) for j in range(17))
ef16 = 4.0
assert ef0 < ef16 and abs(ef0 - 3.8428955078125) < 1e-12
# SIFA bit-0 reset (p_f=0.5)
p_ineff = 0.5 + 0.5 * 0.5
assert abs((0.5 / p_ineff) - 2/3) < 1e-12
print("revalidation ok")
```
3. **Target Silicon Revalidation**: For any new CPU stepping, FPGA cloud provider, or mixed-signal SoC, revalidation requires direct hardware telemetry checks (confirming RAPL/powercap privilege boundaries, testing whether pinned non-Turbo P-states keep frequency invariant under worst-case synthetic `HW`/`HD` workloads, and checking FPGA bitstream DRC against combinational RO/TDC primitives); purely static software analysis cannot revalidate physical substrate assumptions.
