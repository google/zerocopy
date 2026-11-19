# Energy-, Thermal-, and Brownout-Safe Compilation and DVFS Power Side Channels

## Summary

Compilers, static Worst-Case Execution Time (WCET) analyzers, and constant-time cryptographic verifiers overwhelmingly idealize physical processors as constant-frequency, zero-Joule, infinite-current-supply machines. Physical CMOS silicon violates all three assumptions simultaneously, coupling energy, temperature, clock frequency, and data values across the ISA boundary in ways that silently break both **real-time timing proofs** and **constant-time security proofs**:

1. **WCET vs. WCEC divergence and peak-current brownouts**: Total energy $E = \int \big(\alpha C V^2 f + V I_{\text{leak}}(T) + P_{\text{periph}}\big)\,dt$ and instantaneous peak power $P_{\max}$ (plus inductive voltage droop $V_{\text{droop}} = L\,dI/dt + IR$) do **not** align with cycle count. As verified in our executable physical probe, a cache-miss-bound CFG path maximizes WCET while a shorter compute-dense SIMD + peripheral-TX path simultaneously maximizes Worst-Case Energy Consumption (WCEC) and triggers instantaneous brownout violations (`> 2.0 W`). Furthermore, exponential thermal leakage $I_{\text{leak}}(T)$ shifts the energy-optimal DVFS frequency upward from `0.4 GHz` at `25 C` (**pace-to-idle**) to `0.8 GHz` at `85 C` (**race-to-sleep**) while converting previously safe `1.2 GHz` execution (`1.93 W`) into a thermal-leakage brownout (`2.20 W`).
2. **Energy-aware type systems (`Energy Types`, `ENT`), static WCEC (`llvm-energy`, `Wägemann`), and brownout-safe compilation (`Alpaca`)**: Phased type systems (`Energy Types`, OOPSLA 2012; `ENT`, PLDI 2017) enforce phase-based non-interference and mixed static/dynamic energy modes; static WCEC analysis (`Jayaseelan et al. 2006`, `Wägemann et al. 2015`, `Grech et al. 2015`) requires modeling both inter-instruction switching state and stateful peripheral power modes; and intermittent-execution compilers (`Alpaca`, OOPSLA 2017) eliminate write-after-read (WAR) non-volatile memory corruption across sudden power-loss brownouts via static task privatization rather than full-RAM checkpointing.
3. **Thermal throttling and DVFS invalidating static WCET**: Static cycle-level WCET bounds assume a fixed clock $f$. Dynamic thermal/power throttling (`PROCHOT`, `RAPL PL1/PL2`, `AVX-512` power licenses, Arm thermal governors) drops $f(t)$ unpredictably at millisecond scales, causing deadline misses even when cycle count is invariant—and scaling memory-bound vs. compute-bound paths non-linearly (`1.30x` vs. `2.50x` under a `2.50x` clock drop in our probe) because DRAM latency stays constant in nanoseconds.
4. **DVFS power side channels (`PLATYPUS`, `Hertzbleed`, `Collide+Power`, `Hot Pixels`) breaking constant-time verification (`Jasmin`)**: Even when software power meters (`Intel RAPL`, exploited by `PLATYPUS`, IEEE S&P 2021) are restricted to root **and** cryptographic code passes strict formal constant-time verification (`Jasmin` `ct_checker_forward.ml`, enforcing public branches, public memory indices, and no secret `div`/`mod`), data-dependent CMOS switching power—both **Hamming distance (`HD`)** and **Hamming weight (`HW`)** of operands in strictly cycle-constant instructions (`shlx`/`shrx`, `or`)—modulates CPU frequency under TDP/thermal caps (`Hertzbleed`, USENIX Security 2022). In our closed-loop TDP probe, a `4.5%` dynamic capacitance shift over a strictly cycle-constant `4e8`-cycle decapsulation induces a `106.4 MHz` steady-state frequency shift and a `2.254 ms` (`2.48%`) wall-clock leak—recoverable remotely with `100.0%` accuracy (`mean Welch t = 6.78`) in `40` samples/class through `1.5 ms` network jitter. Eliminating power/DVFS leakage requires hardware frequency pinning or algorithmic masking hardened against microarchitectural pipeline-register transitions (`Rosita` / `ELMO`, NDSS 2021).

## Applicability

This report synthesizes primary physics/architecture literature, verified compiler/security tool source code, and executable numerical probes across four tightly coupled domains:

- **Constant-time verification vs. physical power/DVFS leakage**: Compares the formal constant-time predicate directly inspected in `jasmin-lang/jasmin` (`5741d17e3134f5b3b110e5e53494704d6d54f7c7`, `compiler/src/ct_checker_forward.ml` and `sct_checker_forward.ml`) against real x86 DVFS leakage microbenchmarks and remote SIKE exploits in `FPSG-UIUC/hertzbleed` (`9cfdf955245e8e1673bb5c6cbee31f4424586ca4`), cross-domain shared-component collision attacks in `IAIK/CollidePower` (`edd8b4a82d47c9bd518844313acf9a1f86e164e3`), `RAPL` attacks (`PLATYPUS`, IEEE S&P 2021), ARM/GPU DVFS/compression attacks (`Hot Pixels`, USENIX Security 2023; `GPU.zip`, IEEE S&P 2024), and leakage-emulation-driven assembly rewriting in `0xADE1A1DE/Rosita` (`d41621879dc2a1faa2c21600967ab2247d3de69d`).
- **Energy-aware languages, static WCEC, and brownout/intermittent compilation**: Connects foundational silicon energy models (`Tiwari et al. 1994`; `Horowitz 2014`) to `Energy Types` (`OOPSLA 2012`), `ENT` (`PLDI 2017`), static WCEC (`Jayaseelan et al. 2006`; `Wägemann et al. 2015`), LLVM IR cost-relation energy inference inspected in `nevillegrech/llvm-energy` (`52809feca6c18e973099accaf05bf8f87671126d`, `inferCR.py`), and intermittent-power compilation inspected in `CMUAbstract/alpaca-oopsla2017` (`a979300cb51409a89b7a776ead8fe50b50711bfd`).

**Scope constraints:** `Hertzbleed` source artifacts specifically target bare-metal x86-64 CPUs (Intel Core/Xeon with Turbo Boost / P-state TDP throttling, AMD Ryzen/EPYC with Precision Boost, and Ampere Altra `CVE-2022-35888`); `Rosita` targets 32-bit Arm Cortex-M0 Thumb assembly characterized by `ELMO` power coefficients (`coeffs.txt`); `Alpaca` targets energy-harvesting non-volatile FRAM microcontrollers (`TI MSP430` / `WISP`). Derived physical equations generalize across CMOS architectures, whereas concrete MHz/mW numbers depend on process node, cooling envelope, voltage-frequency curve, and power-management firmware.

## Findings

### 1. CMOS Power, Energy, Inter-Instruction Switching, and Brownout Physics

**Basis:** normative / documentation (`Tiwari et al., ICCAD/TVLSI 1994`, `Horowitz, ISSCC 2014`) + derived + execution (`probe_energy_dvfs.py`).

A processor's instantaneous power draw $P(t)$ and total task energy $E$ decompose into three physically distinct components whose dependence on voltage $V$, clock frequency $f$, die temperature $T$, and data bit-patterns drives every compiler and security anomaly below:

$$P(t) = \underbrace{\alpha(I_t, I_{t-1}, D_t, D_{t-1}) \cdot C_{\text{eff}} \cdot V(f)^2 \cdot f}_{\text{Dynamic switching power } P_{\text{dyn}}} + \underbrace{V(f) \cdot I_{\text{leak}}(V, T)}_{\text{Static leakage power } P_{\text{leak}}} + \underbrace{P_{\text{periph}}(S_{\text{dev}}(t))}_{\text{Off-core / DRAM / RF peripherals}}$$

1. **Circuit-State & Data-Dependent Switching (`Tiwari, Malik, Wolfe 1994`, DOI `10.1109/ICCAD.1994.629825` & `10.1109/92.335012`)**:
   - Instruction energy is **non-compositional**: executing instruction $I_t$ immediately after $I_{t-1}$ consumes $E(I_t \mid I_{t-1}) = B(I_t) + O(I_{t-1}, I_t) + \Delta_{\text{data}}(D_{t-1}, D_t)$, where $B(I_t)$ is the instruction base cost, $O(I_{t-1}, I_t)$ is the inter-instruction circuit-state switching overhead (activating/deactivating decode/functional-unit paths), and $\Delta_{\text{data}}$ depends on both the **Hamming weight (`HW`)** of operand values (precharged buses, register-file sense amplifiers, carry-chain propagation) and the **Hamming distance (`HD`)** between consecutive values written to the same physical register, bus, or pipeline latch (`HW(x ^ y)`).
2. **Data-Movement vs. ALU Energy Asymmetry (`Horowitz, ISSCC 2014`, DOI `10.1109/ISSCC.2014.6757323`)**:
   - At 45 nm CMOS (Horowitz's canonical architectural energy table), a 32-bit integer `ADD` costs $\approx 0.1\text{ pJ}$ and a 32-bit `FP MULT` costs $\approx 3.7\text{ pJ}$, whereas reading 64 bits from an 8 KiB SRAM costs $\approx 10\text{ pJ}$, from a 1 MiB SRAM costs $\approx 100\text{ pJ}$, and from off-chip DRAM costs $\approx 1.3\text{–}2.6\text{ nJ}$—a **$\sim 10^3\times$ to $10^4\times$ energy ratio** between DRAM access and ALU arithmetic. Consequently, compiler optimizations that reduce instruction count at the cost of increased spill/fill or cache misses routinely *increase* total energy.
3. **Peak-Current Voltage Droop ($dI/dt$) and Power-Supply Brownouts**:
   - Power delivery networks (PDNs) exhibit finite inductance $L$ and resistance $R$. Sudden simultaneous activation of wide SIMD/vector pipelines, DMA engines, or radio transceivers induces a supply voltage droop:
     $$\Delta V_{\text{droop}}(t) = L \frac{dI}{dt} + I(t) R$$
   - On high-performance x86 CPUs, avoiding PDN voltage emergencies forces hardware **AVX-512 power-license throttling** (dropping core frequency across License 0 / License 1 / License 2 states whenever wide 256-bit/512-bit heavy FMA instructions enter the pipeline, with millisecond-scale hysteresis). On battery-, solar-, or RF-harvesting embedded devices (e.g., medical implants, cubesats, `WISP` tags), exceeding the capacitor/regulator instantaneous power envelope $P_{\max}(T)$ drops $V_{\text{dd}}$ below the brownout detector threshold $V_{\text{BOD}}$, triggering an immediate **hardware reset** that wipes volatile SRAM and registers.

---

### 2. Energy-Aware Type Systems, Static WCEC, and Brownout-Safe Compilation

**Basis:** normative (`Energy Types`, `ENT`, `Jayaseelan 2006`, `Wägemann 2015`, `Grech 2015`, `Alpaca 2017`) + source (`nevillegrech/llvm-energy`, `CMUAbstract/alpaca-oopsla2017`) + execution (`probe_energy_dvfs.py`).

#### 2.1 Phased and Mixed Energy Type Systems (`Energy Types` & `ENT`)
- **`Energy Types` (`Cohen, Zhu, Emgin, Liu, OOPSLA 2012`, DOI `10.1145/2384616.2384676`)**:
  - Introduces **energy phases** (`modes`, ordered in a finite energy-consumption lattice such as $\text{low} \preceq \text{mid} \preceq \text{high}$) as first-class type qualifiers on classes, methods, and object references (`Type@mode`), paired with explicit phase blocks (`phases { ... }`) that map to runtime DVFS/approximation settings.
  - **Key Soundness Invariant — Data-Phase Decoupling (Non-Interference)**: Objects allocated or mutated in a high-energy precision mode cannot silently leak into low-energy execution contexts without explicit mode-aware conversion, and low-energy phases cannot invoke methods typed for higher-energy modes without an explicit checked mode transition. Type soundness guarantees that execution inside a phase bounded by mode $m$ never performs unannotated operations exceeding mode $m$'s energy specification.
- **`ENT` (`Canino & Liu, PLDI 2017`, DOI `10.1145/3062341.3062356`)**:
  - Addresses the rigidity of purely static energy types when runtime energy conditions (battery level, thermal headroom, ambient harvesting rate) vary dynamically.
  - Introduces **mixed static/dynamic mode typechecking**: static mode qualifiers (`mode`) coexist with a dynamic mode wildcard (`?`) and a runtime mode-case dispatch construct (`mcase`) plus **attributed mode snapshots** (`snapshot`), bridging proactive compile-time mode guarantees with adaptive runtime energy-state recovery while preserving static type safety across mode boundaries.

#### 2.2 Static Worst-Case Energy Consumption (`WCEC`) and `WCET != WCEC`
- **Implicit Path Enumeration (`IPET`) for WCEC (`Jayaseelan, Mitra, Li, RTAS 2006`, DOI `10.1109/RTAS.2006.17`; `Wägemann et al., ECRTS 2015`, DOI `10.1109/ECRTS.2015.17`)**:
  - Classical WCET uses ILP/IPET over a Control-Flow Graph (CFG) to maximize $\sum_{b} c_b \cdot x_b$ subject to flow-conservation and loop-bound constraints.
  - Extending IPET to WCEC ($\max \sum_b e_b \cdot x_b + \sum_{(u,v)} e_{u\to v} \cdot x_{u\to v}$) faces two fundamental complications highlighted by `Wägemann et al.`:
    1. **Stateful Peripheral Coupling**: Turning on an external device (radio TX, sensor ADC, flash write pump) in basic block $b_1$ and turning it off in $b_2$ changes the *per-cycle power draw of every intervening block*—requiring product-automaton CFG expansion across device power states (`SysWCEC` / explicit power-state graphs) before ILP solving.
    2. **Leakage & Switching Coupling**: Because static leakage energy scales with wall-clock time ($P_{\text{leak}} \cdot \Delta t$) while dynamic switching scales with instruction activity and operand transitions, the path maximizing WCEC is generally **distinct** from the path maximizing WCET.
- **Symbolic LLVM IR Cost-Relation Energy Analysis (`nevillegrech/llvm-energy @ 52809feca6c18e973099accaf05bf8f87671126d`, `Grech et al., SCOPES 2015`, DOI `10.1145/2764967.2764974`)**:
  - Direct inspection of `llvm-energy/inferCR.py` (lines 37–198) reveals how symbolic input-parameterized energy bounds are extracted from LLVM IR without executing the binary on every input size:
    - `PubsSolver.addrel()` (`lines 178-194`) emits one cost-relation recurrence per LLVM basic block: `eq(block(formals), energy, [continuations], [conditions]).`, transforming integer division guards (`transformdivision`, lines 157–176) into linear inequalities (`>=`, `*`) solvable by the `PUBS` recurrence solver to obtain closed-form symbolic energy expressions in terms of input arguments (`In0`, `In1`, ...).
    - Block energy costs come from two paths: `getenergy_()` (`lines 37-47`), which reads ISA-level measured/mapped per-block energy from a compiler-generated JSON mapping (after subtracting a fixed `phi`-node artifact), or a fallback static LLVM-opcode heuristic `getenergy()` (`lines 49-84`, using `armdef = 13` scaled by `5x` for `div/rem`, `3x` for `ret`, `2x` for `load/store`).
    - **Source-level defect observed (`inferCR.py:56-60`)**: In the fallback `getenergy()` loop, `prev = op` is assigned at line 57 *before* `if op == 'add' and prev == 'mul':` at line 58, making the multiply-accumulate (`MAC`) energy-coalescing rule dead code in the heuristic fallback (though bypassed when external ISA JSON mappings are supplied via `getenergy_()`). Moreover, `inferCR.py` models neither operand Hamming weight/distance nor temperature-dependent leakage power.

#### 2.3 Quantitative Demonstration: `WCET != WCEC`, Temperature-Driven Optimal DVFS Crossover, and Thermal-Leakage Brownout
**Basis:** execution (`/tmp/probe_energy_dvfs.py`, Part 1) + derived.

Consider an embedded controller CFG with two mutually exclusive paths:
- **Path A (Memory-Bound / Cache-Miss Stall)**: `600` core cycles (`C_eff = 0.35 nF`) + `1200 ns` fixed physical DRAM latency (`15` LLC misses at `2.0 nJ`/miss = `30 nJ`), no radio TX.
- **Path B (Compute-Dense SIMD + Radio TX Burst)**: `900` dense SIMD cycles (`C_eff = 1.60 nF`, zero DRAM misses) with an active `120 mW` RF transceiver.
- **Leakage & Brownout Model**: $P_{\text{leak}}(V, T) = 0.04\,V \cdot e^{0.035(T - 25^\circ\text{C})}$ (`40 mW` at `1 V, 25 C`; `327 mW` at `1 V, 85 C`), instantaneous brownout power cap $P_{\text{cap}} = 2.0\text{ W}$.

Executing `probe_energy_dvfs.py` across 5 DVFS operating points at $25^\circ\text{C}$ and $85^\circ\text{C}$ yields:

| Operating Point `(f, V)` | Temp $T$ | Path A Time / Energy / $P_{\text{peak}}$ | Path B Time / Energy / $P_{\text{peak}}$ | Path B Brownout? | WCET Path | WCEC Path |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `0.4 GHz, 0.70 V` | `25 C` | `2.700 us` / **`0.208 uJ`** / `0.10 W` | `2.250 us` / **`1.039 uJ`** / `0.46 W` | Safe | **A** | **B** |
| `0.8 GHz, 0.82 V` | `25 C` | `1.950 us` / `0.235 uJ` / `0.22 W` | `1.125 us` / `1.140 uJ` / `1.01 W` | Safe | **A** | **B** |
| `1.2 GHz, 0.96 V` | `25 C` | `1.700 us` / `0.289 uJ` / `0.43 W` | `0.750 us` / `1.446 uJ` / `1.93 W` | **Safe** (`1.93 W`) | **A** | **B** |
| `1.6 GHz, 1.10 V` | `25 C` | `1.575 us` / `0.353 uJ` / `0.72 W` | `0.562 us` / `1.835 uJ` / `3.26 W` | **BROWNOUT** | **A** | **B** |
| `2.0 GHz, 1.25 V` | `25 C` | `1.500 us` / `0.433 uJ` / `1.14 W` | `0.450 us` / `2.327 uJ` / `5.17 W` | **BROWNOUT** | **A** | **B** |
| `0.4 GHz, 0.70 V` | `85 C` | `2.700 us` / `0.750 uJ` / `0.30 W` | `2.250 us` / `1.490 uJ` / `0.66 W` | Safe | **A** | **B** |
| `0.8 GHz, 0.82 V` | `85 C` | `1.950 us` / **`0.694 uJ`** / `0.46 W` | `1.125 us` / **`1.405 uJ`** / `1.25 W` | Safe | **A** | **B** |
| `1.2 GHz, 0.96 V` | `85 C` | `1.700 us` / `0.757 uJ` / `0.70 W` | `0.750 us` / `1.652 uJ` / **`2.20 W`** | **BROWNOUT!** | **A** | **B** |

Three compiler-design consequences follow directly from this table:
1. **Path Inversion**: At every operating point and temperature, **WCET is achieved by Path A** while **WCEC is achieved by Path B** (up to $5.4\times$ higher energy than Path A despite executing in $3.3\times$ less wall-clock time at `2.0 GHz`).
2. **Temperature-Driven Optimal-Frequency Shift**: At `25 C`, running slower (`0.4 GHz`, **pace-to-idle**) minimizes energy for both paths; at `85 C`, exponential leakage growth makes `0.4 GHz` *worse* than `0.8 GHz` (`0.750 uJ -> 0.694 uJ` for Path A; `1.490 uJ -> 1.405 uJ` for Path B), forcing a shift toward **race-to-sleep**.
3. **Thermal-Leakage Brownout Coupling**: At `1.2 GHz`, Path B is brownout-safe at `25 C` (`1.93 W <= 2.0 W`) yet browns out at `85 C` (`2.20 W > 2.0 W`) purely due to elevated static leakage—proving that brownout-safe compilation requires temperature-parameterized peak-power envelopes $P_{\max}(f, T)$, not room-temperature measurements.

#### 2.4 Brownout Recovery & Intermittent Execution Compilation (`Alpaca`)
When brownouts cannot be prevented (energy-harvesting sensors powered by microfarad capacitors), naive reboot-and-retry corrupts non-volatile memory (`FRAM`/`MRAM`) through **Write-After-Read (`WAR`) idempotency violations**: if a task reads global NVM variable `x`, updates `x = x + 1`, and suffers a brownout before committing the task boundary, restarting the task re-reads the *already incremented* `x`.
- **`Alpaca` (`Maeng, Colin, Lucia, OOPSLA 2017`, DOI `10.1145/3133920`; `CMUAbstract/alpaca-oopsla2017 @ a979300cb51409a89b7a776ead8fe50b50711bfd`)**: Replaces expensive runtime full-state checkpoints (`DINO`) and manual channel plumbing (`Chain`) with an LLVM compiler pass (`ext/alpaca/LLVM`) targeting `MSP430`/`WISP` that statically identifies every non-volatile variable involved in a `WAR` dependence inside a task, privatizes it into a task-local buffer on first access, and emits a lightweight two-phase atomic commit list at task exit—guaranteeing crash-consistent forward progress across arbitrary brownouts provided each task's WCEC fits within one capacitor charge cycle.

---

### 3. Thermal Throttling and DVFS Breaking Static WCET Bounds

**Basis:** derived + execution (`probe_energy_dvfs.py`) + documentation.

Static WCET tools compute cycle bounds $C_{\text{wc}}$ and convert to wall-clock time via $T_{\text{wc}} = C_{\text{wc}} / f_{\text{const}}$. Modern hardware power management breaks this formula in three distinct ways:
1. **Reactive Thermal & Power-Cap Throttling**: Package power caps (`Intel RAPL PL1/PL2` sliding time windows $\tau$), thermal control circuits (`PROCHOT#` / `TCC` activation temperature), and OS/firmware thermal governors dynamically lower clock frequency $f(t)$ below nominal base frequency whenever cumulative workload heat exceeds dissipation capacity. Because $T_{\text{wall}} = \int_0^{C_{\text{wc}}} \frac{dc}{f(t)}$, even a 100% cycle-deterministic kernel misses its deadline as soon as $f(t) < f_{\text{assumed}}$.
2. **Non-Linear Memory-vs.-Compute Stretch Under DVFS**: In our probe above, dropping frequency by $2.50\times$ (`2.0 GHz -> 0.8 GHz`) stretches compute-bound Path B by exactly **`2.50x`** (`0.450 us -> 1.125 us`), whereas memory-bound Path A stretches by only **`1.30x`** (`1.500 us -> 1.950 us`) because off-chip DRAM latency (`1200 ns`) stays invariant in physical nanoseconds—yet still **violates** a `1.800 us` deadline calibrated at `2.0 GHz`! On out-of-order superscalar pipelines, changing the ratio of CPU cycle period to DRAM latency also alters memory-level parallelism (MLP) overlap and prefetcher timing, creating **DVFS timing anomalies** where running faster does not monotonically tighten every microarchitectural stall.
3. **Cross-Core Voltage/Frequency Domain Coupling**: Most COTS multicore chips share a single voltage regulator (VR) or clock domain across a core cluster (or entire socket). A non-real-time AVX-512 or high-activity co-runner on Core 1 can push the shared socket into `PL1` or `PROCHOT` throttling, dragging down the clock frequency of a real-time task on Core 0 even when Core 0 is completely isolated in LLC (`CAT`/`MPAM`), DRAM banks (`PALLOC`), and bandwidth (`MemGuard`)!

---

### 4. Power and DVFS Side Channels: `PLATYPUS`, `Hertzbleed`, `Collide+Power`, and `Hot Pixels`

**Basis:** normative (peer-reviewed security disclosures & CVEs) + source (`FPSG-UIUC/hertzbleed`, `IAIK/CollidePower`, `jasmin-lang/jasmin`, `0xADE1A1DE/Rosita`) + execution (`probe_energy_dvfs.py`).

#### 4.1 Threat-Model Evolution: From Physical Probes to Remote Cycle-Constant Timing Oracles

| Attack / Framework | Venue & Primary ID | Measurement Oracle Required | Target Property Leaked | Works When RAPL Is Root-Only? | Defeats Constant-Time (`Jasmin` CT)? | Primary Evidence Examined |
| :--- | :--- | :--- | :--- | :---: | :---: | :--- |
| **PLATYPUS** (`Lipp et al.`) | IEEE S&P 2021 (`10.1109/SP40001.2021.00063`, `CVE-2020-8694/8695/12912`) | Unprivileged `Intel RAPL` energy counters (`sysfs` / `MSR_PKG_ENERGY_STATUS`) | Instruction & operand `HW`/`HD` power: AES-NI keys, SGX enclave secrets, KASLR | **No** (mitigated by root-only `sysfs` + SGX energy filtering) | **Yes** (leaks operand `HW`/`HD` directly) | Crossref + CVE advisories |
| **Hertzbleed** (`Wang et al.`) | USENIX Sec 2022 (`ISBN 978-1-939133-31-1`) & IEEE Micro 2023 (`10.1109/MM.2023.3274619`, `CVE-2022-24436/23823/35888`) | **Remote wall-clock execution time** (zero power-meter access! Driven by hardware TDP/thermal DVFS!) | Operand `HD` & `HW` -> frequency drop -> remote key extraction (`CIRCL` / `pqcrypto-sidh` SIKE), timer-free KASLR & covert channel | **Yes** (uses no RAPL at all for remote timing) | **Yes** (breaks strictly cycle-constant code!) | `FPSG-UIUC/hertzbleed @ 9cfdf955...` (`01..09`) |
| **Collide+Power** (`Kogler et al.`) | USENIX Sec 2023 (`ISBN 978-1-939133-37-3`) | RAPL or Hertzbleed frequency scaling | **Actual inaccessible victim data values** (not just metadata!) via `HD(victim_word, attacker_word)` collisions in shared L1/L2/memory buffers (`MDS-Power`, `Meltdown-Power`) | **Yes** (when paired with Hertzbleed channel) | **Yes** (leaks data from cross-process/kernel buffers) | `IAIK/CollidePower @ edd8b4a8...` (`README.md`, `analyze/power.py`) |
| **Hot Pixels** (`Taneja et al.`) | USENIX Sec 2023 | Frequency/power/thermal telemetry or JS rendering timing on GPUs & ARM SoCs (Apple M1/M2, Qualcomm, NVIDIA, AMD) | Cross-origin pixel stealing & browsing history via DVFS triangle (Frequency–Power–Temperature) | **Yes** (on ARM SoCs & GPUs without x86 RAPL) | **Yes** (data-dependent shader/pixel switching power) | USENIX Sec 2023 metadata |
| **GPU.zip** (`Wang et al.`) | IEEE S&P 2024 (`10.1109/SP54263.2024.00084`) | Cross-origin GPU rendering time | Pixel data via data-dependent hardware lossless framebuffer compression ratios (complementary microarchitectural data-dependent timing leak) | **Yes** | **Yes** | Crossref (`10.1109/SP54263.2024.00084`) |

#### 4.2 Direct Source Proof of the Constant-Time Verification Gap (`Jasmin` vs. `Hertzbleed`)
Comparing `jasmin-lang/jasmin` (`5741d17e3134f5b3b110e5e53494704d6d54f7c7`, `compiler/src/ct_checker_forward.ml:313-385`) directly against `FPSG-UIUC/hertzbleed` (`9cfdf955245e8e1673bb5c6cbee31f4424586ca4`, `03-leakage-model-hd/driver.c:20-58` and `04-leakage-model-hw/driver.c:50-147`) pins down the exact formal blind spot:

1. **What `Jasmin`'s Constant-Time Checker Proves (`ct_checker_forward.ml:313-385, 548-563`)**:
   - `is_ct_op1 _ = true`; `is_ct_opN _ = true`; and `is_ct_op2` rejects **only** integer division/modulo (`Omod (_, Op_w _) | Odiv (_, Op_w _)` and `Owi2(_, _, (WImod | WIdiv))`, lines 315–319).
   - `ty_expr` (`lines 336-364`) and `ty_lval` (`lines 374-385`) enforce `~public:true` strictly on memory addresses (`Pload`, `Lmem`), array indices (`Pget`, `Psub`, `Laset`, `Lasub`), and branch/loop conditions (`Cif`, `Cfor`, `Cwhile`, lines 548–563). (`sct_checker_forward.ml` extends this with `Msf` speculative-load-hardening tracking for Spectre-v1, still purely over the control-flow + memory-address leakage trace.)
   - **Consequence**: Any straight-line loop of shifts (`shlx`/`shrx`), bitwise logic (`or`/`xor`/`and`), additions, or multiplications over `Secret` registers passes `Jasmin`'s constant-time and speculative-constant-time checkers with zero errors.
2. **How `Hertzbleed` Leaks Through Those Exact Instructions (`hertzbleed` source)**:
   - **Pure Hamming-Distance (`HD`) Leakage (`03-leakage-model-hd/driver.c:23-55`)**: Executes an aligned infinite loop alternating `shlx %0, %1, %%reg` and `shrx %0, %1, %%reg` across `rbx..r13` on constant `0x0000FFFFFFFF0000` shifted by variable `count`, toggling `0..64` bits per register overwrite with zero branches and zero memory loads.
   - **Pure Hamming-Weight (`HW`) Leakage (`04-leakage-model-hw/driver.c:95-145`)**: Preloads `rbx..r15` with `first` and executes an aligned loop of `or %1, %%reg` where `first == second`—causing **zero bit flips (`HD = 0`)** per iteration while varying only the number of `1` bits (`HW`).
   - Both loops are monitored via `IA32_APERF`/`IA32_MPERF` (`khz = (maximum_frequency * aperf_delta) / mperf_delta`, `03-leakage-model-hd/driver.c:98-100`) every `1 ms`, demonstrating that **both `HD` and `HW` independently and additively (`05-leakage-model-hd_hw`) shift steady-state CPU frequency** whenever the package operates at a power or thermal limit!
   - **Amplifying Micro-Watts to Remote Key Extraction (`06-circl/README.MD:45-104`)**: Because DVFS updates on a millisecond timescale (`~1 ms`), a single instruction's pJ difference is buried in noise. To turn `Hertzbleed` into a remote attack against Cloudflare's constant-time `CIRCL` SIKE (`commit 1fc363868f344ff5a071bfc7a6b423a9c22010c9`) and `pqcrypto-sidh`, the attacker sends specially crafted **chosen ciphertexts** that drive the Montgomery ladder into an anomalous zero state (`0` coordinates) for thousands of subsequent field multiplications *if and only if* secret key bits satisfy `m[i] != m[i-1]`. Sustained all-zero operands lower `HW`/`HD` switching power across concurrent decapsulation threads (`request_count`), raising package frequency and producing a remotely measurable response-time speedup!

#### 4.3 Closed-Loop TDP DVFS Timing Oracle Probe (`Basis: execution`)
To quantify how small a data-dependent switching difference suffices to build a remote timing oracle, our standalone probe (`/tmp/probe_energy_dvfs.py`, Part 2) solves the steady-state TDP-cap equation $P_{\text{static}} + n_{\text{cores}} \cdot \alpha_b \cdot V(f_b)^2 f_b = P_{\text{TDP}}$ (`P_TDP = 65 W`, `P_static = 14 W`, `8` cores, $V(f) = 0.72 + 0.11 f_{\text{GHz}}$) for a strictly cycle-constant kernel ($N = 4.0 \times 10^8$ cycles) with a `4.5%` dynamic capacitance contrast ($\alpha_0 = 1.000$ vs. $\alpha_1 = 1.045\,\text{W}/(\text{V}^2\cdot\text{GHz})$):

| Secret Class | Capacitance Factor $\alpha$ | Steady-State Frequency $f$ | Voltage $V(f)$ | Execution Time ($N = 4 \times 10^8$ cycles) | Remote Distinguishability ($\sigma_{\text{net}} = 1.5\text{ ms}$) |
| :--- | :---: | :---: | :---: | :---: | :--- |
| Low `HW`/`HD` (e.g. `m[i] != m[i-1]`) | `1.000` | **`4.3987 GHz`** | `1.204 V` | **`90.935 ms`** | Analytical $n(\alpha=10^{-3}, \text{power}=0.99) = 28$ samples/class |
| High `HW`/`HD` (e.g. `m[i] == m[i-1]`) | `1.045` (`+4.5%`) | **`4.2924 GHz`** | `1.192 V` | **`93.189 ms`** | Monte Carlo ($n=40$, `500` trials): **`100.0%` bit accuracy**, mean Welch $t = 6.78$ |
| **Delta** | `+4.5%` | **`-106.4 MHz`** | `-12 mV` | **`+2.254 ms` (`+2.48%`)** | **Zero** branches, **zero** secret addresses, **zero** RAPL access |

#### 4.4 Defenses & Microarchitectural Masking Hardening (`Rosita` / `ELMO`)
Three defense tiers address power/DVFS side channels, each carrying sharp systems trade-offs:
1. **System/Firmware Frequency Pinning (Disable Turbo Boost / Lock P-State)**: Disabling Intel Turbo Boost / AMD Precision Boost (`hertzbleed/scripts/`) eliminates power-cap DVFS scaling under normal loads, **but** (a) sacrifices peak throughput, (b) does **not** disable emergency thermal throttling (`PROCHOT`) if cooling saturates (and `Hertzbleed` confirmed thermal throttling still leaks even with Turbo off under sustained heat), and (c) requires privileged OS/BIOS control unavailable to portable cryptographic libraries.
2. **Algorithmic Blinding & Key/Ciphertext Randomization**: Prevents chosen-ciphertext amplification (e.g., validating/rejecting anomalous SIKE/ECDH inputs, scalar blinding, projective coordinate re-randomization) so the attacker cannot sustain a low-HW/HD zero state across milliseconds—the practical mitigation deployed by `CIRCL` and `OpenSSL`/`BoringSSL` against `Hertzbleed`, though it does not eliminate single-trace local power leakage (`PLATYPUS`/`Collide+Power`).
3. **Boolean/Arithmetic Masking + Microarchitectural Leakage Rewriting (`Rosita` & `ELMO`, `0xADE1A1DE/Rosita @ d41621879dc2a1faa2c21600967ab2247d3de69d`, NDSS 2021 DOI `10.14722/ndss.2021.23137`; `Rosita++`, CCS 2021 DOI `10.1145/3460120.3485380`)**:
   - Mathematically sound first-order Boolean masking (splitting secret $x = s_0 \oplus s_1$) routinely **fails in compiled assembly** because register allocators and CPU pipelines combine shares physically: overwriting a register holding $s_0$ with $s_1$ switches `HD(s_0, s_1) = HW(x)` bits, and consecutive `ldr`/`str` instructions across shares leak via the shared memory-bus latch!
   - Direct inspection of `Rosita/ELMO/include/powermodel.h` (`hweight()`, `hdistance()`) and `Rosita/ROSITA/ARMMatcher.py` (`lines 18-250`) shows how `Rosita` closes this compiler-microarchitecture seam iteratively: `ELMO` emulates fixed-vs-random Welch $t$-test power traces on Cortex-M0 Thumb binaries to localize leaking instructions (`L`/`S` load/store bus transitions, `Op1Op2` register-overwrite transitions, `E` barrel-shifter state), and `ARMMatcher.py` automatically rewrites leaking instructions using a dedicated random-mask register (`r7`, line 19)—inserting `push {r7}; pop {rd}` (`lines 60-63, 127-128, 210-211`) to scrub load/store bus and destination-register transitions, `push {r7}; pop {r7}` (`lines 70-71, 135-136`) when only the memory bus leaks, and `ror r7, r7` (`lines 154, 250`) to flush hidden barrel-shifter state—repeating emulation until all $t$-values fall below the leakage threshold.

## Boundaries

- **Not examined — Source code of `Energy Types` and `ENT` compiler prototypes**: No official public GitHub repository for `Energy Types` (`OOPSLA 2012`) or `ENT` (`PLDI 2017`) was located at an immutable commit SHA; findings for `Energy Types` and `ENT` are grounded strictly in the Crossref-verified peer-reviewed papers (`10.1145/2384616.2384676`, `10.1145/3062341.3062356`), not direct compiler-source inspection.
- **Not examined — Bare-metal hardware execution of `Hertzbleed`, `Collide+Power`, or `Rosita` binaries**: Because hardware MSRs (`IA32_APERF`/`MPERF`, `MSR_PKG_ENERGY_STATUS`), bare-metal Turbo/thermal governors, and Cortex-M0 hardware probes were not available in the observation environment, `Hertzbleed` and `Collide+Power` findings rest on direct source inspection + peer-reviewed papers + the closed-loop numerical TDP probe (`probe_energy_dvfs.py`), rather than new bare-metal CPU power traces.
- **Known not to apply — Cycle-accurate constant-time verification (`Jasmin`, `FaCT`) to DVFS/power side channels**: Inspecting `jasmin-lang/jasmin` `ct_checker_forward.ml:313-385` confirms that formal constant-time verification proves non-interference strictly over an *architectural/speculative control-flow and memory-address trace model*. It does **not** prove wall-clock non-interference on DVFS-enabled CPUs where operand `HW`/`HD` modulates frequency (`Hertzbleed`) or where shared microarchitectural buffers collide (`Collide+Power`).
- **Known not to apply — `Rosita`'s Cortex-M0 `ELMO` rewrite rules to out-of-order x86-64 / Armv8 superscalar cores**: `Rosita`'s leakage emulator (`ELMO`) characterizes an in-order 3-stage Arm Cortex-M0 pipeline (`ARMMatcher.py`); on out-of-order superscalar cores with physical register renaming, store-to-load forwarding, and speculative execution, `push`/`pop` bus-scrubbing idioms do not map 1-to-1 to microarchitectural leakage sources (`unsupported` by `Rosita` as inspected).
- **Unknown — Closed-form static WCEC soundness under coupled thermal runaway and speculative execution on OoO CPUs**: Existing static WCEC frameworks (`Jayaseelan 2006`, `Wägemann 2015`, `llvm-energy`) target in-order embedded microcontrollers (`ARM Cortex-M`, `AVR`, `XMOS`, `MSP430`). Compositional sound static WCEC (simultaneously bounding dynamic switching, temperature-coupled leakage feedback, and out-of-order speculative wrong-path energy) on modern desktop/server OoO CPUs remains unresolved.

## Evidence

### Upstream Repository Source Citations (Pinned Revisions)
- **`FPSG-UIUC/hertzbleed` @ `9cfdf955245e8e1673bb5c6cbee31f4424586ca4`**:
  - `README.md:1-58` — tested on bare-metal Intel Core i7-9700 / Ubuntu 20.04; experiment map `01..09` (`06-circl`, `07-pqcrypto`, `08-kaslr`, `09-cc`).
  - `03-leakage-model-hd/driver.c:20-111` — aligned cycle-constant `shlx`/`shrx` Hamming-distance victim loop across `rbx..r13`; `monitor()` reading `PP0_ENERGY` and `IA32_APERF`/`IA32_MPERF` at `1 ms` intervals (`khz = (maximum_frequency * aperf_delta) / mperf_delta`, L100).
  - `04-leakage-model-hw/driver.c:50-147` — aligned cycle-constant `or %1, %%reg` (`first == second`, zero bit flips, pure Hamming-weight modulation) across `rbx..r15`.
  - `06-circl/README.MD:1-120` — Cloudflare `circl` commit `1fc363868f344ff5a071bfc7a6b423a9c22010c9` SIKE decapsulation attack exploiting `m[i] != m[i-1]` lower-power / higher-frequency / lower-runtime anomaly locally and remotely.
- **`IAIK/CollidePower` @ `edd8b4a82d47c9bd518844313acf9a1f86e164e3`**:
  - `README.md:1-36` — `E1..E6` experiment suite (`MDS-Power`, `Meltdown-Power`) demonstrating actual victim data-content leakage via shared-component Hamming distance over RAPL or Hertzbleed.
  - `analyze/power.py:1-60` — `Word(name in ['v', 'g'])` and `HW` correlation power analysis (`pearsonr`/`spearmanr`) over victim vs. attacker-guess words.
- **`jasmin-lang/jasmin` @ `5741d17e3134f5b3b110e5e53494704d6d54f7c7`**:
  - `compiler/src/ct_checker_forward.ml:313-385, 548-563` — `is_ct_op1`, `is_ct_op2` (rejecting only `Odiv`/`Omod`/`WIdiv`/`WImod`), `is_ct_opN`, `ty_expr` (`Pload`/`Pget`/`Psub` public-index check), `ty_lval` (`Lmem`/`Laset`/`Lasub`), and `Cif`/`Cfor`/`Cwhile` branch condition checks.
  - `compiler/src/sct_checker_forward.ml:1-120` — speculative constant-time lattice (`Secret`, `Transient`, `Public`, `Msf` / SLH operators), orthogonal to power/DVFS leakage.
- **`0xADE1A1DE/Rosita` @ `d41621879dc2a1faa2c21600967ab2247d3de69d`**:
  - `README.md:1-69` — iterative `ELMO` trace emulation (`emulatetraces`) + pattern-based assembly rewrite loop (`rosita -m`) until Welch $t$-test leakage vanishes.
  - `ELMO/include/powermodel.h:48-80` — `hweight()` and `hdistance()` (`x ^ y`) bit-level power model primitives.
  - `ROSITA/ARMMatcher.py:18-250` — `random_regs = ['r7']`; `LDRMatcherARM{,1,2}` inserting `push {r7}; pop {rd}` / `push {r7}; pop {r7}` for `L`/`S`/`Op1Op2` leakage markers and `ror r7, r7` for `E` barrel-shifter markers.
- **`nevillegrech/llvm-energy` @ `52809feca6c18e973099accaf05bf8f87671126d`**:
  - `inferCR.py:37-198` — `getenergy_()` (JSON ISA-mapped block energy), `getenergy()` (LLVM opcode fallback heuristic with dead `prev == 'mul'` check at L57–58), and `PubsSolver.addrel()` emitting `eq(block(formals), energy, [continuations], [conditions]).`.
- **`CMUAbstract/alpaca-oopsla2017` @ `a979300cb51409a89b7a776ead8fe50b50711bfd`**:
  - `README.md:1-55` — unified LLVM build/flash harness comparing `Alpaca` (`ext/alpaca/LLVM`), `Chain`, and `DINO` on `WISP` and `MSP430` (`ar`, `cuckoo`, `rsa`, `blowfish`, `cem`, `bc`).

### Verified Peer-Reviewed Literature
- Tiwari, V., Malik, S., & Wolfe, A. (1994). *Power Analysis of Embedded Software: A First Step Towards Software Power Minimization*. IEEE/ACM ICCAD, pp. 384–390, DOI `10.1109/ICCAD.1994.629825`; expanded in IEEE Trans. VLSI Systems, pp. 437–445, DOI `10.1109/92.335012`.
- Jayaseelan, R., Mitra, T., & Li, X. (2006). *Estimating the Worst-Case Energy Consumption of Embedded Software*. IEEE RTAS, pp. 81–90, DOI `10.1109/RTAS.2006.17`.
- Cohen, M., Zhu, H. S., Emgin, S. E., & Liu, Y. D. (2012). *Energy Types*. ACM OOPSLA, pp. 831–850, DOI `10.1145/2384616.2384676`.
- Horowitz, M. (2014). *1.1 Computing's energy problem (and what we can do about it)*. IEEE ISSCC, pp. 10–14, DOI `10.1109/ISSCC.2014.6757323`.
- Wägemann, P., Distler, T., Hönig, T., Janker, H., Kapitza, R., & Schröder-Preikschat, W. (2015). *Worst-Case Energy Consumption Analysis for Energy-Constrained Embedded Systems*. ECRTS, pp. 105–114, DOI `10.1109/ECRTS.2015.17`.
- Grech, N., Georgiou, K., Pallister, J., Kerrison, S., Morse, J., & Eder, K. (2015). *Static Analysis of Energy Consumption for LLVM IR Programs*. ACM SCOPES, pp. 12–21, DOI `10.1145/2764967.2764974`.
- Canino, A., & Liu, Y. D. (2017). *Proactive and Adaptive Energy-Aware Programming with Mixed Typechecking*. ACM PLDI, pp. 217–232, DOI `10.1145/3062341.3062356`.
- Maeng, K., Colin, A., & Lucia, B. (2017). *Alpaca: Intermittent Execution without Checkpoints*. ACM OOPSLA (PACMPL), pp. 1–30, DOI `10.1145/3133920`.
- Lipp, M., Kogler, A., Oswald, D., Schwarz, M., Easdon, C., Canella, C., & Gruss, D. (2021). *PLATYPUS: Software-based Power Side-Channel Attacks on x86*. IEEE S&P, pp. 355–371, DOI `10.1109/SP40001.2021.00063`.
- Shelton, M. A., Samwel, N., Batina, L., Regazzoni, F., Wagner, M., & Yarom, Y. (2021). *Rosita: Towards Automatic Elimination of Power-Analysis Leakage in Ciphers*. NDSS, DOI `10.14722/ndss.2021.23137`; Shelton et al. (2021), *Rosita++*, ACM CCS, DOI `10.1145/3460120.3485380`.
- Wang, Y., Paccagnella, R., He, E. T., Shacham, H., Fletcher, C. W., & Kohlbrenner, D. (2022). *Hertzbleed: Turning Power Side-Channel Attacks Into Remote Timing Attacks on x86*. USENIX Security 2022, pp. 679–697, ISBN `978-1-939133-31-1`; IEEE Micro 43(4), 2023, pp. 19–27, DOI `10.1109/MM.2023.3274619`.
- Kogler, A., Juffinger, J., Giner, L., Gerlach, L., Schwarzl, M., Schwarz, M., Gruss, D., & Mangard, S. (2023). *Collide+Power: Leaking Inaccessible Data with Software-based Power Side Channels*. USENIX Security 2023, ISBN `978-1-939133-37-3`.
- Taneja, H., Kim, J., Xu, J. J., van Schaik, S., Genkin, D., & Yarom, Y. (2023). *Hot Pixels: Frequency, Power, and Temperature Attacks on GPUs and ARM SoCs*. USENIX Security 2023.
- Wang, Y., Paccagnella, R., Gang, Z., Vasquez, W. R., Kohlbrenner, D., Shacham, H., & Fletcher, C. W. (2024). *GPU.zip: On the Side-Channel Implications of Hardware-Based Graphical Data Compression*. IEEE S&P, pp. 3716–3734, DOI `10.1109/SP54263.2024.00084`.

### Self-Contained Executable Micro-Probe (`Python 3.13.15`, Linux x86-64, observed 2026-11-19)
Save as `/tmp/probe_energy_dvfs.py` and run `python3 /tmp/probe_energy_dvfs.py`:

```python
import math, random

op_points = [(0.4, 0.70), (0.8, 0.82), (1.2, 0.96), (1.6, 1.10), (2.0, 1.25)]
def eval_path(path, f_ghz, v, temp_c):
    f_hz = f_ghz * 1e9
    p_leak = 0.04 * v * math.exp(0.035 * (temp_c - 25.0))
    if path == "A":
        t_tot = 600.0 / f_hz + 1200e-9
        e_dyn, e_periph = 0.35e-9 * (v**2) * 600.0 + 15 * 2.0e-9, 0.0
        p_peak = 0.35e-9 * (v**2) * f_hz + p_leak
    else:
        t_tot = 900.0 / f_hz
        e_dyn, e_periph = 1.60e-9 * (v**2) * 900.0, 0.120 * t_tot
        p_peak = 1.60e-9 * (v**2) * f_hz + p_leak + 0.120
    return t_tot * 1e6, (e_dyn + p_leak * t_tot + e_periph) * 1e6, p_peak

for temp_c in [25.0, 85.0]:
    print(f"T={temp_c}C:")
    for f, v in op_points:
        tA, eA, pA = eval_path("A", f, v, temp_c)
        tB, eB, pB = eval_path("B", f, v, temp_c)
        print(f"  f={f:.1f}GHz A=({tA:.3f}us,{eA:.3f}uJ,{pA:.2f}W) B=({tB:.3f}us,{eB:.3f}uJ,{pB:.2f}W) bo={pB>2.0}")

def solve_freq(alpha, p_tdp=65.0, p_stat=14.0, n_cores=8):
    lo, hi = 1.5, 5.0
    for _ in range(80):
        m = 0.5 * (lo + hi)
        if p_stat + n_cores * alpha * ((0.72 + 0.11 * m)**2) * m > p_tdp: hi = m
        else: lo = m
    return 0.5 * (lo + hi)

f0, f1 = solve_freq(1.000), solve_freq(1.045)
t0, t1 = (4e8 / (f0 * 1e9)) * 1e3, (4e8 / (f1 * 1e9)) * 1e3
dt, sigma = t1 - t0, 1.5
n_th = math.ceil(2.0 * ((3.29 + 2.33)**2) * ((sigma / dt)**2))
rng, ok, ts = random.Random(20261119), 0, []
for _ in range(500):
    s0 = [t0 + rng.gauss(0, sigma) for _ in range(40)]
    s1 = [t1 + rng.gauss(0, sigma) for _ in range(40)]
    m0, m1 = sum(s0)/40, sum(s1)/40
    v0 = sum((x-m0)**2 for x in s0)/39; v1 = sum((x-m1)**2 for x in s1)/39
    ts.append((m1 - m0) / math.sqrt(v0/40 + v1/40))
    ok += int(m1 > m0)
print(f"f0={f0:.4f}GHz f1={f1:.4f}GHz df={(f0-f1)*1000:.1f}MHz dT={dt:.3f}ms n_th={n_th} acc={100*ok/500:.1f}% mean_t={sum(ts)/500:.2f}")
```

## Revalidation

1. **Re-run the Energy/Brownout/Hertzbleed Probe**: Execute the embedded Python script above; confirm `WCET=A` vs. `WCEC=B` at all operating points, `0.4 GHz -> 0.8 GHz` energy-optimal shift from `25 C` to `85 C`, `1.2 GHz` thermal-leakage brownout (`1.93 W -> 2.20 W`), and Hertzbleed steady-state shift `df = 106.4 MHz`, `dT = 2.254 ms`, `acc = 100.0%`, `mean_t = 6.78`.
2. **Audit Constant-Time Verifier Leakage Models**: Diff `jasmin-lang/jasmin` `compiler/src/ct_checker_forward.ml` (`is_ct_op1`, `is_ct_op2`, `ty_expr`) against revision `5741d17e3134f5b3b110e5e53494704d6d54f7c7` to verify whether any future release introduces hardware-masking or operand-switching (power/probing) leakage predicates beyond control-flow and address secrecy.
3. **Check Bare-Metal Target Hardware for DVFS / Power-Cap Leakage**: On a target x86 or Arm server/SoC, compile and run `FPSG-UIUC/hertzbleed` (`03-leakage-model-hd`, `04-leakage-model-hw`) under sustained multi-core load with (a) default Turbo/Boost enabled and (b) frequency pinned to base P-state while thermally loaded, measuring `IA32_APERF`/`IA32_MPERF` (or Arm `AMU` cycle/constant counters) to determine whether the platform's power-management firmware leaks operand `HD`/`HW` into clock frequency.
4. **Revalidate Static WCEC & Brownout Envelopes on Target MCU**: When porting WCEC bounds to a new embedded processor or compiler version, re-measure per-instruction and peripheral power states across the target's *maximum* operating die temperature $T_{\max}$ (not ambient $25^\circ\text{C}$) and verify whether `nevillegrech/llvm-energy` or an IPET-based WCEC analyzer accounts for inter-instruction switching and stateful peripherals rather than flat opcode heuristics.
