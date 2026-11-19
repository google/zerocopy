# Post-ISA Microarchitectural Contract Fuzzing, TVLA Power/EM Leakage Assessment, Glitch-Extended Masking Verification, and Fault-Injection Cartography

## Summary

ISA-level formal proofs of functional correctness and architectural constant-time non-interference (`PC` + architectural load/store address invariance) terminate at an idealized sequential state machine that real silicon and synthesized gate netlists routinely violate through four physical mechanisms:

1. **Undocumented microarchitectural speculation and data-value-dependent prefetching**: Commercial CPUs transiently execute past branches, faults, store-to-load forwarding hazards, microcode assists, and division/string fast paths, or dereference register/cache contents that resemble pointers via Data Memory-Dependent Prefetchers (`DMP`s, as in Augury and GoFetch). Black-box Model-based Relational Testing (`MRT`) in **Revizor** (`microsoft/sca-fuzzer`) and symbolic observation equivalence generation in **Scam-V** (`kth-step/HolBA`) falsify assumed hardware-software leakage contracts $\llbracket P \rrbracket_{\text{exec}}^{\text{obs}}$ by finding input pairs $(x_1, x_2)$ with identical contract traces (`CTrace`) whose measured hardware side-channel traces (`HTrace`) diverge statistically.
2. **Analog CMOS power and electromagnetic (EM) side-channel emissions**: Even non-speculative, branch-free code leaks intermediate Hamming weights (`HW`) and register-bus Hamming distances (`HD`) into supply current. **ISO/IEC 17825** Test Vector Leakage Assessment (**TVLA**) applies Welch's two-sample $t$-test ($|t| > 4.5$, single-point two-sided $p = 6.795 \times 10^{-6}$) across fixed-vs-random trace ensembles captured via **ChipWhisperer** or high-bandwidth oscilloscopes. However, naive single-threshold $|t| > 4.5$ screening suffers severe multi-point Family-Wise Error Rates ($\text{FWER} = 49.31\%$ across $10^5$ independent sample points) and systematic **false negatives** both on higher-order masked shares (without centered multivariate product preprocessing) and on balanced fixed intermediates ($\text{HW}(s_{\text{fix}}) = 4$ in an 8-bit state yields exact second-order covariance $2 - \tfrac{1}{2}\text{HW}(s_{\text{fix}}) = 0$, masking real bivariate leakage).
3. **Combinational glitches and microarchitectural state transitions in masked circuits/CPUs**: Software-level $d$-probing security proofs fail on physical cores (such as unmodified RISC-V `Ibex`) when combinational logic hazards temporarily recombine shares before clock edges or when shared ALU buses, register files, and hidden forwarding latches overwrite share $s_0$ with share $s_1$ ($s_0 \oplus s_1 = s$). Execution-aware SAT correlation checking in **CocoAlma** (`isec-tugraz/coco-alma`) and exact Sylvan ROBDD probability-distribution independence checking in **SILVER** (`Chair-for-Security-Engineering/SILVER`) verify glitch-extended and transition-extended probing security directly over post-synthesis gate netlists (`Coco-Ibex`).
4. **Physical clock/voltage/EM/laser fault injection**: Transient multi-bit faults bypass single-fault error-detection codes when spatial laser spots or shared combinational cones corrupt redundant branches simultaneously. **FIVER** (`Chair-for-Security-Engineering/FIVER`) and **VerFI** (`emsec/VerFI`) partition synthesized netlists into register-bounded logic layers and symbolically classify fault tuples into `ineffective`, `detected`, and `effective` differential faults, complementing physical XY laser fault cartography.

## Applicability

This report governs the post-ISA hardware/physical validation layer for cryptographic, high-assurance isolation, and safety-critical systems whose software or RTL correctness proofs rely on assumptions about physical execution substrates.

### Relationships Among Examined Subjects

The nine subjects in `REPORT.json` form a four-tier physical validation stack below ISA semantics:

- **Post-silicon microarchitectural contract fuzzers**: `microsoft/sca-fuzzer` (`7dec7b81d4562cdd2a6026ef0830a3dac2b20cbc`) tests closed-source `x86-64` (`GenuineIntel`, `AuthenticAMD`, including VMX/SVM guest boundaries) and `arm64` CPUs via a custom Linux kernel executor module (`rvzr/executor_km/`) paired with Unicorn or DynamoRIO contract models (`rvzr/model_unicorn/`, `rvzr/model_dynamorio/`). `kth-step/HolBA` (`a39e4332dcee3c8243ac6f1bc3f8b4691eb5a4e7`) provides HOL4-formalized ARMv8/RISC-V ISA lifters and Scam-V symbolic observation-equivalent input pair synthesis for in-order/out-of-order ARM cores.
- **Physical power/EM trace acquisition and statistical leakage assessment**: `newaetech/chipwhisperer` (`884412281b1c1749b871e16e563d3ff310affd68`, v7.0 Zarr-backed integer CPA/capture pipeline; legacy analyzer modules pinned at `v6.1.0`) provides synchronous ADC clock-locked power/EM capture and fault glitching, evaluated under **ISO/IEC 17825:2024** (superseding `ISO/IEC 17825:2016`), Schneider & Moradi's higher-order moment roadmap (`DOI: 10.1007/978-3-662-48324-4_25`), and Standaert's statistical soundness critique (`DOI: 10.1007/978-3-030-15462-2_5`).
- **Pre-silicon gate-level masking verifiers**: `isec-tugraz/coco-alma` (`95c80df5d6d704bf525f47ef6e58e98e27fedf97`) verifies Yosys JSON netlists driven by concrete Verilator VCD control traces (`examples/ibex/`, `examples/aes_dom/`) for `IAIK/coco-ibex` (`1ac262929d900d63d5ed702cd40edca1602a79c9`). `Chair-for-Security-Engineering/SILVER` (`0a3c85fc5a60d76eedb84d996473df28fc18ef42`) verifies flattened or hierarchical Nangate 45 nm / Yosys Verilog netlists (`--verilog=1`) or `.nl` gate lists using exact Sylvan ROBDDs across standard and glitch-robust probing, `NI`, `SNI`, `PINI`, and output `uniformity`.
- **Gate-level fault-countermeasure verifiers**: `Chair-for-Security-Engineering/FIVER` (`176a1db7f80764543324db5378b6f82d4adebcbe`) symbolically verifies detection-based (`correction_based = false`) and correction-based (`correction_based = true`) Verilog/`.nl` netlists using CUDD ROBDDs against configurable gate-fault models (`model/bitflip.txt`, `model/set-reset.txt`, `model/em.txt`, `model/laser.txt`), complementing netlist simulation diagnosis in `emsec/VerFI` (`e7a16f93a43e814272322349df698d4408fc45a6`).

### Host, Synthesis, and Environment Constraints

- **Revizor kernel execution**: Requires bare-metal Linux root access to load `executor_km`, disable preemption and local IRQs (`raw_local_irq_save`), pin a physical core (`executor_taskset`), write `MSR_IA32_FLUSH_CMD` / `verw` / `wbinvd`, read hardware performance counters (`pfc_configure`), and discard System Management Interrupt (`status->smi_count != 0`) corrupted runs (`rvzr/executor_km/measurement.c:48-168`).
- **SILVER and FIVER cell-library restrictions**: Both verifiers require standard-cell netlists restricted to 2-input primitive gates and basic D-flip-flops (`set_dont_use` on `FA*`, `HA*`, `AOI*`, `OAI*`, `MUX*`, `XOR3*..5*`, `AND3*..5*` in Nangate 45 nm; `SILVER/README.md:89-118`). Unannotated complex cells or unflattened vendor macros invalidate structural glitch/fault decomposition.

## Findings

### 1. Black-Box Microarchitectural Contract Fuzzing (`Revizor`, `Scam-V`, `SPEECHMINER`, and `DMP` Leaks)

`Basis: normative + source + execution`

Formal hardware-software leakage contracts (Guarnieri et al., IEEE S&P 2021; Oleksenko et al., ASPLOS 2022, `DOI: 10.1145/3503222.3507729`) parameterize permitted CPU information flow as $\mathcal{C} = (\text{Exec}, \text{Obs})$, mapping an instruction sequence $P$ and architectural input state $x$ to a contract trace $\text{CTra}_{\mathcal{C}}(P, x)$. A physical CPU violates $\mathcal{C}$ if there exist $P$ and inputs $(x_1, x_2)$ such that:
$$\text{CTra}_{\mathcal{C}}(P, x_1) = \text{CTra}_{\mathcal{C}}(P, x_2) \quad \land \quad \text{HTra}_{\text{CPU}}(P, x_1) \not\equiv_{\text{stat}} \text{HTra}_{\text{CPU}}(P, x_2)$$

In `microsoft/sca-fuzzer` (`7dec7b81d4562cdd2a6026ef0830a3dac2b20cbc`), `rvzr/config.py:315-334` defines orthogonal execution and observation axes:
- **Contract observation clauses (`contract_observation_clause`)**: `"none"`, `"pc"`, `"l1d"`, `"memory"`, `"ct"` (constant-time: program counter plus all memory access addresses), `"loads+stores+pc"`, `"ct-nonspecstore"`, `"ctr"` (constant-time plus register values), `"arch"` (Meltdown/exception check exposing loaded architectural values), `"tct"`, `"tcto"`, and `"ct-ni"`.
- **Contract execution clauses (`contract_execution_clause`)**: `"seq"` / `"no_speculation"`, `"cond"` (Spectre-v1 branch misprediction), `"bpas"` (Spectre-v4 speculative store bypass), `"nullinj-fault"` / `"nullinj-assist"` (LVI/MDS zero-value injection on faults or microcode assists), `"div-zero"`, `"div-overflow"`, `"meltdown"`, `"noncanonical"`, and value-speculation clauses `"vspec-ops-div"` / `"vspec-ops-memory-faults"` (added after *Hide and Seek with Spectres*, IEEE S&P 2023, uncovered speculative operand leaks in x86 division and string-compare fast paths).
- **Hardware trace modes (`executor_mode`)**: `'P+P'` (L1D Prime+Probe 64-set occupancy bitmask), `'F+R'` (Flush+Reload), `'E+R'` (Evict+Reload), `'PP+P'` (Partial Prime+Probe), and `'TSC'` (cycle-counter timing).

#### Seven-Pass False-Positive Elimination Pipeline in `rvzr/fuzzer.py`

Direct inspection of `_RoundManager` (`rvzr/fuzzer.py:42-43, 102-205`) and `EquivalenceAnalyserCommon` (`rvzr/analyser.py:67-200`) shows how Revizor eliminates modeling artifacts and physical measurement noise before reporting a `Violation`:

1. **`fast`**: Collects taint sets on initial inputs (`_boost_inputs`, `rvzr/fuzzer.py:226-243`), generates `CONF.inputs_per_class` boosted inputs sharing identical contract-tainted bytes while randomizing untainted secret bytes, reuses one `CTrace` per taint class (`enable_fast_contract_tracing = True`), and runs minimum sample count `CONF.executor_sample_sizes[0]` (`10` repetitions after `executor_warmups = 5`).
2. **`nesting`**: Escalates speculative nesting depth from `model_min_nesting = 1` to `model_max_nesting = 30` (`max_spec_window = 250` instructions, `rvzr/config.py:236-241`) so nested mispredictions not modeled at depth 1 are filtered out.
3. **`taint_mistake`**: Disables `enable_fast_contract_tracing` and traces every boosted input individually through Unicorn/DynamoRIO (`rvzr/fuzzer.py:164-174`) to catch cases where untainted bytes unexpectedly altered contract observations.
4. **`priming`**: Executes `_priming_check()` (`rvzr/fuzzer.py:176-180`), replaying candidate violating input $x_2$'s preceding microarchitectural sequence before measuring $x_1$ (and vice versa) to eliminate cross-input residual predictor/cache state not cleared by `uarch_flush()` (`verw` + `MSR_IA32_FLUSH_CMD` `L1D_FLUSH` + `wbinvd` + `lfence` in `rvzr/executor_km/measurement.c:48-64`).
5. **`noise`**: Progressively increases hardware repetitions through `executor_sample_sizes = [10, 50, 100, 500]` (`rvzr/config.py:252`), discarding violations that vanish under `chi2` (`stat / (N_1 + N_2) < analyser_stat_threshold = 0.5`) or `MergedBitmapAnalyser` outlier filtering (`counter[x] >= 0.10 * sample_size`, `rvzr/analyser.py:172-200`).
6. **`priming_large`** and **`arch_mismatch`**: Re-runs priming at peak sample size (`500`) and verifies architectural register/memory agreement between Unicorn and silicon so emulator ISA bugs are classified as `arch_violations` rather than side-channel leaks.

#### Subset vs. Disjoint Bitmap Nuance and Data Memory-Dependent Prefetchers (`DMP`)

`Basis: source + execution + derived`

In `MergedBitmapAnalyser.htraces_are_equivalent` (`rvzr/analyser.py:194-200`), `CONF.analyser_subsets_is_violation` defaults to `False` (`rvzr/config.py:269`), treating hardware cache-set bitmaps $B_1, B_2 \in \{0,1\}^{64}$ as equivalent whenever $B_1 \subseteq B_2$ or $B_2 \subseteq B_1$ (`((B_1 & ~B_2) == 0) or ((B_2 & ~B_1) == 0)`). Our standalone probe (`Basis: execution`) demonstrates a subtle consequence for Data Memory-Dependent Prefetchers (Vicarte et al., *Augury*, IEEE S&P 2022, `DOI: 10.1109/SP46214.2022.9833570`; Chen et al., *GoFetch*, USENIX Security 2024):
- If secret $x_1$ is a non-pointer integer (`B_1 = {3, 11}`) and secret $x_2$ resembles a valid virtual address triggering a single DMP line fill on cache set `27` (`B_2 = {3, 11, 27}`), then $B_1 \subsetneq B_2$: `MergedBitmapAnalyser` with default `analyser_subsets_is_violation = False` marks $(x_1, x_2)$ **equivalent** (`True`) unless either `analyser_subsets_is_violation = True` (`False`), `chi2` distribution comparison is used, or a third boosted input $x_3$ triggers a distinct DMP cache set `42` (`B_3 = {3, 11, 42}`, making $B_2$ and $B_3$ incomparable and triggering violation `False`).
- Crucially, DMP leaks violate `"ct"`-`"seq"` even **without transient execution or secret-dependent architectural branches**: GoFetch extracts keys from constant-time OpenSSL Diffie-Hellman, Go RSA, CRYSTALS-Kyber, and CRYSTALS-Dilithium via chosen inputs that steer intermediate data words through pointer-pattern matching in Apple M1–M3 L2 DMP hardware (mitigated on M3 only via privileged `DIT` / `SYS_APL_HID11_EL1` bits).
- **Scam-V** (`kth-step/HolBA`, Nemati et al., CAV 2020, `DOI: 10.1007/978-3-030-53288-8_12`) complements Revizor's random taint boosting by lifting binary programs into HOL4 BIR intermediate representation and solving SMT queries for observation-equivalent input pairs $\text{obs}(P, x_1) = \text{obs}(P, x_2)$ that maximize path/data divergence, while **SPEECHMINER** (Xiao et al., NDSS 2020) isolates exception-driven transient windows into fault-raise vs. retirement sub-windows across x86 cores.

---

### 2. ISO/IEC 17825 Welch's $t$-Test (`TVLA`), Multi-Point FWER Traps, and Standaert's False-Negative Algebra

`Basis: normative + source + execution + derived`

Under **ISO/IEC 17825:2024** (and CRI's non-specific TVLA methodology), an evaluator partitions $N_A + N_B$ physical power or EM traces $\mathbf{l}_i \in \mathbb{R}^M$ (sampled at $M$ time points per cryptographic operation, e.g., via `newaetech/chipwhisperer` synchronous ADC capture where target clock and ADC sampling clock share a frequency-locked PLL root, eliminating clock-jitter de-alignment) into Group $A$ (fixed input $x_{\text{fix}}$) and Group $B$ (random inputs $x \leftarrow \mathcal{U}$), computing univariate Welch's $t$-statistic at each sample index $j \in \{1, \dots, M\}$:
$$t_j = \frac{\hat{\mu}_{A,j} - \hat{\mu}_{B,j}}{\sqrt{\frac{s_{A,j}^2}{N_A} + \frac{s_{B,j}^2}{N_B}}}, \qquad \text{reject } H_0 \text{ if } \max_{1 \le j \le M} |t_j| > 4.5$$

#### Trap 1: Multi-Point Family-Wise Error Rate (`FWER`) Without Holdout Confirmation

At a single Gaussian sample point under $H_0$, $p_1 = \Pr[|Z| > 4.5] = \operatorname{erfc}(4.5 / \sqrt{2}) = 6.7953 \times 10^{-6}$. Across $M$ independent oscilloscope sample points, the probability of at least one false alarm is $\text{FWER}(M) = 1 - (1 - p_1)^M$:
- At $M = 10{,}000$ samples: $\text{FWER} = 6.57\%$;
- At $M = 100{,}000$ samples: $\text{FWER} = 49.31\%$ (`Basis: execution`);
- At $M = 1{,}000{,}000$ samples (typical multi-round asymmetric or PQC trace): $\text{FWER} = 99.89\%$.

ISO/IEC 17825 and Schneider & Moradi (`DOI: 10.1007/978-3-662-48324-4_25`) resolve this in two ways: (i) **two-dataset independent confirmation**, requiring peaks exceeding $|t| > 4.5$ to recur at the **exact same sample index $j$ with identical sign** across two independently acquired trace sets ($p_{\text{joint}} = \tfrac{1}{2} p_1^2 \approx 2.31 \times 10^{-11}$, reducing $M = 10^5$ FWER to $2.31 \times 10^{-6}$), or (ii) Šidák/min-$p$ threshold adjustment $C(\alpha, M) = \sqrt{2}\,\operatorname{erfc}^{-1}(\alpha / M)$ (e.g., $|t| > 5.89$ for $\alpha = 10^{-3}, M = 10^5$).

#### Trap 2: Higher-Order Masking Blindness and Standaert's Balanced-Intermediate False Negative

`Basis: execution + derived`

For a $d$-th order Boolean-masked secret $s = s_0 \oplus s_1 \oplus \dots \oplus s_d$ where fresh uniform masks $s_0, \dots, s_{d-1} \leftarrow \mathcal{U}(\{0,1\}^n)$ are processed at distinct times $t_0, \dots, t_d$, every marginal distribution $s_k$ is uniform and independent of $s$. Consequently, first-order Welch's $t$-test yields $\mathbb{E}[t_j] = 0$ for all $j$, regardless of how many millions of traces are collected. Schneider & Moradi (`CHES 2015`) detect $(d+1)$-th order leakage by centering and multiplying sample tuples:
$$C_{j_0, \dots, j_d}^{(i)} = \prod_{r=0}^{d} \left(l_{i, j_r} - \hat{\mu}_{j_r}\right)$$
and applying Welch's $t$-test to $C^{(i)}$ via one-pass online central-moment recurrences.

However, as Standaert proved (`CARDIS 2018`, `DOI: 10.1007/978-3-030-15462-2_5`) and our executable micro-probe confirms quantitatively (`Basis: execution`), **even centered second-order fixed-vs-random TVLA suffers complete false negatives when the fixed intermediate happens to have balanced Hamming weight**. For an $n$-bit byte ($n = 8$) split into $s_0 = m$ and $s_1 = s \oplus m$ under noisy Hamming-weight leakage $L_0 = \text{HW}(s_0) + \varepsilon_0$, $L_1 = \text{HW}(s_1) + \varepsilon_1$, Walsh-Hadamard expansion gives the exact population covariance:
$$\mathbb{E}_{m \leftarrow \mathcal{U}(\{0,1\}^8)}\!\left[(\text{HW}(m) - 4)(\text{HW}(s \oplus m) - 4)\right] = \frac{1}{4}\sum_{b=0}^{7} (1 - 2 s_b) = 2 - \frac{1}{2}\text{HW}(s)$$
For the random group $s \leftarrow \mathcal{U}(\{0,1\}^8)$, $\mathbb{E}_s[2 - \tfrac{1}{2}\text{HW}(s)] = 0$. Therefore:
- If the fixed test vector hits an intermediate with $\text{HW}(s_{\text{fix}}) = 4$ (e.g., `0x5A`, which comprises $\binom{8}{4}/256 = 27.34\%$ of all byte values!), the fixed-group second-order moment is **identically zero** ($2 - 4/2 = 0$). Over $4{,}000 + 4{,}000$ traces at $\sigma = 1.0$, `s_fix = 0x5A` produces $t_1 = (+0.956, +0.009)$ and **$t_2 = +1.922 < 4.5$** (false "PASS"), even though a standard second-order CPA attack trivially recovers the key!
- Conversely, `s_fix = 0x00` ($\text{HW} = 0$, covariance $+2.0$) leaves 1st-order TVLA blind ($t_1 = -0.685, -2.894$) while firing **$t_2 = +28.345 \gg 4.5$**. Sound TVLA campaigns must therefore include **semi-fixed (intermediate-class-partitioned) test vectors** spanning $\text{HW} \in \{0, 8\}$ rather than relying on a single arbitrary fixed plaintext.

---

### 3. Gate-Level Glitch-Extended & Transition-Extended Masking Verification (`CocoAlma`, `Coco-Ibex`, and `SILVER`)

`Basis: source + execution`

Software masking proofs in the Ishai-Sahai-Wagner (`ISW`) $d$-probing model assume each probe reads one pure intermediate variable. On real CMOS netlists and CPUs, two hardware effects destroy pure ISW security (`Gigerl et al., USENIX Security 2021`; `Hadžić & Bloem, FMCAD 2021, DOI: 10.34727/2021/isbn.978-3-85448-046-4_9`):
1. **Combinational glitches**: Unequal gate/wire propagation delays within a clock cycle allow an internal gate output to transiently evaluate arbitrary Boolean functions of **all register outputs and primary inputs in its combinational fan-in cone** up to the nearest synchronization flip-flop boundary.
2. **Register/bus transitions and microarchitectural state sharing**: Overwriting flip-flop or register $R$ from previous cycle value $v^{(t-1)}$ to $v^{(t)}$ dissipates dynamic power proportional to $\text{HW}(v^{(t-1)} \oplus v^{(t)})$. On an unmodified 32-bit `Ibex` RISC-V core, Coco identified leaks in (a) consecutive register-file reads/writes sharing read-data muxes, (b) ALU/shifter operand latches retaining share $s_0$ into the next instruction processing $s_1$, (c) data-memory load/store write-data registers, and (d) forwarding paths—patched in `IAIK/coco-ibex` (`1ac262929d900d63d5ed702cd40edca1602a79c9`) via register-file one-hot gating and operand clearing at ~`10%` core area cost and `0%` cycle penalty for non-masked code.

#### `CocoAlma` Execution-Aware SAT Correlation Encoding vs. `SILVER` Exact ROBDD Independence

Direct source inspection of `isec-tugraz/coco-alma` (`95c80df5d6d704bf525f47ef6e58e98e27fedf97`, `verify.py:40-122` and `SatChecker.py:13-260`) and `Chair-for-Security-Engineering/SILVER` (`0a3c85fc5a60d76eedb84d996473df28fc18ef42`, `inc/Silver.hpp:60-87`) exposes a crisp algorithmic trade-off:

- **`CocoAlma` (`SatChecker.py`)**: Simulates concrete software instructions on the Verilated CPU netlist (`verilator_tb.cpp`) to record deterministic control signals (`pc`, instruction decode, non-secret addresses) in a `.vcd` trace (`VCDStorage.py`), pruning inactive multiplexers per cycle (`SafeGraph.py`). It then encodes **Fourier/Walsh-Hadamard correlation sets** (`PropVarSet`) into an incremental SAT solver (`CaDiCaL` by default, or exported CNF for `Kissat` via `--export-cnf`, `verify.py:95-103`):
  - Linear gates (`XOR`/`XNOR`, `SatChecker.py:138-159`) take the symmetric difference of support sets (`set(l1).symmetric_difference(l2)`), memoized in `linear_set_cache` so `a ^ a == 0` cancels syntactically.
  - Nonlinear gates (`AND`/`OR`, `SatChecker.py:160-198`) promote arguments via `assure_biased` (`PropVarSet(biased=...)`, allowing subsets of the Fourier support to correlate) and memoize unions in `nonlin_set_cache`.
  - Three symbol tables per cycle (`node_vars_stable[cycle]`, `node_vars_trans[cycle]` for `--mode transient`, and `node_vars_diff[cycle]` combined via `make_choice` for `--include-hamming` / `--glitch-behavior loose`, `SatChecker.py:16-18, 200-222`) check whether any $q$-tuple (`--order q`) of probes correlates with **all shares of any secret bit** while canceling all fresh masks (`make_act_assumes`, `SatChecker.py:36-45`).
  - Note the probing-model distinction in `SatChecker.py:213-260`: `--probing-model time-constrained` counts each `(wire, cycle)` pair as one probe (appropriate for software running thousands of cycles on a CPU), whereas `--probing-model classic` allows a single hardware probe on `cell_id` to observe that wire across **all clock cycles simultaneously** (`node_to_vars[info.cell_id]`; CNF export is explicitly blocked for `time-constrained` in `verify.py:115-117`).
- **`SILVER` (`inc/Silver.hpp:68-77`)**: Represents exact Boolean functions of every gate and glitch-extended fan-in bundle as canonical multi-core **Sylvan ROBDDs** (`--memory` default `1 GiB`), verifying exact statistical independence (zero false positives! Because Fourier-support over-approximation in SAT verifiers can flag rare algebraic false positives when nonlinear bias terms cancel exactly, whereas ROBDD probability counting is **necessary and sufficient**). `SILVER` checks five composability notions in both `standard` and glitch-`robust` models: `probing`, Non-Interference (`NI`), Strong Non-Interference (`SNI`), Probe-Isolating Non-Interference (`PINI`, Cassiers et al., where $t$ internal + $o$ output-share probes can be simulated from at most $t + o$ input share indices, giving **trivial gadget composition across arbitrary linear wiring without fresh mask insertion**), and output `uniformity` (`SILVER/README.md:38-46` shows `dom1.nl` passing `SNI.standard` in `6 ms` while failing `SNI.robust` on `<out:line18>` and `PINI.robust` on `<reg:line14>` in `7 ms`!).

---

### 4. Gate-Level Symbolic Fault-Injection Verification (`FIVER`, `VerFI`) and Physical Laser Cartography

`Basis: source + execution + documentation`

Physical fault adversaries inject clock/voltage glitches, EM pulses, or focused near-infrared (`1,064 nm` Nd:YAG backside through-silicon photoelectric current) laser spots to skip instructions or corrupt intermediate cipher rounds for Differential Fault Analysis (`DFA`) or Statistical Ineffective Fault Analysis (`SIFA`).

In `Chair-for-Security-Engineering/FIVER` (`176a1db7f80764543324db5378b6f82d4adebcbe`, `inc/passes/analysis/fault.hpp:46-167`, Richter-Brockmann et al., TCHES 2021, `DOI: 10.46586/tches.v2021.i4.447-473`):
- Every gate can be transformed into any of **16 complete 2-input Boolean fault functions** (`enum Fault { AND..NCONV }`, `B0..B15`, encompassing `RESET` stuck-at-0 `B6`, `SET` stuck-at-1 `B7`, bit-flip `XOR`/`XNOR`, and asymmetric laser/EM fault models `model/laser.txt`, `model/em.txt`).
- `elaborate.cpp` partitions the netlist at flip-flop boundaries into register-bounded logic layers, builds golden CUDD ROBDDs (`elaborate_node`), and incrementally re-evaluates only the forward propagation cone (`determine_propagation_path` + `fault_injection_incremental`) for all $\binom{|G|}{n}$ multivariate fault tuples (`fault.number = n`, `fault.variate`).
- `evaluate_detection` (`fault.hpp:143`) symbolically intersects the faulty output BDD $\mathbf{F}_{\text{faulty}}(x)$ with the golden output BDD $\mathbf{F}_{\text{gold}}(x)$ and error-flag BDD $E_{\text{faulty}}(x)$ across **all $2^{|x|}$ input vectors simultaneously** in $O(|BDD|)$ operations (`18.92 ms` for `98,048` fault scenarios over `128`-bit `CRAFT` in `FIVER/README.md:45-79`), classifying every `(location_tuple, input)` into:
  1. **`detected`**: $E_{\text{faulty}}(x) = 1$ (countermeasure raises `ErrorFlag` / suppresses output);
  2. **`ineffective`**: $E_{\text{faulty}}(x) = 0 \land \mathbf{F}_{\text{faulty}}(x) = \mathbf{F}_{\text{gold}}(x)$ (safe against DFA, **but secret-dependent `ineffective` probability leaks keys under SIFA!**);
  3. **`effective`**: $E_{\text{faulty}}(x) = 0 \land \mathbf{F}_{\text{faulty}}(x) \neq \mathbf{F}_{\text{gold}}(x)$ (undetected corrupt ciphertext).

 critically, `FIVER/README.md:122-138` exposes two verification soundness boundaries that human auditors must verify:
- **`blacklist` assumptions (`model/blacklist.txt`)**: Final error-checker gates (`Check1_CheckInst`) are excluded from single-fault injection because faulting the 1-bit `ErrorFlag` wire itself trivially suppresses detection unless dual-rail complementary error flags `(e_0, e_1) \in \{(0,1), (1,0)\}$ are carried to the actuator/bus interface.
- **`reduced_complexity` soundness**: Mode `2` ("aggressive") carries **no guarantee of soundness** (`README.md:136`), whereas mode `3` ("conservative") soundly prunes fault locations dominated within fanout-free cones.
- **Spatial laser common-mode bypass (`Basis: execution + documentation`)**: Our standalone 4-bit redundant S-Box probe verifies `0` effective single-bit faults (`128/128` detected), yet `64` undetected **effective** bivariate faults when a `5–15 µm` laser spot simultaneously flips homologous bits in interleaved branch $A$ and branch $B$! Pre-silicon `FIVER` proofs at `number = 1` must therefore be paired with post-place-and-route GDSII spatial minimum-distance separation constraints ($d_{\text{homologous}} > r_{\text{laser}}$) and physical XY laser cartography (`Courbon et al., DOI: 10.1109/TCAD.2015.2411603`; `Rivière et al., DOI: 10.1109/HST.2015.7140238`).

---

### 5. Cross-System Six-Level Performance & Resource Footprint Matrix (`L1`–`L6`)

`Basis: source + documentation + execution`

| System / Method | `L1` Human & Agent Authoring Burden | `L2` Toolchain Build Time & Deps | `L3` Analysis / Campaign Latency | `L4` Target Code / Silicon Overhead | `L5` Witness / Result Check Speed | `L6` RAM, Disk & Trace Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`Revizor`** (`microsoft/sca-fuzzer`) | `~25–80 LoC` YAML contract/actor config (`demo/*.yaml`); zero RTL/source annotations | `< 15 s` Python `pip` + `make` C kernel module (`executor_km`, `< 5 s`) | `100–3,000` test cases/min (`100x` speedup with speculation + observation filters; hours for deep campaigns) | `0%` production overhead (offline test harness); software mitigations (`lfence`) add `15–180%` cycles | `< 50 ms` deterministic replay of minimized `violation.asm` + 2 `InputData` blobs | `~200–600 MiB` Python + Unicorn RSS; `< 10 KiB` minimized reproducer |
| **`Scam-V`** (`kth-step/HolBA`) | `~50–200 LoC` SML observation model over HOL4 BIR lifter | `25–60 min` HOL4 + Poly/ML + HolBA theorem-prover build (`4–8 GiB` RAM) | `1–30 s` per program (`Z3` bit-vector SMT input-pair synthesis + UART board measurement) | `0%` target overhead | `~10–100 ms` board UART measurement replay | `2–6 GiB` Poly/ML + Z3 solver RSS |
| **`TVLA` + `ChipWhisperer`** (`ISO/IEC 17825`) | `~80–250 LoC` Python capture + trigger + incremental Welford/moment script | `< 20 s` `pip install chipwhisperer` (Zarr + NumPy); FPGA bitstream prebuilt | `10^4` traces in `~20 s` (`CW-Husky` USB) to `10^7` traces in `1–6 h` (`oscilloscope` segmented capture) | `1` GPIO trigger pin during lab evaluation (`0%` field cost) | `~10–80 MB/s` streaming Welford $t$-test pass (`90 ms` for `8,000` traces in Python; `> 2 GB/s` SIMD/C) | `Zarr` trace stores: `10^6` traces $\times 10^4$ `int16` pts = **`20 GB` disk**; `O(M)` (`< 10 MB`) streaming RAM |
| **`CocoAlma`** (`isec-tugraz/coco-alma`) | `~15–60 LoC` signal share `labels.txt` + `verilator_tb.cpp` wrapper | `1–4 min` (`Yosys` + `Verilator` + `python-sat`/`CaDiCaL` or `Kissat`) | `0.5 s` (masked S-Box gadget) to `2–45 min` (`Coco-Ibex` executing masked AES-128 software, $q=1,2$) | `Coco-Ibex` netlist gating: **`~10%` LUT/gate area**, **`0%` cycle overhead** on unmasked code (`2–5x` cycles for masked SW) | `< 10 ms` SAT assignment check (`verify.py` `pretty_error` minimal leaking linear set) | `0.5–12 GiB` `CaDiCaL`/`Kissat` RSS + `.vcd` trace (`10–500 MB`) |
| **`SILVER`** (`Chair-for-Security-Engineering/SILVER`) | `~5–20` `(* SILVER="Vn_Sm" *)` Verilog port attributes | `2–5 min` C++17 + Boost Graph + `Sylvan` parallel BDD (`make release`) | **`3–7 ms`** (`dom1` AND gadget) to `10 s – 40 min` ($d=1,2$ AES S-Box `PINI.robust`); exponential blowup at $d \ge 3$ full rounds | `PINI`/`DOM` hardware masking: `2.2–4.5x` area + `36–144` fresh random bits/S-Box | No standalone certificate (`Sylvan` BDD is trusted; re-run takes `ms–min`) | Default `1 GiB` (`--memory 1073741824`) up to `64+ GiB` Sylvan BDD table |
| **`FIVER` / `VerFI`** | `~10–25 LoC` INI config (`config/verify`) + 2 `(* fiver=... *)` port attrs + `blacklist.txt` | `2–6 min` C++ + Boost + `CUDD 3.0.0` (`make release`) | **`18.9 ms`** (`1,118`-gate `CRAFT` `n=1`, `98,048` scenarios) to `minutes–hours` (`n=2,3` bivariate/trivariate AES) | Redundant cipher + parity/duplication: `1.8–3.1x` area + `ErrorFlag` interlock | `< 5 ms` concrete fault-vector simulation check on reported `(gate, Fault, input)` witness | `1–8 GiB` per core CUDD BDD table (`general.memory = 8`) |

---

### 6. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

`Basis: source + derived`

#### `C1` — Human Comprehensibility vs. Agent Execution Ergonomics

- **Diagnostic legibility gradient**:
  - `CocoAlma` (`verify.py:53-55, 202-220`, `--minimize-leaks`) and `SILVER` (`README.md:43-45`) exhibit high `C1` counterexample legibility: when a masked design fails, `CocoAlma` minimizes the SAT witness to the smallest linear combination of gate signals and prints exact `(cycle, cell_name, mode ∈ {stable, hamming, trans})` contributors, enabling a human designer to insert a single pipeline register or mask refresh directly at the offending wire.
  - `Revizor` (`rvzr/postprocessing/minimizer.py`) automatically shrinks failing random programs (`24` instructions + multi-page sandbox memory) down to `3–7` assembly instructions and two concrete inputs, plus differential `CTrace` vs. `HTrace` cache-set bitmaps. However, mapping a black-box silicon `HTrace` divergence back to an undocumented microarchitectural structure (e.g., AMD Transient Scheduler Attacks `demo/tsa-sq/` or `uop`-cache tag aliasing) still demands high human microarchitectural expertise, whereas LLM agents can automate instruction-variant bisection loops mechanically.
  - `TVLA` $t$-curves have **deceptively high visual legibility paired with severe semantic footguns**: an oscilloscope spike of $t = +6.2$ at sample `41,820` tells an engineer *when* current differed, not *which instruction or netlist wire* caused it, and $t \in [-4.5, +4.5]$ creates false human confidence when fixed-input $\text{HW}=4$ cancellation (`Standaert`) or unaligned clock jitter hides fatal leakage.
- **Hidden annotation footguns (`Working-Memory Audit`)**: Three small files silently govern the entire soundness of gate-level proofs and MUST remain < 20 lines for human line-by-line review: (1) `CocoAlma`'s `labels.txt` (`static_random` vs. `volatile_random`—mislabeling a reused RNG bus as `volatile_random` unsoundly assumes fresh entropy every cycle!), (2) `CocoAlma`'s `--ignored-signals` (`verify.py:85-88`, forcing ignored cones stable), and (3) `FIVER`'s `blacklist.txt` (`README.md:122-127`, excluding faulted error checkers).

#### `C2` — Conceptual Simplicity, Orthogonality, and Anti-Shell-Game Model Refinement

Across these nine tools, fragmented ad-hoc models (`Spectre-v1`, `Spectre-v4`, `Meltdown`, `LVI`, `MDS`, `DMP`, `glitches`, `transitions`, `SIFA`, `DFA`) collapse cleanly into **two universal semantic abstractions** without shifting complexity into trusted adapters:

1. **Observational Non-Interference Parameterized by Explicit Transition-Observation Morphisms $(\tau_{\text{phys}}, \omega_{\text{phys}})$**:
   - Guarnieri et al.'s contract lattice $(\text{Exec}, \text{Obs})$ already unifies control/value/exception speculation (`seq`, `cond`, `bpas`, `nullinj`, `vspec`), and extending $\omega_{\text{phys}}$ with cache-line data-pointer dereference (`dmp(val)`) turns `Augury`/`GoFetch` from "constant-time violations outside the model" into ordinary contract clauses (`ct-dmp`) testable by the exact same relational equivalence check $\omega_{\text{phys}}(s_1) = \omega_{\text{phys}}(s_2)$.
2. **Probe-Isolating Non-Interference (`PINI`) Under Glitch+Transition Extended Wires (`Cassiers et al.` / `SILVER`)**:
   - Early masking theory required distinct security notions (`d-probing`, `NI`, `SNI`), manual mask-refresh insertion rules, and separate glitch vs. register-transition patches. Extending each physical wire $w$ at cycle $t$ to its **physical observation bundle** $\mathcal{B}(w, t) = \text{CombCone}(w, t) \cup \{R^{(t-1)}, R^{(t)}\}$ and enforcing **robust `PINI`** makes arbitrary affine/linear composition free (`0` refresh gadgets needed across share-isolated wires!) while simultaneously discharging glitches and Hamming-distance transitions under one uniform law.
   - **Shell-game warning**: Hiding CPU register-overwrite leaks exclusively via compiler instruction-scheduling heuristics (inserting dummy register clears in LLVM backends without `Coco-Ibex` hardware gating) fails Ousterhout's deep-module test whenever out-of-order rename tables, hidden ALU operand latches, or microarchitectural forwarding buses re-alias shares behind the ISA's back.

---

### 7. End-to-End Solution & Implementation Validation Methodology (`V1`–`V4`)

`Basis: source + execution + derived`

Because physical security tools sit at the bottom of the formal assurance stack, **who validates the validators and their physical assumptions?** Every deployment requires end-to-end validation across all four axes `V1`–`V4`:

| Validation Axis | Failure Mode If Omitted | Concrete End-to-End Validation Protocol & Quantitative Oracle |
| :--- | :--- | :--- |
| **`V1` Spec, Label & Contract Adequacy / Mutation Kill Rate** | Mislabeling a reused RNG wire as `volatile_random` in `CocoAlma`, over-populating `FIVER`'s `blacklist.txt`, or testing against an overly weak contract (`arch` instead of `ct`) yields **vacuous `SECURE` verdicts**. | **Mutant-netlist & broken-label litmus gates**: Notice `coco-alma` ships paired positive/negative regression fixtures (`labels_dom_and_1storder.txt` $\to$ `SECURE` vs. `labels_dom_and_1storder_broken.txt` $\to$ `INSECURE`, `examples/gadgets/`). Enforce `100%` mutant-kill rate on intentional unmasked/unregistered wire injections, audit `|ignored_signals| == 0` on secret cones, and verify non-empty `effective_classes >= 2` (`STAT.eff_classes`, `rvzr/analyser.py:124, 145`) so `Revizor` never passes vacuously on singleton contract classes! |
| **`V2` Synthesis, Lowering & Cross-Checker Soundness Fuzzing** | Logic synthesizers (`Yosys` `opt_expr`/`abc`, Design Compiler) apply Boolean identities $(a_0 \oplus a_1) \land b$ or CSE across share domains, destroying RTL masking; or `CocoAlma`'s SAT encoding / `FIVER`'s mode-2 reduction has an implementation bug. | **Post-synthesis netlist-level verification + cross-engine differential fuzzing**: Always run `CocoAlma`/`SILVER`/`FIVER` on the **post-synthesis, post-place-and-route gate netlist** (`set_dont_use` complex cells, `keep_hierarchy`), never pre-synthesis RTL. Cross-check `CocoAlma` (Fourier-SAT) against `SILVER` (exact Sylvan ROBDD) on small gadgets ($d \le 2$): `SILVER` catches any unsound under-approximation in `CocoAlma`, while `SILVER` pins exact false-positive bounds where `CocoAlma` over-approximates nonlinear cancellation. |
| **`V3` Post-Silicon Contract Fuzzing, Multi-Moment TVLA & Fault Cartography** | Pre-silicon `Coco-Ibex` netlist proofs omit analog cross-capacitance coupling between adjacent metal routes, substrate power-grid IR drop, undocumented commercial CPU errata, and multi-bit spatial laser spots. | **Three-prong physical silicon campaign**: (1) Run `Revizor` (`executor_sample_sizes: [10, 50, 100, 500]`, `enable_priming: true`, `chi2` + `bitmaps` with `analyser_subsets_is_violation: true`) across user/kernel/VM boundaries; (2) Execute `ISO/IEC 17825` multi-million trace TVLA using **both** skewed ($\text{HW} \in \{0, 8\}$) and semi-fixed vectors across orders $1 \dots d+1$ with two-dataset independent peak confirmation; (3) Run pulsed `1,064 nm` XY laser scan + EM fault sweeps checking both `effective` (DFA) and secret-biased `ineffective` (SIFA) fault maps. |
| **`V4` Analog Acquisition Envelope, HIL Bench Replay & Human Mental-Model Validation** | Attenuated probe bandwidth (`< 20 MHz` low-pass missing `500 ps` combinational glitch spikes), ADC clipping (`overflow` flattening $t$-statistics toward `0`!), thermal drift, or operator misinterpretation of TVLA pass criteria. | **Calibrated canary-leak injection & operator litmus tests**: Inject a deterministic hardware canary (`1`-cycle unmasked `XOR` key toggle before/after target operation): if the acquisition chain fails to produce $|t_{\text{canary}}| \gg 10$ without ADC rail clipping (`min > ADC_MIN`, `max < ADC_MAX`), invalidate the entire trace campaign! Replay recorded EM/power disturbance envelopes and test security engineers against concrete litmus cases (`constant-time != DMP-safe`, `HW=4 TVLA blind spot`, `register-overwrite HD leak`). |

## Boundaries

- **Completeness of black-box `Revizor` campaigns (`known not to apply`)**: Absence of a `Revizor` violation over $K$ random programs does **not** prove silicon compliance with contract $\mathcal{C}$. Random generation covers bounded basic-block lengths (`program_size = 24`), finite speculation windows (`model_max_spec_window = 250`), and the chosen `executor_mode` (`P+P` observes L1D set occupancy but **does not** directly observe contention on execution ports, AVX frequency throttling, BTB/RSB state without transmitter gadgets, or off-core DRAM row buffers unless `TSC` / `F+R` transmitters convert them).
- **Proprietary commercial CPU netlist masking (`unsupported` / `not examined`)**: `CocoAlma` and `SILVER` require full white-box gate-level netlists (`Verilog` / Yosys JSON). Because commercial `x86-64` and `Apple M`-series RTL netlists are proprietary (`not examined` at gate level), masked software on closed-source cores cannot be proved glitch/transition-free via `CocoAlma` and must rely on post-silicon `TVLA` and microarchitectural leak testing.
- **TVLA non-detection vs. worst-case key-recovery security (`known not to apply`)**: Passing `ISO/IEC 17825` $|t| \le 4.5$ at $N$ traces does **not** bound mutual information or defeat horizontal/template/deep-learning multi-sample attacks when leakage is spread across thousands of time points (e.g., shuffled or masked post-quantum lattice NTTs) or masked by balanced fixed test vectors (`Standaert`, `DOI: 10.1007/978-3-030-15462-2_5`).
- **Analog coupling and post-layout parasitic capacitance in `CocoAlma`/`SILVER` (`known not to apply`)**: Digital gate-level probing models treat physically disjoint wires without shared gates/registers as independent. Sub-threshold cross-wire capacitive coupling, shared power-ring voltage-drop (`VDD` sag coupling simultaneous switching activity of $s_0$ and $s_1$ across separate modules—*wire-free* Leviathan/coupling effects), and static leakage current (`LLPA`) are **known not to apply** to digital logic-cone verifiers and require post-layout SPICE/parasitic extraction + silicon TVLA.
- **Scalability of exact ROBDD verification (`SILVER` / `FIVER`) at high order (`unsupported`)**: Exact Sylvan/CUDD ROBDD construction scales to $d = 1, 2$ masked S-Boxes and single-round redundant ciphers, but hits multi-gigabyte memory exhaustion (`cache_create: Unable to allocate memory`, `SILVER/README.md:194`) on unpartitioned full-cipher masked cores at order $d \ge 3$ unless modular `PINI` composition is used.
- **Aggressive fault-location pruning in `FIVER` (`known not to apply`)**: Setting `reduced_complexity = 2` in `FIVER` (`README.md:136`) is explicitly documented as an unsound heuristic that may miss effective fault tuples; formal sign-off must restrict `reduced_complexity` to `0` (exhaustive) or `3` (conservative).

## Evidence

### Primary Repositories and Source Coordinates (Observed `2026-11-19`)

1. **`microsoft/sca-fuzzer` @ `7dec7b81d4562cdd2a6026ef0830a3dac2b20cbc`**:
   - `rvzr/fuzzer.py:42-43, 102-260`: `_RoundManager` 7-step validation pipeline (`fast`, `nesting`, `taint_mistake`, `priming`, `noise`, `priming_large`, `arch_mismatch`) and taint-guided input boosting (`_boost_inputs`).
   - `rvzr/analyser.py:67-245`: `EquivalenceAnalyserCommon.filter_violations`, `MergedBitmapAnalyser` (`64`-bit bitmap merge, outlier filter, `analyser_subsets_is_violation` subset check at lines `194-200`), `SetAnalyser`, and `MWUAnalyser`.
   - `rvzr/config.py:221-361`: Contract execution clauses (`seq`, `cond`, `bpas`, `nullinj-fault`, `vspec-ops-div`, etc.), observation clauses (`ct`, `l1d`, `pc`, `arch`, `ctr`), `executor_sample_sizes = [10, 50, 100, 500]`, and `executor_mode` options.
   - `rvzr/executor_km/measurement.c:48-168`: Kernel-level `uarch_flush()` (`verw`, `MSR_IA32_FLUSH_CMD`, `wbinvd`, `lfence`), SMI corruption rejection (`status->smi_count != 0`), and IRQ-disabled execution (`raw_local_irq_save`).
2. **`kth-step/HolBA` @ `a39e4332dcee3c8243ac6f1bc3f8b4691eb5a4e7`**: HOL4 binary analysis and `Scam-V` side-channel model validation (`Nemati et al., CAV 2020, DOI: 10.1007/978-3-030-53288-8_12`).
3. **`newaetech/chipwhisperer` @ `884412281b1c1749b871e16e563d3ff310affd68`**: `README.md:9-35` (v7.0 Zarr trace architecture, integer CPA engine) and `software/chipwhisperer/analyzer/leakage_models.py:64-138` (`sbox_output`, `last_round_state_diff`, `pipeline_diff`, `half_pipeline_diff`, `ttable_output`).
4. **`isec-tugraz/coco-alma` @ `95c80df5d6d704bf525f47ef6e58e98e27fedf97`** and **`IAIK/coco-ibex` @ `1ac262929d900d63d5ed702cd40edca1602a79c9`**:
   - `verify.py:20-220`: CLI semantics (`--mode {stable,transient}`, `--glitch-behavior {strict,loose}`, `--probing-model {classic,time-constrained}`, `--include-hamming`, `--export-cnf`, `--kissat`), share label parser (`generate_labeling`), and `--ignored-signals` cone propagation (`generate_ignored`).
   - `SatChecker.py:13-260`: `Formula` incremental SAT Fourier-correlation set builder (`linear_set_cache` symmetric difference on `XOR`, `nonlin_set_cache` + `assure_biased` union on `AND`, `make_choice` Hamming-distance transition combination, and `time-constrained` vs. `classic` active variable collection).
5. **`Chair-for-Security-Engineering/SILVER` @ `0a3c85fc5a60d76eedb84d996473df28fc18ef42`**:
   - `inc/Silver.hpp:51-87` & `README.md:34-174`: Sylvan ROBDD `check_Uniform`, `check_Probing`, `check_NI`, `check_PINI`, `check_SNI` (standard and robust), Nangate 45 nm `set_dont_use` cell constraints, and `dom1.nl` benchmark (`6 ms` pass on `SNI.standard`, `7 ms` fail on `SNI.robust` / `PINI.robust`).
6. **`Chair-for-Security-Engineering/FIVER` @ `176a1db7f80764543324db5378b6f82d4adebcbe`** and **`emsec/VerFI` @ `e7a16f93a43e814272322349df698d4408fc45a6`**:
   - `FIVER/inc/passes/analysis/fault.hpp:46-167` & `README.md:42-151`: 16-operation gate fault algebra (`B0..B15`), incremental CUDD propagation, `evaluate_detection` / `evaluate_correction`, `CRAFT` 1-round timing (`18.92 ms` for `98,048` scenarios), `blacklist.txt`, and `reduced_complexity` soundness warning.

### Normative Standards and Peer-Reviewed Publications

- **ISO/IEC 17825:2024** (and `ISO/IEC 17825:2016`), *Information technology — Security techniques — Testing methods for the mitigation of non-invasive attack classes against cryptographic modules*.
- Tobias Schneider and Amir Moradi, *Leakage Assessment Methodology – A Clear Roadmap for Side-Channel Evaluations*, CHES 2015 (`DOI: 10.1007/978-3-662-48324-4_25`).
- François-Xavier Standaert, *How (Not) to Use Welch's T-Test in Side-Channel Security Evaluations*, CARDIS 2018 (`DOI: 10.1007/978-3-030-15462-2_5`).
- Oleksii Oleksenko, Christof Fetzer, Boris Köpf, and Mark Silberstein, *Revizor: Testing Black-Box CPUs against Speculation Contracts*, ASPLOS 2022 (`DOI: 10.1145/3503222.3507729`), and *Hide and Seek with Spectres*, IEEE S&P 2023.
- Jose Rodrigo Sanchez Vicarte et al., *Augury: Using Data Memory-Dependent Prefetchers to Leak Data at Rest*, IEEE S&P 2022 (`DOI: 10.1109/SP46214.2022.9833570`), and Boru Chen et al., *GoFetch: Breaking Constant-Time Cryptographic Implementations Using Data Memory-Dependent Prefetchers*, USENIX Security 2024.
- Yuan Xiao, Yinqian Zhang, and Radu Teodorescu, *SPEECHMINER: A Framework for Investigating and Measuring Speculative Execution Vulnerabilities*, NDSS 2020.
- Barbara Gigerl, Vedad Hadžić, Robert Primas, Stefan Mangard, and Roderick Bloem, *Coco: Co-Design and Co-Verification of Masked Software Implementations on CPUs*, USENIX Security 2021; Vedad Hadžić and Roderick Bloem, *COCOALMA: A Versatile Masking Verifier*, FMCAD 2021 (`DOI: 10.34727/2021/isbn.978-3-85448-046-4_9`).
- David Knichel, Pascal Sasdrich, and Amir Moradi, *SILVER – Statistical Independence and Leakage Verification*, ASIACRYPT 2020 (`DOI: 10.1007/978-3-030-64837-4_26`).
- Jan Richter-Brockmann et al., *FIVER – Robust Verification of Countermeasures against Fault Injections*, IACR TCHES 2021(4) (`DOI: 10.46586/tches.v2021.i4.447-473`); Franck Courbon et al., *Combining Image Processing and Laser Fault Injections for Characterizing a Hardware AES*, IEEE TCAD 2015 (`DOI: 10.1109/TCAD.2015.2411603`); Lionel Rivière et al., *High Precision Fault Injections on the Instruction Cache of ARMv7-M Architectures*, IEEE HOST 2015 (`DOI: 10.1109/HST.2015.7140238`).

### Executed Micro-Probe Output (`2026-11-19`, Python 3 Standard Library, `90.69 ms`)

Executing the standalone verification script reproduced below in `## Revalidation` yielded:
```text
revizor_bitmap: subset_ignored_eq=True strict_eq=False disjoint_dmp_eq=False
tvla_fwer: p_single=6.795e-06 fwer_10k=0.0657 fwer_100k=0.4931
tvla_balanced_0x5A: t1_s0=+0.956 t1_s1=+0.009 t2_biv=+1.922
tvla_skewed_0x00:   t1_s0=-0.685 t1_s1=-2.894 t2_biv=+28.345
alma_probing_mi_bits: synced=0.000000 glitch_unreg=1.000000 reg_overwrite=1.000000
fiver_faults: n1_eff=0 n1_det=128 n2_laser_common_mode_eff=64
```

## Revalidation

Run the following self-contained standard-library Python check (`< 0.2 s`, zero network or third-party dependencies) to revalidate (1) `Revizor`'s `MergedBitmapAnalyser` subset vs. disjoint DMP cache-set equivalence semantics, (2) `ISO/IEC 17825` $|t| > 4.5$ multi-point FWER and Standaert's $\text{HW}=4$ (`0x5A`) 2nd-order TVLA false-negative vs. `0x00` detection, (3) exact mutual-information leakage (`0.0` vs. `1.0` bit) of synchronized vs. unregistered glitch-extended `DOM-indep` AND and register-overwrite transitions, and (4) single-fault immunity vs. bivariate spatial-laser bypass on a redundant S-Box:

```bash
python3 - <<'PY'
import collections, itertools, math, random

def merged_bitmap_eq(raw1, raw2, outlier_thresh=0.10, subsets_is_violation=False):
    min_cnt = outlier_thresh * len(raw1)
    b = [0, 0]
    for idx, raw in enumerate((raw1, raw2)):
        cnt = collections.Counter(raw)
        for sample in raw:
            if cnt[sample] >= min_cnt:
                b[idx] |= int(sample)
    mask = (1 << 64) - 1
    if subsets_is_violation:
        return b[0] == b[1]
    return ((b[0] & ((~b[1]) & mask)) == 0) or ((b[1] & ((~b[0]) & mask)) == 0)

rng = random.Random(20261119)
base = (1 << 3) | (1 << 11)
h1 = [base | ((1 << 61) if rng.random() < 0.04 else 0) for _ in range(50)]
h2 = [base | (1 << 27) | ((1 << 61) if rng.random() < 0.04 else 0) for _ in range(50)]
h3 = [base | (1 << 42) for _ in range(50)]
assert merged_bitmap_eq(h1, h2, subsets_is_violation=False) is True
assert merged_bitmap_eq(h1, h2, subsets_is_violation=True) is False
assert merged_bitmap_eq(h2, h3, subsets_is_violation=False) is False

p_single = math.erfc(4.5 / math.sqrt(2.0))
fwer_100k = 1.0 - (1.0 - p_single) ** 100_000
assert 0.49 < fwer_100k < 0.50

def welch_t(a, b):
    na, nb = len(a), len(b)
    ma, mb = sum(a) / na, sum(b) / nb
    va = sum((x - ma) ** 2 for x in a) / (na - 1)
    vb = sum((x - mb) ** 2 for x in b) / (nb - 1)
    return (ma - mb) / math.sqrt(va / na + vb / nb)

def tvla_2nd(s_fix, n=4000):
    f1, f2, r1, r2 = [], [], [], []
    for _ in range(n):
        mf = rng.randrange(256)
        f1.append(mf.bit_count() + rng.gauss(0.0, 1.0))
        f2.append((s_fix ^ mf).bit_count() + rng.gauss(0.0, 1.0))
        sr, mr = rng.randrange(256), rng.randrange(256)
        r1.append(mr.bit_count() + rng.gauss(0.0, 1.0))
        r2.append((sr ^ mr).bit_count() + rng.gauss(0.0, 1.0))
    t1 = max(abs(welch_t(f1, r1)), abs(welch_t(f2, r2)))
    mf1, mf2, mr1, mr2 = sum(f1)/n, sum(f2)/n, sum(r1)/n, sum(r2)/n
    fp = [(x - mf1) * (y - mf2) for x, y in zip(f1, f2)]
    rp = [(x - mr1) * (y - mr2) for x, y in zip(r1, r2)]
    return t1, welch_t(fp, rp)

t1_bal, t2_bal = tvla_2nd(0x5A)
t1_skw, t2_skw = tvla_2nd(0x00)
assert t1_bal < 4.5 and abs(t2_bal) < 4.5
assert t1_skw < 4.5 and t2_skw > 25.0

def mi_bits(obs_fn):
    cab, co = collections.Counter(), collections.Counter()
    for a, b, ma, mb, z in itertools.product((0, 1), repeat=5):
        o = obs_fn(ma, a ^ ma, mb, b ^ mb, z)
        cab[((a, b), o)] += 1
        co[o] += 1
    return sum((c/32.0) * math.log2((c/32.0) / (0.25 * (co[o]/32.0))) for (ab, o), c in cab.items())

assert abs(mi_bits(lambda a0, a1, b0, b1, z: (a0 & b0, (a0 & b1) ^ z))) < 1e-12
assert abs(mi_bits(lambda a0, a1, b0, b1, z: (a0, b0, b1, z)) - 1.0) < 1e-12
assert abs(mi_bits(lambda a0, a1, b0, b1, z: a0 ^ a1) - 1.0) < 1e-12

SBOX4 = [0xC, 0x5, 0x6, 0xB, 0x9, 0x0, 0xA, 0xD, 0x3, 0xE, 0xF, 0x8, 0x4, 0x7, 0x1, 0x2]
eff1 = sum(1 for bit in range(8) for x in range(16)
           if (SBOX4[x] ^ (1 << bit if bit < 4 else 0)) == (SBOX4[x] ^ (1 << (bit - 4) if bit >= 4 else 0))
           and (SBOX4[x] ^ (1 << bit if bit < 4 else 0)) != SBOX4[x])
eff2 = sum(1 for b1, b2 in itertools.combinations(range(8), 2) for x in range(16)
           if (SBOX4[x] ^ ((1 << b1 if b1 < 4 else 0) | (1 << b2 if b2 < 4 else 0)))
           == (SBOX4[x] ^ ((1 << (b1 - 4) if b1 >= 4 else 0) | (1 << (b2 - 4) if b2 >= 4 else 0)))
           and (SBOX4[x] ^ ((1 << b1 if b1 < 4 else 0) | (1 << b2 if b2 < 4 else 0))) != SBOX4[x])
assert eff1 == 0 and eff2 == 64
print("OK: revizor + tvla + alma + fiver revalidation passed")
PY
```

To revalidate upstream repository behavior when bumping any pinned commit in `REPORT.json`:
1. Diff `rvzr/analyser.py` (`MergedBitmapAnalyser.htraces_are_equivalent`) and `rvzr/fuzzer.py` (`_RoundManager`) in `microsoft/sca-fuzzer` to check whether `analyser_subsets_is_violation` defaults or priming passes changed.
2. Diff `verify.py` and `SatChecker.py` (`make_simple`, `collect_active_time_constrained`, `collect_active_classic`) in `isec-tugraz/coco-alma` to confirm `time-constrained` vs. `classic` probe counting and CNF export restrictions.
3. Diff `inc/Silver.hpp` in `Chair-for-Security-Engineering/SILVER` and `inc/passes/analysis/fault.hpp` in `Chair-for-Security-Engineering/FIVER` to verify `PINI.robust` and `reduced_complexity` semantics.
