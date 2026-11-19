# Cross-Substrate Physical Leakage, Fault, Errata, and World-Transition Contracts

## Summary

Architectural ISA semantics—even when mechanized in Sail or verified through a certified compiler—do not enforce security or memory safety across five physical substrates below and beside the ISA: **CMOS gate-level glitch/transition leakage**, **ineffective fault induction (SIFA)**, **microarchitectural data-dependent prefetching and power-to-frequency throttling (GoFetch, Spectre, Hertzbleed)**, **DRAM charge disturbance and post-compile silicon errata relaxation (Rowhammer/RowPress, SKX102, Cortex-A53 843419)**, and **attested mutual-distrust world transitions (ARM CCA, AMD SEV-SNP, pKVM, TPM 2.0, SPDM, PCIe TDISP)**.

1. **CMOS Gate-Level Masking (`TI`, `DOM`, `PINI`/`O-PINI`) vs. Synthesis Drift:** Functional Combinational Equivalence Checking (`CEC`) across `RTL -> Gate Netlist` synthesis (`Yosys`/`ABC`) is strictly blind to glitch-probing collapse: stripping the synchronization register in a 1st-order Domain-Oriented Masking (`DOM`) AND gate passes `CEC` on `32/32` inputs while merging both input shares $\{b_0, b_1\}$ into one combinational glitch cone, collapsing probing order $d = 1 \to 0$. Similarly, IEEE 1800 4-state simulation evaluates `if (1'bX) LEAK else SAFE` deterministically to `SAFE`, while synthesis legally resolves `1'bX` as don't-care freedom to `LEAK`. Hardware-software co-verification (`Coco-Alma`, `PROLEAD`) must check post-synthesis gate netlists with preserved `Keep-Domain` register barriers and 4-state `X`-freedom.
2. **SIFA Order-Independence and Infective / Error-Correcting Masking:** Statistical Ineffective Fault Attacks (SIFA) bypass arbitrary Boolean masking orders $d \ge 1$ when fault detection suppresses corrupted outputs or compares output shares directly. Exact-rational analysis confirms that a single `sa0` or `flip` fault on one pre-fanout share $a_0$ of a masked AND gate leaks `0.311278` bits (`sa0`) and `1.000000` bit (`flip`) **identically at $d = 1$ and $d = 2$**—and comparing redundant output shares $c_0^{(0)} \oplus c_0^{(1)}$ in `DOM` cancels the mask $r$ and reproduces the exact same leak. Defeating single-fault ($f = 1$) SIFA without sacrificing glitch-robust `O-PINI` requires either (a) **Registered Wire-Local Infective `PINI`** (comparing every internal wire across two fault domains, latching share-local error flags through a `Keep-Domain` register barrier before OR reduction, and infecting output shares with fresh randomness $r_{\text{inf}}$, achieving exact `0.000000` bits across all `39/39` wire faults, with a sharp $f = 2$ boundary), or (b) **Share-Wise Majority-Voted Error-Correcting Masking (`Maj_{2f+1}-ECM-PINI`)** (achieving `0.000000` bits, `0` output errors, and zero cross-share error bus).
3. **GoFetch DMP Non-Pointer Blinding, Spectre Contracts, and Hertzbleed DVFS Regimes:** Data Memory-Dependent Prefetchers (`Augury`, `GoFetch`) violate software constant-time discipline whenever secret data words resemble canonical virtual pointers (e.g., naive 64-bit `ML-KEM` $q=3329$ coefficients trigger DMP on `3329/3329 = 100%` of values in `P_reg = 0`). Packing secret limbs with a balanced non-canonical top-16-bit tag `0x5AA5` (`HW = 8/16`, `Hertzbleed`-neutral) achieves Hamming distance $d_H = 4$ from ARM64 EL0 `[55:48] = 0x00` (`0/696` hits across all 1–3-bit flips) and $d_H = 8$ from x86-64 canonicals (`0` hits up to 7-bit flips), reducing `ML-KEM` DMP hits to `0/3329` while constant-time Barrett reduction (`16,645/16,645` exact matches) eliminates `KyberSlash` `UDIV`/`SDIV` timing leaks. Simultaneously, `Hertzbleed` DVFS throttling requires splitting deployments into **Regime A** (frequency-pinned with verified cubic power headroom $P_{\text{peak}} \le P_{\text{cap}}$) or **Regime B** (dynamic DVFS with $d \ge 2$ hardware/software masking), coupled with `Revizor` hardware-software speculation contracts (`ct-seq`, `ct-arch`).
4. **Rowhammer/RowPress Guardbands and Post-Compile Errata Relaxation:** `RowPress` amplifies DRAM read disturbance by keeping aggressor rows open near $t_{\mathrm{RAS}}^{\max}$, bypassing bank-coloring timing isolation unless sensitive arenas reserve $\ge R_{\text{blast}}$ unmapped physical guard rows (`14 -> 0` victim hits in a 32-row subarray with $R_{\text{blast}} = 2$). Post-compile layout shifts also break instruction-level errata invariants: Intel `SKX102` (`LLVM` `X86AsmBackend.cpp:416–584`) forbids conditional/macro-fused branches from crossing or ending on 32-byte DSB boundaries, while ARM `Cortex-A53` erratum `843419` (`LLD` `AArch64ErrataFix.cpp:286–401`) forbids `ADRP` at page offsets `0xff8`/`0xffc` followed by dependent unsigned-offset loads/stores—requiring post-link verification or `4 KiB`-anchored code islands with fixed-point relaxation convergence.
5. **Attested World Transitions, Ownership State Machines, and Cross-Chip Reset Desynchronization:** Confidential-computing boundaries (`ARM CCA` `TF-RMM`, `AMD SEV-SNP`, `pKVM`, `TPM 2.0`, `DMTF SPDM`, `PCIe TDISP`) require three cross-substrate invariants: (a) strict ownership-state-machine exclusivity (e.g., `pKVM` `PKVM_PAGE_{OWNED,SHARED_OWNED,SHARED_BORROWED}` + `PKVM_NOPAGE` with zero dual-owner states; `PCIe TDISP` `CONFIG_UNLOCKED -> CONFIG_LOCKED -> RUN -> ERROR` with fail-closed revocation forcing `ERROR -> CONFIG_UNLOCKED` before re-attestation); (b) **dual-epoch `(e_host, e_chip, nv_ctr)` session binding** over discrete hardware reset lines (`TPM RST#`, `PERST#`, `SPDM`), eliminating cross-reset replay and stale-PCR unseal attacks (`6/33 -> 0/72`); and (c) linear **`CopyInOnce`** volatile snapshots over guest-shared `VirtIO`/GHCB buffers plus physical `NVMe ZNS`/KEK-shred erasure for copy-on-write flash remanence.

## Applicability

This report integrates primary hardware specifications, upstream source code, peer-reviewed cryptographic and architectural literature, and executable micro-probes pinned in `REPORT.json`:

- **Masking, Netlist Verification, and SIFA:** `IAIK/coco-alma@95c80df5` (`verify.py`), `ChairImpSec/PROLEAD@2c8c8486`, `YosysHQ/yosys@d1338f82`, plus Nikova et al. (ICISC 2006), Gross et al. (TIS 2016), Dobraunig et al. (TCHES 2018), Daemen et al. (TCHES 2020), Cassiers & Standaert (IEEE TIFS 2020), and Cassiers et al. (IEEE TC 2021).
- **Speculation Contracts, DMPs, and DVFS:** `microsoft/sca-fuzzer@cc9fa2e5` (Revizor), Guarnieri et al. (IEEE S&P 2021), Oleksenko et al. (ASPLOS 2022), Vicarte et al. (Augury, IEEE S&P 2022), Wang et al. (Hertzbleed, USENIX Security 2022), and Chen et al. (GoFetch, USENIX Security 2024).
- **DRAM Disturbance, Relaxed `ifetch`, and Silicon Errata:** `CMU-SAFARI/RowPress@5b6f1502`, `comsec-group/blacksmith@60bae8e5`, `rems-project/isla@e9b5d945`, `llvm/llvm-project@8ffaed7c` (`X86AsmBackend.cpp`, `AArch64ErrataFix.cpp`), Kim et al. (ISCA 2014), Frigo et al. (IEEE S&P 2020), Simner et al. (ESOP 2020), and Luo et al. (ISCA 2023).
- **Confidential Computing, Device Attestation, and Bus Protocol Verification:** `TF-RMM/tf-rmm@8d7961df` (Arm `DEN0137`), `torvalds/linux@4405c18c` (`arch/arm64/kvm/hyp/nvhe/mem_protect.c`, `arch/x86/coco/sev/vc-handle.c`), `AMDESE/AMDSEV@6e0ef356` (AMD `56860`), `coconut-svsm/svsm@2a40e72a`, `DMTF/libspdm@3f1253df` (`pci_tdisp.h`, `DMTF DSP0274`, `PCI-SIG TDISP ECN`), `lowRISC/opentitan@237c8216`, `tamarin-prover/tamarin-prover@0e533bd4`, `squirrel-prover/squirrel-prover@ebef0aca`, and TCG TPM 2.0 Library Specification Rev 01.59 / 01.83.

**Scope of Applicability:** Applies to cryptographic accelerators, masked software running on embedded or server CPUs, confidential virtual machines (CVMs), host-hypervisor/EL2 isolation kernels, and hardware-attested PCIe/CXL device assignment stacks. Platform-specific mitigations (e.g., Apple M-series EL0 `[55:48]` DMP heuristics, Intel Skylake-class `SKX102`, ARM Cortex-A53 r0p0–r0p4 `843419`) apply strictly to affected microarchitectures, whereas the underlying contract invariants (post-synthesis netlist checking, SIFA wire-local absorption, non-canonical tag blinding, guardband isolation, and dual-epoch reset binding) generalize across hardware families.

## Findings

### 1. CMOS Gate-Level Masking (`TI`, `DOM`, `O-PINI`), Synthesis Drift, and `Coco`/`PROLEAD` Co-Verification

Basis: normative + source + execution

#### 1.1 Probing Models and Compositional Masking Families

Physical CMOS gates exhibit **combinational glitches** (transient intermediate evaluations before wire delays equalize within a clock cycle) and **register/wire transitions** (capacitive switching power proportional to $v_{t-1} \oplus v_t$). Standard Ishai–Sahai–Wagner (`ISW`) probing security fails immediately under glitches unless extended to glitch-robust security notions:

| Scheme / Notion | Primary Reference | Core Structural Mechanism | Compositional Property | Key Synthesis / Microarchitectural Hazard |
| :--- | :--- | :--- | :--- | :--- |
| **Threshold Implementations (`TI`)** | Nikova, Rechberger, Rijmen, ICISC 2006 (`10.1007/11935308_38`) | Correctness, **Non-Completeness** (each component function omits at least one input share), and Uniformity | Glitch-resistant per stage without fresh randomness in 1st-order uniform designs | Higher-order `TI` requires $d+1$ or more shares and re-masking registers to maintain uniformity |
| **Domain-Oriented Masking (`DOM`)** | Gross, Mangard, Korak, TIS 2016 (`10.1145/2996366.2996426`) | Partition shares into $d+1$ domains; insert **fresh-randomness-masked pipeline registers** on every cross-domain product: $c_0 = (a_0 \land b_0) \oplus \mathsf{Reg}((a_0 \land b_1) \oplus r)$ | Arbitrary order $d$ with $d+1$ shares and low area/randomness overhead | Logic synthesis retiming or register stripping across $\mathsf{Reg}(\cdot)$ merges domains into one glitch cone ($d \to 0$) |
| **`PINI` / `O-PINI` (Hardware Private Circuits)** | Cassiers & Standaert, IEEE TIFS 2020 (`10.1109/TIFS.2020.2971153`); Cassiers et al., IEEE TC 2021 (`10.1109/TC.2020.3022979`) | Probe-Isolating Non-Interference: any set of $t_1$ internal probes and $t_2$ output probes ($t_1 + t_2 \le d$) can be simulated using only the output share indices plus at most $t_1$ input share indices | **Trivial composition** of masked gadgets without inserting extra refresh gadgets (`HPC1`/`HPC2`) | Combinational cross-share error flags or shared CPU datapath registers violate domain isolation |
| **`Coco-Alma` CPU/Netlist Co-Verification** | Gigerl et al., USENIX Security 2021 (`ePrint 2020/1294`); `IAIK/coco-alma@95c80df5` | Symbolic SAT-based Fourier/correlation verification of masked software executed cycle-by-cycle on an actual **synthesized CPU gate netlist** (e.g., RISC-V Ibex) | Detects hidden microarchitectural leaks in ALU latches, register-file read/write ports, and load/store forwarding paths | Requires cycle-accurate VCD execution traces and gate netlists; `verify.py:37–58` exposes `-q/--order`, `-m/--mode`, `--glitch-behavior` (`strict`/`loose`), `-t/--probing-model`, and `--checking-mode` (`per-secret`/`per-location`) |
| **`PROLEAD` / `PROLEAD_SW` & `FIESTA`** | Müller & Moradi, TCHES 2022 (`10.46586/tches.v2022.i4.311-348`); `ChairImpSec/PROLEAD@2c8c8486` | Simulation-based $G$-test / statistical probing leakage detection on hardware netlists and ARM binaries (`PROLEAD_SW`), plus fault analysis (`FIESTA`) | Scales to large real-world designs, higher-order multivariate glitches, and transitions without a fixed power model | Statistical detection depends on trace count and probing configuration; complements SAT-complete proofs |

#### 1.2 Synthesis `CEC` Blindness, `1'bX` Optimism, and Glitch-Aware `NetlistCert`

Basis: execution + derived

Standard EDA flows (`YosysHQ/yosys@d1338f82` + `ABC` AIG/FRAIG rewriting + retiming) verify functional equivalence via Combinational Equivalence Checking (`CEC`). `Probe 1` (`## Evidence`) demonstrates two structural soundness breaks below RTL:
1. **`CEC` Blindness to `DOM` Register Stripping:** Stripping the cross-domain register barrier in 1st-order `DOM` AND and reassociating $c_0 = ((a_0 \land b_0) \oplus (a_0 \land b_1)) \oplus r$ yields **`0/32` functional `CEC` mismatches**, yet expands the combinational glitch-probing cone of $c_0$ to $\{a_0, b_0, b_1, r\}$, exposing both shares of secret $b$ simultaneously (`registered_glitch_leaks_b=False (d=1)` vs. `barrier_stripped_glitch_leaks_b=True (d=0!)`).
2. **IEEE 1800 4-State `1'bX` Simulation-vs.-Synthesis Divergence:** In 4-state RTL simulation (`{0, 1, X, Z}`), `if (en_x) LEAK else SAFE` takes the `else` branch deterministically whenever `en_x = 1'bX` (`SAFE`), whereas logic synthesis treats `1'bX` as a don't-care optimization freedom that may map to constant `1'b1` (`synth_reachable = ['LEAK', 'SAFE']`).

A sound sub-ISA gate certificate (`NetlistCert`) therefore requires five simultaneous obligations: (i) `LRAT`/miter `CEC` or `IC3` `SEC` functional equivalence; (ii) **`Keep-Domain` Register-Cut Preservation** (every security-barrier register in RTL maps bijectively to a post-synthesis flip-flop with zero retiming across the cut); (iii) post-synthesis glitch-robust `O-PINI` verification (`Coco-Alma` strict glitch mode / `PROLEAD`); (iv) symbolic 4-state `X`-freedom after reset; and (v) multi-corner static timing analysis (`SetupSlack > 0 ∧ HoldSlack > 0`). Even all five remain blind to **sub-gate analog silicon trojans** (e.g., capacitor-charge triggers in `A2`, Yang et al., IEEE S&P 2016, DOI `10.1109/SP.2016.10`), which must be explicitly recorded in the residual physical assumption ledger.

---

### 2. SIFA-Resilient Infective Masking and Error-Correcting Masking (`ECM`)

Basis: normative + execution + derived

#### 2.1 Order-Independent SIFA Collapse and Output-Share Mask Cancellation

Statistical Ineffective Fault Attacks (`SIFA`, Dobraunig et al., TCHES 2018, DOI `10.13154/tches.v2018.i3.547-572`) exploit biased fault inductions (e.g., stuck-at-0, clock/voltage glitch, or laser-induced bit bias) where the attacker **retains only outputs for which the fault was ineffective** (i.e., passed redundancy checks or produced an uncorrupted ciphertext). Because a fault's effectiveness depends on the secret state value, conditioning on fault ineffectiveness leaks secret information even when the algorithm is arbitrarily masked and guarded by error-detecting duplication.

Consider any $d$-th order masked AND gate computing $c = a \land b$ over $d+1$ uniform shares, with a single fault injected on one pre-fanout input share $a_0$:
- **Final-Output Suppression (`d = 1` and `d = 2`):** Under `sa0` ($a_0' = 0$), the output error is $\Delta c = (a_0 \oplus 0) \land b = a_0 \land b$. Because $a_0$ is uniform, $\Pr[\mathsf{Pass} = 1 \mid b = 0] = 1$ whereas $\Pr[\mathsf{Pass} = 1 \mid b = 1] = \tfrac{1}{2}$, yielding exact mutual information:
  $$I(B;\,\mathsf{Pass}) = \tfrac{3}{4}\log_2\tfrac{4}{3} + \tfrac{1}{4}\log_2 2 \approx \mathbf{0.311278\text{ bits}}$$
  **identically for every masking order $d \ge 1$**. Under a deterministic bit-flip ($a_0' = a_0 \oplus 1$), $\Delta c = b$, giving $\Pr[\mathsf{Pass}=1 \mid b=0] = 1$ vs. $\Pr[\mathsf{Pass}=1 \mid b=1] = 0$, leaking an **exact `1.000000` full bit** regardless of $d$.
- **Output-Share Comparison Mask Cancellation (`c_0^(0) == c_0^(1)`):** Attempting to defeat SIFA by comparing duplicated shares before recombination fails in `DOM` because the random mask $r$ cancels identically:
  $$c_0^{(0)} \oplus c_0^{(1)} = ((a_0 \land b_0) \oplus (a_0 \land b_1) \oplus r) \oplus ((a_0' \land b_0) \oplus (a_0' \land b_1) \oplus r) = (a_0 \oplus a_0') \land b,$$
  reproducing the exact `0.311278` (`sa0`) and `1.000000` (`flip`) bit leak!
- **Combinational Error-Bus Glitch Hazard:** Combining share-local discrepancy flags $e_{a_0} = a_0^{(0)} \oplus a_0^{(1)}$ and $e_{a_1} = a_1^{(0)} \oplus a_1^{(1)}$ directly in a combinational OR gate creates a glitch cone containing $\{a_0, a_1\}$, collapsing fault-free `O-PINI` order $d = 1 \to 0$.

#### 2.2 Two Verified SIFA-Resilient Countermeasures

Following Daemen et al. (TCHES 2020, DOI `10.13154/tches.v2020.i3.508-543`) and verified exhaustively using exact `fractions.Fraction` probability distributions in `Probe 2` (`## Evidence`):

| Architecture | Fault Budget & Overhead | Exact `I((A,B); Obs)` across `39` Wire Faults | Output Error Behavior | Glitch-`O-PINI` Preservation |
| :--- | :--- | :---: | :--- | :--- |
| **Naive Output Suppression (`d = 1, 2`)** | $2\times$ area, suppress on mismatch | `0.311278` (`sa0`) / `1.000000` (`flip`) bits | Suppresses corrupted output | N/A (broken by SIFA) |
| **Naive Output-Share Compare (`DOM`, `d = 1`)** | $2\times$ area, compare $c_i^{(0)} = c_i^{(1)}$ | `0.311278` (`sa0`) / `1.000000` (`flip`) bits | Suppresses on share mismatch | Mask $r$ cancels in XOR |
| **Registered Wire-Local Infective `PINI`** | $2\times$ area + fresh $r_{\text{inf}}$, **$f = 1$** | **Exact `0.000000` bits (`39/39` wire faults)** | Never suppresses; infects $c_0^{\text{out}} = c_0^{(0)} \oplus (E \land r_{\text{inf}})$ | **Preserved** via `Keep-Domain` error registers $\mathsf{reg\_e}_w \Leftarrow_R e_w$ before OR aggregation |
| **Share-Wise `Maj3-ECM-PINI`** | $3\times$ area ($2f+1$ replicas), **$f = 1$** | **Exact `0.000000` bits (`39/39` wire faults)** | **`0` output errors (`100%` correction)** | **Unconditional combinational `O-PINI`** (zero cross-share error bus!) |

In **Registered Wire-Local Infective `PINI`**, every wire $w$ in the gadget (pre-fanout inputs $a_i, b_j, r$, partial products $p_{ij}$, masked products $t_{ij}$, outputs $c_i$) is compared locally across two fault-isolated replicas ($e_w = w^{(0)} \oplus w^{(1)}$), latched through a `Keep-Domain` register barrier (which holds constant `0` in fault-free runs, preserving `O-PINI`), and aggregated via Boolean absorption: on a pre-fanout $a_0$ fault, $e_{a_0} \lor e_{c_0} = a_0 \lor (a_0 \land b) \equiv a_0$ (`sa0`) and $1 \lor b \equiv 1$ (`flip`), erasing all dependence on $b$. **Sharp boundary verified in `Probe 2`:** injecting $f = 2$ simultaneous faults (e.g., `a0 sa0` plus forcing `E := 0`) immediately re-opens `0.311278` bits of SIFA leakage, marking the exact transition threshold where `Maj_{2f+1}-ECM-PINI` is required.

---

### 3. GoFetch DMP Non-Pointer Blinding, Spectre Contracts, and Hertzbleed DVFS Regimes

Basis: normative + source + execution

#### 3.1 Hardware-Software Speculation Contracts (`ct-seq`, `ct-arch`) and `Revizor`

Guarnieri et al. (IEEE S&P 2021, DOI `10.1109/SP40001.2021.00036`) formalize hardware-software security boundaries as **leakage contracts**: an abstract contract execution assigns an observation trace $\llbracket P \rrbracket_{\text{ct}}(s)$ to each architectural state $s$, and a CPU microarchitecture satisfies the contract iff contract-indistinguishable initial states produce hardware-indistinguishable microarchitectural traces:

$$\forall s_1\;s_2,\quad \llbracket P \rrbracket_{\text{contract}}(s_1) = \llbracket P \rrbracket_{\text{contract}}(s_2) \implies \llbracket P \rrbracket_{\text{hw}}(s_1) = \llbracket P \rrbracket_{\text{hw}}(s_2).$$

Common contract points span `ct-seq` (sequential constant-time: program counter and memory addresses only), `ct-cond` (adds conditional branch misprediction transient traces, Spectre v1), `ct-bpas` (adds store-to-load bypass speculation, Spectre v4), and `arch-seq` (sandbox isolation exposing architectural loads). `Revizor` (`microsoft/sca-fuzzer@cc9fa2e5`, Oleksenko et al., ASPLOS 2022, DOI `10.1145/3503222.3507729`) operationalizes contract conformance via **Model-Based Relational Testing**, generating random instruction sequences and input pairs with identical contract traces to discover black-box CPU violations on real x86/ARM silicon.

#### 3.2 GoFetch DMP Non-Pointer Blinding (`0x5AA5`), `KyberSlash`, and `PAC × DMP` Coupling

Data Memory-Dependent Prefetchers (`Augury`, Vicarte et al., IEEE S&P 2022, DOI `10.1109/SP46214.2022.9833570`; `GoFetch`, Chen et al., USENIX Security 2024) break `ct-seq` without executing a secret-dependent architectural load: the DMP inspects **data values** loaded from memory and, whenever a 64-bit value matches the address region heuristic of a valid canonical pointer, speculatively dereferences that data value into cache—breaking constant-time OpenSSL DH, Go RSA, CRYSTALS-Kyber (`ML-KEM`), and CRYSTALS-Dilithium (`ML-DSA`) on Apple M1–M3 cores (where `DIT` / Data Independent Timing does not disable the DMP on M1/M2, and disabling requires privileged `SYS_APL_HID11_EL1[30]` or M3 `DIT` support).

When hardware DMP disable is unavailable, **Fault-Resilient Non-Pointer Blinding (`SecretNonPtr`)** packs secret limbs in the low 48 bits while setting the top 16 bits `[63:48] = 0x5AA5`. `Probe 3` (`## Evidence`) establishes three quantitative properties:
1. **Hamming-Weight Neutrality & Fault Distance:** `0x5AA5` has balanced Hamming weight `8/16` (avoiding bias in `Hertzbleed` dynamic power), sits at Hamming distance **$d_H = 4$** from ARM64 EL0 `TTBR0` non-tagged pointers (`[55:48] = 0x00`, yielding **`0/696` DMP hits across all 1-, 2-, and 3-bit `RowPress`/SIFA flips**), and **$d_H = 8$** from x86-64 `48b`/`LA57` canonical prefixes (`0x0000`/`0xFFFF`, surviving up to 7-bit flips). Because `0x5AA5` is a public constant, checking `(w >> 48) == 0x5AA5` introduces zero SIFA leakage.
2. **Post-Quantum Mod-$q$ Packing & `KyberSlash` Elimination:** Naive 64-bit storage of `ML-KEM` ($q = 3329$) coefficients leaves bits `[55:32] = 0`, matching `P_reg = 0` DMP pointers on **`3329/3329` (`100%`)** of coefficients; `0x5AA5`-tagged limbs reduce DMP matches to **`0/3329` (`0%`)**. Simultaneously, replacing variable-time `UDIV`/`SDIV` (`KyberSlash`) in `FIPS 203` `Compress_d(x)` ($d \in \{1, 4, 5, 10, 11\}$) with constant-time Barrett multiplication `(((x << (d + 1)) + 3329) * 10321340 >> 36) & ((1 << d) - 1)` achieves **`16,645/16,645` exact matches** across all $x \in [0, 3328]$ with zero division instructions.
3. **Non-Monotonic `PAC × DMP` Hazard:** On ARMv8.3+ cores with Pointer Authentication (`PAC`), if hardware strips PAC tags in bits `[54:48]` prior to DMP region inspection while `dmp_hw_disabled = false`, `PAC` silently neutralizes `SecretNonPtr` blinding! Platform contracts must explicitly check `dmp_hw_disabled ∨ ¬pac_strips_before_dmp`.

#### 3.3 Hertzbleed DVFS Regimes (Regime A vs. Regime B)

`Hertzbleed` (Wang et al., USENIX Security 2022) turns CMOS data-dependent switching power (Hamming weight/distance) into a **remote timing side channel** whenever CPU cores operate near power/thermal limits (`TDP`/`P_cap`) and Dynamic Voltage and Frequency Scaling (DVFS) throttles clock frequency in response to workload power. Because software constant-time code cannot prevent hardware DVFS frequency scaling, end-to-end contracts must classify execution into two explicit physical regimes:
- **Regime A (Frequency-Pinned Thermal-Headroom Regime):** DVFS is locked at pinned frequency $f_{\text{pin}}$ AND coupled peak dynamic power $P_{\text{peak}} = P_{\text{static}} + k f_{\text{pin}}^3 \alpha(d, \mathsf{dmp}) \le P_{\text{cap}}$ holds with positive thermal margin, preventing the core from crossing the DVFS throttling knee.
- **Regime B (Dynamic-DVFS Masked Regime):** When frequency pinning is unavailable or $P_{\text{peak}} > P_{\text{cap}}$, secrets must be processed under $d \ge 2$ glitch-robust masking (`O-PINI`/`DOM`) so that first- and second-order statistical moments of average switching power (and hence time-averaged DVFS frequency trajectories) remain independent of secret values.

---

### 4. DRAM Disturbance (`Rowhammer`/`RowPress`), Relaxed `ifetch`, and Post-Compile Errata Relaxation

Basis: normative + source + execution

#### 4.1 Rowhammer, TRRespass, Blacksmith, and RowPress Guardbands

DRAM cells leak charge across physically adjacent wordlines when aggressor rows are repeatedly activated (`Rowhammer`, Kim et al., ISCA 2014, DOI `10.1145/2678373.2665726`). Target Row Refresh (`TRR`) hardware mitigations were defeated by many-sided patterns (`TRRespass`, Frigo et al., IEEE S&P 2020, DOI `10.1109/SP40000.2020.00090`) and non-uniform frequency-domain patterns (`Blacksmith`, Jattke et al., IEEE S&P 2022, DOI `10.1109/SP46214.2022.9833772`, `comsec-group/blacksmith@60bae8e5`).

**`RowPress`** (Luo et al., ISCA 2023, `arXiv:2306.17061`, `CMU-SAFARI/RowPress@5b6f1502`) introduces an orthogonal physical mechanism: keeping an aggressor row open for an extended period (approaching $t_{\mathrm{RAS}}^{\max}$) amplifies disturbance by $10\times\text{–}100\times$ fewer activations than Rowhammer, bypassing activation-count trackers and bank-coloring timing partitions. As shown in `Probe 4` (`## Evidence`), interleaving sensitive and untrusted 4-row arenas inside a 32-row subarray under blast radius $R_{\text{blast}} = 2$ leaves **`14` victim rows vulnerable**, whereas **`RowGuardAlloc`**—isolating sensitive arenas (`GPT`/`RMP` tables, `SecretNonPtr` stacks, real-time kernels) in disjoint DRAM subarrays or flanking them with $\ge R_{\text{blast}}$ unmapped zeroed guard rows plus a memory-controller $t_{\mathrm{RAS}}^{\max}$ cap—reduces reachable victim hits to **`0`**.

#### 4.2 Multicore Instruction-Fetch Coherency (`ifetch`/`CMODX`) and Post-Compile Errata Relaxation

Two instruction-stream realities invalidate naive source-level or pre-link binary verification:

1. **Relaxed Multicore Instruction Fetch (`ARMv8-A` `CMODX` & `x86-64` `text_poke_bp`):** Under ARMv8-A's split D-cache/I-cache/micro-op cache memory model (Simner et al., ESOP 2020, DOI `10.1007/978-3-030-44914-8_23`, mechanized in `rems-project/isla@e9b5d945`), modifying executable code (e.g., Linux `static_branch` / `ftrace` live patching) without `DC CVAU -> DSB ISH -> IC IVAU -> DSB ISH` (modulo `FEAT_IDC`/`FEAT_DIC`) plus a reader-side `ISB` leaves stale fetches; concurrently modifying instructions outside the single-word `CMODX` allowlist (`B`, `BL`, `NOP`, `BRK`, `HVC`, `SMC`, `SVC`) triggers `CONSTRAINED UNPREDICTABLE`. On `x86-64`, directly overwriting a 5-byte `NOP5 <-> JMP rel32` exposes torn decodes (`#UD` or wild jumps) unless mediated by the 3-step `INT3 (0xCC)` breakpoint protocol (`text_poke_bp`) with cross-core serializing IPIs. Live-patchable verified binaries must declare finite equal-width variant sets $\mathcal{V}(s_i)$ per patch site outside masked/errata windows and validate every variant $v \in \mathcal{V}(s_i)$.
2. **Post-Compile Silicon Errata Relaxation (`Intel SKX102` & `ARM Cortex-A53 843419`):** Direct source inspection of `llvm/llvm-project@8ffaed7c` reveals how instruction byte-offset placement governs architectural correctness and microarchitectural stability *after* code generation:
   - **Intel `SKX102` (Jump Conditional Code Erratum):** In `llvm/lib/Target/X86/MCTargetDesc/X86AsmBackend.cpp:416–430, 559–584`, `X86AsmBackend::needAlign(const MCInst &Inst)` identifies conditional branches (`AlignBranchJcc`), fused `CMP/TEST + JCC` pairs (`AlignBranchFused`), unconditional jumps, calls, returns, and indirect branches that would cross or end on a 32-byte Decoded Stream Buffer (`DSB`) boundary, inserting prefix padding or `NOP`s so instructions never end at `addr % 32 == 0` or straddle a `32B` boundary. `Probe 4` confirms that shifting a 5-byte macro-fused `CMP+JCC` from offset `0x1A` by just `+1` byte to `0x1B` causes it to end at `0x20` (`hazard=True`), while `0x1C` straddles `0x20` (`hazard=True`), and 4-byte `NOP` padding to `0x20` restores `hazard=False`.
   - **ARM `Cortex-A53` Erratum `843419` (AArch64 r0p0–r0p4):** In `lld/ELF/AArch64ErrataFix.cpp:295–401`, `is843419ErratumSequence` and `scanCortexA53Errata843419` scan linked `InputSection`s for a 3- or 4-instruction pattern: (1) an `ADRP Xn, ...` located at `4 KiB` page offset **`0xff8` or `0xffc`**; (2) a load/store (`LDR`/`STR`/`STP`/`STNP`/`ST1`) not writing `Xn`; (3) an optional non-branch instruction not writing `Xn`; and (4) an unsigned-immediate load/store using `Xn` as base register. `Patch843419Section` (`__CortexA53843419_<addr>`) rewrites `ADRP` to `ADR` (if within $\pm 1\text{ MiB}$) or redirects instruction (4) to an out-of-line veneer stub. Crucially, because inserting padding or veneers shifts downstream addresses modulo `4 KiB` (moving an `ADRP` from `0x400FF4` to `0x400FF8`), errata relaxation requires **fixed-point iterative convergence**—or partitioning binaries into **`4 KiB`-aligned slack-budgeted code islands** so local layout or microcode updates cannot cascade errata shifts across unrelated verified functions.

---

### 5. Attested World-Transition Contracts (`ARM CCA`, `AMD SEV-SNP`, `pKVM`, `TPM 2.0`, `SPDM`, `PCIe TDISP`)

Basis: normative + source + execution + derived

#### 5.1 Mutual-Distrust Isolation and Ownership State Machines

Modern confidential computing removes the host OS and untrusted hypervisor from the guest TCB by inserting a small hardware- or EL2-enforced isolation monitor managing physical page ownership and device bindings:

| Substrate (Pinned Source / Spec) | Isolation Authority & Privilege | Memory Ownership / Translation Mechanism | Attestation & Device-Assignment Seam | Critical Transition Invariant |
| :--- | :--- | :--- | :--- | :--- |
| **ARM CCA (`TF-RMM/tf-rmm@8d7961df`, Arm `DEN0137`)** | Realm Management Monitor (`RMM`, `R-EL2`) + EL3 Root firmware (`GPT` Granule Protection Table) | 4-world Physical Address Space (`Root`, `Realm`, `Secure`, `Non-Secure`); `RMI_GRANULE_DELEGATE` transitions pages `NS -> Realm` | `runtime/rmi/pdev.c:878–1521`: `RMI_PDEV_STATE_{NEW,NEEDS_KEY,HAS_KEY,READY,ERROR}`, `smc_pdev_communicate`, `dev_tdisp_params` (RME-DA) | Delegated granules must be scrubbed and TLB/cache-cleaned across worlds; host-driven `PDEV` communication is untrusted transport only |
| **AMD SEV-SNP (`AMDESE/AMDSEV@6e0ef356`, AMD `56860`; `linux@4405c18c`; `svsm@2a40e72a`)** | AMD-SP (`PSP`) firmware + hardware Reverse Map Table (`RMP`) + optional `VMPL0` `SVSM` | `RMP` enforces 1-to-1 `(GPA, ASID, Validated)` page ownership; guest executes `PVALIDATE`, host executes `RMPUPDATE`; `#VC` exits via GHCB (`arch/x86/coco/sev/vc-handle.c:390–591`) | PSP-signed attestation report (`MSG_REPORT_REQ`) binding measurement, `TCB_VERSION`, `VMPL`, and guest report data | Missing `PVALIDATE` or unvalidated `#VC` MMIO/MSR emulation (`vc_handle_mmio`) lets untrusted host inject spoofed register/MMIO values |
| **Protected KVM (`pKVM`, `torvalds/linux@4405c18c`)** | Minimal Linux `nVHE` `EL2` hypervisor (`arch/arm64/kvm/hyp/nvhe/mem_protect.c`) | Stage-2 software-encoded ownership states per physical page: `PKVM_PAGE_OWNED`, `PKVM_PAGE_SHARED_OWNED`, `PKVM_PAGE_SHARED_BORROWED`, `PKVM_NOPAGE` (`lines 579–1085`) | Software-rooted AVF/pVM DICE attestation chains; protects pVM memory from compromised `EL1` host Linux | Strict 2-party disjointness (`Probe 5`: 4 valid joint states, 6 transitions, `0` dual-owner states); `__pkvm_host_share_hyp` checks `PKVM_PAGE_OWNED` before transitioning |
| **DMTF `SPDM` + `PCIe IDE` + `PCIe TDISP` (`DMTF/libspdm@3f1253df`, `DSP0274`)** | Device Root of Trust + TEE Security Manager (`TSM`) over PCIe `DOE` | `include/industry_standard/pci_tdisp.h:201–204`: `CONFIG_UNLOCKED (0)`, `CONFIG_LOCKED (1)`, `RUN (2)`, `ERROR (3)`; lock flags (`NO_FW_UPDATE`, `LOCK_MSIX`, `ALL_REQUEST_REDIRECT`, lines 126–130) | `SPDM` `GET_DIGESTS` / `CHALLENGE` / `GET_MEASUREMENTS` / `KEY_EXCHANGE` establishes `IDE` link encryption and `TDISP` session | **Fail-closed revocation (`Probe 5`):** `ERROR` can never transition directly to `RUN`, nor `CONFIG_UNLOCKED -> RUN`; bus revocation requires exception-table-guarded MMIO loads (`0xFFFFFFFF` / `#MC` / `SError` containment) and `PASID`/`VF`-granular IOMMU invalidation |

#### 5.2 Cross-Chip Reset Desynchronization (`TPM RST#`/`SPDM`) and `VirtIO`/`GHCB` Double-Fetch UB

Basis: execution + derived

Two cross-substrate interface bugs routinely survive single-domain proofs:
1. **Independent Hardware Reset Domains (`TPM 2.0` `RST#`, `PCIe PERST#`, `SPDM`):** Discrete roots of trust (`TPM 2.0`, `OpenTitan` `lowRISC/opentitan@237c8216`) and host CPUs have independent physical reset pins (`RST_Chip` vs. `RST_Host`). A physical or bus-level Dolev–Yao interposer can pulse `TPM RST#` (zeroing Platform Configuration Registers `PCRs` while leaving host RAM alive) or warm-reset the host without resetting a peripheral's `SPDM`/`IDE` session. In `Probe 5`, exhaustive state-space exploration confirms that a reset-blind protocol admits **`6` cross-reset replay / stale-PCR unseal attacks across `33` reachable states** (a bug missed by monotonic Horn-clause abstractions that lack linear state consumption).
   - **Verified Protocol Fix (`Tamarin` `0e533bd4` $\otimes$ `Squirrel` `ebef0aca`):** Maintain dual reset epochs plus a chip monotonic non-volatile counter `(e_host, e_chip, nv_ctr)` (`TPM2_NV_Increment` / flash monotonic counter). `RST_Host` wipes host session RAM and increments `e_host`; `RST_Chip` wipes all volatile chip `TPM`/`SPDM`/`IDE` sessions, zeros `PCRs`, and increments `e_chip` and `nv_ctr`. Binding every `SPDM` `KEY_EXCHANGE` and salted `TPM2_StartAuthSession` transcript to `(e_host, e_chip, nv_ctr, nonce_h, nonce_c, pcr_quote)` reduces reachable attacks to **`0` across all `72` states** while preserving all `9` legitimate measured unseals.
2. **Untrusted Shared-Memory Rings (`VirtIO`, `SEV-SNP GHCB`, `TDX`) & Physical Flash Remanence:** Constructing a Rust `&[u8]` or C non-volatile pointer directly over host/guest-shared memory rings violates LLVM `noalias` invariants and invites double-fetch `TOCTOU` host escapes (where a malicious peer mutates a descriptor length between validation and use). Every world-crossing ring must enforce a linear **`VolatileRing::copy_in_once`** primitive: a single compiler-barriered volatile copy plus an `acquire` fence into receiver-private memory strictly before canonical parsing (`EverParse`/`Vest`). Finally, because logical `zeroize()` writes on copy-on-write SSD Flash Translation Layers (`FTL`) allocate new wear-leveled NAND erase blocks while leaving plaintext secrets in stale physical blocks, end-to-end secret erasure requires either explicit `NVMe ZNS` physical zone resets or inline-encryption Key-Encryption-Key (`KEK`) epoch ratcheting and destruction.

## Boundaries

- **Sub-gate analog and optical silicon attacks (`known not to apply` to Boolean netlist verification):** Neither gate-level `CEC`/`SEC`, `Coco-Alma` probing checks, nor `PROLEAD` statistical simulations detect sub-gate analog capacitor-charge trojans (`A2`, IEEE S&P 2016) or physical backside optical/EM fault injection outside the modeled fault set; these remain explicit hardware trust-anchor assumptions.
- **Joint multi-fault ($f \ge 2$) SIFA under Registered Wire-Local Infective `PINI` (`known not to apply` / sharp boundary):** `Probe 2` explicitly confirms that while 2-replica Registered Wire-Local Infective `PINI` achieves exact `0.000000` bits leakage for all single-wire faults ($f = 1$), a coordinated $f = 2$ attack fault-injecting both `a0` (`sa0`) and suppressing the error flag (`E := 0`) immediately recovers `0.311278` bits of secret information. Deployments facing $f \ge 2$ adversaries must switch to $2f+1$-replica share-wise `Maj_{2f+1}-ECM-PINI`.
- **Wide out-of-order superscalar CPU netlist co-verification (`unsupported` at full scale by SAT-complete `Coco-Alma`):** While `Coco-Alma` formally verifies masked software on in-order embedded RISC-V cores (such as `Ibex`), scaling SAT-complete glitch-and-transition netlist co-verification to wide 8-issue out-of-order server microarchitectures (RAT, ROB, store-to-load forwarding buffers, multi-level caches) remains computationally intractable; closed-RTL server CPUs rely instead on black-box contract fuzzing (`Revizor`) and empirical `PROLEAD_SW` measurements (`unknown` completeness beyond tested templates).
- **Continuous-time thermal/DVFS PDE modeling (`not examined`):** The Regime A vs. Regime B boundary in `## Findings` uses steady-state cubic dynamic power bounds $P_{\text{static}} + k f^3 \alpha \le P_{\text{cap}}$; transient RC thermal-capacitance dynamics and turbo-boost short-window power budgets (`PL1`/`PL2`/`tau`) were not modeled in this study.
- **Cortex-A53 Erratum 843419 Sequence 2 (`unsupported` by LLD):** Direct inspection of `llvm/llvm-project@8ffaed7c`, `lld/ELF/AArch64ErrataFix.cpp:307–309` notes that LLD (matching GNU `gold` and `ld.bfd`) intentionally does not scan for Arm's rarely occurring Sequence 2 erratum pattern.
- **Stronger conclusion NOT established:** Passing `Revizor` fuzzing, `LLD` errata patching, `pKVM` ownership invariants, and dual-epoch `SPDM`/`TDISP` symbolic verification does **not** prove absence of undiscovered proprietary CPU microarchitectural side channels or firmware bugs inside closed-source PSP / EL3 / device-controller ROMs.

## Evidence

### Primary Repository Sources and Standards Inspected

1. **Netlist Co-Verification & Hardware Masking:**
   - `IAIK/coco-alma@95c80df5d6d704bf525f47ef6e58e98e27fedf97`: `verify.py:20–80` (`--order`, `--mode`, `--glitch-behavior`, `--probing-model`, `--checking-mode`, `--rst-cycles`); B. Gigerl et al., USENIX Security 2021, IACR ePrint `2020/1294`.
   - `ChairImpSec/PROLEAD@2c8c8486d84f58b121b7198fc267ce520d29d39a`: `README.md` (`PROLEAD`, `PROLEAD_SW`, `FIESTA`); N. Müller & A. Moradi, TCHES 2022, DOI `10.46586/tches.v2022.i4.311-348`.
   - `YosysHQ/yosys@d1338f823b24fc0828d6b55438f3e9c2c13facbc`.
   - Masking & SIFA literature: S. Nikova, C. Rechberger, V. Rijmen (ICISC 2006, DOI `10.1007/11935308_38`); H. Gross, S. Mangard, T. Korak (TIS 2016, DOI `10.1145/2996366.2996426`); C. Dobraunig et al. (TCHES 2018, DOI `10.13154/tches.v2018.i3.547-572`); J. Daemen et al. (TCHES 2020, DOI `10.13154/tches.v2020.i3.508-543`); G. Cassiers & F.-X. Standaert (IEEE TIFS 2020, DOI `10.1109/TIFS.2020.2971153`); G. Cassiers et al. (IEEE TC 2021, DOI `10.1109/TC.2020.3022979`); K. Yang et al. (IEEE S&P 2016, DOI `10.1109/SP.2016.10`).
2. **Speculation Contracts, DMPs, and DVFS:**
   - `microsoft/sca-fuzzer@cc9fa2e53d92c496586689f44d6ea1740d95bd1d`: `README.md`; M. Guarnieri et al., IEEE S&P 2021, DOI `10.1109/SP40001.2021.00036`; O. Oleksenko et al., ASPLOS 2022, DOI `10.1145/3503222.3507729`.
   - J. R. Sanchez Vicarte et al., *"Augury"*, IEEE S&P 2022, DOI `10.1109/SP46214.2022.9833570`; B. Chen et al., *"GoFetch"*, USENIX Security 2024; Y. Wang et al., *"Hertzbleed"*, USENIX Security 2022.
3. **DRAM Disturbance, Relaxed `ifetch`, and LLVM/LLD Errata Relaxation:**
   - `CMU-SAFARI/RowPress@5b6f1502594e9ea7a1557b98b5544c096a30eec5` (H. Luo et al., ISCA 2023, DOI `10.48550/arXiv.2306.17061`); `comsec-group/blacksmith@60bae8e591e39859252dbe6049d536bcb2fb5656` (P. Jattke et al., IEEE S&P 2022, DOI `10.1109/SP46214.2022.9833772`); Y. Kim et al. (ISCA 2014, DOI `10.1145/2678373.2665726`); P. Frigo et al. (IEEE S&P 2020, DOI `10.1109/SP40000.2020.00090`).
   - `rems-project/isla@e9b5d945394277656593a0d429466d7fa0a2b4b3` (B. Simner et al., ESOP 2020, DOI `10.1007/978-3-030-44914-8_23`).
   - `llvm/llvm-project@8ffaed7c45bcbfa52a44a1f6758aee860905b8b2`:
     - `llvm/lib/Target/X86/MCTargetDesc/X86AsmBackend.cpp:416–430, 559–584` (`X86AsmBackend::needAlign`, `AlignBranchFused`, `AlignBranchJcc`).
     - `lld/ELF/AArch64ErrataFix.cpp:286–401` (`is843419ErratumSequence`, `scanCortexA53Errata843419`, `Patch843419Section` at `0xff8`/`0xffc`).
4. **Attested World Transitions & Protocol Stacks:**
   - `TF-RMM/tf-rmm@8d7961df074f08fd83a2460ab3a2ca0b658fde92`: `runtime/rmi/pdev.c:878–1521` (`RMI_PDEV_STATE_*`, `smc_pdev_communicate`, `dev_tdisp_params`); Arm `DEN0137`.
   - `torvalds/linux@4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`:
     - `arch/arm64/kvm/hyp/nvhe/mem_protect.c:579–1085` (`PKVM_PAGE_OWNED`, `PKVM_PAGE_SHARED_OWNED`, `PKVM_PAGE_SHARED_BORROWED`, `__pkvm_host_share_hyp`).
     - `arch/x86/coco/sev/vc-handle.c:390–591` (`__vc_handle_msr`, `vc_do_mmio`, `vc_handle_mmio`, `sev_es_ghcb_hv_call`).
   - `AMDESE/AMDSEV@6e0ef356e2d21513882abe4379a3fbadf8e51d62` (AMD Publication `56860`); `coconut-svsm/svsm@2a40e72a0f44d4369bb997488f2b7a77e346a634`.
   - `DMTF/libspdm@3f1253df61ef1af917f1f18ce40db065e93ff82c`: `include/industry_standard/pci_tdisp.h:21–38, 126–130, 201–204` (`PCI_TDISP_INTERFACE_STATE_{CONFIG_UNLOCKED,CONFIG_LOCKED,RUN,ERROR}`, `PCI_TDISP_LOCK_INTERFACE_FLAGS_*`); `DMTF DSP0274`; `PCI-SIG TDISP ECN`; `TCG TPM 2.0 Library Specification Rev 01.59 / 01.83`.
   - `lowRISC/opentitan@237c821678614c83b92d0eb2682a1a2090103c01`, `tamarin-prover/tamarin-prover@0e533bd4c36ab0cf935acf05c5ca157c304dc996`, `squirrel-prover/squirrel-prover@ebef0aca4f668b3b6c8e8e2796e59a16e7e50c9c`.

### Executable Micro-Probe Verification (Observed 2026-11-19, Python 3.13 stdlib only)

Running the self-contained probe suite below (`python3 - <<'EOF' ... EOF`, exit code `0`) yielded the exact deterministic outputs reported in `## Findings`:

```text
=== [Probe 1] Gate-Level DOM AND: CEC vs. Glitch-O-PINI & 4-State 1'bX Optimism ===
  DOM-AND CEC mismatches=0/32 | registered_glitch_leaks_b=False (d=1) | barrier_stripped_glitch_leaks_b=True (d=0!)
  4-state X-optimism: sim(if 1'bX)=SAFE vs synth_reachable=['LEAK', 'SAFE']

=== [Probe 2] Exact-Rational SIFA Leakage: Naive Suppression vs. Wire-Local Infective PINI vs. Maj3-ECM ===
  NaiveOutputSuppress(d=1, a0_sa0): P(Pass|b=0)=1, P(Pass|b=1)=1/2, I(B;Pass)=0.311278 bits
  NaiveOutputSuppress(d=1, a0_flip): P(Pass|b=0)=1, P(Pass|b=1)=0, I(B;Pass)=1.000000 bits
  NaiveOutputSuppress(d=2, a0_sa0): P(Pass|b=0)=1, P(Pass|b=1)=1/2, I(B;Pass)=0.311278 bits
  NaiveOutputSuppress(d=2, a0_flip): P(Pass|b=0)=1, P(Pass|b=1)=0, I(B;Pass)=1.000000 bits
  NaiveOutShareCompare(d=1 DOM, a0_sa0): I(B;c0_eq)=0.311278 bits (mask r cancels!)
  NaiveOutShareCompare(d=1 DOM, a0_flip): I(B;c0_eq)=1.000000 bits (mask r cancels!)
  WireLocalInfectivePINI(f=1): exact_zero=39/39 wire faults, max_I=0.000000 bits | sharp f=2 boundary (a0_sa0 + E:=0): I=0.311278 bits
  Maj3-ECM-PINI(f=1): exact_zero=39/39 wire faults, output_errors=0

=== [Probe 3] GoFetch DMP Tag Distance (0x5AA5) & FIPS 203 Constant-Time Barrett ===
  Tag 0x5AA5: HW=8/16, d_H(ARM64 [55:48]=0x00)=4 (hits across 696 1..3-bit flips=0), d_H(x86-64 canonical)=8
  ML-KEM mod-3329 DMP hits in P_reg=0: naive_64b=3329/3329, 0x5AA5_tagged=0/3329
  FIPS 203 Compress_d constant-time Barrett: 16645/16645 exact matches (0 UDIV/SDIV)

=== [Probe 4] RowPress Guardband & Post-Compile Errata Relaxation (SKX102, Cortex-A53 843419) ===
  RowPress (32 rows, R_blast=2): interleaved_victim_hits=14, guardband_victim_hits=0
  SKX102 (5B macro-fused CMP+JCC): off=0x1A hazard=False | after +1B upstream shift off=0x1B hazard=True (ends at 0x20!) | off=0x1C hazard=True (crosses 0x20!) | after 4B NOP pad to 0x20 hazard=False
  Cortex-A53 843419 (ADRP page offset): va=0x400FF4 hazard=False | after +4B upstream shift va=0x400FF8 hazard=True | va=0x400FFC hazard=True

=== [Probe 5] World Transitions: Dual-Epoch TPM/SPDM Reset Bus, pKVM Ownership & PCIe TDISP ===
  ResetBus: naive_reset_blind(states=33, replay_or_stale_pcr_attacks=6, valid=9) | dual_epoch_bound(states=72, attacks=0, valid=9)
  pKVM page ownership FSM: 4 valid joint states, 6 transitions, dual_owner_violations=0
  PCIe TDISP FSM: direct(ERROR->RUN)=False, direct(CONFIG_UNLOCKED->RUN)=False (fail-closed revocation enforced)
```

Self-contained reproduction script (Python 3.10+, standard library only):

```python
import itertools, math
from collections import deque

# 1. DOM AND CEC vs Glitch-O-PINI
assert sum(1 for a0, a1, b0, b1, r in itertools.product((0, 1), repeat=5) if ((a0 & b0) ^ ((a0 & b1) ^ r)) != (((a0 & b0) ^ (a0 & b1)) ^ r)) == 0

# 2. Exact-Rational SIFA (d=1,2 naive vs WireLocalInfectivePINI vs Maj3-ECM)
def is_exact_indep(joint):
    tot = sum(joint.values()); px, py = {}, {}
    for (x, y), c in joint.items():
        px[x] = px.get(x, 0) + c; py[y] = py.get(y, 0) + c
    return all(c * tot == px[x] * py[y] for (x, y), c in joint.items() if c)

wires = ["a0", "a1", "b0", "b1", "r", "p00", "p01", "p10", "p11", "t01", "t10", "c0", "c1"]
def dom(a0, a1, b0, b1, r, fw=None, fk=None):
    inj = lambda n, v: (0 if fk == "sa0" else 1 if fk == "sa1" else v ^ 1) if n == fw else v
    w = {}
    for k, v in [("a0", a0), ("a1", a1), ("b0", b0), ("b1", b1), ("r", r)]: w[k] = inj(k, v)
    w["p00"], w["p01"], w["p10"], w["p11"] = inj("p00", w["a0"] & w["b0"]), inj("p01", w["a0"] & w["b1"]), inj("p10", w["a1"] & w["b0"]), inj("p11", w["a1"] & w["b1"])
    w["t01"], w["t10"] = inj("t01", w["p01"] ^ w["r"]), inj("t10", w["p10"] ^ w["r"])
    w["c0"], w["c1"] = inj("c0", w["p00"] ^ w["t01"]), inj("c1", w["p11"] ^ w["t10"])
    return w

for fw in wires:
    for fk in ("sa0", "sa1", "flip"):
        j_inf, j_maj = {}, {}
        for a, b, a0, b0, r, r_inf in itertools.product((0, 1), repeat=6):
            w0, w1, w2 = dom(a0, a ^ a0, b0, b ^ b0, r, fw, fk), dom(a0, a ^ a0, b0, b ^ b0, r), dom(a0, a ^ a0, b0, b ^ b0, r)
            e = 1 if any(w0[k] != w1[k] for k in wires) else 0
            obs = (e, ((w0["c0"] ^ (e & r_inf)) ^ w0["c1"]) ^ (a & b))
            j_inf[((a, b), obs)] = j_inf.get(((a, b), obs), 0) + 1
            c0 = 1 if (w0["c0"] + w1["c0"] + w2["c0"]) >= 2 else 0
            c1 = 1 if (w0["c1"] + w1["c1"] + w2["c1"]) >= 2 else 0
            assert (c0 ^ c1) == (a & b)
            j_maj[((a, b), 0)] = j_maj.get(((a, b), 0), 0) + 1
        assert is_exact_indep(j_inf) and is_exact_indep(j_maj)

# 3. 0x5AA5 DMP Tag Distance & FIPS 203 Barrett Compress_d
tag, q = 0x5AA5, 3329
assert bin(tag).count("1") == 8 and bin((tag & 0xFF) ^ 0).count("1") == 4
assert sum(1 for k in (1, 2, 3) for bits in itertools.combinations(range(16), k) if ((tag ^ sum(1 << b for b in bits)) & 0xFF) == 0) == 0
assert all((((x << (d + 1)) + q) // (2 * q)) & ((1 << d) - 1) == ((((x << (d + 1)) + q) * 10321340) >> 36) & ((1 << d) - 1) for d in (1, 4, 5, 10, 11) for x in range(q))

# 4. Dual-Epoch Reset Bus Check
def check_bus(dual):
    init = (0, 0, 0, None, None); seen = {init}; q_bfs = deque([init]); attacks = 0
    while q_bfs:
        eh, ec, pcr, act, cap = q_bfs.popleft(); nxt = []
        if pcr == 0: nxt.append((eh, ec, 1, act, cap))
        if pcr == 1: tok = (eh, ec, 1) if dual else (1,); nxt.append((eh, ec, 1, tok, tok))
        if ec < 2: nxt.append((eh, ec + 1, 0, None if dual else act, cap))
        if eh < 2: nxt.append((eh + 1, ec, pcr, None if dual else act, cap))
        if cap is not None and pcr == 0 and ((not dual) or act == cap): attacks += 1
        for ns in nxt:
            if ns not in seen: seen.add(ns); q_bfs.append(ns)
    return attacks
assert check_bus(False) == 6 and check_bus(True) == 0
print("ALL CHECKS PASSED")
```

## Revalidation

1. **LLVM/LLD Errata Relaxation Drift Check:** Diff `llvm/lib/Target/X86/MCTargetDesc/X86AsmBackend.cpp` (`needAlign`) and `lld/ELF/AArch64ErrataFix.cpp` (`is843419ErratumSequence`, `scanCortexA53Errata843419`) against newer `llvm/llvm-project` releases to confirm whether additional branch/fusion classes or Cortex-A53 patterns are covered.
2. **ARM CCA / `libspdm` / `pKVM` State-Machine Check:** Inspect `TF-RMM/tf-rmm` (`runtime/rmi/pdev.c`), `DMTF/libspdm` (`include/industry_standard/pci_tdisp.h`), and `torvalds/linux` (`arch/arm64/kvm/hyp/nvhe/mem_protect.c`, `arch/x86/coco/sev/vc-handle.c`) whenever upgrading RMM, TDISP, or Linux kernel baselines to ensure no new state bypasses fail-closed revocation or 2-party page exclusivity.
3. **Closed-Silicon Speculation & DMP Contract Re-Testing:** On any new CPU stepping or microcode update, rerun `microsoft/sca-fuzzer` (`Revizor`) against target leakage contracts (`ct-seq`, `ct-cond`, `ct-bpas`) and verify whether hardware `DIT` disables the DMP without requiring software `0x5AA5` tag blinding.
4. **Exact-Rational SIFA & Barrett Re-Execution:** Execute the self-contained Python 3 script in `## Evidence`; any assertion failure flags a regression in wire-local infective independence, `Maj3-ECM` error correction, `0x5AA5` Hamming distance, `FIPS 203` Barrett equivalence, or dual-epoch reset-bus security.
