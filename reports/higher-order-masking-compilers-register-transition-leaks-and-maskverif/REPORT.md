# Higher-Order Masking, Compiler Register-Transition Leakage, and Verified Masking Toolchains

## Summary

Higher-order masking splits each secret $x$ into $d+1$ randomized shares so that any $t \le d$ physical observations reveal zero secret information, yet standard optimizing compilers—including constant-time (`CT`) compilers—routinely destroy masking soundness before or during machine-code generation. Four core results define this verification boundary:

1. **Probing-to-Noisy-Leakage Soundness Requires Composability**: Ishai-Sahai-Wagner (`ISW`, CRYPTO 2003) $t$-probing security reduces to physical noisy leakage via random probing (Prouff & Rivain, EUROCRYPT 2013; Duc, Dziembowski, Faust, EUROCRYPT 2014). Modular composition of masked gadgets fails under plain $t$-Non-Interference (`t-NI`)—for instance, naive circular refresh passes `2-NI` at $d=2$ yet fails `2-SNI`, breaking `SecMult(a, Refresh(a))`. Sound composition requires **Strong Non-Interference (`t-SNI`, Barthe et al. CCS 2016)** for software gadgets or **Probe-Isolating Non-Interference (`PINI`, Cassiers et al. IEEE TC 2020)** for glitch-resilient hardware.
2. **Boolean-to-Arithmetic (`B2A`) and `A2B` Conversions Bridge Linear Domains**: Symmetric/post-quantum algorithms mixing XOR and modular addition ($\bmod\, 2^k$ or $\bmod\, q$) require provably probing-secure conversions (Goubin CHES 2001 at $d=1$; Coron-Großschädl-Vadnala CHES 2014 at arbitrary order $d$) whose intermediate carry/masking terms must never be reordered by a compiler.
3. **Why ISA Constant-Time Compilers Break Masking**: ISA constant-time preservation only forbids secret-dependent branches and memory addresses; it treats algebraic rewrites and storage reuse as semantics-preserving. Consequently, standard passes collapse masking order $d \to \lfloor d/2 \rfloor$ or $0$ through: (a) **algebraic CSE / XOR cancellation and reassociation** (`(x ^ r) ^ r -> x`, or `rnd ^ ((a0 & b1) ^ (a1 & b0))` leaking `0.2044` bits at a single probe), (b) **physical register reuse** ($\mathrm{HD}(x_0, x_1) = \mathrm{HW}(x_0 \oplus x_1) = \mathrm{HW}(x)$), (c) **stack spill-slot and memory-bus reuse**, and (d) **hidden microarchitectural latches** (ALU operand latches `opA`/`opB`, memory read/write latches `opR`/`opW`, and RISC-V immediate-field shadow `rs2` register reads as explicitly modeled in `leakage-resilience/scverif`).
4. **Stratified Verification Toolchain Landscape**: No single tool covers all abstraction layers simultaneously. `CryptoExperts/Tornado` (`Usuba` + `tightPROVE+`) synthesizes bitsliced C proven secure in the register-probing model; `cassiersg/maskverif` verifies symbolic `NI`/`SNI`/threshold security with optional `Transition` and `Glitch` extensions; `CryptoExperts/IronMask` verifies `NI`/`SNI`/`PINI`/`fSNI`/`IOS`, tight random-probing (`RP`/`RPC`/`RPE`), arithmetic prime-field masking, and combined fault+probing (`CNI`/`CRP`/`CRPC`); `leakage-resilience/scverif` verifies concrete ARM Cortex-M0+/M4 and RISC-V `Ibex` assembly against stateful microarchitectural transition leakage models; and `0xADE1A1DE/rosita` rewrites leaking assembly using an `ELMO`-driven leakage oracle.

## Applicability

This report applies to higher-order Boolean and arithmetic masked cryptographic implementations compiled to embedded and general-purpose ISAs (ARM Thumb / Cortex-M0+/M4, RISC-V `RV32EI`, and bitsliced C/SIMD targets) and to the formal verifiers that audit them:

- **Source/IR-level masking synthesis and symbolic verification**: Directly characterized by `CryptoExperts/Tornado` (commit `708b6111...`, bitsliced `Usuba` -> masked C with `tightPROVE+`), `cassiersg/maskverif` (commit `ce1780d6...`, `.mv` gadget verifier), and `CryptoExperts/IronMask` (commit `8d2d79b6...`, binary/arithmetic probing, random-probing, and combined fault-probing verifier).
- **Target assembly and microarchitectural transition verification**: Directly characterized by `leakage-resilience/scverif` (commit `4f9b1480...`, `.il` leakage semantics for ARM Cortex-M0+, Cortex-M4, and RISC-V `Ibex`) and `0xADE1A1DE/rosita` (commit `d4162187...`, ARM Cortex-M0 rewrite engine).

Relationship among subjects: ISW, Prouff-Rivain, Duc-Dziembowski-Faust, Barthe et al., Goubin, Coron et al., and Cassiers et al. establish the formal security hierarchy (`t-probing`, `t-NI`, `t-SNI`, `PINI`, `RP`/`RPC`/`RPE`, `B2A`/`A2B`); Balasch et al. and Papagiannopoulos-Veshchikov establish the software-to-silicon transition/order-reduction gap; `Tornado`, `maskVerif`, `IronMask`, `scVerif`, and `ROSITA` represent distinct points on the abstraction-vs-hardware-fidelity frontier.

## Findings

### 1. Probing, Noisy-Leakage, and Composable Non-Interference Hierarchy

Basis: normative (`doi:10.1007/978-3-540-45146-4_27`, `doi:10.1007/978-3-642-38348-9_9`, `doi:10.1007/s00145-018-9284-1`, `doi:10.1145/2976749.2978427`, `doi:10.1109/TC.2020.3022979`) + execution (Probe 2A).

In Boolean $d$-th order masking over $\mathbb{F}_2^w$, a secret $x$ is encoded as $d+1$ shares $(x_0, \dots, x_d)$ with $x = \bigoplus_{i=0}^d x_i$ and $d$ uniform fresh masks. In arithmetic masking over $\mathbb{Z}_M$, $x = \sum_{i=0}^d A_i \bmod M$.

| Security Notion | Definition (for $d+1$ shares, order $t \le d$) | Composable Without Extra Refreshes? | Physical Relevance |
| :--- | :--- | :--- | :--- |
| **$t$-Probing (ISW 2003)** | Any $t$ internal/output wire values are jointly independent of every secret input | No (whole-circuit global check) | Reduces to bounded noisy leakage via random probing (Prouff-Rivain 2013; Duc-Dziembowski-Faust 2014) |
| **$t$-NI (Barthe et al. 2016)** | Any $t_1$ internal + $t_2$ output probes ($t_1 + t_2 \le t$) can be simulated using at most $t_1 + t_2$ shares of each input | **No** when fan-out > 1 (e.g., `Mult(a, a)`) | Fails composition across shared inputs without SNI refresh |
| **$t$-SNI (Barthe et al. 2016)** | Any $t_1$ internal + $t_2$ output probes ($t_1 + t_2 \le t$) can be simulated using at most **$t_1$** shares of each input (independent of $t_2$) | **Yes** (output probes do not propagate share requirements upstream) | Software compositional baseline; requires quadratic $O(d^2)$ ISW refresh or verified $O(d \log d)$ refresh |
| **$t$-PINI (Cassiers et al. 2020)** | Any $t_1$ internal probes + output probes at share indices $O$ can be simulated using input indices $I \cup O$ with $|I| \le t_1$ | **Trivially composable** (linear gadgets are free, no refresh insertion needed) | Standard for glitch-extended robust probing in hardware |
| **Random Probing (`RP`/`RPC`/`RPE`)** | Each wire leaks independently with probability $p$; advantage bounded directly in $p$ | `RPC`/`RPE` enable tight compositional bounds (`IronMask`) | Tighter noise-rate bounds than worst-case $t$-probing reductions |

**Concrete `2-NI` vs. `2-SNI` Separation (Execution, Probe 2A)**:
For $d = 2$ ($3$ shares $x_0, x_1, x_2$), compare:
- **Naive Circular Refresh** (2 masks $r_0, r_1$): $y_0 = x_0 \oplus r_0$, $y_1 = x_1 \oplus r_1$, $m_0 = x_2 \oplus r_0$, $y_2 = m_0 \oplus r_1$.
- **ISW Quadratic Refresh** (3 masks $r_0, r_1, r_2$, matching `CryptoExperts/Tornado` `src/usuba/arch/MASKED_UA.h:126-141`): pairwise XOR of fresh `rnd` across all $(i, j)$ with $0 \le i < j \le 2$.

Exhaustive exact distributional verification across all 2-probe tuples (Probe 2A) confirms:
- `CircularRefresh(d=2)` **passes `2-NI`** (every 2 probes depend on $\le 2$ input shares) but **fails `2-SNI`** on witness `['m0=x2^r0', 'y0=x0^r0']` ($t_1 = 1$ internal probe + $t_2 = 1$ output probe yields $m_0 \oplus y_0 = x_0 \oplus x_2$, requiring $2 > t_1 = 1$ input shares!). Consequently, composing `ISW_Mult(x, CircularRefresh(x))` allows a 2-probe secret recovery.
- `ISWRefresh(d=2)` **passes both `2-NI` and `2-SNI`** across all probe pairs.

### 2. Boolean/Arithmetic Masking Conversions (`B2A` / `A2B`)

Basis: normative (`doi:10.1007/3-540-44709-1_2`, `doi:10.1007/978-3-662-44709-3_11`) + execution (Probe 2C).

Algorithms combining bitwise operations with modular addition (ARX ciphers, lattice post-quantum schemes) require switching between Boolean shares ($x = x' \oplus r$) and arithmetic shares ($x = (A + r) \bmod 2^w$):
- **First-Order Goubin `B2A` (CHES 2001)**: Exploiting the affine-in-$\mathbb{F}_2$ differential identity $\Psi(x', r) = (x' \oplus r) - r \bmod 2^w$, introduces a fresh uniform mask $\gamma$ and computes in $O(1)$ instructions:
  $$T = ((x' \oplus \gamma) - \gamma) \oplus x', \quad \gamma' = \gamma \oplus r, \quad A = ((x' \oplus \gamma') - \gamma') \oplus T \pmod{2^w}.$$
  Probe 2C verifies exact functional equivalence $(A + r) \bmod 2^8 = x$ over all 8-bit $x$ and exact 1-probe distributional uniformity of all 7 intermediates (`T1, T2, T3, g2, A1, A2, A`) over uniform $(r, \gamma)$.
- **Higher-Order `B2A`/`A2B` (Coron-Großschädl-Vadnala, CHES 2014)**: Generalizes conversions to arbitrary order $d$ using recursive `SecAdd` (masked ripple-carry or Kogge-Stone adder built from `ISW` masked `AND` and `SNI` refreshes) for `A2B` and randomized share-reduction loops for `B2A`. Because `SecAdd` executes carry propagation via nonlinear masked gates, compiler reassociation or register reuse across carry shares immediately breaks $d$-th order security.

### 3. Failure Modes of Standard & Constant-Time Compilers on Masked Code

Basis: normative (`doi:10.1007/978-3-319-16763-3_5`, `doi:10.1007/978-3-319-64647-3_17`) + source (`CryptoExperts/Tornado`, `leakage-resilience/scverif`) + execution (Probe 2B).

Standard optimizing compilers (LLVM/Clang, GCC) and ISA constant-time compilers enforce **functional equivalence** (plus branch/address independence for CT). Under a physical transition/probing semantics, four classes of semantics-preserving transformations silently break masking:

| Compiler / Microarchitectural Hazard | Mechanism | Effective Order Loss | Primary Source / Proof |
| :--- | :--- | :--- | :--- |
| **Algebraic CSE, Folding & XOR Reassociation** | Simplifying `(x ^ r) ^ r -> x`, hoisting masks, or reassociating `(rnd ^ (a0 & b1)) ^ (a1 & b0)` into `rnd ^ ((a0 & b1) ^ (a1 & b0))` | $d \to 0$ (immediate unmasked secret) | `Tornado` `MASKED_UA.h:119` explicit parenthesization; Probe 2B (`I(V; (a,b))` jumps `0.0000 -> 0.2044` bits) |
| **Physical Register Reuse (`HD` Overwrite)** | Graph-coloring register allocator assigns share $x_1$ to the register previously holding $x_0$, producing transition $x_0 \oplus x_1$ | $d \to \lfloor d/2 \rfloor$ (at $d=1$: $1 \to 0$) | Balasch et al. (CARDIS 2014); `scverif` `eorsTransition`/`ldrTransition`/`overwrite_leakage` |
| **Stack Spill-Slot & Memory-Bus Transitions** | Spilling $x_0$ and $x_1$ to the same stack slot, or loading/storing two shares sequentially across a shared SRAM data bus (`MDR`) | $d \to \lfloor d/2 \rfloor$ or $0$ | `ELMO` `powermodel.h:309` (`readbus`/`writebus` `hdistance`); `scverif` `ldrMemOperand(opR, val)` & `strMemOperand(opW, val)` |
| **Hidden Pipeline / ALU / Decode Latches** | ALU input latches (`opA`, `opB`), barrel-shifter state, status flags, or RISC-V immediate bits accidentally selecting a register file read port (`rs2`) | $d \to \lfloor d/2 \rfloor$ or $0$ (even with disjoint registers!) | Papagiannopoulos & Veshchikov (COSADE 2017); `scverif` `leakyisa-cortex-m0plus.il:4-61` & `rv32ei_ibexleaks.il:10-65` |

Two primary-source artifacts illustrate the subtlety of microarchitectural coupling:
1. **Algebraic Parenthesization Fragility (`CryptoExperts/Tornado`, `src/usuba/arch/MASKED_UA.h:105-122`)**: In `isw_mult`, line 119 writes `res[j] ^= (rnd ^ (op1[i] & op2[j])) ^ (op1[j] & op2[i]);` specifically so `rnd` masks `op1[i] & op2[j]` before XORing `op1[j] & op2[i]`. In standard C without compiler barriers, an optimizer may legally reassociate XOR to `rnd ^ ((op1[i] & op2[j]) ^ (op1[j] & op2[i]))`. Probe 2B proves this single reassociation raises 1-probe mutual information $I(V; (a, b))$ from `0.000000` bits to `0.204434` bits.
2. **Hidden Microarchitectural State (`leakage-resilience/scverif`)**:
   - In `models/leakyisa-cortex-m0plus.il` (lines 4–61), ARM Cortex-M0+ instructions implicitly update four persistent non-architectural registers (`opA`, `opB`, `opR`, `opW`), emitting `eorsOperand(opA, op1, opB, op2)`, `eorsTransition(op1, op1 ^ op2)`, `ldrMemOperand(opR, val)`, and `ldrTransition(dst, val)`. Even if shares reside in distinct registers `r0` and `r1`, consecutive `ldr` instructions recombine them on `opR` unless an intervening clearing/dummy transfer flushes the bus latch.
   - In `models/rv32ei_ibexleaks.il` (lines 10–65), `common_leakage` couples `(rs1_val, rs2_val, rf_pA, rf_pB, mem_last_addr, mem_last_read)`, and `addi3_leak` (lines 34–65) models the Ibex decoder hazard where immediate bits `imm & 0xF` index the `rs2` register-file read port (`rf_pB`), leaking a shadow register that never appears as an architectural operand of `addi`.

### 4. Verified Masking Compilers, Verifiers, and Rewriters

Basis: source (`CryptoExperts/Tornado`, `cassiersg/maskverif`, `leakage-resilience/scverif`, `CryptoExperts/IronMask`, `0xADE1A1DE/rosita`).

| Tool & Pinned Revision | Input Abstraction | Verification / Synthesis Method | Leakage & Security Models | Key Limitation / Trust Boundary |
| :--- | :--- | :--- | :--- | :--- |
| **Tornado** (`CryptoExperts/Tornado@708b6111`) | High-level `Usuba` bitsliced spec (`-tp -ua-masked`) | Compiles via `Usuba` + verifies/inserts refreshes via `tightPROVE+` (`src/tightPROVEp/manual.txt`) | Bit-probing & register-probing security on bitsliced Boolean circuits (`isw_mult`, `isw_refresh`) | Emits C source (`MASKED_UA.h`); relies on downstream C compiler not reassociating expressions or introducing register/bus transitions |
| **maskVerif** (`cassiersg/maskverif@ce1780d6`) | `.mv` gadget/circuit descriptions | Symbolic expression simplification & tuple enumeration (`src/checker.ml`, `src/poly_solve.ml`) | `NI`, `SNI`, Threshold (`src/main.ml:59-131`) with configurable `trans` (transition) and `glitch` (default `true` unless `NoGlitch`) | Operates on abstract circuit/gadget IR, not native ELF/machine code; combinatorial scaling at high orders |
| **IronMask** (`CryptoExperts/IronMask@8d2d79b6`) | Binary / prime-field gadget circuits | Parallel C/GMP bitvector dependency solver (`src/circuit.h` `BitDep`, `MultDependency`) | `NI`, `SNI`, `PINI`, `fSNI`, `IOS`; random probing `RP`/`RPC`/`RPE`/`cardRPC`; combined fault+probing `CNI`/`CRP`/`CRPC` (`IronMask+`) | Gadget/circuit-level verification; requires separate lowering guarantee to target silicon |
| **scVerif** (`leakage-resilience/scverif@4f9b1480`) | Concrete ARM Thumb / RISC-V assembly + `.il` leakage model | Lifts assembly (`src/asmlifter.ml`) to IL (`src/illeakage.ml`) and checks probing/NI via `maskVerif`-style backend (`src/ilmaskverif.ml`) | Stateful fine-grained register overwrite, ALU operand latch (`opA`/`opB`), memory bus (`opR`/`opW`), and Ibex shadow-read leaks | Soundness is relative to fidelity of the hand-crafted/profiled `.il` microarchitectural model |
| **ROSITA** (`0xADE1A1DE/rosita@d4162187`) | Compiled ARM Cortex-M0 assembly | Empirical trace-guided rewrite loop using `ELMO` power emulator (`ROSITA/ARMMatcher.py`, `ASMParser.py`) | Eliminates concrete `ELMO`-detected first-order transition/bus leaks (e.g., inserting register-clearing/reordering rewrites) | Empirical (`ELMO` model coverage only), not a sound universal formal proof over all inputs or arbitrary orders |

**Architectural Takeaway for Compiler & Verification Engineers**: Achieving end-to-end masked security requires separating two obligations that general-purpose compilers conflate: (1) **algebraic/compositional masking soundness** (`Tornado` / `maskVerif` / `IronMask` ensuring `t-SNI` / `PINI` / `RPC` at the gadget/circuit level), and (2) **post-codegen microarchitectural transition verification** (`scVerif` or gate-level hardware-software co-verification checking emitted machine code against register-reuse, stack-spill, and bus-latch leakage models). Masking-aware compiler passes must treat share operations as non-reassociable opaque intrinsics and enforce share-disjoint register/stack-slot allocation plus explicit latch-clearing barriers where required by the target CPU model.

## Boundaries

- **known not to apply**: Proving constant-time (`CT`) non-interference at source, MIR, LLVM IR, or ISA level does not imply probing or transition security of masked code; `t-NI` does not imply safe arbitrary composition without `t-SNI` refreshes; C-level verified masking (`Tornado` output) does not remain secure if compiled with unconstrained LLVM/GCC optimization and register allocation.
- **unsupported**: `CryptoExperts/Tornado` (`MASKED_UA.h:92-103`) uses placeholder `get_random()` stubs (`rand()` / `volatile int __rand`) for functional testing and does not ship a verified hardware TRNG/CSPRNG; `cassiersg/maskverif` and `CryptoExperts/IronMask` do not ingest raw compiled ARM/x86/RISC-V binaries directly; `0xADE1A1DE/rosita` targets ARM Cortex-M0/ELMO and does not provide formal higher-order proofs.
- **not examined**: Gate-level hardware netlist co-verification tools (`IAIK/Coco-Alma`, `ChairImpSec/PROLEAD`), LLVM masked-register-allocation compiler backends (`SecAlloc`), and physical oscilloscope TVLA measurements of `Tornado`/`scVerif` outputs on silicon were not compiled or executed in this study.
- **unknown**: Whether a given commercial out-of-order CPU (x86-64 / ARMv8-A) exhibits undocumented cross-port forwarding, store-buffer, or cache-line fill transitions that violate `.il` in-order leakage models cannot be determined without silicon characterization or gate-level RTL access.

## Evidence

### Upstream Repositories and Source Anchors
- `CryptoExperts/Tornado` @ `708b61119721bde415095903b7985cf441320a4b`:
  - `README.md` (combination of `Usuba` and `tightPROVE+`, `-tp -ua-masked` flags).
  - `src/tightPROVEp/manual.txt` (lines 1–75: `simple_search` bit/register probing attack search options).
  - `src/usuba/arch/MASKED_UA.h`: `MASKED_AND` -> `isw_mult` (line 74, lines 105–122, parenthesized cross-product masking at line 119), `REFRESH` -> `isw_refresh` (lines 124–141).
- `cassiersg/maskverif` @ `ce1780d60a2e4abe83c7c605ee3e78b2f88c7fdf`:
  - `src/main.ml`: `check_opt` (`trans`, `glitch`, `para`, `order`, lines 59–87), `check_ni`, `check_threshold`, `check_sni` dispatching `Prog.build_obs_func ~trans ~glitch` (lines 99–132).
  - `src/checker.ml` (lines 1–80: tuple-set combinatorial representation `L.ldf` and symbolic checking entrypoint).
- `leakage-resilience/scverif` @ `4f9b1480f751fa4e8ed2cc9c4dd69fb692551ca3`:
  - `README.md` (fine-grained leakage models and TCHES 2021 reference).
  - `models/leakyisa-cortex-m0plus.il` (lines 4–85: hidden latches `opA`, `opB`, `opR`, `opW`; `eors2_leak`, `ands2_leak`, `ldr3_leak`, `str3_leak`, `mov2_leak`).
  - `models/rv32ei_ibexleaks.il` (lines 4–65: `mem_last_read`, `mem_last_addr`, `rf_pA`, `rf_pB`, `common_leakage`, `overwrite_leakage`, `addi3_leak` shadow `rs2` read from `imm & 0xF`).
  - `src/asmlifter.ml`, `src/illeakage.ml`, `src/ilmaskverif.ml`.
- `CryptoExperts/IronMask` @ `8d2d79b686316a9152510f97443b91f4e456f749`:
  - `Readme.md` (lines 1–52: `IronMask` `NI`/`SNI`/`PINI`/`fSNI`/`IOS`/`RP`/`RPC`/`RPE`, `IronMask+` `CNI`/`CRP`/`CRPC`, `IronMaskArithmetic` prime-field and `cardRPC`).
  - `src/circuit.h` (lines 25–64: `BitDep` bitvector dependency representation and `MultDependency`).
- `0xADE1A1DE/rosita` @ `d41621879dc2a1faa2c21600967ab2247d3de69d`:
  - `README.md` (ELMO-based leakage-driven assembly rewrite workflow).
  - `ROSITA/ARMMatcher.py`, `ROSITA/ASMParser.py`, `ROSITA/Build.py`.

### Peer-Reviewed Literature
- Goubin, *A Sound Method for Switching between Boolean and Arithmetic Masking*, CHES 2001, `doi:10.1007/3-540-44709-1_2`.
- Ishai, Sahai, Wagner, *Private Circuits: Securing Hardware against Probing Attacks*, CRYPTO 2003, `doi:10.1007/978-3-540-45146-4_27`.
- Prouff, Rivain, *Masking against Side-Channel Attacks: A Formal Security Proof*, EUROCRYPT 2013, `doi:10.1007/978-3-642-38348-9_9`.
- Coron, Großschädl, Vadnala, *Secure Conversion between Boolean and Arithmetic Masking of Any Order*, CHES 2014, `doi:10.1007/978-3-662-44709-3_11`.
- Balasch, Gierlichs, Grosso, Reparaz, Standaert, *On the Cost of Lazy Engineering for Masked Software Implementations*, CARDIS 2014, `doi:10.1007/978-3-319-16763-3_5`.
- Barthe, Belaïd, Dupressoir, Fouque, Grégoire, Strub, Zucchini, *Strong Non-Interference and Type-Directed Higher-Order Masking*, ACM CCS 2016, `doi:10.1145/2976749.2978427`.
- Papagiannopoulos, Veshchikov, *Mind the Gap: Towards Secure 1st-Order Masking in Software*, COSADE 2017, `doi:10.1007/978-3-319-64647-3_17`.
- Duc, Dziembowski, Faust, *Unifying Leakage Models: From Probing Attacks to Noisy Leakage*, EUROCRYPT 2014 / JoC, `doi:10.1007/s00145-018-9284-1`.
- Barthe, Belaïd, Cassiers, Fouque, Grégoire, Standaert, *maskVerif: Automated Verification of Higher-Order Masking in Presence of Physical Defaults*, ESORICS 2019, `doi:10.1007/978-3-030-29959-0_15`.
- Belaïd, Dagand, Mercadier, Rivain, Wintersdorff, *Tornado: Automatic Generation of Probing-Secure Masked Bitsliced Implementations*, EUROCRYPT 2020, `ePrint 2020/506`.
- Cassiers, Grégoire, Levi, Standaert, *Hardware Private Circuits: From Trivial Composition to Full Verification*, IEEE TC 2020, `doi:10.1109/TC.2020.3022979`.
- Shelton, Samwel, Batina, Regazzoni, Wagner, Yarom, *ROSITA: Towards Automatic Elimination of Power-Analysis Leakage in Ciphers*, NDSS 2021, `doi:10.14722/ndss.2021.23137`.
- Barthe, Gourjon, Grégoire, Orlt, Paglialonga, Porth, *Masking in Fine-Grained Leakage Models: Construction, Implementation and Verification*, TCHES 2021(2):189–228, `doi:10.46586/tches.v2021.i2.189-228`.
- Belaïd, Mercadier, Rivain, Taleb, *IronMask: Versatile Verification of Masking Security*, IEEE S&P 2022, `doi:10.1109/SP46214.2022.9833600`.

### Analytical Micro-Probe Execution (2026-11-19, Python 3)
Executed standalone exact-distribution probe verifying `2-NI` vs. `2-SNI` on circular vs. ISW refresh (Probe 2A), 1-probe mutual information under `isw_mult` XOR reassociation (Probe 2B), and Goubin `B2A` correctness and 1-probe uniformity (Probe 2C):
```text
=== Probe 2A: Exact 2-NI & 2-SNI Verification (d=2, 3 shares) ===
CircularRefresh(d=2): 2-NI=PASS, 2-SNI=FAIL (['m0=x2^r0', 'y0=x0^r0'], 1, 2, (0, 2))
ISWRefresh(d=2)     : 2-NI=PASS, 2-SNI=PASS

=== Probe 2B: Exact 1-Probe Mutual Information I(V; (a,b)) Under XOR Reassociation ===
Parenthesized  v_safe = rnd ^ (a0 & b1)        => I(V; (a,b)) = 0.000000 bits
Reassociated   v_bad  = (a0 & b1) ^ (a1 & b0)  => I(V; (a,b)) = 0.204434 bits

=== Probe 2C: Goubin B2A Correctness (8-bit) & 1-Probing Uniformity (4-bit exact) ===
  Intermediate T1=x'^g  : dist(x=0x0) == dist(x=0xF) -> True
  Intermediate T2=T1-g  : dist(x=0x0) == dist(x=0xF) -> True
  Intermediate T3=T2^x' : dist(x=0x0) == dist(x=0xF) -> True
  Intermediate g2=g^r   : dist(x=0x0) == dist(x=0xF) -> True
  Intermediate A1=x'^g2 : dist(x=0x0) == dist(x=0xF) -> True
  Intermediate A2=A1-g2 : dist(x=0x0) == dist(x=0xF) -> True
  Intermediate A=A2^T3  : dist(x=0x0) == dist(x=0xF) -> True
```

## Revalidation

1. **Pin & Diff Upstream Toolchains**: Resolve `HEAD` SHAs for `CryptoExperts/Tornado`, `cassiersg/maskverif`, `leakage-resilience/scverif`, `CryptoExperts/IronMask`, and `0xADE1A1DE/rosita`; diff `scverif/models/*.il` for newly added CPU leakage models and `maskverif/src/main.ml` / `IronMask/Readme.md` for newly supported probing or combined-security notions.
2. **Re-run Exact Probing & Reassociation Checks**: Execute the compact Python 3 check below to revalidate the `isw_mult` reassociation leak and Goubin `B2A` identity:
```python
import itertools, math
from collections import Counter
def mi(fn):
    j = Counter(((a, b), fn(a^ra, ra, b^rb, rb, r)) for a,b,ra,rb,r in itertools.product((0,1), repeat=5))
    n = 32; ps, pv = Counter(), Counter()
    for (s, v), c in j.items(): ps[s] += c; pv[v] += c
    return sum((c/n)*math.log2((c/n)/((ps[s]/n)*(pv[v]/n))) for (s,v), c in j.items())
assert abs(mi(lambda a0,a1,b0,b1,r: r ^ (a0 & b1))) < 1e-12
assert mi(lambda a0,a1,b0,b1,r: (a0 & b1) ^ (a1 & b0)) > 0.20
for x in range(256):
    r, g = (x*7 + 3) & 0xFF, (x*13 + 5) & 0xFF; xp = x ^ r
    T = (((xp ^ g) - g) & 0xFF) ^ xp; g2 = g ^ r; A = ((((xp ^ g2) - g2) & 0xFF) ^ T)
    assert (A + r) & 0xFF == x
print("revalidation ok")
```
3. **Compiler Output Audit**: For any target compiler version (e.g., new `rustc`/LLVM or GCC release) compiling masked Rust/C code, revalidation requires inspecting the emitted target assembly—or running `scverif` over the lifted assembly—to confirm zero share-merging register overwrites, zero shared spill-slot transitions, and zero algebraic reassociation across masked gadgets.
